#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct value {
	enum {
		VALUE_NONE,
		VALUE_GLOBAL,
		VALUE_INTCONST,
		VALUE_FLTCONST,
		VALUE_DBLCONST,
		VALUE_TEMP,
		VALUE_TYPE,
		VALUE_LABEL,

		VALUE_EXTERN = 1<<4,
		VALUE_THREAD = 1<<5,
		VALUE_QUOTE = 1<<6,
	} kind;
	unsigned id;
	union {
		char *name;
		unsigned long long i;
		double f;
	} u;
	struct decl *decl;   /* a global's declaration (mkglobal), for funcsccp's calls; null for cproc's own names */
};

struct lvalue {
	struct value *addr;
	struct bitfield bits;
};

enum instkind {
	INONE,

#define OP(op, name) op,
#include "ops.h"
#undef OP

	IARG,
	IVARARG,
};

struct qbetype {
	char base, data;
	enum instkind load, store;
};

struct inst {
	enum instkind kind;
	int class;
	struct value res, *arg[3];  /* arg[2]: the size of a blit */
};

struct jump {
	enum {
		JUMP_NONE,
		JUMP_JMP,
		JUMP_JNZ,
		JUMP_RET,
		JUMP_HLT,
	} kind;
	struct value *arg;
	struct block *blk[2];
};

struct block {
	struct value label;
	struct array insts;
	struct {
		int class;
		struct block *blk[2];
		struct value *val[2];
		struct value res;
	} phi;
	struct jump jump;

	/* inline asm (funcasm): the thunks of the asm statements in this block, their symbol operands (struct value *), and
	 * a refusal deferred under cproc -p. emitfunc writes them out only for a block that can be reached: the kernel's
	 * cmpxchg switches on sizeof(*ptr), and the asm of a case never taken may not even assemble */
	struct array thunks, asmrefs;
	char *lazyerror;
	bool reach;
	unsigned idx;   /* funcsccp: the block's number */

	struct block *next;
};

struct switchcase {
	struct treenode node;   /* the key is the low end of the values */
	unsigned long long hi;  /* the high end: hi == key for a single value, more for a GNU case range */
	struct block *body;
};

struct func {
	struct decl *decl, *namedecl;
	char *name;
	struct value *paramtemps;
	struct type *type;
	struct block *start, *end;
	struct map gotos;
	unsigned lastid;
	struct array asan;   /* -fsanitize=address: the stack objects with redzones (asanalloc), unpoisoned by funcret */
	const char *asanfile;   /* -fsanitize=address: the file of the first check, for dbgfile before the function */
	struct array asanrets;   /* -fsanitize=address: the blocks that return (funcret), for asandynret */
	struct value *asanlo, *asanhi;   /* -fsanitize=address: the dynamic allocations' bounds (asandynalloc); NULL if none */
	struct array asanopen;   /* -fsanitize=address: the blocks being compiled, outermost first (unsigned numbers; asanbegin) */
	unsigned asanblocks;   /* -fsanitize=address: the blocks begun so far, for numbering them */
	struct array asanjmps;   /* -fsanitize=address: the calls of setjmp (struct asanjmp), poisoned in asanfinish */
	struct array ehobjs;     /* nfcxx's cleanup attribute: the objects (struct ehobj, in declaration order; ehcleanupobj) */
	struct array cleanups;   /* cproc -G: the cleanup objects live now (struct ehobj), innermost last */
	struct funcshape shape;  /* stmt.c: whether the body is { return C; } */
	struct array cleangotos; /* cproc -G: the gotos (struct cleangoto), their cleanups made after the body */
};

/* a block-scope object with a cleanup attribute: the cleanup function and the object's address */
struct ehobj {
	const char *cleanup;
	struct value *fn;   /* cproc -G: the cleanup function */
	struct value *addr;
};

/* a stack object with redzones: the base of its allocation (an entry block temporary) and the allocation's size */
struct asanobj {
	struct value *base;
	unsigned long long size;
	struct value *obj;   /* the object itself (base + ASANRZ), poisoned as stack-use-after-scope when its block is left */
	unsigned long long obj8;   /* the object's size rounded up to a granule: the bytes poisoned */
	unsigned block;   /* the block that declares it (the innermost open block at asanalloc, asantop) */
	/* a dynamic block (asandynalloc: base is NULL): the address and the size (rounded up) are kept in entry-block slots,
	 * since the block is poisoned where a scope ends, which need not be dominated by the allocation */
	struct value *objslot, *sizeslot;
	/* -fsanitize=address, use after return: the fake frame that __asan_stack_malloc_N returned for this object (NULL when it
	 * returned none, and the object is in the real frame), its size and class for __asan_stack_free_N (asanfree), and its
	 * description: desc is the text of a data item named desclabel, which emitfunc writes before the function */
	struct value *fake;
	unsigned long long fsize;
	int fclass;
	char *desclabel, *desc;
};

/* a call of setjmp (asansetjmp): the block that poisons the objects out of scope at the call (pad, see asanfinish) and the
 * block after it. Both returns of the call pass through pad; open is the set of blocks open at the call. */
struct asanjmp {
	struct block *pad, *next;
	struct array *open;
};

/* the QBE class of a pointer (and of size_t): w on an ILP32 target (i386) */
#define ptrclass (targ->ilp32 ? 'w' : 'l')

void
switchcase(struct switchcases *cases, unsigned long long lo, unsigned long long hi, struct block *b)
{
	struct switchcase *c;

	/* the values in the tree are disjoint intervals ordered by their low end, so an overlap is found on one path */
	for (c = cases->root; c;) {
		if (c->hi < lo)
			c = c->node.child[1];
		else if (c->node.key > hi)
			c = c->node.child[0];
		else
			error(&tok.loc, "multiple 'case' labels with same value");
	}
	c = treeinsert(&cases->root, lo, sizeof(*c));
	c->hi = hi;
	c->body = b;
}

/* values */

struct block *
mkblock(char *name)
{
	static unsigned id;
	struct block *b;

	b = xmalloc(sizeof(*b));
	b->label.kind = VALUE_LABEL;
	b->label.u.name = name;
	b->label.id = ++id;
	b->insts = (struct array){0};
	b->thunks = b->asmrefs = (struct array){0};
	b->lazyerror = NULL;
	b->reach = false;
	b->jump.kind = JUMP_NONE;
	b->phi.res.kind = VALUE_NONE;
	b->next = NULL;

	return b;
}

struct value *
mkglobal(struct decl *d)
{
	static unsigned id;
	struct value *v;

	v = xmalloc(sizeof(*v));
	v->kind = VALUE_GLOBAL;
	if (d->linkage == LINKEXTERN)
		v->kind |= VALUE_EXTERN;
	if (d->kind == DECLOBJECT && d->u.obj.storage == SDTHREAD)
		v->kind |= VALUE_THREAD;
	if (d->asmname) {
		v->kind |= VALUE_QUOTE;
		v->u.name = d->asmname;
		v->id = 0;
	} else {
		v->u.name = d->name;
		v->id = d->linkage == LINKNONE ? ++id : 0;
	}
	v->decl = d;

	return v;
}

struct decl *
funcdecl(struct func *f)
{
	return f->decl;
}

struct funcshape *
funcshape(struct func *f)
{
	return &f->shape;
}

/* a local name for the body of an extern gnu_inline function: "$.LNAME.N", a symbol of this object only */
struct value *
mkinlinealias(struct decl *d)
{
	static unsigned id;
	struct value *v;

	assert(!d->asmname);
	v = xmalloc(sizeof(*v));
	*v = *d->value;
	v->kind &= ~VALUE_EXTERN;
	v->id = 1000000000 + ++id;   /* beyond mkglobal's numbers for block-scope statics */
	return v;
}

struct value *
mkintconst(unsigned long long n)
{
	struct value *v;

	v = xmalloc(sizeof(*v));
	v->kind = VALUE_INTCONST;
	v->u.i = n;

	return v;
}

static struct value *
mkfltconst(int kind, double n)
{
	struct value *v;

	v = xmalloc(sizeof(*v));
	v->kind = kind;
	v->u.f = n;

	return v;
}

/* ILP32 (i386): long double (gcc's 12-byte x87 value) and __float128 are declared with gcc's layout, but cproc's
 * values of them are 16-byte soft values: a value of them, a parameter or a return, or an initializer is refused */
static bool
softvalue(struct type *t)
{
	return t->kind == TYPELDOUBLE || t->kind == TYPEFLOAT128;
}

static struct qbetype
qbetype(struct type *t)
{
	static const struct qbetype
		ub = {'w', 'b', ILOADUB, ISTOREB},
		sb = {'w', 'b', ILOADSB, ISTOREB},
		uh = {'w', 'h', ILOADUH, ISTOREH},
		sh = {'w', 'h', ILOADSH, ISTOREH},
		w = {'w', 'w', ILOADW, ISTOREW},
		l = {'l', 'l', ILOADL, ISTOREL},
		p32 = {'w', 'w', ILOADW, ISTOREW},
		s = {'s', 's', ILOADS, ISTORES},
		d = {'d', 'd', ILOADD, ISTORED},
		v = {0};

	if (t == &typevoid)
		return v;
	if (!(t->prop & PROPSCALAR) || t->prop & PROPSOFT)
		return targ->ilp32 ? p32 : l;   /* the address of the object */
	switch (t->size) {
	case 1: return t->u.arith.issigned ? sb : ub;
	case 2: return t->u.arith.issigned ? sh : uh;
	case 4: return t->prop & PROPFLOAT ? s : w;
	case 8: return t->prop & PROPFLOAT ? d : l;
	}
	assert(0);
}

/* functions */

static void emittype(struct type *);
static void emitname(struct value *);
static void emitbarename(struct value *);
static void funcasmout(struct func *);
static void emitvalue(struct value *);

static void
functemp(struct func *f, struct value *v)
{
	v->kind = VALUE_TEMP;
	v->u.name = NULL;
	v->id = ++f->lastid;
}

static const char *const instname[] = {
#define OP(op, name) [op] = name,
#include "ops.h"
#undef OP
};

static struct inst *
mkinst(struct func *f, int op, int class, struct value *arg0, struct value *arg1)
{
	struct inst *inst;

	inst = xmalloc(sizeof(*inst));
	inst->kind = op;
	inst->class = class;
	inst->arg[0] = arg0;
	inst->arg[1] = arg1;
	inst->arg[2] = NULL;
	if (class && op != IARG)
		functemp(f, &inst->res);
	else
		inst->res.kind = VALUE_NONE;
	return inst;
}

/*
-fsanitize=address (nfcxx: the environment variable NFCXX_ASAN, set by the driver): every load and store is preceded by a
call of libasan's check on its address, __asan_load{1,2,4,8} and __asan_store{1,2,4,8}. Every access goes through funcinst,
so this is the one place. A check is an ordinary call, so QBE cannot merge or forward the access past it.
*/
bool asanon;   /* set by main from NFCXX_ASAN */
/* -fsanitize=address: the location of the expression being generated (funcexpr), for dbgloc before each check */
static struct location asanloc;

static struct value *funcinst(struct func *f, int op, int class, struct value *arg0, struct value *arg1);
static struct value *asanraw(struct func *f, struct block *b, int op, int class, struct value *arg0, struct value *arg1);

/* the global function name, as a call target */
static struct value *
asanfn(const char *name)
{
	struct value *fn;
	char *s;

	s = xmalloc(strlen(name) + 1);
	strcpy(s, name);
	fn = xmalloc(sizeof(*fn));
	fn->kind = VALUE_GLOBAL;
	fn->u.name = s;
	fn->id = 0;
	fn->decl = NULL;
	return fn;
}

/* a call of the runtime function name with one or two pointer-sized arguments (b may be NULL) */
static void
asancall(struct func *f, const char *name, struct value *a, struct value *b)
{
	funcinst(f, ICALL, 0, asanfn(name), NULL);
	funcinst(f, IARG, ptrclass, a, NULL);
	if (b)
		funcinst(f, IARG, ptrclass, b, NULL);
}

/* a call of the runtime function name with one pointer-sized argument a, whose result (a pointer) is returned */
static struct value *
asancallret(struct func *f, const char *name, struct value *a)
{
	struct value *r;

	r = funcinst(f, ICALL, ptrclass, asanfn(name), NULL);
	funcinst(f, IARG, ptrclass, a, NULL);
	return r;
}

static void
asancheck(struct func *f, const char *name, struct value *addr)
{
	if (asanloc.line) {
		funcinst(f, IDBGLOC, 0, mkintconst(asanloc.line), NULL);
		if (!f->asanfile)
			f->asanfile = asanloc.file;
	}
	asancall(f, name, addr, NULL);
}

static void
asanaccess(struct func *f, int op, struct value *arg0, struct value *arg1)
{
	switch (op) {
	/* a load's address is arg0; a store's is arg1 (the value stored is arg0) */
	case ILOADUB: case ILOADSB: asancheck(f, "__asan_load1", arg0); break;
	case ILOADUH: case ILOADSH: asancheck(f, "__asan_load2", arg0); break;
	case ILOADW:  case ILOADS:  asancheck(f, "__asan_load4", arg0); break;
	case ILOADL:  case ILOADD:  asancheck(f, "__asan_load8", arg0); break;
	case ISTOREB: asancheck(f, "__asan_store1", arg1); break;
	case ISTOREH: asancheck(f, "__asan_store2", arg1); break;
	case ISTOREW: case ISTORES: asancheck(f, "__asan_store4", arg1); break;
	case ISTOREL: case ISTORED: asancheck(f, "__asan_store8", arg1); break;
	}
}

static struct value *
funcinst(struct func *f, int op, int class, struct value *arg0, struct value *arg1)
{
	struct inst *inst;
	struct block *b;

	if (f->end->jump.kind) {
		b = mkblock("dead");
		funclabel(f, b);
	}
	if (asanon)
		asanaccess(f, op, arg0, arg1);
	inst = mkinst(f, op, class, arg0, arg1);
	arrayaddptr(&f->end->insts, inst);
	return &inst->res;
}

/*
SysV passes a _Float16 argument or return value in an SSE register (the low 16 bits of an xmm), not in an integer
register, so QBE's class for it at the function boundary is 's'. The register holds the float's bits, and the binary16
pattern is its low 16 bits. Inside a function a _Float16 stays a 'w' pattern. Only the boundary converts: a value
passed out (an argument, a return value) is cast to 's', and a value passed in is cast back and masked, because the
upper 16 bits of the register are undefined.
*/
static int
abiclass(struct type *t)
{
	return t->kind == TYPEFLOAT16 ? 's' : qbetype(t).base;
}

/* the register form (s) of a _Float16 pattern (w) */
static struct value *
f16tosse(struct func *f, struct value *v)
{
	return funcinst(f, ICAST, 's', v, NULL);
}

/* the pattern (w) of a _Float16 in a register (s): its low 16 bits */
static struct value *
f16fromsse(struct func *f, struct value *v)
{
	v = funcinst(f, ICAST, 'w', v, NULL);
	return funcinst(f, IAND, 'w', v, mkintconst(0xffff));
}

static struct value *
funcbits(struct func *f, struct type *t, struct value *v, struct bitfield b)
{
	int class, bits;

	class = t->size <= 4 ? 'w' : 'l';
	bits = b.after;
	if (!bits && t->kind == TYPEBITINT)
		bits = t->size * 8 - t->u.arith.width;
	if (bits) {
		bits += (t->size + 3 & -4) - t->size << 3;
		v = funcinst(f, ISHL, class, v, mkintconst(bits));
	}
	bits += b.before;
	if (bits)
		v = funcinst(f, t->u.arith.issigned ? ISAR : ISHR, class, v, mkintconst(bits));
	return v;
}

/*
Soft floating types: long double and __float128 (PROPSOFT in cc.h). Such a value is not a QBE scalar. Like a struct, its
value is the address of a 16-byte, 16-aligned object, and passing or returning one by value uses the QBE aggregate
:__nfcxx_soft16 (two integer eightbytes), which the struct code of the calls, parameters and returns already handles.
Every arithmetic operation, comparison and conversion is a call of a helper of the runtime (be/nfcxx_ldrt.c, names
__nfcxx_ld_<op> for long double and __nfcxx_f128_<op> for __float128). A helper takes its operands by address and writes
a result through the first address, so no 16-byte value crosses the call in a register. A predicate or integer result is
returned in an integer register.
*/
struct softarg {
	int class;
	struct value *v;
};

static struct value *convert(struct func *f, struct type *dst, struct type *src, struct value *l);

static struct value *
softname(struct type *t, const char *op)
{
	const char *prefix = t->kind == TYPEINT128 ? "__nfcxx_i128_" : t->kind == TYPEFLOAT128 ? "__nfcxx_f128_" :
	                     t->kind == TYPEFLOAT16 ? "__nfcxx_f16_" : "__nfcxx_ld_";
	struct value *v;
	char *name;

	name = xmalloc(strlen(prefix) + strlen(op) + 1);
	strcpy(name, prefix);
	strcat(name, op);
	v = xmalloc(sizeof(*v));
	v->kind = VALUE_GLOBAL;
	v->u.name = name;
	v->id = 0;
	v->decl = NULL;
	return v;
}

/* a 16-byte temporary, allocated in the entry block as funcalloc does, so that a loop does not grow the stack */
static struct value *
softtemp(struct func *f)
{
	struct block *end = f->end;
	struct value *v;

	f->end = f->start;
	v = funcinst(f, IALLOC16, ptrclass, mkintconst(16), NULL);
	f->end = end;
	return v;
}

static struct value *softcall(struct func *f, int class, struct value *fn, unsigned n, struct softarg *arg);

/* an atomic builtin (expr.c, atomicbuiltin) as a call of libatomic's sized function __atomic_OP_N for the size N of the
 * pointee: the pointer, the value(s) and the memory order, in the sized functions' own convention (compare-exchange
 * takes the expected pointer and returns a bool). libSystem exports them on macOS. */
static struct value *
funcatomic(struct func *f, struct expr *e)
{
	struct expr *a[5];
	struct softarg sa[5];
	struct type *pt;
	struct value *r;
	const char *op;
	char name[32];
	unsigned n = 0, i, size;
	int vclass, rclass;

	for (struct expr *x = e->base; x; x = x->next)
		a[n++] = x;
	pt = a[0]->type->base;
	size = pt->size;
	vclass = qbetype(pt).base;
	rclass = 0;
	switch (e->u.builtin.kind) {
	case BUILTINC11INIT:
	case BUILTINC11STORE:
		op = "store";
		break;
	case BUILTINC11LOAD:
		op = "load";
		rclass = vclass;
		break;
	case BUILTINC11XCHG:
		op = "exchange";
		rclass = vclass;
		break;
	case BUILTINC11CAS:
		op = "compare_exchange";
		rclass = 'w';
		break;
	case BUILTINC11FETCHADD:
		op = "fetch_add";
		rclass = vclass;
		break;
	case BUILTINC11FETCHSUB:
		op = "fetch_sub";
		rclass = vclass;
		break;
	case BUILTINC11FETCHAND:
		op = "fetch_and";
		rclass = vclass;
		break;
	case BUILTINC11FETCHOR:
		op = "fetch_or";
		rclass = vclass;
		break;
	case BUILTINC11FETCHXOR:
		op = "fetch_xor";
		rclass = vclass;
		break;
	default:
		fatal("internal error; not an atomic builtin");
	}
	snprintf(name, sizeof(name), "__atomic_%s_%u", op, size);
	/* the sized functions: (ptr, value, order), (ptr, order) for load, (ptr, expected, desired, success, failure) for
	 * compare-exchange; INIT is a relaxed store (order 0) */
	switch (e->u.builtin.kind) {
	case BUILTINC11LOAD:
		n = 2;
		sa[0] = (struct softarg){ptrclass, funcexpr(f, a[0])};
		sa[1] = (struct softarg){'w', funcexpr(f, a[1])};
		break;
	case BUILTINC11CAS:
		sa[0] = (struct softarg){ptrclass, funcexpr(f, a[0])};
		sa[1] = (struct softarg){ptrclass, funcexpr(f, a[1])};
		sa[2] = (struct softarg){vclass, funcexpr(f, a[2])};
		sa[3] = (struct softarg){'w', funcexpr(f, a[3])};
		sa[4] = (struct softarg){'w', funcexpr(f, a[4])};
		n = 5;
		break;
	case BUILTINC11INIT:
		sa[0] = (struct softarg){ptrclass, funcexpr(f, a[0])};
		sa[1] = (struct softarg){vclass, funcexpr(f, a[1])};
		sa[2] = (struct softarg){'w', mkintconst(0)};
		n = 3;
		break;
	default:
		sa[0] = (struct softarg){ptrclass, funcexpr(f, a[0])};
		sa[1] = (struct softarg){vclass, funcexpr(f, a[1])};
		sa[2] = (struct softarg){'w', funcexpr(f, a[2])};
		n = 3;
		break;
	}
	r = softcall(f, rclass, asanfn(name), n, sa);
	return rclass ? r : NULL;
}

/* a call of fn (class is the class of its result, 0 for none) with n arguments */
static struct value *
softcall(struct func *f, int class, struct value *fn, unsigned n, struct softarg *arg)
{
	struct value *r;
	unsigned i;

	r = funcinst(f, ICALL, class, fn, NULL);
	for (i = 0; i < n; ++i)
		funcinst(f, IARG, arg[i].class, arg[i].v, NULL);
	return r;
}

/*
__int128 and unsigned __int128 (TYPEINT128, PROPSOFT): the same scheme as the floating soft types, with the helpers
__nfcxx_i128_<op> of be/nfcxx_ldrt.c. A shift takes its count as a long (the caller converts it). The comparisons > and >=
are the < and <= helpers with the operands swapped.
*/
static struct value *
int128binary(struct func *f, enum tokenkind op, struct type *t, struct value *l, struct value *r)
{
	struct softarg a[3];
	struct value *d;
	struct value *tmp;
	const char *name;
	bool s = t->u.arith.issigned;
	bool cmp = false, swap = false;

	switch (op) {
	case TADD:     name = "add"; break;
	case TSUB:     name = "sub"; break;
	case TMUL:     name = "mul"; break;
	case TDIV:     name = s ? "div_s" : "div_u"; break;
	case TMOD:     name = s ? "rem_s" : "rem_u"; break;
	case TBAND:    name = "and"; break;
	case TBOR:     name = "or"; break;
	case TXOR:     name = "xor"; break;
	case TSHL:     name = "shl"; break;
	case TSHR:     name = s ? "shr_s" : "shr_u"; break;
	case TEQL:     name = "eq"; cmp = true; break;
	case TNEQ:     name = "ne"; cmp = true; break;
	case TLESS:    name = s ? "lt_s" : "lt_u"; cmp = true; break;
	case TLEQ:     name = s ? "le_s" : "le_u"; cmp = true; break;
	case TGREATER: name = s ? "lt_s" : "lt_u"; cmp = true; swap = true; break;
	case TGEQ:     name = s ? "le_s" : "le_u"; cmp = true; swap = true; break;
	default:
		fatal("internal error; unsupported operation on __int128");
	}
	if (swap) {
		tmp = l;
		l = r;
		r = tmp;
	}
	if (cmp) {
		a[0] = (struct softarg){'l', l};
		a[1] = (struct softarg){'l', r};
		return softcall(f, 'w', softname(t, name), 2, a);
	}
	d = softtemp(f);
	a[0] = (struct softarg){'l', d};
	a[1] = (struct softarg){'l', l};
	a[2] = (struct softarg){'l', r};
	softcall(f, 0, softname(t, name), 3, a);
	return d;
}

/* the operation op (an operator token) on two soft operands of type t: a new temporary, or an int for a comparison */
static struct value *
softbinary(struct func *f, enum tokenkind op, struct type *t, struct value *l, struct value *r)
{
	struct softarg a[3];
	struct value *d;
	const char *name;
	bool cmp = false;

	if (t->kind == TYPEINT128)
		return int128binary(f, op, t, l, r);
	switch (op) {
	case TADD:    name = "add"; break;
	case TSUB:    name = "sub"; break;
	case TMUL:    name = "mul"; break;
	case TDIV:    name = "div"; break;
	case TEQL:    name = "eq"; cmp = true; break;
	case TNEQ:    name = "ne"; cmp = true; break;
	case TLESS:   name = "lt"; cmp = true; break;
	case TLEQ:    name = "le"; cmp = true; break;
	case TGREATER: name = "gt"; cmp = true; break;
	case TGEQ:    name = "ge"; cmp = true; break;
	default:
		fatal("internal error; unsupported operation on a 16-byte floating type");
	}
	a[0] = (struct softarg){'l', l};
	a[1] = (struct softarg){'l', r};
	if (cmp)
		return softcall(f, 'w', softname(t, name), 2, a);
	d = softtemp(f);
	a[0] = (struct softarg){'l', d};
	a[1] = (struct softarg){'l', l};
	a[2] = (struct softarg){'l', r};
	softcall(f, 0, softname(t, name), 3, a);
	return d;
}

/* a unary helper on a soft value: neg */
static struct value *
softunary(struct func *f, struct type *t, const char *name, struct value *l)
{
	struct softarg a[2];
	struct value *d;

	d = softtemp(f);
	a[0] = (struct softarg){'l', d};
	a[1] = (struct softarg){'l', l};
	softcall(f, 0, softname(t, name), 2, a);
	return d;
}

/*
A conversion where dst or src is __int128 (src and dst differ). The unsigned and signed forms differ only in the helper
suffix _s or _u, chosen by the signedness of the integer side: from an integer or a float, the destination's; to one, the
source's. The same bit pattern is copied for a change of signedness only.
*/
static struct value *
convertint128(struct func *f, struct type *dst, struct type *src, struct value *l)
{
	struct softarg a[2];
	struct value *d;
	const char *name;
	bool s;

	if (dst->kind == TYPEBOOL) {
		a[0] = (struct softarg){'l', l};
		return softcall(f, 'w', softname(src, "nz"), 1, a);
	}
	if (dst->kind == TYPEINT128) {
		d = softtemp(f);
		a[0] = (struct softarg){'l', d};
		s = dst->u.arith.issigned;
		if (src->kind == TYPEINT128) {
			a[1] = (struct softarg){'l', l};
			softcall(f, 0, softname(dst, "copy"), 2, a);
			return d;
		}
		if (src->prop & PROPINT) {
			if (src->size < 8)
				l = convert(f, src->u.arith.issigned ? &typelong : &typeulong, src, l);
			name = src->u.arith.issigned ? "from_s64" : "from_u64";
			a[1] = (struct softarg){'l', l};
		} else if (src->kind == TYPELDOUBLE || src->kind == TYPEFLOAT128) {
			name = src->kind == TYPELDOUBLE ? (s ? "from_ld_s" : "from_ld_u") : (s ? "from_f128_s" : "from_f128_u");
			a[1] = (struct softarg){'l', l};
		} else if (src->size == 4) {
			name = s ? "from_f32_s" : "from_f32_u";
			a[1] = (struct softarg){'s', l};
		} else {
			name = s ? "from_f64_s" : "from_f64_u";
			a[1] = (struct softarg){'d', l};
		}
		softcall(f, 0, softname(dst, name), 2, a);
		return d;
	}
	/* from __int128 to a scalar integer, or to a float type */
	a[0] = (struct softarg){'l', l};
	if (dst->prop & PROPINT) {
		l = softcall(f, 'l', softname(src, "lo64"), 1, a);
		return convert(f, dst, &typeulong, l);
	}
	s = src->u.arith.issigned;
	if (dst->prop & PROPSOFT) {
		/* a long double or __float128 result */
		d = softtemp(f);
		a[0] = (struct softarg){'l', d};
		a[1] = (struct softarg){'l', l};
		name = dst->kind == TYPELDOUBLE ? (s ? "to_ld_s" : "to_ld_u") : (s ? "to_f128_s" : "to_f128_u");
		softcall(f, 0, softname(src, name), 2, a);
		return d;
	}
	if (dst->size == 4)
		return softcall(f, 's', softname(src, s ? "to_f32_s" : "to_f32_u"), 1, a);
	return softcall(f, 'd', softname(src, s ? "to_f64_s" : "to_f64_u"), 1, a);
}

/* a conversion where dst or src is a soft type (src and dst differ, and neither is a pointer or void) */
static struct value *
convertsoft(struct func *f, struct type *dst, struct type *src, struct value *l)
{
	struct softarg a[2];
	struct value *d;
	const char *name;
	int bits;

	if (dst->kind == TYPEINT128 || src->kind == TYPEINT128)
		return convertint128(f, dst, src, l);
	if (dst->prop & PROPSOFT && src->prop & PROPSOFT) {
		d = softtemp(f);
		a[0] = (struct softarg){'l', d};
		a[1] = (struct softarg){'l', l};
		softcall(f, 0, softname(dst, src->kind == TYPELDOUBLE ? "from_ld" : "from_f128"), 2, a);
		return d;
	}
	if (dst->prop & PROPSOFT) {
		d = softtemp(f);
		a[0] = (struct softarg){'l', d};
		if (src->prop & PROPINT) {
			if (src->size < 8)
				l = convert(f, src->u.arith.issigned ? &typelong : &typeulong, src, l);
			name = src->u.arith.issigned ? "from_s64" : "from_u64";
			a[1] = (struct softarg){'l', l};
		} else if (src->size == 4) {
			name = "from_f32";
			a[1] = (struct softarg){'s', l};
		} else {
			name = "from_f64";
			a[1] = (struct softarg){'d', l};
		}
		softcall(f, 0, softname(dst, name), 2, a);
		return d;
	}
	/* from a soft type to a scalar */
	a[0] = (struct softarg){'l', l};
	if (dst->kind == TYPEBOOL) {
		return softcall(f, 'w', softname(src, "nz"), 1, a);
	} else if (dst->prop & PROPINT) {
		bits = dst->size * 8;
		a[1] = (struct softarg){'w', mkintconst(bits)};
		name = dst->u.arith.issigned ? "to_s" : "to_u";
		return softcall(f, dst->size == 8 ? 'l' : 'w', softname(src, name), 2, a);
	}
	name = dst->size == 4 ? "to_f32" : "to_f64";
	return softcall(f, dst->size == 4 ? 's' : 'd', softname(src, name), 1, a);
}

/*
_Float16 (TYPEFLOAT16) is a scalar whose QBE value is its 16-bit pattern in a word. Each operation is a call of a
helper of the runtime (be/nfcxx_ldrt.c, __nfcxx_f16_<op>) on patterns, which returns a pattern or, for a comparison, an
int. The helpers round a result once, to nearest with ties to even. A conversion to a wider type goes through double,
which holds every binary16 value exactly.
*/
static struct value *
f16binary(struct func *f, enum tokenkind op, struct type *t, struct value *l, struct value *r)
{
	struct softarg a[2];
	const char *name;

	switch (op) {
	case TADD:     name = "add"; break;
	case TSUB:     name = "sub"; break;
	case TMUL:     name = "mul"; break;
	case TDIV:     name = "div"; break;
	case TEQL:     name = "eq"; break;
	case TNEQ:     name = "ne"; break;
	case TLESS:    name = "lt"; break;
	case TLEQ:     name = "le"; break;
	case TGREATER: name = "gt"; break;
	case TGEQ:     name = "ge"; break;
	default:
		fatal("internal error; unsupported operation on _Float16");
	}
	a[0] = (struct softarg){'w', l};
	a[1] = (struct softarg){'w', r};
	return softcall(f, 'w', softname(t, name), 2, a);
}

/* a conversion where dst or src is _Float16 (src and dst differ) */
static struct value *
convertf16(struct func *f, struct type *dst, struct type *src, struct value *l)
{
	struct softarg a[1];
	struct value *d;

	if (dst->kind == TYPEFLOAT16) {
		if (src->prop & PROPINT) {
			if (src->size < 8)
				l = convert(f, src->u.arith.issigned ? &typelong : &typeulong, src, l);
			a[0] = (struct softarg){'l', l};
			return softcall(f, 'w', softname(dst, src->u.arith.issigned ? "from_s64" : "from_u64"), 1, a);
		}
		/* the 16-byte types are rounded to binary16 directly (rounding them to double first could double round) */
		if (src->kind == TYPELDOUBLE || src->kind == TYPEFLOAT128) {
			a[0] = (struct softarg){'l', l};
			return softcall(f, 'w', softname(dst, src->kind == TYPELDOUBLE ? "from_ld" : "from_f128"), 1, a);
		}
		/* a float or double is exact as a double */
		d = convert(f, &typedouble, src, l);
		a[0] = (struct softarg){'d', d};
		return softcall(f, 'w', softname(dst, "from_f64"), 1, a);
	}
	if (dst->kind == TYPEBOOL) {
		/* a value is true unless it is +0 or -0 (a NaN is true) */
		l = funcinst(f, IAND, 'w', l, mkintconst(0x7fff));
		return funcinst(f, ICNEW, 'w', l, mkintconst(0));
	}
	a[0] = (struct softarg){'w', l};
	d = softcall(f, 'd', softname(src, "to_f64"), 1, a);
	return convert(f, dst, &typedouble, d);
}

static struct value *
convert(struct func *f, struct type *dst, struct type *src, struct value *l)
{
	enum instkind op;
	struct value *r = NULL;
	int class;

	if (src == dst)
		return l;
	if (src->kind == TYPEPOINTER)
		src = &typeulong;
	if (dst->kind == TYPEPOINTER)
		dst = &typeulong;
	if (dst->kind == TYPEVOID)
		return NULL;
	if (src->kind == TYPEFLOAT16 || dst->kind == TYPEFLOAT16)
		return convertf16(f, dst, src, l);
	if ((src->prop | dst->prop) & PROPSOFT)
		return convertsoft(f, dst, src, l);
	if (!(src->prop & PROPREAL) || !(dst->prop & PROPREAL))
		fatal("internal error; unsupported conversion");
	if (dst->kind == TYPEBOOL) {
		class = 'w';
		if (src->prop & PROPINT) {
			r = mkintconst(0);
			switch (src->size) {
			case 1: op = ICNEW; if (src->kind != TYPEBITINT) l = funcinst(f, IEXTUB, 'w', l, NULL); break;
			case 2: op = ICNEW; if (src->kind != TYPEBITINT) l = funcinst(f, IEXTUH, 'w', l, NULL); break;
			case 4: op = ICNEW; break;
			case 8: op = ICNEL; break;
			default: fatal("internal error; unknown integer conversion");
			}
		} else {
			assert(src->prop & PROPFLOAT);
			switch (src->size) {
			case 4: op = ICNES, r = mkfltconst(VALUE_FLTCONST, 0); break;
			case 8: op = ICNED, r = mkfltconst(VALUE_DBLCONST, 0); break;
			default: fatal("internal error; unknown floating point conversion");
			}
		}
	} else if (dst->prop & PROPINT) {
		class = dst->size == 8 ? 'l' : 'w';
		if (src->prop & PROPINT) {
			if (dst->u.arith.width <= src->u.arith.width) {
				if (dst->kind == TYPEBITINT)
					return funcbits(f, dst, l, (struct bitfield){0});
				return l;
			}
			if (src->kind == TYPEBITINT && (src->size == 8 || dst->size == 4))
				return l;
			switch (src->size) {
			case 4: op = src->u.arith.issigned ? IEXTSW : IEXTUW; break;
			case 2: op = src->u.arith.issigned ? IEXTSH : IEXTUH; break;
			case 1: op = src->u.arith.issigned ? IEXTSB : IEXTUB; break;
			default: fatal("internal error; unknown integer conversion");
			}
		} else {
			if (dst->u.arith.issigned)
				op = src->size == 8 ? IDTOSI : ISTOSI;
			else
				op = src->size == 8 ? IDTOUI : ISTOUI;
		}
	} else {
		class = dst->size == 8 ? 'd' : 's';
		if (src->prop & PROPINT) {
			if (src->size < 4)
				l = convert(f, src->u.arith.issigned ? &typeint : &typeuint, src, l);
			if (src->u.arith.issigned)
				op = src->size == 8 ? ISLTOF : ISWTOF;
			else
				op = src->size == 8 ? IULTOF : IUWTOF;
		} else {
			assert(src->prop & PROPFLOAT);
			if (src->size == dst->size)
				return l;
			op = src->size < dst->size ? IEXTS : ITRUNCD;
		}
	}

	return funcinst(f, op, class, l, r);
}

static void
calcvla(struct func *f, struct type *t)
{
	struct value *length, *basesize;

	if (!(t->prop & PROPVM))
		return;
	if (t->base)
		calcvla(f, t->base);
	if (t->kind == TYPEFUNC || t->size)
		return;
	assert(t->kind == TYPEARRAY);
	if (!t->u.array.size) {
		assert(t->base->size || t->base->kind == TYPEARRAY);
		assert(t->u.array.length);
		length = convert(f, &typeulong, t->u.array.length->type, funcexpr(f, t->u.array.length));
		basesize = t->base->size ? mkintconst(t->base->size) : t->base->u.array.size;
		t->u.array.size = funcinst(f, IMUL, ptrclass, length, basesize);
	}
}

/*
-fsanitize=address: a stack object with a redzone of ASANRZ bytes on each side, allocated in the entry block. The object's
size is rounded up to a granule (8 bytes) so the right redzone starts on one: the bytes between the size and the rounding
are not covered. The object's whole allocation is unpoisoned on entry (poison left by a frame that longjmp left must not
catch this object), the redzones are poisoned, and funcret unpoisons the allocation before the function returns.
*/
#define ASANRZ 32

/* -fsanitize=address: sets of block numbers (struct array of unsigned); a null set is empty */
static bool
asaninset(const struct array *a, unsigned id)
{
	size_t i;

	if (!a)
		return false;
	for (i = 0; i < a->len / sizeof(unsigned); i++)
		if (((unsigned *)a->val)[i] == id)
			return true;
	return false;
}

static void
asanadd(struct array *a, unsigned id)
{
	if (!asaninset(a, id))
		*(unsigned *)arrayadd(a, sizeof(unsigned)) = id;
}

/* the innermost open block, 0 outside any block (the parameters) */
static unsigned
asantop(struct func *f)
{
	size_t n = f->asanopen.len / sizeof(unsigned);

	return n ? ((unsigned *)f->asanopen.val)[n - 1] : 0;
}

/*
-fsanitize=address, use after return: the fake frame of an object (libasan's fake stack, which the runtime keeps per thread).
A frame is asked for at the entry, with the frame size rounded up to 64 bytes: __asan_stack_malloc_N(size), N the smallest
class with 64 << N >= size (N <= 10, so size <= 64 KiB), returns 0 when detect_stack_use_after_return is off or the class is
full, and then the object stays in the real frame. The same classes and sizes gcc passes (`movl $64, %edi` for 64 bytes,
`__asan_stack_malloc_2` with 192). The frame's header is what gcc writes: magic 0x41B58AB3, the description (a data item,
"1 OFFSET SIZE NAMELEN NAME:LINE", as libasan reads it for the report), and the pc (the function, for the frame's name).
The object is at ASANRZ into the frame, as in the real frame. asanselect picks the frame when there is one. Objects over
16-byte alignment get none (the object's offset would depend on the address). asanfree gives the frame back at each return.
*/
#define ASANFRAMEMAGIC 0x41B58AB3LL
static unsigned asandescs;

/* the class of a fake frame of size bytes (a multiple of 64), or -1 when it is too big for one */
static int
asanclass(unsigned long long size)
{
	int c;

	for (c = 0; c <= 10; c++)
		if ((64ULL << c) >= size)
			return c;
	return -1;
}

/* base = fake when fake is not NULL, else real: m is all ones when fake is a non-null pointer (below 2^63, so -fake has its top
 * bit set) and zero when it is NULL, and base = real ^ ((real ^ fake) & m) (branch-free, as asanhi) */
static struct value *
asanselect(struct func *f, struct value *real, struct value *fake)
{
	struct value *m, *x;

	m = funcinst(f, IOR, ptrclass, fake, funcinst(f, ISUB, ptrclass, mkintconst(0), fake));
	m = funcinst(f, ISAR, ptrclass, m, mkintconst(63));
	x = funcinst(f, IAND, ptrclass, funcinst(f, IXOR, ptrclass, real, fake), m);
	return funcinst(f, IXOR, ptrclass, real, x);
}

static void
asanalloc(struct func *f, struct decl *d)
{
	struct block *end = f->end;
	unsigned long long size8 = (d->type->size + 7) & ~7ULL, align = d->u.obj.align, total = size8 + 2 * ASANRZ;
	unsigned long long frame = 0;
	struct value *real, *base, *obj, *right, *left, *rlen, *fake = NULL, *p;
	struct asanobj *o;
	int cls = -1;
	char name[64], *nl;

	f->end = f->start;
	if (align <= 16) {
		real = funcinst(f, IALLOC16, ptrclass, mkintconst(total), NULL);
		base = real;
		frame = (total + 63) & ~63ULL;
		cls = asanclass(frame);
		if (cls >= 0) {
			snprintf(name, sizeof(name), "__asan_stack_malloc_%d", cls);
			fake = asancallret(f, name, mkintconst(frame));
			base = asanselect(f, real, fake);
		}
		obj = funcinst(f, IADD, ptrclass, base, mkintconst(ASANRZ));
		right = funcinst(f, IADD, ptrclass, obj, mkintconst(size8));
		left = mkintconst(ASANRZ);
		rlen = mkintconst(ASANRZ);
	} else {
		/* over-aligned: the object is at the first multiple of align after base + ASANRZ; the left redzone is what lies
		 * before it, the right one what lies after it up to the end of the block (all multiples of 8) */
		total = size8 + align + 2 * ASANRZ;
		base = funcinst(f, IALLOC16, ptrclass, mkintconst(total), NULL);
		obj = funcinst(f, IADD, ptrclass, base, mkintconst(ASANRZ + align - 1));
		obj = funcinst(f, IAND, ptrclass, obj, mkintconst(-(long long)align));
		right = funcinst(f, IADD, ptrclass, obj, mkintconst(size8));
		left = funcinst(f, ISUB, ptrclass, obj, base);
		rlen = funcinst(f, ISUB, ptrclass, funcinst(f, IADD, ptrclass, base, mkintconst(total)), right);
	}
	/* the header, stored raw into the entry block (no check: nothing of the frame is unpoisoned yet): the magic, the
	 * description's address and the pc of the function */
	o = arrayadd(&f->asan, sizeof(*o));
	o->desclabel = o->desc = NULL;
	if (fake) {
		asanraw(f, f->start, ISTOREL, 0, mkintconst(ASANFRAMEMAGIC), base);
		o->desclabel = xmalloc(32);
		snprintf(o->desclabel, 32, "asandesc.%u", ++asandescs);
		p = funcinst(f, IADD, ptrclass, base, mkintconst(8));
		asanraw(f, f->start, ISTOREL, 0, asanfn(o->desclabel), p);
		p = funcinst(f, IADD, ptrclass, base, mkintconst(16));
		asanraw(f, f->start, ISTOREL, 0, f->decl->value, p);
		nl = xmalloc(strlen(d->name ? d->name : "") + 32);
		sprintf(nl, "%s:%zu", d->name ? d->name : "", d->loc.line);
		o->desc = xmalloc(strlen(nl) + 64);
		sprintf(o->desc, "1 %d %llu %zu %s", ASANRZ, d->type->size, strlen(nl), nl);
	}
	f->end = end;
	/* the poison is at the declaration, not in the entry block: a return that comes before this declaration never poisons it */
	asancall(f, "__asan_unpoison_memory_region", base, mkintconst(total));
	asancall(f, "__asan_poison_memory_region", base, left);
	asancall(f, "__asan_poison_memory_region", right, rlen);
	o->base = base;
	o->size = total;
	o->obj = obj;
	o->obj8 = size8;
	o->block = asantop(f);
	o->objslot = o->sizeslot = NULL;
	o->fake = fake;
	o->fsize = fake ? frame : 0;
	o->fclass = cls;
	d->value = obj;
}

/* an instruction appended to block b as is: no access check (funcinst checks loads and stores), for the bookkeeping below */
static struct value *
asanraw(struct func *f, struct block *b, int op, int class, struct value *arg0, struct value *arg1)
{
	struct inst *inst;

	inst = mkinst(f, op, class, arg0, arg1);
	arrayaddptr(&b->insts, inst);
	return &inst->res;
}

/*
-fsanitize=address: a dynamic allocation (alloca, a variable-length array) is not in the entry block, so its redzones cannot
be unpoisoned in funcret by a temporary that dominates every return. asanlo and asanhi are two entry-block slots (created
at the first dynamic allocation, as softtemp does) that hold the lowest base and the highest end of this function's
dynamic allocations. QBE's alloc only moves the stack down, so the latest base is the lowest, and asanhi is the maximum,
kept branch-free: d = end - hi; hi += d & ~(d >> 63). They start at 0, and asandynret tests lo for it.
*/
static void
asanslots(struct func *f)
{
	f->asanlo = asanraw(f, f->start, IALLOC8, ptrclass, mkintconst(8), NULL);
	f->asanhi = asanraw(f, f->start, IALLOC8, ptrclass, mkintconst(8), NULL);
	asanraw(f, f->start, ISTOREL, 0, mkintconst(0), f->asanlo);
	asanraw(f, f->start, ISTOREL, 0, mkintconst(0), f->asanhi);
}

/*
-fsanitize=address: a dynamic allocation of size bytes in the current block, laid out as asanalloc lays out a stack object
(redzones of ASANRZ bytes on each side, the size rounded up to 8). The whole allocation is unpoisoned, then the redzones
are poisoned, here at the allocation: a return before it never poisons it. QBE does not reclaim the allocation until the
function returns (a loop allocates again on each pass), so asandynret unpoisons [asanlo, asanhi) at each return.
Returns the object's address.
*/
static struct value *
asandynalloc(struct func *f, struct value *size, bool scoped)
{
	struct value *size8, *total, *base, *obj, *right, *end, *h, *d, *m;
	struct asanobj *o;

	if (!f->asanlo)
		asanslots(f);
	size8 = funcinst(f, IAND, ptrclass, funcinst(f, IADD, ptrclass, size, mkintconst(7)), mkintconst(-8));
	total = funcinst(f, IADD, ptrclass, size8, mkintconst(2 * ASANRZ));
	base = funcinst(f, IALLOC16, ptrclass, total, NULL);
	obj = funcinst(f, IADD, ptrclass, base, mkintconst(ASANRZ));
	right = funcinst(f, IADD, ptrclass, obj, size8);
	asancall(f, "__asan_unpoison_memory_region", base, total);
	asancall(f, "__asan_poison_memory_region", base, mkintconst(ASANRZ));
	asancall(f, "__asan_poison_memory_region", right, mkintconst(ASANRZ));
	asanraw(f, f->end, ISTOREL, 0, base, f->asanlo);
	end = funcinst(f, IADD, ptrclass, base, total);
	h = asanraw(f, f->end, ILOADL, ptrclass, f->asanhi, NULL);
	d = funcinst(f, ISUB, ptrclass, end, h);
	m = funcinst(f, ISAR, ptrclass, d, mkintconst(63));
	m = funcinst(f, IXOR, ptrclass, m, mkintconst(-1));
	d = funcinst(f, IAND, ptrclass, d, m);
	h = funcinst(f, IADD, ptrclass, h, d);
	asanraw(f, f->end, ISTOREL, 0, h, f->asanhi);
	/* a variable-length array lives until the end of its block, so it is poisoned where that block ends (asanend, asanleave,
	 * asangoto). An alloca lives until the function returns, as C requires: it is not a scope object. */
	if (!scoped)
		return obj;
	o = arrayadd(&f->asan, sizeof(*o));
	o->base = NULL;
	o->size = 0;
	o->obj = NULL;
	o->obj8 = 0;
	o->fake = NULL;
	o->desclabel = o->desc = NULL;
	o->block = asantop(f);
	o->objslot = asanraw(f, f->start, IALLOC8, ptrclass, mkintconst(8), NULL);
	o->sizeslot = asanraw(f, f->start, IALLOC8, ptrclass, mkintconst(8), NULL);
	asanraw(f, f->start, ISTOREL, 0, mkintconst(0), o->objslot);
	asanraw(f, f->start, ISTOREL, 0, mkintconst(0), o->sizeslot);
	asanraw(f, f->end, ISTOREL, 0, obj, o->objslot);
	asanraw(f, f->end, ISTOREL, 0, size8, o->sizeslot);
	return obj;
}

/*
-fsanitize=address, use after return: the fake frames (asanalloc) are given back where the function returns, as gcc's
__asan_stack_free_N does: libasan poisons the frame with the stack-use-after-return shadow, so a pointer into it that is
read later is reported. __asan_stack_free_N dereferences its pointer, so each frame is freed on a branch that skips it
when the object is in the real frame. Every return block b becomes a chain: for each fake frame, jnz fake, free, next; then
the return, in a block r that takes b's jump (asanrets then names r, for asandynret). Called by emitfunc after the body.
*/
static void
asanfree(struct func *f)
{
	struct block **bp, *b, *u, *n, *r, *cur;
	struct asanobj *o;
	size_t i, j, nret = f->asanrets.len / sizeof(*bp), nobj = f->asan.len / sizeof(*o);
	char *name;

	for (i = 0; i < nret; i++) {
		bp = (struct block **)f->asanrets.val + i;
		b = *bp;
		r = mkblock("asanret");
		r->jump = b->jump;
		cur = b;
		for (j = 0; j < nobj; j++) {
			o = (struct asanobj *)f->asan.val + j;
			if (!o->fake)
				continue;
			u = mkblock("asanfree");
			n = mkblock("asanfreenext");
			cur->jump.kind = JUMP_JNZ;
			cur->jump.arg = o->fake;
			cur->jump.blk[0] = u;
			cur->jump.blk[1] = n;
			funclabel(f, u);
			name = xmalloc(32);
			snprintf(name, 32, "__asan_stack_free_%d", o->fclass);
			asancall(f, name, o->fake, mkintconst(o->fsize));
			u->jump.kind = JUMP_JMP;
			u->jump.blk[0] = n;
			funclabel(f, n);
			cur = n;
		}
		if (cur == b)
			continue;
		cur->jump.kind = JUMP_JMP;
		cur->jump.blk[0] = r;
		funclabel(f, r);
		*bp = r;
	}
}

/*
-fsanitize=address: the returns of a function with dynamic allocations. Each return block b (recorded by funcret) becomes
jnz lo, unpoison, ret; unpoison: call __asan_unpoison_memory_region(lo, hi - lo); jmp ret. A return that ran before the
first dynamic allocation at run time (a return before a VLA declaration, or one earlier in a loop body) has lo == 0, and
then there is nothing to unpoison: the branch skips the call instead of passing it an empty range at address 0.
Called by emitfunc after the function body is generated, when every return is known. f->end is the last block.
*/
static void
asandynret(struct func *f)
{
	struct block **bp, *b, *u, *r;
	struct value *lo, *hi;
	size_t i, n = f->asanrets.len / sizeof(*bp);

	for (i = 0; i < n; i++) {
		bp = (struct block **)f->asanrets.val + i;
		b = *bp;
		u = mkblock("asanunpoison");
		r = mkblock("asanret");
		lo = asanraw(f, b, ILOADL, ptrclass, f->asanlo, NULL);
		r->jump = b->jump;
		b->jump.kind = JUMP_JNZ;
		b->jump.arg = lo;
		b->jump.blk[0] = u;
		b->jump.blk[1] = r;
		funclabel(f, u);
		hi = asanraw(f, u, ILOADL, ptrclass, f->asanhi, NULL);
		asancall(f, "__asan_unpoison_memory_region", lo, funcinst(f, ISUB, ptrclass, hi, lo));
		u->jump.kind = JUMP_JMP;
		u->jump.blk[0] = r;
		funclabel(f, r);
	}
}

/*
-fsanitize=address, use after scope: when a block is left, the objects it declared are poisoned as stack-use-after-scope
(__asan_poison_stack_memory, the marker gcc's own instrumentation uses), and the declaration that re-enters the block
unpoisons them again (asanalloc, at the declaration). The ways out covered here are the normal end of the block (asanend,
after its join point), break and continue (asanleave), and goto (asangoto, asanlabel). A return needs nothing: funcret
unpoisons the whole frame and nothing of it runs after. A goto is how EDG lowers break, continue and the exits of a switch
in C++ (`goto __T1;` to a label after the loop), so the goto case matters as much as asanleave.
*/
/* the address and size of o's object, as values of the current block (a dynamic block reads its slots) */
static void
asanobjrange(struct func *f, struct asanobj *o, struct value **obj, struct value **size)
{
	if (!o->objslot) {
		*obj = o->obj;
		*size = mkintconst(o->obj8);
		return;
	}
	*obj = asanraw(f, f->end, ILOADL, ptrclass, o->objslot, NULL);
	*size = asanraw(f, f->end, ILOADL, ptrclass, o->sizeslot, NULL);
}

static void
asanpoisonobj(struct func *f, struct asanobj *o)
{
	struct value *obj, *size;

	asanobjrange(f, o, &obj, &size);
	asancall(f, "__asan_poison_stack_memory", obj, size);
}

static void
asanunpoisonobj(struct func *f, struct asanobj *o)
{
	struct value *obj, *size;

	asanobjrange(f, o, &obj, &size);
	asancall(f, "__asan_unpoison_memory_region", obj, size);
}

/* the objects of the blocks in set that are not open in keep (the blocks a jump leaves, or enters): poisoned or unpoisoned */
static void
asanmove(struct func *f, const struct array *set, const struct array *keep, bool poison)
{
	size_t i;
	struct asanobj *o;

	for (i = 0; i < f->asan.len / sizeof(*o); i++) {
		o = (struct asanobj *)f->asan.val + i;
		if (asaninset(set, o->block) && !asaninset(keep, o->block)) {
			if (poison)
				asanpoisonobj(f, o);
			else
				asanunpoisonobj(f, o);
		}
	}
}

/* a block begins: its declarations are numbered (asanalloc records the number) and it is open until asanend */
void
asanbegin(struct func *f)
{
	if (asanon)
		asanadd(&f->asanopen, ++f->asanblocks);
}

/* the number of stack objects with redzones registered so far: the mark of a loop or switch body (asanleave) */
size_t
asanmark(struct func *f)
{
	return f->asan.len / sizeof(struct asanobj);
}

/* the normal end of a block, after its join point and before its scope is deleted: poison the objects it declared */
void
asanend(struct func *f)
{
	size_t i;
	unsigned top;

	if (!asanon)
		return;
	top = asantop(f);
	if (!f->end->jump.kind) {
		for (i = 0; i < asanmark(f); i++) {
			struct asanobj *o = (struct asanobj *)f->asan.val + i;
			if (o->block == top)
				asanpoisonobj(f, o);
		}
	}
	f->asanopen.len -= sizeof(unsigned);
}

/*
A goto to a label (asangoto), and the label (asanlabel). The blocks a jump leaves have their objects poisoned, and the blocks
it enters have theirs unpoisoned: a block is open at a point only if its objects are in scope there (C++ allows a jump into
a block past a declaration without initializer). A backward goto knows the label's open blocks; a forward goto does not,
so it records the blocks open where it is (asanfrom, their union; asanall, their intersection) and the label does the work
once it is defined. Every forward goto leaves only blocks that end before the label, so their objects are all registered.
*/
static struct array *
asanset(struct array **p)
{
	if (!*p) {
		*p = xmalloc(sizeof(**p));
		**p = (struct array){0};
	}
	return *p;
}

/* a becomes its intersection with b: the members of a that are also in b */
static void
asanintersect(struct array *a, const struct array *b)
{
	size_t i, n = 0, len = a->len / sizeof(unsigned);
	unsigned *v = a->val;

	for (i = 0; i < len; i++)
		if (asaninset(b, v[i]))
			v[n++] = v[i];
	a->len = n * sizeof(unsigned);
}

void
asangoto(struct func *f, struct gotolabel *g)
{
	size_t i;

	if (!asanon)
		return;
	if (g->defined) {
		asanmove(f, &f->asanopen, g->asanopen, true);
		asanmove(f, g->asanopen, &f->asanopen, false);
		return;
	}
	if (!g->asanall) {
		asanset(&g->asanall);
		for (i = 0; i < f->asanopen.len / sizeof(unsigned); i++)
			asanadd(g->asanall, ((unsigned *)f->asanopen.val)[i]);
	} else {
		asanintersect(g->asanall, &f->asanopen);
	}
	for (i = 0; i < f->asanopen.len / sizeof(unsigned); i++)
		asanadd(asanset(&g->asanfrom), ((unsigned *)f->asanopen.val)[i]);
}

void
asanlabel(struct func *f, struct gotolabel *g)
{
	size_t i;

	if (!asanon)
		return;
	if (g->asanfrom) {
		asanmove(f, g->asanfrom, &f->asanopen, true);
		asanmove(f, &f->asanopen, g->asanall, false);
	}
	asanset(&g->asanopen);
	g->asanopen->len = 0;
	for (i = 0; i < f->asanopen.len / sizeof(unsigned); i++)
		asanadd(g->asanopen, ((unsigned *)f->asanopen.val)[i]);
}

/* the dispatch of a switch enters its cases from the switch statement, where the blocks open are recorded (asanswitch) */
void
asanswitch(struct func *f, struct switchcases *sw)
{
	size_t i;

	sw->asanopen = NULL;
	if (!asanon)
		return;
	asanset(&sw->asanopen);
	for (i = 0; i < f->asanopen.len / sizeof(unsigned); i++)
		asanadd(sw->asanopen, ((unsigned *)f->asanopen.val)[i]);
}

/* a case or default label (after funclabel): the blocks open here that the switch was not in are entered, as for a goto */
void
asancase(struct func *f, struct switchcases *sw)
{
	if (asanon)
		asanmove(f, &f->asanopen, sw->asanopen, false);
}

/*
a break or continue: the objects declared in the body since its mark (asanmark, taken as the body begins) leave their blocks.
Objects of blocks that already ended are poisoned again, which changes nothing; the objects declared before the body (a for
statement's, say) are poisoned where the loop or switch ends, which every break reaches.
*/
void
asanleave(struct func *f, size_t mark)
{
	size_t i;

	if (asanon)
		for (i = mark; i < asanmark(f); i++)
			asanpoisonobj(f, (struct asanobj *)f->asan.val + i);
}

/*
A call of setjmp (or _setjmp, __sigsetjmp, sigsetjmp, the names glibc and EDG use; EDG's try and throw are a _setjmp and a
longjmp). The call returns twice, the second time from a longjmp that left blocks since the call, and the code after it
cannot tell which way it returned. The longjmp itself is not seen here, and nothing runs between it and the return, so the
return is where the objects it left are poisoned. An object is in scope at the call only if its block is open there, so
every other object of the function is out of scope at the return (C: a block's objects are out of scope outside it), and
asanfinish poisons them in pad, which both returns pass through. The objects of the open blocks are left alone. A block
entered again unpoisons its objects at their declaration, as before. This needs no record of the longjmp, which is what
makes it work for a longjmp in another function that lands in this one too, and for EDG's throw (its runtime runs the
destructors of the left objects before it longjmps, so poisoning at the throw would poison objects still in use).
*/
static bool
asansetjmpname(const char *name)
{
	return !strcmp(name, "setjmp") || !strcmp(name, "_setjmp") || !strcmp(name, "sigsetjmp") || !strcmp(name, "__sigsetjmp");
}

static void
asansetjmp(struct func *f)
{
	struct asanjmp *j;
	struct block *pad, *next;
	struct array *open = NULL;
	size_t i, n = f->asanopen.len / sizeof(unsigned);

	asanset(&open);
	for (i = 0; i < n; i++)
		asanadd(open, ((unsigned *)f->asanopen.val)[i]);
	pad = mkblock("asansetjmp");
	next = mkblock("asansetjmp_next");
	funcjmp(f, pad);
	funclabel(f, pad);
	funclabel(f, next);
	j = arrayadd(&f->asanjmps, sizeof(*j));
	j->pad = pad;
	j->next = next;
	j->open = open;
}

/*
The pads of the setjmp calls (asansetjmp), filled now that every object of the function is known: an object declared after
the call, in a block not open there, is poisoned too, and its declaration unpoisons it. A pad has no jump until here, since
funcinst appends only to a block without one, so it is filled first and then jumps to the block after its call.
*/
static void
asanfinish(struct func *f)
{
	struct block *end = f->end;
	struct asanjmp *j;
	struct asanobj *o;
	size_t i, k, nobj, njmp = f->asanjmps.len / sizeof(*j);

	for (k = 0; k < njmp; k++) {
		j = (struct asanjmp *)f->asanjmps.val + k;
		f->end = j->pad;
		nobj = f->asan.len / sizeof(*o);
		for (i = 0; i < nobj; i++) {
			o = (struct asanobj *)f->asan.val + i;
			/* block 0 is the parameters (asantop): in scope everywhere, so never poisoned */
			if (o->block && !asaninset(j->open, o->block))
				asanpoisonobj(f, o);
		}
		funcjmp(f, j->next);
	}
	f->end = end;
}

void
funcalloc(struct func *f, struct decl *d)
{
	enum instkind op;
	struct block *end;
	struct value *v;
	int align;

	assert(!d->type->incomplete);
	calcvla(f, d->type);
	end = f->end;
	if (asanon && d->type->size && !(d->type->prop & PROPVM)) {
		asanalloc(f, d);
		f->end = end;
		return;
	}
	/* a variable-length array: allocated where it is declared, as below, with redzones (asandynalloc) */
	if (asanon && !d->type->size && (d->type->prop & PROPVM) && d->u.obj.align <= 16) {
		assert(d->type->kind == TYPEARRAY);
		assert(d->type->u.array.size);
		d->value = asandynalloc(f, d->type->u.array.size, true);
		return;
	}
	if (d->type->size) {
		f->end = f->start;
		v = mkintconst(d->type->size);
	} else if (d->type->prop & PROPVM) {
		assert(d->type->kind == TYPEARRAY);
		assert(d->type->u.array.size);
		v = d->type->u.array.size;
	} else {
		/* zero-size object: an empty struct or union, or an array of them (GNU extension) */
		f->end = f->start;
		v = mkintconst(0);
	}
	align = d->u.obj.align;
	switch (align) {
	case 1:
	case 2:
	case 4:  op = IALLOC4; break;
	case 8:  op = IALLOC8; break;
	default: v = funcinst(f, IADD, ptrclass, v, mkintconst(align - 16));  /* fallthrough */
	case 16: op = IALLOC16; break;
	}
	v = funcinst(f, op, ptrclass, v, NULL);
	if (align > 16) {
		/* TODO: implement alloc32 in QBE and use that instead */
		v = funcinst(f, IADD, ptrclass, v, mkintconst(align - 16));
		v = funcinst(f, IAND, ptrclass, v, mkintconst(-align));
	}
	d->value = v;
	f->end = end;
}

static void
funccopy(struct func *f, struct value *dst, struct value *src, unsigned long long size, int align)
{
	enum instkind load, store;
	int class;
	struct value *tmp, *inc;
	unsigned long long off;

	assert((align & align - 1) == 0);
	/* an empty struct or union (size 0, see cproc-empty-struct.patch) has nothing to copy; the loop
	 * below always runs once and would write one byte past the zero-size destination */
	if (size == 0)
		return;
	/* A larger copy is one blit, which QBE expands into word copies at fixed offsets (or a call to memmove).
	 * The unit by unit copy below makes a chain of address temporaries, a pair per unit: a 2 KB array of bytes
	 * was 4096 instructions, and their temporaries were spilled to the stack (16 KB of spill slots in one
	 * function of mold 3 built through mrustc). Under -fsanitize=address the copy stays unit by unit, so that
	 * each access is checked. */
	if (size > 16 && !asanon && size <= 0x7fffffff) {
		struct inst *inst;

		inst = mkinst(f, IBLIT, 0, src, dst);
		inst->arg[2] = mkintconst(size);
		if (f->end->jump.kind)
			funclabel(f, mkblock("dead"));
		arrayaddptr(&f->end->insts, inst);
		return;
	}
	class = 'w';
	switch (align) {
	case 1: load = ILOADUB, store = ISTOREB; break;
	case 2: load = ILOADUH, store = ISTOREH; break;
	case 4: load = ILOADW, store = ISTOREW; break;
	default:
		if (targ->ilp32) {   /* no 64-bit integers: by words */
			load = ILOADW, store = ISTOREW, align = 4;
			break;
		}
		load = ILOADL, store = ISTOREL, align = 8, class = 'l';
		break;
	}
	inc = mkintconst(align);
	off = 0;
	for (;;) {
		tmp = funcinst(f, load, class, src, NULL);
		funcinst(f, store, 0, tmp, dst);
		off += align;
		if (off >= size)
			break;
		src = funcinst(f, IADD, ptrclass, src, inc);
		dst = funcinst(f, IADD, ptrclass, dst, inc);
	}
}

/*
cproc -V: volatile accesses go through opaque helpers in the inline-asm side file (nfcxx_vload4: movl (%rdi), %eax),
one call per access. QBE has no volatile; its load optimization forwards and merges plain loads (a polling loop's
load could be hoisted out of it), and a call is something it never forwards, merges or removes. Scalars of 1, 2, 4
and 8 bytes; a volatile bit-field or aggregate is still refused for stores. Returns null when the access is not one
of these (the caller does an ordinary access).
*/
bool volatilecalls;

static struct value *
funcvolatile(struct func *f, struct type *t, struct lvalue lval, struct value *v)
{
	static bool done[2][9];
	static const char *const ld[9] = {[1] = "movzbl (%rdi), %eax", [2] = "movzwl (%rdi), %eax",
		[4] = "movl (%rdi), %eax", [8] = "movq (%rdi), %rax"};
	static const char *const st[9] = {[1] = "movb %sil, (%rdi)", [2] = "movw %si, (%rdi)",
		[4] = "movl %esi, (%rdi)", [8] = "movq %rsi, (%rdi)"};
	/* i386 (QBE's i386_regparm3; cdecl takes them from the stack, the same bodies at 4(%esp) and up): the value of an 8-byte
	 * access is the pair %edx:%eax (a load returns it in %edx:%eax, a store takes it in %edx and %ecx) */
	static const char *const i386ld[9] = {[1] = "\tmovzbl (%eax), %eax\n", [2] = "\tmovzwl (%eax), %eax\n",
		[4] = "\tmovl (%eax), %eax\n", [8] = "\tmovl 4(%eax), %edx\n\tmovl (%eax), %eax\n"};
	static const char *const i386st[9] = {[1] = "\tmovb %dl, (%eax)\n", [2] = "\tmovw %dx, (%eax)\n",
		[4] = "\tmovl %edx, (%eax)\n", [8] = "\tmovl %edx, (%eax)\n\tmovl %ecx, 4(%eax)\n"};
	/* cdecl (target i386): the address at 4(%esp), a store's value after it, and the same bodies after these loads */
	static const char *const i386cdecl[2][9] = {
		[0] = {[1] = "\tmovl 4(%esp), %eax\n", [2] = "\tmovl 4(%esp), %eax\n", [4] = "\tmovl 4(%esp), %eax\n",
			[8] = "\tmovl 4(%esp), %eax\n"},
		[1] = {[1] = "\tmovl 4(%esp), %eax\n\tmovl 8(%esp), %edx\n", [2] = "\tmovl 4(%esp), %eax\n\tmovl 8(%esp), %edx\n",
			[4] = "\tmovl 4(%esp), %eax\n\tmovl 8(%esp), %edx\n",
			[8] = "\tmovl 4(%esp), %eax\n\tmovl 8(%esp), %edx\n\tmovl 12(%esp), %ecx\n"},
	};
	static const int ldop[9] = {[1] = ILOADUB, [2] = ILOADUH, [4] = ILOADW, [8] = ILOADL};
	static const int stop[9] = {[1] = ISTOREB, [2] = ISTOREH, [4] = ISTOREW, [8] = ISTOREL};
	struct value *fn, *r;
	size_t size;
	bool store = v != NULL, agg, i386, regparm;
	int class;

	if (!volatilecalls || !asmout || lval.bits.before || lval.bits.after)
		return NULL;
	regparm = strcmp(targ->name, "i386_regparm3") == 0;
	i386 = regparm || strcmp(targ->name, "i386") == 0;
	if (!i386 && strcmp(targ->name, "x86_64-sysv") != 0)
		error(&tok.loc, "volatile access helpers (-V) are only supported on x86_64 and i386");
	if (t->kind == TYPEPOINTER)
		t = &typeulong;
	/* an aggregate of 1, 2, 4 or 8 bytes (the kernel's pte_t through WRITE_ONCE and READ_ONCE) is one access of
	 * that size, as gcc makes it: its value is the address of its bytes */
	agg = t->kind == TYPESTRUCT || t->kind == TYPEUNION || t->kind == TYPEARRAY;
	if (!agg && (!(t->prop & PROPINT) || t->prop & PROPSOFT))
		return NULL;
	size = t->size;
	if (size != 1 && size != 2 && size != 4 && size != 8)
		return NULL;
	if (!done[store][size]) {
		if (i386)   /* the arguments in %eax, %edx and %ecx (i386_regparm3), or on the stack (i386, cdecl) */
			fprintf(asmout, "#nfcxx:keep\n\t.text\n\t.p2align 4\nnfcxx_v%s%zu:\n%s%s\tret\n", store ? "store" : "load", size,
				regparm ? "" : i386cdecl[store][size], store ? i386st[size] : i386ld[size]);
		else
			fprintf(asmout, "#nfcxx:keep\n\t.text\n\t.p2align 4\nnfcxx_v%s%zu:\n\t%s\n\tret\n", store ? "store" : "load", size,
				store ? st[size] : ld[size]);
		done[store][size] = true;
	}
	fn = xmalloc(sizeof(*fn));
	*fn = (struct value){.kind = VALUE_GLOBAL};
	fn->u.name = xmalloc(24);
	snprintf(fn->u.name, 24, "nfcxx_v%s%zu", store ? "store" : "load", size);
	class = size == 8 ? 'l' : 'w';
	if (store && agg)
		v = funcinst(f, ldop[size], class, v, NULL);   /* the source's bytes, then one store of them */
	if (store) {
		funcinst(f, ICALL, 0, fn, NULL);
		funcinst(f, IARG, ptrclass, lval.addr, NULL);
		funcinst(f, IARG, class, v, NULL);
		return v;
	}
	r = funcinst(f, ICALL, class, fn, NULL);
	funcinst(f, IARG, ptrclass, lval.addr, NULL);
	if (agg) {   /* one load of the bytes, into a temporary that is the value */
		struct decl *tmp = mkdecl(NULL, DECLOBJECT, t, QUALNONE, LINKNONE);

		tmp->u.obj.storage = SDAUTO;
		funcalloc(f, tmp);
		funcinst(f, stop[size], 0, r, tmp->value);
		return tmp->value;
	}
	/* the helper zero-extends; a signed char or short is sign-extended as loadsb/loadsh would */
	if (size < 4 && t->u.arith.issigned)
		r = funcinst(f, size == 1 ? IEXTSB : IEXTSH, 'w', r, NULL);
	return r;
}

static struct value *
funcstore(struct func *f, struct type *t, enum typequal tq, struct lvalue lval, struct value *v)
{
	struct value *r;
	enum typeprop tp;
	unsigned long long mask;
	struct qbetype qt;
	int bits;

	if (tq & QUALVOLATILE) {
		if (funcvolatile(f, t, lval, v))
			return v;
		error(&tok.loc, "volatile store is not yet supported");
	}
	if (tq & QUALCONST)
		error(&tok.loc, "cannot store to 'const' object");
	tp = t->prop;
	assert(!lval.bits.before && !lval.bits.after || tp & PROPINT);
	r = v;
	if (tp & PROPSOFT) {
		funccopy(f, lval.addr, v, t->size, t->align);
		return r;
	}
	switch (t->kind) {
	case TYPESTRUCT:
	case TYPEUNION:
	case TYPEARRAY:
		funccopy(f, lval.addr, v, t->size, t->align);
		break;
	case TYPEPOINTER:
		t = &typeulong;
		/* fallthrough */
	default:
		assert(tp & PROPSCALAR);
		qt = qbetype(t);
		bits = lval.bits.before + lval.bits.after;
		if (bits) {
			mask = 0xffffffffffffffffu >> 64 - t->size * 8 + bits << lval.bits.before;
			v = funcinst(f, ISHL, qt.base, v, mkintconst(lval.bits.before));
			r = funcbits(f, t, v, lval.bits);
			v = funcinst(f, IAND, qt.base, v, mkintconst(mask));
			v = funcinst(f, IOR, qt.base, v,
				funcinst(f, IAND, qt.base,
					funcinst(f, qt.load, qt.base, lval.addr, NULL),
					mkintconst(~mask)
				)
			);
		}
		funcinst(f, qt.store, 0, v, lval.addr);
		break;
	}
	return r;
}

static struct value *funcload(struct func *, struct type *, struct lvalue);

/* a load from an lvalue with qualifiers tq: a volatile scalar goes through funcvolatile under cproc -V */
static struct value *
funcloadq(struct func *f, struct type *t, enum typequal tq, struct lvalue lval)
{
	struct value *v;

	if (tq & QUALVOLATILE && (v = funcvolatile(f, t, lval, NULL)))
		return funcbits(f, t, v, lval.bits);
	/* -V: a volatile access it cannot make one call is refused, not left to QBE as a plain load */
	if (tq & QUALVOLATILE && volatilecalls)
		error(&tok.loc, "volatile load of this type is not yet supported (-V covers scalars and aggregates of 1, 2, 4 and 8 bytes)");
	return funcload(f, t, lval);
}

static struct value *
funcload(struct func *f, struct type *t, struct lvalue lval)
{
	struct value *v;
	struct qbetype qt;

	if (t->prop & PROPSOFT)
		return lval.addr;
	switch (t->kind) {
	case TYPESTRUCT:
	case TYPEUNION:
	case TYPEARRAY:
		return lval.addr;
	}
	qt = qbetype(t);
	v = funcinst(f, qt.load, qt.base, lval.addr, NULL);
	return funcbits(f, t, v, lval.bits);
}

struct func *
mkfunc(struct decl *decl, char *name, struct type *t, struct scope *s)
{
	struct func *f;
	struct decl *d;
	struct value *v, *r;

	f = xmalloc(sizeof(*f));
	f->decl = decl;
	f->name = name;
	f->type = t;
	f->start = f->end = mkblock("start");
	f->lastid = 0;
	f->ehobjs = (struct array){0};
	f->cleanups = f->cleangotos = (struct array){0};
	f->shape = (struct funcshape){0};
	f->asan = (struct array){0};
	f->asanfile = NULL;
	f->asanrets = (struct array){0};
	f->asanlo = f->asanhi = NULL;
	f->asanopen = (struct array){0};
	f->asanblocks = 0;
	f->asanjmps = (struct array){0};
	mapinit(&f->gotos, 8);
	if (t->u.func.abi)
		error(&tok.loc, "a function with the %s calling convention is not supported", t->u.func.abi);
	if (targ->ilp32) {
		if (softvalue(t->base))
			error(&tok.loc, "a function returning %s is not supported on %s", t->base->kind == TYPELDOUBLE ? "long double" : "__float128", targ->name);
		for (d = t->u.func.params; d; d = d->next)
			if (softvalue(d->type))
				error(&tok.loc, "a %s parameter is not supported on %s", d->type->kind == TYPELDOUBLE ? "long double" : "__float128", targ->name);
	}
	emittype(t->base);

	/* allocate space for parameters */
	f->paramtemps = xreallocarray(NULL, t->u.func.nparam, sizeof *f->paramtemps);
	for (d = t->u.func.params, v = f->paramtemps; d; d = d->next, ++v) {
		emittype(d->type);
		functemp(f, v);
		if(!d->name)
			continue;
		if (d->type->kind == TYPEUNION && d->type->u.structunion.transparent) {
			/* passed as its first member (abiparam): stored into the union */
			funcalloc(f, d);
			funcstore(f, d->type->u.structunion.members->type, QUALNONE, (struct lvalue){d->value}, v);
		} else if (d->type->value) {
			d->value = v;
		} else {
			funcalloc(f, d);
			r = v;
			if (d->type->kind == TYPEFLOAT16)
				r = f16fromsse(f, v);
			funcstore(f, d->type, QUALNONE, (struct lvalue){d->value}, r);
		}
	}

	t = mkarraytype(&typechar, QUALCONST, strlen(name) + 1);
	d = mkdecl("__func__", DECLOBJECT, t, QUALNONE, LINKNONE);
	d->u.obj.storage = SDSTATIC;
	d->value = mkglobal(d);
	scopeputdecl(s, d);
	f->namedecl = d;

	funclabel(f, mkblock("body"));

	return f;
}

void
delfunc(struct func *f)
{
	struct block *b;
	struct inst **inst;

	while (b = f->start) {
		f->start = b->next;
		arrayforeach (&b->insts, inst)
			free(*inst);
		free(b->insts.val);
		free(b);
	}
	mapfree(&f->gotos, free);
	free(f);
}

struct type *
functype(struct func *f)
{
	return f->type;
}

void
funclabel(struct func *f, struct block *b)
{
	f->end->next = b;
	f->end = b;
}

/*
GNU statement expressions. The statements are parsed into a chain of blocks that is not part of the function yet
(funcdetach makes a fresh current block and returns the one to come back to; funcreattach ends the chain and returns
its last block). funcexpr links the chain in where the expression is evaluated, so the statements run only where and
when the expression does: in the operand of &&, || or ?: that is taken, and not at all under sizeof or typeof, or in the
operand __builtin_choose_expr does not choose.
*/
struct block *
funcdetach(struct func *f, struct block **first)
{
	struct block *saved = f->end;

	*first = f->end = mkblock("stmtexpr");
	return saved;
}

struct block *
funcreattach(struct func *f, struct block *saved)
{
	struct block *last = f->end;

	f->end = saved;
	return last;
}

void
funcjmp(struct func *f, struct block *l)
{
	struct block *b = f->end;

	if (!b->jump.kind) {
		b->jump.kind = JUMP_JMP;
		b->jump.blk[0] = l;
	}
}

void
funcjnz(struct func *f, struct value *v, struct type *t, struct block *l1, struct block *l2)
{
	struct block *b = f->end;

	if (b->jump.kind)
		return;
	if (v->kind == VALUE_INTCONST && (!t || t->prop & PROPINT || t->kind == TYPEPOINTER)) {
		/* a constant condition: the other way is not an edge, so what only it reaches is unreachable (emitfunc) */
		unsigned long long c = v->u.i;

		if (t && t->size < 8)
			c &= (1ull << t->size * 8) - 1;
		funcjmp(f, c ? l1 : l2);
		return;
	}
	if (t) {
		assert(t->prop & PROPSCALAR);
		/*
		Ideally we would just do this conversion unconditionally,
		but QBE is not currently able to optimize the conversion
		away for int.
		*/
		if (t->prop & PROPINT && t->size < 4)
			v = convert(f, &typeint, t, v);
		else if (t->prop & PROPFLOAT || t->size > 4)
			v = convert(f, &typebool, t, v);
	}
	b->jump.kind = JUMP_JNZ;
	b->jump.arg = v;
	b->jump.blk[0] = l1;
	b->jump.blk[1] = l2;
}

void
funcret(struct func *f, struct value *v)
{
	struct block *b = f->end;
	struct asanobj *o;
	size_t i;

	if (!b->jump.kind) {
		if (v && f->type->base->kind == TYPELDOUBLE) {
			struct softarg pa[1] = {{'l', v}};

			softcall(f, 0, softname(f->type->base, "push"), 1, pa);
			v = NULL;
		}
		if (v && f->type->base->kind == TYPEFLOAT16)
			v = f16tosse(f, v);
		/* -fsanitize=address: the redzones of this frame's objects are addressable again when the frame is left */
		for (i = 0; i < f->asan.len / sizeof(*o); i++) {
			o = (struct asanobj *)f->asan.val + i;
			if (o->base)   /* a dynamic block (asandynalloc) has no base: asandynret unpoisons it */
				asancall(f, "__asan_unpoison_memory_region", o->base, mkintconst(o->size));
		}
		if (asanon) {
			/* the dynamic allocations are only known at the end of the function (asandynret) */
			struct block **r = arrayadd(&f->asanrets, sizeof(*r));
			*r = b;
		}
		b->jump.kind = JUMP_RET;
		b->jump.arg = v;
	}
}

void
funchlt(struct func *f)
{
	struct block *b = f->end;

	if (!b->jump.kind)
		b->jump.kind = JUMP_HLT;
}

struct gotolabel *
funcgoto(struct func *f, char *name)
{
	struct gotolabel *g;
	struct mapkey key;
	size_t idx;

	mapkey(&key, name, strlen(name));
	if (mapput(&f->gotos, &key, &idx)) {
		g = xmalloc(sizeof(*g));
		g->label = mkblock(name);
		g->defined = false;
		g->asanopen = g->asanfrom = g->asanall = NULL;
		g->cleanat = (struct array){0};
		f->gotos.vals[idx].p = g;
	}

	return f->gotos.vals[idx].p;
}

/*
A read of a GNU global register variable. Only %rsp is supported (the kernel's current_stack_pointer): a local helper in
the inline-asm side file returns the caller's stack pointer as it was at the call, which is the value of %rsp at that
point of the caller.
*/
static struct value *
funcregvar(struct func *f, struct decl *d)
{
	static bool emitted;
	static struct value fn = {.kind = VALUE_GLOBAL, .u.name = "nfcxx_read_rsp"};

	if (strcmp(d->regvar, "rsp") != 0 || strcmp(targ->name, "x86_64-sysv") != 0)
		error(&tok.loc, "global register variable '%s' in %%%s: only %%rsp on x86_64 is supported", d->name, d->regvar);
	if (!asmout)
		error(&tok.loc, "global register variable '%s' needs the inline-asm side file (-a)", d->name);
	if (!emitted) {
		fputs("#nfcxx:keep\n\t.text\n\t.p2align 4\nnfcxx_read_rsp:\n\tleaq 8(%rsp), %rax\n\tret\n", asmout);
		emitted = true;
	}
	return funcinst(f, ICALL, 'l', &fn, NULL);
}

/*
__builtin_return_address(0) and __builtin_frame_address(0): a call of a local helper in the inline-asm side file. The
caller is then no leaf, and QBE gives every function that is not a leaf a frame pointer (push %rbp; mov %rsp, %rbp), so
the helper finds the caller's frame in %rbp and its return address at 8(%rbp).
*/
/* the type a parameter is passed as: a GNU transparent union as its first member */
static struct type *
abiparam(struct type *t)
{
	if (t->kind == TYPEUNION && t->u.structunion.transparent)
		return t->u.structunion.members->type;
	return t;
}

/*
A construct of a function body that cproc can only refuse, found while generating code (the parse goes on). Under
cproc -p it is deferred like an asm refusal (funcasm): kept with the block, and reported only if the block can be
reached and pruning keeps the function -- the kernel's headers have static inline helpers nothing calls.
*/
static void
funcrefuse(struct func *f, const char *fmt, ...)
{
	va_list ap;
	char body[400], msg[512];

	va_start(ap, fmt);
	vsnprintf(body, sizeof body, fmt, ap);
	va_end(ap);
	if (!prune)
		error(&tok.loc, "%s", body);
	snprintf(msg, sizeof msg, "%s:%zu:%zu: error: %s", tok.loc.file, tok.loc.line, tok.loc.col, body);
	if (!f->end->lazyerror && !f->end->jump.kind) {
		f->end->lazyerror = xmalloc(strlen(msg) + 1);
		strcpy(f->end->lazyerror, msg);
	}
}

static struct value *
funcframeinfo(struct func *f, bool ret)
{
	static bool emitted[2];
	static struct value fn[2] = {
		{.kind = VALUE_GLOBAL, .u.name = "nfcxx_frame_address"},
		{.kind = VALUE_GLOBAL, .u.name = "nfcxx_return_address"},
	};

	if (!asmout || strcmp(targ->name, "x86_64-sysv") != 0)
		error(&tok.loc, "__builtin_%s_address is only supported on x86_64 ELF (the inline-asm side file, -a)", ret ? "return" : "frame");
	if (!emitted[ret]) {
		fprintf(asmout, "#nfcxx:keep\n\t.text\n\t.p2align 4\n%s:\n\t%s\n\tret\n", fn[ret].u.name,
			ret ? "movq 8(%rbp), %rax" : "movq %rbp, %rax");
		emitted[ret] = true;
	}
	return funcinst(f, ICALL, 'l', &fn[ret], NULL);
}

static struct lvalue
funclval(struct func *f, struct expr *e)
{
	struct lvalue lval = {0};
	struct decl *d;

	if (e->kind == EXPRBITFIELD) {
		lval.bits = e->u.bitfield.bits;
		e = e->base;
	}
	switch (e->kind) {
	case EXPRIDENT:
		d = e->u.ident.decl;
		if (d->kind != DECLOBJECT && d->kind != DECLFUNC)
			error(&tok.loc, "identifier '%s' is not an object or function", d->name);
		if (d->kind == DECLOBJECT && d->regvar && d->u.obj.storage != SDAUTO)
			error(&tok.loc, "global register variable '%s' cannot be assigned or have its address taken", d->name);
		if (d == f->namedecl) {
			fputs("data ", stdout);
			emitname(d->value);
			printf(" = { b \"%s\", b 0 }\n", f->name);
			f->namedecl = NULL;
		}
		lval.addr = d->value;
		break;
	case EXPRSTRING:
		d = stringdecl(e);
		lval.addr = d->value;
		break;
	case EXPRCOMPOUND:
		if (e->toeval)
			funcexpr(f, e->toeval);
		d = e->u.compound.decl;
		funcinit(f, d, e->u.compound.init, true);
		lval.addr = d->value;
		break;
	case EXPRUNARY:
		if (e->op != TMUL)
			error(&tok.loc, "expression is not an object");
		lval.addr = funcexpr(f, e->base);
		break;
	default:
		if (e->type->kind != TYPESTRUCT && e->type->kind != TYPEUNION)
			error(&tok.loc, "expression is not an object");
		lval.addr = funcexpr(f, e);
	}
	return lval;
}

/* returns the expression value in the true branch */
struct value *
funcbranch(struct func *f, struct expr *e, struct block *bt, struct block *bf)
{
	static struct value one = {.kind = VALUE_INTCONST, .u.i = 1};
	struct expr *l, *r;
	struct value *v;
	struct block *b;

	/* a condition that folds to a constant (the kernel's udelay: if ((10) / 20000 >= 1) __bad_udelay();) is a jump:
	 * the other way is unreachable, and neither cproc's asm thunks nor QBE keep code that only it reaches -- gcc
	 * never emits that call, whose symbol may not exist */
	if (!(e->type->prop & PROPSOFT)) {
		struct expr *c = eval(e);

		if (c->kind == EXPRCONST && c->type->prop & PROPINT) {
			funcjmp(f, c->u.constant.u ? bt : bf);
			return mkintconst(c->u.constant.u);
		}
		e = c;
	}
	/* Maybe we we could do something for EXPRCOND as well. */
	switch (e->kind) {
	case EXPRBINARY:
		l = e->u.binary.l;
		r = e->u.binary.r;
		switch (e->op) {
		case TEQL:
		case TNEQ:
			r = eval(r);
			if (r->kind == EXPRCONST && r->type->prop & PROPINT && r->u.constant.u == 0) {
				if (e->op == TEQL)
					b = bt, bt = bf, bf = b;
				funcbranch(f, l, bt, bf);
				return &one;
			}
			break;
		case TLOR:
		case TLAND:
			if (e->op == TLOR) {
				b = mkblock("logic_or");
				funcbranch(f, l, bt, b);
			} else {
				b = mkblock("logic_and");
				funcbranch(f, l, b, bf);
			}
			funclabel(f, b);
			funcbranch(f, r, bt, bf);
			return &one;
		}
		break;
	case EXPRCOMMA:
		for (e = e->base; e->next; e = e->next)
			funcexpr(f, e);
		return funcbranch(f, e, bt, bf);
	}
	v = funcexpr(f, e);
	funcjnz(f, v, e->type, bt, bf);
	return v;
}

/* true if every scalar in t is an integer, pointer or bool, so each eightbyte is SysV class INTEGER */
static bool
intclass(struct type *t)
{
	struct member *m;

	switch (t->kind) {
	case TYPEARRAY:
		return intclass(t->base);
	case TYPESTRUCT:
	case TYPEUNION:
		for (m = t->u.structunion.members; m; m = m->next) {
			if (!intclass(m->type))
				return false;
		}
		return true;
	default:
		return t->prop & PROPSCALAR && !(t->prop & PROPFLOAT);
	}
}

struct value *funcvalistaddr(struct func *f, struct expr *e);

/*
va_arg for a struct/union of at most 16 bytes whose eightbytes are all class INTEGER
(x86_64 SysV only; QBE's vaarg handles scalars). Such an argument is in the general
registers when enough remain (gp_offset <= 48 - size), all of it or none, and otherwise in
the overflow area. The result is the address of the argument, like any aggregate value.
*/
static struct value *
funcvaargagg(struct func *f, struct expr *e)
{
	struct value *ap, *gp, *cond, *tmp, *addr[2];
	struct block *b[3];
	unsigned long long size;

	if (strcmp(targ->name, "aarch64-apple") == 0) {
		/* Apple arm64: every variadic argument is in the 8-byte aligned stack slots that the va_list pointer walks
		 * (QBE's apple_selvaarg), so an aggregate of alignment 8 or less is its address, and the pointer moves on by
		 * its size rounded up to 8. */
		if (!e->type->size || e->type->align > 8)
			error(&tok.loc, "va_arg with non-scalar type is not yet supported (aggregates of alignment 8 or less on aarch64-apple)");
		size = ALIGNUP(e->type->size, 8);
		ap = funcvalistaddr(f, e->base);
		tmp = funcinst(f, ILOADL, 'l', ap, NULL);
		funcinst(f, ISTOREL, 0, funcinst(f, IADD, 'l', tmp, mkintconst(size)), ap);
		return tmp;
	}
	if (targ->ilp32) {
		/* i386: every argument is in the stack slots that the va_list pointer walks, rounded up to 4 bytes */
		size = ALIGNUP(e->type->size, 4);
		ap = funcvalistaddr(f, e->base);
		tmp = funcinst(f, ILOADW, 'w', ap, NULL);
		funcinst(f, ISTOREW, 0, funcinst(f, IADD, 'w', tmp, mkintconst(size)), ap);
		return tmp;
	}
	if (e->type->kind == TYPELDOUBLE) {
		/* a long double is class X87 (memory): the next 16-byte aligned slot of the overflow area */
		ap = funcexpr(f, e->base);
		tmp = funcinst(f, IADD, 'l', ap, mkintconst(8));  /* &overflow_arg_area */
		addr[0] = funcinst(f, IAND, 'l', funcinst(f, IADD, 'l', funcinst(f, ILOADL, 'l', tmp, NULL), mkintconst(15)), mkintconst(-16ull));
		funcinst(f, ISTOREL, 0, funcinst(f, IADD, 'l', addr[0], mkintconst(16)), tmp);
		return addr[0];
	}
	if (strcmp(targ->name, "x86_64-sysv") != 0 || !e->type->size || e->type->size > 16
	    || e->type->align > 8 || !intclass(e->type))
		error(&tok.loc, "va_arg with non-scalar type is not yet supported (only integer-class aggregates of up to 16 bytes on x86_64)");
	size = ALIGNUP(e->type->size, 8);
	ap = funcexpr(f, e->base);
	b[0] = mkblock("vaarg_reg");
	b[1] = mkblock("vaarg_stack");
	b[2] = mkblock("vaarg_join");

	gp = funcinst(f, ILOADW, 'w', ap, NULL);
	cond = funcinst(f, ICULEW, 'w', gp, mkintconst(48 - size));
	funcjnz(f, cond, NULL, b[0], b[1]);

	funclabel(f, b[0]);
	tmp = funcinst(f, ILOADL, 'l', funcinst(f, IADD, 'l', ap, mkintconst(16)), NULL);  /* reg_save_area */
	addr[0] = funcinst(f, IADD, 'l', tmp, funcinst(f, IEXTUW, 'l', gp, NULL));
	funcinst(f, ISTOREW, 0, funcinst(f, IADD, 'w', gp, mkintconst(size)), ap);
	b[2]->phi.val[0] = addr[0];
	b[2]->phi.blk[0] = f->end;
	funcjmp(f, b[2]);

	funclabel(f, b[1]);
	tmp = funcinst(f, IADD, 'l', ap, mkintconst(8));  /* &overflow_arg_area */
	addr[1] = funcinst(f, ILOADL, 'l', tmp, NULL);
	funcinst(f, ISTOREL, 0, funcinst(f, IADD, 'l', addr[1], mkintconst(size)), tmp);
	b[2]->phi.val[1] = addr[1];
	b[2]->phi.blk[1] = f->end;

	funclabel(f, b[2]);
	functemp(f, &b[2]->phi.res);
	b[2]->phi.class = 'l';
	return &b[2]->phi.res;
}

/*
A call of a function with a __float128 argument or result (passed by value) is checked when the translation unit is complete
(checkf128calls): a function defined later in the unit is fine, and so is one with internal linkage.
*/
struct f128call {
	struct decl *decl;
	struct location loc;
};
static struct f128call *f128calls;
static size_t nf128calls, cap128calls;

static void
addf128call(struct decl *d)
{
	if (nf128calls == cap128calls) {
		cap128calls = cap128calls ? 2 * cap128calls : 16;
		f128calls = xreallocarray(f128calls, cap128calls, sizeof(f128calls[0]));
	}
	f128calls[nf128calls].decl = d;
	f128calls[nf128calls].loc = tok.loc;
	++nf128calls;
}

void
checkf128calls(void)
{
	size_t i;

	for (i = 0; i < nf128calls; ++i) {
		struct decl *d = f128calls[i].decl;

		if (!d->defined && d->linkage != LINKINTERN) {
			error(&f128calls[i].loc, "__float128 passed or returned by value to '%s' (not defined in this unit) is not supported by the qbe backend",
			      d->name);
		}
	}
}

/* whether a call has a __float128 argument (passed by value) */
static bool
anyf128arg(struct expr *e)
{
	struct expr *arg;

	for (arg = e->u.call.args; arg; arg = arg->next)
		if (arg->type->kind == TYPEFLOAT128)
			return true;
	return false;
}

/* The address of a va_list object. A pointer-typed va_list (Apple arm64) is the object itself, so its address is
 * needed; an array-typed one (x86-64, Linux aarch64) already evaluates to its address. */
struct value *
funcvalistaddr(struct func *f, struct expr *e)
{
	if (targ->typevalist->kind == TYPEPOINTER) {
		/* the argument may be converted to the va_list type, or taken by address (the parser's array-style view of
		 * va_list): the object is under the cast and the address-of */
		for (;;) {
			if (e->kind == EXPRCAST || (e->kind == EXPRUNARY && e->op == TBAND))
				e = e->base;
			else
				break;
		}
		return funclval(f, e).addr;
	}
	return funcexpr(f, e);
}

/*
GNU __builtin_{add,sub,mul}_overflow(a, b, r) for any mix of integer types up to 64 bits: the exact result is computed
as a sign and a 128-bit magnitude (as GCC defines it, infinite precision), wrapped into *r, and the flag says whether
*r cannot hold it. The algorithm is __nfcxx_ovx of scripts/qbe-prep.rb, with its branches as masks; the operands'
signedness is known here, so it is straight-line code.
*/
static struct value *
ovl(struct func *f, int op, struct value *x, struct value *y)
{
	return funcinst(f, op, 'l', x, y);
}

static struct value *
ovcmp(struct func *f, int op, struct value *x, struct value *y)   /* 0 or 1, as a long */
{
	return funcinst(f, IEXTUW, 'l', funcinst(f, op, 'w', x, y), NULL);
}

/*
The bit-counting built-ins, branch-free (QBE has no bit-count instructions): a population count by halves (the SWAR
sum, gathered by a multiply), and the others reduced to it -- ctz(x) = popcount((x & -x) - 1), clz(x) = width -
popcount(x with every bit below its top bit set), ffs(x) = popcount(x ^ (x - 1)) when x is not zero, parity the low
bit of the count. clz and ctz of zero are the width.
*/
static struct value *
funcpopcount(struct func *f, int class, struct value *x)
{
	bool l = class == 'l';
	unsigned long long m1 = 0x5555555555555555ull, m2 = 0x3333333333333333ull, m4 = 0x0f0f0f0f0f0f0f0full, h = 0x0101010101010101ull;
	struct value *t;

	if (!l)
		m1 &= 0xffffffff, m2 &= 0xffffffff, m4 &= 0xffffffff, h &= 0xffffffff;
	t = funcinst(f, IAND, class, funcinst(f, ISHR, class, x, mkintconst(1)), mkintconst(m1));
	x = funcinst(f, ISUB, class, x, t);
	t = funcinst(f, IAND, class, funcinst(f, ISHR, class, x, mkintconst(2)), mkintconst(m2));
	x = funcinst(f, IADD, class, funcinst(f, IAND, class, x, mkintconst(m2)), t);
	x = funcinst(f, IAND, class, funcinst(f, IADD, class, x, funcinst(f, ISHR, class, x, mkintconst(4))), mkintconst(m4));
	return funcinst(f, ISHR, class, funcinst(f, IMUL, class, x, mkintconst(h)), mkintconst(l ? 56 : 24));
}

static struct value *
funcbitcount(struct func *f, struct expr *e)
{
	int kind = e->u.builtin.kind, class = e->base->type->size == 8 ? 'l' : 'w', w = class == 'l' ? 64 : 32, k;
	struct value *x = funcexpr(f, e->base), *t, *r;

	switch (kind) {
	case BUILTINCLZ: case BUILTINCLZL:
		for (k = 1; k < w; k *= 2)
			x = funcinst(f, IOR, class, x, funcinst(f, ISHR, class, x, mkintconst(k)));
		r = funcinst(f, ISUB, class, mkintconst(w), funcpopcount(f, class, x));
		break;
	case BUILTINCTZ: case BUILTINCTZL:
		t = funcinst(f, IAND, class, x, funcinst(f, INEG, class, x, NULL));
		r = funcpopcount(f, class, funcinst(f, ISUB, class, t, mkintconst(1)));
		break;
	case BUILTINFFS: case BUILTINFFSL:
		t = funcinst(f, IXOR, class, x, funcinst(f, ISUB, class, x, mkintconst(1)));
		r = funcpopcount(f, class, t);
		t = funcinst(f, class == 'l' ? ICNEL : ICNEW, class, x, mkintconst(0));
		r = funcinst(f, IMUL, class, r, t);
		break;
	default:
		r = funcpopcount(f, class, x);
		if (kind == BUILTINPARITY || kind == BUILTINPARITYL)
			r = funcinst(f, IAND, class, r, mkintconst(1));
	}
	return r;   /* a long result is read as its low word, the int */
}

static struct value *
funcoverflow(struct func *f, struct expr *e)
{
	struct expr *ae = e->base, *be = ae->next, *re = be->next;
	struct type *rt = re->type->base;
	bool as = ae->type->u.arith.issigned, bs = be->type->u.arith.issigned, rs = rt->u.arith.issigned;
	struct value *ua, *ub, *rp, *ma, *mb, *an, *bn, *am, *bm, *lo, *hi, *neg, *out, *zero = mkintconst(0), *v;
	struct value *flag, *rest;
	unsigned w = rt->size * 8;

	/* in 64-bit integers: long long (long is 4 bytes on ILP32) */
	ua = convert(f, as ? &typellong : &typeullong, ae->type, funcexpr(f, ae));
	ub = convert(f, bs ? &typellong : &typeullong, be->type, funcexpr(f, be));
	rp = funcexpr(f, re);
	/* sign masks (all ones for a negative operand) and magnitudes */
	ma = as ? ovl(f, ISAR, ua, mkintconst(63)) : zero;
	mb = bs ? ovl(f, ISAR, ub, mkintconst(63)) : zero;
	an = ovl(f, IAND, ma, mkintconst(1));
	bn = ovl(f, IAND, mb, mkintconst(1));
	am = ovl(f, ISUB, ovl(f, IXOR, ua, ma), ma);
	bm = ovl(f, ISUB, ovl(f, IXOR, ub, mb), mb);
	if (e->u.builtin.kind == BUILTINMULOVERFLOW) {
		struct value *m32 = mkintconst(0xffffffff), *s32 = mkintconst(32);
		struct value *a0 = ovl(f, IAND, am, m32), *a1 = ovl(f, ISHR, am, s32);
		struct value *b0 = ovl(f, IAND, bm, m32), *b1 = ovl(f, ISHR, bm, s32);
		struct value *p00 = ovl(f, IMUL, a0, b0), *p01 = ovl(f, IMUL, a0, b1);
		struct value *p10 = ovl(f, IMUL, a1, b0), *p11 = ovl(f, IMUL, a1, b1), *mid;

		mid = ovl(f, IADD, ovl(f, IADD, ovl(f, ISHR, p00, s32), ovl(f, IAND, p01, m32)), ovl(f, IAND, p10, m32));
		lo = ovl(f, IOR, ovl(f, IAND, p00, m32), ovl(f, ISHL, mid, s32));
		hi = ovl(f, IADD, ovl(f, IADD, p11, ovl(f, ISHR, p01, s32)), ovl(f, IADD, ovl(f, ISHR, p10, s32), ovl(f, ISHR, mid, s32)));
		neg = ovl(f, IXOR, an, bn);
	} else {
		struct value *s, *sum, *carry, *d, *borrow, *mk, *absd, *ms;

		if (e->u.builtin.kind == BUILTINSUBOVERFLOW)
			bn = ovl(f, IXOR, bn, mkintconst(1));   /* a - b is a + (-b) */
		s = ovl(f, IXOR, an, bn);                    /* the signs differ: a magnitude difference */
		sum = ovl(f, IADD, am, bm);
		carry = ovcmp(f, ICULTL, sum, am);
		d = ovl(f, ISUB, am, bm);
		borrow = ovcmp(f, ICULTL, am, bm);
		mk = ovl(f, ISUB, zero, borrow);
		absd = ovl(f, ISUB, ovl(f, IXOR, d, mk), mk);
		ms = ovl(f, ISUB, zero, s);
		lo = ovl(f, IOR, ovl(f, IAND, absd, ms), ovl(f, IAND, sum, ovl(f, IXOR, ms, mkintconst(-1))));
		hi = ovl(f, IAND, carry, ovl(f, IXOR, s, mkintconst(1)));
		neg = ovl(f, IXOR, an, ovl(f, IAND, s, borrow));   /* the larger magnitude's sign when they differ */
	}
	neg = ovl(f, IAND, neg, ovcmp(f, ICNEL, ovl(f, IOR, hi, lo), zero));   /* zero is not negative */
	v = ovl(f, ISUB, zero, neg);
	out = ovl(f, ISUB, ovl(f, IXOR, lo, v), v);
	funcstore(f, rt, re->type->qual, (struct lvalue){.addr = rp}, convert(f, rt, &typeullong, out));
	/* overflow: a high half, or a magnitude out of the result type's range */
	if (rs) {
		rest = ovcmp(f, ICUGTL, lo, ovl(f, IADD, mkintconst((1ull << (w - 1)) - 1), neg));
	} else {
		rest = neg;
		if (w < 64)
			rest = ovl(f, IOR, rest, ovcmp(f, ICNEL, ovl(f, ISHR, lo, mkintconst(w)), zero));
	}
	flag = ovl(f, IOR, ovcmp(f, ICNEL, hi, zero), rest);
	return funcinst(f, ICNEL, 'w', flag, zero);
}

struct value *
funcexpr(struct func *f, struct expr *e)
{
	struct expr *callee;
	enum instkind op = INONE;

	if (e->loc.line)
		asanloc = e->loc;
	struct decl *d;
	struct value *l, *r, *v, **argvals;
	struct lvalue lval;
	struct expr *arg;
	struct block *b[3];
	struct type *t, *functype;
	size_t i;

	calcvla(f, e->type);
	if (targ->ilp32 && softvalue(e->type))
		error(&e->loc, "a %s value is not supported on %s", e->type->kind == TYPELDOUBLE ? "long double" : "__float128", targ->name);
	switch (e->kind) {
	case EXPRSTMT:
		if (e->u.stmt.done)
			fatal("internal error: statement expression evaluated twice");
		e->u.stmt.done = true;
		funcjmp(f, e->u.stmt.first);
		f->end->next = e->u.stmt.first;
		f->end = e->u.stmt.last;
		return e->base ? funcexpr(f, e->base) : NULL;
	case EXPRIDENT:
		d = e->u.ident.decl;
		if (d->kind == DECLOBJECT && d->regvar && d->u.obj.storage != SDAUTO)
			return funcregvar(f, d);
		switch (d->kind) {
		case DECLOBJECT: return funcloadq(f, e->type, e->qual | d->qual, (struct lvalue){d->value});
		case DECLCONST:  return d->value;
		default:
			fatal("unimplemented declaration kind %d", d->kind);
		}
		break;
	case EXPRCONST:
		t = e->type;
		if (t->prop & PROPSOFT) {
			/* the image of the constant, stored into a temporary */
			v = softtemp(f);
			funcinst(f, ISTOREL, 0, mkintconst(e->u.constant.soft[0]), v);
			r = funcinst(f, IADD, ptrclass, v, mkintconst(8));
			funcinst(f, ISTOREL, 0, mkintconst(e->u.constant.soft[1]), r);
			return v;
		}
		if (t->prop & PROPINT || t->kind == TYPEPOINTER)
			return mkintconst(e->u.constant.u);
		assert(t->prop & PROPFLOAT);
		if (t->kind == TYPEFLOAT16)
			return mkintconst(halfbits(e->u.constant.f));
		return mkfltconst(t->size == 4 ? VALUE_FLTCONST : VALUE_DBLCONST, e->u.constant.f);
	case EXPRBITFIELD:
	case EXPRCOMPOUND:
		lval = funclval(f, e);
		return funcloadq(f, e->type, e->qual, lval);
	case EXPRINCDEC:
		lval = funclval(f, e->base);
		l = funcloadq(f, e->base->type, e->base->qual, lval);
		t = e->type;
		if (t->prop & PROPSOFT) {
			/* the old value is copied out first: the store overwrites the object that l addresses */
			if (e->u.incdec.post) {
				r = softtemp(f);
				funccopy(f, r, l, t->size, t->align);
				l = r;
			}
			r = convert(f, t, &typeint, mkintconst(1));
			v = softbinary(f, e->op == TINC ? TADD : TSUB, t, funcload(f, t, lval), r);
			v = funcstore(f, e->type, e->qual, lval, v);
			return e->u.incdec.post ? l : v;
		}
		if (t->kind == TYPEFLOAT16) {
			/* 1.0 is 0x3c00 */
			v = f16binary(f, e->op == TINC ? TADD : TSUB, t, l, mkintconst(0x3c00));
			v = funcstore(f, e->type, e->qual, lval, v);
			return e->u.incdec.post ? l : v;
		}
		if (t->kind == TYPEPOINTER) {
			if (t->base->kind == TYPEARRAY && t->base->size == 0 && t->base->prop & PROPVM) {
				r = t->base->u.array.size;
			} else {
				/* GNU C: a void or function pointer steps by 1 */
				r = mkintconst(t->base->kind == TYPEVOID || t->base->kind == TYPEFUNC ? 1 : t->base->size);
			}
		} else if (t->prop & PROPINT) {
			r = mkintconst(1);
		} else if (t->prop & PROPFLOAT) {
			r = mkfltconst(t->size == 4 ? VALUE_FLTCONST : VALUE_DBLCONST, 1);
		} else {
			fatal("not a scalar");
		}
		v = funcinst(f, e->op == TINC ? IADD : ISUB, qbetype(t).base, l, r);
		v = funcstore(f, e->type, e->qual, lval, v);
		return e->u.incdec.post ? l : v;
	case EXPRCALL:
		/* __float128 is passed in one SSE register (class SSE, SSEUP) in the SysV ABI, which this backend does not do: a
		 * call of a function that is not defined in this unit (its code may be gcc's) with a __float128 argument or result
		 * is an error, not a silently different convention. Calls within the unit use the same convention on both sides. */
		callee = e->base;
		if (callee->kind == EXPRUNARY && callee->op == TBAND)
			callee = callee->base;  /* a function designator, decayed to a pointer */
		if (callee->kind == EXPRIDENT && callee->u.ident.decl->kind == DECLFUNC && (e->type->kind == TYPEFLOAT128 || anyf128arg(e)))
			addf128call(callee->u.ident.decl);
		if (e->base->type->base->u.func.abi)
			funcrefuse(f, "call of a function with the %s calling convention is not supported", e->base->type->base->u.func.abi);
		argvals = xreallocarray(NULL, e->u.call.nargs, sizeof(argvals[0]));
		for (arg = e->u.call.args, i = 0; arg; arg = arg->next, ++i) {
			emittype(arg->type);
			argvals[i] = funcexpr(f, arg);
			if (arg->type->kind == TYPEFLOAT16)
				argvals[i] = f16tosse(f, argvals[i]);
		}
		t = e->type;
		emittype(t);
		/* a long double is returned in st(0): the call has no QBE result, and the value is popped into a temporary */
		if (t->kind == TYPELDOUBLE) {
			v = softtemp(f);
			funcinst(f, ICALL, 0, funcexpr(f, e->base), NULL);
		} else {
			/* a direct call of an extern gnu_inline function goes to its body (decl.c, mkinlinealias) */
			struct value *fv = callee->kind == EXPRIDENT && callee->u.ident.decl->kind == DECLFUNC &&
				callee->u.ident.decl->u.func.inlinealias ? callee->u.ident.decl->u.func.inlinealias : funcexpr(f, e->base);
			v = funcinst(f, ICALL, abiclass(t), fv, t->value);
		}
		functype = e->base->type->base;
		for (arg = e->u.call.args, i = 0; arg; arg = arg->next, ++i) {
			if (functype->u.func.isvararg && i == functype->u.func.nparam)
				funcinst(f, IVARARG, 0, NULL, NULL);
			t = arg->type;
			funcinst(f, IARG, abiclass(t), argvals[i], t->value);
		}
		if (e->type->kind == TYPELDOUBLE) {
			struct softarg pa[1] = {{'l', v}};

			softcall(f, 0, softname(e->type, "pop"), 1, pa);
		}
		if (e->type->kind == TYPEFLOAT16)
			v = f16fromsse(f, v);
		/* after the whole call (its IARG instructions follow the ICALL): the call's block ends, and its return is a pad */
		if (asanon && callee->kind == EXPRIDENT && callee->u.ident.decl->kind == DECLFUNC && asansetjmpname(callee->u.ident.decl->name))
			asansetjmp(f);
		e = e->base;
		if (e->kind == EXPRUNARY && e->op == TBAND) {
			e = e->base;
			if (e->kind == EXPRIDENT && e->u.ident.decl->u.func.isnoreturn)
				funchlt(f);
		}
		return v;
	case EXPRUNARY:
		switch (e->op) {
		case TBAND:
			lval = funclval(f, e->base);
			return lval.addr;
		case TMUL:
			r = funcexpr(f, e->base);
			return funcloadq(f, e->type, e->qual, (struct lvalue){r});
		case TSUB:
			r = funcexpr(f, e->base);
			if (e->type->prop & PROPSOFT)
				return softunary(f, e->type, "neg", r);
			if (e->type->kind == TYPEFLOAT16)
				return funcinst(f, IXOR, 'w', r, mkintconst(0x8000));
			return funcinst(f, INEG, qbetype(e->type).base, r, NULL);
		}
		fatal("internal error; unknown unary expression");
		break;
	case EXPRCAST:
		if (e->toeval)
			funcexpr(f, e->toeval);
		l = funcexpr(f, e->base);
		return convert(f, e->type, e->base->type, l);
	case EXPRBINARY:
		if (e->op == TLOR || e->op == TLAND) {
			b[0] = mkblock("logic_true");
			b[1] = mkblock("logic_false");
			b[2] = mkblock("logic_join");

			funcbranch(f, e, b[0], b[1]);
			funclabel(f, b[0]);
			funcjmp(f, b[2]);
			funclabel(f, b[1]);

			b[2]->phi.class = 'w';
			b[2]->phi.blk[0] = b[0];
			b[2]->phi.val[0] = mkintconst(1);
			b[2]->phi.blk[1] = b[1];
			b[2]->phi.val[1] = mkintconst(0);
			functemp(f, &b[2]->phi.res);
			funclabel(f, b[2]);

			return &b[2]->phi.res;
		}
		l = funcexpr(f, e->u.binary.l);
		r = funcexpr(f, e->u.binary.r);
		t = e->u.binary.l->type;
		if (t->kind == TYPEPOINTER)
			t = &typeulong;
		if (t->kind == TYPEINT128 && (e->op == TSHL || e->op == TSHR))
			r = convert(f, &typelong, e->u.binary.r->type, r);
		if (t->prop & PROPSOFT)
			return softbinary(f, e->op, t, l, r);
		if (t->kind == TYPEFLOAT16)
			return f16binary(f, e->op, t, l, r);
		switch (e->op) {
		case TMUL:
			op = IMUL;
			break;
		case TDIV:
			op = !(t->prop & PROPINT) || t->u.arith.issigned ? IDIV : IUDIV;
			break;
		case TMOD:
			op = t->u.arith.issigned ? IREM : IUREM;
			break;
		case TADD:
			op = IADD;
			break;
		case TSUB:
			op = ISUB;
			break;
		case TSHL:
			op = ISHL;
			break;
		case TSHR:
			op = t->u.arith.issigned ? ISAR : ISHR;
			break;
		case TBOR:
			op = IOR;
			break;
		case TBAND:
			op = IAND;
			break;
		case TXOR:
			op = IXOR;
			break;
		case TLESS:
			if (t->size <= 4)
				op = t->prop & PROPFLOAT ? ICLTS : t->u.arith.issigned ? ICSLTW : ICULTW;
			else
				op = t->prop & PROPFLOAT ? ICLTD : t->u.arith.issigned ? ICSLTL : ICULTL;
			break;
		case TGREATER:
			if (t->size <= 4)
				op = t->prop & PROPFLOAT ? ICGTS : t->u.arith.issigned ? ICSGTW : ICUGTW;
			else
				op = t->prop & PROPFLOAT ? ICGTD : t->u.arith.issigned ? ICSGTL : ICUGTL;
			break;
		case TLEQ:
			if (t->size <= 4)
				op = t->prop & PROPFLOAT ? ICLES : t->u.arith.issigned ? ICSLEW : ICULEW;
			else
				op = t->prop & PROPFLOAT ? ICLED : t->u.arith.issigned ? ICSLEL : ICULEL;
			break;
		case TGEQ:
			if (t->size <= 4)
				op = t->prop & PROPFLOAT ? ICGES : t->u.arith.issigned ? ICSGEW : ICUGEW;
			else
				op = t->prop & PROPFLOAT ? ICGED : t->u.arith.issigned ? ICSGEL : ICUGEL;
			break;
		case TEQL:
			if (t->size <= 4)
				op = t->prop & PROPFLOAT ? ICEQS : ICEQW;
			else
				op = t->prop & PROPFLOAT ? ICEQD : ICEQL;
			break;
		case TNEQ:
			if (t->size <= 4)
				op = t->prop & PROPFLOAT ? ICNES : ICNEW;
			else
				op = t->prop & PROPFLOAT ? ICNED : ICNEL;
			break;
		}
		if (op == INONE)
			fatal("internal error; unimplemented binary expression");
		v = funcinst(f, op, qbetype(e->type).base, l, r);
		if (t->kind == TYPEBITINT)
			v = funcbits(f, t, v, (struct bitfield){0});
		return v;
	case EXPRCOND:
		b[0] = mkblock("cond_true");
		b[1] = mkblock("cond_false");
		b[2] = mkblock("cond_join");

		v = funcbranch(f, e->base, b[0], b[1]);

		funclabel(f, b[0]);
		if (e->u.cond.t != e->base)
			v = funcexpr(f, e->u.cond.t);
		b[2]->phi.val[0] = convert(f, e->type, e->u.cond.t->type, v);
		b[2]->phi.blk[0] = f->end;
		funcjmp(f, b[2]);

		funclabel(f, b[1]);
		v = funcexpr(f, e->u.cond.f);
		b[2]->phi.val[1] = convert(f, e->type, e->u.cond.f->type, v);
		b[2]->phi.blk[1] = f->end;

		funclabel(f, b[2]);
		if (e->type == &typevoid)
			return NULL;
		functemp(f, &b[2]->phi.res);
		b[2]->phi.class = qbetype(e->type).base;
		return &b[2]->phi.res;
	case EXPRASSIGN:
		r = funcexpr(f, e->u.assign.r);
		if (e->u.assign.l->kind == EXPRTEMP) {
			e->u.assign.l->u.temp = r;
		} else {
			lval = funclval(f, e->u.assign.l);
			r = funcstore(f, e->u.assign.l->type, e->u.assign.l->qual, lval, r);
		}
		return r;
	case EXPRCOMMA:
		for (e = e->base; e->next; e = e->next)
			funcexpr(f, e);
		return funcexpr(f, e);
	case EXPRBUILTIN:
		switch (e->u.builtin.kind) {
		case BUILTINADDOVERFLOW:
		case BUILTINSUBOVERFLOW:
		case BUILTINMULOVERFLOW:
			return funcoverflow(f, e);
		case BUILTINBSWAP16:
		case BUILTINBSWAP32:
		case BUILTINBSWAP64: {
			/* QBE has no byte swap: the bytes moved one by one with shifts and masks */
			int bytes = e->type->size, k, class = bytes == 8 ? 'l' : 'w';
			struct value *x = funcexpr(f, e->base), *acc = NULL, *b;

			for (k = 0; k < bytes; ++k) {
				b = k ? funcinst(f, ISHR, class, x, mkintconst(8 * k)) : x;
				b = funcinst(f, IAND, class, b, mkintconst(0xff));
				if (bytes - 1 - k)
					b = funcinst(f, ISHL, class, b, mkintconst(8 * (bytes - 1 - k)));
				acc = acc ? funcinst(f, IOR, class, acc, b) : b;
			}
			return acc;
		}
		case BUILTINCLZ: case BUILTINCLZL:
		case BUILTINCTZ: case BUILTINCTZL:
		case BUILTINFFS: case BUILTINFFSL:
		case BUILTINPARITY: case BUILTINPARITYL:
		case BUILTINPOPCOUNT: case BUILTINPOPCOUNTL:
			return funcbitcount(f, e);
		case BUILTINRETURNADDRESS:
		case BUILTINFRAMEADDRESS:
			return funcframeinfo(f, e->u.builtin.kind == BUILTINRETURNADDRESS);
		case BUILTINVASTART:
			l = funcvalistaddr(f, e->base);
			funcinst(f, IVASTART, 0, l, NULL);
			break;
		case BUILTINVAARG:
			if (e->toeval)
				funcexpr(f, e->toeval);
			/* https://todo.sr.ht/~mcf/cproc/52 */
			if (!(e->type->prop & PROPSCALAR) || e->type->prop & PROPSOFT)
				return funcvaargagg(f, e);
			l = funcvalistaddr(f, e->base);
			return funcinst(f, IVAARG, qbetype(e->type).base, l, NULL);
		case BUILTINALLOCA:
			l = funcexpr(f, e->base);
			if (asanon)
				return asandynalloc(f, l, false);
			return funcinst(f, IALLOC16, ptrclass, l, NULL);
		case BUILTINC11INIT:
		case BUILTINC11LOAD:
		case BUILTINC11STORE:
		case BUILTINC11XCHG:
		case BUILTINC11CAS:
		case BUILTINC11FETCHADD:
		case BUILTINC11FETCHSUB:
		case BUILTINC11FETCHAND:
		case BUILTINC11FETCHOR:
		case BUILTINC11FETCHXOR:
			return funcatomic(f, e);
		case BUILTINUNREACHABLE:
			funchlt(f);
			return NULL;
		case BUILTINSIGNBIT:
			/* the sign bit: bit 15 of a _Float16 pattern, the top bit of the sign-and-exponent byte of the 16-byte
			 * types (byte 9 of long double, byte 15 of __float128), and the top byte of float and double, which are
			 * stored to a temporary (entry block, as softtemp) to read it */
			l = funcexpr(f, e->base);
			t = e->base->type;
			if (t->kind == TYPEFLOAT16)
				return funcinst(f, IAND, 'w', funcinst(f, ISHR, 'w', l, mkintconst(15)), mkintconst(1));
			if (t->prop & PROPSOFT) {
				v = funcinst(f, IADD, ptrclass, l, mkintconst(t->kind == TYPEFLOAT128 ? 15 : 9));
			} else {
				struct block *end = f->end;
				f->end = f->start;
				v = funcinst(f, t->size == 4 ? IALLOC4 : IALLOC8, ptrclass, mkintconst(t->size), NULL);
				f->end = end;
				funcinst(f, t->size == 4 ? ISTORES : ISTORED, 0, l, v);
				v = funcinst(f, IADD, ptrclass, v, mkintconst(t->size - 1));
			}
			l = funcinst(f, ILOADUB, 'w', v, NULL);
			return funcinst(f, ISHR, 'w', l, mkintconst(7));
		case BUILTINFABSF:
			/* clear the sign bit of the float in a 4-byte temporary (entry block, as softtemp) */
			l = funcexpr(f, e->base);
			{
				struct block *end = f->end;
				f->end = f->start;
				v = funcinst(f, IALLOC4, ptrclass, mkintconst(4), NULL);
				f->end = end;
			}
			funcinst(f, ISTORES, 0, l, v);
			l = funcinst(f, ILOADW, 'w', v, NULL);
			l = funcinst(f, IAND, 'w', l, mkintconst(0x7fffffff));
			funcinst(f, ISTOREW, 0, l, v);
			return funcinst(f, ILOADS, 's', v, NULL);
		default:
			fatal("internal error: unimplemented builtin");
		}
		return NULL;
	case EXPRTEMP:
		/* a reference to a temporary (its base is the definition, expr.c fpuse) reads the definition's value */
		if (e->base)
			e = e->base;
		assert(e->u.temp);
		return e->u.temp;
	case EXPRSIZEOF:
		t = e->u.szof.type;
		assert(t->kind == TYPEARRAY);
		calcvla(f, t);
		/* if the sizeof operand has VLA type, we must evaluate it */
		if (e->base)
			funcexpr(f, e->base);
		return t->u.array.size;
	}
	fatal("unimplemented expression %d", e->kind);
	return NULL;
}

static void
zero(struct func *func, struct value *addr, int align, unsigned long long offset, unsigned long long end)
{
	static const enum instkind store[] = {
		[1] = ISTOREB,
		[2] = ISTOREH,
		[4] = ISTOREW,
		[8] = ISTOREL,
	};
	static struct value z = {.kind = VALUE_INTCONST};
	struct value *tmp;
	int a = 1;

	/* the stores are at most 8 bytes (store[] has no entry for more); an object aligned to 16 is aligned to 8 at each
	 * offset that matters here, so clamping the alignment is enough (long double arrays and structs reach this) */
	if (align > 8)
		align = 8;
	if (align > 4 && targ->ilp32)   /* no 64-bit integers: by words */
		align = 4;
	while (offset < end) {
		if ((align - (offset & align - 1)) & a) {
			tmp = offset ? funcinst(func, IADD, ptrclass, addr, mkintconst(offset)) : addr;
			funcinst(func, store[a], 0, &z, tmp);
			offset += a;
		}
		if (a < align)
			a <<= 1;
	}
}

/* GNU cleanup(f) on a block-scope object d (nfcxx's EH frames): when a throw unwinds the function, its landing pad (emitfunc)
   calls f(&d) for each such object, the last declared first, and resumes the unwind. nfcxx's cleanup functions do nothing
   at the normal end of the scope (they run only during a throw), so the normal end is not lowered. */
static void
ehcleanupobj(struct func *f, struct decl *d)
{
	struct ehobj *o;

	o = arrayadd(&f->ehobjs, sizeof(*o));
	o->cleanup = d->u.obj.cleanup;
	o->addr = d->value;
}

/*
cproc -G: GNU C's cleanup attribute (the Linux kernel's guard() and scoped_guard()): f(&object) runs when the object
leaves its scope -- at the end of the block, and at a return, break, continue or goto that leaves it -- the last
declared first, as gcc does without -fexceptions (no unwind tables, no landing pads). The function keeps the
objects live at each point (cleanups); a goto jumps to a block of its own whose cleanups are made after the body,
when the label's live objects are known (funcgotoflush). Without -G, nfcxx's EDG-made C keeps its own meaning:
the cleanups run only when a throw unwinds the function (ehcleanupobj).
*/
bool gnucleanup;

struct cleangoto {
	struct block *trampoline;
	struct gotolabel *label;
	struct array live;   /* struct ehobj: the cleanup objects live at the goto */
};

size_t
funccleanmark(struct func *f)
{
	return f->cleanups.len / sizeof(struct ehobj);
}

static void
cleancalls(struct func *f, struct ehobj *o, size_t from, size_t to)
{
	while (to-- > from) {
		funcinst(f, ICALL, 0, o[to].fn, NULL);
		funcinst(f, IARG, ptrclass, o[to].addr, NULL);
	}
}

void
funccleanleave(struct func *f, size_t mark)
{
	if (!f->end->jump.kind)
		cleancalls(f, f->cleanups.val, mark, funccleanmark(f));
}

void
funccleanpop(struct func *f, size_t mark)
{
	funccleanleave(f, mark);
	f->cleanups.len = mark * sizeof(struct ehobj);
}

struct block *
funcgototarget(struct func *f, struct gotolabel *g)
{
	struct cleangoto *c;

	if (!gnucleanup)
		return g->label;
	c = arrayadd(&f->cleangotos, sizeof(*c));
	c->trampoline = mkblock("goto_cleanup");
	c->label = g;
	c->live = (struct array){0};
	if (f->cleanups.len)
		arrayaddbuf(&c->live, f->cleanups.val, f->cleanups.len);
	return c->trampoline;
}

void
funclabeldefined(struct func *f, struct gotolabel *g)
{
	if (!gnucleanup)
		return;
	g->cleanat.len = 0;
	if (f->cleanups.len)
		arrayaddbuf(&g->cleanat, f->cleanups.val, f->cleanups.len);
}

void
funcgotoflush(struct func *f)
{
	struct cleangoto *c;
	struct block *cont;
	size_t n, k, nl;

	if (!f->cleangotos.len)
		return;
	/* the body's last block keeps falling through to the end of the function, past the gotos' blocks */
	cont = mkblock("goto_end");
	funcjmp(f, cont);
	arrayforeach(&f->cleangotos, c) {
		struct ehobj *live = c->live.val, *at = c->label->cleanat.val;

		if (!c->label->defined)
			continue;
		n = c->live.len / sizeof(struct ehobj);
		nl = c->label->cleanat.len / sizeof(struct ehobj);
		for (k = 0; k < n && k < nl && live[k].addr == at[k].addr; ++k)
			;
		if (k < nl)
			error(&tok.loc, "a jump into the scope of an object with a cleanup attribute is not supported");
		funclabel(f, c->trampoline);
		cleancalls(f, live, k, n);
		funcjmp(f, c->label->label);
	}
	funclabel(f, cont);
}

void
funcinit(struct func *func, struct decl *d, struct init *init, bool hasinit)
{
	struct lvalue dst;
	struct value *src, *v;
	unsigned long long offset = 0, max = 0;
	size_t i, w;

	if (!d->value)   /* allocated before its initializer was parsed (decl.c) */
		funcalloc(func, d);
	if (d->u.obj.cleanup && gnucleanup) {
		struct ehobj *o = arrayadd(&func->cleanups, sizeof(*o));

		o->cleanup = d->u.obj.cleanup;
		o->fn = d->u.obj.cleanupfn->value;
		o->addr = d->value;
	} else if (d->u.obj.cleanup) {
		ehcleanupobj(func, d);
	}
	if (!hasinit)
		return;
	for (; init; init = init->next) {
		zero(func, d->value, d->type->align, offset, init->start);
		dst.bits = init->bits;
		if (init->expr->kind == EXPRSTRING) {
			w = init->expr->type->base->size;
			for (i = 0; i < init->expr->u.string.size && i * w < init->end - init->start; ++i) {
				v = mkintconst(init->start + i * w);
				dst.addr = funcinst(func, IADD, ptrclass, d->value, v);
				switch (w) {
				case 1: v = mkintconst(((unsigned char *)init->expr->u.string.data)[i]); break;
				case 2: v = mkintconst(((uint_least16_t *)init->expr->u.string.data)[i]); break;
				case 4: v = mkintconst(((uint_least32_t *)init->expr->u.string.data)[i]); break;
				}
				funcstore(func, init->expr->type->base, QUALNONE, dst, v);
			}
			offset = init->start + i * w;
		} else {
			if (offset < init->end && (dst.bits.before || dst.bits.after))
				zero(func, d->value, d->type->align, offset, init->end);
			dst.addr = d->value;
			/*
			QBE's memopt does not eliminate the store for ptr + 0,
			so only emit the add if the offset is non-zero
			*/
			if (init->start > 0)
				dst.addr = funcinst(func, IADD, ptrclass, dst.addr, mkintconst(init->start));
			src = funcexpr(func, init->expr);
			funcstore(func, init->expr->type, QUALNONE, dst, src);
			offset = init->end;
		}
		if (max < offset)
			max = offset;
	}
	zero(func, d->value, d->type->align, max, d->type->size);
}

static void
casesearch(struct func *f, int class, struct value *v, struct switchcase *c, struct block *defaultlabel, unsigned long long min, unsigned long long max)
{
	struct value *res, *key;
	struct block *label[3];

	if (!c) {
		funcjmp(f, defaultlabel);
		return;
	}
	if (c->node.key <= min && c->hi >= max) {   /* every value still possible is this case's */
		funcjmp(f, c->body);
		return;
	}
	label[0] = mkblock("switch_ne");
	label[1] = mkblock("switch_lt");
	label[2] = mkblock("switch_gt");

	key = mkintconst(c->node.key);
	if (c->hi == c->node.key) {
		res = funcinst(f, class == 'w' ? ICEQW : ICEQL, 'w', v, key);
	} else {   /* lo <= v <= hi, as v - lo <= hi - lo unsigned */
		res = funcinst(f, ISUB, class, v, key);
		res = funcinst(f, class == 'w' ? ICULEW : ICULEL, 'w', res, mkintconst(c->hi - c->node.key));
	}
	funcjnz(f, res, NULL, c->body, label[0]);
	funclabel(f, label[0]);
	res = funcinst(f, class == 'w' ? ICULTW : ICULTL, 'w', v, key);
	funcjnz(f, res, NULL, label[1], label[2]);
	funclabel(f, label[1]);
	casesearch(f, class, v, c->node.child[0], defaultlabel, min, c->node.key - 1);
	funclabel(f, label[2]);
	casesearch(f, class, v, c->node.child[1], defaultlabel, c->hi + 1, max);
}

/* the case of a constant controlling value, by the test casesearch makes (v - lo <= hi - lo, in the class's width) */
static struct switchcase *
casefind(struct switchcase *c, unsigned long long v, unsigned long long mask)
{
	struct switchcase *r;

	if (!c)
		return NULL;
	if ((v - c->node.key & mask) <= (c->hi - c->node.key & mask))
		return c;
	if ((r = casefind(c->node.child[0], v, mask)))
		return r;
	return casefind(c->node.child[1], v, mask);
}

void
funcswitch(struct func *f, struct value *v, struct switchcases *c, struct block *defaultlabel)
{
	int class = qbetype(c->type).base;

	if (v->kind == VALUE_INTCONST) {   /* switch (sizeof(*ptr)): straight to the case, the others unreachable */
		struct switchcase *k = casefind(c->root, v->u.i, class == 'w' ? 0xffffffffull : -1ull);

		funcjmp(f, k ? k->body : defaultlabel);
		return;
	}
	casesearch(f, class, v, c->root, defaultlabel, 0, -1);
}

/*
GNU extended inline assembly, lowered the way Cranelift's rustc backend lowers asm!: each statement becomes an
out-of-line function (a "thunk") written as assembly to a side file (main's -a), and the call site passes a pointer to a
stack slot that carries the operand values. The thunk owns register allocation -- it loads inputs from the slot into the
registers the constraints ask for, runs the user's template, and stores outputs back -- so the QBE IL never has to model
inline asm. x86_64 only, a deliberately small constraint subset; everything else is refused rather than miscompiled.
*/
FILE *asmout;
static unsigned asmthunkid;
static void emitname(struct value *);

/* x86_64 general registers, by size: [reg][0]=8, [1]=4, [2]=2, [3]=1 byte */
enum { RAX, RCX, RDX, RBX, RSI, RDI, RBP, RSP, R8, R9, R10, R11, R12, R13, R14, R15 };
static const char *const regname[16][4] = {
	{"rax","eax","ax","al"},   {"rcx","ecx","cx","cl"},   {"rdx","edx","dx","dl"},
	{"rbx","ebx","bx","bl"},   {"rsi","esi","si","sil"},  {"rdi","edi","di","dil"},
	{"rbp","ebp","bp","bpl"},  {"rsp","esp","sp","spl"},
	{"r8","r8d","r8w","r8b"},   {"r9","r9d","r9w","r9b"},   {"r10","r10d","r10w","r10b"},
	{"r11","r11d","r11w","r11b"},{"r12","r12d","r12w","r12b"},{"r13","r13d","r13w","r13b"},
	{"r14","r14d","r14w","r14b"},{"r15","r15d","r15w","r15b"},
};
/* caller-saved GP registers offered to a plain "r" operand (rdi is used only transiently for the slot pointer) */
static const int rpool[] = {RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11};

/*
The i386 targets (the kernel's real-mode code): the same numbers for the eight registers they have, with their names.
%esi and %edi have no byte form (an empty name), so a byte operand takes one of the other four.
*/
static const char *const regname386[8][4] = {
	{"eax","eax","ax","al"}, {"ecx","ecx","cx","cl"}, {"edx","edx","dx","dl"}, {"ebx","ebx","bx","bl"},
	{"esi","esi","si",""},   {"edi","edi","di",""},   {"ebp","ebp","bp",""},   {"esp","esp","sp",""},
};
static const int rpool386[] = {RAX, RCX, RDX};
static const int callee386[] = {RBX, RSI, RDI};
static const char *const (*regs)[4] = regname;   /* the names of the target being compiled */
static bool asmi386;       /* an i386 target: the thunk is 32-bit, its slot pointer in %eax (i386_regparm3) or at 4(%esp) */
static bool asmregparm3;
static char psfx = 'q';                 /* the suffix of push and pop */
static const char *msfx = "qlwb";       /* the suffix of a move, by column (regsizecol) */

/* the name of register r at column col: an empty name is a register the target has no form of at that size */
static const char *
asmregname(int r, int col)
{
	if (!*regs[r][col])
		error(&tok.loc, "asm operand needs a register the target has no %s form of", col == 3 ? "byte" : "this size");
	return regs[r][col];
}

/*
The register of an operand the constraint leaves to the compiler: a caller-saved one from the pool, else -- every one
is taken, as by the kernel's call_on_stack(), whose asm clobbers them all for the call it makes -- a callee-saved one,
which the thunk preserves; one is left for the thunk's slot pointer.
*/
static bool
bytereg(int r)
{
	return !asmi386 || r == RAX || r == RCX || r == RDX || r == RBX;
}

static bool
asmcallee(int r)
{
	if (asmi386)
		return r == RBX || r == RSI || r == RDI || r == RBP;
	return r == RBX || r == R12 || r == R13 || r == R14 || r == R15 || r == RBP;
}

/* a register for an operand the constraint leaves to the compiler; byte: it needs a byte form (i386) */
static int
asmpoolreg(const bool *used, unsigned *pool, bool byte)
{
	static const int callee[] = {R12, R13, R14, R15, RBX};
	const int *pl = asmi386 ? rpool386 : rpool, *ce = asmi386 ? callee386 : callee;
	unsigned npool = asmi386 ? countof(rpool386) : countof(rpool), nce = asmi386 ? countof(callee386) : countof(callee);
	unsigned k, nfree = 0;

	while (*pool < npool && used[pl[*pool]])
		++*pool;
	if (*pool < npool)
		return pl[(*pool)++];
	for (k = 0; k < nce; ++k)
		nfree += !used[ce[k]];
	if (nfree < 2)
		error(&tok.loc, "too many register asm operands");
	for (k = 0; used[ce[k]] || byte && !bytereg(ce[k]); ++k)
		;
	return ce[k];
}
static int
regsizecol(int sz)
{
	return sz == 8 ? 0 : sz == 4 ? 1 : sz == 2 ? 2 : 3;
}

/* the register a fixed-register constraint letter names, or -1 */
static int
fixedreg(int c)
{
	switch (c) {
	case 'a': return RAX;
	case 'b': return RBX;
	case 'c': return RCX;
	case 'd': return RDX;
	case 'S': return RSI;
	case 'D': return RDI;
	}
	return -1;
}

/* map a clobber name ("rax", "eax", ...) to a register index, or -1 */
static int
clobberreg(const char *name)
{
	int r, s;

	if (*name == '%')
		++name;
	for (r = 0; r < (asmi386 ? 8 : 16); ++r)
		for (s = 0; s < 4; ++s)
			if (*regs[r][s] && strcmp(name, regs[r][s]) == 0)
				return r;
	return -1;
}

struct asmrec {
	int reg;      /* register index, or -1 for an immediate */
	int size;     /* operand size in bytes (1,2,4,8) */
	int feedsize; /* a tied input wider than its output: the bytes the thunk loads into the register (0: size) */
	long slot;    /* byte offset of this operand's slot, or -1 (immediate, or tied: shares another's) */
	bool feed;    /* the thunk loads this operand from its slot on entry */
	bool prestore;/* the caller stores a value into this operand's slot before the call ("+" outputs and inputs) */
	bool back;    /* the thunk stores this operand to its slot on exit, and the caller reads it back */
	bool pseudo;  /* the %rsp register variable (ASM_CALL_CONSTRAINT): named in the template, never moved */
	bool mem;     /* a memory operand: the slot and the register carry the object's address; %N is (reg) */
	bool memsym;  /* a memory operand of an object (immsym, imm): the template names it, rip-relative, no slot */
	const char *flag;  /* a flag output "=@ccCOND": the condition, set from the flags right after the template */
	char *immsym; /* an immediate that is a symbol's address (plus imm): "i"(&x), "i"(f) */
	long imm;     /* immediate value, when reg == -1 */
	struct expr *expr;
	struct lvalue lval;   /* an output's destination (outputs only) */
	char *symname;
};

/* the register variable an asm operand names (register T x asm("REG")), or null */
static struct decl *
asmregvar(struct expr *e)
{
	if (e->kind == EXPRIDENT && e->u.ident.decl->kind == DECLOBJECT && e->u.ident.decl->regvar)
		return e->u.ident.decl;
	return NULL;
}

/* operand size from a type: scalars up to 8 bytes; anything else is refused */
static int
asmopsize(struct type *t)
{
	if (!(t->prop & PROPSCALAR) || t->size == 0 || t->size > 8 || asmi386 && t->size == 8)
		error(&tok.loc, "unsupported type for an asm operand");
	return t->size;
}

/* strip and record the leading constraint modifiers (= + & %); return the remaining class/tie body */
static const char *
asmconstraintbody(const char *c, bool *isout, bool *inout)
{
	*isout = *inout = false;
	for (;; ++c) {
		switch (*c) {
		case '=': *isout = true; continue;
		case '+': *isout = *inout = true; continue;
		case '&': case '%': continue;   /* early-clobber and commutativity: always satisfied by the thunk */
		}
		break;
	}
	return c;
}

/* the assembler name of a global value, as emitname spells it in the IL (without the sigil or the quotes) */
static char *
asmglobalname(struct value *v)
{
	size_t n = strlen(v->u.name) + 32;
	char *s = xmalloc(n);

	if (v->id)
		snprintf(s, n, ".L%s.%u", v->u.name, v->id);
	else
		snprintf(s, n, "%s", v->u.name);
	return s;
}

static bool
asmimmfits(const char *alt, long long v)
{
	const char *c;

	for (c = alt; *c; ++c) {
		switch (*c) {
		case 'i': case 'n': case 'g': return true;
		case 'I': if (v >= 0 && v <= 31) return true; break;
		case 'J': if (v >= 0 && v <= 63) return true; break;
		case 'K': if (v >= -128 && v <= 127) return true; break;
		case 'L': if (v == 0xff || v == 0xffff || v == 0xffffffffLL) return true; break;
		case 'M': if (v >= 0 && v <= 3) return true; break;
		case 'N': if (v >= 0 && v <= 255) return true; break;
		case 'e': if (v >= -0x80000000LL && v <= 0x7fffffffLL) return true; break;
		case 'Z': if (v >= 0 && v <= 0xffffffffLL) return true; break;
		}
	}
	return false;
}

/*
Whether an asm input is an immediate the constraint letters accept, filling in rec: an integer constant within the
letters' ranges, or the address of a function or static object ("i" and "s": the kernel's "i"(&symbol), "i"(func)).
A symbol named only here is kept alive under cproc -p by an IL comment in the function (asmrefs) that references it.
*/
static struct block *asmblock;   /* the block of the asm statement being lowered (funcasm) */

static bool
asmimm(struct expr *e, const char *alt, struct asmrec *rec)
{
	struct expr *c = eval(e);
	struct decl *d;
	long off = 0;

	if (c->kind == EXPRCONST && c->type->prop & PROPINT) {
		if (!asmimmfits(alt, c->u.constant.i))
			return false;
		rec->imm = c->u.constant.i;
		return true;
	}
	if (!strpbrk(alt, "isgp"))
		return false;
	while (c->kind == EXPRCAST)
		c = c->base;
	/* a symbol plus a byte offset (eval folds &s.member and &a[2] to &s + C): the kernel's "p"(&pcpu_hot.current_task) */
	if (c->kind == EXPRBINARY && c->op == TADD && c->type->kind == TYPEPOINTER && c->u.binary.r->kind == EXPRCONST) {
		off = c->u.binary.r->u.constant.i;
		for (c = c->u.binary.l; c->kind == EXPRCAST; c = c->base)
			;
	}
	if (c->kind == EXPRUNARY && c->op == TBAND)
		c = c->base;
	if (c->decayed)
		c = c->base;
	if (c->kind != EXPRIDENT)
		return false;
	d = c->u.ident.decl;
	if (!(d->kind == DECLFUNC || d->kind == DECLOBJECT && d->u.obj.storage != SDAUTO && !d->regvar) || !d->value)
		return false;
	rec->immsym = asmglobalname(d->value);
	rec->imm = off;
	arrayaddptr(&asmblock->asmrefs, d->value);   /* kept alive by the function, not by the file (cproc -p) */
	return true;
}

/* substitute one operand reference into the thunk, given its already-parsed modifier and index */
static void
asmsubst(struct asmrec *rec, unsigned total, int mod, unsigned idx)
{
	struct asmrec *r;

	if (idx >= total)
		error(&tok.loc, "asm operand index out of range");
	r = &rec[idx];
	if (r->memsym) {   /* an object's memory operand: the object itself, rip-relative (absolute on i386) */
		fputs(r->immsym, asmout);
		if (r->imm)
			fprintf(asmout, "%+ld", r->imm);
		if (!asmi386)
			fputs("(%rip)", asmout);
		return;
	}
	if (r->immsym) {   /* a symbol's address; %a addresses it, rip-relative as gcc writes it */
		switch (mod) {
		case 'c': case 'P': case 'p': case 'a': break;
		case 0:   fputc('$', asmout); break;
		default:  error(&tok.loc, "unsupported asm operand modifier '%%%c' on a symbol", mod);
		}
		fprintf(asmout, "%s", r->immsym);
		if (r->imm)
			fprintf(asmout, "%+ld", r->imm);
		if (mod == 'a' && !asmi386)
			fputs("(%rip)", asmout);
		return;
	}
	if (r->mem) {   /* memory: the object's address is in the register; P changes only a symbol */
		switch (mod) {
		case 0: case 'a': case 'b': case 'w': case 'k': case 'q': case 'P':
			fprintf(asmout, "(%%%s)", asmregname(r->reg, 0));
			return;
		}
		error(&tok.loc, "unsupported asm operand modifier '%%%c' on a memory operand", mod);
	}
	if (r->reg < 0) {   /* immediate */
		switch (mod) {
		case 'c': case 'P': case 'p': fprintf(asmout, "%ld", r->imm); break;   /* bare, as gcc prints them */
		case 'n': fprintf(asmout, "$%ld", -r->imm); break;
		default:  fprintf(asmout, "$%ld", r->imm); break;
		}
		return;
	}
	switch (mod) {
	case 'b': fprintf(asmout, "%%%s", asmregname(r->reg, 3)); break;
	case 'w': fprintf(asmout, "%%%s", asmregname(r->reg, 2)); break;
	case 'k': fprintf(asmout, "%%%s", asmregname(r->reg, 1)); break;
	case 'q': fprintf(asmout, "%%%s", asmregname(r->reg, 0)); break;
	case 'a': fprintf(asmout, "(%%%s)", asmregname(r->reg, 0)); break;   /* the address in the register */
	case 0:   fprintf(asmout, "%%%s", asmregname(r->reg, regsizecol(r->size))); break;
	default:  error(&tok.loc, "unsupported asm operand modifier '%%%c'", mod);
	}
}

/* the label an asm goto template jumps to for its label j: a stub in the thunk (funcasm1) */
static void
asmlabel(unsigned expid, unsigned j, unsigned nlab)
{
	if (j >= nlab)
		error(&tok.loc, "asm goto label index out of range");
	fprintf(asmout, ".Lnfcxx_goto_%u_%u", expid, j);
}

/* write the thunk body: template with %N / %[name] / %lN / %l[label] / %%/%= expanded */
static void
asmtemplate(const char *t, struct asmrec *rec, unsigned total, char **names, unsigned expid, char **labnames, unsigned nlab)
{
	const char *p;
	unsigned i;
	int mod;

	for (p = t; *p; ++p) {
		if (*p != '%') {
			fputc(*p, asmout);
			continue;
		}
		++p;
		if (*p == '%') { fputc('%', asmout); continue; }
		if (*p == '=') { fprintf(asmout, "%u", expid); continue; }
		if (*p == '{' || *p == '}' || *p == '|')
			error(&tok.loc, "asm dialect alternatives ('%%{') are not supported");
		mod = 0;
		if (*p && !isdigit((unsigned char)*p) && *p != '[') {
			mod = *p;
			++p;
		}
		if (*p == '[') {   /* %[name] symbolic reference */
			char buf[64];
			unsigned n = 0;
			++p;
			while (*p && *p != ']' && n < sizeof buf - 1)
				buf[n++] = *p++;
			buf[n] = 0;
			if (*p != ']')
				error(&tok.loc, "unterminated asm operand name");
			if (mod == 'l') {   /* asm goto: %l[label] */
				for (i = 0; i < nlab && strcmp(labnames[i], buf) != 0; ++i)
					;
				if (i == nlab)
					error(&tok.loc, "unknown asm goto label '%%l[%s]'", buf);
				asmlabel(expid, i, nlab);
				continue;
			}
			for (i = 0; i < total; ++i)
				if (names[i] && strcmp(names[i], buf) == 0)
					break;
			if (i == total)
				error(&tok.loc, "unknown asm operand '%%[%s]'", buf);
			asmsubst(rec, total, mod, i);
			continue;
		}
		if (!isdigit((unsigned char)*p))
			error(&tok.loc, "bad asm operand reference");
		i = 0;
		while (isdigit((unsigned char)*p))
			i = i * 10 + (*p++ - '0');
		--p;
		if (mod == 'l') {   /* asm goto: %lN counts the labels after the operands */
			asmlabel(expid, i < total ? nlab : i - total, nlab);
			continue;
		}
		asmsubst(rec, total, mod, i);
	}
}

static void
funcasm1(struct func *f, char *template, struct asmoperand *out, unsigned nout, struct asmoperand *in, unsigned nin, char **clob, unsigned nclob, bool isvolatile, struct gotolabel **labels, char **labnames, unsigned nlab)
{
	struct asmrec rec[32];
	char *names[32];
	bool used[16] = {0}, save[16] = {0};
	unsigned total = nout + nin, i, j, pool = 0, expid;
	long idxslot = -1;   /* asm goto: the slot cell the thunk writes the taken label to (0: none, j + 1: label j) */
	long slotsize = 0;
	int holder = -1, nsave, pad;
	struct value *base, *addr, *v, *fn;
	struct type *t;

	(void)isvolatile;   /* every lowered asm is a call, which QBE never reorders or removes */
	funcdecl(f)->u.func.hasasm = true;
	asmi386 = strncmp(targ->name, "i386", 4) == 0;
	asmregparm3 = strcmp(targ->name, "i386_regparm3") == 0;
	regs = asmi386 ? regname386 : regname;
	psfx = asmi386 ? 'l' : 'q';
	msfx = asmi386 ? "llwb" : "qlwb";
	if (strcmp(targ->name, "x86_64-sysv") != 0 && !asmi386)
		error(&tok.loc, "inline assembly is only supported on x86_64 and i386");
	if (!asmout)
		error(&tok.loc, "inline assembly is not available in this compilation mode");
	if (total > 32)
		error(&tok.loc, "too many asm operands");

	/* first mark the registers the fixed-register and clobber constraints pin down */
	for (i = 0; i < total; ++i) {
		struct asmoperand *op = i < nout ? &out[i] : &in[i - nout];
		bool isout, inout;
		int fr = fixedreg((unsigned char)*asmconstraintbody(op->constraint, &isout, &inout));
		struct decl *rv = asmregvar(op->expr);
		if (fr >= 0)
			used[fr] = true;
		if (rv && (fr = clobberreg(rv->regvar)) >= 0 && fr != RSP)
			used[fr] = true;   /* a register variable's register is not offered to other operands */
	}
	for (i = 0; i < nclob; ++i) {
		int r;
		if (strcmp(clob[i], "memory") == 0 || strcmp(clob[i], "cc") == 0)
			continue;
		r = clobberreg(clob[i]);
		if (r < 0)
			error(&tok.loc, "unknown asm clobber '%s'", clob[i]);
		if (r == RSP || r == RBP)
			error(&tok.loc, "asm may not clobber the stack or frame pointer");
		used[r] = true;
		save[r] = true;   /* a callee-saved clobber is preserved by the thunk (harmless on caller-saved; filtered below) */
	}

	/* parse every operand: assign registers, lay out the slot, classify direction */
	for (i = 0; i < total; ++i) {
		struct asmoperand *op = i < nout ? &out[i] : &in[i - nout];
		bool isout, inout, isin = i >= nout, hasq = false;
		const char *body = asmconstraintbody(op->constraint, &isout, &inout);
		int fr;

		names[i] = op->symname;
		rec[i].expr = op->expr;
		rec[i].reg = -1;
		rec[i].slot = -1;
		rec[i].feed = rec[i].prestore = rec[i].back = false;
		rec[i].pseudo = rec[i].mem = rec[i].memsym = false;
		rec[i].feedsize = 0;
		rec[i].flag = NULL;
		rec[i].immsym = NULL;
		rec[i].imm = 0;
		if (i < nout) {
			if (!isout)
				error(&tok.loc, "asm output operand lacks '=' or '+'");
			rec[i].feed = rec[i].prestore = inout;   /* "+": the current value is fed in */
			rec[i].back = true;
		} else if (isout) {
			error(&tok.loc, "asm input operand has an output constraint");
		}

		if (strncmp(body, "@cc", 3) == 0) {
			/* x86 flag output (__GCC_ASM_FLAG_OUTPUTS__): a register the thunk fills with set<cond> */
			static const char *const conds[] = {"a", "ae", "b", "be", "c", "e", "g", "ge", "l", "le", "na", "nae",
				"nb", "nbe", "nc", "ne", "ng", "nge", "nl", "nle", "no", "np", "ns", "nz", "o", "p", "pe", "po", "s", "z"};
			size_t k;

			for (k = 0; k < countof(conds) && strcmp(body + 3, conds[k]); ++k)
				;
			if (i >= nout || k == countof(conds))
				error(&tok.loc, "bad asm flag output constraint '%s'", op->constraint);
			if (!(op->expr->type->prop & PROPINT))
				error(&tok.loc, "asm flag output must have integer type");
			rec[i].flag = body + 3;
			rec[i].feed = rec[i].prestore = false;
			rec[i].reg = asmpoolreg(used, &pool, asmi386);   /* setcc: a byte register */
			used[rec[i].reg] = true;
			rec[i].size = asmopsize(op->expr->type);
			rec[i].slot = slotsize;
			slotsize += 8;
			continue;
		}
		if (isdigit((unsigned char)*body)) {   /* a tied operand: shares a matching output */
			unsigned m = 0;
			while (isdigit((unsigned char)*body))
				m = m * 10 + (*body++ - '0');
			if (i < nout || m >= nout)
				error(&tok.loc, "bad matching asm constraint");
			rec[i].reg = rec[m].reg;
			rec[i].size = asmopsize(op->expr->type);
			rec[m].feed = true;   /* the thunk loads the tied value the input writes into the output's slot */
			/* all of it: the kernel's put_user ties its user pointer to an int output, "=c"(ret) : "0"(ptr) */
			if (rec[i].size > rec[m].size && rec[i].size > rec[m].feedsize)
				rec[m].feedsize = rec[i].size;
			continue;
		}
		{
			/* GNU constraint letters, first alternative only (operands' alternatives are separated by ','): a constant
			 * goes to an immediate when an immediate letter allows it, as gcc chooses; then a register when any
			 * register letter is present; then memory */
			char alt[32];
			size_t n = 0;
			bool hasreg = false, hasmem = false, hasimm = false, anyreg = false;
			const char *c;

			for (c = body; *c && *c != ',' && n < sizeof alt - 1; ++c)
				alt[n++] = *c;
			alt[n] = 0;
			fr = -1;
			for (c = alt; *c; ++c) {
				switch (*c) {
				case 'q': case 'Q': hasq = true; /* fall through */
				case 'r': case 'R': case 'l': anyreg = hasreg = true; break;
				case 'g': anyreg = hasreg = hasmem = hasimm = true; break;
				/* an address: a symbol (plus an offset) as an immediate, otherwise the pointer in a register (%a) */
				case 'p': anyreg = hasreg = hasimm = true; break;
				case 'a': case 'b': case 'c': case 'd': case 'S': case 'D':
					hasreg = true;
					if (fr < 0)
						fr = fixedreg((unsigned char)*c);
					break;
				case 'm': case 'o': case 'V': hasmem = true; break;
				case 'i': case 'n': case 's': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N': case 'e':
				case 'Z': case 'E': case 'F': hasimm = true; break;
				case '*': case '#': case '!': case '?': case '^': break;   /* register preference hints */
				default:
					error(&tok.loc, "unsupported asm constraint '%s'", op->constraint);
				}
			}
			/* a memory operand of an object (*&sym: the pointer parameter of a funcclone, decl.c): the template names
			 * the object, rip-relative, with no register or slot, as gcc's inlined copy does */
			if (hasmem && !hasreg && !hasimm && op->expr->kind == EXPRUNARY && op->expr->op == TMUL &&
			    asmimm(op->expr->base, "p", &rec[i])) {
				rec[i].memsym = rec[i].mem = true;
				rec[i].reg = -1;
				rec[i].feed = rec[i].prestore = rec[i].back = false;
				rec[i].size = 8;
				continue;
			}
			if (hasimm && i >= nout && asmimm(op->expr, alt, &rec[i])) {
				rec[i].size = 8;
				continue;   /* no register, no slot */
			}
			if (asmregvar(op->expr) && hasreg) {
				/* a register variable takes its own register (GNU: "an operand in a register variable is in that register") */
				fr = clobberreg(asmregvar(op->expr)->regvar);
				if (fr < 0)
					error(&tok.loc, "unknown register '%s' for register variable", asmregvar(op->expr)->regvar);
				if (fr == RSP) {
					/* the stack pointer (the kernel's ASM_CALL_CONSTRAINT "+r"(current_stack_pointer)): the template may
					 * name it, but the thunk neither loads nor stores it -- the asm runs on the thunk's own stack */
					rec[i].reg = RSP;
					rec[i].size = 8;
					rec[i].pseudo = true;
					rec[i].feed = rec[i].prestore = rec[i].back = false;
					continue;
				}
			} else if (hasreg) {
				if (anyreg)
					fr = -1;   /* a generic register class wins over a fixed letter in the same alternative */
			} else if (hasmem) {
				/* memory: the slot carries the object's address, which the thunk loads into a register; %N is (reg),
				 * so the asm reads and writes the object itself and nothing is copied back */
				rec[i].mem = true;
				rec[i].back = false;
				rec[i].feed = rec[i].prestore = true;
			} else if (hasimm) {
				error(&tok.loc, "asm immediate operand is not an integer constant or a symbol address");
			} else {
				error(&tok.loc, "unsupported asm constraint '%s'", op->constraint);
			}
		}
		if (fr >= 0) {
			rec[i].reg = fr;
		} else {
			rec[i].reg = asmpoolreg(used, &pool, asmi386 && (hasq || op->expr->type->size == 1));
			used[rec[i].reg] = true;
		}
		rec[i].size = rec[i].mem ? asmi386 ? 4 : 8 : asmopsize(op->expr->type);
		rec[i].slot = slotsize;
		slotsize += 8;
		if (isin)
			rec[i].feed = rec[i].prestore = true;
	}

	if (nlab) {
		if (asanon)
			error(&tok.loc, "asm goto is not supported with -fsanitize=address");
		idxslot = slotsize;
		slotsize += 8;
	}

	/* choose a callee-saved register to hold the slot pointer; preserve it and any clobbered callee-saved register */
	for (j = 0; j < (asmi386 ? 3 : 5); ++j) {
		static const int cand[] = {RBX, R12, R13, R14, R15}, cand386[] = {RBX, RSI, RDI};
		int c = asmi386 ? cand386[j] : cand[j];

		if (!used[c]) { holder = c; break; }
	}
	if (holder < 0)
		error(&tok.loc, "asm uses too many registers");
	/* only callee-saved registers that are clobbered (or a callee-saved operand) need saving */
	for (i = 0; i < 16; ++i)
		save[i] = false;
	for (i = 0; i < nclob; ++i) {
		int r = (strcmp(clob[i], "memory") && strcmp(clob[i], "cc")) ? clobberreg(clob[i]) : -1;
		if (r >= 0 && asmcallee(r))
			save[r] = true;
	}
	for (i = 0; i < total; ++i) {   /* a callee-saved operand register ("b", or asmpoolreg's) is written: preserve it */
		int r = rec[i].reg;

		if (r >= 0 && asmcallee(r))
			save[r] = true;
	}
	save[holder] = false;   /* the holder is pushed and popped separately */

	expid = asmthunkid++;
	fn = xmalloc(sizeof *fn);
	fn->kind = VALUE_GLOBAL;
	fn->u.name = xmalloc(32);
	snprintf(fn->u.name, 32, "nfcxx_asm_thunk.%u", expid);
	fn->id = 0;
	fn->decl = NULL;

	/* ---- call site: build the slot, feed inputs, call, read outputs back ---- */
	base = NULL;
	if (slotsize) {
		struct block *end = f->end;
		f->end = f->start;
		base = funcinst(f, IALLOC8, ptrclass, mkintconst(slotsize), NULL);
		f->end = end;
	}
	for (i = 0; i < nout; ++i)   /* evaluate output destinations now; "+" feeds its current value in */
		if (!rec[i].pseudo)
			rec[i].lval = funclval(f, rec[i].expr);
	for (i = 0; i < nout; ++i) {
		if (!rec[i].prestore)
			continue;
		t = rec[i].expr->type;
		addr = rec[i].slot ? funcinst(f, IADD, ptrclass, base, mkintconst(rec[i].slot)) : base;
		if (rec[i].mem) {   /* "=m"/"+m": the slot carries the destination's address */
			funcinst(f, asmi386 ? ISTOREW : ISTOREL, 0, rec[i].lval.addr, addr);
			continue;
		}
		v = funcload(f, t, rec[i].lval);
		funcstore(f, t, 0, (struct lvalue){.addr = addr}, v);
	}
	for (i = nout; i < total; ++i) {
		long slot;
		bool o, io;
		const char *b;
		if (rec[i].reg < 0 || rec[i].pseudo)
			continue;   /* immediate (substituted into the thunk) or %rsp: no slot */
		if (rec[i].slot >= 0) {
			slot = rec[i].slot;   /* a plain register input */
		} else {   /* a tied input: store into the matching output's slot */
			unsigned m = 0;
			b = asmconstraintbody(in[i - nout].constraint, &o, &io);
			while (isdigit((unsigned char)*b))
				m = m * 10 + (*b++ - '0');
			slot = rec[m].slot;
		}
		t = rec[i].expr->type;
		addr = slot ? funcinst(f, IADD, ptrclass, base, mkintconst(slot)) : base;
		if (rec[i].mem) {
			/* "m": the object's address; an array is the array (not its decayed pointer); a value that is not an
			 * object is put in a temporary first, as gcc does */
			struct expr *me = rec[i].expr->decayed ? rec[i].expr->base : rec[i].expr;
			if (me->lvalue || me->kind == EXPRUNARY && me->op == TMUL) {
				v = funclval(f, me).addr;
			} else {
				struct decl *tmpd = mkdecl(NULL, DECLOBJECT, me->type, QUALNONE, LINKNONE);
				tmpd->u.obj.storage = SDAUTO;
				funcalloc(f, tmpd);
				funcstore(f, me->type, 0, (struct lvalue){.addr = tmpd->value}, funcexpr(f, me));
				v = tmpd->value;
			}
			funcinst(f, asmi386 ? ISTOREW : ISTOREL, 0, v, addr);
			continue;
		}
		v = funcexpr(f, rec[i].expr);
		funcstore(f, t, 0, (struct lvalue){.addr = addr}, v);
	}
	funcinst(f, ICALL, 0, fn, NULL);
	funcinst(f, IARG, ptrclass, slotsize ? base : mkintconst(0), NULL);
	for (i = 0; i < nout; ++i) {
		if (rec[i].pseudo || rec[i].mem)
			continue;
		t = rec[i].expr->type;
		addr = rec[i].slot ? funcinst(f, IADD, ptrclass, base, mkintconst(rec[i].slot)) : base;
		v = funcload(f, t, (struct lvalue){.addr = addr});
		funcstore(f, t, 0, rec[i].lval, v);
	}
	if (nlab) {   /* asm goto: on to the label the thunk took, the outputs stored on every way out */
		struct value *taken;

		addr = idxslot ? funcinst(f, IADD, ptrclass, base, mkintconst(idxslot)) : base;
		taken = funcinst(f, ILOADW, 'w', addr, NULL);
		for (j = 0; j < nlab; ++j) {
			struct block *next = mkblock("asm_goto_next");

			funcjnz(f, funcinst(f, ICEQW, 'w', taken, mkintconst(j + 1)), NULL, funcgototarget(f, labels[j]), next);
			funclabel(f, next);
		}
	}

	/* ---- thunk: load inputs, run the template, store outputs ---- */
	nsave = 0;
	for (i = 0; i < 16; ++i)
		nsave += save[i];
	/* keep %rsp 16-aligned for a call inside the template: 8 mod 16 on entry, so an even number of pushes (the holder
	 * and the saves) needs 8 more */
	pad = (1 + nsave) % 2 ? 0 : 8;
	if (asmi386)   /* i386 keeps no alignment promise (-mpreferred-stack-boundary=2): no pad */
		pad = 0;
	/* the slot pointer: the first argument, in %rdi (x86_64) or %eax (i386_regparm3), or on the stack (i386, cdecl:
	 * above the holder's push) */
	/* in the function's own section, where gcc's inlined copy of the template is: a thunk of a __head or __init
	 * function may name the object of an address clone (decl.c funcclone), which lasting .text must not */
	if (funcdecl(f)->section)
		fprintf(asmout, "\t.section %s,\"ax\",@progbits\n", funcdecl(f)->section);
	else
		fputs("\t.text\n", asmout);
	fprintf(asmout, "\t.p2align 4\nnfcxx_asm_thunk.%u:\n", expid);
	fprintf(asmout, "\tpush%c %%%s\n", psfx, regs[holder][0]);
	if (asmi386)
		fprintf(asmout, asmregparm3 ? "\tmovl %%eax, %%%s\n" : "\tmovl 8(%%esp), %%%s\n", regs[holder][0]);
	for (i = 0; i < 16; ++i)
		if (save[i])
			fprintf(asmout, "\tpush%c %%%s\n", psfx, regs[i][0]);
	if (pad)
		fprintf(asmout, "\tsubq $8, %%rsp\n");
	if (!asmi386)
		fprintf(asmout, "\tmovq %%rdi, %%%s\n", regs[holder][0]);
	for (i = 0; i < total; ++i)   /* load fed operands from the slot */
		if (rec[i].slot >= 0 && rec[i].feed) {
			int col = regsizecol(rec[i].feedsize > rec[i].size ? rec[i].feedsize : rec[i].size);
			fprintf(asmout, "\tmov%c %ld(%%%s), %%%s\n", msfx[col], rec[i].slot, regs[holder][0], asmregname(rec[i].reg, col));
		}
	fputs("\t", asmout);
	asmtemplate(template, rec, total, names, expid, labnames, nlab);
	fputc('\n', asmout);
	if (nlab)   /* asm goto: the template fell through (mov does not change the flags) */
		fprintf(asmout, "\tmovl $0, %ld(%%%s)\n.Lnfcxx_gend_%u:\n", idxslot, regs[holder][0], expid);
	for (i = 0; i < total; ++i)   /* flag outputs, before anything can change the flags (set and movzbl do not) */
		if (rec[i].flag)
			fprintf(asmout, "\tset%s %%%s\n\tmovzbl %%%s, %%%s\n", rec[i].flag, asmregname(rec[i].reg, 3),
				asmregname(rec[i].reg, 3), asmregname(rec[i].reg, 1));
	for (i = 0; i < total; ++i)   /* store written-back operands to the slot */
		if (rec[i].slot >= 0 && rec[i].back) {
			int col = regsizecol(rec[i].size);
			fprintf(asmout, "\tmov%c %%%s, %ld(%%%s)\n", msfx[col], asmregname(rec[i].reg, col), rec[i].slot, regs[holder][0]);
		}
	if (pad)
		fprintf(asmout, "\taddq $8, %%rsp\n");
	for (i = 16; i-- > 0;)
		if (save[i])
			fprintf(asmout, "\tpop%c %%%s\n", psfx, regs[i][0]);
	fprintf(asmout, "\tpop%c %%%s\n\tret\n", psfx, regs[holder][0]);
	for (j = 0; j < nlab; ++j)   /* asm goto: each label's stub records it and leaves the way a fall-through does */
		fprintf(asmout, ".Lnfcxx_goto_%u_%u:\n\tmovl $%u, %ld(%%%s)\n\tjmp .Lnfcxx_gend_%u\n", expid, j, j + 1, idxslot,
			regs[holder][0], expid);
}

/* the IL name of a global value as emitname spells it, without the sigil: what cproc -p's pruning calls the item */
static void
valuename(struct value *v, char *buf, size_t n)
{
	const char *q = v->kind & VALUE_QUOTE ? "\"" : "";

	if (v->id)
		snprintf(buf, n, ".L%s%s%s.%u", q, v->u.name, q, v->id);
	else
		snprintf(buf, n, "%s%s%s", q, v->u.name, q);
}

/*
An asm statement. The thunk is written to a temporary file and kept with its block once it is complete; emitfunc
writes the thunks of the blocks that can be reached to the side file, after a "#nfcxx:owner NAME" line naming the
function, so cproc -p can drop the thunks of the functions it drops. Under -p a refusal is deferred: error() jumps
back here, the block records it (lazyerror), and it is reported only if the block can be reached (emitfunc writes it
into the function's IL) and pruning keeps the function -- the kernel's always_inline helpers ask for "i"(1 << (nr & 7)),
satisfiable only after inlining, in functions that are dead without it.
*/
void
funcasm(struct func *f, char *template, struct asmoperand *out, unsigned nout, struct asmoperand *in, unsigned nin, char **clob, unsigned nclob, bool isvolatile, struct gotolabel **labels, char **labnames, unsigned nlab)
{
	jmp_buf jb, *savedjmp = errorjmp;
	FILE *real = asmout, *th = NULL;
	struct block *b = f->end;
	char buf[4096];
	size_t n;

	if (b->jump.kind)   /* after a jump, return or break: never run (funcinst drops the call too) */
		return;
	if (real && !(th = tmpfile()))
		fatal("tmpfile:");
	asmout = th;
	asmblock = b;
	if (prune) {
		if (setjmp(jb)) {
			errorjmp = savedjmp;
			asmout = real;
			if (th)
				fclose(th);
			if (!b->lazyerror) {
				b->lazyerror = xmalloc(strlen(errorbuf) + 1);
				strcpy(b->lazyerror, errorbuf);
			}
			return;
		}
		errorjmp = &jb;
	}
	funcasm1(f, template, out, nout, in, nin, clob, nclob, isvolatile, labels, labnames, nlab);
	errorjmp = savedjmp;
	asmout = real;
	if (th) {
		rewind(th);
		while ((n = fread(buf, 1, sizeof buf, th)) > 0)
			arrayaddbuf(&b->thunks, buf, n);
		fclose(th);
	}
}

/*
A file-scope asm. Its text joins the side file as a "#nfcxx:keep" chunk (kept by cproc -p's pruning, main.c) after
.text, the section an assembly file starts in, where gcc puts it; the kernel's uses switch sections themselves
(.section ... .previous, .pushsection ... .popsection).
*/
void
emitasm(const char *text)
{
	if (!asmout)
		error(&tok.loc, "inline assembly is only supported on x86_64 ELF (cproc -a)");
	fprintf(asmout, "#nfcxx:keep\n\t.text\n%s\n", text);
}

/* the assembler's name of a global value, as QBE writes it on ELF */
static void
asmsymname(struct value *v, FILE *f)
{
	if (v->kind & VALUE_QUOTE)
		fprintf(f, "\"%s\"", v->u.name);
	else if (v->id)
		fprintf(f, ".L%s.%u", v->u.name, v->id);
	else
		fputs(v->u.name, f);
}

/*
GNU weak and visibility on a global: directives in the inline-asm side file, after the code that defines or uses the
symbol. Under cproc -p the chunk ("#nfcxx:symattr NAME", main.c asmprune) stays only when a live item defines or
names the symbol: an unused weak declaration would otherwise be a weak undefined symbol gcc's object does not have.
A symbol the unit only declares can still be named by a live item only from code QBE drops (the block of an
if (0 && ...)), and the directive alone would make it an undefined symbol: its directives are marked
"#nfcxx:ifused NAME", and qbe-cc keeps them only when the final assembly names the symbol elsewhere.
*/
void
emitsymattr(struct decl *d)
{
	bool undef;

	/* without the side file (Mach-O, the CIL backend) the attributes stay without effect, as before cproc took them:
	 * nfcxx's weak-symbols.rb marks EDG's COMDAT functions weak in the assembly there. Under -p (the Linux kernel,
	 * x86-64 ELF) they would be lost, so that is refused. */
	if (!asmout) {
		if (prune)
			error(&tok.loc, "the weak and visibility attributes need the inline-asm side file (x86_64 ELF, -a)");
		return;
	}
	if (!d->value)
		return;
	undef = !d->defined && !d->tentative && !d->alias;
	fputs("#nfcxx:symattr ", asmout);
	asmsymname(d->value, asmout);
	fputs("\n", asmout);
	if (d->weak) {
		if (undef) {
			fputs("#nfcxx:ifused ", asmout);
			asmsymname(d->value, asmout);
			fputc('\n', asmout);
		}
		fputs("\t.weak ", asmout);
		asmsymname(d->value, asmout);
		fputc('\n', asmout);
	}
	if (d->visibility && strcmp(d->visibility, "default")) {
		if (undef) {
			fputs("#nfcxx:ifused ", asmout);
			asmsymname(d->value, asmout);
			fputc('\n', asmout);
		}
		fprintf(asmout, "\t.%s ", d->visibility);
		asmsymname(d->value, asmout);
		fputc('\n', asmout);
	}
}

/*
A GNU alias, T name(...) __attribute__((alias("target"))): the declaration defines name as target, a symbol of this
unit. The side file gets .set with the binding and type gcc gives it, and a top-level "# nfcxx:ref $target" line in
the IL keeps the target under cproc -p.
*/
void
emitalias(struct decl *d)
{
	struct decl *t = scopegetdecl(&filescope, d->alias, false);
	struct value tv = {.kind = VALUE_GLOBAL, .u.name = d->alias};

	if (!asmout)
		error(&tok.loc, "the alias attribute needs the inline-asm side file (x86_64 ELF, -a)");
	if (!d->value)
		d->value = mkglobal(d);
	fputs("#nfcxx:keep\n", asmout);
	if (d->linkage == LINKEXTERN) {
		fputs(d->weak ? "\t.weak " : "\t.globl ", asmout);
		asmsymname(d->value, asmout);
		fputc('\n', asmout);
	}
	fputs("\t.set ", asmout);
	asmsymname(d->value, asmout);
	fputs(", ", asmout);
	asmsymname(t && t->value ? t->value : &tv, asmout);
	fputs("\n\t.type ", asmout);
	asmsymname(d->value, asmout);
	fprintf(asmout, ", @%s\n", d->kind == DECLFUNC ? "function" : "object");
	fputs("# nfcxx:ref ", stdout);
	emitname(t && t->value ? t->value : &tv);
	putchar('\n');
}

/* emit */

/*
The inline asm of the blocks that can be reached from the start (block->reach): each thunk to the side file after a
"#nfcxx:owner NAME" line, the symbols the thunks name as "# nfcxx:ref" lines in the function's IL, and the first
deferred refusal as "# nfcxx:error" (reported by cproc -p if the function is kept, main.c ilprune). Called inside the
function's braces. QBE drops the unreachable blocks, and with them the calls of the thunks left out.
*/
static void
funcasmout(struct func *f)
{
	struct array stack = {0};
	struct block *b;
	struct value **r;
	char name[256];
	bool erred = false;
	size_t i;

	f->start->reach = true;
	arrayaddptr(&stack, f->start);
	while (stack.len) {
		stack.len -= sizeof(b);
		b = *(struct block **)((char *)stack.val + stack.len);
		for (i = 0; i < 2; ++i) {
			struct block *s;

			switch (b->jump.kind) {
			case JUMP_NONE: s = i == 0 ? b->next : NULL; break;   /* falls through to the next block */
			case JUMP_JMP:  s = i == 0 ? b->jump.blk[0] : NULL; break;
			case JUMP_JNZ:  s = b->jump.blk[i]; break;
			default:        s = NULL;
			}
			if (s && !s->reach) {
				s->reach = true;
				arrayaddptr(&stack, s);
			}
		}
	}
	free(stack.val);
	valuename(f->decl->value, name, sizeof name);
	for (b = f->start; b; b = b->next) {
		if (!b->reach)
			continue;
		if (b->lazyerror && !erred) {
			printf("# nfcxx:error %s\n", b->lazyerror);
			erred = true;
			f->decl->u.func.refused = true;   /* a call with constant arguments may get a clone (decl.c funcclone) */
		}
		arrayforeach(&b->asmrefs, r) {
			fputs("# nfcxx:ref ", stdout);
			emitname(*r);
			putchar('\n');
		}
		if (b->thunks.len && asmout) {
			fprintf(asmout, "#nfcxx:owner %s\n", name);
			fwrite(b->thunks.val, 1, b->thunks.len, asmout);
		}
	}
}

static void
emitname(struct value *v)
{
	static const char sigil[] = {
		[VALUE_TEMP] = '%',
		[VALUE_GLOBAL] = '$',
		[VALUE_TYPE] = ':',
		[VALUE_LABEL] = '@',
	};
	int kind;

	kind = v->kind & 0xf;
	if (kind >= countof(sigil) || !sigil[kind])
		fatal("invalid value");
	putchar(sigil[kind]);
	emitbarename(v);
}

/* a name as emitname writes it, without the sigil */
static void
emitbarename(struct value *v)
{
	if ((v->kind & 0xf) == VALUE_GLOBAL && v->id)
		fputs(".L", stdout);
	if (v->kind & VALUE_QUOTE)
		putchar('"');
	if (v->u.name)
		fputs(v->u.name, stdout);
	if (v->kind & VALUE_QUOTE)
		putchar('"');
	if (v->id)
		printf(".%u", v->id);
}

static void
emitvalue(struct value *v)
{
	switch (v->kind & 0xf) {
	case VALUE_INTCONST:
		printf("%llu", v->u.i);
		break;
	case VALUE_FLTCONST:
		printf("s_%.17g", v->u.f);
		break;
	case VALUE_DBLCONST:
		printf("d_%.17g", v->u.f);
		break;
	case VALUE_GLOBAL:
		if (v->kind & VALUE_EXTERN)
			fputs("extern ", stdout);
		if (v->kind & VALUE_THREAD)
			fputs("thread ", stdout);
		/* fallthrough */
	default:
		emitname(v);
		break;
	}
}

static void
emitclass(int class, struct value *v)
{
	if (v && v->kind == VALUE_TYPE)
		emitname(v);
	else if (class)
		putchar(class);
	else
		fatal("type has no QBE representation");
}

/* XXX: need to consider _Alignas on struct members */
static void
emittype(struct type *t)
{
	static unsigned id;
	static struct value soft = {.kind = VALUE_TYPE, .u.name = "__nfcxx_soft16"};
	static struct value ldmem = {.kind = VALUE_TYPE, .u.name = "__nfcxx_ldmem"};
	static bool softemitted, ldemitted;
	struct member *m, *other;
	struct type *sub;
	unsigned long long off, qoff;
	int natalign;

	if (t->kind == TYPELDOUBLE) {
		/* long double: class X87 in the SysV ABI, so an argument is in memory (a dark type of 16 bytes), and a result is
		 * in st(0), which a call pops into a temporary (funccall, funcret) */
		if (!ldemitted) {
			ldemitted = true;
			puts("type :__nfcxx_ldmem = align 16 { 16 }");
		}
		t->value = &ldmem;
		return;
	}
	if (t->prop & PROPSOFT) {
		/* the aggregate of a 16-byte floating value: two integer eightbytes, 16-aligned */
		if (!softemitted) {
			softemitted = true;
			puts("type :__nfcxx_soft16 = align 16 { l, l }");
		}
		t->value = &soft;
		return;
	}
	if (t->value || t->kind != TYPESTRUCT && t->kind != TYPEUNION)
		return;
	t->value = xmalloc(sizeof(*t->value));
	t->value->kind = VALUE_TYPE;
	t->value->u.name = t->u.structunion.tag;
	t->value->id = ++id;
	for (m = t->u.structunion.members; m; m = m->next) {
		for (sub = m->type; sub->kind == TYPEARRAY; sub = sub->base)
			;
		emittype(sub);
	}
	fputs("type ", stdout);
	emitname(t->value);
	if (t == targ->typevalist) {
		printf(" = align %d { %llu }\n", t->align, t->size);
		return;
	}
	/* QBE places each member at its natural alignment, and aligns and sizes the aggregate by its members. A C
	 * alignment above that (_Alignas, __attribute__((aligned(N))), Rust's repr(align)) is given to QBE explicitly:
	 * byte padding before a member whose C offset is further on, `align` on the type, and padding at its end. */
	natalign = 1;
	for (m = t->u.structunion.members; m; m = m->next) {
		for (sub = m->type; sub->kind == TYPEARRAY; sub = sub->base)
			;
		if (sub->align > natalign)
			natalign = sub->align;
	}
	fputs(" = ", stdout);
	if (t->align > natalign)
		printf("align %d ", t->align);
	fputs("{ ", stdout);
	qoff = 0;
	for (m = t->u.structunion.members, off = 0; m;) {
		if (t->kind == TYPESTRUCT) {
			/* look for a subsequent member with a larger storage unit */
			for (other = m->next; other; other = other->next) {
				if (other->offset >= ALIGNUP(m->offset + 1, 8))
					break;
				if (other->offset <= m->offset)
					m = other;
			}
			off = m->offset + m->type->size;
		} else {
			fputs("{ ", stdout);
		}
		for (sub = m->type; sub->kind == TYPEARRAY; sub = sub->base)
			;
		if (t->kind == TYPESTRUCT) {
			qoff = ALIGNUP(qoff, sub->align);
			if (m->offset > qoff) {
				printf("b %llu, ", m->offset - qoff);
				qoff = m->offset;
			}
			qoff += m->type->size;
		}
		if (targ->ilp32 && sub->prop & PROPSCALAR && (sub->size == 8 && !(sub->prop & PROPSOFT) || sub->kind == TYPELDOUBLE)) {
			/* ILP32: an 8-byte scalar (long long, double) is aligned on 4 in a struct, QBE's l and d are on 8; a
			 * long double is 12 bytes on 4 */
			printf("w %llu", m->type->size / 4);
		} else {
			emitclass(qbetype(sub).data, sub->value);
			if (m->type->size > sub->size)
				printf(" %llu", m->type->size / sub->size);
		}
		if (t->kind == TYPESTRUCT) {
			fputs(", ", stdout);
			/* skip subsequent members contained within the same storage unit */
			do m = m->next;
			while (m && m->offset < off);
		} else {
			fputs(" } ", stdout);
			m = m->next;
		}
	}
	/* the C size can be larger than QBE's rounding of the members (a trailing _Alignas member, a union of an
	 * over-aligned type): pad to it */
	if (t->kind == TYPESTRUCT) {
		if (t->size > ALIGNUP(qoff, t->align > natalign ? t->align : natalign))
			printf("b %llu, ", t->size - qoff);
	}
	puts("}");
}

static struct inst **
emitinst(struct inst **instp, struct inst **instend)
{
	int op, first;
	struct inst *inst = *instp;

	putchar('\t');
	assert(inst->kind < countof(instname));
	if (inst->res.kind) {
		emitvalue(&inst->res);
		fputs(" =", stdout);
		emitclass(inst->class, inst->arg[1]);
		putchar(' ');
	}
	fputs(instname[inst->kind], stdout);
	putchar(' ');
	emitvalue(inst->arg[0]);
	++instp;
	op = inst->kind;
	switch (op) {
	case ICALL:
		putchar('(');
		for (first = 1; instp != instend; ++instp) {
			inst = *instp;
			if (inst->kind == IVARARG) {
				/* no comma before the marker when no fixed argument precedes it */
				fputs(first ? "..." : ", ...", stdout);
				first = 0;
				continue;
			}
			if (inst->kind != IARG)
				break;
			if (first)
				first = 0;
			else
				fputs(", ", stdout);
			emitclass(inst->class, inst->arg[1]);
			putchar(' ');
			emitvalue(inst->arg[0]);
		}
		putchar(')');
		break;
	default:
		if (inst->arg[1]) {
			fputs(", ", stdout);
			emitvalue(inst->arg[1]);
		}
		if (inst->arg[2]) {
			fputs(", ", stdout);
			emitvalue(inst->arg[2]);
		}
	}
	putchar('\n');
	return instp;
}

static void
emitjump(struct jump *j)
{
	switch (j->kind) {
	case JUMP_NONE:
		break;
	case JUMP_RET:
		fputs("\tret", stdout);
		if (j->arg) {
			fputc(' ', stdout);
			emitvalue(j->arg);
		}
		putchar('\n');
		break;
	case JUMP_JMP:
		fputs("\tjmp ", stdout);
		emitname(&j->blk[0]->label);
		putchar('\n');
		break;
	case JUMP_JNZ:
		fputs("\tjnz ", stdout);
		emitvalue(j->arg);
		fputs(", ", stdout);
		emitname(&j->blk[0]->label);
		fputs(", ", stdout);
		emitname(&j->blk[1]->label);
		putchar('\n');
		break;
	case JUMP_HLT:
		fputs("\thlt\n", stdout);
		break;
	default:
		assert(0);
	}
}

/*
cproc -p (the kernel): sparse conditional constant propagation through the function's temporaries and its stack slots
whose address only loads and stores use (no call, arithmetic, blit or jump sees it, so nothing else reads or writes the
slot). A conditional jump whose condition is the same constant on every way that reaches it becomes a jump, and what only
the other way reached is unreachable (emitfunc's "# nfcxx:dead", main.c's pruning), as gcc folds it: the kernel's
fpu/signal.c clears a flag with &= IS_ENABLED(CONFIG_IA32_EMULATION), and the call that the flag guards names a function
this configuration does not have. Only under -p -V, where a volatile access is a call (funcvolatile), and not with
-fsanitize=address, a landing pad or a setjmp (whose second return the slots do not show). A function in which a
condition is still undetermined at the end is left as it is.
*/
enum { SCTOP, SCCON, SCBOT };

struct scval {
	unsigned char kind, size;   /* size: a slot's, the bytes of the store that set it */
	unsigned long long c;
};

struct sccp {
	struct scval *tmp;   /* by temporary id */
	int *slot;           /* by temporary id: the slot's number, or -1 */
	unsigned ntmp, nslot, nblk;
	struct block **blk;  /* by number */
	struct scval *in;    /* nblk by nslot: the slots where the block begins */
	bool *exec;          /* by number: the block can be reached */
	bool (*edge)[2];     /* by number: the block's ways (scsucc) that can be taken */
	bool changed;
};

static const struct scval scbot = {SCBOT};

static struct scval
scmeet(struct scval a, struct scval b)
{
	if (a.kind == SCTOP)
		return b;
	if (b.kind == SCTOP || (a.kind == SCCON && b.kind == SCCON && a.c == b.c && a.size == b.size))
		return a;
	return scbot;
}

static bool
scsame(struct scval a, struct scval b)
{
	return a.kind == b.kind && (a.kind != SCCON || (a.c == b.c && a.size == b.size));
}

static struct scval
sccon(unsigned long long c)
{
	return (struct scval){SCCON, 0, c};
}

static unsigned long long
scmask(unsigned bytes)
{
	return bytes >= 8 ? ~0ull : (1ull << bytes * 8) - 1;
}

static unsigned long long
scsext(unsigned long long c, unsigned bytes)
{
	unsigned shift = 64 - bytes * 8;

	return shift ? (unsigned long long)((long long)(c << shift) >> shift) : c;
}

static struct block *
scsucc(struct block *b, int i)
{
	switch (b->jump.kind) {
	case JUMP_NONE: return i == 0 ? b->next : NULL;
	case JUMP_JMP:  return i == 0 ? b->jump.blk[0] : NULL;
	case JUMP_JNZ:  return b->jump.blk[i];
	default:        return NULL;
	}
}

static struct scval
scvalue(struct sccp *s, struct value *v)
{
	if (v && v->kind == VALUE_INTCONST)
		return sccon(v->u.i);
	if (v && v->kind == VALUE_TEMP && v->id < s->ntmp)
		return s->tmp[v->id];
	return scbot;
}

static int
scslot(struct sccp *s, struct value *v)
{
	return v && v->kind == VALUE_TEMP && v->id < s->ntmp ? s->slot[v->id] : -1;
}

static void
scset(struct sccp *s, struct value *res, struct scval v)
{
	struct scval m;

	if (res->kind != VALUE_TEMP || res->id >= s->ntmp)
		return;
	m = scmeet(s->tmp[res->id], v);
	if (!scsame(m, s->tmp[res->id])) {
		s->tmp[res->id] = m;
		s->changed = true;
	}
}

/* the bytes a load or store of the slot moves, or 0 for one that is not an integer's */
static unsigned
scaccess(int kind)
{
	switch (kind) {
	case ILOADL: case ISTOREL: return 8;
	case ILOADW: case ISTOREW: return 4;
	case ILOADSH: case ILOADUH: case ISTOREH: return 2;
	case ILOADSB: case ILOADUB: case ISTOREB: return 1;
	}
	return 0;
}

/* an integer instruction's result from constant operands (class w or l), or false */
static bool
scfold(int op, int class, unsigned long long a, unsigned long long b, unsigned long long *r)
{
	unsigned bytes = class == 'w' ? 4 : 8, bits = bytes * 8;
	unsigned long long m = scmask(bytes);
	long long sa = scsext(a, bytes), sb = scsext(b, bytes);
	long long smin = bytes == 4 ? INT32_MIN : INT64_MIN;
	bool w = op >= ICEQW && op <= ICUGTW;

	if (op >= ICEQW && op <= ICUGTL) {   /* the operands' width is the comparison's, the result is 0 or 1 */
		unsigned cb = w ? 4 : 8;
		unsigned long long ua = a & scmask(cb), ub = b & scmask(cb);
		long long xa = scsext(a, cb), xb = scsext(b, cb);

		switch (w ? op : op - (ICEQL - ICEQW)) {
		case ICEQW:  *r = ua == ub; break;
		case ICNEW:  *r = ua != ub; break;
		case ICSLEW: *r = xa <= xb; break;
		case ICSLTW: *r = xa < xb; break;
		case ICSGEW: *r = xa >= xb; break;
		case ICSGTW: *r = xa > xb; break;
		case ICULEW: *r = ua <= ub; break;
		case ICULTW: *r = ua < ub; break;
		case ICUGEW: *r = ua >= ub; break;
		case ICUGTW: *r = ua > ub; break;
		default: return false;
		}
		return true;
	}
	if (class != 'w' && class != 'l')
		return false;
	a &= m, b &= m;
	switch (op) {
	case IADD: *r = a + b; break;
	case ISUB: *r = a - b; break;
	case IMUL: *r = a * b; break;
	case IAND: *r = a & b; break;
	case IOR:  *r = a | b; break;
	case IXOR: *r = a ^ b; break;
	case INEG: *r = -a; break;
	case ISHL: *r = a << (b & (bits - 1)); break;
	case ISHR: *r = a >> (b & (bits - 1)); break;
	case ISAR: *r = (unsigned long long)(sa >> (b & (bits - 1))); break;
	case IUDIV: if (!b) return false; *r = a / b; break;
	case IUREM: if (!b) return false; *r = a % b; break;
	case IDIV: if (!b || (sb == -1 && sa == smin)) return false; *r = (unsigned long long)(sa / sb); break;
	case IREM: if (!b || (sb == -1 && sa == smin)) return false; *r = (unsigned long long)(sa % sb); break;
	case IEXTSW: *r = scsext(a, 4); break;
	case IEXTUW: *r = a & scmask(4); break;
	case IEXTSH: *r = scsext(a, 2); break;
	case IEXTUH: *r = a & scmask(2); break;
	case IEXTSB: *r = scsext(a, 1); break;
	case IEXTUB: *r = a & scmask(1); break;
	case ICOPY: *r = a; break;
	default: return false;
	}
	*r &= m;
	return true;
}

static struct scval
scinst(struct sccp *s, struct inst *inst, struct scval *cur)
{
	unsigned bytes = scaccess(inst->kind);
	unsigned long long m = scmask(inst->class == 'w' ? 4 : 8), r;
	struct scval a, b;
	int k;

	if (bytes && inst->kind >= ILOADD && inst->kind <= ILOADUB) {
		k = scslot(s, inst->arg[0]);
		if (k < 0 || cur[k].kind == SCBOT)
			return scbot;
		if (cur[k].kind == SCTOP)
			return cur[k];
		if (cur[k].size != bytes)
			return scbot;
		r = cur[k].c;
		if (inst->kind != ILOADUH && inst->kind != ILOADUB)
			r = scsext(r, bytes);
		return sccon(r & m);
	}
	if (inst->kind == IAND || inst->kind == IMUL || inst->kind == IOR) {
		/* x & 0 and x * 0 are 0, x | ~0 is ~0, whatever x is */
		a = scvalue(s, inst->arg[0]), b = scvalue(s, inst->arg[1]);
		if (a.kind == SCCON && b.kind != SCCON)
			b = a, a = scvalue(s, inst->arg[1]);
		if (b.kind == SCCON && a.kind != SCCON && (inst->class == 'w' || inst->class == 'l')) {
			if (inst->kind != IOR && (b.c & m) == 0)
				return sccon(0);
			if (inst->kind == IOR && (b.c & m) == m)
				return sccon(m);
		}
	}
	switch (inst->kind) {
	case IADD: case ISUB: case IMUL: case IUDIV: case IUREM: case IDIV: case IREM:
	case IOR: case IXOR: case IAND: case ISAR: case ISHR: case ISHL:
	case INEG: case IEXTSW: case IEXTUW: case IEXTSH: case IEXTUH: case IEXTSB: case IEXTUB: case ICOPY:
	case ICEQW: case ICNEW: case ICSLEW: case ICSLTW: case ICSGEW: case ICSGTW: case ICULEW: case ICULTW: case ICUGEW: case ICUGTW:
	case ICEQL: case ICNEL: case ICSLEL: case ICSLTL: case ICSGEL: case ICSGTL: case ICULEL: case ICULTL: case ICUGEL: case ICUGTL:
		a = scvalue(s, inst->arg[0]);
		b = inst->arg[1] ? scvalue(s, inst->arg[1]) : sccon(0);
		if (a.kind == SCBOT || b.kind == SCBOT)
			return scbot;
		if (a.kind == SCTOP || b.kind == SCTOP)
			return (struct scval){SCTOP};
		return scfold(inst->kind, inst->class, a.c, b.c, &r) ? sccon(r) : scbot;
	}
	return scbot;
}

/* the block from where it begins, with the slots in cur (updated): its temporaries, then the ways out */
static void
scblock(struct sccp *s, struct block *b, struct scval *cur)
{
	struct inst **ip, **end;
	struct block *p, *succ;
	struct scval v, c;
	unsigned i, j, k;

	if (b->phi.res.kind) {
		v = (struct scval){SCTOP};
		for (i = 0; i < 2; ++i) {
			if (!(p = b->phi.blk[i]) || !s->exec[p->idx])
				continue;
			for (j = 0; j < 2; ++j)
				if (s->edge[p->idx][j] && scsucc(p, j) == b)
					v = scmeet(v, scvalue(s, b->phi.val[i]));
		}
		scset(s, &b->phi.res, v);
	}
	end = (struct inst **)((char *)b->insts.val + b->insts.len);
	for (ip = b->insts.val; ip != end; ++ip) {
		struct inst *inst = *ip;
		unsigned bytes = scaccess(inst->kind);

		if (inst->kind >= ISTORED && inst->kind <= ISTOREB) {
			int sl = scslot(s, inst->arg[1]);

			if (sl >= 0) {
				v = bytes ? scvalue(s, inst->arg[0]) : scbot;
				if (v.kind == SCCON)
					v.c &= scmask(bytes);
				v.size = bytes;
				cur[sl] = v;
			}
			continue;
		}
		if (inst->res.kind == VALUE_TEMP)
			scset(s, &inst->res, scinst(s, inst, cur));
	}
	c = b->jump.kind == JUMP_JNZ ? scvalue(s, b->jump.arg) : scbot;
	for (i = 0; i < 2; ++i) {
		if (!(succ = scsucc(b, i)))
			continue;
		if (b->jump.kind == JUMP_JNZ && (c.kind == SCTOP || (c.kind == SCCON && (c.c != 0) != (i == 0))))
			continue;
		if (!s->edge[b->idx][i])
			s->edge[b->idx][i] = s->changed = true;
		if (!s->exec[succ->idx]) {
			s->exec[succ->idx] = s->changed = true;
			memcpy(s->in + (size_t)succ->idx * s->nslot, cur, s->nslot * sizeof(*cur));
			continue;
		}
		for (k = 0; k < s->nslot; ++k) {
			struct scval *t = s->in + (size_t)succ->idx * s->nslot + k;

			v = scmeet(*t, cur[k]);
			if (!scsame(v, *t)) {
				*t = v;
				s->changed = true;
			}
		}
	}
}

static void
funcsccp(struct func *f)
{
	struct sccp s = {0};
	struct block *b;
	struct inst **ip, **end;
	struct scval *cur;
	struct value *v;
	unsigned i, j, rounds;
	bool ok = true;

	if (!prune || !volatilecalls || asanon || f->ehobjs.len)
		return;
	s.ntmp = f->lastid + 1;
	for (b = f->start; b; b = b->next)
		b->idx = s.nblk++;
	s.blk = xreallocarray(NULL, s.nblk, sizeof(*s.blk));
	for (b = f->start; b; b = b->next)
		s.blk[b->idx] = b;
	s.slot = xreallocarray(NULL, s.ntmp, sizeof(*s.slot));
	for (i = 0; i < s.ntmp; ++i)
		s.slot[i] = -1;
	/* the slots: the allocations, then those whose address is used other than as a load's or store's address go */
	for (b = f->start; b; b = b->next) {
		end = (struct inst **)((char *)b->insts.val + b->insts.len);
		for (ip = b->insts.val; ip != end; ++ip) {
			if ((*ip)->kind >= IALLOC4 && (*ip)->kind <= IALLOC16 && (*ip)->res.kind == VALUE_TEMP && (*ip)->res.id < s.ntmp)
				s.slot[(*ip)->res.id] = 0;
			if ((*ip)->kind == ICALL && (v = (*ip)->arg[0]) && (v->kind & 0xf) == VALUE_GLOBAL && v->u.name &&
			    asansetjmpname(v->u.name))
				ok = false;
		}
	}
	for (b = f->start; b; b = b->next) {
		end = (struct inst **)((char *)b->insts.val + b->insts.len);
		for (ip = b->insts.val; ip != end; ++ip)
			for (j = 0; j < 3; ++j) {
				int kind = (*ip)->kind;

				v = (*ip)->arg[j];
				if (!v || v->kind != VALUE_TEMP || v->id >= s.ntmp || s.slot[v->id] < 0)
					continue;
				if ((j == 0 && kind >= ILOADD && kind <= ILOADUB) || (j == 1 && kind >= ISTORED && kind <= ISTOREB))
					continue;
				s.slot[v->id] = -2;
			}
		for (j = 0; j < 2; ++j)
			if ((v = b->phi.val[j]) && b->phi.res.kind && v->kind == VALUE_TEMP && v->id < s.ntmp && s.slot[v->id] >= 0)
				s.slot[v->id] = -2;
		if ((b->jump.kind == JUMP_JNZ || b->jump.kind == JUMP_RET) && (v = b->jump.arg) && v->kind == VALUE_TEMP &&
		    v->id < s.ntmp && s.slot[v->id] >= 0)
			s.slot[v->id] = -2;
	}
	for (i = 0; i < s.ntmp; ++i)
		s.slot[i] = s.slot[i] == 0 ? (int)s.nslot++ : -1;
	if (!ok || (size_t)s.nblk * (s.nslot + 1) > 1u << 22)
		goto out;
	s.tmp = xreallocarray(NULL, s.ntmp, sizeof(*s.tmp));
	for (i = 0; i < s.ntmp; ++i)
		s.tmp[i] = (struct scval){SCTOP};
	for (i = 0; i < f->type->u.func.nparam; ++i)
		if (f->paramtemps[i].kind == VALUE_TEMP && f->paramtemps[i].id < s.ntmp)
			s.tmp[f->paramtemps[i].id] = scbot;
	s.in = xreallocarray(NULL, (size_t)s.nblk * s.nslot + 1, sizeof(*s.in));
	s.exec = xmalloc(s.nblk);
	memset(s.exec, 0, s.nblk);
	s.edge = xreallocarray(NULL, s.nblk, sizeof(*s.edge));
	memset(s.edge, 0, s.nblk * sizeof(*s.edge));
	cur = xreallocarray(NULL, s.nslot + 1, sizeof(*cur));
	s.exec[0] = true;
	for (i = 0; i < s.nslot; ++i)
		s.in[i] = scbot;   /* nothing is known of a slot where the function begins */
	rounds = 0;
	do {
		s.changed = false;
		for (b = f->start; b; b = b->next) {
			if (!s.exec[b->idx])
				continue;
			memcpy(cur, s.in + (size_t)b->idx * s.nslot, s.nslot * sizeof(*cur));
			scblock(&s, b, cur);
		}
	} while (s.changed && ++rounds < 1000);
	if (s.changed)
		ok = false;
	/* a condition still undetermined where it can be reached: something here is not followed, change nothing */
	for (b = f->start; b && ok; b = b->next)
		if (s.exec[b->idx] && b->jump.kind == JUMP_JNZ && scvalue(&s, b->jump.arg).kind == SCTOP)
			ok = false;
	for (b = f->start; b && ok; b = b->next) {
		struct scval c;
		struct block *taken, *other;

		if (!s.exec[b->idx] || b->jump.kind != JUMP_JNZ || (c = scvalue(&s, b->jump.arg)).kind != SCCON)
			continue;
		taken = b->jump.blk[c.c ? 0 : 1];
		other = b->jump.blk[c.c ? 1 : 0];
		if (other != taken && other->phi.res.kind)
			for (j = 0; j < 2; ++j)
				if (other->phi.blk[j] == b)
					other->phi.blk[j] = NULL;   /* no longer a predecessor (emitfunc writes the others) */
		b->jump.kind = JUMP_JMP;
		b->jump.blk[0] = taken;
		b->jump.blk[1] = NULL;
		b->jump.arg = NULL;
	}
	/* a direct call of a static function with constant arguments may go to a clone of it (decl.c funcvalueclone) */
	for (b = f->start; b && ok; b = b->next) {
		if (!s.exec[b->idx])
			continue;
		end = (struct inst **)((char *)b->insts.val + b->insts.len);
		for (ip = b->insts.val; ip != end; ++ip) {
			struct inst **jp;
			struct decl *d, *c;
			bool isconst[16] = {0};
			unsigned long long val[16];
			unsigned n = 0, nconst = 0;

			if ((*ip)->kind != ICALL || !(v = (*ip)->arg[0]) || (v->kind & 0xf) != VALUE_GLOBAL || !(d = v->decl) ||
			    d->kind != DECLFUNC || d->linkage != LINKINTERN || !d->u.func.body)
				continue;
			for (jp = ip + 1; jp != end && (*jp)->kind == IARG && n < 16; ++jp, ++n) {
				struct scval a = scvalue(&s, (*jp)->arg[0]);

				if (a.kind == SCCON) {
					isconst[n] = true;
					val[n] = a.c;
					++nconst;
				}
			}
			if (!nconst || (jp != end && ((*jp)->kind == IARG || (*jp)->kind == IVARARG)))
				continue;
			if ((c = funcvalueclone(d, n, isconst, val, f->decl->section)))
				(*ip)->arg[0] = c->value;
		}
	}
	free(cur);
out:
	free(s.tmp);
	free(s.slot);
	free(s.blk);
	free(s.in);
	free(s.exec);
	free(s.edge);
}

/* a global name the function references: a declaration at file scope (not a string, a block-scope static, cproc's own
 * helpers or thunks, whose names differ from one compile of a body to the next) */
static void
funcref(struct array *out, struct value *v)
{
	char name[256], **n, *c;

	if (!v || (v->kind & 0xf) != VALUE_GLOBAL || !v->decl || v->decl->linkage == LINKNONE)
		return;
	valuename(v, name, sizeof name);
	arrayforeach(out, n)
		if (strcmp(*n, name) == 0)
			return;
	c = xmalloc(strlen(name) + 1);
	strcpy(c, name);
	arrayaddptr(out, c);
}

/* the global names that the blocks reachable from the start reference, each once */
static void
funcrefs(struct func *f, struct array *out)
{
	struct array stack = {0};
	struct block *b, *t;
	struct inst **ip, **end;
	struct value **r;
	bool *seen;
	unsigned n = 0, i, j;

	for (b = f->start; b; b = b->next)
		b->idx = n++;
	seen = xmalloc(n);
	memset(seen, 0, n);
	seen[0] = true;
	arrayaddptr(&stack, f->start);
	while (stack.len) {
		stack.len -= sizeof(b);
		b = *(struct block **)((char *)stack.val + stack.len);
		for (i = 0; i < 2; ++i)
			if ((t = scsucc(b, i)) && !seen[t->idx]) {
				seen[t->idx] = true;
				arrayaddptr(&stack, t);
			}
	}
	free(stack.val);
	for (b = f->start; b; b = b->next) {
		if (!seen[b->idx])
			continue;
		end = (struct inst **)((char *)b->insts.val + b->insts.len);
		for (ip = b->insts.val; ip != end; ++ip)
			for (j = 0; j < 3; ++j)
				funcref(out, (*ip)->arg[j]);
		if (b->phi.res.kind)
			for (i = 0; i < 2; ++i)
				if (b->phi.blk[i])
					funcref(out, b->phi.val[i]);
		if (b->jump.kind == JUMP_JNZ || b->jump.kind == JUMP_RET)
			funcref(out, b->jump.arg);
		arrayforeach(&b->asmrefs, r)
			funcref(out, *r);
	}
	free(seen);
}

/* decl.c funcvalueclone: whether the clone f of orig references less than orig (a name orig's code reached, gone) */
bool
funcclonegain(struct func *f, struct decl *orig)
{
	struct array refs = {0};
	char **o, **r, self[256];
	bool gain = false, found;

	funcsccp(f);
	funcrefs(f, &refs);
	valuename(orig->value, self, sizeof self);
	arrayforeach(&orig->u.func.refs, o) {
		if (strcmp(*o, self) == 0)   /* a recursive call: the clone's goes to the clone */
			continue;
		found = false;
		arrayforeach(&refs, r)
			if (strcmp(*o, *r) == 0) {
				found = true;
				break;
			}
		if (!found) {
			gain = true;
			break;
		}
	}
	arrayforeach(&refs, r)
		free(*r);
	free(refs.val);
	return gain;
}

void
emitfunc(struct func *f, bool global)
{
	struct block *b;
	struct inst **inst, **instend;
	struct decl *p;
	struct value *v;

	/* dbgfile is top-level: it names the file of the .loc lines (dbgloc) of this function */
	if (f->asanfile)
		printf("dbgfile \"%s\"\n", f->asanfile);
	/* -fsanitize=address, use after return: the descriptions of the fake frames (asanalloc), read by libasan's report */
	if (asanon) {
		struct asanobj *o;
		size_t i, n = f->asan.len / sizeof(*o);

		for (i = 0; i < n; i++) {
			o = (struct asanobj *)f->asan.val + i;
			if (o->desc)
				printf("data $%s = { b \"%s\", b 0 }\n", o->desclabel, o->desc);
		}
	}

	if (asanon)
		asanfinish(f);
	if (f->end->jump.kind == JUMP_NONE) {
		v = NULL;
		/* implicitly return 0 from main if we reach the end of the function */
		if (strcmp(f->name, "main") == 0 && f->type->base == &typeint)
			v = mkintconst(0);
		funcret(f, v);
	}
	if (asanon)
		asanfree(f);
	if (asanon && f->asanlo)
		asandynret(f);
	funcsccp(f);
	/* what a function with a recorded body references, for its clones (funcclonegain) */
	if (prune && f->decl->u.func.body && !f->decl->u.func.refs.len)
		funcrefs(f, &f->decl->u.func.refs);
	/* GNU used and section (cproc -p keeps a "# nfcxx:keep" item even when nothing references it; a section alone
	 * does not keep it) */
	if (f->decl->used && prune)
		puts("# nfcxx:keep");
	if (f->decl->section)
		printf("section \"%s\" \"ax\"\n", f->decl->section);
	if (global)
		puts("export");
	fputs("function ", stdout);
	if (f->type->base != &typevoid && f->type->base->kind != TYPELDOUBLE) {
		emitclass(abiclass(f->type->base), f->type->base->value);
		putchar(' ');
	}
	emitname(f->decl->value);
	putchar('(');
	for (p = f->type->u.func.params, v = f->paramtemps; p; p = p->next, ++v) {
		if (p != f->type->u.func.params)
			fputs(", ", stdout);
		emitclass(abiclass(abiparam(p->type)), abiparam(p->type)->value);
		putchar(' ');
		emitname(v);
	}
	if (f->type->u.func.isvararg) {
		if (f->type->u.func.params)
			fputs(", ", stdout);
		fputs("...", stdout);
	}
	puts(") {");
	funcasmout(f);
	for (b = f->start; b; b = b->next) {
		emitname(&b->label);
		putchar('\n');
		/* cproc -p: what only an unreachable block names is not referenced (main.c ilref) */
		if (prune && !b->reach)
			puts("# nfcxx:dead");
		if (b->phi.res.kind) {
			int i, n = 0;

			putchar('\t');
			emitvalue(&b->phi.res);
			/* funcsccp drops the entry of a way it found is not taken; with none left the block cannot be reached */
			if (!b->phi.blk[0] && !b->phi.blk[1]) {
				printf(" =%c copy 0\n", b->phi.class);
			} else {
				printf(" =%c phi ", b->phi.class);
				for (i = 0; i < 2; ++i) {
					if (!b->phi.blk[i])
						continue;
					if (n++)
						fputs(", ", stdout);
					emitname(&b->phi.blk[i]->label);
					putchar(' ');
					emitvalue(b->phi.val[i]);
				}
				putchar('\n');
			}
		}
		instend = (struct inst **)((char *)b->insts.val + b->insts.len);
		for (inst = b->insts.val; inst != instend;)
			inst = emitinst(inst, instend);
		emitjump(&b->jump);
	}
	if (f->ehobjs.len) {
		/* the landing pad: the cleanups of the objects (the last declared first), then the unwind resumes with the
		 * exception the system unwinder holds */
		struct ehobj *o;
		size_t i = f->ehobjs.len / sizeof(*o);

		puts("@eh.lp");
		while (i-- > 0) {
			o = (struct ehobj *)f->ehobjs.val + i;
			fputs("\tcall $", stdout);
			fputs(o->cleanup, stdout);
			fputs("(l ", stdout);
			emitvalue(o->addr);
			puts(")");
		}
		puts("\t%.ehe =l call $__nfcxx_eh_unwind_exc()");
		puts("\tcall $_Unwind_Resume(l %.ehe)");
		puts("\thlt");
	}
	puts("}");
}

static void
dataitem(struct expr *expr, unsigned long long size)
{
	struct decl *decl;
	size_t i, w;
	unsigned c;

	switch (expr->kind) {
	case EXPRUNARY:
		if (expr->op != TBAND)
			fatal("not a address expr");
		expr = expr->base;
		if (expr->kind != EXPRIDENT)
			error(&tok.loc, "initializer is not a constant expression");
		decl = expr->u.ident.decl;
		if (decl->kind == DECLOBJECT && decl->u.obj.storage != SDSTATIC)
			error(&tok.loc, "initializer is not a constant expression");
		emitname(decl->value);
		break;
	case EXPRBINARY:
		if (expr->op != TADD || expr->u.binary.l->kind != EXPRUNARY || expr->u.binary.r->kind != EXPRCONST)
			error(&tok.loc, "initializer is not a constant expression");
		dataitem(expr->u.binary.l, 0);
		fputs(" + ", stdout);
		dataitem(expr->u.binary.r, 0);
		break;
	case EXPRCONST:
		if (expr->type->kind == TYPEFLOAT16)
			printf("%u", halfbits(expr->u.constant.f));
		else if (expr->type->prop & PROPFLOAT)
			printf("%c_%.17g", expr->type->size == 4 ? 's' : 'd', expr->u.constant.f);
		else
			printf("%llu", expr->u.constant.u);
		break;
	case EXPRSTRING:
		w = expr->type->base->size;
		if (w == 1) {
			fputc('"', stdout);
			for (i = 0; i < expr->u.string.size && i < size; ++i) {
				c = ((unsigned char *)expr->u.string.data)[i];
				if (isprint(c) && c != '"' && c != '\\')
					putchar(c);
				else
					printf("\\%03o", c);
			}
			fputc('"', stdout);
		} else {
			for (i = 0; i < expr->u.string.size && i * w < size; ++i) {
				switch (w) {
				case 2: printf("%" PRIuLEAST16 " ", ((uint_least16_t *)expr->u.string.data)[i]); break;
				case 4: printf("%" PRIuLEAST32 " ", ((uint_least32_t *)expr->u.string.data)[i]); break;
				default: assert(0);
				}
			}
		}
		if (i * w < size)
			printf(", z %llu", size - (unsigned long long)i * w);
		break;
	default:
		error(&tok.loc, "initializer is not a constant expression");
	}
}

/*
-fsanitize=address: a global of the unit is followed, in its own data item, by the rest of its 8-byte granule and ASANRZ zero
bytes (emitdata). The unit's constructor (emitasanctor, in .init_array) poisons that tail, so an access past the object
reports. A symbol is only the object's address, so the redzone has to be inside the item.
*/
struct asanglobal {
	struct value *v;
	unsigned long long granule;   /* the object's size rounded up to 8: the start of its redzone */
};
static struct array asanglobals;

void
emitdata(struct decl *d, struct init *init, struct func *owner)
{
	struct init *cur;
	struct type *t;
	unsigned long long offset = 0, start, end, bits = 0, size, pad = 0;
	struct asanglobal *g;
	size_t i;
	int align;

	align = d->u.obj.align;
	size = d->type->size + d->u.obj.famsize;
	for (cur = init; cur; cur = cur->next)
		cur->expr = eval(cur->expr);
	/* GNU section: read-only ("a") when the object is const, as gcc chooses; used keeps it under cproc -p (a section
	 * alone does not: gcc drops an unreferenced static object in .init.data too). A used static in a function (owner)
	 * lives with that function: gcc emits nothing of an inline function it drops (the kernel's static_call_cond has an
	 * __ADDRESSABLE(key) in kvm_host.h's unused helpers, and the key is not defined) */
	if (d->used && prune && owner) {
		fputs("# nfcxx:keepwith ", stdout);
		emitbarename(owner->decl->value);
		putchar('\n');
	} else if (d->used && prune) {
		puts("# nfcxx:keep");
	}
	if (d->section) {
		struct type *et = d->type;
		bool ro = d->qual & QUALCONST;

		for (; et->kind == TYPEARRAY; et = et->base)
			ro |= et->qual & QUALCONST;
		printf("section \"%s\" \"%s\"\n", d->section, ro ? "a" : "aw");
	}
	if (d->u.obj.storage == SDTHREAD)
		fputs("thread ", stdout);
	if (d->linkage == LINKEXTERN)
		fputs("export ", stdout);
	fputs("data ", stdout);
	emitname(d->value);
	printf(" = align %d { ", align);

	while (init) {
		cur = init;
		while ((init = init->next) && init->start * 8 + init->bits.before < cur->end * 8 - cur->bits.after) {
			/*
			XXX: Currently, if multiple union members are
			initialized, these assertions may not hold.
			(https://todo.sr.ht/~mcf/cproc/38)
			*/
			assert(cur->expr->kind == EXPRSTRING);
			assert(init->expr->kind == EXPRCONST);
			i = (init->start - cur->start) / cur->expr->type->base->size;
			switch (cur->expr->type->base->size) {
			case 1: ((unsigned char *)cur->expr->u.string.data)[i]  = init->expr->u.constant.u; break;
			case 2: ((uint_least16_t *)cur->expr->u.string.data)[i] = init->expr->u.constant.u; break;
			case 4: ((uint_least32_t *)cur->expr->u.string.data)[i] = init->expr->u.constant.u; break;
			}
		}
		start = cur->start + cur->bits.before / 8;
		end = cur->end - (cur->bits.after + 7) / 8;
		if (offset < start && bits) {
			printf("b %u, ", (unsigned)bits);  /* unfinished byte from previous bit-field */
			++offset;
			bits = 0;
		}
		if (offset < start)
			printf("z %llu, ", start - offset);
		if (cur->bits.before || cur->bits.after) {
			/* little-endian target specific */
			assert(cur->expr->type->prop & PROPINT);
			assert(cur->expr->kind == EXPRCONST);
			bits |= cur->expr->u.constant.u << cur->bits.before % 8;
			for (offset = start; offset < end; ++offset, bits >>= 8)
				printf("b %u, ", (unsigned)bits & 0xff);
			/*
			clear the upper `after` bits in the last byte,
			or all bits when `after` is 0 (we ended on a
			byte boundary).
			*/
			bits &= 0x7f >> (cur->bits.after + 7) % 8;
		} else {
			t = cur->expr->type;
			if (t->kind == TYPEARRAY)
				t = t->base;
			if (t->prop & PROPSOFT) {
				if (targ->ilp32 && softvalue(t))
					error(&tok.loc, "a %s initializer is not supported on %s", t->kind == TYPELDOUBLE ? "long double" : "__float128", targ->name);
				if (cur->expr->kind != EXPRCONST)
					error(&tok.loc, "initializer is not a constant expression");
				printf("l %llu, l %llu, ", cur->expr->u.constant.soft[0], cur->expr->u.constant.soft[1]);
				offset = end;
				continue;
			}
			printf("%c ", qbetype(t).data);
			dataitem(cur->expr, cur->end - cur->start);
			fputs(", ", stdout);
		}
		offset = end;
	}
	if (bits) {
		printf("b %u, ", (unsigned)bits);
		++offset;
	}
	assert(offset <= size);
	if (asanon && size && d->u.obj.storage != SDTHREAD) {
		pad = ((size + 7) & ~7ULL) - size + ASANRZ;
		g = arrayadd(&asanglobals, sizeof(*g));
		g->v = d->value;
		g->granule = (size + 7) & ~7ULL;
	}
	if (offset < size || pad)
		printf("z %llu ", size - offset + pad);
	puts("}");
}

/* the constructor of the unit: poisons the redzone of each global emitdata wrote (see asanglobal), then the .init_array entry */
void
emitasanctor(void)
{
	struct asanglobal *g;
	size_t i, n = asanglobals.len / sizeof(*g);

	if (n == 0)
		return;
	puts("function $__nfcxx_asan_globals() {");
	puts("@start");
	for (i = 0; i < n; i++) {
		g = (struct asanglobal *)asanglobals.val + i;
		printf("\t%%g%zu =l add ", i);
		emitname(g->v);
		printf(", %llu\n", g->granule);
		printf("\tcall $__asan_poison_memory_region(l %%g%zu, l %d)\n", i, ASANRZ);
	}
	puts("\tret");
	puts("}");
	puts("section \".init_array\" \"aw\"");
	puts("data $__nfcxx_asan_ctor = align 8 { l $__nfcxx_asan_globals }");
}
