#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
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
	struct value res, *arg[2];
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

	struct block *next;
};

struct switchcase {
	struct treenode node;
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
};

/* a call of setjmp (asansetjmp): the block that poisons the objects out of scope at the call (pad, see asanfinish) and the
 * block after it. Both returns of the call pass through pad; open is the set of blocks open at the call. */
struct asanjmp {
	struct block *pad, *next;
	struct array *open;
};

static const int ptrclass = 'l';

void
switchcase(struct switchcases *cases, unsigned long long i, struct block *b)
{
	struct switchcase *c;

	c = treeinsert(&cases->root, i, sizeof(*c));
	if (!c->node.new)
		error(&tok.loc, "multiple 'case' labels with same value");
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
		s = {'s', 's', ILOADS, ISTORES},
		d = {'d', 'd', ILOADD, ISTORED},
		v = {0};

	if (t == &typevoid)
		return v;
	if (!(t->prop & PROPSCALAR) || t->prop & PROPSOFT)
		return l;
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

/* a call of the runtime function name with one or two pointer-sized arguments (b may be NULL) */
static void
asancall(struct func *f, const char *name, struct value *a, struct value *b)
{
	struct value *fn;
	char *s;

	s = xmalloc(strlen(name) + 1);
	strcpy(s, name);
	fn = xmalloc(sizeof(*fn));
	fn->kind = VALUE_GLOBAL;
	fn->u.name = s;
	fn->id = 0;
	funcinst(f, ICALL, 0, fn, NULL);
	funcinst(f, IARG, ptrclass, a, NULL);
	if (b)
		funcinst(f, IARG, ptrclass, b, NULL);
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
		t->u.array.size = funcinst(f, IMUL, 'l', length, basesize);
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

static void
asanalloc(struct func *f, struct decl *d)
{
	struct block *end = f->end;
	unsigned long long size8 = (d->type->size + 7) & ~7ULL, align = d->u.obj.align, total = size8 + 2 * ASANRZ;
	struct value *base, *obj, *right, *left, *rlen;
	struct asanobj *o;

	f->end = f->start;
	if (align <= 16) {
		base = funcinst(f, IALLOC16, ptrclass, mkintconst(total), NULL);
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
	f->end = end;
	/* the poison is at the declaration, not in the entry block: a return that comes before this declaration never poisons it */
	asancall(f, "__asan_unpoison_memory_region", base, mkintconst(total));
	asancall(f, "__asan_poison_memory_region", base, left);
	asancall(f, "__asan_poison_memory_region", right, rlen);
	o = arrayadd(&f->asan, sizeof(*o));
	o->base = base;
	o->size = total;
	o->obj = obj;
	o->obj8 = size8;
	o->block = asantop(f);
	o->objslot = o->sizeslot = NULL;
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

static void
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
	class = 'w';
	switch (align) {
	case 1: load = ILOADUB, store = ISTOREB; break;
	case 2: load = ILOADUH, store = ISTOREH; break;
	case 4: load = ILOADW, store = ISTOREW; break;
	default: load = ILOADL, store = ISTOREL, align = 8, class = 'l'; break;
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

static struct value *
funcstore(struct func *f, struct type *t, enum typequal tq, struct lvalue lval, struct value *v)
{
	struct value *r;
	enum typeprop tp;
	unsigned long long mask;
	struct qbetype qt;
	int bits;

	if (tq & QUALVOLATILE)
		error(&tok.loc, "volatile store is not yet supported");
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
	f->asan = (struct array){0};
	f->asanfile = NULL;
	f->asanrets = (struct array){0};
	f->asanlo = f->asanhi = NULL;
	f->asanopen = (struct array){0};
	f->asanblocks = 0;
	f->asanjmps = (struct array){0};
	mapinit(&f->gotos, 8);
	emittype(t->base);

	/* allocate space for parameters */
	f->paramtemps = xreallocarray(NULL, t->u.func.nparam, sizeof *f->paramtemps);
	for (d = t->u.func.params, v = f->paramtemps; d; d = d->next, ++v) {
		emittype(d->type);
		functemp(f, v);
		if(!d->name)
			continue;
		if (d->type->value) {
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
		f->gotos.vals[idx].p = g;
	}

	return f->gotos.vals[idx].p;
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
	switch (e->kind) {
	case EXPRIDENT:
		d = e->u.ident.decl;
		switch (d->kind) {
		case DECLOBJECT: return funcload(f, e->type, (struct lvalue){d->value});
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
		return funcload(f, e->type, lval);
	case EXPRINCDEC:
		lval = funclval(f, e->base);
		l = funcload(f, e->base->type, lval);
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
			if (t->base->kind == TYPEARRAY && t->base->size == 0) {
				r = t->base->u.array.size;
			} else {
				r = mkintconst(t->base->size);
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
			v = funcinst(f, ICALL, abiclass(t), funcexpr(f, e->base), t->value);
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
			return funcload(f, e->type, (struct lvalue){r});
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
		case BUILTINVASTART:
			l = funcexpr(f, e->base);
			funcinst(f, IVASTART, 0, l, NULL);
			break;
		case BUILTINVAARG:
			if (e->toeval)
				funcexpr(f, e->toeval);
			/* https://todo.sr.ht/~mcf/cproc/52 */
			if (!(e->type->prop & PROPSCALAR) || e->type->prop & PROPSOFT)
				return funcvaargagg(f, e);
			l = funcexpr(f, e->base);
			return funcinst(f, IVAARG, qbetype(e->type).base, l, NULL);
		case BUILTINALLOCA:
			l = funcexpr(f, e->base);
			if (asanon)
				return asandynalloc(f, l, false);
			return funcinst(f, IALLOC16, ptrclass, l, NULL);
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

void
funcinit(struct func *func, struct decl *d, struct init *init, bool hasinit)
{
	struct lvalue dst;
	struct value *src, *v;
	unsigned long long offset = 0, max = 0;
	size_t i, w;

	funcalloc(func, d);
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
	if (min == max) {
		funcjmp(f, c->body);
		return;
	}
	label[0] = mkblock("switch_ne");
	label[1] = mkblock("switch_lt");
	label[2] = mkblock("switch_gt");

	key = mkintconst(c->node.key);
	res = funcinst(f, class == 'w' ? ICEQW : ICEQL, 'w', v, key);
	funcjnz(f, res, NULL, c->body, label[0]);
	funclabel(f, label[0]);
	res = funcinst(f, class == 'w' ? ICULTW : ICULTL, 'w', v, key);
	funcjnz(f, res, NULL, label[1], label[2]);
	funclabel(f, label[1]);
	casesearch(f, class, v, c->node.child[0], defaultlabel, min, c->node.key - 1);
	funclabel(f, label[2]);
	casesearch(f, class, v, c->node.child[1], defaultlabel, c->node.key + 1, max);
}

void
funcswitch(struct func *f, struct value *v, struct switchcases *c, struct block *defaultlabel)
{
	casesearch(f, qbetype(c->type).base, v, c->root, defaultlabel, 0, -1);
}

/* emit */

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
	if (kind == VALUE_GLOBAL && v->id)
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
	unsigned long long off;

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
	fputs(" = { ", stdout);
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
		emitclass(qbetype(sub).data, sub->value);
		if (m->type->size > sub->size)
			printf(" %llu", m->type->size / sub->size);
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
				fputs(", ...", stdout);
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

	if (asanon)
		asanfinish(f);
	if (f->end->jump.kind == JUMP_NONE) {
		v = NULL;
		/* implicitly return 0 from main if we reach the end of the function */
		if (strcmp(f->name, "main") == 0 && f->type->base == &typeint)
			v = mkintconst(0);
		funcret(f, v);
	}
	if (asanon && f->asanlo)
		asandynret(f);
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
		emitclass(abiclass(p->type), p->type->value);
		putchar(' ');
		emitname(v);
	}
	if (f->type->u.func.isvararg) {
		if (f->type->u.func.params)
			fputs(", ", stdout);
		fputs("...", stdout);
	}
	puts(") {");
	for (b = f->start; b; b = b->next) {
		emitname(&b->label);
		putchar('\n');
		if (b->phi.res.kind) {
			putchar('\t');
			emitvalue(&b->phi.res);
			printf(" =%c phi ", b->phi.class);
			emitname(&b->phi.blk[0]->label);
			putchar(' ');
			emitvalue(b->phi.val[0]);
			fputs(", ", stdout);
			emitname(&b->phi.blk[1]->label);
			putchar(' ');
			emitvalue(b->phi.val[1]);
			putchar('\n');
		}
		instend = (struct inst **)((char *)b->insts.val + b->insts.len);
		for (inst = b->insts.val; inst != instend;)
			inst = emitinst(inst, instend);
		emitjump(&b->jump);
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
emitdata(struct decl *d, struct init *init)
{
	struct init *cur;
	struct type *t;
	unsigned long long offset = 0, start, end, bits = 0, size, pad = 0;
	struct asanglobal *g;
	size_t i;
	int align;

	align = d->u.obj.align;
	size = d->type->size;
	for (cur = init; cur; cur = cur->next)
		cur->expr = eval(cur->expr);
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
	assert(offset <= d->type->size);
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
