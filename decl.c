#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

static struct decl *tentativedefns, **tentativedefnsend = &tentativedefns;

struct qualtype {
	struct type *type;
	enum typequal qual;
	struct expr *expr;
};

enum storageclass {
	SCNONE,

	SCTYPEDEF     = 1<<1,
	SCEXTERN      = 1<<2,
	SCSTATIC      = 1<<3,
	SCAUTO        = 1<<4,
	SCREGISTER    = 1<<5,
	SCTHREADLOCAL = 1<<6,
};

enum typespec {
	SPECNONE,

	SPECVOID     = 1<<1,
	SPECCHAR     = 1<<2,
	SPECBOOL     = 1<<3,
	SPECINT      = 1<<4,
	SPECFLOAT    = 1<<5,
	SPECDOUBLE   = 1<<6,
	SPECSHORT    = 1<<7,
	SPECLONG     = 1<<8,
	SPECLONG2    = 1<<9,
	SPECSIGNED   = 1<<10,
	SPECUNSIGNED = 1<<11,
	SPECCOMPLEX  = 1<<12,
	SPECBITINT   = 1<<13,
	SPECFLOAT128 = 1<<14,
	SPECFLOAT16  = 1<<15,
	SPECINT128   = 1<<16,

	SPECLONGLONG = SPECLONG|SPECLONG2,
};

enum funcspec {
	FUNCNONE,

	FUNCINLINE   = 1<<1,
	FUNCNORETURN = 1<<2,
};

struct structbuilder {
	struct type *type;
	struct member **last;
	unsigned bits;  /* number of bits remaining in the last byte */
	bool pack;
	bool hasbits;   /* a bit-field was added (a trailing packed attribute cannot re-lay those out) */
	/* where gcc's packed layout would put the next member, in bits, and whether some member so far is elsewhere in the
	 * natural layout: a trailing packed attribute is taken with bit-fields only when packing moves nothing */
	unsigned long long packbits;
	bool packmoves;
	bool fam;   /* a flexible array member was added: no member may follow it */
	int pragmapack;   /* #pragma pack(N) when the struct was defined: the most alignment of a member (0: none) */
};

struct func *curfunc;
static bool curclone;   /* a clone's body is being parsed (funcclone): nothing is recorded */
static bool alignasseen;   /* the declaration being parsed has an _Alignas (not only GNU aligned) */

/* GNU mode on a declaration of an integer type (glibc's typedef int register_t __attribute__((__mode__(__word__)))):
 * the integer type of that size, of the same signedness, as gcc gives it */
static struct type *
modetype(struct type *t, int size)
{
	static struct type *const bysize[9][2] = {
		[1] = {&typeuchar, &typeschar}, [2] = {&typeushort, &typeshort},
		[4] = {&typeuint, &typeint}, [8] = {&typeulong, &typelong},
	};

	if (!(t->prop & PROPINT) || t->kind == TYPEBOOL)
		error(&tok.loc, "GNU attribute mode on a type that is not an integer is not supported");
	return bysize[size][t->u.arith.issigned];
}

static void structpackbits(struct type *, struct structbuilder *);

/* GNU packed on a member declarator (declaratortypes): structdecl lays that member out with alignment 1 */
static bool declpacked;
static void structpack(struct type *);

struct decl *
mkdecl(char *name, enum declkind k, struct type *t, enum typequal tq, enum linkage linkage)
{
	struct decl *d;

	d = xmalloc(sizeof(*d));
	memset(d, 0, sizeof(*d));
	d->name = name;
	d->loc = tok.loc;
	d->kind = k;
	d->linkage = linkage;
	d->type = t;
	d->qual = tq;
	if (k == DECLOBJECT && t)
		d->u.obj.align = t->align;

	return d;
}

/* 6.7.1 Storage-class specifiers */
static int
storageclass(enum storageclass *sc)
{
	enum storageclass allowed, new;

	switch (tok.kind) {
	case TTYPEDEF:       new = SCTYPEDEF;     break;
	case TEXTERN:        new = SCEXTERN;      break;
	case TSTATIC:        new = SCSTATIC;      break;
	case TTHREAD_LOCAL:  new = SCTHREADLOCAL; break;
	case TAUTO:          new = SCAUTO;        break;
	case TREGISTER:      new = SCREGISTER;    break;
	default: return 0;
	}
	if (!sc)
		error(&tok.loc, "storage class not allowed in this declaration");
	switch (*sc) {
	case SCNONE:        allowed = ~SCNONE;           break;
	case SCTHREADLOCAL: allowed = SCSTATIC|SCEXTERN; break;
	case SCSTATIC:
	case SCEXTERN:      allowed = SCTHREADLOCAL;     break;
	default:            allowed = SCNONE;            break;
	}
	if (new & ~allowed)
		error(&tok.loc, "invalid combination of storage class specifiers");
	*sc |= new;
	next();

	return 1;
}

/* 6.7.3 Type qualifiers */
static int
typequal(enum typequal *tq)
{
	switch (tok.kind) {
	case TCONST:    *tq |= QUALCONST;    break;
	case TVOLATILE: *tq |= QUALVOLATILE; break;
	case TRESTRICT: *tq |= QUALRESTRICT; break;
	case T_ATOMIC: error(&tok.loc, "_Atomic type qualifier is not yet supported");
	default: return 0;
	}
	next();

	return 1;
}

/* 6.7.4 Function specifiers */
static int
funcspec(enum funcspec *fs)
{
	enum funcspec new;

	switch (tok.kind) {
	case TINLINE:    new = FUNCINLINE;   break;
	case T_NORETURN: new = FUNCNORETURN; break;
	default: return 0;
	}
	if (!fs)
		error(&tok.loc, "function specifier not allowed in this declaration");
	*fs |= new;
	next();

	return 1;
}

static void structdecl(struct scope *, struct structbuilder *);
static struct qualtype declspecs(struct scope *, enum storageclass *, enum funcspec *, int *);

static struct type *
tagspec(struct scope *s)
{
	static struct type *const inttypes[][2] = {
		{&typeuint, &typeint},
		{&typeulong, &typelong},
		{&typeullong, &typellong},
	};
	struct type *t, *et;
	char *tag, *name;
	enum typekind kind;
	struct decl *d, *enumconsts;
	struct expr *e;
	struct attr a;
	enum attrkind allowedattr;
	struct structbuilder b;
	bool leadpack;
	unsigned long long value, max, min;
	bool sign;
	int i;

	allowedattr = 0;
	switch (tok.kind) {
	case TSTRUCT: kind = TYPESTRUCT, allowedattr |= ATTRPACKED; break;
	case TUNION:  kind = TYPEUNION, allowedattr |= ATTRPACKED; break;
	case TENUM:   kind = TYPEENUM, allowedattr |= ATTRPACKED; break;
	default: fatal("internal error: unknown tag kind");
	}
	next();
	a.kind = 0;
	attr(&a, allowedattr);
	gnuattr(&a, allowedattr);
	tag = 0;
	t = NULL;
	et = NULL;
	if (iscident(tok.kind)) {
		tag = tokenstr(tok.kind);
		next();
	}
	if (kind == TYPEENUM && consume(TCOLON)) {
		et = declspecs(s, NULL, NULL, NULL).type;
		if (!et)
			error(&tok.loc, "no type in enum type specifier");
	}
	if (tag)
		t = scopegettag(s, tag, tok.kind != TLBRACE && tok.kind != TSEMICOLON);
	if (t) {
		if (t->kind != kind)
			error(&tok.loc, "redeclaration of tag '%s' with different kind", tag);
	} else {
		if (kind == TYPEENUM) {
			t = mktype(kind, PROPSCALAR|PROPARITH|PROPREAL|PROPINT);
			t->base = et;
		} else {
			t = mktype(kind, 0);
			t->size = 0;
			t->align = 0;
			t->u.structunion.tag = tag;
			t->u.structunion.members = NULL;
		}
		t->incomplete = true;
		if (tag)
			scopeputtag(s, tag, t);
	}
	if (tok.kind != TLBRACE)
		return t;
	if (!t->incomplete)
		error(&tok.loc, "redefinition of tag '%s'", tag);
	next();
	switch (t->kind) {
	case TYPESTRUCT:
	case TYPEUNION:
		b.type = t;
		b.last = &t->u.structunion.members;
		b.bits = 0;
		/* struct __attribute__((packed)) S { ... } is laid out as one with the attribute after its body: naturally
		 * first, then packed (structpack, structpackbits), so bit-fields are taken the same way */
		leadpack = a.kind & ATTRPACKED;
		b.pack = false;
		b.hasbits = false;
		b.packbits = 0;
		b.packmoves = false;
		b.fam = false;
		b.pragmapack = pragmapack;
		/* GNU extension, accepted by gcc in C: an empty body is size 0 with alignment 1.
		 * EDG emits `struct X {}` for empty C++ classes. */
		while (tok.kind != TRBRACE)
			structdecl(s, &b);
		if (!t->u.structunion.members)
			t->align = 1;
		next();
		/* a trailing GNU attribute after the body, struct S { ... } __attribute__((aligned(N))), raises the alignment */
		{
			struct attr trail;

			trail.kind = 0;
			trail.align = 0;
			trail.section = NULL;
			gnuattr(&trail, ATTRALIGNED | ATTRPACKED);
			if ((trail.kind & ATTRPACKED || leadpack) && !b.pack) {
				if (b.hasbits)
					structpackbits(t, &b);
				else
					structpack(t);
				b.pack = true;
			}
			if (trail.kind & ATTRALIGNED && trail.align > t->align)
				t->align = trail.align;
		}
		/* also when packed: the alignment is then 1, unless a member asked for more (gcc rounds the size up to it) */
		t->size = ALIGNUP(t->size, t->align);
		break;
	case TYPEENUM:
		enumconsts = NULL;
		if (et) {
			t->size = t->base->size;
			t->align = t->base->align;
			t->u.arith.issigned = t->base->u.arith.issigned;
			t->u.arith.width = t->base->u.arith.width;
			t->incomplete = false;
			et = t;
		} else {
			et = &typeint;
		}
		max = 0;
		min = 0;
		for (value = 0; iscident(tok.kind); ++value) {
			name = tokenstr(tok.kind);
			next();
			attr(NULL, 0);
			if (consume(TASSIGN)) {
				e = eval(condexpr(s));
				if (e->kind != EXPRCONST || !(e->type->prop & PROPINT))
					error(&tok.loc, "expected integer constant expression");
				value = e->u.constant.u;
				if (!t->base)
					et = typehasint(&typeint, value, e->type->u.arith.issigned) ? &typeint : e->type;
				else if (!typehasint(et, value, e->type->u.arith.issigned))
					goto invalid;
			} else if (value == 0 && !et->u.arith.issigned || value == 1ull << 63 && et->u.arith.issigned) {
				error(&tok.loc, "no %ssigned integer type can represent enumerator value", et->u.arith.issigned ? "" : "un");
			} else if (!typehasint(et, value, et->u.arith.issigned)) {
				if (t->base) {
				invalid:
					/* fixed underlying type */
					error(&tok.loc, "enumerator '%s' value cannot be represented in underlying type", name);
				}
				sign = et->u.arith.issigned;
				for (i = 0; i < countof(inttypes); ++i) {
					et = inttypes[i][sign];
					if (typehasint(et, value, sign))
						break;
				}
				assert(i < countof(inttypes));
			}
			d = mkdecl(name, DECLCONST, et, QUALNONE, LINKNONE);
			d->u.enumconst = value;
			d->value = mkintconst(value);
			d->next = enumconsts;
			enumconsts = d;
			if (et->u.arith.issigned && value >= 1ull << 63) {
				if (-value > min)
					min = -value;
			} else if (value > max) {
				max = value;
			}
			scopeputdecl(s, d);
			if (!consume(TCOMMA))
				break;
		}
		expect(TRBRACE, "to close enum specifier");
		{
			struct attr trail = {0};

			gnuattr(&trail, ATTRPACKED | ATTRMODE);
			a.kind |= trail.kind & ATTRPACKED;
			if (trail.kind & ATTRMODE) {
				/* GNU mode on an enum: the integer type of that size, unsigned when no value is negative, as gcc
				 * gives it (the kernel's trace enums: enum afs_call_trace { ... } __mode(byte)) */
				static struct type *const bysize[9][2] = {
					[1] = {&typeuchar, &typeschar}, [2] = {&typeushort, &typeshort},
					[4] = {&typeuint, &typeint}, [8] = {&typeulong, &typelong},
				};

				sign = min > 0;
				et = bysize[trail.modesize][sign];
				if (!typehasint(et, max, false) || sign && !typehasint(et, -min, true))
					error(&tok.loc, "an enumerator value does not fit the enum's mode");
				t->base = et;
				t->size = et->size;
				t->align = et->align;
				t->u.arith.issigned = et->u.arith.issigned;
				t->u.arith.width = et->u.arith.width;
			}
		}
		if (!t->base && a.kind & ATTRPACKED) {
			/* GNU packed enum: the smallest integer type that holds the values, unsigned when none is negative */
			static struct type *const small[][2] = {
				{&typeuchar, &typeschar}, {&typeushort, &typeshort}, {&typeuint, &typeint},
			};
			sign = min > 0;
			for (i = 0; i < countof(small); ++i) {
				if (typehasint(small[i][sign], max, false) && (!sign || typehasint(small[i][sign], -min, true)))
					break;
			}
			if (i < countof(small)) {
				t->base = small[i][sign];
				t->size = t->base->size;
				t->align = t->base->align;
				t->u.arith.issigned = t->base->u.arith.issigned;
				t->u.arith.width = t->base->u.arith.width;
			}
		}
		if (!t->base) {
			if (min <= 0x80000000 && max <= 0x7fffffff) {
				t->base = min ? &typeint : &typeuint;
			} else {
				sign = min > 0;
				for (i = 0; i < countof(inttypes); ++i) {
					et = inttypes[i][sign];
					if (typehasint(et, max, false) && typehasint(et, -min, true))
						break;
				}
				if (i == countof(inttypes))
					error(&tok.loc, "no integer type can represent all enumerator values");
				t->base = et;
				for (d = enumconsts; d; d = d->next)
					d->type = t;
			}
			t->size = t->base->size;
			t->align = t->base->align;
			t->u.arith.issigned = t->base->u.arith.issigned;
			t->u.arith.width = t->base->u.arith.width;
		}
	}
	t->incomplete = false;

	return t;
}

/* 6.7 Declarations */
static struct qualtype
declspecs(struct scope *s, enum storageclass *sc, enum funcspec *fs, int *align)
{
	struct type *t, *other;
	struct decl *d;
	struct expr *e;
	enum typespec ts = SPECNONE;
	enum typequal tq = QUALNONE;
	enum tokenkind op;
	int ntypes = 0;
	unsigned long long i, bits;
	struct expr *typeofexpr = NULL;

	t = NULL;
	if (sc)
		*sc = SCNONE;
	if (fs)
		*fs = FUNCNONE;
	if (align)
		*align = 0;
	for (;;) {
		if (typequal(&tq) || storageclass(sc) || funcspec(fs))
			continue;
		op = tok.kind;
		switch (op) {
		/* 6.7.2 Type specifiers */
		case TVOID:
			t = &typevoid;
			++ntypes;
			next();
			break;
		case TCHAR:
			ts |= SPECCHAR;
			++ntypes;
			next();
			break;
		case TSHORT:
			if (ts & SPECSHORT)
				error(&tok.loc, "duplicate 'short'");
			ts |= SPECSHORT;
			next();
			break;
		case TINT:
			ts |= SPECINT;
			++ntypes;
			next();
			break;
		case TLONG:
			if (ts & SPECLONG2)
				error(&tok.loc, "too many 'long'");
			if (ts & SPECLONG)
				ts |= SPECLONG2;
			ts |= SPECLONG;
			next();
			break;
		case TFLOAT:
			ts |= SPECFLOAT;
			++ntypes;
			next();
			break;
		case TDOUBLE:
			ts |= SPECDOUBLE;
			++ntypes;
			next();
			break;
		case T__FLOAT128:
			ts |= SPECFLOAT128;
			++ntypes;
			next();
			break;
		case T__INT128:
			ts |= SPECINT128;
			++ntypes;
			next();
			break;
		case T__FLOAT16:
			ts |= SPECFLOAT16;
			++ntypes;
			next();
			break;
		case TSIGNED:
			if (ts & SPECSIGNED)
				error(&tok.loc, "duplicate 'signed'");
			ts |= SPECSIGNED;
			next();
			break;
		case TUNSIGNED:
			if (ts & SPECUNSIGNED)
				error(&tok.loc, "duplicate 'unsigned'");
			ts |= SPECUNSIGNED;
			next();
			break;
		case T_BITINT:
			ts |= SPECBITINT;
			++ntypes;
			next();
			expect(TLPAREN, "after _BitInt");
			bits = intconstexpr(s, false);
			expect(TRPAREN, "after _BitInt width");
			break;
		case TBOOL:
			t = &typebool;
			++ntypes;
			next();
			break;
		case T_COMPLEX:
			error(&tok.loc, "_Complex is not yet supported");
			break;
		case T_ATOMIC:
			error(&tok.loc, "_Atomic is not yet supported");
			break;
		case TSTRUCT:
		case TUNION:
		case TENUM:
			t = tagspec(s);
			++ntypes;
			break;
		case TTYPEOF:
		case TTYPEOF_UNQUAL:
			next();
			expect(TLPAREN, "after 'typeof'");
			t = typename(s, &tq, &typeofexpr);
			if (!t) {
				e = expr(s);
				if (e->decayed)
					e = e->base;
				t = e->type;
				if (op == TTYPEOF)
					tq |= e->qual;
				if (t->prop & PROPVM)
					typeofexpr = e;
			}
			++ntypes;
			expect(TRPAREN, "to close 'typeof'");
			break;

		/* 6.7.5 Alignment specifier */
		case TALIGNAS:
			if (!align)
				error(&tok.loc, "alignment specifier not allowed in this declaration");
			alignasseen = true;
			next();
			expect(TLPAREN, "after 'alignas'");
			other = typename(s, NULL, NULL);
			i = other ? other->align : intconstexpr(s, false);
			if (i & i - 1 || i > INT_MAX)
				error(&tok.loc, "invalid alignment: %llu", i);
			if (i > *align)
				*align = i;
			expect(TRPAREN, "to close 'alignas' specifier");
			break;

		case T__ATTRIBUTE__: {
			/* static int __attribute__((aligned(64))) x; typedef int __attribute__((aligned(8))) aint; */
			struct attr da = {0};

			gnuattr(&da, align ? ATTRALIGNED : 0);
			if (align && da.kind & ATTRALIGNED && da.align > *align)
				*align = da.align;
			break;
		}

		default:
			if (!iscident(op) || t || ts)
				goto done;
			d = scopegetdecl(s, tokenstr(tok.kind), 1);
			if (!d || d->kind != DECLTYPE)
				goto done;
			t = d->type;
			tq |= d->qual;
			++ntypes;
			next();
			break;
		}
		if (ntypes > 1 || (t && ts))
			error(&tok.loc, "multiple types in declaration specifiers");
	}
done:
	switch ((int)ts) {
	case SPECNONE:                                            break;
	case SPECCHAR:                          t = &typechar;    break;
	case SPECSIGNED|SPECCHAR:               t = &typeschar;   break;
	case SPECUNSIGNED|SPECCHAR:             t = &typeuchar;   break;
	case SPECSHORT:
	case SPECSHORT|SPECINT:
	case SPECSIGNED|SPECSHORT:
	case SPECSIGNED|SPECSHORT|SPECINT:      t = &typeshort;   break;
	case SPECUNSIGNED|SPECSHORT:
	case SPECUNSIGNED|SPECSHORT|SPECINT:    t = &typeushort;  break;
	case SPECINT:
	case SPECSIGNED:
	case SPECSIGNED|SPECINT:                t = &typeint;     break;
	case SPECUNSIGNED:
	case SPECUNSIGNED|SPECINT:              t = &typeuint;    break;
	case SPECLONG:
	case SPECLONG|SPECINT:
	case SPECSIGNED|SPECLONG:
	case SPECSIGNED|SPECLONG|SPECINT:       t = &typelong;    break;
	case SPECUNSIGNED|SPECLONG:
	case SPECUNSIGNED|SPECLONG|SPECINT:     t = &typeulong;   break;
	case SPECLONGLONG:
	case SPECLONGLONG|SPECINT:
	case SPECSIGNED|SPECLONGLONG:
	case SPECSIGNED|SPECLONGLONG|SPECINT:   t = &typellong;   break;
	case SPECUNSIGNED|SPECLONGLONG:
	case SPECUNSIGNED|SPECLONGLONG|SPECINT: t = &typeullong;  break;
	case SPECBITINT:
	case SPECBITINT|SPECSIGNED:             t = mkbitinttype(bits, true); break;
	case SPECBITINT|SPECUNSIGNED:           t = mkbitinttype(bits, false); break;
	case SPECFLOAT:                         t = &typefloat;   break;
	case SPECDOUBLE:                        t = &typedouble;  break;
	case SPECLONG|SPECDOUBLE:               t = &typeldouble; break;
	case SPECFLOAT128:                      t = &typefloat128; break;
	case SPECFLOAT16:                       t = &typefloat16; break;
	case SPECINT128:
	case SPECINT128|SPECSIGNED:             t = &typeint128;  break;
	case SPECINT128|SPECUNSIGNED:           t = &typeuint128; break;
	default:
		error(&tok.loc, "invalid combination of type specifiers");
	}
	if (tq & QUALRESTRICT) {
		/* C23 6.7.4.1p2 */
		other = t;
		while (other->kind == TYPEARRAY)
			other = other->base;
		if (!other || other->kind != TYPEPOINTER)
			error(&tok.loc, "'restrict' applied to non-pointer type");
		if (other->base->kind == TYPEFUNC)
			error(&tok.loc, "'restrict' applied to function pointer");
	}
	if (!t && (tq || sc && *sc || fs && *fs))
		error(&tok.loc, "declaration has no type specifier");
	/*
	TODO: consider delaying attribute parsing to declarator(),
	so we can tell the difference between the start of an
	attribute and an array declarator.
	*/
	attr(NULL, 0);

	return (struct qualtype){t, tq, typeofexpr};
}

/* 6.7.6 Declarators */
static struct decl *parameter(struct scope *);

static bool
istypename(struct scope *s, const char *name)
{
	struct decl *d;

	d = scopegetdecl(s, name, 1);
	return d && d->kind == DECLTYPE;
}

/*
When parsing a declarator, qualifiers for derived types are temporarily
stored in the `qual` field of the type itself (elsewhere this field
is used for the qualifiers of the base type). This is corrected in
declarator().
*/
/* the cleanup attribute of the last declarator that has one (declaratortypes), for the object declaration that reads it */
static const char *declcleanup;

static void
declaratortypes(struct scope *s, struct list *result, char **name, int *align, struct scope **funcscope, bool allowabstract)
{
	struct list *ptr;
	struct type *t;
	struct decl *d, **paramend;
	struct expr *e;
	struct attr a;
	enum typequal tq;
	int allowedattr;

	a.kind = 0;
	for (;;) {
		/* GNU attributes before a pointer, (__attribute__((ms_abi)) *f)(...), and between a pointer and the name */
		if (tok.kind == T__ATTRIBUTE__) {
			gnuattr(&a, align ? ATTRALIGNED : 0);
			continue;
		}
		if (!consume(TMUL))
			break;
		attr(NULL, 0);
		tq = QUALNONE;
		while (typequal(&tq))
			;
		t = mkpointertype(NULL, tq);
		listinsert(result, &t->link);
	}
	if (name)
		*name = NULL;
	/* GNU attributes between the pointer and the declarator name, e.g. void * __attribute__((...)) f() -- they
	 * appertain to the declared entity (the kernel's __must_check, __user and friends sit here) */
	while (tok.kind == T__ATTRIBUTE__)
		gnuattr(&a, align ? ATTRALIGNED : 0);
	if (align && (a.kind & ATTRALIGNED) && a.align > *align)
		*align = a.align;
	ptr = result->next;
	switch (tok.kind) {
	case TLPAREN:
		next();
		if (allowabstract) {
			switch (tok.kind) {
			case TMUL:
			case TLPAREN:
			case T__ATTRIBUTE__:   /* (__attribute__((ms_abi)) *f): a declarator, not parameters */
				break;
			default:
				if (iscident(tok.kind) && !istypename(s, tokenstr(tok.kind)))
					break;
				goto func;
			}
		}
		declaratortypes(s, result, name, align, funcscope, allowabstract);
		expect(TRPAREN, "after parenthesized declarator");
		allowedattr = -1;
		break;
	default:
		if (iscident(tok.kind)) {
			if (!name)
				error(&tok.loc, "identifier not allowed in abstract declarator");
			*name = tokenstr(tok.kind);
			next();
		} else if (!allowabstract) {
			error(&tok.loc, "expected '(' or identifier");
		}
		/*
		the aligned attribute is used in the definition of
		max_align_t from gcc/clang (used with glibc),
		dragonflybsd, freebsd, and openbsd
		*/
		allowedattr = align ? ATTRALIGNED : 0;
	}
	for (;;) {
		switch (tok.kind) {
		case TLPAREN:  /* function declarator */
			next();
		func:
			t = mktype(TYPEFUNC, 0);
			t->qual = QUALNONE;
			t->u.func.abi = attrabi;   /* (__attribute__((ms_abi)) *f)(...) */
			attrabi = NULL;
			t->u.func.isvararg = false;
			t->u.func.params = NULL;
			t->u.func.nparam = 0;
			t->u.func.unprototyped = tok.kind == TRPAREN;
			paramend = &t->u.func.params;
			s = mkscope(s);
			d = NULL;
			do {
				if (consume(TELLIPSIS)) {
					t->u.func.isvararg = true;
					break;
				}
				if (tok.kind == TRPAREN)
					break;
				d = parameter(s);
				if (d->name)
					scopeputdecl(s, d);
				*paramend = d;
				paramend = &d->next;
				++t->u.func.nparam;
			} while (consume(TCOMMA));
			expect(TRPAREN, "to close function declarator");
			if (funcscope && ptr->prev == result) {
				/* we may need to re-open the scope later if this is a function definition */
				*funcscope = s;
				s = s->parent;
			} else {
				s = delscope(s);
			}
			if (t->u.func.nparam == 1 && !t->u.func.isvararg && d->type->kind == TYPEVOID && !d->name) {
				t->u.func.params = NULL;
				t->u.func.nparam = 0;
			}
			listinsert(ptr->prev, &t->link);
			allowedattr = 0;
			break;
		case TLBRACK:  /* array declarator */
			if (allowedattr != -1 && attr(&a, allowedattr))
				goto attr;
			next();
			t = mkarraytype(NULL, QUALNONE, 0);
			while (consume(TSTATIC) || typequal(&t->u.array.ptrqual))
				;
			if (tok.kind == TMUL && peek(TRBRACK)) {
				t->prop |= PROPVM;
				t->incomplete = false;
			} else if (!consume(TRBRACK)) {
				e = assignexpr(s);
				if (!(e->type->prop & PROPINT))
					error(&tok.loc, "array length expression must have integer type");
				t->u.array.length = e;
				t->incomplete = false;
				expect(TRBRACK, "after array length");
			}
			listinsert(ptr->prev, &t->link);
			allowedattr = align ? ATTRALIGNED : 0;   /* T a[N] __attribute__((aligned(M))) aligns a */
			break;
		case T__ATTRIBUTE__:
			if (allowedattr == -1)
				error(&tok.loc, "attribute not allowed after parenthesized declarator");
			/* packed is meaningful on a member (structdecl reads declpacked); gcc ignores it on other declarators */
			gnuattr(&a, allowedattr | ATTRCLEANUP | (align && allowedattr != -1 ? ATTRPACKED : 0));
			if (a.kind & ATTRPACKED)
				declpacked = true;
		attr:
			/* aligned applies to the declared entity, after an array declarator too; cleanup to the identifier */
			if (align && a.kind & ATTRALIGNED && a.align > *align)
				*align = a.align;
			if (ptr->prev == result && a.kind & ATTRCLEANUP)
				declcleanup = a.cleanup;
			break;
		default:
			return;
		}
	}
}

/* 6.7.3p9: a qualified array type is an array of qualified elements. A derived type keeps its base's
   qualifiers in its own qual field, so for a qualified array (const T typedef'd to an array) the
   qualifiers must go on the array node itself, or a pointer to it differs from a pointer to the
   elements-qualified array (`const S *` against `const unsigned char (*)[12]`). */
static struct type *
qualarray(struct type *t, enum typequal qual)
{
	struct type *n;

	n = xmalloc(sizeof(*n));
	*n = *t;
	n->qual |= qual;
	return n;
}

static struct qualtype
declarator(struct scope *s, struct qualtype base, char **name, int *align, struct scope **funcscope, bool allowabstract)
{
	struct type *t;
	enum typequal tq;
	struct expr *e;
	struct list result = {&result, &result}, *l, *prev;

	if (funcscope)
		*funcscope = NULL;
	declaratortypes(s, &result, name, align, funcscope, allowabstract);
	if (result.prev != &result && base.type->kind == TYPEARRAY && base.qual) {
		base.type = qualarray(base.type, base.qual);
		base.qual = QUALNONE;
	}
	for (l = result.prev; l != &result; l = prev) {
		prev = l->prev;
		t = listelement(l, struct type, link);
		tq = t->qual;
		t->base = base.type;
		t->qual = base.qual;
		t->prop |= base.type->prop & PROPVM;
		switch (t->kind) {
		case TYPEFUNC:
			if (base.type->kind == TYPEFUNC)
				error(&tok.loc, "function declarator specifies function return type");
			if (base.type->kind == TYPEARRAY)
				error(&tok.loc, "function declarator specifies array return type");
			break;
		case TYPEARRAY:
			if (base.type->incomplete)
				error(&tok.loc, "array element has incomplete type");
			if (base.type->kind == TYPEFUNC)
				error(&tok.loc, "array element has function type");
			if (t->u.array.ptrqual) {
				/* TODO: check if we are in a function prototype
				if (?)
					error(&tok.loc, "array type has qualifiers outside of a function prototype");
				*/
				if (prev != &result)
					error(&tok.loc, "nested array type has qualifiers");
			}
			t->align = base.type->align;
			t->size = 0;
			if (t->u.array.length) {
				e = eval(t->u.array.length);
				if (e->kind == EXPRCONST && !(t->prop & PROPVM)) {
					if (e->type->u.arith.issigned && e->u.constant.u >> 63)
						error(&tok.loc, "array length must be non-negative");
					if (base.type->size && e->u.constant.u > ULLONG_MAX / base.type->size)
						error(&tok.loc, "array length is too large");
					t->size = base.type->size * e->u.constant.u;
				} else {
					t->prop |= PROPVM;
					t->u.array.length = e;
					t->u.array.size = NULL;
				}
			}
			break;
		}
		base.type = t;
		base.qual = tq;
	}

	return base;
}

static struct decl *
parameter(struct scope *s)
{
	struct decl *d;
	char *name;
	struct qualtype t;
	enum storageclass sc;

	attr(NULL, 0);
	t = declspecs(s, &sc, NULL, NULL);
	if (!t.type)
		error(&tok.loc, "no type in parameter declaration");
	if (sc && sc != SCREGISTER)
		error(&tok.loc, "parameter declaration has invalid storage-class specifier");
	t = declarator(s, t, &name, NULL, NULL, true);
	t.type = typeadjust(t.type, &t.qual);
	d = mkdecl(name, DECLOBJECT, t.type, t.qual, LINKNONE);
	d->u.obj.storage = SDAUTO;
	return d;
}

static void
addmember(struct structbuilder *b, struct qualtype mt, char *name, int align, unsigned long long width)
{
	struct type *t = b->type;
	struct member *m;
	size_t end;

	/* a member after a struct that ends in a flexible array member is a GNU extension (the kernel's tty_bufhead) */
	if (t->kind == TYPESTRUCT && b->fam)
		error(&tok.loc, "struct has member '%s' after flexible array member", name);
	if (mt.type->incomplete) {
		if (mt.type->kind != TYPEARRAY)
			error(&tok.loc, "struct member '%s' has incomplete type", name);
		t->prop |= PROPFLEX;
		b->fam = true;
	}
	if (mt.type->prop & PROPFLEX) {
		/*
		ISO C doesn't allow structures with members containing
		FAMs, but allow it as an extension
		*/
		t->prop |= PROPFLEX;
	}
	if (mt.type->kind == TYPEFUNC)
		error(&tok.loc, "struct member '%s' has function type", name);
	if (mt.type->prop & PROPVM)
		error(&tok.loc, "struct member '%s' has variably modified type", name);
	assert(mt.type->align > 0);
	if (width != -1)
		b->hasbits = true;
	if (name || width == -1) {
		m = xmalloc(sizeof(*m));
		m->type = mt.type;
		m->qual = mt.qual;
		m->name = name;
		m->align = width == -1 ? align : 0;
		m->next = NULL;
		*b->last = m;
		b->last = &m->next;
	} else {
		m = NULL;
	}
	if (width == -1) {
		m->bits.before = 0;
		m->bits.after = 0;
		bool packlimited = false;

		if (b->pragmapack && (align ? align : mt.type->align) > b->pragmapack) {
			/* #pragma pack(N): the member's alignment is at most N, its type's or an aligned attribute's */
			if (align)
				error(&tok.loc, "an aligned attribute on member '%s' under #pragma pack is not supported", name);
			align = b->pragmapack;
			packlimited = true;
		}
		if (align < mt.type->align && !packlimited) {
			/* in a packed struct (or a packed member) an explicit alignment below the type's is what was asked for;
			 * otherwise gcc ignores it (aligned on a member only raises the alignment: the kernel's
			 * compat_group_req has struct __kernel_sockaddr_storage gr_group __aligned(4)) */
			if (!align || !b->pack)
				align = b->pack ? 1 : mt.type->align;
		}
		if (t->kind == TYPESTRUCT) {
			m->offset = ALIGNUP(t->size, align);
			t->size = m->offset + mt.type->size;
			b->packbits = ALIGNUP(b->packbits, 8 * (m->align ? m->align : 1));
			if (b->packbits != m->offset * 8ull)
				b->packmoves = true;
			b->packbits = t->size * 8ull;
		} else {
			m->offset = 0;
			if (t->size < mt.type->size)
				t->size = mt.type->size;
		}
		b->bits = 0;
	} else {  /* bit-field */
		if (!(mt.type->prop & PROPINT))
			error(&tok.loc, "bit-field '%s' has invalid type", name);
		if (align)
			error(&tok.loc, "alignment specified for bit-field '%s'", name);
		if (b->pack)
			error(&tok.loc, "bit-field '%s' in packed struct is not supported", name);
		if (b->pragmapack && mt.type->align > b->pragmapack)
			error(&tok.loc, "bit-field '%s' under #pragma pack(%d) is not supported", name, b->pragmapack);
		if (!width && name)
			error(&tok.loc, "bit-field '%s' with zero width must not have declarator", name);
		if (width > mt.type->u.arith.width)
			error(&tok.loc, "bit-field '%s' exceeds width of underlying type", name);
		align = mt.type->align;
		if (t->kind == TYPESTRUCT) {
			/* calculate end of the storage-unit for this bit-field */
			end = ALIGNUP(t->size, mt.type->size);
			if (!width || width > (end - t->size) * 8 + b->bits) {
				/* no room, allocate a new storage-unit */
				t->size = end;
				b->bits = 0;
			}
			/* packed, gcc puts a bit-field at the next bit; a zero-width one is not modelled */
			if (!width || b->packbits != t->size * 8ull - b->bits)
				b->packmoves = true;
			b->packbits = t->size * 8ull - b->bits + width;
			if (m) {
				m->offset = ALIGNDOWN(t->size - !!b->bits, mt.type->size);
				m->bits.before = (t->size - m->offset) * 8 - b->bits;
				m->bits.after = mt.type->size * 8 - width - m->bits.before;
			}
			t->size += (width - b->bits + 7) / 8;
			b->bits = (b->bits - width) % 8;
		} else if (m) {
			m->offset = 0;
			m->bits.before = 0;
			m->bits.after = mt.type->size * 8 - width;
			if (t->size < mt.type->size)
				t->size = mt.type->size;
		}
	}
	if (m && t->align < align)
		t->align = align;
}

/* struct S { ... } __attribute__((packed)): the members were laid out as they were parsed, so lay them out again with
 * alignment 1, except where a member asked for an alignment (aligned attribute), as gcc does */
static void
structpack(struct type *t)
{
	struct member *m;
	int align;

	t->size = 0;
	t->align = 1;
	for (m = t->u.structunion.members; m; m = m->next) {
		align = m->align ? m->align : 1;
		if (t->kind == TYPESTRUCT) {
			m->offset = ALIGNUP(t->size, align);
			t->size = m->offset + m->type->size;
		} else {
			m->offset = 0;
			if (t->size < m->type->size)
				t->size = m->type->size;
		}
		if (t->align < align)
			t->align = align;
	}
}

/*
struct S { ... } __attribute__((packed)) with bit-fields (the kernel's desc_struct: u16 base1: 8, type: 4, ...; its
orc_entry: s16, s16, unsigned sp_reg: 4, ... in 6 bytes). gcc packs bit-fields bit by bit and accesses only the bytes a
field spans; cproc accesses a bit-field through a unit of its type's size. So this is taken only when the packed layout
is the natural one (packing moves no member, b->packmoves): then only the alignment and the tail padding change. A
bit-field whose unit would reach past the packed struct or into a member that is not a bit-field moves to the smallest
integer unit of its signedness that holds its bits (the field keeps its place, and its value converts and promotes
alike: cproc promotes a bit-field by its width). Anything else is refused.
*/
static struct type *
bitunittype(struct type *t, unsigned long long size)
{
	bool s = t->u.arith.issigned;

	switch (size) {
	case 1: return s ? &typeschar : &typeuchar;
	case 2: return s ? &typeshort : &typeushort;
	case 4: return s ? &typeint : &typeuint;
	case 8: return s ? &typelong : &typeulong;
	}
	return NULL;
}

/* whether the unit [off, off + size) of bit-field m lies inside the struct and shares no byte with a plain member */
static bool
bitunitfits(struct type *t, struct member *m, unsigned long long off, unsigned long long size, unsigned long long end)
{
	struct member *n;

	if (off + size > end)
		return false;
	for (n = t->u.structunion.members; n; n = n->next) {
		if (n == m || n->bits.before || n->bits.after || !n->type->size)
			continue;
		if (n->offset < off + size && off < n->offset + n->type->size)
			return false;
	}
	return true;
}

static void
structpackbits(struct type *t, struct structbuilder *b)
{
	struct member *m;
	unsigned long long size, end, pos, width, u;
	int align = 1;

	if (t->kind != TYPESTRUCT || b->packmoves)
		error(&tok.loc, "bit-fields in a packed struct are not supported (packing would move a member)");
	size = (b->packbits + 7) / 8;
	for (m = t->u.structunion.members; m; m = m->next)
		if (m->align > align)
			align = m->align;
	end = ALIGNUP(size, align);
	for (m = t->u.structunion.members; m; m = m->next) {
		if (!m->bits.before && !m->bits.after)
			continue;
		if (bitunitfits(t, m, m->offset, m->type->size, end))
			continue;
		pos = m->offset * 8ull + m->bits.before;
		width = m->type->size * 8ull - m->bits.before - m->bits.after;
		if (m->type->kind == TYPEBOOL || m->type->kind == TYPEENUM)
			u = 0;
		else
			for (u = 1; u < m->type->size && (pos % 8 + width > u * 8 || !bitunitfits(t, m, pos / 8, u, end)); u *= 2)
				;
		if (!u || u >= m->type->size)
			error(&tok.loc, "bit-fields in a packed struct are not supported (bit-field '%s' would be accessed past the end or with another member)", m->name);
		m->type = bitunittype(m->type, u);
		m->offset = pos / 8;
		m->bits.before = pos % 8;
		m->bits.after = u * 8 - width - pos % 8;
	}
	t->size = size;
	t->align = align;
}

static bool
staticassert(struct scope *s)
{
	struct stringlit msg;
	unsigned long long c;

	if (!consume(TSTATIC_ASSERT))
		return false;
	expect(TLPAREN, "after static_assert");
	c = intconstexpr(s, true);
	if (consume(TCOMMA)) {
		tokencheck(&tok, TSTRINGLIT, "after static assertion expression");
		stringconcat(&msg, true);
		if (!c)
			error(&tok.loc, "static assertion failed: %.*s", (int)(msg.size - 1), (char *)msg.data);
	} else if (!c) {
		error(&tok.loc, "static assertion failed");
	}
	expect(TRPAREN, "after static assertion");
	expect(TSEMICOLON, "after static assertion");
	return true;
}

static void
structdecl(struct scope *s, struct structbuilder *b)
{
	struct qualtype base, mt;
	char *name;
	unsigned long long width;
	int align, specalign, savedmode = declattr.modesize, basemode;

	if (staticassert(s))
		return;
	if (consume(TSEMICOLON))   /* GNU: an empty member declaration (the kernel's cleanup.h guards, "T *lock; ;") */
		return;
	attr(NULL, 0);
	declattr.modesize = 0;   /* a member's mode is its own, not the enclosing declaration's */
	base = declspecs(s, NULL, NULL, &align);
	basemode = declattr.modesize;
	specalign = align;
	if (!base.type)
		error(&tok.loc, "no type in struct member declaration");
	if (tok.kind == TSEMICOLON) {
		if ((base.type->kind != TYPESTRUCT && base.type->kind != TYPEUNION) || base.type->u.structunion.tag)
			error(&tok.loc, "struct declaration must declare at least one member");
		next();
		addmember(b, base, NULL, align, -1);
		return;
	}
	for (;;) {
		if (consume(TCOLON)) {
			width = intconstexpr(s, false);
			addmember(b, base, NULL, 0, width);
		} else {
			bool pack = b->pack;

			align = specalign;   /* a member's aligned attribute does not carry to the next declarator */
			declpacked = false;
			declattr.modesize = basemode;
			mt = declarator(s, base, &name, &align, NULL, false);
			if (declattr.modesize)
				mt.type = modetype(mt.type, declattr.modesize);
			width = consume(TCOLON) ? intconstexpr(s, false) : -1;
			b->pack = pack || declpacked;   /* int x __attribute__((packed)): this member alone has alignment 1 */
			addmember(b, mt, name, align, width);
			b->pack = pack;
		}
		if (tok.kind == TSEMICOLON)
			break;
		expect(TCOMMA, "or ';' after declarator");
	}
	declattr.modesize = savedmode;
	next();
}

/* 6.7.7 Type names */
struct type *
typename(struct scope *s, enum typequal *tq, struct expr **toeval)
{
	struct qualtype t;

	int savedmode = declattr.modesize;

	declattr.modesize = 0;
	t = declspecs(s, NULL, NULL, NULL);
	if (t.type) {
		t = declarator(s, t, NULL, NULL, NULL, true);
		if (declattr.modesize)
			error(&tok.loc, "GNU attribute mode in a type name is not supported");
		declattr.modesize = savedmode;
		if (tq)
			*tq |= t.qual;
		if (toeval)
			*toeval = t.expr;
	}
	return t.type;
}

static enum linkage
getlinkage(enum declkind kind, enum storageclass sc, struct decl *prior, bool filescope)
{
	if (sc & SCSTATIC)
		return filescope ? LINKINTERN : LINKNONE;
	if (sc & SCEXTERN || kind == DECLFUNC)
		return prior ? prior->linkage : LINKEXTERN;
	return filescope ? LINKEXTERN : LINKNONE;
}

static struct decl *
declcommon(struct scope *s, enum declkind kind, char *name, char *asmname, struct type *t, enum typequal tq, enum storageclass sc, struct decl *prior)
{
	struct decl *d;
	enum linkage linkage;
	const char *kindstr = kind == DECLFUNC ? "function" : "object";

	if (prior) {
		if (prior->linkage == LINKNONE)
			error(&tok.loc, "%s '%s' with no linkage redeclared", kindstr, name);
		linkage = getlinkage(kind, sc, prior, s == &filescope);
		if (prior->linkage != linkage)
			error(&tok.loc, "%s '%s' redeclared with different linkage", kindstr, name);
		if (!typecompatible(t, prior->type) || tq != prior->qual)
			error(&tok.loc, "%s '%s' redeclared with incompatible type", kindstr, name);
		if (asmname && (!prior->asmname || strcmp(prior->asmname, asmname) != 0))
			error(&tok.loc, "%s '%s' redeclared with different assembler name", kindstr, name);
		prior->type = typecomposite(t, prior->type);
		return prior;
	}
	if (s->parent)
		prior = scopegetdecl(s->parent, name, true);
	linkage = getlinkage(kind, sc, prior, s == &filescope);
	if (linkage != LINKNONE && s->parent) {
		/* XXX: should maintain map of identifiers with linkage to their declaration, and use that */
		if (s->parent != &filescope)
			prior = scopegetdecl(&filescope, name, false);
		if (prior && prior->linkage != LINKNONE) {
			if (prior->kind != kind)
				error(&tok.loc, "'%s' redeclared with different kind", name);
			if (prior->linkage != linkage)
				error(&tok.loc, "%s '%s' redeclared with different linkage", kindstr, name);
			if (!typecompatible(t, prior->type) || tq != prior->qual)
				error(&tok.loc, "%s '%s' redeclared with incompatible type", kindstr, name);
			if (!asmname)
				asmname = prior->asmname;
			else if (!prior->asmname || strcmp(prior->asmname, asmname) != 0)
				error(&tok.loc, "%s '%s' redeclared with different assembler name", kindstr, name);
			t = typecomposite(t, prior->type);
		}
	}
	d = mkdecl(name, kind, t, tq, linkage);
	d->asmname = asmname;
	scopeputdecl(s, d);
	return d;
}

/* the section/used attributes gathered for this declarator (declattr); a redeclaration keeps an earlier section */
static struct decl *symattrs, **symattrsend = &symattrs;

static void
declapplyattr(struct decl *d)
{
	if (declattr.section)
		d->section = declattr.section;
	if (declattr.used)
		d->used = true;
	if (declattr.weak)
		d->weak = true;
	if (declattr.noipa)
		d->noipa = true;
	if (declattr.visibility)
		d->visibility = declattr.visibility;
	else if (pragmavisibility && !d->visibility)
		d->visibility = pragmavisibility;
	if (declattr.alias)
		d->alias = declattr.alias;
	/* weak and visibility are directives for the symbol, written at the end (emitsymattrs) */
	if ((d->weak || d->visibility && strcmp(d->visibility, "default")) && d->linkage == LINKEXTERN && !d->symattr) {
		d->symattr = true;
		*symattrsend = d;
		symattrsend = &d->symattrnext;
	}
}

void
emitsymattrs(void)
{
	struct decl *d;

	for (d = symattrs; d; d = d->symattrnext)
		emitsymattr(d);
}

static void
defineobj(struct decl *d, struct init *init, bool hasinit, struct func *f)
{
	if (d->type->incomplete)
		error(&tok.loc, "object '%s' has incomplete type", d->name);
	if (d->u.obj.align < d->type->align)
		d->u.obj.align = d->type->align;
	if (d->u.obj.storage == SDAUTO)
		funcinit(f, d, init, hasinit || autozero);   /* -z: zero an automatic object that has no initializer */
	else
		emitdata(d, init, f);
	d->defined = true;
}

static bool decl1(struct scope *, struct func *);

/* the attributes of a declaration name its scope's constants (the kernel's block-scope enum { TEST_ALIGNMENT = 16 } in
 * __aligned(TEST_ALIGNMENT)) */
bool
decl(struct scope *s, struct func *f)
{
	struct scope *old = attrscope;
	bool r;

	attrscope = s;
	r = decl1(s, f);
	attrscope = old;
	return r;
}

static bool
decl1(struct scope *s, struct func *f)
{
	struct qualtype base, qt;
	struct type *t;
	enum typequal tq;
	enum storageclass sc;
	enum funcspec fs;
	struct attr a;
	struct init *init;
	bool hasinit;
	char *name, *asmname;
	int specalign;
	char *regname;
	struct declattr specattr;
	int allowfunc = !f;
	bool gnuinlineonly;
	struct decl *d, *prior;
	enum declkind kind;
	struct scope *funcscope;
	int align;

	if (staticassert(s))
		return true;
	attrabi = NULL;
	if (!f && consume(TSEMICOLON))   /* GNU: an empty declaration at file scope (a ';' after a function body) */
		return true;
	if (!f && tok.kind == T__ASM__) {
		/* GNU basic asm at file scope (the kernel's EXPORT_SYMBOL): __asm__ ( string ) ; its text goes to the
		 * assembly as it is, no operands and no '%' substitution */
		struct stringlit lit;

		next();
		expect(TLPAREN, "after 'asm'");
		tokencheck(&tok, TSTRINGLIT, "for asm text");
		stringconcat(&lit, true);
		if (tok.kind == TCOLON)
			error(&tok.loc, "operands in a file-scope asm are not supported");
		expect(TRPAREN, "after asm text");
		expect(TSEMICOLON, "after file-scope asm");
		emitasm(lit.data);
		return true;
	}
	a.kind = 0;
	declattr = (struct declattr){0};
	alignasseen = false;
	if (attr(&a, ATTRNORETURN) && consume(TSEMICOLON))
		return true;
	base = declspecs(s, &sc, &fs, &align);
	specattr = declattr;   /* section/used in the declaration specifiers apply to every declarator */
	if (!base.type)
		return false;
	if (f) {
		if (sc == SCTHREADLOCAL)
			error(&tok.loc, "block scope declaration containing 'thread_local' must contain 'static' or 'extern'");
	} else {
		/* 6.9p2 */
		if (sc & SCAUTO)
			error(&tok.loc, "external declaration must not contain 'auto'");
		/* 'register' at file scope only with asm("REG"), a GNU global register variable: checked per declarator */
	}
	if (consume(TSEMICOLON)) {
		/* XXX 6.7p2 error unless in function parameter/struct/union, or tag/enum members are declared */
		return true;
	}
	specalign = align;
	for (;;) {
		declcleanup = NULL;
		align = specalign;   /* the declaration's _Alignas, raised per declarator by a trailing aligned attribute */
		declattr = specattr;
		qt = declarator(s, base, &name, &align, &funcscope, false);
		t = qt.type;
		tq = qt.qual;
		if (consume(T__ASM__)) {
			struct stringlit lit;

			expect(TLPAREN, "after __asm__");
			tokencheck(&tok, TSTRINGLIT, "after __asm__");
			stringconcat(&lit, true);
			asmname = lit.data;
			expect(TRPAREN, "after assembler name");
			allowfunc = 0;
		} else {
			asmname = NULL;
		}
		gnuattr(&a, 0);  /* appertains to identifier */
		if (declattr.modesize)
			t = modetype(t, declattr.modesize);
		kind = sc & SCTYPEDEF ? DECLTYPE : t->kind == TYPEFUNC ? DECLFUNC : DECLOBJECT;
		if (declattr.transparent && kind != DECLTYPE)
			error(&tok.loc, "transparent_union is only supported on a typedef of a union");
		/* GNU register variable: register T x asm("REG"). The asm name is the register, not a symbol. At file scope it
		 * is a global register variable (the kernel's current_stack_pointer is %rsp); in a block it is an ordinary
		 * automatic object that inline asm operands take in REG. */
		regname = NULL;
		if (kind == DECLOBJECT && sc & SCREGISTER && asmname) {
			regname = asmname[0] == '%' ? asmname + 1 : asmname;
			asmname = NULL;
		} else if (!f && sc & SCREGISTER) {
			error(&tok.loc, "external declaration must not contain 'register'");
		}
		if (regname && !f) {
			prior = scopegetdecl(s, name, false);
			if (prior && (prior->kind != DECLOBJECT || !prior->regvar || strcmp(prior->regvar, regname)))
				error(&tok.loc, "'%s' redeclared as a different register variable", name);
			if (!prior) {
				d = mkdecl(name, DECLOBJECT, t, tq, LINKNONE);
				d->u.obj.storage = SDSTATIC;
				d->regvar = regname;
				d->defined = true;
				scopeputdecl(s, d);
			}
			if (tok.kind == TASSIGN)
				error(&tok.loc, "global register variable '%s' cannot have an initializer", name);
			if (consume(TSEMICOLON))
				return true;
			expect(TCOMMA, "or ';' after declarator");
			continue;
		}
		prior = scopegetdecl(s, name, false);
		/* a file-scope function may declare a name that is a builtin (as GCC allows for library-like builtins, such as
		 * the generic __atomic_* forms): the declaration replaces the builtin, and calls go to the declared function */
		if (prior && prior->kind == DECLBUILTIN && kind == DECLFUNC && s == &filescope)
			prior = NULL;
		if (prior && prior->kind != kind)
			error(&tok.loc, "'%s' redeclared with different kind", name);
		switch (kind) {
		case DECLTYPE:
			if (asmname)
				error(&tok.loc, "typedef '%s' declared with assembler label", name);
			if (align > t->align) {
				/* an aligned attribute on a typedef raises the alignment of a copy of the type (GNU) */
				struct type *nt = xmalloc(sizeof *nt);
				*nt = *t;
				nt->align = align;
				t = nt;
			}
			if (declattr.transparent) {
				/* GNU transparent_union (the kernel's release_pages_arg): a copy of the union. Every member must be
				 * passed as the first one is, so only pointers and integers of the first one's size are taken. */
				struct type *nt;
				struct member *m;

				if (t->kind != TYPEUNION || !t->u.structunion.members)
					error(&tok.loc, "transparent_union is only valid on a union with members");
				for (m = t->u.structunion.members; m; m = m->next)
					if (!(m->type->kind == TYPEPOINTER || m->type->prop & PROPINT && !(m->type->prop & PROPSOFT)) ||
					    m->type->size != t->u.structunion.members->type->size || m->bits.before || m->bits.after)
						error(&tok.loc, "transparent_union member '%s' is not a pointer or an integer of the first member's size", m->name);
				nt = xmalloc(sizeof *nt);
				*nt = *t;
				nt->u.structunion.transparent = true;
				t = nt;
			}
			if (!prior)
				scopeputdecl(s, mkdecl(name, DECLTYPE, t, tq, LINKNONE));
			else if (!typesame(prior->type, t) || prior->qual != tq)
				error(&tok.loc, "typedef '%s' redefined with different type", name);
			break;
		case DECLOBJECT:
			/* _Alignas cannot weaken the type's alignment (6.7.5p4); GNU aligned on an object is its alignment
			 * even below the type's, as gcc lays it out (the kernel's DEFINE_PER_CPU_PAGE_ALIGNED, 4096, of the
			 * 16 KiB-aligned struct irq_stack) */
			if (align && align < t->align && alignasseen)
				error(&tok.loc, "object '%s' requires alignment %d, which is stricter than specified alignment %d", name, t->align, align);
			d = declcommon(s, kind, name, asmname, t, tq, sc, prior);
			declapplyattr(d);
			d->regvar = regname;   /* a block-scope register variable: asm operands take it in this register */
			if (d->u.obj.align < align || align && align < t->align)
				d->u.obj.align = align;
			d->u.obj.cleanup = declcleanup;
			if (declcleanup && gnucleanup) {
				struct decl *cf = scopegetdecl(s, declcleanup, true);

				if (!cf || cf->kind != DECLFUNC)
					error(&tok.loc, "cleanup function '%s' is not a declared function", declcleanup);
				if (s->stmtexpr)
					error(&tok.loc, "an object with a cleanup attribute directly in a statement expression is not supported");
				d->u.obj.cleanupfn = cf;
			}
			declcleanup = NULL;
			if (d->u.obj.cleanup && s == &filescope)
				error(&tok.loc, "cleanup attribute on '%s', which is not a block-scope object", name);
			if (d->linkage == LINKNONE && !(sc & SCSTATIC)) {
				d->u.obj.storage = SDAUTO;
			} else {
				d->u.obj.storage = sc & SCTHREADLOCAL ? SDTHREAD : SDSTATIC;
				if (t->prop & PROPVM)
					error(&tok.loc, "object '%s' with %s storage duration cannot have variably modified type", name, d->u.obj.storage == SDSTATIC ? "static" : "thread");
				d->value = mkglobal(d);
			}

			if (base.expr)
				funcexpr(f, base.expr);
			init = NULL;
			hasinit = false;
			if (d->alias && !d->defined) {   /* GNU alias on an object: this declaration defines the name */
				if (tok.kind == TASSIGN)
					error(&tok.loc, "an alias '%s' cannot have an initializer", name);
				emitalias(d);
				d->defined = true;
				break;
			}
			if (consume(TASSIGN)) {
				if (f && d->linkage != LINKNONE)
					error(&tok.loc, "object '%s' with block scope and %s linkage cannot have initializer", name, d->linkage == LINKEXTERN ? "external" : "internal");
				if (d->defined)
					error(&tok.loc, "object '%s' redefined", name);
				/* an automatic object has its storage before its initializer is parsed: a statement expression in it
				 * is lowered as it is parsed, and may take the object's address (the kernel's
				 * COMPLETION_INITIALIZER_ONSTACK(fwork.done) in the initializer of fwork) */
				if (f && d->u.obj.storage == SDAUTO && !d->type->incomplete && !(d->type->prop & PROPVM))
					funcalloc(f, d);
				init = parseinit(s, d->type);
				if (initfamsize) {
					if (d->u.obj.storage != SDSTATIC)
						error(&tok.loc, "non-static initialization of a flexible array member");
					d->u.obj.famsize = initfamsize;
				}
				hasinit = true;
			} else if (sc & SCEXTERN) {
				break;
			} else if (d->linkage != LINKNONE && (d->u.obj.storage == SDSTATIC || d->u.obj.storage == SDTHREAD)) {
				/* a tentative definition, thread storage too (6.9.2): EDG declares a thread_local of the file before
				 * its definition with the initializer */
				if (!d->defined && !d->tentative) {
					d->tentative = true;
					*tentativedefnsend = d;
					tentativedefnsend = &d->next;
				}
				break;
			}
			defineobj(d, init, hasinit, f);
			break;
		case DECLFUNC:
			/* GNU aligned on a function (the kernel's __function_aligned, CONFIG_FUNCTION_ALIGNMENT=16): QBE starts
			 * every x86-64 function on a 16-byte boundary, so up to 16 it already holds; above, it would not */
			if (align && (align > 16 || strcmp(targ->name, "x86_64-sysv") != 0))
				error(&tok.loc, "function '%s' declared with alignment specifier", name);
			if (f && sc && sc != SCEXTERN)  /* 6.7.1p7 */
				error(&tok.loc, "function '%s' with block scope may only have storage class 'extern'", name);
			d = declcommon(s, kind, name, asmname, t, tq, sc, prior);
			declapplyattr(d);
			d->value = mkglobal(d);
			if (declattr.gnuinline)
				d->u.func.gnuinline = true;
			/* GNU gnu_inline (the kernel's inline): plain inline defines the external symbol, the reverse of C99 */
			d->u.func.inlinedefn = d->linkage == LINKEXTERN && fs & FUNCINLINE && !(sc & SCEXTERN) && !d->u.func.gnuinline &&
				(!prior || prior->u.func.inlinedefn);
			gnuinlineonly = d->linkage == LINKEXTERN && fs & FUNCINLINE && sc & SCEXTERN && d->u.func.gnuinline;
			d->u.func.isnoreturn = fs & FUNCNORETURN || a.kind & ATTRNORETURN;
			if (tok.kind == TLBRACE) {
				if (!allowfunc)
					error(&tok.loc, "function definition not allowed");
				if (d->defined)
					error(&tok.loc, "function '%s' redefined", name);
				/* re-open scope from function declarator */
				assert(funcscope);
				s = funcscope;
				f = mkfunc(d, name, t, s);
				curfunc = f;
				/* an always_inline function's body is recorded for the clones of calls with constant arguments
				 * (funcclone), under cproc -p, where its refusals are deferred */
				if (prune && declattr.alwaysinline && (d->linkage == LINKINTERN || gnuinlineonly) && !curclone) {
					d->u.func.body = xmalloc(sizeof(*d->u.func.body));
					*d->u.func.body = (struct array){0};
					arrayaddbuf(d->u.func.body, &tok, sizeof(tok));
					tokrecord(d->u.func.body);
				}
				stmt(f, s);
				funcgotoflush(f);
				if (d->u.func.body) {
					struct token *k;

					tokrecord(NULL);
					d->u.func.body->len -= sizeof(tok);   /* the token after the body */
					arrayforeach(d->u.func.body, k)
						if (k->kind == TSTATIC)
							d->u.func.hasstatic = true;
				}
				curfunc = NULL;
				if (d->u.func.isnoreturn)
					funchlt(f);
				/* XXX: need to keep track of function in case a later declaration specifies extern */
				if (gnuinlineonly && d->asmname) {
					/* with an asm label: no symbol and no local body; calls go to the external one, as at gcc -O0 */
				} else if (gnuinlineonly) {
					/* extern inline with gnu_inline: no symbol; the body, under a local name, serves the direct
					 * calls that follow (the kernel's extern __always_inline native_save_fl) */
					struct value *ext = d->value;

					d->value = d->u.func.inlinealias = mkinlinealias(d);
					emitfunc(f, false);
					d->value = ext;
				} else if (!d->u.func.inlinedefn) {
					emitfunc(f, d->linkage == LINKEXTERN);
				}
				s = delscope(s);
				delfunc(f);
				d->defined = true;
				return true;
			} else if (funcscope) {
				delscope(funcscope);
			}
			if (d->alias && !d->defined) {   /* GNU alias: this declaration defines the name */
				emitalias(d);
				d->defined = true;
			}
			break;
		}
		if (consume(TSEMICOLON))
			return true;
		expect(TCOMMA, "or ';' after declarator");
		allowfunc = 0;
	}
}

struct decl *
stringdecl(struct expr *expr)
{
	static struct map strings;
	struct mapkey key;
	struct decl *d;
	size_t i;

	if (!strings.len)
		mapinit(&strings, 64);
	assert(expr->kind == EXPRSTRING);
	mapkey(&key, expr->u.string.data, expr->u.string.size);
	if (mapput(&strings, &key, &i)) {
		d = mkdecl("string", DECLOBJECT, expr->type, QUALNONE, LINKNONE);
		d->value = mkglobal(d);
		emitdata(d, mkinit(0, expr->type->size, (struct bitfield){0}, expr), NULL);
		strings.vals[i].p = d;
	} else {
		d = strings.vals[i].p;
	}
	return d;
}

void
emittentativedefns(void)
{
	struct decl *d;

	for (d = tentativedefns; d; d = d->next) {
		if (!d->defined)
			defineobj(d, NULL, false, NULL);
	}
}

/*
A clone of an always_inline function for a call with integer constant arguments: gcc inlines such a function, and an
asm operand in it that must be an immediate ("i"(1 << (bit & 7)) in the kernel's _static_cpu_has) is constant only in
the inlined copy. cproc does not inline, so for a function in which it refused something (decl->u.func.refused, a
refusal deferred under -p) its recorded body is parsed again as a local function NAME.constN in which each parameter
given a constant is that constant (an enumeration-like constant of the parameter's type), with the semantics of the
inlined copy. The call goes to the clone. A body that does not compile so (the parameter assigned or its address
taken) keeps the call on the function; a body with a static local is not cloned (gcc's inlined copies share it).
*/
struct funcclone {
	unsigned n;
	bool isconst[16];
	unsigned long long val[16];
	struct decl *decl;
	struct funcclone *next;
};

struct decl *
funcclone(struct decl *d, struct expr *args)
{
	static unsigned id;
	struct type *t = d->type, *t2;
	struct decl *p, *q, **pend, *k, *c;
	struct expr *a;
	struct funcclone key = {0}, *cl;
	struct scope *s;
	struct func *f;
	struct token savedtok;
	struct func *savedfunc;
	bool savedclone;
	struct tokreplay savedreplay;
	jmp_buf jb, *savedjmp;
	char *name;
	unsigned i, nconst = 0;

	if (!d->u.func.body || d->u.func.hasstatic || !d->u.func.refused || t->u.func.isvararg || !asmout)
		return NULL;
	for (p = t->u.func.params, a = args; p && a; p = p->next, a = a->next, ++key.n) {
		struct expr *e;

		if (key.n == 16)
			return NULL;
		e = eval(a);
		if (e->kind == EXPRCONST && e->type->prop & PROPINT && !(e->type->prop & PROPSOFT) && p->type->prop & PROPINT &&
		    p->type->kind != TYPEBOOL && !(p->type->prop & PROPSOFT)) {
			key.isconst[key.n] = true;
			key.val[key.n] = e->u.constant.u;
			++nconst;
		}
	}
	if (!nconst)
		return NULL;
	for (cl = d->u.func.clones; cl; cl = cl->next)
		if (cl->n == key.n && memcmp(cl->isconst, key.isconst, sizeof key.isconst) == 0 &&
		    memcmp(cl->val, key.val, sizeof key.val) == 0)
			return cl->decl;

	/* the clone's type: the function's, with parameters of its own */
	t2 = mktype(TYPEFUNC, 0);
	*t2 = *t;
	t2->u.func.params = NULL;
	pend = &t2->u.func.params;
	s = mkscope(&filescope);
	for (p = t->u.func.params, i = 0; p; p = p->next, ++i) {
		q = mkdecl(p->name, DECLOBJECT, p->type, p->qual, LINKNONE);
		q->u.obj.storage = SDAUTO;
		*pend = q;
		pend = &q->next;
		if (!p->name)
			continue;
		if (i < key.n && key.isconst[i]) {
			k = mkdecl(p->name, DECLCONST, p->type, QUALNONE, LINKNONE);
			k->u.enumconst = key.val[i];
			k->value = mkintconst(key.val[i]);
			scopeputdecl(s, k);
		} else {
			scopeputdecl(s, q);
		}
	}
	name = xmalloc(strlen(d->name) + 24);
	sprintf(name, "%s.const%u", d->name, ++id);
	c = mkdecl(name, DECLFUNC, t2, QUALNONE, LINKINTERN);
	c->value = mkglobal(c);
	c->section = d->section;
	c->u.func.isnoreturn = d->u.func.isnoreturn;
	cl = xmalloc(sizeof(*cl));
	*cl = key;
	cl->decl = c;
	cl->next = d->u.func.clones;
	d->u.func.clones = cl;   /* before the body, for a call in it with the same constants */

	savedtok = tok;
	savedfunc = curfunc;
	savedclone = curclone;
	savedjmp = errorjmp;
	tokreplay(&savedreplay, d->u.func.body->val, d->u.func.body->len / sizeof(struct token));
	next();
	if (setjmp(jb)) {   /* it does not compile with constants: the call stays on the function */
		errorjmp = savedjmp;
		curfunc = savedfunc;
		curclone = savedclone;
		tokreplayend(&savedreplay);
		tok = savedtok;
		d->u.func.clones = cl->next;
		return NULL;
	}
	errorjmp = &jb;
	curclone = true;
	f = mkfunc(c, name, t2, s);
	curfunc = f;
	stmt(f, s);
	funcgotoflush(f);
	if (c->u.func.isnoreturn)
		funchlt(f);
	errorjmp = savedjmp;
	curfunc = savedfunc;
	curclone = savedclone;
	tokreplayend(&savedreplay);
	tok = savedtok;
	emitfunc(f, false);
	delfunc(f);
	return c;
}
