#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "utf.h"
#include "cc.h"

static struct expr *parenexpr(struct scope *);

static struct expr *
mkexpr(enum exprkind k, struct type *t, struct expr *b)
{
	struct expr *e;

	e = xmalloc(sizeof(*e));
	e->loc = tok.loc;
	e->qual = QUALNONE;
	e->type = t;
	e->lvalue = false;
	e->decayed = false;
	e->kind = k;
	e->base = b;
	e->next = NULL;
	e->toeval = NULL;

	return e;
}

void
delexpr(struct expr *e)
{
	struct expr *sub;

	switch (e->kind) {
	case EXPRCALL:
		delexpr(e->base);
		while (sub = e->u.call.args) {
			e->u.call.args = sub->next;
			delexpr(sub);
		}
		break;
	case EXPRBITFIELD:
	case EXPRINCDEC:
	case EXPRUNARY:
	case EXPRCAST:
		delexpr(e->base);
		break;
	case EXPRBINARY:
		delexpr(e->u.binary.l);
		delexpr(e->u.binary.r);
		break;
	case EXPRCOND:
		delexpr(e->base);
		if (e->u.cond.t != e->base)
			delexpr(e->u.cond.t);
		delexpr(e->u.cond.f);
		break;
	/*
	XXX: compound assignment causes some reuse of expressions,
	so we can't free them without risk of a double-free

	case EXPRASSIGN:
		delexpr(e->assign.l);
		delexpr(e->assign.r);
		break;
	*/
	case EXPRCOMMA:
		while (sub = e->base) {
			e->base = sub->next;
			delexpr(sub);
		}
		break;
	}
	free(e);
}

static struct expr *
mkconstexpr(struct type *t, unsigned long long n)
{
	struct expr *e;

	e = mkexpr(EXPRCONST, t, NULL);
	e->u.constant.u = n;
	if (t->kind == TYPEINT128) {
		/* the 128-bit image: n sign-extended (the constants are ints, and ~x is x ^ -1) */
		e->u.constant.soft[0] = n;
		e->u.constant.soft[1] = (long long)n < 0 ? ~0ull : 0;
	}

	return e;
}

static struct expr *mkunaryexpr(enum tokenkind, struct expr *);
static struct expr *mkassignexpr(struct expr *, struct expr *);

/* 6.3.2.1 Conversion of arrays and function designators */
static struct expr *
decay(struct expr *e)
{
	struct type *t;
	enum typequal tq;

	/* XXX: combine with decl.c:adjust in some way? */
	t = e->type;
	tq = e->qual;
	switch (t->kind) {
	case TYPEARRAY:
		/*
		XXX: qualifiers should be applied to the element
		type of array types, not the array type itself

		assert(tq == QUALNONE);
		*/
		e = mkunaryexpr(TBAND, e);
		e->type = mkpointertype(t->base, t->qual | tq);
		e->decayed = true;
		break;
	case TYPEFUNC:
		e = mkunaryexpr(TBAND, e);
		e->decayed = true;
		break;
	}

	return e;
}

static struct expr *
mkunaryexpr(enum tokenkind op, struct expr *base)
{
	struct expr *expr;
	struct type *type;

	switch (op) {
	case TBAND:
		if (base->decayed) {
			expr = base;
			base = base->base;
			free(expr);
		}
		/*
		Allow struct and union types even if they are not lvalues,
		since we take their address when compiling member access.
		*/
		if (!base->lvalue && base->type->kind != TYPEFUNC && base->type->kind != TYPESTRUCT && base->type->kind != TYPEUNION)
			error(&tok.loc, "'&' operand is not an lvalue or function designator");
		if (base->kind == EXPRBITFIELD)
			error(&tok.loc, "cannot take address of bit-field");
		expr = mkexpr(EXPRUNARY, mkpointertype(base->type, base->qual), base);
		expr->op = op;
		return expr;
	case TMUL:
		if (base->type->kind != TYPEPOINTER)
			error(&tok.loc, "cannot dereference non-pointer");
		if (base->kind == EXPRUNARY && base->op == TBAND && base->base->kind != EXPRSTRING) {
			type = base->type->base;
			expr = base->base;
			expr->type = type;
		} else {
			expr = mkexpr(EXPRUNARY, base->type->base, base);
			expr->qual = base->type->qual;
			expr->lvalue = true;
			expr->op = op;
		}
		return decay(expr);
	}
	/* other unary operators get compiled as equivalent binary ones */
	fatal("internal error: unknown unary operator %d", op);
	return NULL;
}

static unsigned
bitfieldwidth(struct expr *e)
{
	if (e->kind != EXPRBITFIELD)
		return -1;
	return e->type->size * 8 - e->u.bitfield.bits.before - e->u.bitfield.bits.after;
}

static struct expr *
exprconvert(struct expr *e, struct type *t)
{
	if (typecompatible(e->type, t))
		return e;
	return mkexpr(EXPRCAST, t, e);
}

/* whether evaluating e can have an effect beyond its value (a call, a store, a volatile access, a statement) */
static bool
nosideeffects(struct expr *e)
{
	struct expr *a;

	if (e->qual & QUALVOLATILE)
		return false;
	switch (e->kind) {
	case EXPRIDENT:
	case EXPRCONST:
	case EXPRSTRING:
	case EXPRSIZEOF:
		return !e->base || nosideeffects(e->base);
	case EXPRUNARY:
	case EXPRCAST:
	case EXPRBITFIELD:
		if (e->kind == EXPRUNARY && e->op == TMUL && e->base->type->kind == TYPEPOINTER &&
		    e->base->type->base->qual & QUALVOLATILE)
			return false;
		return nosideeffects(e->base);
	case EXPRBINARY:
		return nosideeffects(e->u.binary.l) && nosideeffects(e->u.binary.r);
	case EXPRCOND:
		return nosideeffects(e->base) && nosideeffects(e->u.cond.t) && nosideeffects(e->u.cond.f);
	case EXPRCOMMA:
		for (a = e->base; a; a = a->next)
			if (!nosideeffects(a))
				return false;
		return true;
	default:
		return false;
	}
}

static bool
nullpointer(struct expr *e)
{
	if (e->kind != EXPRCONST)
		return false;
	if (e->type->kind == TYPENULLPTR)
		return true;
	if (!(e->type->prop & PROPINT) && (e->type->kind != TYPEPOINTER || e->type->base != &typevoid))
		return false;
	return e->u.constant.u == 0;
}

/* Qualifiers of the object a pointer points to. An array's qualifiers are those of its elements (decl.c qualarray),
   so for a pointer to an array they are on the array type, not on the pointer. */
static enum typequal
pointeequal(struct type *p)
{
	if (p->base->kind == TYPEARRAY)
		return p->qual | p->base->qual;
	return p->qual;
}

/* 6.5.16.1 for the pointed-to types: compatible apart from qualifiers, which pointeequal checks. */
static bool
pointeecompatible(struct type *t, struct type *et)
{
	struct type a, b;

	/*
	integer pointees that differ only in signedness (unsigned char * and const char *, the kernel's unsigned int *
	for int *) are accepted, as gcc accepts them with -Wpointer-sign, a warning in C that is on by default in gcc's
	C modes (the kernel turns it off). The qualifiers are checked by the caller.
	*/
	if (t->kind == et->kind && t->prop & PROPINT && et->prop & PROPINT && t->kind != TYPEENUM && t->kind != TYPEBOOL &&
	    t->size == et->size)
		return true;
	if (t->kind != TYPEARRAY || et->kind != TYPEARRAY)
		return typecompatible(t, et);
	a = *t;
	b = *et;
	a.qual = QUALNONE;
	b.qual = QUALNONE;
	return typecompatible(&a, &b);
}

struct expr *
exprassign(struct expr *e, struct type *t)
{
	struct type *et;

	et = e->type;
	switch (t->kind) {
	case TYPEBOOL:
		if (!(et->prop & PROPARITH) && et->kind != TYPEPOINTER && et->kind != TYPENULLPTR)
			error(&tok.loc, "assignment to bool must be from arithmetic, pointer, or nullptr_t type");
		break;
	case TYPEPOINTER:
		if (nullpointer(e))
			break;
		if (et->kind != TYPEPOINTER)
			error(&tok.loc, "assignment to pointer must be from pointer or null pointer constant");
		if (t->base != &typevoid && et->base != &typevoid && !pointeecompatible(t->base, et->base))
			error(&tok.loc, "base types of pointer assignment must be compatible or void");
		if (pointeequal(et) & ~pointeequal(t))
			error(&tok.loc, "assignment to pointer discards qualifiers");
		break;
	case TYPENULLPTR:
		if (!nullpointer(e))
			error(&tok.loc, "assignment to nullptr_t must be from null pointer constant or expression with type nullptr_t");
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		if (!typecompatible(t, et))
			error(&tok.loc, "assignment to %s type must be from compatible type", t->kind == TYPEUNION ? "union" : "struct");
		break;
	default:
		assert(t->prop & PROPARITH);
		if (!(et->prop & PROPARITH))
			error(&tok.loc, "assignment to arithmetic type must be from arithmetic type");
		break;
	}
	return exprconvert(e, t);
}

/*
An argument for a parameter of a GNU transparent_union type: an argument of a member's type converts to that member and
is passed as the first member is (gcc's convention for such a parameter, qbe.c abiparam); the union itself passes its
first member.
*/
static struct expr *
transparentarg(struct expr *e, struct type *t)
{
	struct member *m, *first = t->u.structunion.members;
	struct type *et = e->type;

	if (typecompatible(t, et)) {
		if (!e->lvalue)
			error(&tok.loc, "a transparent union argument that is not an lvalue is not supported");
		return mkunaryexpr(TMUL, exprconvert(mkunaryexpr(TBAND, e), mkpointertype(first->type, QUALNONE)));
	}
	for (m = t->u.structunion.members; m; m = m->next) {
		struct type *mt = m->type;

		if (mt->kind == TYPEPOINTER ? nullpointer(e) || et->kind == TYPEPOINTER &&
		    (mt->base == &typevoid || et->base == &typevoid || pointeecompatible(mt->base, et->base)) &&
		    !(pointeequal(et) & ~pointeequal(mt)) : typecompatible(mt, et))
			return exprconvert(exprassign(e, mt), first->type);
	}
	error(&tok.loc, "argument type matches no member of the transparent union");
	return NULL;
}

struct expr *
exprpromote(struct expr *e)
{
	struct type *t;

	t = typepromote(e->type, bitfieldwidth(e));
	return exprconvert(e, t);
}

static struct type *
commonreal(struct expr **e1, struct expr **e2)
{
	struct type *t;

	t = typecommonreal((*e1)->type, bitfieldwidth(*e1), (*e2)->type, bitfieldwidth(*e2));
	*e1 = exprconvert(*e1, t);
	*e2 = exprconvert(*e2, t);

	return t;
}

static struct expr *
mksizeofexpr(struct type *t) {
	struct expr *e;

	if (t->kind == TYPEARRAY && t->size == 0 && t->prop & PROPVM) {   /* a GNU int a[0] has the constant size 0 */
		e = mkexpr(EXPRSIZEOF, &typeulong, NULL);
		e->u.szof.type = t;
	} else {
		e = mkconstexpr(&typeulong, t->size);
	}

	return e;
}

/* the element size of pointer arithmetic: GNU C counts void and function types as size 1 */
static struct expr *
ptrscale(struct location *loc, struct type *base, const char *op)
{
	if (base->kind == TYPEVOID || base->kind == TYPEFUNC)
		return mkconstexpr(&typeulong, 1);
	if (base->incomplete)
		error(loc, "pointer operand to '%s' must be to complete object type", op);
	return mksizeofexpr(base);
}

static struct expr *
mkbinaryexpr(struct location *loc, enum tokenkind op, struct expr *l, struct expr *r)
{
	struct expr *e;
	struct type *t = NULL;
	enum typeprop lp, rp;

	lp = l->type->prop;
	rp = r->type->prop;
	switch (op) {
	case TLOR:
	case TLAND:
		if (!(lp & PROPSCALAR))
			error(loc, "left operand of '%s' operator must be scalar", tokenstr(op));
		if (!(rp & PROPSCALAR))
			error(loc, "right operand of '%s' operator must be scalar", tokenstr(op));
		t = &typeint;
		/* x && 0 is 0 and x || 1 is 1 when evaluating x has no effect, as x & 0 below: the kernel's
		 * dax_mapping() is mapping->host && IS_DAX(mapping->host), with S_DAX 0 */
		if (prune && rp & PROPINT && nosideeffects(l)) {
			e = eval(r);
			if (e->kind == EXPRCONST && (op == TLAND) == (e->u.constant.u == 0))
				return mkconstexpr(t, op == TLOR);
		}
		break;
	case TEQL:
	case TNEQ:
		t = &typeint;
		if (lp & PROPARITH && rp & PROPARITH) {
			commonreal(&l, &r);
			break;
		}
		if (l->type->kind != TYPEPOINTER)
			e = l, l = r, r = e;
		if (l->type->kind != TYPEPOINTER)
			error(loc, "invalid operands to '%s' operator", tokenstr(op));
		if (nullpointer(eval(r))) {
			r = exprconvert(r, l->type);
			break;
		}
		if (nullpointer(eval(l))) {
			l = exprconvert(l, r->type);
			break;
		}
		if (r->type->kind != TYPEPOINTER)
			error(loc, "invalid operands to '%s' operator", tokenstr(op));
		if (l->type->base->kind == TYPEVOID)
			e = l, l = r, r = e;
		/* GNU: pointers to distinct types, or void * and a function pointer (the kernel's handler == SIG_IGN),
		 * compare as addresses (gcc warns, without -pedantic only for distinct object pointer types) */
		if (r->type->base->kind == TYPEVOID || !typecompatible(l->type->base, r->type->base))
			r = exprconvert(r, l->type);
		break;
	case TLESS:
	case TGREATER:
	case TLEQ:
	case TGEQ:
		t = &typeint;
		if (lp & PROPREAL && rp & PROPREAL) {
			commonreal(&l, &r);
		} else if (l->type->kind == TYPEPOINTER && r->type->kind == TYPEPOINTER) {
			if (!typecompatible(l->type->base, r->type->base) || l->type->base->kind == TYPEFUNC)
				error(loc, "pointer operands to '%s' operator must be to compatible object types", tokenstr(op));
		} else {
			error(loc, "invalid operands to '%s' operator", tokenstr(op));
		}
		break;
	case TBOR:
	case TXOR:
	case TBAND:
		t = commonreal(&l, &r);
		/*
		x & 0 is 0 when evaluating x has no effect, as gcc folds it: the kernel's configuration masks (S_DAX,
		ARCH_PAGE_TABLE_SYNC_MASK) are 0 when a feature is off, and the code they guard calls functions that
		configuration does not define. Under -p only, the kernel mode, as the calls above.
		*/
		if (prune && op == TBAND && t->prop & PROPINT) {
			e = eval(r);
			if (e->kind == EXPRCONST && e->u.constant.u == 0 && nosideeffects(l))
				return mkconstexpr(t, 0);
			e = eval(l);
			if (e->kind == EXPRCONST && e->u.constant.u == 0 && nosideeffects(r))
				return mkconstexpr(t, 0);
		}
		break;
	case TADD:
		if (lp & PROPARITH && rp & PROPARITH) {
			t = commonreal(&l, &r);
			break;
		}
		if (r->type->kind == TYPEPOINTER)
			e = l, l = r, r = e, rp = lp;
		if (l->type->kind != TYPEPOINTER || !(rp & PROPINT))
			error(loc, "invalid operands to '+' operator");
		t = l->type;
		r = mkbinaryexpr(loc, TMUL, exprconvert(r, &typeulong), ptrscale(loc, t->base, "+"));
		break;
	case TSUB:
		if (lp & PROPARITH && rp & PROPARITH) {
			t = commonreal(&l, &r);
			break;
		}
		if (l->type->kind != TYPEPOINTER || !(rp & PROPINT) && r->type->kind != TYPEPOINTER)
			error(loc, "invalid operands to '-' operator");
		if (rp & PROPINT) {
			t = l->type;
			r = mkbinaryexpr(loc, TMUL, exprconvert(r, &typeulong), ptrscale(loc, t->base, "-"));
		} else {
			if (!typecompatible(l->type->base, r->type->base))
				error(&tok.loc, "pointer operands to '-' are to incompatible types");
			op = TDIV;
			t = &typelong;
			e = mkbinaryexpr(loc, TSUB, exprconvert(l, &typelong), exprconvert(r, &typelong));
			r = ptrscale(loc, l->type->base, "-");
			l = e;
		}
		break;
	case TMOD:
		if (!(lp & PROPINT) || !(rp & PROPINT))
			error(loc, "operands to '%%' operator must be integer");
		t = commonreal(&l, &r);
		break;
	case TMUL:
	case TDIV:
		if (!(lp & PROPARITH) || !(rp & PROPARITH))
			error(loc, "operands to '%s' operator must be arithmetic", tokenstr(op));
		t = commonreal(&l, &r);
		break;
	case TSHL:
	case TSHR:
		if (!(lp & PROPINT) || !(rp & PROPINT))
			error(loc, "operands to '%s' operator must be integer", tokenstr(op));
		l = exprpromote(l);
		r = exprpromote(r);
		t = l->type;
		break;
	default:
		fatal("internal error: unknown binary operator %d", op);
	}
	e = mkexpr(EXPRBINARY, t, NULL);
	e->op = op;
	e->u.binary.l = l;
	e->u.binary.r = r;

	return e;
}

static struct type *
inttype(unsigned long long val, bool decimal, char *suffix)
{
	enum {
		U = 1,
		L = 2,
		LL = 4,
		WB = 8,
	};
	static struct type *const types[] = {
		&typeint,
		&typeuint,   /* u */
		&typelong,   /* l */
		&typeulong,  /* ul */
		&typellong,  /* ll */
		&typeullong, /* ull */
	};
	int flags, i, step;
	bool sign;
	char *s;
	struct type *t;

	/* parse suffix */
	flags = 0;
	for (s = suffix; *s; ++s) {
		int new;

		switch (*s) {
		case 'u':
		case 'U': new = U; break;
		case 'l':
		case 'L': new = s[1] == s[0] ? (++s, LL) : L; break;
		case 'w': if (s[1] != 'b') goto invalid; ++s, new = WB; break;
		case 'W': if (s[1] != 'B') goto invalid; ++s, new = WB; break;
		default:
		invalid: error(&tok.loc, "invalid integer constant suffix '%s'", suffix);
		}
		if (flags & new || flags & ~U && new & ~U)
			goto invalid;
		flags |= new;
	}

	/* find integer type */
	sign = !(flags & U);
	if (flags & WB) {
		for (i = 1;; ++i) {
			if (i > 64 - sign)
				goto notype;
			if (val <= 0xffffffffffffffff >> 64 - i)
				break;
		}
		return mkbitinttype(i + sign, sign);
	}
	assert(flags < countof(types));
	step = !sign || decimal ? 2 : 1;
	for (i = flags; i < countof(types); i += step) {
		t = types[i];
		if (typehasint(t, val, false))
			return t;
	}
	/* gcc: a decimal constant too large for every signed type is unsigned (gcc also warns: "so large that it is unsigned") */
	if (sign && decimal)
		return &typeullong;
notype:
	error(&tok.loc, "no suitable type for constant '%s'", tok.lit);
}

static int
octval(int c)
{
	if ('0' <= c && c <= '7')
		return c - '0';
	return -1;
}

static int
hexval(int c)
{
	if ('0' <= c && c <= '9')
		return c - '0';
	if ('a' <= c && c <= 'f')
		return c - 'a' + 10;
	if ('A' <= c && c <= 'F')
		return c - 'A' + 10;
	return -1;
}

static size_t
decodechar(const char *src, uint_least32_t *chr, bool *hexoct, const char *desc, struct location *loc)
{
	uint_least32_t c;
	size_t n;
	int i, v;
	const unsigned char *s = (const unsigned char *)src;

	*hexoct = false;
	if (*s == '\\') {
		++s;
		switch (*s) {
		case '\'':
		case '"':
		case '?':
		case '\\': c = *s;   ++s; break;
		case 'a':  c = '\a'; ++s; break;
		case 'b':  c = '\b'; ++s; break;
		case 'f':  c = '\f'; ++s; break;
		case 'n':  c = '\n'; ++s; break;
		case 'r':  c = '\r'; ++s; break;
		case 't':  c = '\t'; ++s; break;
		case 'v':  c = '\v'; ++s; break;
		case 'e':  c = 0x1b; ++s; break;   /* GNU: escape (the kernel's string_helpers) */
		case 'x':
			++s;
			c = 0;
			v = hexval(*s);
			assert(v >= 0);
			do {
				if (c > 0xffffffff / 16)
					error(&tok.loc, "character constant escape is out of range");
				c = c * 16 + v;
				v = hexval(*++s);
			} while (v >= 0);
			*hexoct = true;
			break;
		default:
			c = 0;
			v = octval(*s);
			assert(v >= 0);
			i = 0;
			do {
				if (c > 0xffffffff / 8)
					error(&tok.loc, "character constant escape is out of range");
				c = c * 8 + v;
				v = octval(*++s);
			} while (v >= 0 && ++i < 3);
			*hexoct = true;
		}
	} else {
		n = utf8dec(&c, s, 4);
		if (n == (size_t)-1)
			error(loc, "%s contains invalid UTF-8", desc);
		s += n;
	}
	*chr = c;
	return s - (const unsigned char *)src;
}

static size_t
encodechar8(void *dst, uint_least32_t chr, bool hexoct)
{
	if (!hexoct)
		return utf8enc(dst, chr);
	*(unsigned char *)dst = chr;
	return 1;
}

static size_t
encodechar16(void *dst, uint_least32_t chr, bool hexoct)
{
	if (!hexoct)
		return utf16enc(dst, chr) * sizeof(uint_least16_t);
	*(uint_least16_t *)dst = chr;
	return sizeof(uint_least16_t);
}

static size_t
encodechar32(void *dst, uint_least32_t chr, bool hexoct)
{
	*(uint_least32_t *)dst = chr;
	return sizeof(uint_least32_t);
}

struct type *
stringconcat(struct stringlit *str, bool forceutf8)
{
	static struct array parts;
	struct {
		struct location loc;
		char *str;
	} *p;
	int kind, newkind;
	struct type *t;
	size_t (*encodechar)(void *, uint_least32_t, bool);
	char *src;
	unsigned char *buf, *dst;
	uint_least32_t chr;
	bool hexoct;
	size_t len, width;

	assert(tok.kind == TSTRINGLIT);
	parts.len = 0;
	len = 0;
	kind = 0;
	do {
		src = tok.lit;
		switch (*src) {
		case 'u': if (src[1] == '8') ++src; /* fallthrough */
		case 'L':
		case 'U': newkind = *src, ++src; break;
		case '"': newkind = 0; break;
		default: assert(0);
		}
		if (kind != newkind && kind && newkind)
			error(&tok.loc, "adjacent string literals have differing prefixes");
		if (newkind)
			kind = newkind;
		p = arrayadd(&parts, sizeof(*p));
		p->loc = tok.loc;
		p->str = src + 1;
		len += strlen(src) - 2;
		next();
	} while (tok.kind == TSTRINGLIT);
	if (forceutf8)
		kind = '8';
	++len;  /* null byte */
	switch (kind) {
	case 0: t = &typechar; break;
	case '8': t = &typeuchar; break;
	case 'u': t = &typeushort; break;
	case 'U': t = &typeuint; break;
	case 'L': t = (shortwchar ? &typeushort : targ->typewchar); break;
	default: assert(0);
	}
	switch (t->size) {
	case 1:
		width = 1;
		encodechar = encodechar8;
		break;
	case 2:
		width = sizeof(uint_least16_t);
		encodechar = encodechar16;
		break;
	case 4:
		width = sizeof(uint_least32_t);
		encodechar = encodechar32;
		break;
	default:
		assert(0);
	}
	buf = xreallocarray(NULL, len, width);
	str->data = buf;
	dst = buf;
	arrayforeach(&parts, p) {
		src = p->str;
		while (*src != '"') {
			src += decodechar(src, &chr, &hexoct, "string literal", &p->loc);
			dst += encodechar(dst, chr, hexoct);
		}
	}
	dst += encodechar(dst, 0, false);
	str->size = (dst - buf) / width;
	return t;
}

static struct expr *
generic(struct scope *s)
{
	struct expr *e, *match = NULL, *def = NULL;
	struct type *t, *want;
	enum typequal qual;

	next();
	expect(TLPAREN, "after '_Generic'");
	e = assignexpr(s);
	expect(TCOMMA, "after generic selector expression");
	want = e->type;
	delexpr(e);
	do {
		if (consume(TDEFAULT)) {
			if (def)
				error(&tok.loc, "multiple default expressions in generic association list");
			expect(TCOLON, "after 'default'");
			def = assignexpr(s);
		} else {
			qual = QUALNONE;
			t = typename(s, &qual, NULL);
			if (!t)
				error(&tok.loc, "expected typename for generic association");
			if (t->kind == TYPEFUNC)
				error(&tok.loc, "generic association must have object type");
			if (t->incomplete)
				error(&tok.loc, "generic association must have complete type");
			if (t->prop & PROPVM)
				error(&tok.loc, "generic association has variably modified type");
			expect(TCOLON, "after type name");
			e = assignexpr(s);
			if (typecompatible(t, want) && qual == QUALNONE) {
				if (match)
					error(&tok.loc, "generic selector matches multiple associations");
				match = e;
			} else {
				delexpr(e);
			}
		}
	} while (consume(TCOMMA));
	expect(TRPAREN, "after generic assocation list");
	if (!match) {
		if (!def)
			error(&tok.loc, "generic selector matches no associations and no default was specified");
		match = def;
	} else if (def) {
		delexpr(def);
	}
	return match;
}

/* 6.5 Expressions */
static struct expr *
primaryexpr(struct scope *s)
{
	struct expr *e;
	struct decl *d;
	struct type *t;
	char *src, *end;
	uint_least32_t chr;
	unsigned long long val;
	bool hexoct, ordinary;
	int base;

	switch (tok.kind) {
	case TSTRINGLIT:
		e = mkexpr(EXPRSTRING, NULL, NULL);
		t = stringconcat(&e->u.string, false);
		e->type = mkarraytype(t, QUALNONE, e->u.string.size);
		e->lvalue = true;
		e = decay(e);
		break;
	case TCHARCONST:
		src = tok.lit;
		ordinary = false;
		switch (*src) {
		case 'L': ++src; t = (shortwchar ? &typeushort : targ->typewchar); break;
		case 'u': ++src; t = *src == '8' ? ++src, &typeuchar : &typeushort; break;
		case 'U': ++src; t = &typeuint; break;
		default: t = &typeuchar, ordinary = true;
		}
		assert(*src == '\'');
		++src;
		src += decodechar(src, &chr, &hexoct, "character constant", &tok.loc);
		if (hexoct && !typehasint(t, chr, false))
			error(&tok.loc, "character constant escape is out of range");
		val = chr;
		if (ordinary) {
			if (typechar.u.arith.issigned)
				val = (val ^ 0x80) - 0x80;
			t = &typeint;
		}
		e = mkconstexpr(t, val);
		if (*src != '\'')
			error(&tok.loc, "character constant contains more than one character: %c", *src);
		next();
		break;
	case TNUMBER:
		e = mkexpr(EXPRCONST, NULL, NULL);
		if (tok.lit[0] == '0') {
			switch (tok.lit[1]) {
			case 'x': case 'X': base = 16; break;
			case 'b': case 'B': base = 2; break;
			default: base = 8; break;
			}
		} else {
			base = 10;
		}
		if (strpbrk(tok.lit, base == 16 ? ".pP" : ".eE")) {
			/* floating constant */
			e->u.constant.f = strtod(tok.lit, &end);
			if (end == tok.lit)
				error(&tok.loc, "invalid floating constant '%s'", tok.lit);
			if (!end[0])
				e->type = &typedouble;
			else if ((end[0] == 'f' || end[0] == 'F') && !end[1])
				e->type = &typefloat;
			else if ((end[0] == 'l' || end[0] == 'L') && !end[1])
				e->type = &typeldouble;
			else if ((end[0] == 'q' || end[0] == 'Q') && !end[1])
				e->type = &typefloat128;
			else
				error(&tok.loc, "invalid floating constant suffix '%s'", end);
			if (e->type == &typefloat128)
				softliteral(e->u.constant.soft, tok.lit);
#ifndef typeldouble
			else if (e->type == &typeldouble)
				softimage(e->u.constant.soft, e->type, strtold(tok.lit, NULL));
#endif
		} else {
			src = tok.lit;
			if (base == 2)
				src += 2;
			/* integer constant */
			e->u.constant.u = strtoull(src, &end, base);
			if (end == src)
				error(&tok.loc, "invalid integer constant '%s'", tok.lit);
			e->type = inttype(e->u.constant.u, base == 10, end);
		}
		next();
		break;
	case TTRUE:
	case TFALSE:
		if (!stdc23)
			goto identref;   /* before C23, true/false are ordinary identifiers (macros or enum constants) */
		e = mkexpr(EXPRCONST, &typebool, NULL);
		e->u.constant.u = tok.kind == TTRUE;
		next();
		break;
	case TNULLPTR:
		if (!stdc23)
			goto identref;
		e = mkexpr(EXPRCONST, &typenullptr, NULL);
		e->u.constant.u = 0;
		next();
		break;
	case TLPAREN:
		next();
		e = parenexpr(s);
		expect(TRPAREN, "after expression");
		break;
	case T_GENERIC:
		e = generic(s);
		break;
	default:
	identref:
		if (iscident(tok.kind)) {
			d = scopegetdecl(s, tokenstr(tok.kind), 1);
			if (!d)
				error(&tok.loc, "undeclared identifier: %s", tokenstr(tok.kind));
			if (d->addrof) {   /* a funcclone's pointer parameter: the address of the object it was called with */
				struct expr *g = mkexpr(EXPRIDENT, d->addrof->type, NULL);

				g->qual = d->addrof->qual;
				g->lvalue = true;
				g->u.ident.decl = d->addrof;
				e = exprconvert(mkunaryexpr(TBAND, g), d->type);
				next();
				break;
			}
			e = mkexpr(EXPRIDENT, d->type, NULL);
			e->qual = d->qual;
			e->lvalue = d->kind == DECLOBJECT;
			e->u.ident.decl = d;
			if (d->kind != DECLBUILTIN)
				e = decay(e);
			next();
			break;
		}
		error(&tok.loc, "expected primary expression");
	}

	return e;
}

/* TODO: merge with init.c:designator() */
/* the member designators of __builtin_offsetof; GNU allows an index that is not constant (the kernel's
 * container_of(node, struct latch_tree_node, node[idx])), whose scaled sum goes to *runtime (null if there is none) */
static void
designator(struct scope *s, struct type *t, unsigned long long *offset, struct expr **runtime)
{
	char *name;
	struct member *m;
	struct expr *i, *c;

	for (;;) {
		switch (tok.kind) {
		case TLBRACK:
			if (t->kind != TYPEARRAY)
				error(&tok.loc, "index designator is only valid for array types");
			next();
			i = expr(s);
			if (!(i->type->prop & PROPINT))
				error(&tok.loc, "index designator is not an integer");
			expect(TRBRACK, "for index designator");
			t = t->base;
			c = eval(i);
			if (c->kind == EXPRCONST) {
				*offset += c->u.constant.u * t->size;
			} else {
				i = mkbinaryexpr(&tok.loc, TMUL, exprconvert(i, &typeulong), mkconstexpr(&typeulong, t->size));
				*runtime = *runtime ? mkbinaryexpr(&tok.loc, TADD, *runtime, i) : i;
			}
			break;
		case TPERIOD:
			if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
				error(&tok.loc, "member designator only valid for struct/union types");
			next();
			name = expect(TIDENT, "for member designator");
			m = typemember(t, name, offset);
			if (!m)
				error(&tok.loc, "%s has no member named '%s'", t->kind == TYPEUNION ? "union" : "struct", name);
			t = m->type;
			break;
		default:
			return;
		}
	}
}

/*
The classification built-ins (C99 7.12) on a real operand x, lowered to comparisons. x is evaluated once into a temporary
(fpvalue, the definition); every reference to the temporary is a new EXPRTEMP node whose base is the definition (fpuse),
so that no node has two parents (delexpr frees each node once) and codegen reads the value the definition holds. A NaN
compares unequal to itself, x - x is NaN for an infinity and 0 for a finite value, and the minimum normal value of each
type is a constant image (fpminnormal).
*/
struct fpbuild {
	struct expr *head;
	struct expr **end;
};

static void
fpadd(struct fpbuild *b, struct expr *e)
{
	*b->end = e;
	b->end = &e->next;
}

static struct expr *
fpvalue(struct fpbuild *b, struct expr *x)
{
	struct expr *def;

	/* long double and __float128 are PROPREAL without PROPFLOAT (type.c): they are operands as they are */
	if (!(x->type->prop & PROPREAL))
		x = exprconvert(x, &typedouble);
	def = mkexpr(EXPRTEMP, x->type, NULL);
	def->lvalue = true;
	def->u.temp = NULL;
	fpadd(b, mkassignexpr(def, x));
	return def;
}

static struct expr *
fpuse(struct expr *def)
{
	return mkexpr(EXPRTEMP, def->type, def);
}

static struct expr *
fpminnormal(struct type *t)
{
	struct expr *e = mkexpr(EXPRCONST, t, NULL);

	switch (t->kind) {
	case TYPEFLOAT:    e->u.constant.f = 0x1p-126; break;
	case TYPEDOUBLE:   e->u.constant.f = 0x1p-1022; break;
	/* 2^-16382: the biased exponent 1, the explicit integer bit 1 (extended) or the implicit bit (binary128) */
	case TYPELDOUBLE:  e->u.constant.soft[0] = 1ull << 63; e->u.constant.soft[1] = 1; break;
	case TYPEFLOAT128: e->u.constant.soft[0] = 0; e->u.constant.soft[1] = 1ull << 48; break;
	default:
		fatal("internal error; no minimum normal value for this type");
	}
	return e;
}

static struct expr *
fpneg(struct expr *e)
{
	struct expr *neg = mkexpr(EXPRUNARY, e->type, e);

	neg->op = TSUB;
	return neg;
}

static struct expr *
fpcond(struct expr *c, struct expr *t, struct expr *f)
{
	struct expr *e = mkexpr(EXPRCOND, &typeint, c);

	e->u.cond.t = t;
	e->u.cond.f = f;
	return e;
}

static struct expr *
fpisfinite(struct expr *def)
{
	struct expr *d = mkbinaryexpr(&tok.loc, TSUB, fpuse(def), fpuse(def));

	return mkbinaryexpr(&tok.loc, TEQL, d, mkconstexpr(&typeint, 0));
}

static struct expr *
fpisinf(struct expr *def)
{
	struct expr *d1 = mkbinaryexpr(&tok.loc, TSUB, fpuse(def), fpuse(def));
	struct expr *d2 = mkbinaryexpr(&tok.loc, TSUB, fpuse(def), fpuse(def));
	struct expr *inf = mkbinaryexpr(&tok.loc, TLAND,
		mkbinaryexpr(&tok.loc, TEQL, fpuse(def), fpuse(def)),
		mkbinaryexpr(&tok.loc, TNEQ, d1, d2));

	/* gcc: nonzero for either infinity (1 for both signs in __builtin_isinf) */
	return fpcond(inf, mkconstexpr(&typeint, 1), mkconstexpr(&typeint, 0));
}

static struct expr *
fpisnormal(struct expr *def)
{
	struct type *t = def->type;
	struct expr *ge = mkbinaryexpr(&tok.loc, TGEQ, fpuse(def), fpminnormal(t));
	struct expr *le = mkbinaryexpr(&tok.loc, TLEQ, fpuse(def), fpneg(fpminnormal(t)));

	return mkbinaryexpr(&tok.loc, TLAND, mkbinaryexpr(&tok.loc, TLOR, ge, le), fpisfinite(def));
}

/* the classification built-in kind on the arguments args (one, two or six of them) */
static struct expr *
fpbuiltin(struct scope *s, enum builtinkind kind)
{
	struct fpbuild b;
	struct expr *ta, *tb, *r, *args[6];
	int i, n = kind == BUILTINFPCLASSIFY ? 6 : kind == BUILTINISUNORDERED || kind == BUILTINISGREATER || kind == BUILTINISLESS
		|| kind == BUILTINISLESSEQUAL || kind == BUILTINISGREATEREQUAL || kind == BUILTINISLESSGREATER ? 2 : 1;

	for (i = 0; i < n; ++i) {
		args[i] = assignexpr(s);
		if (i + 1 < n)
			expect(TCOMMA, "between the arguments of a built-in");
	}
	b.head = NULL;
	b.end = &b.head;
	if (kind == BUILTINFPCLASSIFY) {
		/* fpclassify(nan, inf, normal, subnormal, zero, x) */
		ta = fpvalue(&b, args[5]);
		r = fpcond(mkbinaryexpr(&tok.loc, TNEQ, fpuse(ta), fpuse(ta)), args[0],
		           fpcond(fpisinf(ta), args[1],
		           fpcond(fpisnormal(ta), args[2],
		           fpcond(mkbinaryexpr(&tok.loc, TEQL, fpuse(ta), mkconstexpr(&typeint, 0)), args[4], args[3]))));
	} else if (n == 2) {
		ta = fpvalue(&b, args[0]);
		tb = fpvalue(&b, args[1]);
		switch (kind) {
		case BUILTINISUNORDERED:    r = mkbinaryexpr(&tok.loc, TLOR, mkbinaryexpr(&tok.loc, TNEQ, fpuse(ta), fpuse(ta)), mkbinaryexpr(&tok.loc, TNEQ, fpuse(tb), fpuse(tb))); break;
		case BUILTINISGREATER:      r = mkbinaryexpr(&tok.loc, TGREATER, fpuse(ta), fpuse(tb)); break;
		case BUILTINISGREATEREQUAL: r = mkbinaryexpr(&tok.loc, TGEQ, fpuse(ta), fpuse(tb)); break;
		case BUILTINISLESS:         r = mkbinaryexpr(&tok.loc, TLESS, fpuse(ta), fpuse(tb)); break;
		case BUILTINISLESSEQUAL:    r = mkbinaryexpr(&tok.loc, TLEQ, fpuse(ta), fpuse(tb)); break;
		default:                    r = mkbinaryexpr(&tok.loc, TLOR, mkbinaryexpr(&tok.loc, TLESS, fpuse(ta), fpuse(tb)), mkbinaryexpr(&tok.loc, TGREATER, fpuse(ta), fpuse(tb))); break;
		}
	} else {
		ta = fpvalue(&b, args[0]);
		switch (kind) {
		case BUILTINISNAN:    r = mkbinaryexpr(&tok.loc, TNEQ, fpuse(ta), fpuse(ta)); break;
		case BUILTINISINF:    r = fpisinf(ta); break;
		case BUILTINISFINITE: r = fpisfinite(ta); break;
		default:              r = fpisnormal(ta); break;
		}
	}
	fpadd(&b, r);
	return mkexpr(EXPRCOMMA, &typeint, b.head);
}

/* __c11_atomic_* and the GCC __atomic_*_n / __atomic_fetch_* forms (libc++ calls the first kind from its inline wrappers).
 * The operand size comes from the pointee type, 1, 2, 4 or 8 bytes; qbe.c lowers each call to libatomic's sized
 * function (__atomic_load_8 and so on), which libSystem exports on macOS. The arguments are the pointer, then the
 * values, then the memory order: compare-exchange takes the expected pointer, the desired value and two orders, and
 * the GCC form's weak flag (the fourth argument) is dropped. */
static struct expr *
atomicbuiltin(struct scope *s, enum builtinkind kind)
{
	struct expr *e, *first, *arg, *prev;
	struct type *pointee;
	unsigned n = 0, want;

	first = assignexpr(s);
	if (first->type->kind != TYPEPOINTER)
		error(&tok.loc, "atomic operation needs a pointer");
	pointee = first->type->base;
	if (!(pointee->prop & PROPSCALAR) || (pointee->size != 1 && pointee->size != 2 && pointee->size != 4 && pointee->size != 8))
		error(&tok.loc, "atomic operation on an unsupported type");
	prev = first;
	while (consume(TCOMMA)) {
		arg = assignexpr(s);
		prev->next = arg;
		prev = arg;
		++n;
	}
	switch (kind) {
	case BUILTINC11INIT:
		want = 1;
		break;
	case BUILTINC11LOAD:
		want = 1;
		break;
	case BUILTINC11CAS:
		want = 4;
		break;
	default:
		want = 2;
		break;
	}
	if (kind == BUILTINC11CAS && n == 5) {
		/* the GCC form: drop the weak flag (the third argument after the pointer) */
		struct expr *desired = first->next->next;
		desired->next = desired->next->next;
		n = 4;
	}
	if (n != want)
		error(&tok.loc, "wrong number of arguments to an atomic builtin");
	switch (kind) {
	case BUILTINC11INIT:
	case BUILTINC11STORE:
		e = mkexpr(EXPRBUILTIN, &typevoid, first);
		break;
	case BUILTINC11CAS:
		e = mkexpr(EXPRBUILTIN, &typebool, first);
		break;
	default:
		e = mkexpr(EXPRBUILTIN, pointee, first);
		break;
	}
	e->u.builtin.kind = kind;
	return e;
}

static struct expr *genericatomic(struct scope *, enum builtinkind);

/* __atomic_test_and_set(p, o) and __atomic_clear(p, o) (GCC): the byte at p is exchanged with 1, or stored with 0, with
 * the order o, as the C11 forms on an unsigned char. test_and_set's result is whether the old byte was nonzero. */
static struct expr *
byteatomicbuiltin(struct scope *s, enum builtinkind kind)
{
	struct expr *first, *byte, *value, *order, *e;

	first = assignexpr(s);
	if (first->type->kind != TYPEPOINTER)
		error(&tok.loc, "atomic operation needs a pointer");
	expect(TCOMMA, "after the pointer of an atomic builtin");
	order = assignexpr(s);
	byte = exprconvert(first, mkpointertype(&typeuchar, QUALNONE));
	value = mkconstexpr(&typeuchar, kind == BUILTINATOMICTESTANDSET);
	byte->next = value;
	value->next = order;
	if (kind == BUILTINATOMICTESTANDSET) {
		e = mkexpr(EXPRBUILTIN, &typeuchar, byte);
		e->u.builtin.kind = BUILTINC11XCHG;
		return exprconvert(mkbinaryexpr(&tok.loc, TNEQ, e, mkconstexpr(&typeuchar, 0)), &typebool);
	}
	e = mkexpr(EXPRBUILTIN, &typevoid, byte);
	e->u.builtin.kind = BUILTINC11STORE;
	return e;
}

static struct expr *
builtinfunc(struct scope *s, enum builtinkind kind)
{
	struct expr *e, *toeval;
	struct type *t;
	struct member *m;
	char *name;
	unsigned long long offset;

	switch (kind) {
	case BUILTINALLOCA:
		e = exprassign(assignexpr(s), &typeulong);
		e = mkexpr(EXPRBUILTIN, mkpointertype(&typevoid, QUALNONE), e);
		e->u.builtin.kind = BUILTINALLOCA;
		break;
	case BUILTINFABSF:
		e = exprconvert(assignexpr(s), &typefloat);
		e = mkexpr(EXPRBUILTIN, &typefloat, e);
		e->u.builtin.kind = BUILTINFABSF;
		break;
	case BUILTINISNAN:
	case BUILTINISINF:
	case BUILTINISFINITE:
	case BUILTINISNORMAL:
	case BUILTINISUNORDERED:
	case BUILTINISGREATER:
	case BUILTINISGREATEREQUAL:
	case BUILTINISLESS:
	case BUILTINISLESSEQUAL:
	case BUILTINISLESSGREATER:
	case BUILTINFPCLASSIFY:
		e = fpbuiltin(s, kind);
		break;
	case BUILTINSIGNBIT:
		e = assignexpr(s);
		if (!(e->type->prop & PROPREAL))
			e = exprconvert(e, &typedouble);
		e = mkexpr(EXPRBUILTIN, &typeint, e);
		e->u.builtin.kind = BUILTINSIGNBIT;
		break;
	case BUILTINADDOVERFLOW:
	case BUILTINSUBOVERFLOW:
	case BUILTINMULOVERFLOW: {
		/* GNU __builtin_{add,sub,mul}_overflow(a, b, r): the exact a OP b wrapped into *r, and whether *r could not
		 * hold it (qbe.c funcoverflow). Integer operands and result up to 64 bits; the result not bool or enum. */
		struct expr *a, *b, *r;
		struct type *rt;

		a = assignexpr(s);
		expect(TCOMMA, "after first operand");
		b = assignexpr(s);
		expect(TCOMMA, "after second operand");
		r = assignexpr(s);
		if (!(a->type->prop & PROPINT) || !(b->type->prop & PROPINT) || a->type->size > 8 || b->type->size > 8)
			error(&tok.loc, "operands of an overflow built-in must have integer type of at most 64 bits");
		rt = r->type->kind == TYPEPOINTER ? r->type->base : NULL;
		if (!rt || !(rt->prop & PROPINT) || rt->kind == TYPEBOOL || rt->kind == TYPEENUM || rt->size > 8)
			error(&tok.loc, "the third argument of an overflow built-in must point to an integer type other than bool or an enum");
		if (r->type->qual & QUALCONST)
			error(&tok.loc, "the third argument of an overflow built-in points to a const object");
		e = mkexpr(EXPRBUILTIN, &typebool, a);
		a->next = b;
		b->next = r;
		r->next = NULL;
		e->u.builtin.kind = kind;
		break;
	}
	case BUILTINBSWAP16:
	case BUILTINBSWAP32:
	case BUILTINBSWAP64: {
		/* the bytes of an unsigned 16-, 32- or 64-bit value reversed; folded when the operand is constant */
		int bytes = kind == BUILTINBSWAP16 ? 2 : kind == BUILTINBSWAP32 ? 4 : 8;
		struct type *bt = bytes == 2 ? &typeushort : bytes == 4 ? &typeuint : &typeulong;
		struct expr *c;

		e = exprconvert(assignexpr(s), bt);
		c = eval(e);
		if (c->kind == EXPRCONST) {
			unsigned long long u = c->u.constant.u, r = 0;
			int k;

			for (k = 0; k < bytes; ++k)
				r |= (u >> 8 * k & 0xff) << 8 * (bytes - 1 - k);
			e = mkconstexpr(bt, r);
		} else {
			e = mkexpr(EXPRBUILTIN, bt, e);
			e->u.builtin.kind = kind;
		}
		break;
	}
	case BUILTINCLZ: case BUILTINCLZL:
	case BUILTINCTZ: case BUILTINCTZL:
	case BUILTINFFS: case BUILTINFFSL:
	case BUILTINPARITY: case BUILTINPARITYL:
	case BUILTINPOPCOUNT: case BUILTINPOPCOUNTL: {
		/* an int result counting the bits of an unsigned int or unsigned long (ffs: of an int or long, bit for bit);
		 * folded when the operand is constant. clz and ctz of zero, undefined in GNU C, are the width here, as
		 * x86's lzcnt and tzcnt give */
		bool wide = kind == BUILTINCLZL || kind == BUILTINCTZL || kind == BUILTINFFSL || kind == BUILTINPARITYL || kind == BUILTINPOPCOUNTL;
		struct type *bt = kind == BUILTINFFS ? &typeint : kind == BUILTINFFSL ? &typelong : wide ? &typeulong : &typeuint;
		struct expr *c;

		e = exprconvert(assignexpr(s), bt);
		c = eval(e);
		if (c->kind == EXPRCONST) {
			unsigned long long u = c->u.constant.u;
			int w = wide ? 64 : 32, r = 0, k;

			if (!wide)
				u &= 0xffffffffull;
			switch (kind) {
			case BUILTINCLZ: case BUILTINCLZL:
				for (k = w - 1; k >= 0 && !(u >> k & 1); --k)
					++r;
				break;
			case BUILTINCTZ: case BUILTINCTZL:
				for (k = 0; k < w && !(u >> k & 1); ++k)
					++r;
				break;
			case BUILTINFFS: case BUILTINFFSL:
				for (k = 0; k < w && !(u >> k & 1); ++k)
					;
				r = k < w ? k + 1 : 0;
				break;
			default:
				for (; u; u &= u - 1)
					++r;
				if (kind == BUILTINPARITY || kind == BUILTINPARITYL)
					r &= 1;
			}
			e = mkconstexpr(&typeint, r);
		} else {
			e = mkexpr(EXPRBUILTIN, &typeint, e);
			e->u.builtin.kind = kind;
		}
		break;
	}
	case BUILTINCHOOSEEXPR: {
		/* GNU: the result is the second or third operand itself (its type, and an lvalue if it is one), chosen by an
		 * integer constant; the other is parsed but not evaluated */
		struct expr *c, *other;

		c = eval(condexpr(s));
		if (c->kind != EXPRCONST || !(c->type->prop & PROPINT))
			error(&tok.loc, "first argument to __builtin_choose_expr must be an integer constant expression");
		expect(TCOMMA, "after condition");
		e = assignexpr(s);
		expect(TCOMMA, "after expression");
		other = assignexpr(s);
		if (!c->u.constant.u) {
			struct expr *x = e;
			e = other;
			other = x;
		}
		(void)other;   /* trees are freed with the translation unit's arena; nothing of it is emitted */
		break;
	}
	case BUILTINCONSTANTP:
		e = mkconstexpr(&typeint, eval(condexpr(s))->kind == EXPRCONST);
		break;
	case BUILTINOBJECTSIZE: {
		/* GNU: the size of the object a pointer points to when the compiler can tell, which cproc never claims to:
		 * the answer for an unknown size, (size_t)-1 for types 0 and 1, 0 for types 2 and 3 (what gcc gives when it
		 * cannot tell, at -O0 for most). The pointer is not evaluated, as in gcc. */
		struct expr *p;
		unsigned long long type;

		p = assignexpr(s);
		if (p->type->kind != TYPEPOINTER)
			error(&tok.loc, "the first argument of __builtin_object_size must be a pointer");
		delexpr(p);
		expect(TCOMMA, "after pointer");
		type = intconstexpr(s, false);
		if (type > 3)
			error(&tok.loc, "the second argument of __builtin_object_size must be 0, 1, 2 or 3");
		e = mkconstexpr(&typeulong, type < 2 ? -1ull : 0);
		break;
	}
	case BUILTINISDIGIT:
		/* the C locale's isdigit, as gcc folds it: (unsigned)c - '0' <= 9 */
		e = exprconvert(exprconvert(assignexpr(s), &typeint), &typeuint);
		e = mkbinaryexpr(&tok.loc, TSUB, e, mkconstexpr(&typeuint, '0'));
		e = exprconvert(mkbinaryexpr(&tok.loc, TLEQ, e, mkconstexpr(&typeuint, 9)), &typeint);
		break;
	case BUILTINPREFETCH:
		/* a hint: the address is evaluated (for its side effects), the read/write and locality constants checked */
		e = assignexpr(s);
		if (e->type->kind != TYPEPOINTER)
			error(&tok.loc, "the argument of __builtin_prefetch must be a pointer");
		while (consume(TCOMMA))
			intconstexpr(s, false);
		e = exprconvert(e, &typevoid);
		break;
	case BUILTINRETURNADDRESS:
	case BUILTINFRAMEADDRESS:
		/* GNU: the current function's return address or frame address; only level 0 (the kernel's _RET_IP_) */
		if (intconstexpr(s, false) != 0)
			error(&tok.loc, "%s of a level other than 0 is not supported", kind == BUILTINRETURNADDRESS ? "__builtin_return_address" : "__builtin_frame_address");
		e = mkexpr(EXPRBUILTIN, mkpointertype(&typevoid, QUALNONE), NULL);
		e->u.builtin.kind = kind;
		break;
	case BUILTINEXTRACTRETURNADDR:
		/* GNU: the address a return address stands for, which on x86-64 is the return address itself (on
		 * aarch64 pointer authentication can make it differ) */
		if (strcmp(targ->name, "x86_64-sysv") != 0)
			error(&tok.loc, "__builtin_extract_return_addr is only supported on x86-64");
		e = exprconvert(assignexpr(s), mkpointertype(&typevoid, QUALNONE));
		break;
	case BUILTINEXPECT:
		/* just a no-op for now */
		/* TODO: check that the expression and the expected value have type 'long' */
		e = assignexpr(s);
		expect(TCOMMA, "after expression");
		delexpr(assignexpr(s));
		break;
	case BUILTININFF:
		e = mkexpr(EXPRCONST, &typefloat, NULL);
		/* TODO: use INFINITY here when we can handle musl's math.h */
		e->u.constant.f = strtod("inf", NULL);
		break;
	case BUILTINNANF:
		e = assignexpr(s);
		if (!e->decayed || e->base->kind != EXPRSTRING || e->base->u.string.size > 1)
			error(&tok.loc, "__builtin_nanf currently only supports empty string literals");
		e = mkexpr(EXPRCONST, &typefloat, NULL);
		/* TODO: use NAN here when we can handle musl's math.h */
		e->u.constant.f = strtod("nan", NULL);
		break;
	case BUILTINOFFSETOF:
		t = typename(s, NULL, NULL);
		expect(TCOMMA, "after type name");
		name = expect(TIDENT, "after ','");
		if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
			error(&tok.loc, "type is not a struct/union type");
		offset = 0;
		m = typemember(t, name, &offset);
		if (!m)
			error(&tok.loc, "struct/union has no member named '%s'", name);
		toeval = NULL;
		designator(s, m->type, &offset, &toeval);
		e = mkconstexpr(&typeulong, offset);
		if (toeval)
			e = mkbinaryexpr(&tok.loc, TADD, e, toeval);
		break;
	case BUILTINTYPESCOMPATIBLEP:
		t = typename(s, NULL, NULL);
		expect(TCOMMA, "after type name");
		e = mkconstexpr(&typeint, typecompatible(t, typename(s, NULL, NULL)));
		break;
	case BUILTINUNREACHABLE:
		e = mkexpr(EXPRBUILTIN, &typevoid, NULL);
		e->u.builtin.kind = BUILTINUNREACHABLE;
		break;
	case BUILTINVAARG:
		e = mkexpr(EXPRBUILTIN, NULL, assignexpr(s));
		e->u.builtin.kind = BUILTINVAARG;
		if (!typesame(e->base->type, typeadjvalist))
			error(&tok.loc, "va_arg argument must have type va_list");
		if (typeadjvalist == targ->typevalist)
			e->base = mkunaryexpr(TBAND, e->base);
		expect(TCOMMA, "after va_list");
		e->type = typename(s, &e->qual, &toeval);
		e->toeval = toeval;
		break;
	case BUILTINVACOPY:
		e = mkexpr(EXPRASSIGN, &typevoid, NULL);
		e->u.assign.l = assignexpr(s);
		if (!typesame(e->u.assign.l->type, typeadjvalist))
			error(&tok.loc, "va_copy destination must have type va_list");
		if (typeadjvalist != targ->typevalist)
			e->u.assign.l = mkunaryexpr(TMUL, e->u.assign.l);
		expect(TCOMMA, "after target va_list");
		e->u.assign.r = assignexpr(s);
		if (!typesame(e->u.assign.r->type, typeadjvalist))
			error(&tok.loc, "va_copy source must have type va_list");
		if (typeadjvalist != targ->typevalist)
			e->u.assign.r = mkunaryexpr(TMUL, e->u.assign.r);
		break;
	case BUILTINVAEND:
		e = assignexpr(s);
		if (!typesame(e->type, typeadjvalist))
			error(&tok.loc, "va_end argument must have type va_list");
		e = mkexpr(EXPRCAST, &typevoid, e);
		break;
	case BUILTINVASTART:
		e = mkexpr(EXPRBUILTIN, &typevoid, assignexpr(s));
		e->u.builtin.kind = BUILTINVASTART;
		if (!typesame(e->base->type, typeadjvalist))
			error(&tok.loc, "va_start argument must have type va_list");
		if (typeadjvalist == targ->typevalist)
			e->base = mkunaryexpr(TBAND, e->base);
		if (consume(TCOMMA))
			delexpr(assignexpr(s));
		break;
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
		e = atomicbuiltin(s, kind);
		break;
	case BUILTINATOMICLOAD:
	case BUILTINATOMICSTORE:
	case BUILTINATOMICXCHG:
	case BUILTINATOMICCAS:
		e = genericatomic(s, kind);
		break;
	case BUILTINATOMICTESTANDSET:
	case BUILTINATOMICCLEAR:
		e = byteatomicbuiltin(s, kind);
		break;
	default:
		fatal("internal error; unknown builtin");
	}
	return e;
}

static struct expr *
mkincdecexpr(enum tokenkind op, struct expr *base, bool post)
{
	struct expr *e;

	if (!base->lvalue)
		error(&tok.loc, "operand of '%s' operator must be an lvalue", tokenstr(op));
	if (base->qual & QUALCONST)
		error(&tok.loc, "operand of '%s' operator is const qualified", tokenstr(op));
	/* a pointer steps by its element size: 1 for void and function types (GNU), none for another incomplete type */
	if (base->type->kind == TYPEPOINTER && base->type->base->incomplete && base->type->base->kind != TYPEVOID &&
	    !(base->type->base->kind == TYPEARRAY && base->type->base->prop & PROPVM))
		error(&tok.loc, "operand of '%s' operator is a pointer to an incomplete type", tokenstr(op));
	e = mkexpr(EXPRINCDEC, base->type, base);
	e->op = op;
	e->u.incdec.post = post;
	return e;
}

static struct expr *
postfixexpr(struct scope *s, struct expr *r)
{
	struct expr *e, *arr, *idx, *tmp, **end;
	struct type *t;
	struct decl *p;
	struct member *m;
	unsigned long long offset;
	enum typequal tq;
	enum tokenkind op;
	bool lvalue;

	if (!r)
		r = primaryexpr(s);
	for (;;) {
		switch (tok.kind) {
		case TLBRACK:  /* subscript */
			next();
			arr = r;
			idx = expr(s);
			if (arr->type->kind != TYPEPOINTER) {
				if (idx->type->kind != TYPEPOINTER)
					error(&tok.loc, "either array or index must be pointer type");
				tmp = arr;
				arr = idx;
				idx = tmp;
			}
			if (arr->type->base->incomplete)
				error(&tok.loc, "array is pointer to incomplete type");
			if (!(idx->type->prop & PROPINT))
				error(&tok.loc, "index is not an integer type");
			e = mkunaryexpr(TMUL, mkbinaryexpr(&tok.loc, TADD, arr, idx));
			expect(TRBRACK, "after array index");
			break;
		case TLPAREN:  /* function call */
			next();
			if (r->kind == EXPRIDENT && r->u.ident.decl->kind == DECLBUILTIN) {
				e = builtinfunc(s, r->u.ident.decl->u.builtin);
				expect(TRPAREN, "after builtin parameters");
				break;
			}
			if (r->type->kind != TYPEPOINTER || r->type->base->kind != TYPEFUNC)
				error(&tok.loc, "called object is not a function");
			t = r->type->base;
			e = mkexpr(EXPRCALL, t->base, r);
			e->u.call.args = NULL;
			e->u.call.nargs = 0;
			p = t->u.func.params;
			end = &e->u.call.args;
			while (tok.kind != TRPAREN) {
				if (e->u.call.args)
					expect(TCOMMA, "or ')' after function call argument");
				if (!p && !t->u.func.isvararg && !t->u.func.unprototyped)
					error(&tok.loc, "too many arguments for function call");
				*end = assignexpr(s);
				if ((t->u.func.isvararg || t->u.func.unprototyped) && !p)
					*end = exprpromote(*end);
				else if (p->type->kind == TYPEUNION && p->type->u.structunion.transparent)
					*end = transparentarg(*end, p->type);
				else
					*end = exprassign(*end, p->type);
				end = &(*end)->next;
				++e->u.call.nargs;
				if (p)
					p = p->next;
			}
			if (p && !t->u.func.isvararg && !t->u.func.unprototyped)
				error(&tok.loc, "not enough arguments for function call");
			/* a call of a function whose body is { return C; } is C when its arguments have no side effects: gcc
			 * inlines it and folds what depends on it (the kernel's pmd_trans_huge() is 0 without transparent huge
			 * pages, and the call it guards names a function this configuration does not have) */
			/* likewise a call of a function whose body is {} is nothing (the kernel's __apply_fineibt() without CFI,
			 * whose arguments name sections this configuration does not have; noinline does not stop gcc, which
			 * finds the function const and drops the call, as for apply_retpolines()). Not folded: a weak function
			 * (the link may take another unit's definition) and a noipa one (qbe-prep.rb's __nfcxx_keep(&x), whose
			 * call is what keeps a volatile local in memory). Under -p only, the kernel mode: elsewhere the call
			 * stays a call, and an expression with it no constant expression (a VLA bound stays a VLA's). */
			if (prune && r->kind == EXPRUNARY && r->op == TBAND && r->base->kind == EXPRIDENT &&
			    r->base->u.ident.decl->kind == DECLFUNC && r->base->u.ident.decl->defined &&
			    !r->base->u.ident.decl->weak && !r->base->u.ident.decl->noipa &&
			    (r->base->u.ident.decl->u.func.constret || r->base->u.ident.decl->u.func.emptybody)) {
				struct expr *a;
				bool pure = true;

				for (a = e->u.call.args; a; a = a->next)
					pure &= nosideeffects(a);
				if (pure) {
					if (r->base->u.ident.decl->u.func.constret)
						e = mkconstexpr(t->base, r->base->u.ident.decl->u.func.retval);
					else
						e = mkexpr(EXPRCAST, &typevoid, mkconstexpr(&typeint, 0));
					next();
					break;
				}
			}
			/* a call of an always_inline function with constant arguments may go to a clone (decl.c funcclone) */
			if (r->kind == EXPRUNARY && r->op == TBAND && r->base->kind == EXPRIDENT &&
			    r->base->u.ident.decl->kind == DECLFUNC && r->base->u.ident.decl->u.func.body) {
				struct decl *c = funcclone(r->base->u.ident.decl, e->u.call.args);

				if (c)
					r->base->u.ident.decl = c;
				else if (r->base->u.ident.decl->u.func.refused && curfunc)
					funcdecl(curfunc)->u.func.refused = true;   /* the caller's constant calls may get clones then */
			}
			e = decay(e);
			next();
			break;
		case TPERIOD:
			r = mkunaryexpr(TBAND, r);
			/* fallthrough */
		case TARROW:
			op = tok.kind;
			if (r->type->kind != TYPEPOINTER)
				error(&tok.loc, "'%s' operator must be applied to pointer to struct/union", tokenstr(op));
			t = r->type->base;
			tq = r->type->qual;
			if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
				error(&tok.loc, "'%s' operator must be applied to pointer to struct/union", tokenstr(op));
			next();
			if (!iscident(tok.kind))
				error(&tok.loc, "expected identifier after '%s' operator", tokenstr(op));
			lvalue = op == TARROW || r->base->lvalue;
			offset = 0;
			m = typemember(t, tokenstr(tok.kind), &offset);
			if (!m)
				error(&tok.loc, "struct/union has no member named '%s'", tok.lit);
			r = mkbinaryexpr(&tok.loc, TADD, exprconvert(r, &typeulong), mkconstexpr(&typeulong, offset));
			r->type = mkpointertype(m->type, tq | m->qual);
			r = mkunaryexpr(TMUL, r);
			r->lvalue = lvalue;
			if (m->bits.before || m->bits.after) {
				e = mkexpr(EXPRBITFIELD, r->type, r);
				e->lvalue = lvalue;
				e->u.bitfield.bits = m->bits;
			} else {
				e = r;
			}
			next();
			break;
		case TINC:
		case TDEC:
			e = mkincdecexpr(tok.kind, r, true);
			next();
			break;
		default:
			return r;
		}
		r = e;
	}
}

static struct expr *castexpr(struct scope *);

static struct expr *
unaryexpr(struct scope *s)
{
	enum tokenkind op;
	struct expr *e, *l;
	struct type *t;

	op = tok.kind;
	switch (op) {
	case TINC:
	case TDEC:
		next();
		l = unaryexpr(s);
		e = mkincdecexpr(op, l, false);
		break;
	case TBAND:
	case TMUL:
		next();
		return mkunaryexpr(op, castexpr(s));
	case TADD:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPARITH))
			error(&tok.loc, "operand of unary '+' operator must have arithmetic type");
		if (e->type->prop & PROPINT)
			e = exprpromote(e);
		break;
	case TSUB:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPARITH))
			error(&tok.loc, "operand of unary '-' operator must have arithmetic type");
		if (e->type->prop & PROPINT)
			e = exprpromote(e);
		e = mkexpr(EXPRUNARY, e->type, e);
		e->op = op;
		break;
	case TBNOT:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPINT))
			error(&tok.loc, "operand of '~' operator must have integer type");
		e = exprpromote(e);
		e = mkbinaryexpr(&tok.loc, TXOR, e, mkconstexpr(e->type, -1));
		break;
	case TLNOT:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPSCALAR))
			error(&tok.loc, "operator '!' must have scalar operand");
		e = mkbinaryexpr(&tok.loc, TEQL, e, mkconstexpr(&typeint, 0));
		break;
	case TSIZEOF:
	case TALIGNOF:
	case T__ALIGNOF__:
		next();
		if (consume(TLPAREN)) {
			t = typename(s, NULL, NULL);
			if (t) {
				expect(TRPAREN, "after type name");
				/* might be part of a compound literal */
				if (op == TSIZEOF && tok.kind == TLBRACE)
					parseinit(s, t);
				e = NULL;
			} else {
				e = parenexpr(s);
				expect(TRPAREN, "after expression");
				if (op == TSIZEOF)
					e = postfixexpr(s, e);
			}
		} else if (op == TSIZEOF) {
			t = NULL;
			e = unaryexpr(s);
		} else {
			error(&tok.loc, "expected ')' after 'alignof'");
		}
		if (!t) {
			if (e->decayed)
				e = e->base;
			if (e->kind == EXPRBITFIELD)
				error(&tok.loc, "%s operator applied to bitfield expression", tokenstr(op));
			t = e->type;
		}
		if (t->kind == TYPEVOID || t->kind == TYPEFUNC) {
			/* GNU C: sizeof and __alignof__ of void and of a function type are 1 */
			e = mkconstexpr(&typeulong, 1);
			break;
		}
		if (t->incomplete)
			error(&tok.loc, "%s operator applied to incomplete type", tokenstr(op));
		if (t->kind == TYPEARRAY && t->size == 0 && t->prop & PROPVM && op == TSIZEOF) {   /* a GNU int a[0] is 0 */
			e = mkexpr(EXPRSIZEOF, &typeulong, e);
			e->u.szof.type = t;
		} else {
			/*
			XXX: __alignof__ is not the same as alignof on 32-bit archs
			this needs to be considered if we gain support for those archs
			*/
			unsigned long long a = t->align;

			/* GNU: the alignment of an object is the object's (aligned on its declaration), as gcc's DECL_ALIGN */
			if (e && e->kind == EXPRIDENT && e->u.ident.decl->kind == DECLOBJECT)
				a = e->u.ident.decl->u.obj.align;
			e = mkconstexpr(&typeulong, op == TSIZEOF ? t->size : a);
		}
		break;
	default:
		e = postfixexpr(s, NULL);
	}

	return e;
}

/* the expression after a '(' already consumed: a GNU statement expression when a '{' follows */
static struct expr *
parenexpr(struct scope *s)
{
	struct block *saved, *first;
	struct expr *e, *v;

	if (tok.kind != TLBRACE)
		return expr(s);
	if (!curfunc)
		error(&tok.loc, "statement expression outside of a function");
	saved = funcdetach(curfunc, &first);
	v = stmtexpr(curfunc, s);
	e = mkexpr(EXPRSTMT, v ? v->type : &typevoid, v);
	e->u.stmt.first = first;
	e->u.stmt.last = funcreattach(curfunc, saved);
	e->u.stmt.done = false;
	return e;
}

static struct expr *
castexpr(struct scope *s)
{
	struct type *t, *ct;
	struct decl *d;
	enum typequal tq;
	struct expr *r, *e, **end, *toeval;

	ct = NULL;
	end = &r;
	while (consume(TLPAREN)) {
		tq = QUALNONE;
		t = typename(s, &tq, &toeval);
		if (!t) {
			e = parenexpr(s);
			expect(TRPAREN, "after expression to match '('");
			e = postfixexpr(s, e);
			goto done;
		}
		expect(TRPAREN, "after type name");
		if (tok.kind == TLBRACE) {
			e = mkexpr(EXPRCOMPOUND, t, NULL);
			e->toeval = toeval;
			e->qual = tq;
			e->lvalue = true;
			d = mkdecl(NULL, DECLOBJECT, t, tq, LINKNONE);
			d->u.obj.storage = s == &filescope ? SDSTATIC : SDAUTO;
			e->u.compound.decl = d;
			e->u.compound.init = parseinit(s, t);
			if (initfamsize)
				error(&tok.loc, "a compound literal that initializes a flexible array member is not supported");
			e = postfixexpr(s, decay(e));
			goto done;
		}
		if ((t->kind == TYPEUNION || t->kind == TYPESTRUCT) && !t->incomplete && !toeval) {
			/* GNU cast to a union (the kernel's (union ibs_fetch_ctl)config): a union value holding the operand in
			 * the member of its type, as the compound literal (union u){.member = operand} would; a cast of a
			 * struct or union to its own type is its value (the kernel's (sockptr_t)dst) */
			struct member *m;
			struct expr *op = castexpr(s);

			if (typecompatible(t, op->type)) {
				e = op;
				if (e->lvalue) {   /* a cast is not an lvalue: the value of a copy */
					e = mkexpr(EXPRCOMMA, op->type, op);
					e->base->next = NULL;
				}
				goto done;
			}
			if (t->kind == TYPESTRUCT)
				error(&tok.loc, "cast type must be scalar");
			for (m = t->u.structunion.members; m; m = m->next)
				if (m->name && typecompatible(m->type, op->type))
					break;
			if (!m)
				error(&tok.loc, "cast to union type from a type that is not one of its members' types");
			if (m->bits.before || m->bits.after)
				error(&tok.loc, "cast to union type through a bit-field member is not supported");
			e = mkexpr(EXPRCOMPOUND, t, NULL);
			e->qual = tq;
			d = mkdecl(NULL, DECLOBJECT, t, tq, LINKNONE);
			d->u.obj.storage = s == &filescope ? SDSTATIC : SDAUTO;
			e->u.compound.decl = d;
			e->u.compound.init = mkinit(0, m->type->size, (struct bitfield){0}, exprconvert(op, m->type));
			goto done;
		}
		if (t != &typevoid && !(t->prop & PROPSCALAR))
			error(&tok.loc, "cast type must be scalar");
		e = mkexpr(EXPRCAST, t, NULL);
		e->toeval = toeval;
		*end = e;
		end = &e->base;
		ct = t;
	}
	e = unaryexpr(s);

done:
	if (ct && ct != &typevoid && !(e->type->prop & PROPSCALAR))
		error(&tok.loc, "cast operand must have scalar type");
	*end = e;
	return r;
}

static int
precedence(enum tokenkind t)
{
	switch (t) {
	case TLOR:     return 0;
	case TLAND:    return 1;
	case TBOR:     return 2;
	case TXOR:     return 3;
	case TBAND:    return 4;
	case TEQL:
	case TNEQ:     return 5;
	case TLESS:
	case TGREATER:
	case TLEQ:
	case TGEQ:     return 6;
	case TSHL:
	case TSHR:     return 7;
	case TADD:
	case TSUB:     return 8;
	case TMUL:
	case TDIV:
	case TMOD:     return 9;
	}
	return -1;
}

static struct expr *
binaryexpr(struct scope *s, struct expr *l, int i)
{
	struct expr *r;
	struct location loc;
	enum tokenkind op;
	int j, k;

	if (!l)
		l = castexpr(s);
	while ((j = precedence(tok.kind)) >= i) {
		op = tok.kind;
		loc = tok.loc;
		next();
		r = castexpr(s);
		while ((k = precedence(tok.kind)) > j)
			r = binaryexpr(s, r, k);
		l = mkbinaryexpr(&loc, op, l, r);
	}
	return l;
}

struct expr *
condexpr(struct scope *s)
{
	struct expr *e, *l, *r;
	struct type *t, *lt, *rt;
	enum typequal tq;

	e = binaryexpr(s, NULL, 0);
	if (!consume(TQUESTION))
		return e;
	l = tok.kind == TCOLON ? e : expr(s);
	expect(TCOLON, "in conditional expression");
	r = condexpr(s);

	lt = l->type;
	rt = r->type;
	if (lt == rt) {
		t = lt;
	} else if (lt->prop & PROPARITH && rt->prop & PROPARITH) {
		t = typecommonreal(lt, bitfieldwidth(l), rt, bitfieldwidth(r));
	} else if (lt == &typevoid && rt == &typevoid) {
		t = &typevoid;
	} else {
		l = eval(l);
		r = eval(r);
		if (nullpointer(l) && rt->kind == TYPEPOINTER) {
			t = rt;
		} else if (nullpointer(r) && lt->kind == TYPEPOINTER) {
			t = lt;
		} else if (lt->kind == TYPEPOINTER && rt->kind == TYPEPOINTER) {
			tq = lt->qual | rt->qual;
			lt = lt->base;
			rt = rt->base;
			if (lt == &typevoid || rt == &typevoid) {
				t = &typevoid;
			} else if (typecompatible(lt, rt)) {
				t = typecomposite(lt, rt);
			} else {
				error(&tok.loc, "operands of conditional operator must have compatible types");
			}
			t = mkpointertype(t, tq);
		} else {
			error(&tok.loc, "invalid operands to conditional operator");
		}
	}
	e = eval(e);
	if (e->kind == EXPRCONST && e->type->prop & PROPINT)
		return exprconvert(e->u.constant.u ? l : r, t);
	e = mkexpr(EXPRCOND, t, e);
	e->u.cond.t = l;
	e->u.cond.f = r;
	return e;
}

unsigned long long
intconstexpr(struct scope *s, bool allowneg)
{
	struct expr *e;

	e = eval(condexpr(s));
	if (e->kind != EXPRCONST || !(e->type->prop & PROPINT))
		error(&tok.loc, "not an integer constant expression");
	if (!allowneg && e->type->u.arith.issigned && e->u.constant.u >> 63)
		error(&tok.loc, "integer constant expression cannot be negative");
	return e->u.constant.u;
}

static struct expr *
mkassignexpr(struct expr *l, struct expr *r)
{
	struct expr *e;

	e = mkexpr(EXPRASSIGN, l->type, NULL);
	e->u.assign.l = l;
	e->u.assign.r = exprassign(r, l->type);
	return e;
}

/* The generic GCC forms take pointers for the values and for the result, and lower to the C11 forms above:
 * __atomic_load(p, out, o) is *out = load(p, o); __atomic_store(p, in, o) is store(p, *in, o);
 * __atomic_exchange(p, in, out, o) is *out = exchange(p, *in, o); and __atomic_compare_exchange(p, expected, desired,
 * weak, success, failure) is cas(p, expected, *desired, success, failure), with the weak flag dropped (it does not
 * change the result on the targets cproc supports). */
static struct expr *
genericatomic(struct scope *s, enum builtinkind kind)
{
	struct expr *first, *arg[5], *e, *value;
	struct type *pointee;
	unsigned n = 0, want;

	first = assignexpr(s);
	if (first->type->kind != TYPEPOINTER)
		error(&tok.loc, "atomic operation needs a pointer");
	pointee = first->type->base;
	if (!(pointee->prop & PROPSCALAR) || (pointee->size != 1 && pointee->size != 2 && pointee->size != 4 && pointee->size != 8))
		error(&tok.loc, "atomic operation on an unsupported type");
	while (consume(TCOMMA)) {
		if (n == 5)
			error(&tok.loc, "wrong number of arguments to an atomic builtin");
		arg[n++] = assignexpr(s);
	}
	switch (kind) {
	case BUILTINATOMICLOAD:
	case BUILTINATOMICSTORE:
		want = 2;
		break;
	case BUILTINATOMICXCHG:
		want = 3;
		break;
	default:
		want = 5;
		break;
	}
	if (n != want)
		error(&tok.loc, "wrong number of arguments to an atomic builtin");
	switch (kind) {
	case BUILTINATOMICLOAD:
		if (arg[0]->type->kind != TYPEPOINTER)
			error(&tok.loc, "atomic load needs a pointer for the result");
		first->next = arg[1];
		e = mkexpr(EXPRBUILTIN, pointee, first);
		e->u.builtin.kind = BUILTINC11LOAD;
		return mkassignexpr(mkunaryexpr(TMUL, arg[0]), e);
	case BUILTINATOMICSTORE:
		if (arg[0]->type->kind != TYPEPOINTER)
			error(&tok.loc, "atomic store needs a pointer to the value");
		value = mkunaryexpr(TMUL, arg[0]);
		first->next = value;
		value->next = arg[1];
		e = mkexpr(EXPRBUILTIN, &typevoid, first);
		e->u.builtin.kind = BUILTINC11STORE;
		return e;
	case BUILTINATOMICXCHG:
		if (arg[0]->type->kind != TYPEPOINTER || arg[1]->type->kind != TYPEPOINTER)
			error(&tok.loc, "atomic exchange needs pointers to the value and the result");
		value = mkunaryexpr(TMUL, arg[0]);
		first->next = value;
		value->next = arg[2];
		e = mkexpr(EXPRBUILTIN, pointee, first);
		e->u.builtin.kind = BUILTINC11XCHG;
		return mkassignexpr(mkunaryexpr(TMUL, arg[1]), e);
	default:
		if (arg[0]->type->kind != TYPEPOINTER || arg[1]->type->kind != TYPEPOINTER)
			error(&tok.loc, "atomic compare-exchange needs pointers to the expected and desired values");
		value = mkunaryexpr(TMUL, arg[1]);
		first->next = arg[0];
		arg[0]->next = value;
		value->next = arg[3];
		arg[3]->next = arg[4];
		e = mkexpr(EXPRBUILTIN, &typebool, first);
		e->u.builtin.kind = BUILTINC11CAS;
		return e;
	}
}

struct expr *
assignexpr(struct scope *s)
{
	struct expr *e, *l, *r, *tmp, *bit;
	enum tokenkind op;

	l = condexpr(s);
	if (l->kind == EXPRBINARY || l->kind == EXPRCOMMA || l->kind == EXPRCAST)
		return l;
	switch (tok.kind) {
	case TASSIGN:     op = TNONE; break;
	case TMULASSIGN:  op = TMUL;  break;
	case TDIVASSIGN:  op = TDIV;  break;
	case TMODASSIGN:  op = TMOD;  break;
	case TADDASSIGN:  op = TADD;  break;
	case TSUBASSIGN:  op = TSUB;  break;
	case TSHLASSIGN:  op = TSHL;  break;
	case TSHRASSIGN:  op = TSHR;  break;
	case TBANDASSIGN: op = TBAND; break;
	case TXORASSIGN:  op = TXOR;  break;
	case TBORASSIGN:  op = TBOR;  break;
	default:
		return l;
	}
	if (!l->lvalue)
		error(&tok.loc, "left side of assignment expression is not an lvalue");
	next();
	r = assignexpr(s);
	if (!op)
		return mkassignexpr(l, r);
	/* rewrite `E1 OP= E2` as `T = &E1, *T = *T OP E2`, where T is a temporary slot */
	if (l->kind == EXPRBITFIELD) {
		bit = l;
		l = l->base;
	} else {
		bit = NULL;
	}
	tmp = mkexpr(EXPRTEMP, mkpointertype(l->type, l->qual), NULL);
	tmp->lvalue = true;
	tmp->u.temp = NULL;
	e = mkassignexpr(tmp, mkunaryexpr(TBAND, l));
	l = mkunaryexpr(TMUL, tmp);
	if (bit) {
		bit->base = l;
		l = bit;
	}
	r = mkbinaryexpr(&tok.loc, op, l, r);
	e->next = mkassignexpr(l, r);
	return mkexpr(EXPRCOMMA, l->type, e);
}

struct expr *
expr(struct scope *s)
{
	struct expr *r, *e, **end;

	end = &r;
	for (;;) {
		e = assignexpr(s);
		*end = e;
		end = &e->next;
		if (tok.kind != TCOMMA)
			break;
		next();
	}
	if (!r->next)
		return r;
	return mkexpr(EXPRCOMMA, e->type, r);
}
