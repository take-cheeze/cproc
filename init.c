#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct object {
	unsigned long long offset;
	struct type *type;
	union {
		struct member *mem;
		unsigned long long idx;
	} u;
	bool iscur;
};

struct initparser {
	/* TODO: keep track of type depth, and allocate maximum possible
	   number of nested objects in initializer */
	struct object obj[32], *cur, *sub;
	struct init *init, **last;
	/* a GNU range designator [lo ... hi] whose element is being initialized: once the parser is back at the array's
	 * level, the element's initializers are repeated for lo + 1 ... hi (rangedone) */
	struct object *rangearr;
	unsigned long long rangelo, rangehi;   /* byte offsets of the first and the last element in the array */
	struct type *fam;   /* GNU: the initialized flexible array member of the object (a copy of its type), or null */
};

/* the bytes the last parseinit's flexible array member takes (GNU; 0 without one) */
unsigned long long initfamsize;

struct init *
mkinit(unsigned long long start, unsigned long long end, struct bitfield bits, struct expr *expr)
{
	struct init *init;

	init = xmalloc(sizeof(*init));
	init->start = start;
	init->end = end;
	init->expr = expr;
	init->bits = bits;
	init->next = NULL;

	return init;
}

static void
initadd(struct initparser *p, struct init *new)
{
	struct init **init, *old;

	init = p->last;
	for (; old = *init; init = &old->next) {
		if (old->end * 8 - old->bits.after <= new->start * 8 + new->bits.before)
			continue;
		/* no overlap, insert before `old` */
		if (new->end * 8 - new->bits.after <= old->start * 8 + old->bits.before)
			break;
		/* replace any initializers that `new` covers */
		if (old->end * 8 - old->bits.after <= new->end * 8 - new->bits.after) {
			do old = old->next;
			while (old && old->end * 8 - old->bits.after <= new->end * 8 - new->bits.after);
			break;
		}
		/* `old` covers `new`, keep looking */
	}
	new->next = old;
	*init = new;
	p->last = &new->next;
}

/* whether t, the type of the member p->sub is at, is the flexible array member of the outermost struct */
static bool
famslot(struct initparser *p, struct type *t)
{
	return t->kind == TYPEARRAY && t->incomplete && p->sub == p->obj && p->sub->type->kind == TYPESTRUCT &&
		p->sub->u.mem && !p->sub->u.mem->next && t == p->sub->u.mem->type;
}

static void
subobj(struct initparser *p, struct type *t, unsigned long long off)
{
	/*
	The subobject could be incomplete if it's a flexible array member. GNU C initializes one of the outermost
	struct (the kernel's init_mm.cpu_bitmap): the array grows with its initializers as an array of unknown size
	does, in a copy of its type (the member's own type is the struct's), and the object is that much larger.
	*/
	if (famslot(p, t)) {
		if (!p->fam) {   /* else a designator names the member again */
			p->fam = xmalloc(sizeof(*p->fam));
			*p->fam = *t;
			p->fam->size = 0;
		}
		t = p->fam;
	} else if (t->incomplete) {
		error(&tok.loc, "initializer specified for incomplete type");
	}
	off += p->sub->offset;
	if (++p->sub == p->obj + countof(p->obj))
		fatal("internal error: too many designators");
	p->sub->type = t;
	p->sub->offset = off;
	p->sub->iscur = false;
}

static bool
findmember(struct initparser *p, const char *name)
{
	struct member *m;

	for (m = p->sub->type->u.structunion.members; m; m = m->next) {
		if (m->name) {
			if (strcmp(m->name, name) == 0) {
				p->sub->u.mem = m;
				subobj(p, m->type, m->offset);
				return true;
			}
		} else {
			p->sub->u.mem = m;   /* the anonymous member is the cursor: initialization goes on after it */
			subobj(p, m->type, m->offset);
			if (findmember(p, name))
				return true;
			--p->sub;
		}
	}
	return false;
}

static void
designator(struct scope *s, struct initparser *p)
{
	struct type *t;
	char *name;

	p->last = &p->init;
	p->sub = p->cur;
	for (;;) {
		t = p->sub->type;
		switch (tok.kind) {
		case TLBRACK: {
			unsigned long long hi;

			if (t->kind != TYPEARRAY)
				error(&tok.loc, "index designator is only valid for array types");
			next();
			p->sub->u.idx = intconstexpr(s, false) * t->base->size;
			hi = p->sub->u.idx;
			if (consume(TELLIPSIS)) {   /* GNU [lo ... hi] */
				hi = intconstexpr(s, false) * t->base->size;
				if (hi < p->sub->u.idx)
					error(&tok.loc, "empty index range in designator");
				if (p->rangearr)
					error(&tok.loc, "a range designator inside a range designator's element is not supported");
				p->rangearr = p->sub;
				p->rangelo = p->sub->u.idx;
				p->rangehi = hi;
			}
			if (hi >= t->size) {
				if (!t->incomplete)
					error(&tok.loc, "index designator is larger than array length");
				t->size = hi + t->base->size;
			}
			expect(TRBRACK, "for index designator");
			subobj(p, t->base, p->sub->u.idx);
			break;
		}
		case TPERIOD:
			if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
				error(&tok.loc, "member designator only valid for struct/union types");
			next();
			name = expect(TIDENT, "for member designator");
			if (!findmember(p, name))
				error(&tok.loc, "%s has no member named '%s'", t->kind == TYPEUNION ? "union" : "struct", name);
			break;
		default:
			expect(TASSIGN, "after designator");
			return;
		}
	}
}

/* whether an initializer may be repeated for a range: gcc evaluates it once, so only a constant one is taken */
static bool
repeatable(struct expr *e)
{
	if (eval(e)->kind == EXPRCONST)   /* an arithmetic constant (the kernel's [0 ... N - 1] = -1, converted) */
		return true;
	while (e->kind == EXPRCAST)
		e = e->base;
	switch (e->kind) {
	case EXPRCONST:
	case EXPRSTRING:
		return true;
	case EXPRIDENT:
		return e->u.ident.decl->kind == DECLFUNC || e->u.ident.decl->kind == DECLCONST ||
			e->u.ident.decl->kind == DECLOBJECT && e->u.ident.decl->u.obj.storage == SDSTATIC && e->type->kind == TYPEARRAY;
	case EXPRUNARY:
		return e->op == TBAND && e->base->kind == EXPRSTRING ||   /* a string literal, decayed */
			e->op == TBAND && e->base->kind == EXPRIDENT && repeatable(e->base) ||
			e->op == TBAND && e->base->kind == EXPRIDENT && e->base->u.ident.decl->kind == DECLOBJECT &&
			e->base->u.ident.decl->u.obj.storage == SDSTATIC;
	case EXPRBINARY:
		return repeatable(e->u.binary.l) && repeatable(e->u.binary.r);
	default:
		return eval(e)->kind == EXPRCONST;
	}
}

/* a range designator's element is complete when the parser is back at the array's level (or above): its
 * initializers are repeated for the other elements of the range, and the array continues after the range */
static void
rangedone(struct initparser *p)
{
	struct init *i, *list = NULL, **end = &list, *c;
	unsigned long long base, esize, k;

	if (!p->rangearr || p->cur > p->rangearr)
		return;
	esize = p->rangearr->type->base->size;
	base = p->rangearr->offset + p->rangelo;
	for (i = p->init; i; i = i->next) {
		if (i->start < base || i->end > base + esize)
			continue;
		if (!repeatable(i->expr))
			error(&tok.loc, "a range designator with an initializer that is not constant is not supported");
		*end = mkinit(i->start, i->end, i->bits, i->expr);
		end = &(*end)->next;
	}
	for (k = esize; p->rangelo + k <= p->rangehi; k += esize) {
		for (c = list; c; c = c->next) {
			p->last = &p->init;
			initadd(p, mkinit(c->start + k, c->end + k, c->bits, c->expr));
		}
	}
	if (p->rangearr->u.idx < p->rangehi)
		p->rangearr->u.idx = p->rangehi;
	p->rangearr = NULL;
}

static void
focus(struct initparser *p)
{
	struct type *t;

	switch (p->sub->type->kind) {
	case TYPEARRAY:
		t = p->sub->type->base;
		p->sub->u.idx = 0;
		if (p->sub->type->incomplete)
			p->sub->type->size = t->size;
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		p->sub->u.mem = p->sub->type->u.structunion.members;
		t = p->sub->u.mem->type;
		break;
	default:
		fatal("internal error: init cursor has unexpected type");
	}
	subobj(p, t, 0);
}

static void
advance(struct initparser *p)
{
	struct type *t;

	for (;;) {
		--p->sub;
		t = p->sub->type;
		switch (t->kind) {
		case TYPEARRAY:
			p->sub->u.idx += t->base->size;
			if (p->sub->u.idx == t->size) {
				if (!t->incomplete)
					break;
				t->size += t->base->size;
			}
			subobj(p, t->base, p->sub->u.idx);
			return;
		case TYPESTRUCT:
			p->sub->u.mem = p->sub->u.mem->next;
			if (p->sub->u.mem) {
				subobj(p, p->sub->u.mem->type, p->sub->u.mem->offset);
				return;
			}
			break;
		}
		if (p->sub == p->cur)
			error(&tok.loc, "too many initializers for type");
	}
}

/* 6.7.9 Initialization */
struct init *
parseinit(struct scope *s, struct type *t)
{
	struct initparser p;
	struct expr *expr;
	struct type *base;
	struct bitfield bits;

	p.cur = NULL;
	p.sub = p.obj;
	p.sub->offset = 0;
	p.sub->type = t;
	p.sub->iscur = false;
	p.init = NULL;
	p.last = &p.init;
	p.rangearr = NULL;
	p.fam = NULL;
	initfamsize = 0;
	if (t->incomplete && t->kind != TYPEARRAY)
		error(&tok.loc, "initializer specified for incomplete type");
	if (t->kind == TYPEARRAY && t->base->size == 0)
		error(&tok.loc, "initializer specified for variable length array type");
	for (;;) {
		rangedone(&p);
		if (p.cur) {
			if (tok.kind == TLBRACK || tok.kind == TPERIOD)
				designator(s, &p);
			else if (p.sub != p.cur)
				advance(&p);
			else if (p.cur->type->kind == TYPESTRUCT || p.cur->type->kind == TYPEUNION)
				focus(&p);
		}
		if (consume(TLBRACE)) {
			if (consume(TRBRACE)){
				/* GNU: an array of unknown size with an empty initializer has no elements (the kernel's
				 * terminator-only tables) */
				if (p.sub->type->incomplete && p.sub->type->kind == TYPEARRAY) {
					p.sub->type->size = 0;
					p.sub->type->incomplete = false;
				}
				goto next;
			}
			if (p.cur == p.sub) {
				if (p.cur->type->prop & PROPSCALAR)
					error(&tok.loc, "nested braces around scalar initializer");
				assert(p.cur->type->kind == TYPEARRAY);
				focus(&p);
			}
			p.cur = p.sub;
			p.cur->iscur = true;
			continue;
		}
		expr = assignexpr(s);
		for (;;) {
			t = p.sub->type;
			switch (t->kind) {
			case TYPEARRAY:
				if (!expr->decayed || expr->base->kind != EXPRSTRING || !(t->base->prop & PROPINT))
					break;
				base = t->base;
				expr = expr->base;
				if (!(base->prop & PROPCHAR && expr->type->base->prop & PROPCHAR) && !typecompatible(base, expr->type->base))
					error(&tok.loc, "cannot initialize array with string literal of different width");
				if (t->incomplete)
					t->size = expr->type->size;
				goto add;
			case TYPESTRUCT:
			case TYPEUNION:
				if (typecompatible(expr->type, t)) {
					/* GNU: a compound literal of the type initializes the object as its braced list would, so a
					 * static object takes it (the kernel's DEFINE_RAW_SPINLOCK: x = (raw_spinlock_t){ ... }) */
					if (expr->kind == EXPRCOMPOUND && !expr->toeval) {
						struct init *i;

						for (i = expr->u.compound.init; i; i = i->next)
							initadd(&p, mkinit(p.sub->offset + i->start, p.sub->offset + i->end, i->bits, i->expr));
						goto added;
					}
					goto add;
				}
				break;
			default:  /* scalar type */
				assert(t->prop & PROPSCALAR);
				expr = exprassign(expr, t);
				goto add;
			}
			focus(&p);
		}
	add:
		if (p.sub > p.obj && (p.sub[-1].type->kind == TYPESTRUCT || p.sub[-1].type->kind == TYPEUNION))
			bits = p.sub[-1].u.mem->bits;
		else
			bits = (struct bitfield){0};
		initadd(&p, mkinit(p.sub->offset, p.sub->offset + p.sub->type->size, bits, expr));
	added:
		for (;;) {
			if (p.sub->type->incomplete)
				p.sub->type->incomplete = false;
		next:
			rangedone(&p);
			if (!p.cur) {
				if (p.fam)
					initfamsize = p.fam->size;
				return p.init;
			}
			if (tok.kind == TCOMMA) {
				next();
				if (tok.kind != TRBRACE)
					break;
			} else if (tok.kind != TRBRACE) {
				error(&tok.loc, "expected ',' or '}' after initializer");
			}
			next();
			p.sub = p.cur;
			do p.cur = p.cur == p.obj ? NULL : p.cur - 1;
			while (p.cur && !p.cur->iscur);
		}
	}
}
