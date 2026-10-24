#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

/* An asm section separator. The scanner lexes adjacent colons (as in "":::"memory") as a single TCOLONCOLON, so a
 * '::' is consumed as one colon here and left as a TCOLON for the next call. Returns false when no separator is next. */
static bool
asmsep(void)
{
	if (tok.kind == TCOLONCOLON) {
		tok.kind = TCOLON;
		return true;
	}
	if (tok.kind == TCOLON) {
		next();
		return true;
	}
	return false;
}

/* the name a label goes by in the function: a GNU local label (__label__) of an enclosing block has its own */
static char *
labelname(struct scope *s, char *name)
{
	struct locallabel *l;

	for (; s; s = s->parent)
		for (l = s->labels; l; l = l->next)
			if (strcmp(l->name, name) == 0)
				return l->unique;
	return name;
}

/* 6.8.1 Labeled statements */
static bool
label(struct func *f, struct scope *s)
{
	char *name;
	struct gotolabel *g;
	struct block *b;
	unsigned long long i;

	attr(NULL, 0);
	switch (tok.kind) {
	case TCASE:
		next();
		if (!s->switchcases)
			error(&tok.loc, "'case' label must be in switch");
		b = mkblock("switch_case");
		funclabel(f, b);
		asancase(f, s->switchcases);
		i = intconstexpr(s, true);
		if (consume(TELLIPSIS)) {
			/* GNU case range: case LO ... HI. The dispatch compares unsigned, so a signed range across zero is two */
			unsigned long long j = intconstexpr(s, true);
			bool sign = s->switchcases->type->u.arith.issigned;

			if (sign ? (long long)i <= (long long)j : i <= j) {
				if (i <= j) {
					switchcase(s->switchcases, i, j, b);
				} else {
					switchcase(s->switchcases, i, -1, b);
					switchcase(s->switchcases, 0, j, b);
				}
			}
		} else {
			switchcase(s->switchcases, i, i, b);
		}
		expect(TCOLON, "after case expression");
		break;
	case TDEFAULT:
		next();
		if (!s->switchcases)
			error(&tok.loc, "'default' label must be in switch");
		if (s->switchcases->defaultlabel)
			error(&tok.loc, "multiple 'default' labels");
		expect(TCOLON, "after 'default'");
		s->switchcases->defaultlabel = mkblock("switch_default");
		funclabel(f, s->switchcases->defaultlabel);
		asancase(f, s->switchcases);
		break;
	default:
		if (!iscident(tok.kind))
			return false;
		name = tokenstr(tok.kind);
		if (strcmp(name, "__label__") == 0) {
			/* GNU: __label__ a, b; declares labels local to the block (macros that expand twice use them) */
			static unsigned id;

			next();
			do {
				struct locallabel *l = xmalloc(sizeof *l);

				l->name = expect(TIDENT, "in __label__ declaration");
				l->unique = xmalloc(strlen(l->name) + 16);
				sprintf(l->unique, "%s.local%u", l->name, ++id);
				l->next = s->labels;
				s->labels = l;
			} while (consume(TCOMMA));
			expect(TSEMICOLON, "after __label__ declaration");
			return true;
		}
		if (!peek(TCOLON))
			return false;
		g = funcgoto(f, labelname(s, name));
		g->defined = true;
		funclabel(f, g->label);
		asanlabel(f, g);
		funclabeldefined(f, g);
		break;
	}
	return true;
}

static void
labelstmt(struct func *f, struct scope *s)
{
	while (label(f, s))
		;
	stmt(f, s);
}

/*
The body of a GNU statement expression ({ ... }), parsed into the current (detached) blocks: declarations and
statements as in a compound statement, except that the last expression statement is not evaluated here -- its tree
is the expression's value, evaluated where the statement expression is (funcexpr). Returns null when the body does not
end in an expression statement (the value is void).
*/
struct expr *
stmtexpr(struct func *f, struct scope *s)
{
	struct expr *e, *v = NULL;

	expect(TLBRACE, "to begin statement expression");
	s = mkscope(s);
	s->stmtexpr = true;
	s->cleanmark = funccleanmark(f);
	while (tok.kind != TRBRACE) {
		v = NULL;
		if (label(f, s) || decl(s, f))
			continue;
		switch (tok.kind) {
		case TLBRACE: case TSEMICOLON: case TIF: case TSWITCH: case TWHILE: case TDO: case TFOR:
		case TGOTO: case TCONTINUE: case TBREAK: case TRETURN: case T__ASM__: case TLBRACK:
			stmt(f, s);
			continue;
		default:
			break;
		}
		e = expr(s);
		expect(TSEMICOLON, "after expression statement");
		if (tok.kind == TRBRACE) {
			v = e;
			break;
		}
		funcexpr(f, e);
		delexpr(e);
	}
	s = delscope(s);
	expect(TRBRACE, "to end statement expression");
	return v;
}

/* a block scope; under cproc -G its cleanup objects leave with it (qbe.c funccleanpop) */
static struct scope *
enterscope(struct func *f, struct scope *s)
{
	s = mkscope(s);
	s->cleanmark = funccleanmark(f);
	return s;
}

static struct scope *
leavescope(struct func *f, struct scope *s)
{
	if (gnucleanup)
		funccleanpop(f, s->cleanmark);
	return delscope(s);
}

/* 6.8 Statements and blocks */
void
stmt(struct func *f, struct scope *s)
{
	char *name;
	struct expr *e;
	struct type *t;
	struct value *v;
	struct block *b[4];
	struct switchcases swtch;
	struct gotolabel *g;

	attr(NULL, 0);
	switch (tok.kind) {
	/* 6.8.2 Compound statement */
	case TLBRACE: {
		struct funcshape *sh = funcshape(f);
		bool top = sh->depth++ == 0;   /* the function's body */

		next();
		s = enterscope(f, s);
		asanbegin(f);
		while (tok.kind != TRBRACE) {
			if (top && ++sh->items == 1)
				sh->firstreturn = tok.kind == TRETURN;
			if (!label(f, s) && !decl(s, f))
				stmt(f, s);
		}
		asanend(f);
		s = leavescope(f, s);
		next();
		if (top && (sh->items != 1 || !sh->firstreturn))
			sh->constret = false;
		if (top && sh->constret) {
			funcdecl(f)->u.func.constret = true;
			funcdecl(f)->u.func.retval = sh->retval;
		}
		if (top && sh->items == 0 && functype(f)->base == &typevoid)
			funcdecl(f)->u.func.emptybody = true;
		--sh->depth;
		break;
	}

	/* 6.8.3 Expression statement */
	case TSEMICOLON:
		next();
		break;
	default:
		e = expr(s);
		v = funcexpr(f, e);
		delexpr(e);
		expect(TSEMICOLON, "after expression statement");
		break;

	/* 6.8.4 Selection statement */
	case TIF:
		next();
		s = enterscope(f, s);
		expect(TLPAREN, "after 'if'");
		e = expr(s);
		t = e->type;
		if (!(t->prop & PROPSCALAR))
			error(&tok.loc, "controlling expression of if statement must have scalar type");
		b[0] = mkblock("if_true");
		b[1] = mkblock("if_false");
		funcbranch(f, e, b[0], b[1]);
		delexpr(e);
		expect(TRPAREN, "after expression");

		funclabel(f, b[0]);
		s = enterscope(f, s);
		labelstmt(f, s);
		s = leavescope(f, s);

		if (consume(TELSE)) {
			b[2] = mkblock("if_join");
			funcjmp(f, b[2]);
			funclabel(f, b[1]);
			s = enterscope(f, s);
			labelstmt(f, s);
			s = leavescope(f, s);
			funclabel(f, b[2]);
		} else {
			funclabel(f, b[1]);
		}
		s = leavescope(f, s);
		break;
	case TSWITCH:
		next();

		s = enterscope(f, s);
		expect(TLPAREN, "after 'switch'");
		e = expr(s);
		expect(TRPAREN, "after expression");

		if (!(e->type->prop & PROPINT))
			error(&tok.loc, "controlling expression of switch statement must have integer type");
		e = exprpromote(e);

		swtch.root = NULL;
		swtch.type = e->type;
		swtch.defaultlabel = NULL;
		asanswitch(f, &swtch);

		b[0] = mkblock("switch_cond");
		b[1] = mkblock("switch_join");

		v = funcexpr(f, e);
		funcjmp(f, b[0]);
		s = enterscope(f, s);
		s->breaklabel = b[1];
		s->switchcases = &swtch;
		s->asanbreak = asanmark(f);
		s->cleanbreak = funccleanmark(f);
		labelstmt(f, s);
		funcjmp(f, b[1]);

		funclabel(f, b[0]);
		funcswitch(f, v, &swtch, swtch.defaultlabel ? swtch.defaultlabel : b[1]);
		s = leavescope(f, s);

		funclabel(f, b[1]);
		s = leavescope(f, s);
		break;

	/* 6.8.5 Iteration statements */
	case TWHILE:
		next();
		s = enterscope(f, s);
		expect(TLPAREN, "after 'while'");
		e = expr(s);
		t = e->type;
		if (!(t->prop & PROPSCALAR))
			error(&tok.loc, "controlling expression of loop must have scalar type");
		expect(TRPAREN, "after expression");

		b[0] = mkblock("while_cond");
		b[1] = mkblock("while_body");
		b[2] = mkblock("while_join");

		funclabel(f, b[0]);
		funcbranch(f, e, b[1], b[2]);
		funclabel(f, b[1]);
		s = enterscope(f, s);
		s->continuelabel = b[0];
		s->breaklabel = b[2];
		s->asanbreak = s->asancontinue = asanmark(f);
		s->cleanbreak = s->cleancontinue = funccleanmark(f);
		labelstmt(f, s);
		s = leavescope(f, s);
		funcjmp(f, b[0]);
		funclabel(f, b[2]);
		s = leavescope(f, s);
		break;
	case TDO:
		next();

		b[0] = mkblock("do_body");
		b[1] = mkblock("do_cond");
		b[2] = mkblock("do_join");

		s = enterscope(f, s);
		s = enterscope(f, s);
		s->continuelabel = b[1];
		s->breaklabel = b[2];
		s->asanbreak = s->asancontinue = asanmark(f);
		s->cleanbreak = s->cleancontinue = funccleanmark(f);
		funclabel(f, b[0]);
		labelstmt(f, s);
		s = leavescope(f, s);

		expect(TWHILE, "after 'do' statement");
		expect(TLPAREN, "after 'while'");
		funclabel(f, b[1]);
		e = expr(s);
		t = e->type;
		if (!(t->prop & PROPSCALAR))
			error(&tok.loc, "controlling expression of loop must have scalar type");
		expect(TRPAREN, "after expression");

		funcbranch(f, e, b[0], b[2]);
		funclabel(f, b[2]);
		s = leavescope(f, s);
		expect(TSEMICOLON, "after 'do' statement");
		break;
	case TFOR:
		next();
		expect(TLPAREN, "after 'for'");
		s = enterscope(f, s);
		asanbegin(f);
		if (!decl(s, f)) {
			if (tok.kind != TSEMICOLON) {
				e = expr(s);
				funcexpr(f, e);
				delexpr(e);
			}
			expect(TSEMICOLON, NULL);
		}

		b[0] = mkblock("for_cond");
		b[1] = mkblock("for_body");
		b[2] = mkblock("for_cont");
		b[3] = mkblock("for_join");

		funclabel(f, b[0]);
		if (tok.kind != TSEMICOLON) {
			e = expr(s);
			t = e->type;
			if (!(t->prop & PROPSCALAR))
				error(&tok.loc, "controlling expression of loop must have scalar type");
			funcbranch(f, e, b[1], b[3]);
			delexpr(e);
		}
		expect(TSEMICOLON, NULL);
		e = tok.kind == TRPAREN ? NULL : expr(s);
		expect(TRPAREN, NULL);

		funclabel(f, b[1]);
		s = enterscope(f, s);
		s->breaklabel = b[3];
		s->continuelabel = b[2];
		s->asanbreak = s->asancontinue = asanmark(f);
		s->cleanbreak = s->cleancontinue = funccleanmark(f);
		labelstmt(f, s);
		s = leavescope(f, s);

		funclabel(f, b[2]);
		if (e) {
			funcexpr(f, e);
			delexpr(e);
		}
		funcjmp(f, b[0]);
		funclabel(f, b[3]);
		asanend(f);
		s = leavescope(f, s);
		break;

	/* 6.8.6 Jump statements */
	case TGOTO:
		next();
		name = expect(TIDENT, "after 'goto'");
		g = funcgoto(f, labelname(s, name));
		asangoto(f, g);
		funcjmp(f, funcgototarget(f, g));   /* -G: through the cleanups of the scopes it leaves */
		expect(TSEMICOLON, "after 'goto' statement");
		break;
	case TCONTINUE:
		next();
		if (!s->continuelabel)
			error(&tok.loc, "'continue' statement must be in loop");
		asanleave(f, s->asancontinue);
		if (gnucleanup)
			funccleanleave(f, s->cleancontinue);
		funcjmp(f, s->continuelabel);
		expect(TSEMICOLON, "after 'continue' statement");
		break;
	case TBREAK:
		next();
		if (!s->breaklabel)
			error(&tok.loc, "'break' statement must be in loop or switch");
		asanleave(f, s->asanbreak);
		if (gnucleanup)
			funccleanleave(f, s->cleanbreak);
		funcjmp(f, s->breaklabel);
		expect(TSEMICOLON, "after 'break' statement");
		break;
	case TRETURN:
		next();
		t = functype(f);
		if (t->base != &typevoid) {
			e = exprassign(expr(s), t->base);
			if (funcshape(f)->depth == 1 && funcshape(f)->items == 1) {   /* the body's first item: { return C; }? */
				struct expr *c = eval(e);

				if (c->kind == EXPRCONST && t->base->prop & PROPINT && !(t->base->prop & PROPSOFT)) {
					funcshape(f)->constret = true;
					funcshape(f)->retval = c->u.constant.u;
				}
				e = c;
			}
			v = funcexpr(f, e);
			delexpr(e);
		} else {
			/* GNU: a void function may return a void expression (return put_unaligned_le16(...);) */
			if (tok.kind != TSEMICOLON) {
				e = expr(s);
				if (e->type->kind != TYPEVOID)
					error(&tok.loc, "return with a value in a function returning void");
				funcexpr(f, e);
				delexpr(e);
			}
			v = NULL;
		}
		if (gnucleanup)   /* the value first, then the cleanups of every scope the return leaves */
			funccleanleave(f, 0);
		funcret(f, v);
		expect(TSEMICOLON, "after 'return' statement");
		break;

	case T__ASM__: {
		/* GNU extended asm: __asm__ [volatile] ( template [: outputs [: inputs [: clobbers]]] ) ; */
		struct asmoperand out[16], in[16];
		struct gotolabel *labels[16];
		char *clob[16], *labnames[16], *template;
		unsigned nout = 0, nin = 0, nclob = 0, nlab = 0;
		bool isvol = false, isgoto = false, basic;
		struct stringlit lit;

		next();
		while (tok.kind == TVOLATILE || tok.kind == TINLINE || tok.kind == TGOTO) {
			if (tok.kind == TVOLATILE)
				isvol = true;
			if (tok.kind == TGOTO)
				isgoto = true;
			next();
		}
		expect(TLPAREN, "after 'asm'");
		tokencheck(&tok, TSTRINGLIT, "for asm template");
		stringconcat(&lit, true);
		template = lit.data;
		basic = tok.kind != TCOLON && tok.kind != TCOLONCOLON;
		/* outputs, then inputs: each is [ [symbol] ] "constraint" ( operand ) */
		for (unsigned sect = 0; sect < 2 && asmsep(); ++sect) {
			struct asmoperand *ops = sect == 0 ? out : in;
			unsigned *n = sect == 0 ? &nout : &nin;
			while (tok.kind == TLBRACK || tok.kind == TSTRINGLIT) {
				char *sym = NULL;
				if (consume(TLBRACK)) {
					sym = expect(TIDENT, "for asm operand name");
					expect(TRBRACK, "after asm operand name");
				}
				tokencheck(&tok, TSTRINGLIT, "for asm operand constraint");
				stringconcat(&lit, true);
				if (*n == 16)
					error(&tok.loc, "too many asm operands");
				ops[*n].constraint = lit.data;
				ops[*n].symname = sym;
				expect(TLPAREN, "before asm operand");
				ops[*n].expr = assignexpr(s);
				expect(TRPAREN, "after asm operand");
				++*n;
				if (!consume(TCOMMA))
					break;
			}
		}
		/* clobbers */
		if (asmsep()) {
			while (tok.kind == TSTRINGLIT) {
				stringconcat(&lit, true);
				if (nclob == 16)
					error(&tok.loc, "too many asm clobbers");
				clob[nclob++] = lit.data;
				if (!consume(TCOMMA))
					break;
			}
		}
		/* asm goto: the labels the template may jump to */
		if (isgoto && asmsep()) {
			while (tok.kind >= TIDENT) {
				if (nlab == 16)
					error(&tok.loc, "too many asm goto labels");
				labnames[nlab] = expect(TIDENT, "for asm goto label");
				labels[nlab] = funcgoto(f, labelname(s, labnames[nlab]));
				++nlab;
				if (!consume(TCOMMA))
					break;
			}
		}
		if (tok.kind == TCOLON || tok.kind == TCOLONCOLON)
			error(&tok.loc, isgoto ? "expected ')' after the asm goto labels" : "asm labels need 'asm goto'");
		if (basic) {
			/* basic asm (no operands): the text is the template as it is, with no '%' substitution
			 * (the kernel's io_delay: asm volatile("outb %al, $0x80")) */
			size_t n = 0;
			char *q, *e;

			for (q = template; *q; ++q)
				n += *q == '%';
			e = xmalloc(strlen(template) + n + 1);
			for (q = template, n = 0; *q; ++q) {
				e[n++] = *q;
				if (*q == '%')
					e[n++] = '%';
			}
			e[n] = 0;
			template = e;
		}
		/* an input tied to an output by name ("[sum]"(rest)) is tied by number, as "0" */
		for (unsigned k = 0; k < nin; ++k) {
			const char *c = in[k].constraint;
			bool found = false;

			if (*c != '[')
				continue;
			for (unsigned o = 0; o < nout && !found; ++o) {
				size_t len = out[o].symname ? strlen(out[o].symname) : 0;

				if (len && strncmp(c + 1, out[o].symname, len) == 0 && c[1 + len] == ']' && !c[2 + len]) {
					char *num = xmalloc(12);

					snprintf(num, 12, "%u", o);
					in[k].constraint = num;
					found = true;
				}
			}
			if (!found)
				error(&tok.loc, "asm input constraint '%s' names no output", c);
		}
		expect(TRPAREN, "after asm");
		expect(TSEMICOLON, "after asm statement");
		if (f)
			funcasm(f, template, out, nout, in, nin, clob, nclob, isvol || isgoto, labels, labnames, nlab);
		else
			error(&tok.loc, "file-scope asm is not yet supported");
		break;
	}
	}
}
