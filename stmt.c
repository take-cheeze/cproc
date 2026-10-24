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
		switchcase(s->switchcases, i, b);
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
		if (!peek(TCOLON))
			return false;
		g = funcgoto(f, name);
		g->defined = true;
		funclabel(f, g->label);
		asanlabel(f, g);
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
The items of a GNU statement expression's braces. Declarations and statements are emitted as in a compound statement; the
last item, if it is an expression statement, is returned unevaluated: it gives the value of the statement expression.
*/
struct expr *
stmtblock(struct func *f, struct scope *s)
{
	struct expr *last = NULL;

	next();
	s = mkscope(s);
	while (tok.kind != TRBRACE) {
		if (last) {
			funcexpr(f, last);
			delexpr(last);
			last = NULL;
		}
		attr(NULL, 0);
		if (label(f, s) || decl(s, f))
			continue;
		switch (tok.kind) {
		case TLBRACE: case TSEMICOLON: case TIF: case TSWITCH: case TWHILE: case TDO: case TFOR:
		case TGOTO: case TCONTINUE: case TBREAK: case TRETURN: case T__ASM__:
			stmt(f, s);
			continue;
		}
		last = expr(s);
		expect(TSEMICOLON, "after expression statement");
	}
	s = delscope(s);
	next();
	return last;
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
	case TLBRACE:
		next();
		s = mkscope(s);
		asanbegin(f);
		while (tok.kind != TRBRACE) {
			if (!label(f, s) && !decl(s, f))
				stmt(f, s);
		}
		asanend(f);
		s = delscope(s);
		next();
		break;

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
		s = mkscope(s);
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
		s = mkscope(s);
		labelstmt(f, s);
		s = delscope(s);

		if (consume(TELSE)) {
			b[2] = mkblock("if_join");
			funcjmp(f, b[2]);
			funclabel(f, b[1]);
			s = mkscope(s);
			labelstmt(f, s);
			s = delscope(s);
			funclabel(f, b[2]);
		} else {
			funclabel(f, b[1]);
		}
		s = delscope(s);
		break;
	case TSWITCH:
		next();

		s = mkscope(s);
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
		s = mkscope(s);
		s->breaklabel = b[1];
		s->switchcases = &swtch;
		s->asanbreak = asanmark(f);
		labelstmt(f, s);
		funcjmp(f, b[1]);

		funclabel(f, b[0]);
		funcswitch(f, v, &swtch, swtch.defaultlabel ? swtch.defaultlabel : b[1]);
		s = delscope(s);

		funclabel(f, b[1]);
		s = delscope(s);
		break;

	/* 6.8.5 Iteration statements */
	case TWHILE:
		next();
		s = mkscope(s);
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
		s = mkscope(s);
		s->continuelabel = b[0];
		s->breaklabel = b[2];
		s->asanbreak = s->asancontinue = asanmark(f);
		labelstmt(f, s);
		s = delscope(s);
		funcjmp(f, b[0]);
		funclabel(f, b[2]);
		s = delscope(s);
		break;
	case TDO:
		next();

		b[0] = mkblock("do_body");
		b[1] = mkblock("do_cond");
		b[2] = mkblock("do_join");

		s = mkscope(s);
		s = mkscope(s);
		s->continuelabel = b[1];
		s->breaklabel = b[2];
		s->asanbreak = s->asancontinue = asanmark(f);
		funclabel(f, b[0]);
		labelstmt(f, s);
		s = delscope(s);

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
		s = delscope(s);
		expect(TSEMICOLON, "after 'do' statement");
		break;
	case TFOR:
		next();
		expect(TLPAREN, "after 'for'");
		s = mkscope(s);
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
		s = mkscope(s);
		s->breaklabel = b[3];
		s->continuelabel = b[2];
		s->asanbreak = s->asancontinue = asanmark(f);
		labelstmt(f, s);
		s = delscope(s);

		funclabel(f, b[2]);
		if (e) {
			funcexpr(f, e);
			delexpr(e);
		}
		funcjmp(f, b[0]);
		funclabel(f, b[3]);
		asanend(f);
		s = delscope(s);
		break;

	/* 6.8.6 Jump statements */
	case TGOTO:
		next();
		name = expect(TIDENT, "after 'goto'");
		g = funcgoto(f, name);
		asangoto(f, g);
		funcjmp(f, g->label);
		expect(TSEMICOLON, "after 'goto' statement");
		break;
	case TCONTINUE:
		next();
		if (!s->continuelabel)
			error(&tok.loc, "'continue' statement must be in loop");
		asanleave(f, s->asancontinue);
		funcjmp(f, s->continuelabel);
		expect(TSEMICOLON, "after 'continue' statement");
		break;
	case TBREAK:
		next();
		if (!s->breaklabel)
			error(&tok.loc, "'break' statement must be in loop or switch");
		asanleave(f, s->asanbreak);
		funcjmp(f, s->breaklabel);
		expect(TSEMICOLON, "after 'break' statement");
		break;
	case TRETURN:
		next();
		t = functype(f);
		if (t->base != &typevoid) {
			e = exprassign(expr(s), t->base);
			v = funcexpr(f, e);
			delexpr(e);
		} else {
			v = NULL;
		}
		funcret(f, v);
		expect(TSEMICOLON, "after 'return' statement");
		break;

	case T__ASM__: {
		/* GNU extended asm: __asm__ [volatile] ( template [: outputs [: inputs [: clobbers]]] ) ; */
		struct asmoperand out[16], in[16];
		char *clob[16], *template;
		unsigned nout = 0, nin = 0, nclob = 0;
		bool isvol = false;
		struct stringlit lit;

		next();
		while (tok.kind == TVOLATILE || tok.kind == TINLINE) {
			if (tok.kind == TVOLATILE)
				isvol = true;
			next();
		}
		if (tok.kind == TGOTO)
			error(&tok.loc, "'asm goto' is not yet supported");
		expect(TLPAREN, "after 'asm'");
		tokencheck(&tok, TSTRINGLIT, "for asm template");
		stringconcat(&lit, true);
		template = lit.data;
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
		if (tok.kind == TCOLON || tok.kind == TCOLONCOLON)
			error(&tok.loc, "'asm goto' is not yet supported");
		expect(TRPAREN, "after asm");
		expect(TSEMICOLON, "after asm statement");
		if (f)
			funcasm(f, template, out, nout, in, nin, clob, nclob, isvol);
		else
			error(&tok.loc, "file-scope asm is not yet supported");
		break;
	}
	}
}
