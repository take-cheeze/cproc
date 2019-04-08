#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"
#include "htab.h"

struct context {
	struct token *tok;
	size_t ntok;
	struct macro *macro;
};

struct macroparam {
	struct macroparam *next;
	char *name;
	struct token *tok;
	size_t ntok;
};

struct macro {
	enum {
		MACROOBJECT,
		MACROFUNC,
	} kind;
	bool expand;
	struct macroparam *params;
	struct token *tok;
	size_t ntok;
};

struct array incdirs;

static enum {
	MODEDEFAULT,
	MODEPREPROC,
	MODECONDITION,
} mode;
static struct hashtable *macros;
static size_t macrodepth;
static struct array context;

static void
ctxpush(struct token *t, size_t n, struct macro *m, bool space)
{
	struct context *ctx;

	ctx = arrayadd(&context, sizeof(*ctx));
	ctx->tok = t;
	ctx->ntok = n;
	ctx->macro = m;
	if (n)
		ctx->tok[0].space = space;
	if (m)
		++macrodepth;
}

static void
keyword(struct token *tok)
{
	static const struct {
		const char *name;
		int value;
	} keywords[] = {
		{"_Alignas",       T_ALIGNAS},
		{"_Alignof",       T_ALIGNOF},
		{"_Atomic",        T_ATOMIC},
		{"_Bool",          T_BOOL},
		{"_Complex",       T_COMPLEX},
		{"_Generic",       T_GENERIC},
		{"_Imaginary",     T_IMAGINARY},
		{"_Noreturn",      T_NORETURN},
		{"_Static_assert", T_STATIC_ASSERT},
		{"_Thread_local",  T_THREAD_LOCAL},
		{"__typeof__",     T__TYPEOF__},
		{"auto",           TAUTO},
		{"break",          TBREAK},
		{"case",           TCASE},
		{"char",           TCHAR},
		{"const",          TCONST},
		{"continue",       TCONTINUE},
		{"default",        TDEFAULT},
		{"do",             TDO},
		{"double",         TDOUBLE},
		{"else",           TELSE},
		{"enum",           TENUM},
		{"extern",         TEXTERN},
		{"float",          TFLOAT},
		{"for",            TFOR},
		{"goto",           TGOTO},
		{"if",             TIF},
		{"inline",         TINLINE},
		{"int",            TINT},
		{"long",           TLONG},
		{"register",       TREGISTER},
		{"restrict",       TRESTRICT},
		{"return",         TRETURN},
		{"short",          TSHORT},
		{"signed",         TSIGNED},
		{"sizeof",         TSIZEOF},
		{"static",         TSTATIC},
		{"struct",         TSTRUCT},
		{"switch",         TSWITCH},
		{"typedef",        TTYPEDEF},
		{"union",          TUNION},
		{"unsigned",       TUNSIGNED},
		{"void",           TVOID},
		{"volatile",       TVOLATILE},
		{"while",          TWHILE},
	};
	size_t low = 0, high = LEN(keywords), mid;
	int cmp;

	while (low < high) {
		mid = (low + high) / 2;
		cmp = strcmp(tok->lit, keywords[mid].name);
		if (cmp == 0) {
			//free(tok->lit);
			tok->kind = keywords[mid].value;
			tok->lit = NULL;
			break;
		}
		if (cmp < 0)
			high = mid;
		else
			low = mid + 1;
	}
}

static struct {
	const char *name;
	struct macro macro;
} predef[] = {
	{"__STDC_VERSION__", {
		.kind = MACROOBJECT,
		.expand = true,
		.tok = (struct token []){{.kind = TNUMBER, .lit = "201112L"}},
		.ntok = 1,
	}},
	{"NDEBUG", {
		.kind = MACROOBJECT,
		.expand = true,
		.tok = (struct token []){{.kind = TNUMBER, .lit = "1"}},
		.ntok = 1,
	}},
};

static bool
macroequal(struct macro *m1, struct macro *m2)
{
	struct token *t1, *t2;
	struct macroparam *p1, *p2;

	if (m1->kind != m2->kind)
		return false;
	if (m1->kind == MACROFUNC) {
		for (p1 = m1->params, p2 = m2->params; p1 && p2; p1 = p1->next, p2 = p2->next) {
			if (strcmp(p1->name, p2->name) != 0)
				return false;
		}
		if (p1 || p2)
			return false;
	}
	if (m1->ntok != m2->ntok)
		return false;
	for (t1 = m1->tok, t2 = m2->tok; t1 < &m1->tok[m1->ntok]; ++t1, ++t2) {
		if (t1->kind != t2->kind)
			return false;
		if (t1->lit && strcmp(t1->lit, t2->lit) != 0)
			return false;
	}
	return true;
}

static struct macro *
macroget(char *name)
{
	struct hashtablekey k;

	htabstrkey(&k, name);
	return htabget(macros, &k);
}

static struct macroparam *
macroparam(struct macro *m, struct token *t)
{
	struct macroparam *p;

	/* XXX: hash table? */
	if (t->kind != TIDENT)
		return NULL;
	for (p = m->params; p; p = p->next) {
		if (strcmp(p->name, t->lit) == 0)
			return p;
	}
	return NULL;
}

static void directive(void);

static struct token *
ctxnext(void)
{
	struct context *ctx;
	struct token *t;

	while (context.len) {
		ctx = arraylast(&context, sizeof(*ctx));
		if (ctx->ntok)
			return --ctx->ntok, ctx->tok++;
		if (ctx->macro) {
			ctx->macro->expand = true;
			--macrodepth;
		}
		context.len -= sizeof(*ctx);
	}
	return NULL;
}

static void
define(void)
{
	struct macro *m;
	struct macroparam *p, **end;
	struct token name, *t;
	void **entry;
	struct hashtablekey key;
	struct array repl = {0};

	scan(&name);
	if (name.kind != TIDENT)
		error(&name.loc, "expected identifier after #define");
	m = xmalloc(sizeof(*m));
	m->expand = true;
	m->params = NULL;
	scan(&tok);
	if (tok.kind == TLPAREN && !tok.space) {
		m->kind = MACROFUNC;
		end = &m->params;
		while (scan(&tok), tok.kind == TIDENT) {
			p = xmalloc(sizeof(*p));
			p->name = tok.lit;
			*end = p;
			end = &p->next;
			if (scan(&tok), tok.kind != TCOMMA)
				break;
		}
		*end = NULL;
		if (tok.kind != TRPAREN)
			error(&tok.loc, "expected ')' after macro parameter list");
		scan(&tok);
	} else {
		m->kind = MACROOBJECT;
	}
	tok.space = false;
	arrayaddbuf(&repl, &tok, sizeof(tok));
	t = &tok;
	while (t->kind != TNEWLINE)
		t = arrayadd(&repl, sizeof(*t)), scan(t);
	tok = *(struct token *)arraylast(&repl, sizeof(tok));
	m->tok = repl.val;
	m->ntok = repl.len / sizeof(*t) - 1;

	htabstrkey(&key, name.lit);
	entry = htabput(macros, &key);
	if (!*entry) {
		*entry = m;
	} else if (!macroequal(m, *entry)) {
		error(&name.loc, "redefinition of macro '%s'", name.lit);
		/* XXX: delete new macro */
	}
}

static bool
cond(void)
{
	uint64_t i;
	int old;

	old = mode;
	mode = MODECONDITION;
	next();
	i = intconstexpr(&filescope, true);
	mode = old;
	return i;
}

static bool
includefile(const char *dir, char *name)
{
	char *path;

	if (dir)
		xasprintf(&path, "%s/%s", dir, name);
	else
		path = name;
	if (scanfrom(path) == 0)
		return true;
	free(path);
	return false;
}

static char *
dirname(const char *path)
{
	const char *slash;
	char *dir;
	size_t n;

	slash = strrchr(path, '/');
	if (!slash)
		return NULL;
	n = slash - path;
	dir = xmalloc(n + 1);
	memcpy(dir, path, n);
	dir[n] = '\0';
	return dir;
}

static void
include(void)
{
	char *path, **dir;
	enum tokenkind k;

	scanflags |= SCANHEADER;
	scan(&tok);
	scanflags &= ~SCANHEADER;
	k = tok.kind;
	if (k != TLOCHDR && k != TSYSHDR)
		error(&tok.loc, "unsupported include directive");
	path = tok.lit + 1;
	path[strlen(path) - 1] = '\0';
	scan(&tok);
	if (k == TSYSHDR || !includefile(dirname(tok.loc.file), path)) {
		for (dir = incdirs.val; dir < (char **)incdirs.val + incdirs.len / sizeof(*dir); ++dir) {
			if (includefile(*dir, path))
				goto found;
		}
		error(&tok.loc, "could not find include '%s'", path);
	}
found:
	free(path - 1);
}

static void
undef(void)
{
	void **entry;
	struct macro *m;
	struct hashtablekey k;

	scan(&tok);
	if (tok.kind != TIDENT)
		error(&tok.loc, "expected identifier after '#undef'");
	htabstrkey(&k, tok.lit);
	entry = htabput(macros, &k);
	//free(tok.lit);
	m = *entry;
	if (m) {
		free(m->tok);
		free(m);
		*entry = NULL;
	}
	scan(&tok);
}

static void
skipgroup(bool found)
{
	bool newline;
	int depth = 0;

	for (;;) {
		newline = tok.kind == TNEWLINE;
		scan(&tok);
		if (tok.kind != THASH || !newline)
			continue;
		scan(&tok);
		if (tok.kind == TNEWLINE)
			continue;
		if (tok.kind != TIDENT)
			error(&tok.loc, "expected newline or identifier after '#'");
		if (strcmp(tok.lit, "if") == 0) {
			++depth;
		} else if (strcmp(tok.lit, "endif") == 0) {
			if (depth == 0) {
				scan(&tok);
				break;
			}
			--depth;
		} else if (depth || found) {
			continue;
		} else if (strcmp(tok.lit, "else") == 0) {
			scan(&tok);
			break;
		} else if (strcmp(tok.lit, "elif") == 0 && cond()) {
			break;
		}
	}
	if (tok.kind != TNEWLINE)
		error(&tok.loc, "expected newline after directive");
}

static void
directive(void)
{
	static bool newline = true;
	char *name;
	bool found = true, skip = false;

	scan(&tok);
	if (tok.kind == TNEWLINE)
		return;
	if (tok.kind != TIDENT)
		error(&tok.loc, "expected newline or identifier after '#'");
	name = tok.lit;
	if (strcmp(name, "define") == 0) {
		define();
	} else if (strcmp(name, "elif") == 0) {
		cond();
		skip = true;
	} else if (strcmp(name, "else") == 0) {
		skip = true;
		scan(&tok);
	} else if (strcmp(name, "endif") == 0) {
		scan(&tok);
	} else if (strcmp(name, "if") == 0) {
		found = cond();
		skip = !found;
	} else if (strcmp(name, "ifdef") == 0) {
		scan(&tok);
		if (tok.kind != TIDENT)
			error(&tok.loc, "expected identifier after #ifdef");
		found = macroget(tok.lit);
		skip = !found;
		free(tok.lit);
		scan(&tok);
	} else if (strcmp(name, "ifndef") == 0) {
		scan(&tok);
		if (tok.kind != TIDENT)
			error(&tok.loc, "expected identifier after #ifdef");
		found = !macroget(tok.lit);
		skip = !found;
		free(tok.lit);
		scan(&tok);
	} else if (strcmp(name, "include") == 0) {
		include();
	} else if (strcmp(name, "undef") == 0) {
		undef();
	} else {
		error(&tok.loc, "invalid directive '%s'", name);
	}
	if (tok.kind != TNEWLINE)
		error(&tok.loc, "expected newline after directive");
	free(name);
	if (skip)
		skipgroup(found);
}

static bool
defined(void)
{
	struct token t;
	struct macro *m;
	bool paren = false;

	assert(context.len == 0);
	scan(&t);
	if (t.kind == TLPAREN)
		paren = true, scan(&t);
	if (t.kind != TIDENT)
		error(&t.loc, "expected identifier after 'defined'");
	m = macroget(t.lit);
	if (paren) {
		scan(&t);
		if (t.kind != TRPAREN)
			error(&t.loc, "expected ')' after identifier");
	}
	return m;
}

static struct token *
rawnext(void)
{
	static bool newline = true;
	struct token *t;

	t = ctxnext();
	if (t)
		return t;
	for (;;) {
		do scan(&tok);
		while (mode == MODEDEFAULT && tok.kind == TNEWLINE);
		if (tok.kind != THASH || !newline)
			break;
		directive();
	}
	return &tok;
}

static bool
peekparen(void)
{
	static struct array pending;
	struct token *t;
	struct context *ctx;

	t = ctxnext();
	if (t) {
		if (t->kind == TLPAREN)
			return true;
		ctx = arraylast(&context, sizeof(*ctx));
		if (ctx) {
			--ctx->tok;
			++ctx->ntok;
		}
		return false;
	}
	pending.len = 0;
	do t = arrayadd(&pending, sizeof(*t)), scan(t);
	while (t->kind == TNEWLINE);
	if (t->kind == TLPAREN)
		return true;
	ctxpush(pending.val, pending.len / sizeof(*t), NULL, false);
	return false;
}

static bool
expand(struct token *t)
{
	char *name;
	struct context *ctx;
	struct macro *m;
	struct macroparam *p;
	struct array repl = {0};
	int paren;
	bool space;
	size_t depth;

	if (t->kind != TIDENT)
		return false;
	if (mode == MODECONDITION && strcmp(t->lit, "defined") == 0) {
		t->kind = TNUMBER;
		t->lit = defined() ? "1" : "0";
		return false;
	}
	ctx = arraylast(&context, sizeof(*ctx));
	if (ctx && ctx->macro) {
		if (t->kind == THASH)
			error(&t->loc, "preprocessor '#' operator not implemented");
		if (t->kind == THASHHASH)
			error(&t->loc, "preprocessor '##' operator not implemented");
		p = macroparam(ctx->macro, t);
		if (p) {
			ctxpush(p->tok, p->ntok, NULL, t->space);
			return true;
		}
	}
	name = t->lit;
	m = macroget(name);
	if (!m || !t->expand) {
		if (mode == MODECONDITION) {
			t->kind = TNUMBER;
			t->lit = "0";
		}
		return false;
	}
	if (!m->expand) {
		t->expand = false;
		return false;
	}
	space = t->space;
	if (m->kind == MACROFUNC) {
		if (!peekparen())
			return false;
		paren = 0;
		depth = macrodepth;
		for (p = m->params; p; p = p->next) {
			for (;;) {
				t = rawnext();
				if (depth >= macrodepth) {
					depth = macrodepth;
					if (t->kind == TEOF || paren == 0 && (t->kind == TCOMMA || t->kind == TRPAREN))
						break;
					switch (t->kind) {
					case TLPAREN: ++paren; break;
					case TRPAREN: --paren; break;
					}
				}
				if (!expand(t))
					arrayaddbuf(&repl, t, sizeof(*t));
			}
			p->tok = repl.val;
			p->ntok = repl.len / sizeof(*t);
			repl = (struct array){0};
		}
		if (p && p->next)
			error(&t->loc, "not enough parameters for macro");
		if (t->kind != TRPAREN)
			error(&t->loc, "expected ')' after macro parameters");
	}
	ctxpush(m->tok, m->ntok, m, space);
	m->expand = false;
	return true;
}

static void
dumpctx(void)
{
	struct context *ctx;
	struct token *t;

	arrayforeach (&context, ctx) {
		fputs(" [ ", stdout);
		for (t = ctx->tok; t < &ctx->tok[ctx->ntok]; ++t)
			tokprint(t);
		fputs(" ]", stdout);
	}
	putchar('\n');
}

void
next(void)
{
	struct token *t;

	do t = rawnext();
	while (expand(t));
	tok = *t;
	if (tok.kind == TIDENT)
		keyword(&tok);
}

bool
peek(int kind)
{
	static struct token pending;
	struct token old;

	old = tok;
	next();
	if (tok.kind == kind) {
		next();
		return true;
	}
	pending = tok;
	ctxpush(&pending, 1, NULL, pending.space);
	tok = old;
	return false;
}

void
ppinit(const char *file, bool pponly)
{
	size_t i;
	struct hashtablekey k;

	macros = mkhtab(32);
	for (i = 0; i < LEN(predef); ++i) {
		htabstrkey(&k, predef[i].name);
		*htabput(macros, &k) = &predef[i].macro;
	}
	if (scanfrom(file) < 0)
		fatal("open %s:", file);
	if (pponly)
		mode = MODEPREPROC;
	next();
}

char *
expect(int kind, const char *msg)
{
	char *lit;

	if (tok.kind != kind)
		error(&tok.loc, "expected %d %s, saw %d", kind, msg, tok.kind);
	lit = tok.lit;
	next();

	return lit;
}

bool
consume(int kind)
{
	if (tok.kind != kind)
		return false;
	next();
	return true;
}
