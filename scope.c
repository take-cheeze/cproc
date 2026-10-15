#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct scope filescope;

void
scopeinit(void)
{
	static struct decl builtins[] = {
		{.name = "__builtin_alloca",      .kind = DECLBUILTIN, .u.builtin = BUILTINALLOCA},
		{.name = "__builtin_constant_p",  .kind = DECLBUILTIN, .u.builtin = BUILTINCONSTANTP},
		{.name = "__builtin_expect",      .kind = DECLBUILTIN, .u.builtin = BUILTINEXPECT},
		{.name = "__builtin_fabsf",      .kind = DECLBUILTIN, .u.builtin = BUILTINFABSF},
		{.name = "__builtin_inff",        .kind = DECLBUILTIN, .u.builtin = BUILTININFF},
		{.name = "__builtin_nanf",        .kind = DECLBUILTIN, .u.builtin = BUILTINNANF},
		{.name = "__builtin_fpclassify", .kind = DECLBUILTIN, .u.builtin = BUILTINFPCLASSIFY},
		{.name = "__builtin_isfinite", .kind = DECLBUILTIN, .u.builtin = BUILTINISFINITE},
		{.name = "__builtin_isgreater", .kind = DECLBUILTIN, .u.builtin = BUILTINISGREATER},
		{.name = "__builtin_isgreaterequal", .kind = DECLBUILTIN, .u.builtin = BUILTINISGREATEREQUAL},
		{.name = "__builtin_isinf", .kind = DECLBUILTIN, .u.builtin = BUILTINISINF},
		{.name = "__builtin_isless", .kind = DECLBUILTIN, .u.builtin = BUILTINISLESS},
		{.name = "__builtin_islessequal", .kind = DECLBUILTIN, .u.builtin = BUILTINISLESSEQUAL},
		{.name = "__builtin_islessgreater", .kind = DECLBUILTIN, .u.builtin = BUILTINISLESSGREATER},
		{.name = "__builtin_isnan", .kind = DECLBUILTIN, .u.builtin = BUILTINISNAN},
		{.name = "__builtin_isnormal", .kind = DECLBUILTIN, .u.builtin = BUILTINISNORMAL},
		{.name = "__builtin_isunordered", .kind = DECLBUILTIN, .u.builtin = BUILTINISUNORDERED},
		{.name = "__builtin_signbit", .kind = DECLBUILTIN, .u.builtin = BUILTINSIGNBIT},
		{.name = "__builtin_offsetof",    .kind = DECLBUILTIN, .u.builtin = BUILTINOFFSETOF},
		{.name = "__builtin_types_compatible_p", .kind = DECLBUILTIN, .u.builtin = BUILTINTYPESCOMPATIBLEP},
		{.name = "__builtin_unreachable", .kind = DECLBUILTIN, .u.builtin = BUILTINUNREACHABLE},
		{.name = "__builtin_va_arg",      .kind = DECLBUILTIN, .u.builtin = BUILTINVAARG},
		{.name = "__builtin_va_copy",     .kind = DECLBUILTIN, .u.builtin = BUILTINVACOPY},
		{.name = "__builtin_va_end",      .kind = DECLBUILTIN, .u.builtin = BUILTINVAEND},
		{.name = "__builtin_va_start",    .kind = DECLBUILTIN, .u.builtin = BUILTINVASTART},
		{.name = "__builtin_c23_va_start", .kind = DECLBUILTIN, .u.builtin = BUILTINVASTART},
		{.name = "__c11_atomic_init", .kind = DECLBUILTIN, .u.builtin = BUILTINC11INIT},
		{.name = "__c11_atomic_load", .kind = DECLBUILTIN, .u.builtin = BUILTINC11LOAD},
		{.name = "__atomic_load_n", .kind = DECLBUILTIN, .u.builtin = BUILTINC11LOAD},
		{.name = "__c11_atomic_store", .kind = DECLBUILTIN, .u.builtin = BUILTINC11STORE},
		{.name = "__atomic_store_n", .kind = DECLBUILTIN, .u.builtin = BUILTINC11STORE},
		{.name = "__c11_atomic_exchange", .kind = DECLBUILTIN, .u.builtin = BUILTINC11XCHG},
		{.name = "__atomic_exchange_n", .kind = DECLBUILTIN, .u.builtin = BUILTINC11XCHG},
		{.name = "__c11_atomic_compare_exchange_strong", .kind = DECLBUILTIN, .u.builtin = BUILTINC11CAS},
		{.name = "__c11_atomic_compare_exchange_weak", .kind = DECLBUILTIN, .u.builtin = BUILTINC11CAS},
		{.name = "__atomic_compare_exchange_n", .kind = DECLBUILTIN, .u.builtin = BUILTINC11CAS},
		{.name = "__c11_atomic_fetch_add", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHADD},
		{.name = "__atomic_fetch_add", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHADD},
		{.name = "__c11_atomic_fetch_sub", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHSUB},
		{.name = "__atomic_fetch_sub", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHSUB},
		{.name = "__c11_atomic_fetch_and", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHAND},
		{.name = "__atomic_fetch_and", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHAND},
		{.name = "__c11_atomic_fetch_or", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHOR},
		{.name = "__atomic_fetch_or", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHOR},
		{.name = "__c11_atomic_fetch_xor", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHXOR},
		{.name = "__atomic_fetch_xor", .kind = DECLBUILTIN, .u.builtin = BUILTINC11FETCHXOR},
	};
	static struct decl valist;
	struct decl *d;

	for (d = builtins; d < builtins + countof(builtins); ++d)
		scopeputdecl(&filescope, d);
	valist.name = "__builtin_va_list";
	valist.kind = DECLTYPE;
	valist.type = targ->typevalist;
	scopeputdecl(&filescope, &valist);
}

struct scope *
mkscope(struct scope *parent)
{
	struct scope *s;

	s = xmalloc(sizeof(*s));
	s->decls.len = 0;
	s->tags.len = 0;
	s->breaklabel = parent->breaklabel;
	s->continuelabel = parent->continuelabel;
	s->switchcases = parent->switchcases;
	s->asanbreak = parent->asanbreak;
	s->asancontinue = parent->asancontinue;
	s->parent = parent;

	return s;
}

struct scope *
delscope(struct scope *s)
{
	struct scope *parent = s->parent;

	if (s->decls.len)
		mapfree(&s->decls, NULL);
	if (s->tags.len)
		mapfree(&s->tags, NULL);
	free(s);

	return parent;
}

struct decl *
scopegetdecl(struct scope *s, const char *name, bool recurse)
{
	struct decl *d;
	struct mapkey k;

	mapkey(&k, name, strlen(name));
	do {
		d = s->decls.len ? mapget(&s->decls, &k, NULL) : NULL;
		s = s->parent;
	} while (!d && s && recurse);

	return d;
}

struct type *
scopegettag(struct scope *s, const char *name, bool recurse)
{
	struct type *t;
	struct mapkey k;

	mapkey(&k, name, strlen(name));
	do {
		t = s->tags.len ? mapget(&s->tags, &k, NULL) : NULL;
		s = s->parent;
	} while (!t && s && recurse);

	return t;
}

void
scopeputdecl(struct scope *s, struct decl *d)
{
	struct mapkey k;
	size_t i;

	if (!s->decls.len)
		mapinit(&s->decls, 32);
	mapkey(&k, d->name, strlen(d->name));
	mapput(&s->decls, &k, &i);
	s->decls.vals[i].p = d;
}

void
scopeputtag(struct scope *s, const char *name, struct type *t)
{
	struct mapkey k;
	size_t i;

	if (!s->tags.len)
		mapinit(&s->tags, 32);
	mapkey(&k, name, strlen(name));
	mapput(&s->tags, &k, &i);
	s->tags.vals[i].p = t;
}
