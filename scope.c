#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct scope filescope;
struct scope *attrscope = &filescope;

/* a builtin that calls the library function symbol: a function of type ret(ptypes...), filed under the builtin's name */
static void
scopeputalias(const char *builtin, char *symbol, struct type *ret, unsigned nparam, struct type **ptypes)
{
	struct decl *f, *arg, *last = NULL;
	struct type *t;
	struct mapkey k;
	size_t i;
	unsigned n;

	t = mktype(TYPEFUNC, 0);
	t->base = ret;
	t->qual = QUALNONE;
	t->u.func.isvararg = false;
	t->u.func.unprototyped = false;
	t->u.func.nparam = nparam;
	t->u.func.params = NULL;
	for (n = 0; n < nparam; ++n) {
		arg = mkdecl(NULL, DECLOBJECT, ptypes[n], QUALNONE, LINKNONE);
		if (last)
			last->next = arg;
		else
			t->u.func.params = arg;
		last = arg;
	}
	f = mkdecl(symbol, DECLFUNC, t, QUALNONE, LINKEXTERN);
	f->value = mkglobal(f);
	mapkey(&k, builtin, strlen(builtin));
	mapput(&filescope.decls, &k, &i);
	filescope.decls.vals[i].p = f;
}

void
scopeinit(void)
{
	static struct decl builtins[] = {
		{.name = "__builtin_alloca",      .kind = DECLBUILTIN, .u.builtin = BUILTINALLOCA},
		{.name = "__builtin_add_overflow", .kind = DECLBUILTIN, .u.builtin = BUILTINADDOVERFLOW},
		{.name = "__builtin_sub_overflow", .kind = DECLBUILTIN, .u.builtin = BUILTINSUBOVERFLOW},
		{.name = "__builtin_mul_overflow", .kind = DECLBUILTIN, .u.builtin = BUILTINMULOVERFLOW},
		{.name = "__builtin_bswap16",     .kind = DECLBUILTIN, .u.builtin = BUILTINBSWAP16},
		{.name = "__builtin_bswap32",     .kind = DECLBUILTIN, .u.builtin = BUILTINBSWAP32},
		{.name = "__builtin_bswap64",     .kind = DECLBUILTIN, .u.builtin = BUILTINBSWAP64},
		{.name = "__builtin_clz", .kind = DECLBUILTIN, .u.builtin = BUILTINCLZ},
		{.name = "__builtin_clzl", .kind = DECLBUILTIN, .u.builtin = BUILTINCLZL},
		{.name = "__builtin_clzll", .kind = DECLBUILTIN, .u.builtin = BUILTINCLZL},
		{.name = "__builtin_ctz", .kind = DECLBUILTIN, .u.builtin = BUILTINCTZ},
		{.name = "__builtin_ctzl", .kind = DECLBUILTIN, .u.builtin = BUILTINCTZL},
		{.name = "__builtin_ctzll", .kind = DECLBUILTIN, .u.builtin = BUILTINCTZL},
		{.name = "__builtin_ffs", .kind = DECLBUILTIN, .u.builtin = BUILTINFFS},
		{.name = "__builtin_ffsl", .kind = DECLBUILTIN, .u.builtin = BUILTINFFSL},
		{.name = "__builtin_ffsll", .kind = DECLBUILTIN, .u.builtin = BUILTINFFSL},
		{.name = "__builtin_parity", .kind = DECLBUILTIN, .u.builtin = BUILTINPARITY},
		{.name = "__builtin_parityl", .kind = DECLBUILTIN, .u.builtin = BUILTINPARITYL},
		{.name = "__builtin_parityll", .kind = DECLBUILTIN, .u.builtin = BUILTINPARITYL},
		{.name = "__builtin_popcount", .kind = DECLBUILTIN, .u.builtin = BUILTINPOPCOUNT},
		{.name = "__builtin_popcountl", .kind = DECLBUILTIN, .u.builtin = BUILTINPOPCOUNTL},
		{.name = "__builtin_popcountll", .kind = DECLBUILTIN, .u.builtin = BUILTINPOPCOUNTL},
		{.name = "__builtin_choose_expr", .kind = DECLBUILTIN, .u.builtin = BUILTINCHOOSEEXPR},
		{.name = "__builtin_constant_p",  .kind = DECLBUILTIN, .u.builtin = BUILTINCONSTANTP},
		{.name = "__builtin_object_size", .kind = DECLBUILTIN, .u.builtin = BUILTINOBJECTSIZE},
		{.name = "__builtin_return_address", .kind = DECLBUILTIN, .u.builtin = BUILTINRETURNADDRESS},
		{.name = "__builtin_extract_return_addr", .kind = DECLBUILTIN, .u.builtin = BUILTINEXTRACTRETURNADDR},
		{.name = "__builtin_isdigit", .kind = DECLBUILTIN, .u.builtin = BUILTINISDIGIT},
		{.name = "__builtin_prefetch", .kind = DECLBUILTIN, .u.builtin = BUILTINPREFETCH},
		{.name = "__builtin_frame_address", .kind = DECLBUILTIN, .u.builtin = BUILTINFRAMEADDRESS},
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
		{.name = "__atomic_load", .kind = DECLBUILTIN, .u.builtin = BUILTINATOMICLOAD},
		{.name = "__atomic_store", .kind = DECLBUILTIN, .u.builtin = BUILTINATOMICSTORE},
		{.name = "__atomic_exchange", .kind = DECLBUILTIN, .u.builtin = BUILTINATOMICXCHG},
		{.name = "__atomic_compare_exchange", .kind = DECLBUILTIN, .u.builtin = BUILTINATOMICCAS},
		{.name = "__atomic_test_and_set", .kind = DECLBUILTIN, .u.builtin = BUILTINATOMICTESTANDSET},
		{.name = "__atomic_clear", .kind = DECLBUILTIN, .u.builtin = BUILTINATOMICCLEAR},
	};
	static struct decl valist;
	struct decl *d;

	for (d = builtins; d < builtins + countof(builtins); ++d)
		scopeputdecl(&filescope, d);
	valist.name = "__builtin_va_list";
	valist.kind = DECLTYPE;
	valist.type = targ->typevalist;
	scopeputdecl(&filescope, &valist);

	/* libc++'s <cstring> and <string> call these (the GCC and clang builtins): each is a call to the library function
	 * of the same name, so the back end names the decl's symbol and the builtin is filed under its own name */
	scopeputalias("__builtin_strstr", "strstr", mkpointertype(&typechar, QUALNONE), 2,
		(struct type *[]){mkpointertype(&typechar, QUALCONST), mkpointertype(&typechar, QUALCONST)});
	/* string functions (C11 7.24.5): libc++'s <string.h> and <string> call these */
	scopeputalias("__builtin_strchr", "strchr", mkpointertype(&typechar, QUALNONE), 2,
		(struct type *[]){mkpointertype(&typechar, QUALCONST), &typeint});
	scopeputalias("__builtin_strrchr", "strrchr", mkpointertype(&typechar, QUALNONE), 2,
		(struct type *[]){mkpointertype(&typechar, QUALCONST), &typeint});
	scopeputalias("__builtin_strpbrk", "strpbrk", mkpointertype(&typechar, QUALNONE), 2,
		(struct type *[]){mkpointertype(&typechar, QUALCONST), mkpointertype(&typechar, QUALCONST)});
	scopeputalias("__builtin_strlen", "strlen", &typeulong, 1,
		(struct type *[]){mkpointertype(&typechar, QUALCONST)});
	/* memory functions (C11 7.24.1): the void * forms libc++'s <cstring> and <string> call */
	scopeputalias("__builtin_memchr", "memchr", mkpointertype(&typevoid, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typevoid, QUALCONST), &typeint, &typeulong});
	scopeputalias("__builtin_memcmp", "memcmp", &typeint, 3,
		(struct type *[]){mkpointertype(&typevoid, QUALCONST), mkpointertype(&typevoid, QUALCONST), &typeulong});
	scopeputalias("__builtin_memmove", "memmove", mkpointertype(&typevoid, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typevoid, QUALNONE), mkpointertype(&typevoid, QUALCONST), &typeulong});
	scopeputalias("__builtin_char_memchr", "memchr", mkpointertype(&typevoid, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typevoid, QUALCONST), &typeint, &typeulong});
	/* the rest of the GCC builtins the Linux kernel's headers call (zstd's bitstream.h: __builtin_memset; fortify) */
	scopeputalias("__builtin_memset", "memset", mkpointertype(&typevoid, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typevoid, QUALNONE), &typeint, &typeulong});
	scopeputalias("__builtin_memcpy", "memcpy", mkpointertype(&typevoid, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typevoid, QUALNONE), mkpointertype(&typevoid, QUALCONST), &typeulong});
	scopeputalias("__builtin_strcpy", "strcpy", mkpointertype(&typechar, QUALNONE), 2,
		(struct type *[]){mkpointertype(&typechar, QUALNONE), mkpointertype(&typechar, QUALCONST)});
	scopeputalias("__builtin_strncpy", "strncpy", mkpointertype(&typechar, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typechar, QUALNONE), mkpointertype(&typechar, QUALCONST), &typeulong});
	scopeputalias("__builtin_strcat", "strcat", mkpointertype(&typechar, QUALNONE), 2,
		(struct type *[]){mkpointertype(&typechar, QUALNONE), mkpointertype(&typechar, QUALCONST)});
	scopeputalias("__builtin_strncat", "strncat", mkpointertype(&typechar, QUALNONE), 3,
		(struct type *[]){mkpointertype(&typechar, QUALNONE), mkpointertype(&typechar, QUALCONST), &typeulong});
	scopeputalias("__builtin_strcmp", "strcmp", &typeint, 2,
		(struct type *[]){mkpointertype(&typechar, QUALCONST), mkpointertype(&typechar, QUALCONST)});
	scopeputalias("__builtin_strncmp", "strncmp", &typeint, 3,
		(struct type *[]){mkpointertype(&typechar, QUALCONST), mkpointertype(&typechar, QUALCONST), &typeulong});
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
	s->labels = NULL;
	s->cleanmark = 0;
	s->cleanbreak = parent->cleanbreak;
	s->cleancontinue = parent->cleancontinue;
	s->stmtexpr = false;

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
