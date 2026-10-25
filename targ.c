#include <stdbool.h>
#include <string.h>
#include "util.h"
#include "cc.h"

const struct target *targ;

static const struct target alltargs[] = {
	{
		.name = "x86_64-sysv",
		.typewchar = &typeint,
		.typevalist = &(struct type){
			.kind = TYPEARRAY,
			.align = 8, .size = 24,
			.base = &(struct type){
				.kind = TYPESTRUCT,
				.align = 8, .size = 24,
			},
		},
		.signedchar = 1,
	},
	{
		/* Apple arm64: va_list is a plain pointer (void *, the SDK's __darwin_va_list), and the variadic arguments are
		 * on the stack (QBE's apple_selvastart and apple_selvaarg read the va_list object by address). */
		.name = "aarch64-apple",
		.typevalist = &(struct type){
			.kind = TYPEPOINTER, .prop = PROPSCALAR,
			.align = 8, .size = 8,
			.base = &typevoid,
		},
		.typewchar = &typeint,
		.signedchar = 1,
	},
	{
		.name = "aarch64",
		.typevalist = &(struct type){
			.kind = TYPESTRUCT,
			.align = 8, .size = 32,
			.u.structunion.tag = "va_list",
		},
		.typewchar = &typeuint,
	},
	{
		/* i386 (System V, Linux; the kernel's -m16 real-mode code is this too): ILP32, va_list a char *, wchar_t a
		 * long, and long long and double aligned on 4 in structs; the calling convention (cdecl or gcc's
		 * -mregparm=3) is QBE's target (i386 or i386_regparm3). QBE has no floating point on i386 yet: it refuses
		 * the code that uses it (cproc refuses long double and __float128 values, _Float16 and __int128 itself). */
		.name = "i386",
		.typevalist = &(struct type){
			.kind = TYPEPOINTER, .prop = PROPSCALAR,
			.align = 4, .size = 4,
			.base = &typechar,
		},
		.typewchar = &typelong,
		.signedchar = 1,
		.ilp32 = 1,
	},
	{
		.name = "riscv64",
		.typevalist = &(struct type){
			.kind = TYPEPOINTER, .prop = PROPSCALAR,
			.align = 8, .size = 8,
			.base = &typevoid,
		},
		.typewchar = &typeint,
	},
};

/* -u (gcc's -funsigned-char): plain char is unsigned whatever the target's default; the Linux kernel builds with it */
bool unsignedchar;
bool shortwchar, autozero, prune, gnukeywords;

void
targinit(const char *name)
{
	size_t i;
	enum typequal qual;

	if (!name) {
		/* TODO: provide a way to set this default */
		targ = &alltargs[0];
	}
	for (i = 0; i < countof(alltargs) && !targ; ++i) {
		if (strcmp(alltargs[i].name, name) == 0)
			targ = &alltargs[i];
	}
	if (!targ)
		fatal("unknown target '%s'", name);
	typechar.u.arith.issigned = targ->signedchar && !unsignedchar;
	if (targ->ilp32) {
		typelong.size = typelong.align = 4;
		typeulong.size = typeulong.align = 4;
		typelong.u.arith.width = typeulong.u.arith.width = 32;
		typellong.align = typeullong.align = 4;
		typedouble.align = 4;
#ifndef typeldouble   /* the Apple arm64 host's is double (cc.h) */
		typeldouble.size = 12, typeldouble.align = 4;   /* gcc's x87 long double; its values are refused (qbe.c) */
#endif
		typenullptr.size = typenullptr.align = 4;
	}
	qual = QUALNONE;
	typeadjvalist = typeadjust(targ->typevalist, &qual);
}
