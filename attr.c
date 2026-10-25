#include <limits.h>
#include <stdbool.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct declattr declattr;
const char *attrabi;

enum attrprefix {
	PREFIXNONE = 1,  /* standard attribute */
	PREFIXGNU,
};

static const char *
strip(const char *name, char *buf, size_t buflen)
{
	size_t len;

	len = strlen(name);
	if (len >= 4 && name[0] == '_' && name[1] == '_' && name[len - 2] == '_' && name[len - 1] == '_') {
		if (len - 4 >= buflen)
			return "";
		memcpy(buf, name + 2, len - 4);
		buf[len - 4] = '\0';
		return buf;
	}
	return name;
}

static bool
parseattr(struct attr *a, enum attrkind allowed, enum attrprefix prefix)
{
	const char *name, *prefixname = "";
	char namebuf[32], *section;
	const char *cleanup;
	enum attrkind kind;
	int paren;

	/* an attribute name is an identifier or a keyword (GNU const, the kernel's __attribute_const__) */
	if (tok.kind < TALIGNAS)
		return false;
	name = strip(tokenstr(tok.kind), namebuf, sizeof namebuf);
	next();
	if (!prefix) {
		if (consume(TCOLONCOLON)) {
			if (strcmp(name, "gnu") == 0)
				prefix = PREFIXGNU;
			name = strip(expect(TIDENT, "after attribute prefix"), namebuf, sizeof namebuf);
		} else {
			prefix = PREFIXNONE;
		}
	}
	kind = 0;
	switch (prefix) {
	case PREFIXNONE:
		if (strcmp(name, "noreturn") == 0 || strcmp(name, "_Noreturn") == 0)
			kind = ATTRNORETURN;
		break;
	case PREFIXGNU:
		prefixname = "GNU ";
		if (strcmp(name, "aligned") == 0) {
			kind = ATTRALIGNED;
			if (consume(TLPAREN)) {
				unsigned long long i;

				i = intconstexpr(attrscope, false);
				if (!i || i & i - 1 || i > INT_MAX)
					error(&tok.loc, "invalid alignment %llu", i);
				if (a)
					a->align = i;
				expect(TRPAREN, "after alignment");
			} else {
				if (a)
					a->align = 16;
			}
		} else if (strcmp(name, "constructor") == 0) {
			kind = ATTRCONSTRUCTOR;
		} else if (strcmp(name, "destructor") == 0) {
			kind = ATTRDESTRUCTOR;
		} else if (strcmp(name, "packed") == 0) {
			kind = ATTRPACKED;
		} else if (strcmp(name, "cleanup") == 0) {
			kind = ATTRCLEANUP;
			expect(TLPAREN, "after 'cleanup'");
			cleanup = expect(TIDENT, "for cleanup function");
			if (a)
				a->cleanup = cleanup;
			expect(TRPAREN, "after cleanup function");
		} else if (strcmp(name, "section") == 0) {
			struct stringlit lit;

			kind = ATTRSECTION;
			expect(TLPAREN, "after 'section'");
			tokencheck(&tok, TSTRINGLIT, "for section name");
			stringconcat(&lit, true);   /* ".initcall" "6" ".init": adjacent literals, as the kernel writes them */
			section = lit.data;
			if (a)
				a->section = section;
			declattr.section = section;
			expect(TRPAREN, "after section name");
		} else if (strcmp(name, "ms_abi") == 0 || strcmp(name, "sysv_abi") == 0 || strcmp(name, "regparm") == 0 ||
		           strcmp(name, "stdcall") == 0 || strcmp(name, "fastcall") == 0 || strcmp(name, "thiscall") == 0) {
			/* another calling convention (the kernel's __efiapi): the function type is marked, its arguments skipped */
			attrabi = strcmp(name, "ms_abi") == 0 ? "ms_abi" : strcmp(name, "sysv_abi") == 0 ? "sysv_abi" : "regparm";
		} else if (strcmp(name, "mode") == 0) {
			/* an integer mode: QI (byte) 1, HI 2, SI 4, DI (word, pointer) 8 bytes; others are refused */
			char mbuf[32];
			const char *m;
			int size = 0;

			kind = ATTRMODE;
			expect(TLPAREN, "after 'mode'");
			m = strip(expect(TIDENT, "for mode"), mbuf, sizeof mbuf);
			if (strcmp(m, "QI") == 0 || strcmp(m, "byte") == 0)
				size = 1;
			else if (strcmp(m, "HI") == 0)
				size = 2;
			else if (strcmp(m, "SI") == 0)
				size = 4;
			else if (strcmp(m, "DI") == 0)
				size = 8;
			else if (strcmp(m, "word") == 0 || strcmp(m, "pointer") == 0)
				size = targ->ilp32 ? 4 : 8;
			else
				error(&tok.loc, "GNU attribute mode(%s) is not supported", m);
			if (a)
				a->modesize = size;
			if (!(allowed & ATTRMODE))   /* not after an enum body: the declaration's (decl.c modetype) */
				declattr.modesize = size;
			expect(TRPAREN, "after mode");
		} else if (strcmp(name, "weak") == 0) {
			declattr.weak = true;
		} else if (strcmp(name, "alias") == 0 || strcmp(name, "visibility") == 0) {
			/* GNU alias("target") and visibility("hidden"): kept for the declaration (declattr) */
			struct stringlit lit;
			bool isalias = name[0] == 'a';

			expect(TLPAREN, isalias ? "after 'alias'" : "after 'visibility'");
			tokencheck(&tok, TSTRINGLIT, isalias ? "for alias target" : "for visibility");
			stringconcat(&lit, true);
			if (isalias) {
				declattr.alias = lit.data;
			} else {
				if (strcmp(lit.data, "default") && strcmp(lit.data, "hidden") && strcmp(lit.data, "protected") &&
				    strcmp(lit.data, "internal"))
					error(&tok.loc, "unknown visibility '%s'", (char *)lit.data);
				declattr.visibility = lit.data;
			}
			expect(TRPAREN, isalias ? "after alias target" : "after visibility");
		} else if (strcmp(name, "always_inline") == 0) {
			declattr.alwaysinline = true;
		} else if (strcmp(name, "noipa") == 0) {
			declattr.noipa = true;
		} else if (strcmp(name, "gnu_inline") == 0) {
			declattr.gnuinline = true;
		} else if (strcmp(name, "transparent_union") == 0) {
			kind = ATTRTRANSPARENT;
			declattr.transparent = true;
		} else if (strcmp(name, "used") == 0) {
			kind = ATTRUSED;
			declattr.used = true;
		}
		break;
	}
	/* a GNU attribute that changes what a declaration means -- its type (vector_size), its code (naked,
	 * interrupt, no_caller_saved_registers, target), its binding (weakref, ifunc) -- is refused, never ignored as
	 * the hints and diagnostics (noinline, cold, format, nonnull, ...) are */
	if (prefix == PREFIXGNU && !kind) {
		static const char *const meaning[] = {
			"vector_size", "naked", "interrupt", "no_caller_saved_registers", "weakref", "ifunc",
			"target_clones", "symver", "tls_model", "scalar_storage_order", "nocf_check", "fentry_name",
		};
		size_t i;

		for (i = 0; i < sizeof meaning / sizeof meaning[0]; ++i)
			if (strcmp(name, meaning[i]) == 0)
				error(&tok.loc, "GNU attribute '%s' is not supported (it changes what the declaration means)", name);
	}
	if (kind) {
		/* section, used, transparent_union and mode are recorded for the declaration (declattr) wherever they appear */
		if (kind & ~(ATTRSECTION | ATTRUSED | ATTRTRANSPARENT | ATTRMODE) & ~allowed)
			error(&tok.loc, "%sattribute '%s' is not supported here", prefixname, name);
		if (a)
			a->kind |= kind;
	} else if (consume(TLPAREN)) {
		/* skip arguments */
		for (paren = 1; paren > 0; next()) {
			switch (tok.kind) {
			case TLPAREN: ++paren; break;
			case TRPAREN: --paren; break;
			}
		}
	}
	return true;
}

static bool
attrspec(struct attr *a, enum attrkind allowed)
{
	if (tok.kind != TLBRACK || !peek(TLBRACK))
		return false;
	while (parseattr(a, allowed, 0) || consume(TCOMMA))
		;
	expect(TRBRACK, "to end attribute specifier");
	expect(TRBRACK, "to end attribute specifier");
	return true;
}

bool
attr(struct attr *a, enum attrkind allowed)
{
	if (!attrspec(a, allowed))
		return false;
	while (attrspec(a, allowed))
		;
	return true;
}

static bool
gnuattrspec(struct attr *a, enum attrkind allowed)
{
	if (!consume(T__ATTRIBUTE__))
		return false;
	while (parseattr(a, allowed, PREFIXGNU) || consume(TCOMMA))
		;
	expect(TLPAREN, "after '__attribute__' to begin attribute specifier");
	expect(TLPAREN, "after '__attribute__' to begin attribute specifier");
	while (parseattr(a, allowed, PREFIXGNU) || consume(TCOMMA))
		;
	expect(TRPAREN, "to end attribute specifier");
	expect(TRPAREN, "to end attribute specifier");
	return true;
}

bool
gnuattr(struct attr *a, enum attrkind allowed)
{
	if (!gnuattrspec(a, allowed))
		return false;
	while (gnuattrspec(a, allowed))
		;
	return true;
}
