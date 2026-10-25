#define _GNU_SOURCE   /* memmem */
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "util.h"
#include "arg.h"
#include "cc.h"

static void
usage(void)
{
	fprintf(stderr, "usage: %s [input]\n", argv0);
	exit(2);
}

extern bool asanon;

/*
cproc -p: drop the internal functions and data that nothing live references, as gcc does at -O. Headers such as the
Linux kernel's define hundreds of static inline functions per translation unit; emitting the unused ones would leave
references to symbols the program does not have. The IL cproc writes is captured and pruned at the end: an item is
live when it is exported, marked "# nfcxx:keep" (GNU used), or referenced ($name) by a live item -- a named section
alone does not keep it, as gcc drops an unreferenced static __init function; type definitions and other top-level
lines are always kept. A live item that contains "# nfcxx:error MSG" (a construct cproc can only refuse, parsed in a
function that might have been dropped) is reported then.

An internal function that is only called, and only from functions in one init section (.init.text and the like), is
put in that section, where gcc's inlined copy of it would be: the kernel's always_inline memblock_alloc, emitted out of
line by cproc, would otherwise be lasting code calling __init code, which the kernel's modpost refuses.
*/
struct ilitem {
	size_t off, len;
	char *name;   /* the $name a function or data item defines, or null */
	bool root, live;
	bool func, exported;
	char *section;     /* the section NAME of its section line, or null */
	bool addrtaken;    /* referenced by a live item other than by a call */
	bool moved;        /* given the section of its callers (ilsection) */
};

static struct ilitem *ilitems;
static size_t nilitems, capilitems;

static struct ilitem *
iladd(size_t off)
{
	if (nilitems == capilitems) {
		capilitems = capilitems ? capilitems * 2 : 256;
		ilitems = xreallocarray(ilitems, capilitems, sizeof(*ilitems));
	}
	ilitems[nilitems] = (struct ilitem){.off = off};
	return &ilitems[nilitems++];
}

/*
The next global name ('$') at or after s and before e, outside the blocks cproc marked unreachable ("# nfcxx:dead" after
a block's label, qbe.c emitfunc): QBE drops those blocks, and a name only they use is not used (the kernel's
create_huge_pmd(), called where __transparent_hugepage_enabled() is false). s is never inside such a block.
*/
static const char *
ilref(const char *s, const char *e)
{
	static const char mark[] = "\n# nfcxx:dead\n";
	const char *c, *m;

	for (;;) {
		if (!(c = memchr(s, '$', e - s)))
			return NULL;
		for (m = s; (m = memchr(m, '\n', c - m)) && (size_t)(e - m) >= sizeof mark - 1; ++m)
			if (memcmp(m, mark, sizeof mark - 1) == 0)
				break;
		if (!m || m >= c || (size_t)(e - m) < sizeof mark - 1)
			return c;
		/* skip the dead block: to the next label or the function's end */
		for (m += sizeof mark - 2; (m = memchr(m, '\n', e - m)) && m + 1 < e && m[1] != '@' && m[1] != '}'; ++m)
			;
		if (!m || m + 1 >= e)
			return NULL;
		s = m + 1;
	}
}

/* the length of the global name at s (after the '$'): a quoted name keeps its quotes */
static size_t
ilnamelen(const char *s, const char *end)
{
	const char *p = s;

	if (p < end && *p == '"') {
		for (++p; p < end && *p != '"'; ++p)
			;
		return p < end ? p + 1 - s : p - s;
	}
	while (p < end && (isalnum((unsigned char)*p) || *p == '_' || *p == '.'))
		++p;
	return p - s;
}

static int
ilfind(const char *name, size_t len)
{
	size_t i;

	/* a linear search is enough: it runs once per reference of a live item */
	for (i = 0; i < nilitems; ++i)
		if (ilitems[i].name && strlen(ilitems[i].name) == len && memcmp(ilitems[i].name, name, len) == 0)
			return i;
	return -1;
}

static bool
initsection(const char *s)
{
	return s && (strncmp(s, ".init.", 6) == 0 || strncmp(s, ".meminit.", 9) == 0 || strncmp(s, ".exit.", 6) == 0);
}

/* the init sections for internal functions called only from one of them (see above), to a fixpoint */
static void
ilsection(const char *buf)
{
	size_t i, n;
	int j;
	bool changed;
	const char **callsec;

	callsec = xreallocarray(NULL, nilitems + 1, sizeof(*callsec));
	/* which live items reference each function other than by a call */
	for (i = 0; i < nilitems; ++i) {
		const char *s = buf + ilitems[i].off, *e = s + ilitems[i].len;

		if (!ilitems[i].live)
			continue;
		for (; (s = ilref(s, e)); s += 1 + n) {
			n = ilnamelen(s + 1, e);
			j = ilfind(s + 1, n);
			if (j < 0 || (size_t)j == i && !ilitems[i].func)
				continue;
			if (!(s - buf >= 5 && memcmp(s - 5, "call ", 5) == 0) && !((size_t)j == i))
				ilitems[j].addrtaken = true;
		}
	}
	do {
		changed = false;
		for (i = 0; i < nilitems; ++i)
			callsec[i] = NULL;
		/* the one section all the callers of each function are in ("" when they are not all in one) */
		for (i = 0; i < nilitems; ++i) {
			const char *s = buf + ilitems[i].off, *e = s + ilitems[i].len;
			const char *sec = ilitems[i].section ? ilitems[i].section : "";

			if (!ilitems[i].live || !ilitems[i].func)
				continue;
			for (; (s = ilref(s, e)); s += 1 + n) {
				n = ilnamelen(s + 1, e);
				j = ilfind(s + 1, n);
				if (j < 0 || (size_t)j == i || !(s - buf >= 5 && memcmp(s - 5, "call ", 5) == 0))
					continue;
				if (!callsec[j])
					callsec[j] = sec;
				else if (strcmp(callsec[j], sec) != 0)
					callsec[j] = "";
			}
		}
		for (i = 0; i < nilitems; ++i) {
			struct ilitem *it = &ilitems[i];

			if (!it->live || !it->func || it->exported || it->section || it->addrtaken || !callsec[i] ||
			    !initsection(callsec[i]) || strstr(callsec[i], "text") == NULL)
				continue;
			it->section = xmalloc(strlen(callsec[i]) + 1);
			strcpy(it->section, callsec[i]);
			it->moved = changed = true;
		}
	} while (changed);
	free(callsec);
}

static void
ilprune(const char *buf, size_t size, FILE *out)
{
	const char *p, *line, *eol, *end = buf + size;
	struct ilitem *it = NULL;
	size_t *stack, nstack = 0, i, n;
	int depth = 0, infunc = 0;

	/* split the IL into items: linkage lines and markers start an item, which a function's closing '}' or the end of a
	 * data or type definition (its braces balanced) finishes */
	for (line = buf; line < end; line = eol) {
		eol = memchr(line, '\n', end - line);
		eol = eol ? eol + 1 : end;
		if (!it)
			it = iladd(line - buf);
		if (!infunc && !depth) {
			const char *q = line, *kw;

			if (strncmp(q, "# nfcxx:keep", 12) == 0)
				it->root = true;
			while (q < eol && (*q == ' ' || *q == '\t'))
				++q;
			/* a section does not keep an item: gcc drops an unreferenced static __init function too */
			if (strncmp(q, "export", 6) == 0)
				it->root = true;
			/* the definition keyword follows the linkage words on the same line (thread export data $x = ...) */
			kw = q;
			for (;;) {
				if (strncmp(kw, "export ", 7) == 0)
					kw += 7;
				else if (strncmp(kw, "thread ", 7) == 0)
					kw += 7;
				else
					break;
			}
			if (strncmp(q, "export", 6) == 0)
				it->exported = true;
			if (strncmp(q, "section \"", 9) == 0 && !it->section) {
				const char *e = memchr(q + 9, '"', eol - (q + 9));
				if (e) {
					it->section = xmalloc(e - (q + 9) + 1);
					memcpy(it->section, q + 9, e - (q + 9));
					it->section[e - (q + 9)] = 0;
				}
			}
			if (strncmp(kw, "function", 8) == 0 && (kw[8] == ' ' || kw[8] == '\n'))
				infunc = 1, it->func = true;
			else if (strncmp(kw, "data ", 5) && strncmp(kw, "type ", 5))
				kw = NULL;
			if (kw && !it->name && strncmp(kw, "type ", 5)) {
				const char *d = memchr(kw, '$', eol - kw);
				if (d) {
					n = ilnamelen(d + 1, eol);
					it->name = xmalloc(n + 1);
					memcpy(it->name, d + 1, n);
					it->name[n] = 0;
				}
			}
			if (kw && strncmp(kw, "type ", 5) == 0)
				it->root = true;
			if (!kw && !infunc) {
				/* a linkage line or marker: it belongs to the item that follows; other lines (dbgfile) are items */
				if (strncmp(q, "export", 6) && strncmp(q, "section", 7) && strncmp(q, "thread", 6) &&
				    strncmp(q, "# nfcxx:keep", 12)) {
					it->root = true;
					it->len = eol - buf - it->off;
					it = NULL;
				}
				continue;
			}
		}
		if (infunc) {
			if (eol - line >= 1 && line[0] == '}') {
				infunc = 0;
				it->len = eol - buf - it->off;
				it = NULL;
			}
			continue;
		}
		/* data or type: balance the braces outside string literals */
		for (p = line; p < eol; ++p) {
			if (*p == '"') {
				for (++p; p < eol && *p != '"'; ++p)
					if (*p == '\\')
						++p;
			} else if (*p == '{') {
				++depth;
			} else if (*p == '}') {
				--depth;
			}
		}
		if (depth <= 0) {
			depth = 0;
			it->len = eol - buf - it->off;
			it = NULL;
		}
	}
	if (it)
		it->len = size - it->off;

	/* mark: the roots, then what live items reference */
	stack = xreallocarray(NULL, nilitems + 1, sizeof(*stack));
	for (i = 0; i < nilitems; ++i)
		if (ilitems[i].root || !ilitems[i].name)
			ilitems[i].live = true, stack[nstack++] = i;
	while (nstack) {
		struct ilitem *l = &ilitems[stack[--nstack]];
		const char *s = buf + l->off, *e = s + l->len;
		int j;

		for (; (s = ilref(s, e)); s += 1 + n) {
			n = ilnamelen(s + 1, e);
			j = ilfind(s + 1, n);
			if (j >= 0 && !ilitems[j].live) {
				ilitems[j].live = true;
				stack[nstack++] = j;
			}
		}
	}
	free(stack);
	ilsection(buf);

	for (i = 0; i < nilitems; ++i) {
		const char *s = buf + ilitems[i].off, *e = s + ilitems[i].len, *m;

		if (!ilitems[i].live)
			continue;
		if (ilitems[i].moved)
			fprintf(out, "section \"%s\" \"ax\"\n", ilitems[i].section);
		for (m = s; m < e && (m = memmem(m, e - m, "# nfcxx:error ", 14)); m += 14) {
			const char *me = memchr(m, '\n', e - m);
			fprintf(stderr, "%.*s\n", (int)((me ? me : e) - (m + 14)), m + 14);
			exit(1);
		}
		fwrite(s, 1, e - s, out);
	}
}

/*
cproc -p and the inline-asm side file (-a): each asm thunk follows a "#nfcxx:owner NAME" line naming its function
(qbe.c funcasm), and a dropped function's thunks are dropped with it -- their text can name symbols the program does
not have. A "#nfcxx:keep" chunk (the volatile and register-variable helpers) always stays.
*/
static const char *ilbufp;   /* the IL, for asmprune */

/* whether a live item defines or names the global NAME */
static bool
ilnamed(const char *buf, const char *name, size_t len)
{
	size_t i, n;
	int j;

	if (!buf)
		return true;
	j = ilfind(name, len);
	if (j >= 0)
		return ilitems[j].live;
	for (i = 0; i < nilitems; ++i) {
		const char *s = buf + ilitems[i].off, *e = s + ilitems[i].len;

		if (!ilitems[i].live)
			continue;
		for (; (s = ilref(s, e)); s += 1 + n) {
			n = ilnamelen(s + 1, e);
			if (n == len && memcmp(s + 1, name, len) == 0)
				return true;
		}
	}
	return false;
}

static void
asmprune(const char *path)
{
	FILE *f;
	char *buf;
	const char *line, *eol, *end, *name;
	size_t size;
	long n;
	bool keep = true;
	int j;

	if (!(f = fopen(path, "r")) || fseek(f, 0, SEEK_END) || (n = ftell(f)) < 0 || fseek(f, 0, SEEK_SET))
		fatal("read back %s:", path);
	size = n;
	buf = xmalloc(size + 1);
	if (size && fread(buf, 1, size, f) != size)
		fatal("read back %s:", path);
	fclose(f);
	if (!(f = fopen(path, "w")))
		fatal("open %s:", path);
	for (line = buf, end = buf + size; line < end; line = eol) {
		eol = memchr(line, '\n', end - line);
		eol = eol ? eol + 1 : end;
		if (strncmp(line, "#nfcxx:owner ", 13) == 0) {
			name = line + 13;
			j = ilfind(name, eol - name - (eol[-1] == '\n'));
			keep = j < 0 || ilitems[j].live;
			continue;
		}
		if (strncmp(line, "#nfcxx:keep", 11) == 0)
			keep = true;
		if (strncmp(line, "#nfcxx:symattr ", 15) == 0) {
			/* weak and visibility (qbe.c emitsymattr): for a symbol a live item defines or names */
			name = line + 15;
			keep = ilnamed(ilbufp, name, eol - name - (eol[-1] == '\n'));
			continue;
		}
		if (keep)
			fwrite(line, 1, eol - line, f);
	}
	if (fflush(f) || ferror(f) || fclose(f))
		fatal("write %s:", path);
	free(buf);
}

int
main(int argc, char *argv[])
{
	bool pponly = false;
	char *output = NULL, *target = NULL, *asmfile = NULL;

	argv0 = progname(argv[0], "cproc-qbe");
	asanon = getenv("NFCXX_ASAN") != NULL;
	ARGBEGIN {
	case 'E':
		pponly = true;
		break;
	case 't':
		target = EARGF(usage());
		break;
	case 'a':
		asmfile = EARGF(usage());
		break;
	case 'u':
		unsignedchar = true;   /* -funsigned-char */
		break;
	case 'W':
		shortwchar = true;     /* -fshort-wchar */
		break;
	case 'z':
		autozero = true;       /* -ftrivial-auto-var-init=zero */
		break;
	case 'p':
		prune = true;
		break;
	case 'g':
		gnukeywords = true;
		break;
	case 'V':
		volatilecalls = true;
		break;
	case 'G':
		gnucleanup = true;   /* GNU C's cleanup attribute: the cleanup runs when the object leaves its scope */
		break;
	case 'c':
		stdc23 = true;   /* treat true/false/nullptr/bool as C23 keywords, not identifiers (the default) */
		break;
	case 'K':
		stdc23 = false;  /* before C23: true/false/nullptr/bool are identifiers (the Linux kernel's gnu11) */
		break;
	case 'o':
		output = EARGF(usage());
		break;
	default:
		usage();
	} ARGEND

	targinit(target);
	if (targ->ilp32 && asanon)
		fatal("-fsanitize=address is not supported on %s", targ->name);

	if (asmfile && !(asmout = fopen(asmfile, "w")))
		fatal("open %s:", asmfile);

	if (output && !freopen(output, "w", stdout))
		fatal("open %s:", output);

	/* -p: the IL goes to a temporary file, pruned into the real output at the end */
	int realout = -1;
	FILE *iltmp = NULL;
	if (prune) {
		fflush(stdout);
		if (!(iltmp = tmpfile()) || (realout = dup(1)) < 0 || dup2(fileno(iltmp), 1) < 0)
			fatal("redirect output for -p:");
	}

	if (argc) {
		while (argc--)
			scanfrom(argv[argc], NULL);
		scanopen();
	} else {
		scanfrom("<stdin>", stdin);
	}

	tokeninit();
	ppinit();
	if (pponly) {
		ppflags |= PPNEWLINE;
		while (tok.kind != TEOF) {
			tokenprint(&tok, stdout);
			next();
		}
	} else {
		scopeinit();
		while (tok.kind != TEOF) {
			if (!decl(&filescope, NULL)) {
				if (tok.kind == TSEMICOLON)
					error(&tok.loc, "unexpected ';' at top-level");
				error(&tok.loc, "expected declaration or function definition");
			}
		}
		emittentativedefns();
		emitsymattrs();
		emitasanctor();
		checkf128calls();
	}

	fflush(stdout);
	if (ferror(stdout))
		fatal("write failed");
	if (prune) {
		char *ilbuf;
		size_t ilsize;
		long n;
		FILE *out;

		if ((n = lseek(fileno(iltmp), 0, SEEK_END)) < 0 || lseek(fileno(iltmp), 0, SEEK_SET) < 0)
			fatal("read back the IL:");
		ilsize = n;
		ilbuf = xmalloc(ilsize + 1);
		if (ilsize && read(fileno(iltmp), ilbuf, ilsize) != (ssize_t)ilsize)
			fatal("read back the IL:");
		if (!(out = fdopen(realout, "w")))
			fatal("fdopen:");
		ilprune(ilbuf, ilsize, out);
		ilbufp = ilbuf;
		if (fflush(out) || ferror(out))
			fatal("write failed");
	}
	if (asmout) {
		if (fflush(asmout) || ferror(asmout) || fclose(asmout))
			fatal("write failed");
		asmout = NULL;
		if (prune)
			asmprune(asmfile);
	}
	return 0;
}
