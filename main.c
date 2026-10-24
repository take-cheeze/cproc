#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
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

	if (asmfile && !(asmout = fopen(asmfile, "w")))
		fatal("open %s:", asmfile);

	if (output && !freopen(output, "w", stdout))
		fatal("open %s:", output);

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
		emitasanctor();
		checkf128calls();
	}

	fflush(stdout);
	if (ferror(stdout))
		fatal("write failed");
	if (asmout) {
		fflush(asmout);
		if (ferror(asmout))
			fatal("write failed");
	}
	return 0;
}
