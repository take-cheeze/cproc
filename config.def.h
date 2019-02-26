#ifndef DYNAMICLINKER
#define DYNAMICLINKER "/lib64/ld-linux-x86-64.so.2"
#endif

static char *startfiles[] = {
	"-l", ":crt1.o",
	"-l", ":crti.o",
};
static char *endfiles[] = {
	"-l", ":crtn.o",
	"-l", "c",
};
static char *incdirs[] = {
	"/usr/include",
};

static char *compilecmd[] = {"cc-qbe"};
static char *codegencmd[] = {"qbe"};
static char *assemblecmd[] = {"as"};
static char *linkcmd[] = {"ld", "--dynamic-linker=" DYNAMICLINKER};
