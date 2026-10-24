#include <setjmp.h>
#include <stdio.h>

struct func;

enum tokenkind {
#define TOKEN(t, s) t,
#include "tokens.h"
#undef TOKEN

	TPPIDENT = TALIGNAS,
	TIDENT = TDEFINE
};

struct location {
	const char *file;
	size_t line, col;
};

struct token {
	enum tokenkind kind;
	/* whether or not the token is ineligible for expansion */
	bool hide;
	/* whether or not the token was preceeded by a space */
	bool space;
	struct location loc;
	char *lit;
};

enum typequal {
	QUALNONE,

	QUALCONST    = 1<<1,
	QUALRESTRICT = 1<<2,
	QUALVOLATILE = 1<<3,
	QUALATOMIC   = 1<<4
};

enum typekind {
	TYPENONE,

	TYPEVOID,
	TYPEBOOL,
	TYPECHAR,
	TYPESHORT,
	TYPEINT,
	TYPEENUM,
	TYPELONG,
	TYPELLONG,
	TYPEFLOAT,
	TYPEDOUBLE,
	TYPELDOUBLE,
	TYPEFLOAT128,
	TYPEFLOAT16,
	TYPEPOINTER,
	TYPEARRAY,
	TYPEFUNC,
	TYPESTRUCT,
	TYPEUNION,
	TYPENULLPTR,
	TYPEBITINT,
	TYPEINT128,
};

enum typeprop {
	PROPNONE,

	PROPCHAR    = 1<<0,
	PROPINT     = 1<<1,
	PROPREAL    = 1<<2,
	PROPARITH   = 1<<3,
	PROPSCALAR  = 1<<4,
	PROPFLOAT   = 1<<5,
	PROPVM      = 1<<6, /* variably-modified type */
	PROPFLEX    = 1<<7, /* struct with flexible array member */
	/* 16-byte floating type (long double, __float128): a value is the address of a 16-byte object, and each
	 * operation is a call of a runtime helper (qbe.c: softname, softbinary, convertsoft) */
	PROPSOFT    = 1<<8,
};

struct bitfield {
	short before;  /* number of bits in the storage unit before the bit-field */
	short after;   /* number of bits in the storage unit after the bit-field */
};

struct member {
	char *name;
	struct type *type;
	enum typequal qual;
	unsigned long long offset;
	struct bitfield bits;
	int align;   /* the alignment the member asked for (an aligned attribute), or 0: kept for a packed re-layout */
	struct member *next;
};

struct type {
	enum typekind kind;
	enum typeprop prop;
	int align;
	unsigned long long size;
	struct value *value;  /* used by the backend */
	struct type *base;
	struct list link;  /* used only during construction of type */
	/* qualifiers of the base type */
	enum typequal qual;
	bool incomplete;
	union {
		struct {
			bool issigned, iscomplex;
			int width;
		} arith;
		struct {
			struct expr *length;
			enum typequal ptrqual;
			struct value *size;
		} array;
		struct {
			bool isvararg;
			bool unprototyped;  /* written as "()", not "(void)" (6.7.6.3p15) */
			const char *abi;    /* a GNU calling-convention attribute (attrabi): never called or defined */
			struct decl *params;
			size_t nparam;
		} func;
		struct {
			char *tag;
			struct member *members;
			bool transparent;   /* GNU transparent_union: an argument of any member's type, passed as the first */
		} structunion;
	} u;
};

enum declkind {
	DECLTYPE,
	DECLOBJECT,
	DECLFUNC,
	DECLCONST,
	DECLBUILTIN,
};

enum linkage {
	LINKNONE,
	LINKINTERN,
	LINKEXTERN,
};

enum storageduration {
	SDSTATIC,
	SDTHREAD,
	SDAUTO,
};

enum builtinkind {
	BUILTINADDOVERFLOW,
	BUILTINSUBOVERFLOW,
	BUILTINMULOVERFLOW,
	BUILTINALLOCA,
	BUILTINBSWAP16,
	BUILTINBSWAP32,
	BUILTINBSWAP64,
	BUILTINCLZ, BUILTINCLZL,   /* the bit-counting built-ins: the int and the long (and long long) forms */
	BUILTINCTZ, BUILTINCTZL,
	BUILTINFFS, BUILTINFFSL,
	BUILTINPARITY, BUILTINPARITYL,
	BUILTINPOPCOUNT, BUILTINPOPCOUNTL,
	BUILTINCHOOSEEXPR,
	BUILTINCONSTANTP,
	BUILTINOBJECTSIZE,
	BUILTINRETURNADDRESS,
	BUILTINEXTRACTRETURNADDR,
	BUILTINISDIGIT,
	BUILTINPREFETCH,
	BUILTINFRAMEADDRESS,
	BUILTINEXPECT,
	BUILTINFABSF,
	BUILTINFPCLASSIFY,
	BUILTININFF,
	BUILTINNANF,
	BUILTINISFINITE,
	BUILTINISGREATER,
	BUILTINISGREATEREQUAL,
	BUILTINISINF,
	BUILTINISLESS,
	BUILTINISLESSEQUAL,
	BUILTINISLESSGREATER,
	BUILTINISNAN,
	BUILTINISNORMAL,
	BUILTINISUNORDERED,
	BUILTINSIGNBIT,
	BUILTINOFFSETOF,
	BUILTINTYPESCOMPATIBLEP,
	BUILTINUNREACHABLE,
	BUILTINVAARG,
	BUILTINVACOPY,
	BUILTINVAEND,
	BUILTINVALIST,
	BUILTINVASTART,
	BUILTINC11INIT,
	BUILTINC11LOAD,
	BUILTINC11STORE,
	BUILTINC11XCHG,
	BUILTINC11CAS,
	BUILTINC11FETCHADD,
	BUILTINC11FETCHSUB,
	BUILTINC11FETCHAND,
	BUILTINC11FETCHOR,
	BUILTINC11FETCHXOR,
	BUILTINATOMICLOAD,
	BUILTINATOMICSTORE,
	BUILTINATOMICXCHG,
	BUILTINATOMICCAS,
	BUILTINATOMICTESTANDSET,
	BUILTINATOMICCLEAR,
};

struct decl {
	char *name;
	enum declkind kind;
	enum linkage linkage;
	struct type *type;
	enum typequal qual;
	struct value *value;
	char *asmname;
	char *section;   /* GNU section("...") on a function or a static-storage object, or null */
	char *regvar;    /* GNU register variable: register T x asm("REG") binds x to REG (without '%'), or null */
	bool used;       /* GNU used: kept even when nothing references it (cproc -p) */
	bool weak;       /* GNU weak */
	bool noipa;      /* GNU noipa */
	char *alias;     /* GNU alias("target"): the declaration defines the name as the target */
	const char *visibility;   /* GNU visibility("hidden"), ... or null */
	bool symattr;    /* in the list of decls whose weak or visibility goes to the assembly (emitsymattrs) */
	struct decl *symattrnext;
	bool defined;
	bool tentative;
	struct decl *next;
	/* where the declarator's name is (the current token when the declaration is made; -fsanitize=address's frame description) */
	struct location loc;

	union {
		struct {
			/* alignment of object storage (may be stricter than type requires) */
			int align;
			enum storageduration storage;
			/* GNU cleanup(f) on a block-scope object: f(&object) runs when a throw unwinds its function (nfcxx, qbe.c) */
			const char *cleanup;
			struct decl *cleanupfn;   /* cproc -G: the cleanup function's declaration */
			/* GNU: the bytes its initialized flexible array member adds to a static object (init.c), as gcc's
			 * object is sizeof the struct plus those */
			unsigned long long famsize;
		} obj;
		struct {
			/* the function might have an "inline definition" (C11 6.7.4p7) */
			bool inlinedefn;
			bool isnoreturn;
			bool gnuinline;   /* GNU gnu_inline: extern inline defines no symbol, inline an external one */
			/* the body of an extern gnu_inline function, emitted under a local name (qbe.c mkinlinealias) for the
			 * direct calls to use; the address and earlier calls name the external symbol */
			struct value *inlinealias;
			/* always_inline under cproc -p: the tokens of the body (decl.c), whether it has a static local, whether
			 * cproc refused something in it that a constant argument may make possible (an asm "i" operand), and
			 * the clones made for constant arguments (funcclone) */
			struct array *body;
			bool hasstatic, refused;
			/* the body is { return C; } with C an integer constant (stmt.c): a direct call whose arguments have no
			 * side effects is C (expr.c), as gcc's inlined and folded call is */
			bool constret;
			unsigned long long retval;
			/* the body is {} and the function returns void: such a call is nothing, as gcc's inlined one */
			bool emptybody;
			struct funcclone *clones;
		} func;
		unsigned long long enumconst;
		enum builtinkind builtin;
	} u;
};

struct scope {
	struct map tags;
	struct map decls;
	struct block *breaklabel;
	struct block *continuelabel;
	struct switchcases *switchcases;
	struct scope *parent;
	/* cproc -G: the depth of the function's cleanup stack when the scope began, and when the loop or switch body that
	 * break and continue leave began (qbe.c funccleanmark) */
	size_t cleanmark, cleanbreak, cleancontinue;
	bool stmtexpr;   /* the scope of a statement expression's own declarations */
	/* GNU local labels (__label__ a, b;): the block's own names for them, a unique name per declaration */
	struct locallabel {
		char *name, *unique;
		struct locallabel *next;
	} *labels;
	/* -fsanitize=address: the stack objects registered when the loop or switch body whose breaklabel or continuelabel this is began (asanmark) */
	size_t asanbreak, asancontinue;
};

enum exprkind {
	/* primary expression */
	EXPRIDENT,
	EXPRCONST,
	EXPRSTRING,

	/* postfix expression */
	EXPRCALL,
	/* member E.M gets transformed to *(typeof(E.M) *)((char *)E + offsetof(typeof(E), M)) */
	EXPRBITFIELD,
	EXPRINCDEC,
	EXPRCOMPOUND,
	/* subscript E1[E2] gets transformed to *((E1)+(E2)) */

	EXPRUNARY,
	EXPRCAST,
	EXPRBINARY,
	EXPRCOND,
	EXPRASSIGN,
	EXPRCOMMA,

	EXPRBUILTIN,
	EXPRTEMP,
	EXPRSIZEOF,
	EXPRSTMT,   /* GNU statement expression ({ ... }): see stmtexpr in stmt.c */
};

struct stringlit {
	size_t size;
	void *data;
};

struct expr {
	enum exprkind kind;
	/* where the expression starts (set by mkexpr from the current token; the qbe backend's -fsanitize=address uses it) */
	struct location loc;
	/* whether this expression is an lvalue */
	bool lvalue;
	/* whether this expression is a pointer decayed from an array or function designator */
	bool decayed;
	/* the unqualified type of the expression */
	struct type *type;
	/* the type qualifiers of the object this expression refers to (ignored for non-lvalues) */
	enum typequal qual;
	enum tokenkind op;
	struct expr *base;
	struct expr *next;
	struct expr *toeval;
	union {
		struct {
			struct decl *decl;
		} ident;
		union {
			unsigned long long u;
			long long i;
			double f;
			/* a 16-byte floating constant (PROPSOFT type): the object image, low and high eightbyte */
			unsigned long long soft[2];
		} constant;
		/* EXPRSTMT: the statements, a chain of blocks not yet part of the function; base is the value (or null) */
		struct {
			struct block *first, *last;
			bool done;
		} stmt;
		struct stringlit string;
		struct {
			struct expr *args;
			size_t nargs;
		} call;
		struct {
			struct bitfield bits;
		} bitfield;
		struct {
			struct decl *decl;
			struct init *init;
		} compound;
		struct {
			bool post;
		} incdec;
		struct {
			struct expr *l, *r;
		} binary;
		struct {
			struct expr *t, *f;
		} cond;
		struct {
			struct expr *l, *r;
		} assign;
		struct {
			enum builtinkind kind;
		} builtin;
		struct {
			struct type *type;
		} szof;
		struct value *temp;
	} u;
};

struct init {
	unsigned long long start, end;
	struct expr *expr;
	struct bitfield bits;
	struct init *next;
};

/* token */

extern struct token tok;

void tokeninit(void);
int tokenget(const void *, size_t);
int iscident(enum tokenkind);
extern bool stdc23;
void tokenprint(const struct token *, FILE *);
char *tokenstr(enum tokenkind);
char *tokencheck(const struct token *, enum tokenkind, const char *);
void diagloc(const struct location *);
noreturn void error(const struct location *, const char *, ...);
/* while errorjmp is set, error() puts its message (with the location) in errorbuf and jumps there: cproc -p uses it
 * to defer a refusal inside a function body until it is known whether the function is kept (qbe.c funcasm) */
extern jmp_buf *errorjmp;
extern char errorbuf[512];

/* scan */

void scanfrom(const char *, FILE *);
void scanopen(void);
void scansetloc(struct location loc);
void scan(struct token *);

/* preprocessor */

enum ppflags {
	/* preserve newlines in preprocessor output */
	PPNEWLINE   = 1 << 0,
};

extern enum ppflags ppflags;

void ppinit(void);

void next(void);
bool peek(enum tokenkind);
/* the tokens next() returns, recorded into an array (null stops), and replayed from one instead of the input (the
 * constant-argument clones of always_inline functions, decl.c funcclone) */
void tokrecord(struct array *);
struct tokreplay {
	struct token *tok;
	size_t n, pos;
	bool on;
};
void tokreplay(struct tokreplay *old, struct token *, size_t);   /* old gets the replay it replaces */
void tokreplayend(const struct tokreplay *old);   /* back to that replay (or to the input) */
char *expect(enum tokenkind, const char *);
bool consume(enum tokenkind);

/* type */

struct type *mktype(enum typekind, enum typeprop);
struct type *mkpointertype(struct type *, enum typequal);
struct type *mkarraytype(struct type *, enum typequal, unsigned long long);
struct type *mkbitinttype(int width, bool sign);

bool typecompatible(struct type *, struct type *);
bool typesame(struct type *, struct type *);
struct type *typecomposite(struct type *, struct type *);
struct type *typeunqual(struct type *, enum typequal *);
struct type *typecommonreal(struct type *, unsigned, struct type *, unsigned);
struct type *typepromote(struct type *, unsigned);
struct type *typeadjust(struct type *, enum typequal *);
enum typeprop typeprop(struct type *);
struct member *typemember(struct type *, const char *, unsigned long long *);
bool typehasint(struct type *, unsigned long long, bool);

/* 16-byte floating types (eval.c): the image of a constant of type t, and the sign flip of such an image */
void softimage(unsigned long long img[2], struct type *t, long double x);
unsigned halfbits(double x);
double halfvalue(unsigned bits);
void softliteral(unsigned long long img[2], const char *lit);
unsigned long long softsignbit(struct type *t);

extern struct type typevoid;
extern struct type typebool;
extern struct type typechar, typeschar, typeuchar;
extern struct type typeshort, typeushort;
extern struct type typeint, typeuint;
extern struct type typelong, typeulong;
extern struct type typellong, typeullong;
/* Apple arm64 (scripts/setup-qbe.sh): long double is a double, as in clang's ABI there, so cproc's long double is the
 * double type. Everywhere else long double is the 16-byte soft type of type.c. */
#if defined(__APPLE__) && defined(__aarch64__)
#define typeldouble typedouble
#endif
extern struct type typefloat, typedouble, typeldouble, typefloat128, typefloat16;
extern struct type typeint128, typeuint128;
extern struct type typenullptr;
extern struct type *typeadjvalist;

/* targ */

struct target {
	const char *name;
	struct type *typevalist;
	struct type *typewchar;
	int signedchar;
};

extern const struct target *targ;

void targinit(const char *);
extern bool unsignedchar;
extern bool shortwchar;   /* -W (gcc's -fshort-wchar): wide literals are unsigned short */
extern bool autozero;     /* -z (gcc's -ftrivial-auto-var-init=zero): automatic objects without initializer are zeroed */
extern bool prune;        /* -p: drop the internal functions and data nothing live references, as gcc does */
extern bool gnukeywords;  /* -g: the GNU C keyword asm (gnu* dialects); __asm__ is a keyword always */
extern bool volatilecalls; /* -V: volatile scalar accesses through opaque helpers (qbe.c funcvolatile) */

/* attr */

enum attrkind {
	ATTRNORETURN    = 1<<0,

	/* GNU attributes */
	ATTRALIGNED     = 1<<2,
	ATTRCONSTRUCTOR = 1<<3,
	ATTRDESTRUCTOR  = 1<<4,
	ATTRPACKED      = 1<<5,
	ATTRSECTION     = 1<<6,
	ATTRCLEANUP     = 1<<7,
	ATTRUSED        = 1<<8,
	ATTRTRANSPARENT = 1<<9,   /* GNU transparent_union, on a typedef of a union */
	ATTRMODE        = 1<<10,  /* GNU mode(byte), ... after an enum body (the kernel's 1-byte trace enums) */
};

struct attr {
	enum attrkind kind;
	int align;
	int modesize;   /* mode: the size in bytes of the integer mode */
	char *section;
	const char *cleanup;
};

bool attr(struct attr *, enum attrkind);
bool gnuattr(struct attr *, enum attrkind);
/* a GNU calling-convention attribute (ms_abi, sysv_abi, regparm, ...) was parsed: the next function declarator takes
 * it (decl.c), and a call or definition of such a function is refused (qbe.c) */
extern const char *attrabi;

/* section(...) and used, wherever they appear in a declaration (declaration specifiers, after a pointer, after the
 * declarator): gnuattr records them here, and decl() hands them to the declared function or object */
struct declattr {
	char *section;
	bool used;
	bool transparent;   /* GNU transparent_union, taken on a typedef of a union (decl) */
	bool gnuinline;     /* GNU gnu_inline */
	bool alwaysinline;  /* GNU always_inline */
	bool noipa;         /* GNU noipa: a call of the function is never folded by what its body is (expr.c) */
	bool weak;          /* GNU weak */
	char *alias;        /* GNU alias("target") */
	const char *visibility;   /* GNU visibility("...") */
};
extern struct declattr declattr;

/* decl */

struct decl *mkdecl(char *name, enum declkind, struct type *, enum typequal, enum linkage);
bool decl(struct scope *, struct func *);
struct type *typename(struct scope *, enum typequal *, struct expr **);

struct decl *stringdecl(struct expr *);

void emittentativedefns(void);
void checkf128calls(void);
void emitasanctor(void);

/* -fsanitize=address, use after scope (qbe.c): blocks and the jumps out of them; all are no-ops without asanon */
void asanbegin(struct func *);
void asanend(struct func *);
size_t asanmark(struct func *);
void asanleave(struct func *, size_t);

/* scope */

void scopeinit(void);
struct scope *mkscope(struct scope *);
struct scope *delscope(struct scope *);

void scopeputdecl(struct scope *, struct decl *);
struct decl *scopegetdecl(struct scope *, const char *, bool);

void scopeputtag(struct scope *, const char *, struct type *);
struct type *scopegettag(struct scope *, const char *, bool);

extern struct scope filescope;
extern struct scope *attrscope;   /* where an attribute's constant arguments are looked up (decl) */

/* expr */

struct type *stringconcat(struct stringlit *, bool);

struct expr *expr(struct scope *);
struct expr *assignexpr(struct scope *);
struct expr *condexpr(struct scope *);
unsigned long long intconstexpr(struct scope *, bool);
void delexpr(struct expr *);

struct expr *exprassign(struct expr *, struct type *);
struct expr *exprpromote(struct expr *);

/* eval */

struct expr *eval(struct expr *);

/* init */

struct init *mkinit(unsigned long long, unsigned long long, struct bitfield, struct expr *);
struct init *parseinit(struct scope *, struct type *);
extern unsigned long long initfamsize;   /* the bytes the last parseinit's flexible array member takes (GNU) */

/* stmt */

void stmt(struct func *, struct scope *);
struct expr *stmtexpr(struct func *, struct scope *);
extern struct func *curfunc;   /* the function whose body is being parsed, for statement expressions */

/* GNU extended inline assembly (nfcxx: lowered to an out-of-line thunk, see funcasm in the backend) */
struct asmoperand {
	char *constraint;   /* the constraint string, e.g. "=r", "r", "0", "i" */
	char *symname;      /* the [name] of a symbolic operand reference, or null */
	struct expr *expr;  /* an output's lvalue, or an input's value */
};

/* backend */

struct gotolabel {
	struct block *label;
	bool defined;
	/* -fsanitize=address (qbe.c asangoto, asanlabel): sets of block numbers, null when empty. The blocks open at the label
	 * (asanopen, once defined); for the gotos before it: the blocks open at any of them (asanfrom) and at all of them (asanall) */
	struct array *asanopen, *asanfrom, *asanall;
	/* cproc -G: the cleanup objects live at the label (struct ehobj, once defined) */
	struct array cleanat;
};

struct switchcases {
	void *root;
	struct type *type;
	struct block *defaultlabel;
	/* -fsanitize=address (qbe.c asanswitch, asancase): the blocks open at the switch, which the dispatch enters the cases from */
	struct array *asanopen;
};

void switchcase(struct switchcases *, unsigned long long, unsigned long long, struct block *);

struct block *mkblock(char *);

struct value *mkglobal(struct decl *);
struct value *mkinlinealias(struct decl *);

struct value *mkintconst(unsigned long long);

struct func *mkfunc(struct decl *, char *, struct type *, struct scope *);
struct decl *funcclone(struct decl *, struct expr *);
void funcalloc(struct func *, struct decl *);   /* the storage of an automatic object */
/* cproc -G, GNU cleanup semantics (qbe.c): the cleanup of a block-scope object runs when it leaves its scope */
extern bool gnucleanup;
extern const char *pragmavisibility;   /* #pragma GCC visibility push (pp.c) */
extern int pragmapack;   /* #pragma pack(N) (pp.c): the most alignment of a struct member, 0 for none */
size_t funccleanmark(struct func *);
void funccleanleave(struct func *, size_t);   /* the cleanups of the objects above the mark, innermost first */
void funccleanpop(struct func *, size_t);     /* and they are no longer live */
struct block *funcgototarget(struct func *, struct gotolabel *);   /* where a goto to the label jumps */
void funclabeldefined(struct func *, struct gotolabel *);
void funcgotoflush(struct func *);   /* after the body: the cleanups of the gotos (funcgototarget) */
struct decl *funcdecl(struct func *);
/* the shape of a function's body as stmt.c parses it: whether it is { return C; } with C an integer constant */
struct funcshape {
	int depth, items;
	bool firstreturn, constret;
	unsigned long long retval;
};
struct funcshape *funcshape(struct func *);
void delfunc(struct func *);
struct type *functype(struct func *);
void funclabel(struct func *, struct block *);
struct value *funcbranch(struct func *, struct expr *, struct block *, struct block *);
struct value *funcexpr(struct func *, struct expr *);
void funcjmp(struct func *, struct block *);
struct block *funcdetach(struct func *, struct block **);
struct block *funcreattach(struct func *, struct block *);
void funcjnz(struct func *, struct value *, struct type *, struct block *, struct block *);
void funcret(struct func *, struct value *);
void funchlt(struct func *);
struct gotolabel *funcgoto(struct func *, char *);
void asangoto(struct func *, struct gotolabel *);
void asanlabel(struct func *, struct gotolabel *);
void asanswitch(struct func *, struct switchcases *);
void asancase(struct func *, struct switchcases *);
void funcswitch(struct func *, struct value *, struct switchcases *, struct block *);
/* asm goto: the C labels (struct gotolabel) and their names, nlab of them */
void funcasm(struct func *, char *template, struct asmoperand *out, unsigned nout, struct asmoperand *in, unsigned nin, char **clob, unsigned nclob, bool isvolatile, struct gotolabel **labels, char **labnames, unsigned nlab);
extern FILE *asmout;   /* the side file for inline-asm thunks (-a); null means inline asm is unavailable */
void emitasm(const char *);
void emitalias(struct decl *);   /* a GNU alias: the name set to its target, in the side file */
void emitsymattrs(void);         /* GNU weak and visibility, at the end */
void emitsymattr(struct decl *);   /* a file-scope asm's text, to the side file */
void funcinit(struct func *, struct decl *, struct init *, bool);

void emitfunc(struct func *, bool);
void emitdata(struct decl *, struct init *);
