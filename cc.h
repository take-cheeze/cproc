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
			struct decl *params;
			size_t nparam;
		} func;
		struct {
			char *tag;
			struct member *members;
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
	BUILTINALLOCA,
	BUILTINCONSTANTP,
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
		} obj;
		struct {
			/* the function might have an "inline definition" (C11 6.7.4p7) */
			bool inlinedefn;
			bool isnoreturn;
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
void tokenprint(const struct token *, FILE *);
char *tokenstr(enum tokenkind);
char *tokencheck(const struct token *, enum tokenkind, const char *);
void diagloc(const struct location *);
noreturn void error(const struct location *, const char *, ...);

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
};

struct attr {
	enum attrkind kind;
	int align;
	char *section;
	const char *cleanup;
};

bool attr(struct attr *, enum attrkind);
bool gnuattr(struct attr *, enum attrkind);

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

/* stmt */

void stmt(struct func *, struct scope *);

/* backend */

struct gotolabel {
	struct block *label;
	bool defined;
	/* -fsanitize=address (qbe.c asangoto, asanlabel): sets of block numbers, null when empty. The blocks open at the label
	 * (asanopen, once defined); for the gotos before it: the blocks open at any of them (asanfrom) and at all of them (asanall) */
	struct array *asanopen, *asanfrom, *asanall;
};

struct switchcases {
	void *root;
	struct type *type;
	struct block *defaultlabel;
	/* -fsanitize=address (qbe.c asanswitch, asancase): the blocks open at the switch, which the dispatch enters the cases from */
	struct array *asanopen;
};

void switchcase(struct switchcases *, unsigned long long, struct block *);

struct block *mkblock(char *);

struct value *mkglobal(struct decl *);

struct value *mkintconst(unsigned long long);

struct func *mkfunc(struct decl *, char *, struct type *, struct scope *);
void delfunc(struct func *);
struct type *functype(struct func *);
void funclabel(struct func *, struct block *);
struct value *funcbranch(struct func *, struct expr *, struct block *, struct block *);
struct value *funcexpr(struct func *, struct expr *);
void funcjmp(struct func *, struct block *);
void funcjnz(struct func *, struct value *, struct type *, struct block *, struct block *);
void funcret(struct func *, struct value *);
void funchlt(struct func *);
struct gotolabel *funcgoto(struct func *, char *);
void asangoto(struct func *, struct gotolabel *);
void asanlabel(struct func *, struct gotolabel *);
void asanswitch(struct func *, struct switchcases *);
void asancase(struct func *, struct switchcases *);
void funcswitch(struct func *, struct value *, struct switchcases *, struct block *);
void funcinit(struct func *, struct decl *, struct init *, bool);

void emitfunc(struct func *, bool);
void emitdata(struct decl *, struct init *);
