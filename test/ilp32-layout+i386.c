/* i386 (ILP32): long and pointers are 4 bytes; long long and double are aligned on 4 in a struct, so its QBE type
 * spells them as words; va_list is a pointer, va_arg an aggregate walks it */
struct s { char c; long long x; double d; long l; void *p; };
struct t { short h; struct s s[2]; };
int sizes[] = {sizeof(long), sizeof(void *), sizeof(struct s), _Alignof(struct s), __builtin_offsetof(struct s, d),
	sizeof(long long), _Alignof(long long), sizeof(__builtin_va_list), sizeof(L'x')};
typedef int word __attribute__((mode(word)));
typedef int di __attribute__((mode(DI)));
int modes[] = {sizeof(word), sizeof(di)};
char *ptr = (char *)&sizes[1];
long diff(char *a, char *b) { return a - b; }
struct t get(struct t *p) { return *p; }
struct s arg(int n, ...) { __builtin_va_list ap; struct s r; __builtin_va_start(ap, n); r = __builtin_va_arg(ap, struct s); __builtin_va_end(ap); return r; }
