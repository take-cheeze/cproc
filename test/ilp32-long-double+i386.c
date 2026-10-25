/* i386: long double has gcc's layout (12 bytes, on 4), but its values are refused */
struct m { char c; long double d; int i; };
int sz[] = {sizeof(long double), _Alignof(long double), sizeof(struct m), __builtin_offsetof(struct m, i)};
long double f(void);
int g(void) { return f() > 0; }
