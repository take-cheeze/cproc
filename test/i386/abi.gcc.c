/* compiled by gcc -m32 (abi.c is the cproc side) */
#include "rt.h"
struct s1 { char c; };
struct s3 { char c[3]; };
struct s6 { short h[3]; };
struct s8 { int a, b; };
struct s12 { int a, b, c; };
struct s40 { int w[10]; };
struct sl { char c; long long x; int i; };

int c_args(int, int, int, int, int);
int c_mixed(char, struct s3, short, struct s8, int);
struct s8 c_ret8(int, int);
struct s3 c_ret3(int);
struct s40 c_ret40(int);
int c_take40(struct s40, int);
int c_var(int, ...);
int c_take1(struct s1, struct s6, int);

int g_args(int a, int b, int c, int d, int e) { return c_args(a, b, c, d, e) * 2 + a - b * 2 + c * 3 - d * 4 + e * 5; }
int g_mixed(char a, struct s3 b, short c, struct s8 d, int e) { return c_mixed(a, b, c, d, e) + a + b.c[1] + c + d.b + e; }
struct s8 g_ret8(int a, int b) { struct s8 r = c_ret8(a, b); r.a += a; r.b += b; return r; }
struct s3 g_ret3(int v) { struct s3 r = c_ret3(v); r.c[1] += 1; return r; }
struct s40 g_ret40(int v) { struct s40 r = c_ret40(v); r.w[9] += c_take40(r, 1); return r; }
int g_take40(struct s40 s, int k) { return c_take40(s, k) + s.w[3]; }
int g_var(int n, ...) { __builtin_va_list ap; int s; __builtin_va_start(ap, n); s = c_var(3, __builtin_va_arg(ap, int), __builtin_va_arg(ap, int), 7); __builtin_va_end(ap); return s + n; }
int g_callback(int (*f)(int, int, int), int k) { struct s1 a = { 5 }; struct s6 b = { { 1, 2, 3 } }; return f(k, k + 1, k + 2) + c_take1(a, b, 10); }
int g_sl(struct sl *p) { return (int)sizeof *p * 1000 + p->i + __builtin_offsetof(struct sl, i); }
