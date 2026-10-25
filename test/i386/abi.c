#include "rt.h"
/* calls between cproc+QBE code (this file) and gcc code (abi.gcc.c), both ways */
struct s1 { char c; };
struct s3 { char c[3]; };
struct s6 { short h[3]; };
struct s8 { int a, b; };
struct s12 { int a, b, c; };
struct s40 { int w[10]; };
struct sl { char c; long long x; int i; };

int g_args(int, int, int, int, int);
int g_mixed(char, struct s3, short, struct s8, int);
struct s8 g_ret8(int, int);
struct s3 g_ret3(int);
struct s40 g_ret40(int);
int g_take40(struct s40, int);
int g_var(int, ...);
int g_callback(int (*)(int, int, int), int);
int g_sl(struct sl *);

int c_args(int a, int b, int c, int d, int e) { return a - b * 2 + c * 3 - d * 4 + e * 5; }
int c_mixed(char a, struct s3 b, short c, struct s8 d, int e) { return a + b.c[0] + b.c[2] * 10 + c * 100 + d.a * 1000 + d.b + e; }
struct s8 c_ret8(int a, int b) { struct s8 r = { a * 2, b * 3 }; return r; }
struct s3 c_ret3(int v) { struct s3 r = { { v, v + 1, v + 2 } }; return r; }
struct s40 c_ret40(int v) { struct s40 r; int i; for (i = 0; i < 10; i++) r.w[i] = v + i; return r; }
int c_take40(struct s40 s, int k) { int i, t = 0; for (i = 0; i < 10; i++) t += s.w[i] * k; return t; }
int c_cb(int a, int b, int c) { return a * 100 + b * 10 + c; }
int c_var(int n, ...) { __builtin_va_list ap; int s = 0; __builtin_va_start(ap, n); while (n--) s = s * 10 + __builtin_va_arg(ap, int); __builtin_va_end(ap); return s; }
int c_take1(struct s1 a, struct s6 b, int c) { return a.c + b.h[0] + b.h[2] + c; }

int main(void)
{
	struct s3 s3 = { { 1, 2, 3 } };
	struct s8 s8 = { 4, 5 }, r8;
	struct s40 s40;
	struct sl sl;
	int i;

	P(g_args(1, 2, 3, 4, 5));
	P(g_mixed(-1, s3, 300, s8, 9));
	r8 = g_ret8(6, 7); P(r8.a); P(r8.b);
	s3 = g_ret3(40); P(s3.c[0] + s3.c[1] + s3.c[2]);
	s40 = g_ret40(100); P(s40.w[0] + s40.w[9]);
	P(g_take40(s40, 2));
	P(g_var(4, 1, 2, 3, 4));
	P(g_callback(c_cb, 3));
	sl.c = 'x'; sl.i = 77; P(sizeof(struct sl)); P(g_sl(&sl));
	for (i = 0; i < 3; i++) { r8 = c_ret8(i, i + 1); P(r8.a + r8.b); }
	return 0;
}
