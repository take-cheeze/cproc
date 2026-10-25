#include "rt.h"

struct pt { short x, y; };
struct big { int a[7]; char tag; };
struct bf { unsigned a : 3, b : 5; signed c : 6; unsigned d : 18; };
union u { int i; unsigned char b[4]; short h[2]; };
enum color { RED = 1, GREEN = 5, BLUE = 9 };

static int counter;
static const char *names[] = { "zero", "one", "two" };
int table[10] = { 1, 2, 3, [7] = 8 };
struct pt gpt = { -3, 4 };
struct pt *gptp = &gpt;
char msg[] = "hello";

static int fib(int n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
static struct pt add(struct pt a, struct pt b) { struct pt r = { a.x + b.x, a.y + b.y }; return r; }
static struct big mkbig(int k) { struct big b; int i; for (i = 0; i < 7; i++) b.a[i] = k * i; b.tag = 'A' + k; return b; }
static int sumbig(struct big b) { int s = b.tag, i; for (i = 0; i < 7; i++) s += b.a[i]; return s; }
static int apply(int (*f)(int), int x) { return f(x) + f(x + 1); }
static int sq(int x) { return x * x; }
static unsigned udiv(unsigned a, unsigned b) { return a / b + a % b; }
static int sdiv(int a, int b) { return a / b * 100 + a % b; }
static int classify(int x)
{
	switch (x) {
	case 0: return 10;
	case 1: case 2: return 20;
	case 5 ... 9: return 30;
	case 100: return 40;
	case -7: return 50;
	default: return 60;
	}
}
static int strlen_(const char *s) { const char *p = s; while (*p) p++; return p - s; }
static void rev(char *s) { int n = strlen_(s), i; for (i = 0; i < n / 2; i++) { char t = s[i]; s[i] = s[n - 1 - i]; s[n - 1 - i] = t; } }
static int many(int a, int b, int c, int d, int e, int f, int g, int h, int i, int j)
{
	int x = a * b + c * d - e * f + g * h - i * j;
	int y = (a ^ j) + (b | i) - (c & h) + (d << 2) - (e >> 1) + (f % 7) + g / 3;
	return x * 3 + y;
}
static int vla(int n) { int a[n], i, s = 0; for (i = 0; i < n; i++) a[i] = i * i; for (i = 0; i < n; i++) s += a[i]; return s + sizeof a; }
static int lp(int n) { int i = 0, s = 0; again: if (i < n) { s += i++; goto again; } return s; }
static int chars(signed char a, unsigned char b, short c, unsigned short d) { return a * 1000 + b * 100 + c * 10 + d; }
static signed char tochar(int x) { return x; }
static unsigned short toushort(int x) { return x; }
static int statics(void) { static int n = 5; return n++; }
static int shifts(int x, unsigned u, int n) { return (x << n) ^ (x >> n) ^ (int)(u >> n); }

int main(void)
{
	struct pt a = { 1, 2 }, b = { 10, 20 }, c;
	struct big bg;
	struct bf f = { 5, 17, -9, 100000 };
	union u un;
	char buf[16];
	int i, s;
	enum color col = GREEN;

	P(fib(15));
	c = add(a, b); P(c.x); P(c.y);
	c = add(c, *gptp); P(c.x * 100 + c.y);
	bg = mkbig(3); P(sumbig(bg)); P(bg.tag);
	P(apply(sq, 7));
	P(udiv(4000000000u, 7)); P(sdiv(-100, 7)); P(sdiv(100, -7));
	for (i = -8; i < 12; i++) P(classify(i)); P(classify(100));
	P(strlen_(names[2])); P(names[1][1]);
	for (i = 0; i < 6; i++) buf[i] = msg[i]; rev(buf); rt_puts(buf); rt_puts("\n");
	P(many(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)); P(many(-5, 3, 11, -2, 8, 1, 0, 9, -4, 6));
	P(vla(10)); P(lp(10));
	P(chars(-3, 200, -300, 60000)); P(tochar(300)); P(toushort(-1));
	P(statics()); P(statics());
	P(f.a); P(f.b); P(f.c); P(f.d); f.c = 31; f.a = 9; P(f.c); P(f.a); P(sizeof f);
	un.i = 0x01020304; P(un.b[0]); P(un.h[1]);
	P(col == GREEN ? BLUE : RED);
	s = 0; for (i = 0; i < 10; i++) s += table[i]; P(s);
	P(shifts(-12345, 0xdeadbeef, 3)); P(shifts(7, 1, 0));
	P((i > 3 && i < 100) || counter++); P(counter);
	P(sizeof(long)); P(sizeof(void *)); P(sizeof(struct big)); P(_Alignof(struct big));
	{ int *p = &table[2], *q = &table[8]; P(q - p); P(*(p + 5)); P(p[-1]); }
	{ struct pt arr[3] = { {1, 2}, {3, 4}, {5, 6} }, *pp = arr; pp++; P(pp->y); P((char *)&arr[2] - (char *)arr); }
	{ unsigned char x = 250; x += 10; P(x); short y = 32767; y++; P(y); }
	{ int k = 1000000; P(k * k / 1000); unsigned m = 3000000000u; P(m > 2000000000u); P((int)m < 0); }
	return 0;
}
