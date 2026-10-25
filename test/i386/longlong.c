#include "rt.h"
/* 64-bit integers: QBE's i386 splits them into words; divisions are libgcc calls (rt.c has them) */
typedef long long ll;
typedef unsigned long long ull;

struct acc { int n; ll sum; ull bits; char tag; };

static ll fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
static ull fib(int n) { ull a = 0, b = 1, t; while (n--) { t = a + b; a = b; b = t; } return a; }
static ull mix(ull x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdull; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ull; x ^= x >> 33; return x; }
static int cmp(ll a, ll b) { return (a < b) - (a > b) + 2 * ((ull)a < (ull)b) - 4 * (a == b); }
static ll args(int a, ll b, int c, ll d, int e) { return a + b * c - d * e; }
static struct acc add(struct acc s, ll v) { s.n++; s.sum += v; s.bits |= 1ull << (v & 63); return s; }
static unsigned strtou(const char *s, ull *out) { ull v = 0; unsigned n = 0; while (*s >= '0' && *s <= '9') { v = v * 10 + (*s++ - '0'); n++; } *out = v; return n; }
static ll vsum(int n, ...) { __builtin_va_list ap; ll s = 0; __builtin_va_start(ap, n); while (n--) s += __builtin_va_arg(ap, ll); __builtin_va_end(ap); return s; }

int main(void)
{
	static ll tab[] = { 0, 1, -1, 0x7fffffff, -0x80000000ll, 0x100000000ll, 0x123456789abcdefll, -987654321012345ll };
	struct acc a = { 0, 0, 0, 'q' };
	ull u;
	int i, j;

	PX(fact(20)); PX(fib(90)); PX(mix(12345)); PX(mix(0xdeadbeefcafebabeull));
	for (i = 0; i < 8; i++)
		for (j = 0; j < 8; j++) {
			ll x = tab[i], y = tab[j];
			P(cmp(x, y));
			PX(x * y + (x ^ y) - (x | y));
			if (y) { PX(x / y); PX(x % y); PX((ull)x / (ull)y); PX((ull)x % (ull)y); }
			PX(x << (j * 9 % 64)); PX(x >> (i * 7 % 64)); PX((ull)x >> (j * 5 % 64));
		}
	for (i = 0; i < 8; i++) a = add(a, tab[i]);
	P(a.n); PX(a.sum); PX(a.bits); P(a.tag); P(sizeof a);
	P(strtou("18446744073709551615", &u)); PX(u);
	PX(args(3, 0x100000001ll, -2, 77, 9));
	PX(vsum(3, 1ll, -2ll, 0x500000000ll));
	{ unsigned w = 4000000000u; int k = -5; ll e = w; ll f = k; ull g = (ull)k; PX(e); PX(f); PX(g); P((int)(e >> 1)); P((unsigned short)(g >> 40)); }
	{ ll big = 1; for (i = 0; i < 70; i++) big = big * 3 + i; PX(big); P(big > 0); P(!big); P(big ? 1 : 2); }
	{ static int iv[] = { 0, 1, -1, 0x7fffffff, -0x7fffffff - 1, 65536, -3 };
	  for (i = 0; i < 7; i++) for (j = 0; j < 7; j++) {
		int r; unsigned ur; ll lr; short sr;
		P(__builtin_add_overflow(iv[i], iv[j], &r)); P(r);
		P(__builtin_sub_overflow(iv[i], iv[j], &ur)); P(ur);
		P(__builtin_mul_overflow(iv[i], iv[j], &r)); P(r);
		P(__builtin_mul_overflow(iv[i], iv[j], &sr)); P(sr);
		P(__builtin_mul_overflow((ll)iv[i] << 20, (ll)iv[j] << 13, &lr)); PX(lr);
	  } }
	return 0;
}
