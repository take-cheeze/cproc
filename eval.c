#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

enum {
	F = 1<<8,
	S = 2<<8
};

/*
Constants of the 16-byte floating types are not folded by the arithmetic below, which computes in double. An operation on
them stays an expression and is evaluated at run time by a helper call (qbe.c). The only folded forms are a literal, a
conversion from an integer or floating constant, and the negation of a constant (a sign flip of the image).

An image holds the value of x as it is stored: long double is the x87 80-bit format (significand in soft[0], sign and
biased exponent in the low 16 bits of soft[1]); __float128 is IEEE binary128 (low 64 bits of the significand in soft[0],
then sign, exponent and the high 48 bits of the fraction in soft[1]). The value is taken from its long double form, so
it is exact when that has a significand of at most 64 bits (every integer below 2^64 and every double), and otherwise
rounded twice (decimal to long double, then to binary128). The exponent is found by scaling with powers of two, which is
exact, so the code does not depend on the math library.
*/
void
softimage(unsigned long long img[2], struct type *t, long double x)
{
	long double a;
	unsigned long long m = 0, bexp = 0, sign;
	int e = 0;

	sign = x < 0;
	a = x < 0 ? -x : x;
	if (a != a || a == a / 2 && a != 0) {
		/* NaN or infinity: the exponent field is all ones; the significand is the infinity's (or a NaN's quiet bit) */
		bexp = 32767;
		m = a != a ? 3ull << 62 : 1ull << 63;
	} else if (a != 0) {
		while (a >= 1) {
			a /= 2;
			++e;
		}
		while (a < 0.5L) {
			a *= 2;
			--e;
		}
		m = (unsigned long long)(a * 18446744073709551616.0L);  /* a * 2^64 is in [2^63, 2^64) */
		bexp = e - 1 + 16383;
	}
	if (t->kind == TYPEFLOAT128) {
		unsigned long long m63 = m & ~(1ull << 63);
		img[0] = m63 << 49;
		img[1] = sign << 63 | bexp << 48 | m63 >> 15;
	} else {
		img[0] = m;
		img[1] = sign << 15 | bexp;
	}
}

/*
An exact binary128 image of a decimal literal (a __float128 literal, `digits.digits e exp` with a Q suffix, as read from
the token). The value is rounded once, to nearest with ties to even, to 113 significant bits. The arithmetic is on a
bignum of 32-bit words (little endian): the digits are read into it; a non-negative exponent multiplies it by 10^e; a
negative one k shifts it left by s bits (enough that the quotient has at least 115 bits) and divides it by 5^k, in steps of
5^13 (a 32-bit divisor), keeping a sticky bit from the remainders; the value is then X * 2^(-k-s) with the sticky bit.
A hexadecimal literal is not handled here (softimage is used instead).
*/
typedef struct {
	uint32_t *w;
	size_t n;
} bignum;

static void
bn_mul_small(bignum *x, uint32_t m, uint32_t add)
{
	uint64_t carry = add;
	size_t i;

	for (i = 0; i < x->n; ++i) {
		uint64_t t = (uint64_t)x->w[i] * m + carry;
		x->w[i] = (uint32_t)t;
		carry = t >> 32;
	}
	assert(carry == 0);
}

static uint32_t
bn_divmod_small(bignum *x, uint32_t d)
{
	uint64_t rem = 0;
	size_t i;

	for (i = x->n; i-- > 0;) {
		uint64_t cur = rem << 32 | x->w[i];
		x->w[i] = (uint32_t)(cur / d);
		rem = cur % d;
	}
	return (uint32_t)rem;
}

static void
bn_shl(bignum *x, size_t s)
{
	for (; s >= 30; s -= 30)
		bn_mul_small(x, 1u << 30, 0);
	if (s)
		bn_mul_small(x, 1u << s, 0);
}

static size_t
bn_bitlen(const bignum *x)
{
	size_t i, b;
	uint32_t v;

	for (i = x->n; i-- > 0;) {
		if (x->w[i]) {
			for (v = x->w[i], b = 0; v; v >>= 1)
				++b;
			return i * 32 + b;
		}
	}
	return 0;
}

static int
bn_bit(const bignum *x, size_t i)
{
	return i / 32 < x->n && (x->w[i / 32] >> i % 32 & 1);
}

/* any bit below position i is set */
static bool
bn_below(const bignum *x, size_t i)
{
	size_t k;

	for (k = 0; k < i / 32 && k < x->n; ++k) {
		if (x->w[k])
			return true;
	}
	return i / 32 < x->n && i % 32 && (x->w[i / 32] & (1u << i % 32) - 1);
}

void
softliteral(unsigned long long img[2], const char *lit)
{
	static const uint32_t pow10[] = {1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000};
	static const uint32_t pow5_13 = 1220703125u;
	char *digits, *end;
	const char *s;
	size_t nd = 0, i, len, words, shift, sz, e2len;
	long exp10 = 0, k, e2 = 0;
	unsigned long long q_lo = 0, q_hi = 0, hi48;
	long biased;
	bignum x;
	bool dot = false, sticky = false, rbit, sticky2;
	int c;
	uint32_t v;

	img[0] = img[1] = 0;
	if (lit[0] == '0' && (lit[1] == 'x' || lit[1] == 'X'))
		fatal("internal error; hexadecimal __float128 literal");
	digits = xmalloc(strlen(lit) + 1);
	for (s = lit; *s; ++s) {
		if (isdigit((unsigned char)*s)) {
			if (nd || *s != '0')
				digits[nd++] = *s;
			if (dot)
				--exp10;
		} else if (*s == '.') {
			dot = true;
		} else if (*s == 'e' || *s == 'E') {
			exp10 += strtol(s + 1, &end, 10);
			break;
		} else {
			break;
		}
	}
	if (nd == 0)
		return;
	/* sizes: about 3.33 bits per power of ten, plus the digits, plus room for the shifts */
	sz = nd + (size_t)(exp10 < 0 ? -exp10 : exp10);
	words = (4 * sz + 256) / 32 + 16;
	x.w = xmalloc(words * sizeof(uint32_t));
	memset(x.w, 0, words * sizeof(uint32_t));
	x.n = words;
	for (i = 0; i < nd; i += len) {
		len = nd - i < 9 ? nd - i : 9;
		v = 0;
		for (c = 0; c < (int)len; ++c)
			v = v * 10 + (uint32_t)(digits[i + c] - '0');
		bn_mul_small(&x, pow10[len], v);
	}
	if (exp10 >= 0) {
		for (k = exp10; k > 0;) {
			len = k < 9 ? k : 9;
			bn_mul_small(&x, pow10[len], 0);
			k -= len;
		}
	} else {
		k = -exp10;
		/* s = 115 + 3k + 64 - bitlen(N), at least 0: the quotient then has at least 178 bits, more than 115 */
		shift = bn_bitlen(&x);
		shift = 115 + 3 * (size_t)k + 64 > shift ? 115 + 3 * (size_t)k + 64 - shift : 0;
		bn_shl(&x, shift);
		for (; k > 0;) {
			len = k < 13 ? k : 13;
			v = 1;
			for (c = 0; c < (int)len; ++c)
				v *= 5;
			if (len == 13)
				v = pow5_13;
			if (bn_divmod_small(&x, v))
				sticky = true;
			k -= len;
		}
		/* value = X * 2^(-k - s), and -k is exp10 */
		e2 = exp10 - (long)shift;
	}
	e2len = bn_bitlen(&x);
	if (e2len < 113) {
		bn_shl(&x, 113 - e2len);
		e2 -= (long)(113 - e2len);
		e2len = 113;
	}
	shift = e2len - 113;
	for (i = 0; i < 113; ++i) {
		if (bn_bit(&x, shift + i)) {
			if (i < 64)
				q_lo |= 1ull << i;
			else
				q_hi |= 1ull << (i - 64);
		}
	}
	rbit = shift && bn_bit(&x, shift - 1);
	sticky2 = sticky || (shift >= 2 && bn_below(&x, shift - 1));
	e2 += (long)shift;
	if (rbit && (sticky2 || (q_lo & 1))) {
		if (++q_lo == 0)
			++q_hi;
		if (q_hi == 1ull << 49) {
			q_hi = 1ull << 48;
			q_lo = 0;
			++e2;
		}
	}
	biased = e2 + 112 + 16383;
	if (biased >= 32767) {
		img[1] = 32767ull << 48;  /* infinity */
	} else if (biased > 0) {
		hi48 = q_hi & ((1ull << 48) - 1);
		img[0] = q_lo;
		img[1] = (unsigned long long)biased << 48 | hi48;
	}  /* else below the least normal: zero (no literal of this program is that small) */
	free(x.w);
	free(digits);
}

unsigned long long
softsignbit(struct type *t)
{
	return t->kind == TYPEFLOAT128 ? 1ull << 63 : 1ull << 15;
}

static bool
issoft(struct type *t)
{
	return t->prop & PROPSOFT;
}

/*
The IEEE binary16 image of _Float16 (2 bytes). halfbits rounds a double to the nearest binary16 value, ties to even,
from its exact value, so the result is that of a single rounding; halfvalue is the double of an image. Both work on
the bits, so the code does not depend on the host having a _Float16 type.
*/
static unsigned
halfmag(unsigned long long m, int e2)
{
	unsigned long long q, rem, half;
	unsigned code;
	int p, E, Q, s;

	/* m > 0; the value is m * 2^e2 */
	for (p = 0; m >> p > 1; ++p)
		;
	E = p + e2;  /* the value is in [2^E, 2^(E+1)) */
	if (E > 15)
		return 0x7c00;
	Q = E >= -14 ? E - 10 : -24;  /* exponent of the last bit kept */
	s = Q - e2;  /* bits of m that are dropped */
	if (s <= 0) {
		q = m << -s;
	} else if (s > 60) {
		q = 0;
	} else {
		q = m >> s;
		rem = m & (1ull << s) - 1;
		half = 1ull << s - 1;
		if (rem > half || (rem == half && (q & 1)))
			++q;
	}
	/* a normal number has q in [1024, 2048]; a carry to 2048 raises the exponent */
	if (E >= -14)
		code = (unsigned)(((E + 15) << 10) + (q - 1024));
	else
		code = (unsigned)q;
	return code >= 0x7c00 ? 0x7c00 : code;
}

unsigned
halfbits(double x)
{
	unsigned long long u, m;
	unsigned sign;
	int exp, e2;

	memcpy(&u, &x, sizeof u);
	sign = (unsigned)(u >> 63) << 15;
	exp = u >> 52 & 0x7ff;
	m = u & (1ull << 52) - 1;
	if (exp == 0x7ff)
		return sign | (m ? 0x7e00 : 0x7c00);
	if (exp == 0) {
		if (m == 0)
			return sign;
		e2 = -1074;
	} else {
		m |= 1ull << 52;
		e2 = exp - 1075;
	}
	return sign | halfmag(m, e2);
}

double
halfvalue(unsigned bits)
{
	unsigned long long u;
	unsigned exp, man;
	double x;

	exp = bits >> 10 & 31;
	man = bits & 1023;
	if (exp == 0) {
		/* a subnormal, man * 2^-24: exact as a double */
		x = (double)man / 16777216.0;
	} else {
		if (exp == 31)
			u = 0x7ffull << 52 | (man ? 1ull << 51 : 0);
		else
			u = (unsigned long long)(exp + 1008) << 52 | (unsigned long long)man << 42;
		memcpy(&x, &u, sizeof x);
	}
	if (bits >> 15)
		x = -x;
	return x;
}

static void
cast(struct expr *expr)
{
	struct type *t;
	unsigned long long m;

	t = expr->type;
	if (t->prop & PROPFLOAT) {
		if (t->size == 4)
			expr->u.constant.f = (float)expr->u.constant.f;
		else if (t->size == 2)
			expr->u.constant.f = halfvalue(halfbits(expr->u.constant.f));
	} else if (t->prop & PROPINT) {
		m = 1ull << t->u.arith.width - 1;
		expr->u.constant.u &= m | m - 1;
		if (t->u.arith.issigned)
			expr->u.constant.u = (expr->u.constant.u ^ m) - m;
	}
}

static void
unary(struct expr *expr, enum tokenkind op, struct expr *l)
{
	if (issoft(l->type)) {
		if (op != TSUB)
			return;
		expr->kind = EXPRCONST;
		expr->u.constant.soft[0] = l->u.constant.soft[0];
		expr->u.constant.soft[1] = l->u.constant.soft[1] ^ softsignbit(expr->type);
		return;
	}
	expr->kind = EXPRCONST;
	if (l->type->prop & PROPFLOAT)
		op |= F;
	switch (op) {
	case TSUB:      expr->u.constant.u = -l->u.constant.u; break;
	case TSUB|F:    expr->u.constant.f = -l->u.constant.f; break;
	default:
		fatal("internal error; unknown unary expression");
	}
	cast(expr);
}

static void
binary(struct expr *expr, enum tokenkind op, struct expr *l, struct expr *r)
{
	expr->kind = EXPRCONST;
	if (l->type->prop & PROPFLOAT)
		op |= F;
	else if (l->type->prop & PROPINT && l->type->u.arith.issigned)
		op |= S;
	switch (op) {
	case TMUL:
	case TMUL|S:     expr->u.constant.u = l->u.constant.u * r->u.constant.u; break;
	case TMUL|F:     expr->u.constant.f = l->u.constant.f * r->u.constant.f; break;
	case TDIV:       expr->u.constant.u = l->u.constant.u / r->u.constant.u; break;
	case TDIV|S:     expr->u.constant.i = l->u.constant.i / r->u.constant.i; break;
	case TDIV|F:     expr->u.constant.f = l->u.constant.f / r->u.constant.f; break;
	case TMOD:       expr->u.constant.u = l->u.constant.u % r->u.constant.u; break;
	case TMOD|S:     expr->u.constant.i = l->u.constant.i % r->u.constant.i; break;
	case TADD:
	case TADD|S:     expr->u.constant.u = l->u.constant.u + r->u.constant.u; break;
	case TADD|F:     expr->u.constant.f = l->u.constant.f + r->u.constant.f; break;
	case TSUB:
	case TSUB|S:     expr->u.constant.u = l->u.constant.u - r->u.constant.u; break;
	case TSUB|F:     expr->u.constant.f = l->u.constant.f - r->u.constant.f; break;
	case TSHL:
	case TSHL|S:     expr->u.constant.u = l->u.constant.u << (r->u.constant.u & 63); break;
	case TSHR:       expr->u.constant.u = l->u.constant.u >> (r->u.constant.u & 63); break;
	case TSHR|S:     expr->u.constant.i = l->u.constant.i >> (r->u.constant.u & 63); break;
	case TBAND:
	case TBAND|S:    expr->u.constant.u = l->u.constant.u & r->u.constant.u; break;
	case TBOR:
	case TBOR|S:     expr->u.constant.u = l->u.constant.u | r->u.constant.u; break;
	case TXOR:
	case TXOR|S:     expr->u.constant.u = l->u.constant.u ^ r->u.constant.u; break;
	case TLESS:      expr->u.constant.u = l->u.constant.u < r->u.constant.u; break;
	case TLESS|S:    expr->u.constant.u = l->u.constant.i < r->u.constant.i; break;
	case TLESS|F:    expr->u.constant.u = l->u.constant.f < r->u.constant.f; break;
	case TGREATER:   expr->u.constant.u = l->u.constant.u > r->u.constant.u; break;
	case TGREATER|S: expr->u.constant.u = l->u.constant.i > r->u.constant.i; break;
	case TGREATER|F: expr->u.constant.u = l->u.constant.f > r->u.constant.f; break;
	case TLEQ:       expr->u.constant.u = l->u.constant.u <= r->u.constant.u; break;
	case TLEQ|S:     expr->u.constant.u = l->u.constant.i <= r->u.constant.i; break;
	case TLEQ|F:     expr->u.constant.u = l->u.constant.f <= r->u.constant.f; break;
	case TGEQ:       expr->u.constant.u = l->u.constant.u >= r->u.constant.u; break;
	case TGEQ|S:     expr->u.constant.u = l->u.constant.i >= r->u.constant.i; break;
	case TGEQ|F:     expr->u.constant.u = l->u.constant.f >= r->u.constant.f; break;
	case TEQL:
	case TEQL|S:     expr->u.constant.u = l->u.constant.u == r->u.constant.u; break;
	case TEQL|F:     expr->u.constant.u = l->u.constant.f == r->u.constant.f; break;
	case TNEQ:
	case TNEQ|S:     expr->u.constant.u = l->u.constant.u != r->u.constant.u; break;
	case TNEQ|F:     expr->u.constant.u = l->u.constant.f != r->u.constant.f; break;
	default:
		fatal("internal error; unknown binary expression");
	}
	cast(expr);
}

struct expr *
eval(struct expr *expr)
{
	struct expr *l, *r, *c;
	struct decl *d;
	struct type *t;

	t = expr->type;
	switch (expr->kind) {
	case EXPRIDENT:
		d = expr->u.ident.decl;
		if (d->kind != DECLCONST)
			break;
		expr->kind = EXPRCONST;
		expr->u.constant.u = d->u.enumconst;
		break;
	case EXPRCOMPOUND:
		d = expr->u.compound.decl;
		if (d->u.obj.storage != SDSTATIC)
			break;
		d->value = mkglobal(d);
		emitdata(d, expr->u.compound.init);
		expr->kind = EXPRIDENT;
		expr->u.ident.decl = d;
		break;
	case EXPRUNARY:
		l = eval(expr->base);
		switch (expr->op) {
		case TBAND:
			switch (l->kind) {
			case EXPRUNARY:
				if (l->op == TMUL)
					expr = eval(l->base);
				break;
			case EXPRSTRING:
				l->u.ident.decl = stringdecl(l);
				l->kind = EXPRIDENT;
				expr->base = l;
				break;
			}
			break;
		case TMUL:
			break;
		default:
			if (l->kind != EXPRCONST)
				break;
			unary(expr, expr->op, l);
			break;
		}
		break;
	case EXPRCAST:
		l = eval(expr->base);
		if (l->kind == EXPRCONST && (issoft(t) || issoft(l->type))) {
			/* only an integer or floating constant converted to a 16-byte floating type is folded */
			if (issoft(t) && !issoft(l->type)) {
				expr->kind = EXPRCONST;
				if (l->type->prop & PROPINT)
					softimage(expr->u.constant.soft, t, l->type->u.arith.issigned ? (long double)l->u.constant.i : (long double)l->u.constant.u);
				else
					softimage(expr->u.constant.soft, t, l->u.constant.f);
			}
		} else if (l->kind == EXPRCONST) {
			expr->kind = EXPRCONST;
			if (l->type->prop & PROPINT && t->prop & PROPFLOAT) {
				if (l->type->u.arith.issigned)
					expr->u.constant.f = l->u.constant.i;
				else
					expr->u.constant.f = l->u.constant.u;
			} else if (l->type->prop & PROPFLOAT && t->prop & PROPINT) {
				if (t->u.arith.issigned) {
					if (l->u.constant.f < -0x1p63 || l->u.constant.f >= 0x1p63)
						error(&tok.loc, "integer part of floating-point constant %g cannot be represented as signed integer", l->u.constant.f);
					expr->u.constant.i = l->u.constant.f;
				} else {
					if (l->u.constant.f < 0.0 || l->u.constant.f >= 0x1p64)
						error(&tok.loc, "integer part of floating-point constant %g cannot be represented as unsigned integer", l->u.constant.f);
					expr->u.constant.u = l->u.constant.f;
				}
			} else {
				expr->u.constant = l->u.constant;
			}
			cast(expr);
		} else if (l->type->kind == TYPEPOINTER) {
			/*
			A cast from a pointer to integer is not a valid constant
			expression, but C11 allows implementations to recognize
			other forms of constant expressions (6.6p10), and some
			programs expect this functionality.
			*/
			if (t->kind == TYPEPOINTER || t->prop & PROPINT && t->size == typelong.size)
				expr = l;
		}
		break;
	case EXPRBINARY:
		l = eval(expr->u.binary.l);
		r = eval(expr->u.binary.r);
		expr->u.binary.l = l;
		expr->u.binary.r = r;
		if (issoft(l->type) || issoft(r->type))
			break;
		switch (expr->op) {
		case TADD:
			if (r->kind == EXPRBINARY)
				c = l, l = r, r = c;
			/* fallthrough */
		case TSUB:
			if (r->kind != EXPRCONST)
				break;
			if (l->kind == EXPRCONST) {
				binary(expr, expr->op, l, r);
			} else if (l->kind == EXPRBINARY && l->type->kind == TYPEPOINTER && l->op == TADD && l->u.binary.r->kind == EXPRCONST) {
				/* (P + C1) ± C2  ->  P + (C1 ± C2) */
				binary(expr->u.binary.r, expr->op, l->u.binary.r, r);
				expr->op = TADD;
				expr->u.binary.l = l->u.binary.l;
			}
			break;
		case TLOR:
			if (l->kind != EXPRCONST)
				break;
			return l->u.constant.u ? l : r;
		case TLAND:
			if (l->kind != EXPRCONST)
				break;
			return l->u.constant.u ? r : l;
		default:
			if (l->kind != EXPRCONST || r->kind != EXPRCONST)
				break;
			binary(expr, expr->op, l, r);
		}
		break;
	}

	return expr;
}
