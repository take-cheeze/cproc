#include "rt.h"

/* GNU extended inline asm on the i386 targets: the thunks load and store the operands as gcc's allocation does */
static unsigned add(unsigned a, unsigned b) {
	__asm__("addl %2, %0" : "=r"(a) : "0"(a), "g"(b) : "cc");
	return a;
}

static unsigned mulfixed(unsigned a, unsigned b) {   /* the fixed %eax and %edx of a widening multiply */
	unsigned lo = a, hi;
	__asm__("mull %3" : "=a"(lo), "=d"(hi) : "0"(lo), "rm"(b));
	return lo ^ hi;
}

static unsigned setflag(unsigned a, unsigned b) {   /* a flag output: a byte register set from the flags */
	int lt;
	__asm__("cmpl %2, %1" : "=@ccl"(lt) : "r"(a), "r"(b));
	return (unsigned)lt;
}

static unsigned char bytes(unsigned char a, unsigned char b) {   /* byte operands take a byte register */
	unsigned char r = a;
	__asm__("addb %1, %0" : "+q"(r) : "qm"(b) : "cc");
	return r;
}

static unsigned cpu(unsigned leaf) {   /* cpuid writes %ebx, which the thunk saves and restores */
	unsigned a, b, c, d;
	__asm__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "0"(leaf) : );
	return a ^ c ^ d;
}

static unsigned shift(unsigned v, unsigned n) {   /* a variable count in %cl */
	__asm__("shll %%cl, %0" : "+r"(v) : "c"(n) : "cc");
	return v;
}

static unsigned tied(unsigned *p) {   /* a memory operand: the thunk loads its address */
	unsigned old = *p;
	__asm__("incl %0" : "+m"(*p) : : "cc");
	return old + *p;
}

int main(void) {
	P(add(40, 2));
	P(mulfixed(0x12345678u, 0x9abcdef0u));
	P(setflag(3, 7));
	P(setflag(9, 2));
	P(bytes(200, 100));
	P(cpu(0) != 0);
	P(shift(3, 4));
	{ unsigned v = 10; P(tied(&v)); P(v); }
	return 0;
}
