#include "rt.h"

/* -V: volatile accesses of 1, 2, 4 and 8 bytes are one access each, through the helpers of the side file */
volatile unsigned char vb;
volatile unsigned short vh;
volatile unsigned int vw;
volatile unsigned long long vq;
volatile int vi;

static unsigned int bump(void) {
	vw += 3;
	vq = vq * 2 + vw;
	return vw + vb + vh + (unsigned int)vq + (unsigned int)(vq >> 32);
}

int main(void) {
	unsigned int r;
	vb = 0x81; vh = 0xfffe; vw = 0x11223344u; vq = 0x0123456789abcdefull; vi = -5;
	P((int)vb); P((int)vh); P(vw);
	PX(vq);
	r = bump();
	P(r);
	PX(vq);
	P(vi + (int)vb);
	vb = vb + 1;   /* read-modify-write of a volatile is two accesses */
	P(vb);
	return 0;
}
