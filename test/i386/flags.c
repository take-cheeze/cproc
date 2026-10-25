#include "rt.h"
/* found by random testing: an 8-bit extension of esi (no byte register) between the test of the if and its jump
 * used to be andl $255, which clobbered the flags */
typedef unsigned long long ull;
static int f0(int v0, unsigned char v1, unsigned long long v2, unsigned char v3)
{
	if (v0 & 1) v0 = (int)(((v0) >= (((ull)(((v1) > (26338u) ? (v1) : (26338u) + 1)) + (ull)(((((v2) < (v0))) | (v0)))))));
	else v0 ^= (int)(((ull)(((((ull)(14520ll) / ((ull)(((37959) < (v3))) | 1))) ^ (((((v0) < (61726))) >= (((v0) ^ (v1))))))) * (ull)(v3)));
	return v0;
}
int main(void)
{
	P(f0(-3956, 241, 1773, 117)); P(f0(-3955, 241, 1773, 117)); P(f0(8, 3, 0x100000000ull, 255));
	return 0;
}
