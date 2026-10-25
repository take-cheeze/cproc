typedef unsigned long size_t;
void *memcpy(void *, const void *, size_t);
struct s { long a, b, c; };
void f(struct s *d, struct s *s) {
	memcpy(d, s, sizeof(*d));
}
void *g(void *d, void *s, size_t n) {
	memcpy(d, s, 0);
	return memcpy(d, s, n);
}
char big[200];
void h(char *s) {
	memcpy(big, s, sizeof(big));
}
