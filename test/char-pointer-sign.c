void f(const char *s);
int g(unsigned char *p);
int main(void) {
	unsigned char buf[2] = {1, 2};
	signed char *q = buf;
	f(buf);
	return g(q);
}
