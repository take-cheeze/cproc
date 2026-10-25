void rt_puts(const char *);
void rt_putd(int);
#define P(x) (rt_putd(x), rt_puts("\n"))
