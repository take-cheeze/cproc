void rt_puts(const char *);
void rt_putd(int);
#define P(x) (rt_putd(x), rt_puts("\n"))
void rt_putx64(unsigned long long);
#define PX(x) (rt_putx64(x), rt_puts("\n"))
