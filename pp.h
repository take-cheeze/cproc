void ppinit(const char *, _Bool);

void next(void);
_Bool peek(int);
char *expect(int, const char *);
_Bool consume(int);

extern struct array incdirs;
