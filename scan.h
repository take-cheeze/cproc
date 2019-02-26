struct token;

enum scanflags {
	SCANHEADER = 1<<0,
};

int scanfrom(const char *file);
void scan(struct token *);

extern enum scanflags scanflags;
