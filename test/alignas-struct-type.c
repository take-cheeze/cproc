struct s1 {
	long x;
} __attribute__((aligned(128)));
struct s2 {
	char c;
	alignas(32) int x;
	alignas(64) char d;
};
struct s3 {
	struct s1 a;
	long b;
};
struct s1 f1(struct s1 a) {
	return a;
}
struct s2 f2(struct s2 a) {
	return a;
}
struct s3 f3(struct s3 a) {
	return a;
}
