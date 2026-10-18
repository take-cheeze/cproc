/* a file-scope prototype of a builtin's name replaces the builtin: the call goes to the declared function */
int __atomic_compare_exchange(void *, void *, void *, int, int, int);

int cas(int *p, int *expected, int desired) {
	return __atomic_compare_exchange(p, expected, &desired, 0, 5, 5);
}
