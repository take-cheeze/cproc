int load(int *p, int *out) {
	__atomic_load(p, out, 5);
	return *out;
}

void store(int *p, int *in) {
	__atomic_store(p, in, 5);
}

int exchange(int *p, int *in, int *out) {
	__atomic_exchange(p, in, out, 5);
	return *out;
}

_Bool cas(int *p, int *expected, int *desired) {
	return __atomic_compare_exchange(p, expected, desired, 0, 5, 5);
}
