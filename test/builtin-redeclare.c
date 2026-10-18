/* a prototype of a builtin's name replaces the builtin (GCC allows this; libc++ and generated C declare the
 * generic __atomic_* forms) */
_Bool __atomic_compare_exchange(void *, void *, void *, _Bool, int, int);
int main(void)
{
	int x = 1, y = 0, z = 2;
	return __atomic_compare_exchange(&x, &y, &z, 0, 5, 5);
}
