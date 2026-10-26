/* a tentative definition of a thread-local object, then its definition with an initializer (6.9.2; EDG writes a
 * file-scope thread_local so), and one that stays tentative */
static _Thread_local long a;
static _Thread_local long a = 100;
_Thread_local int b;
_Thread_local int b = 11;
static _Thread_local int c;
long f(void) {
	return a + b + c;
}
