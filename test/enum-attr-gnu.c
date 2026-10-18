/* Enumerators followed by GNU attribute specifiers before their values (my own reproducer). */
enum clock_id {
	CLOCK_FIRST __attribute__((availability(macosx, introduced=10.12))) __attribute__((availability(ios, introduced=10.0))) = 0,
	CLOCK_SECOND __attribute__((unused)),
	CLOCK_THIRD __attribute__((deprecated("use another"))) = 7
};
int main(void) {
	return CLOCK_FIRST + CLOCK_SECOND * 10 + CLOCK_THIRD * 100;
}
