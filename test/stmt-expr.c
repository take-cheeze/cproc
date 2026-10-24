/* GNU statement expressions: the value of the last expression statement, evaluated where the expression is. */
int g(int);
int early(int x) { int v = ({ int t = g(x); if (t < 0) return -1; t; }); return v + 1; }
int cond(int c) { return c ? ({ int a = g(1); a * 2; }) : 7; }
int logic(int c) { return c && ({ g(2); }); }
int loop(void) { int n = 0; while (({ n++; n < 5; })) ; return n; }
int nested(void) { return ({ int a = 3; ({ int b = a + 1; b * 2; }); }); }
void voidexpr(int *p) { ({ *p = 1; }); }
