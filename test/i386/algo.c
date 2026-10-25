#include "rt.h"

typedef unsigned int u32;
typedef unsigned char u8;

static u32 crc32(const u8 *p, int n)
{
	u32 c = 0xffffffff;
	int k;

	while (n--) {
		c ^= *p++;
		for (k = 0; k < 8; k++)
			c = c & 1 ? (c >> 1) ^ 0xedb88320 : c >> 1;
	}
	return ~c;
}

static void isort(int *a, int n)
{
	int i, j, t;

	for (i = 1; i < n; i++) {
		t = a[i];
		for (j = i; j > 0 && a[j - 1] > t; j--)
			a[j] = a[j - 1];
		a[j] = t;
	}
}

static void qs(int *a, int lo, int hi)
{
	int i = lo, j = hi, p = a[(lo + hi) / 2], t;

	while (i <= j) {
		while (a[i] < p) i++;
		while (a[j] > p) j--;
		if (i <= j) { t = a[i]; a[i] = a[j]; a[j] = t; i++; j--; }
	}
	if (lo < j) qs(a, lo, j);
	if (i < hi) qs(a, i, hi);
}

static int sieve(int n)
{
	static char comp[2000];
	int i, j, c = 0;

	for (i = 2; i < n; i++) {
		if (comp[i]) continue;
		c++;
		for (j = i * i; j < n; j += i) comp[j] = 1;
	}
	return c;
}

static void matmul(int n, int a[n][n], int b[n][n], int c[n][n])
{
	int i, j, k;

	for (i = 0; i < n; i++)
		for (j = 0; j < n; j++) {
			c[i][j] = 0;
			for (k = 0; k < n; k++)
				c[i][j] += a[i][k] * b[k][j];
		}
}

struct node { int key; struct node *l, *r; };
static struct node pool[100];
static int npool;

static struct node *insert(struct node *t, int k)
{
	if (!t) { t = &pool[npool++]; t->key = k; t->l = t->r = 0; return t; }
	if (k < t->key) t->l = insert(t->l, k); else t->r = insert(t->r, k);
	return t;
}
static int depth(struct node *t) { int a, b; if (!t) return 0; a = depth(t->l); b = depth(t->r); return 1 + (a > b ? a : b); }
static int inorder(struct node *t, int *out, int n) { if (!t) return n; n = inorder(t->l, out, n); out[n++] = t->key; return inorder(t->r, out, n); }

typedef int (*binop)(int, int);
static int add(int a, int b) { return a + b; }
static int sub(int a, int b) { return a - b; }
static int mul(int a, int b) { return a * b; }
static int dv(int a, int b) { return b ? a / b : 0; }
static const binop ops[] = { add, sub, mul, dv };

/* a tiny stack machine */
static int eval(const char *s)
{
	int st[32], sp = 0;

	for (; *s; s++) {
		if (*s >= '0' && *s <= '9') st[sp++] = *s - '0';
		else if (*s == ' ') continue;
		else {
			int b = st[--sp], a = st[--sp];
			st[sp++] = ops[*s == '+' ? 0 : *s == '-' ? 1 : *s == '*' ? 2 : 3](a, b);
		}
	}
	return st[0];
}

static int popcount(u32 x) { int n = 0; while (x) { x &= x - 1; n++; } return n; }
static u32 rotl(u32 x, int n) { return x << n | x >> (32 - n); }
static int hash(const char *s) { u32 h = 5381; while (*s) h = h * 33 ^ (u8)*s++; return (int)(h % 100003); }

struct rec { char name[12]; short age; u8 flags; int score; };
static struct rec best(struct rec *r, int n)
{
	struct rec b = r[0];
	int i;
	for (i = 1; i < n; i++)
		if (r[i].score > b.score || (r[i].score == b.score && r[i].age < b.age))
			b = r[i];
	return b;
}

int main(void)
{
	static int arr[] = { 9, -3, 7, 100, 0, 42, -55, 8, 8, 1, 6 };
	int a2[11], i, n = sizeof arr / sizeof arr[0], out[20];
	int ma[3][3] = { {1, 2, 3}, {4, 5, 6}, {7, 8, 9} }, mb[3][3] = { {9, 8, 7}, {6, 5, 4}, {3, 2, 1} }, mc[3][3];
	struct node *root = 0;
	struct rec rs[3] = { { "ann", 30, 1, 77 }, { "bob", 25, 2, 91 }, { "cy", 22, 3, 91 } }, b;

	P((int)crc32((const u8 *)"The quick brown fox", 19));
	for (i = 0; i < n; i++) a2[i] = arr[i];
	isort(arr, n); for (i = 0; i < n; i++) P(arr[i]);
	qs(a2, 0, n - 1); for (i = 0; i < n; i++) P(a2[i] - arr[i]);
	P(sieve(2000));
	matmul(3, ma, mb, mc); for (i = 0; i < 9; i++) P(mc[i / 3][i % 3]);
	for (i = 0; i < 20; i++) root = insert(root, (i * 37) % 23);
	P(depth(root)); n = inorder(root, out, 0); for (i = 0; i < n; i++) P(out[i]);
	P(eval("34+2*")); P(eval("92-3*4/"));
	P(popcount(0xf0f0f0f1)); P((int)rotl(0x80000001, 4)); P(hash("hello world"));
	b = best(rs, 3); rt_puts(b.name); rt_puts("\n"); P(b.age); P(b.flags);
	return 0;
}
