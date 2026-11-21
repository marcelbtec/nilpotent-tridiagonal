/* valuation.c -- largest 2-adic valuation of chi - lam^n over the pairs (d, b) of the class C_n.
   Usage: ./valuation nmax
   For each n the program enumerates all pairs whose diagonal is congruent modulo 2 to the diagonal of the
   integer reference fold (by Lemma 2.3 these are the pairs with chi = lam^n modulo 2) and all products
   b in {1,-1}^(n-1), computes chi exactly, and prints the number of pairs for each valuation of chi - lam^n.
   Expected (Corollary 1.6): largest finite valuation = floor(log2 n) if N_n is non-empty,
   and 1 + (number of final binary digits 1 of n) otherwise.
   Compile: gcc -O3 -march=native -fopenmp -o valuation valuation.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXN 28
static int n, par[MAXN + 1];
typedef struct { uint64_t hist[66]; } H;
static void step(int k, int d, int b, int64_t p[][MAXN + 1]) {
    for (int j = 0; j <= k; j++) {
        int64_t x = (j >= 1 ? p[k - 1][j - 1] : 0) - (j <= k - 1 ? d * p[k - 1][j] : 0);
        if (k >= 2 && j <= k - 2) x -= b * p[k - 2][j];
        p[k][j] = x;
    }
}
static void rec(int k, int64_t p[][MAXN + 1], H *h) {
    if (k > n) {
        int v = 65;
        for (int j = 0; j < n; j++) if (p[n][j]) { int c = __builtin_ctzll((uint64_t)p[n][j]); if (c < v) v = c; }
        h->hist[v]++; return;
    }
    for (int di = 0; di < (par[k] ? 2 : 1); di++)
        for (int bi = 0; bi < (k >= 2 ? 2 : 1); bi++) {
            step(k, par[k] ? (di ? 1 : -1) : 0, bi ? 1 : -1, p);
            rec(k + 1, p, h);
        }
}
static int reference(int m, int *r) {              /* integer fold of size m with all fold signs +1 */
    if (m == 1) { r[0] = 0; return 1; }
    int h = m / 2, q[MAXN + 1]; reference(h, q);
    if (m % 2) { for (int i = 0; i < h; i++) { r[i] = q[i]; r[m - 1 - i] = q[i]; } r[h] = 0; }
    else { for (int i = 0; i < h - 1; i++) { r[i] = q[i]; r[m - 1 - i] = q[i]; } r[h - 1] = q[h - 1] - 1; r[h] = q[h - 1] + 1; }
    return m;
}
int main(int argc, char **argv) {
    int nmax = argc > 1 ? atoi(argv[1]) : 19, allok = 1;
    for (n = 2; n <= nmax; n++) {
        int r[MAXN + 1]; reference(n, r);
        for (int k = 1; k <= n; k++) par[k] = abs(r[k - 1]) % 2;
        int L = n < 6 ? n : 6;                      /* parallel over the choices at the first L positions */
        H tot; memset(&tot, 0, sizeof tot);
        #pragma omp parallel
        {
            H loc; memset(&loc, 0, sizeof loc);
            int64_t p[MAXN + 1][MAXN + 1];
            #pragma omp for schedule(dynamic, 1)
            for (int code = 0; code < (1 << (2 * L)); code++) {
                memset(p, 0, sizeof p); p[0][0] = 1;
                int valid = 1;
                for (int k = 1; k <= L && valid; k++) {
                    int di = (code >> (2 * (k - 1))) & 1, bi = (code >> (2 * (k - 1) + 1)) & 1;
                    if ((!par[k] && di) || (k == 1 && bi)) { valid = 0; break; }
                    step(k, par[k] ? (di ? 1 : -1) : 0, bi ? 1 : -1, p);
                }
                if (valid) rec(L + 1, p, &loc);
            }
            #pragma omp critical
            for (int v = 0; v < 66; v++) tot.hist[v] += loc.hist[v];
        }
        int ell = 0; while ((2 << ell) <= n) ell++;
        int top = n >> (ell - 1), adm = (top == 3) || ((n + 1) == (3 << (ell - 1)));
        int t = 0; while ((n >> t) & 1) t++;
        int expect = adm ? ell : t + 1, vmax = 0; uint64_t pairs = 0;
        for (int v = 0; v < 65; v++) { pairs += tot.hist[v]; if (tot.hist[v]) vmax = v; }
        uint64_t nil = tot.hist[65]; pairs += nil;
        int ok = vmax == expect && tot.hist[0] == 0 && nil == (adm ? (1ULL << ell) : 0);
        allok &= ok;
        printf("n = %2d  %s  pairs with chi = lam^n mod 2: %11llu  nilpotent: %3llu  valuations:", n, adm ? "admissible    " : "not admissible",
               (unsigned long long)pairs, (unsigned long long)nil);
        for (int v = 1; v <= vmax; v++) printf(" v=%d: %llu", v, (unsigned long long)tot.hist[v]);
        printf("  largest: %d (expected %d)  %s\n", vmax, expect, ok ? "PASS" : "FAIL");
        fflush(stdout);
    }
    printf(allok ? "all sizes pass\n" : "FAILURE\n");
    return !allok;
}
