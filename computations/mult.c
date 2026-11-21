// Degrees of D_s for all s in {+-1}^(m-1): histogram of deg D_s (zero-eigenvalue multiplicity of T_m is m - 2 deg D_s).
// D_k = D_{k-1} + s_{k-1} x D_{k-2}, D_0 = D_1 = 1.  Depth-first over sign prefixes; OpenMP over the first bits.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W 20
static int m, N;
typedef struct { int32_t c[W]; } poly;
static void dfs(int k, const poly *a, const poly *b, uint64_t *hist) {   // a = D_{k-2}, b = D_{k-1}; build D_k
    for (int s = -1; s <= 1; s += 2) {
        poly d = *b;
        int top = (k) / 2;                                   // deg D_k <= floor(k/2)
        for (int j = 1; j <= top; j++) d.c[j] += s * a->c[j - 1];
        if (k == m) { int g = N; while (g > 0 && d.c[g] == 0) g--; hist[g]++; }
        else dfs(k + 1, b, &d, hist);
    }
}
int main(int argc, char **argv) {
    m = atoi(argv[1]); N = m / 2;
    int P = (m - 1 <= 12) ? 0 : 12;                          // prefix bits handled by the parallel loop
    uint64_t total[W] = {0};
    #pragma omp parallel
    {
        uint64_t hist[W] = {0};
        #pragma omp for schedule(dynamic, 8)
        for (long pre = 0; pre < (1L << P); pre++) {
            poly a, b, d; memset(&a, 0, sizeof a); memset(&b, 0, sizeof b); a.c[0] = b.c[0] = 1;   // D_0, D_1
            for (int k = 2; k < 2 + P; k++) {                // edges 1..P fixed by the prefix
                int s = ((pre >> (k - 2)) & 1) ? 1 : -1; d = b;
                for (int j = 1; j <= k / 2; j++) d.c[j] += s * a.c[j - 1];
                a = b; b = d;
            }
            dfs(2 + P, &a, &b, hist);
        }
        #pragma omp critical
        for (int g = 0; g < W; g++) total[g] += hist[g];
    }
    printf("m=%d:", m);
    for (int g = 0; g <= N; g++) if (total[g]) printf("  mult %d (deg %d): %llu", m - 2 * g, g, (unsigned long long)total[g]);
    printf("\n");
    return 0;
}
