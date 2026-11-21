// All s in {+-1}^(m-1), m = 2^K - 1, with deg D_s <= d, found inside the set allowed by the mod-4 condition:
// s = (sigma, eps, eta, W rev sigma) with mirror twist W = (-1)^rho, rho in V_d (2^d patterns, supplied by twists.py).
// D_s = A B + x (eps A' B + eta A B'),  A = D_sigma, A' = D_(sigma minus last vertex), B, B' the same for the twisted chain.
// usage: lowsym K d rho2 ... rhod   (bitmask generators of V_d other than the all-ones pattern)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W 34
#define MAXTW 64
typedef struct { int32_t c[W]; } poly;
static int K, d, m, n, h, TW; static uint64_t rho[MAXTW];
typedef struct { poly prev[MAXTW], cur[MAXTW]; } state;
static uint64_t hist[W]; static FILE *out;
static void leaf(const state *st, const signed char *sig) {
    const poly *A = &st->cur[0], *A1 = &st->prev[0];
    for (int u = 0; u < TW; u++) {
        const poly *B0 = &st->cur[u], *B10 = &st->prev[u];
        int cbit = (rho[u] >> (n - 1)) & 1;
        for (int g = 1; g >= -1; g -= 2) for (int eps = 1; eps >= -1; eps -= 2) {
            int eta = -eps * (cbit ? -1 : 1) * g;           // centre pair: tau_N = 1 + rho_N (+1 for the global twist)
            int32_t Ds[W]; int ok = 1, k;
            for (k = n; k > d; k--) {                       // coefficients of D_s from the top; all must vanish
                long acc = 0;
                for (int i = 0; i <= h && i <= k; i++) {
                    int j = k - i;
                    if (j <= h) { long b = B0->c[j]; if (g < 0 && (j & 1)) b = -b; acc += (long)A->c[i] * b; }
                    j = k - 1 - i;
                    if (j >= 0 && j <= h) {
                        long b = B0->c[j], b1 = B10->c[j]; if (g < 0 && (j & 1)) { b = -b; b1 = -b1; }
                        acc += eps * (long)A1->c[i] * b + eta * (long)A->c[i] * b1;
                    }
                }
                if (acc) { ok = 0; break; }
            }
            if (!ok) continue;
            int deg = 0;
            for (k = d; k >= 0; k--) {
                long acc = 0;
                for (int i = 0; i <= h && i <= k; i++) {
                    int j = k - i;
                    if (j <= h) { long b = B0->c[j]; if (g < 0 && (j & 1)) b = -b; acc += (long)A->c[i] * b; }
                    j = k - 1 - i;
                    if (j >= 0 && j <= h) {
                        long b = B0->c[j], b1 = B10->c[j]; if (g < 0 && (j & 1)) { b = -b; b1 = -b1; }
                        acc += eps * (long)A1->c[i] * b + eta * (long)A->c[i] * b1;
                    }
                }
                Ds[k] = (int32_t)acc; if (acc && !deg) deg = k;
            }
            #pragma omp critical
            {
                hist[deg]++;
                for (int e = 1; e < n; e++) fputc(sig[e] > 0 ? '+' : '-', out);
                fputc(eps > 0 ? '+' : '-', out); fputc(eta > 0 ? '+' : '-', out);
                for (int e = n - 1; e >= 1; e--) { int w = ((rho[u] >> (e - 1)) & 1) ? -1 : 1; fputc(sig[e] * w * g > 0 ? '+' : '-', out); }
                fprintf(out, " %d :", deg); for (k = 0; k <= deg; k++) fprintf(out, " %d", Ds[k]); fputc('\n', out);
            }
        }
    }
}
static void dfs(int k, state *st, signed char *sig) {       // k = number of vertices of the half chain built so far
    if (k == n) { leaf(st, sig); return; }
    state nx;
    for (int s = -1; s <= 1; s += 2) {
        sig[k] = (signed char)s;                             // edge k joins vertices k and k+1
        for (int u = 0; u < TW; u++) {
            int w = ((rho[u] >> (k - 1)) & 1) ? -s : s;
            nx.prev[u] = st->cur[u]; nx.cur[u] = st->cur[u];
            int top = (k + 1) / 2;
            for (int j = 1; j <= top; j++) nx.cur[u].c[j] += w * st->prev[u].c[j - 1];
        }
        dfs(k + 1, &nx, sig);
    }
}
int main(int argc, char **argv) {
    K = atoi(argv[1]); d = atoi(argv[2]); m = (1 << K) - 1; n = (m - 1) / 2; h = (n - 1) / 2;
    int ng = argc - 3; uint64_t gen[8]; for (int i = 0; i < ng; i++) gen[i] = strtoull(argv[3 + i], 0, 10);
    TW = 1 << ng;
    for (int u = 0; u < TW; u++) { rho[u] = 0; for (int i = 0; i < ng; i++) if (u >> i & 1) rho[u] ^= gen[i]; }
    char name[64]; sprintf(name, "sym_K%d_d%d.txt", K, d); out = fopen(name, "w");
    int P = (n - 1 > 14) ? 10 : 0;
    #pragma omp parallel for schedule(dynamic, 4)
    for (long pre = 0; pre < (1L << P); pre++) {
        state st; signed char sig[64]; memset(&st, 0, sizeof st);
        for (int u = 0; u < TW; u++) st.cur[u].c[0] = 1;     // one vertex: D = 1; prev = D_0 = 1
        for (int u = 0; u < TW; u++) st.prev[u].c[0] = 1;
        state cur = st;
        for (int k = 1; k <= P; k++) {
            int s = ((pre >> (k - 1)) & 1) ? 1 : -1; sig[k] = (signed char)s; state nx;
            for (int u = 0; u < TW; u++) {
                int w = ((rho[u] >> (k - 1)) & 1) ? -s : s;
                nx.prev[u] = cur.cur[u]; nx.cur[u] = cur.cur[u];
                for (int j = 1; j <= (k + 1) / 2; j++) nx.cur[u].c[j] += w * cur.prev[u].c[j - 1];
            }
            cur = nx;
        }
        dfs(P + 1, &cur, sig);
    }
    fclose(out);
    printf("m=%d, deg<=%d:", m, d); for (int g = 0; g <= d; g++) printf("  deg %d: %llu", g, (unsigned long long)hist[g]); printf("\n");
    return 0;
}
