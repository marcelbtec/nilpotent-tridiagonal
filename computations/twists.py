# Twist patterns for "deg D_s <= d" at m = 2^K - 1 (mod-4 necessary condition).
# c_e = x f_{e-1} f_{m-1-e} mod 2 (e = 1..N); rho^(k) solves sum_e rho_e c_e = x^k over F_2.
import sys
def pmul2(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def fibs(m):                       # f_k mod 2 as bitmasks in x: f_0 = f_1 = 1, f_k = f_{k-1} + x f_{k-2}
    f = [1, 1]
    for k in range(2, m + 1): f.append(f[-1] ^ (f[-2] << 1))
    return f
def twists(K, d):
    m = 2 ** K - 1; N = (m - 1) // 2; f = fibs(m)
    c = [pmul2(f[e - 1], f[m - 1 - e]) << 1 for e in range(1, N + 1)]
    # Gaussian elimination over F_2: express each x^k in the basis c_1..c_N
    rows = []                                     # (vector, combination mask)
    for e, v in enumerate(c):
        comb = 1 << e
        for (w, cw) in rows:
            if v >> (w.bit_length() - 1) & 1: v ^= w; comb ^= cw
        assert v, "c_e dependent"
        rows.append((v, comb)); rows.sort(key=lambda t: -t[0])
    def solve(target):
        comb = 0
        for (w, cw) in rows:
            if target >> (w.bit_length() - 1) & 1: target ^= w; comb ^= cw
        assert target == 0
        return comb
    G0 = sum((( __import__('math').comb(m - k, k) // 2) & 1) << k for k in range(1, N + 1))
    assert all(__import__('math').comb(m - k, k) % 2 == 0 for k in range(1, N + 1))        # f_m = 1 mod 2
    assert G0 == sum(1 << (2 ** j) for j in range(K - 1)), "G0 != trace polynomial"       # (f_m - 1)/2 = x + x^2 + x^4 + ...
    assert solve(G0) == 1 << (N - 1)                                                       # fold pattern tau0 = e_N
    return m, N, [solve(1 << k) for k in range(1, d + 1)]
if __name__ == "__main__":
    K, d = int(sys.argv[1]), int(sys.argv[2])
    m, N, rho = twists(K, d)
    assert rho[0] == (1 << N) - 1                 # rho^(1) = all ones
    if len(sys.argv) > 3:
        for k, r in enumerate(rho, 1): print(f"rho^({k}) =", "".join(str(r >> e & 1) for e in range(N)))
    else:
        print(m, d, " ".join(str(r) for r in rho[1:]))
