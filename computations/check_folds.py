#!/usr/bin/env python3
"""
check_folds.py -- nilpotent tridiagonal matrices with entries in {-1, 0, 1}: fold classification, Liu matrices, counts.

Coordinates: a tridiagonal matrix with diagonal d_1..d_n and off-diagonal entries a_k (above), c_k (below) has the
characteristic polynomial of the pair (d, b), b_k = a_k c_k.  "Class": d_k in {0, 1, -1}, b_k in {1, -1}.

Folds (n = size of the input):
    odd  step, n -> 2n+1:  (d, b) -> ((d, 0, rev d),                                  (b, eps, -eps, rev b))
    even step, n -> 2n:    (d, b) -> ((d_1..d_{n-1}, d_n - dl, d_n + dl, d_{n-1}..d_1), (b, -1, rev b))
An iterated fold of size n starts from the 1 x 1 zero matrix and follows the binary digits of n.

usage: python3 check_folds.py [NEXH]      (NEXH = largest size of the filtered exhaustive search, default 22; 27 takes minutes)
"""
import itertools, random, sys, time
import numpy as np
T0 = time.time(); random.seed(3)
def report(tag, ok, text):
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}: {text}   ({time.time() - T0:.0f} s)", flush=True); assert ok

# ---------- basic objects ----------
def charpoly(d, b):
    p0, p1 = [1], [-d[0], 1]
    for k in range(1, len(d)):
        q = [0] + p1
        for i, v in enumerate(p1): q[i] -= d[k] * v
        for i, v in enumerate(p0): q[i] -= b[k - 1] * v
        p0, p1 = p1, q
    return p1
def nilp(d, b): return not any(charpoly(d, b)[:-1])
def fold_odd(d, b, eps): return (d + (0,) + d[::-1], b + (eps, -eps) + b[::-1])
def fold_even(d, b, dl): return (d[:-1] + (d[-1] - dl, d[-1] + dl) + d[:-1][::-1], b + (-1,) + b[::-1])
def family(n, pop=None):
    if n == 1: return {((0,), ())}
    out = set()
    for (d, b) in family(n // 2, pop):
        for e in (1, -1):
            nd, nb = fold_odd(d, b, e) if n % 2 else fold_even(d, b, e)
            if pop is None or all(v in pop for v in nd): out.add((nd, nb))
    return out
POP = (0, 1, -1)
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def moments(d, b, J):                       # mu_j = (M^j)_{11}
    n = len(d); v = [0] * n; v[0] = 1; out = []
    for _ in range(J):
        out.append(v[0]); w = [0] * n
        for i in range(n):
            w[i] += d[i] * v[i]
            if i + 1 < n: w[i] += b[i] * v[i + 1]
            if i > 0: w[i] += v[i - 1]
        v = w
    return out
def prefixes(n):
    out = set()
    while n: out.add(n); n //= 2
    return out

# ---------- F1: folding identities ----------
ok = True
for _ in range(3000):
    n = random.randint(1, 12)
    d = tuple(random.randint(-3, 3) for _ in range(n)); b = tuple(random.choice((1, -1)) for _ in range(n - 1))
    c = charpoly(d, b); c2 = pmul(c, c)
    for e in (1, -1):
        ok &= charpoly(*fold_odd(d, b, e)) == [0] + c2 and charpoly(*fold_even(d, b, e)) == c2
report("F1", ok, "chi(odd fold) = lam chi^2 and chi(even fold) = chi^2 for 3000 random integer pairs (d, b), n <= 12")

# ---------- F2: Liu's test matrices ----------
g14 = (-1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 1, 1, -1)
d14 = (0,) * 6 + (-1, 1) + (0,) * 6                                   # Ferreira-Parlett-Dopico (2012)
d28 = (0,) * 6 + (-1, 1) + (0,) * 5 + (-1, 1) + (0,) * 5 + (1, -1) + (0,) * 6     # Bini-Gemignani-Tisseur (2005)
g28 = g14 + (-1,) + g14
ok = nilp(d14, g14) and nilp(d28, g28) and (d14, g14) in family(14, POP) and (d28, g28) in family(28, POP)
report("F2", ok, "Liu-14 and Liu-28 are nilpotent and are iterated folds")

# ---------- F3: folds are nilpotent; admissible sizes ----------
ok = all(nilp(d, b) for n in range(1, 41) for (d, b) in family(n))
report("F3", ok, "every iterated fold with integer diagonal is nilpotent, n <= 40")
def admissible(n):
    j = 0
    while 3 * 2 ** j - 1 <= n:
        if n == 3 * 2 ** j - 1 or 3 * 2 ** j <= n <= 2 ** (j + 2) - 1: return True
        j += 1
    return n == 1
ok = all((len(family(n, POP)) == (2 ** (n.bit_length() - 1) if admissible(n) else 0)) for n in range(1, 201))
report("F4", ok, "folds with diagonal in {0,1,-1} exist exactly for n = 1, 3*2^j - 1, 3*2^j..2^(j+2) - 1; "
       "2^floor(log2 n) gauge classes each (n <= 200)")

# ---------- F5: plain brute force ----------
ok = True
for n in range(1, 11):
    found = set()
    ds = np.array([d for d in itertools.product(POP, repeat=n) if sum(d) == 0], dtype=np.int64)
    for b in itertools.product((1, -1), repeat=n - 1):
        m = ds.shape[0]
        p0 = np.zeros((m, n + 1), dtype=np.int64); p0[:, 0] = 1
        p1 = np.zeros((m, n + 1), dtype=np.int64); p1[:, 1] = 1; p1[:, 0] = -ds[:, 0]
        for k in range(1, n):
            q = np.zeros_like(p1); q[:, 1:] = p1[:, :-1]; q -= ds[:, k:k + 1] * p1; q -= b[k - 1] * p0
            p0, p1 = p1, q
        for row in ds[~p1[:, :n].any(axis=1)]: found.add((tuple(int(x) for x in row), b))
    ok &= found == family(n, POP)
report("F5", ok, "brute force over all (d, b) in the class, n <= 10: nilpotent set = fold family")

# ---------- F6: filtered exhaustive search (mod 2 support, mod 4 linear system, exact check) ----------
def supports(n, chunk_bits=22):
    out = []; lo_bits = min(n, chunk_bits); lo = np.arange(1 << lo_bits, dtype=np.uint64)
    for hi in range(1 << (n - lo_bits)):
        masks = lo | (np.uint64(hi) << np.uint64(lo_bits))
        p_prev = np.ones_like(masks); p_cur = np.uint64(2) | (masks & np.uint64(1))
        for k in range(2, n + 1):
            dk = (masks >> np.uint64(k - 1)) & np.uint64(1)
            p_prev, p_cur = p_cur, (p_cur << np.uint64(1)) ^ (p_cur * dk) ^ p_prev
        out.extend(int(x) for x in masks[p_cur == np.uint64(1 << n)])
    return out
def pmul2(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def bits_of(p): return sum((v & 1) << i for i, v in enumerate(p))
def solve_f2(cols, rhs):
    basis = {}; null = []
    for e, v in enumerate(cols):
        combo = 1 << e
        while v:
            h = v.bit_length() - 1
            if h in basis: v ^= basis[h][0]; combo ^= basis[h][1]
            else: basis[h] = (v, combo); break
        if v == 0: null.append(combo)
    r = rhs; sol = 0
    while r:
        h = r.bit_length() - 1
        if h not in basis: return None, None
        r ^= basis[h][0]; sol ^= basis[h][1]
    return sol, null
def classify(n):
    S_list = supports(n); found = set(); cand = 0
    for S in S_list:
        idx = [k for k in range(n) if (S >> k) & 1]
        dbase = [1 if (S >> k) & 1 else 0 for k in range(n)]; bbase = [1] * (n - 1)
        chi = charpoly(dbase, bbase)
        rhs = bits_of([(-v) // 2 % 2 for v in chi[:-1]] + [0])
        lead = [1] + [bits_of(charpoly(dbase[:k], bbase[:k - 1])) for k in range(1, n + 1)]
        trail = [bits_of(charpoly(dbase[k:], bbase[k:])) for k in range(0, n)] + [1, 1]
        cols = [pmul2(lead[k], trail[k + 1]) for k in idx] + [pmul2(lead[k], trail[k + 2]) for k in range(n - 1)]
        sol, null = solve_f2(cols, rhs)
        if sol is None: continue
        cand += 1 << len(null); nv = len(idx)
        for mask in range(1 << len(null)):
            x = sol
            for i, nb in enumerate(null):
                if (mask >> i) & 1: x ^= nb
            d = [0] * n
            for j, k in enumerate(idx): d[k] = 1 - 2 * ((x >> j) & 1)
            b = [1 - 2 * ((x >> (nv + k)) & 1) for k in range(n - 1)]
            if nilp(d, b): found.add((tuple(d), tuple(b)))
    return found, len(S_list), cand
NEXH = int(sys.argv[1]) if len(sys.argv) > 1 else 22
ok = True; uniq = True; tot = 0
for n in range(1, NEXH + 1):
    found, ns, cand = classify(n); ok &= found == family(n, POP); uniq &= ns == 1; tot += cand
report("F6", ok and uniq, f"filtered exhaustive search, n <= {NEXH}: one diagonal support mod 2 for each n; "
       f"{tot} candidates survive mod 4 in total; nilpotent set = fold family")

# ---------- F7: rank condition R'(n) ----------
def support(n):
    if n == 1: return [0]
    s = support(n // 2)
    if n % 2: return s + [0] + s[::-1]
    t = s[:-1] + [s[-1] ^ 1]
    return t + t[::-1]
def rank_f2(vs):
    basis = {}; rk = 0
    for v in vs:
        while v:
            h = v.bit_length() - 1
            if h in basis: v ^= basis[h]
            else: basis[h] = v; rk += 1; break
    return rk
def Rprime(n):
    S = support(n); lead = [1]; p0, p1 = 0, 1
    for k in range(n):
        p0, p1 = p1, (p1 << 1) ^ (p1 if S[k] else 0) ^ p0
        lead.append(p1)
    if lead[n] != 1 << n or S != S[::-1]: return False
    T = lambda j: lead[n - j]
    A = [pmul2(lead[k - 1], T(k)) for k in range(1, n + 1)]            # vertex k:  chi_{<k} chi_{>k}
    B = [pmul2(lead[k - 1], T(k + 1)) for k in range(1, n)]            # edge k:    chi_{<k} chi_{>k+1}
    reps = [A[k] for k in range((n + 1) // 2)] + [B[k] for k in range(n // 2)]
    return rank_f2(reps) == len(reps)
ok = all(Rprime(n) for n in range(2, 1025))
report("F7", ok, "rank condition R'(n): the derivative polynomials of the mirror orbits are independent over F_2, 2 <= n <= 1024")

# ---------- F8: uniqueness of the support mod 2 (Wang-Massey) and the binary-prefix law mod 2 ----------
def det2(M):
    M = [row[:] for row in M]; n = len(M)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c]), None)
        if p is None: return 0
        M[c], M[p] = M[p], M[c]
        for r in range(c + 1, n):
            if M[r][c]: M[r] = [x ^ y for x, y in zip(M[r], M[c])]
    return 1
ok = True
for n in range(1, 7):
    for bits in itertools.product((0, 1), repeat=2 * n - 1):
        c = (None,) + bits                                             # c[1..2n-1]
        plcp = all(det2([[c[a + b - 1] for b in range(1, j + 1)] for a in range(1, j + 1)]) for j in range(1, n + 1))
        wm = c[1] == 1 and all(c[2 * i + 1] == c[2 * i] ^ c[i] for i in range(1, n))
        ok &= plcp == wm
report("F8a", ok, "finite Wang-Massey criterion (Hankel minors H_1..H_n nonzero iff c_1 = 1 and c_(2i+1) = c_(2i) + c_i), n <= 6")
def laurent_f2(S):
    n = len(S); v = [0] * n; v[0] = 1; out = []
    for _ in range(2 * n):
        out.append(v[0]); w = [0] * n
        for i in range(n):
            w[i] ^= S[i] & v[i]
            if i + 1 < n: w[i] ^= v[i + 1]
            if i > 0: w[i] ^= v[i - 1]
        v = w
    return out
ok = True
for n in range(1, 400):
    c = laurent_f2(support(n)); P = prefixes(n)
    ok &= all(c[j] == (1 if (j + 1) in P else 0) for j in range(2 * n))
report("F8b", ok, "mod 2 the resolvent entry of the fold support is the sum of lam^(-p) over the binary prefixes p of n, n < 400")

# ---------- F9: binary-prefix law over Z ----------
ok = True
for n in range(1, 41):
    P = sorted(prefixes(n)); fam = family(n); sigs = set()
    for (d, b) in fam:
        mu = moments(d, b, n + 3)
        ok &= all((abs(mu[j]) == 1) if (j + 1) in P else (mu[j] == 0) for j in range(n + 3))
        sigs.add(tuple(mu[p - 1] for p in P))
    ok &= len(sigs) == len(fam) == 2 ** (len(P) - 1)
report("F9", ok, "moments (M^j)_11 of every fold: +-1 if j+1 is a binary prefix of n, else 0; sign vectors <-> folds, n <= 40")

# ---------- F10: number of nilpotent tridiagonal matrices with all entries in {-1,0,1} ----------
def brute_count(n):
    wvals = [(-1, 2), (0, 5), (1, 2)]; total = 0
    ds = np.array(list(itertools.product(POP, repeat=n)), dtype=np.int64); ds = ds[ds.sum(axis=1) == 0]
    for ws in itertools.product(range(3), repeat=n - 1):
        mult = 1
        for i in ws: mult *= wvals[i][1]
        w = [wvals[i][0] for i in ws]; m = ds.shape[0]
        p0 = np.zeros((m, n + 1), dtype=np.int64); p0[:, 0] = 1
        p1 = np.zeros((m, n + 1), dtype=np.int64); p1[:, 1] = 1; p1[:, 0] = -ds[:, 0]
        for k in range(1, n):
            q = np.zeros_like(p1); q[:, 1:] = p1[:, :-1]; q -= ds[:, k:k + 1] * p1; q -= w[k - 1] * p0
            p0, p1 = p1, q
        total += mult * int((~p1[:, :n].any(axis=1)).sum())
    return total
U = lambda m: len(family(m, POP)) * 2 ** (m - 1)
memo = {}
def count(n):
    if n not in memo: memo[n] = U(n) + sum(U(k) * 5 * count(n - k) for k in range(1, n))
    return memo[n]
bf = [brute_count(n) for n in range(1, 7)]
report("F10", bf == [count(n) for n in range(1, 7)] == [1, 9, 73, 585, 4809, 39113],
       f"count of nilpotent tridiagonal {{-1,0,1}} matrices: brute force = formula = {bf}, n = 1..6")
print("      formula, n = 7..16:", [count(n) for n in range(7, 17)])

# ---------- F11: integer diagonals outside {0,1,-1} ----------
ex = ((0, -2, 1, -1, 2, 0), (-1,) * 5)
report("F11", nilp(*ex) and ex not in family(6), "diagonal (0,-2,1,-1,2,0), all b_k = -1: nilpotent, not a fold "
       "(the classification needs the population {-1,0,1})")
print("all checks passed")
