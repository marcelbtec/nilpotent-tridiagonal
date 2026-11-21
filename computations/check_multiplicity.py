#!/usr/bin/env python3
"""
check_multiplicity.py -- zero-eigenvalue multiplicities of the skew-symmetric tridiagonal matrices T_m(u), u in {1, i}^(m-1).

s_k = u_k^2 = +-1,  det(lam - T) = lam^m D_s(lam^-2),  D_k = D_{k-1} + s_{k-1} x D_{k-2};  multiplicity of 0 = m - 2 deg D_s.

Python part (this file): sizes m <= 19 by brute force, the classification of deg D_s = 1, the anti-fold formulas.
C part: mult.c   (all 2^(m-1) patterns, histogram of deg D_s;  gcc -O3 -fopenmp -o mult mult.c;  ./mult 31)
        lowsym.c (patterns with deg D_s <= d inside the set allowed by the mod-4 condition; twists from twists.py:
                  set -- $(python3 twists.py 6 3); shift 2; ./lowsym 6 3 "$@"      -> sym_K6_d3.txt)
If low31.txt (all patterns with deg <= 7 at m = 31) and sym_K6_d3.txt are present, they are checked as well.
"""
import itertools, os, time
T0 = time.time()
def report(tag, ok, text):
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}: {text}   ({time.time() - T0:.0f} s)", flush=True); assert ok
def D(s):
    a, b = [1], [1]
    for sk in s:
        c = b + [0] * (len(a) + 1 - len(b))
        for j, v in enumerate(a): c[j + 1] += sk * v
        a, b = b, c
    while len(b) > 1 and b[-1] == 0: b.pop()
    return b
deg = lambda s: len(D(s)) - 1
v2 = lambda n: (n & -n).bit_length() - 1
def fold(sig, eps): return sig + (eps, -eps) + sig[::-1]
def FK(K):
    F = {()}
    for _ in range(K - 1): F = {fold(s, e) for s in F for e in (1, -1)}
    return F
neg = lambda t: tuple(-v for v in t)

# M1: bound mult <= 2^v2(m+1) - 1 and sharpness, all m <= 19
ok = True; table = {}
for m in range(2, 20):
    mults = {}
    for s in itertools.product((1, -1), repeat=m - 1):
        mu = m - 2 * deg(s); mults[mu] = mults.get(mu, 0) + 1
    table[m] = mults
    ok &= max(mults) == 2 ** v2(m + 1) - 1
report("M1", ok, "largest multiplicity of the eigenvalue 0 equals 2^v2(m+1) - 1 for every m <= 19 (all sign patterns)")
print("      m = 15:", dict(sorted(table[15].items())))

# M2: deg D_s = 1  <=>  s = (sigma, eps, eps, -rev sigma), sigma in F_(K-1);  D_s = 1 + 2 eps x
ok = True
for K in (2, 3, 4):
    m = 2 ** K - 1
    anti = {sig + (e, e) + neg(sig[::-1]): e for sig in FK(K - 1) for e in (1, -1)}
    brute = {s for s in itertools.product((1, -1), repeat=m - 1) if deg(s) == 1}
    ok &= brute == set(anti) and all(D(s) == [1, 2 * e] for s, e in anti.items()) and len(anti) == 2 ** (K - 1)
report("M2", ok, "deg D_s = 1 exactly for the anti-folds (sigma, eps, eps, -rev sigma), sigma in F_(K-1); D_s = 1 + 2 eps x; K = 2, 3, 4")

# M3: anti-folds for K <= 8: D = 1 + 2 eps x;  (sigma, eps, -eps, -rev sigma): D = 1 + 2 eps sum_j eta_j x^(2^j)
ok = True
for K in range(3, 9):
    polys = set()
    for sig in FK(K - 1):
        for e in (1, -1):
            ok &= D(sig + (e, e) + neg(sig[::-1])) == [1, 2 * e]
            p = D(sig + (e, -e) + neg(sig[::-1]))
            ok &= p[0] == 1 and all((abs(c) == 2) if ((k & (k - 1)) == 0 and k >= 2) else (c == 0) for k, c in enumerate(p) if k >= 1)
            ok &= len(p) - 1 == 2 ** (K - 2); polys.add(tuple(p))
    ok &= len(polys) == 2 ** (K - 2)
report("M3", ok, "anti-fold formulas for K <= 8; all 2^(K-2) polynomials 1 +- 2x^2 +- 2x^4 ... +- 2x^(2^(K-2)) occur, each twice")

# M4: files produced by the C programs
def load(f):
    out = []
    for line in open(f):
        s, rest = line.split(" ", 1); g, poly = rest.split(":")
        out.append((tuple(1 if ch == '+' else -1 for ch in s), int(g), [int(v) for v in poly.split()]))
    return out
for f, K, counts in (("low31.txt", 5, {0: 16, 1: 16, 2: 48, 3: 0}), ("sym_K6_d3.txt", 6, {0: 32, 1: 32, 2: 96, 3: 0})):
    if not os.path.exists(f): print(f"      ({f} not present, skipped)"); continue
    rows = [r for r in load(f) if r[1] <= 3]
    ok = all(D(s) == p for s, g, p in rows)                                   # recompute every polynomial
    hist = {g: sum(1 for r in rows if r[1] == g) for g in range(4)}
    ok &= hist == counts
    ok &= {s for s, g, p in rows if g == 0} == FK(K)
    ok &= {s for s, g, p in rows if g == 1} == {sig + (e, e) + neg(sig[::-1]) for sig in FK(K - 1) for e in (1, -1)}
    deg2 = sorted({tuple(p) for s, g, p in rows if g == 2})
    report("M4", ok, f"m = {2**K - 1}: patterns with deg D_s = 0, 1, 2, 3: {hist}; deg 0 = folds, deg 1 = anti-folds; "
           f"deg-2 polynomials {deg2}")
print("all checks passed")
