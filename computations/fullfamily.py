# fullfamily.py -- the full family (1.1), with vanishing products a_k c_k allowed (Remark 1.7).
# J(n) := least J such that every matrix M of size n with chi_M = lam^n mod 2^J is nilpotent
#       = 1 + (largest finite 2-adic valuation of chi_M - lam^n).
# chi_M is the product of the characteristic polynomials of the blocks, which are pairs of the classes C_k.
# Only blocks with chi = lam^k mod 2 matter (otherwise the product is not lam^n mod 2), so by Lemma 2.3 the block
# diagonals have prescribed parities.  For n <= 7 the result is compared with a direct enumeration of all
# (d, b) in {-1,0,1}^n x {-1,0,1}^(n-1).     Usage: python3 fullfamily.py [nmax]   (default 12, about 15 s)
import itertools, sys, time
T0 = time.time()
def fold_odd(d, b, e): return (d + (0,) + d[::-1], b + (e, -e) + b[::-1])
def fold_even(d, b, dl): return (d[:-1] + (d[-1] - dl, d[-1] + dl) + d[:-1][::-1], b + (-1,) + b[::-1])
def reference(n):
    d, b = (0,), ()
    for dg in bin(n)[3:]: d, b = fold_odd(d, b, 1) if dg == "1" else fold_even(d, b, 1)
    return d
def charpoly(d, b):
    p0, p1 = (1,), (-d[0], 1)
    for k in range(1, len(d)):
        q = [0] + list(p1)
        for i, v in enumerate(p1): q[i] -= d[k] * v
        for i, v in enumerate(p0): q[i] -= b[k - 1] * v
        p0, p1 = p1, tuple(q)
    return p1
def pmul(f, g):
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, c in enumerate(g): h[i + j] += a * c
    return tuple(h)
def val(f):                      # valuation of f - lam^deg; None if zero
    c = [v for v in f[:-1] if v]
    if not c: return None
    m = 99
    for v in c:
        v = abs(v); t = 0
        while v % 2 == 0: v //= 2; t += 1
        m = min(m, t)
    return m
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
S = {}                           # S[k]: characteristic polynomials of the pairs of C_k with chi = lam^k mod 2
for k in range(1, NMAX + 1):
    par = [v % 2 for v in reference(k)]
    choices = [(-1, 1) if x else (0,) for x in par]
    S[k] = set()
    for d in itertools.product(*choices):
        for b in itertools.product((1, -1), repeat=k - 1):
            S[k].add(charpoly(d, b))
T = {0: {(1,)}}                  # T[n]: products over all block decompositions
best = {}
for n in range(1, NMAX + 1):
    T[n] = set()
    for k in range(1, n + 1):
        for f in S[k]:
            for g in T[n - k]: T[n].add(pmul(f, g))
    vals = [val(f) for f in T[n]]
    fin = [v for v in vals if v is not None]
    best[n] = max(fin) if fin else 0
    ell = n.bit_length() - 1
    wit = [f for f in T[n] if val(f) == best[n]][:2] or [None]
    print(f"n = {n:2d}: polynomials {len(T[n]):8d}, largest finite valuation {best[n]}, floor(log2 n) = {ell}, "
          f"{'EXCEEDS' if best[n] > ell else 'ok'}   e.g. {wit[0]}   ({time.time() - T0:.0f} s)", flush=True)

# direct enumeration for n <= 7
ok = True
for n in range(1, min(NMAX, 7) + 1):
    m = 0
    for d in itertools.product((-1, 0, 1), repeat=n):
        for b in itertools.product((-1, 0, 1), repeat=n - 1):
            v = val(charpoly(d, b))
            if v is not None and v > m: m = v
    ok &= m == best[n]
    print(f"direct enumeration, n = {n}: largest finite valuation {m}", flush=True)
J = [best[n] + 1 for n in range(1, NMAX + 1)]
print("J(n), n = 1..%d:" % NMAX, J)
f = pmul(charpoly((-1, 1), (1,)), charpoly((-1, -1, 0, 1, 1), (-1, -1, -1, -1)))
ok &= f == (0, -8, 0, 0, 0, 0, 0, 1) and J[:12] == [1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 5][:NMAX]
print("example: (lam^2 - 2)(lam^5 + 2 lam^3 + 4 lam) = lam^7 - 8 lam:", f == (0, -8, 0, 0, 0, 0, 0, 1))
print("PASS" if ok else "FAIL"); assert ok
