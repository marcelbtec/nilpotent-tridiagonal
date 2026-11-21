#!/usr/bin/env python3
"""check_revision.py -- tests of the statements added after the first draft (numbering of the sixth version).
R1 Theorem 1.5 (rigidity modulo 4)          R2 Corollary 1.6 (nilpotency modulo powers of two)
R3 Remark 3.1 (recognition)                 R4 examples: the hypothesis of Takata et al., Remark 3.3, Section 4.1
R5 Remark 5.4                                R6 Liu's matrices as printed in the sources (Section 4.1)
R7 the chains of Takata et al. (Section 4.2) R8 Corollaries 1.2 and 1.4, and the count of Section 6
Run time: about one minute.  See also valuation.c for Corollary 1.6(ii), (iii) up to n = 21."""
import itertools, random, time
from fractions import Fraction
import numpy as np
T0 = time.time(); random.seed(7)
def report(tag, ok, text):
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}: {text}   ({time.time() - T0:.0f} s)", flush=True); assert ok
POP = (0, 1, -1)
def charpoly(d, b):
    p0, p1 = [1], [-d[0], 1]
    for k in range(1, len(d)):
        q = [0] + p1
        for i, v in enumerate(p1): q[i] -= d[k] * v
        for i, v in enumerate(p0): q[i] -= b[k - 1] * v
        p0, p1 = p1, q
    return p1
def fold_odd(d, b, e): return (d + (0,) + d[::-1], b + (e, -e) + b[::-1])
def fold_even(d, b, dl): return (d[:-1] + (d[-1] - dl, d[-1] + dl) + d[:-1][::-1], b + (-1,) + b[::-1])
def family(n):
    if n == 1: return {((0,), ())}
    out = set()
    for (d, b) in family(n // 2):
        for e in (1, -1):
            nd, nb = fold_odd(d, b, e) if n % 2 else fold_even(d, b, e)
            if all(v in POP for v in nd): out.add((nd, nb))
    return out
def admissible(n):
    s = bin(n)[2:]; return n == 1 or s.startswith("11") or (s.startswith("10") and set(s[2:]) <= {"1"})
def val2(x):
    x = abs(x); v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def content_val(p, n):                       # 2-adic valuation of chi - lam^n (None if zero)
    c = [v for v in p[:n] if v]
    return min(val2(v) for v in c) if c else None

def all_polys(n):
    """yield (ds, b, coefficient array) for all pairs of C_n; coefficients low degree first, shape (3^n, n+1)"""
    ds = np.array(list(itertools.product(POP, repeat=n)), dtype=np.int64)
    for b in itertools.product((1, -1), repeat=n - 1):
        m = ds.shape[0]
        p0 = np.zeros((m, n + 1), dtype=np.int64); p0[:, 0] = 1
        p1 = np.zeros((m, n + 1), dtype=np.int64); p1[:, 1] = 1; p1[:, 0] = -ds[:, 0]
        for k in range(1, n):
            q = np.zeros_like(p1); q[:, 1:] = p1[:, :-1]; q -= ds[:, k:k + 1] * p1; q -= b[k - 1] * p0
            p0, p1 = p1, q
        yield ds, b, p1

def recognise(d, b):
    """O(n) test: returns the fold history (list of signs, outermost first) if (d, b) in C_n is nilpotent, else None"""
    d = list(d); b = list(b); hist = []
    while len(d) >= 2:
        n = len(d); h = n // 2
        if any(d[k] != d[n - 1 - k] for k in range(h - 1)): return None           # mirror positions k < h (1-based k <= h-1)
        if any(b[k] != b[n - 2 - k] for k in range(h - 1)): return None
        if n % 2:
            if d[h - 1] != d[h + 1] or d[h] != 0 or b[h - 1] != -b[h]: return None
            hist.append(('odd', b[h - 1])); d, b = d[:h], b[:h - 1]
        else:
            if d[h - 1] != -d[h] or d[h] == 0 or b[h - 1] != -1: return None
            hist.append(('even', d[h])); d, b = d[:h - 1] + [0], b[:h - 1]
    return hist if d[0] == 0 else None

okA = okB = okC = okS = True; sharp = {}; vmax = {}
for n in range(1, 11):
    h = n // 2; ell = n.bit_length() - 1
    nil = set(); mod4 = set(); near = False; vmax[n] = 0
    for ds, b, P in all_polys(n):
        E = P[:, :n]                                                               # chi - lam^n
        z = ~E.any(axis=1)
        m4 = ~(E % 4).any(axis=1)
        mk = ~(E % (2 ** (ell + 1))).any(axis=1)
        okB &= bool((mk == z).all())                                               # power-of-two test
        if ell >= 1: near |= bool((~(E % (2 ** ell)).any(axis=1) & ~z).any())      # sharpness witness
        for j in range(vmax[n] + 1, 8):                                            # largest valuation of a non-nilpotent pair
            if (~(E % (2 ** j)).any(axis=1) & ~z).any(): vmax[n] = j
            else: break
        for row in ds[z]: nil.add((tuple(int(x) for x in row), b))
        for row in ds[m4]: mod4.add((tuple(int(x) for x in row), b))
    sharp[n] = near
    if n >= 2:                                                                     # modulo-4 lemma
        folds = set()
        for dp in itertools.product(POP, repeat=h):
            for bp in itertools.product((1, -1), repeat=h - 1):
                if any(v % 2 for v in charpoly(dp, bp)[:h]): continue              # q = lam^h mod 2
                for e in (1, -1):
                    nd, nb = fold_odd(dp, bp, e) if n % 2 else fold_even(dp, bp, e)
                    if all(v in POP for v in nd): folds.add((nd, nb))
        okA &= folds == mod4
    okC &= nil == family(n)
    for ds, b, P in all_polys(n) if n <= 8 else []:                                # recognition, exhaustive n <= 8
        z = ~P[:, :n].any(axis=1)
        for row, zz in zip(ds, z): okS &= (recognise(row.tolist(), b) is not None) == bool(zz)
report("R1", okA, "modulo-4 lemma: chi = lam^n mod 4 exactly for the admissible folds of parents with q = lam^h mod 2; all pairs, n <= 10")
report("R2a", okB and okC, "power-of-two test: chi = lam^n iff chi = lam^n mod 2^(1+floor(log2 n)); all pairs, n <= 10")
report("R2b", all(sharp[n] == admissible(n) for n in range(2, 11)), f"modulus 2^floor(log2 n) is insufficient exactly for the admissible sizes among 2..10: {[n for n in sharp if sharp[n]]}")
trail = lambda n: len(bin(n)) - len(bin(n).rstrip("1"))
expect = {n: (n.bit_length() - 1 if admissible(n) else 1 + trail(n)) for n in range(1, 11)}
report("R2d", vmax == expect, f"largest v(chi - lam^n) over the non-nilpotent pairs, all pairs, n <= 10: {vmax}; "
       "floor(log2 n) for the admissible sizes, 1 + (number of final binary ones) for the others")
ok = True
for n in [m for m in range(4, 200) if admissible(m)]:                              # sharpness construction for larger n
    digits = bin(n)[2:]
    start = ((-1, 1), (1,)) if digits.startswith("10") else ((0, 0, 0), (1, 1))
    d, b = start
    for dg in digits[2:]:
        d, b = fold_odd(d, b, 1) if dg == "1" else fold_even(d, b, 1)
    ok &= len(d) == n and all(v in POP for v in d) and content_val(charpoly(d, b), n) == n.bit_length() - 1
report("R2c", ok, "sharpness construction: one flipped product in the prefix of size 2 or 3 gives valuation floor(log2 n) exactly; admissible n < 200")
ok = okS
for _ in range(4000):                                                              # recognition on folds and perturbed folds
    n = random.choice([m for m in range(2, 300) if admissible(m)])
    d, b = (0,), ()
    for dg in bin(n)[3:]:
        s = random.choice((1, -1)); d, b = fold_odd(d, b, s) if dg == "1" else fold_even(d, b, s)
    ok &= recognise(d, b) is not None and len(recognise(d, b)) == n.bit_length() - 1
    d2, b2 = list(d), list(b)
    if random.random() < 0.5: i = random.randrange(n); d2[i] = random.choice([v for v in POP if v != d2[i]])
    else: i = random.randrange(n - 1); b2[i] = -b2[i]
    ok &= (recognise(d2, b2) is not None) == (not any(charpoly(d2, b2)[:n]))
report("R3", ok, "O(n) recognition agrees with the characteristic polynomial: all pairs n <= 8, 4000 folds and perturbed folds up to n = 300")

# R4 examples: a matrix violating the hypothesis of Takata et al., Remark 3.3, the size-5 matrix of Section 4.1
import sympy as sp
lam = sp.symbols('lam'); I = sp.I
v = sp.Matrix([1, I, 0]); e = sp.Matrix([0, 0, 1]); H = v * e.T + e * v.T
R = sp.Matrix(3, 3, lambda i, j: 1 if i + j == 2 else 0); A, B = 1, I
D = sp.zeros(6, 6); D[:3, :3] = H; D[3:, 3:] = R * H * R; D[2, 2] += A; D[3, 3] -= A; D[2, 3] = B; D[3, 2] = B
ok = H.T == H and H**2 != sp.zeros(3, 3) and H**3 == sp.zeros(3, 3) and D.T == D and sp.expand(D.charpoly(lam).as_expr()) == lam**6 and len(D.nullspace()) == 2
report("R4a", ok, "H = v e3^T + e3 v^T, v = (1, i, 0): one Jordan block of size 3; doubled matrix (A = 1, B = i) is nilpotent with a 2-dimensional kernel")
w = sp.Rational(-1, 2) + sp.sqrt(3) / 2 * I                       # exp(2 pi i/3)
M = sp.Matrix([[-1, w, 0, 0], [1, 1, -1, 0], [0, 1, -1, w**2], [0, 0, 1, 1]])
report("R4b", sp.expand(w**2 + w + 1) == 0 and sp.expand((lam * sp.eye(4) - M).det() - lam**4) == 0, "d = (-1,1,-1,1), b = (w, -1, w^2), w = exp(2 pi i/3): chi = lam^4")
b5 = [Fraction(-1), Fraction(2), Fraction(-1, 2), Fraction(-1, 2)]
report("R4c", charpoly([0] * 5, b5) == [0, 0, 0, 0, 0, 1], "zero diagonal, b = (-1, 2, -1/2, -1/2): chi = lam^5")

# R5 Remark 5.4: sigma with D_sigma = 1 +- 2x gives degree 2^(K-2) + 1 for s = (sigma, eps, eps, -rev sigma)
def D(s):
    a, bb = [1], [1]
    for sk in s:
        c = bb + [0] * (len(a) + 1 - len(bb))
        for j, vv in enumerate(a): c[j + 1] += sk * vv
        a, bb = bb, c
    while len(bb) > 1 and bb[-1] == 0: bb.pop()
    return bb
def FK(K):
    F = {()}
    for _ in range(K - 1): F = {s + (e2, -e2) + s[::-1] for s in F for e2 in (1, -1)}
    return F
neg = lambda t: tuple(-x for x in t)
ok = True
for K in (4, 5, 6):
    for tau in FK(K - 2):
        for e1 in (1, -1):
            sigma = tau + (e1, e1) + neg(tau[::-1])                      # D_sigma = 1 + 2 e1 x
            ok &= D(sigma) == [1, 2 * e1]
            for e2 in (1, -1): ok &= len(D(sigma + (e2, e2) + neg(sigma[::-1]))) - 1 == 2 ** (K - 2) + 1
report("R5", ok, "Remark 5.4: for D_sigma = 1 +- 2x the anti-fold has degree 2^(K-2) + 1 (5, 9, 17 for K = 4, 5, 6)")

# R6 Liu's matrices as printed in the sources (pairs: diagonal, products; subdiagonal 1)
g14 = (-1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 1, 1, -1)
liu6 = ((0, 0, -1, 1, 0, 0), (-1, 1, -1, 1, -1))                                  # Ferreira-Parlett (2009)
liu14 = ((0,) * 6 + (-1, 1) + (0,) * 6, g14)                                       # Ferreira-Parlett-Dopico (2012), Section 4.2
liu28 = ((0,) * 6 + (-1, 1) + (0,) * 5 + (-1, 1) + (0,) * 5 + (1, -1) + (0,) * 6, g14 + (-1,) + g14)   # Bini-Gemignani-Tisseur (2005), Section 5
nilp = lambda pr: not any(charpoly(*pr)[:len(pr[0])])
kinds = lambda pr: [k for k, _ in recognise(*pr)][::-1]                            # fold types, first fold first
ok = all(nilp(pr) for pr in (liu6, liu14, liu28)) and kinds(liu6) == ['odd', 'even'] \
     and kinds(liu14) == ['odd', 'odd', 'even'] and kinds(liu28) == ['odd', 'odd', 'even', 'even']
o = ((0,), ())
ok &= liu6 == fold_even(*fold_odd(*o, -1), 1) and liu14 == fold_even(*fold_odd(*fold_odd(*o, -1), 1), 1) and liu28 == fold_even(*liu14, 1)
report("R6a", ok, "Liu_6 = Psi_1 Phi_-1 (o), Liu_14 = Psi_1 Phi_1 Phi_-1 (o), Liu_28 = Psi_1 (Liu_14)")
# pencil data of Berhanu (2005, Section 7.6): J T has diagonal sigma_k a_k and products sigma_k sigma_(k+1) beta_k^2
s7a = (1, -1, -1, -1, 1, 1, -1); s7b = (1, -1, -1, 1, 1, 1, -1)
def pencil(sig, ones):
    a = [0] * len(sig)
    for k in ones: a[k - 1] = 1
    return tuple(s * x for s, x in zip(sig, a)), tuple(sig[k] * sig[k + 1] for k in range(len(sig) - 1))
ber14 = pencil(s7a + s7b, (7, 8)); ber28 = pencil((s7a + s7b) * 2, (7, 8, 14, 15, 21, 22))
c28 = charpoly(*ber28); c28[28] -= 1; c28[14] += 2
bgt14 = ((0,) * 6 + (-1, -1) + (0,) * 6, g14)
ok = ber14 == liu14 and ber28[1] == liu28[1] and not any(c28) and charpoly(*bgt14)[13] == 2 and not nilp(bgt14)
report("R6b", ok, "Berhanu's size-14 data give the same pair; two versions that are not nilpotent as extracted: "
       "Berhanu's size-28 diagonal (chi = lam^28 - 2 lam^14) and alpha_14 = (0^6, -1, -1, 0^6) in Bini et al. (trace -2)")
sig5 = (1, -1, -1, 1, -1); beta2 = (Fraction(1), Fraction(2), Fraction(1, 2), Fraction(1, 2))
report("R6c", [sig5[k] * sig5[k + 1] * beta2[k] for k in range(4)] == b5, "Berhanu's size-5 data give the products (-1, 2, -1/2, -1/2)")

# R7 the chains of Takata et al. (arXiv:2510.00623), Eqs. (8)-(13), as pairs (diagonal, products = squares of the couplings)
a, c, dd = sp.symbols('a c d')
def spoly(d, b): return [sp.expand(x) for x in charpoly(list(d), list(b))]
six = spoly((0, 0, dd, -dd, 0, 0), (a**2, -a**2, -dd**2, -a**2, a**2))             # a6^2 + b6^2 = 0, c6^2 + d6^2 = 0
seven = spoly((0,) * 7, (a**2, -a**2, c**2, -c**2, -a**2, a**2))                   # Eq. (11)
ok = six == [0] * 6 + [1] and seven == [0] * 7 + [1]
# (a6, b6, c6, d6) = (i gamma, -gamma, i gamma, gamma), divided by gamma
passive = ((0, 0, 1, -1, 0, 0), tuple(int(sp.expand(x**2)) for x in (sp.I, -1, sp.I, -1, sp.I)))
ok &= passive == (liu6[0][::-1], liu6[1][::-1]) and kinds(passive) == ['odd', 'even']
# seven-site design (a7, ..., f7) = (-1, i, -1, i, i, -1) (mu = gamma = 1): Proposition 4.1(i) applied to the
# three-site chain with couplings (-1, i), with B = -1, C = i; the mirrored couplings agree in sign
def sym_tridiag(c):
    n = len(c) + 1; M7 = sp.zeros(n, n)
    for k, v in enumerate(c): M7[k, k + 1] = v; M7[k + 1, k] = v
    return M7
H3 = sym_tridiag([-1, sp.I]); R3 = sp.Matrix(3, 3, lambda i, j: 1 if i + j == 2 else 0)
G = sp.zeros(7, 7); G[:3, :3] = H3; G[4:, 4:] = R3 * H3 * R3
G[2, 3] = G[3, 2] = -1; G[3, 4] = G[4, 3] = sp.I
H7 = sym_tridiag([-1, sp.I, -1, sp.I, sp.I, -1])
ok &= G == H7 and H7**6 != sp.zeros(7, 7) and H7**7 == sp.zeros(7, 7)
# a seven-site chain with a mirrored coupling of the opposite sign satisfies Eq. (11) and is conjugate to H7 by a sign matrix
H7m = sym_tridiag([-1, sp.I, -1, sp.I, sp.I, 1]); Dg = sp.diag(1, 1, 1, 1, 1, 1, -1)
ok &= H7m != H7 and Dg * H7m * Dg == H7 and H7m**7 == sp.zeros(7, 7)
report("R7", ok, "six-site and seven-site chains of Takata et al. are nilpotent under their conditions (10), (11); "
       "the passive six-site chain, divided by gamma, is Liu_6 with the sites in reverse order; "
       "the seven-site design is Proposition 4.1(i) applied to the three-site chain")

# R8 Corollary 1.2 (interval form), Corollary 1.4 (generating function), count of Section 6
def interval(n): return n == 1 or any(3 * 2**j - 1 <= n <= 2**(j + 2) - 1 for j in range(n.bit_length()))
ok = all(admissible(n) == interval(n) for n in range(1, 5000)) and all(len(family(n)) == (2**(n.bit_length() - 1) if admissible(n) else 0) for n in range(1, 130))
report("R8a", ok, "N_n is non-empty iff n = 1 or 3*2^j - 1 <= n <= 2^(j+2) - 1 (n < 5000); |N_n| = 2^floor(log2 n) (n < 130)")
x = sp.symbols('x')
U = sum(2**(n - 1 + n.bit_length() - 1) * x**n for n in range(1, 11) if admissible(n))
ser = sp.series(U / (1 - 5 * U), x, 0, 11).removeO()
vals = [ser.coeff(x, n) for n in range(1, 11)]
report("R8b", vals == [1, 9, 73, 585, 4809, 39113, 318921, 2599625, 21186505, 172688585], f"coefficients of U/(1 - 5U): {vals}")
def reference(n):                                        # integer fold with all signs +1
    d, b = (0,), ()
    for dg in bin(n)[3:]: d, b = fold_odd(d, b, 1) if dg == "1" else fold_even(d, b, 1)
    return d
def cmod2(h): return 2**(h - 1) * 2**sum(v % 2 for v in reference(h))      # pairs of C_h with chi = lam^h mod 2 (Lemma 2.3)
total = 1                                                                   # n = 1
for n in range(2, 28):
    h = n // 2
    if n % 2 or not bin(h)[2:].startswith("10"): total += 2 * cmod2(h)     # Theorem 1.5
report("R8c", total == 1386853, f"number of pairs with chi = lam^n mod 4, n <= 27, by Theorem 1.5: {total} (the candidate total of check_folds.py)")
print("all checks passed")
