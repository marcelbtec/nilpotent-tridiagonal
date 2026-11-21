#!/usr/bin/env python3
"""
check_newproofs.py -- tests of the steps of the proofs in Sections 2 and 3 of the sixth version of the manuscript,
which are also the steps of the Lean formalisation (see ../proof.md).

N1  the identity (12) over F_2:  r_k^2 + lam r_k r_(k+1) + r_(k+1)^2 + 1 = (1 + lam) g_k^2,  g_k = sum_(j >= k) d_j r_(j+1)
N2  Lemma 2.3: exactly one nilpotent diagonal modulo 2 for each n (exhaustive, n <= 16), the recursion (11),
    and the relations (13) for the coefficients of r_2
N3  Lemma 2.4(i): the induction "f r_(k+1) lies in the span W for deg f < k", over several fields
N4  Theorem 1.5, proof: for every pair P in C_n with chi_P = lam^n mod 4 (all pairs, n <= 9), the fold Q of the
    left half satisfies chi_Q = lam^n mod 4 and Q = P mod 2, the linearisation holds modulo 4, and P = Q mod 4
N5  the descent: for monic q of degree h with q = lam^h mod 2, v(lam^e q^2 - lam^(e + 2h)) = v(q - lam^h) + 1

Python 3, standard library only.  Run time: about 20 s.
"""
import itertools, random, time

random.seed(20261121)
T0 = time.time()
ALL = True


def report(tag, cond, text):
    global ALL
    ALL &= bool(cond)
    print(f"[{'PASS' if cond else 'FAIL'}] {tag}: {text}   ({time.time() - T0:.0f} s)", flush=True)


# ---------------------------------------------------------------- polynomials over F_2 as integers (bit i = lam^i)
def mul2(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def r_list2(d):
    """[r_1, ..., r_(n+2)] for the pair (d, 1) over F_2; r_(n+1) = 1, r_(n+2) = 0."""
    n = len(d)
    r = [0] * (n + 3)
    r[n + 1] = 1
    for k in range(n, 0, -1):
        r[k] = mul2(2 | d[k - 1], r[k + 1]) ^ r[k + 2]
    return r[1:]


# N1
ok = True
for _ in range(2000):
    n = random.randint(1, 48)
    d = [random.randint(0, 1) for _ in range(n)]
    r = [None] + r_list2(d)                       # r[k] = r_k
    for k in range(1, n + 2):
        g = 0
        for j in range(k, n + 1):
            if d[j - 1]:
                g ^= r[j + 1]
        lhs = mul2(r[k], r[k]) ^ mul2(2, mul2(r[k], r[k + 1])) ^ mul2(r[k + 1], r[k + 1]) ^ 1
        ok &= lhs == mul2(3, mul2(g, g))
report("N1", ok, "identity (12) for all k; 2000 random diagonals over F_2, n <= 48")


# N2
def nu(n):
    """the diagonal of (11)"""
    if n == 1:
        return [0]
    e = nu(n // 2)
    if n % 2:
        return e + [0] + e[::-1]
    return e[:-1] + [e[-1] ^ 1, e[-1] ^ 1] + e[:-1][::-1]


ok = True
for n in range(1, 17):
    sols = [d for d in itertools.product((0, 1), repeat=n) if r_list2(d)[0] == 1 << n]
    ok &= sols == [tuple(nu(n))]
report("N2a", ok, "Lemma 2.3: exactly one nilpotent diagonal modulo 2, given by (11); all diagonals, n <= 16")
ok = True
for n in range(1, 400):
    d = nu(n)
    r = r_list2(d)
    ok &= r[0] == 1 << n and d == d[::-1]
    c = lambda j: (r[1] >> (n - j)) & 1 if 1 <= j <= n else 0
    ok &= c(n) == 1 and all(c(i) == c(2 * i) ^ c(2 * i + 1) for i in range(1, n))
    ok &= (d[0] == 1) == bin(n)[2:].startswith("10")
report("N2b", ok, "nu_n is nilpotent and a palindrome; relations (13); first entry 1 iff n begins with 10 in binary; n < 400")


# ---------------------------------------------------------------- polynomials over F_p as coefficient lists
def padd(a, b, P):
    m = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % P for i in range(m)]


def pmul(a, b, P):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % P
    return r


def rank(rows, P):
    rows = [r[:] for r in rows]
    ncol = max(len(r) for r in rows)
    for r in rows:
        r += [0] * (ncol - len(r))
    rk = 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % P), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], P - 2, P)
        rows[rk] = [(x * inv) % P for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % P:
                f = rows[i][c]
                rows[i] = [(x - f * y) % P for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def seg_fn(d, b, P):
    def seg(i, j):                                # chi[i, j], positions counted from 1
        if j == i - 1:
            return [1]
        p0, p1 = [1], [(-d[i - 1]) % P, 1]
        for k in range(i, j):
            new = padd(pmul([(-d[k]) % P, 1], p1, P), [(-b[k - 1] * x) % P for x in p0], P)
            p0, p1 = p1, new
        return p1
    return seg


# N3
ok = True
for _ in range(300):
    P = random.choice([2, 3, 5, 7, 101])
    n = random.randint(1, 14)
    d = [random.randrange(P) for _ in range(n)]
    b = [random.randrange(1, P) for _ in range(n - 1)]
    seg = seg_fn(d, b, P)
    A = [pmul(seg(1, k - 1), seg(k + 1, n), P) for k in range(1, n + 1)]
    B = [pmul(seg(1, k - 1), seg(k + 2, n), P) for k in range(1, n)]
    W = A + B
    r0 = rank(W, P)
    ok &= r0 == n
    for k in range(1, n + 1):                     # lam^i r_(k+1), i < k, lies in W
        gens = [pmul([0] * i + [1], seg(k + 1, n), P) for i in range(k)]
        ok &= rank(W + gens, P) == r0
report("N3", ok, "Lemma 2.4(i): W has dimension n and contains f r_(k+1) for deg f < k, 1 <= k <= n; 300 random pairs")


# ---------------------------------------------------------------- integer pairs
def chi(d, b):
    """coefficients (low degree first) of the characteristic polynomial of the integer pair (d, b)"""
    p0, p1 = [1], [-d[0], 1]
    for k in range(1, len(d)):
        new = [0] * (len(p1) + 1)
        for t, a in enumerate(p1):
            new[t + 1] += a
            new[t] -= d[k] * a
        for t, a in enumerate(p0):
            new[t] -= b[k - 1] * a
        p0, p1 = p1, new
    return p1


def chi_seg(d, b, i, j):
    """chi[i, j] for positions counted from 1; chi[i, i - 1] = 1"""
    if j == i - 1:
        return [1]
    return chi(d[i - 1:j], b[i - 1:j - 1])


def imul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def is_lam_n_mod(p, n, m):
    return all((c - (1 if t == n else 0)) % m == 0 for t, c in enumerate(p))


# N4
ok = True
count = 0
for n in range(2, 10):
    h = n // 2
    for d in itertools.product((-1, 0, 1), repeat=n):
        if sum(x % 2 for x in d) % 2 != sum(nu(n)) % 2:      # cheap filter: the trace of chi modulo 2
            continue
        for b in itertools.product((1, -1), repeat=n - 1):
            P_ = chi(d, b)
            if not is_lam_n_mod(P_, n, 4):
                continue
            count += 1
            if n % 2:                                       # Q = Phi_eps(left half), eps = b_h
                dq = d[:h] + (0,) + d[:h][::-1]
                bq = b[:h] + (-b[h - 1],) + b[:h - 1][::-1]
            else:                                           # Q = Psi_1(left half with last entry raised by 1)
                dq = d[:h] + (d[h - 1] + 2,) + d[:h - 1][::-1]
                bq = b[:h - 1] + (-1,) + b[:h - 1][::-1]
            Q_ = chi(dq, bq)
            ok &= is_lam_n_mod(Q_, n, 4)
            ok &= all((x - y) % 2 == 0 for x, y in zip(d, dq)) and all((x - y) % 2 == 0 for x, y in zip(b, bq))
            # linearisation at Q modulo 4
            lin = Q_[:]
            for k in range(1, n + 1):
                if d[k - 1] != dq[k - 1]:
                    Ak = imul(chi_seg(dq, bq, 1, k - 1), chi_seg(dq, bq, k + 1, n))
                    for t, a in enumerate(Ak):
                        lin[t] -= (d[k - 1] - dq[k - 1]) * a
            for k in range(1, n):
                if b[k - 1] != bq[k - 1]:
                    Bk = imul(chi_seg(dq, bq, 1, k - 1), chi_seg(dq, bq, k + 2, n))
                    for t, a in enumerate(Bk):
                        lin[t] -= (b[k - 1] - bq[k - 1]) * a
            ok &= all((x - y) % 4 == 0 for x, y in zip(P_, lin))
            # conclusion: P = Q modulo 4, hence the shape of a fold
            ok &= all((x - y) % 4 == 0 for x, y in zip(d, dq)) and all((x - y) % 4 == 0 for x, y in zip(b, bq))
            if n % 2:
                ok &= d == dq and b == bq
            else:
                ok &= d[h] == -d[h - 1] != 0 and b[h - 1] == -1
report("N4", ok and count > 0,
       f"Theorem 1.5, proof: fold Q of the left half, linearisation modulo 4, P = Q modulo 4; all {count} pairs with "
       f"chi = lam^n mod 4, n <= 9")


# N5
def val(p):
    v = 0
    if not any(p):
        return None
    while all(c % 2 == 0 for c in p):
        p = [c // 2 for c in p]
        v += 1
    return v


ok = True
for _ in range(3000):
    h = random.randint(1, 8)
    k = random.randint(1, 6)
    e = random.randint(0, 2)
    g = [random.randint(-3, 3) for _ in range(h)]
    if all(c % 2 == 0 for c in g):
        g[random.randrange(h)] += 1                         # v(q - lam^h) = k exactly
    q = [2 ** k * c for c in g] + [1]
    lhs = [0] * e + imul(q, q)
    lhs[e + 2 * h] -= 1
    ok &= val(lhs) == k + 1
report("N5", ok, "descent: v(lam^e q^2 - lam^(e+2h)) = v(q - lam^h) + 1 for monic q = lam^h mod 2; 3000 random q")

print("all checks passed" if ALL else "SOME CHECKS FAILED")
raise SystemExit(0 if ALL else 1)
