#!/usr/bin/env python3
"""
check_proof.py -- numerical tests of the three lemmas of Section 2 (statement numbers of the sixth version).

Lemma 2.1  folding identities:  chi(odd fold) = lam chi^2,  chi(even fold) = chi^2,  and the increments of the resolvent entry.
Lemma 2.3  moments modulo 2:   for a symmetric tridiagonal matrix over F_2 with unit off-diagonal entries and ANY diagonal,
                              c_j = (M^(j-1))_11 satisfies c_(2i+1) = c_(2i) + c_i (1 <= i <= n-1) and
                              c_(2n+1) = c_(2n) + c_n + 1.  The diagonal is recovered from the moments.
Lemma 2.4  transversality:    for a tridiagonal pair (d, b) over a field, all b_k != 0, the polynomials
                              A_k = chi_<k chi_>k and B_k = chi_<k chi_>k+1 span the polynomials of degree < n;
                              for a mirror-symmetric pair the n orbit representatives are a basis.
"""
import random, time
T0 = time.time(); random.seed(20261120)
def report(tag, ok, text):
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}: {text}   ({time.time() - T0:.0f} s)", flush=True); assert ok

# ---------- integer side ----------
def charpoly(d, b):
    p0, p1 = [1], [-d[0], 1]
    for k in range(1, len(d)):
        q = [0] + p1
        for i, v in enumerate(p1): q[i] -= d[k] * v
        for i, v in enumerate(p0): q[i] -= b[k - 1] * v
        p0, p1 = p1, q
    return p1
def fold_odd(d, b, eps): return (d + (0,) + d[::-1], b + (eps, -eps) + b[::-1])
def fold_even(d, b, dl): return (d[:-1] + (d[-1] - dl, d[-1] + dl) + d[:-1][::-1], b + (-1,) + b[::-1])
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def moments(d, b, J):
    n = len(d); v = [0] * n; v[0] = 1; out = []
    for _ in range(J):
        out.append(v[0]); w = [0] * n
        for i in range(n):
            w[i] += d[i] * v[i]
            if i + 1 < n: w[i] += b[i] * v[i + 1]
            if i > 0: w[i] += v[i - 1]
        v = w
    return out
def prod(t):
    r = 1
    for v in t: r *= v
    return r

ok = True
for _ in range(2000):
    n = random.randint(1, 12)
    d = tuple(random.randint(-3, 3) for _ in range(n)); b = tuple(random.choice((1, -1)) for _ in range(n - 1))
    c = charpoly(d, b); c2 = pmul(c, c)
    for e in (1, -1):
        ok &= charpoly(*fold_odd(d, b, e)) == [0] + c2 and charpoly(*fold_even(d, b, e)) == c2
report("P1", ok, "Lemma 2.1: chi(odd fold) = lam chi^2, chi(even fold) = chi^2 (2000 random integer pairs)")

# resolvent increments along iterated integer folds: new moment = eps*prod(b) at lam^-(2n+1), -delta*prod(b) at lam^-(2n)
ok = True
for trial in range(300):
    d, b = (0,), ()
    while len(d) < 60:
        n = len(d); mu = moments(d, b, 2 * n + 2); s = random.choice((1, -1))
        if random.random() < 0.5:
            d2, b2 = fold_odd(d, b, s); new_index, new_val = 2 * n, s * prod(b)
        else:
            d2, b2 = fold_even(d, b, s); new_index, new_val = 2 * n - 1, -s * prod(b)
        mu2 = moments(d2, b2, 2 * n + 2)
        ok &= all(mu2[j] == (mu[j] if j < n else 0) + (new_val if j == new_index else 0) for j in range(2 * n + 2))
        d, b = d2, b2
report("P2", ok, "Proposition 3.2, proof: resolvent entry gains eps*prod(b)*lam^-(2n+1) (odd step), -delta*prod(b)*lam^-(2n) (even step); 300 random fold chains")

# ---------- Lemma 2.3 over F_2, in the form of moments ----------
def moments2(dbar, J):
    n = len(dbar); v = [0] * n; v[0] = 1; out = [None]          # out[j] = c_j, j >= 1
    for _ in range(J):
        out.append(v[0]); w = [0] * n
        for i in range(n):
            w[i] ^= dbar[i] & v[i]
            if i + 1 < n: w[i] ^= v[i + 1]
            if i > 0: w[i] ^= v[i - 1]
        v = w
    return out
ok = True
for _ in range(400):
    n = random.randint(2, 60); dbar = [random.randint(0, 1) for _ in range(n)]
    c = moments2(dbar, 2 * n + 1)
    ok &= all(c[2 * i + 1] == c[2 * i] ^ c[i] for i in range(1, n)) and c[2 * n + 1] == c[2 * n] ^ c[n] ^ 1
report("P3", ok, "Lemma 2.3 (moments): c_(2i+1) = c_(2i) + c_i for i < n and c_(2n+1) = c_(2n) + c_n + 1; 400 random diagonals, n <= 60")

def reconstruct(c, n):
    """diagonal from the moments c_1..c_2n over F_2:  d_(k+1) = L(lam p_k^2),  L(lam^j) = c_(j+1);  p_k^2 = p_k(lam^2)"""
    d = []; p_prev, p_cur = 0, 1                                  # bitmask polynomials p_(k-1), p_k
    for k in range(n):
        dk = 0; j = 0; q = p_cur
        while q:
            if q & 1: dk ^= c[2 * j + 2]
            q >>= 1; j += 1
        d.append(dk)
        p_prev, p_cur = p_cur, (p_cur << 1) ^ (p_cur if dk else 0) ^ p_prev
    return d, p_cur
ok = True
for _ in range(300):
    n = random.randint(1, 60); dbar = [random.randint(0, 1) for _ in range(n)]
    ok &= reconstruct(moments2(dbar, 2 * n), n)[0] == dbar
report("P4", ok, "Lemma 2.3 (moments): the diagonal is recovered from the moments by d_(k+1) = L(lam p_k^2); 300 random diagonals")

def support(n):
    if n == 1: return [0]
    s = support(n // 2)
    if n % 2: return s + [0] + s[::-1]
    t = s[:-1] + [s[-1] ^ 1]
    return t + t[::-1]
def prefixes(n):
    out = set()
    while n: out.add(n); n //= 2
    return out
ok = True
for n in range(1, 513):
    P = prefixes(n); c = [None] + [1 if j in P else 0 for j in range(1, 2 * n + 1)]
    d, chi = reconstruct(c, n)
    ok &= d == support(n) and chi == 1 << n and d == d[::-1]
report("P5", ok, "Lemma 2.3 (moments): the prefix sequence c_j = [j binary prefix of n] gives the fold support, nilpotent and mirror symmetric, n <= 512")

# ---------- Lemma 2.4 over F_p ----------
def padd(a, b, p):
    r = [0] * max(len(a), len(b))
    for i, v in enumerate(a): r[i] = v
    for i, v in enumerate(b): r[i] = (r[i] + v) % p
    return r
def pmulp(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] = (r[i + j] + x * y) % p
    return r
def seg_polys(d, b, p):
    """lead[k] = char poly of vertices 1..k, trail[k] = char poly of the last k vertices (coefficients mod p, low degree first)"""
    n = len(d)
    def run(dd, bb):
        out = [[1]]; prev = [0]
        for k in range(n):
            cur = out[-1]
            q = padd(pmulp([(-dd[k]) % p, 1], cur, p), [(-(bb[k - 1] if k else 0) * v) % p for v in prev], p)
            prev = cur; out.append(q)
        return out
    return run(d, b), run(d[::-1], b[::-1])
def rank_mod(vecs, p):
    rows = [v[:] for v in vecs]; rk = 0; ncol = max(len(v) for v in rows)
    rows = [v + [0] * (ncol - len(v)) for v in rows]
    for col in range(ncol):
        piv = next((r for r in range(rk, len(rows)) if rows[r][col] % p), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p); rows[rk] = [(v * inv) % p for v in rows[rk]]
        for r in range(len(rows)):
            if r != rk and rows[r][col] % p:
                f = rows[r][col]; rows[r] = [(x - f * y) % p for x, y in zip(rows[r], rows[rk])]
        rk += 1
    return rk
ok_span = ok_basis = True
for p in (2, 3, 5, 7, 101):
    for _ in range(40):
        n = random.randint(2, 30)
        d = [random.randrange(p) for _ in range(n)]; b = [random.randrange(1, p) for _ in range(n - 1)]
        lead, trail = seg_polys(d, b, p)
        A = [pmulp(lead[k - 1], trail[n - k], p) for k in range(1, n + 1)]
        B = [pmulp(lead[k - 1], trail[n - k - 1], p) for k in range(1, n)]
        ok_span &= rank_mod(A + B, p) == n
        # mirror-symmetric pair
        h = [random.randrange(p) for _ in range((n + 1) // 2)]; d = h + h[:n // 2][::-1]
        hb = [random.randrange(1, p) for _ in range(n // 2)]; b = hb + hb[:(n - 1) // 2][::-1]
        assert d == d[::-1] and b == b[::-1] and len(d) == n and len(b) == n - 1
        lead, trail = seg_polys(d, b, p)
        A = [pmulp(lead[k - 1], trail[n - k], p) for k in range(1, n + 1)]
        B = [pmulp(lead[k - 1], trail[n - k - 1], p) for k in range(1, n)]
        ok_basis &= all(A[k] == A[n - 1 - k] for k in range(n)) and all(B[k] == B[n - 2 - k] for k in range(n - 1))
        reps = A[:(n + 1) // 2] + B[:n // 2]
        ok_basis &= len(reps) == n and rank_mod(reps, p) == n
report("P6", ok_span, "Lemma 2.4(i): A_k, B_k span the polynomials of degree < n; 200 random pairs over F_2, F_3, F_5, F_7, F_101, n <= 30")
report("P7", ok_basis, "Lemma 2.4(ii): for mirror-symmetric pairs the n orbit representatives are a basis; 200 random pairs, same fields")
# ---------- consequences: Section 3.1 and Corollary 1.2 ----------
def family(n, pop=None, signs=(1, -1)):
    if n == 1: return {((0,), ())}
    out = set()
    for (d, b) in family(n // 2, pop, signs):
        for e in signs:
            nd, nb = fold_odd(d, b, e) if n % 2 else fold_even(d, b, e)
            if pop is None or all(v in pop for v in nd): out.add((nd, nb))
    return out
ok = True
for n in range(2, 65):
    (r, s), = family(n, None, (1,))                      # reference fold, all signs +1
    for (d, b) in family(n, (0, 1, -1)):
        for k in range(1, n + 1):                         # relation 1
            kk = n + 1 - k
            if k < kk: ok &= (d[k - 1] + d[kk - 1] - r[k - 1] - r[kk - 1]) % 4 == 0
            if k == kk: ok &= (d[k - 1] - r[k - 1]) % 4 == 0
        for k in range(1, n):                             # relation 2
            kk = n - k
            if k < kk: ok &= b[k - 1] * b[kk - 1] == s[k - 1] * s[kk - 1]
            if k == kk: ok &= b[k - 1] == s[k - 1]
        ok &= all((x - y) % 2 == 0 for x, y in zip(d, r))
report("P8", ok, "Section 3.1: every nilpotent pair in the class satisfies relations 1 and 2 against the reference fold, n <= 64")
ok = True
for n in range(1, 130):
    for (d, b) in family(n):
        if n >= 3: ok &= d[0] == d[-1]
        if n == 2: ok &= abs(d[0]) == 1 and abs(d[1]) == 1
    cnt = len(family(n, (0, 1, -1)))
    bits = bin(n)[2:]
    admissible = n == 1 or bits.startswith("11") or (bits.startswith("10") and set(bits[2:]) <= {"1"})
    ok &= cnt == (2 ** (len(bits) - 1) if admissible else 0)
report("P9", ok, "Corollary 1.2: first entry = last entry for folds of size >= 3; sizes 1, 11..., 101...1 in binary; 2^floor(log2 n) pairs; n < 130")
print("all checks passed")
