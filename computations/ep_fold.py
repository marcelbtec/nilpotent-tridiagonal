# The two folding steps for ARBITRARY square matrices H (exact arithmetic, sympy):
#   even step  H -> [[H + A e_N e_N^T, B e_N e_1^T], [C e_1 e_N^T, R H^T... ]]   (Takata et al. use H symmetric, R H R)
#   odd  step  H -> [[H, b1 e_N, 0], [c1 e_N^T, 0, c2 e_1^T], [0, b2 e_1, R H R]]  with b1 c1 + b2 c2 = 0
# Claim: char poly = chi_H^2 (even, A^2 + BC = 0) and lambda chi_H^2 (odd).  Jordan structure checked separately.
import random, sympy as sp
random.seed(11); lam = sp.symbols('lam')
def flip(H):
    n = H.shape[0]; R = sp.Matrix(n, n, lambda i, j: 1 if i + j == n - 1 else 0); return R * H * R
def odd_fold(H, b1, c1, b2, c2, mirror):
    n = H.shape[0]; M = sp.zeros(2 * n + 1, 2 * n + 1)
    M[:n, :n] = H; M[n + 1:, n + 1:] = mirror
    M[n - 1, n] = b1; M[n, n - 1] = c1; M[n, n + 1] = b2; M[n + 1, n] = c2
    return M
def even_fold(H, A, B, C, mirror):
    n = H.shape[0]; M = sp.zeros(2 * n, 2 * n)
    M[:n, :n] = H; M[n:, n:] = mirror
    M[n - 1, n - 1] += A; M[n, n] -= A; M[n - 1, n] = B; M[n, n - 1] = C
    return M
def nil_index(M):
    P = sp.eye(M.shape[0]); k = 0
    while P != sp.zeros(*M.shape): P = P * M; k += 1
    return k
okc = True; full_sym = full_gen = tot = 0
for trial in range(40):
    n = random.randint(2, 5)
    H = sp.Matrix(n, n, lambda i, j: random.randint(-2, 2))                # arbitrary integer matrix
    chi = H.charpoly(lam).as_expr()
    b1, c1, b2 = (random.choice([-3, -2, -1, 1, 2, 3]) for _ in range(3)); c2 = sp.Rational(-b1 * c1, b2)
    okc &= sp.expand(odd_fold(H, b1, c1, b2, c2, flip(H)).charpoly(lam).as_expr() - lam * chi**2) == 0
    A = random.choice([-2, -1, 1, 2]); B = random.choice([-2, -1, 1, 2]); C = sp.Rational(-A * A, B)
    okc &= sp.expand(even_fold(H, A, B, C, flip(H)).charpoly(lam).as_expr() - chi**2) == 0
print("char poly identities (odd: lam*chi^2, even: chi^2) for 40 random integer matrices H, mirror block R H R:", okc)
# Jordan structure: start from a nilpotent H with one Jordan block and test the index of the folds
for trial in range(60):
    n = random.randint(2, 4)
    J = sp.Matrix(n, n, lambda i, j: 1 if j == i + 1 else 0)
    while True:
        P = sp.Matrix(n, n, lambda i, j: random.randint(-2, 2))
        if P.det() != 0: break
    Hg = P * J * P.inv()                                                    # generic nilpotent, single block
    tot += 1
    full_gen += nil_index(odd_fold(Hg, 1, 1, 1, -1, flip(Hg))) == 2 * n + 1
    # complex symmetric nilpotent with one block: use a tridiagonal symmetric chain (entries 1, i) of size 3
print(f"odd fold of a generic one-block nilpotent H (non-symmetric): full index 2n+1 in {full_gen} of {tot} cases")
# chains: unreduced tridiagonal folds are always one block; example orders 1 -> 3 -> 6 -> 13 with free magnitudes
a, b, c = sp.symbols('a b c', nonzero=True)
H1 = sp.Matrix([[0]])
H3 = odd_fold(H1, a, a, sp.I * a, sp.I * a, flip(H1))                       # symmetric chain (0 a; a 0 ia; ia 0)
H6 = even_fold(H3, b, sp.I * b, sp.I * b, flip(H3))
H13 = odd_fold(H6, c, c, sp.I * c, sp.I * c, flip(H6))
for name, H in (("H3", H3), ("H6", H6), ("H13", H13)):
    n = H.shape[0]
    print(name, "symmetric:", H == H.T, " H^n = 0:", sp.simplify(H**n) == sp.zeros(n, n), " H^(n-1) != 0:", sp.simplify(H**(n - 1)) != sp.zeros(n, n))
