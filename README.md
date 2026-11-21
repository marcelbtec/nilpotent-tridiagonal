# Nilpotent tridiagonal matrices with entries in {−1, 0, 1}: proof, Lean formalisation and computations

This repository accompanies the paper *Nilpotent tridiagonal matrices with entries in {−1, 0, 1}* by M. Blattner (2026). It contains the proof of the classification, a formalisation in Lean 4 with Mathlib, and the programs that check the remaining statements of the paper by exact computation. The paper continues *Nilpotent skew-symmetric tridiagonal Bohemian matrices: a proof of Corless's conjecture*, [arXiv:2611.25266](https://arxiv.org/abs/2611.25266), whose formalisation is at [marcelbtec/corless-nilpotent](https://github.com/marcelbtec/corless-nilpotent).

**Setting.** An n × n tridiagonal matrix M has diagonal entries d₁, …, dₙ and off-diagonal entries aₖ (above the diagonal) and cₖ (below). Its characteristic polynomial depends on the off-diagonal entries only through the products bₖ = aₖcₖ. Let 𝒩ₙ be the set of the pairs (d, b) ∈ {−1, 0, 1}ⁿ × {1, −1}ⁿ⁻¹ whose matrices are nilpotent. For a pair p = (d, b) of size h and signs ε, δ = ±1, the *odd fold* and the *even fold* of p are the pairs of sizes 2h + 1 and 2h

    Φ_ε(p) = ((d, 0, rev d), (b, ε, −ε, rev b)),
    Ψ_δ(p) = ((d₁, …, d_{h−1}, d_h − δ, d_h + δ, d_{h−1}, …, d₁), (b, −1, rev b)).

**Theorem (classification).** 𝒩₁ = {((0), ())}, and for every h ≥ 1

- 𝒩_{2h+1} consists of the odd folds Φ_ε(p) with p ∈ 𝒩_h and ε = ±1;
- 𝒩_{2h} consists of the even folds Ψ_δ(p) with p ∈ 𝒩_h, last diagonal entry of p equal to 0, and δ = ±1.

Each element arises from exactly one p and one sign.

**Corollary (sizes and count).** 𝒩ₙ is non-empty if and only if n = 1 or 3·2^j − 1 ≤ n ≤ 2^{j+2} − 1 for some j ≥ 0, that is, for n = 1, 2, 3, 5, 6, 7, 11, …, 15, 23, …, 31, …. In that case it has 2^{⌊log₂ n⌋} elements.

**Theorem (rigidity modulo 4).** A pair P in {−1, 0, 1}ⁿ × {1, −1}ⁿ⁻¹ with n ≥ 2 has characteristic polynomial congruent to λⁿ modulo 4 if and only if it is a fold of a pair p of size h = ⌊n/2⌋ in the same class whose characteristic polynomial is congruent to λ^h modulo 2. Each fold accounts for exactly one power of two. Consequently P is nilpotent as soon as its characteristic polynomial is congruent to λⁿ modulo 2^{⌊log₂ n⌋ + 1}.

The proof studies the equation χ_P = λⁿ modulo 2 and then modulo 4. Modulo 2 the diagonal is determined uniquely, so P agrees modulo 2 with the fold Q of its own left half. Modulo 4 the difference of the characteristic polynomials of P and Q is linear in P − Q, and a linear independence statement forces P ≡ Q modulo 4, hence P = Q. `proof.md` has the full argument.

These statements are formalised. The paper contains further results: the number of all nilpotent tridiagonal matrices with entries in {−1, 0, 1} (1, 9, 73, 585, 4809, 39113, …), the sharpness of the modulus above, the (1,1) entry of the resolvent, the relation to the test matrices of Liu and to a design of exceptional points, and the multiplicity of the eigenvalue 0 in Corless's skew-symmetric family. These are not formalised; the programs in `computations/` check them by exact computation.

## Contents

| Path | Content |
|---|---|
| `proof.md` | the informal proof that the formalisation follows, with a table of the corresponding formal statements |
| `lean/` | the Lean 4 formalisation; `lean/README.md` lists the statements and files |
| `computations/` | Python and C programs that check every statement of the paper by exact computation, with their recorded outputs; `computations/README.md` describes each program |
| `.github/workflows/check.yml` | continuous integration: builds the Lean proof, checks its axioms, and reruns the computations |

## Main formal statements

```lean
inductive Folded : List ℤ → List ℤ → Prop
  | base : Folded [0] []
  | odd {d b : List ℤ} {ε : ℤ} (hp : Folded d b) (hε : ε = 1 ∨ ε = -1) :
      Folded (d ++ 0 :: d.reverse) (b ++ ε :: -ε :: b.reverse)
  | even {d b : List ℤ} {δ : ℤ} (hp : Folded (d ++ [0]) b) (hδ : δ = 1 ∨ δ = -1) :
      Folded (d ++ -δ :: δ :: d.reverse) (b ++ -1 :: b.reverse)

theorem Tridiagonal.isNilpotent_iff_folded (d a c : List ℤ) (ha : a.length + 1 = d.length)
    (hc : c.length + 1 = d.length) (hd : ∀ x ∈ d, x = -1 ∨ x = 0 ∨ x = 1)
    (ha1 : ∀ x ∈ a, x = 1 ∨ x = -1) (hc1 : ∀ x ∈ c, x = 1 ∨ x = -1) :
    IsNilpotent (Tri d.length (seqOf d) (seqOf a) (seqOf c))
      ↔ Folded d (List.zipWith (· * ·) a c)

theorem Tridiagonal.nilPairs_nonempty_iff (n : ℕ) :
    (NilPairs n).Nonempty ↔ n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j - 1 ≤ n ∧ n ≤ 2 ^ (j + 2) - 1

theorem Tridiagonal.nilPairs_ncard {n : ℕ} (hn : (NilPairs n).Nonempty) :
    (NilPairs n).ncard = 2 ^ Nat.log 2 n

theorem Tridiagonal.nil_of_congr (n : ℕ) : ∀ {d b : ℕ → ℤ}, 1 ≤ n → InC d b n →
    (2 : ℤ[X]) ^ (Nat.log 2 n + 1) ∣ K d b n - X ^ n → K d b n = X ^ n
```

`Tri` is the tridiagonal matrix with the given diagonal, superdiagonal and subdiagonal, and `Folded d b` says that the pair `(d, b)` is obtained from `((0), ())` by folds. `NilPairs n` is the set 𝒩ₙ, and `K d b n` is the characteristic polynomial of a pair. `lean/README.md` explains the statements, including the rigidity modulo 4. All main theorems depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Checking

**Lean.** You need [elan](https://github.com/leanprover/elan). The toolchain is `leanprover/lean4:v4.36.0` and Mathlib is `v4.36.0`.

```
cd lean
lake exe cache get          # downloads the compiled Mathlib, about 5 GB
lake build
lake env lean Axioms.lean   # prints the axioms of the main theorems
```

**Computations.** You need Python 3 with numpy and sympy, and a C compiler with OpenMP.

```
computations/run_all.sh     # about 3 minutes on 14 cores
```

## License

The code in `lean/` and `computations/` is licensed under the Apache License 2.0 (`LICENSE`), the license of Mathlib. The text of `proof.md` and the data and output files in `computations/` are licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Citation

See `CITATION.cff`.
