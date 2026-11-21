# Lean formalisation: nilpotent tridiagonal matrices with entries in {−1, 0, 1}

This is a machine-checked proof, in Lean 4 with Mathlib, of the classification of the nilpotent tridiagonal matrices with diagonal entries in {−1, 0, 1} and off-diagonal entries in {1, −1}, of the rigidity modulo 4 on which it rests, and of the admissible sizes with the count. The informal proof is in `../proof.md`.

All names are in the namespace `Tridiagonal`. Positions are counted from 0.

## Main statements

```lean
-- NilpotentTridiagonal/Matrix.lean
def Tri (n : ℕ) (d a c : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  fun i j =>
    if (i : ℕ) = j then d i
    else if (j : ℕ) = i + 1 then a i
    else if (i : ℕ) = j + 1 then c j
    else 0

-- NilpotentTridiagonal/Folded.lean
inductive Folded : List ℤ → List ℤ → Prop
  | base : Folded [0] []
  | odd {d b : List ℤ} {ε : ℤ} (hp : Folded d b) (hε : ε = 1 ∨ ε = -1) :
      Folded (d ++ 0 :: d.reverse) (b ++ ε :: -ε :: b.reverse)
  | even {d b : List ℤ} {δ : ℤ} (hp : Folded (d ++ [0]) b) (hδ : δ = 1 ∨ δ = -1) :
      Folded (d ++ -δ :: δ :: d.reverse) (b ++ -1 :: b.reverse)

-- NilpotentTridiagonal/Main.lean
theorem isNilpotent_iff_folded (d a c : List ℤ) (ha : a.length + 1 = d.length)
    (hc : c.length + 1 = d.length) (hd : ∀ x ∈ d, x = -1 ∨ x = 0 ∨ x = 1)
    (ha1 : ∀ x ∈ a, x = 1 ∨ x = -1) (hc1 : ∀ x ∈ c, x = 1 ∨ x = -1) :
    IsNilpotent (Tri d.length (seqOf d) (seqOf a) (seqOf c))
      ↔ Folded d (List.zipWith (· * ·) a c)

theorem nilPairs_nonempty_iff (n : ℕ) :
    (NilPairs n).Nonempty ↔ n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j - 1 ≤ n ∧ n ≤ 2 ^ (j + 2) - 1

theorem nilPairs_ncard {n : ℕ} (hn : (NilPairs n).Nonempty) :
    (NilPairs n).ncard = 2 ^ Nat.log 2 n
```

- **`Tri n d a c`** is the `n × n` tridiagonal matrix with `d i` at position `(i, i)`, `a i` at `(i, i + 1)` and `c i` at `(i + 1, i)`. `seqOf l` extends a list `l` by zeros to a sequence `ℕ → ℤ`, so `Tri d.length (seqOf d) (seqOf a) (seqOf c)` is the matrix (1) of the paper with diagonal `d`, superdiagonal `a` and subdiagonal `c`.
- **`Folded d b`** says that the pair `(d, b)` is obtained from `((0), ())` by odd folds `(d, b) ↦ ((d, 0, rev d), (b, ε, −ε, rev b))` and by even folds `((d, 0), b) ↦ ((d, −δ, δ, rev d), (b, −1, rev b))`. These are the folds Φ_ε and Ψ_δ of the paper; the even fold is applied only to pairs whose last diagonal entry is 0.
- **`isNilpotent_iff_folded`** is Theorem 1.1 for matrices: the matrix is nilpotent if and only if the pair formed by its diagonal and by the products of its opposite off-diagonal entries is folded.
- **`NilPairs n`** is the set 𝒩ₙ: the pairs of lists `(d, b)` with `d` of length `n`, `b` of length `n − 1`, entries of `d` in {−1, 0, 1}, entries of `b` in {1, −1}, and characteristic polynomial `X ^ n`. The two theorems on it are Corollary 1.2.

Theorem 1.1 is also available in the form in which the paper states it:

```lean
-- NilpotentTridiagonal/Main.lean
theorem nilPairs_one : NilPairs 1 = {([0], [])}
theorem nilPairs_odd {h : ℕ} (hh : 1 ≤ h) :
    NilPairs (2 * h + 1) = oddFold '' (NilPairs h ×ˢ {1, -1})
theorem nilPairs_even (h : ℕ) :
    NilPairs (2 * h) = evenFold '' ((snocZero ⁻¹' NilPairs h) ×ˢ {1, -1})

-- NilpotentTridiagonal/Sizes.lean
lemma oddFold_injective : Function.Injective oddFold
lemma evenFold_injective : Function.Injective evenFold

-- NilpotentTridiagonal/Pairs.lean
theorem folded_iff (d b : List ℤ) :
    Folded d b ↔ IsPair d b ∧ charPoly d b = X ^ d.length
```

Here `oddFold ((d, b), ε)` and `evenFold ((d, b), δ)` are the two folds as maps, and `snocZero (d, b) = ((d, 0), b)`, so `snocZero ⁻¹' NilPairs h` is the set of the pairs `(d, b)` for which `((d, 0), b)` is a nilpotent pair of size `h`.

## Rigidity modulo 4 and powers of two

The statements below are about a pair given by two sequences `d b : ℕ → ℤ`, of which the first `n` and `n − 1` values count. `K d b n : ℤ[X]` is its characteristic polynomial, and `InC d b n` says that the pair lies in 𝒞ₙ.

```lean
-- NilpotentTridiagonal/Classification.lean
theorem mod_four_odd_iff {d b : ℕ → ℤ} {h : ℕ} (hC : InC d b (2 * h + 1)) :
    (4 : ℤ[X]) ∣ K d b (2 * h + 1) - X ^ (2 * h + 1) ↔
      d h = 0 ∧ (∀ i < h, d (2 * h - i) = d i) ∧ (∀ i, i + 1 < h → b (2 * h - 1 - i) = b i)
        ∧ (1 ≤ h → b h = -b (h - 1)) ∧ (2 : ℤ[X]) ∣ K d b h - X ^ h

theorem mod_four_even_iff {d b : ℕ → ℤ} {m : ℕ} (hC : InC d b (2 * m + 2)) :
    (4 : ℤ[X]) ∣ K d b (2 * m + 2) - X ^ (2 * m + 2) ↔
      d m ≠ 0 ∧ d (m + 1) = -d m ∧ b m = -1 ∧ (∀ i < m, d (2 * m + 1 - i) = d i)
        ∧ (∀ i < m, b (2 * m - i) = b i)
        ∧ (2 : ℤ[X]) ∣ K (Function.update d m 0) b (m + 1) - X ^ (m + 1)

theorem nil_of_congr (n : ℕ) : ∀ {d b : ℕ → ℤ}, 1 ≤ n → InC d b n →
    (2 : ℤ[X]) ^ (Nat.log 2 n + 1) ∣ K d b n - X ^ n → K d b n = X ^ n
```

- **`mod_four_odd_iff`, `mod_four_even_iff`** are Theorem 1.5: the characteristic polynomial is congruent to `X ^ n` modulo 4 exactly when the pair is a fold of a pair that is nilpotent modulo 2. The conditions on the right spell out the shape of an odd fold (central diagonal entry 0, mirror-image halves, opposite central products) and of an even fold (central diagonal entries `−δ, δ` with `δ ≠ 0`, central product `−1`, mirror-image halves otherwise). In the even case the pair that is folded is the left half with last diagonal entry 0, which is `Function.update d m 0`.
- **`descent_odd`, `descent_even`** (same file) are the identity (5) of the paper, `v(χ_P − λⁿ) = v(χ_p − λ^h) + 1`, in the form: for `k ≥ 1`, `2 ^ (k + 1)` divides `χ_P − λⁿ` if and only if `2 ^ k` divides `χ_p − λ^h`.
- **`nil_of_congr`** is Corollary 1.6 (i).
- **`nil_odd_iff`, `nil_even_iff`** (same file) are Theorem 1.1 in the same entrywise form.

## Files

| File | Content |
|---|---|
| `NilpotentTridiagonal/Continuant.lean` | the characteristic polynomial `K d b n` of a pair, by its three-term recurrence; splitting at an edge, reversal, dependence on a single entry |
| `NilpotentTridiagonal/Fold.lean` | the two folding identities (Lemma 2.1), over every commutative ring |
| `NilpotentTridiagonal/ModTwo.lean` | the situation modulo 2 (Lemma 2.3): the identity (12), uniqueness of the nilpotent diagonal, and its structure as a fold |
| `NilpotentTridiagonal/Transversality.lean` | Lemma 2.4: the partial derivatives of the characteristic polynomial span the polynomials of degree less than `n`, and for a palindrome one half of them is linearly independent |
| `NilpotentTridiagonal/Linearise.lean` | the first-order expansion of `K` under a perturbation `t` with `t² = 0`, and its expression by the partial derivatives |
| `NilpotentTridiagonal/Congruence.lean` | congruences between integer polynomials, read in `(ℤ/m)[X]`; the descent step |
| `NilpotentTridiagonal/Rigidity.lean` | the class 𝒞ₙ (`InC`), the comparison of a pair with the fold of its own left half, and Theorem 1.5 in the direction "only if" (`rigid_odd`, `rigid_even`) |
| `NilpotentTridiagonal/Classification.lean` | Theorem 1.5, the descent, Theorem 1.1 for sequences, Corollary 1.6 (i) |
| `NilpotentTridiagonal/Folded.lean` | folded pairs of lists |
| `NilpotentTridiagonal/Pairs.lean` | Theorem 1.1 for pairs of lists (`folded_iff`) |
| `NilpotentTridiagonal/Matrix.lean` | the tridiagonal matrix `Tri`, its characteristic polynomial by Laplace expansion, and nilpotency |
| `NilpotentTridiagonal/Sizes.lean` | the sizes and the number of the folded pairs |
| `NilpotentTridiagonal/Main.lean` | Theorem 1.1 for matrices, the sets 𝒩ₙ, Corollary 1.2 |
| `Axioms.lean` | prints the axioms used by the main theorems |
| `Examples.lean` | the main theorems applied to concrete matrices and sizes (Liu's matrix of size 6, the sizes 4 and 7) |

The formalisation has about 3,000 lines. Corollary 1.4 (the number of all nilpotent tridiagonal matrices with entries in {−1, 0, 1}), Corollary 1.6 (ii) and (iii), Proposition 3.2 and Sections 4 and 5 of the paper are not formalised; they are checked by the programs in `../computations`.

## Checking

You need [elan](https://github.com/leanprover/elan). The toolchain is `leanprover/lean4:v4.36.0` and Mathlib is `v4.36.0`.

```
lake exe cache get      # download the compiled Mathlib (about 5 GB)
lake build              # compiles the proof
lake env lean Axioms.lean
lake env lean Examples.lean   # no output: all examples are proved
```

**Build.** `lake build` compiles all files with no errors and no warnings. The files use the module system, and Mathlib's standard linter set is on. The copyright-header linter is switched off in `lakefile.toml`, because it enforces a Mathlib convention.

**Axioms.** The command `lake env lean Axioms.lean` prints `[propext, Classical.choice, Quot.sound]` for each of the twelve main theorems. These are only Lean's standard axioms, so there is no `sorry`.

Checked on 21 November 2026.
