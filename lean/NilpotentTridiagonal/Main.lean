module

public import NilpotentTridiagonal.Pairs
public import NilpotentTridiagonal.Matrix
public import NilpotentTridiagonal.Sizes

/-!
# The nilpotent tridiagonal matrices with entries in `{-1, 0, 1}`

Let `M` be an `n × n` integer tridiagonal matrix with diagonal entries in `{-1, 0, 1}` and
off-diagonal entries in `{1, -1}`. Then `M` is nilpotent if and only if the pair formed by its
diagonal and by the products of its opposite off-diagonal entries is obtained from `((0), ())` by
folds (`isNilpotent_iff_folded`).

The set `NilPairs n` of the nilpotent pairs of size `n` is described recursively by
`nilPairs_one`, `nilPairs_odd` and `nilPairs_even`. It is non-empty if and only if `n = 1` or
`3 · 2 ^ j - 1 ≤ n ≤ 2 ^ (j + 2) - 1` for some `j` (`nilPairs_nonempty_iff`), and then it has
`2 ^ ⌊log₂ n⌋` elements (`nilPairs_ncard`).
-/

@[expose] public section

open Polynomial

namespace Tridiagonal

lemma seqOf_zipWith_mul (a c : List ℤ) {i : ℕ} (ha : i < a.length) (hc : i < c.length) :
    seqOf (List.zipWith (· * ·) a c) i = seqOf a i * seqOf c i := by
  unfold seqOf
  grind

/-- **Classification of the nilpotent tridiagonal matrices.** Let `d` be a list of `n` integers in
`{-1, 0, 1}` and let `a` and `c` be lists of `n - 1` integers in `{1, -1}`. The tridiagonal matrix
with diagonal `d`, superdiagonal `a` and subdiagonal `c` is nilpotent if and only if the pair
`(d, a * c)` is obtained from `((0), ())` by folds. -/
theorem isNilpotent_iff_folded (d a c : List ℤ) (ha : a.length + 1 = d.length)
    (hc : c.length + 1 = d.length) (hd : ∀ x ∈ d, x = -1 ∨ x = 0 ∨ x = 1)
    (ha1 : ∀ x ∈ a, x = 1 ∨ x = -1) (hc1 : ∀ x ∈ c, x = 1 ∨ x = -1) :
    IsNilpotent (Tri d.length (seqOf d) (seqOf a) (seqOf c))
      ↔ Folded d (List.zipWith (· * ·) a c) := by
  have hP : IsPair d (List.zipWith (· * ·) a c) := by
    refine ⟨by rw [List.length_zipWith]; omega, hd, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_zipWith] at hi
    rw [List.getElem_zipWith]
    have h1 := ha1 _ (List.getElem_mem (by omega : i < a.length))
    have h2 := hc1 _ (List.getElem_mem (by omega : i < c.length))
    rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> simp [e1, e2]
  rw [Tri_isNilpotent_iff, folded_iff]
  constructor
  · intro hK
    refine ⟨hP, ?_⟩
    unfold charPoly
    rw [← hK]
    exact K_congr (fun _ _ => rfl) (fun i hi => seqOf_zipWith_mul a c (by omega) (by omega))
  · rintro ⟨-, hK⟩
    unfold charPoly at hK
    rw [← hK]
    exact K_congr (fun _ _ => rfl)
      (fun i hi => (seqOf_zipWith_mul a c (by omega) (by omega)).symm)

/-! ### The sets of nilpotent pairs -/

/-- The set `𝒩_n` of the nilpotent pairs of size `n`: the pairs of lists `(d, b)` with `d` of
length `n`, entries of `d` in `{-1, 0, 1}`, entries of `b` in `{1, -1}`, and characteristic
polynomial `X ^ n`. -/
def NilPairs (n : ℕ) : Set (List ℤ × List ℤ) :=
  {p | IsPair p.1 p.2 ∧ p.1.length = n ∧ charPoly p.1 p.2 = X ^ n}

/-- The nilpotent pairs of size `n` are the folded pairs of size `n`. -/
theorem nilPairs_eq_foldedOfSize (n : ℕ) : NilPairs n = FoldedOfSize n := by
  ext ⟨d, b⟩
  change IsPair d b ∧ d.length = n ∧ charPoly d b = X ^ n ↔ Folded d b ∧ d.length = n
  rw [folded_iff]
  constructor
  · rintro ⟨hP, hn, hK⟩
    exact ⟨⟨hP, by rw [hn]; exact hK⟩, hn⟩
  · rintro ⟨⟨hP, hK⟩, hn⟩
    exact ⟨hP, hn, by rw [← hn]; exact hK⟩

/-- **Classification, size 1.** The only nilpotent pair of size `1` is `((0), ())`. -/
theorem nilPairs_one : NilPairs 1 = {([0], [])} := by
  rw [nilPairs_eq_foldedOfSize, foldedOfSize_one]

/-- **Classification, odd size.** The nilpotent pairs of size `2 h + 1`, `h ≥ 1`, are the odd
folds `((d, 0, rev d), (b, ε, -ε, rev b))` of the nilpotent pairs `(d, b)` of size `h`, with
`ε = ±1`. The map `oddFold` is injective (`oddFold_injective`). -/
theorem nilPairs_odd {h : ℕ} (hh : 1 ≤ h) :
    NilPairs (2 * h + 1) = oddFold '' (NilPairs h ×ˢ {1, -1}) := by
  rw [nilPairs_eq_foldedOfSize, nilPairs_eq_foldedOfSize, foldedOfSize_odd hh]

/-- **Classification, even size.** The nilpotent pairs of size `2 h` are the even folds
`((d, -δ, δ, rev d), (b, -1, rev b))` of the nilpotent pairs `((d, 0), b)` of size `h` whose last
diagonal entry is `0`, with `δ = ±1`. The map `evenFold` is injective (`evenFold_injective`). -/
theorem nilPairs_even (h : ℕ) :
    NilPairs (2 * h) = evenFold '' ((snocZero ⁻¹' NilPairs h) ×ˢ {1, -1}) := by
  rw [nilPairs_eq_foldedOfSize, nilPairs_eq_foldedOfSize, foldedOfSize_even]

/-- **Admissible sizes.** There is a nilpotent pair of size `n` if and only if `n = 1` or
`3 · 2 ^ j - 1 ≤ n ≤ 2 ^ (j + 2) - 1` for some `j`. -/
theorem nilPairs_nonempty_iff (n : ℕ) :
    (NilPairs n).Nonempty ↔ n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j - 1 ≤ n ∧ n ≤ 2 ^ (j + 2) - 1 := by
  rw [nilPairs_eq_foldedOfSize]
  exact foldedOfSize_nonempty_iff n

theorem nilPairs_finite (n : ℕ) : (NilPairs n).Finite := by
  rw [nilPairs_eq_foldedOfSize]
  exact foldedOfSize_finite n

/-- **Count.** If there is a nilpotent pair of size `n`, there are exactly `2 ^ ⌊log₂ n⌋`. -/
theorem nilPairs_ncard {n : ℕ} (hn : (NilPairs n).Nonempty) :
    (NilPairs n).ncard = 2 ^ Nat.log 2 n := by
  rw [nilPairs_eq_foldedOfSize] at hn ⊢
  exact foldedOfSize_ncard hn

end Tridiagonal
