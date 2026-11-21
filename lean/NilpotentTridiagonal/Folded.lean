module

public import Mathlib

/-!
# Folded pairs

A pair is here a pair of lists of integers: the diagonal `d`, of length `n`, and the products `b` of
opposite off-diagonal entries, of length `n - 1`.

The *odd fold* of `(d, b)` with sign `ε` is `((d, 0, rev d), (b, ε, -ε, rev b))`. The *even fold*
with sign `δ` of a pair `((d, 0), b)` whose last diagonal entry is `0` is
`((d, -δ, δ, rev d), (b, -1, rev b))`.

`Folded d b` says that the pair `(d, b)` is obtained from `((0), ())` by finitely many folds.
-/

@[expose] public section

namespace Tridiagonal

/-- The pairs obtained from `((0), ())` by odd folds, and by even folds of pairs whose last
diagonal entry is `0`. -/
inductive Folded : List ℤ → List ℤ → Prop
  | base : Folded [0] []
  | odd {d b : List ℤ} {ε : ℤ} (hp : Folded d b) (hε : ε = 1 ∨ ε = -1) :
      Folded (d ++ 0 :: d.reverse) (b ++ ε :: -ε :: b.reverse)
  | even {d b : List ℤ} {δ : ℤ} (hp : Folded (d ++ [0]) b) (hδ : δ = 1 ∨ δ = -1) :
      Folded (d ++ -δ :: δ :: d.reverse) (b ++ -1 :: b.reverse)

/-- The set of folded pairs of size `n`. -/
def FoldedOfSize (n : ℕ) : Set (List ℤ × List ℤ) := {p | Folded p.1 p.2 ∧ p.1.length = n}

/-- A folded pair of size `n` has `n - 1` products. -/
lemma Folded.length_eq {d b : List ℤ} (h : Folded d b) : b.length + 1 = d.length := by
  induction h with
  | base => rfl
  | odd hp hε ih =>
      simp only [List.length_append, List.length_cons, List.length_reverse]
      omega
  | even hp hδ ih =>
      simp only [List.length_append, List.length_cons, List.length_reverse, List.length_nil] at ih ⊢
      omega

/-- The diagonal entries of a folded pair lie in `{-1, 0, 1}`. -/
lemma Folded.diag_mem {d b : List ℤ} (h : Folded d b) : ∀ x ∈ d, x = -1 ∨ x = 0 ∨ x = 1 := by
  induction h with
  | base =>
      intro x hx
      simp only [List.mem_singleton] at hx
      exact Or.inr (Or.inl hx)
  | odd hp hε ih =>
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hx
      rcases hx with hx | hx | hx
      · exact ih x hx
      · exact Or.inr (Or.inl hx)
      · exact ih x hx
  | @even d b δ hp hδ ih =>
      intro x hx
      have ih' : ∀ x ∈ d, x = -1 ∨ x = 0 ∨ x = 1 := fun x hx => ih x (List.mem_append_left _ hx)
      simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hx
      rcases hx with hx | hx | hx | hx
      · exact ih' x hx
      · rcases hδ with h1 | h1 <;> omega
      · rcases hδ with h1 | h1 <;> omega
      · exact ih' x hx

/-- The products of a folded pair are `1` or `-1`. -/
lemma Folded.off_mem {d b : List ℤ} (h : Folded d b) : ∀ x ∈ b, x = 1 ∨ x = -1 := by
  induction h with
  | base =>
      intro x hx
      simp at hx
  | odd hp hε ih =>
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hx
      rcases hx with hx | hx | hx | hx
      · exact ih x hx
      · rcases hε with h1 | h1 <;> omega
      · rcases hε with h1 | h1 <;> omega
      · exact ih x hx
  | even hp hδ ih =>
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hx
      rcases hx with hx | hx | hx
      · exact ih x hx
      · exact Or.inr hx
      · exact ih x hx

end Tridiagonal
