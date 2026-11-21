import NilpotentTridiagonal

/-!
Examples: the main theorems applied to concrete matrices and sizes. This file is not part of the
library; check it with `lake env lean Examples.lean` (no output means that everything is proved).
-/

open Polynomial Tridiagonal

/-- The pair of Liu's matrix of size 6 is the even fold of the odd fold of `((0), ())`. -/
example : Folded [0, 0, -1, 1, 0, 0] [-1, 1, -1, 1, -1] :=
  Folded.even (d := [0, 0]) (b := [-1, 1]) (δ := 1)
    (Folded.odd (d := [0]) (b := []) (ε := -1) Folded.base (Or.inr rfl)) (Or.inl rfl)

/-- Hence the tridiagonal matrix with diagonal `(0, 0, -1, 1, 0, 0)`, superdiagonal
`(1, 1, 1, 1, 1)` and subdiagonal `(-1, 1, -1, 1, -1)` is nilpotent. -/
example : IsNilpotent (Tri 6 (seqOf [0, 0, -1, 1, 0, 0]) (seqOf [1, 1, 1, 1, 1])
    (seqOf [-1, 1, -1, 1, -1])) :=
  (isNilpotent_iff_folded [0, 0, -1, 1, 0, 0] [1, 1, 1, 1, 1] [-1, 1, -1, 1, -1] rfl rfl
    (by decide) (by decide) (by decide)).mpr
    (Folded.even (d := [0, 0]) (b := [-1, 1]) (δ := 1)
      (Folded.odd (d := [0]) (b := []) (ε := -1) Folded.base (Or.inr rfl)) (Or.inl rfl))

/-- The matrix `!![-1, 1; -1, 1]` is `Tri 2` of the lists `(-1, 1)`, `(1)`, `(-1)`. -/
example : Tri 2 (seqOf [-1, 1]) (seqOf [1]) (seqOf [-1]) = !![-1, 1; -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The pair `((0, 0), (1))` is not folded: its characteristic polynomial is `X ^ 2 - 1`. -/
example : ¬ Folded [0, 0] [1] := by
  intro h
  have h2 := (folded_iff [0, 0] [1]).mp h
  have hK := h2.2
  have hval := congrArg (Polynomial.eval 0) hK
  simp [charPoly, seqOf, K_succ_succ] at hval

/-- There is no nilpotent pair of size 4. -/
example : ¬ (NilPairs 4).Nonempty := by
  rw [nilPairs_nonempty_iff]
  rintro (h | ⟨j, h1, h2⟩)
  · omega
  · rcases j with _ | j
    · norm_num at h2
    · have : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      have := Nat.two_pow_pos j
      omega

/-- There are exactly four nilpotent pairs of size 7. -/
example : (NilPairs 7).ncard = 4 := by
  have hne : (NilPairs 7).Nonempty :=
    (nilPairs_nonempty_iff 7).mpr (Or.inr ⟨1, by norm_num, by norm_num⟩)
  rw [nilPairs_ncard hne]
  have : Nat.log 2 7 = 2 := by
    rw [Nat.log_eq_iff (by norm_num)]
    norm_num
  rw [this]
  norm_num

/-- A pair of size 3 whose characteristic polynomial is `X ^ 3` modulo 4 is nilpotent
(`⌊log₂ 3⌋ + 1 = 2`). -/
example (d b : ℕ → ℤ) (hC : InC d b 3) (h : (4 : ℤ[X]) ∣ K d b 3 - X ^ 3) : K d b 3 = X ^ 3 := by
  apply nil_of_congr 3 (by norm_num) hC
  have : Nat.log 2 3 = 1 := by
    rw [Nat.log_eq_iff (by norm_num)]
    norm_num
  rw [this]
  norm_num
  exact h
