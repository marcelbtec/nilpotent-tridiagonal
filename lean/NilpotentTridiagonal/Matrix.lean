module

public import NilpotentTridiagonal.Continuant

/-!
# Tridiagonal matrices

`Tri n d a c` is the `n × n` tridiagonal matrix with diagonal `d`, superdiagonal `a` and
subdiagonal `c`. Its characteristic polynomial is the continuant `K d b n` of the pair `(d, b)`,
where `b k = a k * c k` is the product of the two opposite off-diagonal entries (`Tri_charpoly`).
Hence, over an integral domain, `Tri n d a c` is nilpotent exactly when `K d b n = X ^ n`
(`Tri_isNilpotent_iff`).
-/

@[expose] public section

open Polynomial Matrix

namespace Tridiagonal

variable {R : Type*} [CommRing R]

/-- The `n × n` tridiagonal matrix with diagonal `d`, superdiagonal `a` and subdiagonal `c`:
`M k k = d k`, `M k (k + 1) = a k`, `M (k + 1) k = c k`, and all other entries are `0`. -/
def Tri (n : ℕ) (d a c : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  fun i j =>
    if (i : ℕ) = j then d i
    else if (j : ℕ) = i + 1 then a i
    else if (i : ℕ) = j + 1 then c j
    else 0

/-- The characteristic matrix of `Tri n d a c`, written out. -/
noncomputable def CM (n : ℕ) (d a c : ℕ → R) : Matrix (Fin n) (Fin n) R[X] :=
  fun i j =>
    if (i : ℕ) = j then X - C (d i)
    else if (j : ℕ) = i + 1 then -C (a i)
    else if (i : ℕ) = j + 1 then -C (c j)
    else 0

lemma charmatrix_Tri (n : ℕ) (d a c : ℕ → R) : charmatrix (Tri n d a c) = CM n d a c := by
  ext i j
  simp only [charmatrix_apply, diagonal_apply, Fin.ext_iff, CM, Tri]
  split_ifs <;> simp

lemma det_CM_zero (d a c : ℕ → R) : (CM 0 d a c).det = 1 := Matrix.det_isEmpty

lemma det_CM_one (d a c : ℕ → R) : (CM 1 d a c).det = X - C (d 0) := by
  rw [Matrix.det_unique]
  simp [CM]

/-- Expansion along the first column, then along the first row of the second minor. -/
lemma det_CM_succ_succ (m : ℕ) (d a c : ℕ → R) :
    (CM (m + 2) d a c).det = (X - C (d 0)) * (CM (m + 1) (sh 1 d) (sh 1 a) (sh 1 c)).det
      - C (a 0 * c 0) * (CM m (sh 2 d) (sh 2 a) (sh 2 c)).det := by
  -- the minor of the entry `(0, 0)`: rows and columns `1, …, m + 1`
  have hA : (CM (m + 2) d a c).submatrix (Fin.succAbove 0) Fin.succ
      = CM (m + 1) (sh 1 d) (sh 1 a) (sh 1 c) := by
    ext i j
    simp [CM]
  -- the minor of the entry `(1, 0)`: rows `0, 2, …, m + 1` and columns `1, …, m + 1`
  have hB : ((CM (m + 2) d a c).submatrix (Fin.succAbove 1) Fin.succ).det
      = -C (a 0) * (CM m (sh 2 d) (sh 2 a) (sh 2 c)).det := by
    -- its first row is `(-a 0, 0, …, 0)`, and the minor of its entry `(0, 0)` consists of the
    -- rows and columns `2, …, m + 1`
    have hC : ((CM (m + 2) d a c).submatrix (Fin.succAbove 1) Fin.succ).submatrix
        Fin.succ (Fin.succAbove 0) = CM m (sh 2 d) (sh 2 a) (sh 2 c) := by
      ext i j
      simp [CM]
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, hC]
    · simp [CM]
    · intro j _
      simp [CM]
  have h00 : CM (m + 2) d a c 0 0 = X - C (d 0) := by simp [CM]
  have h10 : CM (m + 2) d a c 1 0 = -C (c 0) := by simp [CM]
  -- the first column has entries only in the rows `0` and `1`
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero,
    Fin.succ_zero_eq_one, hA, hB, h00, h10, Fin.val_zero, Fin.val_one, C_mul]
  · ring
  · intro i _
    simp [CM]

/-- The determinant of the characteristic matrix of `Tri n d a c` is the continuant. -/
lemma det_CM : ∀ (n : ℕ) (d a c : ℕ → R), (CM n d a c).det = K d (fun k => a k * c k) n
  | 0, d, a, c => by rw [det_CM_zero, K_zero]
  | 1, d, a, c => by rw [det_CM_one, K_one]
  | m + 2, d, a, c => by
      rw [det_CM_succ_succ, det_CM (m + 1), det_CM m, K_succ_succ_left d (fun k => a k * c k) m]
      rfl

/-- The characteristic polynomial of a tridiagonal matrix is the continuant of its diagonal and of
the products of its opposite off-diagonal entries. -/
theorem Tri_charpoly (n : ℕ) (d a c : ℕ → R) :
    (Tri n d a c).charpoly = K d (fun k => a k * c k) n := by
  rw [Matrix.charpoly, charmatrix_Tri, det_CM]

/-- A square matrix over an integral domain is nilpotent if and only if its characteristic
polynomial is `X ^ n`. -/
lemma isNilpotent_iff_charpoly_eq_X_pow [IsDomain R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    IsNilpotent A ↔ A.charpoly = X ^ n := by
  constructor
  · intro h
    have h' := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
    rw [Fintype.card_fin] at h'
    exact sub_eq_zero.mp h'.eq_zero
  · intro h
    exact ⟨n, by rw [← aeval_X_pow (R := R), ← h, Matrix.aeval_self_charpoly]⟩

/-- A tridiagonal matrix over an integral domain is nilpotent if and only if its continuant is
`X ^ n`. -/
theorem Tri_isNilpotent_iff [IsDomain R] (n : ℕ) (d a c : ℕ → R) :
    IsNilpotent (Tri n d a c) ↔ K d (fun k => a k * c k) n = X ^ n := by
  rw [isNilpotent_iff_charpoly_eq_X_pow, Tri_charpoly]

example (n : ℕ) (d a c : ℕ → ℤ) :
    IsNilpotent (Tri n d a c) ↔ K d (fun k => a k * c k) n = X ^ n :=
  Tri_isNilpotent_iff n d a c

end Tridiagonal
