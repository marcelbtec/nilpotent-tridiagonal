module

public import Mathlib

/-!
# Continuants

A *pair* `(d, b)` consists of a diagonal `d 0, d 1, …` and of the products `b 0, b 1, …` of
opposite off-diagonal entries of a tridiagonal matrix. `K d b n` is the characteristic polynomial
of the leading `n × n` block of such a matrix:

  K d b 0 = 1,  K d b 1 = X - d 0,  K d b (n + 2) = (X - d (n + 1)) K d b (n + 1) - b n · K d b n.

Positions are counted from `0`. The characteristic polynomial of the block formed by the positions
`k, …, k + m - 1` is `K (sh k d) (sh k b) m`, where `sh k` shifts a sequence by `k`.
-/

@[expose] public section

open Polynomial Finset

namespace Tridiagonal

/-- The sequence `f` shifted by `k`. -/
def sh {α : Type*} (k : ℕ) (f : ℕ → α) : ℕ → α := fun i => f (i + k)

@[simp] lemma sh_apply {α : Type*} (k : ℕ) (f : ℕ → α) (i : ℕ) : sh k f i = f (i + k) := rfl

/-- Shifting twice. -/
lemma sh_sh {α : Type*} (j k : ℕ) (f : ℕ → α) : sh j (sh k f) = sh (j + k) f := by
  funext i
  simp only [sh_apply]
  congr 1
  omega

@[simp] lemma sh_one {α : Type*} [One α] (k : ℕ) : sh k (1 : ℕ → α) = 1 := rfl

/-- Transport of an equation between values of a sequence along equalities of indices. -/
lemma idx_congr {α : Type*} (f : ℕ → α) {a a' b b' : ℕ} (h : f a' = f b') (ha : a = a')
    (hb : b = b') : f a = f b := by
  subst ha hb
  exact h

variable {R : Type*} [CommRing R]

/-- The continuant of the pair `(d, b)`: the characteristic polynomial of the leading `n × n`
block. -/
noncomputable def K (d b : ℕ → R) : ℕ → R[X]
  | 0 => 1
  | 1 => X - C (d 0)
  | (n + 2) => (X - C (d (n + 1))) * K d b (n + 1) - C (b n) * K d b n

@[simp] lemma K_zero (d b : ℕ → R) : K d b 0 = 1 := by rw [K]
@[simp] lemma K_one (d b : ℕ → R) : K d b 1 = X - C (d 0) := by rw [K]

lemma K_succ_succ (d b : ℕ → R) (n : ℕ) :
    K d b (n + 2) = (X - C (d (n + 1))) * K d b (n + 1) - C (b n) * K d b n := by
  rw [K]

/-- `K d b n` depends only on the first `n` diagonal entries and the first `n - 1` products. -/
lemma K_congr {d d' b b' : ℕ → R} : ∀ {n : ℕ}, (∀ i < n, d i = d' i) →
    (∀ i, i + 1 < n → b i = b' i) → K d b n = K d' b' n
  | 0, _, _ => by simp
  | 1, hd, _ => by simp [hd 0 (by omega)]
  | n + 2, hd, hb => by
      rw [K_succ_succ, K_succ_succ,
        K_congr (n := n + 1) (fun i hi => hd i (by omega)) (fun i hi => hb i (by omega)),
        K_congr (n := n) (fun i hi => hd i (by omega)) (fun i hi => hb i (by omega)),
        hd (n + 1) (by omega), hb n (by omega)]

/-- Splitting at the edge between the positions `k` and `k + 1`. -/
lemma K_split (d b : ℕ → R) (k : ℕ) : ∀ m : ℕ,
    K d b (k + m + 2) = K d b (k + 1) * K (sh (k + 1) d) (sh (k + 1) b) (m + 1)
      - C (b k) * K d b k * K (sh (k + 2) d) (sh (k + 2) b) m
  | 0 => by
      simp only [add_zero, K_succ_succ, zero_add, K_one, sh_apply, K_zero]
      ring
  | 1 => by
      have e2 : d (1 + (k + 1)) = d (k + 2) := by congr 1; omega
      rw [show k + 1 + 2 = (k + 1) + 2 by omega, K_succ_succ, K_succ_succ d b k,
        show (1 : ℕ) + 1 = 0 + 2 by rfl, K_succ_succ (sh (k + 1) d) (sh (k + 1) b) 0]
      simp only [zero_add, K_one, K_zero, sh_apply, e2]
      ring
  | m + 2 => by
      have h1 := K_split d b k (m + 1)
      have h0 := K_split d b k m
      have e1 : d (m + 1 + 1 + (k + 1)) = d (k + m + 2 + 1) := by congr 1; omega
      have e2 : b (m + 1 + (k + 1)) = b (k + m + 2) := by congr 1; omega
      have e3 : d (m + 1 + (k + 2)) = d (k + m + 2 + 1) := by congr 1; omega
      have e4 : b (m + (k + 2)) = b (k + m + 2) := by congr 1; omega
      rw [show k + (m + 2) + 2 = (k + m + 2) + 2 by omega, K_succ_succ,
        show (k + m + 2) + 1 = k + (m + 1) + 2 by omega,
        show m + 2 + 1 = (m + 1) + 2 by omega,
        K_succ_succ (sh (k + 1) d) (sh (k + 1) b) (m + 1),
        K_succ_succ (sh (k + 2) d) (sh (k + 2) b) m, h1, h0]
      simp only [sh_apply, e1, e2, e3, e4]
      rw [show k + (m + 1) + 2 = k + m + 2 + 1 by omega]
      ring

/-- The recurrence from the first position. -/
lemma K_succ_succ_left (d b : ℕ → R) (m : ℕ) :
    K d b (m + 2) = (X - C (d 0)) * K (sh 1 d) (sh 1 b) (m + 1)
      - C (b 0) * K (sh 2 d) (sh 2 b) m := by
  have h := K_split d b 0 m
  simp only [zero_add, K_one, K_zero, mul_one] at h
  rw [h]

/-- Reversing a pair does not change its characteristic polynomial. -/
lemma K_reverse (d b : ℕ → R) : ∀ n : ℕ,
    K (fun i => d (n - 1 - i)) (fun i => b (n - 2 - i)) n = K d b n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [K_succ_succ, K_succ_succ_left d b n]
      have h1 : K (fun i => d (n + 2 - 1 - i)) (fun i => b (n + 2 - 2 - i)) (n + 1)
          = K (sh 1 d) (sh 1 b) (n + 1) := by
        rw [← K_reverse (sh 1 d) (sh 1 b) (n + 1)]
        apply K_congr
        · intro i hi
          simp only [sh_apply]
          congr 1
          omega
        · intro i hi
          simp only [sh_apply]
          congr 1
          omega
      have h0 : K (fun i => d (n + 2 - 1 - i)) (fun i => b (n + 2 - 2 - i)) n
          = K (sh 2 d) (sh 2 b) n := by
        rw [← K_reverse (sh 2 d) (sh 2 b) n]
        apply K_congr
        · intro i hi
          simp only [sh_apply]
          congr 1
          omega
        · intro i hi
          simp only [sh_apply]
          congr 1
          omega
      have e1 : d (n + 2 - 1 - (n + 1)) = d 0 := by congr 1; omega
      have e2 : b (n + 2 - 2 - n) = b 0 := by congr 1; omega
      rw [h1, h0, e1, e2]

/-- Continuants commute with ring homomorphisms. -/
lemma K_map {S : Type*} [CommRing S] (f : R →+* S) (d b : ℕ → R) : ∀ n : ℕ,
    (K d b n).map f = K (fun i => f (d i)) (fun i => f (b i)) n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [K_succ_succ, K_succ_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C,
        K_map f d b (n + 1), K_map f d b n]

/-- Continuants are monic of degree `n`. -/
lemma K_monic_natDegree [Nontrivial R] (d b : ℕ → R) :
    ∀ n : ℕ, (K d b n).Monic ∧ (K d b n).natDegree = n
  | 0 => by simp
  | 1 => by
      rw [K_one]
      exact ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩
  | n + 2 => by
      obtain ⟨m1, d1⟩ := K_monic_natDegree d b (n + 1)
      obtain ⟨-, d0⟩ := K_monic_natDegree d b n
      have hp : ((X - C (d (n + 1))) * K d b (n + 1)).Monic := (monic_X_sub_C _).mul m1
      have hpd : ((X - C (d (n + 1))) * K d b (n + 1)).natDegree = n + 2 := by
        rw [(monic_X_sub_C _).natDegree_mul m1, natDegree_X_sub_C, d1]
        omega
      have hq : (C (b n) * K d b n).natDegree
          < ((X - C (d (n + 1))) * K d b (n + 1)).natDegree := by
        rw [hpd]
        exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega)
      rw [K_succ_succ]
      exact ⟨hp.sub_of_left (degree_lt_degree hq),
        by rw [natDegree_sub_eq_left_of_natDegree_lt hq, hpd]⟩

lemma K_monic [Nontrivial R] (d b : ℕ → R) (n : ℕ) : (K d b n).Monic := (K_monic_natDegree d b n).1

lemma K_natDegree [Nontrivial R] (d b : ℕ → R) (n : ℕ) : (K d b n).natDegree = n :=
  (K_monic_natDegree d b n).2

/-! ### Dependence on a single entry -/

/-- The continuant is an affine function of each diagonal entry: raising `d j` by `t` lowers
`K d b n` by `t` times the product of the continuants to the left and to the right of `j`. -/
lemma K_update_diag (d b : ℕ → R) (j : ℕ) (t : R) : ∀ m : ℕ,
    K (Function.update d j (d j + t)) b (j + 1 + m)
      = K d b (j + 1 + m) - C t * K d b j * K (sh (j + 1) d) (sh (j + 1) b) m
  | 0 => by
      have hj : K (Function.update d j (d j + t)) b j = K d b j :=
        K_congr (fun i hi => Function.update_of_ne (by omega) _ _) (fun _ _ => rfl)
      rcases j with _ | j
      · simp
        ring
      · have hj' : K (Function.update d (j + 1) (d (j + 1) + t)) b j = K d b j :=
          K_congr (fun i hi => Function.update_of_ne (by omega) _ _) (fun _ _ => rfl)
        rw [add_zero, K_succ_succ, K_succ_succ, hj, hj', Function.update_self, K_zero, C_add]
        ring
  | 1 => by
      have hj : K (Function.update d j (d j + t)) b j = K d b j :=
        K_congr (fun i hi => Function.update_of_ne (by omega) _ _) (fun _ _ => rfl)
      have h0 := K_update_diag d b j t 0
      rw [add_zero] at h0
      have e : d (0 + (j + 1)) = d (j + 1) := by congr 1; omega
      rw [show j + 1 + 1 = j + 2 by omega, K_succ_succ, K_succ_succ d b j, h0, hj,
        Function.update_of_ne (by omega), K_zero, K_one, sh_apply, e]
      ring
  | m + 2 => by
      have h1 := K_update_diag d b j t (m + 1)
      have h0 := K_update_diag d b j t m
      have e1 : d (m + 1 + (j + 1)) = d (j + m + 1 + 1) := by congr 1; omega
      have e2 : b (m + (j + 1)) = b (j + m + 1) := by congr 1; omega
      rw [show j + 1 + (m + 2) = (j + m + 1) + 2 by omega, K_succ_succ, K_succ_succ d b (j + m + 1),
        show j + m + 1 + 1 = j + 1 + (m + 1) by omega, h1,
        show j + m + 1 = j + 1 + m by omega, h0,
        Function.update_of_ne (by omega),
        K_succ_succ (sh (j + 1) d) (sh (j + 1) b) m]
      have e3 : d (j + 1 + (m + 1)) = d (j + m + 1 + 1) := by congr 1; omega
      have e4 : b (j + 1 + m) = b (j + m + 1) := by congr 1; omega
      simp only [sh_apply, e1, e2, e3, e4]
      ring

/-- The continuant is an affine function of each product: raising `b j` by `t` lowers `K d b n`
by `t` times the product of the continuants to the left of `j` and to the right of `j + 1`. -/
lemma K_update_off (d b : ℕ → R) (j : ℕ) (t : R) : ∀ m : ℕ,
    K d (Function.update b j (b j + t)) (j + 2 + m)
      = K d b (j + 2 + m) - C t * K d b j * K (sh (j + 2) d) (sh (j + 2) b) m
  | 0 => by
      have hj : K d (Function.update b j (b j + t)) j = K d b j :=
        K_congr (fun _ _ => rfl) (fun i hi => Function.update_of_ne (by omega) _ _)
      have hj1 : K d (Function.update b j (b j + t)) (j + 1) = K d b (j + 1) :=
        K_congr (fun _ _ => rfl) (fun i hi => Function.update_of_ne (by omega) _ _)
      rw [add_zero, K_succ_succ, K_succ_succ d b j, hj, hj1, Function.update_self, K_zero, C_add]
      ring
  | 1 => by
      have hj1 : K d (Function.update b j (b j + t)) (j + 1) = K d b (j + 1) :=
        K_congr (fun _ _ => rfl) (fun i hi => Function.update_of_ne (by omega) _ _)
      have h0 := K_update_off d b j t 0
      rw [add_zero] at h0
      have e : d (0 + (j + 2)) = d (j + 2) := by congr 1; omega
      rw [show j + 2 + 1 = (j + 1) + 2 by omega, K_succ_succ, K_succ_succ d b (j + 1),
        show j + 1 + 1 = j + 2 by omega, h0, hj1,
        Function.update_of_ne (by omega), K_zero, K_one, sh_apply, e]
      ring
  | m + 2 => by
      have h1 := K_update_off d b j t (m + 1)
      have h0 := K_update_off d b j t m
      have e1 : d (m + 1 + (j + 2)) = d (j + m + 2 + 1) := by congr 1; omega
      have e2 : b (m + (j + 2)) = b (j + m + 2) := by congr 1; omega
      rw [show j + 2 + (m + 2) = (j + m + 2) + 2 by omega, K_succ_succ,
        K_succ_succ d b (j + m + 2),
        show j + m + 2 + 1 = j + 2 + (m + 1) by omega, h1,
        show j + m + 2 = j + 2 + m by omega, h0,
        Function.update_of_ne (by omega),
        K_succ_succ (sh (j + 2) d) (sh (j + 2) b) m]
      have e3 : d (j + 2 + (m + 1)) = d (j + m + 2 + 1) := by congr 1; omega
      have e4 : b (j + 2 + m) = b (j + m + 2) := by congr 1; omega
      simp only [sh_apply, e1, e2, e3, e4]
      ring

end Tridiagonal
