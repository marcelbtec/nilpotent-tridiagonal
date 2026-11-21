module

public import NilpotentTridiagonal.Transversality

/-!
# Linearisation

`V d b x y n` is the first-order variation of the continuant `K d b n` when the diagonal moves in
the direction `x` and the products move in the direction `y`. If `t * t = 0`, then

  K (d + t x) (b + t y) n = K d b n + t · V d b x y n

exactly (`K_perturb`); this will be applied in `ℤ / 4` with `t = 2`. For unit products, `-V` is the
linear combination of the polynomials `A k` and `B k` of the file `Transversality` with
coefficients `x k` and `y k` (`V_eq_sum`).
-/

@[expose] public section

open Polynomial Finset

namespace Tridiagonal

section Variation

variable {R : Type*} [CommRing R]

/-- The first-order variation of the continuant `K d b n` in the direction `(x, y)`. -/
noncomputable def V (d b x y : ℕ → R) : ℕ → R[X]
  | 0 => 0
  | 1 => -C (x 0)
  | (n + 2) => (X - C (d (n + 1))) * V d b x y (n + 1) - C (b n) * V d b x y n
      - C (x (n + 1)) * K d b (n + 1) - C (y n) * K d b n

@[simp] lemma V_zero (d b x y : ℕ → R) : V d b x y 0 = 0 := by rw [V]
@[simp] lemma V_one (d b x y : ℕ → R) : V d b x y 1 = -C (x 0) := by rw [V]

lemma V_succ_succ (d b x y : ℕ → R) (n : ℕ) :
    V d b x y (n + 2) = (X - C (d (n + 1))) * V d b x y (n + 1) - C (b n) * V d b x y n
      - C (x (n + 1)) * K d b (n + 1) - C (y n) * K d b n := by
  rw [V]

/-- If `t * t = 0`, the continuant of the perturbed pair `(d + t x, b + t y)` is given exactly by
its first-order expansion. -/
lemma K_perturb (t : R) (ht : t * t = 0) (d b x y : ℕ → R) : ∀ n : ℕ,
    K (fun i => d i + t * x i) (fun i => b i + t * y i) n = K d b n + C t * V d b x y n
  | 0 => by simp
  | 1 => by
      rw [K_one, K_one, V_one, C_add, C_mul]
      ring
  | n + 2 => by
      have hC : (C t : R[X]) * C t = 0 := by rw [← C_mul, ht, C_0]
      rw [K_succ_succ, K_perturb t ht d b x y (n + 1), K_perturb t ht d b x y n, K_succ_succ,
        V_succ_succ]
      simp only [C_add, C_mul]
      linear_combination (-(C (x (n + 1)) * V d b x y (n + 1)) - C (y n) * V d b x y n) * hC

/-- The variation commutes with ring homomorphisms. -/
lemma V_map {S : Type*} [CommRing S] (f : R →+* S) (d b x y : ℕ → R) : ∀ n : ℕ,
    (V d b x y n).map f
      = V (fun i => f (d i)) (fun i => f (b i)) (fun i => f (x i)) (fun i => f (y i)) n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [V_succ_succ, V_succ_succ]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
        K_map, V_map f d b x y (n + 1), V_map f d b x y n]

/-- `V d b x y n` depends only on the first `n - 1` products. -/
lemma V_congr_b {d b b' x y : ℕ → R} : ∀ {n : ℕ}, (∀ i, i + 1 < n → b i = b' i) →
    V d b x y n = V d b' x y n
  | 0, _ => by rw [V_zero, V_zero]
  | 1, _ => by rw [V_one, V_one]
  | n + 2, hb => by
      rw [V_succ_succ, V_succ_succ,
        V_congr_b (n := n + 1) (fun i hi => hb i (by omega)),
        V_congr_b (n := n) (fun i hi => hb i (by omega)), hb n (by omega),
        K_congr (d := d) (d' := d) (b := b) (b' := b') (n := n + 1) (fun _ _ => rfl)
          (fun i hi => hb i (by omega)),
        K_congr (d := d) (d' := d) (b := b) (b' := b') (n := n) (fun _ _ => rfl)
          (fun i hi => hb i (by omega))]

end Variation

section Sum

variable {F : Type*} [Field F]

lemma Aa_succ_succ (d : ℕ → F) {n k : ℕ} (hk : k < n) :
    Aa d (n + 2) k = (X - C (d (n + 1))) * Aa d (n + 1) k - Aa d n k := by
  unfold Aa
  have e : d (n - 1 - k + 1 + (k + 1)) = d (n + 1) := by congr 1; omega
  rw [show n + 2 - 1 - k = (n - 1 - k) + 2 by omega, show n + 1 - 1 - k = (n - 1 - k) + 1 by omega,
    K_succ_succ]
  simp only [sh_apply, e, Pi.one_apply, C_1, one_mul]
  ring

lemma Aa_self (d : ℕ → F) (n : ℕ) : Aa d (n + 1) n = K d 1 n := by
  unfold Aa
  rw [show n + 1 - 1 - n = 0 by omega, K_zero, mul_one]

lemma Aa_succ_self (d : ℕ → F) (n : ℕ) : Aa d (n + 2) n = (X - C (d (n + 1))) * K d 1 n := by
  unfold Aa
  have e : d (0 + (n + 1)) = d (n + 1) := by congr 1; omega
  rw [show n + 2 - 1 - n = 1 by omega, K_one, sh_apply, e]
  ring

lemma Bb_succ_succ (d : ℕ → F) {n k : ℕ} (hk : k + 1 < n) :
    Bb d (n + 2) k = (X - C (d (n + 1))) * Bb d (n + 1) k - Bb d n k := by
  unfold Bb
  have e : d (n - 2 - k + 1 + (k + 2)) = d (n + 1) := by congr 1; omega
  rw [show n + 2 - 2 - k = (n - 2 - k) + 2 by omega, show n + 1 - 2 - k = (n - 2 - k) + 1 by omega,
    K_succ_succ]
  simp only [sh_apply, e, Pi.one_apply, C_1, one_mul]
  ring

lemma Bb_self (d : ℕ → F) (n : ℕ) : Bb d (n + 2) n = K d 1 n := by
  unfold Bb
  rw [show n + 2 - 2 - n = 0 by omega, K_zero, mul_one]

lemma Bb_succ_self (d : ℕ → F) (n : ℕ) : Bb d (n + 3) n = (X - C (d (n + 2))) * K d 1 n := by
  unfold Bb
  have e : d (0 + (n + 2)) = d (n + 2) := by congr 1; omega
  rw [show n + 3 - 2 - n = 1 by omega, K_one, sh_apply, e]
  ring

/-- The sum over the `A k` satisfies the three-term recurrence, with a source term. -/
lemma sum_Aa_succ_succ (d x : ℕ → F) (n : ℕ) :
    ∑ k ∈ range (n + 2), C (x k) * Aa d (n + 2) k
      = (X - C (d (n + 1))) * ∑ k ∈ range (n + 1), C (x k) * Aa d (n + 1) k
        - ∑ k ∈ range n, C (x k) * Aa d n k + C (x (n + 1)) * K d 1 (n + 1) := by
  have h1 : ∑ k ∈ range n, C (x k) * Aa d (n + 2) k
      = (X - C (d (n + 1))) * ∑ k ∈ range n, C (x k) * Aa d (n + 1) k
        - ∑ k ∈ range n, C (x k) * Aa d n k := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [Aa_succ_succ d (mem_range.mp hk)]
    ring
  have h2 : Aa d (n + 2) (n + 1) = K d 1 (n + 1) := Aa_self d (n + 1)
  rw [sum_range_succ, sum_range_succ, h1, h2, Aa_succ_self, sum_range_succ _ n, Aa_self]
  ring

/-- The sum over the `B k` satisfies the three-term recurrence, with a source term. -/
lemma sum_Bb_succ_succ (d y : ℕ → F) (n : ℕ) :
    ∑ k ∈ range (n + 1), C (y k) * Bb d (n + 2) k
      = (X - C (d (n + 1))) * ∑ k ∈ range n, C (y k) * Bb d (n + 1) k
        - ∑ k ∈ range (n - 1), C (y k) * Bb d n k + C (y n) * K d 1 n := by
  rw [sum_range_succ, Bb_self]
  rcases n with _ | m
  · simp
  · have h1 : ∑ k ∈ range m, C (y k) * Bb d (m + 1 + 2) k
        = (X - C (d (m + 1 + 1))) * ∑ k ∈ range m, C (y k) * Bb d (m + 1 + 1) k
          - ∑ k ∈ range m, C (y k) * Bb d (m + 1) k := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k hk => ?_
      rw [Bb_succ_succ d (by have := mem_range.mp hk; omega)]
      ring
    have h2 : Bb d (m + 1 + 2) m = (X - C (d (m + 1 + 1))) * K d 1 m := Bb_succ_self d m
    have h3 : Bb d (m + 1 + 1) m = K d 1 m := Bb_self d m
    rw [sum_range_succ, h1, h2, sum_range_succ _ m, h3, Nat.add_sub_cancel]
    ring

/-- For unit products, `-V` is the linear combination of the polynomials `A k` and `B k` with
coefficients `x k` and `y k`. -/
lemma V_eq_sum (d x y : ℕ → F) : ∀ n : ℕ,
    V d 1 x y n
      = -(∑ k ∈ range n, C (x k) * Aa d n k + ∑ k ∈ range (n - 1), C (y k) * Bb d n k)
  | 0 => by simp
  | 1 => by simp [Aa]
  | n + 2 => by
      have ih1 := V_eq_sum d x y (n + 1)
      have ih0 := V_eq_sum d x y n
      rw [Nat.add_sub_cancel] at ih1
      rw [V_succ_succ, ih1, ih0, show n + 2 - 1 = n + 1 by omega, sum_Aa_succ_succ,
        sum_Bb_succ_succ]
      simp only [Pi.one_apply, C_1, one_mul]
      ring

end Sum

end Tridiagonal
