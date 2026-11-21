module

public import NilpotentTridiagonal.Fold

/-!
# The situation modulo 2

Over `𝔽₂` all products `±1` become `1`. We show that for every size `n` there is at most one
diagonal `d` over `𝔽₂` with `K d 1 n = X ^ n` (`nil_unique`), that it is a palindrome
(`nil_palindrome`), and that it is the fold of the corresponding diagonal of half the size
(`mod2_odd`, `mod2_even`).

The uniqueness rests on a polynomial identity (`riccati`), a finite form of the criterion of Baum
and Sweet: with `p = K d 1 (n + 1)` and `q` the continuant of the positions `1, …, n`,

  p² + X p q + q² + 1 = (1 + X) g²  for some polynomial `g`.

If `p = X ^ (n + 1)`, comparing the coefficients of `X ^ (2 j)` and `X ^ (2 j + 1)` determines `q`,
and the pair `(p, q)` determines `d` by division with remainder.
-/

@[expose] public section

open Polynomial Finset

namespace Tridiagonal

lemma two_eq_zero_Z2X : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero

lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by revert a; decide

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- Over `𝔽₂` a polynomial is determined by its square. -/
lemma eq_of_sq_eq_sq_Z2 {a b : (ZMod 2)[X]} (h : a ^ 2 = b ^ 2) : a = b := by
  have h0 : (a - b) ^ 2 = 0 := by
    linear_combination h + (b ^ 2 - a * b) * two_eq_zero_Z2X
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)

/-! ### The finite Baum–Sweet identity -/

/-- For every diagonal `d` over `𝔽₂`, with `p` the continuant of the positions `0, …, n` and `q`
that of the positions `1, …, n`, the polynomial `p² + X p q + q² + 1` is `1 + X` times a square. -/
lemma riccati : ∀ (n : ℕ) (d : ℕ → ZMod 2), ∃ g : (ZMod 2)[X],
    K d 1 (n + 1) ^ 2 + X * K d 1 (n + 1) * K (sh 1 d) 1 n + K (sh 1 d) 1 n ^ 2 + 1
      = (1 + X) * g ^ 2
  | 0, d => by
      refine ⟨C (d 0), ?_⟩
      have hsq : (C (d 0) : (ZMod 2)[X]) * C (d 0) = C (d 0) := by rw [← C_mul, zmod2_mul_self]
      rw [zero_add, K_one, K_zero]
      linear_combination (X ^ 2 - 2 * X * C (d 0) + 1) * two_eq_zero_Z2X - X * hsq
  | n + 1, d => by
      obtain ⟨g, hg⟩ := riccati n (sh 1 d)
      rw [sh_sh, show 1 + 1 = 2 by rfl] at hg
      refine ⟨g + C (d 0) * K (sh 1 d) 1 (n + 1), ?_⟩
      have hsq : (C (d 0) : (ZMod 2)[X]) * C (d 0) = C (d 0) := by rw [← C_mul, zmod2_mul_self]
      have hrec := K_succ_succ_left d 1 n
      rw [sh_one, sh_one] at hrec
      simp only [Pi.one_apply, C_1, one_mul] at hrec
      rw [hrec]
      linear_combination hg
        + (K (sh 1 d) 1 (n + 1) ^ 2 * (X ^ 2 - 2 * X * C (d 0))
            - K (sh 1 d) 1 (n + 1) * K (sh 2 d) 1 n * (2 * X - C (d 0))
            - (1 + X) * g * C (d 0) * K (sh 1 d) 1 (n + 1)) * two_eq_zero_Z2X
        - X * K (sh 1 d) 1 (n + 1) ^ 2 * hsq

/-! ### Coefficients of `(1 + X) g²` -/

lemma coeff_sq_even (g : (ZMod 2)[X]) (j : ℕ) : (g ^ 2).coeff (2 * j) = g.coeff j := by
  rw [← ZMod.expand_card, coeff_expand (by norm_num)]
  simp

lemma coeff_sq_odd (g : (ZMod 2)[X]) (j : ℕ) : (g ^ 2).coeff (2 * j + 1) = 0 := by
  rw [← ZMod.expand_card, coeff_expand (by norm_num)]
  split_ifs with h
  · omega
  · rfl

/-- In `(1 + X) g²` the coefficients of `X ^ (2 j)` and `X ^ (2 j + 1)` agree. -/
lemma coeff_one_add_X_mul_sq (g : (ZMod 2)[X]) (j : ℕ) :
    ((1 + X) * g ^ 2).coeff (2 * j) = ((1 + X) * g ^ 2).coeff (2 * j + 1) := by
  rw [add_mul, one_mul, coeff_add, coeff_add, coeff_X_mul, coeff_sq_even, coeff_sq_odd]
  rcases j with _ | j
  · simp
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, coeff_X_mul, coeff_sq_odd]
    ring

/-- A polynomial `u` of degree less than `N` with `u² + X ^ (N + 1) u = (1 + X) s²` vanishes. -/
lemma eq_zero_of_sq_add (N : ℕ) (u s : (ZMod 2)[X]) (hdeg : ∀ j, N ≤ j → u.coeff j = 0)
    (h : u ^ 2 + X ^ (N + 1) * u = (1 + X) * s ^ 2) : u = 0 := by
  ext j
  rw [coeff_zero]
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : N ≤ j
    · exact hdeg j hj
    · have h2 := congrArg (fun p : (ZMod 2)[X] => p.coeff (2 * j)) h
      have h3 := congrArg (fun p : (ZMod 2)[X] => p.coeff (2 * j + 1)) h
      simp only [coeff_add, coeff_sq_even, coeff_sq_odd, coeff_X_pow_mul'] at h2 h3
      rw [coeff_one_add_X_mul_sq] at h2
      have h4 := h2.trans h3.symm
      have e1 : (if N + 1 ≤ 2 * j then u.coeff (2 * j - (N + 1)) else 0) = 0 := by
        split_ifs with hc
        · exact ih _ (by omega)
        · rfl
      have e2 : (if N + 1 ≤ 2 * j + 1 then u.coeff (2 * j + 1 - (N + 1)) else 0) = 0 := by
        split_ifs with hc
        · exact ih _ (by omega)
        · rfl
      rw [e1, e2] at h4
      simpa using h4

/-! ### Uniqueness -/

/-- Two nilpotent diagonals of the same size have the same continuant after removal of the first
position. -/
lemma K_tail_eq {n : ℕ} {d d' : ℕ → ZMod 2} (h : K d 1 (n + 1) = X ^ (n + 1))
    (h' : K d' 1 (n + 1) = X ^ (n + 1)) : K (sh 1 d) 1 n = K (sh 1 d') 1 n := by
  obtain ⟨g, hg⟩ := riccati n d
  obtain ⟨g', hg'⟩ := riccati n d'
  rw [h] at hg
  rw [h'] at hg'
  have hu : K (sh 1 d) 1 n - K (sh 1 d') 1 n = 0 := by
    apply eq_zero_of_sq_add (n + 1) _ (g - g')
    · intro j hj
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [K_natDegree]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [K_natDegree]; omega), sub_zero]
    · linear_combination hg - hg'
        + ((K (sh 1 d') 1 n ^ 2 - K (sh 1 d) 1 n * K (sh 1 d') 1 n)
            - (1 + X) * (g' ^ 2 - g * g')) * two_eq_zero_Z2X
  exact sub_eq_zero.mp hu

/-- The continuant of a pair over `𝔽₂` with unit products, together with the continuant of the
positions `1, …, n`, determines the diagonal (division with remainder). -/
lemma K_pair_inj : ∀ (n : ℕ) (d d' : ℕ → ZMod 2), K d 1 (n + 1) = K d' 1 (n + 1) →
    K (sh 1 d) 1 n = K (sh 1 d') 1 n → ∀ i ≤ n, d i = d' i
  | 0, d, d', h, _ => by
      intro i hi
      obtain rfl : i = 0 := by omega
      rw [zero_add, K_one, K_one] at h
      have hC : (C (d 0) : (ZMod 2)[X]) = C (d' 0) := by linear_combination -h
      exact C_injective hC
  | n + 1, d, d', h, h2 => by
      have hl := K_succ_succ_left d 1 n
      have hl' := K_succ_succ_left d' 1 n
      rw [sh_one, sh_one] at hl hl'
      simp only [Pi.one_apply, C_1, one_mul] at hl hl'
      rw [show n + 1 + 1 = n + 2 by omega, hl, hl', h2] at h
      have h0 : d 0 = d' 0 := by
        by_contra hne
        have ha : d' 0 - d 0 ≠ 0 := fun e => hne (sub_eq_zero.mp e).symm
        have hdeg : (C (d' 0 - d 0) * K (sh 1 d') 1 (n + 1)).natDegree = n + 1 := by
          rw [natDegree_C_mul ha, K_natDegree]
        have heq : C (d' 0 - d 0) * K (sh 1 d') 1 (n + 1)
            = K (sh 2 d) 1 n - K (sh 2 d') 1 n := by
          rw [C_sub]
          linear_combination h
        rw [heq] at hdeg
        have hle := natDegree_sub_le (K (sh 2 d) 1 n) (K (sh 2 d') 1 n)
        rw [K_natDegree, K_natDegree, max_self] at hle
        omega
      have hR : K (sh 2 d) 1 n = K (sh 2 d') 1 n := by
        rw [h0] at h
        linear_combination -h
      intro i hi
      rcases i with _ | i
      · exact h0
      · have hrec := K_pair_inj n (sh 1 d) (sh 1 d') h2 (by rw [sh_sh, sh_sh]; exact hR) i
          (by omega)
        simpa using hrec

/-- **Uniqueness modulo 2.** There is at most one diagonal `d` over `𝔽₂` with `K d 1 N = X ^ N`. -/
theorem nil_unique {N : ℕ} {d d' : ℕ → ZMod 2} (h : K d 1 N = X ^ N) (h' : K d' 1 N = X ^ N) :
    ∀ i < N, d i = d' i := by
  rcases N with _ | n
  · intro i hi
    omega
  · intro i hi
    exact K_pair_inj n d d' (h.trans h'.symm) (K_tail_eq h h') i (by omega)

/-- The nilpotent diagonal modulo 2 is a palindrome. -/
theorem nil_palindrome {N : ℕ} {d : ℕ → ZMod 2} (h : K d 1 N = X ^ N) :
    ∀ i < N, d (N - 1 - i) = d i := by
  have hrev : K (fun i => d (N - 1 - i)) 1 N = X ^ N := by
    rw [← h]
    exact K_reverse d 1 N
  exact fun i hi => nil_unique hrev h i hi

/-! ### The nilpotent diagonal modulo 2 is the fold of the one of half the size -/

/-- Odd size: the central entry vanishes, the halves are mirror images, and the left half is
nilpotent. -/
theorem mod2_odd {h : ℕ} {d : ℕ → ZMod 2} (hK : K d 1 (2 * h + 1) = X ^ (2 * h + 1)) :
    d h = 0 ∧ (∀ i < h, d (2 * h - i) = d i) ∧ K d 1 h = X ^ h := by
  have hpal := nil_palindrome hK
  have hd : ∀ i < h, d (2 * h - i) = d i := fun i hi => by
    have := hpal i (by omega)
    rwa [show 2 * h + 1 - 1 - i = 2 * h - i by omega] at this
  have hfold := K_fold_odd d 1 h hd (fun _ _ => rfl)
    (fun _ => by simp only [Pi.one_apply]; decide)
  rw [hK] at hfold
  have h0 : d h = 0 := by
    rcases zmod2_cases (d h) with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at hfold
      have := congrArg (Polynomial.eval 1) hfold
      simp at this
  refine ⟨h0, hd, ?_⟩
  rw [h0, C_0, sub_zero] at hfold
  have hX : (X : (ZMod 2)[X]) * (X ^ h) ^ 2 = X * K d 1 h ^ 2 := by
    rw [← hfold]
    ring
  exact eq_of_sq_eq_sq_Z2 (mul_left_cancel₀ X_ne_zero hX).symm

/-- Even size: the diagonal is a palindrome, and the left half with its last entry raised by `1`
is nilpotent. -/
theorem mod2_even {n : ℕ} {d : ℕ → ZMod 2} (hK : K d 1 (2 * n + 2) = X ^ (2 * n + 2)) :
    (∀ i < 2 * n + 2, d (2 * n + 1 - i) = d i) ∧
      K (Function.update d n (d n + 1)) 1 (n + 1) = X ^ (n + 1) := by
  have hpal := nil_palindrome hK
  have hd : ∀ i < 2 * n + 2, d (2 * n + 1 - i) = d i := fun i hi => by
    have := hpal i hi
    rwa [show 2 * n + 2 - 1 - i = 2 * n + 1 - i by omega] at this
  refine ⟨hd, ?_⟩
  have hc : d (n + 1) = d n + (1 + 1) := by
    have := hd n (by omega)
    rw [show 2 * n + 1 - n = n + 1 by omega] at this
    rw [this, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
  have hfold := K_fold_even d 1 n 1 (by decide) hc (by simp only [Pi.one_apply]; decide)
    (fun i hi => hd i (by omega)) (fun _ _ => rfl)
  rw [hK] at hfold
  apply eq_of_sq_eq_sq_Z2
  rw [← hfold]
  ring

end Tridiagonal
