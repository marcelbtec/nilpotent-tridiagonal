module

public import NilpotentTridiagonal.Continuant

/-!
# The two folding identities

A pair of size `2h + 1` is an *odd fold* if its two halves are mirror images, its two central
products are opposite, and its central diagonal entry is `0`. Then `K = X * (K of a half)²`.

A pair of size `2h` is an *even fold* if its halves are mirror images except in the two central
diagonal entries, which are `z - δ` and `z + δ` with `δ² = 1`, and its central product is `-1`.
Then `K = (K of the left half with last diagonal entry z)²`.

Both identities hold over every commutative ring. The first is stated for an arbitrary central
entry `c`, which gives `K = (X - c) * (K of a half)²`.
-/

@[expose] public section

open Polynomial Finset

namespace Tridiagonal

variable {R : Type*} [CommRing R]

/-- The right half of a mirror-symmetric pair of size `2n + 3` has the continuant of the left
half. -/
private lemma right_half_odd (d b : ℕ → R) (n : ℕ)
    (hd : ∀ i < n + 1, d (2 * (n + 1) - i) = d i)
    (hb : ∀ i, i + 1 < n + 1 → b (2 * (n + 1) - 1 - i) = b i) :
    K (sh (n + 2) d) (sh (n + 2) b) (n + 1) = K d b (n + 1) := by
  rw [← K_reverse d b (n + 1)]
  apply K_congr
  · intro i hi
    simp only [sh_apply]
    exact idx_congr d (hd (n - i) (by omega)) (by omega) (by omega)
  · intro i hi
    simp only [sh_apply]
    exact idx_congr b (hb (n - 1 - i) (by omega)) (by omega) (by omega)

/-- The same with the position next to the centre removed. -/
private lemma right_half_odd' (d b : ℕ → R) (n : ℕ)
    (hd : ∀ i < n + 1, d (2 * (n + 1) - i) = d i)
    (hb : ∀ i, i + 1 < n + 1 → b (2 * (n + 1) - 1 - i) = b i) :
    K (sh (n + 3) d) (sh (n + 3) b) n = K d b n := by
  rw [← K_reverse d b n]
  apply K_congr
  · intro i hi
    simp only [sh_apply]
    exact idx_congr d (hd (n - 1 - i) (by omega)) (by omega) (by omega)
  · intro i hi
    simp only [sh_apply]
    exact idx_congr b (hb (n - 2 - i) (by omega)) (by omega) (by omega)

/-- **Odd fold.** If the two halves of a pair of size `2h + 1` are mirror images and the two
central products are opposite, then `K = (X - c) * (K of the left half)²`, where `c` is the central
diagonal entry. -/
lemma K_fold_odd (d b : ℕ → R) (h : ℕ)
    (hd : ∀ i < h, d (2 * h - i) = d i)
    (hb : ∀ i, i + 1 < h → b (2 * h - 1 - i) = b i)
    (hmid : 1 ≤ h → b h = -b (h - 1)) :
    K d b (2 * h + 1) = (X - C (d h)) * K d b h ^ 2 := by
  rcases h with _ | n
  · simp
  · have hsplit := K_split d b n (n + 1)
    rw [show n + (n + 1) + 2 = 2 * (n + 1) + 1 by omega] at hsplit
    have hleft := K_succ_succ_left (sh (n + 1) d) (sh (n + 1) b) n
    rw [sh_sh, sh_sh, sh_sh, sh_sh, show 1 + (n + 1) = n + 2 by omega,
      show 2 + (n + 1) = n + 3 by omega, right_half_odd d b n hd hb,
      right_half_odd' d b n hd hb] at hleft
    have e0 : d (0 + (n + 1)) = d (n + 1) := by congr 1; omega
    have e1 : b (0 + (n + 1)) = b (n + 1) := by congr 1; omega
    have hm := hmid (by omega)
    rw [show n + 1 - 1 = n by omega] at hm
    rw [hsplit, hleft, right_half_odd d b n hd hb, sh_apply, sh_apply, e0, e1, hm, C_neg]
    ring

/-- **Even fold.** Let a pair of size `2n + 2` have central product `-1` and central diagonal
entries `d n` and `d (n + 1) = d n + 2δ` with `δ² = 1`, and let its halves be mirror images
otherwise. Then `K` is the square of the continuant of the left half with its last diagonal entry
raised by `δ`. -/
lemma K_fold_even (d b : ℕ → R) (n : ℕ) (δ : R) (hδ : δ * δ = 1)
    (hc : d (n + 1) = d n + (δ + δ)) (hmid : b n = -1)
    (hd : ∀ i < n, d (2 * n + 1 - i) = d i)
    (hb : ∀ i < n, b (2 * n - i) = b i) :
    K d b (2 * n + 2) = K (Function.update d n (d n + δ)) b (n + 1) ^ 2 := by
  have hsplit := K_split d b n n
  rw [show n + n + 2 = 2 * n + 2 by omega] at hsplit
  -- the right half without its first position
  have hB : K (sh (n + 2) d) (sh (n + 2) b) n = K d b n := by
    rw [← K_reverse d b n]
    apply K_congr
    · intro i hi
      simp only [sh_apply]
      exact idx_congr d (hd (n - 1 - i) (by omega)) (by omega) (by omega)
    · intro i hi
      simp only [sh_apply]
      exact idx_congr b (hb (n - 2 - i) (by omega)) (by omega) (by omega)
  -- the right half is the left half with its last diagonal entry raised by 2δ
  have hA : K (sh (n + 1) d) (sh (n + 1) b) (n + 1)
      = K (Function.update d n (d n + (δ + δ))) b (n + 1) := by
    rw [← K_reverse (Function.update d n (d n + (δ + δ))) b (n + 1)]
    apply K_congr
    · intro i hi
      simp only [sh_apply]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        rw [show n + 1 - 1 - 0 = n by omega, Function.update_self, zero_add, hc]
      · rw [Function.update_of_ne (by omega)]
        exact idx_congr d (hd (n - i) (by omega)) (by omega) (by omega)
    · intro i hi
      simp only [sh_apply]
      exact idx_congr b (hb (n - 1 - i) (by omega)) (by omega) (by omega)
  have h2 := K_update_diag d b n (δ + δ) 0
  have h1 := K_update_diag d b n δ 0
  rw [add_zero, K_zero, mul_one] at h1 h2
  have hC : (C δ : R[X]) * C δ = 1 := by rw [← C_mul, hδ, C_1]
  rw [hsplit, hA, hB, h2, h1, hmid, C_add, C_neg, C_1]
  linear_combination (-(K d b n) ^ 2) * hC

end Tridiagonal
