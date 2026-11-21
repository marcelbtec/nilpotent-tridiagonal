module

public import NilpotentTridiagonal.ModTwo

/-!
# Congruences between integer polynomials

An integer polynomial is divisible by a natural number `m` if and only if it vanishes in
`(ℤ / m)[X]`. We record this for continuants, and we prove the descent step of the main argument:
for a monic polynomial `q` of degree `h`, squaring improves a congruence `q ≡ X ^ h` modulo a
power of `2` by exactly one power of `2` (`descent`).
-/

@[expose] public section

open Polynomial

namespace Tridiagonal

/-- An integer polynomial is divisible by `m` if and only if it vanishes modulo `m`. -/
lemma natCast_dvd_iff_map_eq_zero (m : ℕ) (f : ℤ[X]) :
    (m : ℤ[X]) ∣ f ↔ f.map (Int.castRingHom (ZMod m)) = 0 := by
  rw [← map_natCast (C : ℤ →+* ℤ[X]) m, C_dvd_iff_dvd_coeff]
  constructor
  · intro h
    ext i
    rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h i
  · intro h i
    have hi := congrArg (fun p : (ZMod m)[X] => p.coeff i) h
    simp only [coeff_map, coeff_zero, eq_intCast] at hi
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi

/-- Two integer polynomials are congruent modulo `m` if and only if they agree modulo `m`. -/
lemma natCast_dvd_sub_iff_map_eq (m : ℕ) (f g : ℤ[X]) :
    (m : ℤ[X]) ∣ f - g
      ↔ f.map (Int.castRingHom (ZMod m)) = g.map (Int.castRingHom (ZMod m)) := by
  rw [natCast_dvd_iff_map_eq_zero, Polynomial.map_sub, sub_eq_zero]

/-- The reduction of a continuant modulo `m`. -/
lemma K_map_intCast (m : ℕ) (d b : ℕ → ℤ) (n : ℕ) :
    (K d b n).map (Int.castRingHom (ZMod m))
      = K (fun i => (d i : ZMod m)) (fun i => (b i : ZMod m)) n := by
  rw [K_map]
  simp only [eq_intCast]

/-- The congruence `K d b n ≡ X ^ n` modulo `m`, read in `(ℤ / m)[X]`. -/
lemma natCast_dvd_K_sub_iff (m : ℕ) (d b : ℕ → ℤ) (n : ℕ) :
    (m : ℤ[X]) ∣ K d b n - X ^ n
      ↔ K (fun i => (d i : ZMod m)) (fun i => (b i : ZMod m)) n = X ^ n := by
  rw [natCast_dvd_sub_iff_map_eq, K_map_intCast, Polynomial.map_pow, map_X]

lemma two_dvd_K_sub_iff (d b : ℕ → ℤ) (n : ℕ) :
    (2 : ℤ[X]) ∣ K d b n - X ^ n
      ↔ K (fun i => (d i : ZMod 2)) (fun i => (b i : ZMod 2)) n = X ^ n :=
  natCast_dvd_K_sub_iff 2 d b n

lemma four_dvd_K_sub_iff (d b : ℕ → ℤ) (n : ℕ) :
    (4 : ℤ[X]) ∣ K d b n - X ^ n
      ↔ K (fun i => (d i : ZMod 4)) (fun i => (b i : ZMod 4)) n = X ^ n :=
  natCast_dvd_K_sub_iff 4 d b n

/-- A natural number which divides `g * M`, with `M` monic, divides `g`. -/
lemma natCast_dvd_of_dvd_mul_monic (m : ℕ) {g M : ℤ[X]} (hM : M.Monic)
    (h : (m : ℤ[X]) ∣ g * M) : (m : ℤ[X]) ∣ g := by
  rw [natCast_dvd_iff_map_eq_zero] at h ⊢
  rw [Polynomial.map_mul] at h
  exact (hM.map _).mul_left_eq_zero_iff.mp h

/-! ### Integers modulo 2 -/

lemma intCast_zmod2_of_unit {a : ℤ} (h : a = 1 ∨ a = -1) : ((a : ℤ) : ZMod 2) = 1 := by
  rcases h with rfl | rfl
  · rw [Int.cast_one]
  · rw [Int.cast_neg, Int.cast_one]
    decide

lemma two_dvd_of_cast_eq_zero {a : ℤ} (h : ((a : ℤ) : ZMod 2) = 0) : (2 : ℤ) ∣ a := by
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h

lemma cast_eq_zero_of_two_dvd {a : ℤ} (h : (2 : ℤ) ∣ a) : ((a : ℤ) : ZMod 2) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr (by exact_mod_cast h)

lemma two_dvd_sub_of_cast_eq {a c : ℤ} (h : ((a : ℤ) : ZMod 2) = (c : ZMod 2)) :
    (2 : ℤ) ∣ a - c := by
  apply two_dvd_of_cast_eq_zero
  rw [Int.cast_sub, h, sub_self]

/-! ### Descent -/

/-- **Descent.** Let `q` be a monic integer polynomial of degree `h`, and let `k ≥ 1`. Then
`X ^ e * q ^ 2 ≡ X ^ (e + 2 h)` modulo `2 ^ (k + 1)` if and only if `q ≡ X ^ h` modulo `2 ^ k`. -/
theorem descent {q : ℤ[X]} {h : ℕ} (hq : q.Monic) (hdeg : q.natDegree = h) (e : ℕ) {k : ℕ}
    (hk : 1 ≤ k) :
    (2 : ℤ[X]) ^ (k + 1) ∣ X ^ e * q ^ 2 - X ^ (e + 2 * h) ↔ (2 : ℤ[X]) ^ k ∣ q - X ^ h := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  constructor
  · intro hD
    -- modulo 2 the polynomial `q` is `X ^ h`
    have h2 : (2 : ℤ[X]) ∣ X ^ e * q ^ 2 - X ^ (e + 2 * h) :=
      dvd_trans (dvd_pow_self 2 (by omega)) hD
    have hm := (natCast_dvd_sub_iff_map_eq 2 _ _).mp h2
    simp only [Polynomial.map_mul, Polynomial.map_pow, map_X] at hm
    have hsq : (q.map (Int.castRingHom (ZMod 2))) ^ 2 = (X ^ h) ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero e (X_ne_zero (R := ZMod 2)))
      rw [hm]
      ring
    have hq2 : (2 : ℤ[X]) ∣ q - X ^ h := by
      refine (natCast_dvd_sub_iff_map_eq 2 _ _).mpr ?_
      rw [eq_of_sq_eq_sq_Z2 hsq, Polynomial.map_pow, map_X]
    obtain ⟨g, hg⟩ := hq2
    -- the quotient `g` has degree less than `h`
    have hgdeg : g.degree < h := by
      rw [degree_lt_iff_coeff_zero]
      intro j hj
      have h2C : (2 : ℤ[X]) = C (2 : ℤ) := (map_ofNat C 2).symm
      have hc : q.coeff j - (X ^ h : ℤ[X]).coeff j = 2 * g.coeff j := by
        rw [← coeff_sub, hg, h2C, coeff_C_mul]
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · have h1 : q.coeff h = 1 := by
          have := hq.coeff_natDegree
          rwa [hdeg] at this
        rw [h1, coeff_X_pow_self] at hc
        omega
      · have h0 : q.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hlt)
        have h0' : (X ^ h : ℤ[X]).coeff j = 0 := by
          rw [coeff_X_pow]
          simp [hlt.ne']
        rw [h0, h0'] at hc
        omega
    have hmon : (X ^ e * (X ^ h + g)).Monic := (monic_X_pow e).mul (monic_X_pow_add hgdeg)
    have hfac : X ^ e * q ^ 2 - X ^ (e + 2 * h) = 2 ^ 2 * (g * (X ^ e * (X ^ h + g))) := by
      have : q = X ^ h + 2 * g := by linear_combination hg
      rw [this]
      ring
    rw [hfac, show k + 1 + 1 = 2 + k by omega, pow_add] at hD
    have hD' : (2 : ℤ[X]) ^ k ∣ g * (X ^ e * (X ^ h + g)) :=
      (mul_dvd_mul_iff_left (pow_ne_zero 2 two_ne_zero)).mp hD
    have hg' : (2 : ℤ[X]) ^ k ∣ g := by
      have := natCast_dvd_of_dvd_mul_monic (2 ^ k) hmon (by push_cast; exact hD')
      push_cast at this
      exact this
    rw [hg, pow_succ, mul_comm ((2 : ℤ[X]) ^ k) 2]
    exact mul_dvd_mul_left 2 hg'
  · rintro ⟨g, hg⟩
    refine ⟨X ^ e * g * (X ^ h + 2 ^ k * g), ?_⟩
    have : q = X ^ h + 2 ^ (k + 1) * g := by linear_combination hg
    rw [this]
    ring

end Tridiagonal
