module

public import NilpotentTridiagonal.Rigidity

/-!
# Classification of the nilpotent pairs

For a pair `(d, b)` in `𝒞_n` we prove:

* `mod_four_odd_iff`, `mod_four_even_iff`: the characteristic polynomial is congruent to `X ^ n`
  modulo `4` if and only if the pair is a fold of a pair which is nilpotent modulo `2`;
* `descent_odd`, `descent_even`: each fold accounts for exactly one power of `2`;
* `nil_odd_iff`, `nil_even_iff`: the pair is nilpotent if and only if it is a fold of a nilpotent
  pair;
* `nil_of_congr`: the pair is nilpotent as soon as its characteristic polynomial is congruent to
  `X ^ n` modulo `2 ^ (⌊log₂ n⌋ + 1)`.

Here "fold" is expressed by equations between the entries: for odd size `2 h + 1`, the central
diagonal entry is `0`, the halves are mirror images and the central products are opposite; for
even size `2 m + 2`, the central diagonal entries are `-δ, δ` with `δ ≠ 0`, the central product is
`-1` and the halves are mirror images otherwise.
-/

@[expose] public section

open Polynomial

namespace Tridiagonal

lemma InC.mono {d b : ℕ → ℤ} {n n' : ℕ} (h : InC d b n) (hn : n' ≤ n) : InC d b n' :=
  ⟨fun i hi => h.1 i (by omega), fun i hi => h.2 i (by omega)⟩

lemma InC.update_zero {d b : ℕ → ℤ} {n : ℕ} (h : InC d b n) (j : ℕ) :
    InC (Function.update d j 0) b n := by
  refine ⟨fun i hi => ?_, h.2⟩
  rcases eq_or_ne i j with heq | hne
  · rw [heq, Function.update_self]
    exact Or.inr (Or.inl rfl)
  · rw [Function.update_of_ne hne]
    exact h.1 i hi

/-- A monic integer polynomial whose square is `X ^ (2 h)` is `X ^ h`. -/
lemma eq_X_pow_of_sq_eq {p : ℤ[X]} {h : ℕ} (hp : p.Monic) (hsq : p ^ 2 = (X ^ h) ^ 2) :
    p = X ^ h := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e
  · exact e
  · exfalso
    have h1 := hp.leadingCoeff
    rw [e, leadingCoeff_neg, leadingCoeff_X_pow] at h1
    norm_num at h1

/-! ### The characteristic polynomial of a fold -/

/-- The characteristic polynomial of an odd fold. -/
lemma K_of_odd_fold {d b : ℕ → ℤ} {h : ℕ} (h0 : d h = 0) (hd : ∀ i < h, d (2 * h - i) = d i)
    (hb : ∀ i, i + 1 < h → b (2 * h - 1 - i) = b i) (hmid : 1 ≤ h → b h = -b (h - 1)) :
    K d b (2 * h + 1) = X ^ 1 * K d b h ^ 2 := by
  rw [K_fold_odd d b h hd hb hmid, h0, C_0, sub_zero, pow_one]

/-- The characteristic polynomial of an even fold. -/
lemma K_of_even_fold {d b : ℕ → ℤ} {m : ℕ} (hC : d m = -1 ∨ d m = 0 ∨ d m = 1) (hne : d m ≠ 0)
    (hc : d (m + 1) = -d m) (hmid : b m = -1) (hd : ∀ i < m, d (2 * m + 1 - i) = d i)
    (hb : ∀ i < m, b (2 * m - i) = b i) :
    K d b (2 * m + 2) = X ^ 0 * K (Function.update d m 0) b (m + 1) ^ 2 := by
  have hδ : d (m + 1) * d (m + 1) = 1 := by
    rcases hC with e | e | e
    · rw [hc, e]
      norm_num
    · exact absurd e hne
    · rw [hc, e]
      norm_num
  have hsum : d m + d (m + 1) = 0 := by omega
  rw [K_fold_even d b m (d (m + 1)) hδ (by omega) hmid hd hb, hsum, pow_zero, one_mul]

/-! ### Rigidity modulo 4 as an equivalence, and the descent -/

/-- **Descent, odd size.** For an odd fold, and `k ≥ 1`, the characteristic polynomial is
congruent to `X ^ (2 h + 1)` modulo `2 ^ (k + 1)` if and only if that of the left half is congruent
to `X ^ h` modulo `2 ^ k`. -/
theorem descent_odd {d b : ℕ → ℤ} {h : ℕ} (h0 : d h = 0) (hd : ∀ i < h, d (2 * h - i) = d i)
    (hb : ∀ i, i + 1 < h → b (2 * h - 1 - i) = b i) (hmid : 1 ≤ h → b h = -b (h - 1)) {k : ℕ}
    (hk : 1 ≤ k) :
    (2 : ℤ[X]) ^ (k + 1) ∣ K d b (2 * h + 1) - X ^ (2 * h + 1)
      ↔ (2 : ℤ[X]) ^ k ∣ K d b h - X ^ h := by
  rw [K_of_odd_fold h0 hd hb hmid, show 2 * h + 1 = 1 + 2 * h by ring]
  exact descent (K_monic _ _ _) (K_natDegree _ _ _) 1 hk

/-- **Descent, even size.** For an even fold, and `k ≥ 1`, the characteristic polynomial is
congruent to `X ^ (2 m + 2)` modulo `2 ^ (k + 1)` if and only if that of the left half with last
diagonal entry `0` is congruent to `X ^ (m + 1)` modulo `2 ^ k`. -/
theorem descent_even {d b : ℕ → ℤ} {m : ℕ} (hC : d m = -1 ∨ d m = 0 ∨ d m = 1) (hne : d m ≠ 0)
    (hc : d (m + 1) = -d m) (hmid : b m = -1) (hd : ∀ i < m, d (2 * m + 1 - i) = d i)
    (hb : ∀ i < m, b (2 * m - i) = b i) {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℤ[X]) ^ (k + 1) ∣ K d b (2 * m + 2) - X ^ (2 * m + 2)
      ↔ (2 : ℤ[X]) ^ k ∣ K (Function.update d m 0) b (m + 1) - X ^ (m + 1) := by
  rw [K_of_even_fold hC hne hc hmid hd hb, show 2 * m + 2 = 0 + 2 * (m + 1) by ring]
  exact descent (K_monic _ _ _) (K_natDegree _ _ _) 0 hk

/-- **Rigidity modulo 4, odd size.** A pair in `𝒞_{2h+1}` has characteristic polynomial congruent
to `X ^ (2 h + 1)` modulo `4` if and only if it is the odd fold of a pair which is nilpotent
modulo `2`. -/
theorem mod_four_odd_iff {d b : ℕ → ℤ} {h : ℕ} (hC : InC d b (2 * h + 1)) :
    (4 : ℤ[X]) ∣ K d b (2 * h + 1) - X ^ (2 * h + 1) ↔
      d h = 0 ∧ (∀ i < h, d (2 * h - i) = d i) ∧ (∀ i, i + 1 < h → b (2 * h - 1 - i) = b i)
        ∧ (1 ≤ h → b h = -b (h - 1)) ∧ (2 : ℤ[X]) ∣ K d b h - X ^ h := by
  refine ⟨rigid_odd hC, ?_⟩
  rintro ⟨h0, hd, hb, hmid, hhalf⟩
  have h := (descent_odd h0 hd hb hmid (le_refl 1)).mpr (by rwa [pow_one])
  norm_num at h
  exact h

/-- **Rigidity modulo 4, even size.** A pair in `𝒞_{2m+2}` has characteristic polynomial
congruent to `X ^ (2 m + 2)` modulo `4` if and only if it is the even fold of a pair which is
nilpotent modulo `2`. -/
theorem mod_four_even_iff {d b : ℕ → ℤ} {m : ℕ} (hC : InC d b (2 * m + 2)) :
    (4 : ℤ[X]) ∣ K d b (2 * m + 2) - X ^ (2 * m + 2) ↔
      d m ≠ 0 ∧ d (m + 1) = -d m ∧ b m = -1 ∧ (∀ i < m, d (2 * m + 1 - i) = d i)
        ∧ (∀ i < m, b (2 * m - i) = b i)
        ∧ (2 : ℤ[X]) ∣ K (Function.update d m 0) b (m + 1) - X ^ (m + 1) := by
  refine ⟨rigid_even hC, ?_⟩
  rintro ⟨hne, hc, hmid, hd, hb, hhalf⟩
  have h := (descent_even (hC.1 m (by omega)) hne hc hmid hd hb (le_refl 1)).mpr
    (by rwa [pow_one])
  norm_num at h
  exact h

/-! ### Nilpotent pairs -/

/-- **Classification, odd size.** A pair in `𝒞_{2h+1}` is nilpotent if and only if it is the odd
fold of a nilpotent pair. -/
theorem nil_odd_iff {d b : ℕ → ℤ} {h : ℕ} (hC : InC d b (2 * h + 1)) :
    K d b (2 * h + 1) = X ^ (2 * h + 1) ↔
      d h = 0 ∧ (∀ i < h, d (2 * h - i) = d i) ∧ (∀ i, i + 1 < h → b (2 * h - 1 - i) = b i)
        ∧ (1 ≤ h → b h = -b (h - 1)) ∧ K d b h = X ^ h := by
  constructor
  · intro hK
    obtain ⟨h0, hd, hb, hmid, -⟩ := rigid_odd hC (by rw [hK, sub_self]; exact dvd_zero _)
    refine ⟨h0, hd, hb, hmid, ?_⟩
    have hfold := K_of_odd_fold h0 hd hb hmid
    rw [hK] at hfold
    refine eq_X_pow_of_sq_eq (K_monic _ _ _) ?_
    apply mul_left_cancel₀ (pow_ne_zero 1 (X_ne_zero (R := ℤ)))
    rw [← hfold]
    ring
  · rintro ⟨h0, hd, hb, hmid, hK⟩
    rw [K_of_odd_fold h0 hd hb hmid, hK]
    ring

/-- **Classification, even size.** A pair in `𝒞_{2m+2}` is nilpotent if and only if it is the even
fold of a nilpotent pair whose last diagonal entry is `0`. -/
theorem nil_even_iff {d b : ℕ → ℤ} {m : ℕ} (hC : InC d b (2 * m + 2)) :
    K d b (2 * m + 2) = X ^ (2 * m + 2) ↔
      d m ≠ 0 ∧ d (m + 1) = -d m ∧ b m = -1 ∧ (∀ i < m, d (2 * m + 1 - i) = d i)
        ∧ (∀ i < m, b (2 * m - i) = b i)
        ∧ K (Function.update d m 0) b (m + 1) = X ^ (m + 1) := by
  constructor
  · intro hK
    obtain ⟨hne, hc, hmid, hd, hb, -⟩ := rigid_even hC (by rw [hK, sub_self]; exact dvd_zero _)
    refine ⟨hne, hc, hmid, hd, hb, ?_⟩
    have hfold := K_of_even_fold (hC.1 m (by omega)) hne hc hmid hd hb
    rw [hK, pow_zero, one_mul] at hfold
    refine eq_X_pow_of_sq_eq (K_monic _ _ _) ?_
    rw [← hfold]
    ring
  · rintro ⟨hne, hc, hmid, hd, hb, hK⟩
    rw [K_of_even_fold (hC.1 m (by omega)) hne hc hmid hd hb, hK]
    ring

/-- **Nilpotency modulo powers of two.** A pair in `𝒞_n` whose characteristic polynomial is
congruent to `X ^ n` modulo `2 ^ (⌊log₂ n⌋ + 1)` is nilpotent. -/
theorem nil_of_congr (n : ℕ) : ∀ {d b : ℕ → ℤ}, 1 ≤ n → InC d b n →
    (2 : ℤ[X]) ^ (Nat.log 2 n + 1) ∣ K d b n - X ^ n → K d b n = X ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d b hn hC hdiv
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · -- size 1: the single diagonal entry is even, hence zero
      obtain rfl : n = 1 := by omega
      rw [Nat.log_of_lt (by norm_num), zero_add, pow_one] at hdiv
      have h2 := (two_dvd_K_sub_iff d b 1).mp hdiv
      rw [K_one, pow_one] at h2
      have hc : (C ((d 0 : ℤ) : ZMod 2) : (ZMod 2)[X]) = 0 := by linear_combination -h2
      have he := two_dvd_of_cast_eq_zero (C_eq_zero.mp hc)
      have hr := hC.1 0 (by omega)
      have hd0 : d 0 = 0 := by omega
      rw [K_one, hd0, C_0, sub_zero, pow_one]
    · have hlog : Nat.log 2 n = Nat.log 2 (n / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by norm_num) hge
      have h4 : (4 : ℤ[X]) ∣ K d b n - X ^ n := by
        refine dvd_trans ?_ hdiv
        rw [hlog, show Nat.log 2 (n / 2) + 1 + 1 = 2 + Nat.log 2 (n / 2) by omega, pow_add]
        exact ⟨2 ^ Nat.log 2 (n / 2), by norm_num⟩
      rcases Nat.even_or_odd n with hev | hodd
      · -- even size: an even fold
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨n / 2 - 1, by obtain ⟨r, hr⟩ := hev; omega⟩
        obtain ⟨hne, hc, hmid, hd, hb, -⟩ := rigid_even hC h4
        have e : (2 * m + 2) / 2 = m + 1 := by omega
        rw [hlog, e] at hdiv
        have hq := (descent_even (hC.1 m (by omega)) hne hc hmid hd hb (by omega)).mp hdiv
        have hnil := ih (m + 1) (by omega) (by omega) ((hC.mono (by omega)).update_zero m) hq
        rw [K_of_even_fold (hC.1 m (by omega)) hne hc hmid hd hb, hnil]
        ring
      · -- odd size: an odd fold
        obtain ⟨h, rfl⟩ : ∃ h, n = 2 * h + 1 := ⟨n / 2, by obtain ⟨r, hr⟩ := hodd; omega⟩
        obtain ⟨h0, hd, hb, hmid, -⟩ := rigid_odd hC h4
        have e : (2 * h + 1) / 2 = h := by omega
        rw [hlog, e] at hdiv
        have hq := (descent_odd h0 hd hb hmid (by omega)).mp hdiv
        have hnil := ih h (by omega) (by omega) (hC.mono (by omega)) hq
        rw [K_of_odd_fold h0 hd hb hmid, hnil]
        ring

end Tridiagonal
