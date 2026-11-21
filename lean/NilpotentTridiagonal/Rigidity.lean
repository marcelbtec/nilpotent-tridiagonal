module

public import NilpotentTridiagonal.Linearise
public import NilpotentTridiagonal.Congruence

/-!
# Rigidity modulo 4

Let `P = (d, b)` be an integer pair of size `n ≥ 2` with diagonal entries in `{-1, 0, 1}` and
products in `{1, -1}`. If `K d b n ≡ X ^ n` modulo `4`, then `P` is a fold: for odd `n`
(`rigid_odd`) the central diagonal entry vanishes, the two halves are mirror images and the two
central products are opposite; for even `n` (`rigid_even`) the two central diagonal entries are
`-δ, δ` with `δ = ±1`, the central product is `-1`, and the two halves are mirror images otherwise.
In both cases the pair which is folded is nilpotent modulo `2`.

The proof compares `P` with the fold `Q` of its own left half. The pairs `P` and `Q` agree modulo
`2` by the uniqueness of the nilpotent diagonal modulo `2`, both have characteristic polynomial
`X ^ n` modulo `4`, and they agree on the left half. Linearising at `Q` and applying
transversality gives `P ≡ Q` modulo `4` (`agree_mod_four`), and the entries are too small for
this to leave any freedom.
-/

@[expose] public section

open Polynomial Finset

namespace Tridiagonal

/-- The pair `(d, b)` of size `n` lies in `𝒞_n`: its diagonal entries are in `{-1, 0, 1}` and its
products are in `{1, -1}`. -/
def InC (d b : ℕ → ℤ) (n : ℕ) : Prop :=
  (∀ i < n, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧ (∀ i, i + 1 < n → b i = 1 ∨ b i = -1)

/-- **Comparison.** Let `P = (d, b)` and `Q = (dQ, bQ)` be integer pairs of size `n` whose
characteristic polynomials are congruent to `X ^ n` modulo `4`. Suppose that `P ≡ Q` modulo `2`,
that the products of `Q` are odd, that the diagonal of `Q` is a palindrome modulo `2`, and that
`P` and `Q` agree on the left half. Then `P ≡ Q` modulo `4`. -/
lemma agree_mod_four {n : ℕ} {d b dQ bQ : ℕ → ℤ}
    (hP : (4 : ℤ[X]) ∣ K d b n - X ^ n) (hQ : (4 : ℤ[X]) ∣ K dQ bQ n - X ^ n)
    (hd2 : ∀ i < n, (2 : ℤ) ∣ d i - dQ i) (hb2 : ∀ i, i + 1 < n → (2 : ℤ) ∣ b i - bQ i)
    (hbQ : ∀ i, i + 1 < n → ((bQ i : ℤ) : ZMod 2) = 1)
    (hpal : ∀ i < n, ((dQ (n - 1 - i) : ℤ) : ZMod 2) = (dQ i : ZMod 2))
    (hdl : ∀ i < n / 2, d i = dQ i) (hbl : ∀ i < (n - 1) / 2, b i = bQ i) :
    (∀ i < n, (4 : ℤ) ∣ d i - dQ i) ∧ (∀ i, i + 1 < n → (4 : ℤ) ∣ b i - bQ i) := by
  -- half the differences
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℤ, ∀ i < n, d i = dQ i + 2 * x i :=
    ⟨fun i => (d i - dQ i) / 2, fun i hi => by
      have := hd2 i hi
      change d i = dQ i + 2 * ((d i - dQ i) / 2)
      omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℤ, ∀ i, i + 1 < n → b i = bQ i + 2 * y i :=
    ⟨fun i => (b i - bQ i) / 2, fun i hi => by
      have := hb2 i hi
      change b i = bQ i + 2 * ((b i - bQ i) / 2)
      omega⟩
  -- modulo 4, the pair `P` is a perturbation of `Q` by twice `(x, y)`
  have hP4 := (four_dvd_K_sub_iff d b n).mp hP
  have hQ4 := (four_dvd_K_sub_iff dQ bQ n).mp hQ
  have hcongr : K (fun i => (d i : ZMod 4)) (fun i => (b i : ZMod 4)) n
      = K (fun i => (dQ i : ZMod 4) + 2 * (x i : ZMod 4))
          (fun i => (bQ i : ZMod 4) + 2 * (y i : ZMod 4)) n := by
    apply K_congr
    · intro i hi
      show ((d i : ℤ) : ZMod 4) = (dQ i : ZMod 4) + 2 * (x i : ZMod 4)
      rw [hx i hi, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    · intro i hi
      show ((b i : ℤ) : ZMod 4) = (bQ i : ZMod 4) + 2 * (y i : ZMod 4)
      rw [hy i hi, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  have hV4 : C (2 : ZMod 4) * V (fun i => (dQ i : ZMod 4)) (fun i => (bQ i : ZMod 4))
      (fun i => (x i : ZMod 4)) (fun i => (y i : ZMod 4)) n = 0 := by
    have hpert := K_perturb (2 : ZMod 4) (by decide) (fun i => (dQ i : ZMod 4))
      (fun i => (bQ i : ZMod 4)) (fun i => (x i : ZMod 4)) (fun i => (y i : ZMod 4)) n
    rw [← hcongr, hP4, hQ4] at hpert
    linear_combination -hpert
  -- hence the variation is even
  have hVZ : (2 : ℤ[X]) ∣ V dQ bQ x y n := by
    have hC2 : (C (2 : ℤ) : ℤ[X]) = 2 := map_ofNat C 2
    have h4 : (4 : ℤ[X]) ∣ C 2 * V dQ bQ x y n := by
      refine (natCast_dvd_iff_map_eq_zero 4 _).mpr ?_
      rw [Polynomial.map_mul, Polynomial.map_C, V_map]
      simp only [eq_intCast, Int.cast_ofNat]
      exact hV4
    obtain ⟨q, hq⟩ := h4
    refine ⟨q, ?_⟩
    rw [hC2] at hq
    have h2 : (2 : ℤ[X]) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    rw [hq]
    ring
  -- modulo 2 the variation is a combination of the `A k` and `B k`, which vanishes
  have hV2 : V (fun i => (dQ i : ZMod 2)) 1 (fun i => (x i : ZMod 2))
      (fun i => (y i : ZMod 2)) n = 0 := by
    have h := (natCast_dvd_iff_map_eq_zero 2 _).mp hVZ
    rw [V_map] at h
    simp only [eq_intCast] at h
    rw [← V_congr_b (b := fun i => (bQ i : ZMod 2)) (b' := 1) (fun i hi => hbQ i hi)]
    exact h
  have hrel := V_eq_sum (fun i => (dQ i : ZMod 2)) (fun i => (x i : ZMod 2))
    (fun i => (y i : ZMod 2)) n
  rw [hV2] at hrel
  have hrel' : ∑ k ∈ range n, C ((x k : ℤ) : ZMod 2) * Aa (fun i => (dQ i : ZMod 2)) n k
      + ∑ k ∈ range (n - 1), C ((y k : ℤ) : ZMod 2) * Bb (fun i => (dQ i : ZMod 2)) n k = 0 := by
    linear_combination hrel
  -- transversality
  obtain ⟨hx0, hy0⟩ := indep_half (d := fun i => (dQ i : ZMod 2)) hpal
    (fun k => (x k : ZMod 2)) (fun k => (y k : ZMod 2))
    (fun k hk => by
      have h1 := hx k (by omega)
      have h2 := hdl k hk
      have hxk : x k = 0 := by omega
      change ((x k : ℤ) : ZMod 2) = 0
      rw [hxk, Int.cast_zero])
    (fun k hk => by
      have h1 := hy k (by omega)
      have h2 := hbl k hk
      have hyk : y k = 0 := by omega
      change ((y k : ℤ) : ZMod 2) = 0
      rw [hyk, Int.cast_zero])
    hrel'
  constructor
  · intro i hi
    have h1 := two_dvd_of_cast_eq_zero (hx0 i hi)
    have h2 := hx i hi
    omega
  · intro i hi
    have h1 := two_dvd_of_cast_eq_zero (hy0 i (by omega))
    have h2 := hy i hi
    omega

/-! ### Odd size -/

/-- The diagonal of the odd fold of the left half of a pair of size `2 h + 1`. -/
def oddRefD (d : ℕ → ℤ) (h : ℕ) : ℕ → ℤ :=
  fun i => if i < h then d i else if i = h then 0 else d (2 * h - i)

/-- The products of the odd fold of the left half of a pair of size `2 h + 1`. -/
def oddRefB (b : ℕ → ℤ) (h : ℕ) : ℕ → ℤ :=
  fun i => if i < h then b i else if i = h then -b (h - 1) else b (2 * h - 1 - i)

lemma oddRefD_lt (d : ℕ → ℤ) {h i : ℕ} (hi : i < h) : oddRefD d h i = d i := by
  simp [oddRefD, hi]

lemma oddRefD_self (d : ℕ → ℤ) (h : ℕ) : oddRefD d h h = 0 := by
  simp [oddRefD]

lemma oddRefD_gt (d : ℕ → ℤ) {h i : ℕ} (hi : h < i) : oddRefD d h i = d (2 * h - i) := by
  simp [oddRefD, Nat.not_lt.mpr hi.le, hi.ne']

lemma oddRefB_lt (b : ℕ → ℤ) {h i : ℕ} (hi : i < h) : oddRefB b h i = b i := by
  simp [oddRefB, hi]

lemma oddRefB_self (b : ℕ → ℤ) (h : ℕ) : oddRefB b h h = -b (h - 1) := by
  simp [oddRefB]

lemma oddRefB_gt (b : ℕ → ℤ) {h i : ℕ} (hi : h < i) : oddRefB b h i = b (2 * h - 1 - i) := by
  simp [oddRefB, Nat.not_lt.mpr hi.le, hi.ne']

/-- **Rigidity modulo 4, odd size.** A pair in `𝒞_{2h+1}` whose characteristic polynomial is
congruent to `X ^ (2 h + 1)` modulo `4` is the odd fold of its left half, and the left half is
nilpotent modulo `2`. -/
theorem rigid_odd {d b : ℕ → ℤ} {h : ℕ} (hC : InC d b (2 * h + 1))
    (h4 : (4 : ℤ[X]) ∣ K d b (2 * h + 1) - X ^ (2 * h + 1)) :
    d h = 0 ∧ (∀ i < h, d (2 * h - i) = d i) ∧ (∀ i, i + 1 < h → b (2 * h - 1 - i) = b i)
      ∧ (1 ≤ h → b h = -b (h - 1)) ∧ (2 : ℤ[X]) ∣ K d b h - X ^ h := by
  obtain ⟨hdC, hbC⟩ := hC
  -- modulo 2
  have h2 : (2 : ℤ[X]) ∣ K d b (2 * h + 1) - X ^ (2 * h + 1) := dvd_trans ⟨2, by norm_num⟩ h4
  have hb1 : ∀ i, i + 1 < 2 * h + 1 → ((b i : ℤ) : ZMod 2) = 1 :=
    fun i hi => intCast_zmod2_of_unit (hbC i hi)
  have hK2 : K (fun i => (d i : ZMod 2)) 1 (2 * h + 1) = X ^ (2 * h + 1) := by
    rw [← (two_dvd_K_sub_iff d b _).mp h2]
    exact K_congr (fun _ _ => rfl) (fun i hi => (hb1 i hi).symm)
  obtain ⟨hmid, hmir, hhalf⟩ := mod2_odd hK2
  have hhalfZ : (2 : ℤ[X]) ∣ K d b h - X ^ h := by
    rw [two_dvd_K_sub_iff, ← hhalf]
    exact K_congr (fun _ _ => rfl) (fun i hi => hb1 i (by omega))
  -- the reference pair `Q`: the odd fold of the left half
  have hQd : ∀ i < 2 * h + 1, oddRefD d h (2 * h - i) = oddRefD d h i := by
    intro i hi
    rcases Nat.lt_trichotomy i h with hlt | heq | hgt
    · rw [oddRefD_gt d (by omega), oddRefD_lt d hlt]
      congr 1
      omega
    · rw [heq, show 2 * h - h = h by omega]
    · rw [oddRefD_lt d (by omega), oddRefD_gt d hgt]
  have hKQ : K (oddRefD d h) (oddRefB b h) (2 * h + 1) = X * K d b h ^ 2 := by
    rw [K_fold_odd (oddRefD d h) (oddRefB b h) h
      (fun i hi => by
        rw [oddRefD_gt d (by omega), oddRefD_lt d hi]
        congr 1
        omega)
      (fun i hi => by
        rw [oddRefB_gt b (by omega), oddRefB_lt b (by omega)]
        congr 1
        omega)
      (fun hh => by rw [oddRefB_self, oddRefB_lt b (by omega)]),
      oddRefD_self, C_0, sub_zero,
      K_congr (d := oddRefD d h) (d' := d) (b := oddRefB b h) (b' := b) (n := h)
        (fun i hi => oddRefD_lt d hi) (fun i hi => oddRefB_lt b (by omega))]
  have hQ4 : (4 : ℤ[X]) ∣ K (oddRefD d h) (oddRefB b h) (2 * h + 1) - X ^ (2 * h + 1) := by
    obtain ⟨g, hg⟩ := hhalfZ
    refine ⟨X * (g * X ^ h + g ^ 2), ?_⟩
    have : K d b h = X ^ h + 2 * g := by linear_combination hg
    rw [hKQ, this]
    ring
  have hQdC : ∀ i < 2 * h + 1, oddRefD d h i = -1 ∨ oddRefD d h i = 0 ∨ oddRefD d h i = 1 := by
    intro i hi
    rcases Nat.lt_trichotomy i h with hlt | heq | hgt
    · rw [oddRefD_lt d hlt]
      exact hdC i hi
    · rw [heq, oddRefD_self]
      exact Or.inr (Or.inl rfl)
    · rw [oddRefD_gt d hgt]
      exact hdC _ (by omega)
  have hQbC : ∀ i, i + 1 < 2 * h + 1 → oddRefB b h i = 1 ∨ oddRefB b h i = -1 := by
    intro i hi
    rcases Nat.lt_trichotomy i h with hlt | heq | hgt
    · rw [oddRefB_lt b hlt]
      exact hbC i hi
    · rw [heq, oddRefB_self]
      have := hbC (h - 1) (by omega)
      omega
    · rw [oddRefB_gt b hgt]
      exact hbC _ (by omega)
  -- `P ≡ Q` modulo 4
  obtain ⟨hd4, hb4⟩ := agree_mod_four (d := d) (b := b) (dQ := oddRefD d h) (bQ := oddRefB b h)
    h4 hQ4
    (fun i hi => by
      rcases Nat.lt_trichotomy i h with hlt | heq | hgt
      · rw [oddRefD_lt d hlt, sub_self]
        exact dvd_zero _
      · rw [heq, oddRefD_self, sub_zero]
        exact two_dvd_of_cast_eq_zero hmid
      · rw [oddRefD_gt d hgt]
        have := hmir (2 * h - i) (by omega)
        rw [show 2 * h - (2 * h - i) = i by omega] at this
        exact two_dvd_sub_of_cast_eq this)
    (fun i hi => by
      have h1 := hbC i hi
      have h2 := hQbC i hi
      omega)
    (fun i hi => intCast_zmod2_of_unit (hQbC i hi))
    (fun i hi => by rw [show 2 * h + 1 - 1 - i = 2 * h - i by omega, hQd i hi])
    (fun i hi => (oddRefD_lt d (by omega)).symm)
    (fun i hi => (oddRefB_lt b (by omega)).symm)
  -- the entries are too small to differ by a multiple of 4
  have hdeq : ∀ i < 2 * h + 1, d i = oddRefD d h i := fun i hi => by
    have h1 := hd4 i hi
    have h2 := hdC i hi
    have h3 := hQdC i hi
    omega
  have hbeq : ∀ i, i + 1 < 2 * h + 1 → b i = oddRefB b h i := fun i hi => by
    have h1 := hb4 i hi
    have h2 := hbC i hi
    have h3 := hQbC i hi
    omega
  refine ⟨?_, ?_, ?_, ?_, hhalfZ⟩
  · rw [hdeq h (by omega), oddRefD_self]
  · intro i hi
    rw [hdeq (2 * h - i) (by omega), oddRefD_gt d (by omega)]
    congr 1
    omega
  · intro i hi
    rw [hbeq (2 * h - 1 - i) (by omega), oddRefB_gt b (by omega)]
    congr 1
    omega
  · intro hh
    rw [hbeq h (by omega), oddRefB_self]

/-! ### Even size -/

/-- The diagonal of the even fold, with sign `1`, of the left half of a pair of size `2 m + 2`
with its last entry raised by `1`. -/
def evenRefD (d : ℕ → ℤ) (m : ℕ) : ℕ → ℤ :=
  fun i => if i ≤ m then d i else if i = m + 1 then d m + 2 else d (2 * m + 1 - i)

/-- The products of the even fold of the left half of a pair of size `2 m + 2`. -/
def evenRefB (b : ℕ → ℤ) (m : ℕ) : ℕ → ℤ :=
  fun i => if i < m then b i else if i = m then -1 else b (2 * m - i)

lemma evenRefD_le (d : ℕ → ℤ) {m i : ℕ} (hi : i ≤ m) : evenRefD d m i = d i := by
  simp [evenRefD, hi]

lemma evenRefD_succ (d : ℕ → ℤ) (m : ℕ) : evenRefD d m (m + 1) = d m + 2 := by
  simp [evenRefD]

lemma evenRefD_gt (d : ℕ → ℤ) {m i : ℕ} (hi : m + 1 < i) :
    evenRefD d m i = d (2 * m + 1 - i) := by
  simp [evenRefD, Nat.not_le.mpr (by omega : m < i), hi.ne']

lemma evenRefB_lt (b : ℕ → ℤ) {m i : ℕ} (hi : i < m) : evenRefB b m i = b i := by
  simp [evenRefB, hi]

lemma evenRefB_self (b : ℕ → ℤ) (m : ℕ) : evenRefB b m m = -1 := by
  simp [evenRefB]

lemma evenRefB_gt (b : ℕ → ℤ) {m i : ℕ} (hi : m < i) : evenRefB b m i = b (2 * m - i) := by
  simp [evenRefB, Nat.not_lt.mpr hi.le, hi.ne']

/-- **Rigidity modulo 4, even size.** A pair in `𝒞_{2m+2}` whose characteristic polynomial is
congruent to `X ^ (2 m + 2)` modulo `4` is an even fold: its central diagonal entries are
`-δ, δ` with `δ = ±1`, its central product is `-1`, its halves are mirror images otherwise, and
its left half with last diagonal entry `0` is nilpotent modulo `2`. -/
theorem rigid_even {d b : ℕ → ℤ} {m : ℕ} (hC : InC d b (2 * m + 2))
    (h4 : (4 : ℤ[X]) ∣ K d b (2 * m + 2) - X ^ (2 * m + 2)) :
    d m ≠ 0 ∧ d (m + 1) = -d m ∧ b m = -1 ∧ (∀ i < m, d (2 * m + 1 - i) = d i)
      ∧ (∀ i < m, b (2 * m - i) = b i)
      ∧ (2 : ℤ[X]) ∣ K (Function.update d m 0) b (m + 1) - X ^ (m + 1) := by
  obtain ⟨hdC, hbC⟩ := hC
  -- modulo 2
  have h2 : (2 : ℤ[X]) ∣ K d b (2 * m + 2) - X ^ (2 * m + 2) := dvd_trans ⟨2, by norm_num⟩ h4
  have hb1 : ∀ i, i + 1 < 2 * m + 2 → ((b i : ℤ) : ZMod 2) = 1 :=
    fun i hi => intCast_zmod2_of_unit (hbC i hi)
  have hK2 : K (fun i => (d i : ZMod 2)) 1 (2 * m + 2) = X ^ (2 * m + 2) := by
    rw [← (two_dvd_K_sub_iff d b _).mp h2]
    exact K_congr (fun _ _ => rfl) (fun i hi => (hb1 i hi).symm)
  obtain ⟨hpal, hhalf⟩ := mod2_even hK2
  have hhalfZ : (2 : ℤ[X]) ∣ K (Function.update d m (d m + 1)) b (m + 1) - X ^ (m + 1) := by
    rw [two_dvd_K_sub_iff, ← hhalf]
    apply K_congr
    · intro i hi
      show ((Function.update d m (d m + 1) i : ℤ) : ZMod 2)
        = Function.update (fun i => (d i : ZMod 2)) m ((d m : ZMod 2) + 1) i
      rcases eq_or_ne i m with heq | hne
      · rw [heq, Function.update_self, Function.update_self, Int.cast_add, Int.cast_one]
      · rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · intro i hi
      exact hb1 i (by omega)
  -- the reference pair `Q`: the even fold of the left half with last entry raised by 1
  have hKQ : K (evenRefD d m) (evenRefB b m) (2 * m + 2)
      = K (Function.update d m (d m + 1)) b (m + 1) ^ 2 := by
    rw [K_fold_even (evenRefD d m) (evenRefB b m) m 1 (by norm_num)
      (by rw [evenRefD_succ, evenRefD_le d le_rfl]; ring)
      (evenRefB_self b m)
      (fun i hi => by
        rw [evenRefD_gt d (by omega), evenRefD_le d (by omega)]
        congr 1
        omega)
      (fun i hi => by
        rw [evenRefB_gt b (by omega), evenRefB_lt b hi]
        congr 1
        omega)]
    congr 1
    apply K_congr
    · intro i hi
      rcases eq_or_ne i m with heq | hne
      · rw [heq, Function.update_self, Function.update_self, evenRefD_le d le_rfl]
      · rw [Function.update_of_ne hne, Function.update_of_ne hne, evenRefD_le d (by omega)]
    · intro i hi
      exact evenRefB_lt b (by omega)
  have hQ4 : (4 : ℤ[X]) ∣ K (evenRefD d m) (evenRefB b m) (2 * m + 2) - X ^ (2 * m + 2) := by
    obtain ⟨g, hg⟩ := hhalfZ
    refine ⟨g * X ^ (m + 1) + g ^ 2, ?_⟩
    have : K (Function.update d m (d m + 1)) b (m + 1) = X ^ (m + 1) + 2 * g := by
      linear_combination hg
    rw [hKQ, this]
    ring
  have hQbC : ∀ i, i + 1 < 2 * m + 2 → evenRefB b m i = 1 ∨ evenRefB b m i = -1 := by
    intro i hi
    rcases Nat.lt_trichotomy i m with hlt | heq | hgt
    · rw [evenRefB_lt b hlt]
      exact hbC i hi
    · rw [heq, evenRefB_self]
      exact Or.inr rfl
    · rw [evenRefB_gt b hgt]
      exact hbC _ (by omega)
  have hcast2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
  -- `P ≡ Q` modulo 4
  obtain ⟨hd4, hb4⟩ := agree_mod_four (d := d) (b := b) (dQ := evenRefD d m)
    (bQ := evenRefB b m) h4 hQ4
    (fun i hi => by
      rcases Nat.lt_trichotomy i (m + 1) with hlt | heq | hgt
      · rw [evenRefD_le d (by omega), sub_self]
        exact dvd_zero _
      · rw [heq, evenRefD_succ]
        have := hpal m (by omega)
        rw [show 2 * m + 1 - m = m + 1 by omega] at this
        have := two_dvd_sub_of_cast_eq this
        omega
      · rw [evenRefD_gt d hgt]
        have := hpal (2 * m + 1 - i) (by omega)
        rw [show 2 * m + 1 - (2 * m + 1 - i) = i by omega] at this
        exact two_dvd_sub_of_cast_eq this)
    (fun i hi => by
      have h1 := hbC i hi
      have h2 := hQbC i hi
      omega)
    (fun i hi => intCast_zmod2_of_unit (hQbC i hi))
    (fun i hi => by
      rw [show 2 * m + 2 - 1 - i = 2 * m + 1 - i by omega]
      rcases Nat.lt_trichotomy i m with hlt | heq | hgt
      · rw [evenRefD_gt d (by omega), evenRefD_le d hlt.le,
          show 2 * m + 1 - (2 * m + 1 - i) = i by omega]
      · rw [heq, show 2 * m + 1 - m = m + 1 by omega, evenRefD_succ, evenRefD_le d le_rfl,
          Int.cast_add, hcast2, add_zero]
      · rcases Nat.eq_or_lt_of_le hgt with heq | hgt'
        · rw [← heq, show 2 * m + 1 - (m + 1) = m by omega, evenRefD_succ,
            evenRefD_le d le_rfl, Int.cast_add, hcast2, add_zero]
        · rw [evenRefD_le d (by omega), evenRefD_gt d hgt'])
    (fun i hi => (evenRefD_le d (by omega)).symm)
    (fun i hi => (evenRefB_lt b (by omega)).symm)
  -- the centre
  have hc := hd4 (m + 1) (by omega)
  rw [evenRefD_succ] at hc
  have hdm := hdC m (by omega)
  have hdm1 := hdC (m + 1) (by omega)
  have hbm := hb4 m (by omega)
  rw [evenRefB_self] at hbm
  have hbmC := hbC m (by omega)
  have hdm_ne : d m ≠ 0 := by omega
  refine ⟨hdm_ne, by omega, by omega, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := hd4 (2 * m + 1 - i) (by omega)
    rw [evenRefD_gt d (by omega), show 2 * m + 1 - (2 * m + 1 - i) = i by omega] at h1
    have h2 := hdC (2 * m + 1 - i) (by omega)
    have h3 := hdC i (by omega)
    omega
  · intro i hi
    have h1 := hb4 (2 * m - i) (by omega)
    rw [evenRefB_gt b (by omega), show 2 * m - (2 * m - i) = i by omega] at h1
    have h2 := hbC (2 * m - i) (by omega)
    have h3 := hbC i (by omega)
    omega
  · have hodd : ((d m : ℤ) : ZMod 2) = 1 := intCast_zmod2_of_unit (by omega)
    rw [two_dvd_K_sub_iff, ← hhalf]
    apply K_congr
    · intro i hi
      show ((Function.update d m 0 i : ℤ) : ZMod 2)
        = Function.update (fun i => (d i : ZMod 2)) m ((d m : ZMod 2) + 1) i
      rcases eq_or_ne i m with heq | hne
      · rw [heq, Function.update_self, Function.update_self, hodd, Int.cast_zero]
        decide
      · rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · intro i hi
      exact hb1 i (by omega)

end Tridiagonal
