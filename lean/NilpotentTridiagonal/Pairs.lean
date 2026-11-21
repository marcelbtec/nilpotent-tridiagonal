module

public import NilpotentTridiagonal.Classification
public import NilpotentTridiagonal.Folded

/-!
# The classification for pairs of lists

A pair of lists `(d, b)` of integers, with `d` of length `n` and `b` of length `n - 1`, has a
characteristic polynomial `charPoly d b`. We prove that the nilpotent pairs with entries in
`{-1, 0, 1}` and products in `{1, -1}` are exactly the pairs obtained from `((0), ())` by folds
(`folded_iff`).
-/

@[expose] public section

open Polynomial

namespace Tridiagonal

/-- The sequence obtained by extending a list by zeros. -/
def seqOf (l : List ℤ) : ℕ → ℤ := fun i => l.getD i 0

/-- The characteristic polynomial of the pair of lists `(d, b)`. -/
noncomputable def charPoly (d b : List ℤ) : ℤ[X] := K (seqOf d) (seqOf b) d.length

/-- The pair of lists `(d, b)` lies in `𝒞_n`, where `n` is the length of `d`: there are `n - 1`
products, the diagonal entries are in `{-1, 0, 1}` and the products are in `{1, -1}`. -/
def IsPair (d b : List ℤ) : Prop :=
  b.length + 1 = d.length ∧ (∀ x ∈ d, x = -1 ∨ x = 0 ∨ x = 1) ∧ (∀ x ∈ b, x = 1 ∨ x = -1)

/-! ### Entries of lists -/

lemma seqOf_fold1_lt (l r : List ℤ) (x : ℤ) {i : ℕ} (hi : i < l.length) :
    seqOf (l ++ x :: r) i = seqOf l i := by
  unfold seqOf
  grind

lemma seqOf_fold1_eq (l r : List ℤ) (x : ℤ) {i : ℕ} (hi : i = l.length) :
    seqOf (l ++ x :: r) i = x := by
  unfold seqOf
  grind

lemma seqOf_fold1_gt (l r : List ℤ) (x : ℤ) {i : ℕ} (hi : l.length < i) :
    seqOf (l ++ x :: r) i = seqOf r (i - l.length - 1) := by
  unfold seqOf
  grind

lemma seqOf_fold2_lt (l r : List ℤ) (x y : ℤ) {i : ℕ} (hi : i < l.length) :
    seqOf (l ++ x :: y :: r) i = seqOf l i :=
  seqOf_fold1_lt l _ x hi

lemma seqOf_fold2_eq (l r : List ℤ) (x y : ℤ) {i : ℕ} (hi : i = l.length) :
    seqOf (l ++ x :: y :: r) i = x :=
  seqOf_fold1_eq l _ x hi

lemma seqOf_fold2_eq' (l r : List ℤ) (x y : ℤ) {i : ℕ} (hi : i = l.length + 1) :
    seqOf (l ++ x :: y :: r) i = y := by
  unfold seqOf
  grind

lemma seqOf_fold2_gt (l r : List ℤ) (x y : ℤ) {i : ℕ} (hi : l.length + 1 < i) :
    seqOf (l ++ x :: y :: r) i = seqOf r (i - l.length - 2) := by
  unfold seqOf
  grind

lemma seqOf_reverse (l : List ℤ) {j : ℕ} (hj : j < l.length) :
    seqOf l.reverse j = seqOf l (l.length - 1 - j) :=
  congrFun (List.getD_reverse j hj) 0

lemma seqOf_take (l : List ℤ) {h i : ℕ} (hi : i < h) : seqOf (l.take h) i = seqOf l i := by
  unfold seqOf
  grind

lemma seqOf_mem (l : List ℤ) {i : ℕ} (hi : i < l.length) : seqOf l i ∈ l := by
  unfold seqOf
  rw [List.getD_eq_getElem l 0 hi]
  exact List.getElem_mem hi

/-- Two lists of the same length with the same entries are equal. -/
lemma ext_seqOf {l l' : List ℤ} (hlen : l.length = l'.length)
    (h : ∀ i < l.length, seqOf l i = seqOf l' i) : l = l' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  unfold seqOf at this
  rwa [List.getD_eq_getElem l 0 h1, List.getD_eq_getElem l' 0 h2] at this

lemma IsPair.inC {d b : List ℤ} (h : IsPair d b) : InC (seqOf d) (seqOf b) d.length := by
  obtain ⟨hlen, hd, hb⟩ := h
  exact ⟨fun i hi => hd _ (seqOf_mem d hi), fun i hi => hb _ (seqOf_mem b (by omega))⟩

lemma Folded.isPair {d b : List ℤ} (h : Folded d b) : IsPair d b :=
  ⟨h.length_eq, h.diag_mem, h.off_mem⟩

/-! ### Folded pairs are nilpotent -/

/-- Folded pairs are nilpotent. -/
theorem charPoly_of_folded {d b : List ℤ} (h : Folded d b) : charPoly d b = X ^ d.length := by
  induction h with
  | base => simp [charPoly, seqOf]
  | @odd d b ε hp hε ih =>
      have hlen := hp.length_eq
      have hL : (d ++ 0 :: d.reverse).length = 2 * d.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_reverse]
        omega
      unfold charPoly at ih ⊢
      rw [hL, K_of_odd_fold (d := seqOf (d ++ 0 :: d.reverse))
        (b := seqOf (b ++ ε :: -ε :: b.reverse)) (h := d.length)
        (seqOf_fold1_eq d _ 0 rfl)
        (fun i hi => by
          rw [seqOf_fold1_gt d _ 0 (by omega), seqOf_reverse d (by omega),
            seqOf_fold1_lt d _ 0 hi]
          congr 1
          omega)
        (fun i hi => by
          rw [seqOf_fold2_gt b _ ε (-ε) (by omega), seqOf_reverse b (by omega),
            seqOf_fold2_lt b _ ε (-ε) (by omega)]
          congr 1
          omega)
        (fun hh => by
          rw [seqOf_fold2_eq' b _ ε (-ε) (by omega), seqOf_fold2_eq b _ ε (-ε) (by omega)]),
        K_congr (d' := seqOf d) (b' := seqOf b)
          (fun i hi => seqOf_fold1_lt d _ 0 hi)
          (fun i hi => seqOf_fold2_lt b _ ε (-ε) (by omega)), ih]
      ring
  | @even d b δ hp hδ ih =>
      have hlen := hp.length_eq
      rw [List.length_append, List.length_singleton] at hlen
      have hL : (d ++ -δ :: δ :: d.reverse).length = 2 * d.length + 2 := by
        simp only [List.length_append, List.length_cons, List.length_reverse]
        omega
      unfold charPoly at ih ⊢
      rw [List.length_append, List.length_singleton] at ih
      have hDm : seqOf (d ++ -δ :: δ :: d.reverse) d.length = -δ :=
        seqOf_fold2_eq d _ (-δ) δ rfl
      have hDm1 : seqOf (d ++ -δ :: δ :: d.reverse) (d.length + 1) = δ :=
        seqOf_fold2_eq' d _ (-δ) δ rfl
      rw [hL, K_of_even_fold (d := seqOf (d ++ -δ :: δ :: d.reverse))
        (b := seqOf (b ++ -1 :: b.reverse)) (m := d.length)
        (by rw [hDm]; omega) (by rw [hDm]; omega) (by rw [hDm, hDm1]; omega)
        (seqOf_fold1_eq b _ (-1) (by omega))
        (fun i hi => by
          rw [seqOf_fold2_gt d _ (-δ) δ (by omega), seqOf_reverse d (by omega),
            seqOf_fold2_lt d _ (-δ) δ hi]
          congr 1
          omega)
        (fun i hi => by
          rw [seqOf_fold1_gt b _ (-1) (by omega), seqOf_reverse b (by omega),
            seqOf_fold1_lt b _ (-1) (by omega)]
          congr 1
          omega),
        K_congr (d' := seqOf (d ++ [0])) (b' := seqOf b)
          (fun i hi => by
            rcases eq_or_ne i d.length with heq | hne
            · rw [heq, Function.update_self, seqOf_fold1_eq d [] 0 rfl]
            · rw [Function.update_of_ne hne, seqOf_fold2_lt d _ (-δ) δ (by omega),
                seqOf_fold1_lt d [] 0 (by omega)])
          (fun i hi => seqOf_fold1_lt b _ (-1) (by omega)), ih]
      ring

/-! ### Nilpotent pairs are folded -/

/-- Nilpotent pairs are folded. -/
theorem folded_of_charPoly (n : ℕ) : ∀ {d b : List ℤ}, d.length = n → IsPair d b →
    charPoly d b = X ^ d.length → Folded d b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d b hn hP hK
    have hC := hP.inC
    obtain ⟨hlen, hdm, hbm⟩ := hP
    unfold charPoly at hK
    rw [hn] at hK hC
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · -- size 1
      have hn1 : d.length = 1 := by omega
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hn1
      have hb0 : b = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      have hn' : n = 1 := by omega
      rw [hn', K_one, pow_one] at hK
      have hx : seqOf [x] 0 = x := rfl
      rw [hx] at hK
      have hC0 : (C x : ℤ[X]) = 0 := by linear_combination -hK
      rw [C_eq_zero.mp hC0, hb0]
      exact Folded.base
    · rcases Nat.even_or_odd n with hev | hodd
      · -- even size
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨n / 2 - 1, by obtain ⟨r, hr⟩ := hev; omega⟩
        obtain ⟨hne, hc, hmid, hd, hb, hKh⟩ := (nil_even_iff hC).mp hK
        obtain ⟨δ, hδ⟩ : ∃ δ, δ = seqOf d (m + 1) := ⟨_, rfl⟩
        obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ = d.take m := ⟨_, rfl⟩
        obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = b.take m := ⟨_, rfl⟩
        have hd₀len : d₀.length = m := by rw [hd₀, List.length_take]; omega
        have hb₁len : b₁.length = m := by rw [hb₁, List.length_take]; omega
        have hd₀get : ∀ i < m, seqOf d₀ i = seqOf d i := fun i hi => by
          rw [hd₀, seqOf_take d hi]
        have hb₁get : ∀ i < m, seqOf b₁ i = seqOf b i := fun i hi => by
          rw [hb₁, seqOf_take b hi]
        have hdm' := hC.1 m (by omega)
        have hδ1 : δ = 1 ∨ δ = -1 := by omega
        -- the two lists are folds
        have hdeq : d = d₀ ++ -δ :: δ :: d₀.reverse := by
          apply ext_seqOf
          · simp only [List.length_append, List.length_cons, List.length_reverse]
            omega
          · intro i hi
            rcases Nat.lt_trichotomy i m with h1 | h1 | h1
            · rw [seqOf_fold2_lt d₀ _ (-δ) δ (by omega), hd₀get i h1]
            · rw [seqOf_fold2_eq d₀ _ (-δ) δ (by omega), h1]
              omega
            · rcases Nat.lt_or_ge i (m + 2) with h2 | h2
              · have h3 : i = m + 1 := by omega
                rw [seqOf_fold2_eq' d₀ _ (-δ) δ (by omega), hδ, h3]
              · rw [seqOf_fold2_gt d₀ _ (-δ) δ (by omega), seqOf_reverse d₀ (by omega),
                  hd₀get _ (by omega)]
                have := hd (2 * m + 1 - i) (by omega)
                rw [show 2 * m + 1 - (2 * m + 1 - i) = i by omega] at this
                rw [this]
                congr 1
                omega
        have hbeq : b = b₁ ++ -1 :: b₁.reverse := by
          apply ext_seqOf
          · simp only [List.length_append, List.length_cons, List.length_reverse]
            omega
          · intro i hi
            rcases Nat.lt_trichotomy i m with h1 | h1 | h1
            · rw [seqOf_fold1_lt b₁ _ (-1) (by omega), hb₁get i h1]
            · rw [seqOf_fold1_eq b₁ _ (-1) (by omega), h1, hmid]
            · rw [seqOf_fold1_gt b₁ _ (-1) (by omega), seqOf_reverse b₁ (by omega),
                hb₁get _ (by omega)]
              have := hb (2 * m - i) (by omega)
              rw [show 2 * m - (2 * m - i) = i by omega] at this
              rw [this]
              congr 1
              omega
        -- the pair which is folded is nilpotent, hence folded by induction
        have hF : Folded (d₀ ++ [0]) b₁ := by
          refine ih (m + 1) (by omega) (by simp [hd₀len]) ⟨by simp [hd₀len, hb₁len], ?_, ?_⟩ ?_
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hdm x (List.mem_of_mem_take (hd₀ ▸ hx))
            · exact Or.inr (Or.inl (List.mem_singleton.mp hx))
          · intro x hx
            exact hbm x (List.mem_of_mem_take (hb₁ ▸ hx))
          · unfold charPoly
            rw [List.length_append, List.length_singleton, hd₀len, ← hKh]
            apply K_congr
            · intro i hi
              rcases eq_or_ne i m with heq | hne'
              · rw [heq, Function.update_self, seqOf_fold1_eq d₀ [] 0 (by omega)]
              · rw [Function.update_of_ne hne', seqOf_fold1_lt d₀ [] 0 (by omega),
                  hd₀get i (by omega)]
            · intro i hi
              exact hb₁get i (by omega)
        rw [hdeq, hbeq]
        exact Folded.even hF hδ1
      · -- odd size
        obtain ⟨h, rfl⟩ : ∃ h, n = 2 * h + 1 := ⟨n / 2, by obtain ⟨r, hr⟩ := hodd; omega⟩
        obtain ⟨h0, hd, hb, hmid, hKh⟩ := (nil_odd_iff hC).mp hK
        obtain ⟨ε, hε⟩ : ∃ ε, ε = seqOf b (h - 1) := ⟨_, rfl⟩
        obtain ⟨d₁, hd₁⟩ : ∃ d₁, d₁ = d.take h := ⟨_, rfl⟩
        obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = b.take (h - 1) := ⟨_, rfl⟩
        have hd₁len : d₁.length = h := by rw [hd₁, List.length_take]; omega
        have hb₁len : b₁.length = h - 1 := by rw [hb₁, List.length_take]; omega
        have hd₁get : ∀ i < h, seqOf d₁ i = seqOf d i := fun i hi => by
          rw [hd₁, seqOf_take d hi]
        have hb₁get : ∀ i < h - 1, seqOf b₁ i = seqOf b i := fun i hi => by
          rw [hb₁, seqOf_take b hi]
        have hε1 : ε = 1 ∨ ε = -1 := by
          rw [hε]
          exact hC.2 (h - 1) (by omega)
        have hmid' := hmid (by omega)
        have hdeq : d = d₁ ++ 0 :: d₁.reverse := by
          apply ext_seqOf
          · simp only [List.length_append, List.length_cons, List.length_reverse]
            omega
          · intro i hi
            rcases Nat.lt_trichotomy i h with h1 | h1 | h1
            · rw [seqOf_fold1_lt d₁ _ 0 (by omega), hd₁get i h1]
            · rw [seqOf_fold1_eq d₁ _ 0 (by omega), h1, h0]
            · rw [seqOf_fold1_gt d₁ _ 0 (by omega), seqOf_reverse d₁ (by omega),
                hd₁get _ (by omega)]
              have := hd (2 * h - i) (by omega)
              rw [show 2 * h - (2 * h - i) = i by omega] at this
              rw [this]
              congr 1
              omega
        have hbeq : b = b₁ ++ ε :: -ε :: b₁.reverse := by
          apply ext_seqOf
          · simp only [List.length_append, List.length_cons, List.length_reverse]
            omega
          · intro i hi
            rcases Nat.lt_trichotomy i (h - 1) with h1 | h1 | h1
            · rw [seqOf_fold2_lt b₁ _ ε (-ε) (by omega), hb₁get i h1]
            · rw [seqOf_fold2_eq b₁ _ ε (-ε) (by omega), h1, hε]
            · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
              · rw [seqOf_fold2_eq' b₁ _ ε (-ε) (by omega), hε,
                  show i = h by omega, hmid']
              · rw [seqOf_fold2_gt b₁ _ ε (-ε) (by omega), seqOf_reverse b₁ (by omega),
                  hb₁get _ (by omega)]
                have := hb (2 * h - 1 - i) (by omega)
                rw [show 2 * h - 1 - (2 * h - 1 - i) = i by omega] at this
                rw [this]
                congr 1
                omega
        have hF : Folded d₁ b₁ := by
          refine ih h (by omega) hd₁len ⟨by omega, ?_, ?_⟩ ?_
          · intro x hx
            exact hdm x (List.mem_of_mem_take (hd₁ ▸ hx))
          · intro x hx
            exact hbm x (List.mem_of_mem_take (hb₁ ▸ hx))
          · unfold charPoly
            rw [hd₁len, ← hKh]
            exact K_congr (fun i hi => hd₁get i hi) (fun i hi => hb₁get i (by omega))
        rw [hdeq, hbeq]
        exact Folded.odd hF hε1

/-- **Classification.** The nilpotent pairs in `𝒞_n` are exactly the pairs obtained from
`((0), ())` by folds. -/
theorem folded_iff (d b : List ℤ) :
    Folded d b ↔ IsPair d b ∧ charPoly d b = X ^ d.length :=
  ⟨fun h => ⟨h.isPair, charPoly_of_folded h⟩, fun h => folded_of_charPoly d.length rfl h.1 h.2⟩

end Tridiagonal
