module

public import NilpotentTridiagonal.Folded

/-!
# Sizes and number of folded pairs

We determine the sizes of the folded pairs and count the folded pairs of each size:

* `foldedOfSize_nonempty_iff`: there is a folded pair of size `n` if and only if `n = 1` or
  `3 · 2 ^ j - 1 ≤ n ≤ 2 ^ (j + 2) - 1` for some `j`, that is, if and only if `n` is one of
  `1, 2, 3, 5, 6, 7, 11, …, 15, 23, …, 31, 47, …, 63, …`;
* `foldedOfSize_finite`, `foldedOfSize_ncard`: in that case the number of folded pairs of size `n`
  is `2 ^ ⌊log₂ n⌋`.

Both folds are injective (`oddFold_inj`, `evenFold_inj`). Hence the folded pairs of size `2 h + 1`
with `h ≥ 1` correspond to the folded pairs of size `h` together with a sign (`foldedOfSize_odd`),
and the folded pairs of size `2 h` to the folded pairs of size `h` whose last diagonal entry is `0`
together with a sign (`foldedOfSize_even`). Whether the last diagonal entry is `0` depends only on
the size: the first and the last diagonal entry of a folded pair of size `n` are `0` if and only if
`n = 1` or the binary expansion of `n` begins with `11` (`ZeroEnds`, `Folded.zeroEnds_iff`).
-/

@[expose] public section

namespace Tridiagonal

/-! ### Arithmetic of the sizes

`omega` treats the powers `2 ^ j` as unknown numbers, so the proofs supply the relations between
the powers that they need. -/

/-- `ZeroEnds n` says that `n = 1` or that the binary expansion of `n` begins with `11`, that is,
`n` is one of `1, 3, 6, 7, 12, …, 15, 24, …, 31, …`. These are the sizes of the folded pairs whose
first and last diagonal entries are `0` (`Folded.zeroEnds_iff`). -/
def ZeroEnds (n : ℕ) : Prop := n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j ≤ n ∧ n < 4 * 2 ^ j

/-- `Admissible n` says that `n = 1` or `3 · 2 ^ j - 1 ≤ n ≤ 2 ^ (j + 2) - 1` for some `j`. These
are the sizes of the folded pairs (`foldedOfSize_nonempty_iff`). -/
def Admissible (n : ℕ) : Prop := n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j - 1 ≤ n ∧ n ≤ 2 ^ (j + 2) - 1

/-- `Admissible` without subtractions: `n = 1` or `3 · 2 ^ j ≤ n + 1 ≤ 2 ^ (j + 2)` for
some `j`. -/
lemma admissible_iff {n : ℕ} :
    Admissible n ↔ n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j ≤ n + 1 ∧ n + 1 ≤ 4 * 2 ^ j := by
  refine or_congr Iff.rfl (exists_congr fun j => ?_)
  have e : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
  have := Nat.two_pow_pos j
  omega

lemma zeroEnds_one : ZeroEnds 1 := Or.inl rfl

lemma not_zeroEnds_two : ¬ ZeroEnds 2 := by
  rintro (h | ⟨j, h, -⟩)
  · omega
  · have := Nat.two_pow_pos j
    omega

/-- For `h ≥ 1` the size `2 h + 1` is in `ZeroEnds` if and only if `h` is. -/
lemma zeroEnds_odd {h : ℕ} (hh : 1 ≤ h) : ZeroEnds (2 * h + 1) ↔ ZeroEnds h := by
  constructor
  · rintro (h1 | ⟨_ | j, h1, h2⟩)
    · omega
    · exact Or.inl (by omega)
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j, by omega, by omega⟩
  · rintro (rfl | ⟨j, h1, h2⟩)
    · exact Or.inr ⟨0, by norm_num, by norm_num⟩
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j + 1, by omega, by omega⟩

/-- For `h ≥ 2` the size `2 h` is in `ZeroEnds` if and only if `h` is. -/
lemma zeroEnds_even {h : ℕ} (hh : 2 ≤ h) : ZeroEnds (2 * h) ↔ ZeroEnds h := by
  constructor
  · rintro (h1 | ⟨_ | j, h1, h2⟩)
    · omega
    · omega
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j, by omega, by omega⟩
  · rintro (rfl | ⟨j, h1, h2⟩)
    · omega
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j + 1, by omega, by omega⟩

/-- The sizes in `ZeroEnds` are admissible. -/
lemma ZeroEnds.admissible {h : ℕ} (hz : ZeroEnds h) : Admissible h := by
  rw [admissible_iff]
  rcases hz with rfl | ⟨j, h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j, by omega, by omega⟩

lemma admissible_one : Admissible 1 := Or.inl rfl

lemma not_admissible_zero : ¬ Admissible 0 := by
  rw [admissible_iff]
  rintro (h | ⟨j, h, -⟩)
  · omega
  · have := Nat.two_pow_pos j
    omega

/-- For `h ≥ 1` the size `2 h + 1` is admissible if and only if `h` is. -/
lemma admissible_odd {h : ℕ} (hh : 1 ≤ h) : Admissible (2 * h + 1) ↔ Admissible h := by
  rw [admissible_iff, admissible_iff]
  constructor
  · rintro (h1 | ⟨_ | j, h1, h2⟩)
    · omega
    · exact Or.inl (by omega)
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j, by omega, by omega⟩
  · rintro (rfl | ⟨j, h1, h2⟩)
    · exact Or.inr ⟨0, by norm_num, by norm_num⟩
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j + 1, by omega, by omega⟩

/-- The size `2 h` is admissible if and only if `h` is in `ZeroEnds`. -/
lemma admissible_even {h : ℕ} : Admissible (2 * h) ↔ ZeroEnds h := by
  rw [admissible_iff]
  constructor
  · rintro (h1 | ⟨_ | j, h1, h2⟩)
    · omega
    · exact Or.inl (by omega)
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j, by omega, by omega⟩
  · rintro (rfl | ⟨j, h1, h2⟩)
    · exact Or.inr ⟨0, by norm_num, by norm_num⟩
    · have e : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      exact Or.inr ⟨j + 1, by omega, by omega⟩

lemma log_two_odd {h : ℕ} (hh : 1 ≤ h) : Nat.log 2 (2 * h + 1) = Nat.log 2 h + 1 := by
  rw [Nat.log_of_one_lt_of_le one_lt_two (by omega), show (2 * h + 1) / 2 = h by omega]

lemma log_two_even {h : ℕ} (hh : 1 ≤ h) : Nat.log 2 (2 * h) = Nat.log 2 h + 1 := by
  rw [Nat.log_of_one_lt_of_le one_lt_two (by omega), Nat.mul_div_cancel_left h two_pos]

/-- Induction on the size along the two folds: a statement holds for all sizes if it holds for `0`
and for `1` and passes from `h ≥ 1` to `2 h + 1` and to `2 h`. -/
lemma size_induction {P : ℕ → Prop} (zero : P 0) (one : P 1)
    (odd : ∀ h, 1 ≤ h → P h → P (2 * h + 1)) (even : ∀ h, 1 ≤ h → P h → P (2 * h)) (n : ℕ) :
    P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨h, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos h with rfl | hh
      · exact zero
      · exact even h hh (ih h (by omega))
    · rcases Nat.eq_zero_or_pos h with rfl | hh
      · exact one
      · exact odd h hh (ih h (by omega))

/-! ### The folds are injective -/

/-- A list `l` followed by a list `m` and by the mirror image of `l` determines `l` and `m`, if the
length of `m` is known. -/
lemma append_append_reverse_inj {α : Type*} {l l' m m' : List α} (hm : m.length = m'.length)
    (h : l ++ (m ++ l.reverse) = l' ++ (m' ++ l'.reverse)) : l = l' ∧ m = m' := by
  have hl : l.length = l'.length := by
    have := congrArg List.length h
    simp only [List.length_append, List.length_reverse] at this
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨h1, (List.append_inj h2 hm).1⟩

/-- The odd fold is injective: the fold determines the pair and the sign. -/
theorem oddFold_inj {d d' b b' : List ℤ} {ε ε' : ℤ}
    (hd : d ++ 0 :: d.reverse = d' ++ 0 :: d'.reverse)
    (hb : b ++ ε :: -ε :: b.reverse = b' ++ ε' :: -ε' :: b'.reverse) :
    d = d' ∧ b = b' ∧ ε = ε' := by
  obtain ⟨h1, -⟩ := append_append_reverse_inj (m := [0]) (m' := [0]) rfl hd
  obtain ⟨h2, h3⟩ := append_append_reverse_inj (m := [ε, -ε]) (m' := [ε', -ε']) rfl hb
  exact ⟨h1, h2, (List.cons.inj h3).1⟩

/-- The even fold is injective: the fold determines the pair and the sign. -/
theorem evenFold_inj {d d' b b' : List ℤ} {δ δ' : ℤ}
    (hd : d ++ -δ :: δ :: d.reverse = d' ++ -δ' :: δ' :: d'.reverse)
    (hb : b ++ -1 :: b.reverse = b' ++ -1 :: b'.reverse) :
    d = d' ∧ b = b' ∧ δ = δ' := by
  obtain ⟨h1, h3⟩ := append_append_reverse_inj (m := [-δ, δ]) (m' := [-δ', δ']) rfl hd
  obtain ⟨h2, -⟩ := append_append_reverse_inj (m := [-1]) (m' := [-1]) rfl hb
  exact ⟨h1, h2, (List.cons.inj (List.cons.inj h3).2).1⟩

/-- The odd fold as a map: `oddFold ((d, b), ε)` is the odd fold of the pair `(d, b)` with
sign `ε`. -/
def oddFold (q : (List ℤ × List ℤ) × ℤ) : List ℤ × List ℤ :=
  (q.1.1 ++ 0 :: q.1.1.reverse, q.1.2 ++ q.2 :: -q.2 :: q.1.2.reverse)

/-- The even fold as a map: `evenFold ((d, b), δ)` is the even fold of the pair `((d, 0), b)` with
sign `δ`. -/
def evenFold (q : (List ℤ × List ℤ) × ℤ) : List ℤ × List ℤ :=
  (q.1.1 ++ -q.2 :: q.2 :: q.1.1.reverse, q.1.2 ++ -1 :: q.1.2.reverse)

/-- `snocZero (d, b)` is the pair `((d, 0), b)`. -/
def snocZero (p : List ℤ × List ℤ) : List ℤ × List ℤ := (p.1 ++ [0], p.2)

lemma oddFold_injective : Function.Injective oddFold := by
  rintro ⟨⟨d, b⟩, ε⟩ ⟨⟨d', b'⟩, ε'⟩ h
  obtain ⟨hd, hb⟩ := Prod.mk.inj h
  obtain ⟨rfl, rfl, rfl⟩ := oddFold_inj hd hb
  rfl

lemma evenFold_injective : Function.Injective evenFold := by
  rintro ⟨⟨d, b⟩, δ⟩ ⟨⟨d', b'⟩, δ'⟩ h
  obtain ⟨hd, hb⟩ := Prod.mk.inj h
  obtain ⟨rfl, rfl, rfl⟩ := evenFold_inj hd hb
  rfl

lemma snocZero_injective : Function.Injective snocZero := by
  rintro ⟨d, b⟩ ⟨d', b'⟩ h
  obtain ⟨hd, hb⟩ := Prod.mk.inj h
  obtain rfl : d = d' := List.append_cancel_right hd
  obtain rfl : b = b' := hb
  rfl

/-! ### First and last diagonal entry -/

/-- A non-empty list `l` followed by a list `m` and by the mirror image of `l` ends with the first
entry of `l`. -/
lemma getLast?_append_append_reverse {α : Type*} {l : List α} (hl : l ≠ []) (m : List α) :
    (l ++ (m ++ l.reverse)).getLast? = l.head? := by
  rw [← List.append_assoc, List.getLast?_append_of_ne_nil _ (List.reverse_eq_nil_iff.not.mpr hl),
    List.getLast?_reverse]

/-- The first diagonal entry of a folded pair is `0` if and only if its size is in `ZeroEnds`, and
likewise for the last diagonal entry. -/
lemma Folded.zeroEnds_iff {d b : List ℤ} (h : Folded d b) :
    (d.head? = some 0 ↔ ZeroEnds d.length) ∧ (d.getLast? = some 0 ↔ ZeroEnds d.length) := by
  induction h with
  | base => exact ⟨iff_of_true rfl zeroEnds_one, iff_of_true rfl zeroEnds_one⟩
  | @odd d b ε hp hε ih =>
    -- the odd fold begins and ends with the first entry of `d`
    have h1 : 1 ≤ d.length := by
      have := hp.length_eq
      omega
    have hd : d ≠ [] := List.ne_nil_of_length_pos h1
    have hlen : (d ++ 0 :: d.reverse).length = 2 * d.length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_reverse]
      omega
    have hhead : (d ++ 0 :: d.reverse).head? = d.head? := List.head?_append_of_ne_nil _ hd
    have hlast : (d ++ 0 :: d.reverse).getLast? = d.head? :=
      getLast?_append_append_reverse hd [0]
    rw [hhead, hlast, hlen, zeroEnds_odd h1]
    exact ⟨ih.1, ih.1⟩
  | @even d b δ hp hδ ih =>
    -- the pair `((d, 0), b)` ends with `0`, so its size is in `ZeroEnds` and it begins with `0`
    have hz : ZeroEnds (d ++ [0]).length := ih.2.mp List.getLast?_concat
    have h0 : (d ++ [0]).head? = some 0 := ih.1.mpr hz
    have hlen : (d ++ -δ :: δ :: d.reverse).length = 2 * (d ++ [0]).length := by
      simp only [List.length_append, List.length_cons, List.length_reverse, List.length_nil]
      omega
    rw [hlen]
    rcases eq_or_ne d [] with rfl | hd
    · -- size `2`, which is not in `ZeroEnds`: the diagonal is `(-δ, δ)`
      have hδ0 : δ ≠ 0 := by
        rcases hδ with h | h <;> omega
      simp [not_zeroEnds_two, hδ0]
    · -- larger sizes: the even fold begins and ends with the first entry of `d`, which is `0`
      have h2 : 2 ≤ (d ++ [0]).length := by
        have := List.length_pos_iff.mpr hd
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hhead : (d ++ -δ :: δ :: d.reverse).head? = d.head? :=
        List.head?_append_of_ne_nil _ hd
      have hlast : (d ++ -δ :: δ :: d.reverse).getLast? = d.head? :=
        getLast?_append_append_reverse hd [-δ, δ]
      rw [List.head?_append_of_ne_nil _ hd] at h0
      rw [hhead, hlast, h0, zeroEnds_even h2]
      exact ⟨iff_of_true rfl hz, iff_of_true rfl hz⟩

/-! ### The folded pairs of a given size -/

lemma mem_foldedOfSize {d b : List ℤ} {n : ℕ} :
    (d, b) ∈ FoldedOfSize n ↔ Folded d b ∧ d.length = n := Iff.rfl

lemma mem_preimage_snocZero {d b : List ℤ} {n : ℕ} :
    (d, b) ∈ snocZero ⁻¹' FoldedOfSize n ↔ Folded (d ++ [0]) b ∧ (d ++ [0]).length = n := Iff.rfl

/-- There is no folded pair of size `0`. -/
lemma foldedOfSize_zero : FoldedOfSize 0 = ∅ := by
  ext ⟨d, b⟩
  refine iff_of_false ?_ (Set.notMem_empty _)
  rintro ⟨hf, hlen⟩
  have := hf.length_eq
  omega

/-- The only folded pair of size `1` is `((0), ())`. -/
lemma foldedOfSize_one : FoldedOfSize 1 = {([0], [])} := by
  ext ⟨d, b⟩
  rw [mem_foldedOfSize, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hf, hlen⟩
    cases hf with
    | base => exact ⟨rfl, rfl⟩
    | odd hp hε =>
      -- an odd fold of size `1` would come from a pair of size `0`
      have := hp.length_eq
      simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
      omega
    | even hp hδ =>
      simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
      omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨Folded.base, rfl⟩

/-- The folded pairs of size `2 h + 1` with `h ≥ 1` are the odd folds of the folded pairs of
size `h`. -/
lemma foldedOfSize_odd {h : ℕ} (hh : 1 ≤ h) :
    FoldedOfSize (2 * h + 1) = oddFold '' (FoldedOfSize h ×ˢ {1, -1}) := by
  ext ⟨d, b⟩
  rw [mem_foldedOfSize]
  constructor
  · rintro ⟨hf, hlen⟩
    cases hf with
    | base =>
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | @odd d₀ b₀ ε hp hε =>
      simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
      have hlen₀ : d₀.length = h := by omega
      exact ⟨((d₀, b₀), ε), ⟨⟨hp, hlen₀⟩, hε⟩, rfl⟩
    | even hp hδ =>
      simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
      omega
  · rintro ⟨⟨⟨d₀, b₀⟩, ε⟩, ⟨⟨hf, (hlen : d₀.length = h)⟩, hε⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    refine ⟨Folded.odd hf hε, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_reverse]
    omega

/-- The folded pairs of size `2 h` are the even folds of the folded pairs `((d, 0), b)` of
size `h`. -/
lemma foldedOfSize_even (h : ℕ) :
    FoldedOfSize (2 * h) = evenFold '' ((snocZero ⁻¹' FoldedOfSize h) ×ˢ {1, -1}) := by
  ext ⟨d, b⟩
  rw [mem_foldedOfSize]
  constructor
  · rintro ⟨hf, hlen⟩
    cases hf with
    | base =>
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | odd hp hε =>
      simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
      omega
    | @even d₀ b₀ δ hp hδ =>
      simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
      have hlen₀ : (d₀ ++ [0]).length = h := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      exact ⟨((d₀, b₀), δ), ⟨⟨hp, hlen₀⟩, hδ⟩, rfl⟩
  · rintro ⟨⟨⟨d₀, b₀⟩, δ⟩, ⟨hp, hδ⟩, heq⟩
    obtain ⟨hf, hlen⟩ := mem_preimage_snocZero.mp hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    refine ⟨Folded.even hf hδ, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    simp only [List.length_append, List.length_cons, List.length_reverse]
    omega

/-- If `h` is in `ZeroEnds`, every folded pair of size `h` is of the form `((d, 0), b)`. -/
lemma foldedOfSize_subset_range {h : ℕ} (hz : ZeroEnds h) :
    FoldedOfSize h ⊆ Set.range snocZero := by
  rintro ⟨d, b⟩ ⟨(hf : Folded d b), (rfl : d.length = h)⟩
  obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp (hf.zeroEnds_iff.2.mpr hz)
  exact ⟨(t, b), rfl⟩

lemma ncard_signs : ({1, -1} : Set ℤ).ncard = 2 := Set.ncard_pair (by norm_num)

/-- There is a folded pair of size `2 h + 1` with `h ≥ 1` if and only if there is one of
size `h`. -/
lemma foldedOfSize_odd_nonempty_iff {h : ℕ} (hh : 1 ≤ h) :
    (FoldedOfSize (2 * h + 1)).Nonempty ↔ (FoldedOfSize h).Nonempty := by
  rw [foldedOfSize_odd hh, Set.image_nonempty, Set.prod_nonempty_iff]
  exact and_iff_left (Set.insert_nonempty _ _)

/-- There is a folded pair of size `2 h` if and only if `h` is in `ZeroEnds` and there is a folded
pair of size `h`. -/
lemma foldedOfSize_even_nonempty_iff {h : ℕ} :
    (FoldedOfSize (2 * h)).Nonempty ↔ ZeroEnds h ∧ (FoldedOfSize h).Nonempty := by
  rw [foldedOfSize_even, Set.image_nonempty, Set.prod_nonempty_iff,
    and_iff_left (Set.insert_nonempty _ _)]
  constructor
  · rintro ⟨⟨d, b⟩, hp⟩
    obtain ⟨hf, rfl⟩ := mem_preimage_snocZero.mp hp
    exact ⟨hf.zeroEnds_iff.2.mp List.getLast?_concat, _, hp⟩
  · rintro ⟨hz, p, hp⟩
    obtain ⟨q, rfl⟩ := foldedOfSize_subset_range hz hp
    exact ⟨q, hp⟩

/-- There are twice as many folded pairs of size `2 h + 1` with `h ≥ 1` as of size `h`. -/
lemma foldedOfSize_odd_ncard {h : ℕ} (hh : 1 ≤ h) :
    (FoldedOfSize (2 * h + 1)).ncard = (FoldedOfSize h).ncard * 2 := by
  rw [foldedOfSize_odd hh, Set.ncard_image_of_injective _ oddFold_injective, Set.ncard_prod,
    ncard_signs]

/-- If `h` is in `ZeroEnds`, there are twice as many folded pairs of size `2 h` as of size `h`. -/
lemma foldedOfSize_even_ncard {h : ℕ} (hz : ZeroEnds h) :
    (FoldedOfSize (2 * h)).ncard = (FoldedOfSize h).ncard * 2 := by
  rw [foldedOfSize_even, Set.ncard_image_of_injective _ evenFold_injective, Set.ncard_prod,
    ncard_signs, Set.ncard_preimage_of_injective_subset_range snocZero_injective
      (foldedOfSize_subset_range hz)]

/-! ### Sizes and count -/

/-- **Admissible sizes.** There is a folded pair of size `n` if and only if `n = 1` or
`3 · 2 ^ j - 1 ≤ n ≤ 2 ^ (j + 2) - 1` for some `j`. -/
theorem foldedOfSize_nonempty_iff (n : ℕ) :
    (FoldedOfSize n).Nonempty ↔ n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j - 1 ≤ n ∧ n ≤ 2 ^ (j + 2) - 1 := by
  change (FoldedOfSize n).Nonempty ↔ Admissible n
  induction n using size_induction with
  | zero =>
    rw [foldedOfSize_zero]
    exact iff_of_false Set.not_nonempty_empty not_admissible_zero
  | one =>
    rw [foldedOfSize_one]
    exact iff_of_true (Set.singleton_nonempty _) admissible_one
  | odd h hh ih => rw [foldedOfSize_odd_nonempty_iff hh, admissible_odd hh, ih]
  | even h hh ih =>
    rw [foldedOfSize_even_nonempty_iff, admissible_even, ih]
    exact and_iff_left_of_imp ZeroEnds.admissible

/-- There are only finitely many folded pairs of a given size. -/
theorem foldedOfSize_finite (n : ℕ) : (FoldedOfSize n).Finite := by
  induction n using size_induction with
  | zero =>
    rw [foldedOfSize_zero]
    exact Set.finite_empty
  | one =>
    rw [foldedOfSize_one]
    exact Set.finite_singleton _
  | odd h hh ih =>
    rw [foldedOfSize_odd hh]
    exact (ih.prod (Set.toFinite _)).image _
  | even h hh ih =>
    rw [foldedOfSize_even]
    exact ((ih.preimage snocZero_injective.injOn).prod (Set.toFinite _)).image _

/-- **Count.** If there is a folded pair of size `n`, the number of folded pairs of size `n` is
`2 ^ ⌊log₂ n⌋`. -/
theorem foldedOfSize_ncard {n : ℕ} (hn : (FoldedOfSize n).Nonempty) :
    (FoldedOfSize n).ncard = 2 ^ Nat.log 2 n := by
  induction n using size_induction with
  | zero =>
    rw [foldedOfSize_zero] at hn
    exact absurd hn Set.not_nonempty_empty
  | one => rw [foldedOfSize_one, Set.ncard_singleton, Nat.log_one_right, pow_zero]
  | odd h hh ih =>
    rw [foldedOfSize_odd_nonempty_iff hh] at hn
    rw [foldedOfSize_odd_ncard hh, ih hn, log_two_odd hh, pow_succ]
  | even h hh ih =>
    rw [foldedOfSize_even_nonempty_iff] at hn
    rw [foldedOfSize_even_ncard hn.1, ih hn.2, log_two_even hh, pow_succ]

end Tridiagonal
