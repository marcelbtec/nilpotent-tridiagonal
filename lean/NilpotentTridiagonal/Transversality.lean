module

public import NilpotentTridiagonal.Continuant

/-!
# Transversality

For a pair `(d, 1)` of size `n` over a field, with all products equal to `1`, let

  A k = K(positions 0, …, k - 1) * K(positions k + 1, …, n - 1),
  B k = K(positions 0, …, k - 1) * K(positions k + 2, …, n - 1)

be the partial derivatives (up to sign) of the continuant with respect to `d k` and `b k`.

* `mem_Wfull_of_coeff`: the `A k` and `B k` span the polynomials of degree less than `n`.
  The proof is an induction with the three-term recurrence.
* `indep_half`: if `d` is a palindrome, then `A k = A (n - 1 - k)` and `B k = B (n - 2 - k)`, and
  there are no further linear relations: a relation whose coefficients vanish on the left half
  is trivial.
-/

@[expose] public section

open Polynomial Finset

namespace Tridiagonal

variable {F : Type*} [Field F]

/-- The product of the continuants of the positions `0, …, i - 1` and `j, …, n - 1`. -/
noncomputable def Mm (d : ℕ → F) (n i j : ℕ) : F[X] := K d 1 i * K (sh j d) 1 (n - j)

/-- Minus the derivative of the continuant with respect to the diagonal entry `d k`. -/
noncomputable def Aa (d : ℕ → F) (n k : ℕ) : F[X] := K d 1 k * K (sh (k + 1) d) 1 (n - 1 - k)

/-- Minus the derivative of the continuant with respect to the product `b k`. -/
noncomputable def Bb (d : ℕ → F) (n k : ℕ) : F[X] := K d 1 k * K (sh (k + 2) d) 1 (n - 2 - k)

lemma Aa_eq (d : ℕ → F) (n k : ℕ) : Aa d n k = Mm d n k (k + 1) := by
  unfold Aa Mm
  rw [show n - 1 - k = n - (k + 1) by omega]

lemma Bb_eq (d : ℕ → F) (n k : ℕ) : Bb d n k = Mm d n k (k + 2) := by
  unfold Bb Mm
  rw [show n - 2 - k = n - (k + 2) by omega]

/-- The span of all the polynomials `A k` and `B k`. -/
noncomputable def Wfull (d : ℕ → F) (n : ℕ) : Submodule F F[X] :=
  Submodule.span F ({p | ∃ k < n, p = Aa d n k} ∪ {p | ∃ k, k + 1 < n ∧ p = Bb d n k})

/-- The three-term recurrence for the continuants of the last positions. -/
lemma Mm_rec (d : ℕ → F) (n i j : ℕ) (hj : j + 2 ≤ n) :
    Mm d n i (j + 2) = (X - C (d j)) * Mm d n i (j + 1) - Mm d n i j := by
  have hl := K_succ_succ_left (sh j d) 1 (n - (j + 2))
  rw [sh_sh, sh_sh, sh_one, sh_one] at hl
  simp only [Pi.one_apply, C_1, one_mul, sh_apply, zero_add] at hl
  rw [show n - (j + 2) + 2 = n - j by omega, show n - (j + 2) + 1 = n - (j + 1) by omega,
    show 1 + j = j + 1 by omega, show 2 + j = j + 2 by omega] at hl
  unfold Mm
  rw [hl]
  ring

/-- Every `Mm d n i j` with at least one position between the two blocks lies in the span. -/
lemma Mm_mem (d : ℕ → F) (n : ℕ) : ∀ j, j ≤ n → ∀ i, i + 1 ≤ j → Mm d n i j ∈ Wfull d n := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hij
    rcases Nat.lt_or_ge j (i + 3) with h3 | h3
    · rcases (by omega : j = i + 1 ∨ j = i + 2) with rfl | rfl
      · rw [← Aa_eq]
        exact Submodule.subset_span (Or.inl ⟨i, by omega, rfl⟩)
      · rw [← Bb_eq]
        exact Submodule.subset_span (Or.inr ⟨i, by omega, rfl⟩)
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have hrec := Mm_rec d n i j' hj
      rcases i with _ | i
      · have e : Mm d n 0 (j' + 2)
            = Mm d n 1 (j' + 1) + (d 0 - d j') • Mm d n 0 (j' + 1) - Mm d n 0 j' := by
          rw [hrec, smul_eq_C_mul, C_sub]
          unfold Mm
          rw [K_one, K_zero]
          ring
        rw [e]
        exact Submodule.sub_mem _ (Submodule.add_mem _ (ih (j' + 1) (by omega) (by omega) 1
          (by omega)) (Submodule.smul_mem _ _ (ih (j' + 1) (by omega) (by omega) 0 (by omega))))
          (ih j' (by omega) (by omega) 0 (by omega))
      · have e : Mm d n (i + 1) (j' + 2)
            = Mm d n (i + 2) (j' + 1) + (d (i + 1) - d j') • Mm d n (i + 1) (j' + 1)
              + Mm d n i (j' + 1) - Mm d n (i + 1) j' := by
          rw [hrec, smul_eq_C_mul, C_sub]
          unfold Mm
          rw [K_succ_succ d 1 i]
          simp only [Pi.one_apply, C_1, one_mul]
          ring
        rw [e]
        exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (ih (j' + 1) (by omega) (by omega) (i + 2) (by omega))
          (Submodule.smul_mem _ _ (ih (j' + 1) (by omega) (by omega) (i + 1) (by omega))))
          (ih (j' + 1) (by omega) (by omega) i (by omega)))
          (ih j' (by omega) (by omega) (i + 1) (by omega))

/-- The continuants of the first `i < n` positions lie in the span. -/
lemma K_mem_Wfull (d : ℕ → F) (n i : ℕ) (hi : i < n) : K d 1 i ∈ Wfull d n := by
  have h := Mm_mem d n n le_rfl i (by omega)
  unfold Mm at h
  rwa [Nat.sub_self, K_zero, mul_one] at h

/-- **Transversality (i).** The polynomials `A k` and `B k` span the polynomials of degree less
than `n`. -/
theorem mem_Wfull_of_coeff (d : ℕ → F) (n : ℕ) : ∀ m, m ≤ n → ∀ f : F[X],
    (∀ j, m ≤ j → f.coeff j = 0) → f ∈ Wfull d n
  | 0, _, f, hf => by
      have : f = 0 := by
        ext j
        rw [coeff_zero]
        exact hf j (Nat.zero_le j)
      rw [this]
      exact Submodule.zero_mem _
  | m + 1, hm, f, hf => by
      have hmon := K_monic d 1 m
      have hdeg := K_natDegree d 1 m
      have hsplit : f = f.coeff m • K d 1 m + (f - f.coeff m • K d 1 m) := by ring
      rw [hsplit]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (K_mem_Wfull d n m (by omega))) ?_
      apply mem_Wfull_of_coeff d n m (by omega)
      intro j hj
      rw [coeff_sub, smul_eq_C_mul, coeff_C_mul]
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · have h1 : (K d 1 m).coeff m = 1 := by
          have := hmon.coeff_natDegree
          rwa [hdeg] at this
        rw [h1, mul_one, sub_self]
      · have h0 : (K d 1 m).coeff j = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hlt)
        rw [hf j (by omega), h0, mul_zero, sub_zero]

/-! ### Palindromes -/

/-- For a palindrome, the continuant of the last `m` positions is that of the first `m`. -/
lemma K_sh_pal {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) (m : ℕ) (hm : m ≤ n) :
    K (sh (n - m) d) 1 m = K d 1 m := by
  rw [← K_reverse d 1 m]
  apply K_congr
  · intro i hi
    simp only [sh_apply]
    exact idx_congr d (hpal (m - 1 - i) (by omega)) (by omega) (by omega)
  · intro i _
    rfl

lemma Aa_pal {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) (k : ℕ) (hk : k < n) :
    Aa d n k = K d 1 k * K d 1 (n - 1 - k) := by
  unfold Aa
  have := K_sh_pal hpal (n - 1 - k) (by omega)
  rw [show n - (n - 1 - k) = k + 1 by omega] at this
  rw [this]

lemma Bb_pal {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) (k : ℕ) (hk : k + 1 < n) :
    Bb d n k = K d 1 k * K d 1 (n - 2 - k) := by
  unfold Bb
  have := K_sh_pal hpal (n - 2 - k) (by omega)
  rw [show n - (n - 2 - k) = k + 2 by omega] at this
  rw [this]

lemma Aa_mirror {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) (k : ℕ) (hk : k < n) :
    Aa d n (n - 1 - k) = Aa d n k := by
  rw [Aa_pal hpal k hk, Aa_pal hpal (n - 1 - k) (by omega),
    show n - 1 - (n - 1 - k) = k by omega, mul_comm]

lemma Bb_mirror {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) (k : ℕ)
    (hk : k + 1 < n) : Bb d n (n - 2 - k) = Bb d n k := by
  rw [Bb_pal hpal k hk, Bb_pal hpal (n - 2 - k) (by omega),
    show n - 2 - (n - 2 - k) = k by omega, mul_comm]

/-- The polynomials `A k` and `B k` on the right half: one representative of each mirror pair. -/
noncomputable def half (d : ℕ → F) (n : ℕ) :
    Fin (n - n / 2) ⊕ Fin (n - 1 - (n - 1) / 2) → F[X]
  | Sum.inl i => Aa d n (n / 2 + i)
  | Sum.inr i => Bb d n ((n - 1) / 2 + i)

lemma Wfull_le_half {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) :
    Wfull d n ≤ Submodule.span F (Set.range (half d n)) := by
  apply Submodule.span_le.mpr
  rintro p (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · rcases Nat.lt_or_ge k (n / 2) with hlt | hge
    · rw [← Aa_mirror hpal k hk]
      refine Submodule.subset_span ⟨Sum.inl ⟨n - 1 - k - n / 2, by omega⟩, ?_⟩
      simp only [half]
      congr 1
      omega
    · refine Submodule.subset_span ⟨Sum.inl ⟨k - n / 2, by omega⟩, ?_⟩
      simp only [half]
      congr 1
      omega
  · rcases Nat.lt_or_ge k ((n - 1) / 2) with hlt | hge
    · rw [← Bb_mirror hpal k hk]
      refine Submodule.subset_span ⟨Sum.inr ⟨n - 2 - k - (n - 1) / 2, by omega⟩, ?_⟩
      simp only [half]
      congr 1
      omega
    · refine Submodule.subset_span ⟨Sum.inr ⟨k - (n - 1) / 2, by omega⟩, ?_⟩
      simp only [half]
      congr 1
      omega

lemma Aa_degree_lt (d : ℕ → F) (n k : ℕ) (hk : k < n) : (Aa d n k).degree < n := by
  refine lt_of_le_of_lt degree_le_natDegree ?_
  unfold Aa
  rw [(K_monic d 1 k).natDegree_mul (K_monic _ _ _), K_natDegree, K_natDegree]
  exact_mod_cast (by omega : k + (n - 1 - k) < n)

lemma Bb_degree_lt (d : ℕ → F) (n k : ℕ) (hk : k + 1 < n) : (Bb d n k).degree < n := by
  refine lt_of_le_of_lt degree_le_natDegree ?_
  unfold Bb
  rw [(K_monic d 1 k).natDegree_mul (K_monic _ _ _), K_natDegree, K_natDegree]
  exact_mod_cast (by omega : k + (n - 2 - k) < n)

lemma half_mem (d : ℕ → F) (n : ℕ) (x : Fin (n - n / 2) ⊕ Fin (n - 1 - (n - 1) / 2)) :
    half d n x ∈ degreeLT F n := by
  rw [mem_degreeLT]
  rcases x with i | i
  · exact Aa_degree_lt d n _ (by omega)
  · exact Bb_degree_lt d n _ (by omega)

/-- The representatives are linearly independent. -/
theorem half_linearIndependent {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) :
    LinearIndependent F (half d n) := by
  -- the family inside the space of polynomials of degree less than `n`
  let v : Fin (n - n / 2) ⊕ Fin (n - 1 - (n - 1) / 2) → degreeLT F n :=
    fun x => ⟨half d n x, half_mem d n x⟩
  have hv : (degreeLT F n).subtype ∘ v = half d n := rfl
  have hspan : ⊤ ≤ Submodule.span F (Set.range v) := by
    rintro ⟨f, hf⟩ -
    have hf' : f ∈ Submodule.span F (Set.range (half d n)) :=
      Wfull_le_half hpal (mem_Wfull_of_coeff d n n le_rfl f
        (fun j hj => (degree_lt_iff_coeff_zero f n).mp (mem_degreeLT.mp hf) j hj))
    rw [← hv, Set.range_comp, ← Submodule.map_span] at hf'
    obtain ⟨y, hy, hyf⟩ := hf'
    have : y = ⟨f, hf⟩ := Subtype.ext hyf
    rwa [this] at hy
  have hcard : Fintype.card (Fin (n - n / 2) ⊕ Fin (n - 1 - (n - 1) / 2))
      = Module.finrank F (degreeLT F n) := by
    rw [(degreeLTEquiv F n).finrank_eq, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  rw [← hv]
  exact hli.map' _ (Submodule.ker_subtype _)

/-- **Transversality (ii).** For a palindrome, a linear relation among the `A k` and `B k` whose
coefficients vanish on the left half is trivial. -/
theorem indep_half {d : ℕ → F} {n : ℕ} (hpal : ∀ i < n, d (n - 1 - i) = d i) (t u : ℕ → F)
    (ht : ∀ k < n / 2, t k = 0) (hu : ∀ k < (n - 1) / 2, u k = 0)
    (hrel : ∑ k ∈ range n, C (t k) * Aa d n k + ∑ k ∈ range (n - 1), C (u k) * Bb d n k = 0) :
    (∀ k < n, t k = 0) ∧ (∀ k < n - 1, u k = 0) := by
  -- restrict both sums to the right half
  have hA : ∑ k ∈ range n, C (t k) * Aa d n k
      = ∑ i : Fin (n - n / 2), t (n / 2 + i) • Aa d n (n / 2 + i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => t (n / 2 + i) • Aa d n (n / 2 + i)) (n - n / 2)]
    conv_lhs => rw [show n = n / 2 + (n - n / 2) by omega, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun k hk => by rw [ht k (Finset.mem_range.mp hk), C_0, zero_mul]),
      zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, show n / 2 + (n - n / 2) = n by omega]
  have hB : ∑ k ∈ range (n - 1), C (u k) * Bb d n k
      = ∑ i : Fin (n - 1 - (n - 1) / 2), u ((n - 1) / 2 + i) • Bb d n ((n - 1) / 2 + i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => u ((n - 1) / 2 + i) • Bb d n ((n - 1) / 2 + i))
      (n - 1 - (n - 1) / 2)]
    conv_lhs => rw [show n - 1 = (n - 1) / 2 + (n - 1 - (n - 1) / 2) by omega,
      Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun k hk => by rw [hu k (Finset.mem_range.mp hk), C_0, zero_mul]),
      zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul]
  let g : Fin (n - n / 2) ⊕ Fin (n - 1 - (n - 1) / 2) → F := fun x =>
    match x with
    | Sum.inl i => t (n / 2 + i)
    | Sum.inr i => u ((n - 1) / 2 + i)
  have hg : ∑ x, g x • half d n x = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [g, half]
    rw [← hA, ← hB]
    exact hrel
  have hzero := Fintype.linearIndependent_iff.mp (half_linearIndependent hpal) g hg
  constructor
  · intro k hk
    rcases Nat.lt_or_ge k (n / 2) with hlt | hge
    · exact ht k hlt
    · have := hzero (Sum.inl ⟨k - n / 2, by omega⟩)
      simp only [g] at this
      rwa [show n / 2 + (k - n / 2) = k by omega] at this
  · intro k hk
    rcases Nat.lt_or_ge k ((n - 1) / 2) with hlt | hge
    · exact hu k hlt
    · have := hzero (Sum.inr ⟨k - (n - 1) / 2, by omega⟩)
      simp only [g] at this
      rwa [show (n - 1) / 2 + (k - (n - 1) / 2) = k by omega] at this

end Tridiagonal
