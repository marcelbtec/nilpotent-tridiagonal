# Nilpotent tridiagonal matrices with entries in {−1, 0, 1}: the proof

This file contains the proof that is formalised in `lean/`. It covers the classification of the
nilpotent pairs (Theorem A), the rigidity modulo 4 (Theorem B), nilpotency modulo powers of two
(Theorem C) and the admissible sizes with the count (Theorem D). The last section lists, for each
statement, the name of its formal counterpart.

Positions are counted from 1 here, as in the paper. The Lean code counts them from 0.

## 1. Statements

A **pair** of size n over a commutative ring R is a pair (d, b) with d = (d₁, …, dₙ) ∈ Rⁿ and
b = (b₁, …, bₙ₋₁) ∈ Rⁿ⁻¹. Its **characteristic polynomial** χ = χ₍d,b₎ ∈ R[λ] is defined by the
three-term recurrence

    χ₀ = 1,   χ₁ = λ − d₁,   χₖ = (λ − dₖ) χₖ₋₁ − bₖ₋₁ χₖ₋₂   (2 ≤ k ≤ n),   χ = χₙ.

It is the characteristic polynomial det(λ − M) of every tridiagonal matrix M with diagonal d whose
opposite off-diagonal entries aₖ (above the diagonal) and cₖ (below) have the products aₖcₖ = bₖ
(Section 9). The pair is **nilpotent** if χ = λⁿ. Over an integral domain this holds if and only if
M is nilpotent.

Let 𝒞ₙ be the set of the integer pairs of size n with all dₖ ∈ {−1, 0, 1} and all bₖ ∈ {1, −1},
and let 𝒩ₙ ⊆ 𝒞ₙ be the set of the nilpotent ones.

For a pair p = (d, b) of size h and signs ε, δ ∈ {1, −1}, the **odd fold** and the **even fold**
of p are the pairs of sizes 2h + 1 and 2h

    Φ_ε(p) = ((d, 0, rev d), (b, ε, −ε, rev b)),
    Ψ_δ(p) = ((d₁, …, d_{h−1}, d_h − δ, d_h + δ, d_{h−1}, …, d₁), (b, −1, rev b)),

where rev reverses a sequence. The even fold of a pair in 𝒞_h lies in 𝒞_{2h} exactly when d_h = 0.

**Theorem A (classification).** 𝒩₁ = {((0), ())}, and for every h ≥ 1

    𝒩_{2h+1} = { Φ_ε(p) : p ∈ 𝒩_h, ε = ±1 },
    𝒩_{2h}   = { Ψ_δ(p) : p ∈ 𝒩_h with last diagonal entry 0, δ = ±1 }.

The pair p and the sign are determined by the fold.

**Theorem B (rigidity modulo 4).** Let n ≥ 2, h = ⌊n/2⌋ and P ∈ 𝒞ₙ. Then χ_P ≡ λⁿ (mod 4) if and
only if P is a fold of a pair p ∈ 𝒞_h with χ_p ≡ λ^h (mod 2) (the odd fold for odd n, the even fold
for even n). In this case, for every k ≥ 1,

    χ_P ≡ λⁿ (mod 2^{k+1})   if and only if   χ_p ≡ λ^h (mod 2^k).

**Theorem C.** If P ∈ 𝒞ₙ and χ_P ≡ λⁿ modulo 2^{⌊log₂ n⌋ + 1}, then χ_P = λⁿ.

**Theorem D (sizes and count).** 𝒩ₙ is non-empty if and only if n = 1 or
3·2^j − 1 ≤ n ≤ 2^{j+2} − 1 for some j ≥ 0. In that case |𝒩ₙ| = 2^{⌊log₂ n⌋}.

## 2. Continuants

For a pair (d, b) of size n and 1 ≤ i ≤ j ≤ n let χ[i, j] be the characteristic polynomial of the
pair formed by d_i, …, d_j and b_i, …, b_{j−1}, with χ[i, i−1] = 1. Write ℓₖ = χ[1, k] and
rₖ = χ[k, n], so that χ = ℓₙ = r₁ and ℓ₀ = r_{n+1} = 1. The following hold over every commutative
ring; each is proved by induction on the size from the recurrence.

1. **Dependence.** χ depends only on d₁, …, dₙ and b₁, …, bₙ₋₁, and it is monic of degree n.
2. **Splitting at an edge.** χ = ℓₖ r_{k+1} − bₖ ℓ_{k−1} r_{k+2} for 1 ≤ k ≤ n − 1.
3. **Recurrence from the left.** rₖ = (λ − dₖ) r_{k+1} − bₖ r_{k+2}.
4. **Reversal.** The pair (rev d, rev b) has the same characteristic polynomial.
5. **Affine dependence on one entry.** Replacing dₖ by dₖ + t lowers χ by t ℓ_{k−1} r_{k+1}, and
   replacing bₖ by bₖ + t lowers χ by t ℓ_{k−1} r_{k+2}.
6. **Base change.** χ commutes with ring homomorphisms.

We put Aₖ = ℓ_{k−1} r_{k+1} (1 ≤ k ≤ n) and Bₖ = ℓ_{k−1} r_{k+2} (1 ≤ k ≤ n − 1).

## 3. The folding identities

**Lemma 1 (odd fold).** Let (D, B) be a pair of size 2h + 1 whose two halves are mirror images,
D_{2h+2−k} = D_k and B_{2h+1−k} = B_k for k ≤ h (k < h for B), and whose central products are
opposite, B_{h+1} = −B_h. Then χ = (λ − D_{h+1}) q², where q is the characteristic polynomial of
the left half.

*Proof.* Split at the edge h (item 2) and expand the right part from its first position, the
centre (item 3). By reversal (item 4) the right half has characteristic polynomial q, and after
removal of the position next to the centre it has the characteristic polynomial q⁻ of the left
half without its last position. Hence χ = (λ − D_{h+1}) q² − B_{h+1} q q⁻ − B_h q⁻ q, and the last
two terms cancel. ∎

**Lemma 2 (even fold).** Let (D, B) be a pair of size 2h with central product B_h = −1, with
central diagonal entries D_h = z − δ and D_{h+1} = z + δ where δ² = 1, and with halves that are
mirror images otherwise. Then χ = q², where q is the characteristic polynomial of the left half
with its last diagonal entry replaced by z.

*Proof.* Split at the central edge. By item 5 the two halves have characteristic polynomials
q + δq⁻ and q − δq⁻, where q⁻ belongs to the left half without its last position, and after removal
of the two central positions both parts have characteristic polynomial q⁻. Hence
χ = (q + δq⁻)(q − δq⁻) + (q⁻)² = q². ∎

In particular χ_{Φ_ε(p)} = λ χ_p² and χ_{Ψ_δ(p)} = χ_p², so folds of nilpotent pairs are nilpotent.

## 4. The situation modulo 2

Modulo 2 all products ±1 become 1, so we consider pairs (d, 𝟏) over 𝔽₂.

**Lemma 3.** For every d ∈ 𝔽₂ⁿ, with r₁ and r₂ as in Section 2 for the pair (d, 𝟏),

    r₁² + λ r₁ r₂ + r₂² + 1 = (1 + λ) g²   for some g ∈ 𝔽₂[λ].

*Proof.* Induction on n, removing the first position. For n = 1 the left side is
(λ + d₁)² + λ(λ + d₁) + 1 + 1 = d₁(1 + λ), since d₁² = d₁, and g = d₁ works. For the step, substitute
r₁ = (λ + d₁) r₂ + r₃. The left side becomes r₂² + λ r₂ r₃ + r₃² + 1 + d₁(1 + λ) r₂², and with the
polynomial g′ of the pair without its first position, g = g′ + d₁ r₂ works. ∎

**Lemma 4 (uniqueness modulo 2).** For every n there is at most one d ∈ 𝔽₂ⁿ with χ₍d,𝟏₎ = λⁿ.

*Proof.* In a polynomial of the form (1 + λ) g² over 𝔽₂ the coefficients of λ^{2j} and λ^{2j+1}
agree, because g² has only even powers. Let d and d′ both be nilpotent, with second continuants r₂
and r₂′, and let u = r₂ − r₂′, of degree less than n − 1. Subtracting the identities of Lemma 3
gives u² + λ^{n+1} u = (1 + λ) s². Comparing the coefficients of λ^{2j} and λ^{2j+1} shows, by
strong induction on j, that every coefficient of u vanishes. So r₂ = r₂′. Finally the pair (r₁, r₂)
determines d: by item 3, λ + dₖ and r_{k+2} are the quotient and the remainder of rₖ by r_{k+1};
formally, if two diagonals have the same r₁ and r₂, comparing degrees in
(d₁′ − d₁) r₂ = r₃ − r₃′ gives d₁ = d₁′ and r₃ = r₃′, and one proceeds by induction. ∎

**Corollary 5.** Let d ∈ 𝔽₂ⁿ with χ₍d,𝟏₎ = λⁿ.

- d is a palindrome (apply Lemma 4 to d and rev d, using item 4).
- If n = 2h + 1, then d_{h+1} = 0 and the left half (d₁, …, d_h) is nilpotent.
- If n = 2h, then (d₁, …, d_{h−1}, d_h + 1) is nilpotent.

*Proof.* For odd n, Lemma 1 applies to the palindrome d and gives λⁿ = (λ + d_{h+1}) q². The value
at λ = 1 shows d_{h+1} = 0, and then q² = (λ^h)², so q = λ^h. For even n, Lemma 2 applies with
δ = 1 and z = d_h + 1 (over 𝔽₂, z − 1 = z + 1 = d_h = d_{h+1}) and gives q² = (λ^h)². ∎

## 5. Transversality

**Lemma 6.** Let (d, 𝟏) be a pair of size n over a field. The polynomials A₁, …, Aₙ, B₁, …, Bₙ₋₁
span the space of the polynomials of degree less than n.

*Proof.* Let W be their span. We show by strong induction on j that ℓ_i r_{j+1} ∈ W whenever
i < j ≤ n. For j = i + 1 and j = i + 2 this is A_{i+1} ∈ W and B_{i+1} ∈ W. For j ≥ i + 3, items 3
and the recurrence λℓ_i = ℓ_{i+1} + d_{i+1} ℓ_i + ℓ_{i−1} give

    ℓ_i r_{j+1} = ℓ_{i+1} r_j + (d_{i+1} − d_{j−1}) ℓ_i r_j + ℓ_{i−1} r_j − ℓ_i r_{j−1},

and all terms on the right lie in W by the induction hypothesis (the term with ℓ_{i−1} is absent
for i = 0). For j = n we obtain ℓ_i ∈ W for all i < n, and ℓ₀, …, ℓₙ₋₁ are monic of degrees
0, …, n − 1. ∎

**Lemma 7.** In addition let d be a palindrome. Then Aₖ = A_{n+1−k} and Bₖ = B_{n−k}, and the
⌈n/2⌉ polynomials Aₖ with k > ⌊n/2⌋ together with the ⌊n/2⌋ polynomials Bₖ with k ≥ ⌈n/2⌉ are
linearly independent. Consequently, a relation Σ tₖ Aₖ + Σ uₖ Bₖ = 0 in which tₖ = 0 for
k ≤ ⌊n/2⌋ and uₖ = 0 for k < ⌈n/2⌉ has all coefficients zero.

*Proof.* The symmetry follows from item 4. By Lemma 6 and the symmetry, the n polynomials named
span a space of dimension n. ∎

## 6. Linearisation

**Lemma 8.** Let t ∈ R with t² = 0, and let (d, b) be a pair and x, y sequences over R. Then

    χ₍d + t x, b + t y₎ = χ₍d,b₎ + t V,

where V is defined by the recurrence V₀ = 0, V₁ = −x₁,
Vₖ = (λ − dₖ) Vₖ₋₁ − bₖ₋₁ Vₖ₋₂ − xₖ χₖ₋₁ − yₖ₋₁ χₖ₋₂. If all bₖ = 1, then
V = −(Σ xₖ Aₖ + Σ yₖ Bₖ).

*Proof.* Both statements follow by induction from the recurrences; in the first, the terms of
second order carry the factor t². ∎

## 7. Rigidity modulo 4

**Lemma 9 (comparison).** Let P = (d, b) and Q = (d′, b′) be integer pairs of size n with
χ_P ≡ χ_Q ≡ λⁿ (mod 4). Suppose that P ≡ Q (mod 2) entrywise, that the products of Q are odd, that
d′ is a palindrome modulo 2, and that dₖ = d′ₖ for k ≤ ⌊n/2⌋ and bₖ = b′ₖ for k < ⌈n/2⌉. Then
P ≡ Q (mod 4) entrywise.

*Proof.* Write d = d′ + 2x and b = b′ + 2y. In ℤ/4 we have 2² = 0, so Lemma 8 gives
χ_P = χ_Q + 2V modulo 4, hence 2V ≡ 0 (mod 4) and V ≡ 0 (mod 2). Modulo 2 the pair Q becomes
(d̄′, 𝟏), so by Lemma 8 again Σ x̄ₖ Aₖ + Σ ȳₖ Bₖ = 0 over 𝔽₂, where Aₖ, Bₖ belong to the palindrome
d̄′. The coefficients vanish on the left half by hypothesis, so Lemma 7 shows that all xₖ and yₖ
are even. ∎

**Proof of Theorem B, "only if".** Let P = (d, b) ∈ 𝒞ₙ with χ_P ≡ λⁿ (mod 4). Modulo 2 the pair is
nilpotent, so Corollary 5 applies to d̄.

*Odd n = 2h + 1.* Let Q be the odd fold, with sign b_h, of the left half p of P:
Q = ((d₁, …, d_h, 0, d_h, …, d₁), (b₁, …, b_h, −b_h, b_{h−1}, …, b₁)). By Lemma 1,
χ_Q = λ χ_p². By Corollary 5, χ_p ≡ λ^h (mod 2), so χ_p = λ^h + 2g and χ_Q ≡ λⁿ (mod 4); moreover
Q ≡ P (mod 2), because d̄ is a palindrome with central entry 0. The pair Q is a palindrome in its
diagonal and agrees with P on the left half. Lemma 9 gives P ≡ Q (mod 4). All entries of P and of
Q lie in {−1, 0, 1}, and two such numbers that are congruent modulo 4 are equal. So P = Q is the
odd fold of p, and χ_p ≡ λ^h (mod 2).

*Even n = 2h.* Let p be the left half of P with its last diagonal entry raised by 1, and let
Q = Ψ₁(p) = ((d₁, …, d_h, d_h + 2, d_{h−1}, …, d₁), (b₁, …, b_{h−1}, −1, b_{h−1}, …, b₁)). By
Lemma 2, χ_Q = χ_p², and χ_p ≡ λ^h (mod 2) by Corollary 5, so χ_Q ≡ λⁿ (mod 4). Again Q ≡ P
(mod 2), the diagonal of Q is a palindrome modulo 2, and Q agrees with P on the left half. Lemma 9
gives P ≡ Q (mod 4). Hence d_{h+1} ≡ d_h + 2 (mod 4), which for entries in {−1, 0, 1} means
d_{h+1} = −d_h ≠ 0; also b_h = −1, and the remaining entries of the right half mirror the left
half. So P = Ψ_δ(p′) with δ = d_{h+1} and p′ = ((d₁, …, d_{h−1}, 0), (b₁, …, b_{h−1})), and
χ_{p′} ≡ λ^h (mod 2) because d_h is odd. ∎

**Lemma 10 (descent).** Let q ∈ ℤ[λ] be monic of degree h, let e ≥ 0 and k ≥ 1. Then
λ^e q² ≡ λ^{e+2h} (mod 2^{k+1}) if and only if q ≡ λ^h (mod 2^k).

*Proof.* If q = λ^h + 2^k g, then λ^e q² − λ^{e+2h} = 2^{k+1} λ^e g (λ^h + 2^{k−1} g). Conversely,
the congruence modulo 2 gives q̄² = (λ^h)² over 𝔽₂, so q = λ^h + 2g with deg g < h, and
λ^e q² − λ^{e+2h} = 4 g · λ^e (λ^h + g). The second factor is monic, so 2^{k−1} divides g: a
constant that divides a product with a monic polynomial divides the other factor. ∎

**Proof of Theorem B, "if" and the descent.** A fold P of p has χ_P = λ^{n−2h} χ_p² by Lemmas 1
and 2. Lemma 10 with q = χ_p and e = n − 2h gives the equivalence of the congruences for every
k ≥ 1; the case k = 1 is the "if" direction. ∎

## 8. Proofs of Theorems A and C

**Theorem A.** Folds of nilpotent pairs are nilpotent (Section 3). Conversely let P ∈ 𝒩ₙ, n ≥ 2.
By Theorem B, P is a fold of a pair p ∈ 𝒞_h, and λ^{n−2h} χ_p² = λⁿ gives χ_p² = (λ^h)². As χ_p is
monic, χ_p = λ^h. For even n the pair that is folded is p′ above, whose last diagonal entry is 0.
The pair p and the sign can be read off from P, which gives the uniqueness. For n = 1,
χ = λ − d₁ = λ forces d₁ = 0. ∎

**Theorem C.** Strong induction on n. For n = 1 the hypothesis says that d₁ is even, so d₁ = 0.
For n ≥ 2 we have ⌊log₂ n⌋ = ⌊log₂ h⌋ + 1 ≥ 1 with h = ⌊n/2⌋. So χ_P ≡ λⁿ (mod 4), P is a fold
of some p ∈ 𝒞_h by Theorem B, and the descent with k = ⌊log₂ h⌋ + 1 gives χ_p ≡ λ^h modulo
2^{⌊log₂ h⌋ + 1}. By induction χ_p = λ^h, hence χ_P = λⁿ. ∎

## 9. Lists, matrices, sizes and the count

**Matrices.** Expanding det(λ − M) along the first column, and the second minor along its first
row, gives the recurrence of item 3 for the determinants of the trailing blocks. So the
characteristic polynomial of the tridiagonal matrix with diagonal d, superdiagonal a and
subdiagonal c is χ₍d, ac₎. Over an integral domain a matrix of size n is nilpotent if and only if
its characteristic polynomial is λⁿ (Cayley–Hamilton in one direction; in the other, the
coefficients of the characteristic polynomial of a nilpotent matrix are nilpotent).

**Folded pairs.** Call a pair of lists *folded* if it is obtained from ((0), ()) by odd folds and
by even folds of pairs with last diagonal entry 0. By Theorem A and induction on the size, the
nilpotent pairs in 𝒞ₙ are exactly the folded pairs of size n.

**Theorem D.** A folded pair of size 2h + 1 ≥ 3 arises from exactly one folded pair of size h and
one sign, and a folded pair of size 2h from exactly one folded pair of size h with last diagonal
entry 0 and one sign. It remains to decide which folded pairs end in 0. The first diagonal entry
of an odd fold of a pair of size h ≥ 1 is that of the pair, and so is its last entry. The first and
the last diagonal entry of an even fold of a pair of size h ≥ 2 are the first entry of that pair,
while the even fold of ((0), ()) is ((−δ, δ), (−1)). By induction, the first and the last diagonal
entry of a folded pair of size n vanish if and only if n = 1 or 3·2^j ≤ n < 2^{j+2} for some j
(the binary expansion of n begins with 11). So |𝒩_{2h+1}| = 2|𝒩_h|, and |𝒩_{2h}| = 2|𝒩_h| if
h = 1 or the expansion of h begins with 11, while 𝒩_{2h} is empty otherwise. Induction on n gives
both assertions. ∎

## 10. The formal statements

All names are in the namespace `Tridiagonal`. `K d b n` is the characteristic polynomial of the
pair formed by the first n values of `d : ℕ → R` and the first n − 1 values of `b : ℕ → R`.

| Statement | Lean | File |
|---|---|---|
| Section 2, items 1–6 | `K_congr`, `K_monic`, `K_natDegree`, `K_split`, `K_succ_succ_left`, `K_reverse`, `K_update_diag`, `K_update_off`, `K_map` | `Continuant.lean` |
| Lemma 1, Lemma 2 | `K_fold_odd`, `K_fold_even` | `Fold.lean` |
| Lemma 3 | `riccati` | `ModTwo.lean` |
| Lemma 4 | `nil_unique` | `ModTwo.lean` |
| Corollary 5 | `nil_palindrome`, `mod2_odd`, `mod2_even` | `ModTwo.lean` |
| Lemma 6 | `mem_Wfull_of_coeff` | `Transversality.lean` |
| Lemma 7 | `half_linearIndependent`, `indep_half` | `Transversality.lean` |
| Lemma 8 | `K_perturb`, `V_eq_sum` | `Linearise.lean` |
| Lemma 9 | `agree_mod_four` | `Rigidity.lean` |
| Theorem B, "only if" | `rigid_odd`, `rigid_even` | `Rigidity.lean` |
| Lemma 10 | `descent` | `Congruence.lean` |
| Theorem B | `mod_four_odd_iff`, `mod_four_even_iff`, `descent_odd`, `descent_even` | `Classification.lean` |
| Theorem A, entrywise | `nil_odd_iff`, `nil_even_iff` | `Classification.lean` |
| Theorem C | `nil_of_congr` | `Classification.lean` |
| Characteristic polynomial of a tridiagonal matrix | `Tri_charpoly`, `Tri_isNilpotent_iff` | `Matrix.lean` |
| Theorem A for lists | `folded_iff` | `Pairs.lean` |
| Theorem A for matrices | `isNilpotent_iff_folded` | `Main.lean` |
| Theorem D | `nilPairs_nonempty_iff`, `nilPairs_ncard` | `Sizes.lean`, `Main.lean` |

The results of the paper on the number of all nilpotent tridiagonal matrices with entries in
{−1, 0, 1}, on the resolvent, on the matrices of Liu and on Corless's family are not formalised.
They are checked by the programs in `computations/`.
