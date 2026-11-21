import NilpotentTridiagonal

/-!
Prints the axioms on which the main theorems depend. The expected output is
`[propext, Classical.choice, Quot.sound]` for each of them.
-/

open Tridiagonal

-- Theorem 1.1 (classification)
#print axioms isNilpotent_iff_folded
#print axioms folded_iff
#print axioms nilPairs_one
#print axioms nilPairs_odd
#print axioms nilPairs_even
-- Corollary 1.2 (admissible sizes and count)
#print axioms nilPairs_nonempty_iff
#print axioms nilPairs_ncard
-- Theorem 1.5 (rigidity modulo 4)
#print axioms mod_four_odd_iff
#print axioms mod_four_even_iff
#print axioms descent_odd
#print axioms descent_even
-- Corollary 1.6 (i) (nilpotency modulo powers of two)
#print axioms nil_of_congr
