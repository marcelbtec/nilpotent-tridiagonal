# Computations

These programs check the statements of the paper *Nilpotent tridiagonal matrices with entries in {−1, 0, 1}* by exact computation, including the statements that are not part of the Lean formalisation. Statement and equation numbers refer to the sixth version of the manuscript. Each program prints `PASS` or `FAIL` lines. The files `out_*.txt` are the outputs of the run of 21 November 2026, without the timings.

```
computations/run_all.sh        # about 3 minutes on 14 cores, 15 minutes on 2 cores
```

You need Python 3 with numpy and sympy, and a C compiler with OpenMP (set `CC`; on macOS a Homebrew gcc such as `CC=gcc-15`). The script exits with status 1 if a program fails.

| Program | What it checks |
|---|---|
| `check_folds.py` | F1–F11. The folding identities; Liu's matrices of sizes 14 and 28; Theorem 1.1 by brute force over all pairs for n ≤ 10 and by a filtered exhaustive search for n ≤ 27 (1,386,853 candidates survive modulo 4); the independence of Lemma 2.4 over 𝔽₂ for n ≤ 1024; Corollary 1.2; the count 1, 9, 73, 585, 4809, 39113 of Corollary 1.4 by enumeration of all matrices for n ≤ 6. `python3 check_folds.py 27` (the argument is the largest size of the exhaustive search; default 22) |
| `check_proof.py` | P1–P9. Lemmas 2.1, 2.3 and 2.4 on random instances over several fields, the increments of the resolvent entry (Proposition 3.2), the relations modulo 4 between a nilpotent pair and the fold with all signs +1 for n ≤ 64, Corollary 1.2 for n < 130. |
| `check_newproofs.py` | N1–N5. The steps of the proofs as they are written in the paper and formalised in Lean: the identity (12), the uniqueness modulo 2 for all diagonals with n ≤ 16, the induction of Lemma 2.4 (i), the comparison of a pair with the fold of its left half for all pairs with n ≤ 9, and the descent. Standard library only. |
| `check_revision.py` | R1–R8. Theorem 1.5 and Corollary 1.6 for all pairs with n ≤ 10; the recognition test of Remark 3.1; the examples of Remark 3.3; Remark 5.4; Liu's matrices as printed in the sources and their fold words; the chains of Takata et al.; Corollaries 1.2 and 1.4. |
| `valuation.c` | Corollary 1.6 (ii), (iii): the largest 2-adic valuation of χ − λⁿ over all pairs with χ ≡ λⁿ (mod 2), for n ≤ 21. `./valuation 21` |
| `fullfamily.py` | Remark 1.7: matrices with vanishing products; the example λ⁷ − 8λ and the values J(n) for n ≤ 12. `python3 fullfamily.py 12` |
| `check_multiplicity.py` | M1–M4. Section 5: the bound 2^{v₂(m+1)} − 1 for m ≤ 19, Proposition 5.2, the anti-fold formulas, and the data files `low31.txt` and `sym_K6_d3.txt`. |
| `mult.c` | Table 1, rows m = 15 and m = 31: the histogram of deg D_s over all 2^{m−1} sign sequences. `./mult 15`, `./mult 31` |
| `twists.py`, `lowsym.c` | Table 1, row m = 63: the sequences with deg D_s ≤ 3 inside the set allowed by the condition modulo 4. `python3 twists.py 6 3` prints the two masks that `./lowsym 6 3 <mask> <mask>` needs; `lowsym` writes the sequences to `sym_K6_d3.txt`. |
| `ep_fold.py` | Proposition 4.1: the two folding steps for arbitrary square matrices, and chains with exceptional points of order 3, 6 and 13. |

Data files:

| File | Content |
|---|---|
| `low31.txt` | all sign sequences with deg D_s ≤ 7 at m = 31 (sequence, degree, coefficients of D_s) |
| `sym_K6_d3.txt` | all sign sequences with deg D_s ≤ 3 at m = 63 |
