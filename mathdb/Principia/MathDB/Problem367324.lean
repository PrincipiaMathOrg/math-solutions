import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum

/-!
# MathDB #367324 -- Wang--Zhang's Motzkin Hankel conjecture is false as printed

Write-up `mathdb-open-problems/problems/367324/solution.tex`,
*MathDB 367324: exact boundary values for all nonmultiples of three*, 18 September 2026.
Source: Wang and Zhang, arXiv:2502.21050, p. 4, **Conjecture 7**.

With `M(z) = 1 + zM(z) + z^2 M(z)^2` the Motzkin generating function and
`H_N^{(r)} = det([z^{i+j}] M(z)^r)_{0 <= i,j < N}`, Conjecture 7 asserts, for `r ≡ 1, 2 mod 3`:

  `H_{3rn} = H_{3rn+1} = H_{3rn+r} = H_{3rn+r+1} = α`                       (first display)
  `H_{3rn+2r} = H_{3rn+2r+1} = 0`                                          (second)
  `H_{3rn+2r-1} + H_{3rn+2r+2} = β (2r(n+1))^{r-2}`                        (third)
  `H_{3rn+2} + H_{3rn-1} = γ r(r-3)/2`                                     (fourth)

with `|α| = |β| = |γ| = 1` (verbatim from the problem statement).

**What is proved.**  `not_conj7`: the FIRST display already fails at `r = 4`, `n = 0`, which
is inside the conjecture's own hypothesis (`witness_in_scope` records `4 ≡ 1 mod 3` and
`r ≥ 2`).  There `3rn = 0` and `3rn + r = 4`, and `H_0 = 1` (`H_zero`, the empty determinant
-- the source's own convention) while `H_4 = -1` (`H_four`).  Two numbers asserted equal are
not.  **The modulus hypothesis `|α| = 1` is never used**, so what is refuted is the weaker
claim that the four determinants merely agree; the printed conjecture follows a fortiori.

**Every theorem is quantified over sequences satisfying the equation, and such a sequence
EXISTS.**  `IsMotzkin` states the source's defining equation
`M = 1 + zM + z^2M^2` coefficientwise (`m 0 = 1`, `m 1 = 1`,
`m (n+2) = m (n+1) + Σ_{k≤n} m k * m (n-k)`), and every theorem below is universally
quantified over sequences satisfying it, so no result depends on a particular encoding of the
Motzkin numbers, and `mot_two` ... `mot_six` are derived, not asserted.  **That design left one
thing unproved for a while: that `IsMotzkin` is satisfiable at all.**  Until `motSeq` and
`isMotzkin_motSeq` were built (see the last section), every theorem here was an implication
from a hypothesis nothing produced, and so was at risk of being VACUOUSLY true -- which no
gate detects, since a vacuous theorem is axiom-free.  `isMotzkin_unique` adds that the
characterisation pins the sequence, and `not_conj7_uncond` and the two `_third_` variants are
the refutations with no hypothesis at all.  `sq` and `qt` are the coefficientwise square and
fourth power.

**The THIRD display is refuted too, twice.**  It is the write-up's headline
discrepancy: `H_7^{(4)} = 64` and `H_{10}^{(4)} = -64`, so the conjectured sum is `0`, not
`±64` -- that is `not_conj7_third`, and it cost the `7x7` and `10x10` integer determinants
`H_seven` and `H_ten`.  A second witness at `r = 2` (`not_conj7_third_two`) is both cheaper and
sharper: a `3x3` and a `6x6` over the coefficients of `M(z)^2`, and there the first TWO displays
HOLD (`conj7_first_holds_two`, `conj7_second_holds_two`), so **the third display is defective on
its own** rather than inheriting the first display's damage.  At `r = 2` the exponent `r - 2`
degenerates to zero, which is what makes that witness cheap, so it supplements the `r = 4` one
rather than replacing it.

**What is still absent.**  The rest of the write-up -- the exact values for all `r` and `n` --
rests on orthogonal polynomials for a translated semicircle measure, Chebyshev `T_j`/`U_j` and
the Christoffel identity, none of which Mathlib has; the row records that gap.  Neither
refutation needs any of it.

**The determinant is computed, not asserted.**  `Matrix.det` unfolds to a sum over `n!`
permutations, so `decide` is useless here and `native_decide` is banned by this campaign;
Mathlib's closed forms stop at `Matrix.det_fin_three`.  The working route is Mathlib's own
idiom for larger determinants (see `Polynomial.disc` in
`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`): iterate `Matrix.det_succ_row_zero`
down to `3x3`, unfold `Fin.succAbove`, and finish with `Matrix.det_fin_three`.

Values checked first in `Campaigns/MathDB-Formalization/verify_367324.py`.
-/

namespace Principia.MathDB.P367324

open Finset Matrix

variable {m : ℕ → ℤ}

/-- The Motzkin sequence, characterised by the source's own defining equation
`M = 1 + zM + z²M²` read off coefficientwise.  No sequence is defined here, so every
statement below holds for whatever encoding satisfies the equation. -/
structure IsMotzkin (m : ℕ → ℤ) : Prop where
  zero : m 0 = 1
  one : m 1 = 1
  step : ∀ n, m (n + 2) = m (n + 1) + ∑ k ∈ range (n + 1), m k * m (n - k)

theorem mot_two (h : IsMotzkin m) : m 2 = 2 := by
  have e := h.step 0
  simp [h.zero, h.one] at e
  omega

theorem mot_three (h : IsMotzkin m) : m 3 = 4 := by
  have e := h.step 1
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h] at e
  omega

theorem mot_four (h : IsMotzkin m) : m 4 = 9 := by
  have e := h.step 2
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h] at e
  omega

theorem mot_five (h : IsMotzkin m) : m 5 = 21 := by
  have e := h.step 3
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h] at e
  omega

theorem mot_six (h : IsMotzkin m) : m 6 = 51 := by
  have e := h.step 4
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h,
    mot_five h] at e
  omega

theorem mot_seven (h : IsMotzkin m) : m 7 = 127 := by
  have e := h.step 5
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h] at e
  omega

theorem mot_eight (h : IsMotzkin m) : m 8 = 323 := by
  have e := h.step 6
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h] at e
  omega

theorem mot_nine (h : IsMotzkin m) : m 9 = 835 := by
  have e := h.step 7
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h] at e
  omega

theorem mot_ten (h : IsMotzkin m) : m 10 = 2188 := by
  have e := h.step 8
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h] at e
  omega

theorem mot_eleven (h : IsMotzkin m) : m 11 = 5798 := by
  have e := h.step 9
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h] at e
  omega

theorem mot_twelve (h : IsMotzkin m) : m 12 = 15511 := by
  have e := h.step 10
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h] at e
  omega

theorem mot_thirteen (h : IsMotzkin m) : m 13 = 41835 := by
  have e := h.step 11
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h] at e
  omega

theorem mot_fourteen (h : IsMotzkin m) : m 14 = 113634 := by
  have e := h.step 12
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h,
    mot_thirteen h] at e
  omega

theorem mot_fifteen (h : IsMotzkin m) : m 15 = 310572 := by
  have e := h.step 13
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h,
    mot_thirteen h, mot_fourteen h] at e
  omega

theorem mot_sixteen (h : IsMotzkin m) : m 16 = 853467 := by
  have e := h.step 14
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h,
    mot_thirteen h, mot_fourteen h, mot_fifteen h] at e
  omega

theorem mot_seventeen (h : IsMotzkin m) : m 17 = 2356779 := by
  have e := h.step 15
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h,
    mot_thirteen h, mot_fourteen h, mot_fifteen h, mot_sixteen h] at e
  omega

theorem mot_eighteen (h : IsMotzkin m) : m 18 = 6536382 := by
  have e := h.step 16
  simp [Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
    mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h,
    mot_thirteen h, mot_fourteen h, mot_fifteen h, mot_sixteen h, mot_seventeen h] at e
  omega

/-- `[z^n] M(z)^2`. -/
def sq (m : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), m k * m (n - k)

/-- `[z^n] M(z)^4`, as the square of the square. -/
def qt (m : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), sq m k * sq m (n - k)

theorem sq_vals (h : IsMotzkin m) :
    sq m 0 = 1 ∧
      sq m 1 = 2 ∧
      sq m 2 = 5 ∧
      sq m 3 = 12 ∧
      sq m 4 = 30 ∧
      sq m 5 = 76 ∧
      sq m 6 = 196 ∧
      sq m 7 = 512 ∧
      sq m 8 = 1353 ∧
      sq m 9 = 3610 ∧
      sq m 10 = 9713 ∧
      sq m 11 = 26324 ∧
      sq m 12 = 71799 ∧
      sq m 13 = 196938 ∧
      sq m 14 = 542895 ∧
      sq m 15 = 1503312 ∧
      sq m 16 = 4179603 ∧
      sq m 17 = 11662902 ∧
      sq m 18 = 32652735 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sq, Finset.sum_range_succ, h.zero, h.one, mot_two h, mot_three h, mot_four h, mot_five h,
      mot_six h, mot_seven h, mot_eight h, mot_nine h, mot_ten h, mot_eleven h, mot_twelve h,
      mot_thirteen h, mot_fourteen h, mot_fifteen h, mot_sixteen h, mot_seventeen h,
      mot_eighteen h]

theorem qt_vals (h : IsMotzkin m) :
    qt m 0 = 1 ∧
      qt m 1 = 4 ∧
      qt m 2 = 14 ∧
      qt m 3 = 44 ∧
      qt m 4 = 133 ∧
      qt m 5 = 392 ∧
      qt m 6 = 1140 ∧
      qt m 7 = 3288 ∧
      qt m 8 = 9438 ∧
      qt m 9 = 27016 ∧
      qt m 10 = 77220 ∧
      qt m 11 = 220584 ∧
      qt m 12 = 630084 ∧
      qt m 13 = 1800384 ∧
      qt m 14 = 5147328 ∧
      qt m 15 = 14727168 ∧
      qt m 16 = 42171849 ∧
      qt m 17 = 120870324 ∧
      qt m 18 = 346757334 := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17,
    s18⟩ := sq_vals h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [qt, Finset.sum_range_succ, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13,
      s14, s15, s16, s17, s18]

/-- The `N × N` Hankel matrix of a coefficient sequence.  The index sum is taken in `ℕ`,
not in `Fin N`. -/
def hank (a : ℕ → ℤ) (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => a ((i : ℕ) + (j : ℕ))

/-- `H_0 = 1`, the empty determinant -- the source's own convention. -/
theorem H_zero (a : ℕ → ℤ) : (hank a 0).det = 1 := by
  simp

theorem H_one (h : IsMotzkin m) : (hank (qt m) 1).det = 1 := by
  obtain ⟨q0, -⟩ := qt_vals h
  simp [hank, q0]

theorem hank_four (h : IsMotzkin m) :
    hank (qt m) 4 = !![1, 4, 14, 44; 4, 14, 44, 133; 14, 44, 133, 392;
                        44, 133, 392, 1140] := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17,
    q18⟩ := qt_vals h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hank, q0, q1, q2, q3, q4, q5, q6]

/-- **`H_4 = -1`.** -/
theorem H_four (h : IsMotzkin m) : (hank (qt m) 4).det = -1 := by
  rw [hank_four h]
  simp [Matrix.det_succ_row_zero (n := 3), Fin.succAbove, Matrix.det_fin_three,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- The first display of Wang--Zhang Conjecture 7 at exponent `r` and block index `n`:
the four boundary determinants `H_{3rn}`, `H_{3rn+1}`, `H_{3rn+r}`, `H_{3rn+r+1}` are all
EQUAL, to a common value `α` of modulus one. -/
def Conj7First (a : ℕ → ℤ) (r n : ℕ) : Prop :=
  ∃ α : ℤ, α.natAbs = 1
    ∧ (hank a (3 * r * n)).det = α
    ∧ (hank a (3 * r * n + 1)).det = α
    ∧ (hank a (3 * r * n + r)).det = α
    ∧ (hank a (3 * r * n + r + 1)).det = α

/-- The witness is inside the conjecture's own hypothesis `r ≡ 1 or 2 (mod 3)`, `r ≥ 2`. -/
theorem witness_in_scope : 4 % 3 = 1 ∧ 2 ≤ 4 := by norm_num

/-- **Conjecture 7 is false**: its first display already fails at `r = 4`, `n = 0`, where
`H_0 = 1` but `H_4 = -1`.  The modulus hypothesis `|α| = 1` is never used, so the
refutation kills the weaker statement that the four determinants merely agree. -/
theorem not_conj7 (h : IsMotzkin m) : ¬ Conj7First (qt m) 4 0 := by
  rintro ⟨α, -, h0, -, h4, -⟩
  rw [show 3 * 4 * 0 = 0 from rfl, H_zero] at h0
  rw [show 3 * 4 * 0 + 4 = 4 from rfl, H_four h] at h4
  omega

theorem hank_seven (h : IsMotzkin m) :
    hank (qt m) 7 = !![1, 4, 14, 44, 133, 392, 1140;
                        4, 14, 44, 133, 392, 1140, 3288;
                        14, 44, 133, 392, 1140, 3288, 9438;
                        44, 133, 392, 1140, 3288, 9438, 27016;
                        133, 392, 1140, 3288, 9438, 27016, 77220;
                        392, 1140, 3288, 9438, 27016, 77220, 220584;
                        1140, 3288, 9438, 27016, 77220, 220584, 630084] := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17,
    q18⟩ := qt_vals h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hank, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12]

set_option maxHeartbeats 2000000 in
/-- **`H_7 = 64`.** -/
theorem H_seven (h : IsMotzkin m) : (hank (qt m) 7).det = 64 := by
  rw [hank_seven h]
  simp [Matrix.det_succ_row_zero (n := 6), Matrix.det_succ_row_zero (n := 5),
    Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem hank_ten (h : IsMotzkin m) :
    hank (qt m) 10 = !![1, 4, 14, 44, 133, 392, 1140, 3288, 9438, 27016;
                        4, 14, 44, 133, 392, 1140, 3288, 9438, 27016, 77220;
                        14, 44, 133, 392, 1140, 3288, 9438, 27016, 77220, 220584;
                        44, 133, 392, 1140, 3288, 9438, 27016, 77220, 220584, 630084;
                        133, 392, 1140, 3288, 9438, 27016, 77220, 220584, 630084, 1800384;
                        392, 1140, 3288, 9438, 27016, 77220, 220584, 630084, 1800384, 5147328;
                        1140, 3288, 9438, 27016, 77220, 220584, 630084, 1800384, 5147328, 14727168;
                        3288, 9438, 27016, 77220, 220584, 630084, 1800384, 5147328, 14727168,
                          42171849;
                        9438, 27016, 77220, 220584, 630084, 1800384, 5147328, 14727168, 42171849,
                          120870324;
                        27016, 77220, 220584, 630084, 1800384, 5147328, 14727168, 42171849,
                          120870324, 346757334] := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17,
    q18⟩ := qt_vals h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hank, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`H_10 = -64`.**  The ten-by-ten determinant: `Matrix.det` unfolds to a sum over `10!`
permutations, so this is the wall the row recorded.  Mathlib's own iterated
`det_succ_row_zero` idiom clears it, but only once `simp`'s step budget is raised -- the
default `maxSteps = 100000` is what fails, not `maxHeartbeats`. -/
theorem H_ten (h : IsMotzkin m) : (hank (qt m) 10).det = -64 := by
  rw [hank_ten h]
  simp (config := { maxSteps := 20000000 })
    [Matrix.det_succ_row_zero (n := 9), Matrix.det_succ_row_zero (n := 8),
    Matrix.det_succ_row_zero (n := 7), Matrix.det_succ_row_zero (n := 6),
    Matrix.det_succ_row_zero (n := 5), Matrix.det_succ_row_zero (n := 4),
    Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- The third display of Conjecture 7 at exponent `r` and block index `n`:
`H_{3rn+2r-1} + H_{3rn+2r+2} = β (2r(n+1))^{r-2}` with `|β| = 1`. -/
def Conj7Third (a : ℕ → ℤ) (r n : ℕ) : Prop :=
  ∃ β : ℤ, β.natAbs = 1
    ∧ (hank a (3 * r * n + 2 * r - 1)).det + (hank a (3 * r * n + 2 * r + 2)).det
        = β * ((2 * r * (n + 1) : ℕ) : ℤ) ^ (r - 2)

/-- **The third display fails too**, and this is the write-up's headline discrepancy: at
`r = 4`, `n = 0` the conjecture puts `H_7 + H_10 = ±64`, but `H_7 = 64` and `H_10 = -64`,
so the sum is `0`.  A nonzero value is claimed next to a pair of vanishing determinants
(`H_8 = H_9 = 0`), and it is not there. -/
theorem not_conj7_third (h : IsMotzkin m) : ¬ Conj7Third (qt m) 4 0 := by
  rintro ⟨β, hβ, hsum⟩
  rw [show 3 * 4 * 0 + 2 * 4 - 1 = 7 from rfl, show 3 * 4 * 0 + 2 * 4 + 2 = 10 from rfl,
    H_seven h, H_ten h] at hsum
  norm_num at hsum
  omega

section ExponentTwo

/-! ### The same defect at `r = 2`, where the FIRST TWO displays HOLD

The refutations above are both at `r = 4`, and there the FIRST display already fails
(`H_0 = 1`, `H_4 = -1`).  A reader could therefore conclude that Conjecture 7 is merely
mis-indexed for `r ≡ 1 (mod 3)`, and that the third display inherits the damage.

It does not.  At `r = 2`, `n = 0` — also inside the conjecture's own hypothesis — the first
display HOLDS (`H_0 = H_1 = H_2 = H_3 = 1`, `conj7_first_holds_two`) and so does the second
(`H_4 = H_5 = 0`, `conj7_second_holds_two`), while the third still FAILS: `H_3 = 1` and
`H_6 = -1`, so their sum is `0` where a value of modulus one is claimed.  **The third display
is defective on its own**, not as a consequence of the first.

**The witness is also far cheaper than the row recorded.**  At `r = 2` the pair of
determinants is `3×3` and `6×6` over the coefficients of `M(z)²` (`sq`), not the `7×7` and
`10×10` over `M(z)⁴` that `H_seven`/`H_ten` needed.

**Honest about the degeneracy:** at `r = 2` the conjecture's exponent `r − 2` is zero, so its
right-hand side is `β` rather than a growing power.  That is what makes this witness cheap, and
it is why it supplements rather than replaces `not_conj7_third` — the `r = 4` witness is the
non-degenerate one, and it is the write-up's own.

**A pattern, checked but NOT proved here** (`Campaigns/MathDB-Formalization/check_367324.py`):
at every `(r, n)` examined — `r = 2, 4, 5, 7, 8` — the two determinants of the third display are
exact negatives of one another, so the sum is always `0` while the claimed modulus
`(2r(n+1))^{r−2}` grows.  The defect is therefore systematic rather than an arithmetic slip; the
general statement is the write-up's own theorem and rests on the orthogonal-polynomial theory
Mathlib does not have.
-/

theorem Hs_one (h : IsMotzkin m) : (hank (sq m) 1).det = 1 := by
  obtain ⟨s0, -⟩ := sq_vals h
  simp [hank, s0]

theorem hank_two_s (h : IsMotzkin m) : hank (sq m) 2 = !![1, 2; 2, 5] := by
  obtain ⟨s0, s1, s2, -⟩ := sq_vals h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hank, s0, s1, s2]

theorem Hs_two (h : IsMotzkin m) : (hank (sq m) 2).det = 1 := by
  rw [hank_two_s h]
  simp [Matrix.det_fin_two]

theorem hank_three_s (h : IsMotzkin m) :
    hank (sq m) 3 = !![1, 2, 5; 2, 5, 12; 5, 12, 30] := by
  obtain ⟨s0, s1, s2, s3, s4, -⟩ := sq_vals h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hank, s0, s1, s2, s3, s4]

/-- **`H_3 = 1` for `M(z)²`.** -/
theorem Hs_three (h : IsMotzkin m) : (hank (sq m) 3).det = 1 := by
  rw [hank_three_s h]
  simp [Matrix.det_fin_three]

theorem hank_four_s (h : IsMotzkin m) :
    hank (sq m) 4 = !![1, 2, 5, 12; 2, 5, 12, 30; 5, 12, 30, 76; 12, 30, 76, 196] := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, -⟩ := sq_vals h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hank, s0, s1, s2, s3, s4, s5, s6]

/-- **`H_4 = 0` for `M(z)²`** — the second display's first vanishing determinant. -/
theorem Hs_four (h : IsMotzkin m) : (hank (sq m) 4).det = 0 := by
  rw [hank_four_s h]
  simp [Matrix.det_succ_row_zero (n := 3), Fin.succAbove, Matrix.det_fin_three,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem hank_five_s (h : IsMotzkin m) :
    hank (sq m) 5 = !![1, 2, 5, 12, 30; 2, 5, 12, 30, 76; 5, 12, 30, 76, 196;
                        12, 30, 76, 196, 512; 30, 76, 196, 512, 1353] := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := sq_vals h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hank, s0, s1, s2, s3, s4, s5, s6, s7, s8]

/-- **`H_5 = 0` for `M(z)²`** — the second display's other vanishing determinant. -/
theorem Hs_five (h : IsMotzkin m) : (hank (sq m) 5).det = 0 := by
  rw [hank_five_s h]
  simp [Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem hank_six_s (h : IsMotzkin m) :
    hank (sq m) 6 = !![1, 2, 5, 12, 30, 76; 2, 5, 12, 30, 76, 196; 5, 12, 30, 76, 196, 512;
                        12, 30, 76, 196, 512, 1353; 30, 76, 196, 512, 1353, 3610;
                        76, 196, 512, 1353, 3610, 9713] := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, -⟩ := sq_vals h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hank, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]

/-- **`H_6 = -1` for `M(z)²`** — the exact negative of `H_3`. -/
theorem Hs_six (h : IsMotzkin m) : (hank (sq m) 6).det = -1 := by
  rw [hank_six_s h]
  simp [Matrix.det_succ_row_zero (n := 5), Matrix.det_succ_row_zero (n := 4),
    Matrix.det_succ_row_zero (n := 3), Fin.succAbove, Matrix.det_fin_three,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- The witness is inside the conjecture's own hypothesis `r ≡ 1 or 2 (mod 3)`, `r ≥ 2`. -/
theorem witness_in_scope_two : 2 % 3 = 2 ∧ 2 ≤ 2 := by norm_num

/-- The second display of Conjecture 7: `H_{3rn+2r} = H_{3rn+2r+1} = 0`. -/
def Conj7Second (a : ℕ → ℤ) (r n : ℕ) : Prop :=
  (hank a (3 * r * n + 2 * r)).det = 0 ∧ (hank a (3 * r * n + 2 * r + 1)).det = 0

/-- **The first display HOLDS at `r = 2`, `n = 0`**, with `α = 1`. -/
theorem conj7_first_holds_two (h : IsMotzkin m) : Conj7First (sq m) 2 0 := by
  refine ⟨1, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [show 3 * 2 * 0 = 0 from rfl]
    exact H_zero _
  · rw [show 3 * 2 * 0 + 1 = 1 from rfl]
    exact Hs_one h
  · rw [show 3 * 2 * 0 + 2 = 2 from rfl]
    exact Hs_two h
  · rw [show 3 * 2 * 0 + 2 + 1 = 3 from rfl]
    exact Hs_three h

/-- **The second display HOLDS at `r = 2`, `n = 0`.** -/
theorem conj7_second_holds_two (h : IsMotzkin m) : Conj7Second (sq m) 2 0 := by
  refine ⟨?_, ?_⟩
  · rw [show 3 * 2 * 0 + 2 * 2 = 4 from rfl]
    exact Hs_four h
  · rw [show 3 * 2 * 0 + 2 * 2 + 1 = 5 from rfl]
    exact Hs_five h

/-- **The third display FAILS at `r = 2`, `n = 0`, where the first two HOLD.**  `H_3 = 1` and
`H_6 = -1`, so the sum is `0`, while the display claims a value of modulus one. -/
theorem not_conj7_third_two (h : IsMotzkin m) : ¬ Conj7Third (sq m) 2 0 := by
  rintro ⟨β, hβ, hsum⟩
  rw [show 3 * 2 * 0 + 2 * 2 - 1 = 3 from rfl, show 3 * 2 * 0 + 2 * 2 + 2 = 6 from rfl,
    Hs_three h, Hs_six h] at hsum
  norm_num at hsum
  omega

end ExponentTwo

section Existence

/-! ### `IsMotzkin` is SATISFIABLE — so the refutations are not vacuous

`IsMotzkin` is a characterisation, and until now nothing produced one: all forty-two
declarations in this file are implications from `IsMotzkin m`, including `not_conj7` and
`not_conj7_third`.  **Had `IsMotzkin` been unsatisfiable, every one of them would have been
vacuously true while reading as content**, and "Conjecture 7 is refuted" would have refuted
nothing.  No gate could see it: a vacuous theorem is axiom-free, its hypothesis IS used in its
proof, and it is gated like any other.

Mathlib has no Motzkin numbers, so the sequence is built here from the source's own recurrence.
The recursion is well-founded rather than structural, because the `n+2` case calls `motSeq` at
every `k ≤ n`; summing over `(range (n+1)).attach` is what puts `k < n+1` in scope for the
termination proof, and `Finset.sum_attach` converts back to the plain sum the spec states.

`isMotzkin_unique` records that the characterisation pins the sequence, which is what justifies
the module's design note that its theorems hold "for whatever encoding satisfies the equation":
there is exactly one.
-/

/-- The Motzkin sequence, CONSTRUCTED from the source's defining equation. -/
def motSeq : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (n + 2) =>
      motSeq (n + 1) + ∑ k ∈ (Finset.range (n + 1)).attach, motSeq k.1 * motSeq (n - k.1)
decreasing_by
  all_goals
    first
      | omega
      | (have hk := Finset.mem_range.mp k.2
         omega)

theorem motSeq_zero : motSeq 0 = 1 := by rw [motSeq]

theorem motSeq_one : motSeq 1 = 1 := by rw [motSeq]

theorem motSeq_step (n : ℕ) :
    motSeq (n + 2) = motSeq (n + 1) + ∑ k ∈ range (n + 1), motSeq k * motSeq (n - k) := by
  conv_lhs => rw [motSeq]
  congr 1
  exact Finset.sum_attach (range (n + 1)) (fun k => motSeq k * motSeq (n - k))

/-- **The constructed sequence satisfies the source's equation.** -/
theorem isMotzkin_motSeq : IsMotzkin motSeq where
  zero := motSeq_zero
  one := motSeq_one
  step := motSeq_step

/-- **`IsMotzkin` is satisfiable.**  Without this, every theorem in this file could be vacuous. -/
theorem exists_isMotzkin : ∃ m : ℕ → ℤ, IsMotzkin m := ⟨motSeq, isMotzkin_motSeq⟩

theorem isMotzkin_agree {m m' : ℕ → ℤ} (h : IsMotzkin m) (h' : IsMotzkin m') :
    ∀ n, ∀ k ≤ n, m k = m' k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [h.zero, h'.zero]
  | succ t ih =>
      intro k hk
      rcases Nat.lt_or_ge k (t + 1) with hlt | hge
      · exact ih k (by omega)
      · have hk1 : k = t + 1 := by omega
        subst hk1
        match t with
        | 0 => rw [h.one, h'.one]
        | (j + 1) =>
            rw [show j + 1 + 1 = j + 2 from rfl, h.step j, h'.step j, ih (j + 1) (by omega)]
            congr 1
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have hir := Finset.mem_range.mp hi
            rw [ih i (by omega), ih (j - i) (by omega)]

/-- **The characterisation pins the sequence**: any two sequences satisfying the source's
equation are equal.  This is what makes "for whatever encoding satisfies the equation" a
statement about exactly one sequence. -/
theorem isMotzkin_unique {m m' : ℕ → ℤ} (h : IsMotzkin m) (h' : IsMotzkin m') : m = m' := by
  funext n
  exact isMotzkin_agree h h' n n le_rfl

/-- **Conjecture 7's first display is false, with no hypothesis at all.** -/
theorem not_conj7_uncond : ¬ Conj7First (qt motSeq) 4 0 := not_conj7 isMotzkin_motSeq

/-- **Conjecture 7's third display is false, with no hypothesis at all** — the write-up's
headline discrepancy, at `r = 4`, `n = 0`. -/
theorem not_conj7_third_uncond : ¬ Conj7Third (qt motSeq) 4 0 :=
  not_conj7_third isMotzkin_motSeq

/-- **And at `r = 2`, where the first two displays hold** — so the third display is defective on
its own, unconditionally. -/
theorem not_conj7_third_two_uncond : ¬ Conj7Third (sq motSeq) 2 0 :=
  not_conj7_third_two isMotzkin_motSeq

end Existence

end Principia.MathDB.P367324
