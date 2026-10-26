import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# MathDB #347493 — the Dilcher–Ulas polynomials are NOT infinitely log-concave

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/347493/solution.tex`, refuting the conjecture of Dilcher and Ulas
that `(f_n(z))_{n ≥ 0}`, with `f_n(z) = ∑_{j=0}^{n} C(n, j) z^{C(j, 2)}`, is infinitely log-concave
for every `0 ≤ z ≤ 1`.

**The objects.**  `𝓛(a)_n = a_n² − a_{n−1} a_{n+1}`, and a sequence is infinitely log-concave when
every iterate `𝓛^r(a)` is nonnegative.

**What is refuted, and why it is stated weakly.**  `DUConj` asks only for `𝓛^r(f(z))_n ≥ 0` with
`r ≤ n`, and only at rational `z`.  Both restrictions weaken the conjecture: the rational points
are among the real ones, and `r ≤ n` keeps every index the iterate reads at `n − r ≥ 0`, so the
statement does not depend on any convention for `a_{−1}` — which the source never needs either.
`Lop` writes `a (n - 1)` with natural-number subtraction; on the indices `DUConj` reaches that is
always a genuine `n − 1`.

**The witness.**  At `z = 3/10`, `𝓛⁶(f)₆ < −63 / 10³⁶`.  It reads only `f₀, …, f₁₂`.  The value is
an exact rational (its denominator has 1,153 digits), so the inequality is a finite computation,
closed by kernel evaluation.  Checked against the write-up's own exact-arithmetic certificate in
Python before this file was written.
-/

namespace Principia.MathDB.P347493

open Finset

/-- `f_n(z) = ∑_{j=0}^{n} C(n, j) z^{C(j, 2)}`. -/
def f (z : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ range (n + 1), (n.choose j : ℚ) * z ^ (j.choose 2)

/-- The log-concavity operator `𝓛(a)_n = a_n² − a_{n−1} a_{n+1}`. -/
def Lop (a : ℕ → ℚ) : ℕ → ℚ :=
  fun n => a n ^ 2 - a (n - 1) * a (n + 1)

/-- The Dilcher–Ulas conjecture, weakened to rational `z` and to iterates with `r ≤ n`. -/
def DUConj : Prop :=
  ∀ z : ℚ, 0 ≤ z → z ≤ 1 → ∀ r n : ℕ, r ≤ n → 0 ≤ (Lop^[r] (f z)) n

/-- **The sixth iterate at index six is negative at `z = 3/10`**, with the write-up's margin. -/
theorem iterate_six_neg : (Lop^[6] (f (3 / 10))) 6 < -63 / 10 ^ 36 := by
  decide +kernel

/-- **MathDB #347493: the Dilcher–Ulas infinite log-concavity conjecture is false.** -/
theorem not_duConj : ¬ DUConj := by
  intro h
  have h6 := h (3 / 10) (by norm_num) (by norm_num) 6 6 le_rfl
  have hneg := iterate_six_neg
  have : (-63 : ℚ) / 10 ^ 36 < 0 := by norm_num
  linarith

end Principia.MathDB.P347493
