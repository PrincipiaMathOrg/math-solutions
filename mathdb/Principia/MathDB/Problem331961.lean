import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# MathDB #331961 — Sun's sequence `R_n² − R_{n−1}R_{n+1}` is NOT infinitely log-concave

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/331961/solution.tex`, refuting Conjecture 4.8 of Brian Yi Sun:
with `R_n = ∑_{k=0}^{n} C(n,k) C(n+k,k) / (2k − 1)` and `a_n = R_n² − R_{n−1}R_{n+1}`, the sequence
`{a_n}_{n ≥ 6}` is infinitely log-concave.

**What is refuted, and why it is stated weakly.**  Infinite log-concavity requires every iterate
`𝓛^k a` to be nonnegative; the first of those requirements is ordinary log-concavity,
`a_n² − a_{n−1}a_{n+1} ≥ 0`.  `SunConj48` asks only for that, and only at indices `n ≥ 7`, where
`a_{n−1}, a_n, a_{n+1}` all lie in the stated subsequence `n ≥ 6`.  Refuting this weakest clause
refutes the conjecture under every iteration convention, and needs no convention for indices
below `6`.

**The witness.**  `R_5, …, R_9 = 329, 1359, 6001, 27759, 132689`; `a_6 = −127448`,
`a_7 = −1712480`, `a_8 = −25704608`; and `a_7² − a_6 a_8 = −343413129984 < 0`.  The binomial sums
are evaluated exactly over `ℚ` (the `k = 0` term has `1/(2k − 1) = −1`).  Checked in Python against
the write-up's values and the source recurrence before this file was written.
-/

namespace Principia.MathDB.P331961

open Finset

/-- `R_n = ∑_{k=0}^{n} C(n,k) C(n+k,k) / (2k − 1)`. -/
def R (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℚ) * ((n + k).choose k : ℚ) * (2 * (k : ℚ) - 1)⁻¹

/-- `a_n = R_n² − R_{n−1} R_{n+1}`. -/
def a (n : ℕ) : ℚ := R n ^ 2 - R (n - 1) * R (n + 1)

/-- Sun's Conjecture 4.8, first clause only: log-concavity of `{a_n}_{n ≥ 6}`. -/
def SunConj48 : Prop := ∀ n : ℕ, 7 ≤ n → 0 ≤ a n ^ 2 - a (n - 1) * a (n + 1)

/-- The write-up's table of `R_5, …, R_9`. -/
theorem R_table : R 5 = 329 ∧ R 6 = 1359 ∧ R 7 = 6001 ∧ R 8 = 27759 ∧ R 9 = 132689 := by
  decide +kernel

/-- `a_6, a_7, a_8`. -/
theorem a_values : a 6 = -127448 ∧ a 7 = -1712480 ∧ a 8 = -25704608 := by
  decide +kernel

/-- **The log-concavity test fails at `n = 7`.** -/
theorem witness : a 7 ^ 2 - a 6 * a 8 = -343413129984 := by
  decide +kernel

/-- **MathDB #331961: Sun's Conjecture 4.8 is false.** -/
theorem not_sunConj48 : ¬ SunConj48 := by
  intro h
  have h7 : 0 ≤ a 7 ^ 2 - a 6 * a 8 := h 7 le_rfl
  rw [witness] at h7
  norm_num at h7

end Principia.MathDB.P331961
