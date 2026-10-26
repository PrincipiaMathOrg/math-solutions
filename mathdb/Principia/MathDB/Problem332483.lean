import Mathlib.Data.Rat.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

/-!
# MathDB #332483 — iterated Catalan–Larcombe–French ratios are NOT alternately log-convex

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/332483/solution.tex`, refuting Conjecture 5.2 of Sun and Zhao: for
each `k ≥ 1`, the ratio iterate `(𝓡^k P)_n`, with its first `k` terms deleted, is log-concave for
odd `k` and log-convex for even `k`.

**The objects.**  The Catalan–Larcombe–French numbers are `P₀ = 1`, `P₁ = 8` and
`n² Pₙ = 8(3n² − 3n + 1) Pₙ₋₁ − 128(n − 1)² Pₙ₋₂` for `n ≥ 2`; `(𝓡a)ₙ = aₙ₊₁ / aₙ`.  `Pp n` below
is the pair `(Pₙ, Pₙ₊₁)`, computed along the recurrence so that each value is evaluated once; its
step at `n + 1` is the recurrence at index `m = n + 2`.  `P` is its first component, and agrees
with the write-up's table (checked in Python for every `n ≤ 26`).

**What is refuted, and why it is stated weakly.**  `CLFConj` keeps only the EVEN-`k`, log-convex
half, and only asks `bₙ₊₁² ≤ bₙ bₙ₊₂` at retained indices `n ≥ k`.  Dropping the odd half and
using the unsquared-root form weakens the conjecture, so refuting it refutes the source.  The
sequence is positive, as the source's ratio operator presupposes (`P_pos`).

**The witness.**  With `b = 𝓡¹² P`, `b₁₂ b₁₄ < b₁₃²`.  The write-up certifies this through the
integer products `A` and `B`; here the rational values themselves are compared by kernel
evaluation.  They are large — `b₁₃`'s numerator has about 29,000 digits — but finite.  In Python,
`(k, n) = (12, 12)` is the only failure of the even clause among all indices the first 27 terms
reach, so this is the witness the write-up names and not a nearby one.
-/

namespace Principia.MathDB.P332483

/-- `(Pₙ, Pₙ₊₁)` for the Catalan–Larcombe–French numbers, along the recurrence. -/
def Pp : ℕ → ℚ × ℚ
  | 0 => (1, 8)
  | n + 1 =>
    ((Pp n).2,
      (8 * (3 * ((n : ℚ) + 2) ^ 2 - 3 * ((n : ℚ) + 2) + 1) * (Pp n).2 -
        128 * ((n : ℚ) + 1) ^ 2 * (Pp n).1) / ((n : ℚ) + 2) ^ 2)

/-- The Catalan–Larcombe–French numbers. -/
def P (n : ℕ) : ℚ := (Pp n).1

/-- The ratio operator `(𝓡a)ₙ = aₙ₊₁ / aₙ`. -/
def Rop (a : ℕ → ℚ) : ℕ → ℚ := fun n => a (n + 1) / a n

/-- Sun–Zhao Conjecture 5.2, even-`k` (log-convex) half only — a weakening of the source. -/
def CLFConj : Prop :=
  ∀ k n : ℕ, 1 ≤ k → Even k → k ≤ n →
    (Rop^[k] P) (n + 1) ^ 2 ≤ (Rop^[k] P) n * (Rop^[k] P) (n + 2)

/-- The recurrence reproduces the write-up's table at its first and last entries. -/
theorem P_table : P 12 = 15008466534400 ∧ P 26 = 497042117469860910740195508224 := by
  decide +kernel

/-- Every term the witness reads is positive, so the ratio operator is well defined there. -/
theorem P_pos : ∀ n, n ≤ 26 → 0 < P n := by
  decide +kernel

/-- **The twelfth ratio iterate fails log-convexity at `n = 12`.** -/
theorem witness : (Rop^[12] P) 12 * (Rop^[12] P) 14 < (Rop^[12] P) 13 ^ 2 := by
  decide +kernel

/-- **MathDB #332483: Sun–Zhao Conjecture 5.2 is false.** -/
theorem not_clfConj : ¬ CLFConj := by
  intro h
  have h12 : (Rop^[12] P) 13 ^ 2 ≤ (Rop^[12] P) 12 * (Rop^[12] P) 14 :=
    h 12 12 (by norm_num) ⟨6, rfl⟩ le_rfl
  exact absurd h12 (not_le.mpr witness)

end Principia.MathDB.P332483
