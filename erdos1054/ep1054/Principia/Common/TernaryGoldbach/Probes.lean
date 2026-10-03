/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Reduction
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

/-!
# `ternaryLogCount` is not a definition that does no work

The project's most expensive recurring error is a decomposition whose pieces can be satisfied by
something degenerate — "a restatement wearing the syntax of a reduction". `Reduction.lean` hands
the ternary-Goldbach programme a new obligation, `TernaryLogCountLower`, so the obligation has to
be attacked adversarially before anything is built on it. This file records the attacks that can
be made *mechanically*, as theorems rather than as prose.

Three of them, and what each rules out:

* `ternaryLogCount_eq_zero_of_even` — for **even** `H` the count is exactly `0`, because three odd
  numbers sum to an odd number. So the `Odd H` hypothesis in `TernaryLogCountLower` is
  load-bearing: drop it and the obligation is *false*, not merely stronger. This also settles the
  **boundary case** `H = 0` (`Even 0`), where the sum is empty.
* `ternaryLogCount_nine` — `ternaryLogCount 9 = (log 3)³` **exactly**, evaluated by the kernel over
  all 81 index pairs. So the definition is not identically zero (the failure mode a wrong cast or a
  mis-transcribed guard would produce), and it demonstrates the two conventions the docstring
  claims: `9 = 3 + 3 + 3` contributes the **diagonal** ordered pair `(3, 3)`, once.
* `ternaryLogCount_nine_pos` — the same fact as a strict positivity statement.

The attack that matters most is **not** here, because it belongs with the reduction: the degenerate
witness for `Cite_Helfgott_weighted` is a degenerate *weighting*. Setting `ηp = ηs = 0` satisfies
both sup-norm constraints and makes the smoothed sum `0`, which fails `0.000422 · H² ≤ 0` for
`H ≥ 10^27` — so the input is not vacuous. And `Reduction.weightedCount_le` proves that **no**
admissible weighting, signed or not, can satisfy the input unless `ternaryLogCount H` is genuinely
`≥ 0.000422 / 1.64915… · H²`. The degenerate-weighting attack is therefore refuted by a theorem,
not by inspection.

The separate module is deliberate: `Reduction.lean` imports exactly what
`Principia.Erdos1054.Statements.Inputs` imports and nothing else, so that its `Iff.rfl`
transcription probe cannot be perturbed by an instance arriving from a new import. The `norm_num`
prime extension needed below is therefore confined to this file.
-/

namespace Principia.Common.TernaryGoldbach

/-- **`Odd H` is load-bearing, and `H = 0` is covered.** Three odd summands sum to an odd number,
so for even `H` every guard in `ternaryLogCount H` fails and the count is `0`. Dropping `Odd H`
from `TernaryLogCountLower` would make it false rather than stronger. -/
theorem ternaryLogCount_eq_zero_of_even {H : ℕ} (hH : Even H) : ternaryLogCount H = 0 := by
  simp only [ternaryLogCount]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  split
  · rename_i hc
    obtain ⟨hpq, -, -, -, hop, hoq, hor⟩ := hc
    exfalso
    have hsum : p + q + (H - p - q) = H := by omega
    have hodd : Odd H := by
      rw [← hsum]
      exact (hop.add_odd hoq).add_odd hor
    have h0 := Nat.even_iff.mp hH
    have h1 := Nat.odd_iff.mp hodd
    omega
  · rfl

/-- **The count really counts, and the diagonal is included.** `9 = 3 + 3 + 3` is the only
representation of `9` by three odd primes, and it enters as the single ordered pair `(3, 3)`, so
`ternaryLogCount 9 = (log 3)³`. Checked by the kernel over all `81` pairs of `Finset.range 9`. -/
theorem ternaryLogCount_nine : ternaryLogCount 9 = Real.log 3 * Real.log 3 * Real.log 3 := by
  simp only [ternaryLogCount, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.odd_iff]

/-- `ternaryLogCount` is not identically zero. -/
theorem ternaryLogCount_nine_pos : 0 < ternaryLogCount 9 := by
  rw [ternaryLogCount_nine]
  have h : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  positivity

end Principia.Common.TernaryGoldbach
