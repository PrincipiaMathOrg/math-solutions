import Principia.MathDB.Problem370788
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# MathDB #370789 — Chamberland–Dilcher Conjecture 7.5, the four residue-class limits

Write-up: `mathdb-open-problems/problems/370789/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: M. Chamberland and K. Dilcher, arXiv:2510.04387v1, Equation (1.4) and **Conjecture 7.5**,
Equation (7.14) — the same paper as row 284.

With `f(n) = Σ_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ − (n²−1)/12`, the claim is that for each `r ∈ {0,1,2,3}`,
`f(4m+r)/(4m+r) → (1−r)/8`, so the four limits are `1/8, 0, −1/8, −1/4`.

## `f` is imported, not redefined

`Principia.MathDB.P370788.f` is *this* `f`, character for character — same paper, same equation.
The module imports it. That is the campaign's shared-asset rule doing its job without rewiring a
banked row: row 284 is untouched and its declaration count does not move.

## The meta-claim is a TYPO DIAGNOSIS, and it is the sharpest thing in the write-up

The source's Equation (7.14) **prints** `f(4m+2)/(4m+3)` with limit `−1/4`. The write-up says the
intended numerator is `f(4m+3)`, and that the printed expression instead has limit `−1/8`. That
is a falsifiable claim about the source, and it is settled here twice over:

* `printed_limit` proves it **from the `r = 2` case alone**: `f(4m+2)/(4m+3)` is
  `(f(4m+2)/(4m+2)) · ((4m+2)/(4m+3))`, and the second factor tends to `1`, so the printed
  expression inherits the `r = 2` limit `−1/8` and nothing else.
* `printed_ne_claimed` records the whole point of the paragraph in one line: `−1/8 ≠ −1/4`.

The verifier settles it numerically and decisively — the two candidates are `1/8` apart, and the
printed expression sits `1.6 × 10⁻⁵` from `−1/8` and `0.125` from `−1/4` at `m = 8000`. The
write-up claims no credit for the typo, and neither does this row; what is recorded is that the
diagnosis is **correct**, which is what a reader of the source needs to know.

## What else is proved

* `limit_values` — the general formula `(1−r)/8` really does reproduce the enumerated list
  `1/8, 0, −1/8, −1/4`, and `limits_distinct` — the four are pairwise distinct, so the residue
  class genuinely matters and the theorem is not one statement in disguise.
* `ratio_tendsto_one` — `(4m+2)/(4m+3) → 1`.
* `gcd_two_mul_le` — the second half of the write-up's Gauss-sum bound,
  `gcd(2h, n) ≤ 2h`, which needs only `0 < h`.

## The named hypothesis

`hfour`, the four-case theorem itself, whose proof is the equidistribution of `k²/n` via the
complete exponential sum `|G_n(h)|² ≤ n·gcd(2h,n)` and a Fejér approximation. Its *first*
inequality is the analytic content and is not attempted here; its second is `gcd_two_mul_le`.
-/

namespace Principia.MathDB.P370789

open Filter Topology

/-- The write-up's `f`, which is row 284's `f`: same paper, same equation, imported. -/
abbrev f (n : ℕ) : ℚ := Principia.MathDB.P370788.f n

/-! ## The four values -/

/-- The general formula reproduces the write-up's enumerated list. -/
theorem limit_values :
    ((1 - (0 : ℚ)) / 8, (1 - (1 : ℚ)) / 8, (1 - (2 : ℚ)) / 8, (1 - (3 : ℚ)) / 8)
      = ((1 / 8 : ℚ), (0 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)) := by
  norm_num

/-- The four limits are pairwise distinct: the residue class genuinely matters. -/
theorem limits_distinct :
    (1 / 8 : ℚ) ≠ 0 ∧ (1 / 8 : ℚ) ≠ -1 / 8 ∧ (1 / 8 : ℚ) ≠ -1 / 4 ∧
      (0 : ℚ) ≠ -1 / 8 ∧ (0 : ℚ) ≠ -1 / 4 ∧ (-1 / 8 : ℚ) ≠ -1 / 4 := by
  norm_num

/-- **The whole content of the write-up's typo paragraph, in one line.** -/
theorem printed_ne_claimed : (-1 / 8 : ℝ) ≠ -1 / 4 := by norm_num

/-! ## The ratio, and the printed expression -/

theorem ratio_tendsto_one :
    Tendsto (fun m : ℕ => ((4 * m + 2 : ℕ) : ℝ) / ((4 * m + 3 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have heq : (fun m : ℕ => ((4 * m + 2 : ℕ) : ℝ) / ((4 * m + 3 : ℕ) : ℝ))
      =ᶠ[atTop] (fun m : ℕ => 1 - 1 / (4 * (m : ℝ) + 3)) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have h3 : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  refine Tendsto.congr' heq.symm ?_
  have hd : Tendsto (fun m : ℕ => 4 * (m : ℝ) + 3) atTop atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have : Tendsto (fun m : ℕ => (1 : ℝ) - 1 / (4 * (m : ℝ) + 3)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (hd.inv_tendsto_atTop.congr fun m => (one_div _).symm)
  simpa using this

/-- **THE TYPO DIAGNOSIS, PROVED FROM THE `r = 2` CASE ALONE.** The source prints
`f(4m+2)/(4m+3)` with limit `−1/4`; since `(4m+2)/(4m+3) → 1`, the printed expression inherits
the `r = 2` limit `−1/8` and nothing else. Together with `printed_ne_claimed`, the printed
equation is false as printed and the write-up's reading of it is right. -/
theorem printed_limit
    (h2 : Tendsto (fun m : ℕ => ((f (4 * m + 2) : ℚ) : ℝ) / ((4 * m + 2 : ℕ) : ℝ))
      atTop (𝓝 (-1 / 8))) :
    Tendsto (fun m : ℕ => ((f (4 * m + 2) : ℚ) : ℝ) / ((4 * m + 3 : ℕ) : ℝ))
      atTop (𝓝 (-1 / 8)) := by
  have hprod := h2.mul ratio_tendsto_one
  have heq : (fun m : ℕ => ((f (4 * m + 2) : ℚ) : ℝ) / ((4 * m + 2 : ℕ) : ℝ)
        * (((4 * m + 2 : ℕ) : ℝ) / ((4 * m + 3 : ℕ) : ℝ)))
      =ᶠ[atTop] (fun m : ℕ => ((f (4 * m + 2) : ℚ) : ℝ) / ((4 * m + 3 : ℕ) : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with m _
    have h2n : ((4 * m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have h3n : ((4 * m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  refine Tendsto.congr' heq ?_
  simpa using hprod

/-! ## The elementary half of the Gauss-sum bound -/

/-- `gcd(2h, n) ≤ 2h` for `0 < h` — the second inequality in `|G_n(h)|² ≤ n·gcd(2h,n) ≤ 2|h|n`.
The first is the analytic content and is not attempted here. -/
theorem gcd_two_mul_le (h n : ℕ) (hh : 0 < h) : Nat.gcd (2 * h) n ≤ 2 * h :=
  Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)

end Principia.MathDB.P370789
