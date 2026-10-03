import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
-- PNT+'s lakefile turns these three style linters off; mirrored here
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.openClassical false

/-!
# PNT+ port: `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`

Ported from PrimeNumberTheoremAnd (PNT+, Kontorovich-Tao et al., Apache 2.0), file
`PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` at commit d963a6e694a05cd82e5f9b9ae7f4d94123e85393
(built there against Mathlib db127794; here against the Mathlib v4.31.0 tag).
Port changes: LeanArchitect `@[blueprint ...]` attributes removed (titles and statements
kept as docstrings), `blueprint_comment` turned into module docstrings, imports of
`PrimeNumberTheoremAnd.*` rewired to `Principia.Common.*`.  Declaration names and
namespaces are unchanged; proofs are byte-identical to PNT+.

Contents: `Real.tendsto_pow_log_div_pow_atTop`.
-/

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
