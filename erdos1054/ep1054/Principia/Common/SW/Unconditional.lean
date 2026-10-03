/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.Rate
import Principia.Common.PNT.Medium.Bound

/-!
# Siegel–Walfisz, unconditional

`Principia.Common.SW.Rate` proves Siegel–Walfisz (`siegel_walfisz_of_mediumPNT`) from the
hypothesis `MediumPNTBound`, the explicit prime number theorem
`|ψ(x) − x| ≤ C·x·exp(−c(log x)^{1/10})` for `x ≥ 2`, because PNT+ pinned another Mathlib and
could not be imported. `Principia.Common.PNT.Medium` ports PNT+'s `MediumPNT` and its closure;
`Principia.Common.PNT.Medium.medium_PNT` is `MediumPNT` in exactly the form `MediumPNTBound`
states. This file discharges the hypothesis:

* `mediumPNTBound : MediumPNTBound`;
* `siegel_walfisz_unconditional` — the conclusion of `siegel_walfisz_of_mediumPNT`, with no
  hypothesis beyond `1 ≤ B`: for every `B ≥ 1` there are `c, C > 0` and `X₀` such that for all
  `X ≥ X₀`, every modulus `q ≤ (log X)^B` and every unit class `a mod q`,
  `|ψ(X; q, a) − X/φ(q)| ≤ C·X·exp(−c(log X)^{1/10})`. The constant is ineffective (Siegel).
-/

set_option autoImplicit false

namespace Principia.Common.SW

/-- The explicit prime number theorem `MediumPNTBound`, proved: it is
`Principia.Common.PNT.Medium.medium_PNT` (PNT+'s `MediumPNT`, ported). -/
theorem mediumPNTBound : MediumPNTBound :=
  Principia.Common.PNT.Medium.medium_PNT

open scoped Classical in
open ArithmeticFunction in
/-- **Siegel–Walfisz, unconditional**: `siegel_walfisz_of_mediumPNT` with its `MediumPNTBound`
hypothesis discharged by `mediumPNTBound`. -/
theorem siegel_walfisz_unconditional (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log X ^ (B : ℝ) →
    ∀ a : ZMod q, IsUnit a →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), if a = ((n : ZMod q)) then vonMangoldt n else 0)
      - X / q.totient| ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10)) :=
  siegel_walfisz_of_mediumPNT mediumPNTBound B hB

end Principia.Common.SW
