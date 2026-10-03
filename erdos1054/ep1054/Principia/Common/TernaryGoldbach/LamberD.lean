/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LamberW
import Principia.Common.TernaryGoldbach.DrujalSpine

set_option autoImplicit false

/-!
# `eq:lamber` at the `DrujalLowD` floor: `DS.LamberNumD HW.phi`, proved

The spine of `lem:drujal` lowers the minor floor to `p ≥ 8.3599` and restates `eq:lamber` there as
`DS.LamberNumD` (constant `3.7·10⁻⁴`; exact supremum `3.6075·10⁻⁴`). It is an instance of the
floor-parametric `LW.lamber_at`: the remaining cubic in `w = log(x/49) ≥ 57.558` has a `2.4 %`
margin (worst ratio `0.97599`, exact rationals).
-/

namespace Principia.Common.TernaryGoldbach.LD

/-- **`DS.LamberNumD HW.phi`** — `eq:lamber` at `p ≥ 8.3599`, `3.7·10⁻⁴`: PROVED. -/
theorem lamberNumD_helf : DS.LamberNumD HW.phi := by
  refine LW.lamber_at 8.3599 3.7e-4 (by norm_num) fun w L hw hL0 hL => ?_
  have hd := sub_nonneg.2 hw
  nlinarith [mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd]

end Principia.Common.TernaryGoldbach.LD
