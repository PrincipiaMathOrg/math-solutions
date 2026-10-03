/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorC0

set_option autoImplicit false

/-!
# The split at the Chebyshev reduction: `HelfgottAt 0.000205` against minor `1.0154`

GENERATED (`scratchpad/cheb/gen_cheb.py`) by counted substitution from the verified
`MC0.helfAt_smooth_c0`, `MC0.helfgottAt_c0` (`MajorC0.lean`) and `OC.close_mnum_c`
(`OstopC.lean`); every stale constant is asserted absent from the copies. The major side is
CALLED, not copied (`MC0.majorAt_c0`), so the major constant stays `1.0563699` (`C₀ ≥ 1.3198`).

What changed is the consumer. `BalancedT0.balanced_of_cheb` reduces EP1054 to
`HelfgottAt 0.000205` (Chebyshev's `θ(t) ≤ 1.11 t` on `[3·10⁹, ∞)`), where `BalancedK` needed
`0.00032`. The split's side condition relaxes, and all of the room goes to the minor arcs.

## The arithmetic (exact rationals, `scratchpad/cheb/price_cheb.py`)

* **the split** (`helfAt_smooth_cheb`): `(1.0563699 − 1.0154)(490/989)²/49 − 13.73·10⁻⁹ =
  2.0522929·10⁻⁴ ≥ 0.000205` (margin `2.29·10⁻⁷`). The largest minor constant that closes is
  `1.01544577…`; `1.0154` keeps `4.58·10⁻⁵` of it. Against `K = 0.00032` it was `0.9924888`.
* **the minor side** (`helfgottAt_cheb`): the single hypothesis `RT.MinorUpperAt 1.0154 η₊ η*`.
  The minor chain on file (`OC.OstopC`, `OC.MNumC`) carries Helfgott's PRINTED minor-arc
  constant, which is wrong (LEAN-PROGRESS 2026-09-30), so the minor arcs enter as one named
  obligation at the raised constant.
* **the closing arithmetic** (`close_cheb`): `(√(1.2533143·(0.8095 + 3.7·10⁻⁴)) + √1.0532·10⁻¹¹)²
  = 1.0150282 ≤ 1.0154` (margin `3.72·10⁻⁴`, on `MinSp.close_num`). The largest admissible `M` is
  `0.8097966` (it was `0.7915162` at `0.9924888`), so a corrected minor chain in the shape of
  `OC.minorAt_mnum_c` attaches to `1.0154` if it delivers `M ≤ 0.8095`.
-/

namespace Principia.Common.TernaryGoldbach.SC

open MeasureTheory Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.EN
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-- **THE CHEBYSHEV SPLIT** (generated from `MC0.helfAt_smooth_c0`): the sup norms, the
major arcs at `1.0563699` and the minor arcs at `1.0154` give `HelfgottAt 0.000205`;
`(0.0409699)(490/989)²/49 − 13.73·10⁻⁹ = 2.0522929·10⁻⁴ ≥ 0.000205`. -/
theorem helfAt_smooth_cheb (ηp ηs : ℝ → ℝ) (sb : Smooth.SupBounds ηp ηs)
    (mj : RT.MajorLowerAt 1.0563699 ηp ηs) (mn : RT.MinorUpperAt 1.0154 ηp ηs) :
    HelfgottAt 0.000205 := by
  have sm := RT.summ_of_majorAt (by norm_num) ηp ηs mj
  have ci := SmCI.circleId_of_summ ηp ηs sm
  refine (RT.helfgottAt_iff 0.000205).mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := RT.weighted_lower_at 1.0563699 1.0154 ηp ηs sm ci mj mn H hodd hH
  have hc : (1.0563699 - 1.0154 : ℝ) = 0.0409699 := by norm_num
  rw [hc] at hW
  have hP := SmPP.pp_crude ηp ηs sb H hodd hH
  have hH0 : (0 : ℝ) ≤ (490 : ℝ) / 989 * H := by positivity
  have hx2 : ((490 : ℝ) / 989 * H) ^ 2 ≤ helfgottX H ^ 2 :=
    pow_le_pow_left₀ hH0 (Smooth.helfX_ge H) 2
  have hx2' : (490 : ℝ) ^ 2 / 989 ^ 2 * (H : ℝ) ^ 2 ≤ helfgottX H ^ 2 :=
    le_of_eq_of_le (by ring) hx2
  have hE := SmPP.ppErr_le H hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **`HelfgottAt 0.000205` on Helfgott's weights with the major arcs at `C₀ ≥ 1.3198`** (generated
from `MC0.helfgottAt_c0`): the minor side is the single hypothesis
`RT.MinorUpperAt 1.0154 η₊ η*`. -/
theorem helfgottAt_cheb (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : RW.RegW HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc) (dj : DS.DrujalE100 HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp27)
    (mn : RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar) : HelfgottAt 0.000205 :=
  helfAt_smooth_cheb HW.etaPlus HW.etaStar BL.supBounds_helf
    (MC0.majorAt_c0 HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm
      RT.starScale_helf rg nf dj cl (normsB27_helf hb) supN_helf pf) mn

/-- **The corrected minor chain closes at the Chebyshev split's minor target**:
`(√(1.2533143·0.80987) + √1.0532·10⁻¹¹)² = 1.0150282 ≤ 1.0154` (exact rationals;
`M ≤ 0.8097966` is the edge). -/
theorem close_cheb : (Real.sqrt (1.2533143 * (0.8095 + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    1.0154 :=
  MinSp.close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Principia.Common.TernaryGoldbach.SC
