/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorR
import Principia.Erdos1054.Alt7.FromOstopL

set_option autoImplicit false

/-!
# EP1054 on HelfMaj RETYPED (`MR.HelfMajR`): the major-arc input at constants its proofs establish

`FromOstopL.ep1054_ostopL` takes `RT.HelfMajFull`, Helfgott's PRINTED majarcs constants, which the
adversarial referee of 2026-09-30 found NOT established by his proofs (F1, F2, F4, N1). This file
composes the same headline from `MR.HelfMajR`, the referee's retype, with every consumer
regenerated (`MajorR.lean`):

* **major arcs**: `MR.helfgottAt_chebR` — `c_maj' = 1.0563578` (was `1.0563699`), the split
  `K = 2.0516868·10⁻⁴ ≥ 0.000205`, so the minor target stays `1.0154`;
* **minor arcs**: `MR.minorAt_ostopL_chebR` — the `J` floor `8.55451` (was `8.57476`) from
  `MR.drujalLowPR_of_spine`, `p₀ = 8.54` survives (`(√8.55451 − √8.4031·10⁻¹²)² = 8.5544930`),
  the closing constant `cM = 0.8095` is unchanged;
* **`OL.FelipaAt 0.6406` LEAVES the headline**: it is derived from `MalheurR` (`0.640212 ≤ 0.6406`).

`ep1054_majR_of_ostopL` shows `ep1054_majR`'s hypotheses follow from `ep1054_ostopL`'s (through
`MR.helfMajR_of_full`; `hfe` is not needed), so the new headline is NO STRONGER.

Open, on Helfgott's fixed weights: `MR.HelfMajR`, `RW.NefumoW`, `DS.PerArc`, `DS.ArcInt`,
`OL.OstopL`, `OL.MNumL HW.phi 8.54 0.8095 0.6406`. Cited: `PC.PlattThm71`, `PC.PlattTrudgian`.
-/

namespace Principia.Erdos1054.Alt7.FromMajR

open Principia.Common.TernaryGoldbach

/-- **EP1054 on HelfMaj RETYPED.** Platt's Theorem 7.1, Platt–Trudgian, `HelfMajR` (the refereed
major-arc input), `NefumoW`, the two `lem:drujal` links, the corrected `thm:ostop` and its `M̃`
numerics. `FelipaAt` is derived. Application only. -/
theorem ep1054_majR (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (hos : OL.OstopL HW.etaPlus HW.etaStar HW.phi)
    (hmn : OL.MNumL HW.phi 8.54 0.8095 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  Round7Bal.ep1054_all_bal (Proofs.BalancedT0.balanced_of_cheb
    (MR.helfgottAt_chebR (PC.plattFull_of_cited p z) hr RW.regW_helf nf
      (MR.drujalE100R_of_spine HW.etaPlus pa ai DP.mardiQ_helf KS.ksmall_helf) CT.clowerE_helf
      BS.band_sharp
      (MR.minorAt_ostopL_chebR (PC.plattFull_of_cited p z) hr hos
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc pa ai DP.bandQ_helf DP.tailQ_helf
          KS.ksmall_helf) hmn)))

/-- **`ep1054_majR` is no stronger than `ep1054_ostopL`**: from `ep1054_ostopL`'s hypotheses (its
`hfe : OL.FelipaAt 0.6406 η₊` is not needed), `MR.helfMajR_of_full` supplies `HelfMajR` and every
other hypothesis passes through unchanged. Application only. -/
theorem ep1054_majR_of_ostopL (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (hos : OL.OstopL HW.etaPlus HW.etaStar HW.phi)
    (hmn : OL.MNumL HW.phi 8.54 0.8095 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_majR p z (MR.helfMajR_of_full _ _ hm) nf pa ai hos hmn

end Principia.Erdos1054.Alt7.FromMajR
