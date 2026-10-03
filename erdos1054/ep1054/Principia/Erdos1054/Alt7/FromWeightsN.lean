/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromWeightsP
import Principia.Common.TernaryGoldbach.NefumoClose

set_option autoImplicit false

/-!
# The finest EP1054 headline: corrected Main Theorem + weight-aware split + `prop:nefumo` closed

`FromWeightsP.ep1054_weightsP` (the corrected Main Theorem `(0.811, 45.7575)` through the
weight-aware split, `cM = 0.84`) still takes `NF.Massacre`, `NF.GatTail`, `NF.T3W`, `NF.JokoW`.
`NefumoClose` PROVES the first three (`NC.massacre`, `NC.gatTail`, `NC.t3W_helf`) and derives
`JokoW` from `NF.ZvsL η_*` (`NC.jokoW_helf`); `FromNefumo` supplied them only to the typed-`L`
headlines. This file supplies them here. Application only.

Open, on Helfgott's fixed weights: `MR.HelfMajR`, `NF.ZvsL η_*`, `CY.EspagnWin 1.36`,
`c_E ≥ 1.3325822` (leaves when `c⁻ = −1.39` is threaded: `CYm.coeurY139_closed`, `CEL.cE_ge`),
`OP.MinMainP 0.811 45.7575` (or its pieces), `GS.RS62Thm15`, `GS.Austeria`, `OS.EBound2`,
`OP.MNumP 0.811 45.7575 φ 8.54 0.84 0.6406`. Cited: `PC.PlattThm71`, `PC.PlattTrudgian`.
-/

namespace Principia.Erdos1054.Alt7.FromWeightsN

open Principia.Common.TernaryGoldbach

/-- **THE FINEST HEADLINE.** `FromWeightsP.ep1054_weightsP` with `Massacre`, `GatTail`, `T3W`
PROVED and `JokoW` from `ZvsL η_*`. Application only. -/
theorem ep1054_top (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (zs : NF.ZvsL HW.etaStar)
    (hesp : CY.EspagnWin 1.36) (hce : 1.3325822 ≤ CY.cE)
    (hmm : OP.MinMainP 0.811 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) (hmn : OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromWeightsP.ep1054_weightsP p z hr NC.massacre NC.gatTail NC.t3W_helf (NC.jokoW_helf zs) hesp
    hce hmm h15 hau heb hmn

/-- **The same, with the Main Theorem from its Totals pieces** (`FromWeightsP.ep1054_piecesP`). -/
theorem ep1054_top_pieces (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (zs : NF.ZvsL HW.etaStar)
    (hesp : CY.EspagnWin 1.36) (hce : 1.3325822 ≤ CY.cE)
    (h1 : MMP.TypeI1W) (h2 : MT.TypeI2) (h3 : MT.TypeII) (h4 : MT.MinMain2L)
    (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) (hmn : OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromWeightsP.ep1054_piecesP p z hr NC.massacre NC.gatTail NC.t3W_helf (NC.jokoW_helf zs) hesp
    hce h1 h2 h3 h4 h15 hau heb hmn

end Principia.Erdos1054.Alt7.FromWeightsN
