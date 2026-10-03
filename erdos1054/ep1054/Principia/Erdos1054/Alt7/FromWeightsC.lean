/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromWeightsN
import Principia.Common.TernaryGoldbach.OstopSpinePm
import Principia.Common.TernaryGoldbach.MNumPm

set_option autoImplicit false

/-!
# The finest EP1054 headline at `c⁻ = −1.39`: no `c_E` binder, no `M̃` binder

`FromWeightsN.ep1054_top` takes `1.3325822 ≤ c_E` only because its minor chain pins `cor:coeur`'s
`c⁻ = −1.306476`, and `OP.MNumP … 0.84` as a named link. Here the same composition runs on the
chain with `c⁻` a parameter (`OstopPm`, `OstopSpinePm`) at `(cm, jc) = (1.39, −3.627308)`:

* `CoeurY` is `CYm.coeurY139_closed` — from `EspagnWin 1.36` ALONE (`c_E ≥ 1.25` is proved,
  `CEL.cE_ge`); the `(1.3325822 ≤ c_E)` binder is GONE;
* the four `c⁻` sites of `M̃` all move: `H̃(r₀)` (`OPm.hR0Cm 1.39`), the weight
  `2/(log x − 2·1.39)`, `coefC`'s denominator, and its jump constant `−3.627308`
  (`OPm.jump_le_139`: exact `−3.62730816`, rounded up);
* `OPm.MNumPm 0.811 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406` is PROVED
  (`MNPm.mnumPm_proved`: certified margin `0.0031298`; float `sup M̃ = 0.8201014`);
* `Massacre`, `GatTail`, `T3W` are `NefumoClose`'s, `JokoW` comes from `ZvsL η_*`.

Generated from `FromWeightsP.ostopP_w`, `FromWeightsP.ep1054_weightsP`, `FromWeightsN.ep1054_top`
and `FromWeightsN.ep1054_top_pieces` by COUNTED substitution
(`scratchpad/ostoppm/gen_fromweightsc.py`). Application only.

Open, on Helfgott's fixed weights: `MR.HelfMajR`, `NF.ZvsL η_*`, `CY.EspagnWin 1.36`,
`OP.MinMainP 0.811 45.7575` (or its Totals pieces and second case), `GS.RS62Thm15`,
`GS.Austeria`, `OS.EBound2`. Cited: `PC.PlattThm71`, `PC.PlattTrudgian`.
-/

namespace Principia.Erdos1054.Alt7.FromWeightsC

open Principia.Common.TernaryGoldbach

/-- **The corrected `thm:ostop` at `(0.811, 45.7575)` and `c⁻ = −1.39` on Helfgott's weights**
(`OSPm.ostopPm_of_open`), `CoeurY` from `EspagnWin 1.36` alone and every numeric layer-2 link
supplied PROVED (generated from `FromWeightsP.ostopP_w`). Open: `EspagnWin 1.36`,
`MinMainP 0.811 45.7575`, `RS62Thm15`, `Austeria`, `EBound2`. -/
theorem ostopPm_w (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) (hesp : CY.EspagnWin 1.36)
    (hmm : OP.MinMainP 0.811 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) :
    OPm.OstopPm 0.811 45.7575 1.39 (-3.627308) HW.etaPlus HW.etaStar HW.phi :=
  OSPm.ostopPm_of_open 0.811 45.7575 1.39 (-3.627308) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) OPm.jump_le_139 (CYm.coeurY139_closed hesp HW.etaPlus) hmm h15
    MOP.gYMonoP MOP.hLeGP
    hau MOP.gtMonoP_helf (MOP.coprarP_of_R (PC.plattFull_of_cited p z) hr) heb
    (FromWeightsP.jgeE_w p z hr)
    MTOP.topStepP_helf

/-- **EP1054 through the weight-aware split at `c⁻ = −1.39`**, the `M̃` link named (generated from
`FromWeightsP.ep1054_weightsP`: `hce` removed, `OstopP ↦ OstopPm 1.39 (−3.627308)`,
`MNumP ↦ MNumPm`). Application only. -/
theorem ep1054_weightsC (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (ms : NF.Massacre) (gt : NF.GatTail) (t3 : NF.T3W HW.etaPlus HW.etaStar)
    (jk : NF.JokoW HW.etaPlus HW.etaStar)
    (hesp : CY.EspagnWin 1.36)
    (hmm : OP.MinMainP 0.811 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus)
    (hmn : OPm.MNumPm 0.811 45.7575 1.39 (-3.627308) HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  Round7Bal.ep1054_all_bal (Proofs.BalancedW.balanced_of_w
    (FromWeights.helfAtW_chebR
      (MR.majorAt_c0R HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hr
        RT.starScale_helf RW.regW_helf (NF.nefumoW_helf_rest ms gt t3 jk)
        (MR.drujalE100R_of_spine HW.etaPlus PA.perArc_helf AI.arcInt_helf DP.mardiQ_helf
          KS.ksmall_helf)
        CT.clowerE_helf (EN.normsB27_helf BS.band_sharp) EN.supN_helf
        (PC.plattFull_of_cited p z))
      (OPm.minorAt_ostopPm_helfR 0.811 45.7575 1.39 (-3.627308) 1.05635 0.84 8.55451 8.54
        0.6406 FromWeights.close_w FromWeights.cM_w MR.hJ0_8545 MR.floor_854R OL.hp0_854
        (PC.plattFull_of_cited p z) hr (MR.felipaAt_6406R (PC.plattFull_of_cited p z) hr)
        (ostopPm_w p z hr hesp hmm h15 hau heb)
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc PA.perArc_helf AI.arcInt_helf
          DP.bandQ_helf DP.tailQ_helf KS.ksmall_helf)
        OL.lamberNumL_helf hmn)))

/-- **THE FINEST HEADLINE, at `c⁻ = −1.39`.** `FromWeightsN.ep1054_top` with the
`(1.3325822 ≤ c_E)` binder GONE and the `M̃` link PROVED (`MNPm.mnumPm_proved`); `Massacre`,
`GatTail`, `T3W` PROVED and `JokoW` from `ZvsL η_*` (`NefumoClose`). Application only. -/
theorem ep1054_topC (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (zs : NF.ZvsL HW.etaStar)
    (hesp : CY.EspagnWin 1.36)
    (hmm : OP.MinMainP 0.811 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_weightsC p z hr NC.massacre NC.gatTail NC.t3W_helf (NC.jokoW_helf zs) hesp hmm h15 hau
    heb MNPm.mnumPm_proved

/-- **The same, with the Main Theorem from its Totals pieces** (generated from
`FromWeightsN.ep1054_top_pieces`). -/
theorem ep1054_topC_pieces (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (zs : NF.ZvsL HW.etaStar)
    (hesp : CY.EspagnWin 1.36)
    (h1 : MMP.TypeI1W) (h2 : MT.TypeI2) (h3 : MT.TypeII) (h4 : MT.MinMain2L)
    (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_topC p z hr zs hesp (MMP.minMainP_of_piecesW h1 h2 h3 h4) h15 hau heb

end Principia.Erdos1054.Alt7.FromWeightsC
