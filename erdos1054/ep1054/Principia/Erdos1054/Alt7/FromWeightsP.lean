/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromWeights
import Principia.Erdos1054.Alt7.FromMono
import Principia.Common.TernaryGoldbach.MonoTopP
import Principia.Common.TernaryGoldbach.MinMainP

set_option autoImplicit false

/-!
# EP1054 through the weight-aware split on the CORRECTED Main Theorem `(0.811, 45.7575)`

`FromMonoTop.ep1054_deep_top` is the finest headline on the typed `OL.MinMainL`, whose two
constants `(0.5, 22.7538)` are UNREACHABLE from the book's pieces (`MT.not_arith_typed`). Here
the same hypothesis list is re-composed

* through the weight-aware split (`FromWeights.helfAtW_chebR`, `BalancedW.balanced_of_w`): the
  minor arcs at `1.05635`, the `M̃` constant `cM = 0.84` (`FromWeights.close_w`);
* on the parametric chain at `(c05, C) = (0.811, 45.7575)` (`OstopP`, `GorshP`, `OstopSpineP`),
  with `OL.MinMainL` REPLACED by `OP.MinMainP 0.811 45.7575` — which the Totals reach from the
  three named piece bounds (`MMP.minMainP_of_pieces`) and which the old hypothesis implies
  (`MMP.minMainP_of_L`);
* with every numeric layer-2 link PROVED at the new constants: `GYMonoP`, `HLeGP` (transferred,
  `MOP.gYMonoP`, `MOP.hLeGP`), `GTMonoP` (`MOP.gtMonoP_helf`), `CoprarP` (`MOP.coprarP_of_R`),
  `TopStepP` (re-proved, `MTOP.topStepP_helf`).

`OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406` stays a NAMED hypothesis: the Lean agent's own
mpmath price (`scratchpad/ostopp/mnump_price.py`) gives `sup M̃ = 0.818495` at the threshold
`x = 4.9·10²⁶` (decreasing in `x` on every sampled point), margin `0.021505` against `0.84`.

Open: `HelfMajR`, `Massacre`, `GatTail`, `T3W`, `JokoW`, `EspagnWin 1.36`, `c_E ≥ 1.3325822`,
`OP.MinMainP 0.811 45.7575`, `RS62Thm15`, `Austeria`, `EBound2`, `OP.MNumP … 0.84 0.6406`.
Cited: `PlattThm71`, `PlattTrudgian`. Application only.
-/

namespace Principia.Erdos1054.Alt7.FromWeightsP

open Principia.Common.TernaryGoldbach

/-- **`E ≤ J` on the retyped route** at the `lem:drujal` floor `8.55451` (`FromCoprar.jgeE_majR`
fed by the proved `PerArc`, `ArcInt`, `BandQ`, `TailQ`, `KSmall`). -/
theorem jgeE_w (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) : OS.JgeE HW.etaPlus :=
  FromCoprar.jgeE_majR 8.55451 MR.hJ0_8545 (PC.plattFull_of_cited p z) hr
    (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc PA.perArc_helf AI.arcInt_helf DP.bandQ_helf
      DP.tailQ_helf KS.ksmall_helf)

/-- **The corrected `thm:ostop` at `(0.811, 45.7575)` on Helfgott's weights**
(`OSP.ostopP_of_open`), every numeric layer-2 link supplied PROVED. Open: `CoeurY`,
`MinMainP 0.811 45.7575`, `RS62Thm15`, `Austeria`, `EBound2`. -/
theorem ostopP_w (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) (hco : OC.CoeurY HW.etaPlus)
    (hmm : OP.MinMainP 0.811 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) : OP.OstopP 0.811 45.7575 HW.etaPlus HW.etaStar HW.phi :=
  OSP.ostopP_of_open 0.811 45.7575 (by norm_num) (by norm_num) hco hmm h15 MOP.gYMonoP MOP.hLeGP
    hau MOP.gtMonoP_helf (MOP.coprarP_of_R (PC.plattFull_of_cited p z) hr) heb (jgeE_w p z hr)
    MTOP.topStepP_helf

/-- **THE HEADLINE: EP1054 on the corrected Main Theorem, through the weight-aware split.**
`FromMonoTop.ep1054_deep_top`'s hypotheses with `OL.MinMainL ↦ OP.MinMainP 0.811 45.7575` and the
`M̃` link at `(0.811, 45.7575)`, `cM = 0.84`. Application only. -/
theorem ep1054_weightsP (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (ms : NF.Massacre) (gt : NF.GatTail) (t3 : NF.T3W HW.etaPlus HW.etaStar)
    (jk : NF.JokoW HW.etaPlus HW.etaStar)
    (hesp : CY.EspagnWin 1.36) (hce : 1.3325822 ≤ CY.cE)
    (hmm : OP.MinMainP 0.811 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) (hmn : OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  Round7Bal.ep1054_all_bal (Proofs.BalancedW.balanced_of_w
    (FromWeights.helfAtW_chebR
      (MR.majorAt_c0R HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hr
        RT.starScale_helf RW.regW_helf (NF.nefumoW_helf_rest ms gt t3 jk)
        (MR.drujalE100R_of_spine HW.etaPlus PA.perArc_helf AI.arcInt_helf DP.mardiQ_helf
          KS.ksmall_helf)
        CT.clowerE_helf (EN.normsB27_helf BS.band_sharp) EN.supN_helf
        (PC.plattFull_of_cited p z))
      (OP.minorAt_ostopP_helfR 0.811 45.7575 1.05635 0.84 8.55451 8.54 0.6406
        FromWeights.close_w FromWeights.cM_w MR.hJ0_8545 MR.floor_854R OL.hp0_854
        (PC.plattFull_of_cited p z) hr (MR.felipaAt_6406R (PC.plattFull_of_cited p z) hr)
        (ostopP_w p z hr (CY.coeurY_helf Principia.Common.PSieve.bellenG hesp hce) hmm h15 hau
          heb)
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc PA.perArc_helf AI.arcInt_helf
          DP.bandQ_helf DP.tailQ_helf KS.ksmall_helf)
        OL.lamberNumL_helf hmn)))

/-- **The same headline with the Main Theorem's first case from the Totals**: `hmm` replaced by
the three named piece bounds (at the verifier's `min(1, 4c₀'/δ²)` reading of Link A1) and the
second case (`MMP.minMainP_of_piecesW`). Application only. -/
theorem ep1054_piecesP (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (ms : NF.Massacre) (gt : NF.GatTail) (t3 : NF.T3W HW.etaPlus HW.etaStar)
    (jk : NF.JokoW HW.etaPlus HW.etaStar)
    (hesp : CY.EspagnWin 1.36) (hce : 1.3325822 ≤ CY.cE)
    (h1 : MMP.TypeI1W) (h2 : MT.TypeI2) (h3 : MT.TypeII) (h4 : MT.MinMain2L)
    (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) (hmn : OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_weightsP p z hr ms gt t3 jk hesp hce (MMP.minMainP_of_piecesW h1 h2 h3 h4) h15 hau heb
    hmn

/-- **No stronger than on the typed Main Theorem**: `OL.MinMainL` supplies the new headline's
`OP.MinMainP 0.811 45.7575` (`MMP.minMainP_of_L`). Application only. -/
theorem ep1054_weightsP_of_L (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (ms : NF.Massacre) (gt : NF.GatTail) (t3 : NF.T3W HW.etaPlus HW.etaStar)
    (jk : NF.JokoW HW.etaPlus HW.etaStar)
    (hesp : CY.EspagnWin 1.36) (hce : 1.3325822 ≤ CY.cE)
    (hmm : OL.MinMainL) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) (hmn : OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_weightsP p z hr ms gt t3 jk hesp hce (MMP.minMainP_of_L hmm) h15 hau heb hmn

end Principia.Erdos1054.Alt7.FromWeightsP
