/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromWeightsC
import Principia.Common.TernaryGoldbach.MNumPC
import Principia.Common.TernaryGoldbach.MinMainTotalsC

set_option autoImplicit false

/-!
# The EP1054 top theorem at the `eq:passi` erratum's Main Theorem constant `0.896`

`FromWeightsC.ep1054_topC` re-run with the minor-arc Main Theorem constant `0.811` replaced by
`0.896` (`eq:passi` refereed FALSE, 2026-10-03; absorbed in `MTC`, `a78e21d5`). Every constant
of the `ostop` assembly (`1.39`, `-3.627308`, `1.05635`, `0.84`, `8.55451`, `8.54`, `0.6406`) is
unchanged; what changes is
* `hmm : OP.MinMainP 0.896 45.7575` (supplied downstream by `MTC.minMainPC_of_open`);
* the generic-in-`c05` monotonicity / top-step / coprar instances, taken at `0.896`
  (`MNPC.gYMonoPC`, `MNPC.hLeGPC`, `MNPC.gtMonoPC`, `MNPC.coprarPC_of_R`, `MNPC.topStepPC`);
* the `M~` certificate, taken at `0.896` (`MNPC.mnumPmC_proved`, `23ef741c`, margin `0.00097`).

Application only. The hypotheses are exactly `FromWeightsC.ep1054_topC`'s with `hmm` at `0.896`.
-/

namespace Principia.Erdos1054.Alt7.FromTop896

open Principia.Common.TernaryGoldbach

/-- **EP1054 top theorem at `0.896`**: `FromWeightsC.ep1054_topC` with the minor-arc Main Theorem
at the erratum's constant `OP.MinMainP 0.896 45.7575`. Application only. -/
theorem ep1054_top896 (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (zs : NF.ZvsL HW.etaStar)
    (hesp : CY.EspagnWin 1.36)
    (hmm : OP.MinMainP 0.896 45.7575) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  Round7Bal.ep1054_all_bal (Proofs.BalancedW.balanced_of_w
    (FromWeights.helfAtW_chebR
      (MR.majorAt_c0R HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hr
        RT.starScale_helf RW.regW_helf (NF.nefumoW_helf_rest NC.massacre NC.gatTail NC.t3W_helf
          (NC.jokoW_helf zs))
        (MR.drujalE100R_of_spine HW.etaPlus PA.perArc_helf AI.arcInt_helf DP.mardiQ_helf
          KS.ksmall_helf)
        CT.clowerE_helf (EN.normsB27_helf BS.band_sharp) EN.supN_helf
        (PC.plattFull_of_cited p z))
      (OPm.minorAt_ostopPm_helfR 0.896 45.7575 1.39 (-3.627308) 1.05635 0.84 8.55451 8.54
        0.6406 FromWeights.close_w FromWeights.cM_w MR.hJ0_8545 MR.floor_854R OL.hp0_854
        (PC.plattFull_of_cited p z) hr (MR.felipaAt_6406R (PC.plattFull_of_cited p z) hr)
        (OSPm.ostopPm_of_open 0.896 45.7575 1.39 (-3.627308) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) OPm.jump_le_139
          (CYm.coeurY139_closed hesp HW.etaPlus) hmm h15 MNPC.gYMonoPC MNPC.hLeGPC hau
          MNPC.gtMonoPC (MNPC.coprarPC_of_R (PC.plattFull_of_cited p z) hr) heb
          (FromWeightsP.jgeE_w p z hr) MNPC.topStepPC)
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc PA.perArc_helf AI.arcInt_helf
          DP.bandQ_helf DP.tailQ_helf KS.ksmall_helf)
        OL.lamberNumL_helf MNPC.mnumPmC_proved)))

end Principia.Erdos1054.Alt7.FromTop896
