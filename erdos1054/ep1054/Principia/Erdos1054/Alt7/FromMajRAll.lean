/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromMajR
import Principia.Common.TernaryGoldbach.PerArcSpine
import Principia.Common.TernaryGoldbach.ArcIntSpine
import Principia.Common.TernaryGoldbach.MNumLProofs
import Principia.Common.TernaryGoldbach.OstopSpine

set_option autoImplicit false

/-!
# EP1054 with lem:drujal and the numeric minor link fully discharged

`FromMajR.ep1054_majR` (the major-arc input at the referee's retyped constants, `MR.HelfMajR`)
with the three links now PROVED supplied:
* `DS.PerArc η₊` by `PA.perArc_helf` (`PerArcSpine.lean`, every weight);
* `DS.ArcInt η₊` by `AI.arcInt_helf` (`ArcIntSpine.lean`, every weight);
* `OL.MNumL HW.phi 8.54 0.8095 0.6406` by `ML.mnumL_proved` (`MNumLProofs.lean`).

With these, the `lem:drujal` spine is closed (BandQ, TailQ, MardiQ, KSmall, PerArc, ArcInt all
proved) and so is the numeric minor-arc link.

Open, on Helfgott's fixed weights: `MR.HelfMajR` (the major arcs, retyped), `RW.NefumoW`
(prop:nefumo), `OL.OstopL` (the corrected thm:ostop, whose layer 2 is `MinMainL`, `GorshL`,
`GTMonoL`, `CoprarL`, `CoeurY` and prop:palan). Cited: `PC.PlattThm71`, `PC.PlattTrudgian`.
-/

namespace Principia.Erdos1054.Alt7.FromMajRAll

open Principia.Common.TernaryGoldbach

/-- **EP1054 from Platt's two cited verifications and three open links**: the retyped major arcs
`HelfMajR`, `prop:nefumo`, and the corrected `thm:ostop`. -/
theorem ep1054_majR_all (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (hos : OL.OstopL HW.etaPlus HW.etaStar HW.phi) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromMajR.ep1054_majR p z hr nf PA.perArc_helf AI.arcInt_helf hos ML.mnumL_proved

/-- **`E ≤ J` on the retyped route** (`OS.JgeE`, defect D2 of `OstopSpine`): `OS.jgeE_helf` with
`RT.HelfMajFull` ↦ `MR.HelfMajR` and `OC.DrujalLowP` ↦ `MR.DrujalLowPR` (its ET/E bounds at the
retyped `1.4490e-8`, `4.2813e-8`). `E/x ≤ 8.4031·10⁻¹²` (`DB.dubistdie_all`) against `J/x ≥ J₀`. -/
theorem jgeE_helfR (J₀ : ℝ) (hJ0 : 8.4031e-12 ≤ J₀) (pf : RT.PlattFull)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hdl : MR.DrujalLowPR J₀ HW.etaPlus HW.etaCirc) : OS.JgeE HW.etaPlus := by
  intro b hb x hx
  obtain ⟨mp, -, -⟩ := hr pf
  have hsn := EN.supN_helf
  have hrg := RW.regW_helf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, -, -, -, -⟩ := EN.normsB27_helf BS.band_sharp
  have hx0 := MinSp.x_pos x hx
  have hE := DB.dubistdie_all HW.etaPlus hsn.1 hsn.2.1 b hb x hx
  have hA := hdl hrg.1 hsn.1 DS.l1_etaPlus_sharp hrg.2.2.2.2.1 hrg.2.2.2.2.2.1
    hrg.2.2.2.2.2.2 hlo1 hlo2 hdiff hl3 x hx (MR.et_plusR HW.etaPlus mp _ hx)
    (MR.eb_plusR HW.etaPlus mp _ hx)
  have h1 : 8.4031e-12 * x ≤ J₀ * x := mul_le_mul_of_nonneg_right hJ0 hx0.le
  have h2 : J₀ * x ≤ MajSp.amaj HW.etaPlus x * x := mul_le_mul_of_nonneg_right hA hx0.le
  linarith [mul_comm x (MajSp.amaj HW.etaPlus x)]

/-- **EP1054 with `OL.OstopL` itself composed** (`OS.ostopL_of_open`): the corrected `thm:ostop`
is replaced by its layer-2 links, `JgeE` discharged on the retyped route (`jgeE_helfR` at the
lem:drujal floor `8.55451`, `MR.drujalLowPR_of_spine`). Open: `HelfMajR`, `NefumoW`, `CoeurY`,
`MinMainL`, `RS62Thm15`, `GYMono`, `HLeG`, `Austeria`, `GTMonoL`, `CoprarL`, `EBound2`,
`TopStepL`. Cited: `PlattThm71`, `PlattTrudgian`. -/
theorem ep1054_layer2 (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (hco : OC.CoeurY HW.etaPlus) (hmm : OL.MinMainL) (h15 : GS.RS62Thm15) (hmo : GS.GYMono)
    (hhl : GS.HLeG) (hau : GS.Austeria) (hgm : OL.GTMonoL HW.phi)
    (hcp : OL.CoprarL HW.etaStar HW.phi) (heb : OS.EBound2 HW.etaPlus) (hts : OS.TopStepL HW.phi) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_majR_all p z hr nf
    (OS.ostopL_of_open hco hmm h15 hmo hhl hau hgm hcp heb
      (jgeE_helfR 8.55451 MR.hJ0_8545 (PC.plattFull_of_cited p z) hr
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc PA.perArc_helf AI.arcInt_helf DP.bandQ_helf
          DP.tailQ_helf KS.ksmall_helf))
      hts)

end Principia.Erdos1054.Alt7.FromMajRAll
