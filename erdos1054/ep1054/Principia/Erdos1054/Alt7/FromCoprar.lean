/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromMajR
import Principia.Common.TernaryGoldbach.CoprarLProof

set_option autoImplicit false

/-!
# EP1054 on HelfMaj RETYPED with `OL.OstopL` opened to layer 2 and the annulus `A₀` CLOSED

`FromMajR.ep1054_majR` takes `OL.OstopL η₊ η* φ`, the corrected `thm:ostop`. `OS.ostopL_of_layer2`
composes it from seven layer-2 links, one of which is `OL.CoprarL η* φ` — the annulus
`A₀ = 𝔐^{(y)}_{8,r₀} ∖ 𝔐^{(x)}_{8,r₀}`. `CP.coprarL_of_R` PROVES that link from the SAME
`MR.HelfMajR` the headline already takes (its `CoprarR` for the base `η₂ ∗_M φ`, under
`RT.PlattFull`, which the headline supplies from Platt's two cited verifications). So:

* `OL.OstopL` is replaced by its layer-2 links MINUS `CoprarL`: `OC.CoeurY`, `OL.GorshL`,
  `OL.GTMonoL`, `OS.EBound2`, `OS.TopStepL`;
* `OS.JgeE` (defect D2 of `OstopSpine`) is discharged on the retyped route (`jgeE_majR`), from
  `MR.drujalLowPR_of_spine` at the floor `8.55451` fed by the headline's own `PerArc`, `ArcInt`.

Everything else is `ep1054_majR` verbatim. Application only.
-/

namespace Principia.Erdos1054.Alt7.FromCoprar

open Principia.Common.TernaryGoldbach

/-- **`E ≤ J` on the retyped route** (`OS.JgeE`): `E/x ≤ 8.4031·10⁻¹²` (`DB.dubistdie_all`)
against `J/x ≥ J₀` (`MR.DrujalLowPR J₀`, its `ET`/`E` inputs from `MR.et_plusR`,
`MR.eb_plusR`). The proof of `OS.jgeE_helf` with `RT.HelfMajFull ↦ MR.HelfMajR`,
`OC.DrujalLowP ↦ MR.DrujalLowPR`. -/
theorem jgeE_majR (J₀ : ℝ) (hJ0 : 8.4031e-12 ≤ J₀) (pf : RT.PlattFull)
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

/-- **EP1054 on HelfMaj RETYPED, `thm:ostop` at layer 2, the annulus closed**:
`FromMajR.ep1054_majR` with `OL.OstopL` supplied by `OS.ostopL_of_layer2`, whose `CoprarL` is
`CP.coprarL_of_R` (PROVED from `hr`) and whose `JgeE` is `jgeE_majR`. OPEN: `MR.HelfMajR`,
`RW.NefumoW`, `DS.PerArc`, `DS.ArcInt`, `OC.CoeurY`, `OL.GorshL`, `OL.GTMonoL`, `OS.EBound2`,
`OS.TopStepL`, `OL.MNumL HW.phi 8.54 0.8095 0.6406`. Cited: `PC.PlattThm71`,
`PC.PlattTrudgian`. Application only. -/
theorem ep1054_coprar (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (hco : OC.CoeurY HW.etaPlus) (hgo : OL.GorshL HW.etaStar HW.phi)
    (hgm : OL.GTMonoL HW.phi) (heb : OS.EBound2 HW.etaPlus) (hts : OS.TopStepL HW.phi)
    (hmn : OL.MNumL HW.phi 8.54 0.8095 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromMajR.ep1054_majR p z hr nf pa ai
    (OS.ostopL_of_layer2 hco hgo hgm (CP.coprarL_of_R (PC.plattFull_of_cited p z) hr) heb
      (jgeE_majR 8.55451 MR.hJ0_8545 (PC.plattFull_of_cited p z) hr
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc pa ai DP.bandQ_helf DP.tailQ_helf
          KS.ksmall_helf))
      hts)
    hmn

end Principia.Erdos1054.Alt7.FromCoprar
