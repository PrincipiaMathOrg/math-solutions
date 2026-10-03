/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromMajRAll
import Principia.Erdos1054.Alt7.FromCoprar
import Principia.Common.TernaryGoldbach.NefumoLinks
import Principia.Common.TernaryGoldbach.CoeurSpine
import Principia.Common.PSieveBellen
import Principia.Common.TernaryGoldbach.MonoLinks

set_option autoImplicit false

/-!
# EP1054 with the monotonicity links `GYMono`, `GTMonoL`, `HLeG` PROVED

`MonoLinks.lean` proves three of the four numeric layer-2 links of the corrected `thm:ostop`:
* `GS.GYMono` (`MO.gYMono`) — `lem:vinc` at `K = 1` on the corrected `L`, every scale;
* `OL.GTMonoL HW.phi` (`MO.gtMonoL_helf`) — `g̃(y,·)` non-increasing on `[r₀, r₁(y)]`;
* `GS.HLeG` (`MO.hLeG`) — the second case of the minarcs Main Theorem fits under `g`.

They are supplied here to two headlines:
* `ep1054_layer2_mono` — `FromMajRAll.ep1054_layer2` (the headline this round was briefed on);
* `ep1054_deep_mono` — every composed spine opened: `FromCoprar.ep1054_coprar` with `NefumoW`
  from its spine (`NF.nefumoW_helf_rest`), `CoeurY` from `CY.coeurY_helf` with `prop:bellen`
  PROVED (`PSieve.bellenG`), `GorshL` from `GS.gorshL_of_open`, `PerArc`, `ArcInt`, `MNumL`
  proved. (This is `FromDeep.ep1054_deep` at the CURRENT signature of `CY.coeurY_helf`, whose
  last argument became `1.3325822 ≤ cE`; `FromDeep.lean` does not build against it.)

`OS.TopStepL HW.phi` stays a hypothesis of both here; `FromMonoTop.lean` supplies it
(`MonoTop.lean`). Application only.
-/

namespace Principia.Erdos1054.Alt7.FromMono

open Principia.Common.TernaryGoldbach

/-- **EP1054 at layer 2 with `GYMono`, `HLeG`, `GTMonoL` discharged**: `FromMajRAll.ep1054_layer2`
with `MO.gYMono`, `MO.hLeG`, `MO.gtMonoL_helf`. Open: `HelfMajR`, `NefumoW`, `CoeurY`,
`MinMainL`, `RS62Thm15`, `Austeria`, `CoprarL`, `EBound2`, `TopStepL`. Cited: `PlattThm71`,
`PlattTrudgian`. -/
theorem ep1054_layer2_mono (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (hco : OC.CoeurY HW.etaPlus) (hmm : OL.MinMainL) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (hcp : OL.CoprarL HW.etaStar HW.phi) (heb : OS.EBound2 HW.etaPlus)
    (hts : OS.TopStepL HW.phi) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromMajRAll.ep1054_layer2 p z hr nf hco hmm h15 MO.gYMono MO.hLeG hau MO.gtMonoL_helf hcp heb
    hts

/-- **The deepest EP1054 headline with `GYMono`, `HLeG`, `GTMonoL` discharged**:
`FromCoprar.ep1054_coprar` with every composed spine opened and `prop:bellen` proved. Open:
`HelfMajR`, `Massacre`, `GatTail`, `T3W`, `JokoW`, `EspagnWin 1.36`, `c_E ≥ 1.3325822`,
`MinMainL`, `RS62Thm15`, `Austeria`, `EBound2`, `TopStepL`. Cited: `PlattThm71`,
`PlattTrudgian`. -/
theorem ep1054_deep_mono (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (ms : NF.Massacre) (gt : NF.GatTail) (t3 : NF.T3W HW.etaPlus HW.etaStar)
    (jk : NF.JokoW HW.etaPlus HW.etaStar)
    (hesp : CY.EspagnWin 1.36) (hce : 1.3325822 ≤ CY.cE)
    (hmm : OL.MinMainL) (h15 : GS.RS62Thm15) (hau : GS.Austeria)
    (heb : OS.EBound2 HW.etaPlus) (hts : OS.TopStepL HW.phi) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromCoprar.ep1054_coprar p z hr (NF.nefumoW_helf_rest ms gt t3 jk) PA.perArc_helf
    AI.arcInt_helf (CY.coeurY_helf Principia.Common.PSieve.bellenG hesp hce)
    (GS.gorshL_of_open HW.etaStar HW.phi hmm h15 MO.gYMono MO.hLeG hau) MO.gtMonoL_helf heb hts
    ML.mnumL_proved

end Principia.Erdos1054.Alt7.FromMono
