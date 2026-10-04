/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZG
import Principia.Common.TernaryGoldbach.Bosta2Main
import Principia.Common.TernaryGoldbach.Bostb1Main

set_option autoImplicit false

/-!
# EP1054 on its atoms: `lem:bosta2` and `lem:bostb1` down to their trig-sum cores

`FromAtomsZG.ep1054_atomsZG` with
* `MPc.Bosta2Eta2` := `MPBM.bosta2Eta2_of_esthel` (`1d6fe46a`) — `TrompaisC` and `MainOddEta2`
  PROVED from Helfgott's cited `HC.CameloGridCited` and `HC.WollustCited`; only
  `MPB2.EsthelEta2` owed;
* `MPG.Bostb1Eta2` := `MPBL.bostb1Eta2_of_esthel` (`c22e3b04`) — `TrompaisLogC` (with the sharp
  `eq:puella` part 3, `EtaHatLBound`) and `MainLogEta2` PROVED from the same citations; only
  `MPB1.EsthelLogEta2` owed.

Application only. Every other binder is `FromAtomsZG`'s. Both verifiers CONFIRMED (w4rel5zty).

**OWED (6), all minor-arc:** `EsthelEta2`, `EsthelLogEta2`, `BogusEta2C`, `Vinland1At`,
`EriksagaAt`, `SecIIAt`. **Caveat:** the last three are Helfgott's printed displays, which rest on
`eq:passi`/`eq:velib`, refereed FALSE (2026-10-03); the corrected route (`TypeIISpineC`,
`MinMainTotalsC`, Main Theorem constant 0.896) is being completed separately and will replace them.
**Cited computations (12):** Platt ×2; Helfgott's `EspagnCheck`, `EspagnSmall`, `Charpy`, `Charpas`,
`AusteriaGrid`, `MalMainCited`, `AmanitaBisectCited`, `AppBCited`, `CameloGridCited`,
`WollustCited`. **Cited published theorems (17).**
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZH

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZG.ep1054_atomsZG` with `Bosta2Eta2` and `Bostb1Eta2`
reduced to their trig-sum cores. Application only. -/
theorem ep1054_atomsZH (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited)
    -- the minarcs analytic links still open
    (he2 : MPB2.EsthelEta2) (hel : MPB1.EsthelLogEta2) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hbo : MPBC.BogusEta2C) (hs3 : MPc.SecIIAt)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtomsZG.ep1054_atomsZG p z chk sm ch cp gr mc am ab (MPBL.bostb1Eta2_of_esthel cg wo hel)
    (MPBM.bosta2Eta2_of_esthel cg wo he2) hv1 her hbo hs3 hZC rs cer hm hc h15 h12 h13 h316 h324
    h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZH
