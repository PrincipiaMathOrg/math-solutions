/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896
import Principia.Common.TernaryGoldbach.EsthelEta2E
import Principia.Common.TernaryGoldbach.EsthelLog
import Principia.Common.TernaryGoldbach.TypeIIKastLarge
import Principia.Common.TernaryGoldbach.TypeIIMenson2C
import Principia.Common.TernaryGoldbach.TypeIIGrottoTab

set_option autoImplicit false

/-!
# EP1054 on the corrected route: both trig-sum cores, `KastLarge` and `GrottoTab` supplied

`FromAtoms896.ep1054_atoms896` (Main Theorem constant 0.896) with
* `MPB2.EsthelEta2` := `MPE2.esthelEta2_holds` (`74ae63ce`) and `MPB1.EsthelLogEta2` :=
  `MPEL.esthelLogEta2_holds` (`e9962e57`): `lem:bosta2` and `lem:bostb1` now rest on Helfgott's
  cited `CameloGrid` and `Wollust` alone;
* `T2S.KastLarge` := `KLR.kastLarge_of_rs75` (`3675d615`), from Rosser–Schoenfeld 1975, Cor. 2,
  (5.7), a NEW cited published theorem (`KLR.RS75Cor2`, stated verbatim on a narrower range);
* `T2SC.Menson2C` := `M2H.menson2C_of_links` with `GrottoTab` PROVED (`M2G.grottoTab_holds`,
  `dda8ca8e`); it now owes `MonroFleming` and `CortoLarge`, plus the cited `HC.CortoSmallCited`.

Application only.

**OWED (6), all minor-arc:** `MainBogusEta2`, `EsthelBogusEta2C`, `MonroFleming`, `CortoLarge`,
`Kraken`, `SecIICalcC`. **Cited computations (15):** Platt ×2 and 13 of Helfgott's.
**Cited published theorems (18):** the 17 plus `RS75Cor2`.
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896B

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**: `FromAtoms896.ep1054_atoms896` with the
trig-sum cores, `KastLarge` and `GrottoTab` supplied. Application only. -/
theorem ep1054_atoms896B (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited)
    -- the minarcs analytic links still open
    (hmb : MPBG.MainBogusEta2) (heb : MPBC.EsthelBogusEta2C) (mf : M2H.MonroFleming)
    (cl : M2H.CortoLarge) (hk : T2S.Kraken) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtoms896.ep1054_atoms896 p z chk sm ch cp gr mc am ab cg wo kc hn MPE2.esthelEta2_holds
    MPEL.esthelLogEta2_holds hmb heb (M2H.menson2C_of_links mf M2G.grottoTab_holds cl cs) hk
    (KLR.kastLarge_of_rs75 r75) h2c hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr
    hro hme

end Principia.Erdos1054.Alt7.FromAtoms896B
