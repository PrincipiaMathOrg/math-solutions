/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896B
import Principia.Common.TernaryGoldbach.TypeIIKrakenLS

set_option autoImplicit false

/-!
# EP1054 on the corrected route: `prop:kraken` down to `Garn1a` and `Procida2Mont`

`FromAtoms896B.ep1054_atoms896B` with `T2S.Kraken` := `T2K.kraken_of_ls` (`b726bfc5`):
`Garn1b`, `Gargamel`, `Procida3` and the large-sieve half of `Procida2` PROVED from the sharp large
sieve, `T2K.LargeSieve` — Montgomery–Vaughan 1974, Cor. 1 (Iwaniec–Kowalski, Thm 7.7), a NEW cited
published theorem, stated weaker (`δ ≤ 1/2`).

Application only.

**OWED (7), all minor-arc:** `MainBogusEta2`, `EsthelBogusEta2C`, `MonroFleming`, `CortoLarge`,
`Garn1a`, `Procida2Mont`, `SecIICalcC`. **Cited computations (15).** **Cited published theorems
(19):** the 17, `RS75Cor2`, and `LargeSieve`.
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896C

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**: `FromAtoms896B.ep1054_atoms896B` with
`Kraken` reduced to `Garn1a` and `Procida2Mont` over the large sieve. Application only. -/
theorem ep1054_atoms896C (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited)
    -- the minarcs analytic links still open
    (hmb : MPBG.MainBogusEta2) (heb : MPBC.EsthelBogusEta2C) (mf : M2H.MonroFleming)
    (cl : M2H.CortoLarge) (g1a : T2X.Garn1a) (p2m : T2K.Procida2Mont) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtoms896B.ep1054_atoms896B p z chk sm ch cp gr mc am ab cg wo kc hn cs hmb heb mf cl
    (T2K.kraken_of_ls ls g1a p2m) h2c hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS
    hgr hro hme r75

end Principia.Erdos1054.Alt7.FromAtoms896C
