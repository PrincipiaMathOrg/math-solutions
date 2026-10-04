/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896E
import Principia.Common.TernaryGoldbach.MainBogusCoef

set_option autoImplicit false

/-!
# EP1054 on the corrected route: `lem:bogus` CLOSED

`FromAtoms896E.ep1054_atoms896E` with the two coefficient links of the corrected `lem:bogus`
discharged (`d4f841fa`, verifier CONFIRMED, w121lkavc):
* `MPMB.CoefMainBound` := `MPCB.coefMainBound_of hgr h12`;
* `MPMB.CoefErrBound` := `MPCB.coefErrBound_of h12`;
from the already-cited Granville–Ramaré Lemma 10.2 (`MPc.Grara`) and Rosser–Schoenfeld 1962 Thm 12
(`EB.RS62Thm12`). `eq:rala` (odd n) is PROVED along the way (`MPCB.ralaOdd_of`, via Stirling), so
RS62 (3.23) is not needed. The whole Type I minor-arc analysis (`lem:bosta2`, `lem:bostb1`,
`lem:bogus`) now rests on cited inputs only.

Application only.

**OWED (5), all minor-arc Type II:** `Monro2`, `CortoLarge`, `Garn1a`, `Procida2Mont`, `SecIICalcC`.
**Cited computations (15).** **Cited published theorems (19).**
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896F

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**, `lem:bogus` closed. Application only. -/
theorem ep1054_atoms896F (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited)
    -- the minarcs analytic links still open
    (mo : M2F.Monro2) (cl : M2H.CortoLarge) (g1a : T2X.Garn1a) (p2m : T2K.Procida2Mont)
    (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtoms896E.ep1054_atoms896E p z chk sm ch cp gr mc am ab cg wo kc hn cs
    (MPCB.coefMainBound_of hgr h12) (MPCB.coefErrBound_of h12) mo cl g1a p2m h2c hZC rs cer hm
    hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls

end Principia.Erdos1054.Alt7.FromAtoms896F
