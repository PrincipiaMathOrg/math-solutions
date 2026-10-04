/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896D
import Principia.Common.TernaryGoldbach.TypeIICrustoCudo

set_option autoImplicit false

/-!
# EP1054 on the corrected route: `CrustoCudo` supplied

`FromAtoms896D.ep1054_atoms896D` with `M2F.CrustoCudo` := `M2C.crustoCudo_holds` (`9e82d2da`):
`eq:crusto` + `eq:cudo` as a bijection of the non-zero terms. `MonroFleming` now owes `Monro2`
(`lem:monro` with `eq:mudo`) alone.

Wording note on `FromAtoms896D`'s docstring: `MPBG.MainBogusEta2` is not refuted; `eq:etoile`, a
step of its printed proof, is false, so the verbatim link is not derivable from the printed proof.
The chain uses the corrected `MainBogusEta2C`.

Application only.

**OWED (7), all minor-arc:** `CoefMainBound`, `CoefErrBound`, `Monro2`, `CortoLarge`, `Garn1a`,
`Procida2Mont`, `SecIICalcC`. **Cited computations (15).** **Cited published theorems (19).**
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896E

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**, `CrustoCudo` supplied. Application only. -/
theorem ep1054_atoms896E (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited)
    -- the minarcs analytic links still open
    (hA : MPMB.CoefMainBound) (hE : MPMB.CoefErrBound) (mo : M2F.Monro2)
    (cl : M2H.CortoLarge) (g1a : T2X.Garn1a) (p2m : T2K.Procida2Mont) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtoms896D.ep1054_atoms896D p z chk sm ch cp gr mc am ab cg wo kc hn cs hA hE
    M2C.crustoCudo_holds mo cl g1a p2m h2c hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR
    hRS hgr hro hme r75 ls

end Principia.Erdos1054.Alt7.FromAtoms896E
