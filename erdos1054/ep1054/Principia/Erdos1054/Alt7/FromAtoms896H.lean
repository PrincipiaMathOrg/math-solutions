/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896G
import Principia.Common.TernaryGoldbach.TypeIIYuttoClosed

set_option autoImplicit false

/-!
# EP1054 on the corrected route: `CortoLarge` from cited inputs

`FromAtoms896G.ep1054_atoms896G` with `M2H.CortoLarge` := `M2YZ.cortoLarge_of_cited ys c0 hR hM`
(`7ad2f9e4`, `c3b2f510`, `ee65e97b`, `1d873cd1`, `9b4781d8`; verifiers CONFIRMED). The printed
`lem:yutto` is not used: its Rankin step drops a factor `e²`, and its last step is false at `10¹⁰`.
The corrected links `YuttoMid2C` and `YuttoBig2C` (strictly weaker than the printed lemma) are
PROVED by direct truncation through a nonnegative Dirichlet convolution, and `WeightEM` is PROVED.
The new inputs are three of Helfgott's cited computations (`HC.YuttoSmallCited`,
`HC.CortoC0Cited`, `HC.RamareCited`, clause 1 only) and one cited published theorem,
`M2Y.RamareMarraki` (Ramaré, Acta Arith. 157 (2013) 365-379, Cor. 1.4; Helfgott's `eq:marraki`),
checked against the published paper.

Application only.

**OWED (2), both minor-arc Type II:** `Garn1a`, `SecIICalcC`. **Cited computations (18).**
**Cited published theorems (21):** the 17, `RS75Cor2`, `LargeSieve`, `MontgomeryIneq`,
`RamareMarraki`.
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896H

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**, `CortoLarge` from cited inputs. Application
only. -/
theorem ep1054_atoms896H (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited) (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
    (hRc : HC.RamareCited)
    -- the minarcs analytic links still open
    (g1a : T2X.Garn1a) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) (hMk : M2Y.RamareMarraki) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtoms896G.ep1054_atoms896G p z chk sm ch cp gr mc am ab cg wo kc hn cs
    (M2YZ.cortoLarge_of_cited ys c0 hRc hMk) g1a h2c hZC rs cer hm hc h15 h12 h13 h316 h324 h330
    h332 hR hRS hgr hro hme r75 ls mi

end Principia.Erdos1054.Alt7.FromAtoms896H
