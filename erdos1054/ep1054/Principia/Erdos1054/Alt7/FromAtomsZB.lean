/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZM
import Principia.Common.TernaryGoldbach.AgamonCont
import Principia.Common.TernaryGoldbach.AgamonDecay
import Principia.Common.TernaryGoldbach.AgamonLimit
import Principia.Common.TernaryGoldbach.I2Arith

set_option autoImplicit false

/-!
# EP1054 on its atoms: three `lem:agamon` links and `I2Arith` proved

`FromAtomsZM.ep1054_atomsZM` (`MalDecay` already gone) with four more owed links supplied:
* `EF.Continuation`, `EF.MollDecay`, `EF.MollLimit` — PROVED with no hypothesis
  (`AG.continuation_holds`, `AG.mollDecay_holds`, `AG.mollLimit_holds`, `4f8c517e`);
* `MPc.I2Arith` — PROVED (`I2A.i2Arith`, `4c5e6473`), the `S_{I,2}` Totals algebra for every
  `Y ≥ 3.4·10²³`, from Chebyshev and Mertens alone.

Application only. Every other binder is `FromAtomsZM`'s.

**OWED argument (16):**
* `lem:agamon`: `Rectangle`, `Horizontal`, `LeftLD`;
* the weight links `PlusDecay`, `PhiDecay`, `MalMain`;
* `EspagnEdgeRes`;
* `Eta2Reg`, `Eta2Norms`;
* seven analytic minarcs links: `Bostb1At`, `Bosta2Eta2`, `Vinland1At`, `EriksagaAt`, `SecI1At`,
  `SecI2At`, `SecIIAt`.

Cited (7) and literature (17) are unchanged.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZB

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZM.ep1054_atomsZM` with `Continuation`, `MollDecay`,
`MollLimit` and `I2Arith` supplied. Application only. -/
theorem ep1054_atomsZB (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- the explicit formula (lem:agamon): three links still open
    (hRe : EF.Rectangle) (hHo : EF.Horizontal) (hLD : EF.LeftLD)
    -- the major-arc weight links still open
    (pd : HM.PlusDecay) (fd : HM.PhiDecay) (mm : HM.MalMain)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited)
    -- the prop:espagn residue, the eta2 links of lem:crepe
    (res : EE.EspagnEdgeRes) (e1 : EF.Eta2Reg) (e2 : EF.Eta2Norms)
    -- the minarcs analytic links still open
    (hb1 : MPc.Bostb1At) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hs1 : MPc.SecI1At) (hs2 : MPc.SecI2At) (hs3 : MPc.SecIIAt)
    -- literature
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtomsZM.ep1054_atomsZM p z hRe hHo AG.continuation_holds AG.mollDecay_holds
    AG.mollLimit_holds hLD pd fd mm chk sm ch cp gr res e1 e2 hb1 hb2 I2A.i2Arith hv1 her hs1 hs2
    hs3 hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZB
