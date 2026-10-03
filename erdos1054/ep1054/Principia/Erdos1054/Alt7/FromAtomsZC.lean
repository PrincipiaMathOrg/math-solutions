/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZB
import Principia.Common.TernaryGoldbach.AgamonHoriz
import Principia.Common.TernaryGoldbach.Eta2Reg
import Principia.Common.TernaryGoldbach.Eta2Norms

set_option autoImplicit false

/-!
# EP1054 on its atoms: `Horizontal` and the two `η₂` links proved

`FromAtomsZB.ep1054_atomsZB` with three more owed links supplied, each by a theorem with no
hypothesis:
* `EF.Horizontal` — `lem:agamon`'s "real risk" (EF5) — `AH.horizontal_holds` (`79c94420`): Landau
  balls plus Jensen at `s₀ ± i(T₀ + 1/2)`, a pigeonhole on the zero ordinates, and the completed
  `L`-function (`ξ` for `q = 1`) as the entire factor;
* `EF.Eta2Reg`, `EF.Eta2Norms` — `E2.eta2Reg_holds`, `E2.eta2Norms_holds` (`aafd78b9`): the
  mollified `η₂` is `C¹`, vanishes at `0`, and has `c₀ ≤ 8·2^{ε/2}`, `|η₂′|₂ ≤ 4√3·2^{ε/2}`.

So the corrected `lem:crepe` (`EF.CrepeC`) now rests on `lem:agamon` and two cited zero-sum lemmas
only. Application only. Every other binder is `FromAtomsZB`'s.

**OWED argument (13):**
* `lem:agamon`: `Rectangle`, `LeftLD`;
* the weight links `PlusDecay`, `PhiDecay`, `MalMain`;
* `EspagnEdgeRes`;
* seven analytic minarcs links: `Bostb1At`, `Bosta2Eta2`, `Vinland1At`, `EriksagaAt`, `SecI1At`,
  `SecI2At`, `SecIIAt`.

Cited (7) and literature (17) are unchanged.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZC

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZB.ep1054_atomsZB` with `Horizontal`, `Eta2Reg` and
`Eta2Norms` supplied. Application only. -/
theorem ep1054_atomsZC (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- the explicit formula (lem:agamon): two links still open
    (hRe : EF.Rectangle) (hLD : EF.LeftLD)
    -- the major-arc weight links still open
    (pd : HM.PlusDecay) (fd : HM.PhiDecay) (mm : HM.MalMain)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited)
    -- the prop:espagn residue
    (res : EE.EspagnEdgeRes)
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
  FromAtomsZB.ep1054_atomsZB p z hRe AH.horizontal_holds hLD pd fd mm chk sm ch cp gr res
    E2.eta2Reg_holds E2.eta2Norms_holds hb1 hb2 hv1 her hs1 hs2 hs3 hZC rs cer hm hc h15 h12 h13
    h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZC
