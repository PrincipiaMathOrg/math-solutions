/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZD
import Principia.Common.TernaryGoldbach.AgamonRectangle
import Principia.Common.TernaryGoldbach.HelfMajElem4

set_option autoImplicit false

/-!
# EP1054 on its atoms: `lem:agamon` closed, `MalMain` proved

`FromAtomsZD.ep1054_atomsZD` with two more owed links supplied:
* `EF.Rectangle` — `AG.rectangle_holds` (`ef93e2e0`, no hypothesis): the residue theorem for
  finitely many simple poles on `[−1/2, 3/2] × [−T, T]` plus the zero map of `L(s, χ)`.
  **`lem:agamon` (`HM.ExplicitFormula`) now has no open link.**
* `HM.MalMain` — `HM.malMain_of_cited` (`0b38797b`): proved at its STATED constants from Helfgott's
  two VNODE-LP values, which enter as the cited machine computation `HC.MalMainCited` (owner
  directive 2026-09-30: Helfgott's computer checks are cited at his exact statements).

Application only. Every other binder is `FromAtomsZD`'s.

**OWED argument (9):** `PlusDecay`, `PhiDecay`; `EspagnEdgeRes`; six analytic minarcs links:
`Bostb1Eta2`, `Bosta2Eta2`, `Vinland1At`, `EriksagaAt`, `SecI2At`, `SecIIAt`.
**Cited machine computations (8):** Platt ×2; Helfgott's `EspagnCheck`, `EspagnSmall`, `Charpy`,
`Charpas`, `AusteriaGrid`, `MalMainCited`. **Cited published theorems (17):** unchanged (owner
decision 2026-10-02: cite all 17).
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZE

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZD.ep1054_atomsZD` with `Rectangle` and `MalMain`
supplied. Application only. -/
theorem ep1054_atomsZE (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- the major-arc weight links still open
    (pd : HM.PlusDecay) (fd : HM.PhiDecay)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    -- the prop:espagn residue
    (res : EE.EspagnEdgeRes)
    -- the minarcs analytic links still open
    (hb1 : MPG.Bostb1Eta2) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hs2 : MPc.SecI2At) (hs3 : MPc.SecIIAt)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtomsZD.ep1054_atomsZD p z AG.rectangle_holds pd fd (HM.malMain_of_cited mc) chk sm ch cp gr
    res hb1 hb2 hv1 her hs2 hs3 hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZE
