/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZC
import Principia.Common.TernaryGoldbach.SecI1Arith

set_option autoImplicit false

/-!
# EP1054 on its atoms: `Bostb1At` and `SecI1At` from the one generic `lem:bostb1` link

`FromAtomsZC.ep1054_atomsZC` carries two minor-arc links that are the same lemma applied twice:
`MPc.Bostb1At` (`lem:bostb1` at the first choice) and `MPc.SecI1At` (`lem:bostb1` at the second
choice plus the Totals algebra). This file replaces both by the single generic link
`MPG.Bostb1Eta2` — `lem:bostb1` for `η₂` with the book's hypotheses, main term corrected (T6) — via
* `MPG.bostb1At_of_gen` (the first-choice instantiation, PROVED), and
* `MPS1.secI1At_of_gen` (the second-choice instantiation with `MPS1.secI1Arith`, the Totals
  algebra `2.4719x^{2/3}log x + 0.00289x^{2/3}(log x)²`, PROVED).
Application only. Every other binder is `FromAtomsZC`'s.

**OWED argument (12):** `lem:agamon` (`Rectangle`, `LeftLD`); `PlusDecay`, `PhiDecay`, `MalMain`;
`EspagnEdgeRes`; six analytic minarcs links: `Bostb1Eta2`, `Bosta2Eta2`, `Vinland1At`,
`EriksagaAt`, `SecI2At`, `SecIIAt`.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZCS

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZC.ep1054_atomsZC` with `Bostb1At` and `SecI1At` replaced
by `MPG.Bostb1Eta2`. Application only. -/
theorem ep1054_atomsZCS (p : PC.PlattThm71) (z : PC.PlattTrudgian)
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
    (hb1 : MPG.Bostb1Eta2) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hs2 : MPc.SecI2At) (hs3 : MPc.SecIIAt)
    -- literature
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtomsZC.ep1054_atomsZC p z hRe hLD pd fd mm chk sm ch cp gr res (MPG.bostb1At_of_gen hb1)
    hb2 hv1 her (MPS1.secI1At_of_gen hb1 hgr hro hme h15) hs2 hs3 hZC rs cer hm hc h15 h12 h13
    h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZCS
