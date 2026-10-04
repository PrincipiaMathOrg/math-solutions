/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZF
import Principia.Common.TernaryGoldbach.BogusEta2C

set_option autoImplicit false

/-!
# EP1054 on its atoms: `lem:bogus` taken in its CORRECTED form

`FromAtomsZF.ep1054_atomsZF` with `MPc.SecI2At` supplied from `MPBC.BogusEta2C` (`0f9bd1fd`)
instead of the verbatim `MPG.BogusEta2`.

**Why.** Helfgott's printed `eq:tvorog` reads `log⁺(e²D/(x/|δ|q))`, but its own proof (`eq:iulia`)
gives `log⁺(e²D/((Q+1)/2))` with `Q = ⌊x/|δq|⌋`, i.e. `log⁺(2e²D/(x/|δ|q))` — a missing factor 2.
The verbatim `BogusEta2` is therefore NOT derivable from the source (it is not refuted either).
`BogusEta2C` states the branch the proof actually gives; it is implied by the verbatim form
(`MPBC.bogusC_of_verbatim`), so it is the weaker, honest hypothesis, and the `S_{I,2}` arithmetic
still closes with it (`MPBC.secI2ArithC`).

Application only. Every other binder is `FromAtomsZF`'s.

**OWED argument (6), all minor-arc:** `Bostb1Eta2`, `Bosta2Eta2`, `Vinland1At`, `EriksagaAt`,
`BogusEta2C`, `SecIIAt`. Cited computations (10) and cited published theorems (17) unchanged.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZG

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZF.ep1054_atomsZF` with `lem:bogus` in its corrected form.
Application only. -/
theorem ep1054_atomsZG (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited)
    -- the minarcs analytic links still open
    (hb1 : MPG.Bostb1Eta2) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hbo : MPBC.BogusEta2C) (hs3 : MPc.SecIIAt)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtomsZE.ep1054_atomsZE p z (S4.plusDecay_holds am ab) (S4.phiDecay_holds am) chk sm ch cp gr
    mc (ER.espagnEdgeRes cer) hb1 hb2 hv1 her (MPBC.secI2At_of_genC hbo) hs3 hZC rs cer hm hc h15
    h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZG
