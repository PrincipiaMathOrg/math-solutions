/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZE
import Principia.Common.TernaryGoldbach.EspagnEdgeRes
import Principia.Common.TernaryGoldbach.HelfMajS4Cases
import Principia.Common.TernaryGoldbach.HelfMajS4IBP
import Principia.Common.TernaryGoldbach.SecI2Arith

set_option autoImplicit false

/-!
# EP1054 on its atoms: the major arcs and `prop:espagn` closed

`FromAtomsZE.ep1054_atomsZE` with four more owed links supplied:
* `HM.PhiDecay`, `HM.PlusDecay` — `S4.phiDecay_holds`, `S4.plusDecay_holds` (`f9d5afcc`): the S4
  saddle-point bound, from two of Helfgott's CITED computations, `HC.AmanitaBisectCited` (only
  `E(1.5) ≥ 0.1598` is used) and `HC.AppBCited` (`C₂ ≤ 10.79195821038`). **The major arcs
  (`MR.HelfMajR`) now owe only the explicit formula, which is proved, and the cited zero count.**
* `EE.EspagnEdgeRes` — `ER.espagnEdgeRes` (`832c926f`): from the already-cited `CY.CERange`, along a
  four-regime spine, with no computation. **`prop:espagn` has no owed link.**
* `MPc.SecI2At` — replaced by `MPG.BogusEta2` through `MPS2.secI2At_of_gen` (`d3bb3b79`;
  `SecI2Arith` PROVED): `SecI2At` now rests on `lem:bogus` for `η₂` alone.

Application only. Every other binder is `FromAtomsZE`'s.

**OWED argument (6), all minor-arc:** `Bostb1Eta2`, `Bosta2Eta2` (each spined to three source
sub-links), `Vinland1At`, `EriksagaAt`, `BogusEta2`, `SecIIAt`.
**Cited machine computations (10):** Platt ×2; Helfgott's `EspagnCheck`, `EspagnSmall`, `Charpy`,
`Charpas`, `AusteriaGrid`, `MalMainCited`, `AmanitaBisectCited`, `AppBCited`.
**Cited published theorems (17):** unchanged.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZF

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZE.ep1054_atomsZE` with `PhiDecay`, `PlusDecay`,
`EspagnEdgeRes` supplied and `SecI2At` reduced to `BogusEta2`. Application only. -/
theorem ep1054_atomsZF (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited)
    -- the minarcs analytic links still open
    (hb1 : MPG.Bostb1Eta2) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hbo : MPG.BogusEta2) (hs3 : MPc.SecIIAt)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtomsZE.ep1054_atomsZE p z (S4.plusDecay_holds am ab) (S4.phiDecay_holds am) chk sm ch cp gr
    mc (ER.espagnEdgeRes cer) hb1 hb2 hv1 her (MPS2.secI2At_of_gen hbo) hs3 hZC rs cer hm hc h15 h12
    h13 h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZF
