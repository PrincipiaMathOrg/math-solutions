/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZCS
import Principia.Common.TernaryGoldbach.AgamonLeftLDHolds

set_option autoImplicit false

/-!
# EP1054 on its atoms: `LeftLD` proved

`FromAtomsZCS.ep1054_atomsZCS` (`Bostb1At`, `SecI1At` from the one generic `MPG.Bostb1Eta2`) with
`EF.LeftLD` supplied by `AG.leftLD_holds` (`9c2b6345`, no hypothesis): the left-line bound
`∫|L'/L(−1/2 + iτ, χ)|²/|s|² dτ ≤ 2π(log q + 8)²` for every primitive `χ`, from the asymmetric
functional equation (`LDFE`), `|ψ(z) − log z| ≤ 1/2` on `Re z = 3/2` (`DigammaLine`),
`∑ Λ(n)n^{−3/2} ≤ 7/4` (`VM32`) and an explicit `K`-integral (`KInt`).

`lem:agamon` now owes only `Rectangle`. Application only. Every other binder is `FromAtomsZCS`'s.

**OWED argument (11):** `Rectangle`; `PlusDecay`, `PhiDecay`, `MalMain`; `EspagnEdgeRes`; six
analytic minarcs links: `Bostb1Eta2`, `Bosta2Eta2`, `Vinland1At`, `EriksagaAt`, `SecI2At`,
`SecIIAt`. Cited (7) and literature (17) are unchanged.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZD

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZCS.ep1054_atomsZCS` with `LeftLD` supplied. Application
only. -/
theorem ep1054_atomsZD (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- the explicit formula (lem:agamon): one link still open
    (hRe : EF.Rectangle)
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
  FromAtomsZCS.ep1054_atomsZCS p z hRe AG.leftLD_holds pd fd mm chk sm ch cp gr res hb1 hb2 hv1
    her hs2 hs3 hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme

end Principia.Erdos1054.Alt7.FromAtomsZD
