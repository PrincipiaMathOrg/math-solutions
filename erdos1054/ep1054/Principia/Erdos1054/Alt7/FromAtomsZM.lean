/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZ
import Principia.Common.TernaryGoldbach.HelfMajElem5

set_option autoImplicit false

/-!
# EP1054 on its atoms: `FromAtomsZ` with `MalDecay` removed

`FromAtomsZ.ep1054_atomsZ` with the major arcs supplied by `HM.helfMajR_of_5` (`549b970f`) instead
of `HM.helfMajR_of_6`: `MalDecay` is REPLACED by the proved `HP.MalDecayL`
(`|Mη₊,₂(s)| ≤ 5·10⁵·fmal`), with Prop 1.5 re-derived at it (`HP.malheurR_of_linksL2`).

Application only. Every other binder is `FromAtomsZ`'s; the owed weight links are now
`PlusDecay`, `PhiDecay`, `MalMain` (three, was four).
-/

namespace Principia.Erdos1054.Alt7.FromAtomsZM

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms**: `FromAtomsZ.ep1054_atomsZ` without `MalDecay`. Application only. -/
theorem ep1054_atomsZM (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- the explicit formula (lem:agamon): six links
    (hRe : EF.Rectangle) (hHo : EF.Horizontal) (hCo : EF.Continuation) (hDe : EF.MollDecay)
    (hML : EF.MollLimit) (hLD : EF.LeftLD)
    -- the major-arc weight links still open
    (pd : HM.PlusDecay) (fd : HM.PhiDecay) (mm : HM.MalMain)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited)
    -- the prop:espagn residue, the eta2 links of lem:crepe
    (res : EE.EspagnEdgeRes) (e1 : EF.Eta2Reg) (e2 : EF.Eta2Norms)
    -- the minarcs analytic links
    (hb1 : MPc.Bostb1At) (hb2 : MPc.Bosta2Eta2) (hA2 : MPc.I2Arith) (hv1 : MPc.Vinland1At)
    (her : MPc.EriksagaAt) (hs1 : MPc.SecI1At) (hs2 : MPc.SecI2At) (hs3 : MPc.SecIIAt)
    -- literature
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromWeightsC.ep1054_topC p z
    (HM.helfMajR_of_5 (EF.agamon_of_links hRe hHo hCo hDe hML hLD) hZC pd fd mm)
    SM.zvsL_star
    (HC.espagnWin_of_cited
      (EE.espagnRed_of_rs2 rs h15 res (LQ.espagnLargeQ_of_rs62 h316 h324 h330 h332)) cer hm hc ch
      (HX.charpyGap_of_charpas cp) sm chk)
    (MPc.minMainP_of_links hb1 hgr hro hme MPI1.i1Arith hb2 hA2 hv1 her MPII.iiArith hs1 hs2 hs3
      MPA.coexistArith h15)
    h15
    (EF.austeria_of_links hRe hHo hCo hDe hML hLD hR hRS e1 e2 z gr AW.austeriaWindow
      HX.austeriaLip)
    (EB.eBound2_of_rs62 h12 h13 HW.etaPlus)

end Principia.Erdos1054.Alt7.FromAtomsZM
