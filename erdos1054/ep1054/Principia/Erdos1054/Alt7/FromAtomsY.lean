/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromWeightsC
import Principia.Common.TernaryGoldbach.HelfMajElem2
import Principia.Common.TernaryGoldbach.ExplicitSpine
import Principia.Common.TernaryGoldbach.LargeQTail
import Principia.Common.TernaryGoldbach.EspagnEdgeCover
import Principia.Common.TernaryGoldbach.EBoundRS
import Principia.Common.TernaryGoldbach.MinPiecesI1
import Principia.Common.TernaryGoldbach.MinPiecesII
import Principia.Common.TernaryGoldbach.AusteriaWindow
import Principia.Common.TernaryGoldbach.StarMass

set_option autoImplicit false

/-!
# EP1054 on its atoms, fully opened (evening 2026-09-30)

`FromWeightsC.ep1054_topC` (`c⁻ = −1.39`, `MNumPm` proved) with every hypothesis opened as far as
the proved compositions go. Application only.

**Supplied** (proved):
* the major arcs: `HM.helfMajR_of_10`, with `Hausierer` proved (`AbelZeros`, `RealSym`);
* `ExplicitFormula`: `EF.agamon_of_links`, with `StartLine` and `MollReg` proved;
* `prop:nefumo`: `SM.zvsL_star`;
* `prop:espagn`: through `EE.espagnRed_of_rs2`, `LQ.espagnLargeQ_of_rs62` and
  `HX.charpyGap_of_charpas`, the hole cut to `EE.EspagnEdgeRes`;
* the minarcs Main Theorem: `MPc.minMainP_of_links` with `I1Arith`, `IIArith` and `CoexistArith`
  proved;
* `cor:austeria`: `EF.austeria_of_links`, with `AW.austeriaWindow` and `HX.austeriaLip` proved;
* the E bound: `EB.eBound2_of_rs62`.

**Binders by kind:**
* **CITED machine verification:** Platt ×2; Helfgott's runs `EspagnCheck`, `EspagnSmall`,
  `Charpy`, `Charpas`, `AusteriaGrid`.
* **Literature, OWNER QUESTION:**
  - Rosser–Schoenfeld 1962: `CERange`, `RS62Thm12`, `RS62Thm13`, `RS62Thm15`, and (3.16), (3.24),
    (3.30), (3.32);
  - Rosser–Schoenfeld 1975: `RS75Theta`;
  - Ramaré 1995: `Malito`, `Cante`;
  - the zero count `ZeroCount`;
  - Rosser 1941 L17 and Ramaré–Saouter 2003 L2;
  - Granville–Ramaré, Ramaré 2015 and Meproz: `Grara`, `Ronsard`, `Meproz`.
* **OWED argument:**
  - the six `lem:agamon` links;
  - the eight Plus/Phi/Mal weight links;
  - `EspagnEdgeRes`;
  - `Eta2Reg`, `Eta2Norms`;
  - the eight analytic minarcs links.
-/

namespace Principia.Erdos1054.Alt7.FromAtomsY

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms, fully opened.** Application only. -/
theorem ep1054_atomsY (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- the explicit formula (lem:agamon): six links
    (hRe : EF.Rectangle) (hHo : EF.Horizontal) (hCo : EF.Continuation) (hDe : EF.MollDecay)
    (hML : EF.MollLimit) (hLD : EF.LeftLD)
    -- the major-arc weight links
    (pr : HM.PlusReg) (pn : HM.PlusNorms) (pd : HM.PlusDecay) (fd : HM.PhiDecay)
    (mr : HM.MalReg) (mn : HM.MalNorms) (md : HM.MalDecay) (mm : HM.MalMain)
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
    (HM.helfMajR_of_10 (EF.agamon_of_links hRe hHo hCo hDe hML hLD) hZC pr pn pd fd mr mn md mm)
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

end Principia.Erdos1054.Alt7.FromAtomsY
