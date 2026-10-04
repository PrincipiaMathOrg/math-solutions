/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtomsZH
import Principia.Erdos1054.Alt7.FromTop896
import Principia.Common.TernaryGoldbach.TypeIIErikCalcC

set_option autoImplicit false

/-!
# EP1054 on its atoms, on the CORRECTED minor-arc route (Main Theorem constant `0.896`)

`eq:passi`/`eq:velib` were refereed FALSE (2026-10-03), so `FromAtomsZH`'s three owed links
`Vinland1At`, `EriksagaAt`, `SecIIAt` (Helfgott's printed displays, which rest on them) are not
the honest targets. This file runs the same atoms through `FromTop896.ep1054_top896` with
`hmm := MTC.minMainPC_of_open` and the Type II sums on the corrected spine (`TypeIISpineC`):
* `Bostb1At`, `SecI1At` from `MPBL.bostb1Eta2_of_esthel cg wo hel` (via `MPG.bostb1At_of_gen`,
  `MPS1.secI1At_of_gen`); `Bosta2Eta2` from `MPBM.bosta2Eta2_of_esthel cg wo he2`; `I2Arith` is
  `I2A.i2Arith`;
* `SecI2At` from `MPBC.secI2At_of_genC`, with `MPBC.BogusEta2C` itself split by
  `MPBC.bogusEta2C_of` into `TrompaisEta2` (PROVED from the cited `CameloGrid`/`Wollust`,
  `MPTS.trompaisEta2_of_cited`), `MPBG.MainBogusEta2` and `MPBC.EsthelBogusEta2C`;
* `T2SC.Vinland1AtC`, `T2SC.EriksagaAtC` from `T2SC.vinland1AtC_of_deep`,
  `T2SC.eriksagaAtC_of_deep`; `SecIIAt` from `T2SC.secIIAtC_of` with `T2S.secInt_holds`.
The major arcs, `prop:espagn`, `Austeria` and `EBound2` are supplied exactly as along
`FromAtomsZB` ... `ZH`.

Application only.

**OWED (8), all minor-arc:** `MPB2.EsthelEta2`, `MPB1.EsthelLogEta2`, `MPBG.MainBogusEta2`,
`MPBC.EsthelBogusEta2C`, `T2SC.Menson2C`, `T2S.Kraken`, `T2S.KastLarge`, `T2SC.SecIICalcC`.
**Cited computations (14):** Platt x2; Helfgott's `EspagnCheck`, `EspagnSmall`, `Charpy`,
`Charpas`, `AusteriaGrid`, `MalMainCited`, `AmanitaBisectCited`, `AppBCited`, `CameloGridCited`,
`WollustCited`, `KastCited`, `NotungCited`. **Cited published theorems (17).**
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected minor-arc route** (Main Theorem constant `0.896`).
Application only. -/
theorem ep1054_atoms896 (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    -- the minarcs analytic links still open
    (he2 : MPB2.EsthelEta2) (hel : MPB1.EsthelLogEta2) (hmb : MPBG.MainBogusEta2)
    (heb : MPBC.EsthelBogusEta2C) (hms : T2SC.Menson2C) (hk : T2S.Kraken)
    (hkl : T2S.KastLarge) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromTop896.ep1054_top896 p z
    (HM.helfMajR_of_5
      (EF.agamon_of_links AG.rectangle_holds AH.horizontal_holds AG.continuation_holds
        AG.mollDecay_holds AG.mollLimit_holds AG.leftLD_holds)
      hZC (S4.plusDecay_holds am ab) (S4.phiDecay_holds am) (HM.malMain_of_cited mc))
    SM.zvsL_star
    (HC.espagnWin_of_cited
      (EE.espagnRed_of_rs2 rs h15 (ER.espagnEdgeRes cer)
        (LQ.espagnLargeQ_of_rs62 h316 h324 h330 h332)) cer hm hc ch
      (HX.charpyGap_of_charpas cp) sm chk)
    (MTC.minMainPC_of_open (MPG.bostb1At_of_gen (MPBL.bostb1Eta2_of_esthel cg wo hel)) hgr hro
      hme (MPBM.bosta2Eta2_of_esthel cg wo he2) I2A.i2Arith
      (T2SC.vinland1AtC_of_deep hms hk kc hkl h13 hn) (T2SC.eriksagaAtC_of_deep hms hk kc hkl h13)
      (MPS1.secI1At_of_gen (MPBL.bostb1Eta2_of_esthel cg wo hel) hgr hro hme h15)
      (MPBC.secI2At_of_genC (MPBC.bogusEta2C_of (MPTS.trompaisEta2_of_cited cg wo) hmb heb))
      (T2SC.secIIAtC_of T2S.secInt_holds hms hk kc hkl h13 h2c) h15)
    h15
    (EF.austeria_of_links AG.rectangle_holds AH.horizontal_holds AG.continuation_holds
      AG.mollDecay_holds AG.mollLimit_holds AG.leftLD_holds hR hRS E2.eta2Reg_holds
      E2.eta2Norms_holds z gr AW.austeriaWindow HX.austeriaLip)
    (EB.eBound2_of_rs62 h12 h13 HW.etaPlus)

end Principia.Erdos1054.Alt7.FromAtoms896
