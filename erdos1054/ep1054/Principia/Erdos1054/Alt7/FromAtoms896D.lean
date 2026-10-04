/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896C
import Principia.Common.TernaryGoldbach.MainBogusSpine
import Principia.Common.TernaryGoldbach.SecI2ArithD
import Principia.Common.TernaryGoldbach.TypeIIMonroFleming

set_option autoImplicit false

/-!
# EP1054 on the corrected route: `lem:bogus` CORRECTED, `MonroFleming` spined

`FromAtoms896.ep1054_atoms896` with every supply of `FromAtoms896C`, and
* `MPc.SecI2At` := `MPSD.secI2At_of_linksD` (`2f7591fe`, `829add69`) — `lem:bogus` in its corrected
  form (`eq:etoile`'s missing factor 3/2; `c₁` for `c1b`; `eq:gator` reweighted at window tops):
  `EsthelBogusED` PROVED, `SecI2ArithD` PROVED, and `MainBogusEta2C` from the cited checks plus the
  two coefficient sums `MPMB.CoefMainBound`, `MPMB.CoefErrBound`;
* `M2H.MonroFleming` := `M2F.monroFleming_of_links` (`7878a7d8`, verifier CONFIRMED): owes
  `CrustoCudo` (an exact finite identity) and `Monro2` (`lem:monro` with `eq:mudo`).

This bypasses the verbatim `MainBogusEta2` (refuted: `eq:etoile`) and `EsthelBogusEta2C` (not
derivable from the printed proof). `CortoLarge` is kept whole: its spine (`419aab0b`) rests on
`lem:yutto`, whose printed proof fails on `[10⁶, 10¹⁰)` and whose last step is false at `10¹⁰`.

Application only.

**OWED (8), all minor-arc:** `CoefMainBound`, `CoefErrBound`, `CrustoCudo`, `Monro2`, `CortoLarge`,
`Garn1a`, `Procida2Mont`, `SecIICalcC`. **Cited computations (15).** **Cited published theorems
(19).**
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896D

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**, `lem:bogus` corrected and `MonroFleming`
spined. Application only. -/
theorem ep1054_atoms896D (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited)
    -- the minarcs analytic links still open
    (hA : MPMB.CoefMainBound) (hE : MPMB.CoefErrBound) (cc : M2F.CrustoCudo) (mo : M2F.Monro2)
    (cl : M2H.CortoLarge) (g1a : T2X.Garn1a) (p2m : T2K.Procida2Mont) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  have hms : T2SC.Menson2C :=
    M2H.menson2C_of_links (M2F.monroFleming_of_links cc mo) M2G.grottoTab_holds cl cs
  have hk : T2S.Kraken := T2K.kraken_of_ls ls g1a p2m
  have hkl : T2S.KastLarge := KLR.kastLarge_of_rs75 r75
  have hel := MPEL.esthelLogEta2_holds
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
      hme (MPBM.bosta2Eta2_of_esthel cg wo MPE2.esthelEta2_holds) I2A.i2Arith
      (T2SC.vinland1AtC_of_deep hms hk kc hkl h13 hn) (T2SC.eriksagaAtC_of_deep hms hk kc hkl h13)
      (MPS1.secI1At_of_gen (MPBL.bostb1Eta2_of_esthel cg wo hel) hgr hro hme h15)
      (MPSD.secI2At_of_linksD (MPTS.trompaisEta2_of_cited cg wo)
        (MPMB.mainBogusEta2C_of
          (MPTC.etaHatBound_of MPTI.etaHatIBP_holds (MPTS.cameloSup_of cg wo)) hA hE)
        MPBE.esthelBogusED_holds)
      (T2SC.secIIAtC_of T2S.secInt_holds hms hk kc hkl h13 h2c) h15)
    h15
    (EF.austeria_of_links AG.rectangle_holds AH.horizontal_holds AG.continuation_holds
      AG.mollDecay_holds AG.mollLimit_holds AG.leftLD_holds hR hRS E2.eta2Reg_holds
      E2.eta2Norms_holds z gr AW.austeriaWindow HX.austeriaLip)
    (EB.eBound2_of_rs62 h12 h13 HW.etaPlus)

end Principia.Erdos1054.Alt7.FromAtoms896D
