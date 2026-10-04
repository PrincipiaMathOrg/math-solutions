/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896F
import Principia.Common.TernaryGoldbach.TypeIICountSq
import Principia.Common.TernaryGoldbach.TypeIIProcidaMont

set_option autoImplicit false

/-!
# EP1054 on the corrected route: `MonroFleming` PROVED, `Procida2Mont` supplied

`FromTop896.ep1054_top896`, assembled as `FromAtoms896F` (`lem:bogus` closed from cited inputs), and
* `M2H.MonroFleming` := `M2Q.monroFleming_holds` (`d040ed3a`), with NO hypotheses: through
  `Monro2B` (constant 10.25 in place of `lem:monro`'s 1.27, which rests on Helfgott's uncited check
  `f(x) ≤ 1.26981x`) and `CountSq` (Möbius inversion and Mathlib's `ζ(2) = π²/6`);
* `T2S.Kraken` := `T2M.kraken_of_mont ls mi g1a` (`0e531321`): `Procida2Mont` PROVED with the case
  split `lem:ogor` omits, from the large sieve and Montgomery's inequality, `T2M.MontgomeryIneq`
  (Montgomery 1968; Iwaniec–Kowalski Lemma 7.15, `ω(p) = 1`), a NEW cited published theorem.

Application only.

**OWED (3), all minor-arc Type II:** `CortoLarge`, `Garn1a`, `SecIICalcC`. **Cited computations
(15).** **Cited published theorems (20):** the 17, `RS75Cor2`, `LargeSieve`, `MontgomeryIneq`.
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896G

open Principia.Common.TernaryGoldbach

/-- **EP1054 from its atoms on the corrected route**: `lem:bogus` closed, `MonroFleming` proved,
`Kraken` down to `Garn1a`. Application only. -/
theorem ep1054_atoms896G (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited)
    -- the minarcs analytic links still open
    (cl : M2H.CortoLarge) (g1a : T2X.Garn1a) (h2c : T2SC.SecIICalcC)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  have hms : T2SC.Menson2C :=
    M2H.menson2C_of_links M2Q.monroFleming_holds M2G.grottoTab_holds cl cs
  have hk : T2S.Kraken := T2M.kraken_of_mont ls mi g1a
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
          (MPTC.etaHatBound_of MPTI.etaHatIBP_holds (MPTS.cameloSup_of cg wo))
          (MPCB.coefMainBound_of hgr h12) (MPCB.coefErrBound_of h12))
        MPBE.esthelBogusED_holds)
      (T2SC.secIIAtC_of T2S.secInt_holds hms hk kc hkl h13 h2c) h15)
    h15
    (EF.austeria_of_links AG.rectangle_holds AH.horizontal_holds AG.continuation_holds
      AG.mollDecay_holds AG.mollLimit_holds AG.leftLD_holds hR hRS E2.eta2Reg_holds
      E2.eta2Norms_holds z gr AW.austeriaWindow HX.austeriaLip)
    (EB.eBound2_of_rs62 h12 h13 HW.etaPlus)

end Principia.Erdos1054.Alt7.FromAtoms896G
