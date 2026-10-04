/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromAtoms896H
import Principia.Common.TernaryGoldbach.TypeIIWeightXMV
import Principia.Common.TernaryGoldbach.TypeIISecIICalcC

set_option autoImplicit false

/-!
# EP1054 on the corrected route with NO owed analytic link

`FromAtoms896H.ep1054_atoms896H` with its last two links discharged:
* `T2SC.SecIICalcC` := `T2SII.secIICalcC_holds` (`81235dbc`), PROVED with no hypotheses: one
  bound on the `prop:kraken` factor covers both cases (Lean bound `0.3299` against the `0.34`
  target; Helfgott's route gives `0.275964` but needs `eq:garn1a` outside its hypothesis);
* `T2X.Garn1a` := `T2V.garn1a_of_mv8 mi mv mv8` (`31e07a32`), from Montgomery's inequality, the
  Montgomery–Vaughan weighted large sieve `T2G.MVWeighted` (checked against Montgomery, Bull. AMS
  84 (1978), p. 557, eq. (16)) and MV Lemma 8 above `R = 100`, `T2V.MV8Large`, as Helfgott quotes
  it (`minarcs.tex` 3524-3527; numerically true with margin `≥ 0.345` on `[100, 3000]`, tending to
  `≈ 0.389`). This repairs `eq:pokor2`, which counts `(W/2)` integers in `(W′, W]` where there can
  be `(W + 1)/2`, by choosing `R = (7X/23)^{1/2}`.

Application only.

**The theorem rests on cited inputs only.** No analytic link is owed. **Cited computations (18):**
Platt ×2 and 16 of Helfgott's. **Cited published theorems (23):** the 17, `RS75Cor2`,
`LargeSieve`, `MontgomeryIneq`, `RamareMarraki`, `MVWeighted`, `MV8Large`.
-/

namespace Principia.Erdos1054.Alt7.FromAtoms896I

open Principia.Common.TernaryGoldbach

/-- **EP1054 from cited inputs only**, on the corrected minor-arc route (Main Theorem constant
`0.896`). Every hypothesis is a cited machine computation or a cited published theorem.
Application only. -/
theorem ep1054_atoms896I (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    -- Helfgott's cited runs
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited) (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
    (hRc : HC.RamareCited)
    -- literature (cited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) (hMk : M2Y.RamareMarraki)
    (mv : T2G.MVWeighted) (mv8 : T2V.MV8Large) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromAtoms896H.ep1054_atoms896H p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc
    (T2V.garn1a_of_mv8 mi mv mv8) T2SII.secIICalcC_holds hZC rs cer hm hc h15 h12 h13 h316 h324
    h330 h332 hR hRS hgr hro hme r75 ls mi hMk

end Principia.Erdos1054.Alt7.FromAtoms896I
