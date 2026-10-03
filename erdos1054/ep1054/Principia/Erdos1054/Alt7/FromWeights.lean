/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromMajR
import Principia.Erdos1054.Proofs.BalancedW
import Principia.Common.TernaryGoldbach.WeightsSmall

set_option autoImplicit false

/-!
# EP1054 through the weight-aware balanced reduction: the minor budget rises to `0.84`

`FromMajR.ep1054_majR` reaches `lem:fraiture-balanced-goldbach` through
`BalancedT0.balanced_of_cheb`, which charges each exceptional triple the weights' SUP norms, so it
needs `HelfgottAt 0.000205`. The split then leaves the minor arcs the target `1.0154`, and the
closing `M̃` constant `0.8095`. The minarcs Main Theorem, corrected (the Conclusion's AM-GM,
`0.5 ↦ 0.811`, and `lem:bosta2` at scale `x/v`, `C ↦ 45.7575`), has `M̃ ≈ 0.8185`
(LEAN-PROGRESS 2026-09-30), which does not fit.

Helfgott's weights vanish at `0` (`WS.etaPlus_le_lin`: `|η₊(t)| ≤ 3t`; `WS.etaStar_le_lin`:
`|η_*(t)| ≤ 250t`), and an exceptional coordinate sits at `t ≤ 1.1·10⁻⁶`. So
`BalancedW.balanced_of_w` needs only `HelfgottAtW 2·10⁻⁸ 3 250`, and:

* **the split** (`helfAtW_chebR`): the major arcs at `c_maj' = 1.0563578` (`MR.majorAt_c0R`,
  unchanged) and the minor arcs at `1.05635`:
  `(7.8·10⁻⁶)(490/989)²/49 − 13.73·10⁻⁹ = 2.5345·10⁻⁸ ≥ 2·10⁻⁸`;
* **the closing** (`close_w`): `(√(1.2533143·0.84037) + √1.0532·10⁻¹¹)² = 1.0532566 ≤ 1.05635`, so
  the `M̃` constant is `0.84`, against `0.8095` (the largest that closes is about `0.8424`);
* **the headline** (`ep1054_weights`): `ep1054_majR` with `OL.MNumL HW.phi 8.54 0.8095 0.6406`
  relaxed to `OL.MNumL HW.phi 8.54 0.84 0.6406` (`ep1054_weights_of_majR` shows it is no
  stronger).

The corrected minor chain (`OstopL`/`MNumL` restated at `(0.811, 45.7575)`) attaches here: its
`M̃ ≈ 0.8185` leaves `0.0215` for `MNumL`'s proof loss.

The paper's proof of `lem:fraiture-balanced-goldbach` (EP1054.tex 856–898) uses the sup bounds
only; this route no longer factors through `Cite_Helfgott_weighted`, only through Helfgott's fixed
weights, which is what the chain proves anyway.
-/

namespace Principia.Erdos1054.Alt7.FromWeights

open Principia.Common.TernaryGoldbach
open Principia.Erdos1054.Proofs.BalancedW (HelfgottAtW)

/-- **THE SPLIT FOR HELFGOTT'S OWN WEIGHTS at `K = 2·10⁻⁸`** (from `MR.helfAt_smooth_chebR`, with
the existential instantiated at `η₊, η_*` and the small-argument bounds added): the major arcs at
`1.0563578`, the minor arcs at `1.05635`;
`(7.8·10⁻⁶)(490/989)²/49 − 13.73·10⁻⁹ = 2.5345·10⁻⁸ ≥ 2·10⁻⁸`. -/
theorem helfAtW_chebR (mj : RT.MajorLowerAt 1.0563578 HW.etaPlus HW.etaStar)
    (mn : RT.MinorUpperAt 1.05635 HW.etaPlus HW.etaStar) : HelfgottAtW 2e-8 3 250 := by
  have sb := BL.supBounds_helf
  have sm := RT.summ_of_majorAt (by norm_num) HW.etaPlus HW.etaStar mj
  have ci := SmCI.circleId_of_summ HW.etaPlus HW.etaStar sm
  intro H hodd hH
  refine ⟨HW.etaPlus, HW.etaStar, sb.1, sb.2, fun u h0 _ => WS.etaPlus_le_lin u h0,
    fun u h0 _ => WS.etaStar_le_lin u h0, ?_⟩
  change (2e-8 : ℝ) * (H : ℝ) ^ 2 ≤ Smooth.citeSum HW.etaPlus HW.etaStar H
  have hW := RT.weighted_lower_at 1.0563578 1.05635 HW.etaPlus HW.etaStar sm ci mj mn H hodd hH
  have hc : (1.0563578 - 1.05635 : ℝ) = 7.8e-6 := by norm_num
  rw [hc] at hW
  have hP := SmPP.pp_crude HW.etaPlus HW.etaStar sb H hodd hH
  have hH0 : (0 : ℝ) ≤ (490 : ℝ) / 989 * H := by positivity
  have hx2 : ((490 : ℝ) / 989 * H) ^ 2 ≤ Principia.Erdos1054.helfgottX H ^ 2 :=
    pow_le_pow_left₀ hH0 (Smooth.helfX_ge H) 2
  have hx2' : (490 : ℝ) ^ 2 / 989 ^ 2 * (H : ℝ) ^ 2 ≤ Principia.Erdos1054.helfgottX H ^ 2 :=
    le_of_eq_of_le (by ring) hx2
  have hE := SmPP.ppErr_le H hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **The minor closing at `1.05635` with `cM = 0.84`**:
`(√(1.2533143·0.84037) + √1.0532·10⁻¹¹)² = 1.0532566 ≤ 1.05635`. -/
theorem close_w : (Real.sqrt (1.2533143 * (0.84 + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    1.05635 :=
  MinSp.close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cM_w : (0 : ℝ) ≤ 0.84 + 3.7e-4 := by norm_num

/-- **EP1054 through the weight-aware reduction.** `FromMajR.ep1054_majR` with
`BalancedT0.balanced_of_cheb ∘ MR.helfgottAt_chebR` replaced by
`BalancedW.balanced_of_w ∘ helfAtW_chebR`, and the `M̃` constant relaxed from `0.8095` to
`0.84`. Application only. -/
theorem ep1054_weights (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (hos : OL.OstopL HW.etaPlus HW.etaStar HW.phi)
    (hmn : OL.MNumL HW.phi 8.54 0.84 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  Round7Bal.ep1054_all_bal (Proofs.BalancedW.balanced_of_w
    (helfAtW_chebR
      (MR.majorAt_c0R HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hr
        RT.starScale_helf RW.regW_helf nf
        (MR.drujalE100R_of_spine HW.etaPlus pa ai DP.mardiQ_helf KS.ksmall_helf)
        CT.clowerE_helf (EN.normsB27_helf BS.band_sharp) EN.supN_helf
        (PC.plattFull_of_cited p z))
      (MR.minorAt_ostopL_helfR 1.05635 0.84 8.55451 8.54 0.6406 close_w cM_w MR.hJ0_8545
        MR.floor_854R OL.hp0_854 (PC.plattFull_of_cited p z) hr
        (MR.felipaAt_6406R (PC.plattFull_of_cited p z) hr) hos
        (MR.drujalLowPR_of_spine HW.etaPlus HW.etaCirc pa ai DP.bandQ_helf DP.tailQ_helf
          KS.ksmall_helf)
        OL.lamberNumL_helf hmn)))

/-- **No stronger than `ep1054_majR`**: its `MNumL` at `0.8095` gives this one's at `0.84`
(`OL.mnumL_const_mono`). -/
theorem ep1054_weights_of_majR (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hr : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (hos : OL.OstopL HW.etaPlus HW.etaStar HW.phi)
    (hmn : OL.MNumL HW.phi 8.54 0.8095 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_weights p z hr nf pa ai hos
    (OL.mnumL_const_mono HW.phi 8.54 0.8095 0.84 0.6406 (by norm_num) hmn)

end Principia.Erdos1054.Alt7.FromWeights
