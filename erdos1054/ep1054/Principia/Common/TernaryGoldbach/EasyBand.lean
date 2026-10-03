/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EasyHelf

set_option autoImplicit false

/-!
# The band-limiting constant a THIRD integration by parts can reach: `2.5·10⁻⁴`, major at `1.0486`

`EN.BandSharp` asks `|h₂₀₀ − h| ≤ 4.5·10⁻⁵` (true sup `1.138·10⁻⁵`). The coordinator measured
(LEAN-PROGRESS, "BANDSHARP BY A THIRD IBP") that a provable third-order integration by parts
reaches `2.0·10⁻⁴` uniformly in `t`, not `4.5·10⁻⁵`. This file re-targets the major side to what
that proof can deliver, per the coordinator's plan: `BandSharp25` (`c = 2.5·10⁻⁴`), and the
retarget's major constant lowered from `1.049` to `1.0486`, with the minor arcs kept at `0.9845`.

* `NormsB` — `EN.NormsE` with `|η₊ − η∘|₂ ≤ 1.6665·10⁻⁴ = 0.6666·2.5·10⁻⁴` (the only change);
  implied by `NormsE` (`normsB_of_normsE`); on Helfgott's weights it follows from `BandSharp25`
  (`normsB_helf`) through `EN.l2_diff_of_unif`, `EN.l2_plus_of_unif`.
* `arith_close_band` — the `prop:nefumo` bound at `ε₀ = 2.0832·10⁻⁴`
  (`1.6665·10⁻⁴ < 2.0832·10⁻⁴·0.8 = 1.66656·10⁻⁴`). Units `x²/49`: main `1.0495810`, line 1
  `≤ 7.726·10⁻⁴·1.2533143 = 9.683·10⁻⁴` (the bracket is `7.725209·10⁻⁴`), lines 2, 3 as in
  `EN.arith_close_easy`. Net `1.0486096 ≥ 1.0486`, margin `9.6·10⁻⁶` (exact rationals).
* `helfAt_smooth_band` — `RT.helfgottAt_of_smooth` at major `1.0486`:
  `(1.0486 − 0.9845)(490/989)²/49 − 13.73·10⁻⁹ = 3.21102·10⁻⁴ ≥ 0.00032`, margin `1.1·10⁻⁶`.
* `helfgottAt_band25` — `HelfgottAt 0.00032` on Helfgott's weights from `PlattFull`, HelfMaj,
  `Reg`, `Nefumo`, `DrujalE`, `CLowerE`, `BandSharp25` and the minor arcs at `0.9845`.

Every new `Prop` constrains: `BandSharp25` is implied by `BandSharp` and implies the proved
`HW.BandUniform`; `NormsB` rejects `η∘ = 0` (`normsB_zero_o`).
-/

namespace Principia.Common.TernaryGoldbach.EN

open MeasureTheory Principia.Common.Goldbach
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## The obligation and the relaxed norms -/

/-- **`BandSharp` at the third-IBP constant**: `|h₂₀₀(t) − h(t)| ≤ 2.5·10⁻⁴` for every `t > 0`
(provable chain `2.0·10⁻⁴`, coordinator's measurement; true sup `1.138·10⁻⁵`). OPEN. -/
def BandSharp25 : Prop := ∀ t : ℝ, 0 < t → |HW.hH 200 t - HW.hFun t| ≤ 2.5e-4

/-- `BandSharp → BandSharp25`. -/
theorem bandSharp25_of_sharp (hb : BandSharp) : BandSharp25 :=
  fun t ht => (hb t ht).trans (by norm_num)

/-- `BandSharp25` is STRONGER than the proved `HW.BandUniform` (`0.13`). -/
theorem bandSharp25_uniform (hb : BandSharp25) : HW.BandUniform :=
  fun t ht => (hb t ht).trans (by norm_num)

/-- **`NormsE` with `|η₊ − η∘|₂ ≤ 1.6665·10⁻⁴`** (every other conjunct unchanged). -/
def NormsB (ηp ηs ηo : ℝ → ℝ) : Prop :=
  0.8 ≤ MajSp.l2 ηo ∧ MajSp.l2 ηo ≤ 0.8002 ∧ MajSp.l2 (fun t => ηp t - ηo t) ≤ 1.6665e-4 ∧
    MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 ∧ MajSp.l2 (deriv ηo) ^ 2 ≤ 3 ∧
    MajSp.l1 ηs = Real.sqrt (Real.pi / 2) / 49 ∧ MajSp.l2 ηs ^ 2 ≤ 2 / 49 ∧
    MajSp.l1 ηp ≤ 1.2 ∧ MajSp.l2 ηp ≤ 0.81

/-- `NormsE → NormsB`. -/
theorem normsB_of_normsE (ηp ηs ηo : ℝ → ℝ) (nm : NormsE ηp ηs ηo) : NormsB ηp ηs ηo := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := nm
  exact ⟨h1, h2, le_trans h3 (by norm_num), h4, h5, h6, h7, h8, h9⟩

/-- `NormsB` still rejects `η∘ = 0`. -/
theorem normsB_zero_o (ηp ηs : ℝ → ℝ) : ¬ NormsB ηp ηs 0 := by
  intro h
  have h1 := h.1
  rw [MajSp.l2_zero] at h1
  norm_num at h1

/-- **`BandSharp25 → NormsB`** on Helfgott's own weights. -/
theorem normsB_helf (hb : BandSharp25) : NormsB HW.etaPlus HW.etaStar HW.etaCirc :=
  ⟨l2_circ_lo, l2_circ_hi,
    (l2_diff_of_unif (HW.hH 200) 2.5e-4 (by norm_num) hb).trans (by norm_num), l1_third_le,
    l2_deriv_sq_le, l1_etaStar, l2_etaStar_sq, l1_etaPlus_le,
    l2_plus_of_unif (HW.hH 200) 2.5e-4 (by norm_num) (by norm_num) hb⟩

/-! ## The arithmetic at `1.0486` -/

/-- **Line 1 of `eq:opus111`** at `ε₀ = 2.0832e-4`: at most `7.726e-4·|η*|₁` (the bracket is
`7.725209e-4`). -/
theorem line1_le_band (s lo l3 : ℝ) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40) :
    (2.82643 * lo ^ 2 * (2 + 2.0832e-4) * 2.0832e-4 +
        (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) ≤
      7.726e-4 * (1.2533143 / 49) := by
  have hlo2sq : lo ^ 2 ≤ 0.8002 ^ 2 := pow_le_pow_left₀ (by linarith) hlo2 2
  have hl3sq : l3 ^ 2 ≤ 40 ^ 2 := pow_le_pow_left₀ hl3 hl3' 2
  have hK : 2.82643 * lo ^ 2 * (2 + 2.0832e-4) * 2.0832e-4 +
      (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000 ≤ 7.726e-4 := by
    linarith
  exact mul_le_mul hK (div_le_div_of_nonneg_right hs2 (by norm_num))
    (div_nonneg (by linarith) (by norm_num)) (by norm_num)

/-- **`ternvin.tex` 4772–4865 at the easy constants with `|η₊ − η∘|₂ ≤ 1.6665e-4`**: the
`prop:nefumo` bound at `ε₀ = 2.0832e-4` forces `Re ∫_𝔐 ≥ 1.0486 x²/49`. Net `1.0486096`. -/
theorem arith_close_band (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.31 ≤ C0) (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40)
    (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls) (hls : ls ^ 2 ≤ 2 / 49)
    (hA : A ≤ 10) (hZp : Zp ≤ 0.640209 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hI : ‖I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * lo ^ 2 * (2 + 2.0832e-4) * 2.0832e-4 +
          (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) * x ^ 2 +
        (1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
        (2 * Zp * (24.32 * Real.log x + 0.57) +
          4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x) :
    1.0486 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (main_ge_easy s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (line1_le_band s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (line2_le_easy A lp ls hA hlp hls0 hls) hX
  have h3 := MajSp.line3_le x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-- `ε₀ = 2.0832e-4 ≥ 0`. -/
theorem eps_nonneg_band : (0 : ℝ) ≤ 2.0832e-4 := by norm_num

/-- `|η₊ − η∘|₂ ≤ 1.6665e-4` and `|η∘|₂ ≥ 0.8` give `|η₊ − η∘|₂ < ε₀|η∘|₂` at
`ε₀ = 2.0832e-4` (`2.0832e-4·0.8 = 1.66656e-4`). -/
theorem eps_lt_band (a b : ℝ) (ha : a ≤ 1.6665e-4) (hb : 0.8 ≤ b) : a < 2.0832e-4 * b := by
  linarith

/-! ## The composition at `1.0486` -/

/-- **(7.25) at `1.0486` from the easy links with `NormsB`**: `EN.majorAt_easy` at `ε₀ = 2.0832e-4`.
Application only; the arithmetic is `arith_close_band`. -/
theorem majorAt_band (ηp ηs ηo ηc : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : MajSp.Reg ηp ηs ηo) (nf : MajSp.Nefumo ηp ηs ηo)
    (dj : DrujalE ηp) (cl : CLowerE ηo ηs) (nm : NormsB ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : RT.PlattFull) : RT.MajorLowerAt 1.0486 ηp ηs := by
  intro N hodd hN
  obtain ⟨mp, cp, mh⟩ := hm pf
  obtain ⟨hlo1, hlo2, hdiff, hl3, hld, hl1s, hls, hl1p, hl2p⟩ := nm
  have hx := MajSp.helfX_big N hN
  have hEp := MajSp.eb_plus ηp mp (helfgottX N) hx
  have hEs := MajSp.eb_star ηs ηc sc cp (helfgottX N) hx
  have hET := MajSp.et_plus ηp mp (helfgottX N) hx
  have hT0 := MajSp.et0_star ηs ηc sc cp (helfgottX N) hx
  have hZp := MajSp.zplus ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hZs := MajSp.zstar_holds ηs sn.2.2.1 sn.2.2.2.2 hl1s (helfgottX N) hx hT0
  have hA := dj rg.2.2.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := eps_lt_band _ _ hdiff hlo1
  have hnef := nf rg 2.0832e-4 eps_nonneg_band hlt N (MajSp.N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  exact arith_close_band (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 (RT.c0_131 N hodd) hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _)
    hls hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-- **`RT.helfgottAt_of_smooth` at major `1.0486`**: `(1.0486 − 0.9845)(490/989)²/49 − 13.73/10⁹ =
3.21102·10⁻⁴ ≥ 0.00032`. -/
theorem helfAt_smooth_band (ηp ηs : ℝ → ℝ) (sb : Smooth.SupBounds ηp ηs)
    (mj : RT.MajorLowerAt 1.0486 ηp ηs) (mn : RT.MinorUpperAt 0.9845 ηp ηs) :
    HelfgottAt 0.00032 := by
  have sm := RT.summ_of_majorAt (by norm_num) ηp ηs mj
  have ci := SmCI.circleId_of_summ ηp ηs sm
  refine (RT.helfgottAt_iff 0.00032).mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := RT.weighted_lower_at 1.0486 0.9845 ηp ηs sm ci mj mn H hodd hH
  have hc : (1.0486 - 0.9845 : ℝ) = 0.0641 := by norm_num
  rw [hc] at hW
  have hP := SmPP.pp_crude ηp ηs sb H hodd hH
  have hH0 : (0 : ℝ) ≤ (490 : ℝ) / 989 * H := by positivity
  have hx2 : ((490 : ℝ) / 989 * H) ^ 2 ≤ helfgottX H ^ 2 :=
    pow_le_pow_left₀ hH0 (Smooth.helfX_ge H) 2
  have hx2' : (490 : ℝ) ^ 2 / 989 ^ 2 * (H : ℝ) ^ 2 ≤ helfgottX H ^ 2 :=
    le_of_eq_of_le (by ring) hx2
  have hE := SmPP.ppErr_le H hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **`HelfgottAt 0.00032` on Helfgott's own weights with `BandSharp25` as the only numerical
link**: `NormsB` from `normsB_helf`, `SupN` from `supN_helf`, link 0 from `BL.supBounds_helf`. -/
theorem helfgottAt_band25 (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp25)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  helfAt_smooth_band HW.etaPlus HW.etaStar BL.supBounds_helf
    (majorAt_band HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm RT.starScale_helf
      rg nf dj cl (normsB_helf hb) supN_helf pf) mn

end Principia.Common.TernaryGoldbach.EN
