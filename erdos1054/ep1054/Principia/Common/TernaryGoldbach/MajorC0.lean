/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.DrujalSpine
import Principia.Common.TernaryGoldbach.SingularSeriesP

set_option autoImplicit false

/-!
# The major arcs at `C₀ ≥ 1.3198`: major constant `1.0563699`, minor target `0.9924888`

GENERATED (`scratchpad/c0/gen_mc0.py`) from the verified major composition of
`DrujalSpine.lean` (`DS.arith_close_d100`, `DS.majorAt_d100`, `DS.helfgottAt_d100`), the main-term
bound `EN.main_ge_easy` and the smoothed split `EN.helfAt_smooth_b27`, by counted substitution;
every stale constant is asserted absent. The ONLY change of input is the singular-series floor:
`RT.c0_131` (`C₀ ≥ 1.31`, from `SingularSeries.sing3_ge_sharp`) is replaced by
`SSP.sing3_ge_P` (`C₀ ≥ 1.3198`, the peel to the primes below `1000`). Every link of
the major side is unchanged (`RT.HelfMajFull`, `RW.RegW`, `RW.NefumoW`, `DS.DrujalE100`,
`EN.CLowerE`, `EN.BandSharp27`, `RT.PlattFull`).

## The arithmetic (exact rationals, `gen_mc0.py` asserts them before writing)

* **main term**: `1.3198·(1.2533139·0.8² − 0.000914) = 1.0574…` (was `1.31·… = 1.0496`), so the
  net of `eq:opus111` at `A ≤ 100` rises by `0.0078518` to `1.0563709718…` (units `x²/49`);
* **major constant**: `c_maj = 1.0563699`, the largest 7-decimal value closing with margin
  `≥ 10⁻⁶` (margin `1.0718·10⁻⁶`); was `1.0485`;
* **the split** (`helfAt_smooth_c0`): `(c_maj − c_min)(490/989)²/49 − 13.73·10⁻⁹ ≥ 0.00032` needs
  `c_maj − c_min ≥ 0.0638800305…`; the prime-power term `13.73·10⁻⁹` alone costs `2.74·10⁻⁶` of
  it. At `c_min = 0.9924888`: difference `0.0638811`, `K = 3.2000536·10⁻⁴`
  (margin `1.07·10⁻⁶` in the constant).

`c_min = 0.9924888` is the minor constant the minor arcs must now deliver; the published
minor bound was `0.9845` (`minorAt_c0_of_9845`: the new target is WEAKER by `0.0080`).
-/

namespace Principia.Common.TernaryGoldbach.MC0

open MeasureTheory Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.EN
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## The arithmetic at `C₀ ≥ 1.3198` -/

/-- **The main term at `C₀ ≥ 1.3198`** (generated from `EN.main_ge_easy`):
`C₀·C ≥ 1.3198·(1.2533139·0.8² − 0.000914)/49`. -/
theorem main_ge_c0 (s C0 Cc lo : ℝ) (hs1 : 1.2533139 ≤ s) (hC0 : 1.3198 ≤ C0)
    (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc) (hlo1 : 0.8 ≤ lo) :
    1.3198 * ((1.2533139 * 0.8 ^ 2 - 0.000914) / 49) ≤ C0 * Cc := by
  have hlo2' : 0.8 ^ 2 ≤ lo ^ 2 := pow_le_pow_left₀ (by norm_num) hlo1 2
  have hslo : 1.2533139 * 0.8 ^ 2 ≤ s * lo ^ 2 :=
    mul_le_mul hs1 hlo2' (by norm_num) (by linarith)
  have hCc' : (1.2533139 * 0.8 ^ 2 - 0.000914) / 49 ≤ Cc :=
    le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hCc
  exact mul_le_mul hC0 hCc' (by norm_num) (by linarith)

/-- **The major arithmetic at `C₀ ≥ 1.3198`, `A ≤ 100`** (generated from `DS.arith_close_d100`):
net `1.0563709718… ≥ 1.0563699` (margin `1.07·10⁻⁶`, units `x²/49`). -/
theorem arith_close_c0 (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.3198 ≤ C0) (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40)
    (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls) (hls : ls ^ 2 ≤ 2 / 49)
    (hA : A ≤ 100) (hZp : Zp ≤ 0.640209 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hI : ‖I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * lo ^ 2 * (2 + 2.25e-4) * 2.25e-4 +
          (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) * x ^ 2 +
        (1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
        (2 * Zp * (24.32 * Real.log x + 0.57) +
          4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x) :
    1.0563699 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (main_ge_c0 s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (line1_le_b27 s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (DS.line2_le_d100 A lp ls hA hlp hls0 hls) hX
  have h3 := MajSp.line3_le x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-! ## The composition -/

/-- **(7.25) at `1.0563699`** (generated from `DS.majorAt_d100`; application only): every
link unchanged, the singular-series floor from `SSP.sing3_ge_P`. -/
theorem majorAt_c0 (ηp ηs ηo ηc : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : RW.RegW ηp ηs ηo) (nf : RW.NefumoW ηp ηs ηo)
    (dj : DS.DrujalE100 ηp) (cl : CLowerE ηo ηs) (nm : NormsB27 ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : RT.PlattFull) : RT.MajorLowerAt 1.0563699 ηp ηs := by
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
  have hA := dj rg.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := eps_lt_b27 _ _ hdiff hlo1
  have hnef := nf rg 2.25e-4 eps_nonneg_b27 hlt N (MajSp.N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  have hC0 := SSP.sing3_ge_P N hodd
  exact arith_close_c0 (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 hC0 hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _)
    hls hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-- **THE SPLIT at the new constants** (generated from `EN.helfAt_smooth_b27`): the sup norms, the
major arcs at `1.0563699` and the minor arcs at `0.9924888` give `HelfgottAt 0.00032`;
`(0.0638811)(490/989)²/49 − 13.73·10⁻⁹ = 3.2000536·10⁻⁴ ≥ 0.00032`. -/
theorem helfAt_smooth_c0 (ηp ηs : ℝ → ℝ) (sb : Smooth.SupBounds ηp ηs)
    (mj : RT.MajorLowerAt 1.0563699 ηp ηs) (mn : RT.MinorUpperAt 0.9924888 ηp ηs) :
    HelfgottAt 0.00032 := by
  have sm := RT.summ_of_majorAt (by norm_num) ηp ηs mj
  have ci := SmCI.circleId_of_summ ηp ηs sm
  refine (RT.helfgottAt_iff 0.00032).mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := RT.weighted_lower_at 1.0563699 0.9924888 ηp ηs sm ci mj mn H hodd hH
  have hc : (1.0563699 - 0.9924888 : ℝ) = 0.0638811 := by norm_num
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

/-- **`HelfgottAt 0.00032` on Helfgott's weights with the major arcs at `C₀ ≥ 1.3198`** (generated
from `DS.helfgottAt_d100`): the minor side is the single hypothesis
`RT.MinorUpperAt 0.9924888 η₊ η*`. -/
theorem helfgottAt_c0 (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : RW.RegW HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc) (dj : DS.DrujalE100 HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp27)
    (mn : RT.MinorUpperAt 0.9924888 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  helfAt_smooth_c0 HW.etaPlus HW.etaStar BL.supBounds_helf
    (majorAt_c0 HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm RT.starScale_helf
      rg nf dj cl (normsB27_helf hb) supN_helf pf) mn

/-- **The new minor target is WEAKER than the old one**: `RT.MinorUpperAt 0.9845` (what
`DS.minorAt_mnum_d` and every earlier minor chain deliver) implies
`RT.MinorUpperAt 0.9924888`. -/
theorem minorAt_c0_of_9845 (ηp ηs : ℝ → ℝ) (h : RT.MinorUpperAt 0.9845 ηp ηs) :
    RT.MinorUpperAt 0.9924888 ηp ηs :=
  RT.minorUpper_le (by norm_num) ηp ηs h

end Principia.Common.TernaryGoldbach.MC0
