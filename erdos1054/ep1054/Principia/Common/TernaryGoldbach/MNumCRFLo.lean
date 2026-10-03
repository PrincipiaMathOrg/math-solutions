/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCData

set_option autoImplicit false

/-!
# Region `RF` of `g̃`, `w ≤ 1`: `r ∈ [5940000, r₁(y)]`, `y ≥ (10 ^ 27)`

GENERATED. The first piece `[w₁, 0.04]` and 8 pieces on the grid `0.04, 0.09, 0.16, 0.25, 0.36,
    0.49, 0.64, 0.81, 1` of the `w ≤ 1` integral of `gT`, each a certified majorant `(P(w, ℓ)/√r +
    Q(w, ℓ)/r + Y(w))e^{−w²/2}` integrated against the moments of `MNumCData`; their sum is `loRF`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **The first piece `[w₁, 0.04]` of region `RF`** (`ptFirstS`, `intBnd_lin`). -/
private theorem tRF_first (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 0.04
      (1 / Real.sqrt r * (0.000002537594678823862 + Real.log r * 0.0001480233408179809 +
          Real.log r ^ 2 * 0.00000275333842390176 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r
          * ((-0.005091521208) + Real.log r * 0.01563247936 + Real.log r ^ 2 * 0.0004155901608) +
          0.00256 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  obtain ⟨-, hm0, hm1⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  have key : ∀ w ∈ Set.Icc (max (1 / kK y) (1000 / r)) 0.04, OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * 0.2 * (((0.72) * ((-2.52572864) + Real.log r) + 0.5) * (1.87904775 + 0.0338002675 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.36440151) + 19.5405992 * Real.log r +
      0.519487701 * Real.log r ^ 2) * (1 / r) + 3.2 * (1 * y ^ (-(1 : ℝ) / 6))) * w ∧ 0 ≤ (0.70711 *
      0.2 * (((0.72) * ((-2.52572864) + Real.log r) + 0.5) * (1.87904775 + 0.0338002675 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.36440151) + 19.5405992 * Real.log r +
      0.519487701 * Real.log r ^ 2) * (1 / r) + 3.2 * (1 * y ^ (-(1 : ℝ) / 6))) := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) ((le_max_right _ _).trans hw.1)
    have hwr1 := wr_ge y r w hr hw.1
    have hw1 : w ≤ 1 := le_trans hw.2 (by norm_num)
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hτ : Real.log w ≤ (-3.21887582356) + 0 * w := by
      have := Real.log_le_log hw0 hw.2
      linarith [lgU11]
    have hR := rFarLo y r w (le_trans (by norm_num) hy) hr hw0 hw1 (by linarith) hr1
    have hRb := hR.2
    have hsp : Real.sqrt w ≤ 0.2 := MN.sqrt_le_of w 0.2 (by norm_num) (le_trans hw.2 (by norm_num))
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-2.52572864) + Real.log r := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-3.21887582356) := by
      rw [hwl]
      linarith
    have hLlo : 6.907 ≤ Real.log (w * r) :=
      le_trans (by norm_num) (lgL13.trans (Real.log_le_log (by norm_num) hwr1))
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 6.907 1.93253538928 0.089745 2.41078296431
        (Real.log r + (-3.21887582356)) 1.7810727 1.2969336 0.21146 1.18226 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL14 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL360]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.87904775 + 0.0338002675 * Real.log r := hS.trans
        (by linarith)
    have hLs : lL (w * r) ≤ (-6.36440151) + 19.5405992 * Real.log r + 0.519487701 * Real.log r ^ 2
        := by
      refine hLL.trans (le_of_sub_eq _ _ (0.0000000015292749909515514973854002 + (18802662221476459
          / 900000000000000000000000) * Real.log r + 0.000000000250125 *
          Real.log r ^ 2) (by ring) ?_)
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ (1 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_w_le w y y hw0 hw1 hy0 le_rfl).trans (le_of_eq (by ring))
    exact ptFirstS y r w 0.2 _ _ _ _ _ hy0 hr hw0 hsp hR.1 hRb hL0 hL hSs hLL0 hLs hY
  have hC0 := (key 0.04 ⟨hm1, le_rfl⟩).2
  refine intBnd_mono _ _ _ _ _ (intBnd_lin _ _ 0.04 _ hm0 hm1 hC0 (fun w hw => (key w hw).1)) ?_
  have e : (0.70711 * 0.2 * (((0.72) * ((-2.52572864) + Real.log r) + 0.5) * (1.87904775 +
      0.0338002675 * Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.36440151) + 19.5405992 *
      Real.log r + 0.519487701 * Real.log r ^ 2) * (1 / r) + 3.2 * (1 * y ^ (-(1 : ℝ) / 6))) *
      (0.04 ^ 2 / 2) = 1 / Real.sqrt r * (0.00000253759467882386157568 + Real.log r *
      0.0001480233408179808642215936 + Real.log r ^ 2 * 0.00000275333842390176 + Real.log r ^ 3 * 0
      + Real.log r ^ 4 * 0) + 1 / r * ((-0.005091521208) + Real.log r * 0.01563247936 +
      Real.log r ^ 2 * 0.0004155901608) + 0.00256 * y ^ (-(1 : ℝ) / 6) := by
    ring
  refine le_trans (le_of_eq e) ?_
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.04, 0.09]` of region `RF`** (`ptLoS`; moments `mom_0_04_0_09`). -/
private theorem tRF_lo0 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.04 0.09
      (1 / Real.sqrt r * (0.0005028766024007063 + Real.log r * 0.0009301916025265903 +
          Real.log r ^ 2 * 0.0000125635849836062 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r
          * (0.01504600841002513 + Real.log r * 0.06754402718069421 + Real.log r ^ 2 *
          0.001310782750882314) + 0.001209775375149458 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.04 : ℝ) 0.09, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, -7.015196392392646622941875, 420.6192000481632577103373,
          -11445.728622569112494048133766624, 201331.97163569454080232998289854976,
          -1940916.995956493604090004960838912, 7734901.899583038512195372312334336,
          1807552.8659175842816557056]
        [0, 0, 11.673707518858856475767175, -383.9178317160391225255725,
          8581.75556902365214226644038935936, -100325.216994645134539429793532032,
          460191.403393239989351743569520896, 225944.1082396980352069632]
        [0, 0, 0.16267975768508625, -5.422658589502875, 122.009818329919477924416,
          -1452.4978331687448537792, 7060.7533824905636002176]
        [0]
        [0]
        [0, -17.6289802, 319.215905, 103.499987]
        [0, 19.9509941, 12.9374984]
        [0, 0.404296824]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 5.471936 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, -7.015196392392646622941875, 420.6192000481632577103373,
          -11445.728622569112494048133766624, 201331.97163569454080232998289854976,
          -1940916.995956493604090004960838912, 7734901.899583038512195372312334336,
          1807552.8659175842816557056]
        [0, 0, 11.673707518858856475767175, -383.9178317160391225255725,
          8581.75556902365214226644038935936, -100325.216994645134539429793532032,
          460191.403393239989351743569520896, 225944.1082396980352069632]
        [0, 0, 0.16267975768508625, -5.422658589502875, 122.009818329919477924416,
          -1452.4978331687448537792, 7060.7533824905636002176]
        [0]
        [0]
        [0, -17.6289802, 319.215905, 103.499987]
        [0, 19.9509941, 12.9374984]
        [0, 0.404296824]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 5.471936 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.04 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.0625 (-2.7725887212) hw0 (by norm_num) lgU172
    have hτ1 : w / 0.0625 ≤ 16 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.7725887212) + 16 * w := by linarith
    have hwa : Real.log 0.04 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 12.3046875 + (-410.15625) * w + 9228.51563 * w ^ 2 + (-109863.281) *
        w ^ 3 + 534057.618 * w ^ 4 := by
      refine (isq_le 0.2 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0.000005 * w ^ 2 + 0.00025 * w ^ 3 + 0.0008125 * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-3.07944154) + Real.log r + 16 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-3.7725887212) + 16 * w := by
      rw [hwl]
      linarith
    have hLlo : 12.37 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL20]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.37 2.51527418536 0.069845 2.66147677879
        (Real.log r + (-3.7725887212) + 16 * w) 1.7810727 0.99645996 0.20875 1.19761 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL361 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL363]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.9253886 + 0.025968296 * Real.log r + 0.415492736 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-17.6289802) + 19.9509941 * Real.log r + 319.215905 * w + 0.404296824 *
        Real.log r ^ 2 + 12.9374984 * w * Real.log r + 103.499987 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((228905236477131904547863 /
          6000000000000000000000000000000) + (3567130091576869 / 90000000000000000000000) *
          Real.log r + (192130091576869 / 5625000000000000000000) * w + 0.000000000122625 *
          Real.log r ^ 2 + 0.000000035924 * w * Real.log r + 0.000000087392 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.70998 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.04 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.70998 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_04_0_09
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.09, 0.16]` of region `RF`** (`ptLoS`; moments `mom_0_09_0_16`). -/
private theorem tRF_lo1 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.09 0.16
      (1 / Real.sqrt r * (0.003480018322331001 + Real.log r * 0.003145514744158856 + Real.log r ^ 2
          * 0.00003938381775562305 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (0.1572317208774754 + Real.log r * 0.1869505716122458 + Real.log r ^ 2 *
          0.003350073781106378) + 0.005317891831982074 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.09 : ℝ) 0.16, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 0.4819707563497620244723125, 58.26507030187941073087655954256,
          -890.697884048746645484518218130752, 9210.14943153632107271520274505248,
          -49434.5346819061087304358428151744, 105381.4005638145156346239144811968,
          11630.33077249558219108747090752]
        [0, 0, 8.012158094083386144867223125, -117.0160772888505196481340520977744,
          1162.059566159512700707578184661056, -6031.08303227023608187768839514488,
          12249.78077610002353956614252497296, 2849.430798646121117961579974544]
        [0, 0, 0.10305681471606346875, -1.52676761565184969729176, 15.2676762821496615791664,
          -80.781355814060333113812, 174.527621679389251139784]
        [0]
        [0]
        [0, -4.01788179, 169.291736, 25.7295246]
        [0, 20.7382359, 6.30373297]
        [0, 0.386103612]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 4.780192 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 0.4819707563497620244723125, 58.26507030187941073087655954256,
          -890.697884048746645484518218130752, 9210.14943153632107271520274505248,
          -49434.5346819061087304358428151744, 105381.4005638145156346239144811968,
          11630.33077249558219108747090752]
        [0, 0, 8.012158094083386144867223125, -117.0160772888505196481340520977744,
          1162.059566159512700707578184661056, -6031.08303227023608187768839514488,
          12249.78077610002353956614252497296, 2849.430798646121117961579974544]
        [0, 0, 0.10305681471606346875, -1.52676761565184969729176, 15.2676762821496615791664,
          -80.781355814060333113812, 174.527621679389251139784]
        [0]
        [0]
        [0, -4.01788179, 169.291736, 25.7295246]
        [0, 20.7382359, 6.30373297]
        [0, 0.386103612]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 4.780192 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.09 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.1225 (-2.09964424815) hw0 (by norm_num) lgU178
    have hτ1 : w / 0.1225 ≤ 8.163266 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.09964424815) + 8.163266 * w := by linarith
    have hwa : Real.log 0.09 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 8.203125 + (-121.527777) * w + 1215.27778 * w ^ 2 + (-6430.04115) *
        w ^ 3 + 13892.0643 * w ^ 4 := by
      refine (isq_le 0.3 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((7 / 9000000) * w + (1 / 450000) * w ^ 2 + (11 / 4860000) * w ^ 3 +
          (16169 / 196830000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-2.40649706) + Real.log r + 8.163266 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-3.09964424815) + 8.163266 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.18 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL36]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.18 2.57870052803 0.066702 2.70752034249
        (Real.log r + (-3.09964424815) + 8.163266 * w) 1.7810727 0.97195079 0.20771 1.20361
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL364 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL366]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.96069789 + 0.0246761789 * Real.log r + 0.201438212 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-4.01788179) + 20.7382359 * Real.log r + 169.291736 * w + 0.386103612 *
        Real.log r ^ 2 + 6.30373297 * w * Real.log r + 25.7295246 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((126295449146191692927060787 /
          72000000000000000000000000000000000) + (53273361985469759 / 1800000000000000000000000) *
          Real.log r + (197237852300838888836447 / 900000000000000000000000000000) * w +
          0.00000000048495 * Real.log r ^ 2 + 0.0000000012839676934 * w * Real.log r +
          0.0000000917006749083153222 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.49381 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.09 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.49381 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_09_0_16
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.16, 0.25]` of region `RF`** (`ptLoS`; moments `mom_0_16_0_25`). -/
private theorem tRF_lo2 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.16 0.25
      (1 / Real.sqrt r * (0.01310420188745725 + Real.log r * 0.008414463753718542 + Real.log r ^ 2 *
          0.00009974957951046872 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (0.5212294265785283 + Real.log r * 0.3981558480746935 + Real.log r ^ 2 *
          0.006741300344053949) + 0.01631632595194709 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.16 : ℝ) 0.25, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.353575676977612704683953125, 2.323721298675998544816032206618,
          -93.23600650405278106306078370304, 935.92221515351959891976070507736,
          -3569.2321175861185814938017177512, 4878.628204369501470381724571606,
          308.0031890289772733468186688]
        [0, 0, 6.12971202211766489436536953125, -50.3451794562549790123682075871616,
          281.198968329049741389935316826672, -820.661086515644622999701324057312,
          936.60000553326883430085803833912, 124.741281486024228316916733696]
        [0, 0, 0.074495087657889609375, -0.62079239654365968319104, 3.4919572426664936166288,
          -10.3927298537163318676128, 12.630053730800489232168]
        [0]
        [0]
        [0, 6.59159442, 105.148834, 9.10870206]
        [0, 21.292637, 3.68902404]
        [0, 0.373513654]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 4.343072 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.353575676977612704683953125, 2.323721298675998544816032206618,
          -93.23600650405278106306078370304, 935.92221515351959891976070507736,
          -3569.2321175861185814938017177512, 4878.628204369501470381724571606,
          308.0031890289772733468186688]
        [0, 0, 6.12971202211766489436536953125, -50.3451794562549790123682075871616,
          281.198968329049741389935316826672, -820.661086515644622999701324057312,
          936.60000553326883430085803833912, 124.741281486024228316916733696]
        [0, 0, 0.074495087657889609375, -0.62079239654365968319104, 3.4919572426664936166288,
          -10.3927298537163318676128, 12.630053730800489232168]
        [0]
        [0]
        [0, 6.59159442, 105.148834, 9.10870206]
        [0, 21.292637, 3.68902404]
        [0, 0.373513654]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 4.343072 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.16 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.2025 (-1.59701539181) hw0 (by norm_num) lgU184
    have hτ1 : w / 0.2025 ≤ 4.938272 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.59701539181) + 4.938272 * w := by linarith
    have hwa : Real.log 0.16 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 6.15234375 + (-51.2695312) * w + 288.391114 * w ^ 2 + (-858.306884)
        * w ^ 3 + 1043.08129 * w ^ 4 := by
      refine (isq_le 0.4 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0.00000005 * w + 0.00000071875 * w ^ 2 + 0.000000765625 * w ^ 3 +
          0.0000064306640625 * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.90386821) + Real.log r + 4.938272 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.59701539181) + 4.938272 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.76 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL52]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.76 2.62176583146 0.064527 2.74067153912
        (Real.log r + (-2.59701539181) + 4.938272 * w) 1.7810727 0.95598546 0.20694 1.20808
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL367 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL369]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.98571502 + 0.023783051 * Real.log r + 0.117447175 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 6.59159442 + 21.292637 * Real.log r + 105.148834 * w + 0.373513654 *
        Real.log r ^ 2 + 3.68902404 * w * Real.log r + 9.10870206 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((24392986806220913241034692187 /
          3600000000000000000000000000000000000) + (99618383171057753 / 18000000000000000000000000)
          * Real.log r + (519787208509340803500713 / 562500000000000000000000000000) * w +
          0.000000000133075 * Real.log r ^ 2 + 0.0000000029825450928 * w * Real.log r +
          0.0000000053348694602558208 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.35721 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.16 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.35721 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_16_0_25
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.25, 0.36]` of region `RF`** (`ptLoS`; moments `mom_0_25_0_36`). -/
private theorem tRF_lo3 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.25 0.36
      (1 / Real.sqrt r * (0.03530424423210578 + Real.log r * 0.01836214935286378 + Real.log r ^ 2 *
          0.0002086964940783975 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (1.209095561373734 + Real.log r * 0.7181401701407364 + Real.log r ^ 2 *
          0.01164114229874885) + 0.0397103391099795 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.25 : ℝ) 0.36, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 4.641071973565971614266575, -8.29927666011887430966780375,
          1.991582944259823536322435, 142.793526775592791613311848, -457.54912342609795527623312,
          444.85321296853822372619296, 18.002662758151216260192]
        [0, 0, 4.977063608690184238204810875, -26.1614311494751742594200455,
          93.5174447701983373148357688, -174.666490800718074785896752,
          127.566313199660757611207776, 10.8916080888170669797152]
        [0, 0, 0.05791483433862433125, -0.3088791164726631, 1.11196481930158716,
          -2.1180282272411184, 1.6473552878542032]
        [0]
        [0]
        [0, 15.3178214, 71.7877175, 3.97822342]
        [0, 21.7157788, 2.40682453]
        [0, 0.364032114]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 4.031776 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 4.641071973565971614266575, -8.29927666011887430966780375,
          1.991582944259823536322435, 142.793526775592791613311848, -457.54912342609795527623312,
          444.85321296853822372619296, 18.002662758151216260192]
        [0, 0, 4.977063608690184238204810875, -26.1614311494751742594200455,
          93.5174447701983373148357688, -174.666490800718074785896752,
          127.566313199660757611207776, 10.8916080888170669797152]
        [0, 0, 0.05791483433862433125, -0.3088791164726631, 1.11196481930158716,
          -2.1180282272411184, 1.6473552878542032]
        [0]
        [0]
        [0, 15.3178214, 71.7877175, 3.97822342]
        [0, 21.7157788, 2.40682453]
        [0, 0.364032114]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 4.031776 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.25 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.3025 (-1.19567400084) hw0 (by norm_num) lgU190
    have hτ1 : w / 0.3025 ≤ 3.305786 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.19567400084) + 3.305786 * w := by linarith
    have hwa : Real.log 0.25 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 4.921875 + (-26.25) * w + 94.5 * w ^ 2 + (-180) * w ^ 3 + 140 * w ^
        4 := by
      refine (isq_le 0.5 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.50252682) + Real.log r + 3.305786 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.19567400084) + 3.305786 * w := by
      rw [hwl]
      linarith
    have hLlo : 14.21 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL68]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.21 2.65394594106 0.062889 2.76638401231
        (Real.log r + (-2.19567400084) + 3.305786 * w) 1.7810727 0.94439377 0.20634 1.2116
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL370 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL372]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 2.00487722 + 0.0231121189 * Real.log r + 0.076403719 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 15.3178214 + 21.7157788 * Real.log r + 71.7877175 * w + 0.364032114 *
        Real.log r ^ 2 + 2.40682453 * w * Real.log r + 3.97822342 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((8609751050525108373730448989 /
          225000000000000000000000000000000000) + (91521451273160831 / 4500000000000000000000000) *
          Real.log r + (69967366159248625434083 / 2250000000000000000000000000000) * w +
          0.000000000651525 * Real.log r ^ 2 + 0.0000000022843964473 * w * Real.log r +
          0.0000000059105728969670389 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.25993 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.25 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.25993 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_25_0_36
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.36, 0.49]` of region `RF`** (`ptLoS`; moments `mom_0_36_0_49`). -/
private theorem tRF_lo4 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.36 0.49
      (1 / Real.sqrt r * (0.07677868931360791 + Real.log r * 0.03445380489335113 + Real.log r ^ 2 *
          0.0003785997637214523 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (2.289185095946554 + Real.log r * 1.14744962936801 + Real.log r ^ 2 * 0.01796477458089696)
          + 0.08175381817067493 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.36 : ℝ) 0.49, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.2511484746561880004284375, -9.51683755993352257149967623627,
          12.1012914763347069213990451748472, 26.6686207249292134252406333582824,
          -84.45823212923621717218060380145, 62.465904857526554665999214566472,
          1.74785071811061987517055079168]
        [0, 0, 4.19621087898832379610763125, -15.3182604044990559206528958083904,
          38.0269106047317638698942357741632, -49.32668651333258689536913233,
          25.024625034483777537025580632896, 1.47693379789595549380096410624]
        [0, 0, 0.047163957629677875, -0.174681324298828676651904, 0.436703311896973896696192,
          -0.57764988276192973857888, 0.31200225236130785337216]
        [0]
        [0]
        [0, 22.7443863, 52.199862, 1.9976552]
        [0, 22.0544409, 1.68801857]
        [0, 0.356593909]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.794048 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.2511484746561880004284375, -9.51683755993352257149967623627,
          12.1012914763347069213990451748472, 26.6686207249292134252406333582824,
          -84.45823212923621717218060380145, 62.465904857526554665999214566472,
          1.74785071811061987517055079168]
        [0, 0, 4.19621087898832379610763125, -15.3182604044990559206528958083904,
          38.0269106047317638698942357741632, -49.32668651333258689536913233,
          25.024625034483777537025580632896, 1.47693379789595549380096410624]
        [0, 0, 0.047163957629677875, -0.174681324298828676651904, 0.436703311896973896696192,
          -0.57764988276192973857888, 0.31200225236130785337216]
        [0]
        [0]
        [0, 22.7443863, 52.199862, 1.9976552]
        [0, 22.0544409, 1.68801857]
        [0, 0.356593909]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.794048 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.36 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.4225 (-0.861565831581) hw0 (by norm_num) lgU196
    have hτ1 : w / 0.4225 ≤ 2.366864 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.861565831581) + 2.366864 * w := by linarith
    have hwa : Real.log 0.36 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 4.1015625 + (-15.1909722) * w + 37.9774306 * w ^ 2 + (-50.2346965) *
        w ^ 3 + 27.132938 * w ^ 4 := by
      refine (isq_le 0.6 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((1 / 45000000) * w + (1 / 22500000) * w ^ 2 + (1 / 486000000) * w ^ 3
          + (2933 / 39366000000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.16841865) + Real.log r + 2.366864 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.861565831581) + 2.366864 * w := by
      rw [hwl]
      linarith
    have hLlo : 14.57 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL84]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.57 2.67896461916 0.061604 2.78702847646
        (Real.log r + (-1.861565831581) + 2.366864 * w) 1.7810727 0.93557414 0.20585 1.21448
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL373 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL375]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 2.02020748 + 0.0225861096 * Real.log r + 0.0534582497 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 22.7443863 + 22.0544409 * Real.log r + 52.199862 * w + 0.356593909 *
        Real.log r ^ 2 + 1.68801857 * w * Real.log r + 1.9976552 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((8462209293696035932117931211101 /
          90000000000000000000000000000000000000) + (4092108048471744479 /
          45000000000000000000000000) * Real.log r + (25016951502376689033991 /
          2812500000000000000000000000000) * w + 0.0000000005149 * Real.log r ^ 2 +
          0.0000000007746445472 * w * Real.log r + 0.0000000085844991457819904 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.18564 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.36 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.18564 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_36_0_49
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.49, 0.64]` of region `RF`** (`ptLoS`; moments `mom_0_49_0_64`). -/
private theorem tRF_lo5 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.49 0.64
      (1 / Real.sqrt r * (0.1426483042914808 + Real.log r * 0.05726809526886303 + Real.log r ^ 2 *
          0.0006116600977601426 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (3.754920612006109 + Real.log r * 1.660638289199595 + Real.log r ^ 2 *
          0.02525146601816983) + 0.1473324399372682 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.49 : ℝ) 0.64, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.531555296815012494239809375, -8.59599183691234942078593971826504,
          10.204582742024462544940566646050696, 5.05781769706967624273114719834872,
          -20.0687747939052231565807604492916, 11.834521829422674068906680089881088,
          0.241483775575040328396295337472]
        [0, 0, 3.6314204079173900850488503125, -9.740465369724127749245446012399656,
          17.76600046691084725536233210428728, -16.93357665233798489796386073903672,
          6.314614489019098968199753781970432, 0.271669213293541820858862033408]
        [0, 0, 0.0396423809579165625, -0.107870424368379456105288, 0.19812935166311710499544,
          -0.19254553040083304888856, 0.076406956612078383150336]
        [0]
        [0]
        [0, 29.2198605, 39.7095687, 1.10741975]
        [0, 22.3366296, 1.24584706]
        [0, 0.35039444]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.604 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.531555296815012494239809375, -8.59599183691234942078593971826504,
          10.204582742024462544940566646050696, 5.05781769706967624273114719834872,
          -20.0687747939052231565807604492916, 11.834521829422674068906680089881088,
          0.241483775575040328396295337472]
        [0, 0, 3.6314204079173900850488503125, -9.740465369724127749245446012399656,
          17.76600046691084725536233210428728, -16.93357665233798489796386073903672,
          6.314614489019098968199753781970432, 0.271669213293541820858862033408]
        [0, 0, 0.0396423809579165625, -0.107870424368379456105288, 0.19812935166311710499544,
          -0.19254553040083304888856, 0.076406956612078383150336]
        [0]
        [0]
        [0, 29.2198605, 39.7095687, 1.10741975]
        [0, 22.3366296, 1.24584706]
        [0, 0.35039444]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.604 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.49 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.5625 (-0.575364144352) hw0 (by norm_num) lgU202
    have hτ1 : w / 0.5625 ≤ 1.777778 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.575364144352) + 1.777778 * w := by linarith
    have hwa : Real.log 0.49 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 3.515625 + (-9.56632653) * w + 17.5708039 * w ^ 2 + (-17.0756111) *
        w ^ 3 + 6.77603616 * w ^ 4 := by
      refine (isq_le 0.7 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((3 / 4900000000) * w + (1639 / 24010000000) * w ^ 2 + (78727 /
          8235430000000) * w ^ 3 + (97513 / 18015003125000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-0.882216963) + Real.log r + 1.777778 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.575364144352) + 1.777778 * w := by
      rw [hwl]
      linarith
    have hLlo : 14.88 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL100]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.88 2.70001802836 0.060533 2.80456660911
        (Real.log r + (-1.575364144352) + 1.777778 * w) 1.7810727 0.92827899 0.20543 1.21696
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL376 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL378]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 2.03303017 + 0.022148163 * Real.log r + 0.039374517 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 29.2198605 + 22.3366296 * Real.log r + 39.7095687 * w + 0.35039444 *
        Real.log r ^ 2 + 1.24584706 * w * Real.log r + 1.10741975 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((32368370118854823330464716613 /
          351562500000000000000000000000000000) + (276163076583561067 / 5625000000000000000000000) *
          Real.log r + (253834820981285013284563 / 2812500000000000000000000000000) * w +
          0.000000000315425 * Real.log r ^ 2 + 0.0000000076128712513 * w * Real.log r +
          0.0000000094506575136968057 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.12625 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.49 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.12625 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_49_0_64
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.64, 0.81]` of region `RF`** (`ptLoS`; moments `mom_0_64_0_81`). -/
private theorem tRF_lo6 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.64 0.81
      (1 / Real.sqrt r * (0.2329366179706894 + Real.log r * 0.08562110984492277 + Real.log r ^ 2 *
          0.000892475915186368 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (5.482078989083751 + Real.log r * 2.198760673532326 + Real.log r ^ 2 *
          0.03260926309678483) + 0.2366425379827542 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.64 : ℝ) 0.81, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.63822419630093899864033234882144, -7.3126768228102802314339054048455264,
          7.346856325075545971555927004795792, 0.562659192759093458439597382460616,
          -5.7390667153607836569164367935874216, 2.7938492877443114804990780925620208,
          0.0432710518668328727310681497664]
        [0, 0, 3.2032908086541747954807946057399424, -6.579110455714543979840216770935872,
          9.187949276276864546466450258523104, -6.7060220154535246399206399742384544,
          1.9156537550320741734663913276558272, 0.0625266268373868219984494290176]
        [0, 0, 0.0341063277263880198473088, -0.071054849245187318940864,
          0.099920881958930854969248, -0.0743458941523314824034528, 0.0225877283714617890963264]
        [0]
        [0]
        [0, 34.9662827, 31.2488342, 0.661166762]
        [0, 22.5772671, 0.955385312]
        [0, 0.345132706]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.447104 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.63822419630093899864033234882144, -7.3126768228102802314339054048455264,
          7.346856325075545971555927004795792, 0.562659192759093458439597382460616,
          -5.7390667153607836569164367935874216, 2.7938492877443114804990780925620208,
          0.0432710518668328727310681497664]
        [0, 0, 3.2032908086541747954807946057399424, -6.579110455714543979840216770935872,
          9.187949276276864546466450258523104, -6.7060220154535246399206399742384544,
          1.9156537550320741734663913276558272, 0.0625266268373868219984494290176]
        [0, 0, 0.0341063277263880198473088, -0.071054849245187318940864,
          0.099920881958930854969248, -0.0743458941523314824034528, 0.0225877283714617890963264]
        [0]
        [0]
        [0, 34.9662827, 31.2488342, 0.661166762]
        [0, 22.5772671, 0.955385312]
        [0, 0.345132706]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.447104 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.64 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.7225 (-0.325037858537) hw0 (by norm_num) lgU208
    have hτ1 : w / 0.7225 ≤ 1.384084 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.325037858537) + 1.384084 * w := by linarith
    have hwa : Real.log 0.64 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 3.07617188 + (-6.4086914) * w + 9.0122223 * w ^ 2 + (-6.70552253) *
        w ^ 3 + 2.03726814 * w ^ 4 := by
      refine (isq_le 0.8 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0.000000005 + 0.00000000625 * w + 0.0000000099609375 * w ^ 2 +
          0.0000000072314453125 * w ^ 3 + 0.0000000080286407470703125 * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-0.631890677) + Real.log r + 1.384084 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.325037858537) + 1.384084 * w := by
      rw [hwl]
      linarith
    have hLlo : 15.15 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL116]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 15.15 2.71800053091 0.059624 2.8196971024
        (Real.log r + (-1.325037858537) + 1.384084 * w) 1.7810727 0.92213743 0.20507 1.2191
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL379 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL381]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 2.04398143 + 0.0217773428 * Real.log r + 0.0301416717 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 34.9662827 + 22.5772671 * Real.log r + 31.2488342 * w + 0.345132706 *
        Real.log r ^ 2 + 0.955385312 * w * Real.log r + 0.661166762 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((1708159686533967540132400474537 /
          45000000000000000000000000000000000000) + (363963603576843199 /
          22500000000000000000000000) * Real.log r + (368734300073262860561179 /
          5625000000000000000000000000000) * w + 0.0000000003394 * Real.log r ^ 2 +
          0.0000000004369082192 * w * Real.log r + 0.0000000002152548378316064 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.07722 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.64 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.07722 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_64_0_81
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.81, 1]` of region `RF`** (`ptLoS`; moments `mom_0_81_1`). -/
private theorem tRF_lo7 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.81 1
      (1 / Real.sqrt r * (0.3389086022686464 + Real.log r * 0.1158803487716253 + Real.log r ^ 2 *
          0.001182840735218139 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (7.208075030271155 + Real.log r * 2.670719365818707 + Real.log r ^ 2 *
          0.03876697538815213) + 0.3415648213757315 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.81 : ℝ) 1, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.64848565327865241865868125, -6.1210161953050155146333910085716,
          5.138235833464434932801621728017024, -0.3233625869697515443346850641106816,
          -1.8908764669190072534568025514095752, 0.78056962394601068308171538849992056,
          0.00946883422764099324601596934128]
        [0, 0, 2.8671525981595730050559704375, -4.653377804634907952986587784415488,
          5.1349961605462923090730427416234112, -2.9617812481791906855466577040859216,
          0.66886500404872164018315489774733808, 0.01709123409751367119906918132704]
        [0, 0, 0.0298794724379274375, -0.049184316698301296822016, 0.0546492408730223290925184,
          -0.0321277136001135466661712, 0.00771241411438218045014256]
        [0]
        [0]
        [0, 40.1335414, 25.2472241, 0.418253696]
        [0, 22.7856041, 0.754947405]
        [0, 0.340669783]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.3144 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.64848565327865241865868125, -6.1210161953050155146333910085716,
          5.138235833464434932801621728017024, -0.3233625869697515443346850641106816,
          -1.8908764669190072534568025514095752, 0.78056962394601068308171538849992056,
          0.00946883422764099324601596934128]
        [0, 0, 2.8671525981595730050559704375, -4.653377804634907952986587784415488,
          5.1349961605462923090730427416234112, -2.9617812481791906855466577040859216,
          0.66886500404872164018315489774733808, 0.01709123409751367119906918132704]
        [0, 0, 0.0298794724379274375, -0.049184316698301296822016, 0.0546492408730223290925184,
          -0.0321277136001135466661712, 0.00771241411438218045014256]
        [0]
        [0]
        [0, 40.1335414, 25.2472241, 0.418253696]
        [0, 22.7856041, 0.754947405]
        [0, 0.340669783]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.3144 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.81 : ℝ) * 5940000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.9025 (-0.102586588552) hw0 (by norm_num) lgU214
    have hτ1 : w / 0.9025 ≤ 1.108034 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.102586588552) + 1.108034 * w := by linarith
    have hwa : Real.log 0.81 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rFarLo y r w (by linarith) hr hw0 (le_trans hw.2 (by norm_num)) (by linarith) hr1
    have hRb := hR.2
    have hq : 1 / Real.sqrt w ≤ 2.734375 + (-4.5010288) * w + 5.00114312 * w ^ 2 + (-2.94011941) * w
        ^ 3 + 0.705789983 * w ^ 4 := by
      refine (isq_le 0.9 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((1 / 151875000) * w + (43 / 27337500000) * w ^ 2 + (63019 /
          53144100000000) * w ^ 3 + (345161687 / 387420489000000000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-0.409439407) + Real.log r + 1.108034 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.102586588552) + 1.108034 * w := by
      rw [hwl]
      linarith
    have hLlo : 15.38 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL132]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 15.38 2.73306796303 0.058853 2.83271247049
        (Real.log r + (-1.102586588552) + 1.108034 * w) 1.7810727 0.91705367 0.20476 1.22095
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL382 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL384]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 2.05343722 + 0.0214632446 * Real.log r + 0.0237820047 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 40.1335414 + 22.7856041 * Real.log r + 25.2472241 * w + 0.340669783 *
        Real.log r ^ 2 + 0.754947405 * w * Real.log r + 0.418253696 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((15120226808694594636524378353 /
          5625000000000000000000000000000000000) + (377676840367138663 / 22500000000000000000000000)
          * Real.log r + (734171140069681060659271 / 11250000000000000000000000000000) * w +
          0.000000000257425 * Real.log r ^ 2 + 0.0000000008972273049 * w * Real.log r +
          0.0000000000211941797787833 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1.03575 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 0.81 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1.03575 hy0 (by norm_num)))
    have hp := ptLoS y r w _ _ _ _ _ _ hr hw0 hq hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h, j4l, j4h, j5l, j5h, j6l, j6h, j7l, j7h, j8l, j8h,
      j9l, j9h, j10l, j10h⟩ := mom_0_81_1
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    nlinarith

/-- **Region `RF`, `w ≤ 1`**: the first piece and the 8 lo pieces, added. -/
theorem loRF (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 1
      (1 / Real.sqrt r * (0.843666092483398071162 + Real.log r * 0.3242237015728479792 +
          Real.log r ^ 2 * 0.00342872332663809913 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r
          * (20.63177092333933183 + Real.log r * 9.06399105428700791 + Real.log r ^ 2 *
          0.138051368419595241) + 0.872407949735486952 * y ^ (-(1 : ℝ) / 6)) := by
  have h0 := tRF_first y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tRF_lo0 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tRF_lo1 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tRF_lo2 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tRF_lo3 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tRF_lo4 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tRF_lo5 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tRF_lo6 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tRF_lo7 y r hy hr0 hr1)
  exact intBnd_mono _ _ _ _ _ h8 (le_of_eq (by ring))

end Principia.Common.TernaryGoldbach.MC
