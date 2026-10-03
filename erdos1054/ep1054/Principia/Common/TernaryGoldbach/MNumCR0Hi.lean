/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCR0Lo

set_option autoImplicit false

/-!
# Region `R0` of `g̃`, `w > 1`, and the region envelope

GENERATED. The 9 pieces on `1, 1.5, 2, 2.4, 2.75, 3.05, 3.35, 3.6, 3.85, 4.1` and the Gaussian tail
    `w > 4.1` (`hiR0`), then **`envR0`**: `gT(y, r) ≤ envF … r` for `r ∈ [150000, 520000]`, `y ≥
    (10 ^ 25)`, from `gT_le_of`, and `envR0_pos`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[1, 1.5]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_1_1_5`). -/
private theorem tR0_hi0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1 1.5
      (1 / Real.sqrt r * (1.008467428030933 + Real.log r * 0.2197884358947243 + Real.log r ^ 2 *
          0.002076607177685875 + Real.log r ^ 3 * 0.0005979656113017515 + Real.log r ^ 4 *
          0.00001008702846802543) + 1 / r * (21.1344474833929 + Real.log r * 7.794599707393548 +
          Real.log r ^ 2 * 0.1682304522360303) + 0.00007625704579484692) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1 : ℝ) 1.5, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88400993525048313590140565799936, -0.000691461454714405575457199974528]
        [0, 0, 0.6300468338541294918285169155174144, -0.00134124015702018963576964191078112]
        [0, 0, 0.006567117269100296076389193814650368, -0.0005012173474915906561934819710139264]
        [0, 0, 0.001719345258307125804023079636272896, -0.000007795238217741492941858]
        [0, 0, 0.00002883813529122928761412]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00021801376] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88400993525048313590140565799936, -0.000691461454714405575457199974528]
        [0, 0, 0.6300468338541294918285169155174144, -0.00134124015702018963576964191078112]
        [0, 0, 0.006567117269100296076389193814650368, -0.0005012173474915906561934819710139264]
        [0, 0, 0.001719345258307125804023079636272896, -0.000007795238217741492941858]
        [0, 0, 0.00002883813529122928761412]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00021801376] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.8109302) + 0.8109302 * w ≤ Real.log w := log_ge_chord 1 1.5 w (-0.8109302)
        0.8109302 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL145)
        (le_trans (by norm_num) lgL146)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.8109302) 0.8109302 11.78323 13.16159 0.1217448
        0.01781047 (2537 / 2888) 0.630453678859 0.458310561 0.1444 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (2537 / 2888) = (5425 / 2888) by norm_num]; exact lgU147)
        (by norm_num) (by norm_num)
    have hRs : 0.458310561 + 0.1444 * ((2.08 + Real.log r) * (0.1217448 + 0.01781047 * (Real.log r -
        ((-0.8109302) + 0.8109302 * w) / 3 - 11.78323)) / 2) ≤ 0.445800042 + (-0.00333996748) *
        Real.log r + (-0.000722999725) * w + 0.00128591594 * Real.log r ^ 2 + (-0.000347596021) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ ((3216106229 / 46875000000000000000) + (48146633 /
          7500000000000000000) * Real.log r + (20733721 / 46875000000000000000) * w + 0.000000000006
          * Real.log r ^ 2 + (6354517 / 7500000000000000000) * w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000681293 :=
      (wy_rpow_le w y 1 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_1_1_5
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[1.5, 2]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_1_5_2`). -/
private theorem tR0_hi1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1.5 2
      (1 / Real.sqrt r * (0.9420161389323991 + Real.log r * 0.2053459030362009 + Real.log r ^ 2 *
          0.002040673905223119 + Real.log r ^ 3 * 0.0005457189764977717 + Real.log r ^ 4 *
          0.000009187104950142432) + 1 / r * (19.74244303475054 + Real.log r * 7.281214274601698 +
          Real.log r ^ 2 * 0.1571500803411093) + 0.00006657962847074482) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1.5 : ℝ) 2, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.8838818551174813389457064298496, -0.00047833559217308604063201936357376]
        [0, 0, 0.6300756234479999703328128045923328, -0.0009278361075136493236885028445198848]
        [0, 0, 0.006847995718055523706969492885781504, -0.0003467295174807277129284996956041856]
        [0, 0, 0.001679549194015532012958125397314944, -0.000005392549159256804411782]
        [0, 0, 0.00002811723502526923597818]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00020376768] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.8838818551174813389457064298496, -0.00047833559217308604063201936357376]
        [0, 0, 0.6300756234479999703328128045923328, -0.0009278361075136493236885028445198848]
        [0, 0, 0.006847995718055523706969492885781504, -0.0003467295174807277129284996956041856]
        [0, 0, 0.001679549194015532012958125397314944, -0.000005392549159256804411782]
        [0, 0, 0.00002811723502526923597818]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00020376768] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.457581043) + 0.5753641 * w ≤ Real.log w := log_ge_chord 1.5 2 w (-0.457581043)
        0.5753641 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL146)
        (le_trans (by norm_num) lgL151)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.457581043) 0.5753641 11.68734 13.02643 0.1203399
        0.01726362 (72 / 83) 0.624584509811 0.457568549 0.14525 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rw [show (1 : ℝ) + (72 / 83) = (155 / 83) by norm_num]; exact lgU152)
        (by norm_num) (by norm_num)
    have hRs : 0.457568549 + 0.14525 * ((2.08 + Real.log r) * (0.1203399 + 0.01726362 * (Real.log r
        - ((-0.457581043) + 0.5753641 * w) / 3 - 11.68734)) / 2) ≤ 0.44566612 + (-0.00311447944) *
        Real.log r + (-0.000500152972) * w + 0.00125377041 * Real.log r ^ 2 + (-0.000240458159) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000005151871686668 + 0.0000000000051015233975 * Real.log r +
          0.00000000000027379484 * w + 0.0000000000075 * Real.log r ^ 2 + 0.00000000000074701675 * w
          * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000636774 :=
      (wy_rpow_le w y 1.5 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_1_5_2
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[2, 2.4]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_2_2_4`). -/
private theorem tR0_hi2 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2 2.4
      (1 / Real.sqrt r * (0.4971009595784816 + Real.log r * 0.1083751677470183 + Real.log r ^ 2 *
          0.001110902399857683 + Real.log r ^ 3 * 0.0002834523331651519 + Real.log r ^ 4 *
          0.000004765579605169877) + 1 / r * (10.41826197964602 + Real.log r * 3.842361237118154 +
          Real.log r ^ 2 * 0.08292948872813015) + 0.00003348980686790178) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2 : ℝ) 2.4, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88380990293093799885098655013888, -0.00037248651192103365487891695950848]
        [0, 0, 0.6301120774686813228311134653650688, -0.0007225187521626427917249987024488704]
        [0, 0, 0.007032231742598761850779210498681472, -0.0002700030489901056900495921771115136]
        [0, 0, 0.001653082889685269878073212419309952, -0.000004199252274005398559942]
        [0, 0, 0.00002763855168519410307594]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00019422816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88380990293093799885098655013888, -0.00037248651192103365487891695950848]
        [0, 0, 0.6301120774686813228311134653650688, -0.0007225187521626427917249987024488704]
        [0, 0, 0.007032231742598761850779210498681472, -0.0002700030489901056900495921771115136]
        [0, 0, 0.001653082889685269878073212419309952, -0.000004199252274005398559942]
        [0, 0, 0.00002763855168519410307594]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00019422816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.21846042) + 0.4558038 * w ≤ Real.log w := log_ge_chord 2 2.4 w (-0.21846042)
        0.4558038 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL151)
        (le_trans (by norm_num) lgL153)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.21846042) 0.4558038 11.62656 12.93054 0.1194661
        0.0169057 (2509 / 2916) 0.6208050862 0.45709338 0.1458 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (2509 / 2916) = (5425 / 2916) by norm_num]; exact lgU154)
        (by norm_num) (by norm_num)
    have hRs : 0.45709338 + 0.1458 * ((2.08 + Real.log r) * (0.1194661 + 0.0169057 * (Real.log r -
        ((-0.21846042) + 0.4558038 * w) / 3 - 11.62656)) / 2) ≤ 0.445590886 + (-0.00296660017) *
        Real.log r + (-0.000389476006) * w + 0.00123242553 * Real.log r ^ 2 + (-0.000187248079) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000183320661664 + 0.0000000000080426258 * Real.log r +
          0.00000000000025510304 * w + 0.000000000000930338 * w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000606963 :=
      (wy_rpow_le w y 2 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_2_2_4
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[2.4, 2.75]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_2_4_2_75`). -/
private theorem tR0_hi3 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.4 2.75
      (1 / Real.sqrt r * (0.245391179433369 + Real.log r * 0.05350089114841657 + Real.log r ^ 2 *
          0.0005593093084198817 + Real.log r ^ 3 * 0.0001384784099358403 + Real.log r ^ 4 *
          0.00000232611967692479) + 1 / r * (5.14302378949834 + Real.log r * 1.896799609085696 +
          Real.log r ^ 2 * 0.04093853026665771) + 0.00001603756890967699) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.4 : ℝ) 2.75, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88374117087109390944211245604352, -0.00031428114954568203208698928247296]
        [0, 0, 0.6301050594443371008009180643782272, -0.0006096167697670599731489548283406208]
        [0, 0, 0.007153437087284950315508976192024448, -0.0002278119238306095196925025928364672]
        [0, 0, 0.001635949798229426104767176646778112, -0.000003543070135203821512934]
        [0, 0, 0.00002732803145430738380364]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00018841472] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88374117087109390944211245604352, -0.00031428114954568203208698928247296]
        [0, 0, 0.6301050594443371008009180643782272, -0.0006096167697670599731489548283406208]
        [0, 0, 0.007153437087284950315508976192024448, -0.0002278119238306095196925025928364672]
        [0, 0, 0.001635949798229426104767176646778112, -0.000003543070135203821512934]
        [0, 0, 0.00002732803145430738380364]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00018841472] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.0580088632) + 0.388949 * w ≤ Real.log w := log_ge_chord 2.4 2.75 w (-0.0580088632)
        0.388949 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL153)
        (le_trans (by norm_num) lgL155)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.0580088632) 0.388949 11.58119 12.86977 0.1188221
        0.01667117 (12506 / 14619) 0.618133759636 0.456758783 0.14619 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (12506 / 14619) = (27125 / 14619) by norm_num]; exact lgU156)
        (by norm_num) (by norm_num)
    have hRs : 0.456758783 + 0.14619 * ((2.08 + Real.log r) * (0.1188221 + 0.01667117 * (Real.log r
        - ((-0.0580088632) + 0.388949 * w) / 3 - 11.58119)) / 2) ≤ 0.445519019 + (-0.00286908803) *
        Real.log r + (-0.000328615837) * w + 0.00121857918 * Real.log r ^ 2 + (-0.000157988383) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000000454350477292352 + 0.00000000000815946525444 * Real.log r
          + 0.000000000000360804136 * w + 0.00000000000885 * Real.log r ^ 2 + 0.00000000000034654045
          * w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000588796 :=
      (wy_rpow_le w y 2.4 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_2_4_2_75
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[2.75, 3.05]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_2_75_3_05`). -/
private theorem tR0_hi4 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.75 3.05
      (1 / Real.sqrt r * (0.1100071624211806 + Real.log r * 0.02398471554417036 + Real.log r ^ 2 *
          0.0002543316972506536 + Real.log r ^ 3 * 0.00006159786557410607 + Real.log r ^ 4 *
          0.000001034017086270101) + 1 / r * (2.305617495663315 + Real.log r * 0.850335239242962 +
          Real.log r ^ 2 * 0.01835274256795826) + 0.000007028362314283219) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.75 : ℝ) 3.05, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88369044837640384131781275723264, -0.00027652999370882732354590174468096]
        [0, 0, 0.6301000801057349821502166792870528, -0.0005363901770929055190077033910071808]
        [0, 0, 0.007243132452514591329079580957119488, -0.0002004473697725524898925884617305728]
        [0, 0, 0.00162324863916301401662744393061568, -0.000003117479882324664153366]
        [0, 0, 0.0000270978779994887449221]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00018418816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88369044837640384131781275723264, -0.00027652999370882732354590174468096]
        [0, 0, 0.6301000801057349821502166792870528, -0.0005363901770929055190077033910071808]
        [0, 0, 0.007243132452514591329079580957119488, -0.0002004473697725524898925884617305728]
        [0, 0, 0.00162324863916301401662744393061568, -0.000003117479882324664153366]
        [0, 0, 0.0000270978779994887449221]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00018418816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.0624782857 + 0.3451355 * w ≤ Real.log w := log_ge_chord 2.75 3.05 w 0.0624782857
        0.3451355 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL155)
        (le_trans (by norm_num) lgL157)
    have hR := rChordHi y r w 19.997138805 2.08 0.0624782857 0.3451355 11.54667 12.82439 0.1183367
        0.01649804 (12477 / 14648) 0.61615200481 0.456511232 0.14648 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (12477 / 14648) = (27125 / 14648) by norm_num]; exact lgU158)
        (by norm_num) (by norm_num)
    have hRs : 0.456511232 + 0.14648 * ((2.08 + Real.log r) * (0.1183367 + 0.01649804 * (Real.log r
        - (0.0624782857 + 0.3451355 * w) / 3 - 11.54667)) / 2) ≤ 0.445465983 + (-0.00279691768) *
        Real.log r + (-0.000289142812) * w + 0.00120831645 * Real.log r ^ 2 + (-0.000139010967) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ ((9547587424121 / 117187500000000000000000) + (175991340317 /
          18750000000000000000000) * Real.log r + (1102463 / 23437500000000000000) * w +
          0.0000000000004 * Real.log r ^ 2 + (1238651 / 3750000000000000000) * w * Real.log r)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000575588 :=
      (wy_rpow_le w y 2.75 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_2_75_3_05
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[3.05, 3.35]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_3_05_3_35`). -/
private theorem tR0_hi5 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.05 3.35
      (1 / Real.sqrt r * (0.05400265423000219 + Real.log r * 0.01177390432995506 + Real.log r ^ 2 *
          0.0001262785939087545 + Real.log r ^ 3 * 0.00003005320448644656 + Real.log r ^ 4 *
          0.0000005042112023766309) + 1 / r * (1.13185274129388 + Real.log r * 0.4174388307541187 +
          Real.log r ^ 2 * 0.00900956122378324) + 0.00000339126684862432) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.05 : ℝ) 3.35, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.883628156569958253280630234368, -0.00024888745731095176147740900525568]
        [0, 0, 0.6300647886328534575352165860362496, -0.0004827714545885599908989429025768064]
        [0, 0, 0.007315035222390701203007861989870208, -0.000180410217039391713826775319262592]
        [0, 0, 0.00161326257807844813732148837076544, -0.00000280584984887872233674]
        [0, 0, 0.0000269164258304963726143]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.0001810368] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.883628156569958253280630234368, -0.00024888745731095176147740900525568]
        [0, 0, 0.6300647886328534575352165860362496, -0.0004827714545885599908989429025768064]
        [0, 0, 0.007315035222390701203007861989870208, -0.000180410217039391713826775319262592]
        [0, 0, 0.00161326257807844813732148837076544, -0.00000280584984887872233674]
        [0, 0, 0.0000269164258304963726143]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.0001810368] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.161317834 + 0.3127291 * w ≤ Real.log w := log_ge_chord 3.05 3.35 w 0.161317834
        0.3127291 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL157)
        (le_trans (by norm_num) lgL159)
    have hR := rChordHi y r w 19.997138805 2.08 0.161317834 0.3127291 11.5154 12.78988 0.1179004
        0.01635853 (12451 / 14674) 0.614378591908 0.456290194 0.14674 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (12451 / 14674) = (27125 / 14674) by norm_num]; exact lgU160)
        (by norm_num) (by norm_num)
    have hRs : 0.456290194 + 0.14674 * ((2.08 + Real.log r) * (0.1179004 + 0.01635853 * (Real.log r
        - (0.161317834 + 0.3127291 * w) / 3 - 11.5154)) / 2) ≤ 0.44540085 + (-0.00273879313) *
        Real.log r + (-0.000260239471) * w + 0.00120022535 * Real.log r ^ 2 + (-0.00012511513) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ ((61437997202581 / 93750000000000000000000) + (54602861737 /
          15000000000000000000000) * Real.log r + (1842953963 / 1875000000000000000000) * w +
          0.0000000000039 * Real.log r ^ 2 + (228304151 / 300000000000000000000) * w * Real.log r)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.000056574 :=
      (wy_rpow_le w y 3.05 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_3_05_3_35
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[3.35, 3.6]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_3_35_3_6`). -/
private theorem tR0_hi6 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.35 3.6
      (1 / Real.sqrt r * (0.02116421526838119 + Real.log r * 0.00461437238132462 + Real.log r ^ 2 *
          0.00004995305738649003 + Real.log r ^ 3 * 0.00001171557237110694 + Real.log r ^ 4 *
          0.0000001964661785122838) + 1 / r * (0.4435902166587489 + Real.log r * 0.1636005945122463
          + Real.log r ^ 2 * 0.003530983377475062) + 0.000001308469053932007) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.35 : ℝ) 3.6, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88359167933430748986844012175872, -0.00022779828807608617709010395098624]
        [0, 0, 0.6300581497769077426670392864386432, -0.0004418644156264547283050259195060352]
        [0, 0, 0.007375504412706500814176308462526848, -0.000165123381581961144477731134693952]
        [0, 0, 0.001604678144106330769733435989204096, -0.00000256809965010866508719]
        [0, 0, 0.00002676089693772417344062]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00017822816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88359167933430748986844012175872, -0.00022779828807608617709010395098624]
        [0, 0, 0.6300581497769077426670392864386432, -0.0004418644156264547283050259195060352]
        [0, 0, 0.007375504412706500814176308462526848, -0.000165123381581961144477731134693952]
        [0, 0, 0.001604678144106330769733435989204096, -0.00000256809965010866508719]
        [0, 0, 0.00002676089693772417344062]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00017822816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.244515779 + 0.2878939 * w ≤ Real.log w := log_ge_chord 3.35 3.6 w 0.244515779
        0.2878939 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL159)
        (le_trans (by norm_num) lgL161)
    have hR := rChordHi y r w 19.997138805 2.08 0.244515779 0.2878939 11.49141 12.7586 0.1175679
        0.01624187 (401 / 474) 0.613016565018 0.456120744 0.14694 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rw [show (1 : ℝ) + (401 / 474) = (875 / 474) by norm_num]; exact lgU162)
        (by norm_num) (by norm_num)
    have hRs : 0.456120744 + 0.14694 * ((2.08 + Real.log r) * (0.1175679 + 0.01624187 * (Real.log r
        - (0.244515779 + 0.2878939 * w) / 3 - 11.49141)) / 2) ≤ 0.445362709 + (-0.00269008903) *
        Real.log r + (-0.000238188403) * w + 0.00119329019 * Real.log r ^ 2 + (-0.000114513655) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000856529164772816 + 0.0000000000004193292177 * Real.log r +
          0.0000000000003111493456 * w + 0.0000000000011 * Real.log r ^ 2 + 0.00000000000043805257 *
          w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000556963 :=
      (wy_rpow_le w y 3.35 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_3_35_3_6
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[3.6, 3.85]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_3_6_3_85`). -/
private theorem tR0_hi7 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.6 3.85
      (1 / Real.sqrt r * (0.00993256246866213 + Real.log r * 0.002165502816150137 + Real.log r ^ 2 *
          0.00002362290464413471 + Real.log r ^ 3 * 0.000005474987431324903 + Real.log r ^ 4 *
          0.00000009177799154387952) + 1 / r * (0.2081844269012622 + Real.log r *
          0.07678053917821007 + Real.log r ^ 2 * 0.001657150503395871) + 0.0000006067646422105215)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.6 : ℝ) 3.85, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88354047673756722161218479943168, -0.0002115140700592106025824157568256]
        [0, 0, 0.6300216434543390885729184433972864, -0.000410277626049790481693551694317248]
        [0, 0, 0.007424745110678466045976285138896, -0.0001533194943203287946082977380179328]
        [0, 0, 0.00159786452652870975575559372499392, -0.000002384518387912674255066]
        [0, 0, 0.0000266369893556912587649]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00017610304] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88354047673756722161218479943168, -0.0002115140700592106025824157568256]
        [0, 0, 0.6300216434543390885729184433972864, -0.000410277626049790481693551694317248]
        [0, 0, 0.007424745110678466045976285138896, -0.0001533194943203287946082977380179328]
        [0, 0, 0.00159786452652870975575559372499392, -0.000002384518387912674255066]
        [0, 0, 0.0000266369893556912587649]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00017610304] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.314127924 + 0.2685572 * w ≤ Real.log w := log_ge_chord 3.6 3.85 w 0.314127924
        0.2685572 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL161)
        (le_trans (by norm_num) lgL163)
    have hR := rChordHi y r w 19.997138805 2.08 0.314127924 0.2685572 11.46903 12.73461 0.1172593
        0.01614579 (12412 / 14713) 0.611724355517 0.455960232 0.14713 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (12412 / 14713) = (27125 / 14713) by norm_num]; exact lgU164)
        (by norm_num) (by norm_num)
    have hRs : 0.455960232 + 0.14713 * ((2.08 + Real.log r) * (0.1172593 + 0.01614579 * (Real.log r
        - (0.314127924 + 0.2685572 * w) / 3 - 11.46903)) / 2) ≤ 0.445309171 + (-0.00265015125) *
        Real.log r + (-0.000221161445) * w + 0.00118776505 * Real.log r ^ 2 + (-0.000106327617) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000289940740002464 + 0.0000000000072327403858 * Real.log r +
          0.0000000000002755692192 * w + 0.00000000000865 * Real.log r ^ 2 + 0.00000000000092094674
          * w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000550322 :=
      (wy_rpow_le w y 3.6 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_3_6_3_85
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[3.85, 4.1]` (`w ≥ 1`) of region `R0`** (`ptHiS`; moments `mom_3_85_4_1`). -/
private theorem tR0_hi8 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.85 4.1
      (1 / Real.sqrt r * (0.004341076231037796 + Real.log r * 0.00094642903547081 + Real.log r ^ 2 *
          0.00001039772753633686 + Real.log r ^ 3 * 0.000002383313727756742 + Real.log r ^ 4 *
          0.00000003993729166794526) + 1 / r * (0.09098924626523 + Real.log r * 0.03355776170028663
          + Real.log r ^ 2 * 0.0007242754777404656) + 0.0000002622419466844462) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.85 : ℝ) 4.1, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88349897468882531976713642795008, -0.00019733620797524384565020952496128]
        [0, 0, 0.6299966749751361229309040158356992, -0.0003827765740170539362745814024011264]
        [0, 0, 0.007470719162369281722170899773997184, -0.00014304243604704439009546148967783936]
        [0, 0, 0.001591457455904126747287608566958848, -0.0000022246833033306419614792]
        [0, 0, 0.00002652060148380712884756]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00017414336] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.88349897468882531976713642795008, -0.00019733620797524384565020952496128]
        [0, 0, 0.6299966749751361229309040158356992, -0.0003827765740170539362745814024011264]
        [0, 0, 0.007470719162369281722170899773997184, -0.00014304243604704439009546148967783936]
        [0, 0, 0.001591457455904126747287608566958848, -0.0000022246833033306419614792]
        [0, 0, 0.00002652060148380712884756]
        [0, 0, 60.4219625]
        [0, 0, 22.2842358]
        [0, 0, 0.480959537]
        [0, 0, 0.00017414336] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.379200242 + 0.2516553 * w ≤ Real.log w := log_ge_chord 3.85 4.1 w 0.379200242
        0.2516553 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL163)
        (le_trans (by norm_num) lgL165)
    have hR := rChordHi y r w 19.997138805 2.08 0.379200242 0.2516553 11.44806 12.71223 0.1169717
        0.01605669 (2479 / 2946) 0.610569581775 0.455817 0.1473 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (2479 / 2946) = (5425 / 2946) by norm_num]; exact lgU166)
        (by norm_num) (by norm_num)
    have hRs : 0.455817 + 0.1473 * ((2.08 + Real.log r) * (0.1169717 + 0.01605669 * (Real.log r -
        (0.379200242 + 0.2516553 * w) / 3 - 11.44806)) / 2) ≤ 0.445265776 + (-0.00261294749) *
        Real.log r + (-0.000206336916) * w + 0.00118257522 * Real.log r ^ 2 + (-0.0000992004404) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000022414093479472 + 0.000000000009433910959 * Real.log r +
          0.000000000000159700248 * w + 0.0000000000015 * Real.log r ^ 2 + 0.00000000000006139435 *
          w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000544198 :=
      (wy_rpow_le w y 3.85 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine and_eq_of _ _ _ hp ?_
    unfold shapeG pevR
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine intBnd_of _ _ _ _ _ (by norm_num) (fun w hw => (key w hw).1)
    (fun w hw => (key w hw).2)
    ((continuous_shapeG _ _ _ _ _ _ _ _ _ _ _ _).intervalIntegrable _ _) ?_
  rw [int_shapeG]
  obtain ⟨j0l, j0h, j1l, j1h, j2l, j2h, j3l, j3h⟩ := mom_3_85_4_1
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **The Gaussian tail `w > 4.1` of region `R0`** (`ptHiS`, `tail_of`, `intBndI_tail`). -/
private theorem tR0_tail (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 4.1
      (1 / Real.sqrt r * (0.002959151655405952 + Real.log r * 0.0006452085132395599 + Real.log r ^ 2
          * 0.000007112283737486264 + Real.log r ^ 3 * 0.00000162039825919282 + Real.log r ^ 4 *
          0.00000002714899372034467) + 1 / r * (0.06202326800114985 + Real.log r *
          0.02287481359487816 + Real.log r ^ 2 * 0.0004937059477513652) + 0.0000001768940587748184)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 11.91 2.47737838232 0.083089 2.4878429575 (Real.log r)
      1.7810727 1.0117026 0.21431 1.16654 0.6931471808 hr (by norm_num) (by linarith) lgL148
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL150]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 1.95127016 + 0.0317152118 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 60.4219625 + 22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((681170891683447999 / 22500000000000000000000000) +
        (278941647607873 / 14062500000000000000000) * Real.log r + 0.000000000896525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Ioi (4.1 : ℝ), OC.gY (w * y) r * HW.phi w ≤ (0.70711 * (((0.444485582 +
      (-0.00298667808) * Real.log r + 0.0011793408 * Real.log r ^ 2) * (0.6931471808 + Real.log r) +
      0.5) * (1.95127016 + 0.0317152118 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (60.4219625 +
      22.2842358 * Real.log r + 0.480959537 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) *
      (w ^ 2 * Real.exp (-w ^ 2 / 2)) ∧ 0 ≤ (0.70711 * (((0.444485582 + (-0.00298667808) *
      Real.log r + 0.0011793408 * Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (1.95127016
      + 0.0317152118 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (60.4219625 + 22.2842358 *
      Real.log r + 0.480959537 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) := by
    intro w hw
    have hw' : (4.1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hτ : 1.41098697297 + 0 * w ≤ Real.log w := by
      have := Real.log_le_log (by norm_num) hw'.le
      linarith [lgL165]
    have hR := rChordHi y r w 19.997138805 2.08 1.41098697297 0 11.44806 12.69126 0.1169717
        0.0160106 (12393 / 14732) 0.610433813669 0.455800172 0.14732 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12393 / 14732) = (27125 / 14732) by norm_num]; exact lgU167)
        (by norm_num) (by norm_num)
    have hRs : 0.455800172 + 0.14732 * ((2.08 + Real.log r) * (0.1169717 + 0.0160106 * (Real.log r -
        (1.41098697297 + 0 * w) / 3 - 11.44806)) / 2) ≤ 0.444485582 + (-0.00298667808) * Real.log r
        + 0.0011793408 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000004303573095303232 + 0.00000000000199178342804 * Real.log r
          + 0.000000000004 * Real.log r ^ 2) (by ring) ?_
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000538522 :=
      (wy_rpow_le w y 4.1 (10 ^ 25) (by norm_num) hw'.le (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    have hp := ptHiS y r w _ _ _ _ _ hr hw0 hR.1 hRb hL0 hL hSs hLL0 hLs hY0 hY
    refine ⟨hp.1.trans_eq (by ring), ?_⟩
    exact cexp_nonneg _ _ _ _ _ _ _ (hR.1.trans hRb) (hL0.trans hL)
      ((Real.sqrt_nonneg _).trans hSs) (hLL0.trans hLs) (hY0.trans hY)
      (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le)
  have hC0 := (key 5.1 (by norm_num)).2
  have ht := intBndI_tail _ 4.1 _ (by norm_num) hC0
    (tail_of _ 4.1 _ (by norm_num) hC0 (fun w hw => (key w hw).1))
  refine intBndI_mono _ _ _ _ ht ?_
  have he := ex_4_1
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he.2 (by norm_num))
    (div_nonneg hC0 (by norm_num))) ?_
  have e : (0.70711 * (((0.444485582 + (-0.00298667808) * Real.log r + 0.0011793408 *
      Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (1.95127016 + 0.0317152118 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + (60.4219625 + 22.2842358 * Real.log r + 0.480959537 *
      Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) / 4.1 * ((4.1 ^ 2 + 2) *
      0.000223745793720620415502418151611) = 1 / Real.sqrt r * (((11848165807777737269692 * 10 ^ 40
      + 8214600121792741610089096783837961291729) / (4003906250000000000000000 * 10 ^ 40 + 0)) +
      Real.log r * ((1033341759485232513503408 * 10 ^ 40 + 5188853660721831909029490351408480040039)
      / (1601562500000000000000000000 * 10 ^ 40 + 0)) + Real.log r ^ 2 * ((71192293270736519742304 *
      10 ^ 40 + 4614701131527543401248231825596407602763) / (10009765625000000000000000000 * 10 ^ 40
      + 0)) + Real.log r ^ 3 * ((202747584920976594145 * 10 ^ 40 +
      637761620724428193451024215472940847689) / (125122070312500000000000000 * 10 ^ 40 + 0)) +
      Real.log r ^ 4 * ((5435101281 * 10 ^ 40 + 9049383463761254902837264688408863492203) /
      (200195312500000000 * 10 ^ 40 + 0))) + 1 / r * ((2034363190437714963199895565937533883287 /
      32800000000000000000000000000000000000000) + Real.log r *
      (46893367869500210139995447978380432783089 / 2050000000000000000000000000000000000000000) +
      Real.log r ^ 2 * (202419438578059719600839225025517266885267 /
      410000000000000000000000000000000000000000000)) + (113322756402617998527060230785268334951 /
      640625000000000000000000000000000000000000000) := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

/-- **Region `R0`, `w > 1`**: the 9 hi pieces and the Gaussian tail, added. -/
theorem hiR0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 1
      (1 / Real.sqrt r * (2.895382528249852558 + Real.log r * 0.6311405304466706169 + Real.log r ^ 2
          * 0.006259189055650414664 + Real.log r ^ 3 * 0.001678460672750449435 + Real.log r ^ 4 *
          0.00002825939144435371415) + 1 / r * (60.68043368207138595 + Real.log r *
          22.37956260718179786 + Real.log r ^ 2 * 0.4830169706700317238) + 0.0002051380489076798421)
          := by
  have h0 := tR0_hi0 y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR0_hi1 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR0_hi2 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR0_hi3 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR0_hi4 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR0_hi5 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR0_hi6 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR0_hi7 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR0_hi8 y r hy hr0 hr1)
  have ht := intBndI_add _ _ _ _ _ h8 (tR0_tail y r hy hr0 hr1)
  exact intBndI_mono _ _ _ _ ht (le_of_eq (by ring))

/-- **THE REGION ENVELOPE `R0`**: `g̃(y, r) ≤ P(ℓ)/√r + Q(ℓ)/r + z` on `r ∈ [150000, 520000]`, `y ≥
    (10 ^ 25)` (`gT_le_of` over `loR0`, `hiR0` and the sliver, divided by `|φ|₁ ≥ 1.2533139`). -/
theorem envR0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    OC.gT HW.phi y r ≤ envF 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633
        0.0000297025673079 63.3868846831 24.6165165572 0.545031222151 0.000210527045125 r := by
  have hr : 0 < r := by linarith
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨hy1, -, -⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  refine (gT_le_of y r _ _ _ hy1 hr (loR0 y r hy hr0 hr1) (hiR0 y r hy hr0 hr1)
    (sliver_bnd r 150000 0.0148148148149 (by norm_num) hr0 (by norm_num))).trans ?_
  rw [div_le_iff₀ (by norm_num), envF_eq]
  have hX : 0 ≤ 1 / Real.sqrt r := one_div_nonneg.mpr (Real.sqrt_nonneg r)
  have hZ : 0 ≤ 1 / r := one_div_nonneg.mpr hr.le
  linarith [hX, hZ, mul_nonneg hX (pow_nonneg hl0 1), mul_nonneg hX (pow_nonneg hl0 2),
      mul_nonneg hX (pow_nonneg hl0 3), mul_nonneg hX (pow_nonneg hl0 4),
      mul_nonneg hZ (pow_nonneg hl0 1), mul_nonneg hZ (pow_nonneg hl0 2)]

/-- **The region envelope `R0` is `≥ 0`** (so its antiderivative `envG` increases). -/
theorem envR0_pos (r : ℝ) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    0 ≤ envF 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633 0.0000297025673079
        63.3868846831 24.6165165572 0.545031222151 0.000210527045125 r := by
  have hr : 0 < r := by linarith
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hl0 : 0 ≤ Real.log r := by linarith
  refine envF_nonneg _ _ _ _ _ _ _ _ _ r hr ?_ ?_ ?_
  · have := tm_ge_pos 0.654209332173 11.9183905686 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.00636024697078 11.9183905686 (Real.log r) 2 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.00173163875633 11.9183905686 (Real.log r) 3 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.0000297025673079 11.9183905686 (Real.log r) 4 (by norm_num) (by norm_num)
        hla
    linarith
  · have := tm_ge_pos 24.6165165572 11.9183905686 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.545031222151 11.9183905686 (Real.log r) 2 (by norm_num) (by norm_num) hla
    linarith
  · norm_num

end Principia.Common.TernaryGoldbach.MC
