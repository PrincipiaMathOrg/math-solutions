/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCR2bLo

set_option autoImplicit false

/-!
# Region `R2b` of `g̃`, `w > 1`, and the region envelope

GENERATED. The 9 pieces on `1, 1.5, 2, 2.4, 2.75, 3.05, 3.35, 3.6, 3.85, 4.1` and the Gaussian tail
    `w > 4.1` (`hiR2b`), then **`envR2b`**: `gT(y, r) ≤ envF … r` for `r ∈ [3216000, 5950000]`, `y ≥
    (10 ^ 26)`, from `gT_le_of`, and `envR2b_pos`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[1, 1.5]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_1_1_5`). -/
private theorem tR2b_hi0 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1 1.5
      (1 / Real.sqrt r * (1.031690201403116 + Real.log r * 0.2342527979674517 + Real.log r ^ 2 *
          (-0.003406971578970305) + Real.log r ^ 3 * 0.0008093645543821469 + Real.log r ^ 4 *
          0.00001063559494511733) + 1 / r * (22.28655971311494 + Real.log r * 8.057322368300835 +
          Real.log r ^ 2 * 0.1335047908615747) + 0.00005195326257438481) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1 : ℝ) 1.5, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.95077072575375506515658535910272, -0.00098447967051391845563295419590912]
        [0, 0, 0.6721089303203357676783130336408192, -0.0019054614276478472222074954311366912]
        [0, 0, -0.00885303235748000662407687548301568, -0.0007056313982576487667232561638020992]
        [0, 0, 0.002324253660994788738577140091406592, -0.000008219169483416286123474]
        [0, 0, 0.00003040644991755906732924]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00014853088] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.95077072575375506515658535910272, -0.00098447967051391845563295419590912]
        [0, 0, 0.6721089303203357676783130336408192, -0.0019054614276478472222074954311366912]
        [0, 0, -0.00885303235748000662407687548301568, -0.0007056313982576487667232561638020992]
        [0, 0, 0.002324253660994788738577140091406592, -0.000008219169483416286123474]
        [0, 0, 0.00003040644991755906732924]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00014853088] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.8109302) + 0.8109302 * w ≤ Real.log w := log_ge_chord 1 1.5 w (-0.8109302)
        0.8109302 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL145)
        (le_trans (by norm_num) lgL146)
    have hR := rChordHi y r w 20.7646671384 2.08 (-0.8109302) 0.8109302 14.84849 15.59891 0.1690281
        0.03272083 (16374 / 10751) 0.92545703927 0.501440222 0.10751 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16374 / 10751) = (27125 / 10751) by norm_num]; exact lgU346)
        (by norm_num) (by norm_num)
    have hRs : 0.501440222 + 0.10751 * ((2.08 + Real.log r) * (0.1690281 + 0.03272083 * (Real.log r
        - ((-0.8109302) + 0.8109302 * w) / 3 - 14.84849)) / 2) ≤ 0.467004627 + (-0.0128970458) *
        Real.log r + (-0.000988937242) * w + 0.00175890822 * Real.log r ^ 2 + (-0.000475450597) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ ((1691864381971 / 1875000000000000000000) + (18723044767 /
          300000000000000000000) * Real.log r + (732516179 / 1875000000000000000000) * w +
          0.00000000000335 * Real.log r ^ 2 + (90962783 / 300000000000000000000) * w * Real.log r)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000464159 :=
      (wy_rpow_le w y 1 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[1.5, 2]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_1_5_2`). -/
private theorem tR2b_hi1 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1.5 2
      (1 / Real.sqrt r * (0.9636048398260132 + Real.log r * 0.2188265566878546 + Real.log r ^ 2 *
          (-0.002914815590118037) + Real.log r ^ 3 * 0.0007346792749824692 + Real.log r ^ 4 *
          0.000009638991893659616) + 1 / r * (20.81867226112609 + Real.log r * 7.526632905534723 +
          Real.log r ^ 2 * 0.1247115984707914) + 0.00004536016489340764) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1.5 : ℝ) 2, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.950300701948753607211022408416, -0.0006776818714357284240963541497216]
        [0, 0, 0.672000248281804264001203068209216, -0.001311653968185882555301067986701696]
        [0, 0, -0.00807679719885358702412163936434944, -0.0004857323326373705052309590222817408]
        [0, 0, 0.00225832514917592031795212619913856, -0.000005657792971567196401326]
        [0, 0, 0.0000295002399506158495782]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00013882528] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.950300701948753607211022408416, -0.0006776818714357284240963541497216]
        [0, 0, 0.672000248281804264001203068209216, -0.001311653968185882555301067986701696]
        [0, 0, -0.00807679719885358702412163936434944, -0.0004857323326373705052309590222817408]
        [0, 0, 0.00225832514917592031795212619913856, -0.000005657792971567196401326]
        [0, 0, 0.0000295002399506158495782]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00013882528] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.457581043) + 0.5753641 * w ≤ Real.log w := log_ge_chord 1.5 2 w (-0.457581043)
        0.5753641 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL146)
        (le_trans (by norm_num) lgL151)
    have hR := rChordHi y r w 20.7646671384 2.08 (-0.457581043) 0.5753641 14.75259 15.46375
        0.1663319 0.0313779 (16248 / 10877) 0.913805344252 0.4995397 0.10877 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16248 / 10877) = (27125 / 10877) by norm_num]; exact lgU350)
        (by norm_num) (by norm_num)
    have hRs : 0.4995397 + 0.10877 * ((2.08 + Real.log r) * (0.1663319 + 0.0313779 * (Real.log r -
        ((-0.457581043) + 0.5753641 * w) / 3 - 14.75259)) / 2) ≤ 0.466532475 + (-0.0123193654) *
        Real.log r + (-0.00068075031) * w + 0.0017064871 * Real.log r ^ 2 + (-0.000327283803) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000096834440167208 + 0.0000000000883071161885 * Real.log r +
          0.000000000000630010504 * w + 0.0000000000085 * Real.log r ^ 2 + 0.00000000000018750505 *
          w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000433829 :=
      (wy_rpow_le w y 1.5 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[2, 2.4]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_2_2_4`). -/
private theorem tR2b_hi2 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2 2.4
      (1 / Real.sqrt r * (0.5084566601294798 + Real.log r * 0.1154767702943216 + Real.log r ^ 2 *
          (-0.001447146129439033) + Real.log r ^ 3 * 0.0003802646187727039 + Real.log r ^ 4 *
          0.000004983935012918342) + 1 / r * (10.9861976708265 + Real.log r * 3.971870821481435 +
          Real.log r ^ 2 * 0.06581141465026108) + 0.00002281633550349507) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2 : ℝ) 2.4, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.95000383212932108382919174842496, -0.00052602626055556117550478284769536]
        [0, 0, 0.6719439854389934051477197298059136, -0.0010181243750489812153644103477511936]
        [0, 0, -0.00756983204049515770850032193872896, -0.000377032311267558930169123377124352]
        [0, 0, 0.002214977401781971519425940799689728, -0.00000439165898037619848144]
        [0, 0, 0.00002890493011610952557616]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00013232608] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.95000383212932108382919174842496, -0.00052602626055556117550478284769536]
        [0, 0, 0.6719439854389934051477197298059136, -0.0010181243750489812153644103477511936]
        [0, 0, -0.00756983204049515770850032193872896, -0.000377032311267558930169123377124352]
        [0, 0, 0.002214977401781971519425940799689728, -0.00000439165898037619848144]
        [0, 0, 0.00002890493011610952557616]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00013232608] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.21846042) + 0.4558038 * w ≤ Real.log w := log_ge_chord 2 2.4 w (-0.21846042)
        0.4558038 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL151)
        (le_trans (by norm_num) lgL153)
    have hR := rChordHi y r w 20.7646671384 2.08 (-0.21846042) 0.4558038 14.69182 15.36786 0.1646675
        0.03051187 (3233 / 2192) 0.906203531122 0.498307708 0.1096 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (3233 / 2192) = (5425 / 2192) by norm_num]; exact lgU351)
        (by norm_num) (by norm_num)
    have hRs : 0.498307708 + 0.1096 * ((2.08 + Real.log r) * (0.1646675 + 0.03051187 * (Real.log r -
        ((-0.21846042) + 0.4558038 * w) / 3 - 14.69182)) / 2) ≤ 0.466234261 + (-0.0119420616) *
        Real.log r + (-0.000528408026) * w + 0.00167205048 * Real.log r ^ 2 + (-0.00025404232) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000004830784213888 + 0.00000000008447693336 * Real.log r +
          0.000000000000121808768 * w + 0.000000000004 * Real.log r ^ 2 + 0.0000000000002508696 * w
          * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000413519 :=
      (wy_rpow_le w y 2 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[2.4, 2.75]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_2_4_2_75`). -/
private theorem tR2b_hi3 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.4 2.75
      (1 / Real.sqrt r * (0.250984078106071 + Real.log r * 0.05700110135082553 + Real.log r ^ 2 *
          (-0.0006852612688495583) + Real.log r ^ 3 * 0.0001853387833019398 + Real.log r ^ 4 *
          0.00000242745990056164) + 1 / r * (5.423387901703706 + Real.log r * 1.960732621583336 +
          Real.log r ^ 2 * 0.03248811287603391) + 0.00001092626727689327) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.4 : ℝ) 2.75, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94977720426519300239113962119552, -0.00044287236153266088537309408013184]
        [0, 0, 0.6718596844252540938636602301996672, -0.0008571799163943156994891144295622784]
        [0, 0, -0.00723904942592198373016263021886208, -0.000317431280901130778797343306404992]
        [0, 0, 0.002186875800306027649315391757085056, -0.00000369742829375642308974]
        [0, 0, 0.00002851861027387854764682]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00012836544] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94977720426519300239113962119552, -0.00044287236153266088537309408013184]
        [0, 0, 0.6718596844252540938636602301996672, -0.0008571799163943156994891144295622784]
        [0, 0, -0.00723904942592198373016263021886208, -0.000317431280901130778797343306404992]
        [0, 0, 0.002186875800306027649315391757085056, -0.00000369742829375642308974]
        [0, 0, 0.00002851861027387854764682]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00012836544] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.0580088632) + 0.388949 * w ≤ Real.log w := log_ge_chord 2.4 2.75 w (-0.0580088632)
        0.388949 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL153)
        (le_trans (by norm_num) lgL155)
    have hR := rChordHi y r w 20.7646671384 2.08 (-0.0580088632) 0.388949 14.64644 15.30708
        0.1634461 0.02994832 (16108 / 11017) 0.901016278099 0.497470666 0.11017 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16108 / 11017) = (27125 / 11017) by norm_num]; exact lgU352)
        (by norm_num) (by norm_num)
    have hRs : 0.497470666 + 0.11017 * ((2.08 + Real.log r) * (0.1634461 + 0.02994832 * (Real.log r
        - ((-0.0580088632) + 0.388949 * w) / 3 - 14.64644)) / 2) ≤ 0.466006607 + (-0.0116955688) *
        Real.log r + (-0.000444877619) * w + 0.00164970321 * Real.log r ^ 2 + (-0.00021388347) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ ((2764469520757 / 29296875000000000000000) + (78268809289 /
          4687500000000000000000) * Real.log r + (11667533 / 23437500000000000000) * w +
          0.0000000000028 * Real.log r ^ 2 + (3421541 / 3750000000000000000) * w * Real.log r)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000401142 :=
      (wy_rpow_le w y 2.4 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[2.75, 3.05]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_2_75_3_05`). -/
private theorem tR2b_hi4 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.75 3.05
      (1 / Real.sqrt r * (0.1125104376871978 + Real.log r * 0.02555238930379322 + Real.log r ^ 2 *
          (-0.0002975751133163714) + Real.log r ^ 3 * 0.00008229525543716476 + Real.log r ^ 4 *
          0.000001077298841844037) + 1 / r * (2.431304723394349 + Real.log r * 0.8789964078858157 +
          Real.log r ^ 2 * 0.0145644205653917) + 0.000004788373126910705) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.75 : ℝ) 3.05, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94961673783235018903734862018304, -0.0003890370405289281057739893222144]
        [0, 0, 0.6718077490955925401439449885238784, -0.000752981596724626116698170365095424]
        [0, 0, -0.00699429850067504947300072386045312, -0.0002788445089436270539570164792106368]
        [0, 0, 0.0021660292544288162453241873406368, -0.000003247970943560389397946]
        [0, 0, 0.0000282321375274206151335]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00012548608] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94961673783235018903734862018304, -0.0003890370405289281057739893222144]
        [0, 0, 0.6718077490955925401439449885238784, -0.000752981596724626116698170365095424]
        [0, 0, -0.00699429850067504947300072386045312, -0.0002788445089436270539570164792106368]
        [0, 0, 0.0021660292544288162453241873406368, -0.000003247970943560389397946]
        [0, 0, 0.0000282321375274206151335]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00012548608] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.0624782857 + 0.3451355 * w ≤ Real.log w := log_ge_chord 2.75 3.05 w 0.0624782857
        0.3451355 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL155)
        (le_trans (by norm_num) lgL157)
    have hR := rChordHi y r w 20.7646671384 2.08 0.0624782857 0.3451355 14.61193 15.26171 0.1625293
        0.02953489 (16066 / 11059) 0.897211236268 0.496858548 0.11059 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16066 / 11059) = (27125 / 11059) by norm_num]; exact lgU353)
        (by norm_num) (by norm_num)
    have hRs : 0.496858548 + 0.11059 * ((2.08 + Real.log r) * (0.1625293 + 0.02953489 * (Real.log r
        - (0.0624782857 + 0.3451355 * w) / 3 - 14.61193)) / 2) ≤ 0.465845414 + (-0.0115132467) *
        Real.log r + (-0.00039079854) * w + 0.00163313175 * Real.log r ^ 2 + (-0.000187883913) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ ((1869616869840991 / 3750000000000000000000000) + (55268128449307 /
          600000000000000000000000) * Real.log r + (76050073 / 750000000000000000000) * w +
          0.00000000000745 * Real.log r ^ 2 + (61234621 / 120000000000000000000) * w * Real.log r)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000392144 :=
      (wy_rpow_le w y 2.75 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[3.05, 3.35]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_3_05_3_35`). -/
private theorem tR2b_hi5 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.05 3.35
      (1 / Real.sqrt r * (0.05522976797356729 + Real.log r * 0.01254263264913146 + Real.log r ^ 2 *
          (-0.0001422960490796016) + Real.log r ^ 3 * 0.00004009203489792276 + Real.log r ^ 4 *
          0.0000005246043167331272) + 1 / r * (1.193553970366169 + Real.log r * 0.4315089106169397 +
          Real.log r ^ 2 * 0.007149832690505743) + 0.000002310448152507361) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.05 : ℝ) 3.35, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94945605438212845889864061633408, -0.00034967341492957166997276021354752]
        [0, 0, 0.6717191671645320520217795269012608, -0.0006767932590248591586237017744695552]
        [0, 0, -0.0067989817999009926412430325925376, -0.000250630407547247030915251582051008]
        [0, 0, 0.002149528822749628684797189119673344, -0.00000291933409211093969901]
        [0, 0, 0.00002800507627586954656368]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.0001233392] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94945605438212845889864061633408, -0.00034967341492957166997276021354752]
        [0, 0, 0.6717191671645320520217795269012608, -0.0006767932590248591586237017744695552]
        [0, 0, -0.0067989817999009926412430325925376, -0.000250630407547247030915251582051008]
        [0, 0, 0.002149528822749628684797189119673344, -0.00000291933409211093969901]
        [0, 0, 0.00002800507627586954656368]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.0001233392] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.161317834 + 0.3127291 * w ≤ Real.log w := log_ge_chord 3.05 3.35 w 0.161317834
        0.3127291 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL157)
        (le_trans (by norm_num) lgL159)
    have hR := rChordHi y r w 20.7646671384 2.08 0.161317834 0.3127291 14.58066 15.22719 0.1617075
        0.02920229 (458 / 317) 0.893961255915 0.496336991 0.11095 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rw [show (1 : ℝ) + (458 / 317) = (775 / 317) by norm_num]; exact lgU354)
        (by norm_num) (by norm_num)
    have hRs : 0.496336991 + 0.11095 * ((2.08 + Real.log r) * (0.1617075 + 0.02920229 * (Real.log r
        - (0.161317834 + 0.3127291 * w) / 3 - 14.58066)) / 2) ≤ 0.465684003 + (-0.01136742) *
        Real.log r + (-0.000351256682) * w + 0.00161999704 * Real.log r ^ 2 + (-0.000168873405) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ ((35526935772071 / 37500000000000000000000) + (470951982467 /
          6000000000000000000000) * Real.log r + (621476233 / 750000000000000000000) * w +
          0.00000000000225 * Real.log r ^ 2 + (24728941 / 120000000000000000000) * w * Real.log r)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000385435 :=
      (wy_rpow_le w y 3.05 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[3.35, 3.6]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_3_35_3_6`). -/
private theorem tR2b_hi6 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.35 3.6
      (1 / Real.sqrt r * (0.02164458343449157 + Real.log r * 0.004915402062723635 + Real.log r ^ 2 *
          (-0.00005453069035504335) + Real.log r ^ 3 * 0.00001561027699958838 + Real.log r ^ 4 *
          0.0000002041881531600622) + 1 / r * (0.4677718620033541 + Real.log r * 0.1691148717207989
          + Real.log r ^ 2 * 0.002802127623624989) + 0.000000891450823232009) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.35 : ℝ) 3.6, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94934117354476893643897527535872, -0.0003196932235930440424360278637632]
        [0, 0, 0.6716738615954252696084518004753152, -0.000618766567330141904292201327713472]
        [0, 0, -0.00663484544062742908099815448493312, -0.0002291419348409360146342953068536704]
        [0, 0, 0.002135529845030675289824359268992384, -0.000002669037124615072913538]
        [0, 0, 0.00002781271648890456729498]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.0001214256] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94934117354476893643897527535872, -0.0003196932235930440424360278637632]
        [0, 0, 0.6716738615954252696084518004753152, -0.000618766567330141904292201327713472]
        [0, 0, -0.00663484544062742908099815448493312, -0.0002291419348409360146342953068536704]
        [0, 0, 0.002135529845030675289824359268992384, -0.000002669037124615072913538]
        [0, 0, 0.00002781271648890456729498]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.0001214256] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.244515779 + 0.2878939 * w ≤ Real.log w := log_ge_chord 3.35 3.6 w 0.244515779
        0.2878939 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL159)
        (le_trans (by norm_num) lgL161)
    have hR := rChordHi y r w 20.7646671384 2.08 0.244515779 0.2878939 14.55667 15.19592 0.1610826
        0.0289261 (16001 / 11124) 0.891350875888 0.495918926 0.11124 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16001 / 11124) = (27125 / 11124) by norm_num]; exact lgU355)
        (by norm_num) (by norm_num)
    have hRs : 0.495918926 + 0.11124 * ((2.08 + Real.log r) * (0.1610826 + 0.0289261 * (Real.log r -
        (0.244515779 + 0.2878939 * w) / 3 - 14.55667)) / 2) ≤ 0.465568602 + (-0.0112450532) *
        Real.log r + (-0.000321140745) * w + 0.00160886969 * Real.log r ^ 2 + (-0.000154394589) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000049920676904608 + 0.000000000024520177426 * Real.log r +
          0.000000000000357632928 * w + 0.000000000008 * Real.log r ^ 2 + 0.0000000000001142466 * w
          * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000379455 :=
      (wy_rpow_le w y 3.35 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[3.6, 3.85]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_3_6_3_85`). -/
private theorem tR2b_hi7 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.6 3.85
      (1 / Real.sqrt r * (0.01015775444119216 + Real.log r * 0.002306627618029437 + Real.log r ^ 2 *
          (-0.00002511850353281774) + Real.log r ^ 3 * 0.000007287733186788356 + Real.log r ^ 4 *
          0.00000009529727347459855) + 1 / r * (0.2195332839962531 + Real.log r *
          0.07936848317996059 + Real.log r ^ 2 * 0.001315086112183892) + 0.0000004133839230559397)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.6 : ℝ) 3.85, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9492140123111419027007037555264, -0.00029656604388117551103153919950464]
        [0, 0, 0.671587895359900070165062584320448, -0.0005740038866776698758410359954708864]
        [0, 0, -0.00650189358686584322021873318582016, -0.0002125653970215267302326890202482688]
        [0, 0, 0.00212432201873599954155922001101248, -0.000002475954200312944004736]
        [0, 0, 0.0000276584006303476725681]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.0001199776] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9492140123111419027007037555264, -0.00029656604388117551103153919950464]
        [0, 0, 0.671587895359900070165062584320448, -0.0005740038866776698758410359954708864]
        [0, 0, -0.00650189358686584322021873318582016, -0.0002125653970215267302326890202482688]
        [0, 0, 0.00212432201873599954155922001101248, -0.000002475954200312944004736]
        [0, 0, 0.0000276584006303476725681]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.0001199776] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.314127924 + 0.2685572 * w ≤ Real.log w := log_ge_chord 3.6 3.85 w 0.314127924
        0.2685572 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL161)
        (le_trans (by norm_num) lgL163)
    have hR := rChordHi y r w 20.7646671384 2.08 0.314127924 0.2685572 14.53429 15.17193 0.160504
        0.02869853 (639 / 446) 0.889016314853 0.495545676 0.1115 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rw [show (1 : ℝ) + (639 / 446) = (1085 / 446) by norm_num]; exact lgU356)
        (by norm_num) (by norm_num)
    have hRs : 0.495545676 + 0.1115 * ((2.08 + Real.log r) * (0.160504 + 0.02869853 * (Real.log r -
        (0.314127924 + 0.2685572 * w) / 3 - 14.53429)) / 2) ≤ 0.465440865 + (-0.0111455856) *
        Real.log r + (-0.000297908849) * w + 0.00159994305 * Real.log r ^ 2 + (-0.000143225408) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000007035991751504 + 0.00000000002639191113 * Real.log r +
          (6198871 / 18750000000000000000) * w + 0.0000000000025 * Real.log r ^ 2 + (996067 /
          3000000000000000000) * w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.000037493 :=
      (wy_rpow_le w y 3.6 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[3.85, 4.1]` (`w ≥ 1`) of region `R2b`** (`ptHiS`; moments `mom_3_85_4_1`). -/
private theorem tR2b_hi8 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.85 4.1
      (1 / Real.sqrt r * (0.00443941752277762 + Real.log r * 0.0010080791850418 + Real.log r ^ 2 *
          (-0.000010783639196982) + Real.log r ^ 3 * 0.000003169267280579664 + Real.log r ^ 4 *
          0.00000004143083258732486) + 1 / r * (0.09594938650441699 + Real.log r *
          0.03468885050265696 + Real.log r ^ 2 * 0.0005747725509662438) + 0.0000001786634637922813)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.85 : ℝ) 4.1, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94911611358142890058002534752128, -0.00027643438391977971315186542608896]
        [0, 0, 0.6715383621030703849086763414447488, -0.0005350390381011224770522142387370496]
        [0, 0, -0.00637688134954736264339847299607424, -0.0001981359157023939875493283722121472]
        [0, 0, 0.002113703918784629215332245917443456, -0.000002307880114126589416284]
        [0, 0, 0.00002751239641702281979482]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00011864256] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.94911611358142890058002534752128, -0.00027643438391977971315186542608896]
        [0, 0, 0.6715383621030703849086763414447488, -0.0005350390381011224770522142387370496]
        [0, 0, -0.00637688134954736264339847299607424, -0.0001981359157023939875493283722121472]
        [0, 0, 0.002113703918784629215332245917443456, -0.000002307880114126589416284]
        [0, 0, 0.00002751239641702281979482]
        [0, 0, 63.7157738]
        [0, 0, 23.0353422]
        [0, 0, 0.381681209]
        [0, 0, 0.00011864256] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.379200242 + 0.2516553 * w ≤ Real.log w := log_ge_chord 3.85 4.1 w 0.379200242
        0.2516553 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL163)
        (le_trans (by norm_num) lgL165)
    have hR := rChordHi y r w 20.7646671384 2.08 0.379200242 0.2516553 14.51331 15.14955 0.1599653
        0.02848827 (15952 / 11173) 0.886955659094 0.495216723 0.11173 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (15952 / 11173) = (27125 / 11173) by norm_num]; exact lgU357)
        (by norm_num) (by norm_num)
    have hRs : 0.495216723 + 0.11173 * ((2.08 + Real.log r) * (0.1599653 + 0.02848827 * (Real.log r
        - (0.379200242 + 0.2516553 * w) / 3 - 14.51331)) / 2) ≤ 0.465342523 + (-0.0110522819) *
        Real.log r + (-0.000277686036) * w + 0.00159149721 * Real.log r ^ 2 + (-0.000133502902) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000032900589432976 + 0.0000000000862797449197 * Real.log r +
          0.0000000000003045851784 * w + 0.00000000000645 * Real.log r ^ 2 + 0.000000000000069512105
          * w * Real.log r) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000370758 :=
      (wy_rpow_le w y 3.85 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **The Gaussian tail `w > 4.1` of region `R2b`** (`ptHiS`, `tail_of`, `intBndI_tail`). -/
private theorem tR2b_tail (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 4.1
      (1 / Real.sqrt r * (0.003026159691383418 + Real.log r * 0.0006872252069668164 + Real.log r ^ 2
          * (-0.000007282477248180511) + Real.log r ^ 3 * 0.000002154102596079514 + Real.log r ^ 4 *
          0.00000002815659524337651) + 1 / r * (0.06540437203273631 + Real.log r *
          0.02364582584964527 + Real.log r ^ 2 * 0.0003917965411469363) + 0.0000001205165956413144)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.98 2.70671597704 0.065938 2.71904037337 (Real.log r)
      1.7810727 0.9259819 0.20817 1.20095 0.6931471808 hr (by norm_num) (by linarith) lgL347
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL349]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.03107322 + 0.0244475622 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 63.7157738 + 23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((263135359511594213561 / 5625000000000000000000000000) +
        (6095104324440653 / 112500000000000000000000) * Real.log r + 0.00000000099905 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Ioi (4.1 : ℝ), OC.gY (w * y) r * HW.phi w ≤ (0.70711 * (((0.464252344 +
      (-0.0115314833) * Real.log r + 0.00158671081 * Real.log r ^ 2) * (0.6931471808 + Real.log r) +
      0.5) * (2.03107322 + 0.0244475622 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (63.7157738 +
      23.0353422 * Real.log r + 0.381681209 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000366891) *
      (w ^ 2 * Real.exp (-w ^ 2 / 2)) ∧ 0 ≤ (0.70711 * (((0.464252344 + (-0.0115314833) * Real.log r
      + 0.00158671081 * Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (2.03107322 +
      0.0244475622 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (63.7157738 + 23.0353422 * Real.log r
      + 0.381681209 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000366891) := by
    intro w hw
    have hw' : (4.1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hτ : 1.41098697297 + 0 * w ≤ Real.log w := by
      have := Real.log_le_log (by norm_num) hw'.le
      linarith [lgL165]
    have hR := rChordHi y r w 20.7646671384 2.08 1.41098697297 0 14.51331 15.12858 0.1599653
        0.02838227 (15944 / 11181) 0.886239903462 0.495102574 0.11181 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15944 / 11181) = (27125 / 11181) by norm_num]; exact lgU358)
        (by norm_num) (by norm_num)
    have hRs : 0.495102574 + 0.11181 * ((2.08 + Real.log r) * (0.1599653 + 0.02838227 * (Real.log r
        - (1.41098697297 + 0 * w) / 3 - 14.51331)) / 2) ≤ 0.464252344 + (-0.0115314833) * Real.log r
        + 0.00158671081 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000090028623182983752 + 0.0000000000059357653028065 *
          Real.log r + 0.00000000000565 * Real.log r ^ 2) (by ring) ?_
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hRb := hR.2.trans hRs
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000366891 :=
      (wy_rpow_le w y 4.1 (10 ^ 26) (by norm_num) hw'.le (by norm_num) hy).trans
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
  have e : (0.70711 * (((0.464252344 + (-0.0115314833) * Real.log r + 0.00158671081 *
      Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (2.03107322 + 0.0244475622 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + (63.7157738 + 23.0353422 * Real.log r + 0.381681209 *
      Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000366891) / 4.1 * ((4.1 ^ 2 + 2) *
      0.000223745793720620415502418151611) = 1 / Real.sqrt r * (((12116459701828138022123 * 10 ^ 40
      + 6524800247740661039736473296120122254881) / (4003906250000000000000000 * 10 ^ 40 + 0)) +
      Real.log r * ((1100634120532791780707650 * 10 ^ 40 + 1166996317354772720344859761560508386569)
      / (1601562500000000000000000000 * 10 ^ 40 + 0)) + Real.log r ^ 2 *
      ((-(233266849355781997816412 * 10 ^ 40 + 6813872222518470671549637004374547482691)) /
      (32031250000000000000000000000 * 10 ^ 40 + 0)) + Real.log r ^ 3 * ((689985987806719122327920 *
      10 ^ 40 + 8444944761774339127395750512338540676977) / (320312500000000000000000000000 *
      10 ^ 40 + 0)) + Real.log r ^ 4 * ((57721020248921 * 10 ^ 40 +
      8257332553922763457612093224708012961591) / (2050000000000000000000 * 10 ^ 40 + 0))) + 1 / r *
      ((134078962667109423978201500471474769870879 / 2050000000000000000000000000000000000000000) +
      Real.log r * (48473942991772788705938260203847397402901 /
      2050000000000000000000000000000000000000000) + Real.log r ^ 2 *
      (160636581870243846836224214059742173851819 / 410000000000000000000000000000000000000000000))
      + (154411888165433984489367770055960145281 / (128125 * 10 ^ 40 + 0)) := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

/-- **Region `R2b`, `w > 1`**: the 9 hi pieces and the Gaussian tail, added. -/
theorem hiR2b (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 1
      (1 / Real.sqrt r * (2.961743900215289858 + Real.log r * 0.6725695823261397984 + Real.log r ^ 2
          * (-0.008991781040105929901) + Real.log r ^ 3 * 0.002260255901837383234 + Real.log r ^ 4 *
          0.00002965695776529945432) + 1 / r * (63.9883351450685145 + Real.log r *
          23.13388206665614612 + Real.log r ^ 2 * 0.3833139529424805941) + 0.0001397588663333204004)
          := by
  have h0 := tR2b_hi0 y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR2b_hi1 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR2b_hi2 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR2b_hi3 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR2b_hi4 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR2b_hi5 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR2b_hi6 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR2b_hi7 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR2b_hi8 y r hy hr0 hr1)
  have ht := intBndI_add _ _ _ _ _ h8 (tR2b_tail y r hy hr0 hr1)
  exact intBndI_mono _ _ _ _ ht (le_of_eq (by ring))

/-- **THE REGION ENVELOPE `R2b`**: `g̃(y, r) ≤ P(ℓ)/√r + Q(ℓ)/r + z` on `r ∈ [3216000, 5950000]`, `y
    ≥ (10 ^ 26)` (`gT_le_of` over `loR2b`, `hiR2b` and the sliver, divided by `|φ|₁ ≥
    1.2533139`). -/
theorem envR2b (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    OC.gT HW.phi y r ≤ envF 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 66.9482087513 25.5001453531 0.431143061793 0.000143820551574 r := by
  have hr : 0 < r := by linarith
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨hy1, -, -⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  refine (gT_le_of y r _ _ _ hy1 hr (loR2b y r hy hr0 hr1) (hiR2b y r hy hr0 hr1)
    (sliver_bnd r 3216000 0.0000322289877314 (by norm_num) hr0 (by norm_num))).trans ?_
  rw [div_le_iff₀ (by norm_num), envF_eq]
  have hX : 0 ≤ 1 / Real.sqrt r := one_div_nonneg.mpr (Real.sqrt_nonneg r)
  have hZ : 0 ≤ 1 / r := one_div_nonneg.mpr hr.le
  linarith [hX, hZ, mul_nonneg hX (pow_nonneg hl0 1), mul_nonneg hX (pow_nonneg hl0 2),
      mul_nonneg hX (pow_nonneg hl0 3), mul_nonneg hX (pow_nonneg hl0 4),
      mul_nonneg hZ (pow_nonneg hl0 1), mul_nonneg hZ (pow_nonneg hl0 2)]

/-- **The region envelope `R2b` is `≥ 0`** (so its antiderivative `envG` increases). -/
theorem envR2b_pos (r : ℝ) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    0 ≤ envF 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774 0.0000310866337797
        66.9482087513 25.5001453531 0.431143061793 0.000143820551574 r := by
  have hr : 0 < r := by linarith
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hl0 : 0 ≤ Real.log r := by linarith
  refine envF_nonneg _ _ _ _ _ _ _ _ _ r hr ?_ ?_ ?_
  · have := tm_ge_pos 0.700385883674 14.9836489035 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_neg (-0.00959431030359) 15.5989017831 (Real.log r) 2 (by norm_num) hl0 hlb
    have := tm_ge_pos 0.00233394703774 14.9836489035 (Real.log r) 3 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.0000310866337797 14.9836489035 (Real.log r) 4 (by norm_num) (by norm_num)
        hla
    linarith
  · have := tm_ge_pos 25.5001453531 14.9836489035 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.431143061793 14.9836489035 (Real.log r) 2 (by norm_num) (by norm_num) hla
    linarith
  · norm_num

end Principia.Common.TernaryGoldbach.MC
