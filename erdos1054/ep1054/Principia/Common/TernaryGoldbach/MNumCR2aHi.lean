/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCR2aLo

set_option autoImplicit false

/-!
# Region `R2a` of `g̃`, `w > 1`, and the region envelope

GENERATED. The 9 pieces on `1, 1.5, 2, 2.4, 2.75, 3.05, 3.35, 3.6, 3.85, 4.1` and the Gaussian tail
    `w > 4.1` (`hiR2a`), then **`envR2a`**: `gT(y, r) ≤ envF … r` for `r ∈ [1740000, 3216400]`, `y ≥
    (10 ^ 25)`, from `gT_le_of`, and `envR2a_pos`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[1, 1.5]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_1_1_5`). -/
private theorem tR2a_hi0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1 1.5
      (1 / Real.sqrt r * (1.026613017699755 + Real.log r * 0.2302048199311695 + Real.log r ^ 2 *
          (-0.003290039393545159) + Real.log r ^ 3 * 0.0008681008314746462 + Real.log r ^ 4 *
          0.00001213972675035178) + 1 / r * (22.03576895262841 + Real.log r * 7.997084538482658 +
          Real.log r ^ 2 * 0.1400830468512018) + 0.00007625704579484692) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1 : ℝ) 1.5, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9363445399008786296143821556928, -0.00105537168978108987856602744576]
        [0, 0, 0.6607095995482664436487064681049344, -0.00204349556825159980711805209266688]
        [0, 0, -0.00845284968264171119874347519248128, -0.0007580258261809288746285136522980352]
        [0, 0, 0.002493638327592004915990879928133376, -0.000009381559944637275880144]
        [0, 0, 0.00003470666148459185867972]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00021801376] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9363445399008786296143821556928, -0.00105537168978108987856602744576]
        [0, 0, 0.6607095995482664436487064681049344, -0.00204349556825159980711805209266688]
        [0, 0, -0.00845284968264171119874347519248128, -0.0007580258261809288746285136522980352]
        [0, 0, 0.002493638327592004915990879928133376, -0.000009381559944637275880144]
        [0, 0, 0.00003470666148459185867972]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00021801376] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.8109302) + 0.8109302 * w ≤ Real.log w := log_ge_chord 1 1.5 w (-0.8109302)
        0.8109302 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL145)
        (le_trans (by norm_num) lgL146)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.8109302) 0.8109302 14.23424 14.98378 0.1735238
        0.03461226 (16137 / 10988) 0.903652044309 0.497895618 0.10988 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16137 / 10988) = (27125 / 10988) by norm_num]; exact lgU298)
        (by norm_num) (by norm_num)
    have hRs : 0.497895618 + 0.10988 * ((2.08 + Real.log r) * (0.1735238 + 0.03461226 * (Real.log r
        - ((-0.8109302) + 0.8109302 * w) / 3 - 14.23424)) / 2) ≤ 0.462493233 + (-0.0130650546) *
        Real.log r + (-0.0010691636) * w + 0.00190159757 * Real.log r ^ 2 + (-0.000514020964) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000003636521557632 + 0.00000000004472692104 * Real.log r +
          0.0000000000059647607168 * w + 0.0000000000056 * Real.log r ^ 2 + 0.00000000000040613496 *
          w * Real.log r) (by ring) ?_
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
/-- **Piece `[1.5, 2]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_1_5_2`). -/
private theorem tR2a_hi1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1.5 2
      (1 / Real.sqrt r * (0.958956914804392 + Real.log r * 0.2151973154382701 + Real.log r ^ 2 *
          (-0.002785623861623551) + Real.log r ^ 3 * 0.0007865084738313507 + Real.log r ^ 4 *
          0.00001098030650036213) + 1 / r * (20.58439964498898 + Real.log r * 7.470362594959685 +
          Real.log r ^ 2 * 0.1308565825895042) + 0.00006657962847074482) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1.5 : ℝ) 2, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9361579631413032262772341666688, -0.0007250371899870895689616226715456]
        [0, 0, 0.6610531633029525191500269052557824, -0.0014038753332882627655167710450258688]
        [0, 0, -0.00762053648654760299678698203539968, -0.0005207614697474332440959914153621248]
        [0, 0, 0.002418317040296296106057546684619264, -0.000006445103551793801087556]
        [0, 0, 0.00003360534795190153595608]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00020376768] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9361579631413032262772341666688, -0.0007250371899870895689616226715456]
        [0, 0, 0.6610531633029525191500269052557824, -0.0014038753332882627655167710450258688]
        [0, 0, -0.00762053648654760299678698203539968, -0.0005207614697474332440959914153621248]
        [0, 0, 0.002418317040296296106057546684619264, -0.000006445103551793801087556]
        [0, 0, 0.00003360534795190153595608]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00020376768] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.457581043) + 0.5753641 * w ≤ Real.log w := log_ge_chord 1.5 2 w (-0.457581043)
        0.5753641 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL146)
        (le_trans (by norm_num) lgL151)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.457581043) 0.5753641 14.13834 14.84862 0.1706835
        0.03315189 (16017 / 11108) 0.892790242836 0.496149354 0.11108 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (16017 / 11108) = (27125 / 11108) by norm_num]; exact lgU302)
        (by norm_num) (by norm_num)
    have hRs : 0.496149354 + 0.11108 * ((2.08 + Real.log r) * (0.1706835 + 0.03315189 * (Real.log r
        - ((-0.457581043) + 0.5753641 * w) / 3 - 14.13834)) / 2) ≤ 0.462304218 + (-0.0124418876) *
        Real.log r + (-0.000734512191) * w + 0.00184125598 * Real.log r ^ 2 + (-0.000353130861) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000152991825420512 + 0.0000000000547057622214 * Real.log r +
          0.0000000000008464341856 * w + 0.0000000000094 * Real.log r ^ 2 + 0.00000000000046463182 *
          w * Real.log r) (by ring) ?_
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
/-- **Piece `[2, 2.4]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_2_2_4`). -/
private theorem tR2a_hi2 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2 2.4
      (1 / Real.sqrt r * (0.5060415676077343 + Real.log r * 0.1136213191743335 + Real.log r ^ 2 *
          (-0.0013719287939379) + Real.log r ^ 3 * 0.0004065158423846187 + Real.log r ^ 4 *
          0.000005669079675679379) + 1 / r * (10.86256993715254 + Real.log r * 3.9421764804004 +
          Real.log r ^ 2 * 0.06905417717447484) + 0.00003348980686790178) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2 : ℝ) 2.4, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9360756389778845100995861372288, -0.000561951950263707872290649423328]
        [0, 0, 0.6613358237767349218738096978010624, -0.001088096572522898558920885386562944]
        [0, 0, -0.00707554855755782395038319027573248, -0.0004036247070557352564067933416850944]
        [0, 0, 0.002368542464836411287754680921502208, -0.000004995383076760484558568]
        [0, 0, 0.00003287850893389129133176]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00019422816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9360756389778845100995861372288, -0.000561951950263707872290649423328]
        [0, 0, 0.6613358237767349218738096978010624, -0.001088096572522898558920885386562944]
        [0, 0, -0.00707554855755782395038319027573248, -0.0004036247070557352564067933416850944]
        [0, 0, 0.002368542464836411287754680921502208, -0.000004995383076760484558568]
        [0, 0, 0.00003287850893389129133176]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00019422816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.21846042) + 0.4558038 * w ≤ Real.log w := log_ge_chord 2 2.4 w (-0.21846042)
        0.4558038 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL151)
        (le_trans (by norm_num) lgL153)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.21846042) 0.4558038 14.07757 14.75273 0.1689313
        0.03221157 (3188 / 2237) 0.88588221767 0.495045552 0.11185 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (3188 / 2237) = (5425 / 2237) by norm_num]; exact lgU303)
        (by norm_num) (by norm_num)
    have hRs : 0.495045552 + 0.11185 * ((2.08 + Real.log r) * (0.1689313 + 0.03221157 * (Real.log r
        - ((-0.21846042) + 0.4558038 * w) / 3 - 14.07757)) / 2) ≤ 0.462220818 + (-0.0120341436) *
        Real.log r + (-0.000569295705) * w + 0.00180143206 * Real.log r ^ 2 + (-0.000273699858) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000004444192163848 + 0.000000000060367700185 * Real.log r +
          0.000000000000234428328 * w + 0.00000000000775 * Real.log r ^ 2 + 0.00000000000028578285 *
          w * Real.log r) (by ring) ?_
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
/-- **Piece `[2.4, 2.75]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_2_4_2_75`). -/
private theorem tR2a_hi3 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.4 2.75
      (1 / Real.sqrt r * (0.2498011128941152 + Real.log r * 0.05609997251944377 + Real.log r ^ 2 *
          (-0.000646224621439164) + Real.log r ^ 3 * 0.0001979844025059802 + Real.log r ^ 4 *
          0.000002758964679813976) + 1 / r * (5.362358492329173 + Real.log r * 1.946073871122693 +
          Real.log r ^ 2 * 0.03408891777403972) + 0.00001603756890967699) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.4 : ℝ) 2.75, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9359557062937673156681204828288, -0.0004727420378548059071513801871936]
        [0, 0, 0.6614216833260732852155780677197824, -0.0009153611636807736098631731229033728]
        [0, 0, -0.00672388116299135375083858602290432, -0.0003395492559880090925739114501109248]
        [0, 0, 0.002336731818213513514195902520806656, -0.000004202365656648380486056]
        [0, 0, 0.00003241323922376897841132]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00018841472] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9359557062937673156681204828288, -0.0004727420378548059071513801871936]
        [0, 0, 0.6614216833260732852155780677197824, -0.0009153611636807736098631731229033728]
        [0, 0, -0.00672388116299135375083858602290432, -0.0003395492559880090925739114501109248]
        [0, 0, 0.002336731818213513514195902520806656, -0.000004202365656648380486056]
        [0, 0, 0.00003241323922376897841132]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00018841472] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.0580088632) + 0.388949 * w ≤ Real.log w := log_ge_chord 2.4 2.75 w (-0.0580088632)
        0.388949 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL153)
        (le_trans (by norm_num) lgL155)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.0580088632) 0.388949 14.03219 14.69196 0.1676461
        0.03160035 (3177 / 2248) 0.880976967977 0.494265003 0.1124 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (3177 / 2248) = (5425 / 2248) by norm_num]; exact lgU304)
        (by norm_num) (by norm_num)
    have hRs : 0.494265003 + 0.1124 * ((2.08 + Real.log r) * (0.1676461 + 0.03160035 * (Real.log r -
        ((-0.0580088632) + 0.388949 * w) / 3 - 14.03219)) / 2) ≤ 0.462099318 + (-0.0117703174) *
        Real.log r + (-0.000478919971) * w + 0.00177593967 * Real.log r ^ 2 + (-0.000230249986) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000071324396902016 + 0.000000000063921138952 * Real.log r +
          0.0000000000003700688 * w + 0.00000000000023561 * w * Real.log r) (by ring) ?_
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
/-- **Piece `[2.75, 3.05]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_2_75_3_05`). -/
private theorem tR2a_hi4 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.75 3.05
      (1 / Real.sqrt r * (0.1119828335863927 + Real.log r * 0.0251527910756886 + Real.log r ^ 2 *
          (-0.0002794867024471692) + Real.log r ^ 3 * 0.00008786477282599893 + Real.log r ^ 4 *
          0.000001223745291326091) + 1 / r * (2.403945239992534 + Real.log r * 0.8724248902514555 +
          Real.log r ^ 2 * 0.0152820613796384) + 0.000007028362314283219) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.75 : ℝ) 3.05, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9358651299720011118736242816128, -0.0004150470786909479187571122259392]
        [0, 0, 0.6614818138139476938952324184710144, -0.0008036475424768524581664691060188416]
        [0, 0, -0.00646471330434981738804362812845312, -0.0002981095724644077537095347593884416]
        [0, 0, 0.00231325950543980406052622580213376, -0.000003689495433003722688852]
        [0, 0, 0.0000320699735498772159222]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00018418816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9358651299720011118736242816128, -0.0004150470786909479187571122259392]
        [0, 0, 0.6614818138139476938952324184710144, -0.0008036475424768524581664691060188416]
        [0, 0, -0.00646471330434981738804362812845312, -0.0002981095724644077537095347593884416]
        [0, 0, 0.00231325950543980406052622580213376, -0.000003689495433003722688852]
        [0, 0, 0.0000320699735498772159222]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00018418816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.0624782857 + 0.3451355 * w ≤ Real.log w := log_ge_chord 2.75 3.05 w 0.0624782857
        0.3451355 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL155)
        (le_trans (by norm_num) lgL157)
    have hR := rChordHi y r w 19.997138805 2.08 0.0624782857 0.3451355 13.99768 14.64658 0.1666818
        0.03115206 (15844 / 11281) 0.87733591773 0.493687368 0.11281 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (15844 / 11281) = (27125 / 11281) by norm_num]; exact lgU305)
        (by norm_num) (by norm_num)
    have hRs : 0.493687368 + 0.11281 * ((2.08 + Real.log r) * (0.1666818 + 0.03115206 * (Real.log r
        - (0.0624782857 + 0.3451355 * w) / 3 - 13.99768)) / 2) ≤ 0.462007558 + (-0.0115758434) *
        Real.log r + (-0.000420471037) * w + 0.00175713195 * Real.log r ^ 2 + (-0.000202149537) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000001199813957613136 + 0.00000000009815474796217 * Real.log r
          + 0.000000000000765620504 * w + 0.0000000000057 * Real.log r ^ 2 + 0.00000000000038731755
          * w * Real.log r) (by ring) ?_
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
/-- **Piece `[3.05, 3.35]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_3_05_3_35`). -/
private theorem tR2a_hi5 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.05 3.35
      (1 / Real.sqrt r * (0.05497190413800724 + Real.log r * 0.01234829386285795 + Real.log r ^ 2 *
          (-0.0001331837551790498) + Real.log r ^ 3 * 0.00004278703129040601 + Real.log r ^ 4 *
          0.0000005956469173475752) + 1 / r * (1.180122901966065 + Real.log r * 0.4282828810335843 +
          Real.log r ^ 2 * 0.007502130382728022) + 0.00000339126684862432) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.05 : ℝ) 3.35, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9357642730008103765564637611328, -0.0003728818306566195757106103504576]
        [0, 0, 0.6614885460763649003357200310073344, -0.0007220037973736185661085498649032448]
        [0, 0, -0.00625784559802466354415166792029184, -0.0002678241792665106596685813557401088]
        [0, 0, 0.002294654007724652164509724877281536, -0.000003314674125035057914536]
        [0, 0, 0.00003179756022154752994492]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.0001810368] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9357642730008103765564637611328, -0.0003728818306566195757106103504576]
        [0, 0, 0.6614885460763649003357200310073344, -0.0007220037973736185661085498649032448]
        [0, 0, -0.00625784559802466354415166792029184, -0.0002678241792665106596685813557401088]
        [0, 0, 0.002294654007724652164509724877281536, -0.000003314674125035057914536]
        [0, 0, 0.00003179756022154752994492]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.0001810368] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.161317834 + 0.3127291 * w ≤ Real.log w := log_ge_chord 3.05 3.35 w 0.161317834
        0.3127291 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL157)
        (le_trans (by norm_num) lgL159)
    have hR := rChordHi y r w 19.997138805 2.08 0.161317834 0.3127291 13.9664 14.61206 0.1658172
        0.03079191 (15809 / 11316) 0.874238158855 0.493197101 0.11316 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (15809 / 11316) = (27125 / 11316) by norm_num]; exact lgU306)
        (by norm_num) (by norm_num)
    have hRs : 0.493197101 + 0.11316 * ((2.08 + Real.log r) * (0.1658172 + 0.03079191 * (Real.log r
        - (0.161317834 + 0.3127291 * w) / 3 - 13.9664)) / 2) ≤ 0.461905383 + (-0.0114203063) *
        Real.log r + (-0.000377754761) * w + 0.00174220627 * Real.log r ^ 2 + (-0.000181612866) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000480053879428672 + 0.0000000000860788266484 * Real.log r +
          0.0000000000003794607328 * w + 0.0000000000022 * Real.log r ^ 2 + 0.00000000000004781766 *
          w * Real.log r) (by ring) ?_
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
/-- **Piece `[3.35, 3.6]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_3_35_3_6`). -/
private theorem tR2a_hi6 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.35 3.6
      (1 / Real.sqrt r * (0.02154378689108492 + Real.log r * 0.004839668923866735 + Real.log r ^ 2 *
          (-0.00005089522501205351) + Real.log r ^ 3 * 0.00001665484736163079 + Real.log r ^ 4 *
          0.0000002317681414376596) + 1 / r * (0.4625080230566466 + Real.log r * 0.1678505419103747
          + Real.log r ^ 2 * 0.002940198420222266) + 0.000001308469053932007) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.35 : ℝ) 3.6, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9356846080855481354553455133632, -0.0003408067572282384729722685740736]
        [0, 0, 0.6615004743066060865247802148852736, -0.0006598974596734788020516528260560128]
        [0, 0, -0.00608552444013283366421861903612416, -0.000244786102248467059861962686000768]
        [0, 0, 0.00227905943422003731423595382064768, -0.00000302954782307459792246]
        [0, 0, 0.0000315694202097655000246]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00017822816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9356846080855481354553455133632, -0.0003408067572282384729722685740736]
        [0, 0, 0.6615004743066060865247802148852736, -0.0006598974596734788020516528260560128]
        [0, 0, -0.00608552444013283366421861903612416, -0.000244786102248467059861962686000768]
        [0, 0, 0.00227905943422003731423595382064768, -0.00000302954782307459792246]
        [0, 0, 0.0000315694202097655000246]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00017822816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.244515779 + 0.2878939 * w ≤ Real.log w := log_ge_chord 3.35 3.6 w 0.244515779
        0.2878939 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL159)
        (le_trans (by norm_num) lgL161)
    have hR := rChordHi y r w 19.997138805 2.08 0.244515779 0.2878939 13.94241 14.58079 0.1651602
        0.03049284 (3156 / 2269) 0.871678694585 0.492792846 0.11345 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (3156 / 2269) = (5425 / 2269) by norm_num]; exact lgU307)
        (by norm_num) (by norm_num)
    have hRs : 0.492792846 + 0.11345 * ((2.08 + Real.log r) * (0.1651602 + 0.03049284 * (Real.log r
        - (0.244515779 + 0.2878939 * w) / 3 - 13.94241)) / 2) ≤ 0.461824677 + (-0.0112907537) *
        Real.log r + (-0.000345260521) * w + 0.00172970635 * Real.log r ^ 2 + (-0.000165990635) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000026836550727056 + 0.000000000011563416957 * Real.log r +
          0.000000000000956737296 * w + 0.000000000001 * Real.log r ^ 2 + 0.0000000000005561237 * w
          * Real.log r) (by ring) ?_
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
/-- **Piece `[3.6, 3.85]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_3_6_3_85`). -/
private theorem tR2a_hi7 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.6 3.85
      (1 / Real.sqrt r * (0.01011061192874945 + Real.log r * 0.00227134369295605 + Real.log r ^ 2 *
          (-0.0000233815574689524) + Real.log r ^ 3 * 0.000007772861827327067 + Real.log r ^ 4 *
          0.0000001081318585686256) + 1 / r * (0.2170628749266503 + Real.log r * 0.07877511171433193
          + Real.log r ^ 2 * 0.001379885083355787) + 0.0000006067646422105215) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.6 : ℝ) 3.85, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9356039383022000400008837920448, -0.0003160430042954052843656693261568]
        [0, 0, 0.6614880601400902241525054042709504, -0.0006119478891275658075456420126705664]
        [0, 0, -0.00594424464056093752855898229119232, -0.0002269994169116578518315223589937664]
        [0, 0, 0.002266358966428066052700272648850432, -0.000002809414354117528180408]
        [0, 0, 0.00003138341902292014717904]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00017610304] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.9356039383022000400008837920448, -0.0003160430042954052843656693261568]
        [0, 0, 0.6614880601400902241525054042709504, -0.0006119478891275658075456420126705664]
        [0, 0, -0.00594424464056093752855898229119232, -0.0002269994169116578518315223589937664]
        [0, 0, 0.002266358966428066052700272648850432, -0.000002809414354117528180408]
        [0, 0, 0.00003138341902292014717904]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00017610304] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.314127924 + 0.2685572 * w ≤ Real.log w := log_ge_chord 3.6 3.85 w 0.314127924
        0.2685572 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL161)
        (le_trans (by norm_num) lgL163)
    have hR := rChordHi y r w 19.997138805 2.08 0.314127924 0.2685572 13.92003 14.5568 0.164552
        0.03024653 (3151 / 2274) 0.869477504937 0.492445774 0.1137 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (3151 / 2274) = (5425 / 2274) by norm_num]; exact lgU308)
        (by norm_num) (by norm_num)
    have hRs : 0.492445774 + 0.1137 * ((2.08 + Real.log r) * (0.164552 + 0.03024653 * (Real.log r -
        (0.314127924 + 0.2685572 * w) / 3 - 13.92003)) / 2) ≤ 0.461742953 + (-0.0111843799) *
        Real.log r + (-0.000320173148) * w + 0.00171951524 * Real.log r ^ 2 + (-0.000153929398) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000001930790342752 + 0.000000000064458030494 * Real.log r +
          0.000000000000991234656 * w + 0.0000000000095 * Real.log r ^ 2 + 0.0000000000005534782 * w
          * Real.log r) (by ring) ?_
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
/-- **Piece `[3.85, 4.1]` (`w ≥ 1`) of region `R2a`** (`ptHiS`; moments `mom_3_85_4_1`). -/
private theorem tR2a_hi8 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.85 4.1
      (1 / Real.sqrt r * (0.004418854893156507 + Real.log r * 0.0009927255496563945 + Real.log r ^ 2
          * (-0.00001001461095682269) + Real.log r ^ 3 * 0.000003379507332613835 + Real.log r ^ 4 *
          0.00000004699970080025416) + 1 / r * (0.09486966761018597 + Real.log r *
          0.03442951111201919 + Real.log r ^ 2 * 0.000603093639308214) + 0.0000002622419466844462)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.85 : ℝ) 4.1, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.935532943088704064897226966848, -0.000294520182908018373281001856896]
        [0, 0, 0.661482116974038386616738361909504, -0.000570273670560172731250628020644608]
        [0, 0, -0.0058131589089638936761049789482368, -0.0002115405457585251384056985727997184]
        [0, 0, 0.002254542663723567597934082317117696, -0.000002618090626733041126348]
        [0, 0, 0.00003121043723107928982012]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00017414336] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.935532943088704064897226966848, -0.000294520182908018373281001856896]
        [0, 0, 0.661482116974038386616738361909504, -0.000570273670560172731250628020644608]
        [0, 0, -0.0058131589089638936761049789482368, -0.0002115405457585251384056985727997184]
        [0, 0, 0.002254542663723567597934082317117696, -0.000002618090626733041126348]
        [0, 0, 0.00003121043723107928982012]
        [0, 0, 62.9987799]
        [0, 0, 22.8631263]
        [0, 0, 0.400488]
        [0, 0, 0.00017414336] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.379200242 + 0.2516553 * w ≤ Real.log w := log_ge_chord 3.85 4.1 w 0.379200242
        0.2516553 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL163)
        (le_trans (by norm_num) lgL165)
    have hR := rChordHi y r w 19.997138805 2.08 0.379200242 0.2516553 13.89906 14.53442 0.1639861
        0.03001909 (15732 / 11393) 0.867456680892 0.492127625 0.11393 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (15732 / 11393) = (27125 / 11393) by norm_num]; exact lgU309)
        (by norm_num) (by norm_num)
    have hRs : 0.492127625 + 0.11393 * ((2.08 + Real.log r) * (0.1639861 + 0.03001909 * (Real.log r
        - (0.379200242 + 0.2516553 * w) / 3 - 13.89906)) / 2) ≤ 0.46167103 + (-0.011085716) *
        Real.log r + (-0.00029836906) * w + 0.00171003747 * Real.log r ^ 2 + (-0.000143446663) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ ((86237471939801 / 187500000000000000000000) + (1514211687677 /
          30000000000000000000000) * Real.log r + 0.0000000000000613495448 * w + 0.00000000000815 *
          Real.log r ^ 2 + 0.000000000000491033435 * w * Real.log r) (by ring) ?_
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
/-- **The Gaussian tail `w > 4.1` of region `R2a`** (`ptHiS`, `tail_of`, `intBndI_tail`). -/
private theorem tR2a_tail (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 4.1
      (1 / Real.sqrt r * (0.00301222191309297 + Real.log r * 0.0006768804599587843 + Real.log r ^ 2
          * (-0.000006748607536899082) + Real.log r ^ 3 * 0.00000229594154516809 + Real.log r ^ 4 *
          0.00000003192627419540105) + 1 / r * (0.06466837632894086 + Real.log r *
          0.02346904587630761 + Real.log r ^ 2 * 0.0004111017505471542) + 0.0000001768940587748184)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 14.36 2.66444656258 0.069187 2.67094229625 (Real.log r)
      1.7810727 0.9406719 0.20946 1.19355 0.6931471808 hr (by norm_num) (by linarith) lgL299
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL301]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.0139507 + 0.0258111436 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.9987799 + 22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((3957025784954338061 / 45000000000000000000000000) +
        (1875465055288847 / 112500000000000000000000) * Real.log r + 0.000000000091575 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Ioi (4.1 : ℝ), OC.gY (w * y) r * HW.phi w ≤ (0.70711 * (((0.460576886 +
      (-0.0115975572) * Real.log r + 0.00170409654 * Real.log r ^ 2) * (0.6931471808 + Real.log r) +
      0.5) * (2.0139507 + 0.0258111436 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (62.9987799 +
      22.8631263 * Real.log r + 0.400488 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) * (w ^ 2
      * Real.exp (-w ^ 2 / 2)) ∧ 0 ≤ (0.70711 * (((0.460576886 + (-0.0115975572) * Real.log r +
      0.00170409654 * Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (2.0139507 +
      0.0258111436 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (62.9987799 + 22.8631263 * Real.log r
      + 0.400488 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) := by
    intro w hw
    have hw' : (4.1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hτ : 1.41098697297 + 0 * w ≤ Real.log w := by
      have := Real.log_le_log (by norm_num) hw'.le
      linarith [lgL165]
    have hR := rChordHi y r w 19.997138805 2.08 1.41098697297 0 13.89906 14.51345 0.1639861
        0.0299043 (15728 / 11397) 0.867105649719 0.492072408 0.11397 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15728 / 11397) = (27125 / 11397) by norm_num]; exact lgU310)
        (by norm_num) (by norm_num)
    have hRs : 0.492072408 + 0.11397 * ((2.08 + Real.log r) * (0.1639861 + 0.0299043 * (Real.log r -
        (1.41098697297 + 0 * w) / 3 - 13.89906)) / 2) ≤ 0.460576886 + (-0.0115975572) * Real.log r +
        0.00170409654 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000004236596314075016 + 0.000000000094457899715145 * Real.log r
          + 0.0000000000045 * Real.log r ^ 2) (by ring) ?_
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
  have e : (0.70711 * (((0.460576886 + (-0.0115975572) * Real.log r + 0.00170409654 *
      Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (2.0139507 + 0.0258111436 * Real.log r)
      + 2.5) * (1 / Real.sqrt r) + (62.9987799 + 22.8631263 * Real.log r + 0.400488 *
      Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) / 4.1 * ((4.1 ^ 2 + 2) *
      0.000223745793720620415502418151611) = 1 / Real.sqrt r * (((9648523315375917955441 * 10 ^ 40 +
      4847680664544994224131981460171261485747) / (3203125000000000000000000 * 10 ^ 40 + 0)) +
      Real.log r * ((542033180826370200012553 * 10 ^ 40 + 503697837137396553432117244785534250889) /
      (800781250000000000000000000 * 10 ^ 40 + 0)) + Real.log r ^ 2 * ((-(54041583791574685546249 *
      10 ^ 40 + 5822346562686624543485916742562889595103)) / (8007812500000000000000000000 * 10 ^ 40
      + 0)) + Real.log r ^ 3 * ((183854694046663384836761 * 10 ^ 40 +
      2810456565788342317412581109598695633971) / (80078125000000000000000000000 * 10 ^ 40 + 0)) +
      Real.log r ^ 4 * ((16362215525143 * 10 ^ 40 + 336211649063530274900021874790332137093) /
      (512500000000000000000 * 10 ^ 40 + 0))) + 1 / r * ((265140342948657513452924548051307987269509
      / 4100000000000000000000000000000000000000000) + Real.log r *
      (96223088092861162625756868768619968037533 / 4100000000000000000000000000000000000000000) +
      Real.log r ^ 2 * 0.0004111017505471541031238554169785082488) +
      (113322756402617998527060230785268334951 / 640625000000000000000000000000000000000000000) :=
      by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

/-- **Region `R2a`, `w > 1`**: the 9 hi pieces and the Gaussian tail, added. -/
theorem hiR2a (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 1
      (1 / Real.sqrt r * (2.947452826356480287 + Real.log r * 0.6614051306282013838 + Real.log r ^ 2
          * (-0.008597527129146720682) + Real.log r ^ 3 * 0.002419864512379740522 + Real.log r ^ 4 *
          0.00003378629578988287161) + 1 / r * (63.26827411098012573 + Real.log r *
          22.96092946686350923 + Real.log r ^ 2 * 0.4022011950450204032) + 0.0002051380489076798421)
          := by
  have h0 := tR2a_hi0 y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR2a_hi1 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR2a_hi2 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR2a_hi3 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR2a_hi4 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR2a_hi5 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR2a_hi6 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR2a_hi7 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR2a_hi8 y r hy hr0 hr1)
  have ht := intBndI_add _ _ _ _ _ h8 (tR2a_tail y r hy hr0 hr1)
  exact intBndI_mono _ _ _ _ ht (le_of_eq (by ring))

/-- **THE REGION ENVELOPE `R2a`**: `g̃(y, r) ≤ P(ℓ)/√r + Q(ℓ)/r + z` on `r ∈ [1740000, 3216400]`, `y
    ≥ (10 ^ 25)` (`gT_le_of` over `loR2a`, `hiR2a` and the sliver, divided by `|φ|₁ ≥
    1.2533139`). -/
theorem envR2a (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    OC.gT HW.phi y r ≤ envF 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 r := by
  have hr : 0 < r := by linarith
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨hy1, -, -⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  refine (gT_le_of y r _ _ _ hy1 hr (loR2a y r hy hr0 hr1) (hiR2a y r hy hr0 hr1)
    (sliver_bnd r 1740000 0.000110098207602 (by norm_num) hr0 (by norm_num))).trans ?_
  rw [div_le_iff₀ (by norm_num), envF_eq]
  have hX : 0 ≤ 1 / Real.sqrt r := one_div_nonneg.mpr (Real.sqrt_nonneg r)
  have hZ : 0 ≤ 1 / r := one_div_nonneg.mpr hr.le
  linarith [hX, hZ, mul_nonneg hX (pow_nonneg hl0 1), mul_nonneg hX (pow_nonneg hl0 2),
      mul_nonneg hX (pow_nonneg hl0 3), mul_nonneg hX (pow_nonneg hl0 4),
      mul_nonneg hZ (pow_nonneg hl0 1), mul_nonneg hZ (pow_nonneg hl0 2)]

/-- **The region envelope `R2a` is `≥ 0`** (so its antiderivative `envG` increases). -/
theorem envR2a_pos (r : ℝ) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    0 ≤ envF 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466 0.0000353941790317
        66.1586347438 25.2980058133 0.452552670596 0.000210527045125 r := by
  have hr : 0 < r := by linarith
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hl0 : 0 ≤ Real.log r := by linarith
  refine envF_nonneg _ _ _ _ _ _ _ _ _ r hr ?_ ?_ ?_
  · have := tm_ge_pos 0.688720800761 14.3693956657 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_neg (-0.00919198398172) 14.983773285 (Real.log r) 2 (by norm_num) hl0 hlb
    have := tm_ge_pos 0.00249610521466 14.3693956657 (Real.log r) 3 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.0000353941790317 14.3693956657 (Real.log r) 4 (by norm_num) (by norm_num)
        hla
    linarith
  · have := tm_ge_pos 25.2980058133 14.3693956657 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.452552670596 14.3693956657 (Real.log r) 2 (by norm_num) (by norm_num) hla
    linarith
  · norm_num

end Principia.Common.TernaryGoldbach.MC
