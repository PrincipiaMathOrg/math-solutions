/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCRFLo

set_option autoImplicit false

/-!
# Region `RF` of `g̃`, `w > 1`, and the region envelope

GENERATED. The 9 pieces on `1, 1.5, 2, 2.4, 2.75, 3.05, 3.35, 3.6, 3.85, 4.1` and the Gaussian tail
    `w > 4.1` (`hiRF`), then **`envRF`**: `gT(y, r) ≤ envF … r` for `r ∈ [5940000, r₁(y)]`, `y ≥
    (10 ^ 27)`, from `gT_le_of`, and `envRF_pos`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[1, 1.5]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_1_1_5`). -/
private theorem tRF_hi0 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1 1.5
      (1 / Real.sqrt r * (1.131944987257892 + Real.log r * 0.3754150344816181 + Real.log r ^ 2 *
          0.003797462160088821 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (22.99214236531117 + Real.log r * 8.237520140819333 + Real.log r ^ 2 * 0.1184470830110146)
          + 1.119298830236726 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1 : ℝ) 1.5, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.2 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 3.2 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (1 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 1 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 1 hy0 (by norm_num)))
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
/-- **Piece `[1.5, 2]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_1_5_2`). -/
private theorem tRF_hi1 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1.5 2
      (1 / Real.sqrt r * (1.057390284130709 + Real.log r * 0.3506886062891483 + Real.log r ^ 2 *
          0.003547345178107229 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (21.47778224392731 + Real.log r * 7.694962087630959 + Real.log r ^ 2 * 0.1106456551946687)
          + 0.9772548695133983 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1.5 : ℝ) 2, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.9908992 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.9908992 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.934656 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 1.5 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.934656 hy0 (by norm_num)))
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
/-- **Piece `[2, 2.4]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_2_2_4`). -/
private theorem tRF_hi2 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2 2.4
      (1 / Real.sqrt r * (0.5579942145668326 + Real.log r * 0.1850614823690412 + Real.log r ^ 2 *
          0.001871965456995539 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (11.33401584419726 + Real.log r * 4.0606996211802 + Real.log r ^ 2 * 0.05838869185027411)
          + 0.4915626726638498 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2 : ℝ) 2.4, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.8508768 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.8508768 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.890899 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 2 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.890899 hy0 (by norm_num)))
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
/-- **Piece `[2.4, 2.75]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_2_4_2_75`). -/
private theorem tRF_hi3 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.4 2.75
      (1 / Real.sqrt r * (0.2754564557434145 + Real.log r * 0.09135646696188614 + Real.log r ^ 2 *
          0.0009241045096827469 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (5.5950899709702 + Real.log r * 2.004583374322696 + Real.log r ^ 2 * 0.02882385102335953)
          + 0.2353994994302728 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.4 : ℝ) 2.75, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.765552 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.765552 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.864235 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 2.4 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.864235 hy0 (by norm_num)))
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
/-- **Piece `[2.75, 3.05]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_2_75_3_05`). -/
private theorem tRF_hi4 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.75 3.05
      (1 / Real.sqrt r * (0.1234871254051447 + Real.log r * 0.04095510291035574 + Real.log r ^ 2 *
          0.0004142760392624464 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (2.508278758737288 + Real.log r * 0.8986546997491197 + Real.log r ^ 2 *
          0.01292173202611863) + 0.1031621718335899 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.75 : ℝ) 3.05, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.7035104 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.7035104 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.844847 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 2.75 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.844847 hy0 (by norm_num)))
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
/-- **Piece `[3.05, 3.35]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_3_05_3_35`). -/
private theorem tRF_hi5 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.05 3.35
      (1 / Real.sqrt r * (0.06062117487710301 + Real.log r * 0.02010530609966722 + Real.log r ^ 2 *
          0.0002033726199482499 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (1.231341362713438 + Real.log r * 0.4411593802097871 + Real.log r ^ 2 *
          0.006343418994493533) + 0.04977700449375498 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.05 : ℝ) 3.35, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.6572576 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.6572576 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.830393 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 3.05 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.830393 hy0 (by norm_num)))
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
/-- **Piece `[3.35, 3.6]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_3_35_3_6`). -/
private theorem tRF_hi6 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.35 3.6
      (1 / Real.sqrt r * (0.0237583557619886 + Real.log r * 0.007879573696615892 + Real.log r ^ 2 *
          0.00007970480721915566 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (0.4825813128680775 + Real.log r * 0.1728970367864206 + Real.log r ^ 2 *
          0.002486081893398888) + 0.01920567843484936 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.35 : ℝ) 3.6, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.6160288 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.6160288 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.817509 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 3.35 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.817509 hy0 (by norm_num)))
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
/-- **Piece `[3.6, 3.85]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_3_6_3_85`). -/
private theorem tRF_hi7 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.6 3.85
      (1 / Real.sqrt r * (0.01115020010062782 + Real.log r * 0.003698017838653534 + Real.log r ^ 2 *
          0.00003740682050470159 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (0.2264836109539071 + Real.log r * 0.081143517518101 + Real.log r ^ 2 *
          0.00116676048021368) + 0.008906084454578506 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.6 : ℝ) 3.85, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.5848384 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.5848384 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.807762 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 3.6 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.807762 hy0 (by norm_num)))
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
/-- **Piece `[3.85, 4.1]` (`w ≥ 1`) of region `RF`** (`ptHiS`; moments `mom_3_85_4_1`). -/
private theorem tRF_hi8 (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.85 4.1
      (1 / Real.sqrt r * (0.004873315059938643 + Real.log r * 0.001616258530106317 + Real.log r ^ 2
          * 0.00001634905383444372 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (0.09898710176769062 + Real.log r * 0.03546464838017495 + Real.log r ^ 2 *
          0.0005099452358031152) + 0.003849183320757796 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.85 : ℝ) 4.1, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.5560736 * y ^ (-(1 : ℝ) / 6)] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 3.2361545115339527917134848]
        [0, 0, 1.073286309150438238400666624]
        [0, 0, 0.01085668865544528]
        [0]
        [0]
        [0, 0, 65.7329871]
        [0, 0, 23.5505155]
        [0, 0, 0.338632236]
        [0 * y ^ (-(1 : ℝ) / 6), 0 * y ^ (-(1 : ℝ) / 6), 2.5560736 * y ^ (-(1 : ℝ) / 6)] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (le_trans (by norm_num) hw.1)
        hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.798773 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 3.85 y (by norm_num) hw.1 hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.798773 hy0 (by norm_num)))
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
/-- **The Gaussian tail `w > 4.1` of region `RF`** (`ptHiS`, `tail_of`, `intBndI_tail`). -/
private theorem tRF_tail (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 4.1
      (1 / Real.sqrt r * (0.003321919220382829 + Real.log r * 0.001101730590005292 + Real.log r ^ 2
          * 0.00001114441309452215 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (0.06747504560811685 + Real.log r * 0.02417465229504477 + Real.log r ^ 2 *
          0.0003476066823757442) + 0.002596445766598694 * y ^ (-(1 : ℝ) / 6)) := by
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 15.59 2.74662968202 0.058501 2.83871143187 (Real.log r)
      1.7810727 0.91252564 0.20466 1.22154 0.6931471808 hr (by norm_num) (by linarith) lgL385
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL387]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.07853418 + 0.0213244534 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((212669528751133458611 / 5625000000000000000000000000) +
        (15933134719181 / 112500000000000000000000) * Real.log r + 0.000000000426225 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Ioi (4.1 : ℝ), OC.gY (w * y) r * HW.phi w ≤ (0.70711 * (((0.72) *
      (0.6931471808 + Real.log r) + 0.5) * (2.07853418 + 0.0213244534 * Real.log r) + 2.5) * (1 /
      Real.sqrt r) + (65.7329871 + 23.5505155 * Real.log r + 0.338632236 * Real.log r ^ 2) * (1 / r)
      + 3.2 * (0.790441 * y ^ (-(1 : ℝ) / 6))) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) ∧ 0 ≤ (0.70711 *
      (((0.72) * (0.6931471808 + Real.log r) + 0.5) * (2.07853418 + 0.0213244534 * Real.log r) +
      2.5) * (1 / Real.sqrt r) + (65.7329871 + 23.5505155 * Real.log r + 0.338632236 *
      Real.log r ^ 2) * (1 / r) + 3.2 * (0.790441 * y ^ (-(1 : ℝ) / 6))) := by
    intro w hw
    have hw' : (4.1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hR := rFarHi y r w (le_trans (by norm_num) hy) (by linarith) (by linarith) hr1
    have hRb := hR.2
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ (0.790441 * y ^ (-(1 : ℝ) / 6)) :=
      (wy_rpow_le w y 4.1 y (by norm_num) hw'.le hy0 le_rfl).trans
        (rpow_neg6_le _ _ (by positivity) (by positivity)
          (yb_far y _ 0.790441 hy0 (by norm_num)))
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
  have e : (0.70711 * (((0.72) * (0.6931471808 + Real.log r) + 0.5) * (2.07853418 + 0.0213244534 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + (65.7329871 + 23.5505155 * Real.log r + 0.338632236 *
      Real.log r ^ 2) * (1 / r) + 3.2 * (0.790441 * y ^ (-(1 : ℝ) / 6))) / 4.1 * ((4.1 ^ 2 + 2) *
      0.000223745793720620415502418151611) = 1 / Real.sqrt r * (((1330065312848593 * 10 ^ 40 +
      6184513700869005218069140354672494748907) / (400390625000000000 * 10 ^ 40 + 0)) + Real.log r *
      ((44112259951383741 * 10 ^ 40 + 5692255943393727188231812770936936931941) /
      (40039062500000000000 * 10 ^ 40 + 0)) + Real.log r ^ 2 * ((2855755 * 10 ^ 40 +
      8554712987442446623825308758341287031103) / (256250000000 * 10 ^ 40 + 0)) + Real.log r ^ 3 * 0
      + Real.log r ^ 4 * 0) + 1 / r * ((276647686993279060220643507642438612772461 /
      4100000000000000000000000000000000000000000) + Real.log r *
      (19823214881936703903576894793839724980021 / 820000000000000000000000000000000000000000) +
      Real.log r ^ 2 * (35629684943513773898803681611421123115169 /
      102500000000000000000000000000000000000000000)) + (332669613845457654000126330519972398331 /
      128125000000000000000000000000000000000000) * y ^ (-(1 : ℝ) / 6) := by
    ring
  refine le_trans (le_of_eq e) ?_
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

/-- **Region `RF`, `w > 1`**: the 9 hi pieces and the Gaussian tail, added. -/
theorem hiRF (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 1
      (1 / Real.sqrt r * (3.249998032124033702 + Real.log r * 1.077877579767097735 + Real.log r ^ 2
          * 0.01090313105873785532 + Real.log r ^ 3 * 0 + Real.log r ^ 4 * 0) + 1 / r *
          (66.01417761705445807 + Real.log r * 23.65125915889183612 + Real.log r ^ 2 *
          0.3400808263917205304) + 3.011012440148376136 * y ^ (-(1 : ℝ) / 6)) := by
  have h0 := tRF_hi0 y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tRF_hi1 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tRF_hi2 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tRF_hi3 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tRF_hi4 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tRF_hi5 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tRF_hi6 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tRF_hi7 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tRF_hi8 y r hy hr0 hr1)
  have ht := intBndI_add _ _ _ _ _ h8 (tRF_tail y r hy hr0 hr1)
  exact intBndI_mono _ _ _ _ ht (le_of_eq (by ring))

/-- **THE REGION ENVELOPE `RF`**: `g̃(y, r) ≤ P(ℓ)/√r + Q(ℓ)/r + z` on `r ∈ [5940000, r₁(y)]`, `y ≥
    (10 ^ 27)` (`gT_le_of` over `loRF`, `hiRF` and the sliver, divided by `|φ|₁ ≥ 1.2533139`). -/
theorem envRF (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    OC.gT HW.phi y r ≤ envF 3.26627202061 1.1187151769 0.0114351675071 0 0 69.1334855631
        26.1029979906 0.381494368499 (3.09852175891 * y ^ (-(1 : ℝ) / 6)) r := by
  have hr : 0 < r := by linarith
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨hy1, -, -⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  refine (gT_le_of y r _ _ _ hy1 hr (loRF y r hy hr0 hr1) (hiRF y r hy hr0 hr1)
    (sliver_bnd r 5940000 0.00000944725972785 (by norm_num) hr0 (by norm_num))).trans ?_
  rw [div_le_iff₀ (by norm_num), envF_eq]
  have hX : 0 ≤ 1 / Real.sqrt r := one_div_nonneg.mpr (Real.sqrt_nonneg r)
  have hZ : 0 ≤ 1 / r := one_div_nonneg.mpr hr.le
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
  linarith [hX, hZ, mul_nonneg hX (pow_nonneg hl0 1), mul_nonneg hX (pow_nonneg hl0 2),
      mul_nonneg hX (pow_nonneg hl0 3), mul_nonneg hX (pow_nonneg hl0 4),
      mul_nonneg hZ (pow_nonneg hl0 1), mul_nonneg hZ (pow_nonneg hl0 2), hY6]

/-- **The region envelope `RF` is `≥ 0`** (so its antiderivative `envG` increases). -/
theorem envRF_pos (y r : ℝ) (hy : 0 < y) (hr0 : 5940000 ≤ r) :
    0 ≤ envF 3.26627202061 1.1187151769 0.0114351675071 0 0 69.1334855631 26.1029979906
        0.381494368499 (3.09852175891 * y ^ (-(1 : ℝ) / 6)) r := by
  have hr : 0 < r := by linarith
  have hla : 15.5972196853 ≤ Real.log r := lgL9.trans (Real.log_le_log (by norm_num) hr0)
  have hl0 : 0 ≤ Real.log r := by linarith
  refine envF_nonneg _ _ _ _ _ _ _ _ _ r hr ?_ ?_ ?_
  · have := tm_ge_pos 1.1187151769 15.5972196853 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.0114351675071 15.5972196853 (Real.log r) 2 (by norm_num) (by norm_num) hla
    linarith
  · have := tm_ge_pos 26.1029979906 15.5972196853 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.381494368499 15.5972196853 (Real.log r) 2 (by norm_num) (by norm_num) hla
    linarith
  · positivity

end Principia.Common.TernaryGoldbach.MC
