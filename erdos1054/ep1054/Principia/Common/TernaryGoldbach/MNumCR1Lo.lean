/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCData

set_option autoImplicit false

/-!
# Region `R1` of `g̃`, `w ≤ 1`: `r ∈ [520000, 1740000]`, `y ≥ (10 ^ 25)`

GENERATED. The first piece `[w₁, 0.04]` and 8 pieces on the grid `0.04, 0.09, 0.16, 0.25, 0.36,
    0.49, 0.64, 0.81, 1` of the `w ≤ 1` integral of `gT`, each a certified majorant `(P(w, ℓ)/√r +
    Q(w, ℓ)/r + Y(w))e^{−w²/2}` integrated against the moments of `MNumCData`; their sum is `loR1`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **The first piece `[w₁, 0.04]` of region `R1`** (`ptFirstS`, `intBnd_lin`). -/
private theorem tR1_first (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 0.04
      (1 / Real.sqrt r * (0.0001528648417303324 + Real.log r * 0.00009118214698253383 +
          Real.log r ^ 2 * 0.0000003387606621313101 + Real.log r ^ 3 * 0.0000001703098510142038 +
          Real.log r ^ 4 * 0.000000005391574705639507) + 1 / r * ((-0.004949182512) + Real.log r *
          0.01433475296 + Real.log r ^ 2 * 0.000512859884) + 0.000000174411008) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  obtain ⟨-, hm0, hm1⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  have key : ∀ w ∈ Set.Icc (max (1 / kK y) (1000 / r)) 0.04, OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * 0.2 * (((0.457146996 + (-0.00720270656) * Real.log r + 0.00110356481 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.75497666 + 0.0431828023 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.18647814) + 17.9184412 * Real.log r +
      0.641074855 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000681293) * w ∧ 0 ≤ (0.70711 * 0.2 *
      (((0.457146996 + (-0.00720270656) * Real.log r + 0.00110356481 * Real.log r ^ 2) *
      ((-2.52572864) + Real.log r) + 0.5) * (1.75497666 + 0.0431828023 * Real.log r) + 2.5) * (1 /
      Real.sqrt r) + ((-6.18647814) + 17.9184412 * Real.log r + 0.641074855 * Real.log r ^ 2) * (1 /
      r) + 3.2 * 0.0000681293) := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) ((le_max_right _ _).trans hw.1)
    have hwr1 := wr_ge y r w hr hw.1
    have hw1 : w ≤ 1 := le_trans hw.2 (by norm_num)
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hτ : Real.log w ≤ (-3.21887582356) + 0 * w := by
      have := Real.log_le_log hw0 hw.2
      linarith [lgU11]
    have hR := rChordLo y r w 19.997138805 2.08 (-3.21887582356) 0 11.01566 12.22348 0.1113403
        0.01432271 (2343 / 3082) 0.56543916286 0.450375373 0.1541 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (2343 / 3082) = (5425 / 3082) by norm_num]; exact lgU168)
        (by norm_num) (by norm_num)
    have hRs : 0.450375373 + 0.1541 * ((2.08 + Real.log r + ((-3.21887582356) + 0 * w)) * (0.1113403
        + 0.01432271 * (Real.log r + 2 / 3 * ((-3.21887582356) + 0 * w) - 11.01566)) / 2) ≤
        0.457146996 + (-0.00720270656) * Real.log r + 0.00110356481 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000002768621294064954554998768 + (55206085879 /
          30000000000000000000000) * Real.log r + 0.0000000000045 * Real.log r ^ 2) (by ring) ?_
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hRb := hR.2.trans hRs
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
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 6.907 1.93253538928 0.11075 2.20047987095
        (Real.log r + (-3.21887582356)) 1.7810727 1.2969336 0.21892 1.14197 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL14 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL170]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.75497666 + 0.0431828023 * Real.log r := hS.trans
        (by linarith)
    have hLs : lL (w * r) ≤ (-6.18647814) + 17.9184412 * Real.log r + 0.641074855 * Real.log r ^ 2
        := by
      refine hLL.trans (le_of_sub_eq _ _ ((648771313227264353927621 /
          300000000000000000000000000000000) + (1434733612334513 / 18000000000000000000000) *
          Real.log r + 0.00000000004375 * Real.log r ^ 2) (by ring) ?_)
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ 0.0000681293 :=
      (wy_rpow_w_le w y (10 ^ 25) hw0 hw1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    exact ptFirstS y r w 0.2 _ _ _ _ _ hy0 hr hw0 hsp hR.1 hRb hL0 hL hSs hLL0 hLs hY
  have hC0 := (key 0.04 ⟨hm1, le_rfl⟩).2
  refine intBnd_mono _ _ _ _ _ (intBnd_lin _ _ 0.04 _ hm0 hm1 hC0 (fun w hw => (key w hw).1)) ?_
  have e : (0.70711 * 0.2 * (((0.457146996 + (-0.00720270656) * Real.log r + 0.00110356481 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.75497666 + 0.0431828023 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.18647814) + 17.9184412 * Real.log r +
      0.641074855 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000681293) * (0.04 ^ 2 / 2) = 1 / Real.sqrt
      r * (0.00015286484173033231413091277725696 + Real.log r *
      0.0000911821469825338246764972503109632 + Real.log r ^ 2 *
      0.000000338760662131310056077647573573632 + Real.log r ^ 3 *
      0.000000170309851014203731211273751917568 + Real.log r ^ 4 *
      0.0000000053915747056395063868688) + 1 / r * ((-0.004949182512) + Real.log r * 0.01433475296 +
      Real.log r ^ 2 * 0.000512859884) + 0.000000174411008 := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.04, 0.09]` of region `R1`** (`ptLoS`; moments `mom_0_04_0_09`). -/
private theorem tR1_lo0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.04 0.09
      (1 / Real.sqrt r * (0.001198555263016161 + Real.log r * 0.0005747945100836321 + Real.log r ^ 2
          * (-0.0000004983002007278606) + Real.log r ^ 3 * 0.000001206641578358823 + Real.log r ^ 4
          * 0.00000002718147763687164) + 1 / r * (0.01291950556142752 + Real.log r *
          0.06268334298049363 + Real.log r ^ 2 * 0.001707724065737899) + 0.00000008242133311787962)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.04 : ℝ) 0.09, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.04156132804413428773079792555234375, -115.498976859719490105729460281137578125,
          1301.334805284581782276291816453076737655, 26774.122030836400749114557490106719060631,
          -764392.646611116225909923818469277252482264, 5252820.0523598420315030256150839665472163,
          -559741.8513789564863032655388444528675404, 1406509.03994293161730900056352418995594,
          667419.960380511970694231770224]
        [0, 0, 7.48265809524216484755667882368547265625,
          -250.6031166985721691129210980133649546875, 5659.43560385468966176888768689948464582745,
          -67959.98593445772809764728406775139697410068,
          341222.2532320519554389932905127210571989666,
          -120070.664922878736101327958708263205684268, 311617.46977544931153013409298866030868716,
          187711.864179026692053303500860536]
        [0, 0, -0.0509915051346063707605145985593874609375,
          2.29155853277833793484179757960849609375, -57.521176895996637337754406557152988629638,
          884.145617125014300430216753872435354631, -7159.5924491994027914122557207360915126868,
          21665.17652231471478925352213319529873944, 19553.31922604492047160986117317]
        [0, 0, 0.0141530962042754455634438269640653125, -0.45112156835602824342712283109384375,
          9.926545321630352181874004576011872792144, -110.8807012595061288318209227162248978928,
          429.9238236345026164901893745990630005984, 896.19379996673973431961554546064]
        [0, 0, 0.000351959747258352274591921875, -0.0117319915752784091530640625,
          0.2639698105867827699092401083064, -3.14249773622721711059151020968,
          15.27603072021761189574653713104]
        [0, -16.509575, 290.953657, 134.842649]
        [0, 18.1846036, 16.8553312]
        [0, 0.526729098]
        [0, 0, 0.0003728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.04156132804413428773079792555234375, -115.498976859719490105729460281137578125,
          1301.334805284581782276291816453076737655, 26774.122030836400749114557490106719060631,
          -764392.646611116225909923818469277252482264, 5252820.0523598420315030256150839665472163,
          -559741.8513789564863032655388444528675404, 1406509.03994293161730900056352418995594,
          667419.960380511970694231770224]
        [0, 0, 7.48265809524216484755667882368547265625,
          -250.6031166985721691129210980133649546875, 5659.43560385468966176888768689948464582745,
          -67959.98593445772809764728406775139697410068,
          341222.2532320519554389932905127210571989666,
          -120070.664922878736101327958708263205684268, 311617.46977544931153013409298866030868716,
          187711.864179026692053303500860536]
        [0, 0, -0.0509915051346063707605145985593874609375,
          2.29155853277833793484179757960849609375, -57.521176895996637337754406557152988629638,
          884.145617125014300430216753872435354631, -7159.5924491994027914122557207360915126868,
          21665.17652231471478925352213319529873944, 19553.31922604492047160986117317]
        [0, 0, 0.0141530962042754455634438269640653125, -0.45112156835602824342712283109384375,
          9.926545321630352181874004576011872792144, -110.8807012595061288318209227162248978928,
          429.9238236345026164901893745990630005984, 896.19379996673973431961554546064]
        [0, 0, 0.000351959747258352274591921875, -0.0117319915752784091530640625,
          0.2639698105867827699092401083064, -3.14249773622721711059151020968,
          15.27603072021761189574653713104]
        [0, -16.509575, 290.953657, 134.842649]
        [0, 18.1846036, 16.8553312]
        [0, 0.526729098]
        [0, 0, 0.0003728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.04 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.0625 (-2.7725887212) hw0 (by norm_num) lgU172
    have hτ1 : w / 0.0625 ≤ 16 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.7725887212) + 16 * w := by linarith
    have hwa : Real.log 0.04 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.7725887212) 16 11.07319 12.81434 0.1120581
        0.01560084 (12308 / 14817) 0.604680642146 0.455089625 0.14817 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12308 / 14817) = (27125 / 14817) by norm_num]; exact lgU173)
        (by norm_num) (by norm_num)
    have hRs : 0.455089625 + 0.14817 * ((2.08 + Real.log r + ((-3.7725887212) + 16 * w)) *
        (0.1120581 + 0.01560084 * (Real.log r + 2 / 3 * ((-3.7725887212) + 16 * w) - 11.07319)) / 2)
        ≤ 0.467620391 + (-0.00935958823) * Real.log r + (-0.139319949) * w + 0.00115578824 *
        Real.log r ^ 2 + 0.0308210196 * w * Real.log r + 0.197254525 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.000000000035419905122987856565056 + 0.0000000000060363921428 *
          Real.log r + 0.00000000077891115062784 * w + 0.0000000000086 * Real.log r ^ 2 +
          0.000000000096 * w * Real.log r + 0.0000000001744 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 9.942 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL20]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 9.942 2.2967682067 0.090996 2.39693973043
        (Real.log r + (-3.7725887212) + 16 * w) 1.7810727 1.0912595 0.21595 1.15768 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL174 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL176]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.79859486 + 0.0349991227 * Real.log r + 0.559985962 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-16.509575) + 18.1846036 * Real.log r + 290.953657 * w + 0.526729098 *
        Real.log r ^ 2 + 16.8553312 * w * Real.log r + 134.842649 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((765141700471273143890519 /
          22500000000000000000000000000000) + (821029382644753 / 14062500000000000000000) *
          Real.log r + (293685632644753 / 878906250000000000000) * w + 0.0000000009201 *
          Real.log r ^ 2 + 0.0000000934432 * w * Real.log r + 0.0000001475456 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0001165 :=
      (wy_rpow_le w y 0.04 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.09, 0.16]` of region `R1`** (`ptLoS`; moments `mom_0_09_0_16`). -/
private theorem tR1_lo1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.09 0.16
      (1 / Real.sqrt r * (0.005042430079833408 + Real.log r * 0.001955226166481382 + Real.log r ^ 2
          * (-0.000003895310808847892) + Real.log r ^ 3 * 0.000004469604592080833 + Real.log r ^ 4 *
          0.00000008939774476799142) + 1 / r * (0.1443588647234835 + Real.log r * 0.1757373187973268
          + Real.log r ^ 2 * 0.00430629780030476) + 0.0000003623034305062087) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.09 : ℝ) 0.16, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.750436539684482784518426503765625, -72.78716134894270445987920192218324168,
          523.7097103660060410967571230276296937936, 182.00108721790291107446129038901527236544,
          -20139.11023440751472097831155780468616508864,
          73103.1071385331411806418297945817972294976, -5742.984011748332733230149049646237768704,
          5590.583962822143824261904358450823847936, 1172.8364508306246797992492560778351104]
        [0, 0, 5.1599627067962846245671033443021015625, -77.00021723494988221123720870588287891756,
          774.286822601234211507789972177581042672308,
          -4150.480394291498119661275868344188530965592,
          9406.79543922626893954191535601663954208788, -2144.4819565903810113754948597197274083716,
          2420.5910355759643112350020673552140468048, 646.52603812262214105495374584361775072]
        [0, 0, -0.041507615604670945070364922981215, 0.8453610758553510090394875699928515154848,
          -9.485161012413845821450507929768379223248, 65.519413812736405839111245096977905184,
          -239.37209482278997171230597081398645912752, 329.1443533901135688819730674108061050384,
          131.99905482837040908265756703041959696]
        [0, 0, 0.010785192650687925117490914998115, -0.1527786511960749993941843227818428742528,
          1.494073290452364154913761770339371843072, -7.41667136341312169041990549877346293056,
          12.77629836835327197402751589561766893952, 11.857914079453738179715722365441824128]
        [0, 0, 0.00023392975449347913847725, -0.00346562597031598088472568168512,
          0.0346562599883313190869266237568, -0.183366454564872322081556216544,
          0.396162095677760136830117923008]
        [0, -4.03103635, 156.858654, 33.0735985]
        [0, 19.2151835, 8.10303093]
        [0, 0.496310602]
        [0, 0, 0.0003256704] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.750436539684482784518426503765625, -72.78716134894270445987920192218324168,
          523.7097103660060410967571230276296937936, 182.00108721790291107446129038901527236544,
          -20139.11023440751472097831155780468616508864,
          73103.1071385331411806418297945817972294976, -5742.984011748332733230149049646237768704,
          5590.583962822143824261904358450823847936, 1172.8364508306246797992492560778351104]
        [0, 0, 5.1599627067962846245671033443021015625, -77.00021723494988221123720870588287891756,
          774.286822601234211507789972177581042672308,
          -4150.480394291498119661275868344188530965592,
          9406.79543922626893954191535601663954208788, -2144.4819565903810113754948597197274083716,
          2420.5910355759643112350020673552140468048, 646.52603812262214105495374584361775072]
        [0, 0, -0.041507615604670945070364922981215, 0.8453610758553510090394875699928515154848,
          -9.485161012413845821450507929768379223248, 65.519413812736405839111245096977905184,
          -239.37209482278997171230597081398645912752, 329.1443533901135688819730674108061050384,
          131.99905482837040908265756703041959696]
        [0, 0, 0.010785192650687925117490914998115, -0.1527786511960749993941843227818428742528,
          1.494073290452364154913761770339371843072, -7.41667136341312169041990549877346293056,
          12.77629836835327197402751589561766893952, 11.857914079453738179715722365441824128]
        [0, 0, 0.00023392975449347913847725, -0.00346562597031598088472568168512,
          0.0346562599883313190869266237568, -0.183366454564872322081556216544,
          0.396162095677760136830117923008]
        [0, -4.03103635, 156.858654, 33.0735985]
        [0, 19.2151835, 8.10303093]
        [0, 0.496310602]
        [0, 0, 0.0003256704] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.09 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.1225 (-2.09964424815) hw0 (by norm_num) lgU178
    have hτ1 : w / 0.1225 ≤ 8.163266 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.09964424815) + 8.163266 * w := by linarith
    have hwa : Real.log 0.09 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.09964424815) 8.163266 11.58495 13.17372
        0.1188752 0.0174216 (2599 / 2826) 0.652155615605 0.461097211 0.1413 hy0 hr hw0 (by linarith)
        hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (2599 / 2826) = (5425 / 2826) by norm_num]; exact lgU179)
        (by norm_num) (by norm_num)
    have hRs : 0.461097211 + 0.1413 * ((2.08 + Real.log r + ((-3.09964424815) + 8.163266 * w)) *
        (0.1188752 + 0.0174216 * (Real.log r + 2 / 3 * ((-3.09964424815) + 8.163266 * w) -
        11.58495)) / 2) ≤ 0.46966638 + (-0.00965909189) * Real.log r + (-0.0754347296) * w +
        0.00123083604 * Real.log r ^ 2 + 0.01674607 * w * Real.log r + 0.0546810496 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000002230861563907139084354 + 0.00000000000140087221 *
          Real.log r + 0.000000000038076353959390288 * w + 0.0000000000051556 * w * Real.log r +
          0.00000000007098661367584 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 10.75 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL36]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 10.75 2.3749057537 0.085741 2.4564241557
        (Real.log r + (-3.09964424815) + 8.163266 * w) 1.7810727 1.0553556 0.21456 1.16518
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL180 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL182]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.84662327 + 0.0327656624 * Real.log r + 0.267474818 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-4.03103635) + 19.2151835 * Real.log r + 156.858654 * w + 0.496310602 *
        Real.log r ^ 2 + 8.10303093 * w * Real.log r + 33.0735985 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((372098237094552614032983739 /
          48000000000000000000000000000000000) + (109303860009935269 / 3600000000000000000000000) *
          Real.log r + (177378442043932121814277 / 1800000000000000000000000000000) * w +
          0.000000000295225 * Real.log r ^ 2 + 0.0000000093277364097 * w * Real.log r +
          0.0000000941637067451330401 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.000101772 :=
      (wy_rpow_le w y 0.09 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.16, 0.25]` of region `R1`** (`ptLoS`; moments `mom_0_16_0_25`). -/
private theorem tR1_lo2 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.16 0.25
      (1 / Real.sqrt r * (0.01566873432528158 + Real.log r * 0.005238061274922065 + Real.log r ^ 2 *
          (-0.00001279164931351095) + Real.log r ^ 3 * 0.00001280756543116247 + Real.log r ^ 4 *
          0.0000002356270969169681) + 1 / r * (0.4847885386050387 + Real.log r * 0.3773049873415658
          + Real.log r ^ 2 * 0.008589001906263187) + 0.000001111617854968913) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.16 : ℝ) 0.25, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.631529490633866208513803451304296875, -44.09412179971515244930094125454278515815,
          194.57321096730384691098347781460892741972,
          -144.5283280738989930002449474548244616557305,
          -1462.218999912019976819216134158580257657904,
          3425.99925824835444399983790189802412100962, -197.56443154318417376743014340292312098788,
          102.7953852207511155532637391588179575873, 11.82845783117503999966057137545305184]
        [0, 0, 3.95261773892389389276490940884828125, -33.2389230634337222022470391191996381146725,
          188.2683978134610197691730453100335616547936,
          -569.4930894918471679100565397822966933443384,
          734.28956545265310419975683073460839883084, -115.725049557488955381876779314804212149868,
          73.48712187673436928492758232530636475648, 10.778681365965833693706559978590067584]
        [0, 0, -0.0346600874501263519134500031849706640625,
          0.40391603136110699532909638673992341936629, -2.562251370421334768084150570290066360212,
          10.0510536225154217038957026318138761827868, -20.925526097058127254390043316584846925192,
          16.51784545265815722111844767817425748099, 3.637804673295418857543439415644724512]
        [0, 0, 0.00889636066484136295449219124259126953125,
          -0.07095002728940985926490326775120598551904, 0.3904643112965916611720414892213250434668,
          -1.0917633909341952601814718968458007102328, 1.063788780218556750902708460881089196478,
          0.5402139505363297325115745808962687424]
        [0, 0, 0.000175971280536189054781224609375, -0.001466427336371459652787525775776,
          0.00824865379569177662138341853572, -0.02454956478504736944260928141032,
          0.0298345407479287825790098990042]
        [0, 5.8665821, 98.4043996, 11.6052773]
        [0, 19.9268894, 4.7001369]
        [0, 0.475888823]
        [0, 0, 0.00029588992] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.631529490633866208513803451304296875, -44.09412179971515244930094125454278515815,
          194.57321096730384691098347781460892741972,
          -144.5283280738989930002449474548244616557305,
          -1462.218999912019976819216134158580257657904,
          3425.99925824835444399983790189802412100962, -197.56443154318417376743014340292312098788,
          102.7953852207511155532637391588179575873, 11.82845783117503999966057137545305184]
        [0, 0, 3.95261773892389389276490940884828125, -33.2389230634337222022470391191996381146725,
          188.2683978134610197691730453100335616547936,
          -569.4930894918471679100565397822966933443384,
          734.28956545265310419975683073460839883084, -115.725049557488955381876779314804212149868,
          73.48712187673436928492758232530636475648, 10.778681365965833693706559978590067584]
        [0, 0, -0.0346600874501263519134500031849706640625,
          0.40391603136110699532909638673992341936629, -2.562251370421334768084150570290066360212,
          10.0510536225154217038957026318138761827868, -20.925526097058127254390043316584846925192,
          16.51784545265815722111844767817425748099, 3.637804673295418857543439415644724512]
        [0, 0, 0.00889636066484136295449219124259126953125,
          -0.07095002728940985926490326775120598551904, 0.3904643112965916611720414892213250434668,
          -1.0917633909341952601814718968458007102328, 1.063788780218556750902708460881089196478,
          0.5402139505363297325115745808962687424]
        [0, 0, 0.000175971280536189054781224609375, -0.001466427336371459652787525775776,
          0.00824865379569177662138341853572, -0.02454956478504736944260928141032,
          0.0298345407479287825790098990042]
        [0, 5.8665821, 98.4043996, 11.6052773]
        [0, 19.9268894, 4.7001369]
        [0, 0.475888823]
        [0, 0, 0.00029588992] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.16 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.2025 (-1.59701539181) hw0 (by norm_num) lgU184
    have hτ1 : w / 0.2025 ≤ 4.938272 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.59701539181) + 4.938272 * w := by linarith
    have hwa : Real.log 0.16 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.59701539181) 4.938272 11.95698 13.4611 0.1243757
        0.01902918 (13528 / 13597) 0.690606631928 0.466197049 0.13597 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (13528 / 13597) = (27125 / 13597) by norm_num]; exact lgU185)
        (by norm_num) (by norm_num)
    have hRs : 0.466197049 + 0.13597 * ((2.08 + Real.log r + ((-2.59701539181) + 4.938272 * w)) *
        (0.1243757 + 0.01902918 * (Real.log r + 2 / 3 * ((-2.59701539181) + 4.938272 * w) -
        11.95698)) / 2) ≤ 0.470980934 + (-0.00992174806) * Real.log r + (-0.0478952828) * w +
        0.00129369881 * Real.log r ^ 2 + 0.0106477277 * w * Real.log r + 0.0210325501 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000058383377114973223062442998 + 0.000000000008406491048605 *
          Real.log r + 0.000000000063826784990598968448 * w + 0.0000000000077 * Real.log r ^ 2 +
          0.000000000080280624 * w * Real.log r + 0.0000000000327652630566912 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 11.32 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL52]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.32 2.42657107173 0.082213 2.49844183955
        (Real.log r + (-2.59701539181) + 4.938272 * w) 1.7810727 1.0328855 0.21353 1.1708
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL186 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL188]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.88002822 + 0.0312666278 * Real.log r + 0.154403113 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 5.8665821 + 19.9268894 * Real.log r + 98.4043996 * w + 0.475888823 *
        Real.log r ^ 2 + 4.7001369 * w * Real.log r + 11.6052773 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ (0.0000000075327821219802768007580010425 +
          (1457506234817709107 / 18000000000000000000000000) * Real.log r + (16170619663303687101347
          / 562500000000000000000000000000) * w + 0.000000000873425 * Real.log r ^ 2 +
          0.0000000091587084432 * w * Real.log r + 0.0000000978956967306090752 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000924656 :=
      (wy_rpow_le w y 0.16 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.25, 0.36]` of region `R1`** (`ptLoS`; moments `mom_0_25_0_36`). -/
private theorem tR1_lo3 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.25 0.36
      (1 / Real.sqrt r * (0.03811728434955056 + Real.log r * 0.01142615254558617 + Real.log r ^ 2 *
          (-0.00003012850352996525) + Real.log r ^ 3 * 0.0000295355217236813 + Real.log r ^ 4 *
          0.0000005099247418287279) + 1 / r * (1.132485764897651 + Real.log r * 0.6844078940782003 +
          Real.log r ^ 2 * 0.01472963882285836) + 0.000002705417152820288) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.25 : ℝ) 0.36, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.31541006586308693793078216928953125, -28.4122549296325442861826744962932265625,
          83.63344719153265926940692542276594296875, -62.331380025038983099878215072136310546875,
          -185.8159276368911272533951895249222590625, 314.7814621394563267087301664618886125,
          -13.80078755320716597467186398531065, 4.4797227471435678490952213054025,
          0.32046889908697740602199256275]
        [0, 0, 3.2080050691547998424940554325131671875, -17.289645211372346540226343505123544375,
          62.74302867584883690840876310889119078125, -121.769125723728122475207679132883642625,
          101.367395557513404330320524991393637, -11.70220143278337619140718855233442,
          4.78133569086389913980730618963364, 0.436238173607462934406480317228]
        [0, 0, -0.02967600573218783513333128515536953125, 0.22468783590409548411925908709233646875,
          -0.916264789314790295594092454540398875, 2.3192392573275340815727801450356702,
          -3.124581112800713964119029764160708, 1.606384943467871558051912326924504,
          0.2199366878670781448989745450408]
        [0, 0, 0.007665190567638145172824187200329703125, -0.0391657683852547754966309866887995625,
          0.1380236696960817272732572206661053, -0.247394208201512075872831307008962,
          0.155303018439635412861509912322756, 0.0487892757470435202398249257612]
        [0, 0, 0.00014150792076594584739659296875, -0.0007547089107517111861151625,
          0.002716952078706160270014585, -0.0051751468165831624190754, 0.0040251141906757929926142]
        [0, 14.0952437, 67.6504543, 5.03368078]
        [0, 20.464257, 3.04537606]
        [0, 0.460613007]
        [0, 0, 0.00027468] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.31541006586308693793078216928953125, -28.4122549296325442861826744962932265625,
          83.63344719153265926940692542276594296875, -62.331380025038983099878215072136310546875,
          -185.8159276368911272533951895249222590625, 314.7814621394563267087301664618886125,
          -13.80078755320716597467186398531065, 4.4797227471435678490952213054025,
          0.32046889908697740602199256275]
        [0, 0, 3.2080050691547998424940554325131671875, -17.289645211372346540226343505123544375,
          62.74302867584883690840876310889119078125, -121.769125723728122475207679132883642625,
          101.367395557513404330320524991393637, -11.70220143278337619140718855233442,
          4.78133569086389913980730618963364, 0.436238173607462934406480317228]
        [0, 0, -0.02967600573218783513333128515536953125, 0.22468783590409548411925908709233646875,
          -0.916264789314790295594092454540398875, 2.3192392573275340815727801450356702,
          -3.124581112800713964119029764160708, 1.606384943467871558051912326924504,
          0.2199366878670781448989745450408]
        [0, 0, 0.007665190567638145172824187200329703125, -0.0391657683852547754966309866887995625,
          0.1380236696960817272732572206661053, -0.247394208201512075872831307008962,
          0.155303018439635412861509912322756, 0.0487892757470435202398249257612]
        [0, 0, 0.00014150792076594584739659296875, -0.0007547089107517111861151625,
          0.002716952078706160270014585, -0.0051751468165831624190754, 0.0040251141906757929926142]
        [0, 14.0952437, 67.6504543, 5.03368078]
        [0, 20.464257, 3.04537606]
        [0, 0.460613007]
        [0, 0, 0.00027468] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.25 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.3025 (-1.19567400084) hw0 (by norm_num) lgU190
    have hτ1 : w / 0.3025 ≤ 3.305786 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.19567400084) + 3.305786 * w := by linarith
    have hwa : Real.log 0.25 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.19567400084) 3.305786 12.24876 13.69901
        0.1290593 0.02049166 (13962 / 13163) 0.723045948679 0.470656214 0.13163 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (13962 / 13163) = (27125 / 13163) by norm_num]; exact lgU191)
        (by norm_num) (by norm_num)
    have hRs : 0.470656214 + 0.13163 * ((2.08 + Real.log r + ((-2.19567400084) + 3.305786 * w)) *
        (0.1290593 + 0.02049166 * (Real.log r + 2 / 3 * ((-2.19567400084) + 3.305786 * w) -
        12.24876)) / 2) ≤ 0.471812897 + (-0.0101555055) * Real.log r + (-0.0334000219) * w +
        0.00134865861 * Real.log r ^ 2 + 0.00743062789 * w * Real.log r + 0.00982562625 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.00000000073533379690935817448119584 + (6397992556609 /
          150000000000000000000000) * Real.log r + (5127146134137569837 /
          93750000000000000000000000000) * w + 0.0000000000071 * Real.log r ^ 2 + (28768103 /
          3000000000000000000) * w * Real.log r + (10093286071979 / 3750000000000000000000000) *
          w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 11.77 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL68]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.77 2.46555392023 0.079574 2.53106787365
        (Real.log r + (-2.19567400084) + 3.305786 * w) 1.7810727 1.0165546 0.21272 1.17526
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL192 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL194]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.90538127 + 0.0301481843 * Real.log r + 0.0996634455 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 14.0952437 + 20.464257 * Real.log r + 67.6504543 * w + 0.460613007 *
        Real.log r ^ 2 + 3.04537606 * w * Real.log r + 5.03368078 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((6497577985614086024222711087 /
          112500000000000000000000000000000000) + (41152045556066473 / 2250000000000000000000000) *
          Real.log r + (78142678035303380756389 / 1125000000000000000000000000000) * w +
          0.00000000015315 * Real.log r ^ 2 + 0.0000000010955582518 * w * Real.log r +
          0.0000000098692605654924574 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000858375 :=
      (wy_rpow_le w y 0.25 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.36, 0.49]` of region `R1`** (`ptLoS`; moments `mom_0_36_0_49`). -/
private theorem tR1_lo4 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.36 0.49
      (1 / Real.sqrt r * (0.07775831762638803 + Real.log r * 0.02140928526223211 + Real.log r ^ 2 *
          (-0.00005750099042864006) + Real.log r ^ 3 * 0.00005803427019469582 + Real.log r ^ 4 *
          0.0000009529820235905908) + 1 / r * (2.15428307059276 + Real.log r * 1.098206626365112 +
          Real.log r ^ 2 * 0.02260790066043166) + 0.000005569787428998745) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.36 : ℝ) 0.49, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.96095654306252351160339184041796875, -19.387141229024101194721405636827380733,
          40.64014988495345568687841716589854473179, -25.50912784123983306616584232145057269657,
          -33.683282202488066805925820971180098730576, 44.412966151444377681167210721013434227358,
          -1.52939401018734285375734555610717129525, 0.33996959056413666717162101244325199124,
          0.0164310022676198519367020039856272256]
        [0, 0, 2.70087651648805955836544418321515625, -10.119821200708644802752533424968791925745,
          25.5252087431458797880723677517363754008135,
          -34.4702450633674739705650754585477493087922,
          20.0674378080981404175030065623863944141336, -1.7725948751979213166796180899403319317775,
          0.506670324844889823905593680285446158158, 0.03123944181524261467129716110849669952]
        [0, 0, -0.02586746427672040931220365069520703125,
          0.13792890875046684734490942465270941979075, -0.3922011649744177812022331708255886740155,
          0.6945332137696458547989580406705429478035, -0.65624609106379713713182972918061090812375,
          0.237930870985655813858686928581600702155, 0.0219977727404140308558797973189928912]
        [0, 0, 0.00678722571934891379905355122691865234375,
          -0.0241075833298840523655582450539765287527, 0.0590287950065499895275367827774149502291,
          -0.07358816785683955726257271744160089546875, 0.032280645694810030452764967882616954623,
          0.00681564298557639722979119074394932512]
        [0, 0, 0.000118717463900848566732931640625, -0.000439694310100673617347001143402,
          0.001099235778146128877521525056946, -0.001454015577797201393929464081565,
          0.00078534792229521366760923349658]
        [0, 21.1498916, 49.4446908, 2.51396365]
        [0, 20.8903811, 2.1242992]
        [0, 0.448758187]
        [0, 0, 0.00025848384] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.96095654306252351160339184041796875, -19.387141229024101194721405636827380733,
          40.64014988495345568687841716589854473179, -25.50912784123983306616584232145057269657,
          -33.683282202488066805925820971180098730576, 44.412966151444377681167210721013434227358,
          -1.52939401018734285375734555610717129525, 0.33996959056413666717162101244325199124,
          0.0164310022676198519367020039856272256]
        [0, 0, 2.70087651648805955836544418321515625, -10.119821200708644802752533424968791925745,
          25.5252087431458797880723677517363754008135,
          -34.4702450633674739705650754585477493087922,
          20.0674378080981404175030065623863944141336, -1.7725948751979213166796180899403319317775,
          0.506670324844889823905593680285446158158, 0.03123944181524261467129716110849669952]
        [0, 0, -0.02586746427672040931220365069520703125,
          0.13792890875046684734490942465270941979075, -0.3922011649744177812022331708255886740155,
          0.6945332137696458547989580406705429478035, -0.65624609106379713713182972918061090812375,
          0.237930870985655813858686928581600702155, 0.0219977727404140308558797973189928912]
        [0, 0, 0.00678722571934891379905355122691865234375,
          -0.0241075833298840523655582450539765287527, 0.0590287950065499895275367827774149502291,
          -0.07358816785683955726257271744160089546875, 0.032280645694810030452764967882616954623,
          0.00681564298557639722979119074394932512]
        [0, 0, 0.000118717463900848566732931640625, -0.000439694310100673617347001143402,
          0.001099235778146128877521525056946, -0.001454015577797201393929464081565,
          0.00078534792229521366760923349658]
        [0, 21.1498916, 49.4446908, 2.51396365]
        [0, 20.8903811, 2.1242992]
        [0, 0.448758187]
        [0, 0, 0.00025848384] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.36 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.4225 (-0.861565831581) hw0 (by norm_num) lgU196
    have hτ1 : w / 0.4225 ≤ 2.366864 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.861565831581) + 2.366864 * w := by linarith
    have hwa : Real.log 0.36 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.861565831581) 2.366864 12.48858 13.90153
        0.1331814 0.02184871 (2047 / 1828) 0.75132319021 0.474656416 0.12796 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (2047 / 1828) = (3875 / 1828) by norm_num]; exact lgU197)
        (by norm_num) (by norm_num)
    have hRs : 0.474656416 + 0.12796 * ((2.08 + Real.log r + ((-1.861565831581) + 2.366864 * w)) *
        (0.1331814 + 0.02184871 * (Real.log r + 2 / 3 * ((-1.861565831581) + 2.366864 * w) -
        12.48858)) / 2) ≤ 0.472325412 + (-0.0103660822) * Real.log r + (-0.02477601) * w +
        0.00139788047 * Real.log r ^ 2 + 0.00551432159 * w * Real.log r + 0.0052206597 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000002964434197679580338743709908 + (18988755152149 /
          3000000000000000000000000) * Real.log r + (10582211827869249421 /
          234375000000000000000000000000) * w + 0.0000000000042 * Real.log r ^ 2 + (998359 /
          187500000000000000) * w * Real.log r + (79790623511 / 29296875000000000000000) * w ^ 2)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 12.13 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL84]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.13 2.49568172191 0.077526 2.55714191601
        (Real.log r + (-1.861565831581) + 2.366864 * w) 1.7810727 1.0042828 0.21207 1.17886
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL198 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL200]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.92547827 + 0.0292825073 * Real.log r + 0.0693077124 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 21.1498916 + 20.8903811 * Real.log r + 49.4446908 * w + 0.448758187 *
        Real.log r ^ 2 + 2.1242992 * w * Real.log r + 2.51396365 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((3358802057196430037927480817863 /
          180000000000000000000000000000000000000) + (8092208039110613677 /
          90000000000000000000000000) * Real.log r + (230301243017593970624933 /
          5625000000000000000000000000000) * w + 0.00000000004435 * Real.log r ^ 2 +
          0.0000000051788048368 * w * Real.log r + 0.0000000052743633656238976 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000807762 :=
      (wy_rpow_le w y 0.36 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.49, 0.64]` of region `R1`** (`ptLoS`; moments `mom_0_49_0_64`). -/
private theorem tR1_lo5 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.49 0.64
      (1 / Real.sqrt r * (0.1382109480103129 + Real.log r * 0.03551416926521344 + Real.log r ^ 2 *
          (-0.00009441038361279945) + Real.log r ^ 3 * 0.0001003790954308112 + Real.log r ^ 4 *
          0.000001581058454180946) + 1 / r * (3.546048204044501 + Real.log r * 1.594660322406238 +
          Real.log r ^ 2 * 0.03163597842475823) + 0.00001003762668089906) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.49 : ℝ) 0.64, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.615844655510014137899977353001171875, -13.853527952388594897355938799305992504235,
          21.70672733037158716086034426562283102472165,
          -11.18767069857682316896312731728570608585425,
          -7.80468233106038228089256467451738204624835, 8.4394800703885951340852682891644136367292,
          -0.2347910647966778797631307547943306970625, 0.0380170898192081666016972650921416183072,
          0.0013151931193898917670103285332057568]
        [0, 0, 2.332649328418252107228879448697232421875,
          -6.42717180248454769289452932097503928691055,
          11.91908921015420242796546285840742313792033,
          -11.8453897714866487054589298944054436831053575,
          5.096318163229676016247852991521953376079925,
          -0.356433758694561958040152620732398098377285,
          0.07542337319974179802252344585185605072144, 0.00332908216754201633356584911297105136]
        [0, 0, -0.022897227331130257629682926920553515625,
          0.09087057530788552422293358241842595570614,
          -0.1905475933924258808305590265883632641875045,
          0.249573547399197894602061255222850722796635,
          -0.174782152962865738566691151230130851014495,
          0.047191767713482059338006933475414637433824, 0.003121014143870940257938182515631169056]
        [0, 0, 0.0061256711646599152866133549373497265625,
          -0.016000539102228537369521396342254536487101,
          0.02879803791402640238212520973608894213263,
          -0.02641439067445601511577249311806657715887,
          0.008562360587306981722534367052681455585472, 0.001287418174730195082532073398851663168]
        [0, 0, 0.0001024701820290294024167578125, -0.000278830427272030777597006614273,
          0.00051213752150169023635883736099, -0.00049770410031613581827810319051,
          0.000197501627377915847247400484256]
        [0, 27.3343571, 37.7643073, 1.38741676]
        [0, 21.2424202, 1.56084366]
        [0, 0.438987223]
        [0, 0, 0.00024553728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.615844655510014137899977353001171875, -13.853527952388594897355938799305992504235,
          21.70672733037158716086034426562283102472165,
          -11.18767069857682316896312731728570608585425,
          -7.80468233106038228089256467451738204624835, 8.4394800703885951340852682891644136367292,
          -0.2347910647966778797631307547943306970625, 0.0380170898192081666016972650921416183072,
          0.0013151931193898917670103285332057568]
        [0, 0, 2.332649328418252107228879448697232421875,
          -6.42717180248454769289452932097503928691055,
          11.91908921015420242796546285840742313792033,
          -11.8453897714866487054589298944054436831053575,
          5.096318163229676016247852991521953376079925,
          -0.356433758694561958040152620732398098377285,
          0.07542337319974179802252344585185605072144, 0.00332908216754201633356584911297105136]
        [0, 0, -0.022897227331130257629682926920553515625,
          0.09087057530788552422293358241842595570614,
          -0.1905475933924258808305590265883632641875045,
          0.249573547399197894602061255222850722796635,
          -0.174782152962865738566691151230130851014495,
          0.047191767713482059338006933475414637433824, 0.003121014143870940257938182515631169056]
        [0, 0, 0.0061256711646599152866133549373497265625,
          -0.016000539102228537369521396342254536487101,
          0.02879803791402640238212520973608894213263,
          -0.02641439067445601511577249311806657715887,
          0.008562360587306981722534367052681455585472, 0.001287418174730195082532073398851663168]
        [0, 0, 0.0001024701820290294024167578125, -0.000278830427272030777597006614273,
          0.00051213752150169023635883736099, -0.00049770410031613581827810319051,
          0.000197501627377915847247400484256]
        [0, 27.3343571, 37.7643073, 1.38741676]
        [0, 21.2424202, 1.56084366]
        [0, 0.438987223]
        [0, 0, 0.00024553728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.49 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.5625 (-0.575364144352) hw0 (by norm_num) lgU202
    have hτ1 : w / 0.5625 ≤ 1.777778 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.575364144352) + 1.777778 * w := by linarith
    have hwa : Real.log 0.49 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.575364144352) 1.777778 12.69208 14.07768
        0.1368915 0.02312563 (14647 / 12478) 0.776488718693 0.478302565 0.12478 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14647 / 12478) = (27125 / 12478) by norm_num]; exact lgU203)
        (by norm_num) (by norm_num)
    have hRs : 0.478302565 + 0.12478 * ((2.08 + Real.log r + ((-1.575364144352) + 1.777778 * w)) *
        (0.1368915 + 0.02312563 * (Real.log r + 2 / 3 * ((-1.575364144352) + 1.777778 * w) -
        12.69208)) / 2) ≤ 0.472606805 + (-0.0105587806) * Real.log r + (-0.0192026302) * w +
        0.00144280806 * Real.log r ^ 2 + 0.00427498737 * w * Real.log r + 0.0030399914 * w ^ 2 := by
      refine le_of_sub_eq _ _ ((14150596526431769082359603 / 14648437500000000000000000000000000) +
          (4428661517627 / 187500000000000000000000) * Real.log r +
          0.0000000000809700145768582093056 * w + 0.0000000000043 * Real.log r ^ 2 + (11768827 /
          3000000000000000000) * w * Real.log r + (15465390863203 / 3750000000000000000000000) *
          w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 12.44 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL100]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.44 2.52091708627 0.075838 2.57915579369
        (Real.log r + (-1.575364144352) + 1.777778 * w) 1.7810727 0.99422945 0.21151 1.18198
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL204 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL206]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.94215362 + 0.0285692885 * Real.log r + 0.0507898525 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 27.3343571 + 21.2424202 * Real.log r + 37.7643073 * w + 0.438987223 *
        Real.log r ^ 2 + 1.56084366 * w * Real.log r + 1.38741676 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((545173990783386212011318109 /
          175781250000000000000000000000000000) + (16388622218178157 / 351562500000000000000000) *
          Real.log r + (14863751952394163797573 / 175781250000000000000000000000) * w +
          0.00000000087655 * Real.log r ^ 2 + 0.0000000084556346118 * w * Real.log r +
          0.0000000074223805944482902 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000767304 :=
      (wy_rpow_le w y 0.49 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.64, 0.81]` of region `R1`** (`ptLoS`; moments `mom_0_64_0_81`). -/
private theorem tR1_lo6 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.64 0.81
      (1 / Real.sqrt r * (0.2184208144999807 + Real.log r * 0.05296879638370652 + Real.log r ^ 2 *
          (-0.0001365516289769168) + Real.log r ^ 3 * 0.0001554263053229769 + Real.log r ^ 4 *
          0.000002363245390251174) + 1 / r * (5.191414308427854 + Real.log r * 2.117088364117342 +
          Real.log r ^ 2 * 0.04069977751252702) + 0.00001612223674138461) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.64 : ℝ) 0.81, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.294538179059398199437962300293905101008,
          -10.27116842571952127150564482203281518925968,
          12.479503896900427828027375226145585224692328,
          -5.3014231875578642099496227840481795113328144,
          -2.162895520862791250654582236570436179815708,
          1.995831495388225566547331268443499199884318,
          -0.0458881935531809945000224668004220126183696,
          0.0056587136496364178798393336646800345094768, 0.0001463333797581365455395686200783854144]
        [0, 0, 2.05266629727370507839647886630518679748672,
          -4.333487153907833516588436385476197838461144,
          6.1567637984997872516481732317512630922485292,
          -4.691306117053633982153934838531653800326386,
          1.553109468841689006833967520179704368955831,
          -0.0883243187428091604465927763332737597137747,
          0.0144191308778768694667553554502315607839026, 0.0004757660718770349451151810661662609208]
        [0, 0, -0.020504638513083796924116687443027975918552,
          0.0630759220299104170572947387962117438731344,
          -0.101619475330289923899260944183959509767252,
          0.102536732291185252007273145983106216050886,
          -0.0554221088969607074365716995638182724299024,
          0.0115968576341543535111928422768591408237232, 0.0005729012498309022929312631508056881856]
        [0, 0, 0.0056059032310882921961970151238003282782168,
          -0.011220632007815759936361638861467688952204,
          0.015468684144230747605224687368135514913178,
          -0.0108771267014190590497614708134170011227758,
          0.0027135563090356519434957822087685264054004, 0.0003035419700146093215124703458484650032]
        [0, 0, 0.0000903123775177181616127635771016, -0.000188150786005934665117453731748,
          0.000264587043371321065844198495886, -0.0001968653592213854470591439454346,
          0.0000598115243692103108858319883548]
        [0, 32.8454191, 29.814043, 0.825205403]
        [0, 21.5406313, 1.19242099]
        [0, 0.430761784]
        [0, 0, 0.000234848] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.294538179059398199437962300293905101008,
          -10.27116842571952127150564482203281518925968,
          12.479503896900427828027375226145585224692328,
          -5.3014231875578642099496227840481795113328144,
          -2.162895520862791250654582236570436179815708,
          1.995831495388225566547331268443499199884318,
          -0.0458881935531809945000224668004220126183696,
          0.0056587136496364178798393336646800345094768, 0.0001463333797581365455395686200783854144]
        [0, 0, 2.05266629727370507839647886630518679748672,
          -4.333487153907833516588436385476197838461144,
          6.1567637984997872516481732317512630922485292,
          -4.691306117053633982153934838531653800326386,
          1.553109468841689006833967520179704368955831,
          -0.0883243187428091604465927763332737597137747,
          0.0144191308778768694667553554502315607839026, 0.0004757660718770349451151810661662609208]
        [0, 0, -0.020504638513083796924116687443027975918552,
          0.0630759220299104170572947387962117438731344,
          -0.101619475330289923899260944183959509767252,
          0.102536732291185252007273145983106216050886,
          -0.0554221088969607074365716995638182724299024,
          0.0115968576341543535111928422768591408237232, 0.0005729012498309022929312631508056881856]
        [0, 0, 0.0056059032310882921961970151238003282782168,
          -0.011220632007815759936361638861467688952204,
          0.015468684144230747605224687368135514913178,
          -0.0108771267014190590497614708134170011227758,
          0.0027135563090356519434957822087685264054004, 0.0003035419700146093215124703458484650032]
        [0, 0, 0.0000903123775177181616127635771016, -0.000188150786005934665117453731748,
          0.000264587043371321065844198495886, -0.0001968653592213854470591439454346,
          0.0000598115243692103108858319883548]
        [0, 32.8454191, 29.814043, 0.825205403]
        [0, 21.5406313, 1.19242099]
        [0, 0.430761784]
        [0, 0, 0.000234848] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.64 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.7225 (-0.325037858537) hw0 (by norm_num) lgU208
    have hτ1 : w / 0.7225 ≤ 1.384084 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.325037858537) + 1.384084 * w := by linarith
    have hwa : Real.log 0.64 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.325037858537) 1.384084 12.86876 14.23345
        0.1402844 0.0243393 (14928 / 12197) 0.799265792616 0.481670847 0.12197 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14928 / 12197) = (27125 / 12197) by norm_num]; exact lgU209)
        (by norm_num) (by norm_num)
    have hRs : 0.481670847 + 0.12197 * ((2.08 + Real.log r + ((-1.325037858537) + 1.384084 * w)) *
        (0.1402844 + 0.0243393 * (Real.log r + 2 / 3 * ((-1.325037858537) + 1.384084 * w) -
        12.86876)) / 2) ≤ 0.472718908 + (-0.0107368538) * Real.log r + (-0.0153777158) * w +
        0.00148433222 * Real.log r ^ 2 + 0.00342406744 * w * Real.log r + 0.00189567879 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.000000000754895406392920262683816217 + 0.0000000000012846658433975
          * Real.log r + 0.000000000013908671482218388312 * w + 0.0000000000095 * Real.log r ^ 2 +
          0.00000000000127053 * w * Real.log r + 0.000000000007253424097808 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 12.71 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL116]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.71 2.54238908416 0.074417 2.59807086959
        (Real.log r + (-1.325037858537) + 1.384084 * w) 1.7810727 0.98583259 0.21104 1.18461
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL210 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL212]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.95627559 + 0.0279716821 * Real.log r + 0.0387151576 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 32.8454191 + 21.5406313 * Real.log r + 29.814043 * w + 0.430761784 *
        Real.log r ^ 2 + 1.19242099 * w * Real.log r + 0.825205403 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((14370390805053651897531139235693 /
          360000000000000000000000000000000000000) + (17965238046813186011 /
          180000000000000000000000000) * Real.log r + (266035634196345436712231 /
          45000000000000000000000000000000) * w + 0.000000000873325 * Real.log r ^ 2 +
          0.0000000063257983186 * w * Real.log r + 0.0000000006161381200005812 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.00007339 :=
      (wy_rpow_le w y 0.64 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
/-- **Piece `[0.81, 1]` of region `R1`** (`ptLoS`; moments `mom_0_81_1`). -/
private theorem tR1_lo7 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.81 1
      (1 / Real.sqrt r * (0.3098292504274942 + Real.log r * 0.07149780793903035 + Real.log r ^ 2 *
          (-0.0001762914422883427) + Real.log r ^ 3 * 0.0002170848951557625 + Real.log r ^ 4 *
          0.00000320119815216103) + 1 / r * (6.84160190106015 + Real.log r * 2.577344764783929 +
          Real.log r ^ 2 * 0.04821285623393873) + 0.00002327043286311157) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.81 : ℝ) 1, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.0002066832050634397903949158111328125, -7.845675559821656887013012621611267651975,
          7.6066608597383698283599836543681639814931, -2.69254766010097960594266911887340730708889,
          -0.686536725016199654894346132765019056941506,
          0.5581281004731505684099664543021489809479384,
          -0.0108085950485879636764606068365727390524022,
          0.00104953943953704018260787143343974709081171,
          0.00002097479446376233433996627151813172998]
        [0, 0, 1.832390445448086460031989690725969140625,
          -3.0585804621481155750499512167571188232504, 3.43536932633446831341632307710180632552287,
          -2.070869370393935802615432469178172886521966,
          0.5440971188397198757335677918310597670139058,
          -0.0257090147640740921591292249678387738213645,
          0.00334061898933984226781550187135134257339007,
          0.00008518382559309496150521513770964476766]
        [0, 0, -0.0185443920193671518367181506684566015625,
          0.04560512863191705812305608879092043103476,
          -0.058243119329366194950392207068470524991672,
          0.0467026423422397708059716100971495155326222,
          -0.0200927222161192115760033132119393073751677,
          0.00335849628600315273610129703471770986673668,
          0.00012813058323815890432460410411099797384]
        [0, 0, 0.005185661745778628419399238299278703125,
          -0.008207532128599796702684599592062056100032,
          0.0089437198522584877514211515168865894934368,
          -0.0049749600235907824370880555333271706568924,
          0.00098525306539382621936861574149512775517012,
          0.00008480103298278149381352175145719068456]
        [0, 0, 0.000080864742909111907570453125, -0.000133110687721511672099674530624,
          0.0001479007643978875618216402510176, -0.0000869493029345791214848055498268,
          0.00002087260361988442104292486670484]
        [0, 37.8197525, 24.153454, 0.520164525]
        [0, 21.7984773, 0.938896324]
        [0, 0.423676676]
        [0, 0, 0.0002258064] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.0002066832050634397903949158111328125, -7.845675559821656887013012621611267651975,
          7.6066608597383698283599836543681639814931, -2.69254766010097960594266911887340730708889,
          -0.686536725016199654894346132765019056941506,
          0.5581281004731505684099664543021489809479384,
          -0.0108085950485879636764606068365727390524022,
          0.00104953943953704018260787143343974709081171,
          0.00002097479446376233433996627151813172998]
        [0, 0, 1.832390445448086460031989690725969140625,
          -3.0585804621481155750499512167571188232504, 3.43536932633446831341632307710180632552287,
          -2.070869370393935802615432469178172886521966,
          0.5440971188397198757335677918310597670139058,
          -0.0257090147640740921591292249678387738213645,
          0.00334061898933984226781550187135134257339007,
          0.00008518382559309496150521513770964476766]
        [0, 0, -0.0185443920193671518367181506684566015625,
          0.04560512863191705812305608879092043103476,
          -0.058243119329366194950392207068470524991672,
          0.0467026423422397708059716100971495155326222,
          -0.0200927222161192115760033132119393073751677,
          0.00335849628600315273610129703471770986673668,
          0.00012813058323815890432460410411099797384]
        [0, 0, 0.005185661745778628419399238299278703125,
          -0.008207532128599796702684599592062056100032,
          0.0089437198522584877514211515168865894934368,
          -0.0049749600235907824370880555333271706568924,
          0.00098525306539382621936861574149512775517012,
          0.00008480103298278149381352175145719068456]
        [0, 0, 0.000080864742909111907570453125, -0.000133110687721511672099674530624,
          0.0001479007643978875618216402510176, -0.0000869493029345791214848055498268,
          0.00002087260361988442104292486670484]
        [0, 37.8197525, 24.153454, 0.520164525]
        [0, 21.7984773, 0.938896324]
        [0, 0.423676676]
        [0, 0, 0.0002258064] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.81 : ℝ) * 520000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.9025 (-0.102586588552) hw0 (by norm_num) lgU214
    have hτ1 : w / 0.9025 ≤ 1.108034 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.102586588552) + 1.108034 * w := by linarith
    have hwa : Real.log 0.81 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.102586588552) 1.108034 13.02486 14.37303
        0.1434252 0.0255018 (15179 / 11946) 0.820059318091 0.484801091 0.11946 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15179 / 11946) = (27125 / 11946) by norm_num]; exact lgU215)
        (by norm_num) (by norm_num)
    have hRs : 0.484801091 + 0.11946 * ((2.08 + Real.log r + ((-1.102586588552) + 1.108034 * w)) *
        (0.1434252 + 0.0255018 * (Real.log r + 2 / 3 * ((-1.102586588552) + 1.108034 * w) -
        13.02486)) / 2) ≤ 0.472688369 + (-0.0109038111) * Real.log r + (-0.0126316805) * w +
        0.00152322252 * Real.log r ^ 2 + 0.00281297056 * w * Real.log r + 0.00124674681 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.000000000056073630215559010564644096 + 0.00000000006077280843288 *
          Real.log r + 0.000000000025685653769966206336 * w + 0.000000000006 * Real.log r ^ 2 +
          0.00000000000153754 * w * Real.log r + 0.000000000002089842638544 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
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
    have hLlo : 12.95 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL132]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.95 2.5610957871 0.073193 2.61465549199
        (Real.log r + (-1.102586588552) + 1.108034 * w) 1.7810727 0.97863189 0.21062 1.18698
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL216 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL218]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.96853085 + 0.0274568559 * Real.log r + 0.0304231299 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 37.8197525 + 21.7984773 * Real.log r + 24.153454 * w + 0.423676676 *
        Real.log r ^ 2 + 0.938896324 * w * Real.log r + 0.520164525 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((486947215034540872122564602693 /
          5625000000000000000000000000000000000) + (1875583145898584803 /
          22500000000000000000000000) * Real.log r + (1077037697741296256803651 /
          11250000000000000000000000000000) * w + 0.000000000073925 * Real.log r ^ 2 +
          0.0000000001338548269 * w * Real.log r + 0.0000000003406498496346573 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000705645 :=
      (wy_rpow_le w y 0.81 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
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
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

/-- **Region `R1`, `w ≤ 1`**: the first piece and the 8 lo pieces, added. -/
theorem loR1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 1
      (1 / Real.sqrt r * (0.8043991994235878714 + Real.log r * 0.20067547549423820293 +
          Real.log r ^ 2 * (-0.0005117294484976196525) + Real.log r ^ 3 * 0.0005791142092805440498 +
          Real.log r ^ 4 * 0.000008966006656039939367) + 1 / r * (19.50295097540086572 + Real.log r
          * 8.70176837383020753 + Real.log r ^ 2 * 0.173002035310819846) +
          0.00005943625449380727432) := by
  have h0 := tR1_first y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR1_lo0 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR1_lo1 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR1_lo2 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR1_lo3 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR1_lo4 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR1_lo5 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR1_lo6 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR1_lo7 y r hy hr0 hr1)
  exact intBnd_mono _ _ _ _ _ h8 (le_of_eq (by ring))

end Principia.Common.TernaryGoldbach.MC
