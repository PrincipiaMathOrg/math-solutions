/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCR1Lo

set_option autoImplicit false

/-!
# Region `R1` of `g̃`, `w > 1`, and the region envelope

GENERATED. The 9 pieces on `1, 1.5, 2, 2.4, 2.75, 3.05, 3.35, 3.6, 3.85, 4.1` and the Gaussian tail
    `w > 4.1` (`hiR1`), then **`envR1`**: `gT(y, r) ≤ envF … r` for `r ∈ [520000, 1740000]`, `y ≥
    (10 ^ 25)`, from `gT_le_of`, and `envR1_pos`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[1, 1.5]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_1_1_5`). -/
private theorem tR1_hi0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1 1.5
      (1 / Real.sqrt r * (1.024081490293224 + Real.log r * 0.231160532109816 + Real.log r ^ 2 *
          (-0.0004548489596454083) + Real.log r ^ 3 * 0.0007031044912864594 + Real.log r ^ 4 *
          0.00001022526720534645) + 1 / r * (21.84103274751633 + Real.log r * 7.956221211766464 +
          Real.log r ^ 2 * 0.1470925648325293) + 0.00007625704579484692) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1 : ℝ) 1.5, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92883233225679879852077163556608, -0.00083687446947410423619746744576384]
        [0, 0, 0.6629107792736088302407572617866112, -0.0016210909188412580436422505594131968]
        [0, 0, -0.000542951525591010792345915644849408, -0.0006023725648715574362855656566372352]
        [0, 0, 0.002020064568112980225489671645613056, -0.000007902068915896522154144]
        [0, 0, 0.00002923335053444873324432]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00021801376] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92883233225679879852077163556608, -0.00083687446947410423619746744576384]
        [0, 0, 0.6629107792736088302407572617866112, -0.0016210909188412580436422505594131968]
        [0, 0, -0.000542951525591010792345915644849408, -0.0006023725648715574362855656566372352]
        [0, 0, 0.002020064568112980225489671645613056, -0.000007902068915896522154144]
        [0, 0, 0.00002923335053444873324432]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00021801376] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.8109302) + 0.8109302 * w ≤ Real.log w := log_ge_chord 1 1.5 w (-0.8109302)
        0.8109302 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL145)
        (le_trans (by norm_num) lgL146)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.8109302) 0.8109302 13.02642 14.3694 0.1434573
        0.02549105 (3043 / 2382) 0.82307742913 0.485259753 0.1191 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (3043 / 2382) = (5425 / 2382) by norm_num]; exact lgU219)
        (by norm_num) (by norm_num)
    have hRs : 0.485259753 + 0.1191 * ((2.08 + Real.log r) * (0.1434573 + 0.02549105 * (Real.log r -
        ((-0.8109302) + 0.8109302 * w) / 3 - 13.02642)) / 2) ≤ 0.462752508 + (-0.00766336754) *
        Real.log r + (-0.000853483334) * w + 0.00151799203 * Real.log r ^ 2 + (-0.000410328526) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000020868419752 + 0.0000000000085135565 * Real.log r +
          0.00000000000039822648 * w + 0.0000000000025 * Real.log r ^ 2 + 0.0000000000001529935 * w
          * Real.log r) (by ring) ?_
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
/-- **Piece `[1.5, 2]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_1_5_2`). -/
private theorem tR1_hi1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 1.5 2
      (1 / Real.sqrt r * (0.9564201213435629 + Real.log r * 0.215753413376634 + Real.log r ^ 2 *
          (-0.0002591545793812512) + Real.log r ^ 3 * 0.000640710915131832 + Real.log r ^ 4 *
          0.000009301659602599952) + 1 / r * (20.40248959320031 + Real.log r * 7.432190700447714 +
          Real.log r ^ 2 * 0.137404423953995) + 0.00006657962847074482) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (1.5 : ℝ) 2, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92813896895516412772131007517184, -0.00057822303233850882994513056614272]
        [0, 0, 0.662261943515730578182085830084416, -0.0011200629736628539678902384127654144]
        [0, 0, -0.000069942848762173681922900260706816, -0.0004161982517910541633723814121645056]
        [0, 0, 0.00197038989862602395812846137551872, -0.000005459789273533636928432]
        [0, 0, 0.0000284678307900793677584]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00020376768] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92813896895516412772131007517184, -0.00057822303233850882994513056614272]
        [0, 0, 0.662261943515730578182085830084416, -0.0011200629736628539678902384127654144]
        [0, 0, -0.000069942848762173681922900260706816, -0.0004161982517910541633723814121645056]
        [0, 0, 0.00197038989862602395812846137551872, -0.000005459789273533636928432]
        [0, 0, 0.0000284678307900793677584]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00020376768] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.457581043) + 0.5753641 * w ≤ Real.log w := log_ge_chord 1.5 2 w (-0.457581043)
        0.5753641 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL146)
        (le_trans (by norm_num) lgL151)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.457581043) 0.5753641 12.93053 14.23425 0.1415106
        0.0245555 (431 / 344) 0.812221372361 0.483615048 0.1204 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rw [show (1 : ℝ) + (431 / 344) = (775 / 344) by norm_num]; exact lgU223)
        (by norm_num) (by norm_num)
    have hRs : 0.483615048 + 0.1204 * ((2.08 + Real.log r) * (0.1415106 + 0.0245555 * (Real.log r -
        ((-0.457581043) + 0.5753641 * w) / 3 - 12.93053)) / 2) ≤ 0.462045384 + (-0.00729528958) *
        Real.log r + (-0.000589698622) * w + 0.0014782411 * Real.log r ^ 2 + (-0.000283508953) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ ((117040719251 / 187500000000000000000) + (40055327 /
          30000000000000000000) * Real.log r + (1859863 / 1875000000000000000) * w + (108451 /
          300000000000000000) * w * Real.log r) (by ring) ?_
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
/-- **Piece `[2, 2.4]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_2_2_4`). -/
private theorem tR1_hi2 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2 2.4
      (1 / Real.sqrt r * (0.5046336400920934 + Real.log r * 0.1137842949888831 + Real.log r ^ 2 *
          (-0.00008079606751090307) + Real.log r ^ 3 * 0.0003325270062444142 + Real.log r ^ 4 *
          0.000004822033192008622) + 1 / r * (10.76657439227851 + Real.log r * 3.92203283371062 +
          Real.log r ^ 2 * 0.07250953103399225) + 0.00003348980686790178) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2 : ℝ) 2.4, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92766578687032505000409419283136, -0.00044999318772388319520146169856064]
        [0, 0, 0.6618085638229998202143135422888896, -0.0008716717938858281042379045245161728]
        [0, 0, 0.000238490681422355937457415339554048, -0.000323899892291707846720449903657472]
        [0, 0, 0.00193780594787875327680767703218688, -0.00000424899708247719845784]
        [0, 0, 0.0000279659610471035271736]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00019422816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92766578687032505000409419283136, -0.00044999318772388319520146169856064]
        [0, 0, 0.6618085638229998202143135422888896, -0.0008716717938858281042379045245161728]
        [0, 0, 0.000238490681422355937457415339554048, -0.000323899892291707846720449903657472]
        [0, 0, 0.00193780594787875327680767703218688, -0.00000424899708247719845784]
        [0, 0, 0.0000279659610471035271736]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00019422816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.21846042) + 0.4558038 * w ≤ Real.log w := log_ge_chord 2 2.4 w (-0.21846042)
        0.4558038 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL151)
        (le_trans (by norm_num) lgL153)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.21846042) 0.4558038 12.86976 14.13835 0.1403041
        0.02394757 (14997 / 12128) 0.804938983857 0.4825197 0.12128 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (14997 / 12128) = (27125 / 12128) by norm_num]; exact lgU224)
        (by norm_num) (by norm_num)
    have hRs : 0.4825197 + 0.12128 * ((2.08 + Real.log r) * (0.1403041 + 0.02394757 * (Real.log r -
        ((-0.21846042) + 0.4558038 * w) / 3 - 12.86976)) / 2) ≤ 0.461562811 + (-0.00705489201) *
        Real.log r + (-0.000458923889) * w + 0.00145218065 * Real.log r ^ 2 + (-0.000220636485) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000072699217319424 + 0.000000000002177621728 * Real.log r +
          0.0000000000006224945664 * w + 0.0000000000052 * Real.log r ^ 2 + 0.00000000000039543008 *
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
/-- **Piece `[2.4, 2.75]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_2_4_2_75`). -/
private theorem tR1_hi3 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.4 2.75
      (1 / Real.sqrt r * (0.2490911589375443 + Real.log r * 0.05614959726445333 + Real.log r ^ 2 *
          (-0.00002167195753508029) + Real.log r ^ 3 * 0.0001623236502866835 + Real.log r ^ 4 *
          0.000002352081971259979) + 1 / r * (5.314969842289701 + Real.log r * 1.936129865650841 +
          Real.log r ^ 2 * 0.03579466937976357) + 0.00001603756890967699) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.4 : ℝ) 2.75, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92737631678149751856680307479296, -0.00037941950738721325051795246607232]
        [0, 0, 0.66154344296096113991736137990368, -0.0007349650868223229250267289485886464]
        [0, 0, 0.000443675024348485833730743061014016, -0.0002731017722320777242253679296917504]
        [0, 0, 0.001916192763034657022740021315958784, -0.000003582615063828459469888]
        [0, 0, 0.00002763304516587875014048]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00018841472] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92737631678149751856680307479296, -0.00037941950738721325051795246607232]
        [0, 0, 0.66154344296096113991736137990368, -0.0007349650868223229250267289485886464]
        [0, 0, 0.000443675024348485833730743061014016, -0.0002731017722320777242253679296917504]
        [0, 0, 0.001916192763034657022740021315958784, -0.000003582615063828459469888]
        [0, 0, 0.00002763304516587875014048]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00018841472] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : (-0.0580088632) + 0.388949 * w ≤ Real.log w := log_ge_chord 2.4 2.75 w (-0.0580088632)
        0.388949 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL153)
        (le_trans (by norm_num) lgL155)
    have hR := rChordHi y r w 19.997138805 2.08 (-0.0580088632) 0.388949 12.82438 14.07758 0.1394164
        0.0235518 (2988 / 2437) 0.800250125439 0.481817847 0.12185 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (2988 / 2437) = (5425 / 2437) by norm_num]; exact lgU225)
        (by norm_num) (by norm_num)
    have hRs : 0.481817847 + 0.12185 * ((2.08 + Real.log r) * (0.1394164 + 0.0235518 * (Real.log r -
        ((-0.0580088632) + 0.388949 * w) / 3 - 12.82438)) / 2) ≤ 0.461267596 + (-0.00689535042) *
        Real.log r + (-0.000386949582) * w + 0.00143489342 * Real.log r ^ 2 + (-0.000186033452) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000076155867702592 + 0.000000000008318594724 * Real.log r +
          0.0000000000001504456 * w + 0.000000000005 * Real.log r ^ 2 + 0.000000000000956945 * w *
          Real.log r) (by ring) ?_
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
/-- **Piece `[2.75, 3.05]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_2_75_3_05`). -/
private theorem tR1_hi4 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 2.75 3.05
      (1 / Real.sqrt r * (0.1116594246544741 + Real.log r * 0.02516456108365299 + Real.log r ^ 2 *
          (-0.000003726283895594553) + Real.log r ^ 3 * 0.00007216503379726951 + Real.log r ^ 4 *
          0.00000104507872035531) + 1 / r * (2.382700908817171 + Real.log r * 0.8679669927321617 +
          Real.log r ^ 2 * 0.01604674980154366) + 0.000007028362314283219) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (2.75 : ℝ) 3.05, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92715514325831541578208787923008, -0.00033369096981233439167939899105152]
        [0, 0, 0.66133678136985339701644644420096, -0.0006463853542049596072376149357231104]
        [0, 0, 0.000594951755224527216901349498067968, -0.000240186900167810099936433554122752]
        [0, 0, 0.001900272373612297221836047367729152, -0.00000315082981582806142944]
        [0, 0, 0.00002738776374209018663744]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00018418816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92715514325831541578208787923008, -0.00033369096981233439167939899105152]
        [0, 0, 0.66133678136985339701644644420096, -0.0006463853542049596072376149357231104]
        [0, 0, 0.000594951755224527216901349498067968, -0.000240186900167810099936433554122752]
        [0, 0, 0.001900272373612297221836047367729152, -0.00000315082981582806142944]
        [0, 0, 0.00002738776374209018663744]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00018418816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.0624782857 + 0.3451355 * w ≤ Real.log w := log_ge_chord 2.75 3.05 w 0.0624782857
        0.3451355 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL155)
        (le_trans (by norm_num) lgL157)
    have hR := rChordHi y r w 19.997138805 2.08 0.0624782857 0.3451355 12.78987 14.0322 0.1387489
        0.02326066 (14897 / 12228) 0.796727408363 0.48129231 0.12228 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (14897 / 12228) = (27125 / 12228) by norm_num]; exact lgU226)
        (by norm_num) (by norm_num)
    have hRs : 0.48129231 + 0.12228 * ((2.08 + Real.log r) * (0.1387489 + 0.02326066 * (Real.log r -
        (0.0624782857 + 0.3451355 * w) / 3 - 12.78987)) / 2) ≤ 0.461042033 + (-0.00677762416) *
        Real.log r + (-0.000340313502) * w + 0.00142215676 * Real.log r ^ 2 + (-0.00016361226) * w *
        Real.log r := by
      refine le_of_sub_eq _ _ (0.0000000002342632287834048 + 0.00000000000378839845356 * Real.log r
          + 0.000000000000060445472 * w + 0.0000000000076 * Real.log r ^ 2 + 0.0000000000006059834 *
          w * Real.log r) (by ring) ?_
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
/-- **Piece `[3.05, 3.35]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_3_05_3_35`). -/
private theorem tR1_hi5 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.05 3.35
      (1 / Real.sqrt r * (0.05481160921498633 + Real.log r * 0.01235068616724693 + Real.log r ^ 2 *
          0.0000005640412510459275 + Real.log r ^ 3 * 0.00003518782512261553 + Real.log r ^ 4 *
          0.0000005093392752330249) + 1 / r * (1.169693828399866 + Real.log r * 0.4260944505861617 +
          Real.log r ^ 2 * 0.007877524257990127) + 0.00000339126684862432) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.05 : ℝ) 3.35, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92697594370695872884086343071552, -0.00030017782779262017777861175374848]
        [0, 0, 0.6611692175613054521046017737792192, -0.0005814677921749512100497874210148096]
        [0, 0, 0.000717399977665027646728958597240576, -0.0002160645279510385694504614448241664]
        [0, 0, 0.001887456019717746189908648199638016, -0.000002834386705992015043408]
        [0, 0, 0.00002719017895625379025552]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.0001810368] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92697594370695872884086343071552, -0.00030017782779262017777861175374848]
        [0, 0, 0.6611692175613054521046017737792192, -0.0005814677921749512100497874210148096]
        [0, 0, 0.000717399977665027646728958597240576, -0.0002160645279510385694504614448241664]
        [0, 0, 0.001887456019717746189908648199638016, -0.000002834386705992015043408]
        [0, 0, 0.00002719017895625379025552]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.0001810368] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.161317834 + 0.3127291 * w ≤ Real.log w := log_ge_chord 3.05 3.35 w 0.161317834
        0.3127291 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL157)
        (le_trans (by norm_num) lgL159)
    have hR := rChordHi y r w 19.997138805 2.08 0.161317834 0.3127291 12.75859 13.99769 0.1381493
        0.02302694 (14862 / 12263) 0.793869213537 0.480867025 0.12263 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (14862 / 12263) = (27125 / 12263) by norm_num]; exact lgU227)
        (by norm_num) (by norm_num)
    have hRs : 0.480867025 + 0.12263 * ((2.08 + Real.log r) * (0.1381493 + 0.02302694 * (Real.log r
        - (0.161317834 + 0.3127291 * w) / 3 - 12.75859)) / 2) ≤ 0.460859277 + (-0.00668236437) *
        Real.log r + (-0.000306135248) * w + 0.00141189683 * Real.log r ^ 2 + (-0.000147180407) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ ((31375349038381 / 93750000000000000000000) + (119937618337 /
          15000000000000000000000) * Real.log r + (834842363 / 1875000000000000000000) * w +
          0.0000000000039 * Real.log r ^ 2 + (271910951 / 300000000000000000000) * w * Real.log r)
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
/-- **Piece `[3.35, 3.6]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_3_35_3_6`). -/
private theorem tR1_hi6 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.35 3.6
      (1 / Real.sqrt r * (0.0214804685347465 + Real.log r * 0.004839508820654697 + Real.log r ^ 2 *
          0.0000009960170172434538 + Real.log r ^ 3 * 0.00001371152838404097 + Real.log r ^ 4 *
          0.0000001983948826188931) + 1 / r * (0.4584207113119297 + Real.log r * 0.1669928629024103
          + Real.log r ^ 2 * 0.003087320960447354) + 0.000001308469053932007) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.35 : ℝ) 3.6, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92683101892807283898444331474176, -0.00027464648555375948031032318580928]
        [0, 0, 0.6610361729586046422323409042826496, -0.0005320115969289005956876717864390656]
        [0, 0, 0.000819679963927170718636685184313088, -0.0001976873628809082992442815954604032]
        [0, 0, 0.00187663696987212376758059083023872, -0.000002593310612268891367104]
        [0, 0, 0.0000270236080680122336584]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00017822816] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92683101892807283898444331474176, -0.00027464648555375948031032318580928]
        [0, 0, 0.6610361729586046422323409042826496, -0.0005320115969289005956876717864390656]
        [0, 0, 0.000819679963927170718636685184313088, -0.0001976873628809082992442815954604032]
        [0, 0, 0.00187663696987212376758059083023872, -0.000002593310612268891367104]
        [0, 0, 0.0000270236080680122336584]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00017822816] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.244515779 + 0.2878939 * w ≤ Real.log w := log_ge_chord 3.35 3.6 w 0.244515779
        0.2878939 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL159)
        (le_trans (by norm_num) lgL161)
    have hR := rChordHi y r w 19.997138805 2.08 0.244515779 0.2878939 12.7346 13.96641 0.1376929
        0.02283188 (2119 / 1756) 0.791507168001 0.48051632 0.12292 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (2119 / 1756) = (3875 / 1756) by norm_num]; exact lgU228)
        (by norm_num) (by norm_num)
    have hRs : 0.48051632 + 0.12292 * ((2.08 + Real.log r) * (0.1376929 + 0.02283188 * (Real.log r -
        (0.244515779 + 0.2878939 * w) / 3 - 12.7346)) / 2) ≤ 0.460711476 + (-0.00660280556) *
        Real.log r + (-0.000280097203) * w + 0.00140324735 * Real.log r ^ 2 + (-0.000134662116) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ ((20812347520987 / 23437500000000000000000) + (19202116999 /
          3750000000000000000000) * Real.log r + (45231467 / 234375000000000000000) * w +
          0.0000000000052 * Real.log r ^ 2 + (34488959 / 37500000000000000000) * w * Real.log r)
          (by ring) ?_
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
/-- **Piece `[3.6, 3.85]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_3_6_3_85`). -/
private theorem tR1_hi7 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.6 3.85
      (1 / Real.sqrt r * (0.0100807567879647 + Real.log r * 0.002270923591681904 + Real.log r ^ 2 *
          0.000000771936678452985 + Real.log r ^ 3 * 0.000006404492162387459 + Real.log r ^ 4 *
          0.00000009263677188703595) + 1 / r * (0.2151446300664503 + Real.log r * 0.0783725883807849
          + Real.log r ^ 2 * 0.001448932191634507) + 0.0000006067646422105215) := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.6 : ℝ) 3.85, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92671222945988460684504149885504, -0.00025489719202268218208309520808384]
        [0, 0, 0.6609278044245743733694100979290368, -0.0004937556801239315705284190310675968]
        [0, 0, 0.00090446722553451162445219279745152, -0.0001834720503436764204828276528637952]
        [0, 0, 0.00186772009453911807390994611565056, -0.000002406830706378527717344]
        [0, 0, 0.0000268862356343984793432]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00017610304] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92671222945988460684504149885504, -0.00025489719202268218208309520808384]
        [0, 0, 0.6609278044245743733694100979290368, -0.0004937556801239315705284190310675968]
        [0, 0, 0.00090446722553451162445219279745152, -0.0001834720503436764204828276528637952]
        [0, 0, 0.00186772009453911807390994611565056, -0.000002406830706378527717344]
        [0, 0, 0.0000268862356343984793432]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00017610304] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.314127924 + 0.2685572 * w ≤ Real.log w := log_ge_chord 3.6 3.85 w 0.314127924
        0.2685572 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL161)
        (le_trans (by norm_num) lgL163)
    have hR := rChordHi y r w 19.997138805 2.08 0.314127924 0.2685572 12.71222 13.94242 0.1372699
        0.02267155 (14809 / 12316) 0.789556582175 0.480227223 0.12316 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (14809 / 12316) = (27125 / 12316) by norm_num]; exact lgU229)
        (by norm_num) (by norm_num)
    have hRs : 0.480227223 + 0.12316 * ((2.08 + Real.log r) * (0.1372699 + 0.02267155 * (Real.log r
        - (0.314127924 + 0.2685572 * w) / 3 - 12.71222)) / 2) ≤ 0.460590329 + (-0.0065368974) *
        Real.log r + (-0.000259955959) * w + 0.00139611405 * Real.log r ^ 2 + (-0.000124978826) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.00000000043027238803136 + 0.000000000008018648092 * Real.log r +
          (17978341 / 46875000000000000000) * w + 0.000000000001 * Real.log r ^ 2 + (4700257 /
          7500000000000000000) * w * Real.log r) (by ring) ?_
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
/-- **Piece `[3.85, 4.1]` (`w ≥ 1`) of region `R1`** (`ptHiS`; moments `mom_3_85_4_1`). -/
private theorem tR1_hi8 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBnd (fun w => OC.gY (w * y) r * HW.phi w) 3.85 4.1
      (1 / Real.sqrt r * (0.0044057308844246 + Real.log r * 0.0009923734499746784 + Real.log r ^ 2 *
          0.0000004597436825052562 + Real.log r ^ 3 * 0.000002786906437503216 + Real.log r ^ 4 *
          0.00000004029812052055342) + 1 / r * (0.09403127803138939 + Real.log r *
          0.03425358395325538 + Real.log r ^ 2 * 0.0006332714217321328) + 0.0000002622419466844462)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Icc (3.85 : ℝ) 4.1, OC.gY (w * y) r * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92659315759620298064011476098944, -0.00023773541485708163488949687440384]
        [0, 0, 0.6608139560777163183243238935004224, -0.0004605119836931666562072328690407168]
        [0, 0, 0.000982445398813685928688204239913472, -0.0001711192021346673349043784065924096]
        [0, 0, 0.001859545188383133426049302917773312, -0.000002244783057744151215312]
        [0, 0, 0.00002676021207842241327264]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00017414336] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 2.92659315759620298064011476098944, -0.00023773541485708163488949687440384]
        [0, 0, 0.6608139560777163183243238935004224, -0.0004605119836931666562072328690407168]
        [0, 0, 0.000982445398813685928688204239913472, -0.0001711192021346673349043784065924096]
        [0, 0, 0.001859545188383133426049302917773312, -0.000002244783057744151215312]
        [0, 0, 0.00002676021207842241327264]
        [0, 0, 62.4420422]
        [0, 0, 22.7463008]
        [0, 0, 0.42052774]
        [0, 0, 0.00017414336] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hτ : 0.379200242 + 0.2516553 * w ≤ Real.log w := log_ge_chord 3.85 4.1 w 0.379200242
        0.2516553 (by norm_num) hw.1 hw.2 (le_trans (by norm_num) lgL163)
        (le_trans (by norm_num) lgL165)
    have hR := rChordHi y r w 19.997138805 2.08 0.379200242 0.2516553 12.69125 13.92004 0.1368759
        0.02252322 (14786 / 12339) 0.787690834295 0.479951139 0.12339 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1, hw.2])
        (by linarith [hw.1, hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
        (by rw [show (1 : ℝ) + (14786 / 12339) = (27125 / 12339) by norm_num]; exact lgU230)
        (by norm_num) (by norm_num)
    have hRs : 0.479951139 + 0.12339 * ((2.08 + Real.log r) * (0.1368759 + 0.02252322 * (Real.log r
        - (0.379200242 + 0.2516553 * w) / 3 - 12.69125)) / 2) ≤ 0.460468894 + (-0.00647615839) *
        Real.log r + (-0.000242453584) * w + 0.00138957006 * Real.log r ^ 2 + (-0.000116564223) * w
        * Real.log r := by
      refine le_of_sub_eq _ _ (0.000000000357606552914848 + 0.0000000000038019196706 * Real.log r +
          0.0000000000003890103632 * w + 0.0000000000021 * Real.log r ^ 2 + 0.00000000000026394729 *
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
/-- **The Gaussian tail `w > 4.1` of region `R1`** (`ptHiS`, `tail_of`, `intBndI_tail`). -/
private theorem tR1_tail (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 4.1
      (1 / Real.sqrt r * (0.003003106754543941 + Real.log r * 0.000676366916928361 + Real.log r ^ 2
          * 0.0000003510030049100403 + Real.log r ^ 3 * 0.000001895416955369732 + Real.log r ^ 4 *
          0.00000002740379553555304) + 1 / r * (0.06409688394198895 + Real.log r *
          0.02334912426178096 + Real.log r ^ 2 * 0.0004316725846158649) + 0.0000001768940587748184)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have hL0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 * r) ≤ 0.6931471808 + Real.log r := by
    rw [Real.log_mul (by norm_num) hr.ne']
    linarith [Real.log_two_lt_d9]
  obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS r 13.16 2.57718192485 0.072649 2.62211565466 (Real.log r)
      1.7810727 0.97252351 0.21048 1.18777 0.6931471808 hr (by norm_num) (by linarith) lgL220
      (by norm_num) (by norm_num) (by norm_num) (by linarith [lgL222]) le_rfl (by norm_num)
      (by norm_num) (by norm_num) Real.log_two_lt_d9.le
  have hSs : Real.sqrt (bigF r) ≤ 2.00056577 + 0.0272346704 * Real.log r := hS.trans (by linarith)
  have hLs : lL r ≤ 62.4420422 + 22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2 := by
    refine hLL.trans (le_of_sub_eq _ _ ((23226242505472367149 / 2812500000000000000000000000) +
        (2557773661510211 / 28125000000000000000000) * Real.log r + 0.000000000607525 *
        Real.log r ^ 2) (by ring) ?_)
    linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
  have key : ∀ w ∈ Set.Ioi (4.1 : ℝ), OC.gY (w * y) r * HW.phi w ≤ (0.70711 * (((0.45942858 +
      (-0.00690839166) * Real.log r + 0.00138625076 * Real.log r ^ 2) * (0.6931471808 + Real.log r)
      + 0.5) * (2.00056577 + 0.0272346704 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (62.4420422 +
      22.7463008 * Real.log r + 0.42052774 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) *
      (w ^ 2 * Real.exp (-w ^ 2 / 2)) ∧ 0 ≤ (0.70711 * (((0.45942858 + (-0.00690839166) * Real.log r
      + 0.00138625076 * Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (2.00056577 +
      0.0272346704 * Real.log r) + 2.5) * (1 / Real.sqrt r) + (62.4420422 + 22.7463008 * Real.log r
      + 0.42052774 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) := by
    intro w hw
    have hw' : (4.1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hτ : 1.41098697297 + 0 * w ≤ Real.log w := by
      have := Real.log_le_log (by norm_num) hw'.le
      linarith [lgL165]
    have hR := rChordHi y r w 19.997138805 2.08 1.41098697297 0 12.69125 13.89907 0.1368759
        0.02244577 (14773 / 12352) 0.786637818917 0.479795509 0.12352 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14773 / 12352) = (27125 / 12352) by norm_num]; exact lgU231)
        (by norm_num) (by norm_num)
    have hRs : 0.479795509 + 0.12352 * ((2.08 + Real.log r) * (0.1368759 + 0.02244577 * (Real.log r
        - (1.41098697297 + 0 * w) / 3 - 12.69125)) / 2) ≤ 0.45942858 + (-0.00690839166) * Real.log r
        + 0.00138625076 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000092231943031094784 + 0.000000000001068341495648 *
          Real.log r + 0.0000000000048 * Real.log r ^ 2) (by ring) ?_
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
  have e : (0.70711 * (((0.45942858 + (-0.00690839166) * Real.log r + 0.00138625076 *
      Real.log r ^ 2) * (0.6931471808 + Real.log r) + 0.5) * (2.00056577 + 0.0272346704 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + (62.4420422 + 22.7463008 * Real.log r + 0.42052774 *
      Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000538522) / 4.1 * ((4.1 ^ 2 + 2) *
      0.000223745793720620415502418151611) = 1 / Real.sqrt r * (((9619326323148560488197 * 10 ^ 40 +
      9896645918312200322898521030863770691551) / (3203125000000000000000000 * 10 ^ 40 + 0)) +
      Real.log r * ((2166487780786156312588472 * 10 ^ 40 + 7049228090324756114026281579735868866643)
      / (3203125000000000000000000000 * 10 ^ 40 + 0)) + Real.log r ^ 2 * ((14053831251280906816965 *
      10 ^ 40 + 218402101880430989477079227770389315237) / (40039062500000000000000000000 * 10 ^ 40
      + 0)) + Real.log r ^ 3 * ((18972679484902101088403 * 10 ^ 40 +
      8149558442142292597880709443277597875167) / (10009765625000000000000000000 * 10 ^ 40 + 0)) +
      Real.log r ^ 4 * ((1755555651496 * 10 ^ 40 + 3666190898899081383472950525779530673861) /
      (64062500000000000000 * 10 ^ 40 + 0))) + 1 / r * ((131398612081077342327820084836561264151401
      / 2050000000000000000000000000000000000000000) + Real.log r *
      (2991606546040685085742166695556464911729 / 128125000000000000000000000000000000000000) +
      Real.log r ^ 2 * (8849287984625229239271184407695009338617 /
      20500000000000000000000000000000000000000000)) + (113322756402617998527060230785268334951 /
      640625000000000000000000000000000000000000000) := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

/-- **Region `R1`, `w > 1`**: the 9 hi pieces and the Gaussian tail, added. -/
theorem hiR1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 1
      (1 / Real.sqrt r * (2.939667507497564771 + Real.log r * 0.6631422577699259904 + Real.log r ^ 2
          * (-0.0008170551063340797502) + Real.log r ^ 3 * 0.001970817265808575517 + Real.log r ^ 4
          * 0.00002861419353736537341) + 1 / r * (62.70915481585364634 + Real.log r *
          22.84360421439219394 + Real.log r ^ 2 * 0.4223266604182437657) + 0.0002051380489076798421)
          := by
  have h0 := tR1_hi0 y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR1_hi1 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR1_hi2 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR1_hi3 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR1_hi4 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR1_hi5 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR1_hi6 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR1_hi7 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR1_hi8 y r hy hr0 hr1)
  have ht := intBndI_add _ _ _ _ _ h8 (tR1_tail y r hy hr0 hr1)
  exact intBndI_mono _ _ _ _ ht (le_of_eq (by ring))

/-- **THE REGION ENVELOPE `R1`**: `g̃(y, r) ≤ P(ℓ)/√r + Q(ℓ)/r + z` on `r ∈ [520000, 1740000]`, `y ≥
    (10 ^ 25)` (`gT_le_of` over `loR1`, `hiR1` and the sliver, divided by `|φ|₁ ≥ 1.2533139`). -/
theorem envR1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    OC.gT HW.phi y r ≤ envF 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033
        0.0000299846672039 65.5968100716 25.1695705188 0.475003664868 0.000211099791842 r := by
  have hr : 0 < r := by linarith
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨hy1, -, -⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  refine (gT_le_of y r _ _ _ hy1 hr (loR1 y r hy hr0 hr1) (hiR1 y r hy hr0 hr1)
    (sliver_bnd r 520000 0.00123274161736 (by norm_num) hr0 (by norm_num))).trans ?_
  rw [div_le_iff₀ (by norm_num), envF_eq]
  have hX : 0 ≤ 1 / Real.sqrt r := one_div_nonneg.mpr (Real.sqrt_nonneg r)
  have hZ : 0 ≤ 1 / r := one_div_nonneg.mpr hr.le
  linarith [hX, hZ, mul_nonneg hX (pow_nonneg hl0 1), mul_nonneg hX (pow_nonneg hl0 2),
      mul_nonneg hX (pow_nonneg hl0 3), mul_nonneg hX (pow_nonneg hl0 4),
      mul_nonneg hZ (pow_nonneg hl0 1), mul_nonneg hZ (pow_nonneg hl0 2)]

/-- **The region envelope `R1` is `≥ 0`** (so its antiderivative `envG` increases). -/
theorem envR1_pos (r : ℝ) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    0 ≤ envF 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033 0.0000299846672039
        65.5968100716 25.1695705188 0.475003664868 0.000211099791842 r := by
  have hr : 0 < r := by linarith
  obtain ⟨hla, hlb⟩ := lr_of r 520000 1740000 13.1615840856 14.3693956763 (by norm_num) hr0 hr1 lgL3
      lgU4
  have hl0 : 0 ≤ Real.log r := by linarith
  refine envF_nonneg _ _ _ _ _ _ _ _ _ r hr ?_ ?_ ?_
  · have := tm_ge_pos 0.689226963225 13.1615840856 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_neg (-0.00106021688168) 14.3693956763 (Real.log r) 2 (by norm_num) hl0 hlb
    have := tm_ge_pos 0.00203455134033 13.1615840856 (Real.log r) 3 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.0000299846672039 13.1615840856 (Real.log r) 4 (by norm_num) (by norm_num)
        hla
    linarith
  · have := tm_ge_pos 25.1695705188 13.1615840856 (Real.log r) 1 (by norm_num) (by norm_num) hla
    have := tm_ge_pos 0.475003664868 13.1615840856 (Real.log r) 2 (by norm_num) (by norm_num) hla
    linarith
  · norm_num

end Principia.Common.TernaryGoldbach.MC
