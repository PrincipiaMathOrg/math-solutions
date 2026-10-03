/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCData

set_option autoImplicit false

/-!
# Region `R2b` of `g̃`, `w ≤ 1`: `r ∈ [3216000, 5950000]`, `y ≥ (10 ^ 26)`

GENERATED. The first piece `[w₁, 0.04]` and 8 pieces on the grid `0.04, 0.09, 0.16, 0.25, 0.36,
    0.49, 0.64, 0.81, 1` of the `w ≤ 1` integral of `gT`, each a certified majorant `(P(w, ℓ)/√r +
    Q(w, ℓ)/r + Y(w))e^{−w²/2}` integrated against the moments of `MNumCData`; their sum is `loR2b`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **The first piece `[w₁, 0.04]` of region `R2b`** (`ptFirstS`, `intBnd_lin`). -/
private theorem tR2b_first (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 0.04
      (1 / Real.sqrt r * (0.0001485792749047571 + Real.log r * 0.00009341779022992975 +
          Real.log r ^ 2 * (-0.0000001109066423376933) + Real.log r ^ 3 * 0.0000001663278895742462 +
          Real.log r ^ 4 * 0.000000006387899652620086) + 1 / r * ((-0.004910942464) + Real.log r *
          0.0139858164 + Real.log r ^ 2 * 0.000541663392) + 0.000000118824704) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  obtain ⟨-, hm0, hm1⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  have key : ∀ w ∈ Set.Icc (max (1 / kK y) (1000 / r)) 0.04, OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * 0.2 * (((0.47102656 + (-0.0108053186) * Real.log r + 0.00122637239 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.72069546 + 0.046039305 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.13867808) + 17.4822705 * Real.log r + 0.67707924
      * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000464159) * w ∧ 0 ≤ (0.70711 * 0.2 * (((0.47102656 +
      (-0.0108053186) * Real.log r + 0.00122637239 * Real.log r ^ 2) * ((-2.52572864) + Real.log r)
      + 0.5) * (1.72069546 + 0.046039305 * Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.13867808) +
      17.4822705 * Real.log r + 0.67707924 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000464159) := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) ((le_max_right _ _).trans hw.1)
    have hwr1 := wr_ge y r w hr hw.1
    have hw1 : w ≤ 1 := le_trans hw.2 (by norm_num)
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hτ : Real.log w ≤ (-3.21887582356) + 0 * w := by
      have := Real.log_le_log hw0 hw.2
      linarith [lgU11]
    have hR := rChordLo y r w 20.7646671384 2.08 (-3.21887582356) 0 12.83773 13.45299 0.1261522
        0.01725341 (12909 / 14216) 0.646087721768 0.460311295 0.14216 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12909 / 14216) = (27125 / 14216) by norm_num]; exact lgU311)
        (by norm_num) (by norm_num)
    have hRs : 0.460311295 + 0.14216 * ((2.08 + Real.log r + ((-3.21887582356) + 0 * w)) *
        (0.1261522 + 0.01725341 * (Real.log r + 2 / 3 * ((-3.21887582356) + 0 * w) - 12.83773)) / 2)
        ≤ 0.47102656 + (-0.0108053186) * Real.log r + 0.00122637239 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000061350945436284833703321728 + (765500998673 /
          37500000000000000000000) * Real.log r + 0.0000000000072 * Real.log r ^ 2) (by ring) ?_
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
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 6.907 1.93253538928 0.11697 2.14583778808
        (Real.log r + (-3.21887582356)) 1.7810727 1.2969336 0.22099 1.13128 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL14 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL313]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.72069546 + 0.046039305 * Real.log r := hS.trans
        (by linarith)
    have hLs : lL (w * r) ≤ (-6.13867808) + 17.4822705 * Real.log r + 0.67707924 * Real.log r ^ 2 :=
        by
      refine hLL.trans (le_of_sub_eq _ _ ((59490750604415952676121959 /
          7500000000000000000000000000000000) + (24430085929033727 / 450000000000000000000000) *
          Real.log r + 0.00000000041325 * Real.log r ^ 2) (by ring) ?_)
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ 0.0000464159 :=
      (wy_rpow_w_le w y (10 ^ 26) hw0 hw1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    exact ptFirstS y r w 0.2 _ _ _ _ _ hy0 hr hw0 hsp hR.1 hRb hL0 hL hSs hLL0 hLs hY
  have hC0 := (key 0.04 ⟨hm1, le_rfl⟩).2
  refine intBnd_mono _ _ _ _ _ (intBnd_lin _ _ 0.04 _ hm0 hm1 hC0 (fun w hw => (key w hw).1)) ?_
  have e : (0.70711 * 0.2 * (((0.47102656 + (-0.0108053186) * Real.log r + 0.00122637239 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.72069546 + 0.046039305 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.13867808) + 17.4822705 * Real.log r + 0.67707924
      * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000464159) * (0.04 ^ 2 / 2) = 1 / Real.sqrt r *
      (0.0001485792749047570578960418471936 + Real.log r * 0.000093417790229929749121939996381184 +
      Real.log r ^ 2 * (-0.0000001109066423376933706652585988096) + Real.log r ^ 3 *
      0.0000001663278895742461734219963433472 + Real.log r ^ 4 * 0.00000000638789965262008550952) +
      1 / r * ((-0.004910942464) + Real.log r * 0.0139858164 + Real.log r ^ 2 * 0.000541663392) +
      0.000000118824704 := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.04, 0.09]` of region `R2b`** (`ptLoS`; moments `mom_0_04_0_09`). -/
private theorem tR2b_lo0 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.04 0.09
      (1 / Real.sqrt r * (0.001161251827161962 + Real.log r * 0.0006110613648909029 + Real.log r ^ 2
          * (-0.000006883925996295264) + Real.log r ^ 3 * 0.000001363045589880441 + Real.log r ^ 4 *
          0.00000002737008481353558) + 1 / r * (0.01361686373364629 + Real.log r *
          0.06426478225298413 + Real.log r ^ 2 * 0.001536775247753077) + 0.00000005615269915621817)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.04 : ℝ) 0.09, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.92257691274569737369072360320390625, -67.708769156801342612052858278669765625,
          90.90655373674355430649954613016266654, 45354.109846492535951854815327733924194858,
          -922896.911010352814893005208383754834560088,
          5903380.64075456000524934078521831939654684, -1531848.5190355721331235045718426727985448,
          1595474.774825733088925644818095038744584, 672051.0674075766392725603395264]
        [0, 0, 8.14328320792287898152907469984471484375,
          -275.3838445800594888583156569325060078125, 6247.9636013153022748953605800395620774369,
          -75963.7392775633692444308309394678922121576,
          395333.2021417694525606413212810025121060828,
          -249324.39664912982883801746059271570571772, 357478.12727561134687364832816280989424808,
          189014.362779736472990737425424368]
        [0, 0, -0.139504081083412019600963352254966015625, 5.323550124975126255593729993386584375,
          -126.62156269450534249767928850375614523426, 1735.51156761175507373593063616711413627312,
          -11727.26456651642224721051179955173996298, 25177.734336023515173104535633546048852432,
          19688.9961289467730954132633110552]
        [0, 0, 0.016168087932873856284521854548899296875, -0.5181446845432519252207921360049765625,
          11.433013293362727993212095484234146885644, -128.7642427207374123721757657271998963428,
          516.1008230082352608663105144499490446984, 902.41232280852140580885873097584]
        [0, 0, 0.00035440192995042577364905078125, -0.011813397665014192454968359375,
          0.2658014476068302732007706225314, -3.16430293878539725938168371718,
          15.38202823305567465738721346604]
        [0, -16.8867778, 300.599041, 121.344455]
        [0, 18.7874401, 15.1680569]
        [0, 0.474001776]
        [0, 0, 0.00025398432] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.92257691274569737369072360320390625, -67.708769156801342612052858278669765625,
          90.90655373674355430649954613016266654, 45354.109846492535951854815327733924194858,
          -922896.911010352814893005208383754834560088,
          5903380.64075456000524934078521831939654684, -1531848.5190355721331235045718426727985448,
          1595474.774825733088925644818095038744584, 672051.0674075766392725603395264]
        [0, 0, 8.14328320792287898152907469984471484375,
          -275.3838445800594888583156569325060078125, 6247.9636013153022748953605800395620774369,
          -75963.7392775633692444308309394678922121576,
          395333.2021417694525606413212810025121060828,
          -249324.39664912982883801746059271570571772, 357478.12727561134687364832816280989424808,
          189014.362779736472990737425424368]
        [0, 0, -0.139504081083412019600963352254966015625, 5.323550124975126255593729993386584375,
          -126.62156269450534249767928850375614523426, 1735.51156761175507373593063616711413627312,
          -11727.26456651642224721051179955173996298, 25177.734336023515173104535633546048852432,
          19688.9961289467730954132633110552]
        [0, 0, 0.016168087932873856284521854548899296875, -0.5181446845432519252207921360049765625,
          11.433013293362727993212095484234146885644, -128.7642427207374123721757657271998963428,
          516.1008230082352608663105144499490446984, 902.41232280852140580885873097584]
        [0, 0, 0.00035440192995042577364905078125, -0.011813397665014192454968359375,
          0.2658014476068302732007706225314, -3.16430293878539725938168371718,
          15.38202823305567465738721346604]
        [0, -16.8867778, 300.599041, 121.344455]
        [0, 18.7874401, 15.1680569]
        [0, 0.474001776]
        [0, 0, 0.00025398432] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.04 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.0625 (-2.7725887212) hw0 (by norm_num) lgU172
    have hτ1 : w / 0.0625 ≤ 16 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.7725887212) + 16 * w := by linarith
    have hwa : Real.log 0.04 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-3.7725887212) 16 12.89525 14.04385 0.1270743
        0.01890748 (13301 / 13824) 0.674049600094 0.463975955 0.13824 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (13301 / 13824) = (27125 / 13824) by norm_num]; exact lgU314)
        (by norm_num) (by norm_num)
    have hRs : 0.463975955 + 0.13824 * ((2.08 + Real.log r + ((-3.7725887212) + 16 * w)) *
        (0.1270743 + 0.01890748 * (Real.log r + 2 / 3 * ((-3.7725887212) + 16 * w) - 12.89525)) / 2)
        ≤ 0.483197207 + (-0.0135681453) * Real.log r + (-0.205292892) * w + 0.00130688502 * Real.log
        r ^ 2 + 0.0348502672 * w * Real.log r + 0.22304171 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.000000000326573570426801961467904 + 0.0000000000661034391552 *
          Real.log r + 0.00000000004061490118656 * w + 0.0000000000024 * Real.log r ^ 2 +
          0.000000000064 * w * Real.log r + 0.0000000003296 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.76 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL20]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.76 2.46470394143 0.081887 2.50241503188
        (Real.log r + (-3.7725887212) + 16 * w) 1.7810727 1.0169051 0.2137 1.16987 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL315 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL317]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.84144274 + 0.0311674399 * Real.log r + 0.498679038 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-16.8867778) + 18.7874401 * Real.log r + 300.599041 * w + 0.474001776 *
        Real.log r ^ 2 + 15.1680569 * w * Real.log r + 121.344455 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((8376954786370431971846147 /
          90000000000000000000000000000000) + (38712720164846087 / 450000000000000000000000) *
          Real.log r + (21837720164846087 / 28125000000000000000000) * w + 0.000000000399075 *
          Real.log r ^ 2 + 0.0000000807704 * w * Real.log r + 0.0000004461632 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000793701 :=
      (wy_rpow_le w y 0.04 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.09, 0.16]` of region `R2b`** (`ptLoS`; moments `mom_0_09_0_16`). -/
private theorem tR2b_lo1 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.09 0.16
      (1 / Real.sqrt r * (0.004973257012972259 + Real.log r * 0.002061655257209481 + Real.log r ^ 2
          * (-0.00002614492177545975) + Real.log r ^ 3 * 0.000005063277555934262 + Real.log r ^ 4 *
          0.00000009046673599905429) + 1 / r * (0.1488375698562637 + Real.log r * 0.1795433637447764
          + Real.log r ^ 2 * 0.003881147514893863) + 0.0000002468335408389792) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.09 : ℝ) 0.16, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.2097306167129949801770651914109375, -61.487088823786714295768449231022030694,
          390.8720025910760130613398278480063040532, 1152.8741490048728343843689545993535704476,
          -24232.46008662233251697604268449765097163432,
          81875.7364982981294212323560090816524630768, -12871.521026051545144948840866818175305604,
          6359.602332477641685805420049457597404088, 1186.8608708113934296327633380740133432]
        [0, 0, 5.564667873765671594277649915170796875, -83.99505403676616333423982578213394004538,
          849.26116656091657925699478517256608641372,
          -4618.920406251626968230510251902519308989372,
          10907.17916985075124874132293257750418265428,
          -4004.4879577463788988205102525562463370574, 2781.0997747745851108083397004684977863948,
          654.25699893065247078360292256762286972]
        [0, 0, -0.1039137414991468632668581494054140625, 1.80195329424791990964918591428117421957,
          -19.20449988042793523307112202532646115003, 119.1720012069170747314710816153881805042,
          -370.0473230219198648309301279216643667465, 382.702632743797324759987593896394397407,
          133.5774592814124654996141936820032423]
        [0, 0, 0.01232778631864846496100439512568125, -0.175548163028815633301897620735763832528,
          1.72136527803767849058594415106311003072, -8.6134333944774817993356189582790848056,
          15.3230642479084619810280462842443703952, 11.99970741521736625604709393344914128]
        [0, 0, 0.0002367270158437202189521875, -0.0035070668789432195192944903512,
          0.035070669078013700221480027568, -0.18555909524624127719004349044,
          0.40089928236471832781944288008]
        [0, -4.02636105, 161.276839, 29.8083227]
        [0, 19.756411, 7.30303843]
        [0, 0.447311066]
        [0, 0, 0.00022187584] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.2097306167129949801770651914109375, -61.487088823786714295768449231022030694,
          390.8720025910760130613398278480063040532, 1152.8741490048728343843689545993535704476,
          -24232.46008662233251697604268449765097163432,
          81875.7364982981294212323560090816524630768, -12871.521026051545144948840866818175305604,
          6359.602332477641685805420049457597404088, 1186.8608708113934296327633380740133432]
        [0, 0, 5.564667873765671594277649915170796875, -83.99505403676616333423982578213394004538,
          849.26116656091657925699478517256608641372,
          -4618.920406251626968230510251902519308989372,
          10907.17916985075124874132293257750418265428,
          -4004.4879577463788988205102525562463370574, 2781.0997747745851108083397004684977863948,
          654.25699893065247078360292256762286972]
        [0, 0, -0.1039137414991468632668581494054140625, 1.80195329424791990964918591428117421957,
          -19.20449988042793523307112202532646115003, 119.1720012069170747314710816153881805042,
          -370.0473230219198648309301279216643667465, 382.702632743797324759987593896394397407,
          133.5774592814124654996141936820032423]
        [0, 0, 0.01232778631864846496100439512568125, -0.175548163028815633301897620735763832528,
          1.72136527803767849058594415106311003072, -8.6134333944774817993356189582790848056,
          15.3230642479084619810280462842443703952, 11.99970741521736625604709393344914128]
        [0, 0, 0.0002367270158437202189521875, -0.0035070668789432195192944903512,
          0.035070669078013700221480027568, -0.18555909524624127719004349044,
          0.40089928236471832781944288008]
        [0, -4.02636105, 161.276839, 29.8083227]
        [0, 19.756411, 7.30303843]
        [0, 0.447311066]
        [0, 0, 0.00022187584] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.09 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.1225 (-2.09964424815) hw0 (by norm_num) lgU178
    have hτ1 : w / 0.1225 ≤ 8.163266 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.09964424815) + 8.163266 * w := by linarith
    have hwa : Real.log 0.09 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-3.09964424815) 8.163266 13.40701 14.40323
        0.1359129 0.02136505 (14046 / 13079) 0.729447921679 0.471552749 0.13079 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14046 / 13079) = (27125 / 13079) by norm_num]; exact lgU318)
        (by norm_num) (by norm_num)
    have hRs : 0.471552749 + 0.13079 * ((2.08 + Real.log r + ((-3.09964424815) + 8.163266 * w)) *
        (0.1359129 + 0.02136505 * (Real.log r + 2 / 3 * ((-3.09964424815) + 8.163266 * w) -
        13.40701)) / 2) ≤ 0.484533802 + (-0.0141555755) * Real.log r + (-0.111679228) * w +
        0.00139716745 * Real.log r ^ 2 + 0.0190090825 * w * Real.log r + 0.0620704788 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000099612821928682940486772875 + (3802911113177 /
          48000000000000000000000) * Real.log r + (15307736997450188041 /
          30000000000000000000000000000) * w + 0.00000000000525 * Real.log r ^ 2 + (3930893 /
          1200000000000000000) * w * Real.log r + (97977462588269 / 1500000000000000000000000) *
          w ^ 2) (by ring) ?_
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
    have hLlo : 12.57 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL36]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.57 2.53131302156 0.077276 2.56037185124
        (Real.log r + (-3.09964424815) + 8.163266 * w) 1.7810727 0.99014622 0.21223 1.17797
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL319 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL321]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.88738379 + 0.0292101008 * Real.log r + 0.238449823 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-4.02636105) + 19.756411 * Real.log r + 161.276839 * w + 0.447311066 *
        Real.log r ^ 2 + 7.30303843 * w * Real.log r + 29.8083227 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((74624590014035348892648001 /
          12000000000000000000000000000000000) + (17214360751686271 / 900000000000000000000000) *
          Real.log r + (431016002917987489360543 / 450000000000000000000000000000) * w +
          0.0000000006131 * Real.log r ^ 2 + 0.0000000070066847692 * w * Real.log r +
          0.0000000724425257745641036 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000693362 :=
      (wy_rpow_le w y 0.09 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.16, 0.25]` of region `R2b`** (`ptLoS`; moments `mom_0_16_0_25`). -/
private theorem tR2b_lo2 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.16 0.25
      (1 / Real.sqrt r * (0.01559651840911114 + Real.log r * 0.0054809375296453 + Real.log r ^ 2 *
          (-0.00007383002883774911) + Real.log r ^ 3 * 0.00001455257132159568 + Real.log r ^ 4 *
          0.000000239784883315932) + 1 / r * (0.4978486611446362 + Real.log r * 0.3845113064912245 +
          Real.log r ^ 2 * 0.007752490177887781) + 0.00000075733666956584) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.16 : ℝ) 0.25, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.3406079783701228917706801111384765625,
          -40.297014463802413519504204618107359497325, 168.33515227626790744367808101161636932738,
          -29.8289984828657910752410740121192685115455,
          -1758.21567491740221705367478343701369045152,
          3824.80892044512452089321317743127467121754, -406.468150030396620040543162404560859523,
          117.2669966614672277907409368428465650535, 12.0371783748518714783121530707926288]
        [0, 0, 4.2311695818957193669812984988020615234375,
          -36.037458953493373640831956880097223171814,
          205.36924279031889147708299919515554029390905,
          -631.27843361898110019161691803139252279768, 851.205897801817069132396709413997261851226,
          -205.86347053723029706854836504394103219214, 84.60056516825592776300760747945342022255,
          10.96887792453601080680177006714043344]
        [0, 0, -0.0836813001598453144575210451111927734375,
          0.82872250881808429371994614772981653646985, -4.9955452054358324462285191839180833882008,
          17.650687783323590394789746667098379374398, -31.492427298429752923074958012585614816736,
          19.22794630980138255539834516563879187791, 3.701996001407203890797672912557423328]
        [0, 0, 0.010187769984568017539746614591095068359375,
          -0.0816555471630561859876982130985583407624, 0.450530586252489393688980897004428699033,
          -1.269291000360053691331751967886834768618, 1.274893218149749775016768761822917113305,
          0.549746361435257631225843523705501744]
        [0, 0, 0.0001790764030216536599204736328125, -0.00149230335705842941446288862456,
          0.0083942064125606871538415814907, -0.0249827570956911725508733824542,
          0.0303609897402735985815273950395]
        [0, 6.13154831, 100.846695, 10.4750004]
        [0, 20.421454, 4.24237479]
        [0, 0.429540413]
        [0, 0, 0.00020158752] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.3406079783701228917706801111384765625,
          -40.297014463802413519504204618107359497325, 168.33515227626790744367808101161636932738,
          -29.8289984828657910752410740121192685115455,
          -1758.21567491740221705367478343701369045152,
          3824.80892044512452089321317743127467121754, -406.468150030396620040543162404560859523,
          117.2669966614672277907409368428465650535, 12.0371783748518714783121530707926288]
        [0, 0, 4.2311695818957193669812984988020615234375,
          -36.037458953493373640831956880097223171814,
          205.36924279031889147708299919515554029390905,
          -631.27843361898110019161691803139252279768, 851.205897801817069132396709413997261851226,
          -205.86347053723029706854836504394103219214, 84.60056516825592776300760747945342022255,
          10.96887792453601080680177006714043344]
        [0, 0, -0.0836813001598453144575210451111927734375,
          0.82872250881808429371994614772981653646985, -4.9955452054358324462285191839180833882008,
          17.650687783323590394789746667098379374398, -31.492427298429752923074958012585614816736,
          19.22794630980138255539834516563879187791, 3.701996001407203890797672912557423328]
        [0, 0, 0.010187769984568017539746614591095068359375,
          -0.0816555471630561859876982130985583407624, 0.450530586252489393688980897004428699033,
          -1.269291000360053691331751967886834768618, 1.274893218149749775016768761822917113305,
          0.549746361435257631225843523705501744]
        [0, 0, 0.0001790764030216536599204736328125, -0.00149230335705842941446288862456,
          0.0083942064125606871538415814907, -0.0249827570956911725508733824542,
          0.0303609897402735985815273950395]
        [0, 6.13154831, 100.846695, 10.4750004]
        [0, 20.421454, 4.24237479]
        [0, 0.429540413]
        [0, 0, 0.00020158752] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.16 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.2025 (-1.59701539181) hw0 (by norm_num) lgU184
    have hτ1 : w / 0.2025 ≤ 4.938272 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.59701539181) + 4.938272 * w := by linarith
    have hwa : Real.log 0.16 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-2.59701539181) 4.938272 13.77905 14.69061
        0.1431513 0.02356763 (2922 / 2503) 0.773527887417 0.47786944 0.12515 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (2922 / 2503) = (5425 / 2503) by norm_num]; exact lgU322)
        (by norm_num) (by norm_num)
    have hRs : 0.47786944 + 0.12515 * ((2.08 + Real.log r + ((-2.59701539181) + 4.938272 * w)) *
        (0.1431513 + 0.02356763 * (Real.log r + 2 / 3 * ((-2.59701539181) + 4.938272 * w) -
        13.77905)) / 2) ≤ 0.485064317 + (-0.0146786398) * Real.log r + (-0.0712320284) * w +
        0.00147474445 * Real.log r ^ 2 + 0.0121378154 * w * Real.log r + 0.0239759335 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000072761333039947283916754285 + 0.0000000000089244135450375 *
          Real.log r + (886342097110845689 / 9375000000000000000000000000) * w + 0.00000000000275 *
          Real.log r ^ 2 + (3623731 / 75000000000000000) * w * Real.log r + (135025291651 /
          5859375000000000000000) * w ^ 2) (by ring) ?_
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
    have hLlo : 13.15 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL52]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.15 2.57642175758 0.074206 2.60091027052
        (Real.log r + (-2.59701539181) + 4.938272 * w) 1.7810727 0.97281045 0.21119 1.18377
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL323 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL325]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.91890342 + 0.0279121969 * Real.log r + 0.137838021 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 6.13154831 + 20.421454 * Real.log r + 100.846695 * w + 0.429540413 *
        Real.log r ^ 2 + 4.24237479 * w * Real.log r + 10.4750004 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((17909991917542906331763734843 /
          1800000000000000000000000000000000000) + (561322989362133817 / 9000000000000000000000000)
          * Real.log r + (230767925041353852773257 / 281250000000000000000000000000) * w +
          0.00000000047735 * Real.log r ^ 2 + 0.0000000059418962784 * w * Real.log r +
          0.0000000951899100092634624 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000629961 :=
      (wy_rpow_le w y 0.16 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.25, 0.36]` of region `R2b`** (`ptLoS`; moments `mom_0_25_0_36`). -/
private theorem tR2b_lo3 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.25 0.36
      (1 / Real.sqrt r * (0.03813530500190435 + Real.log r * 0.01187171537160613 + Real.log r ^ 2 *
          (-0.0001661426226012293) + Real.log r ^ 3 * 0.00003365051326626342 + Real.log r ^ 4 *
          0.0000005222165175856855) + 1 / r * (1.160224525530025 + Real.log r * 0.6960715151663028 +
          Real.log r ^ 2 * 0.01332560849351872) + 0.000001843178998267559) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.25 : ℝ) 0.36, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.153591131129913967122604714925, -26.8762860590688867503857377476108203125,
          76.50128847924982498332714323130146484375, -41.14351168193415937703446277819640234375,
          -223.526854994913395897668945299112890625, 350.315336814495992962476633099606625,
          -27.0421167592155566861383089627775, 5.121280213221849987476260656045,
          0.3281938297388695374039324715]
        [0, 0, 3.4116540943378235011429749459014671875, -18.642362981609329270143346648738636875,
          68.10109769081005802902813687648083234375, -134.474726636538460419390951390648769875,
          117.410640826489283744343269608688751, -20.2361350911717644611123399183415,
          5.51295602147716505897374574956012, 0.446753731056500702179336269124]
        [0, 0, -0.07039968758528093227451721780315421875, 0.4514420327835294593386718451009705,
          -1.7489663074611795896412223358867295, 3.9911439892864388747198544559290816,
          -4.629032774661888886914022766289384, 1.871532401523649290334727166965632,
          0.2252382794695875199855092010464]
        [0, 0, 0.0087943283238604963844188948477010625, -0.04514649023035585608166355809299525,
          0.1594826016124319769706887485705604, -0.287894542189272903347907923125416,
          0.185908625452382894623684405155408, 0.0499653450970109525874881733616]
        [0, 0, 0.000144918980256117722110509375, -0.00077290122803262785125605,
          0.00278244442091746026452178, -0.0052998941350808766943272, 0.0041221398828406818733656]
        [0, 14.546262, 69.1517541, 4.55386992]
        [0, 20.9184001, 2.75509058]
        [0, 0.416707339]
        [0, 0, 0.00018713728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.153591131129913967122604714925, -26.8762860590688867503857377476108203125,
          76.50128847924982498332714323130146484375, -41.14351168193415937703446277819640234375,
          -223.526854994913395897668945299112890625, 350.315336814495992962476633099606625,
          -27.0421167592155566861383089627775, 5.121280213221849987476260656045,
          0.3281938297388695374039324715]
        [0, 0, 3.4116540943378235011429749459014671875, -18.642362981609329270143346648738636875,
          68.10109769081005802902813687648083234375, -134.474726636538460419390951390648769875,
          117.410640826489283744343269608688751, -20.2361350911717644611123399183415,
          5.51295602147716505897374574956012, 0.446753731056500702179336269124]
        [0, 0, -0.07039968758528093227451721780315421875, 0.4514420327835294593386718451009705,
          -1.7489663074611795896412223358867295, 3.9911439892864388747198544559290816,
          -4.629032774661888886914022766289384, 1.871532401523649290334727166965632,
          0.2252382794695875199855092010464]
        [0, 0, 0.0087943283238604963844188948477010625, -0.04514649023035585608166355809299525,
          0.1594826016124319769706887485705604, -0.287894542189272903347907923125416,
          0.185908625452382894623684405155408, 0.0499653450970109525874881733616]
        [0, 0, 0.000144918980256117722110509375, -0.00077290122803262785125605,
          0.00278244442091746026452178, -0.0052998941350808766943272, 0.0041221398828406818733656]
        [0, 14.546262, 69.1517541, 4.55386992]
        [0, 20.9184001, 2.75509058]
        [0, 0.416707339]
        [0, 0, 0.00018713728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.25 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.3025 (-1.19567400084) hw0 (by norm_num) lgU190
    have hτ1 : w / 0.3025 ≤ 3.305786 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.19567400084) + 3.305786 * w := by linarith
    have hwa : Real.log 0.25 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-2.19567400084) 3.305786 14.07083 14.92851
        0.1493912 0.02559746 (3013 / 2412) 0.810561620921 0.48336484 0.1206 hy0 hr hw0 (by linarith)
        hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (3013 / 2412) = (5425 / 2412) by norm_num]; exact lgU326)
        (by norm_num) (by norm_num)
    have hRs : 0.48336484 + 0.1206 * ((2.08 + Real.log r + ((-2.19567400084) + 3.305786 * w)) *
        (0.1493912 + 0.02559746 * (Real.log r + 2 / 3 * ((-2.19567400084) + 3.305786 * w) -
        14.07083)) / 2) ≤ 0.485096457 + (-0.0151483481) * Real.log r + (-0.0498804523) * w +
        0.00154352684 * Real.log r ^ 2 + 0.00850428236 * w * Real.log r + 0.0112453351 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000000866090623864798019354048 + 0.0000000000345544975732 *
          Real.log r + 0.00000000001353191745050282816 * w + 0.000000000002 * Real.log r ^ 2 +
          0.00000000000719222 * w * Real.log r + 0.000000000083216392073968 * w ^ 2) (by ring) ?_
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
    have hLlo : 13.59 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL68]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.59 2.60933422712 0.071989 2.63124195042
        (Real.log r + (-2.19567400084) + 3.305786 * w) 1.7810727 0.96054004 0.2104 1.18822
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL327 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL329]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.9423728 + 0.0269769921 * Real.log r + 0.0891801625 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 14.546262 + 20.9184001 * Real.log r + 69.1517541 * w + 0.416707339 *
        Real.log r ^ 2 + 2.75509058 * w * Real.log r + 4.55386992 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((11952203215476060230164298089 /
          225000000000000000000000000000000000) + (128714953114194731 / 4500000000000000000000000) *
          Real.log r + (3550194997780671506783 / 2250000000000000000000000000000) * w +
          0.000000000549025 * Real.log r ^ 2 + 0.0000000089030103173 * w * Real.log r +
          0.0000000006677834323929489 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000584804 :=
      (wy_rpow_le w y 0.25 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.36, 0.49]` of region `R2b`** (`ptLoS`; moments `mom_0_36_0_49`). -/
private theorem tR2b_lo4 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.36 0.49
      (1 / Real.sqrt r * (0.07803075013277014 + Real.log r * 0.02210238156676278 + Real.log r ^ 2 *
          (-0.0003180417177653044) + Real.log r ^ 3 * 0.00006631820722500437 + Real.log r ^ 4 *
          0.0000009808099567743462) + 1 / r * (2.203770134286427 + Real.log r * 1.115306348126584 +
          Real.log r ^ 2 * 0.02047705514687888) + 0.000003794653075412619) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.36 : ℝ) 0.49, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.872706656166989555670929981765625, -18.693040303699240630049690446697529573,
          38.268378669466938545524139608943305471665, -20.299934413189716910654794595044034928925,
          -40.5938775501561212729306845542828414371728,
          49.2947335097250766351613933939703013479074, -2.908910059743983976531645582086801231925,
          0.389737788568827181231202339713609337972, 0.01691080232638165330736000756351031168]
        [0, 0, 2.855926452384093489138359643661171875, -10.859394286454417762689261155189216540015,
          27.5853099828495790409154393798960661208235,
          -37.9449064348757123496262504198762997457234,
          23.2301126636408696905955597813539473163532, -3.0140842605769408529503525859144519525275,
          0.585551223029769366977395663110637482246, 0.03215166162102244470914729412639439424]
        [0, 0, -0.0610004513519146882922173395480703125,
          0.2742419085052658786316788791369602387465, -0.7403384830407080680906779114167932426122,
          1.1817942321815922490089747680133329850666, -0.9635845081817741700485743872820272914725,
          0.277695571775915430925266012682213913098, 0.02264012749277896355604832597957880512]
        [0, 0, 0.00780627700834361305034917506811875, -0.0278517619722640092124705183371048662976,
          0.0683530277476599031557673105109260521408, -0.08579063132874903256276716664505527,
          0.038653467086128347536738482258129916224, 0.00701466589382280725870580625142054656]
        [0, 0, 0.000122184120743682139267125, -0.000452533779870163798124111054976,
          0.001131334452654374724870527890048, -0.00149647414191011999903811213472,
          0.00080828078877814037368497202304]
        [0, 21.7455598, 50.4507516, 2.27701692]
        [0, 21.3154417, 1.92407922]
        [0, 0.406461718]
        [0, 0, 0.00017610304] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.872706656166989555670929981765625, -18.693040303699240630049690446697529573,
          38.268378669466938545524139608943305471665, -20.299934413189716910654794595044034928925,
          -40.5938775501561212729306845542828414371728,
          49.2947335097250766351613933939703013479074, -2.908910059743983976531645582086801231925,
          0.389737788568827181231202339713609337972, 0.01691080232638165330736000756351031168]
        [0, 0, 2.855926452384093489138359643661171875, -10.859394286454417762689261155189216540015,
          27.5853099828495790409154393798960661208235,
          -37.9449064348757123496262504198762997457234,
          23.2301126636408696905955597813539473163532, -3.0140842605769408529503525859144519525275,
          0.585551223029769366977395663110637482246, 0.03215166162102244470914729412639439424]
        [0, 0, -0.0610004513519146882922173395480703125,
          0.2742419085052658786316788791369602387465, -0.7403384830407080680906779114167932426122,
          1.1817942321815922490089747680133329850666, -0.9635845081817741700485743872820272914725,
          0.277695571775915430925266012682213913098, 0.02264012749277896355604832597957880512]
        [0, 0, 0.00780627700834361305034917506811875, -0.0278517619722640092124705183371048662976,
          0.0683530277476599031557673105109260521408, -0.08579063132874903256276716664505527,
          0.038653467086128347536738482258129916224, 0.00701466589382280725870580625142054656]
        [0, 0, 0.000122184120743682139267125, -0.000452533779870163798124111054976,
          0.001131334452654374724870527890048, -0.00149647414191011999903811213472,
          0.00080828078877814037368497202304]
        [0, 21.7455598, 50.4507516, 2.27701692]
        [0, 21.3154417, 1.92407922]
        [0, 0.406461718]
        [0, 0, 0.00017610304] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.36 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.4225 (-0.861565831581) hw0 (by norm_num) lgU196
    have hτ1 : w / 0.4225 ≤ 2.366864 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.861565831581) + 2.366864 * w := by linarith
    have hwa : Real.log 0.36 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-1.861565831581) 2.366864 14.31065 15.13104
        0.1549423 0.02750306 (15447 / 11678) 0.842749082634 0.488275689 0.11678 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15447 / 11678) = (27125 / 11678) by norm_num]; exact lgU330)
        (by norm_num) (by norm_num)
    have hRs : 0.488275689 + 0.11678 * ((2.08 + Real.log r + ((-1.861565831581) + 2.366864 * w)) *
        (0.1549423 + 0.02750306 * (Real.log r + 2 / 3 * ((-1.861565831581) + 2.366864 * w) -
        14.31065)) / 2) ≤ 0.484796592 + (-0.0155766572) * Real.log r + (-0.037144582) * w +
        0.00160590368 * Real.log r ^ 2 + 0.00633492599 * w * Real.log r + 0.00599756331 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000004270553220783728163265657484 + (34268398148227 /
          3000000000000000000000000) * Real.log r + (12196519827611571883 /
          234375000000000000000000000000) * w + 0.0000000000066 * Real.log r ^ 2 + (613057 /
          187500000000000000) * w * Real.log r + (168087033953 / 29296875000000000000000) * w ^ 2)
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
    have hLlo : 13.96 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL84]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.96 2.63619609629 0.070219 2.6561363503
        (Real.log r + (-1.861565831581) + 2.366864 * w) 1.7810727 0.95075249 0.20976 1.19184
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL331 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL333]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.96116307 + 0.0262336646 * Real.log r + 0.0620915164 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 21.7455598 + 21.3154417 * Real.log r + 50.4507516 * w + 0.406461718 *
        Real.log r ^ 2 + 1.92407922 * w * Real.log r + 2.27701692 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((20158875326750535202025726108519 /
          360000000000000000000000000000000000000) + (7651608049858355501 /
          180000000000000000000000000) * Real.log r + (1088820727207496670907429 /
          11250000000000000000000000000000) * w + 0.000000000255775 * Real.log r ^ 2 +
          0.0000000057860652792 * w * Real.log r + 0.0000000073643748054942144 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000550322 :=
      (wy_rpow_le w y 0.36 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.49, 0.64]` of region `R2b`** (`ptLoS`; moments `mom_0_49_0_64`). -/
private theorem tR2b_lo5 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.49 0.64
      (1 / Real.sqrt r * (0.1389464528767841 + Real.log r * 0.03644199864060584 + Real.log r ^ 2 *
          (-0.0005355398909562362) + Real.log r ^ 3 * 0.0001150346635576195 + Real.log r ^ 4 *
          0.000001635591484526005) + 1 / r * (3.623151486748958 + Real.log r * 1.61753229977007 +
          Real.log r ^ 2 * 0.02869505630643123) + 0.000006838553752428539) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.49 : ℝ) 0.64, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.5724709247180199127589081362751953125,
          -13.520606673205575273840968068754201600715, 20.8075621785866903703529218135906545969845,
          -9.634293728360523380706336430453292038235224,
          -9.4281562632707931052958441508202047893188008,
          9.342825418646238084980658108744738868524424,
          -0.437437758368289489625432540847933966928968,
          0.0436918594687109874054233581356623807576576, 0.0013605560611588057202555484428308268544]
        [0, 0, 2.453349926690700504317829864557208984375,
          -6.86571559498156679675634158527445760335985,
          12.828290722036464343195548967312329704228263,
          -12.999135733174123904390770700426977306355399,
          5.89527527220979226280156193089906281966368,
          -0.599148115022077946256279293010392701384366,
          0.087352917395996340994293397369918221734848, 0.003443907097952702747041631835389070912]
        [0, 0, -0.0539410296512125955838359666309994140625,
          0.179624472500625016891301832852317673923445,
          -0.3572949928189583673722494773891405153371756,
          0.421599179145838542361560750303420914882678,
          -0.255129937023261967669550032851908357088912,
          0.0551716521718125797806375170293724668229632, 0.0032286625035524506109825442155008478208]
        [0, 0, 0.007062407921932870191638814568142578125,
          -0.01852644394944430089571050897477880168065, 0.0334170806295991674110254498311105121595,
          -0.0308490342777410592180714324494284248155, 0.0102559320263657346575263760309533782368,
          0.0013318231186202838537369975729285792]
        [0, 0, 0.000106004529245146453119140625, -0.00028844769860778819931279252245,
          0.0005298018974942672652905139935, -0.0005148706463939405926419419815,
          0.0002043137488466175632586074064]
        [0, 28.0429322, 38.4748584, 1.25844068]
        [0, 21.6421051, 1.41574558]
        [0, 0.398178394]
        [0, 0, 0.00016728256] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.5724709247180199127589081362751953125,
          -13.520606673205575273840968068754201600715, 20.8075621785866903703529218135906545969845,
          -9.634293728360523380706336430453292038235224,
          -9.4281562632707931052958441508202047893188008,
          9.342825418646238084980658108744738868524424,
          -0.437437758368289489625432540847933966928968,
          0.0436918594687109874054233581356623807576576, 0.0013605560611588057202555484428308268544]
        [0, 0, 2.453349926690700504317829864557208984375,
          -6.86571559498156679675634158527445760335985,
          12.828290722036464343195548967312329704228263,
          -12.999135733174123904390770700426977306355399,
          5.89527527220979226280156193089906281966368,
          -0.599148115022077946256279293010392701384366,
          0.087352917395996340994293397369918221734848, 0.003443907097952702747041631835389070912]
        [0, 0, -0.0539410296512125955838359666309994140625,
          0.179624472500625016891301832852317673923445,
          -0.3572949928189583673722494773891405153371756,
          0.421599179145838542361560750303420914882678,
          -0.255129937023261967669550032851908357088912,
          0.0551716521718125797806375170293724668229632, 0.0032286625035524506109825442155008478208]
        [0, 0, 0.007062407921932870191638814568142578125,
          -0.01852644394944430089571050897477880168065, 0.0334170806295991674110254498311105121595,
          -0.0308490342777410592180714324494284248155, 0.0102559320263657346575263760309533782368,
          0.0013318231186202838537369975729285792]
        [0, 0, 0.000106004529245146453119140625, -0.00028844769860778819931279252245,
          0.0005298018974942672652905139935, -0.0005148706463939405926419419815,
          0.0002043137488466175632586074064]
        [0, 28.0429322, 38.4748584, 1.25844068]
        [0, 21.6421051, 1.41574558]
        [0, 0.398178394]
        [0, 0, 0.00016728256] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.49 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.5625 (-0.575364144352) hw0 (by norm_num) lgU202
    have hτ1 : w / 0.5625 ≤ 1.777778 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.575364144352) + 1.777778 * w := by linarith
    have hwa : Real.log 0.49 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-1.575364144352) 1.777778 14.51414 15.30718
        0.1599866 0.02931494 (15776 / 11349) 0.871326178478 0.492737226 0.11349 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15776 / 11349) = (27125 / 11349) by norm_num]; exact lgU334)
        (by norm_num) (by norm_num)
    have hRs : 0.492737226 + 0.11349 * ((2.08 + Real.log r + ((-1.575364144352) + 1.777778 * w)) *
        (0.1599866 + 0.02931494 * (Real.log r + 2 / 3 * ((-1.575364144352) + 1.777778 * w) -
        14.51414)) / 2) ≤ 0.484253015 + (-0.0159730919) * Real.log r + (-0.0288940633) * w +
        0.00166347628 * Real.log r ^ 2 + 0.0049288192 * w * Real.log r + 0.00350493854 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000004022024666756678290297812992 + 0.000000000099939734950576
          * Real.log r + 0.0000000000278061691469072801024 * w + 0.0000000000097 * Real.log r ^ 2 +
          0.000000000005231011 * w * Real.log r + 0.0000000000078247905094232 * w ^ 2) (by ring) ?_
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
    have hLlo : 14.27 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL100]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.27 2.65815943044 0.068788 2.67672596883
        (Real.log r + (-1.575364144352) + 1.777778 * w) 1.7810727 0.9428968 0.20923 1.19486
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL335 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL337]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.97659761 + 0.0256341125 * Real.log r + 0.0455717612 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 28.0429322 + 21.6421051 * Real.log r + 38.4748584 * w + 0.398178394 *
        Real.log r ^ 2 + 1.41574558 * w * Real.log r + 1.25844068 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ (0.0000000546670497427180928053146202112 +
          (12576168911473781 / 2812500000000000000000000) * Real.log r + (123020974457551017719309 /
          1406250000000000000000000000000) * w + 0.0000000001153 * Real.log r ^ 2 +
          0.0000000025528916068 * w * Real.log r + 0.0000000094086172674768452 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000522758 :=
      (wy_rpow_le w y 0.49 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.64, 0.81]` of region `R2b`** (`ptLoS`; moments `mom_0_64_0_81`). -/
private theorem tR2b_lo6 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.64 0.81
      (1 / Real.sqrt r * (0.2198102422115286 + Real.log r * 0.0540358169408482 + Real.log r ^ 2 *
          (-0.0008072442235075407) + Real.log r ^ 3 * 0.0001786087902088366 + Real.log r ^ 4 *
          0.000002457754120979482) + 1 / r * (5.298698735051531 + Real.log r * 2.14518806963941 +
          Real.log r ^ 2 * 0.03697966129456294) + 0.00001098394654679426) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.64 : ℝ) 0.81, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.279543220716124040728480025770883737916,
          -10.10796325066990115403504308370591171189424,
          12.107086040586247730446694264091542035488736,
          -4.7692103916900126541844312602012907641578392,
          -2.620155634494778351229407601085594975551924,
          2.203848067733421955795230516729620053942782,
          -0.0842262190945302850175794493055729232012118,
          0.0065184957707207186505434600963810408206724, 0.0001521854102423844824055443952167991792]
        [0, 0, 2.147834047521553735482616271871819675027,
          -4.609083193795062893077089475264114315239412,
          6.6002690674721859062924312297617630079032436,
          -5.132757283987990393829091688909145260481178,
          1.795158794084685151632196594504822411738578,
          -0.1472783268691315948147156739116580883040501,
          0.0167337753742856186498064460287849520452758, 0.0004947924732330306376375469798595473064]
        [0, 0, -0.04841744923773498176819932906008427602354,
          0.124335922838363225544670947146923473105746,
          -0.18983634347278856243105532994910188820378,
          0.17241614190952487547724429715786458554015,
          -0.0805822646750648275802990005132110240145835,
          0.013580001573064773493655079481272042720513, 0.000595812191739345552323030465150252604]
        [0, 0, 0.00647848320204589500718246895312956059523,
          -0.01302017770919646624032998901334889065815,
          0.017986884873776364617244517936344376428925,
          -0.0127255011585100896141615787904345205423175,
          0.003251488632570870718337125456590969845065, 0.00031568094165402503992516438920205302]
        [0, 0, 0.00009392406685115135596897527401, -0.00019567513876435239213509438405,
          0.000275168164459860100840281093975, -0.0002047382171569754983554474468725,
          0.000062203451705397157402463530155]
        [0, 33.642183, 30.3352828, 0.749778455]
        [0, 21.9172267, 1.08342912]
        [0, 0.3913885]
        [0, 0, 0.00016] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.279543220716124040728480025770883737916,
          -10.10796325066990115403504308370591171189424,
          12.107086040586247730446694264091542035488736,
          -4.7692103916900126541844312602012907641578392,
          -2.620155634494778351229407601085594975551924,
          2.203848067733421955795230516729620053942782,
          -0.0842262190945302850175794493055729232012118,
          0.0065184957707207186505434600963810408206724, 0.0001521854102423844824055443952167991792]
        [0, 0, 2.147834047521553735482616271871819675027,
          -4.609083193795062893077089475264114315239412,
          6.6002690674721859062924312297617630079032436,
          -5.132757283987990393829091688909145260481178,
          1.795158794084685151632196594504822411738578,
          -0.1472783268691315948147156739116580883040501,
          0.0167337753742856186498064460287849520452758, 0.0004947924732330306376375469798595473064]
        [0, 0, -0.04841744923773498176819932906008427602354,
          0.124335922838363225544670947146923473105746,
          -0.18983634347278856243105532994910188820378,
          0.17241614190952487547724429715786458554015,
          -0.0805822646750648275802990005132110240145835,
          0.013580001573064773493655079481272042720513, 0.000595812191739345552323030465150252604]
        [0, 0, 0.00647848320204589500718246895312956059523,
          -0.01302017770919646624032998901334889065815,
          0.017986884873776364617244517936344376428925,
          -0.0127255011585100896141615787904345205423175,
          0.003251488632570870718337125456590969845065, 0.00031568094165402503992516438920205302]
        [0, 0, 0.00009392406685115135596897527401, -0.00019567513876435239213509438405,
          0.000275168164459860100840281093975, -0.0002047382171569754983554474468725,
          0.000062203451705397157402463530155]
        [0, 33.642183, 30.3352828, 0.749778455]
        [0, 21.9172267, 1.08342912]
        [0, 0.3913885]
        [0, 0, 0.00016] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.64 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.7225 (-0.325037858537) hw0 (by norm_num) lgU208
    have hτ1 : w / 0.7225 ≤ 1.384084 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.325037858537) + 1.384084 * w := by linarith
    have hwa : Real.log 0.64 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-1.325037858537) 1.384084 14.69083 15.46295
        0.1646406 0.03105416 (459 / 316) 0.897120816265 0.496844022 0.1106 hy0 hr hw0 (by linarith)
        hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (459 / 316) = (775 / 316) by norm_num]; exact lgU338) (by norm_num)
        (by norm_num)
    have hRs : 0.496844022 + 0.1106 * ((2.08 + Real.log r + ((-1.325037858537) + 1.384084 * w)) *
        (0.1646406 + 0.03105416 * (Real.log r + 2 / 3 * ((-1.325037858537) + 1.384084 * w) -
        14.69083)) / 2) ≤ 0.483525847 + (-0.0163443589) * Real.log r + (-0.0232201173) * w +
        0.00171729505 * Real.log r ^ 2 + 0.00396146767 * w * Real.log r + 0.00219320161 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.000000000200768075495459907704458192 + 0.00000000008496669770796 *
          Real.log r + (1962749489444952037 / 23437500000000000000000000000) * w + 0.000000000002 *
          Real.log r ^ 2 + (86999 / 18750000000000000) * w * Real.log r + (60270918479 /
          11718750000000000000000) * w ^ 2) (by ring) ?_
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
    have hLlo : 14.53 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL116]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.53 2.67621547654 0.067615 2.69392542803
        (Real.log r + (-1.325037858537) + 1.384084 * w) 1.7810727 0.93653521 0.20879 1.19738
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL339 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL341]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.98952277 + 0.0251440015 * Real.log r + 0.0348014102 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 33.642183 + 21.9172267 * Real.log r + 30.3352828 * w + 0.3913885 *
        Real.log r ^ 2 + 1.08342912 * w * Real.log r + 0.749778455 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((937052063379011317524899746567 /
          72000000000000000000000000000000000000) + (1151510318521021009 /
          36000000000000000000000000) * Real.log r + (399861551924962210555189 /
          9000000000000000000000000000000) * w + 0.000000000515875 * Real.log r ^ 2 +
          0.000000000160028667 * w * Real.log r + 0.000000000047706558768014 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.00005 :=
      (wy_rpow_le w y 0.64 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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
/-- **Piece `[0.81, 1]` of region `R2b`** (`ptLoS`; moments `mom_0_81_1`). -/
private theorem tR2b_lo7 (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.81 1
      (1 / Real.sqrt r * (0.3119727390214792 + Real.log r * 0.07253479658432017 + Real.log r ^ 2 *
          (-0.001098963186220176) + Real.log r ^ 3 * 0.0002501549658070449 + Real.log r ^ 4 *
          0.000003343970771311828) + 1 / r * (6.977514753651505 + Real.log r * 2.609401054704544 +
          Real.log r ^ 2 * 0.04385418171634044) + 0.00001585395007254482) := by
  obtain ⟨hla, hlb⟩ := lr_of r 3216000 5950000 14.9836489035 15.5989017831 (by norm_num) hr0 hr1
      lgL7 lgU8
  have hkd := kD_ge y (10 ^ 26) 59.867211 (by norm_num) hy MN.lya_ge_3
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.81 : ℝ) 1, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.0035758009644046450530243667090234375, -7.76711643615232687045934190403015717559,
          7.4428847002619521597609371362795754834286, -2.48985671242259583687766822993232367779188,
          -0.8347600149124318187931344803211536512312,
          0.6148738874109006828499867428527334766567904,
          -0.0196243486897168726726609966713344430184418,
          0.00121206813742670575950264985750048667560496,
          0.00002191026495796136858742108568679514848]
        [0, 0, 1.908156111566983493238701684300117578125,
          -3.2399257605727101237058462288887765442509, 3.66933210442574703111860671129184512802719,
          -2.259470628612741156660937966251012907742734,
          0.6284929828968211666553551946731047272118368,
          -0.0426354281633426842794371675742196213035322,
          0.00388570920070158108884957341757413827150287,
          0.00008898300239581433700194637823658465406]
        [0, 0, -0.0439994015048822266848511180144048046875,
          0.08985333360634778994372864163073710392767,
          -0.108641224658963686402095245069457897670392,
          0.0783290922904891258571901211162240802321106,
          -0.029146160548383111934732944008615891520936,
          0.00394048100352094620228974390297879969540519,
          0.00013384517436173128086043531643576346222]
        [0, 0, 0.006007743447533361609633594947290515625,
          -0.009546100387814863831891078153795903936448,
          0.0104231790560871731568915358560216149245152,
          -0.0058320986322245630829757888688384720879436,
          0.00118169155620993352204137408163727800501668,
          0.00008858313730563883558072581219767221384]
        [0, 0, 0.000084471289768542033781265625, -0.000139047390362094821690532380736,
          0.0001544971006769263121100742090464, -0.0000908272196155336561083153402252,
          0.00002180351640492886160722830306276]
        [0, 38.6930098, 24.5507588, 0.473139145]
        [0, 22.1570447, 0.854015571]
        [0, 0.385374263]
        [0, 0, 0.00015384] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.0035758009644046450530243667090234375, -7.76711643615232687045934190403015717559,
          7.4428847002619521597609371362795754834286, -2.48985671242259583687766822993232367779188,
          -0.8347600149124318187931344803211536512312,
          0.6148738874109006828499867428527334766567904,
          -0.0196243486897168726726609966713344430184418,
          0.00121206813742670575950264985750048667560496,
          0.00002191026495796136858742108568679514848]
        [0, 0, 1.908156111566983493238701684300117578125,
          -3.2399257605727101237058462288887765442509, 3.66933210442574703111860671129184512802719,
          -2.259470628612741156660937966251012907742734,
          0.6284929828968211666553551946731047272118368,
          -0.0426354281633426842794371675742196213035322,
          0.00388570920070158108884957341757413827150287,
          0.00008898300239581433700194637823658465406]
        [0, 0, -0.0439994015048822266848511180144048046875,
          0.08985333360634778994372864163073710392767,
          -0.108641224658963686402095245069457897670392,
          0.0783290922904891258571901211162240802321106,
          -0.029146160548383111934732944008615891520936,
          0.00394048100352094620228974390297879969540519,
          0.00013384517436173128086043531643576346222]
        [0, 0, 0.006007743447533361609633594947290515625,
          -0.009546100387814863831891078153795903936448,
          0.0104231790560871731568915358560216149245152,
          -0.0058320986322245630829757888688384720879436,
          0.00118169155620993352204137408163727800501668,
          0.00008858313730563883558072581219767221384]
        [0, 0, 0.000084471289768542033781265625, -0.000139047390362094821690532380736,
          0.0001544971006769263121100742090464, -0.0000908272196155336561083153402252,
          0.00002180351640492886160722830306276]
        [0, 38.6930098, 24.5507588, 0.473139145]
        [0, 22.1570447, 0.854015571]
        [0, 0.385374263]
        [0, 0, 0.00015384] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.81 : ℝ) * 3216000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.9025 (-0.102586588552) hw0 (by norm_num) lgU214
    have hτ1 : w / 0.9025 ≤ 1.108034 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.102586588552) + 1.108034 * w := by linarith
    have hwa : Real.log 0.81 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 20.7646671384 2.08 (-1.102586588552) 1.108034 14.84692 15.60254
        0.1689833 0.0327351 (16323 / 10802) 0.920724510392 0.500666524 0.10802 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (16323 / 10802) = (27125 / 10802) by norm_num]; exact lgU342)
        (by norm_num) (by norm_num)
    have hRs : 0.500666524 + 0.10802 * ((2.08 + Real.log r + ((-1.102586588552) + 1.108034 * w)) *
        (0.1689833 + 0.0327351 * (Real.log r + 2 / 3 * ((-1.102586588552) + 1.108034 * w) -
        14.84692)) / 2) ≤ 0.482660123 + (-0.0166944139) * Real.log r + (-0.0191362387) * w +
        0.00176802276 * Real.log r ^ 2 + 0.00326504887 * w * Real.log r + 0.00144711407 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.000000000594186934399113875393684864 + 0.00000000004304260691092 *
          Real.log r + 0.000000000069515098175803465024 * w + 0.000000000009 * Real.log r ^ 2 +
          0.00000000000186411 * w * Real.log r + 0.000000000006977566903896 * w ^ 2) (by ring) ?_
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
    have hLlo : 14.77 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL132]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.77 2.6925980955 0.066576 2.70941112772
        (Real.log r + (-1.102586588552) + 1.108034 * w) 1.7810727 0.93083703 0.20839 1.19968
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL343 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL345]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 2.00087317 + 0.0247101977 * Real.log r + 0.0273797392 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 38.6930098 + 22.1570447 * Real.log r + 24.5507588 * w + 0.385374263 *
        Real.log r ^ 2 + 0.854015571 * w * Real.log r + 0.473139145 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((30544015830448176197774913161 /
          351562500000000000000000000000000000) + (130721177680945381 / 1406250000000000000000000) *
          Real.log r + (25228145320264317145477 / 703125000000000000000000000000) * w +
          0.0000000007556 * Real.log r ^ 2 + 0.0000000004165769808 * w * Real.log r +
          0.0000000006320837291718736 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.000048075 :=
      (wy_rpow_le w y 0.81 (10 ^ 26) (by norm_num) hw.1 (by norm_num) hy).trans
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

/-- **Region `R2b`, `w ≤ 1`**: the first piece and the 8 lo pieces, added. -/
theorem loR2b (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 1
      (1 / Real.sqrt r * (0.8087750957686165081 + Real.log r * 0.20523378104611873365 +
          Real.log r ^ 2 * (-0.0030329014243023284173) + Real.log r ^ 3 * 0.0006649123624217534192 +
          Real.log r ^ 4 * 0.000009304352454958488656) + 1 / r * (19.91875178753899219 + Real.log r
          * 8.82580455629589583 + Real.log r ^ 2 * 0.157043639290266931) +
          0.00004049343005900883437) := by
  have h0 := tR2b_first y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR2b_lo0 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR2b_lo1 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR2b_lo2 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR2b_lo3 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR2b_lo4 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR2b_lo5 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR2b_lo6 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR2b_lo7 y r hy hr0 hr1)
  exact intBnd_mono _ _ _ _ _ h8 (le_of_eq (by ring))

end Principia.Common.TernaryGoldbach.MC
