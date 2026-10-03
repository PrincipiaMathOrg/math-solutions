/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCData

set_option autoImplicit false

/-!
# Region `R2a` of `g̃`, `w ≤ 1`: `r ∈ [1740000, 3216400]`, `y ≥ (10 ^ 25)`

GENERATED. The first piece `[w₁, 0.04]` and 16 pieces on the grid `0.04, 0.0625, 0.09, 0.1225, 0.16,
    0.2025, 0.25, 0.3025, 0.36, 0.4225, 0.49, 0.5625, 0.64, 0.7225, 0.81, 0.9025, 1` of the `w ≤ 1`
    integral of `gT`, each a certified majorant `(P(w, ℓ)/√r + Q(w, ℓ)/r + Y(w))e^{−w²/2}`
    integrated against the moments of `MNumCData`; their sum is `loR2a`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **The first piece `[w₁, 0.04]` of region `R2a`** (`ptFirstS`, `intBnd_lin`). -/
private theorem tR2a_first (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 0.04
      (1 / Real.sqrt r * (0.0001556127861923518 + Real.log r * 0.00008831600180066158 +
          Real.log r ^ 2 * 0.0000003079318795179673 + Real.log r ^ 3 * 0.0000001585942170010624 +
          Real.log r ^ 4 * 0.000000007760098891918598) + 1 / r * ((-0.004830017024) + Real.log r *
          0.0132469564 + Real.log r ^ 2 * 0.0006064481304) + 0.000000174411008) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  obtain ⟨-, hm0, hm1⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  have key : ∀ w ∈ Set.Icc (max (1 / kK y) (1000 / r)) 0.04, OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * 0.2 * (((0.468347483 + (-0.0108889125) * Real.log r + 0.00130422108 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.64671232 + 0.0525907154 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.03752128) + 16.5586955 * Real.log r +
      0.758060163 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000681293) * w ∧ 0 ≤ (0.70711 * 0.2 *
      (((0.468347483 + (-0.0108889125) * Real.log r + 0.00130422108 * Real.log r ^ 2) *
      ((-2.52572864) + Real.log r) + 0.5) * (1.64671232 + 0.0525907154 * Real.log r) + 2.5) * (1 /
      Real.sqrt r) + ((-6.03752128) + 16.5586955 * Real.log r + 0.758060163 * Real.log r ^ 2) * (1 /
      r) + 3.2 * 0.0000681293) := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) ((le_max_right _ _).trans hw.1)
    have hwr1 := wr_ge y r w hr hw.1
    have hw1 : w ≤ 1 := le_trans hw.2 (by norm_num)
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hτ : Real.log w ≤ (-3.21887582356) + 0 * w := by
      have := Real.log_le_log hw0 hw.2
      linarith [lgU11]
    have hR := rChordLo y r w 19.997138805 2.08 (-3.21887582356) 0 12.22347 12.83786 0.1286394
        0.01796819 (12608 / 14517) 0.625135436042 0.457637988 0.14517 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12608 / 14517) = (27125 / 14517) by norm_num]; exact lgU232)
        (by norm_num) (by norm_num)
    have hRs : 0.457637988 + 0.14517 * ((2.08 + Real.log r + ((-3.21887582356) + 0 * w)) *
        (0.1286394 + 0.01796819 * (Real.log r + 2 / 3 * ((-3.21887582356) + 0 * w) - 12.22347)) / 2)
        ≤ 0.468347483 + (-0.0108889125) * Real.log r + 0.00130422108 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000018772657671245304800034224 + 0.00000000008374832651049 *
          Real.log r + 0.00000000000885 * Real.log r ^ 2) (by ring) ?_
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
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 6.907 1.93253538928 0.13096 2.03286334667
        (Real.log r + (-3.21887582356)) 1.7810727 1.2969336 0.22547 1.1088 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL14 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL234]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.64671232 + 0.0525907154 * Real.log r := hS.trans
        (by linarith)
    have hLs : lL (w * r) ≤ (-6.03752128) + 16.5586955 * Real.log r + 0.758060163 * Real.log r ^ 2
        := by
      refine hLL.trans (le_of_sub_eq _ _ ((2640886633033151841457507 /
          468750000000000000000000000000000) + (9265127075755409 / 112500000000000000000000) *
          Real.log r + 0.000000000426 * Real.log r ^ 2) (by ring) ?_)
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ 0.0000681293 :=
      (wy_rpow_w_le w y (10 ^ 25) hw0 hw1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    exact ptFirstS y r w 0.2 _ _ _ _ _ hy0 hr hw0 hsp hR.1 hRb hL0 hL hSs hLL0 hLs hY
  have hC0 := (key 0.04 ⟨hm1, le_rfl⟩).2
  refine intBnd_mono _ _ _ _ _ (intBnd_lin _ _ 0.04 _ hm0 hm1 hC0 (fun w hw => (key w hw).1)) ?_
  have e : (0.70711 * 0.2 * (((0.468347483 + (-0.0108889125) * Real.log r + 0.00130422108 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.64671232 + 0.0525907154 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-6.03752128) + 16.5586955 * Real.log r +
      0.758060163 * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000681293) * (0.04 ^ 2 / 2) = 1 / Real.sqrt
      r * (0.00015561278619235178728938022895616 + Real.log r *
      0.0000883160018006615720095748119037952 + Real.log r ^ 2 *
      0.0000003079318795179672097717904905216 + Real.log r ^ 3 *
      0.000000158594217001062395152514867453952 + Real.log r ^ 4 *
      0.0000000077600988919185971989632) + 1 / r * ((-0.004830017024) + Real.log r * 0.0132469564 +
      Real.log r ^ 2 * 0.0006064481304) + 0.000000174411008 := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.04, 0.0625]` of region `R2a`** (`ptLoS`; moments `mom_0_04_0_0625`). -/
private theorem tR2a_lo0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.04 0.0625
      (1 / Real.sqrt r * (0.000276572469438423 + Real.log r * 0.0001640675933744524 + Real.log r ^ 2
          * (-0.000001722547101953483) + Real.log r ^ 3 * 0.0000003716360551610699 + Real.log r ^ 4
          * 0.000000008571815914391482) + 1 / r * ((-0.001462593656231745) + Real.log r *
          0.02198006271570998 + Real.log r ^ 2 * 0.0005892115982276788) + 0.00000002235376319024123)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.04 : ℝ) 0.0625, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 4.92462841343001457132736913499453125, -9.7088256145918165269522346953946875,
          -1489.7259627400965221995209996902933548425, 73104.6182312522807093989808647371740489795,
          -1193896.981163315065097510407453738754874536,
          7069573.768580447918021294618391117122801358,
          -2143172.8430726689919223654823696499714202, 2815324.6904261634968146167139377719061588,
          1767394.3462654764445587286742618920044]
        [0, 0, 7.8630164346263835474780353537656640625, -266.353674978207503735145628212313734375,
          6052.640897651338231529052715967275873880125,
          -73839.6611675500115259844228077888284556257,
          389147.6292057478498820680277225407000059573,
          -299137.00279259378176399195541973785702513, 507782.72638901853687942115936605081813078,
          402634.45151783272467783731079492457914]
        [0, 0, -0.125573795043689815718130934974966796875,
          5.00043590587282227820289087595059296875, -120.5523830277972133474515483020666449933,
          1706.08594199672546611690273138893414085036, -12136.806461938703246449618868997239983432,
          28369.175364966840290544587449925783061496, 33972.275702345955316966144785403366248]
        [0, 0, 0.01586920746121270721588085196413955078125,
          -0.499915061586821392280647600216728515625, 10.933288253904564216430410841230236711445,
          -119.8954616578247786542342128844638344865, 429.316611108144101155208886140038043727,
          1261.220507717490640482477987092643801]
        [0, 0, 0.000401205636182873844012919921875, -0.0133735212060957948004306640625,
          0.3009042273001849748554291542115, -3.58219317205275115782839580505,
          17.4134390969295414879933825789]
        [0, -20.3698562, 356.246582, 199.647003]
        [0, 18.03498, 20.2142553]
        [0, 0.511673245]
        [0, 0, 0.0003728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 4.92462841343001457132736913499453125, -9.7088256145918165269522346953946875,
          -1489.7259627400965221995209996902933548425, 73104.6182312522807093989808647371740489795,
          -1193896.981163315065097510407453738754874536,
          7069573.768580447918021294618391117122801358,
          -2143172.8430726689919223654823696499714202, 2815324.6904261634968146167139377719061588,
          1767394.3462654764445587286742618920044]
        [0, 0, 7.8630164346263835474780353537656640625, -266.353674978207503735145628212313734375,
          6052.640897651338231529052715967275873880125,
          -73839.6611675500115259844228077888284556257,
          389147.6292057478498820680277225407000059573,
          -299137.00279259378176399195541973785702513, 507782.72638901853687942115936605081813078,
          402634.45151783272467783731079492457914]
        [0, 0, -0.125573795043689815718130934974966796875,
          5.00043590587282227820289087595059296875, -120.5523830277972133474515483020666449933,
          1706.08594199672546611690273138893414085036, -12136.806461938703246449618868997239983432,
          28369.175364966840290544587449925783061496, 33972.275702345955316966144785403366248]
        [0, 0, 0.01586920746121270721588085196413955078125,
          -0.499915061586821392280647600216728515625, 10.933288253904564216430410841230236711445,
          -119.8954616578247786542342128844638344865, 429.316611108144101155208886140038043727,
          1261.220507717490640482477987092643801]
        [0, 0, 0.000401205636182873844012919921875, -0.0133735212060957948004306640625,
          0.3009042273001849748554291542115, -3.58219317205275115782839580505,
          17.4134390969295414879933825789]
        [0, -20.3698562, 356.246582, 199.647003]
        [0, 18.03498, 20.2142553]
        [0, 0.511673245]
        [0, 0, 0.0003728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.04 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.050625 (-2.98330975251) hw0 (by norm_num) lgU18
    have hτ1 : w / 0.050625 ≤ 19.75309 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.98330975251) + 19.75309 * w := by linarith
    have hwa : Real.log 0.04 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.98330975251) 19.75309 12.2406 13.15128 0.1289235
        0.01883232 (12722 / 14403) 0.633019294045 0.458636484 0.14403 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12722 / 14403) = (27125 / 14403) by norm_num]; exact lgU235)
        (by norm_num) (by norm_num)
    have hRs : 0.458636484 + 0.14403 * ((2.08 + Real.log r + ((-3.98330975251) + 19.75309 * w)) *
        (0.1289235 + 0.01883232 * (Real.log r + 2 / 3 * ((-3.98330975251) + 19.75309 * w) -
        12.2406)) / 2) ≤ 0.479416556 + (-0.0134991476) * Real.log r + (-0.249653748) * w +
        0.00135620953 * Real.log r ^ 2 + 0.0446488814 * w * Real.log r + 0.352781349 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000092103822066266391535787168 + 0.00000000008948753451208 *
          Real.log r + 0.00000000097624448901601786176 * w + 0.0000000000052 * Real.log r ^ 2 +
          0.00000000006294728 * w * Real.log r + 0.00000000041995091483808 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 12.3046875 + (-410.15625) * w + 9228.51563 * w ^ 2 + (-109863.281) *
        w ^ 3 + 534057.618 * w ^ 4 := by
      refine (isq_le 0.2 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0.000005 * w ^ 2 + 0.00025 * w ^ 3 + 0.0008125 * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-3.29016257) + Real.log r + 19.75309 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-3.98330975251) + 19.75309 * w := by
      rw [hwl]
      linarith
    have hLlo : 11.15 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL20]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.15 2.41143949699 0.088395 2.42593987294
        (Real.log r + (-3.98330975251) + 19.75309 * w) 1.7810727 1.0393668 0.21596 1.15763
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL236 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL238]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.79513213 + 0.0340002935 * Real.log r + 0.671610858 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-20.3698562) + 18.03498 * Real.log r + 356.246582 * w + 0.511673245 *
        Real.log r ^ 2 + 20.2142553 * w * Real.log r + 199.647003 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((5016567327172093828075463753 /
          240000000000000000000000000000000000) + (347091954868482151 / 3600000000000000000000000) *
          Real.log r + (293861862279306609209659 / 360000000000000000000000000000) * w +
          0.000000000721375 * Real.log r ^ 2 + 0.0000000103446705975 * w * Real.log r +
          0.0000009902311046663856375 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_04_0_0625
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
/-- **Piece `[0.0625, 0.09]` of region `R2a`** (`ptLoS`; moments `mom_0_0625_0_09`). -/
private theorem tR2a_lo1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.0625 0.09
      (1 / Real.sqrt r * (0.000741177735843976 + Real.log r * 0.0003683017412209026 + Real.log r ^ 2
          * (-0.000004196643481141576) + Real.log r ^ 3 * 0.0000008890802206311035 + Real.log r ^ 4
          * 0.00000001889572484115055) + 1 / r * (0.01338019542267488 + Real.log r *
          0.04115866495535502 + Real.log r ^ 2 * 0.001030745169885195) + 0.00000005576178214681686)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.0625 : ℝ) 0.09, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.1113803143484716320078839580075, -45.881529014149166315651128760592,
          60.15489425815387186602814159924575, 11985.77403605680415008388365146493485,
          -158188.9978377880017170098496398137906, 655504.387731869931780080299197512512,
          -150388.754615268084115331418342118912, 125577.87090654674719965737526099968,
          47595.3693070800528389308102656]
        [0, 0, 6.4158708213714753461623945742805375, -139.43820822776895333285155929181805,
          2031.05699432775341239746015646527381375, -15917.160543313954240036433616966244275,
          54322.78247354625748251909934254543072, -30534.8371468239730715697584350605952,
          33778.9162608827021839198635788877824, 16197.287456893232574436739396608]
        [0, 0, -0.10994763129822488089369551103324875, 2.8233769144964542387446229674007209375,
          -43.68920282748818107088357644210229475, 398.147826390379089261316125674587824,
          -1832.87637207067981414367452497902656, 2823.22668558930255716500245434933248,
          2041.5316386529261838663335932416]
        [0, 0, 0.01388408472070313237881935892153453125, -0.280645425613276762534068929270210625,
          3.933492015283236509317433758170408, -27.72022913194144750614633538227168,
          64.70872147198918205576416312569856, 113.2198607929227118782714205952]
        [0, 0, 0.0003206851436188037843725078125, -0.0068412830638678140666135,
          0.0985144761196965225592344, -0.750586484721497314737024, 2.335157952466880534737408]
        [0, -13.1573095, 247.043216, 86.2088989]
        [0, 18.6826298, 13.0390866]
        [0, 0.493040107]
        [0, 0, 0.0003460768] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.1113803143484716320078839580075, -45.881529014149166315651128760592,
          60.15489425815387186602814159924575, 11985.77403605680415008388365146493485,
          -158188.9978377880017170098496398137906, 655504.387731869931780080299197512512,
          -150388.754615268084115331418342118912, 125577.87090654674719965737526099968,
          47595.3693070800528389308102656]
        [0, 0, 6.4158708213714753461623945742805375, -139.43820822776895333285155929181805,
          2031.05699432775341239746015646527381375, -15917.160543313954240036433616966244275,
          54322.78247354625748251909934254543072, -30534.8371468239730715697584350605952,
          33778.9162608827021839198635788877824, 16197.287456893232574436739396608]
        [0, 0, -0.10994763129822488089369551103324875, 2.8233769144964542387446229674007209375,
          -43.68920282748818107088357644210229475, 398.147826390379089261316125674587824,
          -1832.87637207067981414367452497902656, 2823.22668558930255716500245434933248,
          2041.5316386529261838663335932416]
        [0, 0, 0.01388408472070313237881935892153453125, -0.280645425613276762534068929270210625,
          3.933492015283236509317433758170408, -27.72022913194144750614633538227168,
          64.70872147198918205576416312569856, 113.2198607929227118782714205952]
        [0, 0, 0.0003206851436188037843725078125, -0.0068412830638678140666135,
          0.0985144761196965225592344, -0.750586484721497314737024, 2.335157952466880534737408]
        [0, -13.1573095, 247.043216, 86.2088989]
        [0, 18.6826298, 13.0390866]
        [0, 0.493040107]
        [0, 0, 0.0003460768] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.0625 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.075625 (-2.58196836159) hw0 (by norm_num) lgU26
    have hτ1 : w / 0.075625 ≤ 13.22315 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.58196836159) + 13.22315 * w := by linarith
    have hwa : Real.log 0.0625 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.58196836159) 13.22315 12.53238 13.38919
        0.1339629 0.02027287 (1884 / 1991) 0.665908638415 0.462897719 0.13937 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (1884 / 1991) = (3875 / 1991) by norm_num]; exact lgU239)
        (by norm_num) (by norm_num)
    have hRs : 0.462897719 + 0.13937 * ((2.08 + Real.log r + ((-3.58196836159) + 13.22315 * w)) *
        (0.1339629 + 0.02027287 * (Real.log r + 2 / 3 * ((-3.58196836159) + 13.22315 * w) -
        12.53238)) / 2) ≤ 0.480535348 + (-0.0138648624) * Real.log r + (-0.173984628) * w +
        0.00141271495 * Real.log r ^ 2 + 0.0311342361 * w * Real.log r + 0.16467707 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000049938589076286628165905587 + (112975087012121 /
          1200000000000000000000000) * Real.log r + (29514484638479456023 /
          30000000000000000000000000000) * w + 0.00000000000405 * Real.log r ^ 2 + (8984503 /
          240000000000000000) * w * Real.log r + (6764636616889 / 12000000000000000000000) * w ^ 2)
          (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 9.84375 + (-210) * w + 3024 * w ^ 2 + (-23040) * w ^ 3 + 71680 * w ^
        4 := by
      refine (isq_le 0.25 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-2.88882118) + Real.log r + 13.22315 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-3.58196836159) + 13.22315 * w := by
      rw [hwl]
      linarith
    have hLlo : 11.59 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL28]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.59 2.45014265631 0.085176 2.46303557595
        (Real.log r + (-3.58196836159) + 13.22315 * w) 1.7810727 1.0229486 0.21497 1.16296
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL126 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL241]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.82621126 + 0.0326119483 * Real.log r + 0.431232684 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-13.1573095) + 18.6826298 * Real.log r + 247.043216 * w + 0.493040107 *
        Real.log r ^ 2 + 13.0390866 * w * Real.log r + 86.2088989 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((39735720774447540049941020227 /
          450000000000000000000000000000000000) + (200859138705057127 / 2250000000000000000000000) *
          Real.log r + (42325660399355522977801 / 45000000000000000000000000000) * w +
          0.0000000000406 * Real.log r ^ 2 + 0.00000001931961978 * w * Real.log r +
          0.0000000403381151469535 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.000108149 :=
      (wy_rpow_le w y 0.0625 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_0625_0_09
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
/-- **Piece `[0.09, 0.1225]` of region `R2a`** (`ptLoS`; moments `mom_0_09_0_1225`). -/
private theorem tR2a_lo2 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.09 0.1225
      (1 / Real.sqrt r * (0.001655622128870592 + Real.log r * 0.00072157969710492 + Real.log r ^ 2 *
          (-0.000008701053548593003) + Real.log r ^ 3 * 0.000001838377823118087 + Real.log r ^ 4 *
          0.00000003662706270711613) + 1 / r * (0.04486137177501104 + Real.log r *
          0.06922889246841804 + Real.log r ^ 2 * 0.001642364742633145) + 0.000000119714379325104) :=
          by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.09 : ℝ) 0.1225, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.66934185897155118046900461448125, -47.611985255868309856870164116490685164,
          222.5796687533129524594820609591116858138, 2467.28593746605218598544052912466333098365,
          -29971.64084518871254867827496219030712075661,
          93151.2558342358819337816419953818353184814,
          -16743.1784319093505377143073280383110755695, 9695.762221564471225899367692287217890199,
          2427.6098274029355996867565689212494656]
        [0, 0, 5.42289703479519912694927553919834375, -82.01167438983765454919495568350236467462,
          830.63351125192569877297543763625243351527,
          -4534.348908000892391753936403837690553995666,
          10849.65493556790232171351372346350904428984,
          -4662.9363969840530737420775760205572293387, 3639.0282406397222759685969995878256450694,
          1153.87325104566383559499472390515527936]
        [0, 0, -0.0979434074906880449431227750459796875, 1.757740130716739774355717353354610973071,
          -18.934287543410017329409929642231731231639, 120.43721098414986084370751763255006532546,
          -388.52675883950186191276964546692264151245, 425.4242947491900354437951335741704309141,
          203.12976226851238867697536584095536704]
        [0, 0, 0.01243468942322488841917146437048390625,
          -0.1749267958479031112110858102103005078356, 1.704534377202519415932677795855215061544,
          -8.37054569366302477537543528082034328262, 13.77561892670805306525153398641646516604,
          15.734092216389938819334269993390990976]
        [0, 0, 0.000267639068833266595546921875, -0.00396502321659817118539282464444,
          0.0396502324922464814792437153016, -0.209789589448604854648333947378,
          0.453249115845956940114886991796]
        [0, -6.88542876, 181.723045, 42.8777925]
        [0, 19.1944958, 9.05793329]
        [0, 0.478372083]
        [0, 0, 0.0003256704] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.66934185897155118046900461448125, -47.611985255868309856870164116490685164,
          222.5796687533129524594820609591116858138, 2467.28593746605218598544052912466333098365,
          -29971.64084518871254867827496219030712075661,
          93151.2558342358819337816419953818353184814,
          -16743.1784319093505377143073280383110755695, 9695.762221564471225899367692287217890199,
          2427.6098274029355996867565689212494656]
        [0, 0, 5.42289703479519912694927553919834375, -82.01167438983765454919495568350236467462,
          830.63351125192569877297543763625243351527,
          -4534.348908000892391753936403837690553995666,
          10849.65493556790232171351372346350904428984,
          -4662.9363969840530737420775760205572293387, 3639.0282406397222759685969995878256450694,
          1153.87325104566383559499472390515527936]
        [0, 0, -0.0979434074906880449431227750459796875, 1.757740130716739774355717353354610973071,
          -18.934287543410017329409929642231731231639, 120.43721098414986084370751763255006532546,
          -388.52675883950186191276964546692264151245, 425.4242947491900354437951335741704309141,
          203.12976226851238867697536584095536704]
        [0, 0, 0.01243468942322488841917146437048390625,
          -0.1749267958479031112110858102103005078356, 1.704534377202519415932677795855215061544,
          -8.37054569366302477537543528082034328262, 13.77561892670805306525153398641646516604,
          15.734092216389938819334269993390990976]
        [0, 0, 0.000267639068833266595546921875, -0.00396502321659817118539282464444,
          0.0396502324922464814792437153016, -0.209789589448604854648333947378,
          0.453249115845956940114886991796]
        [0, -6.88542876, 181.723045, 42.8777925]
        [0, 19.1944958, 9.05793329]
        [0, 0.478372083]
        [0, 0, 0.0003256704] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.09 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.105625 (-2.24786019246) hw0 (by norm_num) lgU34
    have hτ1 : w / 0.105625 ≤ 9.467456 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.24786019246) + 9.467456 * w := by linarith
    have hwa : Real.log 0.09 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.24786019246) 9.467456 12.7722 13.59171 0.1384095
        0.02160813 (13577 / 13548) 0.694216877146 0.466686328 0.13548 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (13577 / 13548) = (27125 / 13548) by norm_num]; exact lgU242)
        (by norm_num) (by norm_num)
    have hRs : 0.466686328 + 0.13548 * ((2.08 + Real.log r + ((-3.24786019246) + 9.467456 * w)) *
        (0.1384095 + 0.02160813 * (Real.log r + 2 / 3 * ((-3.24786019246) + 9.467456 * w) -
        12.7722)) / 2) ≤ 0.481271256 + (-0.0141980278) * Real.log r + (-0.129024528) * w +
        0.00146373473 * Real.log r ^ 2 + 0.0230964069 * w * Real.log r + 0.0874656863 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000052128852198955979201277872 + 0.00000000002538616900742 *
          Real.log r + 0.000000000891499890815418018816 * w + 0.0000000000038 * Real.log r ^ 2 +
          0.000000000040049088 * w * Real.log r + 0.0000000000181266313920512 * w ^ 2) (by ring) ?_
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
    have hL : Real.log (2 * (w * r)) ≤ (-2.55471301) + Real.log r + 9.467456 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-3.24786019246) + 9.467456 * w := by
      rw [hwl]
      linarith
    have hLlo : 11.96 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL36]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.96 2.48156774748 0.082642 2.49323725409
        (Real.log r + (-3.24786019246) + 9.467456 * w) 1.7810727 1.0099946 0.21416 1.16736
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL243 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL245]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.85085198 + 0.0315225124 * Real.log r + 0.298437999 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-6.88542876) + 19.1944958 * Real.log r + 181.723045 * w + 0.478372083 *
        Real.log r ^ 2 + 9.05793329 * w * Real.log r + 42.8777925 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((4078610941652957547016015189 /
          450000000000000000000000000000000000) + (73099988448195077 / 4500000000000000000000000) *
          Real.log r + (50984208191153049545533 / 70312500000000000000000000000) * w +
          0.00000000026145 * Real.log r ^ 2 + 0.0000000000888367424 * w * Real.log r +
          0.0000000634154089749276672 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_09_0_1225
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
/-- **Piece `[0.1225, 0.16]` of region `R2a`** (`ptLoS`; moments `mom_0_1225_0_16`). -/
private theorem tR2a_lo3 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.1225 0.16
      (1 / Real.sqrt r * (0.003257301713976649 + Real.log r * 0.001280421558122562 + Real.log r ^ 2
          * (-0.00001606422720135293) + Real.log r ^ 3 * 0.000003418277967951592 + Real.log r ^ 4 *
          0.00000006472643166250255) + 1 / r * (0.09938786708841798 + Real.log r *
          0.1077553468242155 + Real.log r ^ 2 * 0.002448647181674617) + 0.0000002304379073870758) :=
          by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.1225 : ℝ) 0.16, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.916462012883859839356896940753125, -41.9559867204678796527921753255848939112,
          186.63775244693555772392775841241191527744, 557.928978631136122810343475196126977121456,
          -7270.914642963159406465902863010919120497488,
          17794.50284396470979751162830451154382439872,
          -2574.8023030892864805318352926674567812064, 1097.2134690290444544432802626429298058368,
          193.82066779619785793087558362001440512]
        [0, 0, 4.6957260179460197727618491352234375, -52.2614454476954117553526024626489891388,
          389.302075037510468930221035915330458914368,
          -1565.30062107131868032848970597422332958132, 2773.5122943194084508223106266934316793998,
          -942.1699735109284322573166330801522996488, 547.93280713942943809356682546287525612,
          122.652126221055875135078712776713336]
        [0, 0, -0.088263962558672367825922801741875, 1.17046021591564819021950875188198169568,
          -9.2830615942285771996204426286123192213024, 43.577036916598382938740448165716365191056,
          -104.09752410877996923532527865431636770784, 85.39055386505636967899518460482175313984,
          28.746588506313409762799557195417494656]
        [0, 0, 0.01131295974191777772437749631679375, -0.1171261565897693199857865308173791845168,
          0.839265563229363451620723954568986308392, -3.03620857818667038644176073129505211888,
          3.71436448790596539109950444905308105888, 2.964491568364450783342432104042774592]
        [0, 0, 0.00023042422365075032326734375, -0.00250801875935312230812412038476,
          0.0184262602962066247117364275034, -0.071627833883570327925104707076,
          0.113694974813703668254046121416]
        [0, -1.33214225, 139.428909, 23.6150999]
        [0, 19.6071879, 6.641746]
        [0, 0.466997708]
        [0, 0, 0.00030935776] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.916462012883859839356896940753125, -41.9559867204678796527921753255848939112,
          186.63775244693555772392775841241191527744, 557.928978631136122810343475196126977121456,
          -7270.914642963159406465902863010919120497488,
          17794.50284396470979751162830451154382439872,
          -2574.8023030892864805318352926674567812064, 1097.2134690290444544432802626429298058368,
          193.82066779619785793087558362001440512]
        [0, 0, 4.6957260179460197727618491352234375, -52.2614454476954117553526024626489891388,
          389.302075037510468930221035915330458914368,
          -1565.30062107131868032848970597422332958132, 2773.5122943194084508223106266934316793998,
          -942.1699735109284322573166330801522996488, 547.93280713942943809356682546287525612,
          122.652126221055875135078712776713336]
        [0, 0, -0.088263962558672367825922801741875, 1.17046021591564819021950875188198169568,
          -9.2830615942285771996204426286123192213024, 43.577036916598382938740448165716365191056,
          -104.09752410877996923532527865431636770784, 85.39055386505636967899518460482175313984,
          28.746588506313409762799557195417494656]
        [0, 0, 0.01131295974191777772437749631679375, -0.1171261565897693199857865308173791845168,
          0.839265563229363451620723954568986308392, -3.03620857818667038644176073129505211888,
          3.71436448790596539109950444905308105888, 2.964491568364450783342432104042774592]
        [0, 0, 0.00023042422365075032326734375, -0.00250801875935312230812412038476,
          0.0184262602962066247117364275034, -0.071627833883570327925104707076,
          0.113694974813703668254046121416]
        [0, -1.33214225, 139.428909, 23.6150999]
        [0, 19.6071879, 6.641746]
        [0, 0.466997708]
        [0, 0, 0.00030935776] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.1225 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.140625 (-1.96165850521) hw0 (by norm_num) lgU42
    have hτ1 : w / 0.140625 ≤ 7.111112 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.96165850521) + 7.111112 * w := by linarith
    have hwa : Real.log 0.1225 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.96165850521) 7.111112 12.97569 13.76786
        0.1424208 0.02286306 (13911 / 13214) 0.719178938894 0.470117288 0.13214 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (13911 / 13214) = (27125 / 13214) by norm_num]; exact lgU246)
        (by norm_num) (by norm_num)
    have hRs : 0.470117288 + 0.13214 * ((2.08 + Real.log r + ((-2.96165850521) + 7.111112 * w)) *
        (0.1424208 + 0.02286306 * (Real.log r + 2 / 3 * ((-2.96165850521) + 7.111112 * w) -
        12.97569)) / 2) ≤ 0.481731693 + (-0.0145051602) * Real.log r + (-0.0999909592) * w +
        0.00151056238 * Real.log r ^ 2 + 0.0179029638 * w * Real.log r + 0.0509239921 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000002027785182790301199631852 + 0.00000000007094659911597 *
          Real.log r + 0.000000000019997007823046126912 * w + 0.0000000000058 * Real.log r ^ 2 +
          0.000000000090129816 * w * Real.log r + 0.0000000000708710464461568 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 7.03125 + (-76.5306122) * w + 562.265723 * w ^ 2 + (-2185.67822) * w
        ^ 3 + 3469.33052 * w ^ 4 := by
      refine (isq_le 0.35 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((11 / 245000000) * w + (923 / 2401000000) * w ^ 2 + (83327 /
          41177150000) * w ^ 3 + (1275663 / 144120025000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-2.26851132) + Real.log r + 7.111112 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.96165850521) + 7.111112 * w := by
      rw [hwl]
      linarith
    have hLlo : 12.26 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL44]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.26 2.50634192946 0.080677 2.5173017515
        (Real.log r + (-2.96165850521) + 7.111112 * w) 1.7810727 1.0000112 0.21352 1.17086
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL247 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL249]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.87053739 + 0.030681031 * Real.log r + 0.218176248 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-1.33214225) + 19.6071879 * Real.log r + 139.428909 * w + 0.466997708 *
        Real.log r ^ 2 + 6.641746 * w * Real.log r + 23.6150999 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((25937036692730994581257088497 /
          3600000000000000000000000000000000000) + (420361866348181223 / 18000000000000000000000000)
          * Real.log r + (9279239016368459131247 / 2250000000000000000000000000000) * w +
          0.000000000791825 * Real.log r ^ 2 + 0.0000000005989205188 * w * Real.log r +
          0.0000000613534954441424528 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000966743 :=
      (wy_rpow_le w y 0.1225 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_1225_0_16
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
/-- **Piece `[0.16, 0.2025]` of region `R2a`** (`ptLoS`; moments `mom_0_16_0_2025`). -/
private theorem tR2a_lo4 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.16 0.2025
      (1 / Real.sqrt r * (0.005833193874626935 + Real.log r * 0.00210785479471713 + Real.log r ^ 2 *
          (-0.00002730024137942368) + Real.log r ^ 3 * 0.000005868174730870278 + Real.log r ^ 4 *
          0.0000001063747592511536) + 1 / r * (0.1836063716945354 + Real.log r * 0.1581820180560835
          + Real.log r ^ 2 * 0.003464008569438608) + 0.0000004080984535493015) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.16 : ℝ) 0.2025, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.99455565383771206904834064449267578125,
          -35.392444731674776591635993967347204398875, 134.949193517085493194126645118027856208335,
          116.207059925787036283002363194567276449984,
          -2116.700873406089397605308671410526350367592,
          4227.60579986326408713208558981714522563172, -504.58044164134224071862143557199813245564,
          164.9764038554744610178314356315783253744, 21.51004262786409697264763070815402856]
        [0, 0, 4.140922309311158098896850198037103515625,
          -35.337121148454042766440978872788346053006,
          201.7264428654095172311966989045708514952156,
          -622.3785278284330435925769789060294325295568,
          850.137530224538762739575710745406190776328,
          -234.667075646278891498742596085589234446256, 105.77618927863242185680726017885144005576,
          17.483628943397107220798337196344754824]
        [0, 0, -0.08050044287356771723262780662942734375,
          0.8214140394395515534712743026591178031664, -4.9972225292909302342613649728843956505376,
          18.03012645385814255149641399351094107312, -33.199855264700836091234355200367343972752,
          21.19819981036615173882470607583982763552, 5.263300013993381719064107606862979648]
        [0, 0, 0.01042424921988353615084134204645125, -0.08275668017854600051224832137028197019392,
          0.4543694898018951525557272696929951359744, -1.2615228738733489560231445949577910137344,
          1.193679586069381473861032898970065272704, 0.6971678434782065812434216297544180096]
        [0, 0, 0.000202565811952601640514125, -0.001688048431292097865875929921536,
          0.00949527245894303326372100737792, -0.02825973936550074429163142692352,
          0.0343434334990493887867676067712]
        [0, 3.65322984, 110.493165, 14.014804]
        [0, 19.9578249, 5.0628472]
        [0, 0.45723832]
        [0, 0, 0.00029588992] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.99455565383771206904834064449267578125,
          -35.392444731674776591635993967347204398875, 134.949193517085493194126645118027856208335,
          116.207059925787036283002363194567276449984,
          -2116.700873406089397605308671410526350367592,
          4227.60579986326408713208558981714522563172, -504.58044164134224071862143557199813245564,
          164.9764038554744610178314356315783253744, 21.51004262786409697264763070815402856]
        [0, 0, 4.140922309311158098896850198037103515625,
          -35.337121148454042766440978872788346053006,
          201.7264428654095172311966989045708514952156,
          -622.3785278284330435925769789060294325295568,
          850.137530224538762739575710745406190776328,
          -234.667075646278891498742596085589234446256, 105.77618927863242185680726017885144005576,
          17.483628943397107220798337196344754824]
        [0, 0, -0.08050044287356771723262780662942734375,
          0.8214140394395515534712743026591178031664, -4.9972225292909302342613649728843956505376,
          18.03012645385814255149641399351094107312, -33.199855264700836091234355200367343972752,
          21.19819981036615173882470607583982763552, 5.263300013993381719064107606862979648]
        [0, 0, 0.01042424921988353615084134204645125, -0.08275668017854600051224832137028197019392,
          0.4543694898018951525557272696929951359744, -1.2615228738733489560231445949577910137344,
          1.193679586069381473861032898970065272704, 0.6971678434782065812434216297544180096]
        [0, 0, 0.000202565811952601640514125, -0.001688048431292097865875929921536,
          0.00949527245894303326372100737792, -0.02825973936550074429163142692352,
          0.0343434334990493887867676067712]
        [0, 3.65322984, 110.493165, 14.014804]
        [0, 19.9578249, 5.0628472]
        [0, 0.45723832]
        [0, 0, 0.00029588992] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.16 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.180625 (-1.71133221913) hw0 (by norm_num) lgU50
    have hτ1 : w / 0.180625 ≤ 5.536333 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.71133221913) + 5.536333 * w := by linarith
    have hwa : Real.log 0.16 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.71133221913) 5.536333 13.15238 13.92363
        0.1460972 0.02405481 (2029 / 1846) 0.741524527638 0.473258529 0.12922 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (2029 / 1846) = (3875 / 1846) by norm_num]; exact lgU250)
        (by norm_num) (by norm_num)
    have hRs : 0.473258529 + 0.12922 * ((2.08 + Real.log r + ((-2.71133221913) + 5.536333 * w)) *
        (0.1460972 + 0.02405481 * (Real.log r + 2 / 3 * ((-2.71133221913) + 5.536333 * w) -
        13.15238)) / 2) ≤ 0.481977929 + (-0.0147923151) * Real.log r + (-0.0800844239) * w +
        0.00155418128 * Real.log r ^ 2 + 0.0143407752 * w * Real.log r + 0.0317581227 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000098732943299072095717140914 + 0.000000000068445764322555 *
          Real.log r + 0.000000000036560192078189912652 * w + 0.0000000000059 * Real.log r ^ 2 +
          0.0000000000736968745 * w * Real.log r + 0.0000000000690675353164834 * w ^ 2) (by ring) ?_
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
    have hL : Real.log (2 * (w * r)) ≤ (-2.01818503) + Real.log r + 5.536333 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.71133221913) + 5.536333 * w := by
      rw [hwl]
      linarith
    have hLlo : 12.53 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL52]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.53 2.52812576786 0.078991 2.53842135804
        (Real.log r + (-2.71133221913) + 5.536333 * w) 1.7810727 0.99139451 0.21295 1.17399
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL251 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL253]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.88736845 + 0.0299596616 * Real.log r + 0.165866664 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 3.65322984 + 19.9578249 * Real.log r + 110.493165 * w + 0.45723832 *
        Real.log r ^ 2 + 5.0628472 * w * Real.log r + 14.014804 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((31104124169018510110398785779 /
          3600000000000000000000000000000000000) + (1690093361812281557 /
          18000000000000000000000000) * Real.log r + (16519269052082274189310481 /
          18000000000000000000000000000000) * w + 0.000000000651475 * Real.log r ^ 2 +
          0.00000000745244508235 * w * Real.log r + 0.000000006970808820051011275 *
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
      j9l, j9h, j10l, j10h⟩ := mom_0_16_0_2025
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
/-- **Piece `[0.2025, 0.25]` of region `R2a`** (`ptLoS`; moments `mom_0_2025_0_25`). -/
private theorem tR2a_lo5 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.2025 0.25
      (1 / Real.sqrt r * (0.009711176803219559 + Real.log r * 0.003269426985672359 + Real.log r ^ 2
          * (-0.00004342849700859334) + Real.log r ^ 3 * 0.000009453630563342251 + Real.log r ^ 4 *
          0.0000001650777502779129) + 1 / r * (0.3039318459044143 + Real.log r * 0.2216264635874823
          + Real.log r ^ 2 * 0.004700969676503455) + 0.0000006764340992411399) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.2025 : ℝ) 0.25, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.978156202257496697663173924, -29.548102345045864915717862278743576384,
          94.94697112874928968914468594314251013824, 8.664614282778573380211249112510631757856,
          -708.364246187909863971281715265478976379216,
          1186.87741837559752325767725944602319928416, -119.0945027940893800337503963621005102808,
          30.84834493160058171968998953865850904984, 3.076684686565205090919450521913658503]
        [0, 0, 3.702806182562631596476248117726, -24.999052864272849053860448092569821650016,
          112.8533190238991155431072711500294203890976,
          -275.6466272399311625410725189233553417396976,
          299.300112713778915309281600098510969253536, -68.59165419787830433332882983291040679792,
          24.698795493910995091428842213150801559224, 3.1237963912671150324163295004709014333]
        [0, 0, -0.0740552726020464667347991252047, 0.5997899173505619123029423682351375173552,
          -2.8880186375336552191021092203676002431008, 8.262016512782339968135413641613390680592,
          -12.093155899434802515468126879967032807216, 6.189506068183911109859986424123148856092,
          1.1746775903293278433918733222835323414]
        [0, 0, 0.00969613253615823416453347855697, -0.06090147594526131277074906618492537191952,
          0.26437893338479588576746891950308012992, -0.5811693141107758891768549239167133990192,
          0.4382895107239585018407220613250085972848, 0.19436019450240108741193576836733676891]
        [0, 0, 0.0001809946464487433402668671875, -0.001191734295861557391871076786048,
          0.0052965968852052168181185301946, -0.01245525424891747042787476092308,
          0.01195977776782302459799944412127]
        [0, 8.17955796, 89.7928082, 8.81793267]
        [0, 20.2595022, 3.97909209]
        [0, 0.448891323]
        [0, 0, 0.00028449824] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.978156202257496697663173924, -29.548102345045864915717862278743576384,
          94.94697112874928968914468594314251013824, 8.664614282778573380211249112510631757856,
          -708.364246187909863971281715265478976379216,
          1186.87741837559752325767725944602319928416, -119.0945027940893800337503963621005102808,
          30.84834493160058171968998953865850904984, 3.076684686565205090919450521913658503]
        [0, 0, 3.702806182562631596476248117726, -24.999052864272849053860448092569821650016,
          112.8533190238991155431072711500294203890976,
          -275.6466272399311625410725189233553417396976,
          299.300112713778915309281600098510969253536, -68.59165419787830433332882983291040679792,
          24.698795493910995091428842213150801559224, 3.1237963912671150324163295004709014333]
        [0, 0, -0.0740552726020464667347991252047, 0.5997899173505619123029423682351375173552,
          -2.8880186375336552191021092203676002431008, 8.262016512782339968135413641613390680592,
          -12.093155899434802515468126879967032807216, 6.189506068183911109859986424123148856092,
          1.1746775903293278433918733222835323414]
        [0, 0, 0.00969613253615823416453347855697, -0.06090147594526131277074906618492537191952,
          0.26437893338479588576746891950308012992, -0.5811693141107758891768549239167133990192,
          0.4382895107239585018407220613250085972848, 0.19436019450240108741193576836733676891]
        [0, 0, 0.0001809946464487433402668671875, -0.001191734295861557391871076786048,
          0.0052965968852052168181185301946, -0.01245525424891747042787476092308,
          0.01195977776782302459799944412127]
        [0, 8.17955796, 89.7928082, 8.81793267]
        [0, 20.2595022, 3.97909209]
        [0, 0.448891323]
        [0, 0, 0.00028449824] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.2025 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.225625 (-1.48888094915) hw0 (by norm_num) lgU58
    have hτ1 : w / 0.225625 ≤ 4.432133 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.48888094915) + 4.432133 * w := by linarith
    have hwa : Real.log 0.2025 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.48888094915) 4.432133 13.30847 14.06321
        0.1495066 0.02519519 (14464 / 12661) 0.761929409609 0.476183353 0.12661 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14464 / 12661) = (27125 / 12661) by norm_num]; exact lgU254)
        (by norm_num) (by norm_num)
    have hRs : 0.476183353 + 0.12661 * ((2.08 + Real.log r + ((-2.48888094915) + 4.432133 * w)) *
        (0.1495066 + 0.02519519 * (Real.log r + 2 / 3 * ((-2.48888094915) + 4.432133 * w) -
        13.30847)) / 2) ≤ 0.482074808 + (-0.0150608851) * Real.log r + (-0.0657883628) * w +
        0.00159498151 * Real.log r ^ 2 + 0.0117819503 * w * Real.log r + 0.0208876683 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000080159866149358911282724575 + 0.0000000000049938023749875 *
          Real.log r + (24704182574590783601 / 300000000000000000000000000000) * w +
          0.00000000000705 * Real.log r ^ 2 + (527714153 / 12000000000000000000) * w * Real.log r +
          (2591020512078349 / 30000000000000000000000000) * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 5.46875 + (-36.0082304) * w + 160.03658 * w ^ 2 + (-376.335284) * w
        ^ 3 + 361.364471 * w ^ 4 := by
      refine (isq_le 0.45 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((1 / 18984375) * w + (23 / 109350000) * w ^ 2 + (83939 /
          132860250000) * w ^ 3 + (62046319 / 387420489000000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.79573376) + Real.log r + 4.432133 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.48888094915) + 4.432133 * w := by
      rw [hwl]
      linarith
    have hLlo : 12.77 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL60]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.77 2.547098669 0.077549 2.55684528534
        (Real.log r + (-2.48888094915) + 4.432133 * w) 1.7810727 0.98400978 0.21246 1.1767
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL255 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL257]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.90184705 + 0.0293450617 * Real.log r + 0.130061217 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 8.17955796 + 20.2595022 * Real.log r + 89.7928082 * w + 0.448891323 *
        Real.log r ^ 2 + 3.97909209 * w * Real.log r + 8.81793267 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((67113395078768550731624473 /
          144000000000000000000000000000000000) + (113283750620420161 / 3600000000000000000000000) *
          Real.log r + (270995289488534669433413 / 3600000000000000000000000000000) * w +
          0.000000000860025 * Real.log r ^ 2 + 0.00000000545957236665 * w * Real.log r +
          0.000000001034790426058782225 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000889057 :=
      (wy_rpow_le w y 0.2025 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_2025_0_25
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
/-- **Piece `[0.25, 0.3025]` of region `R2a`** (`ptLoS`; moments `mom_0_25_0_3025`). -/
private theorem tR2a_lo6 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.25 0.3025
      (1 / Real.sqrt r * (0.01524419825015694 + Real.log r * 0.004828876520022343 + Real.log r ^ 2 *
          (-0.00006546002742266889) + Real.log r ^ 3 * 0.00001445682808890432 + Real.log r ^ 4 *
          0.0000002444754860842565) + 1 / r * (0.4660813944640451 + Real.log r * 0.2987797355898267
          + Real.log r ^ 2 * 0.006165531365832868) + 0.000001061890116819073) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.25 : ℝ) 0.3025, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.90769400418966424821672491412890625, -24.7005788217920064379960040554866796875,
          67.06159995902574348096144653310451171875, -14.90463768097835533984654154813473828125,
          -264.59159244491675540377568489625859375, 380.202515874488948310266649905965125,
          -32.581391394859233776996620919565, 6.856006365315208662808408325715,
          0.5384611910644553183864840118]
        [0, 0, 3.34742124082979920528442485667689453125,
          -18.326982518126805380617812166933817578125, 67.06474350793613038535755377251288671875,
          -132.91668763740827226570743111185519125, 117.532722462811849039392169661262505,
          -22.7576772543774806568004689206253, 6.7043146938852555979092350621806,
          0.667860129135931336307973886392]
        [0, 0, -0.068596496207619539267632230226086328125,
          0.4519379942402075869653151611243530859375, -1.7654135954065892532330132067353609375,
          4.10407546919425357816089778534741425, -4.89253522871341380236245808199506,
          2.05432775463392202332618719853551, 0.3067982392785073877997268339052]
        [0, 0, 0.0090859853926871844486363112425834375, -0.0462784937078722039572534735738075,
          0.162823745922921338202402848462202, -0.29042964076968137398903637539104,
          0.17871661621099793562897270336344, 0.0620115926222538837942097461088]
        [0, 0, 0.00016387873221805348640068125, -0.0008740199051629519274703,
          0.00314647165858662693889308, -0.0059932793496888132169392, 0.0046614394942024102798416]
        [0, 12.324986, 74.4542224, 5.81552515]
        [0, 20.5214446, 3.20580816]
        [0, 0.441800427]
        [0, 0, 0.00027468] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.90769400418966424821672491412890625, -24.7005788217920064379960040554866796875,
          67.06159995902574348096144653310451171875, -14.90463768097835533984654154813473828125,
          -264.59159244491675540377568489625859375, 380.202515874488948310266649905965125,
          -32.581391394859233776996620919565, 6.856006365315208662808408325715,
          0.5384611910644553183864840118]
        [0, 0, 3.34742124082979920528442485667689453125,
          -18.326982518126805380617812166933817578125, 67.06474350793613038535755377251288671875,
          -132.91668763740827226570743111185519125, 117.532722462811849039392169661262505,
          -22.7576772543774806568004689206253, 6.7043146938852555979092350621806,
          0.667860129135931336307973886392]
        [0, 0, -0.068596496207619539267632230226086328125,
          0.4519379942402075869653151611243530859375, -1.7654135954065892532330132067353609375,
          4.10407546919425357816089778534741425, -4.89253522871341380236245808199506,
          2.05432775463392202332618719853551, 0.3067982392785073877997268339052]
        [0, 0, 0.0090859853926871844486363112425834375, -0.0462784937078722039572534735738075,
          0.162823745922921338202402848462202, -0.29042964076968137398903637539104,
          0.17871661621099793562897270336344, 0.0620115926222538837942097461088]
        [0, 0, 0.00016387873221805348640068125, -0.0008740199051629519274703,
          0.00314647165858662693889308, -0.0059932793496888132169392, 0.0046614394942024102798416]
        [0, 12.324986, 74.4542224, 5.81552515]
        [0, 20.5214446, 3.20580816]
        [0, 0.441800427]
        [0, 0, 0.00027468] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.25 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.275625 (-1.28871403221) hw0 (by norm_num) lgU66
    have hτ1 : w / 0.275625 ≤ 3.628118 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.28871403221) + 3.628118 * w := by linarith
    have hwa : Real.log 0.25 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.28871403221) 3.628118 13.44827 14.18964
        0.1526982 0.02629318 (14699 / 12426) 0.780664760907 0.478915317 0.12426 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14699 / 12426) = (27125 / 12426) by norm_num]; exact lgU258)
        (by norm_num) (by norm_num)
    have hRs : 0.478915317 + 0.12426 * ((2.08 + Real.log r + ((-2.28871403221) + 3.628118 * w)) *
        (0.1526982 + 0.02629318 * (Real.log r + 2 / 3 * ((-2.28871403221) + 3.628118 * w) -
        13.44827)) / 2) ≤ 0.482040695 + (-0.0153154003) * Real.log r + (-0.0551537389) * w +
        0.00163359528 * Real.log r ^ 2 + 0.00987812737 * w * Real.log r + 0.0143356047 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000097612577192020825716689804 + 0.00000000004803920359369 *
          Real.log r + 0.000000000021519831450369900336 * w + 0.0000000000066 * Real.log r ^ 2 +
          0.000000000009770898 * w * Real.log r + 0.0000000000272241243639856 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 4.921875 + (-26.25) * w + 94.5 * w ^ 2 + (-180) * w ^ 3 + 140 * w ^
        4 := by
      refine (isq_le 0.5 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ (0) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.59556685) + Real.log r + 3.628118 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.28871403221) + 3.628118 * w := by
      rw [hwl]
      linarith
    have hLlo : 12.98 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL68]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 12.98 2.56340971023 0.076324 2.57276784329
        (Real.log r + (-2.28871403221) + 3.628118 * w) 1.7810727 0.97774851 0.21204 1.17903
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL259 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL261]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.91435034 + 0.0288244193 * Real.log r + 0.104578395 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 12.324986 + 20.5214446 * Real.log r + 74.4542224 * w + 0.441800427 *
        Real.log r ^ 2 + 3.20580816 * w * Real.log r + 5.81552515 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((5951398664798717468296247647 /
          300000000000000000000000000000000000) + (277191294354079919 / 4500000000000000000000000) *
          Real.log r + (189500062244667863781221 / 2250000000000000000000000000000) * w +
          0.0000000005469 * Real.log r ^ 2 + 0.0000000007556634684 * w * Real.log r +
          0.0000000064493781158222356 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_25_0_3025
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
/-- **Piece `[0.3025, 0.36]` of region `R2a`** (`ptLoS`; moments `mom_0_3025_0_36`). -/
private theorem tR2a_lo7 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.3025 0.36
      (1 / Real.sqrt r * (0.02278651883087772 + Real.log r * 0.006843321070687217 + Real.log r ^ 2 *
          (-0.00009435954176964074) + Real.log r ^ 3 * 0.00002115908242282897 + Real.log r ^ 4 *
          0.0000003478401138936017) + 1 / r * (0.6746002351513301 + Real.log r * 0.3898006426414107
          + Real.log r ^ 2 * 0.007850258546734312) + 0.00000159213277044089) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.3025 : ℝ) 0.36, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.80577581457871481122494166530483949356,
          -20.7631517627321965173948980796452532718412,
          48.00564551610897589604581463135297653630692,
          -16.86644176174639596307253485138829575064996,
          -108.0445193387967086854181842019504534621594,
          135.559082023468125091354009412299734754884,
          -10.0552182810056434540229630570995396843868, 1.7538690927784543547450848249228289452752,
          0.110990058774715860784786943936758224]
        [0, 0, 3.0533699235703001631126056544540602789544,
          -13.83033570314775388698440857511951223710402,
          41.85531060889078367382563899930756379833358,
          -68.6665293801872938858462113378292841484591,
          50.4272159212392157384093571317182132831646, -8.3722188742497621572754897353280348509254,
          2.0569765804207928548329398150755930524204, 0.165132378479156872400259998371366473]
        [0, 0, -0.06393074910440634683124689693463551187174,
          0.349482072753647724805128654492469016114362,
          -1.12989557266609101164264425204405857701105,
          2.17726132968011557578666785465628287730231,
          -2.15584642352124702724958691898888307345612,
          0.75670185539520731864066282709537422990506, 0.09099481102007663699940661583366082345]
        [0, 0, 0.008566999478383597301475941953490741347186,
          -0.03609824111256083139280950648917975263605,
          0.10501798542005745247180888680665282959473,
          -0.15505026437704452411564655582790768537576,
          0.07935730501342565335968520398059858175318, 0.02206244780039920945504731218138165535]
        [0, 0, 0.0001499208141550666122653655467966, -0.000660807995214287301509670762255,
          0.001966040321075189632173524249763, -0.003094908015685147071578098515556,
          0.001989380729024827500318305152458]
        [0, 16.1508671, 62.7701154, 3.98463629]
        [0, 20.7533672, 2.63484046]
        [0, 0.435572016]
        [0, 0, 0.00026609056] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.80577581457871481122494166530483949356,
          -20.7631517627321965173948980796452532718412,
          48.00564551610897589604581463135297653630692,
          -16.86644176174639596307253485138829575064996,
          -108.0445193387967086854181842019504534621594,
          135.559082023468125091354009412299734754884,
          -10.0552182810056434540229630570995396843868, 1.7538690927784543547450848249228289452752,
          0.110990058774715860784786943936758224]
        [0, 0, 3.0533699235703001631126056544540602789544,
          -13.83033570314775388698440857511951223710402,
          41.85531060889078367382563899930756379833358,
          -68.6665293801872938858462113378292841484591,
          50.4272159212392157384093571317182132831646, -8.3722188742497621572754897353280348509254,
          2.0569765804207928548329398150755930524204, 0.165132378479156872400259998371366473]
        [0, 0, -0.06393074910440634683124689693463551187174,
          0.349482072753647724805128654492469016114362,
          -1.12989557266609101164264425204405857701105,
          2.17726132968011557578666785465628287730231,
          -2.15584642352124702724958691898888307345612,
          0.75670185539520731864066282709537422990506, 0.09099481102007663699940661583366082345]
        [0, 0, 0.008566999478383597301475941953490741347186,
          -0.03609824111256083139280950648917975263605,
          0.10501798542005745247180888680665282959473,
          -0.15505026437704452411564655582790768537576,
          0.07935730501342565335968520398059858175318, 0.02206244780039920945504731218138165535]
        [0, 0, 0.0001499208141550666122653655467966, -0.000660807995214287301509670762255,
          0.001966040321075189632173524249763, -0.003094908015685147071578098515556,
          0.001989380729024827500318305152458]
        [0, 16.1508671, 62.7701154, 3.98463629]
        [0, 20.7533672, 2.63484046]
        [0, 0.435572016]
        [0, 0, 0.00026609056] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.3025 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.330625 (-1.10677047565) hw0 (by norm_num) lgU74
    have hτ1 : w / 0.330625 ≤ 3.024575 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.10677047565) + 3.024575 * w := by linarith
    have hwa : Real.log 0.3025 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.10677047565) 3.024575 13.57483 14.30516
        0.1557073 0.02735548 (14913 / 12212) 0.798036737561 0.481487466 0.12212 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (14913 / 12212) = (27125 / 12212) by norm_num]; exact lgU262)
        (by norm_num) (by norm_num)
    have hRs : 0.481487466 + 0.12212 * ((2.08 + Real.log r + ((-2.10677047565) + 3.024575 * w)) *
        (0.1557073 + 0.02735548 * (Real.log r + 2 / 3 * ((-2.10677047565) + 3.024575 * w) -
        13.57483)) / 2) ≤ 0.481902754 + (-0.0155576089) * Real.log r + (-0.0470100734) * w +
        0.00167032561 * Real.log r ^ 2 + 0.0084200418 * w * Real.log r + 0.0101868192 * w ^ 2 := by
      refine le_of_sub_eq _ _ ((345431206733984074148141 / 750000000000000000000000000000000) +
          (1130586355643 / 15000000000000000000000) * Real.log r + 0.000000000061907010726836092 * w
          + 0.0000000000012 * Real.log r ^ 2 + (88187 / 30000000000000000) * w * Real.log r +
          (97987127821 / 3000000000000000000000) * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 4.47443182 + (-19.7220135) * w + 58.6770651 * w ^ 2 + (-92.3684612)
        * w ^ 3 + 59.3736666 * w ^ 4 := by
      refine (isq_le 0.55 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((1 / 550000000) + (63 / 2662000000) * w + (114201 / 1610510000000) *
          w ^ 2 + (3971837 / 48717927500000) * w ^ 3 + (328369103 / 11789738455000000) * w ^ 4)
          (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.41362329) + Real.log r + 3.024575 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.10677047565) + 3.024575 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.17 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL76]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.17 2.57794151471 0.075248 2.58696595477
        (Real.log r + (-2.10677047565) + 3.024575 * w) 1.7810727 0.97223696 0.21167 1.18109
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL263 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL265]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.92540317 + 0.0283684703 * Real.log r + 0.0858025661 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 16.1508671 + 20.7533672 * Real.log r + 62.7701154 * w + 0.435572016 *
        Real.log r ^ 2 + 2.63484046 * w * Real.log r + 3.98463629 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((155668085766773875811233711 /
          9000000000000000000000000000000000) + (22101110255757727 / 225000000000000000000000) *
          Real.log r + (883398622072337085641 / 9000000000000000000000000000) * w + 0.0000000007788
          * Real.log r ^ 2 + 0.00000000412467802 * w * Real.log r + 0.00000000408544901117075 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000831533 :=
      (wy_rpow_le w y 0.3025 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_3025_0_36
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
/-- **Piece `[0.36, 0.4225]` of region `R2a`** (`ptLoS`; moments `mom_0_36_0_4225`). -/
private theorem tR2a_lo8 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.36 0.4225
      (1 / Real.sqrt r * (0.03266098525772853 + Real.log r * 0.009355627923519368 + Real.log r ^ 2 *
          (-0.0001308477583909274) + Real.log r ^ 3 * 0.00002980995712373484 + Real.log r ^ 4 *
          0.0000004779372572914853) + 1 / r * (0.9320927614731064 + Real.log r * 0.494098251221627 +
          Real.log r ^ 2 * 0.0097382712925152) + 0.000002293835969986407) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.36 : ℝ) 0.4225, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.686035732493909981439190418625, -17.578598803106377598574435879492719802,
          34.929245947273470988359696722340806052838, -13.9143144067356940918051607777040922096542,
          -47.48798733133691376657185416231983419584056,
          52.80858439199785774261012498193156606175568,
          -3.4290881016539420877109175141010825003522, 0.5040886019472111234586568353355522319464,
          0.0262021884870263627685615658149888]
        [0, 0, 2.80588701282104889107004907100821875, -10.689709102312619829521437953152354330556,
          27.2008835198260019826901727813429321231836,
          -37.55241200468454115505594396432439161539536,
          23.27694231648473469717800454814093647193888,
          -3.3547512846448919004523160018933038790172, 0.6984151018119510127016004067922011631024,
          0.0460585344467124961848198136546208]
        [0, 0, -0.05988210041959292839364845490976328125,
          0.2760988361404360405193821463336373407766, -0.75109133637584924531613632279317613692296,
          1.21953024715658241599256865124317821539968, -1.0193779567959549884243657356134827799942,
          0.3037799531467714617043161372045706183864, 0.0299860250705319063388216748151488]
        [0, 0, 0.00811855418107698751426100046885796875,
          -0.02877024629646897417005683727597784997296,
          0.07036263936898409628162469708456479255408, -0.0874106984367556243759003016871256562012,
          0.0378031147339392462377905206422377089584, 0.0085897467852729132016018412181728]
        [0, 0, 0.000138331624941034849815421875, -0.000512339350883983126619976858672,
          0.001280848380582614577017077532656, -0.00169424388760739744338914716284,
          0.00091510086777035635465292877488]
        [0, 19.7031541, 53.6579297, 2.81882959]
        [0, 20.9601288, 2.20221062]
        [0, 0.430119262]
        [0, 0, 0.00025848384] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.686035732493909981439190418625, -17.578598803106377598574435879492719802,
          34.929245947273470988359696722340806052838, -13.9143144067356940918051607777040922096542,
          -47.48798733133691376657185416231983419584056,
          52.80858439199785774261012498193156606175568,
          -3.4290881016539420877109175141010825003522, 0.5040886019472111234586568353355522319464,
          0.0262021884870263627685615658149888]
        [0, 0, 2.80588701282104889107004907100821875, -10.689709102312619829521437953152354330556,
          27.2008835198260019826901727813429321231836,
          -37.55241200468454115505594396432439161539536,
          23.27694231648473469717800454814093647193888,
          -3.3547512846448919004523160018933038790172, 0.6984151018119510127016004067922011631024,
          0.0460585344467124961848198136546208]
        [0, 0, -0.05988210041959292839364845490976328125,
          0.2760988361404360405193821463336373407766, -0.75109133637584924531613632279317613692296,
          1.21953024715658241599256865124317821539968, -1.0193779567959549884243657356134827799942,
          0.3037799531467714617043161372045706183864, 0.0299860250705319063388216748151488]
        [0, 0, 0.00811855418107698751426100046885796875,
          -0.02877024629646897417005683727597784997296,
          0.07036263936898409628162469708456479255408, -0.0874106984367556243759003016871256562012,
          0.0378031147339392462377905206422377089584, 0.0085897467852729132016018412181728]
        [0, 0, 0.000138331624941034849815421875, -0.000512339350883983126619976858672,
          0.001280848380582614577017077532656, -0.00169424388760739744338914716284,
          0.00091510086777035635465292877488]
        [0, 19.7031541, 53.6579297, 2.81882959]
        [0, 20.9601288, 2.20221062]
        [0, 0.430119262]
        [0, 0, 0.00025848384] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.36 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.390625 (-0.940007257657) hw0 (by norm_num) lgU82
    have hτ1 : w / 0.390625 ≤ 2.56 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.940007257657) + 2.56 * w := by linarith
    have hwa : Real.log 0.36 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.940007257657) 2.56 13.69045 14.41151 0.1585619
        0.02838734 (3022 / 2403) 0.814299943085 0.48392886 0.12015 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (3022 / 2403) = (5425 / 2403) by norm_num]; exact lgU266)
        (by norm_num) (by norm_num)
    have hRs : 0.48392886 + 0.12015 * ((2.08 + Real.log r + ((-1.940007257657) + 2.56 * w)) *
        (0.1585619 + 0.02838734 * (Real.log r + 2 / 3 * ((-1.940007257657) + 2.56 * w) - 13.69045))
        / 2) ≤ 0.481685156 + (-0.0157885491) * Real.log r + (-0.0406224099) * w + 0.00170536946 *
        Real.log r ^ 2 + 0.00727624299 * w * Real.log r + 0.00745087283 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.000000000063614019826311993350741417 + 0.0000000000123186083457975
          * Real.log r + 0.00000000006952686509219328 * w + 0.0000000000095 * Real.log r ^ 2 +
          0.0000000000012 * w * Real.log r + 0.0000000000094688 * w ^ 2) (by ring) ?_
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
    have hL : Real.log (2 * (w * r)) ≤ (-1.24686007) + Real.log r + 2.56 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.940007257657) + 2.56 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.34 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL84]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.34 2.59076703944 0.074306 2.59956357779
        (Real.log r + (-1.940007257657) + 2.56 * w) 1.7810727 0.96742392 0.21133 1.18299
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL267 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL269]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.9352432 + 0.0279683396 * Real.log r + 0.0715989492 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 19.7031541 + 20.9601288 * Real.log r + 53.6579297 * w + 0.430119262 *
        Real.log r ^ 2 + 2.20221062 * w * Real.log r + 2.81882959 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((16269080090997834803830678593277 /
          180000000000000000000000000000000000000) + (2446310820766964539 /
          90000000000000000000000000) * Real.log r + (1461935820766964539 /
          35156250000000000000000000) * w + 0.00000000084985 * Real.log r ^ 2 + 0.000000002911232 *
          w * Real.log r + 0.00000000012637696 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_36_0_4225
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
/-- **Piece `[0.4225, 0.49]` of region `R2a`** (`ptLoS`; moments `mom_0_4225_0_49`). -/
private theorem tR2a_lo9 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.4225 0.49
      (1 / Real.sqrt r * (0.04511867524206402 + Real.log r * 0.01238698977560028 + Real.log r ^ 2 *
          (-0.0001754444477077133) + Real.log r ^ 3 * 0.00004060428447129179 + Real.log r ^ 4 *
          0.0000006362730770754201) + 1 / r * (1.238713144991883 + Real.log r * 0.610254637743306 +
          Real.log r ^ 2 * 0.01179205873748372) + 0.000003189701227287133) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.4225 : ℝ) 0.49, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.5568773398649808720043154849797532337, -14.9951867863406807088509360482013679236,
          25.839388919189755830822946305106919544998, -10.51091940695904695394070393488103473312,
          -22.204749951741220057651859139072432598176, 22.165330634982753661422498819604530934954,
          -1.272703300862817069765197293335907221324, 0.15986959038830210590447340118121232424,
          0.006932154061900636946874505670794272]
        [0, 0, 2.594784056500143406323749589740410154848,
          -8.4307434827711128934374890631568940106288, 18.2902047640516067656152691408456464170164,
          -21.5449943697892785588265011743670597610424,
          11.4268353434596693757217572232165699188688, -1.4451401711691077279384082910547969159444,
          0.2583329707761867574507408409150626443528, 0.01421307810480577544728304624546328864]
        [0, 0, -0.0563601922744099706649325534960930742476,
          0.22219973805719443495906574484483405429936, -0.5157037033548270142166688870312631789056,
          0.71531272926695392588494831095555986799288,
          -0.51165081126469199291116772321218559472912,
          0.13115158639893328808029388580178360395712, 0.010793053141017442405833855848385574656]
        [0, 0, 0.00772803758647696590559606707736402395464,
          -0.0233540889020500668013283222417452458232, 0.04868764244867624232199200784856421351232,
          -0.05160092461122188766032206842803367267208,
          0.01911176788092934423975707899529279025488, 0.003606227865347511735839521716254938944]
        [0, 0, 0.000128510472346068374945129878664, -0.00040555572839084183989959548152,
          0.000863905700522752260534583968832, -0.000973689149192975153749383339208,
          0.000448114666139414594382854430288]
        [0, 23.0217335, 46.4155406, 2.04786145]
        [0, 21.1480747, 1.86611322]
        [0, 0.425123798]
        [0, 0, 0.0002516784] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.5568773398649808720043154849797532337, -14.9951867863406807088509360482013679236,
          25.839388919189755830822946305106919544998, -10.51091940695904695394070393488103473312,
          -22.204749951741220057651859139072432598176, 22.165330634982753661422498819604530934954,
          -1.272703300862817069765197293335907221324, 0.15986959038830210590447340118121232424,
          0.006932154061900636946874505670794272]
        [0, 0, 2.594784056500143406323749589740410154848,
          -8.4307434827711128934374890631568940106288, 18.2902047640516067656152691408456464170164,
          -21.5449943697892785588265011743670597610424,
          11.4268353434596693757217572232165699188688, -1.4451401711691077279384082910547969159444,
          0.2583329707761867574507408409150626443528, 0.01421307810480577544728304624546328864]
        [0, 0, -0.0563601922744099706649325534960930742476,
          0.22219973805719443495906574484483405429936, -0.5157037033548270142166688870312631789056,
          0.71531272926695392588494831095555986799288,
          -0.51165081126469199291116772321218559472912,
          0.13115158639893328808029388580178360395712, 0.010793053141017442405833855848385574656]
        [0, 0, 0.00772803758647696590559606707736402395464,
          -0.0233540889020500668013283222417452458232, 0.04868764244867624232199200784856421351232,
          -0.05160092461122188766032206842803367267208,
          0.01911176788092934423975707899529279025488, 0.003606227865347511735839521716254938944]
        [0, 0, 0.000128510472346068374945129878664, -0.00040555572839084183989959548152,
          0.000863905700522752260534583968832, -0.000973689149192975153749383339208,
          0.000448114666139414594382854430288]
        [0, 23.0217335, 46.4155406, 2.04786145]
        [0, 21.1480747, 1.86611322]
        [0, 0.425123798]
        [0, 0, 0.0002516784] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.4225 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.455625 (-0.786085175881) hw0 (by norm_num) lgU90
    have hτ1 : w / 0.455625 ≤ 2.194788 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.786085175881) + 2.194788 * w := by linarith
    have hwa : Real.log 0.4225 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.786085175881) 2.194788 13.79687 14.51002
        0.1612834 0.02939299 (15292 / 11833) 0.829563574408 0.48624912 0.11833 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15292 / 11833) = (27125 / 11833) by norm_num]; exact lgU270)
        (by norm_num) (by norm_num)
    have hRs : 0.48624912 + 0.11833 * ((2.08 + Real.log r + ((-1.786085175881) + 2.194788 * w)) *
        (0.1612834 + 0.02939299 * (Real.log r + 2 / 3 * ((-1.786085175881) + 2.194788 * w) -
        13.79687)) / 2) ≤ 0.481393167 + (-0.0160105074) * Real.log r + (-0.0355136092) * w +
        0.00173903626 * Real.log r ^ 2 + 0.00636135984 * w * Real.log r + 0.0055847345 * w ^ 2 := by
      refine le_of_sub_eq _ _ ((22173317971829943969541822213 /
          30000000000000000000000000000000000000) + (786029574509027 / 12000000000000000000000000) *
          Real.log r + 0.0000000000505504977577864234184 * w + 0.00000000000665 * Real.log r ^ 2 +
          0.000000000005970767 * w * Real.log r + 0.0000000000090362591049584 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 3.7860577 + (-11.948111) * w + 25.4515976 * w ^ 2 + (-28.6859369) *
        w ^ 3 + 13.2019434 * w ^ 4 := by
      refine (isq_le 0.65 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((1 / 130000000) + (133 / 2197000000) * w + (34621 / 464116250000) *
          w ^ 2 + (7694227 / 627485170000000) * w ^ 3 + (2538407441 / 53022496865000000) * w ^ 4)
          (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-1.09293799) + Real.log r + 2.194788 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.786085175881) + 2.194788 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.5 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL92]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.5 2.6026896844 0.073443 2.61124568482
        (Real.log r + (-1.786085175881) + 2.194788 * w) 1.7810727 0.96299226 0.21102 1.18473
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL271 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL273]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.94421313 + 0.0276029612 * Real.log r + 0.060582648 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 23.0217335 + 21.1480747 * Real.log r + 46.4155406 * w + 0.425123798 *
        Real.log r ^ 2 + 1.86611322 * w * Real.log r + 2.04786145 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((2051265537077819218799071624343 /
          360000000000000000000000000000000000000) + (6045701173804926497 /
          180000000000000000000000000) * Real.log r + (1485798698987747251374803 /
          15000000000000000000000000000000) * w + 0.000000000505175 * Real.log r ^ 2 +
          0.0000000014878560558 * w * Real.log r + 0.0000000006840843084985852 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000786495 :=
      (wy_rpow_le w y 0.4225 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_4225_0_49
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
/-- **Piece `[0.49, 0.5625]` of region `R2a`** (`ptLoS`; moments `mom_0_49_0_5625`). -/
private theorem tR2a_lo10 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.49 0.5625
      (1 / Real.sqrt r * (0.06028924107528376 + Real.log r * 0.01592715636332279 + Real.log r ^ 2 *
          (-0.0002281338442689606) + Real.log r ^ 3 * 0.00005363210878551067 + Real.log r ^ 4 *
          0.0000008230019971598267) + 1 / r * (1.591234628547027 + Real.log r * 0.7358026421198543 +
          Real.log r ^ 2 * 0.01396198413177028) + 0.000004294777446215978) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.49 : ℝ) 0.5625, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.423568869325583299461502567123125, -12.887131980013237009913853644522884671984,
          19.42192395318672445860172695754324542170312,
          -7.708231301335381265646936050988503175227172,
          -10.9432294056962759101173912690396404096487192,
          9.914124506111810250974089329814679145038816,
          -0.50774599625343871557410371231022015637852,
          0.0551441797259432591118748514324412596471424, 0.0020215649853242759925042382038051318528]
        [0, 0, 2.4124620046227038546819450306654671875,
          -6.76435160865644994548696758415154540516132,
          12.660621379404033893333251639224913237170204,
          -12.8758569593690393656549678185283744624281444,
          5.911413316509838425504622313947324217756292,
          -0.662148151395790032821846729237157967001916,
          0.1027897499557150631662729872140785408546368, 0.0047816304808073889958847893125840410496]
        [0, 0, -0.05326128517738518064514155860178453125,
          0.181660202723027465699066548108432454441628,
          -0.3639719302668990772849861108741641336595484,
          0.436360742376363513938452291270193491547052,
          -0.270201317182186514272849755757466813299524,
          0.0602405346496151511965391029644794888806848, 0.0041889053962950132555632695736353405056]
        [0, 0, 0.00738416723502539526660680501177578125,
          -0.01925524104254558298245360440144572817482, 0.0346259188420289959055387475162205370566,
          -0.0316784527514605081971514228574924367134, 0.01016337493881436226968879983391567843104,
          0.00161464766941069931607915580057879488]
        [0, 0, 0.000120090585127606455905859375, -0.00032677710236713104342229268523,
          0.0006002028434527088392805978849, -0.0005832875031923062655709163801,
          0.00023146329523206245247076940256]
        [0, 26.136329, 40.5609834, 1.52216244]
        [0, 21.319856, 1.60017245]
        [0, 0.420545105]
        [0, 0, 0.00024553728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.423568869325583299461502567123125, -12.887131980013237009913853644522884671984,
          19.42192395318672445860172695754324542170312,
          -7.708231301335381265646936050988503175227172,
          -10.9432294056962759101173912690396404096487192,
          9.914124506111810250974089329814679145038816,
          -0.50774599625343871557410371231022015637852,
          0.0551441797259432591118748514324412596471424, 0.0020215649853242759925042382038051318528]
        [0, 0, 2.4124620046227038546819450306654671875,
          -6.76435160865644994548696758415154540516132,
          12.660621379404033893333251639224913237170204,
          -12.8758569593690393656549678185283744624281444,
          5.911413316509838425504622313947324217756292,
          -0.662148151395790032821846729237157967001916,
          0.1027897499557150631662729872140785408546368, 0.0047816304808073889958847893125840410496]
        [0, 0, -0.05326128517738518064514155860178453125,
          0.181660202723027465699066548108432454441628,
          -0.3639719302668990772849861108741641336595484,
          0.436360742376363513938452291270193491547052,
          -0.270201317182186514272849755757466813299524,
          0.0602405346496151511965391029644794888806848, 0.0041889053962950132555632695736353405056]
        [0, 0, 0.00738416723502539526660680501177578125,
          -0.01925524104254558298245360440144572817482, 0.0346259188420289959055387475162205370566,
          -0.0316784527514605081971514228574924367134, 0.01016337493881436226968879983391567843104,
          0.00161464766941069931607915580057879488]
        [0, 0, 0.000120090585127606455905859375, -0.00032677710236713104342229268523,
          0.0006002028434527088392805978849, -0.0005832875031923062655709163801,
          0.00023146329523206245247076940256]
        [0, 26.136329, 40.5609834, 1.52216244]
        [0, 21.319856, 1.60017245]
        [0, 0.420545105]
        [0, 0, 0.00024553728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.49 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.525625 (-0.643167247404) hw0 (by norm_num) lgU98
    have hτ1 : w / 0.525625 ≤ 1.902498 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.643167247404) + 1.902498 * w := by linarith
    have hwa : Real.log 0.49 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.643167247404) 1.902498 13.89543 14.60177
        0.1638886 0.03037566 (15461 / 11664) 0.843948637273 0.488461068 0.11664 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15461 / 11664) = (27125 / 11664) by norm_num]; exact lgU274)
        (by norm_num) (by norm_num)
    have hRs : 0.488461068 + 0.11664 * ((2.08 + Real.log r + ((-1.643167247404) + 1.902498 * w)) *
        (0.1638886 + 0.03037566 * (Real.log r + 2 / 3 * ((-1.643167247404) + 1.902498 * w) -
        13.89543)) / 2) ≤ 0.481035576 + (-0.0162246259) * Real.log r + (-0.0313580696) * w +
        0.0017715085 * Real.log r ^ 2 + 0.00561715227 * w * Real.log r + 0.00427464839 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000003290116904974656129002460672 + 0.000000000072242411261408
          * Real.log r + 0.0000000000804361235043185577472 * w + 0.0000000000088 * Real.log r ^ 2 +
          0.000000000000848304 * w * Real.log r + 0.0000000000068973746653568 * w ^ 2) (by ring) ?_
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
    have hL : Real.log (2 * (w * r)) ≤ (-0.950020066) + Real.log r + 1.902498 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.643167247404) + 1.902498 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.65 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL100]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.65 2.61373952059 0.072652 2.62207436107
        (Real.log r + (-1.643167247404) + 1.902498 * w) 1.7810727 0.95892111 0.21074 1.1863
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL275 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL277]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.95240947 + 0.0272694386 * Real.log r + 0.0518800524 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 26.136329 + 21.319856 * Real.log r + 40.5609834 * w + 0.420545105 *
        Real.log r ^ 2 + 1.60017245 * w * Real.log r + 1.52216244 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((109536835203799045139343196861 /
          1875000000000000000000000000000000000) + (296792034160986767 / 11250000000000000000000000)
          * Real.log r + (93567708567868167040661 / 1875000000000000000000000000000) * w +
          0.0000000001487 * Real.log r ^ 2 + 0.0000000082212229052 * w * Real.log r +
          0.0000000049303800673485948 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_49_0_5625
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
/-- **Piece `[0.5625, 0.64]` of region `R2a`** (`ptLoS`; moments `mom_0_5625_0_64`). -/
private theorem tR2a_lo11 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.5625 0.64
      (1 / Real.sqrt r * (0.0781292703636234 + Real.log r * 0.01992690980005307 + Real.log r ^ 2 *
          (-0.0002882942161327673) + Real.log r ^ 3 * 0.00006884006977367474 + Real.log r ^ 4 *
          0.00000103626604335898) + 1 / r * (1.982487442221489 + Real.log r * 0.8671714321529805 +
          Real.log r ^ 2 * 0.01618229021907651) + 0.000005612282985974552) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.5625 : ℝ) 0.64, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.2893818363047943471350013032859375, -11.1543348424996537395398127507448547811,
          14.8170026399128633160304897650102240702464,
          -5.60889007055698694369459599223444128962798,
          -5.6427498809221355402637176987360466115779908,
          4.68444718168961162678275603109411447907658,
          -0.215603299141028802592052885942177855366316,
          0.0204514070374212425703566736513243317216116, 0.0006412943992513391178631219529797543116]
        [0, 0, 2.2533703892526524603003408923952390625,
          -5.5083584091625011025515715234315061242761,
          8.985818074671460857758840507379637714664318,
          -7.9704840714768674864262348631379301401117773,
          3.199497732681806003665037575797338453087665,
          -0.319977724181885394790125192205896549463492,
          0.0435587270875940306655264448709315332779221, 0.0017332978562151944734148467395665344971]
        [0, 0, -0.050508456510257662208748772270899984375,
          0.150544704636547558187569631781019658841663,
          -0.2630517239638913161130140468512673184787467,
          0.275351098465589655897366929010566774845755,
          -0.149083661556621255120726468819743619519225,
          0.0291874777623365571680418319572072971325759, 0.0017351027121750339349266438918261065009]
        [0, 0, 0.0070784791599066527281525590386400328125,
          -0.0160900244634341057761343538045457132972977,
          0.025213567808914121680398418437922481303745,
          -0.020115040732384541739136311761333102569194,
          0.0056452685482350169405523472630874406342529, 0.0007642401570008678979988597816309449279]
        [0, 0, 0.0001127961505269444277210734375, -0.0002673686528335366570527502454019,
          0.000427789846871224589823743961415, -0.000362150132480200743919633557318,
          0.0001251877006640817496620797924563]
        [0, 29.0707804, 35.758507, 1.15415079]
        [0, 21.477445, 1.38642311]
        [0, 0.41636003]
        [0, 0, 0.00023995488] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.2893818363047943471350013032859375, -11.1543348424996537395398127507448547811,
          14.8170026399128633160304897650102240702464,
          -5.60889007055698694369459599223444128962798,
          -5.6427498809221355402637176987360466115779908,
          4.68444718168961162678275603109411447907658,
          -0.215603299141028802592052885942177855366316,
          0.0204514070374212425703566736513243317216116, 0.0006412943992513391178631219529797543116]
        [0, 0, 2.2533703892526524603003408923952390625,
          -5.5083584091625011025515715234315061242761,
          8.985818074671460857758840507379637714664318,
          -7.9704840714768674864262348631379301401117773,
          3.199497732681806003665037575797338453087665,
          -0.319977724181885394790125192205896549463492,
          0.0435587270875940306655264448709315332779221, 0.0017332978562151944734148467395665344971]
        [0, 0, -0.050508456510257662208748772270899984375,
          0.150544704636547558187569631781019658841663,
          -0.2630517239638913161130140468512673184787467,
          0.275351098465589655897366929010566774845755,
          -0.149083661556621255120726468819743619519225,
          0.0291874777623365571680418319572072971325759, 0.0017351027121750339349266438918261065009]
        [0, 0, 0.0070784791599066527281525590386400328125,
          -0.0160900244634341057761343538045457132972977,
          0.025213567808914121680398418437922481303745,
          -0.020115040732384541739136311761333102569194,
          0.0056452685482350169405523472630874406342529, 0.0007642401570008678979988597816309449279]
        [0, 0, 0.0001127961505269444277210734375, -0.0002673686528335366570527502454019,
          0.000427789846871224589823743961415, -0.000362150132480200743919633557318,
          0.0001251877006640817496620797924563]
        [0, 29.0707804, 35.758507, 1.15415079]
        [0, 21.477445, 1.38642311]
        [0, 0.41636003]
        [0, 0, 0.00023995488] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.5625 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.600625 (-0.509784498458) hw0 (by norm_num) lgU106
    have hτ1 : w / 0.600625 ≤ 1.664933 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.509784498458) + 1.664933 * w := by linarith
    have hwa : Real.log 0.5625 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.509784498458) 1.664933 13.98722 14.68763
        0.1663916 0.03133842 (15619 / 11506) 0.857587173879 0.490580521 0.11506 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15619 / 11506) = (27125 / 11506) by norm_num]; exact lgU278)
        (by norm_num) (by norm_num)
    have hRs : 0.490580521 + 0.11506 * ((2.08 + Real.log r + ((-1.509784498458) + 1.664933 * w)) *
        (0.1663916 + 0.03133842 * (Real.log r + 2 / 3 * ((-1.509784498458) + 1.664933 * w) -
        13.98722)) / 2) ≤ 0.48062473 + (-0.0164316589) * Real.log r + (-0.027928151) * w +
        0.00180289931 * Real.log r ^ 2 + 0.00500284425 * w * Real.log r + 0.00333176019 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000006197630900341475093423017424 + 0.000000000018148470292318
          * Real.log r + 0.0000000000451687375114151077552 * w + 0.0000000000074 * Real.log r ^ 2 +
          0.000000000009040457 * w * Real.log r + 0.0000000000017466020777524 * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 3.28125 + (-7.77777777) * w + 12.4444445 * w ^ 2 + (-10.5349794) * w
        ^ 3 + 3.64172129 * w ^ 4 := by
      refine (isq_le 0.75 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((7 / 900000000) * w + (1 / 18000000) * w ^ 2 + (29 / 1215000000) *
          w ^ 3 + (15107 / 1968300000000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-0.816637317) + Real.log r + 1.664933 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.509784498458) + 1.664933 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.79 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL108]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.79 2.62394369076 0.071929 2.6320757586
        (Real.log r + (-1.509784498458) + 1.664933 * w) 1.7810727 0.955192 0.21048 1.18777
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL279 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL281]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.9599407 + 0.0269647567 * Real.log r + 0.0448945132 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 29.0707804 + 21.477445 * Real.log r + 35.758507 * w + 0.41636003 *
        Real.log r ^ 2 + 1.38642311 * w * Real.log r + 1.15415079 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((8940352181134273361790779556749 /
          90000000000000000000000000000000000000) + (186953136434745919 /
          90000000000000000000000000) * Real.log r + (6054614446303710827158427 /
          90000000000000000000000000000000) * w + 0.000000000725525 * Real.log r ^ 2 +
          0.00000000475992102965 * w * Real.log r + 0.000000000061659799829131725 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000749859 :=
      (wy_rpow_le w y 0.5625 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_5625_0_64
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
/-- **Piece `[0.64, 0.7225]` of region `R2a`** (`ptLoS`; moments `mom_0_64_0_7225`). -/
private theorem tR2a_lo12 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.64 0.7225
      (1 / Real.sqrt r * (0.09837186160136152 + Real.log r * 0.0242910586639359 + Real.log r ^ 2 *
          (-0.0003545166560962769) + Real.log r ^ 3 * 0.00008598535683387013 + Real.log r ^ 4 *
          0.000001271684518225365) + 1 / r * (2.400955702260628 + Real.log r * 0.9996880150965269 +
          Real.log r ^ 2 * 0.01837136924055233) + 0.000007129312411285399) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.64 : ℝ) 0.7225, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.156358678605571943039651986498309685184,
          -9.718943344465075262020115906304131971628, 11.46001998918351750913489770837603382020928,
          -4.088546869983601468739606614181263345981632,
          -3.02619877109708393945696513591353099613124, 2.3217970522937328298811959972314320113156,
          -0.096660090476418001575156890499004683820268,
          0.008079435249184726329712919764707499457304, 0.000218930005847969831083156278882903612]
        [0, 0, 2.11331107085647391716669797997398946099648,
          -4.543875442532362132159776189592439377093552,
          6.5181665075495004090909674834735087342903424,
          -5.087430044503922917412776473230128324930872,
          1.801172486802929117758703606725994906982356,
          -0.1619543824842787963188435486166211875356504,
          0.0194992280040017373269484284319183857659472, 0.0006705414823366432137052599174595319016]
        [0, 0, -0.048036825249764361049742783133813451433792,
          0.1262257320794707815698444577166238585056816,
          -0.194061460714442652074417542163879516081368,
          0.178927621958782766259049797598681962919588,
          -0.0854490052736602134808183848321219306778556,
          0.0148141970807313687681700133016531882482648, 0.0007606454084275675014817211693898950844]
        [0, 0, 0.00680404742819663242356977169598308543856,
          -0.0136018357521045539635522751180996538968, 0.0187394347346698211296592028600358282276,
          -0.01315216481154067697525850445626078622636,
          0.00325652835556197269562543942929330976568, 0.00037965709706250658334711560044638604]
        [0, 0, 0.00010641193622038930857102404636, -0.0002216915332159389827369035358,
          0.0003117537192335202808580917281, -0.00023195961201841021770022936691,
          0.00007047384081071281255856750658]
        [0, 31.8447102, 31.7685879, 0.890545414]
        [0, 21.6224927, 1.21225481]
        [0, 0.412545417]
        [0, 0, 0.000234848] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.156358678605571943039651986498309685184,
          -9.718943344465075262020115906304131971628, 11.46001998918351750913489770837603382020928,
          -4.088546869983601468739606614181263345981632,
          -3.02619877109708393945696513591353099613124, 2.3217970522937328298811959972314320113156,
          -0.096660090476418001575156890499004683820268,
          0.008079435249184726329712919764707499457304, 0.000218930005847969831083156278882903612]
        [0, 0, 2.11331107085647391716669797997398946099648,
          -4.543875442532362132159776189592439377093552,
          6.5181665075495004090909674834735087342903424,
          -5.087430044503922917412776473230128324930872,
          1.801172486802929117758703606725994906982356,
          -0.1619543824842787963188435486166211875356504,
          0.0194992280040017373269484284319183857659472, 0.0006705414823366432137052599174595319016]
        [0, 0, -0.048036825249764361049742783133813451433792,
          0.1262257320794707815698444577166238585056816,
          -0.194061460714442652074417542163879516081368,
          0.178927621958782766259049797598681962919588,
          -0.0854490052736602134808183848321219306778556,
          0.0148141970807313687681700133016531882482648, 0.0007606454084275675014817211693898950844]
        [0, 0, 0.00680404742819663242356977169598308543856,
          -0.0136018357521045539635522751180996538968, 0.0187394347346698211296592028600358282276,
          -0.01315216481154067697525850445626078622636,
          0.00325652835556197269562543942929330976568, 0.00037965709706250658334711560044638604]
        [0, 0, 0.00010641193622038930857102404636, -0.0002216915332159389827369035358,
          0.0003117537192335202808580917281, -0.00023195961201841021770022936691,
          0.00007047384081071281255856750658]
        [0, 31.8447102, 31.7685879, 0.890545414]
        [0, 21.6224927, 1.21225481]
        [0, 0.412545417]
        [0, 0, 0.000234848] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.64 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.680625 (-0.384743784828) hw0 (by norm_num) lgU114
    have hτ1 : w / 0.680625 ≤ 1.469238 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.384743784828) + 1.469238 * w := by linarith
    have hwa : Real.log 0.64 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.384743784828) 1.469238 14.0731 14.7683 0.1688038
        0.03228316 (15768 / 11357) 0.870621518849 0.492626087 0.11357 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15768 / 11357) = (27125 / 11357) by norm_num]; exact lgU282)
        (by norm_num) (by norm_num)
    have hRs : 0.492626087 + 0.11357 * ((2.08 + Real.log r + ((-1.384743784828) + 1.469238 * w)) *
        (0.1688038 + 0.03228316 * (Real.log r + 2 / 3 * ((-1.384743784828) + 1.469238 * w) -
        14.0731)) / 2) ≤ 0.480177099 + (-0.0166310701) * Real.log r + (-0.0250592026) * w +
        0.00183319925 * Real.log r ^ 2 + 0.00448900998 * w * Real.log r + 0.00263816962 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000009238378173756886718303267264 + (15545219252021 /
          750000000000000000000000) * Real.log r + 0.0000000000192536670462968853312 * w +
          0.0000000000094 * Real.log r ^ 2 + 0.000000000003565562 * w * Real.log r +
          0.0000000000040973676727024 * w ^ 2) (by ring) ?_
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
    have hL : Real.log (2 * (w * r)) ≤ (-0.691596604) + Real.log r + 1.469238 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.384743784828) + 1.469238 * w := by
      rw [hwl]
      linarith
    have hLlo : 13.92 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL116]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 13.92 2.63332665386 0.07127 2.64127979845
        (Real.log r + (-1.384743784828) + 1.469238 * w) 1.7810727 0.9517885 0.21023 1.18918
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL283 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL285]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.96687372 + 0.0266859764 * Real.log r + 0.0392080505 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 31.8447102 + 21.6224927 * Real.log r + 31.7685879 * w + 0.412545417 *
        Real.log r ^ 2 + 1.21225481 * w * Real.log r + 0.890545414 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((151475674417104799795839841243 /
          2250000000000000000000000000000000000) + (244272317324784851 / 4500000000000000000000000)
          * Real.log r + (37643745160272040818923 / 750000000000000000000000000000) * w +
          0.00000000018075 * Real.log r ^ 2 + 0.000000003766637537 * w * Real.log r +
          0.000000000499653500793403 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_64_0_7225
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
/-- **Piece `[0.7225, 0.81]` of region `R2a`** (`ptLoS`; moments `mom_0_7225_0_81`). -/
private theorem tR2a_lo13 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.7225 0.81
      (1 / Real.sqrt r * (0.1204858123934221 + Real.log r * 0.02887347711101924 + Real.log r ^ 2 *
          (-0.0004245908193862001) + Real.log r ^ 3 * 0.0001046105836901738 + Real.log r ^ 4 *
          0.000001522378363370838) + 1 / r * (2.830715427346119 + Real.log r * 1.127688508757465 +
          Real.log r ^ 2 * 0.02043378039772544) + 0.000008813016829057493) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.7225 : ℝ) 0.81, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.025792537911196759478685922835404403634,
          -8.52087042891596556724212157426344941643234,
          8.976068598251652153224779143487606137218016,
          -2.9992552332203612059133120162747928279733239,
          -1.6796370345015724271936413857381950609893297,
          1.2001530316698547244310630790856384110829757,
          -0.0454540930631821842575386864417081086103299,
          0.0033740815275865343894267321484970381045067, 0.0000797411562072814130323168360061641653]
        [0, 0, 1.98898897841938629009985475218836729478542,
          -3.790970952452322119092294280553237846280797,
          4.8194979364051420811002167012756964321640762,
          -3.3357534310271084830122138937825464058101794,
          1.0496101187775014115136516687711126558368494,
          -0.0853751458539023040433806563969795914876918,
          0.0091597918781737677297842778526366063764104, 0.0002747330864624554862496373311409234536]
        [0, 0, -0.045799879742566158239369310219161132427408,
          0.1069228280264001871139447519394502548526806,
          -0.1457671810710646723204475457868177539852582,
          0.1193034933384081844770007060767174291398222,
          -0.0506404096566879227438718895185931549639714,
          0.0078319323456983739517546801089244019038722, 0.0003505707179034737290470742088892252798]
        [0, 0, 0.0065557868067070103707172156800546086142152,
          -0.0116156271245185291718888226575402785737864,
          0.0141797782853585875485843969502284182610024,
          -0.0088231685081522680060966227376961613746648,
          0.0019418297507918512252400525243424301455064, 0.0001968307681435454859003239917885387176]
        [0, 0, 0.0001007932374161095667113972189416, -0.0001860082809224489024072327742312,
          0.0002317058175563087134116260859592, -0.0001527143299431570732689738228984,
          0.0000410995891245184043339108961912]
        [0, 34.4746824, 28.4166435, 0.697859916]
        [0, 21.7564835, 1.06859755]
        [0, 0.409072326]
        [0, 0, 0.00023014976] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.025792537911196759478685922835404403634,
          -8.52087042891596556724212157426344941643234,
          8.976068598251652153224779143487606137218016,
          -2.9992552332203612059133120162747928279733239,
          -1.6796370345015724271936413857381950609893297,
          1.2001530316698547244310630790856384110829757,
          -0.0454540930631821842575386864417081086103299,
          0.0033740815275865343894267321484970381045067, 0.0000797411562072814130323168360061641653]
        [0, 0, 1.98898897841938629009985475218836729478542,
          -3.790970952452322119092294280553237846280797,
          4.8194979364051420811002167012756964321640762,
          -3.3357534310271084830122138937825464058101794,
          1.0496101187775014115136516687711126558368494,
          -0.0853751458539023040433806563969795914876918,
          0.0091597918781737677297842778526366063764104, 0.0002747330864624554862496373311409234536]
        [0, 0, -0.045799879742566158239369310219161132427408,
          0.1069228280264001871139447519394502548526806,
          -0.1457671810710646723204475457868177539852582,
          0.1193034933384081844770007060767174291398222,
          -0.0506404096566879227438718895185931549639714,
          0.0078319323456983739517546801089244019038722, 0.0003505707179034737290470742088892252798]
        [0, 0, 0.0065557868067070103707172156800546086142152,
          -0.0116156271245185291718888226575402785737864,
          0.0141797782853585875485843969502284182610024,
          -0.0088231685081522680060966227376961613746648,
          0.0019418297507918512252400525243424301455064, 0.0001968307681435454859003239917885387176]
        [0, 0, 0.0001007932374161095667113972189416, -0.0001860082809224489024072327742312,
          0.0002317058175563087134116260859592, -0.0001527143299431570732689738228984,
          0.0000410995891245184043339108961912]
        [0, 34.4746824, 28.4166435, 0.697859916]
        [0, 21.7564835, 1.06859755]
        [0, 0.409072326]
        [0, 0, 0.00023014976] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.7225 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.765625 (-0.267062784469) hw0 (by norm_num) lgU122
    have hτ1 : w / 0.765625 ≤ 1.306123 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.267062784469) + 1.306123 * w := by linarith
    have hwa : Real.log 0.7225 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.267062784469) 1.306123 14.1538 14.84438
        0.1711351 0.03321223 (15909 / 11216) 0.883114482216 0.494604804 0.11216 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (15909 / 11216) = (27125 / 11216) by norm_num]; exact lgU286)
        (by norm_num) (by norm_num)
    have hRs : 0.494604804 + 0.11216 * ((2.08 + Real.log r + ((-1.267062784469) + 1.306123 * w)) *
        (0.1711351 + 0.03321223 * (Real.log r + 2 / 3 * ((-1.267062784469) + 1.306123 * w) -
        14.1538)) / 2) ≤ 0.479697086 + (-0.0168239639) * Real.log r + (-0.0226333794) * w +
        0.00186254186 * Real.log r ^ 2 + 0.0040545146 * w * Real.log r + 0.00211827791 * w ^ 2 := by
      refine le_of_sub_eq _ _ ((1297715325080162454696239597 /
          1875000000000000000000000000000000000) + (28080402396487 / 750000000000000000000000) *
          Real.log r + 0.0000000000116362534712925758944 * w + 0.0000000000016 * Real.log r ^ 2 +
          (351271 / 750000000000000000) * w * Real.log r + (2036953132333 /
          1875000000000000000000000) * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 2.89522059 + (-5.34296763) * w + 6.65559983 * w ^ 2 + (-4.38662041)
        * w ^ 3 + 1.18055913 * w ^ 4 := by
      refine (isq_le 0.85 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((3 / 1700000000) + (3381 / 491300000000) * w + (782431 /
          141985700000000) * w ^ 2 + (200588407 / 41033867300000000) * w ^ 3 + (30584576761 /
          11858787649700000000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-0.573915603) + Real.log r + 1.306123 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.267062784469) + 1.306123 * w := by
      rw [hwl]
      linarith
    have hLlo : 14.04 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL124]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.04 2.64191039755 0.07067 2.64973412525
        (Real.log r + (-1.267062784469) + 1.306123 * w) 1.7810727 0.94869607 0.21001 1.19042
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL287 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL289]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.97323423 + 0.0264336244 * Real.log r + 0.0345255647 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 34.4746824 + 21.7564835 * Real.log r + 28.4166435 * w + 0.409072326 *
        Real.log r ^ 2 + 1.06859755 * w * Real.log r + 0.697859916 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ (0.00000003804914641552080120823797051575 +
          (1061979176957071157 / 18000000000000000000000000) * Real.log r +
          (1414606428544700650794311 / 18000000000000000000000000000000) * w + 0.00000000094575 *
          Real.log r ^ 2 + 0.0000000051663356545 * w * Real.log r + 0.00000000047460991203125175 *
          w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000719218 :=
      (wy_rpow_le w y 0.7225 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_7225_0_81
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
/-- **Piece `[0.81, 0.9025]` of region `R2a`** (`ptLoS`; moments `mom_0_81_0_9025`). -/
private theorem tR2a_lo14 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.81 0.9025
      (1 / Real.sqrt r * (0.143655259779052 + Real.log r * 0.03347677642385163 + Real.log r ^ 2 *
          (-0.0004957151872318241) + Real.log r ^ 3 * 0.0001240489155966117 + Real.log r ^ 4 *
          0.000001778811155520268) + 1 / r * (3.251793252854863 + Real.log r * 1.244751383527373 +
          Real.log r ^ 2 * 0.02226541828694456) + 0.00001060807226978646) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.81 : ℝ) 0.9025, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.8985362245075480778556044307754296875, -7.513691766501220258328833364164405787715,
          7.1125231950668333513424114585325715877282, -2.2190746480412597437541356090132398172248,
          -0.960792552059886011156874143426673307979498,
          0.6438951503292042133577915331976600185048854,
          -0.022305033631190910496519953385305163397997,
          0.00148044089816408673195958594137279658872476,
          0.00003076735567171542715913046516586427988]
        [0, 0, 1.87777672215052072920798464013494921875,
          -3.194601663041259811741779733597705499398, 3.62429961026197293966993176691742046421434,
          -2.239902217126011969096334718710320338189796,
          0.630660869280574852211889682785419510216122,
          -0.0466699202677517281560378916176118332224794,
          0.0044913691402520896832716450526370900852521, 0.0001184638633099614661294465013755134323]
        [0, 0, -0.043776530382109595332917026087994140625,
          0.09142098319335516460199329379554950515725,
          -0.11128204110794085261264271985613138439656,
          0.081403886647422924256603149107479133710234,
          -0.0309200719403103396574373496354326866547345,
          0.00429364201310379878234126229260544235599685,
          0.00016893430425952805313447691955007487655]
        [0, 0, 0.0063309310920024501931971277267099609375,
          -0.010010623215874150308309292713145710696, 0.0109032187091073142999706844661171818754,
          -0.006056196156440332685566308200837517925325,
          0.0011925617044150404378919208026872866047975, 0.0001059991738205566044391387604270284925]
        [0, 0, 0.0000958289746188475183095703125, -0.000157743167866112622708993204,
          0.0001752701868294231363741189846, -0.000103039498356030515350783292175,
          0.0000247351333914125975505568254525]
        [0, 36.9744513, 25.5726124, 0.5544695]
        [0, 21.8805535, 0.948835367]
        [0, 0.405923389]
        [0, 0, 0.0002258064] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.8985362245075480778556044307754296875, -7.513691766501220258328833364164405787715,
          7.1125231950668333513424114585325715877282, -2.2190746480412597437541356090132398172248,
          -0.960792552059886011156874143426673307979498,
          0.6438951503292042133577915331976600185048854,
          -0.022305033631190910496519953385305163397997,
          0.00148044089816408673195958594137279658872476,
          0.00003076735567171542715913046516586427988]
        [0, 0, 1.87777672215052072920798464013494921875,
          -3.194601663041259811741779733597705499398, 3.62429961026197293966993176691742046421434,
          -2.239902217126011969096334718710320338189796,
          0.630660869280574852211889682785419510216122,
          -0.0466699202677517281560378916176118332224794,
          0.0044913691402520896832716450526370900852521, 0.0001184638633099614661294465013755134323]
        [0, 0, -0.043776530382109595332917026087994140625,
          0.09142098319335516460199329379554950515725,
          -0.11128204110794085261264271985613138439656,
          0.081403886647422924256603149107479133710234,
          -0.0309200719403103396574373496354326866547345,
          0.00429364201310379878234126229260544235599685,
          0.00016893430425952805313447691955007487655]
        [0, 0, 0.0063309310920024501931971277267099609375,
          -0.010010623215874150308309292713145710696, 0.0109032187091073142999706844661171818754,
          -0.006056196156440332685566308200837517925325,
          0.0011925617044150404378919208026872866047975, 0.0001059991738205566044391387604270284925]
        [0, 0, 0.0000958289746188475183095703125, -0.000157743167866112622708993204,
          0.0001752701868294231363741189846, -0.000103039498356030515350783292175,
          0.0000247351333914125975505568254525]
        [0, 36.9744513, 25.5726124, 0.5544695]
        [0, 21.8805535, 0.948835367]
        [0, 0.405923389]
        [0, 0, 0.0002258064] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.81 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.855625 (-0.155923082336) hw0 (by norm_num) lgU130
    have hτ1 : w / 0.855625 ≤ 1.168737 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.155923082336) + 1.168737 * w := by linarith
    have hwa : Real.log 0.81 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.155923082336) 1.168737 14.22989 14.91635
        0.173393 0.03412702 (16041 / 11084) 0.894953185316 0.496496052 0.11084 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (16041 / 11084) = (27125 / 11084) by norm_num]; exact lgU290)
        (by norm_num) (by norm_num)
    have hRs : 0.496496052 + 0.11084 * ((2.08 + Real.log r + ((-1.155923082336) + 1.168737 * w)) *
        (0.173393 + 0.03412702 * (Real.log r + 2 / 3 * ((-1.155923082336) + 1.168737 * w) -
        14.22989)) / 2) ≤ 0.479159161 + (-0.0170135828) * Real.log r + (-0.0205652806) * w +
        0.00189131945 * Real.log r ^ 2 + 0.0036840917 * w * Real.log r + 0.00172229372 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000002212649489743976262526132224 + 0.000000000070381594839104
          * Real.log r + 0.0000000000231213507152183133184 * w + 0.0000000000016 * Real.log r ^ 2 +
          0.000000000003058882 * w * Real.log r + 0.0000000000089568514288136 * w ^ 2) (by ring) ?_
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
    have hL : Real.log (2 * (w * r)) ≤ (-0.462775901) + Real.log r + 1.168737 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.155923082336) + 1.168737 * w := by
      rw [hwl]
      linarith
    have hLlo : 14.15 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL132]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.15 2.64971462304 0.070126 2.65746165599
        (Real.log r + (-1.155923082336) + 1.168737 * w) 1.7810727 0.94590187 0.20981 1.19156
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL291 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL293]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.97910017 + 0.026205165 * Real.log r + 0.0306269459 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 36.9744513 + 21.8805535 * Real.log r + 25.5726124 * w + 0.405923389 *
        Real.log r ^ 2 + 0.948835367 * w * Real.log r + 0.5544695 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((7329904449979817882344731457 /
          175781250000000000000000000000000000) + (80343403899135433 / 1406250000000000000000000) *
          Real.log r + (5083149822621282852707 / 468750000000000000000000000000) * w +
          0.00000000047935 * Real.log r ^ 2 + 0.0000000003410821619 * w * Real.log r +
          0.00000000003857817132626015 * w ^ 2) (by ring) ?_)
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
      j9l, j9h, j10l, j10h⟩ := mom_0_81_0_9025
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
/-- **Piece `[0.9025, 1]` of region `R2a`** (`ptLoS`; moments `mom_0_9025_1`). -/
private theorem tR2a_lo15 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.9025 1
      (1 / Real.sqrt r * (0.16679681778187 + Real.log r * 0.03786806016052127 + Real.log r ^ 2 *
          (-0.0005644463874756192) + Real.log r ^ 3 * 0.0001433938906502343 + Real.log r ^ 4 *
          0.000002027019114013566) + 1 / r * (3.641598348431986 + Real.log r * 1.344199207352812 +
          Real.log r ^ 2 * 0.02374600020682001) + 0.00001243618965337901) := by
  obtain ⟨hla, hlb⟩ := lr_of r 1740000 3216400 14.3693956657 14.983773285 (by norm_num) hr0 hr1 lgL5
      lgU6
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.9025 : ℝ) 1, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.77508152591191673478026247995593631304,
          -6.6607799101890960018160731115097181360108, 5.6957461873060540751039083865373084915958,
          -1.656982518435475465163300794239673121012288,
          -0.564702138988308550287602679519774795211296,
          0.35718045375068606224443753495266863665956,
          -0.011371918964430421485281759637082514279888,
          0.000678986744607151079232213781831358276208, 0.000012488503894159970327103370918473408]
        [0, 0, 1.77794944956501927220437231033409091245,
          -2.71658185632491226113050150620056524722573,
          2.767357016873606558929266654031780759348847,
          -1.536574355631389893585476702373729521298031,
          0.389484737097305383604960076256967232612355,
          -0.026356320874617610143167659119639200360088,
          0.002288569122585062588130417495524119395938, 0.000053423453381623078634524836252038888]
        [0, 0, -0.0419449033344819313162110038813239005191,
          0.078833873462887583743535287669559564590549,
          -0.086208002496184252296611762203779609455017,
          0.056707067189396262901664233866035559581495,
          -0.019390889671312790401235398445048435980076,
          0.002431792787386584643260394082848441245866, 0.000084642744841848921045423875932139016]
        [0, 0, 0.00612631334348218369932789514397994144502,
          -0.00869856307501889481078738998007404535966, 0.0085053039541419396985291191498812608881,
          -0.00424326945116600767874337843277385558648,
          0.00075217374775359349769243498036312358268, 0.00005900654623236267110620281903161968]
        [0, 0, 0.000091341711972987175494719978508, -0.000134946203773548485702444918364,
          0.00013457239203868769326139614674, -0.000071005087240170611170599236592,
          0.000015298110570550389150758742072]
        [0, 39.3614428, 23.14055, 0.445784523]
        [0, 21.9979752, 0.847547432]
        [0, 0.402849703]
        [0, 0, 0.00022177312] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.77508152591191673478026247995593631304,
          -6.6607799101890960018160731115097181360108, 5.6957461873060540751039083865373084915958,
          -1.656982518435475465163300794239673121012288,
          -0.564702138988308550287602679519774795211296,
          0.35718045375068606224443753495266863665956,
          -0.011371918964430421485281759637082514279888,
          0.000678986744607151079232213781831358276208, 0.000012488503894159970327103370918473408]
        [0, 0, 1.77794944956501927220437231033409091245,
          -2.71658185632491226113050150620056524722573,
          2.767357016873606558929266654031780759348847,
          -1.536574355631389893585476702373729521298031,
          0.389484737097305383604960076256967232612355,
          -0.026356320874617610143167659119639200360088,
          0.002288569122585062588130417495524119395938, 0.000053423453381623078634524836252038888]
        [0, 0, -0.0419449033344819313162110038813239005191,
          0.078833873462887583743535287669559564590549,
          -0.086208002496184252296611762203779609455017,
          0.056707067189396262901664233866035559581495,
          -0.019390889671312790401235398445048435980076,
          0.002431792787386584643260394082848441245866, 0.000084642744841848921045423875932139016]
        [0, 0, 0.00612631334348218369932789514397994144502,
          -0.00869856307501889481078738998007404535966, 0.0085053039541419396985291191498812608881,
          -0.00424326945116600767874337843277385558648,
          0.00075217374775359349769243498036312358268, 0.00005900654623236267110620281903161968]
        [0, 0, 0.000091341711972987175494719978508, -0.000134946203773548485702444918364,
          0.00013457239203868769326139614674, -0.000071005087240170611170599236592,
          0.000015298110570550389150758742072]
        [0, 39.3614428, 23.14055, 0.445784523]
        [0, 21.9979752, 0.847547432]
        [0, 0.402849703]
        [0, 0, 0.00022177312] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.9025 : ℝ) * 1740000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.950625 (-0.050635615919) hw0 (by norm_num) lgU138
    have hτ1 : w / 0.950625 ≤ 1.05194 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.050635615919) + 1.05194 * w := by linarith
    have hwa : Real.log 0.9025 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.050635615919) 1.05194 14.30188 14.98465
        0.1755847 0.03502936 (16167 / 10958) 0.906386029534 0.498337211 0.10958 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (16167 / 10958) = (27125 / 10958) by norm_num]; exact lgU294)
        (by norm_num) (by norm_num)
    have hRs : 0.498337211 + 0.10958 * ((2.08 + Real.log r + ((-1.050635615919) + 1.05194 * w)) *
        (0.1755847 + 0.03502936 * (Real.log r + 2 / 3 * ((-1.050635615919) + 1.05194 * w) -
        14.30188)) / 2) ≤ 0.478601192 + (-0.0171973988) * Real.log r + (-0.018783375) * w +
        0.00191925864 * Real.log r ^ 2 + 0.00336490822 * w * Real.log r + 0.00141587262 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000000682342040932923019184963344 + 0.000000000001368510068356
          * Real.log r + (1367279540270990399 / 46875000000000000000000000000) * w + 0.0000000000056
          * Real.log r ^ 2 + (258079 / 37500000000000000) * w * Real.log r + (8048931163 /
          4687500000000000000000) * w ^ 2) (by ring) ?_
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hRb := hR.2.trans hRs
    have hq : 1 / Real.sqrt w ≤ 2.59046053 + (-3.82708849) * w + 3.81648715 * w ^ 2 + (-2.01371172)
        * w ^ 3 + 0.43385602 * w ^ 4 := by
      refine (isq_le 0.95 w (by norm_num) (le_trans (le_of_eq (by norm_num)) hw.1)).trans ?_
      refine le_of_sub_eq _ _ ((7 / 1900000000) + (4709 / 685900000000) * w + (312557 /
          49521980000000) * w ^ 2 + (74972973 / 22346793475000000) * w ^ 3 + (13067988979 /
          16134384888950000000) * w ^ 4) (by ring) ?_
      linarith [pow_nonneg hw0.le 1, pow_nonneg hw0.le 2, pow_nonneg hw0.le 3, pow_nonneg hw0.le 4]
    have hL0 : 0 ≤ Real.log (2 * (w * r)) := Real.log_nonneg (by linarith)
    have hL : Real.log (2 * (w * r)) ≤ (-0.357488435) + Real.log r + 1.05194 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-1.050635615919) + 1.05194 * w := by
      rw [hwl]
      linarith
    have hLlo : 14.26 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL140]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 14.26 2.65745841394 0.069595 2.66506255428
        (Real.log r + (-1.050635615919) + 1.05194 * w) 1.7810727 0.94314553 0.20961 1.1927
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL295 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL297]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.98471406 + 0.0259819465 * Real.log r + 0.0273314488 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 39.3614428 + 21.9979752 * Real.log r + 23.14055 * w + 0.402849703 *
        Real.log r ^ 2 + 0.847547432 * w * Real.log r + 0.445784523 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((319505451322971125963395324819 /
          72000000000000000000000000000000000000) + (3333112140264414499 /
          36000000000000000000000000) * Real.log r + (117913299241487409403903 /
          1800000000000000000000000000000) * w + 0.000000000691375 * Real.log r ^ 2 +
          0.000000000306930035 * w * Real.log r + 0.00000000035239599050895 * w ^ 2) (by ring) ?_)
      linarith [mul_nonneg (pow_nonneg hw0.le 1) (pow_nonneg hl0 1), pow_nonneg hl0 1,
          pow_nonneg hl0 2, pow_nonneg hw0.le 1, pow_nonneg hw0.le 2]
    have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    have hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ 0.0000693041 :=
      (wy_rpow_le w y 0.9025 (10 ^ 25) (by norm_num) hw.1 (by norm_num) hy).trans
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
      j9l, j9h, j10l, j10h⟩ := mom_0_9025_1
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    rw [mI_eq]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    linarith

/-- **Region `R2a`, `w ≤ 1`**: the first piece and the 16 lo pieces, added. -/
theorem loR2a (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 1
      (1 / Real.sqrt r * (0.8051692980876084758 + Real.log r * 0.20177822218454609558 +
          Real.log r ^ 2 * (-0.0029229141637241385747) + Real.log r ^ 3 * 0.0007085388490149107038 +
          Real.log r ^ 4 * 0.00001057372076953975311) + 1 / r * (19.649147378947298455 + Real.log r
          * 8.74541286121044644 + Real.log r ^ 2 * 0.1649893574942179288) +
          0.00005871842307307207429) := by
  have h0 := tR2a_first y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR2a_lo0 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR2a_lo1 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR2a_lo2 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR2a_lo3 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR2a_lo4 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR2a_lo5 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR2a_lo6 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR2a_lo7 y r hy hr0 hr1)
  have h9 := intBnd_add _ _ _ _ _ _ h8 (tR2a_lo8 y r hy hr0 hr1)
  have h10 := intBnd_add _ _ _ _ _ _ h9 (tR2a_lo9 y r hy hr0 hr1)
  have h11 := intBnd_add _ _ _ _ _ _ h10 (tR2a_lo10 y r hy hr0 hr1)
  have h12 := intBnd_add _ _ _ _ _ _ h11 (tR2a_lo11 y r hy hr0 hr1)
  have h13 := intBnd_add _ _ _ _ _ _ h12 (tR2a_lo12 y r hy hr0 hr1)
  have h14 := intBnd_add _ _ _ _ _ _ h13 (tR2a_lo13 y r hy hr0 hr1)
  have h15 := intBnd_add _ _ _ _ _ _ h14 (tR2a_lo14 y r hy hr0 hr1)
  have h16 := intBnd_add _ _ _ _ _ _ h15 (tR2a_lo15 y r hy hr0 hr1)
  exact intBnd_mono _ _ _ _ _ h16 (le_of_eq (by ring))

end Principia.Common.TernaryGoldbach.MC
