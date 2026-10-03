/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCData

set_option autoImplicit false

/-!
# Region `R0` of `g̃`, `w ≤ 1`: `r ∈ [150000, 520000]`, `y ≥ (10 ^ 25)`

GENERATED. The first piece `[w₁, 0.04]` and 16 pieces on the grid `0.04, 0.0625, 0.09, 0.1225, 0.16,
    0.2025, 0.25, 0.3025, 0.36, 0.4225, 0.49, 0.5625, 0.64, 0.7225, 0.81, 0.9025, 1` of the `w ≤ 1`
    integral of `gT`, each a certified majorant `(P(w, ℓ)/√r + Q(w, ℓ)/r + Y(w))e^{−w²/2}`
    integrated against the moments of `MNumCData`; their sum is `loR0`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **The first piece `[w₁, 0.04]` of region `R0`** (`ptFirstS`, `intBnd_lin`). -/
private theorem tR0_first (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 0.04
      (1 / Real.sqrt r * (0.0001719174180181647 + Real.log r * 0.0000778326051201967 +
          Real.log r ^ 2 * 0.000001710361792926441 + Real.log r ^ 3 * 0.0000001339868929140186 +
          Real.log r ^ 4 * 0.000000006100554117768196) + 1 / r * ((-0.00478795448) + Real.log r *
          0.01286269008 + Real.log r ^ 2 * 0.0006421978216) + 0.000000174411008) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  obtain ⟨-, hm0, hm1⟩ := w1_facts y r (le_trans (by norm_num) hy) (by linarith)
  have key : ∀ w ∈ Set.Icc (max (1 / kK y) (1000 / r)) 0.04, OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * 0.2 * (((0.439446723 + (-0.00390525596) * Real.log r + 0.000958157427 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.60750945 + 0.0562762891 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-5.9849431) + 16.0783626 * Real.log r + 0.802747277
      * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000681293) * w ∧ 0 ≤ (0.70711 * 0.2 * (((0.439446723 +
      (-0.00390525596) * Real.log r + 0.000958157427 * Real.log r ^ 2) * ((-2.52572864) +
      Real.log r) + 0.5) * (1.60750945 + 0.0562762891 * Real.log r) + 2.5) * (1 / Real.sqrt r) +
      ((-5.9849431) + 16.0783626 * Real.log r + 0.802747277 * Real.log r ^ 2) * (1 / r) + 3.2 *
      0.0000681293) := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) ((le_max_right _ _).trans hw.1)
    have hwr1 := wr_ge y r w hr hw.1
    have hw1 : w ≤ 1 := le_trans hw.2 (by norm_num)
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hτ : Real.log w ≤ (-3.21887582356) + 0 * w := by
      have := Real.log_le_log hw0 hw.2
      linarith [lgU11]
    have hR := rChordLo y r w 19.997138805 2.08 (-3.21887582356) 0 9.772473 11.01567 0.09780271
        0.01088939 (1361 / 2514) 0.43267055323 0.436241888 0.17598 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith) (by linarith) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (1361 / 2514) = (3875 / 2514) by norm_num]; exact lgU12)
        (by norm_num) (by norm_num)
    have hRs : 0.436241888 + 0.17598 * ((2.08 + Real.log r + ((-3.21887582356) + 0 * w)) *
        (0.09780271 + 0.01088939 * (Real.log r + 2 / 3 * ((-3.21887582356) + 0 * w) - 9.772473)) /
        2) ≤ 0.439446723 + (-0.00390525596) * Real.log r + 0.000958157427 * Real.log r ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000012136072962471778797355936 + 0.00000000000718669086486 *
          Real.log r + 0.0000000000009 * Real.log r ^ 2) (by ring) ?_
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
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 6.907 1.93253538928 0.13868 1.975586159
        (Real.log r + (-3.21887582356)) 1.7810727 1.2969336 0.22784 1.09727 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL14 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL16]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.60750945 + 0.0562762891 * Real.log r := hS.trans
        (by linarith)
    have hLs : lL (w * r) ≤ (-5.9849431) + 16.0783626 * Real.log r + 0.802747277 * Real.log r ^ 2 :=
        by
      refine hLL.trans (le_of_sub_eq _ _ ((3964725302088171107412149 /
          1875000000000000000000000000000000) + (7030241448935297 / 112500000000000000000000) *
          Real.log r + 0.000000000383 * Real.log r ^ 2) (by ring) ?_)
      linarith [pow_nonneg hl0 1, pow_nonneg hl0 2]
    have hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ 0.0000681293 :=
      (wy_rpow_w_le w y (10 ^ 25) hw0 hw1 (by norm_num) hy).trans
        (rpow_neg6_le _ _ (by norm_num) (by norm_num) (by norm_num))
    exact ptFirstS y r w 0.2 _ _ _ _ _ hy0 hr hw0 hsp hR.1 hRb hL0 hL hSs hLL0 hLs hY
  have hC0 := (key 0.04 ⟨hm1, le_rfl⟩).2
  refine intBnd_mono _ _ _ _ _ (intBnd_lin _ _ 0.04 _ hm0 hm1 hC0 (fun w hw => (key w hw).1)) ?_
  have e : (0.70711 * 0.2 * (((0.439446723 + (-0.00390525596) * Real.log r + 0.000958157427 *
      Real.log r ^ 2) * ((-2.52572864) + Real.log r) + 0.5) * (1.60750945 + 0.0562762891 *
      Real.log r) + 2.5) * (1 / Real.sqrt r) + ((-5.9849431) + 16.0783626 * Real.log r + 0.802747277
      * Real.log r ^ 2) * (1 / r) + 3.2 * 0.0000681293) * (0.04 ^ 2 / 2) = 1 / Real.sqrt r *
      (0.0001719174180181646219365877930496 + Real.log r * 0.0000778326051201966906655781388131328 +
      Real.log r ^ 2 * 0.000001710361792926440233826064981653504 + Real.log r ^ 3 *
      0.0000001339868929140185208126102604721152 + Real.log r ^ 4 *
      0.00000000610055411776819505054832) + 1 / r * ((-0.00478795448) + Real.log r * 0.01286269008 +
      Real.log r ^ 2 * 0.0006421978216) + 0.000000174411008 := by
    ring
  refine le_trans (le_of_eq e) ?_
  refine rows_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (one_div_nonneg.mpr (Real.sqrt_nonneg r)) (one_div_nonneg.mpr hr.le) hl0
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    linarith

set_option maxHeartbeats 4000000 in
-- generated certificate: `norm_num`/`linarith` over a few hundred exact numerals
/-- **Piece `[0.04, 0.0625]` of region `R0`** (`ptLoS`; moments `mom_0_04_0_0625`). -/
private theorem tR0_lo0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.04 0.0625
      (1 / Real.sqrt r * (0.0003082671323852724 + Real.log r * 0.0001390857993146762 +
          Real.log r ^ 2 * 0.000001761469872127953 + Real.log r ^ 3 * 0.0000002651581645617266 +
          Real.log r ^ 4 * 0.000000008223524935681891) + 1 / r * ((-0.0017138862353481) + Real.log r
          * 0.02035108620443136 + Real.log r ^ 2 * 0.0007514205938896986) +
          0.00000002235376319024123) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.04 : ℝ) 0.0625, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.78397143846067579082419343431015625, -134.59017126542203494105437563100314453125,
          1704.609375068967548976113111172672265351875,
          23237.7981807529625100588225652697937762015,
          -756963.9982131688669963287817751334035579557,
          5197771.88472510487709819076083394122690141, 825553.76957859542177963614598319260291898,
          1930517.745349228943917062533506108278812, 1695581.384346384935683407061578841536]
        [0, 0, 6.351882346506219537488522993493978515625,
          -209.2546422441169598695105692136671322265625,
          4691.00818740216227059533587098415088121045,
          -55167.88286590282843498871900375017113804217,
          260488.0764043729036133517241469013556326838, 28472.980418616783817676190043530980309178,
          336715.54550592081876265645651519390236128, 386274.56424129035805572381109243939864]
        [0, 0, 0.0505797458731740397378784811288385546875,
          -1.1189073665256078874016618264454781640625, 19.782921621902895628867259534860146479784,
          -51.322337868031013608969646852021574247482, -2304.7617543954802149966644139485948069602,
          17908.4063727434625586565179210410275792548, 32591.9104579658020079045290390754410524]
        [0, 0, 0.01094746351575518670473796692219262890625,
          -0.337037639087129774668076013445930078125, 7.2813372599967792900556136571089334865626,
          -76.83685114981476256410884742849591429682, 226.24129679712512776127810466381344684236,
          1209.97445661699745237833261270797558868]
        [0, 0, 0.000384903804099040866228512109375, -0.0128301268033013622076170703125,
          0.28867785323068600498781973560982, -3.436641100206882825504218297634,
          16.705894300547852280088854009252]
        [0, -18.9863213, 322.579788, 254.609498]
        [0, 16.3305988, 25.779207]
        [0, 0.652536058]
        [0, 0, 0.0003728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.78397143846067579082419343431015625, -134.59017126542203494105437563100314453125,
          1704.609375068967548976113111172672265351875,
          23237.7981807529625100588225652697937762015,
          -756963.9982131688669963287817751334035579557,
          5197771.88472510487709819076083394122690141, 825553.76957859542177963614598319260291898,
          1930517.745349228943917062533506108278812, 1695581.384346384935683407061578841536]
        [0, 0, 6.351882346506219537488522993493978515625,
          -209.2546422441169598695105692136671322265625,
          4691.00818740216227059533587098415088121045,
          -55167.88286590282843498871900375017113804217,
          260488.0764043729036133517241469013556326838, 28472.980418616783817676190043530980309178,
          336715.54550592081876265645651519390236128, 386274.56424129035805572381109243939864]
        [0, 0, 0.0505797458731740397378784811288385546875,
          -1.1189073665256078874016618264454781640625, 19.782921621902895628867259534860146479784,
          -51.322337868031013608969646852021574247482, -2304.7617543954802149966644139485948069602,
          17908.4063727434625586565179210410275792548, 32591.9104579658020079045290390754410524]
        [0, 0, 0.01094746351575518670473796692219262890625,
          -0.337037639087129774668076013445930078125, 7.2813372599967792900556136571089334865626,
          -76.83685114981476256410884742849591429682, 226.24129679712512776127810466381344684236,
          1209.97445661699745237833261270797558868]
        [0, 0, 0.000384903804099040866228512109375, -0.0128301268033013622076170703125,
          0.28867785323068600498781973560982, -3.436641100206882825504218297634,
          16.705894300547852280088854009252]
        [0, -18.9863213, 322.579788, 254.609498]
        [0, 16.3305988, 25.779207]
        [0, 0.652536058]
        [0, 0, 0.0003728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.04 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.050625 (-2.98330975251) hw0 (by norm_num) lgU18
    have hτ1 : w / 0.050625 ≤ 19.75309 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.98330975251) + 19.75309 * w := by linarith
    have hwa : Real.log 0.04 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.98330975251) 19.75309 9.789599 11.32909
        0.0979668 0.01130206 (9608 / 17517) 0.437283974409 0.436683279 0.17517 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (9608 / 17517) = (27125 / 17517) by norm_num]; exact lgU21)
        (by norm_num) (by norm_num)
    have hRs : 0.436683279 + 0.17517 * ((2.08 + Real.log r + ((-3.98330975251) + 19.75309 * w)) *
        (0.0979668 + 0.01130206 * (Real.log r + 2 / 3 * ((-3.98330975251) + 19.75309 * w) -
        9.789599)) / 2) ≤ 0.443799579 + (-0.00562297686) * Real.log r + (-0.0986657729) * w +
        0.000989890926 * Real.log r ^ 2 + 0.0325890076 * w * Real.log r + 0.25749344 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000028934296627790752660985166 + 0.000000000008046661478335 *
          Real.log r + 0.00000000006119943950143564412 * w + 0.0000000000009 * Real.log r ^ 2 +
          0.000000000043860735 * w * Real.log r + 0.00000000029316041836846 * w ^ 2) (by ring) ?_
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
    have hLlo : 8.699 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL20]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 8.699 2.16320807571 0.11273 2.18275970068
        (Real.log r + (-3.98330975251) + 19.75309 * w) 1.7810727 1.1586357 0.22258 1.1232
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL22 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL24]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.67195908 + 0.0446896849 * Real.log r + 0.882759367 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-18.9863213) + 16.3305988 * Real.log r + 322.579788 * w + 0.652536058 *
        Real.log r ^ 2 + 25.779207 * w * Real.log r + 254.609498 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ (0.000000078726076654304801057235490925 +
          (35243206773037937 / 1800000000000000000000000) * Real.log r + (96563663527642794297533 /
          180000000000000000000000000000) * w + 0.00000000021925 * Real.log r ^ 2 +
          0.000000044823289965 * w * Real.log r + 0.000000442884240387370925 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.0625, 0.09]` of region `R0`** (`ptLoS`; moments `mom_0_0625_0_09`). -/
private theorem tR0_lo1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.0625 0.09
      (1 / Real.sqrt r * (0.0007936451057984886 + Real.log r * 0.0003173115500319872 +
          Real.log r ^ 2 * 0.00000358147608032768 + Real.log r ^ 3 * 0.0000006358768808431544 +
          Real.log r ^ 4 * 0.00000001776053564303629) + 1 / r * (0.01187962476960169 + Real.log r *
          0.03854910812346002 + Real.log r ^ 2 * 0.001300169779664224) + 0.00000005576178214681686)
          := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.0625 : ℝ) 0.09, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 8.0216481302812087717746653996259375, -101.60643078533549386567386486819365625,
          989.96542286884146058098069609216140625, 2407.0352939261765068526704625583586125,
          -101881.48596716388495479368377895711995, 489678.916691335196153116619271273328,
          33696.947431448477960639956370235776, 87204.4317220230103459565442967552,
          44736.005614793585316168854784]
        [0, 0, 5.2752474807081181614035492012242875, -111.4300311131768299430410169786485546875,
          1600.705220394343346769080032053001798125, -12085.4905173549938991428019465215743275,
          36940.8970255218773401411528329243864, -176.9716403809061987860658555349568,
          22769.537370096333288971996019156992, 15224.21094802101474615405329664]
        [0, 0, 0.03320808229937485327514185428667453125, -0.373202797340430289393467700327880625,
          3.313333878650741687506399563795216, 19.63697105971158208443142714658592,
          -461.87771104551396828507095888467968, 1824.3321836597529603997187958429696,
          1918.883541990707395297792991232]
        [0, 0, 0.009659271442397212848205079355346875, -0.1914501681906128263880803420833375,
          2.65555668316427699144231378246256, -18.1187051021527340451346187616576,
          36.1308802779097069501918034337792, 106.418006678236772872972491264]
        [0, 0, 0.00030141949945367532546421875, -0.00643028265501174027657,
          0.092596070232169059982608, -0.70549386843557379034368, 2.19486981291067401440256]
        [0, -12.4705157, 227.064099, 108.742887]
        [0, 17.1717102, 16.4473498]
        [0, 0.621914966]
        [0, 0, 0.0003460768] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 8.0216481302812087717746653996259375, -101.60643078533549386567386486819365625,
          989.96542286884146058098069609216140625, 2407.0352939261765068526704625583586125,
          -101881.48596716388495479368377895711995, 489678.916691335196153116619271273328,
          33696.947431448477960639956370235776, 87204.4317220230103459565442967552,
          44736.005614793585316168854784]
        [0, 0, 5.2752474807081181614035492012242875, -111.4300311131768299430410169786485546875,
          1600.705220394343346769080032053001798125, -12085.4905173549938991428019465215743275,
          36940.8970255218773401411528329243864, -176.9716403809061987860658555349568,
          22769.537370096333288971996019156992, 15224.21094802101474615405329664]
        [0, 0, 0.03320808229937485327514185428667453125, -0.373202797340430289393467700327880625,
          3.313333878650741687506399563795216, 19.63697105971158208443142714658592,
          -461.87771104551396828507095888467968, 1824.3321836597529603997187958429696,
          1918.883541990707395297792991232]
        [0, 0, 0.009659271442397212848205079355346875, -0.1914501681906128263880803420833375,
          2.65555668316427699144231378246256, -18.1187051021527340451346187616576,
          36.1308802779097069501918034337792, 106.418006678236772872972491264]
        [0, 0, 0.00030141949945367532546421875, -0.00643028265501174027657,
          0.092596070232169059982608, -0.70549386843557379034368, 2.19486981291067401440256]
        [0, -12.4705157, 227.064099, 108.742887]
        [0, 17.1717102, 16.4473498]
        [0, 0.621914966]
        [0, 0, 0.0003460768] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.0625 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.075625 (-2.58196836159) hw0 (by norm_num) lgU26
    have hτ1 : w / 0.075625 ≤ 13.22315 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.58196836159) + 13.22315 * w := by linarith
    have hwa : Real.log 0.0625 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.58196836159) 13.22315 10.08137 11.567 0.1008495
        0.01196295 (10027 / 17098) 0.46149431485 0.439060333 0.17098 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (10027 / 17098) = (27125 / 17098) by norm_num]; exact lgU29)
        (by norm_num) (by norm_num)
    have hRs : 0.439060333 + 0.17098 * ((2.08 + Real.log r + ((-3.58196836159) + 13.22315 * w)) *
        (0.1008495 + 0.01196295 * (Real.log r + 2 / 3 * ((-3.58196836159) + 13.22315 * w) -
        10.08137)) / 2) ≤ 0.445264869 + (-0.00566701839) * Real.log r + (-0.0681652201) * w +
        0.0010227126 * Real.log r ^ 2 + 0.0225391368 * w * Real.log r + 0.119215355 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000001774748994074268771759443 + 0.000000000002056820678075 *
          Real.log r + 0.000000000088118429595479949 * w + 0.0000000000045 * Real.log r ^ 2 +
          0.000000000038023625 * w * Real.log r + 0.0000000004903488387675 * w ^ 2) (by ring) ?_
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
    have hLlo : 9.145 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL28]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 9.145 2.21320728098 0.10744 2.23082272756
        (Real.log r + (-3.58196836159) + 13.22315 * w) 1.7810727 1.1324606 0.22127 1.12985
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL30 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL32]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.71382699 + 0.0423418845 * Real.log r + 0.55989309 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-12.4705157) + 17.1717102 * Real.log r + 227.064099 * w + 0.621914966 *
        Real.log r ^ 2 + 16.4473498 * w * Real.log r + 108.742887 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((4161651702039955391220475363 /
          45000000000000000000000000000000000) + (22090704908323963 / 225000000000000000000000) *
          Real.log r + (2552089092170080226869 / 4500000000000000000000000000) * w + 0.000000000614
          * Real.log r ^ 2 + 0.0000000509122282 * w * Real.log r + 0.000000582675015161415 *
          w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.09, 0.1225]` of region `R0`** (`ptLoS`; moments `mom_0_09_0_1225`). -/
private theorem tR0_lo2 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.09 0.1225
      (1 / Real.sqrt r * (0.001730613956764407 + Real.log r * 0.0006295564911555026 + Real.log r ^ 2
          * 0.000006564049140621066 + Real.log r ^ 3 * 0.000001313912708222564 + Real.log r ^ 4 *
          0.00000003388527678913936) + 1 / r * (0.04115855260707228 + Real.log r *
          0.06535043463563446 + Real.log r ^ 2 * 0.002055887233780219) + 0.000000119714379325104) :=
          by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.09 : ℝ) 0.1225, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 8.0150512692101025396763224705, -76.067158287125433928365114444947118885,
          558.4703634622952940582535911238067337883, -4.29591638989069217661364873904561849098,
          -19459.69316689845710942571368705295722794888,
          70371.2913530752942944523490618569367008882, 2116.507891736528073380005188708336279066,
          6768.585166084692699643348664610854463672, 2245.8866495682307741339620422336813568]
        [0, 0, 4.518072009678410859729309504678609375, -66.36689475851507417483859578660184056913,
          662.68826556170287026871079707672053107539,
          -3482.749254614483781538689399523804451287612,
          7456.73352206829351934959745497289430858038, -318.6495520351189698114328788994831097084,
          2472.4942817574972984717414978824143972908, 1067.49795740435900744298896711269354752]
        [0, 0, 0.02348484980433062671015497685040296875,
          -0.1321846292250195369177065417620825768692, 0.394069982406729447704454127590223533572,
          11.9087221416933469190048428670104440663, -112.89623721793819666746148690852378093192,
          278.3739934015208449615153722718508902044, 187.92411215141433276694473390072608256]
        [0, 0, 0.008677101103824628924781678165765859375,
          -0.1199543027510952340251024861699906535422, 1.158158056935545857903311347152586109628,
          -5.52818450522549795936201598481902902569, 7.95726519895466229373267734426964903098,
          14.556287929686193326403621427964746112]
        [0, 0, 0.0002476044557414311575163828125, -0.00366821413565574282624034673178,
          0.0366821416583990504995766879092, -0.194085405176777886808072933611,
          0.419320322453512023069381282702]
        [0, -6.6960052, 168.716021, 53.6737692]
        [0, 17.820629, 11.3385833]
        [0, 0.598818906]
        [0, 0, 0.0003256704] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 8.0150512692101025396763224705, -76.067158287125433928365114444947118885,
          558.4703634622952940582535911238067337883, -4.29591638989069217661364873904561849098,
          -19459.69316689845710942571368705295722794888,
          70371.2913530752942944523490618569367008882, 2116.507891736528073380005188708336279066,
          6768.585166084692699643348664610854463672, 2245.8866495682307741339620422336813568]
        [0, 0, 4.518072009678410859729309504678609375, -66.36689475851507417483859578660184056913,
          662.68826556170287026871079707672053107539,
          -3482.749254614483781538689399523804451287612,
          7456.73352206829351934959745497289430858038, -318.6495520351189698114328788994831097084,
          2472.4942817574972984717414978824143972908, 1067.49795740435900744298896711269354752]
        [0, 0, 0.02348484980433062671015497685040296875,
          -0.1321846292250195369177065417620825768692, 0.394069982406729447704454127590223533572,
          11.9087221416933469190048428670104440663, -112.89623721793819666746148690852378093192,
          278.3739934015208449615153722718508902044, 187.92411215141433276694473390072608256]
        [0, 0, 0.008677101103824628924781678165765859375,
          -0.1199543027510952340251024861699906535422, 1.158158056935545857903311347152586109628,
          -5.52818450522549795936201598481902902569, 7.95726519895466229373267734426964903098,
          14.556287929686193326403621427964746112]
        [0, 0, 0.0002476044557414311575163828125, -0.00366821413565574282624034673178,
          0.0366821416583990504995766879092, -0.194085405176777886808072933611,
          0.419320322453512023069381282702]
        [0, -6.6960052, 168.716021, 53.6737692]
        [0, 17.820629, 11.3385833]
        [0, 0.598818906]
        [0, 0, 0.0003256704] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.09 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.105625 (-2.24786019246) hw0 (by norm_num) lgU34
    have hτ1 : w / 0.105625 ≤ 9.467456 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-3.24786019246) + 9.467456 * w := by linarith
    have hwa : Real.log 0.09 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-3.24786019246) 9.467456 10.32119 11.76952
        0.1033491 0.0125612 (10377 / 16748) 0.482176964511 0.441170502 0.16748 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (10377 / 16748) = (27125 / 16748) by norm_num]; exact lgU37)
        (by norm_num) (by norm_num)
    have hRs : 0.441170502 + 0.16748 * ((2.08 + Real.log r + ((-3.24786019246) + 9.467456 * w)) *
        (0.1033491 + 0.0125612 * (Real.log r + 2 / 3 * ((-3.24786019246) + 9.467456 * w) -
        10.32119)) / 2) ≤ 0.446402176 + (-0.00570815146) * Real.log r + (-0.0501649301) * w +
        0.00105187489 * Real.log r ^ 2 + 0.0165976321 * w * Real.log r + 0.0628549404 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000005836480501410152329502528 + (29534705903 /
          3750000000000000000000) * Real.log r + (1129624527849887 / 73242187500000000000000000) * w
          + 0.000000000002 * Real.log r ^ 2 + (157637 / 2343750000000000) * w * Real.log r +
          (118235081 / 11444091796875000000) * w ^ 2) (by ring) ?_
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
    have hLlo : 9.51 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL36]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 9.51 2.25234387569 0.10345 2.26866687559
        (Real.log r + (-3.24786019246) + 9.467456 * w) 1.7810727 1.1127831 0.22025 1.13508
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL38 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL40]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.7460417 + 0.0405814966 * Real.log r + 0.384203534 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-6.6960052) + 17.820629 * Real.log r + 168.716021 * w + 0.598818906 *
        Real.log r ^ 2 + 11.3385833 * w * Real.log r + 53.6737692 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((20763643585487649181634107 /
          6000000000000000000000000000000000) + (13932978227238353 / 180000000000000000000000) *
          Real.log r + (2202211536177142320937 / 2812500000000000000000000000) * w +
          0.00000000085125 * Real.log r ^ 2 + 0.00000002707207184 * w * Real.log r +
          0.00000008060942448701952 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.1225, 0.16]` of region `R0`** (`ptLoS`; moments `mom_0_1225_0_16`). -/
private theorem tR0_lo3 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.1225 0.16
      (1 / Real.sqrt r * (0.003351076061752263 + Real.log r * 0.001129141476989513 + Real.log r ^ 2
          * 0.00001113746297748047 + Real.log r ^ 3 * 0.000002439452584485927 + Real.log r ^ 4 *
          0.00000005903132735702063) + 1 / r * (0.09231966352939263 + Real.log r *
          0.1023314091131748 + Real.log r ^ 2 * 0.003044229609018053) + 0.0000002304379073870758) :=
          by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.1225 : ℝ) 0.16, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.8952714170628291391347971881625, -57.8543104573836211176784954795216557384,
          327.1029147160046993851852192701037834124, -222.024532480927745849102761070812426212,
          -4741.6648859143698699846971292228008373508, 13563.976688372256149953115629809608327812,
          157.19332737476131827638958888663248832, 768.25562798690729103982561802899660528,
          176.766908428947014628540714244688352]
        [0, 0, 3.95516993974880081086779289276021875, -42.730266430788016197006583748196384024064,
          313.708561711091730072412408603110484099684,
          -1213.527752632674717035172248688181905596912,
          1921.90635110052459489327669267115770242718, -104.4681955619754504001305425443433029916,
          374.1257790644211884630953932246000257432, 111.86029565307953472797562991604104688]
        [0, 0, 0.0175259996519926843036709421027159375,
          -0.04309733026098002749667319740579021153912,
          -0.1525735976498432857331460005410568272204, 5.781704366333026395431497359590133345216,
          -33.004411679531216007557516235494149219728, 56.34183411475491484872758892824921919392,
          26.217253573452823104838184489533129408]
        [0, 0, 0.0079036877961571105042387500411815625,
          -0.08054707120422078325454358814923552694792, 0.5723912685822624185017239124574412632348,
          -2.018702831497085960704679912773076626472, 2.196503220777027107047264362362726287472,
          2.7036539399934749249919252804445367648]
        [0, 0, 0.0002101498171294194827491640625, -0.002287344947005513905123678540994,
          0.01680498330547069582766147687071, -0.0653254937936718342668108251894,
          0.1036912603505086295302099038604]
        [0, -1.51989852, 130.440938, 29.3589811]
        [0, 18.3432546, 8.25721239]
        [0, 0.580585174]
        [0, 0, 0.00030935776] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.8952714170628291391347971881625, -57.8543104573836211176784954795216557384,
          327.1029147160046993851852192701037834124, -222.024532480927745849102761070812426212,
          -4741.6648859143698699846971292228008373508, 13563.976688372256149953115629809608327812,
          157.19332737476131827638958888663248832, 768.25562798690729103982561802899660528,
          176.766908428947014628540714244688352]
        [0, 0, 3.95516993974880081086779289276021875, -42.730266430788016197006583748196384024064,
          313.708561711091730072412408603110484099684,
          -1213.527752632674717035172248688181905596912,
          1921.90635110052459489327669267115770242718, -104.4681955619754504001305425443433029916,
          374.1257790644211884630953932246000257432, 111.86029565307953472797562991604104688]
        [0, 0, 0.0175259996519926843036709421027159375,
          -0.04309733026098002749667319740579021153912,
          -0.1525735976498432857331460005410568272204, 5.781704366333026395431497359590133345216,
          -33.004411679531216007557516235494149219728, 56.34183411475491484872758892824921919392,
          26.217253573452823104838184489533129408]
        [0, 0, 0.0079036877961571105042387500411815625,
          -0.08054707120422078325454358814923552694792, 0.5723912685822624185017239124574412632348,
          -2.018702831497085960704679912773076626472, 2.196503220777027107047264362362726287472,
          2.7036539399934749249919252804445367648]
        [0, 0, 0.0002101498171294194827491640625, -0.002287344947005513905123678540994,
          0.01680498330547069582766147687071, -0.0653254937936718342668108251894,
          0.1036912603505086295302099038604]
        [0, -1.51989852, 130.440938, 29.3589811]
        [0, 18.3432546, 8.25721239]
        [0, 0.580585174]
        [0, 0, 0.00030935776] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.1225 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.140625 (-1.96165850521) hw0 (by norm_num) lgU42
    have hτ1 : w / 0.140625 ≤ 7.111112 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.96165850521) + 7.111112 * w := by linarith
    have hwa : Real.log 0.1225 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.96165850521) 7.111112 10.52469 11.94567
        0.1055694 0.01311176 (10676 / 16449) 0.500191127206 0.443066844 0.16449 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (10676 / 16449) = (27125 / 16449) by norm_num]; exact lgU45)
        (by norm_num) (by norm_num)
    have hRs : 0.443066844 + 0.16449 * ((2.08 + Real.log r + ((-2.96165850521) + 7.111112 * w)) *
        (0.1055694 + 0.01311176 * (Real.log r + 2 / 3 * ((-2.96165850521) + 7.111112 * w) -
        10.52469)) / 2) ≤ 0.447295468 + (-0.00574697419) * Real.log r + (-0.0386137235) * w +
        0.00107837671 * Real.log r ^ 2 + 0.0127807626 * w * Real.log r + 0.0363541735 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000095807946448553874018730472 + 0.00000000000007209935542 *
          Real.log r + 0.000000000034348652387282741632 * w + 0.0000000000088 * Real.log r ^ 2 +
          0.000000000099293776 * w * Real.log r + 0.0000000000648311848155648 * w ^ 2) (by ring) ?_
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
    have hLlo : 9.818 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL44]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 9.818 2.28421743479 0.1003 2.29958958499
        (Real.log r + (-2.96165850521) + 7.111112 * w) 1.7810727 1.0972555 0.21941 1.13942
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL46 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL48]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.77194473 + 0.0391957517 * Real.log r + 0.27872538 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ (-1.51989852) + 18.3432546 * Real.log r + 130.440938 * w + 0.580585174 *
        Real.log r ^ 2 + 8.25721239 * w * Real.log r + 29.3589811 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((112900536305979325697850661 /
          12000000000000000000000000000000000) + (5523327675628097 / 180000000000000000000000) *
          Real.log r + (7044533214261383514233 / 22500000000000000000000000000) * w +
          0.0000000006175 * Real.log r ^ 2 + 0.00000000307524732 * w * Real.log r +
          0.00000005439537406010992 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.16, 0.2025]` of region `R0`** (`ptLoS`; moments `mom_0_16_0_2025`). -/
private theorem tR0_lo4 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.16 0.2025
      (1 / Real.sqrt r * (0.005934516357096849 + Real.log r * 0.001875748199718095 + Real.log r ^ 2
          * 0.00001781681635616957 + Real.log r ^ 3 * 0.000004176254772598707 + Real.log r ^ 4 *
          0.00000009593253281330265) + 1 / r * (0.1717368056312141 + Real.log r * 0.1508865866149721
          + Real.log r ^ 2 * 0.004287045529265878) + 0.0000004080984535493015) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.16 : ℝ) 0.2025, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.7227724397869369296903822019009765625,
          -44.892659525554522060418794915959008031525,
          200.4564609016657145282662714425929912523025,
          -169.6693986210255741935289901308407605588335,
          -1381.931249017337329556545885440219857320506,
          3244.6946049419215280062842621203863083891, 7.32161796061975599256475783027134273538,
          115.5116084193963965298999122110297667487, 19.39851961048268182207828617041599463]
        [0, 0, 3.5192980116219310627557958912414072265625,
          -29.134432669571398144495473410415458909549,
          163.86149270980987685461278086194862222489595,
          -486.024192596075448839692904175384863531297,
          592.547232267654979697602424890693239993614, -33.1049040000612791006361541172891279513,
          72.33152185426115310101080675989725512085, 15.767356910451903887863620409614510065]
        [0, 0, 0.013674808677695043361130611001974072265625,
          -0.0080917844629613046967641013696510210348, -0.2132045272398482154051901338239676228414,
          2.821355454029684295300669574545699507082, -11.138302092410493385313949338794177537233,
          14.04276791708381557144494295358385685688, 4.746630706278853236833449142863494562]
        [0, 0, 0.007276038280673266655064269381479833984375,
          -0.0569252477396212767936765802125337624709, 0.310160924118470542212423441148598639713,
          -0.841240840621305005591406492370304488038, 0.716239278793843180443396996282739905705,
          0.6287306998448554061051999066539819045]
        [0, 0, 0.0001826810376709314787496630859375, -0.00152234197910644976279454290472,
          0.0085631736621666977847722934009, -0.0254856358130547915017159987754,
          0.0309721270747158434305310327865]
        [0, 3.16693732, 103.949391, 17.3446751]
        [0, 18.775856, 6.26576292]
        [0, 0.56587663]
        [0, 0, 0.00029588992] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.7227724397869369296903822019009765625,
          -44.892659525554522060418794915959008031525,
          200.4564609016657145282662714425929912523025,
          -169.6693986210255741935289901308407605588335,
          -1381.931249017337329556545885440219857320506,
          3244.6946049419215280062842621203863083891, 7.32161796061975599256475783027134273538,
          115.5116084193963965298999122110297667487, 19.39851961048268182207828617041599463]
        [0, 0, 3.5192980116219310627557958912414072265625,
          -29.134432669571398144495473410415458909549,
          163.86149270980987685461278086194862222489595,
          -486.024192596075448839692904175384863531297,
          592.547232267654979697602424890693239993614, -33.1049040000612791006361541172891279513,
          72.33152185426115310101080675989725512085, 15.767356910451903887863620409614510065]
        [0, 0, 0.013674808677695043361130611001974072265625,
          -0.0080917844629613046967641013696510210348, -0.2132045272398482154051901338239676228414,
          2.821355454029684295300669574545699507082, -11.138302092410493385313949338794177537233,
          14.04276791708381557144494295358385685688, 4.746630706278853236833449142863494562]
        [0, 0, 0.007276038280673266655064269381479833984375,
          -0.0569252477396212767936765802125337624709, 0.310160924118470542212423441148598639713,
          -0.841240840621305005591406492370304488038, 0.716239278793843180443396996282739905705,
          0.6287306998448554061051999066539819045]
        [0, 0, 0.0001826810376709314787496630859375, -0.00152234197910644976279454290472,
          0.0085631736621666977847722934009, -0.0254856358130547915017159987754,
          0.0309721270747158434305310327865]
        [0, 3.16693732, 103.949391, 17.3446751]
        [0, 18.775856, 6.26576292]
        [0, 0.56587663]
        [0, 0, 0.00029588992] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.16 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.180625 (-1.71133221913) hw0 (by norm_num) lgU50
    have hτ1 : w / 0.180625 ≤ 5.536333 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.71133221913) + 5.536333 * w := by linarith
    have hwa : Real.log 0.16 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.71133221913) 5.536333 10.70137 12.10144
        0.1075759 0.01362456 (10938 / 16187) 0.516247361576 0.444802097 0.16187 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (10938 / 16187) = (27125 / 16187) by norm_num]; exact lgU53)
        (by norm_num) (by norm_num)
    have hRs : 0.444802097 + 0.16187 * ((2.08 + Real.log r + ((-2.71133221913) + 5.536333 * w)) *
        (0.1075759 + 0.01362456 * (Real.log r + 2 / 3 * ((-2.71133221913) + 5.536333 * w) -
        10.70137)) / 2) ≤ 0.448013674 + (-0.00578315541) * Real.log r + (-0.0307327267) * w +
        0.00110270377 * Real.log r ^ 2 + 0.0101748921 * w * Real.log r + 0.0225326363 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000073196837729797274046360744 + 0.00000000000722911686278 *
          Real.log r + 0.000000000043879878866603508592 * w + 0.0000000000064 * Real.log r ^ 2 +
          0.000000000040595202 * w * Real.log r + 0.0000000000280317025897064 * w ^ 2) (by ring) ?_
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
    have hLlo : 10.08 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL52]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 10.08 2.3105532617 0.097759 2.32525001362
        (Real.log r + (-2.71133221913) + 5.536333 * w) 1.7810727 1.0847489 0.21871 1.14307
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL54 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL56]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.79330129 + 0.0380808855 * Real.log r + 0.210828463 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 3.16693732 + 18.775856 * Real.log r + 103.949391 * w + 0.56587663 *
        Real.log r ^ 2 + 6.26576292 * w * Real.log r + 17.3446751 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((25902936693412700512201859971 /
          3600000000000000000000000000000000000) + (1720149285939890693 /
          18000000000000000000000000) * Real.log r + (6354455256675452860048769 /
          18000000000000000000000000000000) * w + 0.000000000242275 * Real.log r ^ 2 +
          0.00000000148705015515 * w * Real.log r + 0.000000092030222423306032475 *
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
/-- **Piece `[0.2025, 0.25]` of region `R0`** (`ptLoS`; moments `mom_0_2025_0_25`). -/
private theorem tR0_lo5 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.2025 0.25
      (1 / Real.sqrt r * (0.009799425718887041 + Real.log r * 0.002933486536825025 + Real.log r ^ 2
          * 0.00002709299698689128 + Real.log r ^ 3 * 0.00000670882009822075 + Real.log r ^ 4 *
          0.0000001472869750145066) + 1 / r * (0.2857087668778537 + Real.log r * 0.2121878852741742
          + Real.log r ^ 2 * 0.005791936042375963) + 0.0000006764340992411399) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.2025 : ℝ) 0.25, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.526616413170889192511566402, -35.506235696030525492006744905860675232,
          128.0644772415629033779350556964340649712, -108.53426230764455146586104596201537500208,
          -462.41437498587887460782059956137346736112, 916.4567324362352131540751977238539775152,
          -2.536086811024888808039667199733385876, 21.5891108980189294231019261082103230388,
          2.74510391966298007046315230698725521]
        [0, 0, 3.172351573820453267210963322691, -20.765162003774987708097611251132080505456,
          92.3266591351470737161458598224002124970448,
          -216.6464493102334165639763331243020609187568,
          209.669145893708302284841295708354896722448, -11.28029290977214883289545365906055808588,
          16.902574930936909429505702033997837625332, 2.7871382922835866181128016009305790969]
        [0, 0, 0.01097074197014263170576904529198, 0.00651090430451872703396716702645549305632,
          -0.18158658935579082063043889660506733952384, 1.4450225128055979506020261138622535211872,
          -4.2298833695142363675750202355225527105632, 4.1118995002530087342870049725462871480616,
          1.04808011907856763730519770287473012872]
        [0, 0, 0.00675876778143491015740596390926, -0.04187780051899307261492156047172241501216,
          0.18050761384247056467489320250488881536, -0.3883093825013623993941445531288455959136,
          0.2660084970993729255661225966314105257184, 0.17341358837353076309513383869391178678]
        [0, 0, 0.000161488473912297567751734375, -0.001063298592105764610370571222784,
          0.0047257715335942075767416426868, -0.01111292538377345760043121325864,
          0.01067084744190440429077799346366]
        [0, 7.45148212, 84.8689858, 10.8643335]
        [0, 19.1485648, 4.90253043]
        [0, 0.55306671]
        [0, 0, 0.00028449824] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.526616413170889192511566402, -35.506235696030525492006744905860675232,
          128.0644772415629033779350556964340649712, -108.53426230764455146586104596201537500208,
          -462.41437498587887460782059956137346736112, 916.4567324362352131540751977238539775152,
          -2.536086811024888808039667199733385876, 21.5891108980189294231019261082103230388,
          2.74510391966298007046315230698725521]
        [0, 0, 3.172351573820453267210963322691, -20.765162003774987708097611251132080505456,
          92.3266591351470737161458598224002124970448,
          -216.6464493102334165639763331243020609187568,
          209.669145893708302284841295708354896722448, -11.28029290977214883289545365906055808588,
          16.902574930936909429505702033997837625332, 2.7871382922835866181128016009305790969]
        [0, 0, 0.01097074197014263170576904529198, 0.00651090430451872703396716702645549305632,
          -0.18158658935579082063043889660506733952384, 1.4450225128055979506020261138622535211872,
          -4.2298833695142363675750202355225527105632, 4.1118995002530087342870049725462871480616,
          1.04808011907856763730519770287473012872]
        [0, 0, 0.00675876778143491015740596390926, -0.04187780051899307261492156047172241501216,
          0.18050761384247056467489320250488881536, -0.3883093825013623993941445531288455959136,
          0.2660084970993729255661225966314105257184, 0.17341358837353076309513383869391178678]
        [0, 0, 0.000161488473912297567751734375, -0.001063298592105764610370571222784,
          0.0047257715335942075767416426868, -0.01111292538377345760043121325864,
          0.01067084744190440429077799346366]
        [0, 7.45148212, 84.8689858, 10.8643335]
        [0, 19.1485648, 4.90253043]
        [0, 0.55306671]
        [0, 0, 0.00028449824] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.2025 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.225625 (-1.48888094915) hw0 (by norm_num) lgU58
    have hτ1 : w / 0.225625 ≤ 4.432133 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.48888094915) + 4.432133 * w := by linarith
    have hwa : Real.log 0.2025 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.48888094915) 4.432133 10.85747 12.24102
        0.1094132 0.01410666 (1596 / 2279) 0.530808912945 0.446411918 0.15953 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (1596 / 2279) = (3875 / 2279) by norm_num]; exact lgU61)
        (by norm_num) (by norm_num)
    have hRs : 0.446411918 + 0.15953 * ((2.08 + Real.log r + ((-2.48888094915) + 4.432133 * w)) *
        (0.1094132 + 0.01410666 * (Real.log r + 2 / 3 * ((-2.48888094915) + 4.432133 * w) -
        10.85747)) / 2) ≤ 0.448602169 + (-0.00581677598) * Real.log r + (-0.0251010127) * w +
        0.00112521774 * Real.log r ^ 2 + 0.00831185776 * w * Real.log r + 0.0147357037 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000000995741081774993976833565 + 0.000000000006949911467225 *
          Real.log r + 0.00000000004747800292187287274 * w + 0.0000000000051 * Real.log r ^ 2 +
          0.0000000000016074305 * w * Real.log r + 0.0000000000750889063057026 * w ^ 2) (by ring) ?_
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
    have hLlo : 10.32 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL60]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 10.32 2.33408375918 0.095546 2.34814747307
        (Real.log r + (-2.48888094915) + 4.432133 * w) 1.7810727 1.0738133 0.21809 1.14632
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL62 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL64]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.8118038 + 0.0371133289 * Real.log r + 0.16449121 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 7.45148212 + 19.1485648 * Real.log r + 84.8689858 * w + 0.55306671 *
        Real.log r ^ 2 + 4.90253043 * w * Real.log r + 10.8643335 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((47308577776607193514758307 /
          24000000000000000000000000000000000) + (87731947938260897 / 1800000000000000000000000) *
          Real.log r + (113946541611448084203301 / 1800000000000000000000000000000) * w +
          0.00000000036885 * Real.log r ^ 2 + 0.0000000000847245141 * w * Real.log r +
          0.00000004903416015742578765 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.25, 0.3025]` of region `R0`** (`ptLoS`; moments `mom_0_25_0_3025`). -/
private theorem tR0_lo6 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.25 0.3025
      (1 / Real.sqrt r * (0.01528797388561018 + Real.log r * 0.004365286152206944 + Real.log r ^ 2 *
          0.00003959699618342595 + Real.log r ^ 3 * 0.00001022825443796095 + Real.log r ^ 4 *
          0.0000002160495192346494) + 1 / r * (0.4397818135038636 + Real.log r * 0.2869225718429207
          + Real.log r ^ 2 * 0.0075679708301573) + 0.000001061890116819073) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.25 : ℝ) 0.3025, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.323422023724460542128873088859375, -28.581197688570966901502570763435234375,
          84.909074783710246119437320772466796875, -67.4225298230393058257503950827163046875,
          -172.4485247665662459881308467298433125, 295.09990716820853986971027784340075,
          -1.5928343220681586514024513229, 4.79248043640142721267148022949,
          0.4758525463865042447463655588]
        [0, 0, 2.888547120325212471513093004229109375, -15.323872378598311069512982989203428125,
          55.2122556043208753695204733771418515625, -105.0510678406928685906169939871238825,
          82.67275321012689998732774235591303, -4.150937623682432297466269885812,
          4.5872867459226319061895949745156, 0.590205844515746263854105742672]
        [0, 0, 0.0090762793794855125355203972259975, 0.01189923081248770554063420864662203125,
          -0.13783595832676180139100695899334925, 0.775107649078341425568657301238907,
          -1.764298911267057811175777672544, 1.36678189005798851206308377869364,
          0.2711258024509575787035699620368]
        [0, 0, 0.00632178011661821037628007793486609375, -0.03178955237000664216084366170658375,
          0.111102934228631524490443697526129, -0.19420565154160305214678974585408,
          0.10936070724556456236743013599388, 0.0548013013890032785820469270576]
        [0, 0, 0.000144824014364744710021753125, -0.00077239474327863845344935,
          0.00278062107580309843241766, -0.0052964210967678065379384, 0.0041194386308194050850632]
        [0, 11.3955967, 70.6387243, 7.13835063]
        [0, 19.469798, 3.93501569]
        [0, 0.542294337]
        [0, 0, 0.00027468] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.323422023724460542128873088859375, -28.581197688570966901502570763435234375,
          84.909074783710246119437320772466796875, -67.4225298230393058257503950827163046875,
          -172.4485247665662459881308467298433125, 295.09990716820853986971027784340075,
          -1.5928343220681586514024513229, 4.79248043640142721267148022949,
          0.4758525463865042447463655588]
        [0, 0, 2.888547120325212471513093004229109375, -15.323872378598311069512982989203428125,
          55.2122556043208753695204733771418515625, -105.0510678406928685906169939871238825,
          82.67275321012689998732774235591303, -4.150937623682432297466269885812,
          4.5872867459226319061895949745156, 0.590205844515746263854105742672]
        [0, 0, 0.0090762793794855125355203972259975, 0.01189923081248770554063420864662203125,
          -0.13783595832676180139100695899334925, 0.775107649078341425568657301238907,
          -1.764298911267057811175777672544, 1.36678189005798851206308377869364,
          0.2711258024509575787035699620368]
        [0, 0, 0.00632178011661821037628007793486609375, -0.03178955237000664216084366170658375,
          0.111102934228631524490443697526129, -0.19420565154160305214678974585408,
          0.10936070724556456236743013599388, 0.0548013013890032785820469270576]
        [0, 0, 0.000144824014364744710021753125, -0.00077239474327863845344935,
          0.00278062107580309843241766, -0.0052964210967678065379384, 0.0041194386308194050850632]
        [0, 11.3955967, 70.6387243, 7.13835063]
        [0, 19.469798, 3.93501569]
        [0, 0.542294337]
        [0, 0, 0.00027468] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.25 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.275625 (-1.28871403221) hw0 (by norm_num) lgU66
    have hτ1 : w / 0.275625 ≤ 3.628118 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.28871403221) + 3.628118 * w := by linarith
    have hwa : Real.log 0.25 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.28871403221) 3.628118 10.99726 12.36745
        0.1111127 0.01456313 (1626 / 2249) 0.544059990524 0.447906273 0.15743 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (1626 / 2249) = (3875 / 2249) by norm_num]; exact lgU69)
        (by norm_num) (by norm_num)
    have hRs : 0.447906273 + 0.15743 * ((2.08 + Real.log r + ((-2.28871403221) + 3.628118 * w)) *
        (0.1111127 + 0.01456313 * (Real.log r + 2 / 3 * ((-2.28871403221) + 3.628118 * w) -
        10.99726)) / 2) ≤ 0.449077038 + (-0.00584867536) * Real.log r + (-0.020930334) * w +
        0.00114633678 * Real.log r ^ 2 + 0.00693174184 * w * Real.log r + 0.010059671 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000058520533536441837028709627 + (5916028235539 /
          1200000000000000000000000) * Real.log r + (7600256559114542801 /
          750000000000000000000000000000) * w + 0.00000000000205 * Real.log r ^ 2 + (58576019 /
          6000000000000000000) * w * Real.log r + (583088994451121 / 7500000000000000000000000) *
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
    have hL : Real.log (2 * (w * r)) ≤ (-1.59556685) + Real.log r + 3.628118 * w := by
      rw [Real.log_mul (by norm_num) (mul_pos hw0 hr).ne', hwl]
      linarith [Real.log_two_lt_d9]
    have hlt : Real.log (w * r) ≤ Real.log r + (-2.28871403221) + 3.628118 * w := by
      rw [hwl]
      linarith
    have hLlo : 10.53 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL68]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 10.53 2.35422832522 0.093685 2.36781718881
        (Real.log r + (-2.28871403221) + 3.628118 * w) 1.7810727 1.0646249 0.21755 1.14917
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL70 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL72]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.8276894 + 0.0363003486 * Real.log r + 0.131701949 * w :=
        hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 11.3955967 + 19.469798 * Real.log r + 70.6387243 * w + 0.542294337 *
        Real.log r ^ 2 + 3.93501569 * w * Real.log r + 7.13835063 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((24777030611590338120929275957 /
          720000000000000000000000000000000000) + (349605686696579263 / 3600000000000000000000000) *
          Real.log r + (129910142403109881258517 / 1800000000000000000000000000000) * w +
          0.000000000326625 * Real.log r ^ 2 + 0.0000000016345360835 * w * Real.log r +
          0.0000000053794348930979265 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.3025, 0.36]` of region `R0`** (`ptLoS`; moments `mom_0_3025_0_36`). -/
private theorem tR0_lo7 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.3025 0.36
      (1 / Real.sqrt r * (0.02274296931359031 + Real.log r * 0.006229341478193494 + Real.log r ^ 2 *
          0.0000558732338807893 + Real.log r ^ 3 * 0.00001492301193784926 + Real.log r ^ 4 *
          0.0000003047217684099527) + 1 / r * (0.6384434647021427 + Real.log r * 0.375288572312601 +
          Real.log r ^ 2 * 0.009604172884729826) + 0.00000159213277044089) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.3025 : ℝ) 0.36, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.12100056266236105868300599770487225176,
          -23.366076052339646705208652534376661624968, 58.1285912444869578903187805295576565047812,
          -42.1515897839713623954747387969949111773654,
          -70.230898873903712559935993142593085524609, 105.696915680427178567389764123256967413071,
          -0.71391220420031653400578633294340769478, 1.223964611322726695185890937368503255898,
          0.097231704278849144918133848477696385]
        [0, 0, 2.652112601121164506091465562956088165993,
          -11.63336588930472008075414793894221330849038,
          34.65383380307657971319819733912485991122434,
          -54.5407394740438199537640817306043519763479, 35.592475514089385028572353381729457848367,
          -1.6467533306531140163509454979680602272638, 1.4063148132186811573019501453339255850292,
          0.144662529098237545698008115230904579]
        [0, 0, 0.007690883942559082026242168118764110317036,
          0.013408476267875210635315740214179963439424,
          -0.10165420600900083804208541739676489899672,
          0.43513989370823519111707824413864073627606,
          -0.79576753087089991549113582031138435475116,
          0.50373755154145757393931398748033902877012, 0.0797150723115879499423708195951260969]
        [0, 0, 0.005947731277225138585464550299264961967988,
          -0.0247593583424387613892001805274038755509, 0.07157770747822784516526151814223221261034,
          -0.10368187178516548077481179549184088398608,
          0.04885548299243880335058157288569731454044, 0.0193275814248741869332776216250062303]
        [0, 0, 0.0001313365934118966024946687749228, -0.00057889407471481727818661705679,
          0.001722329482638555001838982565854, -0.002711262462081039586818564137448,
          0.001742776607917495399492128616164]
        [0, 15.0511126, 59.7436077, 4.87488859]
        [0, 19.7527282, 3.22351973]
        [0, 0.532888047]
        [0, 0, 0.00026609056] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 7.12100056266236105868300599770487225176,
          -23.366076052339646705208652534376661624968, 58.1285912444869578903187805295576565047812,
          -42.1515897839713623954747387969949111773654,
          -70.230898873903712559935993142593085524609, 105.696915680427178567389764123256967413071,
          -0.71391220420031653400578633294340769478, 1.223964611322726695185890937368503255898,
          0.097231704278849144918133848477696385]
        [0, 0, 2.652112601121164506091465562956088165993,
          -11.63336588930472008075414793894221330849038,
          34.65383380307657971319819733912485991122434,
          -54.5407394740438199537640817306043519763479, 35.592475514089385028572353381729457848367,
          -1.6467533306531140163509454979680602272638, 1.4063148132186811573019501453339255850292,
          0.144662529098237545698008115230904579]
        [0, 0, 0.007690883942559082026242168118764110317036,
          0.013408476267875210635315740214179963439424,
          -0.10165420600900083804208541739676489899672,
          0.43513989370823519111707824413864073627606,
          -0.79576753087089991549113582031138435475116,
          0.50373755154145757393931398748033902877012, 0.0797150723115879499423708195951260969]
        [0, 0, 0.005947731277225138585464550299264961967988,
          -0.0247593583424387613892001805274038755509, 0.07157770747822784516526151814223221261034,
          -0.10368187178516548077481179549184088398608,
          0.04885548299243880335058157288569731454044, 0.0193275814248741869332776216250062303]
        [0, 0, 0.0001313365934118966024946687749228, -0.00057889407471481727818661705679,
          0.001722329482638555001838982565854, -0.002711262462081039586818564137448,
          0.001742776607917495399492128616164]
        [0, 15.0511126, 59.7436077, 4.87488859]
        [0, 19.7527282, 3.22351973]
        [0, 0.532888047]
        [0, 0, 0.00026609056] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.3025 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.330625 (-1.10677047565) hw0 (by norm_num) lgU74
    have hτ1 : w / 0.330625 ≤ 3.024575 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-2.10677047565) + 3.024575 * w := by linarith
    have hwa : Real.log 0.3025 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-2.10677047565) 3.024575 11.12383 12.48297
        0.1126976 0.01499796 (11573 / 15552) 0.556266564571 0.449307306 0.15552 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (11573 / 15552) = (27125 / 15552) by norm_num]; exact lgU77)
        (by norm_num) (by norm_num)
    have hRs : 0.449307306 + 0.15552 * ((2.08 + Real.log r + ((-2.10677047565) + 3.024575 * w)) *
        (0.1126976 + 0.01499796 * (Real.log r + 2 / 3 * ((-2.10677047565) + 3.024575 * w) -
        11.12383)) / 2) ≤ 0.449463852 + (-0.00587892811) * Real.log r + (-0.0177497824) * w +
        0.00116624137 * Real.log r ^ 2 + 0.00587897416 * w * Real.log r + 0.0071125593 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.000000000094606900124782881928896 + 0.0000000000078877337504 *
          Real.log r + 0.000000000025290295173212864 * w + 0.0000000000004 * Real.log r ^ 2 +
          0.0000000000092368 * w * Real.log r + 0.000000000003182157744 * w ^ 2) (by ring) ?_
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
    have hLlo : 10.72 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL76]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 10.72 2.37211115478 0.09206 2.38531474156
        (Real.log r + (-2.10677047565) + 3.024575 * w) 1.7810727 1.0565989 0.21708 1.15165
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL78 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL80]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.84164039 + 0.0355936422 * Real.log r + 0.107655641 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 15.0511126 + 19.7527282 * Real.log r + 59.7436077 * w + 0.532888047 *
        Real.log r ^ 2 + 3.22351973 * w * Real.log r + 4.87488859 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ (0.00000006828196933797194373680034875 + (15855648904825577
          / 180000000000000000000000) * Real.log r + (510555971452512782191 /
          7200000000000000000000000000) * w + 0.0000000005235 * Real.log r ^ 2 +
          0.000000003656680025 * w * Real.log r + 0.0000000018475764933071875 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.36, 0.4225]` of region `R0`** (`ptLoS`; moments `mom_0_36_0_4225`). -/
private theorem tR0_lo8 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.36 0.4225
      (1 / Real.sqrt r * (0.03247602583540018 + Real.log r * 0.008571549695409912 + Real.log r ^ 2 *
          0.00007647045940716523 + Real.log r ^ 3 * 0.00002095639521042847 + Real.log r ^ 4 *
          0.0000004153860881405768) + 1 / r * (0.8842897717048465 + Real.log r * 0.4767360668025204
          + Real.log r ^ 2 * 0.01188038691822892) + 0.000002293835969986407) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.36 : ℝ) 0.4225, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.92362200569659337929872049874296875, -19.36518892142111704975596760827759033105,
          40.9154658029254336332381359718060207966045,
          -26.8298452521309459249970183767973776660508,
          -30.75649028684944776683773902341687028840236,
          41.34263879538724936113312868435094242315598,
          -0.3047325942395574205462999077691892764402, 0.3510695512524216901514405411166158816504,
          0.0227729150853754845365788766189568]
        [0, 0, 2.45191656370639334230836892509116015625,
          -9.04098130532539672247328320699782537379925,
          22.63736397408481161156036391644563470150126,
          -29.9606181016344092753131442457806043174409,
          16.47661928309500436512649344630867532748761,
          -0.6981918340027890116151924051632519174728, 0.4768646441770737269002792400699169902968,
          0.0400305147967397444739260798796256]
        [0, 0, 0.006670852011402225654727432877626875, 0.01315168922011475415175205733693397753953,
          -0.07451009460313803175549189313238618458122,
          0.25424841636294988300947524479355721026354,
          -0.38307276201019943280371761166651100579405, 0.2021934036981808178707982783924713357562,
          0.0260615331057455909180743107431904]
        [0, 0, 0.00562270580070562863836895953238796875,
          -0.01969630412542947960196643745385523049648,
          0.04788234213647736303987198152240619150704, -0.0584158276915098832308447198777391121756,
          0.0233737894248491712106714370172995023792, 0.0074655433551173990879906783349864]
        [0, 0, 0.000120227146291174099836421875, -0.000445285726352959111552026636336,
          0.001113214318813650107502977977328, -0.00147250571093290216446618880892,
          0.00079533487694881080029072941744]
        [0, 18.456314, 51.2087227, 3.43888409]
        [0, 20.0034073, 2.6866282]
        [0, 0.52473207]
        [0, 0, 0.00025848384] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.92362200569659337929872049874296875, -19.36518892142111704975596760827759033105,
          40.9154658029254336332381359718060207966045,
          -26.8298452521309459249970183767973776660508,
          -30.75649028684944776683773902341687028840236,
          41.34263879538724936113312868435094242315598,
          -0.3047325942395574205462999077691892764402, 0.3510695512524216901514405411166158816504,
          0.0227729150853754845365788766189568]
        [0, 0, 2.45191656370639334230836892509116015625,
          -9.04098130532539672247328320699782537379925,
          22.63736397408481161156036391644563470150126,
          -29.9606181016344092753131442457806043174409,
          16.47661928309500436512649344630867532748761,
          -0.6981918340027890116151924051632519174728, 0.4768646441770737269002792400699169902968,
          0.0400305147967397444739260798796256]
        [0, 0, 0.006670852011402225654727432877626875, 0.01315168922011475415175205733693397753953,
          -0.07451009460313803175549189313238618458122,
          0.25424841636294988300947524479355721026354,
          -0.38307276201019943280371761166651100579405, 0.2021934036981808178707982783924713357562,
          0.0260615331057455909180743107431904]
        [0, 0, 0.00562270580070562863836895953238796875,
          -0.01969630412542947960196643745385523049648,
          0.04788234213647736303987198152240619150704, -0.0584158276915098832308447198777391121756,
          0.0233737894248491712106714370172995023792, 0.0074655433551173990879906783349864]
        [0, 0, 0.000120227146291174099836421875, -0.000445285726352959111552026636336,
          0.001113214318813650107502977977328, -0.00147250571093290216446618880892,
          0.00079533487694881080029072941744]
        [0, 18.456314, 51.2087227, 3.43888409]
        [0, 20.0034073, 2.6866282]
        [0, 0.52473207]
        [0, 0, 0.00025848384] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.36 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.390625 (-0.940007257657) hw0 (by norm_num) lgU82
    have hτ1 : w / 0.390625 ≤ 2.56 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.940007257657) + 2.56 * w := by linarith
    have hwa : Real.log 0.36 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.940007257657) 2.56 11.23945 12.58932 0.1141854
        0.01541416 (379 / 496) 0.567647960522 0.45063451 0.15376 hy0 hr hw0 (by linarith) hτ
        (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1]) (by linarith [hw.2])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (379 / 496) = (875 / 496) by norm_num]; exact lgU85) (by norm_num)
        (by norm_num)
    have hRs : 0.45063451 + 0.15376 * ((2.08 + Real.log r + ((-1.940007257657) + 2.56 * w)) *
        (0.1141854 + 0.01541416 * (Real.log r + 2 / 3 * ((-1.940007257657) + 2.56 * w) - 11.23945))
        / 2) ≤ 0.449784294 + (-0.00590739243) * Real.log r + (-0.0152644901) * w + 0.00118504063 *
        Real.log r ^ 2 + 0.00505617332 * w * Real.log r + 0.00517752148 * w ^ 2 := by
      refine le_of_sub_eq _ _ ((106740958347717767534461547 / 234375000000000000000000000000000000)
          + (669108255229 / 93750000000000000000000) * Real.log r + 0.000000000052708358258229248 *
          w + 0.0000000000092 * Real.log r ^ 2 + (43 / 9375000000000) * w * Real.log r + (5879 /
          1171875000000000) * w ^ 2) (by ring) ?_
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
    have hLlo : 10.89 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL84]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 10.89 2.38784493605 0.090651 2.40073831125
        (Real.log r + (-1.940007257657) + 2.56 * w) 1.7810727 1.0496369 0.21666 1.15389 0.6931471808
        (mul_pos hw0 hr) (by norm_num) hLlo lgL86 (by norm_num) (by norm_num) (by norm_num)
        (by linarith [lgL88]) hlt (by norm_num) (by norm_num) (by norm_num) Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.85396782 + 0.0349810616 * Real.log r + 0.0895515177 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 18.456314 + 20.0034073 * Real.log r + 51.2087227 * w + 0.52473207 *
        Real.log r ^ 2 + 2.6866282 * w * Real.log r + 3.43888409 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((32254253973772892519792028982159 /
          360000000000000000000000000000000000000) + (5873673081744832313 /
          180000000000000000000000000) * Real.log r + (6717423081744832313 /
          70312500000000000000000000) * w + 0.000000000684975 * Real.log r ^ 2 + 0.000000005107072 *
          w * Real.log r + 0.00000000053705216 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.4225, 0.49]` of region `R0`** (`ptLoS`; moments `mom_0_4225_0_49`). -/
private theorem tR0_lo9 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.4225 0.49
      (1 / Real.sqrt r * (0.04472895652415251 + Real.log r * 0.011418709170961 + Real.log r ^ 2 *
          0.0001016320529865125 + Real.log r ^ 3 * 0.00002845335420885647 + Real.log r ^ 4 *
          0.0000005488778936151946) + 1 / r * (1.177641680725696 + Real.log r * 0.5899288299100909 +
          Real.log r ^ 2 * 0.01434834547642983) + 0.000003189701227287133) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.4225 : ℝ) 0.49, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.7335189029233464140145777131326340488,
          -16.243458472027987406848677304207188066144, 29.5028257986618923722472516244535323324235,
          -17.44157090227253536624006285011004125592142,
          -14.3199798486482456646778753498948489297394,
          17.41763720681917068913144762664852077899154,
          -0.13241290287721393923851602991745497322826,
          0.11110012807210505269984594008861864425436, 0.005979989168917737317194331910736720368]
        [0, 0, 2.280353950322398121038332822969920282668,
          -7.16707259284745828680586222794730945500058,
          15.29522172393430083782862663676392344604492,
          -17.26057169269622173003914172622860358439264,
          8.10928498371183003155290066188881379039402, -0.3147202350382841007356750156346338724258,
          0.17611657706999433188480341572182200132384, 0.012260843079763635797254520304278616192]
        [0, 0, 0.00587144902480985812059190640279090177364,
          0.01229376688046147692346296067876804009565,
          -0.05513114259786447662595819816195045849118,
          0.15429345033056982720244654908960010076372,
          -0.19511427005865306195251430651247724829557, 0.0872489080834883106815917794963020425757,
          0.00931057509289546088397219755559285396]
        [0, 0, 0.00533883212139782475731694344712140619621,
          -0.0159562417666796337922151709860591277123, 0.03307460875777210956981256843988246482248,
          -0.03445349599934960617958129085757830929037,
          0.01185692102632195734973654397750692598082, 0.003110895029429973770760632786289750216]
        [0, 0, 0.000110858937632595654870897509421, -0.00034985068827036896519436936003,
          0.000745244075648482919656127628648, -0.000839948236850609629863999062037,
          0.000386563950150484455292776765282]
        [0, 21.6473592, 44.4015668, 2.4917976]
        [0, 20.2304582, 2.27064992]
        [0, 0.517282288]
        [0, 0, 0.0002516784] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.7335189029233464140145777131326340488,
          -16.243458472027987406848677304207188066144, 29.5028257986618923722472516244535323324235,
          -17.44157090227253536624006285011004125592142,
          -14.3199798486482456646778753498948489297394,
          17.41763720681917068913144762664852077899154,
          -0.13241290287721393923851602991745497322826,
          0.11110012807210505269984594008861864425436, 0.005979989168917737317194331910736720368]
        [0, 0, 2.280353950322398121038332822969920282668,
          -7.16707259284745828680586222794730945500058,
          15.29522172393430083782862663676392344604492,
          -17.26057169269622173003914172622860358439264,
          8.10928498371183003155290066188881379039402, -0.3147202350382841007356750156346338724258,
          0.17611657706999433188480341572182200132384, 0.012260843079763635797254520304278616192]
        [0, 0, 0.00587144902480985812059190640279090177364,
          0.01229376688046147692346296067876804009565,
          -0.05513114259786447662595819816195045849118,
          0.15429345033056982720244654908960010076372,
          -0.19511427005865306195251430651247724829557, 0.0872489080834883106815917794963020425757,
          0.00931057509289546088397219755559285396]
        [0, 0, 0.00533883212139782475731694344712140619621,
          -0.0159562417666796337922151709860591277123, 0.03307460875777210956981256843988246482248,
          -0.03445349599934960617958129085757830929037,
          0.01185692102632195734973654397750692598082, 0.003110895029429973770760632786289750216]
        [0, 0, 0.000110858937632595654870897509421, -0.00034985068827036896519436936003,
          0.000745244075648482919656127628648, -0.000839948236850609629863999062037,
          0.000386563950150484455292776765282]
        [0, 21.6473592, 44.4015668, 2.4917976]
        [0, 20.2304582, 2.27064992]
        [0, 0.517282288]
        [0, 0, 0.0002516784] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.4225 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.455625 (-0.786085175881) hw0 (by norm_num) lgU90
    have hτ1 : w / 0.455625 ≤ 2.194788 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.786085175881) + 2.194788 * w := by linarith
    have hwa : Real.log 0.4225 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.786085175881) 2.194788 11.34586 12.68783
        0.1155899 0.01581403 (11911 / 15214) 0.578239755806 0.451887534 0.15214 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (11911 / 15214) = (27125 / 15214) by norm_num]; exact lgU93)
        (by norm_num) (by norm_num)
    have hRs : 0.451887534 + 0.15214 * ((2.08 + Real.log r + ((-1.786085175881) + 2.194788 * w)) *
        (0.1155899 + 0.01581403 * (Real.log r + 2 / 3 * ((-1.786085175881) + 2.194788 * w) -
        11.34586)) / 2) ≤ 0.450039324 + (-0.00593467932) * Real.log r + (-0.0132840345) * w +
        0.00120297327 * Real.log r ^ 2 + 0.00440045214 * w * Real.log r + 0.00386322382 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ ((2783207678032854371928802019 /
          15000000000000000000000000000000000000) + (8351624114101 / 6000000000000000000000000) *
          Real.log r + 0.0000000000813995546353375340784 * w + 0.0000000000079 * Real.log r ^ 2 +
          0.000000000006703442 * w * Real.log r + 0.0000000000053065256241184 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.05 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL92]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.05 2.40243042704 0.089364 2.41503736336
        (Real.log r + (-1.786085175881) + 2.194788 * w) 1.7810727 1.0432644 0.21627 1.15597
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL94 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL96]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.86517746 + 0.0344223509 * Real.log r + 0.0755497627 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 21.6473592 + 20.2304582 * Real.log r + 44.4015668 * w + 0.517282288 *
        Real.log r ^ 2 + 2.27064992 * w * Real.log r + 2.4917976 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((8874015925294777851616267590641 /
          90000000000000000000000000000000000000) + (3276716612340796439 /
          45000000000000000000000000) * Real.log r + (254827191680519327896661 /
          3750000000000000000000000000000) * w + 0.0000000005209 * Real.log r ^ 2 +
          0.0000000056566421384 * w * Real.log r + 0.0000000078990851428273296 *
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
/-- **Piece `[0.49, 0.5625]` of region `R0`** (`ptLoS`; moments `mom_0_49_0_5625`). -/
private theorem tR0_lo10 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.49 0.5625
      (1 / Real.sqrt r * (0.05962484008976587 + Real.log r * 0.01476852222704313 + Real.log r ^ 2 *
          0.0001315225503898224 + Real.log r ^ 3 * 0.00003746035885971802 + Real.log r ^ 4 *
          0.0000007049722264638859) + 1 / r * (1.515508570528592 + Real.log r * 0.7124794570385346 +
          Real.log r ^ 2 * 0.0169484020421105) + 0.000004294777446215978) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.49 : ℝ) 0.5625, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.55169855981426144867406030226875, -13.77095849681198457234361619138049007236,
          21.7285201546218117770102011022598857110964,
          -11.58579031425332111245322331527301955390928,
          -7.022785750349082529592983874649796764387492,
          7.81750661606612974029463451575870359010956,
          -0.05936285221218635773414918785112320527788,
          0.038231645959291400374060410971217204642624, 0.001731644846689793335977600993251564928]
        [0, 0, 2.13156371796058695690323959504057734375,
          -5.77833271386190535403496561283458940980926,
          10.635596969100473289880512403541777375517548,
          -10.355182621639496004681930706629641872629233,
          4.20467580036701045700343900307591565161007,
          -0.149568402487536841162276624509268068964366,
          0.069950279900520400933913426690575104031696, 0.004095879111785810823112358623741430112]
        [0, 0, 0.0052463763103187755818404128966848046875,
          0.011188865720417652053764895461038318982773,
          -0.041209145825533477805687535566504437760849,
          0.09672287074255233211843995017053818742568,
          -0.104267460645825052932880636656493916862586,
          0.040038688847791666949690965260940928257648, 0.003588158932976396150145608406675226656]
        [0, 0, 0.0050877692070021374824974855927308203125,
          -0.013126681040232403627732654782778764838953,
          0.02347562814526817189305671607866063995839,
          -0.02112516389788996113474104143186713101211,
          0.006320821750079343481086127144644092747216, 0.001383085056440931731963212372678323552]
        [0, 0, 0.00010286794864037067918802734375, -0.0002799127853980602189797105313795,
          0.000514125526230819506438439732585, -0.000499636077692513700311500429665,
          0.000198268285067996318714832418224]
        [0, 24.649788, 38.8813867, 1.84774748]
        [0, 20.4370185, 1.94244354]
        [0, 0.510498182]
        [0, 0, 0.00024553728] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.55169855981426144867406030226875, -13.77095849681198457234361619138049007236,
          21.7285201546218117770102011022598857110964,
          -11.58579031425332111245322331527301955390928,
          -7.022785750349082529592983874649796764387492,
          7.81750661606612974029463451575870359010956,
          -0.05936285221218635773414918785112320527788,
          0.038231645959291400374060410971217204642624, 0.001731644846689793335977600993251564928]
        [0, 0, 2.13156371796058695690323959504057734375,
          -5.77833271386190535403496561283458940980926,
          10.635596969100473289880512403541777375517548,
          -10.355182621639496004681930706629641872629233,
          4.20467580036701045700343900307591565161007,
          -0.149568402487536841162276624509268068964366,
          0.069950279900520400933913426690575104031696, 0.004095879111785810823112358623741430112]
        [0, 0, 0.0052463763103187755818404128966848046875,
          0.011188865720417652053764895461038318982773,
          -0.041209145825533477805687535566504437760849,
          0.09672287074255233211843995017053818742568,
          -0.104267460645825052932880636656493916862586,
          0.040038688847791666949690965260940928257648, 0.003588158932976396150145608406675226656]
        [0, 0, 0.0050877692070021374824974855927308203125,
          -0.013126681040232403627732654782778764838953,
          0.02347562814526817189305671607866063995839,
          -0.02112516389788996113474104143186713101211,
          0.006320821750079343481086127144644092747216, 0.001383085056440931731963212372678323552]
        [0, 0, 0.00010286794864037067918802734375, -0.0002799127853980602189797105313795,
          0.000514125526230819506438439732585, -0.000499636077692513700311500429665,
          0.000198268285067996318714832418224]
        [0, 24.649788, 38.8813867, 1.84774748]
        [0, 20.4370185, 1.94244354]
        [0, 0.510498182]
        [0, 0, 0.00024553728] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.49 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.525625 (-0.643167247404) hw0 (by norm_num) lgU98
    have hτ1 : w / 0.525625 ≤ 1.902498 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.643167247404) + 1.902498 * w := by linarith
    have hwa : Real.log 0.49 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.643167247404) 1.902498 11.44442 12.77958
        0.1169219 0.01619964 (12062 / 15063) 0.588214406498 0.453083158 0.15063 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12062 / 15063) = (27125 / 15063) by norm_num]; exact lgU101)
        (by norm_num) (by norm_num)
    have hRs : 0.453083158 + 0.15063 * ((2.08 + Real.log r + ((-1.643167247404) + 1.902498 * w)) *
        (0.1169219 + 0.01619964 * (Real.log r + 2 / 3 * ((-1.643167247404) + 1.902498 * w) -
        11.44442)) / 2) ≤ 0.450246535 + (-0.00596064469) * Real.log r + (-0.0116781054) * w +
        0.00122007589 * Real.log r ^ 2 + 0.00386865323 * w * Real.log r + 0.00294404201 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000001921926415488165653873407296 + 0.000000000005842300080644
          * Real.log r + 0.0000000000998434511711512389696 * w + 0.0000000000034 * Real.log r ^ 2 +
          0.000000000006492122 * w * Real.log r + 0.0000000000018330836483024 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.2 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL100]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.2 2.41591377733 0.088192 2.42823902402
        (Real.log r + (-1.643167247404) + 1.902498 * w) 1.7810727 1.0374419 0.21592 1.15784
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL102 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL104]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.87537168 + 0.0339159285 * Real.log r + 0.064524986 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 24.649788 + 20.4370185 * Real.log r + 38.8813867 * w + 0.510498182 *
        Real.log r ^ 2 + 1.94244354 * w * Real.log r + 1.84774748 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((30595307930453341765779030023 /
          351562500000000000000000000000000000) + (100581800190350029 / 1406250000000000000000000) *
          Real.log r + (3249107074756758245407 / 234375000000000000000000000000) * w +
          0.0000000004352 * Real.log r ^ 2 + 0.0000000011386622592 * w * Real.log r +
          0.0000000061016913354017408 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.5625, 0.64]` of region `R0`** (`ptLoS`; moments `mom_0_5625_0_64`). -/
private theorem tR0_lo11 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.5625 0.64
      (1 / Real.sqrt r * (0.07711857794119482 + Real.log r * 0.01858166860882256 + Real.log r ^ 2 *
          0.0001659653375723145 + Real.log r ^ 3 * 0.00004792753338335619 + Real.log r ^ 4 *
          0.0000008817412229570499) + 1 / r * (1.891121086064416 + Real.log r * 0.8409244852281294 +
          Real.log r ^ 2 * 0.01960102369965845) + 0.000005612282985974552) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.5625 : ℝ) 0.64, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.37851947268577557146928662750175, -11.786134170998504006246162874744789880644,
          16.30436637425041954617746848605373416679914,
          -7.857403713897560545495604158578353893261392,
          -3.6012219145344518192177402561852532093400576,
          3.70570532619267860043626529481202846985254,
          -0.027591036244831129655927249901569272487288,
          0.0141444322905627119742241601546612486754752, 0.0005456665461143618969082862183303458752]
        [0, 0, 2.00123491294817239482767033544854109375,
          -4.72708369317185925273713514314307646620531,
          7.5810586720793199290903691954705802743487956,
          -6.4333575636169393667545388328275157417709464,
          2.280367021389334584599045311161242168152342,
          -0.0744815527664528870026804501311333770604092,
          0.0295849949760488453572645104264276758126128, 0.0014748337952969538044809517773885454128]
        [0, 0, 0.004750938307697601100194816220105546875,
          0.010045645572231593357546647382591020855065,
          -0.0311571806944463313059171294448318980060708,
          0.06240246573475061072945989761280756555978,
          -0.058092056983654799609107366846423196643881,
          0.0193769596863320560598604935520351205495216, 0.0014763695135572711088359172294719797216]
        [0, 0, 0.0048640121475011825278123310833678125,
          -0.01094359832369444205879215436283290039498, 0.017058388221620957974431614157774652913,
          -0.0133945658367682710510935672134288502756, 0.00351719813203403512555994971307420045546,
          0.00065027900561707183557323480567265046]
        [0, 0, 0.0000959763338264881883184375, -0.00022749945773158365509202799806,
          0.000363999134359529109160942871, -0.0003081474132570137107133134332,
          0.00010652009393739251850141962462]
        [0, 27.4847795, 34.3406836, 1.39798117]
        [0, 20.6258652, 1.67932424]
        [0, 0.504321867]
        [0, 0, 0.00023995488] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.37851947268577557146928662750175, -11.786134170998504006246162874744789880644,
          16.30436637425041954617746848605373416679914,
          -7.857403713897560545495604158578353893261392,
          -3.6012219145344518192177402561852532093400576,
          3.70570532619267860043626529481202846985254,
          -0.027591036244831129655927249901569272487288,
          0.0141444322905627119742241601546612486754752, 0.0005456665461143618969082862183303458752]
        [0, 0, 2.00123491294817239482767033544854109375,
          -4.72708369317185925273713514314307646620531,
          7.5810586720793199290903691954705802743487956,
          -6.4333575636169393667545388328275157417709464,
          2.280367021389334584599045311161242168152342,
          -0.0744815527664528870026804501311333770604092,
          0.0295849949760488453572645104264276758126128, 0.0014748337952969538044809517773885454128]
        [0, 0, 0.004750938307697601100194816220105546875,
          0.010045645572231593357546647382591020855065,
          -0.0311571806944463313059171294448318980060708,
          0.06240246573475061072945989761280756555978,
          -0.058092056983654799609107366846423196643881,
          0.0193769596863320560598604935520351205495216, 0.0014763695135572711088359172294719797216]
        [0, 0, 0.0048640121475011825278123310833678125,
          -0.01094359832369444205879215436283290039498, 0.017058388221620957974431614157774652913,
          -0.0133945658367682710510935672134288502756, 0.00351719813203403512555994971307420045546,
          0.00065027900561707183557323480567265046]
        [0, 0, 0.0000959763338264881883184375, -0.00022749945773158365509202799806,
          0.000363999134359529109160942871, -0.0003081474132570137107133134332,
          0.00010652009393739251850141962462]
        [0, 27.4847795, 34.3406836, 1.39798117]
        [0, 20.6258652, 1.67932424]
        [0, 0.504321867]
        [0, 0, 0.00023995488] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.5625 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.600625 (-0.509784498458) hw0 (by norm_num) lgU106
    have hτ1 : w / 0.600625 ≤ 1.664933 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.509784498458) + 1.664933 * w := by linarith
    have hwa : Real.log 0.5625 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.509784498458) 1.664933 11.53621 12.86544
        0.1181904 0.01657249 (12203 / 14922) 0.59761917858 0.454224203 0.14922 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12203 / 14922) = (27125 / 14922) by norm_num]; exact lgU109)
        (by norm_num) (by norm_num)
    have hRs : 0.454224203 + 0.14922 * ((2.08 + Real.log r + ((-1.509784498458) + 1.664933 * w)) *
        (0.1181904 + 0.01657249 * (Real.log r + 2 / 3 * ((-1.509784498458) + 1.664933 * w) -
        11.53621)) / 2) ≤ 0.450409136 + (-0.00598551461) * Real.log r + (-0.0103567713) * w +
        0.00123647348 * Real.log r ^ 2 + 0.00343107584 * w * Real.log r + 0.00228500456 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000002767862655481899548494112136 + 0.000000000007238393909227
          * Real.log r + 0.0000000000333916626379922294328 * w + 0.0000000000011 * Real.log r ^ 2 +
          0.0000000000089243105 * w * Real.log r + 0.0000000000093358636214786 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.34 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL108]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.34 2.42833629725 0.087125 2.44041141088
        (Real.log r + (-1.509784498458) + 1.664933 * w) 1.7810727 1.0321347 0.21559 1.15961
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL110 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL112]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.88471029 + 0.033454385 * Real.log r + 0.0556993096 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 27.4847795 + 20.6258652 * Real.log r + 34.3406836 * w + 0.504321867 *
        Real.log r ^ 2 + 1.67932424 * w * Real.log r + 1.39798117 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((47185619135029005253153562957 /
          720000000000000000000000000000000000) + (41053966064544767 / 720000000000000000000000) *
          Real.log r + (50329350881740712555611 / 720000000000000000000000000000) * w +
          0.000000000290625 * Real.log r ^ 2 + 0.00000000298792030625 * w * Real.log r +
          0.000000000049383559622865625 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.64, 0.7225]` of region `R0`** (`ptLoS`; moments `mom_0_64_0_7225`). -/
private theorem tR0_lo12 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.64 0.7225
      (1 / Real.sqrt r * (0.09694736105018131 + Real.log r * 0.02277439044115921 + Real.log r ^ 2 *
          0.0002044481651419343 + Real.log r ^ 3 * 0.0000596742256929159 + Real.log r ^ 4 *
          0.000001075290588127951) + 1 / r * (2.293495862106448 + Real.log r * 0.9707097637721221 +
          Real.log r ^ 2 * 0.02220855463945825) + 0.000007129312411285399) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.64 : ℝ) 0.7225, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.21389200862363378100904435685006147904,
          -10.17328443007414895208612778933661962148272,
          12.4385147770638166262738935905322580190142464,
          -5.433471900846439090561635409103299982882992,
          -1.919439000936648109555800366449233267271736,
          1.8422566968400093941942594400334630098161616,
          -0.0132888169343892209946185442181480473332608,
          0.0055738763573094770524610704266974367672, 0.0001851193220681353801697549896961988]
        [0, 0, 1.886086204119893729822142552810654380744,
          -3.916524612542249970869922801498188522060792,
          5.5217058092245128356843279144140256254174736,
          -4.120368750889241810366320517116972301524628,
          1.286094815930696972168999758698042781442158,
          -0.0386446051528334196682481908852072187048576,
          0.0132166811091856078533352000895111146111408, 0.0005669857093541180771004263886036747624]
        [0, 0, 0.0043592969810340544646801849018903623052,
          0.0089446257987108012046021562039635932627024,
          -0.023812658145925630909572072467805219138672,
          0.041286230738583266440268601013181741696504,
          -0.0335623936705771656941697079167995821041644,
          0.0098215131951742396345623272028874621066072, 0.0006431743410780376358997249894441116316]
        [0, 0, 0.0046627753647289013391076077784965792182,
          -0.009229384771653430047561220249409957471, 0.0126506193921483834194687189178197472345,
          -0.00874393462758743212390336512548324792795, 0.0020314053763321129206182307386693982171,
          0.00032102435654487986910509219686183755]
        [0, 0, 0.00008997809743090583260634770295, -0.00018745436916022010565747064475,
          0.000263607707179997449887291047625, -0.0001961366864615751506220364848875,
          0.000059590139415031745270711380725]
        [0, 30.1696943, 30.5589078, 1.07655158]
        [0, 20.7991542, 1.46545567]
        [0, 0.498712824]
        [0, 0, 0.000234848] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.21389200862363378100904435685006147904,
          -10.17328443007414895208612778933661962148272,
          12.4385147770638166262738935905322580190142464,
          -5.433471900846439090561635409103299982882992,
          -1.919439000936648109555800366449233267271736,
          1.8422566968400093941942594400334630098161616,
          -0.0132888169343892209946185442181480473332608,
          0.0055738763573094770524610704266974367672, 0.0001851193220681353801697549896961988]
        [0, 0, 1.886086204119893729822142552810654380744,
          -3.916524612542249970869922801498188522060792,
          5.5217058092245128356843279144140256254174736,
          -4.120368750889241810366320517116972301524628,
          1.286094815930696972168999758698042781442158,
          -0.0386446051528334196682481908852072187048576,
          0.0132166811091856078533352000895111146111408, 0.0005669857093541180771004263886036747624]
        [0, 0, 0.0043592969810340544646801849018903623052,
          0.0089446257987108012046021562039635932627024,
          -0.023812658145925630909572072467805219138672,
          0.041286230738583266440268601013181741696504,
          -0.0335623936705771656941697079167995821041644,
          0.0098215131951742396345623272028874621066072, 0.0006431743410780376358997249894441116316]
        [0, 0, 0.0046627753647289013391076077784965792182,
          -0.009229384771653430047561220249409957471, 0.0126506193921483834194687189178197472345,
          -0.00874393462758743212390336512548324792795, 0.0020314053763321129206182307386693982171,
          0.00032102435654487986910509219686183755]
        [0, 0, 0.00008997809743090583260634770295, -0.00018745436916022010565747064475,
          0.000263607707179997449887291047625, -0.0001961366864615751506220364848875,
          0.000059590139415031745270711380725]
        [0, 30.1696943, 30.5589078, 1.07655158]
        [0, 20.7991542, 1.46545567]
        [0, 0.498712824]
        [0, 0, 0.000234848] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.64 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.680625 (-0.384743784828) hw0 (by norm_num) lgU114
    have hτ1 : w / 0.680625 ≤ 1.469238 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.384743784828) + 1.469238 * w := by linarith
    have hwa : Real.log 0.64 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.384743784828) 1.469238 11.6221 12.94611
        0.1194025 0.016934 (12336 / 14789) 0.606572151141 0.455322696 0.14789 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12336 / 14789) = (27125 / 14789) by norm_num]; exact lgU117)
        (by norm_num) (by norm_num)
    have hRs : 0.455322696 + 0.14789 * ((2.08 + Real.log r + ((-1.384743784828) + 1.469238 * w)) *
        (0.1194025 + 0.016934 * (Real.log r + 2 / 3 * ((-1.384743784828) + 1.469238 * w) - 11.6221))
        / 2) ≤ 0.450539496 + (-0.0060091779) * Real.log r + (-0.00925528007) * w + 0.00125218463 *
        Real.log r ^ 2 + 0.00306626207 * w * Real.log r + 0.0018020275 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.00000000079932827863849829071007072 + (27586219841 /
          15000000000000000000000) * Real.log r + 0.00000000000430869646636006176 * w +
          0.0000000000009801 * w * Real.log r + 0.00000000000009493606552 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.47 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL116]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.47 2.4397349301 0.086156 2.45159567346
        (Real.log r + (-1.384743784828) + 1.469238 * w) 1.7810727 1.0273125 0.21528 1.16128
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL118 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL120]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.89327955 + 0.0330347375 * Real.log r + 0.0485358916 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 30.1696943 + 20.7991542 * Real.log r + 30.5589078 * w + 0.498712824 *
        Real.log r ^ 2 + 1.46545567 * w * Real.log r + 1.07655158 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((102142736446886605935103059517 /
          1875000000000000000000000000000000000) + (26499251671815407 / 11250000000000000000000000)
          * Real.log r + (159302201254632454158311 / 1875000000000000000000000000000) * w +
          0.0000000004911 * Real.log r ^ 2 + 0.0000000072268615636 * w * Real.log r +
          0.0000000064692598149902684 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.7225, 0.81]` of region `R0`** (`ptLoS`; moments `mom_0_7225_0_81`). -/
private theorem tR0_lo13 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.7225 0.81
      (1 / Real.sqrt r * (0.1185907643779876 + Real.log r * 0.02721246947694839 + Real.log r ^ 2 *
          0.0002460367016167813 + Real.log r ^ 3 * 0.00007237693986590826 + Real.log r ^ 4 *
          0.000001279778412524929) + 1 / r * (2.707364708802738 + Real.log r * 1.096297518278699 +
          Real.log r ^ 2 * 0.02465759052333001) + 0.000008813016829057493) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.7225 : ℝ) 0.81, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.057535777858941440804591811338444841, -8.8483778451466544566966622644605704075409,
          9.6307227709985627460739581018524984853834729,
          -3.8258486628169834307623635329086944013038073,
          -1.0579892522157923818962788121578049169363387,
          0.9549746341299096082712631228585850309328189,
          -0.0066211026925183128239937801000888124128517,
          0.002321923669939765187223084325308876226416, 0.000067033933711796502915091904732663844]
        [0, 0, 1.7834948250751094051030154192733895135391,
          -3.2812525513207398229559376798546746181630177,
          4.0986219438024236565332996334458511390623587,
          -2.7103853160148533893631581007703633241128735,
          0.7506778767774804978297666172549634086895749,
          -0.0207942790717703668941754487737985355445641,
          0.0061955513113008115714894281800767587856086, 0.0002309527523926168615565563035494944674]
        [0, 0, 0.0040514813358055179587685394483855168319844,
          0.0079238001047545793984414637502702613455947,
          -0.0183845349069750936462666286306069721167907,
          0.0279309386638352231304590506201206303456079,
          -0.0200203159492340195382290535752384397869137,
          0.0051847222444294182759399156605327626714685, 0.0002947052109774025009874374233286266915]
        [0, 0, 0.0044806705137637508810605120268005269606012,
          -0.0078630388816412863796275676573361303913884,
          0.0095514098166747137641376296653168461644844,
          -0.0058559403013840637496710083826690038116788,
          0.0012122250955211762088894785340924122252084, 0.0001654646269457955183713597861290873356]
        [0, 0, 0.0000847312419023229827055356258796, -0.0001563667667664008007074606604972,
          0.0001947821320242785784761415542652, -0.0001283784027984469474735877021604,
          0.0000345501277413980968689685177572]
        [0, 32.7191787, 27.374671, 0.842112607]
        [0, 20.9587237, 1.28948439]
        [0, 0.493630533]
        [0, 0, 0.00023014976] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 6.057535777858941440804591811338444841, -8.8483778451466544566966622644605704075409,
          9.6307227709985627460739581018524984853834729,
          -3.8258486628169834307623635329086944013038073,
          -1.0579892522157923818962788121578049169363387,
          0.9549746341299096082712631228585850309328189,
          -0.0066211026925183128239937801000888124128517,
          0.002321923669939765187223084325308876226416, 0.000067033933711796502915091904732663844]
        [0, 0, 1.7834948250751094051030154192733895135391,
          -3.2812525513207398229559376798546746181630177,
          4.0986219438024236565332996334458511390623587,
          -2.7103853160148533893631581007703633241128735,
          0.7506778767774804978297666172549634086895749,
          -0.0207942790717703668941754487737985355445641,
          0.0061955513113008115714894281800767587856086, 0.0002309527523926168615565563035494944674]
        [0, 0, 0.0040514813358055179587685394483855168319844,
          0.0079238001047545793984414637502702613455947,
          -0.0183845349069750936462666286306069721167907,
          0.0279309386638352231304590506201206303456079,
          -0.0200203159492340195382290535752384397869137,
          0.0051847222444294182759399156605327626714685, 0.0002947052109774025009874374233286266915]
        [0, 0, 0.0044806705137637508810605120268005269606012,
          -0.0078630388816412863796275676573361303913884,
          0.0095514098166747137641376296653168461644844,
          -0.0058559403013840637496710083826690038116788,
          0.0012122250955211762088894785340924122252084, 0.0001654646269457955183713597861290873356]
        [0, 0, 0.0000847312419023229827055356258796, -0.0001563667667664008007074606604972,
          0.0001947821320242785784761415542652, -0.0001283784027984469474735877021604,
          0.0000345501277413980968689685177572]
        [0, 32.7191787, 27.374671, 0.842112607]
        [0, 20.9587237, 1.28948439]
        [0, 0.493630533]
        [0, 0, 0.00023014976] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.7225 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.765625 (-0.267062784469) hw0 (by norm_num) lgU122
    have hτ1 : w / 0.765625 ≤ 1.306123 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.267062784469) + 1.306123 * w := by linarith
    have hwa : Real.log 0.7225 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.267062784469) 1.306123 11.70279 13.02219
        0.1205641 0.01728523 (12461 / 14664) 0.615060301655 0.456375107 0.14664 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (12461 / 14664) = (27125 / 14664) by norm_num]; exact lgU125)
        (by norm_num) (by norm_num)
    have hRs : 0.456375107 + 0.14664 * ((2.08 + Real.log r + ((-1.267062784469) + 1.306123 * w)) *
        (0.1205641 + 0.01728523 * (Real.log r + 2 / 3 * ((-1.267062784469) + 1.306123 * w) -
        11.70279)) / 2) ≤ 0.45063386 + (-0.00603207241) * Real.log r + (-0.00832718531) * w +
        0.00126735307 * Real.log r ^ 2 + 0.00275886498 * w * Real.log r + 0.0014413668 * w ^ 2 := by
      refine le_of_sub_eq _ _ (0.0000000008608024589721153524724308536 + 0.000000000000996666748714
          * Real.log r + 0.0000000000059610521061868606576 * w + 0.0000000000064 * Real.log r ^ 2 +
          0.000000000004185962 * w * Real.log r + 0.0000000000004779364981304 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.59 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL124]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.59 2.45014265631 0.085278 2.46183877198
        (Real.log r + (-1.267062784469) + 1.306123 * w) 1.7810727 1.0229486 0.21501 1.16274
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL126 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL128]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.9011145 + 0.0326570772 * Real.log r + 0.0426541597 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 32.7191787 + 20.9587237 * Real.log r + 27.374671 * w + 0.493630533 *
        Real.log r ^ 2 + 1.28948439 * w * Real.log r + 0.842112607 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((2584664674350344977375679128139 /
          180000000000000000000000000000000000000) + (8362963671811707169 /
          90000000000000000000000000) * Real.log r + (4153700199917722402695787 /
          90000000000000000000000000000000) * w + 0.00000000044055 * Real.log r ^ 2 +
          0.0000000058437069753 * w * Real.log r + 0.00000000085631504284988095 *
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
/-- **Piece `[0.81, 0.9025]` of region `R0`** (`ptLoS`; moments `mom_0_81_0_9025`). -/
private theorem tR0_lo14 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.81 0.9025
      (1 / Real.sqrt r * (0.141252592052471 + Real.log r * 0.03171298179310869 + Real.log r ^ 2 *
          0.0002892664314066199 + Real.log r ^ 3 * 0.0000855559794231026 + Real.log r ^ 4 *
          0.000001486960454110368) + 1 / r * (3.113508687663757 + Real.log r * 1.211393197596216 +
          Real.log r ^ 2 * 0.02682512039630188) + 0.00001060807226978646) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.81 : ℝ) 0.9025, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.9090504168228309812822719432158203125, -7.749127575659766231151373094566746066125,
          7.5563353535250070616784505583099451652409,
          -2.739071179995943696517899855836384862524828,
          -0.6006215089312894901806193920639514834640268,
          0.5137325733431894713571534631089359766121584,
          -0.00340637148005510385576020176487914539225562,
          0.0010160991302393886711189369423704913976675, 0.0000257193354309938058589368845137650825]
        [0, 0, 1.69149800271542706122274960160320078125,
          -2.7762925372514533209881039767091594787196,
          3.093794946151682039351709308290135358918484,
          -1.8255957770558352573366598894665412535642776,
          0.4517005437097654651144002077989629581375596,
          -0.01156082102953580621323518766022468395654644,
          0.00303096473735704346252338655469749341676002,
          0.00009902741986777733767416405963811423126]
        [0, 0, 0.003808840904661839030108308815883328125,
          0.007002219151822802990444886443879874685212,
          -0.0143333413441469207061222206293861755600928,
          0.019278179961108796756125304323986603352066,
          -0.01228676763797171620791271663948189462719072,
          0.00283744326437027776038990779201464275168934,
          0.00014121714294278792780761766528664543842]
        [0, 0, 0.0043149561833070131687758879572301875,
          -0.006759523670873557624202322750741725706752,
          0.0073269315396073001417476359305223467051648,
          -0.0040117649398558579512353305320754595480464,
          0.00074465075122749612412430346101703091002032,
          0.00008860782047125877196899798221255072016]
        [0, 0, 0.0000801062525237513058760625, -0.000131862143879123131167366050048,
          0.0001465134934594345983901569991552, -0.0000861337409490076161532556473136,
          0.00002067682399339232595035207386768]
        [0, 35.1453416, 24.6673338, 0.668018491]
        [0, 21.1059749, 1.14314597]
        [0, 0.48905184]
        [0, 0, 0.0002258064] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.9090504168228309812822719432158203125, -7.749127575659766231151373094566746066125,
          7.5563353535250070616784505583099451652409,
          -2.739071179995943696517899855836384862524828,
          -0.6006215089312894901806193920639514834640268,
          0.5137325733431894713571534631089359766121584,
          -0.00340637148005510385576020176487914539225562,
          0.0010160991302393886711189369423704913976675, 0.0000257193354309938058589368845137650825]
        [0, 0, 1.69149800271542706122274960160320078125,
          -2.7762925372514533209881039767091594787196,
          3.093794946151682039351709308290135358918484,
          -1.8255957770558352573366598894665412535642776,
          0.4517005437097654651144002077989629581375596,
          -0.01156082102953580621323518766022468395654644,
          0.00303096473735704346252338655469749341676002,
          0.00009902741986777733767416405963811423126]
        [0, 0, 0.003808840904661839030108308815883328125,
          0.007002219151822802990444886443879874685212,
          -0.0143333413441469207061222206293861755600928,
          0.019278179961108796756125304323986603352066,
          -0.01228676763797171620791271663948189462719072,
          0.00283744326437027776038990779201464275168934,
          0.00014121714294278792780761766528664543842]
        [0, 0, 0.0043149561833070131687758879572301875,
          -0.006759523670873557624202322750741725706752,
          0.0073269315396073001417476359305223467051648,
          -0.0040117649398558579512353305320754595480464,
          0.00074465075122749612412430346101703091002032,
          0.00008860782047125877196899798221255072016]
        [0, 0, 0.0000801062525237513058760625, -0.000131862143879123131167366050048,
          0.0001465134934594345983901569991552, -0.0000861337409490076161532556473136,
          0.00002067682399339232595035207386768]
        [0, 35.1453416, 24.6673338, 0.668018491]
        [0, 21.1059749, 1.14314597]
        [0, 0.48905184]
        [0, 0, 0.0002258064] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.81 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.855625 (-0.155923082336) hw0 (by norm_num) lgU130
    have hτ1 : w / 0.855625 ≤ 1.168737 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.155923082336) + 1.168737 * w := by linarith
    have hwa : Real.log 0.81 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.155923082336) 1.168737 11.77889 13.09416
        0.1216805 0.01762718 (1797 / 2078) 0.623139770895 0.457386663 0.14546 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (1797 / 2078) = (3875 / 2078) by norm_num]; exact lgU133)
        (by norm_num) (by norm_num)
    have hRs : 0.457386663 + 0.14546 * ((2.08 + Real.log r + ((-1.155923082336) + 1.168737 * w)) *
        (0.1216805 + 0.01762718 * (Real.log r + 2 / 3 * ((-1.155923082336) + 1.168737 * w) -
        11.77889)) / 2) ≤ 0.450697313 + (-0.00605426486) * Real.log r + (-0.00753737351) * w +
        0.00128202481 * Real.log r ^ 2 + 0.00249724971 * w * Real.log r + 0.00116745125 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000006579789676119102296771170304 + 0.000000000001159589746784
          * Real.log r + 0.0000000000022164134228500734464 * w + 0.0000000000086 * Real.log r ^ 2 +
          0.000000000009476947 * w * Real.log r + 0.0000000000007039154423756 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.7 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL132]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.7 2.45958884076 0.084487 2.47115760358
        (Real.log r + (-1.155923082336) + 1.168737 * w) 1.7810727 1.01902 0.21476 1.1641
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL134 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL136]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.90831175 + 0.0323165456 * Real.log r + 0.0377695426 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 35.1453416 + 21.1059749 * Real.log r + 24.6673338 * w + 0.48905184 *
        Real.log r ^ 2 + 1.14314597 * w * Real.log r + 0.668018491 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((31494082580715620228536862243 /
          351562500000000000000000000000000000) + (112849059507230359 / 5625000000000000000000000) *
          Real.log r + (68898686253767296028861 / 1875000000000000000000000000000) * w +
          0.000000000084075 * Real.log r ^ 2 + 0.00000000954436312655 * w * Real.log r +
          0.000000000807480163717333675 * w ^ 2) (by ring) ?_)
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
/-- **Piece `[0.9025, 1]` of region `R0`** (`ptLoS`; moments `mom_0_9025_1`). -/
private theorem tR0_lo15 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) 0.9025 1
      (1 / Real.sqrt r * (0.1638759425058522 + Real.log r * 0.03605203737151255 + Real.log r ^ 2 *
          0.0003317203184678774 + Real.log r ^ 3 * 0.00009859673520441647 + Real.log r ^ 4 *
          0.000001685250128025622) + 1 / r * (3.490293046738064 + Real.log r * 1.309460100648093 +
          Real.log r ^ 2 * 0.02856378196574093) + 0.00001243618965337901) := by
  obtain ⟨hla, hlb⟩ := lr_of r 150000 520000 11.9183905686 13.1615840952 (by norm_num) hr0 hr1 lgL1
      lgU2
  have hkd := kD_ge y (10 ^ 25) 57.564626 (by norm_num) hy MN.lya_ge_1
  have hr : 0 < r := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hl0 : 0 ≤ Real.log r := by linarith
  have key : ∀ w ∈ Set.Icc (0.9025 : ℝ) 1, OC.gY (w * y) (w * r) * HW.phi w ≤
      shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.768137254157967391039147600637094709735,
          -6.8288676920209871071758525497690183365536,
          5.9999941751496786120085887392687833841494575,
          -1.99101326244040743575836023320338931502224395,
          -0.35013607049922232605226318522392692782803965,
          0.28571954747513034487744911648920997557639525,
          -0.0018106713393647985454426021718630879675952,
          0.0004648262338180947423563810986908437246507, 0.0000103828585220434227758575649882095932]
        [0, 0, 1.60870640669997109025478549261062581236555,
          -2.3701663471611043671435319677510777123068675,
          2.3709113315746895988615232027169464964087331,
          -1.2561079132730017288666993761596725526492173,
          0.279353595413604755456903373967043310769088,
          -0.0066297570404200759253299722122955321209094,
          0.0015409800346943554107736469634290530774504, 0.0000444159014825810393557774128550683104]
        [0, 0, 0.00359433387748514113329348811580158099764,
          0.006218879793462000756388864238126018388434,
          -0.011317136494788352325061288236080567057882,
          0.01357077290906373987619404558617664879751,
          -0.007741177095329062576996451558368589647736,
          0.001604289811064493608355132093485351451236, 0.000070371411475975824164883367390221136]
        [0, 0, 0.004164196315457138100055414780452558517312,
          -0.005859177954710177037938974301031525285696,
          0.00570230623958856324448439604729709347936,
          -0.002805521884021909484658643238073117049088,
          0.000469731179817646429823919762283500039808, 0.000049057647626972816756857230777227008]
        [0, 0, 0.0000759408881407942804308385797248, -0.0001121933708536417229621694214784,
          0.000111882586278559805756929214144, -0.0000590331544161093443151385508352,
          0.0000127187467643176968793604863232]
        [0, 37.4661233, 22.3485073, 0.536228915]
        [0, 21.2450399, 1.01950476]
        [0, 0.484583129]
        [0, 0, 0.00022177312] w ∧
      0 ≤ shapeG (1 / Real.sqrt r) (1 / r) (Real.log r)
        [0, 0, 5.768137254157967391039147600637094709735,
          -6.8288676920209871071758525497690183365536,
          5.9999941751496786120085887392687833841494575,
          -1.99101326244040743575836023320338931502224395,
          -0.35013607049922232605226318522392692782803965,
          0.28571954747513034487744911648920997557639525,
          -0.0018106713393647985454426021718630879675952,
          0.0004648262338180947423563810986908437246507, 0.0000103828585220434227758575649882095932]
        [0, 0, 1.60870640669997109025478549261062581236555,
          -2.3701663471611043671435319677510777123068675,
          2.3709113315746895988615232027169464964087331,
          -1.2561079132730017288666993761596725526492173,
          0.279353595413604755456903373967043310769088,
          -0.0066297570404200759253299722122955321209094,
          0.0015409800346943554107736469634290530774504, 0.0000444159014825810393557774128550683104]
        [0, 0, 0.00359433387748514113329348811580158099764,
          0.006218879793462000756388864238126018388434,
          -0.011317136494788352325061288236080567057882,
          0.01357077290906373987619404558617664879751,
          -0.007741177095329062576996451558368589647736,
          0.001604289811064493608355132093485351451236, 0.000070371411475975824164883367390221136]
        [0, 0, 0.004164196315457138100055414780452558517312,
          -0.005859177954710177037938974301031525285696,
          0.00570230623958856324448439604729709347936,
          -0.002805521884021909484658643238073117049088,
          0.000469731179817646429823919762283500039808, 0.000049057647626972816756857230777227008]
        [0, 0, 0.0000759408881407942804308385797248, -0.0001121933708536417229621694214784,
          0.000111882586278559805756929214144, -0.0000590331544161093443151385508352,
          0.0000127187467643176968793604863232]
        [0, 37.4661233, 22.3485073, 0.536228915]
        [0, 21.2450399, 1.01950476]
        [0, 0.484583129]
        [0, 0, 0.00022177312] w := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwr : (0.9025 : ℝ) * 150000 ≤ w * r := mul_le_mul hw.1 hr0 (by norm_num) hw0.le
    have hτ0 := log_le_tan w 0.950625 (-0.050635615919) hw0 (by norm_num) lgU138
    have hτ1 : w / 0.950625 ≤ 1.05194 * w := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num) hw0.le
    have hτ : Real.log w ≤ (-1.050635615919) + 1.05194 * w := by linarith
    have hwa : Real.log 0.9025 ≤ Real.log w := Real.log_le_log (by norm_num) hw.1
    have hwl : Real.log (w * r) = Real.log w + Real.log r := Real.log_mul hw0.ne' hr.ne'
    have hR := rChordLo y r w 19.997138805 2.08 (-1.050635615919) 1.05194 11.85088 13.16246
        0.1227558 0.01796067 (1813 / 2062) 0.630869277662 0.458363292 0.14434 hy0 hr hw0
        (by linarith) hτ (by linarith) (log8_le.trans (by norm_num)) (by linarith [hw.1])
        (by linarith [hw.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [show (1 : ℝ) + (1813 / 2062) = (3875 / 2062) by norm_num]; exact lgU141)
        (by norm_num) (by norm_num)
    have hRs : 0.458363292 + 0.14434 * ((2.08 + Real.log r + ((-1.050635615919) + 1.05194 * w)) *
        (0.1227558 + 0.01796067 * (Real.log r + 2 / 3 * ((-1.050635615919) + 1.05194 * w) -
        11.85088)) / 2) ≤ 0.450735719 + (-0.00607570005) * Real.log r + (-0.00685913425) * w +
        0.00129622156 * Real.log r ^ 2 + 0.00227257884 * w * Real.log r + 0.000956246633 * w ^ 2 :=
        by
      refine le_of_sub_eq _ _ (0.0000000009831255293102552315331824414 + 0.0000000000049857815942235
          * Real.log r + 0.000000000008535332279797974872 * w + 0.0000000000061 * Real.log r ^ 2 +
          0.00000000000431739 * w * Real.log r + 0.00000000000083681409464 * w ^ 2) (by ring) ?_
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
    have hLlo : 11.81 ≤ Real.log (w * r) := by
      rw [hwl]
      linarith [lgL140]
    obtain ⟨hF0, hS, hLL, hLL0⟩ := factorsS (w * r) 11.81 2.46894662916 0.083715 2.48033710707
        (Real.log r + (-1.050635615919) + 1.05194 * w) 1.7810727 1.0151577 0.21451 1.16545
        0.6931471808 (mul_pos hw0 hr) (by norm_num) hLlo lgL142 (by norm_num) (by norm_num)
        (by norm_num) (by linarith [lgL144]) hlt (by norm_num) (by norm_num) (by norm_num)
        Real.log_two_lt_d9.le
    have hSs : Real.sqrt (bigF (w * r)) ≤ 1.91518247 + 0.0319839776 * Real.log r + 0.0336452253 * w
        := hS.trans (by linarith)
    have hLs : lL (w * r) ≤ 37.4661233 + 21.2450399 * Real.log r + 22.3485073 * w + 0.484583129 *
        Real.log r ^ 2 + 1.01950476 * w * Real.log r + 0.536228915 * w ^ 2 := by
      refine hLL.trans (le_of_sub_eq _ _ ((6708118674013108159388300434043 /
          72000000000000000000000000000000000000) + (709161627406285003 /
          36000000000000000000000000) * Real.log r + (86968974116688372302791 /
          1800000000000000000000000000000) * w + 0.000000000488375 * Real.log r ^ 2 +
          0.000000007586962395 * w * Real.log r + 0.00000000037331461089815 * w ^ 2) (by ring) ?_)
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

/-- **Region `R0`, `w ≤ 1`**: the first piece and the 16 lo pieces, added. -/
theorem loR0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 1
      (1 / Real.sqrt r * (0.7947354653269084657 + Real.log r * 0.1887891190745208757 +
          Real.log r ^ 2 * 0.00171219688025978724 + Real.log r ^ 3 * 0.0004918262503263594376 +
          Real.log r ^ 4 * 0.000008967249028280634917) + 1 / r * (18.7477502652403501 + Real.log r *
          8.47265976347577404 + Real.log r ^ 2 * 0.2000782359857399316) + 0.00005871842307307207429)
          := by
  have h0 := tR0_first y r hy hr0 hr1
  have h1 := intBnd_add _ _ _ _ _ _ h0 (tR0_lo0 y r hy hr0 hr1)
  have h2 := intBnd_add _ _ _ _ _ _ h1 (tR0_lo1 y r hy hr0 hr1)
  have h3 := intBnd_add _ _ _ _ _ _ h2 (tR0_lo2 y r hy hr0 hr1)
  have h4 := intBnd_add _ _ _ _ _ _ h3 (tR0_lo3 y r hy hr0 hr1)
  have h5 := intBnd_add _ _ _ _ _ _ h4 (tR0_lo4 y r hy hr0 hr1)
  have h6 := intBnd_add _ _ _ _ _ _ h5 (tR0_lo5 y r hy hr0 hr1)
  have h7 := intBnd_add _ _ _ _ _ _ h6 (tR0_lo6 y r hy hr0 hr1)
  have h8 := intBnd_add _ _ _ _ _ _ h7 (tR0_lo7 y r hy hr0 hr1)
  have h9 := intBnd_add _ _ _ _ _ _ h8 (tR0_lo8 y r hy hr0 hr1)
  have h10 := intBnd_add _ _ _ _ _ _ h9 (tR0_lo9 y r hy hr0 hr1)
  have h11 := intBnd_add _ _ _ _ _ _ h10 (tR0_lo10 y r hy hr0 hr1)
  have h12 := intBnd_add _ _ _ _ _ _ h11 (tR0_lo11 y r hy hr0 hr1)
  have h13 := intBnd_add _ _ _ _ _ _ h12 (tR0_lo12 y r hy hr0 hr1)
  have h14 := intBnd_add _ _ _ _ _ _ h13 (tR0_lo13 y r hy hr0 hr1)
  have h15 := intBnd_add _ _ _ _ _ _ h14 (tR0_lo14 y r hy hr0 hr1)
  have h16 := intBnd_add _ _ _ _ _ _ h15 (tR0_lo15 y r hy hr0 hr1)
  exact intBnd_mono _ _ _ _ _ h16 (le_of_eq (by ring))

end Principia.Common.TernaryGoldbach.MC
