/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajGarmola

set_option autoImplicit false

/-!
# The four moments of `η₂` — `HM.Eta2Moments` PROVED

`HM.eta2Moments_holds : HM.Eta2Moments`: `∫_{1/4}^{1} η₂ = 1`, `∫ w^{−1/2}η₂ = 24 − 16√2 ≤ 1.37259`,
`∫ w^{−1}η₂ = 4(log 2)² ≤ 1.92182`, `∫ w^{−3/2}η₂ = 48 − 32√2 ≤ 2.74517` (majarcs 4157–4163), by
the fundamental theorem of calculus on `[1/4, 1/2]`, where `η₂(w) = 4 log 4w` (`eta2_lo'`), and on
`[1/2, 1]`, where `η₂(w) = −4 log w` (`eta2_hi'`). The antiderivatives are
`4(w log 4w − w)`, `8√w(log 4w − 2)`, `2 log² 4w`, `−8(log 4w + 2)/√w` and their `log w` twins.

`helfMajR_of_links''`: `MR.HelfMajR η₊ (η₂ ∗_M φ)` from seventeen named links (`GarmolaDecr` and
`Eta2Moments` discharged).
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set HW

/-- `η₂(w) = 4 log 4w` on `[1/4, 1/2]`. -/
theorem eta2_lo' {w : ℝ} (h1 : 1 / 4 ≤ w) (h2 : w ≤ 1 / 2) : eta2 w = 4 * Real.log (4 * w) := by
  unfold eta2
  rw [if_pos (by linarith)]
  have hlog : Real.log (2 * w) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have e : Real.log (4 * w) = Real.log 2 + Real.log (2 * w) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    ring_nf
  have h4 : 0 ≤ Real.log (4 * w) := Real.log_nonneg (by linarith)
  rw [abs_of_nonpos hlog, max_eq_left (by linarith)]
  linarith

/-- `η₂(w) = −4 log w` on `[1/2, 1]`. -/
theorem eta2_hi' {w : ℝ} (h1 : 1 / 2 ≤ w) (h2 : w ≤ 1) : eta2 w = -4 * Real.log w := by
  unfold eta2
  rw [if_pos (by linarith)]
  have hlog : 0 ≤ Real.log (2 * w) := Real.log_nonneg (by linarith)
  have e : Real.log (2 * w) = Real.log 2 + Real.log w := Real.log_mul (by norm_num) (by linarith)
  have h4 : Real.log w ≤ 0 := Real.log_nonpos (by linarith) h2
  rw [abs_of_nonneg hlog, max_eq_left (by linarith)]
  linarith

/-- `η₂` is continuous on `[1/4, 1]`. -/
theorem eta2_contOn : ContinuousOn eta2 (Icc (1 / 4) 1) := by
  have hg : ContinuousOn (fun w : ℝ => 4 * max (Real.log 2 - |Real.log (2 * w)|) 0)
      (Icc (1 / 4) 1) := by
    refine continuousOn_const.mul (ContinuousOn.sup (continuousOn_const.sub
      (ContinuousOn.abs (ContinuousOn.log (by fun_prop) fun w hw => ?_))) continuousOn_const)
    have := hw.1
    positivity
  refine hg.congr fun w hw => ?_
  unfold eta2
  rw [if_pos (by linarith [hw.1])]

/-- **A moment of `η₂` from two antiderivatives.** -/
theorem eta2_moment {p F₁ F₂ : ℝ → ℝ} (hp : ContinuousOn p (Icc (1 / 4) 1))
    (hnn : ∀ w ∈ Icc (1 / 4 : ℝ) 1, 0 ≤ p w)
    (hF₁ : ∀ w ∈ uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt F₁ (4 * Real.log (4 * w) * p w) w)
    (hF₂ : ∀ w ∈ uIcc (1 / 2 : ℝ) 1, HasDerivAt F₂ (-4 * Real.log w * p w) w) :
    ∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w * p w) =
      ENNReal.ofReal (F₁ (1 / 2) - F₁ (1 / 4) + (F₂ 1 - F₂ (1 / 2))) := by
  have hc : ContinuousOn (fun w => eta2 w * p w) (Icc (1 / 4) 1) := eta2_contOn.mul hp
  have hnn' : ∀ w ∈ Icc (1 / 4 : ℝ) 1, 0 ≤ eta2 w * p w :=
    fun w hw => mul_nonneg (eta2_nonneg w) (hnn w hw)
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
    ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hnn'))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hs1 : uIcc (1 / 4 : ℝ) (1 / 2) ⊆ Icc (1 / 4) 1 := by
    rw [uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hs2 : uIcc (1 / 2 : ℝ) 1 ⊆ Icc (1 / 4) 1 := by
    rw [uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hi1 : IntervalIntegrable (fun w => eta2 w * p w) volume (1 / 4) (1 / 2) :=
    (hc.mono hs1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun w => eta2 w * p w) volume (1 / 2) 1 :=
    (hc.mono hs2).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hpos1 : ∀ w ∈ uIcc (1 / 4 : ℝ) (1 / 2), 0 < w := fun w hw => by
    have := (hs1 hw).1
    linarith
  have hpos2 : ∀ w ∈ uIcc (1 / 2 : ℝ) 1, 0 < w := fun w hw => by
    have := (hs2 hw).1
    linarith
  have e1 : ∫ w in (1 / 4 : ℝ)..(1 / 2), eta2 w * p w =
      ∫ w in (1 / 4 : ℝ)..(1 / 2), 4 * Real.log (4 * w) * p w := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le (by norm_num)] at hw
    rw [eta2_lo' hw.1 hw.2]
  have e2 : ∫ w in (1 / 2 : ℝ)..1, eta2 w * p w =
      ∫ w in (1 / 2 : ℝ)..1, -4 * Real.log w * p w := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le (by norm_num)] at hw
    rw [eta2_hi' hw.1 hw.2]
  have hd1 : ContinuousOn (fun w => 4 * Real.log (4 * w) * p w) (uIcc (1 / 4 : ℝ) (1 / 2)) := by
    refine (continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun w hw => ?_)).mul
      (hp.mono hs1)
    have := hpos1 w hw
    positivity
  have hd2 : ContinuousOn (fun w => -4 * Real.log w * p w) (uIcc (1 / 2 : ℝ) 1) := by
    refine (continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun w hw => ?_)).mul
      (hp.mono hs2)
    exact (hpos2 w hw).ne'
  rw [e1, e2, intervalIntegral.integral_eq_sub_of_hasDerivAt hF₁ hd1.intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF₂ hd2.intervalIntegrable]

/-! ## The eight antiderivatives -/

theorem dF1 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => 4 * (w * Real.log (4 * w) - w)) (4 * Real.log (4 * w) * 1) w := by
  have h2 := ((hasDerivAt_id w).const_mul 4).log (mul_ne_zero (by norm_num) hw.ne')
  refine ((((hasDerivAt_id w).mul h2).sub (hasDerivAt_id w)).const_mul 4).congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem dG1 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => -4 * (w * Real.log w - w)) (-4 * Real.log w * 1) w := by
  have h2 := Real.hasDerivAt_log hw.ne'
  refine ((((hasDerivAt_id w).mul h2).sub (hasDerivAt_id w)).const_mul (-4)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem dF2 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => 8 * Real.sqrt w * (Real.log (4 * w) - 2))
      (4 * Real.log (4 * w) * (1 / Real.sqrt w)) w := by
  have h1 := ((Real.hasDerivAt_sqrt hw.ne').const_mul 8)
  have h2 := (((hasDerivAt_id w).const_mul 4).log (mul_ne_zero (by norm_num) hw.ne')).sub_const 2
  refine (h1.mul h2).congr_deriv ?_
  simp only [id]
  field_simp
  rw [Real.sq_sqrt hw.le]
  ring

theorem dG2 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => -8 * Real.sqrt w * (Real.log w - 2))
      (-4 * Real.log w * (1 / Real.sqrt w)) w := by
  have h1 := ((Real.hasDerivAt_sqrt hw.ne').const_mul (-8))
  have h2 := (Real.hasDerivAt_log hw.ne').sub_const 2
  refine (h1.mul h2).congr_deriv ?_
  field_simp
  rw [Real.sq_sqrt hw.le]
  ring

theorem dF3 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => 2 * Real.log (4 * w) ^ 2) (4 * Real.log (4 * w) * (1 / w)) w := by
  have h2 := ((hasDerivAt_id w).const_mul 4).log (mul_ne_zero (by norm_num) hw.ne')
  refine ((h2.pow 2).const_mul 2).congr_deriv ?_
  simp only [id]
  field_simp
  norm_num

theorem dG3 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => -2 * Real.log w ^ 2) (-4 * Real.log w * (1 / w)) w := by
  have h2 := Real.hasDerivAt_log hw.ne'
  refine ((h2.pow 2).const_mul (-2)).congr_deriv ?_
  field_simp
  norm_num

theorem dF4 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => -8 * (Real.log (4 * w) + 2) / Real.sqrt w)
      (4 * Real.log (4 * w) * (1 / (w * Real.sqrt w))) w := by
  have h1 := (((hasDerivAt_id w).const_mul 4).log (mul_ne_zero (by norm_num) hw.ne')).add_const 2
  have h3 := (h1.const_mul (-8)).div (Real.hasDerivAt_sqrt hw.ne') (Real.sqrt_pos.mpr hw).ne'
  refine h3.congr_deriv ?_
  simp only [id]
  field_simp
  rw [Real.sq_sqrt hw.le]
  ring

theorem dG4 (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w => 8 * (Real.log w + 2) / Real.sqrt w)
      (-4 * Real.log w * (1 / (w * Real.sqrt w))) w := by
  have h1 := (Real.hasDerivAt_log hw.ne').add_const 2
  have h3 := (h1.const_mul 8).div (Real.hasDerivAt_sqrt hw.ne') (Real.sqrt_pos.mpr hw).ne'
  refine h3.congr_deriv ?_
  field_simp
  rw [Real.sq_sqrt hw.le]
  ring

/-! ## The four moments -/

/-- A point of `uIcc a b` with `0 < a ≤ b` is positive. -/
theorem pos_of_uIcc {a b w : ℝ} (ha : 0 < a) (hab : a ≤ b) (hw : w ∈ uIcc a b) : 0 < w := by
  rw [uIcc_of_le hab] at hw
  linarith [hw.1]

/-- `√(1/4) = 1/2`. -/
theorem sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `0.7071067 ≤ √(1/2) ≤ 0.70710679`. -/
theorem sqrt_half_bounds : 0.7071067 ≤ Real.sqrt (1 / 2) ∧ Real.sqrt (1 / 2) ≤ 0.70710679 :=
  ⟨(Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num),
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)⟩

/-- `log(1/2) = −log 2`. -/
theorem log_half : Real.log (1 / 2) = -Real.log 2 := by
  rw [one_div, Real.log_inv]

/-- **The four moments of `η₂` — `Eta2Moments` PROVED.** -/
theorem eta2Moments_holds : Eta2Moments := by
  have hl2 : Real.log (4 * (1 / 2)) = Real.log 2 := by norm_num
  have hl4 : Real.log (4 * (1 / 4)) = 0 := by norm_num
  have hl2' : Real.log (4 / 2) = Real.log 2 := by norm_num
  have hl4' : Real.log (4 / 4) = 0 := by norm_num
  have hlh := log_half
  obtain ⟨hs1, hs2⟩ := sqrt_half_bounds
  have hsq := sqrt_quarter
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := eta2_moment (p := fun _ => 1) continuousOn_const (fun _ _ => zero_le_one)
      (fun w hw => dF1 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
      (fun w hw => dG1 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
    simp only [mul_one] at h
    rw [h]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hl2, hl4, Real.log_one, hlh]
    ring
  · have hp : ContinuousOn (fun w : ℝ => 1 / Real.sqrt w) (Icc (1 / 4) 1) :=
      continuousOn_const.div (by fun_prop) fun w hw => by
        have := hw.1
        positivity
    have h := eta2_moment (p := fun w => 1 / Real.sqrt w) hp
      (fun w _ => by positivity)
      (fun w hw => dF2 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
      (fun w hw => dG2 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
    simp only [mul_one_div] at h
    rw [h]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hl2', hl4', Real.log_one, hlh, hsq, Real.sqrt_one]
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  · have hp : ContinuousOn (fun w : ℝ => 1 / w) (Icc (1 / 4) 1) :=
      continuousOn_const.div continuousOn_id fun w hw => by
        have := hw.1
        positivity
    have h := eta2_moment (p := fun w => 1 / w) hp
      (fun w hw => by
        have := hw.1
        positivity)
      (fun w hw => dF3 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
      (fun w hw => dG3 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
    simp only [mul_one_div] at h
    rw [h]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hl2', hl4', Real.log_one, hlh]
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  · have hp : ContinuousOn (fun w : ℝ => 1 / (w * Real.sqrt w)) (Icc (1 / 4) 1) :=
      continuousOn_const.div (by fun_prop) fun w hw => by
        have := hw.1
        positivity
    have h := eta2_moment (p := fun w => 1 / (w * Real.sqrt w)) hp
      (fun w hw => by
        have := hw.1
        positivity)
      (fun w hw => dF4 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
      (fun w hw => dG4 w (pos_of_uIcc (by norm_num) (by norm_num) hw))
    simp only [mul_one_div] at h
    rw [h]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hl2', hl4', Real.log_one, hlh, hsq, Real.sqrt_one]
    have hs0 : 0 < Real.sqrt (1 / 2) := by linarith
    have e : -8 * (Real.log 2 + 2) / Real.sqrt (1 / 2) - -8 * (0 + 2) / (1 / 2) +
        (8 * (0 + 2) / 1 - 8 * (-Real.log 2 + 2) / Real.sqrt (1 / 2)) =
          48 - 32 / Real.sqrt (1 / 2) := by
      field_simp
      ring
    rw [e]
    have h32 : 32 / 0.70710679 ≤ 32 / Real.sqrt (1 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) hs0 hs2
    have hn : (48 : ℝ) - 32 / 0.70710679 ≤ 2.74517 := by norm_num
    linarith

/-- **THE HEADLINE WITH `GarmolaDecr` AND `Eta2Moments` DISCHARGED**: seventeen named links. -/
theorem helfMajR_of_links'' (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt) (ko : Kolona)
    (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mt : MalTailInt) (mm : MalMain) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  helfMajR_of_links' hEF hZC hHs pr pn pd pt fr fn fd ft ko eta2Moments_holds mr mn md mt mm

end Principia.Common.TernaryGoldbach.HM
