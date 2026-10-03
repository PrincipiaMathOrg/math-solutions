/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EasyCirc

set_option autoImplicit false

/-!
# `|η*|₁ = √(π/2)/49` EXACTLY, and `|η*|₂² ≤ 2/49`

Two of `EN.NormsE`'s conjuncts, for Helfgott's `η* = (η₂ ∗_M φ)(49·)` (`HW.etaStar`):

* `l1_etaStar : MajSp.l1 HW.etaStar = √(π/2)/49`. Fubini on the Mellin convolution:
  `∫₀^∞ (η₂ ∗_M φ)(s) ds = ∫₀^∞ (φ(y)/y)·∫₀^∞ η₂(s/y) ds dy = ∫₀^∞ φ(y)·|η₂|₁ dy`, with
  `|η₂|₁ = 1` (`int_eta2_Ioi`: `(2 log 2 − 1) + (2 − 2 log 2)` by the fundamental theorem of
  calculus on `[1/4, 1/2]`, `[1/2, 1]`) and `|φ|₁ = ∫₀^∞ t²e^{−t²/2} = √(π/2)` (`int_phi`:
  `t = √2·s` and `EN.int_t2_exp`). The swap is `integral_integral_swap`; its integrability
  hypothesis is `integrable_mconv_prod`, whose two slices are the same two integrals.
* `l2_etaStar_sq : MajSp.l2 HW.etaStar ^ 2 ≤ 2/49`, from `0 ≤ η* ≤ 1.414`:
  `|η*|₂² ≤ 1.414·|η*|₁ = 1.414·1.2533143/49 = 1.7722/49` (truth `1.77082/49`).
-/

namespace Principia.Common.TernaryGoldbach.EN

open MeasureTheory Set Filter

/-! ## `|η₂|₁ = 1` -/

/-- `η₂(t) = 4(2 log 2 + log t)` on `[1/4, 1/2]`. -/
theorem eta2_left {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) :
    HW.eta2 t = 4 * (2 * Real.log 2 + Real.log t) := by
  have ht : 0 < t := by linarith
  have hl : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul two_ne_zero ht.ne'
  have hle : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h4 : Real.log (4 * t) = 2 * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num) ht.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hge : 0 ≤ 2 * Real.log 2 + Real.log t := by
    rw [← h4]
    exact Real.log_nonneg (by linarith)
  rw [HW.eta2, if_pos ht, abs_of_nonpos hle, hl, max_eq_left (by linarith)]
  ring

/-- `η₂(t) = −4 log t` on `[1/2, 1]`. -/
theorem eta2_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) : HW.eta2 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hl : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul two_ne_zero ht.ne'
  have hge : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have hle : Real.log t ≤ 0 := Real.log_nonpos ht.le h2
  rw [HW.eta2, if_pos ht, abs_of_nonneg hge, hl, max_eq_left (by linarith)]
  ring

/-- `η₂` is continuous on `(0, ∞)`. -/
theorem eta2_contOn : ContinuousOn HW.eta2 (Ioi 0) := by
  have hE : Continuous fun v : ℝ => 4 * max (Real.log 2 - |v|) 0 :=
    continuous_const.mul ((continuous_const.sub continuous_abs).max continuous_const)
  have hL : ContinuousOn (fun t : ℝ => Real.log (2 * t)) (Ioi 0) :=
    ContinuousOn.log (continuousOn_const.mul continuousOn_id)
      fun t ht => (mul_pos two_pos (mem_Ioi.mp ht)).ne'
  refine (hE.comp_continuousOn hL).congr fun t ht => ?_
  simp only [Function.comp, HW.eta2, if_pos (mem_Ioi.mp ht)]

/-- `η₂` is measurable. -/
theorem measurable_eta2 : Measurable HW.eta2 := by
  have hE : Continuous fun v : ℝ => 4 * max (Real.log 2 - |v|) 0 :=
    continuous_const.mul ((continuous_const.sub continuous_abs).max continuous_const)
  have hL : Measurable fun t : ℝ => Real.log (2 * t) :=
    Real.measurable_log.comp (measurable_const.mul measurable_id)
  unfold HW.eta2
  exact Measurable.ite measurableSet_Ioi (hE.measurable.comp hL) measurable_const

/-- `log(1/2) = −log 2`. -/
theorem log_half : Real.log (1 / 2) = -Real.log 2 := by
  rw [one_div, Real.log_inv]

/-- `∫_{1/4}^{1/2} η₂ = 2 log 2 − 1`. -/
theorem int_eta2_left : ∫ t in (1 / 4 : ℝ)..(1 / 2), HW.eta2 t = 2 * Real.log 2 - 1 := by
  have hsub : uIcc (1 / 4 : ℝ) (1 / 2) ⊆ Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hcongr : EqOn HW.eta2 (fun t => 4 * (2 * Real.log 2 + Real.log t))
      (uIcc (1 / 4) (1 / 2)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact eta2_left ht.1 ht.2
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ t ∈ uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt
      (fun t => 4 * (2 * Real.log 2 * t + (t * Real.log t - t)))
      (4 * (2 * Real.log 2 + Real.log t)) t := by
    intro t ht
    have ht0 : 0 < t := hsub ht
    have h := ((hasDerivAt_id' t).const_mul (2 * Real.log 2)).add
      (((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht0.ne')).sub (hasDerivAt_id' t))
    refine (h.const_mul 4).congr_deriv ?_
    rw [mul_inv_cancel₀ ht0.ne']
    ring
  have hi : IntervalIntegrable (fun t => 4 * (2 * Real.log 2 + Real.log t)) volume (1 / 4)
      (1 / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul
      (continuousOn_const.add (Real.continuousOn_log.mono fun t ht => (hsub ht).ne'))
  have h14 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, log_half, h14]
  ring

/-- `∫_{1/2}^{1} η₂ = 2 − 2 log 2`. -/
theorem int_eta2_right : ∫ t in (1 / 2 : ℝ)..1, HW.eta2 t = 2 - 2 * Real.log 2 := by
  have hsub : uIcc (1 / 2 : ℝ) 1 ⊆ Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hcongr : EqOn HW.eta2 (fun t => -4 * Real.log t) (uIcc (1 / 2) 1) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact eta2_right ht.1 ht.2
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ t ∈ uIcc (1 / 2 : ℝ) 1, HasDerivAt (fun t => -4 * (t * Real.log t - t))
      (-4 * Real.log t) t := by
    intro t ht
    have ht0 : 0 < t := hsub ht
    have h := ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht0.ne')).sub (hasDerivAt_id' t)
    refine (h.const_mul (-4)).congr_deriv ?_
    rw [mul_inv_cancel₀ ht0.ne']
    ring
  have hi : IntervalIntegrable (fun t => -4 * Real.log t) volume (1 / 2) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (Real.continuousOn_log.mono fun t ht => (hsub ht).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, log_half, Real.log_one]
  ring

/-- **`|η₂|₁ = ∫₀^∞ η₂ = 1`.** -/
theorem int_eta2_Ioi : ∫ t in Ioi (0 : ℝ), HW.eta2 t = 1 := by
  have h : ∫ t in Ioi (0 : ℝ), HW.eta2 t = ∫ t in (1 / 4 : ℝ)..1, HW.eta2 t := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num) ht.1) fun t ht => ?_
    obtain ⟨h0, h1⟩ := ht
    have h0' : 0 < t := h0
    rcases le_or_gt t (1 / 4) with hq | hq
    · exact HW.eta2_of_le_quarter h0' hq
    · exact HW.eta2_of_one_le (le_of_lt (not_le.mp fun h => h1 ⟨hq, h⟩))
  have hi1 : IntervalIntegrable HW.eta2 volume (1 / 4) (1 / 2) :=
    (eta2_contOn.mono (HW.uIcc_pos (by norm_num) (by norm_num))).intervalIntegrable
  have hi2 : IntervalIntegrable HW.eta2 volume (1 / 2) 1 :=
    (eta2_contOn.mono (HW.uIcc_pos (by norm_num) (by norm_num))).intervalIntegrable
  rw [h, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, int_eta2_left,
    int_eta2_right]
  ring

/-- `η₂` is integrable on `(0, ∞)` (its integral is `1 ≠ 0`). -/
theorem integrable_eta2 : IntegrableOn HW.eta2 (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [int_eta2_Ioi]; norm_num)

/-- **`∫₀^∞ η₂(s/y) ds = y`** for `y > 0` (`s = y·r`). -/
theorem int_eta2_scale {y : ℝ} (hy : 0 < y) : ∫ s in Ioi (0 : ℝ), HW.eta2 (s / y) = y := by
  have h := integral_comp_mul_left_Ioi HW.eta2 0 (inv_pos.mpr hy)
  rw [mul_zero, smul_eq_mul, inv_inv, int_eta2_Ioi, mul_one] at h
  calc ∫ s in Ioi (0 : ℝ), HW.eta2 (s / y) = ∫ s in Ioi (0 : ℝ), HW.eta2 (y⁻¹ * s) :=
        setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [div_eq_inv_mul]
    _ = y := h

/-! ## `|φ|₁ = √(π/2)` -/

/-- **`|φ|₁ = ∫₀^∞ t²e^{−t²/2} = √(π/2)`** (`t = √2·s`, then `∫₀^∞ s²e^{−s²} = √π/4`). -/
theorem int_phi : ∫ t in Ioi (0 : ℝ), HW.phi t = Real.sqrt (Real.pi / 2) := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs' : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc := integral_comp_mul_left_Ioi HW.phi 0 h2
  rw [mul_zero, smul_eq_mul] at hc
  have he : (fun x => HW.phi (Real.sqrt 2 * x)) = fun x => 2 * (x ^ 2 * Real.exp (-x ^ 2)) := by
    funext x
    unfold HW.phi
    rw [mul_pow, hs2, show -(2 * x ^ 2) / 2 = -x ^ 2 by ring]
    ring
  rw [he, integral_const_mul, int_t2_exp] at hc
  have hI : ∫ t in Ioi (0 : ℝ), HW.phi t = Real.sqrt 2 * (2 * (Real.sqrt Real.pi / 4)) := by
    rw [hc, mul_inv_cancel_left₀ h2.ne']
  rw [hI, Real.sqrt_div Real.pi_pos.le, eq_div_iff h2.ne']
  linear_combination (Real.sqrt Real.pi / 2) * hs'

/-- `φ` is integrable on `(0, ∞)` (its integral is `√(π/2) ≠ 0`). -/
theorem integrable_phi : IntegrableOn HW.phi (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [int_phi]; positivity)

/-! ## Fubini on the Mellin convolution -/

/-- The `s`-slice: `∫₀^∞ η₂(s/y)φ(y)/y ds = φ(y)` for `y > 0`. -/
theorem int_slice {y : ℝ} (hy : 0 < y) :
    ∫ s in Ioi (0 : ℝ), HW.eta2 (s / y) * HW.phi y / y = HW.phi y := by
  simp_rw [mul_div_assoc]
  rw [integral_mul_const, int_eta2_scale hy, mul_comm]
  exact div_mul_cancel₀ (HW.phi y) hy.ne'

/-- The same slice with the norm inside (the integrand is nonnegative). -/
theorem int_norm_slice {y : ℝ} (hy : 0 < y) :
    ∫ s in Ioi (0 : ℝ), ‖HW.eta2 (s / y) * HW.phi y / y‖ = HW.phi y :=
  (setIntegral_congr_fun measurableSet_Ioi fun _ _ => Real.norm_of_nonneg
    (div_nonneg (mul_nonneg (HW.eta2_nonneg _) (HW.phi_nonneg y)) hy.le)).trans (int_slice hy)

/-- **The integrand of `η₂ ∗_M φ` is integrable on `(0,∞)²`**: every `y`-slice is, and the slice
integrals of its norm form `φ`, which is integrable. -/
theorem integrable_mconv_prod :
    Integrable (Function.uncurry fun s y : ℝ => HW.eta2 (s / y) * HW.phi y / y)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun s y : ℝ => HW.eta2 (s / y) * HW.phi y / y)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    (((measurable_eta2.comp (measurable_fst.div measurable_snd)).mul
      (HW.continuous_phi.measurable.comp measurable_snd)).div measurable_snd).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  constructor
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := hy
    have h1 : IntegrableOn (fun s => HW.eta2 (y⁻¹ * s)) (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff HW.eta2 0 (inv_pos.mpr hy0), mul_zero]
      exact integrable_eta2
    refine (h1.mul_const (HW.phi y / y)).congr (ae_of_all _ fun s => ?_)
    change HW.eta2 (y⁻¹ * s) * (HW.phi y / y) = HW.eta2 (s / y) * HW.phi y / y
    rw [div_eq_inv_mul s y]
    ring
  · refine integrable_phi.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun y hy => ?_)
    exact (int_norm_slice hy).symm

/-- **`∫₀^∞ (η₂ ∗_M φ) = |η₂|₁·|φ|₁ = √(π/2)`**, by `integral_integral_swap`. -/
theorem int_mconv : ∫ s in Ioi (0 : ℝ), HW.mconv HW.eta2 HW.phi s = Real.sqrt (Real.pi / 2) := by
  have h := integral_integral_swap integrable_mconv_prod
  unfold HW.mconv
  rw [h]
  calc ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), HW.eta2 (s / y) * HW.phi y / y
      = ∫ y in Ioi (0 : ℝ), HW.phi y :=
        setIntegral_congr_fun measurableSet_Ioi fun y hy => int_slice hy
    _ = Real.sqrt (Real.pi / 2) := int_phi

/-- **`∫₀^∞ η* = √(π/2)/49`** (`η*(t) = (η₂ ∗_M φ)(49t)`). -/
theorem int_etaStar : ∫ t in Ioi (0 : ℝ), HW.etaStar t = Real.sqrt (Real.pi / 2) / 49 := by
  have h := integral_comp_mul_left_Ioi (HW.mconv HW.eta2 HW.phi) 0 (by norm_num : (0 : ℝ) < 49)
  rw [mul_zero, smul_eq_mul, int_mconv] at h
  calc ∫ t in Ioi (0 : ℝ), HW.etaStar t = 49⁻¹ * Real.sqrt (Real.pi / 2) := h
    _ = Real.sqrt (Real.pi / 2) / 49 := by ring

/-- **`|η*|₁ = √(π/2)/49`, exactly** (`η* > 0` on `t > 0`). -/
theorem l1_etaStar : MajSp.l1 HW.etaStar = Real.sqrt (Real.pi / 2) / 49 :=
  (setIntegral_congr_fun measurableSet_Ioi fun _ ht => abs_of_pos (HW.etaStar_pos ht)).trans
    int_etaStar

/-- **`|η*|₂² ≤ 2/49`**: `η*² ≤ 1.414·η*`, so `|η*|₂² ≤ 1.414·√(π/2)/49 ≤ 1.7722/49`. -/
theorem l2_etaStar_sq : MajSp.l2 HW.etaStar ^ 2 ≤ 2 / 49 := by
  have hint : Integrable HW.etaStar (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [int_etaStar]; positivity)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), HW.etaStar t ^ 2 ≤ 1.414 * HW.etaStar t := fun t ht => by
    have h0 := (HW.etaStar_pos ht).le
    have h1 := (le_abs_self _).trans (HW.etaStar_le t)
    calc HW.etaStar t ^ 2 = HW.etaStar t * HW.etaStar t := sq _
      _ ≤ 1.414 * HW.etaStar t := mul_le_mul_of_nonneg_right h1 h0
  have h := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg (HW.etaStar t))
    (hint.const_mul 1.414) (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_const_mul, int_etaStar] at h
  have hs := MajSp.sqrt_pi_half.2
  unfold MajSp.l2
  rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  linarith

end Principia.Common.TernaryGoldbach.EN
