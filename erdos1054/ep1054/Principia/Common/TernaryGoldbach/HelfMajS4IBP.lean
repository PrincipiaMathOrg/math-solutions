/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajS4Plus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

/-!
# S4, links `AC1` and `AC2` PROVED, and `HM.PlusDecay`

`A(r) = ∫₀² p(u) u^{−ir} du` with `p(u) = h(u)/u = u(2 − u)³e^{u−1/2}` (`Ah_eq`: the substitution
`v = 1/u` in `HP.Ah`, as in `HP.integral_aH_eq`). Two integrations by parts, each written as the
fundamental theorem of calculus for a product that is continuous on `[0, 2]` although `u^{−ir}`
is not continuous at `0` (`cont_Icc`: the other factor vanishes there):

* `J1_eq`: `(h(u)u^{−ir})' = h'(u)u^{−ir} − ir·p(u)u^{−ir}`, and `h(0) = h(2) = 0`, so
  `∫h'u^{−ir} = ir·A(r)`. Hence `|r||A(r)| ≤ ∫₀²|h'| = 2h(1) = 2e^{1/2} ≤ 3.2975`, since
  `h'(u) = u(2 − u)²(4 + u)(1 − u)e^{u−1/2}` changes sign only at `1` (`int_abs_h1P`).
* `J2_eq`: `(h'(u)u·u^{−ir})' = h''(u)u·u^{−ir} + (1 − ir)h'(u)u^{−ir}`, and `h'(2) = 0`, so
  `|1 − ir||∫h'u^{−ir}| ≤ ∫₀²|h''(u)|u du`, which IS Helfgott's `C₂ = cK 2` (`cK2_eq`: `h` is
  `hP` near every point of `(0, 2)` and `0` beyond `2`). With `|1 − ir| ≥ |r|`:
  `r²|A(r)| ≤ C₂ ≤ 10.79195821038` (the CITED `HC.AppBCited`).

`plusDecay_holds`: the STATED `HM.PlusDecay` from `HC.AmanitaBisectCited` and `HC.AppBCited`.
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set Filter Topology

/-! ## (1) The polynomial-exponential pieces -/

/-- `p(u) = h(u)/u = u(2 − u)³e^{u−1/2}`. -/
noncomputable def pP (u : ℝ) : ℝ := u * (2 - u) ^ 3 * Real.exp (u - 1 / 2)

/-- `h'(u) = (16u − 28u² + 12u³ + u⁴ − u⁵)e^{u−1/2}`, in Horner form. -/
noncomputable def h1P (u : ℝ) : ℝ :=
  ((((-u + 1) * u + 12) * u - 28) * u + 16) * u * Real.exp (u - 1 / 2)

/-- `h''(u) = (16 − 40u + 8u² + 16u³ − 4u⁴ − u⁵)e^{u−1/2}`. -/
noncomputable def h2P (u : ℝ) : ℝ :=
  (16 - 40 * u + 8 * u ^ 2 + 16 * u ^ 3 - 4 * u ^ 4 - u ^ 5) * Real.exp (u - 1 / 2)

theorem hP_eq :
    BL.hP = fun x => (((-x + 6) * x - 12) * x + 8) * x * x * Real.exp (x - 1 / 2) := by
  funext x
  unfold BL.hP
  ring

theorem hasDerivAt_hP (u : ℝ) : HasDerivAt BL.hP (h1P u) u := by
  rw [hP_eq]
  have d0 := (hasDerivAt_id' u).fun_neg.add_const (6 : ℝ)
  have d1 := (d0.fun_mul (hasDerivAt_id' u)).sub_const (12 : ℝ)
  have d2 := (d1.fun_mul (hasDerivAt_id' u)).add_const (8 : ℝ)
  have d3 := (d2.fun_mul (hasDerivAt_id' u)).fun_mul (hasDerivAt_id' u)
  exact (d3.fun_mul (hasDerivAt_expm u)).congr_deriv (by unfold h1P; ring)

theorem hasDerivAt_h1P (u : ℝ) : HasDerivAt h1P (h2P u) u := by
  have d0 := (hasDerivAt_id' u).fun_neg.add_const (1 : ℝ)
  have d1 := (d0.fun_mul (hasDerivAt_id' u)).add_const (12 : ℝ)
  have d2 := (d1.fun_mul (hasDerivAt_id' u)).sub_const (28 : ℝ)
  have d3 := (d2.fun_mul (hasDerivAt_id' u)).add_const (16 : ℝ)
  have d4 := d3.fun_mul (hasDerivAt_id' u)
  exact (d4.fun_mul (hasDerivAt_expm u)).congr_deriv (by unfold h2P; ring)

theorem continuous_hP : Continuous BL.hP := by
  unfold BL.hP
  fun_prop

theorem continuous_pP : Continuous pP := by
  unfold pP
  fun_prop

theorem continuous_h1P : Continuous h1P := by
  unfold h1P
  fun_prop

theorem continuous_h2P : Continuous h2P := by
  unfold h2P
  fun_prop

theorem hP_zero : BL.hP 0 = 0 := by
  unfold BL.hP
  norm_num

theorem hP_two : BL.hP 2 = 0 := by
  unfold BL.hP
  norm_num

theorem hP_one : BL.hP 1 = Real.exp (1 / 2) := by
  unfold BL.hP
  norm_num

theorem h1P_two : h1P 2 = 0 := by
  unfold h1P
  norm_num

theorem h1P_fac (u : ℝ) :
    h1P u = u * (2 - u) ^ 2 * (4 + u) * Real.exp (u - 1 / 2) * (1 - u) := by
  unfold h1P
  ring

/-- `∫₀²|h'| = 2h(1) = 2e^{1/2}`: `h'` changes sign only at `1`. -/
theorem int_abs_h1P : ∫ u in (0 : ℝ)..2, |h1P u| = 2 * Real.exp (1 / 2) := by
  have hc : Continuous fun u => |h1P u| := continuous_h1P.abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2)]
  have hA : ∀ u : ℝ, 0 ≤ u → u ≤ 2 →
      0 ≤ u * (2 - u) ^ 2 * (4 + u) * Real.exp (u - 1 / 2) := fun u h0 h2 =>
    mul_nonneg (mul_nonneg (mul_nonneg h0 (sq_nonneg _)) (by linarith)) (Real.exp_pos _).le
  have e1 : ∫ u in (0 : ℝ)..1, |h1P u| = ∫ u in (0 : ℝ)..1, h1P u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    show |h1P u| = h1P u
    refine abs_of_nonneg ?_
    rw [h1P_fac]
    exact mul_nonneg (hA u hu.1 (by linarith [hu.2])) (by linarith [hu.2])
  have e2 : ∫ u in (1 : ℝ)..2, |h1P u| = ∫ u in (1 : ℝ)..2, -h1P u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    show |h1P u| = -h1P u
    refine abs_of_nonpos ?_
    rw [h1P_fac]
    nlinarith [mul_nonneg (hA u (by linarith [hu.1]) hu.2) (by linarith [hu.1] : (0 : ℝ) ≤ u - 1)]
  rw [e1, e2, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_hP x)
      (continuous_h1P.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_hP x)
      (continuous_h1P.intervalIntegrable _ _), hP_zero, hP_one, hP_two]
  ring

theorem exp_half_le : Real.exp (1 / 2) ≤ 1.64875 := by
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have h0 := Real.exp_pos (1 / 2)
  nlinarith

/-! ## (2) `u^{−ir}` -/

/-- `E_r(u) = e^{−ir log u}`, i.e. `u^{−ir}` for `u > 0`. -/
noncomputable def Er (r u : ℝ) : ℂ := Complex.exp ((-(r * Real.log u) : ℝ) * Complex.I)

theorem norm_Er (r u : ℝ) : ‖Er r u‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem measurable_Er (r : ℝ) : Measurable (Er r) :=
  Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
    ((Real.measurable_log.const_mul r).neg)).mul_const Complex.I)

theorem hasDerivAt_Er (r : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (Er r) (Er r u * ((-(r * u⁻¹) : ℝ) * Complex.I)) u :=
  (((((Real.hasDerivAt_log hu.ne').const_mul r).neg).ofReal_comp).mul_const Complex.I).cexp

theorem ii_Er (r : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun u => Er r u * (g u : ℂ)) volume a b := by
  refine IntervalIntegrable.mono_fun' (hg.abs.intervalIntegrable a b)
    ((measurable_Er r).mul (Complex.measurable_ofReal.comp hg.measurable)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  simp [norm_Er]

/-- `g(u)u^{−ir}` is continuous on `[0, 2]` when `g` is continuous with `g(0) = 0`. -/
theorem cont_Icc (r : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : g 0 = 0) :
    ContinuousOn (fun u => (g u : ℂ) * Er r u) (Icc 0 2) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h | h
  · rw [← h]
    have hz : (g 0 : ℂ) * Er r 0 = 0 := by rw [hg0, Complex.ofReal_zero, zero_mul]
    have ht : Tendsto (fun u => |g u|) (𝓝 0) (𝓝 0) := by
      have := hg.abs.tendsto 0
      rwa [hg0, abs_zero] at this
    change Tendsto (fun u => (g u : ℂ) * Er r u) (𝓝[Icc 0 2] 0) (𝓝 ((g 0 : ℂ) * Er r 0))
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    exact (ht.mono_left nhdsWithin_le_nhds).congr fun x => by simp [norm_Er]
  · exact ((Complex.continuous_ofReal.comp hg).continuousAt.mul
      (hasDerivAt_Er r h).continuousAt).continuousWithinAt

theorem norm_J (r : ℝ) (g : ℝ → ℝ) :
    ‖∫ u in (0 : ℝ)..2, Er r u * (g u : ℂ)‖ ≤ ∫ u in (0 : ℝ)..2, |g u| := by
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp [norm_Er]

/-! ## (3) `A(r)` on `[0, 2]` -/

theorem Ah_eq (r : ℝ) : HP.Ah r = ∫ u in (0 : ℝ)..2, Er r u * (pP u : ℂ) := by
  set G : ℝ → ℂ := fun v =>
    (HP.aH v : ℂ) * Complex.exp (((r * Real.log v : ℝ) : ℂ) * Complex.I) with hG
  have key : ∀ u : ℝ, 0 < u → (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) • G (u ^ (-1 : ℝ)) =
      Er r u * ((HW.hFun u / u : ℝ) : ℂ) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.ne'
    have e1 : |(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1) * HP.aH (u ^ (-1 : ℝ)) = HW.hFun u / u := by
      rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg_one, abs_neg, abs_one, one_mul,
        Real.rpow_neg hu.le, Real.rpow_two]
      unfold HP.aH
      rw [one_div, inv_inv]
      field_simp
    have e2 : Complex.exp (((r * Real.log (u ^ (-1 : ℝ)) : ℝ) : ℂ) * Complex.I) = Er r u := by
      unfold Er
      rw [Real.rpow_neg_one, Real.log_inv, mul_neg]
    simp only [hG]
    rw [Complex.real_smul, e2, ← e1]
    push_cast
    ring
  have hAh : HP.Ah r = ∫ v in Ioi (0 : ℝ), G v := rfl
  rw [hAh, ← integral_comp_rpow_Ioi G (p := -1) (by norm_num),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_,
    intervalIntegral.integral_of_le (by norm_num)]
  · refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    change (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) • G (u ^ (-1 : ℝ)) = Er r u * (pP u : ℂ)
    rw [key u hu.1, BL.hFun_eq_hP hu.1.le hu.2]
    unfold BL.hP pP
    congr 2
    rw [div_eq_iff hu.1.ne']
    ring
  · intro u hu
    have h2 : 2 < u := by
      by_contra h
      exact hu.2 ⟨hu.1, not_lt.mp h⟩
    change (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) • G (u ^ (-1 : ℝ)) = 0
    rw [key u hu.1, HW.hFun_of_two_le h2.le, zero_div, Complex.ofReal_zero, mul_zero]

/-! ## (4) The two integrations by parts -/

/-- `∫₀² h'(u)u^{−ir} du = ir·A(r)`. -/
theorem J1_eq (r : ℝ) :
    ∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ) =
      (r : ℂ) * Complex.I * ∫ u in (0 : ℝ)..2, Er r u * (pP u : ℂ) := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 2, HasDerivAt (fun u => (BL.hP u : ℂ) * Er r u)
      (Er r x * (h1P x : ℂ) - (r : ℂ) * Complex.I * (Er r x * (pP x : ℂ))) x := by
    intro x hx
    have hp : BL.hP x * x⁻¹ = pP x := by
      unfold BL.hP pP
      rw [← div_eq_mul_inv, div_eq_iff hx.1.ne']
      ring
    have hpc : (BL.hP x : ℂ) * (x : ℂ)⁻¹ = (pP x : ℂ) := by
      rw [← hp, Complex.ofReal_mul, Complex.ofReal_inv]
    refine (((hasDerivAt_hP x).ofReal_comp).fun_mul (hasDerivAt_Er r hx.1)).congr_deriv ?_
    push_cast
    linear_combination (-((r : ℂ) * Complex.I * Er r x)) * hpc
  have i1 := ii_Er r continuous_h1P 0 2
  have i2 := (ii_Er r continuous_pP 0 2).const_mul ((r : ℂ) * Complex.I)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 2)
    (cont_Icc r continuous_hP hP_zero) hderiv (i1.sub i2)
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul, hP_two,
    hP_zero] at hF
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hF
  linear_combination hF

/-- `∫₀² h''(u)u·u^{−ir} du + (1 − ir)∫₀² h'(u)u^{−ir} du = 0`. -/
theorem J2_eq (r : ℝ) :
    (∫ u in (0 : ℝ)..2, Er r u * ((h2P u * u : ℝ) : ℂ)) +
      (1 - (r : ℂ) * Complex.I) * ∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ) = 0 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 2, HasDerivAt (fun u => ((h1P u * u : ℝ) : ℂ) * Er r u)
      (Er r x * ((h2P x * x : ℝ) : ℂ) +
        (1 - (r : ℂ) * Complex.I) * (Er r x * (h1P x : ℂ))) x := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
    have hxx : (x : ℂ) * (x : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hx0
    refine ((((hasDerivAt_h1P x).fun_mul (hasDerivAt_id' x)).ofReal_comp).fun_mul
      (hasDerivAt_Er r hx.1)).congr_deriv ?_
    push_cast
    linear_combination (-((r : ℂ) * Complex.I * Er r x * (h1P x : ℂ))) * hxx
  have hc : Continuous fun u => h1P u * u := continuous_h1P.mul continuous_id'
  have hc2 : Continuous fun u => h2P u * u := continuous_h2P.mul continuous_id'
  have i1 := ii_Er r hc2 0 2
  have i2 := (ii_Er r continuous_h1P 0 2).const_mul (1 - (r : ℂ) * Complex.I)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 2)
    (cont_Icc r hc (by simp)) hderiv (i1.add i2)
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul, h1P_two] at hF
  simp only [zero_mul, mul_zero, Complex.ofReal_zero, sub_zero] at hF
  exact hF

/-! ## (5) `C₂` is Helfgott's `cK 2` -/

theorem cK2_eq : HC.cK 2 = ∫ u in (0 : ℝ)..2, |h2P u| * u := by
  have hin : ∀ x ∈ Ioo (0 : ℝ) 2, iteratedDeriv 2 HW.hFun x = h2P x := by
    intro x hx
    have hev : HW.hFun =ᶠ[𝓝 x] BL.hP := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact BL.hFun_eq_hP hy.1.le hy.2.le
    rw [(hev.iteratedDeriv 2).eq_of_nhds]
    have hd : deriv BL.hP = h1P := funext fun y => (hasDerivAt_hP y).deriv
    change iteratedDeriv (1 + 1) BL.hP x = h2P x
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
    exact (hasDerivAt_h1P x).deriv
  have hout : ∀ x : ℝ, 2 < x → iteratedDeriv 2 HW.hFun x = 0 := by
    intro x hx
    have hev : HW.hFun =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact HW.hFun_of_two_le (le_of_lt hy)
    rw [(hev.iteratedDeriv 2).eq_of_nhds]
    change iteratedDeriv (1 + 1) (fun _ : ℝ => (0 : ℝ)) x = 0
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simp
  unfold HC.cK
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_,
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  · refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [hin x hx]
    norm_num
  · intro x hx
    have h2 : 2 < x := by
      by_contra h
      exact hx.2 ⟨hx.1, not_lt.mp h⟩
    change |iteratedDeriv 2 HW.hFun x| * x ^ (2 - 1) = 0
    rw [hout x h2, abs_zero, zero_mul]

/-! ## (6) `AC1`, `AC2`, `HM.PlusDecay` -/

/-- **LINK [AC1] PROVED** -- `|r||A(r)| ≤ 2e^{1/2} ≤ 3.2975`. -/
theorem ac1_holds : AC1 := by
  intro r
  rw [Ah_eq]
  have hn : ‖∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ)‖ =
      |r| * ‖∫ u in (0 : ℝ)..2, Er r u * (pP u : ℂ)‖ := by
    rw [J1_eq, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := norm_J r h1P
  rw [int_abs_h1P] at hb
  have hx := exp_half_le
  calc ‖∫ u in (0 : ℝ)..2, Er r u * (pP u : ℂ)‖ * |r|
      = ‖∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ)‖ := by rw [hn, mul_comm]
    _ ≤ 3.2975 := by linarith

/-- **LINK [AC2] PROVED** -- `r²|A(r)| ≤ C₂ ≤ 10.79195821038` (`C₂` CITED). -/
theorem ac2_holds : AC2 := by
  intro hb r
  rw [Ah_eq]
  have h2 := J2_eq r
  have hn1 : ‖∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ)‖ =
      |r| * ‖∫ u in (0 : ℝ)..2, Er r u * (pP u : ℂ)‖ := by
    rw [J1_eq, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖(1 - (r : ℂ) * Complex.I) * ∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ)‖ =
      ‖∫ u in (0 : ℝ)..2, Er r u * ((h2P u * u : ℝ) : ℂ)‖ := by
    rw [show (1 - (r : ℂ) * Complex.I) * ∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ) =
      -∫ u in (0 : ℝ)..2, Er r u * ((h2P u * u : ℝ) : ℂ) by linear_combination h2, norm_neg]
  have hr : |r| ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.I‖ := by
    have := Complex.abs_im_le_norm ((1 : ℂ) - (r : ℂ) * Complex.I)
    simpa using this
  have hJ2 : ‖∫ u in (0 : ℝ)..2, Er r u * ((h2P u * u : ℝ) : ℂ)‖ ≤ HC.cK 2 := by
    have := norm_J r fun u => h2P u * u
    rw [cK2_eq]
    refine this.trans (le_of_eq (intervalIntegral.integral_congr fun u hu => ?_))
    rw [uIcc_of_le (by norm_num)] at hu
    rw [abs_mul, abs_of_nonneg hu.1]
  have hC := hb.1.2
  calc ‖∫ u in (0 : ℝ)..2, Er r u * (pP u : ℂ)‖ * r ^ 2
      = |r| * ‖∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ)‖ := by
        rw [hn1, ← sq_abs]
        ring
    _ ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.I‖ * ‖∫ u in (0 : ℝ)..2, Er r u * (h1P u : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ = ‖∫ u in (0 : ℝ)..2, Er r u * ((h2P u * u : ℝ) : ℂ)‖ := by rw [← norm_mul, hn2]
    _ ≤ 10.792 := by linarith

/-- **`HM.PlusDecay` PROVED** -- `lem:schastya`'s pointwise decay of `G_δ^{η₊}`, from the two
CITED computations `E(1.5) ≥ 0.1598` (`HC.AmanitaBisectCited`) and `C₂ ≤ 10.79195821038`
(`HC.AppBCited`) and nothing else. -/
theorem plusDecay_holds (hc : HC.AmanitaBisectCited) (hb : HC.AppBCited) : HM.PlusDecay :=
  plusDecay_of_ac12 hc hb ac1_holds ac2_holds

end Principia.Common.TernaryGoldbach.S4
