/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajS4Spine
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-!
# S4, link `AC0` PROVED: `|A(r)| ≤ 2.03`

`|A(r)| ≤ ∫₀^∞ h(1/v)dv/v = ∫₀² h(u)du/u = ∫₀² u(2 − u)³e^{u−1/2} du = 92e^{−1/2} − 12e^{3/2}`
(`integral_p0`: the antiderivative is `(−u⁴ + 10u³ − 42u² + 92u − 92)e^{u−1/2}`), and with
`x = e^{1/2}`, `x² = e > 2.7182818`, the value `92/x − 12x³` is at most `2.03` (truth `2.02055`).
This sharpens `HP.norm_Ah_le` (`7.172`, a crude majorant) by computing the integral exactly.
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set

/-- The antiderivative of `u(2 − u)³e^{u−1/2}` (Horner form). -/
noncomputable def F0 (u : ℝ) : ℝ :=
  ((((-u + 10) * u - 42) * u + 92) * u - 92) * Real.exp (u - 1 / 2)

/-- `(e^{u−1/2})' = e^{u−1/2}`. -/
theorem hasDerivAt_expm (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (x - 1 / 2)) (Real.exp (u - 1 / 2)) u := by
  have h := ((hasDerivAt_id' u).sub_const (1 / 2)).exp
  rwa [mul_one] at h

theorem hasDerivAt_F0 (u : ℝ) :
    HasDerivAt F0 (u * (2 - u) ^ 3 * Real.exp (u - 1 / 2)) u := by
  have d0 := (hasDerivAt_id' u).fun_neg.add_const (10 : ℝ)
  have d1 := (d0.fun_mul (hasDerivAt_id' u)).sub_const (42 : ℝ)
  have d2 := (d1.fun_mul (hasDerivAt_id' u)).add_const (92 : ℝ)
  have d3 := (d2.fun_mul (hasDerivAt_id' u)).sub_const (92 : ℝ)
  exact (d3.fun_mul (hasDerivAt_expm u)).congr_deriv (by ring)

/-- `∫₀² u(2 − u)³e^{u−1/2} du = 92e^{−1/2} − 12e^{3/2}`. -/
theorem integral_p0 :
    ∫ u in (0 : ℝ)..2, u * (2 - u) ^ 3 * Real.exp (u - 1 / 2) =
      92 * Real.exp (-(1 / 2)) - 12 * Real.exp (3 / 2) := by
  have hc : Continuous fun u : ℝ => u * (2 - u) ^ 3 * Real.exp (u - 1 / 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_F0 x)
    (hc.intervalIntegrable _ _)]
  unfold F0
  norm_num
  ring

/-- `92e^{−1/2} − 12e^{3/2} ≤ 2.03`. -/
theorem p0_val_le : 92 * Real.exp (-(1 / 2)) - 12 * Real.exp (3 / 2) ≤ 2.03 := by
  set x := Real.exp (1 / 2) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx2 : x ^ 2 = Real.exp 1 := by
    rw [hx, ← Real.exp_nat_mul]
    norm_num
  have hx3 : Real.exp (3 / 2) = x ^ 3 := by
    rw [hx, ← Real.exp_nat_mul]
    norm_num
  have hxi : Real.exp (-(1 / 2)) = x⁻¹ := by
    rw [hx, Real.exp_neg]
  have he := Real.exp_one_gt_d9
  have hsq : 2.7182818 ≤ x ^ 2 := by linarith
  have hxl : 1.64872 ≤ x := by nlinarith
  have hx4 : 2.7182818 ^ 2 ≤ x ^ 2 * x ^ 2 := by nlinarith
  rw [hx3, hxi, sub_le_iff_le_add, ← div_eq_mul_inv, div_le_iff₀ hx0]
  nlinarith

/-- **LINK [AC0] PROVED** -- `|A(r)| ≤ 2.03`. -/
theorem ac0_holds : AC0 := by
  intro r
  have h1 : ‖HP.Ah r‖ ≤ ∫ v in Ioi (0 : ℝ), HP.aH v := by
    unfold HP.Ah
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (HP.aH_nonneg v hv)]
  rw [HP.integral_aH_eq, EN.setInt_Ioi_02 _ fun t ht => by
    rw [HW.hFun_of_two_le ht.le, zero_div]] at h1
  have h2 : ∫ u in (0 : ℝ)..2, HW.hFun u / u =
      ∫ u in (0 : ℝ)..2, u * (2 - u) ^ 3 * Real.exp (u - 1 / 2) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    show HW.hFun u / u = u * (2 - u) ^ 3 * Real.exp (u - 1 / 2)
    rw [BL.hFun_eq_hP hu.1 hu.2]
    unfold BL.hP
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]
      simp
    · rw [div_eq_iff h.ne']
      ring
  rw [h2, integral_p0] at h1
  exact h1.trans p0_val_le

end Principia.Common.TernaryGoldbach.S4
