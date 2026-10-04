/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajS4Ray
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false

/-!
# S4, links `Moment1` and `Moment2` PROVED: the real ray integral

`rayInt m c b = ∫₀^∞ r^m e^{−cr²/2 + br} dr`, for `c > 0`, `b ≥ 0`, `r₀ = b/c`, `g = √(2π/c)`:

* `moment1_holds`: `m ∈ [0, 1]`: `≤ e^{b²/2c}((1 − m)g + m(r₀g + 2/c))`;
* `moment2_holds`: `m ∈ [1, 2]`: `≤ e^{b²/2c}((2 − m)(r₀g + 2/c) + (m − 1)(r₀²g + g/c))`.

Completing the square (`exp_complete`), Bernoulli's inequality for real exponents (Mathlib's
`rpow_one_add_le_one_add_mul_self`: `t^m ≤ (1 − m) + mt`, and `t^m = t·t^{m−1}`), extending
`(0, ∞)` to `ℝ` and translating by `r₀` (`integral_sub_right_eq_self`), then the Gaussian moments
`∫e^{−cu²/2} = g` (`integral_gaussian`), `∫|u|e^{−cu²/2} = 2/c` (`integral_comp_abs`, Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow`), `∫ue^{−cu²/2} = 0` (oddness) and `∫u²e^{−cu²/2} = g/c`
(integration by parts against `(ue^{−cu²/2})'`, `integral_eq_zero_of_hasDerivAt_of_integrable`).
The cross term of the second moment vanishes exactly; only the first moment uses `|u + r₀| ≤
|u| + r₀`.
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set Filter

/-- `∫ e^{−cu²/2} = √(2π/c)`. -/
theorem gauss0 {c : ℝ} (hc : 0 < c) : ∫ u : ℝ, Real.exp (-(c / 2) * u ^ 2) = gw c := by
  rw [integral_gaussian, gw]
  congr 1
  field_simp

theorem int_sq_gauss {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ℝ => u ^ 2 * Real.exp (-(c / 2) * u ^ 2) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := c / 2) (by positivity) (s := 2) (by norm_num)
  simp only [Real.rpow_two] at this
  exact this

/-- `∫ |u| e^{−cu²/2} = 2/c`. -/
theorem gauss1abs {c : ℝ} (hc : 0 < c) : ∫ u : ℝ, |u| * Real.exp (-(c / 2) * u ^ 2) = 2 / c := by
  have h1 := integral_comp_abs (f := fun x : ℝ => x * Real.exp (-(c / 2) * x ^ 2))
  simp only [sq_abs] at h1
  rw [h1]
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := c / 2) two_pos
    (by norm_num) (by positivity)
  have e : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(c / 2) * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(c / 2) * x ^ (2 : ℝ)) := by
    congr 1
    funext x
    rw [Real.rpow_one, Real.rpow_two]
  rw [e, h]
  norm_num [Real.rpow_neg_one]
  field_simp

/-- `∫ u e^{−cu²/2} = 0`. -/
theorem gauss1 {c : ℝ} : ∫ u : ℝ, u * Real.exp (-(c / 2) * u ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => u * Real.exp (-(c / 2) * u ^ 2)) volume
  simp only [neg_sq] at h
  rw [show (fun u : ℝ => -u * Real.exp (-(c / 2) * u ^ 2)) =
    fun u => -(u * Real.exp (-(c / 2) * u ^ 2)) from funext fun u => neg_mul _ _,
    integral_neg] at h
  linarith

/-- `∫ u² e^{−cu²/2} = √(2π/c)/c` (integration by parts against `(u e^{−cu²/2})'`). -/
theorem gauss2 {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, u ^ 2 * Real.exp (-(c / 2) * u ^ 2) = gw c / c := by
  have hb : 0 < c / 2 := by positivity
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => u * Real.exp (-(c / 2) * u ^ 2))
      (Real.exp (-(c / 2) * u ^ 2) - c * (u ^ 2 * Real.exp (-(c / 2) * u ^ 2))) u := by
    intro u
    have h3 := (hasDerivAt_id' u).fun_mul (((hasDerivAt_pow 2 u).const_mul (-(c / 2))).exp)
    refine h3.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hf' : Integrable fun u : ℝ =>
      Real.exp (-(c / 2) * u ^ 2) - c * (u ^ 2 * Real.exp (-(c / 2) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).sub ((int_sq_gauss hc).const_mul c)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd hf' (integrable_mul_exp_neg_mul_sq hb)
  rw [integral_sub (integrable_exp_neg_mul_sq hb) ((int_sq_gauss hc).const_mul c),
    integral_const_mul, gauss0 hc] at h0
  rw [eq_div_iff hc.ne']
  linarith

/-- Completing the square: `e^{−ct²/2 + bt} = e^{b²/2c} e^{−c(t − b/c)²/2}`. -/
theorem exp_complete {c b : ℝ} (hc : 0 < c) (t : ℝ) :
    Real.exp (-(c * t ^ 2) / 2 + b * t) =
      Real.exp (b ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (t - b / c) ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

theorem int_sh0 {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable fun t : ℝ => Real.exp (-(c / 2) * (t - r) ^ 2) :=
  (integrable_exp_neg_mul_sq (b := c / 2) (by positivity)).comp_sub_right r

theorem int_sh1 {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable fun t : ℝ => (t - r) * Real.exp (-(c / 2) * (t - r) ^ 2) :=
  (integrable_mul_exp_neg_mul_sq (b := c / 2) (by positivity)).comp_sub_right r

theorem int_sh2 {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable fun t : ℝ => (t - r) ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2) :=
  (int_sq_gauss hc).comp_sub_right r

theorem int_abs_gauss {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ℝ => |u| * Real.exp (-(c / 2) * u ^ 2) := by
  refine (integrable_mul_exp_neg_mul_sq (b := c / 2) (by positivity)).abs.congr
    (Eventually.of_forall fun u => ?_)
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)]

theorem int_lin {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable fun t : ℝ => t * Real.exp (-(c / 2) * (t - r) ^ 2) := by
  refine ((int_sh1 hc r).add ((int_sh0 hc r).const_mul r)).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

theorem int_quad {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable fun t : ℝ => t ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2) := by
  refine (((int_sh2 hc r).add ((int_sh1 hc r).const_mul (2 * r))).add
    ((int_sh0 hc r).const_mul (r ^ 2))).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

theorem int_absl {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable fun t : ℝ => |t| * Real.exp (-(c / 2) * (t - r) ^ 2) := by
  refine (int_lin hc r).abs.congr (Eventually.of_forall fun t => ?_)
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- `∫₀^∞ e^{−c(t−r)²/2} ≤ √(2π/c)`. -/
theorem J0_le {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(c / 2) * (t - r) ^ 2) ≤ gw c := by
  refine (setIntegral_le_integral (int_sh0 hc r)
    (Eventually.of_forall fun t => (Real.exp_pos _).le)).trans (le_of_eq ?_)
  rw [integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(c / 2) * t ^ 2)) r, gauss0 hc]

/-- `∫₀^∞ t e^{−c(t−r)²/2} ≤ r√(2π/c) + 2/c` for `r ≥ 0`. -/
theorem J1_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c / 2) * (t - r) ^ 2) ≤ r * gw c + 2 / c := by
  have hA : Integrable fun t : ℝ => |t - r| * Real.exp (-(c / 2) * (t - r) ^ 2) :=
    (int_abs_gauss hc).comp_sub_right r
  calc ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c / 2) * (t - r) ^ 2)
      ≤ ∫ t in Ioi (0 : ℝ), |t| * Real.exp (-(c / 2) * (t - r) ^ 2) :=
        setIntegral_mono_on (int_lin hc r).integrableOn (int_absl hc r).integrableOn
          measurableSet_Ioi fun t _ =>
            mul_le_mul_of_nonneg_right (le_abs_self t) (Real.exp_pos _).le
    _ ≤ ∫ t : ℝ, |t| * Real.exp (-(c / 2) * (t - r) ^ 2) :=
        setIntegral_le_integral (int_absl hc r) (Eventually.of_forall fun t => by positivity)
    _ ≤ ∫ t : ℝ, (|t - r| * Real.exp (-(c / 2) * (t - r) ^ 2) +
          r * Real.exp (-(c / 2) * (t - r) ^ 2)) := by
        refine integral_mono (int_absl hc r) (hA.add ((int_sh0 hc r).const_mul r)) fun t => ?_
        have h1 : |t| ≤ |t - r| + r := by
          have := abs_sub_abs_le_abs_sub t r
          rw [abs_of_nonneg hr] at this
          linarith
        have := Real.exp_pos (-(c / 2) * (t - r) ^ 2)
        simp only
        nlinarith
    _ = r * gw c + 2 / c := by
        rw [integral_add hA ((int_sh0 hc r).const_mul r), integral_const_mul,
          integral_sub_right_eq_self (fun t : ℝ => |t| * Real.exp (-(c / 2) * t ^ 2)) r,
          integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(c / 2) * t ^ 2)) r,
          gauss1abs hc, gauss0 hc]
        ring

/-- `∫₀^∞ t² e^{−c(t−r)²/2} ≤ r²√(2π/c) + √(2π/c)/c`. -/
theorem J2_le {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2) ≤ r ^ 2 * gw c + gw c / c := by
  refine (setIntegral_le_integral (int_quad hc r)
    (Eventually.of_forall fun t => by positivity)).trans (le_of_eq ?_)
  have e : (fun t : ℝ => t ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2)) = fun t =>
      (t - r) ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2) +
        (2 * r) * ((t - r) * Real.exp (-(c / 2) * (t - r) ^ 2)) +
          r ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2) := by
    funext t
    ring
  have hAB : Integrable fun t : ℝ => (t - r) ^ 2 * Real.exp (-(c / 2) * (t - r) ^ 2) +
      (2 * r) * ((t - r) * Real.exp (-(c / 2) * (t - r) ^ 2)) :=
    (int_sh2 hc r).add ((int_sh1 hc r).const_mul (2 * r))
  rw [e, integral_add hAB ((int_sh0 hc r).const_mul (r ^ 2)),
    integral_add (int_sh2 hc r) ((int_sh1 hc r).const_mul (2 * r)), integral_const_mul,
    integral_const_mul,
    integral_sub_right_eq_self (fun t : ℝ => t ^ 2 * Real.exp (-(c / 2) * t ^ 2)) r,
    integral_sub_right_eq_self (fun t : ℝ => t * Real.exp (-(c / 2) * t ^ 2)) r,
    integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(c / 2) * t ^ 2)) r,
    gauss2 hc, gauss1, gauss0 hc]
  ring

/-- **LINK [Moment1] PROVED** (Bernoulli `t^m ≤ (1 − m) + mt`, completing the square). -/
theorem moment1_holds : Moment1 := by
  intro m c b hm0 hm1 hc hb
  have hr : 0 ≤ b / c := div_nonneg hb hc.le
  have hA := Real.exp_pos (b ^ 2 / (2 * c))
  have hint : IntegrableOn (fun t : ℝ => Real.exp (b ^ 2 / (2 * c)) *
      ((1 - m) * Real.exp (-(c / 2) * (t - b / c) ^ 2) +
        m * (t * Real.exp (-(c / 2) * (t - b / c) ^ 2)))) (Ioi 0) :=
    ((((int_sh0 hc (b / c)).const_mul (1 - m)).add
      ((int_lin hc (b / c)).const_mul m)).const_mul _).integrableOn
  calc rayInt m c b
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (b ^ 2 / (2 * c)) *
          ((1 - m) * Real.exp (-(c / 2) * (t - b / c) ^ 2) +
            m * (t * Real.exp (-(c / 2) * (t - b / c) ^ 2))) := by
        refine setIntegral_mono_on (integrableOn_ray (by linarith) hc) hint measurableSet_Ioi
          fun t ht => ?_
        have ht0 : 0 < t := ht
        have hB : t ^ m ≤ (1 - m) + m * t := by
          have := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hm0 hm1
          rw [show 1 + (t - 1) = t by ring] at this
          linarith
        have hE := Real.exp_pos (-(c / 2) * (t - b / c) ^ 2)
        rw [exp_complete hc]
        calc t ^ m * (Real.exp (b ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (t - b / c) ^ 2))
            = Real.exp (b ^ 2 / (2 * c)) * (t ^ m * Real.exp (-(c / 2) * (t - b / c) ^ 2)) := by
              ring
          _ ≤ Real.exp (b ^ 2 / (2 * c)) *
                (((1 - m) + m * t) * Real.exp (-(c / 2) * (t - b / c) ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hE.le) hA.le
          _ = _ := by ring
    _ = Real.exp (b ^ 2 / (2 * c)) *
          ((1 - m) * ∫ t in Ioi (0 : ℝ), Real.exp (-(c / 2) * (t - b / c) ^ 2)) +
        Real.exp (b ^ 2 / (2 * c)) *
          (m * ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c / 2) * (t - b / c) ^ 2)) := by
        rw [integral_const_mul, integral_add ((int_sh0 hc (b / c)).const_mul (1 - m)).integrableOn
          ((int_lin hc (b / c)).const_mul m).integrableOn, integral_const_mul,
          integral_const_mul]
        ring
    _ ≤ Real.exp (b ^ 2 / (2 * c)) * ((1 - m) * gw c) +
        Real.exp (b ^ 2 / (2 * c)) * (m * (b / c * gw c + 2 / c)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (J0_le hc _) (by linarith)) hA.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (J1_le hc hr) hm0) hA.le)
    _ = _ := by ring

/-- **LINK [Moment2] PROVED** (`t^m = t·t^{m−1} ≤ (2 − m)t + (m − 1)t²`). -/
theorem moment2_holds : Moment2 := by
  intro m c b hm1 hm2 hc hb
  have hr : 0 ≤ b / c := div_nonneg hb hc.le
  have hA := Real.exp_pos (b ^ 2 / (2 * c))
  have hint : IntegrableOn (fun t : ℝ => Real.exp (b ^ 2 / (2 * c)) *
      ((2 - m) * (t * Real.exp (-(c / 2) * (t - b / c) ^ 2)) +
        (m - 1) * (t ^ 2 * Real.exp (-(c / 2) * (t - b / c) ^ 2)))) (Ioi 0) :=
    ((((int_lin hc (b / c)).const_mul (2 - m)).add
      ((int_quad hc (b / c)).const_mul (m - 1))).const_mul _).integrableOn
  calc rayInt m c b
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (b ^ 2 / (2 * c)) *
          ((2 - m) * (t * Real.exp (-(c / 2) * (t - b / c) ^ 2)) +
            (m - 1) * (t ^ 2 * Real.exp (-(c / 2) * (t - b / c) ^ 2))) := by
        refine setIntegral_mono_on (integrableOn_ray (by linarith) hc) hint measurableSet_Ioi
          fun t ht => ?_
        have ht0 : 0 < t := ht
        have hB : t ^ m ≤ (2 - m) * t + (m - 1) * t ^ 2 := by
          have h1 := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith)
            (p := m - 1) (by linarith) (by linarith)
          rw [show 1 + (t - 1) = t by ring] at h1
          have h2 : t ^ m = t * t ^ (m - 1) := by
            rw [Real.rpow_sub_one ht0.ne']
            field_simp
          rw [h2]
          nlinarith
        have hE := Real.exp_pos (-(c / 2) * (t - b / c) ^ 2)
        rw [exp_complete hc]
        calc t ^ m * (Real.exp (b ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (t - b / c) ^ 2))
            = Real.exp (b ^ 2 / (2 * c)) * (t ^ m * Real.exp (-(c / 2) * (t - b / c) ^ 2)) := by
              ring
          _ ≤ Real.exp (b ^ 2 / (2 * c)) *
                (((2 - m) * t + (m - 1) * t ^ 2) * Real.exp (-(c / 2) * (t - b / c) ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hE.le) hA.le
          _ = _ := by ring
    _ = Real.exp (b ^ 2 / (2 * c)) *
          ((2 - m) * ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c / 2) * (t - b / c) ^ 2)) +
        Real.exp (b ^ 2 / (2 * c)) *
          ((m - 1) * ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-(c / 2) * (t - b / c) ^ 2)) := by
        rw [integral_const_mul, integral_add ((int_lin hc (b / c)).const_mul (2 - m)).integrableOn
          ((int_quad hc (b / c)).const_mul (m - 1)).integrableOn, integral_const_mul,
          integral_const_mul]
        ring
    _ ≤ Real.exp (b ^ 2 / (2 * c)) * ((2 - m) * (b / c * gw c + 2 / c)) +
        Real.exp (b ^ 2 / (2 * c)) * ((m - 1) * ((b / c) ^ 2 * gw c + gw c / c)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (J1_le hc hr) (by linarith)) hA.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (J2_le hc _) (by linarith)) hA.le)
    _ = _ := by ring

end Principia.Common.TernaryGoldbach.S4
