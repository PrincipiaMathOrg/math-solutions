/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

/-!
# `Γ` on vertical lines: explicit exponential decay, with numerals

Mathlib has no bound on `|Γ(σ + iy)|` along any vertical line. This file proves the ones the
Mellin decay of `η₊,₂` needs (`HelfMajMalDecay`), all with explicit numerals, from three facts:

* **the critical line** (`gamma_half_norm_le`): `|Γ(½ + iy)|² = π/cosh(πy)`, so
  `|Γ(½ + iy)| ≤ √(2π)e^{−π|y|/2}`. PORTED from PrimeNumberTheoremAnd
  (`Mathlib/Analysis/SpecialFunctions/Gamma/CriticalLineDecay.lean`, `gamma_half_vertical_norm_sq`
  and `gamma_half_vertical_norm_le_exp`): Euler's reflection plus `Γ(s̄) = conj Γ(s)`;
* **the Beta comparison** (`gamma_beta_cmp`): for `0 < σ < c`,
  `|Γ(σ + iy)|·Γ(c) ≤ Γ(σ)·|Γ(c + iy)|`, because `Γ(s)Γ(c−σ) = Γ(c + iy)B(s, c − σ)` and
  `|B(σ + iy, c − σ)| ≤ B(σ, c − σ)` (the integrand's modulus does not depend on `y`);
* **convexity of `Γ` on `(0, ∞)`** (`Γ ≤ 1` on `[1, 2]`, `Γ ≤ √π` on `[½, 3/2]`).

Consequences (`y = Im z`):
* `gamma_le_strip`: `|Γ(z)| ≤ 2(3/2 + |y|)(1/2 + |y|)√(2π)e^{−π|y|/2}` for `½ ≤ Re z ≤ 2`;
* `gamma_le_one_three_half`: `|Γ(z)| ≤ (2/√π)(1/2 + |y|)√(2π)e^{−π|y|/2}` for `1 ≤ Re z < 3/2`;
* `deriv_gamma_le`: `|Γ'(z)| ≤ 4(2 + |y|)(1 + |y|)√(2π)e^{−π(|y| − 1/2)/2}` for `1 ≤ Re z ≤ 3/2`
  (Cauchy's estimate on the circle of radius `½`,
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`).

They lose only polynomial factors against Stirling; DLMF 5.6.9 / 5.11.2 are not needed.
-/

namespace Principia.Common.TernaryGoldbach.HP

open Complex Set Metric

/-! ## (1) The critical line (ported from PrimeNumberTheoremAnd, `CriticalLineDecay.lean`) -/

theorem sin_pi_half_add_mul_I (τ : ℝ) :
    Complex.sin (Real.pi * (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)) =
      (Real.cosh (Real.pi * τ) : ℂ) := by
  have harg : (Real.pi : ℂ) * (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)
      = (Real.pi / 2 : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * I := by
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
    ring_nf
  rw [harg]
  simp [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
    Complex.sin_mul_I, Complex.ofReal_cosh]

/-- **`‖Γ(½ + iτ)‖² = π/cosh(πτ)`** (ported). -/
theorem gamma_half_norm_sq (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * τ) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I
  have hconj : (starRingEnd ℂ) z = 1 - z := by
    apply Complex.ext <;> norm_num [z, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hleft :
      Complex.Gamma z * Complex.Gamma (1 - z) = ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsin : Complex.sin (Real.pi * z) = (Real.cosh (Real.pi * τ) : ℂ) := by
    simpa [z] using sin_pi_half_add_mul_I τ
  have hcomplex :
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) =
        ((Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
    calc
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ)
          = Complex.Gamma z * Complex.Gamma (1 - z) := hleft.symm
      _ = (Real.pi : ℂ) / Complex.sin (Real.pi * z) := Complex.Gamma_mul_Gamma_one_sub z
      _ = ((Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
        simp [hsin, Complex.ofReal_div]
  simpa [z] using Complex.ofReal_injective hcomplex

theorem exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- **`‖Γ(½ + iτ)‖ ≤ √(2π)e^{−π|τ|/2}`** (ported). -/
theorem gamma_half_norm_le (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)) := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  have hrhs_sq :
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) ^ 2 =
        2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), sq, ← Real.exp_add]
    ring_nf
  rw [hrhs_sq, gamma_half_norm_sq]
  have hxabs : |Real.pi * τ| = Real.pi * |τ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcosh_lower : Real.exp (Real.pi * |τ|) / 2 ≤ Real.cosh (Real.pi * τ) := by
    simpa [hxabs] using exp_abs_div_two_le_cosh (Real.pi * τ)
  have hden_pos : 0 < Real.exp (Real.pi * |τ|) / 2 := by positivity
  have hinv : (Real.cosh (Real.pi * τ))⁻¹ ≤ (Real.exp (Real.pi * |τ|) / 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hcosh_lower
  have hinv_eval : (Real.exp (Real.pi * |τ|) / 2)⁻¹ = 2 * Real.exp (-(Real.pi * |τ|)) := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, ← Real.exp_neg]
  calc Real.pi / Real.cosh (Real.pi * τ) = Real.pi * (Real.cosh (Real.pi * τ))⁻¹ := by ring
    _ ≤ Real.pi * (Real.exp (Real.pi * |τ|) / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
    _ = 2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
        rw [hinv_eval]
        ring

/-! ## (2) The lines `Re = 3/2` and `Re = 5/2` -/

/-- `‖a + iy‖ ≤ a + |y|` for `a ≥ 0`. -/
theorem norm_add_mul_I_le {a y : ℝ} (ha : 0 ≤ a) : ‖(a : ℂ) + (y : ℂ) * I‖ ≤ a + |y| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- **`‖Γ(3/2 + iy)‖ ≤ (1/2 + |y|)√(2π)e^{−π|y|/2}`** (`Γ(z + 1) = zΓ(z)`). -/
theorem gamma_three_half_le (y : ℝ) :
    ‖Complex.Gamma (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      (1 / 2 + |y|) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |y| / 2))) := by
  have hz : (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have e : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I = (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) + 1 := by
    push_cast
    ring
  rw [e, Complex.Gamma_add_one _ hz, norm_mul]
  exact mul_le_mul (norm_add_mul_I_le (by norm_num)) (gamma_half_norm_le y) (norm_nonneg _)
    (by positivity)

/-- **`‖Γ(5/2 + iy)‖ ≤ (3/2 + |y|)(1/2 + |y|)√(2π)e^{−π|y|/2}`**. -/
theorem gamma_five_half_le (y : ℝ) :
    ‖Complex.Gamma (((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      (3 / 2 + |y|) * ((1 / 2 + |y|) *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |y| / 2)))) := by
  have hz : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have e : ((5 / 2 : ℝ) : ℂ) + (y : ℂ) * I = (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) + 1 := by
    push_cast
    ring
  rw [e, Complex.Gamma_add_one _ hz, norm_mul]
  exact mul_le_mul (norm_add_mul_I_le (by norm_num)) (gamma_three_half_le y) (norm_nonneg _)
    (by positivity)

/-! ## (3) The Beta comparison -/

/-- `‖Γ(r)‖ = Γ(r)` for real `r > 0`. -/
theorem norm_gamma_ofReal {r : ℝ} (hr : 0 < r) : ‖Complex.Gamma (r : ℂ)‖ = Real.Gamma r := by
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos hr)]

/-- **`|B(σ + iy, u)| ≤ B(σ, u)`** for real `u > 0`: the modulus of the integrand does not see
`y`. -/
theorem norm_beta_le (σ y u : ℝ) :
    ‖Complex.betaIntegral ((σ : ℂ) + (y : ℂ) * I) (u : ℂ)‖ ≤
      ‖Complex.betaIntegral (σ : ℂ) (u : ℂ)‖ := by
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have hpt : ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖(x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * I - 1) * (1 - (x : ℂ)) ^ ((u : ℂ) - 1)‖ =
        x ^ (σ - 1) * (1 - x) ^ (u - 1) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have e1 : ((σ : ℂ) + (y : ℂ) * I - 1).re = σ - 1 := by simp
    have e2 : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    have e3 : ((u : ℂ) - 1) = ((u - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, ← Complex.ofReal_cpow hx1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx1 _)]
  have hreal : ∀ x ∈ Ioc (0 : ℝ) 1,
      (x : ℂ) ^ ((σ : ℂ) - 1) * (1 - (x : ℂ)) ^ ((u : ℂ) - 1) =
        ((x ^ (σ - 1) * (1 - x) ^ (u - 1) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
    have e2 : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    have e3 : ((u : ℂ) - 1) = ((u - 1 : ℝ) : ℂ) := by push_cast; ring
    have e4 : ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e2, e3, e4, ← Complex.ofReal_cpow hx0, ← Complex.ofReal_cpow hx1, Complex.ofReal_mul]
  calc ‖∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * I - 1) * (1 - (x : ℂ)) ^ ((u : ℂ) - 1)‖
      ≤ ∫ x in Ioc (0 : ℝ) 1,
          ‖(x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * I - 1) * (1 - (x : ℂ)) ^ ((u : ℂ) - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Ioc (0 : ℝ) 1, x ^ (σ - 1) * (1 - x) ^ (u - 1) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt
    _ = ‖∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ ((σ : ℂ) - 1) * (1 - (x : ℂ)) ^ ((u : ℂ) - 1)‖ := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hreal, integral_complex_ofReal,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun x hx => ?_
        exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (by linarith [hx.2]) _)

/-- **The Beta comparison**: `‖Γ(σ + iy)‖·Γ(c) ≤ Γ(σ)·‖Γ(c + iy)‖` for `0 < σ < c`. -/
theorem gamma_beta_cmp {σ c y : ℝ} (hσ : 0 < σ) (hσc : σ < c) :
    ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I)‖ * Real.Gamma c ≤
      Real.Gamma σ * ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ := by
  have hu : 0 < c - σ := by linarith
  have hs : 0 < ((σ : ℂ) + (y : ℂ) * I).re := by simp [hσ]
  have hu' : 0 < ((c - σ : ℝ) : ℂ).re := by simp [hu]
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral hs hu'
  have e1 : (σ : ℂ) + (y : ℂ) * I + ((c - σ : ℝ) : ℂ) = (c : ℂ) + (y : ℂ) * I := by
    push_cast
    ring
  rw [e1] at h1
  have h2 := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (σ : ℂ)) (by simp [hσ]) hu'
  have e2 : (σ : ℂ) + ((c - σ : ℝ) : ℂ) = (c : ℂ) := by
    push_cast
    ring
  rw [e2] at h2
  have hB := norm_beta_le σ y (c - σ)
  have n1 := congrArg norm h1
  have n2 := congrArg norm h2
  rw [norm_mul, norm_mul] at n1 n2
  rw [norm_gamma_ofReal hσ, norm_gamma_ofReal hu, norm_gamma_ofReal (by linarith : 0 < c)] at n2
  rw [norm_gamma_ofReal hu] at n1
  have hGu := Real.Gamma_pos_of_pos hu
  have hGc := Real.Gamma_pos_of_pos (by linarith : 0 < c)
  -- ‖Γ(s)‖Γ(c−σ) = ‖Γ(c+iy)‖‖B(s)‖ ≤ ‖Γ(c+iy)‖‖B(σ)‖ = ‖Γ(c+iy)‖Γ(σ)Γ(c−σ)/Γ(c)
  have key : ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I)‖ * Real.Gamma (c - σ) * Real.Gamma c ≤
      Real.Gamma σ * ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ * Real.Gamma (c - σ) := by
    rw [n1]
    have := mul_le_mul_of_nonneg_left hB (norm_nonneg (Complex.Gamma ((c : ℂ) + (y : ℂ) * I)))
    have h3 : ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ *
        ‖Complex.betaIntegral (σ : ℂ) ((c - σ : ℝ) : ℂ)‖ * Real.Gamma c =
          Real.Gamma σ * ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ * Real.Gamma (c - σ) := by
      rw [show Real.Gamma σ * ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ * Real.Gamma (c - σ) =
        ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ * (Real.Gamma σ * Real.Gamma (c - σ)) by ring,
        n2]
      ring
    nlinarith [norm_nonneg (Complex.Gamma ((c : ℂ) + (y : ℂ) * I))]
  have e3 : ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I)‖ * Real.Gamma (c - σ) * Real.Gamma c =
      (‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I)‖ * Real.Gamma c) * Real.Gamma (c - σ) := by ring
  rw [e3] at key
  exact le_of_mul_le_mul_right key hGu

/-! ## (4) Real `Γ` on `[½, 2]` -/

theorem gamma_le_one_of_mem {a : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 2) : Real.Gamma a ≤ 1 := by
  have h := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (show (0 : ℝ) ≤ 2 - a by linarith)
    (show (0 : ℝ) ≤ a - 1 by linarith) (by ring)
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Real.Gamma_one, Real.Gamma_two,
    show (2 - a) * 1 + (a - 1) * 2 = a by ring] at h
  linarith

theorem gamma_le_sqrt_pi_of_mem {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 3 / 2) :
    Real.Gamma a ≤ Real.sqrt Real.pi := by
  have h := Real.convexOn_Gamma.2 (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show (0 : ℝ) ≤ 3 / 2 - a by linarith)
    (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (by ring)
  have g32 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Real.Gamma_one_half_eq, g32,
    show (3 / 2 - a) * (1 / 2) + (a - 1 / 2) * (3 / 2) = a by ring] at h
  have hp : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  nlinarith

theorem gamma_three_half_eq : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

theorem gamma_five_half_eq : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    gamma_three_half_eq]
  ring

/-! ## (5) The strip `½ ≤ Re ≤ 2` and the band `1 ≤ Re < 3/2` -/

/-- `√π ≥ 1.77`. -/
theorem sqrt_pi_ge : (1.77 : ℝ) ≤ Real.sqrt Real.pi :=
  (Real.le_sqrt (by norm_num) Real.pi_pos.le).mpr (by nlinarith [Real.pi_gt_d2])

/-- **`‖Γ(a + iv)‖ ≤ 2(3/2 + |v|)(1/2 + |v|)√(2π)e^{−π|v|/2}`** for `½ ≤ a ≤ 2`. -/
theorem gamma_le_strip {a v : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 2) :
    ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤ 2 * ((3 / 2 + |v|) * ((1 / 2 + |v|) *
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v| / 2))))) := by
  have hE : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v| / 2)) := by positivity
  have hsp := sqrt_pi_ge
  rcases lt_or_ge a (3 / 2) with h | h
  · have hc := gamma_beta_cmp (y := v) (by linarith : 0 < a) h
    rw [gamma_three_half_eq] at hc
    have hG := gamma_le_sqrt_pi_of_mem h1 h.le
    have h3 := gamma_three_half_le v
    have hGa : 0 ≤ Real.Gamma a := (Real.Gamma_pos_of_pos (by linarith)).le
    have p := mul_le_mul hG h3 (norm_nonneg _) (Real.sqrt_nonneg _)
    have hn : ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ * (Real.sqrt Real.pi / 2) ≤
        Real.sqrt Real.pi * ((1 / 2 + |v|) * (Real.sqrt (2 * Real.pi) *
          Real.exp (-(Real.pi * |v| / 2)))) := by
      have := mul_le_mul_of_nonneg_left h3 hGa
      nlinarith
    have hv1 : 1 ≤ 3 / 2 + |v| := by linarith [abs_nonneg v]
    have hX : 0 ≤ (1 / 2 + |v|) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v| / 2))) :=
      by positivity
    have hn2 : ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        2 * ((1 / 2 + |v|) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v| / 2)))) := by
      have hsp0 : 0 < Real.sqrt Real.pi := by linarith
      nlinarith
    have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX hv1) (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  · have hc := gamma_beta_cmp (y := v) (by linarith : 0 < a) (by linarith : a < 5 / 2)
    rw [gamma_five_half_eq] at hc
    have hG := gamma_le_one_of_mem (by linarith) h2
    have h5 := gamma_five_half_le v
    have hGa : 0 ≤ Real.Gamma a := (Real.Gamma_pos_of_pos (by linarith)).le
    have hX : 0 ≤ (3 / 2 + |v|) * ((1 / 2 + |v|) *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v| / 2)))) := by positivity
    have hn : ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ * (3 / 4 * Real.sqrt Real.pi) ≤
        (3 / 2 + |v|) * ((1 / 2 + |v|) *
          (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v| / 2)))) := by
      have := mul_le_mul hG h5 (norm_nonneg _) zero_le_one
      linarith
    nlinarith

/-- **`‖Γ(a + iy)‖ ≤ (2/√π)(1/2 + |y|)√(2π)e^{−π|y|/2}`** for `1 ≤ a < 3/2`. -/
theorem gamma_le_one_three_half {a y : ℝ} (h1 : 1 ≤ a) (h2 : a < 3 / 2) :
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ≤ 2 / Real.sqrt Real.pi * ((1 / 2 + |y|) *
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |y| / 2)))) := by
  have hc := gamma_beta_cmp (y := y) (by linarith : 0 < a) h2
  rw [gamma_three_half_eq] at hc
  have hG := gamma_le_one_of_mem h1 (by linarith)
  have h3 := gamma_three_half_le y
  have hsp0 : 0 < Real.sqrt Real.pi := by linarith [sqrt_pi_ge]
  have hn : ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ * (Real.sqrt Real.pi / 2) ≤
      (1 / 2 + |y|) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |y| / 2))) := by
    have := mul_le_mul hG h3 (norm_nonneg _) zero_le_one
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hsp0]
  nlinarith

/-! ## (6) `Γ'` by Cauchy's estimate -/

/-- `Γ` is differentiable on `Re > 0`. -/
theorem diffAt_gamma_re_pos {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.Gamma w := by
  refine Complex.differentiableAt_Gamma w fun m hm => ?_
  have := congrArg Complex.re hm
  simp at this
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **`‖Γ'(a + iy)‖ ≤ 4(2 + |y|)(1 + |y|)√(2π)e^{−π(|y| − 1/2)/2}`** for `1 ≤ a ≤ 3/2`. -/
theorem deriv_gamma_le {a y : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 3 / 2) :
    ‖deriv Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ≤ 4 * ((2 + |y|) * ((1 + |y|) *
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * (|y| - 1 / 2) / 2))))) := by
  set z : ℂ := (a : ℂ) + (y : ℂ) * I with hz
  have hzre : z.re = a := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hd : DiffContOnCl ℂ Complex.Gamma (ball z (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z (by norm_num)]
    intro w hw
    refine (diffAt_gamma_re_pos ?_).differentiableWithinAt
    rw [mem_closedBall, Complex.dist_eq] at hw
    have := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re, hzre] at this
    have := (abs_le.mp (this.trans hw)).1
    linarith
  have hC : ∀ w ∈ sphere z (1 / 2), ‖Complex.Gamma w‖ ≤ 2 * ((2 + |y|) * ((1 + |y|) *
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * (|y| - 1 / 2) / 2))))) := by
    intro w hw
    rw [mem_sphere, Complex.dist_eq] at hw
    have hre := Complex.abs_re_le_norm (w - z)
    have him := Complex.abs_im_le_norm (w - z)
    rw [hw, Complex.sub_re, hzre] at hre
    rw [hw, Complex.sub_im, hzim] at him
    have hre' := abs_le.mp hre
    have him' := abs_le.mp him
    have hw_eq : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * I := (Complex.re_add_im w).symm
    have hs := gamma_le_strip (v := w.im) (a := w.re) (by linarith) (by linarith)
    rw [← hw_eq] at hs
    have hv1 : |w.im| ≤ |y| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub w.im y
      have h3 : |w.im - y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hv2 : |y| - 1 / 2 ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub y w.im
      have h3 : |y - w.im| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hE : Real.exp (-(Real.pi * |w.im| / 2)) ≤ Real.exp (-(Real.pi * (|y| - 1 / 2) / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hs2 : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hA : 3 / 2 + |w.im| ≤ 2 + |y| := by linarith
    have hB : 1 / 2 + |w.im| ≤ 1 + |y| := by linarith
    have p1 := mul_le_mul_of_nonneg_left hE hs2
    have p2 := mul_le_mul hB p1 (by positivity) (by positivity)
    have p3 := mul_le_mul hA p2 (by positivity) (by positivity)
    linarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hd hC
  rw [show (2 * ((2 + |y|) * ((1 + |y|) * (Real.sqrt (2 * Real.pi) *
    Real.exp (-(Real.pi * (|y| - 1 / 2) / 2)))))) / (1 / 2) = 4 * ((2 + |y|) * ((1 + |y|) *
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * (|y| - 1 / 2) / 2))))) by ring] at this
  exact this

end Principia.Common.TernaryGoldbach.HP
