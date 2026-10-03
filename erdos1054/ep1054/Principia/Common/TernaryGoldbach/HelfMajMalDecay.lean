/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajBandRep
import Principia.Common.TernaryGoldbach.HelfMajMalNorms

set_option autoImplicit false

/-!
# `HM.MalDecay` REPLACED by a proved `MalDecayL` (`5·10⁵ × fmal`); Prop 1.5 re-derived

**`malDecayL_holds`**: for `x ≥ 10¹²`, `0 < Re s < 1`, `|Im s| ≥ 450`,
`|M η₊,₂(s)| ≤ 5·10⁵·fmal(x, |Im s|) = 5·10⁶(log x + 10)e^{−0.7(|Im s| − 400)}`.

## The route (no DLMF, no Stirling)

* `η₊,₂(t) = h_H(t)·h_H(t)·g(t)`, `g(t) = t²e^{−t²}log(xt)`; `HP.norm_mellin_hH_mul_le` twice:
  each factor `h_H = (1/2π)∫_{−200}^{200}A(r)t^{ir}dr` shifts the Mellin variable by `|r| ≤ 200`
  and costs `(1/2π)·400·7.172`. So `|Mη₊,₂(s)| ≤ 456.6²·sup |Mg(s + iρ)|` over `|ρ| ≤ 400`.
* `Mg(w) = (log x)·Γ(z)/2 + Γ'(z)/4`, `z = (w + 2)/2` (`mellin_g_eq`: Mathlib's
  `mellin_cpow_smul`, `mellin_comp_rpow` at `a = 2`, `GammaIntegral_eq_mellin`, and
  `hasDerivAt_GammaIntegral` for the `log` term). `Re z = (σ + 2)/2 ∈ (1, 3/2)` and
  `|Im z| ≥ (|Im s| − 400)/2 ≥ 25`.
* `HP.gamma_le_one_three_half`, `HP.deriv_gamma_le` (`HelfMajGammaV`) and
  `(1/2 + u) ≤ 2e^{0.17u}`, `(2 + u)(1 + u) ≤ 27e^{0.17u}` for `u ≥ 25` (Taylor) give
  `|Mg| ≤ (2.8285 log x + 184.1)e^{−1.4u}`; `π/2 − 0.17 ≥ 1.4`.
* Total `≤ (5.9·10⁵ log x + 3.84·10⁷)e^{−0.7(|Im s| − 400)} ≤ 5·10⁵·fmal` (margins `8.5×`, `1.3×`).

**Why the factor `5·10⁵` and why it does not matter.** The crude ingredients — `|A(r)| ≤ 7.172`
uniformly (truth `2.02` at `r = 0`, decaying like `r⁻²`), Cauchy's estimate for `Γ'` — leave the
proved bound a factor `5.9·10⁴` (on `log x`) and `3.8·10⁵` (on the constant) above `fmal` itself.
`MalDecay` enters Prop 1.5 only through the high-zero
tail `Tm`, whose budget is `1.05·10⁻⁶ log x` (the room left by `MalMain`'s `3.9·10⁻⁶`): at
`5·10⁵·fmal`, `MalTailInt` scales to `5·10⁻⁷ log x` (`malTailIntL_of`) and
`Tm ≤ 7·10⁻⁷ log x` (`malheur_closeL2`). Prop 1.5's retyped `5·10⁻⁶ + 500/√x` still closes.
-/

namespace Principia.Common.TernaryGoldbach.HP

open MeasureTheory Set Filter

/-! ## (1) The Mellin transform of `t²e^{−t²}` and of `t²e^{−t²}log t` -/

theorem mellin_congr {f g : ℝ → ℂ} {s : ℂ} (h : ∀ t : ℝ, 0 < t → f t = g t) :
    mellin f s = mellin g s :=
  setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [h t ht]

/-- **`M(t²e^{−t²})(w) = Γ((w + 2)/2)/2`** for `Re w > −2`. -/
theorem mellin_t2_gauss {w : ℂ} (hw : -2 < w.re) :
    mellin (fun t => ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)) w =
      Complex.Gamma ((w + 2) / 2) / 2 := by
  have e1 : mellin (fun t => ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)) w =
      mellin (fun t => (t : ℂ) ^ (2 : ℂ) • (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ))
        (t ^ (2 : ℝ))) w := by
    refine mellin_congr fun t _ => ?_
    rw [smul_eq_mul, Real.rpow_two, Complex.cpow_two]
    push_cast
    ring
  have hz : 0 < ((w + 2) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.normSq_ofNat]
    norm_num
    linarith
  rw [e1, mellin_cpow_smul, mellin_comp_rpow (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) (w + 2) 2,
    ← Complex.GammaIntegral_eq_mellin, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num,
    ← Complex.Gamma_eq_integral hz, Complex.real_smul]
  norm_num
  ring

/-- `Γ = ∫` near any point of the right half-plane. -/
theorem gamma_eventuallyEq {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma =ᶠ[nhds z] Complex.GammaIntegral := by
  have ho : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho.mem_nhds hz] with s hs
  exact Complex.Gamma_eq_integral hs

/-- **`M(t²e^{−t²}log t)(w) = Γ'((w + 2)/2)/4`** for `Re w > −2`. -/
theorem mellin_t2_gauss_log {w : ℂ} (hw : -2 < w.re) :
    mellin (fun t => ((t ^ 2 * Real.exp (-t ^ 2) * Real.log t : ℝ) : ℂ)) w =
      deriv Complex.Gamma ((w + 2) / 2) / 4 := by
  have hz : 0 < ((w + 2) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.normSq_ofNat]
    norm_num
    linarith
  have e1 : mellin (fun t => ((t ^ 2 * Real.exp (-t ^ 2) * Real.log t : ℝ) : ℂ)) w =
      mellin (fun t => (1 / 2 : ℂ) • ((t : ℂ) ^ (2 : ℂ) •
        (fun u : ℝ => ((Real.log u * Real.exp (-u) : ℝ) : ℂ)) (t ^ (2 : ℝ)))) w := by
    refine mellin_congr fun t ht => ?_
    rw [smul_eq_mul, smul_eq_mul, Real.rpow_two, Complex.cpow_two]
    beta_reduce
    rw [Real.log_pow]
    push_cast
    ring
  rw [e1, mellin_const_smul, mellin_cpow_smul,
    mellin_comp_rpow (fun u : ℝ => ((Real.log u * Real.exp (-u) : ℝ) : ℂ)) (w + 2) 2,
    show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  have hD := (Complex.hasDerivAt_GammaIntegral hz).congr_of_eventuallyEq (gamma_eventuallyEq hz)
  rw [hD.deriv]
  have e2 : mellin (fun u : ℝ => ((Real.log u * Real.exp (-u) : ℝ) : ℂ)) ((w + 2) / 2) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((w + 2) / 2 - 1) * (Real.log t * Real.exp (-t)) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [smul_eq_mul]
    push_cast
    ring
  rw [e2, Complex.real_smul, smul_eq_mul]
  norm_num
  ring

/-! ## (2) `M g` for `g(t) = t²e^{−t²}log(xt)` -/

/-- `g(t) = t²e^{−t²}log(xt)`, as a complex function. -/
noncomputable def gx (x t : ℝ) : ℂ := ((t ^ 2 * Real.exp (-t ^ 2) * Real.log (x * t) : ℝ) : ℂ)

theorem measurable_gx (x : ℝ) : Measurable (gx x) := by
  unfold gx
  exact Complex.measurable_ofReal.comp (((measurable_id.pow_const 2).mul
    (Real.measurable_exp.comp ((measurable_id.pow_const 2).neg))).mul
      (Real.measurable_log.comp (measurable_const.mul measurable_id)))

/-- `t^{σ−1}·t^k e^{−t²}` is integrable for `σ > 0`. -/
theorem int_rpow_gauss {σ : ℝ} (k : ℕ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1 + (k : ℕ)) * Real.exp (-t ^ 2)) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := σ - 1 + (k : ℕ))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)).congr_fun (fun t _ => by
      beta_reduce
      rw [show -(1 : ℝ) * t ^ 2 = -t ^ 2 by ring]) measurableSet_Ioi

/-- **`t^{σ−1}|g(t)| ∈ L¹`**, with the envelope `C·t²e^{−t²}(log x + t + 1/t)`. -/
theorem int_env_gx {x σ C : ℝ} (hσ : 0 < σ) {φ : ℝ → ℂ} (hφm : Measurable φ)
    (hφ : ∀ t, 0 < t → ‖φ t‖ ≤ C * (t ^ 2 * Real.exp (-t ^ 2) * (Real.log x + (t + 1 / t)))) :
    IntegrableOn (fun t => t ^ (σ - 1) * ‖φ t‖) (Ioi 0) := by
  have hg := (((int_rpow_gauss 2 hσ).const_mul (C * Real.log x)).add
    ((int_rpow_gauss 3 hσ).const_mul C)).add ((int_rpow_gauss 1 hσ).const_mul C)
  refine int_of_le hg ((measurable_id.pow_const _).mul hφm.norm).aestronglyMeasurable
    fun t ht => ?_
  simp only [Pi.add_apply]
  have hp : 0 < t ^ (σ - 1) := Real.rpow_pos_of_pos ht _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.le (norm_nonneg _))]
  have h := mul_le_mul_of_nonneg_left (hφ t ht) hp.le
  have e2 : t ^ (σ - 1 + ((2 : ℕ) : ℝ)) = t ^ (σ - 1) * t ^ 2 := by
    rw [Real.rpow_add ht, Real.rpow_natCast]
  have e3 : t ^ (σ - 1 + ((3 : ℕ) : ℝ)) = t ^ (σ - 1) * t ^ 3 := by
    rw [Real.rpow_add ht, Real.rpow_natCast]
  have e1 : t ^ (σ - 1 + ((1 : ℕ) : ℝ)) = t ^ (σ - 1) * t := by
    rw [Real.rpow_add ht, Nat.cast_one, Real.rpow_one]
  rw [e1, e2, e3]
  have e : t ^ (σ - 1) * (C * (t ^ 2 * Real.exp (-t ^ 2) * (Real.log x + (t + 1 / t)))) =
      C * Real.log x * (t ^ (σ - 1) * t ^ 2 * Real.exp (-t ^ 2)) +
        C * (t ^ (σ - 1) * t ^ 3 * Real.exp (-t ^ 2)) +
          C * (t ^ (σ - 1) * t * Real.exp (-t ^ 2)) := by
    field_simp
    ring
  linarith

/-- The envelope of `g`. -/
theorem norm_gx_le {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) :
    ‖gx x t‖ ≤ 1 * (t ^ 2 * Real.exp (-t ^ 2) * (Real.log x + (t + 1 / t))) := by
  unfold gx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), one_mul]
  exact mul_le_mul_of_nonneg_left (abs_log_mul_le hx ht) (by positivity)

/-- `t^{w−1}·t²e^{−t²}` is integrable for `Re w > 0`. -/
theorem mellinConv_t2 {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (fun t => ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)) w := by
  unfold MellinConvergent
  refine (int_rpow_gauss 2 hw).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  · exact ((Complex.measurable_ofReal.pow_const _).smul (Complex.measurable_ofReal.comp
      ((measurable_id.pow_const 2).mul (Real.measurable_exp.comp
        (measurable_id.pow_const 2).neg)))).aestronglyMeasurable
  · have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_add ht0,
      Real.rpow_natCast]
    exact le_of_eq (by ring)

/-- `t^{w−1}·t²e^{−t²}log t` is integrable for `Re w > 0`. -/
theorem mellinConv_t2_log {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (fun t => ((t ^ 2 * Real.exp (-t ^ 2) * Real.log t : ℝ) : ℂ)) w := by
  unfold MellinConvergent
  refine ((int_rpow_gauss 3 hw).add (int_rpow_gauss 1 hw)).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact ((Complex.measurable_ofReal.pow_const _).smul (Complex.measurable_ofReal.comp
      (((measurable_id.pow_const 2).mul (Real.measurable_exp.comp
        (measurable_id.pow_const 2).neg)).mul Real.measurable_log))).aestronglyMeasurable
  · have ht0 : (0 : ℝ) < t := ht
    have hp : 0 < t ^ (w.re - 1) := Real.rpow_pos_of_pos ht0 _
    simp only [Pi.add_apply]
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
      Real.rpow_add ht0, Real.rpow_add ht0, Real.rpow_natCast, Real.rpow_natCast]
    have hl := HM.abs_log_le ht0
    have h := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ t ^ (w.re - 1) *
      (t ^ 2 * Real.exp (-t ^ 2)))
    have e : t ^ (w.re - 1) * (t ^ 2 * Real.exp (-t ^ 2)) * (t + 1 / t) =
        t ^ (w.re - 1) * t ^ 3 * Real.exp (-t ^ 2) + t ^ (w.re - 1) * t ^ 1 *
          Real.exp (-t ^ 2) := by
      field_simp
    nlinarith

/-- **`Mg(w) = (log x)Γ(z)/2 + Γ'(z)/4`**, `z = (w + 2)/2`, for `0 < Re w`. -/
theorem mellin_gx_eq {x : ℝ} (hx : 1 ≤ x) {w : ℂ} (hw : 0 < w.re) :
    mellin (gx x) w = (Real.log x : ℂ) * (Complex.Gamma ((w + 2) / 2) / 2) +
      deriv Complex.Gamma ((w + 2) / 2) / 4 := by
  have hx0 : 0 < x := by linarith
  have hw2 : -2 < w.re := by linarith
  have e1 : mellin (gx x) w = ∫ t in Ioi (0 : ℝ), ((Real.log x : ℂ) *
      ((t : ℂ) ^ (w - 1) • ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)) +
        (t : ℂ) ^ (w - 1) • ((t ^ 2 * Real.exp (-t ^ 2) * Real.log t : ℝ) : ℂ)) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    unfold gx
    rw [Real.log_mul hx0.ne' ht0.ne', smul_eq_mul, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e1, integral_add ((mellinConv_t2 hw).const_mul _) (mellinConv_t2_log hw),
    integral_const_mul]
  rw [show (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)) =
      mellin (fun t => ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)) w from rfl,
    show (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) •
      ((t ^ 2 * Real.exp (-t ^ 2) * Real.log t : ℝ) : ℂ)) =
      mellin (fun t => ((t ^ 2 * Real.exp (-t ^ 2) * Real.log t : ℝ) : ℂ)) w from rfl,
    mellin_t2_gauss hw2, mellin_t2_gauss_log hw2]

/-- The point `z = (w + 2)/2` as `a + iy`. -/
theorem half_shift_eq (σ v : ℝ) :
    ((σ : ℂ) + (v : ℂ) * Complex.I + 2) / 2 =
      (((σ + 2) / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- **`|Mg(σ + iv)| ≤ (log x/2)|Γ(z)| + |Γ'(z)|/4`** with the bounds of `HelfMajGammaV`. -/
theorem norm_mellin_gx_le {x : ℝ} (hx : 1 ≤ x) {σ v : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ‖mellin (gx x) ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      Real.log x / 2 * (2 / Real.sqrt Real.pi * ((1 / 2 + |v / 2|) *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |v / 2| / 2))))) +
      1 / 4 * (4 * ((2 + |v / 2|) * ((1 + |v / 2|) *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * (|v / 2| - 1 / 2) / 2)))))) := by
  have hw : 0 < ((σ : ℂ) + (v : ℂ) * Complex.I).re := by simp [hσ0]
  rw [mellin_gx_eq hx hw, half_shift_eq]
  have hl0 := Real.log_nonneg hx
  have h1 := gamma_le_one_three_half (y := v / 2) (a := (σ + 2) / 2) (by linarith)
    (by linarith)
  have h2 := deriv_gamma_le (y := v / 2) (a := (σ + 2) / 2) (by linarith) (by linarith)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have p1 := mul_le_mul_of_nonneg_left h1 hl0
  have p2 := div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 4)
  have e1 : Real.log x * (‖Complex.Gamma ((((σ + 2) / 2 : ℝ) : ℂ) +
      ((v / 2 : ℝ) : ℂ) * Complex.I)‖ / 2) = Real.log x / 2 *
        ‖Complex.Gamma ((((σ + 2) / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I)‖ := by ring
  rw [e1]
  have p3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Real.log x / 2)
  linarith

/-! ## (3) Against `e^{−1.4u}` -/

/-- `e^x ≥ 1 + x + x²/2 + x³/6` for `x ≥ 0`. -/
theorem exp_cubic_le {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- **`(ℓ/2)|Γ| + |Γ'|/4 ≤ (2.8285ℓ + 184.1)e^{−1.4u}`** for `u = |Im z| ≥ 25`
(`1/2 + u ≤ 2e^{0.17u}`, `(2 + u)(1 + u) ≤ 27e^{0.17u}`, `π/2 − 0.17 ≥ 1.4`, `e^{π/4} ≤ e`). -/
theorem decay_bound {u ℓ : ℝ} (hu : 25 ≤ u) (hℓ : 0 ≤ ℓ) :
    ℓ / 2 * (2 / Real.sqrt Real.pi * ((1 / 2 + u) * (Real.sqrt (2 * Real.pi) *
      Real.exp (-(Real.pi * u / 2))))) + 1 / 4 * (4 * ((2 + u) * ((1 + u) *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * (u - 1 / 2) / 2)))))) ≤
      (2.8285 * ℓ + 184.1) * Real.exp (-1.4 * u) := by
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 ≤ 1.41422 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2p := HM.sqrt_2pi_bounds.2
  have hF0 : 0 < Real.exp (0.17 * u) := Real.exp_pos _
  have hE0 : 0 < Real.exp (-(Real.pi * u / 2)) := Real.exp_pos _
  have hEF : Real.exp (-(Real.pi * u / 2)) * Real.exp (0.17 * u) ≤ Real.exp (-1.4 * u) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_d2])
  have hc := exp_cubic_le (x := 0.17 * u) (by linarith)
  have hv : 0 ≤ u - 25 := by linarith
  have hA : 1 / 2 + u ≤ 2 * Real.exp (0.17 * u) := by
    nlinarith [sq_nonneg (u - 25), pow_nonneg (by linarith : (0 : ℝ) ≤ 0.17 * u) 3]
  have hB : (2 + u) * (1 + u) ≤ 27 * Real.exp (0.17 * u) := by
    nlinarith [mul_nonneg hv hv, mul_nonneg (mul_nonneg hv hv) hv]
  have hE2 : Real.exp (-(Real.pi * (u - 1 / 2) / 2)) =
      Real.exp (Real.pi / 4) * Real.exp (-(Real.pi * u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpi4 : Real.exp (Real.pi / 4) ≤ 2.7182818286 :=
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_lt_d2])).trans
      ((Real.exp_one_lt_d9).le.trans (by norm_num))
  have hpi40 : 0 < Real.exp (Real.pi / 4) := Real.exp_pos _
  have t1 : ℓ / 2 * (2 / Real.sqrt Real.pi * ((1 / 2 + u) * (Real.sqrt (2 * Real.pi) *
      Real.exp (-(Real.pi * u / 2))))) =
        ℓ * Real.sqrt 2 * ((1 / 2 + u) * Real.exp (-(Real.pi * u / 2))) := by
    rw [h2pi]
    field_simp
  rw [hE2, t1]
  have k1 : ℓ * Real.sqrt 2 * ((1 / 2 + u) * Real.exp (-(Real.pi * u / 2))) ≤
      2.8285 * ℓ * Real.exp (-1.4 * u) := by
    have p1 := mul_le_mul_of_nonneg_right hA hE0.le
    have p2 : (1 / 2 + u) * Real.exp (-(Real.pi * u / 2)) ≤ 2 * Real.exp (-1.4 * u) := by
      nlinarith
    have p3 := mul_le_mul_of_nonneg_left p2 (mul_nonneg hℓ hs20)
    have p4 : ℓ * Real.sqrt 2 * (2 * Real.exp (-1.4 * u)) ≤ 2.8285 * ℓ * Real.exp (-1.4 * u) := by
      have := Real.exp_pos (-1.4 * u)
      have h5 : ℓ * Real.sqrt 2 ≤ ℓ * 1.41422 := mul_le_mul_of_nonneg_left hs2 hℓ
      nlinarith
    linarith
  have k2 : 1 / 4 * (4 * ((2 + u) * ((1 + u) * (Real.sqrt (2 * Real.pi) *
      (Real.exp (Real.pi / 4) * Real.exp (-(Real.pi * u / 2))))))) ≤
        184.1 * Real.exp (-1.4 * u) := by
    have hs : Real.sqrt (2 * Real.pi) ≤ 2.50663 := by rw [h2pi]; exact hs2p
    have hs0 : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hK : Real.sqrt (2 * Real.pi) * Real.exp (Real.pi / 4) ≤ 2.50663 * 2.7182818286 :=
      mul_le_mul hs hpi4 hpi40.le (by norm_num)
    have hK0 : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (Real.pi / 4) := by positivity
    have hP0 : 0 ≤ (2 + u) * (1 + u) := by nlinarith
    have e : 1 / 4 * (4 * ((2 + u) * ((1 + u) * (Real.sqrt (2 * Real.pi) *
        (Real.exp (Real.pi / 4) * Real.exp (-(Real.pi * u / 2))))))) =
          ((2 + u) * (1 + u)) * (Real.sqrt (2 * Real.pi) * Real.exp (Real.pi / 4)) *
            Real.exp (-(Real.pi * u / 2)) := by ring
    rw [e]
    have p1 := mul_le_mul hB hK hK0 (by positivity)
    have p2 := mul_le_mul_of_nonneg_right p1 hE0.le
    have e2 : 27 * Real.exp (0.17 * u) * (2.50663 * 2.7182818286) * Real.exp (-(Real.pi * u / 2)) =
        27 * (2.50663 * 2.7182818286) * (Real.exp (-(Real.pi * u / 2)) * Real.exp (0.17 * u)) := by
      ring
    have p3 := mul_le_mul_of_nonneg_left hEF (by norm_num : (0 : ℝ) ≤ 27 * (2.50663 * 2.7182818286))
    have := Real.exp_pos (-1.4 * u)
    nlinarith
  nlinarith

/-! ## (4) `MalDecayL` -/

/-- **`MalDecay` with `fmal` scaled by `5·10⁵`** (the spine's `fmal` is itself a weakening of
Helfgott's `eq:cajun`). -/
def MalDecayL : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x → ∀ s : ℂ, 0 < s.re → s.re < 1 → 450 ≤ |s.im| →
    ‖HM.Gm (HM.eta2x x) 0 s‖ ≤ 5e5 * HM.fmal x |s.im|

/-- `φ₁(t) = η₊(t)·t·e^{−t²/2}·log(xt) = h_H(t)·g(t)`. -/
noncomputable def phx (x t : ℝ) : ℂ :=
  ((HW.etaPlus t * t * Real.exp (-t ^ 2 / 2) * Real.log (x * t) : ℝ) : ℂ)

theorem phx_eq (x t : ℝ) : phx x t = (HW.hH 200 t : ℂ) * gx x t := by
  have e : Real.exp (-t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) = Real.exp (-t ^ 2) := by
    rw [← sq, HM.exp_half_sq]
  have hr : HW.etaPlus t * t * Real.exp (-t ^ 2 / 2) * Real.log (x * t) =
      HW.hH 200 t * (t ^ 2 * Real.exp (-t ^ 2) * Real.log (x * t)) := by
    unfold HW.etaPlus
    rw [← e]
    ring
  unfold phx gx
  rw [hr, Complex.ofReal_mul]

theorem measurable_phx (x : ℝ) : Measurable (phx x) := by
  unfold phx
  exact Complex.measurable_ofReal.comp (((contDiff_etaPlus.continuous.measurable.mul
    measurable_id).mul (Real.measurable_exp.comp ((measurable_id.pow_const 2).neg.div_const
      2))).mul (Real.measurable_log.comp (measurable_const.mul measurable_id)))

theorem norm_phx_le {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) :
    ‖phx x t‖ ≤ 1.65 * (t ^ 2 * Real.exp (-t ^ 2) * (Real.log x + (t + 1 / t))) := by
  unfold phx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_etaPlus_le ht
  have h2 := abs_log_mul_le hx ht
  have e : Real.exp (-t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) = Real.exp (-t ^ 2) := by
    rw [← sq, HM.exp_half_sq]
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have p1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg ht.le hE.le)
  have p2 := mul_le_mul p1 h2 (abs_nonneg _) (by positivity)
  have e2 : 1.65 * (t * Real.exp (-t ^ 2 / 2)) * (t * Real.exp (-t ^ 2 / 2)) *
      (Real.log x + (t + 1 / t)) = 1.65 * (t ^ 2 * Real.exp (-t ^ 2) *
        (Real.log x + (t + 1 / t))) := by
    rw [← e]
    ring
  calc |HW.etaPlus t| * t * Real.exp (-t ^ 2 / 2) * |Real.log (x * t)|
      = |HW.etaPlus t| * (t * Real.exp (-t ^ 2 / 2)) * |Real.log (x * t)| := by ring
    _ ≤ 1.65 * (t * Real.exp (-t ^ 2 / 2)) * (t * Real.exp (-t ^ 2 / 2)) *
          (Real.log x + (t + 1 / t)) := p2
    _ = _ := e2

/-- `Gm η₊,₂ 0 = M(h_H·φ₁)`. -/
theorem Gm_eta2x_eq (x : ℝ) (s : ℂ) :
    HM.Gm (HM.eta2x x) 0 s = mellin (fun t => (HW.hH 200 t : ℂ) * phx x t) s := by
  unfold HM.Gm
  refine mellin_congr fun t _ => ?_
  have he : Principia.Common.Goldbach.e (0 * t) = 1 := by
    simp [Principia.Common.Goldbach.e]
  rw [he, mul_one]
  unfold HM.eta2x phx HW.etaPlus
  push_cast
  ring

/-- **`MalDecayL` PROVED.** -/
theorem malDecayL_holds : MalDecayL := by
  intro x hx s hs0 hs1 hτ
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hl0 := Real.log_nonneg hx1
  set σ := s.re with hσ
  set τ := s.im with hτdef
  set Y := (|τ| - 400) / 2 with hY
  have hY25 : 25 ≤ Y := by rw [hY]; linarith
  set M2 := (2.8285 * Real.log x + 184.1) * Real.exp (-1.4 * Y) with hM2def
  have hseq : ∀ r2 r1 : ℝ, s + (r2 : ℂ) * Complex.I + (r1 : ℂ) * Complex.I =
      (σ : ℂ) + ((τ + r2 + r1 : ℝ) : ℂ) * Complex.I := fun r2 r1 => by
    apply Complex.ext <;> simp [hσ, hτdef]
  have hM2 : ∀ r2 r1 : ℝ, -200 ≤ r2 → r2 ≤ 200 → -200 ≤ r1 → r1 ≤ 200 →
      ‖mellin (gx x) (s + (r2 : ℂ) * Complex.I + (r1 : ℂ) * Complex.I)‖ ≤ M2 := by
    intro r2 r1 h1 h2 h3 h4
    rw [hseq]
    have hb := norm_mellin_gx_le hx1 (v := τ + r2 + r1) hs0 hs1
    have hu : Y ≤ |(τ + r2 + r1) / 2| := by
      rw [abs_div, abs_two, hY]
      have := abs_sub_abs_le_abs_sub τ (-(r2 + r1))
      have h5 : |-(r2 + r1)| ≤ 400 := by rw [abs_le]; constructor <;> linarith
      rw [show τ - -(r2 + r1) = τ + r2 + r1 by ring] at this
      linarith
    have hd := decay_bound (u := |(τ + r2 + r1) / 2|) (ℓ := Real.log x) (by linarith) hl0
    have hE : Real.exp (-1.4 * |(τ + r2 + r1) / 2|) ≤ Real.exp (-1.4 * Y) :=
      Real.exp_le_exp.mpr (by linarith)
    have := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 2.8285 * Real.log x + 184.1)
    linarith
  have hM20 : 0 ≤ M2 := by positivity
  have hre : ∀ r : ℝ, (s + (r : ℂ) * Complex.I).re = σ := fun r => by simp [hσ]
  have hM1 : ∀ r2 : ℝ, -200 ≤ r2 → r2 ≤ 200 →
      ‖mellin (phx x) (s + (r2 : ℂ) * Complex.I)‖ ≤ 1 / (2 * Real.pi) * (400 * (7.172 * M2)) := by
    intro r2 h1 h2
    rw [mellin_congr (fun t _ => phx_eq x t)]
    refine norm_mellin_hH_mul_le (measurable_gx x) ?_ fun r1 h3 h4 => hM2 r2 r1 h1 h2 h3 h4
    rw [hre r2]
    exact int_env_gx hs0 (measurable_gx x) fun t ht => norm_gx_le hx1 ht
  have hmain := norm_mellin_hH_mul_le (φ := phx x) (s := s) (measurable_phx x)
    (int_env_gx hs0 (measurable_phx x) fun t ht => norm_phx_le hx1 ht) hM1
  rw [Gm_eta2x_eq]
  have hc : 1 / (2 * Real.pi) * (400 * 7.172) ≤ 456.6 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d6]
  have hc0 : 0 ≤ 1 / (2 * Real.pi) * (400 * 7.172) := by positivity
  have hfm : HM.fmal x |τ| = 10 * (Real.log x + 10) * Real.exp (-1.4 * Y) := by
    unfold HM.fmal
    congr 2
    rw [hY]
    ring
  rw [hfm]
  have e1 : 1 / (2 * Real.pi) * (400 * (7.172 * (1 / (2 * Real.pi) * (400 * (7.172 * M2))))) =
      (1 / (2 * Real.pi) * (400 * 7.172)) * ((1 / (2 * Real.pi) * (400 * 7.172)) * M2) := by
    ring
  rw [e1] at hmain
  have p1 := mul_le_mul_of_nonneg_right hc hM20
  have p2 := mul_le_mul hc p1 (by positivity) (by norm_num)
  have hEY := Real.exp_pos (-1.4 * Y)
  rw [hM2def] at p2
  nlinarith

/-! ## (5) Prop 1.5 RETYPED at `MalNormsL` and `MalDecayL` -/

/-- **`MalTailInt` at `5·10⁵·fmal`**: `≤ 5·10⁻⁷ log x` (from `HM.malTailInt_holds`, constant
factor). -/
theorem malTailIntL_of {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    ∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (5e5 * HM.fmal x t * HM.gw 1 t) ≤
      ENNReal.ofReal (5e-7 * Real.log x) := by
  have h := HM.malTailInt_holds x hx
  have e : ∀ t : ℝ, ENNReal.ofReal (5e5 * HM.fmal x t * HM.gw 1 t) =
      ENNReal.ofReal 5e5 * ENNReal.ofReal (HM.fmal x t * HM.gw 1 t) := fun t => by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal 5e5 * ∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (HM.fmal x t * HM.gw 1 t)
      ≤ ENNReal.ofReal 5e5 * ENNReal.ofReal (1e-12 * Real.log x) := by gcongr
    _ = ENNReal.ofReal (5e-7 * Real.log x) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **The high zeros of `ζ` for `η₊,₂` at `MalDecayL`** (copy of `HM.mal_high`). -/
theorem mal_highL (hZC : HM.ZeroCount) (hG : HM.GarmolaDecr) {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    HM.zsum (1 : DirichletCharacter ℂ 1) {s | 450 < |s.im|}
        (fun ρ => ENNReal.ofReal ‖HM.Gm (HM.eta2x x) 0 ρ‖) ≤
      ENNReal.ofReal (5e-7 * Real.log x + 2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450) := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hL0 : 0 ≤ 5e-7 * Real.log x := mul_nonneg (by norm_num) (Real.log_nonneg hx1)
  have hg0 := HM.gZ_nonneg (q := 1) (T := 450) (by norm_num)
  have hF0 : ∀ T, 0 ≤ 5e5 * HM.fmal x T := fun T =>
    mul_nonneg (by norm_num) (HM.fmal_nonneg hx1 T)
  have hc1 : 0 ≤ 2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450 :=
    mul_nonneg (mul_nonneg (by norm_num) (hF0 450)) hg0
  have hanti : AntitoneOn (fun T => 5e5 * HM.fmal x T) (Ici 450) := fun a ha b hb hab =>
    mul_le_mul_of_nonneg_left (HM.fmal_antitoneOn hx1 _ ha hb hab) (by norm_num)
  have hgar := hG hZC 1 1 DirichletCharacter.isPrimitive_one_level_one
    (fun T => 5e5 * HM.fmal x T) 450 (by norm_num)
    ((HM.continuous_fmal x).const_mul (5e5 : ℝ)).measurable hanti (fun t _ => hF0 t)
  simp only [Nat.cast_one] at hgar
  calc HM.zsum (1 : DirichletCharacter ℂ 1) {s | 450 < |s.im|}
        (fun ρ => ENNReal.ofReal ‖HM.Gm (HM.eta2x x) 0 ρ‖)
      ≤ HM.zsum (1 : DirichletCharacter ℂ 1) {s | 450 < |s.im|}
          (fun ρ => ENNReal.ofReal (5e5 * HM.fmal x |ρ.im|)) := by
        refine HM.zsum_mono _ fun ρ hρ => ENNReal.ofReal_le_ofReal ?_
        have hlt : 450 < |ρ.im| := hρ.2
        exact malDecayL_holds x hx ρ hρ.1.2.1 hρ.1.2.2 hlt.le
    _ ≤ (∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (5e5 * HM.fmal x t * HM.gw 1 t)) +
          ENNReal.ofReal (2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450) := hgar
    _ ≤ ENNReal.ofReal (5e-7 * Real.log x) +
          ENNReal.ofReal (2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450) :=
        add_le_add (malTailIntL_of hx) le_rfl
    _ = ENNReal.ofReal (5e-7 * Real.log x + 2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450) :=
        (ENNReal.ofReal_add hL0 hc1).symm

/-- **`prop:konechno` at the PROVED `MalReg`, `MalNormsL` and `MalDecayL`.** -/
theorem mal_errL2 (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount) (hHs : HM.Hausierer)
    (hG : HM.GarmolaDecr) (pf : RT.PlattFull)
    {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    ‖MajSp.err (HM.eta2x x) (1 : DirichletCharacter ℂ 1) 0 x‖ ≤
      (5e-7 * Real.log x + 2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450) +
        HM.hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
          (1.24703 * Real.log x + 0.40745) / Real.sqrt x + RmalL x / x := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hL0 := Real.log_nonneg hx1
  have mr := malReg_holds
  obtain ⟨n2, nl, n1, nd, nc⟩ := malNormsL_holds x hx
  have hT : (450 : ℝ) ≤ RT.plattHeight 1 := by
    rw [PC.plattHeight_one]
    norm_num
  have hgrh := HM.grh_of_platt pf (by norm_num) DirichletCharacter.isPrimitive_one_level_one hT
  have hH := (hHs hZC (HM.eta2x x) (mr x hx).2 1 1 DirichletCharacter.isPrimitive_one_level_one
    0 450 (by norm_num) (by norm_num) hgrh).2 (HM.isRealChar_one 1)
  simp only [Nat.cast_one] at hH
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hR : HM.c0 (HM.eta2x x) 0 + (Real.log ((1 : ℕ) : ℝ) + 8) *
      (MajSp.l2 (deriv (HM.eta2x x)) + 2 * Real.pi * |(0 : ℝ)| * MajSp.l2 (HM.eta2x x)) /
        Real.sqrt x ≤ RmalL x := by
    unfold RmalL
    rw [Nat.cast_one, Real.log_one, abs_zero, mul_zero, zero_mul, add_zero, zero_add]
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left nd (by norm_num : (0 : ℝ) ≤ 8)) hs0.le
    linarith
  have hHb : 0 ≤ HM.hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
      (1.24703 * Real.log x + 0.40745) :=
    HM.hbR_nonneg (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
  have hTb : 0 ≤ 5e-7 * Real.log x + 2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450 := by
    have := HM.fmal_nonneg hx1 450
    have := HM.gZ_nonneg (q := 1) (T := 450) (by norm_num)
    positivity
  exact HM.err_le_of_zero_sums hEF (mr x hx).1 (HM.eta2x_zero x)
    DirichletCharacter.isPrimitive_one_level_one hx1 hgrh hHb hTb
    (le_trans hH (ENNReal.ofReal_le_ofReal (HM.hbR_mono (by norm_num) (by norm_num) n2 nl n1)))
    (mal_highL hZC hG hx) hR


/-- The closing arithmetic of Prop 1.5 at `MalNormsL` and `MalDecayL` (`Tm ≤ 7·10⁻⁷ℓ`, was
`1.4·10⁻¹²ℓ`; the budget is `1.05·10⁻⁶ℓ`). -/
theorem malheur_closeL2 {ℓ sx X E Tm H R D : ℝ} (hℓ : 27 ≤ ℓ) (hsx : 1000000 ≤ sx)
    (hX : X = sx * sx) (hE : E ≤ Tm + H / sx + R / X) (hTm : Tm ≤ 7e-7 * ℓ)
    (hH : H ≤ 391 * ℓ) (hR : R ≤ 1.75e6 * ℓ) (hD : D ≤ 3.9e-6 * ℓ + 1.3e-6) :
    X * E + X * D ≤ (5e-6 + 500 / sx) * X * ℓ := by
  have hsx0 : 0 < sx := by linarith
  have hX0 : 0 < X := by rw [hX]; positivity
  have e1 : X * (H / sx) = sx * H := by
    rw [hX]
    field_simp
  have e2 : X * (R / X) = R := by field_simp
  have e3 : (5e-6 + 500 / sx) * X * ℓ = 5e-6 * X * ℓ + 500 * sx * ℓ := by
    rw [hX]
    field_simp
  have p0 := mul_le_mul_of_nonneg_left hE hX0.le
  have p1 := mul_le_mul_of_nonneg_left hTm hX0.le
  have p2 := mul_le_mul_of_nonneg_left hH hsx0.le
  have p3 : R ≤ 1.75 * sx * ℓ := by nlinarith
  have p4 := mul_le_mul_of_nonneg_left hD hX0.le
  have p5 : X * 1.3e-6 ≤ X * (1.3e-6 / 27 * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) hX0.le
  have p6 : 0 ≤ sx * ℓ := by positivity
  rw [e3]
  have e4 : X * (Tm + H / sx + R / X) = X * Tm + X * (H / sx) + X * (R / X) := by ring
  nlinarith


/-- **`MR.MalheurAtR η₊ x` at `MalNormsL` and `MalDecayL`**. -/
theorem malheurAt_of_linksL2 (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount)
    (hHs : HM.Hausierer) (hG : HM.GarmolaDecr) (mm : HM.MalMain) (pf : RT.PlattFull) (x : ℝ)
    (hx : 10 ^ 12 ≤ x) :
    MR.MalheurAtR HW.etaPlus x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have he0 : ∀ y : ℝ, y = 0 → Principia.Common.Goldbach.e y = 1 := fun y hy => by
    rw [hy]
    simp [Principia.Common.Goldbach.e]
  have htw : MajSp.twSum (HM.eta2x x) (1 : DirichletCharacter ℂ 1) x (0 / x) =
      ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
        HW.etaPlus ((n : ℝ) / x) ^ 2 : ℝ) : ℂ) := by
    rw [zero_div, Complex.ofReal_tsum]
    unfold MajSp.twSum
    congr 1
    funext n
    have hxn : x * ((n : ℝ) / x) = n := by field_simp
    rw [MulChar.one_apply (isUnit_of_subsingleton _), he0 _ (mul_zero _)]
    unfold HM.eta2x
    rw [hxn]
    push_cast
    ring
  have hft : MajSp.mainFT (HM.eta2x x) 0 =
      ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t) : ℝ) : ℂ) := by
    unfold MajSp.mainFT
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [he0 _ (zero_mul t), mul_one]
    rfl
  have herr : MajSp.err (HM.eta2x x) (1 : DirichletCharacter ℂ 1) 0 x =
      ((((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
        HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
        ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t) : ℝ)) : ℂ) := by
    unfold MajSp.err
    rw [htw, hft, if_pos (rfl : (1 : ℕ) = 1), Complex.ofReal_sub, Complex.ofReal_div]
  have hb := mal_errL2 hEF hZC hHs hG pf hx
  rw [herr, Complex.norm_real, Real.norm_eq_abs] at hb
  have hm := mm x hx
  obtain ⟨hs450, hL7, hL3, hg, hE⟩ := HM.malT_facts
  have hℓ := log_x_ge hx
  have hsx : 1000000 ≤ Real.sqrt x := HM.sqrt_x_ge' hx
  have hTm : 5e-7 * Real.log x + 2 * (5e5 * HM.fmal x 450) * HM.gZ 1 450 ≤
      7e-7 * Real.log x := by
    unfold HM.fmal
    have h1 : Real.exp (-0.7 * (450 - 400)) * HM.gZ 1 450 ≤ 6.4e-16 * 21.2 :=
      mul_le_mul hE hg (HM.gZ_nonneg (by norm_num)) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1e7 * (Real.log x + 10))
    have e : 2 * (5e5 * (10 * (Real.log x + 10) * Real.exp (-0.7 * (450 - 400)))) *
        HM.gZ 1 450 = 1e7 * (Real.log x + 10) * (Real.exp (-0.7 * (450 - 400)) *
          HM.gZ 1 450) := by ring
    rw [e]
    nlinarith
  have hH : HM.hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
      (1.24703 * Real.log x + 0.40745) ≤ 391 * Real.log x := by
    unfold HM.hbR
    rw [Real.log_one]
    exact HM.hbR_mal_close hs450 (Real.sqrt_nonneg _) hL7 hL3 hℓ
  have hR : RmalL x ≤ 1.75e6 * Real.log x := by
    unfold RmalL
    have h1 : 8 * (560000 * (Real.log x + 2)) / Real.sqrt x ≤
        8 * (560000 * (Real.log x + 2)) / 1000000 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hsx
    linarith
  have key := malheur_closeL2 hℓ hsx (Real.mul_self_sqrt hx0.le).symm hb hTm hH hR hm
  unfold MR.MalheurAtR
  have e1 : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
      HW.etaPlus ((n : ℝ) / x) ^ 2 - (0.640206 * x * Real.log x - 0.021095 * x) =
        x * ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) +
        x * ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095)) := by
    field_simp
    ring
  rw [e1]
  calc |x * ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) +
        x * ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095))|
      ≤ |x * ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t))| +
        |x * ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095))| := abs_add_le _ _
    _ = x * |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)| +
        x * |(∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095)| := by
        rw [abs_mul, abs_mul, abs_of_pos hx0]
    _ ≤ (5e-6 + 500 / Real.sqrt x) * x * Real.log x := key


/-- **`MR.MalheurR η₊` from `ExplicitFormula`, `ZeroCount`, `Hausierer`, `GarmolaDecr`, `MalMain`
and Platt**: `MalReg`, the norms, the decay and the tail are PROVED. -/
theorem malheurR_of_linksL2 (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount)
    (hHs : HM.Hausierer) (hG : HM.GarmolaDecr) (mm : HM.MalMain) (pf : RT.PlattFull) :
    MR.MalheurR HW.etaPlus :=
  fun x hx => malheurAt_of_linksL2 hEF hZC hHs hG mm pf x hx

end Principia.Common.TernaryGoldbach.HP
