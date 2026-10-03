/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajPlusNorms
import Principia.Common.TernaryGoldbach.HelfMajGammaV
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

/-!
# `h_H` is band-limited: `h_H(t) = (1/2π)∫_{−200}^{200} A(r) t^{ir} dr`

**`hH_rep`**: for `t > 0`, `h₂₀₀(t) = (1/2π)∫_{−200}^{200} A(r)e^{ir log t} dr`, where
`A(r) = ∫₀^∞ h(1/v)v^{ir} dv/v` is the Mellin transform of `h` at `−ir` written in the scaled
variable (`Ah`). The proof is Fubini plus the elementary
`F_H(y) = (1/2π)∫_{−H}^{H} e^{ir log y} dr` (`FH_eq_integral`, from Mathlib's
`integral_exp_mul_I_eq_sinc`); no Mellin inversion and no Plancherel.

Consequences:
* `norm_Ah_le`: `|A(r)| ≤ ∫₀^∞ h(1/v)dv/v = ∫₀² h(u)du/u ≤ (8/5)e^{3/2} ≤ 7.172` (the substitution
  `u = 1/v` is Mathlib's `integral_comp_rpow_Ioi` at `p = −1`; the truth is `2.02055`);
* `mellin_hH_mul`: for `φ` with `t^{σ−1}φ ∈ L¹`,
  `M(h_H·φ)(s) = (1/2π)∫_{−200}^{200} A(r)·Mφ(s + ir) dr`
  — multiplying by `h_H` shifts the Mellin variable by at most `200` vertically;
* `norm_mellin_hH_mul_le`: `|M(h_H·φ)(s)| ≤ (1/2π)·400·7.172·sup_{|r| ≤ 200}|Mφ(s + ir)|`.
-/

namespace Principia.Common.TernaryGoldbach.HP

open MeasureTheory Set Filter

/-! ## (1) `F_H` as a band-limited Fourier integral -/

/-- `∫_{−H}^{H} e^{irL} dr = 2H·sinc(HL)`. -/
theorem integral_exp_rL (H L : ℝ) :
    ∫ r in (-H)..H, Complex.exp (((r * L : ℝ) : ℂ) * Complex.I) = 2 * H * Real.sinc (H * L) := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
    ring
  · have h := intervalIntegral.integral_comp_mul_right
      (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hL (a := -H) (b := H)
    rw [h, neg_mul, integral_exp_mul_I_eq_sinc (H * L)]
    rw [Complex.real_smul]
    have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    push_cast
    field_simp

/-- **`F_H(y) = (1/2π)∫_{−H}^{H} e^{ir log y} dr`**. -/
theorem FH_eq_integral (H y : ℝ) :
    (HW.FH H y : ℂ) =
      1 / (2 * Real.pi) * ∫ r in (-H)..H, Complex.exp (((r * Real.log y : ℝ) : ℂ) * Complex.I) := by
  rw [integral_exp_rL, HW.FH]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-! ## (2) The coefficient `A(r)` -/

/-- `a(v) = h(1/v)/v`. -/
noncomputable def aH (v : ℝ) : ℝ := HW.hFun (1 / v) / v

theorem measurable_aH : Measurable aH :=
  (HW.measurable_hFun.comp (measurable_const.div measurable_id)).div measurable_id

theorem aH_nonneg (v : ℝ) (hv : 0 < v) : 0 ≤ aH v :=
  div_nonneg (BL.hFun_nonneg _) hv.le

/-- `|a(v)| ≤ 360/(1 + v²)`. -/
theorem abs_aH_le {v : ℝ} (hv : 0 < v) : |aH v| ≤ 5 * 72 * (1 + v ^ 2)⁻¹ := by
  have h := scaled_bound HW.hFun (C := 72) (H := Real.pi) Real.pi_pos.le (by norm_num)
    (fun _ hu => abs_hFun_lin hu) (fun _ hu => HW.hFun_of_two_le hu) (1 / v) hv
  rw [show 1 / v * v = 1 by field_simp, HW.FH_one, div_self Real.pi_ne_zero, mul_one,
    Real.norm_eq_abs] at h
  have e : (5 : ℝ) * 72 * 1 = 5 * 72 := by norm_num
  rw [e] at h
  exact h

theorem integrable_aH : Integrable aH (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' (scaled_bound_int 72 Real.pi) measurable_aH.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_))
  rw [Real.norm_eq_abs, div_self Real.pi_ne_zero, mul_one]
  exact abs_aH_le hv

/-- **`A(r) = ∫₀^∞ h(1/v)v^{ir}dv/v`** (the Mellin transform of `h` at `−ir`, scaled). -/
noncomputable def Ah (r : ℝ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), (aH v : ℂ) * Complex.exp (((r * Real.log v : ℝ) : ℂ) * Complex.I)

/-- `∫₀^∞ h(1/v)dv/v = ∫₀^∞ h(u)du/u` (`u = 1/v`). -/
theorem integral_aH_eq :
    ∫ v in Ioi (0 : ℝ), aH v = ∫ u in Ioi (0 : ℝ), HW.hFun u / u := by
  rw [← integral_comp_rpow_Ioi (fun u => HW.hFun u / u) (p := -1) (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : 0 < v := hv
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg_one, abs_neg, abs_one, one_mul,
    smul_eq_mul, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hv0.le,
    Real.rpow_natCast]
  unfold aH
  field_simp

/-- `g₀(u) = e^{3/2}u·max(2−u, 0)³`, a continuous majorant of `h(u)/u`; `∫₀^∞ g₀ = (8/5)e^{3/2}`. -/
noncomputable def g0 (u : ℝ) : ℝ := u * max (2 - u) 0 ^ 3

theorem gi_g0 : HM.GI g0 (8 / 5) := by
  have h2 : ∀ t : ℝ, 2 < t → g0 t = 0 := fun t ht => by
    unfold g0
    rw [max_eq_right (by linarith)]
    ring
  refine ⟨EN.integrableOn_of_cont _ (by unfold g0; fun_prop) h2, ?_⟩
  rw [EN.setInt_Ioi_02 _ h2]
  have h : EqOn g0 (fun u => ∑ k : Fin 5, (![0, 8, -12, 6, -1] : Fin 5 → ℝ) k * u ^ (k : ℕ))
      (uIcc 0 2) := by
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    unfold g0
    rw [max_eq_left (by linarith [hu.2])]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ]
    ring
  rw [intervalIntegral.integral_congr h, EN.int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- **`C₀ = ∫₀^∞ h(1/v)dv/v ≤ (8/5)e^{3/2} ≤ 7.172`**. -/
theorem integral_aH_le : ∫ v in Ioi (0 : ℝ), aH v ≤ 7.172 := by
  rw [integral_aH_eq]
  have hG := gi_smul (Real.exp (3 / 2)) gi_g0
  have h := HM.int_le_of_pt (f := fun u => HW.hFun u / u) hG (fun u => ?_) fun u hu => ?_
  · have := exp_three_half_le
    nlinarith
  · rcases le_or_gt u 0 with h0 | h0
    · rw [HW.hFun_of_nonpos h0, zero_div]
    · exact div_nonneg (BL.hFun_nonneg u) h0.le
  · rcases le_or_gt u 2 with h2 | h2
    · have hE : Real.exp (u - 1 / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by linarith)
      rw [BL.hFun_eq_hP hu.le h2]
      unfold BL.hP g0
      rw [max_eq_left (by linarith)]
      have hp : 0 ≤ u * (2 - u) ^ 3 := mul_nonneg hu.le (pow_nonneg (by linarith) 3)
      have e : u ^ 2 * (2 - u) ^ 3 * Real.exp (u - 1 / 2) / u =
          u * (2 - u) ^ 3 * Real.exp (u - 1 / 2) := by
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hE hp
      linarith
    · rw [HW.hFun_of_two_le h2.le, zero_div]
      unfold g0
      rw [max_eq_right (by linarith)]
      norm_num

/-- **`|A(r)| ≤ 7.172`**. -/
theorem norm_Ah_le (r : ℝ) : ‖Ah r‖ ≤ 7.172 := by
  unfold Ah
  refine (norm_integral_le_integral_norm _).trans (le_trans (le_of_eq ?_) integral_aH_le)
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (aH_nonneg v hv)]

/-- `A` is continuous (dominated convergence). -/
theorem continuous_Ah : Continuous Ah := by
  refine continuous_of_dominated (bound := fun v => |aH v|) (fun r => ?_) (fun r => ?_)
    integrable_aH.abs ?_
  · exact ((Complex.measurable_ofReal.comp measurable_aH).mul (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul Real.measurable_log)).mul
        measurable_const))).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · refine Eventually.of_forall fun v => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
        continuous_const))

/-! ## (3) The representation -/

/-- **`h_H(t) = (1/2π)∫_{−200}^{200} A(r)e^{ir log t} dr`** for `t > 0`. -/
theorem hH_rep {t : ℝ} (ht : 0 < t) :
    (HW.hH 200 t : ℂ) = 1 / (2 * Real.pi) *
      ∫ r in (-200 : ℝ)..200, Ah r * Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) := by
  set F : ℝ → ℝ → ℂ := fun r v => (aH v : ℂ) *
    Complex.exp (((r * Real.log v : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) with hF
  have hmeas : Measurable (Function.uncurry F) := by
    refine ((Complex.measurable_ofReal.comp (measurable_aH.comp measurable_snd)).mul
      (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_fst.mul (Real.measurable_log.comp measurable_snd))).mul
          measurable_const))).mul (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
            (measurable_fst.mul measurable_const)).mul measurable_const))
  haveI : IsFiniteMeasure (volume.restrict (uIoc (-200 : ℝ) 200)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [uIoc_of_le (by norm_num), Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (-200 : ℝ) 200)).prod (volume.restrict (Ioi 0))) := by
    have hmaj : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * |aH z.2|)
        ((volume.restrict (uIoc (-200 : ℝ) 200)).prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod (integrable_const 1) integrable_aH.abs
    refine hmaj.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hswap := intervalIntegral_integral_swap hint
  have hL : ∫ r in (-200 : ℝ)..200, ∫ v in Ioi (0 : ℝ), F r v =
      ∫ r in (-200 : ℝ)..200, Ah r * Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [hF]
    rw [integral_mul_const]
    rfl
  have hR : ∫ v in Ioi (0 : ℝ), (∫ r in (-200 : ℝ)..200, F r v) =
      ∫ v in Ioi (0 : ℝ), (aH v : ℂ) * (2 * Real.pi * (HW.FH 200 (t * v) : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv0 : 0 < v := hv
    simp only [hF]
    have e : ∀ r : ℝ, (aH v : ℂ) * Complex.exp (((r * Real.log v : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) = (aH v : ℂ) *
          Complex.exp (((r * Real.log (t * v) : ℝ) : ℂ) * Complex.I) := fun r => by
      rw [mul_assoc, ← Complex.exp_add, Real.log_mul ht.ne' hv0.ne']
      congr 2
      push_cast
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, FH_eq_integral]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    generalize (∫ r in (-200 : ℝ)..200,
      Complex.exp (((r * Real.log (t * v) : ℝ) : ℂ) * Complex.I)) = J
    field_simp
  have hM : (HW.hH 200 t : ℂ) =
      ∫ v in Ioi (0 : ℝ), (aH v : ℂ) * (HW.FH 200 (t * v) : ℂ) := by
    rw [show HW.hH 200 t = HW.mconv HW.hFun (HW.FH 200) t from rfl, mconv_scale _ _ ht,
      ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    unfold aH
    push_cast
    ring
  rw [hM, ← hL, hswap, hR]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : ∀ v : ℝ, (aH v : ℂ) * (2 * Real.pi * (HW.FH 200 (t * v) : ℂ)) =
      2 * Real.pi * ((aH v : ℂ) * (HW.FH 200 (t * v) : ℂ)) := fun v => by ring
  simp_rw [e]
  rw [integral_const_mul]
  generalize (∫ v in Ioi (0 : ℝ), (aH v : ℂ) * (HW.FH 200 (t * v) : ℂ)) = J
  field_simp

/-! ## (4) Multiplying by `h_H` shifts the Mellin variable -/

/-- `t^{s−1}e^{ir log t} = t^{(s + ir) − 1}` for `t > 0`. -/
theorem cpow_shift {t : ℝ} (ht : 0 < t) (s : ℂ) (r : ℝ) :
    (t : ℂ) ^ (s - 1) * Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) ^ (s + (r : ℂ) * Complex.I - 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [show s + (r : ℂ) * Complex.I - 1 = (s - 1) + (r : ℂ) * Complex.I by ring,
    Complex.cpow_add _ _ ht', Complex.cpow_def_of_ne_zero ht' ((r : ℂ) * Complex.I),
    ← Complex.ofReal_log ht.le]
  congr 2
  push_cast
  ring

/-- **`M(h_H·φ)(s) = (1/2π)∫_{−200}^{200} A(r)·Mφ(s + ir) dr`** for measurable `φ` with
`t^{Re s − 1}φ ∈ L¹(0, ∞)`. -/
theorem mellin_hH_mul {φ : ℝ → ℂ} {s : ℂ} (hφm : Measurable φ)
    (hφ : IntegrableOn (fun t => t ^ (s.re - 1) * ‖φ t‖) (Ioi 0)) :
    mellin (fun t => (HW.hH 200 t : ℂ) * φ t) s =
      1 / (2 * Real.pi) * ∫ r in (-200 : ℝ)..200, Ah r * mellin φ (s + (r : ℂ) * Complex.I) := by
  set F : ℝ → ℝ → ℂ := fun r t => Ah r * ((t : ℂ) ^ (s - 1) *
    Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) * φ t) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (uIoc (-200 : ℝ) 200)).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aestronglyMeasurable ?_
    refine (continuous_Ah.measurable.comp measurable_fst).mul (((?_ : Measurable fun z : ℝ × ℝ =>
      (z.2 : ℂ) ^ (s - 1)).mul (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_fst.mul (Real.measurable_log.comp measurable_snd))).mul
          measurable_const))).mul (hφm.comp measurable_snd))
    exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  haveI : IsFiniteMeasure (volume.restrict (uIoc (-200 : ℝ) 200)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [uIoc_of_le (by norm_num), Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (-200 : ℝ) 200)).prod (volume.restrict (Ioi 0))) := by
    have hmaj : Integrable (fun z : ℝ × ℝ => (7.172 : ℝ) * (z.2 ^ (s.re - 1) * ‖φ z.2‖))
        ((volume.restrict (uIoc (-200 : ℝ) 200)).prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod (integrable_const 7.172) hφ
    refine hmaj.mono' hmeas ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_Ioi)).mpr
      (Eventually.of_forall fun z hz => ?_)
    have ht : 0 < z.2 := hz.2
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
    have h1 := norm_Ah_le z.1
    have h2 : 0 ≤ z.2 ^ (s.re - 1) * ‖φ z.2‖ := by positivity
    calc ‖Ah z.1‖ * (z.2 ^ (s.re - 1) * ‖φ z.2‖) ≤ 7.172 * (z.2 ^ (s.re - 1) * ‖φ z.2‖) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = 7.172 * (z.2 ^ (s.re - 1) * ‖φ z.2‖) := rfl
  have hswap := intervalIntegral_integral_swap hint
  have hL : ∫ r in (-200 : ℝ)..200, ∫ t in Ioi (0 : ℝ), F r t =
      ∫ r in (-200 : ℝ)..200, Ah r * mellin φ (s + (r : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [hF]
    rw [integral_const_mul]
    congr 1
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, ← cpow_shift ht s r]
  have hR : mellin (fun t => (HW.hH 200 t : ℂ) * φ t) s =
      1 / (2 * Real.pi) * ∫ t in Ioi (0 : ℝ), ∫ r in (-200 : ℝ)..200, F r t := by
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hF]
    rw [hH_rep ht, smul_eq_mul]
    have e : ∫ r in (-200 : ℝ)..200, Ah r * ((t : ℂ) ^ (s - 1) *
        Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) * φ t) =
          ((t : ℂ) ^ (s - 1) * φ t) * ∫ r in (-200 : ℝ)..200,
            Ah r * Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext r
      ring
    rw [e]
    ring
  rw [hR, ← hswap, hL]

/-- **`|M(h_H·φ)(s)| ≤ (1/2π)·400·7.172·M`** when `|Mφ(s + ir)| ≤ M` for `|r| ≤ 200`. -/
theorem norm_mellin_hH_mul_le {φ : ℝ → ℂ} {s : ℂ} {M : ℝ} (hφm : Measurable φ)
    (hφ : IntegrableOn (fun t => t ^ (s.re - 1) * ‖φ t‖) (Ioi 0))
    (hM : ∀ r : ℝ, -200 ≤ r → r ≤ 200 → ‖mellin φ (s + (r : ℂ) * Complex.I)‖ ≤ M) :
    ‖mellin (fun t => (HW.hH 200 t : ℂ) * φ t) s‖ ≤ 1 / (2 * Real.pi) * (400 * (7.172 * M)) := by
  rw [mellin_hH_mul hφm hφ, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -200) (b := 200)
    (C := 7.172 * M) (f := fun r : ℝ => Ah r * mellin φ (s + (r : ℂ) * Complex.I)) fun r hr => by
      rw [uIoc_of_le (by norm_num)] at hr
      rw [norm_mul]
      exact mul_le_mul (norm_Ah_le r) (hM r hr.1.le hr.2) (norm_nonneg _) (by norm_num)
  rw [show |(200 : ℝ) - -200| = 400 by norm_num] at h
  linarith

end Principia.Common.TernaryGoldbach.HP
