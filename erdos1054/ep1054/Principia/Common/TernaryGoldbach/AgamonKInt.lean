/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonLeftLD

set_option autoImplicit false

/-!
# `AG.KInt` PROVED: `∫ K(τ)²/|−1/2 + iτ|² dτ ≤ 2π·8²`

**`kInt_holds : KInt`**. `K(τ) = |log 2π − log z| + π/2 + 1/2 + 7/4`, `z = 3/2 − iτ`.
* Pointwise (`kfun_le`): `K(τ) ≤ 6.84 + log(1 + τ²)/2`, from
  `|log 2π − log z| ≤ |log 2π − log|z|| + |arg z|`, `|arg z| ≤ π/2` (`Re z > 0`),
  `log|z| ≤ log 2π + log(1 + τ²)/2` (`|z|² = 9/4 + τ² ≤ 4π²(1 + τ²)`) and
  `log 2π − log|z| ≤ log(4π/3) ≤ 1.44` (`e^{1.44} ≥ ∑_{i<8} 1.44^i/i! > 4.21`).
* `∫ log(1 + τ²)²/|s|² dτ ≤ 25` (`lint_log_sq_le`): even integrand, majorised on `[0, 1]` by `1`
  (`log(1 + τ²) ≤ τ²`) and on `(1, ∞)` by `(log 2 + 2 log τ)²/τ²`, whose integral is
  `log² 2 + 4 log 2 + 8` exactly (antiderivative
  `−((log 2 + 2 log τ)² + 4(log 2 + 2 log τ) + 8)/τ`); total `2(1 + 11.26) ≤ 25`.
* Minkowski: `‖K/s‖₂ ≤ 6.84√(2π) + (1/2)·5 ≤ 8√(2π)`.
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF
open scoped ENNReal

/-! ## (1) The pointwise majorant -/

/-- `|z| = √(9/4 + τ²)` for `z = 3/2 − iτ`. -/
theorem norm_sR (τ : ℝ) : ‖sR τ‖ = Real.sqrt (9 / 4 + τ ^ 2) := by
  have e : sR τ = ((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I := by
    unfold sR
    push_cast
    ring
  rw [e, Complex.norm_add_mul_I]
  congr 1
  ring

/-- `log(4π/3) ≤ 1.44`. -/
theorem log_four_pi_div_three : Real.log 2 + Real.log Real.pi - Real.log (3 / 2) ≤ 1.44 := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have e : Real.log 2 + Real.log Real.pi - Real.log (3 / 2) = Real.log (4 * Real.pi / 3) := by
    rw [← Real.log_mul (by norm_num) hpi0.ne', ← Real.log_div (by positivity) (by norm_num)]
    congr 1
    ring
  rw [e, Real.log_le_iff_le_exp (by positivity)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1.44 by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- **`K(τ) ≤ 6.84 + log(1 + τ²)/2`.** -/
theorem kfun_le (τ : ℝ) : Kfun τ ≤ 6.84 + Real.log (1 + τ ^ 2) / 2 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  set z := sR τ with hz
  have hzre : 0 ≤ z.re := by rw [hz, sR_re]; norm_num
  have harg : |Complex.arg z| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hzre
  have hN := norm_sR τ
  have hL0 : 0 ≤ Real.log (1 + τ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
  have hNpos : 0 < ‖z‖ := by rw [hN]; positivity
  -- `log|z| ≤ log 2π + log(1 + τ²)/2`
  have hup : Real.log ‖z‖ ≤ Real.log (2 * Real.pi) + Real.log (1 + τ ^ 2) / 2 := by
    have h1 : ‖z‖ ≤ 2 * Real.pi * Real.sqrt (1 + τ ^ 2) := by
      rw [hN]
      rw [show 2 * Real.pi * Real.sqrt (1 + τ ^ 2) = Real.sqrt ((2 * Real.pi) ^ 2 * (1 + τ ^ 2))
        by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      have hp2 : (36 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
      have h1t : (0 : ℝ) ≤ 1 + τ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hp2 h1t, sq_nonneg τ]
    have h2 := Real.log_le_log hNpos h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity)] at h2
    linarith
  -- `log|z| ≥ log(3/2)`
  have hlo : Real.log (3 / 2) ≤ Real.log ‖z‖ := by
    apply Real.log_le_log (by norm_num)
    rw [hN, show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg τ])
  have h2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) hpi0.ne'
  have hlog := log_four_pi_div_three
  have habs : |Real.log (2 * Real.pi) - Real.log ‖z‖| ≤ 1.44 + Real.log (1 + τ ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  -- the complex logarithm
  have hc : ‖((Real.log (2 * Real.pi) : ℝ) : ℂ) - Complex.log z‖ ≤
      |Real.log (2 * Real.pi) - Real.log ‖z‖| + Real.pi / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.log_re,
      Complex.log_im, zero_sub, abs_neg]
    linarith
  unfold Kfun
  rw [← hz]
  linarith

/-! ## (2) `∫ log(1 + τ²)²/|s|² ≤ 25` -/

/-- The majorant on `(1, ∞)`. -/
noncomputable def gTail (t : ℝ) : ℝ := (Real.log 2 + 2 * Real.log t) ^ 2 / t ^ 2

/-- Its antiderivative `G(t) = −(P(log 2 + 2 log t))/t`, `P(u) = u² + 4u + 8`. -/
noncomputable def GTail (t : ℝ) : ℝ :=
  -(((Real.log 2 + 2 * Real.log t) ^ 2 + 4 * (Real.log 2 + 2 * Real.log t) + 8) / t)

theorem hasDerivAt_GTail {t : ℝ} (ht : 0 < t) : HasDerivAt GTail (gTail t) t := by
  have hl : HasDerivAt (fun x => Real.log 2 + 2 * Real.log x) (2 * t⁻¹) t := by
    simpa using ((Real.hasDerivAt_log ht.ne').const_mul 2).const_add (Real.log 2)
  have hP := ((hl.pow 2).add (hl.const_mul 4)).add_const 8
  have hG := (hP.div (hasDerivAt_id t) ht.ne').neg
  refine HasDerivAt.congr_deriv (f := GTail) hG ?_
  unfold gTail
  simp only [id, Pi.add_apply, Pi.pow_apply]
  field_simp
  ring

theorem tendsto_GTail : Tendsto GTail atTop (𝓝 0) := by
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  simp only [one_mul, add_zero, pow_one, pow_zero] at h2 h1 h0
  have hsum := (((h2.const_mul 4).add (h1.const_mul (4 * Real.log 2 + 8))).add
    (h0.const_mul ((Real.log 2) ^ 2 + 4 * Real.log 2 + 8))).neg
  simp only [mul_zero, add_zero, neg_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold GTail
  field_simp
  ring

theorem gTail_nonneg (t : ℝ) : 0 ≤ gTail t := by
  unfold gTail
  positivity

/-- **`∫_{(1,∞)} (log 2 + 2 log t)²/t² = log² 2 + 4 log 2 + 8`**, with integrability. -/
theorem integral_gTail :
    IntegrableOn gTail (Ioi 1) ∧
      ∫ t in Ioi (1 : ℝ), gTail t = Real.log 2 ^ 2 + 4 * Real.log 2 + 8 := by
  have hc : ContinuousWithinAt GTail (Ici 1) 1 :=
    (hasDerivAt_GTail one_pos).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt GTail (gTail x) x := fun x hx =>
    hasDerivAt_GTail (lt_trans one_pos hx)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd (fun x _ => gTail_nonneg x) tendsto_GTail, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd (fun x _ => gTail_nonneg x) tendsto_GTail]
  unfold GTail
  simp

/-- The full majorant on `[0, ∞)`: `1` on `[0, 1]`, `gTail` on `(1, ∞)`. -/
noncomputable def hMaj (t : ℝ) : ℝ := (Icc 0 1).indicator 1 t + (Ioi 1).indicator gTail t

/-- `log(1 + τ²)²/|s|²` for `τ ≥ 0` is below `hMaj`. -/
theorem log_sq_le_hMaj {t : ℝ} (ht : 0 ≤ t) :
    (Real.log (1 + t ^ 2) / ‖sL t‖) ^ 2 ≤ hMaj t := by
  rw [div_pow, norm_sL_sq]
  have hL0 : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
  have hd : 0 < 1 / 4 + t ^ 2 := by positivity
  unfold hMaj
  rcases le_or_gt t 1 with h1 | h1
  · rw [indicator_of_mem (show t ∈ Icc (0 : ℝ) 1 from ⟨ht, h1⟩),
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr h1), Pi.one_apply, add_zero,
      div_le_one hd]
    have hle : Real.log (1 + t ^ 2) ≤ t ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + t ^ 2 by positivity)
      linarith
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul hle hle hL0 (sq_nonneg t)]
  · rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) 1 from fun h => absurd h.2 (not_le.mpr h1)),
      indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1), zero_add]
    unfold gTail
    have ht0 : 0 < t := lt_trans one_pos h1
    have hle : Real.log (1 + t ^ 2) ≤ Real.log 2 + 2 * Real.log t := by
      have e : Real.log 2 + 2 * Real.log t = Real.log (2 * t ^ 2) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
      rw [e]
      apply Real.log_le_log (by positivity)
      have h2 : (1 : ℝ) < t ^ 2 := by nlinarith
      linarith
    calc Real.log (1 + t ^ 2) ^ 2 / (1 / 4 + t ^ 2)
        ≤ (Real.log 2 + 2 * Real.log t) ^ 2 / (1 / 4 + t ^ 2) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0 hle 2) hd.le
      _ ≤ (Real.log 2 + 2 * Real.log t) ^ 2 / t ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)

/-- **`∫ hMaj = 1 + (log² 2 + 4 log 2 + 8)`.** -/
theorem lint_hMaj :
    ∫⁻ t : ℝ, ENNReal.ofReal (hMaj t) =
      1 + ENNReal.ofReal (Real.log 2 ^ 2 + 4 * Real.log 2 + 8) := by
  obtain ⟨hint, hval⟩ := integral_gTail
  have hm1 : Measurable fun t : ℝ => (Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) t :=
    measurable_const.indicator measurableSet_Icc
  unfold hMaj
  rw [show (fun t : ℝ => ENNReal.ofReal ((Icc (0 : ℝ) 1).indicator 1 t + (Ioi 1).indicator gTail t))
    = fun t => ENNReal.ofReal ((Icc (0 : ℝ) 1).indicator 1 t) +
      ENNReal.ofReal ((Ioi 1).indicator gTail t) from by
    funext t
    exact ENNReal.ofReal_add (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
      (Set.indicator_nonneg (fun x _ => gTail_nonneg x) t)]
  rw [lintegral_add_left hm1.ennreal_ofReal]
  congr 1
  · rw [show (fun t : ℝ => ENNReal.ofReal ((Icc (0 : ℝ) 1).indicator 1 t)) =
        (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) from by
      funext t
      by_cases h : t ∈ Icc (0 : ℝ) 1
      · simp [indicator_of_mem h]
      · simp [indicator_of_notMem h]]
    rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, one_mul, Real.volume_Icc]
    norm_num
  · rw [show (fun t : ℝ => ENNReal.ofReal ((Ioi 1).indicator gTail t)) =
        (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (gTail t)) from by
      funext t
      by_cases h : t ∈ Ioi (1 : ℝ)
      · simp [indicator_of_mem h]
      · simp [indicator_of_notMem h]]
    rw [lintegral_indicator measurableSet_Ioi, ← hval,
      ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => gTail_nonneg x)]

/-- **`∫ log(1 + τ²)²/|s|² dτ ≤ 25`** (even integrand). -/
theorem lint_log_sq_le :
    ∫⁻ τ : ℝ, ENNReal.ofReal ((Real.log (1 + τ ^ 2) / ‖sL τ‖) ^ 2) ≤ ENNReal.ofReal 25 := by
  set hP : ℝ → ℝ := fun t => if 0 ≤ t then hMaj t else 0 with hPdef
  have hPnn : ∀ t, 0 ≤ hP t := by
    intro t
    simp only [hPdef]
    split_ifs
    · unfold hMaj
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
        (Set.indicator_nonneg (fun x _ => gTail_nonneg x) t)
    · exact le_refl 0
  have hpt : ∀ τ : ℝ, ENNReal.ofReal ((Real.log (1 + τ ^ 2) / ‖sL τ‖) ^ 2) ≤
      ENNReal.ofReal (hP τ) + ENNReal.ofReal (hP (-τ)) := by
    intro τ
    rcases le_or_gt 0 τ with h | h
    · have := log_sq_le_hMaj h
      refine (ENNReal.ofReal_le_ofReal ?_).trans le_self_add
      simp only [hPdef, if_pos h]
      exact this
    · have hn : 0 ≤ -τ := by linarith
      have h1 := log_sq_le_hMaj hn
      have e1 : (-τ) ^ 2 = τ ^ 2 := by ring
      have e2 : ‖sL (-τ)‖ = ‖sL τ‖ := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sL_sq, norm_sL_sq, e1]
      rw [e1, e2] at h1
      refine (ENNReal.ofReal_le_ofReal ?_).trans le_add_self
      simp only [hPdef, if_pos hn]
      exact h1
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (hP t) := by
    apply Measurable.ennreal_ofReal
    simp only [hPdef]
    refine Measurable.ite measurableSet_Ici ?_ measurable_const
    unfold hMaj
    exact (measurable_const.indicator measurableSet_Icc).add
      ((show Measurable gTail by unfold gTail; fun_prop).indicator measurableSet_Ioi)
  have hhalf : ∫⁻ t : ℝ, ENNReal.ofReal (hP t) ≤
      1 + ENNReal.ofReal (Real.log 2 ^ 2 + 4 * Real.log 2 + 8) := by
    rw [← lint_hMaj]
    refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
    simp only [hPdef]
    split_ifs
    · exact le_rfl
    · unfold hMaj
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
        (Set.indicator_nonneg (fun x _ => gTail_nonneg x) t)
  have hneg : ∫⁻ t : ℝ, ENNReal.ofReal (hP (-t)) = ∫⁻ t : ℝ, ENNReal.ofReal (hP t) :=
    lintegral_neg_eq_self (fun t => ENNReal.ofReal (hP t))
  set v : ℝ := Real.log 2 ^ 2 + 4 * Real.log 2 + 8 with hv
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hv0 : 0 ≤ v := by positivity
  calc ∫⁻ τ : ℝ, ENNReal.ofReal ((Real.log (1 + τ ^ 2) / ‖sL τ‖) ^ 2)
      ≤ ∫⁻ τ : ℝ, (ENNReal.ofReal (hP τ) + ENNReal.ofReal (hP (-τ))) := lintegral_mono hpt
    _ = (∫⁻ τ : ℝ, ENNReal.ofReal (hP τ)) + ∫⁻ τ : ℝ, ENNReal.ofReal (hP (-τ)) :=
        lintegral_add_left hmeas (fun τ => ENNReal.ofReal (hP (-τ)))
    _ ≤ (1 + ENNReal.ofReal v) + (1 + ENNReal.ofReal v) := by
        rw [hneg]
        exact add_le_add hhalf hhalf
    _ ≤ ENNReal.ofReal 25 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hv0,
          ← ENNReal.ofReal_add (show 0 ≤ 1 + v by positivity) (show 0 ≤ 1 + v by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [hv]
        nlinarith

/-! ## (3) `KInt` -/

/-- **`KInt` HOLDS.** -/
theorem kInt_holds : KInt := by
  unfold KInt
  have hpi : 0 < 2 * Real.pi := by positivity
  have hK0 : ∀ τ, 0 ≤ Kfun τ := fun τ => by unfold Kfun; positivity
  have hL0 : ∀ τ : ℝ, 0 ≤ Real.log (1 + τ ^ 2) := fun τ =>
    Real.log_nonneg (by nlinarith [sq_nonneg τ])
  set f : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (6.84 / ‖sL τ‖) with hf
  set g : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (Real.log (1 + τ ^ 2) / 2 / ‖sL τ‖) with hg
  have hfm : AEMeasurable f volume :=
    (measurable_const.div measurable_sL.norm).ennreal_ofReal.aemeasurable
  have hgm : AEMeasurable g volume :=
    ((((measurable_const.add (measurable_id.pow_const 2)).log).div_const 2).div
      measurable_sL.norm).ennreal_ofReal.aemeasurable
  have hpt : ∀ τ : ℝ, ENNReal.ofReal ((Kfun τ / ‖sL τ‖) ^ 2) ≤ (f + g) τ ^ (2 : ℝ) := by
    intro τ
    have hs : 0 < ‖sL τ‖ := norm_pos_iff.mpr (sL_ne_zero τ)
    simp only [Pi.add_apply, hf, hg]
    have ha : 0 ≤ 6.84 / ‖sL τ‖ := by positivity
    have hb : 0 ≤ Real.log (1 + τ ^ 2) / 2 / ‖sL τ‖ := div_nonneg (by linarith [hL0 τ]) hs.le
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_pow (add_nonneg ha hb)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (div_nonneg (hK0 τ) hs.le) ?_ 2)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (kfun_le τ) hs.le
  have hmk := ENNReal.lintegral_Lp_add_le hfm hgm (show (1 : ℝ) ≤ 2 by norm_num)
  have e2 : ∀ (u : ℝ → ℝ), (∀ τ, 0 ≤ u τ) →
      (fun τ => ENNReal.ofReal (u τ) ^ (2 : ℝ)) = fun τ => ENNReal.ofReal (u τ ^ 2) := by
    intro u hu
    funext τ
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hu τ)]
  rw [show (fun τ => f τ ^ (2 : ℝ)) = fun τ => ENNReal.ofReal ((6.84 / ‖sL τ‖) ^ 2) from
      e2 _ fun τ => by positivity,
    show (fun τ => g τ ^ (2 : ℝ)) = fun τ => ENNReal.ofReal
      ((Real.log (1 + τ ^ 2) / 2 / ‖sL τ‖) ^ 2) from
      e2 _ fun τ => div_nonneg (by linarith [hL0 τ]) (norm_nonneg _), lint_c_div_sL] at hmk
  -- the `g` integral: `(1/4)·∫ log(1 + τ²)²/|s|² ≤ 25/4`
  have hg2 : ∫⁻ τ : ℝ, ENNReal.ofReal ((Real.log (1 + τ ^ 2) / 2 / ‖sL τ‖) ^ 2) ≤
      ENNReal.ofReal ((5 / 2) ^ 2) := by
    have e : ∀ τ : ℝ, ENNReal.ofReal ((Real.log (1 + τ ^ 2) / 2 / ‖sL τ‖) ^ 2) =
        ENNReal.ofReal (1 / 4) * ENNReal.ofReal ((Real.log (1 + τ ^ 2) / ‖sL τ‖) ^ 2) := by
      intro τ
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (1 / 4) * ∫⁻ τ : ℝ, ENNReal.ofReal ((Real.log (1 + τ ^ 2) / ‖sL τ‖) ^ 2)
        ≤ ENNReal.ofReal (1 / 4) * ENNReal.ofReal 25 := by
          gcongr
          exact lint_log_sq_le
      _ = ENNReal.ofReal ((5 / 2) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hg' := ENNReal.rpow_le_rpow hg2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [ofReal_sq_rpow_half (by norm_num)] at hg'
  have k1 : 2 * Real.pi * 6.84 ^ 2 = (Real.sqrt (2 * Real.pi) * 6.84) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpi.le]
  rw [k1, ofReal_sq_rpow_half (by positivity)] at hmk
  have hsum := hmk.trans (add_le_add le_rfl hg')
  rw [← ENNReal.ofReal_add (by positivity) (by norm_num)] at hsum
  have h3 := le_sq_of_rpow_half_le hsum
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two] at h3
  refine (lintegral_mono hpt).trans (h3.trans (ENNReal.ofReal_le_ofReal ?_))
  -- `(6.84√(2π) + 5/2)² ≤ 2π·64`
  have hs2 : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) hpi.le]
    nlinarith [Real.pi_gt_d2]
  have hsq := Real.sq_sqrt hpi.le
  nlinarith [hs2, Real.sqrt_nonneg (2 * Real.pi)]

end Principia.Common.TernaryGoldbach.AG
