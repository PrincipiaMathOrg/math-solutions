/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajS4Cases
import Principia.Common.TernaryGoldbach.HelfMajS4AC0
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

/-!
# S4, links `PlusBand` and `AIntOf` PROVED

* `plusBand_holds : PlusBand` -- `G_δ^{η₊}(s) = (1/2π)∫_{−200}^{200} A(r) F_δ(s + 1 + ir) dr`
  (`HP.mellin_hH_mul` with `φ(t) = t e^{−t²/2} e(δt)`, whose Mellin transform at `w` is
  `F_δ(w + 1)`, `mellin_phiD`), then `Decay1` at `s + 1 + ir` and the monotonicity of `f1` in
  `T ≥ |τ| − 200` (`f1_anti`: both summands decrease once `T ≥ 100` and `T ≥ 4π²|δ|`). The
  bracket of `f1` at `|τ| − 200` IS the bracket of `HM.fplus`, so the constant is
  `18.2·3.1/2π = 8.98 ≤ 9.062`.
* `aIntOf_holds : AIntOf` -- `∫_{−200}^{200}|A| ≤ 18.2` from `|A| ≤ 2.03` on `[−1.6, 1.6]`,
  `|A| ≤ 3.2975/|r|` on `1.6 ≤ |r| ≤ 3.2`, `|A| ≤ 10.792/r²` beyond: the five pieces total
  `2(3.248 + 3.2975 log 2 + 10.792(1/3.2 − 1/200)) ≤ 17.71`.

Application of `Decay1` and the three pointwise bounds on `A`; no numerics beyond `π > 3.14`
and `log 2 < 0.6931471808`.
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set Filter

/-! ## (1) The Mellin side -/

/-- `φ_δ(t) = t e^{−t²/2} e(δt)`, so that `η₊(t)e(δt) = h_H(t)·φ_δ(t)`. -/
noncomputable def phiD (δ t : ℝ) : ℂ :=
  (t : ℂ) * (((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * Principia.Common.Goldbach.e (δ * t))

theorem norm_e_one (x : ℝ) : ‖Principia.Common.Goldbach.e x‖ = 1 := by
  rw [Principia.Common.Goldbach.e, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℝ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- `Mφ_δ(w) = F_δ(w + 1)`. -/
theorem mellin_phiD (δ : ℝ) (w : ℂ) : mellin (phiD δ) w = Fd δ (w + 1) := by
  rw [Fd, ← mellin_cpow_smul]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, phiD, Complex.cpow_one]

theorem Gm_etaPlus_eq (δ : ℝ) (s : ℂ) :
    HM.Gm HW.etaPlus δ s = mellin (fun t => (HW.hH 200 t : ℂ) * phiD δ t) s := by
  unfold HM.Gm HW.etaPlus phiD
  congr 1
  funext t
  push_cast
  ring

theorem measurable_phiD (δ : ℝ) : Measurable (phiD δ) := by
  have he : Continuous Principia.Common.Goldbach.e := by
    unfold Principia.Common.Goldbach.e
    fun_prop
  have hc : Continuous (phiD δ) := by
    unfold phiD
    fun_prop
  exact hc.measurable

theorem integrableOn_phiD (δ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t => t ^ (σ - 1) * ‖phiD δ t‖) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    (by linarith : (-1 : ℝ) < σ)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  simp only [phiD]
  rw [norm_mul, norm_mul, norm_e_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos (Real.exp_pos _), mul_one,
    show -t ^ 2 / 2 = -(1 / 2) * t ^ 2 by ring, ← mul_assoc,
    show t ^ (σ - 1) * t = t ^ σ by
      rw [Real.rpow_sub_one ht0.ne']
      field_simp]

/-! ## (2) Monotonicity of `f1` -/

/-- `√T e^{−cT}` decreases on `T ≥ T₀` once `2cT₀ ≥ 1`. -/
theorem sqrt_exp_anti {c T0 T : ℝ} (hc : 1 ≤ 2 * c * T0) (h0 : 0 < T0) (hT : T0 ≤ T) :
    Real.sqrt T * Real.exp (-c * T) ≤ Real.sqrt T0 * Real.exp (-c * T0) := by
  have hs0 := Real.sqrt_pos.mpr h0
  have hq0 := Real.sq_sqrt h0.le
  have hqT := Real.sq_sqrt (h0.le.trans hT)
  have hsT : Real.sqrt T * Real.sqrt T0 ≤ (T + T0) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt T - Real.sqrt T0)]
  have h2 : (T + T0) / 2 ≤ T0 * (1 + c * (T - T0)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (by linarith : (0 : ℝ) ≤ 2 * c * T0 - 1)]
  have h1 : Real.sqrt T ≤ Real.sqrt T0 * (1 + c * (T - T0)) := by
    refine le_of_mul_le_mul_right ?_ hs0
    have e : Real.sqrt T0 * (1 + c * (T - T0)) * Real.sqrt T0 =
        Real.sqrt T0 ^ 2 * (1 + c * (T - T0)) := by ring
    rw [e, hq0]
    linarith
  have hE : 1 + c * (T - T0) ≤ Real.exp (c * (T - T0)) := by
    linarith [Real.add_one_le_exp (c * (T - T0))]
  have e1 : Real.exp (-c * T0) = Real.exp (-c * T) * Real.exp (c * (T - T0)) := by
    rw [← Real.exp_add]
    ring_nf
  have hp := Real.exp_pos (-c * T)
  rw [e1]
  calc Real.sqrt T * Real.exp (-c * T)
      ≤ Real.sqrt T0 * (1 + c * (T - T0)) * Real.exp (-c * T) :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ ≤ Real.sqrt T0 * Real.exp (c * (T - T0)) * Real.exp (-c * T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hs0.le) hp.le
    _ = Real.sqrt T0 * (Real.exp (-c * T) * Real.exp (c * (T - T0))) := by ring

/-- `x e^{−ax²}` decreases on `x ≥ x₀` once `2ax₀² ≥ 1`. -/
theorem lin_gauss_anti {a x0 x : ℝ} (hc : 1 ≤ 2 * a * x0 ^ 2) (h0 : 0 < x0) (hx : x0 ≤ x) :
    x * Real.exp (-a * x ^ 2) ≤ x0 * Real.exp (-a * x0 ^ 2) := by
  have ha : 0 < a := by
    by_contra h
    have h' : a ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg x0]
  have hk : 0 ≤ a * x0 * (x + x0) - 1 := by
    nlinarith [mul_nonneg (mul_nonneg ha.le h0.le) (sub_nonneg.mpr hx)]
  have h1 : x ≤ x0 * (1 + a * (x ^ 2 - x0 ^ 2)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hk]
  have hE : 1 + a * (x ^ 2 - x0 ^ 2) ≤ Real.exp (a * (x ^ 2 - x0 ^ 2)) := by
    linarith [Real.add_one_le_exp (a * (x ^ 2 - x0 ^ 2))]
  have e1 : Real.exp (-a * x0 ^ 2) = Real.exp (-a * x ^ 2) * Real.exp (a * (x ^ 2 - x0 ^ 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hp := Real.exp_pos (-a * x ^ 2)
  rw [e1]
  calc x * Real.exp (-a * x ^ 2)
      ≤ x0 * (1 + a * (x ^ 2 - x0 ^ 2)) * Real.exp (-a * x ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ ≤ x0 * Real.exp (a * (x ^ 2 - x0 ^ 2)) * Real.exp (-a * x ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE h0.le) hp.le
    _ = x0 * (Real.exp (-a * x ^ 2) * Real.exp (a * (x ^ 2 - x0 ^ 2))) := by ring

/-- **`f1 δ` decreases** on `T ≥ T₀` when `T₀ ≥ 100` and `T₀ ≥ 4π²|δ|`. -/
theorem f1_anti {δ T0 T : ℝ} (h100 : 100 ≤ T0) (hd : 4 * Real.pi ^ 2 * |δ| ≤ T0)
    (hT : T0 ≤ T) : f1 δ T ≤ f1 δ T0 := by
  unfold f1
  have hs := sqrt_exp_anti (c := 0.1598) (by linarith) (by linarith) hT
  have hg : T / (2 * Real.pi * |δ|) * Real.exp (-0.1065 * (T / (Real.pi * δ)) ^ 2) ≤
      T0 / (2 * Real.pi * |δ|) * Real.exp (-0.1065 * (T0 / (Real.pi * δ)) ^ 2) := by
    rcases eq_or_ne δ 0 with h | h
    · subst h
      simp
    · have hA : 0 < 2 * Real.pi * |δ| := by positivity
      have e : ∀ X : ℝ, -0.1065 * (4 * X ^ 2) = -0.426 * X ^ 2 := fun X => by ring
      rw [sqB T δ, sqB T0 δ, e, e]
      have hx : 2 * Real.pi ≤ T0 / (2 * Real.pi * |δ|) := by
        rw [le_div_iff₀ hA]
        have e2 : 2 * Real.pi * (2 * Real.pi * |δ|) = 4 * Real.pi ^ 2 * |δ| := by ring
        linarith
      have hpi := Real.pi_gt_three
      refine lin_gauss_anti ?_ (by linarith) (div_le_div_of_nonneg_right hT hA.le)
      nlinarith
  linarith

/-! ## (3) `PlusBand` -/

theorem f1_nonneg {δ T : ℝ} (hT : 0 ≤ T) : 0 ≤ f1 δ T := by
  unfold f1
  have : 0 ≤ T / (2 * Real.pi * |δ|) := div_nonneg hT (by positivity)
  positivity

/-- **LINK [PlusBand] PROVED**. -/
theorem plusBand_holds : PlusBand := by
  intro hD hI δ s h0 h1 hT hTd
  have hφ := integrableOn_phiD δ h0
  rw [Gm_etaPlus_eq, HP.mellin_hH_mul (measurable_phiD δ) hφ, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hpt : ∀ r : ℝ, -200 ≤ r → r ≤ 200 →
      ‖HP.Ah r * mellin (phiD δ) (s + (r : ℂ) * Complex.I)‖ ≤
        ‖HP.Ah r‖ * f1 δ (|s.im| - 200) := by
    intro r hr1 hr2
    rw [norm_mul, mellin_phiD]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (s + (r : ℂ) * Complex.I + 1).re = s.re + 1 := by simp
    have him : (s + (r : ℂ) * Complex.I + 1).im = s.im + r := by simp
    have habs : |s.im| - 200 ≤ |s.im + r| := by
      have h3 := abs_sub_abs_le_abs_sub s.im (-r)
      rw [sub_neg_eq_add, abs_neg] at h3
      have : |r| ≤ 200 := abs_le.mpr ⟨hr1, hr2⟩
      linarith
    have hk := hD δ (s + (r : ℂ) * Complex.I + 1) (by rw [hre]; linarith)
      (by rw [hre]; linarith) (by rw [him]; linarith) (by rw [him]; linarith)
    rw [him] at hk
    exact hk.trans (f1_anti (by linarith) (by linarith) habs)
  have hcont : Continuous fun r => ‖HP.Ah r‖ * f1 δ (|s.im| - 200) :=
    HP.continuous_Ah.norm.mul continuous_const
  have hint := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (-200 : ℝ) ≤ 200) (Eventually.of_forall fun r hr => hpt r hr.1.le hr.2)
    (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const] at hint
  have hf0 := f1_nonneg (δ := δ) (by linarith : (0 : ℝ) ≤ |s.im| - 200)
  have hmul := mul_le_mul_of_nonneg_right hI hf0
  have hp2 : 1 / (2 * Real.pi) ≤ 0.15924 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d2]
  have hP0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hX : 0 ≤ Real.sqrt (|s.im| - 200) * Real.exp (-0.1598 * (|s.im| - 200)) +
      (|s.im| - 200) / (2 * Real.pi * |δ|) *
        Real.exp (-0.1065 * ((|s.im| - 200) / (Real.pi * δ)) ^ 2) := by
    have : 0 ≤ (|s.im| - 200) / (2 * Real.pi * |δ|) :=
      div_nonneg (by linarith) (by positivity)
    positivity
  unfold HM.fplus
  unfold f1 at hmul
  calc 1 / (2 * Real.pi) * ‖∫ r in (-200 : ℝ)..200,
        HP.Ah r * mellin (phiD δ) (s + (r : ℂ) * Complex.I)‖
      ≤ 1 / (2 * Real.pi) * (18.2 * (3.1 * (Real.sqrt (|s.im| - 200) *
          Real.exp (-0.1598 * (|s.im| - 200)) + (|s.im| - 200) / (2 * Real.pi * |δ|) *
            Real.exp (-0.1065 * ((|s.im| - 200) / (Real.pi * δ)) ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hP0
        unfold f1 at hint
        linarith
    _ ≤ _ := by nlinarith

/-! ## (4) `AIntOf` -/

/-- **LINK [AIntOf] PROVED** -- the five-piece integration of the pointwise bounds. -/
theorem aIntOf_holds : AIntOf := by
  intro h0 h1 h2
  have hc : Continuous fun r => ‖HP.Ah r‖ := HP.continuous_Ah.norm
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun r => ‖HP.Ah r‖) volume a b :=
    fun a b => hc.intervalIntegrable a b
  -- the pointwise bounds
  have hB2 : ∀ r : ℝ, r ≠ 0 → ‖HP.Ah r‖ ≤ 10.792 * r ^ (-2 : ℤ) := by
    intro r hr
    have hr2 : 0 < r ^ 2 := by positivity
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ hr2]
    exact h2 r
  have hB1p : ∀ r : ℝ, 0 < r → ‖HP.Ah r‖ ≤ 3.2975 * r⁻¹ := by
    intro r hr
    rw [← div_eq_mul_inv, le_div_iff₀ hr]
    have := h1 r
    rwa [abs_of_pos hr] at this
  have hB1n : ∀ r : ℝ, r < 0 → ‖HP.Ah r‖ ≤ -(3.2975 * r⁻¹) := by
    intro r hr
    rw [← neg_mul, ← div_eq_mul_inv, le_div_iff_of_neg hr]
    have := h1 r
    rw [abs_of_neg hr] at this
    linarith
  -- integrability of the majorants
  have hz : ∀ a b : ℝ, (0 : ℝ) ∉ uIcc a b →
      IntervalIntegrable (fun r : ℝ => 10.792 * r ^ (-2 : ℤ)) volume a b :=
    fun a b h => (intervalIntegral.intervalIntegrable_zpow (Or.inr h)).const_mul _
  have hinv : ∀ a b : ℝ, (0 : ℝ) ∉ uIcc a b →
      IntervalIntegrable (fun r : ℝ => 3.2975 * r⁻¹) volume a b :=
    fun a b h => (intervalIntegral.intervalIntegrable_inv (fun x hx => by
      rintro rfl
      exact h hx) continuousOn_id).const_mul _
  have n1 : (0 : ℝ) ∉ uIcc (-200) (-3.2) := by
    rw [uIcc_of_le (by norm_num)]
    intro h
    linarith [h.2]
  have n2 : (0 : ℝ) ∉ uIcc (-3.2) (-1.6) := by
    rw [uIcc_of_le (by norm_num)]
    intro h
    linarith [h.2]
  have n4 : (0 : ℝ) ∉ uIcc 1.6 3.2 := by
    rw [uIcc_of_le (by norm_num)]
    intro h
    linarith [h.1]
  have n5 : (0 : ℝ) ∉ uIcc 3.2 200 := by
    rw [uIcc_of_le (by norm_num)]
    intro h
    linarith [h.1]
  -- the five pieces
  have p1 : ∫ r in (-200 : ℝ)..(-3.2), ‖HP.Ah r‖ ≤
      ∫ r in (-200 : ℝ)..(-3.2), 10.792 * r ^ (-2 : ℤ) :=
    intervalIntegral.integral_mono_on (by norm_num) (hii _ _) (hz _ _ n1) fun r hr =>
      hB2 r (by linarith [hr.2])
  have p2 : ∫ r in (-3.2 : ℝ)..(-1.6), ‖HP.Ah r‖ ≤
      ∫ r in (-3.2 : ℝ)..(-1.6), -(3.2975 * r⁻¹) :=
    intervalIntegral.integral_mono_on (by norm_num) (hii _ _) (hinv _ _ n2).neg fun r hr =>
      hB1n r (by linarith [hr.2])
  have p3 : ∫ r in (-1.6 : ℝ)..1.6, ‖HP.Ah r‖ ≤ ∫ _ in (-1.6 : ℝ)..1.6, (2.03 : ℝ) :=
    intervalIntegral.integral_mono_on (by norm_num) (hii _ _) intervalIntegrable_const
      fun r _ => h0 r
  have p4 : ∫ r in (1.6 : ℝ)..3.2, ‖HP.Ah r‖ ≤ ∫ r in (1.6 : ℝ)..3.2, 3.2975 * r⁻¹ :=
    intervalIntegral.integral_mono_on (by norm_num) (hii _ _) (hinv _ _ n4) fun r hr =>
      hB1p r (by linarith [hr.1])
  have p5 : ∫ r in (3.2 : ℝ)..200, ‖HP.Ah r‖ ≤ ∫ r in (3.2 : ℝ)..200, 10.792 * r ^ (-2 : ℤ) :=
    intervalIntegral.integral_mono_on (by norm_num) (hii _ _) (hz _ _ n5) fun r hr =>
      hB2 r (by linarith [hr.1])
  -- their values
  have v1 : ∫ r in (-200 : ℝ)..(-3.2), 10.792 * r ^ (-2 : ℤ) = 10.792 * (1 / 3.2 - 1 / 200) := by
    rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, n1⟩)]
    norm_num
  have v5 : ∫ r in (3.2 : ℝ)..200, 10.792 * r ^ (-2 : ℤ) = 10.792 * (1 / 3.2 - 1 / 200) := by
    rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, n5⟩)]
    norm_num
  have v2 : ∫ r in (-3.2 : ℝ)..(-1.6), -(3.2975 * r⁻¹) = 3.2975 * Real.log 2 := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, integral_inv n2,
      show (-1.6 : ℝ) / -3.2 = 2⁻¹ by norm_num, Real.log_inv]
    ring
  have v4 : ∫ r in (1.6 : ℝ)..3.2, 3.2975 * r⁻¹ = 3.2975 * Real.log 2 := by
    rw [intervalIntegral.integral_const_mul, integral_inv n4,
      show (3.2 : ℝ) / 1.6 = 2 by norm_num]
  have v3 : ∫ _ in (-1.6 : ℝ)..1.6, (2.03 : ℝ) = 2.03 * 3.2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  have hsplit : ∫ r in (-200 : ℝ)..200, ‖HP.Ah r‖ =
      ((((∫ r in (-200 : ℝ)..(-3.2), ‖HP.Ah r‖) + ∫ r in (-3.2 : ℝ)..(-1.6), ‖HP.Ah r‖) +
        ∫ r in (-1.6 : ℝ)..1.6, ‖HP.Ah r‖) + ∫ r in (1.6 : ℝ)..3.2, ‖HP.Ah r‖) +
          ∫ r in (3.2 : ℝ)..200, ‖HP.Ah r‖ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have hl := Real.log_two_lt_d9
  unfold AInt
  rw [hsplit]
  linarith

/-! ## (5) `HM.PlusDecay` from the two integration-by-parts links -/

/-- **`HM.PlusDecay` FROM `AC1` AND `AC2`** -- every other S4 link is discharged (`RayBound`,
`Moment1`, `Cases1`, `AC0`, `AIntOf`, `PlusBand`); citations: `E(1.5) ≥ 0.1598`
(`HC.AmanitaBisectCited`) and `C₂ ≤ 10.79195821038` (`HC.AppBCited`, consumed by `AC2`). -/
theorem plusDecay_of_ac12 (hc : HC.AmanitaBisectCited) (hb : HC.AppBCited) (h1 : AC1)
    (h2 : AC2) : HM.PlusDecay :=
  plusDecay_of_links hc hb rayBound_holds moment1_holds cases1_holds ac0_holds h1 h2
    aIntOf_holds plusBand_holds

end Principia.Common.TernaryGoldbach.S4
