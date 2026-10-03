/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

/-!
# Bessel and Parseval for the Fourier transform on `ℝ`, from the integral definition

Mathlib has Plancherel on `L²` (`MeasureTheory.Lp.norm_fourier_eq`), but the `L²` transform is
identified with the Fourier INTEGRAL `𝓕 f ξ = ∫ e(−yξ) f(y) dy` only for Schwartz functions
(`SchwartzMap.toLp_fourier_eq`). This file works with the integral directly, which is what a
consumer stating `∫ |𝓕 f|²` needs, for `f ∈ L¹ ∩ L²` with NO smoothness.

* **`bessel`** — `∫_{−w}^{w} |𝓕 f|² ≤ ‖f‖₂²` for `f ∈ L¹ ∩ L²`, by Gaussian regularisation:
  `∫ e^{−πcξ²}|𝓕 f(ξ)|² dξ = ∫∫ conj f(x) f(y) k_c(x − y)` (`fubini_conj`, `fubini_kernel`,
  `gauss_ft`), where `k_c(u) = c^{−1/2}e^{−πu²/c} ≥ 0` has `∫ k_c = 1` (`integral_kern`);
  AM–GM and translation invariance bound the double integral by `‖f‖₂²` (`double_le`);
  `∫_{−w}^{w} ≤ e^{πcw²}·∫ e^{−πcξ²}` (`interval_le_gauss`); let `c → 0⁺`.
* **`parseval`** — `∫ |𝓕 f|² = ∫ |f|²` for continuous `f ∈ L¹` with `𝓕 f ∈ L¹`, from
  `fubini_conj` and Mathlib's inversion theorem `Continuous.fourierInv_fourier_eq`.
* **`decay3`** — three integrations by parts: if `u₀, u₁, u₂` (with `u₀' = u₁`, `u₁' = u₂`,
  `u₂' = u₃`) vanish at `a` and `b`, then `|∫_a^b u₀ e(−tξ)| ≤ ∫_a^b |u₃| / (2π|ξ|)³`.
* **`tail_bound`** — under `|F(ξ)| ≤ L/(2π|ξ|)³` the two tails `|ξ| > w` of `∫ |F|²` cost at
  most `L²/(160π⁶w⁵)`.
* **`band_lower`** — `∫_{−w}^{w}|G + D|² ≥ ∫|G|² − 2√(∫|G|²)√(∫|D|²)` (Cauchy–Schwarz,
  `cs_real`, from its AM–GM family).

Everything is generic: no campaign object appears. The ternary-Goldbach instantiation is
`Principia.Common.TernaryGoldbach.DrujalPlancherel`.
-/

namespace Principia.Common.FourierBessel

open MeasureTheory Complex Filter Set Real
open scoped FourierTransform ComplexConjugate Topology

/-- `𝓕 f ξ = ∫ e^{−2πiyξ} f(y) dy`. -/
theorem fourier_eq_exp (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ y, cexp (↑(-2 * π * y * ξ) * I) * f y := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]

/-- `𝓕⁻ g x = ∫ e^{2πixv} g(v) dv`. -/
theorem fourierInv_eq_exp (g : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ g x = ∫ v, cexp (↑(2 * π * x * v) * I) * g v := by
  rw [fourierInv_eq']
  congr 1
  ext v
  simp only [smul_eq_mul]
  congr 3
  simp
  ring

/-- `conj (𝓕 f ξ) = ∫ e^{2πixξ} conj (f x) dx`. -/
theorem conj_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    conj (𝓕 f ξ) = ∫ x, cexp (↑(2 * π * x * ξ) * I) * conj (f x) := by
  rw [fourier_eq_exp, ← integral_conj]
  congr 1
  ext x
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- `|𝓕 f ξ| ≤ ‖f‖₁`. -/
theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ y, ‖f y‖ := by
  rw [fourier_eq_exp]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext y
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `𝓕 f` is continuous for `f ∈ L¹`. -/
theorem continuous_fourier (f : ℝ → ℂ) (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- **Fubini against `conj (𝓕 f)`**: `∫ G·conj(𝓕 f) = ∫_x conj(f x)·∫_ξ G(ξ)e^{2πixξ}` for
integrable `f, G`. -/
theorem fubini_conj (f G : ℝ → ℂ) (hf : Integrable f) (hG : Integrable G) :
    ∫ ξ, G ξ * conj (𝓕 f ξ) =
      ∫ x, conj (f x) * ∫ ξ, G ξ * cexp (↑(2 * π * x * ξ) * I) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun ξ x : ℝ =>
      G ξ * (cexp (↑(2 * π * x * ξ) * I) * conj (f x))) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1) (volume.prod volume) :=
      hG.1.comp_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (f p.2)) (volume.prod volume) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable hf.1).comp_snd
    have h3 : Continuous fun p : ℝ × ℝ => cexp (↑(2 * π * p.2 * p.1) * I) := by fun_prop
    exact h1.mul (h3.aestronglyMeasurable.mul h2)
  have hint : Integrable (Function.uncurry fun ξ x : ℝ =>
      G ξ * (cexp (↑(2 * π * x * ξ) * I) * conj (f x))) (volume.prod volume) := by
    refine (hG.norm.mul_prod hf.norm).mono' hm (ae_of_all _ fun p => ?_)
    obtain ⟨ξ, x⟩ := p
    simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I,
      RCLike.norm_conj, one_mul, le_refl]
  calc ∫ ξ, G ξ * conj (𝓕 f ξ)
      = ∫ ξ, ∫ x, G ξ * (cexp (↑(2 * π * x * ξ) * I) * conj (f x)) := by
        congr 1
        ext ξ
        rw [conj_fourier, integral_const_mul]
    _ = ∫ x, ∫ ξ, G ξ * (cexp (↑(2 * π * x * ξ) * I) * conj (f x)) :=
        integral_integral_swap hint
    _ = ∫ x, conj (f x) * ∫ ξ, G ξ * cexp (↑(2 * π * x * ξ) * I) := by
        congr 1
        ext x
        rw [← integral_const_mul (conj (f x))]
        congr 1
        ext ξ
        ring

/-- **Fubini inside `𝓕 f`**: `∫_ξ g(ξ)(𝓕 f)(ξ)e^{2πixξ} = ∫_y f(y)·∫_ξ g(ξ)e^{2πi(x−y)ξ}` for
integrable `f, g`. -/
theorem fubini_kernel (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    ∫ ξ, g ξ * 𝓕 f ξ * cexp (↑(2 * π * x * ξ) * I) =
      ∫ y, f y * ∫ ξ, g ξ * cexp (↑(2 * π * (x - y) * ξ) * I) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun ξ y : ℝ =>
      g ξ * cexp (↑(2 * π * x * ξ) * I) * (cexp (↑(-2 * π * y * ξ) * I) * f y))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1) (volume.prod volume) :=
      hg.1.comp_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (volume.prod volume) :=
      hf.1.comp_snd
    have h3 : Continuous fun p : ℝ × ℝ => cexp (↑(2 * π * x * p.1) * I) := by fun_prop
    have h4 : Continuous fun p : ℝ × ℝ => cexp (↑(-2 * π * p.2 * p.1) * I) := by fun_prop
    exact (h1.mul h3.aestronglyMeasurable).mul (h4.aestronglyMeasurable.mul h2)
  have hint : Integrable (Function.uncurry fun ξ y : ℝ =>
      g ξ * cexp (↑(2 * π * x * ξ) * I) * (cexp (↑(-2 * π * y * ξ) * I) * f y))
      (volume.prod volume) := by
    refine (hg.norm.mul_prod hf.norm).mono' hm (ae_of_all _ fun p => ?_)
    obtain ⟨ξ, y⟩ := p
    simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      mul_one, le_refl]
  calc ∫ ξ, g ξ * 𝓕 f ξ * cexp (↑(2 * π * x * ξ) * I)
      = ∫ ξ, ∫ y, g ξ * cexp (↑(2 * π * x * ξ) * I) *
          (cexp (↑(-2 * π * y * ξ) * I) * f y) := by
        congr 1
        ext ξ
        have e : ∫ y, g ξ * cexp (↑(2 * π * x * ξ) * I) * (cexp (↑(-2 * π * y * ξ) * I) * f y) =
            g ξ * cexp (↑(2 * π * x * ξ) * I) * ∫ y, cexp (↑(-2 * π * y * ξ) * I) * f y :=
          integral_const_mul _ _
        rw [e, fourier_eq_exp]
        ring
    _ = ∫ y, ∫ ξ, g ξ * cexp (↑(2 * π * x * ξ) * I) *
          (cexp (↑(-2 * π * y * ξ) * I) * f y) :=
        integral_integral_swap hint
    _ = ∫ y, f y * ∫ ξ, g ξ * cexp (↑(2 * π * (x - y) * ξ) * I) := by
        congr 1
        ext y
        rw [← integral_const_mul (f y)]
        congr 1
        ext ξ
        have e : cexp (↑(2 * π * (x - y) * ξ) * I) =
            cexp (↑(2 * π * x * ξ) * I) * cexp (↑(-2 * π * y * ξ) * I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [e]
        ring

/-- The Gaussian weight `e^{−π c ξ²}`, as a complex-valued function. -/
noncomputable def gauss (c ξ : ℝ) : ℂ := ((Real.exp (-(π * c) * ξ ^ 2) : ℝ) : ℂ)

/-- The heat kernel `c^{−1/2} e^{−π u²/c}`: the Fourier transform of `gauss c`. -/
noncomputable def kern (c u : ℝ) : ℝ := Real.sqrt c⁻¹ * Real.exp (-π * u ^ 2 / c)

/-- **The Gaussian integral**: `∫ e^{−πcξ²}e^{2πiuξ} dξ = kern c u`. -/
theorem gauss_ft (c : ℝ) (hc : 0 < c) (u : ℝ) :
    ∫ ξ, gauss c ξ * cexp (↑(2 * π * u * ξ) * I) = (kern c u : ℂ) := by
  have hb : 0 < ((π * c : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have h := fourierIntegral_gaussian hb ((2 * π * u : ℝ) : ℂ)
  have e1 : ∀ ξ : ℝ, gauss c ξ * cexp (↑(2 * π * u * ξ) * I) =
      cexp (I * ((2 * π * u : ℝ) : ℂ) * ξ) * cexp (-((π * c : ℝ) : ℂ) * ξ ^ 2) := by
    intro ξ
    rw [gauss, Complex.ofReal_exp, mul_comm]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  simp_rw [e1]
  rw [h]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e2 : (π : ℂ) / ((π * c : ℝ) : ℂ) = ((c⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e3 : -((2 * π * u : ℝ) : ℂ) ^ 2 / (4 * ((π * c : ℝ) : ℂ)) =
      ((-π * u ^ 2 / c : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  have e4 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e2, e3, e4, ← Complex.ofReal_cpow (inv_nonneg.mpr hc.le), ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, kern, Real.sqrt_eq_rpow]

/-- `kern c u ≥ 0`. -/
theorem kern_nonneg (c u : ℝ) : 0 ≤ kern c u :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- `kern c` is continuous. -/
theorem continuous_kern (c : ℝ) : Continuous (kern c) := by
  unfold kern
  fun_prop

/-- `kern c u = c^{−1/2}e^{−(π/c)u²}`. -/
theorem kern_eq (c : ℝ) :
    kern c = fun u => Real.sqrt c⁻¹ * Real.exp (-(π / c) * u ^ 2) := by
  funext u
  rw [kern, show -(π / c) * u ^ 2 = -π * u ^ 2 / c by ring]

/-- `kern c ∈ L¹` for `c > 0`. -/
theorem integrable_kern (c : ℝ) (hc : 0 < c) : Integrable (kern c) := by
  rw [kern_eq]
  exact (integrable_exp_neg_mul_sq (b := π / c) (by positivity)).const_mul _

/-- `∫ kern c = 1` for `c > 0`. -/
theorem integral_kern (c : ℝ) (hc : 0 < c) : ∫ u, kern c u = 1 := by
  have hπ := Real.pi_pos.ne'
  rw [kern_eq, integral_const_mul, integral_gaussian,
    show π / (π / c) = c by field_simp, ← Real.sqrt_mul (by positivity),
    inv_mul_cancel₀ hc.ne', Real.sqrt_one]

/-- **The double integral is at most `‖f‖₂²`** for a nonnegative kernel of mass `1`:
`|∫∫ conj f(x) f(y) k(x − y)| ≤ ∫|f|²` (AM–GM, then translation invariance). -/
theorem double_le (f : ℝ → ℂ) (hfm : StronglyMeasurable f)
    (hf2 : Integrable fun t => ‖f t‖ ^ 2) (k : ℝ → ℝ) (hkc : Continuous k)
    (hk0 : ∀ u, 0 ≤ k u) (hki : Integrable k) (hk1 : ∫ u, k u = 1) :
    ‖∫ x, conj (f x) * ∫ y, f y * (k (x - y) : ℂ)‖ ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hA : Measurable fun x => ‖f x‖ := hfm.measurable.norm
  have hkl : ∫⁻ u, ENNReal.ofReal (k u) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hki (ae_of_all _ hk0), hk1, ENNReal.ofReal_one]
  have ht : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (k (x - y)) = 1 := fun x =>
    (lintegral_sub_left_eq_self (μ := volume) (fun u => ENNReal.ofReal (k u)) x).trans hkl
  have ht' : ∀ y : ℝ, ∫⁻ x, ENNReal.ofReal (k (x - y)) = 1 := fun y =>
    (lintegral_sub_right_eq_self (μ := volume) (fun u => ENNReal.ofReal (k u)) y).trans hkl
  have hcm : ∀ (a : ℝ) (x : ℝ), 0 ≤ a →
      ∫⁻ y, ENNReal.ofReal (a * k (x - y)) = ENNReal.ofReal a := by
    intro a x ha
    have e : (fun y => ENNReal.ofReal (a * k (x - y))) =
        fun y => ENNReal.ofReal a * ENNReal.ofReal (k (x - y)) := by
      funext y
      rw [ENNReal.ofReal_mul ha]
    rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ht, mul_one]
  have hcm' : ∀ (a : ℝ) (y : ℝ), 0 ≤ a →
      ∫⁻ x, ENNReal.ofReal (a * k (x - y)) = ENNReal.ofReal a := by
    intro a y ha
    have e : (fun x => ENNReal.ofReal (a * k (x - y))) =
        fun x => ENNReal.ofReal a * ENNReal.ofReal (k (x - y)) := by
      funext x
      rw [ENNReal.ofReal_mul ha]
    rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ht', mul_one]
  have hin : ∀ x, ENNReal.ofReal ‖conj (f x) * ∫ y, f y * (k (x - y) : ℂ)‖ ≤
      ENNReal.ofReal (‖f x‖ ^ 2 / 2) +
        ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / 2 * k (x - y)) := by
    intro x
    have h1 : ENNReal.ofReal ‖∫ y, f y * (k (x - y) : ℂ)‖ ≤
        ∫⁻ y, ENNReal.ofReal (‖f y‖ * k (x - y)) := by
      rw [ofReal_norm]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      congr 1
      ext y
      rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hk0 _)]
    have hmeas : Measurable fun y => ENNReal.ofReal (‖f x‖ ^ 2 / 2 * k (x - y)) :=
      (measurable_const.mul
        (hkc.measurable.comp (measurable_const.sub measurable_id))).ennreal_ofReal
    calc ENNReal.ofReal ‖conj (f x) * ∫ y, f y * (k (x - y) : ℂ)‖
        = ENNReal.ofReal ‖f x‖ * ENNReal.ofReal ‖∫ y, f y * (k (x - y) : ℂ)‖ := by
          rw [norm_mul, RCLike.norm_conj, ENNReal.ofReal_mul (norm_nonneg _)]
      _ ≤ ENNReal.ofReal ‖f x‖ * ∫⁻ y, ENNReal.ofReal (‖f y‖ * k (x - y)) := by gcongr
      _ = ∫⁻ y, ENNReal.ofReal (‖f x‖ * (‖f y‖ * k (x - y))) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          ext y
          rw [ENNReal.ofReal_mul (norm_nonneg (f x))]
      _ ≤ ∫⁻ y, (ENNReal.ofReal (‖f x‖ ^ 2 / 2 * k (x - y)) +
            ENNReal.ofReal (‖f y‖ ^ 2 / 2 * k (x - y))) := by
          refine lintegral_mono fun y => ?_
          have hk := hk0 (x - y)
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg (sq_nonneg (‖f x‖ - ‖f y‖)) hk]
      _ = ENNReal.ofReal (‖f x‖ ^ 2 / 2) +
            ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / 2 * k (x - y)) := by
          rw [lintegral_add_left hmeas, hcm _ x (by positivity)]
  have hsq : Measurable fun x => ENNReal.ofReal (‖f x‖ ^ 2 / 2) :=
    ((hA.pow_const 2).div_const 2).ennreal_ofReal
  have hprod : AEMeasurable (Function.uncurry fun x y : ℝ =>
      ENNReal.ofReal (‖f y‖ ^ 2 / 2 * k (x - y))) (volume.prod volume) :=
    ((((hA.comp measurable_snd).pow_const 2).div_const 2).mul
      (hkc.measurable.comp (measurable_fst.sub measurable_snd))).ennreal_ofReal.aemeasurable
  have htot : ∫⁻ x, ENNReal.ofReal ‖conj (f x) * ∫ y, f y * (k (x - y) : ℂ)‖ ≤
      ENNReal.ofReal (∫ x, ‖f x‖ ^ 2) := by
    calc ∫⁻ x, ENNReal.ofReal ‖conj (f x) * ∫ y, f y * (k (x - y) : ℂ)‖
        ≤ ∫⁻ x, (ENNReal.ofReal (‖f x‖ ^ 2 / 2) +
            ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / 2 * k (x - y))) := lintegral_mono hin
      _ = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 / 2)) +
            ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / 2 * k (x - y)) := lintegral_add_left hsq _
      _ = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 / 2)) + ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / 2) := by
          rw [lintegral_lintegral_swap hprod]
          congr 1
          congr 1
          ext y
          exact hcm' _ y (by positivity)
      _ = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
          rw [← lintegral_add_left hsq]
          congr 1
          ext x
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun x => by positivity)).symm
  exact (norm_integral_le_lintegral_norm _).trans
    (ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => by positivity) htot)

/-- **The Gaussian-weighted Bessel inequality**: `∫ e^{−πcξ²}|𝓕 f(ξ)|² ≤ ‖f‖₂²`. -/
theorem gauss_bound (f : ℝ → ℂ) (hfm : StronglyMeasurable f) (hf : Integrable f)
    (hf2 : Integrable fun t => ‖f t‖ ^ 2) (c : ℝ) (hc : 0 < c) :
    ∫ ξ, Real.exp (-(π * c) * ξ ^ 2) * ‖𝓕 f ξ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hgi : Integrable (gauss c) :=
    (integrable_exp_neg_mul_sq (b := π * c) (by positivity)).ofReal
  have hG : Integrable fun ξ => gauss c ξ * 𝓕 f ξ :=
    hgi.mul_bdd (continuous_fourier f hf).aestronglyMeasurable
      (ae_of_all _ fun ξ => norm_fourier_le f ξ)
  have h1 := fubini_conj f (fun ξ => gauss c ξ * 𝓕 f ξ) hf hG
  have h2 : ∀ x, ∫ ξ, gauss c ξ * 𝓕 f ξ * cexp (↑(2 * π * x * ξ) * I) =
      ∫ y, f y * (kern c (x - y) : ℂ) := by
    intro x
    rw [fubini_kernel f (gauss c) hf hgi x]
    congr 1
    ext y
    rw [gauss_ft c hc (x - y)]
  have hL : ∫ ξ, gauss c ξ * 𝓕 f ξ * conj (𝓕 f ξ) =
      ((∫ ξ, Real.exp (-(π * c) * ξ ^ 2) * ‖𝓕 f ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext ξ
    rw [mul_assoc, Complex.mul_conj', gauss, Complex.ofReal_mul, Complex.ofReal_pow]
  simp only [h2] at h1
  rw [hL] at h1
  have hb := double_le f hfm hf2 (kern c) (continuous_kern c) (kern_nonneg c)
    (integrable_kern c hc) (integral_kern c hc)
  rw [← h1, Complex.norm_real, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb

/-- `∫_{−w}^{w}|F|² ≤ e^{πcw²}∫ e^{−πcξ²}|F(ξ)|²` for a bounded continuous `F`. -/
theorem interval_le_gauss (F : ℝ → ℂ) (hF : Continuous F) (C : ℝ) (hC : ∀ ξ, ‖F ξ‖ ≤ C)
    (c : ℝ) (hc : 0 < c) (w : ℝ) (hw : 0 ≤ w) :
    ∫ ξ in (-w)..w, ‖F ξ‖ ^ 2 ≤
      Real.exp (π * c * w ^ 2) * ∫ ξ, Real.exp (-(π * c) * ξ ^ 2) * ‖F ξ‖ ^ 2 := by
  have hint : Integrable fun ξ => Real.exp (-(π * c) * ξ ^ 2) * ‖F ξ‖ ^ 2 := by
    refine (integrable_exp_neg_mul_sq (b := π * c) (by positivity)).mul_bdd
      (hF.norm.pow 2).aestronglyMeasurable (c := C ^ 2) (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC ξ) 2
  have hcont : Continuous fun ξ => Real.exp (-(π * c) * ξ ^ 2) * ‖F ξ‖ ^ 2 := by fun_prop
  calc ∫ ξ in (-w)..w, ‖F ξ‖ ^ 2
      ≤ ∫ ξ in (-w)..w, Real.exp (π * c * w ^ 2) *
          (Real.exp (-(π * c) * ξ ^ 2) * ‖F ξ‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((hF.norm.pow 2).intervalIntegrable _ _)
          ((continuous_const.mul hcont).intervalIntegrable _ _) fun ξ hξ => ?_
        rw [← mul_assoc, ← Real.exp_add]
        have hξ2 : ξ ^ 2 ≤ w ^ 2 := sq_le_sq' hξ.1 hξ.2
        have h1 : 1 ≤ Real.exp (π * c * w ^ 2 + -(π * c) * ξ ^ 2) := by
          refine Real.one_le_exp ?_
          nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hc.le) (sub_nonneg.mpr hξ2)]
        exact le_mul_of_one_le_left (by positivity) h1
    _ = Real.exp (π * c * w ^ 2) *
          ∫ ξ in (-w)..w, Real.exp (-(π * c) * ξ ^ 2) * ‖F ξ‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp (π * c * w ^ 2) * ∫ ξ, Real.exp (-(π * c) * ξ ^ 2) * ‖F ξ‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hint (ae_of_all _ fun ξ => by positivity)

/-- **Bessel's inequality on a band, for `f ∈ L¹ ∩ L²`**:
`∫_{−w}^{w} |𝓕 f|² ≤ ‖f‖₂²`. -/
theorem bessel (f : ℝ → ℂ) (hf : Integrable f) (hf2 : Integrable fun t => ‖f t‖ ^ 2)
    (w : ℝ) (hw : 0 ≤ w) : ∫ ξ in (-w)..w, ‖𝓕 f ξ‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 := by
  have hae : f =ᵐ[volume] hf.1.mk f := hf.1.ae_eq_mk
  have hF : 𝓕 f = 𝓕 (hf.1.mk f) := funext (Real.fourier_congr_ae hae)
  have hI : ∫ t, ‖f t‖ ^ 2 = ∫ t, ‖hf.1.mk f t‖ ^ 2 :=
    integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  have hfi' : Integrable (hf.1.mk f) := hf.congr hae
  have hf2' : Integrable fun t => ‖hf.1.mk f t‖ ^ 2 :=
    hf2.congr (hae.mono fun t ht => by simp only [ht])
  rw [hF, hI]
  have key : ∀ c : ℝ, 0 < c → ∫ ξ in (-w)..w, ‖𝓕 (hf.1.mk f) ξ‖ ^ 2 ≤
      Real.exp (π * c * w ^ 2) * ∫ t, ‖hf.1.mk f t‖ ^ 2 := by
    intro c hc
    refine (interval_le_gauss (𝓕 (hf.1.mk f)) (continuous_fourier _ hfi') _
      (norm_fourier_le _) c hc w hw).trans ?_
    exact mul_le_mul_of_nonneg_left
      (gauss_bound _ hf.1.stronglyMeasurable_mk hfi' hf2' c hc) (Real.exp_pos _).le
  have hlim : Tendsto (fun c : ℝ => Real.exp (π * c * w ^ 2) * ∫ t, ‖hf.1.mk f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 (∫ t, ‖hf.1.mk f t‖ ^ 2)) := by
    have hcont : Continuous fun c : ℝ => Real.exp (π * c * w ^ 2) * ∫ t, ‖hf.1.mk f t‖ ^ 2 := by
      fun_prop
    have h0 := hcont.tendsto 0
    simp only [mul_zero, zero_mul, Real.exp_zero, one_mul] at h0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun c hc => key c hc)

/-- **Parseval** for a continuous `f ∈ L¹` with `𝓕 f ∈ L¹`: `‖𝓕 f‖₂² = ‖f‖₂²`. -/
theorem parseval (f : ℝ → ℂ) (hc : Continuous f) (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  have h1 := fubini_conj f (𝓕 f) hf hF
  have hinv : ∀ x, ∫ ξ, 𝓕 f ξ * cexp (↑(2 * π * x * ξ) * I) = f x := by
    intro x
    rw [← congrFun (hc.fourierInv_fourier_eq hf hF) x, fourierInv_eq_exp]
    congr 1
    ext ξ
    ring
  simp only [hinv] at h1
  have hL : ∫ ξ, 𝓕 f ξ * conj (𝓕 f ξ) = ((∫ ξ, ‖𝓕 f ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext ξ
    rw [Complex.mul_conj', Complex.ofReal_pow]
  have hR : ∫ x, conj (f x) * f x = ((∫ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext x
    rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [hL, hR] at h1
  exact_mod_cast h1

/-- One integration by parts against `e(−tξ)` on `[a, b]`, the boundary terms vanishing:
`2πiξ·∫ u e(−tξ) = ∫ u' e(−tξ)`. -/
theorem ibp_step (a b ξ : ℝ) (u u' : ℝ → ℝ) (hu : ∀ t, HasDerivAt u (u' t) t)
    (hc : Continuous u') (ha : u a = 0) (hb : u b = 0) :
    (2 * π * ξ * I) * ∫ t in a..b, (u t : ℂ) * cexp (↑(-2 * π * t * ξ) * I) =
      ∫ t in a..b, (u' t : ℂ) * cexp (↑(-2 * π * t * ξ) * I) := by
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (↑(-2 * π * t * ξ) * I))
      ((↑(-2 * π * ξ) * I) * cexp (↑(-2 * π * t * ξ) * I)) t := by
    intro t
    have h1 := ((((hasDerivAt_id' t).const_mul (-2 * π)).mul_const ξ).ofReal_comp.mul_const
      I).cexp
    refine h1.congr_deriv ?_
    rw [mul_one]
    ring
  have hU : ∀ t ∈ uIcc a b, HasDerivAt (fun t => (u t : ℂ)) (u' t : ℂ) t :=
    fun t _ => (hu t).ofReal_comp
  have hV : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => cexp (↑(-2 * π * t * ξ) * I))
      ((↑(-2 * π * ξ) * I) * cexp (↑(-2 * π * t * ξ) * I)) t := fun t _ => hv t
  have hU' : IntervalIntegrable (fun t => (u' t : ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp hc).intervalIntegrable _ _
  have hV' : IntervalIntegrable
      (fun t : ℝ => (↑(-2 * π * ξ) * I) * cexp (↑(-2 * π * t * ξ) * I)) volume a b :=
    (by fun_prop : Continuous fun t : ℝ =>
      (↑(-2 * π * ξ) * I) * cexp (↑(-2 * π * t * ξ) * I)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hV hU' hV'
  rw [ha, hb] at hibp
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at hibp
  have e : ∫ t in a..b, (u t : ℂ) * ((↑(-2 * π * ξ) * I) * cexp (↑(-2 * π * t * ξ) * I)) =
      (↑(-2 * π * ξ) * I) * ∫ t in a..b, (u t : ℂ) * cexp (↑(-2 * π * t * ξ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [e] at hibp
  have hc' : (2 * π * ξ * I : ℂ) = -(↑(-2 * π * ξ) * I) := by
    push_cast
    ring
  rw [hc', neg_mul, hibp, neg_neg]

/-- **Three integrations by parts** (`eq:madge`): if `u₀, u₁, u₂` vanish at `a` and `b`, then
`|∫_a^b u₀(t) e(−tξ) dt| ≤ ∫_a^b |u₃| / (2π|ξ|)³`. -/
theorem decay3 (a b ξ : ℝ) (hab : a ≤ b) (hξ : ξ ≠ 0) (u0 u1 u2 u3 : ℝ → ℝ)
    (h0 : ∀ t, HasDerivAt u0 (u1 t) t) (h1 : ∀ t, HasDerivAt u1 (u2 t) t)
    (h2 : ∀ t, HasDerivAt u2 (u3 t) t) (hc3 : Continuous u3)
    (ha0 : u0 a = 0) (hb0 : u0 b = 0) (ha1 : u1 a = 0) (hb1 : u1 b = 0)
    (ha2 : u2 a = 0) (hb2 : u2 b = 0) :
    ‖∫ t in a..b, (u0 t : ℂ) * cexp (↑(-2 * π * t * ξ) * I)‖ ≤
      (∫ t in a..b, |u3 t|) / (2 * π * |ξ|) ^ 3 := by
  have hc2 : Continuous u2 := continuous_iff_continuousAt.2 fun t => (h2 t).continuousAt
  have hc1 : Continuous u1 := continuous_iff_continuousAt.2 fun t => (h1 t).continuousAt
  have s0 := ibp_step a b ξ u0 u1 h0 hc1 ha0 hb0
  have s1 := ibp_step a b ξ u1 u2 h1 hc2 ha1 hb1
  have s2 := ibp_step a b ξ u2 u3 h2 hc3 ha2 hb2
  have hJ : (2 * π * ξ * I) ^ 3 * ∫ t in a..b, (u0 t : ℂ) * cexp (↑(-2 * π * t * ξ) * I) =
      ∫ t in a..b, (u3 t : ℂ) * cexp (↑(-2 * π * t * ξ) * I) := by
    rw [← s2, ← s1, ← s0]
    ring
  have hn3 : ‖∫ t in a..b, (u3 t : ℂ) * cexp (↑(-2 * π * t * ξ) * I)‖ ≤
      ∫ t in a..b, |u3 t| := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    congr 1
    ext t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hξ' : 0 < |ξ| := abs_pos.mpr hξ
  have hnorm : ‖(2 * π * ξ * I : ℂ) ^ 3‖ = (2 * π * |ξ|) ^ 3 := by
    rw [norm_pow, norm_mul, Complex.norm_I, mul_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [le_div_iff₀ (by positivity), ← hnorm, mul_comm, ← norm_mul, hJ]
  exact hn3

/-- **The two tails of `∫|F|²`** under `|F(ξ)| ≤ L/(2π|ξ|)³`:
`∫_{−w}^{w}|F|² ≥ ∫_ℝ |F|² − L²/(160π⁶w⁵)`. -/
theorem tail_bound (F : ℝ → ℂ) (hF2 : Integrable fun ξ => ‖F ξ‖ ^ 2) (L : ℝ)
    (hdec : ∀ ξ, ξ ≠ 0 → ‖F ξ‖ ≤ L / (2 * π * |ξ|) ^ 3) (w : ℝ) (hw : 0 < w) :
    (∫ ξ, ‖F ξ‖ ^ 2) - L ^ 2 / (160 * π ^ 6 * w ^ 5) ≤ ∫ ξ in (-w)..w, ‖F ξ‖ ^ 2 := by
  have hπ := Real.pi_pos.ne'
  have hpt : ∀ ξ : ℝ, w < ξ → ∀ s : ℝ, |s| = ξ →
      ‖F s‖ ^ 2 ≤ L ^ 2 / (64 * π ^ 6) * ξ ^ (-6 : ℝ) := by
    intro ξ hξ s hs
    have hξ0 : 0 < ξ := hw.trans hξ
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hs
      linarith
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hdec s hs0) 2
    rw [hs] at h1
    rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hξ0.le, Real.rpow_natCast]
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  have hIc : IntegrableOn (fun ξ : ℝ => L ^ 2 / (64 * π ^ 6) * ξ ^ (-6 : ℝ)) (Ioi w) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hw).const_mul _
  have hIB : ∫ ξ in Ioi w, L ^ 2 / (64 * π ^ 6) * ξ ^ (-6 : ℝ) =
      L ^ 2 / (64 * π ^ 6) * ((w ^ 5)⁻¹ / 5) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hw]
    rw [show (-6 : ℝ) + 1 = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hw.le, Real.rpow_natCast]
    ring
  have hR : ∫ ξ in Ioi w, ‖F ξ‖ ^ 2 ≤ ∫ ξ in Ioi w, L ^ 2 / (64 * π ^ 6) * ξ ^ (-6 : ℝ) :=
    setIntegral_mono_on hF2.integrableOn hIc measurableSet_Ioi fun ξ hξ =>
      hpt ξ hξ ξ (abs_of_pos (hw.trans hξ))
  have hneg : Integrable fun ξ => ‖F (-ξ)‖ ^ 2 := hF2.comp_neg
  have hL' : ∫ ξ in Ioi w, ‖F (-ξ)‖ ^ 2 ≤ ∫ ξ in Ioi w, L ^ 2 / (64 * π ^ 6) * ξ ^ (-6 : ℝ) :=
    setIntegral_mono_on hneg.integrableOn hIc measurableSet_Ioi fun ξ hξ =>
      hpt ξ hξ (-ξ) (by rw [abs_neg, abs_of_pos (hw.trans hξ)])
  have hs1 := intervalIntegral.integral_Iic_add_Ioi (b := w) hF2.integrableOn hF2.integrableOn
  have hs2 := intervalIntegral.integral_Iic_sub_Iic (a := -w) (b := w) hF2.integrableOn
    hF2.integrableOn
  have hs3 := integral_comp_neg_Ioi w (fun ξ => ‖F ξ‖ ^ 2)
  have hT : L ^ 2 / (160 * π ^ 6 * w ^ 5) = 2 * (L ^ 2 / (64 * π ^ 6) * ((w ^ 5)⁻¹ / 5)) := by
    field_simp
    ring
  rw [hT, ← hs2]
  rw [hIB] at hR hL'
  linarith

/-- `x² − 2xy ≤ z²` whenever `0 ≤ x ≤ z + y`. -/
theorem aux_sq (x y z : ℝ) (hx : 0 ≤ x) (h : x ≤ z + y) :
    x ^ 2 - 2 * x * y ≤ z ^ 2 := by
  rcases le_or_gt y x with hxy | hxy
  · have h1 : x - y ≤ z := by linarith
    have h2 : (x - y) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [sq_nonneg y]
  · nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 2 * y - x), sq_nonneg z]

/-- **Cauchy–Schwarz from its AM–GM family**: `2X ≤ lA + B/l` for every `l > 0` forces
`X ≤ √A·√B`. -/
theorem cs_real (A B X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * X ≤ l * A + B / l) : X ≤ Real.sqrt A * Real.sqrt B := by
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · rw [← hA0, Real.sqrt_zero, zero_mul]
    refine le_of_not_gt fun hX => ?_
    have h1 := h ((B + 1) / X) (by positivity)
    rw [← hA0, mul_zero, zero_add] at h1
    have h2 : B / ((B + 1) / X) < X := by
      rw [div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases eq_or_lt_of_le hB with hB0 | hB0
  · rw [← hB0, Real.sqrt_zero, mul_zero]
    refine le_of_not_gt fun hX => ?_
    have h1 := h (X / (A + 1)) (by positivity)
    rw [← hB0, zero_div, add_zero] at h1
    have h2 : X / (A + 1) * A < X := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  · obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ A = a * a :=
      ⟨Real.sqrt A, Real.sqrt_pos.2 hA0, (Real.mul_self_sqrt hA).symm⟩
    obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ B = b * b :=
      ⟨Real.sqrt B, Real.sqrt_pos.2 hB0, (Real.mul_self_sqrt hB).symm⟩
    rw [Real.sqrt_mul_self ha.le, Real.sqrt_mul_self hb.le]
    have h1 := h (b / a) (by positivity)
    have e : b / a * (a * a) + b * b / (b / a) = 2 * (a * b) := by
      field_simp
      ring
    rw [e] at h1
    linarith

/-- **The band inequality in `L²([−w, w])`**, for continuous `G, D`:
`∫|G + D|² ≥ ∫|G|² − 2√(∫|G|²)√(∫|D|²)`. -/
theorem band_lower (G D : ℝ → ℂ) (hG : Continuous G) (hD : Continuous D) (w : ℝ)
    (hw : 0 ≤ w) :
    (∫ ξ in (-w)..w, ‖G ξ‖ ^ 2) - 2 * Real.sqrt (∫ ξ in (-w)..w, ‖G ξ‖ ^ 2) *
      Real.sqrt (∫ ξ in (-w)..w, ‖D ξ‖ ^ 2) ≤ ∫ ξ in (-w)..w, ‖G ξ + D ξ‖ ^ 2 := by
  have hww : -w ≤ w := by linarith
  have iG : IntervalIntegrable (fun ξ => ‖G ξ‖ ^ 2) volume (-w) w :=
    (hG.norm.pow 2).intervalIntegrable _ _
  have iD : IntervalIntegrable (fun ξ => ‖D ξ‖ ^ 2) volume (-w) w :=
    (hD.norm.pow 2).intervalIntegrable _ _
  have iGD : IntervalIntegrable (fun ξ => ‖G ξ‖ * ‖D ξ‖) volume (-w) w :=
    (hG.norm.mul hD.norm).intervalIntegrable _ _
  have iS : IntervalIntegrable (fun ξ => ‖G ξ + D ξ‖ ^ 2) volume (-w) w :=
    ((hG.add hD).norm.pow 2).intervalIntegrable _ _
  have hA : 0 ≤ ∫ ξ in (-w)..w, ‖G ξ‖ ^ 2 :=
    intervalIntegral.integral_nonneg hww fun ξ _ => by positivity
  have hB : 0 ≤ ∫ ξ in (-w)..w, ‖D ξ‖ ^ 2 :=
    intervalIntegral.integral_nonneg hww fun ξ _ => by positivity
  have hAM : ∀ l : ℝ, 0 < l → 2 * (∫ ξ in (-w)..w, ‖G ξ‖ * ‖D ξ‖) ≤
      l * (∫ ξ in (-w)..w, ‖G ξ‖ ^ 2) + (∫ ξ in (-w)..w, ‖D ξ‖ ^ 2) / l := by
    intro l hl
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_div, ← intervalIntegral.integral_add
        (iG.const_mul l) (iD.div_const l)]
    refine intervalIntegral.integral_mono_on hww (iGD.const_mul 2)
      ((iG.const_mul l).add (iD.div_const l)) fun ξ _ => ?_
    have e : l * ‖G ξ‖ ^ 2 + ‖D ξ‖ ^ 2 / l - 2 * (‖G ξ‖ * ‖D ξ‖) =
        (l * ‖G ξ‖ - ‖D ξ‖) ^ 2 / l := by
      field_simp
      ring
    have : 0 ≤ (l * ‖G ξ‖ - ‖D ξ‖) ^ 2 / l := by positivity
    linarith
  have hcs := cs_real _ _ _ hA hB hAM
  have hpt : ∫ ξ in (-w)..w, (‖G ξ‖ ^ 2 - 2 * (‖G ξ‖ * ‖D ξ‖)) ≤
      ∫ ξ in (-w)..w, ‖G ξ + D ξ‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hww (iG.sub (iGD.const_mul 2)) iS fun ξ _ => ?_
    have h1 : ‖G ξ‖ ≤ ‖G ξ + D ξ‖ + ‖D ξ‖ := by
      have := norm_add_le (G ξ + D ξ) (-D ξ)
      rwa [add_neg_cancel_right, norm_neg] at this
    have := aux_sq _ _ _ (norm_nonneg (G ξ)) h1
    linarith
  rw [intervalIntegral.integral_sub iG (iGD.const_mul 2),
    intervalIntegral.integral_const_mul] at hpt
  linarith

end Principia.Common.FourierBessel
