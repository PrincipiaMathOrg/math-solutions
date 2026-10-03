/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajKolona
import Principia.Common.FourierBessel
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

/-!
# `lem:hausierer`, corrected — the spine, with `CritDeriv` PROVED

**`hausierer_of : AbelZeros → CritDeriv → RealSym → Hausierer`**, and `critDeriv_holds`, so
`hausierer_of' : AbelZeros → RealSym → Hausierer`. The link `HM.Hausierer` (majarcs 3389–3524, with
the referee's corrections F1, F2, F8 in its constants `hbC`, `hbR`) is split into:

| sub-link | content | status |
|---|---|---|
| Mellin–Plancherel | `crit_bessel`: `∫_{−T}^{T}|G_δ(½+iτ)|² ≤ 2π|η|₂²` | PROVED (here) |
| `CritDeriv` | `τ ↦ G_δ(½+iτ)` has derivative `i·G'_δ`, `G' = M((log t)η e(δt))` | PROVED (here) |
| `AbelZeros` | partial summation over zeros, `N = M + O*(g)`, `F ∈ C¹` | named (ELEM) |
| `RealSym` | zeros of `L(s,χ)`, `χ` real, symmetric under `s ↦ s̄` with multiplicity | named |

`crit_bessel` comes from the library's generic `FourierBessel.bessel` (`∫_{−w}^{w}|𝓕f|² ≤ ‖f‖₂²`,
`f ∈ L¹ ∩ L²`) and Mathlib's `mellin_eq_fourier` (`t = e^{−u}`: `G_δ(½ + iτ) = 𝓕φ(τ/2π)`,
`φ(u) = e^{−u/2}η(e^{−u})e(δe^{−u})`, `‖φ‖₂² = |η|₂²`). The Bessel INEQUALITY is all the lemma
needs; no Plancherel identity is used.

## The proof of the corrected lemma (`hausierer_of`)

GRH to `T` puts every zero with `|γ| ≤ T` at `½ + iγ`. Low zeros (`|γ| ≤ 1`): `|G| ≤ |η/√t|₁`
(`norm_gcl_le`) times `N(1) ≤ 0.819 log q + 16.8` (`zcount_one_le`). High zeros: with
`F_ε(t) = √(|G(½+it)|² + |G(½−it)|² + ε²)` (complex `χ`, `smooth_c`) — or, for real `χ`, pairing
`ρ ↔ ρ̄` (`zsum_conj`) and `F_ε(t) = √(|G(½+it)|² + ε²) + √(|G(½−it)|² + ε²)` (`smooth_r`) —
`AbelZeros` and Cauchy–Schwarz (`high_bound`, `cs_interval`) give
`A√T(log qT − 2.33787)/π + C(g(T) + g(1)) + B√T(½log qT + 17.21)` with
`∫_1^T F_ε² ≤ A²` (`crit_bessel`, `√(a² + 1) ≤ a + ½` at `log(qT/2π) ≥ 7/4`, `log 2π ≥ 1.83787`
by a certified Taylor bound, `log_two_pi_ge`), `∫_1^T F_ε'² ≤ B²` (`crit_bessel` for
`(log t)η`) and `F_ε ≤ C`; then `ε → 0` (`ennreal_le_of_eps`). The constants close with room
`√(2/π) = 0.797885 ≤ 0.7979`, `1/√π = 0.564190 ≤ 0.5642`, `√(2π) ≤ 2.5067`, `√π ≤ 1.7725`,
`√2 ≤ 1.4143` (`haus_consts`).
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set Principia.Common.Goldbach
open scoped FourierTransform

/-! ## (1) The critical line -/

/-- **`G_δ(½ + iτ)`**, the Mellin transform of `η(t)e(δt)` on the critical line. -/
noncomputable def gcl (η : ℝ → ℝ) (δ τ : ℝ) : ℂ := Gm η δ (1 / 2 + (τ : ℂ) * Complex.I)

theorem re_crit (τ : ℝ) : (1 / 2 + (τ : ℂ) * Complex.I).re = 1 / 2 := by simp

theorem im_crit (τ : ℝ) : (1 / 2 + (τ : ℂ) * Complex.I).im = τ := by simp

/-- `|t^{s−1}| = 1/√t` on the critical line. -/
theorem norm_cpow_crit {t : ℝ} (ht : 0 < t) (τ : ℝ) :
    ‖(t : ℂ) ^ ((1 / 2 + (τ : ℂ) * Complex.I) - 1)‖ = 1 / Real.sqrt t := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, re_crit, Complex.one_re,
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  ring

/-- **The trivial bound** `|G_δ(½ + iτ)| ≤ |η/√t|₁`. -/
theorem norm_gcl_le (η : ℝ → ℝ) (δ τ : ℝ) : ‖gcl η δ τ‖ ≤ n1h η := by
  unfold gcl Gm mellin n1h
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [norm_smul, norm_cpow_crit ht0, norm_mul, e_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  ring

/-! ## (2) Mellin–Plancherel on the critical line (Bessel form) -/

/-- The change of variables `t = e^{−u}`: image. -/
theorem image_exp_neg : (Real.exp ∘ Neg.neg) '' (univ : Set ℝ) = Ioi 0 := by
  rw [image_comp, image_univ_of_surjective neg_surjective, image_univ, Real.range_exp]

/-- The change of variables `t = e^{−u}`: derivative. -/
theorem hasDeriv_exp_neg (x : ℝ) :
    HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x := by
  have h := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  rw [mul_neg_one] at h
  exact h.hasDerivWithinAt

/-- The change of variables `t = e^{−u}`: injectivity. -/
theorem injOn_exp_neg : InjOn (Real.exp ∘ Neg.neg) univ :=
  (Real.exp_injective.comp neg_injective).injOn

/-- `√(e^{−u}) = e^{−u/2}`. -/
theorem sqrt_exp_neg (u : ℝ) : Real.sqrt (Real.exp (-u)) = Real.exp (-(1 / 2) * u) := by
  rw [show Real.exp (-u) = Real.exp (-(1 / 2) * u) ^ 2 by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- The Fourier-side function `φ(u) = e^{−u/2}ζ(e^{−u})e(δe^{−u})`. -/
noncomputable def phiF (ζ : ℝ → ℝ) (δ u : ℝ) : ℂ :=
  Real.exp (-(1 / 2) * u) • (((ζ (Real.exp (-u)) : ℝ) : ℂ) * e (δ * Real.exp (-u)))

/-- **`G_δ(½ + iτ) = 𝓕φ(τ/2π)`** (Mathlib's `mellin_eq_fourier`). -/
theorem gcl_eq_fourier (ζ : ℝ → ℝ) (δ τ : ℝ) :
    gcl ζ δ τ = 𝓕 (phiF ζ δ) (τ / (2 * Real.pi)) := by
  unfold gcl Gm
  rw [mellin_eq_fourier, re_crit, im_crit]
  rfl

theorem integrable_phiF (ζ : ℝ → ℝ) (δ : ℝ)
    (h1 : IntegrableOn (fun t => ζ t / Real.sqrt t) (Ioi 0)) : Integrable (phiF ζ δ) := by
  have hg : IntegrableOn (fun t => (((ζ t / Real.sqrt t : ℝ) : ℂ)) * e (δ * t)) (Ioi 0) := by
    refine Integrable.mul_bdd (c := 1) h1.ofReal ?_ (ae_of_all _ fun t => (e_norm _).le)
    exact (continuous_e'.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  rw [← image_exp_neg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => hasDeriv_exp_neg x) injOn_exp_neg, integrableOn_univ] at hg
  refine hg.congr (ae_of_all _ fun u => ?_)
  simp only [Function.comp, phiF]
  rw [abs_neg, abs_of_pos (Real.exp_pos _), sqrt_exp_neg, Complex.real_smul,
    Complex.real_smul]
  have h1 : Real.exp (-u) = Real.exp (-(1 / 2) * u) * Real.exp (-(1 / 2) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(1 / 2) * u) ≠ 0 := (Real.exp_pos _).ne'
  rw [h1]
  push_cast
  field_simp

theorem integrable_phiF_sq (ζ : ℝ → ℝ) (δ : ℝ)
    (h2 : IntegrableOn (fun t => ζ t ^ 2) (Ioi 0)) :
    Integrable fun u => ‖phiF ζ δ u‖ ^ 2 := by
  have hg := h2
  rw [← image_exp_neg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => hasDeriv_exp_neg x) injOn_exp_neg, integrableOn_univ] at hg
  refine hg.congr (ae_of_all _ fun u => ?_)
  simp only [Function.comp, phiF, smul_eq_mul]
  rw [abs_neg, abs_of_pos (Real.exp_pos _), norm_smul, norm_mul, e_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, mul_pow,
    sq_abs, ← Real.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- `‖φ‖₂² = ∫₀^∞ ζ²`. -/
theorem integral_phiF_sq (ζ : ℝ → ℝ) (δ : ℝ) :
    ∫ u, ‖phiF ζ δ u‖ ^ 2 = ∫ t in Ioi (0 : ℝ), ζ t ^ 2 := by
  rw [← image_exp_neg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => hasDeriv_exp_neg x) injOn_exp_neg, setIntegral_univ]
  congr 1
  funext u
  simp only [Function.comp, phiF, smul_eq_mul]
  rw [abs_neg, abs_of_pos (Real.exp_pos _), norm_smul, norm_mul, e_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, mul_pow,
    sq_abs, ← Real.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- **Mellin–Plancherel on the critical line, Bessel form**:
`∫_{−T}^{T} |G_δ(½ + iτ)|² dτ ≤ 2π ∫₀^∞ ζ²` for `ζ/√t ∈ L¹(0,∞)`, `ζ ∈ L²(0,∞)`. -/
theorem crit_bessel (ζ : ℝ → ℝ) (δ : ℝ) (h1 : IntegrableOn (fun t => ζ t / Real.sqrt t) (Ioi 0))
    (h2 : IntegrableOn (fun t => ζ t ^ 2) (Ioi 0)) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in (-T)..T, ‖gcl ζ δ τ‖ ^ 2 ≤ 2 * Real.pi * ∫ t in Ioi (0 : ℝ), ζ t ^ 2 := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hb := FourierBessel.bessel (phiF ζ δ) (integrable_phiF ζ δ h1) (integrable_phiF_sq ζ δ h2)
    (T / (2 * Real.pi)) (by positivity)
  rw [integral_phiF_sq] at hb
  calc ∫ τ in (-T)..T, ‖gcl ζ δ τ‖ ^ 2
      = ∫ τ in (-T)..T, ‖𝓕 (phiF ζ δ) (τ / (2 * Real.pi))‖ ^ 2 := by
        refine intervalIntegral.integral_congr fun τ _ => ?_
        rw [gcl_eq_fourier]
    _ = (2 * Real.pi) • ∫ ξ in (-T) / (2 * Real.pi)..T / (2 * Real.pi),
          ‖𝓕 (phiF ζ δ) ξ‖ ^ 2 :=
        intervalIntegral.integral_comp_div (fun ξ => ‖𝓕 (phiF ζ δ) ξ‖ ^ 2) h2pi
    _ ≤ 2 * Real.pi * ∫ t in Ioi (0 : ℝ), ζ t ^ 2 := by
        rw [smul_eq_mul, neg_div]
        exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ## (3) Integrability and continuity on the critical line -/

/-- `|log t| ≤ (t^ε + t^{−ε})/ε` for `t, ε > 0`. -/
theorem abs_log_le_rpow {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    |Real.log t| ≤ (t ^ ε + t ^ (-ε)) / ε := by
  have h1 : Real.log (t ^ ε) = ε * Real.log t := Real.log_rpow ht ε
  have h2 : Real.log (t ^ (-ε)) = -ε * Real.log t := Real.log_rpow ht (-ε)
  have h3 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht ε)
  have h4 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht (-ε))
  have h5 : 0 < t ^ ε := Real.rpow_pos_of_pos ht ε
  have h6 : 0 < t ^ (-ε) := Real.rpow_pos_of_pos ht _
  rw [abs_le]
  constructor
  · have e : -((t ^ ε + t ^ (-ε)) / ε) = (-(t ^ ε + t ^ (-ε))) / ε := by ring
    rw [e, div_le_iff₀ hε]
    nlinarith
  · rw [le_div_iff₀ hε]
    nlinarith

/-- **`(log t)ζ(t)/√t ∈ L¹`** from `ζ t^{σ−1} ∈ L¹` for `σ` in an open interval around `1/2`. -/
theorem llog_div_sqrt_int (ζ : ℝ → ℝ) (hm : AEStronglyMeasurable ζ (volume.restrict (Ioi 0)))
    (h6 : ∃ a b : ℝ, a < 1 / 2 ∧ 1 / 2 < b ∧ ∀ σ ∈ Ioo a b,
      IntegrableOn (fun t => ζ t * t ^ (σ - 1)) (Ioi 0)) :
    IntegrableOn (fun t => llog ζ t / Real.sqrt t) (Ioi 0) := by
  obtain ⟨a, b, ha, hb, hσ⟩ := h6
  set ε := min (1 / 2 - a) (b - 1 / 2) / 2 with hεdef
  have hε : 0 < ε := by
    have : 0 < min (1 / 2 - a) (b - 1 / 2) := lt_min (by linarith) (by linarith)
    positivity
  have hεa : ε ≤ (1 / 2 - a) / 2 := by
    have := min_le_left (1 / 2 - a) (b - 1 / 2)
    linarith
  have hεb : ε ≤ (b - 1 / 2) / 2 := by
    have := min_le_right (1 / 2 - a) (b - 1 / 2)
    linarith
  have i1 := hσ (1 / 2 - ε) ⟨by linarith, by linarith⟩
  have i2 := hσ (1 / 2 + ε) ⟨by linarith, by linarith⟩
  refine Integrable.mono' ((i1.norm.add i2.norm).const_mul (1 / ε))
    ((Real.measurable_log.aemeasurable.mul hm.aemeasurable).div
      Real.continuous_sqrt.measurable.aemeasurable).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := ht
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hl := abs_log_le_rpow ht0 hε
  have e1 : t ^ (1 / 2 - ε - 1) = t ^ (-ε) / Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht0]
    congr 1
    ring
  have e2 : t ^ (1 / 2 + ε - 1) = t ^ ε / Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht0]
    congr 1
    ring
  simp only [Pi.add_apply]
  unfold llog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, e1, e2, abs_div, abs_mul, abs_mul,
    abs_mul, abs_of_pos hs0, abs_of_pos (div_pos (Real.rpow_pos_of_pos ht0 ε) hs0),
    abs_of_pos (div_pos (Real.rpow_pos_of_pos ht0 (-ε)) hs0)]
  have hz := abs_nonneg (ζ t)
  have key := mul_le_mul_of_nonneg_right hl hz
  have e3 : 1 / ε * (|ζ t| * (t ^ (-ε) / Real.sqrt t) + |ζ t| * (t ^ ε / Real.sqrt t)) =
      (t ^ ε + t ^ (-ε)) / ε * |ζ t| / Real.sqrt t := by
    field_simp
    ring
  rw [e3]
  exact div_le_div_of_nonneg_right key hs0.le

/-- **`τ ↦ G_δ(½ + iτ)` is continuous** for `ζ/√t ∈ L¹` (dominated by `|ζ|/√t`). -/
theorem continuous_gcl (ζ : ℝ → ℝ) (δ : ℝ) (hm : AEStronglyMeasurable ζ (volume.restrict (Ioi 0)))
    (h1 : IntegrableOn (fun t => ζ t / Real.sqrt t) (Ioi 0)) : Continuous (gcl ζ δ) := by
  unfold gcl Gm mellin
  refine continuous_of_dominated (bound := fun t => |ζ t| / Real.sqrt t) (fun τ => ?_)
    (fun τ => ?_) ?_ ?_
  · refine ((Complex.measurable_ofReal.pow_const _).aestronglyMeasurable).smul ?_
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hm).mul
      (continuous_e'.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht
    rw [norm_smul, norm_cpow_crit ht0, norm_mul, e_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact le_of_eq (by ring)
  · refine h1.norm.congr (ae_of_all _ fun t => ?_)
    simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg t)]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht
    refine Continuous.smul ?_ continuous_const
    exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
      continuous_const |>.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ht0.ne'))

/-! ## (4) The three sub-links of `lem:hausierer` -/

/-- **LINK [CritDeriv] — the derivative on the critical line (MELLIN)**: for `η` with the
hypotheses of `lem:hausierer`, `τ ↦ G_δ(½ + iτ)` is differentiable with derivative
`i·G'_δ(½ + iτ)`, `G'_δ = M((log t)η(t)e(δt))` (majarcs 3431–3440: "`G_δ' = M((log t)η e(δt))`").
Differentiation under the integral sign, dominated on the line by `|log t||η(t)|/√t`. -/
def CritDeriv : Prop :=
  ∀ η : ℝ → ℝ, HausiererReg η → ∀ δ τ : ℝ,
    HasDerivAt (gcl η δ) (Complex.I * gcl (llog η) δ τ) τ

/-- **LINK [AbelZeros] — partial summation over the zeros against the zero count (ELEM given
`ZeroCount`)**: for `F` of class `C¹` on `[1, T]`, `F ≥ 0`, and every primitive `χ`,
`∑_{1 < |Im ρ| ≤ T} F(|Im ρ|) ≤ ∫_1^T F(t)(1/π)log(qt/2π)dt + F(T)g(T) + F(1)g(1) + ∫_1^T |F'|g`
(two-sided count, multiplicity; `∑ F(|γ|) = F(T)N(T) − F(1)N(1) − ∫F'N`, `N = M + O*(g)`,
`M(t) = (t/π)log(qt/2πe)`). -/
def AbelZeros : Prop :=
  ZeroCount → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ (F F' : ℝ → ℝ) (T : ℝ), 1 ≤ T → (∀ t ∈ Icc 1 T, HasDerivAt F (F' t) t) →
      ContinuousOn F' (Icc 1 T) → (∀ t ∈ Icc 1 T, 0 ≤ F t) →
        zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal (F |ρ.im|)) ≤
          ENNReal.ofReal ((∫ t in (1 : ℝ)..T, F t * (Real.log (q * t / (2 * Real.pi)) / Real.pi))
            + F T * gZ q T + F 1 * gZ q 1 + ∫ t in (1 : ℝ)..T, |F' t| * gZ q t)

/-- **LINK [RealSym] — the zeros of `L(s, χ)` are symmetric under `s ↦ s̄` for a real `χ`, with
multiplicity** (`L(s̄, χ) = \overline{L(s, χ)}` for real `χ`). -/
def RealSym : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), IsRealChar χ → ∀ s : ℂ,
    (s ∈ zeroSet χ → starRingEnd ℂ s ∈ zeroSet χ) ∧ zmult χ (starRingEnd ℂ s) = zmult χ s

/-! ## (5) Partial summation + Cauchy–Schwarz: the generic high-zero bound -/

/-- Cauchy–Schwarz on an interval, for functions continuous on it. -/
theorem cs_interval {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hu : ContinuousOn u (Icc a b))
    (hv : ContinuousOn v (Icc a b)) :
    ∫ x in a..b, u x * v x ≤
      Real.sqrt (∫ x in a..b, u x ^ 2) * Real.sqrt (∫ x in a..b, v x ^ 2) := by
  have hI : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc a b) → IntervalIntegrable f volume a b :=
    fun hf => (uIcc_of_le hab ▸ hf).intervalIntegrable
  have hu2 := hI (hu.pow 2)
  have hv2 := hI (hv.pow 2)
  refine FourierBessel.cs_real _ _ _
    (intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _)
    (intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _) fun l hl => ?_
  have hm : ∫ x in a..b, 2 * (u x * v x) ≤ ∫ x in a..b, (l * u x ^ 2 + v x ^ 2 / l) := by
    refine intervalIntegral.integral_mono_on hab (hI (continuousOn_const.mul (hu.mul hv)))
      ((hu2.const_mul l).add (hv2.div_const l)) fun x _ => ?_
    have key : l * (2 * (u x * v x)) ≤ l * (l * u x ^ 2 + v x ^ 2 / l) := by
      rw [mul_add, mul_div_cancel₀ _ hl.ne']
      nlinarith [sq_nonneg (l * u x - v x)]
    exact le_of_mul_le_mul_left key hl
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hu2.const_mul l)
    (hv2.div_const l), intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hm
  linarith

/-- `∫_1^T log²(ct) dt ≤ T((log cT − 1)² + 1)`. -/
theorem int_log_sq_le {c T : ℝ} (hc : 0 < c) (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, Real.log (c * t) ^ 2 ≤ T * ((Real.log (c * T) - 1) ^ 2 + 1) := by
  have hpos : ∀ t ∈ uIcc (1 : ℝ) T, 0 < t := fun t ht => by
    rw [uIcc_of_le hT] at ht
    linarith [ht.1]
  have hd : ∀ t ∈ uIcc (1 : ℝ) T, HasDerivAt (fun t => t * ((Real.log (c * t) - 1) ^ 2 + 1))
      (Real.log (c * t) ^ 2) t := by
    intro t ht
    have ht0 := hpos t ht
    have h1 : HasDerivAt (fun t => Real.log (c * t)) (1 / t) t := by
      have := ((hasDerivAt_id t).const_mul c).log (by positivity)
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
    have h2 := ((h1.sub_const 1).pow 2).add_const 1
    refine ((hasDerivAt_id t).mul h2).congr_deriv ?_
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have hc2 : ContinuousOn (fun t => Real.log (c * t) ^ 2) (uIcc (1 : ℝ) T) :=
    (ContinuousOn.log (by fun_prop) fun t ht => (mul_pos hc (hpos t ht)).ne').pow 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc2.intervalIntegrable]
  have : 0 ≤ 1 * ((Real.log (c * 1) - 1) ^ 2 + 1) := by positivity
  linarith

/-- `∫_1^T g(t)² dt ≤ T((½log qT + 17.2)² + ¼)`, `g = gZ q`. -/
theorem int_gZ_sq_le {q T : ℝ} (hq : 0 < q) (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, gZ q t ^ 2 ≤ T * ((0.5 * Real.log (q * T) + 17.2) ^ 2 + 0.25) := by
  have hpos : ∀ t ∈ uIcc (1 : ℝ) T, 0 < t := fun t ht => by
    rw [uIcc_of_le hT] at ht
    linarith [ht.1]
  have hd : ∀ t ∈ uIcc (1 : ℝ) T,
      HasDerivAt (fun t => t * ((0.5 * Real.log (q * t) + 17.2) ^ 2 + 0.25)) (gZ q t ^ 2) t := by
    intro t ht
    have ht0 := hpos t ht
    have h1 : HasDerivAt (fun t => Real.log (q * t)) (1 / t) t := by
      have := ((hasDerivAt_id t).const_mul q).log (by positivity)
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
    have h2 := (((h1.const_mul 0.5).add_const 17.2).pow 2).add_const 0.25
    refine ((hasDerivAt_id t).mul h2).congr_deriv ?_
    simp only [id, Pi.pow_apply]
    unfold gZ
    field_simp
    ring
  have hc2 : ContinuousOn (fun t => gZ q t ^ 2) (uIcc (1 : ℝ) T) := by
    unfold gZ
    exact ((continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      fun t ht => (mul_pos hq (hpos t ht)).ne')).add continuousOn_const).pow 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc2.intervalIntegrable]
  have : 0 ≤ 1 * ((0.5 * Real.log (q * 1) + 17.2) ^ 2 + 0.25) := by positivity
  linarith

/-- **`log 2π ≥ 1.83787`** (`e^{0.83787}` by its Taylor polynomial of degree 11, `e ≤ 2.7182818286`,
`π > 3.141592`). -/
theorem log_two_pi_ge : 1.83787 ≤ Real.log (2 * Real.pi) := by
  rw [Real.le_log_iff_exp_le (by positivity), show (1.83787 : ℝ) = 1 + 0.83787 by norm_num,
    Real.exp_add]
  have h1 := Real.exp_bound' (x := 0.83787) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 12, (0.83787 : ℝ) ^ m / m.factorial) +
      (0.83787 : ℝ) ^ 12 * (12 + 1) / (Nat.factorial 12 * 12) ≤ 2.31148 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.pi_gt_d6
  have h5 : 0 < Real.exp 0.83787 := Real.exp_pos _
  nlinarith

/-- The height facts: `log(qT/2π) ≥ 7/4` and `log(qT/2π) ≤ log qT − 1.83787` for `qT ≥ 37`. -/
theorem crit_L_facts {q T : ℝ} (hq : 0 < q) (hT : 0 < T) (hqT : 37 ≤ q * T) :
    7 / 4 ≤ Real.log (q * T / (2 * Real.pi)) ∧
      Real.log (q * T / (2 * Real.pi)) ≤ Real.log (q * T) - 1.83787 := by
  have hpi := Real.pi_lt_d4
  constructor
  · have hy : (2.7182818286 : ℝ) ^ 7 ≤ (q * T / (2 * Real.pi)) ^ 4 := by
      have h1 : (5.88 : ℝ) ≤ q * T / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc (2.7182818286 : ℝ) ^ 7 ≤ 5.88 ^ 4 := by norm_num
        _ ≤ (q * T / (2 * Real.pi)) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
    have h := nat_le_log 7 hy
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  · rw [Real.log_div (by positivity) (by positivity)]
    linarith [log_two_pi_ge]

/-- **The generic high-zero bound** (`AbelZeros` + Cauchy–Schwarz): for `F ∈ C¹[1,T]`, `F ≥ 0`,
with `∫_1^T F² ≤ A²`, `∫_1^T F'² ≤ B²`, `F(1), F(T) ≤ C`:
`∑_{1<|γ|≤T} F(|γ|) ≤ A√T(log qT − 1.83787 − ½)/π + C(g(T) + g(1)) + B√T(½log qT + 17.21)`. -/
theorem high_bound (hAb : AbelZeros) (hZC : ZeroCount) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hqT : 37 ≤ (q : ℝ) * T) {F F' : ℝ → ℝ} (hd : ∀ t ∈ Icc 1 T, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Icc 1 T)) (hF0 : ∀ t ∈ Icc 1 T, 0 ≤ F t) {A B C : ℝ} (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : ∫ t in (1 : ℝ)..T, F t ^ 2 ≤ A ^ 2)
    (hB : ∫ t in (1 : ℝ)..T, F' t ^ 2 ≤ B ^ 2) (hC1 : F 1 ≤ C) (hCT : F T ≤ C) :
    zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal (F |ρ.im|)) ≤
      ENNReal.ofReal (A * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi +
        C * (gZ q T + gZ q 1) + B * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21)) := by
  refine le_trans (hAb hZC q χ hχ F F' T hT hd hc hF0) (ENNReal.ofReal_le_ofReal ?_)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hL74, hLx⟩ := crit_L_facts hq0 hT0 hqT
  set L := Real.log (q * T / (2 * Real.pi)) with hL
  set x := Real.log (q * T) with hx
  have hFc : ContinuousOn F (Icc 1 T) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hpos : ∀ t ∈ Icc (1 : ℝ) T, 0 < t := fun t ht => by linarith [ht.1]
  have hI : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 1 T) → IntervalIntegrable f volume 1 T :=
    fun hf => (uIcc_of_le hT ▸ hf).intervalIntegrable
  -- (i) the main term
  set m : ℝ → ℝ := fun t => max (Real.log (q * t / (2 * Real.pi))) 0 / Real.pi with hm
  have hmc : ContinuousOn m (Icc 1 T) := by
    refine ContinuousOn.div_const (ContinuousOn.sup (ContinuousOn.log (by fun_prop)
      fun t ht => ?_) continuousOn_const) _
    have := hpos t ht
    positivity
  have hM1 : ∫ t in (1 : ℝ)..T, F t * (Real.log (q * t / (2 * Real.pi)) / Real.pi) ≤
      ∫ t in (1 : ℝ)..T, F t * m t := by
    refine intervalIntegral.integral_mono_on hT (hI (hFc.mul (ContinuousOn.div_const
      (ContinuousOn.log (by fun_prop) fun t ht => ?_) _))) (hI (hFc.mul hmc)) fun t ht => ?_
    · have := hpos t ht
      positivity
    · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_max_left _ _)
        Real.pi_pos.le) (hF0 t ht)
  have hM2 := cs_interval hT hFc hmc
  have hm2 : ∫ t in (1 : ℝ)..T, m t ^ 2 ≤ T * ((L - 1) ^ 2 + 1) / Real.pi ^ 2 := by
    have h1 : ∫ t in (1 : ℝ)..T, m t ^ 2 ≤
        ∫ t in (1 : ℝ)..T, Real.log (q / (2 * Real.pi) * t) ^ 2 / Real.pi ^ 2 := by
      refine intervalIntegral.integral_mono_on hT (hI (hmc.pow 2)) (hI (ContinuousOn.div_const
        ((ContinuousOn.log (by fun_prop) fun t ht => ?_).pow 2) _)) fun t ht => ?_
      · have := hpos t ht
        positivity
      · have e : q / (2 * Real.pi) * t = q * t / (2 * Real.pi) := by ring
        rw [e]
        simp only [hm, div_pow]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rcases le_total (Real.log (q * t / (2 * Real.pi))) 0 with h | h
        · rw [max_eq_right h]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
          exact sq_nonneg _
        · rw [max_eq_left h]
    have h2 := int_log_sq_le (c := q / (2 * Real.pi)) (by positivity) hT
    rw [intervalIntegral.integral_div] at h1
    have e : q / (2 * Real.pi) * T = q * T / (2 * Real.pi) := by ring
    rw [e, ← hL] at h2
    calc ∫ t in (1 : ℝ)..T, m t ^ 2 ≤ (∫ t in (1 : ℝ)..T, Real.log (q / (2 * Real.pi) * t) ^ 2) /
          Real.pi ^ 2 := h1
      _ ≤ T * ((L - 1) ^ 2 + 1) / Real.pi ^ 2 :=
        div_le_div_of_nonneg_right h2 (by positivity)
  have hsqm : Real.sqrt (∫ t in (1 : ℝ)..T, m t ^ 2) ≤ Real.sqrt T * (L - 1 / 2) / Real.pi := by
    refine (Real.sqrt_le_sqrt hm2).trans ?_
    rw [Real.sqrt_le_left (div_nonneg (mul_nonneg (Real.sqrt_nonneg T) (by linarith))
      Real.pi_pos.le)]
    rw [div_pow, mul_pow, Real.sq_sqrt hT0.le]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith) hT0.le
  have hsqF : Real.sqrt (∫ t in (1 : ℝ)..T, F t ^ 2) ≤ A := by
    rw [Real.sqrt_le_left hA0]
    exact hA
  have hMain : ∫ t in (1 : ℝ)..T, F t * (Real.log (q * t / (2 * Real.pi)) / Real.pi) ≤
      A * Real.sqrt T * (x - 2.33787) / Real.pi := by
    have h0 : 0 ≤ Real.sqrt T * (L - 1 / 2) / Real.pi := by
      have := Real.sqrt_nonneg T
      have : 0 ≤ L - 1 / 2 := by linarith
      positivity
    have h1 := mul_le_mul hsqF hsqm (Real.sqrt_nonneg _) hA0
    have h2 : A * (Real.sqrt T * (L - 1 / 2) / Real.pi) ≤ A * Real.sqrt T * (x - 2.33787) /
        Real.pi := by
      rw [mul_div_assoc', mul_assoc]
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)) hA0) Real.pi_pos.le
    linarith
  -- (ii) the boundary terms
  have hg1 : 0 ≤ gZ q 1 := gZ_nonneg (by linarith)
  have hgT : 0 ≤ gZ q T := gZ_nonneg (by linarith)
  have hBd : F T * gZ q T + F 1 * gZ q 1 ≤ C * (gZ q T + gZ q 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hCT hgT, mul_le_mul_of_nonneg_right hC1 hg1]
  -- (iii) the derivative term
  have hgc : ContinuousOn (gZ (q : ℝ)) (Icc 1 T) := by
    unfold gZ
    refine (continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun t ht => ?_)).add
      continuousOn_const
    have := hpos t ht
    positivity
  have hD1 := cs_interval hT hc.abs hgc
  have hD2 : ∫ t in (1 : ℝ)..T, |F' t| ^ 2 = ∫ t in (1 : ℝ)..T, F' t ^ 2 :=
    intervalIntegral.integral_congr fun t _ => sq_abs _
  have hsqD : Real.sqrt (∫ t in (1 : ℝ)..T, |F' t| ^ 2) ≤ B := by
    rw [hD2, Real.sqrt_le_left hB0]
    exact hB
  have hsqg : Real.sqrt (∫ t in (1 : ℝ)..T, gZ q t ^ 2) ≤
      Real.sqrt T * (0.5 * x + 17.21) := by
    refine (Real.sqrt_le_sqrt (int_gZ_sq_le hq0 hT)).trans ?_
    have hx0 : 0 ≤ x := Real.log_nonneg (by nlinarith)
    rw [Real.sqrt_le_left (by have := Real.sqrt_nonneg T; positivity), mul_pow,
      Real.sq_sqrt hT0.le]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hT0.le
  have hDer : ∫ t in (1 : ℝ)..T, |F' t| * gZ q t ≤ B * Real.sqrt T * (0.5 * x + 17.21) := by
    have h1 := mul_le_mul hsqD hsqg (Real.sqrt_nonneg _) hB0
    rw [← mul_assoc] at h1
    linarith
  linarith

/-! ## (6) The smoothed weights -/

theorem norm_I_mul (z : ℂ) : ‖Complex.I * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

theorem norm_neg_one_smul (z : ℂ) : ‖((-1 : ℝ) • z)‖ = ‖z‖ := by
  rw [norm_smul, norm_neg, norm_one, one_mul]

theorem cont_of_deriv {g d : ℝ → ℂ} (hD : ∀ τ, HasDerivAt g (Complex.I * d τ) τ) :
    Continuous g :=
  continuous_iff_continuousAt.mpr fun τ => (hD τ).continuousAt

/-- `d/dt |g(t)|² = 2⟨g(t), i d(t)⟩`. -/
theorem hasDerivAt_nsq {g d : ℝ → ℂ} (hD : ∀ τ, HasDerivAt g (Complex.I * d τ) τ) (t : ℝ) :
    HasDerivAt (fun t => ‖g t‖ ^ 2) (2 * inner ℝ (g t) (Complex.I * d t)) t :=
  (hD t).norm_sq

/-- `d/dt |g(−t)|² = 2⟨g(−t), −i d(−t)⟩`. -/
theorem hasDerivAt_nsq_neg {g d : ℝ → ℂ} (hD : ∀ τ, HasDerivAt g (Complex.I * d τ) τ) (t : ℝ) :
    HasDerivAt (fun t => ‖g (-t)‖ ^ 2)
      (2 * inner ℝ (g (-t)) ((-1 : ℝ) • (Complex.I * d (-t)))) t :=
  ((hD (-t)).scomp t (hasDerivAt_neg t)).norm_sq

theorem abs_inner_I_le (a z : ℂ) : |inner ℝ a (Complex.I * z)| ≤ ‖a‖ * ‖z‖ := by
  have h := abs_real_inner_le_norm a (Complex.I * z)
  rwa [norm_I_mul] at h

theorem abs_inner_negI_le (a z : ℂ) :
    |inner ℝ a ((-1 : ℝ) • (Complex.I * z))| ≤ ‖a‖ * ‖z‖ := by
  have h := abs_real_inner_le_norm a ((-1 : ℝ) • (Complex.I * z))
  rwa [norm_neg_one_smul, norm_I_mul] at h

/-- **The complex-character weight** `F_ε(t) = √(|g(t)|² + |g(−t)|² + ε²)`: `C¹`, and
`F_ε'² ≤ |d(t)|² + |d(−t)|²` (Cauchy–Schwarz). -/
theorem smooth_c {g d : ℝ → ℂ} (hD : ∀ τ, HasDerivAt g (Complex.I * d τ) τ) (hdc : Continuous d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F F' : ℝ → ℝ, (∀ t, HasDerivAt F (F' t) t) ∧ Continuous F' ∧ (∀ t, 0 ≤ F t) ∧
      (∀ t, F t ^ 2 = ‖g t‖ ^ 2 + ‖g (-t)‖ ^ 2 + ε ^ 2) ∧
      (∀ t, F' t ^ 2 ≤ ‖d t‖ ^ 2 + ‖d (-t)‖ ^ 2) := by
  have hgc := cont_of_deriv hD
  set h : ℝ → ℝ := fun t => ‖g t‖ ^ 2 + ‖g (-t)‖ ^ 2 + ε ^ 2 with hh
  set h' : ℝ → ℝ := fun t => 2 * inner ℝ (g t) (Complex.I * d t) +
    2 * inner ℝ (g (-t)) ((-1 : ℝ) • (Complex.I * d (-t))) with hh'
  have hpos : ∀ t, 0 < h t := fun t => by
    simp only [hh]
    positivity
  have hdh : ∀ t, HasDerivAt h (h' t) t := fun t =>
    ((hasDerivAt_nsq hD t).add (hasDerivAt_nsq_neg hD t)).add_const (ε ^ 2)
  have hc1 : Continuous h' := by
    simp only [hh']
    exact (continuous_const.mul (hgc.inner (continuous_const.mul hdc))).add
      (continuous_const.mul ((hgc.comp continuous_neg).inner
        (continuous_const.smul (continuous_const.mul (hdc.comp continuous_neg)))))
  have hc2 : Continuous h := by
    simp only [hh]
    fun_prop
  refine ⟨fun t => Real.sqrt (h t), fun t => h' t / (2 * Real.sqrt (h t)),
    fun t => (hdh t).sqrt (hpos t).ne', ?_, fun t => Real.sqrt_nonneg _,
    fun t => Real.sq_sqrt (hpos t).le, fun t => ?_⟩
  · exact hc1.div (continuous_const.mul (Real.continuous_sqrt.comp hc2)) fun t => by
      have := Real.sqrt_pos.mpr (hpos t)
      positivity
  · have hsq : (h' t / (2 * Real.sqrt (h t))) ^ 2 = h' t ^ 2 / (4 * h t) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (hpos t).le]
      norm_num
    rw [hsq, div_le_iff₀ (by have := hpos t; positivity)]
    have hi1 := abs_inner_I_le (g t) (d t)
    have hi2 := abs_inner_negI_le (g (-t)) (d (-t))
    set u := inner ℝ (g t) (Complex.I * d t)
    set v := inner ℝ (g (-t)) ((-1 : ℝ) • (Complex.I * d (-t)))
    set a := ‖g t‖
    set b := ‖d t‖
    set c := ‖g (-t)‖
    set e := ‖d (-t)‖
    have s1 : |u + v| ≤ a * b + c * e := (abs_add_le u v).trans (add_le_add hi1 hi2)
    have s2 : (u + v) ^ 2 ≤ (a * b + c * e) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) s1 2
    have s3 : (a * b + c * e) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + e ^ 2) := by
      nlinarith [sq_nonneg (a * e - c * b)]
    have s4 : (a ^ 2 + c ^ 2) * (b ^ 2 + e ^ 2) ≤ h t * (b ^ 2 + e ^ 2) :=
      mul_le_mul_of_nonneg_right (by simp only [hh]; nlinarith) (by positivity)
    have e1 : h' t = 2 * (u + v) := by simp only [hh']; ring
    rw [e1]
    nlinarith

/-- **The real-character weight** `F_ε(t) = √(|g(t)|² + ε²) + √(|g(−t)|² + ε²)`: `C¹`, bounded by
`|g(t)| + |g(−t)| + 2ε` and at least `|g(t)| + |g(−t)|`, with `F_ε'² ≤ 2(|d(t)|² + |d(−t)|²)`. -/
theorem smooth_r {g d : ℝ → ℂ} (hD : ∀ τ, HasDerivAt g (Complex.I * d τ) τ) (hdc : Continuous d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F F' : ℝ → ℝ, (∀ t, HasDerivAt F (F' t) t) ∧ Continuous F' ∧
      (∀ t, ‖g t‖ + ‖g (-t)‖ ≤ F t) ∧ (∀ t, F t ≤ ‖g t‖ + ‖g (-t)‖ + 2 * ε) ∧
      (∀ t, F t ^ 2 ≤ 2 * (‖g t‖ ^ 2 + ‖g (-t)‖ ^ 2 + 2 * ε ^ 2)) ∧
      (∀ t, F' t ^ 2 ≤ 2 * (‖d t‖ ^ 2 + ‖d (-t)‖ ^ 2)) := by
  have hgc := cont_of_deriv hD
  set h1 : ℝ → ℝ := fun t => ‖g t‖ ^ 2 + ε ^ 2 with hh1
  set h2 : ℝ → ℝ := fun t => ‖g (-t)‖ ^ 2 + ε ^ 2 with hh2
  have hp1 : ∀ t, 0 < h1 t := fun t => by
    simp only [hh1]
    positivity
  have hp2 : ∀ t, 0 < h2 t := fun t => by
    simp only [hh2]
    positivity
  have hd1 : ∀ t, HasDerivAt h1 (2 * inner ℝ (g t) (Complex.I * d t)) t := fun t =>
    (hasDerivAt_nsq hD t).add_const (ε ^ 2)
  have hd2 : ∀ t, HasDerivAt h2 (2 * inner ℝ (g (-t)) ((-1 : ℝ) • (Complex.I * d (-t)))) t :=
    fun t => (hasDerivAt_nsq_neg hD t).add_const (ε ^ 2)
  have hc1 : Continuous h1 := by
    simp only [hh1]
    fun_prop
  have hc2 : Continuous h2 := by
    simp only [hh2]
    fun_prop
  -- `√(a² + ε²)` versus `a`
  have hsq_ge : ∀ a : ℝ, 0 ≤ a → a ≤ Real.sqrt (a ^ 2 + ε ^ 2) := fun a ha =>
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq_le : ∀ a : ℝ, 0 ≤ a → Real.sqrt (a ^ 2 + ε ^ 2) ≤ a + ε := fun a ha => by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  -- each derivative term is at most `|d|`
  have hterm : ∀ (a w : ℂ) (x : ℝ), 0 < ‖a‖ ^ 2 + ε ^ 2 → |x| ≤ ‖a‖ * ‖w‖ →
      (2 * x / (2 * Real.sqrt (‖a‖ ^ 2 + ε ^ 2))) ^ 2 ≤ ‖w‖ ^ 2 := by
    intro a w x hp hx
    have hs := hsq_ge ‖a‖ (norm_nonneg _)
    have hs0 : 0 < Real.sqrt (‖a‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr hp
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hp.le, div_le_iff₀ (by positivity)]
    have hx2 : x ^ 2 ≤ (‖a‖ * ‖w‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖a‖]
  refine ⟨fun t => Real.sqrt (h1 t) + Real.sqrt (h2 t),
    fun t => 2 * inner ℝ (g t) (Complex.I * d t) / (2 * Real.sqrt (h1 t)) +
      2 * inner ℝ (g (-t)) ((-1 : ℝ) • (Complex.I * d (-t))) / (2 * Real.sqrt (h2 t)),
    fun t => ((hd1 t).sqrt (hp1 t).ne').add ((hd2 t).sqrt (hp2 t).ne'), ?_, fun t => ?_,
    fun t => ?_, fun t => ?_, fun t => ?_⟩
  · refine Continuous.add ?_ ?_
    · exact (continuous_const.mul (hgc.inner (continuous_const.mul hdc))).div
        (continuous_const.mul (Real.continuous_sqrt.comp hc1)) fun t => by
          have := Real.sqrt_pos.mpr (hp1 t)
          positivity
    · exact (continuous_const.mul ((hgc.comp continuous_neg).inner
        (continuous_const.smul (continuous_const.mul (hdc.comp continuous_neg))))).div
        (continuous_const.mul (Real.continuous_sqrt.comp hc2)) fun t => by
          have := Real.sqrt_pos.mpr (hp2 t)
          positivity
  · exact add_le_add (hsq_ge _ (norm_nonneg _)) (hsq_ge _ (norm_nonneg _))
  · have := add_le_add (hsq_le _ (norm_nonneg (g t))) (hsq_le _ (norm_nonneg (g (-t))))
    simp only [hh1, hh2]
    linarith
  · simp only [hh1, hh2]
    have a1 := Real.sq_sqrt (hp1 t).le
    have a2 := Real.sq_sqrt (hp2 t).le
    simp only [hh1, hh2] at a1 a2
    nlinarith [sq_nonneg (Real.sqrt (‖g t‖ ^ 2 + ε ^ 2) - Real.sqrt (‖g (-t)‖ ^ 2 + ε ^ 2))]
  · have t1 := hterm (g t) (d t) _ (hp1 t) (abs_inner_I_le (g t) (d t))
    have t2 := hterm (g (-t)) (d (-t)) _ (hp2 t) (abs_inner_negI_le (g (-t)) (d (-t)))
    simp only [hh1, hh2] at t1 t2 ⊢
    nlinarith [sq_nonneg (2 * inner ℝ (g t) (Complex.I * d t) /
        (2 * Real.sqrt (‖g t‖ ^ 2 + ε ^ 2)) - 2 * inner ℝ (g (-t))
          ((-1 : ℝ) • (Complex.I * d (-t))) / (2 * Real.sqrt (‖g (-t)‖ ^ 2 + ε ^ 2)))]

/-! ## (7) Zero sums: congruence, additivity, the reflection -/

theorem zsum_congr {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {A : Set ℂ}
    {w w' : ℂ → ENNReal} (h : ∀ ρ ∈ zeroSet χ ∩ A, w ρ = w' ρ) : zsum χ A w = zsum χ A w' :=
  le_antisymm (zsum_mono χ fun ρ hρ => (h ρ hρ).le) (zsum_mono χ fun ρ hρ => (h ρ hρ).ge)

theorem zsum_add' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (A : Set ℂ)
    (w w' : ℂ → ENNReal) : zsum χ A (fun ρ => w ρ + w' ρ) = zsum χ A w + zsum χ A w' := by
  unfold zsum
  rw [← ENNReal.tsum_add]
  congr 1
  funext ρ
  ring

/-- **The reflection `ρ ↦ ρ̄` for a real character** (`RealSym`): a conjugation-invariant zero sum
is unchanged when the weight is composed with conjugation. -/
theorem zsum_conj (hRS : RealSym) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hr : IsRealChar χ) {A : Set ℂ} (hA : ∀ s ∈ A, starRingEnd ℂ s ∈ A) (w : ℂ → ENNReal) :
    zsum χ A (fun ρ => w (starRingEnd ℂ ρ)) = zsum χ A w := by
  unfold zsum
  let e : ↥(zeroSet χ ∩ A) ≃ ↥(zeroSet χ ∩ A) :=
    { toFun := fun ρ => ⟨starRingEnd ℂ ρ, (hRS q χ hr ρ).1 ρ.2.1, hA _ ρ.2.2⟩
      invFun := fun ρ => ⟨starRingEnd ℂ ρ, (hRS q χ hr ρ).1 ρ.2.1, hA _ ρ.2.2⟩
      left_inv := fun ρ => Subtype.ext (Complex.conj_conj (ρ : ℂ))
      right_inv := fun ρ => Subtype.ext (Complex.conj_conj (ρ : ℂ)) }
  rw [← e.tsum_eq (fun ρ : ↥(zeroSet χ ∩ A) => zmult χ ρ * w ρ)]
  congr 1
  funext ρ
  change zmult χ ρ * w (starRingEnd ℂ ρ) = zmult χ (starRingEnd ℂ ρ) * w (starRingEnd ℂ ρ)
  rw [(hRS q χ hr ρ).2]

/-- `∫_1^T (φ(t) + φ(−t)) ≤ ∫_{−T}^{T} φ` for `φ ≥ 0` continuous. -/
theorem sym_int_le {φ : ℝ → ℝ} (hc : Continuous φ) (h0 : ∀ t, 0 ≤ φ t) (T : ℝ) :
    ∫ t in (1 : ℝ)..T, (φ t + φ (-t)) ≤ ∫ t in (-T)..T, φ t := by
  have hi : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b => hc.intervalIntegrable a b
  have hn : IntervalIntegrable (fun t => φ (-t)) volume 1 T :=
    (hc.comp continuous_neg).intervalIntegrable 1 T
  rw [intervalIntegral.integral_add (hi 1 T) hn,
    intervalIntegral.integral_comp_neg (fun t => φ t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-T) (-1)) (hi (-1) T),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 T)]
  have : 0 ≤ ∫ t in (-1 : ℝ)..1, φ t := intervalIntegral.integral_nonneg (by norm_num) fun t _ =>
    h0 t
  linarith

/-! ## (8) `lem:hausierer`, corrected — PROVED from `CritDeriv`, `AbelZeros`, `RealSym` -/

/-- **The zeros up to height `1`**: `N(1) ≤ (1/π)log(q/2πe) + g(1) ≤ 0.819 log q + 16.8`. -/
theorem zcount_one_le (hZC : ZeroCount) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : zcount χ 1 ≤ ENNReal.ofReal (0.819 * Real.log q + 16.8) := by
  obtain ⟨hfin, hb⟩ := hZC q χ hχ 1 le_rfl
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq1
  have h1 : (zcount χ 1).toReal ≤ 1 / Real.pi *
      Real.log ((q : ℝ) * 1 / (2 * Real.pi * Real.exp 1)) + gZ q 1 := by
    have := (abs_le.mp hb).2
    linarith
  have e1 : Real.log ((q : ℝ) * 1 / (2 * Real.pi * Real.exp 1)) =
      Real.log q - Real.log (2 * Real.pi) - 1 := by
    rw [mul_one, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    ring
  have hpi : 1 / Real.pi ≤ 0.31832 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d6]
  have hpi2 : 0.3183 ≤ 1 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d4]
  have hl2 := log_two_pi_ge
  unfold gZ at h1
  rw [e1, mul_one] at h1
  have k1 := mul_le_mul_of_nonneg_right hpi hlq
  have k2 : 0.3183 * (Real.log (2 * Real.pi) + 1) ≤ 1 / Real.pi * (Real.log (2 * Real.pi) + 1) :=
    mul_le_mul_of_nonneg_right hpi2 (by linarith)
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
  nlinarith

/-- **The low zeros** (`|Im ρ| ≤ 1`): `∑ |G_δ(ρ)| ≤ |η/√t|₁·N(1)`. -/
theorem low_sum (hZC : ZeroCount) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (g : ℝ → ℂ) {n1 : ℝ} (hn1 : 0 ≤ n1) (hg : ∀ τ, ‖g τ‖ ≤ n1) :
    zsum χ {s | |s.im| ≤ 1} (fun ρ => ENNReal.ofReal ‖g ρ.im‖) ≤
      ENNReal.ofReal (n1 * (0.819 * Real.log q + 16.8)) := by
  calc zsum χ {s | |s.im| ≤ 1} (fun ρ => ENNReal.ofReal ‖g ρ.im‖)
      ≤ zsum χ {s | |s.im| ≤ 1} (fun _ => ENNReal.ofReal n1 * 1) :=
        zsum_mono χ fun ρ _ => by
          rw [mul_one]
          exact ENNReal.ofReal_le_ofReal (hg _)
    _ = ENNReal.ofReal n1 * zcount χ 1 := by
        rw [zsum_const_mul]
        rfl
    _ ≤ ENNReal.ofReal n1 * ENNReal.ofReal (0.819 * Real.log q + 16.8) :=
        mul_le_mul' le_rfl (zcount_one_le hZC hχ)
    _ = ENNReal.ofReal (n1 * (0.819 * Real.log q + 16.8)) := (ENNReal.ofReal_mul hn1).symm

/-- `{|Im| ≤ T} ⊆ {|Im| ≤ 1} ∪ {1 < |Im| ≤ T}`. -/
theorem zsum_split1 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} (w : ℂ → ENNReal) :
    zsum χ {s | |s.im| ≤ T} w ≤
      zsum χ {s | |s.im| ≤ 1} w + zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} w := by
  refine le_trans (zsum_mono_set χ (fun s hs => ?_) w) (zsum_union χ _ _ w)
  rcases le_or_gt |s.im| 1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hs⟩

/-- An `ε`-family of bounds gives the limit bound. -/
theorem ennreal_le_of_eps {S : ENNReal} {H K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → S ≤ ENNReal.ofReal (H + ε * K)) : S ≤ ENNReal.ofReal H := by
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
  have hε'r : (0 : ℝ) < ε' := by exact_mod_cast hε'
  have h1 := h (ε' / (K + 1)) (by positivity)
  have h2 : ε' / (K + 1) * K ≤ ε' := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc S ≤ ENNReal.ofReal (H + ε' / (K + 1) * K) := h1
    _ ≤ ENNReal.ofReal H + ENNReal.ofReal (ε' / (K + 1) * K) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal H + ε' := by
        refine add_le_add le_rfl ?_
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal h2

/-- `a + a ≤ b` gives `a ≤ b/2`. -/
theorem ennreal_half {S : ENNReal} {R : ℝ} (hR : 0 ≤ R) (h : S + S ≤ ENNReal.ofReal R) :
    S ≤ ENNReal.ofReal (R / 2) := by
  by_contra hc
  push Not at hc
  have h1 : ENNReal.ofReal (R / 2) + ENNReal.ofReal (R / 2) < S + S :=
    ENNReal.add_lt_add hc hc
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at h1
  exact absurd h (not_le.mpr h1)

/-- `√(2π)/π ≤ 0.797885`, `√(2π) ≤ 2.5067`, `1/√π ≤ 0.56419`, `√π ≤ 1.7725`, `√2 ≤ 1.4143`. -/
theorem haus_consts : Real.sqrt (2 * Real.pi) / Real.pi ≤ 0.797885 ∧
    Real.sqrt (2 * Real.pi) ≤ 2.5067 ∧ 1 / Real.sqrt Real.pi ≤ 0.56419 ∧
    Real.sqrt Real.pi ≤ 1.7725 ∧ Real.sqrt 2 ≤ 1.4143 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨?_, (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith),
    ?_, (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith),
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)⟩
  · rw [div_le_iff₀ Real.pi_pos]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  · have hs : 1.772453 ≤ Real.sqrt Real.pi :=
      (Real.le_sqrt (by norm_num) Real.pi_pos.le).mpr (by nlinarith)
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- The closing arithmetic of the complex case, over atoms: `a = |η|₂√T`, `b = |η·log|₂√T`,
`X = log qT − 2.33787`, `Y = ½log qT + 17.21`, `G = g(T) + g(1)`, `N₁ = 0.819 log q + 16.8`. -/
theorem haus_close_c {p n1 a b X x Y G N1 ε K0 : ℝ} (hp1 : p ≤ 0.797885) (hX : 0 ≤ X)
    (hXx : X = x - 2.33787) (ha : 0 ≤ a) (hb : 0 ≤ b) (hY : 0 ≤ Y) (hG : 0 ≤ G) (hn1 : 0 ≤ n1)
    (s2 : ℝ) (hs2 : s2 ≤ 1.4143) (sp : ℝ) (hsp : sp ≤ 2.5067) :
    n1 * N1 + (p * X * a + ε * K0 + (s2 * n1 + ε) * G + sp * b * Y) ≤
      0.7979 * a * (x - 2.3378) + 2.5067 * b * Y + n1 * (N1 + 1.4143 * G) + ε * (K0 + G) := by
  have k1 : p * X * a ≤ 0.7979 * a * (x - 2.3378) := by
    have h1 : p * X ≤ 0.797885 * X := mul_le_mul_of_nonneg_right hp1 hX
    have h2 : 0.797885 * X ≤ 0.7979 * (x - 2.3378) := by rw [hXx]; linarith
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) ha
    linarith
  have k2 : sp * b * Y ≤ 2.5067 * b * Y := by
    have := mul_le_mul_of_nonneg_right hsp (mul_nonneg hb hY)
    linarith
  have k3 : s2 * n1 * G ≤ 1.4143 * n1 * G := by
    have := mul_le_mul_of_nonneg_right hs2 (mul_nonneg hn1 hG)
    linarith
  linarith

/-- **`lem:hausierer`, CORRECTED — PROVED from `CritDeriv`, `AbelZeros`, `RealSym`**, with
`ZeroCount` (the link's own premise). Complex `χ`: `F_ε = √(|G(½+it)|² + |G(½−it)|² + ε²)`, real
`χ`: the zeros pair `ρ ↔ ρ̄` (`RealSym`) and `F_ε = √(|G(½+it)|² + ε²) + √(|G(½−it)|² + ε²)`;
`AbelZeros` + Cauchy–Schwarz (`high_bound`) with `crit_bessel` for `∫|G|²` and `∫|G'|²`; `ε → 0`. -/
theorem hausierer_of (hAb : AbelZeros) (hCD : CritDeriv) (hRS : RealSym) : Hausierer := by
  intro hZC η hreg q _ χ hχ δ T hT1 hqT hgrh
  have hD := hCD η hreg δ
  obtain ⟨hL1, hL2, hLl1, hLl2, hdiv, h6⟩ := hreg
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hm : AEStronglyMeasurable η (volume.restrict (Ioi 0)) := hL1.1
  have hml : AEStronglyMeasurable (llog η) (volume.restrict (Ioi 0)) := hLl1.1
  have hI2 : IntegrableOn (fun t => η t ^ 2) (Ioi 0) := (memLp_two_iff_integrable_sq hm).mp hL2
  have hIl2 : IntegrableOn (fun t => llog η t ^ 2) (Ioi 0) :=
    (memLp_two_iff_integrable_sq hml).mp hLl2
  have hdl := llog_div_sqrt_int η hm h6
  have hdc := continuous_gcl (llog η) δ hml hdl
  have hB1 := crit_bessel η δ hdiv hI2 hT0.le
  have hB2 := crit_bessel (llog η) δ hdl hIl2 hT0.le
  have hgc := cont_of_deriv hD
  have hI1 : 0 ≤ ∫ t in Ioi (0 : ℝ), η t ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hIl : 0 ≤ ∫ t in Ioi (0 : ℝ), llog η t ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hn1 : 0 ≤ n1h η := n1h_nonneg η
  have hgn : ∀ τ, ‖gcl η δ τ‖ ≤ n1h η := norm_gcl_le η δ
  obtain ⟨hL74, hLx⟩ := crit_L_facts hq0 hT0 hqT
  have hX : 0 ≤ Real.log (q * T) - 2.33787 := by linarith
  have hY : 0 ≤ 0.5 * Real.log (q * T) + 17.21 := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hgT : 0 ≤ gZ q T := gZ_nonneg (by linarith)
  have hg1 : 0 ≤ gZ q 1 := gZ_nonneg (by linarith)
  have hg1e : gZ q 1 = 0.5 * Real.log q + 17.7 := by unfold gZ; rw [mul_one]
  have hgTe : gZ q T = 0.5 * Real.log (q * T) + 17.7 := rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := haus_consts
  have hsT := Real.sqrt_nonneg T
  have hs1 := Real.sqrt_nonneg (∫ t in Ioi (0 : ℝ), η t ^ 2)
  have hsl := Real.sqrt_nonneg (∫ t in Ioi (0 : ℝ), llog η t ^ 2)
  have hK0 : 0 ≤ Real.sqrt T * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi := by
    have := mul_nonneg (mul_nonneg hsT hsT) hX
    positivity
  -- the zero sum on the critical line (GRH to `T`)
  have hcl : zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖Gm η δ ρ‖) =
      zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖) := by
    refine zsum_congr χ fun ρ hρ => ?_
    have hre : ρ.re = 1 / 2 := hgrh ρ hρ.1 hρ.2
    have e : (1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I = ρ := by
      apply Complex.ext <;> simp [hre]
    unfold gcl
    rw [e]
  have hsp := zsum_split1 χ (T := T) (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖)
  have hlow := low_sum hZC hχ (gcl η δ) hn1 hgn
  -- `∫_1^T (|G(t)|² + |G(−t)|²) ≤ 2π|η|₂²`, same for `G'`
  have hG2 : ∫ t in (1 : ℝ)..T, (‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2) ≤
      2 * Real.pi * ∫ t in Ioi (0 : ℝ), η t ^ 2 :=
    (sym_int_le (φ := fun t => ‖gcl η δ t‖ ^ 2) (by fun_prop) (fun t => sq_nonneg _) T).trans hB1
  have hD2 : ∫ t in (1 : ℝ)..T, (‖gcl (llog η) δ t‖ ^ 2 + ‖gcl (llog η) δ (-t)‖ ^ 2) ≤
      2 * Real.pi * ∫ t in Ioi (0 : ℝ), llog η t ^ 2 :=
    (sym_int_le (φ := fun t => ‖gcl (llog η) δ t‖ ^ 2) (by fun_prop) (fun t => sq_nonneg _)
      T).trans hB2
  have hcg : Continuous fun t => ‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2 := by fun_prop
  have hcd : Continuous fun t => ‖gcl (llog η) δ t‖ ^ 2 + ‖gcl (llog η) δ (-t)‖ ^ 2 := by
    fun_prop
  have hHs : ∀ s ∈ {s : ℂ | 1 < |s.im| ∧ |s.im| ≤ T}, starRingEnd ℂ s ∈
      {s : ℂ | 1 < |s.im| ∧ |s.im| ≤ T} := fun s hs => by
    simp only [mem_setOf_eq, Complex.conj_im, abs_neg] at hs ⊢
    exact hs
  have hpt_abs : ∀ γ : ℝ, (‖gcl η δ γ‖ = ‖gcl η δ |γ|‖ ∧ ‖gcl η δ (-γ)‖ = ‖gcl η δ (-|γ|)‖) ∨
      (‖gcl η δ γ‖ = ‖gcl η δ (-|γ|)‖ ∧ ‖gcl η δ (-γ)‖ = ‖gcl η δ |γ|‖) := fun γ => by
    rcases le_total 0 γ with h | h
    · left
      rw [abs_of_nonneg h]
      exact ⟨rfl, rfl⟩
    · right
      rw [abs_of_nonpos h, neg_neg]
      exact ⟨rfl, rfl⟩
  refine ⟨?_, fun hr => ?_⟩
  · -- complex `χ`
    rw [hcl]
    refine ennreal_le_of_eps (K := Real.sqrt T * Real.sqrt T * (Real.log (q * T) - 2.33787) /
      Real.pi + (gZ q T + gZ q 1)) (by positivity) fun ε hε => ?_
    obtain ⟨F, F', hFd, hFc, hF0, hF2, hF'2⟩ := smooth_c hD hdc hε
    have hFa : ∀ t, ‖gcl η δ t‖ ≤ F |t| := fun t => by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (hF0 _) two_ne_zero).mp ?_
      rw [hF2]
      rcases hpt_abs t with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
        linarith [sq_nonneg ‖gcl η δ (-|t|)‖, sq_nonneg ε]
      · rw [h1]
        linarith [sq_nonneg ‖gcl η δ |t|‖, sq_nonneg ε]
    have hFb : ∀ t, F t ≤ Real.sqrt 2 * n1h η + ε := fun t => by
      refine (pow_le_pow_iff_left₀ (hF0 _) (by positivity) two_ne_zero).mp ?_
      rw [hF2]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hgn t) 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (hgn (-t)) 2
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have e : (Real.sqrt 2 * n1h η + ε) ^ 2 =
          Real.sqrt 2 ^ 2 * n1h η ^ 2 + 2 * (Real.sqrt 2 * n1h η * ε) + ε ^ 2 := by ring
      have h3 : 0 ≤ Real.sqrt 2 * n1h η * ε := by positivity
      rw [e, hs2]
      linarith
    have hA : ∫ t in (1 : ℝ)..T, F t ^ 2 ≤ (Real.sqrt (2 * Real.pi) *
        Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) + ε * Real.sqrt T) ^ 2 := by
      have e1 : ∫ t in (1 : ℝ)..T, F t ^ 2 =
          (∫ t in (1 : ℝ)..T, (‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2)) + (T - 1) * ε ^ 2 := by
        rw [intervalIntegral.integral_congr
          (g := fun t => (‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2) + ε ^ 2) (fun t _ => hF2 t),
          intervalIntegral.integral_add (hcg.intervalIntegrable 1 T) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
      have hp : (Real.sqrt (2 * Real.pi) * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) ^ 2 =
          2 * Real.pi * ∫ t in Ioi (0 : ℝ), η t ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hI1]
      have hq : (ε * Real.sqrt T) ^ 2 = ε ^ 2 * T := by
        rw [mul_pow, Real.sq_sqrt hT0.le]
      have hsq : (Real.sqrt (2 * Real.pi) * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) +
          ε * Real.sqrt T) ^ 2 = (Real.sqrt (2 * Real.pi) *
            Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) ^ 2 + 2 * ((Real.sqrt (2 * Real.pi) *
              Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) * (ε * Real.sqrt T)) +
                (ε * Real.sqrt T) ^ 2 := by ring
      have hpq : 0 ≤ (Real.sqrt (2 * Real.pi) * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) *
          (ε * Real.sqrt T) := by positivity
      rw [e1, hsq, hp, hq]
      linarith [hG2, hpq, sq_nonneg ε]
    have hB : ∫ t in (1 : ℝ)..T, F' t ^ 2 ≤ (Real.sqrt (2 * Real.pi) *
        Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hIl]
      exact le_trans (intervalIntegral.integral_mono_on hT1
        ((hFc.pow 2).intervalIntegrable 1 T) (hcd.intervalIntegrable 1 T)
        fun t _ => hF'2 t) hD2
    have hH := high_bound hAb hZC hχ hT1 hqT (fun t _ => hFd t) hFc.continuousOn
      (fun t _ => hF0 t) (by positivity) (by positivity) hA hB (hFb 1) (hFb T)
    have hHpt : zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T}
        (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖) ≤
        zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal (F |ρ.im|)) :=
      zsum_mono χ fun ρ _ => ENNReal.ofReal_le_ofReal (hFa ρ.im)
    refine hsp.trans ((add_le_add hlow (hHpt.trans hH)).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by
      have : 0 ≤ Real.sqrt 2 * n1h η + ε := by positivity
      positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold hbC MajSp.l2
    rw [hg1e, hgTe]
    have k1 : (Real.sqrt (2 * Real.pi) * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) +
        ε * Real.sqrt T) * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi =
        Real.sqrt (2 * Real.pi) / Real.pi * (Real.log (q * T) - 2.33787) *
          (Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T) +
        ε * (Real.sqrt T * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi) := by ring
    have k2 : Real.sqrt (2 * Real.pi) * Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) *
        Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) = Real.sqrt (2 * Real.pi) *
          (Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) * Real.sqrt T) *
            (0.5 * Real.log (q * T) + 17.21) := by ring
    have k3 : 0.7979 * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T *
        (Real.log (q * T) - 2.3378) = 0.7979 * (Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) *
          Real.sqrt T) * (Real.log (q * T) - 2.3378) := by ring
    have k4 : 2.5067 * Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) * Real.sqrt T *
        (0.5 * Real.log (q * T) + 17.21) = 2.5067 * (Real.sqrt (∫ t in Ioi (0 : ℝ),
          llog η t ^ 2) * Real.sqrt T) * (0.5 * Real.log (q * T) + 17.21) := by ring
    have k5 : n1h η * (0.819 * Real.log q + 16.8 + 1.4143 * (0.5 * Real.log q + 17.7) +
        1.4143 * (0.5 * Real.log (q * T) + 17.7)) = n1h η * (0.819 * Real.log q + 16.8 +
          1.4143 * (0.5 * Real.log (q * T) + 17.7 + (0.5 * Real.log q + 17.7))) := by ring
    rw [k1, k2, k3, k4, k5]
    exact haus_close_c c1 hX rfl (mul_nonneg hs1 hsT) (mul_nonneg hsl hsT)
      hY (by linarith) hn1 _ c5 _ c2
  · -- real `χ`: the zeros pair with their conjugates
    rw [hcl]
    refine ennreal_le_of_eps (K := Real.sqrt T * Real.sqrt T * (Real.log (q * T) - 2.33787) /
      Real.pi + (gZ q T + gZ q 1)) (by positivity) fun ε hε => ?_
    obtain ⟨F, F', hFd, hFc, hFlo, hFhi, hF2, hF'2⟩ := smooth_r hD hdc hε
    have hF0 : ∀ t, 0 ≤ F t := fun t => le_trans (by positivity) (hFlo t)
    have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun t => (hFd t).continuousAt
    have hFub : ∀ t, F t ≤ 2 * (n1h η + ε) := fun t => by
      have := hFhi t
      have := hgn t
      have := hgn (-t)
      linarith
    have hA : ∫ t in (1 : ℝ)..T, F t ^ 2 ≤ (2 * Real.sqrt Real.pi *
        Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) + 2 * ε * Real.sqrt T) ^ 2 := by
      have h1 : ∫ t in (1 : ℝ)..T, F t ^ 2 ≤
          ∫ t in (1 : ℝ)..T, 2 * ((‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2) + 2 * ε ^ 2) :=
        intervalIntegral.integral_mono_on hT1 ((hFcont.pow 2).intervalIntegrable 1 T)
          ((continuous_const.mul (hcg.add continuous_const)).intervalIntegrable 1 T)
          fun t _ => by have := hF2 t; linarith
      have e1 : ∫ t in (1 : ℝ)..T, 2 * ((‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2) + 2 * ε ^ 2) =
          2 * (∫ t in (1 : ℝ)..T, (‖gcl η δ t‖ ^ 2 + ‖gcl η δ (-t)‖ ^ 2)) +
            4 * ε ^ 2 * (T - 1) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          (hcg.intervalIntegrable 1 T) intervalIntegrable_const, intervalIntegral.integral_const,
          smul_eq_mul]
        ring
      rw [e1] at h1
      have hp : (2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) ^ 2 =
          2 * (2 * Real.pi * ∫ t in Ioi (0 : ℝ), η t ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hI1]
        ring
      have hq : (2 * ε * Real.sqrt T) ^ 2 = 4 * ε ^ 2 * T := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hT0.le]
        ring
      have hsq : (2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) +
          2 * ε * Real.sqrt T) ^ 2 = (2 * Real.sqrt Real.pi *
            Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) ^ 2 + 2 * ((2 * Real.sqrt Real.pi *
              Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) * (2 * ε * Real.sqrt T)) +
                (2 * ε * Real.sqrt T) ^ 2 := by ring
      have hpq : 0 ≤ (2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2)) *
          (2 * ε * Real.sqrt T) := by positivity
      rw [hsq, hp, hq]
      linarith [h1, hG2, hpq, sq_nonneg ε]
    have hB : ∫ t in (1 : ℝ)..T, F' t ^ 2 ≤ (2 * Real.sqrt Real.pi *
        Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2)) ^ 2 := by
      have hp : (2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2)) ^ 2 =
          2 * (2 * Real.pi * ∫ t in Ioi (0 : ℝ), llog η t ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hIl]
        ring
      rw [hp]
      have h1 : ∫ t in (1 : ℝ)..T, F' t ^ 2 ≤
          ∫ t in (1 : ℝ)..T, 2 * (‖gcl (llog η) δ t‖ ^ 2 + ‖gcl (llog η) δ (-t)‖ ^ 2) :=
        intervalIntegral.integral_mono_on hT1 ((hFc.pow 2).intervalIntegrable 1 T)
          ((continuous_const.mul hcd).intervalIntegrable 1 T) fun t _ => hF'2 t
      rw [intervalIntegral.integral_const_mul] at h1
      linarith
    have hH := high_bound hAb hZC hχ hT1 hqT (fun t _ => hFd t) hFc.continuousOn
      (fun t _ => hF0 t) (by positivity) (by positivity) hA hB (hFub 1) (hFub T)
    -- pair each zero with its conjugate
    have hsym : zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖) +
        zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖) ≤
        zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal (F |ρ.im|)) := by
      have h1 := zsum_conj hRS hr hHs (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖)
      calc zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖) +
            zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖)
          = zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖) +
              zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T}
                (fun ρ => ENNReal.ofReal ‖gcl η δ (starRingEnd ℂ ρ).im‖) := by
            congr 1
            exact h1.symm
        _ = zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖gcl η δ ρ.im‖ +
              ENNReal.ofReal ‖gcl η δ (starRingEnd ℂ ρ).im‖) := (zsum_add' χ _ _ _).symm
        _ ≤ zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} (fun ρ => ENNReal.ofReal (F |ρ.im|)) := by
            refine zsum_mono χ fun ρ _ => ?_
            rw [Complex.conj_im, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
            refine ENNReal.ofReal_le_ofReal ?_
            rcases hpt_abs ρ.im with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2]
              exact hFlo _
            · rw [h1, h2, add_comm]
              exact hFlo _
    have hRnn : 0 ≤ (2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) +
        2 * ε * Real.sqrt T) * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi +
        2 * (n1h η + ε) * (gZ q T + gZ q 1) + 2 * Real.sqrt Real.pi *
          Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) * Real.sqrt T *
            (0.5 * Real.log (q * T) + 17.21) := by
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt Real.pi *
        Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) + 2 * ε * Real.sqrt T) hsT) hX
      have : 0 ≤ 0.5 * Real.log (q * T) + 17.21 := by linarith
      positivity
    have hhalf := ennreal_half hRnn (hsym.trans hH)
    refine hsp.trans ((add_le_add hlow hhalf).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold hbR MajSp.l2
    rw [hg1e, hgTe]
    have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
    have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hinv : Real.sqrt Real.pi / Real.pi = 1 / Real.sqrt Real.pi := by
      rw [div_eq_div_iff Real.pi_pos.ne' hspi.ne', one_mul, hpp]
    have k1 : (2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) +
        2 * ε * Real.sqrt T) * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi =
        2 * (Real.sqrt Real.pi / Real.pi * (Real.log (q * T) - 2.33787) *
          (Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T)) +
        2 * ε * (Real.sqrt T * Real.sqrt T * (Real.log (q * T) - 2.33787) / Real.pi) := by ring
    rw [k1, hinv]
    have k2 : 1 / Real.sqrt Real.pi * (Real.log (q * T) - 2.33787) *
        (Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T) ≤
        0.5642 * (Real.log (q * T) - 2.3378) *
          (Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hs1 hsT)
      linarith [mul_le_mul_of_nonneg_right c3 hX, hX]
    have k3 : Real.sqrt Real.pi * (Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) * Real.sqrt T *
        (0.5 * Real.log (q * T) + 17.21)) ≤ 1.7725 * (Real.sqrt (∫ t in Ioi (0 : ℝ),
          llog η t ^ 2) * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21)) :=
      mul_le_mul_of_nonneg_right c4 (mul_nonneg (mul_nonneg hsl hsT) (by linarith))
    have k4 : 2 * Real.sqrt Real.pi * Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) *
        Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) = 2 * (Real.sqrt Real.pi *
          (Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) * Real.sqrt T *
            (0.5 * Real.log (q * T) + 17.21))) := by ring
    have k5 : 0.5642 * Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T *
        (Real.log (q * T) - 2.3378) = 0.5642 * (Real.log (q * T) - 2.3378) *
          (Real.sqrt (∫ t in Ioi (0 : ℝ), η t ^ 2) * Real.sqrt T) := by ring
    have k6 : 1.7725 * Real.sqrt (∫ t in Ioi (0 : ℝ), llog η t ^ 2) * Real.sqrt T *
        (0.5 * Real.log (q * T) + 17.21) = 1.7725 * (Real.sqrt (∫ t in Ioi (0 : ℝ),
          llog η t ^ 2) * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21)) := by ring
    rw [k4, k5, k6]
    linarith only [k2, k3]

/-! ## (9) `CritDeriv` — PROVED (differentiation under the integral sign) -/

/-- `d/dτ t^{(½ + iτ) − 1} = i log t · t^{(½ + iτ) − 1}` for `t > 0`. -/
theorem hasDerivAt_cpow_crit {t : ℝ} (ht : 0 < t) (τ : ℝ) :
    HasDerivAt (fun y : ℝ => (t : ℂ) ^ ((1 / 2 + (y : ℂ) * Complex.I) - 1))
      ((t : ℂ) ^ ((1 / 2 + (τ : ℂ) * Complex.I) - 1) * (Real.log t : ℂ) * Complex.I) τ := by
  have hf : HasDerivAt (fun z : ℂ => (1 / 2 + z * Complex.I) - 1) Complex.I (τ : ℂ) := by
    have := (((hasDerivAt_id (τ : ℂ)).mul_const Complex.I).const_add (1 / 2)).sub_const 1
    simpa using this
  have hz := hf.const_cpow (c := (t : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  rw [← Complex.ofReal_log ht.le] at hz
  exact hz.comp_ofReal

/-- **`CritDeriv` PROVED**: on the critical line `|t^{s−1}| = t^{−1/2}` does not depend on `τ`, so
`|∂_τ| ≤ |log t||η(t)|/√t`, integrable by `llog_div_sqrt_int`
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). -/
theorem critDeriv_holds : CritDeriv := by
  intro η hreg δ τ₀
  obtain ⟨hL1, _, hLl1, _, hdiv, h6⟩ := hreg
  have hm : AEStronglyMeasurable η (volume.restrict (Ioi 0)) := hL1.1
  have hml : AEStronglyMeasurable (llog η) (volume.restrict (Ioi 0)) := hLl1.1
  have hdl := llog_div_sqrt_int η hm h6
  have hem : AEStronglyMeasurable (fun t : ℝ => e (δ * t)) (volume.restrict (Ioi 0)) :=
    (continuous_e'.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hcpm : ∀ τ : ℝ, AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ ((1 / 2 + (τ : ℂ) * Complex.I) - 1)) (volume.restrict (Ioi 0)) :=
    fun τ => (Complex.measurable_ofReal.pow_const _).aestronglyMeasurable
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (τ t : ℝ) => (t : ℂ) ^ ((1 / 2 + (τ : ℂ) * Complex.I) - 1) •
      (((η t : ℝ) : ℂ) * e (δ * t)))
    (F' := fun (τ t : ℝ) => Complex.I * ((t : ℂ) ^ ((1 / 2 + (τ : ℂ) * Complex.I) - 1) •
      (((llog η t : ℝ) : ℂ) * e (δ * t))))
    (x₀ := τ₀) (bound := fun t => |llog η t| / Real.sqrt t) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun τ =>
      (hcpm τ).smul ((Complex.continuous_ofReal.comp_aestronglyMeasurable hm).mul hem))
    ?_ ?_ ?_ ?_ ?_
  · refine hkey.2.congr_deriv ?_
    rw [integral_const_mul]
    rfl
  · -- `F τ₀` is integrable: `|F τ₀ t| = |η(t)|/√t`
    refine Integrable.mono' hdiv.norm ((hcpm τ₀).smul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hm).mul hem))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_))
    have ht0 : 0 < t := ht
    rw [norm_smul, norm_cpow_crit ht0, norm_mul, e_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr ht0)]
    exact le_of_eq (by ring)
  · exact (aestronglyMeasurable_const.mul ((hcpm τ₀).smul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hml).mul hem)))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht τ _ => ?_)
    have ht0 : 0 < t := ht
    rw [norm_mul, Complex.norm_I, one_mul, norm_smul, norm_cpow_crit ht0, norm_mul, e_norm,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (by ring)
  · refine hdl.norm.congr (ae_of_all _ fun t => ?_)
    simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg t)]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht τ _ => ?_)
    have ht0 : 0 < t := ht
    refine ((hasDerivAt_cpow_crit ht0 τ).smul_const (((η t : ℝ) : ℂ) * e (δ * t))).congr_deriv ?_
    unfold llog
    simp only [smul_eq_mul]
    push_cast
    ring

/-- **`lem:hausierer` from `AbelZeros` and `RealSym`** (`CritDeriv` discharged). -/
theorem hausierer_of' (hAb : AbelZeros) (hRS : RealSym) : Hausierer :=
  hausierer_of hAb critDeriv_holds hRS

end Principia.Common.TernaryGoldbach.HM
