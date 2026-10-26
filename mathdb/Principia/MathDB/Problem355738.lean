/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #355738 — the residue-class decomposition fails already at `n = 2`

MathDB open problem #355738.  For a continuous, normalized, `‖·‖₁`-dominating gauge norm `α` on
`L^∞(𝕋)`, let `H^α` be the `α`-closure of `H^∞` and `M_α(zⁿ) = [H^∞(zⁿ)]_α`.  Conjecture 4.4 of the
source asks whether

  `H^α = M_α(zⁿ) ⊕ z M_α(zⁿ) ⊕ ⋯ ⊕ z^{n-1} M_α(zⁿ)`.

**It fails for `n = 2`.**  Take `a = b = 2/3`, the weight `w(ζ) = |1 − ζ|^{-b}`, and
`f(z) = (1 + z)^{-a}`.  Then `α(f) < ∞`, because the weight's singularity sits at `1` where `f` is
bounded and `f`'s singularity sits at `−1` where the weight is bounded, while the even part

  `E₀f(z) = ½((1+z)^{-a} + (1−z)^{-a})`

has `∫|E₀f| w = ∞`: near `ζ = 1` the integrand dominates `θ^{-(a+b)}` and `a + b = 4/3 > 1`.
Since every member of `M_α(z²)` is even, a decomposition `f = g₀ + z g₁` forces `g₀ = E₀f`, which
is not even in `L^α`.

## What is proved

The analysis is proved outright — it is the content of the refutation:

* `alphaFinite_f` — both integrals defining `α(f)` converge;
* `not_alphaFinite_E0f` — the even part's weighted integral diverges;
* `no_decomposition` — hence no family of even, `α`-finite functions can decompose `f`.

Two soft steps of the source are hypotheses of `no_decomposition`, because stating them needs the
`H^α`-closure machinery, which is scaffolding rather than content: that members of `M_α(z²)` are
**even** (three lines in the source, from `α ≥ ‖·‖₁` and `L¹`-continuity of Fourier coefficients),
and that they lie in `L^α` (immediate from `M_α(z²) ⊆ H^α ⊆ L^α`).  Quantifying over an arbitrary
such family makes `no_decomposition` *stronger* than the conjecture needs.

## Three simplifications that make it tractable

1. **The weighted integrand collapses.**  `‖f θ‖ · w θ = (2|cos(θ/2)|)^{-a}(2|sin(θ/2)|)^{-a}`
   `= (2|sin θ|)^{-a}` exactly, by `Real.mul_rpow` and the double-angle identity — one function
   with three singularities rather than a product of two.
2. **The unweighted integral is free.**  `w ≥ 2^{-a}`, since the base `2|sin(θ/2)| ≤ 2` and the
   exponent is negative; so `‖f‖ ≤ 2^a ‖f‖ w` and the first integral follows from the second.
3. **`rpow`'s zero convention helps.**  `(0:ℝ)^{-a} = 0` and `(0:ℂ)^w = 0`, so
   `‖f θ‖ = (2|cos(θ/2)|)^{-a}` holds *everywhere*, `θ = ±π` included, with no side condition.

## Coordinates

The circle is parametrised by `θ`, with `pt θ = exp(iθ)`, so `f(−z)` is `f` at `θ + π`.  Integrals
run over one period `Ioc (-π) π`; the normalising constants `1/2π` and `c_b` are positive and
cancel out of every statement, so they are omitted — neither finiteness nor divergence is affected.
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Principia.MathDB.P355738

open MeasureTheory Set

/-! ### The exponent -/

/-- The common exponent `a = b = 2/3`.  What matters is `a < 1`, so each singularity alone is
integrable, and `a + a > 1`, so the two together are not. -/
noncomputable def a : ℝ := 2 / 3

theorem a_pos : 0 < a := by norm_num [a]

theorem a_lt_one : a < 1 := by norm_num [a]

theorem neg_a_gt : (-1 : ℝ) < -a := by norm_num [a]

theorem two_a_le : -(a + a) ≤ -1 := by norm_num [a]

/-- Raising to `-a` is antitone on the positives. -/
theorem rpow_neg_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : v ^ (-a) ≤ u ^ (-a) := by
  rw [Real.rpow_neg hu.le, Real.rpow_neg (hu.trans_le huv).le]
  have h1 : (0 : ℝ) < u ^ a := Real.rpow_pos_of_pos hu a
  have h2 : u ^ a ≤ v ^ a := Real.rpow_le_rpow hu.le huv a_pos.le
  first
  | exact inv_anti₀ h1 h2
  | exact inv_le_inv_of_le h1 h2
  | exact one_div_le_one_div_of_le h1 h2

/-! ### Interval integrability of the model singularities -/

theorem ii_rpow (u v : ℝ) : IntervalIntegrable (fun x : ℝ => x ^ (-a)) MeasureTheory.volume u v :=
  intervalIntegral.intervalIntegrable_rpow' neg_a_gt

theorem ii_sub (c u v : ℝ) :
    IntervalIntegrable (fun x : ℝ => (c - x) ^ (-a)) MeasureTheory.volume u v := by
  have h := (ii_rpow (c - u) (c - v)).comp_sub_left c
  simpa using h

theorem ii_add (c u v : ℝ) :
    IntervalIntegrable (fun x : ℝ => (x + c) ^ (-a)) MeasureTheory.volume u v := by
  have h := (ii_rpow (u + c) (v + c)).comp_add_right c
  simpa using h

/-! ### The circle, and the two boundary moduli -/

/-- The boundary point `e^{iθ}`. -/
noncomputable def pt (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

theorem pt_add_pi (θ : ℝ) : pt (θ + Real.pi) = -pt θ := by
  have hcast : ((θ + Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [pt, pt, hcast, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `|1 − e^{iθ}| = 2|sin(θ/2)|`. -/
theorem norm_one_sub_pt (θ : ℝ) : ‖1 - pt θ‖ = 2 * |Real.sin (θ / 2)| := by
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul' (θ / 2)
    have hθ : 2 * (θ / 2) = θ := by ring
    rw [hθ] at h
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2), h]
  have hsq : ‖1 - pt θ‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, pt, Complex.exp_mul_I]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]
    rw [mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ, hcos]
  have h1 : (0 : ℝ) ≤ ‖1 - pt θ‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [hsq, h1, h2]

/-- `|1 + e^{iθ}| = 2|cos(θ/2)|`. -/
theorem norm_one_add_pt (θ : ℝ) : ‖1 + pt θ‖ = 2 * |Real.cos (θ / 2)| := by
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2)
    have hθ : 2 * (θ / 2) = θ := by ring
    rw [hθ] at h
    linarith [h]
  have hsq : ‖1 + pt θ‖ ^ 2 = (2 * |Real.cos (θ / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, pt, Complex.exp_mul_I]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im]
    rw [mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ, hcos]
  have h1 : (0 : ℝ) ≤ ‖1 + pt θ‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.cos (θ / 2)| := by positivity
  nlinarith [hsq, h1, h2]

/-! ### The weight, the function, and its even part -/

/-- The weight `w(ζ) = |1 − ζ|^{-b}` in the `θ` coordinate. -/
noncomputable def wgt (θ : ℝ) : ℝ := (2 * |Real.sin (θ / 2)|) ^ (-a)

theorem wgt_nonneg (θ : ℝ) : 0 ≤ wgt θ := Real.rpow_nonneg (by positivity) _

/-- `f(z) = (1 + z)^{-a}` on the boundary. -/
noncomputable def f (θ : ℝ) : ℂ := (1 + pt θ) ^ (-(a : ℂ))

/-- The even residue component `E₀f(z) = ½(f(z) + f(−z))`. -/
noncomputable def E0f (θ : ℝ) : ℂ := (f θ + f (θ + Real.pi)) / 2

/-- The modulus of `f`, valid at **every** `θ`: at `θ = ±π` both sides are `0`, because
`(0:ℂ)^w = 0` and `(0:ℝ)^{-a} = 0`. -/
theorem norm_f (θ : ℝ) : ‖f θ‖ = (2 * |Real.cos (θ / 2)|) ^ (-a) := by
  by_cases h : (1 : ℂ) + pt θ = 0
  · rw [f, h, ← norm_one_add_pt θ, h]
    simp [Complex.zero_cpow, Real.zero_rpow, a_pos.ne']
  · rw [f, Complex.norm_cpow_of_ne_zero h, norm_one_add_pt]
    simp

/-- The modulus of `f(−z)`. -/
theorem norm_f_shift (θ : ℝ) : ‖f (θ + Real.pi)‖ = (2 * |Real.sin (θ / 2)|) ^ (-a) := by
  rw [norm_f]
  congr 1
  have hhalf : (θ + Real.pi) / 2 = θ / 2 + Real.pi / 2 := by ring
  rw [hhalf, Real.cos_add_pi_div_two]
  rw [abs_neg]

/-- **The collapse.**  `‖f θ‖ · w θ = (2|sin θ|)^{-a}`, one function instead of a product. -/
theorem norm_f_mul_wgt (θ : ℝ) : ‖f θ‖ * wgt θ = (2 * |Real.sin θ|) ^ (-a) := by
  rw [norm_f, wgt, ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    have hθ : 2 * (θ / 2) = θ := by ring
    rw [hθ] at h
    exact h
  rw [hsin, abs_mul, abs_mul]
  simp only [abs_two]
  ring

/-! ### `α`-finiteness -/

/-- Both integrals defining `α(h)` converge over one period. -/
def alphaFinite (h : ℝ → ℂ) : Prop :=
  IntegrableOn (fun θ => ‖h θ‖) (Ioc (-Real.pi) Real.pi) ∧
    IntegrableOn (fun θ => ‖h θ‖ * wgt θ) (Ioc (-Real.pi) Real.pi)

theorem measurable_sinPow : Measurable fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a) := by
  have h : Measurable fun θ : ℝ => 2 * |Real.sin θ| :=
    (continuous_const.mul Real.continuous_sin.abs).measurable
  first
  | exact h.rpow_const
  | exact h.pow_const _

/-- The model bound on a piece where `|sin|` is bounded below by a linear function. -/
theorem integrableOn_sinPow_piece {u v : ℝ} (huv : u ≤ v)
    (bnd : ℝ → ℝ) (hbnd : IntegrableOn bnd (Ioc u v))
    (hle : ∀ θ ∈ Ioc u v, (2 * |Real.sin θ|) ^ (-a) ≤ bnd θ) :
    IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc u v) := by
  refine Integrable.mono' hbnd measurable_sinPow.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact hle θ hθ

theorem sinPow_zero {θ : ℝ} (h : Real.sin θ = 0) : (2 * |Real.sin θ|) ^ (-a) = 0 := by
  rw [h]
  simp [Real.zero_rpow, a_pos.ne']

/-- The comparison on a piece: a linear lower bound on `|sin|` gives a power bound. -/
theorem sinPow_le {θ d : ℝ} (hd : 0 < d) (h : 2 / Real.pi * d ≤ |Real.sin θ|) :
    (2 * |Real.sin θ|) ^ (-a) ≤ (4 / Real.pi) ^ (-a) * d ^ (-a) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu : 0 < 4 / Real.pi * d := by positivity
  have huv : 4 / Real.pi * d ≤ 2 * |Real.sin θ| := by
    have h2 : 2 * (2 / Real.pi * d) ≤ 2 * |Real.sin θ| := by linarith
    calc 4 / Real.pi * d = 2 * (2 / Real.pi * d) := by ring
      _ ≤ 2 * |Real.sin θ| := h2
  have hres := rpow_neg_le hu huv
  rwa [Real.mul_rpow (by positivity) hd.le] at hres

/-! ### The four pieces -/

theorem intOn_A :
    IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc 0 (Real.pi / 2)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine integrableOn_sinPow_piece (by positivity)
    (fun θ => (4 / Real.pi) ^ (-a) * θ ^ (-a)) ?_ ?_
  · have h := ii_rpow 0 (Real.pi / 2)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at h
    exact h.const_mul _
  · rintro θ ⟨h0, h1⟩
    have hs : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin h0.le h1
    exact sinPow_le h0 (hs.trans (le_abs_self _))

theorem intOn_B :
    IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc (Real.pi / 2) Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine integrableOn_sinPow_piece (by linarith)
    (fun θ => (4 / Real.pi) ^ (-a) * (Real.pi - θ) ^ (-a)) ?_ ?_
  · have h := ii_sub Real.pi (Real.pi / 2) Real.pi
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
    exact h.const_mul _
  · rintro θ ⟨h0, h1⟩
    rcases eq_or_lt_of_le h1 with hpi' | hlt
    · have hz : Real.sin θ = 0 := by rw [hpi']; exact Real.sin_pi
      rw [sinPow_zero hz]
      positivity
    · have hd : 0 < Real.pi - θ := by linarith
      have hle : Real.pi - θ ≤ Real.pi / 2 := by linarith
      have hs : 2 / Real.pi * (Real.pi - θ) ≤ Real.sin (Real.pi - θ) :=
        Real.mul_le_sin hd.le hle
      rw [Real.sin_pi_sub] at hs
      exact sinPow_le hd (hs.trans (le_abs_self _))

theorem intOn_C :
    IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc (-(Real.pi / 2)) 0) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine integrableOn_sinPow_piece (by linarith)
    (fun θ => (4 / Real.pi) ^ (-a) * (0 - θ) ^ (-a)) ?_ ?_
  · have h := ii_sub 0 (-(Real.pi / 2)) 0
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
    exact h.const_mul _
  · rintro θ ⟨h0, h1⟩
    rcases eq_or_lt_of_le h1 with hz0 | hlt
    · have hz : Real.sin θ = 0 := by rw [hz0]; exact Real.sin_zero
      rw [sinPow_zero hz]
      positivity
    · have hd : 0 < 0 - θ := by linarith
      have hle : 0 - θ ≤ Real.pi / 2 := by linarith
      have hs : 2 / Real.pi * (0 - θ) ≤ Real.sin (0 - θ) := Real.mul_le_sin hd.le hle
      rw [zero_sub, Real.sin_neg] at hs
      have hb : -Real.sin θ ≤ |Real.sin θ| := neg_le_abs _
      have hs' : 2 / Real.pi * (0 - θ) ≤ |Real.sin θ| := by
        rw [zero_sub]
        exact hs.trans hb
      exact sinPow_le hd hs'

theorem intOn_D :
    IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc (-Real.pi) (-(Real.pi / 2))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine integrableOn_sinPow_piece (by linarith)
    (fun θ => (4 / Real.pi) ^ (-a) * (θ + Real.pi) ^ (-a)) ?_ ?_
  · have h := ii_add Real.pi (-Real.pi) (-(Real.pi / 2))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
    exact h.const_mul _
  · rintro θ ⟨h0, h1⟩
    have hd : 0 < θ + Real.pi := by linarith
    have hle : θ + Real.pi ≤ Real.pi / 2 := by linarith
    have hs : 2 / Real.pi * (θ + Real.pi) ≤ Real.sin (θ + Real.pi) := Real.mul_le_sin hd.le hle
    rw [Real.sin_add_pi] at hs
    have hb : -Real.sin θ ≤ |Real.sin θ| := neg_le_abs _
    exact sinPow_le hd (hs.trans hb)

/-- **The weighted integrand is integrable over one period.** -/
theorem intOn_sinPow :
    IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc (-Real.pi) Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hDC : IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc (-Real.pi) 0) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by linarith : -Real.pi ≤ -(Real.pi / 2))
      (by linarith : -(Real.pi / 2) ≤ (0 : ℝ))]
    exact intOn_D.union intOn_C
  have hAB : IntegrableOn (fun θ : ℝ => (2 * |Real.sin θ|) ^ (-a)) (Ioc 0 Real.pi) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      (by linarith : Real.pi / 2 ≤ Real.pi)]
    exact intOn_A.union intOn_B
  rw [← Set.Ioc_union_Ioc_eq_Ioc (by linarith : -Real.pi ≤ (0 : ℝ))
    (by linarith : (0 : ℝ) ≤ Real.pi)]
  exact hDC.union hAB

/-! ### `f` has finite `α`-norm -/

theorem measurable_normf : Measurable fun θ : ℝ => (2 * |Real.cos (θ / 2)|) ^ (-a) := by
  have h : Measurable fun θ : ℝ => 2 * |Real.cos (θ / 2)| :=
    (continuous_const.mul (Real.continuous_cos.comp
      (continuous_id.div_const 2)).abs).measurable
  first
  | exact h.rpow_const
  | exact h.pow_const _

theorem alphaFinite_f : alphaFinite f := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : IntegrableOn (fun θ => ‖f θ‖ * wgt θ) (Ioc (-Real.pi) Real.pi) :=
    intOn_sinPow.congr_fun (fun θ _ => (norm_f_mul_wgt θ).symm) measurableSet_Ioc
  refine ⟨?_, h2⟩
  have hae : ∀ᵐ θ : ℝ, θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using MeasureTheory.measure_singleton (μ := MeasureTheory.volume) (0 : ℝ)
  have hfeq : (fun θ : ℝ => ‖f θ‖) = fun θ : ℝ => (2 * |Real.cos (θ / 2)|) ^ (-a) :=
    funext norm_f
  have hmeas : Measurable fun θ : ℝ => ‖f θ‖ := by
    rw [hfeq]
    exact measurable_normf
  refine Integrable.mono' (h2.const_mul ((2 : ℝ) ^ a)) hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc]
    with θ hθ hmem
  have hne : Real.sin (θ / 2) ≠ 0 := by
    have hlt1 : -Real.pi < θ / 2 := by linarith [hmem.1]
    have hlt2 : θ / 2 < Real.pi := by linarith [hmem.2]
    intro hc
    have hz : θ / 2 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hlt1 hlt2).mp hc
    exact hθ (by linarith)
  have hs : 0 < 2 * |Real.sin (θ / 2)| := by positivity
  have hb : 2 * |Real.sin (θ / 2)| ≤ 2 := by
    have habs : |Real.sin (θ / 2)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    linarith
  have hw : (2 : ℝ) ^ (-a) ≤ wgt θ := rpow_neg_le hs hb
  have hf0 : (0 : ℝ) ≤ ‖f θ‖ := norm_nonneg _
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have h2a : (0 : ℝ) ≤ (2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) a
  have hstep : ‖f θ‖ * (2 : ℝ) ^ (-a) ≤ ‖f θ‖ * wgt θ := mul_le_mul_of_nonneg_left hw hf0
  rw [Real.norm_eq_abs, abs_of_nonneg hf0]
  nlinarith [hstep, hpow, h2a, hf0]

/-! ### The even part is not `α`-finite -/

theorem two_le_four_rpow : (2 : ℝ) ≤ (4 : ℝ) ^ a := by
  have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) a
  have hcube : ((4 : ℝ) ^ a) ^ (3 : ℕ) = 16 := by
    rw [← Real.rpow_natCast ((4 : ℝ) ^ a) 3, ← Real.rpow_mul (by norm_num)]
    norm_num [a]
  by_contra hcon
  push_neg at hcon
  have hlt : ((4 : ℝ) ^ a) ^ (3 : ℕ) < (2 : ℝ) ^ (3 : ℕ) := by
    first
    | exact pow_lt_pow_left hcon hnn (by norm_num)
    | exact pow_lt_pow_left₀ hcon hnn (by norm_num)
    | exact pow_lt_pow_left hcon hnn 3
  rw [hcube] at hlt
  norm_num at hlt

theorem two_le_rpow {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 4) : (2 : ℝ) ≤ θ ^ (-a) := by
  have hq : (1 / 4 : ℝ) ^ (-a) ≤ θ ^ (-a) := rpow_neg_le h0 h1
  have hval : (1 / 4 : ℝ) ^ (-a) = (4 : ℝ) ^ a := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num), inv_inv]
  rw [hval] at hq
  linarith [two_le_four_rpow, hq]

theorem two_abs_sin_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 4) :
    0 < 2 * |Real.sin (θ / 2)| := by
  have hhalf0 : 0 < θ / 2 := by linarith
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf0 (by linarith [Real.two_le_pi])
  rw [abs_of_pos hsin]
  linarith

theorem two_abs_sin_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 4) : 2 * |Real.sin (θ / 2)| ≤ θ := by
  have hhalf0 : 0 < θ / 2 := by linarith
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf0 (by linarith [Real.two_le_pi])
  rw [abs_of_pos hsin]
  have := Real.sin_le hhalf0.le
  linarith

/-- Near `θ = 0` the even part dominates `θ^{-a}/4`. -/
theorem norm_E0f_lower {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 4) : θ ^ (-a) / 4 ≤ ‖E0f θ‖ := by
  have hbig : θ ^ (-a) ≤ ‖f (θ + Real.pi)‖ := by
    rw [norm_f_shift]
    exact rpow_neg_le (two_abs_sin_pos h0 h1) (two_abs_sin_le h0 h1)
  have hcos : (1 : ℝ) ≤ 2 * |Real.cos (θ / 2)| := by
    have hc : 1 - (θ / 2) ^ 2 / 2 ≤ Real.cos (θ / 2) := Real.one_sub_sq_div_two_le_cos
    have hb : (1 : ℝ) / 2 ≤ Real.cos (θ / 2) := by nlinarith
    have := le_abs_self (Real.cos (θ / 2))
    linarith
  have hsmall : ‖f θ‖ ≤ 1 := by
    rw [norm_f]
    exact Real.rpow_le_one_of_one_le_of_nonpos hcos (by linarith [a_pos])
  have htwo : (2 : ℝ) ≤ θ ^ (-a) := two_le_rpow h0 h1
  have htri : ‖f (θ + Real.pi)‖ - ‖f θ‖ ≤ ‖f θ + f (θ + Real.pi)‖ := by
    have h := norm_sub_norm_le (f (θ + Real.pi)) (-(f θ))
    rw [norm_neg, sub_neg_eq_add] at h
    calc ‖f (θ + Real.pi)‖ - ‖f θ‖ ≤ ‖f (θ + Real.pi) + f θ‖ := h
      _ = ‖f θ + f (θ + Real.pi)‖ := by rw [add_comm]
  have hE : ‖E0f θ‖ = ‖f θ + f (θ + Real.pi)‖ / 2 := by
    rw [E0f, norm_div]
    simp
  rw [hE]
  linarith

/-- **The even part's weighted integral diverges.** -/
theorem not_alphaFinite_E0f : ¬ alphaFinite E0f := by
  rintro ⟨-, h2⟩
  have hpi := Real.two_le_pi
  have hsub : Ioo (0 : ℝ) (1 / 4) ⊆ Ioc (-Real.pi) Real.pi := by
    rintro x ⟨hx0, hx1⟩
    exact ⟨by linarith, by linarith⟩
  have hres : IntegrableOn (fun θ => ‖E0f θ‖ * wgt θ) (Ioo (0 : ℝ) (1 / 4)) := h2.mono_set hsub
  have hbad : ¬ IntegrableOn (fun θ : ℝ => θ ^ (-(a + a))) (Ioo (0 : ℝ) (1 / 4)) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
    push_neg
    exact two_a_le
  apply hbad
  have hmeas : Measurable fun θ : ℝ => θ ^ (-(a + a)) := by
    first
    | exact measurable_id.rpow_const
    | exact Real.measurable_rpow_const _
    | exact measurable_id.pow_const _
  refine Integrable.mono' (hres.const_mul 4) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  obtain ⟨h0, h1⟩ := hθ
  have hlow := norm_E0f_lower h0 h1.le
  have hwlow : θ ^ (-a) ≤ wgt θ :=
    rpow_neg_le (two_abs_sin_pos h0 h1.le) (two_abs_sin_le h0 h1.le)
  have hpos : (0 : ℝ) < θ ^ (-a) := Real.rpow_pos_of_pos h0 _
  have hsplit : θ ^ (-(a + a)) = θ ^ (-a) * θ ^ (-a) := by
    rw [← Real.rpow_add h0]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0.le _), hsplit]
  have hEnn : (0 : ℝ) ≤ ‖E0f θ‖ := norm_nonneg _
  nlinarith [hlow, hwlow, hpos, hEnn]

/-! ### The refutation -/

/-- **MathDB #355738: the decomposition fails at `n = 2`.**  No family `M` of *even* functions of
finite `α`-norm can decompose `f` as `g₀ + z g₁`, because that forces `g₀ = E₀f`, whose weighted
integral diverges.

Stated for an arbitrary such family, this is stronger than the conjecture needs: the source's
`M_α(z²)` is one instance, its members being even (from `α ≥ ‖·‖₁` and `L¹`-continuity of Fourier
coefficients) and `α`-finite (from `M_α(z²) ⊆ H^α ⊆ L^α`). -/
theorem no_decomposition (M : Set (ℝ → ℂ))
    (hEven : ∀ g ∈ M, ∀ θ : ℝ, g (θ + Real.pi) = g θ)
    (hFinite : ∀ g ∈ M, alphaFinite g) :
    ¬ ∃ g₀ ∈ M, ∃ g₁ ∈ M, ∀ θ : ℝ, f θ = g₀ θ + pt θ * g₁ θ := by
  rintro ⟨g₀, hg₀, g₁, hg₁, hrep⟩
  have hval : ∀ θ : ℝ, E0f θ = g₀ θ := by
    intro θ
    have h1 : f θ = g₀ θ + pt θ * g₁ θ := hrep θ
    have h2 : f (θ + Real.pi) = g₀ (θ + Real.pi) + pt (θ + Real.pi) * g₁ (θ + Real.pi) := hrep _
    rw [pt_add_pi, hEven g₀ hg₀ θ, hEven g₁ hg₁ θ] at h2
    rw [E0f, h1, h2]
    ring
  apply not_alphaFinite_E0f
  have hfun : E0f = g₀ := funext hval
  rw [hfun]
  exact hFinite g₀ hg₀

end Principia.MathDB.P355738
