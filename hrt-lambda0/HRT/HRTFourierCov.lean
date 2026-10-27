import HRTChar
import HRTSmall

/-!
# The Fourier covariance of the time–frequency shift

`HRTSmall.fourier_tfShift` already proves, axiom-free, that the Fourier transform implements the
symplectic rotation `(x,ω) ↦ (ω,−x)`:

  `𝓕 (π(x,ω) g) ξ = e^{2πixω} · π(ω,−x) (𝓕 g) ξ`

but for the CONCRETE integral on raw functions.  This file lifts it to Schwartz space, which is
the form the `L²` density argument consumes.

The lift is essentially free: `SchwartzMap.fourierTransformCLM` is *defined* as
`mkCLM ((𝓕 : (V → E) → (V → E)) ·)`, so its underlying function IS the raw Fourier integral of the
coercion, and `HRTSmall.fourier_tfShift` applies pointwise on the nose.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000

namespace HRTFourierCov

open Complex MeasureTheory SchwartzMap FourierTransform HRTChar

/-- **The Schwartz Fourier transform is the raw Fourier integral on the underlying function.**

Definitional, because `fourierTransformCLM` is built by `mkCLM` directly from `𝓕`. -/
theorem coeFn_fourierCLM (f : 𝓢(ℝ, ℂ)) :
    ⇑(SchwartzMap.fourierTransformCLM ℂ f) = 𝓕 (⇑f) := rfl

/-- The Schwartz-space shift agrees pointwise with `HRTSmall.tfShift`. -/
theorem coeFn_tfS (x ω : ℝ) (f : 𝓢(ℝ, ℂ)) :
    ⇑(tfS x ω f) = HRTSmall.tfShift x ω (⇑f) := by
  funext t
  rw [tfS_apply]
  rfl

/-- **Fourier covariance on Schwartz space.**  `𝓕 ∘ π(x,ω) = e^{2πixω} · π(ω,−x) ∘ 𝓕`. -/
theorem fourier_tfS (x ω : ℝ) (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.fourierTransformCLM ℂ (tfS x ω f)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))
        • tfS ω (-x) (SchwartzMap.fourierTransformCLM ℂ f) := by
  refine SchwartzMap.ext fun ξ => ?_
  have hlhs : (SchwartzMap.fourierTransformCLM ℂ (tfS x ω f)) ξ
      = 𝓕 (HRTSmall.tfShift x ω (⇑f)) ξ := by
    rw [show ((SchwartzMap.fourierTransformCLM ℂ (tfS x ω f)) ξ) = 𝓕 (⇑(tfS x ω f)) ξ from rfl,
      coeFn_tfS]
  rw [hlhs, HRTSmall.fourier_tfShift]
  rw [SchwartzMap.smul_apply, tfS_apply, coeFn_fourierCLM]
  rfl

/-! ### Transport to `L²` by density

Both sides are continuous in the window and agree on the dense range of `SchwartzMap.toLpCLM`,
where `TFL_toLp`, `SchwartzMap.toLp_fourier_eq` and `fourier_tfS` settle it. -/

/-- The two sides agree on a Schwartz window. -/
theorem fourier_TFL_toLp (x ω : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Lp.fourierTransformₗᵢ ℝ ℂ (TFL x ω (f.toLp 2 (volume : Measure ℝ)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))
        • TFL ω (-x) (Lp.fourierTransformₗᵢ ℝ ℂ (f.toLp 2 (volume : Measure ℝ))) := by
  rw [TFL_toLp]
  rw [show Lp.fourierTransformₗᵢ ℝ ℂ ((tfS x ω f).toLp 2 (volume : Measure ℝ))
      = (SchwartzMap.fourierTransformCLM ℂ (tfS x ω f)).toLp 2 (volume : Measure ℝ) from
    SchwartzMap.toLp_fourier_eq _]
  rw [fourier_tfS]
  rw [show Lp.fourierTransformₗᵢ ℝ ℂ (f.toLp 2 (volume : Measure ℝ))
      = (SchwartzMap.fourierTransformCLM ℂ f).toLp 2 (volume : Measure ℝ) from
    SchwartzMap.toLp_fourier_eq _]
  rw [TFL_toLp]
  -- `SchwartzMap.toLp_smul` does not exist; `toLp` is linear via its bundled CLM
  exact (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 (volume : Measure ℝ)).map_smul
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ)))
    (tfS ω (-x) (SchwartzMap.fourierTransformCLM ℂ f))

/-- **Fourier covariance on all of `L²`.**  `𝓕 ∘ π(x,ω) = e^{2πixω} · π(ω,−x) ∘ 𝓕`.

Both sides are continuous in the window and agree on the dense range of `toLpCLM`
(`fourier_TFL_toLp`), so they agree everywhere.  `𝓕` implements the symplectic rotation
`(x,ω) ↦ (ω,−x)` — which is exactly the generator the Borel subgroup lacks. -/
theorem fourier_TFL (x ω : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp.fourierTransformₗᵢ ℝ ℂ (TFL x ω g)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))
        • TFL ω (-x) (Lp.fourierTransformₗᵢ ℝ ℂ g) := by
  have hd : DenseRange ⇑(SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  have hc1 : Continuous fun u : Lp ℂ 2 (volume : Measure ℝ) =>
      Lp.fourierTransformₗᵢ ℝ ℂ (TFL x ω u) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (TFL x ω).continuous
  have hc2 : Continuous fun u : Lp ℂ 2 (volume : Measure ℝ) =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))
        • TFL ω (-x) (Lp.fourierTransformₗᵢ ℝ ℂ u) :=
    (continuous_const_smul _).comp
      ((TFL ω (-x)).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  have hEq := hd.equalizer hc1 hc2 (funext fun f => fourier_TFL_toLp x ω f)
  exact congrFun hEq g

/-! ### Transferring a three-point dependence through `𝓕`

Three explicit terms rather than a `Finset` sum: `hthree` only ever needs three points, and this
avoids needing an `Lp.coeFn_sum` (which Mathlib does not appear to have).

The coefficients pick up unimodular phases, so they vanish together — which is all the HRT
conclusion cares about. -/

/-- **A three-point dependence transfers through the Fourier transform**, with the time–frequency
points rotated by `(x,ω) ↦ (ω,−x)`. -/
theorem fourier_three_dep (x₁ ω₁ x₂ ω₂ x₃ ω₃ : ℝ) (c₁ c₂ c₃ : ℂ)
    (G : Lp ℂ 2 (volume : Measure ℝ))
    (hdep : c₁ • TFL x₁ ω₁ G + c₂ • TFL x₂ ω₂ G + c₃ • TFL x₃ ω₃ G = 0) :
    (c₁ * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x₁ : ℂ) * (ω₁ : ℂ)))
        • TFL ω₁ (-x₁) (Lp.fourierTransformₗᵢ ℝ ℂ G)
      + (c₂ * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x₂ : ℂ) * (ω₂ : ℂ)))
        • TFL ω₂ (-x₂) (Lp.fourierTransformₗᵢ ℝ ℂ G)
      + (c₃ * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x₃ : ℂ) * (ω₃ : ℂ)))
        • TFL ω₃ (-x₃) (Lp.fourierTransformₗᵢ ℝ ℂ G) = 0 := by
  have h := congrArg (Lp.fourierTransformₗᵢ ℝ ℂ) hdep
  rw [map_add, map_add, map_smul, map_smul, map_smul, map_zero,
    fourier_TFL, fourier_TFL, fourier_TFL] at h
  rw [← h]
  simp only [smul_smul]

/-- **Unpack an `Lp` three-point dependence into the a.e. statement `hrt_shear` consumes.**

Eight `filter_upwards` hypotheses: `coeFn_add` ×2, `coeFn_smul` ×3, `coeFn_TFL` ×3.  The
`coeFn_smul`/`coeFn_TFL` facts go INSIDE the `simp only` that applies `Pi.add_apply`/`Pi.smul_apply`
— they cannot rewrite a goal reading `(F + G) t` until the application has been split. -/
theorem ae_of_lp_three_dep (y₁ η₁ y₂ η₂ y₃ η₃ : ℝ) (d₁ d₂ d₃ : ℂ)
    (H : Lp ℂ 2 (volume : Measure ℝ))
    (hdep : d₁ • TFL y₁ η₁ H + d₂ • TFL y₂ η₂ H + d₃ • TFL y₃ η₃ H = 0) :
    ∀ᵐ t : ℝ, d₁ * (chr η₁ t * H (t + -y₁)) + d₂ * (chr η₂ t * H (t + -y₂))
      + d₃ * (chr η₃ t * H (t + -y₃)) = 0 := by
  have h0 := Lp.eq_zero_iff_ae_eq_zero.mp hdep
  filter_upwards [h0,
    Lp.coeFn_add (d₁ • TFL y₁ η₁ H + d₂ • TFL y₂ η₂ H) (d₃ • TFL y₃ η₃ H),
    Lp.coeFn_add (d₁ • TFL y₁ η₁ H) (d₂ • TFL y₂ η₂ H),
    Lp.coeFn_smul d₁ (TFL y₁ η₁ H), Lp.coeFn_smul d₂ (TFL y₂ η₂ H),
    Lp.coeFn_smul d₃ (TFL y₃ η₃ H),
    coeFn_TFL y₁ η₁ H, coeFn_TFL y₂ η₂ H, coeFn_TFL y₃ η₃ H]
    with t ht0 ha1 ha2 hs1 hs2 hs3 hT1 hT2 hT3
  rw [ha1] at ht0
  -- `ha2` belongs in the simp set too: after `ha1` the hypothesis reads `(F + G) t`, in which
  -- `ha2`'s subterm does not occur until `Pi.add_apply` splits the application
  simp only [Pi.add_apply, ha2, Pi.smul_apply, hs1, hs2, hs3, hT1, hT2, hT3, smul_eq_mul] at ht0
  exact ht0

/-- **`𝓕` preserves non-vanishing.**  Needed by the assembly: `hrt_shear` requires a nonzero
window, and the window on the Fourier side is `𝓕 G`. -/
theorem fourier_ne_zero {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ≠ 0) :
    Lp.fourierTransformₗᵢ ℝ ℂ G ≠ 0 := by
  intro h
  exact hG ((Lp.fourierTransformₗᵢ ℝ ℂ).injective (by rw [h, map_zero]))

end HRTFourierCov

/-! ## Acceptance gate -/

#print axioms HRTFourierCov.coeFn_fourierCLM
#print axioms HRTFourierCov.coeFn_tfS
#print axioms HRTFourierCov.fourier_tfS
#print axioms HRTFourierCov.fourier_TFL_toLp
#print axioms HRTFourierCov.fourier_TFL
#print axioms HRTFourierCov.fourier_three_dep
#print axioms HRTFourierCov.ae_of_lp_three_dep
#print axioms HRTFourierCov.fourier_ne_zero
