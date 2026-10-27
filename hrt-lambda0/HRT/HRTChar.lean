import Mathlib

/-!
# Temperate growth of the modulation character

The metaplectic Fourier generator is the last thing standing between `HRTRect.hrt_shear` and the
two `Λ₀` triples with no zero time component.  The route to it is:

1. build the time–frequency shift as a continuous linear map on Schwartz space, out of
   `SchwartzMap.compCLM` (translation) and `SchwartzMap.smulLeftCLM` (modulation);
2. prove the Fourier covariance there — `HRTSmall.fourier_tfShift` already has it, axiom-free,
   at the level of the concrete integral;
3. push it to `Lp ℂ 2` by density, using `SchwartzMap.toLp_fourier_eq` and `denseRange_toLpCLM`.

Step 1 needs `SchwartzMap.smulLeftCLM`, whose hypothesis is that the multiplier has **temperate
growth**.  For the modulation character `t ↦ e^{2πiωt}` that is not in Mathlib (checked
2026-07-31), so it is proved here.

It is the easiest possible instance of temperate growth: every derivative of `t ↦ e^{ct}` is the
CONSTANT `c^n` times the function itself, and for purely imaginary `c` the function is
unimodular.  So the polynomial degree `k = 0` works for every `n` — no growth at all.

Note `Function.HasTemperateGrowth.of_fderiv` is useless here: it would ask for the temperate
growth of the derivative, which is again a multiple of the function.  The induction has to be on
the derivative ORDER, which is what `iteratedDeriv_cexp_linear` does.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000

namespace HRTChar

open Complex

/-- `fun_prop` has no smoothness lemma for `Complex.ofReal` — it says so explicitly ("No theorems
found for `Complex.ofReal`").  Register one, exactly as with `measurable_ee` in `HRTRectangular`.
Term mode, not `simpa`: `fun t => (t : ℂ)` and `⇑Complex.ofRealCLM` are defeq. -/
@[fun_prop]
theorem contDiff_ofReal {n : WithTop ℕ∞} : ContDiff ℝ n (fun t : ℝ => (t : ℂ)) :=
  Complex.ofRealCLM.contDiff

/-- **Every derivative of `t ↦ e^{ct}` is `c^n` times the function.**

The induction is on the derivative ORDER; each step is one application of `HasDerivAt.cexp`. -/
theorem iteratedDeriv_cexp_linear (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (c * (t : ℂ)))
      = fun t : ℝ => c ^ n * Complex.exp (c * (t : ℂ)) := by
  induction n with
  | zero =>
      funext t
      rw [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      -- TERM MODE, not `simpa`: the only discrepancy is `AddCommGroup ℂ` appearing as
      -- `instNormedAddCommGroup.toAddCommGroup` on one side and `Complex.addCommGroup` on the
      -- other.  Those are defeq, so elaboration at default transparency unifies them, whereas
      -- `simpa` matches syntactically and fails.
      have hbase : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
        simpa using hbase.const_mul c
      have h2 : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)))
          (Complex.exp (c * (t : ℂ)) * c) t := h1.cexp
      have h3 : HasDerivAt (fun s : ℝ => c ^ n * Complex.exp (c * (s : ℂ)))
          (c ^ n * (Complex.exp (c * (t : ℂ)) * c)) t := h2.const_mul _
      rw [h3.deriv]
      ring

/-- The character is unimodular. -/
theorem norm_char (ω t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))‖ = 1 := by
  have hct : 2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)
      = ((2 * Real.pi * ω * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hct, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero]

/-- **The modulation character has temperate growth.**

`k = 0` for every `n`: the derivatives do not grow at all, they are bounded by the constant
`‖2πiω‖ⁿ`. -/
theorem hasTemperateGrowth_char (ω : ℝ) :
    Function.HasTemperateGrowth
      (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))) := by
  -- `2 * π * I * ω * t` already parses as `(2 * π * I * ω) * t`, so no reassociation is needed:
  -- the goal's function IS `fun t => exp (c * t)` for `c = 2 * π * I * ω`, on the nose.
  refine ⟨by fun_prop, fun n => ⟨0, ‖2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)‖ ^ n, fun t => ?_⟩⟩
  refine le_of_eq ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  -- `simp only`, not `rw`: it beta-reduces the `(fun t => c^n * exp (c*t)) t` that the rewrite
  -- would otherwise leave standing
  simp only [iteratedDeriv_cexp_linear (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) n]
  rw [norm_mul, norm_pow, norm_char ω t, mul_one, pow_zero, mul_one]

/-! ### The time–frequency shift as a continuous linear map on Schwartz space

`π(x,ω) = (modulation by e^{2πiωt}) ∘ (translation by x)`, and Mathlib supplies both factors as
CLMs on `𝓢(ℝ,ℂ)`: `smulLeftCLM` for the first (needing `hasTemperateGrowth_char`, above) and
`compCLM` for the second. -/

open SchwartzMap

/-- Translation has temperate growth. -/
theorem hasTemperateGrowth_sub (x : ℝ) :
    Function.HasTemperateGrowth (fun t : ℝ => t - x) :=
  Function.HasTemperateGrowth.sub Function.HasTemperateGrowth.id'
    (Function.HasTemperateGrowth.const x)

/-- The polynomial bound `compCLM` additionally requires of the translation.

`‖t‖ ≤ ‖t-x‖ + ‖x‖ ≤ (1+‖x‖)(1+‖t-x‖)`, so `k = 1` and `C = 1 + ‖x‖`. -/
theorem sub_upper (x : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ t : ℝ, ‖t‖ ≤ C * (1 + ‖t - x‖) ^ k := by
  refine ⟨1, 1 + ‖x‖, fun t => ?_⟩
  have h1 : ‖t‖ ≤ ‖t - x‖ + ‖x‖ := by
    calc ‖t‖ = ‖(t - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖t - x‖ + ‖x‖ := norm_add_le _ _
  have h2 : ‖t - x‖ + ‖x‖ ≤ (1 + ‖x‖) * (1 + ‖t - x‖) ^ 1 := by
    rw [pow_one]
    nlinarith [norm_nonneg (t - x), norm_nonneg x]
  linarith

/-- **The time–frequency shift `π(x,ω)` as a continuous linear map on Schwartz space.** -/
noncomputable def tfS (x ω : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ
      (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)))).comp
    (SchwartzMap.compCLM ℂ (hasTemperateGrowth_sub x) (sub_upper x))

@[simp] theorem tfS_apply (x ω : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    tfS x ω f t
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) * f (t - x) := by
  rw [tfS]
  rw [ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char ω),
    SchwartzMap.compCLM_apply]
  rw [smul_eq_mul]
  rfl

/-! ### Modulation on `L²`

Translation on `Lp` is free (`Lp.compMeasurePreserving`, since translation is measure-preserving),
but Mathlib has no bounded-multiplication operator on `Lp`, so modulation has to be built.  These
are its two prerequisites: the character preserves `MemLp`, and it preserves the `L²` seminorm
exactly — multiplication by a unimodular function is an ISOMETRY, which is what gives the
operator norm bound `1`. -/

open MeasureTheory

/-- The modulation character as a bare function. -/
noncomputable def chr (ω : ℝ) : ℝ → ℂ :=
  fun t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))

theorem continuous_chr (ω : ℝ) : Continuous (chr ω) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem measurable_chr (ω : ℝ) : Measurable (chr ω) := (continuous_chr ω).measurable

theorem norm_chr (ω t : ℝ) : ‖chr ω t‖ = 1 := norm_char ω t

/-- Multiplying by the character preserves `MemLp`. -/
theorem memLp_chr_mul {ω : ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun t => chr ω t * f t) 2 (volume : Measure ℝ) :=
  MemLp.of_le hf
    (((measurable_chr ω).aestronglyMeasurable).mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => by rw [norm_mul, norm_chr, one_mul])

/-- **Modulation is an isometry**: it preserves the `L²` seminorm on the nose. -/
theorem eLpNorm_chr_mul (ω : ℝ) (f : ℝ → ℂ) :
    eLpNorm (fun t => chr ω t * f t) 2 (volume : Measure ℝ)
      = eLpNorm f 2 (volume : Measure ℝ) :=
  eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun t => by
    rw [norm_mul, norm_chr, one_mul])

/-! ### The modulation operator on `L²`

Built as MULTIPLICATION IN THE `AEEqFun` RING rather than via `MemLp.toLp`.  `Lp` elements are
`AEEqFun`s and `α →ₘ[μ] ℂ` is a ring, so `map_add'` is literally `mul_add` and `map_smul'` is
`mul_smul_comm` — no almost-everywhere reasoning anywhere.  The `MemLp.toLp` route needs a
six-hypothesis `filter_upwards` for each field. -/

/-- The character as an `AEEqFun`. -/
noncomputable def chrAE (ω : ℝ) : ℝ →ₘ[(volume : Measure ℝ)] ℂ :=
  AEEqFun.mk (chr ω) (measurable_chr ω).aestronglyMeasurable

theorem coeFn_chrAE (ω : ℝ) : ⇑(chrAE ω) =ᵐ[(volume : Measure ℝ)] chr ω :=
  AEEqFun.coeFn_mk (chr ω) (measurable_chr ω).aestronglyMeasurable

/-- Multiplying by the character preserves the `L²` seminorm of an `AEEqFun`. -/
theorem eLpNorm_chrAE_mul (ω : ℝ) (f : ℝ →ₘ[(volume : Measure ℝ)] ℂ) :
    eLpNorm (chrAE ω * f) 2 (volume : Measure ℝ) = eLpNorm f 2 (volume : Measure ℝ) := by
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [AEEqFun.coeFn_mul (chrAE ω) f, coeFn_chrAE ω] with t h1 h2
  rw [h1]
  simp only [Pi.mul_apply]
  rw [h2, norm_mul, norm_chr, one_mul]

/-- Left distributivity, by hand: `AEEqFun ℂ` does not have `LeftDistribClass` synthesizable,
so `mul_add` is unavailable and the a.e. argument has to be made explicitly. -/
theorem chrAE_mul_add (ω : ℝ) (a b : ℝ →ₘ[(volume : Measure ℝ)] ℂ) :
    chrAE ω * (a + b) = chrAE ω * a + chrAE ω * b := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul (chrAE ω) (a + b), AEEqFun.coeFn_add a b,
    AEEqFun.coeFn_add (chrAE ω * a) (chrAE ω * b),
    AEEqFun.coeFn_mul (chrAE ω) a, AEEqFun.coeFn_mul (chrAE ω) b] with t h1 h2 h3 h4 h5
  -- split the pointwise sum FIRST: `h4` mentions `↑(chrAE ω * a) t`, which only appears once
  -- `Pi.add_apply` has broken `(↑(chrAE ω * a) + ↑(chrAE ω * b)) t` apart
  rw [h1, h3]
  simp only [Pi.mul_apply, Pi.add_apply, h2, h4, h5]
  ring

/-- Scalar commutation, by hand, for the same reason. -/
theorem chrAE_mul_smul (ω : ℝ) (c : ℂ) (a : ℝ →ₘ[(volume : Measure ℝ)] ℂ) :
    chrAE ω * (c • a) = c • (chrAE ω * a) := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul (chrAE ω) (c • a), AEEqFun.coeFn_smul c a,
    AEEqFun.coeFn_smul c (chrAE ω * a), AEEqFun.coeFn_mul (chrAE ω) a] with t h1 h2 h3 h4
  rw [h1, h3]
  simp only [Pi.mul_apply, Pi.smul_apply, h2, h4, smul_eq_mul]
  ring

/-- **Modulation on `L²`, as a linear map.** -/
noncomputable def modL (ω : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := ⟨chrAE ω * (f : ℝ →ₘ[(volume : Measure ℝ)] ℂ), by
    rw [Lp.mem_Lp_iff_eLpNorm_lt_top, eLpNorm_chrAE_mul]
    exact Lp.eLpNorm_lt_top f⟩
  map_add' f g := by
    refine Subtype.ext ?_
    show chrAE ω * ((f : ℝ →ₘ[(volume : Measure ℝ)] ℂ) + (g : ℝ →ₘ[(volume : Measure ℝ)] ℂ))
        = chrAE ω * (f : ℝ →ₘ[(volume : Measure ℝ)] ℂ)
          + chrAE ω * (g : ℝ →ₘ[(volume : Measure ℝ)] ℂ)
    exact chrAE_mul_add ω _ _
  map_smul' c f := by
    refine Subtype.ext ?_
    show chrAE ω * (c • (f : ℝ →ₘ[(volume : Measure ℝ)] ℂ))
        = c • (chrAE ω * (f : ℝ →ₘ[(volume : Measure ℝ)] ℂ))
    exact chrAE_mul_smul ω c _

theorem norm_modL (ω : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖modL ω f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_chrAE_mul ω _

/-- **Modulation on `L²`, as a continuous linear map** — an isometry, so the bound is `1`. -/
noncomputable def modLC (ω : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (modL ω).mkContinuous 1 (fun f => by rw [one_mul, norm_modL])

/-! ### Translation on `L²`

`Lp.compMeasurePreserving` supplies only an `AddMonoidHom`, so `ℂ`-linearity has to be added.  The
bound is `1` because it is an isometry (`Lp.norm_compMeasurePreserving`).

Note `measurePreserving_sub_right` does not exist, so translation is written `fun t => t + (-x)`. -/

/-- Translation by `x` on `L²`, as a linear map. -/
noncomputable def translLm (x : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := Lp.compMeasurePreserving (fun t : ℝ => t + (-x))
    (measurePreserving_add_right (volume : Measure ℝ) (-x))
  map_add' f g := map_add _ f g
  map_smul' c f := by
    have hmp := measurePreserving_add_right (volume : Measure ℝ) (-x)
    refine Subtype.ext (AEEqFun.ext ?_)
    -- `Lp.coeFn_smul c f` holds at `t`, but after `coeFn_compMeasurePreserving` the goal needs it
    -- at `t + -x`.  An a.e. statement does NOT transfer pointwise through a shift, so push it
    -- forward along the measure-preserving map first.
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f) hmp,
      Lp.coeFn_compMeasurePreserving f hmp,
      hmp.quasiMeasurePreserving.ae (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (Lp.compMeasurePreserving (fun t : ℝ => t + (-x)) hmp f)]
      with t h1 h2 h3 h4
    rw [h1]
    -- `map_smul'` states the scalar as `(RingHom.id ℂ) c`, so `h4` cannot match until that is
    -- unfolded
    simp only [RingHom.id_apply]
    rw [h4]
    -- and again: `h2` mentions `↑↑(compMeasurePreserving …) t`, which only appears once
    -- `Pi.smul_apply` has split `(c • ↑↑(compMeasurePreserving …)) t`
    simp only [Pi.smul_apply, Function.comp_apply, h2]
    simp only [Function.comp_apply, Pi.smul_apply] at h3
    exact h3

theorem norm_translLm (x : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖translLm x f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (measurePreserving_add_right (volume : Measure ℝ) (-x))

/-- Translation by `x` on `L²`, as a continuous linear map — an isometry. -/
noncomputable def translL (x : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (translLm x).mkContinuous 1 (fun f => by rw [one_mul, norm_translLm])

/-- **The time–frequency shift `π(x,ω)` as a continuous linear map on `L²`.** -/
noncomputable def TFL (x ω : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (modLC ω).comp (translL x)

/-! ### How the `L²` operators act pointwise

These are what the Schwartz-agreement step needs. -/

theorem coeFn_translL (x : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(translL x g) =ᵐ[(volume : Measure ℝ)] fun t : ℝ => g (t + (-x)) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right (volume : Measure ℝ) (-x))

theorem coeFn_modLC (ω : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(modLC ω g) =ᵐ[(volume : Measure ℝ)] fun t : ℝ => chr ω t * g t := by
  filter_upwards [AEEqFun.coeFn_mul (chrAE ω) (g : ℝ →ₘ[(volume : Measure ℝ)] ℂ),
    coeFn_chrAE ω] with t h1 h2
  show ((chrAE ω * (g : ℝ →ₘ[(volume : Measure ℝ)] ℂ) : ℝ →ₘ[(volume : Measure ℝ)] ℂ)) t
      = chr ω t * g t
  rw [h1]
  simp only [Pi.mul_apply]
  rw [h2]

theorem coeFn_TFL (x ω : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(TFL x ω g) =ᵐ[(volume : Measure ℝ)] fun t : ℝ => chr ω t * g (t + (-x)) := by
  filter_upwards [coeFn_modLC ω (translL x g), coeFn_translL x g] with t h1 h2
  show ⇑(modLC ω (translL x g)) t = _
  rw [h1, h2]

/-! ### The `L²` and Schwartz shifts agree

This is what lets the covariance be proved on Schwartz functions and transported to `L²` by
density. -/

/-- **`TFL` agrees with `tfS` on Schwartz functions.** -/
theorem TFL_toLp (x ω : ℝ) (f : 𝓢(ℝ, ℂ)) :
    TFL x ω (f.toLp 2 (volume : Measure ℝ)) = (tfS x ω f).toLp 2 (volume : Measure ℝ) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-x)
  refine Subtype.ext (AEEqFun.ext ?_)
  -- the third hypothesis MUST be pushed forward: `coeFn_TFL` puts `f.toLp` at `t + -x`, not `t`
  filter_upwards [coeFn_TFL x ω (f.toLp 2 (volume : Measure ℝ)),
    SchwartzMap.coeFn_toLp (tfS x ω f) 2 (volume : Measure ℝ),
    hmp.quasiMeasurePreserving.ae (SchwartzMap.coeFn_toLp f 2 (volume : Measure ℝ))]
    with t h1 h2 h3
  rw [h1, h2, h3, tfS_apply]
  simp only [chr, sub_eq_add_neg]

end HRTChar

/-! ## Acceptance gate -/


#print axioms HRTChar.contDiff_ofReal
#print axioms HRTChar.iteratedDeriv_cexp_linear
#print axioms HRTChar.norm_char
#print axioms HRTChar.hasTemperateGrowth_char
#print axioms HRTChar.hasTemperateGrowth_sub
#print axioms HRTChar.sub_upper
#print axioms HRTChar.tfS_apply
#print axioms HRTChar.memLp_chr_mul
#print axioms HRTChar.eLpNorm_chr_mul
#print axioms HRTChar.eLpNorm_chrAE_mul
#print axioms HRTChar.norm_modL
#print axioms HRTChar.modLC
#print axioms HRTChar.norm_translLm
#print axioms HRTChar.TFL
#print axioms HRTChar.coeFn_translL
#print axioms HRTChar.coeFn_modLC
#print axioms HRTChar.coeFn_TFL
#print axioms HRTChar.TFL_toLp
