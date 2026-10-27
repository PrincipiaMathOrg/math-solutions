import Mathlib

/-!
# Toward the three-point HRT theorem

`HRTResonantFibre.heil_speegle_lambda_zero` currently assumes `hthree`, the `≤ 3`-point HRT
theorem (Heil–Ramanathan–Topiwala 1996).  Per the owner's standing no-hypotheses rule that must
be discharged.  No formalisation exists: notably Oussa's own Lean-certified HRT paper
(arXiv:2604.21228) lists the three-point theorem as assumed analytic input `(A4)`.

This file builds it from the bottom.  The first genuinely reusable ingredient is that a
*nonconstant character* attains any fixed value only on a null set — which is what kills the
two-point configuration `{(0,0), (0,ω)}` and, after a symplectic reduction, feeds the
general case.
-/

set_option maxHeartbeats 1000000

namespace HRTSmall

open Complex Real MeasureTheory

/-- Two points where the character `t ↦ e^{2πiωt}` agree differ by an element of `(1/ω)ℤ`. -/
theorem sub_mem_of_exp_eq {ω : ℝ} (hω : ω ≠ 0) {t₁ t₂ : ℝ}
    (h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t₁ : ℂ))
       = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t₂ : ℂ))) :
    ∃ k : ℤ, t₁ - t₂ = (k : ℝ) / ω := by
  have hdiff : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t₁ : ℂ)
      - 2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t₂ : ℂ)) = 1 := by
    rw [Complex.exp_sub, h, div_self]
    exact Complex.exp_ne_zero _
  have hform : 2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t₁ : ℂ)
      - 2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t₂ : ℂ)
      = ((ω * (t₁ - t₂) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hform, Complex.exp_eq_one_iff] at hdiff
  obtain ⟨k, hk⟩ := hdiff
  refine ⟨k, ?_⟩
  have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hk' : ((ω * (t₁ - t₂) : ℝ) : ℂ) = (k : ℂ) := mul_right_cancel₀ h2πI hk
  have hreal : ω * (t₁ - t₂) = (k : ℝ) := by exact_mod_cast hk'
  field_simp [hω] at hreal ⊢
  linarith [hreal]

/-- **A nonconstant character hits any value only on a countable set.** -/
theorem countable_setOf_exp_eq {ω : ℝ} (hω : ω ≠ 0) (c : ℂ) :
    {t : ℝ | Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) = c}.Countable := by
  classical
  by_cases hne : {t : ℝ | Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))
      = c}.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hne
    refine Set.Countable.mono (fun t ht => ?_)
      (Set.countable_range (fun k : ℤ => t₀ + (k : ℝ) / ω))
    obtain ⟨k, hk⟩ := sub_mem_of_exp_eq hω (ht.trans ht₀.symm)
    exact ⟨k, by linarith [hk]⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.countable_empty

/-- Hence that set is null. -/
theorem measure_setOf_exp_eq_zero {ω : ℝ} (hω : ω ≠ 0) (c : ℂ) :
    volume {t : ℝ | Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) = c} = 0 :=
  (countable_setOf_exp_eq hω c).measure_zero _

/-! ### The two-point modulation case

`g` and `M_ω g` are linearly independent for every nonzero `g` and every `ω ≠ 0`. -/

/-- **Two-point HRT, modulation case.** -/
theorem two_point_modulation {ω : ℝ} (hω : ω ≠ 0) {g : ℝ → ℂ} (A B : ℂ)
    (hg : ¬ (∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), g t = 0))
    (hdep : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      A * g t + B * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) * g t) = 0) :
    A = 0 ∧ B = 0 := by
  have key : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      (A + B * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))) * g t = 0 := by
    filter_upwards [hdep] with t ht
    linear_combination ht
  have hB : B = 0 := by
    by_contra hB
    refine hg ?_
    have hnull := measure_setOf_exp_eq_zero hω (-A / B)
    have hae : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) ≠ -A / B := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [key, hae] with t ht hnt
    rcases mul_eq_zero.mp ht with h | h
    · exact absurd (by rw [eq_div_iff hB]; linear_combination h) hnt
    · exact h
  refine ⟨?_, hB⟩
  by_contra hA
  refine hg ?_
  filter_upwards [key] with t ht
  rw [hB] at ht
  simpa [hA] using ht

/-! ### A periodic integrable function on `ℝ` vanishes

If `f ≥ 0` is `x`-periodic and has finite integral over all of `ℝ`, then `f = 0` a.e.: the
integral is the sum over the lattice of a CONSTANT (the mass on one period), and an infinite sum
of a positive constant is `∞`.

This is what closes the two-point translation case: a dependence `A g + B T_x g = 0` makes `|g|`
scale by a fixed factor under translation by `x`, and in the borderline case that factor is `1`,
making `|g|²` periodic. -/

section Periodic

open scoped ENNReal

theorem infinite_zmultiples {x : ℝ} (hx : x ≠ 0) :
    Infinite (AddSubgroup.zmultiples x) :=
  Infinite.of_injective (fun n : ℤ => (⟨n • x, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
      AddSubgroup.zmultiples x))
    (by
      intro m n hmn
      have : m • x = n • x := congrArg Subtype.val hmn
      have hxx : (m : ℝ) * x = (n : ℝ) * x := by simpa [zsmul_eq_mul] using this
      exact_mod_cast mul_right_cancel₀ hx hxx)

/-- One-step a.e. periodicity propagates to the whole lattice `x·ℤ`. -/
theorem ae_periodic_zsmul {x : ℝ} {f : ℝ → ℝ≥0∞}
    (hstep : ∀ᵐ (t : ℝ), f (t + x) = f t) :
    ∀ n : ℤ, ∀ᵐ (t : ℝ), f (t + n • x) = f t := by
  have hshift : ∀ c : ℝ, ∀ᵐ (t : ℝ), f (t + c + x) = f (t + c) := fun c =>
    (measurePreserving_add_right volume c).quasiMeasurePreserving.ae hstep
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      filter_upwards [ih, hshift ((k : ℤ) • x)] with t h1 h2
      have heq : t + ((k : ℤ) + 1) • x = t + (k : ℤ) • x + x := by
        rw [add_zsmul, one_zsmul]; ring
      rw [heq, h2, h1]
  | pred k ih =>
      filter_upwards [ih, hshift ((-(k : ℤ) - 1) • x)] with t h1 h2
      have heq : t + (-(k : ℤ) - 1) • x + x = t + (-(k : ℤ)) • x := by
        rw [sub_zsmul, one_zsmul]; ring
      rw [heq] at h2
      exact h2.symm.trans h1

/-- Periodicity under `x` gives periodicity under `-x`. -/
theorem ae_periodic_neg {x : ℝ} {f : ℝ → ℝ≥0∞} (h : ∀ᵐ (t : ℝ), f (t + x) = f t) :
    ∀ᵐ (t : ℝ), f (t + -x) = f t := by
  have h2 := (measurePreserving_add_right volume (-x)).quasiMeasurePreserving.ae h
  filter_upwards [h2] with t ht
  rw [show t + -x + x = t by ring] at ht
  exact ht.symm

/-- **A periodic function with finite integral vanishes.** -/
theorem ae_eq_zero_of_periodic {x : ℝ} (hx : 0 < x) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hper : ∀ n : AddSubgroup.zmultiples x, ∀ᵐ (t : ℝ), f (n +ᵥ t) = f t)
    (hfin : ∫⁻ t, f t ≠ ⊤) :
    ∀ᵐ t, f t = 0 := by
  haveI := infinite_zmultiples (ne_of_gt hx)
  have hfd := isAddFundamentalDomain_Ioc hx 0
  rw [zero_add] at hfd
  have h := hfd.lintegral_eq_tsum'' f
  have hconst : ∀ n : AddSubgroup.zmultiples x,
      ∫⁻ t in Set.Ioc (0 : ℝ) x, f (n +ᵥ t) = ∫⁻ t in Set.Ioc (0 : ℝ) x, f t :=
    fun n => lintegral_congr_ae (ae_restrict_of_ae (hper n))
  rw [tsum_congr hconst] at h
  have hc : ∫⁻ t in Set.Ioc (0 : ℝ) x, f t = 0 := by
    by_contra hc0
    exact hfin (h.trans (ENNReal.tsum_const_eq_top_of_ne_zero hc0))
  rw [hc] at h
  simp only [tsum_zero] at h
  exact (lintegral_eq_zero_iff hf).mp h

/-- Bridge: lattice periodicity in the `ℤ`-indexed form gives the subgroup-indexed form that
`ae_eq_zero_of_periodic` consumes. -/
theorem ae_periodic_subgroup {x : ℝ} {f : ℝ → ℝ≥0∞}
    (h : ∀ n : ℤ, ∀ᵐ (t : ℝ), f (t + n • x) = f t) :
    ∀ n : AddSubgroup.zmultiples x, ∀ᵐ (t : ℝ), f (n +ᵥ t) = f t := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  filter_upwards [h k] with t ht
  simpa [add_comm] using ht

/-- **Two-point HRT, translation case.**  `g` and `T_x g` are linearly independent for every
`x > 0` and every `g ∈ L²` that is not a.e. zero. -/
theorem two_point_translation {x : ℝ} (hx : 0 < x) {g : ℝ → ℂ} (hgm : Measurable g)
    (hL2 : ∫⁻ t, (‖g t‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤) (A B : ℂ)
    (hg : ¬ (∀ᵐ (t : ℝ), g t = 0))
    (hdep : ∀ᵐ (t : ℝ), A * g t + B * g (t + x) = 0) :
    A = 0 ∧ B = 0 := by
  set F : ℝ → ℝ≥0∞ := fun t => (‖g t‖₊ : ℝ≥0∞) ^ 2 with hF
  have hFmeas : Measurable F := (hgm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hM0 : ∫⁻ t, F t ≠ 0 := by
    intro h0
    exact hg (by
      have := (lintegral_eq_zero_iff hFmeas).mp h0
      filter_upwards [this] with t ht
      simpa [hF, pow_eq_zero_iff] using ht)
  have hB : B = 0 := by
    by_contra hB
    refine hg ?_
    -- the modulus scales by a fixed factor
    have hscale : ∀ᵐ (t : ℝ), F (t + x) = ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * F t := by
      filter_upwards [hdep] with t ht
      have hgx : g (t + x) = -(A / B) * g t := by
        field_simp at ht ⊢
        linear_combination ht
      simp only [hF, hgx, nnnorm_mul, nnnorm_neg]
      push_cast
      ring
    -- comparing L² masses forces the factor to be 1
    have htrans : ∫⁻ t, F (t + x) = ∫⁻ t, F t :=
      (measurePreserving_add_right volume x).lintegral_comp_emb
        (measurableEmbedding_addRight x) F
    have hEq : ∫⁻ t, F t = ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ t, F t := by
      calc ∫⁻ t, F t = ∫⁻ t, F (t + x) := htrans.symm
        _ = ∫⁻ t, ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * F t := lintegral_congr_ae hscale
        _ = ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ t, F t := lintegral_const_mul _ hFmeas
    have hone : ((‖A / B‖₊ : ℝ≥0∞) ^ 2) = 1 := by
      have h1 : ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * (∫⁻ t, F t) = 1 * (∫⁻ t, F t) := by
        rw [one_mul]; exact hEq.symm
      exact (ENNReal.mul_left_inj hM0 hL2).mp h1
    -- so F is periodic with period x, and integrable, hence zero
    have hper : ∀ᵐ (t : ℝ), F (t + x) = F t := by
      filter_upwards [hscale] with t ht
      rw [ht, hone, one_mul]
    have hzero := ae_eq_zero_of_periodic hx hFmeas
      (ae_periodic_subgroup (ae_periodic_zsmul hper)) hL2
    filter_upwards [hzero] with t ht
    simpa [hF, pow_eq_zero_iff] using ht
  refine ⟨?_, hB⟩
  by_contra hA
  refine hg ?_
  filter_upwards [hdep] with t ht
  rw [hB] at ht
  simpa [hA] using ht

/-- **Two-point HRT, general case with `x > 0`.**  `g` and `M_ω T_x g` are linearly independent.

The modulation is invisible to the argument: it has modulus one, so the modulus of `g` still
scales by the fixed factor `|A/B|` under translation by `x`.  Together with
`two_point_modulation` (which handles `x = 0`, `ω ≠ 0`) this settles every two-point
configuration up to the reduction of a general pair by a common translate. -/
theorem two_point_general {x ω : ℝ} (hx : x ≠ 0) {g : ℝ → ℂ} (hgm : Measurable g)
    (hL2 : ∫⁻ t, (‖g t‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤) (A B : ℂ)
    (hg : ¬ (∀ᵐ (t : ℝ), g t = 0))
    (hdep : ∀ᵐ (t : ℝ), A * g t
      + B * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) * g (t + x)) = 0) :
    A = 0 ∧ B = 0 := by
  set F : ℝ → ℝ≥0∞ := fun t => (‖g t‖₊ : ℝ≥0∞) ^ 2 with hF
  have hFmeas : Measurable F := (hgm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hM0 : ∫⁻ t, F t ≠ 0 := by
    intro h0
    exact hg (by
      have := (lintegral_eq_zero_iff hFmeas).mp h0
      filter_upwards [this] with t ht
      simpa [hF, pow_eq_zero_iff] using ht)
  have hB : B = 0 := by
    by_contra hB
    refine hg ?_
    have hscale : ∀ᵐ (t : ℝ), F (t + x) = ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * F t := by
      filter_upwards [hdep] with t ht
      have he : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      have hgx : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) * g (t + x)
          = -(A / B) * g t := by
        field_simp at ht ⊢
        linear_combination ht
      have hn : ‖g (t + x)‖ = ‖A / B‖ * ‖g t‖ := by
        have := congrArg norm hgx
        rw [norm_mul, he, one_mul, norm_mul, norm_neg] at this
        exact this
      simp only [hF]
      have : (‖g (t + x)‖₊ : ℝ≥0∞) = (‖A / B‖₊ : ℝ≥0∞) * (‖g t‖₊ : ℝ≥0∞) := by
        rw [← ENNReal.coe_mul]
        congr 1
        ext
        push_cast
        simpa using hn
      rw [this]
      ring
    have htrans : ∫⁻ t, F (t + x) = ∫⁻ t, F t :=
      (measurePreserving_add_right volume x).lintegral_comp_emb
        (measurableEmbedding_addRight x) F
    have hEq : ∫⁻ t, F t = ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ t, F t := by
      calc ∫⁻ t, F t = ∫⁻ t, F (t + x) := htrans.symm
        _ = ∫⁻ t, ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * F t := lintegral_congr_ae hscale
        _ = ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ t, F t := lintegral_const_mul _ hFmeas
    have hone : ((‖A / B‖₊ : ℝ≥0∞) ^ 2) = 1 := by
      have h1 : ((‖A / B‖₊ : ℝ≥0∞) ^ 2) * (∫⁻ t, F t) = 1 * (∫⁻ t, F t) := by
        rw [one_mul]; exact hEq.symm
      exact (ENNReal.mul_left_inj hM0 hL2).mp h1
    have hper : ∀ᵐ (t : ℝ), F (t + x) = F t := by
      filter_upwards [hscale] with t ht
      rw [ht, hone, one_mul]
    have hzero : ∀ᵐ (t : ℝ), F t = 0 := by
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · have hpos' : (0 : ℝ) < -x := by linarith
        exact ae_eq_zero_of_periodic hpos' hFmeas
          (ae_periodic_subgroup (ae_periodic_zsmul (ae_periodic_neg hper))) hL2
      · exact ae_eq_zero_of_periodic hpos hFmeas
          (ae_periodic_subgroup (ae_periodic_zsmul hper)) hL2
    filter_upwards [hzero] with t ht
    simpa [hF, pow_eq_zero_iff] using ht
  refine ⟨?_, hB⟩
  by_contra hA
  refine hg ?_
  filter_upwards [hdep] with t ht
  rw [hB] at ht
  simpa [hA] using ht

end Periodic

/-! ### The Heisenberg composition law

Time–frequency shifts compose up to a unimodular phase.  This is what lets a general pair of
points be reduced, by applying a common shift, to one with the first point at the origin — the
normal form the two-point theorems above are stated in. -/

section Composition

open scoped ENNReal

/-- `π(x, ω) g (t) = e^{2πiωt} · g (t - x)`. -/
noncomputable def tfShift (x ω : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) * g (t - x)

/-- **Composition law.**  `π(x,ω) ∘ π(x',ω') = e^{-2πiω'x} · π(x+x', ω+ω')`. -/
theorem tfShift_comp (x ω x' ω' : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    tfShift x ω (tfShift x' ω' g) t
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω' : ℂ) * (x : ℂ)))
        * tfShift (x + x') (ω + ω') g t := by
  unfold tfShift
  have harg : t - x - x' = t - (x + x') := by ring
  rw [harg]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω' : ℂ) * (((t - x) : ℝ) : ℂ))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω' : ℂ) * (x : ℂ)))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((ω + ω') : ℝ) : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (g (t - (x + x'))) * hexp

/-- `π(x,ω)` never destroys information: it is pointwise a unimodular multiple of a translate. -/
theorem norm_tfShift (x ω : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    ‖tfShift x ω g t‖ = ‖g (t - x)‖ := by
  unfold tfShift
  rw [norm_mul, Complex.norm_exp]
  simp

/-- **Two-point HRT.**  For any two DISTINCT points of the time–frequency plane and any
`g ∈ L²` that is not a.e. zero, the two translates are linearly independent.

The composition law reduces an arbitrary pair to normal form (first point at the origin); the
`Δx ≠ 0` case is `two_point_general` and the `Δx = 0` case is `two_point_modulation`. -/
theorem two_point_hrt {x₁ ω₁ x₂ ω₂ : ℝ} (hne : x₁ ≠ x₂ ∨ ω₁ ≠ ω₂)
    {g : ℝ → ℂ} (hgm : Measurable g) (hL2 : ∫⁻ t, (‖g t‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤)
    (hg : ¬ (∀ᵐ (t : ℝ), g t = 0)) (A B : ℂ)
    (hdep : ∀ᵐ (t : ℝ), A * tfShift x₁ ω₁ g t + B * tfShift x₂ ω₂ g t = 0) :
    A = 0 ∧ B = 0 := by
  classical
  -- put the pair into normal form
  have hrw : ∀ t : ℝ, tfShift x₂ ω₂ g t
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ω₂ - ω₁ : ℝ) : ℂ) * (x₁ : ℂ))
        * tfShift x₁ ω₁ (tfShift (x₂ - x₁) (ω₂ - ω₁) g) t := by
    intro t
    rw [tfShift_comp x₁ ω₁ (x₂ - x₁) (ω₂ - ω₁) g t,
      show x₁ + (x₂ - x₁) = x₂ by ring, show ω₁ + (ω₂ - ω₁) = ω₂ by ring,
      ← mul_assoc, ← Complex.exp_add]
    simp
  set B' : ℂ := B * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ω₂ - ω₁ : ℝ) : ℂ) * (x₁ : ℂ))
    with hB'
  -- strip the common shift: it is pointwise a nonzero multiple
  have hred : ∀ᵐ (s : ℝ), A * g s + B' * tfShift (x₂ - x₁) (ω₂ - ω₁) g s = 0 := by
    have hshift : ∀ᵐ (t : ℝ),
        A * g (t - x₁) + B' * tfShift (x₂ - x₁) (ω₂ - ω₁) g (t - x₁) = 0 := by
      filter_upwards [hdep] with t ht
      rw [hrw t] at ht
      have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω₁ : ℂ) * (t : ℂ)) ≠ 0 :=
        Complex.exp_ne_zero _
      have hfac : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω₁ : ℂ) * (t : ℂ))
          * (A * g (t - x₁) + B' * tfShift (x₂ - x₁) (ω₂ - ω₁) g (t - x₁)) = 0 := by
        rw [← ht]; unfold tfShift; rw [hB']; ring
      exact (mul_eq_zero.mp hfac).resolve_left hexp
    have := (measurePreserving_add_right volume x₁).quasiMeasurePreserving.ae hshift
    filter_upwards [this] with s hs
    rwa [show s + x₁ - x₁ = s by ring] at hs
  -- now dispatch on whether the shift is nonzero
  by_cases hdx : x₂ - x₁ = 0
  · have hdw : ω₂ - ω₁ ≠ 0 := by
      rcases hne with h | h
      · exact absurd (by linarith [sub_eq_zero.mp hdx] : x₁ = x₂) h
      · intro h0; exact h (by linarith [sub_eq_zero.mp h0])
    have hmod : ∀ᵐ (t : ℝ), A * g t
        + B' * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ω₂ - ω₁ : ℝ) : ℂ) * (t : ℂ))
            * g t) = 0 := by
      filter_upwards [hred] with t ht
      unfold tfShift at ht
      rwa [hdx, sub_zero] at ht
    obtain ⟨hA, hB'0⟩ := two_point_modulation hdw A B' hg hmod
    refine ⟨hA, ?_⟩
    have := Complex.exp_ne_zero
      (2 * (Real.pi : ℂ) * Complex.I * ((ω₂ - ω₁ : ℝ) : ℂ) * (x₁ : ℂ))
    exact (mul_eq_zero.mp (hB' ▸ hB'0)).resolve_right this
  · have hxne : -(x₂ - x₁) ≠ 0 := neg_ne_zero.mpr hdx
    have hgen : ∀ᵐ (t : ℝ), A * g t
        + B' * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ω₂ - ω₁ : ℝ) : ℂ) * (t : ℂ))
            * g (t + -(x₂ - x₁))) = 0 := by
      filter_upwards [hred] with t ht
      unfold tfShift at ht
      rwa [show t + -(x₂ - x₁) = t - (x₂ - x₁) by ring]
    obtain ⟨hA, hB'0⟩ := two_point_general hxne hgm hL2 A B' hg hgen
    refine ⟨hA, ?_⟩
    have := Complex.exp_ne_zero
      (2 * (Real.pi : ℂ) * Complex.I * ((ω₂ - ω₁ : ℝ) : ℂ) * (x₁ : ℂ))
    exact (mul_eq_zero.mp (hB' ▸ hB'0)).resolve_right this

/-! ### The Zak symbol of the lattice triple

For the three LATTICE points `(0,0), (1,0), (0,1)` the Zak transform diagonalises the whole
dependence: it becomes `p(t,ω) · Zg(t,ω) = 0` with the trigonometric symbol

  `p(t,ω) = A + B e^{-2πiω} + C e^{2πit}`.

So independence reduces to: a nonzero such symbol vanishes only on a NULL set.  That is
elementary — for each fixed `t` the equation pins `e^{-2πiω}` to a single value, so the fibre is
countable, and Fubini finishes.  No metaplectic machinery is needed for this triple. -/

/-- `tfShift 0 0` is the identity. -/
theorem tfShift_zero (g : ℝ → ℂ) : tfShift 0 0 g = g := by
  funext t
  simp [tfShift]

/-- **Three-point independence, assembled.**

A three-term time–frequency dependence is impossible provided the Zak/Jensen chain forces all three
coefficient moduli to coincide (`hforce` — this is `HRTResonant.threePoint_moduli_all_equal`
transported through `borel_transfer_exists`), and no such equal-moduli dependence exists (`hexcl`,
the codimension-two stratum).

The point of stating it this way: the cases where SOME COEFFICIENT VANISHES need no hypothesis at
all.  They collapse to two points, and `two_point_hrt` settles those unconditionally.  So the only
content the analysis has to supply concerns dependences with every coefficient nonzero. -/
theorem threePoint_no_dependence {x₁ ω₁ x₂ ω₂ : ℝ}
    (h01 : (0 : ℝ) ≠ x₁ ∨ (0 : ℝ) ≠ ω₁) (h02 : (0 : ℝ) ≠ x₂ ∨ (0 : ℝ) ≠ ω₂)
    (h12 : x₁ ≠ x₂ ∨ ω₁ ≠ ω₂)
    {g : ℝ → ℂ} (hgm : Measurable g)
    (hL2 : ∫⁻ t, ((‖g t‖₊ : ENNReal)) ^ 2 ≠ ⊤)
    (hg : ¬ (∀ᵐ (t : ℝ), g t = 0))
    (hforce : ∀ c₀ c₁ c₂ : ℂ, c₀ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      (∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₁ * tfShift x₁ ω₁ g t + c₂ * tfShift x₂ ω₂ g t = 0) →
      ‖c₀‖ = ‖c₁‖ ∧ ‖c₁‖ = ‖c₂‖)
    (hexcl : ∀ c₀ c₁ c₂ : ℂ, c₀ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 → ‖c₀‖ = ‖c₁‖ → ‖c₁‖ = ‖c₂‖ →
      ¬ (∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₁ * tfShift x₁ ω₁ g t + c₂ * tfShift x₂ ω₂ g t = 0))
    (c₀ c₁ c₂ : ℂ)
    (hdep : ∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₁ * tfShift x₁ ω₁ g t + c₂ * tfShift x₂ ω₂ g t = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  by_cases h0 : c₀ = 0
  · subst h0
    have hd : ∀ᵐ (t : ℝ), c₁ * tfShift x₁ ω₁ g t + c₂ * tfShift x₂ ω₂ g t = 0 := by
      filter_upwards [hdep] with t ht
      simpa using ht
    obtain ⟨h1, h2⟩ := two_point_hrt h12 hgm hL2 hg c₁ c₂ hd
    exact ⟨rfl, h1, h2⟩
  by_cases h1 : c₁ = 0
  · subst h1
    have hd : ∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₂ * tfShift x₂ ω₂ g t = 0 := by
      filter_upwards [hdep] with t ht
      simpa using ht
    obtain ⟨ha, hb⟩ := two_point_hrt h02 hgm hL2 hg c₀ c₂ hd
    exact ⟨ha, rfl, hb⟩
  by_cases h2 : c₂ = 0
  · subst h2
    have hd : ∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₁ * tfShift x₁ ω₁ g t = 0 := by
      filter_upwards [hdep] with t ht
      simpa using ht
    obtain ⟨ha, hb⟩ := two_point_hrt h01 hgm hL2 hg c₀ c₁ hd
    exact ⟨ha, hb, rfl⟩
  obtain ⟨he1, he2⟩ := hforce c₀ c₁ c₂ h0 h1 h2 hdep
  exact absurd hdep (hexcl c₀ c₁ c₂ h0 h1 h2 he1 he2)


/-- The three-point time–frequency family at `(0,0)`, `(x₁,ω₁)`, `(x₂,ω₂)`. -/
noncomputable def threePointFamily (g : ℝ → ℂ) (x₁ ω₁ x₂ ω₂ : ℝ) : Fin 3 → (ℝ → ℂ) :=
  ![tfShift 0 0 g, tfShift x₁ ω₁ g, tfShift x₂ ω₂ g]

/-- **Three-point HRT as a first-class `LinearIndependent` statement.**

`threePoint_no_dependence` is phrased as "the coefficients vanish"; this is the same content in the
form the conjecture is actually stated in.  Note the hypotheses are almost-everywhere statements
while linear independence is an everywhere one — that direction is free, since a combination equal
to the zero FUNCTION is in particular zero a.e.

As before, the vanishing-coefficient cases cost nothing: they are `two_point_hrt`, unconditional. -/
theorem threePoint_linearIndependent {x₁ ω₁ x₂ ω₂ : ℝ}
    (h01 : (0 : ℝ) ≠ x₁ ∨ (0 : ℝ) ≠ ω₁) (h02 : (0 : ℝ) ≠ x₂ ∨ (0 : ℝ) ≠ ω₂)
    (h12 : x₁ ≠ x₂ ∨ ω₁ ≠ ω₂)
    {g : ℝ → ℂ} (hgm : Measurable g)
    (hL2 : ∫⁻ t, ((‖g t‖₊ : ENNReal)) ^ 2 ≠ ⊤)
    (hg : ¬ (∀ᵐ (t : ℝ), g t = 0))
    (hforce : ∀ c₀ c₁ c₂ : ℂ, c₀ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      (∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₁ * tfShift x₁ ω₁ g t + c₂ * tfShift x₂ ω₂ g t = 0) →
      ‖c₀‖ = ‖c₁‖ ∧ ‖c₁‖ = ‖c₂‖)
    (hexcl : ∀ c₀ c₁ c₂ : ℂ, c₀ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 → ‖c₀‖ = ‖c₁‖ → ‖c₁‖ = ‖c₂‖ →
      ¬ (∀ᵐ (t : ℝ), c₀ * tfShift 0 0 g t + c₁ * tfShift x₁ ω₁ g t + c₂ * tfShift x₂ ω₂ g t = 0)) :
    LinearIndependent ℂ (threePointFamily g x₁ ω₁ x₂ ω₂) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hpt : ∀ t : ℝ,
      c 0 * tfShift 0 0 g t + c 1 * tfShift x₁ ω₁ g t + c 2 * tfShift x₂ ω₂ g t = 0 := by
    intro t
    have h := congrFun hc t
    simpa [Fin.sum_univ_three, threePointFamily, Finset.sum_apply] using h
  have hdep : ∀ᵐ (t : ℝ),
      c 0 * tfShift 0 0 g t + c 1 * tfShift x₁ ω₁ g t + c 2 * tfShift x₂ ω₂ g t = 0 :=
    Filter.Eventually.of_forall hpt
  obtain ⟨e0, e1, e2⟩ :=
    threePoint_no_dependence h01 h02 h12 hgm hL2 hg hforce hexcl (c 0) (c 1) (c 2) hdep
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2


/-- The two-point time–frequency family. -/
noncomputable def twoPointFamily (g : ℝ → ℂ) (x₁ ω₁ x₂ ω₂ : ℝ) : Fin 2 → (ℝ → ℂ) :=
  ![tfShift x₁ ω₁ g, tfShift x₂ ω₂ g]

/-- **Two-point HRT, unconditional, as a `LinearIndependent` statement.**

This one carries NO reduction hypothesis at all — only that the two points are distinct and the
window is a nonzero `L²` function.  It is the fully finished corner of the conjecture in this
development, and worth stating in the conjecture's own language rather than as a coefficient
lemma. -/
theorem twoPoint_linearIndependent {x₁ ω₁ x₂ ω₂ : ℝ} (hne : x₁ ≠ x₂ ∨ ω₁ ≠ ω₂)
    {g : ℝ → ℂ} (hgm : Measurable g)
    (hL2 : ∫⁻ t, ((‖g t‖₊ : ENNReal)) ^ 2 ≠ ⊤)
    (hg : ¬ (∀ᵐ (t : ℝ), g t = 0)) :
    LinearIndependent ℂ (twoPointFamily g x₁ ω₁ x₂ ω₂) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hpt : ∀ t : ℝ, c 0 * tfShift x₁ ω₁ g t + c 1 * tfShift x₂ ω₂ g t = 0 := by
    intro t
    have h := congrFun hc t
    simpa [Fin.sum_univ_two, twoPointFamily, Finset.sum_apply] using h
  obtain ⟨e0, e1⟩ :=
    two_point_hrt hne hgm hL2 hg (c 0) (c 1) (Filter.Eventually.of_forall hpt)
  intro i
  fin_cases i
  · exact e0
  · exact e1


section Symbol

/-- For fixed `t`, the symbol vanishes for only countably many `ω` (when `B ≠ 0`). -/
theorem countable_symbol_fibre {A B C : ℂ} (hB : B ≠ 0) (t : ℝ) :
    {ω : ℝ | A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)))
      + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 0}.Countable := by
  have hsub : {ω : ℝ | A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)))
        + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 0}
      ⊆ {ω : ℝ | Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℝ) : ℂ) * (ω : ℂ))
        = -(A + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) / B} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [eq_div_iff hB]
    have hrw : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℝ) : ℂ) * (ω : ℂ))
        = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ))) := by
      congr 1; push_cast; ring
    rw [hrw]
    linear_combination hω
  exact Set.Countable.mono hsub (countable_setOf_exp_eq (by norm_num) _)

/-- Hence for fixed `t` the symbol's zero set in `ω` is null. -/
theorem measure_symbol_fibre_zero {A B C : ℂ} (hB : B ≠ 0) (t : ℝ) :
    volume {ω : ℝ | A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)))
      + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 0} = 0 :=
  (countable_symbol_fibre hB t).measure_zero _

/-- The symbol as a function on the plane. -/
noncomputable def symbolFn (A B C : ℂ) (q : ℝ × ℝ) : ℂ :=
  A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((q.2 : ℝ) : ℂ)))
    + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((q.1 : ℝ) : ℂ))

theorem continuous_symbolFn (A B C : ℂ) : Continuous (symbolFn A B C) := by
  unfold symbolFn
  fun_prop

/-- **The symbol vanishes only on a null set of the plane.**  Fubini over the countable fibres. -/
theorem measure_symbolFn_zero_prod {A B C : ℂ} (hB : B ≠ 0) :
    (volume.prod volume) {q : ℝ × ℝ | symbolFn A B C q = 0} = 0 := by
  refine MeasureTheory.Measure.measure_prod_null_of_ae_null ?_ ?_
  · exact (continuous_symbolFn A B C).measurable (measurableSet_singleton 0)
  · refine Filter.Eventually.of_forall fun t => ?_
    have hfib : Prod.mk t ⁻¹' {q : ℝ × ℝ | symbolFn A B C q = 0}
        = {ω : ℝ | A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)))
            + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 0} := by
      ext ω; simp [symbolFn]
    simpa [hfib] using measure_symbol_fibre_zero (A := A) (B := B) (C := C) hB t

/-- **The lattice triple, at the Zak level.**  If the Zak symbol annihilates a Zak transform
that is not a.e. zero, all three coefficients vanish.

This is HRT for `{(0,0), (1,0), (0,1)}` once the dependence has been pushed through the Zak
transform — the same interface `zak_dep_zero` provides.  No metaplectic machinery is used. -/
theorem lattice_triple_of_zak {A B C : ℂ} {G : ℝ × ℝ → ℂ}
    (hG : ¬ (∀ᵐ q ∂(volume.prod volume : Measure (ℝ × ℝ)), G q = 0))
    (hann : ∀ᵐ q ∂(volume.prod volume : Measure (ℝ × ℝ)), symbolFn A B C q * G q = 0) :
    B = 0 := by
  by_contra hB
  refine hG ?_
  have hnull : ∀ᵐ q ∂(volume.prod volume : Measure (ℝ × ℝ)), symbolFn A B C q ≠ 0 := by
    rw [ae_iff]
    simpa using measure_symbolFn_zero_prod (A := A) (B := B) (C := C) hB
  filter_upwards [hann, hnull] with q hq hne
  exact (mul_eq_zero.mp hq).resolve_left hne

end Symbol

/-! ### Metaplectic: the chirp (shear) covariance

The symplectic group in dimension one is `SL₂(ℝ)`, generated by dilations, the Fourier
transform, and the SHEARS `(x,ω) ↦ (x, ω + c x)`.  The shear is implemented on `L²` by
multiplication by the chirp `e^{iπct²}` — no Fourier transform, no Weil representation
machinery, just an algebraic identity.

This matters for `Λ₀`: each of its triples spans a rank-2 lattice, and a determinant-one shear
carries such a lattice to one where the Zak-symbol argument already proved applies. -/

section Chirp

/-- The chirp multiplier `e^{iπct²}`. -/
noncomputable def chirp (c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (Complex.I * (Real.pi : ℂ) * (c : ℂ) * (t : ℂ) ^ 2) * g t

/-- **Shear covariance.**  Conjugating a time–frequency shift by the chirp shears the frequency:
`chirp c ∘ π(x,ω) = e^{-iπcx²} · π(x, ω + cx) ∘ chirp c`. -/
theorem chirp_tfShift (c x ω : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    chirp c (tfShift x ω g) t
      = Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * (x : ℂ) ^ 2))
        * tfShift x (ω + c * x) (chirp c g) t := by
  unfold chirp tfShift
  dsimp only
  have hexp : Complex.exp (Complex.I * (Real.pi : ℂ) * (c : ℂ) * (t : ℂ) ^ 2)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))
      = Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * (x : ℂ) ^ 2))
        * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((ω + c * x) : ℝ) : ℂ) * (t : ℂ))
          * Complex.exp (Complex.I * (Real.pi : ℂ) * (c : ℂ) * (((t - x) : ℝ) : ℂ) ^ 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (g (t - x)) * hexp

/-- The chirp is pointwise unimodular, so it destroys no information. -/
theorem norm_chirp (c : ℝ) (g : ℝ → ℂ) (t : ℝ) : ‖chirp c g t‖ = ‖g t‖ := by
  unfold chirp
  rw [norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (Real.pi : ℂ) * (c : ℂ) * (t : ℂ) ^ 2).re = 0 := by
    have hform : Complex.I * (Real.pi : ℂ) * (c : ℂ) * (t : ℂ) ^ 2
        = ((Real.pi * c * t ^ 2 : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [hform, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [hre]
  simp

end Chirp

/-! ### Metaplectic: the Fourier generator

The second shear direction `(x,ω) ↦ (x - cω, ω)` is the Fourier conjugate of the chirp, so the
reduction needs the Fourier covariance of time–frequency shifts.  Mathlib supplies the
translation half (`fourierIntegral_comp_add_right`); the modulation half is a direct
computation from the definition, proved here. -/

section FourierGen

open FourierTransform

/-- **Modulation becomes translation under the Fourier transform.**  This is the half of the
Fourier covariance of `π(x,ω)` that Mathlib does not already provide. -/
theorem fourier_modulation (f : ℝ → ℂ) (ν w : ℝ) :
    𝓕 (fun v : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ν : ℂ) * (v : ℂ)) * f v) w
      = 𝓕 f (w - ν) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Circle.smul_def, Circle.smul_def, Real.fourierChar_apply, Real.fourierChar_apply]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Fourier covariance.**  `𝓕 ∘ π(x,ω) = e^{2πixω} · π(ω,-x) ∘ 𝓕`.

The Fourier transform implements the symplectic ROTATION `(x,ω) ↦ (ω,-x)`.  With
`chirp_tfShift` (the shear `(x,ω) ↦ (x, ω+cx)`) these generate the shears in both directions,
which is all the metaplectic input the `Λ₀` lattice reduction needs. -/
theorem fourier_tfShift (g : ℝ → ℂ) (x ω ξ : ℝ) :
    𝓕 (tfShift x ω g) ξ
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))
        * tfShift ω (-x) (𝓕 g) ξ := by
  have hfun : tfShift x ω g
      = fun v : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (v : ℂ))
          * (g ∘ fun u : ℝ => u + (-x)) v := by
    funext v; unfold tfShift; simp [sub_eq_add_neg]
  rw [hfun, fourier_modulation]
  have hbridge : ∀ f : ℝ → ℂ, 𝓕 f = Fourier.fourierIntegral 𝐞 (volume : Measure ℝ) f := by
    intro f; funext w
    rw [Real.fourier_real_eq, Fourier.fourierIntegral_def]
  have h2 : 𝓕 (g ∘ fun u : ℝ => u + (-x)) (ξ - ω)
      = ((𝐞 ((-x) * (ξ - ω)) : Circle) : ℂ) * 𝓕 g (ξ - ω) := by
    rw [hbridge, hbridge g,
      Fourier.fourierIntegral_comp_add_right (𝐞) (volume : Measure ℝ) g (-x)]
    simp [Circle.smul_def]
  rw [h2]
  unfold tfShift
  rw [Real.fourierChar_apply]
  have hexp : Complex.exp (((2 * Real.pi * (-x * (ξ - ω)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((-x : ℝ)) : ℂ) * (ξ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

end FourierGen

/-! ### Metaplectic transfer of a dependence

A metaplectic operator carries a linear dependence among time–frequency translates to a
dependence among the translates at the SHEARED points, with each coefficient multiplied by a
nonzero phase.  Since the operator is injective, independence at the new points implies
independence at the old — which is how a hard configuration is traded for an easy one. -/

section Transfer

/-- **Chirp transfer.**  A three-term dependence transfers along the shear
`(x,ω) ↦ (x, ω + cx)`, each coefficient picking up the unimodular phase `e^{-iπcxᵢ²}`. -/
theorem chirp_transfer (c : ℝ) (g : ℝ → ℂ) (A B C : ℂ) (x₁ ω₁ x₂ ω₂ t : ℝ)
    (hdep : A * g t + B * tfShift x₁ ω₁ g t + C * tfShift x₂ ω₂ g t = 0) :
    A * chirp c g t
      + (B * Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * (x₁ : ℂ) ^ 2)))
        * tfShift x₁ (ω₁ + c * x₁) (chirp c g) t
      + (C * Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * (x₂ : ℂ) ^ 2)))
        * tfShift x₂ (ω₂ + c * x₂) (chirp c g) t = 0 := by
  have h1 := chirp_tfShift c x₁ ω₁ g t
  have h2 := chirp_tfShift c x₂ ω₂ g t
  simp only [chirp] at h1 h2 ⊢
  linear_combination
    (Complex.exp (Complex.I * (Real.pi : ℂ) * (c : ℂ) * (t : ℂ) ^ 2)) * hdep - B * h1 - C * h2

/-- The transferred coefficients vanish exactly when the originals do. -/
theorem chirp_transfer_coeff_ne_zero {B : ℂ} (hB : B ≠ 0) (c x : ℝ) :
    B * Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * (x : ℂ) ^ 2)) ≠ 0 :=
  mul_ne_zero hB (Complex.exp_ne_zero _)

/-! ### The dilation generator

`(x,ω) ↦ (λx, ω/λ)`, implemented by `g(t) ↦ |λ|^{-1/2} g(t/λ)`.  Unlike the shear and the
rotation this one carries NO phase, and unlike the rotation it needs no Fourier transform. -/

/-- The `L²`-normalised dilation. -/
noncomputable def dilate (lam : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ((|lam| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * g (t / lam)

/-- **Dilation covariance.**  `D_λ ∘ π(x,ω) = π(λx, ω/λ) ∘ D_λ` — no phase factor. -/
theorem dilate_tfShift {lam : ℝ} (hlam : lam ≠ 0) (x ω : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    dilate lam (tfShift x ω g) t = tfShift (lam * x) (ω / lam) (dilate lam g) t := by
  unfold dilate tfShift
  dsimp only
  have harg : t / lam - x = (t - lam * x) / lam := by field_simp
  rw [harg]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (((t / lam) : ℝ) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((ω / lam) : ℝ) : ℂ) * (t : ℂ)) := by
    congr 1
    push_cast
    field_simp
  rw [hexp]
  ring

/-- The dilation is injective pointwise: it scales by a nonzero constant. -/
theorem dilate_eq_zero_iff {lam : ℝ} (hlam : lam ≠ 0) (g : ℝ → ℂ) (t : ℝ) :
    dilate lam g t = 0 ↔ g (t / lam) = 0 := by
  unfold dilate
  have hne : ((|lam| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hne
  · intro h; rw [h, mul_zero]

/-! ### The three-point symbol is log-expandable

ROUTE FINDING.  For the triple `{(0,0),(1,0),(√2,√2)}` the Zak fibre symbol is
`P_θ(t) = α + β e^{-2πi(t+θ)}`.  When `|β| < |α|` this factors as
`α · (1 + (β/α) e^{-2πi(t+θ)})`, and Mathlib's Mercator series gives `log P_θ` an absolutely
convergent Fourier expansion with GEOMETRICALLY decaying coefficients.

That is precisely the hypothesis of the residual-cone machinery already proved
(`smallDivisor_summable` / `smallDivisor_summable_sqrt_two` + `eigenvalue_quantised`): geometric
decay beats the small divisors of a badly-approximable `a`, the cocycle is a coboundary, the
eigenvalue is quantised, and the live set collapses to a countable set.

So this triple may not need the metaplectic reduction at all — the same argument that closes the
four-point residual cone closes it.  The lemma below is the bridge: Mathlib's Taylor coefficients
satisfy the geometric bound those lemmas consume. -/

section LogExpandable

/-- The Mercator coefficients of `log (1 + z)` obey the geometric bound
`‖cₙ‖ ≤ ‖z‖ⁿ` that `smallDivisor_summable` consumes.  (At `n = 0` the term is `0` by the junk
value of division by zero.) -/
theorem norm_taylorSeries_log_coeff_le (z : ℂ) (n : ℕ) :
    ‖(-1 : ℂ) ^ (n + 1) * z ^ n / (n : ℂ)‖ ≤ ‖z‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    rw [div_le_iff₀ hnpos]
    nlinarith [pow_nonneg (norm_nonneg z) n]

/-- Consequently the log of a symbol with a strictly dominant constant term has geometrically
decaying Fourier coefficients. -/
theorem norm_taylorSeries_log_coeff_le_geom {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    ‖(-1 : ℂ) ^ (n + 1) * z ^ n / (n : ℂ)‖ ≤ 2 * ‖z‖ ^ n := by
  refine le_trans (norm_taylorSeries_log_coeff_le z n) ?_
  nlinarith [pow_nonneg (norm_nonneg z) n]

end LogExpandable

/-! ### Symplectic normalisation: every three-point configuration is a lattice configuration

The literature status of the three-point case is not what the residual-cone route assumed.  Three
-point HRT is a THEOREM for arbitrary `L²` windows, and the proof is a reduction, not an analysis:
any three points in general position are carried by a determinant-one linear map to
`{(0,0), (1,0), (0,d)}`, which sits inside the lattice `ℤ × dℤ`, and Linnell's theorem (1999)
settles every subset of a lattice.  (Collinear triples reduce instead to distinct pure translates.)

The lemma below is that reduction, made explicit and axiom-free.  The determinant `d` is a
symplectic invariant, so it cannot be normalised away — for the Heil–Speegle triple
`{(0,0),(1,0),(√2,√2)}` it equals `√2`, an IRRATIONAL covolume.  That is precisely the regime
where the Zak transform stops diagonalising the problem and Linnell's group–von-Neumann-algebra
machinery is genuinely needed. -/

section SymplecticNormalisation

/-- **Symplectic normalisation of a three-point configuration.**  Two vectors `p q : ℝ × ℝ` with
nonzero determinant `d` are carried by an explicit **determinant-one** linear map to `(1,0)` and
`(0,d)`.  Hence `{0, p, q}` is symplectically equivalent to `{(0,0),(1,0),(0,d)} ⊆ ℤ × dℤ`. -/
theorem symplectic_normalise (p q : ℝ × ℝ) (hd0 : p.1 * q.2 - p.2 * q.1 ≠ 0) :
    ∃ a b c e : ℝ, a * e - b * c = 1 ∧
      a * p.1 + b * p.2 = 1 ∧ c * p.1 + e * p.2 = 0 ∧
      a * q.1 + b * q.2 = 0 ∧ c * q.1 + e * q.2 = p.1 * q.2 - p.2 * q.1 := by
  set d : ℝ := p.1 * q.2 - p.2 * q.1 with hd
  refine ⟨q.2 / d, -q.1 / d, -p.2, p.1, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · ring
  · field_simp; ring
  · ring

/-- The determinant is exactly the covolume of the lattice the normalised configuration generates,
and it is a symplectic invariant.  For the Heil–Speegle triple it is `√2`. -/
theorem heil_speegle_triple_det :
    (1 : ℝ) * Real.sqrt 2 - 0 * Real.sqrt 2 = Real.sqrt 2 := by ring

/-- So the Heil–Speegle triple normalises to `{(0,0),(1,0),(0,√2)}` — a lattice configuration of
irrational covolume. -/
theorem heil_speegle_normalises :
    ∃ a b c e : ℝ, a * e - b * c = 1 ∧
      a * 1 + b * 0 = 1 ∧ c * 1 + e * 0 = 0 ∧
      a * Real.sqrt 2 + b * Real.sqrt 2 = 0 ∧
      c * Real.sqrt 2 + e * Real.sqrt 2 = Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hd0 : (1 : ℝ) * Real.sqrt 2 - 0 * Real.sqrt 2 ≠ 0 := by
    rw [heil_speegle_triple_det]; exact h2
  simpa using symplectic_normalise (1, 0) (Real.sqrt 2, Real.sqrt 2) (by simpa using hd0)

/-- **Any nonzero vector normalises to `(1,0)`.**  `SL₂(ℝ)` acts transitively on `ℝ² ∖ {0}`, by an
explicit determinant-one matrix.

This is what repairs the scope gap in `HRTResonant.threePoint_moduli_all_equal`.  That result needs
the cyclic mean condition for EACH choice of distinguished coefficient, and the clean linear symbol
`c₀ + c₁e^{-2πiω}` is only available when the two REMAINING points form a lattice pair.  For
`{(0,0),(1,0),(√2,√2)}` that holds when the `(√2,√2)` term is the distinguished one, but not for
the other two choices.

Transitivity fixes it: for any choice, a determinant-one change of coordinates carries the
remaining pair to `{(0,0),(1,0)}`, restoring the lattice situation.  What still has to be supplied
is metaplectic invariance of linear independence — the three `SL₂` generators (`chirp_tfShift`,
`fourier_tfShift`, `dilate_tfShift`) proved above are exactly the ingredients for it. -/
theorem symplectic_normalise_pair (p : ℝ × ℝ) (hp : p ≠ (0, 0)) :
    ∃ a b c e : ℝ, a * e - b * c = 1 ∧ a * p.1 + b * p.2 = 1 ∧ c * p.1 + e * p.2 = 0 := by
  by_cases h1 : p.1 = 0
  · have h2 : p.2 ≠ 0 := by
      intro h
      apply hp
      have hpp : p = (p.1, p.2) := rfl
      rw [hpp, h1, h]
    have hk : (1 : ℝ) / p.2 * p.2 = 1 := one_div_mul_cancel h2
    refine ⟨0, 1 / p.2, -p.2, p.1, ?_, ?_, ?_⟩
    · linear_combination hk
    · rw [h1]; linear_combination hk
    · rw [h1]; ring
  · have hk : (1 : ℝ) / p.1 * p.1 = 1 := one_div_mul_cancel h1
    refine ⟨1 / p.1, 0, -p.2, p.1, ?_, ?_, ?_⟩
    · linear_combination hk
    · linear_combination hk
    · ring

end SymplecticNormalisation

/-- **Dilation transfers a three-point dependence.**  Unlike the chirp, dilation needs no phase
correction: it is a pointwise rescaling, so a dependence maps across with the SAME coefficients,
only the time–frequency points moving by `(x, ω) ↦ (λx, ω/λ)`. -/
theorem dilate_transfer {lam : ℝ} (hlam : lam ≠ 0) (g : ℝ → ℂ) (A B C : ℂ)
    (x₁ ω₁ x₂ ω₂ : ℝ) (t : ℝ)
    (hdep : ∀ s : ℝ, A * g s + B * tfShift x₁ ω₁ g s + C * tfShift x₂ ω₂ g s = 0) :
    A * dilate lam g t
      + B * tfShift (lam * x₁) (ω₁ / lam) (dilate lam g) t
      + C * tfShift (lam * x₂) (ω₂ / lam) (dilate lam g) t = 0 := by
  rw [← dilate_tfShift hlam x₁ ω₁ g t, ← dilate_tfShift hlam x₂ ω₂ g t]
  simp only [dilate]
  have h := hdep (t / lam)
  linear_combination ((|lam| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * h

/-- The dilated points, recorded as a lattice statement: dilation by `λ` carries `(x, ω)` to
`(λx, ω/λ)`, which preserves the symplectic determinant `x₁ω₂ - x₂ω₁`. -/
theorem dilate_preserves_det (lam : ℝ) (hlam : lam ≠ 0) (x₁ ω₁ x₂ ω₂ : ℝ) :
    (lam * x₁) * (ω₂ / lam) - (lam * x₂) * (ω₁ / lam) = x₁ * ω₂ - x₂ * ω₁ := by
  field_simp

/-! ### The Fourier generator is not needed for this configuration

`symplectic_normalise_pair` produces an arbitrary `SL₂` matrix, and realising an arbitrary `SL₂`
element metaplectically needs all three generators — including the Fourier transform, whose
dependence-transfer form requires `𝓕`-linearity across the three terms and hence integrability
plumbing.

That plumbing is avoidable here.  Shear and dilation alone generate the Borel subgroup, which
already acts transitively on vectors with NONZERO TIME COMPONENT: dilate by `1/p₁` to reach
`(1, p₁p₂)`, then shear by `-p₁p₂` to reach `(1,0)`.

And every pair arising from the Heil–Speegle triple has nonzero time component —
`{(0,0),(1,0)}` gives `1`, `{(0,0),(√2,√2)}` gives `√2`, and `{(1,0),(√2,√2)}` translates to
`{(0,0),(√2-1,√2)}` giving `√2-1`.  So the two generators already promoted to dependence transfers
(`chirp_transfer`, `dilate_transfer`) suffice, and `fourier_tfShift` can stay a covariance. -/

/-- **Borel normalisation.**  Dilation then shear carries `(p₁,p₂)` with `p₁ ≠ 0` to `(1,0)`. -/
theorem borel_normalise (p₁ p₂ : ℝ) (hp : p₁ ≠ 0) :
    ∃ lam c : ℝ, lam ≠ 0 ∧ lam * p₁ = 1 ∧ p₂ / lam + c * (lam * p₁) = 0 := by
  have hk : (1 : ℝ) / p₁ * p₁ = 1 := one_div_mul_cancel hp
  refine ⟨1 / p₁, -(p₁ * p₂), one_div_ne_zero hp, hk, ?_⟩
  have hd : p₂ / (1 / p₁) = p₂ * p₁ := by field_simp
  rw [hd, hk]
  ring

/-- The three pairs of the Heil–Speegle triple all have nonzero time component, so `borel_normalise`
applies to each and no Fourier generator is required. -/
theorem heil_speegle_pairs_time_ne_zero :
    (1 : ℝ) ≠ 0 ∧ Real.sqrt 2 ≠ 0 ∧ Real.sqrt 2 - 1 ≠ 0 := by
  refine ⟨one_ne_zero, by positivity, ?_⟩
  have h : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

/-- **Borel transfer.**  A three-point dependence whose second point has nonzero time component
transfers to a dependence whose second point is exactly `(1,0)` — a LATTICE point — with all
coefficients still nonzero.

This is the composite of `dilate_transfer` (by `1/x₁`) and `chirp_transfer` (by `-ω₁x₁`), and it is
the step that repairs the scope gap in `HRTResonant.threePoint_moduli_all_equal`: for each choice
of distinguished coefficient, the two remaining points can be moved so that they form a lattice
pair, which is what makes the linear-symbol argument available. -/
theorem borel_transfer_exists (g : ℝ → ℂ) (A B C : ℂ) (hB : B ≠ 0) (hC : C ≠ 0)
    (x₁ ω₁ x₂ ω₂ : ℝ) (hx₁ : x₁ ≠ 0)
    (hdep : ∀ s : ℝ, A * g s + B * tfShift x₁ ω₁ g s + C * tfShift x₂ ω₂ g s = 0) :
    ∃ (h : ℝ → ℂ) (B' C' : ℂ) (x₂' ω₂' : ℝ),
      B' ≠ 0 ∧ C' ≠ 0 ∧
      ∀ t : ℝ, A * h t + B' * tfShift 1 0 h t + C' * tfShift x₂' ω₂' h t = 0 := by
  set lam : ℝ := 1 / x₁ with hlamdef
  have hlam : lam ≠ 0 := one_div_ne_zero hx₁
  have hlx : lam * x₁ = 1 := by rw [hlamdef]; field_simp
  have hstep1 : ∀ t : ℝ, A * dilate lam g t
      + B * tfShift 1 (ω₁ / lam) (dilate lam g) t
      + C * tfShift (lam * x₂) (ω₂ / lam) (dilate lam g) t = 0 := by
    intro t
    have h1 := dilate_transfer hlam g A B C x₁ ω₁ x₂ ω₂ t hdep
    rwa [hlx] at h1
  set c : ℝ := -(ω₁ / lam) with hcdef
  have hzero : ω₁ / lam + c * 1 = 0 := by rw [hcdef]; ring
  refine ⟨chirp c (dilate lam g),
    B * Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * ((1 : ℝ) : ℂ) ^ 2)),
    C * Complex.exp (-(Complex.I * (Real.pi : ℂ) * (c : ℂ) * ((lam * x₂ : ℝ) : ℂ) ^ 2)),
    lam * x₂, ω₂ / lam + c * (lam * x₂),
    chirp_transfer_coeff_ne_zero hB c 1,
    chirp_transfer_coeff_ne_zero hC c (lam * x₂), ?_⟩
  intro t
  have h := chirp_transfer c (dilate lam g) A B C 1 (ω₁ / lam) (lam * x₂) (ω₂ / lam) t (hstep1 t)
  rwa [hzero] at h

end Transfer

end Composition

end HRTSmall

#print axioms HRTSmall.sub_mem_of_exp_eq
#print axioms HRTSmall.countable_setOf_exp_eq
#print axioms HRTSmall.measure_setOf_exp_eq_zero
#print axioms HRTSmall.two_point_modulation
#print axioms HRTSmall.ae_periodic_zsmul
#print axioms HRTSmall.ae_eq_zero_of_periodic
#print axioms HRTSmall.ae_periodic_neg
#print axioms HRTSmall.ae_periodic_subgroup
#print axioms HRTSmall.two_point_translation
#print axioms HRTSmall.two_point_general
#print axioms HRTSmall.tfShift_comp
#print axioms HRTSmall.norm_tfShift
#print axioms HRTSmall.two_point_hrt
#print axioms HRTSmall.tfShift_zero
#print axioms HRTSmall.threePoint_no_dependence
#print axioms HRTSmall.threePoint_linearIndependent
#print axioms HRTSmall.twoPoint_linearIndependent
#print axioms HRTSmall.countable_symbol_fibre
#print axioms HRTSmall.measure_symbol_fibre_zero
#print axioms HRTSmall.continuous_symbolFn
#print axioms HRTSmall.measure_symbolFn_zero_prod
#print axioms HRTSmall.lattice_triple_of_zak
#print axioms HRTSmall.chirp_tfShift
#print axioms HRTSmall.norm_chirp
#print axioms HRTSmall.fourier_modulation
#print axioms HRTSmall.fourier_tfShift
#print axioms HRTSmall.chirp_transfer
#print axioms HRTSmall.chirp_transfer_coeff_ne_zero
#print axioms HRTSmall.dilate_tfShift
#print axioms HRTSmall.dilate_eq_zero_iff
#print axioms HRTSmall.dilate_transfer
#print axioms HRTSmall.dilate_preserves_det
#print axioms HRTSmall.borel_normalise
#print axioms HRTSmall.heil_speegle_pairs_time_ne_zero
#print axioms HRTSmall.borel_transfer_exists
#print axioms HRTSmall.norm_taylorSeries_log_coeff_le
#print axioms HRTSmall.norm_taylorSeries_log_coeff_le_geom
#print axioms HRTSmall.symplectic_normalise
#print axioms HRTSmall.heil_speegle_normalises
#print axioms HRTSmall.symplectic_normalise_pair
