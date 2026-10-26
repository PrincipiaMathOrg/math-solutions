/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #361368 — the cone/cylinder Fourier-dimension conjecture is FALSE

MathDB open problem #361368, Conjecture 8.1 of arXiv:2401.01455v1: for a Borel set
`A ⊆ ℝ^d`, the cone `C_A = {(h y, h) : y ∈ A, h ∈ ℝ}` and the cylinder `D_A = A × ℝ`,
both living in `ℝ^{d+1}`, were conjectured to satisfy `dim_F C_A = dim_F D_A = dim_F A`.

**They do not.**  The conjecture already fails for the most ordinary generating set there is:
`A = {y : ‖y‖ ≤ 1}`, the closed unit ball of `ℝ^d`, which is compact, convex, and Borel.

## The mechanism

Fourier dimension is bounded by the ambient dimension and *saturates* on any set with nonempty
interior.  `A` has interior in `ℝ^d`, so `dim_F A = d`.  But the cone and the cylinder both have
interior in `ℝ^{d+1}` — the cone contains a ball around `(0, 2)`, the cylinder a ball around the
origin — so both have Fourier dimension `d + 1`.  Passing to the cone gains a whole dimension,
and the conjectured equality fails by `1` at every `d`.

The one analytic ingredient is `admissible_of_bump`: a set carrying a normalized smooth bump has
a probability measure whose Fourier transform decays like a Schwartz function.
`HasCompactSupport.toSchwartzMap` makes the bump a Schwartz function,
`SchwartzMap.fourierTransformCLM` keeps it one, and `SchwartzMap.decay` then supplies the required
`‖ξ‖^{N/2}` bound — with room to spare, since a Schwartz function beats every polynomial and only
`N/2` is asked for.

## What is and is not claimed

`dimF` is the source's own definition: the supremum of the `s ∈ [0, N]` for which some nonzero
finite measure carried by the set has `sup_ξ ‖ξ‖^{s/2} |μ̂(ξ)| < ∞`.  Note the endpoint `s = N`
is explicitly allowed there, and the counterexample uses it.

This refutes the conjecture **as stated**.  It says nothing about any repaired version that adds
a thinness hypothesis on `A` (empty interior, or `s < d`); the point of the example is precisely
that no boundedness, compactness, convexity or measurability hypothesis repairs it, since `A` is
already a compact convex body and every measure used is a compactly supported probability measure.

The cone is defined here exactly as the source defines it — as the set of points `(h y, h)` —
not as a sublevel set; `cone_eq_sublevel` proves the sublevel description rather than assuming it.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

namespace Principia.MathDB.P361368

open MeasureTheory Metric Module
open scoped FourierTransform RealInnerProductSpace NNReal ENNReal

/-- Smoothness of every order.  Spelled out rather than written `∞`, because that notation is
scoped in `ContDiff` and would collide with the `ENNReal` `∞` this file also needs. -/
local notation "ω∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Fourier dimension -/

section Ambient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of a finite measure, `μ̂(ξ) = ∫ e^{-2πi⟪v,ξ⟫} dμ(v)`.  The phase
convention is the one Mathlib uses for functions (`Real.fourier_eq'`), which is what makes
`measureFourier_withDensity` below a literal identity rather than a rescaling. -/
noncomputable def measureFourier (ν : Measure V) (ξ : V) : ℂ :=
  ∫ v, Complex.exp ((↑(-2 * Real.pi * ⟪v, ξ⟫) : ℂ) * Complex.I) ∂ν

theorem measureFourier_def (ν : Measure V) (ξ : V) :
    measureFourier ν ξ = ∫ v, Complex.exp ((↑(-2 * Real.pi * ⟪v, ξ⟫) : ℂ) * Complex.I) ∂ν := rfl

/-- `s` is Fourier-admissible for `E`: some nonzero finite measure carried by `E` has
`sup_ξ ‖ξ‖^{s/2} |μ̂(ξ)| < ∞`.  This is the condition inside the source's supremum, including
its ambient restriction `s ∈ [0, N]`. -/
def Admissible (E : Set V) (s : ℝ) : Prop :=
  0 ≤ s ∧ s ≤ (finrank ℝ V : ℝ) ∧
    ∃ ν : Measure V, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν Eᶜ = 0 ∧
      ∃ C : ℝ, ∀ ξ : V, ‖ξ‖ ^ (s / 2) * ‖measureFourier ν ξ‖ ≤ C

/-- The Fourier dimension of a set, as defined in the source. -/
noncomputable def dimF (E : Set V) : ℝ := sSup {s : ℝ | Admissible E s}

/-- The Fourier dimension never exceeds the ambient dimension. -/
theorem dimF_le_finrank {E : Set V} {s : ℝ} (hs : Admissible E s) :
    dimF E ≤ (finrank ℝ V : ℝ) :=
  csSup_le ⟨s, hs⟩ fun t ht => ht.2.1

end Ambient

/-! ### The analytic core: a smooth bump saturates the Fourier dimension -/

section Core

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of a measure with a density is the Fourier transform of the density. -/
theorem measureFourier_withDensity {φ : V → ℝ} (hφ0 : ∀ x, 0 ≤ φ x)
    (hφm : Measurable fun x => Real.toNNReal (φ x)) (ξ : V) :
    measureFourier ((volume : Measure V).withDensity
        (fun x => ((Real.toNNReal (φ x) : ℝ≥0) : ℝ≥0∞))) ξ
      = 𝓕 (fun x => (φ x : ℂ)) ξ := by
  rw [measureFourier_def, integral_withDensity_eq_integral_smul hφm, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hc : ((Real.toNNReal (φ v) : ℝ≥0) : ℝ) = φ v := Real.coe_toNNReal _ (hφ0 v)
  simp only [NNReal.smul_def, hc, Complex.real_smul, smul_eq_mul]
  ring

/-- A unit-mass nonnegative density gives a probability measure. -/
theorem withDensity_univ {φ : V → ℝ} (hφ0 : ∀ x, 0 ≤ φ x)
    (hφintble : Integrable φ (volume : Measure V)) (hφint : ∫ x, φ x = 1) :
    ((volume : Measure V).withDensity
      (fun x => ((Real.toNNReal (φ x) : ℝ≥0) : ℝ≥0∞))) Set.univ = 1 := by
  rw [show (fun x => ((Real.toNNReal (φ x) : ℝ≥0) : ℝ≥0∞))
        = fun x => ENNReal.ofReal (φ x) from rfl,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hφintble (Filter.Eventually.of_forall hφ0), hφint,
    ENNReal.ofReal_one]

/-- A measure with a density supported in `s` gives no mass to the complement of `s`. -/
theorem withDensity_compl {φ : V → ℝ} {s : Set V} (hs : MeasurableSet s)
    (hsupp : Function.support φ ⊆ s) :
    ((volume : Measure V).withDensity
      (fun x => ((Real.toNNReal (φ x) : ℝ≥0) : ℝ≥0∞))) sᶜ = 0 := by
  rw [show (fun x => ((Real.toNNReal (φ x) : ℝ≥0) : ℝ≥0∞))
        = fun x => ENNReal.ofReal (φ x) from rfl,
    withDensity_apply _ hs.compl]
  have hae : ∀ᵐ x ∂((volume : Measure V).restrict sᶜ), ENNReal.ofReal (φ x) = 0 := by
    filter_upwards [ae_restrict_mem hs.compl] with x hx
    have hx0 : φ x = 0 := by
      by_contra hne
      exact hx (hsupp (Function.mem_support.mpr hne))
    simp [hx0]
  simpa using lintegral_congr_ae hae

/-- **The decay estimate.**  A smooth compactly supported density has a Schwartz Fourier
transform, hence beats `‖ξ‖^{-N/2}`. -/
theorem exists_decay_bound {φ : V → ℝ} (hφcs : HasCompactSupport φ) (hφsm : ContDiff ℝ ω∞ φ) :
    ∃ C : ℝ, ∀ ξ : V,
      ‖ξ‖ ^ ((finrank ℝ V : ℝ) / 2) * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ≤ C := by
  have hΦcs : HasCompactSupport (⇑Complex.ofRealCLM ∘ φ) :=
    hφcs.comp_left (map_zero Complex.ofRealCLM)
  let Φ : SchwartzMap V ℂ := hΦcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφsm)
  have hfc : ∀ ξ : V,
      𝓕 (fun x => (φ x : ℂ)) ξ = (SchwartzMap.fourierTransformCLM ℂ Φ) ξ := fun ξ => rfl
  obtain ⟨C₁, -, hC₁⟩ := (SchwartzMap.fourierTransformCLM ℂ Φ).decay (finrank ℝ V) 0
  obtain ⟨C₀, -, hC₀⟩ := (SchwartzMap.fourierTransformCLM ℂ Φ).decay 0 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hC₁ hC₀
  refine ⟨max C₀ C₁, fun ξ => ?_⟩
  rw [hfc ξ]
  have hN : (0:ℝ) ≤ (finrank ℝ V : ℝ) := Nat.cast_nonneg _
  rcases le_or_gt ‖ξ‖ 1 with hle | hgt
  · have h1 : ‖ξ‖ ^ ((finrank ℝ V : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) hle (by linarith)
    calc ‖ξ‖ ^ ((finrank ℝ V : ℝ) / 2) * ‖(SchwartzMap.fourierTransformCLM ℂ Φ) ξ‖
        ≤ 1 * ‖(SchwartzMap.fourierTransformCLM ℂ Φ) ξ‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖(SchwartzMap.fourierTransformCLM ℂ Φ) ξ‖ := one_mul _
      _ ≤ C₀ := hC₀ ξ
      _ ≤ max C₀ C₁ := le_max_left _ _
  · have h2 : ‖ξ‖ ^ ((finrank ℝ V : ℝ) / 2) ≤ ‖ξ‖ ^ ((finrank ℝ V : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have h3 : ‖ξ‖ ^ ((finrank ℝ V : ℝ)) = ‖ξ‖ ^ (finrank ℝ V) := Real.rpow_natCast _ _
    calc ‖ξ‖ ^ ((finrank ℝ V : ℝ) / 2) * ‖(SchwartzMap.fourierTransformCLM ℂ Φ) ξ‖
        ≤ ‖ξ‖ ^ (finrank ℝ V) * ‖(SchwartzMap.fourierTransformCLM ℂ Φ) ξ‖ := by
          rw [← h3]; exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ C₁ := hC₁ ξ
      _ ≤ max C₀ C₁ := le_max_right _ _

/-- **A set carrying a normalized smooth bump is admissible at the ambient dimension.** -/
theorem admissible_of_bump {E s : Set V} {φ : V → ℝ}
    (hs : MeasurableSet s) (hsE : s ⊆ E) (hsupp : Function.support φ ⊆ s)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφintble : Integrable φ (volume : Measure V))
    (hφint : ∫ x, φ x = 1) (hφcs : HasCompactSupport φ) (hφcont : Continuous φ)
    (hφsm : ContDiff ℝ ω∞ φ) : Admissible E (finrank ℝ V : ℝ) := by
  have hφm : Measurable fun x => Real.toNNReal (φ x) :=
    (continuous_real_toNNReal.comp hφcont).measurable
  have hmass := withDensity_univ hφ0 hφintble hφint
  obtain ⟨C, hC⟩ := exists_decay_bound hφcs hφsm
  refine ⟨Nat.cast_nonneg _, le_rfl,
    (volume : Measure V).withDensity (fun x => ((Real.toNNReal (φ x) : ℝ≥0) : ℝ≥0∞)),
    ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩, ?_, ?_, C, fun ξ => ?_⟩
  · intro hzero
    rw [hzero] at hmass
    simp at hmass
  · exact measure_mono_null (Set.compl_subset_compl.mpr hsE) (withDensity_compl hs hsupp)
  · rw [measureFourier_withDensity hφ0 hφm ξ]
    exact hC ξ

/-- **A set containing a nonempty open set has full Fourier dimension.** -/
theorem dimF_eq_finrank_of_isOpen {E U : Set V} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUE : U ⊆ E) : dimF E = (finrank ℝ V : ℝ) := by
  obtain ⟨c, hc⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU c hc
  obtain ⟨f, hrOut⟩ : ∃ f : ContDiffBump c, f.rOut = r :=
    ⟨⟨r / 2, r, by linarith, by linarith⟩, rfl⟩
  have hsuppEq : Function.support (f.normed (volume : Measure V)) = Metric.ball c r := by
    rw [f.support_normed_eq, hrOut]
  have hmem : Admissible E (finrank ℝ V : ℝ) :=
    admissible_of_bump measurableSet_ball (hball.trans hUE) hsuppEq.subset
      (fun x => f.nonneg_normed x)
      (f.integrable_normed : Integrable (f.normed (volume : Measure V)) volume)
      f.integral_normed f.hasCompactSupport_normed f.continuous_normed f.contDiff_normed
  refine le_antisymm (csSup_le ⟨_, hmem⟩ fun t ht => ht.2.1) (le_csSup ?_ hmem)
  exact ⟨(finrank ℝ V : ℝ), fun t ht => ht.2.1⟩

end Core

/-! ### Splitting `ℝ^{d+1}` into `ℝ^d × ℝ` -/

section Split

variable {d : ℕ}

/-- The point of `ℝ^{d+1}` with base `y ∈ ℝ^d` and height `h`. -/
def pt (y : EuclideanSpace ℝ (Fin d)) (h : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp y) h)

/-- The base of a point of `ℝ^{d+1}`: its first `d` coordinates. -/
def base (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => x i.castSucc

/-- The height of a point of `ℝ^{d+1}`: its last coordinate. -/
def hgt (x : EuclideanSpace ℝ (Fin (d + 1))) : ℝ := x (Fin.last d)

@[simp] theorem base_apply (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    base x i = x i.castSucc := rfl

@[simp] theorem pt_castSucc (y : EuclideanSpace ℝ (Fin d)) (h : ℝ) (i : Fin d) :
    pt y h i.castSucc = y i := by
  change Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp y) h i.castSucc = WithLp.ofLp y i
  simp

@[simp] theorem pt_last (y : EuclideanSpace ℝ (Fin d)) (h : ℝ) : pt y h (Fin.last d) = h := by
  change Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp y) h (Fin.last d) = h
  simp

@[simp] theorem base_pt (y : EuclideanSpace ℝ (Fin d)) (h : ℝ) : base (pt y h) = y := by
  ext i; simp

@[simp] theorem hgt_pt (y : EuclideanSpace ℝ (Fin d)) (h : ℝ) : hgt (pt y h) = h := by
  simp [hgt]

@[simp] theorem pt_base_hgt (x : EuclideanSpace ℝ (Fin (d + 1))) : pt (base x) (hgt x) = x := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [hgt]
  · intro j; simp

theorem base_sub (x z : EuclideanSpace ℝ (Fin (d + 1))) :
    base (x - z) = base x - base z := by ext i; rfl

theorem hgt_sub (x z : EuclideanSpace ℝ (Fin (d + 1))) : hgt (x - z) = hgt x - hgt z := rfl

theorem norm_base_le (x : EuclideanSpace ℝ (Fin (d + 1))) : ‖base x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_castSucc (f := fun i : Fin (d + 1) => ‖x i‖ ^ 2)]
  have hcoord : ∀ i : Fin d, ‖base x i‖ ^ 2 = ‖x i.castSucc‖ ^ 2 := fun i => rfl
  simp only [hcoord]
  have hlast : (0:ℝ) ≤ ‖x (Fin.last d)‖ ^ 2 := by positivity
  linarith

theorem abs_hgt_le (x : EuclideanSpace ℝ (Fin (d + 1))) : |hgt x| ≤ ‖x‖ := by
  have hsq : ‖x (Fin.last d)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (f := fun i : Fin (d + 1) => ‖x i‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ _)
  have hn : ‖x (Fin.last d)‖ = |hgt x| := Real.norm_eq_abs _
  rw [hn] at hsq
  nlinarith [abs_nonneg (hgt x), norm_nonneg x]

theorem norm_base_sub_le (x z : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖base x - base z‖ ≤ ‖x - z‖ := by
  rw [← base_sub]; exact norm_base_le _

theorem abs_hgt_sub_le (x z : EuclideanSpace ℝ (Fin (d + 1))) :
    |hgt x - hgt z| ≤ ‖x - z‖ := by
  rw [← hgt_sub]; exact abs_hgt_le _

end Split

/-! ### The counterexample -/

section Counterexample

variable {d : ℕ}

/-- The generating set: the closed unit ball of `ℝ^d`.  Compact, convex, Borel. -/
def gen (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {y | ‖y‖ ≤ 1}

/-- `C_A = {(h y, h) : y ∈ A, h ∈ ℝ}`, the source's cone. -/
def coneOver (A : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | ∃ y ∈ A, ∃ h : ℝ, x = pt (h • y) h}

/-- `D_A = A × ℝ`, the source's cylinder. -/
def cylOver (A : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | ∃ y ∈ A, ∃ h : ℝ, x = pt y h}

/-- **The sublevel description of the cone**, equation (3) of the source: the cone over the closed
unit ball is the closed double cone `‖y‖ ≤ |h|`.  Proved, not assumed. -/
theorem cone_eq_sublevel (d : ℕ) :
    coneOver (gen d) = {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖base x‖ ≤ |hgt x|} := by
  ext x
  constructor
  · rintro ⟨y, hy, h, rfl⟩
    have hy' : ‖y‖ ≤ 1 := hy
    show ‖base (pt (h • y) h)‖ ≤ |hgt (pt (h • y) h)|
    rw [base_pt, hgt_pt, norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg h, norm_nonneg y]
  · intro hx
    have hx' : ‖base x‖ ≤ |hgt x| := hx
    rcases eq_or_ne (hgt x) 0 with h0 | h0
    · have hb : base x = 0 := by
        have hle : ‖base x‖ ≤ 0 := by rw [h0] at hx'; simpa using hx'
        exact norm_le_zero_iff.mp hle
      refine ⟨0, ?_, 0, ?_⟩
      · show ‖(0 : EuclideanSpace ℝ (Fin d))‖ ≤ 1
        simp
      · rw [smul_zero, ← hb, ← h0, pt_base_hgt]
    · refine ⟨(hgt x)⁻¹ • base x, ?_, hgt x, ?_⟩
      · have hnorm : ‖(hgt x)⁻¹ • base x‖ = ‖base x‖ / |hgt x| := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
          ring
        show ‖(hgt x)⁻¹ • base x‖ ≤ 1
        rw [hnorm, div_le_one (abs_pos.mpr h0)]
        exact hx'
      · rw [smul_inv_smul₀ h0, pt_base_hgt]

/-- The cylinder over the closed unit ball is the slab `‖y‖ ≤ 1`. -/
theorem cyl_eq_slab (d : ℕ) :
    cylOver (gen d) = {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖base x‖ ≤ 1} := by
  ext x
  constructor
  · rintro ⟨y, hy, h, rfl⟩
    have hy' : ‖y‖ ≤ 1 := hy
    show ‖base (pt y h)‖ ≤ 1
    rw [base_pt]
    exact hy'
  · intro hx
    exact ⟨base x, hx, hgt x, (pt_base_hgt x).symm⟩

/-- `dim_F A = d`: the closed unit ball has interior. -/
theorem dimF_gen (d : ℕ) : dimF (gen d) = (d : ℝ) := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ gen d := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  have hd := dimF_eq_finrank_of_isOpen Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self one_pos⟩ hsub
  rwa [finrank_euclideanSpace_fin] at hd

/-- `dim_F C_A = d + 1`: the double cone contains a ball around `(0, 2)`. -/
theorem dimF_cone (d : ℕ) : dimF (coneOver (gen d)) = (d : ℝ) + 1 := by
  have hbz : base (pt (0 : EuclideanSpace ℝ (Fin d)) 2) = 0 := base_pt _ _
  have hhz : hgt (pt (0 : EuclideanSpace ℝ (Fin d)) 2) = 2 := hgt_pt _ _
  have hsub : Metric.ball (pt (0 : EuclideanSpace ℝ (Fin d)) 2) (1 / 2)
      ⊆ coneOver (gen d) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hb : ‖base x‖ < 1 / 2 := by
      have h1 := norm_base_sub_le x (pt (0 : EuclideanSpace ℝ (Fin d)) 2)
      rw [hbz, sub_zero] at h1
      linarith
    have hh : |hgt x - 2| < 1 / 2 := by
      have h1 := abs_hgt_sub_le x (pt (0 : EuclideanSpace ℝ (Fin d)) 2)
      rw [hhz] at h1
      linarith
    have hhpos : 3 / 2 < hgt x := by
      have hlt := abs_lt.mp hh
      linarith [hlt.1]
    rw [cone_eq_sublevel]
    show ‖base x‖ ≤ |hgt x|
    rw [abs_of_pos (by linarith : (0:ℝ) < hgt x)]
    linarith
  have hd := dimF_eq_finrank_of_isOpen Metric.isOpen_ball
    ⟨_, Metric.mem_ball_self (by norm_num)⟩ hsub
  rw [finrank_euclideanSpace_fin] at hd
  rw [hd, Nat.cast_add, Nat.cast_one]

/-- `dim_F D_A = d + 1`: the slab contains a ball around the origin. -/
theorem dimF_cyl (d : ℕ) : dimF (cylOver (gen d)) = (d : ℝ) + 1 := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) (1 / 2) ⊆ cylOver (gen d) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [cyl_eq_slab]
    show ‖base x‖ ≤ 1
    have hle := norm_base_le x
    linarith
  have hd := dimF_eq_finrank_of_isOpen Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (by norm_num)⟩ hsub
  rw [finrank_euclideanSpace_fin] at hd
  rw [hd, Nat.cast_add, Nat.cast_one]

/-- **MathDB #361368: Conjecture 8.1 is false.**  For the closed unit ball `A` of `ℝ^d` — compact,
convex and Borel — the cone and the cylinder both have Fourier dimension `d + 1`, one more than
`dim_F A = d`. -/
theorem conjecture_false (d : ℕ) :
    dimF (gen d) = (d : ℝ) ∧
      dimF (coneOver (gen d)) = (d : ℝ) + 1 ∧ dimF (cylOver (gen d)) = (d : ℝ) + 1 :=
  ⟨dimF_gen d, dimF_cone d, dimF_cyl d⟩

/-- The conjectured equalities fail, at every `d`, by exactly one dimension. -/
theorem cone_ne_gen (d : ℕ) : dimF (coneOver (gen d)) ≠ dimF (gen d) := by
  rw [dimF_cone, dimF_gen]
  intro h
  linarith

theorem cyl_ne_gen (d : ℕ) : dimF (cylOver (gen d)) ≠ dimF (gen d) := by
  rw [dimF_cyl, dimF_gen]
  intro h
  linarith

end Counterexample

end Principia.MathDB.P361368
