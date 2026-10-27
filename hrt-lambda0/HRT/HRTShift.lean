import HRTZakL2
import ZakTransform

/-!
# `S_a` — the Zak shift on the torus, as an isometry

The `√2` translation is the one `Λ₀` covariance that `HRTTransfer.W_rep` cannot supply: a
non-lattice shift is not a reindex of the coefficient array.  `HRTMix` computes what it is at
COEFFICIENT level and records why that level is unusable (the covariance becomes convolution with
the Fourier coefficients of an indicator, which decay like `1/j` — in `ℓ²` but not `ℓ¹`, so there is
no algebraic normal form).

At FUNCTION level it is clean, and this file supplies the two factors.

**Derivation (checked).**  On `ℝ × ℝ` the shift is literally a translation:
`Z(T_a g)(t,ω) = ∑ₙ g(t−a−n)e^{2πinω} = Zg(t−a, ω)`.  The twist is an artefact of restricting to
the fundamental domain, via `Zg(t+1,ω) = e^{2πiω}Zg(t,ω)`.  For `t ∈ [0,1)`, `0 < a < 1`: if
`t ≥ a` there is no correction; if `t < a` then `t−a+1 ∈ [1−a,1)` and
`Zg(t−a,ω) = e^{−2πiω}Zg(t−a+1,ω)`.  Hence

    S_a = M_φ ∘ R_a,   R_a(t,ω) = (t − a, ω),   φ(t,ω) = e^{−2πiω}·1_{t<a} + 1_{t≥a}

Both factors are isometries, so `S_a` is one:

* `R_a` is a ROTATION of the first coordinate — measure preserving, transported by
  `Lp.compMeasurePreserving` (`norm_rot_comp`).
* `M_φ` is multiplication by a UNIMODULAR function (`eLpNorm_unimodular_mul`).  Note this needs no
  measurability of `φ` at all for the seminorm identity — it depends only on pointwise norms.

Neither is new mathematics; the content was finding that the twist appears ONCE, as a multiplier,
rather than smeared across a convolution.

**VERIFICATION STATUS.**  This module BUILDS (`Built HRTShift (950s)`,
`Build completed successfully`), every declaration `[propext, Classical.choice, Quot.sound]`.
Mathematics and integration are both verified; the earlier "daemon-verified but unbuilt" caveat is
discharged.  Workflow that got here, worth keeping: the warm `leand` daemon checks pure-Mathlib
content in ~1 s but strips imports (so it cannot see repo modules), while the module build catches
file-level defects no inlined probe can (a stray `set_option` between a docstring and its theorem).
Neither substitutes for the other — daemon for mathematics, build for integration.
-/

namespace HRTShift

open MeasureTheory AddCircle
open scoped ENNReal

/-! ### The `M_φ` factor — multiplication by a unimodular function -/

/-- **Multiplication by a unimodular function preserves every `eLpNorm`.**  No measurability
hypothesis: the statement depends only on pointwise norms.  `HRTChar.eLpNorm_chr_mul` is the
special case of a pure character; the Zak wrap multiplier is indicator-based, so the general form
is what is needed. -/
theorem eLpNorm_unimodular_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} (hφ : ∀ x, ‖φ x‖ = 1) (f : α → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => φ x * f x) p μ = eLpNorm f p μ := by
  refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hφ x, one_mul]

/-- Hence `MemLp` is preserved. -/
theorem memLp_unimodular_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} (hφ : ∀ x, ‖φ x‖ = 1) (hφm : AEStronglyMeasurable φ μ)
    {f : α → ℂ} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp (fun x => φ x * f x) p μ := by
  refine ⟨hφm.mul hf.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_unimodular_mul hφ f p]
  exact hf.2

/-- The Zak wrap multiplier: `e^{−2πiω}` where the shift wraps, `1` where it does not. -/
noncomputable def wrapPhi (a : ℝ) (p : ℝ × ℝ) : ℂ :=
  if p.1 < a then Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (p.2 : ℂ))) else 1

/-- It is unimodular — the line-bundle twist has modulus one, which is why `S_a` is an isometry. -/
theorem norm_wrapPhi (a : ℝ) (p : ℝ × ℝ) : ‖wrapPhi a p‖ = 1 := by
  unfold wrapPhi
  split
  · rw [Complex.norm_exp]
    simp
  · simp

/-- So the wrap multiplier is an `eLpNorm` isometry. -/
theorem eLpNorm_wrapPhi_mul (a : ℝ) {μ : Measure (ℝ × ℝ)} (f : ℝ × ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => wrapPhi a x * f x) p μ = eLpNorm f p μ :=
  eLpNorm_unimodular_mul (norm_wrapPhi a) f p

/-! ### Why `wrapPhi` is the RIGHT multiplier

The two isometry facts alone do not say the composite IS the Zak shift — they would hold for any
unimodular `φ`.  What pins `wrapPhi` down is the identity below: for a QUASI-PERIODIC `F` (which
`Zg` is, by `zak_quasi_periodic_fst`), translating time by `a` equals `wrapPhi` times `F` evaluated
at the representative brought back into the fundamental domain.

Stated with quasi-periodicity as a HYPOTHESIS, so it is a fact about the structure rather than
about `zak` — which also means it transfers to any other quasi-periodic object unchanged. -/

/-- The representative of `t − a` inside `[0,1)`, for `t ∈ [0,1)` and `a ∈ (0,1)`. -/
noncomputable def shiftRep (a t : ℝ) : ℝ := if t < a then t - a + 1 else t - a

/-- **The wrap multiplier is exactly right.**  This is what makes `S_a = M_φ ∘ R_a` the Zak shift
and not merely some isometry: the twist `e^{−2πiω}` cancels precisely the quasi-periodicity factor
picked up by re-entering the fundamental domain. -/
theorem quasi_shift_eq (F : ℝ → ℝ → ℂ)
    (hq : ∀ t ω : ℝ, F (t + 1) ω = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * F t ω)
    (a t ω : ℝ) :
    F (t - a) ω = wrapPhi a (t, ω) * F (shiftRep a t) ω := by
  unfold wrapPhi shiftRep
  by_cases h : t < a
  · simp only [if_pos h]
    rw [hq (t - a) ω, ← mul_assoc, ← Complex.exp_add]
    have hz : -(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ))
        + 2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) = 0 := by ring
    rw [hz, Complex.exp_zero, one_mul]
  · simp only [if_neg h, one_mul]

/-- The wrapped representative does land back in the fundamental domain. -/
theorem shiftRep_mem (a t : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ shiftRep a t ∧ shiftRep a t < 1 := by
  unfold shiftRep
  by_cases h : t < a
  · simp only [if_pos h]
    constructor <;> linarith
  · simp only [if_neg h]
    push Not at h
    constructor <;> linarith

/-! ### The `R_a` factor — rotation of the first torus coordinate -/

/-- Rotation of the time coordinate on `T² = AddCircle 1 × AddCircle 1`. -/
noncomputable abbrev rot (a : ℝ) :
    AddCircle (1:ℝ) × AddCircle (1:ℝ) → AddCircle (1:ℝ) × AddCircle (1:ℝ) :=
  fun p => (p.1 - ((a : ℝ) : AddCircle (1:ℝ)), p.2)

/-- Haar on the two-torus, as the product of the circle Haars.  `HRTZakL2` supplies
`volume_prod_eq_haar_prod` to reconcile this with the pi-torus presentation. -/
noncomputable abbrev T2mu : Measure (AddCircle (1:ℝ) × AddCircle (1:ℝ)) :=
  (haarAddCircle : Measure (AddCircle (1:ℝ))).prod haarAddCircle

/-- **The rotation preserves Haar.**  Delegates to `HRTZakL2.measurePreserving_rotFst`, which is
STRICTLY MORE GENERAL (any `UnitAddCircle`, not a coerced real).  I originally re-derived it here —
the daemon made writing a lemma cheaper than searching for one, which is a real hazard of a fast
verification loop.  Kept as a named specialisation because `rot` is stated with a real shift. -/
theorem measurePreserving_rotFst (a : ℝ) : MeasurePreserving (rot a) T2mu T2mu :=
  HRTZakL2.measurePreserving_rotFst ((a : ℝ) : AddCircle (1:ℝ))

/-! ### `hGnz` for a GENERAL `L²` window — no compact support

`HRTAssembly` carries `hGnz` (the fibre is not a.e. zero) as a hypothesis, and on the compactly
supported class it is θ-dependent for a reason recorded there: a slice of an `L²` function exists
only for a.e. θ.  The `L²` route removes the restriction entirely, and the argument is ABSTRACT —
nothing about the Zak transform enters until the final line.

Chain: `g ≠ 0` ⟹ `zakL2 g ≠ 0` (`HRTZakL2.zakL2_ne_zero`) ⟹ `zakSheared g ≠ 0` (the shear is an
isometry) ⟹ some θ-slice is live (Tonelli).  Only the last step needed new mathematics. -/

/-- **A nonzero `L²` element has nonzero mass.** -/
theorem lintegral_nnnorm_sq_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) (hf : f ≠ 0) :
    (∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂μ) ≠ 0 := by
  intro hzero
  refine hf ?_
  have hm : AEMeasurable (fun x => (‖f x‖₊ : ENNReal) ^ 2) μ :=
    ((Lp.aestronglyMeasurable f).aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hae : ∀ᵐ x ∂μ, (‖f x‖₊ : ENNReal) ^ 2 = 0 := (lintegral_eq_zero_iff' hm).mp hzero
  refine (Lp.eq_zero_iff_ae_eq_zero).mpr ?_
  filter_upwards [hae] with x hx
  have hn : (‖f x‖₊ : ENNReal) = 0 := by
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  simpa using hn

/-- **A nonzero `L²` element on a product has a LIVE SLICE.**  Contrapositive of Tonelli: if every
`y`-slice vanished a.e. the double integral would vanish, forcing `F = 0`. -/
theorem exists_live_slice {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (F : Lp ℂ 2 (μ.prod ν)) (hF : F ≠ 0) :
    ∃ y : β, ¬ (∀ᵐ x ∂μ, F (x, y) = 0) := by
  by_contra hcon
  push Not at hcon
  refine lintegral_nnnorm_sq_ne_zero F hF ?_
  have hm : AEMeasurable (fun p : α × β => (‖F p‖₊ : ENNReal) ^ 2) (μ.prod ν) :=
    ((Lp.aestronglyMeasurable F).aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
  rw [MeasureTheory.lintegral_prod_symm _ hm]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards with y
  have hslice : ∀ᵐ x ∂μ, (‖F (x, y)‖₊ : ENNReal) ^ 2 = 0 := by
    filter_upwards [hcon y] with x hx
    simp [hx]
  rw [lintegral_congr_ae hslice]
  exact lintegral_zero

/-- The sheared Zak transform of a nonzero window is nonzero — the shear is an isometry. -/
theorem zakSheared_ne_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0)) :
    HRTZakL2.zakSheared hθ0 hθ1 hg ≠ 0 := by
  intro h0
  refine HRTZakL2.zakL2_ne_zero hθ0 hθ1 hg hgne (norm_eq_zero.mp ?_)
  rw [← Lp.norm_compMeasurePreserving (HRTZakL2.zakL2 hθ0 hθ1 hg)
      HRTZakL2.measurePreserving_prodToTorusHaar]
  first
    | exact norm_eq_zero.mpr h0
    | simpa [HRTZakL2.zakSheared] using congrArg norm h0

/-- **`hGnz` for a general `L²` window.**  Some θ-slice of the sheared Zak transform is live — which
is all the argument needs, since θ is chosen by us.  No compact support anywhere. -/
theorem exists_live_fibre {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0)) :
    ∃ y : UnitAddCircle, ¬ (∀ᵐ x ∂(haarAddCircle : Measure UnitAddCircle),
      (HRTZakL2.zakSheared hθ0 hθ1 hg) (x, y) = 0) :=
  exists_live_slice _ (zakSheared_ne_zero hθ0 hθ1 hg hgne)

/-- **The rotation transports `L²` isometrically** — the `R_a` factor of `S_a`. -/
theorem norm_rot_comp (a : ℝ) (f : Lp ℂ 2 T2mu) :
    ‖Lp.compMeasurePreserving (rot a) (measurePreserving_rotFst a) f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (measurePreserving_rotFst a)


/-! ### `M_φ` as a BUNDLED operator, and the slice transfer

Two pieces `hcoc` needs, both stated ABSTRACTLY so they carry no Zak content.

`eLpNorm_unimodular_mul` above gives the seminorm isometry but not the OPERATOR.  `HRTChar` built
the operator for a character on `L²(ℝ)`; the version here is for an arbitrary measurable unimodular
`φ` on an arbitrary measure space.  That generality is not decoration — the Zak wrap multiplier is
`if p.1 < a`, which uses an ORDER, and `AddCircle` has none, so a torus-specific construction would
have to fix a representative first.  Abstractly, instantiating needs only a measurable unimodular
function.

`ae_ae_slice_eq_zero` is the converse of `exists_live_slice`: it carries an `L²` identity on the
torus down to the individual θ-fibres, which is how the Λ₀ dependence reaches the cocycle. -/

section Multiplier

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The multiplier as an `AEEqFun`. -/
noncomputable def phiAE (φ : α → ℂ) (hφm : Measurable φ) : α →ₘ[μ] ℂ :=
  AEEqFun.mk φ hφm.aestronglyMeasurable

theorem coeFn_phiAE (φ : α → ℂ) (hφm : Measurable φ) :
    ⇑(phiAE (μ := μ) φ hφm) =ᵐ[μ] φ :=
  AEEqFun.coeFn_mk φ hφm.aestronglyMeasurable

/-- Multiplying an `AEEqFun` by a unimodular multiplier preserves the `L²` seminorm. -/
theorem eLpNorm_phiAE_mul {φ : α → ℂ} (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1)
    (f : α →ₘ[μ] ℂ) :
    eLpNorm (phiAE (μ := μ) φ hφm * f) 2 μ = eLpNorm f 2 μ := by
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [AEEqFun.coeFn_mul (phiAE (μ := μ) φ hφm) f, coeFn_phiAE (μ := μ) φ hφm]
    with x h1 h2
  rw [h1, Pi.mul_apply, h2, norm_mul, hφ x, one_mul]


/-! `AEEqFun` is a ring, but `LeftDistribClass (α →ₘ[μ] ℂ)` and
`SMulCommClass ℂ (α →ₘ[μ] ℂ) (α →ₘ[μ] ℂ)` are BOTH UNSYNTHESIZABLE, so `mul_add` and
`mul_smul_comm` do not apply.  The distributivity has to be done by a.e. reasoning, as standalone
lemmas.  (Recorded in the campaign notes after the same trap in `HRTChar`; hit again here by
copying that file's SHAPE without its fix.) -/

theorem phiAE_mul_add {φ : α → ℂ} (hφm : Measurable φ) (f g : α →ₘ[μ] ℂ) :
    phiAE (μ := μ) φ hφm * (f + g)
      = phiAE (μ := μ) φ hφm * f + phiAE (μ := μ) φ hφm * g := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul (phiAE (μ := μ) φ hφm) (f + g),
    AEEqFun.coeFn_add f g,
    AEEqFun.coeFn_add (phiAE (μ := μ) φ hφm * f) (phiAE (μ := μ) φ hφm * g),
    AEEqFun.coeFn_mul (phiAE (μ := μ) φ hφm) f,
    AEEqFun.coeFn_mul (phiAE (μ := μ) φ hφm) g] with x h1 h2 h3 h4 h5
  rw [h1, h3]
  simp only [Pi.add_apply, Pi.mul_apply, h2, h4, h5]
  ring

theorem phiAE_mul_smul {φ : α → ℂ} (hφm : Measurable φ) (c : ℂ) (f : α →ₘ[μ] ℂ) :
    phiAE (μ := μ) φ hφm * (c • f) = c • (phiAE (μ := μ) φ hφm * f) := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul (phiAE (μ := μ) φ hφm) (c • f),
    AEEqFun.coeFn_smul c f,
    AEEqFun.coeFn_smul c (phiAE (μ := μ) φ hφm * f),
    AEEqFun.coeFn_mul (phiAE (μ := μ) φ hφm) f] with x h1 h2 h3 h4
  rw [h1, h3]
  simp only [Pi.smul_apply, Pi.mul_apply, h2, h4, smul_eq_mul]
  ring

/-- **Multiplication by a unimodular function, as a linear map on `L²`.** -/
noncomputable def multL {φ : α → ℂ} (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ⟨phiAE (μ := μ) φ hφm * (f : α →ₘ[μ] ℂ), by
    rw [Lp.mem_Lp_iff_eLpNorm_lt_top, eLpNorm_phiAE_mul hφm hφ]
    exact Lp.eLpNorm_lt_top f⟩
  map_add' f g := by
    refine Subtype.ext ?_
    exact phiAE_mul_add hφm _ _
  map_smul' c f := by
    refine Subtype.ext ?_
    exact phiAE_mul_smul hφm c _

theorem norm_multL {φ : α → ℂ} (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1) (f : Lp ℂ 2 μ) :
    ‖multL hφm hφ f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_phiAE_mul hφm hφ _

/-- **`M_φ` as a continuous linear map** — an isometry, so the bound is `1` exactly. -/
noncomputable def multLC {φ : α → ℂ} (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (multL hφm hφ).mkContinuous 1 (fun f => by rw [one_mul, norm_multL])

/-- **A vanishing `L²` element has a.e.-vanishing slices.** -/
theorem ae_ae_slice_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (F : Lp ℂ 2 (μ.prod ν)) (hF : F = 0) :
    ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, F (x, y) = 0 := by
  have h0 : ∀ᵐ p ∂(μ.prod ν), F p = 0 := by
    have hz := Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ.prod ν)
    filter_upwards [hF ▸ hz] with p hp using hp
  -- `ae_ae_of_ae_prod` gives `∀ᵐ x, ∀ᵐ y`; the fibre index is the SECOND coordinate, so go
  -- through the measure-preserving swap to get `∀ᵐ y, ∀ᵐ x`.
  have hmap : Measure.map (Prod.swap : β × α → α × β) (ν.prod μ) = μ.prod ν :=
    Measure.prod_swap
  have hqmp : Measure.QuasiMeasurePreserving (Prod.swap : β × α → α × β) (ν.prod μ) (μ.prod ν) := by
    refine ⟨measurable_swap, ?_⟩
    rw [hmap]
  exact Measure.ae_ae_of_ae_prod (hqmp.ae h0)

/-- Same, in the form the cocycle actually consumes: two `L²` elements agreeing forces their slices
to agree a.e., for a.e. `y`. -/
theorem ae_ae_slice_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (F G : Lp ℂ 2 (μ.prod ν)) (hFG : F = G) :
    ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, F (x, y) = G (x, y) := by
  subst hFG
  filter_upwards with y
  filter_upwards with x
  rfl

/-! ### The multiplier on the TORUS

`wrapPhi` above is defined on `ℝ × ℝ` by `if p.1 < a`, using an ORDER.  `AddCircle` has no order,
so `wrapPhi` cannot be transported to `L²(T²)` — which is exactly where `M_φ` has to act.  This was
found by reading the target type, not by a failed build: `eLpNorm_wrapPhi_mul` is stated for a
`Measure (ℝ × ℝ)`, so it typechecks in isolation and would have failed only at the bundling step.

The repair is that the wrap region was never really an order comparison.  It is the ARC `[0,a)`,
and an arc is a perfectly good measurable SET on the circle — the fibre of the fundamental-domain
representative, which `Mathlib` supplies as a *measurable equivalence* `AddCircle.measurableEquivIco`.
The twist needs no repair at all: `e^{−2πiω}` is already `1`-periodic, so it descends to the circle
on the nose as `fourier (-1)`. -/

/-- The wrap arc `[0,a)` inside the circle, via the fundamental-domain representative. -/
noncomputable def wrapArc (a : ℝ) : Set UnitAddCircle :=
  {q | ((AddCircle.equivIco (1 : ℝ) 0 q : ℝ)) < a}

/-- The arc is measurable — this is the step the order was doing, done properly. -/
theorem measurableSet_wrapArc (a : ℝ) : MeasurableSet (wrapArc a) := by
  have h : wrapArc a
      = (AddCircle.measurableEquivIco (1 : ℝ) 0) ⁻¹' (Subtype.val ⁻¹' Set.Iio a) := rfl
  rw [h]
  exact (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
    (measurable_subtype_coe measurableSet_Iio)

open scoped Classical in
/-- The torus wrap multiplier — `wrapPhi` with the order replaced by the arc.

`wrapArc` is cut out by a real `<`, which is not decidable, so the branch needs classical
decidability; on `ℝ × ℝ` this never arose because `p.1 < a` had `Real.decidableLT`. -/
noncomputable def torusPhi (a : ℝ) (q : UnitAddCircle × UnitAddCircle) : ℂ :=
  if q.1 ∈ wrapArc a then fourier (-1) q.2 else 1

/-- Unimodular, exactly as `wrapPhi` was — so `M_φ` is still an isometry on the torus. -/
theorem norm_torusPhi (a : ℝ) (q : UnitAddCircle × UnitAddCircle) : ‖torusPhi a q‖ = 1 := by
  unfold torusPhi
  split
  · first
      | exact Circle.norm_coe _
      | simp [fourier]
      | simp
  · simp

/-- And measurable, which `wrapPhi` could not be on the circle for want of the arc. -/
theorem measurable_torusPhi (a : ℝ) : Measurable (torusPhi a) := by
  unfold torusPhi
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurable_fst (measurableSet_wrapArc a)
  · exact ((map_continuous (fourier (-1))).measurable).comp measurable_snd

/-- Hence the torus multiplier is an `eLpNorm` isometry, for ANY measure on `T²`. -/
theorem eLpNorm_torusPhi_mul (a : ℝ) {μ : Measure (UnitAddCircle × UnitAddCircle)}
    (f : UnitAddCircle × UnitAddCircle → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => torusPhi a x * f x) p μ = eLpNorm f p μ :=
  eLpNorm_unimodular_mul (norm_torusPhi a) f p

/-- **`M_φ` on the torus, BUNDLED** — step (1) of the `hcoc` decomposition.

This is an instantiation, not a construction: `multLC` above already bundles multiplication by an
arbitrary measurable unimodular function on an arbitrary measure space, so once `torusPhi` had its
two properties there was nothing left to build.  (Recording that because the previous wake billed
steps (1)–(2) as "real construction work" — the general multiplier was already in this file.) -/
noncomputable def MphiTorus (a : ℝ) (μ : Measure (UnitAddCircle × UnitAddCircle)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  multLC (μ := μ) (measurable_torusPhi a) (norm_torusPhi a)

/-- **`M_φ` is an isometry of `L²(T²)`** — which is what makes `S_a = M_φ ∘ R_a` one. -/
theorem norm_MphiTorus (a : ℝ) {μ : Measure (UnitAddCircle × UnitAddCircle)} (f : Lp ℂ 2 μ) :
    ‖MphiTorus a μ f‖ = ‖f‖ := by
  show ‖multL (μ := μ) (measurable_torusPhi a) (norm_torusPhi a) f‖ = ‖f‖
  exact norm_multL _ _ f

/-! ### `S_a = M_φ ∘ R_a`, assembled — step (2)

`Lp.compMeasurePreserving` is only an `AddMonoidHom`, so I started to build the linear upgrade by
hand; `Lp.compMeasurePreservingₗᵢ` already is it.  Both factors are therefore off-the-shelf, and
the composite needs nothing but composition.

Type-checked against the daemon before building: what was uncertain here was never the mathematics
(a composite of isometries is an isometry) but whether it would ELABORATE at these types — the
torus as a `Prod` of `AddCircle 1`s, the measure as a `prod` of Haars, and `Fact (1 ≤ 2)`.  On a
68-minute build that question is worth asking in 2.5 s first. -/

/-- **`R_a` as a linear isometry of `L²(T²)`.** -/
noncomputable def Ra (a : ℝ) : Lp ℂ 2 T2mu →ₗᵢ[ℂ] Lp ℂ 2 T2mu :=
  Lp.compMeasurePreservingₗᵢ ℂ (rot a) (measurePreserving_rotFst a)

/-- **`S_a = M_φ ∘ R_a`** — the Zak shift on `L²(T²)`, as a continuous linear map. -/
noncomputable def Sa (a : ℝ) : Lp ℂ 2 T2mu →L[ℂ] Lp ℂ 2 T2mu :=
  (MphiTorus a T2mu).comp (Ra a).toContinuousLinearMap

/-- **`S_a` is an isometry** — the twist is unimodular and the rotation preserves Haar, so the
non-lattice `√2` shift costs nothing in norm.  This is what the coefficient-level route could not
deliver: there the covariance became convolution against `1/j`-decaying coefficients. -/
theorem norm_Sa (a : ℝ) (f : Lp ℂ 2 T2mu) : ‖Sa a f‖ = ‖f‖ := by
  show ‖MphiTorus a T2mu ((Ra a).toContinuousLinearMap f)‖ = ‖f‖
  rw [norm_MphiTorus]
  exact (Ra a).norm_map f

/-! ### The POINTWISE `√2` shift identity

This is the mathematical heart of the missing covariance, and it costs almost nothing:
translating the WINDOW is translating the Zak TIME VARIABLE (definitional — the Zak series for
`g(·−a)` at `t` is the series for `g` at `t−a`, up to reassociating `t − n − a`), and
`quasi_shift_eq` then wraps `t−a` back into the fundamental domain at the price of exactly the
factor `wrapPhi`.  Together they say `Z(T_a g) = M_φ ∘ R_a` applied to `Zg` — pointwise.

**No summability, no compact support.**  That matters: `HRTCocycle`'s route to the same fact needs
`hcs` precisely because it rearranges the defining series, and this one never does. -/

/-- Translating the window IS translating the Zak time variable.  Definitional. -/
theorem zak_shift_window (g : ℝ → ℂ) (a t ω : ℝ) :
    ZakPeriodization.zak (fun y => g (y - a)) t ω = ZakPeriodization.zak g (t - a) ω := by
  unfold ZakPeriodization.zak
  refine tsum_congr fun n => ?_
  congr 2
  ring

/-- **THE POINTWISE `√2` SHIFT IDENTITY.**  `Z(T_a g)` is `Zg` rotated in time times the wrap
phase — exactly the action of `S_a = M_φ ∘ R_a`, with NO summability or compact-support
hypothesis. -/
theorem zak_shift_wrap (g : ℝ → ℂ) (a t ω : ℝ) :
    ZakPeriodization.zak (fun y => g (y - a)) t ω
      = wrapPhi a (t, ω) * ZakPeriodization.zak g (shiftRep a t) ω := by
  rw [zak_shift_window g a t ω]
  exact quasi_shift_eq (fun s u => ZakPeriodization.zak g s u)
    (fun s u => ZakPeriodization.zak_quasi_periodic_fst g s u) a t ω

/-! ### Norm consistency of the `√2` shift identity

The remaining gap in the campaign is the OPERATOR identity
`zakSheared hga = Sa a (zakSheared hg)`.  These two lemmas establish its norm half: `Sa` is an
isometry, so the identity is norm-consistent, and — crucially for the density route — BOTH sides
are bounded in the window `g`.  Two bounded operators agreeing on a dense subspace are equal, so
this is the input that will let the identity be proved on compactly supported `g` and extended to
all of `L²`. -/

/-- **`Sa` does not change the norm of a sheared Zak transform.** -/
theorem norm_Sa_zakSheared {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (a : ℝ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖Sa a (HRTZakL2.zakSheared hθ0 hθ1 hg)‖ = ‖HRTZakL2.zakSheared hθ0 hθ1 hg‖ :=
  norm_Sa a _

/-- **The shift identity is norm-consistent.**  If the operator identity holds then the two
transforms have equal norms — the cheap necessary condition, recorded so a future attempt that
breaks it is caught immediately rather than after a long proof. -/
theorem norm_eq_of_shift_identity {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (a : ℝ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hga : MemLp (fun y => g (y - a)) 2 (volume : Measure ℝ))
    (hid : HRTZakL2.zakSheared hθ0 hθ1 hga = Sa a (HRTZakL2.zakSheared hθ0 hθ1 hg)) :
    ‖HRTZakL2.zakSheared hθ0 hθ1 hga‖ = ‖HRTZakL2.zakSheared hθ0 hθ1 hg‖ := by
  rw [hid]; exact norm_Sa a _

end Multiplier

end HRTShift

/-! ## Acceptance gate -/

#print axioms HRTShift.eLpNorm_unimodular_mul
#print axioms HRTShift.memLp_unimodular_mul
#print axioms HRTShift.norm_wrapPhi
#print axioms HRTShift.eLpNorm_wrapPhi_mul
#print axioms HRTShift.quasi_shift_eq
#print axioms HRTShift.shiftRep_mem
#print axioms HRTShift.measurePreserving_rotFst
#print axioms HRTShift.norm_rot_comp
#print axioms HRTShift.lintegral_nnnorm_sq_ne_zero
#print axioms HRTShift.exists_live_slice
#print axioms HRTShift.zakSheared_ne_zero
#print axioms HRTShift.exists_live_fibre
#print axioms HRTShift.eLpNorm_phiAE_mul
#print axioms HRTShift.phiAE_mul_add
#print axioms HRTShift.phiAE_mul_smul
#print axioms HRTShift.norm_multL
#print axioms HRTShift.multLC
#print axioms HRTShift.ae_ae_slice_eq_zero
#print axioms HRTShift.ae_ae_slice_congr
#print axioms HRTShift.measurableSet_wrapArc
#print axioms HRTShift.norm_torusPhi
#print axioms HRTShift.measurable_torusPhi
#print axioms HRTShift.eLpNorm_torusPhi_mul
#print axioms HRTShift.MphiTorus
#print axioms HRTShift.norm_MphiTorus
#print axioms HRTShift.Ra
#print axioms HRTShift.Sa
#print axioms HRTShift.norm_Sa
#print axioms HRTShift.zak_shift_window
#print axioms HRTShift.zak_shift_wrap
#print axioms HRTShift.norm_Sa_zakSheared
#print axioms HRTShift.norm_eq_of_shift_identity
