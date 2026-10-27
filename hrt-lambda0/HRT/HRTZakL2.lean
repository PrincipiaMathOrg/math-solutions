import HRTTransfer

/-!
# Towards an `L²`-valued Zak transform

`HRTReduction.summable_not_implied_by_memLp` proves that the POINTWISE Zak series of
`ZakTransform.zak` cannot serve a general `L²` window: its summability hypothesis reads `g` on the
null set `ℤ`, so it is not even a property of the `L²` class.

`HRTTransfer.W` has no such defect — it is built by INTEGRATION over a fibre,

    W θ g (j,k) = √θ · ∫₀¹ g(s+k)·e^{−2πijθs} ds

and never evaluates `g` at a point.  This file develops `W` as the `L²`-valued replacement.

The first brick is UNITARITY: `∑_{j,k} ‖W θ g (j,k)‖² = ‖g‖²₂`.  It composes the two halves
already proved in `HRTTransfer` — `hasSum_sq_W` (Parseval in `j`, one fibre at a time) and
`hasSum_slice_sq` (the periodization identity `∑_k ∫₀¹‖g(x+k)‖² = ∫_ℝ‖g‖²`).

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace HRTZakL2

open MeasureTheory HRTTransfer AddCircle
open scoped NNReal ENNReal

/-- **`W` is an isometry onto its image in `ℓ²(ℤ²)`.**  The Zak/`W` unitarity, in `HasSum` form:
the total energy of the transform is the `L²` energy of the window. -/
theorem hasSum_W_sq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    HasSum (fun p : ℤ × ℤ => ‖W θ g p.2 p.1‖ ^ 2) (∫ x, ‖g x‖ ^ 2) := by
  have htot := (summable_W_sq hθ0 hθ1 hg).hasSum
  have hfib : ∀ k : ℤ, HasSum (fun j : ℤ => ‖W θ g j k‖ ^ 2)
      (∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2) := fun k => hasSum_sq_W hθ0 hθ1 hg k
  have heq : (∑' p : ℤ × ℤ, ‖W θ g p.2 p.1‖ ^ 2) = ∫ x, ‖g x‖ ^ 2 :=
    (htot.prod_fiberwise hfib).unique (hasSum_slice_sq hg)
  exact heq ▸ htot

/-- **The correct replacement for the refuted pointwise hypothesis:** for almost every `t` in the
fundamental domain, the integer-shift sequence `n ↦ g (t + n)` is SQUARE-summable.

`HRTReduction.summable_not_implied_by_memLp` shows `ℓ¹`-summability-everywhere is not implied by
`MemLp g 2` — indeed is not a property of the `L²` class at all.  `ℓ²`-summability a.e. is, and it
is exactly what the fibre `∑_n g(t+n)·e^{2πinθ}` needs to be an `L²(circle)` function of `θ`. -/
theorem ae_summable_sq_shift {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)),
      Summable (fun k : ℤ => ‖g (t + (k : ℝ))‖ ^ 2) := by
  classical
  set μ := (volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1) with hμ
  have hsum_a : Summable (fun k : ℤ => ∫ t in (0:ℝ)..1, ‖g (t + (k : ℝ))‖ ^ 2) :=
    (hasSum_slice_sq hg).summable
  have hnn : ∀ k : ℤ, 0 ≤ ∫ t in (0:ℝ)..1, ‖g (t + (k : ℝ))‖ ^ 2 := fun k =>
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => by positivity
  have hint : ∀ k : ℤ, Integrable (fun t : ℝ => ‖g (t + (k : ℝ))‖ ^ 2) μ := fun k =>
    ((memLp_two_iff_integrable_sq_norm
      (memLp_shift hg k).aestronglyMeasurable).mp (memLp_shift hg k)).restrict
  have hmeas : ∀ k : ℤ, AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (‖g (t + (k : ℝ))‖ ^ 2)) μ :=
    fun k => (hint k).aemeasurable.ennreal_ofReal
  have hnnsum : Summable (fun k : ℤ => (∫ t in (0:ℝ)..1, ‖g (t + (k : ℝ))‖ ^ 2).toNNReal) :=
    NNReal.summable_coe.mp (hsum_a.congr fun k => (Real.coe_toNNReal _ (hnn k)).symm)
  have hlt : (∫⁻ t, ∑' k : ℤ, ENNReal.ofReal (‖g (t + (k : ℝ))‖ ^ 2) ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have hterm : ∀ k : ℤ,
        (∫⁻ t, ENNReal.ofReal (‖g (t + (k : ℝ))‖ ^ 2) ∂μ)
          = ENNReal.ofReal (∫ t in (0:ℝ)..1, ‖g (t + (k : ℝ))‖ ^ 2) := by
      intro k
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact (ofReal_integral_eq_lintegral_ofReal (hint k)
        (Filter.Eventually.of_forall fun x => by positivity)).symm
    simp_rw [hterm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hnnsum
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hlt] with t ht
  -- `ENNReal.ofReal x` IS `↑x.toNNReal`, so `ht` already bounds the `ℝ≥0` series
  have hne : (∑' k : ℤ, (((‖g (t + (k : ℝ))‖ ^ 2).toNNReal : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := ne_of_lt ht
  exact (NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hne)).congr
    fun k => Real.coe_toNNReal _ (by positivity)

/-- **The fibre sequence is an honest `ℓ²` element, for a.e. `t`.**  This is the form Mathlib's
Fourier machinery consumes: `AddCircle.fourierBasis` is a `ℤ`-indexed Hilbert basis of
`Lp ℂ 2 haarAddCircle`, so `fourierBasis.repr.symm` turns this `Memℓp` witness into a genuine
element of `L²(AddCircle 1)` — the Zak fibre, with no pointwise series anywhere. -/
theorem ae_memℓp_shift {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)),
      Memℓp (fun k : ℤ => g (t + (k : ℝ))) 2 := by
  filter_upwards [ae_summable_sq_shift hg] with t ht
  refine memℓp_gen ?_
  simpa using ht

/-! ### Towards `Zg ∈ L²(T²)`

Mathlib has NO `L²`-product / Bochner-`Lp`-of-`Lp` identification, so the textbook chain
`L²(ℝ) ≅ L²([0,1]) ⊗ ℓ²(ℤ) ≅ L²(T²)` is not available and would have to be built from scratch.
It is not needed.  `Analysis/Fourier/AddCircleMulti.lean` supplies
`UnitAddTorus.mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)` — a `ℤᵈ`-INDEXED Hilbert
basis — so `L²(T²)` is reached from a `ℤ²`-indexed `ℓ²` family by exactly the move that built
`zakFibreL2` one dimension down.  `hasSum_W_sq` already proves the `W` family is that `ℓ²` family.

And this is not a coincidence of shape.  Computing the double Fourier coefficients of
`Zg(t,ω) = ∑_n g(t−n) e^{2πinω}` on `T²`:

    ĉ(j,n) = ∫₀¹∫₀¹ Zg(t,ω) e^{−2πijt} e^{−2πinω} dω dt = ∫₀¹ g(t−n) e^{−2πijt} dt

which is `W 1 g j (−n)`.  **`W` and the Zak transform are the same object**: `W` is the coefficient
sequence, `Zg` the function it synthesises.  `HRTTransfer` built `W` for the RECTANGULAR case,
before the pointwise Zak route was known to be broken, and it turns out to be the replacement —
which is also why `hasSum_W_sq` fell out as a pure composition of two already-proved lemmas rather
than needing new analysis. -/

/-- **The `W` family is `ℓ²` over `ℤ²`.**  Immediate from `hasSum_W_sq`; this is the input
`UnitAddTorus.mFourierBasis.repr.symm` consumes. -/
theorem memℓp_W {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    Memℓp (fun p : ℤ × ℤ => W θ g p.2 p.1) 2 := by
  refine memℓp_gen ?_
  simpa using (hasSum_W_sq hθ0 hθ1 hg).summable

/-! ### The fibre as an honest `L²(AddCircle 1)` element

`fourierBasis` lives at the ROOT namespace — `Analysis/Fourier/AddCircle.lean` wraps it in a
`section FourierL2`, not a `namespace`, so `AddCircle.fourierBasis` is an unknown constant. -/

/-- **The Zak fibre of `g` at `t`**, as a genuine element of `L²(AddCircle 1)`: the function whose
`ℤ`-indexed Fourier coefficients are the integer shifts `k ↦ g (t + k)`.  Total by fiat — off the
a.e. set where `ae_memℓp_shift` applies it is junk (`0`) — which is harmless because every
statement about it is quantified a.e. -/
noncomputable def zakFibreL2 (g : ℝ → ℂ) (t : ℝ) :
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  haveI := Classical.propDecidable (Memℓp (fun k : ℤ => g (t + (k : ℝ))) 2)
  if h : Memℓp (fun k : ℤ => g (t + (k : ℝ))) 2 then
    (fourierBasis (T := 1)).repr.symm ⟨_, h⟩
  else 0

/-- **The defining property:** the fibre's Fourier coefficients ARE the integer shifts. -/
theorem repr_zakFibreL2 {g : ℝ → ℂ} {t : ℝ}
    (h : Memℓp (fun k : ℤ => g (t + (k : ℝ))) 2) (k : ℤ) :
    (fourierBasis (T := 1)).repr (zakFibreL2 g t) k = g (t + (k : ℝ)) := by
  simp only [zakFibreL2, dif_pos h, LinearIsometryEquiv.apply_symm_apply]

/-! ### The shear on the torus DOES preserve Haar

Having established (below) that the shear is unavoidable, here it is.  No
Haar-under-automorphism uniqueness argument is needed: the shear is a SKEW PRODUCT over the
identity, and `MeasurePreserving.skew_product` reduces it to translation-invariance of Haar in the
second coordinate alone. -/

/-- **The shear `(t,ω) ↦ (t, ω+t)` preserves Haar on `T² = AddCircle 1 × AddCircle 1`.** -/
theorem measurePreserving_shear :
    MeasurePreserving
      (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => (p.1, p.2 + p.1))
      ((haarAddCircle : Measure (AddCircle (1 : ℝ))).prod haarAddCircle)
      ((haarAddCircle : Measure (AddCircle (1 : ℝ))).prod haarAddCircle) :=
  (MeasurePreserving.id _).skew_product (by fun_prop)
    (Filter.Eventually.of_forall fun x =>
      (measurePreserving_add_right (haarAddCircle : Measure (AddCircle (1 : ℝ))) x).map_eq)

/-- **The `W` coefficients, reindexed for `mFourierBasis`.**  `mFourierBasis` is indexed by
`d → ℤ`; at `d = Fin 2` that is `Fin 2 → ℤ`, which `piFinTwoEquiv` identifies with `ℤ × ℤ`.
This is the `ℓ²(ℤ²)` witness in the shape `mFourierBasis.repr.symm` consumes. -/
theorem memℓp_W_pi {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    Memℓp (fun i : Fin 2 → ℤ => W θ g (i 1) (i 0)) 2 := by
  refine memℓp_gen ?_
  have h : Summable (fun p : ℤ × ℤ => ‖W θ g p.2 p.1‖ ^ 2) := summable_W_sq hθ0 hθ1 hg
  have h2 := (Equiv.summable_iff (piFinTwoEquiv fun _ : Fin 2 => ℤ)).mpr h
  -- `h2` carries the composition `(·) ∘ (fun f => (f 0, f 1))`, defeq to the goal but not
  -- syntactically equal, so `simpa` alone stalls; `congr` with `rfl` bridges it.
  have h3 : Summable (fun i : Fin 2 → ℤ => ‖W θ g (i 1) (i 0)‖ ^ 2) := h2.congr fun i => rfl
  simpa using h3

/-! ### `Zg` as an honest `L²(T²)` object -/

/-- **The Zak transform of `g`, as a genuine element of `L²(T²)`.**  `UnitAddTorus (Fin 2)` is
`Fin 2 → AddCircle 1`, i.e. the two-torus, and `UnitAddTorus.mFourierBasis` is its `ℤ²`-indexed
Hilbert basis.  Feeding it the `W` coefficients — which `memℓp_W_pi` shows are `ℓ²` — synthesises
`Zg` with no pointwise series anywhere, so the defect `summable_not_implied_by_memLp` proves fatal
to `ZakTransform.zak` cannot arise. -/
-- NO explicit return type: ascribing `Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))`
-- elaborates a DIFFERENT `MeasureSpace.pi` instance than `mFourierBasis` carries (the ascription
-- leaves the `Fintype` argument as a metavariable), and the two `Lp` types then fail to unify.
noncomputable def zakL2 {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :=
  UnitAddTorus.mFourierBasis.repr.symm
    (⟨_, memℓp_W_pi hθ0 hθ1 hg⟩ : lp (fun _ : Fin 2 → ℤ => ℂ) 2)

/-- **The defining property of `zakL2`:** its `ℤ²`-indexed Fourier coefficients ARE the `W`
coefficients. -/
theorem repr_zakL2 {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (i : Fin 2 → ℤ) :
    UnitAddTorus.mFourierBasis.repr (zakL2 hθ0 hθ1 hg) i = W θ g (i 1) (i 0) := by
  rw [zakL2, LinearIsometryEquiv.apply_symm_apply]

/-! ### From the pi-torus to a binary product, so Fubini applies

`UnitAddTorus (Fin 2)` is a PI type (`Fin 2 → UnitAddCircle`), but every Fubini/slicing lemma in
Mathlib is stated for a BINARY product `α × β`.  `volume_preserving_piFinTwo` is the bridge, and it
is measure-preserving for `volume` on both sides, so nothing is lost crossing it. -/

/-- **The two-torus, as a binary product.** -/
theorem volumePreserving_torusProd :
    MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
      (volume : Measure (UnitAddTorus (Fin 2)))
      (volume : Measure (UnitAddCircle × UnitAddCircle)) :=
  volume_preserving_piFinTwo _

/-- **On the unit circle, `volume` IS Haar.**  `AddCircle.volume_eq_smul_haarAddCircle` scales by
the period, which is `1` here. -/
theorem volume_eq_haar_circle :
    (volume : Measure UnitAddCircle) = (haarAddCircle : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- **…so on the torus-as-a-product, `volume` is the Haar product.**  This is the measure
`measurePreserving_shear` is stated for, so it composes with `volumePreserving_torusProd`. -/
theorem volume_prod_eq_haar_prod :
    (volume : Measure (UnitAddCircle × UnitAddCircle))
      = (haarAddCircle : Measure UnitAddCircle).prod haarAddCircle := by
  rw [Measure.volume_eq_prod, volume_eq_haar_circle]

/-- **The torus, sheared, in one measure-preserving map.**  Composes the pi-to-binary bridge with
the shear: `Zg` lives on `UnitAddTorus (Fin 2)`, Fubini wants a binary product, and the θ-slicing
wants the sheared coordinates `(t, ω) ↦ (t, ω + t)`.  This is all three at once, so a Fubini
argument downstream can work in `haarAddCircle.prod haarAddCircle` directly. -/
theorem measurePreserving_torusShear :
    MeasurePreserving
      ((fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 + p.1)) ∘
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)))
      (volume : Measure (UnitAddTorus (Fin 2)))
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
      (volume : Measure (UnitAddTorus (Fin 2)))
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle) := by
    rw [← volume_prod_eq_haar_prod]
    exact volumePreserving_torusProd
  exact measurePreserving_shear.comp h1

/-- **The inverse shear.**  `Lp.compMeasurePreserving` is CONTRAVARIANT — from `f : α → β`
measure-preserving it builds `Lp β → Lp α` — so pushing `zakL2` (which lives on the torus) into
sheared product coordinates needs the map running product → torus, i.e. `(t,ω) ↦ (t, ω − t)`.
Same skew-product argument as `measurePreserving_shear`. -/
theorem measurePreserving_shearInv :
    MeasurePreserving
      (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 - p.1))
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle)
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle) :=
  (MeasurePreserving.id _).skew_product
    (g := fun (x y : UnitAddCircle) => y - x) (by fun_prop)
    (Filter.Eventually.of_forall fun x => by
      simpa [sub_eq_add_neg] using
        (measurePreserving_add_right (haarAddCircle : Measure UnitAddCircle) (-x)).map_eq)

/-- **Product → torus, sheared, measure-preserving.**  The inverse of
`measurePreserving_torusShear`, in the direction `Lp.compMeasurePreserving` consumes. -/
theorem measurePreserving_prodToTorus :
    MeasurePreserving
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm ∘
        (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 - p.1)))
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle)
      (volume : Measure (UnitAddTorus (Fin 2))) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle)
      (volume : Measure (UnitAddTorus (Fin 2))) := by
    rw [← volume_prod_eq_haar_prod]
    exact (volumePreserving_torusProd).symm _
  exact h1.comp measurePreserving_shearInv

/-! ### The instance blocker, SOLVED — name the measure explicitly

The obstruction was that `zakL2`'s ambient measure comes from a LOCAL instance inside
`AddCircleMulti` and is not defeq to anything this file can write with `volume`.  The way through
is not to fight instance resolution but to BYPASS it: `zakL2`'s measure is literally
`Measure.pi (fun _ : Fin 2 => haarAddCircle)`, which is an explicit `Measure` term needing no
instance at all.  (Verified: ascribing that type to `zakL2` typechecks.) -/

/-- The torus `volume` IS the pi-measure of Haar, because on the unit circle `volume = haar`. -/
theorem torusVolume_eq_piHaar :
    (volume : Measure (UnitAddTorus (Fin 2)))
      = Measure.pi (fun _ : Fin 2 => (haarAddCircle : Measure UnitAddCircle)) := by
  rw [← volume_eq_haar_circle]
  first
    | rfl
    | exact Measure.volume_pi

/-- **Product → torus, landing in the measure `zakL2` actually lives on.** -/
theorem measurePreserving_prodToTorusHaar :
    MeasurePreserving
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm ∘
        (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 - p.1)))
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle)
      (Measure.pi (fun _ : Fin 2 => (haarAddCircle : Measure UnitAddCircle))) := by
  rw [← torusVolume_eq_piHaar]
  exact measurePreserving_prodToTorus

/-- **`Zg`, in sheared product coordinates.**  The composition the instance mismatch blocked. -/
noncomputable def zakSheared {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :=
  Lp.compMeasurePreserving _ measurePreserving_prodToTorusHaar (zakL2 hθ0 hθ1 hg)

/-! ### (Former blocker — SOLVED, kept for the lesson)

`zakSheared` was blocked for five wakes because `mFourierBasis`'s type is elaborated against a
LOCAL instance (`AddCircleMulti.lean:30`, `local instance : MeasureSpace UnitAddCircle :=
⟨AddCircle.haarAddCircle⟩`) which is NOT defeq to the global `AddCircle.measureSpace 1` — verified
by a failing `rfl` probe, after three earlier notes had asserted defeq without checking.

Every failed attempt tried to make instance resolution agree (ascription, `attribute [instance
2000]`, `by exact`, rephrasing).  The fix was to stop invoking resolution: name the measure as the
explicit term `Measure.pi (fun _ : Fin 2 => haarAddCircle)`.  See `torusVolume_eq_piHaar`. -/

/-- **A.e. slice of an `L²` function on a product.**  For a.e. `θ`, the `t`-slice of an `L²`
function on the torus is itself `L²` — the Fubini step the θ-slicing needs.

Both factors are `haarAddCircle`, a PROBABILITY measure, so `L² ⊆ L¹` and `Integrable.prod_left_ae`
applies directly; it delivers a.e. slice MEASURABILITY for free, which is the part a bare
`‖f‖²`-argument does not give. -/
theorem ae_memLp_slice {f : UnitAddCircle × UnitAddCircle → ℂ}
    (hf : MemLp f 2 ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle)) :
    ∀ᵐ y ∂(haarAddCircle : Measure UnitAddCircle),
      MemLp (fun x => f (x, y)) 2 (haarAddCircle : Measure UnitAddCircle) := by
  have hint : Integrable f ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle) :=
    hf.integrable (by norm_num)
  have hsq : Integrable (fun p => ‖f p‖ ^ 2)
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  filter_upwards [hint.prod_left_ae, hsq.prod_left_ae] with y h1 h2
  exact (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).mpr h2

/-- **The `Λ₀` fibre family, as `L²` functions of `t`.**  Applying `ae_memLp_slice` to
`zakSheared`: for a.e. `θ`, the map `t ↦ Zg(t, t+θ)` is a genuine `L²(circle)` function.

This is the object `HRTMaster.fibreCircle` names and `BirkhoffErgodic` consumes — reached WITHOUT
the pointwise Zak series whose summability hypothesis
`HRTReduction.summable_not_implied_by_memLp` proves is not implied by `MemLp`. -/
theorem ae_memLp_zakSlice {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ∀ᵐ y ∂(haarAddCircle : Measure UnitAddCircle),
      MemLp (fun x => (zakSheared hθ0 hθ1 hg) (x, y)) 2
        (haarAddCircle : Measure UnitAddCircle) :=
  ae_memLp_slice (Lp.memLp _)

/-- **The fibre modulus is genuinely MEASURABLE**, not merely a.e.-measurable.

`BirkhoffErgodic.integral_log_eq_of_modulus_cocycle` demands `Measurable G`, so an
`AEStronglyMeasurable` witness is not enough.  It is available for free: an `Lp` element IS an
`AEEqFun`, whose coercion is strongly measurable by construction, and a slice of a measurable
function is measurable because `x ↦ (x, y)` is. -/
theorem measurable_zakSliceNorm {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (y : UnitAddCircle) :
    Measurable (fun x : UnitAddCircle => ‖(zakSheared hθ0 hθ1 hg) (x, y)‖) := by
  have hm : Measurable (fun p : UnitAddCircle × UnitAddCircle =>
      (zakSheared hθ0 hθ1 hg) p) :=
    (zakSheared hθ0 hθ1 hg).1.stronglyMeasurable.measurable
  have hsec : Measurable (fun x : UnitAddCircle => (x, y)) := by
    first
      | exact measurable_id.prodMk measurable_const
      | exact measurable_id.prod_mk measurable_const
      | fun_prop
  exact (hm.comp hsec).norm

/-! ### `W` is linear — so a dependence becomes a coefficient relation

The cocycle comes from applying the Zak transform to a `Λ₀` dependence.  At the coefficient level
that is `HRTTransfer.W_rep` (the intertwining relation) plus LINEARITY of `W`, which is what turns
`∑ cᵢ πᵢ g = 0` into a relation among the `W` coefficients.

Kept here rather than in `HRTTransfer` deliberately: editing that module rebuilds the whole
downstream chain, and these are only needed for the Zak application. -/

/-- `W` is additive in the window. -/
theorem W_add (θ : ℝ) (g₁ g₂ : ℝ → ℂ) (j k : ℤ)
    (h₁ : IntervalIntegrable
      (fun s : ℝ => g₁ (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume 0 1)
    (h₂ : IntervalIntegrable
      (fun s : ℝ => g₂ (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume 0 1) :
    W θ (fun t => g₁ t + g₂ t) j k = W θ g₁ j k + W θ g₂ j k := by
  unfold W
  rw [← mul_add, ← intervalIntegral.integral_add h₁ h₂]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- `W` is homogeneous in the window. -/
theorem W_smul (θ : ℝ) (c : ℂ) (g : ℝ → ℂ) (j k : ℤ) :
    W θ (fun t => c * g t) j k = c * W θ g j k := by
  unfold W
  have hpt : ∀ s : ℝ, c * g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))
      = c * (g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) := fun s => by ring
  rw [intervalIntegral.integral_congr (g := fun s : ℝ =>
      c * (g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s)))) (fun s _ => hpt s),
    intervalIntegral.integral_const_mul]
  ring

/-- **`W`'s integrand is interval-integrable**, which is what makes `W_add` usable at an `L²`
window.  Written directly rather than importing `HRTRectangular.intervalIntegrable_rep`: that
module sits ABOVE this one in the dependency graph, and importing upward to reach one lemma pays
the whole transitive cost (the mistake this campaign's module-layering rule records). -/
theorem intervalIntegrable_W_integrand {θ : ℝ} {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (j k : ℤ) :
    IntervalIntegrable
      (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume 0 1 := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp
  have hbound : ∀ s : ℝ,
      ‖g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))‖ ≤ ‖g (s + (k : ℝ))‖ := by
    intro s
    rw [norm_mul, HRTTransfer.norm_ee, mul_one]
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s)))
      (volume : Measure ℝ) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hgm.comp (by fun_prop)).aestronglyMeasurable
    · refine Measurable.aestronglyMeasurable ?_
      unfold HRTTransfer.ee
      fun_prop
  have hmem : MemLp (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) 2
      (volume : Measure ℝ) :=
    MemLp.of_le (HRTTransfer.memLp_shift hg k) hmeas (Filter.Eventually.of_forall hbound)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact (hmem.restrict _).integrable (by norm_num)

/-! ### Rotation of the time coordinate — the `√2` shift on the Zak side

The three LATTICE shifts of `Λ₀` — `(0,0)`, `(1,0)`, `(0,1)` — act on `W`'s coefficients by index
shift and a character (`HRTTransfer.W_rep`), and assemble into the symbol
`P_θ(t) = A + B e^{−2πi(t+θ)} + C e^{2πit}`.

The `(√2,√2)` shift does NOT: `√2` is irrational, so
`W θ (T_√2 g) j k = √θ ∫_{−√2}^{1−√2} …` runs over a translated interval that no index shift
repairs.  That is not an accident of the coefficient picture — it is the whole difficulty of the
problem.  On the Zak side the same shift is simply a TRANSLATION of the time coordinate, and it is
that translation which becomes the Birkhoff rotation `R : t ↦ t − √2`.

So the cocycle needs the time-rotation as a measure-preserving map of the torus. -/

/-- **Rotation of the first (time) coordinate preserves Haar on the torus.** -/
theorem measurePreserving_rotFst (a : UnitAddCircle) :
    MeasurePreserving (fun p : UnitAddCircle × UnitAddCircle => (p.1 - a, p.2))
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle)
      ((haarAddCircle : Measure UnitAddCircle).prod haarAddCircle) := by
  have h1 : MeasurePreserving (fun x : UnitAddCircle => x - a)
      (haarAddCircle : Measure UnitAddCircle) (haarAddCircle : Measure UnitAddCircle) := by
    simpa [sub_eq_add_neg] using
      measurePreserving_add_right (haarAddCircle : Measure UnitAddCircle) (-a)
  exact h1.prod (MeasurePreserving.id _)

/-! ### `zakL2` is an isometry — the continuity a density argument needs

The covariance `Z(T_a g) = Zg ∘ (t ↦ t−a)` is trivial for the pointwise Zak series but CANNOT be
proved coefficient-wise here.  Directly:

    W θ (T_a g) j k = e^{−2πijθa} · √θ ∫_{−a}^{1−a} g(u+k) e^{−2πijθu} du

and for irrational `a` that interval is not `[0,1]`.  Term by term the identity is false; it is only
the SUMMED family `∑_n g(u−n)e^{2πinω}` that is quasi-periodic, so translation by an irrational
spreads across the `k` index instead of acting as a character on each coefficient.

The standard route is therefore density plus continuity: prove the covariance on a class where the
pointwise series converges, then extend.  Continuity is what this brick supplies. -/

/-! ### Removing compact support: the density argument that DOES work

Two different extension problems have been conflated in this campaign's notes, and they have
opposite answers.  Recording the distinction because it redirects the remaining work.

**Does NOT work — extending linear independence.**  `HRT` for compactly supported windows does not
imply `HRT` for `L²`.  Linear independence is not a closed condition: approximating a general `g`
by compactly supported `gₙ` says nothing, since a dependence for `g` need not be inherited by any
`gₙ`.  No amount of density fixes this, and it is a genuine obstruction.

**DOES work — extending the covariance identities.**  But the argument never needs the first thing.
It takes a dependence for a GIVEN, arbitrary `g` and pushes it through the Zak transform.  The only
place compact support enters is `HRTCocycle.summable_s1`–`s4`: they make the POINTWISE Zak series
converge so `zak_dep_zero` applies.  Those are identities between BOUNDED OPERATORS on `L²`
(`g ↦ Zg`, precomposition with a shift, multiplication by a character), and bounded operators
agreeing on a dense subspace agree everywhere.  That is the standard, valid density argument.

So compact support is a crutch for pointwise definedness, not a real hypothesis, and `zakL2` — an
`L²` element whose coefficients are the `W`'s, with no summability anywhere — is what removes it.
The route is to redo the cocycle on `zakL2` with a.e. statements, not to extend the dense result.

This also explains why `hGnz` had to become `θ`-dependent: a slice of an `L²` function is defined
only for a.e. `θ`, so choosing a good `θ` is forced by the same move.  The two remaining gaps are
one gap.

Linearity is the first requirement, since a dependence is a linear relation. -/

/-- **`zakL2` depends only on the a.e. class of the window.**

This is the prerequisite for packaging `zakL2` as a continuous linear map on `Lp ℂ 2 volume`,
which is what the density engine needs: `HRTDensity.ae_norm_eq_of_dense` takes its two arguments
as `E →L[ℂ] Lp ℂ 2 μ`, and `zakL2` eats a raw function plus a `MemLp` proof, so it does not
descend to `Lp` until this is known.  `Sa` is already a bundled `→L[ℂ]`; this is the other half.

True because `W` is defined by an INTEGRAL: a.e.-equal integrands integrate equally, once the a.e.
equality is transported through the translation `s ↦ s + k`, which preserves `volume` on `ℝ`. -/
theorem zakL2_congr {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g₁ g₂ : ℝ → ℂ}
    (h₁ : MemLp g₁ 2 (volume : Measure ℝ)) (h₂ : MemLp g₂ 2 (volume : Measure ℝ))
    (hae : g₁ =ᵐ[volume] g₂) :
    zakL2 hθ0 hθ1 h₁ = zakL2 hθ0 hθ1 h₂ := by
  refine UnitAddTorus.mFourierBasis.repr.injective ?_
  ext i
  rw [repr_zakL2 hθ0 hθ1 h₁ i, repr_zakL2 hθ0 hθ1 h₂ i]
  unfold HRTTransfer.W
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hshift : (fun s : ℝ => g₁ (s + ((i 0 : ℤ) : ℝ)))
      =ᵐ[volume] fun s : ℝ => g₂ (s + ((i 0 : ℤ) : ℝ)) := by
    have hmap : Measure.map (fun s : ℝ => s + ((i 0 : ℤ) : ℝ)) (volume : Measure ℝ) = volume :=
      map_add_right_eq_self volume _
    exact ae_eq_comp (measurable_add_const _).aemeasurable (by rw [hmap]; exact hae)
  filter_upwards [hshift] with s hs _
  rw [hs]

/-- **`zakL2` is additive.**  Immediate from `W_add` through the basis representation — the
`MemLp` proofs are irrelevant to the value, so the three may be supplied independently. -/
theorem zakL2_add {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g₁ g₂ : ℝ → ℂ}
    (hm₁ : Measurable g₁) (hm₂ : Measurable g₂)
    (h₁ : MemLp g₁ 2 (volume : Measure ℝ)) (h₂ : MemLp g₂ 2 (volume : Measure ℝ))
    (h₁₂ : MemLp (fun t => g₁ t + g₂ t) 2 (volume : Measure ℝ)) :
    zakL2 hθ0 hθ1 h₁₂ = zakL2 hθ0 hθ1 h₁ + zakL2 hθ0 hθ1 h₂ := by
  refine UnitAddTorus.mFourierBasis.repr.injective ?_
  ext i
  rw [map_add]
  rw [repr_zakL2 hθ0 hθ1 h₁₂ i]
  have e₁ := repr_zakL2 hθ0 hθ1 h₁ i
  have e₂ := repr_zakL2 hθ0 hθ1 h₂ i
  simp only [lp.coeFn_add, Pi.add_apply, e₁, e₂]
  exact W_add θ g₁ g₂ (i 1) (i 0)
    (intervalIntegrable_W_integrand hm₁ h₁ _ _)
    (intervalIntegrable_W_integrand hm₂ h₂ _ _)

/-- **`zakL2` is homogeneous.**  The scalar passes through `W_smul`. -/
theorem zakL2_smul {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hcg : MemLp (fun t => c * g t) 2 (volume : Measure ℝ)) :
    zakL2 hθ0 hθ1 hcg = c • zakL2 hθ0 hθ1 hg := by
  refine UnitAddTorus.mFourierBasis.repr.injective ?_
  ext i
  rw [map_smul]
  rw [repr_zakL2 hθ0 hθ1 hcg i]
  have e := repr_zakL2 hθ0 hθ1 hg i
  simp only [lp.coeFn_smul, Pi.smul_apply, e, smul_eq_mul]
  exact W_smul θ c g (i 1) (i 0)

/-! ### Which covariances are free, and which one is the crux

`Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}` splits sharply under the `L²` transform.

**Three points are free.**  `(0,0)`, `(1,0)`, `(0,1)` are LATTICE points, and `HRTTransfer.W_rep`
already computes the transfer of a lattice time–frequency shift as a twisted REINDEX of the
coefficient array — with no hypotheses at all, since it is an identity of integrals.  So for these
three the `L²` covariance costs nothing beyond `repr_zakL2`; no density, no summability, no
continuity.  That is what the next lemma records.

**One point is the crux.**  `(√2,√2)` is not a lattice point, and a non-integer shift is NOT a
reindex of the `W` array — it mixes the coefficients.  In the pointwise picture
`ZakTransform.zak_covariance` absorbed this into `Zg(t−a, ω)`, a TRANSLATION of the argument rather
than a permutation of coefficients.  On the `L²` side that is precomposition with a
measure-preserving translation of the torus, which is exactly what `Lp.compMeasurePreserving` and
the `measurePreserving_*` family in this file were built to supply.

So the remaining work is concentrated in one place: the `√2` translation as an operator identity.
That is the honest statement of what stands between this development and a compact-support-free
result — not a diffuse "density problem" across the whole argument. -/

/-- **Lattice covariance for `zakL2`, hypothesis-free in the transform.**  A lattice
time–frequency shift acts on the Zak coefficients by a twisted reindex.  Covers three of the four
`Λ₀` points; the `√2` point is not of this form. -/
theorem repr_zakL2_rep {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (m n : ℤ) {g : ℝ → ℂ}
    (hrg : MemLp (HRTTransfer.rep θ m n g) 2 (volume : Measure ℝ)) (i : Fin 2 → ℤ) :
    UnitAddTorus.mFourierBasis.repr (zakL2 hθ0 hθ1 hrg) i
      = HRTTransfer.ee ((n : ℝ) * θ * ((i 0 : ℤ) : ℝ)) * W θ g (i 1 - n) (i 0 - m) := by
  rw [repr_zakL2 hθ0 hθ1 hrg i]
  exact HRTTransfer.W_rep θ m n g (i 1) (i 0)

/-! ### The `√2` translation: why it MIXES, and the first half of the computation

A non-integer shift is not a reindex, and it is worth recording exactly where that comes from,
because it is a real phenomenon rather than a bookkeeping nuisance.

`Zg(t+1, ω) = e^{2πiω}·Zg(t, ω)` — the Zak transform is QUASI-periodic in `t`, not periodic.  So
the object living on `T²` is a section of a line bundle, and translating `t` past the edge of the
fundamental domain picks up the twist `e^{2πiω}` on the part that wraps.  A lattice shift never
wraps a fractional amount, which is why `W_rep` is free; an irrational shift always does.

Concretely, substituting `u = s − a` in the defining integral,

    ∫₀¹ g(s+k−a)·e(−jθs) ds = e(−jθa)·∫_{−a}^{1−a} g(u+k)·e(−jθu) du

and `[−a, 1−a]` splits at `0` into a piece contributing to index `k` and a piece which — after the
unit shift `g(u+k) = g((u−1)+(k+1))` — contributes to index `k−1`.  THAT is the mixing: the shifted
coefficient is not any single `W θ g j k'` but a combination of two PARTIAL integrals.

This lemma is the substitution, which is exact and hypothesis-free.  The splitting is separate. -/

/-- **The real-shift substitution.**  Translating the window by `a` pulls out the phase `e(−jθa)`
and moves the integration window from `[0,1]` to `[−a, 1−a]`.  No hypotheses: an identity of
interval integrals. -/
theorem W_shift_real (θ a : ℝ) (g : ℝ → ℂ) (j k : ℤ) :
    W θ (fun y => g (y - a)) j k
      = HRTTransfer.ee (-((j : ℝ) * θ * a)) * ((Real.sqrt θ : ℂ) *
          ∫ u in (-a)..(1 - a), g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u))) := by
  unfold W
  have hpt : ∀ s : ℝ,
      g (s + (k : ℝ) - a) * HRTTransfer.ee (-((j : ℝ) * θ * s))
        = (fun u : ℝ => HRTTransfer.ee (-((j : ℝ) * θ * a))
            * (g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)))) (s - a) := by
    intro s
    simp only
    have harg : s - a + (k : ℝ) = s + (k : ℝ) - a := by ring
    -- the two characters merge only after the `g` factor is moved out of the way
    have hee : HRTTransfer.ee (-((j : ℝ) * θ * a))
        * HRTTransfer.ee (-((j : ℝ) * θ * (s - a)))
        = HRTTransfer.ee (-((j : ℝ) * θ * s)) := by
      rw [← HRTTransfer.ee_add]
      congr 1
      ring
    rw [harg]
    calc g (s + (k : ℝ) - a) * HRTTransfer.ee (-((j : ℝ) * θ * s))
        = g (s + (k : ℝ) - a) * (HRTTransfer.ee (-((j : ℝ) * θ * a))
            * HRTTransfer.ee (-((j : ℝ) * θ * (s - a)))) := by rw [hee]
      _ = _ := by ring
  -- Worked backwards so that `integral_congr` is applied to a goal where BOTH integrands are
  -- already fixed: its `f`/`g` are higher-order implicits and cannot be inferred from a
  -- pointwise proof alone.
  have key : (∫ s in (0:ℝ)..1, g (s + (k : ℝ) - a) * HRTTransfer.ee (-((j : ℝ) * θ * s)))
      = HRTTransfer.ee (-((j : ℝ) * θ * a))
        * ∫ u in (-a)..(1 - a), g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)) := by
    rw [← intervalIntegral.integral_const_mul,
      show (-a : ℝ) = 0 - a from (zero_sub a).symm,
      ← intervalIntegral.integral_comp_sub_right
        (fun u : ℝ => HRTTransfer.ee (-((j : ℝ) * θ * a))
          * (g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)))) a]
    exact intervalIntegral.integral_congr (fun s _ => hpt s)
  rw [key]
  ring

/-- **The wrap piece IS a `k−1` contribution.**  The part of `[−a, 1−a]` lying below `0` is, after
the unit substitution `u = v − 1`, an integral over `[1−a, 1]` of the window shifted to index
`k − 1`, carrying the phase `e(jθ)`.

This is the mixing, made explicit and hypothesis-free: a non-lattice shift sends the coefficient at
`k` to a combination of `k` and `k−1`, which is why `W_rep`'s reindex has no analogue here. -/
theorem integral_wrap_piece (θ a : ℝ) (g : ℝ → ℂ) (j k : ℤ) :
    (∫ u in (-a)..(0:ℝ), g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)))
      = HRTTransfer.ee ((j : ℝ) * θ)
        * ∫ v in (1 - a)..(1:ℝ),
            g (v + ((k - 1 : ℤ) : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * v)) := by
  -- Every step forwards and in explicit (beta-reduced) form.  A backwards `rw` through
  -- `integral_const_mul` leaves `r` and `f` unconstrained and sends elaboration into a
  -- higher-order search that does not terminate in reasonable time.
  have hsub : (∫ x in (1 - a)..(1:ℝ),
        g (x - 1 + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * (x - 1))))
      = ∫ x in (-a)..(0:ℝ), g (x + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * x)) := by
    have h := intervalIntegral.integral_comp_sub_right
      (a := 1 - a) (b := (1:ℝ))
      (fun u : ℝ => g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u))) (1:ℝ)
    have hb1 : (1 : ℝ) - a - 1 = -a := by ring
    have hb2 : (1 : ℝ) - 1 = 0 := by ring
    rw [hb1, hb2] at h
    exact h
  have hcongr : (∫ x in (1 - a)..(1:ℝ),
        g (x - 1 + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * (x - 1))))
      = ∫ x in (1 - a)..(1:ℝ), HRTTransfer.ee ((j : ℝ) * θ)
          * (g (x + ((k - 1 : ℤ) : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * x))) := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    -- `EqOn` unfolds to `f x = g x` with BOTH sides beta-redexes, and `rw` matches syntactically
    -- so it cannot see through them.  `W_shift_real` above has this `simp only`; dropping it here
    -- is what made the daemon probe report `sorryAx`.
    simp only
    have harg : x - 1 + (k : ℝ) = x + ((k - 1 : ℤ) : ℝ) := by push_cast; ring
    have hee : HRTTransfer.ee (-((j : ℝ) * θ * (x - 1)))
        = HRTTransfer.ee ((j : ℝ) * θ) * HRTTransfer.ee (-((j : ℝ) * θ * x)) := by
      rw [← HRTTransfer.ee_add]
      congr 1
      ring
    rw [harg, hee]
    ring
  have hconst : (∫ x in (1 - a)..(1:ℝ), HRTTransfer.ee ((j : ℝ) * θ)
        * (g (x + ((k - 1 : ℤ) : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * x))))
      = HRTTransfer.ee ((j : ℝ) * θ)
        * ∫ x in (1 - a)..(1:ℝ),
            g (x + ((k - 1 : ℤ) : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * x)) := by
    rw [intervalIntegral.integral_const_mul]
  rw [← hsub, hcongr, hconst]

/-- **`zakL2` is norm-preserving.**  `mFourierBasis.repr` is a `LinearIsometryEquiv`, so the Zak
transform inherits its norm from the `ℓ²(ℤ²)` coefficient sequence — and `hasSum_W_sq` identifies
that with `‖g‖₂`.  This is the "Zak unitarity" appealed to when ruling out a conull zero set in
`HRTReduction.ae_ne_zero_of_cocycle`, now stated for `zakL2` itself. -/
theorem norm_zakL2 {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖zakL2 hθ0 hθ1 hg‖
      = ‖(⟨_, memℓp_W_pi hθ0 hθ1 hg⟩ : lp (fun _ : Fin 2 → ℤ => ℂ) 2)‖ := by
  rw [zakL2]
  exact LinearIsometryEquiv.norm_map _ _

/-- **`zakL2` is injective on nonzero windows.**  If `Zg = 0` then every `W` coefficient vanishes
(`repr` is a linear isometry, so it sends `0` to `0`), and `HRTTransfer.ae_eq_zero_of_W_eq_zero`
then forces `g = 0` a.e.

This is the input `hGnz` needs — `ae_ne_zero_of_cocycle` rules out a CONULL zero set only once the
fibre is known not to vanish identically, and that is exactly Zak unitarity applied to a nonzero
window. -/
theorem zakL2_ne_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0)) :
    zakL2 hθ0 hθ1 hg ≠ 0 := by
  intro h0
  refine hgne (HRTTransfer.ae_eq_zero_of_W_eq_zero hθ0 hθ1 hg ?_)
  intro j k
  have h := repr_zakL2 hθ0 hθ1 hg ![k, j]
  rw [h0] at h
  simpa using h.symm

/-! ### The dense class: compactly supported windows

`norm_zakL2` gives the continuity half of the density argument.  This is the entry point to the
other half.  For a COMPACTLY SUPPORTED window the integer-shift family is FINITELY supported —
only finitely many `n` can put `t − n` inside a bounded support — so the pointwise Zak series is a
finite sum and every classical identity, including the translation covariance, holds outright.
That is the class on which the covariance can be proved before extending by continuity. -/

/-- **For a compactly supported window the shift family is finitely supported.** -/
theorem finite_shift_support_of_compactSupport {g : ℝ → ℂ} (hcs : HasCompactSupport g) (t : ℝ) :
    {n : ℤ | g (t - (n : ℝ)) ≠ 0}.Finite := by
  obtain ⟨M, hM⟩ := (hcs.isCompact.isBounded).subset_closedBall 0
  have hsub : {n : ℤ | g (t - (n : ℝ)) ≠ 0} ⊆ {n : ℤ | |t - (n : ℝ)| ≤ M} := by
    intro n hn
    have hmem : t - (n : ℝ) ∈ Metric.closedBall (0 : ℝ) M :=
      hM (subset_tsupport _ hn)
    simpa [Real.dist_eq] using hmem
  refine Set.Finite.subset (Set.finite_Icc ⌈t - M⌉ ⌊t + M⌋) ?_
  intro n hn
  have h : |t - (n : ℝ)| ≤ M := hsub hn
  rw [abs_le] at h
  constructor
  · exact Int.ceil_le.mpr (by linarith [h.2])
  · exact Int.le_floor.mpr (by linarith [h.1])

/-- Hence the shift family is summable — the pointwise Zak series converges absolutely. -/
theorem summable_shift_of_compactSupport {g : ℝ → ℂ} (hcs : HasCompactSupport g) (t : ℝ) :
    Summable (fun n : ℤ => ‖g (t - (n : ℝ))‖) := by
  refine summable_of_hasFiniteSupport ?_
  refine Set.Finite.subset (finite_shift_support_of_compactSupport hcs t) ?_
  intro n hn
  simpa using hn

/-! ### What actually costs summability — it is ADDITIVITY, not covariance

`ZakTransform.zak_covariance` is already proved and carries NO summability hypothesis:

    zak (fun y => e^{2πiby} g(y−x)) t ω = e^{2πibt} · zak g (t−x) (ω−b)

for ANY real `x`, `√2` included — it goes through `tsum_congr` and `tsum_mul_left`, both of which
hold unconditionally (Mathlib's `tsum` is `0` off summability, and both sides degenerate together).

So the covariance was never the thing needing density.  What needs it is ADDITIVITY: turning a
DEPENDENCE `∑ cᵢ πᵢ g = 0` into a relation among Zak transforms requires `∑(a+b) = ∑a + ∑b`, and
`ZakTransform.zak_add` takes exactly those summability hypotheses.  This lemma supplies them on the
compactly supported class. -/

/-- **The Zak series converges absolutely for a compactly supported window.**  Supplies the
summability hypotheses of `ZakTransform.zak_add`; the character has modulus one, so it reduces to
`summable_shift_of_compactSupport`. -/
theorem summable_zak_of_compactSupport {g : ℝ → ℂ} (hcs : HasCompactSupport g) (t ω : ℝ) :
    Summable (fun n : ℤ =>
      g (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) := by
  refine Summable.of_norm ?_
  refine (summable_shift_of_compactSupport hcs t).congr fun n => ?_
  rw [norm_mul, Complex.norm_exp]
  simp

/-- **General summability of a Zak term.**  `ZakTransform.zak_dep_zero` takes four summability
hypotheses, one per `Λ₀` point, each of the shape "constant × unimodular factor × shifted window ×
character".  This covers all four at once: the character and the unimodular factor drop out under
the norm, leaving the shifted window, whose summability is `summable_shift_of_compactSupport` at
the shifted point. -/
theorem summable_zak_term {g : ℝ → ℂ} (hcs : HasCompactSupport g) (c : ℂ) (d t ω : ℝ)
    (u : ℤ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) :
    Summable (fun n : ℤ => c * (u n * g (t - (n : ℝ) - d))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_shift_of_compactSupport hcs (t - d)).mul_left ‖c‖)
  have harg : t - (n : ℝ) - d = (t - d) - (n : ℝ) := by ring
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, harg]
  have h1 : ‖u n‖ * ‖g (t - d - (n : ℝ))‖ ≤ ‖g (t - d - (n : ℝ))‖ := by
    nlinarith [hu n, norm_nonneg (g (t - d - (n : ℝ))), norm_nonneg (u n)]
  have h2 : Real.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)).re = 1 := by
    simp
  rw [h2, mul_one]
  nlinarith [h1, norm_nonneg c, norm_nonneg (g (t - d - (n : ℝ)))]

/-! ## RETRACTION — the torus shear IS needed, and this file does not avoid it

An earlier revision of this docstring (and commits fa2fb96a / 3b50800c) claimed the shear
`(t,ω) ↦ (t,ω+t)` could be avoided by "fibring in `θ` instead".  **That is wrong**, and the error
is a transpose.

`zakFibreL2 g t` is the **ω-slice**: for FIXED `t`, an `L²(circle)` function of the frequency
variable, with coefficients `k ↦ g(t+k)`.  That construction is sound and stays.

But `HRTMaster` does not consume the ω-slice.  `ZakTransform.zakFibre g θ t = zak g t (t+θ)` and
`fibreCircle g θ : AddCircle 1 → ℝ` are the **t-function for FIXED θ**, and the Birkhoff rotation
`x ↦ x − a` acts on `t`.  That is the transpose slicing, and obtaining it means slicing
`H(t,θ) := Zg(t,t+θ)` along `θ = const` — i.e. exactly the shear.  There is no cheap way around it:
for fixed `θ`, `∑_n g(t−n)e^{2πint}e^{2πinθ}` is NOT a Fourier series in `t`, because the
coefficients themselves depend on `t`.

So the honest remaining route is: assemble `Zg ∈ L²(T²)` (for which `ae_summable_sq_shift` and
`ae_memℓp_shift` are the input), prove the shear preserves Haar on `T²`, then Fubini for a.e. `θ`.
(That last sentence originally added "and the Haar-under-automorphism step is the one Mathlib does
not hand over directly".  That was ALSO wrong, and cheaply so: the shear is a SKEW PRODUCT over the
identity, so `MeasurePreserving.skew_product` reduces it to translation-invariance in the second
coordinate alone — three lines, no uniqueness argument.  See `measurePreserving_shear`.)

What survives unaffected: `hasSum_W_sq`, `ae_summable_sq_shift` (still the correct replacement for
the hypothesis `HRTReduction.summable_not_implied_by_memLp` refutes), `ae_memℓp_shift`, and
`zakFibreL2` itself. What does not survive is the claim that the shear was dodged. -/

/-! ## The next brick, routed but not built

**No torus shear is needed.**  The obvious construction — `Zg ∈ L²(T²)` and then
`G_θ(t) := Zg(t, t+θ)` — restricts an `L²` function to a LINE, which is undefined, and repairing
it wants the shear `(t,ω) ↦ (t,ω+t)` to preserve Haar on `T²`.  All of that is avoidable: for
fixed `t` the fibre

    ∑_n g(t−n) · e^{2πin(t+θ)}

is a Fourier series **in θ** whose coefficients `g(t−n)·e^{2πint}` have the same moduli as
`g(t−n)`.  So it is an `L²(circle)` function of `θ` exactly when `(g(t−n))_n ∈ ℓ²` — no line
restriction anywhere.

That makes the next brick:

    theorem ae_summable_sq_shift {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
        ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Summable (fun n : ℤ => ‖g (t - (n:ℝ))‖ ^ 2)

This is the CORRECT replacement for the false pointwise hypothesis that
`HRTReduction.summable_not_implied_by_memLp` refutes: `ℓ²`-summability a.e., rather than
`ℓ¹`-summability everywhere.  Unlike the false one it is automatic, and the route is:

1. `lintegral_tsum` (`Integral/Lebesgue/Add.lean:360`) to exchange `∫⁻_{Ioc 0 1}` with `∑'_n`;
2. each term `∫⁻ t in Ioc 0 1, ‖g(t+k)‖₊²` equals `ENNReal.ofReal` of the Bochner integral
   already summed by `HRTTransfer.hasSum_slice_sq`, whose total is `∫_ℝ‖g‖² < ∞`;
3. `ae_lt_top'` (`Integral/Lebesgue/Markov.lean:148`) for a.e. finiteness of the `∑'`;
4. `ENNReal.tsum_coe_ne_top_iff_summable` to land back in `Summable`.

`MeasureTheory.isAddFundamentalDomain_Ioc` + `IsAddFundamentalDomain.lintegral_eq_tsum`
(`Group/FundamentalDomain.lean:228`) is an alternative for step 1–2, at the cost of reindexing the
`tsum` from `AddSubgroup.zmultiples 1` to `ℤ`.

After that: the cocycle at a.e. `θ` by Fubini (also the source of `hreduction`'s "infinitely many
`w`"), and then `hGne` — which remains genuinely open and is the load-bearing obstruction. -/

end HRTZakL2

/-! ## Acceptance gate -/

#print axioms HRTZakL2.hasSum_W_sq
#print axioms HRTZakL2.memℓp_W
#print axioms HRTZakL2.memℓp_W_pi
#print axioms HRTZakL2.repr_zakL2
#print axioms HRTZakL2.volumePreserving_torusProd
#print axioms HRTZakL2.volume_eq_haar_circle
#print axioms HRTZakL2.volume_prod_eq_haar_prod
#print axioms HRTZakL2.measurePreserving_torusShear
#print axioms HRTZakL2.measurePreserving_shearInv
#print axioms HRTZakL2.measurePreserving_prodToTorus
#print axioms HRTZakL2.torusVolume_eq_piHaar
#print axioms HRTZakL2.measurePreserving_prodToTorusHaar
#print axioms HRTZakL2.ae_memLp_slice
#print axioms HRTZakL2.ae_memLp_zakSlice
#print axioms HRTZakL2.measurable_zakSliceNorm
#print axioms HRTZakL2.W_add
#print axioms HRTZakL2.W_smul
#print axioms HRTZakL2.intervalIntegrable_W_integrand
#print axioms HRTZakL2.measurePreserving_rotFst
#print axioms HRTZakL2.W_shift_real
#print axioms HRTZakL2.integral_wrap_piece
#print axioms HRTZakL2.repr_zakL2_rep
#print axioms HRTZakL2.zakL2_congr
#print axioms HRTZakL2.zakL2_add
#print axioms HRTZakL2.zakL2_smul
#print axioms HRTZakL2.norm_zakL2
#print axioms HRTZakL2.zakL2_ne_zero
#print axioms HRTZakL2.finite_shift_support_of_compactSupport
#print axioms HRTZakL2.summable_shift_of_compactSupport
#print axioms HRTZakL2.summable_zak_of_compactSupport
#print axioms HRTZakL2.summable_zak_term
#print axioms HRTZakL2.ae_summable_sq_shift
#print axioms HRTZakL2.ae_memℓp_shift
#print axioms HRTZakL2.repr_zakFibreL2
#print axioms HRTZakL2.measurePreserving_shear
