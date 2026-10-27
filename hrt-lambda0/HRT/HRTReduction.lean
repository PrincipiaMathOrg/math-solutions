import HRTMaster

/-!
# Discharging the side conditions of the `hreduction` chain

`HRTMaster.mean_of_zak_cocycle`, `threePoint_constraint_of_cocycle` and `rootCount_of_cocycle`
carry six side hypotheses beyond the Zak cocycle itself:

| hypothesis | status |
|---|---|
| `hR` — rotation preserves Haar | **discharged here** — unconditionally true |
| `hPmeas` — symbol measurable | routine |
| `hGmeas` — Zak fibre measurable | routine |
| `hPne` — symbol a.e. nonzero | a nonzero trig polynomial has finitely many zeros per period |
| `hint` — `log‖symbol‖` integrable | follows from `hPne` plus a bound |
| `hGne` — Zak fibre a.e. nonzero | **OPEN — where Heil–Speegle's difficulty lives** |

`hGne` is not plumbing: the Zak transform of a nonzero `L²` window genuinely can vanish, and no
argument in this development makes it automatic.  Everything else is reachable.
-/

namespace HRTReduction

open MeasureTheory AddCircle

/-- **The rotation of `AddCircle 1` preserves Haar measure.**  Discharges the `hR` hypothesis of
every `HRTMaster` chain theorem: `haarAddCircle` is the Haar probability measure on a compact
additive group, so it is translation invariant by construction. -/
theorem measurePreserving_sub_circle (a : ℝ) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => x - ((a : ℝ) : AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) haarAddCircle := by
  exact measurePreserving_sub_right haarAddCircle _

/-! ### Towards `hPne` — the symbol is a.e. nonzero

The symbol `P_θ(t) = A + B e^{−2πi(t+θ)} + C e^{2πit}`, multiplied by the unimodular `e^{2πit}`,
becomes a QUADRATIC in `z = e^{2πit}`:

    P_θ(t) · z  =  C z² + A z + B e^{−2πiθ}

and that is exactly the polynomial `heil_speegle_lambda_zero`'s `hreduction` already speaks about.
Since `z ≠ 0`, the symbol vanishes precisely where the quadratic does — at most two points of the
unit circle — so its zero set is finite and therefore null. -/

/-- **The symbol is a quadratic in `z = e^{2πit}`, up to the unimodular factor `z`.** -/
theorem symbol_mul_exp (A B C : ℂ) (θ t : ℝ) :
    ZakPeriodization.symbol A B C θ t * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
        + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ))) := by
  have h1 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (θ : ℂ))))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2 := (pow_two _).symm
  unfold ZakPeriodization.symbol
  push_cast
  linear_combination B * h1 + C * h2

/-- **The symbol vanishes only at the two roots.**  `hreduction` already hands us the
factorisation `C z² + A z + B e^{−2πiθ} = C (z − ζ₁)(z − ζ₂)`, so the zero set of the symbol is
carried by `{ζ₁, ζ₂}` and no `Polynomial` machinery is needed — at `C ≠ 0` the symbol is nonzero
at every `t` whose `e^{2πit}` misses both roots. -/
theorem symbol_ne_zero_of_ne_roots (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (t : ℝ) (h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ ζ₁)
    (h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ ζ₂) :
    ZakPeriodization.symbol A B C θ t ≠ 0 := by
  intro h
  have hmul := symbol_mul_exp A B C θ t
  rw [h, zero_mul, hfac] at hmul
  rcases mul_eq_zero.mp hmul.symm with hh | hh
  · rcases mul_eq_zero.mp hh with hh' | hh'
    · exact hC hh'
    · exact h1 (sub_eq_zero.mp hh')
  · exact h2 (sub_eq_zero.mp hh)

/-- The same statement phrased on the norm, which is what `symbolCircle` carries. -/
theorem norm_symbol_pos_of_ne_roots (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (t : ℝ) (h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ ζ₁)
    (h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ ζ₂) :
    0 < ‖ZakPeriodization.symbol A B C θ t‖ :=
  norm_pos_iff.mpr (symbol_ne_zero_of_ne_roots A B C θ ζ₁ ζ₂ hC hfac t h1 h2)

/-- On `AddCircle 1`, `toCircle` IS the character `e^{2πit}`. -/
theorem coe_toCircle (t : ℝ) :
    ((AddCircle.toCircle ((t : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- **The symbol's zero set on the circle is finite** — it injects into `{ζ₁, ζ₂}` under
`toCircle`, which is injective on `AddCircle 1`. -/
theorem finite_symbol_zeros (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂)) :
    {x : AddCircle (1 : ℝ) | ZakPeriodization.symbolCircle A B C θ x = 0}.Finite := by
  have hinj : Function.Injective
      (fun x : AddCircle (1 : ℝ) => ((AddCircle.toCircle x : Circle) : ℂ)) :=
    Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  have hsub : {x : AddCircle (1 : ℝ) | ZakPeriodization.symbolCircle A B C θ x = 0}
      ⊆ (fun x : AddCircle (1 : ℝ) => ((AddCircle.toCircle x : Circle) : ℂ)) ⁻¹' {ζ₁, ζ₂} := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | _ t =>
      intro hx
      simp only [Set.mem_setOf_eq, ZakPeriodization.symbolCircle_coe] at hx
      have hs : ZakPeriodization.symbol A B C θ t = 0 := norm_eq_zero.mp hx
      by_contra hcon
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
      rw [coe_toCircle] at hcon
      exact symbol_ne_zero_of_ne_roots A B C θ ζ₁ ζ₂ hC hfac t hcon.1 hcon.2 hs
  exact Set.Finite.subset (Set.Finite.preimage hinj.injOn (Set.toFinite _)) hsub

/-! ### The last step of `hPne`

`Set.Finite.measure_zero` needs `NoAtoms` on `AddCircle 1`, which **Mathlib does not provide** —
its only `NoAtoms`-from-Haar instance requires a normed *space*.  We supply it: a singleton's
preimage under the covering map `ℝ → AddCircle 1` is a coset of `ℤ`, hence countable, hence null
in `ℝ`, and `AddCircle.add_projection_respects_measure` transports that back. -/

/-- The fibre of the covering map over a point is a coset of `ℤ`, hence countable. -/
theorem countable_preimage_singleton (x : AddCircle (1 : ℝ)) :
    ((QuotientAddGroup.mk ⁻¹' {x} : Set ℝ)).Countable := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine (Set.countable_range (fun n : ℤ => y + (n : ℝ))).mono ?_
  intro z hz
  have hz' : ((z : ℝ) : AddCircle (1 : ℝ)) = ((y : ℝ) : AddCircle (1 : ℝ)) := hz
  have hmem : z - y ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hz'
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨k, ?_⟩
  -- the goal reads `(fun n => y + ↑n) k = z`, un-beta-reduced, so `show` first; and `k • (1:ℝ)`
  -- needs `zsmul_eq_mul` before it is an equation about `(k : ℝ)`
  have hk' : (k : ℝ) = z - y := by simpa using hk
  show y + (k : ℝ) = z
  linarith

instance noAtoms_volume_addCircle_one : NoAtoms (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  intro x
  rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left
    ((countable_preimage_singleton x).measure_zero volume)

instance noAtoms_haarAddCircle_one :
    NoAtoms (haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  constructor
  intro x
  rw [← ZakPeriodization.volume_eq_haar_one]
  exact measure_singleton x

/-- **`hPne`, DISCHARGED.**  The symbol is a.e. nonzero on `AddCircle 1`. -/
theorem symbolCircle_ae_ne_zero (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂)) :
    ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.symbolCircle A B C θ x ≠ 0 := by
  have hfin := finite_symbol_zeros A B C θ ζ₁ ζ₂ hC hfac
  rw [MeasureTheory.ae_iff]
  simp only [not_not]
  exact hfin.measure_zero _

/-! ### `hPmeas` — the symbol is measurable

`symbolCircle` is a `Function.Periodic.lift` of `t ↦ ‖symbol A B C θ t‖`, which is a finite sum of
exponentials and hence continuous; continuity descends through the quotient topology on
`AddCircle 1`. -/

theorem continuous_norm_symbol (A B C : ℂ) (θ : ℝ) :
    Continuous (fun t : ℝ => ‖ZakPeriodization.symbol A B C θ t‖) := by
  have h : Continuous (fun t : ℝ => ZakPeriodization.symbol A B C θ t) := by
    unfold ZakPeriodization.symbol
    continuity
  exact h.norm

theorem continuous_symbolCircle (A B C : ℂ) (θ : ℝ) :
    Continuous (ZakPeriodization.symbolCircle A B C θ) := by
  unfold ZakPeriodization.symbolCircle Function.Periodic.lift
  exact Continuous.quotient_liftOn' (continuous_norm_symbol A B C θ) _

/-- **`hPmeas`, DISCHARGED.** -/
theorem measurable_symbolCircle (A B C : ℂ) (θ : ℝ) :
    Measurable (ZakPeriodization.symbolCircle A B C θ) := by
  exact (continuous_symbolCircle A B C θ).measurable

/-! ### Towards `hint` — the symbol is bounded AWAY from zero when the roots miss the circle

`MeromorphicOn.intervalIntegrable_log_norm` would handle `log‖symbol‖` in general, but it is not
needed: `rootCount_of_cocycle` already assumes `‖ζ₁‖ ≠ 1` and `‖ζ₂‖ ≠ 1`, and on `|z| = 1` the
factorisation gives `‖symbol t‖ = ‖C‖·|z−ζ₁|·|z−ζ₂|`, which is then bounded below by a positive
constant.  So `log‖symbol‖` is CONTINUOUS, and integrability is immediate rather than a singular
integral. -/

theorem norm_exp_circle (t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **The symbol's modulus factors through the two roots.** -/
theorem norm_symbol_factor (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (t : ℝ) :
    ‖ZakPeriodization.symbol A B C θ t‖
      = ‖C‖ * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁‖
        * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂‖ := by
  have h := symbol_mul_exp A B C θ t
  rw [hfac] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_exp_circle, mul_one, norm_mul, norm_mul] at hn
  exact hn

/-- **The symbol is bounded away from zero when both roots miss the unit circle.** -/
theorem norm_symbol_pos_of_roots_off_circle (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (t : ℝ) :
    0 < ‖ZakPeriodization.symbol A B C θ t‖ := by
  rw [norm_symbol_factor A B C θ ζ₁ ζ₂ hfac t]
  have e1 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro hz
    exact h1 (by rw [← hz, norm_exp_circle])
  have e2 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro hz
    exact h2 (by rw [← hz, norm_exp_circle])
  exact mul_pos (mul_pos (norm_pos_iff.mpr hC) ((norm_nonneg _).lt_of_ne' e1))
    ((norm_nonneg _).lt_of_ne' e2)

theorem symbolCircle_pos (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (x : AddCircle (1 : ℝ)) : 0 < ZakPeriodization.symbolCircle A B C θ x := by
  induction x using QuotientAddGroup.induction_on with
  | _ t =>
    rw [ZakPeriodization.symbolCircle_coe]
    exact norm_symbol_pos_of_roots_off_circle A B C θ ζ₁ ζ₂ hC h1 h2 hfac t

/-- **`hint`, DISCHARGED** in the regime `HRTMaster.rootCount_of_cocycle` uses it — where both
roots miss the unit circle, so `log‖symbol‖` is continuous rather than singular. -/
theorem integrable_log_symbolCircle (A B C : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂)) :
    Integrable (fun x => Real.log |ZakPeriodization.symbolCircle A B C θ x|)
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  have hpos := symbolCircle_pos A B C θ ζ₁ ζ₂ hC h1 h2 hfac
  have hcont : Continuous (fun x : AddCircle (1 : ℝ) =>
      Real.log |ZakPeriodization.symbolCircle A B C θ x|) :=
    (continuous_symbolCircle A B C θ).abs.log
      (fun x => ne_of_gt (abs_pos.mpr (ne_of_gt (hpos x))))
  first
    | exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    | exact hcont.integrable

/-! ### Why the pointwise Zak route cannot serve a general `L²` window

`ZakTransform.zak_dep_zero` carries `Summable (fun n : ℤ => g (t - n) * …)` as HYPOTHESES, and
nothing in this development discharges them.  They are not merely restrictive — **they are not
determined by the `L²` class of `g` at all.**  `MemLp` constrains only the a.e. equivalence class,
while the summability condition reads `g` pointwise on the measure-zero set `ℤ`.

The witness below is `0` almost everywhere — hence in every `Lᵖ` — yet its values on `ℤ` make the
sum diverge.  Any honest route to `hreduction` for a general window must therefore rebuild the Zak
transform as an `L²`-valued object (the classical Zak is a unitary `L²(ℝ) → L²([0,1]²)`, with
convergence in `L²` rather than pointwise), or else restrict the window class — which weakens the
theorem, since linear independence does not pass to limits and HRT on a dense subclass does not
give HRT on `L²`. -/

/-- The indicator of `ℤ ⊆ ℝ`: zero a.e., but `1` at every integer. -/
noncomputable def intSpike : ℝ → ℂ := (Set.range ((↑) : ℤ → ℝ)).indicator (fun _ => 1)

theorem intSpike_ae_zero : intSpike =ᵐ[(volume : Measure ℝ)] 0 := by
  filter_upwards [(Set.countable_range ((↑) : ℤ → ℝ)).ae_notMem (volume : Measure ℝ)] with t ht
  unfold intSpike
  rw [Set.indicator_of_notMem ht]
  rfl

theorem intSpike_memLp : MemLp intSpike 2 (volume : Measure ℝ) := by
  have h0 : MemLp (0 : ℝ → ℂ) 2 (volume : Measure ℝ) := by
    first
      | exact MemLp.zero
      | exact ⟨aestronglyMeasurable_const, by simp⟩
  exact MemLp.ae_eq intSpike_ae_zero.symm h0

theorem intSpike_apply_int (n : ℤ) : intSpike ((0 : ℝ) - (n : ℝ)) = 1 := by
  have hmem : ((0 : ℝ) - (n : ℝ)) ∈ Set.range ((↑) : ℤ → ℝ) := ⟨-n, by push_cast; ring⟩
  unfold intSpike
  rw [Set.indicator_of_mem hmem]

/-! #### The replacement already exists in this repo

`HRTTransfer.W g (j,k) = √θ · ∫₀¹ g(s+k)·e^{−2πijθs} ds` is a Zak-type transform built by
INTEGRATION rather than by a pointwise series, and it carries `hasSum_sq_W` (Parseval) and
`ae_eq_zero_of_W_eq_zero` (injectivity on the `L²` class).  It has no summability hypothesis to
discharge — which is exactly why `HRTRectangular` is unconditional.  Any `L²`-valued
reformulation of the Zak route should be built on `W`, or on the same integrate-over-a-fibre
idea, rather than on `ZakTransform.zak`.

The remaining mismatch is that `W` lands in `ℓ²(ℤ²)` whereas the Birkhoff step consumes a
function on `AddCircle 1`; bridging that is the substance of the reformulation, together with a
Fubini step producing the cocycle for a.e. `θ` (which is also where `hreduction`'s "infinitely
many `w`" would come from). -/

/-- **The summability hypothesis of `zak_dep_zero` is not implied by `MemLp g 2`** — indeed it is
not even a property of the `L²` class, since it reads `g` on the null set `ℤ`. -/
theorem summable_not_implied_by_memLp :
    ¬ ∀ g : ℝ → ℂ, MemLp g 2 (volume : Measure ℝ) →
      Summable (fun n : ℤ => g ((0 : ℝ) - (n : ℝ))) := by
  intro h
  have hsum := h intSpike intSpike_memLp
  rw [funext intSpike_apply_int] at hsum
  exact one_ne_zero (tendsto_const_nhds_iff.mp hsum.tendsto_cofinite_zero)
/-! ### `hGne` is NOT an extra hypothesis — it follows from the cocycle and ERGODICITY

I spent this campaign calling `hGne` "genuinely open, load-bearing mathematics".  That looks
wrong.  The cocycle `|P|·|G| = d·|G ∘ R|` makes the ZERO SET OF `G` an `R`-INVARIANT SET:

* `G x = 0` ⟹ `d·|G (R x)| = 0` ⟹ `G (R x) = 0`  (using `d > 0`);
* `G (R x) = 0` ⟹ `|P x|·|G x| = 0` ⟹ `G x = 0`  (using `P x ≠ 0`).

`R` is an irrational rotation, hence **ergodic** (`AddCircle.ergodic_add_right`, valid exactly when
the shift has infinite additive order).  An ergodic map admits no invariant set of intermediate
measure, so the zero set is null or conull — and it is not conull the moment `G` is nonzero on a
set of positive measure, which Zak unitarity supplies. -/

/-- **The zero set of a cocycle solution is null, given ergodicity.** -/
theorem ae_ne_zero_of_cocycle {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {R : α → α} (hErg : Ergodic R μ) {G P : α → ℝ} {d : ℝ} (hd : 0 < d)
    (hGmeas : Measurable G) (hPne : ∀ᵐ x ∂μ, P x ≠ 0)
    (hcoc : ∀ᵐ x ∂μ, |P x| * |G x| = d * |G (R x)|)
    (hGnz : ¬ (∀ᵐ x ∂μ, G x = 0)) :
    ∀ᵐ x ∂μ, G x ≠ 0 := by
  have hZmeas : MeasurableSet {x | G x = 0} := hGmeas (measurableSet_singleton 0)
  have hinv : R ⁻¹' {x | G x = 0} =ᵐ[μ] {x | G x = 0} := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hcoc, hPne] with x hx hPx
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h
      rw [h, abs_zero, mul_zero] at hx
      exact abs_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (abs_ne_zero.mpr hPx))
    · intro h
      rw [h, abs_zero, mul_zero] at hx
      exact abs_eq_zero.mp ((mul_eq_zero.mp hx.symm).resolve_left (ne_of_gt hd))
  rcases hErg.quasiErgodic.ae_empty_or_univ₀ hZmeas.nullMeasurableSet hinv with h | h
  · exact Filter.eventuallyEq_empty.mp h
  · exact absurd (Filter.eventuallyEq_univ.mp h) hGnz

/-- **The `√2` rotation of `AddCircle 1` is ergodic.**  This is the `R` that `HRTMaster`'s chain
theorems rotate by, so it is the concrete input `ae_ne_zero_of_cocycle` needs in order to discharge
`hGne` for `Λ₀`.  Ergodic exactly because `√2` is irrational. -/
theorem ergodic_sub_sqrt2 :
    Ergodic (fun x : AddCircle (1 : ℝ) => x - ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  -- `AddCircle.ergodic_add_right` is stated for `volume`, not `haarAddCircle`; on the
  -- unit-length circle they are equal (`ZakPeriodization.volume_eq_haar_one`).
  rw [← ZakPeriodization.volume_eq_haar_one]
  simp only [sub_eq_add_neg]
  rw [AddCircle.ergodic_add_right, addOrderOf_neg, addOrderOf_eq_zero_iff,
    AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro q hq
  rw [div_one] at hq
  exact irrational_sqrt_two ⟨q, hq⟩

/-- **`√2` has infinite additive order on `AddCircle 1`** — the hypothesis
`AddCircle.ergodic_add_right` needs to make the `√2` rotation ergodic, and hence (via
`ae_ne_zero_of_cocycle`) to discharge `hGne` for `Λ₀`. -/
theorem addOrderOf_sqrtTwo : addOrderOf ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [addOrderOf_eq_zero_iff, isOfFinAddOrder_iff_nsmul_eq_zero]
  push_neg
  intro m hm hcon
  have hz : (((m : ℝ) * Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [← hcon, ← nsmul_eq_mul]
    first
      | rfl
      | simp
  rw [AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  rw [zsmul_eq_mul, mul_one] at hk
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine irrational_sqrt_two ⟨(k : ℚ) / (m : ℚ), ?_⟩
  push_cast
  field_simp
  linarith [hk]

/-- **The `√2` rotation of `AddCircle 1` is ergodic.**  `AddCircle.ergodic_add_right` is stated for
`volume`; on the unit circle `volume = haarAddCircle` (`ZakPeriodization.volume_eq_haar_one`), so
the Birkhoff-side measure is the same one. -/
theorem ergodic_sqrtTwo_rotation :
    Ergodic (fun x : AddCircle (1 : ℝ) => x - ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  have hord : addOrderOf (-((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    rw [addOrderOf_neg]; exact addOrderOf_sqrtTwo
  have h := (AddCircle.ergodic_add_right (p := 1)
    (a := -((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)))).mpr hord
  rw [← ZakPeriodization.volume_eq_haar_one]
  simpa [sub_eq_add_neg] using h

/-- **`hGne` at the concrete `Λ₀` fibre.**  Specialises `ae_ne_zero_of_cocycle` to the objects
`HRTMaster`'s chain actually consumes: the rotation is `x ↦ x − √2` on `AddCircle 1`, which
`ergodic_sqrtTwo_rotation` shows is ergodic.  So `hGne` need never be assumed — it is implied by
the cocycle together with the symbol being a.e. nonzero and the fibre not being a.e. zero. -/
theorem fibreCircle_ae_ne_zero {g : ℝ → ℂ} {A B C D : ℂ} {θ : ℝ} (hD : 0 < ‖D‖)
    (hGmeas : Measurable (ZakPeriodization.fibreCircle g θ))
    (hPne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.symbolCircle A B C θ x ≠ 0)
    (hcoc : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      |ZakPeriodization.symbolCircle A B C θ x| * |ZakPeriodization.fibreCircle g θ x|
        = ‖D‖ * |ZakPeriodization.fibreCircle g θ
            (x - ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)))|)
    (hGnz : ¬ (∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.fibreCircle g θ x = 0)) :
    ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.fibreCircle g θ x ≠ 0 :=
  ae_ne_zero_of_cocycle ergodic_sqrtTwo_rotation hD hGmeas hPne hcoc hGnz

end HRTReduction

/-! ## Acceptance gate -/

#print axioms HRTReduction.measurePreserving_sub_circle
#print axioms HRTReduction.symbol_mul_exp
#print axioms HRTReduction.symbol_ne_zero_of_ne_roots
#print axioms HRTReduction.norm_symbol_pos_of_ne_roots
#print axioms HRTReduction.coe_toCircle
#print axioms HRTReduction.finite_symbol_zeros
#print axioms HRTReduction.countable_preimage_singleton
#print axioms HRTReduction.symbolCircle_ae_ne_zero
#print axioms HRTReduction.continuous_norm_symbol
#print axioms HRTReduction.measurable_symbolCircle
#print axioms HRTReduction.norm_exp_circle
#print axioms HRTReduction.norm_symbol_factor
#print axioms HRTReduction.continuous_symbolCircle
#print axioms HRTReduction.norm_symbol_pos_of_roots_off_circle
#print axioms HRTReduction.symbolCircle_pos
#print axioms HRTReduction.integrable_log_symbolCircle
#print axioms HRTReduction.ae_ne_zero_of_cocycle
#print axioms HRTReduction.addOrderOf_sqrtTwo
#print axioms HRTReduction.ergodic_sqrtTwo_rotation
#print axioms HRTReduction.fibreCircle_ae_ne_zero
#print axioms HRTReduction.ergodic_sub_sqrt2
#print axioms HRTReduction.intSpike_memLp
#print axioms HRTReduction.summable_not_implied_by_memLp
