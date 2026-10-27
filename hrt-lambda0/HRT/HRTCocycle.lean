import HRTZakL2
import ZakTransform

/-!
# The cocycle — assembling `hcoc` on the dense class

`BirkhoffErgodic.integral_log_eq_of_modulus_cocycle` has six hypotheses beyond the cocycle, and all
six are discharged (`HRTReduction`: `hR`, `hPne`, `hPmeas`, `hint`, `hGne`; `HRTZakL2`: `hGmeas`).
The cocycle itself is the last input.

Its two ingredients turned out to sit at very different depths:

* **Covariance is free.**  `ZakTransform.zak_covariance` holds for ANY real shift, `√2` included,
  with no summability hypothesis — `tsum_congr` and `tsum_mul_left` are unconditional.
* **Additivity is not.**  Turning a DEPENDENCE into a relation among Zak transforms needs
  `∑(a+b) = ∑a + ∑b`, which is exactly what `ZakTransform.zak_dep_zero` takes as `s1`–`s4`.

`HRTZakL2.summable_zak_term` supplies all four on the compactly supported class, where the Zak
series is a FINITE sum.  This file instantiates them.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace HRTCocycle

open Complex MeasureTheory

/-- Every character `e^{2πi r s}` with real argument is unimodular. -/
theorem norm_char_le_one (r s : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp

/-- `zak_dep_zero`'s `s1`: the `(0,0)` term. -/
theorem summable_s1 {g : ℝ → ℂ} (hcs : HasCompactSupport g) (A : ℂ) (t ω : ℝ) :
    Summable (fun n : ℤ =>
      A * g (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) := by
  refine (HRTZakL2.summable_zak_term hcs A 0 t ω (fun _ => 1) (by simp)).congr fun n => ?_
  simp

/-- `zak_dep_zero`'s `s2`: the `(1,0)` term — a unit time shift. -/
theorem summable_s2 {g : ℝ → ℂ} (hcs : HasCompactSupport g) (B : ℂ) (t ω : ℝ) :
    Summable (fun n : ℤ =>
      B * g (t - (n : ℝ) - 1)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) := by
  refine (HRTZakL2.summable_zak_term hcs B 1 t ω (fun _ => 1) (by simp)).congr fun n => ?_
  simp

/-- `zak_dep_zero`'s `s3`: the `(0,1)` term — a unit modulation. -/
theorem summable_s3 {g : ℝ → ℂ} (hcs : HasCompactSupport g) (C : ℂ) (t ω : ℝ) :
    Summable (fun n : ℤ =>
      C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t - (n : ℝ) : ℝ) : ℂ)) * g (t - (n : ℝ)))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) := by
  refine (HRTZakL2.summable_zak_term hcs C 0 t ω
    (fun n => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t - (n : ℝ) : ℝ) : ℂ)))
    (fun n => by
      rw [Complex.norm_exp]; simp)).congr fun n => ?_
  simp

/-- `zak_dep_zero`'s `s4`: the `(√2,√2)` term — the shift that is NOT a lattice point. -/
theorem summable_s4 {g : ℝ → ℂ} (hcs : HasCompactSupport g) (D : ℂ) (a b t ω : ℝ) :
    Summable (fun n : ℤ =>
      D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * ((t - (n : ℝ) : ℝ) : ℂ))
            * g (t - (n : ℝ) - a))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) := by
  refine (HRTZakL2.summable_zak_term hcs D a t ω
    (fun n => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * ((t - (n : ℝ) : ℝ) : ℂ)))
    (fun n => by
      rw [Complex.norm_exp]; simp)).congr fun n => ?_
  rfl

/-- **A `Λ₀` dependence becomes a relation among Zak transforms** — on the compactly supported
class, where the four summability hypotheses hold.

This is the step `HRTReduction.summable_not_implied_by_memLp` shows CANNOT be taken for a general
`L²` window: the hypotheses `s1`–`s4` read `g` pointwise on a null set, so they are not implied by
`MemLp` and are not even a property of the `L²` class.  Compact support buys them outright; the
restriction is removed afterwards by continuity (`HRTZakL2.norm_zakL2`). -/
theorem zak_dep_zero_compactSupport {g : ℝ → ℂ} (hcs : HasCompactSupport g)
    (A B C D : ℂ) (a b t ω : ℝ)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    A * ZakPeriodization.zak g t ω
      + B * ZakPeriodization.zak (fun y => g (y - 1)) t ω
      + C * ZakPeriodization.zak
          (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t ω
      + D * ZakPeriodization.zak
          (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
            * g (y - a)) t ω = 0 :=
  ZakPeriodization.zak_dep_zero g A B C D a b t ω hdep
    (summable_s1 hcs A t ω) (summable_s2 hcs B t ω) (summable_s3 hcs C t ω)
    (summable_s4 hcs D a b t ω)

/-- **`hcoc` — THE COCYCLE — from a `Λ₀` dependence, on the dense class.**

Chains the three steps, two of which were already in `ZakTransform`:

  dependence  --(zak_dep_zero, summability from compact support)-->  Zak relation
              --(zakFibre_equation, uses zak_covariance)-->          fibre equation
              --(zakFibre_modulus)-->                                 the cocycle

The `Λ₀` instance is `a = b = √2`, so `zakFibre_equation`'s integrality hypothesis `b = a + j`
holds at `j = 0`.

With this, every hypothesis of `BirkhoffErgodic.integral_log_eq_of_modulus_cocycle` is in hand on
the compactly supported class: `hR`, `hPne`, `hPmeas`, `hint`, `hGne` (`HRTReduction`), `hGmeas`
(`HRTZakL2`), and now `hcoc`. -/
theorem cocycle_of_dependence_compactSupport {g : ℝ → ℂ} (hcs : HasCompactSupport g)
    (A B C D : ℂ) (hD : D ≠ 0) (a θ t : ℝ)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ‖ZakPeriodization.symbol A B C θ t‖ * ‖ZakPeriodization.zakFibre g θ t‖
      = ‖D‖ * ‖ZakPeriodization.zakFibre g θ (t - a)‖ :=
  ZakPeriodization.zakFibre_modulus g A B C D a a hD θ t
    (ZakPeriodization.zakFibre_equation g A B C D a a 0 (by push_cast; ring) θ t
      (zak_dep_zero_compactSupport hcs A B C D a a t (t + θ) hdep))

/-! ### Uniform finiteness on a bounded set — the route to `hGmeas` for the pointwise fibre

`HRTMaster` wants `Measurable (fibreCircle g θ)`, which is about `ZakTransform`'s POINTWISE fibre,
not the `L²` slice `HRTZakL2.measurable_zakSliceNorm` covers.  Mathlib has no `Measurable.tsum` for
a Banach codomain, so the series would need a sequential-exhaustion argument.

It is avoidable.  For `t` ranging over a BOUNDED set the compact support forces the contributing
indices into ONE finite set, uniformly in `t`: if `supp g ⊆ [−M,M]` and `t ∈ [c,d]`, then
`g (t − n) ≠ 0` needs `n ∈ [c − M, d + M]`.  So on the fundamental domain the Zak series is a
FINITE sum with a FIXED index set, and measurability is `Finset.measurable_sum`. -/

/-- **One finite index set works for all `t` in a bounded interval.** -/
theorem exists_finset_zak_eq {g : ℝ → ℂ} (hcs : HasCompactSupport g) (c d : ℝ) :
    ∃ S : Finset ℤ, ∀ t ∈ Set.Icc c d, ∀ n : ℤ, n ∉ S → g (t - (n : ℝ)) = 0 := by
  obtain ⟨M, hM⟩ := (hcs.isCompact.isBounded).subset_closedBall 0
  refine ⟨Finset.Icc ⌈c - M⌉ ⌊d + M⌋, fun t ht n hn => ?_⟩
  by_contra hne
  refine hn (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
  · have hmem : t - (n : ℝ) ∈ Metric.closedBall (0 : ℝ) M := hM (subset_tsupport _ hne)
    have h : |t - (n : ℝ)| ≤ M := by simpa [Real.dist_eq] using hmem
    rw [abs_le] at h
    exact Int.ceil_le.mpr (by linarith [ht.1, h.2])
  · have hmem : t - (n : ℝ) ∈ Metric.closedBall (0 : ℝ) M := hM (subset_tsupport _ hne)
    have h : |t - (n : ℝ)| ≤ M := by simpa [Real.dist_eq] using hmem
    rw [abs_le] at h
    exact Int.le_floor.mpr (by linarith [ht.2, h.1])

/-- **On a bounded interval the Zak series IS a finite sum.**  `tsum_eq_sum` applies because the
index set from `exists_finset_zak_eq` works uniformly in `t`. -/
theorem zak_eq_finsum {g : ℝ → ℂ} (hcs : HasCompactSupport g) (c d : ℝ) :
    ∃ S : Finset ℤ, ∀ t ∈ Set.Icc c d, ∀ ω : ℝ,
      ZakPeriodization.zak g t ω
        = ∑ n ∈ S, g (t - (n : ℝ))
            * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
  obtain ⟨S, hS⟩ := exists_finset_zak_eq hcs c d
  refine ⟨S, fun t ht ω => ?_⟩
  unfold ZakPeriodization.zak
  refine tsum_eq_sum fun n hn => ?_
  rw [hS t ht n hn, zero_mul]

/-- The finite sum is measurable in `t` — the character does not depend on `t`. -/
theorem measurable_zakFinsum {g : ℝ → ℂ} (hgm : Measurable g) (S : Finset ℤ) (ω : ℝ) :
    Measurable (fun t : ℝ =>
      ∑ n ∈ S, g (t - (n : ℝ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) :=
  Finset.measurable_sum S fun n _ =>
    (hgm.comp (measurable_id.sub_const _)).mul_const _

/-- **The FIBRE finite sum is measurable.**  `zakFibre g θ t = zak g t (t+θ)`, so unlike
`measurable_zakFinsum` the character `e^{2πin(t+θ)}` DEPENDS on `t` — each summand is a product of
two `t`-dependent factors rather than a function times a constant.  Still a finite sum of
measurable terms, but the previous lemma does not cover it. -/
theorem measurable_zakFibreFinsum {g : ℝ → ℂ} (hgm : Measurable g) (S : Finset ℤ) (θ : ℝ) :
    Measurable (fun t : ℝ =>
      ∑ n ∈ S, g (t - (n : ℝ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (((t + θ : ℝ)) : ℂ))) := by
  refine Finset.measurable_sum S fun n _ => ?_
  refine Measurable.mul (hgm.comp (measurable_id.sub_const _)) ?_
  refine Complex.measurable_exp.comp ?_
  refine Measurable.mul measurable_const ?_
  exact (Complex.measurable_ofReal.comp (measurable_id.add_const _))

/-- Hence the fibre modulus is measurable on any bounded interval. -/
theorem measurable_zakFibreNorm_finsum {g : ℝ → ℂ} (hgm : Measurable g) (S : Finset ℤ) (θ : ℝ) :
    Measurable (fun t : ℝ =>
      ‖∑ n ∈ S, g (t - (n : ℝ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (((t + θ : ℝ)) : ℂ))‖) :=
  (measurable_zakFibreFinsum hgm S θ).norm

/-! ### `hGmeas`, discharged on the compactly supported class

`HRTMaster.rootCount_of_cocycle` wants `Measurable (fibreCircle g θ)` — measurability of the
function on `AddCircle 1`, not of the `ℝ`-function.  `symbolCircle` got this for free from
`Continuous.quotient_liftOn'`, but `‖zakFibre g θ ·‖` is only measurable, so that route is closed.

`AddCircle.measurableEquivIoc 1 0 : AddCircle 1 ≃ᵐ Ioc 0 (0+1)` supplies the missing direction,
and it pays an unexpected dividend: transporting along it means the ONLY thing that must be
measurable is the restriction to `Ioc 0 1`.  `zak_eq_finsum` delivers a single finite index set
valid on all of `Icc 0 1`, so no patching over a cover of `ℝ` is needed — the bounded-interval
lemma is already the whole story. -/

/-- On `Ioc 0 1` the fibre modulus IS the finite sum's modulus, so its restriction is measurable. -/
theorem measurable_zakFibreNorm_restrict {g : ℝ → ℂ} (hcs : HasCompactSupport g)
    (hgm : Measurable g) (θ : ℝ) :
    Measurable (fun x : Set.Ioc (0:ℝ) (0+1) => ‖ZakPeriodization.zakFibre g θ (x : ℝ)‖) := by
  obtain ⟨S, hS⟩ := zak_eq_finsum hcs 0 1
  have heq : (fun x : Set.Ioc (0:ℝ) (0+1) => ‖ZakPeriodization.zakFibre g θ (x : ℝ)‖)
      = fun x : Set.Ioc (0:ℝ) (0+1) => ‖∑ n ∈ S, g ((x : ℝ) - (n : ℝ))
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
              * ((((x : ℝ) + θ : ℝ)) : ℂ))‖ := by
    funext x
    obtain ⟨hx1, hx2⟩ := x.2
    have hmem : (x : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨hx1.le, by simpa using hx2⟩
    change ‖ZakPeriodization.zak g (x : ℝ) ((x : ℝ) + θ)‖ = _
    rw [hS (x : ℝ) hmem ((x : ℝ) + θ)]
  rw [heq]
  exact (measurable_zakFibreNorm_finsum hgm S θ).comp measurable_subtype_coe

/-- **`hGmeas`, discharged on the compactly supported class.**  The fourth of the seven inputs to
`HRTMaster.rootCount_of_cocycle`. -/
theorem measurable_fibreCircle {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (θ : ℝ) : Measurable (ZakPeriodization.fibreCircle g θ) := by
  refine (MeasurableEquiv.measurable_comp_iff
    (AddCircle.measurableEquivIoc (1:ℝ) 0).symm).mp ?_
  have heq : (ZakPeriodization.fibreCircle g θ) ∘ (AddCircle.measurableEquivIoc (1:ℝ) 0).symm
      = fun x : Set.Ioc (0:ℝ) (0+1) => ‖ZakPeriodization.zakFibre g θ (x : ℝ)‖ := by
    -- `rfl`: the equiv's inverse IS `Ioc`-coe followed by `mk`, and `fibreCircle`'s `lift`
    -- computes on a `mk`, so both sides reduce to `‖zakFibre g θ x‖` definitionally.
    rfl
  rw [heq]
  exact measurable_zakFibreNorm_restrict hcs hgm θ

end HRTCocycle

/-! ## Acceptance gate -/

#print axioms HRTCocycle.norm_char_le_one
#print axioms HRTCocycle.summable_s1
#print axioms HRTCocycle.summable_s2
#print axioms HRTCocycle.summable_s3
#print axioms HRTCocycle.summable_s4
#print axioms HRTCocycle.zak_dep_zero_compactSupport
#print axioms HRTCocycle.cocycle_of_dependence_compactSupport
#print axioms HRTCocycle.exists_finset_zak_eq
#print axioms HRTCocycle.zak_eq_finsum
#print axioms HRTCocycle.measurable_zakFinsum
#print axioms HRTCocycle.measurable_zakFibreFinsum
#print axioms HRTCocycle.measurable_zakFibreNorm_finsum
#print axioms HRTCocycle.measurable_zakFibreNorm_restrict
#print axioms HRTCocycle.measurable_fibreCircle
