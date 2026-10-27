import HRTShift
import HRTMix
import HRTCocycle
import HRTReduction
import HRTHthree

/-!
# The `zakL2` ↔ pointwise-`zak` bridge

`zakL2` is synthesised from the `W` coefficients through `UnitAddTorus.mFourierBasis`, with no
pointwise series anywhere — that is exactly why it survives a general `L²` window, where
`summable_not_implied_by_memLp` shows the pointwise Zak series cannot.  But the shift identity we
ultimately need is proved POINTWISE (`HRTShift.zak_shift_wrap`), so the two pictures have to be
identified before that identity can be transported to `L²`.

## Two facts that the naive statement of this bridge gets wrong

**(1) `zak` does not descend to the torus.**  `ZakPeriodization.zak_quasi_periodic_fst` says

    zak g (t+1) ω = e^{2πiω} · zak g t ω

so `zak` is QUASI-periodic in `t`, not periodic — it is a section of a non-trivial line bundle over
`T²`, and there is no global trivialisation (multiplying by `e(-tω)` fixes the `t`-period and breaks
the `ω`-period).  So "`zakL2 g` = the `L²` class of `zak g`" is not even a well-formed statement.
The bridge must read `zak` on a FUNDAMENTAL DOMAIN, which is what `zakBox` below does.  Only the
values on `[0,1)²` are ever used, and those are what the Fourier coefficients integrate over anyway.

**(2) The index conventions differ by a 90° ROTATION, not merely a transpose.**  Computing the
`n`-th coefficient of `zakBox` (`coeff_zakBox_eq_W` below) gives

    mFourierCoeff (zakBox g) n = W 1 g (n 0) (-(n 1))

whereas `HRTZakL2.repr_zakL2` gives `repr (zakL2 …) i = W 1 g (i 1) (i 0)`.  These agree under
`i ↦ (i 1, -i 0)` — a quarter-turn of `ℤ²`, i.e. the Fourier rotation `(t,ω) ↦ (ω,-t)`, the same
metaplectic rotation that appears throughout this campaign.  A transpose alone (the guess recorded
in `HRTMix`'s section header, which mentions "a TRANSPOSE and a NEGATION") is the same map, but
naming it as a rotation is what makes the downstream conjugation obvious.

**Both points fail SILENTLY if got wrong**: `zakBox g` and `zakL2 g` are honest `L²` elements with
the correct norms under any of these conventions, so a mis-identification produces neither a build
error nor a change in axiom footprint.  Hence every step below is machine-checked rather than
asserted.
-/

open scoped NNReal ENNReal
open MeasureTheory

noncomputable section

namespace HRTBridge

/-! ### The fundamental-domain representative -/

/-- The `[0,1)` representative of a point of the unit circle. -/
noncomputable def rep1 (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x : ℝ)

/-- On the fundamental domain the representative is the identity. -/
theorem rep1_coe {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) : rep1 ((t : UnitAddCircle)) = t := by
  unfold rep1
  rw [AddCircle.equivIco_coe_eq (by simpa using ht)]

/-- **`rep1` is measurable.**  `fun_prop` cannot do this: `equivIco` unfolds to a
`Function.Periodic.lift` and the automation has no lemma for it.  The witness is
`AddCircle.measurableEquivIco`, whose `toEquiv` IS `equivIco` — so the representative map is a
measurable equivalence composed with the subtype coercion. -/
theorem measurable_rep1 : Measurable rep1 :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1:ℝ) 0).measurable

/-- **`zak` read on the fundamental box**, as an honest function on `T² = T × T`.  This is the
object the bridge compares against `zakL2`; see the module docstring for why `zak` itself does not
descend to the torus. -/
noncomputable def zakBox (g : ℝ → ℂ) (p : UnitAddCircle × UnitAddCircle) : ℂ :=
  ZakPeriodization.zak g (rep1 p.1) (rep1 p.2)

/-! ### Reducing a torus integral to an iterated `[0,1]` integral

Three steps, each a one-liner given the right Mathlib lemma, and together they turn
`mFourierCoeff` — an integral over `UnitAddTorus (Fin 2)` — into the iterated interval integral that
`HRTMix.coeff_zak_finsum` consumes. -/

/-- **Step 1 — the pi-torus IS the binary product.**  `volumePreserving_torusProd` is already ours;
this is the integral form of it. -/
theorem torus_integral_eq_prod (F : UnitAddTorus (Fin 2) → ℂ) :
    (∫ x, F x ∂(volume : Measure (UnitAddTorus (Fin 2))))
      = ∫ p : UnitAddCircle × UnitAddCircle,
          F ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p) :=
  (MeasurePreserving.integral_comp
    (HRTZakL2.volumePreserving_torusProd).symm
    (MeasurableEquiv.measurableEmbedding _) F).symm

/-- **Step 2 — Fubini on the product.** -/
theorem prod_integral_iterated (H : UnitAddCircle × UnitAddCircle → ℂ)
    (hH : Integrable H (volume : Measure (UnitAddCircle × UnitAddCircle))) :
    (∫ p, H p ∂(volume : Measure (UnitAddCircle × UnitAddCircle)))
      = ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, H (x, y) := by
  rw [← integral_prod H (by rwa [← Measure.volume_eq_prod]), ← Measure.volume_eq_prod]

/-- **Step 3 — the circle integral IS the `[0,1]` integral.**  On the unit-length circle no
normalising constant appears; compare `ZakPeriodization.symbol_mean_circle_eq_interval`. -/
theorem circle_integral_eq_interval (f : UnitAddCircle → ℂ) :
    (∫ b : UnitAddCircle, f b) = ∫ a in (0:ℝ)..1, f (a : UnitAddCircle) := by
  have h := AddCircle.intervalIntegral_preimage (1:ℝ) 0 f
  rw [zero_add] at h
  exact h.symm

/-! ### The characters, concretely

`mFourier` is a product of `fourier`s, and on the unit circle `fourier` is `HRTTransfer.ee`.  Both
are needed to line the coefficient integral up with `HRTMix`'s statement of it. -/

/-- **`mFourier` on the two-torus is a product of two circle characters.** -/
theorem mFourier_two (n : Fin 2 → ℤ) (x : UnitAddTorus (Fin 2)) :
    UnitAddTorus.mFourier n x = fourier (n 0) (x 0) * fourier (n 1) (x 1) := by
  simp [UnitAddTorus.mFourier, Fin.prod_univ_two]

/-- **On the unit circle, `fourier` IS `ee`.**  The `/T` in `fourier_coe_apply` is division by
one. -/
theorem fourier_eq_ee (n : ℤ) (t : ℝ) :
    fourier n ((t : ℝ) : UnitAddCircle) = HRTTransfer.ee ((n : ℝ) * t) := by
  rw [fourier_coe_apply]
  unfold HRTTransfer.ee
  push_cast
  ring_nf

/-! ### The coefficient of the finite Zak sum, as a `W` -/

/-- **The box coefficient of a finite Zak sum IS a `W` coefficient.**  This packages
`HRTMix.coeff_zak_finsum` (which does the `ω`-integral first, collapsing the sum to its `m`-th term)
with `HRTMix.coeff_eq_W_neg` (which absorbs the `g (t-n)` vs `g (s+k)` sign convention). -/
theorem box_coeff_eq_W (S : Finset ℤ) (g : ℝ → ℂ) (j m : ℤ) :
    (∫ t in (0:ℝ)..1,
        (∫ ω in (0:ℝ)..1, (∑ n ∈ S, g (t - (n:ℝ)) * HRTTransfer.ee ((n:ℝ) * ω))
            * HRTTransfer.ee (-((m:ℝ) * ω)))
          * HRTTransfer.ee (-((j:ℝ) * t)))
      = if m ∈ S then HRTTransfer.W 1 g j (-m) else 0 := by
  rw [HRTMix.coeff_zak_finsum S g j m]
  by_cases hm : m ∈ S
  · rw [if_pos hm, if_pos hm, HRTMix.coeff_eq_W_neg]
  · rw [if_neg hm, if_neg hm]

/-! ### Crossing the Haar/`volume` instance gap

`mFourierBasis` and `mFourierCoeff` are built in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`,
which at line 30 installs

    local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

so every `mFourier*` declaration lives over **Haar**, whereas `volumePreserving_torusProd` and the
rest of our transport machinery is stated for **`volume`**.  On the unit circle the two measures are
equal (`HRTZakL2.volume_eq_haar_circle`), but the `MeasureSpace` INSTANCE TERMS differ, so `exact`
and `rw` both fail with a `MeasureSpace.pi` mismatch that mentions
`AddCircle.measureSpace 1` on one side and `instMeasureSpaceUnitAddCircle` on the other.

This is the same trap recorded on `HRTZakL2.zakL2` ("do NOT ascribe an explicit return type"), met
from the other direction.  The escape is the one anticipated there: `Measure.pi (fun _ =>
haarAddCircle)` is an explicit measure TERM needing no instance, `mFourierCoeff` unfolds to it by
`rfl`, and `HRTZakL2.torusVolume_eq_piHaar` identifies it with `volume`. -/

/-- `zak` on the box, as a function on the PI-torus — the shape `mFourierCoeff` consumes. -/
noncomputable def zakTor (g : ℝ → ℂ) (x : UnitAddTorus (Fin 2)) : ℂ :=
  ZakPeriodization.zak g (rep1 (x 0)) (rep1 (x 1))

/-- **The Fourier coefficient, moved off the Haar instance and into the product picture.**  The
first step is `rfl` because the Haar pi-measure is literally what `mFourierCoeff` unfolds to; the
second is `torusVolume_eq_piHaar`; the third is our own transport.  With this the coefficient of any
torus function is an integral over `T × T`, where Fubini and the interval-integral rewrites apply. -/
theorem coeff_eq_prod (F : UnitAddTorus (Fin 2) → ℂ) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff F n
      = ∫ p : UnitAddCircle × UnitAddCircle,
          UnitAddTorus.mFourier (-n)
              ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
            • F ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p) := by
  have h0 : UnitAddTorus.mFourierCoeff F n
      = ∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier (-n) x • F x
          ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := rfl
  rw [h0, ← HRTZakL2.torusVolume_eq_piHaar]
  exact torus_integral_eq_prod _

/-! ### From the coefficient to an iterated integral

With `coeff_eq_prod` in hand the rest is mechanical: simplify the integrand through
`piFinTwo.symm`, apply Fubini, and convert each circle integral to a `[0,1]` interval integral.
The one wrinkle is that `rep1` is the identity only on `[0,1)`, while the interval integral runs
over `(0,1]` — they differ at the single point `t = 1`, which is null. -/

/-- **The integrand, through `piFinTwo.symm`.**  The equivalence sends `p` to the function taking
`0 ↦ p.1` and `1 ↦ p.2`, so both the character and `zakTor` split into their two coordinates. -/
theorem integrand_simp (g : ℝ → ℂ) (n : Fin 2 → ℤ) (p : UnitAddCircle × UnitAddCircle) :
    UnitAddTorus.mFourier (-n)
        ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
        • zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
      = (fourier (-n 0) p.1 * fourier (-n 1) p.2)
          * ZakPeriodization.zak g (rep1 p.1) (rep1 p.2) := by
  rw [mFourier_two]; rfl

/-- **`rep1` collapses a.e. on the interval.**  `rep1 ↑t = t` holds on `[0,1)`; the interval
integral runs over `(0,1]`, so the two agree off the null set `{1}`. -/
theorem rep_ae (f : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, f (rep1 ((t : ℝ) : UnitAddCircle))) = ∫ t in (0:ℝ)..1, f t := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t : ℝ, t ≠ 1 := by
    rw [ae_iff]
    simpa using measure_singleton (1:ℝ)
  filter_upwards [hne] with t ht hmem
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
  rw [rep1_coe ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 ht⟩]

/-- **The coefficient as an iterated circle integral.**  Integrability is carried as a hypothesis
here; on the compactly supported class it is discharged from `HRTCocycle.zak_eq_finsum`, which
makes the Zak series a FINITE sum of `L¹` pieces on the box. -/
theorem coeff_iter_circle (g : ℝ → ℂ) (n : Fin 2 → ℤ)
    (hInt : Integrable
      (fun p : UnitAddCircle × UnitAddCircle =>
        UnitAddTorus.mFourier (-n)
            ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
          • zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p))
      (volume : Measure (UnitAddCircle × UnitAddCircle))) :
    UnitAddTorus.mFourierCoeff (zakTor g) n
      = ∫ x : UnitAddCircle, ∫ y : UnitAddCircle,
          (fourier (-n 0) x * fourier (-n 1) y)
            * ZakPeriodization.zak g (rep1 x) (rep1 y) := by
  rw [coeff_eq_prod, prod_integral_iterated _ hInt]
  exact integral_congr_ae (.of_forall (fun x => integral_congr_ae
    (.of_forall (fun y => integrand_simp g n (x, y)))))

/-! ### The coefficient as an iterated `[0,1]` integral

The last conversion.  `fourier` at a circle point is `ee` of its REPRESENTATIVE
(`fourier_eq_ee_rep`), so the whole integrand becomes a function of `(rep1 x, rep1 y)` — and then
`iter_circle_to_interval` replaces both circle integrals by `[0,1]` integrals in one step. -/

/-- **`fourier` at a circle point is `ee` of its representative.**  `AddCircle.coe_equivIco` says
`↑(rep1 x) = x`, so this is `fourier_eq_ee` applied at the representative. -/
theorem fourier_eq_ee_rep (n : ℤ) (x : UnitAddCircle) :
    fourier n x = HRTTransfer.ee ((n : ℝ) * rep1 x) := by
  have hx : ((rep1 x : ℝ) : UnitAddCircle) = x := AddCircle.coe_equivIco
  calc fourier n x = fourier n ((rep1 x : ℝ) : UnitAddCircle) := by rw [hx]
    _ = HRTTransfer.ee ((n : ℝ) * rep1 x) := fourier_eq_ee n (rep1 x)

/-- **The iterated circle integral IS the iterated `[0,1]` integral**, for any integrand that sees
only the representatives. -/
theorem iter_circle_to_interval (F : ℝ → ℝ → ℂ) :
    (∫ x : UnitAddCircle, ∫ y : UnitAddCircle, F (rep1 x) (rep1 y))
      = ∫ t in (0:ℝ)..1, ∫ w in (0:ℝ)..1, F t w := by
  rw [circle_integral_eq_interval
    (fun x : UnitAddCircle => ∫ y : UnitAddCircle, F (rep1 x) (rep1 y))]
  rw [show (fun t : ℝ => ∫ y : UnitAddCircle, F (rep1 ((t:ℝ) : UnitAddCircle)) (rep1 y))
        = (fun t : ℝ => ∫ w in (0:ℝ)..1, F (rep1 ((t:ℝ) : UnitAddCircle)) w) from
      funext (fun t => by
        rw [circle_integral_eq_interval
          (fun y : UnitAddCircle => F (rep1 ((t:ℝ) : UnitAddCircle)) (rep1 y))]
        exact rep_ae _)]
  exact rep_ae (fun t => ∫ w in (0:ℝ)..1, F t w)

/-- **THE COEFFICIENT, as an iterated `[0,1]` integral.**  This is the shape `box_coeff_eq_W`
consumes: once `zak` is replaced by its finite sum on the compactly supported class, the two
statements meet.

Note the proof supplies `F` to `iter_circle_to_interval` EXPLICITLY — leaving it to unification
fails, because the goal carries the beta-redex `(fun t w => …) (rep1 x) (rep1 y)` and Lean will not
solve that higher-order pattern on its own. -/
theorem coeff_interval (g : ℝ → ℂ) (n : Fin 2 → ℤ)
    (hInt : Integrable
      (fun p : UnitAddCircle × UnitAddCircle =>
        UnitAddTorus.mFourier (-n)
            ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
          • zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p))
      (volume : Measure (UnitAddCircle × UnitAddCircle))) :
    UnitAddTorus.mFourierCoeff (zakTor g) n
      = ∫ t in (0:ℝ)..1, ∫ w in (0:ℝ)..1,
          (HRTTransfer.ee (-((n 0 : ℝ) * t)) * HRTTransfer.ee (-((n 1 : ℝ) * w)))
            * ZakPeriodization.zak g t w := by
  have key := iter_circle_to_interval
    (fun t w : ℝ => (HRTTransfer.ee (-((n 0 : ℝ) * t)) * HRTTransfer.ee (-((n 1 : ℝ) * w)))
      * ZakPeriodization.zak g t w)
  rw [coeff_iter_circle g n hInt, ← key]
  exact integral_congr_ae (.of_forall (fun x => integral_congr_ae (.of_forall (fun y => by
    simp only [fourier_eq_ee_rep]
    push_cast
    ring_nf))))

/-! ### The bridge coefficient identity

Everything above meets here.  On the compactly supported class `HRTCocycle.exists_finset_zak_eq`
supplies a single finite index set `S` that works for every `t ∈ [0,1]`, so the Zak series is a
finite sum and `box_coeff_eq_W` applies.  Its `if m ∈ S` disappears because `W` vanishes off `S`
too — the same hypothesis that kills the series terms kills the coefficient. -/

/-- Off the finite index set the `W` coefficient vanishes, so `box_coeff_eq_W`'s `if` collapses. -/
theorem W_vanishes_off {g : ℝ → ℂ} {S : Finset ℤ}
    (hS : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ n : ℤ, n ∉ S → g (t - (n:ℝ)) = 0)
    (j m : ℤ) (hm : m ∉ S) : HRTTransfer.W 1 g j (-m) = 0 := by
  rw [← HRTMix.coeff_eq_W_neg]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0:ℂ)) (fun t ht => ?_)]
  · simp
  · rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rw [hS t ht m hm, zero_mul]

/-- The reordering into `box_coeff_eq_W`'s shape at a single `t`: replace `zak` by its finite sum,
pull the `t`-character out of the `w`-integral, and commute. -/
theorem inner_reorder (g : ℝ → ℂ) (S : Finset ℤ) (n : Fin 2 → ℤ) (t : ℝ)
    (hz : ∀ w : ℝ, ZakPeriodization.zak g t w
        = ∑ k ∈ S, g (t - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * w)) :
    (∫ w in (0:ℝ)..1, (HRTTransfer.ee (-((n 0 : ℝ) * t)) * HRTTransfer.ee (-((n 1 : ℝ) * w)))
        * ZakPeriodization.zak g t w)
      = (∫ w in (0:ℝ)..1, (∑ k ∈ S, g (t - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * w))
          * HRTTransfer.ee (-((n 1 : ℝ) * w))) * HRTTransfer.ee (-((n 0 : ℝ) * t)) := by
  rw [intervalIntegral.integral_congr (g := fun w : ℝ =>
      HRTTransfer.ee (-((n 0 : ℝ) * t))
        * ((∑ k ∈ S, g (t - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * w))
            * HRTTransfer.ee (-((n 1 : ℝ) * w)))) (fun w _ => by rw [hz w]; ring)]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **THE BRIDGE COEFFICIENT IDENTITY.**

    mFourierCoeff (zakTor g) n = W 1 g (n 0) (-(n 1))

on the compactly supported class.  Against `HRTZakL2.repr_zakL2 … i = W 1 g (i 1) (i 0)` this is
the 90° index rotation `i ↦ (i 1, -i 0)` announced in the module docstring — now MEASURED rather
than conjectured, which matters because a wrong identification here is invisible to both the build
and the axiom footprint. -/
theorem coeff_zakTor_eq_W {g : ℝ → ℂ} (hcs : HasCompactSupport g) (n : Fin 2 → ℤ)
    (hInt : Integrable
      (fun p : UnitAddCircle × UnitAddCircle =>
        UnitAddTorus.mFourier (-n)
            ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
          • zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p))
      (volume : Measure (UnitAddCircle × UnitAddCircle))) :
    UnitAddTorus.mFourierCoeff (zakTor g) n = HRTTransfer.W 1 g (n 0) (-(n 1)) := by
  obtain ⟨S, hS⟩ := HRTCocycle.exists_finset_zak_eq hcs 0 1
  have hz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ w : ℝ, ZakPeriodization.zak g t w
      = ∑ k ∈ S, g (t - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * w) := by
    intro t ht w
    unfold ZakPeriodization.zak
    rw [tsum_eq_sum (fun k hk => by rw [hS t ht k hk, zero_mul])]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    unfold HRTTransfer.ee; push_cast; ring_nf
  rw [coeff_interval g n hInt]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (∫ w in (0:ℝ)..1, (∑ k ∈ S, g (t - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * w))
          * HRTTransfer.ee (-((n 1 : ℝ) * w))) * HRTTransfer.ee (-((n 0 : ℝ) * t)))
      (fun t ht => inner_reorder g S n t (hz t (by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht)))]
  rw [box_coeff_eq_W]
  by_cases hm : n 1 ∈ S
  · rw [if_pos hm]
  · rw [if_neg hm, W_vanishes_off hS (n 0) (n 1) hm]

/-! ### Towards `MemLp (zakTor g) 2`

The integrability hypothesis on `coeff_interval` / `coeff_zakTor_eq_W` should come from
`MemLp (zakTor g) 2`, which subsumes it (the torus has finite measure, so `L² ⊆ L¹`).  The
structural input is that `rep1` ALWAYS lands in the fundamental domain, so the finite-sum form
holds at every point rather than merely almost everywhere — no null-set bookkeeping is needed
downstream. -/

/-- The representative always lands in `[0,1)`. -/
theorem rep1_mem (x : UnitAddCircle) : rep1 x ∈ Set.Ico (0:ℝ) 1 := by
  unfold rep1
  simpa using (AddCircle.equivIco (1:ℝ) 0 x).2

/-- …hence in `[0,1]`, which is the form `exists_finset_zak_eq` consumes. -/
theorem rep1_mem_Icc (x : UnitAddCircle) : rep1 x ∈ Set.Icc (0:ℝ) 1 :=
  ⟨(rep1_mem x).1, le_of_lt (rep1_mem x).2⟩

/-- **`zakTor` IS a finite sum — everywhere, not just a.e.**  Because `rep1_mem_Icc` puts every
representative inside the interval on which `exists_finset_zak_eq`'s index set is valid, one
`Finset` works at every point of the torus. -/
theorem zakTor_finsum {g : ℝ → ℂ} (hcs : HasCompactSupport g) :
    ∃ S : Finset ℤ, ∀ x : UnitAddTorus (Fin 2),
      zakTor g x
        = ∑ k ∈ S, g (rep1 (x 0) - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * rep1 (x 1)) := by
  obtain ⟨S, hS⟩ := HRTCocycle.exists_finset_zak_eq hcs 0 1
  refine ⟨S, fun x => ?_⟩
  unfold zakTor ZakPeriodization.zak
  rw [tsum_eq_sum (fun k hk => by rw [hS _ (rep1_mem_Icc (x 0)) k hk, zero_mul])]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  unfold HRTTransfer.ee; push_cast; ring_nf

/-! ### `MemLp (zakTor g) 2` — discharging the integrability hypothesis

The torus has finite measure, so `L² ⊆ L¹` and this subsumes the `Integrable` hypothesis carried by
`coeff_interval` and `coeff_zakTor_eq_W`.

The route is forced by what Mathlib has.  There is `measurePreserving_equivIoc` but NO `Ico`
analogue, and the `Ioc` one lands in `Measure.comap Subtype.val volume` on a subtype — awkward to
consume.  So `rep1` is NOT treated as a measure-preserving map; instead the `eLpNorm` is bounded
through `UnitAddCircle.lintegral_preimage`, comparing the circle integral against the whole line. -/

/-- The translated window is still `L²` on the line — translation preserves Lebesgue measure. -/
theorem memLp_shift {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) (k : ℤ) :
    MemLp (fun t : ℝ => g (t - (k:ℝ))) 2 (volume : Measure ℝ) :=
  hg.comp_measurePreserving (measurePreserving_sub_right (volume : Measure ℝ) (k:ℝ))

/-- **The circle `∫⁻` is at most the line `∫⁻`.**  Note the a.e. step is genuinely needed: the
preimage interval is `Ioc 0 1`, which CONTAINS `1`, while `rep1 ↑1 = 0 ≠ 1`.  The two integrands
really do differ there, so a pointwise `setLIntegral_congr_fun` fails; `{1}` is null, so the a.e.
version goes through. -/
theorem circle_lint_le (g : ℝ → ℂ) (k : ℤ) :
    (∫⁻ c : UnitAddCircle, ‖g (rep1 c - (k:ℝ))‖ₑ ^ (2:ℝ))
      ≤ ∫⁻ t : ℝ, ‖g (t - (k:ℝ))‖ₑ ^ (2:ℝ) := by
  rw [← UnitAddCircle.lintegral_preimage 0
    (fun c : UnitAddCircle => ‖g (rep1 c - (k:ℝ))‖ₑ ^ (2:ℝ))]
  have hcong : (∫⁻ a in Set.Ioc (0:ℝ) (0+1), ‖g (rep1 ((a:ℝ) : UnitAddCircle) - (k:ℝ))‖ₑ ^ (2:ℝ))
      = ∫⁻ a in Set.Ioc (0:ℝ) (0+1), ‖g (a - (k:ℝ))‖ₑ ^ (2:ℝ) := by
    have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0:ℝ) (0+1))), t ≠ 1 :=
      ae_restrict_of_ae (by rw [ae_iff]; simpa using measure_singleton (1:ℝ))
    have hmem : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0:ℝ) (0+1))),
        t ∈ Set.Ioc (0:ℝ) (0+1) := ae_restrict_mem measurableSet_Ioc
    refine lintegral_congr_ae ?_
    filter_upwards [hne, hmem] with t ht htm
    rw [rep1_coe ⟨le_of_lt htm.1, lt_of_le_of_ne (by simpa using htm.2) ht⟩]
  rw [hcong]
  exact setLIntegral_le_lintegral _ _

/-- **The shifted window, read through the representative, is `L²` on the circle.** -/
theorem memLp_g_rep {g : ℝ → ℂ} (hgm : Measurable g) (hg : MemLp g 2 (volume : Measure ℝ))
    (k : ℤ) :
    MemLp (fun c : UnitAddCircle => g (rep1 c - (k:ℝ))) 2 (volume : Measure UnitAddCircle) := by
  refine ⟨(hgm.comp (measurable_rep1.sub measurable_const)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have hline : (∫⁻ t : ℝ, ‖g (t - (k:ℝ))‖ₑ ^ ((2:ℝ≥0∞)).toReal) < ⊤ := by
    have := (memLp_shift hg k).eLpNorm_lt_top
    rwa [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at this
  simp only [ENNReal.toReal_ofNat] at hline ⊢
  exact lt_of_le_of_lt (circle_lint_le g k) hline

/-- On the unit circle `volume` IS Haar, hence a probability measure.  Mathlib registers this for
`haarAddCircle` but not for `volume`, and `measurePreserving_fst` needs it. -/
instance isProb_volume_circle : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [HRTZakL2.volume_eq_haar_circle]
  infer_instance

/-- **Evaluating the first coordinate is measure preserving** — both factors are probability
measures, so the projection off the product is. -/
theorem mp_eval0 :
    MeasurePreserving (fun x : UnitAddTorus (Fin 2) => x 0)
      (volume : Measure (UnitAddTorus (Fin 2))) (volume : Measure UnitAddCircle) := by
  have hfst : MeasurePreserving (Prod.fst : UnitAddCircle × UnitAddCircle → UnitAddCircle)
      (volume : Measure (UnitAddCircle × UnitAddCircle)) (volume : Measure UnitAddCircle) := by
    rw [Measure.volume_eq_prod]
    exact measurePreserving_fst
  exact hfst.comp HRTZakL2.volumePreserving_torusProd

/-- **`zakTor g` is `L²` on the torus.**  A finite sum (`zakTor_finsum`) of translated windows
(`memLp_g_rep`, pulled back along `mp_eval0`) each twisted by a unimodular character
(`HRTShift.memLp_unimodular_mul`).  Because `zakTor_finsum` is a POINTWISE identity, the rewrite is
a plain `funext` — no a.e. congruence lemma is needed. -/
theorem memLp_zakTor {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (zakTor g) 2 (volume : Measure (UnitAddTorus (Fin 2))) := by
  obtain ⟨S, hSum⟩ := zakTor_finsum hcs
  rw [show zakTor g = fun x : UnitAddTorus (Fin 2) =>
      ∑ k ∈ S, g (rep1 (x 0) - (k:ℝ)) * HRTTransfer.ee ((k:ℝ) * rep1 (x 1)) from funext hSum]
  refine memLp_finsetSum S (fun k _ => ?_)
  have hbase : MemLp (fun x : UnitAddTorus (Fin 2) => g (rep1 (x 0) - (k:ℝ))) 2
      (volume : Measure (UnitAddTorus (Fin 2))) :=
    (memLp_g_rep hgm hg k).comp_measurePreserving mp_eval0
  have := HRTShift.memLp_unimodular_mul
    (φ := fun x : UnitAddTorus (Fin 2) => HRTTransfer.ee ((k:ℝ) * rep1 (x 1)))
    (fun x => by simpa using HRTTransfer.norm_ee _)
    (by
      have hm1 : Measurable (fun x : UnitAddTorus (Fin 2) => rep1 (x 1)) :=
        measurable_rep1.comp (measurable_pi_apply 1)
      exact (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp (measurable_const.mul hm1)))).aestronglyMeasurable)
    hbase
  simpa [mul_comm] using this

/-! ### The 90° rotation, and what it does to indices

`coeff_zakTor_eq_W` and `HRTZakL2.repr_zakL2` do NOT describe the same `L²` element — they differ by
the quarter-turn.  This section pins the rotation's action on the Fourier index by MACHINE CHECK,
so the identification below rests on a computation rather than on a convention guess.

Chaining `mFourier_rotT` through `mFourierCoeff` gives

    mFourierCoeff (F ∘ rotT) n = mFourierCoeff F ![n 1, -(n 0)]

and substituting `coeff_zakTor_eq_W` turns the right side into `W 1 g (n 1) (n 0)` — which is
exactly `repr_zakL2`.  So the bridge reads

    zakL2 g  =  (the L² class of zakTor g) ∘ rotT

and NOT `zakL2 g = toLp (zakTor g)`. -/

/-- **Negating the POINT is the same as negating the INDEX.**  Mathlib has `fourier_neg` (negate the
index) and `fourier_neg'` (the `toCircle` form), but nothing for a negated argument; both sides here
reduce to the same conjugate. -/
theorem fourier_neg_point {T' : ℝ} (n : ℤ) (x : AddCircle T') :
    fourier n (-x) = fourier (-n) x := by
  rw [fourier_apply, smul_neg, fourier_neg', fourier_neg]

/-- The 90° torus rotation `(t,ω) ↦ (ω,−t)` — the Fourier rotation, as a map of the two-torus. -/
noncomputable def rotT (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![x 1, -(x 0)]

/-- **How `mFourier` transforms under the rotation.**  No measure theory is involved, which is what
makes this a clean way to pin the convention. -/
theorem mFourier_rotT (n : Fin 2 → ℤ) (x : UnitAddTorus (Fin 2)) :
    UnitAddTorus.mFourier n (rotT x)
      = UnitAddTorus.mFourier (![-(n 1), n 0]) x := by
  rw [mFourier_two, mFourier_two]
  simp only [rotT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [fourier_neg_point]
  ring

/-! ### Which coordinate the transported shift actually moves — a NEGATIVE result

`HRTShift.Sa = M_φ ∘ R_a` is built on `rot a p = (p.1 - a, p.2)`, a translation of the FIRST product
coordinate.  The two lemmas below show that this is **not** the operator the bridge route delivers,
and identify the one that is.

**Why the question arises.**  `zakL2 g = (zakTor g) ∘ rotT` (forced by `mFourier_rotT` +
`coeff_zakTor_eq_W` + `repr_zakL2`), and `rotT` is a quarter-turn, so it carries a translation in
one coordinate to a translation in the OTHER.  `HRTShift.zak_shift_wrap` is a `t`-translation in
the pointwise picture — `zakTor`'s coordinate `0` — so after `rotT` it lands on coordinate `1`.

**What the shear does.**  `zakSheared` is `zakL2` pre-composed with
`prodToTorusHaar = piFinTwo.symm ∘ (p ↦ (p.1, p.2 - p.1))`, so one might hope the shear absorbs the
discrepancy.  `shear_rot` shows it does not: it turns `rot a` into an ANTI-DIAGONAL shift
`(c₀ - a, c₁ + a)`, whereas the transported identity needs `(c₀, c₁ - a)`.  These differ by
`(-a, +2a)`, so no choice of sign or direction reconciles them.

**The operator that works** is `shear_rotSnd`'s: translate the SECOND product coordinate.

None of this invalidates anything already proved — `norm_Sa` and friends are true statements about
`Sa`; `Sa` is simply not the intertwiner for THIS route.  Recorded as lemmas rather than prose so
the next attempt cannot re-assume the comfortable answer. -/

/-- **`rot a`, after the shear, is an ANTI-DIAGONAL torus shift** — not a single-coordinate one. -/
theorem shear_rot (a : ℝ) (p : UnitAddCircle × UnitAddCircle) :
    ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
        ((HRTShift.rot a p).1, (HRTShift.rot a p).2 - (HRTShift.rot a p).1))
      = ![p.1 - ((a:ℝ) : UnitAddCircle),
          (p.2 - p.1) + ((a:ℝ) : UnitAddCircle)] := by
  funext i
  fin_cases i <;>
    simp [HRTShift.rot, MeasurableEquiv.piFinTwo] <;> abel

/-- **Shifting the SECOND product coordinate gives the coordinate-1 torus shift** — which is what
the transported pointwise `t`-shift requires.  This is the intertwiner the route needs. -/
theorem shear_rotSnd (a : ℝ) (p : UnitAddCircle × UnitAddCircle) :
    ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
        ((p.1, p.2 - ((a:ℝ) : UnitAddCircle)).1,
         (p.1, p.2 - ((a:ℝ) : UnitAddCircle)).2 - (p.1, p.2 - ((a:ℝ) : UnitAddCircle)).1))
      = ![p.1, (p.2 - p.1) - ((a:ℝ) : UnitAddCircle)] := by
  funext i
  fin_cases i <;> simp [MeasurableEquiv.piFinTwo] <;> abel

/-! ### The intertwiner this route needs — the second-coordinate rotation

`shear_rotSnd` identified the map; this builds it as an operator.  `RaSnd` is the analogue of
`HRTShift.Ra` with the factors swapped, and it is an isometry for the same reason.  What remains for
a full replacement of `Sa` is the matching wrap multiplier (the analogue of `HRTShift.MphiTorus`),
whose phase must be recomputed for this coordinate — do not reuse `torusPhi` unchecked.

**Gotcha worth recording:** writing `haarAddCircle` unqualified here does NOT refer to
`AddCircle.haarAddCircle`.  With `autoImplicit` on it becomes an auto-bound implicit VARIABLE, and
the failure surfaces as `failed to synthesize haarAddCircle.IsAddRightInvariant` — which reads like
a missing instance on the real measure rather than a name that silently turned into a variable.
Qualify it. -/

/-- **Rotation of the SECOND (frequency) coordinate preserves Haar on the torus.**  Mirrors
`HRTZakL2.measurePreserving_rotFst` with the factors swapped. -/
theorem measurePreserving_rotSnd (a : UnitAddCircle) :
    MeasurePreserving (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 - a))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
  have h1 : MeasurePreserving (fun x : UnitAddCircle => x - a)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    simpa [sub_eq_add_neg] using
      measurePreserving_add_right (AddCircle.haarAddCircle : Measure UnitAddCircle) (-a)
  exact (MeasurePreserving.id _).prod h1

/-- The second-coordinate rotation with a REAL shift — the shape the campaign states shifts in. -/
noncomputable abbrev rotSnd (a : ℝ) :
    UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle :=
  fun p => (p.1, p.2 - ((a : ℝ) : UnitAddCircle))

theorem measurePreserving_rotSnd' (a : ℝ) :
    MeasurePreserving (rotSnd a) HRTShift.T2mu HRTShift.T2mu :=
  measurePreserving_rotSnd ((a : ℝ) : UnitAddCircle)

/-- **`R'_a` as a linear isometry of `L²(T²)`** — the second-coordinate analogue of `HRTShift.Ra`. -/
noncomputable def RaSnd (a : ℝ) : Lp ℂ 2 HRTShift.T2mu →ₗᵢ[ℂ] Lp ℂ 2 HRTShift.T2mu :=
  Lp.compMeasurePreservingₗᵢ ℂ (rotSnd a) (measurePreserving_rotSnd' a)

/-- **`R'_a` is an isometry**, exactly as `HRTShift.norm_rot_comp` is for the first coordinate. -/
theorem norm_RaSnd (a : ℝ) (f : Lp ℂ 2 HRTShift.T2mu) : ‖RaSnd a f‖ = ‖f‖ :=
  (RaSnd a).norm_map f

/-! ### The wrap multiplier, and `S'_a` — the candidate replacement for `S_a`

`HRTShift.torusPhi a q = if q.1 ∈ wrapArc a then fourier (-1) q.2 else 1`: the wrap is decided by
the FIRST coordinate and the phase carried by the SECOND.  After the quarter-turn both change.

Tracking it through `zakL2 g = (zakTor g) ∘ rotT`: the pointwise arguments are `t = rep1 (x 1)` and
`ω = rep1 (-(x 0))`.  So the wrap is decided by the coordinate carrying `t` — now `x 1` — while the
phase `e(-ω)` is read at `-(x 0)`, and `fourier_neg_point` turns `fourier (-1) (-(x 0))` into
`fourier 1 (x 0)`.  **The character's sign flips**, which is easy to miss.  Pulling back through the
shear (`prodToTorusHaar p` has coordinate 1 equal to `p.2 - p.1`) gives `phiSnd` below.

**Status of `phiSnd`: it is a CANDIDATE.**  Its unimodularity and measurability are proved
unconditionally, so `S'_a` is an honest isometry whatever else is true — but the claim that it is
the correct intertwiner rests on the coordinate bookkeeping just described and is NOT yet
machine-checked.  It becomes a theorem only when the transported shift identity is proved.  Do not
cite it as established before then. -/

open scoped Classical in
/-- **Candidate wrap multiplier for the second-coordinate route.**  Compare `HRTShift.torusPhi`:
the wrap condition moves to `p.2 - p.1` and the character sign flips to `+1`. -/
noncomputable def phiSnd (a : ℝ) (p : UnitAddCircle × UnitAddCircle) : ℂ :=
  if (p.2 - p.1) ∈ HRTShift.wrapArc a then fourier 1 p.1 else 1

/-- Unimodular — so `M_φ'` is an isometry.  Unconditional. -/
theorem norm_phiSnd (a : ℝ) (p : UnitAddCircle × UnitAddCircle) : ‖phiSnd a p‖ = 1 := by
  unfold phiSnd
  split
  · first
      | exact Circle.norm_coe _
      | simp [fourier]
      | simp
  · simp

/-- Measurable — the wrap arc is measurable and the character is continuous.  Unconditional. -/
theorem measurable_phiSnd (a : ℝ) : Measurable (phiSnd a) := by
  unfold phiSnd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_snd.sub measurable_fst) (HRTShift.measurableSet_wrapArc a)
  · exact (map_continuous (fourier (T := (1:ℝ)) 1)).measurable.comp measurable_fst

/-- `M_φ'` — multiplication by the candidate wrap multiplier. -/
noncomputable def MphiSnd (a : ℝ) :
    Lp ℂ 2 HRTShift.T2mu →L[ℂ] Lp ℂ 2 HRTShift.T2mu :=
  HRTShift.multLC (μ := HRTShift.T2mu) (measurable_phiSnd a) (norm_phiSnd a)

theorem norm_MphiSnd (a : ℝ) (f : Lp ℂ 2 HRTShift.T2mu) : ‖MphiSnd a f‖ = ‖f‖ := by
  show ‖HRTShift.multL (μ := HRTShift.T2mu) (measurable_phiSnd a) (norm_phiSnd a) f‖ = ‖f‖
  exact HRTShift.norm_multL _ _ f

/-- **`S'_a = M_φ' ∘ R'_a`** — the candidate Zak shift for the second-coordinate route, the
structural analogue of `HRTShift.Sa`. -/
noncomputable def SaSnd (a : ℝ) : Lp ℂ 2 HRTShift.T2mu →L[ℂ] Lp ℂ 2 HRTShift.T2mu :=
  (MphiSnd a).comp (RaSnd a).toContinuousLinearMap

/-- **`S'_a` is an isometry**, exactly as `HRTShift.norm_Sa` is for `S_a`.  This holds regardless of
whether `phiSnd` is the correct intertwiner — the twist is unimodular and the rotation preserves
Haar, and that is all an isometry needs. -/
theorem norm_SaSnd (a : ℝ) (f : Lp ℂ 2 HRTShift.T2mu) : ‖SaSnd a f‖ = ‖f‖ := by
  show ‖MphiSnd a ((RaSnd a).toContinuousLinearMap f)‖ = ‖f‖
  rw [norm_MphiSnd]
  exact (RaSnd a).norm_map f

/-! ### The transported shift identity, pointwise

This is the step the whole bridge exists to enable, and it CONFIRMS BY COMPUTATION the coordinate
claim that `shear_rot` was argued against: a real translation of the window becomes a translation of
`zakTor`'s **first** coordinate — hence, after `rotT`, of torus coordinate **1**, which is what
`shear_rotSnd`'s operator moves and `HRTShift.rot` does not.

The bookkeeping is carried by `rep1_sub`: taking the fundamental-domain representative AFTER
shifting on the circle equals `HRTShift.shiftRep` applied to the representative.  That is exactly
the wrap accounting `zak_shift_wrap` performs, so the two line up with no leftover correction. -/

/-- **`rep1` intertwines the circle shift with `shiftRep`.**  Stated for `a ∈ [0,1)`; the wrap case
`t < a` re-enters the fundamental domain via `AddCircle.coe_add_period`. -/
theorem rep1_sub (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (x : UnitAddCircle) :
    rep1 (x - ((a : ℝ) : UnitAddCircle)) = HRTShift.shiftRep a (rep1 x) := by
  have hx : ((rep1 x : ℝ) : UnitAddCircle) = x := AddCircle.coe_equivIco
  have hmem := rep1_mem x
  set t := rep1 x with ht
  unfold HRTShift.shiftRep
  by_cases hlt : t < a
  · have h1 : x - ((a : ℝ) : UnitAddCircle) = ((t - a + 1 : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_add_period 1 (t - a), ← hx]
      rfl
    rw [h1, rep1_coe ⟨by linarith [hmem.1], by linarith [hmem.2]⟩, if_pos hlt]
  · have h1 : x - ((a : ℝ) : UnitAddCircle) = ((t - a : ℝ) : UnitAddCircle) := by
      rw [← hx]
      rfl
    rw [h1, rep1_coe ⟨by linarith [not_lt.mp hlt], by linarith [hmem.2]⟩, if_neg hlt]

/-- **THE TRANSPORTED SHIFT IDENTITY, pointwise on the torus.**

    zakTor (g(·-a)) x = wrapPhi a (rep1 (x 0), rep1 (x 1)) · zakTor g (x 0 - a, x 1)

A real translation of the window becomes a translation of the FIRST torus coordinate, times the
wrap multiplier.  Combined with `mFourier_rotT` (which puts `zakL2 = zakTor ∘ rotT`) this is the
machine-checked form of the coordinate analysis: after the quarter-turn the shift moves torus
coordinate 1, so `shear_rotSnd`'s operator is the right one and `HRTShift.rot` is not. -/
theorem zakTor_shift (g : ℝ → ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (x : UnitAddTorus (Fin 2)) :
    zakTor (fun y => g (y - a)) x
      = HRTShift.wrapPhi a (rep1 (x 0), rep1 (x 1))
        * zakTor g (![x 0 - ((a : ℝ) : UnitAddCircle), x 1]) := by
  unfold zakTor
  rw [HRTShift.zak_shift_wrap g a (rep1 (x 0)) (rep1 (x 1))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [rep1_sub a ha0 ha1 (x 0)]

/-! ### The rotation is measure preserving

The last input needed to state the bridge as an `L²` identity rather than a coefficient-by-
coefficient one.  `rotT` factors as `piFinTwo.symm ∘ (a,b) ↦ (b,-a) ∘ piFinTwo`, and the middle map
is `Prod.swap` followed by negating the second coordinate — both Haar-preserving.

Note `Measure.measurePreserving_swap` needs its `Measure.` prefix; `measurePreserving_swap` alone is
an unknown identifier even with `MeasureTheory` open. -/

/-- `(a,b) ↦ (b,-a)` on the product preserves Haar. -/
theorem mp_sigma :
    MeasurePreserving (fun q : UnitAddCircle × UnitAddCircle => (q.2, -q.1))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
  have hneg : MeasurePreserving (fun q : UnitAddCircle × UnitAddCircle => (q.1, -q.2))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
  exact hneg.comp Measure.measurePreserving_swap

/-- **The 90° rotation preserves the torus measure**, so it induces an isometry of `L²(T²)` and the
bridge can be stated as an equality of `L²` elements. -/
theorem measurePreserving_rotT :
    MeasurePreserving rotT (volume : Measure (UnitAddTorus (Fin 2)))
      (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [HRTZakL2.torusVolume_eq_piHaar]
  have hfwd : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    rw [← HRTZakL2.torusVolume_eq_piHaar, ← HRTZakL2.volume_prod_eq_haar_prod]
    exact HRTZakL2.volumePreserving_torusProd
  have hbwd := hfwd.symm (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
  have hfun : rotT
      = ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
          ∘ (fun q : UnitAddCircle × UnitAddCircle => (q.2, -q.1)))
        ∘ (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)) := by
    funext x i
    fin_cases i <;> rfl
  rw [hfun]
  exact (hbwd.comp mp_sigma).comp hfwd

/-! ### The coefficient law for composition with the rotation

`MeasurePreserving.integral_comp` needs a measurable EMBEDDING, so `rotT` is repackaged as a
measurable equivalence — it is `piFinTwo` then `prodComm` then negate-the-second-coordinate then
`piFinTwo.symm`, each of which Mathlib already provides as a `≃ᵐ`. -/

/-- `rotT` as a measurable EQUIVALENCE. -/
noncomputable def rotTEquiv : UnitAddTorus (Fin 2) ≃ᵐ UnitAddTorus (Fin 2) :=
  ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).trans
    (MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.refl UnitAddCircle).prodCongr (MeasurableEquiv.neg UnitAddCircle)))).trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm

theorem rotTEquiv_apply : (rotTEquiv : UnitAddTorus (Fin 2) → UnitAddTorus (Fin 2)) = rotT := by
  funext x i
  fin_cases i <;> rfl

theorem measurableEmbedding_rotT : MeasurableEmbedding rotT := by
  rw [← rotTEquiv_apply]
  exact rotTEquiv.measurableEmbedding

/-- Index bookkeeping: `![-(n 0), -(n 1)]` IS `-n`. -/
theorem neg_index (n : Fin 2 → ℤ) : (![-(n 0), -(n 1)] : Fin 2 → ℤ) = -n := by
  funext i; fin_cases i <;> rfl

/-- …and the index the rotation feeds back. -/
theorem neg_rot_index (n : Fin 2 → ℤ) :
    -(![n 1, -(n 0)] : Fin 2 → ℤ) = ![-(n 1), n 0] := by
  funext i; fin_cases i <;> simp

/-- **THE COEFFICIENT LAW FOR THE ROTATION.**

    mFourierCoeff (F ∘ rotT) n = mFourierCoeff F ![n 1, -(n 0)]

Combined with `coeff_zakTor_eq_W` this turns the right-hand side into `W 1 g (n 1) (n 0)`, which is
exactly `HRTZakL2.repr_zakL2` — so `zakL2 g` and `(zakTor g) ∘ rotT` have the SAME Fourier
coefficients, and `mFourierBasis.repr` is injective. -/
theorem coeff_comp_rotT (F : UnitAddTorus (Fin 2) → ℂ) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => F (rotT x)) n
      = UnitAddTorus.mFourierCoeff F (![n 1, -(n 0)]) := by
  have hrw : ∀ x : UnitAddTorus (Fin 2),
      UnitAddTorus.mFourier (-n) x
        = UnitAddTorus.mFourier (![-(n 1), n 0]) (rotT x) := by
    intro x
    rw [mFourier_rotT]
    congr 1
  have h0 : UnitAddTorus.mFourierCoeff (fun x => F (rotT x)) n
      = ∫ x : UnitAddTorus (Fin 2),
          UnitAddTorus.mFourier (![-(n 1), n 0]) (rotT x) • F (rotT x)
          ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
    show (∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier (-n) x • F (rotT x)
        ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))) = _
    exact integral_congr_ae (.of_forall (fun x => by simp only [hrw x]))
  rw [h0, ← HRTZakL2.torusVolume_eq_piHaar]
  rw [MeasurePreserving.integral_comp measurePreserving_rotT measurableEmbedding_rotT
    (fun y => UnitAddTorus.mFourier (![-(n 1), n 0]) y • F y)]
  show _ = ∫ y : UnitAddTorus (Fin 2),
      UnitAddTorus.mFourier (-(![n 1, -(n 0)] : Fin 2 → ℤ)) y • F y
      ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  rw [neg_rot_index, HRTZakL2.torusVolume_eq_piHaar]

/-! ### THE BRIDGE, as an `L²` identity

Everything assembles here.  `coeff_comp_rotT` + `coeff_zakTor_eq_W` give the coefficients of
`(zakTor g) ∘ rotT`; `HRTZakL2.repr_zakL2` gives those of `zakL2 g`; they agree, and
`mFourierBasis.repr` is a linear isometry equivalence, hence injective. -/

/-- `mFourierCoeff` only sees the a.e. class — it is an integral. -/
theorem mFourierCoeff_congr_ae {F G : UnitAddTorus (Fin 2) → ℂ}
    (h : F =ᵐ[(volume : Measure (UnitAddTorus (Fin 2)))] G) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff F n = UnitAddTorus.mFourierCoeff G n := by
  show (∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier (-n) x • F x
      ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))))
      = ∫ x : UnitAddTorus (Fin 2), UnitAddTorus.mFourier (-n) x • G x
      ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  rw [← HRTZakL2.torusVolume_eq_piHaar]
  exact integral_congr_ae (h.mono (fun x hx => by simp only [hx]))

/-! #### The last obstacle, and how it was cleared

Stated the obvious way, the bridge does NOT typecheck, for a structural rather than mathematical
reason.  Recorded because the error is opaque and the fix is not the one it suggests.

    zakL2 g = Lp.compMeasurePreserving rotT measurePreserving_rotT (toLp (zakTor g))   -- FAILS

`HRTZakL2.zakL2` carries no return-type ascription (deliberately — see the comment there), so its
type is whatever `mFourierBasis.repr.symm` produces: `Lp ℂ 2 volume` where `volume` is taken with
`MeasureSpace.pi … fun i => instMeasureSpaceUnitAddCircle`, the HAAR instance local to
`AddCircleMulti.lean`.  `measurePreserving_rotT` above is stated with `volume` as elaborated HERE,
which resolves to `MeasureSpace.pi … fun i => AddCircle.measureSpace 1`.

`torusVolume_eq_piHaar` proves those two measures EQUAL, but `Lp ℂ 2 μ` is indexed by the measure
TERM, so equal-but-distinct terms give **distinct types**, and no `rw` can bridge a type mismatch.
The error is a `Type mismatch` on the `Lp` subtype, not a failed unifier hint.

This is the third and sharpest form of the Haar/`volume` trap recorded above: at the level of
integrals it was cured by `Measure.pi (fun _ => haarAddCircle)` being an explicit term
(`coeff_eq_prod`), but at the level of `Lp` TYPES that escape is unavailable.

**THE FIX** — and it does not require touching `HRTZakL2`.  `mFourierCoeff` unfolds to an integral
against `Measure.pi (fun _ => haarAddCircle)` by `rfl` (that is exactly what makes `coeff_eq_prod`
work), so `zakL2`'s ambient measure is **DEFEQ** to that explicit term.  Restating the two inputs
(`measurePreserving_rotT_haar`, `memLp_zakTor_haar`) over the same explicit term therefore lands
them in the same `Lp` type, and the equation typechecks.

The lesson generalises: when an `Lp` type mismatch comes from two equal-but-distinct measure TERMS,
look for a term both sides are DEFEQ to and restate over it — do not reach for a transport
isomorphism, and do not assume the upstream definition must change. -/

/-! #### Clearing the obstacle — restate over the EXPLICIT measure term

Route (b) above, and it turns out not to need `HRTZakL2` touched at all.  `mFourierCoeff` unfolds to
an integral against `Measure.pi (fun _ => haarAddCircle)` by `rfl` (that is what makes
`coeff_eq_prod` work), so `zakL2`'s ambient measure is DEFEQ to that explicit term.  Restating the
two inputs over the same term therefore lands them in the same `Lp` type. -/

/-- `mFourier` is pointwise unimodular. -/
theorem norm_mFourier (n : Fin 2 → ℤ) (x : UnitAddTorus (Fin 2)) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  have h : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y‖ = 1 := by
    intro m y
    first
      | exact Circle.norm_coe _
      | simp [fourier]
      | simp
  rw [mFourier_two, norm_mul, h, h, mul_one]

/-- The integrability hypothesis `coeff_zakTor_eq_W` carries, discharged from `memLp_zakTor`:
the integrand is an `L²` function times a unimodular character on a FINITE measure space. -/
theorem integrable_mFourier_zakTor {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (n : Fin 2 → ℤ) :
    Integrable
      (fun p : UnitAddCircle × UnitAddCircle =>
        UnitAddTorus.mFourier (-n)
            ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
          • zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p))
      (volume : Measure (UnitAddCircle × UnitAddCircle)) := by
  have hcomp : MemLp (fun p : UnitAddCircle × UnitAddCircle =>
      zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)) 2
      (volume : Measure (UnitAddCircle × UnitAddCircle)) :=
    (memLp_zakTor hcs hgm hg).comp_measurePreserving
      ((HRTZakL2.volumePreserving_torusProd).symm _)
  have hmul : MemLp (fun p : UnitAddCircle × UnitAddCircle =>
      UnitAddTorus.mFourier (-n)
          ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)
        * zakTor g ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm p)) 2
      (volume : Measure (UnitAddCircle × UnitAddCircle)) :=
    HRTShift.memLp_unimodular_mul (fun p => norm_mFourier _ _)
      ((map_continuous (UnitAddTorus.mFourier (-n))).measurable.comp
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm.measurable).aestronglyMeasurable
      hcomp
  exact hmul.integrable (by norm_num)

theorem measurePreserving_rotT_haar :
    MeasurePreserving rotT
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
  rw [← HRTZakL2.torusVolume_eq_piHaar]
  exact measurePreserving_rotT

theorem memLp_zakTor_haar {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (zakTor g) 2
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
  rw [← HRTZakL2.torusVolume_eq_piHaar]
  exact memLp_zakTor hcs hgm hg

/-- **THE BRIDGE.**  On the compactly supported class,

    zakL2 g = (the L² class of zakTor g) ∘ rotT

an equality of `L²(T²)` elements.  It is NOT `zakL2 g = toLp (zakTor g)` — the quarter-turn is
essential, and dropping it would be invisible to both the build and `#print axioms`. -/
theorem zakL2_eq_zakTor_comp_rotT {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    HRTZakL2.zakL2 (θ := 1) one_pos le_rfl hg
      = Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
          ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)) := by
  refine UnitAddTorus.mFourierBasis.repr.injective ?_
  ext i
  rw [HRTZakL2.repr_zakL2, UnitAddTorus.mFourierBasis_repr]
  have hae : (↑↑(Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
        ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)))
      : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[(volume : Measure (UnitAddTorus (Fin 2)))] (fun x => zakTor g (rotT x)) := by
    rw [HRTZakL2.torusVolume_eq_piHaar]
    refine (Lp.coeFn_compMeasurePreserving _ measurePreserving_rotT_haar).trans ?_
    exact measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
      ((memLp_zakTor_haar hcs hgm hg).coeFn_toLp)
  rw [mFourierCoeff_congr_ae hae i, coeff_comp_rotT (zakTor g) i]
  rw [coeff_zakTor_eq_W hcs (![i 1, -(i 0)])
    (integrable_mFourier_zakTor hcs hgm hg (![i 1, -(i 0)]))]
  simp

/-! ### Lifting the shift identity to `L²`

`zakTor_shift` is pointwise; these package its two ingredients as operators on `L²(T²)` — the
first-coordinate torus shift `tauT` (measure preserving, so it induces an isometry) and the wrap
multiplier `phiTor` (unimodular and measurable, so multiplication by it is an isometry). -/

/-- The first-coordinate shift on the pi-torus — the move `zakTor_shift` performs. -/
noncomputable def tauT (a : ℝ) (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![x 0 - ((a : ℝ) : UnitAddCircle), x 1]

/-- It preserves the Haar pi-measure, via `HRTZakL2.measurePreserving_rotFst` on the product. -/
theorem measurePreserving_tauT (a : ℝ) :
    MeasurePreserving (tauT a)
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
  have hprod : MeasurePreserving
      (fun p : UnitAddCircle × UnitAddCircle => (p.1 - ((a : ℝ) : UnitAddCircle), p.2))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) :=
    HRTZakL2.measurePreserving_rotFst ((a : ℝ) : UnitAddCircle)
  have hfwd : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    rw [← HRTZakL2.torusVolume_eq_piHaar, ← HRTZakL2.volume_prod_eq_haar_prod]
    exact HRTZakL2.volumePreserving_torusProd
  have hbwd := hfwd.symm (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
  have hfun : tauT a
      = ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
          ∘ (fun p : UnitAddCircle × UnitAddCircle => (p.1 - ((a : ℝ) : UnitAddCircle), p.2)))
        ∘ (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)) := by
    funext x i
    fin_cases i <;> rfl
  rw [hfun]
  exact (hbwd.comp hprod).comp hfwd

/-- The wrap multiplier, read on the torus through the representatives. -/
noncomputable def phiTor (a : ℝ) (x : UnitAddTorus (Fin 2)) : ℂ :=
  HRTShift.wrapPhi a (rep1 (x 0), rep1 (x 1))

theorem norm_phiTor (a : ℝ) (x : UnitAddTorus (Fin 2)) : ‖phiTor a x‖ = 1 :=
  HRTShift.norm_wrapPhi a _

theorem measurable_phiTor (a : ℝ) : Measurable (phiTor a) := by
  unfold phiTor HRTShift.wrapPhi
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_rep1.comp
      (measurable_pi_apply (0 : Fin 2) (X := fun _ : Fin 2 => UnitAddCircle))) measurableSet_Iio
  · refine Complex.measurable_exp.comp ?_
    refine Measurable.neg ?_
    refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
    exact measurable_rep1.comp
      (measurable_pi_apply (1 : Fin 2) (X := fun _ : Fin 2 => UnitAddCircle))

/-- **The shift identity as a FUNCTION equality** — `zakTor_shift` holds at every point, so no a.e.
reasoning is needed to pass to `L²`: the two functions are literally equal. -/
theorem zakTor_shift_eq (g : ℝ → ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    zakTor (fun y => g (y - a)) = fun x => phiTor a x * zakTor g (tauT a x) :=
  funext (fun x => zakTor_shift g a ha0 ha1 x)

/-- The translated window keeps compact support. -/
theorem hasCompactSupport_shift {g : ℝ → ℂ} (hcs : HasCompactSupport g) (a : ℝ) :
    HasCompactSupport (fun y => g (y - a)) :=
  hcs.comp_homeomorph (Homeomorph.subRight a)

/-- …and stays `L²` (translation preserves Lebesgue measure). -/
theorem memLp_shift_real {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) (a : ℝ) :
    MemLp (fun y => g (y - a)) 2 (volume : Measure ℝ) :=
  hg.comp_measurePreserving (measurePreserving_sub_right (volume : Measure ℝ) a)

/-- **THE SHIFT IDENTITY IN `L²`.**  The `L²` class of `zakTor` of the translated window is the
wrap multiplier times the class of `zakTor g` pre-composed with the torus shift.  Both `phiTor`
(unimodular) and `tauT` (measure preserving) are isometries, so this exhibits the translation as a
composition of two isometries — the structure the cocycle argument consumes. -/
theorem toLp_zakTor_shift {g : ℝ → ℂ} (hcs : HasCompactSupport g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hgm' : Measurable (fun y => g (y - a)))
    (hMul : MemLp (fun x => phiTor a x * zakTor g (tauT a x)) 2
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))) :
    (memLp_zakTor_haar (hasCompactSupport_shift hcs a) hgm' (memLp_shift_real hg a)).toLp
        (zakTor (fun y => g (y - a)))
      = hMul.toLp (fun x => phiTor a x * zakTor g (tauT a x)) :=
  MemLp.toLp_congr _ _ (by rw [zakTor_shift_eq g a ha0 ha1])

/-! ### Conjugating the shift through the rotation

To move `toLp_zakTor_shift` across the bridge, the torus shift `tauT` must be conjugated by `rotT`.
The result is the SECOND-coordinate shift — which is precisely what `shear_rotSnd` predicted and
what `HRTShift.rot` is not.  Proving `sigmaT_conj` therefore closes the loop on the refutation:
it is the same fact a third time, now as an equation between the two maps themselves. -/

/-- The SECOND-coordinate shift on the pi-torus. -/
noncomputable def sigmaT (a : ℝ) (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![x 0, x 1 - ((a : ℝ) : UnitAddCircle)]

/-- **The conjugate of the first-coordinate shift by the rotation is the SECOND-coordinate shift.**
`tauT a ∘ rotT = rotT ∘ sigmaT a`. -/
theorem sigmaT_conj (a : ℝ) : (tauT a) ∘ rotT = rotT ∘ (sigmaT a) := by
  funext x i
  fin_cases i <;> rfl

/-- It preserves the Haar pi-measure, by the same route as `measurePreserving_tauT` with the
factors swapped (`measurePreserving_rotSnd` on the product). -/
theorem measurePreserving_sigmaT (a : ℝ) :
    MeasurePreserving (sigmaT a)
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
  have hprod := measurePreserving_rotSnd ((a : ℝ) : UnitAddCircle)
  have hfwd : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    rw [← HRTZakL2.torusVolume_eq_piHaar, ← HRTZakL2.volume_prod_eq_haar_prod]
    exact HRTZakL2.volumePreserving_torusProd
  have hbwd := hfwd.symm (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
  have hfun : sigmaT a
      = ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
          ∘ (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 - ((a : ℝ) : UnitAddCircle))))
        ∘ (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)) := by
    funext x i
    fin_cases i <;> rfl
  rw [hfun]
  exact (hbwd.comp hprod).comp hfwd

/-! ### THE SHIFT IDENTITY AT THE `zakL2` LEVEL

This is what the bridge was built for.  `zakL2` is defined for EVERY `L²` window, so this is the
statement the density extension can act on — unlike anything phrased through `zakTor`, which
`summable_not_implied_by_memLp` shows cannot serve a general window. -/

/-- `multLC` acts by pointwise multiplication on representatives.  `HRTShift` builds it through
`AEEqFun.mk`, so this unpacks that; there was no `coeFn` lemma for it. -/
theorem coeFn_multLC {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℂ}
    (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1) (f : Lp ℂ 2 μ) :
    (↑↑(HRTShift.multLC hφm hφ f) : α → ℂ) =ᵐ[μ] fun x => φ x * (↑↑f : α → ℂ) x := by
  filter_upwards [AEEqFun.coeFn_mul (HRTShift.phiAE (μ := μ) φ hφm) (f : α →ₘ[μ] ℂ),
    HRTShift.coeFn_phiAE (μ := μ) φ hφm] with x h1 h2
  show (⇑(HRTShift.phiAE (μ := μ) φ hφm * (f : α →ₘ[μ] ℂ))) x = _
  rw [h1, Pi.mul_apply, h2]

/-- The wrap multiplier, conjugated by the rotation — the multiplier the `zakL2` picture sees. -/
noncomputable def phiRot (a : ℝ) (x : UnitAddTorus (Fin 2)) : ℂ := phiTor a (rotT x)

theorem norm_phiRot (a : ℝ) (x : UnitAddTorus (Fin 2)) : ‖phiRot a x‖ = 1 :=
  norm_phiTor a _

theorem measurable_phiRot (a : ℝ) : Measurable (phiRot a) := by
  refine (measurable_phiTor a).comp ?_
  rw [← rotTEquiv_apply]
  exact rotTEquiv.measurable

/-- **THE SHIFT IDENTITY FOR `zakL2`.**  On the compactly supported class,

    zakL2 (g(·-a)) = M_{φ∘rotT} ( C_{σ_a} (zakL2 g) )

where `σ_a` is the SECOND-coordinate torus shift (`sigmaT`) — not the first.  Both factors are
isometries, so the right-hand side is a bounded operator applied to `zakL2 g`, which is exactly the
shape a density argument extends. -/
theorem zakL2_shift {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hgm' : Measurable (fun y => g (y - a))) :
    HRTZakL2.zakL2 (θ := 1) one_pos le_rfl (memLp_shift_real hg a)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (measurable_phiRot a) (norm_phiRot a)
          (Lp.compMeasurePreserving (sigmaT a) (measurePreserving_sigmaT a)
            (HRTZakL2.zakL2 (θ := 1) one_pos le_rfl hg)) := by
  rw [zakL2_eq_zakTor_comp_rotT (hasCompactSupport_shift hcs a) hgm' (memLp_shift_real hg a),
    zakL2_eq_zakTor_comp_rotT hcs hgm hg]
  refine Lp.ext_iff.mpr ?_
  have hL := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar (hasCompactSupport_shift hcs a) hgm' (memLp_shift_real hg a)).toLp
      (zakTor (fun y => g (y - a)))) measurePreserving_rotT_haar
  have hL2 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar (hasCompactSupport_shift hcs a) hgm' (memLp_shift_real hg a)).coeFn_toLp)
  have hR := coeFn_multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_phiRot a) (norm_phiRot a)
    (Lp.compMeasurePreserving (sigmaT a) (measurePreserving_sigmaT a)
      (Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
        ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g))))
  have hR2 := Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
      ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g))) (measurePreserving_sigmaT a)
  have hR3 := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)) measurePreserving_rotT_haar
  have hR4 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar hcs hgm hg).coeFn_toLp)
  filter_upwards [hL, hL2, hR, hR2,
    (measurePreserving_sigmaT a).quasiMeasurePreserving.ae_eq_comp (hR3.trans hR4)]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  show zakTor (fun y => g (y - a)) (rotT x)
      = phiRot a x * zakTor g (rotT (sigmaT a x))
  rw [zakTor_shift g a ha0 ha1 (rotT x)]
  -- `tauT a (rotT x)` and `rotT (sigmaT a x)` are DEFEQ — `sigmaT_conj` is itself an `rfl` —
  -- so `congr` discharges the reindex without needing it explicitly.
  unfold phiRot phiTor
  congr 2

/-! ### Step 2a — `zakL2` as a map on `Lp`

`HRTZakL2.zakL2` is a function of a `MemLp` PROOF, not of an `Lp` ELEMENT, so a density argument
cannot be applied to it as written.  This repackages it.

The one wrinkle: `zakL2_add` carries `Measurable` hypotheses while `Lp` supplies only
`AEStronglyMeasurable`.  Every `Lp` element has a measurable representative
(`AEStronglyMeasurable.mk`), and `zakL2_congr` says `zakL2` sees only the a.e. class, so the fix is
to run everything through that representative — a few lines, not a barrier. -/

/-- A MEASURABLE representative of an `Lp` element. -/
noncomputable def rep (f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ :=
  (Lp.aestronglyMeasurable f).mk _

theorem measurable_rep (f : Lp ℂ 2 (volume : Measure ℝ)) : Measurable (rep f) :=
  ((Lp.aestronglyMeasurable f).stronglyMeasurable_mk).measurable

theorem rep_ae' (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (↑↑f : ℝ → ℂ) =ᵐ[volume] rep f :=
  (Lp.aestronglyMeasurable f).ae_eq_mk

theorem memLp_rep (f : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (rep f) 2 (volume : Measure ℝ) :=
  (Lp.memLp f).ae_eq (rep_ae' f)

/-- `zakL2` of an `Lp` element, through a measurable representative. -/
noncomputable def zakOf (f : Lp ℂ 2 (volume : Measure ℝ)) :=
  HRTZakL2.zakL2 (θ := 1) one_pos le_rfl (memLp_rep f)

/-- …and it does not depend on which representative is chosen. -/
theorem zakOf_congr {f : Lp ℂ 2 (volume : Measure ℝ)} {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume : Measure ℝ)) (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] h) :
    zakOf f = HRTZakL2.zakL2 (θ := 1) one_pos le_rfl hh :=
  HRTZakL2.zakL2_congr one_pos le_rfl _ _ ((rep_ae' f).symm.trans hae)

theorem zakOf_add (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    zakOf (f + g) = zakOf f + zakOf g := by
  have hsum : MemLp (fun t => rep f t + rep g t) 2 (volume : Measure ℝ) :=
    (memLp_rep f).add (memLp_rep g)
  have hae : (↑↑(f + g) : ℝ → ℂ) =ᵐ[volume] fun t => rep f t + rep g t := by
    filter_upwards [Lp.coeFn_add f g, rep_ae' f, rep_ae' g] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  rw [zakOf_congr hsum hae]
  exact HRTZakL2.zakL2_add one_pos le_rfl (measurable_rep f) (measurable_rep g)
    (memLp_rep f) (memLp_rep g) hsum

theorem zakOf_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    zakOf (c • f) = c • zakOf f := by
  have hsm : MemLp (fun t => c * rep f t) 2 (volume : Measure ℝ) := (memLp_rep f).const_mul c
  have hae : (↑↑(c • f) : ℝ → ℂ) =ᵐ[volume] fun t => c * rep f t := by
    filter_upwards [Lp.coeFn_smul c f, rep_ae' f] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  rw [zakOf_congr hsm hae]
  exact HRTZakL2.zakL2_smul one_pos le_rfl c (memLp_rep f) hsm

/-- **`zakL2` as a LINEAR MAP on `Lp`.** -/
noncomputable def zakLM : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ]
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) where
  toFun := zakOf
  map_add' := zakOf_add
  map_smul' := zakOf_smul

/-! #### The isometry, and hence the continuous linear map

`‖f‖²_{L²(ℝ)} = ∫‖f‖²` on one side, `‖⟨W⟩‖²_{ℓ²} = ∫‖g‖²` (Parseval, `hasSum_W_sq`) on the other,
and `HRTZakL2.norm_zakL2` connects `zakL2` to the `ℓ²` norm of its `W` array. -/

/-- The `L²(ℝ)` norm squared IS the integral of the squared modulus. -/
theorem normSq_Lp (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ x, ‖(↑↑f : ℝ → ℂ) x‖ ^ 2 := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat]
  have hnn : (0:ℝ) ≤ ∫ a, ‖(↑↑f : ℝ → ℂ) a‖ ^ (2:ℝ) := by positivity
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnn]
  norm_num

/-- **Parseval for the `W` array** — its `ℓ²(ℤ²)` norm squared is `∫‖g‖²`.  The reindex from
`Fin 2 → ℤ` to `ℤ × ℤ` must be a typed `have`; inlining it into the `rw` fails to match, because the
equivalence's projections are only DEFEQ to `i 0` / `i 1`, not syntactically equal. -/
theorem normSq_W {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖(⟨fun i : Fin 2 → ℤ => HRTTransfer.W 1 g (i 1) (i 0),
        HRTZakL2.memℓp_W_pi one_pos le_rfl hg⟩ : lp (fun _ : Fin 2 → ℤ => ℂ) 2)‖ ^ 2
      = ∫ x, ‖g x‖ ^ 2 := by
  have h1 : ‖(⟨fun i : Fin 2 → ℤ => HRTTransfer.W 1 g (i 1) (i 0),
      HRTZakL2.memℓp_W_pi one_pos le_rfl hg⟩ : lp (fun _ : Fin 2 → ℤ => ℂ) 2)‖ ^ 2
      = ∑' i : Fin 2 → ℤ, ‖HRTTransfer.W 1 g (i 1) (i 0)‖ ^ 2 := by
    rw [lp.norm_eq_tsum_rpow (by norm_num)]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    norm_num
  have h2 : ∑' i : Fin 2 → ℤ, ‖HRTTransfer.W 1 g (i 1) (i 0)‖ ^ 2
      = ∑' p : ℤ × ℤ, ‖HRTTransfer.W 1 g p.2 p.1‖ ^ 2 :=
    (piFinTwoEquiv (fun _ : Fin 2 => ℤ)).tsum_eq (fun p : ℤ × ℤ => ‖HRTTransfer.W 1 g p.2 p.1‖ ^ 2)
  rw [h1, h2]
  exact (HRTZakL2.hasSum_W_sq one_pos le_rfl hg).tsum_eq

/-- **`zakOf` IS AN ISOMETRY** — the Zak transform is unitary, here in the form the density argument
needs. -/
theorem norm_zakOf (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖zakOf f‖ = ‖f‖ := by
  have hsq : ‖zakOf f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [zakOf, HRTZakL2.norm_zakL2, normSq_W (memLp_rep f), normSq_Lp f]
    exact integral_congr_ae ((rep_ae' f).mono (fun x hx => by simp only [hx]))
  nlinarith [hsq, norm_nonneg (zakOf f), norm_nonneg f]

/-- **`zakL2` AS A CONTINUOUS LINEAR MAP** — step 2a complete.  This is the object the density
argument acts on: `zakCLM` is defined for EVERY `L²` window, and it is an isometry, so it is
bounded with constant `1`. -/
noncomputable def zakCLM : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) :=
  zakLM.mkContinuous 1 (fun f => by rw [one_mul]; exact le_of_eq (norm_zakOf f))

/-! ### Step 2b — the density foundation

`zakL2_shift` holds on the compactly supported class.  To remove `hcs` the argument is: both sides
are continuous in the window, and the compactly supported class is DENSE, so the identity extends.
This is the density half. -/

/-- The compactly supported class, as a set of `Lp` elements — exactly the hypotheses
`zakL2_shift` consumes (`HasCompactSupport` + `Measurable`, up to a.e. equality). -/
def CS : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {f | ∃ g : ℝ → ℂ, HasCompactSupport g ∧ Measurable g ∧ (↑↑f : ℝ → ℂ) =ᵐ[volume] g}

/-- **The compactly supported class is DENSE in `L²(ℝ)`.**  From Mathlib's
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, which supplies a compactly supported CONTINUOUS
approximant — continuity gives the `Measurable` half for free. -/
theorem dense_CS : Dense CS := by
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨g, hcs, hle, hcont, hmem⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp)
      (ε := ENNReal.ofReal (r/2)) (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith)
  refine ⟨hmem.toLp g, ?_, ⟨g, hcs, hcont.measurable, hmem.coeFn_toLp⟩⟩
  rw [Metric.mem_ball, dist_comm, Lp.dist_def]
  have hcongr : eLpNorm ((↑↑f : ℝ → ℂ) - (↑↑(hmem.toLp g) : ℝ → ℂ)) 2 volume
      = eLpNorm ((↑↑f : ℝ → ℂ) - g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    simp [hx]
  rw [hcongr]
  calc (eLpNorm ((↑↑f : ℝ → ℂ) - g) 2 volume).toReal
      ≤ (ENNReal.ofReal (r/2)).toReal := ENNReal.toReal_mono (by simp) hle
    _ = r/2 := by rw [ENNReal.toReal_ofReal (by linarith)]
    _ < r := by linarith

/-- Translation by `a`, as a linear isometry of `L²(ℝ)`. -/
noncomputable def transL (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x - a) (measurePreserving_sub_right volume a)

/-- The second-coordinate torus shift, as a linear isometry of `L²(T²)`. -/
noncomputable def sigL (a : ℝ) :
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      →ₗᵢ[ℂ]
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) :=
  Lp.compMeasurePreservingₗᵢ ℂ (sigmaT a) (measurePreserving_sigmaT a)

/-- The right-hand side of the shift identity, as a continuous map of the window. -/
noncomputable def shiftRHS (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) :=
  HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_phiRot a) (norm_phiRot a) (sigL a (zakCLM f))

theorem continuous_shiftLHS (a : ℝ) :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (transL a f)) :=
  zakCLM.continuous.comp (transL a).continuous

theorem continuous_shiftRHS (a : ℝ) : Continuous (shiftRHS a) :=
  (HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_phiRot a) (norm_phiRot a)).continuous.comp
      ((sigL a).continuous.comp zakCLM.continuous)

/-- **The two sides agree on the compactly supported class** — this is `zakL2_shift`, transported
from the function-level statement to the `Lp`-level one through `zakOf_congr`. -/
theorem eqOn_CS (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Set.EqOn (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (transL a f)) (shiftRHS a) CS := by
  rintro f ⟨g, hcs, hgm, hae⟩
  have hg : MemLp g 2 (volume : Measure ℝ) := (Lp.memLp f).ae_eq hae
  have hgm' : Measurable (fun y => g (y - a)) := hgm.comp (measurable_id.sub_const a)
  -- the translated window represents `transL a f`
  have haeT : (↑↑(transL a f) : ℝ → ℂ) =ᵐ[volume] fun y => g (y - a) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) a)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp hae
  show zakOf (transL a f) = _
  rw [zakOf_congr (memLp_shift_real hg a) haeT]
  rw [zakL2_shift hcs hgm hg a ha0 ha1 hgm']
  show _ = HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_phiRot a) (norm_phiRot a) (sigL a (zakOf f))
  rw [zakOf_congr hg hae]
  rfl

/-- **THE DENSITY EXTENSION — `hcs` IS GONE.**

    zakCLM (transL a f) = M_{φ∘rotT} ( σ_a (zakCLM f) )     for EVERY `f : L²(ℝ)`

`zakL2_shift` held only on the compactly supported class.  Both sides are continuous in the window
(`continuous_shiftLHS`, `continuous_shiftRHS`), they agree on `CS` (`eqOn_CS`), and `CS` is dense
(`dense_CS`) — so they agree everywhere.

This is the step the campaign has been carrying `HasCompactSupport` for.  Note what made it work:
the identity extended is an **operator identity**, and equality of continuous maps IS closed.  The
CONCLUSION of Heil–Speegle (linear independence) is not closed and could never have been extended
this way — see the module docstring of `HRTReduction` and `summable_not_implied_by_memLp`. -/
theorem zakL2_shift_of_memLp (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (transL a f)) = shiftRHS a :=
  Continuous.ext_on dense_CS (continuous_shiftLHS a) (continuous_shiftRHS a) (eqOn_CS a ha0 ha1)

/-! ### Step 3 — the `(√2, √2)` term: a full time–frequency shift

`ZakPeriodization.zak_modulate_timeShift` already gives the pointwise identity

    zak (e^{2πib·} g(·-a)) t ω = e^{2πibt} · zak g (t-a) (ω-a)        (b = a + j)

which at `b = a`, `j = 0` is exactly the `Λ₀` point `(√2, √2)`.  Lifting it to `zakTor` needs the
representative bookkeeping in BOTH coordinates, and the two coordinates behave differently:

* the TIME coordinate wraps, picking up `wrapPhi` (same as `zakTor_shift`);
* the FREQUENCY coordinate does NOT — `zak` is periodic there (`zak_periodic_snd`), so passing to
  the representative costs no phase.  That asymmetry is the line-bundle structure again. -/

/-- **In the frequency coordinate the representative is free.**  `rep1 (x - a)` and `rep1 x - a`
differ by an integer, and `zak` is periodic in `ω`, so the values agree. -/
theorem zak_rep_snd (g : ℝ → ℂ) (t : ℝ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (x : UnitAddCircle) :
    ZakPeriodization.zak g t (rep1 (x - ((a:ℝ) : UnitAddCircle)))
      = ZakPeriodization.zak g t (rep1 x - a) := by
  rw [rep1_sub a ha0 ha1 x]
  unfold HRTShift.shiftRep
  by_cases h : rep1 x < a
  · rw [if_pos h]
    have := ZakPeriodization.zak_periodic_snd g t (rep1 x - a)
    simpa using this
  · rw [if_neg h]

/-- The DIAGONAL torus shift — both coordinates by `a`, which is what a `(a,a)` time–frequency
translate induces. -/
noncomputable def diagT (a : ℝ) (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![x 0 - ((a : ℝ) : UnitAddCircle), x 1 - ((a : ℝ) : UnitAddCircle)]

/-- Re-entering the fundamental domain in the TIME coordinate costs `wrapPhi`.  This is
`zak_shift_window` and `zak_shift_wrap` combined, stated directly about `zak g (t-a)`. -/
theorem zak_sub_wrap (g : ℝ → ℂ) (a t ω : ℝ) :
    ZakPeriodization.zak g (t - a) ω
      = HRTShift.wrapPhi a (t, ω) * ZakPeriodization.zak g (HRTShift.shiftRep a t) ω := by
  rw [← HRTShift.zak_shift_window g a t ω]
  exact HRTShift.zak_shift_wrap g a t ω

/-- **THE `(√2,√2)` INTERTWINER, pointwise on the torus.**  A full time–frequency translate by
`(a,a)` acts on `zakTor` as the DIAGONAL torus shift, times a character in the time representative
and the wrap phase.  The frequency coordinate contributes no phase (`zak_rep_snd`). -/
theorem zakTor_modShift (g : ℝ → ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (x : UnitAddTorus (Fin 2)) :
    zakTor (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a)) x
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((rep1 (x 0) : ℝ) : ℂ))
        * (HRTShift.wrapPhi a (rep1 (x 0), rep1 (x 1) - a)
          * zakTor g (diagT a x)) := by
  unfold zakTor diagT
  rw [ZakPeriodization.zak_modulate_timeShift g a a 0 (by push_cast; ring)
    (rep1 (x 0)) (rep1 (x 1))]
  congr 1
  rw [zak_sub_wrap g a (rep1 (x 0)) (rep1 (x 1) - a)]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [rep1_sub a ha0 ha1 (x 0), zak_rep_snd g (HRTShift.shiftRep a (rep1 (x 0))) a ha0 ha1 (x 1)]

/-- The ANTI-diagonal torus shift.  Conjugating the diagonal shift by the quarter-turn flips one
sign, so this — not `diagT` — is what the `zakL2` picture sees for a `(a,a)` translate. -/
noncomputable def antidiagT (a : ℝ) (x : UnitAddTorus (Fin 2)) : UnitAddTorus (Fin 2) :=
  ![x 0 + ((a : ℝ) : UnitAddCircle), x 1 - ((a : ℝ) : UnitAddCircle)]

/-- **`diagT a ∘ rotT = rotT ∘ antidiagT a`** — computed, not assumed.  The quarter-turn sends the
diagonal shift to the ANTI-diagonal one, exactly as it sent the first-coordinate shift to the
second (`sigmaT_conj`). -/
theorem antidiagT_conj (a : ℝ) : (diagT a) ∘ rotT = rotT ∘ (antidiagT a) := by
  funext x i
  fin_cases i
  · rfl
  · show -(x 0) - ((a : ℝ) : UnitAddCircle) = -(x 0 + ((a : ℝ) : UnitAddCircle))
    rw [neg_add, sub_eq_add_neg]

/-- …and it preserves the Haar pi-measure. -/
theorem measurePreserving_antidiagT (a : ℝ) :
    MeasurePreserving (antidiagT a)
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
  have hprod : MeasurePreserving
      (fun p : UnitAddCircle × UnitAddCircle =>
        (p.1 + ((a : ℝ) : UnitAddCircle), p.2 - ((a : ℝ) : UnitAddCircle)))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    have h1 : MeasurePreserving (fun x : UnitAddCircle => x + ((a : ℝ) : UnitAddCircle))
        (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
      measurePreserving_add_right _ _
    have h2 : MeasurePreserving (fun x : UnitAddCircle => x - ((a : ℝ) : UnitAddCircle))
        (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      simpa [sub_eq_add_neg] using
        measurePreserving_add_right (AddCircle.haarAddCircle : Measure UnitAddCircle)
          (-((a : ℝ) : UnitAddCircle))
    exact h1.prod h2
  have hfwd : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
      (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    rw [← HRTZakL2.torusVolume_eq_piHaar, ← HRTZakL2.volume_prod_eq_haar_prod]
    exact HRTZakL2.volumePreserving_torusProd
  have hbwd := hfwd.symm (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle))
  have hfun : antidiagT a
      = ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm
          ∘ (fun p : UnitAddCircle × UnitAddCircle =>
              (p.1 + ((a : ℝ) : UnitAddCircle), p.2 - ((a : ℝ) : UnitAddCircle))))
        ∘ (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)) := by
    funext x i
    fin_cases i <;> rfl
  rw [hfun]
  exact (hbwd.comp hprod).comp hfwd

/-! ### The `(√2,√2)` multiplier, and its two properties

`zakTor_modShift`'s multiplier is a character in the time representative times the wrap phase.  Both
factors are unimodular, so multiplication by it is an isometry of `L²(T²)` — which is what lets the
same lift-and-density-extend used for the pure translation run again here. -/

/-- The `(a,a)` intertwiner's multiplier, as a function on the torus. -/
noncomputable def psiTor (a : ℝ) (x : UnitAddTorus (Fin 2)) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((rep1 (x 0) : ℝ) : ℂ))
    * HRTShift.wrapPhi a (rep1 (x 0), rep1 (x 1) - a)

theorem norm_psiTor (a : ℝ) (x : UnitAddTorus (Fin 2)) : ‖psiTor a x‖ = 1 := by
  unfold psiTor
  rw [norm_mul, HRTShift.norm_wrapPhi, mul_one, Complex.norm_exp]
  simp

theorem measurable_psiTor (a : ℝ) : Measurable (psiTor a) := by
  unfold psiTor HRTShift.wrapPhi
  refine Measurable.mul ?_ ?_
  · refine Complex.measurable_exp.comp ?_
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_rep1.comp (measurable_pi_apply (0 : Fin 2)
        (X := fun _ : Fin 2 => UnitAddCircle))))
  · refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurable_rep1.comp
        (measurable_pi_apply (0 : Fin 2) (X := fun _ : Fin 2 => UnitAddCircle))) measurableSet_Iio
    · refine Complex.measurable_exp.comp ?_
      refine Measurable.neg ?_
      refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
      exact (measurable_rep1.comp
        (measurable_pi_apply (1 : Fin 2) (X := fun _ : Fin 2 => UnitAddCircle))).sub
          measurable_const

/-! ### Lifting the `(√2,√2)` intertwiner to `L²` — same two steps as the translation -/

/-- The `(a,a)` multiplier conjugated by the rotation. -/
noncomputable def psiRot (a : ℝ) (x : UnitAddTorus (Fin 2)) : ℂ := psiTor a (rotT x)

theorem norm_psiRot (a : ℝ) (x : UnitAddTorus (Fin 2)) : ‖psiRot a x‖ = 1 := norm_psiTor a _

theorem measurable_psiRot (a : ℝ) : Measurable (psiRot a) := by
  refine (measurable_psiTor a).comp ?_
  rw [← rotTEquiv_apply]
  exact rotTEquiv.measurable

/-- The modulation factor is unimodular. -/
theorem norm_modChar (a y : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The modulated translate stays `L²`. -/
theorem memLp_modShift {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) (a : ℝ) :
    MemLp (fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a))
      2 (volume : Measure ℝ) :=
  HRTShift.memLp_unimodular_mul (fun y => norm_modChar a y)
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).aestronglyMeasurable
    (memLp_shift_real hg a)

/-- …and keeps compact support: multiplying by a nowhere-zero character cannot enlarge it. -/
theorem hasCompactSupport_modShift {g : ℝ → ℂ} (hcs : HasCompactSupport g) (a : ℝ) :
    HasCompactSupport
      (fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a)) :=
  (hasCompactSupport_shift hcs a).mul_left

/-- **The `(√2,√2)` identity as a FUNCTION equality** — `zakTor_modShift` holds at every point. -/
theorem zakTor_modShift_eq (g : ℝ → ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    zakTor (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a))
      = fun x => psiTor a x * zakTor g (diagT a x) := by
  funext x
  rw [zakTor_modShift g a ha0 ha1 x]
  unfold psiTor
  ring

/-- **THE `(√2,√2)` IDENTITY FOR `zakL2`**, on the compactly supported class.  The shift that
appears is `antidiagT` — the ANTI-diagonal one — by `antidiagT_conj`. -/
theorem zakL2_modShift {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hgm2 : Measurable (fun y : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a))) :
    HRTZakL2.zakL2 (θ := 1) one_pos le_rfl (memLp_modShift hg a)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (measurable_psiRot a) (norm_psiRot a)
          (Lp.compMeasurePreserving (antidiagT a) (measurePreserving_antidiagT a)
            (HRTZakL2.zakL2 (θ := 1) one_pos le_rfl hg)) := by
  rw [zakL2_eq_zakTor_comp_rotT (hasCompactSupport_modShift hcs a) hgm2 (memLp_modShift hg a),
    zakL2_eq_zakTor_comp_rotT hcs hgm hg]
  refine Lp.ext_iff.mpr ?_
  have hL := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar (hasCompactSupport_modShift hcs a) hgm2 (memLp_modShift hg a)).toLp
      (zakTor (fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a))))
    measurePreserving_rotT_haar
  have hL2 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar (hasCompactSupport_modShift hcs a) hgm2
      (memLp_modShift hg a)).coeFn_toLp)
  have hR := coeFn_multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_psiRot a) (norm_psiRot a)
    (Lp.compMeasurePreserving (antidiagT a) (measurePreserving_antidiagT a)
      (Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
        ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g))))
  have hR2 := Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
      ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g))) (measurePreserving_antidiagT a)
  have hR3 := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)) measurePreserving_rotT_haar
  have hR4 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar hcs hgm hg).coeFn_toLp)
  filter_upwards [hL, hL2, hR, hR2,
    (measurePreserving_antidiagT a).quasiMeasurePreserving.ae_eq_comp (hR3.trans hR4)]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  show zakTor (fun y : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a)) (rotT x)
      = psiRot a x * zakTor g (rotT (antidiagT a x))
  have hconj : diagT a (rotT x) = rotT (antidiagT a x) := congrFun (antidiagT_conj a) x
  rw [zakTor_modShift g a ha0 ha1 (rotT x), hconj]
  unfold psiRot psiTor
  ring

/-! ### Density-extending the `(√2,√2)` identity -/

/-- Multiplication by the modulation character, on `L²(ℝ)`. -/
noncomputable def modCLM (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  HRTShift.multLC (μ := (volume : Measure ℝ))
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
    (fun y => norm_modChar a y)

/-- The full `(a,a)` time–frequency translate of the window, as a continuous linear map. -/
noncomputable def modTransCLM (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (modCLM a).comp (transL a).toContinuousLinearMap

/-- The anti-diagonal torus shift as a linear isometry of `L²(T²)`. -/
noncomputable def antidiagL (a : ℝ) :
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
      →ₗᵢ[ℂ]
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) :=
  Lp.compMeasurePreservingₗᵢ ℂ (antidiagT a) (measurePreserving_antidiagT a)

/-- The right-hand side of the `(√2,√2)` identity, as a map of the window. -/
noncomputable def modShiftRHS (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) :=
  HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_psiRot a) (norm_psiRot a) (antidiagL a (zakCLM f))

theorem continuous_modShiftLHS (a : ℝ) :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (modTransCLM a f)) :=
  zakCLM.continuous.comp (modTransCLM a).continuous

theorem continuous_modShiftRHS (a : ℝ) : Continuous (modShiftRHS a) :=
  (HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_psiRot a) (norm_psiRot a)).continuous.comp
      ((antidiagL a).continuous.comp zakCLM.continuous)

/-- The two sides of the `(√2,√2)` identity agree on the compactly supported class. -/
theorem modEqOn_CS (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Set.EqOn (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (modTransCLM a f))
      (modShiftRHS a) CS := by
  rintro f ⟨g, hcs, hgm, hae⟩
  have hg : MemLp g 2 (volume : Measure ℝ) := (Lp.memLp f).ae_eq hae
  have hgm2 : Measurable (fun y : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a)) :=
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).mul
      (hgm.comp (measurable_id.sub_const a))
  have haeT : (↑↑(transL a f) : ℝ → ℂ) =ᵐ[volume] fun y => g (y - a) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) a)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp hae
  have haeM : (↑↑(modTransCLM a f) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a) := by
    refine (coeFn_multLC (μ := (volume : Measure ℝ))
      (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
      (fun y => norm_modChar a y) (transL a f)).trans ?_
    filter_upwards [haeT] with y hy
    rw [hy]
    rfl
  show zakOf (modTransCLM a f) = _
  rw [zakOf_congr (memLp_modShift hg a) haeM, zakL2_modShift hcs hgm hg a ha0 ha1 hgm2]
  show _ = HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (measurable_psiRot a) (norm_psiRot a) (antidiagL a (zakOf f))
  rw [zakOf_congr hg hae]
  rfl

/-- **THE `(√2,√2)` IDENTITY FOR EVERY `L²` WINDOW.**  Density extension of `zakL2_modShift`,
exactly as `zakL2_shift_of_memLp` was for the pure translation.  With this, all four `Λ₀` points
have `hcs`-free intertwiners in the `L²` picture. -/
theorem zakL2_modShift_of_memLp (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (modTransCLM a f)) = modShiftRHS a :=
  Continuous.ext_on dense_CS (continuous_modShiftLHS a) (continuous_modShiftRHS a)
    (modEqOn_CS a ha0 ha1)

/-! ### The LATTICE points act by MULTIPLICATION, not by a shift

This is the structural fact that makes the cocycle assemble.  For the three lattice points of `Λ₀`
the intertwiner is not a torus shift at all:

* `T₁` (translate by 1) acts as multiplication by `e^{-2πiω}` — quasi-periodicity in `t`;
* `M₁` (modulate by `e^{2πiy}`) acts as multiplication by `e^{2πit}` (`zak_modulate_one`);
* `(0,0)` is the identity.

So three of the four terms collect into a single MULTIPLIER — the symbol
`A + B·e^{-2πiω} + C·e^{2πit}` — and only the `(√2,√2)` term moves the point.  That is precisely
the shape `‖symbol‖·‖Zg‖ = ‖D‖·‖Zg∘shift‖` needs, and it needs no density argument, because
multiplication identities are pointwise. -/

/-- **`T₁` acts on `zakTor` by multiplication by `e^{-2πiω}`.** -/
theorem zakTor_transOne (g : ℝ → ℂ) (x : UnitAddTorus (Fin 2)) :
    zakTor (fun y => g (y - 1)) x
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((rep1 (x 1) : ℝ) : ℂ))) * zakTor g x := by
  unfold zakTor
  rw [HRTShift.zak_shift_window g 1 (rep1 (x 0)) (rep1 (x 1))]
  have hq := ZakPeriodization.zak_quasi_periodic_fst g (rep1 (x 0) - 1) (rep1 (x 1))
  rw [sub_add_cancel] at hq
  rw [hq, ← mul_assoc, ← Complex.exp_add]
  simp

/-- **`M₁` acts on `zakTor` by multiplication by `e^{2πit}`.** -/
theorem zakTor_modOne (g : ℝ → ℂ) (x : UnitAddTorus (Fin 2)) :
    zakTor (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) x
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((rep1 (x 0) : ℝ) : ℂ)) * zakTor g x := by
  unfold zakTor
  exact ZakPeriodization.zak_modulate_one g (rep1 (x 0)) (rep1 (x 1))

/-! ### Lifting the two lattice multipliers to `L²`

`zak_add` needs SUMMABILITY of the translate families, which is precisely why the pointwise cocycle
route carries `hcs`.  `zakL2` is linear with no such hypothesis (`zakL2_add`, `zakL2_smul`), so the
assembly must run there — and that means the lattice intertwiners are needed at the `zakL2` level
too, not just on `zakTor`.  Same bridge-plus-density pattern as before, but lighter: there is no
shift, so the right-hand side is a plain multiplication operator. -/

/-- The `T₁` multiplier, conjugated by the rotation. -/
noncomputable def chiT1 (x : UnitAddTorus (Fin 2)) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((rep1 ((rotT x) 1) : ℝ) : ℂ)))

/-- The `M₁` multiplier, conjugated by the rotation. -/
noncomputable def chiM1 (x : UnitAddTorus (Fin 2)) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((rep1 ((rotT x) 0) : ℝ) : ℂ))

theorem norm_chiT1 (x : UnitAddTorus (Fin 2)) : ‖chiT1 x‖ = 1 := by
  unfold chiT1; rw [Complex.norm_exp]; simp

theorem norm_chiM1 (x : UnitAddTorus (Fin 2)) : ‖chiM1 x‖ = 1 := by
  unfold chiM1; rw [Complex.norm_exp]; simp

theorem measurable_chiT1 : Measurable chiT1 := by
  unfold chiT1
  refine Complex.measurable_exp.comp (Measurable.neg ?_)
  refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
  refine measurable_rep1.comp ?_
  refine (measurable_pi_apply (1 : Fin 2) (X := fun _ : Fin 2 => UnitAddCircle)).comp ?_
  exact measurableEmbedding_rotT.measurable

theorem measurable_chiM1 : Measurable chiM1 := by
  unfold chiM1
  refine Complex.measurable_exp.comp ?_
  refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
  refine measurable_rep1.comp ?_
  refine (measurable_pi_apply (0 : Fin 2) (X := fun _ : Fin 2 => UnitAddCircle)).comp ?_
  exact measurableEmbedding_rotT.measurable

/-- The translated-by-one window keeps compact support and stays `L²`. -/
theorem hasCompactSupport_trans1 {g : ℝ → ℂ} (hcs : HasCompactSupport g) :
    HasCompactSupport (fun y : ℝ => g (y - 1)) := hasCompactSupport_shift hcs 1

theorem memLp_trans1 {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (fun y : ℝ => g (y - 1)) 2 (volume : Measure ℝ) := memLp_shift_real hg 1

/-- The modulated window keeps compact support and stays `L²`. -/
theorem hasCompactSupport_mod1 {g : ℝ → ℂ} (hcs : HasCompactSupport g) :
    HasCompactSupport
      (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) :=
  hcs.mul_left

theorem memLp_mod1 {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      2 (volume : Measure ℝ) :=
  HRTShift.memLp_unimodular_mul
    (fun y => by simp [Complex.norm_exp])
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).aestronglyMeasurable
    hg

/-! ### The two lattice intertwiners at the `zakL2` level, and their density extensions -/

/-- `T₁` on `zakL2`, on the compactly supported class. -/
theorem zakL2_transOne {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgm1 : Measurable (fun y : ℝ => g (y - 1))) :
    HRTZakL2.zakL2 (θ := 1) one_pos le_rfl (memLp_trans1 hg)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1
          (HRTZakL2.zakL2 (θ := 1) one_pos le_rfl hg) := by
  rw [zakL2_eq_zakTor_comp_rotT (hasCompactSupport_trans1 hcs) hgm1 (memLp_trans1 hg),
    zakL2_eq_zakTor_comp_rotT hcs hgm hg]
  refine Lp.ext_iff.mpr ?_
  have hL := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar (hasCompactSupport_trans1 hcs) hgm1 (memLp_trans1 hg)).toLp
      (zakTor (fun y : ℝ => g (y - 1)))) measurePreserving_rotT_haar
  have hL2 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar (hasCompactSupport_trans1 hcs) hgm1 (memLp_trans1 hg)).coeFn_toLp)
  have hR := coeFn_multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    measurable_chiT1 norm_chiT1
    (Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
      ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)))
  have hR2 := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)) measurePreserving_rotT_haar
  have hR3 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar hcs hgm hg).coeFn_toLp)
  filter_upwards [hL, hL2, hR, hR2.trans hR3] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  show zakTor (fun y : ℝ => g (y - 1)) (rotT x) = chiT1 x * zakTor g (rotT x)
  rw [zakTor_transOne g (rotT x)]
  rfl

/-- `M₁` on `zakL2`, on the compactly supported class. -/
theorem zakL2_modOne {g : ℝ → ℂ} (hcs : HasCompactSupport g) (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hgm1 : Measurable
      (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)) :
    HRTZakL2.zakL2 (θ := 1) one_pos le_rfl (memLp_mod1 hg)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1
          (HRTZakL2.zakL2 (θ := 1) one_pos le_rfl hg) := by
  rw [zakL2_eq_zakTor_comp_rotT (hasCompactSupport_mod1 hcs) hgm1 (memLp_mod1 hg),
    zakL2_eq_zakTor_comp_rotT hcs hgm hg]
  refine Lp.ext_iff.mpr ?_
  have hL := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar (hasCompactSupport_mod1 hcs) hgm1 (memLp_mod1 hg)).toLp
      (zakTor (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)))
    measurePreserving_rotT_haar
  have hL2 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar (hasCompactSupport_mod1 hcs) hgm1 (memLp_mod1 hg)).coeFn_toLp)
  have hR := coeFn_multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    measurable_chiM1 norm_chiM1
    (Lp.compMeasurePreserving rotT measurePreserving_rotT_haar
      ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)))
  have hR2 := Lp.coeFn_compMeasurePreserving
    ((memLp_zakTor_haar hcs hgm hg).toLp (zakTor g)) measurePreserving_rotT_haar
  have hR3 := measurePreserving_rotT_haar.quasiMeasurePreserving.ae_eq_comp
    ((memLp_zakTor_haar hcs hgm hg).coeFn_toLp)
  filter_upwards [hL, hL2, hR, hR2.trans hR3] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  show zakTor (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) (rotT x)
      = chiM1 x * zakTor g (rotT x)
  rw [zakTor_modOne g (rotT x)]
  rfl

/-! ### Density-extending the two lattice intertwiners

Same three ingredients as before: both sides continuous in the window, agreement on `CS`,
`dense_CS`.  With these the last two of the four `Λ₀` terms become `hcs`-free. -/

/-- Multiplication by `e^{2πiy}` on `L²(ℝ)` — the `M₁` operator. -/
noncomputable def mod1CLM : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  HRTShift.multLC (μ := (volume : Measure ℝ))
    (φ := fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)))
    (by exact Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
    (fun y => by rw [Complex.norm_exp]; simp)

theorem continuous_T1LHS :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (transL 1 f)) :=
  zakCLM.continuous.comp (transL 1).continuous

theorem continuous_T1RHS :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) =>
      HRTShift.multLC
        (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
        measurable_chiT1 norm_chiT1 (zakCLM f)) :=
  (HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    measurable_chiT1 norm_chiT1).continuous.comp zakCLM.continuous

theorem continuous_M1LHS :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (mod1CLM f)) :=
  zakCLM.continuous.comp mod1CLM.continuous

theorem continuous_M1RHS :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) =>
      HRTShift.multLC
        (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
        measurable_chiM1 norm_chiM1 (zakCLM f)) :=
  (HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    measurable_chiM1 norm_chiM1).continuous.comp zakCLM.continuous

theorem T1_eqOn_CS :
    Set.EqOn (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (transL 1 f))
      (fun f => HRTShift.multLC
        (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
        measurable_chiT1 norm_chiT1 (zakCLM f)) CS := by
  rintro f ⟨g, hcs, hgm, hae⟩
  have hg : MemLp g 2 (volume : Measure ℝ) := (Lp.memLp f).ae_eq hae
  have hgm1 : Measurable (fun y : ℝ => g (y - 1)) := hgm.comp (measurable_id.sub_const 1)
  have haeT : (↑↑(transL 1 f) : ℝ → ℂ) =ᵐ[volume] fun y : ℝ => g (y - 1) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) 1)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) 1).quasiMeasurePreserving.ae_eq_comp hae
  show zakOf (transL 1 f) = _
  rw [zakOf_congr (memLp_trans1 hg) haeT, zakL2_transOne hcs hgm hg hgm1]
  show _ = HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    measurable_chiT1 norm_chiT1 (zakOf f)
  rw [zakOf_congr hg hae]

theorem M1_eqOn_CS :
    Set.EqOn (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (mod1CLM f))
      (fun f => HRTShift.multLC
        (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
        measurable_chiM1 norm_chiM1 (zakCLM f)) CS := by
  rintro f ⟨g, hcs, hgm, hae⟩
  have hg : MemLp g 2 (volume : Measure ℝ) := (Lp.memLp f).ae_eq hae
  have hgm1 : Measurable
      (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) :=
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).mul hgm
  have haeM : (↑↑(mod1CLM f) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y := by
    refine (coeFn_multLC (μ := (volume : Measure ℝ))
      (φ := fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)))
      (by exact Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
      (fun y => by rw [Complex.norm_exp]; simp) f).trans ?_
    filter_upwards [hae] with y hy
    rw [hy]
  show zakOf (mod1CLM f) = _
  rw [zakOf_congr (memLp_mod1 hg) haeM, zakL2_modOne hcs hgm hg hgm1]
  show _ = HRTShift.multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    measurable_chiM1 norm_chiM1 (zakOf f)
  rw [zakOf_congr hg hae]

/-- **`T₁` for EVERY `L²` window.** -/
theorem zakL2_transOne_of_memLp :
    (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (transL 1 f))
      = fun f => HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1 (zakCLM f) :=
  Continuous.ext_on dense_CS continuous_T1LHS continuous_T1RHS T1_eqOn_CS

/-- **`M₁` for EVERY `L²` window.** -/
theorem zakL2_modOne_of_memLp :
    (fun f : Lp ℂ 2 (volume : Measure ℝ) => zakCLM (mod1CLM f))
      = fun f => HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM f) :=
  Continuous.ext_on dense_CS continuous_M1LHS continuous_M1RHS M1_eqOn_CS

/-! ### The dependence, as an identity between `Lp` elements

The four-term time–frequency dependence is a pointwise identity on `ℝ`.  This states it as an
equation in `L²(ℝ)` between the four operator images of a single `f`, which is the form `zakCLM`'s
linearity can act on. -/

theorem dep_Lp {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    A • f + B • (transL 1 f) + C • (mod1CLM f) + D • (modTransCLM a f) = 0 := by
  refine Lp.ext_iff.mpr ?_
  have h1 : (↑↑(transL 1 f) : ℝ → ℂ) =ᵐ[volume] fun y : ℝ => g (y - 1) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) 1)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) 1).quasiMeasurePreserving.ae_eq_comp hae
  have h2 : (↑↑(mod1CLM f) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y := by
    refine (coeFn_multLC (μ := (volume : Measure ℝ))
      (φ := fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)))
      (by exact Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
      (fun y => by rw [Complex.norm_exp]; simp) f).trans ?_
    filter_upwards [hae] with y hy
    rw [hy]
  have h3T : (↑↑(transL a f) : ℝ → ℂ) =ᵐ[volume] fun y : ℝ => g (y - a) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) a)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp hae
  have h3 : (↑↑(modTransCLM a f) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a) := by
    refine (coeFn_multLC (μ := (volume : Measure ℝ))
      (φ := fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)))
      (by exact Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
      (fun y => norm_modChar a y) (transL a f)).trans ?_
    filter_upwards [h3T] with y hy
    rw [hy]
  filter_upwards [Lp.coeFn_add (A • f + B • (transL 1 f) + C • (mod1CLM f)) (D • (modTransCLM a f)),
    Lp.coeFn_add (A • f + B • (transL 1 f)) (C • (mod1CLM f)),
    Lp.coeFn_add (A • f) (B • (transL 1 f)),
    Lp.coeFn_smul A f, Lp.coeFn_smul B (transL 1 f), Lp.coeFn_smul C (mod1CLM f),
    Lp.coeFn_smul D (modTransCLM a f),
    hae, h1, h2, h3, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))]
    with y e1 e2 e3 s1 s2 s3 s4 ha hb hc hd hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 e3 s1 s2 s3 s4 hz
  rw [e1, e2, e3, s1, s2, s3, s4, ha, hb, hc, hd, hz]
  linear_combination hdep y

/-! ### THE DEPENDENCE, TRANSPORTED — the cocycle relation without compact support

Apply `zakCLM` to `dep_Lp` and substitute the four intertwiners.  Three of them are pure
multipliers, so they collect; only the `(√2,√2)` term moves the point.  Nothing here carries
`HasCompactSupport`. -/

theorem zakCLM_dep {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    A • zakCLM f
      + B • (HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1 (zakCLM f))
      + C • (HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM f))
      + D • (HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (measurable_psiRot a) (norm_psiRot a) (antidiagL a (zakCLM f))) = 0 := by
  have h0 := dep_Lp A B C D a f hae hdep
  have h1 : zakCLM (A • f + B • (transL 1 f) + C • (mod1CLM f) + D • (modTransCLM a f)) = 0 := by
    rw [h0, map_zero]
  simp only [map_add, map_smul] at h1
  -- explicit types force the beta-reduction of the `fun f => …` statements
  have e1 : zakCLM (transL 1 f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1 (zakCLM f) :=
    congrFun zakL2_transOne_of_memLp f
  have e2 : zakCLM (mod1CLM f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM f) :=
    congrFun zakL2_modOne_of_memLp f
  have e3 : zakCLM (modTransCLM a f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (measurable_psiRot a) (norm_psiRot a) (antidiagL a (zakCLM f)) :=
    congrFun (zakL2_modShift_of_memLp a ha0 ha1) f
  rw [e1, e2, e3] at h1
  exact h1

/-! ### The symbol, and the cocycle

The three multiplier terms of `zakCLM_dep` collect into a single symbol; the fourth moves the
point.  Rearranging and taking moduli — the `(√2,√2)` multiplier is unimodular — gives the cocycle,
with no compact support. -/

/-- The symbol, on the torus: the three lattice terms collected. -/
noncomputable def symbolTor (A B C : ℂ) (x : UnitAddTorus (Fin 2)) : ℂ :=
  A + B * chiT1 x + C * chiM1 x

/-- `antidiagL` acts on representatives by pre-composition. -/
theorem coeFn_antidiagL (a : ℝ)
    (F : Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))) :
    (↑↑(antidiagL a F) : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))]
        (↑↑F : UnitAddTorus (Fin 2) → ℂ) ∘ (antidiagT a) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_antidiagT a)

/-- **THE COCYCLE EQUATION**, a.e. on the torus, for every `L²` window. -/
theorem cocycle_eq {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
      symbolTor A B C x * (↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) x
        = -(D * (psiRot a x
            * (↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (antidiagT a x))) := by
  set μT := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) with hμT
  set Z := zakCLM f with hZ
  set T1 := HRTShift.multLC (μ := μT) measurable_chiT1 norm_chiT1 Z with hT1
  set M1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 Z with hM1
  set S := HRTShift.multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a) (antidiagL a Z) with hS
  have h0 : A • Z + B • T1 + C • M1 + D • S = 0 := zakCLM_dep A B C D a ha0 ha1 f hae hdep
  have hcoe : (↑↑(A • Z + B • T1 + C • M1 + D • S) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[μT] 0 := by
    rw [h0]; exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μT)
  filter_upwards [hcoe,
    Lp.coeFn_add (A • Z + B • T1 + C • M1) (D • S),
    Lp.coeFn_add (A • Z + B • T1) (C • M1),
    Lp.coeFn_add (A • Z) (B • T1),
    Lp.coeFn_smul A Z, Lp.coeFn_smul B T1, Lp.coeFn_smul C M1, Lp.coeFn_smul D S,
    coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z,
    coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 Z,
    coeFn_multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a) (antidiagL a Z),
    coeFn_antidiagL a Z]
    with x hz e1 e2 e3 s1 s2 s3 s4 m1 m2 m3 mA
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Function.comp_apply] at hz e1 e2 e3 s1 s2 s3 s4 m1 m2 m3 mA
  rw [e1, e2, e3, s1, s2, s3, s4, m1, m2, m3, mA] at hz
  unfold symbolTor
  linear_combination hz

/-- **THE COCYCLE** — a.e. on the torus, for EVERY `L²` window, with no compact support:

    ‖symbol(x)‖ · ‖Z(x)‖ = ‖D‖ · ‖Z(antidiag x)‖

`HRTCocycle.cocycle_of_dependence_compactSupport` obtains the same relation for the POINTWISE fibre
and needs `HasCompactSupport` to do it, because that route goes through the pointwise Zak series —
which `summable_not_implied_by_memLp` proves cannot serve a general `L²` window.  This one goes
through `zakCLM`, whose linearity is unconditional, so no such hypothesis appears. -/
theorem cocycle_norm {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
      ‖symbolTor A B C x‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) x‖
        = ‖D‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (antidiagT a x)‖ := by
  filter_upwards [cocycle_eq A B C D a ha0 ha1 f hae hdep] with x hx
  have h := congrArg norm hx
  rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_psiRot, one_mul] at h
  exact h

/-! ### Towards the fibre: the shear makes `antidiag` a ONE-COORDINATE shift

`antidiagT` sends `(x₀,x₁) ↦ (x₀+a, x₁-a)`, so **`x₀ + x₁` is invariant** — that is the fibration.
`HRTZakL2.measurePreserving_shear`'s map `(t,ω) ↦ (t, ω+t)` turns it into a shift of the FIRST
coordinate alone, leaving the second fixed, which is exactly the form Fubini + the abstract Birkhoff
lemma consume.

In `(t,ω)` terms this is the DIAGONAL shift `(t-a, ω-a)`: recall `zakL2`'s coordinates are
`(dual to ω, dual to t)`, so `θ = ω - t` is what the second sheared coordinate tracks. -/

/-- `antidiagT`, read on the binary product. -/
noncomputable def antidiagP (a : ℝ) (p : UnitAddCircle × UnitAddCircle) :
    UnitAddCircle × UnitAddCircle :=
  (p.1 + ((a : ℝ) : UnitAddCircle), p.2 - ((a : ℝ) : UnitAddCircle))

/-- `piFinTwo` intertwines `antidiagT` with `antidiagP`. -/
theorem piFinTwo_antidiag (a : ℝ) (x : UnitAddTorus (Fin 2)) :
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)) (antidiagT a x)
      = antidiagP a ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)) x) := rfl

/-- **The shear conjugates `antidiagP` to a shift of the FIRST coordinate.**  The second sheared
coordinate — the fibre parameter — is left fixed, which is what makes the slicing possible. -/
theorem shear_conj_antidiagP (a : ℝ) :
    (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 + p.1)) ∘ (antidiagP a)
      = (fun q : UnitAddCircle × UnitAddCircle => (q.1 + ((a : ℝ) : UnitAddCircle), q.2))
        ∘ (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 + p.1)) := by
  funext p
  simp only [Function.comp_apply, antidiagP, Prod.mk.injEq, true_and]
  abel

/-- `antidiagP` preserves Haar on the product. -/
theorem measurePreserving_antidiagP (a : ℝ) :
    MeasurePreserving (antidiagP a)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
  have h1 : MeasurePreserving (fun x : UnitAddCircle => x + ((a : ℝ) : UnitAddCircle))
      (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    measurePreserving_add_right _ _
  have h2 : MeasurePreserving (fun x : UnitAddCircle => x - ((a : ℝ) : UnitAddCircle))
      (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    simpa [sub_eq_add_neg] using
      measurePreserving_add_right (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (-((a : ℝ) : UnitAddCircle))
  exact h1.prod h2

/-! ### Transporting the cocycle to sheared product coordinates

`HRTZakL2.measurePreserving_prodToTorusHaar` is already exactly the map needed: it is
`piFinTwo.symm ∘ (p ↦ (p.1, p.2 - p.1))`, and it conjugates `antidiagT` to a shift of the FIRST
product coordinate with the SECOND — the fibre parameter `θ` — left fixed.  Transporting
`cocycle_norm` along it therefore puts the cocycle in exactly the shape Fubini slices. -/

/-- Sheared product → torus; the map `measurePreserving_prodToTorusHaar` is stated for. -/
noncomputable abbrev toTor : UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2) :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm ∘
    (fun p : UnitAddCircle × UnitAddCircle => (p.1, p.2 - p.1))

/-- **`toTor` conjugates the first-coordinate shift to `antidiagT`.**  The second coordinate — the
fibre parameter — is untouched. -/
theorem toTor_conj_antidiag (a : ℝ) :
    (antidiagT a) ∘ toTor
      = toTor ∘ (fun q : UnitAddCircle × UnitAddCircle =>
          (q.1 + ((a : ℝ) : UnitAddCircle), q.2)) := by
  funext q i
  fin_cases i
  · rfl
  · show q.2 - q.1 - ((a : ℝ) : UnitAddCircle) = q.2 - (q.1 + ((a : ℝ) : UnitAddCircle))
    abel

/-- **THE COCYCLE IN SHEARED PRODUCT COORDINATES.**  The shift is now in the FIRST coordinate only;
the second is the fibre parameter.  This is the form `Fubini` slices into 1-D cocycles. -/
theorem cocycle_prod {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ q ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle),
      ‖symbolTor A B C (toTor q)‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (toTor q)‖
        = ‖D‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ)
            (toTor (q.1 + ((a : ℝ) : UnitAddCircle), q.2))‖ := by
  have hT := (HRTZakL2.measurePreserving_prodToTorusHaar).quasiMeasurePreserving.ae
    (cocycle_norm A B C D a ha0 ha1 f hae hdep)
  filter_upwards [hT] with q hq
  have hconj : antidiagT a (toTor q)
      = toTor (q.1 + ((a : ℝ) : UnitAddCircle), q.2) := congrFun (toTor_conj_antidiag a) q
  rw [← hconj]
  exact hq

/-- **THE COCYCLE ON THE FIBRES.**  For a.e. fibre parameter `u`, the relation holds a.e. in `v`
with the shift acting as a ROTATION BY `a` on the circle — a 1-D cocycle, which is what
`BirkhoffErgodic.integral_log_eq_of_modulus_cocycle` (abstract in `G` and `P`) consumes.

The `Prod.swap` detour is needed because `ae_ae_of_ae_prod` yields `∀ᵐ x, ∀ᵐ y` while the fibre
index is the SECOND coordinate; the same trick appears in `HRTShift.ae_ae_slice_eq_zero`. -/
theorem cocycle_fibre {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        ‖symbolTor A B C (toTor (v, u))‖
            * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (toTor (v, u))‖
          = ‖D‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ)
              (toTor (v + ((a : ℝ) : UnitAddCircle), u))‖ := by
  have h0 := cocycle_prod A B C D a ha0 ha1 f hae hdep
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.swap : UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    refine ⟨measurable_swap, ?_⟩
    rw [Measure.prod_swap]
  exact Measure.ae_ae_of_ae_prod (hqmp.ae h0)

/-! ### A MEASURABLE representative for the fibre

`BirkhoffErgodic.integral_log_eq_of_modulus_cocycle` needs `Measurable G`, but `Lp` supplies only
`AEStronglyMeasurable`.  Same fix as `rep` on the window side: take the `.mk` representative and
carry an a.e. equality.  The cocycle is an a.e. statement, so nothing is lost. -/

/-- A measurable representative of the transform. -/
noncomputable def zakRep (f : Lp ℂ 2 (volume : Measure ℝ)) : UnitAddTorus (Fin 2) → ℂ :=
  (Lp.aestronglyMeasurable (zakCLM f)).mk _

theorem measurable_zakRep (f : Lp ℂ 2 (volume : Measure ℝ)) : Measurable (zakRep f) :=
  ((Lp.aestronglyMeasurable (zakCLM f)).stronglyMeasurable_mk).measurable

theorem zakRep_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))]
        zakRep f :=
  (Lp.aestronglyMeasurable (zakCLM f)).ae_eq_mk

/-- The fibre function the Birkhoff lemma consumes: `G_u(v) = ‖Z(toTor (v,u))‖`, MEASURABLE. -/
noncomputable def fibreG (f : Lp ℂ 2 (volume : Measure ℝ)) (u : UnitAddCircle) :
    UnitAddCircle → ℝ :=
  fun v => ‖zakRep f (toTor (v, u))‖

/-- The fibre symbol: `P_u(v) = ‖symbol(toTor (v,u))‖`, MEASURABLE. -/
noncomputable def fibreP (A B C : ℂ) (u : UnitAddCircle) : UnitAddCircle → ℝ :=
  fun v => ‖symbolTor A B C (toTor (v, u))‖

theorem measurable_toTor : Measurable toTor := by
  refine (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)).symm.measurable.comp ?_
  exact measurable_fst.prodMk (measurable_snd.sub measurable_fst)

theorem measurable_fibreG (f : Lp ℂ 2 (volume : Measure ℝ)) (u : UnitAddCircle) :
    Measurable (fibreG f u) := by
  unfold fibreG
  refine ((measurable_zakRep f).comp ?_).norm
  exact measurable_toTor.comp (measurable_id.prodMk measurable_const)

theorem measurable_symbolTor (A B C : ℂ) : Measurable (symbolTor A B C) := by
  unfold symbolTor
  exact (measurable_const.add (measurable_const.mul measurable_chiT1)).add
    (measurable_const.mul measurable_chiM1)

theorem measurable_fibreP (A B C : ℂ) (u : UnitAddCircle) : Measurable (fibreP A B C u) := by
  unfold fibreP
  refine ((measurable_symbolTor A B C).comp ?_).norm
  exact measurable_toTor.comp (measurable_id.prodMk measurable_const)

/-! ### The cocycle carried onto the measurable representative

Three copies of the chain already proved, with `zakRep f` in place of the `Lp` coercion.  The
final one is stated in `fibreP`/`fibreG` form with `|·|` rather than `‖·‖` — i.e. LITERALLY the
shape of `BirkhoffErgodic.integral_log_eq_of_modulus_cocycle`'s `hcoc`. -/

theorem cocycle_norm_rep {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
      ‖symbolTor A B C x‖ * ‖zakRep f x‖ = ‖D‖ * ‖zakRep f (antidiagT a x)‖ := by
  have hshift := (measurePreserving_antidiagT a).quasiMeasurePreserving.ae_eq_comp (zakRep_ae f)
  filter_upwards [cocycle_norm A B C D a ha0 ha1 f hae hdep, zakRep_ae f, hshift] with x hx h1 h2
  simp only [Function.comp_apply] at h2
  rw [← h1, ← h2]
  exact hx

theorem cocycle_prod_rep {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ q ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle),
      ‖symbolTor A B C (toTor q)‖ * ‖zakRep f (toTor q)‖
        = ‖D‖ * ‖zakRep f (toTor (q.1 + ((a : ℝ) : UnitAddCircle), q.2))‖ := by
  have hT := (HRTZakL2.measurePreserving_prodToTorusHaar).quasiMeasurePreserving.ae
    (cocycle_norm_rep A B C D a ha0 ha1 f hae hdep)
  filter_upwards [hT] with q hq
  have hconj : antidiagT a (toTor q)
      = toTor (q.1 + ((a : ℝ) : UnitAddCircle), q.2) := congrFun (toTor_conj_antidiag a) q
  rw [← hconj]
  exact hq

/-- **THE BIRKHOFF-READY COCYCLE.**  For a.e. fibre `u`, `|P| · |G| = d · |G ∘ R|` with
`R = (· + a)` a rotation of the circle, `G = fibreG f u` and `P = fibreP A B C u` both
MEASURABLE.  This is exactly `integral_log_eq_of_modulus_cocycle`'s `hcoc`. -/
theorem cocycle_fibre_rep {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        |fibreP A B C u v| * |fibreG f u v|
          = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))| := by
  have h0 := cocycle_prod_rep A B C D a ha0 ha1 f hae hdep
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.swap : UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    refine ⟨measurable_swap, ?_⟩
    rw [Measure.prod_swap]
  have h1 := Measure.ae_ae_of_ae_prod (hqmp.ae h0)
  filter_upwards [h1] with u hu
  filter_upwards [hu] with v hv
  unfold fibreP fibreG
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]
  exact hv

/-! ### The multipliers ARE the standard characters

`chiT1`/`chiM1` were defined through `rep1` and `rotT`, which makes their analytic behaviour
opaque — `rep1` is not even continuous.  In fact each collapses to a single `fourier` character of
ONE coordinate (the `rep1` jump is by an integer, which the character does not see), so
`symbolTor` is an honest two-variable trigonometric polynomial.  Continuity, the finite zero set
and log-integrability then all become routine, and the `symbolCircle` machinery of `HRTReduction`
becomes reachable.

Recorded as LEMMAS rather than prose: each of these could be off by a sign or a conjugate
invisibly — every candidate is an honest unimodular character, so neither the build nor
`#print axioms` would flag a wrong one. -/

theorem fourier_negOne_neg (y : UnitAddCircle) :
    fourier (-1 : ℤ) (-y) = fourier (1 : ℤ) y := by
  have h : ((-1 : ℤ)) • (-y) = (1 : ℤ) • y := by simp
  rw [fourier_apply, fourier_apply, h]

theorem chiT1_eq (x : UnitAddTorus (Fin 2)) : chiT1 x = fourier (1 : ℤ) (x 0) := by
  have hrot : (rotT x) 1 = -(x 0) := by simp [rotT]
  have h1 : chiT1 x = HRTTransfer.ee (((-1 : ℤ) : ℝ) * rep1 (-(x 0))) := by
    unfold chiT1 HRTTransfer.ee
    simp only [hrot]
    congr 1
    push_cast
    ring
  rw [h1, ← fourier_eq_ee_rep (-1 : ℤ) (-(x 0)), fourier_negOne_neg]

theorem chiM1_eq (x : UnitAddTorus (Fin 2)) : chiM1 x = fourier (1 : ℤ) (x 1) := by
  have hrot : (rotT x) 0 = x 1 := by simp [rotT]
  have h1 : chiM1 x = HRTTransfer.ee (((1 : ℤ) : ℝ) * rep1 (x 1)) := by
    unfold chiM1 HRTTransfer.ee
    simp only [hrot]
    congr 1
    push_cast
    ring
  rw [h1, ← fourier_eq_ee_rep (1 : ℤ) (x 1)]

/-- **`symbolTor` is a trigonometric polynomial.** -/
theorem symbolTor_eq (A B C : ℂ) (x : UnitAddTorus (Fin 2)) :
    symbolTor A B C x = A + B * fourier (1 : ℤ) (x 0) + C * fourier (1 : ℤ) (x 1) := by
  unfold symbolTor
  rw [chiT1_eq, chiM1_eq]

theorem toTor_apply_zero (p : UnitAddCircle × UnitAddCircle) : (toTor p) 0 = p.1 := rfl

theorem toTor_apply_one (p : UnitAddCircle × UnitAddCircle) : (toTor p) 1 = p.2 - p.1 := rfl

/-- **The fibre symbol, explicitly.**  A trigonometric polynomial in `v`, with the fibre parameter
`u` entering only through the unimodular twist `fourier 1 u` on the `C` coefficient. -/
theorem fibreP_eq (A B C : ℂ) (u v : UnitAddCircle) :
    fibreP A B C u v = ‖A + B * fourier (1 : ℤ) v + C * fourier (1 : ℤ) (u - v)‖ := by
  unfold fibreP
  rw [symbolTor_eq]
  simp only [toTor_apply_zero, toTor_apply_one]

theorem continuous_fibreP (A B C : ℂ) (u : UnitAddCircle) :
    Continuous (fibreP A B C u) := by
  have h : fibreP A B C u
      = fun v => ‖A + B * fourier (1 : ℤ) v + C * fourier (1 : ℤ) (u - v)‖ :=
    funext (fibreP_eq A B C u)
  rw [h]
  exact ((continuous_const.add
    (continuous_const.mul (fourier (1 : ℤ)).continuous)).add
    (continuous_const.mul
      ((fourier (1 : ℤ)).continuous.comp (continuous_const.sub continuous_id)))).norm

/-! ### The fibre symbol as a QUADRATIC on the circle

Multiplying by the unimodular `fourier 1 v` turns the fibre symbol into the modulus of a quadratic
in `z = fourier 1 v`:

    fibreP A B C u v = ‖B z² + A z + C w‖,    z = fourier 1 v,   w = fourier 1 u.

So the symbol vanishes exactly where the character meets a root of that quadratic, and the
hypothesis the Birkhoff step needs (`hPne` and `hint`) is simply that the quadratic has no root ON
the unit circle — the same condition `HRTReduction.symbolCircle_pos` imposes through `‖ζᵢ‖ ≠ 1`,
here stated directly so no factorisation has to be carried. -/

theorem fourier_one_sub (u v : UnitAddCircle) :
    (fourier (1 : ℤ) (u - v) : ℂ) * (fourier (1 : ℤ) v : ℂ) = (fourier (1 : ℤ) u : ℂ) := by
  have h : u - v + v = u := by abel
  simp_rw [fourier_one]
  rw [← Circle.coe_mul, ← AddCircle.toCircle_add, h]

theorem norm_fourier_one (v : UnitAddCircle) : ‖(fourier (1 : ℤ) v : ℂ)‖ = 1 := by
  rw [fourier_one]
  exact Circle.norm_coe _

/-- **The fibre symbol is the modulus of a quadratic in the character.** -/
theorem fibreP_quad (A B C : ℂ) (u v : UnitAddCircle) :
    fibreP A B C u v
      = ‖B * (fourier (1 : ℤ) v : ℂ) ^ 2 + A * (fourier (1 : ℤ) v : ℂ)
          + C * (fourier (1 : ℤ) u : ℂ)‖ := by
  have key : (A + B * (fourier (1 : ℤ) v : ℂ) + C * (fourier (1 : ℤ) (u - v) : ℂ))
        * (fourier (1 : ℤ) v : ℂ)
      = B * (fourier (1 : ℤ) v : ℂ) ^ 2 + A * (fourier (1 : ℤ) v : ℂ)
          + C * (fourier (1 : ℤ) u : ℂ) := by
    linear_combination C * fourier_one_sub u v
  rw [fibreP_eq, ← key, norm_mul, norm_fourier_one, mul_one]

/-- The root condition, in the form the fibre consumes. -/
def NoCircleRoot (A B C : ℂ) (u : UnitAddCircle) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → B * z ^ 2 + A * z + C * (fourier (1 : ℤ) u : ℂ) ≠ 0

theorem fibreP_ne_zero {A B C : ℂ} {u : UnitAddCircle} (hroot : NoCircleRoot A B C u)
    (v : UnitAddCircle) : fibreP A B C u v ≠ 0 := by
  rw [fibreP_quad]
  exact norm_ne_zero_iff.mpr (hroot _ (norm_fourier_one v))

theorem fibreP_pos {A B C : ℂ} {u : UnitAddCircle} (hroot : NoCircleRoot A B C u)
    (v : UnitAddCircle) : 0 < fibreP A B C u v :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (fibreP_ne_zero hroot v))

/-- `hPne`. -/
theorem ae_fibreP_ne_zero {A B C : ℂ} {u : UnitAddCircle} (hroot : NoCircleRoot A B C u) :
    ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreP A B C u v ≠ 0 :=
  Filter.Eventually.of_forall (fun v => fibreP_ne_zero hroot v)

/-- `hint`. -/
theorem integrable_log_fibreP {A B C : ℂ} {u : UnitAddCircle} (hroot : NoCircleRoot A B C u) :
    Integrable (fun v => Real.log |fibreP A B C u v|)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hcont : Continuous (fun v : UnitAddCircle => Real.log |fibreP A B C u v|) :=
    (continuous_fibreP A B C u).abs.log
      (fun v => ne_of_gt (abs_pos.mpr (fibreP_ne_zero hroot v)))
  first
    | exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    | exact hcont.integrable

/-! ### `hGnz` — a LIVE fibre, for an arbitrary `L²` window

`HRTShift.exists_live_slice` is abstract in both factors, but what it returns is a SINGLE live
fibre — not quite enough here, because the cocycle only holds for a.e. `u`, and that one `u` could
sit in the exceptional null set.  The form proved below says the DEAD fibres are not conull, which
does meet every conull set; `exists_live_fibre_of_ae` then picks a live fibre inside any
a.e.-property at all. -/

theorem norm_zakCLM (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖zakCLM f‖ = ‖f‖ := by
  first
    | exact norm_zakOf f
    | simpa [zakCLM] using norm_zakOf f

/-- The transform read on the sheared product. -/
noncomputable def zakProd (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
  Lp.compMeasurePreserving _ HRTZakL2.measurePreserving_prodToTorusHaar (zakCLM f)

theorem norm_zakProd (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖zakProd f‖ = ‖f‖ := by
  rw [zakProd, Lp.norm_compMeasurePreserving (zakCLM f)
    HRTZakL2.measurePreserving_prodToTorusHaar]
  exact norm_zakCLM f

theorem coeFn_zakProd (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (↑↑(zakProd f) : UnitAddCircle × UnitAddCircle → ℂ)
      =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle]
        (↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) ∘ toTor :=
  Lp.coeFn_compMeasurePreserving (zakCLM f) HRTZakL2.measurePreserving_prodToTorusHaar

theorem measurable_fibreG_swap (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Measurable (fun q : UnitAddCircle × UnitAddCircle => fibreG f q.1 q.2) := by
  unfold fibreG
  exact ((measurable_zakRep f).comp
    (measurable_toTor.comp (measurable_snd.prodMk measurable_fst))).norm

/-- **`hGnz`, in the form that meets every conull set.** -/
theorem not_ae_ae_fibreG_zero {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    ¬ (∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreG f u v = 0) := by
  intro hcon
  have hmeas : MeasurableSet {q : UnitAddCircle × UnitAddCircle | fibreG f q.1 q.2 = 0} :=
    (measurable_fibreG_swap f) (measurableSet_singleton 0)
  have hq : ∀ᵐ q ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
      AddCircle.haarAddCircle), fibreG f q.1 q.2 = 0 :=
    (Measure.ae_prod_iff_ae_ae hmeas).mpr hcon
  have hswap : Measure.QuasiMeasurePreserving
      (Prod.swap : UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    refine ⟨measurable_swap, ?_⟩
    rw [Measure.prod_swap]
  have hp : ∀ᵐ p ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
      AddCircle.haarAddCircle), fibreG f p.2 p.1 = 0 := hswap.ae hq
  have hrep := (HRTZakL2.measurePreserving_prodToTorusHaar).quasiMeasurePreserving.ae_eq_comp
    (zakRep_ae f)
  have hzero : (↑↑(zakProd f) : UnitAddCircle × UnitAddCircle → ℂ)
      =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle] 0 := by
    filter_upwards [hp, coeFn_zakProd f, hrep] with p hp0 hc hr
    simp only [Function.comp_apply] at hc hr
    simp only [fibreG] at hp0
    simp only [Pi.zero_apply]
    rw [hc, hr]
    exact norm_eq_zero.mp hp0
  have hz0 : zakProd f = 0 := Lp.eq_zero_iff_ae_eq_zero.mpr hzero
  have hn : ‖f‖ = 0 := by rw [← norm_zakProd f, hz0, norm_zero]
  exact hf (norm_eq_zero.mp hn)

/-- **A live fibre inside ANY conull set.**  The Birkhoff step needs a single `u` that is
simultaneously live and in the (conull) set where the cocycle holds; this supplies it. -/
theorem exists_live_fibre_of_ae {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0)
    {Q : UnitAddCircle → Prop}
    (hQ : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), Q u) :
    ∃ u : UnitAddCircle, Q u ∧
      ¬ (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreG f u v = 0) := by
  by_contra hcon
  first
    | push_neg at hcon
    | push Not at hcon
  exact not_ae_ae_fibreG_zero hf (by filter_upwards [hQ] with u hu using hcon u hu)

/-! ### The Birkhoff step

Every hypothesis of `BirkhoffErgodic.integral_log_eq_of_modulus_cocycle` is now in hand, and
`HRTReduction.ae_ne_zero_of_cocycle` — abstract in the space, so it applies here unchanged —
turns the live fibre into `hGne`.  The rotation is ergodic exactly when the shift is irrational,
by the same `volume_eq_haar_one` bridge `HRTReduction.ergodic_sub_sqrt2` uses. -/

theorem ergodic_add_irrational {a : ℝ} (ha : Irrational a) :
    Ergodic (fun x : UnitAddCircle => x + ((a : ℝ) : UnitAddCircle))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rw [← ZakPeriodization.volume_eq_haar_one, AddCircle.ergodic_add_right,
    addOrderOf_eq_zero_iff, AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro q hq
  rw [div_one] at hq
  exact ha ⟨q, hq⟩

/-- **THE MEAN, ON A LIVE FIBRE, FOR EVERY `L²` WINDOW.**

    ∫ log |symbol| = log ‖D‖

with no compact support anywhere.  This is the statement
`HRTCocycle.rootCount_of_dependence_compactSupport` obtains only for compactly supported windows;
the route here goes through `zakCLM`, whose linearity is unconditional.

The fibre `u` is chosen so that the cocycle, the root condition AND liveness all hold at it —
that simultaneity is what `exists_live_fibre_of_ae` buys. -/
theorem exists_fibre_mean {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hairr : Irrational a) (hD : D ≠ 0)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0)
    (hroot : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), NoCircleRoot A B C u) :
    ∃ u : UnitAddCircle, NoCircleRoot A B C u ∧
      ∫ v, Real.log |fibreP A B C u v|
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) = Real.log ‖D‖ := by
  have hErg := ergodic_add_irrational hairr
  have hdpos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  have hQ : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          |fibreP A B C u v| * |fibreG f u v|
            = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))|)
        ∧ NoCircleRoot A B C u := by
    filter_upwards [cocycle_fibre_rep A B C D a ha0 ha1 f hae hdep, hroot] with u h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨u, ⟨hcoc, hnr⟩, hlive⟩ := exists_live_fibre_of_ae hf hQ
  refine ⟨u, hnr, ?_⟩
  have hGne : ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreG f u v ≠ 0 :=
    HRTReduction.ae_ne_zero_of_cocycle hErg hdpos (measurable_fibreG f u)
      (ae_fibreP_ne_zero hnr) hcoc hlive
  exact integral_log_eq_of_modulus_cocycle hErg.toMeasurePreserving hdpos
    (measurable_fibreG f u) (measurable_fibreP A B C u) hGne (ae_fibreP_ne_zero hnr)
    hcoc (integrable_log_fibreP hnr)

/-! ### The Jensen side — handing the mean back to the campaign's machinery

`HRTMaster.rootCount_eq_one_of_symbol_mean` consumes an INTERVAL integral of
`log ‖ZakPeriodization.symbol …‖`, so two impedance mismatches have to be crossed:

* **Haar vs `volume`** on the circle — equal, by `ZakPeriodization.volume_eq_haar_one`, but not
  the same instance term (the trap this file meets repeatedly).
* **the coefficient convention** — the campaign's quadratic is `C z² + A z + B e(−2πiθ)` while
  `fibreP_quad` gives `B z² + A z + C w`.  So the campaign's `B` and `C` are SWAPPED relative to
  ours, and its fibre parameter is `θ = −rep1 u`, which is exactly the `θ` with
  `e^{−2πiθ} = fourier 1 u`.  Getting this backwards would be invisible — both sides are honest
  moduli of quadratics — so it is recorded as a lemma. -/

theorem fibreP_nonneg (A B C : ℂ) (u v : UnitAddCircle) : 0 ≤ fibreP A B C u v := norm_nonneg _

theorem circle_integral_eq_interval_real (F : UnitAddCircle → ℝ) :
    (∫ b, F b ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      = ∫ t in (0:ℝ)..1, F ((t : ℝ) : UnitAddCircle) := by
  rw [← ZakPeriodization.volume_eq_haar_one]
  have h := AddCircle.intervalIntegral_preimage (1:ℝ) 0 F
  rw [zero_add] at h
  exact h.symm

/-- **The fibre symbol IS the campaign's symbol**, with `B`/`C` swapped and `θ = −rep1 u`. -/
theorem fibreP_eq_symbol (A B C : ℂ) (u : UnitAddCircle) (t : ℝ) :
    fibreP A B C u ((t : ℝ) : UnitAddCircle)
      = ‖ZakPeriodization.symbol A C B (-(rep1 u)) t‖ := by
  have hz : (fourier (1 : ℤ) ((t : ℝ) : UnitAddCircle) : ℂ)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
    rw [fourier_eq_ee 1 t]
    unfold HRTTransfer.ee
    congr 1
    push_cast
    ring
  have hw : (fourier (1 : ℤ) u : ℂ)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((-(rep1 u) : ℝ) : ℂ))) := by
    rw [fourier_eq_ee_rep 1 u]
    unfold HRTTransfer.ee
    congr 1
    push_cast
    ring
  rw [fibreP_quad, ZakPeriodization.norm_symbol_eq_norm_quadratic, hz, hw]

/-- **THE MEAN, IN THE CAMPAIGN'S OWN FORM.**  For every `L²` window with a `Λ₀`-dependence, some
fibre satisfies the hypothesis `HRTMaster.rootCount_eq_one_of_symbol_mean` wants — and no compact
support was used anywhere in reaching it. -/
theorem exists_fibre_symbol_mean {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hairr : Irrational a) (hD : D ≠ 0)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0)
    (hroot : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), NoCircleRoot A B C u) :
    ∃ u : UnitAddCircle, NoCircleRoot A B C u ∧
      (∫ t in (0:ℝ)..1, Real.log ‖ZakPeriodization.symbol A C B (-(rep1 u)) t‖)
        = Real.log ‖D‖ := by
  obtain ⟨u, hnr, hmean⟩ := exists_fibre_mean A B C D a ha0 ha1 hairr hD f hf hae hdep hroot
  refine ⟨u, hnr, ?_⟩
  have hpt : ∀ t : ℝ, Real.log ‖ZakPeriodization.symbol A C B (-(rep1 u)) t‖
      = Real.log |fibreP A B C u ((t : ℝ) : UnitAddCircle)| := by
    intro t
    rw [abs_of_nonneg (fibreP_nonneg A B C u _), fibreP_eq_symbol]
  rw [← hmean, circle_integral_eq_interval_real (fun v => Real.log |fibreP A B C u v|)]
  exact intervalIntegral.integral_congr (fun t _ => hpt t)

/-! ### The degree condition, with NO compact support

`HRTAssembly.rootCount_of_dependence_compactSupport` carries `hcs` because it routes through the
POINTWISE fibre — `hGmeas` and `hcocPt` are the two places it enters.  Feeding the mean instead to
`HRTMaster.rootCount_eq_one_of_symbol_mean`, which mentions no window at all, avoids both.

The factorisation is quantified over `θ` rather than fixed, because the fibre — and hence
`θ = −rep1 u` — is chosen by the argument, not by the caller. -/

theorem fourier_one_eq_exp_neg (u : UnitAddCircle) :
    (fourier (1 : ℤ) u : ℂ)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((-(rep1 u) : ℝ) : ℂ))) := by
  rw [fourier_eq_ee_rep 1 u]
  unfold HRTTransfer.ee
  congr 1
  push_cast
  ring

/-- Roots off the unit circle give the `NoCircleRoot` the fibre needs. -/
theorem noCircleRoot_of_fac {A B C : ℂ} {u : UnitAddCircle} {ζ₁ ζ₂ : ℂ} (hB : B ≠ 0)
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hfac : ∀ z : ℂ, B * z ^ 2 + A * z
        + C * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((-(rep1 u) : ℝ) : ℂ)))
      = B * (z - ζ₁) * (z - ζ₂)) :
    NoCircleRoot A B C u := by
  intro z hz
  rw [fourier_one_eq_exp_neg u, hfac z]
  exact mul_ne_zero (mul_ne_zero hB (sub_ne_zero.mpr (fun h => h1 (h ▸ hz))))
    (sub_ne_zero.mpr (fun h => h2 (h ▸ hz)))

/-- **THE DEGREE CONDITION FOR AN ARBITRARY `L²` WINDOW.**  The `hcs`-free analogue of
`HRTAssembly.rootCount_of_dependence_compactSupport`. -/
theorem exists_rootCount_of_dependence_L2 {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hairr : Irrational a)
    (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDB : ‖D‖ ≠ ‖B‖) (hDC : ‖D‖ ≠ ‖C‖)
    (hroots : ∀ θ : ℝ, ∃ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, B * z ^ 2 + A * z
            + C * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
          = B * (z - ζ₁) * (z - ζ₂)) ∧ ‖ζ₁‖ ≠ 1 ∧ ‖ζ₂‖ ≠ 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∃ ζ₁ ζ₂ : ℂ, HRTResonant.rootCount ζ₁ ζ₂ = 1 := by
  have hnr : ∀ u : UnitAddCircle, NoCircleRoot A B C u := by
    intro u
    obtain ⟨ζ₁, ζ₂, hfac, h1, h2⟩ := hroots (-(rep1 u))
    exact noCircleRoot_of_fac hB h1 h2 hfac
  obtain ⟨u, -, hmean⟩ := exists_fibre_symbol_mean A B C D a ha0 ha1 hairr hD f hf hae hdep
    (Filter.Eventually.of_forall hnr)
  obtain ⟨ζ₁, ζ₂, hfac, h1, h2⟩ := hroots (-(rep1 u))
  exact ⟨ζ₁, ζ₂, HRTMaster.rootCount_eq_one_of_symbol_mean A C B D (-(rep1 u)) ζ₁ ζ₂
    hC hB hD hDB hDC hfac h1 h2 hmean⟩

/-! ### The mean in the campaign's coefficient convention

`HRTResonant.heil_speegle_lambda_zero_of_fibre_mean` wants the mean of `log ‖C z² + A z + B w‖`,
while `fibreP_quad` produces `log ‖B z² + A z + C w‖` — the REVERSE polynomial, whose roots are
genuinely different, so this is not a relabelling and must not be waved through.

They reconcile with no conjugation at all.  Writing `z = fourier 1 v`, `y = fourier 1 (u − v)`,
so that `y · z = w`:

    B z² + A z + C w = z · (B z + A + C y)        C y² + A y + B w = y · (C y + A + B z)

— the SAME bracket, and both prefactors are unimodular.  So the two integrands agree pointwise
under `v ↦ u − v`, which is measure preserving.  Recorded as a lemma: a coefficient convention
got backwards is exactly the error that fails invisibly, since both sides are honest moduli of
quadratics with the same modulus at every point of the circle. -/

theorem fourier_one_coe (t : ℝ) :
    (fourier (1 : ℤ) ((t : ℝ) : UnitAddCircle) : ℂ)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
  rw [fourier_eq_ee 1 t]
  unfold HRTTransfer.ee
  congr 1
  push_cast
  ring

theorem fibreP_eq_campaign (A B C : ℂ) (u v : UnitAddCircle) :
    fibreP A B C u v
      = ‖C * (fourier (1 : ℤ) (u - v) : ℂ) ^ 2 + A * (fourier (1 : ℤ) (u - v) : ℂ)
          + B * (fourier (1 : ℤ) u : ℂ)‖ := by
  have hyz : (fourier (1 : ℤ) (u - v) : ℂ) * (fourier (1 : ℤ) v : ℂ)
      = (fourier (1 : ℤ) u : ℂ) := fourier_one_sub u v
  have e1 : B * (fourier (1 : ℤ) v : ℂ) ^ 2 + A * (fourier (1 : ℤ) v : ℂ)
        + C * (fourier (1 : ℤ) u : ℂ)
      = (fourier (1 : ℤ) v : ℂ)
        * (B * (fourier (1 : ℤ) v : ℂ) + A + C * (fourier (1 : ℤ) (u - v) : ℂ)) := by
    rw [← hyz]; ring
  have e2 : C * (fourier (1 : ℤ) (u - v) : ℂ) ^ 2 + A * (fourier (1 : ℤ) (u - v) : ℂ)
        + B * (fourier (1 : ℤ) u : ℂ)
      = (fourier (1 : ℤ) (u - v) : ℂ)
        * (C * (fourier (1 : ℤ) (u - v) : ℂ) + A + B * (fourier (1 : ℤ) v : ℂ)) := by
    rw [← hyz]; ring
  rw [fibreP_quad, e1, e2, norm_mul, norm_mul, norm_fourier_one, norm_fourier_one,
    one_mul, one_mul]
  congr 1
  ring

theorem measurePreserving_sub_circle (u : UnitAddCircle) :
    MeasurePreserving (fun v : UnitAddCircle => u - v)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  Measure.measurePreserving_sub_left _ u

/-- The change of variables `v ↦ u − v`, on the circle. -/
theorem mean_campaign_circle (A B C : ℂ) (u : UnitAddCircle) :
    (∫ v, Real.log |fibreP A B C u v| ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      = ∫ y, Real.log ‖C * (fourier (1 : ℤ) y : ℂ) ^ 2 + A * (fourier (1 : ℤ) y : ℂ)
            + B * (fourier (1 : ℤ) u : ℂ)‖
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  refine Eq.trans ?_ ((measurePreserving_sub_circle u).integral_comp
    (measurableEmbedding_subLeft u)
    (fun y : UnitAddCircle => Real.log ‖C * (fourier (1 : ℤ) y : ℂ) ^ 2
      + A * (fourier (1 : ℤ) y : ℂ) + B * (fourier (1 : ℤ) u : ℂ)‖))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  dsimp only
  rw [abs_of_nonneg (fibreP_nonneg A B C u v), fibreP_eq_campaign]

/-- **The mean, in the shape the capstone consumes** — an interval integral of the campaign's
quadratic. -/
theorem mean_campaign_interval (A B C : ℂ) (u : UnitAddCircle) :
    (∫ v, Real.log |fibreP A B C u v| ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      = ∫ t in (0:ℝ)..1,
          Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
            + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
            + B * (fourier (1 : ℤ) u : ℂ)‖ := by
  rw [mean_campaign_circle, circle_integral_eq_interval_real]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [fourier_one_coe t]

/-! ### The live fibres are INFINITE

The capstone needs an infinite set `L` of unimodular parameters, not a single one.  A finite set
is null on the circle, so if the good fibres were finite then a.e. fibre would be dead — which
`not_ae_ae_fibreG_zero` forbids. -/

theorem injective_fourier_one :
    Function.Injective (fun u : UnitAddCircle => (fourier (1 : ℤ) u : ℂ)) := by
  have h : (fun u : UnitAddCircle => (fourier (1 : ℤ) u : ℂ))
      = fun u : UnitAddCircle => ((AddCircle.toCircle u : Circle) : ℂ) := by
    funext u
    rw [fourier_one]
  rw [h]
  exact Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)

theorem infinite_live_fibres {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0)
    {Q : UnitAddCircle → Prop}
    (hQ : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), Q u) :
    {u : UnitAddCircle | Q u ∧
      ¬ (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          fibreG f u v = 0)}.Infinite := by
  intro hfin
  refine not_ae_ae_fibreG_zero hf ?_
  have hnull := Set.Finite.measure_zero hfin (AddCircle.haarAddCircle : Measure UnitAddCircle)
  have hae_not : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      ¬ (Q u ∧ ¬ (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          fibreG f u v = 0)) :=
    ae_iff.mpr (by simpa only [not_not] using hnull)
  filter_upwards [hQ, hae_not] with u hu hnot
  by_contra hlive
  exact hnot ⟨hu, hlive⟩

/-! ### The Birkhoff mean at a NAMED good fibre

`exists_fibre_mean` produces a fibre; the capstone needs the mean at every fibre of an infinite
family, so the core is factored out here. -/

theorem fibre_mean_of_good {A B C D : ℂ} {a : ℝ} (hairr : Irrational a) (hD : D ≠ 0)
    {f : Lp ℂ 2 (volume : Measure ℝ)} {u : UnitAddCircle} (hnr : NoCircleRoot A B C u)
    (hcoc : ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      |fibreP A B C u v| * |fibreG f u v|
        = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))|)
    (hlive : ¬ (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreG f u v = 0)) :
    ∫ v, Real.log |fibreP A B C u v|
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) = Real.log ‖D‖ := by
  have hErg := ergodic_add_irrational hairr
  have hdpos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  have hGne := HRTReduction.ae_ne_zero_of_cocycle hErg hdpos (measurable_fibreG f u)
    (ae_fibreP_ne_zero hnr) hcoc hlive
  exact integral_log_eq_of_modulus_cocycle hErg.toMeasurePreserving hdpos
    (measurable_fibreG f u) (measurable_fibreP A B C u) hGne (ae_fibreP_ne_zero hnr)
    hcoc (integrable_log_fibreP hnr)

/-! ### `NoCircleRoot` holds for ALMOST EVERY fibre

The campaign always ASSUMED the root condition (`‖ζᵢ‖ ≠ 1` is a hypothesis of
`rootCount_of_cocycle` and of everything above it).  It does not have to be assumed.  If
`B z² + A z + C w = 0` with `‖z‖ = ‖w‖ = 1`, then conjugating and substituting `z̄ = z⁻¹`,
`w̄ = w⁻¹` eliminates `w` entirely and leaves

    (Ā B) z³ + (‖A‖² + ‖B‖² − ‖C‖²) z² + (A B̄) z = 0,

i.e. — after cancelling `z ≠ 0` — a genuine quadratic whose leading coefficient `Ā B` is nonzero
whenever `A, B ≠ 0`.  So at most two `z` can occur, each of which determines `w`; the bad fibres
are finite, hence null. -/

theorem finite_quadratic_roots {a b c : ℂ} (ha : a ≠ 0) :
    {z : ℂ | a * z ^ 2 + b * z + c = 0}.Finite := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (discrim a b c) (n := 2) (by norm_num)
  refine Set.Finite.subset
    ((Set.finite_singleton ((-b - s) / (2 * a))).insert ((-b + s) / (2 * a))) ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  have hz' : a * (z * z) + b * z + c = 0 := by linear_combination hz
  have hdisc : discrim a b c = s * s := by rw [← hs]; ring
  rcases (quadratic_eq_zero_iff ha hdisc z).mp hz' with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr h)

theorem finite_badW {A B C : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    {w : ℂ | ‖w‖ = 1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧ B * z ^ 2 + A * z + C * w = 0}.Finite := by
  have hZfin : {z : ℂ | (starRingEnd ℂ) A * B * z ^ 2
      + (A * (starRingEnd ℂ) A + B * (starRingEnd ℂ) B - C * (starRingEnd ℂ) C) * z
      + A * (starRingEnd ℂ) B = 0}.Finite :=
    finite_quadratic_roots (mul_ne_zero (by simpa using hA) hB)
  refine Set.Finite.subset (hZfin.image (fun z : ℂ => -(B * z ^ 2 + A * z) / C)) ?_
  rintro w ⟨hw1, z, hz1, heq⟩
  have hzc : z * (starRingEnd ℂ) z = 1 := by simp [Complex.mul_conj', hz1]
  have hwc : w * (starRingEnd ℂ) w = 1 := by simp [Complex.mul_conj', hw1]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz1
    simp at hz1
  have hconj : (starRingEnd ℂ) B * ((starRingEnd ℂ) z) ^ 2
      + (starRingEnd ℂ) A * (starRingEnd ℂ) z
      + (starRingEnd ℂ) C * (starRingEnd ℂ) w = 0 := by
    have h := congrArg (starRingEnd ℂ) heq
    simpa using h
  have key : z * ((starRingEnd ℂ) A * B * z ^ 2
      + (A * (starRingEnd ℂ) A + B * (starRingEnd ℂ) B - C * (starRingEnd ℂ) C) * z
      + A * (starRingEnd ℂ) B) = 0 := by
    linear_combination ((starRingEnd ℂ) B + (starRingEnd ℂ) A * z) * heq
      - C * z ^ 2 * w * hconj
      + (C * (starRingEnd ℂ) B * w * (1 + z * (starRingEnd ℂ) z)
          + C * (starRingEnd ℂ) A * z * w) * hzc
      + C * (starRingEnd ℂ) C * z ^ 2 * hwc
  refine ⟨z, (mul_eq_zero.mp key).resolve_left hz0, ?_⟩
  field_simp
  linear_combination -heq

theorem ae_noCircleRoot {A B C : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), NoCircleRoot A B C u := by
  have hsub : {u : UnitAddCircle | ¬ NoCircleRoot A B C u}
      ⊆ (fun u : UnitAddCircle => (fourier (1 : ℤ) u : ℂ)) ⁻¹'
        {w : ℂ | ‖w‖ = 1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧ B * z ^ 2 + A * z + C * w = 0} := by
    intro u hu
    simp only [Set.mem_setOf_eq, NoCircleRoot] at hu
    push Not at hu
    obtain ⟨z, hz1, hz2⟩ := hu
    exact ⟨norm_fourier_one u, z, hz1, hz2⟩
  have hfin : {u : UnitAddCircle | ¬ NoCircleRoot A B C u}.Finite :=
    Set.Finite.subset (Set.Finite.preimage (injective_fourier_one.injOn)
      (finite_badW hA hB hC)) hsub
  exact ae_iff.mpr (Set.Finite.measure_zero hfin _)

/-! ### THE REDUCTION, for an arbitrary `L²` window

Exactly the package `HRTResonant.heil_speegle_lambda_zero_of_fibre_mean`'s `hreduction` asks for,
apart from the two codimension-one non-degeneracies `‖D‖ ≠ ‖C‖`, `‖D‖ ≠ ‖B‖` — which are
conditions on the COEFFICIENTS of the dependence, not on the window, and so cannot come from
here. -/
theorem exists_infinite_mean {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hairr : Irrational a) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    ∃ L : Set ℂ, L.Infinite ∧ (∀ w ∈ L, ‖w‖ = 1)
      ∧ (∀ w ∈ L, (∫ t in (0:ℝ)..1,
          Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
            + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
        = Real.log ‖D‖) := by
  have hQ : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          |fibreP A B C u v| * |fibreG f u v|
            = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))|)
        ∧ NoCircleRoot A B C u := by
    filter_upwards [cocycle_fibre_rep A B C D a ha0 ha1 f hae hdep,
      ae_noCircleRoot hA hB hC] with u h1 h2
    exact ⟨h1, h2⟩
  have hSinf := infinite_live_fibres hf hQ
  refine ⟨(fun u : UnitAddCircle => (fourier (1 : ℤ) u : ℂ)) ''
    {u : UnitAddCircle | ((∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          |fibreP A B C u v| * |fibreG f u v|
            = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))|)
        ∧ NoCircleRoot A B C u)
      ∧ ¬ (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreG f u v = 0)},
    hSinf.image injective_fourier_one.injOn, ?_, ?_⟩
  · rintro w ⟨u, -, rfl⟩
    exact norm_fourier_one u
  · rintro w ⟨u, ⟨⟨hcoc, hnr⟩, hlive⟩, rfl⟩
    rw [← mean_campaign_interval A B C u]
    exact fibre_mean_of_good hairr hD hnr hcoc hlive

/-! ### Lifting the shift out of `[0,1)`

Every theorem in the shift chain carries `a < 1`, inherited from `rep1_sub`'s fundamental domain.
**Λ₀'s fourth point is `(√2, √2)`, and `√2 > 1`**, so the chain as stated does not reach it.

`modTransCLM` is however defined for EVERY `a` — only its Zak formula needs the fundamental
domain — and the operator factors:

    M_{1+a} T_{1+a} = M₁ ∘ (M_a T_a) ∘ T₁

Each factor has a known multiplier (`chiM1`, `psiRot a` with the `antidiag a` shift, `chiT1`), and
all three are UNIMODULAR.  So a dependence with shift `1 + a` yields the cocycle with the point
moved by `antidiag a` — the fractional part, back inside `[0,1)` — and with `‖D‖` untouched. -/

theorem coeFn_transL (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (↑↑(transL a f) : ℝ → ℂ) =ᵐ[volume] (↑↑f : ℝ → ℂ) ∘ (fun y : ℝ => y - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right (volume : Measure ℝ) a)

theorem coeFn_modCLM (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (↑↑(modCLM a f) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ))
        * (↑↑f : ℝ → ℂ) y :=
  coeFn_multLC (μ := (volume : Measure ℝ))
    (φ := fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)))
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
    (fun y => norm_modChar a y) f

theorem coeFn_mod1CLM (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (↑↑(mod1CLM f) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * (↑↑f : ℝ → ℂ) y :=
  coeFn_multLC (μ := (volume : Measure ℝ))
    (φ := fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)))
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
    (fun y => by rw [Complex.norm_exp]; simp) f

/-- **The composite.**  `M_{1+a} T_{1+a} = M₁ ∘ (M_a T_a) ∘ T₁`, as operators on `L²(ℝ)`. -/
theorem modTransCLM_succ (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modTransCLM (1 + a) f = mod1CLM (modTransCLM a (transL 1 f)) := by
  refine Lp.ext_iff.mpr ?_
  have hL : (↑↑(modTransCLM (1 + a) f) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 + a : ℝ) : ℂ) * (y : ℂ))
        * (↑↑f : ℝ → ℂ) (y - (1 + a)) := by
    have h1 : (↑↑(modTransCLM (1 + a) f) : ℝ → ℂ)
        =ᵐ[volume] (↑↑(modCLM (1 + a) (transL (1 + a) f)) : ℝ → ℂ) := by rfl
    refine h1.trans ((coeFn_modCLM (1 + a) (transL (1 + a) f)).trans ?_)
    filter_upwards [coeFn_transL (1 + a) f] with y hy
    simp only [Function.comp_apply] at hy
    simp only [hy]
  have hR : (↑↑(mod1CLM (modTransCLM a (transL 1 f))) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 + a : ℝ) : ℂ) * (y : ℂ))
        * (↑↑f : ℝ → ℂ) (y - (1 + a)) := by
    refine (coeFn_mod1CLM (modTransCLM a (transL 1 f))).trans ?_
    have h2 : (↑↑(modTransCLM a (transL 1 f)) : ℝ → ℂ)
        =ᵐ[volume] (↑↑(modCLM a (transL a (transL 1 f))) : ℝ → ℂ) := by rfl
    have h3 := (h2.trans (coeFn_modCLM a (transL a (transL 1 f))))
    have h6 := (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_transL 1 f)
    filter_upwards [h3, coeFn_transL a (transL 1 f), h6] with y h3y h4y h6y
    simp only [Function.comp_apply] at h4y h6y
    rw [h3y, h4y, h6y]
    have hsub : y - a - 1 = y - (1 + a) := by ring
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)
        + 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * ((1 + a : ℝ) : ℂ) * (y : ℂ) := by
      push_cast
      ring
    rw [hsub, ← mul_assoc, ← Complex.exp_add, harg]
  exact hL.trans hR.symm

/-- The dependence in the `zakCLM` picture, for a shift of `1 + a`.  The `D` term now carries
THREE unimodular multipliers instead of one — `chiM1`, `psiRot a`, and `chiT1` evaluated at the
shifted point — but the point still moves only by `antidiag a`. -/
theorem zakCLM_dep_succ {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 + a : ℝ) : ℂ) * (y : ℂ))
            * g (y - (1 + a))) = 0) :
    A • zakCLM f
      + B • (HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1 (zakCLM f))
      + C • (HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM f))
      + D • (HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1
          (HRTShift.multLC
            (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
            (measurable_psiRot a) (norm_psiRot a)
            (antidiagL a (HRTShift.multLC
              (μ := Measure.pi
                (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
              measurable_chiT1 norm_chiT1 (zakCLM f))))) = 0 := by
  have h0 := dep_Lp A B C D (1 + a) f hae hdep
  rw [modTransCLM_succ a f] at h0
  have h1 : zakCLM (A • f + B • (transL 1 f) + C • (mod1CLM f)
      + D • (mod1CLM (modTransCLM a (transL 1 f)))) = 0 := by rw [h0, map_zero]
  simp only [map_add, map_smul] at h1
  have e1 : zakCLM (transL 1 f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1 (zakCLM f) :=
    congrFun zakL2_transOne_of_memLp f
  have e2 : zakCLM (mod1CLM f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM f) :=
    congrFun zakL2_modOne_of_memLp f
  have e3 : zakCLM (mod1CLM (modTransCLM a (transL 1 f)))
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM (modTransCLM a (transL 1 f))) :=
    congrFun zakL2_modOne_of_memLp (modTransCLM a (transL 1 f))
  have e4 : zakCLM (modTransCLM a (transL 1 f))
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (measurable_psiRot a) (norm_psiRot a) (antidiagL a (zakCLM (transL 1 f))) :=
    congrFun (zakL2_modShift_of_memLp a ha0 ha1) (transL 1 f)
  rw [e3, e4, e1, e2] at h1
  exact h1

/-- **THE COCYCLE FOR A SHIFT OF `1 + a`.**  Identical conclusion to `cocycle_norm` — the three
extra multipliers are unimodular, so they vanish under `‖·‖` and `‖D‖` is untouched.  This is what
puts `√2` in reach: apply it with `a = √2 − 1 ∈ (0,1)`. -/
theorem cocycle_norm_succ {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 + a : ℝ) : ℂ) * (y : ℂ))
            * g (y - (1 + a))) = 0) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
      ‖symbolTor A B C x‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) x‖
        = ‖D‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (antidiagT a x)‖ := by
  set μT := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) with hμT
  set Z := zakCLM f with hZ
  set T1 := HRTShift.multLC (μ := μT) measurable_chiT1 norm_chiT1 Z with hT1
  set M1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 Z with hM1
  set S0 := HRTShift.multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a) (antidiagL a T1)
    with hS0
  set S := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 S0 with hS
  have h0 : A • Z + B • T1 + C • M1 + D • S = 0 :=
    zakCLM_dep_succ A B C D a ha0 ha1 f hae hdep
  have hcoe : (↑↑(A • Z + B • T1 + C • M1 + D • S) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[μT] 0 := by
    rw [h0]; exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μT)
  have hT1shift := (measurePreserving_antidiagT a).quasiMeasurePreserving.ae_eq_comp
    (coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z)
  have hpt : ∀ᵐ x ∂μT, symbolTor A B C x * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) x
      = -(D * (chiM1 x * (psiRot a x
          * (chiT1 (antidiagT a x) * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) (antidiagT a x))))) := by
    filter_upwards [hcoe,
      Lp.coeFn_add (A • Z + B • T1 + C • M1) (D • S),
      Lp.coeFn_add (A • Z + B • T1) (C • M1),
      Lp.coeFn_add (A • Z) (B • T1),
      Lp.coeFn_smul A Z, Lp.coeFn_smul B T1, Lp.coeFn_smul C M1, Lp.coeFn_smul D S,
      coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z,
      coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 Z,
      coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 S0,
      coeFn_multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a) (antidiagL a T1),
      coeFn_antidiagL a T1, hT1shift]
      with x hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mS0 mA mT
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Function.comp_apply] at hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mS0 mA mT
    rw [e1, e2, e3, s1, s2, s3, s4, m1, m2, mS, mS0, mA, mT] at hz
    unfold symbolTor
    linear_combination hz
  filter_upwards [hpt] with x hx
  have h := congrArg norm hx
  simp only [norm_mul, norm_neg, norm_chiM1, norm_psiRot, norm_chiT1, one_mul] at h
  exact h

/-! ### The endgame, re-based on the cocycle as a HYPOTHESIS

`cocycle_norm` is the only place the shift enters analytically; everything after it merely
transports the relation.  Restating that tail with the cocycle as a hypothesis lets BOTH routes —
the direct `a ∈ [0,1)` dependence and the `1 + a` composite — feed one endgame, with no
duplication. -/

/-- The cocycle relation on the torus: the single analytic input the endgame needs. -/
def CocycleNorm (A B C D : ℂ) (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
    ‖symbolTor A B C x‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) x‖
      = ‖D‖ * ‖(↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (antidiagT a x)‖

theorem cocycle_norm_rep_of {A B C D : ℂ} {a : ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hcn : CocycleNorm A B C D a f) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
      ‖symbolTor A B C x‖ * ‖zakRep f x‖ = ‖D‖ * ‖zakRep f (antidiagT a x)‖ := by
  have hshift := (measurePreserving_antidiagT a).quasiMeasurePreserving.ae_eq_comp (zakRep_ae f)
  filter_upwards [hcn, zakRep_ae f, hshift] with x hx h1 h2
  simp only [Function.comp_apply] at h2
  rw [← h1, ← h2]
  exact hx

theorem cocycle_prod_rep_of {A B C D : ℂ} {a : ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hcn : CocycleNorm A B C D a f) :
    ∀ᵐ q ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle),
      ‖symbolTor A B C (toTor q)‖ * ‖zakRep f (toTor q)‖
        = ‖D‖ * ‖zakRep f (toTor (q.1 + ((a : ℝ) : UnitAddCircle), q.2))‖ := by
  have hT := (HRTZakL2.measurePreserving_prodToTorusHaar).quasiMeasurePreserving.ae
    (cocycle_norm_rep_of hcn)
  filter_upwards [hT] with q hq
  have hconj : antidiagT a (toTor q)
      = toTor (q.1 + ((a : ℝ) : UnitAddCircle), q.2) := congrFun (toTor_conj_antidiag a) q
  rw [← hconj]
  exact hq

theorem cocycle_fibre_rep_of {A B C D : ℂ} {a : ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hcn : CocycleNorm A B C D a f) :
    ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      ∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        |fibreP A B C u v| * |fibreG f u v|
          = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))| := by
  have h0 := cocycle_prod_rep_of hcn
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.swap : UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) := by
    refine ⟨measurable_swap, ?_⟩
    rw [Measure.prod_swap]
  have h1 := Measure.ae_ae_of_ae_prod (hqmp.ae h0)
  filter_upwards [h1] with u hu
  filter_upwards [hu] with v hv
  unfold fibreP fibreG
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]
  exact hv

/-- **THE REDUCTION, from the cocycle alone.** -/
theorem exists_infinite_mean_of {A B C D : ℂ} {a : ℝ} (hairr : Irrational a)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) (hcn : CocycleNorm A B C D a f) :
    ∃ L : Set ℂ, L.Infinite ∧ (∀ w ∈ L, ‖w‖ = 1)
      ∧ (∀ w ∈ L, (∫ t in (0:ℝ)..1,
          Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
            + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
        = Real.log ‖D‖) := by
  have hQ : ∀ᵐ u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          |fibreP A B C u v| * |fibreG f u v|
            = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))|)
        ∧ NoCircleRoot A B C u := by
    filter_upwards [cocycle_fibre_rep_of hcn, ae_noCircleRoot hA hB hC] with u h1 h2
    exact ⟨h1, h2⟩
  have hSinf := infinite_live_fibres hf hQ
  refine ⟨(fun u : UnitAddCircle => (fourier (1 : ℤ) u : ℂ)) ''
    {u : UnitAddCircle | ((∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
          |fibreP A B C u v| * |fibreG f u v|
            = ‖D‖ * |fibreG f u (v + ((a : ℝ) : UnitAddCircle))|)
        ∧ NoCircleRoot A B C u)
      ∧ ¬ (∀ᵐ v ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), fibreG f u v = 0)},
    hSinf.image injective_fourier_one.injOn, ?_, ?_⟩
  · rintro w ⟨u, -, rfl⟩
    exact norm_fourier_one u
  · rintro w ⟨u, ⟨⟨hcoc, hnr⟩, hlive⟩, rfl⟩
    rw [← mean_campaign_interval A B C u]
    exact fibre_mean_of_good hairr hD hnr hcoc hlive

/-- **THE REDUCTION FOR A SHIFT OF `1 + a`** — the form Λ₀ needs, with `a = √2 − 1`. -/
theorem exists_infinite_mean_succ {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hairr : Irrational a) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 + a : ℝ) : ℂ) * (y : ℂ))
            * g (y - (1 + a))) = 0) :
    ∃ L : Set ℂ, L.Infinite ∧ (∀ w ∈ L, ‖w‖ = 1)
      ∧ (∀ w ∈ L, (∫ t in (0:ℝ)..1,
          Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
            + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
        = Real.log ‖D‖) :=
  exists_infinite_mean_of hairr hA hB hC hD hf
    (cocycle_norm_succ A B C D a ha0 ha1 f hae hdep)

/-! ## Λ₀ — the reduction, DISCHARGED

`HRTResonant.heil_speegle_lambda_zero_of_fibre_mean` asks its `hreduction` for three things: the
two codimension-one non-degeneracies, and an infinite family of unimodular parameters carrying the
mean.  The last of those is exactly `exists_infinite_mean_succ`, now proved for EVERY `L²` window
with no compact support anywhere — so the capstone reduces to `hthree` (three-point HRT, i.e.
Linnell) plus the non-degeneracies.

Both remaining hypotheses are honest: `hthree` is a research input, and the non-degeneracies are
conditions on the dependence COEFFICIENTS which no argument about the window can supply. -/

theorem sqrtTwo_sub_one_nonneg : (0:ℝ) ≤ Real.sqrt 2 - 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [h2, hnn]

theorem sqrtTwo_sub_one_lt_one : Real.sqrt 2 - 1 < 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [h2, hnn]

theorem irrational_sqrtTwo_sub_one : Irrational (Real.sqrt 2 - 1) := by
  simpa using irrational_sqrt_two.sub_natCast 1

/-- **HEIL–SPEEGLE CONJECTURE 2, FOR EVERY `L²` WINDOW.**

The four `Λ₀`-translates of any nonzero `L²` window are linearly independent, assuming only:

* `hthree` — the three-point HRT theorem (Linnell), a genuine research input; and
* `hnd` — the two codimension-one non-degeneracies `‖D‖ ≠ ‖C‖`, `‖D‖ ≠ ‖B‖` on the dependence
  coefficients.

Everything else — the Zak transform as an `L²` isometry, the cocycle, the fibration, the live
fibre, ergodicity, Birkhoff, Jensen, the root condition, and the `√2` shift — is discharged.
**No compact support is assumed at any point**, which is what
`HRTAssembly.rootCount_of_dependence_compactSupport` could not avoid. -/
theorem heil_speegle_lambda_zero_L2 (g : ℝ → ℂ)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (hthree : ∀ c : Fin 4 → ℂ,
        (∑ i, c i • HRTResonant.lambdaZeroFamily g i) = 0 → (∃ i, c i = 0) → ∀ i, c i = 0)
    (hnd : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        (A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
          + D • HRTResonant.modulate (Real.sqrt 2)
              (HRTResonant.timeShift (Real.sqrt 2) g) = 0) →
        ‖D‖ ≠ ‖C‖ ∧ ‖D‖ ≠ ‖B‖) :
    LinearIndependent ℂ (HRTResonant.lambdaZeroFamily g) := by
  have hg0 : g ≠ 0 := by
    intro h
    exact hgne (by simp [h])
  refine HRTResonant.heil_speegle_lambda_zero_of_fibre_mean g hg0 hthree ?_
  intro A B C D hA hB hC hD hdepFun
  obtain ⟨hDC, hDB⟩ := hnd A B C D hA hB hC hD hdepFun
  refine ⟨hDC, hDB, ?_⟩
  have hae : (↑↑(hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hf : hg2.toLp g ≠ 0 := by
    intro h
    refine hgne (hae.symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hsum : (1 : ℝ) + (Real.sqrt 2 - 1) = Real.sqrt 2 := by ring
  have hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * (((1 : ℝ) + (Real.sqrt 2 - 1) : ℝ) : ℂ) * (y : ℂ))
          * g (y - ((1 : ℝ) + (Real.sqrt 2 - 1)))) = 0 := by
    intro y
    have h := congrFun hdepFun y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      HRTResonant.timeShift, HRTResonant.modulate, Complex.ofReal_one, mul_one] at h
    rw [hsum]
    exact h
  exact exists_infinite_mean_succ A B C D (Real.sqrt 2 - 1) sqrtTwo_sub_one_nonneg
    sqrtTwo_sub_one_lt_one irrational_sqrtTwo_sub_one hA hB hC hD (hg2.toLp g) hf hae hdep

/-- **HEIL–SPEEGLE CONJECTURE 2 FOR `Λ₀`, OFF THE CODIMENSION-ONE STRATUM.**

`hthree` is gone.  It does **not** require Linnell's general three-point theorem, because each of
the four three-point subsets of `Λ₀` is individually reducible — the integer lattice
`{(0,0),(1,0),(0,1)}`, a shear for `{(0,0),(0,1),(√2,√2)}`, and the Fourier route for the other
two — and `HRTHthree.hthree_lambdaZero` proves exactly that, axiom-free.

So for every measurable nonzero `L²` window the four `Λ₀`-translates are linearly independent,
with **one** hypothesis remaining: the two codimension-one non-degeneracies on the dependence
coefficients.  Those are the `rootCount ∈ {0,2}` cases (`‖D‖ = ‖C‖` is "both roots inside",
`‖D‖ = ‖B‖` is "both outside"), and they are conditions on the coefficients rather than on the
window, so nothing here can remove them. -/
theorem heil_speegle_lambda_zero_L2_of_nd (g : ℝ → ℂ) (hgm : Measurable g)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (hnd : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        (A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
          + D • HRTResonant.modulate (Real.sqrt 2)
              (HRTResonant.timeShift (Real.sqrt 2) g) = 0) →
        ‖D‖ ≠ ‖C‖ ∧ ‖D‖ ≠ ‖B‖) :
    LinearIndependent ℂ (HRTResonant.lambdaZeroFamily g) :=
  heil_speegle_lambda_zero_L2 g hg2 hgne
    (fun c hsum hex => HRTHthree.hthree_lambdaZero hgm hg2 hgne c hsum hex) hnd

/-! ## The UNCONDITIONAL statement

The conditional form above quantifies `hnd` over every dependence, which is more than the argument
needs: the reduction applies to a SINGLE dependence, so it directly forbids any dependence lying
off the codimension-one stratum.  That is a hypothesis-free theorem, and it is the sharpest thing
this machinery proves. -/

/-- **No `Λ₀`-dependence exists off the codimension-one stratum.**  Hypothesis-free: for a
measurable nonzero `L²` window there is NO dependence with all four coefficients nonzero and
`‖D‖ ≠ ‖C‖`, `‖D‖ ≠ ‖B‖`. -/
theorem no_lambdaZero_dependence_off_stratum {g : ℝ → ℂ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (hdepFun : A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
      + D • HRTResonant.modulate (Real.sqrt 2)
          (HRTResonant.timeShift (Real.sqrt 2) g) = 0) :
    False := by
  have hae : (↑↑(hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hf : hg2.toLp g ≠ 0 := by
    intro h
    refine hgne (hae.symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hsum : (1 : ℝ) + (Real.sqrt 2 - 1) = Real.sqrt 2 := by ring
  have hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * (((1 : ℝ) + (Real.sqrt 2 - 1) : ℝ) : ℂ) * (y : ℂ))
          * g (y - ((1 : ℝ) + (Real.sqrt 2 - 1)))) = 0 := by
    intro y
    have h := congrFun hdepFun y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      HRTResonant.timeShift, HRTResonant.modulate, Complex.ofReal_one, mul_one] at h
    rw [hsum]
    exact h
  obtain ⟨L, hinf, hunit, hmean⟩ :=
    exists_infinite_mean_succ A B C D (Real.sqrt 2 - 1) sqrtTwo_sub_one_nonneg
      sqrtTwo_sub_one_lt_one irrational_sqrtTwo_sub_one hA hB hC hD (hg2.toLp g) hf hae hdep
  exact HRTResonant.live_set_not_infinite_of_fibre_mean A B C D hA hB hC hD hDC hDB
    L hunit hmean hinf

/-- **EVERY `Λ₀`-DEPENDENCE LIES ON THE CODIMENSION-ONE STRATUM.**  Hypothesis-free.

For a measurable nonzero `L²` window, any linear dependence among the four `Λ₀`-translates with
all coefficients nonzero must satisfy `‖D‖ = ‖C‖` (both roots inside the unit circle) or
`‖D‖ = ‖B‖` (both outside).  Heil–Speegle Conjecture 2 for `Λ₀` is exactly the assertion that
neither can happen either; that residue is a genuine research problem, not a formalisation gap. -/
theorem lambdaZero_dependence_forces_norm_eq {g : ℝ → ℂ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hdepFun : A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
      + D • HRTResonant.modulate (Real.sqrt 2)
          (HRTResonant.timeShift (Real.sqrt 2) g) = 0) :
    ‖D‖ = ‖C‖ ∨ ‖D‖ = ‖B‖ := by
  by_contra h
  first
    | push_neg at h
    | push Not at h
  exact no_lambdaZero_dependence_off_stratum hg2 hgne A B C D hA hB hC hD h.1 h.2 hdepFun

/-! ## The PAPER's route: Λ₀ from the ILR degree clause, with no norm conditions

`hrt_lambda0_rigorous.tex` proves its Theorem 1 differently from the chain above.  Where we used
Jensen plus the two codimension-one non-degeneracies to pin `rootCount = 1`, the paper uses the
theorem of **Iwanik–Lemańczyk–Rudolph** on absolutely continuous cocycles over irrational
rotations: the phase cocycle `ξ_θ` has degree `−j−1+N(θ)`, and a nonzero-degree cocycle admits no
measurable unimodular solution, so `N(θ) = 1 + j`.

For `j = 0` that route needs **no** norm conditions at all — in `live_set_subset_four` the clauses
`hj1 : j = 1 → ‖D‖ ≠ ‖C‖` and `hjm1 : j = -1 → ‖D‖ ≠ ‖B‖` are vacuous.  So the paper's Λ₀
statement follows from the degree clause alone.

`hILR` below is that degree clause, stated as a hypothesis exactly as the paper states ILR as an
external input ("We use one external spectral theorem").  **It is not proved here**: ILR is
Israel J. Math. 83 (1993) 73–95, and neither it nor the §4 phase-cocycle/winding-degree machinery
that derives the clause from it has been formalised. -/

/-- **No `Λ₀`-dependence, from the ILR degree clause** — the paper's Theorem 1 at `a = √2`,
`j = 0`, with no non-degeneracy assumptions. -/
theorem no_lambdaZero_dependence_of_ILR {g : ℝ → ℂ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hILR : ∀ w : ℂ, ‖w‖ = 1 → ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → HRTResonant.rootCount ζ₁ ζ₂ = 1)
    (hdepFun : A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
      + D • HRTResonant.modulate (Real.sqrt 2)
          (HRTResonant.timeShift (Real.sqrt 2) g) = 0) :
    False := by
  have hae : (↑↑(hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hf : hg2.toLp g ≠ 0 := by
    intro h
    refine hgne (hae.symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hsum : (1 : ℝ) + (Real.sqrt 2 - 1) = Real.sqrt 2 := by ring
  have hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * (((1 : ℝ) + (Real.sqrt 2 - 1) : ℝ) : ℂ) * (y : ℂ))
          * g (y - ((1 : ℝ) + (Real.sqrt 2 - 1)))) = 0 := by
    intro y
    have h := congrFun hdepFun y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      HRTResonant.timeShift, HRTResonant.modulate, Complex.ofReal_one, mul_one] at h
    rw [hsum]
    exact h
  obtain ⟨L, hinf, hunit, hmean⟩ :=
    exists_infinite_mean_succ A B C D (Real.sqrt 2 - 1) sqrtTwo_sub_one_nonneg
      sqrtTwo_sub_one_lt_one irrational_sqrtTwo_sub_one hA hB hC hD (hg2.toLp g) hf hae hdep
  have hmean' : ∀ w ∈ L, Real.circleAverage
      (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖ := by
    intro w hw
    rw [← HRTResonant.quadratic_fibre_mean_eq_circleAverage]
    exact hmean w hw
  obtain ⟨w₁, w₂, w₃, w₄, hsub⟩ :=
    HRTResonant.live_set_subset_four A B C D hA hB hC hD 0
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
      L hunit hmean'
      (fun w hw ζ₁ ζ₂ hfac h1 h2 => by
        simpa using hILR w (hunit w hw) ζ₁ ζ₂ hfac h1 h2)
  exact hinf (Set.Finite.subset (Set.toFinite ({w₁, w₂, w₃, w₄} : Set ℂ)) hsub)

/-- **THE PAPER'S THEOREM 1 AT `a = √2`, `j = 0`.**  Heil–Speegle Conjecture 2 for every nonzero
measurable `L²` window, from the ILR degree clause alone — no non-degeneracy conditions, no
compact support, and no `hthree` (Λ₀'s three-point subsets are handled by
`HRTHthree.hthree_lambdaZero`).

The only hypothesis is `hILR`, which the source paper likewise takes as an external input. -/
theorem heil_speegle_lambda_zero_L2_of_ILR (g : ℝ → ℂ) (hgm : Measurable g)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (hILR : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        ∀ w : ℂ, ‖w‖ = 1 → ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → HRTResonant.rootCount ζ₁ ζ₂ = 1) :
    LinearIndependent ℂ (HRTResonant.lambdaZeroFamily g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  first
    | push_neg at hne
    | push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  have hall : ∀ i, c i ≠ 0 := fun i hi =>
    hi₀ (HRTHthree.hthree_lambdaZero hgm hg2 hgne c hc ⟨i, hi⟩ i₀)
  have hdep : c 0 • g + c 1 • HRTResonant.timeShift 1 g + c 2 • HRTResonant.modulate 1 g
      + c 3 • HRTResonant.modulate (Real.sqrt 2)
          (HRTResonant.timeShift (Real.sqrt 2) g) = 0 := by
    simpa [Fin.sum_univ_four, HRTResonant.lambdaZeroFamily] using hc
  exact no_lambdaZero_dependence_of_ILR hg2 hgne (c 0) (c 1) (c 2) (c 3)
    (hall 0) (hall 1) (hall 2) (hall 3)
    (hILR (c 0) (c 1) (c 2) (c 3) (hall 0) (hall 1) (hall 2) (hall 3)) hdep

/-! ## Towards the paper's general `j`

The paper's fourth point is `(a, a+j)` with `j ∈ ℤ`, i.e. the translate `M_{a+j}T_a g`.  That
factors as `M_j ∘ (M_a T_a)`, and the INTEGRALITY of `j` is exactly what makes it work: the Zak
transform is `1`-periodic in `ω`, so shifting `ω` by `a+j` is the same as shifting by `a` and the
fibration by `θ = ω − t` survives.  On the torus that shows up as `M_j` acting by multiplication
alone — by the character `fourier j` of the second coordinate — with no shift at all.

Since that multiplier is unimodular, **the modulus cocycle is independent of `j`**, which is why
the whole Jensen side of the paper never mentions `j`; only the phase (§4) does. -/

theorem multLC_congr {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ ψ : α → ℂ}
    {hφm : Measurable φ} {hφ : ∀ x, ‖φ x‖ = 1}
    {hψm : Measurable ψ} {hψ : ∀ x, ‖ψ x‖ = 1}
    (h : ∀ x, φ x = ψ x) (F : Lp ℂ 2 μ) :
    HRTShift.multLC hφm hφ F = HRTShift.multLC hψm hψ F := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_multLC hφm hφ F, coeFn_multLC hψm hψ F] with x h1 h2
  rw [h1, h2, h x]

theorem multLC_one {α : Type*} [MeasurableSpace α] {μ : Measure α} (F : Lp ℂ 2 μ) :
    HRTShift.multLC (μ := μ) (φ := fun _ : α => (1 : ℂ)) measurable_const
      (fun _ => by simp) F = F := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_multLC (μ := μ) (φ := fun _ : α => (1 : ℂ)) measurable_const
    (fun _ => by simp) F] with x h
  rw [h, one_mul]

theorem multLC_multLC {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ ψ : α → ℂ}
    (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1)
    (hψm : Measurable ψ) (hψ : ∀ x, ‖ψ x‖ = 1) (F : Lp ℂ 2 μ) :
    HRTShift.multLC hφm hφ (HRTShift.multLC hψm hψ F)
      = HRTShift.multLC (μ := μ) (φ := fun x => φ x * ψ x) (hφm.mul hψm)
          (fun x => by rw [norm_mul, hφ, hψ, one_mul]) F := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_multLC hφm hφ (HRTShift.multLC hψm hψ F),
    coeFn_multLC hψm hψ F,
    coeFn_multLC (μ := μ) (φ := fun x => φ x * ψ x) (hφm.mul hψm)
      (fun x => by rw [norm_mul, hφ, hψ, one_mul]) F] with x h1 h2 h3
  rw [h1, h2, h3]
  ring

theorem modCLM_add (x y : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modCLM (x + y) f = modCLM x (modCLM y f) := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_modCLM (x + y) f, coeFn_modCLM x (modCLM y f), coeFn_modCLM y f]
    with t h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem modCLM_zero (f : Lp ℂ 2 (volume : Measure ℝ)) : modCLM 0 f = f := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_modCLM 0 f] with t h
  rw [h]
  simp

/-- The integer modulation's torus multiplier: the `j`-th character of the second coordinate.
`chiMint 1 = chiM1` by `chiM1_eq`. -/
noncomputable def chiMint (j : ℤ) (x : UnitAddTorus (Fin 2)) : ℂ := fourier j (x 1)

theorem norm_chiMint (j : ℤ) (x : UnitAddTorus (Fin 2)) : ‖chiMint j x‖ = 1 := by
  unfold chiMint
  rw [fourier_apply]
  exact Circle.norm_coe _

theorem measurable_chiMint (j : ℤ) : Measurable (chiMint j) := by
  unfold chiMint
  exact (map_continuous (fourier j)).measurable.comp
    (measurable_pi_apply 1 (X := fun _ : Fin 2 => UnitAddCircle))

theorem chiMint_zero (x : UnitAddTorus (Fin 2)) : chiMint 0 x = 1 := by
  unfold chiMint
  simp

theorem chiMint_succ (j : ℤ) (x : UnitAddTorus (Fin 2)) :
    chiMint (j + 1) x = chiMint j x * chiMint 1 x := by
  unfold chiMint
  rw [fourier_add]

theorem chiMint_pred (j : ℤ) (x : UnitAddTorus (Fin 2)) :
    chiMint (j - 1) x = chiMint j x * chiMint (-1) x := by
  unfold chiMint
  rw [show j - 1 = j + (-1) by ring, fourier_add]

theorem multLC_inv_cancel {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ ψ : α → ℂ}
    (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1)
    (hψm : Measurable ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hmul : ∀ x, φ x * ψ x = 1) (F : Lp ℂ 2 μ) :
    HRTShift.multLC hφm hφ (HRTShift.multLC hψm hψ F) = F := by
  rw [multLC_multLC]
  exact (multLC_congr hmul F).trans (multLC_one F)

theorem mod1CLM_eq_modCLM_one (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mod1CLM f = modCLM 1 f := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_mod1CLM f, coeFn_modCLM 1 f] with t h1 h2
  rw [h1, h2]
  congr 2
  push_cast
  ring

theorem chiM1_eq_chiMint (x : UnitAddTorus (Fin 2)) : chiM1 x = chiMint 1 x := chiM1_eq x

theorem chiMint_negOne_mul (x : UnitAddTorus (Fin 2)) : chiMint (-1) x * chiM1 x = 1 := by
  rw [chiM1_eq_chiMint]
  unfold chiMint
  rw [← fourier_add]
  simp

/-- The Zak formula for the modulation by `−1`, from the fact that it inverts `M₁`. -/
theorem zakL2_modNegOne (f : Lp ℂ 2 (volume : Measure ℝ)) :
    zakCLM (modCLM (-1 : ℝ) f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (measurable_chiMint (-1)) (norm_chiMint (-1)) (zakCLM f) := by
  have hcancel : modCLM 1 (modCLM (-1 : ℝ) f) = f := by
    rw [← modCLM_add, show (1 : ℝ) + (-1) = 0 by norm_num, modCLM_zero]
  have hstep : zakCLM f
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiM1 norm_chiM1 (zakCLM (modCLM (-1 : ℝ) f)) := by
    conv_lhs => rw [← hcancel, ← mod1CLM_eq_modCLM_one]
    exact congrFun zakL2_modOne_of_memLp (modCLM (-1 : ℝ) f)
  rw [hstep]
  exact (multLC_inv_cancel (measurable_chiMint (-1)) (norm_chiMint (-1))
    measurable_chiM1 norm_chiM1 chiMint_negOne_mul (zakCLM (modCLM (-1 : ℝ) f))).symm

/-- **The integer modulation acts on the torus by the `j`-th character alone.**  No shift: the Zak
transform's `1`-periodicity in `ω` absorbs the integer part, which is exactly why the paper needs
`j ∈ ℤ`. -/
theorem zakL2_modInt (j : ℤ) :
    ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      zakCLM (modCLM ((j : ℝ)) f)
        = HRTShift.multLC
            (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
            (measurable_chiMint j) (norm_chiMint j) (zakCLM f) := by
  induction j using Int.induction_on with
  | zero =>
      intro f
      rw [Int.cast_zero, modCLM_zero]
      exact ((multLC_congr chiMint_zero (zakCLM f)).trans (multLC_one (zakCLM f))).symm
  | succ n ih =>
      intro f
      have hcast : (((n : ℤ) + 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) + 1 := by push_cast; ring
      rw [hcast, modCLM_add, ih (modCLM 1 f), ← mod1CLM_eq_modCLM_one,
        congrFun zakL2_modOne_of_memLp f, multLC_multLC]
      exact multLC_congr (fun x => by rw [chiMint_succ, chiM1_eq_chiMint]) (zakCLM f)
  | pred n ih =>
      intro f
      have hcast : ((-(n : ℤ) - 1 : ℤ) : ℝ) = ((-(n : ℤ) : ℤ) : ℝ) + (-1) := by push_cast; ring
      rw [hcast, modCLM_add, ih (modCLM (-1 : ℝ) f), zakL2_modNegOne, multLC_multLC]
      exact multLC_congr (fun x => (chiMint_pred (-(n : ℤ)) x).symm) (zakCLM f)

/-! ### The dependence and cocycle for the paper's general `j`

`M_{a+j}T_a = M_j ∘ (M_a T_a)`, so the `D` term picks up one further multiplier `chiMint j`.
It is unimodular, so `cocycle_norm_j_succ` has EXACTLY the conclusion of `cocycle_norm` — the
modulus cocycle does not see `j` at all. -/

theorem dep_Lp_j {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (j : ℤ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    A • f + B • (transL 1 f) + C • (mod1CLM f)
      + D • (modCLM ((j : ℝ)) (modTransCLM a f)) = 0 := by
  refine Lp.ext_iff.mpr ?_
  have h1 : (↑↑(transL 1 f) : ℝ → ℂ) =ᵐ[volume] fun y : ℝ => g (y - 1) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) 1)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) 1).quasiMeasurePreserving.ae_eq_comp hae
  have h2 : (↑↑(mod1CLM f) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y := by
    refine (coeFn_mod1CLM f).trans ?_
    filter_upwards [hae] with y hy
    rw [hy]
  have h3T : (↑↑(transL a f) : ℝ → ℂ) =ᵐ[volume] fun y : ℝ => g (y - a) := by
    refine (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_sub_right (volume : Measure ℝ) a)).trans ?_
    exact (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp hae
  have h3M : (↑↑(modTransCLM a f) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (y : ℂ)) * g (y - a) := by
    refine (coeFn_modCLM a (transL a f)).trans ?_
    filter_upwards [h3T] with y hy
    rw [hy]
  have h3 : (↑↑(modCLM ((j : ℝ)) (modTransCLM a f)) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
          * g (y - a) := by
    refine (coeFn_modCLM ((j : ℝ)) (modTransCLM a f)).trans ?_
    filter_upwards [h3M] with y hy
    rw [hy, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  filter_upwards [Lp.coeFn_add (A • f + B • (transL 1 f) + C • (mod1CLM f))
      (D • (modCLM ((j : ℝ)) (modTransCLM a f))),
    Lp.coeFn_add (A • f + B • (transL 1 f)) (C • (mod1CLM f)),
    Lp.coeFn_add (A • f) (B • (transL 1 f)),
    Lp.coeFn_smul A f, Lp.coeFn_smul B (transL 1 f), Lp.coeFn_smul C (mod1CLM f),
    Lp.coeFn_smul D (modCLM ((j : ℝ)) (modTransCLM a f)),
    hae, h1, h2, h3, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))]
    with y e1 e2 e3 s1 s2 s3 s4 ha hb hc hd hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 e3 s1 s2 s3 s4 hz
  rw [e1, e2, e3, s1, s2, s3, s4, ha, hb, hc, hd, hz]
  linear_combination hdep y

/-- **THE COCYCLE FOR THE PAPER'S GENERAL `j`.**  Same conclusion as `cocycle_norm`: the `j`
multiplier is unimodular, so the modulus cocycle is `j`-independent. -/
theorem cocycle_norm_j_succ {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (j : ℤ)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
                * (((1 : ℝ) + a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - ((1 : ℝ) + a))) = 0) :
    CocycleNorm A B C D a f := by
  set μT := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) with hμT
  set Z := zakCLM f with hZ
  set T1 := HRTShift.multLC (μ := μT) measurable_chiT1 norm_chiT1 Z with hT1
  set M1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 Z with hM1
  set S0 := HRTShift.multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a) (antidiagL a T1)
    with hS0
  set S1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 S0 with hS1
  set S := HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j) S1 with hS
  have hdep' : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * ((((1 : ℝ) + a) + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
          * g (y - ((1 : ℝ) + a))) = 0 := by
    intro y
    have h := hdep y
    have hre : (((1 : ℝ) + a + (j : ℝ) : ℝ) : ℂ) = ((((1 : ℝ) + a) + (j : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [← hre]
    exact h
  have h0 : A • Z + B • T1 + C • M1 + D • S = 0 := by
    have hLp := dep_Lp_j A B C D ((1 : ℝ) + a) j f hae hdep'
    rw [modTransCLM_succ a f] at hLp
    have h1 : zakCLM (A • f + B • (transL 1 f) + C • (mod1CLM f)
        + D • (modCLM ((j : ℝ)) (mod1CLM (modTransCLM a (transL 1 f))))) = 0 := by
      rw [hLp, map_zero]
    simp only [map_add, map_smul] at h1
    have e1 : zakCLM (transL 1 f) = T1 := congrFun zakL2_transOne_of_memLp f
    have e2 : zakCLM (mod1CLM f) = M1 := congrFun zakL2_modOne_of_memLp f
    have e3 : zakCLM (modCLM ((j : ℝ)) (mod1CLM (modTransCLM a (transL 1 f))))
        = HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
            (zakCLM (mod1CLM (modTransCLM a (transL 1 f)))) :=
      zakL2_modInt j (mod1CLM (modTransCLM a (transL 1 f)))
    have e4 : zakCLM (mod1CLM (modTransCLM a (transL 1 f)))
        = HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1
            (zakCLM (modTransCLM a (transL 1 f))) :=
      congrFun zakL2_modOne_of_memLp (modTransCLM a (transL 1 f))
    have e5 : zakCLM (modTransCLM a (transL 1 f))
        = HRTShift.multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a)
            (antidiagL a (zakCLM (transL 1 f))) :=
      congrFun (zakL2_modShift_of_memLp a ha0 ha1) (transL 1 f)
    rw [e3, e4, e5, e1, e2] at h1
    exact h1
  have hT1shift := (measurePreserving_antidiagT a).quasiMeasurePreserving.ae_eq_comp
    (coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z)
  have hcoe : (↑↑(A • Z + B • T1 + C • M1 + D • S) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[μT] 0 := by
    rw [h0]; exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μT)
  have hpt : ∀ᵐ x ∂μT, symbolTor A B C x * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) x
      = -(D * (chiMint j x * (chiM1 x * (psiRot a x
          * (chiT1 (antidiagT a x) * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) (antidiagT a x)))))) := by
    filter_upwards [hcoe,
      Lp.coeFn_add (A • Z + B • T1 + C • M1) (D • S),
      Lp.coeFn_add (A • Z + B • T1) (C • M1),
      Lp.coeFn_add (A • Z) (B • T1),
      Lp.coeFn_smul A Z, Lp.coeFn_smul B T1, Lp.coeFn_smul C M1, Lp.coeFn_smul D S,
      coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z,
      coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 Z,
      coeFn_multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j) S1,
      coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 S0,
      coeFn_multLC (μ := μT) (measurable_psiRot a) (norm_psiRot a) (antidiagL a T1),
      coeFn_antidiagL a T1, hT1shift]
      with x hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mS1 mS0 mA mT
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Function.comp_apply] at hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mS1 mS0 mA mT
    rw [e1, e2, e3, s1, s2, s3, s4, m1, m2, mS, mS1, mS0, mA, mT] at hz
    unfold symbolTor
    linear_combination hz
  filter_upwards [hpt] with x hx
  have h := congrArg norm hx
  simp only [norm_mul, norm_neg, norm_chiMint, norm_chiM1, norm_psiRot, norm_chiT1,
    one_mul] at h
  exact h

/-! ## The paper's resonant family at `a = √2`, for every `j`

`live_set_subset_four` already carries exactly the paper's `j ≠ ±1` exclusions, as the clauses
`hj1 : j = 1 → ‖D‖ ≠ ‖C‖` and `hjm1 : j = -1 → ‖D‖ ≠ ‖B‖` — vacuous for every other `j`.  So the
whole family follows from the ILR degree clause `rootCount = 1 + j`. -/

/-- The paper's four-point family `g, T₁g, M₁g, M_{a+j}T_a g`. -/
noncomputable def resonantFamily (g : ℝ → ℂ) (a : ℝ) (j : ℤ) : Fin 4 → (ℝ → ℂ) :=
  ![g, HRTResonant.timeShift 1 g, HRTResonant.modulate 1 g,
    HRTResonant.modulate (a + (j : ℝ)) (HRTResonant.timeShift a g)]

theorem resonantFamily_lambdaZero (g : ℝ → ℂ) :
    resonantFamily g (Real.sqrt 2) 0 = HRTResonant.lambdaZeroFamily g := by
  unfold resonantFamily HRTResonant.lambdaZeroFamily
  norm_num

/-- **No dependence in the resonant family at `a = √2`, for any `j`, from the ILR degree
clause.**  The paper's Theorem 1 at `a = √2`, all `j ∈ ℤ∖{−1,1}` (and `j = ±1` too, given the
corresponding non-degeneracy). -/
theorem no_resonant_dependence_sqrt2_of_ILR {g : ℝ → ℂ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (j : ℤ) (hj1 : j = 1 → ‖D‖ ≠ ‖C‖) (hjm1 : j = -1 → ‖D‖ ≠ ‖B‖)
    (hILR : ∀ w : ℂ, ‖w‖ = 1 → ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → HRTResonant.rootCount ζ₁ ζ₂ = 1 + j)
    (hdepFun : A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
      + D • HRTResonant.modulate (Real.sqrt 2 + (j : ℝ))
          (HRTResonant.timeShift (Real.sqrt 2) g) = 0) :
    False := by
  have hae : (↑↑(hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hf : hg2.toLp g ≠ 0 := by
    intro h
    refine hgne (hae.symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hsum : (1 : ℝ) + (Real.sqrt 2 - 1) = Real.sqrt 2 := by ring
  have hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * (((1 : ℝ) + (Real.sqrt 2 - 1) + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
          * g (y - ((1 : ℝ) + (Real.sqrt 2 - 1)))) = 0 := by
    intro y
    have h := congrFun hdepFun y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      HRTResonant.timeShift, HRTResonant.modulate, Complex.ofReal_one, mul_one] at h
    rw [hsum]
    exact h
  have hcn := cocycle_norm_j_succ A B C D (Real.sqrt 2 - 1) j sqrtTwo_sub_one_nonneg
    sqrtTwo_sub_one_lt_one (hg2.toLp g) hae hdep
  obtain ⟨L, hinf, hunit, hmean⟩ :=
    exists_infinite_mean_of irrational_sqrtTwo_sub_one hA hB hC hD hf hcn
  have hmean' : ∀ w ∈ L, Real.circleAverage
      (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖ := by
    intro w hw
    rw [← HRTResonant.quadratic_fibre_mean_eq_circleAverage]
    exact hmean w hw
  obtain ⟨w₁, w₂, w₃, w₄, hsub⟩ :=
    HRTResonant.live_set_subset_four A B C D hA hB hC hD j hj1 hjm1 L hunit hmean'
      (fun w hw ζ₁ ζ₂ hfac h1 h2 => hILR w (hunit w hw) ζ₁ ζ₂ hfac h1 h2)
  exact hinf (Set.Finite.subset (Set.toFinite ({w₁, w₂, w₃, w₄} : Set ℂ)) hsub)

/-! ## General irrational `a` — stripping the integer part

The paper allows any irrational `a`; the chain so far handles `a ∈ [0,1)` and `a = 1 + α`.  Write
`a = n + α` with `n : ℕ` and `α = a − n ∈ [0,1)`.  Iterating `modTransCLM_succ` peels one unit at
a time, each pass contributing only `chiM1` and a shifted `chiT1` — both unimodular — while the
POINT moves by `antidiag α` throughout, because `antidiagT` is a map of the torus and does not see
the integer part.

So the whole integer part is invisible to the modulus cocycle, exactly as `j` was. -/

theorem antidiagL_multLC (a : ℝ) {φ : UnitAddTorus (Fin 2) → ℂ}
    (hφm : Measurable φ) (hφ : ∀ x, ‖φ x‖ = 1)
    (F : Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))) :
    antidiagL a (HRTShift.multLC hφm hφ F)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          (φ := fun x => φ (antidiagT a x))
          (hφm.comp (measurePreserving_antidiagT a).measurable)
          (fun x => hφ (antidiagT a x)) (antidiagL a F) := by
  refine Lp.ext_iff.mpr ?_
  have hL := coeFn_antidiagL a (HRTShift.multLC hφm hφ F)
  have hmul := (measurePreserving_antidiagT a).quasiMeasurePreserving.ae_eq_comp
    (coeFn_multLC hφm hφ F)
  have hR := coeFn_multLC
    (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (φ := fun x => φ (antidiagT a x))
    (hφm.comp (measurePreserving_antidiagT a).measurable)
    (fun x => hφ (antidiagT a x)) (antidiagL a F)
  have hF := coeFn_antidiagL a F
  filter_upwards [hL, hmul, hR, hF] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **The Zak image of `M_{n+α}T_{n+α}` is a unimodular multiple of `Z ∘ antidiag α`.**  The
integer part contributes only unimodular factors and does not move the point. -/
theorem exists_zak_modTrans_nat (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (n : ℕ) :
    ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ∃ (χ : UnitAddTorus (Fin 2) → ℂ) (hm : Measurable χ) (hu : ∀ x, ‖χ x‖ = 1),
        zakCLM (modTransCLM ((n : ℝ) + α) f)
          = HRTShift.multLC
              (μ := Measure.pi
                (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
              hm hu (antidiagL α (zakCLM f)) := by
  induction n with
  | zero =>
      intro f
      refine ⟨psiRot α, measurable_psiRot α, norm_psiRot α, ?_⟩
      rw [show ((0 : ℕ) : ℝ) + α = α by norm_num]
      exact congrFun (zakL2_modShift_of_memLp α hα0 hα1) f
  | succ n ih =>
      intro f
      obtain ⟨χ, hm, hu, hχ⟩ := ih (transL 1 f)
      refine ⟨fun x => chiM1 x * χ x * chiT1 (antidiagT α x),
        (measurable_chiM1.mul hm).mul
          (measurable_chiT1.comp (measurePreserving_antidiagT α).measurable),
        fun x => by rw [norm_mul, norm_mul, norm_chiM1, hu, norm_chiT1]; norm_num, ?_⟩
      have hcast : (((n + 1 : ℕ) : ℝ) + α) = 1 + (((n : ℕ) : ℝ) + α) := by push_cast; ring
      rw [hcast, modTransCLM_succ,
        congrFun zakL2_modOne_of_memLp (modTransCLM (((n : ℕ) : ℝ) + α) (transL 1 f)),
        hχ, congrFun zakL2_transOne_of_memLp f, antidiagL_multLC, multLC_multLC,
        multLC_multLC]

/-- **THE COCYCLE, FOR EVERY SHIFT AND EVERY `j`.**  The paper's full generality on the modulus
side: shift `n + α` with `n : ℕ` and `α ∈ [0,1)`, modulation `(n+α) + j` with `j : ℤ`. -/
theorem cocycle_norm_gen {g : ℝ → ℂ} (A B C D : ℂ) (α : ℝ) (n : ℕ) (j : ℤ)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
                * ((((n : ℝ) + α) + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - ((n : ℝ) + α))) = 0) :
    CocycleNorm A B C D α f := by
  set μT := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) with hμT
  set Z := zakCLM f with hZ
  set T1 := HRTShift.multLC (μ := μT) measurable_chiT1 norm_chiT1 Z with hT1
  set M1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 Z with hM1
  obtain ⟨χ, hm, hu, hχ⟩ := exists_zak_modTrans_nat α hα0 hα1 n f
  set S := HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
    (HRTShift.multLC (μ := μT) hm hu (antidiagL α Z)) with hS
  have h0 : A • Z + B • T1 + C • M1 + D • S = 0 := by
    have hLp := dep_Lp_j A B C D ((n : ℝ) + α) j f hae hdep
    have h1 : zakCLM (A • f + B • (transL 1 f) + C • (mod1CLM f)
        + D • (modCLM ((j : ℝ)) (modTransCLM ((n : ℝ) + α) f))) = 0 := by
      rw [hLp, map_zero]
    simp only [map_add, map_smul] at h1
    have e1 : zakCLM (transL 1 f) = T1 := congrFun zakL2_transOne_of_memLp f
    have e2 : zakCLM (mod1CLM f) = M1 := congrFun zakL2_modOne_of_memLp f
    have e3 : zakCLM (modCLM ((j : ℝ)) (modTransCLM ((n : ℝ) + α) f))
        = HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
            (zakCLM (modTransCLM ((n : ℝ) + α) f)) :=
      zakL2_modInt j (modTransCLM ((n : ℝ) + α) f)
    rw [e3, hχ, e1, e2] at h1
    exact h1
  have hcoe : (↑↑(A • Z + B • T1 + C • M1 + D • S) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[μT] 0 := by
    rw [h0]; exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μT)
  have hpt : ∀ᵐ x ∂μT, symbolTor A B C x * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) x
      = -(D * (chiMint j x * (χ x
          * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) (antidiagT α x)))) := by
    filter_upwards [hcoe,
      Lp.coeFn_add (A • Z + B • T1 + C • M1) (D • S),
      Lp.coeFn_add (A • Z + B • T1) (C • M1),
      Lp.coeFn_add (A • Z) (B • T1),
      Lp.coeFn_smul A Z, Lp.coeFn_smul B T1, Lp.coeFn_smul C M1, Lp.coeFn_smul D S,
      coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z,
      coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 Z,
      coeFn_multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
        (HRTShift.multLC (μ := μT) hm hu (antidiagL α Z)),
      coeFn_multLC (μ := μT) hm hu (antidiagL α Z),
      coeFn_antidiagL α Z]
      with x hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mX mA
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Function.comp_apply] at hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mX mA
    rw [e1, e2, e3, s1, s2, s3, s4, m1, m2, mS, mX, mA] at hz
    unfold symbolTor
    linear_combination hz
  filter_upwards [hpt] with x hx
  have h := congrArg norm hx
  simp only [norm_mul, norm_neg, norm_chiMint, hu, one_mul] at h
  exact h

/-! ## GAP 2 CLOSED — the paper's Theorem 1 for every positive irrational `a`

`a = ⌊a⌋ + fract a` with `fract a ∈ [0,1)`, and `fract a` is irrational whenever `a` is, so the
rotation on the fibre circle is still ergodic. -/

theorem irrational_fract {a : ℝ} (ha : Irrational a) : Irrational (Int.fract a) := by
  unfold Int.fract
  exact ha.sub_intCast ⌊a⌋

theorem natFloor_add_fract {a : ℝ} (ha : 0 ≤ a) :
    ((⌊a⌋.toNat : ℕ) : ℝ) + Int.fract a = a := by
  have hfl : (0 : ℤ) ≤ ⌊a⌋ := Int.floor_nonneg.mpr ha
  have hcast : ((⌊a⌋.toNat : ℕ) : ℝ) = ((⌊a⌋ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hfl)
  rw [hcast]
  exact Int.floor_add_fract a

/-- **The cocycle for an arbitrary nonnegative shift.** -/
theorem cocycle_norm_of_nonneg {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (ha : 0 ≤ a) (j : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    CocycleNorm A B C D (Int.fract a) f := by
  refine cocycle_norm_gen A B C D (Int.fract a) ⌊a⌋.toNat j (Int.fract_nonneg a)
    (Int.fract_lt_one a) f hae ?_
  intro y
  rw [natFloor_add_fract ha]
  exact hdep y

/-- **THE PAPER'S THEOREM 1 — no dependence, for every positive irrational `a` and every `j`.**

Given the ILR degree clause, for every nonzero `L²` window there is no dependence

    `A g + B T₁g + C M₁g + D M_{a+j}T_a g = 0`

with all four coefficients nonzero.  `hj1`/`hjm1` are the paper's `j ≠ ±1` exclusions, vacuous
for every other `j`. -/
theorem no_resonant_dependence_of_ILR {g : ℝ → ℂ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (a : ℝ) (ha : 0 ≤ a) (hairr : Irrational a)
    (j : ℤ) (hj1 : j = 1 → ‖D‖ ≠ ‖C‖) (hjm1 : j = -1 → ‖D‖ ≠ ‖B‖)
    (hILR : ∀ w : ℂ, ‖w‖ = 1 → ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → HRTResonant.rootCount ζ₁ ζ₂ = 1 + j)
    (hdepFun : A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
      + D • HRTResonant.modulate (a + (j : ℝ)) (HRTResonant.timeShift a g) = 0) :
    False := by
  have hae : (↑↑(hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hf : hg2.toLp g ≠ 0 := by
    intro h
    refine hgne (hae.symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
          * g (y - a)) = 0 := by
    intro y
    have h := congrFun hdepFun y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      HRTResonant.timeShift, HRTResonant.modulate, Complex.ofReal_one, mul_one] at h
    exact h
  have hcn := cocycle_norm_of_nonneg A B C D a ha j (hg2.toLp g) hae hdep
  obtain ⟨L, hinf, hunit, hmean⟩ :=
    exists_infinite_mean_of (irrational_fract hairr) hA hB hC hD hf hcn
  have hmean' : ∀ w ∈ L, Real.circleAverage
      (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖ := by
    intro w hw
    rw [← HRTResonant.quadratic_fibre_mean_eq_circleAverage]
    exact hmean w hw
  obtain ⟨w₁, w₂, w₃, w₄, hsub⟩ :=
    HRTResonant.live_set_subset_four A B C D hA hB hC hD j hj1 hjm1 L hunit hmean'
      (fun w hw ζ₁ ζ₂ hfac h1 h2 => hILR w (hunit w hw) ζ₁ ζ₂ hfac h1 h2)
  exact hinf (Set.Finite.subset (Set.toFinite ({w₁, w₂, w₃, w₄} : Set ℂ)) hsub)

/-! ## §4 — the phase cocycle

The paper's §4 introduces `m_θ(t) = e^{2πiθt}e^{πit(t−1)}` purely to convert the QUASI-periodic
`G_θ` on `ℝ` into a genuinely `1`-periodic `V_θ`.  **That device is unnecessary here**: the shear
`toTor` was applied before slicing, so `zakCLM f` is an honest function on the torus and every
fibre is periodic by construction.  So §4 starts directly at the phase.

What is retained is `W = Z/|Z|` and the phase cocycle `W(shift x) = ξ(x)·W(x)`, with

    ξ = −phase(symbol) · (‖D‖/D) · conj Θ

where `Θ` collects every unimodular factor the shift picked up (`chiMint j`, and one `chiM1`
plus one shifted `chiT1` per unit of `⌊a⌋`).  This is the paper's
`ξ_θ = (Λ_θ/|Λ_θ|)·e^{−2πijt}·P_θ/|P_θ|`.

**The degree formula `deg ξ_θ = −j−1+N(θ)` is NOT formalised, and cannot be with current
Mathlib**: there is no winding number, no argument principle, no degree of a circle map, and no
`π₁(S¹) ≅ ℤ`.  `Circle.isCoveringMap_exp` and `Topology.Homotopy.Lifting` exist, so a degree
could be *built* — lift along the covering, then show `deg` is additive — but that is
foundational work, not an application. -/

/-- The complex cocycle, with every unimodular factor collected into `Θ`.  This is the input
§4 takes phases of; `cocycle_norm_gen` is its modulus shadow. -/
theorem exists_cocycle_eq_gen {g : ℝ → ℂ} (A B C D : ℂ) (α : ℝ) (n : ℕ) (j : ℤ)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
                * ((((n : ℝ) + α) + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - ((n : ℝ) + α))) = 0) :
    ∃ Θ : UnitAddTorus (Fin 2) → ℂ, (∀ x, ‖Θ x‖ = 1) ∧
      ∀ᵐ x ∂(Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))),
        symbolTor A B C x * (↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) x
          = -(D * (Θ x * (↑↑(zakCLM f) : UnitAddTorus (Fin 2) → ℂ) (antidiagT α x))) := by
  set μT := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) with hμT
  set Z := zakCLM f with hZ
  set T1 := HRTShift.multLC (μ := μT) measurable_chiT1 norm_chiT1 Z with hT1
  set M1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 Z with hM1
  obtain ⟨χ, hm, hu, hχ⟩ := exists_zak_modTrans_nat α hα0 hα1 n f
  set S := HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
    (HRTShift.multLC (μ := μT) hm hu (antidiagL α Z)) with hS
  refine ⟨fun x => chiMint j x * χ x, fun x => by rw [norm_mul, norm_chiMint, hu, one_mul], ?_⟩
  have h0 : A • Z + B • T1 + C • M1 + D • S = 0 := by
    have hLp := dep_Lp_j A B C D ((n : ℝ) + α) j f hae hdep
    have h1 : zakCLM (A • f + B • (transL 1 f) + C • (mod1CLM f)
        + D • (modCLM ((j : ℝ)) (modTransCLM ((n : ℝ) + α) f))) = 0 := by
      rw [hLp, map_zero]
    simp only [map_add, map_smul] at h1
    have e1 : zakCLM (transL 1 f) = T1 := congrFun zakL2_transOne_of_memLp f
    have e2 : zakCLM (mod1CLM f) = M1 := congrFun zakL2_modOne_of_memLp f
    have e3 : zakCLM (modCLM ((j : ℝ)) (modTransCLM ((n : ℝ) + α) f))
        = HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
            (zakCLM (modTransCLM ((n : ℝ) + α) f)) :=
      zakL2_modInt j (modTransCLM ((n : ℝ) + α) f)
    rw [e3, hχ, e1, e2] at h1
    exact h1
  have hcoe : (↑↑(A • Z + B • T1 + C • M1 + D • S) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[μT] 0 := by
    rw [h0]; exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μT)
  filter_upwards [hcoe,
    Lp.coeFn_add (A • Z + B • T1 + C • M1) (D • S),
    Lp.coeFn_add (A • Z + B • T1) (C • M1),
    Lp.coeFn_add (A • Z) (B • T1),
    Lp.coeFn_smul A Z, Lp.coeFn_smul B T1, Lp.coeFn_smul C M1, Lp.coeFn_smul D S,
    coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z,
    coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 Z,
    coeFn_multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
      (HRTShift.multLC (μ := μT) hm hu (antidiagL α Z)),
    coeFn_multLC (μ := μT) hm hu (antidiagL α Z),
    coeFn_antidiagL α Z]
    with x hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mX mA
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Function.comp_apply] at hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mX mA
  rw [e1, e2, e3, s1, s2, s3, s4, m1, m2, mS, mX, mA] at hz
  unfold symbolTor
  linear_combination hz

/-- The phase of a nonzero complex number. -/
noncomputable def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  have h : ‖((‖z‖ : ℝ) : ℂ)‖ = ‖z‖ := by
    simp [abs_of_nonneg (norm_nonneg z)]
  unfold phase
  rw [norm_div, h]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- The unimodular factor of the paper's `ξ_θ`, in the division-free form the cocycle gives it. -/
theorem cocycle_shift_eq {Θ Zf S : UnitAddTorus (Fin 2) → ℂ} {D : ℂ}
    {ad : UnitAddTorus (Fin 2) → UnitAddTorus (Fin 2)} {x : UnitAddTorus (Fin 2)}
    (heq : S x * Zf x = -(D * (Θ x * Zf (ad x)))) :
    D * Θ x * Zf (ad x) = -(S x * Zf x) := by
  linear_combination heq

/-! ## §4's degree — building the winding number from EXPLICIT lifts

Mathlib has no winding number, no argument principle and no `π₁(S¹) ≅ ℤ`.  But the paper needs
the degree of only ONE family of loops — `t ↦ phase (e(t) − ζ)` — and for that a lift can be
written down by hand, with no covering-space theory:

* `‖ζ‖ > 1`:  `e(t) − ζ = −ζ · (1 − e(t)/ζ)`, and `‖e(t)/ζ‖ = 1/‖ζ‖ < 1`, so the second factor
  has `Re > 0` and never leaves the slit plane.  `arg` of it is continuous and `1`-periodic, so
  `L(t) = (arg(−ζ) + arg(1 − e(t)/ζ))/2π` is a lift with `L 1 = L 0` — **degree 0**.
* `‖ζ‖ < 1`:  `e(t) − ζ = e(t) · (1 − ζ·e(−t))`, and again the second factor has `Re > 0`, so
  `L(t) = t + arg(1 − ζ e(−t))/2π` is a lift — **degree 1**.

Since `Q_θ(z) = C(z − ζ₁)(z − ζ₂)`, adding the two lifts gives the argument principle FOR A
QUADRATIC — which is all the paper uses.  The general argument principle is not needed.

This section builds the infrastructure; the two lift computations come next. -/

/-- A continuous lift of a unimodular loop: `ξ t = e(L t)`. -/
def IsLoopLift (L : ℝ → ℝ) (ξ : ℝ → ℂ) : Prop :=
  Continuous L ∧
    ∀ t : ℝ, ξ t = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (L t : ℂ))

/-- The winding number read off a lift. -/
noncomputable def windOf (L : ℝ → ℝ) : ℝ := L 1 - L 0

theorem phase_eq_exp_arg {z : ℂ} (hz : z ≠ 0) :
    phase z = Complex.exp (Complex.arg z * Complex.I) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr hz
  have h : (‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I) = z :=
    Complex.norm_mul_exp_arg_mul_I z
  unfold phase
  rw [div_eq_iff hn]
  linear_combination -h

theorem phase_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    phase (a * b) = phase a * phase b := by
  have hna : (‖a‖ : ℂ) ≠ 0 := by simpa using norm_ne_zero_iff.mpr ha
  have hnb : (‖b‖ : ℂ) ≠ 0 := by simpa using norm_ne_zero_iff.mpr hb
  unfold phase
  rw [norm_mul]
  push_cast
  field_simp

theorem mem_slitPlane_of_re_pos {z : ℂ} (h : 0 < z.re) : z ∈ Complex.slitPlane := Or.inl h

/-- `Re w < 1` whenever `‖w‖ < 1`, so `1 − w` sits strictly in the right half-plane. -/
theorem re_pos_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - w).re := by
  have h := Complex.re_le_norm w
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem norm_exp_neg_circle (t : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The `‖ζ‖ > 1` factor stays in the right half-plane. -/
theorem outside_factor_re_pos {ζ : ℂ} (hζ : 1 < ‖ζ‖) (t : ℝ) :
    0 < (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) / ζ).re := by
  refine re_pos_of_norm_lt_one ?_
  rw [norm_div, HRTReduction.norm_exp_circle t,
    div_lt_one (by linarith : (0:ℝ) < ‖ζ‖)]
  exact hζ

/-- The `‖ζ‖ < 1` factor stays in the right half-plane. -/
theorem inside_factor_re_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) (t : ℝ) :
    0 < (1 - ζ * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))).re := by
  refine re_pos_of_norm_lt_one ?_
  rw [norm_mul, norm_exp_neg_circle t, mul_one]
  exact hζ

/-- The `‖ζ‖ > 1` factorisation. -/
theorem outside_factor_eq {ζ : ℂ} (hζ0 : ζ ≠ 0) (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ
      = (-ζ) * (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) / ζ) := by
  field_simp
  ring

/-- The `‖ζ‖ < 1` factorisation. -/
theorem inside_factor_eq (ζ : ℂ) (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        * (1 - ζ * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))) := by
  have h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [mul_sub, mul_one]
  linear_combination ζ * h

theorem two_pi_ne_zero_C : (2 * (Real.pi : ℂ)) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by
    simpa using Real.pi_ne_zero
  simpa using this

theorem phase_exp_circle (t : ℝ) :
    phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
  unfold phase
  rw [HRTReduction.norm_exp_circle t]
  norm_num

theorem exp_two_pi_I_one : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
  push_cast
  rw [mul_one]
  exact Complex.exp_two_pi_mul_I

theorem exp_two_pi_I_zero : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) = 1 := by
  push_cast
  simp

/-- **DEGREE 0 when the root lies OUTSIDE the unit circle.** -/
theorem exists_lift_outside {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    ∃ L : ℝ → ℝ,
      IsLoopLift L (fun t => phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ))
        ∧ windOf L = 0 := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    simp at hζ
    linarith
  set u : ℝ → ℂ :=
    fun t => 1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) / ζ with hu
  have hure : ∀ t, 0 < (u t).re := outside_factor_re_pos hζ
  have hune : ∀ t, u t ≠ 0 := by
    intro t h
    have h2 := hure t
    rw [h] at h2
    simp at h2
  have hexp : Continuous (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hucont : Continuous u := continuous_const.sub (hexp.div_const ζ)
  have hargcont : Continuous (fun t => Complex.arg (u t)) :=
    Complex.continuousOn_arg.comp_continuous hucont
      (fun t => mem_slitPlane_of_re_pos (hure t))
  refine ⟨fun t => (Complex.arg (-ζ) + Complex.arg (u t)) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact (continuous_const.add hargcont).div_const _
  · intro t
    dsimp only
    rw [outside_factor_eq hζ0 t, phase_mul (neg_ne_zero.mpr hζ0) (hune t),
      phase_eq_exp_arg (neg_ne_zero.mpr hζ0), phase_eq_exp_arg (hune t), ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  · unfold windOf
    dsimp only
    have h1 : u 1 = u 0 := by
      simp only [hu, exp_two_pi_I_one, exp_two_pi_I_zero]
    rw [h1]
    ring

/-- **DEGREE 1 when the root lies INSIDE the unit circle.** -/
theorem exists_lift_inside {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∃ L : ℝ → ℝ,
      IsLoopLift L (fun t => phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ))
        ∧ windOf L = 1 := by
  set v : ℝ → ℂ :=
    fun t => 1 - ζ * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) with hv
  have hvre : ∀ t, 0 < (v t).re := inside_factor_re_pos hζ
  have hvne : ∀ t, v t ≠ 0 := by
    intro t h
    have h2 := hvre t
    rw [h] at h2
    simp at h2
  have hexpn : Continuous
      (fun t : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg
  have hvcont : Continuous v := continuous_const.sub (hexpn.const_mul ζ)
  have hargcont : Continuous (fun t => Complex.arg (v t)) :=
    Complex.continuousOn_arg.comp_continuous hvcont
      (fun t => mem_slitPlane_of_re_pos (hvre t))
  refine ⟨fun t => t + Complex.arg (v t) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact continuous_id.add (hargcont.div_const _)
  · intro t
    dsimp only
    rw [inside_factor_eq ζ t, phase_mul (Complex.exp_ne_zero _) (hvne t),
      phase_exp_circle t, phase_eq_exp_arg (hvne t), ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  · unfold windOf
    dsimp only
    have he1 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ))) = 1 := by
      push_cast
      rw [mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    have he0 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((0 : ℝ) : ℂ))) = 1 := by
      push_cast
      simp
    have h1 : v 1 = v 0 := by
      simp only [hv, he1, he0]
    rw [h1]
    ring

/-! ### Lifts add, so winding numbers add

This is the whole content of `deg` being a homomorphism — no `π₁` needed, because a lift of a
product is literally the sum of lifts. -/

theorem IsLoopLift.mul {L₁ L₂ : ℝ → ℝ} {ξ₁ ξ₂ : ℝ → ℂ}
    (h₁ : IsLoopLift L₁ ξ₁) (h₂ : IsLoopLift L₂ ξ₂) :
    IsLoopLift (fun t => L₁ t + L₂ t) (fun t => ξ₁ t * ξ₂ t) := by
  refine ⟨h₁.1.add h₂.1, fun t => ?_⟩
  dsimp only
  rw [h₁.2 t, h₂.2 t, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem windOf_add (L₁ L₂ : ℝ → ℝ) :
    windOf (fun t => L₁ t + L₂ t) = windOf L₁ + windOf L₂ := by
  unfold windOf
  ring

/-- The character `t ↦ e(m·t)` has degree `m`. -/
theorem exists_lift_char (m : ℤ) :
    ∃ L : ℝ → ℝ,
      IsLoopLift L (fun t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) * t : ℝ)))
        ∧ windOf L = (m : ℝ) := by
  refine ⟨fun t => (m : ℝ) * t, ⟨continuous_const.mul continuous_id, ?_⟩, ?_⟩
  · intro t
    rfl
  · unfold windOf
    dsimp only
    ring

/-- **THE ARGUMENT PRINCIPLE FOR A QUADRATIC.**  For `Q(z) = C(z−ζ₁)(z−ζ₂)` with both roots off
the unit circle, the loop `t ↦ e(−(j+1)t)·phase(e(t)−ζ₁)·phase(e(t)−ζ₂)` has a lift of winding
number `−(j+1) + rootCount ζ₁ ζ₂`.

This is the paper's `deg ξ_θ = −j−1+N(θ)`: the `z⁻¹` in `P_θ = z⁻¹Q_θ` contributes `−1`, the
`e(−2πijt)` factor contributes `−j`, and each root inside the disc contributes `+1`. -/
theorem exists_lift_quadratic {ζ₁ ζ₂ : ℂ} (j : ℤ) (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1) :
    ∃ L : ℝ → ℝ,
      IsLoopLift L (fun t =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((-(j + 1) : ℤ) : ℝ) * t : ℝ))
            * (phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁)
              * phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂)))
        ∧ windOf L = ((-(j + 1) : ℤ) : ℝ) + ((HRTResonant.rootCount ζ₁ ζ₂ : ℤ) : ℝ) := by
  obtain ⟨Lc, hLc, hwc⟩ := exists_lift_char (-(j + 1))
  have hroot : ∀ ζ : ℂ, ‖ζ‖ ≠ 1 →
      ∃ L : ℝ → ℝ,
        IsLoopLift L (fun t => phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ))
          ∧ windOf L = (if ‖ζ‖ < 1 then (1 : ℝ) else 0) := by
    intro ζ hζ
    rcases lt_or_gt_of_ne hζ with hlt | hgt
    · obtain ⟨L, hL, hw⟩ := exists_lift_inside hlt
      exact ⟨L, hL, by rw [hw, if_pos hlt]⟩
    · obtain ⟨L, hL, hw⟩ := exists_lift_outside hgt
      exact ⟨L, hL, by rw [hw, if_neg (by linarith : ¬ ‖ζ‖ < 1)]⟩
  obtain ⟨L₁, hL₁, hw₁⟩ := hroot ζ₁ h1
  obtain ⟨L₂, hL₂, hw₂⟩ := hroot ζ₂ h2
  refine ⟨fun t => Lc t + (L₁ t + L₂ t), hLc.mul (hL₁.mul hL₂), ?_⟩
  rw [windOf_add, windOf_add, hwc, hw₁, hw₂]
  unfold HRTResonant.rootCount
  by_cases c1 : ‖ζ₁‖ < 1 <;> by_cases c2 : ‖ζ₂‖ < 1 <;>
    simp [c1, c2] <;> push_cast <;> ring

/-! ### The phase cocycle — the deferred normalisation

Earlier this drowned in `field_simp`.  The clean route is not to divide at all: apply `phase` to
the cocycle and use that `phase` is MULTIPLICATIVE, then cancel with `conj·(·) = 1` for the
unimodular factors. -/

theorem phase_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : phase z = z := by
  unfold phase
  rw [hz]
  norm_num

theorem phase_neg (z : ℂ) : phase (-z) = -phase z := by
  unfold phase
  rw [norm_neg]
  ring

theorem phase_ne_zero {z : ℂ} (hz : z ≠ 0) : phase z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_phase hz]
  norm_num

theorem conj_phase_mul {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ) (phase z) * phase z = 1 := by
  rw [mul_comm, Complex.mul_conj', norm_phase hz]
  norm_num

theorem conj_mul_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    (starRingEnd ℂ) z * z = 1 := by
  rw [mul_comm, Complex.mul_conj', hz]
  norm_num

/-- **THE PHASE COCYCLE.**  From `S·Z = −(D·Θ·Z')` with `Θ` unimodular, the phases satisfy
`W' = ξ·W` with `ξ = −phase(S)·conj(phase D)·conj Θ`, which is unimodular.  This is the paper's
`ξ_θ = (Λ_θ/|Λ_θ|)·e^{−2πijt}·P_θ/|P_θ|`. -/
theorem phase_cocycle {Θ Z Z' S D : ℂ}
    (hΘu : ‖Θ‖ = 1) (hD : D ≠ 0) (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) (hS : S ≠ 0)
    (heq : S * Z = -(D * (Θ * Z'))) :
    phase Z'
      = (-(phase S) * (starRingEnd ℂ) (phase D) * (starRingEnd ℂ) Θ) * phase Z := by
  have hΘ0 : Θ ≠ 0 := by
    intro h
    rw [h] at hΘu
    simp at hΘu
  have h1 : phase S * phase Z = -(phase D * (Θ * phase Z')) := by
    have h := congrArg phase heq
    rw [phase_mul hS hZ, phase_neg, phase_mul hD (mul_ne_zero hΘ0 hZ'),
      phase_mul hΘ0 hZ', phase_of_norm_one hΘu] at h
    exact h
  have hkey : phase D * Θ * phase Z' = -(phase S * phase Z) := by linear_combination h1
  have hcD := conj_phase_mul hD
  have hcΘ := conj_mul_of_norm_one hΘu
  calc phase Z'
      = ((starRingEnd ℂ) (phase D) * phase D) * ((starRingEnd ℂ) Θ * Θ) * phase Z' := by
        rw [hcD, hcΘ]; ring
    _ = (starRingEnd ℂ) (phase D) * (starRingEnd ℂ) Θ * (phase D * Θ * phase Z') := by ring
    _ = (starRingEnd ℂ) (phase D) * (starRingEnd ℂ) Θ * (-(phase S * phase Z)) := by rw [hkey]
    _ = (-(phase S) * (starRingEnd ℂ) (phase D) * (starRingEnd ℂ) Θ) * phase Z := by ring

/-- The cocycle's `ξ` is unimodular. -/
theorem norm_phase_cocycle_factor {Θ S D : ℂ}
    (hΘu : ‖Θ‖ = 1) (hD : D ≠ 0) (hS : S ≠ 0) :
    ‖-(phase S) * (starRingEnd ℂ) (phase D) * (starRingEnd ℂ) Θ‖ = 1 := by
  rw [norm_mul, norm_mul, norm_neg, norm_phase hS, RCLike.norm_conj, norm_phase hD,
    RCLike.norm_conj, hΘu]
  norm_num

/-! ### Negative shifts — peeling downward

`exists_zak_modTrans_nat` strips `+1` at a time, so it only reaches `a ≥ 0`.  The same composite
works downward:

    M_{a−1}T_{a−1} = M_{−1} ∘ (M_a T_a) ∘ T_{−1}

`M_{−1}`'s torus multiplier is `chiMint (−1)`; `T_{−1}`'s is `conj chiT1`, obtained from
`T₁ ∘ T_{−1} = id` by the same inverse trick used for `M_{−1}`.  Both unimodular, so once again
the modulus cocycle does not see the integer part — now in either direction. -/

theorem transL_one_neg_cancel (f : Lp ℂ 2 (volume : Measure ℝ)) :
    transL 1 (transL (-1 : ℝ) f) = f := by
  refine Lp.ext_iff.mpr ?_
  have h1 := coeFn_transL 1 (transL (-1 : ℝ) f)
  have h2 := (measurePreserving_sub_right (volume : Measure ℝ) 1).quasiMeasurePreserving.ae_eq_comp
    (coeFn_transL (-1 : ℝ) f)
  filter_upwards [h1, h2] with y hy1 hy2
  simp only [Function.comp_apply] at hy1 hy2
  rw [hy1, hy2]
  norm_num

theorem measurable_conj_chiT1 : Measurable (fun x => (starRingEnd ℂ) (chiT1 x)) :=
  Complex.continuous_conj.measurable.comp measurable_chiT1

theorem norm_conj_chiT1 (x : UnitAddTorus (Fin 2)) : ‖(starRingEnd ℂ) (chiT1 x)‖ = 1 := by
  rw [RCLike.norm_conj]
  exact norm_chiT1 x

theorem conj_chiT1_mul (x : UnitAddTorus (Fin 2)) :
    (starRingEnd ℂ) (chiT1 x) * chiT1 x = 1 := conj_mul_of_norm_one (norm_chiT1 x)

/-- The Zak formula for the shift by `−1`, from `T₁` inverting it. -/
theorem zakL2_transNegOne (f : Lp ℂ 2 (volume : Measure ℝ)) :
    zakCLM (transL (-1 : ℝ) f)
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_conj_chiT1 norm_conj_chiT1 (zakCLM f) := by
  have hstep : zakCLM f
      = HRTShift.multLC
          (μ := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
          measurable_chiT1 norm_chiT1 (zakCLM (transL (-1 : ℝ) f)) := by
    conv_lhs => rw [← transL_one_neg_cancel f]
    exact congrFun zakL2_transOne_of_memLp (transL (-1 : ℝ) f)
  rw [hstep]
  exact (multLC_inv_cancel measurable_conj_chiT1 norm_conj_chiT1
    measurable_chiT1 norm_chiT1 conj_chiT1_mul (zakCLM (transL (-1 : ℝ) f))).symm

/-- **The composite, downward.**  `M_{a−1}T_{a−1} = M_{−1} ∘ (M_a T_a) ∘ T_{−1}`. -/
theorem modTransCLM_pred (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modTransCLM (a - 1) f = modCLM (-1 : ℝ) (modTransCLM a (transL (-1 : ℝ) f)) := by
  refine Lp.ext_iff.mpr ?_
  have hLL : (↑↑(modTransCLM (a - 1) f) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a - 1 : ℝ) : ℂ) * (y : ℂ))
        * (↑↑f : ℝ → ℂ) (y - (a - 1)) := by
    refine (coeFn_modCLM (a - 1) (transL (a - 1) f)).trans ?_
    filter_upwards [coeFn_transL (a - 1) f] with y hy
    simp only [Function.comp_apply] at hy
    rw [hy]
  have hR : (↑↑(modCLM (-1 : ℝ) (modTransCLM a (transL (-1 : ℝ) f))) : ℝ → ℂ) =ᵐ[volume]
      fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a - 1 : ℝ) : ℂ) * (y : ℂ))
        * (↑↑f : ℝ → ℂ) (y - (a - 1)) := by
    refine (coeFn_modCLM (-1 : ℝ) (modTransCLM a (transL (-1 : ℝ) f))).trans ?_
    have h2 : (↑↑(modTransCLM a (transL (-1 : ℝ) f)) : ℝ → ℂ)
        =ᵐ[volume] (↑↑(modCLM a (transL a (transL (-1 : ℝ) f))) : ℝ → ℂ) := by rfl
    have h3 := (coeFn_modCLM a (transL a (transL (-1 : ℝ) f)))
    have h4 := coeFn_transL a (transL (-1 : ℝ) f)
    have h5 := (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_transL (-1 : ℝ) f)
    filter_upwards [h2, h3, h4, h5] with y h2y h3y h4y h5y
    simp only [Function.comp_apply] at h4y h5y
    rw [h2y, h3y, h4y, h5y]
    have hsub : y - a - (-1 : ℝ) = y - (a - 1) := by ring
    rw [hsub, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact hLL.trans hR.symm

/-- **The Zak image of `M_{n+α}T_{n+α}` for ANY integer `n`** — positive or negative.  Peeling
`+1` uses `modTransCLM_succ`, peeling `−1` uses `modTransCLM_pred`; both contribute only
unimodular factors, and neither moves the point beyond `antidiag α`. -/
theorem exists_zak_modTrans_int (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (n : ℤ) :
    ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ∃ (χ : UnitAddTorus (Fin 2) → ℂ) (hm : Measurable χ) (hu : ∀ x, ‖χ x‖ = 1),
        zakCLM (modTransCLM ((n : ℝ) + α) f)
          = HRTShift.multLC
              (μ := Measure.pi
                (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
              hm hu (antidiagL α (zakCLM f)) := by
  induction n using Int.induction_on with
  | zero =>
      intro f
      refine ⟨psiRot α, measurable_psiRot α, norm_psiRot α, ?_⟩
      rw [show ((0 : ℤ) : ℝ) + α = α by norm_num]
      exact congrFun (zakL2_modShift_of_memLp α hα0 hα1) f
  | succ n ih =>
      intro f
      obtain ⟨χ, hm, hu, hχ⟩ := ih (transL 1 f)
      refine ⟨fun x => chiM1 x * χ x * chiT1 (antidiagT α x),
        (measurable_chiM1.mul hm).mul
          (measurable_chiT1.comp (measurePreserving_antidiagT α).measurable),
        fun x => by rw [norm_mul, norm_mul, norm_chiM1, hu, norm_chiT1]; norm_num, ?_⟩
      have hcast : (((n : ℤ) + 1 : ℤ) : ℝ) + α = 1 + (((n : ℤ) : ℝ) + α) := by push_cast; ring
      rw [hcast, modTransCLM_succ,
        congrFun zakL2_modOne_of_memLp (modTransCLM (((n : ℤ) : ℝ) + α) (transL 1 f)),
        hχ, congrFun zakL2_transOne_of_memLp f, antidiagL_multLC, multLC_multLC,
        multLC_multLC]
  | pred n ih =>
      intro f
      obtain ⟨χ, hm, hu, hχ⟩ := ih (transL (-1 : ℝ) f)
      refine ⟨fun x => chiMint (-1) x * χ x * (starRingEnd ℂ) (chiT1 (antidiagT α x)),
        ((measurable_chiMint (-1)).mul hm).mul
          (measurable_conj_chiT1.comp (measurePreserving_antidiagT α).measurable),
        fun x => by
          rw [norm_mul, norm_mul, norm_chiMint, hu, norm_conj_chiT1]; norm_num, ?_⟩
      have hcast : ((-(n : ℤ) - 1 : ℤ) : ℝ) + α = ((((-(n : ℤ)) : ℤ) : ℝ) + α) - 1 := by
        push_cast; ring
      rw [hcast, modTransCLM_pred,
        zakL2_modNegOne (modTransCLM ((((-(n : ℤ)) : ℤ) : ℝ) + α) (transL (-1 : ℝ) f)),
        hχ, zakL2_transNegOne f, antidiagL_multLC, multLC_multLC, multLC_multLC]

/-- **THE COCYCLE FOR ANY REAL SHIFT AND ANY `j`.**  No sign restriction — the paper's full
generality on the modulus side. -/
theorem cocycle_norm_int {g : ℝ → ℂ} (A B C D : ℂ) (α : ℝ) (n : ℤ) (j : ℤ)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
                * ((((n : ℝ) + α) + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - ((n : ℝ) + α))) = 0) :
    CocycleNorm A B C D α f := by
  set μT := Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) with hμT
  set Z := zakCLM f with hZ
  set T1 := HRTShift.multLC (μ := μT) measurable_chiT1 norm_chiT1 Z with hT1
  set M1 := HRTShift.multLC (μ := μT) measurable_chiM1 norm_chiM1 Z with hM1
  obtain ⟨χ, hm, hu, hχ⟩ := exists_zak_modTrans_int α hα0 hα1 n f
  set S := HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
    (HRTShift.multLC (μ := μT) hm hu (antidiagL α Z)) with hS
  have h0 : A • Z + B • T1 + C • M1 + D • S = 0 := by
    have hLp := dep_Lp_j A B C D ((n : ℝ) + α) j f hae hdep
    have h1 : zakCLM (A • f + B • (transL 1 f) + C • (mod1CLM f)
        + D • (modCLM ((j : ℝ)) (modTransCLM ((n : ℝ) + α) f))) = 0 := by
      rw [hLp, map_zero]
    simp only [map_add, map_smul] at h1
    have e1 : zakCLM (transL 1 f) = T1 := congrFun zakL2_transOne_of_memLp f
    have e2 : zakCLM (mod1CLM f) = M1 := congrFun zakL2_modOne_of_memLp f
    have e3 : zakCLM (modCLM ((j : ℝ)) (modTransCLM ((n : ℝ) + α) f))
        = HRTShift.multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
            (zakCLM (modTransCLM ((n : ℝ) + α) f)) :=
      zakL2_modInt j (modTransCLM ((n : ℝ) + α) f)
    rw [e3, hχ, e1, e2] at h1
    exact h1
  have hcoe : (↑↑(A • Z + B • T1 + C • M1 + D • S) : UnitAddTorus (Fin 2) → ℂ) =ᵐ[μT] 0 := by
    rw [h0]; exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μT)
  have hpt : ∀ᵐ x ∂μT, symbolTor A B C x * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) x
      = -(D * (chiMint j x * (χ x
          * (↑↑Z : UnitAddTorus (Fin 2) → ℂ) (antidiagT α x)))) := by
    filter_upwards [hcoe,
      Lp.coeFn_add (A • Z + B • T1 + C • M1) (D • S),
      Lp.coeFn_add (A • Z + B • T1) (C • M1),
      Lp.coeFn_add (A • Z) (B • T1),
      Lp.coeFn_smul A Z, Lp.coeFn_smul B T1, Lp.coeFn_smul C M1, Lp.coeFn_smul D S,
      coeFn_multLC (μ := μT) measurable_chiT1 norm_chiT1 Z,
      coeFn_multLC (μ := μT) measurable_chiM1 norm_chiM1 Z,
      coeFn_multLC (μ := μT) (measurable_chiMint j) (norm_chiMint j)
        (HRTShift.multLC (μ := μT) hm hu (antidiagL α Z)),
      coeFn_multLC (μ := μT) hm hu (antidiagL α Z),
      coeFn_antidiagL α Z]
      with x hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mX mA
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Function.comp_apply] at hz e1 e2 e3 s1 s2 s3 s4 m1 m2 mS mX mA
    rw [e1, e2, e3, s1, s2, s3, s4, m1, m2, mS, mX, mA] at hz
    unfold symbolTor
    linear_combination hz
  filter_upwards [hpt] with x hx
  have h := congrArg norm hx
  simp only [norm_mul, norm_neg, norm_chiMint, hu, one_mul] at h
  exact h

/-- **GAP 2 FULLY CLOSED** — the cocycle for an arbitrary real shift, no sign restriction. -/
theorem cocycle_norm_of_real {g : ℝ → ℂ} (A B C D : ℂ) (a : ℝ) (j : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hae : (↑↑f : ℝ → ℂ) =ᵐ[volume] g)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
            * g (y - a)) = 0) :
    CocycleNorm A B C D (Int.fract a) f := by
  refine cocycle_norm_int A B C D (Int.fract a) ⌊a⌋ j (Int.fract_nonneg a)
    (Int.fract_lt_one a) f hae ?_
  intro y
  rw [Int.floor_add_fract a]
  exact hdep y

/-- **THE PAPER'S THEOREM 1, IN FULL — every irrational `a`, every `j`, no sign restriction.**

Given the ILR degree clause, for every nonzero `L²` window there is no dependence

    `A g + B T₁g + C M₁g + D M_{a+j}T_a g = 0`

with all four coefficients nonzero.  `hj1`/`hjm1` are the paper's `j ≠ ±1` exclusions, vacuous
for every other `j`.

Everything here is proved: the Zak transform as an `L²` isometry, the cocycle, the fibration,
liveness, ergodicity, Birkhoff, Jensen, the root condition, and the shift in both directions.
The one hypothesis is `hILR` — which the source paper likewise takes as an external citation. -/
theorem no_resonant_dependence_of_ILR_real {g : ℝ → ℂ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (a : ℝ) (hairr : Irrational a)
    (j : ℤ) (hj1 : j = 1 → ‖D‖ ≠ ‖C‖) (hjm1 : j = -1 → ‖D‖ ≠ ‖B‖)
    (hILR : ∀ w : ℂ, ‖w‖ = 1 → ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → HRTResonant.rootCount ζ₁ ζ₂ = 1 + j)
    (hdepFun : A • g + B • HRTResonant.timeShift 1 g + C • HRTResonant.modulate 1 g
      + D • HRTResonant.modulate (a + (j : ℝ)) (HRTResonant.timeShift a g) = 0) :
    False := by
  have hae : (↑↑(hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hf : hg2.toLp g ≠ 0 := by
    intro h
    refine hgne (hae.symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (j : ℝ) : ℝ) : ℂ) * (y : ℂ))
          * g (y - a)) = 0 := by
    intro y
    have h := congrFun hdepFun y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      HRTResonant.timeShift, HRTResonant.modulate, Complex.ofReal_one, mul_one] at h
    exact h
  have hcn := cocycle_norm_of_real A B C D a j (hg2.toLp g) hae hdep
  obtain ⟨L, hinf, hunit, hmean⟩ :=
    exists_infinite_mean_of (irrational_fract hairr) hA hB hC hD hf hcn
  have hmean' : ∀ w ∈ L, Real.circleAverage
      (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖ := by
    intro w hw
    rw [← HRTResonant.quadratic_fibre_mean_eq_circleAverage]
    exact hmean w hw
  obtain ⟨w₁, w₂, w₃, w₄, hsub⟩ :=
    HRTResonant.live_set_subset_four A B C D hA hB hC hD j hj1 hjm1 L hunit hmean'
      (fun w hw ζ₁ ζ₂ hfac h1 h2 => hILR w (hunit w hw) ζ₁ ζ₂ hfac h1 h2)
  exact hinf (Set.Finite.subset (Set.toFinite ({w₁, w₂, w₃, w₄} : Set ℂ)) hsub)

/-! ## The paper's Theorem 2 (ILR), STATED — and its Lemma, PROVED from it

Until now `hILR` was the *conclusion* of the paper's degree-kill Lemma (`rootCount = 1+j`).  That
conflated two different things: the paper's **Theorem 2** (Iwanik–Lemańczyk–Rudolph, cited) and
its **Lemma** deriving `N(θ) = 1+j` from Theorem 2 plus the degree formula.

Now that `exists_lift_quadratic` proves the degree formula, the two can be separated properly:
`ILRStatement` states Theorem 2, and `rootCount_eq_of_ILR` *proves* the Lemma from it.  So the
Lean now mirrors the paper's logical structure exactly — Theorem 2 cited, everything downstream
derived.

`ILRStatement` is a hypothesis, not an axiom: nothing in this file asserts it, and any consumer
must supply it. -/

/-- The loop whose degree the paper computes: `e(−(j+1)t)·phase(e(t)−ζ₁)·phase(e(t)−ζ₂)`, i.e.
`ξ_θ` up to the constant unimodular factor (which has degree `0` and so does not affect it). -/
noncomputable def quadLoop (j : ℤ) (ζ₁ ζ₂ : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((-(j + 1) : ℤ) : ℝ) * t : ℝ))
    * (phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁)
      * phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂))

/-- **THE PAPER'S THEOREM 2 (Iwanik–Lemańczyk–Rudolph).**

Israel J. Math. **83** (1993) 73–95.  For an irrational rotation and a unimodular loop of nonzero
degree, `V_{ξ,α}` has Lebesgue maximal spectral type and hence NO eigenvectors — equivalently, the
cocycle equation `W(t−a) = ξ(t)·W(t)` admits no unimodular solution.

Stated here in the form the paper's Lemma consumes.  **Not proved** — the source paper cites it
too ("We use one external spectral theorem"), and its conclusion is not even expressible in
current Mathlib, which has no maximal spectral type, no spectral measure for unitaries and no
Lebesgue spectrum. -/
def ILRStatement : Prop :=
  ∀ a : ℝ, Irrational a → ∀ (j : ℤ) (ζ₁ ζ₂ : ℂ) (L : ℝ → ℝ),
    IsLoopLift L (quadLoop j ζ₁ ζ₂) → windOf L ≠ 0 →
      ¬ ∃ W : ℝ → ℂ, (∀ t, ‖W t‖ = 1) ∧ (∀ t, W (t + 1) = W t) ∧
        ∀ t, W (t - a) = quadLoop j ζ₁ ζ₂ t * W t

/-- **THE PAPER'S DEGREE-KILL LEMMA, PROVED FROM THEOREM 2.**

If the phase cocycle has a unimodular solution, then `deg ξ_θ = 0`, i.e. `N(θ) = 1 + j`.  This is
the step that previously had to be assumed. -/
theorem rootCount_eq_of_ILR (hILR : ILRStatement) {a : ℝ} (hairr : Irrational a)
    {j : ℤ} {ζ₁ ζ₂ : ℂ} (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (W : ℝ → ℂ) (hWu : ∀ t, ‖W t‖ = 1) (hWp : ∀ t, W (t + 1) = W t)
    (hcoc : ∀ t, W (t - a) = quadLoop j ζ₁ ζ₂ t * W t) :
    HRTResonant.rootCount ζ₁ ζ₂ = 1 + j := by
  by_contra hne
  obtain ⟨L, hL, hw⟩ := exists_lift_quadratic j h1 h2
  refine hILR a hairr j ζ₁ ζ₂ L hL ?_ ⟨W, hWu, hWp, hcoc⟩
  rw [hw]
  intro h
  refine hne ?_
  have hz : ((-(j + 1) + HRTResonant.rootCount ζ₁ ζ₂ : ℤ) : ℝ) = 0 := by
    push_cast
    push_cast at h
    linarith
  have hzz : (-(j + 1) + HRTResonant.rootCount ζ₁ ζ₂ : ℤ) = 0 := by exact_mod_cast hz
  omega

/-! ## Towards ILR itself — the character case

ILR in general is out of reach (its conclusion, Lebesgue maximal spectral type, is not
expressible in current Mathlib).  But for a PURE CHARACTER loop `ξ(t) = fourier d t` with
`d ≠ 0` it is elementary, and that case can be proved outright:

the cocycle forces `Ŵ(n)·fourier(−n)(a) = Ŵ(n−d)`, so `|Ŵ|` is constant along every arithmetic
progression of step `d`; Parseval makes `Σ|Ŵ|²` finite; an infinite progression of a constant
value therefore forces that value to be `0`, so `W = 0` — contradicting `‖W‖ = 1`.

Mathlib has Parseval (`tsum_sq_fourierCoeff`) but neither transformation rule, so both are
proved here. -/

theorem fourier_add_arg (n : ℤ) (x y : UnitAddCircle) :
    (fourier n (x + y) : ℂ) = (fourier n x : ℂ) * (fourier n y : ℂ) := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- **Modulation rule.**  Multiplying by `fourier d` shifts the coefficient index by `d`. -/
theorem fourierCoeff_fourier_mul (f : UnitAddCircle → ℂ) (d n : ℤ) :
    fourierCoeff (fun t => (fourier d t : ℂ) * f t) n = fourierCoeff f (n - d) := by
  unfold fourierCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← fourier_add]
  congr 1
  ring

/-- **Translation rule.**  Translating the argument multiplies the coefficient by a character. -/
theorem fourierCoeff_comp_sub (f : UnitAddCircle → ℂ) (c : UnitAddCircle) (n : ℤ) :
    fourierCoeff (fun t => f (t - c)) n = (fourier (-n) c : ℂ) * fourierCoeff f n := by
  have hmp : MeasurePreserving (fun s : UnitAddCircle => s + c)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    measurePreserving_add_right _ c
  have hme : MeasurableEmbedding (fun s : UnitAddCircle => s + c) :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  unfold fourierCoeff
  rw [← hmp.integral_comp hme (fun t => (fourier (-n) t : ℂ) • f (t - c))]
  have hpt : ∀ s : UnitAddCircle,
      (fourier (-n) (s + c) : ℂ) • f ((s + c) - c)
        = (fourier (-n) c : ℂ) * ((fourier (-n) s : ℂ) • f s) := by
    intro s
    rw [add_sub_cancel_right, fourier_add_arg]
    simp only [smul_eq_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]

theorem norm_fourier_arg (n : ℤ) (x : UnitAddCircle) : ‖(fourier n x : ℂ)‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The cocycle forces the coefficient moduli to be constant along steps of `d`. -/
theorem norm_fourierCoeff_step {a : ℝ} {d : ℤ} (W : UnitAddCircle → ℂ)
    (hcoc : ∀ x, W (x - ((a : ℝ) : UnitAddCircle)) = (fourier d x : ℂ) * W x) (n : ℤ) :
    ‖fourierCoeff W (n - d)‖ = ‖fourierCoeff W n‖ := by
  have h1 : fourierCoeff (fun t => W (t - ((a : ℝ) : UnitAddCircle))) n
      = (fourier (-n) ((a : ℝ) : UnitAddCircle) : ℂ) * fourierCoeff W n :=
    fourierCoeff_comp_sub W _ n
  have h2 : fourierCoeff (fun t => W (t - ((a : ℝ) : UnitAddCircle))) n
      = fourierCoeff W (n - d) := by
    rw [show (fun t => W (t - ((a : ℝ) : UnitAddCircle)))
        = fun t => (fourier d t : ℂ) * W t from funext hcoc]
    exact fourierCoeff_fourier_mul W d n
  rw [← h2, h1, norm_mul, norm_fourier_arg]
  ring

/-- Hence constant along the whole progression `n₀ + k·d`. -/
theorem norm_fourierCoeff_prog {a : ℝ} {d : ℤ} (W : UnitAddCircle → ℂ)
    (hcoc : ∀ x, W (x - ((a : ℝ) : UnitAddCircle)) = (fourier d x : ℂ) * W x) (n₀ : ℤ) :
    ∀ k : ℤ, ‖fourierCoeff W (n₀ + k * d)‖ = ‖fourierCoeff W n₀‖ := by
  intro k
  induction k using Int.induction_on with
  | zero => norm_num
  | succ m ih =>
      have hstep := norm_fourierCoeff_step W hcoc (n₀ + ((m : ℤ) + 1) * d)
      rw [show n₀ + ((m : ℤ) + 1) * d - d = n₀ + (m : ℤ) * d by ring] at hstep
      rw [← hstep]
      exact ih
  | pred m ih =>
      have hstep := norm_fourierCoeff_step W hcoc (n₀ + (-(m : ℤ)) * d)
      rw [show n₀ + (-(m : ℤ)) * d - d = n₀ + (-(m : ℤ) - 1) * d by ring] at hstep
      rw [hstep]
      exact ih

/-- **THE PAPER'S THEOREM 2, PROVED FOR CHARACTER LOOPS.**

For `ξ = fourier d` with `d ≠ 0` there is no unimodular `W` on the circle satisfying the cocycle
equation.  Elementary: the two transformation rules make `‖Ŵ‖` constant along every progression
of step `d`, Parseval makes `Σ‖Ŵ‖²` finite, and an infinite progression of a constant forces that
constant to vanish — whereupon Parseval gives `0 = 1`.

Note irrationality of `a` is NOT used: the character case holds for every shift.  It is the
GENERAL case that needs it, and that is where ILR's spectral machinery becomes unavoidable — the
paper's `ξ_θ` carries `P_θ/|P_θ|` and is not a character, and reducing it to one requires a
measurable solution of `u(t−a)/u(t) = e(ψ(t))`, which need not exist. -/
theorem ILR_character {a : ℝ} {d : ℤ} (hd : d ≠ 0)
    (W : UnitAddCircle → ℂ) (hWm : Measurable W) (hWu : ∀ x, ‖W x‖ = 1)
    (hcoc : ∀ x, W (x - ((a : ℝ) : UnitAddCircle)) = (fourier d x : ℂ) * W x) :
    False := by
  have hW2 : MemLp W 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    MemLp.of_bound hWm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => le_of_eq (hWu x)))
  have hFae : (↑↑(hW2.toLp W) : UnitAddCircle → ℂ)
      =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)] W := hW2.coeFn_toLp
  have hcoeff : ∀ n, fourierCoeff (↑↑(hW2.toLp W) : UnitAddCircle → ℂ) n = fourierCoeff W n := by
    intro n
    unfold fourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hFae] with x hx
    simp only [hx]
  have hpars := tsum_sq_fourierCoeff (hW2.toLp W)
  have hone : ∫ t : UnitAddCircle, ‖(↑↑(hW2.toLp W) : UnitAddCircle → ℂ) t‖ ^ 2
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) = 1 := by
    have hae : ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        ‖(↑↑(hW2.toLp W) : UnitAddCircle → ℂ) t‖ ^ 2 = 1 := by
      filter_upwards [hFae] with t ht
      rw [ht, hWu t]
      norm_num
    rw [integral_congr_ae hae]
    simp
  simp only [hcoeff] at hpars
  rw [hone] at hpars
  -- every coefficient vanishes, so the sum is 0, contradicting Parseval
  have hsum : Summable (fun n : ℤ => ‖fourierCoeff W n‖ ^ 2) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hpars
    exact zero_ne_one hpars
  have hzero : ∀ n : ℤ, fourierCoeff W n = 0 := by
    intro n
    by_contra hne
    have hpos : 0 < ‖fourierCoeff W n‖ ^ 2 := by positivity
    have hinj : Function.Injective (fun k : ℤ => n + k * d) := by
      intro k₁ k₂ hk
      simp only at hk
      have : k₁ * d = k₂ * d := by linarith [hk]
      exact mul_right_cancel₀ hd this
    have hsub := hsum.comp_injective hinj
    have hconst : (fun k : ℤ => ‖fourierCoeff W ((fun k : ℤ => n + k * d) k)‖ ^ 2)
        = fun _ : ℤ => ‖fourierCoeff W n‖ ^ 2 := by
      funext k
      rw [norm_fourierCoeff_prog W hcoc n k]
    rw [Function.comp_def, hconst] at hsub
    exact absurd (tendsto_const_nhds_iff.mp hsub.tendsto_cofinite_zero) (ne_of_gt hpos)
  simp only [hzero, norm_zero] at hpars
  norm_num at hpars

/-! ### The paper's `ξ_θ` IS `quadLoop`

The last link of §4.  `P_θ(t) = z⁻¹·Q_θ(z)` with `Q_θ(z) = C(z−ζ₁)(z−ζ₂)`, so phase
multiplicativity factors the symbol's phase into exactly the loops whose degrees
`exists_lift_quadratic` computes: the `z⁻¹` supplies the `−1`, the `e(−2πijt)` twist the `−j`,
and each root its `+1` or `0`. -/

theorem phase_exp_neg_circle (t : ℝ) :
    phase (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) :=
  phase_of_norm_one (norm_exp_neg_circle t)

/-- **The symbol's phase factors through the roots.** -/
theorem phase_fibre_symbol {C ζ₁ ζ₂ : ℂ} (hC : C ≠ 0) (t : ℝ)
    (h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁ ≠ 0)
    (h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂ ≠ 0) :
    phase (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
        * (C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁)
             * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂)))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) * phase C
          * phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₁)
          * phase (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ₂) := by
  rw [phase_mul (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero hC h1) h2),
    phase_exp_neg_circle, phase_mul (mul_ne_zero hC h1) h2, phase_mul hC h1]
  ring

/-- A root off the unit circle is never met by `e(t)`. -/
theorem exp_circle_sub_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ ≠ 1) (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - ζ ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hζ (by rw [← h]; exact HRTReduction.norm_exp_circle t)

/-! ## Bridge to the `Principia-Math-Solutions/hrt-lambda0` vocabulary

That directory formalises the ENDGAME of a companion paper and carries the whole analytic
reduction as one unproved hypothesis, `ZakReduction` — "the Zak-transform reduction, the fibre
dichotomy, the degree identity at `j = 0`, and Jensen's formula on the fibre", none of it proved
there.  Its README notes that discharging it "would need a Lean theory of the Zak transform,
circle-map degree theory, and Jensen's formula — none of which is in Mathlib".

All three now exist here.  The definitions below MIRROR that directory's `HRTLambda0.Statement`
so the transfer can be verified in this tree, where the build runs; in the merged directory the
real statement module is used and these are deleted. -/

namespace HRTLambda0Mirror

/-- Mirror of `HRTLambda0.tfTranslate`. -/
noncomputable def tfTranslate (a b : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (x : ℂ)) * g (x - a)

/-- Mirror of `HRTLambda0.configTranslates`. -/
noncomputable def configTranslates (α : ℝ) (j : ℤ) (g : ℝ → ℂ) : Fin 4 → (ℝ → ℂ)
  | 0 => tfTranslate 0 0 g
  | 1 => tfTranslate 1 0 g
  | 2 => tfTranslate 0 1 g
  | 3 => tfTranslate α (α + (j : ℝ)) g

/-- Mirror of `HRTLambda0.lambda0Translates`. -/
noncomputable def lambda0Translates (g : ℝ → ℂ) : Fin 4 → (ℝ → ℂ) :=
  configTranslates (Real.sqrt 2) 0 g

end HRTLambda0Mirror

/-- **The two formalisations describe the same four functions.** -/
theorem lambda0Translates_eq (g : ℝ → ℂ) :
    HRTLambda0Mirror.lambda0Translates g = HRTResonant.lambdaZeroFamily g := by
  funext i x
  fin_cases i
  · simp [HRTLambda0Mirror.lambda0Translates, HRTLambda0Mirror.configTranslates,
      HRTLambda0Mirror.tfTranslate, HRTResonant.lambdaZeroFamily]
  · simp [HRTLambda0Mirror.lambda0Translates, HRTLambda0Mirror.configTranslates,
      HRTLambda0Mirror.tfTranslate, HRTResonant.lambdaZeroFamily, HRTResonant.timeShift]
  · simp [HRTLambda0Mirror.lambda0Translates, HRTLambda0Mirror.configTranslates,
      HRTLambda0Mirror.tfTranslate, HRTResonant.lambdaZeroFamily, HRTResonant.modulate]
  · simp [HRTLambda0Mirror.lambda0Translates, HRTLambda0Mirror.configTranslates,
      HRTLambda0Mirror.tfTranslate, HRTResonant.lambdaZeroFamily, HRTResonant.modulate,
      HRTResonant.timeShift]

/-- **`hrt-lambda0`'s conclusion, from ILR instead of `ZakReduction`.**

Their `lambda0_independent_of_reduction` assumes the entire analytic reduction.  This proves the
same conclusion with that package DISCHARGED — the Zak theory, fibre dichotomy, degree identity
and Jensen are all theorems here — leaving only the ILR degree clause, a single named literature
citation. -/
theorem lambda0Translates_linearIndependent_of_ILR (g : ℝ → ℂ) (hgm : Measurable g)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (hILR : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        ∀ w : ℂ, ‖w‖ = 1 → ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → HRTResonant.rootCount ζ₁ ζ₂ = 1) :
    LinearIndependent ℂ (HRTLambda0Mirror.lambda0Translates g) := by
  rw [lambda0Translates_eq]
  exact heil_speegle_lambda_zero_L2_of_ILR g hgm hg2 hgne hILR

end HRTBridge

/-! ## Acceptance gate -/

#print axioms HRTBridge.rep1_coe
#print axioms HRTBridge.measurable_rep1
#print axioms HRTBridge.torus_integral_eq_prod
#print axioms HRTBridge.prod_integral_iterated
#print axioms HRTBridge.circle_integral_eq_interval
#print axioms HRTBridge.mFourier_two
#print axioms HRTBridge.fourier_eq_ee
#print axioms HRTBridge.box_coeff_eq_W
#print axioms HRTBridge.coeff_eq_prod
#print axioms HRTBridge.integrand_simp
#print axioms HRTBridge.rep_ae
#print axioms HRTBridge.coeff_iter_circle
#print axioms HRTBridge.fourier_eq_ee_rep
#print axioms HRTBridge.iter_circle_to_interval
#print axioms HRTBridge.coeff_interval
#print axioms HRTBridge.W_vanishes_off
#print axioms HRTBridge.inner_reorder
#print axioms HRTBridge.coeff_zakTor_eq_W
#print axioms HRTBridge.rep1_mem
#print axioms HRTBridge.rep1_mem_Icc
#print axioms HRTBridge.zakTor_finsum
#print axioms HRTBridge.memLp_shift
#print axioms HRTBridge.circle_lint_le
#print axioms HRTBridge.memLp_g_rep
#print axioms HRTBridge.mp_eval0
#print axioms HRTBridge.memLp_zakTor
#print axioms HRTBridge.fourier_neg_point
#print axioms HRTBridge.mFourier_rotT
#print axioms HRTBridge.shear_rot
#print axioms HRTBridge.shear_rotSnd
#print axioms HRTBridge.measurePreserving_rotSnd
#print axioms HRTBridge.measurePreserving_rotSnd'
#print axioms HRTBridge.RaSnd
#print axioms HRTBridge.norm_RaSnd
#print axioms HRTBridge.norm_phiSnd
#print axioms HRTBridge.measurable_phiSnd
#print axioms HRTBridge.MphiSnd
#print axioms HRTBridge.norm_MphiSnd
#print axioms HRTBridge.SaSnd
#print axioms HRTBridge.norm_SaSnd
#print axioms HRTBridge.rep1_sub
#print axioms HRTBridge.zakTor_shift
#print axioms HRTBridge.mp_sigma
#print axioms HRTBridge.measurePreserving_rotT
#print axioms HRTBridge.rotTEquiv_apply
#print axioms HRTBridge.measurableEmbedding_rotT
#print axioms HRTBridge.neg_index
#print axioms HRTBridge.neg_rot_index
#print axioms HRTBridge.coeff_comp_rotT
#print axioms HRTBridge.mFourierCoeff_congr_ae
#print axioms HRTBridge.norm_mFourier
#print axioms HRTBridge.integrable_mFourier_zakTor
#print axioms HRTBridge.measurePreserving_rotT_haar
#print axioms HRTBridge.memLp_zakTor_haar
#print axioms HRTBridge.zakL2_eq_zakTor_comp_rotT
#print axioms HRTBridge.measurePreserving_tauT
#print axioms HRTBridge.norm_phiTor
#print axioms HRTBridge.measurable_phiTor
#print axioms HRTBridge.zakTor_shift_eq
#print axioms HRTBridge.hasCompactSupport_shift
#print axioms HRTBridge.memLp_shift_real
#print axioms HRTBridge.toLp_zakTor_shift
#print axioms HRTBridge.sigmaT_conj
#print axioms HRTBridge.measurePreserving_sigmaT
#print axioms HRTBridge.coeFn_multLC
#print axioms HRTBridge.norm_phiRot
#print axioms HRTBridge.measurable_phiRot
#print axioms HRTBridge.zakL2_shift
#print axioms HRTBridge.measurable_rep
#print axioms HRTBridge.memLp_rep
#print axioms HRTBridge.zakOf_congr
#print axioms HRTBridge.zakOf_add
#print axioms HRTBridge.zakOf_smul
#print axioms HRTBridge.zakLM
#print axioms HRTBridge.normSq_Lp
#print axioms HRTBridge.normSq_W
#print axioms HRTBridge.norm_zakOf
#print axioms HRTBridge.zakCLM
#print axioms HRTBridge.dense_CS
#print axioms HRTBridge.transL
#print axioms HRTBridge.sigL
#print axioms HRTBridge.continuous_shiftLHS
#print axioms HRTBridge.continuous_shiftRHS
#print axioms HRTBridge.eqOn_CS
#print axioms HRTBridge.zakL2_shift_of_memLp
#print axioms HRTBridge.zak_rep_snd
#print axioms HRTBridge.zak_sub_wrap
#print axioms HRTBridge.zakTor_modShift
#print axioms HRTBridge.antidiagT_conj
#print axioms HRTBridge.measurePreserving_antidiagT
#print axioms HRTBridge.norm_psiTor
#print axioms HRTBridge.measurable_psiTor
#print axioms HRTBridge.norm_psiRot
#print axioms HRTBridge.measurable_psiRot
#print axioms HRTBridge.memLp_modShift
#print axioms HRTBridge.hasCompactSupport_modShift
#print axioms HRTBridge.zakTor_modShift_eq
#print axioms HRTBridge.zakL2_modShift
#print axioms HRTBridge.continuous_modShiftLHS
#print axioms HRTBridge.continuous_modShiftRHS
#print axioms HRTBridge.modEqOn_CS
#print axioms HRTBridge.zakL2_modShift_of_memLp
#print axioms HRTBridge.zakTor_transOne
#print axioms HRTBridge.zakTor_modOne
#print axioms HRTBridge.norm_chiT1
#print axioms HRTBridge.norm_chiM1
#print axioms HRTBridge.measurable_chiT1
#print axioms HRTBridge.measurable_chiM1
#print axioms HRTBridge.memLp_trans1
#print axioms HRTBridge.memLp_mod1
#print axioms HRTBridge.hasCompactSupport_trans1
#print axioms HRTBridge.hasCompactSupport_mod1
#print axioms HRTBridge.zakL2_transOne
#print axioms HRTBridge.zakL2_modOne
#print axioms HRTBridge.continuous_T1LHS
#print axioms HRTBridge.continuous_T1RHS
#print axioms HRTBridge.continuous_M1LHS
#print axioms HRTBridge.continuous_M1RHS
#print axioms HRTBridge.T1_eqOn_CS
#print axioms HRTBridge.M1_eqOn_CS
#print axioms HRTBridge.zakL2_transOne_of_memLp
#print axioms HRTBridge.zakL2_modOne_of_memLp
#print axioms HRTBridge.dep_Lp
#print axioms HRTBridge.zakCLM_dep
#print axioms HRTBridge.coeFn_antidiagL
#print axioms HRTBridge.cocycle_eq
#print axioms HRTBridge.cocycle_norm
#print axioms HRTBridge.piFinTwo_antidiag
#print axioms HRTBridge.shear_conj_antidiagP
#print axioms HRTBridge.measurePreserving_antidiagP
#print axioms HRTBridge.toTor_conj_antidiag
#print axioms HRTBridge.cocycle_prod
#print axioms HRTBridge.cocycle_fibre
#print axioms HRTBridge.measurable_zakRep
#print axioms HRTBridge.zakRep_ae
#print axioms HRTBridge.measurable_toTor
#print axioms HRTBridge.measurable_fibreG
#print axioms HRTBridge.measurable_symbolTor
#print axioms HRTBridge.measurable_fibreP
#print axioms HRTBridge.cocycle_norm_rep
#print axioms HRTBridge.cocycle_prod_rep
#print axioms HRTBridge.cocycle_fibre_rep
#print axioms HRTBridge.fourier_negOne_neg
#print axioms HRTBridge.chiT1_eq
#print axioms HRTBridge.chiM1_eq
#print axioms HRTBridge.symbolTor_eq
#print axioms HRTBridge.toTor_apply_zero
#print axioms HRTBridge.toTor_apply_one
#print axioms HRTBridge.fibreP_eq
#print axioms HRTBridge.continuous_fibreP
#print axioms HRTBridge.fourier_one_sub
#print axioms HRTBridge.norm_fourier_one
#print axioms HRTBridge.fibreP_quad
#print axioms HRTBridge.fibreP_ne_zero
#print axioms HRTBridge.fibreP_pos
#print axioms HRTBridge.ae_fibreP_ne_zero
#print axioms HRTBridge.integrable_log_fibreP
#print axioms HRTBridge.norm_zakCLM
#print axioms HRTBridge.norm_zakProd
#print axioms HRTBridge.coeFn_zakProd
#print axioms HRTBridge.measurable_fibreG_swap
#print axioms HRTBridge.not_ae_ae_fibreG_zero
#print axioms HRTBridge.exists_live_fibre_of_ae
#print axioms HRTBridge.ergodic_add_irrational
#print axioms HRTBridge.exists_fibre_mean
#print axioms HRTBridge.fibreP_nonneg
#print axioms HRTBridge.circle_integral_eq_interval_real
#print axioms HRTBridge.fibreP_eq_symbol
#print axioms HRTBridge.exists_fibre_symbol_mean
#print axioms HRTBridge.fourier_one_eq_exp_neg
#print axioms HRTBridge.noCircleRoot_of_fac
#print axioms HRTBridge.exists_rootCount_of_dependence_L2
#print axioms HRTBridge.fourier_one_coe
#print axioms HRTBridge.fibreP_eq_campaign
#print axioms HRTBridge.measurePreserving_sub_circle
#print axioms HRTBridge.mean_campaign_circle
#print axioms HRTBridge.mean_campaign_interval
#print axioms HRTBridge.injective_fourier_one
#print axioms HRTBridge.infinite_live_fibres
#print axioms HRTBridge.fibre_mean_of_good
#print axioms HRTBridge.finite_quadratic_roots
#print axioms HRTBridge.finite_badW
#print axioms HRTBridge.ae_noCircleRoot
#print axioms HRTBridge.exists_infinite_mean
#print axioms HRTBridge.coeFn_transL
#print axioms HRTBridge.coeFn_modCLM
#print axioms HRTBridge.coeFn_mod1CLM
#print axioms HRTBridge.modTransCLM_succ
#print axioms HRTBridge.zakCLM_dep_succ
#print axioms HRTBridge.cocycle_norm_succ
#print axioms HRTBridge.cocycle_norm_rep_of
#print axioms HRTBridge.cocycle_prod_rep_of
#print axioms HRTBridge.cocycle_fibre_rep_of
#print axioms HRTBridge.exists_infinite_mean_of
#print axioms HRTBridge.exists_infinite_mean_succ
#print axioms HRTBridge.sqrtTwo_sub_one_nonneg
#print axioms HRTBridge.sqrtTwo_sub_one_lt_one
#print axioms HRTBridge.irrational_sqrtTwo_sub_one
#print axioms HRTBridge.heil_speegle_lambda_zero_L2
#print axioms HRTBridge.heil_speegle_lambda_zero_L2_of_nd
#print axioms HRTBridge.no_lambdaZero_dependence_off_stratum
#print axioms HRTBridge.lambdaZero_dependence_forces_norm_eq
#print axioms HRTBridge.no_lambdaZero_dependence_of_ILR
#print axioms HRTBridge.heil_speegle_lambda_zero_L2_of_ILR
#print axioms HRTBridge.multLC_congr
#print axioms HRTBridge.multLC_one
#print axioms HRTBridge.multLC_multLC
#print axioms HRTBridge.modCLM_add
#print axioms HRTBridge.modCLM_zero
#print axioms HRTBridge.norm_chiMint
#print axioms HRTBridge.measurable_chiMint
#print axioms HRTBridge.chiMint_zero
#print axioms HRTBridge.chiMint_succ
#print axioms HRTBridge.chiMint_pred
#print axioms HRTBridge.multLC_inv_cancel
#print axioms HRTBridge.mod1CLM_eq_modCLM_one
#print axioms HRTBridge.chiM1_eq_chiMint
#print axioms HRTBridge.chiMint_negOne_mul
#print axioms HRTBridge.zakL2_modNegOne
#print axioms HRTBridge.zakL2_modInt
#print axioms HRTBridge.dep_Lp_j
#print axioms HRTBridge.cocycle_norm_j_succ
#print axioms HRTBridge.resonantFamily_lambdaZero
#print axioms HRTBridge.no_resonant_dependence_sqrt2_of_ILR
#print axioms HRTBridge.antidiagL_multLC
#print axioms HRTBridge.exists_zak_modTrans_nat
#print axioms HRTBridge.cocycle_norm_gen
#print axioms HRTBridge.irrational_fract
#print axioms HRTBridge.natFloor_add_fract
#print axioms HRTBridge.cocycle_norm_of_nonneg
#print axioms HRTBridge.no_resonant_dependence_of_ILR
#print axioms HRTBridge.exists_cocycle_eq_gen
#print axioms HRTBridge.norm_phase
#print axioms HRTBridge.cocycle_shift_eq
#print axioms HRTBridge.phase_eq_exp_arg
#print axioms HRTBridge.phase_mul
#print axioms HRTBridge.mem_slitPlane_of_re_pos
#print axioms HRTBridge.re_pos_of_norm_lt_one
#print axioms HRTBridge.norm_exp_neg_circle
#print axioms HRTBridge.outside_factor_re_pos
#print axioms HRTBridge.inside_factor_re_pos
#print axioms HRTBridge.outside_factor_eq
#print axioms HRTBridge.inside_factor_eq
#print axioms HRTBridge.two_pi_ne_zero_C
#print axioms HRTBridge.phase_exp_circle
#print axioms HRTBridge.exp_two_pi_I_one
#print axioms HRTBridge.exp_two_pi_I_zero
#print axioms HRTBridge.exists_lift_outside
#print axioms HRTBridge.exists_lift_inside
#print axioms HRTBridge.IsLoopLift.mul
#print axioms HRTBridge.windOf_add
#print axioms HRTBridge.exists_lift_char
#print axioms HRTBridge.exists_lift_quadratic
#print axioms HRTBridge.phase_of_norm_one
#print axioms HRTBridge.phase_neg
#print axioms HRTBridge.phase_ne_zero
#print axioms HRTBridge.conj_phase_mul
#print axioms HRTBridge.conj_mul_of_norm_one
#print axioms HRTBridge.phase_cocycle
#print axioms HRTBridge.norm_phase_cocycle_factor
#print axioms HRTBridge.transL_one_neg_cancel
#print axioms HRTBridge.measurable_conj_chiT1
#print axioms HRTBridge.norm_conj_chiT1
#print axioms HRTBridge.conj_chiT1_mul
#print axioms HRTBridge.zakL2_transNegOne
#print axioms HRTBridge.modTransCLM_pred
#print axioms HRTBridge.exists_zak_modTrans_int
#print axioms HRTBridge.cocycle_norm_int
#print axioms HRTBridge.cocycle_norm_of_real
#print axioms HRTBridge.no_resonant_dependence_of_ILR_real
#print axioms HRTBridge.rootCount_eq_of_ILR
#print axioms HRTBridge.fourier_add_arg
#print axioms HRTBridge.fourierCoeff_fourier_mul
#print axioms HRTBridge.fourierCoeff_comp_sub
#print axioms HRTBridge.norm_fourier_arg
#print axioms HRTBridge.norm_fourierCoeff_step
#print axioms HRTBridge.norm_fourierCoeff_prog
#print axioms HRTBridge.ILR_character
#print axioms HRTBridge.phase_exp_neg_circle
#print axioms HRTBridge.phase_fibre_symbol
#print axioms HRTBridge.exp_circle_sub_ne_zero
#print axioms HRTBridge.lambda0Translates_eq
#print axioms HRTBridge.lambda0Translates_linearIndependent_of_ILR
