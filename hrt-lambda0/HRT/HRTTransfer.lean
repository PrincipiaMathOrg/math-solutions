import Mathlib

/-!
# The transfer `L²(ℝ) → ℓ²(ℤ²)` for a rectangular lattice

`GroupVN.HRT.hrt_lattice` proves HRT on `ℓ²(ℤ²)`: the twisted group-algebra operator of the
lattice, at ANY real twist `θ`, is injective.  That is Linnell's algebraic core, and it is
unconditional.  What it does not do is talk about `L²(ℝ)`, which is where the HRT conjecture
actually lives.

This file builds the bridge, and it builds it CONCRETELY — no direct integrals, no von Neumann
algebras, no unbounded operators.  The whole content is one explicit map.

## The map

For `0 < θ ≤ 1` put

  `W g (j,k) = √θ · ∫₀¹ g(s+k) · e^{-2πi j θ s} ds`.

Two facts make it work.

* **It is an isometry onto its image.**  Fixing `k` and extending `s ↦ g(s+k)` by zero from
  `(0,1]` to `(0,1/θ]`, the numbers `W g (j,k)` are (a rescaling of) the Fourier coefficients of
  that extension on an interval of length `1/θ ≥ 1`.  Parseval on that interval gives
  `∑_j ‖W g (j,k)‖² = ∫₀¹ ‖g(s+k)‖² ds`, and summing over `k` reassembles `∫_ℝ ‖g‖²`.
  **This is exactly where `θ ≤ 1` is used**: for `θ > 1` the interval would be shorter than the
  support and the Fourier coefficients would lose information.

* **It intertwines the representations.**  With
  `π(m,n) g (t) = e^{2πi n θ t} g(t-m)` — the projective representation of the rectangular
  lattice `ℤ × θℤ` — one computes `W (π(m,n) g) (j,k) = e^{2πi θ n k} · W g (j-n, k-m)`, a
  twisted translate on `ℤ²`.  A diagonal unitary `e^{-2πi θ j k}` turns that into the twisted
  regular representation with cocycle `heisCocycle (-θ)`, which is the one
  `GroupVN.HRT.hrt_lattice` is stated for.

The covolume constraint `θ ≤ 1` costs nothing in applications: a configuration inside `aℤ × bℤ`
also sits inside `aℤ × (b/N)ℤ`, whose covolume is `ab/N`.
-/

set_option maxHeartbeats 1000000

namespace HRTTransfer

open Complex MeasureTheory

/-! ### The character `e(x) = e^{2πix}` -/

/-- `ee x = e^{2πix}`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

theorem ee_ne_zero (x : ℝ) : ee x ≠ 0 := Complex.exp_ne_zero _

/-! ### The representation and the transfer -/

/-- The projective representation of the rectangular lattice `ℤ × θℤ` on functions on `ℝ`:
`π(m,n) g (t) = e^{2πi n θ t} · g (t - m)`. -/
noncomputable def rep (θ : ℝ) (m n : ℤ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ee ((n : ℝ) * θ * t) * g (t - (m : ℝ))

/-- The transfer coefficients `W g (j,k) = √θ ∫₀¹ g(s+k) e^{-2πi j θ s} ds`. -/
noncomputable def W (θ : ℝ) (g : ℝ → ℂ) (j k : ℤ) : ℂ :=
  (Real.sqrt θ : ℂ) * ∫ s in (0:ℝ)..1, g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s))

/-- **The transfer intertwines.**  A time–frequency shift by the lattice point `(m,n)` becomes a
twisted translate of the coefficient array by `(n,m)`, with the phase `e^{2πi θ n k}`.

No hypotheses: this is an identity of integrals, true whether or not either side converges
(both sides are `0` on a non-integrable integrand). -/
theorem W_rep (θ : ℝ) (m n : ℤ) (g : ℝ → ℂ) (j k : ℤ) :
    W θ (rep θ m n g) j k = ee ((n : ℝ) * θ * (k : ℝ)) * W θ g (j - n) (k - m) := by
  unfold W
  have hpt : ∀ s : ℝ,
      rep θ m n g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s))
        = ee ((n : ℝ) * θ * (k : ℝ))
          * (g (s + ((k - m : ℤ) : ℝ)) * ee (-(((j - n : ℤ) : ℝ) * θ * s))) := by
    intro s
    unfold rep
    have harg : s + (k : ℝ) - (m : ℝ) = s + ((k - m : ℤ) : ℝ) := by push_cast; ring
    rw [harg]
    have hexp : ee ((n : ℝ) * θ * (s + (k : ℝ))) * ee (-((j : ℝ) * θ * s))
        = ee ((n : ℝ) * θ * (k : ℝ)) * ee (-(((j - n : ℤ) : ℝ) * θ * s)) := by
      rw [← ee_add, ← ee_add]
      congr 1
      push_cast
      ring
    calc ee ((n : ℝ) * θ * (s + (k : ℝ))) * g (s + ((k - m : ℤ) : ℝ)) * ee (-((j : ℝ) * θ * s))
        = (ee ((n : ℝ) * θ * (s + (k : ℝ))) * ee (-((j : ℝ) * θ * s)))
            * g (s + ((k - m : ℤ) : ℝ)) := by ring
      _ = ee ((n : ℝ) * θ * (k : ℝ))
            * (g (s + ((k - m : ℤ) : ℝ)) * ee (-(((j - n : ℤ) : ℝ) * θ * s))) := by
          rw [hexp]; ring
  rw [intervalIntegral.integral_congr (g := fun s =>
        ee ((n : ℝ) * θ * (k : ℝ))
          * (g (s + ((k - m : ℤ) : ℝ)) * ee (-(((j - n : ℤ) : ℝ) * θ * s))))
      (fun s _ => hpt s),
    intervalIntegral.integral_const_mul]
  ring

/-! ### Parseval on one slice

`W g (·,k)` is a rescaled Fourier coefficient sequence of the `k`-th unit slice of `g`, viewed on
the LONGER interval `(0, 1/θ]` and extended there by zero.  Parseval on that interval turns the
`ℓ²` norm of the `j`-sum into the `L²` norm of the slice — and this is the one and only place the
covolume constraint `θ ≤ 1` is used, since it is what makes `1/θ ≥ 1`. -/

section Parseval

open AddCircle

/-- The `k`-th unit slice of `g`, extended by zero past `1`. -/
noncomputable def slice (g : ℝ → ℂ) (k : ℤ) : ℝ → ℂ :=
  Set.indicator (Set.Iic (1 : ℝ)) (fun s => g (s + (k : ℝ)))

theorem slice_apply (g : ℝ → ℂ) (k : ℤ) (s : ℝ) :
    slice g k s = if s ≤ 1 then g (s + (k : ℝ)) else 0 := by
  simp only [slice, Set.indicator_apply, Set.mem_Iic]

theorem norm_slice_le (g : ℝ → ℂ) (k : ℤ) (s : ℝ) : ‖slice g k s‖ ≤ ‖g (s + (k : ℝ))‖ := by
  rw [slice_apply]
  split_ifs with h
  · exact le_refl _
  · simpa using norm_nonneg (g (s + (k : ℝ)))

theorem memLp_shift {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) (k : ℤ) :
    MemLp (fun s : ℝ => g (s + (k : ℝ))) 2 (volume : Measure ℝ) :=
  hg.comp_measurePreserving (measurePreserving_add_right volume (k : ℝ))

theorem memLp_slice {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) (k : ℤ) :
    MemLp (slice g k) 2 (volume : Measure ℝ) :=
  MemLp.indicator measurableSet_Iic (memLp_shift hg k)

/-- The character appearing in `fourierCoeffOn` on an interval of length `T` is `ee`. -/
theorem fourier_coe_eq_ee {T : ℝ} (j : ℤ) (x : ℝ) :
    (fourier (-j) ((x : ℝ) : AddCircle T) : ℂ) = ee (-((j : ℝ) * (x / T))) := by
  rw [fourier_coe_apply]
  unfold ee
  congr 1
  push_cast
  ring

/-- **The transfer coefficients ARE Fourier coefficients.**

Note the interval length is kept in the unreduced form `1/θ - 0` throughout: `simp only [sub_zero]`
would leave the `AddCircle (1/θ - 0)` TYPE index untouched (a dependent position), so the reduced
statement would no longer match the goal. -/
theorem fourierCoeffOn_slice {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hlt : (0 : ℝ) < 1 / θ)
    (g : ℝ → ℂ) (j k : ℤ) :
    fourierCoeffOn hlt (slice g k) j
      = (θ : ℂ) * ∫ x in (0:ℝ)..1, g (x + (k : ℝ)) * ee (-((j : ℝ) * θ * x)) := by
  have hle : (1 : ℝ) ≤ 1 / θ := by
    rw [le_div_iff₀ hθ0]; linarith
  have h0 : (0 : ℝ) ≤ 1 / θ := by positivity
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  rw [fourierCoeffOn_eq_integral]
  have hInt : ∀ x : ℝ,
      (fourier (-j) ((x : ℝ) : AddCircle (1 / θ - 0)) : ℂ) • slice g k x
        = (Set.Iic (1 : ℝ)).indicator
            (fun s : ℝ => g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s))) x := by
    intro x
    rw [slice, Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ Set.Iic (1 : ℝ)
    · rw [if_pos hx, if_pos hx, smul_eq_mul, fourier_coe_eq_ee j x]
      have harg : -((j : ℝ) * (x / (1 / θ - 0))) = -((j : ℝ) * θ * x) := by
        field_simp
        ring
      rw [harg]
      ring
    · rw [if_neg hx, if_neg hx, smul_zero]
  rw [intervalIntegral.integral_congr (fun x _ => hInt x),
    intervalIntegral.integral_of_le h0,
    MeasureTheory.setIntegral_indicator measurableSet_Iic]
  have hIset : Set.Ioc (0 : ℝ) (1 / θ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hle⟩, h2⟩
  rw [hIset, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), sub_zero,
    one_div_one_div, Complex.real_smul]

/-- `W` is the Fourier coefficient divided by `√θ`. -/
theorem W_eq_fourierCoeffOn {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hlt : (0 : ℝ) < 1 / θ)
    (g : ℝ → ℂ) (j k : ℤ) :
    W θ g j k = ((Real.sqrt θ : ℝ) : ℂ)⁻¹ * fourierCoeffOn hlt (slice g k) j := by
  rw [fourierCoeffOn_slice hθ0 hθ1 hlt, W]
  set Iv : ℂ := ∫ s in (0:ℝ)..1, g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s)) with hIvdef
  have hsC : ((Real.sqrt θ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hcast : ((Real.sqrt θ : ℝ) : ℂ) * ((Real.sqrt θ : ℝ) : ℂ) = (θ : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt hθ0.le
  rw [← hcast]
  field_simp

/-- **Parseval for one slice.** -/
theorem hasSum_sq_W {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (k : ℤ) :
    HasSum (fun j : ℤ => ‖W θ g j k‖ ^ 2) (∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2) := by
  have hlt : (0 : ℝ) < 1 / θ := by positivity
  have hle : (1 : ℝ) ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hL2 : MemLp (slice g k) 2 (volume.restrict (Set.Ioc (0:ℝ) (1/θ))) :=
    (memLp_slice hg k).restrict _
  have hP := hasSum_sq_fourierCoeffOn hlt hL2
  -- the right-hand side collapses to the unit-interval integral
  have hRHS : ∫ x in (0:ℝ)..(1/θ), ‖slice g k x‖ ^ 2
      = ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2 := by
    have hpt : ∀ x : ℝ, ‖slice g k x‖ ^ 2
        = (Set.Iic (1 : ℝ)).indicator (fun s : ℝ => ‖g (s + (k : ℝ))‖ ^ 2) x := by
      intro x
      rw [slice, Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Iic (1 : ℝ)
      · rw [if_pos hx, if_pos hx]
      · rw [if_neg hx, if_neg hx, norm_zero]
        norm_num
    rw [intervalIntegral.integral_congr (g := fun x =>
          (Set.Iic (1 : ℝ)).indicator (fun s : ℝ => ‖g (s + (k : ℝ))‖ ^ 2) x) (fun x _ => hpt x),
      intervalIntegral.integral_of_le hlt.le,
      MeasureTheory.setIntegral_indicator measurableSet_Iic]
    have hIset : Set.Ioc (0 : ℝ) (1 / θ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_trans h.2 hle⟩, h.2⟩⟩
    rw [hIset, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [sub_zero, hRHS] at hP
  have hdiv := hP.div_const θ
  have hval : (1 / θ)⁻¹ • (∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2) / θ
      = ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2 := by
    rw [smul_eq_mul]
    field_simp
  rw [hval] at hdiv
  have hfun : (fun j : ℤ => ‖W θ g j k‖ ^ 2)
      = fun j : ℤ => ‖fourierCoeffOn hlt (slice g k) j‖ ^ 2 / θ := by
    funext j
    rw [W_eq_fourierCoeffOn hθ0 hθ1 hlt, norm_mul, mul_pow, norm_inv]
    have h1 : ‖((Real.sqrt θ : ℝ) : ℂ)‖ = Real.sqrt θ := by
      simp [abs_of_nonneg (Real.sqrt_nonneg θ)]
    rw [h1, inv_pow, Real.sq_sqrt hθ0.le]
    ring
  rw [hfun]
  exact hdiv

/-! ### Summing over the slices

The unit-slice energies of an `L²` function are exactly the pieces of `∫_ℝ ‖g‖²` cut out by the
partition `ℝ = ⨆_k (k, k+1]`. -/

/-- **The slice energies sum to the total energy.** -/
theorem hasSum_slice_sq {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    HasSum (fun k : ℤ => ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2) (∫ x, ‖g x‖ ^ 2) := by
  have hint : Integrable (fun x => ‖g x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hcover : (⋃ k : ℤ, Set.Ioc (k : ℝ) ((k : ℝ) + 1)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
    refine ⟨⌈x⌉ - 1, ?_, ?_⟩
    · push_cast
      have h := Int.ceil_lt_add_one x
      linarith
    · push_cast
      have h := Int.le_ceil x
      linarith
  have hm : ∀ k : ℤ, MeasurableSet (Set.Ioc (k : ℝ) ((k : ℝ) + 1)) := fun _ => measurableSet_Ioc
  have hd : Pairwise (Function.onFun Disjoint fun k : ℤ => Set.Ioc (k : ℝ) ((k : ℝ) + 1)) := by
    intro a b hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_Ioc]
    rintro x ⟨hxa, hxa'⟩ ⟨hxb, hxb'⟩
    have h1 : (a : ℝ) < (b : ℝ) + 1 := lt_of_lt_of_le hxa hxb'
    have h2 : (b : ℝ) < (a : ℝ) + 1 := lt_of_lt_of_le hxb hxa'
    have h1' : a < b + 1 := by exact_mod_cast h1
    have h2' : b < a + 1 := by exact_mod_cast h2
    exact hab (by omega)
  have hfi : IntegrableOn (fun x => ‖g x‖ ^ 2)
      (⋃ k : ℤ, Set.Ioc (k : ℝ) ((k : ℝ) + 1)) volume := by
    rw [hcover]
    exact hint.integrableOn
  have hS := hasSum_integral_iUnion hm hd hfi
  rw [hcover, MeasureTheory.setIntegral_univ] at hS
  have hshift : ∀ k : ℤ, ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2
      = ∫ x in Set.Ioc (k : ℝ) ((k : ℝ) + 1), ‖g x‖ ^ 2 := by
    intro k
    have hpre : (fun x : ℝ => x + (k : ℝ)) ⁻¹' Set.Ioc (k : ℝ) ((k : ℝ) + 1)
        = Set.Ioc (0 : ℝ) 1 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    have := (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ)).setIntegral_preimage_emb
      (measurableEmbedding_addRight (k : ℝ)) (fun x => ‖g x‖ ^ 2)
      (Set.Ioc (k : ℝ) ((k : ℝ) + 1))
    rw [hpre] at this
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact this
  have hfun : (fun k : ℤ => ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2)
      = fun k : ℤ => ∫ x in Set.Ioc (k : ℝ) ((k : ℝ) + 1), ‖g x‖ ^ 2 := funext hshift
  rw [hfun]
  exact hS

/-! ### The array is square-summable, and `W` loses nothing -/

/-- **The whole coefficient array is square-summable**, with total mass `∫_ℝ ‖g‖²`. -/
theorem summable_W_sq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    Summable (fun p : ℤ × ℤ => ‖W θ g p.2 p.1‖ ^ 2) := by
  refine (summable_prod_of_nonneg ?_).mpr ⟨?_, ?_⟩
  · intro p
    positivity
  · intro k
    exact (hasSum_sq_W hθ0 hθ1 hg k).summable
  · have hfun : (fun k : ℤ => ∑' j : ℤ, ‖W θ g j k‖ ^ 2)
        = fun k : ℤ => ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2 :=
      funext fun k => (hasSum_sq_W hθ0 hθ1 hg k).tsum_eq
    rw [hfun]
    exact (hasSum_slice_sq hg).summable

/-- **`W` is injective.**  A window whose whole coefficient array vanishes is a.e. zero.

This is Parseval read backwards: each slice has zero energy, so the total energy is zero. -/
theorem ae_eq_zero_of_W_eq_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (h : ∀ j k : ℤ, W θ g j k = 0) :
    g =ᵐ[volume] 0 := by
  have hint : Integrable (fun x => ‖g x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hz : ∀ k : ℤ, (∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2) = 0 := by
    intro k
    have hk := hasSum_sq_W hθ0 hθ1 hg k
    have hzero : (fun j : ℤ => ‖W θ g j k‖ ^ 2) = fun _ : ℤ => (0 : ℝ) := by
      funext j
      rw [h j k, norm_zero]
      norm_num
    rw [hzero] at hk
    exact (hasSum_zero.unique hk).symm
  have htot := hasSum_slice_sq hg
  have hfun : (fun k : ℤ => ∫ x in (0:ℝ)..1, ‖g (x + (k : ℝ))‖ ^ 2) = fun _ : ℤ => (0 : ℝ) :=
    funext hz
  rw [hfun] at htot
  have htotal : (∫ x, ‖g x‖ ^ 2) = 0 := (hasSum_zero.unique htot).symm
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp htotal
  filter_upwards [hae] with x hx
  have : ‖g x‖ ^ 2 = 0 := hx
  have hnx : ‖g x‖ = 0 := by
    nlinarith [norm_nonneg (g x)]
  simpa using hnx

end Parseval

end HRTTransfer

/-! ## Acceptance gate -/

#print axioms HRTTransfer.ee_add
#print axioms HRTTransfer.norm_ee
#print axioms HRTTransfer.W_rep
#print axioms HRTTransfer.memLp_slice
#print axioms HRTTransfer.fourierCoeffOn_slice
#print axioms HRTTransfer.W_eq_fourierCoeffOn
#print axioms HRTTransfer.hasSum_sq_W
#print axioms HRTTransfer.hasSum_slice_sq
#print axioms HRTTransfer.summable_W_sq
#print axioms HRTTransfer.ae_eq_zero_of_W_eq_zero
