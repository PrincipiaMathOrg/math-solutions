import Mathlib

/-!
# Toward the Zak transform — periodization over a fundamental domain

The Zak transform `Zg(t,ω) = Σ_n g(t-n) e^{2πinω}` is the analytic engine of the HRT
argument, and is **not in Mathlib** (verified 2026-07-28: no formalisation found anywhere).
Discharging the `hreduction` hypothesis of `HRTResonantFibre.heil_speegle_lambda_zero`
requires building it, per the owner's standing no-hypotheses rule.

Unitarity `L²(ℝ) → L²([0,1)²)` factors as:
  (a) **periodization**: `∫_ℝ |g|² = Σ_n ∫_{(0,1]} |g(n + t)|² dt`   ← THIS FILE
  (b) fibrewise Parseval: `∫_0^1 |Zg(t,ω)|² dω = Σ_n |g(t - n)|²`     (Mathlib `fourierBasis`)
  (c) Tonelli to combine.

Step (a) is proved here from Mathlib's `isAddFundamentalDomain_Ioc` (the interval `(0,1]` is a
fundamental domain for the `ℤ`-action on `ℝ`) and `IsAddFundamentalDomain.lintegral_eq_tsum''`.
-/

set_option maxHeartbeats 1000000

namespace ZakPeriodization

open MeasureTheory Set AddCircle
open scoped ENNReal NNReal

/-- `(0, 1]` is a fundamental domain for the action of `ℤ` (as `zmultiples 1`) on `ℝ`. -/
theorem isAddFundamentalDomain_Ioc_zero_one :
    IsAddFundamentalDomain (AddSubgroup.zmultiples (1 : ℝ)) (Ioc (0 : ℝ) 1) volume := by
  have h := isAddFundamentalDomain_Ioc (T := (1 : ℝ)) one_pos 0
  rwa [zero_add] at h

/-- **Periodization.**  The `L²` mass of `g` over `ℝ` is the sum of the masses of its integer
translates over the fundamental domain `(0,1]`.  This is step (a) of Zak unitarity. -/
theorem lintegral_sq_eq_tsum (g : ℝ → ℂ) :
    ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2
      = ∑' n : AddSubgroup.zmultiples (1 : ℝ),
          ∫⁻ t in Ioc (0 : ℝ) 1, (‖g ((n : ℝ) + t)‖₊ : ℝ≥0∞) ^ 2 :=
  isAddFundamentalDomain_Ioc_zero_one.lintegral_eq_tsum'' _

/-! ### Step (b): fibrewise Parseval

Rather than define `Z g (t, ·)` by its series and then *prove* Parseval, we define the fibre as
the image of the sample sequence `n ↦ g (t - n)` under the inverse Fourier isometry
`fourierBasis.repr.symm`.  Parseval is then structural: it is exactly the statement that a
`LinearIsometryEquiv` preserves norms. -/

section Parseval

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The `L²(𝕋)` element whose `n`-th Fourier coefficient is `v n`. -/
noncomputable def ofCoeffs (v : lp (fun _ : ℤ => ℂ) 2) :
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  (fourierBasis (T := 1)).repr.symm v

/-- **Step (b), fibrewise Parseval.**  The `L²` norm of a fibre equals the `ℓ²` norm of its
Fourier coefficients. -/
theorem norm_sq_ofCoeffs (v : lp (fun _ : ℤ => ℂ) 2) :
    ‖ofCoeffs v‖ ^ (2 : ℝ) = ∑' n : ℤ, ‖v n‖ ^ (2 : ℝ) := by
  rw [ofCoeffs, LinearIsometryEquiv.norm_map]
  exact lp.norm_rpow_eq_tsum (by norm_num) v

/-- The fibre built from a coefficient sequence has exactly those Fourier coefficients. -/
theorem fourierCoeff_ofCoeffs (v : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    fourierCoeff ((ofCoeffs v : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
      AddCircle (1 : ℝ) → ℂ) n = v n := by
  have h := fourierBasis_repr (T := 1) (ofCoeffs v) n
  rw [ofCoeffs, LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- **Injectivity.**  `ofCoeffs` is injective — it is a linear isometry equivalence. -/
theorem ofCoeffs_injective : Function.Injective ofCoeffs := by
  intro v w h
  exact (fourierBasis (T := 1)).repr.symm.injective h

/-- A vanishing fibre has vanishing coefficients. -/
theorem eq_zero_of_ofCoeffs_eq_zero {v : lp (fun _ : ℤ => ℂ) 2} (h : ofCoeffs v = 0) :
    ∀ n : ℤ, v n = 0 := by
  intro n
  have : v = 0 := ofCoeffs_injective (by simpa [ofCoeffs] using h)
  simp [this]

end Parseval

/-! ### Step (c): Tonelli join

Combining (a) and (c) gives the `lintegral`-level Zak isometry: the `L²` mass of `g` over `ℝ`
is the integral over the fundamental domain of the fibrewise `ℓ²` mass — which by (b) is the
`L²(𝕋)` mass of the Zak fibre. -/

section Tonelli

/-- **Zak isometry at the `lintegral` level.**  `∫_ℝ |g|² = ∫_{(0,1]} Σ_n |g(n+t)|² dt`. -/
theorem lintegral_sq_eq_setLIntegral_tsum {g : ℝ → ℂ} (hg : Measurable g) :
    ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ t in Ioc (0 : ℝ) 1,
          ∑' n : AddSubgroup.zmultiples (1 : ℝ), (‖g ((n : ℝ) + t)‖₊ : ℝ≥0∞) ^ 2 := by
  rw [lintegral_sq_eq_tsum g]
  refine (lintegral_tsum ?_).symm
  intro n
  exact ((hg.comp (measurable_const_add _)).nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable

/-- **A nonzero window has a live fibre.**  If `g` carries positive `L²` mass then the fibrewise
mass cannot vanish almost everywhere on the fundamental domain.

This is the step that produces the positive-measure set of live fibres — the `L.Infinite`
input to `HRTResonant.live_set_not_infinite`. -/
theorem not_ae_fibre_zero_of_lintegral_ne_zero {g : ℝ → ℂ} (hg : Measurable g)
    (hne : ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ≠ 0) :
    ¬ (∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        (∑' n : AddSubgroup.zmultiples (1 : ℝ), (‖g ((n : ℝ) + t)‖₊ : ℝ≥0∞) ^ 2) = 0) := by
  intro hae
  apply hne
  rw [lintegral_sq_eq_setLIntegral_tsum hg]
  calc ∫⁻ t in Ioc (0 : ℝ) 1,
        (∑' n : AddSubgroup.zmultiples (1 : ℝ), (‖g ((n : ℝ) + t)‖₊ : ℝ≥0∞) ^ 2)
      = ∫⁻ _t in Ioc (0 : ℝ) 1, (0 : ℝ≥0∞) := lintegral_congr_ae hae
    _ = 0 := lintegral_zero

end Tonelli

/-! ## The Zak transform itself: quasi-periodicity and covariance

`Z g (t, ω) = Σ_{n ∈ ℤ} g (t - n) e^{2πinω}`.

The two structural identities the HRT argument runs on are purely formal reindexings of this
series — they need no analysis, only `Equiv.tsum_eq`.  They are what turn a linear dependence
among time–frequency translates into the fibre functional equation. -/

section ZakDef

open Complex Real

/-- The Zak transform. -/
noncomputable def zak (g : ℝ → ℂ) (t ω : ℝ) : ℂ :=
  ∑' n : ℤ, g (t - n) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))

/-- `Z g` is `1`-periodic in the frequency variable. -/
theorem zak_periodic_snd (g : ℝ → ℂ) (t ω : ℝ) : zak g t (ω + 1) = zak g t ω := by
  unfold zak
  refine tsum_congr fun n => ?_
  congr 1
  have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((ω : ℂ) + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)
        + (n : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [show (((ω + 1 : ℝ)) : ℂ) = (ω : ℂ) + 1 by push_cast; ring, this, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Quasi-periodicity in time**: `Z g (t + 1, ω) = e^{2πiω} Z g (t, ω)`. -/
theorem zak_quasi_periodic_fst (g : ℝ → ℂ) (t ω : ℝ) :
    zak g (t + 1) ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * zak g t ω := by
  unfold zak
  rw [← tsum_mul_left,
    ← (Equiv.addRight (1 : ℤ)).tsum_eq
      (fun n : ℤ => g (t + 1 - (n : ℝ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)))]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addRight]
  have hg : (t + 1 - (((n + 1 : ℤ)) : ℝ)) = t - ((n : ℤ) : ℝ) := by push_cast; ring
  rw [hg]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n + 1 : ℤ)) : ℂ) * (ω : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (ω : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hexp]
  ring

/-- **Zak covariance.**  `Z (M_b T_x g) (t, ω) = e^{2πibt} · Z g (t - x, ω - b)`.

This is the identity that converts a linear dependence among time–frequency translates into the
fibre functional equation.  Note it is termwise — no reindexing is needed. -/
theorem zak_covariance (g : ℝ → ℂ) (b x t ω : ℝ) :
    zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ)) * g (y - x)) t ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (t : ℂ)) * zak g (t - x) (ω - b) := by
  unfold zak
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  dsimp only
  have harg : (t - ((n : ℤ) : ℝ) - x) = (t - x - ((n : ℤ) : ℝ)) := by ring
  rw [harg]
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (((t - ((n : ℤ) : ℝ)) : ℝ) : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (ω : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (t : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (((ω - b) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (g (t - x - ((n : ℤ) : ℝ))) * hexp

/-- **Integer quasi-periodicity in the FIRST variable.**  The `+1` version iterated over `ℤ`.
This is what turns an integer TIME shift into multiplication by a character. -/
theorem zak_quasi_periodic_fst_int (g : ℝ → ℂ) (t ω : ℝ) (j : ℤ) :
    zak g (t + (j : ℝ)) ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (ω : ℂ)) * zak g t ω := by
  have hstep : ∀ s : ℝ, zak g (s + 1) ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * zak g s ω :=
    fun s => zak_quasi_periodic_fst g s ω
  induction j using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have harg : t + (((k : ℤ) + 1 : ℤ) : ℝ) = (t + ((k : ℤ) : ℝ)) + 1 := by push_cast; ring
      rw [harg, hstep, ih, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  | pred k ih =>
      have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      have harg : (t + ((-(k : ℤ) - 1 : ℤ) : ℝ)) + 1 = t + ((-(k : ℤ) : ℤ) : ℝ) := by
        push_cast; ring
      have h := hstep (t + ((-(k : ℤ) - 1 : ℤ) : ℝ))
      rw [harg, ih] at h
      apply mul_left_cancel₀ hne
      rw [← h, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- `Z g` is periodic in the frequency variable under every INTEGER shift.  This is what makes
the `j` in the resonant configuration `(a, a + j)` drop out of the fibre equation. -/
theorem zak_periodic_snd_int (g : ℝ → ℂ) (t ω : ℝ) (j : ℤ) :
    zak g t (ω + (j : ℝ)) = zak g t ω := by
  unfold zak
  refine tsum_congr fun n => ?_
  congr 1
  have hsplit : (2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (((ω + (j : ℝ)) : ℝ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (ω : ℂ)
        + ((n * j : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **AN INTEGER TIME–FREQUENCY SHIFT BECOMES MULTIPLICATION BY A CHARACTER.**

`Z (M_n T_m g)(t,ω) = e^{2πi(nt − mω)} · Z g(t,ω)` for `m n : ℤ`.

This is the fact that makes HRT over the integer lattice a statement about trigonometric
polynomials: every translate in a lattice dependence becomes the SAME function `Zg` times a
character, so the dependence collapses to `P · Zg = 0`. -/
theorem zak_intShift (g : ℝ → ℂ) (m n : ℤ) (t ω : ℝ) :
    zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) * (y : ℂ))
        * g (y - (m : ℝ))) t ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * (((n : ℂ) * (t : ℂ)) - ((m : ℂ) * (ω : ℂ)))) * zak g t ω := by
  rw [zak_covariance g (n : ℝ) (m : ℝ) t ω]
  have hsnd : zak g (t - (m : ℝ)) (ω - (n : ℝ)) = zak g (t - (m : ℝ)) ω := by
    have h := zak_periodic_snd_int g (t - (m : ℝ)) ω (-n)
    rw [show ω + ((-n : ℤ) : ℝ) = ω - (n : ℝ) by push_cast; ring] at h
    exact h
  have hfst : zak g (t - (m : ℝ)) ω
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (ω : ℂ))) * zak g t ω := by
    have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (ω : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have h := zak_quasi_periodic_fst_int g (t - (m : ℝ)) ω m
    rw [show t - (m : ℝ) + ((m : ℤ) : ℝ) = t by push_cast; ring] at h
    apply mul_left_cancel₀ hne
    rw [h, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [hsnd, hfst, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `Z (T_1 g) (t, ω) = e^{-2πiω} · Z g (t, ω)`: the unit time-shift acts by a character. -/
theorem zak_timeShift_one (g : ℝ → ℂ) (t ω : ℝ) :
    zak (fun y => g (y - 1)) t ω
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ))) * zak g t ω := by
  have h0 : zak (fun y => g (y - 1)) t ω = zak g (t - 1) ω := by
    unfold zak
    refine tsum_congr fun n => ?_
    dsimp only
    have harg : (t - ((n : ℤ) : ℝ)) - 1 = (t - 1) - ((n : ℤ) : ℝ) := by ring
    rw [harg]
  have h1 : zak g ((t - 1) + 1) ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) * zak g (t - 1) ω :=
    zak_quasi_periodic_fst g (t - 1) ω
  rw [sub_add_cancel] at h1
  rw [h0, h1, ← mul_assoc, ← Complex.exp_add]
  simp

/-- `Z (M_1 g) (t, ω) = e^{2πit} · Z g (t, ω)`: the unit modulation acts by a character. -/
theorem zak_modulate_one (g : ℝ → ℂ) (t ω : ℝ) :
    zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) * zak g t ω := by
  have hfun : (fun y : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      = fun y : ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * (y : ℂ)) * g (y - 0) := by
    funext y; push_cast; ring_nf
  rw [hfun, zak_covariance g 1 0 t ω]
  have : zak g (t - 0) (ω - 1) = zak g t ω := by
    rw [sub_zero]
    have h := zak_periodic_snd_int g t (ω - 1) 1
    push_cast at h
    rw [sub_add_cancel] at h
    exact h.symm
  rw [this]
  push_cast
  ring_nf

/-- **The resonant translate.**  `Z (M_{a+j} T_a g) (t, ω) = e^{2πi(a+j)t} · Z g (t - a, ω - a)`.

The `j` disappears from the SECOND argument because `Z g` is periodic under integer frequency
shifts — this is exactly why the fourth point must have the form `(a, a + j)` with `j ∈ ℤ`, and
why the whole family fibres over `θ = ω - t`. -/
theorem zak_modulate_timeShift (g : ℝ → ℂ) (a b : ℝ) (j : ℤ) (hb : b = a + (j : ℝ))
    (t ω : ℝ) :
    zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
          * g (y - a)) t ω
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (t : ℂ))
          * zak g (t - a) (ω - a) := by
  rw [zak_covariance g b a t ω]
  congr 1
  have hshift : ω - b = (ω - a) - (j : ℝ) := by rw [hb]; ring
  rw [hshift]
  have h := zak_periodic_snd_int g (t - a) ((ω - a) - (j : ℝ)) j
  rw [sub_add_cancel] at h
  exact h.symm

/-! ### Linearity primitives

`zak` is homogeneous with no hypothesis at all (`tsum_mul_left` holds unconditionally in a
complete space, returning `0` on both sides when the family is not summable); additivity needs
summability of the two families, as usual for `tsum`. -/

/-- `Z` is homogeneous. -/
theorem zak_smul (g : ℝ → ℂ) (c : ℂ) (t ω : ℝ) :
    zak (fun y => c * g y) t ω = c * zak g t ω := by
  unfold zak
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by dsimp only; ring

/-- `Z` is additive on summable families. -/
theorem zak_add (g₁ g₂ : ℝ → ℂ) (t ω : ℝ)
    (h₁ : Summable fun n : ℤ =>
      g₁ (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)))
    (h₂ : Summable fun n : ℤ =>
      g₂ (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) :
    zak (fun y => g₁ y + g₂ y) t ω = zak g₁ t ω + zak g₂ t ω := by
  unfold zak
  rw [← Summable.tsum_add h₁ h₂]
  exact tsum_congr fun n => by dsimp only; ring

/-! ### The fibre functional equation

This is the payoff of the covariance identities.  The *algebraic* content — substituting the
three translate identities and collecting — is proved here outright.  The one analytic input is
that `Z` is linear and annihilates the dependence, which is hypothesis `hz`; the `L²` Zak
transform supplies exactly that, and stating it this way keeps the algebra independent of the
construction of that transform. -/

/-- **The fibre functional equation.**  From a linear dependence among the four resonant
time–frequency translates, `Z g` satisfies

  `p(t,ω) · Z g (t,ω) = −D e^{2πibt} · Z g (t−a, ω−a)`,  `p(t,ω) = A + B e^{−2πiω} + C e^{2πit}`.

The right-hand side moves `(t,ω)` by `(−a,−a)`, which preserves `θ = ω − t` — this is the
resonance that fibres the torus into invariant circles. -/
theorem zak_fibre_equation (g : ℝ → ℂ) (A B C D : ℂ) (a b : ℝ) (j : ℤ)
    (hb : b = a + (j : ℝ)) (t ω : ℝ)
    (hz : A * zak g t ω
        + B * zak (fun y => g (y - 1)) t ω
        + C * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t ω
        + D * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
              * g (y - a)) t ω = 0) :
    (A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)))
        + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) * zak g t ω
      = -(D * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (t : ℂ))
            * zak g (t - a) (ω - a)) := by
  rw [zak_timeShift_one, zak_modulate_one, zak_modulate_timeShift g a b j hb] at hz
  linear_combination hz

/-! ### The resonant fibration

The shift `(t,ω) ↦ (t−a, ω−a)` on the right-hand side of the fibre equation preserves
`θ = ω − t`.  Restricting to the invariant circle `ω = t + θ` turns the two-variable functional
equation into a ONE-variable equation on each fibre, driven by the rotation `t ↦ t − a`.  That
one-variable equation is exactly the input to `HRTResonantFibre`. -/

/-- The resonance: the shift preserves `θ = ω − t`. -/
theorem resonant_shift_preserves_theta (a t ω : ℝ) : (ω - a) - (t - a) = ω - t := by ring

/-- The fibre of `Z g` over `θ`. -/
noncomputable def zakFibre (g : ℝ → ℂ) (θ t : ℝ) : ℂ := zak g t (t + θ)

/-- The symbol `P_θ(t) = A + B e^{−2πi(t+θ)} + C e^{2πit}`. -/
noncomputable def symbol (A B C : ℂ) (θ t : ℝ) : ℂ :=
  A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))
    + C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-- **The one-variable fibre equation.**  `P_θ(t) · G_θ(t) = −D e^{2πibt} · G_θ(t − a)`.

This is the equation `HRTResonantFibre` consumes: taking absolute values gives the modulus
cocycle whose zero set is rotation-invariant (the dichotomy), and taking logarithms gives the
coboundary whose mean vanishes (`integral_eq_zero_of_coboundary`). -/
theorem zakFibre_equation (g : ℝ → ℂ) (A B C D : ℂ) (a b : ℝ) (j : ℤ)
    (hb : b = a + (j : ℝ)) (θ t : ℝ)
    (hz : A * zak g t (t + θ)
        + B * zak (fun y => g (y - 1)) t (t + θ)
        + C * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t (t + θ)
        + D * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
              * g (y - a)) t (t + θ) = 0) :
    symbol A B C θ t * zakFibre g θ t
      = -(D * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (t : ℂ))
            * zakFibre g θ (t - a)) := by
  have h := zak_fibre_equation g A B C D a b j hb t (t + θ) hz
  unfold symbol zakFibre
  have harg : (t - a) + θ = (t + θ) - a := by ring
  rw [harg]
  exact h

/-! ### The modulus cocycle

Two facts let the fibre equation descend to the circle and feed `HRTResonantFibre`:
the modulus `|G_θ|` is genuinely `1`-periodic (the quasi-periodic phase drops out), and it
satisfies a multiplicative cocycle relation over the rotation `t ↦ t − a`. -/

/-- `|G_θ|` is `1`-periodic — the quasi-periodic phase has modulus one. -/
theorem norm_zakFibre_periodic (g : ℝ → ℂ) (θ t : ℝ) :
    ‖zakFibre g θ (t + 1)‖ = ‖zakFibre g θ t‖ := by
  unfold zakFibre
  have h1 : zak g (t + 1) ((t + 1) + θ)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((t + 1) + θ : ℝ) : ℂ))
        * zak g t ((t + 1) + θ) := zak_quasi_periodic_fst g t ((t + 1) + θ)
  have h2 : zak g t ((t + 1) + θ) = zak g t (t + θ) := by
    have h := zak_periodic_snd_int g t (t + θ) 1
    push_cast at h
    rw [show (t + 1) + θ = (t + θ) + 1 by ring]
    exact h
  rw [h1, h2, norm_mul, Complex.norm_exp]
  simp

/-- **The modulus cocycle.**  `|G_θ(t − a)| = |D|⁻¹ · |P_θ(t)| · |G_θ(t)|`.

This is precisely the shape `ae_eq_zero_or_ae_ne_zero_of_ergodic` consumes (with the rotation
`t ↦ t − a` and weight `−D⁻¹ e^{2πibt} P_θ(t)`), and its logarithm is the coboundary consumed by
`integral_eq_zero_of_coboundary`. -/
theorem zakFibre_modulus (g : ℝ → ℂ) (A B C D : ℂ) (a b : ℝ) (hD : D ≠ 0) (θ t : ℝ)
    (heq : symbol A B C θ t * zakFibre g θ t
      = -(D * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (t : ℂ))
            * zakFibre g θ (t - a))) :
    ‖symbol A B C θ t‖ * ‖zakFibre g θ t‖ = ‖D‖ * ‖zakFibre g θ (t - a)‖ := by
  have h := congrArg norm heq
  rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_exp] at h
  simpa using h

/-! ### Discharging `hz` from summability alone

`hz` — that `Z` annihilates the dependence — does NOT require the `L²` unitary.  It follows from
linearity plus summability of the four translate families, since the dependence says the
underlying function is identically `0` and `Z 0 = 0`. -/

/-- `Z 0 = 0`. -/
theorem zak_zero (t ω : ℝ) : zak (fun _ => (0 : ℂ)) t ω = 0 := by
  unfold zak; simp

/-- **`hz` from summability.**  Given the pointwise dependence and summability of the four
translate families at `(t, ω)`, the Zak transform annihilates the dependence. -/
theorem zak_dep_zero (g : ℝ → ℂ) (A B C D : ℂ) (a b : ℝ) (t ω : ℝ)
    (hdep : ∀ y : ℝ, A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ)) * g (y - a)) = 0)
    (s1 : Summable fun n : ℤ => A * g (t - (n : ℝ))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)))
    (s2 : Summable fun n : ℤ => B * g (t - (n : ℝ) - 1)
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)))
    (s3 : Summable fun n : ℤ => C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((t - (n : ℝ) : ℝ) : ℂ)) * g (t - (n : ℝ)))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)))
    (s4 : Summable fun n : ℤ => D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)
        * ((t - (n : ℝ) : ℝ) : ℂ)) * g (t - (n : ℝ) - a))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ))) :
    A * zak g t ω
      + B * zak (fun y => g (y - 1)) t ω
      + C * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t ω
      + D * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
            * g (y - a)) t ω = 0 := by
  have hzero : zak (fun y : ℝ => A * g y + B * g (y - 1)
      + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
      + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
          * g (y - a))) t ω = 0 := by
    rw [show (fun y : ℝ => A * g y + B * g (y - 1)
        + C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y)
        + D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
            * g (y - a))) = fun _ : ℝ => (0 : ℂ) from funext hdep]
    exact zak_zero t ω
  set X1 : ℝ → ℂ := fun y => A * g y with hX1
  set X2 : ℝ → ℂ := fun y => B * g (y - 1) with hX2
  set X3 : ℝ → ℂ :=
    fun y => C * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) with hX3
  set X4 : ℝ → ℂ :=
    fun y => D * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
      * g (y - a)) with hX4
  have t1 : Summable fun n : ℤ => X1 (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
    refine s1.congr fun n => ?_; simp only [hX1]
  have t2 : Summable fun n : ℤ => X2 (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
    refine s2.congr fun n => ?_; simp only [hX2]
  have t3 : Summable fun n : ℤ => X3 (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
    refine s3.congr fun n => ?_; simp only [hX3]
  have t4 : Summable fun n : ℤ => X4 (t - (n : ℝ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
    refine s4.congr fun n => ?_; simp only [hX4]
  have t12 : Summable fun n : ℤ => (X1 (t - (n : ℝ)) + X2 (t - (n : ℝ))) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
    refine (t1.add t2).congr fun n => ?_; ring
  have t123 : Summable fun n : ℤ =>
      (X1 (t - (n : ℝ)) + X2 (t - (n : ℝ)) + X3 (t - (n : ℝ))) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ω : ℂ)) := by
    refine (t12.add t3).congr fun n => ?_; ring
  have h12 := zak_add X1 X2 t ω t1 t2
  have h123 := zak_add (fun y => X1 y + X2 y) X3 t ω t12 t3
  have h1234 := zak_add (fun y => X1 y + X2 y + X3 y) X4 t ω t123 t4
  have hcollapse : zak (fun y => X1 y + X2 y + X3 y + X4 y) t ω = 0 := hzero
  rw [h1234, h123, h12] at hcollapse
  rw [← zak_smul g A t ω, ← zak_smul (fun y => g (y - 1)) B t ω,
    ← zak_smul (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) C t ω,
    ← zak_smul (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
      * g (y - a)) D t ω]
  exact hcollapse

/-! ### The symbol IS the quadratic, on the unit circle

The fibre symbol `A + B e^{-2πi(t+θ)} + C e^{2πit}` and the quadratic `C z² + A z + B w` of the
counting/Mahler machinery are the same object.  Setting `z = e^{2πit}` and `w = e^{-2πiθ}`,

  `symbol A B C θ t · z = C z² + A z + B w`,

and since `‖z‖ = 1` the two moduli agree pointwise.

This is the identity that lets the Birkhoff mean of `log‖symbol‖` over `t` — which
`integral_log_eq_of_modulus_cocycle` evaluates from the cocycle relation `zakFibre_modulus` — be
read as the CIRCLE AVERAGE of `log‖C z² + A z + B w‖`, i.e. as a Mahler measure, which is exactly
what `HRTResonant.mahler_mean` evaluates by Jensen's formula.  It is the join between the dynamical
side and the complex-analytic side of the argument. -/

/-- `e^{2πit}` is unimodular. -/
theorem norm_exp_two_pi_I_mul_real (x : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Multiplying the symbol by `z = e^{2πit}` produces the quadratic `C z² + A z + B w`. -/
theorem symbol_mul_eq_quadratic (A B C : ℂ) (θ t : ℝ) :
    symbol A B C θ t * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
        + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ))) := by
  have hsplit : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [symbol]
  linear_combination B * hsplit

/-- **The moduli agree.**  `‖symbol A B C θ t‖ = ‖C z² + A z + B w‖` with `z = e^{2πit}`,
`w = e^{-2πiθ}`. -/
theorem norm_symbol_eq_norm_quadratic (A B C : ℂ) (θ t : ℝ) :
    ‖symbol A B C θ t‖
      = ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
          + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
          + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))‖ := by
  rw [← symbol_mul_eq_quadratic, norm_mul, norm_exp_two_pi_I_mul_real, mul_one]

/-- The fibre parameter `w = e^{-2πiθ}` is unimodular — the `‖w‖ = 1` clause of the live set. -/
theorem norm_fibre_param (θ : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **From a Zak-side dependence to the fibre cocycle, in one step.**

Composing `zakFibre_equation` with `zakFibre_modulus`: a four-term time–frequency dependence,
transported to the Zak side, produces at every fibre the multiplicative cocycle relation

  `‖symbol A B C θ t‖ · ‖zakFibre g θ t‖ = ‖D‖ · ‖zakFibre g θ (t - a)‖`.

That relation is precisely the input of `integral_log_eq_of_modulus_cocycle` (in
`BirkhoffErgodic.lean`), whose output is the mean condition `∫ log‖symbol‖ = log‖D‖` — which
`norm_symbol_eq_norm_quadratic` and `HRTResonant.intervalIntegral_eq_circleAverage` then turn into
the circle-average form the Jensen machinery consumes.

So this lemma is the first link of the reduction that `heil_speegle_lambda_zero_of_mean` assumes. -/
theorem dependence_to_cocycle (g : ℝ → ℂ) (A B C D : ℂ) (a b : ℝ) (j : ℤ)
    (hb : b = a + (j : ℝ)) (hD : D ≠ 0) (θ t : ℝ)
    (hz : A * zak g t (t + θ)
        + B * zak (fun y => g (y - 1)) t (t + θ)
        + C * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t (t + θ)
        + D * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
              * g (y - a)) t (t + θ) = 0) :
    ‖symbol A B C θ t‖ * ‖zakFibre g θ t‖ = ‖D‖ * ‖zakFibre g θ (t - a)‖ :=
  zakFibre_modulus g A B C D a b hD θ t (zakFibre_equation g A B C D a b j hb θ t hz)

/-- The cocycle relation with the symbol rewritten as the quadratic — the form in which the
Birkhoff mean is literally a Mahler measure. -/
theorem dependence_to_cocycle_quadratic (g : ℝ → ℂ) (A B C D : ℂ) (a b : ℝ) (j : ℤ)
    (hb : b = a + (j : ℝ)) (hD : D ≠ 0) (θ t : ℝ)
    (hz : A * zak g t (t + θ)
        + B * zak (fun y => g (y - 1)) t (t + θ)
        + C * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t (t + θ)
        + D * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
              * g (y - a)) t (t + θ) = 0) :
    ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
        + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))‖
      * ‖zakFibre g θ t‖ = ‖D‖ * ‖zakFibre g θ (t - a)‖ := by
  rw [← norm_symbol_eq_norm_quadratic]
  exact dependence_to_cocycle g A B C D a b j hb hD θ t hz

/-! ### The three-point specialisation

A three-point dependence is the four-point one with `C = 0`, and then the symbol
`A + B e^{-2πi(t+θ)} + C e^{2πit}` collapses to `A + B e^{-2πi(t+θ)}` — LINEAR in the fibre
variable rather than quadratic.

That is the case in which Jensen's formula is an exact evaluation rather than an inequality, which
is what `HRTResonant.linear_mean_max` exploits to pin the coefficients.  Specialising here means
the three-point route reuses the whole four-point fibration instead of rebuilding it. -/

/-- The three-point symbol: the four-point one at `C = 0`, linear in the fibre variable. -/
theorem symbol_linear (A B : ℂ) (θ t : ℝ) :
    symbol A B 0 θ t
      = A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ))) := by
  rw [symbol]; ring

/-- The fibre variable `u = e^{-2πi(t+θ)}` is unimodular. -/
theorem norm_fibre_var (θ t : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **The three-point fibre cocycle.**  `dependence_to_cocycle` at `C = 0`: a three-term
dependence gives `‖A + B u‖ · ‖fibre t‖ = ‖D‖ · ‖fibre (t - a)‖` with `u` unimodular. -/
theorem threePoint_dependence_to_cocycle (g : ℝ → ℂ) (A B D : ℂ) (a b : ℝ) (j : ℤ)
    (hb : b = a + (j : ℝ)) (hD : D ≠ 0) (θ t : ℝ)
    (hz : A * zak g t (t + θ)
        + B * zak (fun y => g (y - 1)) t (t + θ)
        + 0 * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * g y) t (t + θ)
        + D * zak (fun y => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) * (y : ℂ))
              * g (y - a)) t (t + θ) = 0) :
    ‖A + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))‖
      * ‖zakFibre g θ t‖ = ‖D‖ * ‖zakFibre g θ (t - a)‖ := by
  rw [← symbol_linear]
  exact dependence_to_cocycle g A B 0 D a b j hb hD θ t hz

/-- `e^{-2πi} = 1`. -/
theorem exp_neg_two_pi_I : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- **The symbol is `1`-periodic in `t`.**  Both exponentials have period one, so the symbol
descends to `AddCircle 1` — which is what lets the abstract Birkhoff mean lemma, stated on a
probability space, consume the Zak cocycle, stated pointwise on `ℝ`. -/
theorem symbol_periodic (A B C : ℂ) (θ : ℝ) :
    Function.Periodic (fun t : ℝ => symbol A B C θ t) 1 := by
  intro t
  have h1 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + 1 + θ : ℝ) : ℂ)))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ))) := by
    have hsplit : (-(2 * (Real.pi : ℂ) * Complex.I * ((t + 1 + θ : ℝ) : ℂ)))
        = (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))
          + (-(2 * (Real.pi : ℂ) * Complex.I)) := by push_cast; ring
    rw [hsplit, Complex.exp_add, exp_neg_two_pi_I, mul_one]
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t + 1 : ℝ) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
    have hsplit : (2 * (Real.pi : ℂ) * Complex.I * ((t + 1 : ℝ) : ℂ))
        = (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  show symbol A B C θ (t + 1) = symbol A B C θ t
  rw [symbol, symbol, h1, h2]

/-- The symbol's MODULUS is `1`-periodic — the form the cocycle uses. -/
theorem norm_symbol_periodic (A B C : ℂ) (θ : ℝ) :
    Function.Periodic (fun t : ℝ => ‖symbol A B C θ t‖) 1 := by
  intro t
  show ‖symbol A B C θ (t + 1)‖ = ‖symbol A B C θ t‖
  congr 1
  exact symbol_periodic A B C θ t

/-- The fibre modulus is `1`-periodic, in `Function.Periodic` form. -/
theorem norm_zakFibre_periodic' (g : ℝ → ℂ) (θ : ℝ) :
    Function.Periodic (fun t : ℝ => ‖zakFibre g θ t‖) 1 :=
  fun t => norm_zakFibre_periodic g θ t

/-- The symbol modulus, descended to `AddCircle 1`. -/
noncomputable def symbolCircle (A B C : ℂ) (θ : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  (norm_symbol_periodic A B C θ).lift

@[simp] theorem symbolCircle_coe (A B C : ℂ) (θ t : ℝ) :
    symbolCircle A B C θ ((t : ℝ) : AddCircle (1 : ℝ)) = ‖symbol A B C θ t‖ :=
  Function.Periodic.lift_coe _ t

/-- The fibre modulus, descended to `AddCircle 1`. -/
noncomputable def fibreCircle (g : ℝ → ℂ) (θ : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  (norm_zakFibre_periodic' g θ).lift

@[simp] theorem fibreCircle_coe (g : ℝ → ℂ) (θ t : ℝ) :
    fibreCircle g θ ((t : ℝ) : AddCircle (1 : ℝ)) = ‖zakFibre g θ t‖ :=
  Function.Periodic.lift_coe _ t

/-- **The cocycle descends to the circle.**

This is the transport that lets the abstract Birkhoff mean lemma consume the Zak relation: on
`AddCircle 1` the Haar measure is a PROBABILITY measure and translation is measure-preserving,
which are exactly `integral_log_eq_of_modulus_cocycle`'s standing hypotheses. -/
theorem cocycle_circle (g : ℝ → ℂ) (A B C D : ℂ) (a θ : ℝ)
    (hcoc : ∀ t : ℝ, ‖symbol A B C θ t‖ * ‖zakFibre g θ t‖
      = ‖D‖ * ‖zakFibre g θ (t - a)‖) (x : AddCircle (1 : ℝ)) :
    symbolCircle A B C θ x * fibreCircle g θ x
      = ‖D‖ * fibreCircle g θ (x - ((a : ℝ) : AddCircle (1 : ℝ))) := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    have hsub : (((t : ℝ) : AddCircle (1 : ℝ)) - ((a : ℝ) : AddCircle (1 : ℝ)))
        = (((t - a : ℝ)) : AddCircle (1 : ℝ)) := by
      simp [QuotientAddGroup.mk_sub]
    rw [symbolCircle_coe, fibreCircle_coe, hsub, fibreCircle_coe]
    exact hcoc t

/-- The descended symbol modulus is nonnegative (it is a lifted norm). -/
theorem symbolCircle_nonneg (A B C : ℂ) (θ : ℝ) (x : AddCircle (1 : ℝ)) :
    0 ≤ symbolCircle A B C θ x := by
  induction x using QuotientAddGroup.induction_on with
  | H t => rw [symbolCircle_coe]; exact norm_nonneg _

/-- The descended fibre modulus is nonnegative. -/
theorem fibreCircle_nonneg (g : ℝ → ℂ) (θ : ℝ) (x : AddCircle (1 : ℝ)) :
    0 ≤ fibreCircle g θ x := by
  induction x using QuotientAddGroup.induction_on with
  | H t => rw [fibreCircle_coe]; exact norm_nonneg _

/-- The cocycle in the ABSOLUTE-VALUE form `integral_log_eq_of_modulus_cocycle` expects.  Both
factors are lifted norms, so the absolute values are cosmetic — but the Birkhoff lemma is stated
for general real functions and wants them. -/
theorem cocycle_circle_abs (g : ℝ → ℂ) (A B C D : ℂ) (a θ : ℝ)
    (hcoc : ∀ t : ℝ, ‖symbol A B C θ t‖ * ‖zakFibre g θ t‖
      = ‖D‖ * ‖zakFibre g θ (t - a)‖) (x : AddCircle (1 : ℝ)) :
    |symbolCircle A B C θ x| * |fibreCircle g θ x|
      = ‖D‖ * |fibreCircle g θ (x - ((a : ℝ) : AddCircle (1 : ℝ)))| := by
  rw [abs_of_nonneg (symbolCircle_nonneg A B C θ x),
    abs_of_nonneg (fibreCircle_nonneg g θ x),
    abs_of_nonneg (fibreCircle_nonneg g θ _)]
  exact cocycle_circle g A B C D a θ hcoc x

/-- On the circle of length one, Haar IS the volume measure. -/
theorem volume_eq_haar_one :
    (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- **The circle integral IS the `[0,1]` integral.**  The last impedance mismatch: Birkhoff returns
a mean over `AddCircle 1`, while every Jensen-side theorem here consumes a `t`-integral over `[0,1]`.
`AddCircle.intervalIntegral_preimage` identifies them, and on the unit-length circle Haar is the
volume measure so no normalising constant appears. -/
theorem symbol_mean_circle_eq_interval (A B C : ℂ) (θ : ℝ) :
    (∫ x, Real.log |symbolCircle A B C θ x|
      ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))))
      = ∫ t in (0 : ℝ)..1, Real.log ‖symbol A B C θ t‖ := by
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun x : AddCircle (1 : ℝ) => Real.log |symbolCircle A B C θ x|)
  rw [← volume_eq_haar_one, ← hpre]
  have hcongr : ∀ t : ℝ, Real.log |symbolCircle A B C θ ((t : ℝ) : AddCircle (1 : ℝ))|
      = Real.log ‖symbol A B C θ t‖ := by
    intro t
    rw [symbolCircle_coe, abs_of_nonneg (norm_nonneg _)]
  rw [zero_add]
  exact intervalIntegral.integral_congr (fun t _ => hcongr t)

end ZakDef

end ZakPeriodization

#print axioms ZakPeriodization.isAddFundamentalDomain_Ioc_zero_one
#print axioms ZakPeriodization.lintegral_sq_eq_tsum
#print axioms ZakPeriodization.norm_sq_ofCoeffs
#print axioms ZakPeriodization.lintegral_sq_eq_setLIntegral_tsum
#print axioms ZakPeriodization.zak_periodic_snd
#print axioms ZakPeriodization.zak_quasi_periodic_fst
#print axioms ZakPeriodization.zak_covariance
#print axioms ZakPeriodization.zak_periodic_snd_int
#print axioms ZakPeriodization.zak_quasi_periodic_fst_int
#print axioms ZakPeriodization.zak_intShift
#print axioms ZakPeriodization.zak_timeShift_one
#print axioms ZakPeriodization.zak_modulate_one
#print axioms ZakPeriodization.zak_modulate_timeShift
#print axioms ZakPeriodization.zak_smul
#print axioms ZakPeriodization.zak_add
#print axioms ZakPeriodization.zak_fibre_equation
#print axioms ZakPeriodization.resonant_shift_preserves_theta
#print axioms ZakPeriodization.zakFibre_equation
#print axioms ZakPeriodization.norm_zakFibre_periodic
#print axioms ZakPeriodization.zakFibre_modulus
#print axioms ZakPeriodization.norm_exp_two_pi_I_mul_real
#print axioms ZakPeriodization.symbol_mul_eq_quadratic
#print axioms ZakPeriodization.norm_symbol_eq_norm_quadratic
#print axioms ZakPeriodization.norm_fibre_param
#print axioms ZakPeriodization.dependence_to_cocycle
#print axioms ZakPeriodization.dependence_to_cocycle_quadratic
#print axioms ZakPeriodization.symbol_linear
#print axioms ZakPeriodization.norm_fibre_var
#print axioms ZakPeriodization.threePoint_dependence_to_cocycle
#print axioms ZakPeriodization.exp_neg_two_pi_I
#print axioms ZakPeriodization.symbol_periodic
#print axioms ZakPeriodization.norm_symbol_periodic
#print axioms ZakPeriodization.norm_zakFibre_periodic'
#print axioms ZakPeriodization.symbolCircle_coe
#print axioms ZakPeriodization.fibreCircle_coe
#print axioms ZakPeriodization.cocycle_circle
#print axioms ZakPeriodization.symbolCircle_nonneg
#print axioms ZakPeriodization.fibreCircle_nonneg
#print axioms ZakPeriodization.cocycle_circle_abs
#print axioms ZakPeriodization.volume_eq_haar_one
#print axioms ZakPeriodization.symbol_mean_circle_eq_interval
#print axioms ZakPeriodization.zak_zero
#print axioms ZakPeriodization.zak_dep_zero
#print axioms ZakPeriodization.fourierCoeff_ofCoeffs
#print axioms ZakPeriodization.ofCoeffs_injective
#print axioms ZakPeriodization.eq_zero_of_ofCoeffs_eq_zero
#print axioms ZakPeriodization.not_ae_fibre_zero_of_lintegral_ne_zero
