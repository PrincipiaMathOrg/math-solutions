import HRTRectangular
import HRTFourierCov

/-!
# `hthree` for `Λ₀` — the three-point cases of Heil–Speegle

`HRTResonantFibre.heil_speegle_lambda_zero` carries the hypothesis

  `hthree : ∀ c, (∑ i, c i • lambdaZeroFamily g i) = 0 → (∃ i, c i = 0) → ∀ i, c i = 0`

with `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}`.  A dependence with one vanishing coefficient is a
THREE-point dependence, so `hthree` is exactly the four three-point subsets of `Λ₀`:

| dropped | triple                        | route                                  |
|---------|-------------------------------|----------------------------------------|
| `c₃`    | `{(0,0),(1,0),(0,1)}`         | `HRTRect.hrt_integer_lattice`          |
| `c₁`    | `{(0,0),(0,1),(√2,√2)}`       | `HRTRect.hrt_lambdaZero_mod_triple`    |
| `c₂`    | `{(0,0),(1,0),(√2,√2)}`       | **Fourier** — no vertical generator    |
| `c₀`    | `{(1,0),(0,1),(√2,√2)}`       | **Fourier** — no vertical generator    |

The last two are the ones the Borel subgroup provably cannot reach: their lattice contains no
nonzero vector of zero time component.  `𝓕` supplies the missing symplectic rotation
`(x,ω) ↦ (ω,−x)`, after which the configuration DOES have a vertical generator and
`HRTRect.hrt_shear` applies.

This file supplies the input half of that transfer — turning a raw-function dependence into the
`Lp` equation `HRTFourierCov.fourier_three_dep` consumes.  (`ae_of_lp_three_dep` already does the
output half.)

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000

namespace HRTLambdaZero

open Complex MeasureTheory HRTChar HRTFourierCov HRTRect

/-- `HRTChar.chr` and `HRTTransfer.ee` are the same character. -/
theorem chr_eq_ee (ω t : ℝ) : chr ω t = HRTTransfer.ee (ω * t) := by
  unfold chr HRTTransfer.ee
  congr 1
  push_cast
  ring

/-- `TFL` acts on an `Lp` class exactly as `tf` acts on a representative. -/
theorem coeFn_TFL_toLp (y η : ℝ) {g : ℝ → ℂ} (hgL : MemLp g 2 (volume : Measure ℝ)) :
    ⇑(TFL y η (hgL.toLp g)) =ᵐ[(volume : Measure ℝ)] fun t : ℝ => tf y η g t := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-y)
  -- the representative identity must be PUSHED FORWARD: `coeFn_TFL` evaluates it at `t + -y`
  filter_upwards [coeFn_TFL y η (hgL.toLp g),
    hmp.quasiMeasurePreserving.ae hgL.coeFn_toLp] with t h1 h2
  rw [h1, h2, chr_eq_ee]
  unfold tf
  rw [sub_eq_add_neg]

/-- **A raw three-point dependence becomes the `Lp` equation.** -/
theorem lp_dep_of_ae (y₁ η₁ y₂ η₂ y₃ η₃ : ℝ) (d₁ d₂ d₃ : ℂ)
    {g : ℝ → ℂ} (hgL : MemLp g 2 (volume : Measure ℝ))
    (hae : ∀ᵐ t : ℝ, d₁ * tf y₁ η₁ g t + d₂ * tf y₂ η₂ g t + d₃ * tf y₃ η₃ g t = 0) :
    d₁ • TFL y₁ η₁ (hgL.toLp g) + d₂ • TFL y₂ η₂ (hgL.toLp g)
      + d₃ • TFL y₃ η₃ (hgL.toLp g) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae,
    Lp.coeFn_add (d₁ • TFL y₁ η₁ (hgL.toLp g) + d₂ • TFL y₂ η₂ (hgL.toLp g))
      (d₃ • TFL y₃ η₃ (hgL.toLp g)),
    Lp.coeFn_add (d₁ • TFL y₁ η₁ (hgL.toLp g)) (d₂ • TFL y₂ η₂ (hgL.toLp g)),
    Lp.coeFn_smul d₁ (TFL y₁ η₁ (hgL.toLp g)), Lp.coeFn_smul d₂ (TFL y₂ η₂ (hgL.toLp g)),
    Lp.coeFn_smul d₃ (TFL y₃ η₃ (hgL.toLp g)),
    coeFn_TFL_toLp y₁ η₁ hgL, coeFn_TFL_toLp y₂ η₂ hgL, coeFn_TFL_toLp y₃ η₃ hgL]
    with t hd ha1 ha2 hs1 hs2 hs3 hT1 hT2 hT3
  rw [ha1]
  simp only [Pi.add_apply, ha2, Pi.smul_apply, hs1, hs2, hs3, hT1, hT2, hT3, smul_eq_mul]
  exact hd

/-! ### HRT for a configuration whose FOURIER ROTATION is sheared-rectangular -/

theorem tf_eq_chr (y η : ℝ) (h : ℝ → ℂ) (t : ℝ) : tf y η h t = chr η t * h (t + -y) := by
  unfold tf
  rw [chr_eq_ee, sub_eq_add_neg]

theorem finset_three_sum {α : Type*} [DecidableEq α] (p₁ p₂ p₃ : α)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (F : α → ℂ) :
    ∑ p ∈ ({p₁, p₂, p₃} : Finset α), F p = F p₁ + F p₂ + F p₃ := by
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton]
  ring

/-- **HRT for a three-point configuration whose Fourier rotation is sheared-rectangular.**

`𝓕` sends `(x,ω)` to `(ω,−x)`.  If the rotated points sit in the sheared lattice
`{(m a, n b + κ m a)}`, then `HRTRect.hrt_shear` applies on the Fourier side — even when the
ORIGINAL configuration has no vertical generator and so is out of reach of chirp-and-dilate. -/
theorem hrt_three_of_rot {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p₁ p₂ p₃ : ℤ × ℤ) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (x₁ ω₁ x₂ ω₂ x₃ ω₃ : ℝ)
    (hω₁ : ω₁ = (p₁.1 : ℝ) * a) (hx₁ : -x₁ = (p₁.2 : ℝ) * b + κ * ((p₁.1 : ℝ) * a))
    (hω₂ : ω₂ = (p₂.1 : ℝ) * a) (hx₂ : -x₂ = (p₂.2 : ℝ) * b + κ * ((p₂.1 : ℝ) * a))
    (hω₃ : ω₃ = (p₃.1 : ℝ) * a) (hx₃ : -x₃ = (p₃.2 : ℝ) * b + κ * ((p₃.1 : ℝ) * a))
    {g : ℝ → ℂ} (hgL : MemLp g 2 (volume : Measure ℝ)) (hgne : hgL.toLp g ≠ 0)
    (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf x₁ ω₁ g t + c₂ * tf x₂ ω₂ g t + c₃ * tf x₃ ω₃ g t = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  classical
  set ph₁ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x₁ : ℂ) * (ω₁ : ℂ)) with hph₁
  set ph₂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x₂ : ℂ) * (ω₂ : ℂ)) with hph₂
  set ph₃ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x₃ : ℂ) * (ω₃ : ℂ)) with hph₃
  -- push the dependence through `𝓕`
  have hlp := lp_dep_of_ae x₁ ω₁ x₂ ω₂ x₃ ω₃ c₁ c₂ c₃ hgL hdep
  have hrot := fourier_three_dep x₁ ω₁ x₂ ω₂ x₃ ω₃ c₁ c₂ c₃ (hgL.toLp g) hlp
  have hae := ae_of_lp_three_dep ω₁ (-x₁) ω₂ (-x₂) ω₃ (-x₃)
    (c₁ * ph₁) (c₂ * ph₂) (c₃ * ph₃) (Lp.fourierTransformₗᵢ ℝ ℂ (hgL.toLp g)) hrot
  -- the Fourier-side window
  set H : Lp ℂ 2 (volume : Measure ℝ) := Lp.fourierTransformₗᵢ ℝ ℂ (hgL.toLp g) with hH
  have hHne : H ≠ 0 := fourier_ne_zero hgne
  have hHm : Measurable (⇑H) := (H : ℝ →ₘ[(volume : Measure ℝ)] ℂ).stronglyMeasurable.measurable
  have hHL : MemLp (⇑H) 2 (volume : Measure ℝ) := Lp.memLp H
  have hHae : ¬ ((⇑H) =ᵐ[(volume : Measure ℝ)] 0) := by
    intro hc
    exact hHne (Lp.eq_zero_iff_ae_eq_zero.mpr hc)
  -- package the three terms as a `Finset` sum in `hrt_shear`'s indexed form
  set C : ℤ × ℤ → ℂ :=
    fun q => if q = p₁ then c₁ * ph₁ else if q = p₂ then c₂ * ph₂
      else if q = p₃ then c₃ * ph₃ else 0 with hC
  have hC₁ : C p₁ = c₁ * ph₁ := by rw [hC]; simp
  have hC₂ : C p₂ = c₂ * ph₂ := by rw [hC]; simp [h12.symm]
  have hC₃ : C p₃ = c₃ * ph₃ := by rw [hC]; simp [h13.symm, h23.symm]
  have hshear : ∀ᵐ t : ℝ, ∑ p ∈ ({p₁, p₂, p₃} : Finset (ℤ × ℤ)),
      C p * tf ((p.1 : ℝ) * a) ((p.2 : ℝ) * b + κ * ((p.1 : ℝ) * a)) (⇑H) t = 0 := by
    filter_upwards [hae] with t ht
    -- the COMPOUND frequency must be rewritten before the time step: `← hω` would otherwise
    -- rewrite `↑p.1 * a` inside `↑p.2 * b + κ * (↑p.1 * a)` and destroy `← hx`'s pattern
    rw [finset_three_sum p₁ p₂ p₃ h12 h13 h23, hC₁, hC₂, hC₃,
      ← hx₁, ← hω₁, ← hx₂, ← hω₂, ← hx₃, ← hω₃]
    simp only [tf_eq_chr]
    exact ht
  have hzero := hrt_shear ha hb hHm hHL hHae ({p₁, p₂, p₃} : Finset (ℤ × ℤ)) C hshear
  have hp₁ : C p₁ = 0 := hzero p₁ (by simp)
  have hp₂ : C p₂ = 0 := hzero p₂ (by simp)
  have hp₃ : C p₃ = 0 := hzero p₃ (by simp)
  rw [hC₁] at hp₁; rw [hC₂] at hp₂; rw [hC₃] at hp₃
  exact ⟨(mul_eq_zero.mp hp₁).resolve_right (Complex.exp_ne_zero _),
    (mul_eq_zero.mp hp₂).resolve_right (Complex.exp_ne_zero _),
    (mul_eq_zero.mp hp₃).resolve_right (Complex.exp_ne_zero _)⟩

/-! ### `Λ₀` triple 2 — `{(0,0), (1,0), (√2,√2)}`

Under `𝓕` this becomes `{(0,0), (0,−1), (√2,−√2)}`, which sits in the sheared lattice at
`a = √2`, `b = 1`, `κ = −1` with indices `(0,0)`, `(0,−1)`, `(1,0)`:

* `(0,0)`  ↦ `(0·√2, 0·1 + (−1)·0)      = (0,0)`
* `(0,−1)` ↦ `(0·√2, (−1)·1 + (−1)·0)   = (0,−1)`
* `(1,0)`  ↦ `(1·√2, 0·1 + (−1)·√2)     = (√2,−√2)`

The original configuration has NO vertical generator — `m(1,0) + n(√2,√2)` has frequency `n√2`,
zero only when `n = 0` — so this is exactly the case chirp-and-dilate cannot reach. -/
theorem hrt_lambdaZero_triple2 {g : ℝ → ℂ} (hgL : MemLp g 2 (volume : Measure ℝ))
    (hgne : hgL.toLp g ≠ 0) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf 0 0 g t + c₂ * tf 1 0 g t
      + c₃ * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  refine hrt_three_of_rot (a := Real.sqrt 2) (b := 1) (κ := -1) (by positivity) one_pos
    ((0, 0) : ℤ × ℤ) ((0, -1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)
    (by decide) (by decide) (by decide)
    0 0 1 0 (Real.sqrt 2) (Real.sqrt 2) ?_ ?_ ?_ ?_ ?_ ?_ hgL hgne c₁ c₂ c₃ hdep
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-! ### `Λ₀` triple 4 — `{(1,0), (0,1), (√2,√2)}`

This is the one triple of `Λ₀` that does **not contain the origin**, and it needs strictly more
than the Fourier rotation.  Two independent obstructions:

* `hrt_three_of_rot` places the points in a lattice **through `(0,0)`**, so the configuration must
  be translated first.  (The three points here generate a rank-3 — hence dense — subgroup; only
  their *differences* are discrete.)
* even after translating, `𝓕` alone is not enough: it needs the frequencies `0, 1, √2` to lie in a
  common `aℤ`, and `1`, `√2` are incommensurable.  A **chirp before the rotation** is required.
  With `κ' = 1` the rotated lattice acquires the vertical generator that `(1,0)` supplies:
  `m + n√2 + κ'(−m + n(√2−1)) = 0` is solvable at `(m,n) = (1,0)` exactly when `κ' = 1`.

So the route is translate by `(−1,0)`, chirp by `1`, then rotate:

    (1,0)  ↦ (0,0)     ↦ (0,0)          ↦ (0,0)
    (0,1)  ↦ (−1,1)    ↦ (−1,0)         ↦ (0,1)
    (√2,√2)↦ (√2−1,√2) ↦ (√2−1, 2√2−1)  ↦ (2√2−1, 1−√2)

landing in the sheared lattice at `a = 2√2−1`, `b = 1`, `κ = (1−√2)/(2√2−1)`. -/

/-- **Translation transfer.**  A three-point dependence may be moved by any `(x', ω')`: the
configuration shifts rigidly and the coefficients pick up unimodular phases.  Purely pointwise —
the only measure theory is that `t ↦ t + (−x')` preserves Lebesgue measure. -/
theorem tf_three_shift (x' ω' : ℝ) {g : ℝ → ℂ} (x₁ ω₁ x₂ ω₂ x₃ ω₃ : ℝ) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf x₁ ω₁ g t + c₂ * tf x₂ ω₂ g t + c₃ * tf x₃ ω₃ g t = 0) :
    ∀ᵐ t : ℝ, (c₁ * HRTTransfer.ee (-(ω₁ * x'))) * tf (x₁ + x') (ω₁ + ω') g t
      + (c₂ * HRTTransfer.ee (-(ω₂ * x'))) * tf (x₂ + x') (ω₂ + ω') g t
      + (c₃ * HRTTransfer.ee (-(ω₃ * x'))) * tf (x₃ + x') (ω₃ + ω') g t = 0 := by
  have key : ∀ x ω t : ℝ,
      HRTTransfer.ee (-(ω * x')) * tf (x + x') (ω + ω') g t
        = HRTTransfer.ee (ω' * t) * tf x ω g (t + -x') := by
    intro x ω t
    unfold tf
    rw [show t + -x' - x = t - (x + x') from by ring, ← mul_assoc, ← mul_assoc,
      ← HRTTransfer.ee_add, ← HRTTransfer.ee_add,
      show -(ω * x') + (ω + ω') * t = ω' * t + ω * (t + -x') from by ring]
  filter_upwards [(measurePreserving_add_right volume (-x')).quasiMeasurePreserving.ae hdep]
    with t ht
  linear_combination (HRTTransfer.ee (ω' * t)) * ht
    + c₁ * key x₁ ω₁ t + c₂ * key x₂ ω₂ t + c₃ * key x₃ ω₃ t

/-- **Chirp transfer, three-point form.**  The `Finset` version is `HRTRect.chirp_transfer`; this
one avoids the packing.  Shears the configuration by `(x,ω) ↦ (x, ω + κ'x)`. -/
theorem tf_three_chirp (κ' : ℝ) {g : ℝ → ℂ} (x₁ ω₁ x₂ ω₂ x₃ ω₃ : ℝ) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf x₁ ω₁ g t + c₂ * tf x₂ ω₂ g t + c₃ * tf x₃ ω₃ g t = 0) :
    ∀ᵐ t : ℝ, (c₁ * HRTTransfer.ee (-(κ' * x₁ ^ 2 / 2))) * tf x₁ (ω₁ + κ' * x₁) (chirp κ' g) t
      + (c₂ * HRTTransfer.ee (-(κ' * x₂ ^ 2 / 2))) * tf x₂ (ω₂ + κ' * x₂) (chirp κ' g) t
      + (c₃ * HRTTransfer.ee (-(κ' * x₃ ^ 2 / 2))) * tf x₃ (ω₃ + κ' * x₃) (chirp κ' g) t = 0 := by
  filter_upwards [hdep] with t ht
  linear_combination (HRTTransfer.ee (κ' * t ^ 2 / 2)) * ht
    - c₁ * chirp_tf κ' x₁ ω₁ g t - c₂ * chirp_tf κ' x₂ ω₂ g t - c₃ * chirp_tf κ' x₃ ω₃ g t

/-- **`Λ₀` triple 4** `{(1,0), (0,1), (√2,√2)}` — translate, chirp, rotate. -/
theorem hrt_lambdaZero_triple4 {g : ℝ → ℂ} (hgm : Measurable g)
    (hgL : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0)) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf 1 0 g t + c₂ * tf 0 1 g t
      + c₃ * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have ha : (0 : ℝ) < 2 * Real.sqrt 2 - 1 := by linarith
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the chirped window is still a nonzero `L²` function
  have hcL : MemLp (chirp 1 g) 2 (volume : Measure ℝ) := memLp_chirp hgm hgL
  have hcne : hcL.toLp (chirp 1 g) ≠ 0 := fun hc =>
    chirp_ne_zero hgne (hcL.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hc))
  -- translate the configuration so that `(1,0)` sits at the origin, then chirp by `1`.
  -- `κ` is `(1−√2)/(2√2−1)` RATIONALISED — clearing the irrational denominator by hand keeps
  -- the side goal a polynomial identity in `√2`, which `linear_combination … * h2` closes
  -- outright; `field_simp` cannot, as it never matches its hypothesis against `-1 + √2*2`.
  have hrot := hrt_three_of_rot (a := 2 * Real.sqrt 2 - 1) (b := 1)
    (κ := (Real.sqrt 2 - 3) / 7) ha one_pos
    ((0, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ)
    (by decide) (by decide) (by decide)
    (1 + -1) (0 + 0 + 1 * (1 + -1))
    (0 + -1) (1 + 0 + 1 * (0 + -1))
    (Real.sqrt 2 + -1) (Real.sqrt 2 + 0 + 1 * (Real.sqrt 2 + -1))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; linear_combination (-2 / 7 : ℝ) * h2)
    hcL hcne _ _ _
    (tf_three_chirp 1 (1 + -1) (0 + 0) (0 + -1) (1 + 0) (Real.sqrt 2 + -1) (Real.sqrt 2 + 0)
      _ _ _ (tf_three_shift (-1) 0 1 0 0 1 (Real.sqrt 2) (Real.sqrt 2) c₁ c₂ c₃ hdep))
  -- strip the unimodular phases
  have kill : ∀ c A B : ℂ, A ≠ 0 → B ≠ 0 → c * A * B = 0 → c = 0 := by
    intro c A B hA hB h
    rcases mul_eq_zero.mp h with h' | h'
    · exact (mul_eq_zero.mp h').resolve_right hA
    · exact absurd h' hB
  obtain ⟨k₁, k₂, k₃⟩ := hrot
  exact ⟨kill _ _ _ (HRTTransfer.ee_ne_zero _) (HRTTransfer.ee_ne_zero _) k₁,
    kill _ _ _ (HRTTransfer.ee_ne_zero _) (HRTTransfer.ee_ne_zero _) k₂,
    kill _ _ _ (HRTTransfer.ee_ne_zero _) (HRTTransfer.ee_ne_zero _) k₃⟩

/-! ### The two Borel-reachable triples, in three-point form

`HRTRect.hrt_shear` is indexed by a `Finset`; `hthree` wants three explicit coefficients.  This
is the same `if`-cascade packing `hrt_three_of_rot` uses internally, factored out so triples 1
and 3 read like triples 2 and 4. -/

/-- **`hrt_shear`, three-point form.** -/
theorem hrt_three_of_shear {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p₁ p₂ p₃ : ℤ × ℤ) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (x₁ ω₁ x₂ ω₂ x₃ ω₃ : ℝ)
    (hx₁ : x₁ = (p₁.1 : ℝ) * a) (hω₁ : ω₁ = (p₁.2 : ℝ) * b + κ * ((p₁.1 : ℝ) * a))
    (hx₂ : x₂ = (p₂.1 : ℝ) * a) (hω₂ : ω₂ = (p₂.2 : ℝ) * b + κ * ((p₂.1 : ℝ) * a))
    (hx₃ : x₃ = (p₃.1 : ℝ) * a) (hω₃ : ω₃ = (p₃.2 : ℝ) * b + κ * ((p₃.1 : ℝ) * a))
    {g : ℝ → ℂ} (hgm : Measurable g) (hgL : MemLp g 2 (volume : Measure ℝ))
    (hgne : ¬ (g =ᵐ[volume] 0)) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf x₁ ω₁ g t + c₂ * tf x₂ ω₂ g t + c₃ * tf x₃ ω₃ g t = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  classical
  set C : ℤ × ℤ → ℂ :=
    fun q => if q = p₁ then c₁ else if q = p₂ then c₂ else if q = p₃ then c₃ else 0 with hC
  have hC₁ : C p₁ = c₁ := by rw [hC]; simp
  have hC₂ : C p₂ = c₂ := by rw [hC]; simp [h12.symm]
  have hC₃ : C p₃ = c₃ := by rw [hC]; simp [h13.symm, h23.symm]
  have hshear : ∀ᵐ t : ℝ, ∑ p ∈ ({p₁, p₂, p₃} : Finset (ℤ × ℤ)),
      C p * tf ((p.1 : ℝ) * a) ((p.2 : ℝ) * b + κ * ((p.1 : ℝ) * a)) g t = 0 := by
    filter_upwards [hdep] with t ht
    -- `hω`'s right-hand side CONTAINS `hx`'s, so it must be rewritten first
    rw [finset_three_sum p₁ p₂ p₃ h12 h13 h23, hC₁, hC₂, hC₃,
      ← hω₁, ← hx₁, ← hω₂, ← hx₂, ← hω₃, ← hx₃]
    exact ht
  have hz := hrt_shear ha hb hgm hgL hgne _ C hshear
  exact ⟨hC₁.symm.trans (hz p₁ (by simp)), hC₂.symm.trans (hz p₂ (by simp)),
    hC₃.symm.trans (hz p₃ (by simp))⟩

/-- **`Λ₀` triple 1** `{(0,0), (1,0), (0,1)}` — the integer lattice, `a = b = 1`, `κ = 0`. -/
theorem hrt_lambdaZero_triple1 {g : ℝ → ℂ} (hgm : Measurable g)
    (hgL : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0)) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf 0 0 g t + c₂ * tf 1 0 g t + c₃ * tf 0 1 g t = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 :=
  hrt_three_of_shear (a := 1) (b := 1) (κ := 0) one_pos one_pos
    ((0, 0) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) (by decide) (by decide) (by decide)
    0 0 1 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hgm hgL hgne c₁ c₂ c₃ hdep

/-- **`Λ₀` triple 3** `{(0,0), (0,1), (√2,√2)}` — the shear `a = √2`, `b = 1`, `κ = 1`.
Same instantiation as `HRTRect.hrt_lambdaZero_mod_triple`, in three-point form. -/
theorem hrt_lambdaZero_triple3 {g : ℝ → ℂ} (hgm : Measurable g)
    (hgL : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0)) (c₁ c₂ c₃ : ℂ)
    (hdep : ∀ᵐ t : ℝ, c₁ * tf 0 0 g t + c₂ * tf 0 1 g t
      + c₃ * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 :=
  hrt_three_of_shear (a := Real.sqrt 2) (b := 1) (κ := 1) (by positivity) one_pos
    ((0, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) ((1, 0) : ℤ × ℤ) (by decide) (by decide) (by decide)
    0 0 0 1 (Real.sqrt 2) (Real.sqrt 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hgm hgL hgne c₁ c₂ c₃ hdep

end HRTLambdaZero

/-! ## Acceptance gate -/

#print axioms HRTLambdaZero.chr_eq_ee
#print axioms HRTLambdaZero.coeFn_TFL_toLp
#print axioms HRTLambdaZero.lp_dep_of_ae
#print axioms HRTLambdaZero.tf_eq_chr
#print axioms HRTLambdaZero.finset_three_sum
#print axioms HRTLambdaZero.hrt_three_of_rot
#print axioms HRTLambdaZero.hrt_lambdaZero_triple2
#print axioms HRTLambdaZero.tf_three_shift
#print axioms HRTLambdaZero.tf_three_chirp
#print axioms HRTLambdaZero.hrt_lambdaZero_triple4
#print axioms HRTLambdaZero.hrt_three_of_shear
#print axioms HRTLambdaZero.hrt_lambdaZero_triple1
#print axioms HRTLambdaZero.hrt_lambdaZero_triple3
