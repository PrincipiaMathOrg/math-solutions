/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #365102 — the logarithmic-growth barycenter conjecture is FALSE

MathDB open problem #365102, from Conjecture 1 of arXiv:2410.02715v2.  For a potential `u`
satisfying the source's one-dimensional confinement hypothesis

  (2)  `lim_{|x|→∞} (u(x) − 2 log|x|) = +∞`,

the free Gibbs measure `ν_{u+λ·id}` exists and is unique, and the conjecture asserts that some
`λ ∈ ℝ` makes its barycenter zero.

**It is false**, already for the smooth potential

  `f(x) = 2 log(1 + (x−1)²)`.

* `f` satisfies (2) — `confinement`, with the explicit witness `R = 4 e^{C/2}`.
* `f` is symmetric about `1` (`f_reflect`), so the untilted functional is invariant under the
  reflection `r(x) = 2 − x`; by uniqueness its maximizer is `r`-invariant, and a reflection-
  invariant probability measure with a finite first moment has barycenter exactly `1`
  (`barycenter_eq_one`).  So `λ = 0` does not centre it.
* For every `λ ≠ 0` the tilted variational problem is **unbounded above**: pushing the uniform
  measure on `[−1,1]` a distance `t` against the tilt costs only `4 log(t+3)` in potential
  (`f_shift_le`) while gaining `|λ| t` from the tilt, and `|λ| t − 4 log(t+3) → ∞`
  (`tilt_exceeds`).  An unbounded problem has no maximizer, so no `λ ≠ 0` centres anything either.

## What is proved and what is assumed

Free entropy `χ` and free Gibbs measures are not in Mathlib, and formalizing them is a separate
project.  They appear here only through their two invariances, which the source uses and which are
immediate from `|r(s) − r(t)| = |s − t|` and translation invariance of the logarithmic energy.  So:

* everything about `f` itself — the confinement bound, the reflection symmetry, the displacement
  estimate, and the divergence — is **proved**;
* `barycenter_eq_one` is proved for an arbitrary reflection-invariant probability measure, so the
  step from uniqueness to "barycenter = 1" is proved, not assumed;
* what is *not* formalized is the source's quoted existence-and-uniqueness theorem, and the
  identification of `χ`.  `barycenter_eq_one` takes the invariance as a hypothesis, which is
  exactly what uniqueness delivers.

## Scope

This refutes the source's literal quantifier over every continuous `f` satisfying only (2).  `f`
grows like `4 log|x|`, so a linear tilt is non-confining in one direction.  It says **nothing**
about a repaired conjecture restricted to superlinear potentials, for which every linear tilt stays
confining — the source's own intended application forces exactly that stronger premise.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Principia.MathDB.P365102

open MeasureTheory

/-! ### The potential -/

/-- The counterexample potential `f(x) = 2 log(1 + (x−1)²)`. -/
noncomputable def f (x : ℝ) : ℝ := 2 * Real.log (1 + (x - 1) ^ 2)

theorem one_add_sq_pos (x : ℝ) : 0 < 1 + (x - 1) ^ 2 := by positivity

/-- **`f` is symmetric about `1`.**  This is what makes the untilted functional invariant under
the reflection `r(x) = 2 − x`. -/
theorem f_reflect (x : ℝ) : f (2 - x) = f x := by
  unfold f
  congr 2
  ring

/-! ### The confinement hypothesis (2) -/

/-- `x²/4 ≤ 1 + (x−1)²` for every `x`; the difference is `(3x−4)²/12 + 2/3`. -/
theorem quarter_sq_le (x : ℝ) : x ^ 2 / 4 ≤ 1 + (x - 1) ^ 2 := by
  nlinarith [sq_nonneg (3 * x - 4)]

/-- The pointwise form of the confinement estimate. -/
theorem f_sub_two_log_ge {x : ℝ} (hx : x ≠ 0) :
    2 * Real.log (|x| / 4) ≤ f x - 2 * Real.log |x| := by
  have habs : 0 < |x| := abs_pos.mpr hx
  have hsq : 0 < x ^ 2 / 4 := by positivity
  have hmono : Real.log (x ^ 2 / 4) ≤ Real.log (1 + (x - 1) ^ 2) :=
    Real.log_le_log hsq (quarter_sq_le x)
  have hxsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hsplit : Real.log (x ^ 2 / 4) = 2 * Real.log |x| - Real.log 4 := by
    rw [hxsq, Real.log_div (by positivity) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hquot : Real.log (|x| / 4) = Real.log |x| - Real.log 4 :=
    Real.log_div (ne_of_gt habs) (by norm_num)
  unfold f
  rw [hquot]
  linarith [hmono, hsplit]

/-- **`f` satisfies the source's hypothesis (2)**: `f(x) − 2 log|x| → +∞`, with the explicit
threshold `R = 4 e^{C/2}`. -/
theorem confinement (C : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ |x| → C ≤ f x - 2 * Real.log |x| := by
  refine ⟨4 * Real.exp (C / 2), by positivity, fun x hx => ?_⟩
  have hR : (0 : ℝ) < 4 * Real.exp (C / 2) := by positivity
  have habs : 0 < |x| := lt_of_lt_of_le hR hx
  have hx0 : x ≠ 0 := by
    intro hc
    rw [hc] at habs
    simp at habs
  have hexp : Real.exp (C / 2) ≤ |x| / 4 := by linarith
  have hlog : C / 2 ≤ Real.log (|x| / 4) := (Real.le_log_iff_exp_le (by positivity)).mpr hexp
  have := f_sub_two_log_ge hx0
  linarith

/-! ### The untilted equilibrium is centred at `1` -/

/-- **A reflection-invariant probability measure has barycenter `1`.**  This is the step the source
takes from uniqueness of the maximizer: `∫x = ∫(2−x) = 2 − ∫x`. -/
theorem barycenter_eq_one {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hinv : Measure.map (fun x => 2 - x) ν = ν) (hint : Integrable (fun x : ℝ => x) ν) :
    ∫ x, x ∂ν = 1 := by
  have hmeas : AEMeasurable (fun x : ℝ => 2 - x) ν :=
    (measurable_const.sub measurable_id).aemeasurable
  have h1 : ∫ x, x ∂ν = ∫ x, (2 - x) ∂ν := by
    conv_lhs => rw [← hinv]
    rw [MeasureTheory.integral_map hmeas measurable_id'.aestronglyMeasurable]
  have h2 : ∫ x, (2 - x) ∂ν = 2 - ∫ x, x ∂ν := by
    rw [MeasureTheory.integral_sub (integrable_const (2 : ℝ)) hint]
    simp
  linarith [h1, h2]

/-- …and `1 ≠ 0`, so the untilted equilibrium is not centred. -/
theorem untilted_not_centered {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hinv : Measure.map (fun x => 2 - x) ν = ν) (hint : Integrable (fun x : ℝ => x) ν) :
    (∫ x, x ∂ν) ≠ 0 := by
  rw [barycenter_eq_one hinv hint]
  norm_num

/-! ### Every nonzero tilt makes the problem unbounded -/

/-- Displacing the uniform measure on `[−1,1]` by `t` costs at most `4 log(t+3)` in potential. -/
theorem f_shift_le {y t s : ℝ} (hy : |y| ≤ 1) (ht : 0 ≤ t) (hs : |s| = 1) :
    f (y - s * t) ≤ 4 * Real.log (t + 3) := by
  have habs : |y - s * t - 1| ≤ t + 2 := by
    have h1 : |y - s * t - 1| ≤ |y| + |s * t| + |(1 : ℝ)| := by
      calc |y - s * t - 1| ≤ |y - s * t| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ |y| + |s * t| + |(1 : ℝ)| := by
            have := abs_sub y (s * t)
            linarith [abs_sub y (s * t)]
    have h2 : |s * t| = t := by rw [abs_mul, hs, abs_of_nonneg ht, one_mul]
    rw [h2] at h1
    simp only [abs_one] at h1
    linarith
  have hsq : (y - s * t - 1) ^ 2 ≤ (t + 2) ^ 2 := by
    have h0 : (0 : ℝ) ≤ t + 2 := by linarith
    nlinarith [abs_nonneg (y - s * t - 1), sq_abs (y - s * t - 1), habs]
  have hchain : 1 + (y - s * t - 1) ^ 2 ≤ (t + 3) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 + (y - s * t - 1) ^ 2 := by positivity
  have hlog : Real.log (1 + (y - s * t - 1) ^ 2) ≤ Real.log ((t + 3) ^ 2) :=
    Real.log_le_log hpos hchain
  have hexp : Real.log ((t + 3) ^ 2) = 2 * Real.log (t + 3) := by
    rw [Real.log_pow]
    push_cast
    ring
  unfold f
  rw [hexp] at hlog
  linarith

/-- `log x ≤ 2√x`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h
  linarith

theorem sqrt_shift_le {t : ℝ} (ht : 1 ≤ t) : Real.sqrt (t + 3) ≤ 2 * Real.sqrt t := by
  have h4 : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hle : t + 3 ≤ 4 * t := by linarith
  calc Real.sqrt (t + 3) ≤ Real.sqrt (4 * t) := Real.sqrt_le_sqrt hle
    _ = 2 * Real.sqrt t := h4

/-- **The tilted objective exceeds every bound.**  Along the escaping family the gain `|λ|t` beats
the potential cost `4 log(t+3)`, so the variational problem for `λ ≠ 0` is unbounded above. -/
theorem tilt_exceeds {lam : ℝ} (hlam : lam ≠ 0) (c0 C : ℝ) :
    ∃ t : ℝ, 0 < t ∧ C < c0 + |lam| * t - 4 * Real.log (t + 3) := by
  have hL : 0 < |lam| := abs_pos.mpr hlam
  set L := |lam| with hLdef
  refine ⟨1 + (32 / L) ^ 2 + 2 * |C - c0| / L, by positivity, ?_⟩
  set t : ℝ := 1 + (32 / L) ^ 2 + 2 * |C - c0| / L with htdef
  have ht1 : 1 ≤ t := by
    have : (0 : ℝ) ≤ (32 / L) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * |C - c0| / L := by positivity
    linarith
  have ht0 : 0 < t := by linarith
  have hsq : (32 / L) ^ 2 ≤ t := by
    have h2 : (0 : ℝ) ≤ 2 * |C - c0| / L := by positivity
    linarith
  -- `√t ≥ 32 / L`
  have hroot : 32 / L ≤ Real.sqrt t := by
    have hnn : (0 : ℝ) ≤ 32 / L := by positivity
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hnn] at this
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  -- `4 log(t+3) ≤ 16 √t ≤ (L/2) t`
  have hlog : 4 * Real.log (t + 3) ≤ 16 * Real.sqrt t := by
    have h1 : Real.log (t + 3) ≤ 2 * Real.sqrt (t + 3) := log_le_two_sqrt (by linarith)
    have h2 : Real.sqrt (t + 3) ≤ 2 * Real.sqrt t := sqrt_shift_le ht1
    linarith
  have hcmp : 16 * Real.sqrt t ≤ L / 2 * t := by
    have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    have h32 : 32 ≤ L * Real.sqrt t := by
      have := (div_le_iff₀ hL).mp hroot
      linarith
    nlinarith [hst, hs0, h32]
  -- and `(L/2) t` beats `C - c0`
  have hbeat : C - c0 < L / 2 * t := by
    have habs : C - c0 ≤ |C - c0| := le_abs_self _
    have hkey : |C - c0| = L / 2 * (2 * |C - c0| / L) := by field_simp
    have hrest : (0 : ℝ) < L / 2 * (1 + (32 / L) ^ 2) := by positivity
    have hexp : L / 2 * t = L / 2 * (1 + (32 / L) ^ 2) + L / 2 * (2 * |C - c0| / L) := by
      rw [htdef]
      ring
    linarith
  linarith

/-- **The tilted functional itself is unbounded above.**  This is `(9)` of the source, assembled.

Along the escaping family `μ_t` (the uniform measure on `[-1,1]` translated by `-s t`) the tilted
objective is `chi t - pot t + |λ| t`, where `chi t` is the free entropy and `pot t = ∫ f dμ_t`.
The two inputs are exactly:

* `hchi` — free entropy is **translation invariant**, so `chi t` is the constant `chi₀`.  This is
  the one genuinely load-bearing fact this file does not prove, because `χ` is not formalized; it
  is stated here as a hypothesis rather than left in prose, so nothing is hidden.
* `hpot` — the potential cost is at most `4 log(t+3)`.  This is `f_shift_le` integrated against a
  probability measure supported in `[-1,1]`: a pointwise bound on `f` integrates to the same bound.

Given those, the conclusion is the divergence, and it is proved. -/
theorem tilted_functional_unbounded {chi pot : ℝ → ℝ} (chi₀ : ℝ)
    (hchi : ∀ t : ℝ, chi t = chi₀)
    (hpot : ∀ t : ℝ, 0 ≤ t → pot t ≤ 4 * Real.log (t + 3))
    {lam : ℝ} (hlam : lam ≠ 0) (C : ℝ) :
    ∃ t : ℝ, 0 < t ∧ C < chi t - pot t + |lam| * t := by
  obtain ⟨t, ht0, hgt⟩ := tilt_exceeds hlam chi₀ C
  refine ⟨t, ht0, ?_⟩
  have hp := hpot t ht0.le
  have hc := hchi t
  rw [hc]
  linarith

end Principia.MathDB.P365102
