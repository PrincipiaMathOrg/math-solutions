/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# Convexity on the nonnegative orthant, and its passage through an integral

**PROMOTED to `Common/` on 2026-09-24**, out of MathDB #347913, which paid for it.  The
promotion test the project actually applies is whether a declaration mentions the campaign's
objects, and not one of these four does: there is no hypergraph, no edge family and no
`f_d` below.  #347913's own row had recorded `integral_convexOn` as campaign-agnostic and a
`Common/` candidate since it was written; the base moves first, so `orthant` and
`convex_orthant` come with it rather than being left behind under `MathDB/` with their
consumers above them.

## What is here

* `orthant` and `convex_orthant` — the nonnegative orthant of `ι → ℝ` and its convexity.
* `pow_linear_convexOn` — for nonnegative weights `Y`, the map `x ↦ (∑ i, x i · Y i)^d` is
  convex on the orthant.  A `d`-th power of a NONNEGATIVE linear form; the nonnegativity is
  what lets `convexOn_pow` apply, since `t ↦ t^d` is convex on `[0,∞)` and not on `ℝ` for
  odd `d`.
* `integral_convexOn` — convexity passes from an integrand to its integral.

## The integrability side conditions are not pedantry

In Mathlib `∫` of a non-integrable function is `0`.  Without the hypothesis
`∀ x ∈ orthant ι, Integrable (fun ω => g x ω) μ` the conclusion of `integral_convexOn` is
FALSE, not merely unprovable: a `g` that is integrable at the endpoints and not at their
midpoint would make the left-hand side `0` while the right-hand side stayed positive.  The
hypothesis is exactly what makes `integral_mono` applicable, and any probabilistic setting
that produces such a `g` supplies it.
-/
import Mathlib

set_option autoImplicit false

open Finset MeasureTheory

namespace Principia.Common.ConvexIntegral

variable {ι : Type*}

/-- The nonnegative orthant. -/
def orthant (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, 0 ≤ x i}

theorem convex_orthant : Convex ℝ (orthant ι) := by
  intro x hx y hy a b ha hb _ i
  have := hx i
  have := hy i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  positivity

/-- **A `d`-th power of a nonnegative linear form is convex on the orthant.** -/
theorem pow_linear_convexOn [Fintype ι] (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) (d : ℕ) :
    ConvexOn ℝ (orthant ι) (fun x : ι → ℝ => (∑ i, x i * Y i) ^ d) := by
  refine ⟨convex_orthant, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp only
  have hLx : (0 : ℝ) ≤ ∑ i, x i * Y i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hY i))
  have hLy : (0 : ℝ) ≤ ∑ i, y i * Y i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hy i) (hY i))
  have hL : ∑ i, (a • x + b • y) i * Y i
      = a * (∑ i, x i * Y i) + b * (∑ i, y i * Y i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
  rw [hL]
  exact (convexOn_pow d).2 (Set.mem_Ici.mpr hLx) (Set.mem_Ici.mpr hLy) ha hb hab

/-- **Convexity passes through an integral.**  Stated with the integrability side conditions
that the conclusion is false without — see the header. -/
theorem integral_convexOn {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (ι → ℝ) → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ (orthant ι) (fun x => g x ω))
    (hint : ∀ x ∈ orthant ι, Integrable (fun ω => g x ω) μ) :
    ConvexOn ℝ (orthant ι) (fun x => ∫ ω, g x ω ∂μ) := by
  refine ⟨convex_orthant, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp only
  have hmem : a • x + b • y ∈ orthant ι := convex_orthant hx hy ha hb hab
  have hIx := hint x hx
  have hIy := hint y hy
  have hIz := hint _ hmem
  have hle : (fun ω => g (a • x + b • y) ω) ≤ fun ω => a * g x ω + b * g y ω := by
    intro ω
    have h := (hconv ω).2 hx hy ha hb hab
    simpa [smul_eq_mul] using h
  have hstep : ∫ ω, g (a • x + b • y) ω ∂μ ≤ ∫ ω, (a * g x ω + b * g y ω) ∂μ :=
    integral_mono hIz ((hIx.const_mul a).add (hIy.const_mul b)) hle
  have hsplit : ∫ ω, (a * g x ω + b * g y ω) ∂μ
      = a * ∫ ω, g x ω ∂μ + b * ∫ ω, g y ω ∂μ := by
    rw [integral_add (hIx.const_mul a) (hIy.const_mul b), integral_const_mul,
      integral_const_mul]
  rw [hsplit] at hstep
  simpa [smul_eq_mul] using hstep

end Principia.Common.ConvexIntegral
