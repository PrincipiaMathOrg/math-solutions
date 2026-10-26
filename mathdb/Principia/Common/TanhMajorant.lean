import Mathlib

/-!
# `tanh y ≤ y`, and the majorant `g(u) = u(1-u)/(1+u)²`

Two things Mathlib does not have, promoted out of MathDB #360139 (the Fibonacci characteristic
function), which paid for them.  Neither mentions a substitution, a Fibonacci word or a generating
function: they are facts about `tanh` and about one rational function of a real variable.

**The Mathlib gap is real and was re-grepped.**  Mathlib has `Real.tanh_eq_sinh_div_cosh`,
`Real.self_lt_sinh` and the whole `artanh` development, but neither `tanh y ≤ y` nor the
`sinh y ≤ y·cosh y` it rests on.  The proof is the obvious one — the difference `y·cosh y - sinh y`
has derivative `y·sinh y ≥ 0` — and it is recorded here so the next campaign does not redo it.

**Why the majorant travels with it.**  `g(u) = u(1-u)/(1+u)²` is a real function with three
elementary bounds, and the only one that is not `nlinarith` is `g(e^{-x}) ≤ x/4`, which is exactly
where `tanh_le_self` is spent: writing `g(u) = [u/(1+u)]·[(1-u)/(1+u)]`, the first factor is
`1/(eˣ+1) ≤ 1/2` and **the second factor IS `tanh(x/2)`**.  Bounding that second factor by `x`
rather than by `x/2` costs a factor of two in the conclusion, which is the kind of slack that
silently breaks a downstream constant — so the sharp form is the one worth keeping.

`gfun_le_eighth` is sharp: `1/8 - g(u) = (3u-1)²/(8(1+u)²)`, attained at `u = 1/3`.
-/

namespace Principia.Common

open Real

/-- `sinh y ≤ y · cosh y` for `y ≥ 0`.  The difference has derivative `y · sinh y ≥ 0`. -/
theorem sinh_le_mul_cosh {y : ℝ} (hy : 0 ≤ y) : sinh y ≤ y * cosh y := by
  have hderiv : ∀ z : ℝ, HasDerivAt (fun w : ℝ => w * cosh w - sinh w) (z * sinh z) z := by
    intro z
    have h1 : HasDerivAt (fun w : ℝ => w * cosh w) (1 * cosh z + z * sinh z) z :=
      (hasDerivAt_id z).mul (Real.hasDerivAt_cosh z)
    have h2 := h1.sub (Real.hasDerivAt_sinh z)
    have he : 1 * cosh z + z * sinh z - cosh z = z * sinh z := by ring
    exact he ▸ h2
  have hmono : MonotoneOn (fun w : ℝ => w * cosh w - sinh w) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun z _ => ((hderiv z).differentiableAt).continuousAt.continuousWithinAt
    · exact fun z _ => ((hderiv z).differentiableAt).differentiableWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      rw [(hderiv z).deriv]
      exact mul_nonneg (le_of_lt hz) (sinh_nonneg_iff.mpr (le_of_lt hz))
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hy) hy
  simp only [cosh_zero, sinh_zero, zero_mul, sub_self] at h
  linarith

/-- **`tanh y ≤ y` for `y ≥ 0`.**  Absent from Mathlib (grepped): it has
`tanh_eq_sinh_div_cosh`, `self_lt_sinh` and the `artanh` development, but not this. -/
theorem tanh_le_self {y : ℝ} (hy : 0 ≤ y) : tanh y ≤ y := by
  rw [tanh_eq_sinh_div_cosh, div_le_iff₀ (cosh_pos y)]
  exact sinh_le_mul_cosh hy

/-- The majorant `g(u) = u(1-u)/(1+u)²`. -/
noncomputable def gfun (u : ℝ) : ℝ := u * (1 - u) / (1 + u) ^ 2

/-- **Sharp.**  `1/8 - g(u) = (3u-1)²/(8(1+u)²)`, so the bound is attained at `u = 1/3`. -/
theorem gfun_le_eighth {u : ℝ} (hu : 0 ≤ u) : gfun u ≤ 1 / 8 := by
  have hpos : (0 : ℝ) < (1 + u) ^ 2 := by positivity
  rw [gfun, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (3 * u - 1), sq_nonneg u]

/-- `u - g(u) = u²(u+3)/(1+u)²`, so `g(u) ≤ u` on `[0,1]` — the far-tail bound. -/
theorem gfun_le_self {u : ℝ} (hu : 0 ≤ u) : gfun u ≤ u := by
  have hpos : (0 : ℝ) < (1 + u) ^ 2 := by positivity
  rw [gfun, div_le_iff₀ hpos]
  nlinarith [sq_nonneg u, mul_nonneg hu hu]

/-- `g` is nonnegative on `[0,1]`. -/
theorem gfun_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ gfun u := by
  rw [gfun]
  have hpos : (0 : ℝ) < (1 + u) ^ 2 := by positivity
  apply div_nonneg _ (le_of_lt hpos)
  nlinarith

/-- The factor `u/(1+u) = 1/(eˣ+1)` never exceeds `1/2` for `u ≤ 1`. -/
theorem half_factor {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : u / (1 + u) ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **The bound that consumes `tanh_le_self`.**  `g(e^{-x}) ≤ x/4`.

Writing `u = e^{-x}`, `g(u) = [u/(1+u)]·[(1-u)/(1+u)]`; the first factor is `1/(eˣ+1) ≤ 1/2`
and the second is exactly `tanh(x/2) ≤ x/2`.  Using `≤ x` for the second factor instead
would give `x/2` here, a factor of two of avoidable slack. -/
theorem gfun_exp_le_quarter {x : ℝ} (hx : 0 ≤ x) : gfun (exp (-x)) ≤ x / 4 := by
  set u : ℝ := exp (-x) with hu
  have hu0 : 0 < u := exp_pos _
  have hu1 : u ≤ 1 := by
    rw [hu, exp_le_one_iff]
    linarith
  -- the second factor IS `tanh (x/2)`
  have hE : (0 : ℝ) < exp (x / 2) := exp_pos _
  have hsq : u = (exp (x / 2))⁻¹ * (exp (x / 2))⁻¹ := by
    rw [hu, ← exp_neg, ← exp_add]
    congr 1
    ring
  have htanh : (1 - u) / (1 + u) = tanh (x / 2) := by
    rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, hsq, exp_neg]
    field_simp
  have hfac : gfun u = (u / (1 + u)) * ((1 - u) / (1 + u)) := by
    rw [gfun]; field_simp
  have hsecond : (1 - u) / (1 + u) ≤ x / 2 := by
    rw [htanh]
    exact le_trans (tanh_le_self (by linarith)) (le_refl _)
  have hsnn : 0 ≤ (1 - u) / (1 + u) := by
    apply div_nonneg (by linarith) (by linarith)
  have hfirst : u / (1 + u) ≤ 1 / 2 := half_factor (le_of_lt hu0) hu1
  have hfnn : 0 ≤ u / (1 + u) := div_nonneg (le_of_lt hu0) (by linarith)
  calc gfun u = (u / (1 + u)) * ((1 - u) / (1 + u)) := hfac
    _ ≤ (1 / 2) * (x / 2) := by
        apply mul_le_mul hfirst hsecond hsnn (by norm_num)
    _ = x / 4 := by ring

end Principia.Common
