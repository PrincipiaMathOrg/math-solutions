import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# MathDB #363590 -- benign non-convexity fails for a two-dimensional Gaussian

Write-up `mathdb-open-problems/problems/363590/solution.tex`,
*Gaussian counterexamples to benign non-convexity in dimensional logarithmic Sobolev
optimization*, 22 September 2026.
Source: M. T. C. Li, T. Cui, F. Li, Y. Marzouk and O. Zahm, *Sharp detection of
low-dimensional structure in probability measures via dimensional logarithmic Sobolev
inequalities*, Information and Inference 14(3) (2025), iaaf021, **Conjecture 2.6**
(equivalently arXiv:2406.13036v3); the majorant is the source's equation (20)/Appendix D.2.

Conjecture 2.6 asserts *benign non-convexity* on `Gr(d, r)`: every local minimum of the
objective is global.  The witness is `d = 2`, `r = 1`, reference `mu = N(0, I_2)`, target
`pi = N(0, C)` with `C = diag(1/2, 2)`; then `M = E[XX^T] = C` and
`H = E[grad log pi grad log pi^T] = C^{-1} = diag(2, 1/2)`.

Writing `u(θ) = (cos θ, sin θ)` and `v(θ) = (-sin θ, cos θ)`, `z θ = u^T C u` and the
source's majorant collapses to `J θ = (3/2 - z θ + log (z θ))/2` (`majorant_eq`, assembled
from the entries of `M` and `H` -- no `Matrix` type appears).  `kl_eq` checks the source's
own Proposition 4 for this instance: the centered-Gaussian KL formula against the optimal
profile `D = I + (z-1)uu^T` returns the SAME function, so what is refuted is the genuine
approximation loss and not merely a bound.

**What is proved.**  `strict_min_zero` and `strict_min_pi_div_two`: both coordinate lines
are strict local minima.  `not_global`: `J(pi/2) < J(0)`, the difference being
`3/4 - log 2 > 0`.  `not_conj`: Conjecture 2.6 is false.

**The Lean takes a stronger route than the write-up.**  The write-up establishes local
minimality with the second-derivative test (`J''(0) = 3/2`, `J''(pi/2) = 3/4`), which is an
infinitesimal statement.  Here the same conclusion comes from exact monotonicity: `J` is a
function of `z` alone, and `x -> (3/2 - x + log x)/2` is strictly increasing below `1` and
strictly decreasing above it (`g_lt`, `g_lt'`, each one application of
`Real.log_lt_sub_one_of_pos`).  So minimality is proved on an EXPLICIT neighbourhood --
every line with `0 < |sin θ| < 1/2`, respectively `0 < |cos θ| < 1/2` -- with no derivative,
no Hessian and no smoothness argument anywhere in the module.

**The statement `Conj` is the weakest reading the witness kills.**  Its hypothesis is
*strict* local minimality, which is stronger than the plain local minimality of the source's
phrasing, so `not_conj` refutes the source's statement a fortiori.  Distance on `Gr(2,1)` is
`|sin (θ - θ₀)|`, the sine of the angle between the two lines, which is the standard metric;
`sin (θ - θ₀) ≠ 0` says exactly that the lines are distinct.

**The modelling step, stated rather than hidden.**  That `N(0, C)` is a probability measure
with `M = C` and `H = C^{-1}`, and that its density ratio against `N(0, I_2)` is smooth and
positive (it is `exp(-x_1^2/2 + x_2^2/4)` up to normalization, so the source's hypotheses
hold -- the source assumes a smooth positive ratio, not a bounded one nor `C <= I_2`), is
classical Gaussian bookkeeping taken as given; `H_eq_C_inv` records the entrywise inverse
relation.  Everything downstream of `M` and `H` is proved.

**Not formalized, and not needed.**  The write-up adds a second theorem refuting the
landscape claim for the sign convention actually PRINTED in the source's equation (18),
via a perturbed target `N(m_delta, C)`, the implicit function theorem and a
non-explicit `delta_0`.  The write-up states that "the resolution therefore does not rest on
detecting the sign error": the refutation above is of the intended objective, is complete on
its own, and is the one certified here.

Values checked first in `Campaigns/MathDB-Formalization/verify_363590.py`.
-/

namespace Principia.MathDB.P363590

open Real

/-- `z θ = u(θ)ᵀ C u(θ)` for `u(θ) = (cos θ, sin θ)` and `C = diag(1/2, 2)`. -/
noncomputable def z (θ : ℝ) : ℝ := 1 / 2 + 3 / 2 * Real.sin θ ^ 2

/-- `z` is the quadratic form of `C = diag(1/2, 2)` along `u(θ)`. -/
theorem z_eq_quad (θ : ℝ) :
    (1 / 2) * Real.cos θ ^ 2 + 2 * Real.sin θ ^ 2 = z θ := by
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [z]; linarith

/-- `H = C⁻¹` for a centered Gaussian target, entrywise. -/
theorem H_eq_C_inv : (2 : ℝ) = (1 / 2 : ℝ)⁻¹ ∧ (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by
  constructor <;> norm_num

/-- Along the complementary direction `v(θ) = (-sin θ, cos θ)`, `vᵀ M v = 5/2 - z`
for `M = C`. -/
theorem vMv (θ : ℝ) :
    (1 / 2) * Real.sin θ ^ 2 + 2 * Real.cos θ ^ 2 = 5 / 2 - z θ := by
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [z]; linarith

/-- And `vᵀ H v = z` for `H = C⁻¹ = diag(2, 1/2)`. -/
theorem vHv (θ : ℝ) :
    2 * Real.sin θ ^ 2 + (1 / 2) * Real.cos θ ^ 2 = z θ := by
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [z]; linarith

/-- The source's majorant (20)/(1) at `d = 2`, `r = 1`. -/
noncomputable def J (θ : ℝ) : ℝ := (3 / 2 - z θ + Real.log (z θ)) / 2

/-- `J` IS the source's majorant, assembled from `M` and `H` entrywise. -/
theorem majorant_eq (θ : ℝ) :
    ((1 / 2) * Real.sin θ ^ 2 + 2 * Real.cos θ ^ 2 - 1
      + Real.log (2 * Real.sin θ ^ 2 + (1 / 2) * Real.cos θ ^ 2)) / 2 = J θ := by
  rw [vMv, vHv, J]; ring

theorem z_pos (θ : ℝ) : 0 < z θ := by
  have : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  rw [z]; linarith

/-- `tr(D⁻¹ C) = 7/2 - z` for the source's optimal profile `D = I + (z-1)uuᵀ`. -/
theorem trace_Dinv_C (θ : ℝ) :
    (1 + (1 / z θ - 1) * Real.cos θ ^ 2) * (1 / 2)
      + (1 + (1 / z θ - 1) * Real.sin θ ^ 2) * 2 = 7 / 2 - z θ := by
  have hz : z θ ≠ 0 := ne_of_gt (z_pos θ)
  have key : (1 / z θ - 1) * z θ = 1 - z θ := by field_simp
  have hq := z_eq_quad θ
  linear_combination (1 / z θ - 1) * hq + key

/-- **The refuted object is the genuine approximation loss**, not only a majorant: the
centered-Gaussian KL formula for `D_KL(N(0,C) ‖ N(0,D))` returns `J` exactly.  This is the
source's own Proposition 4, verified directly for this instance. -/
theorem kl_eq (θ : ℝ) :
    (Real.log (z θ) - Real.log 1 - 2
      + ((1 + (1 / z θ - 1) * Real.cos θ ^ 2) * (1 / 2)
        + (1 + (1 / z θ - 1) * Real.sin θ ^ 2) * 2)) / 2 = J θ := by
  rw [trace_Dinv_C, Real.log_one, J]; ring

theorem z_zero : z 0 = 1 / 2 := by
  rw [z, Real.sin_zero]; norm_num

theorem z_pi_div_two : z (π / 2) = 2 := by
  rw [z, Real.sin_pi_div_two]; norm_num

theorem J_zero : J 0 = (1 - Real.log 2) / 2 := by
  rw [J, z_zero, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

theorem J_pi_div_two : J (π / 2) = (-(1 / 2) + Real.log 2) / 2 := by
  rw [J, z_pi_div_two]; ring

/-- Below `1` the map `x ↦ (3/2 - x + log x)/2` is strictly increasing. -/
theorem g_lt (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) :
    (3 / 2 - a + Real.log a) / 2 < (3 / 2 - b + Real.log b) / 2 := by
  have hb0 : 0 < b := lt_trans ha hab
  have hne : a / b ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq (ne_of_gt hb0)] at h
    linarith
  have hlog := Real.log_lt_sub_one_of_pos (div_pos ha hb0) hne
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb0)] at hlog
  have hdiv : a / b - 1 = (a - b) / b := by field_simp
  rw [hdiv] at hlog
  have hle : (a - b) / b ≤ a - b := by
    rw [div_le_iff₀ hb0]; nlinarith
  linarith

/-- Above `1` it is strictly decreasing. -/
theorem g_lt' (a b : ℝ) (ha : 1 ≤ a) (hab : a < b) :
    (3 / 2 - b + Real.log b) / 2 < (3 / 2 - a + Real.log a) / 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hb0 : 0 < b := lt_trans ha0 hab
  have hne : b / a ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq (ne_of_gt ha0)] at h
    linarith
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hb0 ha0) hne
  rw [Real.log_div (ne_of_gt hb0) (ne_of_gt ha0)] at hlog
  have hdiv : b / a - 1 = (b - a) / a := by field_simp
  rw [hdiv] at hlog
  have hle : (b - a) / a ≤ b - a := by
    rw [div_le_iff₀ ha0]; nlinarith
  linarith

/-- **The line spanned by `e₁` is a strict local minimum.**  `|sin θ|` is the standard
distance on `Gr(2,1)` between the line at angle `θ` and the one at angle `0`, and
`sin θ ≠ 0` says the two lines are distinct. -/
theorem strict_min_zero (θ : ℝ) (h0 : Real.sin θ ≠ 0) (hlt : |Real.sin θ| < 1 / 2) :
    J 0 < J θ := by
  have hs : 0 < Real.sin θ ^ 2 := by positivity
  obtain ⟨hl, hr⟩ := abs_lt.mp hlt
  have hs2 : Real.sin θ ^ 2 < 1 / 4 := by nlinarith
  have h1 : (1 : ℝ) / 2 < z θ := by rw [z]; linarith
  have h2 : z θ ≤ 1 := by rw [z]; linarith
  simp only [J, z_zero]
  exact g_lt (1 / 2) (z θ) (by norm_num) h1 h2

/-- **The line spanned by `e₂` is also a strict local minimum.** -/
theorem strict_min_pi_div_two (θ : ℝ) (h0 : Real.cos θ ≠ 0) (hlt : |Real.cos θ| < 1 / 2) :
    J (π / 2) < J θ := by
  have hc : 0 < Real.cos θ ^ 2 := by positivity
  obtain ⟨hl, hr⟩ := abs_lt.mp hlt
  have hc2 : Real.cos θ ^ 2 < 1 / 4 := by nlinarith
  have hpy : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h1 : (1 : ℝ) ≤ z θ := by rw [z]; linarith
  have h2 : z θ < 2 := by rw [z]; linarith
  simp only [J, z_pi_div_two]
  exact g_lt' (z θ) 2 h1 h2

theorem log_two_lt_three_quarters : Real.log 2 < 3 / 4 :=
  lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num)

/-- **The `e₁` minimum is not global**: the difference is `3/4 - log 2 > 0`. -/
theorem not_global : J (π / 2) < J 0 := by
  rw [J_zero, J_pi_div_two]
  have := log_two_lt_three_quarters
  linarith

/-- Benign non-convexity (source Conjecture 2.6) for this instance: on `Gr(2,1)`, where the
distance between the lines at angles `θ` and `θ₀` is `|sin (θ - θ₀)|`, every strict local
minimum of the objective is global.  This is the WEAKEST reading the witness kills: the
hypothesis demands only that `θ₀` beat every distinct line within SOME positive distance. -/
def Conj : Prop :=
  ∀ θ₀ : ℝ,
    (∃ δ > 0, ∀ θ : ℝ, Real.sin (θ - θ₀) ≠ 0 → |Real.sin (θ - θ₀)| < δ → J θ₀ < J θ) →
    ∀ θ : ℝ, J θ₀ ≤ J θ

/-- **Conjecture 2.6 is false.** -/
theorem not_conj : ¬ Conj := by
  intro h
  have hloc : ∃ δ > 0, ∀ θ : ℝ,
      Real.sin (θ - 0) ≠ 0 → |Real.sin (θ - 0)| < δ → J 0 < J θ := by
    refine ⟨1 / 2, by norm_num, fun θ h1 h2 => ?_⟩
    rw [sub_zero] at h1 h2
    exact strict_min_zero θ h1 h2
  have hglob := h 0 hloc (π / 2)
  linarith [not_global]

end Principia.MathDB.P363590
