import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MathDB #339682 — an anisotropic Gaussian counterexample to observable-gradient coupling

Write-up: `mathdb-open-problems/problems/339682/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Nüsken and Pavliotis, **Conjecture 62, equation (157)** of the final publication
(Conjecture 60 on arXiv).  For the overdamped generator `L = −∇V·∇ + Δ`, centred
`f, φ ∈ L²(π)` with `−Lφ = f` and `π(dx) = Z⁻¹e^{−V(x)}dx`, it asserts

`∫∫ ∇φ(y)ᵀ α_f(x,y) ∇φ(x) e^{−V(x)−V(y)} dx dy ≤ 0`,

with `α_f(x,y) = I − 2wwᵀ/‖w‖²`, `w(x,y) = ∇f(x)/‖∇f(x)‖ + ∇f(y)/‖∇f(y)‖`, and the source's
admissibility requirement `α_fᵀα_f ≤ I`.

Witness: `V(x) = (x₁² + 9x₂²)/2`, `f(x) = x₁ + 3x₂`, `φ(x) = x₁ + x₂/3`, `d = 2`.

## Why this row was mis-deferred

Deferred 2026-09-16 as "needs the generator, weighted `L²` and Gaussian integrals of
gradients".  For this witness **`∇f = (1,3)` is constant**, so `w = 2∇f/‖∇f‖` is constant
and nonzero — the non-degenerate branch of `α_f` applies everywhere — and `α_f` is one
fixed matrix.  `∇φ = (1,1/3)` is constant too.  The integrand is therefore a **constant
scalar** times `e^{−V(x)−V(y)}`, and the conjecture's sign is settled by that scalar.  No
integral of a gradient is ever taken.

## What is proved

* `poisson` — `−Lφ = f`, i.e. `∇V·∇φ − Δφ = f`, with every partial derivative obtained
  from `HasDerivAt`, not assumed.  This is the conjecture's own hypothesis on the witness.
* `al_orthogonal` — `αᵀα = I` entrywise, so the source's admissibility holds (with
  equality: `α` is a Householder reflection).
* `scalar_eq` and `scalar_pos` — `∇φᵀ α ∇φ = 14/45 > 0`.
* `gauss_one`, `gauss_nine` — the two one-dimensional Gaussian integrals,
  `√(2π)` and `√(2π)/3`.
* `Z_eq` — `Z = ∫ e^{−V} = 2π/3`, as the product of those two.
* `not_conj` — the integrand is everywhere positive, and the value `(14/45)·Z² = 56π²/405`
  is positive, contradicting `≤ 0`.

**The one step not formalized**, and stated here rather than buried: that the double
integral over `ℝ²×ℝ²` equals `(∇φᵀα∇φ)·Z²`.  That is Fubini–Tonelli for a product of
Gaussians against a constant, and it is the only gap; everything the refutation turns on —
the Poisson equation, admissibility, the sign of the scalar, and `Z` — is proved.  The
positivity of the integrand (`integrand_pos`) is what makes the conclusion independent of
that step's exact constant.

Values checked in `Campaigns/MathDB-Formalization/verify_339682.py`.
-/

namespace Principia.MathDB.P339682

open Real MeasureTheory

/-! ### The witness -/

noncomputable def Vp (x1 x2 : ℝ) : ℝ := (x1 ^ 2 + 9 * x2 ^ 2) / 2

def fp (x1 x2 : ℝ) : ℝ := x1 + 3 * x2

noncomputable def phip (x1 x2 : ℝ) : ℝ := x1 + x2 / 3

/-! ### The partial derivatives, computed -/

theorem hV1 (x1 x2 : ℝ) : HasDerivAt (fun t => Vp t x2) x1 x1 := by
  have h := ((hasDerivAt_pow 2 x1).add_const (9 * x2 ^ 2)).div_const 2
  have e : ((2 : ℕ) : ℝ) * x1 ^ (2 - 1) / 2 = x1 := by norm_num
  rw [e] at h
  exact h

theorem hV2 (x1 x2 : ℝ) : HasDerivAt (fun t => Vp x1 t) (9 * x2) x2 := by
  have h := (((hasDerivAt_pow 2 x2).const_mul (9 : ℝ)).const_add (x1 ^ 2)).div_const 2
  have e : (9 : ℝ) * (((2 : ℕ) : ℝ) * x2 ^ (2 - 1)) / 2 = 9 * x2 := by norm_num; ring
  rw [e] at h
  exact h

theorem hp1 (x1 x2 : ℝ) : HasDerivAt (fun t => phip t x2) 1 x1 :=
  (hasDerivAt_id x1).add_const (x2 / 3)

theorem hp2 (x1 x2 : ℝ) : HasDerivAt (fun t => phip x1 t) (1 / 3) x2 :=
  ((hasDerivAt_id x2).div_const 3).const_add x1

theorem dV1 (x1 x2 : ℝ) : deriv (fun t => Vp t x2) x1 = x1 := (hV1 x1 x2).deriv
theorem dV2 (x1 x2 : ℝ) : deriv (fun t => Vp x1 t) x2 = 9 * x2 := (hV2 x1 x2).deriv
theorem dp1 (x1 x2 : ℝ) : deriv (fun t => phip t x2) x1 = 1 := (hp1 x1 x2).deriv
theorem dp2 (x1 x2 : ℝ) : deriv (fun t => phip x1 t) x2 = 1 / 3 := (hp2 x1 x2).deriv

/-- `∂²φ/∂x₁² = 0`: the first partial is constantly `1`. -/
theorem d2p1 (x1 x2 : ℝ) : deriv (fun s => deriv (fun t => phip t x2) s) x1 = 0 := by
  have h : (fun s => deriv (fun t => phip t x2) s) = fun _ : ℝ => (1 : ℝ) := by
    funext s; exact dp1 s x2
  rw [h, deriv_const]

/-- `∂²φ/∂x₂² = 0`: the second partial is constantly `1/3`. -/
theorem d2p2 (x1 x2 : ℝ) : deriv (fun s => deriv (fun t => phip x1 t) s) x2 = 0 := by
  have h : (fun s => deriv (fun t => phip x1 t) s) = fun _ : ℝ => (1 / 3 : ℝ) := by
    funext s; exact dp2 x1 s
  rw [h, deriv_const]

/-- **The witness satisfies the conjecture's hypothesis `−Lφ = f`**, i.e.
`∇V·∇φ − Δφ = f`. -/
theorem poisson (x1 x2 : ℝ) :
    deriv (fun t => Vp t x2) x1 * deriv (fun t => phip t x2) x1
        + deriv (fun t => Vp x1 t) x2 * deriv (fun t => phip x1 t) x2
        - (deriv (fun s => deriv (fun t => phip t x2) s) x1
          + deriv (fun s => deriv (fun t => phip x1 t) s) x2)
      = fp x1 x2 := by
  rw [dV1, dV2, dp1, dp2, d2p1, d2p2, fp]
  ring

/-! ### The coupling matrix, as a Householder reflection -/

/-- `v = ∇f = (1,3)`, constant. -/
noncomputable def vv : Fin 2 → ℝ := fun i => if i = 0 then 1 else 3

/-- `∇φ = (1,1/3)`, constant. -/
noncomputable def gphi : Fin 2 → ℝ := fun i => if i = 0 then 1 else 1 / 3

/-- `α_f = I − 2vvᵀ/‖v‖²` entrywise, with `‖v‖² = 10`. -/
noncomputable def al (i j : Fin 2) : ℝ :=
  (if i = j then 1 else 0) - 2 * (vv i * vv j) / 10

theorem al_00 : al 0 0 = 4 / 5 := by norm_num [al, vv]
theorem al_01 : al 0 1 = -3 / 5 := by norm_num [al, vv]
theorem al_10 : al 1 0 = -3 / 5 := by norm_num [al, vv]
theorem al_11 : al 1 1 = -4 / 5 := by norm_num [al, vv]

/-- **`αᵀα = I`**: the source's admissibility `αᵀα ≤ I` holds, with equality. -/
theorem al_orthogonal (i j : Fin 2) :
    (∑ k : Fin 2, al k i * al k j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, al_00, al_01, al_10, al_11] <;> norm_num

/-- **The constant scalar `∇φᵀ α ∇φ = 14/45`.** -/
theorem scalar_eq : (∑ i : Fin 2, ∑ j : Fin 2, gphi i * al i j * gphi j) = 14 / 45 := by
  simp [Fin.sum_univ_two, gphi, al_00, al_01, al_10, al_11]
  norm_num

theorem scalar_pos : (0 : ℝ) < ∑ i : Fin 2, ∑ j : Fin 2, gphi i * al i j * gphi j := by
  rw [scalar_eq]; norm_num

/-! ### The Gaussian integrals -/

theorem gauss_one : (∫ t : ℝ, Real.exp (-(t ^ 2) / 2)) = Real.sqrt (2 * π) := by
  have h : (∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2)) = Real.sqrt (π / (1 / 2)) :=
    integral_gaussian (1 / 2)
  have he : ∀ t : ℝ, -(t ^ 2) / 2 = -(1 / 2 : ℝ) * t ^ 2 := by intro t; ring
  simp only [he, h]
  rw [show π / (1 / 2 : ℝ) = 2 * π by ring]

theorem gauss_nine : (∫ t : ℝ, Real.exp (-(9 * t ^ 2) / 2)) = Real.sqrt (2 * π) / 3 := by
  have h : (∫ t : ℝ, Real.exp (-(9 / 2 : ℝ) * t ^ 2)) = Real.sqrt (π / (9 / 2)) :=
    integral_gaussian (9 / 2)
  have he : ∀ t : ℝ, -(9 * t ^ 2) / 2 = -(9 / 2 : ℝ) * t ^ 2 := by intro t; ring
  simp only [he, h]
  rw [show π / (9 / 2 : ℝ) = (2 * π) * (1 / 9) by ring, Real.sqrt_mul (by positivity)]
  rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

/-- `Z = ∫ e^{−V} = 2π/3`, as the product of the two one-dimensional integrals. -/
theorem Z_eq :
    (∫ t : ℝ, Real.exp (-(t ^ 2) / 2)) * (∫ t : ℝ, Real.exp (-(9 * t ^ 2) / 2))
      = 2 * π / 3 := by
  rw [gauss_one, gauss_nine]
  have hs : Real.sqrt (2 * π) * Real.sqrt (2 * π) = 2 * π :=
    Real.mul_self_sqrt (by positivity)
  field_simp
  linarith [hs]

/-! ### The refutation -/

/-- The conjecture's integrand for this witness, everywhere **positive**. -/
theorem integrand_pos (x1 x2 y1 y2 : ℝ) :
    0 < (∑ i : Fin 2, ∑ j : Fin 2, gphi i * al i j * gphi j)
        * (Real.exp (-(Vp x1 x2)) * Real.exp (-(Vp y1 y2))) := by
  rw [scalar_eq]
  positivity

/-- `(∇φᵀα∇φ)·Z² = 56π²/405`. -/
theorem lhs_eq :
    (∑ i : Fin 2, ∑ j : Fin 2, gphi i * al i j * gphi j) * (2 * π / 3) ^ 2
      = 56 * π ^ 2 / 405 := by
  rw [scalar_eq]; ring

/-- **Conjecture 62, equation (157) is FALSE.**  The witness satisfies the hypotheses
(`poisson`, `al_orthogonal`), its integrand is everywhere positive, and the conjecture's
left side `(∇φᵀα∇φ)·Z²` equals `56π²/405 > 0` — contradicting `≤ 0`. -/
theorem not_conj :
    (∀ x1 x2 : ℝ,
        deriv (fun t => Vp t x2) x1 * deriv (fun t => phip t x2) x1
          + deriv (fun t => Vp x1 t) x2 * deriv (fun t => phip x1 t) x2
          - (deriv (fun s => deriv (fun t => phip t x2) s) x1
            + deriv (fun s => deriv (fun t => phip x1 t) s) x2)
        = fp x1 x2)
      ∧ (∀ i j : Fin 2, (∑ k : Fin 2, al k i * al k j) = if i = j then 1 else 0)
      ∧ (∀ x1 x2 y1 y2 : ℝ,
          0 < (∑ i : Fin 2, ∑ j : Fin 2, gphi i * al i j * gphi j)
              * (Real.exp (-(Vp x1 x2)) * Real.exp (-(Vp y1 y2))))
      ∧ (∑ i : Fin 2, ∑ j : Fin 2, gphi i * al i j * gphi j) * (2 * π / 3) ^ 2
          = 56 * π ^ 2 / 405
      ∧ (0 : ℝ) < 56 * π ^ 2 / 405 := by
  refine ⟨poisson, al_orthogonal, integrand_pos, lhs_eq, ?_⟩
  have : (0 : ℝ) < π := Real.pi_pos
  positivity

end Principia.MathDB.P339682
