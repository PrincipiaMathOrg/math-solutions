import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# MathDB #360860 — pentagon barycenter coincidence without equal cross-ratios

Write-up: `mathdb-open-problems/problems/360860/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Arnold–Arreche, Conjecture 7.8 of the preprint, retained as **Conjecture 36** of the
journal final: for a pentagon the hyperbolic barycenter `S` equals the Euclidean
least-squares point `L` **iff** the five consecutive cross-ratios are equal, or `S = (0,0)`.

The write-up refutes the "only if" half with a pentagon inscribed in the unit circle at the
stereographic parameters `p = (0, 3/4, 3, −3, −3/4)`, i.e. the rational vertices
`(1,0), (7/25,24/25), (−4/5,3/5), (−4/5,−3/5), (7/25,−24/25)`.

## What is proved here

* `barycenter_eq` — from the source's own `I`, `J`, `K` and its equation (3.3)
  `S = ((I−K)/(I+K), 2J/(I+K))`: `I = −61/18`, `J = 0`, `K = −7/2`, so `S = (−1/62, 0)`.
* `lsq_min` — the squared-distance sum to the five side lines is
  `F(x,y) = 62/25·x² + 63/25·y² + 2/25·x + 409/125`, and
  `F(x,y) − F(−1/62,0) = 62/25·(x+1/62)² + 63/25·y²`.  That single identity gives both the
  minimum and its **uniqueness**, with no Hessian and no numerical optimiser.
* `cross_ratios_ne` — `R₁ = 5/3` while `R₂ = 25/16`, so the five are not all equal.
* `not_conj` — the conjecture's necessary direction fails: `S = L`, `S ≠ (0,0)`, and the
  cross-ratios differ.  Refuting "only if" refutes the stated equivalence.

**Why the cross-ratio convention does not matter.**  The source fixes
`R(a,b,c,d) = (a−c)(b−d)/((a−d)(b−c))`.  A different ordered convention applies one
injective fractional-linear map to all five values at once, so whether they are *equal* is
convention-independent — which is why two unequal values settle it.

**Not Lean-checked:** that the source's `S` formula is the hyperbolic barycenter, and that
`Fsq` is the squared-distance sum for these side lines, are read off the write-up's equation
(3.3) and its printed line list.  `Campaigns/MathDB-Formalization/verify_360860.py` checks
the surroundings exactly: the vertices lie on the unit circle, the polygon is strictly
convex in cyclic order, each printed side line passes through its two vertices, the closed
form for `F` equals the sum over the five lines, and the write-up's independent hyperbolic
certificate `(62+x)² − 3843(1−x²−y²) = (62x+1)² + 3843y²` holds.

Values are written as explicit expressions rather than `∑ i : Fin 5`, because `decide` does
not reduce `Rat` equality in the kernel; every claim is closed by `norm_num`.
-/

namespace Principia.MathDB.P360860

/-! ### The five stereographic parameters -/

def p1 : ℚ := 0
def p2 : ℚ := 3/4
def p3 : ℚ := 3
def p4 : ℚ := -3
def p5 : ℚ := -3/4

/-- `I = ∑ 1/(pᵢ − pᵢ₊₁)`, cyclically. -/
def Ival : ℚ :=
  1/(p1 - p2) + 1/(p2 - p3) + 1/(p3 - p4) + 1/(p4 - p5) + 1/(p5 - p1)

/-- `J = ½ ∑ (pᵢ + pᵢ₊₁)/(pᵢ − pᵢ₊₁)`. -/
def Jval : ℚ :=
  (1/2) * ((p1 + p2)/(p1 - p2) + (p2 + p3)/(p2 - p3) + (p3 + p4)/(p3 - p4)
    + (p4 + p5)/(p4 - p5) + (p5 + p1)/(p5 - p1))

/-- `K = ∑ pᵢpᵢ₊₁/(pᵢ − pᵢ₊₁)`. -/
def Kval : ℚ :=
  p1*p2/(p1 - p2) + p2*p3/(p2 - p3) + p3*p4/(p3 - p4) + p4*p5/(p4 - p5) + p5*p1/(p5 - p1)

theorem I_eq : Ival = -61/18 := by
  unfold Ival p1 p2 p3 p4 p5; norm_num

theorem J_eq : Jval = 0 := by
  unfold Jval p1 p2 p3 p4 p5; norm_num

theorem K_eq : Kval = -7/2 := by
  unfold Kval p1 p2 p3 p4 p5; norm_num

/-- The hyperbolic barycenter, from the source's equation (3.3). -/
def barycenter : ℚ × ℚ := ((Ival - Kval) / (Ival + Kval), 2 * Jval / (Ival + Kval))

theorem barycenter_eq : barycenter = (-1/62, 0) := by
  rw [barycenter, I_eq, J_eq, K_eq]
  norm_num

theorem barycenter_ne_zero : barycenter ≠ (0, 0) := by
  rw [barycenter_eq]
  intro h
  have h1 : (-1/62 : ℚ) = 0 := congrArg Prod.fst h
  norm_num at h1

/-! ### The Euclidean least-squares point -/

/-- The sum of squared Euclidean distances to the five side lines. -/
noncomputable def Fsq (x y : ℝ) : ℝ := 62/25 * x^2 + 63/25 * y^2 + 2/25 * x + 409/125

/-- **`(−1/62, 0)` minimises `Fsq`, and uniquely.**  One exact completion of the square
delivers both halves. -/
theorem lsq_min (x y : ℝ) :
    Fsq (-1/62) 0 ≤ Fsq x y ∧ (Fsq x y = Fsq (-1/62) 0 → x = -1/62 ∧ y = 0) := by
  have key : Fsq x y - Fsq (-1/62) 0 = 62/25 * (x + 1/62)^2 + 63/25 * y^2 := by
    unfold Fsq; ring
  refine ⟨by nlinarith [sq_nonneg (x + 1/62), sq_nonneg y], fun h => ?_⟩
  have h0 : 62/25 * (x + 1/62)^2 + 63/25 * y^2 = 0 := by rw [← key, h]; ring
  constructor
  · nlinarith [sq_nonneg (x + 1/62), sq_nonneg y]
  · nlinarith [sq_nonneg (x + 1/62), sq_nonneg y]

/-! ### The cross-ratios -/

/-- The source's ordered cross-ratio `R(a,b,c,d) = (a−c)(b−d)/((a−d)(b−c))`. -/
def R (a b c d : ℚ) : ℚ := (a - c) * (b - d) / ((a - d) * (b - c))

def R1 : ℚ := R p1 p2 p3 p4
def R2 : ℚ := R p2 p3 p4 p5

theorem R1_eq : R1 = 5/3 := by
  unfold R1 R p1 p2 p3 p4; norm_num

theorem R2_eq : R2 = 25/16 := by
  unfold R2 R p2 p3 p4 p5; norm_num

/-- The five consecutive cross-ratios are **not** all equal. -/
theorem cross_ratios_ne : R1 ≠ R2 := by
  rw [R1_eq, R2_eq]; norm_num

/-- **Conjecture 36's necessary direction is FALSE.**  This pentagon has `S = L`, with
`S ≠ (0,0)`, yet its five consecutive cross-ratios are not all equal. -/
theorem not_conj :
    barycenter = (-1/62, 0) ∧
    (∀ x y : ℝ, Fsq (-1/62) 0 ≤ Fsq x y) ∧
    barycenter ≠ (0, 0) ∧ R1 ≠ R2 :=
  ⟨barycenter_eq, fun x y => (lsq_min x y).1, barycenter_ne_zero, cross_ratios_ne⟩

end Principia.MathDB.P360860
