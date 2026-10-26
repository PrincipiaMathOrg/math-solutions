import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# MathDB #325835 -- the tensor tubal norm is not a norm

Write-up `mathdb-open-problems/problems/325835/solution.tex`,
*A counterexample to the tensor-tubal-norm conjecture*, 22 September 2026.
Source: Z. Zhang, G. Ely, S. Aeron, N. Hao and M. Kilmer, **Conjecture 2.4.1**, p. 4:
`TTN(X) = sum_i ||S(i,i,:)||_2` (from the t-SVD of their Algorithm 1) is a norm, and the
tightest convex relaxation of tensor-tubal-rank.

**The witness** is two real `2x2x2` tensors with diagonal frontal slices,
`A = (diag(3/2,0), diag(1/2,0))` and `B = (diag(1/2,1), diag(-1/2,1))`.  Their length-2 DFT
slices are `diag(2,0), diag(1,0)` and `diag(0,2), diag(1,0)`, so both have
`TTN = sqrt(10)/2 = sqrt(5/2)`; their sum has slices `diag(2,2), diag(2,0)` and
`TTN = 2 + sqrt(2)`.  Since `sqrt(10) < 2 + sqrt(2)`, the triangle inequality fails.

**`TTN` is computed here, not assumed.**  `TTN` is defined exactly as Algorithm 1 computes
it -- the `i`-th diagonal singular tube is the inverse length-2 DFT of `(s_{i1}, s_{i2})`,
and `TTN` sums the tubes' Euclidean norms -- and `F` composes that with the Fourier step and
the singular values.  `TTN_eq` records the write-up's simplification
`TTN = (1/sqrt 2) sum_i sqrt(s_{i1}^2 + s_{i2}^2)`, which the proofs do not need.

**`Subadditive` is the weakest reading the witness kills.**  Being a norm implies the
triangle inequality, so refuting subadditivity refutes the conjecture a fortiori; and the
statement is further restricted to tensors with DIAGONAL frontal slices, which weakens it
again.  It is quantified over a tensor and a second tensor with the SUM taken tensorwise --
not over unrelated singular-value data, which would be a statement nobody made.

**The one classical identification, stated rather than hidden.**  `svDiag u v` is the sorted
pair `(max |u| |v|, min |u| |v|)`, the singular values of `diag(u,v)`: this is immediate
from `diag(u,v)^T diag(u,v) = diag(u^2, v^2)` and is taken as given rather than derived from
an SVD-uniqueness theorem.  The write-up exhibits the corresponding real t-SVDs explicitly
(identity factors for `A` and for the sum, the coordinate-swap permutation at the first
frequency of `B`) and notes that the repeated singular value of `2I` causes no ambiguity.

**Upstream status.**  The collaborator's own state for this problem is
`full-proof-eligibility-pending`.  Nothing certified here depends on that audit.

Values checked first in `Campaigns/MathDB-Formalization/verify_325835.py`, which recomputes
`TTN` from Algorithm 1 with a genuine numerical SVD -- so the closed form is checked against
the definition rather than against itself.
-/

namespace Principia.MathDB.P325835

/-- The length-2 DFT along the third coordinate, on DIAGONAL frontal slices: the source's
convention sends `(X₁, X₂)` to `(X₁ + X₂, X₁ - X₂)`. -/
def fourier (x1 y1 x2 y2 : ℝ) : ℝ × ℝ × ℝ × ℝ := (x1 + x2, y1 + y2, x1 - x2, y1 - y2)

/-- The sorted singular values of `diag(u, v)`: since `diag(u,v)ᵀ diag(u,v) = diag(u², v²)`,
they are `|u|` and `|v|` in nonincreasing order. -/
noncomputable def svDiag (u v : ℝ) : ℝ × ℝ := (max |u| |v|, min |u| |v|)

/-- `TTN` exactly as the source's Algorithm 1 computes it: the `i`-th diagonal singular
tube is the inverse length-2 DFT of `(s_{i1}, s_{i2})`, namely
`((s_{i1}+s_{i2})/2, (s_{i1}-s_{i2})/2)`, and `TTN` is the sum of the tubes' Euclidean
norms. -/
noncomputable def TTN (s11 s21 s12 s22 : ℝ) : ℝ :=
  Real.sqrt (((s11 + s12) / 2) ^ 2 + ((s11 - s12) / 2) ^ 2)
    + Real.sqrt (((s21 + s22) / 2) ^ 2 + ((s21 - s22) / 2) ^ 2)

/-- The write-up's simplification (1): `TTN = (1/√2) Σ_i √(s_{i1}² + s_{i2}²)`. -/
theorem TTN_eq (s11 s21 s12 s22 : ℝ) :
    TTN s11 s21 s12 s22
      = Real.sqrt ((s11 ^ 2 + s12 ^ 2) / 2) + Real.sqrt ((s21 ^ 2 + s22 ^ 2) / 2) := by
  rw [TTN]
  congr 1 <;> · congr 1; ring

/-! ### The Fourier slices of the three tensors -/

theorem fourier_A : fourier (3 / 2) 0 (1 / 2) 0 = (2, 0, 1, 0) := by
  rw [fourier]; norm_num

theorem fourier_B : fourier (1 / 2) 1 (-(1 / 2)) 1 = (0, 2, 1, 0) := by
  rw [fourier]; norm_num

/-- `A + B` has frontal slices `diag(2, 1)` and `diag(0, 1)`. -/
theorem fourier_C : fourier 2 1 0 1 = (2, 2, 2, 0) := by
  rw [fourier]; norm_num

/-! ### Their singular-value lists -/

theorem sv_20 : svDiag 2 0 = (2, 0) := by
  rw [svDiag]; norm_num

theorem sv_02 : svDiag 0 2 = (2, 0) := by
  rw [svDiag]; norm_num

theorem sv_10 : svDiag 1 0 = (1, 0) := by
  rw [svDiag]; norm_num

theorem sv_22 : svDiag 2 2 = (2, 2) := by
  rw [svDiag]; norm_num

/-! ### The three values -/

theorem TTN_A : TTN 2 0 1 0 = Real.sqrt 10 / 2 := by
  rw [TTN]
  have hs : (Real.sqrt 10 / 2) ^ 2 = 10 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have e : (((2 : ℝ) + 1) / 2) ^ 2 + (((2 : ℝ) - 1) / 2) ^ 2 = (Real.sqrt 10 / 2) ^ 2 := by
    rw [hs]; norm_num
  rw [e, Real.sqrt_sq (by positivity)]
  norm_num

theorem TTN_B : TTN 2 0 1 0 = Real.sqrt 10 / 2 := TTN_A

theorem TTN_C : TTN 2 2 2 0 = 2 + Real.sqrt 2 := by
  rw [TTN]
  have e1 : (((2 : ℝ) + 2) / 2) ^ 2 + (((2 : ℝ) - 2) / 2) ^ 2 = 2 ^ 2 := by norm_num
  have e2 : (((2 : ℝ) + 0) / 2) ^ 2 + (((2 : ℝ) - 0) / 2) ^ 2 = 2 := by norm_num
  rw [e1, e2, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-! ### The triangle inequality fails -/

theorem sqrt_ten_lt : Real.sqrt 10 < 2 + Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hn2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hn10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    rwa [Real.sqrt_one] at this
  nlinarith [h2, h10, hn2, hn10, h1]

/-- **The triangle inequality fails**: `TTN(A+B) > TTN(A) + TTN(B)`. -/
theorem triangle_fails :
    TTN 2 0 1 0 + TTN 2 0 1 0 < TTN 2 2 2 0 := by
  rw [TTN_A, TTN_C]
  have h10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have := sqrt_ten_lt
  linarith

/-- `TTN` as a functional ON THE TENSOR: Fourier slices, then their sorted singular
values, then the tube norms.  The four arguments are the diagonal entries of the two
frontal slices. -/
noncomputable def F (x1 y1 x2 y2 : ℝ) : ℝ :=
  TTN (svDiag (x1 + x2) (y1 + y2)).1 (svDiag (x1 + x2) (y1 + y2)).2
    (svDiag (x1 - x2) (y1 - y2)).1 (svDiag (x1 - x2) (y1 - y2)).2

theorem F_A : F (3 / 2) 0 (1 / 2) 0 = Real.sqrt 10 / 2 := by
  rw [F, show (3 : ℝ) / 2 + 1 / 2 = 2 from by norm_num,
    show (0 : ℝ) + 0 = 0 from by norm_num,
    show (3 : ℝ) / 2 - 1 / 2 = 1 from by norm_num,
    show (0 : ℝ) - 0 = 0 from by norm_num, sv_20, sv_10, TTN_A]

theorem F_B : F (1 / 2) 1 (-(1 / 2)) 1 = Real.sqrt 10 / 2 := by
  rw [F, show (1 : ℝ) / 2 + -(1 / 2) = 0 from by norm_num,
    show (1 : ℝ) + 1 = 2 from by norm_num,
    show (1 : ℝ) / 2 - -(1 / 2) = 1 from by norm_num,
    show (1 : ℝ) - 1 = 0 from by norm_num, sv_02, sv_10, TTN_A]

theorem F_C : F 2 1 0 1 = 2 + Real.sqrt 2 := by
  rw [F, show (2 : ℝ) + 0 = 2 from by norm_num,
    show (1 : ℝ) + 1 = 2 from by norm_num,
    show (2 : ℝ) - 0 = 2 from by norm_num,
    show (1 : ℝ) - 1 = 0 from by norm_num, sv_22, sv_20, TTN_C]

/-- Conjecture 2.4.1 of Zhang--Ely--Aeron--Hao--Kilmer asserts that `TTN` is a norm (and
the tightest convex relaxation of tensor-tubal-rank).  `Subadditive` is the WEAKEST reading
the witness kills: `TTN` satisfies the triangle inequality, and only on tensors with
DIAGONAL frontal slices.  A norm is subadditive, so refuting this refutes the conjecture a
fortiori. -/
def Subadditive : Prop :=
  ∀ x1 y1 x2 y2 u1 v1 u2 v2 : ℝ,
    F (x1 + u1) (y1 + v1) (x2 + u2) (y2 + v2) ≤ F x1 y1 x2 y2 + F u1 v1 u2 v2

/-- **`TTN` is not a norm**: the two tensors with frontal slices `diag(3/2,0), diag(1/2,0)`
and `diag(1/2,1), diag(-1/2,1)` have `TTN = √10/2` each, while their sum has `2 + √2`, and
`√10 < 2 + √2`. -/
theorem not_subadditive : ¬ Subadditive := by
  intro h
  have hsum := h (3 / 2) 0 (1 / 2) 0 (1 / 2) 1 (-(1 / 2)) 1
  rw [show (3 : ℝ) / 2 + 1 / 2 = 2 from by norm_num,
    show (0 : ℝ) + 1 = 1 from by norm_num,
    show (1 : ℝ) / 2 + -(1 / 2) = 0 from by norm_num, F_C, F_A, F_B] at hsum
  have h10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have := sqrt_ten_lt
  linarith

end Principia.MathDB.P325835
