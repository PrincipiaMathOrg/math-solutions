import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# MathDB #371784 — a strictly positive biquadratic M-tensor that is not a sum of squares

Write-up: `mathdb-open-problems/problems/371784/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Xu, Cui and Qi, **Question 1** (Conjecture 3.1 of their preprint): is every
symmetric biquadratic M-tensor a sum of squares of bilinear forms?  The answer is no.

The witness is `P = 8C + J`, where `C` is the Choi form (cyclically oriented) and
`J(x,y) = ‖x‖²‖y‖²`.

## Why a non-SOS claim is provable at all

"Not a sum of squares" quantifies over every decomposition.  What makes it finite is a
**dual certificate**: a linear functional `ℓ` with `ℓ(g²) ≥ 0` for every bilinear `g`, yet
`ℓ(P) < 0`.  One functional rules out all representations at once.

`ℓ` is defined on monomials in the source, which would drag in `MvPolynomial` and
coefficient extraction — and stating SOS at the level of coefficient ARRAYS would refute
fewer representations than the real question does.  Instead `ℓ` is realised here as a
combination of **24 point evaluations** with 0/1 coordinates and integer weights
(`{6, 3, −2, 2}`), found by exact linear solve and checked in
`Campaigns/MathDB-Formalization/verify_371784.py`.  That lets `not_sos` be stated at FORM
level — `∀ x y, P x y = ∑ₜ gₜ(x,y)²` — and proved by evaluating that hypothesis at the 24
points.  No polynomial machinery is used anywhere in this file.

The weights necessarily have mixed signs: a nonnegative combination of evaluations is
nonnegative on every PSD form, and `C` is PSD.

## The witness satisfies the conjecture's hypotheses

Refuting SOS alone would only re-derive Choi's classical result.  What is new is that a
STRICTLY POSITIVE M-tensor fails SOS, so the hypotheses are checked too:

* `choi_nonneg` : `C ≥ 0` — Choi's form is PSD but famously **not** SOS, so no `positivity`
  or SOS tactic can prove it; `nlinarith` finds a degree-8 certificate from products of the
  supplied squares.
* `P_ge_J` : `P(x,y) ≥ ‖x‖²‖y‖²`, so `P` is strictly positive off the zero vectors.
* `Bform_le_eight` : on unit vectors the form of `B = 8(I − T)` is at most `8`.  Every
  M-eigenvalue of `B` is such a value (contract its two defining equations with `x` and
  `y`), so `λ_max(B) ≤ 8 < 9` and `𝒜 = 9I − B` is a STRONG M-tensor.  **The contraction
  step itself is not formalised here** — that is the one piece taken from the write-up.

## Values

`ℓ(C) = −3`, `ℓ(J) = 21`, `ℓ(P) = 8(−3) + 21 = −3 < 0`.
-/

namespace Principia.MathDB.P371784

/-- The Choi form, cyclically oriented, grouped as `xᵀM(y)x`. -/
def Cf (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  x1^2*(y1^2+y2^2) + x2^2*(y2^2+y3^2) + x3^2*(y3^2+y1^2)
    - 2*(x1*x2*y1*y2 + x1*x3*y1*y3 + x2*x3*y2*y3)

/-- `J(x,y) = ‖x‖²‖y‖²`, the form of the M-identity tensor. -/
def Jf (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ := (x1^2+x2^2+x3^2)*(y1^2+y2^2+y3^2)

/-- The witness `P = 8C + J`. -/
def Pf (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  8 * Cf x1 x2 x3 y1 y2 y3 + Jf x1 x2 x3 y1 y2 y3

/-- A bilinear form with coefficient matrix `u`. -/
def bil (u : Fin 3 → Fin 3 → ℝ) (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  u 0 0 * (x1*y1) + u 0 1 * (x1*y2) + u 0 2 * (x1*y3)
    + u 1 0 * (x2*y1) + u 1 1 * (x2*y2) + u 1 2 * (x2*y3)
    + u 2 0 * (x3*y1) + u 2 1 * (x3*y2) + u 2 2 * (x3*y3)

set_option maxHeartbeats 1000000 in
/-- **The Choi form is nonnegative.**  It is PSD but not a sum of squares, so no SOS tactic
can do this; `nlinarith` builds a higher-degree certificate from the supplied squares. -/
theorem choi_nonneg (x1 x2 x3 y1 y2 y3 : ℝ) : 0 ≤ Cf x1 x2 x3 y1 y2 y3 := by
  unfold Cf
  nlinarith [sq_nonneg (x1*y1 - x2*y2), sq_nonneg (x2*y2 - x3*y3), sq_nonneg (x3*y3 - x1*y1),
    sq_nonneg (x1*y2 - x2*y3), sq_nonneg (x2*y3 - x3*y1), sq_nonneg (x3*y1 - x1*y2),
    sq_nonneg (x1*y2 - x2*y1), sq_nonneg (x2*y3 - x3*y2), sq_nonneg (x3*y1 - x1*y3),
    sq_nonneg (x1*y1 - x2*y2 + x3*y3), sq_nonneg (x1*y2 + x2*y3 + x3*y1),
    sq_nonneg (x1*y1 + x2*y2 + x3*y3), sq_nonneg (x1*y2 - x2*y3),
    sq_nonneg (x1*y3 - x3*y1), sq_nonneg (x2*y1 - x1*y2)]

/-- `P` dominates `‖x‖²‖y‖²`, so it is strictly positive off the zero vectors. -/
theorem P_ge_J (x1 x2 x3 y1 y2 y3 : ℝ) :
    Jf x1 x2 x3 y1 y2 y3 ≤ Pf x1 x2 x3 y1 y2 y3 := by
  have h := choi_nonneg x1 x2 x3 y1 y2 y3
  unfold Pf
  linarith

/-- The form of `B = 8(I − T)`, whose tensor is entrywise nonnegative. -/
def Bform (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  8 * (Jf x1 x2 x3 y1 y2 y3 - Cf x1 x2 x3 y1 y2 y3)

/-- On unit vectors `B`'s form is at most `8`.  Every M-eigenvalue of `B` is such a value,
so `λ_max(B) ≤ 8 < 9` and `𝒜 = 9I − B` is a strong M-tensor. -/
theorem Bform_le_eight (x1 x2 x3 y1 y2 y3 : ℝ)
    (hx : x1^2+x2^2+x3^2 = 1) (hy : y1^2+y2^2+y3^2 = 1) :
    Bform x1 x2 x3 y1 y2 y3 ≤ 8 := by
  have h := choi_nonneg x1 x2 x3 y1 y2 y3
  unfold Bform Jf
  rw [hx, hy]
  linarith

/-- The separating functional, realised as 24 point evaluations. -/
def Lc (F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (6) * F 0 0 1 0 0 1 + (6) * F 0 0 1 0 1 0
  + (-2) * F 0 0 1 0 1 1 + (3) * F 0 0 1 1 0 0
  + (-2) * F 0 0 1 1 0 1 + (3) * F 0 1 0 0 0 1
  + (6) * F 0 1 0 0 1 0 + (-2) * F 0 1 0 0 1 1
  + (6) * F 0 1 0 1 0 0 + (-2) * F 0 1 0 1 1 0
  + (-2) * F 0 1 1 0 0 1 + (-2) * F 0 1 1 0 1 0
  + (2) * F 0 1 1 0 1 1 + (6) * F 1 0 0 0 0 1
  + (3) * F 1 0 0 0 1 0 + (6) * F 1 0 0 1 0 0
  + (-2) * F 1 0 0 1 0 1 + (-2) * F 1 0 0 1 1 0
  + (-2) * F 1 0 1 0 0 1 + (-2) * F 1 0 1 1 0 0
  + (2) * F 1 0 1 1 0 1 + (-2) * F 1 1 0 0 1 0
  + (-2) * F 1 1 0 1 0 0 + (2) * F 1 1 0 1 1 0

/-- `ℓ` is nonnegative on the square of every bilinear form: the separator identity. -/
theorem Lc_sq_nonneg (u : Fin 3 → Fin 3 → ℝ) :
    0 ≤ Lc (fun a b c d e f => (bil u a b c d e f)^2) := by
  have h : Lc (fun a b c d e f => (bil u a b c d e f)^2)
      = 2*(u 0 0 + u 1 1 + u 2 2)^2 + (u 0 1 + 2*(u 1 0))^2
        + (u 1 2 + 2*(u 2 1))^2 + (u 2 0 + 2*(u 0 2))^2 := by
    simp only [Lc, bil]
    norm_num
    ring
  rw [h]
  have h1 := sq_nonneg (u 0 0 + u 1 1 + u 2 2)
  have h2 := sq_nonneg (u 0 1 + 2*(u 1 0))
  have h3 := sq_nonneg (u 1 2 + 2*(u 2 1))
  have h4 := sq_nonneg (u 2 0 + 2*(u 0 2))
  linarith

/-- `ℓ(P) = −3 < 0`. -/
theorem Lc_P : Lc Pf = -3 := by
  simp only [Lc, Pf, Cf, Jf]
  norm_num

/-- Pushing `ℓ` through a finite sum, since it is a linear combination of evaluations. -/
theorem Lc_sum {n : ℕ} (f : Fin n → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Lc (fun a b c d e g => ∑ t : Fin n, f t a b c d e g) = ∑ t : Fin n, Lc (f t) := by
  simp only [Lc, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- **Xu–Cui–Qi Question 1 is answered NO.**  `P` is a strictly positive symmetric
biquadratic M-tensor (`P_ge_J`, `Bform_le_eight`) that is not a sum of squares of bilinear
forms — no finite family of bilinear forms has squares summing to `P`. -/
theorem not_sos :
    ¬ ∃ (n : ℕ) (u : Fin n → Fin 3 → Fin 3 → ℝ),
        ∀ x1 x2 x3 y1 y2 y3 : ℝ,
          Pf x1 x2 x3 y1 y2 y3 = ∑ t : Fin n, (bil (u t) x1 x2 x3 y1 y2 y3)^2 := by
  rintro ⟨n, u, hP⟩
  have hfun : Pf = fun a b c d e g => ∑ t : Fin n, (bil (u t) a b c d e g)^2 := by
    funext a b c d e g
    exact hP a b c d e g
  have h1 : Lc Pf = ∑ t : Fin n, Lc (fun a b c d e g => (bil (u t) a b c d e g)^2) := by
    rw [hfun, Lc_sum]
  have h2 : (0:ℝ) ≤ ∑ t : Fin n, Lc (fun a b c d e g => (bil (u t) a b c d e g)^2) :=
    Finset.sum_nonneg fun t _ => Lc_sq_nonneg (u t)
  rw [← h1, Lc_P] at h2
  norm_num at h2

end Principia.MathDB.P371784
