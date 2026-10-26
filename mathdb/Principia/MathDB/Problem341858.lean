import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# MathDB 341858 — the two-variable Bernoulli determinant, as printed, is false

Write-up: `mathdb-open-problems/problems/341858/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "The two-variable Bernoulli
determinant: a corrected evaluation".  MathDB 341858 repeats **Conjecture 4.4** of
Chapoton's preprint (numbered 4.1 in the published article).

## The matrix

With the normalisation `B₁(X) = X - 1/2` (which is Mathlib's `Polynomial.bernoulli 1`,
`= X - C 2⁻¹`), the `2r × 2r` matrix `A r x y` has its columns indexed in the order
`(m,v) = (0,1),(0,2),(1,1),(1,2),…`, so column `c` carries `m = c / 2` and `v = c % 2`
with `x₁ = x`, `x₂ = y`, and

  `(A r)_{a,(m,v)} = [a = m]` for `a < r`,  `(A r)_{r+i,(m,v)} = B_{i+m+1}(x_v)/(i+m+1)`.

`F r x y = det (A r x y)` is the polynomial `F̄_{r,2}` of the source's (4.7).

## What is refuted

The conjecture's product is **printed starting at `j = 0`**:

  `(-1)^C(r,2) · C_r · tʳ · ∏_{j=0}^{r-1} (t² - j²)^{r-j}`,  `t = y - x`.

The `j = 0` factor is `(t²)^r = t^{2r}`, so the printed expression carries `t^{3r}` where
the determinant carries only `tʳ`.  At `r = 1` the determinant is `y - x` while the
printed expression is `(y-x)³`; at `(x,y) = (0,2)` that is **`2` against `8`**.
`not_conj_as_printed` is exactly that.  The corrected identity starts the product at
`j = 1`, and `corrected_fixes_it` checks that the corrected form does give `2` here.

## Scope (the 215 check)

* This refutes the conjecture **as printed**.  The write-up's positive result — the
  corrected identity for **every** `r` — is *not* formalised here: its proof reduces the
  determinant by column operations to a Hankel determinant of power-sum moments and then
  invokes Dominici's published Hahn-determinant theorem, neither of which is in Mathlib.
  `Campaigns/MathDB-Formalization/verify_341858.py` checks the corrected identity
  numerically at `r = 1, 2, 3` over several rational points, and confirms the printed form
  fails at every **non-degenerate** point (at a degenerate one, where some `t² - j²`
  vanishes, both sides are `0` and agree — which is why a witness must be chosen away from
  `t = ±1, ±2, …`; `t = 2` at `r = 1` has an empty corrected product and is safe).
* `ConjAsPrinted` quantifies over every `r ≥ 1` and every `x, y`, which is the conjecture's
  own strength; refuting it needs the single instance supplied.
-/

namespace Principia.MathDB.P341858

open Finset

/-- The source's `2r × 2r` matrix; column `c` carries `m = c / 2` and `v = c % 2`. -/
noncomputable def A (r : ℕ) (x y : ℚ) : Matrix (Fin (2 * r)) (Fin (2 * r)) ℚ :=
  Matrix.of fun a c =>
    if (a : ℕ) < r then (if (a : ℕ) = (c : ℕ) / 2 then 1 else 0)
    else (Polynomial.bernoulli ((a : ℕ) - r + (c : ℕ) / 2 + 1)).eval
        (if (c : ℕ) % 2 = 0 then x else y)
      / ((((a : ℕ) - r + (c : ℕ) / 2 + 1 : ℕ) : ℚ))

/-- `F̄_{r,2}(x,y)` of the source's (4.7). -/
noncomputable def F (r : ℕ) (x y : ℚ) : ℚ := (A r x y).det

/-- `C_r = (∏_{j=1}^{r-1} j!)³ / ∏_{j=r}^{2r-1} j!`. -/
noncomputable def cCoef (r : ℕ) : ℚ :=
  (∏ j ∈ Ico 1 r, ((Nat.factorial j : ℚ))) ^ 3 / ∏ j ∈ Ico r (2 * r), ((Nat.factorial j : ℚ))

/-- The conjecture's expression **as printed**: the product starts at `j = 0`. -/
noncomputable def printedExpr (r : ℕ) (x y : ℚ) : ℚ :=
  (-1) ^ (r.choose 2) * cCoef r * (y - x) ^ r *
    ∏ j ∈ range r, ((y - x) ^ 2 - (j : ℚ) ^ 2) ^ (r - j)

/-- The write-up's corrected expression: the product starts at `j = 1`. -/
noncomputable def correctedExpr (r : ℕ) (x y : ℚ) : ℚ :=
  (-1) ^ (r.choose 2) * cCoef r * (y - x) ^ r *
    ∏ j ∈ Ico 1 r, ((y - x) ^ 2 - (j : ℚ) ^ 2) ^ (r - j)

/-! ## The `r = 1` computation -/

theorem F_one (x y : ℚ) : F 1 x y = y - x := by
  rw [F, Matrix.det_fin_two]
  simp [A, Polynomial.bernoulli_one]

theorem F_one_zero_two : F 1 0 2 = 2 := by
  rw [F_one]; norm_num

theorem cCoef_one : cCoef 1 = 1 := by
  simp [cCoef]

theorem printed_one_zero_two : printedExpr 1 0 2 = 8 := by
  rw [printedExpr, cCoef_one]
  norm_num

theorem corrected_one_zero_two : correctedExpr 1 0 2 = 2 := by
  rw [correctedExpr, cCoef_one]
  norm_num

/-! ## The refutation -/

/-- Conjecture 4.4 exactly as printed: the product runs from `j = 0`. -/
def ConjAsPrinted : Prop := ∀ r : ℕ, 1 ≤ r → ∀ x y : ℚ, F r x y = printedExpr r x y

/-- **The conjecture as printed is false**, at `r = 1`, `(x,y) = (0,2)`: `2 ≠ 8`. -/
theorem not_conj_as_printed : ¬ ConjAsPrinted := by
  intro h
  have := h 1 le_rfl 0 2
  rw [F_one_zero_two, printed_one_zero_two] at this
  norm_num at this

/-- Moving the product's lower index from `0` to `1` repairs it at the witness: the
corrected expression gives the determinant's value, the printed one does not. -/
theorem corrected_fixes_it :
    F 1 0 2 = correctedExpr 1 0 2 ∧ F 1 0 2 ≠ printedExpr 1 0 2 := by
  refine ⟨?_, ?_⟩
  · rw [F_one_zero_two, corrected_one_zero_two]
  · rw [F_one_zero_two, printed_one_zero_two]; norm_num

end Principia.MathDB.P341858
