import Mathlib

/-!
# MathDB #376316 — the product Hermitian Jacobi eigenfunction conjecture is FALSE

Write-up `mathdb-open-problems/problems/376316/solution.tex`,
*A quadratic counterexample to the product Hermitian Jacobi eigenfunction conjecture*,
17 September 2026.

Conjecture 3.12 asks whether every product polynomial of equation (21) is an eigenfunction of the
Hermitian Jacobi operator `𝒢` on the matrix simplex.  At `m = k = 2`, `κ = (r,s,s)`, the
prescribed product polynomial is a nonzero multiple of

`F = tr A + tr B − 1 − det A − M`,  `M = (tr A)(tr B) − tr (A B)`,

and the write-up's direct differentiation of Definition 3.5 gives the table

`𝒢 tr A = 2(r+1) − N tr A`,     `𝒢 tr B = 2(s+1) − N tr B`,
`𝒢 det A = r tr A − 2(N−1) det A`,  `𝒢 M = (s+1) tr A + (r+1) tr B − 2(N−1) M`,

with `N = r + 2s + 3`.  Since `𝒢` is linear and kills constants, those four lines force

`𝒢 F = −2(N−1) F + s L`,  `L = tr A + 2 tr B − 2`.                     (`residual`)

At the interior point `A = diag(1/3, 2/3)`, `B = (2/9) I` we get `F = 0` but `L = −1/9`, so
`𝒢 F = −s/9 ≠ 0`, while an eigenfunction would satisfy `𝒢 F = λ F = 0` there.

## Status: the table is now DERIVED, not assumed

This module was CONDITIONAL until 2026-09-22: the four differentiation identities entered as
hypotheses of `main`, so the result was only *"for any operator acting on these four invariants
as the source computes, `F` is not an eigenfunction"*.  That gap is now closed.

Definition 3.5's operator is, at `m = k = 2`, a second-order differential operator in the
**eight formal matrix entries**.  The write-up is explicit that the derivatives are taken in
those entries before any restriction, and that setting off-diagonal entries to zero first would
give the wrong operator -- so formal differentiation in eight independent variables is exactly
what is wanted, and that is `MvPolynomial.pderiv` over `Fin 8`.  No analysis is involved: the
whole table is a polynomial computation, carried out in `section Operator` below.

* `G` is equation (G) verbatim -- 72 terms, the three sums of Definition 3.5.
* `G_trA`, `G_trB`, `G_detA`, `G_M` are the four table lines, now **theorems**.
* `G_F` is the residual identity `G F = -2(N-1) F + s L`, also a theorem.
* `main_operator` concludes without hypotheses: `eval w F = 0` while
  `eval w (G F) = -s/9`, so `G F` is not `C lam * F` for any `lam`.

`main` and `residual` are kept: they are still true, and they record the implication that was
all this module claimed before.

The witness is genuinely interior: `A > 0`, `B > 0` and `I - A - B = diag(4/9, 1/9) > 0`, all
checked below; `w_A` and `w_B` identify the point of `R^8` with those matrices, so the
interiority proof applies to the point the polynomial statement uses.

Checked in SymPy before formalizing: the operator differentiated in all eight formal entries;
all four table lines; the two intermediate identities for `(tr A)(tr B)` and `tr(AB)`;
`G L = -N L`; the residual identity; and the witness values `F = 0`, `L = -1/9`, `G F = -s/9`.
-/

namespace Principia.MathDB.P376316

open Matrix

/-- The product polynomial, in terms of the four invariants. -/
noncomputable def Fv (tA tB dA M : ℝ) : ℝ := tA + tB - 1 - dA - M

/-- The residual direction `L`. -/
noncomputable def Lv (tA tB : ℝ) : ℝ := tA + 2 * tB - 2

/-- **The residual identity.**  Linearity of `𝒢` plus the source's four differentiation lines
force `𝒢 F = −2(N−1) F + s L`; the eigenfunction claim would need the `s L` term to vanish. -/
theorem residual (r s N tA tB dA M GtA GtB GdA GM : ℝ)
    (hN : N = r + 2 * s + 3)
    (h1 : GtA = 2 * (r + 1) - N * tA)
    (h2 : GtB = 2 * (s + 1) - N * tB)
    (h3 : GdA = r * tA - 2 * (N - 1) * dA)
    (h4 : GM = (s + 1) * tA + (r + 1) * tB - 2 * (N - 1) * M) :
    GtA + GtB - GdA - GM = -2 * (N - 1) * Fv tA tB dA M + s * Lv tA tB := by
  subst hN h1 h2 h3 h4
  unfold Fv Lv
  ring

/-- The witness `A = diag(1/3, 2/3)`. -/
noncomputable def Amat : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 3, 0; 0, 2 / 3]

/-- The witness `B = (2/9) I`. -/
noncomputable def Bmat : Matrix (Fin 2) (Fin 2) ℝ := !![2 / 9, 0; 0, 2 / 9]

theorem trA_val : Amat.trace = 1 := by simp [Amat, Matrix.trace_fin_two]; norm_num

theorem trB_val : Bmat.trace = 4 / 9 := by simp [Bmat, Matrix.trace_fin_two]; norm_num

theorem detA_val : Amat.det = 2 / 9 := by simp [Amat, Matrix.det_fin_two]; norm_num

theorem trAB_val : (Amat * Bmat).trace = 2 / 9 := by
  simp [Amat, Bmat, Matrix.trace_fin_two, Matrix.mul_fin_two]
  norm_num

/-- `M = (tr A)(tr B) − tr (A B) = 2/9` at the witness. -/
theorem M_val : Amat.trace * Bmat.trace - (Amat * Bmat).trace = 2 / 9 := by
  rw [trA_val, trB_val, trAB_val]
  norm_num

/-- The product polynomial VANISHES at the witness. -/
theorem F_zero : Fv 1 (4 / 9) (2 / 9) (2 / 9) = 0 := by norm_num [Fv]

/-- The residual direction does NOT vanish there. -/
theorem L_nonzero : Lv 1 (4 / 9) = -(1 / 9) := by norm_num [Lv]

/-- The witness is interior: `I − A − B = diag(4/9, 1/9)`, positive, as are `A` and `B`. -/
theorem interior : (1 : Matrix (Fin 2) (Fin 2) ℝ) - Amat - Bmat = !![4 / 9, 0; 0, 1 / 9] := by
  simp [Amat, Bmat, Matrix.one_fin_two]
  norm_num [← Matrix.etaExpand_eq]

/-- **MathDB #376316 — Conjecture 3.12 is FALSE.**  At the interior witness the product
polynomial vanishes while `𝒢 F = −s/9 ≠ 0`, so no `λ` can satisfy `𝒢 F = λ F`.

The four differentiation identities are hypotheses: this certifies that *any* operator acting on
the invariants as the source computes fails to have `F` as an eigenfunction. -/
theorem main (r s N GtA GtB GdA GM : ℝ) (hs : 0 < s)
    (hN : N = r + 2 * s + 3)
    (h1 : GtA = 2 * (r + 1) - N * 1)
    (h2 : GtB = 2 * (s + 1) - N * (4 / 9))
    (h3 : GdA = r * 1 - 2 * (N - 1) * (2 / 9))
    (h4 : GM = (s + 1) * 1 + (r + 1) * (4 / 9) - 2 * (N - 1) * (2 / 9)) :
    Fv 1 (4 / 9) (2 / 9) (2 / 9) = 0 ∧
      GtA + GtB - GdA - GM = -(s / 9) ∧
      ∀ lam : ℝ, GtA + GtB - GdA - GM ≠ lam * Fv 1 (4 / 9) (2 / 9) (2 / 9) := by
  have hres := residual r s N 1 (4 / 9) (2 / 9) (2 / 9) GtA GtB GdA GM hN h1 h2 h3 h4
  rw [F_zero, L_nonzero] at hres
  have hG : GtA + GtB - GdA - GM = -(s / 9) := by rw [hres]; ring
  refine ⟨F_zero, hG, fun lam => ?_⟩
  rw [hG, F_zero, mul_zero]
  intro hc
  have : s = 0 := by linarith [hc]
  exact absurd this (ne_of_gt hs)

/-! ## The operator itself, and the four identities as THEOREMS

Everything above takes the source's differentiation table on faith.  This section removes
that.  Definition 3.5's operator is, at `m = k = 2`, a second-order differential operator
in the **eight formal matrix entries** — the write-up is explicit that the derivatives are
taken in those entries before any restriction, and that setting off-diagonal entries to
zero first would give the wrong operator.  Formal differentiation in eight independent
variables is exactly `MvPolynomial.pderiv` over `Fin 8`, so no analysis is involved and
the table becomes a polynomial computation. -/

section Operator

open MvPolynomial

set_option maxHeartbeats 2000000

/-- The eight formal matrix entries: `v j a b` is entry `(a,b)` of `X_j`. -/
def v (j a b : Fin 2) : Fin 8 :=
  ⟨4 * (j : ℕ) + 2 * (a : ℕ) + (b : ℕ), by
    have := j.isLt; have := a.isLt; have := b.isLt; omega⟩

noncomputable abbrev Pol := MvPolynomial (Fin 8) ℝ

/-- Entry `(a,b)` of `X_j` as a formal variable. -/
noncomputable def E (j a b : Fin 2) : Pol := X (v j a b)

/-- Kronecker delta. -/
def dl (a b : Fin 2) : ℝ := if a = b then 1 else 0

/-- `κ₁ = r`, `κ₂ = s`. -/
def kap (r s : ℝ) (j : Fin 2) : ℝ := if j = 0 then r else s

/-- **Definition 3.5, specialised to `m = k = 2`** — equation (G) of the write-up. -/
noncomputable def G (r s N : ℝ) (f : Pol) : Pol :=
  (∑ j : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
      (C (dl a d) - E j a d) * E j c b * pderiv (v j a b) (pderiv (v j c d) f))
  - C (1 / 2) *
    (∑ j : Fin 2, ∑ l : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
      (if j = l then 0 else
        (E j a d * E l c b + E j c b * E l a d)
          * pderiv (v j a b) (pderiv (v l c d) f)))
  + (∑ j : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2,
      (C (kap r s j + 1) * C (dl a b) - C N * E j a b) * pderiv (v j a b) f)

noncomputable def trAp : Pol := E 0 0 0 + E 0 1 1

noncomputable def trBp : Pol := E 1 0 0 + E 1 1 1

noncomputable def detAp : Pol := E 0 0 0 * E 0 1 1 - E 0 0 1 * E 0 1 0

noncomputable def trABp : Pol := ∑ a : Fin 2, ∑ b : Fin 2, E 0 a b * E 1 b a

/-- `M = (tr A)(tr B) − tr(AB)`, as in equation (F). -/
noncomputable def Mp : Pol := trAp * trBp - trABp

/-- The product polynomial `F = tr A + tr B − 1 − det A − M`. -/
noncomputable def Fp : Pol := trAp + trBp - 1 - detAp - Mp

/-- The residual direction `L = tr A + 2 tr B − 2`. -/
noncomputable def Lp : Pol := trAp + 2 * trBp - 2

/-! The local simp set below unfolds the operator into its 72 explicit terms and
differentiates them. -/
attribute [local simp] G E v dl kap trAp trBp detAp trABp Mp Fp Lp

/-- `C` of a real numeral is the polynomial numeral; this is the one fact `ring`
cannot supply about the operator's `1/2`. -/
theorem Chalf : (C (1 / 2 : ℝ) : Pol) * 2 = 1 := by
  rw [mul_two, ← MvPolynomial.C_add]
  norm_num

theorem G_trA (r s N : ℝ) : G r s N trAp = C (2 * (r + 1)) - C N * trAp := by
  simp [Fin.sum_univ_two, pderiv_X, Pi.single_apply, map_add, map_mul, map_ofNat,
    MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  ring

theorem G_trB (r s N : ℝ) : G r s N trBp = C (2 * (s + 1)) - C N * trBp := by
  simp [Fin.sum_univ_two, pderiv_X, Pi.single_apply, map_add, map_mul, map_ofNat,
    MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  ring

theorem G_detA (r s N : ℝ) :
    G r s N detAp = C r * trAp - C (2 * (N - 1)) * detAp := by
  simp [Fin.sum_univ_two, pderiv_X, Pi.single_apply, map_add, map_mul, map_ofNat,
    MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  ring

theorem G_M (r s N : ℝ) :
    G r s N Mp = C (s + 1) * trAp + C (r + 1) * trBp - C (2 * (N - 1)) * Mp := by
  simp [Fin.sum_univ_two, pderiv_X, Pi.single_apply, map_add, map_mul, map_ofNat,
    MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  linear_combination (norm := ring_nf)
    (2 * X 0 * X 7 - 2 * X 1 * X 6 - 2 * X 2 * X 5 + 2 * X 3 * X 4) * Chalf

/-- **The residual identity, now a theorem about the operator itself.**  This is what the
`residual` lemma above had to assume. -/
theorem G_F (r s N : ℝ) (hN : N = r + 2 * s + 3) :
    G r s N Fp = C (-2 * (N - 1)) * Fp + C s * Lp := by
  subst hN
  simp [Fin.sum_univ_two, pderiv_X, Pi.single_apply, map_add, map_mul, map_ofNat,
    MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  linear_combination (norm := ring_nf)
    (-2 * X 0 * X 7 + 2 * X 1 * X 6 + 2 * X 2 * X 5 - 2 * X 3 * X 4) * Chalf

/-! ### The witness, and the conjecture refuted without hypotheses -/

/-- The witness `A = diag(1/3, 2/3)`, `B = (2/9) I` as a point of `ℝ⁸`. -/
noncomputable def w : Fin 8 → ℝ := ![1 / 3, 0, 0, 2 / 3, 2 / 9, 0, 0, 2 / 9]

/-- The `ℝ⁸` witness is the matrix witness whose interiority is proved above. -/
theorem w_A (a b : Fin 2) : w (v 0 a b) = Amat a b := by
  fin_cases a <;> fin_cases b <;> simp [w, v, Amat]

theorem w_B (a b : Fin 2) : w (v 1 a b) = Bmat a b := by
  fin_cases a <;> fin_cases b <;> simp [w, v, Bmat]

theorem Fp_at_w : eval w Fp = 0 := by
  simp [w, Fin.sum_univ_two]
  norm_num

theorem Lp_at_w : eval w Lp = -(1 / 9) := by
  simp [w, Fin.sum_univ_two]
  norm_num

theorem GF_at_w (r s N : ℝ) (hN : N = r + 2 * s + 3) :
    eval w (G r s N Fp) = -(s / 9) := by
  rw [G_F r s N hN, eval_add, eval_mul, eval_mul, eval_C, eval_C, Fp_at_w, Lp_at_w]
  ring

/-- **MathDB #376316 — Conjecture 3.12 is FALSE, with no carried hypotheses.**

`F` is the prescribed product polynomial and `𝒢` is Definition 3.5's operator, built here
from `MvPolynomial.pderiv` in the eight formal matrix entries.  At the interior witness
`F` vanishes while `𝒢 F` does not, so no scalar `λ` can satisfy `𝒢 F = λ F`. -/
theorem main_operator (r s N : ℝ) (hs : 0 < s) (hN : N = r + 2 * s + 3) :
    eval w Fp = 0 ∧ eval w (G r s N Fp) = -(s / 9) ∧
      ∀ lam : ℝ, G r s N Fp ≠ C lam * Fp := by
  refine ⟨Fp_at_w, GF_at_w r s N hN, fun lam hc => ?_⟩
  have h := congrArg (eval w) hc
  rw [GF_at_w r s N hN, eval_mul, eval_C, Fp_at_w, mul_zero] at h
  have : s = 0 := by linarith
  exact absurd this (ne_of_gt hs)

end Operator

end Principia.MathDB.P376316
