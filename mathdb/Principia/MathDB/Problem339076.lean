import Mathlib

/-!
# MathDB #339076 — the printed two-shifted q-Motzkin evaluation is FALSE

Write-up `mathdb-open-problems/problems/339076/solution.tex`,
*An exact evaluation of the two-shifted q-Motzkin determinant*, 18 September 2026.

With `M₀ = 1` and `M_{n+1}(q) = M_n(q) + ∑_{r<n} q^{r+1} M_r(q) M_{n-r-1}(q)`, set
`D_n^{(2)} = det [M_{i+j+2}(q)]_{i,j<n}`.  Conjecture A.2 predicts `D_n^{(2)} = q^{c_n} f_n(q)`
with, for `n ≡ 0 (mod 3)`,

`f_n(q) = ∑_{1 ≤ l ≤ n, l ≢ 1 (mod 3)} q^l`,   so   `f₃(q) = q² + q³`.

At `n = 3` the true value is `D₃^{(2)} = q¹¹ + q¹³ + q¹⁴`, which has **three** nonzero terms
against `f₃`'s two.  No monomial prefactor can repair that, and the cleanest way to say so is a
single evaluation: a monomial has value `1` at `q = 1`, so the printed form forces
`D₃^{(2)}(1) = f₃(1) = 2`, while in fact `D₃^{(2)}(1) = 3`.  That is `main`, and it refutes the
printed formula for **every** exponent `c`, not merely for the one the source prints.

## Scope, stated honestly

This refutes the printed **Conjecture A.2** at `n = 3`.  It does **not** formalize the write-up's
positive theorem — the condensation proof of `D_n^{(2)} = q^{S_n+n²} ∑_{j ≤ n, j ≢ 2 (3)} q^{-j}`
for all `n`, which would need Desnanot–Jacobi and Cigler's two credited evaluations.  What is
certified here is the counterexample plus the exact value at the counterexample (`detH`), which is
the first case of that theorem and is what the refutation rests on.

`missing_constant_term` records the write-up's diagnosis in the same breath: the corrected
polynomial is `q¹¹(1 + q² + q³)`, i.e. the printed `f₃` is missing precisely the constant term of
the normalized factor — the write-up's `g₃`.  The lower limit `1 ≤ l` in the printed sum is the
defect, and it is present in the primary preprint too.

The write-up claims **zero campaign credit** (the 2019 journal final could not be obtained for a
corrections check).  That is a statement about the collaborator's credit accounting, not about the
mathematics, which is the finite polynomial computation reproduced below.

Checked in Python before formalizing, with exact integer-coefficient arithmetic (no floating
point): `M₀ … M₇`; that `eq (sum)` of the write-up's theorem holds for `0 ≤ n ≤ 7`; that Cigler's
two credited inputs `D_n^{(0)} = q^{S_n}` and `D_n^{(1)} = κ_n q^{S_n+n(n-1)/2}` hold for
`0 ≤ n ≤ 7`; the Hankel entries below; `D₃^{(2)} = q¹¹ + q¹³ + q¹⁴`; the Motzkin specialisation
`M_n(1) = 1,1,2,4,9,21,51,127`; and `det [M_{i+j+2}(1)] = 3`.
-/

namespace Principia.MathDB.P339076

open Matrix

/-- `Mq n q = M_n(q)`, the q-Motzkin polynomials, tabulated over the range the `3 × 3` Hankel
matrix needs.  `Mq_rec` below certifies that this table is exactly the source's recurrence. -/
def Mq : ℕ → ℚ → ℚ
  | 0, _ => 1
  | 1, _ => 1
  | 2, q => 1 + q
  | 3, q => 1 + 2 * q + q ^ 2
  | 4, q => 1 + 3 * q + 3 * q ^ 2 + q ^ 3 + q ^ 4
  | 5, q => 1 + 4 * q + 6 * q ^ 2 + 4 * q ^ 3 + 3 * q ^ 4 + 2 * q ^ 5 + q ^ 6
  | 6, q => 1 + 5 * q + 10 * q ^ 2 + 10 * q ^ 3 + 8 * q ^ 4 + 7 * q ^ 5 + 5 * q ^ 6 + 3 * q ^ 7
              + q ^ 8 + q ^ 9
  | _, _ => 0

/-- The table satisfies the defining recurrence `M_{n+1} = M_n + ∑_{r<n} q^{r+1} M_r M_{n-r-1}`
over its whole range, so the determinant below really is the two-shifted q-Motzkin determinant
and not a table of unrelated polynomials. -/
theorem Mq_rec : ∀ n ≤ 5, ∀ q : ℚ,
    Mq (n + 1) q = Mq n q + ∑ r ∈ Finset.range n, q ^ (r + 1) * Mq r q * Mq (n - r - 1) q := by
  intro n hn q
  interval_cases n <;> norm_num [Finset.sum_range_succ, Mq] <;> ring

/-- The two-shifted Hankel matrix `[M_{i+j+2}]` of order three. -/
def H (q : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![Mq 2 q, Mq 3 q, Mq 4 q;
     Mq 3 q, Mq 4 q, Mq 5 q;
     Mq 4 q, Mq 5 q, Mq 6 q]

/-- `H` really is the two-shifted Hankel matrix of `Mq`. -/
theorem H_eq (q : ℚ) : ∀ i j : Fin 3, H q i j = Mq (i.val + j.val + 2) q := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [H]

set_option maxHeartbeats 1000000 in
/-- **The exact value at the counterexample.**  `D₃^{(2)} = q¹¹ + q¹³ + q¹⁴`, three nonzero
terms.

The `ring` call expands a `3 × 3` determinant whose entries reach degree `9`, so the normal form
passes through a few thousand monomials — comfortably correct, but past the default heartbeat
budget.  The raised limit is the whole cost; there is no search here, only expansion. -/
theorem detH (q : ℚ) : (H q).det = q ^ 11 + q ^ 13 + q ^ 14 := by
  -- `!![…]` is `Matrix.of ![…]`, so `Matrix.of_apply` must come before the `cons_val` lemmas or
  -- no entry reduces at all and `ring` is handed unreduced matrix applications.
  simp only [H, Matrix.of_apply, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Mq]
  ring

/-- The printed `f₃(q) = q² + q³` (the `n ≡ 0 (mod 3)` branch of Conjecture A.2 at `n = 3`). -/
def fprint (q : ℚ) : ℚ := q ^ 2 + q ^ 3

/-- The write-up's corrected normalized form at `n = 3`: `c₃ = 11` and `g₃ = 1 + q² + q³`.
The printed `f₃` is exactly `g₃` with its constant term dropped — the effect of the lower limit
`1 ≤ l` in the printed sum. -/
theorem missing_constant_term (q : ℚ) :
    (H q).det = q ^ 11 * (1 + q ^ 2 + q ^ 3) ∧ q ^ 11 * (1 + q ^ 2 + q ^ 3) - q ^ 11 * fprint q
      = q ^ 11 := by
  refine ⟨by rw [detH]; ring, by simp only [fprint]; ring⟩

/-- Term counts at `q = 1`: the true determinant evaluates to `3`, the printed formula to `2`. -/
theorem eval_one : (H 1).det = 3 ∧ fprint 1 = 2 := by
  refine ⟨by rw [detH]; norm_num, by norm_num [fprint]⟩

/-- **MathDB #339076 — Conjecture A.2 is FALSE at `n = 3`.**  No exponent whatsoever makes the
printed formula fit: a monomial `q^c` has value `1` at `q = 1`, so `D₃^{(2)} = q^c f₃` would give
`D₃^{(2)}(1) = f₃(1) = 2`, whereas `D₃^{(2)}(1) = 3`.

Quantifying over `c` is the point — the write-up's remark that the printed `f₃` "cannot be
repaired by changing only its monomial prefactor" is exactly this statement. -/
theorem main : ¬ ∃ c : ℕ, ∀ q : ℚ, (H q).det = q ^ c * fprint q := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  rw [detH] at h1
  simp only [fprint, one_pow, one_mul] at h1
  norm_num at h1

end Principia.MathDB.P339076
