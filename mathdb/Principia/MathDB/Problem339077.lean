import Mathlib

/-!
# MathDB #339077 — the three-shifted q-Motzkin divisibility conjecture is FALSE

Write-up `mathdb-open-problems/problems/339077/solution.tex`,
*A counterexample to the three-shifted q-Motzkin divisibility conjecture*, 18 September 2026.

With `M₀ = 1` and `M_{n+1}(q) = M_n(q) + ∑_{r<n} q^{r+1} M_r(q) M_{n-r-1}(q)`, set
`D_n(q) = det [M_{i+j+3}(q)]_{i,j<n}` and `t_n(q) = ∑_{r ≤ ⌊n/3⌋} q^{3r}`.  Conjecture A.3
intends `D_n = (−1)^⌊n/3⌋ q^{c_n} g_n` with `g_n ∈ ℤ≥0[q]`, and asserts `t_n ∣ g_n` when
`n ≡ 2 (mod 3)`.

At `n = 5` that fails.  Specialising the recurrence to `q = −1` gives the integer sequence
`a_j = M_j(−1) = (1,1,0,0,1,1,−1,−1,3,3,−6,−6)`, and the Hankel matrix `A = [a_{i+j+3}]` has

`D₅(−1) = det A = 2 ≠ 0`,  while  `t₅(−1) = 1 + (−1)³ = 0`.

Any `g` divisible by `X³ + 1` vanishes at `−1`, so no `s` and `c` can satisfy
`det A = s · (−1)^c · g(−1)`.  That is `main`.

## Scope, stated honestly

This refutes the **divisibility** assertion only — the part the write-up calls substantive — and
says nothing about the sign, the monomial prefactor, or nonnegativity of `g_n`.  Refuting more
than the witness supports would prove less.  The write-up also records that the journal final was
unavailable for a corrections check, so it claims **zero campaign credit** for this result; that
is a statement about the collaborator's credit accounting, not about the mathematics, which is a
finite integer computation reproduced below.

Checked in Python before formalizing: the twelve values `a_j` from the specialised recurrence,
the matrix `A`, `det A = 2`, and `t₅(−1) = 0`.
-/

namespace Principia.MathDB.P339077

open Matrix

/-- `a j = M_j(−1)`, the Motzkin-like polynomials specialised at `q = −1`. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => -1
  | 7 => -1
  | 8 => 3
  | 9 => 3
  | 10 => -6
  | 11 => -6
  | _ => 0

/-- The table really does satisfy the defining recurrence at `q = −1`, over its whole range. -/
theorem a_rec : ∀ n ≤ 10,
    a (n + 1) = a n + ∑ r ∈ Finset.range n, (-1 : ℤ) ^ (r + 1) * a r * a (n - r - 1) := by
  -- NOT `decide`: a `Finset.sum` is a `Quot` of `Multiset` of `List`, and kernel reduction
  -- through `Quot` made this exceed twelve minutes.  Expanding the sum is 44 seconds.
  intro n hn
  interval_cases n <;> simp [Finset.sum_range_succ, a] <;> norm_num

/-- The three-shifted Hankel matrix `[a_{i+j+3}]` of order five. -/
def A : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 0,  1,  1, -1, -1;
      1,  1, -1, -1,  3;
      1, -1, -1,  3,  3;
     -1, -1,  3,  3, -6;
     -1,  3,  3, -6, -6]

/-- `A` is exactly the three-shifted Hankel matrix of `a`. -/
theorem A_eq : ∀ i j : Fin 5, A i j = a (i.val + j.val + 3) := by decide

/-- **`D₅(−1) = 2`.**  `Matrix.det` sums over the 120 permutations of `Fin 5`, which the kernel
handles directly — no cofactor expansion is needed at this size. -/
theorem detA : A.det = 2 := by decide +kernel

/-- `t₅ = X³ + 1` vanishes at `−1`. -/
theorem t5_eval : ((Polynomial.X ^ 3 + 1 : Polynomial ℤ)).eval (-1) = 0 := by simp

/-- **MathDB #339077 — the divisibility half of Conjecture A.3 is FALSE.**  If `D₅` factored as
`s · q^c · g` with `t₅ = X³ + 1` dividing `g`, then evaluating at `q = −1` would force
`D₅(−1) = 0`; but `D₅(−1) = det A = 2`. -/
theorem main (g h : Polynomial ℤ) (c : ℕ) (s : ℤ)
    (hg : g = (Polynomial.X ^ 3 + 1) * h)
    (hD : A.det = s * (-1) ^ c * g.eval (-1)) : False := by
  rw [hg, Polynomial.eval_mul, t5_eval, zero_mul, mul_zero, detA] at hD
  exact absurd hD (by norm_num)

end Principia.MathDB.P339077
