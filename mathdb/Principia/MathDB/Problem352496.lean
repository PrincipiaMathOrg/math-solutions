/-
MathDB #352496 — the Polynexus formula for nonzero interval-translation products.

`M_n` is the submonoid of the rook monoid consisting of the zero matrix together with the
matrices whose ones form a nonempty consecutive block on one diagonal; a nonzero element is a
triple `⟨d,k,m⟩` with `1 − min(0,d) ≤ k ≤ m ≤ n − max(0,d)`, equivalently the unique increasing
translation from an interval `A ⊆ [n]` to an interval `I ⊆ [n]` of the same length.  With

    ψ(n) = #{(x,y) ∈ (M_n \ {0})² : xy ≠ 0}

Conjecture 1 of Fikioris–Fikioris (§8, p. 207) asserts
`ψ(n) = ((n+1)⁷ − n⁷ − (n+1)³ + n³)/120`.

WHAT IS PROVED HERE — the two facts that make the statement well-formed and supply its first
ingredient, neither of which needs the counting argument.

* **`dvd_120`** — `120 ∣ (n+1)⁷ − n⁷ − (n+1)³ + n³` for every integer `n`, so the right-hand
  side is an integer at all.  A closed form presented as a fraction is not obviously a count;
  this is the obligation that gap creates, and the write-up passes over it.  Proved by `decide`
  over `ZMod 120` and transported with `ZMod.intCast_zmod_eq_zero_iff_dvd` — 120 residues, no
  case analysis by hand.
* **`six_mul_total`** — the write-up's equation (total), `T_n = ∑_{l=1}^n (n−l+1)² =
  n(n+1)(2n+1)/6`, the number of nonzero elements of `M_n`.  Stated as `6 * T n = n(n+1)(2n+1)`
  so that no division appears, and proved by induction.  The reindexing `∑_{l=1}^n (n−l+1)² =
  ∑_{j=1}^n j²` is where truncated `ℕ` subtraction would bite, so the sum is taken over
  `Finset.range` with the substitution already performed.

CARRIED.  `Conjecture1` itself.  Its proof counts the zero products through disjoint intermediate
intervals and evaluates the resulting weighted sum by a formal generating function — a genuine
combinatorial argument over the pair set, not in reach here.  Per the spine rule it is a named
hypothesis, never a `sorry`.

Reference: G. Fikioris and G. Fikioris, *A subsemigroup of the rook monoid*, Semigroup Forum;
Conjecture 1, Section 8, p. 207.  Note the write-up is explicit that `M_n` is the
interval-translation submonoid, **not** the full rook monoid `R_n`, and that products are counted
with their ordered factorizations rather than as distinct resulting matrices.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Principia.MathDB.P352496

open Finset

/-! ## 1. The closed form is integer-valued -/

/-- The numerator of the Polynexus formula. -/
def num (n : ℤ) : ℤ := (n + 1) ^ 7 - n ^ 7 - (n + 1) ^ 3 + n ^ 3

-- NB `set_option ... in` must precede the DOCSTRING: a docstring has to attach directly to its
-- declaration, so putting the option between them is a parse error ("expected 'lemma'").
set_option maxRecDepth 8000 in
/-- **`120` divides the numerator for every integer `n`**, so the formula denotes an integer.
A closed form presented as a fraction is not obviously a count; this is the obligation that gap
creates.  Proved over `ZMod 120` and transported. -/
theorem dvd_120 (n : ℤ) : (120 : ℤ) ∣ num n := by
  have key : ∀ x : ZMod 120, (x + 1) ^ 7 - x ^ 7 - (x + 1) ^ 3 + x ^ 3 = 0 := by decide
  have h : ((num n : ℤ) : ZMod 120) = 0 := by
    push_cast [num]
    exact key _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

/-- The value of the formula, as an integer. -/
def psiFormula (n : ℤ) : ℤ := num n / 120

theorem psiFormula_spec (n : ℤ) : 120 * psiFormula n = num n := by
  rw [psiFormula, Int.mul_ediv_cancel' (dvd_120 n)]

/-- Two sanity values the write-up's own description forces: `M_1 \ {0}` is a single element, so
`ψ(1) = 1`; and `ψ(2) = 17`. -/
theorem psiFormula_one : psiFormula 1 = 1 := by decide

theorem psiFormula_two : psiFormula 2 = 17 := by decide

/-! ## 2. The number of nonzero elements -/

/-- `T n = ∑_{j=1}^{n} j²`, the write-up's equation (total) after the reindexing
`∑_{l=1}^n (n−l+1)² = ∑_{j=1}^n j²`.  Summing over `range` with the substitution already
performed avoids truncated `ℕ` subtraction entirely. -/
def total (n : ℕ) : ℕ := ∑ j ∈ range n, (j + 1) ^ 2

/-- **`6 · T_n = n(n+1)(2n+1)`** — the write-up's closed form, with no division. -/
theorem six_mul_total (n : ℕ) : 6 * total n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [total, Finset.sum_range_succ, ← total, Nat.mul_add, ih]
      ring

/-! ## 3. The conjecture -/

/-- Conjecture 1 of Fikioris–Fikioris, relative to the counting function `psi` supplied as a
parameter.  `psi` is carried rather than defined: constructing `M_n` and its product would be a
substantial development, and the conjecture's CONTENT is the closed form, which is stated exactly.
(Compare row 299, where a predicate that dropped its subject was vacuous — here `psi` appears in
the statement, so the conjecture cannot be satisfied by ignoring it.) -/
def Conjecture1 (psi : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → psi n = psiFormula (n : ℤ)

/-- The two values any `psi` satisfying the conjecture must take, so the statement has testable
content at its smallest instances. -/
theorem conjecture_values (psi : ℕ → ℤ) (h : Conjecture1 psi) :
    psi 1 = 1 ∧ psi 2 = 17 := by
  constructor
  · rw [h 1 (by norm_num)]; exact psiFormula_one
  · rw [h 2 (by norm_num)]; exact psiFormula_two

end Principia.MathDB.P352496
