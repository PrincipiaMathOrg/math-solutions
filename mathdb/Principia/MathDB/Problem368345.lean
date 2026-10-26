import Mathlib

/-!
# MathDB #368345 — Fang–Zhang–Zhao Conjecture 4.3 is FALSE

Write-up `mathdb-open-problems/problems/368345/solution.tex`,
*Hoggatt sums fail infinite log-convexity for every `m ≥ 4`*, 18 September 2026.

With the source's operator `(ℒa)_n = a_n a_{n+2} − a_{n+1}²`, a sequence is *infinitely
log-convex* when every entry of `ℒ^r a` is nonnegative for every `r ≥ 1`.  The Hoggatt sums are

`A_n(m) = ∑_{k=0}^{n-1} (∏_{i=0}^{m-1} C(n+m−2, k+i)) / (∏_{j=1}^{m-1} C(n+m−2, j))`,  `n ≥ 1`,

and Conjecture 4.3 asserts that `(A_n(m))_{n≥1}` is infinitely log-convex for every `m ≥ 2`.

It fails at `m = 4`:

`(ℒ⁴ A(4))_2 = −111509459048444462640611465400686603136 < 0`.

That single entry refutes the conjecture, and `main` says exactly that.

## Why this is a finite certificate and nothing more is needed

`ℒ⁴` at index `2` reads `ℒ³` at `2,3,4`, hence `ℒ²` at `2…6`, hence `ℒ` at `2…8`, hence `A(4)` at
`2…10` — nine values, each an explicit binomial sum.  So no asymptotics, no generating function,
and no statement about general `m` enters: the conjecture is universally quantified over `m ≥ 2`,
so one `m` kills it.

`A` is defined here **from the source's formula**, not tabulated, and the nine values are derived
from that definition (`A4_2 … A4_10`).  Tabulating them instead would have proved a statement
about a table rather than about the Hoggatt sums.  The denominator's index range `1 ≤ j ≤ m−1` is
written as `j + 1` over `Finset.range (m−1)`, which is the same product with no `Finset.Icc`.

`iterates_nonneg_before` records that `ℒ¹, ℒ², ℒ³` are all **positive** at index `2`, so `r = 4`
is genuinely the first failure — the counterexample is minimal in `r`, not merely some failure
found far out.

## Scope, stated honestly

This refutes **Conjecture 4.3 as stated**, using `m = 4`.  The write-up proves more — failure for
*every* `m ≥ 4`, with `ℒ³` already negative once `m ≥ 6` — and that stronger family is **not**
formalized here; refuting the conjecture does not need it.  The write-up leaves the Baxter case
`m = 3` undecided and records that the journal final was not read, so it claims **pending**
campaign eligibility; that is the collaborator's accounting, not a mathematical qualification.

Note the refutation uses the *small* index `n = 2`.  The source's definition of infinite
log-convexity asks for nonnegativity of **every** entry, not merely eventual nonnegativity, so
this is a legitimate witness against the conjecture as posed; it would not refute an "eventually
nonnegative" variant, which the source does not assert.

Checked in Python before formalizing, with exact rational arithmetic: `A_n(4)` for `n = 1…10`
reproduces the write-up's `(1, 2, 7, 32, 177, 1122, 7898, 60398, 494078, 4274228)` from formula
(1); the `ℒ` and `ℒ²` tables of the write-up's display (4) reproduce entry by entry; both large
certificates of display (2) reproduce exactly (`m = 4` and `m = 5`); and `(ℒ³A(m))_2 < 0` for
`m = 6…10`.
-/

namespace Principia.MathDB.P368345

/-- The Hoggatt sums `A_n(m)` of the source's formula (1). -/
noncomputable def A (m n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ∏ i ∈ Finset.range m, (Nat.choose (n + m - 2) (k + i) : ℚ)) /
    (∏ j ∈ Finset.range (m - 1), (Nat.choose (n + m - 2) (j + 1) : ℚ))

/-- The source's operator `(ℒa)_n = a_n a_{n+2} − a_{n+1}²`. -/
noncomputable def L (a : ℕ → ℚ) (n : ℕ) : ℚ := a n * a (n + 2) - a (n + 1) ^ 2

/-- Infinite log-convexity in the source's sense: **every** entry of every iterate is
nonnegative. -/
def InfLogConvex (a : ℕ → ℚ) : Prop := ∀ r, 1 ≤ r → ∀ n, 1 ≤ n → 0 ≤ (L^[r] a) n

/-- **Conjecture 4.3** (Fang–Zhang–Zhao): the Hoggatt sums are infinitely log-convex for every
`m ≥ 2`. -/
def Conj43 : Prop := ∀ m, 2 ≤ m → InfLogConvex (A m)

section Values

-- `norm_num` does not evaluate `Nat.choose`; expand the `Finset` sums and products
-- FIRST, then hand `Nat.choose` to `norm_num` as a rewrite.
theorem A4_1 : A 4 1 = 1 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_2 : A 4 2 = 2 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_3 : A 4 3 = 7 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_4 : A 4 4 = 32 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_5 : A 4 5 = 177 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_6 : A 4 6 = 1122 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_7 : A 4 7 = 7898 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_8 : A 4 8 = 60398 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_9 : A 4 9 = 494078 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

theorem A4_10 : A 4 10 = 4274228 := by
  simp only [A, Finset.sum_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.sum_empty, Finset.prod_empty]
  norm_num [Nat.choose]

end Values

/-- The write-up's display (3): the ten Hoggatt sums at `m = 4`, straight from the definition. -/
theorem hoggatt_values :
    A 4 1 = 1 ∧ A 4 2 = 2 ∧ A 4 3 = 7 ∧ A 4 4 = 32 ∧ A 4 5 = 177 ∧ A 4 6 = 1122 ∧
      A 4 7 = 7898 ∧ A 4 8 = 60398 ∧ A 4 9 = 494078 ∧ A 4 10 = 4274228 :=
  ⟨A4_1, A4_2, A4_3, A4_4, A4_5, A4_6, A4_7, A4_8, A4_9, A4_10⟩

/-- Unfold the four iterates and substitute the nine values `A 4 2 … A 4 10`. -/
theorem unfold_iterates :
    (L^[4] (A 4)) 2 = L (L (L (L (A 4)))) 2 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]

/-- **The certificate.**  `(ℒ⁴A(4))_2 = −111509459048444462640611465400686603136`. -/
theorem iterate_four_at_two :
    (L^[4] (A 4)) 2 = -111509459048444462640611465400686603136 := by
  rw [unfold_iterates]
  simp only [L]
  rw [A4_2, A4_3, A4_4, A4_5, A4_6, A4_7, A4_8, A4_9, A4_10]
  norm_num

/-- `r = 4` is the FIRST failure: the first three iterates are strictly positive at index `2`. -/
theorem iterates_nonneg_before :
    (L^[1] (A 4)) 2 = 15 ∧ (L^[2] (A 4)) 2 = 22400 ∧ (L^[3] (A 4)) 2 = 38581511487375 := by
  -- The three goals read DIFFERENT subsets of the values, so each gets its own rewrite list.
  -- (A shared `simp only` carrying all seven as lemmas leaves `A 4 3`, `A 4 4`, … unrewritten.)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, L]
    rw [A4_2, A4_3, A4_4]; norm_num
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, L]
    rw [A4_2, A4_3, A4_4, A4_5, A4_6]; norm_num
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, L]
    rw [A4_2, A4_3, A4_4, A4_5, A4_6, A4_7, A4_8]; norm_num

/-- **MathDB #368345 — Conjecture 4.3 is FALSE.**  The Hoggatt sums at `m = 4` are not infinitely
log-convex: the fourth iterate is negative at index `2`.

`m = 4` satisfies the conjecture's own hypothesis `m ≥ 2`, and `r = 4`, `n = 2` satisfy `r ≥ 1`,
`n ≥ 1`, so the witness meets every guard the conjecture imposes. -/
theorem main : ¬ Conj43 := by
  intro h
  have hn := h 4 (by norm_num) 4 (by norm_num) 2 (by norm_num)
  rw [iterate_four_at_two] at hn
  norm_num at hn

end Principia.MathDB.P368345
