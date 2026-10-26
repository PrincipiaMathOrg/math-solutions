import Mathlib.Tactic.NormNum
import Mathlib.Logic.Function.Iterate

/-!
# MathDB #317479 — the LIS polynomials are not infinitely q-log-convex

Write-up: `mathdb-open-problems/problems/317479/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source conjecture: W. Y. C. Chen, *Log-concavity and q-Log-convexity Conjectures on the
Longest Increasing Subsequences of Permutations*, arXiv:0806.3392v2, **Conjecture 1.4**.

Let `P_{n,k}` count permutations of `{1,…,n}` whose longest increasing subsequence has
length `k`, and `P_n(q) = ∑_k P_{n,k} q^k`.  Chen conjectures the family is *infinitely
q-log-convex*: every iterate of the centered operator

`(𝓗A)_n = A_{n-1} A_{n+1} − A_n²`

is coefficientwise nonnegative.  The write-up refutes this: `(𝓗³P)_5` has degree 34 with
leading coefficient `−32`, and evaluates to a negative integer at `q = 6`.

## What this module proves, and in which reading

`𝓗` is defined **pointwise in `q`**, so evaluation commutes with it: evaluating each `P_n`
at a fixed `q` and then iterating gives the same numbers as iterating and then evaluating.
Hence coefficientwise nonnegativity of every iterate implies, for every `q ≥ 0`, that the
NUMERICAL sequence `n ↦ P_n(q)` is infinitely log-convex in the sense of `InfLogConvex`
below.  This module refutes that consequence at `q = 6`, which refutes Chen's conjecture.
Refuting the weaker, evaluated statement is the stronger result.

**The witness carries no boundary convention.**  The write-up notes it uses only
`P_2, …, P_8`.  `main` is therefore stated for an ARBITRARY sequence agreeing with those
seven values — however it is extended below `2` or above `8`, it is not infinitely
log-convex.  A truncated sequence padded with zeros would have left open the objection that
the padding, not the mathematics, caused the failure.

**Not Lean-checked here:** that these seven integers really are `P_n(6)`, and the
degree bookkeeping behind the `−32` leading coefficient.  Both are combinatorial facts about
Young tableaux and polynomial degrees that Mathlib cannot currently express cheaply; they are
checked instead by `Campaigns/MathDB-Formalization/verify_317479.py`, which enumerates all
46232 permutations of sizes 2–8, recomputes `P_{n,k}` from scratch, cross-checks the
write-up's printed `a_n`/`b_n` tables against both the enumeration and the hook-length
formula, and reproduces `(𝓗³P)_5(6)` and the `−32` exactly.

## The values

`P_n(6)` for `n = 2 … 8`: `42, 366, 3714, 43170, 562650, 8112390, 128008770`, whence
`(𝓗³P)_5(6) = −8449005348498088692649082880000 < 0`.
-/

namespace Principia.MathDB.P317479

/-- The centered log-convexity operator `(𝓗A)_n = A_{n-1} A_{n+1} − A_n²`. -/
def H (A : ℕ → ℤ) : ℕ → ℤ := fun n => A (n - 1) * A (n + 1) - A n ^ 2

/-- Infinite log-convexity of an integer sequence: every iterate of `H` is nonnegative
from index `1` on.  This is what Chen's conjecture implies for `n ↦ P_n(q)` at each
`q ≥ 0`, because `H` acts pointwise in `q`. -/
def InfLogConvex (A : ℕ → ℤ) : Prop := ∀ r n, 1 ≤ n → 0 ≤ (H^[r] A) n

/-- The third iterate at index `5`, for any sequence carrying the seven LIS values at
`q = 6`.  Only `A 2 … A 8` occur, which is why no boundary convention is needed. -/
theorem iterate3_at5 (A : ℕ → ℤ)
    (h2 : A 2 = 42) (h3 : A 3 = 366) (h4 : A 4 = 3714) (h5 : A 5 = 43170)
    (h6 : A 6 = 562650) (h7 : A 7 = 8112390) (h8 : A 8 = 128008770) :
    (H^[3] A) 5 = -8449005348498088692649082880000 := by
  show H (H (H A)) 5 = _
  simp only [H]
  norm_num [h2, h3, h4, h5, h6, h7, h8]

/-- **Chen's Conjecture 1.4 is FALSE.**  No sequence carrying the seven values
`P_2(6), …, P_8(6)` is infinitely log-convex — whatever it does outside that window. -/
theorem main (A : ℕ → ℤ)
    (h2 : A 2 = 42) (h3 : A 3 = 366) (h4 : A 4 = 3714) (h5 : A 5 = 43170)
    (h6 : A 6 = 562650) (h7 : A 7 = 8112390) (h8 : A 8 = 128008770) :
    ¬ InfLogConvex A := by
  intro hconv
  have hneg := iterate3_at5 A h2 h3 h4 h5 h6 h7 h8
  have hpos := hconv 3 5 (by norm_num)
  rw [hneg] at hpos
  norm_num at hpos

end Principia.MathDB.P317479
