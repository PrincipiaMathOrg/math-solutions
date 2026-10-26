import Principia.MathDB.Problem317479

/-!
# MathDB #317480 — matching crossing polynomials fail third-order q-log-convexity

Write-up: `mathdb-open-problems/problems/317480/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source conjecture: W. Y. C. Chen, arXiv:0806.3392v2, **Conjecture 1.8** — a DIFFERENT
conjecture from #317479's Conjecture 1.4, about a different family.

A perfect matching of the ordered set `[2n]` has crossing number `k` when `k` is the
maximum size of a set of pairwise crossing arcs (`(i,j)` and `(a,b)`, `i<j`, `a<b`, cross
iff `i<a<j<b` or `a<i<b<j`).  With `M_{2n,k}` counting those matchings and
`F_n(x) = M_{2n}(x) = ∑_k M_{2n,k} x^k`, Conjecture 1.8 asserts that every iterate of

`(𝓗A)_n = A_{n-1} A_{n+1} − A_n²`

is coefficientwise nonnegative (and proposes a further log-concavity property *for those
nonnegative iterates*, so the failure below strikes its first hypothesis).  The write-up
refutes it: `(𝓗³F)_5` has degree 34 with leading coefficient `−14224`.

## What this module proves

`H` and `InfLogConvex` are reused from `Problem317479` rather than restated — the operator
and the property are the same, only the sequence differs.

As there, `𝓗` acts **pointwise in `x`**, so evaluation commutes with iteration, and
coefficientwise nonnegativity of every iterate implies that the numeric sequence
`n ↦ F_n(x)` is infinitely log-convex for each `x ≥ 0`.  At `x = 10` it is not.  Refuting
that evaluated consequence refutes the conjecture, and since the evaluated statement is
weaker, refuting it is the stronger result.

**No boundary convention.**  The write-up calls this "an interior counterexample: only
`F_2, …, F_8` are involved".  `main` is accordingly stated for an ARBITRARY sequence
carrying those seven values, so no padding outside the window can be blamed.

**Not Lean-checked here:** that the seven integers are really `F_n(10)`, and the degree
bookkeeping behind the `−14224`.  Both are checked by
`Campaigns/MathDB-Formalization/verify_317480.py`, which enumerates **all 2173623** perfect
matchings of `[4], [6], …, [16]` (each exactly once, by pairing the smallest unmatched
point), computes each crossing number as a maximum clique in the crossing graph, confirms
every row total is `(2n−1)!!`, cross-checks the write-up's printed `a_n`/`b_n` tables, and
reproduces both the evaluation and the `−14224`.

## The values

`F_n(10)` for `n = 2 … 8`: `120, 1950, 37140, 820620, 20500020, 569321190, 17370468900`,
whence `(𝓗³F)_5(10) = −1584481155042307779051353803951488000000000 < 0`.
-/

namespace Principia.MathDB.P317480

open Principia.MathDB.P317479 (H InfLogConvex)

/-- The third iterate at index `5`, for any sequence carrying the seven crossing-polynomial
values at `x = 10`.  Only `A 2 … A 8` occur. -/
theorem iterate3_at5 (A : ℕ → ℤ)
    (h2 : A 2 = 120) (h3 : A 3 = 1950) (h4 : A 4 = 37140) (h5 : A 5 = 820620)
    (h6 : A 6 = 20500020) (h7 : A 7 = 569321190) (h8 : A 8 = 17370468900) :
    (H^[3] A) 5 = -1584481155042307779051353803951488000000000 := by
  show H (H (H A)) 5 = _
  simp only [H]
  norm_num [h2, h3, h4, h5, h6, h7, h8]

/-- **Chen's Conjecture 1.8 is FALSE.**  No sequence carrying the seven values
`F_2(10), …, F_8(10)` is infinitely log-convex — whatever it does outside that window. -/
theorem main (A : ℕ → ℤ)
    (h2 : A 2 = 120) (h3 : A 3 = 1950) (h4 : A 4 = 37140) (h5 : A 5 = 820620)
    (h6 : A 6 = 20500020) (h7 : A 7 = 569321190) (h8 : A 8 = 17370468900) :
    ¬ InfLogConvex A := by
  intro hconv
  have hneg := iterate3_at5 A h2 h3 h4 h5 h6 h7 h8
  have hpos := hconv 3 5 (by norm_num)
  rw [hneg] at hpos
  norm_num at hpos

end Principia.MathDB.P317480
