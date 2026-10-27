import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 4000000

/-!
# MathDB #367323 — the Hankel determinant `H_9^{(9)} = 256` (PARTIAL)

Write-up `mathdb-open-problems/problems/367323/solution.tex`,
*MathDB 367323: all multiples of three, with the exact signs*, 18 September 2026.
Source: Z. Wang and Y. Zhang, arXiv:2502.21050, Conjecture 3.

With `M(z) = 1 + zM(z) + z²M(z)²` (the Motzkin generating function) and

`H_N^{(r)} = det([z^{i+j}] M(z)^r)_{0 ≤ i,j < N}`,

the write-up proves, for `r ≥ 3` divisible by three and `ε_r = (−1)^{C(r,2)}`,

`H_{rn}^{(r)} = H_{rn+1}^{(r)} = ε_rⁿ (n+1)^{r−1}`  and
`H_{rn−1}^{(r)} + H_{rn+2}^{(r)} = −(r(r−3)/2) ε_rⁿ (n+1)^{r−1}`,

and reports that the source's Conjecture 3 carries a **sign error**, visible at `H_9^{(9)}`.

## What is proved here

`H9` : the single exact value **`H_9^{(9)} = 256`**, and `H9_formula`, that this is the
`ε_9·(1+1)^8` the write-up's corrected formula predicts (`ε_9 = (−1)^{C(9,2)} = (−1)^{36} = 1`).
This is the exact point at which the source is reported to differ.

## What is NOT proved, and why the row is not counted

The general theorem. Its proof runs through the translated semicircle measure, its monic
orthogonal polynomials `P_j = U_j((t−a)/2)`, and a Christoffel-type remainder determinant —
orthogonal-polynomial theory Mathlib does not have.

## A 215 note, and its RESOLUTION

The write-up says the source's printed sign gives `−256`, but it does **not** quote the printed
formula, so a Lean theorem asserting “Conjecture 3 as printed is false” would have certified
the write-up's prose about a document not in evidence.  That refusal was right, and it stood
until the document was located: **the printed statement is shipped alongside the write-up**, in
the problem's own directory (`mathdb-page-snapshot.txt`), which the note did not check.  It is
quoted and refuted in the `PrintedConjecture` section at the end of this file, and the refutation
rests on the same self-contained VALUE claim `H9` — no new determinant.

## How the entries are pinned, rather than transcribed

Every integer below is computed, and re-checked inside Lean -- and since 2026-09-25 the
chain is COMPOSED by a theorem rather than by this paragraph.  `Amat_eq_hankel` proves that
`Amat` IS the Hankel matrix of the ninth convolution power of any sequence satisfying the
write-up's defining equation, and `H9_hankel` states the headline in those terms with no
explicit matrix in it.  Before that, every link below was true and CONSUMED BY NOTHING, so a
reader had to compose them by hand:

* `mot_base` and `mot_rec` verify the defining equation `M = 1 + zM + z²M²` coefficientwise
  (`m₀ = 1`, `m₁ = m₀`, `m_{n+2} = m_{n+1} + ∑_{k≤n} m_k m_{n−k}`) across the whole range the
  determinant depends on.  Together these determine `m₀ … m₁₆` uniquely, so the listed
  coefficients ARE `M`'s.
* `mpow2_conv` … `mpow9_conv` verify each convolution step, so `mpow9` is `[z^k] M(z)^9`.
* `Amat_entries` verifies that the matrix used for the determinant has exactly those entries.

Only then is the determinant computed, by an LU certificate: `LU_eq` checks `L * U = A`
entrywise, `Lmat_tri`/`Umat_tri` check triangularity, and `det_mul` with
`det_of_lowerTriangular`/`det_of_upperTriangular` gives the value.  `decide` on `Matrix.det`
over `Fin 9` is not an option — it would enumerate `9! = 362880` permutations.

Python cross-check: `Campaigns/MathDB-Formalization/check_367323.py`, which also confirms
every instance of both displayed identities for `r ∈ {3,6,9}`, `n ≤ 2`.
-/

namespace Principia.MathDB.P367323

open Finset Matrix

/-- Lookup with `0` off the end. -/
def gt (l : List ℤ) (n : ℕ) : ℤ := l.getD n 0

/-- The first 17 coefficients of `M(z)`. -/
def mot : List ℤ :=
  [1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798, 15511, 41835, 113634,
    310572, 853467]

/-- **`mot` satisfies the write-up's defining equation** `M = 1 + zM + z²M²`, read off
coefficientwise: `m_{n+2} = m_{n+1} + ∑_{k≤n} m_k m_{n-k}`, on the whole range the
determinant depends on. -/
theorem mot_rec : ∀ n ∈ range 15,
    gt mot (n + 2) = gt mot (n + 1) + ∑ k ∈ range (n + 1), gt mot k * gt mot (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^2`. -/
def mpow2 : List ℤ :=
  [1, 2, 5, 12, 30, 76, 196, 512, 1353, 3610, 9713, 26324, 71799, 196938,
    542895, 1503312, 4179603]

theorem mpow2_conv : ∀ n ∈ range 17,
    gt mpow2 n = ∑ k ∈ range (n + 1), gt mot k * gt mot (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^3`. -/
def mpow3 : List ℤ :=
  [1, 3, 9, 25, 69, 189, 518, 1422, 3915, 10813, 29964, 83304, 232323,
    649845, 1822824, 5126520, 14453451]

theorem mpow3_conv : ∀ n ∈ range 17,
    gt mpow3 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow2 (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^4`. -/
def mpow4 : List ℤ :=
  [1, 4, 14, 44, 133, 392, 1140, 3288, 9438, 27016, 77220, 220584, 630084,
    1800384, 5147328, 14727168, 42171849]

theorem mpow4_conv : ∀ n ∈ range 17,
    gt mpow4 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow3 (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^5`. -/
def mpow5 : List ℤ :=
  [1, 5, 20, 70, 230, 726, 2235, 6765, 20240, 60060, 177177, 520455,
    1524120, 4453320, 12991230, 37854954, 110218905]

theorem mpow5_conv : ∀ n ∈ range 17,
    gt mpow5 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow4 (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^6`. -/
def mpow6 : List ℤ :=
  [1, 6, 27, 104, 369, 1242, 4037, 12804, 39897, 122694, 373581, 1128816,
    3390582, 10136556, 30192102, 89662216, 265640691]

theorem mpow6_conv : ∀ n ∈ range 17,
    gt mpow6 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow5 (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^7`. -/
def mpow7 : List ℤ :=
  [1, 7, 35, 147, 560, 2002, 6853, 22737, 73710, 234780, 737646, 2292654,
    7064316, 21615160, 65759570, 199117226, 600560037]

theorem mpow7_conv : ∀ n ∈ range 17,
    gt mpow7 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow6 (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^8`. -/
def mpow8 : List ℤ :=
  [1, 8, 44, 200, 814, 3080, 11076, 38376, 129285, 426192, 1381080,
    4414288, 13952308, 43695440, 135802120, 419367696, 1288054878]

theorem mpow8_conv : ∀ n ∈ range 17,
    gt mpow8 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow7 (n - k) := by
  decide

/-- The first 17 coefficients of `M(z)^9`. -/
def mpow9 : List ℤ :=
  [1, 9, 54, 264, 1143, 4563, 17199, 62127, 217242, 740554, 2473704,
    8127972, 26347110, 84448350, 268127145, 844521291, 2641866894]

theorem mpow9_conv : ∀ n ∈ range 17,
    gt mpow9 n = ∑ k ∈ range (n + 1), gt mot k * gt mpow8 (n - k) := by
  decide

def Amat : Matrix (Fin 9) (Fin 9) ℚ :=
  Matrix.of ![
    ![(1 : ℚ), (9 : ℚ), (54 : ℚ), (264 : ℚ), (1143 : ℚ), (4563 : ℚ), (17199 : ℚ), (62127 : ℚ),
      (217242 : ℚ)], 
    ![(9 : ℚ), (54 : ℚ), (264 : ℚ), (1143 : ℚ), (4563 : ℚ), (17199 : ℚ), (62127 : ℚ),
      (217242 : ℚ), (740554 : ℚ)], 
    ![(54 : ℚ), (264 : ℚ), (1143 : ℚ), (4563 : ℚ), (17199 : ℚ), (62127 : ℚ), (217242 : ℚ),
      (740554 : ℚ), (2473704 : ℚ)], 
    ![(264 : ℚ), (1143 : ℚ), (4563 : ℚ), (17199 : ℚ), (62127 : ℚ), (217242 : ℚ), (740554 : ℚ),
      (2473704 : ℚ), (8127972 : ℚ)], 
    ![(1143 : ℚ), (4563 : ℚ), (17199 : ℚ), (62127 : ℚ), (217242 : ℚ), (740554 : ℚ), (2473704 : ℚ),
      (8127972 : ℚ), (26347110 : ℚ)], 
    ![(4563 : ℚ), (17199 : ℚ), (62127 : ℚ), (217242 : ℚ), (740554 : ℚ), (2473704 : ℚ),
      (8127972 : ℚ), (26347110 : ℚ), (84448350 : ℚ)], 
    ![(17199 : ℚ), (62127 : ℚ), (217242 : ℚ), (740554 : ℚ), (2473704 : ℚ), (8127972 : ℚ),
      (26347110 : ℚ), (84448350 : ℚ), (268127145 : ℚ)], 
    ![(62127 : ℚ), (217242 : ℚ), (740554 : ℚ), (2473704 : ℚ), (8127972 : ℚ), (26347110 : ℚ),
      (84448350 : ℚ), (268127145 : ℚ), (844521291 : ℚ)], 
    ![(217242 : ℚ), (740554 : ℚ), (2473704 : ℚ), (8127972 : ℚ), (26347110 : ℚ), (84448350 : ℚ),
      (268127145 : ℚ), (844521291 : ℚ), (2641866894 : ℚ)]]

/-- The matrix entries ARE the coefficients certified above. -/
theorem Amat_entries : ∀ i : Fin 9, ∀ j : Fin 9,
    Amat i j = ((gt mpow9 ((i : ℕ) + (j : ℕ)) : ℤ) : ℚ) := by
  decide

def Lmat : Matrix (Fin 9) (Fin 9) ℚ :=
  Matrix.of ![
    ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(9 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(54 : ℚ), (74 / 9 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(264 : ℚ), (137 / 3 : ℚ), (1335 / 157 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
      (0 : ℚ)], 
    ![(1143 : ℚ), (212 : ℚ), (7623 / 157 : ℚ), (2868 / 455 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ),
      (0 : ℚ), (0 : ℚ)], 
    ![(4563 : ℚ), (884 : ℚ), (35919 / 157 : ℚ), (13491 / 455 : ℚ), (262193 / 29889 : ℚ), (1 : ℚ),
      (0 : ℚ), (0 : ℚ), (0 : ℚ)], 
    ![(17199 : ℚ), (3432 : ℚ), (151200 / 157 : ℚ), (488818 / 4095 : ℚ), (1022069 / 19926 : ℚ),
      (724254 / 60067 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)], 
    ![(62127 : ℚ), (12663 : ℚ), (590646 / 157 : ℚ), (120691 / 273 : ℚ), (544255 / 2214 : ℚ),
      (697923 / 8581 : ℚ), (186537939 / 20796373 : ℚ), (1 : ℚ), (0 : ℚ)], 
    ![(217242 : ℚ), (1214624 / 27 : ℚ), (6565900 / 471 : ℚ), (141168 / 91 : ℚ),
      (10438930 / 9963 : ℚ), (25659024 / 60067 : ℚ), (1115470170 / 20796373 : ℚ),
      (46576 / 4653 : ℚ), (1 : ℚ)]]

def Umat : Matrix (Fin 9) (Fin 9) ℚ :=
  Matrix.of ![
    ![(1 : ℚ), (9 : ℚ), (54 : ℚ), (264 : ℚ), (1143 : ℚ), (4563 : ℚ), (17199 : ℚ), (62127 : ℚ),
      (217242 : ℚ)], 
    ![(0 : ℚ), (-27 : ℚ), (-222 : ℚ), (-1233 : ℚ), (-5724 : ℚ), (-23868 : ℚ), (-92664 : ℚ),
      (-341901 : ℚ), (-1214624 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (157 / 3 : ℚ), (445 : ℚ), (2541 : ℚ), (11973 : ℚ), (50400 : ℚ),
      (196882 : ℚ), (6565900 / 9 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (4095 / 157 : ℚ), (25812 / 157 : ℚ), (121419 / 157 : ℚ),
      (488818 / 157 : ℚ), (1810365 / 157 : ℚ), (6352560 / 157 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-59778 / 455 : ℚ), (-524386 / 455 : ℚ),
      (-3066207 / 455 : ℚ), (-2938977 / 91 : ℚ), (-12526716 / 91 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (60067 / 29889 : ℚ), (241418 / 9963 : ℚ),
      (180943 / 1107 : ℚ), (8553008 / 9963 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-20796373 / 1081206 : ℚ),
      (-8882759 / 51486 : ℚ), (-61970565 / 60067 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-24816 / 20796373 : ℚ),
      (-745216 / 62389119 : ℚ)], 
    ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (16 / 13959 : ℚ)]]

theorem LU_eq : Lmat * Umat = Amat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Amat, Lmat, Umat, Fin.sum_univ_succ]

theorem Lmat_tri : Lmat.BlockTriangular OrderDual.toDual := by
  intro i j h
  rw [OrderDual.toDual_lt_toDual] at h
  fin_cases i <;> fin_cases j <;> simp_all [Lmat]

theorem Umat_tri : Umat.BlockTriangular id := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [Umat]

theorem Lmat_det : Lmat.det = 1 := by
  rw [Matrix.det_of_lowerTriangular Lmat Lmat_tri]
  norm_num [Lmat, Fin.prod_univ_succ]

theorem Umat_det : Umat.det = 256 := by
  rw [Matrix.det_of_upperTriangular Umat_tri]
  norm_num [Umat, Fin.prod_univ_succ]

/-- **`H_9^{(9)} = 256`.** -/
theorem H9 : Amat.det = 256 := by
  rw [← LU_eq, Matrix.det_mul, Lmat_det, Umat_det]
  ring

/-- The two low-order coefficients of the defining equation.  With `mot_rec` these pin
`mot 0 … mot 16` uniquely, so the listed numbers are forced, not chosen. -/
theorem mot_base : gt mot 0 = 1 ∧ gt mot 1 = gt mot 0 := by decide

/-- The value is exactly the write-up's corrected formula at `r = 9`, `n = 1`:
`ε_9¹·(1+1)^{9−1}` with `ε_9 = (−1)^{C(9,2)}`. -/
theorem H9_formula : Amat.det = (-1 : ℚ) ^ Nat.choose 9 2 * 2 ^ 8 := by
  have h : Nat.choose 9 2 = 36 := by decide
  rw [H9, h]
  norm_num

section PrintedConjecture

/-! ### The printed Conjecture 3 is now IN EVIDENCE, and it is false

The "215 note" above declined to state *"Conjecture 3 as printed is false"*, on the ground that
the write-up never quotes the printed formula, so such a theorem would certify prose about a
document not in evidence.  That was the right call — and the document turns out to be shipped
alongside the write-up, in the problem's own directory, which the note did not check.

`mathdb-open-problems/problems/367323/mathdb-page-snapshot.txt`, on branch `mathdb-results`
at `b210789d`, prints the problem as follows, verbatim up to LaTeX stripping:

> For `r ≡ 0 (mod 3)`, the conjecture asserts
> `H_rn(F(x,r)) = H_rn+1(F(x,r)) = (-1)^n (n+1)^(r-1)`.
> `H_rn+2(F(x,r)) + H_rn-1(F(x,r)) = 3^2 α (n+1)^(r-1)`, where `|α| = (1/18) r(r-3)`.

So the printed first display carries the sign `(-1)^n`, where the write-up's corrected form
carries `ε_r^n` with `ε_r = (-1)^{C(r,2)}`.  **`not_printed_first` is the refutation**, and it
needs no new determinant: `H9` already proves `H_9^{(9)} = 256`, while the printed display
demands `(-1)^1 · 2^8 = -256`.

**Why `r = 9` and not earlier.**  `ε_3 = ε_6 = -1`, which is exactly the printed `(-1)^n`, so
the printed formula is CORRECT at `r = 3` and `r = 6`; `ε_9 = (-1)^36 = +1` is the first
disagreement (`eps_diverges_at_nine`).  The error is not a one-off: within the paper's own range
`r ≤ 27` the printed sign is wrong for `r = 9, 12, 21, 24` — precisely the multiples of three
with `C(r,2)` even — and `r = 9` is merely the smallest.  Checked in
`Campaigns/MathDB-Formalization/check_367323_printed.py`, which asserts the violation set
EXACTLY and carries the corrected display at all nine `(r, n)` pairs with `r ∈ {3,6,9}`,
`n ≤ 2` as its positive control.

**What is deliberately still NOT claimed.**  The printed SECOND display is *not* refuted here,
and that is a fact about it rather than an omission: it pins `α` only in modulus, and
`3²·(1/18)·r(r-3) = r(r-3)/2` is exactly the magnitude the write-up's corrected version carries,
so at `r = 9`, `n = 1` both give `6912` up to sign and the printed form's free sign absorbs the
difference.  Only the first display is falsifiable from a single determinant.
-/

/-- The PRINTED first display of Wang–Zhang Conjecture 3, as the problem statement prints it:
for `r ≡ 0 (mod 3)`, `H_{rn} = H_{rn+1} = (-1)^n (n+1)^{r-1}`.  `Hval` is any indexing of the
Hankel determinants of `M(z)^r`. -/
def PrintedFirst (Hval : ℕ → ℚ) (r n : ℕ) : Prop :=
  Hval (r * n) = (-1 : ℚ) ^ n * ((n : ℚ) + 1) ^ (r - 1)
    ∧ Hval (r * n + 1) = (-1 : ℚ) ^ n * ((n : ℚ) + 1) ^ (r - 1)

/-- The witness lies inside the printed conjecture's own hypothesis `r ≡ 0 (mod 3)`, `r ≥ 3`. -/
theorem printed_witness_in_scope : 9 % 3 = 0 ∧ 3 ≤ 9 := by norm_num

theorem eps_three : (-1 : ℚ) ^ Nat.choose 3 2 = -1 := by
  rw [show Nat.choose 3 2 = 3 from rfl]
  norm_num

theorem eps_six : (-1 : ℚ) ^ Nat.choose 6 2 = -1 := by
  rw [show Nat.choose 6 2 = 15 from rfl]
  norm_num

theorem eps_nine : (-1 : ℚ) ^ Nat.choose 9 2 = 1 := by
  rw [show Nat.choose 9 2 = 36 from rfl]
  norm_num

theorem eps_twelve : (-1 : ℚ) ^ Nat.choose 12 2 = 1 := by
  rw [show Nat.choose 12 2 = 66 from rfl]
  norm_num

/-- **`r = 9` is the first divergence.**  The printed sign `(-1)^n` and the write-up's `ε_r^n`
agree at `r = 3` and `r = 6`, where `ε_r = -1`, and differ from `r = 9` on, where `ε_r = +1`. -/
theorem eps_diverges_at_nine :
    (-1 : ℚ) ^ Nat.choose 3 2 = -1 ∧ (-1 : ℚ) ^ Nat.choose 6 2 = -1
      ∧ (-1 : ℚ) ^ Nat.choose 9 2 = 1 ∧ (-1 : ℚ) ^ Nat.choose 12 2 = 1 :=
  ⟨eps_three, eps_six, eps_nine, eps_twelve⟩

/-- **The printed Conjecture 3 is FALSE.**  At `r = 9`, `n = 1` its first display demands
`H_9 = (-1)^1 · 2^8 = -256`, and `H9` proves `H_9^{(9)} = 256`.  Stated for any indexing `Hval`
of the Hankel determinants agreeing with `Amat.det` at `9`, so it does not depend on how the
family is encoded; and only the first of the display's two equalities is used, so the printed
display falls without `H_10`. -/
theorem not_printed_first (Hval : ℕ → ℚ) (h : Hval 9 = Amat.det) :
    ¬ PrintedFirst Hval 9 1 := by
  rintro ⟨h1, -⟩
  rw [show (9 : ℕ) * 1 = 9 from rfl, h, H9] at h1
  norm_num at h1

end PrintedConjecture

section Pinned

/-! ### The entries are pinned BY A THEOREM, not by the header

The module's header says *"Every integer below is computed, and re-checked inside Lean"*, and
lists `mot_rec`, `mpow2_conv` … `mpow9_conv` and `Amat_entries` as the chain that makes it so.
Those theorems were all true and all **consumed by nothing**: a reader had to compose them by
hand, and `H9` said only that one explicit matrix of rationals has determinant `256`.

This section writes the composition down.  `Amat_eq_hankel` proves that `Amat` IS the Hankel
matrix of the ninth convolution power of **any** sequence satisfying the write-up's defining
equation, and `H9_hankel` states the row's headline in those terms, with no explicit matrix in
sight.  Nothing new is computed; what changes is that the identification is now a typing fact
rather than a paragraph.

`mpowSeq m r` is the `r`-th convolution power, indexed honestly: `mpowSeq m 0` is the unit
sequence `[1,0,0,…]`, so `mpowSeq m 1 = m` (that is `mpowSeq_one`, via `convSeq_delta`) and
`mpowSeq m 9` is the ninth power the determinant is about.  The ladder from `mot` to `mpow9` is
eight applications of one step lemma, each spending exactly one of the `mpow*_conv` theorems.
-/

/-- The coefficientwise product of two sequences. -/
def convSeq (a b : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), a k * b (n - k)

/-- The convolution powers of `m`; `mpowSeq m 0` is the unit sequence. -/
def mpowSeq (m : ℕ → ℤ) : ℕ → (ℕ → ℤ)
  | 0 => fun n => if n = 0 then 1 else 0
  | (r + 1) => convSeq m (mpowSeq m r)

theorem convSeq_delta (m : ℕ → ℤ) (n : ℕ) :
    convSeq m (fun k => if k = 0 then 1 else 0) n = m n := by
  rw [convSeq]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hne
    have hk' := mem_range.mp hk
    have : n - k ≠ 0 := by omega
    simp [this]
  · intro hn
    exact absurd (mem_range.mpr (by omega)) hn

/-- The first power is the sequence itself. -/
theorem mpowSeq_one (m : ℕ → ℤ) : mpowSeq m 1 = m := by
  funext n
  exact convSeq_delta m n

/-- One rung of the ladder: if `a` agrees with the list `la` on the determinant's range and the
list `lc` is the convolution of `mot` with `la`, then `m * a` agrees with `lc`. -/
theorem conv_step {a : ℕ → ℤ} {la : List ℤ} (ha : ∀ n ≤ 16, a n = gt la n)
    {m : ℕ → ℤ} (hm : ∀ n ≤ 16, m n = gt mot n)
    {lc : List ℤ}
    (hc : ∀ n ∈ range 17, gt lc n = ∑ k ∈ range (n + 1), gt mot k * gt la (n - k)) :
    ∀ n ≤ 16, convSeq m a n = gt lc n := by
  intro n hn
  rw [convSeq, hc n (mem_range.mpr (by omega))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := mem_range.mp hk
  rw [hm k (by omega), ha (n - k) (by omega)]

/-- **The listed coefficients are forced.**  Any sequence satisfying the write-up's equation
agrees with `mot` on the whole range the determinant depends on. -/
theorem eq_mot_of_rec {m : ℕ → ℤ} (h0 : m 0 = 1) (h1 : m 1 = m 0)
    (hrec : ∀ n, m (n + 2) = m (n + 1) + ∑ k ∈ range (n + 1), m k * m (n - k)) :
    ∀ n ≤ 16, m n = gt mot n := by
  have key : ∀ n, ∀ k ≤ n, k ≤ 16 → m k = gt mot k := by
    intro n
    induction n with
    | zero =>
        intro k hk _
        have hk0 : k = 0 := by omega
        subst hk0
        rw [h0]
        exact mot_base.1.symm
    | succ t ih =>
        intro k hk hk16
        rcases Nat.lt_or_ge k (t + 1) with hlt | hge
        · exact ih k (by omega) hk16
        · have hkt : k = t + 1 := by omega
          subst hkt
          match t with
          | 0 =>
              rw [h1, h0]
              exact (mot_base.2.trans mot_base.1).symm
          | (j + 1) =>
              have hj : j ∈ range 15 := mem_range.mpr (by omega)
              rw [show j + 1 + 1 = j + 2 from rfl, hrec j, mot_rec j hj,
                ih (j + 1) le_rfl (by omega)]
              congr 1
              refine Finset.sum_congr rfl (fun k hk => ?_)
              have hk' := mem_range.mp hk
              rw [ih k (by omega) (by omega), ih (j - k) (by omega) (by omega)]
  intro n hn
  exact key n n le_rfl hn

/-- **The ninth convolution power agrees with `mpow9`** on the determinant's range, for any
sequence satisfying the write-up's equation.  Eight rungs, one per `mpow*_conv`. -/
theorem mpowSeq_nine {m : ℕ → ℤ} (h0 : m 0 = 1) (h1 : m 1 = m 0)
    (hrec : ∀ n, m (n + 2) = m (n + 1) + ∑ k ∈ range (n + 1), m k * m (n - k)) :
    ∀ n ≤ 16, mpowSeq m 9 n = gt mpow9 n := by
  have hm := eq_mot_of_rec h0 h1 hrec
  have e1 : ∀ n ≤ 16, mpowSeq m 1 n = gt mot n := by
    intro n hn
    rw [mpowSeq_one]
    exact hm n hn
  have e2 : ∀ n ≤ 16, mpowSeq m 2 n = gt mpow2 n := conv_step e1 hm mpow2_conv
  have e3 : ∀ n ≤ 16, mpowSeq m 3 n = gt mpow3 n := conv_step e2 hm mpow3_conv
  have e4 : ∀ n ≤ 16, mpowSeq m 4 n = gt mpow4 n := conv_step e3 hm mpow4_conv
  have e5 : ∀ n ≤ 16, mpowSeq m 5 n = gt mpow5 n := conv_step e4 hm mpow5_conv
  have e6 : ∀ n ≤ 16, mpowSeq m 6 n = gt mpow6 n := conv_step e5 hm mpow6_conv
  have e7 : ∀ n ≤ 16, mpowSeq m 7 n = gt mpow7 n := conv_step e6 hm mpow7_conv
  have e8 : ∀ n ≤ 16, mpowSeq m 8 n = gt mpow8 n := conv_step e7 hm mpow8_conv
  exact conv_step e8 hm mpow9_conv

/-- **`Amat` IS the Hankel matrix of the ninth convolution power.** -/
theorem Amat_eq_hankel {m : ℕ → ℤ} (h0 : m 0 = 1) (h1 : m 1 = m 0)
    (hrec : ∀ n, m (n + 2) = m (n + 1) + ∑ k ∈ range (n + 1), m k * m (n - k)) :
    ∀ i j : Fin 9, Amat i j = ((mpowSeq m 9 ((i : ℕ) + (j : ℕ)) : ℤ) : ℚ) := by
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Amat_entries i j, mpowSeq_nine h0 h1 hrec ((i : ℕ) + (j : ℕ)) (by omega)]

/-- **`H_9^{(9)} = 256`, with the matrix identified rather than transcribed**: for every sequence
satisfying the write-up's defining equation, the `9×9` Hankel matrix of its ninth convolution
power has determinant `256`. -/
theorem H9_hankel {m : ℕ → ℤ} (h0 : m 0 = 1) (h1 : m 1 = m 0)
    (hrec : ∀ n, m (n + 2) = m (n + 1) + ∑ k ∈ range (n + 1), m k * m (n - k)) :
    (Matrix.of fun i j : Fin 9 => ((mpowSeq m 9 ((i : ℕ) + (j : ℕ)) : ℤ) : ℚ)).det = 256 := by
  have h : (Matrix.of fun i j : Fin 9 => ((mpowSeq m 9 ((i : ℕ) + (j : ℕ)) : ℤ) : ℚ)) = Amat := by
    ext i j
    simp only [Matrix.of_apply]
    exact (Amat_eq_hankel h0 h1 hrec i j).symm
  rw [h, H9]

end Pinned

end Principia.MathDB.P367323
