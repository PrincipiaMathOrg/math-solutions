import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Fin
-- `Matrix.trace` and `conjTranspose` are NOT reachable from this module's other imports;
-- without these two, `Matrix.trace` reports as an UNKNOWN CONSTANT, which reads as a rename.
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MathDB #332493 — the four-projection trace inequality (scalar and summation core)

Write-up: `mathdb-open-problems/problems/332493/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Banica and Nechita, **Conjecture 6.6**.  For orthogonal projections `P,Q,R,S` on
`ℂ^K` with `PQ = 0`, `RS = 0`, `im P ∩ im R = 0`, `im Q ∩ im S = 0`, and with
`P' = (P+R)^{-1/2} P (P+R)^{-1/2}` (Moore–Penrose inverse square roots), and similarly for
`Q', R', S'`:

`Tr(P'Q') + Tr(R'S') ≤ Tr(PR) + Tr(QS)`.

The write-up proves it, and shows the conjecture's two rank identities are **unnecessary**.

## What this module proves

The proof's engine is two steps that need no matrices at all, and both are proved here.

* **`scalar_lemma`** — the write-up's Lemma 1.  For `|λ| < 1`, `|μ| < 1`,
  `a = 1/√((1+λ)(1+μ))`, `b = 1/√((1−λ)(1−μ))`:  `(a−b)² ≤ (λ²+μ²)(a²+b²)`.
* **`entrywise`** — the scaled form used at each matrix entry: since in the eigenbases
  `(D±)ᵢⱼ = cᵢⱼ/√((1±λᵢ)(1±μⱼ)) = cᵢⱼ·a` resp. `cᵢⱼ·b`, the lemma scales by
  `cc = |cᵢⱼ|²`.
* **`block_sum_bound`** — the write-up's Lemma 2 *summation*, over abstract finite index
  types, with the row and column contraction bounds as hypotheses.  `P`, `M`, `E` stand for
  `|(D₊)ᵢⱼ|²`, `|(D₋)ᵢⱼ|²`, `|(D₊−D₋)ᵢⱼ|²`.  **Nonnegativity of `P` and `M` turns out
  unnecessary** — the row/column bounds carry the whole argument.
* **`engine`** — the two composed: instantiating `block_sum_bound` at `P = cc·a²`,
  `M = cc·b²`, `E = cc·(a−b)²` discharges its entrywise hypothesis by `entrywise`, so the
  Frobenius bound `∑ᵢⱼ |(D₊−D₋)ᵢⱼ|²/4 ≤ ½(∑λᵢ² + ∑μⱼ²)` follows from `scalar_lemma`
  alone.  This is the entire non-matrix content of the write-up.

**The reduction is shorter than the write-up's.**  It presents Lemma 1 through the ratio
identity `(a−b)²/(a²+b²) = 1 − √(1−t+w²)/(1+w)`.  Clearing that is unnecessary: with
`t = λ²+μ²`, `w = λμ` and `Δ = (1−λ²)(1−μ²)`, the closed forms `a²+b² = 2(1+w)/Δ` and
`(ab)² = 1/Δ` turn the claim into `(1−t)(a²+b²) ≤ 2ab`, which is trivial when `t ≥ 1` and,
when `t < 1`, squares to the polynomial inequality `key_poly`:

`(1+w)²(1−t)² ≤ 1 − t + w²   ( = Δ )`.

The case split is **load-bearing, not a convenience**: at `λ = μ = 0.99` the squared form is
`3.615 ≤ 0.000396`, which is false.  Squaring is licensed only where `1 − t ≥ 0`.

## What is NOT here, and why the row is not counted

The matrix half is absent: Gram-matrix positivity, the Schur complement giving that `D±`
are contractions (which is what supplies `block_sum_bound`'s row/column hypotheses), the
identity `(FF*)^{-1/2}F = F(F*F)^{-1/2}`, and the identification of `Tr(P'Q') + Tr(R'S')`
with the Frobenius norm of the two retained diagonal blocks.  Those need Moore–Penrose
pseudo-inverses and the continuous functional calculus for matrices.  `engine` takes the
contraction bounds as hypotheses precisely because that is where the matrix argument
enters; discharging them is what the row still owes.  **The row is therefore PARTIAL and
deliberately not counted** — the conjecture itself is not stated in this file, because
stating it would require the objects the module cannot define.

Values checked in `Campaigns/MathDB-Formalization/verify_332493.py`.
-/

namespace Principia.MathDB.P332493

/-! ### The scalar estimate -/

/-- `a = 1/√((1+λ)(1+μ))`. -/
noncomputable def av (lam mu : ℝ) : ℝ := 1 / Real.sqrt ((1 + lam) * (1 + mu))

/-- `b = 1/√((1−λ)(1−μ))`. -/
noncomputable def bv (lam mu : ℝ) : ℝ := 1 / Real.sqrt ((1 - lam) * (1 - mu))

theorem pos_one_add {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) :
    0 < (1 + lam) * (1 + mu) := by
  rw [abs_lt] at hl hm
  have h1 : (0:ℝ) < 1 + lam := by linarith [hl.1]
  have h2 : (0:ℝ) < 1 + mu := by linarith [hm.1]
  positivity

theorem pos_one_sub {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) :
    0 < (1 - lam) * (1 - mu) := by
  rw [abs_lt] at hl hm
  have h1 : (0:ℝ) < 1 - lam := by linarith [hl.2]
  have h2 : (0:ℝ) < 1 - mu := by linarith [hm.2]
  positivity

theorem av_pos {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) : 0 < av lam mu := by
  rw [av]
  have := Real.sqrt_pos.2 (pos_one_add hl hm)
  positivity

theorem bv_pos {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) : 0 < bv lam mu := by
  rw [bv]
  have := Real.sqrt_pos.2 (pos_one_sub hl hm)
  positivity

theorem av_sq {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) :
    (av lam mu) ^ 2 = 1 / ((1 + lam) * (1 + mu)) := by
  rw [av, div_pow, one_pow, Real.sq_sqrt (pos_one_add hl hm).le]

theorem bv_sq {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) :
    (bv lam mu) ^ 2 = 1 / ((1 - lam) * (1 - mu)) := by
  rw [bv, div_pow, one_pow, Real.sq_sqrt (pos_one_sub hl hm).le]

theorem ab_sq {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) :
    (av lam mu * bv lam mu) ^ 2 = 1 / ((1 - lam ^ 2) * (1 - mu ^ 2)) := by
  rw [mul_pow, av_sq hl hm, bv_sq hl hm]
  have h1 : (1 + lam) * (1 + mu) ≠ 0 := ne_of_gt (pos_one_add hl hm)
  have h2 : (1 - lam) * (1 - mu) ≠ 0 := ne_of_gt (pos_one_sub hl hm)
  field_simp
  ring

/-- **The polynomial heart of Lemma 1**, valid exactly on `t < 1`.  Squaring the lemma is
licensed only there: at `λ = μ = 99/100` this inequality is FALSE. -/
theorem key_poly {lam mu : ℝ} (ht : lam ^ 2 + mu ^ 2 < 1) :
    (1 + lam * mu) ^ 2 * (1 - (lam ^ 2 + mu ^ 2)) ^ 2
      ≤ 1 - (lam ^ 2 + mu ^ 2) + (lam * mu) ^ 2 := by
  have hl : -1 < lam ∧ lam < 1 := by constructor <;> nlinarith [sq_nonneg mu]
  have hm : -1 < mu ∧ mu < 1 := by constructor <;> nlinarith [sq_nonneg lam]
  rcases le_or_gt 0 (lam * mu) with hw | hw
  · -- the write-up's factorisation: every term is nonnegative here
    nlinarith [sq_nonneg (lam - mu), sq_nonneg (lam * mu), mul_nonneg hw hw,
      sq_nonneg (lam + mu), sq_nonneg lam, sq_nonneg mu,
      mul_nonneg (mul_nonneg hw (add_nonneg (sq_nonneg lam) (sq_nonneg mu)))
        (by linarith : (0:ℝ) ≤ 1 - (lam ^ 2 + mu ^ 2)),
      mul_nonneg hw (sq_nonneg (lam - mu))]
  · -- `w < 0`: `(1+w)² ≤ 1`, then `(1−t)² ≤ 1−t ≤ 1−t+w²`
    have hw1 : (0 : ℝ) < 1 + lam * mu := by nlinarith [sq_nonneg (lam + mu)]
    have hw2 : 1 + lam * mu ≤ 1 := by linarith
    have h1t0 : (0:ℝ) ≤ 1 - (lam ^ 2 + mu ^ 2) := by linarith
    have h1t1 : 1 - (lam ^ 2 + mu ^ 2) ≤ 1 := by
      nlinarith [sq_nonneg lam, sq_nonneg mu]
    have hsq1 : (1 + lam * mu) ^ 2 ≤ 1 := by nlinarith [hw1, hw2]
    calc (1 + lam * mu) ^ 2 * (1 - (lam ^ 2 + mu ^ 2)) ^ 2
        ≤ 1 * (1 - (lam ^ 2 + mu ^ 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq1 (sq_nonneg _)
      _ = (1 - (lam ^ 2 + mu ^ 2)) ^ 2 := one_mul _
      _ ≤ 1 - (lam ^ 2 + mu ^ 2) := by nlinarith
      _ ≤ 1 - (lam ^ 2 + mu ^ 2) + (lam * mu) ^ 2 := by nlinarith [sq_nonneg (lam * mu)]

/-- **Lemma 1 of the write-up.** -/
theorem scalar_lemma {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) :
    (av lam mu - bv lam mu) ^ 2
      ≤ (lam ^ 2 + mu ^ 2) * ((av lam mu) ^ 2 + (bv lam mu) ^ 2) := by
  have hl' := abs_lt.1 hl
  have hm' := abs_lt.1 hm
  set a := av lam mu with ha
  set b := bv lam mu with hb
  have hap : 0 < a := av_pos hl hm
  have hbp : 0 < b := bv_pos hl hm
  have hD1 : (0:ℝ) < 1 - lam ^ 2 := by nlinarith [hl'.1, hl'.2]
  have hD2 : (0:ℝ) < 1 - mu ^ 2 := by nlinarith [hm'.1, hm'.2]
  have hD : (0:ℝ) < (1 - lam ^ 2) * (1 - mu ^ 2) := mul_pos hD1 hD2
  -- division-free closed forms: multiply through by Δ instead of clearing denominators
  have hXY : (1 - lam ^ 2) * (1 - mu ^ 2)
      = ((1 + lam) * (1 + mu)) * ((1 - lam) * (1 - mu)) := by ring
  -- proved over ABSTRACT `X, Y`, where `field_simp` sees the denominators literally;
  -- instantiating afterwards avoids `ring_nf` expanding the factorisations away
  have gen : ∀ X Y : ℝ, X ≠ 0 → Y ≠ 0 → (1 / X + 1 / Y) * (X * Y) = Y + X := by
    intro X Y hX hY; field_simp
  have hsum : (a ^ 2 + b ^ 2) * ((1 - lam ^ 2) * (1 - mu ^ 2)) = 2 * (1 + lam * mu) := by
    have hX : (1 + lam) * (1 + mu) ≠ 0 := ne_of_gt (pos_one_add hl hm)
    have hY : (1 - lam) * (1 - mu) ≠ 0 := ne_of_gt (pos_one_sub hl hm)
    rw [ha, hb, av_sq hl hm, bv_sq hl hm, hXY, gen _ _ hX hY]
    ring
  have hprod : (a * b) ^ 2 * ((1 - lam ^ 2) * (1 - mu ^ 2)) = 1 := by
    rw [ha, hb, ab_sq hl hm, one_div, inv_mul_cancel₀ (ne_of_gt hD)]
  -- it suffices to show `(1 − t)(a² + b²) ≤ 2ab`
  have hgoal : (1 - (lam ^ 2 + mu ^ 2)) * (a ^ 2 + b ^ 2) ≤ 2 * (a * b) →
      (a - b) ^ 2 ≤ (lam ^ 2 + mu ^ 2) * (a ^ 2 + b ^ 2) := by
    intro h; nlinarith [h]
  refine hgoal ?_
  rcases le_or_gt 1 (lam ^ 2 + mu ^ 2) with ht | ht
  · -- `t ≥ 1`: the left side is nonpositive
    have h1 : (1 - (lam ^ 2 + mu ^ 2)) ≤ 0 := by linarith
    have h2 : (0:ℝ) < a ^ 2 + b ^ 2 := by positivity
    nlinarith [mul_pos hap hbp]
  · -- `t < 1`: both sides are nonnegative, so compare squares after scaling by Δ²
    have hkey := key_poly ht
    have hab : 0 < a * b := mul_pos hap hbp
    have h1t : (0:ℝ) ≤ 1 - (lam ^ 2 + mu ^ 2) := by linarith
    have hlhs : 0 ≤ (1 - (lam ^ 2 + mu ^ 2)) * (a ^ 2 + b ^ 2) := by positivity
    have hscaled :
        ((1 - (lam ^ 2 + mu ^ 2)) * (a ^ 2 + b ^ 2)) ^ 2
            * (((1 - lam ^ 2) * (1 - mu ^ 2)) ^ 2)
          ≤ (2 * (a * b)) ^ 2 * (((1 - lam ^ 2) * (1 - mu ^ 2)) ^ 2) := by
      have e1 : ((1 - (lam ^ 2 + mu ^ 2)) * (a ^ 2 + b ^ 2)) ^ 2
            * (((1 - lam ^ 2) * (1 - mu ^ 2)) ^ 2)
          = (1 - (lam ^ 2 + mu ^ 2)) ^ 2
            * ((a ^ 2 + b ^ 2) * ((1 - lam ^ 2) * (1 - mu ^ 2))) ^ 2 := by ring
      have e2 : (2 * (a * b)) ^ 2 * (((1 - lam ^ 2) * (1 - mu ^ 2)) ^ 2)
          = 4 * ((a * b) ^ 2 * ((1 - lam ^ 2) * (1 - mu ^ 2)))
              * ((1 - lam ^ 2) * (1 - mu ^ 2)) := by ring
      rw [e1, e2, hsum, hprod]
      nlinarith [hkey, hD]
    have hDsq : (0:ℝ) < ((1 - lam ^ 2) * (1 - mu ^ 2)) ^ 2 := by positivity
    have hsq : ((1 - (lam ^ 2 + mu ^ 2)) * (a ^ 2 + b ^ 2)) ^ 2 ≤ (2 * (a * b)) ^ 2 :=
      le_of_mul_le_mul_right (by linarith [hscaled]) hDsq
    -- from `X² ≤ Y²` with `X ≥ 0` and `Y > 0`
    nlinarith [hsq, hlhs, hab]


/-! ### The entrywise form and the summation (the write-up's Lemma 2) -/

/-- The entrywise application: in the eigenbases `(D±)ᵢⱼ = cᵢⱼ·a` and `cᵢⱼ·b`, so the
scalar lemma scales by `|cᵢⱼ|²` (written `cc`). -/
theorem entrywise {lam mu : ℝ} (hl : |lam| < 1) (hm : |mu| < 1) {cc : ℝ} (hc : 0 ≤ cc) :
    cc * (av lam mu - bv lam mu) ^ 2
      ≤ (lam ^ 2 + mu ^ 2) * (cc * (av lam mu) ^ 2 + cc * (bv lam mu) ^ 2) := by
  have h := scalar_lemma hl hm
  nlinarith [h, hc]

/-- **The write-up's Lemma 2, summation step**, over abstract finite index types.
`P`, `M` and `E` stand for `|(D₊)ᵢⱼ|²`, `|(D₋)ᵢⱼ|²` and `|(D₊−D₋)ᵢⱼ|²`; the row and column
bounds are exactly what the Schur complement supplies, namely that `D±` are contractions.
Nonnegativity of `P` and `M` is NOT needed: the row/column bounds carry the argument. -/
theorem block_sum_bound {I J : Type*} [Fintype I] [Fintype J]
    (lam : I → ℝ) (mu : J → ℝ) (P M E : I → J → ℝ)
    (hent : ∀ i j, E i j ≤ ((lam i) ^ 2 + (mu j) ^ 2) * (P i j + M i j))
    (hProw : ∀ i, ∑ j, P i j ≤ 1) (hPcol : ∀ j, ∑ i, P i j ≤ 1)
    (hMrow : ∀ i, ∑ j, M i j ≤ 1) (hMcol : ∀ j, ∑ i, M i j ≤ 1) :
    (∑ i, ∑ j, E i j) / 4 ≤ (1 / 2) * ((∑ i, (lam i) ^ 2) + ∑ j, (mu j) ^ 2) := by
  -- bound the double sum termwise, then split the two halves
  have step1 : (∑ i, ∑ j, E i j)
      ≤ ∑ i, ∑ j, ((lam i) ^ 2 + (mu j) ^ 2) * (P i j + M i j) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hent i j))
  have split : (∑ i, ∑ j, ((lam i) ^ 2 + (mu j) ^ 2) * (P i j + M i j))
      = (∑ i, ∑ j, (lam i) ^ 2 * (P i j + M i j))
        + ∑ i, ∑ j, (mu j) ^ 2 * (P i j + M i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- the `λ` half, using the ROW bounds
  have halfL : (∑ i, ∑ j, (lam i) ^ 2 * (P i j + M i j)) ≤ 2 * ∑ i, (lam i) ^ 2 := by
    have : ∀ i ∈ (Finset.univ : Finset I),
        (∑ j, (lam i) ^ 2 * (P i j + M i j)) ≤ (lam i) ^ 2 * 2 := by
      intro i _
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have : (∑ j, (P i j + M i j)) = (∑ j, P i j) + ∑ j, M i j :=
        Finset.sum_add_distrib
      rw [this]
      linarith [hProw i, hMrow i]
    calc (∑ i, ∑ j, (lam i) ^ 2 * (P i j + M i j))
        ≤ ∑ i, (lam i) ^ 2 * 2 := Finset.sum_le_sum this
      _ = 2 * ∑ i, (lam i) ^ 2 := by rw [← Finset.sum_mul]; ring
  -- the `μ` half, using the COLUMN bounds (after swapping the order of summation)
  have halfM : (∑ i, ∑ j, (mu j) ^ 2 * (P i j + M i j)) ≤ 2 * ∑ j, (mu j) ^ 2 := by
    rw [Finset.sum_comm]
    have : ∀ j ∈ (Finset.univ : Finset J),
        (∑ i, (mu j) ^ 2 * (P i j + M i j)) ≤ (mu j) ^ 2 * 2 := by
      intro j _
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have : (∑ i, (P i j + M i j)) = (∑ i, P i j) + ∑ i, M i j :=
        Finset.sum_add_distrib
      rw [this]
      linarith [hPcol j, hMcol j]
    calc (∑ j, ∑ i, (mu j) ^ 2 * (P i j + M i j))
        ≤ ∑ j, (mu j) ^ 2 * 2 := Finset.sum_le_sum this
      _ = 2 * ∑ j, (mu j) ^ 2 := by rw [← Finset.sum_mul]; ring
  rw [split] at step1
  linarith [step1, halfL, halfM]

/-- **The two engine steps composed.**  With `(D±)ᵢⱼ = cᵢⱼ·a(λᵢ,μⱼ)` and `cᵢⱼ·b(λᵢ,μⱼ)`
as in the matrix proof — `cc i j` being `|cᵢⱼ|²` — the Frobenius bound of Lemma 2 follows
from `scalar_lemma` alone.  This is the whole non-matrix content of the write-up. -/
theorem engine {I J : Type*} [Fintype I] [Fintype J]
    (lam : I → ℝ) (mu : J → ℝ) (hl : ∀ i, |lam i| < 1) (hm : ∀ j, |mu j| < 1)
    (cc : I → J → ℝ) (hcc : ∀ i j, 0 ≤ cc i j)
    (hProw : ∀ i, (∑ j, cc i j * (av (lam i) (mu j)) ^ 2) ≤ 1)
    (hPcol : ∀ j, (∑ i, cc i j * (av (lam i) (mu j)) ^ 2) ≤ 1)
    (hMrow : ∀ i, (∑ j, cc i j * (bv (lam i) (mu j)) ^ 2) ≤ 1)
    (hMcol : ∀ j, (∑ i, cc i j * (bv (lam i) (mu j)) ^ 2) ≤ 1) :
    (∑ i, ∑ j, cc i j * (av (lam i) (mu j) - bv (lam i) (mu j)) ^ 2) / 4
      ≤ (1 / 2) * ((∑ i, (lam i) ^ 2) + ∑ j, (mu j) ^ 2) :=
  block_sum_bound lam mu
    (fun i j => cc i j * (av (lam i) (mu j)) ^ 2)
    (fun i j => cc i j * (bv (lam i) (mu j)) ^ 2)
    (fun i j => cc i j * (av (lam i) (mu j) - bv (lam i) (mu j)) ^ 2)
    (fun i j => entrywise (hl i) (hm j) (hcc i j))
    hProw hPcol hMrow hMcol

/-! ## The conjecture, now STATED

The header above says the conjecture *"is not stated in this file, because stating it would
require the objects the module cannot define"*.  That is true of **constructing** `P'`, and it
is not true of **stating** the conjecture.  The project's spine rule is exactly this case: name
every unconstructible object as a parameter and write the obligation down, so that what the row
owes becomes a typed statement instead of a sentence in a comment.

Re-measured 2026-09-30: Mathlib still has **no Moore–Penrose pseudo-inverse and no matrix square
root** (`NonsingularInverse.lean` mentions Moore–Penrose only in prose; there is no `sqrt` in
`Matrix/PosDef.lean`), so `T^{-1/2} · P · T^{-1/2}` cannot be built.  It enters as a parameter
`cj : Matrix K K ℂ → Matrix K K ℂ → Matrix K K ℂ`, read as `cj T P = T^{-1/2} P T^{-1/2}`.

**Two hypotheses of the printed conjecture are deliberately OMITTED**, and that makes the
statement STRONGER, not weaker: the header records that the write-up *"shows the conjecture's two
rank identities are unnecessary"* — `im P ∩ im R = 0` and `im Q ∩ im S = 0`.  `Conjecture66`
therefore quantifies over all four projections with only the two orthogonality relations.

**What is proved about it here is only that it has CONTENT.**  `not_conjecture66_const`
exhibits a `cj` for which it fails, so the statement genuinely constrains the conjugation and
is not vacuously true of any parameter.  **Satisfiability is the write-up's theorem and is not
proved here** — that is the matrix half, and it remains exactly what the row owes. -/

open Matrix in
/-- An orthogonal projection: Hermitian and idempotent. -/
def IsOrthProj {K : Type*} [Fintype K] [DecidableEq K] (P : Matrix K K ℂ) : Prop :=
  Pᴴ = P ∧ P * P = P

open Matrix in
/-- **Banica–Nechita Conjecture 6.6**, relative to the square-root conjugation `cj`.

`cj T P` stands for `T^{-1/2} P T^{-1/2}`; with `P' = cj (P+R) P`, `R' = cj (P+R) R`,
`Q' = cj (Q+S) Q` and `S' = cj (Q+S) S`, the claim is `Tr(P'Q') + Tr(R'S') ≤ Tr(PR) + Tr(QS)`.
The two rank identities of the printed conjecture are omitted, per the write-up's own finding
that they are unnecessary. -/
def Conjecture66 {K : Type*} [Fintype K] [DecidableEq K]
    (cj : Matrix K K ℂ → Matrix K K ℂ → Matrix K K ℂ) : Prop :=
  ∀ P Q R S : Matrix K K ℂ, IsOrthProj P → IsOrthProj Q → IsOrthProj R → IsOrthProj S →
    P * Q = 0 → R * S = 0 →
      (Matrix.trace (cj (P + R) P * cj (Q + S) Q)).re
          + (Matrix.trace (cj (P + R) R * cj (Q + S) S)).re
        ≤ (Matrix.trace (P * R)).re + (Matrix.trace (Q * S)).re

open Matrix in
/-- **The statement has content: it fails for the constant conjugation `cj ≡ 1`.**  So
`Conjecture66` genuinely constrains `cj` and is not satisfied by every parameter — the
anti-vacuity check every spine in this campaign carries.  Witness: `K = Fin 1`, `P = S = 1`,
`Q = R = 0`, where the right-hand side is `0` and the left-hand side is `2`. -/
theorem not_conjecture66_const : ¬ Conjecture66 (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  intro h
  have hP : IsOrthProj (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
    ⟨Matrix.conjTranspose_one, one_mul 1⟩
  have hZ : IsOrthProj (0 : Matrix (Fin 1) (Fin 1) ℂ) :=
    ⟨Matrix.conjTranspose_zero, mul_zero 0⟩
  have hkey := h 1 0 0 1 hP hZ hZ hP (mul_zero 1) (zero_mul 1)
  simp only [add_zero, zero_add, mul_one, one_mul, mul_zero, zero_mul,
    Matrix.trace_zero, Matrix.trace_one] at hkey
  norm_num at hkey

end Principia.MathDB.P332493
