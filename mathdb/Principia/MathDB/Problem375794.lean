import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-!
# MathDB 375794 — uniform initial partial quotients of a zeta-tail root

Write-up: `mathdb-open-problems/problems/375794/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.

With `R N = ∑_{j > N} j⁻³` and `g N = √(R N / 2)`, the write-up proves that the regular
continued fraction `g N = [0; a₁, a₂, a₃, …]` has

    a₁(N) = 2N+1  (N ≥ 1),   a₂(N) = 4N+2  (N ≥ 1),
    a₃(N) = ⌊(12N+6)/19⌋     (N ≥ 2),

covering every Pell index in Feldman's Conjecture 4.1.  At `N = 1` the third quotient is
`1` while the floor formula gives `0`, so the `N ≥ 2` guard is necessary.

## Status: VERIFIED — all three partial quotients

`a₁` (`floor_one_div_sqrt`), `a₂` (`floor_a2`) and `a₃` (`floor_a3_cf`) are proved with
EXACTLY the write-up's guards — `N ≥ 1`, `N ≥ 1`, `N ≥ 2` — and `a₁` in fact holds for
every `N ≥ 0`.  The three are successive steps of one floor-and-invert process: with
`u = 1/g N`, `a₁ = ⌊u⌋`, `δ = u - a₁`, `a₂ = ⌊1/δ⌋`, `a₃ = ⌊1/(1/δ - a₂)⌋`.

Everything rests on ONE shape.  Writing the tail in the odd variable `q = 2N+1`, where
`R N = ∑_{r≥0} 8/(q+1+2r)³`, a rational `f` with `f(q) - f(q+2) ≷ 8/(q+1)³` termwise
telescopes to `f(q) ≷ R N`.  Three comparison pairs of increasing sharpness are used:

| quotient | pair | why sharper is needed |
|---|---|---|
| `a₁` | `Uc = 2/(2j-1)²`, `Lc = 1/(2j²)` | pins `u` to within `1` |
| `a₂` | `U₆ = 2/q² - 2/q⁴ + 14/(3q⁶)`, `L₈ = U₆ - 62/(3q⁸)` | pins `δ` between `1/(2q+1)` and `1/(2q)` |
| `a₃` | `U₁₀ = L₈ + 762/(5q¹⁰)`, `L₁₂ = U₁₀ - 5110/(3q¹²)` | pins `X₃` to width `1/q` |

Three facts about that shape organise the file.

* **The upper half never needs a limit.**  `Real.tsum_le_of_sum_range_le` reduces `R N ≤ f`
  to a uniform bound on partial sums and `Finset.sum_range_sub'` evaluates the finite
  telescope exactly.  The lower half genuinely needs the limit (`squeeze_zero` /
  `squeeze_zero_norm`, then `le_of_tendsto`), which is the only analysis in the file.
* **A limit cannot deliver strictness.**  `a₁` needs `2/(2N+2)² < R N` STRICTLY, and the
  obvious integral comparison `∫_{N+1}^∞ x⁻³ dx` lands EXACTLY on `2/(2N+2)²`.  `Rt_gt`
  recovers strictness by PEELING the `j = N+1` term with `Summable.tsum_eq_zero_add`,
  where the per-term inequality is strict.  `a₂` and `a₃` need no peel, because there the
  rational comparisons are themselves strict.
* **Every rational inequality is an exact coefficient certificate.**  Each difference is
  ONE fraction whose numerator, re-expanded around the LEFT ENDPOINT of its range
  (`s = q-1`, `q-3`, `q-5`), has all-positive coefficients — degrees 5 to 12.  So each is
  `linarith` over `pow_nonneg hs 2 … hs 12`: no `nlinarith` search, no numerics.  The
  coefficients were generated and the identities re-verified symbolically before any Lean
  was written.

Two exceptional cases are real, and both are the write-up's too.
`U₆(q) < 2/(q+1/(2q+1))²` FAILS at `q = 3` (by `-769/529254`), so `N = 1` is proved
separately: `Rt_one_lt` peels four terms and closes with the crude `Rt_le` at `N = 5`,
giving `R 1 ≤ 1/2³+1/3³+1/4³+1/5³+2/121 = 5284463/26136000 < 49/242` — and `U₆(3)`,
`U₁₀(3)` are both too large to do this.  For `a₃`, the uniform estimate
`6q/19 < X₃ < 6q/19 + 1/q` does not by itself keep `X₃` below the next integer: the
fractional part of `6q/19` is a multiple of `1/19`, so the argument closes once
`1/q ≤ 1/19`, i.e. `q ≥ 21`; `frac_gap` handles `N = 2…9` by `interval_cases`.

The `v∓` in the `a₃` comparisons are not arbitrary.  `X₃ = δ/(1-2qδ)` is strictly
increasing in `δ` (`X3_mono`, a two-line cross-multiplication), and `v∓` are chosen so
that its endpoint values are EXACTLY `6q/19` and `6q/19 + 1/q`.

## A note on the source

The write-up **disclaims campaign credit** — Hu's 2026 dissertation claims the general
eventual-quasi-polynomial mechanism, and could not be obtained to check whether it also
contains these specific uniform formulas.  The row records that.  Formalizing was chosen
anyway: verification is orthogonal to novelty credit, and the mathematics is
self-contained.

Python check: `Campaigns/MathDB-Formalization/verify_375794.py` — mpmath at 80 digits
confirms all three formulas for `N = 1…44` and the `N = 1` exception, and sympy confirms
the two per-term surpluses and their telescoped totals.
-/

namespace Principia.MathDB.P375794

open Finset

/-- The zeta-3 tail `R N = ∑_{j > N} j⁻³`, reindexed so the summand carries no
ℕ-subtraction. -/
noncomputable def Rt (N : ℕ) : ℝ := ∑' k : ℕ, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3

/-- The midpoint comparison `U j = 2/(2j-1)²`; it is the antiderivative that makes the
convexity bound telescope. -/
noncomputable def Uc (j : ℕ) : ℝ := 2 / (2 * (j : ℝ) - 1) ^ 2

lemma Uc_nonneg (j : ℕ) : 0 ≤ Uc j := by
  rw [Uc]; positivity

/-- **The per-term upper inequality.**  The surplus is exactly
`(8j²-1)/(j³(2j-1)²(2j+1)²)`, nonnegative for `j ≥ 1`. -/
lemma term_le_Uc_sub (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (j : ℝ) ^ 3 ≤ Uc j - Uc (j + 1) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) := by linarith
  have h1 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by linarith
  have h1' : (2 * (j : ℝ) - 1) ≠ 0 := ne_of_gt h1
  have h2' : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  have h3' : (j : ℝ) ≠ 0 := ne_of_gt hjp
  have key : Uc j - Uc (j + 1) - 1 / (j : ℝ) ^ 3
      = (8 * (j : ℝ) ^ 2 - 1)
        / ((j : ℝ) ^ 3 * (2 * (j : ℝ) - 1) ^ 2 * (2 * (j : ℝ) + 1) ^ 2) := by
    have hcast : (2 : ℝ) * (((j + 1 : ℕ) : ℝ)) - 1 = 2 * (j : ℝ) + 1 := by
      push_cast; ring
    rw [Uc, Uc, hcast]
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ (8 * (j : ℝ) ^ 2 - 1)
      / ((j : ℝ) ^ 3 * (2 * (j : ℝ) - 1) ^ 2 * (2 * (j : ℝ) + 1) ^ 2) :=
    div_nonneg (by nlinarith) (by positivity)
  linarith

/-- **The upper tail bound**, `R N ≤ 2/(2N+1)²`.  Only a finite telescope is needed:
`Real.tsum_le_of_sum_range_le` turns the claim into a uniform bound on partial sums, and
`Finset.sum_range_sub'` evaluates those exactly. -/
theorem Rt_le (N : ℕ) : Rt N ≤ 2 / (2 * (N : ℝ) + 1) ^ 2 := by
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun n => ?_)
  have hstep : ∀ k ∈ Finset.range n,
      (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3
        ≤ Uc (N + 1 + k) - Uc (N + 1 + k + 1) :=
    fun k _ => term_le_Uc_sub (N + 1 + k) (by omega)
  calc ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3
      ≤ ∑ k ∈ Finset.range n, (Uc (N + 1 + k) - Uc (N + 1 + k + 1)) :=
        Finset.sum_le_sum hstep
    _ = Uc (N + 1 + 0) - Uc (N + 1 + n) :=
        Finset.sum_range_sub' (fun k => Uc (N + 1 + k)) n
    _ ≤ Uc (N + 1 + 0) := by linarith [Uc_nonneg (N + 1 + n)]
    _ = 2 / (2 * (N : ℝ) + 1) ^ 2 := by
        rw [Uc]; push_cast; ring_nf

/-! ### The lower bound

This side needs the telescope's LIMIT, and it must be strict.  The strictness comes from
peeling the `j = N+1` term, where the per-term inequality is strict, and bounding the
remaining tail by the non-strict telescope. -/

lemma summable_cube_shift (N : ℕ) :
    Summable (fun k : ℕ => (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have := (summable_nat_add_iff (N + 1)).mpr h
  simpa [add_comm, add_left_comm, add_assoc] using this

/-- The lower comparison `L j = 1/(2j²)`. -/
noncomputable def Lc (j : ℕ) : ℝ := 1 / (2 * (j : ℝ) ^ 2)

/-- **The per-term lower inequality, STRICT.**  The surplus is exactly
`(3j+2)/(2j³(j+1)²) > 0`. -/
lemma Lc_sub_lt_term (j : ℕ) (hj : 1 ≤ j) :
    Lc j - Lc (j + 1) < (1 : ℝ) / (j : ℝ) ^ 3 := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) := by linarith
  have key : 1 / (j : ℝ) ^ 3 - (Lc j - Lc (j + 1))
      = (3 * (j : ℝ) + 2) / (2 * (j : ℝ) ^ 3 * ((j : ℝ) + 1) ^ 2) := by
    rw [Lc, Lc]
    push_cast
    field_simp
    ring
  have hpos : (0 : ℝ) < (3 * (j : ℝ) + 2) / (2 * (j : ℝ) ^ 3 * ((j : ℝ) + 1) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

lemma Lc_tendsto (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => Lc (N + 1 + n)) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  · simp only [Lc]; positivity
  · simp only [Lc]
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hc : ((N + 1 + n : ℕ) : ℝ) = (N : ℝ) + 1 + (n : ℝ) := by push_cast; ring
    rw [hc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hN, hn]

/-- The non-strict lower bound, from the telescope's limit. -/
lemma Lc_le_Rt (N : ℕ) : Lc (N + 1) ≤ Rt N := by
  have hsum := summable_cube_shift N
  have hcomb : ∀ n : ℕ, Lc (N + 1) - Lc (N + 1 + n) ≤ Rt N := by
    intro n
    have hpart : Lc (N + 1 + 0) - Lc (N + 1 + n)
        ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3 := by
      rw [← Finset.sum_range_sub' (fun k => Lc (N + 1 + k)) n]
      refine Finset.sum_le_sum (fun k _ => ?_)
      exact le_of_lt (Lc_sub_lt_term (N + 1 + k) (by omega))
    have hts : ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3 ≤ Rt N :=
      hsum.sum_le_tsum _ (fun k _ => by positivity)
    simpa using le_trans hpart hts
  have htend : Filter.Tendsto (fun n : ℕ => Lc (N + 1) - Lc (N + 1 + n)) Filter.atTop
      (nhds (Lc (N + 1) - 0)) := Filter.Tendsto.const_sub _ (Lc_tendsto N)
  simpa using le_of_tendsto htend (Filter.Eventually.of_forall hcomb)

/-- Peeling the first term. -/
lemma Rt_succ (N : ℕ) : Rt N = (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 3 + Rt (N + 1) := by
  rw [Rt, Rt, (summable_cube_shift N).tsum_eq_zero_add]
  norm_num
  exact tsum_congr (fun k => by ring_nf)

/-- **The strict lower bound**, `2/(2N+2)² < R N`. -/
theorem Rt_gt (N : ℕ) : Lc (N + 1) < Rt N := by
  have hpeel := Rt_succ N
  have hstrict := Lc_sub_lt_term (N + 1) (by omega)
  have htail := Lc_le_Rt (N + 1)
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have : Lc (N + 1) - Lc (N + 1 + 1) < (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 3 := by
    simpa using hstrict
  linarith [hpeel, this, htail]

/-! ### The first partial quotient -/

/-- **`a₁(N) = 2N+1`.**  The first regular-continued-fraction quotient of
`g N = √(R N / 2)` is `⌊1/g N⌋`, and the two tail bounds pin it exactly.  Note this
holds for every `N ≥ 0`, one better than the write-up's `N ≥ 1`. -/
theorem floor_one_div_sqrt (N : ℕ) :
    ⌊1 / Real.sqrt (Rt N / 2)⌋ = 2 * (N : ℤ) + 1 := by
  have hNc : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hhi := Rt_le N
  have hlo := Rt_gt N
  have hLc : Lc (N + 1) = 1 / (2 * ((N : ℝ) + 1) ^ 2) := by
    rw [Lc]; push_cast; ring_nf
  rw [hLc] at hlo
  have hp1 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by linarith
  have hp2 : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by linarith
  -- square bounds for `R N / 2`
  have hb1 : (1 / (2 * ((N : ℝ) + 1))) ^ 2 < Rt N / 2 := by
    have he : (1 / (2 * ((N : ℝ) + 1))) ^ 2 = 1 / (2 * ((N : ℝ) + 1) ^ 2) / 2 := by
      field_simp
    rw [he]; linarith
  have hb2 : Rt N / 2 ≤ (1 / (2 * (N : ℝ) + 1)) ^ 2 := by
    have he : (1 / (2 * (N : ℝ) + 1)) ^ 2 = 2 / (2 * (N : ℝ) + 1) ^ 2 / 2 := by
      field_simp
    rw [he]; linarith
  -- pass to square roots
  have hs1 : 1 / (2 * ((N : ℝ) + 1)) < Real.sqrt (Rt N / 2) :=
    (Real.lt_sqrt (by positivity)).mpr hb1
  have hs2 : Real.sqrt (Rt N / 2) ≤ 1 / (2 * (N : ℝ) + 1) := by
    have := Real.sqrt_le_sqrt hb2
    rwa [Real.sqrt_sq (by positivity)] at this
  have hspos : 0 < Real.sqrt (Rt N / 2) := lt_trans (by positivity) hs1
  -- invert
  have hq1 : ((2 * (N : ℤ) + 1 : ℤ) : ℝ) ≤ 1 / Real.sqrt (Rt N / 2) := by
    push_cast
    rw [le_div_iff₀ hspos]
    calc (2 * (N : ℝ) + 1) * Real.sqrt (Rt N / 2)
        ≤ (2 * (N : ℝ) + 1) * (1 / (2 * (N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hs2 hp1.le
      _ = 1 := by field_simp
  have hq2 : 1 / Real.sqrt (Rt N / 2) < ((2 * (N : ℤ) + 1 : ℤ) : ℝ) + 1 := by
    push_cast
    rw [div_lt_iff₀ hspos]
    calc (1 : ℝ) = (2 * ((N : ℝ) + 1)) * (1 / (2 * ((N : ℝ) + 1))) := by field_simp
      _ < (2 * ((N : ℝ) + 1)) * Real.sqrt (Rt N / 2) := by
          exact mul_lt_mul_of_pos_left hs1 hp2
      _ = (2 * (N : ℝ) + 1 + 1) * Real.sqrt (Rt N / 2) := by ring_nf
  exact Int.floor_eq_iff.mpr ⟨hq1, hq2⟩


/-! ### The second partial quotient

`a₂` needs a sharper comparison pair.  Writing the tail in the odd variable `q = 2N+1`,
where `R N = ∑_{r ≥ 0} 8/(q+1+2r)³`, the write-up's functions are

    U₆(q) = 2/q² - 2/q⁴ + 14/(3q⁶),     L₈(q) = U₆(q) - 62/(3q⁸),

and all four inequalities needed below are certified the same way: the difference is a
single fraction whose numerator, **re-expanded around the left endpoint of its range**,
has every coefficient positive.  That turns each one into `linarith` over the powers of
the shifted variable — no `nlinarith` search, no numeric approximation. -/

noncomputable def U6 (q : ℝ) : ℝ := 2 / q ^ 2 - 2 / q ^ 4 + 14 / (3 * q ^ 6)

noncomputable def L8 (q : ℝ) : ℝ := U6 q - 62 / (3 * q ^ 8)

lemma U6_nonneg (q : ℝ) (hq : 1 ≤ q) : 0 ≤ U6 q := by
  have h0 : (0 : ℝ) < q := by linarith
  have hne : q ≠ 0 := ne_of_gt h0
  have he : U6 q = (6 * q ^ 4 - 6 * q ^ 2 + 14) / (3 * q ^ 6) := by
    rw [U6]; field_simp; ring
  rw [he]
  refine div_nonneg ?_ (le_of_lt (mul_pos (by norm_num) (pow_pos h0 6)))
  nlinarith [sq_nonneg (q ^ 2 - 1), sq_nonneg q]

/-- **`D_{U₆}(q) > 0`.**  The certificate is the shifted numerator below; every
coefficient is positive, so the whole defect is nonnegative for `q ≥ 1`. -/
lemma U6_defect (q : ℝ) (hq : 1 ≤ q) : 8 / (q + 1) ^ 3 ≤ U6 q - U6 (q + 2) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 1 + s := ⟨q - 1, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 1 + s := by linarith
  have h1 : (0 : ℝ) < 1 + s + 1 := by linarith
  have h2 : (0 : ℝ) < 1 + s + 2 := by linarith
  have hne0 : (1 : ℝ) + s ≠ 0 := ne_of_gt h0
  have hne1 : (1 : ℝ) + s + 1 ≠ 0 := ne_of_gt h1
  have hne2 : (1 : ℝ) + s + 2 ≠ 0 := ne_of_gt h2
  have key : U6 (1 + s) - U6 (1 + s + 2) - 8 / ((1 + s) + 1) ^ 3
      = (992 * s ^ 6 + 11904 * s ^ 5 + 59304 * s ^ 4 + 156992 * s ^ 3
          + 233040 * s ^ 2 + 184128 * s + 60584)
        / (3 * (1 + s) ^ 6 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 6) := by
    rw [U6, U6]; field_simp; ring
  have hnum : (0 : ℝ) ≤ 992 * s ^ 6 + 11904 * s ^ 5 + 59304 * s ^ 4 + 156992 * s ^ 3
      + 233040 * s ^ 2 + 184128 * s + 60584 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6
    linarith
  have hden : (0 : ℝ) < 3 * (1 + s) ^ 6 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 6 :=
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h0 6)) (pow_pos h1 3)) (pow_pos h2 6)
  linarith [key, div_nonneg hnum hden.le]

/-- **`D_{L₈}(q) < 0`.**  Same certificate shape, with the inequality reversed. -/
lemma L8_defect (q : ℝ) (hq : 1 ≤ q) : L8 q - L8 (q + 2) ≤ 8 / (q + 1) ^ 3 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 1 + s := ⟨q - 1, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 1 + s := by linarith
  have h1 : (0 : ℝ) < 1 + s + 1 := by linarith
  have h2 : (0 : ℝ) < 1 + s + 2 := by linarith
  have hne0 : (1 : ℝ) + s ≠ 0 := ne_of_gt h0
  have hne1 : (1 : ℝ) + s + 1 ≠ 0 := ne_of_gt h1
  have hne2 : (1 : ℝ) + s + 2 ≠ 0 := ne_of_gt h2
  have key : 8 / ((1 + s) + 1) ^ 3 - (L8 (1 + s) - L8 (1 + s + 2))
      = (9144 * s ^ 8 + 146304 * s ^ 7 + 1029504 * s ^ 6 + 4161024 * s ^ 5
          + 10565360 * s ^ 4 + 17258368 * s ^ 3 + 17712576 * s ^ 2
          + 10443520 * s + 2708504)
        / (3 * (1 + s) ^ 8 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 8) := by
    rw [L8, L8, U6, U6]; field_simp; ring
  have hnum : (0 : ℝ) ≤ 9144 * s ^ 8 + 146304 * s ^ 7 + 1029504 * s ^ 6 + 4161024 * s ^ 5
      + 10565360 * s ^ 4 + 17258368 * s ^ 3 + 17712576 * s ^ 2 + 10443520 * s + 2708504 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6; have p7 := pow_nonneg hs 7
    have p8 := pow_nonneg hs 8
    linarith
  have hden : (0 : ℝ) < 3 * (1 + s) ^ 8 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 8 :=
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h0 8)) (pow_pos h1 3)) (pow_pos h2 8)
  linarith [key, div_nonneg hnum hden.le]

/-! The two comparison functions in the `ℕ` index `j`, with `q = 2j-1`.  Then `j = N+1+k`
runs the telescope and `q + 1 = 2j`, so the defect's `8/(q+1)³` is exactly `1/j³`. -/

noncomputable def Uh (j : ℕ) : ℝ := U6 (2 * (j : ℝ) - 1)

noncomputable def Lh (j : ℕ) : ℝ := L8 (2 * (j : ℝ) - 1)

lemma term_le_Uh_sub (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (j : ℝ) ^ 3 ≤ Uh j - Uh (j + 1) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) := by linarith
  have hx : (1 : ℝ) ≤ 2 * (j : ℝ) - 1 := by linarith
  have hb : (8 : ℝ) / ((2 * (j : ℝ) - 1) + 1) ^ 3 = 1 / (j : ℝ) ^ 3 := by
    rw [show (2 * (j : ℝ) - 1) + 1 = 2 * (j : ℝ) by ring, mul_pow]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hU : Uh (j + 1) = U6 ((2 * (j : ℝ) - 1) + 2) := by
    rw [Uh]; congr 1; push_cast; ring
  rw [Uh, hU, ← hb]
  exact U6_defect _ hx

lemma Lh_sub_le_term (j : ℕ) (hj : 1 ≤ j) :
    Lh j - Lh (j + 1) ≤ (1 : ℝ) / (j : ℝ) ^ 3 := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) := by linarith
  have hx : (1 : ℝ) ≤ 2 * (j : ℝ) - 1 := by linarith
  have hb : (8 : ℝ) / ((2 * (j : ℝ) - 1) + 1) ^ 3 = 1 / (j : ℝ) ^ 3 := by
    rw [show (2 * (j : ℝ) - 1) + 1 = 2 * (j : ℝ) by ring, mul_pow]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hL : Lh (j + 1) = L8 ((2 * (j : ℝ) - 1) + 2) := by
    rw [Lh]; congr 1; push_cast; ring
  rw [Lh, hL, ← hb]
  exact L8_defect _ hx

lemma Uh_eq (N : ℕ) : Uh (N + 1) = U6 (2 * (N : ℝ) + 1) := by
  rw [Uh]; congr 1; push_cast; ring

lemma Lh_eq (N : ℕ) : Lh (N + 1) = L8 (2 * (N : ℝ) + 1) := by
  rw [Lh]; congr 1; push_cast; ring

lemma Uh_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Uh j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  exact U6_nonneg _ (by linarith)

/-- **`R N ≤ U₆(2N+1)`.**  A finite telescope again — no limit on this side. -/
theorem Rt_le_Uh (N : ℕ) : Rt N ≤ Uh (N + 1) := by
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun n => ?_)
  calc ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3
      ≤ ∑ k ∈ Finset.range n, (Uh (N + 1 + k) - Uh (N + 1 + k + 1)) :=
        Finset.sum_le_sum (fun k _ => term_le_Uh_sub (N + 1 + k) (by omega))
    _ = Uh (N + 1 + 0) - Uh (N + 1 + n) :=
        Finset.sum_range_sub' (fun k => Uh (N + 1 + k)) n
    _ ≤ Uh (N + 1 + 0) := by linarith [Uh_nonneg (N + 1 + n) (by omega)]
    _ = Uh (N + 1) := by norm_num

/-- `L₈` along the telescope tends to zero; `|L₈ q| ≤ 32/q²` for `q ≥ 1`. -/
lemma Lh_tendsto (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => Lh (N + 1 + n)) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => 32 * (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (32 : ℝ)
  refine squeeze_zero_norm (fun n => ?_) hg
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcast : (2 : ℝ) * ((N + 1 + n : ℕ) : ℝ) - 1 = 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by
    push_cast; ring
  have h1 : (1 : ℝ) ≤ 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by linarith
  have h2 : (n : ℝ) + 1 ≤ 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by linarith
  have hqp : (0 : ℝ) < 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by linarith
  have hne : (2 : ℝ) * (N : ℝ) + 1 + 2 * (n : ℝ) ≠ 0 := ne_of_gt hqp
  set q : ℝ := 2 * (N : ℝ) + 1 + 2 * (n : ℝ) with hqd
  have hL : Lh (N + 1 + n) = (6 * q ^ 6 - 6 * q ^ 4 + 14 * q ^ 2 - 62) / (3 * q ^ 8) := by
    rw [Lh, hcast, L8, U6]; field_simp; ring
  have e2 : (1 : ℝ) ≤ q ^ 2 := by nlinarith
  have e4 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have e6 : q ^ 4 ≤ q ^ 6 := by nlinarith
  have hd8 : (0 : ℝ) < 3 * q ^ 8 := mul_pos (by norm_num) (pow_pos hqp 8)
  have hnum : |6 * q ^ 6 - 6 * q ^ 4 + 14 * q ^ 2 - 62| ≤ 96 * q ^ 6 := by
    rw [abs_le]; constructor <;> nlinarith
  rw [Real.norm_eq_abs, hL, abs_div, abs_of_pos hd8]
  calc |6 * q ^ 6 - 6 * q ^ 4 + 14 * q ^ 2 - 62| / (3 * q ^ 8)
      ≤ 96 * q ^ 6 / (3 * q ^ 8) := by gcongr
    _ = 32 / q ^ 2 := by field_simp; ring
    _ ≤ 32 / ((n : ℝ) + 1) := by
        have hb : (n : ℝ) + 1 ≤ q ^ 2 := by nlinarith
        gcongr
    _ = 32 * (1 / ((n : ℝ) + 1)) := by ring

/-- **`L₈(2N+1) ≤ R N`**, from the telescope's limit. -/
lemma Lh_le_Rt (N : ℕ) : Lh (N + 1) ≤ Rt N := by
  have hsum := summable_cube_shift N
  have hcomb : ∀ n : ℕ, Lh (N + 1) - Lh (N + 1 + n) ≤ Rt N := by
    intro n
    have hpart : Lh (N + 1 + 0) - Lh (N + 1 + n)
        ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3 := by
      rw [← Finset.sum_range_sub' (fun k => Lh (N + 1 + k)) n]
      exact Finset.sum_le_sum (fun k _ => Lh_sub_le_term (N + 1 + k) (by omega))
    have hts : ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3 ≤ Rt N :=
      hsum.sum_le_tsum _ (fun k _ => by positivity)
    simpa using le_trans hpart hts
  have htend : Filter.Tendsto (fun n : ℕ => Lh (N + 1) - Lh (N + 1 + n)) Filter.atTop
      (nhds (Lh (N + 1) - 0)) := Filter.Tendsto.const_sub _ (Lh_tendsto N)
  simpa using le_of_tendsto htend (Filter.Eventually.of_forall hcomb)

/-! ### The two rational comparisons that pin `δ = 1/g - a₁` -/

/-- `L₈(q) > 2/(q + 1/(2q))²` for `q ≥ 3`; this forces `δ < 1/(2q)`. -/
lemma firstlo (q : ℝ) (hq : 3 ≤ q) : 2 / (q + 1 / (2 * q)) ^ 2 < L8 q := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 3 + s := ⟨q - 3, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 3 + s := by linarith
  have hne0 : (3 : ℝ) + s ≠ 0 := ne_of_gt h0
  have hd : (0 : ℝ) < 2 * (3 + s) ^ 2 + 1 := by nlinarith
  have hned : (2 : ℝ) * (3 + s) ^ 2 + 1 ≠ 0 := ne_of_gt hd
  have hrw : (3 + s) + 1 / (2 * (3 + s)) = (2 * (3 + s) ^ 2 + 1) / (2 * (3 + s)) := by
    field_simp
  have key : L8 (3 + s) - 2 / ((3 + s) + 1 / (2 * (3 + s))) ^ 2
      = (38 * s ^ 6 + 684 * s ^ 5 + 4932 * s ^ 4 + 18144 * s ^ 3 + 35244 * s ^ 2
          + 32616 * s + 9496)
        / (3 * (3 + s) ^ 8 * (2 * (3 + s) ^ 2 + 1) ^ 2) := by
    rw [L8, U6, hrw]; field_simp; ring
  have hnum : (0 : ℝ) < 38 * s ^ 6 + 684 * s ^ 5 + 4932 * s ^ 4 + 18144 * s ^ 3
      + 35244 * s ^ 2 + 32616 * s + 9496 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6
    linarith
  have hden : (0 : ℝ) < 3 * (3 + s) ^ 8 * (2 * (3 + s) ^ 2 + 1) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos h0 8)) (pow_pos hd 2)
  linarith [key, div_pos hnum hden]

/-- `U₆(q) < 2/(q + 1/(2q+1))²` for `q ≥ 5`; this forces `δ > 1/(2q+1)`.
It genuinely fails at `q = 3` (the difference there is `-769/529254`), which is why
`N = 1` is handled separately by `Rt_one_lt`. -/
lemma firsthi (q : ℝ) (hq : 5 ≤ q) : U6 q < 2 / (q + 1 / (2 * q + 1)) ^ 2 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 5 + s := ⟨q - 5, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 5 + s := by linarith
  have hne0 : (5 : ℝ) + s ≠ 0 := ne_of_gt h0
  have h1 : (0 : ℝ) < 2 * (5 + s) + 1 := by linarith
  have hne1 : (2 : ℝ) * (5 + s) + 1 ≠ 0 := ne_of_gt h1
  have hd : (0 : ℝ) < 2 * (5 + s) ^ 2 + (5 + s) + 1 := by nlinarith
  have hned : (2 : ℝ) * (5 + s) ^ 2 + (5 + s) + 1 ≠ 0 := ne_of_gt hd
  have hrw : (5 + s) + 1 / (2 * (5 + s) + 1)
      = (2 * (5 + s) ^ 2 + (5 + s) + 1) / (2 * (5 + s) + 1) := by
    field_simp
  have key : 2 / ((5 + s) + 1 / (2 * (5 + s) + 1)) ^ 2 - U6 (5 + s)
      = (12 * s ^ 5 + 268 * s ^ 4 + 2316 * s ^ 3 + 9476 * s ^ 2 + 17532 * s + 10246)
        / (3 * (5 + s) ^ 6 * (2 * (5 + s) ^ 2 + (5 + s) + 1) ^ 2) := by
    rw [U6, hrw]; field_simp; ring
  have hnum : (0 : ℝ) < 12 * s ^ 5 + 268 * s ^ 4 + 2316 * s ^ 3 + 9476 * s ^ 2
      + 17532 * s + 10246 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5
    linarith
  have hden : (0 : ℝ) < 3 * (5 + s) ^ 6 * (2 * (5 + s) ^ 2 + (5 + s) + 1) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos h0 6)) (pow_pos hd 2)
  linarith [key, div_pos hnum hden]

/-- The `N = 1` upper bound, which `U₆` cannot supply.  Peel four terms and close with
the crude `Rt_le` at `N = 5`: `R 1 = 1/2³+1/3³+1/4³+1/5³ + R 5 ≤ … < 49/242`. -/
lemma Rt_one_lt : Rt 1 < 49 / 242 := by
  have h1 := Rt_succ 1
  have h2 := Rt_succ 2
  have h3 := Rt_succ 3
  have h4 := Rt_succ 4
  have h5 := Rt_le 5
  norm_num at h1 h2 h3 h4 h5 ⊢
  linarith

/-! ### Assembling `a₂` -/

lemma u_between (N : ℕ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (h1 : Rt N < 2 / A ^ 2) (h2 : 2 / B ^ 2 < Rt N) :
    A < 1 / Real.sqrt (Rt N / 2) ∧ 1 / Real.sqrt (Rt N / 2) < B := by
  have hB2 : (0 : ℝ) < 2 / B ^ 2 := by positivity
  have hR : (0 : ℝ) < Rt N := lt_trans hB2 h2
  have hsq1 : Rt N / 2 < (1 / A) ^ 2 := by
    have he : (1 / A) ^ 2 = (2 / A ^ 2) / 2 := by field_simp
    rw [he]; linarith
  have hsq2 : (1 / B) ^ 2 < Rt N / 2 := by
    have he : (1 / B) ^ 2 = (2 / B ^ 2) / 2 := by field_simp
    rw [he]; linarith
  have hs : 0 < Real.sqrt (Rt N / 2) := Real.sqrt_pos.mpr (by linarith)
  have hlt : Real.sqrt (Rt N / 2) < 1 / A := by
    have h := Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ Rt N / 2) hsq1
    rwa [Real.sqrt_sq (by positivity)] at h
  have hgt : 1 / B < Real.sqrt (Rt N / 2) := (Real.lt_sqrt (by positivity)).mpr hsq2
  constructor
  · rw [lt_div_iff₀ hs]
    calc A * Real.sqrt (Rt N / 2) < A * (1 / A) := mul_lt_mul_of_pos_left hlt hA
      _ = 1 := by field_simp
  · rw [div_lt_iff₀ hs]
    calc (1 : ℝ) = B * (1 / B) := by field_simp
      _ < B * Real.sqrt (Rt N / 2) := mul_lt_mul_of_pos_left hgt hB

lemma Rt_lt_up (N : ℕ) (hN : 1 ≤ N) :
    Rt N < 2 / ((2 * (N : ℝ) + 1) + 1 / (2 * (2 * (N : ℝ) + 1) + 1)) ^ 2 := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have hone : N = 1 := by omega
    subst hone
    have he : (2 : ℝ) / ((2 * ((1 : ℕ) : ℝ) + 1)
        + 1 / (2 * (2 * ((1 : ℕ) : ℝ) + 1) + 1)) ^ 2 = 49 / 242 := by
      norm_num
    rw [he]; exact Rt_one_lt
  · have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    have h1 := firsthi (2 * (N : ℝ) + 1) (by linarith)
    have h2 : Rt N ≤ U6 (2 * (N : ℝ) + 1) := by rw [← Uh_eq]; exact Rt_le_Uh N
    linarith

lemma Rt_gt_low (N : ℕ) (hN : 1 ≤ N) :
    2 / ((2 * (N : ℝ) + 1) + 1 / (2 * (2 * (N : ℝ) + 1))) ^ 2 < Rt N := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 := firstlo (2 * (N : ℝ) + 1) (by linarith)
  have h2 : L8 (2 * (N : ℝ) + 1) ≤ Rt N := by rw [← Lh_eq]; exact Lh_le_Rt N
  linarith

/-- **`a₂(N) = 4N+2`.**  The second regular-continued-fraction quotient of
`g N = √(R N / 2)` is `⌊1/δ⌋` with `δ = 1/g N - a₁`, and the sharper tail envelope
`L₈(q) ≤ R N ≤ U₆(q)` pins `δ` strictly between `1/(2q+1)` and `1/(2q)`, `q = 2N+1`.
`N ≥ 1` is necessary: at `N = 0` the quotient is `3`, not `2`. -/
theorem floor_a2 (N : ℕ) (hN : 1 ≤ N) :
    ⌊1 / (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1))⌋ = 4 * (N : ℤ) + 2 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hq0 : (0 : ℝ) < 2 * (2 * (N : ℝ) + 1) := by linarith
  have hq1 : (0 : ℝ) < 2 * (2 * (N : ℝ) + 1) + 1 := by linarith
  have hA0 : (0 : ℝ) < (2 * (N : ℝ) + 1) + 1 / (2 * (2 * (N : ℝ) + 1) + 1) := by
    have := div_pos one_pos hq1; linarith
  have hB0 : (0 : ℝ) < (2 * (N : ℝ) + 1) + 1 / (2 * (2 * (N : ℝ) + 1)) := by
    have := div_pos one_pos hq0; linarith
  obtain ⟨hlo, hhi⟩ := u_between N _ _ hA0 hB0 (Rt_lt_up N hN) (Rt_gt_low N hN)
  set u : ℝ := 1 / Real.sqrt (Rt N / 2) with hud
  have hdlo : 1 / (2 * (2 * (N : ℝ) + 1) + 1) < u - (2 * (N : ℝ) + 1) := by linarith
  have hdhi : u - (2 * (N : ℝ) + 1) < 1 / (2 * (2 * (N : ℝ) + 1)) := by linarith
  set d : ℝ := u - (2 * (N : ℝ) + 1) with hdd
  have hdpos : 0 < d := lt_trans (div_pos one_pos hq1) hdlo
  have k1 : 2 * (2 * (N : ℝ) + 1) < 1 / d := by
    rw [lt_div_iff₀ hdpos]
    calc 2 * (2 * (N : ℝ) + 1) * d
        < 2 * (2 * (N : ℝ) + 1) * (1 / (2 * (2 * (N : ℝ) + 1))) :=
          mul_lt_mul_of_pos_left hdhi hq0
      _ = 1 := by field_simp
  have k2 : 1 / d < 2 * (2 * (N : ℝ) + 1) + 1 := by
    rw [div_lt_iff₀ hdpos]
    calc (1 : ℝ) = (2 * (2 * (N : ℝ) + 1) + 1) * (1 / (2 * (2 * (N : ℝ) + 1) + 1)) := by
          field_simp
      _ < (2 * (2 * (N : ℝ) + 1) + 1) * d := mul_lt_mul_of_pos_left hdlo hq1
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith

/-! ### The third partial quotient

Two more comparison functions, built the same way:

    U₁₀(q) = L₈(q) + 762/(5q¹⁰),      L₁₂(q) = U₁₀(q) - 5110/(3q¹²),

and two more rational comparisons, this time against

    v₋(q) = q + 6q/(12q²+19),         v₊(q) = q + (6q²+19)/(q(12q²+57)).

Those two are not arbitrary: the complete quotient `X₃ = δ/(1-2qδ)` is strictly
increasing in `δ`, and `v∓` are reverse-engineered so that its values at the endpoints
are **exactly** `6q/19` and `6q/19 + 1/q`.  That is the whole content of the uniform
estimate in the write-up. -/

noncomputable def U10 (q : ℝ) : ℝ := L8 q + 762 / (5 * q ^ 10)

noncomputable def L12 (q : ℝ) : ℝ := U10 q - 5110 / (3 * q ^ 12)

lemma U10_nonneg (q : ℝ) (hq : 1 ≤ q) : 0 ≤ U10 q := by
  have h0 : (0 : ℝ) < q := by linarith
  have hne : q ≠ 0 := ne_of_gt h0
  have he : U10 q
      = (30 * q ^ 8 - 30 * q ^ 6 + 70 * q ^ 4 - 310 * q ^ 2 + 2286) / (15 * q ^ 10) := by
    rw [U10, L8, U6]; field_simp; ring
  rw [he]
  refine div_nonneg ?_ (le_of_lt (mul_pos (by norm_num) (pow_pos h0 10)))
  have e2 : (1 : ℝ) ≤ q ^ 2 := by nlinarith
  have e4 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have e6 : q ^ 4 ≤ q ^ 6 := by nlinarith
  have e8 : q ^ 6 ≤ q ^ 8 := by nlinarith
  nlinarith [sq_nonneg (14 * q ^ 2 - 31)]

lemma U10_defect (q : ℝ) (hq : 1 ≤ q) : 8 / (q + 1) ^ 3 ≤ U10 q - U10 (q + 2) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 1 + s := ⟨q - 1, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 1 + s := by linarith
  have h1 : (0 : ℝ) < 1 + s + 1 := by linarith
  have h2 : (0 : ℝ) < 1 + s + 2 := by linarith
  have hne0 : (1 : ℝ) + s ≠ 0 := ne_of_gt h0
  have hne1 : (1 : ℝ) + s + 1 ≠ 0 := ne_of_gt h1
  have hne2 : (1 : ℝ) + s + 2 ≠ 0 := ne_of_gt h2
  have key : U10 (1 + s) - U10 (1 + s + 2) - 8 / ((1 + s) + 1) ^ 3
      = (613200 * s ^ 10 + 12264000 * s ^ 9 + 111528584 * s ^ 8 + 607113344 * s ^ 7
          + 2189979328 * s ^ 6 + 5467657472 * s ^ 5 + 9564613360 * s ^ 4
          + 11570538368 * s ^ 3 + 9259462448 * s ^ 2 + 4424270016 * s + 957987144)
        / (15 * (1 + s) ^ 10 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 10) := by
    rw [U10, U10, L8, L8, U6, U6]; field_simp; ring
  have hnum : (0 : ℝ) ≤ 613200 * s ^ 10 + 12264000 * s ^ 9 + 111528584 * s ^ 8
      + 607113344 * s ^ 7 + 2189979328 * s ^ 6 + 5467657472 * s ^ 5
      + 9564613360 * s ^ 4 + 11570538368 * s ^ 3 + 9259462448 * s ^ 2
      + 4424270016 * s + 957987144 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6; have p7 := pow_nonneg hs 7
    have p8 := pow_nonneg hs 8; have p9 := pow_nonneg hs 9; have p10 := pow_nonneg hs 10
    linarith
  have hden : (0 : ℝ) < 15 * (1 + s) ^ 10 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 10 :=
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h0 10)) (pow_pos h1 3)) (pow_pos h2 10)
  linarith [key, div_nonneg hnum hden.le]

lemma L12_defect (q : ℝ) (hq : 1 ≤ q) : L12 q - L12 (q + 2) ≤ 8 / (q + 1) ^ 3 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 1 + s := ⟨q - 1, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 1 + s := by linarith
  have h1 : (0 : ℝ) < 1 + s + 1 := by linarith
  have h2 : (0 : ℝ) < 1 + s + 2 := by linarith
  have hne0 : (1 : ℝ) + s ≠ 0 := ne_of_gt h0
  have hne1 : (1 : ℝ) + s + 1 ≠ 0 := ne_of_gt h1
  have hne2 : (1 : ℝ) + s + 2 ≠ 0 := ne_of_gt h2
  have key : 8 / ((1 + s) + 1) ^ 3 - (L12 (1 + s) - L12 (1 + s + 2))
      = (11315816 * s ^ 12 + 271579584 * s ^ 11 + 3029000672 * s ^ 10
          + 20748341120 * s ^ 9 + 97154165736 * s ^ 8 + 327394012800 * s ^ 7
          + 813563841408 * s ^ 6 + 1501028015616 * s ^ 5 + 2039231999800 * s ^ 4
          + 1988028176832 * s ^ 3 + 1319213094816 * s ^ 2 + 534633091200 * s
          + 100004451704)
        / (15 * (1 + s) ^ 12 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 12) := by
    rw [L12, L12, U10, U10, L8, L8, U6, U6]; field_simp; ring
  have hnum : (0 : ℝ) ≤ 11315816 * s ^ 12 + 271579584 * s ^ 11 + 3029000672 * s ^ 10
      + 20748341120 * s ^ 9 + 97154165736 * s ^ 8 + 327394012800 * s ^ 7
      + 813563841408 * s ^ 6 + 1501028015616 * s ^ 5 + 2039231999800 * s ^ 4
      + 1988028176832 * s ^ 3 + 1319213094816 * s ^ 2 + 534633091200 * s
      + 100004451704 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6; have p7 := pow_nonneg hs 7
    have p8 := pow_nonneg hs 8; have p9 := pow_nonneg hs 9; have p10 := pow_nonneg hs 10
    have p11 := pow_nonneg hs 11; have p12 := pow_nonneg hs 12
    linarith
  have hden : (0 : ℝ) < 15 * (1 + s) ^ 12 * (1 + s + 1) ^ 3 * (1 + s + 2) ^ 12 :=
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h0 12)) (pow_pos h1 3)) (pow_pos h2 12)
  linarith [key, div_nonneg hnum hden.le]

noncomputable def Uk (j : ℕ) : ℝ := U10 (2 * (j : ℝ) - 1)

noncomputable def Lk (j : ℕ) : ℝ := L12 (2 * (j : ℝ) - 1)

lemma term_le_Uk_sub (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (j : ℝ) ^ 3 ≤ Uk j - Uk (j + 1) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) := by linarith
  have hb : (8 : ℝ) / ((2 * (j : ℝ) - 1) + 1) ^ 3 = 1 / (j : ℝ) ^ 3 := by
    rw [show (2 * (j : ℝ) - 1) + 1 = 2 * (j : ℝ) by ring, mul_pow]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hU : Uk (j + 1) = U10 ((2 * (j : ℝ) - 1) + 2) := by
    rw [Uk]; congr 1; push_cast; ring
  rw [Uk, hU, ← hb]
  exact U10_defect _ (by linarith)

lemma Lk_sub_le_term (j : ℕ) (hj : 1 ≤ j) :
    Lk j - Lk (j + 1) ≤ (1 : ℝ) / (j : ℝ) ^ 3 := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) := by linarith
  have hb : (8 : ℝ) / ((2 * (j : ℝ) - 1) + 1) ^ 3 = 1 / (j : ℝ) ^ 3 := by
    rw [show (2 * (j : ℝ) - 1) + 1 = 2 * (j : ℝ) by ring, mul_pow]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hL : Lk (j + 1) = L12 ((2 * (j : ℝ) - 1) + 2) := by
    rw [Lk]; congr 1; push_cast; ring
  rw [Lk, hL, ← hb]
  exact L12_defect _ (by linarith)

lemma Uk_eq (N : ℕ) : Uk (N + 1) = U10 (2 * (N : ℝ) + 1) := by
  rw [Uk]; congr 1; push_cast; ring

lemma Lk_eq (N : ℕ) : Lk (N + 1) = L12 (2 * (N : ℝ) + 1) := by
  rw [Lk]; congr 1; push_cast; ring

lemma Uk_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Uk j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  exact U10_nonneg _ (by linarith)

theorem Rt_le_Uk (N : ℕ) : Rt N ≤ Uk (N + 1) := by
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun n => ?_)
  calc ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3
      ≤ ∑ k ∈ Finset.range n, (Uk (N + 1 + k) - Uk (N + 1 + k + 1)) :=
        Finset.sum_le_sum (fun k _ => term_le_Uk_sub (N + 1 + k) (by omega))
    _ = Uk (N + 1 + 0) - Uk (N + 1 + n) :=
        Finset.sum_range_sub' (fun k => Uk (N + 1 + k)) n
    _ ≤ Uk (N + 1 + 0) := by linarith [Uk_nonneg (N + 1 + n) (by omega)]
    _ = Uk (N + 1) := by norm_num

lemma Lk_tendsto (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => Lk (N + 1 + n)) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => 2000 * (1 / ((n : ℝ) + 1))) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2000 : ℝ)
  refine squeeze_zero_norm (fun n => ?_) hg
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcast : (2 : ℝ) * ((N + 1 + n : ℕ) : ℝ) - 1 = 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by
    push_cast; ring
  have h1 : (1 : ℝ) ≤ 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by linarith
  have hqp : (0 : ℝ) < 2 * (N : ℝ) + 1 + 2 * (n : ℝ) := by linarith
  have hne : (2 : ℝ) * (N : ℝ) + 1 + 2 * (n : ℝ) ≠ 0 := ne_of_gt hqp
  set q : ℝ := 2 * (N : ℝ) + 1 + 2 * (n : ℝ) with hqd
  have hL : Lk (N + 1 + n)
      = (30 * q ^ 10 - 30 * q ^ 8 + 70 * q ^ 6 - 310 * q ^ 4 + 2286 * q ^ 2 - 25550)
        / (15 * q ^ 12) := by
    rw [Lk, hcast, L12, U10, L8, U6]; field_simp; ring
  have e2 : (1 : ℝ) ≤ q ^ 2 := by nlinarith
  have e4 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have e6 : q ^ 4 ≤ q ^ 6 := by nlinarith
  have e8 : q ^ 6 ≤ q ^ 8 := by nlinarith
  have e10 : q ^ 8 ≤ q ^ 10 := by nlinarith
  have hd12 : (0 : ℝ) < 15 * q ^ 12 := mul_pos (by norm_num) (pow_pos hqp 12)
  have hnum : |30 * q ^ 10 - 30 * q ^ 8 + 70 * q ^ 6 - 310 * q ^ 4 + 2286 * q ^ 2 - 25550|
      ≤ 30000 * q ^ 10 := by
    rw [abs_le]; constructor <;> nlinarith
  rw [Real.norm_eq_abs, hL, abs_div, abs_of_pos hd12]
  calc |30 * q ^ 10 - 30 * q ^ 8 + 70 * q ^ 6 - 310 * q ^ 4 + 2286 * q ^ 2 - 25550|
        / (15 * q ^ 12)
      ≤ 30000 * q ^ 10 / (15 * q ^ 12) := by gcongr
    _ = 2000 / q ^ 2 := by field_simp; ring
    _ ≤ 2000 / ((n : ℝ) + 1) := by
        have hb : (n : ℝ) + 1 ≤ q ^ 2 := by nlinarith
        gcongr
    _ = 2000 * (1 / ((n : ℝ) + 1)) := by ring

lemma Lk_le_Rt (N : ℕ) : Lk (N + 1) ≤ Rt N := by
  have hsum := summable_cube_shift N
  have hcomb : ∀ n : ℕ, Lk (N + 1) - Lk (N + 1 + n) ≤ Rt N := by
    intro n
    have hpart : Lk (N + 1 + 0) - Lk (N + 1 + n)
        ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3 := by
      rw [← Finset.sum_range_sub' (fun k => Lk (N + 1 + k)) n]
      exact Finset.sum_le_sum (fun k _ => Lk_sub_le_term (N + 1 + k) (by omega))
    have hts : ∑ k ∈ Finset.range n, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 3 ≤ Rt N :=
      hsum.sum_le_tsum _ (fun k _ => by positivity)
    simpa using le_trans hpart hts
  have htend : Filter.Tendsto (fun n : ℕ => Lk (N + 1) - Lk (N + 1 + n)) Filter.atTop
      (nhds (Lk (N + 1) - 0)) := Filter.Tendsto.const_sub _ (Lk_tendsto N)
  simpa using le_of_tendsto htend (Filter.Eventually.of_forall hcomb)

/-- `U₁₀(q) < 2/v₋(q)²` for `q ≥ 5`. -/
lemma thirdlo (q : ℝ) (hq : 5 ≤ q) :
    U10 q < 2 / (q + 6 * q / (12 * q ^ 2 + 19)) ^ 2 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 5 + s := ⟨q - 5, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 5 + s := by linarith
  have hne0 : (5 : ℝ) + s ≠ 0 := ne_of_gt h0
  have h19 : (0 : ℝ) < 12 * (5 + s) ^ 2 + 19 := by nlinarith
  have hne19 : (12 : ℝ) * (5 + s) ^ 2 + 19 ≠ 0 := ne_of_gt h19
  have h25 : (0 : ℝ) < 12 * (5 + s) ^ 2 + 25 := by nlinarith
  have hne25 : (12 : ℝ) * (5 + s) ^ 2 + 25 ≠ 0 := ne_of_gt h25
  have hrw : (5 + s) + 6 * (5 + s) / (12 * (5 + s) ^ 2 + 19)
      = (5 + s) * (12 * (5 + s) ^ 2 + 25) / (12 * (5 + s) ^ 2 + 19) := by
    field_simp; ring
  have key : 2 / ((5 + s) + 6 * (5 + s) / (12 * (5 + s) ^ 2 + 19)) ^ 2 - U10 (5 + s)
      = (21390 * s ^ 6 + 641700 * s ^ 5 + 7834316 * s ^ 4 + 49736320 * s ^ 3
          + 171313300 * s ^ 2 + 295817000 * s + 186510000)
        / (15 * (5 + s) ^ 10 * (12 * (5 + s) ^ 2 + 25) ^ 2) := by
    rw [U10, L8, U6, hrw]; field_simp; ring
  have hnum : (0 : ℝ) < 21390 * s ^ 6 + 641700 * s ^ 5 + 7834316 * s ^ 4
      + 49736320 * s ^ 3 + 171313300 * s ^ 2 + 295817000 * s + 186510000 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6
    linarith
  have hden : (0 : ℝ) < 15 * (5 + s) ^ 10 * (12 * (5 + s) ^ 2 + 25) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos h0 10)) (pow_pos h25 2)
  linarith [key, div_pos hnum hden]

/-- `L₁₂(q) > 2/v₊(q)²` for `q ≥ 5`. -/
lemma thirdhi (q : ℝ) (hq : 5 ≤ q) :
    2 / (q + (6 * q ^ 2 + 19) / (q * (12 * q ^ 2 + 57))) ^ 2 < L12 q := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ q = 5 + s := ⟨q - 5, by linarith, by ring⟩
  have h0 : (0 : ℝ) < 5 + s := by linarith
  have hne0 : (5 : ℝ) + s ≠ 0 := ne_of_gt h0
  have h57 : (0 : ℝ) < 12 * (5 + s) ^ 2 + 57 := by nlinarith
  have hne57 : (12 : ℝ) * (5 + s) ^ 2 + 57 ≠ 0 := ne_of_gt h57
  have hbig : (0 : ℝ) < 12 * (5 + s) ^ 4 + 63 * (5 + s) ^ 2 + 19 := by nlinarith
  have hnebig : (12 : ℝ) * (5 + s) ^ 4 + 63 * (5 + s) ^ 2 + 19 ≠ 0 := ne_of_gt hbig
  have hrw : (5 + s) + (6 * (5 + s) ^ 2 + 19) / ((5 + s) * (12 * (5 + s) ^ 2 + 57))
      = (12 * (5 + s) ^ 4 + 63 * (5 + s) ^ 2 + 19)
        / ((5 + s) * (12 * (5 + s) ^ 2 + 57)) := by
    field_simp; ring
  have key : L12 (5 + s)
      - 2 / ((5 + s) + (6 * (5 + s) ^ 2 + 19) / ((5 + s) * (12 * (5 + s) ^ 2 + 57))) ^ 2
      = (270 * s ^ 12 + 16200 * s ^ 11 + 554724 * s ^ 10 + 12886200 * s ^ 9
          + 204970482 * s ^ 8 + 2249099280 * s ^ 7 + 17198104480 * s ^ 6
          + 91778786400 * s ^ 5 + 336625888274 * s ^ 4 + 813144965480 * s ^ 3
          + 1174679399646 * s ^ 2 + 790309722460 * s + 45337098850)
        / (15 * (5 + s) ^ 12 * (12 * (5 + s) ^ 4 + 63 * (5 + s) ^ 2 + 19) ^ 2) := by
    rw [L12, U10, L8, U6, hrw]; field_simp; ring
  have hnum : (0 : ℝ) < 270 * s ^ 12 + 16200 * s ^ 11 + 554724 * s ^ 10
      + 12886200 * s ^ 9 + 204970482 * s ^ 8 + 2249099280 * s ^ 7 + 17198104480 * s ^ 6
      + 91778786400 * s ^ 5 + 336625888274 * s ^ 4 + 813144965480 * s ^ 3
      + 1174679399646 * s ^ 2 + 790309722460 * s + 45337098850 := by
    have p2 := pow_nonneg hs 2; have p3 := pow_nonneg hs 3; have p4 := pow_nonneg hs 4
    have p5 := pow_nonneg hs 5; have p6 := pow_nonneg hs 6; have p7 := pow_nonneg hs 7
    have p8 := pow_nonneg hs 8; have p9 := pow_nonneg hs 9; have p10 := pow_nonneg hs 10
    have p11 := pow_nonneg hs 11; have p12 := pow_nonneg hs 12
    linarith
  have hden : (0 : ℝ) < 15 * (5 + s) ^ 12
      * (12 * (5 + s) ^ 4 + 63 * (5 + s) ^ 2 + 19) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos h0 12)) (pow_pos hbig 2)
  linarith [key, div_pos hnum hden]

/-- `δ ↦ δ/(1-2Qδ)` is strictly increasing where the denominator stays positive. -/
lemma X3_mono (Q d1 d2 : ℝ) (hQ : 0 < Q) (h1 : 0 < d1) (h12 : d1 < d2)
    (hp2 : 0 < 1 - 2 * Q * d2) : d1 / (1 - 2 * Q * d1) < d2 / (1 - 2 * Q * d2) := by
  have hp1 : 0 < 1 - 2 * Q * d1 := by nlinarith
  rw [div_lt_div_iff₀ hp1 hp2]
  nlinarith

/-! ### Assembling `a₃` -/

lemma Rt_lt_up3 (N : ℕ) (hN : 2 ≤ N) :
    Rt N < 2 / ((2 * (N : ℝ) + 1)
      + 6 * (2 * (N : ℝ) + 1) / (12 * (2 * (N : ℝ) + 1) ^ 2 + 19)) ^ 2 := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 := thirdlo (2 * (N : ℝ) + 1) (by linarith)
  have h2 : Rt N ≤ U10 (2 * (N : ℝ) + 1) := by rw [← Uk_eq]; exact Rt_le_Uk N
  linarith

lemma Rt_gt_low3 (N : ℕ) (hN : 2 ≤ N) :
    2 / ((2 * (N : ℝ) + 1) + (6 * (2 * (N : ℝ) + 1) ^ 2 + 19)
      / ((2 * (N : ℝ) + 1) * (12 * (2 * (N : ℝ) + 1) ^ 2 + 57))) ^ 2 < Rt N := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 := thirdhi (2 * (N : ℝ) + 1) (by linarith)
  have h2 : L12 (2 * (N : ℝ) + 1) ≤ Rt N := by rw [← Lk_eq]; exact Lk_le_Rt N
  linarith

/-- **The uniform estimate** `6q/19 < X₃ < 6q/19 + 1/q`, `q = 2N+1`, for `N ≥ 2`. -/
lemma X3_bounds (N : ℕ) (hN : 2 ≤ N) :
    6 * (2 * (N : ℝ) + 1) / 19
        < (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1))
          / (1 - 2 * (2 * (N : ℝ) + 1) * (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)))
      ∧ (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1))
          / (1 - 2 * (2 * (N : ℝ) + 1) * (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)))
        < 6 * (2 * (N : ℝ) + 1) / 19 + 1 / (2 * (N : ℝ) + 1) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set Q : ℝ := 2 * (N : ℝ) + 1 with hQd
  have hQ5 : (5 : ℝ) ≤ Q := by simp only [hQd]; linarith
  have hQ : (0 : ℝ) < Q := by linarith
  have h19 : (0 : ℝ) < 12 * Q ^ 2 + 19 := by nlinarith
  have h57 : (0 : ℝ) < 12 * Q ^ 2 + 57 := by nlinarith
  have hA0 : (0 : ℝ) < Q + 6 * Q / (12 * Q ^ 2 + 19) := by
    have := div_pos (by linarith : (0:ℝ) < 6 * Q) h19; linarith
  have hB0 : (0 : ℝ) < Q + (6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57)) := by
    have := div_pos (by nlinarith : (0:ℝ) < 6 * Q ^ 2 + 19)
      (by positivity : (0:ℝ) < Q * (12 * Q ^ 2 + 57))
    linarith
  obtain ⟨hlo, hhi⟩ := u_between N _ _ hA0 hB0 (Rt_lt_up3 N hN) (Rt_gt_low3 N hN)
  set d : ℝ := 1 / Real.sqrt (Rt N / 2) - Q with hdd
  have hdlo : 6 * Q / (12 * Q ^ 2 + 19) < d := by simp only [hdd]; linarith
  have hdhi : d < (6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57)) := by
    simp only [hdd]; linarith
  have hdpos : 0 < d := lt_trans (div_pos (by linarith) h19) hdlo
  -- the two endpoint evaluations, exactly
  have hem : (6 * Q / (12 * Q ^ 2 + 19)) / (1 - 2 * Q * (6 * Q / (12 * Q ^ 2 + 19)))
      = 6 * Q / 19 := by
    rw [show (1 : ℝ) - 2 * Q * (6 * Q / (12 * Q ^ 2 + 19)) = 19 / (12 * Q ^ 2 + 19) by
      field_simp; ring]
    field_simp
  have hbot : (0 : ℝ) < 1 - 2 * Q * ((6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57))) := by
    rw [show (1 : ℝ) - 2 * Q * ((6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57)))
        = 19 / (12 * Q ^ 2 + 57) by field_simp; ring]
    positivity
  have hep : ((6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57)))
        / (1 - 2 * Q * ((6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57))))
      = 6 * Q / 19 + 1 / Q := by
    rw [show (1 : ℝ) - 2 * Q * ((6 * Q ^ 2 + 19) / (Q * (12 * Q ^ 2 + 57)))
        = 19 / (12 * Q ^ 2 + 57) by field_simp; ring]
    field_simp
  constructor
  · have := X3_mono Q _ _ hQ (div_pos (by linarith) h19) hdlo (by nlinarith [hbot, hdhi])
    rwa [hem] at this
  · have := X3_mono Q _ _ hQ hdpos hdhi hbot
    rwa [hep] at this

/-- The integrality step: `6q/19` sits at distance at least `1/19` below the next
integer unless it is one, and `1/q ≤ 1/19` once `q ≥ 21`. -/
lemma frac_gap (N : ℕ) (hN : 2 ≤ N) :
    6 * (2 * (N : ℝ) + 1) / 19 + 1 / (2 * (N : ℝ) + 1)
      < (⌊(12 * (N : ℝ) + 6) / 19⌋ : ℝ) + 1 := by
  have hcast : 6 * (2 * (N : ℝ) + 1) / 19 = (12 * (N : ℝ) + 6) / 19 := by ring
  rw [hcast]
  rcases Nat.lt_or_ge N 10 with h | h
  · interval_cases N <;> norm_num
  · have hNr : (10 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    have hinv : 1 / (2 * (N : ℝ) + 1) ≤ 1 / 21 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hfl : ((⌊(12 * (N : ℝ) + 6) / 19⌋ : ℤ) : ℝ) ≤ (12 * (N : ℝ) + 6) / 19 :=
      Int.floor_le _
    have hfu : (12 * (N : ℝ) + 6) / 19 < ((⌊(12 * (N : ℝ) + 6) / 19⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have zlo : (19 : ℤ) * ⌊(12 * (N : ℝ) + 6) / 19⌋ ≤ 12 * (N : ℤ) + 6 := by
      have hr : (19 : ℝ) * ((⌊(12 * (N : ℝ) + 6) / 19⌋ : ℤ) : ℝ)
          ≤ 12 * (N : ℝ) + 6 := by linarith
      exact_mod_cast hr
    have zhi : 12 * (N : ℤ) + 6 < 19 * (⌊(12 * (N : ℝ) + 6) / 19⌋ + 1) := by
      have hr : 12 * (N : ℝ) + 6
          < 19 * (((⌊(12 * (N : ℝ) + 6) / 19⌋ : ℤ) : ℝ) + 1) := by linarith
      exact_mod_cast hr
    have zgap : 12 * (N : ℤ) + 6 - 19 * ⌊(12 * (N : ℝ) + 6) / 19⌋ ≤ 18 := by omega
    have rgap : 12 * (N : ℝ) + 6
        - 19 * ((⌊(12 * (N : ℝ) + 6) / 19⌋ : ℤ) : ℝ) ≤ 18 := by
      exact_mod_cast zgap
    linarith

/-- **`a₃(N) = ⌊(12N+6)/19⌋`** for `N ≥ 2`.  The third regular-continued-fraction
quotient of `g N = √(R N / 2)`.  At `N = 1` the true quotient is `1` while the formula
gives `0`, so the guard is necessary — the write-up flags this too. -/
theorem floor_a3 (N : ℕ) (hN : 2 ≤ N) :
    ⌊(1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1))
      / (1 - 2 * (2 * (N : ℝ) + 1)
          * (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)))⌋
      = ⌊(12 * (N : ℝ) + 6) / 19⌋ := by
  obtain ⟨hlo, hhi⟩ := X3_bounds N hN
  have hfl : ((⌊(12 * (N : ℝ) + 6) / 19⌋ : ℤ) : ℝ) ≤ (12 * (N : ℝ) + 6) / 19 :=
    Int.floor_le _
  have he : 6 * (2 * (N : ℝ) + 1) / 19 = (12 * (N : ℝ) + 6) / 19 := by ring
  rw [he] at hlo hhi
  refine Int.floor_eq_iff.mpr ⟨by linarith, ?_⟩
  have := frac_gap N hN
  rw [he] at this
  push_cast at this ⊢
  linarith

/-! ### The three quotients as one continued-fraction chain

`floor_a3` above states `a₃` through the closed form `δ/(1-2qδ)`.  The algorithm's own
form is `1/(1/δ - a₂)`, and these two lemmas close that gap, so the module's three
headline theorems read as successive steps of the SAME floor-and-invert process:
`⌊u⌋`, then `⌊1/δ⌋`, then `⌊1/(1/δ - a₂)⌋`. -/

lemma delta_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 < 1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)
      ∧ 0 < 1 - 2 * (2 * (N : ℝ) + 1)
          * (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hq0 : (0 : ℝ) < 2 * (2 * (N : ℝ) + 1) := by linarith
  have hq1 : (0 : ℝ) < 2 * (2 * (N : ℝ) + 1) + 1 := by linarith
  have hA0 : (0 : ℝ) < (2 * (N : ℝ) + 1) + 1 / (2 * (2 * (N : ℝ) + 1) + 1) := by
    have := div_pos one_pos hq1; linarith
  have hB0 : (0 : ℝ) < (2 * (N : ℝ) + 1) + 1 / (2 * (2 * (N : ℝ) + 1)) := by
    have := div_pos one_pos hq0; linarith
  obtain ⟨hlo, hhi⟩ := u_between N _ _ hA0 hB0 (Rt_lt_up N hN) (Rt_gt_low N hN)
  refine ⟨by linarith [div_pos one_pos hq1], ?_⟩
  have hd : 1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)
      < 1 / (2 * (2 * (N : ℝ) + 1)) := by linarith
  have hone : 2 * (2 * (N : ℝ) + 1) * (1 / (2 * (2 * (N : ℝ) + 1))) = 1 := by field_simp
  have hm := mul_lt_mul_of_pos_left hd hq0
  rw [hone] at hm
  linarith

lemma X3_eq (N : ℕ) (hN : 1 ≤ N) :
    1 / (1 / (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)) - (4 * (N : ℝ) + 2))
      = (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1))
        / (1 - 2 * (2 * (N : ℝ) + 1)
            * (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1))) := by
  obtain ⟨hd, hden⟩ := delta_bounds N hN
  set d : ℝ := 1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1) with hdd
  have hdne : d ≠ 0 := ne_of_gt hd
  have hkey : 1 / d - (4 * (N : ℝ) + 2) = (1 - 2 * (2 * (N : ℝ) + 1) * d) / d := by
    field_simp; ring
  rw [hkey, one_div_div]

/-- **`a₃(N) = ⌊(12N+6)/19⌋` in the algorithm's own form.**  With
`u = 1/g N`, `a₁ = ⌊u⌋ = 2N+1` (`floor_one_div_sqrt`), `δ = u - a₁`,
`a₂ = ⌊1/δ⌋ = 4N+2` (`floor_a2`), the third quotient is `⌊1/(1/δ - a₂)⌋`. -/
theorem floor_a3_cf (N : ℕ) (hN : 2 ≤ N) :
    ⌊1 / (1 / (1 / Real.sqrt (Rt N / 2) - (2 * (N : ℝ) + 1)) - (4 * (N : ℝ) + 2))⌋
      = ⌊(12 * (N : ℝ) + 6) / 19⌋ := by
  rw [X3_eq N (by omega)]
  exact floor_a3 N hN

end Principia.MathDB.P375794
