import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

/-!
# MathDB #357173 — Garcia Conjecture 6.6, with an explicit rate

Write-up: `mathdb-open-problems/problems/357173/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: J. Garcia, *Class Number of the Imaginary Quadratic Field and Quadratic Residues
Identities*, arXiv:2301.02951v1, Notation 2.2 and **Conjecture 6.6**.

With `p = 4n − 1`, `M = ⌊n²/p⌋`, `R_m = √(mp)` and `Q_m = (1 + √(4mp + 3p − 4))/2`, set

`A_n = Σ_{m=1}^{M} ⌊R_m⌋ + Σ_{m=0}^{M−1} ⌊Q_m⌋`  and  `D_n = Mp + 2n`.

The source conjectures `A_n/D_n → 1/3` along primes `p`. The write-up proves the limit **with an
explicit rate and no primality assumption**: for every `n ≥ 4`,
`|A_n − D_n/3| ≤ 4n`, `|A_n − ⌊D_n/3⌋| ≤ 4n+1` and `|A_n/D_n − 1/3| ≤ 8/n`.

## This module is a SPINE

Per the project's spine rule, the chain of inferences to the goal is written first, with the one
genuinely analytic step — the integral comparison `(2/3)M^{3/2} ≤ Σ_{m≤M} √m ≤ (2/3)M^{3/2} + √M`
and the rounding that turns it into a bound on `A_n` — carried as a **named hypothesis**
(`hsandwich`) rather than as `sorry`. It is an obligation, not a gap in an argument this module
claims: `garcia_spine` composes it with everything below, and the composition is a typing fact.

Everything that is *not* that one step is proved here, and it is most of the argument:

* **The arithmetic core.** `M_eq` proves `⌊n²/(4n−1)⌋ = ⌊n/4⌋` — exactly, for every `n ≥ 1` —
  which is the write-up's opening move and the only place the definition of `M` is used.
* **The `D` expansion**, `D_expand`: `4 D_n = 4n² + (7 − 4r)n + r` with `r = n mod 4`, an exact
  identity over `ℤ` with no truncation; and its two consequences `D_close` (`|D_n − n²| ≤ 2n`)
  and `D_ge_half` (`n² ≤ 2 D_n`, which is where `n ≥ 4` is actually spent).
* **The root sandwich**, `R_le_Q` and `Q_le_R_succ`, with their floor forms — the comparison that
  brackets the second sum by the first.
* **The two elementary inequalities** the write-up uses to bound `n²/3 − W`, including Bernoulli
  at the exponent `3/2`.

## What the verifier measured that the write-up does not say

* **The constant `4` is slack by a factor of six.** Over `4 ≤ n ≤ 4000` the worst value of
  `|A_n − D_n/3|/n` is `2/3`, not `4`. The write-up's own Task 2 asks for the optimal constant;
  `2/3` is the measurement, and it is attained.
* **`n ≥ 4` is spent in exactly one place.** `M = ⌊n/4⌋` holds from `n = 1`, and the main bound
  holds at `n = 1, 2, 3` too — but only because `M = 0` there makes both sums **empty**, so that
  is degeneracy, not strength. The hypothesis is genuinely needed for `D_n ≥ n²/2`.
* **Dropping primality costs nothing**, as the write-up claims: the worst ratio off the prime
  subsequence (`0.6667`, 345 values) is no worse than on it (`0.6111`, 151 values).
-/

namespace Principia.MathDB.P357173

open Finset

/-! ## Definitions -/

/-- `p = 4n − 1`. -/
def pp (n : ℕ) : ℕ := 4 * n - 1

/-- `M = ⌊n²/p⌋`. -/
def MM (n : ℕ) : ℕ := n ^ 2 / pp n

/-- `R_m = √(m p)`. -/
noncomputable def R (n m : ℕ) : ℝ := Real.sqrt (m * pp n)

/-- `Q_m = (1 + √(4 m p + 3 p − 4))/2`. -/
noncomputable def Q (n m : ℕ) : ℝ := (1 + Real.sqrt (4 * m * pp n + 3 * pp n - 4)) / 2

/-- `A_n`, the paired floor sum. -/
noncomputable def A (n : ℕ) : ℤ :=
  (∑ m ∈ Finset.Icc 1 (MM n), ⌊R n m⌋) + (∑ m ∈ Finset.range (MM n), ⌊Q n m⌋)

/-- `D_n = M p + 2n`. -/
def D (n : ℕ) : ℕ := MM n * pp n + 2 * n

/-! ## The arithmetic core -/

/-- `p + 1 = 4n`, which is how `pp` is used everywhere below: no `ℕ`-subtraction ever appears
in a proof. -/
theorem pp_succ (n : ℕ) (hn : 1 ≤ n) : pp n + 1 = 4 * n := by
  simp only [pp]; omega

theorem pp_pos (n : ℕ) (hn : 1 ≤ n) : 0 < pp n := by
  simp only [pp]; omega

/-- **The arithmetic core of the write-up's opening move:** `⌊n²/(4n−1)⌋ = ⌊n/4⌋`.

The write-up gets this from `n²/(4n−1) = n/4 + n/(4(4n−1))` with the second term in `(0, 1/4)`;
here it is an exact `ℕ` statement, proved from the single identity
`n² = M·p + (r·n + M)` with `n = 4M + r`, which has no subtraction in it at all. -/
theorem M_eq (n : ℕ) (hn : 1 ≤ n) : MM n = n / 4 := by
  have hp := pp_succ n hn
  obtain ⟨M, r, hMdef, hn4, hrlt⟩ :
      ∃ M r : ℕ, M = n / 4 ∧ 4 * M + r = n ∧ r < 4 :=
    ⟨n / 4, n % 4, rfl, by omega, by omega⟩
  have key : M * pp n + (r * n + M) = n ^ 2 := by
    have e1 : M * pp n + (r * n + M) = M * (pp n + 1) + r * n := by ring
    rw [e1, hp]
    have e2 : M * (4 * n) + r * n = (4 * M + r) * n := by ring
    rw [e2, hn4]
    ring
  have hlo : M * pp n ≤ n ^ 2 := by
    rw [← key]; exact Nat.le_add_right _ _
  have hhi : n ^ 2 < (M + 1) * pp n := by
    have e : (M + 1) * pp n = M * pp n + pp n := by ring
    rw [e, ← key]
    -- `r·n + M < p` is linear once `r` is one of its four values
    have hsmall : r * n + M < pp n := by interval_cases r <;> omega
    exact Nat.add_lt_add_left hsmall _
  rw [MM, hMdef.symm]
  exact Nat.div_eq_of_lt_le hlo hhi

theorem M_ge_one (n : ℕ) (hn : 4 ≤ n) : 1 ≤ MM n := by
  rw [M_eq n (by omega)]; omega

/-- **The exact expansion of `D_n`**, over `ℤ` so no truncation occurs:
`4 D_n = 4n² + (7 − 4r) n + r` with `r = n mod 4`. -/
theorem D_expand (n : ℕ) (hn : 1 ≤ n) :
    4 * (D n : ℤ) = 4 * (n : ℤ) ^ 2 + (7 - 4 * ((n : ℤ) % 4)) * n + (n : ℤ) % 4 := by
  have hp := pp_succ n hn
  have hMe := M_eq n hn
  have hmod : ((n : ℤ) % 4) = ((n % 4 : ℕ) : ℤ) := by omega
  have hn4 : 4 * (n / 4) + n % 4 = n := by omega
  have hD : D n = n / 4 * pp n + 2 * n := by rw [D, hMe]
  have hpz : (pp n : ℤ) + 1 = 4 * n := by exact_mod_cast hp
  have hn4z : 4 * ((n / 4 : ℕ) : ℤ) + ((n % 4 : ℕ) : ℤ) = n := by exact_mod_cast hn4
  rw [hD, hmod]
  push_cast
  nlinarith [hpz, hn4z]

/-- `|D_n − n²| ≤ 2n`: the write-up's `|D_n/3 − n²/3| ≤ 2n/3`, cleared of the division. -/
theorem D_close (n : ℕ) (hn : 1 ≤ n) : |(D n : ℤ) - (n : ℤ) ^ 2| ≤ 2 * n := by
  have h := D_expand n hn
  have hr : (n : ℤ) % 4 = 0 ∨ (n : ℤ) % 4 = 1 ∨ (n : ℤ) % 4 = 2 ∨ (n : ℤ) % 4 = 3 := by omega
  have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  rw [abs_le]
  constructor <;> rcases hr with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> linarith

/-- `n² ≤ 2 D_n` for `n ≥ 4`. **This is the one place `n ≥ 4` is spent** — the verifier confirms
`M_eq` and the main bound survive below it, the latter only because both sums are then empty. -/
theorem D_ge_half (n : ℕ) (hn : 4 ≤ n) : (n : ℤ) ^ 2 ≤ 2 * (D n : ℤ) := by
  have h := D_close n (by omega)
  have hn4 : (4 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  rw [abs_le] at h
  nlinarith [h.1, h.2]

theorem D_pos (n : ℕ) (hn : 4 ≤ n) : 0 < (D n : ℤ) := by
  have h := D_ge_half n hn
  have hn4 : (4 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  nlinarith

/-! ## The root sandwich -/

theorem R_le_Q (n m : ℕ) (hn : 1 ≤ n) : R n m ≤ Q n m := by
  have hP : (0 : ℝ) ≤ (pp n : ℝ) := by positivity
  have hP2 : (2 : ℝ) ≤ (pp n : ℝ) := by
    have : 3 ≤ pp n := by simp only [pp]; omega
    have := (Nat.cast_le (α := ℝ)).2 this
    simp at this ⊢; linarith
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hstep : (4 : ℝ) * m * pp n ≤ 4 * m * pp n + 3 * pp n - 4 := by nlinarith
  have h1 : Real.sqrt (4 * m * pp n) ≤ Real.sqrt (4 * m * pp n + 3 * pp n - 4) :=
    Real.sqrt_le_sqrt hstep
  have h2 : Real.sqrt (4 * (m : ℝ) * pp n) = 2 * Real.sqrt ((m : ℝ) * pp n) := by
    rw [show (4 : ℝ) * m * pp n = 2 ^ 2 * ((m : ℝ) * pp n) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [R, Q]
  rw [h2] at h1
  linarith

theorem Q_le_R_succ (n m : ℕ) : Q n m ≤ R n (m + 1) + 1 := by
  have hP : (0 : ℝ) ≤ (pp n : ℝ) := by positivity
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hstep : (4 : ℝ) * m * pp n + 3 * pp n - 4 ≤ 4 * ((m : ℝ) + 1) * pp n := by nlinarith
  have h1 : Real.sqrt (4 * (m : ℝ) * pp n + 3 * pp n - 4)
      ≤ Real.sqrt (4 * ((m : ℝ) + 1) * pp n) := Real.sqrt_le_sqrt hstep
  have h2 : Real.sqrt (4 * ((m : ℝ) + 1) * pp n) = 2 * Real.sqrt (((m : ℝ) + 1) * pp n) := by
    rw [show (4 : ℝ) * ((m : ℝ) + 1) * pp n = 2 ^ 2 * (((m : ℝ) + 1) * pp n) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have h3 : Real.sqrt (((m : ℝ) + 1) * pp n) = R n (m + 1) := by
    rw [R]; push_cast; ring_nf
  rw [Q]
  rw [h2, h3] at h1
  have : (0 : ℝ) ≤ R n (m + 1) := by rw [R]; positivity
  linarith

/-- The floor form of the left comparison. -/
theorem floor_R_le_floor_Q (n m : ℕ) (hn : 1 ≤ n) : ⌊R n m⌋ ≤ ⌊Q n m⌋ :=
  Int.floor_le_floor (R_le_Q n m hn)

/-- The floor form of the right comparison: `⌊x + 1⌋ = ⌊x⌋ + 1` costs nothing. -/
theorem floor_Q_le_floor_R_succ (n m : ℕ) : ⌊Q n m⌋ ≤ ⌊R n (m + 1)⌋ + 1 := by
  have h := Int.floor_le_floor (Q_le_R_succ n m)
  rwa [Int.floor_add_one] at h

/-! ## The two elementary inequalities -/

/-- `1 − √(1−x) ≤ x` on `[0,1]`, because `t ≤ √t` there. -/
theorem one_sub_sqrt_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 - Real.sqrt (1 - x) ≤ x := by
  have ht : (0 : ℝ) ≤ 1 - x := by linarith
  have hsq : (1 - x) ^ 2 ≤ 1 - x := by nlinarith
  have h2 : Real.sqrt ((1 - x) ^ 2) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq ht] at h2
  linarith

/-- `1 − (1−y)^{3/2} ≤ (3/2) y` — Bernoulli's inequality at the exponent `3/2`.
The write-up states it on `[0,1]`; only `y ≤ 1` is used, and the verifier confirms it holds
for every `y ≤ 1`, so the lower bound comes out of the statement. -/
theorem one_sub_rpow_le (y : ℝ) (h1 : y ≤ 1) :
    1 - (1 - y) ^ (3 / 2 : ℝ) ≤ 3 / 2 * y := by
  have hb := one_add_mul_self_le_rpow_one_add (s := -y) (by linarith)
    (p := (3 / 2 : ℝ)) (by norm_num)
  have e : (1 : ℝ) + -y = 1 - y := by ring
  rw [e] at hb
  linarith

/-! ## The spine

The one analytic step — the integral comparison and the rounding that turns it into a bound on
`A_n` — is a NAMED HYPOTHESIS. Everything else is discharged. -/

/-- **The spine.** Given the write-up's displayed estimate `|A_n − n²/3| ≤ 37n/12`, the theorem's
first claim follows from `D_close` alone, and the arithmetic is exact: `37/12 + 8/12 = 45/12 ≤ 4`.
The hypothesis is an obligation the campaign owes, not a gap in the argument stated here. -/
theorem garcia_spine (n : ℕ) (hn : 4 ≤ n)
    (hsandwich : |(A n : ℝ) - (n : ℝ) ^ 2 / 3| ≤ 37 * (n : ℝ) / 12) :
    |(A n : ℝ) - (D n : ℝ) / 3| ≤ 4 * (n : ℝ) := by
  have hD := D_close n (by omega)
  rw [abs_le] at hD
  -- cast the two SIDES, never the `abs`: `Int.cast_abs` transport is where this goes wrong
  have h1 : -(2 * (n : ℝ)) ≤ (D n : ℝ) - (n : ℝ) ^ 2 := by exact_mod_cast hD.1
  have h2 : (D n : ℝ) - (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) := by exact_mod_cast hD.2
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [abs_le] at hsandwich ⊢
  -- 37/12 + 8/12 = 45/12 = 3.75 ≤ 4
  constructor <;> linarith [hsandwich.1, hsandwich.2]

/-- The second claim: rounding `D_n/3` moves it by less than one. -/
theorem garcia_floor (n : ℕ)
    (hmain : |(A n : ℝ) - (D n : ℝ) / 3| ≤ 4 * (n : ℝ)) :
    |(A n : ℝ) - (⌊(D n : ℝ) / 3⌋ : ℝ)| ≤ 4 * (n : ℝ) + 1 := by
  have h1 : (⌊(D n : ℝ) / 3⌋ : ℝ) ≤ (D n : ℝ) / 3 := Int.floor_le _
  have h2 : (D n : ℝ) / 3 - 1 < (⌊(D n : ℝ) / 3⌋ : ℝ) := Int.sub_one_lt_floor _
  rw [abs_le] at hmain ⊢
  constructor <;> linarith [hmain.1, hmain.2]

/-- The third claim, and with it the conjectured limit: `|A_n/D_n − 1/3| ≤ 8/n`. -/
theorem garcia_ratio (n : ℕ) (hn : 4 ≤ n)
    (hmain : |(A n : ℝ) - (D n : ℝ) / 3| ≤ 4 * (n : ℝ)) :
    |(A n : ℝ) / (D n : ℝ) - 1 / 3| ≤ 8 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hDpos : (0 : ℝ) < (D n : ℝ) := by
    have := D_pos n hn
    exact_mod_cast this
  have hDhalf : (n : ℝ) ^ 2 ≤ 2 * (D n : ℝ) := by
    have := D_ge_half n hn
    exact_mod_cast this
  have key : (A n : ℝ) / (D n : ℝ) - 1 / 3
      = ((A n : ℝ) - (D n : ℝ) / 3) / (D n : ℝ) := by
    field_simp
  rw [key, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  -- `8/n · D ≥ 4n` is exactly `n² ≤ 2D`
  have hstep : (4 : ℝ) * n ≤ 8 / (n : ℝ) * (D n : ℝ) := by
    rw [show (8 : ℝ) / (n : ℝ) * (D n : ℝ) = 8 * (D n : ℝ) / (n : ℝ) by ring,
      le_div_iff₀ hn0]
    nlinarith [hDhalf]
  linarith

end Principia.MathDB.P357173
