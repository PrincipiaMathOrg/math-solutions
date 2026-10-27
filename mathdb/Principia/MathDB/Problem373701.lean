import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# MathDB #373701 — Hyman's Conjecture 3.17 is FALSE

Write-up: `mathdb-open-problems/problems/373701/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: J. M. Hyman, *Why Eight Percent of Benford Sequences Never Converge*, arXiv:2603.18243v1
(2026), Definition 3.11, Corollary 3.16 and **Conjecture 3.17**, pp. 16–18.

The conjecture proposes that the persistent integer bases `P_N` have natural density `1/12`. The
refutation: for every fixed sample depth `N ≥ 3` the density **does not exist**, because two
continued-fraction cylinders inside `(0,1)` — one entirely persistent, one entirely
non-persistent — each repeat in every decimal decade, forcing `δ = 1` and `δ = 0`.

## What this module proves: the criterion is DECIDED on both cylinders

Persistence at depth `N` depends only on the partial quotients and convergent denominators, so
the two cylinder verdicts are statements about an abstract quotient sequence and need no
continued-fraction theory at all. Both are here:

* `persistent_of_cylinder_plus` — if `a₁ = 1` and `a₂ ≥ N²` then the criterion fires **at
  `k = 1`**, because `q₁ = a₁ = 1 ≤ N` and `N log N < N² ≤ a₂`. The only analytic input is
  `log N < N`.
* `not_persistent_of_all_ones` — if the first `L` quotients are `1` and `q_L > N`, the criterion
  **never** fires: monotonicity of `q` forces every index with `q_k ≤ N` to have `k < L`, so
  `a_{k+1} q_k = q_k ≤ N < N log N`. The only analytic input is `1 < log N`, which is exactly
  why the theorem needs `N ≥ 3`.

`qden_all_ones` identifies the all-ones denominators as Fibonacci numbers, `least_L_three` pins
the least admissible `L` at `4` for `N = 3`, and the three integer witnesses place bases `9` and
`4` in the two cylinders **without a floating-point logarithm** — `9¹⁰ > 10⁹` for the persistent
one, `4⁵ > 10³` and `4⁸ < 10⁵` for the other. `ten_rpow_lt_iff` is the bridge that makes those
integer inequalities mean what they are meant to mean.

## What is absent, and it is a genuine Mathlib gap

Two things, both named rather than worked around.

* **Cylinders.** Mathlib has `GenContFract`, the continuant recurrence, the determinant and the
  approximation theory — but **no characterisation of a cylinder as an interval**: nothing says
  that the reals whose first `L` partial quotients are `1` are exactly the open interval between
  `p_L/q_L` and `(p_L+p_{L-1})/(q_L+q_{L-1})`. That is what links the abstract verdicts above to
  a set of real `θ`, and it is a project rather than a tick.
* **Natural density.** Mathlib has no notion of it at all — no `natDensity`, no upper or lower
  density. The counting argument that turns the two cylinders into `δ = 1` and `δ = 0` therefore
  has to define its own, which is stage 2 here.

The verifier runs the whole argument, including both counting families with their local counts
asserted exactly.

## A control that refuted a proxy, not a prediction

The verifier's first version of the counting step measured a **cumulative** counting ratio against
an invented threshold of `0.05`; the measurement returned `0.0288` and refuted it. The threshold
was a guess, and the quantity was the wrong one as well — the proof is **local to one decade
interval**. Both local counts are exact and are now asserted exactly.
-/

namespace Principia.MathDB.P373701

/-! ## Convergent denominators of an abstract quotient sequence -/

/-- `q₀ = 1`, `q₁ = a₁`, `q_{k+2} = a_{k+2} q_{k+1} + q_k`. -/
def qden (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | (k + 2) => a (k + 2) * qden a (k + 1) + qden a k

theorem qden_zero (a : ℕ → ℕ) : qden a 0 = 1 := rfl

theorem qden_one (a : ℕ → ℕ) : qden a 1 = a 1 := rfl

theorem qden_succ_succ (a : ℕ → ℕ) (k : ℕ) :
    qden a (k + 2) = a (k + 2) * qden a (k + 1) + qden a k := rfl

theorem qden_le_succ (a : ℕ → ℕ) (hpos : ∀ j, 1 ≤ a j) (k : ℕ) :
    qden a k ≤ qden a (k + 1) := by
  match k with
  | 0 => simpa [qden_zero, qden_one] using hpos 1
  | (n + 1) =>
      rw [qden_succ_succ]
      have := hpos (n + 2)
      nlinarith [Nat.zero_le (qden a n), Nat.zero_le (qden a (n + 1))]

theorem qden_mono (a : ℕ → ℕ) (hpos : ∀ j, 1 ≤ a j) : Monotone (qden a) :=
  monotone_nat_of_le_succ (qden_le_succ a hpos)

/-! ## Hyman's persistence criterion -/

/-- Corollary 3.16 of the source: some index `k` has `q_k ≤ N` and `a_{k+1} q_k > N log N`. -/
def Persistent (N : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ k, qden a k ≤ N ∧ (N : ℝ) * Real.log N < ((a (k + 1) * qden a k : ℕ) : ℝ)

/-! ## The two analytic inputs -/

theorem log_lt_self (N : ℕ) (h : 1 ≤ N) : Real.log N < N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast h
  have := Real.log_le_sub_one_of_pos hN
  linarith

theorem one_lt_log_of_three_le (N : ℕ) (h : 3 ≤ N) : 1 < Real.log N := by
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have : Real.exp 1 < (N : ℝ) := lt_of_lt_of_le he h3
  exact (Real.lt_log_iff_exp_lt (by linarith)).mpr this

/-! ## The persistent cylinder `J₊ = (A/(A+1), 1)`, `A = N²` -/

/-- Every `θ` in `J₊` has `a₁ = 1` and `a₂ ≥ N²`, and that alone fires the criterion at `k = 1`.
The bound is a **positivity statement**, not an estimate: `N log N < N·N = N² ≤ a₂`. -/
theorem persistent_of_cylinder_plus (N : ℕ) (a : ℕ → ℕ) (hN : 1 ≤ N)
    (h1 : a 1 = 1) (h2 : N ^ 2 ≤ a 2) : Persistent N a := by
  have hq : qden a 1 = 1 := by rw [qden_one, h1]
  refine ⟨1, ?_, ?_⟩
  · rw [hq]; exact hN
  · rw [hq]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog : (N : ℝ) * Real.log N < (N : ℝ) * N :=
      mul_lt_mul_of_pos_left (log_lt_self N hN) hNR
    have h2' : ((N : ℝ)) * N ≤ ((a 2 : ℕ) : ℝ) := by
      have : ((N ^ 2 : ℕ) : ℝ) ≤ ((a 2 : ℕ) : ℝ) := by exact_mod_cast h2
      calc (N : ℝ) * N = ((N ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((a 2 : ℕ) : ℝ) := this
    have : ((a (1 + 1) * 1 : ℕ) : ℝ) = ((a 2 : ℕ) : ℝ) := by norm_num
    rw [this]
    linarith

/-! ## The non-persistent cylinder: an all-ones prefix long enough that `q_L > N` -/

/-- Every `θ` whose first `L` partial quotients are `1`, with `q_L > N`, fails the criterion at
**every** index. `N ≥ 3` is what makes `1 < log N`, and that is the whole of its role. -/
theorem not_persistent_of_all_ones (N L : ℕ) (a : ℕ → ℕ) (hN : 3 ≤ N)
    (hpos : ∀ j, 1 ≤ a j) (hones : ∀ j, 1 ≤ j → j ≤ L → a j = 1)
    (hL : N < qden a L) : ¬ Persistent N a := by
  rintro ⟨k, hk, hbig⟩
  have hkL : k < L := by
    by_contra hcon
    push Not at hcon
    have := qden_mono a hpos hcon
    omega
  have ha : a (k + 1) = 1 := hones (k + 1) (by omega) (by omega)
  rw [ha, one_mul] at hbig
  have hlog : 1 < Real.log N := one_lt_log_of_three_le N hN
  have hNR : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hgrow : (N : ℝ) < (N : ℝ) * Real.log N := by nlinarith
  have hkN : ((qden a k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  linarith

/-! ## The all-ones denominators are Fibonacci -/

theorem qden_all_ones (a : ℕ → ℕ) (hones : ∀ j, 1 ≤ j → a j = 1) (k : ℕ) :
    qden a k = Nat.fib (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rw [qden_one, hones 1 le_rfl]; rfl
  | more n ih1 ih2 =>
      -- `rw [Nat.fib_add_two]` would fire on the LEFT-hand `fib (n+2)` and leave the right
      -- alone; state the expansion of the side that is meant to move, and rewrite with that.
      have h : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
      rw [qden_succ_succ, hones (n + 2) (by omega), one_mul, ih2, ih1]
      change Nat.fib (n + 2) + Nat.fib (n + 1) = Nat.fib (n + 3)
      rw [h]; ring

/-- For `N = 3` the least admissible prefix length is `L = 4`: `q₃ = fib 4 = 3 ≤ 3` but
`q₄ = fib 5 = 5 > 3`. -/
theorem least_L_three : Nat.fib 4 ≤ 3 ∧ 3 < Nat.fib 5 := by decide

theorem fib_endpoints : Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 := by decide

/-- The cylinder's endpoints for `N = 3` are `u = p₄/q₄ = 3/5` and
`v = (p₄+p₃)/(q₄+q₃) = 5/8`, and the determinant that separates them is `±1`. -/
theorem endpoint_determinant : (3 : ℤ) * 3 - 2 * 5 = -1 := by decide

/-! ## Placing the two integer bases, without a floating-point logarithm -/

/-- `10^(p/q) < b` exactly when `10^p < b^q`. This is the bridge that gives the three integer
witnesses below their meaning. -/
theorem ten_rpow_lt_iff (b p q : ℕ) (hb : 1 ≤ b) (hq : 1 ≤ q) :
    (10 : ℝ) ^ ((p : ℝ) / (q : ℝ)) < (b : ℝ) ↔ (10 : ℕ) ^ p < b ^ q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [show ((10 : ℕ) ^ p < b ^ q) ↔ ((10 : ℝ) ^ p < (b : ℝ) ^ q) by exact_mod_cast Iff.rfl]
  rw [← Real.rpow_natCast (10 : ℝ) p, ← Real.rpow_natCast (b : ℝ) q]
  constructor
  · intro h
    have := Real.rpow_lt_rpow (by positivity) h hq0
    rwa [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (ne_of_gt hq0)] at this
  · intro h
    by_contra hcon
    push Not at hcon
    have := Real.rpow_le_rpow (by positivity) hcon hq0.le
    rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (ne_of_gt hq0)] at this
    linarith

/-- Base `9` lies in the persistent decade interval `(10^(9/10), 10)`. -/
theorem witness_nine : (10 : ℕ) ^ 9 < 9 ^ 10 ∧ (9 : ℕ) < 10 := by norm_num

/-- Base `4` lies in the non-persistent interval `(10^(3/5), 10^(5/8))`. -/
theorem witness_four : (10 : ℕ) ^ 3 < 4 ^ 5 ∧ (4 : ℕ) ^ 8 < 10 ^ 5 := by norm_num

/-! ## The bases with rational `log₁₀` are exactly the powers of ten

They therefore have density zero, which is why the source may include or exclude them
arbitrarily. -/

theorem factorization_ten_two : (10 : ℕ).factorization 2 = 1 := by
  have : (10 : ℕ) = 2 * 5 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 ∣ 5))]

/-- If `b^q = 10^p` with `p, q` coprime and `b ≥ 2`, then `q = 1` — so `b` is a power of ten. -/
theorem denominator_one_of_pow_eq (b p q : ℕ) (hb : 2 ≤ b)
    (h : b ^ q = 10 ^ p) (hcop : Nat.Coprime p q) : q = 1 := by
  have hb0 : b ≠ 0 := by omega
  have key : q * b.factorization 2 = p * (10 : ℕ).factorization 2 := by
    have h1 : (b ^ q).factorization 2 = q * b.factorization 2 := by
      rw [Nat.factorization_pow]; simp
    have h2 : ((10 : ℕ) ^ p).factorization 2 = p * (10 : ℕ).factorization 2 := by
      rw [Nat.factorization_pow]; simp
    rw [← h1, ← h2, h]
  rw [factorization_ten_two, mul_one] at key
  have hdvd : q ∣ p := ⟨b.factorization 2, key.symm⟩
  have := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
  exact this

end Principia.MathDB.P373701
