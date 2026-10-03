/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Principia.Common.Mertens.Mertens

/-!
# Chebyshev's 1852 lower bound `ψ(x) ≥ A x − O(log x)`, `A = 0.92129…`

Mathlib's `Chebyshev.psi_ge` has the constant `log 2 = 0.693…` (from the central binomial
coefficient). Chebyshev's own argument (1852) uses five factorials instead of three:

* **the floor identity.** `f(q) = q − ⌊q/2⌋ − ⌊q/3⌋ − ⌊q/5⌋ + ⌊q/30⌋` satisfies `f(q) ≤ 1`
  (`floorComb_le_one`; `f` has period `30`, so this is a check of thirty cases, done by `omega`);
* **Legendre.** `log m! = ∑_{d ≤ X} Λ(d) ⌊m/d⌋` for every `X ≥ m` (`log_factorial_eq_sum_of_le`,
  from the library's `Mertens.sum_log_eq_sum_mangoldt`). With `q = ⌊30n/d⌋` one has
  `⌊15n/d⌋ = ⌊q/2⌋`, `⌊10n/d⌋ = ⌊q/3⌋`, `⌊6n/d⌋ = ⌊q/5⌋`, `⌊n/d⌋ = ⌊q/30⌋`, so
  `log (30n)! + log n! − log (15n)! − log (10n)! − log (6n)! = ∑_{d ≤ 30n} Λ(d) f(q) ≤ ψ(30n)`
  (`chebyshev_comb_le_psi`);
* **Stirling.** Mathlib's `Stirling.le_log_factorial_stirling` bounds `log m!` below, and the
  monotonicity of the Stirling sequence (`stirlingSeq m ≤ stirlingSeq 1 = e/√2`) bounds it above:
  `log m! ≤ m log m − m + (log m)/2 + 1` (`log_factorial_le`). The `m log m` and `m` terms cancel
  in the combination and leave `30 n A`, where
  `30 A = 30 log 30 − 15 log 15 − 10 log 10 − 6 log 6 = log (2¹⁴ 3⁹ 5⁵)` (`chebyshev_comb_ge`).

Results: `psi_thirty_mul_ge` (`ψ(30n) ≥ 30nA − log(30n)/2 + log(2π) − 3` for `n ≥ 1`),
`psi_ge_chebyshev` (`ψ(x) ≥ A(x − 30) − (log x)/2 − 3` for real `x ≥ 30`), the `θ` version
`theta_ge_chebyshev`, and the numerical value `chebyshevA_gt : 0.9208 < A`, from
`(2¹⁴ 3⁹ 5⁵)⁷ ≥ (2³¹)⁹` (`chebyshevA_ge_log_two : (93/70) log 2 ≤ A`).

Nothing here mentions a campaign: it is the classical theorem, with explicit constants.
-/

set_option autoImplicit false

open Real Finset Chebyshev
open ArithmeticFunction hiding log
open scoped Nat

namespace Principia.Common.Chebyshev

/-! ## 1. The floor identity -/

/-- **Chebyshev's floor identity (upper half)**: `⌊q⌋ − ⌊q/2⌋ − ⌊q/3⌋ − ⌊q/5⌋ + ⌊q/30⌋ ≤ 1`,
written without subtraction. The left side has period `30` in `q`; `omega` checks it. -/
theorem floorComb_le_one (q : ℕ) : q + q / 30 ≤ q / 2 + q / 3 + q / 5 + 1 := by
  omega

/-- `⌊⌊k a / d⌋ / k⌋ = ⌊a / d⌋` for `k > 0`. -/
theorem mul_div_div_self (a k d : ℕ) (hk : 0 < k) : k * a / d / k = a / d := by
  rw [Nat.div_div_eq_div_mul, mul_comm d k, Nat.mul_div_mul_left a d hk]

/-! ## 2. Legendre's formula through `Λ` -/

/-- **Legendre's formula**: `log m! = ∑_{0 < d ≤ m} Λ(d) ⌊m/d⌋` (from the library's
`Mertens.sum_log_eq_sum_mangoldt` at `x = m`). -/
theorem log_factorial_eq_sum (m : ℕ) :
    Real.log (m ! : ℝ) = ∑ d ∈ Ioc 0 m, Λ d * ((m / d : ℕ) : ℝ) := by
  have h1 := Mertens.sum_log_eq_log_factorial (m : ℝ)
  have h2 := Mertens.sum_log_eq_sum_mangoldt (x := (m : ℝ))
  rw [Nat.floor_natCast] at h1 h2
  rw [← h1, h2]
  refine sum_congr rfl fun d _ => ?_
  rw [Nat.floor_div_eq_div]

/-- Legendre's formula over any longer range `0 < d ≤ X`, `X ≥ m` (the extra terms vanish). -/
theorem log_factorial_eq_sum_of_le (m X : ℕ) (h : m ≤ X) :
    Real.log (m ! : ℝ) = ∑ d ∈ Ioc 0 X, Λ d * ((m / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum, ← sum_Ioc_consecutive _ (Nat.zero_le m) h]
  have hz : ∑ d ∈ Ioc m X, Λ d * ((m / d : ℕ) : ℝ) = 0 := by
    refine sum_eq_zero fun d hd => ?_
    rw [Nat.div_eq_of_lt (mem_Ioc.mp hd).1]
    simp
  rw [hz, add_zero]

/-- **The combination is at most `ψ(30n)`**:
`log (30n)! + log n! − log (15n)! − log (10n)! − log (6n)! ≤ ψ(30n)`. -/
theorem chebyshev_comb_le_psi (n : ℕ) :
    Real.log ((30 * n) ! : ℝ) + Real.log (n ! : ℝ) - Real.log ((15 * n) ! : ℝ)
      - Real.log ((10 * n) ! : ℝ) - Real.log ((6 * n) ! : ℝ) ≤ ψ ((30 * n : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_of_le (30 * n) (30 * n) le_rfl,
    log_factorial_eq_sum_of_le n (30 * n) (by omega),
    log_factorial_eq_sum_of_le (15 * n) (30 * n) (by omega),
    log_factorial_eq_sum_of_le (10 * n) (30 * n) (by omega),
    log_factorial_eq_sum_of_le (6 * n) (30 * n) (by omega), Chebyshev.psi, Nat.floor_natCast,
    ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_le_sum fun d _ => ?_
  have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
  have h2 : 30 * n / d / 2 = 15 * n / d := by
    rw [show 30 * n = 2 * (15 * n) by ring, mul_div_div_self _ _ _ (by norm_num)]
  have h3 : 30 * n / d / 3 = 10 * n / d := by
    rw [show 30 * n = 3 * (10 * n) by ring, mul_div_div_self _ _ _ (by norm_num)]
  have h5 : 30 * n / d / 5 = 6 * n / d := by
    rw [show 30 * n = 5 * (6 * n) by ring, mul_div_div_self _ _ _ (by norm_num)]
  have h30 : 30 * n / d / 30 = n / d := mul_div_div_self _ _ _ (by norm_num)
  have key := floorComb_le_one (30 * n / d)
  rw [h2, h3, h5, h30] at key
  have keyR : ((30 * n / d : ℕ) : ℝ) + ((n / d : ℕ) : ℝ) ≤ ((15 * n / d : ℕ) : ℝ)
      + ((10 * n / d : ℕ) : ℝ) + ((6 * n / d : ℕ) : ℝ) + 1 := by
    exact_mod_cast key
  nlinarith [mul_le_mul_of_nonneg_left keyR hΛ]

/-! ## 3. Stirling -/

/-- **Upper Stirling bound**: `log m! ≤ m log m − m + (log m)/2 + 1` for `m ≥ 1`, because the
Stirling sequence `m!/(√(2m)(m/e)^m)` decreases from its value `e/√2` at `m = 1`. -/
theorem log_factorial_le (m : ℕ) (hm : m ≠ 0) :
    Real.log (m ! : ℝ) ≤ m * Real.log m - m + Real.log m / 2 + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  rw [Real.log_div (exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h
  have hf := Stirling.log_stirlingSeq_formula (k + 1)
  have hm0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) hm0.ne', Real.log_div hm0.ne' (exp_pos 1).ne',
    Real.log_exp] at hf
  nlinarith [hf, h]

/-! ## 4. Chebyshev's constant -/

/-- **Chebyshev's 1852 constant** `A = log (2¹⁴ 3⁹ 5⁵)/30
= (log 2)/2 + (log 3)/3 + (log 5)/5 − (log 30)/30 = 0.921292…`. -/
noncomputable def chebyshevA : ℝ := Real.log (2 ^ 14 * 3 ^ 9 * 5 ^ 5) / 30

theorem chebyshevA_eq :
    chebyshevA = (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30 := by
  rw [chebyshevA, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `A ≥ (93/70) log 2`, from `(2¹⁴ 3⁹ 5⁵)⁷ ≥ (2³¹)⁹ = 2²⁷⁹` (written as a power of `2³¹`:
the numeral evaluator refuses exponents above 256). -/
theorem chebyshevA_ge_log_two : 93 / 70 * Real.log 2 ≤ chebyshevA := by
  have h : Real.log (((2 : ℝ) ^ 31) ^ 9) ≤ Real.log (((2 : ℝ) ^ 14 * 3 ^ 9 * 5 ^ 5) ^ 7) :=
    Real.log_le_log (by positivity) (by norm_num)
  have hK : Real.log ((2 : ℝ) ^ 14 * 3 ^ 9 * 5 ^ 5) = 30 * chebyshevA := by
    rw [chebyshevA]; ring
  rw [Real.log_pow, Real.log_pow, Real.log_pow, hK] at h
  push_cast at h
  linarith

/-- **`A > 0.9208`** (the true value is `0.92129…`). -/
theorem chebyshevA_gt : (0.9208 : ℝ) < chebyshevA := by
  have := chebyshevA_ge_log_two
  have := Real.log_two_gt_d9
  linarith

theorem chebyshevA_pos : 0 < chebyshevA := lt_trans (by norm_num) chebyshevA_gt

/-- **The combination from below (Stirling)**: for `n ≥ 1`,
`log (30n)! + log n! − log (15n)! − log (10n)! − log (6n)! ≥ 30nA − log(30n)/2 + log(2π) − 3`. -/
theorem chebyshev_comb_ge (n : ℕ) (hn : n ≠ 0) :
    30 * n * chebyshevA - Real.log (30 * n) / 2 + Real.log (2 * π) - 3 ≤
      Real.log ((30 * n) ! : ℝ) + Real.log (n ! : ℝ) - Real.log ((15 * n) ! : ℝ)
        - Real.log ((10 * n) ! : ℝ) - Real.log ((6 * n) ! : ℝ) := by
  have h30 := Stirling.le_log_factorial_stirling (n := 30 * n) (by omega)
  have h1 := Stirling.le_log_factorial_stirling hn
  have h15 := log_factorial_le (15 * n) (by omega)
  have h10 := log_factorial_le (10 * n) (by omega)
  have h6 := log_factorial_le (6 * n) (by omega)
  push_cast at h30 h15 h10 h6
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Real.log_mul (by norm_num) hn0.ne'] at h30 h15 h10 h6 ⊢
  have l30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have l15 : Real.log (15 : ℝ) = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [l30] at h30 ⊢
  rw [l15] at h15
  rw [l10] at h10
  rw [l6] at h6
  rw [chebyshevA_eq]
  nlinarith [h30, h1, h15, h10, h6]

/-! ## 5. The lower bounds for `ψ` and `θ` -/

/-- **Chebyshev's lower bound at multiples of 30**: for `n ≥ 1`,
`ψ(30n) ≥ 30nA − log(30n)/2 + log(2π) − 3`. -/
theorem psi_thirty_mul_ge (n : ℕ) (hn : n ≠ 0) :
    30 * n * chebyshevA - Real.log (30 * n) / 2 + Real.log (2 * π) - 3 ≤ ψ (30 * n) := by
  have h := chebyshev_comb_le_psi n
  push_cast at h
  linarith [chebyshev_comb_ge n hn]

/-- **Chebyshev's lower bound (1852)**: `ψ(x) ≥ A (x − 30) − (log x)/2 − 3` for real `x ≥ 30`,
with `A = chebyshevA = 0.92129…`. -/
theorem psi_ge_chebyshev {x : ℝ} (hx : 30 ≤ x) :
    chebyshevA * (x - 30) - Real.log x / 2 - 3 ≤ ψ x := by
  have hx30 : 0 ≤ x / 30 := by positivity
  set n := ⌊x / 30⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)
  have hlow : 30 * (n : ℝ) ≤ x := by
    have := Nat.floor_le hx30
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have hup : x - 30 < 30 * (n : ℝ) := by
    have := Nat.lt_floor_add_one (x / 30)
    rw [div_lt_iff₀ (by norm_num)] at this
    linarith
  have hmain := psi_thirty_mul_ge n (by omega)
  have hmono : ψ (30 * n) ≤ ψ x := psi_mono hlow
  have hpos : (0 : ℝ) < 30 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hlog : Real.log (30 * n) ≤ Real.log x := Real.log_le_log hpos hlow
  have h2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [pi_gt_three])
  nlinarith [mul_le_mul_of_nonneg_left hup.le chebyshevA_pos.le]

/-- **The `θ` version**: `θ(x) ≥ A (x − 30) − (log x)/2 − 3 − 2√x log x` for `x ≥ 30`
(Mathlib's `Chebyshev.psi_sub_theta_le`). -/
theorem theta_ge_chebyshev {x : ℝ} (hx : 30 ≤ x) :
    chebyshevA * (x - 30) - Real.log x / 2 - 3 - 2 * √x * Real.log x ≤ θ x := by
  have h1 := psi_ge_chebyshev hx
  have h2 := psi_sub_theta_le (x := x) (by linarith)
  linarith

end Principia.Common.Chebyshev
