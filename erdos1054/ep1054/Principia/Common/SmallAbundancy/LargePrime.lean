/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-!
# Large primes contribute nothing to the colossally-abundant bound

In the comparison of `Principia.Common.SmallAbundancy.Criterion` a prime `p` that does not divide
`M` (exponent `0`) needs `W(p^k) ≤ W(1) = 1`, i.e. `σ(p^k)^N ≤ p^{k(N+1)}`, for every `k`. By
`compare_of_tail` (with `e = 0`, `A = 1`) that follows from the single inequality
`p^N ≤ (p − 1)^N p`, i.e. `(1 + 1/(p − 1))^N ≤ p`, proved here uniformly for all
`p ≥ P₀ + 1` once `N ≤ (11/2) P₀` and `P₀ ≥ 244`:
`(1 + 1/q)^N ≤ e^{N/q} ≤ e^{11/2} < 245 ≤ p` (`q = p − 1 ≥ P₀`).

* `exp_eleven_half_lt` — `e^{11/2} < 245` (from `e < 2.7182818286`: `e^{11} < 60025 = 245²`).
* `pow_le_pred_pow_mul` — `p^N ≤ (p − 1)^N p` for `p ≥ P₀ + 1`.
-/

namespace Principia.Common.SmallAbundancy

/-- `e^{11/2} < 245` (true value `244.69…`). -/
theorem exp_eleven_half_lt : Real.exp (11 / 2) < 245 := by
  have h2 : Real.exp (11 / 2) ^ 2 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have h11 : Real.exp 1 ^ 11 < (2.7182818286 : ℝ) ^ 11 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  have hsq : Real.exp (11 / 2) ^ 2 < (245 : ℝ) ^ 2 := by
    rw [h2]
    calc Real.exp 1 ^ 11 < (2.7182818286 : ℝ) ^ 11 := h11
      _ < 245 ^ 2 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

/-- **`(p/(p − 1))^N ≤ p` for every `p > P₀`**, when `2N ≤ 11 P₀` and `P₀ ≥ 244`, in the cleared
form `p^N ≤ (p − 1)^N p`. -/
theorem pow_le_pred_pow_mul {N P0 p : ℕ} (hN : 2 * N ≤ 11 * P0) (hP0 : 244 ≤ P0)
    (hp : P0 + 1 ≤ p) : p ^ N ≤ (p - 1) ^ N * p := by
  have hq0 : 0 < p - 1 := by omega
  have hq : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hq0
  have hpq : (p : ℝ) = ((p - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have h1 : 1 + 1 / ((p - 1 : ℕ) : ℝ) ≤ Real.exp (1 / ((p - 1 : ℕ) : ℝ)) := by
    linarith [Real.add_one_le_exp (1 / ((p - 1 : ℕ) : ℝ))]
  have h2 : (1 + 1 / ((p - 1 : ℕ) : ℝ)) ^ N ≤ Real.exp ((N : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
    calc (1 + 1 / ((p - 1 : ℕ) : ℝ)) ^ N ≤ Real.exp (1 / ((p - 1 : ℕ) : ℝ)) ^ N :=
          pow_le_pow_left₀ (by positivity) h1 N
      _ = Real.exp ((N : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have h3 : (N : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 11 / 2 := by
    rw [div_le_iff₀ hq]
    have hP : (P0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show P0 ≤ p - 1 by omega)
    have hN' : (2 * N : ℝ) ≤ 11 * P0 := by exact_mod_cast hN
    linarith
  have h4 : Real.exp ((N : ℝ) / ((p - 1 : ℕ) : ℝ)) < 245 :=
    lt_of_le_of_lt (Real.exp_le_exp.2 h3) exp_eleven_half_lt
  have h5 : (245 : ℝ) ≤ p := by exact_mod_cast (show 245 ≤ p by omega)
  have key : (p : ℝ) ^ N ≤ ((p - 1 : ℕ) : ℝ) ^ N * p := by
    have e : (p : ℝ) ^ N = ((p - 1 : ℕ) : ℝ) ^ N * (1 + 1 / ((p - 1 : ℕ) : ℝ)) ^ N := by
      rw [← mul_pow]
      congr 1
      rw [hpq]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact_mod_cast key

end Principia.Common.SmallAbundancy
