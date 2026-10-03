/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Sums of primes from `θ`: discrete Abel summation

For an integer `N ≥ 0`, summation by parts over the integers gives the exact identity

  `∑_{p ≤ N} p log p = N θ(N) − ∑_{k < N} θ(k)`   (`sum_prime_mul_log_eq`),

so Mathlib's `θ(k) ≤ k log 4` yields `∑_{p ≤ N} p log p ≥ N θ(N) − log 4 · N(N−1)/2`, and since
`log p ≤ log N`,

  `log N · ∑_{p ≤ N} p ≥ N θ(N) − log 4 · N(N−1)/2`   (`sum_primes_ge`).

With Chebyshev's lower constant `A = 0.92129…` for `θ(N)` (`Principia.Common.Chebyshev.Lower`)
this gives `∑_{p ≤ N} p ≥ (A − log 2 − o(1)) N²/log N`, where `A − log 2 = 0.228 > 0`.
(Mathlib's own lower constant `log 2` in place of `A` would leave a main term of `0`.)

Nothing here mentions a campaign.
-/

set_option autoImplicit false

open Real Finset Chebyshev

namespace Principia.Common.Chebyshev

/-- `θ(N)` at an integer, as a sum over `0 < p ≤ N` with the primality test inside. -/
theorem theta_natCast_eq (N : ℕ) :
    θ (N : ℝ) = ∑ p ∈ Ioc 0 N, if p.Prime then Real.log (p : ℝ) else 0 := by
  rw [Chebyshev.theta, Nat.floor_natCast, sum_filter]

/-- **Discrete Abel summation for `∑ p log p`**:
`∑_{0 < p ≤ N, p prime} p log p + ∑_{k < N} θ(k) = N θ(N)`. -/
theorem sum_prime_mul_log_add_sum_theta (N : ℕ) :
    ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ) * Real.log p
      + ∑ k ∈ range N, θ (k : ℝ) = N * θ (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hθ : θ ((N + 1 : ℕ) : ℝ) =
        θ (N : ℝ) + if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) else 0 := by
      rw [theta_natCast_eq, theta_natCast_eq, sum_Ioc_succ_top (Nat.zero_le N)]
    rw [sum_filter] at ih ⊢
    rw [sum_Ioc_succ_top (Nat.zero_le N), sum_range_succ, hθ]
    split_ifs with hp
    · push_cast
      linear_combination ih
    · push_cast
      linear_combination ih

/-- The exact form: `∑_{p ≤ N} p log p = N θ(N) − ∑_{k < N} θ(k)`. -/
theorem sum_prime_mul_log_eq (N : ℕ) :
    ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ) * Real.log p
      = N * θ (N : ℝ) - ∑ k ∈ range N, θ (k : ℝ) := by
  linarith [sum_prime_mul_log_add_sum_theta N]

/-- `∑_{k < N} k = N (N − 1)/2`, over `ℝ`. -/
theorem sum_range_natCast (N : ℕ) : ∑ k ∈ range N, (k : ℝ) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- `∑_{k < N} θ(k) ≤ log 4 · N(N − 1)/2` (Mathlib's `θ(x) ≤ x log 4`). -/
theorem sum_range_theta_le (N : ℕ) :
    ∑ k ∈ range N, θ (k : ℝ) ≤ Real.log 4 * ((N : ℝ) * (N - 1) / 2) := by
  calc ∑ k ∈ range N, θ (k : ℝ) ≤ ∑ k ∈ range N, Real.log 4 * (k : ℝ) :=
        sum_le_sum fun k _ => theta_le_log4_mul_x (Nat.cast_nonneg k)
    _ = Real.log 4 * ((N : ℝ) * (N - 1) / 2) := by rw [← mul_sum, sum_range_natCast]

/-- `∑_{p ≤ N} p log p ≥ N θ(N) − log 4 · N(N − 1)/2`. -/
theorem sum_prime_mul_log_ge (N : ℕ) :
    (N : ℝ) * θ (N : ℝ) - Real.log 4 * ((N : ℝ) * (N - 1) / 2)
      ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ) * Real.log p := by
  linarith [sum_prime_mul_log_add_sum_theta N, sum_range_theta_le N]

/-- `∑_{p ≤ N} p log p ≤ log N · ∑_{p ≤ N} p`. -/
theorem sum_prime_mul_log_le (N : ℕ) :
    ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ) * Real.log p
      ≤ Real.log N * ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ) := by
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  have hp' := mem_Ioc.mp (mem_filter.mp hp).1
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp'.1
  have h2 : (p : ℝ) ≤ N := by exact_mod_cast hp'.2
  rw [mul_comm (Real.log N)]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log h1 h2) h1.le

/-- **Sum of the primes up to `N` from `θ(N)`**:
`N θ(N) − log 4 · N(N − 1)/2 ≤ log N · ∑_{0 < p ≤ N, p prime} p`. -/
theorem sum_primes_ge (N : ℕ) :
    (N : ℝ) * θ (N : ℝ) - Real.log 4 * ((N : ℝ) * (N - 1) / 2)
      ≤ Real.log N * ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ) :=
  (sum_prime_mul_log_ge N).trans (sum_prime_mul_log_le N)

/-- **Cutting off the primes `≤ M` costs at most `M²`**: for `M ≤ N`,
`∑_{0 < p ≤ N} p ≤ M² + ∑_{M < p ≤ N} p`. (Stated for variables `M, N`, so that no tactic ever
meets two different concrete prime sums and tries to decide their equality by evaluation.) -/
theorem sum_primes_le_sq_add (M N : ℕ) (h : M ≤ N) :
    ∑ p ∈ (Ioc 0 N).filter Nat.Prime, p ≤ M * M + ∑ p ∈ (Ioc M N).filter Nat.Prime, p := by
  rw [sum_filter, sum_filter, ← sum_Ioc_consecutive _ (Nat.zero_le M) h]
  refine Nat.add_le_add_right ?_ _
  calc ∑ p ∈ Ioc 0 M, (if p.Prime then p else 0) ≤ ∑ _p ∈ Ioc 0 M, M :=
        sum_le_sum fun p hp => by
          split_ifs
          · exact (mem_Ioc.mp hp).2
          · exact Nat.zero_le _
    _ = M * M := by rw [sum_const, Nat.card_Ioc, smul_eq_mul, Nat.sub_zero]

/-- **From `(0, N]` to `(M, N]`**: `A + M² < ∑_{0 < p ≤ N} p` gives `A < ∑_{M < p ≤ N} p`.

Stated for variables so that a concrete use is one instantiation: the kernel then never compares
arithmetic on a concrete prime sum with anything, which it would decide by evaluating the sum. -/
theorem lt_sum_primes_Ioc_of_lt (A M N : ℕ) (hMN : M ≤ N)
    (h : A + M * M < ∑ p ∈ (Ioc 0 N).filter Nat.Prime, p) :
    A < ∑ p ∈ (Ioc M N).filter Nat.Prime, p := by
  have h1 := sum_primes_le_sq_add M N hMN
  generalize M * M = K at h h1
  generalize ∑ p ∈ (Ioc 0 N).filter Nat.Prime, p = S at h h1
  generalize ∑ p ∈ (Ioc M N).filter Nat.Prime, p = T at h1 ⊢
  omega

/-- **Cast transfer for sums**: `(A : ℝ) < ∑_{p ∈ s} (p : ℝ)` gives `A < ∑_{p ∈ s} p` in `ℕ`. -/
theorem lt_sum_of_cast_lt (A : ℕ) (s : Finset ℕ) (h : (A : ℝ) < ∑ p ∈ s, (p : ℝ)) :
    A < ∑ p ∈ s, p := by
  rw [← Nat.cast_sum] at h
  exact_mod_cast h

end Principia.Common.Chebyshev
