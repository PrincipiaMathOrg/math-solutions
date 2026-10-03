/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Chebyshev.Lower
import Principia.Common.Chebyshev.PrimeSum

set_option autoImplicit false

/-!
# The numerical core of `Step_FraitureLargePrimeSum`

`10^27 + 10^8 < ∑_{4·10^7 < p ≤ 3.99·10^14, p prime} p`, from Chebyshev's 1852 lower constant
(`Principia.Common.Chebyshev`), with no citation. `N = 3.99·10^14 = 30 n`, `n = 1.33·10^13`:

* `log N · ∑_{p ≤ N} p ≥ N θ(N) − log 4 · N(N − 1)/2` — discrete Abel summation and Mathlib's
  `θ(x) ≤ x log 4` (`Principia.Common.Chebyshev.sum_primes_ge`);
* `θ(N) ≥ ψ(N) − 2√N log N` (Mathlib's `Chebyshev.psi_sub_theta_le`), `√N ≤ 2·10^7`;
* `ψ(30n) ≥ 30 n A − log(30n)/2 + log(2π) − 3` with Chebyshev's constant `A = 0.92129…`
  (`Principia.Common.Chebyshev.psi_thirty_mul_ge`), and `A ≥ (93/70) log 2`
  (`chebyshevA_ge_log_two`);
* `log N ≤ 49 log 2` (`N ≤ 2^49`) and `log 2 > 0.6931471803` (Mathlib's `Real.log_two_gt_d9`).

Together: `∑_{p ≤ N} p ≥ ((93/70 − 1) N² − O(10^9 N)) / 49 ≥ 1.067·10^27`
(`sum_primes_le_upper_gt`); the primes `≤ 4·10^7` are removed at a cost of at most `(4·10^7)²`
(`Principia.Common.Chebyshev.sum_primes_le_sq_add`). The margin over `10^27 + 10^8` is `6.7%`.
Mathlib's own lower constant `log 2` in place of `A` would leave a main term of `0`: Chebyshev's
constant is what the step needs.

**Kernel hygiene.** Every prime sum over a concrete range is generalized to a variable before
any arithmetic tactic runs, or is reached only through lemmas stated for variable endpoints
(`lt_sum_primes_Ioc_of_lt`, `lt_sum_of_cast_lt`). A first version did the `ℕ` bookkeeping on the
concrete sums in one tactic block (`rw [add_comm …] at h`, `lt_of_lt_of_le`, then
`Nat.lt_of_add_lt_add_right`): it elaborated in seconds, each step checked instantly on its own,
but the kernel check of the combined term ran past 8 GB (a heartbeat cap did not stop it;
`debug.skipKernelTC` did), i.e. the kernel began evaluating a prime sum.
-/

open Real Finset Chebyshev

namespace Principia.Erdos1054.Alt6.Dusart

open Principia.Common.Chebyshev

/-- **The primes up to `3.99·10^14` sum to more than `10^27 + 10^8 + (4·10^7)²`** (over `ℝ`). -/
theorem sum_primes_le_upper_gt :
    ((10 ^ 27 + 10 ^ 8 + 40000000 * 40000000 : ℕ) : ℝ)
      < ∑ p ∈ (Ioc 0 399000000000000).filter Nat.Prime, (p : ℝ) := by
  have hsum := sum_primes_ge 399000000000000
  -- the prime sum becomes an uninterpreted real: nothing below may try to evaluate it
  generalize (∑ p ∈ (Ioc 0 399000000000000).filter Nat.Prime, (p : ℝ)) = S at hsum ⊢
  have eT : ((10 ^ 27 + 10 ^ 8 + 40000000 * 40000000 : ℕ) : ℝ)
      = (10 : ℝ) ^ 27 + 10 ^ 8 + 40000000 * 40000000 := by push_cast; ring
  rw [eT]
  have hpsi := psi_thirty_mul_ge 13300000000000 (by norm_num)
  have hdiff := Chebyshev.psi_sub_theta_le (x := (399000000000000 : ℝ)) (by norm_num)
  have hA := chebyshevA_ge_log_two
  have hl := Real.log_two_gt_d9
  have e1 : ((399000000000000 : ℕ) : ℝ) = 399000000000000 := by norm_num
  have e2 : (30 : ℝ) * ((13300000000000 : ℕ) : ℝ) = 399000000000000 := by norm_num
  rw [e1] at hsum
  rw [e2] at hpsi
  have hu_le : Real.log 399000000000000 ≤ 49 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num) (by norm_num :
      (399000000000000 : ℝ) ≤ 2 ^ 49)
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hu_pos : 0 < Real.log 399000000000000 := Real.log_pos (by norm_num)
  have hsqrt : √(399000000000000 : ℝ) ≤ 20000000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsq_u : √(399000000000000 : ℝ) * Real.log 399000000000000
      ≤ 20000000 * Real.log 399000000000000 :=
    mul_le_mul_of_nonneg_right hsqrt hu_pos.le
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hlog4] at hsum
  by_contra hcon
  have hcon' : S ≤ (10 : ℝ) ^ 27 + 10 ^ 8 + 40000000 * 40000000 := not_lt.mp hcon
  have huS : Real.log 399000000000000 * S
      ≤ Real.log 399000000000000 * ((10 : ℝ) ^ 27 + 10 ^ 8 + 40000000 * 40000000) :=
    mul_le_mul_of_nonneg_left hcon' hu_pos.le
  linarith

/-- **`10^27 + 10^8 < ∑_{4·10^7 < p ≤ 3.99·10^14, p prime} p`**, with no hypothesis: one
instantiation of the variable-endpoint lemmas `lt_sum_primes_Ioc_of_lt` and `lt_sum_of_cast_lt`. -/
theorem sum_primes_Ioc_gt :
    10 ^ 27 + 10 ^ 8 < ∑ p ∈ (Ioc 40000000 399000000000000).filter Nat.Prime, p :=
  lt_sum_primes_Ioc_of_lt (10 ^ 27 + 10 ^ 8) 40000000 399000000000000 (by norm_num)
    (lt_sum_of_cast_lt _ _ sum_primes_le_upper_gt)

end Principia.Erdos1054.Alt6.Dusart
