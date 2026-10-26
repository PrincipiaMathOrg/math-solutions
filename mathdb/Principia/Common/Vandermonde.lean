import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Principia.Common

open Finset

/-!
# Vandermonde's identity as a `Finset.range` convolution

Mathlib's `Nat.add_choose_eq` states Vandermonde over `Finset.antidiagonal`.  The form a
convolution over a coefficient index actually meets is a sum over `Finset.range`, with one factor
reflected:

    `∑_{i ≤ j} C(N, j - i) · C(M, i) = C(N + M, j)`.

Converting is a reflection of the summation index, which is the kind of step worth doing once in a
shared file rather than inline at every use.
-/

/-- **Vandermonde, as a `range` convolution.** -/
theorem vandermonde_range (N M j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), N.choose (j - i) * M.choose i = (N + M).choose j := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_nbij' (fun i => j - i) (fun k => j - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    have h1 : j - (j - i) = i := by omega
    rw [h1]

end Principia.Common
