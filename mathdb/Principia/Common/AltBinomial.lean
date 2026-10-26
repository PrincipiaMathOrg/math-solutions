import Mathlib

/-!
# The alternating binomial sum annihilates low degree

`∑_{k ≤ n} (−1)^k C(n,k) P(k) = 0` whenever `deg P < n`.

Mathlib has the forward-difference operator `fwdDiff` and `fwdDiff_iter_eq_sum_shift`, which
expresses the `n`-th difference as exactly this alternating binomial sum — but not the fact that
the `n`-th difference annihilates polynomials of degree below `n`.  That gap is filled here.

The degree drop is realised as `taylor 1 P − P`: `taylor` preserves degree and leading
coefficient (`degree_taylor`, `leadingCoeff_taylor`), so the difference loses at least one
degree by `degree_sub_lt`.

Promoted out of the MathDB campaign (`Principia/MathDB/Problem336466.lean`), where it was built
to peel the two endpoints off a finite-difference identity.  It mentions nothing of that problem,
so it belongs here.
-/

namespace Principia.Common

open Finset Polynomial

variable {K : Type*} [Field K]

/-- One forward difference of a polynomial function is the polynomial function of
`taylor 1 P − P`. -/
theorem fwdDiff_poly (P : Polynomial K) :
    fwdDiff (1 : K) (fun z => P.eval z) = fun z => (taylor (1 : K) P - P).eval z := by
  funext z
  simp [fwdDiff, taylor_apply, Polynomial.eval_comp, add_comm]

/-- Shifting by one drops the degree of the difference, since `taylor` preserves both the degree
and the leading coefficient. -/
theorem natDegree_taylor_sub_lt (P : Polynomial K) (hP : 0 < P.natDegree) :
    (taylor (1 : K) P - P).natDegree < P.natDegree := by
  have hne : P ≠ 0 := fun h => by simp [h] at hP
  have htne : taylor (1 : K) P ≠ 0 := by rw [Ne, taylor_eq_zero]; exact hne
  have hlt : (taylor (1 : K) P - P).degree < (taylor (1 : K) P).degree :=
    degree_sub_lt (degree_taylor P 1) htne (leadingCoeff_taylor 1 P)
  rw [degree_taylor] at hlt
  by_cases hz : taylor (1 : K) P - P = 0
  · rw [hz]; simpa using hP
  · exact natDegree_lt_natDegree hz hlt

theorem fwdDiff_iter_zero_fun (k : ℕ) :
    (fwdDiff (1 : K))^[k] (fun _ => (0 : K)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have hz : fwdDiff (1 : K) (fun _ => (0 : K)) = fun _ => 0 := by funext z; simp [fwdDiff]
    rw [hz, ih]

/-- The `n`-th forward difference annihilates polynomials of degree below `n`. -/
theorem fwdDiff_iter_eq_zero : ∀ (n : ℕ) (P : Polynomial K), P.natDegree < n →
    (fwdDiff (1 : K))^[n] (fun z => P.eval z) = fun _ => 0 := by
  intro n
  induction n with
  | zero => intro P h; omega
  | succ k ih =>
    intro P hP
    rw [Function.iterate_succ_apply, fwdDiff_poly]
    by_cases hz : taylor (1 : K) P - P = 0
    · rw [hz]
      simpa using fwdDiff_iter_zero_fun (K := K) k
    · refine ih _ ?_
      rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
      · exfalso
        apply hz
        obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp h0
        simp [taylor_C]
      · have := natDegree_taylor_sub_lt P hpos
        omega

/-- **The alternating binomial sum annihilates low degree.** -/
theorem altBinom_eq_zero (P : Polynomial K) (n : ℕ) (hdeg : P.natDegree < n) :
    ∑ k ∈ range (n + 1), (-1 : K) ^ k * (n.choose k : K) * P.eval (k : K) = 0 := by
  have h0 := congrFun (fwdDiff_iter_eq_zero n P hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  have key : ∀ k ∈ range (n + 1),
      (((-1 : ℤ)) ^ (n - k) * (n.choose k : ℤ)) • (P.eval ((0 : K) + (k : ℕ) • (1 : K)))
        = (-1 : K) ^ n * ((-1 : K) ^ k * (n.choose k : K) * P.eval (k : K)) := by
    intro k hk
    rw [mem_range] at hk
    have hsq : ((-1 : K)) ^ k * (-1) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hprod : ((-1 : K)) ^ (n - k) * (-1) ^ k = (-1 : K) ^ n := by
      rw [← pow_add, show n - k + k = n from by omega]
    have hsign : ((-1 : K)) ^ (n - k) = (-1 : K) ^ n * (-1) ^ k := by
      calc ((-1 : K)) ^ (n - k)
          = ((-1 : K) ^ (n - k) * (-1) ^ k) * (-1) ^ k := by rw [mul_assoc, hsq, mul_one]
        _ = (-1 : K) ^ n * (-1) ^ k := by rw [hprod]
    have hz : (0 : K) + (k : ℕ) • (1 : K) = (k : K) := by simp
    rw [hz, zsmul_eq_mul]
    push_cast
    rw [hsign]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum] at h0
  have hne : ((-1 : K)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp h0).resolve_left hne

end Principia.Common
