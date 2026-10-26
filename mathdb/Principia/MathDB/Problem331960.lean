import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# MathDB #331960 — log-concavity of Sun's ratio sequence `rₙ = R_{n+1}/Rₙ` (Conjecture 4.7)

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/331960/solution.tex`, proving Conjecture 4.7 of Brian Yi Sun: with
`Rₙ = ∑_{k=0}^{n} C(n,k) C(n+k,k)/(2k − 1)` and `rₙ = R_{n+1}/Rₙ`, the sequence `{rₙ}_{n ≥ 4}` is
log-concave.

**Status of this file: part 1 of the build — the recurrence.**  The source derives
`(n+3)R_{n+3} − (7n+13)R_{n+2} + (7n+15)R_{n+1} − (n+1)Rₙ = 0` from a square-root generating
function.  Here it is proved directly from the binomial sum by a creative-telescoping certificate,
found with SymPy and checked exactly for `n < 25`, `k < 40`:
with `F(n,k) = C(n,k) C(n+k,k)/(2k − 1)` and `G(n,k) = −4k² C(n+3,k) C(n+k,k)/((n+1)(n+3))`,
`−(n+1)F(n,k) + (7n+15)F(n+1,k) − (7n+13)F(n+2,k) + (n+3)F(n+3,k) = G(n,k+1) − G(n,k)`,
and `G(n,0) = G(n,n+4) = 0`, so summing over `k` telescopes to the recurrence.  Every binomial in
the certificate is reduced to `C(n+3,k)` and `C(n+k,k)` through Mathlib's `choose_mul_succ_eq`,
`succ_mul_choose_eq` and `choose_succ_right_eq`.
-/

namespace Principia.MathDB.P331960

open Finset

/-- The summand `F(m,k) = C(m,k) C(m+k,k)/(2k − 1)`; it vanishes for `k > m`. -/
def F (m k : ℕ) : ℚ := (m.choose k : ℚ) * ((m + k).choose k : ℚ) * (2 * (k : ℚ) - 1)⁻¹

/-- Sun's `Rₙ = ∑_{k=0}^{n} C(n,k) C(n+k,k)/(2k − 1)`. -/
def R (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), F n k

/-- The telescoping certificate `G(n,k) = −4k² C(n+3,k) C(n+k,k)/((n+1)(n+3))`. -/
def G (n k : ℕ) : ℚ :=
  -4 * (k : ℚ) ^ 2 * ((n + 3).choose k : ℚ) * ((n + k).choose k : ℚ) /
    (((n : ℚ) + 1) * ((n : ℚ) + 3))

theorem R_ext (m : ℕ) : ∀ N, m + 1 ≤ N → R m = ∑ k ∈ range N, F m k := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ← ih, F, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- On the support of `C(a,k)`, `ℕ`-subtraction and `ℚ`-subtraction agree. -/
theorem cast_choose_sub (a k : ℕ) :
    (a.choose k : ℚ) * ((a : ℚ) - k) = (a.choose k : ℚ) * ((a - k : ℕ) : ℚ) := by
  by_cases h : k ≤ a
  · rw [Nat.cast_sub h]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `C(a,k)(a+1) = C(a+1,k)(a+1−k)`, over `ℚ`. -/
theorem rel_up (a k : ℕ) :
    (a.choose k : ℚ) * ((a : ℚ) + 1) = ((a + 1).choose k : ℚ) * ((a : ℚ) + 1 - k) := by
  have h := Nat.choose_mul_succ_eq a k
  have h' : ((a.choose k * (a + 1) : ℕ) : ℚ) = (((a + 1).choose k * (a + 1 - k) : ℕ) : ℚ) := by
    rw [h]
  have hs := cast_choose_sub (a + 1) k
  push_cast at h' hs
  rw [h', ← hs]

/-- `(a+1) C(a,k) = C(a+1,k+1)(k+1)`, over `ℚ`. -/
theorem rel_diag (a k : ℕ) :
    ((a : ℚ) + 1) * (a.choose k : ℚ) = ((a + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
  exact_mod_cast Nat.succ_mul_choose_eq a k

/-- `C(a,k+1)(k+1) = C(a,k)(a−k)`, over `ℚ`. -/
theorem rel_right (a k : ℕ) :
    (a.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (a.choose k : ℚ) * ((a : ℚ) - k) := by
  have h := Nat.choose_succ_right_eq a k
  have h' : ((a.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((a.choose k * (a - k) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  rw [h', cast_choose_sub]

theorem two_k_sub_one_ne (k : ℕ) : (2 * (k : ℚ) - 1) ≠ 0 := by
  intro h
  have h2 : (2 * k : ℚ) = 1 := by linarith
  have h3 : (2 * k : ℕ) = 1 := by exact_mod_cast h2
  omega

/-- **The certificate identity**, for every `n` and `k`. -/
theorem certificate (n k : ℕ) :
    -((n : ℚ) + 1) * F n k + (7 * (n : ℚ) + 15) * F (n + 1) k
      - (7 * (n : ℚ) + 13) * F (n + 2) k + ((n : ℚ) + 3) * F (n + 3) k = G n (k + 1) - G n k := by
  set N : ℚ := (n : ℚ) with hN
  set K : ℚ := (k : ℚ) with hK
  set A : ℚ := ((n + 3).choose k : ℚ) with hA
  set B : ℚ := ((n + k).choose k : ℚ) with hB
  -- the three shifts of the first binomial, down from `C(n+3,k)`
  have r3 : ((n + 2).choose k : ℚ) * (N + 3) = A * (N + 3 - K) := by
    have := rel_up (n + 2) k
    rw [show n + 2 + 1 = n + 3 from rfl] at this
    push_cast at this
    rw [hA, hN, hK]
    linear_combination this
  have r2 : ((n + 1).choose k : ℚ) * (N + 2) = ((n + 2).choose k : ℚ) * (N + 2 - K) := by
    have := rel_up (n + 1) k
    rw [show n + 1 + 1 = n + 2 from rfl] at this
    push_cast at this
    rw [hN, hK]
    linear_combination this
  have r1 : (n.choose k : ℚ) * (N + 1) = ((n + 1).choose k : ℚ) * (N + 1 - K) := by
    have := rel_up n k
    rw [hN, hK]
    linear_combination this
  -- the three shifts of the second binomial, up from `C(n+k,k)`
  have s1 : ((n + k + 1).choose k : ℚ) * (N + 1) = B * (N + K + 1) := by
    have := rel_up (n + k) k
    push_cast at this
    rw [hB, hN, hK]
    linear_combination -this
  have s2 : ((n + k + 2).choose k : ℚ) * (N + 2) = ((n + k + 1).choose k : ℚ) * (N + K + 2) := by
    have := rel_up (n + k + 1) k
    rw [show n + k + 1 + 1 = n + k + 2 from rfl] at this
    push_cast at this
    rw [hN, hK]
    linear_combination -this
  have s3 : ((n + k + 3).choose k : ℚ) * (N + 3) = ((n + k + 2).choose k : ℚ) * (N + K + 3) := by
    have := rel_up (n + k + 2) k
    rw [show n + k + 2 + 1 = n + k + 3 from rfl] at this
    push_cast at this
    rw [hN, hK]
    linear_combination -this
  -- the two binomials of `G(n,k+1)`
  have t1 : ((n + 3).choose (k + 1) : ℚ) * (K + 1) = A * (N + 3 - K) := by
    have := rel_right (n + 3) k
    push_cast at this
    rw [hA, hN, hK]
    linear_combination this
  have t2 : ((n + k + 1).choose (k + 1) : ℚ) * (K + 1) = (N + K + 1) * B := by
    have := rel_diag (n + k) k
    push_cast at this
    rw [hB, hN, hK]
    linear_combination -this
  have hN1 : N + 1 ≠ 0 := by positivity
  have hN2 : N + 2 ≠ 0 := by positivity
  have hN3 : N + 3 ≠ 0 := by positivity
  have hK1 : K + 1 ≠ 0 := by positivity
  have hk1 : 2 * K - 1 ≠ 0 := two_k_sub_one_ne k
  have hk2 : 2 * (K + 1) - 1 ≠ 0 := by
    have := two_k_sub_one_ne (k + 1)
    push_cast at this
    exact this
  have e3 : ((n + 2).choose k : ℚ) = A * (N + 3 - K) / (N + 3) := by
    rw [eq_div_iff hN3]; exact r3
  have e2 : ((n + 1).choose k : ℚ) = ((n + 2).choose k : ℚ) * (N + 2 - K) / (N + 2) := by
    rw [eq_div_iff hN2]; exact r2
  have e1 : (n.choose k : ℚ) = ((n + 1).choose k : ℚ) * (N + 1 - K) / (N + 1) := by
    rw [eq_div_iff hN1]; exact r1
  have f1 : ((n + k + 1).choose k : ℚ) = B * (N + K + 1) / (N + 1) := by
    rw [eq_div_iff hN1]; exact s1
  have f2 : ((n + k + 2).choose k : ℚ) = ((n + k + 1).choose k : ℚ) * (N + K + 2) / (N + 2) := by
    rw [eq_div_iff hN2]; exact s2
  have f3 : ((n + k + 3).choose k : ℚ) = ((n + k + 2).choose k : ℚ) * (N + K + 3) / (N + 3) := by
    rw [eq_div_iff hN3]; exact s3
  have g1 : ((n + 3).choose (k + 1) : ℚ) = A * (N + 3 - K) / (K + 1) := by
    rw [eq_div_iff hK1]; exact t1
  have g2 : ((n + k + 1).choose (k + 1) : ℚ) = (N + K + 1) * B / (K + 1) := by
    rw [eq_div_iff hK1]; exact t2
  simp only [F, G]
  rw [show n + 1 + k = n + k + 1 by omega, show n + 2 + k = n + k + 2 by omega,
    show n + 3 + k = n + k + 3 by omega, show n + (k + 1) = n + k + 1 by omega]
  push_cast
  rw [← hN, ← hK, ← hA, ← hB, e1, e2, e3, f3, f2, f1, g1, g2]
  field_simp
  -- `field_simp` clears every denominator except `(2K − 1)⁻¹`; what is left is `I·P = A·B·Q` with
  -- `P = Q·(2K − 1)` as polynomials (checked in SymPy), closed by `I·(2K − 1) = 1`.
  have hI : (2 * K - 1)⁻¹ * (2 * K - 1) = 1 := inv_mul_cancel₀ hk1
  linear_combination (A * B * (-24 - 44 * N - 8 * N * K + 8 * N * K ^ 2 - 24 * N ^ 2 - 4 * N ^ 3
    - 16 * K + 16 * K ^ 2)) * hI

/-- **The recurrence** `(n+3)R_{n+3} − (7n+13)R_{n+2} + (7n+15)R_{n+1} − (n+1)Rₙ = 0`. -/
theorem R_rec (n : ℕ) :
    ((n : ℚ) + 3) * R (n + 3) - (7 * (n : ℚ) + 13) * R (n + 2)
      + (7 * (n : ℚ) + 15) * R (n + 1) - ((n : ℚ) + 1) * R n = 0 := by
  rw [R_ext n (n + 4) (by omega), R_ext (n + 1) (n + 4) (by omega),
    R_ext (n + 2) (n + 4) (by omega), R_ext (n + 3) (n + 4) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hsum : ∑ k ∈ range (n + 4), (G n (k + 1) - G n k) = G n (n + 4) - G n 0 :=
    Finset.sum_range_sub (G n) (n + 4)
  have hG0 : G n 0 = 0 := by simp [G]
  have hGe : G n (n + 4) = 0 := by
    simp [G]
  rw [hG0, hGe, sub_zero] at hsum
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hsum
  linear_combination certificate n k

end Principia.MathDB.P331960
