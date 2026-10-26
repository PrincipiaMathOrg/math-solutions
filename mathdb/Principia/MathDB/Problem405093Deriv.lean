import Principia.MathDB.Problem405093Newton

/-!
# MathDB #405093 — Newton's inequalities for the coefficients of a real-rooted polynomial

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, Lemma "newton": if
`F(t) = ∑ c_ℓ t^ℓ/ℓ!` has nonnegative coefficients and only real zeros, then
`c_ℓ² ≥ ((D−ℓ+1)/(D−ℓ)) c_{ℓ−1} c_{ℓ+1}`.

`newton_coeffs` proves it in the form `(D−k) c_{k+2} c_k ≤ (D−k−1) c_{k+1}²`, `c_i = i! [tⁱ] F`, as
in the write-up: `R = F^{(k)}` is again real-rooted (Rolle, `card_roots_le_derivative`,
`real_rooted_iterate`), its zeros are nonpositive because its coefficients are nonnegative
(`roots_nonpos`), and `newton_splits` applies to its first three coefficients, which are
`c_k`, `c_{k+1}` and `c_{k+2}/2` (`coeff_iterate_derivative`).  The lattice-path theorem is the
consumer.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

theorem real_rooted_derivative (p : ℝ[X]) (hp : Multiset.card p.roots = p.natDegree) :
    Multiset.card (derivative p).roots = (derivative p).natDegree := by
  have h1 := card_roots_le_derivative p
  have h2 := card_roots' (derivative p)
  rw [natDegree_derivative] at h2 ⊢
  omega

theorem real_rooted_iterate (p : ℝ[X]) (hp : Multiset.card p.roots = p.natDegree) :
    ∀ k, Multiset.card (derivative^[k] p).roots = (derivative^[k] p).natDegree := by
  intro k
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact real_rooted_derivative _ ih

theorem natDegree_iterate_eq (p : ℝ[X]) : ∀ k, (derivative^[k] p).natDegree = p.natDegree - k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', natDegree_derivative, ih]
    omega

/-- A nonzero real polynomial with nonnegative coefficients has no positive zeros. -/
theorem roots_nonpos (p : ℝ[X]) (hp : p ≠ 0) (hc : ∀ i, 0 ≤ p.coeff i) :
    ∀ r ∈ p.roots, r ≤ 0 := by
  intro r hr
  by_contra h
  rw [not_le] at h
  have hroot : p.eval r = 0 := (mem_roots hp).1 hr
  rw [eval_eq_sum_range] at hroot
  have hlead : 0 < p.coeff p.natDegree :=
    lt_of_le_of_ne (hc _) (leadingCoeff_ne_zero.2 hp).symm
  have hterm : p.coeff p.natDegree * r ^ p.natDegree
      ≤ ∑ i ∈ range (p.natDegree + 1), p.coeff i * r ^ i :=
    single_le_sum (f := fun i => p.coeff i * r ^ i)
      (fun i _ => mul_nonneg (hc i) (pow_nonneg h.le i)) (mem_range.2 (by omega))
  have := mul_pos hlead (pow_pos h p.natDegree)
  linarith

/-- **Newton's inequalities** for the scaled coefficients `c_i = i! [tⁱ] F`. -/
theorem newton_coeffs (F : ℝ[X]) (hF : Multiset.card F.roots = F.natDegree)
    (hc : ∀ i, 0 ≤ F.coeff i) (k : ℕ) (hk : k + 2 ≤ F.natDegree) :
    ((F.natDegree : ℝ) - k) * (((k + 2).factorial : ℝ) * F.coeff (k + 2)
        * ((k.factorial : ℝ) * F.coeff k))
      ≤ ((F.natDegree : ℝ) - k - 1) * (((k + 1).factorial : ℝ) * F.coeff (k + 1)) ^ 2 := by
  have hR := real_rooted_iterate F hF k
  have hdeg := natDegree_iterate_eq F k
  have hRne : derivative^[k] F ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hRc : ∀ i, 0 ≤ (derivative^[k] F).coeff i := by
    intro i
    rw [coeff_iterate_derivative, nsmul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (hc _)
  have hN := newton_splits _ hR (roots_nonpos _ hRne hRc)
  have c0 : (derivative^[k] F).coeff 0 = (k.factorial : ℝ) * F.coeff k := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, zero_add, Nat.descFactorial_self]
  have c1 : (derivative^[k] F).coeff 1 = ((k + 1).factorial : ℝ) * F.coeff (k + 1) := by
    rw [coeff_iterate_derivative, nsmul_eq_mul]
    have h := Nat.factorial_mul_descFactorial (show k ≤ 1 + k by omega)
    rw [show 1 + k - k = 1 by omega, Nat.factorial_one, one_mul, show 1 + k = k + 1 by ring] at h
    rw [show 1 + k = k + 1 by ring, h]
  have c2 : 2 * (derivative^[k] F).coeff 2 = ((k + 2).factorial : ℝ) * F.coeff (k + 2) := by
    rw [coeff_iterate_derivative, nsmul_eq_mul]
    have h := Nat.factorial_mul_descFactorial (show k ≤ 2 + k by omega)
    rw [show 2 + k - k = 2 by omega, show 2 + k = k + 2 by ring] at h
    rw [show 2 + k = k + 2 by ring, ← mul_assoc, ← h]
    push_cast
    simp [Nat.factorial]
  rw [c2, c0, c1, hdeg] at hN
  push_cast [Nat.cast_sub (show k ≤ F.natDegree by omega)] at hN
  linarith

end Principia.MathDB.P405093
