import Principia.MathDB.Problem405093Egf

/-!
# MathDB #405093 — the polynomials `A_a` and their three-term recurrence

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`.  For `a ≥ 1`,
`A_a(t) = ∑_{j<a} C(a−1, j) t^j/(j+1)!`, so that `E_a = t A_a` (`E_eq_X_mul_A`), `A_a(0) = 1`
(`eval_A_zero`), and the write-up's recurrence (5) holds (`A_rec`):

`(a+1) A_{a+1} = (2a + t) A_a − (a−1) A_{a−1}` (stated for `a = n + 2`).

Coefficientwise the recurrence is the integer identity
`(n+3) C(n+2, j) = 2(n+2) C(n+1, j) + (j+1) C(n+1, j−1) − (n+1) C(n, j)`, which after Pascal's rule
is `(k+1) C(n, k+1) = (n−k) C(n, k)` (`Nat.choose_succ_right_eq`).  All identities were checked in
SymPy for `a ≤ 11`.  The interlacing lemma is the consumer.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

/-- `A_a(t) = ∑_{j<a} C(a−1, j) t^j / (j+1)!`. -/
noncomputable def A (a : ℕ) : ℝ[X] :=
  ∑ j ∈ range a, C (((a - 1).choose j : ℝ) / ((j + 1).factorial : ℝ)) * X ^ j

theorem coeff_A (n j : ℕ) :
    (A (n + 1)).coeff j = (n.choose j : ℝ) / ((j + 1).factorial : ℝ) := by
  unfold A
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow, Nat.add_sub_cancel]
  rw [sum_ite_eq]
  split_ifs with hj
  · rfl
  · rw [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_div]

theorem eval_A_zero (n : ℕ) : (A (n + 1)).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_A]
  simp

/-- `comp (n+1) (h+1) = C(n, h)`. -/
theorem comp_closed : ∀ h n : ℕ, comp (n + 1) (h + 1) = n.choose h := by
  intro h
  induction h with
  | zero =>
    intro n
    rw [comp_succ, sum_range_succ', sum_eq_zero fun u _ => by simp [comp]]
    simp [comp]
  | succ h ih =>
    intro n
    induction n with
    | zero =>
      rw [comp_succ]
      simp [comp_succ, comp]
    | succ n ihn =>
      rw [comp_succ, sum_range_succ, ← comp_succ, ihn, ih, Nat.choose_succ_succ, add_comm]

/-- `E_a = t A_a` for `a ≥ 1`. -/
theorem E_eq_X_mul_A (n : ℕ) : E (n + 1) = X * A (n + 1) := by
  ext h
  rcases h with _ | h
  · rw [coeff_E, mul_coeff_zero, coeff_X_zero, zero_mul]
    simp [comp]
  · rw [coeff_E, coeff_X_mul, coeff_A, comp_closed]

/-- **The write-up's recurrence (5)** at `a = n + 2`. -/
theorem A_rec (n : ℕ) :
    C ((n : ℝ) + 3) * A (n + 1 + 1 + 1) = (C (2 * ((n : ℝ) + 2)) + X) * A (n + 1 + 1)
      - C ((n : ℝ) + 1) * A (n + 1) := by
  ext j
  rw [coeff_sub, add_mul, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_A, coeff_A,
    coeff_A]
  rcases j with _ | _ | k
  · simp only [coeff_X_mul_zero, Nat.choose_zero_right, zero_add, Nat.factorial_one]
    push_cast
    ring
  · rw [coeff_X_mul, coeff_A]
    simp only [zero_add, Nat.choose_one_right, Nat.choose_zero_right, Nat.factorial,
      Nat.succ_eq_add_one]
    push_cast
    ring
  · rw [coeff_X_mul, coeff_A]
    have hkey : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
      rcases le_or_gt k n with hkn | hkn
      · have h := Nat.choose_succ_right_eq n k
        rw [← Nat.cast_sub hkn]
        exact_mod_cast h
      · rw [Nat.choose_eq_zero_of_lt hkn, Nat.choose_eq_zero_of_lt (by omega)]
        simp
    have hint : ((n : ℝ) + 3) * ((n + 1 + 1).choose (k + 1 + 1) : ℝ)
        = 2 * ((n : ℝ) + 2) * ((n + 1).choose (k + 1 + 1) : ℝ)
          + ((k : ℝ) + 3) * ((n + 1).choose (k + 1) : ℝ)
          - ((n : ℝ) + 1) * (n.choose (k + 1 + 1) : ℝ) := by
      rw [Nat.choose_succ_succ (n + 1) (k + 1), Nat.choose_succ_succ n (k + 1),
        Nat.choose_succ_succ n k]
      push_cast
      linear_combination (-1 : ℝ) * hkey
    have hF : ((k + 1 + 1 + 1).factorial : ℝ) = ((k : ℝ) + 3) * ((k + 1 + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hFpos : ((k + 1 + 1).factorial : ℝ) ≠ 0 := by positivity
    have hk3 : (k : ℝ) + 3 ≠ 0 := by positivity
    rw [hF]
    generalize ((k + 1 + 1).factorial : ℝ) = F at hFpos ⊢
    generalize ((n + 1 + 1).choose (k + 1 + 1) : ℝ) = C3 at hint ⊢
    generalize ((n + 1).choose (k + 1 + 1) : ℝ) = C1 at hint ⊢
    generalize ((n + 1).choose (k + 1) : ℝ) = C2 at hint ⊢
    generalize (n.choose (k + 1 + 1) : ℝ) = C0 at hint ⊢
    rw [show 2 * ((n : ℝ) + 2) * (C1 / (((k : ℝ) + 3) * F)) + C2 / F
        - ((n : ℝ) + 1) * (C0 / (((k : ℝ) + 3) * F))
        = (2 * ((n : ℝ) + 2) * C1 + ((k : ℝ) + 3) * C2 - ((n : ℝ) + 1) * C0)
          / (((k : ℝ) + 3) * F) by field_simp <;> ring]
    rw [← hint]
    ring

end Principia.MathDB.P405093
