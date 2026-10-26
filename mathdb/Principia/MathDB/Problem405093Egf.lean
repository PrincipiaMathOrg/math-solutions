import Principia.MathDB.Problem405093Paths

/-!
# MathDB #405093 — the exponential generating polynomial of the path counts

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, equation (3).  With
`E_a(t) = ∑_h comp(a, h) tʰ/h!` (the write-up's `t A_a(t)` for `a ≥ 1`), `egf_paths` proves that the
coefficient of `t^ℓ` in `E_a E_b` is `paths a b ℓ / ℓ!` — the product form of equation (2)
(`paths_eq`), using `C(h+v, v) h! v! = (h+v)!`.  The real-rootedness and log-concavity links are
the consumers.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

/-- `comp n k = 0` when there are more parts than units. -/
theorem comp_eq_zero_of_lt : ∀ k n : ℕ, n < k → comp n k = 0 := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n h
    rw [comp_succ]
    exact sum_eq_zero fun u hu => ih u (by rw [mem_range] at hu; omega)

/-- `E_a(t) = ∑_h comp(a, h) tʰ / h!`. -/
noncomputable def E (a : ℕ) : ℝ[X] :=
  ∑ h ∈ range (a + 1), C ((comp a h : ℝ) / (h.factorial : ℝ)) * X ^ h

theorem coeff_E (a h : ℕ) : (E a).coeff h = (comp a h : ℝ) / (h.factorial : ℝ) := by
  unfold E
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with hh
  · rfl
  · rw [mem_range, not_lt] at hh
    rw [comp_eq_zero_of_lt h a (by omega), Nat.cast_zero, zero_div]

/-- **Equation (3)**: `[t^ℓ] E_a E_b = paths a b ℓ / ℓ!`. -/
theorem egf_paths (a b l : ℕ) : (E a * E b).coeff l = (paths a b l : ℝ) / (l.factorial : ℝ) := by
  rw [coeff_mul, paths_eq, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [coeff_E, coeff_E]
  have hf := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  rw [← Nat.choose_symm_add, hp] at hf
  have h1 : (p.1.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (p.2.factorial : ℝ) ≠ 0 := by positivity
  have hc : (l.choose p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hfR : (l.factorial : ℝ) = (l.choose p.1 : ℝ) * p.1.factorial * p.2.factorial := by
    exact_mod_cast hf.symm
  rw [hfR]
  push_cast
  field_simp
  try ring

end Principia.MathDB.P405093
