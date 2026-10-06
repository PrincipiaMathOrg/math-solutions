/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/KernelNumerics.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.KernelNumerics

set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option maxHeartbeats 4000000

theorem exp_nat_upper (n : ℕ) : Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
  simpa only [← Real.exp_nat_mul, mul_one] using h

theorem exp_nat_lower (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le n
  simpa only [← Real.exp_nat_mul, mul_one] using h

theorem log_lower_of_power (n k a : ℕ) (hk : 0 < k) (ha : 0 < a)
    (h : (2.7182818286 : ℝ) ^ n ≤ (a : ℝ) ^ k) :
    (n : ℝ) / k ≤ Real.log a := by
  have hb := (exp_nat_upper n).trans h
  have hcast : (0 : ℝ) < a := by exact_mod_cast ha
  rw [← Real.exp_log hcast, ← Real.exp_nat_mul] at hb
  have he := Real.exp_le_exp.mp hb
  exact (div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).mpr (by nlinarith)

theorem log_upper_of_power (n k a : ℕ) (hk : 0 < k) (ha : 0 < a)
    (h : (a : ℝ) ^ k ≤ (2.7182818283 : ℝ) ^ n) :
    Real.log a ≤ (n : ℝ) / k := by
  have hb := h.trans (exp_nat_lower n)
  have hcast : (0 : ℝ) < a := by exact_mod_cast ha
  rw [← Real.exp_log hcast, ← Real.exp_nat_mul] at hb
  have he := Real.exp_le_exp.mp hb
  exact (le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).mpr (by nlinarith)

theorem exp31_upper : Real.exp 31 ≤ (10 ^ 27 : ℝ) :=
  (exp_nat_upper 31).trans (by norm_num)

theorem exp60_upper : Real.exp 60 ≤ (10 ^ 27 : ℝ) :=
  (exp_nat_upper 60).trans (by norm_num)

theorem exp63_lower : (1000000000000000000100000000 : ℝ) < Real.exp 63 :=
  lt_of_lt_of_le (by norm_num) (exp_nat_lower 63)

theorem exp31_ratio : (30000 : ℝ) ≤ Real.exp 31 / (31 : ℝ) ^ 6 := by
  apply (le_div_iff₀ (by positivity)).mpr
  exact le_trans (by norm_num) (exp_nat_lower 31)

end Pntpp.DivisorPrefix.KernelNumerics
