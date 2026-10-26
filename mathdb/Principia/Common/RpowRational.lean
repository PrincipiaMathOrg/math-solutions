import Mathlib

set_option autoImplicit false

/-!
# A rational-exponent comparison reduces to an integer-power comparison

`a ^ (m/n) < b` and `a ^ m < b ^ n` say the same thing for nonnegative `a`, `b` and `n > 0`, and the
second is decidable by `norm_num` when `a` and `b` are rational.  Every MathDB certificate that
bounds a quantity raised to a fractional power wants exactly this step, and Mathlib states it only
through the `rpow`/`pow` interface lemmas, which have to be assembled each time.

The proofs are one `by_contra` each, on the identity `(a ^ (m/n)) ^ n = a ^ m`.
-/

namespace Principia.Common

/-- The power identity the two comparisons rest on. -/
theorem rpow_div_pow {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hn : 0 < n) :
    (a ^ ((m : ℝ) / (n : ℝ))) ^ n = a ^ m := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hexp : (m : ℝ) / (n : ℝ) * (n : ℝ) = (m : ℝ) := by field_simp
  rw [← Real.rpow_natCast (a ^ ((m : ℝ) / (n : ℝ))) n, ← Real.rpow_mul ha, hexp,
    Real.rpow_natCast]

/-- **Upper bound.**  `a ^ m < b ^ n` gives `a ^ (m/n) < b`. -/
theorem rpow_div_lt_of_pow_lt_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {m n : ℕ} (hn : 0 < n)
    (h : a ^ m < b ^ n) : a ^ ((m : ℝ) / (n : ℝ)) < b := by
  by_contra hcon
  rw [not_lt] at hcon
  have := pow_le_pow_left₀ hb hcon n
  rw [rpow_div_pow ha hn] at this
  linarith

/-- **Lower bound.**  `b ^ n < a ^ m` gives `b < a ^ (m/n)`. -/
theorem lt_rpow_div_of_pow_lt_pow {a b : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hn : 0 < n)
    (h : b ^ n < a ^ m) : b < a ^ ((m : ℝ) / (n : ℝ)) := by
  by_contra hcon
  rw [not_lt] at hcon
  have hnn : (0 : ℝ) ≤ a ^ ((m : ℝ) / (n : ℝ)) := Real.rpow_nonneg ha _
  have := pow_le_pow_left₀ hnn hcon n
  rw [rpow_div_pow ha hn] at this
  linarith

end Principia.Common
