import Mathlib

set_option autoImplicit false

/-!
# The iterated derivative of an analytic function is `n!` times its `n`-th coefficient

Every certificate-shaped MathDB row that refutes a conjecture by exhibiting one derivative of high
order meets the same wall: the certificate is produced by a COEFFICIENT RECURRENCE, and the
conjecture is stated about `iteratedDeriv`.  The two are joined by `f^(n)(x) = n! * a_n`, which the
campaign priced as missing from Mathlib.

**It is not missing; it is one rewrite away from `HasFPowerSeriesOnBall.factorial_smul`.**  That
lemma reads `n ! • p n (fun _ => y) = iteratedFDeriv k n f x (fun _ => y)`, for a series on a ball
in any normed space.  Specialising the domain to `k` itself and `y` to `1` turns the left side into
`FormalMultilinearSeries.coeff` (which is *defined* as `p n 1`) and the right side into
`iteratedDeriv` (`iteratedDeriv_eq_iteratedFDeriv`, which is `rfl`).  Nothing else is needed -- no
Cauchy product, no `HasFPowerSeriesAt` algebra, no completeness of the domain.

What a row must still supply is the power series itself: `HasFPowerSeriesAt f p x` with `p.coeff`
the recurrence's output.  That is a real obligation, and it is a different one.
-/

namespace Principia.Common

open scoped Nat

/-- **The bridge.**  For a function of one variable with a power series at `x`, the `n`-th iterated
derivative is `n!` times the `n`-th coefficient. -/
theorem iteratedDeriv_eq_factorial_smul_coeff {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜} (h : HasFPowerSeriesAt f p x) (n : ℕ) :
    iteratedDeriv n f x = Nat.factorial n • p.coeff n := by
  obtain ⟨r, hr⟩ := h
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hr.factorial_smul 1 n]
  rfl

/-- The real-valued form, with the `ℕ`-scalar action written as multiplication. -/
theorem iteratedDeriv_eq_factorial_mul_coeff {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x : ℝ} (h : HasFPowerSeriesAt f p x) (n : ℕ) :
    iteratedDeriv n f x = (Nat.factorial n : ℝ) * p.coeff n := by
  rw [iteratedDeriv_eq_factorial_smul_coeff h n, nsmul_eq_mul]

/-- **What a sign certificate actually needs.**  A negative coefficient is a negative derivative;
the factorial cannot flip it. -/
theorem iteratedDeriv_neg_of_coeff_neg {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ} {x : ℝ}
    (h : HasFPowerSeriesAt f p x) {n : ℕ} (hc : p.coeff n < 0) : iteratedDeriv n f x < 0 := by
  rw [iteratedDeriv_eq_factorial_mul_coeff h n]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.factorial_pos n) hc

end Principia.Common
