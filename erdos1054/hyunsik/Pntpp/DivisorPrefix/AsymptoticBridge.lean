import Mathlib

namespace Pntpp.DivisorPrefix

/-- The number of primes at most a real bound. -/
noncomputable def pi (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

/-- The two external prime-counting estimates used in the finite bridge.
These are explicit literature hypotheses, not project axioms. -/
class DusartBounds : Prop where
  lower : ∀ x : ℝ, 17 ≤ x → x / Real.log x ≤ pi x
  upper : ∀ x : ℝ, 1 < x → pi x ≤ 1.2551 * (x / Real.log x)

theorem pnt_explicit_prime_count_lower [DusartBounds] {x : ℝ} (hx : 17 ≤ x) :
    x / Real.log x ≤ pi x := DusartBounds.lower x hx

theorem pnt_explicit_prime_count_upper [DusartBounds] {x : ℝ} (hx : 1 < x) :
    pi x ≤ 1.2551 * (x / Real.log x) := DusartBounds.upper x hx

theorem pnt_explicit_prime_count_interval_lower [DusartBounds] {a b : ℝ}
    (ha : 17 ≤ a) (hb : 17 ≤ b) :
    b / Real.log b - 1.2551 * (a / Real.log a) ≤ pi b - pi a := by
  linarith [pnt_explicit_prime_count_lower hb,
    pnt_explicit_prime_count_upper (by linarith : 1 < a)]

end Pntpp.DivisorPrefix
