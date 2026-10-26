import Mathlib

set_option autoImplicit false

/-!
# Bounding a polynomial on an interval by its Bernstein coefficients

A recurring MathDB obligation is "this explicit polynomial has one sign on this interval".  The
obvious routes are a Lipschitz grid (many cells, each a `norm_num`) or Sturm theory (absent from
Mathlib).  The Bernstein basis does it in ONE step and with no analysis at all:

    sum_i C(n,i) (u-a)^i (b-u)^(n-i) = (b-a)^n                    (the binomial theorem)

so every term of a Bernstein expansion is nonnegative on `[a,b]`, the terms sum to `(b-a)^n`, and a
bound on the COEFFICIENTS is a bound on the polynomial.

**The form here is deliberately division-free.**  The textbook statement divides by `(b-a)^n` to
make the basis functions sum to `1`; carrying that division into Lean puts `(b-a)^n` in the
denominator of every certificate coefficient, which for a degree-12 certificate on an interval with
eight-digit endpoints means ~240-digit literals and a `ring` call over rational functions.  Keeping
`(b-a)^n` on the right instead leaves the coefficients as plain rationals and the identity a
polynomial one.

**A trap this form leaves for the consumer.**  `ring` treats the cast of `Nat.choose` as an
OPAQUE ATOM, so an identity mentioning the weights cannot be closed until every
`Nat.choose n i` has been reduced to a numeral.  Plain `norm_num` does NOT do that --
measured: `(Nat.choose 12 4 : ℝ) = 495` fails under `norm_num` and succeeds under
`norm_num [Nat.choose]`.  The failure surfaces as an unhelpful "ring failed" on a goal
thousands of characters wide, so it is worth stating here rather than rediscovering.

Nothing here mentions any campaign's objects; `u` ranges over an ordered field's interval and the
coefficients are arbitrary.
-/

namespace Principia.Common

open Finset

/-- **The Bernstein basis sums to `(b-a)^n`.**  This is the binomial theorem for `(u-a) + (b-u)`. -/
theorem bernstein_basis_sum (n : ℕ) (a b u : ℝ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i) = (b - a) ^ n := by
  have hsum : (u - a) + (b - u) = b - a := by ring
  have h := add_pow (u - a) (b - u) n
  rw [hsum] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Every Bernstein basis function is nonnegative on `[a,b]`. -/
theorem bernstein_basis_nonneg {a b u : ℝ} (hau : a ≤ u) (hub : u ≤ b) (n i : ℕ) :
    0 ≤ (n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i) := by
  have h1 : (0 : ℝ) ≤ (u - a) ^ i := pow_nonneg (by linarith) i
  have h2 : (0 : ℝ) ≤ (b - u) ^ (n - i) := pow_nonneg (by linarith) _
  have h3 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (mul_nonneg h3 h1) h2

/-- **Upper bound.**  A Bernstein expansion whose coefficients are all at most `M` is at most
`M * (b-a)^n` on `[a,b]`. -/
theorem bernstein_le {n : ℕ} (c : ℕ → ℝ) {a b u M : ℝ} (hau : a ≤ u) (hub : u ≤ b)
    (hc : ∀ i ∈ range (n + 1), c i ≤ M) :
    ∑ i ∈ range (n + 1), c i * ((n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i))
      ≤ M * (b - a) ^ n := by
  calc ∑ i ∈ range (n + 1), c i * ((n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i))
      ≤ ∑ i ∈ range (n + 1), M * ((n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i)) :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hc i hi) (bernstein_basis_nonneg hau hub n i)
    _ = M * (b - a) ^ n := by
        rw [← Finset.mul_sum, bernstein_basis_sum]

/-- **Lower bound.**  A Bernstein expansion whose coefficients are all at least `M` is at least
`M * (b-a)^n` on `[a,b]`. -/
theorem le_bernstein {n : ℕ} (c : ℕ → ℝ) {a b u M : ℝ} (hau : a ≤ u) (hub : u ≤ b)
    (hc : ∀ i ∈ range (n + 1), M ≤ c i) :
    M * (b - a) ^ n
      ≤ ∑ i ∈ range (n + 1), c i * ((n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i)) := by
  calc M * (b - a) ^ n
      = ∑ i ∈ range (n + 1), M * ((n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i)) := by
        rw [← Finset.mul_sum, bernstein_basis_sum]
    _ ≤ ∑ i ∈ range (n + 1), c i * ((n.choose i : ℝ) * (u - a) ^ i * (b - u) ^ (n - i)) :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hc i hi) (bernstein_basis_nonneg hau hub n i)

end Principia.Common
