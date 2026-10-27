import Mathlib

set_option autoImplicit false

namespace Principia.MathDB.P370786

open Finset

/-! ### `G_t(x)`, written as a geometric sum rather than a quotient

The write-up sets `G_t(x) = (x^t − 1)/(x − 1)`.  Written as `∑_{i<t} x^i` it is the same object with
no division, and Mathlib's `geom_sum_mul` supplies the defining identity directly. -/

/-- `G t x = ∑_{i<t} x^i`. -/
def G (t : ℕ) (x : ℤ) : ℤ := ∑ i ∈ range t, x ^ i

theorem G_mul_sub_one (t : ℕ) (x : ℤ) : G t x * (x - 1) = x ^ t - 1 := by
  unfold G; exact geom_sum_mul x t

theorem G_zero (x : ℤ) : G 0 x = 0 := by simp [G]

theorem G_one (x : ℤ) : G 1 x = 1 := by simp [G]

theorem G_succ (t : ℕ) (x : ℤ) : G (t + 1) x = G t x + x ^ t := by
  unfold G; rw [Finset.sum_range_succ]

/-! ### The totient sum the write-up computes by hand IS Mathlib's `Nat.sum_totient`

The write-up evaluates `∑_{j=B}^{b} φ(q^{b−j}) = ∑_{t=0}^{v} φ(q^t) = q^v` by telescoping.  That is
the classical `∑_{d ∣ n} φ(d) = n` at `n = q^v`, whose divisors are exactly the
`q^t` for `t ≤ v`. -/

theorem totient_prime_pow_sum {q : ℕ} (hq : q.Prime) (v : ℕ) :
    ∑ t ∈ range (v + 1), Nat.totient (q ^ t) = q ^ v := by
  rw [← Nat.sum_totient (q ^ v), Nat.divisors_prime_pow hq, Finset.sum_map]
  rfl

/-! ### The conjecture, stated

`H_r = h*(−r)`, the class number of `ℚ(√−r)` for a prime `r ≡ 3 (mod 4)`, with `H_3 = 1/3`; the
Legendre symbols enter as `legendreSym`, which Mathlib has.  Both are carried as parameters here,
because the identification of `H` through Dirichlet's finite class-number formula
`(1/r)∑_{x<r} x·χ_r(x) = −H_r` is what **the source itself cites rather than
proves** (CD Theorem 4.1
and Corollary 4.3), and Mathlib has only the analytic class-number formula, not this finite one. -/

/-- **Chamberland–Dilcher Conjecture 7.2**, Equation (7.2).  `S` is the quadratic remainder sum at
`n = p^a q^b`; `H p` and `H q` are the class numbers; `lpq` and `lqp` are the two Legendre
symbols. -/
def Conjecture72 (S : ℕ → ℕ → ℚ) (H : ℕ → ℚ) (lpq lqp : ℤ) : Prop :=
  ∀ p q a b : ℕ, p.Prime → q.Prime → p % 4 = 3 → q % 4 = 3 → p ≠ q → 0 < a → 0 < b →
    S a b =
      ((p ^ a * q ^ b : ℚ) - (p ^ (a / 2) * q ^ (b / 2) : ℚ)) / 2
        - ((G ((a + 1) / 2) p * (G (b / 2 + 1) q + lpq * G (b / 2) q) : ℤ) : ℚ) * H p
        - ((G ((b + 1) / 2) q * (G (a / 2 + 1) p + lqp * G (a / 2) p) : ℤ) : ℚ) * H q

end Principia.MathDB.P370786
