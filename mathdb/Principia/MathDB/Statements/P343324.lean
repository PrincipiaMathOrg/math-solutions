import Mathlib

/-!
# MathDB #343324 — statements only

This module carries the definitions the problem's statements mention, and the statements
themselves as `Prop`-valued constants. **It contains no proof.**

That is the whole point of separating it: `Challenge343324` imports this module and nothing
else, so Comparator never compiles the development's proofs while building the challenge.
`Solution343324` imports the development (`Principia.MathDB.Problem343324`) and discharges the
same constants. Because both sides name the *same* constants, defined here once, the comparison
is between the two proofs of one statement rather than between two statements.
-/

namespace Principia.MathDB.P343324

/-- `q_m(n) = ∑_{j<n} j·m`, the source's quantity. -/
def qm (m n : ℕ) : ℕ := ∑ j ∈ Finset.range n, j * m

/-- **The arithmetic core.** Oddness of `m` alone forces any `n` dividing `q_m(n)` to be odd.
Neither primality of `m` nor the greedy selection rule appears. -/
def ArithmeticCore : Prop :=
  ∀ m n : ℕ, Odd m → 0 < n → n ∣ qm m n → Odd n

/-- **MathDB #343324, Conjecture 3.1.** Every fixed point of the Navarrete–Orellana greedy
sequence is odd.

The only property of the greedy rule that appears is `a k ∣ q_p k`, and `p` is required only to
be odd, not prime — so this constant states something strictly stronger than the conjecture as
posed. -/
def Conjecture31 : Prop :=
  ∀ p : ℕ, Odd p → ∀ a : ℕ → ℕ, (∀ k, a k ∣ qm p k) →
    ∀ n : ℕ, 0 < n → a n = n → Odd n

end Principia.MathDB.P343324
