import Mathlib

namespace Pntpp.DivisorPrefix

def divisorList (m : ℕ) : List ℕ :=
  (Nat.divisors m).sort (· ≤ ·)

def prefixDivisorSum (m k : ℕ) : ℕ :=
  ((divisorList m).take k).sum

def Represents (n : ℕ) : Prop :=
  ∃ m k : ℕ,
    0 < m ∧
    0 < k ∧
    k ≤ (divisorList m).length ∧
    prefixDivisorSum m k = n

abbrev TargetClassification : Prop :=
  ∀ n : ℕ, 0 < n → (Represents n ↔ n ≠ 2 ∧ n ≠ 5)

def HelfgottTailHypothesis : Prop :=
  ∀ N : ℕ,
    10 ^ 27 ≤ N →
    Odd N →
    ∃ p q r : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧
      Odd p ∧ Odd q ∧ Odd r ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      N = p + q + r ∧
      (N : ℝ) / (30000 * Real.log N) < (p : ℝ) ∧
      (N : ℝ) / (30000 * Real.log N) < (q : ℝ) ∧
      (N : ℝ) / (30000 * Real.log N) < (r : ℝ)

noncomputable def pi (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

/-- The two external prime-counting estimates used in the finite bridge.
These are explicit literature hypotheses, not project axioms. -/
class DusartBounds : Prop where
  lower : ∀ x : ℝ, 17 ≤ x → x / Real.log x ≤ pi x
  upper : ∀ x : ℝ, 1 < x → pi x ≤ 1.2551 * (x / Real.log x)

/-- Conditional formalization: the two prime-counting bounds and the explicit
Helfgott tail imply the divisor-prefix classification. -/
theorem erdos1054_conditional (dusart : DusartBounds) (helfgott : HelfgottTailHypothesis) :
    TargetClassification := by
  sorry

end Pntpp.DivisorPrefix
