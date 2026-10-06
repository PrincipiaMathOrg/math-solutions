/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Statement.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000

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

end Pntpp.DivisorPrefix
