/-
  Comparator bridge — standalone almost-all Goldbach master.

  Certifies only statement (B). Delegates to
  `GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven` in
  `masters/GoldbachChainMaster.lean`.

  NOTE ON STRUCTURE. As with the other bridges this file does **not**
  `import Challenge` — comparator compares two independently elaborated
  environments, and importing the challenge would be an "already been declared"
  error. The three definitions its statement depends on are reproduced VERBATIM
  from `Challenge.lean`, so the delegation holds by definitional equality.

  Built as `Solution` by the assemble script; compared via
  `comparator/config/goldbach.json`.
-/

import Mathlib
import Master

namespace Erdos1054Challenge

open Finset

/-! ### Definitions used by statement (B) (verbatim from `Challenge.lean`) -/

/-- `countUpTo P X` — number of `n ≤ X` satisfying `P`. -/
noncomputable def countUpTo (P : Nat → Prop) (X : Nat) : Nat := by
  classical
  exact ((Finset.range (X + 1)).filter P).card

/-- The exceptional set of `P` has density zero. -/
def DensityZero (P : Nat → Prop) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ X₀ : Nat, ∀ X : Nat, X ≥ X₀ → (countUpTo P X : Rat) ≤ ε * X

/-- `n` is even and is NOT a sum of two primes. -/
def notSumOfTwoPrimes (n : Nat) : Prop :=
  Even n ∧ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-! ### (B) Almost-all binary Goldbach — the heavy circle-method input -/

theorem almost_all_binary_goldbach : DensityZero notSumOfTwoPrimes :=
  GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven

end Erdos1054Challenge
