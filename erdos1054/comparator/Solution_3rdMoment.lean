/-
  Comparator bridge — third-moment master.

  Proves each `Challenge.lean` statement by delegating to the fully verified
  theorem in `masters/Erdos1054_3rdMomentProof.lean`.

  NOTE ON STRUCTURE. This file deliberately does **not** `import Challenge`.
  Comparator compares two *independently elaborated* environments: it builds
  `Challenge` and `Solution` in separate sandboxes, exports both, and checks
  that the declarations used in the statements of the listed theorems agree.
  A solution that imported the challenge would (a) fail to compile, since
  re-declaring `Erdos1054Challenge.erdos1054_main` in a namespace where the
  imported one already exists is an "already been declared" error, and
  (b) defeat the point of the comparison. So the definitions below are
  reproduced VERBATIM from `Challenge.lean` — byte-identical bodies — and the
  theorems are then discharged against the master.

  The delegation holds by definitional equality: each `Erdos1054Challenge`
  definition has a body identical to its `Erdos1054` counterpart in the master,
  so the Challenge proposition and the master's conclusion are the same term up
  to unfolding.

  The assemble script (`scripts/assemble-workspace.sh`) copies the master into
  the PNT+ checkout as module `Master`, then builds this file as `Solution` so
  `comparator/config/3rdMoment.json` can compare `Challenge` against `Solution`.
-/

import Mathlib
import Master

namespace Erdos1054Challenge

open Finset

/-! ### Shared definitions (verbatim from `Challenge.lean`) -/

/-- `F e d` — the partial sum of the divisors of `e*d` that are `≤ d`. -/
noncomputable def F (e d : Nat) : Nat :=
  ((e * d).divisors.filter (fun q => q ≤ d)).sum (fun q => q)

/-- `m` realises `N` as a prefix-sum-of-divisors value with cofactor split `e*d = m`. -/
def IsRep (m N : Nat) : Prop := ∃ e d, 0 < e ∧ 0 < d ∧ m = e * d ∧ N = F e d

/-- `N` is *represented*: `N = F e d` for some positive `e, d`. -/
def Represented (N : Nat) : Prop := ∃ e d, 0 < e ∧ 0 < d ∧ N = F e d

/-- `f N` — the least modulus realising `N`; `sInf ∅ = 0` when `N` is not
    represented, so no finiteness is presupposed. -/
noncomputable def f (N : Nat) : Nat := sInf {m | 0 < m ∧ IsRep m N}

/-- `countUpTo P X` — number of `n ≤ X` satisfying `P`. -/
noncomputable def countUpTo (P : Nat → Prop) (X : Nat) : Nat := by
  classical
  exact ((Finset.range (X + 1)).filter P).card

/-- Lower density of `P` is bounded below by a positive constant. -/
def PositiveLowerDensity (P : Nat → Prop) : Prop :=
  ∃ c : Rat, 0 < c ∧ ∃ X₀ : Nat, ∀ X : Nat, X ≥ X₀ → c * X ≤ (countUpTo P X : Rat)

/-- The exceptional set of `P` has density zero. -/
def DensityZero (P : Nat → Prop) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ X₀ : Nat, ∀ X : Nat, X ≥ X₀ → (countUpTo P X : Rat) ≤ ε * X

/-- `n` is even and is NOT a sum of two primes. -/
def notSumOfTwoPrimes (n : Nat) : Prop :=
  Even n ∧ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-! ### (A) Main result — unconditional -/

theorem erdos1054_main (A : Nat) (hA : 1 ≤ A) :
    PositiveLowerDensity (fun N => Represented N ∧ A * N < f N) :=
  Erdos1054.erdos1054_third_moment_full_proof A hA

theorem erdos1054_ratio_unbounded (A : Nat) (hA : 1 ≤ A) :
    ∃ N, Represented N ∧ A * N < f N :=
  Erdos1054.erdos1054_ratio_unbounded A hA

/-! ### (B) Almost-all binary Goldbach -/

theorem almost_all_binary_goldbach : DensityZero notSumOfTwoPrimes :=
  Erdos1054.almost_all_binary_goldbach

end Erdos1054Challenge
