/-
  Erdős Problem 1054 — human-readable comparator statement file
  ==============================================================

  This file is the *specification* half of the `comparator` setup requested by
  T. Tao (email, 16 Jul 2026): a short, self-contained, human-auditable file
  stating exactly what the machine-verified masters prove, so that `comparator`
  can certify that the full proofs in `masters/` establish *these* statements and
  nothing weaker — using no axioms beyond Lean's three foundations
  `[propext, Quot.sound, Classical.choice]`.

  Every definition below is reproduced VERBATIM (identical bodies) from the
  master files, so the statements elaborate to the same terms the masters prove:
    • `Represented`, `f`, `countUpTo`, `PositiveLowerDensity`  — from
      `masters/Erdos1054_3rdMomentProof.lean` (namespace `Erdos1054`, ~L35100).
    • `notSumOfTwoPrimes`, `DensityZero`                       — from
      `masters/GoldbachChainMaster.lean` (namespace `GoldbachChain.GoldbachReduction`, ~L31134).

  Per Tao's suggestion, the results are SPLIT by logical dependency:

    (A) Main result — UNCONDITIONAL, light formalization relative to (B):
        for every A ≥ 1, the represented N with f(N) > A·N have positive lower
        density. Stated with the convention f(N) = sInf{…} so it does not
        presuppose that f(N) is finite.

    (B) Almost-all binary Goldbach — the heavy circle-method theorem, the only
        part requiring a substantial formal effort. Proven separately in
        `GoldbachChainMaster.lean` and consumed by (A).

  The dependency is: (A) is proven in the Erdős masters with (B) discharged
  internally against the proven Goldbach theorem, so BOTH stand on Lean's
  foundations alone. See `comparator/README.md` for how each `config/*.json`
  points `comparator` at the corresponding master.

  `sorry` here marks "proven elsewhere (in the master), to be certified by
  comparator" — it is NOT an admitted gap in the mathematics.
-/

import Mathlib

namespace Erdos1054Challenge

open Finset

/-! ### Shared definitions (verbatim from the masters) -/

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

/-- **Erdős 1054, main theorem.** For every fixed `A ≥ 1`, the represented
    integers `N` with `f(N) > A·N` have positive lower density. In particular
    `f(N)/N` is unbounded on the represented integers.

    Proven in `masters/Erdos1054_3rdMomentProof.lean` as
    `Erdos1054.erdos1054_third_moment_full_proof`
    (and in `Erdos1054_2ndMomentProof.lean` as `…_second_moment_full_proof`),
    axioms `[propext, Classical.choice, Quot.sound]`.

    QUANTIFIER NOTE (read this before judging faithfulness). The paper's
    Theorem 1 quantifies over *real* `A ≥ 1`; this statement quantifies over
    `A : Nat`. The two are equivalent in strength: given a real `A ≥ 1`, apply
    this theorem to `⌈A⌉ : Nat`, and `A * N ≤ ⌈A⌉ * N` gives the real form.
    The Nat form is the one formalized because it avoids a cast layer in the
    density bookkeeping; `Erdos1054Conditional.lean` states the real form
    directly (`Represented.main`, `A : ℝ`). -/
theorem erdos1054_main (A : Nat) (hA : 1 ≤ A) :
    PositiveLowerDensity (fun N => Represented N ∧ A * N < f N) := by
  sorry

/-- Corollary: for every `A ≥ 1` there is a represented `N` with `f(N) > A·N`. -/
theorem erdos1054_ratio_unbounded (A : Nat) (hA : 1 ≤ A) :
    ∃ N, Represented N ∧ A * N < f N := by
  sorry

/-! ### (B) Almost-all binary Goldbach — the heavy circle-method input -/

/-- **Almost-all binary Goldbach.** The even numbers that are not a sum of two
    primes form a set of density zero.

    Proven in `masters/GoldbachChainMaster.lean` as
    `GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven`,
    axioms `[propext, Classical.choice, Quot.sound]`. Consumed by (A) inside the
    Erdős masters, where it is discharged against this proof rather than assumed. -/
theorem almost_all_binary_goldbach : DensityZero notSumOfTwoPrimes := by
  sorry

end Erdos1054Challenge
