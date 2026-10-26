import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum.Prime

/-!
# MathDB #371655 — both Bernoulli–Toda denominator claims are false

Write-up: `mathdb-open-problems/problems/371655/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Conjecture 5.6 of the cited manuscript.

For even `N > 0`, von Staudt–Clausen gives the Bernoulli denominator
`D_N = ∏ {p prime : (p-1) ∣ N}`, and `F d` is the least positive even `N` with `D_N = d`.
The Toda primes are `T n = {p odd prime : (p-1) ∣ 4n and gcd (p, 4n/(p-1)) = 1}`.

Conjecture 5.6 has two clauses, for a Bernoulli denominator `d`:

* **(i)** if `F d = 4a` and `D_{4am} = D_{4a} = d`, then `T (a*m) = T a`;
* **(ii)** if `D_{4am} ≠ D_{4a} = d`, then `t (a*m) ≥ t a`.

## What is proved here

`not_clause1` refutes **(i)** outright, with the write-up's witness `a = 23`, `m = 47`,
`d = 1410`.  All four hypotheses are discharged, not assumed: `F 1410 = 92 = 4a`
(`isF_1410`, whose minimality is a decision over every smaller even index),
`D_{4324} = D_{92} = 1410`, and `0 < a`, `0 < m`.  Yet `T 1081 = {3,5}` while
`T 23 = {3,5,47}` — the prime `47` is lost.  Since Conjecture 5.6 asserts both clauses,
`not_conj` follows: **the conjecture is false.**

`Tset` is the source's own definition, gcd condition and all — the write-up's simplification
`T n = P(4n) \ ({2} ∪ primes(n))` is *not* used here, so nothing rests on that reduction.
(It is separately checked against the raw definition for all `n < 400` in
`Campaigns/MathDB-Formalization/verify_371655.py`.)

## What is NOT proved here

Clause **(ii)** is stated (`Clause2`) but not refuted in Lean.  The write-up's witness is
`a = 58`, `m = 13747`, needing `D` at `N = 3189304`; `Nat.divisors` at that size is a filter
over a range of three million, which the kernel will not do without `native_decide` — and
that is banned in this campaign.  The Python verifier confirms that half: `t(797326) = 3 <
4 = t(58)`.  Refuting clause (i) already falsifies the conjecture, so `not_conj` does not
depend on it.
-/

namespace Principia.MathDB.P371655

set_option maxRecDepth 100000

/-- `P N = {p prime : (p-1) ∣ N}`.  As `p - 1` divides `N`, it is one of `N`'s divisors. -/
def Pset (N : ℕ) : Finset ℕ := (N.divisors.image (· + 1)).filter (fun p => Nat.Prime p)

/-- The von Staudt–Clausen denominator `D_N = ∏ P(N)`. -/
def Dnum (N : ℕ) : ℕ := (Pset N).prod id

/-- The Toda primes, in the source's own form. -/
def Tset (n : ℕ) : Finset ℕ :=
  ((4*n).divisors.image (· + 1)).filter
    (fun p => 2 < p ∧ Nat.Prime p ∧ Nat.gcd p ((4*n) / (p - 1)) = 1)

/-- `IsF d N` : `N` is the least positive even index whose denominator is `d`. -/
def IsF (d N : ℕ) : Prop :=
  0 < N ∧ N % 2 = 0 ∧ Dnum N = d ∧
    ∀ M : ℕ, 0 < M → M % 2 = 0 → Dnum M = d → N ≤ M

/-- **Clause (i) of Conjecture 5.6.** -/
def Clause1 : Prop :=
  ∀ a m d : ℕ, 0 < a → 0 < m → IsF d (4*a) → Dnum (4*a*m) = d → Dnum (4*a) = d →
    Tset (a*m) = Tset a

/-- **Clause (ii) of Conjecture 5.6.**  Stated for completeness; not refuted here. -/
def Clause2 : Prop :=
  ∀ a m d : ℕ, 0 < a → 0 < m → Dnum (4*a) = d → Dnum (4*a*m) ≠ d →
    (Tset a).card ≤ (Tset (a*m)).card

/-- Conjecture 5.6 asserts both clauses. -/
def Conj56 : Prop := Clause1 ∧ Clause2

/-- No positive even index below `92` has denominator `1410`. -/
theorem no_smaller : ∀ M ∈ Finset.range 92, 0 < M → M % 2 = 0 → Dnum M ≠ 1410 := by decide

/-- `F 1410 = 92`, so the witness really does satisfy `F d = 4a`. -/
theorem isF_1410 : IsF 1410 92 := by
  refine ⟨by norm_num, by norm_num, by decide, ?_⟩
  intro M hM h2 hD
  by_contra h
  push_neg at h
  exact no_smaller M (Finset.mem_range.mpr h) hM h2 hD

theorem D_4324 : Dnum (4*23*47) = 1410 := by decide

theorem D_92 : Dnum (4*23) = 1410 := by decide

theorem T_23 : Tset 23 = {3, 5, 47} := by decide

theorem T_1081 : Tset (23*47) = {3, 5} := by decide

/-- **Clause (i) is FALSE.**  With `a = 23`, `m = 47`, `d = 1410` every hypothesis holds,
yet `T 1081 = {3,5}` loses the prime `47` present in `T 23 = {3,5,47}`. -/
theorem not_clause1 : ¬ Clause1 := by
  intro h
  have := h 23 47 1410 (by norm_num) (by norm_num) isF_1410 D_4324 D_92
  rw [T_23, T_1081] at this
  exact absurd this (by decide)

/-- **Conjecture 5.6 is FALSE**, since it asserts clause (i). -/
theorem not_conj : ¬ Conj56 := fun h => not_clause1 h.1

end Principia.MathDB.P371655
