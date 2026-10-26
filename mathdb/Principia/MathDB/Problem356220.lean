import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# MathDB 356220 — the proposed inverse of a shifted Lambert factorization is wrong

Write-up: `mathdb-open-problems/problems/356220/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "An odd-divisor inverse for a
shifted Lambert factorization".  It refutes **Conjecture 2.26** of M. D. Schmidt's 2022
Georgia Tech thesis (p. 31, arXiv:2209.12287), repeated as equation (5) of Remark 2.7 in
Merca–Schmidt, arXiv:1712.00611.  The conjecture proposes a closed form for the entries
of `S⁻¹`, where `S` is the coefficient matrix of the factorization
`∑ f(k)qᵏ/(1-q^{2k+1}) = (q;q)_∞⁻¹ ∑∑ s_{n,k} f(k) qⁿ`.

## The refutation, and why it is stronger here than in the write-up

The write-up refutes the conjecture at `(n,k) = (58,1)` by arithmetic: the true entry is
`613767`, the proposed formula gives `613766`.  Those two numbers are built from four
partition values (`p 57 = 614154`, `p 18 = 385`, `p 5 = 7`, `p 3 = 3`).

**That presentation understates the result.**  Expanding both sides symbolically in `p`:

* corrected: `p 57 - p 18 - p 3 + p 0`
* proposed : `p 57 - (p 18 + p 5 + p 3 + p 0) + (p 5 + p 0)` `= p 57 - p 18 - p 3`

the `p 5` and `p 0` of the negative sum are **cancelled** by the double sum, and the two
formulas differ by **exactly `p 0`**.  So `discrepancy` below says

        corrected p 58 1 - proposed p 58 1 = p 0

for an ARBITRARY `p : ℕ → ℕ` satisfying only the hypotheses the index sets actually need.
`p 57`, `p 18` and `p 3` never appear in it.  This matters for a mechanical check: Mathlib
has no theory of integer partitions at all, so a formalisation that had to assert
`p 57 = 614154` would be asserting an unverifiable number, and a typo in it could not be
caught by anything.  A statement that never mentions `p 57` cannot be broken by mistyping
it.

## What is carried, and what is proved

* **Carried**: that `corrected` really is the inverse (the write-up's Theorem 1, a Möbius
  inversion over odd divisors).  It enters `not_conj` as the hypothesis `htrue`.
* **Carried**: `p 1 … p 7` and `Monotone p`.  These are needed, but ONLY inside the index
  *conditions* of the double sum, never as values of the answer.  `Monotone p` is what
  kills every `m ≥ 6`: there `p (m+1) ≥ 15` and `p (m-1) ≥ 7`, so the numerator is at most
  `58 - 15 - 7 = 36` while the modulus is at least `45`, and the quotient is `≤ 0`.
* **Proved**: everything else — both index sets, the cancellation, and the discrepancy.

## Faithfulness (the 215 check)

The source's summation conditions are **Iverson brackets on congruences**, not on
non-negative divisibility, so they also fire when the numerator is negative; `negTerm` and
`posTerm` render them as `ℕ` congruences (`n % D = … % D`) and take the quotient in `ℤ`,
where `/` is floor division.  `Campaigns/MathDB-Formalization/verify_356220.py` checks
that reading against the non-negative one and confirms the supports agree: the negative
sum fires at `i = 1,4,6,19,58` (the last with index `-1`, contributing nothing) and the
double sum only at `m = 2`, `i = 1,6,19` (likewise).  It also re-runs the whole expansion
with `p` scrambled above index 7 and confirms the difference is still `p 0`.

Indices are kept in `ℤ` throughout: in `ℕ` the index `(58-58)/117 - 1` would truncate
`-1` to `0` and silently contribute `p 0 = 1`, which is precisely the size of the
discrepancy being proved.
-/

namespace Principia.MathDB.P356220

open Finset
open ArithmeticFunction (moebius moebius_apply_prime moebius_apply_prime_pow
  isMultiplicative_moebius)

/-! ## Möbius values at the divisors of `117 = 3² · 13` -/

theorem mu_three : moebius 3 = -1 := moebius_apply_prime (by norm_num)

theorem mu_thirteen : moebius 13 = -1 := moebius_apply_prime (by norm_num)

theorem mu_nine : moebius 9 = 0 := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
    moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

theorem mu_thirtynine : moebius 39 = 1 := by
  rw [show (39 : ℕ) = 3 * 13 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), mu_three, mu_thirteen]
  norm_num

theorem mu_onehundredseventeen : moebius 117 = 0 := by
  rw [show (117 : ℕ) = 9 * 13 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), mu_nine]
  norm_num

/-! ## The partition function extended by zero -/

/-- `pv p z` is `p z`, extended by `0` to negative `z` — the source's convention that
`p j = 0` for `j < 0`.  The argument is an `ℤ` on purpose. -/
def pv (p : ℕ → ℕ) (z : ℤ) : ℤ := if 0 ≤ z then (p z.toNat : ℤ) else 0

theorem pv_of_neg (p : ℕ → ℕ) {z : ℤ} (h : z < 0) : pv p z = 0 := by
  simp [pv, not_le.mpr h]

/-! ## The two formulas, as printed -/

/-- One term of the subtracted sum of Conjecture 2.26: the Iverson bracket is the
congruence `n ≡ i (mod 2i+1)`. -/
def negTerm (p : ℕ → ℕ) (n k i : ℕ) : ℤ :=
  if n % (2 * i + 1) = i % (2 * i + 1) then
    pv p (((n : ℤ) - i) / (2 * (i : ℤ) + 1) - k)
  else 0

/-- One term of the added double sum of Conjecture 2.26: the Iverson bracket is the
congruence `n ≡ p(m+1)·i + p(m-1) (mod p(m+1)(2i+1))`. -/
def posTerm (p : ℕ → ℕ) (n k m i : ℕ) : ℤ :=
  if n % (p (m + 1) * (2 * i + 1)) = (p (m + 1) * i + p (m - 1)) % (p (m + 1) * (2 * i + 1))
  then
    pv p (((n : ℤ) - (p (m + 1) : ℤ) * i - (p (m - 1) : ℤ))
      / ((p (m + 1) : ℤ) * (2 * (i : ℤ) + 1)) - k)
  else 0

/-- Schmidt's Conjecture 2.26, exactly as printed. -/
def proposed (p : ℕ → ℕ) (n k : ℕ) : ℤ :=
  pv p ((n : ℤ) - k) - ∑ i ∈ Icc 1 n, negTerm p n k i
    + ∑ m ∈ Icc 2 n, ∑ i ∈ Icc 1 n, posTerm p n k m i

/-- The write-up's corrected inverse: `∑_{d ∣ 2n+1} μ(d) p(((2n+1)/d - 1)/2 - k)`. -/
def corrected (p : ℕ → ℕ) (n k : ℕ) : ℤ :=
  ∑ d ∈ (2 * n + 1).divisors, moebius d * pv p ((((2 * n + 1) / d - 1) / 2 : ℕ) - (k : ℤ))

/-! ## Numeral reductions for `Int.toNat`

`pv` unfolds to `p z.toNat`, and `simp` pushes `toNat` through the subtraction but leaves
`Int.toNat <numeral>` stuck; these five close it at the literals that occur. -/

theorem toNat_four : Int.toNat 4 = 4 := rfl

theorem toNat_six : Int.toNat 6 = 6 := rfl

theorem toNat_nineteen : Int.toNat 19 = 19 := rfl

theorem toNat_fiftyseven : Int.toNat 57 = 57 := rfl

theorem toNat_fiftyeight : Int.toNat 58 = 58 := rfl

/-! ## Evaluation at `(58, 1)` -/

theorem corrected_58 (p : ℕ → ℕ) :
    corrected p 58 1 = (p 57 : ℤ) - p 18 - p 3 + p 0 := by
  rw [corrected, show (2 * 58 + 1 : ℕ) = 117 from rfl,
    show (117 : ℕ).divisors = {1, 3, 9, 13, 39, 117} from by decide]
  norm_num [mu_three, mu_nine, mu_thirteen, mu_thirtynine, mu_onehundredseventeen, pv,
    toNat_four, toNat_six, toNat_nineteen, toNat_fiftyseven, toNat_fiftyeight]
  ring

theorem negSum_58 (p : ℕ → ℕ) :
    ∑ i ∈ Icc 1 58, negTerm p 58 1 i = (p 18 : ℤ) + p 5 + p 3 + p 0 := by
  have hsub : ({1, 4, 6, 19, 58} : Finset ℕ) ⊆ Icc 1 58 := by decide
  have hz : ∀ i ∈ Icc 1 58, i ∉ ({1, 4, 6, 19, 58} : Finset ℕ) → negTerm p 58 1 i = 0 := by
    intro i hi hni
    have h : ¬ (58 % (2 * i + 1) = i % (2 * i + 1)) := by
      revert hni hi; revert i; decide
    simp [negTerm, h]
  rw [← Finset.sum_subset hsub hz]
  norm_num [negTerm, pv, toNat_four, toNat_six, toNat_nineteen, toNat_fiftyseven, toNat_fiftyeight]
  ring

/-- Every `m ≥ 6` contributes nothing: monotonicity forces the modulus above the
numerator, so the floor quotient is at most `0` and the index is negative. -/
theorem posTerm_eq_zero_of_large (p : ℕ → ℕ) (m i : ℕ)
    (ha : 15 ≤ p (m + 1)) (hb : 7 ≤ p (m - 1)) (hi : 1 ≤ i) :
    posTerm p 58 1 m i = 0 := by
  rw [posTerm]
  split
  · refine pv_of_neg p ?_
    have ha' : (15 : ℤ) ≤ (p (m + 1) : ℤ) := by exact_mod_cast ha
    have hb' : (7 : ℤ) ≤ (p (m - 1) : ℤ) := by exact_mod_cast hb
    have hi' : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi
    have hden : (0 : ℤ) < (p (m + 1) : ℤ) * (2 * (i : ℤ) + 1) := by nlinarith
    have hlt : ((58 : ℤ) - (p (m + 1) : ℤ) * i - (p (m - 1) : ℤ))
        < 1 * ((p (m + 1) : ℤ) * (2 * (i : ℤ) + 1)) := by nlinarith
    have := (Int.ediv_lt_iff_lt_mul hden).mpr hlt
    push_cast
    linarith
  · rfl

theorem posSum_58 (p : ℕ → ℕ) (hp1 : p 1 = 1) (hp2 : p 2 = 2) (hp3 : p 3 = 3)
    (hp4 : p 4 = 5) (hp5 : p 5 = 7) (hp6 : p 6 = 11) (hp7 : p 7 = 15)
    (hmono : Monotone p) :
    ∑ m ∈ Icc 2 58, ∑ i ∈ Icc 1 58, posTerm p 58 1 m i = (p 5 : ℤ) + p 0 := by
  have hsub : ({2} : Finset ℕ) ⊆ Icc 2 58 := by decide
  have hz : ∀ m ∈ Icc 2 58, m ∉ ({2} : Finset ℕ) →
      ∑ i ∈ Icc 1 58, posTerm p 58 1 m i = 0 := by
    intro m hm hnm
    simp only [Finset.mem_Icc] at hm
    obtain ⟨hm2, hm58⟩ := hm
    simp only [Finset.mem_singleton] at hnm
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    obtain ⟨hi1, hi58⟩ := hi
    rcases Nat.lt_or_ge m 6 with h6 | h6
    · interval_cases m
      · exact absurd rfl hnm
      · rw [posTerm, hp4, hp2]
        have : ¬ (58 % (5 * (2 * i + 1)) = (5 * i + 2) % (5 * (2 * i + 1))) := by
          revert hi58 hi1; revert i; decide
        simp [this]
      · rw [posTerm, hp5, hp3]
        have : ¬ (58 % (7 * (2 * i + 1)) = (7 * i + 3) % (7 * (2 * i + 1))) := by
          revert hi58 hi1; revert i; decide
        simp [this]
      · rw [posTerm, hp6, hp4]
        have : ¬ (58 % (11 * (2 * i + 1)) = (11 * i + 5) % (11 * (2 * i + 1))) := by
          revert hi58 hi1; revert i; decide
        simp [this]
    · refine posTerm_eq_zero_of_large p m i ?_ ?_ hi1
      · calc 15 = p 7 := hp7.symm
          _ ≤ p (m + 1) := hmono (by omega)
      · calc 7 = p 5 := hp5.symm
          _ ≤ p (m - 1) := hmono (by omega)
  rw [← Finset.sum_subset hsub hz, Finset.sum_singleton]
  have hsub2 : ({1, 6, 19} : Finset ℕ) ⊆ Icc 1 58 := by decide
  have hz2 : ∀ i ∈ Icc 1 58, i ∉ ({1, 6, 19} : Finset ℕ) → posTerm p 58 1 2 i = 0 := by
    intro i hi hni
    rw [posTerm, hp3, hp1]
    have h : ¬ (58 % (3 * (2 * i + 1)) = (3 * i + 1) % (3 * (2 * i + 1))) := by
      revert hni hi; revert i; decide
    simp [h]
  rw [← Finset.sum_subset hsub2 hz2]
  simp only [posTerm, hp3, hp1]
  norm_num [pv, toNat_four, toNat_six, toNat_nineteen, toNat_fiftyseven, toNat_fiftyeight]

theorem proposed_58 (p : ℕ → ℕ) (hp1 : p 1 = 1) (hp2 : p 2 = 2) (hp3 : p 3 = 3)
    (hp4 : p 4 = 5) (hp5 : p 5 = 7) (hp6 : p 6 = 11) (hp7 : p 7 = 15)
    (hmono : Monotone p) :
    proposed p 58 1 = (p 57 : ℤ) - p 18 - p 3 := by
  rw [proposed, negSum_58 p, posSum_58 p hp1 hp2 hp3 hp4 hp5 hp6 hp7 hmono]
  norm_num [pv, toNat_four, toNat_six, toNat_nineteen, toNat_fiftyseven, toNat_fiftyeight]
  ring

/-- **The discrepancy, free of every partition value but `p 0`.**  `p 57`, `p 18` and
`p 3` cancel; the two formulas differ by exactly one `p 0`. -/
theorem discrepancy (p : ℕ → ℕ) (hp1 : p 1 = 1) (hp2 : p 2 = 2) (hp3 : p 3 = 3)
    (hp4 : p 4 = 5) (hp5 : p 5 = 7) (hp6 : p 6 = 11) (hp7 : p 7 = 15)
    (hmono : Monotone p) :
    corrected p 58 1 - proposed p 58 1 = (p 0 : ℤ) := by
  rw [corrected_58 p, proposed_58 p hp1 hp2 hp3 hp4 hp5 hp6 hp7 hmono]
  ring

/-! ## The refutation -/

/-- Schmidt's Conjecture 2.26: the proposed formula gives every entry of `S⁻¹`. -/
def ConjInverse (p : ℕ → ℕ) (sinv : ℕ → ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ n → sinv n k = proposed p n k

/-- Conjecture 2.26 is false.  The witness is the single entry `(n,k) = (58,1)`, and the
argument needs no partition value beyond `p 0 ≠ 0`. -/
theorem not_conj (p : ℕ → ℕ) (sinv : ℕ → ℕ → ℤ)
    (htrue : ∀ n k : ℕ, 1 ≤ k → k ≤ n → sinv n k = corrected p n k)
    (hp0 : p 0 ≠ 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2) (hp3 : p 3 = 3)
    (hp4 : p 4 = 5) (hp5 : p 5 = 7) (hp6 : p 6 = 11) (hp7 : p 7 = 15)
    (hmono : Monotone p) :
    ¬ ConjInverse p sinv := by
  intro hconj
  have h1 := htrue 58 1 (by norm_num) (by norm_num)
  have h2 := hconj 58 1 (by norm_num) (by norm_num)
  have hd := discrepancy p hp1 hp2 hp3 hp4 hp5 hp6 hp7 hmono
  have : (p 0 : ℤ) = 0 := by rw [← hd, ← h1, ← h2]; ring
  exact hp0 (by exact_mod_cast this)

end Principia.MathDB.P356220
