import Principia.Common.HalberstamRichert
import Principia.Common.Mertens.Mertens

set_option autoImplicit false

/-!
# Pollack's mean-value bound, unconditionally

Pollack (2014), Lemma 2.4 -- the form used by the Erdős-1054 paper's `lem:sigma-rate`:

> there is an absolute `C` such that for every multiplicative `f` with `0 ≤ f (p^k) ≤ 1` at all
> prime powers and every `x ≥ 1`,
> `∑_{n ≤ x} f n ≤ C · x · exp (∑_{p ≤ x} (f p - 1)/p)`.

`Principia.Common.HalberstamRichert` proves this conditionally on `MertensUpper B` (the upper half
of Mertens' second theorem, `∑_{p ≤ N} 1/p ≤ log log N + B`). This module discharges that
hypothesis from `Mertens.sum_prime_div_eq_log_log` in the Mertens port
(`Principia.Common.Mertens.Mertens`, ported from PrimeNumberTheoremAnd, Apache 2.0), and states
the unconditional result. Nothing here is new mathematics: the Halberstam--Richert part is a port
of `plby/lean-proofs` (see `Principia.Common.HalberstamRichert` for provenance and licence) and
Mertens' theorem is a port of PNT+.

## Conventions

* `f : ℕ → ℝ` is multiplicative in the usual sense: `f 1 = 1` and `f (m n) = f m f n` for
  coprime `m, n`. Its value at `0` is irrelevant (the sums start at `n = 1`).
* `∑_{n ≤ x}` is `∑ n ∈ Finset.Icc 1 ⌊x⌋₊`; `∑_{p ≤ x}` is `∑ p ∈ Nat.primesLE ⌊x⌋₊`.
-/

open Finset

namespace Principia.Common.HalberstamRichert

/-- The upper half of Mertens' second theorem holds for some constant `B`
(from `Mertens.sum_prime_div_eq_log_log`). -/
theorem exists_mertensUpper : ∃ B : ℝ, MertensUpper B := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun N hN => ?_⟩
  have hx : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h := hC (N : ℝ) hx
  rw [Nat.floor_natCast] at h
  have hset : ∑ p ∈ Finset.Ioc 0 N with p.Prime, (1 : ℝ) / (p : ℝ) =
      ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨hpN, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.pos, hpN⟩, hp⟩
  rw [hset] at h
  have habs := le_abs_self
    (∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) - Real.log (Real.log (N : ℝ)))
  linarith

/-- **Pollack (2014), Lemma 2.4, integer cut-off.** There is an absolute constant `C > 0` such
that for every multiplicative `f : ℕ → ℝ` with `0 ≤ f (p^k) ≤ 1` at every prime power `p^k`
(`k ≥ 1`) and every integer `N ≥ 1`,
`∑_{1 ≤ n ≤ N} f n ≤ C · N · exp (∑_{p ≤ N} (f p - 1)/p)`. -/
theorem pollack_mean_value_nat :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℕ → ℝ), f 1 = 1 →
        (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) →
        (∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ f (p ^ k) ∧ f (p ^ k) ≤ 1) →
        ∀ N : ℕ, 1 ≤ N →
          ∑ n ∈ Finset.Icc 1 N, f n ≤
            C * (N : ℝ) * Real.exp (∑ p ∈ Nat.primesLE N, (f p - 1) / (p : ℝ)) := by
  obtain ⟨B, hB⟩ := exists_mertensUpper
  have hK : 0 ≤ explicitMassConstant 1 1 :=
    explicitMassConstant_nonneg (by norm_num) (by norm_num)
  refine ⟨(explicitMassConstant 1 1 + 1) * Real.exp (B + 1), by positivity, ?_⟩
  intro f hf1 hmul hpp N hN
  exact sum_le_mul_exp_of_mertensUpper hB f hf1 hmul hpp N hN

/-- **Pollack (2014), Lemma 2.4, real cut-off** -- the statement the Erdős-1054 paper uses.
There is an absolute constant `C > 0` such that for every multiplicative `f : ℕ → ℝ` with
`0 ≤ f (p^k) ≤ 1` at every prime power and every real `x ≥ 1`,
`∑_{n ≤ x} f n ≤ C · x · exp (∑_{p ≤ x} (f p - 1)/p)`. -/
theorem pollack_mean_value :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℕ → ℝ), f 1 = 1 →
        (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) →
        (∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ f (p ^ k) ∧ f (p ^ k) ≤ 1) →
        ∀ x : ℝ, 1 ≤ x →
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n ≤
            C * x * Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, (f p - 1) / (p : ℝ)) := by
  obtain ⟨B, hB⟩ := exists_mertensUpper
  have hK : 0 ≤ explicitMassConstant 1 1 :=
    explicitMassConstant_nonneg (by norm_num) (by norm_num)
  refine ⟨(explicitMassConstant 1 1 + 1) * Real.exp (B + 1), by positivity, ?_⟩
  intro f hf1 hmul hpp x hx
  exact sum_le_mul_exp_of_mertensUpper_real hB f hf1 hmul hpp x hx

/-- The same, for a Mathlib `ArithmeticFunction` that is `IsMultiplicative`. -/
theorem pollack_mean_value_arithmeticFunction :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative →
        (∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ f (p ^ k) ∧ f (p ^ k) ≤ 1) →
        ∀ x : ℝ, 1 ≤ x →
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n ≤
            C * x * Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, (f p - 1) / (p : ℝ)) := by
  obtain ⟨C, hC, hmain⟩ := pollack_mean_value
  refine ⟨C, hC, fun f hf hpp x hx => ?_⟩
  exact hmain (fun n => f n) hf.map_one
    (fun m n hmn => hf.map_mul_of_coprime hmn) hpp x hx

end Principia.Common.HalberstamRichert
