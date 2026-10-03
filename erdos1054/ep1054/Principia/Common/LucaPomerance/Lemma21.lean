/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Lemma21Part2

set_option autoImplicit false

/-!
# Luca–Pomerance (2015), Lemma 2.1 — proved

`lucaPomerance_lemma21`: with `y(n) = log log n / log log log n` (`lpY`), there is a set `E` of
natural density zero (in counting form: for every `ε > 0`, eventually `#(E ∩ [1, N]) ≤ ε N`)
outside which

* (i)   `v_p(n) < v_p(σ(n))` for every prime `p ≤ y(n)`;
* (ii)  every prime factor of `gcd(n, σ(n))` is `≤ y(n)`;
* (iii) every prime `p ≤ y(n)` divides `σ(n)/gcd(n, σ(n))`;
* (iv)  every prime factor of `s(n)/gcd(n, σ(n))` exceeds `y(n)` (`s(n) = σ(n) − n`).

`E = {n : (i) fails} ∪ {n : a prime > y(n) divides n and σ(n)}`. (iii) and (iv) follow from (i)
by divisibility (`iii_of_i`, `iv_of_i`); (ii) from the second set (`smooth_gcd_of_forall`).
The two density statements are `failI_count_le` and `failII_count_le`.

Source: F. Luca, C. Pomerance, *The range of the sum-of-proper-divisors function*, Acta Arith.
168 (2015), Lemma 2.1. Nothing here is new mathematics; the Lean proof follows the plan in
`Campaigns/Erdos-1054/LP21-PLAN.md`, whose one non-routine input — the second Mertens
estimate in progressions, uniform in the modulus and with the exact constant `1/φ(m)`
(`mertens_AP`) — is derived from the library's unconditional Siegel–Walfisz theorem.
-/

namespace Principia.Common.LucaPomerance.LP21

open Finset Real ArithmeticFunction

/-- The exceptional set: (i) fails, or a prime `> y(n)` divides both `n` and `σ(n)`. -/
def LP21Exc : Set ℕ := {n | FailI n ∨ FailII n}

open Classical in
/-- **Luca–Pomerance, Lemma 2.1.** -/
theorem lucaPomerance_lemma21 :
    ∃ E : Set ℕ,
      (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Icc 1 N).filter (· ∈ E)).card : ℝ) ≤ ε * N) ∧
      ∀ n : ℕ, n ∉ E →
        (∀ p : ℕ, p.Prime → (p : ℝ) ≤ lpY n →
          n.factorization p < (sigma 1 n).factorization p) ∧
        (∀ r ∈ (Nat.gcd n (sigma 1 n)).primeFactors, (r : ℝ) ≤ lpY n) ∧
        (∀ p : ℕ, p.Prime → (p : ℝ) ≤ lpY n → p ∣ sigma 1 n / Nat.gcd n (sigma 1 n)) ∧
        (∀ p ∈ ((sigma 1 n - n) / Nat.gcd n (sigma 1 n)).primeFactors, lpY n < (p : ℝ)) := by
  refine ⟨LP21Exc, ?_, ?_⟩
  · intro ε hε
    obtain ⟨N₁, h₁⟩ := failI_count_le (ε / 2) (by positivity)
    obtain ⟨N₂, h₂⟩ := failII_count_le (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have e1 := h₁ N (le_trans (le_max_left _ _) hN)
    have e2 := h₂ N (le_trans (le_max_right _ _) hN)
    have hS : ∀ S : Finset ℕ,
        S ⊆ (Finset.Icc 1 N).filter FailI ∪ (Finset.Icc 1 N).filter FailII →
          (S.card : ℝ) ≤ ε * N := by
      intro S hSsub
      have hc := (Finset.card_le_card hSsub).trans (Finset.card_union_le _ _)
      have hc' : (S.card : ℝ) ≤ (((Finset.Icc 1 N).filter FailI).card : ℝ) +
          (((Finset.Icc 1 N).filter FailII).card : ℝ) := by exact_mod_cast hc
      linarith
    apply hS
    intro n hn
    rw [Finset.mem_filter] at hn
    have hn2 : FailI n ∨ FailII n := hn.2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hn2 with h | h
    · exact Or.inl ⟨hn.1, h⟩
    · exact Or.inr ⟨hn.1, h⟩
  · intro n hn
    have hn' : ¬ (FailI n ∨ FailII n) := hn
    obtain ⟨hI, hII⟩ := not_or.mp hn'
    have hi : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lpY n →
        n.factorization p < (sigma 1 n).factorization p := by
      intro p hp hpy
      by_contra h
      exact hI ⟨p, hp, hpy, not_lt.mp h⟩
    refine ⟨hi, ?_, iii_of_i n (lpY n) hi, iv_of_i n (lpY n) hi⟩
    exact smooth_gcd_of_forall n (lpY n) (fun r hr hry hrn hrσ => hII ⟨r, hr, hry, hrn, hrσ⟩)

end Principia.Common.LucaPomerance.LP21
