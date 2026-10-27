import Erdos361.BasileGlue
import Erdos361.BasileGreedy
import Erdos361.BasileCovering
import Erdos361.BasileFreiman
open scoped Pointwise

/-!
# Erdős #361 — Basile's Problem 7.1: the UNCONDITIONAL assembly

`basile71_unconditional` composes the three axiom-free in-project theorems into one statement,
carrying ONLY Freiman's `3k-3` theorem as a hypothesis (regime (c) — the single cited fact, never an
axiom):
* `good_core_exists`   (Erdos361Greedy)   — discharges Alon's Prop 2.5 good core (hAlon).
* `hLev_covering`      (Erdos361Covering) — discharges the located covering (hLev), elementary route.
* `basile71_glue`      (Erdos361Basile71) — distinctification + `Represents ↔ ¬Avoids`.

Result: for every `ε > 0` there is an `E₀` such that for all `E ≥ E₀`, every `A ⊆ [1,E]` of density
`≥ 1/3 + ε` represents every even `t ∈ (2E,3E)` with `3 ∤ t` (i.e. `¬ Avoids A t`). This is a rigorous
Lean proof of Basile 7.1 modulo Freiman `3k-3` and pending expert referee.
-/

namespace Erdos361BasileMaster

open Erdos361Basile71 Erdos361Covering

/-- **Basile 7.1 (snd = 3 linear case), unconditional modulo Freiman `3k-3`.** -/
theorem basile71_unconditional (ε : ℝ) (hε : 0 < ε)
    (hFreiman : ∀ (B' : Finset ℕ) (L' : ℕ), B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → 2 * B'.card - 3 ≤ L' → B'.gcd id = 1 → 3 * B'.card - 3 ≤ (B' + B').card) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t := by
  obtain ⟨E₀gce, hgce⟩ := good_core_exists ε hε
  refine ⟨max E₀gce (⌈16 / ε⌉₊ + 1), fun E hE A hAsub hden t htlo hthi ht2 ht3 => ?_⟩
  have hEge : E₀gce ≤ E := le_trans (le_max_left _ _) hE
  have hEbig : ⌈16 / ε⌉₊ + 1 ≤ E := le_trans (le_max_right _ _) hE
  -- ε·E ≥ 16
  have hεE : (16 : ℝ) ≤ ε * E := by
    have hc : (16 / ε) ≤ (⌈16 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : (⌈16 / ε⌉₊ : ℝ) < (E : ℝ) := by exact_mod_cast (by omega : ⌈16 / ε⌉₊ < E)
    have h16 : 16 / ε < (E : ℝ) := lt_of_le_of_lt hc hlt
    rw [div_lt_iff₀ hε] at h16
    nlinarith [h16]
  -- the good core
  obtain ⟨G, hGsubA, hmid, hGsize⟩ := hgce E hEge A hAsub hden
  have hGsub : G ⊆ Finset.Icc 1 E := hGsubA.trans hAsub
  -- real → ℕ size bound  E + 24 ≤ 3|G|
  have hsizeR : (E : ℝ) + 24 ≤ 3 * (G.card : ℝ) := by nlinarith [hGsize, hεE]
  have hsizeN : E + 24 ≤ 3 * G.card := by exact_mod_cast hsizeR
  have hG3 : 3 ≤ G.card := by omega
  -- hLev covering → h-fold representation
  obtain ⟨h, _, hh9, hhf⟩ := hLev_covering E G hGsub hG3 hsizeN hFreiman t ht2 htlo hthi
  have hrep : RepWithRep G h t := hhf
  have hgood : GoodCore A G := ⟨hGsubA, hmid⟩
  exact basile71_glue E t A hAsub ht2 ht3 htlo hthi G hgood ⟨h, by omega, hrep⟩

#print axioms basile71_unconditional

/-- **Basile 7.1 (snd = 3 linear case), FULLY unconditional.** Same statement as
`basile71_unconditional`, but with `hFreiman` discharged by the in-project, from-scratch,
axiom-free `Erdos361Freiman.freiman_3k3` (Freiman's `3k-3` theorem). No cited hypothesis remains —
the only inputs are Mathlib and the three standard axioms. A candidate pending expert referee; it
does not claim the full erdosproblems.com #361. -/
theorem basile71_fully_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t :=
  basile71_unconditional ε hε
    (fun B' L' hsub h0 hL hk hL2 hgcd =>
      Erdos361Freiman.freiman_3k3 B' L' hsub h0 hL hk hgcd hL2)

#print axioms basile71_fully_unconditional

end Erdos361BasileMaster
