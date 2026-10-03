/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Common.SW.Dyadic

/-!
# EP1054 trusted input `Std_SiegelWalfisz_dyadic`, discharged

`Std_SiegelWalfisz_dyadic` (Statements/Inputs.lean; paper lines 543–548, used by `lem:sigma-rate`):
there are `C, c > 0` with `π(2t; q, −1) − π(t; q, −1) ≥ c·t/(q log t)` for every prime `q ≥ 3` and
every `t ≥ exp(C q²)`.

It is the case `a = q − 1` of `Principia.Common.SW.sw_dyadic_count` (any modulus `q ≥ 1`, any
residue coprime to `q`), which rests on the ported axiom-clean Siegel–Walfisz master
(`Principia.Common.SW.*`: Landau/Jensen zero bounds, de la Vallée-Poussin and Siegel zero-free
regions, the smoothed Perron formula with the kernel re-proved from Mathlib's Mellin inversion, the
sharp twisted-`ψ` bound `psi_sharp_SW_rate`) plus Chebyshev's elementary dyadic bound for the
principal character — no prime number theorem and no PrimeNumberTheoremAnd dependency. The only
bridge needed here is `π(2t; q, a) − π(t; q, a) = #{p ∈ (⌊t⌋, ⌊2t⌋] prime, p ≡ a}`
(`piAP_dyadic_sub`).
-/

set_option autoImplicit false

namespace Principia.Erdos1054.Proofs.InputsSW

open Principia.Erdos1054

/-- `π(2t; q, a) − π(t; q, a)` counts the primes `p ∈ (⌊t⌋, ⌊2t⌋]` with `p ≡ a (mod q)`. -/
theorem piAP_dyadic_sub (t : ℝ) (ht : 0 ≤ t) (q a : ℕ) :
    (piAP (2 * t) q a : ℝ) - (piAP t q a : ℝ) =
      (((Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) := by
  have hfl : ⌊t⌋₊ ≤ ⌊2 * t⌋₊ := Nat.floor_le_floor (by linarith)
  have hunion : (Finset.Iic ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q) =
      (Finset.Iic ⌊t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q) ∪
        (Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨hp, hP⟩
      by_cases h : p ≤ ⌊t⌋₊
      · exact Or.inl ⟨h, hP⟩
      · exact Or.inr ⟨⟨by omega, hp⟩, hP⟩
    · rintro (⟨hp, hP⟩ | ⟨⟨_, hp⟩, hP⟩)
      · exact ⟨le_trans hp hfl, hP⟩
      · exact ⟨hp, hP⟩
  have hdisj : Disjoint ((Finset.Iic ⌊t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q))
      ((Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc] at hp1 hp2
    omega
  unfold piAP
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

end Principia.Erdos1054.Proofs.InputsSW

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054

/-- **`Std_SiegelWalfisz_dyadic` holds** (no hypotheses): the class `q − 1` of the dyadic
Siegel–Walfisz lower bound `Principia.Common.SW.sw_dyadic_count`, via `piAP_dyadic_sub`. -/
theorem input_Std_SiegelWalfisz_dyadic : Principia.Erdos1054.Std_SiegelWalfisz_dyadic := by
  obtain ⟨C, hC, c, hc, h⟩ := Principia.Common.SW.sw_dyadic_count
  unfold Std_SiegelWalfisz_dyadic
  refine ⟨C, hC, c, hc, ?_⟩
  intro q hq hq3 t ht
  have hcop : Nat.Coprime (q - 1) q :=
    (Nat.coprime_self_sub_left (m := 1) (n := q) (by omega)).mpr (Nat.coprime_one_left q)
  have ht0 : 0 ≤ t := le_trans (Real.exp_pos _).le ht
  rw [InputsSW.piAP_dyadic_sub t ht0 q (q - 1)]
  exact h q (by omega) (q - 1) hcop t ht

end Principia.Erdos1054.Proofs
