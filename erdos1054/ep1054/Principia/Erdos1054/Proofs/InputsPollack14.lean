/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Density
import Principia.Erdos1054.Proofs.Normality
import Principia.Erdos1054.Proofs.InputsStd
import Principia.Common.LucaPomerance.Pollack14

set_option autoImplicit false

/-!
# EP1054: the Pollack Theorem 1.4 input, discharged

Discharges `Principia.Erdos1054.Cite_Pollack_Thm14` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, `lem:sv-regular`, eq:sv-image-abundancy,
lines 1470–1476): the `n` with `s(s(n))/s(n) > s(n)/n + 1` have density zero.

The proof is `Common.LucaPomerance.pollack_weak`, whose one hypothesis — fixed-modulus normality
of `σ` — is the library's unconditional `Lem_FixedModulusNormality`
(`link_Lem_FixedModulusNormality leaf_Std_recipPrimesAP_diverges`, the same composition as
`ep1054_Lem_FixedModulusNormality`). Other ingredients: Brun–Titchmarsh (`C = 2008`), Mertens'
first theorem, Legendre's formula, and the Davenport-module counts of `σ(n)/n > K` and of
`P² ∣ n`. No rate is claimed (Pollack's `(log₃x)²/(log₂x)^{1/4}` is not used by the paper).
See `Campaigns/Erdos-1054/LP22-POLLACK-PLAN.md`.
-/

namespace Principia.Erdos1054.Proofs.InputsPollack14

open Finset Principia.Common.LucaPomerance.Pollack14

/-- `Lem_FixedModulusNormality` in the counting form `Common.LucaPomerance.FixedModulusNormal`. -/
theorem fixedModulusNormal : FixedModulusNormal := by
  intro V hV ε hε
  have hLem : Principia.Erdos1054.Lem_FixedModulusNormality :=
    link_Lem_FixedModulusNormality leaf_Std_recipPrimesAP_diverges
  obtain ⟨X₀, hX₀⟩ := (hLem V hV).exists_le_mul hε
  refine ⟨X₀, fun X hX => le_trans ?_ (hX₀ X hX)⟩
  unfold cnt
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact hn

end Principia.Erdos1054.Proofs.InputsPollack14

namespace Principia.Erdos1054.Proofs

open Principia.Common.LucaPomerance.Pollack14

/-- **`Cite_Pollack_Thm14`**, discharged (weak form, which is the input's statement): from
fixed-modulus normality of `σ` (unconditional in the library), Brun–Titchmarsh and Mertens. -/
theorem input_Cite_Pollack_Thm14 : Principia.Erdos1054.Cite_Pollack_Thm14 := by
  unfold Principia.Erdos1054.Cite_Pollack_Thm14
  rw [densZero_iff_exists_real]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := pollack_weak InputsPollack14.fixedModulusNormal ε hε
  refine ⟨X₀, fun X hX => le_trans ?_ (hX₀ X hX)⟩
  unfold cnt
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact hn

end Principia.Erdos1054.Proofs
