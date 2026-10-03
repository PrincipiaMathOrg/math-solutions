/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Mathlib.Tactic.NormNum.Basic

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — worklist row #122: `thm:fraiture-representability`

The link `Link_Thm_FraitureRepresentability` (paper lines 677–684; proof lines 955–966):
from `Prop_FraitureFinite`, `Prop_FraitureTail` and `Step_FraitureSmallCases`,
`𝓡 = ℕ ∖ {2, 5}` (Lean: `R = {N | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5}`, `Eq_ExactRepresentability`).

## Proof

* `⊆`: `0, 2, 5 ∉ R` are three conjuncts of `Step_FraitureSmallCases`.
* `⊇`: `1, 3, 4` are represented by `m = 1, 2, 3` (the `IsRep` conjuncts of
  `Step_FraitureSmallCases`). For `N ≥ 6` the three finite intervals
  `[6, 10^7]`, `[469 616, 273 803 744 799 154]`, `[105 000 001, 10^27 + 10^8]` overlap
  (`10^7 ≥ 469 616 - 1`, `273 803 744 799 154 ≥ 105 000 001 - 1`), and the tail
  `n ≥ 10^27 + 10^8` of `Prop_FraitureTail` meets the last one at its right end. The case split is
  on `N ≤ 10^7`, `N ≤ 273 803 744 799 154`, `N ≤ 10^27 + 10^8`, each closed by `omega` on literals.
-/

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054

theorem link_Thm_FraitureRepresentability :
    Principia.Erdos1054.Spine.Link_Thm_FraitureRepresentability := by
  rintro ⟨hS, hW1, hW2⟩ hT ⟨h1, h3, h4, h2, h5, h0⟩
  change R = {N : ℕ | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5}
  have e7 : (10 : ℕ) ^ 7 = 10000000 := by norm_num
  have e27 : (10 : ℕ) ^ 27 + 10 ^ 8 = 1000000000000000000100000000 := by norm_num
  ext N
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hN
    refine ⟨Nat.pos_of_ne_zero ?_, ?_, ?_⟩
    · rintro rfl
      exact h0 hN
    · rintro rfl
      exact h2 hN
    · rintro rfl
      exact h5 hN
  · rintro ⟨hN1, hN2, hN5⟩
    by_cases hsmall : N < 6
    · have hcases : N = 1 ∨ N = 3 ∨ N = 4 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact ⟨1, le_rfl, h1⟩
      · exact ⟨2, by norm_num, h3⟩
      · exact ⟨3, by norm_num, h4⟩
    · by_cases hA : N ≤ 10000000
      · exact hS N (by omega) (by rw [e7]; exact hA)
      · by_cases hB : N ≤ 273803744799154
        · exact hW1 N (by omega) hB
        · by_cases hC : N ≤ 1000000000000000000100000000
          · exact hW2 N (by omega) (by rw [e27]; exact hC)
          · exact hT N (by rw [e27]; omega)

end Principia.Erdos1054.Proofs
