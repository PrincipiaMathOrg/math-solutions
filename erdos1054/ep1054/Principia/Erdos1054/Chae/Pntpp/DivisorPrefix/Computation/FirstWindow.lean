/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindow.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 6000

theorem firstWindow_subsetSum_coverage :
    ∀ n,
      firstWindowLower ≤ n →
      n ≤ firstWindowUpper →
      IsSubsetSum firstWindowPrimes n := by
  intro n hnLower hnUpper
  let k := n - firstWindowLower
  have hk : k < 10889 := by
    dsimp [k, firstWindowLower, firstWindowUpper] at *
    omega
  have hjNat : k / 100 < 109 := by
    omega
  let j : Fin 109 := ⟨k / 100, hjNat⟩
  have hchunkSize := firstWindowMaskChunk_sizes j
  have hrem : k % 100 < (firstWindowMaskChunk j).size := by
    rw [hchunkSize]
    by_cases hj : (j : ℕ) = 108
    · simp only [hj, ↓reduceIte]
      have hdecomp := Nat.mod_add_div k 100
      dsimp [j] at hj
      omega
    · simp only [hj, ↓reduceIte]
      exact Nat.mod_lt _ (by omega)
  let i : Fin (firstWindowMaskChunk j).size := ⟨k % 100, hrem⟩
  have hvalid := firstWindowMaskChunks_valid j i
  refine
    ⟨maskFinset firstWindowSeed (firstWindowMaskChunk j)[i], ?_, ?_⟩
  · exact maskFinset_subset_toFinset _ _
  · rw [sum_maskFinset _ _ firstWindowSeed_nodup, hvalid]
    have hdecomp := Nat.mod_add_div k 100
    change firstWindowLower + 100 * (k / 100) + k % 100 = n
    dsimp [k] at hdecomp ⊢
    omega

end Pntpp.DivisorPrefix.Computation
