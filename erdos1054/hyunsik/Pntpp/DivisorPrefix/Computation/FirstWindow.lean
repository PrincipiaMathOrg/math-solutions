import Pntpp.DivisorPrefix.Computation.FirstWindowChecks

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
