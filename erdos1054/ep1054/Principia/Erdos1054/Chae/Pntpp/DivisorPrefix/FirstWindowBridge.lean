/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/FirstWindowBridge.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindow
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.PrimeWindow

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

open Computation

def firstWindowBridgePrimes : List ℕ :=
  [10889, 21773, 43543, 87083, 174169, 348323, 696659,
    1393313, 2786633, 5573257, 11146507, 22293031, 44586041, 89172101]

def firstWindowBridgeSet : Finset ℕ :=
  firstWindowPrimes ∪ firstWindowBridgePrimes.toFinset

theorem firstWindowBridgePrimes_prime :
    ∀ p ∈ firstWindowBridgePrimes, p.Prime := by
  norm_num [firstWindowBridgePrimes]

theorem firstWindowBridgePrimes_lower :
    ∀ p ∈ firstWindowBridgePrimes, 10000 < p := by
  decide

theorem firstWindowBridgePrimes_upper :
    ∀ p ∈ firstWindowBridgePrimes, p ≤ 99000000 := by
  decide

theorem firstWindowBridgePrimes_sum :
    firstWindowBridgePrimes.sum = 178333322 := by
  decide

theorem firstWindowBridge_chain :
    IsSubsetSumExtensionChain firstWindowPrimes
      firstWindowLower firstWindowUpper firstWindowBridgePrimes := by
  norm_num [IsSubsetSumExtensionChain, firstWindowPrimes, firstWindowSeed,
    firstWindowLower, firstWindowUpper, firstWindowBridgePrimes]

theorem firstWindow_extended_subsetSum :
    ∀ n,
      firstWindowLower ≤ n →
      n ≤ 178813825 →
      IsSubsetSum firstWindowBridgeSet n := by
  have hcover :=
    subsetSum_extension_chain
      (A := firstWindowPrimes)
      (C := firstWindowLower)
      (U := firstWindowUpper)
      (ps := firstWindowBridgePrimes)
      (by norm_num [firstWindowLower, firstWindowUpper])
      firstWindow_subsetSum_coverage
      firstWindowBridge_chain
  simpa [firstWindowBridgeSet, firstWindowBridgePrimes_sum,
    firstWindowUpper] using hcover

theorem firstWindowBridgeSet_prime :
    ∀ p ∈ firstWindowBridgeSet, p.Prime := by
  intro p hp
  simp only [firstWindowBridgeSet, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact firstWindowSeed_prime p (by
      simpa [firstWindowPrimes] using hp)
  · exact firstWindowBridgePrimes_prime p (by simpa using hp)

theorem firstWindowBridgeSet_lower :
    ∀ p ∈ firstWindowBridgeSet, 10000 < p := by
  intro p hp
  simp only [firstWindowBridgeSet, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact firstWindowSeed_lower p (by
      simpa [firstWindowPrimes] using hp)
  · exact firstWindowBridgePrimes_lower p (by simpa using hp)

theorem firstWindowBridgeSet_upper :
    ∀ p ∈ firstWindowBridgeSet, p ≤ 99000000 := by
  intro p hp
  simp only [firstWindowBridgeSet, Finset.mem_union] at hp
  rcases hp with hp | hp
  · have hpUpper := firstWindowSeed_upper p (by
      simpa [firstWindowPrimes] using hp)
    omega
  · exact firstWindowBridgePrimes_upper p (by simpa using hp)

theorem firstWindow_bridge_representation :
    ∀ n, 469616 ≤ n → n ≤ 178813826 → Represents n := by
  intro n hnLower hnUpper
  have hnPos : 1 ≤ n := by omega
  have hnSubset :
      IsSubsetSum firstWindowBridgeSet (n - 1) :=
    firstWindow_extended_subsetSum (n - 1) (by
      norm_num [firstWindowLower]
      omega) (by omega)
  have hrep :=
    represents_succ_of_subsetSum_prime_window
      firstWindowBridgeSet 10000 99000000 (n - 1)
      firstWindowBridgeSet_prime
      firstWindowBridgeSet_lower
      firstWindowBridgeSet_upper
      (by norm_num)
      hnSubset
  simpa [Nat.sub_add_cancel hnPos] using hrep

end Pntpp.DivisorPrefix
