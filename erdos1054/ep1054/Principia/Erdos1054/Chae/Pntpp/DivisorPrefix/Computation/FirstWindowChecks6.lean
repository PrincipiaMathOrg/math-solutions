/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks6.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks5

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime60 : Nat.Prime 10567 := by
  norm_num

theorem firstWindowPrime61 : Nat.Prime 10589 := by
  norm_num

theorem firstWindowPrime62 : Nat.Prime 10597 := by
  norm_num

theorem firstWindowPrime63 : Nat.Prime 10601 := by
  norm_num

theorem firstWindowPrime64 : Nat.Prime 10607 := by
  norm_num

theorem firstWindowPrime65 : Nat.Prime 10613 := by
  norm_num

theorem firstWindowPrime66 : Nat.Prime 10627 := by
  norm_num

theorem firstWindowPrime67 : Nat.Prime 10631 := by
  norm_num

theorem firstWindowPrime68 : Nat.Prime 10639 := by
  norm_num

theorem firstWindowPrime69 : Nat.Prime 10651 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks60_valid :
    ∀ i : Fin firstWindowMasks60.size,
      maskSum firstWindowSeed firstWindowMasks60[i] =
        firstWindowLower + 100 * 60 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks61_valid :
    ∀ i : Fin firstWindowMasks61.size,
      maskSum firstWindowSeed firstWindowMasks61[i] =
        firstWindowLower + 100 * 61 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks62_valid :
    ∀ i : Fin firstWindowMasks62.size,
      maskSum firstWindowSeed firstWindowMasks62[i] =
        firstWindowLower + 100 * 62 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks63_valid :
    ∀ i : Fin firstWindowMasks63.size,
      maskSum firstWindowSeed firstWindowMasks63[i] =
        firstWindowLower + 100 * 63 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks64_valid :
    ∀ i : Fin firstWindowMasks64.size,
      maskSum firstWindowSeed firstWindowMasks64[i] =
        firstWindowLower + 100 * 64 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks65_valid :
    ∀ i : Fin firstWindowMasks65.size,
      maskSum firstWindowSeed firstWindowMasks65[i] =
        firstWindowLower + 100 * 65 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks66_valid :
    ∀ i : Fin firstWindowMasks66.size,
      maskSum firstWindowSeed firstWindowMasks66[i] =
        firstWindowLower + 100 * 66 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks67_valid :
    ∀ i : Fin firstWindowMasks67.size,
      maskSum firstWindowSeed firstWindowMasks67[i] =
        firstWindowLower + 100 * 67 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks68_valid :
    ∀ i : Fin firstWindowMasks68.size,
      maskSum firstWindowSeed firstWindowMasks68[i] =
        firstWindowLower + 100 * 68 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks69_valid :
    ∀ i : Fin firstWindowMasks69.size,
      maskSum firstWindowSeed firstWindowMasks69[i] =
        firstWindowLower + 100 * 69 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
