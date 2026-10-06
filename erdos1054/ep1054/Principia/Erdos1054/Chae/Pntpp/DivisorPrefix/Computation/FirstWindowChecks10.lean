/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks10.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks9

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks100_valid :
    ∀ i : Fin firstWindowMasks100.size,
      maskSum firstWindowSeed firstWindowMasks100[i] =
        firstWindowLower + 100 * 100 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks101_valid :
    ∀ i : Fin firstWindowMasks101.size,
      maskSum firstWindowSeed firstWindowMasks101[i] =
        firstWindowLower + 100 * 101 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks102_valid :
    ∀ i : Fin firstWindowMasks102.size,
      maskSum firstWindowSeed firstWindowMasks102[i] =
        firstWindowLower + 100 * 102 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks103_valid :
    ∀ i : Fin firstWindowMasks103.size,
      maskSum firstWindowSeed firstWindowMasks103[i] =
        firstWindowLower + 100 * 103 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks104_valid :
    ∀ i : Fin firstWindowMasks104.size,
      maskSum firstWindowSeed firstWindowMasks104[i] =
        firstWindowLower + 100 * 104 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks105_valid :
    ∀ i : Fin firstWindowMasks105.size,
      maskSum firstWindowSeed firstWindowMasks105[i] =
        firstWindowLower + 100 * 105 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks106_valid :
    ∀ i : Fin firstWindowMasks106.size,
      maskSum firstWindowSeed firstWindowMasks106[i] =
        firstWindowLower + 100 * 106 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks107_valid :
    ∀ i : Fin firstWindowMasks107.size,
      maskSum firstWindowSeed firstWindowMasks107[i] =
        firstWindowLower + 100 * 107 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks108_valid :
    ∀ i : Fin firstWindowMasks108.size,
      maskSum firstWindowSeed firstWindowMasks108[i] =
        firstWindowLower + 100 * 108 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
