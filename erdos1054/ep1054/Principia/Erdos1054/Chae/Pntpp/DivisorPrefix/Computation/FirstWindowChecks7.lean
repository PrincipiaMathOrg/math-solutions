/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks7.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks6

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime70 : Nat.Prime 10657 := by
  norm_num

theorem firstWindowPrime71 : Nat.Prime 10663 := by
  norm_num

theorem firstWindowPrime72 : Nat.Prime 10667 := by
  norm_num

theorem firstWindowPrime73 : Nat.Prime 10687 := by
  norm_num

theorem firstWindowPrime74 : Nat.Prime 10691 := by
  norm_num

theorem firstWindowPrime75 : Nat.Prime 10709 := by
  norm_num

theorem firstWindowPrime76 : Nat.Prime 10711 := by
  norm_num

theorem firstWindowPrime77 : Nat.Prime 10723 := by
  norm_num

theorem firstWindowPrime78 : Nat.Prime 10729 := by
  norm_num

theorem firstWindowPrime79 : Nat.Prime 10733 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks70_valid :
    ∀ i : Fin firstWindowMasks70.size,
      maskSum firstWindowSeed firstWindowMasks70[i] =
        firstWindowLower + 100 * 70 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks71_valid :
    ∀ i : Fin firstWindowMasks71.size,
      maskSum firstWindowSeed firstWindowMasks71[i] =
        firstWindowLower + 100 * 71 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks72_valid :
    ∀ i : Fin firstWindowMasks72.size,
      maskSum firstWindowSeed firstWindowMasks72[i] =
        firstWindowLower + 100 * 72 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks73_valid :
    ∀ i : Fin firstWindowMasks73.size,
      maskSum firstWindowSeed firstWindowMasks73[i] =
        firstWindowLower + 100 * 73 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks74_valid :
    ∀ i : Fin firstWindowMasks74.size,
      maskSum firstWindowSeed firstWindowMasks74[i] =
        firstWindowLower + 100 * 74 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks75_valid :
    ∀ i : Fin firstWindowMasks75.size,
      maskSum firstWindowSeed firstWindowMasks75[i] =
        firstWindowLower + 100 * 75 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks76_valid :
    ∀ i : Fin firstWindowMasks76.size,
      maskSum firstWindowSeed firstWindowMasks76[i] =
        firstWindowLower + 100 * 76 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks77_valid :
    ∀ i : Fin firstWindowMasks77.size,
      maskSum firstWindowSeed firstWindowMasks77[i] =
        firstWindowLower + 100 * 77 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks78_valid :
    ∀ i : Fin firstWindowMasks78.size,
      maskSum firstWindowSeed firstWindowMasks78[i] =
        firstWindowLower + 100 * 78 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks79_valid :
    ∀ i : Fin firstWindowMasks79.size,
      maskSum firstWindowSeed firstWindowMasks79[i] =
        firstWindowLower + 100 * 79 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
