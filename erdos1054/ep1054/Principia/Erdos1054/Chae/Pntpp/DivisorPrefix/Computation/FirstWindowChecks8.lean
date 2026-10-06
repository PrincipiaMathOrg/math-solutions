/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks8.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks7

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime80 : Nat.Prime 10739 := by
  norm_num

theorem firstWindowPrime81 : Nat.Prime 10753 := by
  norm_num

theorem firstWindowPrime82 : Nat.Prime 10771 := by
  norm_num

theorem firstWindowPrime83 : Nat.Prime 10781 := by
  norm_num

theorem firstWindowPrime84 : Nat.Prime 10789 := by
  norm_num

theorem firstWindowPrime85 : Nat.Prime 10799 := by
  norm_num

theorem firstWindowPrime86 : Nat.Prime 10831 := by
  norm_num

theorem firstWindowPrime87 : Nat.Prime 10837 := by
  norm_num

theorem firstWindowPrime88 : Nat.Prime 10847 := by
  norm_num

theorem firstWindowPrime89 : Nat.Prime 10853 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks80_valid :
    ∀ i : Fin firstWindowMasks80.size,
      maskSum firstWindowSeed firstWindowMasks80[i] =
        firstWindowLower + 100 * 80 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks81_valid :
    ∀ i : Fin firstWindowMasks81.size,
      maskSum firstWindowSeed firstWindowMasks81[i] =
        firstWindowLower + 100 * 81 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks82_valid :
    ∀ i : Fin firstWindowMasks82.size,
      maskSum firstWindowSeed firstWindowMasks82[i] =
        firstWindowLower + 100 * 82 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks83_valid :
    ∀ i : Fin firstWindowMasks83.size,
      maskSum firstWindowSeed firstWindowMasks83[i] =
        firstWindowLower + 100 * 83 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks84_valid :
    ∀ i : Fin firstWindowMasks84.size,
      maskSum firstWindowSeed firstWindowMasks84[i] =
        firstWindowLower + 100 * 84 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks85_valid :
    ∀ i : Fin firstWindowMasks85.size,
      maskSum firstWindowSeed firstWindowMasks85[i] =
        firstWindowLower + 100 * 85 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks86_valid :
    ∀ i : Fin firstWindowMasks86.size,
      maskSum firstWindowSeed firstWindowMasks86[i] =
        firstWindowLower + 100 * 86 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks87_valid :
    ∀ i : Fin firstWindowMasks87.size,
      maskSum firstWindowSeed firstWindowMasks87[i] =
        firstWindowLower + 100 * 87 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks88_valid :
    ∀ i : Fin firstWindowMasks88.size,
      maskSum firstWindowSeed firstWindowMasks88[i] =
        firstWindowLower + 100 * 88 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks89_valid :
    ∀ i : Fin firstWindowMasks89.size,
      maskSum firstWindowSeed firstWindowMasks89[i] =
        firstWindowLower + 100 * 89 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
