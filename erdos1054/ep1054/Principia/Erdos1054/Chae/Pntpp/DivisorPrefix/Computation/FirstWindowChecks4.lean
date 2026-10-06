/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks4.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks3

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime40 : Nat.Prime 10343 := by
  norm_num

theorem firstWindowPrime41 : Nat.Prime 10357 := by
  norm_num

theorem firstWindowPrime42 : Nat.Prime 10369 := by
  norm_num

theorem firstWindowPrime43 : Nat.Prime 10391 := by
  norm_num

theorem firstWindowPrime44 : Nat.Prime 10399 := by
  norm_num

theorem firstWindowPrime45 : Nat.Prime 10427 := by
  norm_num

theorem firstWindowPrime46 : Nat.Prime 10429 := by
  norm_num

theorem firstWindowPrime47 : Nat.Prime 10433 := by
  norm_num

theorem firstWindowPrime48 : Nat.Prime 10453 := by
  norm_num

theorem firstWindowPrime49 : Nat.Prime 10457 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks40_valid :
    ∀ i : Fin firstWindowMasks40.size,
      maskSum firstWindowSeed firstWindowMasks40[i] =
        firstWindowLower + 100 * 40 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks41_valid :
    ∀ i : Fin firstWindowMasks41.size,
      maskSum firstWindowSeed firstWindowMasks41[i] =
        firstWindowLower + 100 * 41 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks42_valid :
    ∀ i : Fin firstWindowMasks42.size,
      maskSum firstWindowSeed firstWindowMasks42[i] =
        firstWindowLower + 100 * 42 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks43_valid :
    ∀ i : Fin firstWindowMasks43.size,
      maskSum firstWindowSeed firstWindowMasks43[i] =
        firstWindowLower + 100 * 43 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks44_valid :
    ∀ i : Fin firstWindowMasks44.size,
      maskSum firstWindowSeed firstWindowMasks44[i] =
        firstWindowLower + 100 * 44 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks45_valid :
    ∀ i : Fin firstWindowMasks45.size,
      maskSum firstWindowSeed firstWindowMasks45[i] =
        firstWindowLower + 100 * 45 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks46_valid :
    ∀ i : Fin firstWindowMasks46.size,
      maskSum firstWindowSeed firstWindowMasks46[i] =
        firstWindowLower + 100 * 46 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks47_valid :
    ∀ i : Fin firstWindowMasks47.size,
      maskSum firstWindowSeed firstWindowMasks47[i] =
        firstWindowLower + 100 * 47 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks48_valid :
    ∀ i : Fin firstWindowMasks48.size,
      maskSum firstWindowSeed firstWindowMasks48[i] =
        firstWindowLower + 100 * 48 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks49_valid :
    ∀ i : Fin firstWindowMasks49.size,
      maskSum firstWindowSeed firstWindowMasks49[i] =
        firstWindowLower + 100 * 49 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
