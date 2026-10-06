/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks0.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowCore

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime0 : Nat.Prime 10007 := by
  norm_num

theorem firstWindowPrime1 : Nat.Prime 10009 := by
  norm_num

theorem firstWindowPrime2 : Nat.Prime 10037 := by
  norm_num

theorem firstWindowPrime3 : Nat.Prime 10039 := by
  norm_num

theorem firstWindowPrime4 : Nat.Prime 10061 := by
  norm_num

theorem firstWindowPrime5 : Nat.Prime 10067 := by
  norm_num

theorem firstWindowPrime6 : Nat.Prime 10069 := by
  norm_num

theorem firstWindowPrime7 : Nat.Prime 10079 := by
  norm_num

theorem firstWindowPrime8 : Nat.Prime 10091 := by
  norm_num

theorem firstWindowPrime9 : Nat.Prime 10093 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks0_valid :
    ∀ i : Fin firstWindowMasks0.size,
      maskSum firstWindowSeed firstWindowMasks0[i] =
        firstWindowLower + 100 * 0 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks1_valid :
    ∀ i : Fin firstWindowMasks1.size,
      maskSum firstWindowSeed firstWindowMasks1[i] =
        firstWindowLower + 100 * 1 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks2_valid :
    ∀ i : Fin firstWindowMasks2.size,
      maskSum firstWindowSeed firstWindowMasks2[i] =
        firstWindowLower + 100 * 2 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks3_valid :
    ∀ i : Fin firstWindowMasks3.size,
      maskSum firstWindowSeed firstWindowMasks3[i] =
        firstWindowLower + 100 * 3 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks4_valid :
    ∀ i : Fin firstWindowMasks4.size,
      maskSum firstWindowSeed firstWindowMasks4[i] =
        firstWindowLower + 100 * 4 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks5_valid :
    ∀ i : Fin firstWindowMasks5.size,
      maskSum firstWindowSeed firstWindowMasks5[i] =
        firstWindowLower + 100 * 5 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks6_valid :
    ∀ i : Fin firstWindowMasks6.size,
      maskSum firstWindowSeed firstWindowMasks6[i] =
        firstWindowLower + 100 * 6 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks7_valid :
    ∀ i : Fin firstWindowMasks7.size,
      maskSum firstWindowSeed firstWindowMasks7[i] =
        firstWindowLower + 100 * 7 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks8_valid :
    ∀ i : Fin firstWindowMasks8.size,
      maskSum firstWindowSeed firstWindowMasks8[i] =
        firstWindowLower + 100 * 8 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks9_valid :
    ∀ i : Fin firstWindowMasks9.size,
      maskSum firstWindowSeed firstWindowMasks9[i] =
        firstWindowLower + 100 * 9 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
