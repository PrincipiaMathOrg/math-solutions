/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks1.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks0

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime10 : Nat.Prime 10099 := by
  norm_num

theorem firstWindowPrime11 : Nat.Prime 10103 := by
  norm_num

theorem firstWindowPrime12 : Nat.Prime 10111 := by
  norm_num

theorem firstWindowPrime13 : Nat.Prime 10133 := by
  norm_num

theorem firstWindowPrime14 : Nat.Prime 10139 := by
  norm_num

theorem firstWindowPrime15 : Nat.Prime 10141 := by
  norm_num

theorem firstWindowPrime16 : Nat.Prime 10151 := by
  norm_num

theorem firstWindowPrime17 : Nat.Prime 10159 := by
  norm_num

theorem firstWindowPrime18 : Nat.Prime 10163 := by
  norm_num

theorem firstWindowPrime19 : Nat.Prime 10169 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks10_valid :
    ∀ i : Fin firstWindowMasks10.size,
      maskSum firstWindowSeed firstWindowMasks10[i] =
        firstWindowLower + 100 * 10 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks11_valid :
    ∀ i : Fin firstWindowMasks11.size,
      maskSum firstWindowSeed firstWindowMasks11[i] =
        firstWindowLower + 100 * 11 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks12_valid :
    ∀ i : Fin firstWindowMasks12.size,
      maskSum firstWindowSeed firstWindowMasks12[i] =
        firstWindowLower + 100 * 12 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks13_valid :
    ∀ i : Fin firstWindowMasks13.size,
      maskSum firstWindowSeed firstWindowMasks13[i] =
        firstWindowLower + 100 * 13 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks14_valid :
    ∀ i : Fin firstWindowMasks14.size,
      maskSum firstWindowSeed firstWindowMasks14[i] =
        firstWindowLower + 100 * 14 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks15_valid :
    ∀ i : Fin firstWindowMasks15.size,
      maskSum firstWindowSeed firstWindowMasks15[i] =
        firstWindowLower + 100 * 15 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks16_valid :
    ∀ i : Fin firstWindowMasks16.size,
      maskSum firstWindowSeed firstWindowMasks16[i] =
        firstWindowLower + 100 * 16 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks17_valid :
    ∀ i : Fin firstWindowMasks17.size,
      maskSum firstWindowSeed firstWindowMasks17[i] =
        firstWindowLower + 100 * 17 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks18_valid :
    ∀ i : Fin firstWindowMasks18.size,
      maskSum firstWindowSeed firstWindowMasks18[i] =
        firstWindowLower + 100 * 18 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks19_valid :
    ∀ i : Fin firstWindowMasks19.size,
      maskSum firstWindowSeed firstWindowMasks19[i] =
        firstWindowLower + 100 * 19 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
