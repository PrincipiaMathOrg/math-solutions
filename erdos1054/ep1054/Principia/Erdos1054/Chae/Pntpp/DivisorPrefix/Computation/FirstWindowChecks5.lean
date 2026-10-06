/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/FirstWindowChecks5.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks4

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime50 : Nat.Prime 10459 := by
  norm_num

theorem firstWindowPrime51 : Nat.Prime 10463 := by
  norm_num

theorem firstWindowPrime52 : Nat.Prime 10477 := by
  norm_num

theorem firstWindowPrime53 : Nat.Prime 10487 := by
  norm_num

theorem firstWindowPrime54 : Nat.Prime 10499 := by
  norm_num

theorem firstWindowPrime55 : Nat.Prime 10501 := by
  norm_num

theorem firstWindowPrime56 : Nat.Prime 10513 := by
  norm_num

theorem firstWindowPrime57 : Nat.Prime 10529 := by
  norm_num

theorem firstWindowPrime58 : Nat.Prime 10531 := by
  norm_num

theorem firstWindowPrime59 : Nat.Prime 10559 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks50_valid :
    ∀ i : Fin firstWindowMasks50.size,
      maskSum firstWindowSeed firstWindowMasks50[i] =
        firstWindowLower + 100 * 50 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks51_valid :
    ∀ i : Fin firstWindowMasks51.size,
      maskSum firstWindowSeed firstWindowMasks51[i] =
        firstWindowLower + 100 * 51 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks52_valid :
    ∀ i : Fin firstWindowMasks52.size,
      maskSum firstWindowSeed firstWindowMasks52[i] =
        firstWindowLower + 100 * 52 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks53_valid :
    ∀ i : Fin firstWindowMasks53.size,
      maskSum firstWindowSeed firstWindowMasks53[i] =
        firstWindowLower + 100 * 53 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks54_valid :
    ∀ i : Fin firstWindowMasks54.size,
      maskSum firstWindowSeed firstWindowMasks54[i] =
        firstWindowLower + 100 * 54 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks55_valid :
    ∀ i : Fin firstWindowMasks55.size,
      maskSum firstWindowSeed firstWindowMasks55[i] =
        firstWindowLower + 100 * 55 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks56_valid :
    ∀ i : Fin firstWindowMasks56.size,
      maskSum firstWindowSeed firstWindowMasks56[i] =
        firstWindowLower + 100 * 56 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks57_valid :
    ∀ i : Fin firstWindowMasks57.size,
      maskSum firstWindowSeed firstWindowMasks57[i] =
        firstWindowLower + 100 * 57 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks58_valid :
    ∀ i : Fin firstWindowMasks58.size,
      maskSum firstWindowSeed firstWindowMasks58[i] =
        firstWindowLower + 100 * 58 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks59_valid :
    ∀ i : Fin firstWindowMasks59.size,
      maskSum firstWindowSeed firstWindowMasks59[i] =
        firstWindowLower + 100 * 59 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
