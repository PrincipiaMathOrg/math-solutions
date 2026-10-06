import Pntpp.DivisorPrefix.Computation.FirstWindowChecks2

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime30 : Nat.Prime 10271 := by
  norm_num

theorem firstWindowPrime31 : Nat.Prime 10273 := by
  norm_num

theorem firstWindowPrime32 : Nat.Prime 10289 := by
  norm_num

theorem firstWindowPrime33 : Nat.Prime 10301 := by
  norm_num

theorem firstWindowPrime34 : Nat.Prime 10303 := by
  norm_num

theorem firstWindowPrime35 : Nat.Prime 10313 := by
  norm_num

theorem firstWindowPrime36 : Nat.Prime 10321 := by
  norm_num

theorem firstWindowPrime37 : Nat.Prime 10331 := by
  norm_num

theorem firstWindowPrime38 : Nat.Prime 10333 := by
  norm_num

theorem firstWindowPrime39 : Nat.Prime 10337 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks30_valid :
    ∀ i : Fin firstWindowMasks30.size,
      maskSum firstWindowSeed firstWindowMasks30[i] =
        firstWindowLower + 100 * 30 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks31_valid :
    ∀ i : Fin firstWindowMasks31.size,
      maskSum firstWindowSeed firstWindowMasks31[i] =
        firstWindowLower + 100 * 31 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks32_valid :
    ∀ i : Fin firstWindowMasks32.size,
      maskSum firstWindowSeed firstWindowMasks32[i] =
        firstWindowLower + 100 * 32 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks33_valid :
    ∀ i : Fin firstWindowMasks33.size,
      maskSum firstWindowSeed firstWindowMasks33[i] =
        firstWindowLower + 100 * 33 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks34_valid :
    ∀ i : Fin firstWindowMasks34.size,
      maskSum firstWindowSeed firstWindowMasks34[i] =
        firstWindowLower + 100 * 34 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks35_valid :
    ∀ i : Fin firstWindowMasks35.size,
      maskSum firstWindowSeed firstWindowMasks35[i] =
        firstWindowLower + 100 * 35 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks36_valid :
    ∀ i : Fin firstWindowMasks36.size,
      maskSum firstWindowSeed firstWindowMasks36[i] =
        firstWindowLower + 100 * 36 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks37_valid :
    ∀ i : Fin firstWindowMasks37.size,
      maskSum firstWindowSeed firstWindowMasks37[i] =
        firstWindowLower + 100 * 37 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks38_valid :
    ∀ i : Fin firstWindowMasks38.size,
      maskSum firstWindowSeed firstWindowMasks38[i] =
        firstWindowLower + 100 * 38 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks39_valid :
    ∀ i : Fin firstWindowMasks39.size,
      maskSum firstWindowSeed firstWindowMasks39[i] =
        firstWindowLower + 100 * 39 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
