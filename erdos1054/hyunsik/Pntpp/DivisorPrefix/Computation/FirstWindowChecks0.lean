import Pntpp.DivisorPrefix.Computation.FirstWindowCore

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
