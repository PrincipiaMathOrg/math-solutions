import Pntpp.DivisorPrefix.Computation.FirstWindowChecks1

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime20 : Nat.Prime 10177 := by
  norm_num

theorem firstWindowPrime21 : Nat.Prime 10181 := by
  norm_num

theorem firstWindowPrime22 : Nat.Prime 10193 := by
  norm_num

theorem firstWindowPrime23 : Nat.Prime 10211 := by
  norm_num

theorem firstWindowPrime24 : Nat.Prime 10223 := by
  norm_num

theorem firstWindowPrime25 : Nat.Prime 10243 := by
  norm_num

theorem firstWindowPrime26 : Nat.Prime 10247 := by
  norm_num

theorem firstWindowPrime27 : Nat.Prime 10253 := by
  norm_num

theorem firstWindowPrime28 : Nat.Prime 10259 := by
  norm_num

theorem firstWindowPrime29 : Nat.Prime 10267 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks20_valid :
    ∀ i : Fin firstWindowMasks20.size,
      maskSum firstWindowSeed firstWindowMasks20[i] =
        firstWindowLower + 100 * 20 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks21_valid :
    ∀ i : Fin firstWindowMasks21.size,
      maskSum firstWindowSeed firstWindowMasks21[i] =
        firstWindowLower + 100 * 21 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks22_valid :
    ∀ i : Fin firstWindowMasks22.size,
      maskSum firstWindowSeed firstWindowMasks22[i] =
        firstWindowLower + 100 * 22 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks23_valid :
    ∀ i : Fin firstWindowMasks23.size,
      maskSum firstWindowSeed firstWindowMasks23[i] =
        firstWindowLower + 100 * 23 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks24_valid :
    ∀ i : Fin firstWindowMasks24.size,
      maskSum firstWindowSeed firstWindowMasks24[i] =
        firstWindowLower + 100 * 24 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks25_valid :
    ∀ i : Fin firstWindowMasks25.size,
      maskSum firstWindowSeed firstWindowMasks25[i] =
        firstWindowLower + 100 * 25 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks26_valid :
    ∀ i : Fin firstWindowMasks26.size,
      maskSum firstWindowSeed firstWindowMasks26[i] =
        firstWindowLower + 100 * 26 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks27_valid :
    ∀ i : Fin firstWindowMasks27.size,
      maskSum firstWindowSeed firstWindowMasks27[i] =
        firstWindowLower + 100 * 27 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks28_valid :
    ∀ i : Fin firstWindowMasks28.size,
      maskSum firstWindowSeed firstWindowMasks28[i] =
        firstWindowLower + 100 * 28 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks29_valid :
    ∀ i : Fin firstWindowMasks29.size,
      maskSum firstWindowSeed firstWindowMasks29[i] =
        firstWindowLower + 100 * 29 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
