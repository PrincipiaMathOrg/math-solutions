import Pntpp.DivisorPrefix.Computation.FirstWindowChecks9

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
