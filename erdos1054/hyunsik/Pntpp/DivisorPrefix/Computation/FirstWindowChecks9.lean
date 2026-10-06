import Pntpp.DivisorPrefix.Computation.FirstWindowChecks8

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowPrime90 : Nat.Prime 10859 := by
  norm_num

theorem firstWindowPrime91 : Nat.Prime 10861 := by
  norm_num

theorem firstWindowPrime92 : Nat.Prime 10867 := by
  norm_num

theorem firstWindowPrime93 : Nat.Prime 10883 := by
  norm_num

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks90_valid :
    ∀ i : Fin firstWindowMasks90.size,
      maskSum firstWindowSeed firstWindowMasks90[i] =
        firstWindowLower + 100 * 90 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks91_valid :
    ∀ i : Fin firstWindowMasks91.size,
      maskSum firstWindowSeed firstWindowMasks91[i] =
        firstWindowLower + 100 * 91 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks92_valid :
    ∀ i : Fin firstWindowMasks92.size,
      maskSum firstWindowSeed firstWindowMasks92[i] =
        firstWindowLower + 100 * 92 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks93_valid :
    ∀ i : Fin firstWindowMasks93.size,
      maskSum firstWindowSeed firstWindowMasks93[i] =
        firstWindowLower + 100 * 93 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks94_valid :
    ∀ i : Fin firstWindowMasks94.size,
      maskSum firstWindowSeed firstWindowMasks94[i] =
        firstWindowLower + 100 * 94 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks95_valid :
    ∀ i : Fin firstWindowMasks95.size,
      maskSum firstWindowSeed firstWindowMasks95[i] =
        firstWindowLower + 100 * 95 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks96_valid :
    ∀ i : Fin firstWindowMasks96.size,
      maskSum firstWindowSeed firstWindowMasks96[i] =
        firstWindowLower + 100 * 96 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks97_valid :
    ∀ i : Fin firstWindowMasks97.size,
      maskSum firstWindowSeed firstWindowMasks97[i] =
        firstWindowLower + 100 * 97 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks98_valid :
    ∀ i : Fin firstWindowMasks98.size,
      maskSum firstWindowSeed firstWindowMasks98[i] =
        firstWindowLower + 100 * 98 + i := by
  decide

set_option maxHeartbeats 0 in
-- Kernel reduction checks this finite certificate without native axioms.
theorem firstWindowMasks99_valid :
    ∀ i : Fin firstWindowMasks99.size,
      maskSum firstWindowSeed firstWindowMasks99[i] =
        firstWindowLower + 100 * 99 + i := by
  decide

end Pntpp.DivisorPrefix.Computation
