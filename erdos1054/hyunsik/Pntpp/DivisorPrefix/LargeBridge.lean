import Pntpp.DivisorPrefix.Computation.LargeSeedKernel
import Pntpp.DivisorPrefix.ExplicitBridge
import Pntpp.DivisorPrefix.PrimeWindow

namespace Pntpp.DivisorPrefix

set_option maxRecDepth 100000

open Computation

/-- The explicit finite data still required by the large-prime-mass bridge.
The analytic task is to certify such a chain from Rosser--Schoenfeld prime-counting bounds. -/
structure LargeBridgeCertificate (X : ℕ) where
  primes : List ℕ
  chain : IsSubsetSumExtensionChain largeSeedPrimeWindow largeSeedStart largeSeedEnd primes
  prime : ∀ p ∈ primes, p.Prime
  lower : ∀ p ∈ primes, largeSeedPrimeLower < p
  upper : ∀ p ∈ primes, p ≤ X

/-- The full large-seed certificate gives the initial subset-sum interval used by the bridge. -/
theorem largeSeed_initial_subsetSum :
    ∀ n, largeSeedStart ≤ n → n ≤ largeSeedEnd → IsSubsetSum largeSeedPrimeWindow n :=
  largeSeedGenerated_full

/-- Any certified extension chain from the large seed covers its whole accumulated interval. -/
theorem largeSeed_bridge_subsetSum {X : ℕ} (certificate : LargeBridgeCertificate X) :
    ∀ n, largeSeedStart ≤ n → n ≤ largeSeedEnd + certificate.primes.sum →
      IsSubsetSum (largeSeedPrimeWindow ∪ certificate.primes.toFinset) n := by
  exact subsetSum_extension_chain (by simp [largeSeedStart, largeSeedEnd])
    largeSeed_initial_subsetSum certificate.chain

/-- A checked prime just beyond the generated large seed establishes the first deterministic
extension of its interval. -/
theorem largeSeed_first_extension_subsetSum :
    ∀ n, largeSeedStart ≤ n → n ≤ largeSeedEnd + 40000003 →
      IsSubsetSum (insert 40000003 largeSeedPrimeWindow) n := by
  exact subsetSum_interval_extension
    (A := largeSeedPrimeWindow) (C := largeSeedStart) (U := largeSeedEnd) (p := 40000003)
    (by norm_num [largeSeedStart, largeSeedEnd])
    (by simp [largeSeedPrimeWindow, largeSeedPrimeLower, largeSeedPrimeUpper])
    largeSeedGenerated_full
    (by norm_num [largeSeedStart, largeSeedEnd])

/-- The first deterministic extension is already large enough to enter the ordinary Bertrand
extension regime: its new interval width exceeds twice its largest selected prime. -/
theorem largeSeed_first_extension_bertrand_ready :
    2 * 40000003 ≤ (largeSeedEnd + 40000003) - largeSeedStart + 1 := by
  norm_num [largeSeedStart, largeSeedEnd]

/-- The checked first extension also yields actual divisor-prefix representations. -/
theorem largeSeed_first_extension_representation :
    ∀ n, largeSeedStart + 1 ≤ n → n ≤ largeSeedEnd + 40000003 + 1 → Represents n := by
  intro n hnLower hnUpper
  have hnPos : 1 ≤ n := by
    omega
  have hnSubset : IsSubsetSum (insert 40000003 largeSeedPrimeWindow) (n - 1) :=
    largeSeed_first_extension_subsetSum (n - 1) (by omega) (by omega)
  have hprime : ∀ p ∈ insert 40000003 largeSeedPrimeWindow, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · norm_num
    · exact (Finset.mem_filter.mp hp).2
  have hlower : ∀ p ∈ insert 40000003 largeSeedPrimeWindow, largeSeedPrimeLower < p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · norm_num [largeSeedPrimeLower]
    · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).1
  have hupper : ∀ p ∈ insert 40000003 largeSeedPrimeWindow, p ≤ 40000003 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rfl
    · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).2.le.trans
        (by norm_num [largeSeedPrimeUpper])
  have hrep :=
    represents_succ_of_subsetSum_prime_window
      (insert 40000003 largeSeedPrimeWindow) largeSeedPrimeLower 40000003 (n - 1)
      hprime hlower hupper (by norm_num [largeSeedPrimeLower]) hnSubset
  simpa [Nat.sub_add_cancel hnPos] using hrep

/-- The source's prime-mass certificate, once supplied as a finite extension chain, produces
actual divisor-prefix representations throughout the bridge interval. -/
theorem largeSeed_bridge_representation {X : ℕ} (certificate : LargeBridgeCertificate X)
    (hseedUpper : largeSeedPrimeUpper ≤ X)
    (hwindow : X < largeSeedPrimeLower * largeSeedPrimeLower) :
    ∀ n, largeSeedStart + 1 ≤ n → n ≤ largeSeedEnd + certificate.primes.sum + 1 →
      Represents n := by
  intro n hnLower hnUpper
  have hnPos : 1 ≤ n := by
    omega
  have hnSubset :
      IsSubsetSum (largeSeedPrimeWindow ∪ certificate.primes.toFinset) (n - 1) :=
    largeSeed_bridge_subsetSum certificate (n - 1) (by omega) (by omega)
  have hprime : ∀ p ∈ largeSeedPrimeWindow ∪ certificate.primes.toFinset, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).2
    · exact certificate.prime p (by simpa using hp)
  have hlower : ∀ p ∈ largeSeedPrimeWindow ∪ certificate.primes.toFinset,
      largeSeedPrimeLower < p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).1
    · exact certificate.lower p (by simpa using hp)
  have hupper : ∀ p ∈ largeSeedPrimeWindow ∪ certificate.primes.toFinset, p ≤ X := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).2.le.trans hseedUpper
    · exact certificate.upper p (by simpa using hp)
  have hrep :=
    represents_succ_of_subsetSum_prime_window
      (largeSeedPrimeWindow ∪ certificate.primes.toFinset) largeSeedPrimeLower X (n - 1)
      hprime hlower hupper hwindow hnSubset
  simpa [Nat.sub_add_cancel hnPos] using hrep

/-- Keep arithmetic normalization abstract in the finite prime mass. -/
private theorem phaseTwo_width_of_mass (mass : ℕ) (h : 80000006000000 ≤ mass) :
    80000097000004 ≤ (largeSeedEnd + 40000003 + mass) - largeSeedStart + 1 := by
  dsimp [largeSeedStart, largeSeedEnd]
  omega

private theorem bridge_reaches_tail_of_masses (m₀ m₁ m₂ : ℕ)
    (h₀ : 40000003 * 2000000 ≤ m₀)
    (h₁ : 16120377708588 * 869456808510 + 48361133125764 * 571519023209 ≤ m₁)
    (h₂ : 80000097000004 * 4109612035042 + 240000291000012 * 2770250302992 ≤ m₂) :
    1000000000000000000100000000 ≤ largeSeedEnd + 40000003 + m₀ + m₁ + m₂ + 1 := by
  dsimp [largeSeedEnd]
  omega

/-- The explicit PNT+ batches extend the large seed through the whole finite bridge. -/
theorem largeSeed_explicitBridge_subsetSum [DusartBounds] :
    ∀ n, largeSeedStart ≤ n →
      n ≤ largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id +
        largeBridgePhaseTwo.sum id + largeBridgePhaseThree.sum id →
      IsSubsetSum
        (((insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
          largeBridgePhaseTwo) ∪ largeBridgePhaseThree) n := by
  have hfirstCover :
      ∀ n, largeSeedStart ≤ n → n ≤ largeSeedEnd + 40000003 →
        IsSubsetSum (insert 40000003 largeSeedPrimeWindow) n :=
    largeSeed_first_extension_subsetSum
  have hfirstUpper : ∀ p ∈ insert 40000003 largeSeedPrimeWindow, p ≤ 40000003 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rfl
    · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).2.le.trans
        (by norm_num [largeSeedPrimeUpper])
  have hbatchDisjoint : Disjoint (insert 40000003 largeSeedPrimeWindow)
      (primeBatch 40000003 91000004) :=
    disjoint_primeBatch_of_upper hfirstUpper
  have hbatchMass : 80000006000000 ≤ (primeBatch 40000003 91000004).sum id := by
    calc
      80000006000000 ≤ 40000003 * 2000000 := by norm_num
      _ ≤ (primeBatch 40000003 91000004).sum id :=
        (Nat.mul_le_mul_left _ primeBatch_one_card_lower).trans
          (primeBatch_left_mul_card_le_sum _ _)
  have hbatchCover := subsetSum_extend_primeBatch
    (C := largeSeedStart) (U := largeSeedEnd + 40000003)
    (a := 40000003) (b := 91000004)
    (by norm_num [largeSeedStart, largeSeedEnd]) hfirstCover hbatchDisjoint
    (by norm_num [largeSeedStart, largeSeedEnd])
  have hbatchUpper : ∀ p ∈ insert 40000003 largeSeedPrimeWindow ∪
      primeBatch 40000003 91000004, p ≤ 16120377708588 := by
    intro p hp
    exact (upper_union_primeBatch (a := 40000003) (b := 91000004)
      (by norm_num) hfirstUpper p hp).trans (by norm_num)
  have hphaseTwoDisjoint : Disjoint
      (insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004)
      largeBridgePhaseTwo := by
    rw [largeBridgePhaseTwo, Finset.disjoint_union_right]
    constructor
    · apply disjoint_primeBatch_of_upper
      exact fun p hp ↦ (hbatchUpper p hp).trans (by norm_num)
    · apply disjoint_primeBatch_of_upper
      exact fun p hp ↦ (hbatchUpper p hp).trans (by norm_num)
  have hphaseTwoWidth : 80000097000004 ≤
      (largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id) -
        largeSeedStart + 1 := by
    exact phaseTwo_width_of_mass _ hbatchMass
  have hphaseTwoCover := subsetSum_extend_bounded_finset
    (A := insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004)
    (S := largeBridgePhaseTwo)
    (C := largeSeedStart)
    (U := largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id)
    (by omega) hbatchCover hphaseTwoDisjoint (by
      intro p hp
      exact (largeBridgePhaseTwo_upper p hp).trans hphaseTwoWidth)
  have hphaseTwoUpper : ∀ p ∈
      (insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
        largeBridgePhaseTwo, p ≤ 80000097000004 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (hbatchUpper p hp).trans (by norm_num)
    · exact largeBridgePhaseTwo_upper p hp
  have hphaseThreeDisjoint : Disjoint
      ((insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
        largeBridgePhaseTwo) largeBridgePhaseThree := by
    rw [largeBridgePhaseThree, Finset.disjoint_union_right]
    constructor
    · apply disjoint_primeBatch_of_upper
      exact fun p hp ↦ (hphaseTwoUpper p hp).trans (by norm_num)
    · apply disjoint_primeBatch_of_upper
      exact fun p hp ↦ (hphaseTwoUpper p hp).trans (by norm_num)
  have hphaseThreeWidth : 399000000000000 ≤
      (largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id +
        largeBridgePhaseTwo.sum id) - largeSeedStart + 1 := by
    have hphaseTwoMass := largeBridgePhaseTwo_mass
    omega
  have hphaseThreeCover := subsetSum_extend_bounded_finset
    (A := (insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
      largeBridgePhaseTwo)
    (S := largeBridgePhaseThree)
    (C := largeSeedStart)
    (U := largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id +
      largeBridgePhaseTwo.sum id)
    (by
      calc
        largeSeedStart ≤ largeSeedEnd := by norm_num [largeSeedStart, largeSeedEnd]
        _ ≤ largeSeedEnd + 40000003 := Nat.le_add_right _ _
        _ ≤ largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id :=
          Nat.le_add_right _ _
        _ ≤ largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id +
            largeBridgePhaseTwo.sum id := Nat.le_add_right _ _)
      hphaseTwoCover hphaseThreeDisjoint (by
      intro p hp
      exact (largeBridgePhaseThree_upper p hp).trans hphaseThreeWidth)
  exact hphaseThreeCover

theorem largeSeed_explicitBridge_representation_through [DusartBounds] :
    ∀ n, largeSeedStart + 1 ≤ n →
      n ≤ largeSeedEnd + 40000003 + (primeBatch 40000003 91000004).sum id +
        largeBridgePhaseTwo.sum id + largeBridgePhaseThree.sum id + 1 → Represents n := by
  intro n hnLower hnUpper
  have hnPos : 1 ≤ n := by omega
  have hnSubset := largeSeed_explicitBridge_subsetSum (n - 1) (by omega) (by omega)
  have hprime : ∀ p ∈
      ((insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
        largeBridgePhaseTwo) ∪ largeBridgePhaseThree, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_insert.mp hp with rfl | hp
          · norm_num
          · exact (Finset.mem_filter.mp hp).2
        · exact primeBatch_prime _ _ p hp
      · exact largeBridgePhaseTwo_prime p hp
    · exact largeBridgePhaseThree_prime p hp
  have hlower : ∀ p ∈
      ((insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
        largeBridgePhaseTwo) ∪ largeBridgePhaseThree, largeSeedPrimeLower < p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_insert.mp hp with rfl | hp
          · norm_num [largeSeedPrimeLower]
          · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).1
        · exact (by norm_num [largeSeedPrimeLower] : largeSeedPrimeLower < 40000003).trans
            (primeBatch_left_lt _ _ p hp)
      · exact largeBridgePhaseTwo_lower p hp
    · exact largeBridgePhaseThree_lower p hp
  have hupper : ∀ p ∈
      ((insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
        largeBridgePhaseTwo) ∪ largeBridgePhaseThree, p ≤ 399000000000000 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_insert.mp hp with rfl | hp
          · norm_num
          · exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hp).1).2.le.trans
              (by norm_num [largeSeedPrimeUpper])
        · exact (primeBatch_upper _ _ p hp).trans (by norm_num)
      · exact (largeBridgePhaseTwo_upper p hp).trans (by norm_num)
    · exact largeBridgePhaseThree_upper p hp
  have hrep := represents_succ_of_subsetSum_prime_window
    (((insert 40000003 largeSeedPrimeWindow ∪ primeBatch 40000003 91000004) ∪
      largeBridgePhaseTwo) ∪ largeBridgePhaseThree)
    largeSeedPrimeLower 399000000000000 (n - 1) hprime hlower hupper
    (by norm_num [largeSeedPrimeLower]) hnSubset
  simpa [Nat.sub_add_cancel hnPos] using hrep

set_option maxRecDepth 100000 in
theorem largeSeed_explicitBridge_representation [DusartBounds] :
    ∀ n, largeSeedStart + 1 ≤ n →
      n ≤ 1000000000000000000100000000 → Represents n := by
  intro n hnLower hnUpper
  apply largeSeed_explicitBridge_representation_through n hnLower
  have hbatchMass : 40000003 * 2000000 ≤ (primeBatch 40000003 91000004).sum id :=
    (Nat.mul_le_mul_left _ primeBatch_one_card_lower).trans
      (primeBatch_left_mul_card_le_sum _ _)
  exact hnUpper.trans (bridge_reaches_tail_of_masses _ _ _ hbatchMass
    largeBridgePhaseTwo_mass largeBridgePhaseThree_mass)

end Pntpp.DivisorPrefix
