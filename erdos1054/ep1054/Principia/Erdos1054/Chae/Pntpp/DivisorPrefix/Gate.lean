/-
Copyright (c) 2026 PrincipiaAI. Released under the Apache License, Version 2.0.
Audit script only: the declarations it names are Hyunsik Chae's (ported).
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.AsymptoticBridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Bq
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.DivisorList
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.ExplicitBridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.FirstWindowBridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.FullCoverage
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.GoldbachTail
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.KernelNumerics
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.LargeBridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Main
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.PrimeWindow
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.RangeCoverage
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.SmallValues
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Statement
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.SubsetSums

set_option autoImplicit false

/-!
# Axiom gate for `Principia/Erdos1054/Chae/Pntpp/DivisorPrefix/`

Every public theorem of the ported files in this directory (118 declarations), one `#print axioms` each. Acceptance: each reads
`[propext, Classical.choice, Quot.sound]` or a subset. Private helpers are not addressable
from a gate; their axioms appear in the footprints of the public theorems that use them.
-/

-- AsymptoticBridge.lean
#print axioms Pntpp.DivisorPrefix.pnt_explicit_prime_count_lower
#print axioms Pntpp.DivisorPrefix.pnt_explicit_prime_count_upper
#print axioms Pntpp.DivisorPrefix.pnt_explicit_prime_count_interval_lower

-- Bq.lean
#print axioms Pntpp.DivisorPrefix.divisorList_mul_prime_of_lt
#print axioms Pntpp.DivisorPrefix.divisorList_mul_prime_take
#print axioms Pntpp.DivisorPrefix.prefixDivisorSum_mul_prime_add
#print axioms Pntpp.DivisorPrefix.represents_divisorSum_add_prime_mul_prefix

-- DivisorList.lean
#print axioms Pntpp.DivisorPrefix.mem_divisorList
#print axioms Pntpp.DivisorPrefix.divisorList_sorted
#print axioms Pntpp.DivisorPrefix.divisorList_nodup
#print axioms Pntpp.DivisorPrefix.positive_of_mem_divisorList
#print axioms Pntpp.DivisorPrefix.divisorList_eq_one_cons
#print axioms Pntpp.DivisorPrefix.prefixDivisorSum_one
#print axioms Pntpp.DivisorPrefix.divisorList_nonempty
#print axioms Pntpp.DivisorPrefix.divisorList_prime
#print axioms Pntpp.DivisorPrefix.divisorList_four
#print axioms Pntpp.DivisorPrefix.prefix_length_le_sum
#print axioms Pntpp.DivisorPrefix.three_le_prefixDivisorSum_two
#print axioms Pntpp.DivisorPrefix.six_le_prefixDivisorSum_three
#print axioms Pntpp.DivisorPrefix.prefixDivisorSum_two_ne_five

-- ExplicitBridge.lean
#print axioms Pntpp.DivisorPrefix.primeBatch_card
#print axioms Pntpp.DivisorPrefix.primeBatch_left_mul_card_le_sum
#print axioms Pntpp.DivisorPrefix.subsetSum_extend_primeBatch
#print axioms Pntpp.DivisorPrefix.subsetSum_extend_bounded_finset
#print axioms Pntpp.DivisorPrefix.disjoint_primeBatch_of_upper
#print axioms Pntpp.DivisorPrefix.primeBatch_upper
#print axioms Pntpp.DivisorPrefix.primeBatch_prime
#print axioms Pntpp.DivisorPrefix.primeBatch_left_lt
#print axioms Pntpp.DivisorPrefix.upper_union_primeBatch
#print axioms Pntpp.DivisorPrefix.pnt_pi_nat
#print axioms Pntpp.DivisorPrefix.primeBatch_card_lower
#print axioms Pntpp.DivisorPrefix.primeBatch_card_lower_of_log_bounds
#print axioms Pntpp.DivisorPrefix.primeBatch_one_card_lower
#print axioms Pntpp.DivisorPrefix.primeBatch_two_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock0_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock1_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock2_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock3_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock4_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock5_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock6_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock7_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock8_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock9_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock10_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock11_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock12_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock13_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgeBlock14_card_lower
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseTwo_upper
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseThree_upper
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseTwo_prime
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseThree_prime
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseTwo_lower
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseThree_lower
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseThree_mass
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseTwo_mass
#print axioms Pntpp.DivisorPrefix.largeBridgePhaseTwo_mass_reaches_final_batch
#print axioms Pntpp.DivisorPrefix.largeBridge_total_mass_reaches_tail

-- FirstWindowBridge.lean
#print axioms Pntpp.DivisorPrefix.firstWindowBridgePrimes_prime
#print axioms Pntpp.DivisorPrefix.firstWindowBridgePrimes_lower
#print axioms Pntpp.DivisorPrefix.firstWindowBridgePrimes_upper
#print axioms Pntpp.DivisorPrefix.firstWindowBridgePrimes_sum
#print axioms Pntpp.DivisorPrefix.firstWindowBridge_chain
#print axioms Pntpp.DivisorPrefix.firstWindow_extended_subsetSum
#print axioms Pntpp.DivisorPrefix.firstWindowBridgeSet_prime
#print axioms Pntpp.DivisorPrefix.firstWindowBridgeSet_lower
#print axioms Pntpp.DivisorPrefix.firstWindowBridgeSet_upper
#print axioms Pntpp.DivisorPrefix.firstWindow_bridge_representation

-- FullCoverage.lean
#print axioms Pntpp.DivisorPrefix.represents_six_le_of_helfgott
#print axioms Pntpp.DivisorPrefix.targetClassification_of_helfgott

-- GoldbachTail.lean
#print axioms Pntpp.DivisorPrefix.small_divisor_of_pairwise_large_prime_product
#print axioms Pntpp.DivisorPrefix.pairwise_large_prime_prefix
#print axioms Pntpp.DivisorPrefix.represents_one_add_sum_of_pairwise_large_prime_finset
#print axioms Pntpp.DivisorPrefix.evenTailWindowMargin
#print axioms Pntpp.DivisorPrefix.represents_even_tail_of_windowMargin
#print axioms Pntpp.DivisorPrefix.shortLogPrimeHypothesis
#print axioms Pntpp.DivisorPrefix.oddTailWindowMargin
#print axioms Pntpp.DivisorPrefix.represents_odd_tail_of_windowMargins
#print axioms Pntpp.DivisorPrefix.represents_odd_tail_of_windowMargin
#print axioms Pntpp.DivisorPrefix.represents_goldbach_tail_of_windowMargins
#print axioms Pntpp.DivisorPrefix.represents_goldbach_tail

-- KernelNumerics.lean
#print axioms Pntpp.DivisorPrefix.KernelNumerics.exp_nat_upper
#print axioms Pntpp.DivisorPrefix.KernelNumerics.exp_nat_lower
#print axioms Pntpp.DivisorPrefix.KernelNumerics.log_lower_of_power
#print axioms Pntpp.DivisorPrefix.KernelNumerics.log_upper_of_power
#print axioms Pntpp.DivisorPrefix.KernelNumerics.exp31_upper
#print axioms Pntpp.DivisorPrefix.KernelNumerics.exp60_upper
#print axioms Pntpp.DivisorPrefix.KernelNumerics.exp63_lower
#print axioms Pntpp.DivisorPrefix.KernelNumerics.exp31_ratio

-- LargeBridge.lean
#print axioms Pntpp.DivisorPrefix.largeSeed_initial_subsetSum
#print axioms Pntpp.DivisorPrefix.largeSeed_bridge_subsetSum
#print axioms Pntpp.DivisorPrefix.largeSeed_first_extension_subsetSum
#print axioms Pntpp.DivisorPrefix.largeSeed_first_extension_bertrand_ready
#print axioms Pntpp.DivisorPrefix.largeSeed_first_extension_representation
#print axioms Pntpp.DivisorPrefix.largeSeed_bridge_representation
#print axioms Pntpp.DivisorPrefix.largeSeed_explicitBridge_subsetSum
#print axioms Pntpp.DivisorPrefix.largeSeed_explicitBridge_representation_through
#print axioms Pntpp.DivisorPrefix.largeSeed_explicitBridge_representation

-- Main.lean
#print axioms Pntpp.DivisorPrefix.targetClassification_of_six_le

-- PrimeWindow.lean
#print axioms Pntpp.DivisorPrefix.small_divisor_of_prime_product
#print axioms Pntpp.DivisorPrefix.prime_window_prefix
#print axioms Pntpp.DivisorPrefix.represents_one_add_sum_of_prefix
#print axioms Pntpp.DivisorPrefix.represents_one_add_sum_of_prime_finset
#print axioms Pntpp.DivisorPrefix.represents_succ_of_subsetSum_prime_window

-- RangeCoverage.lean
#print axioms Pntpp.DivisorPrefix.represents_six_to_firstWindowBridge

-- SmallValues.lean
#print axioms Pntpp.DivisorPrefix.represents_one
#print axioms Pntpp.DivisorPrefix.represents_three
#print axioms Pntpp.DivisorPrefix.represents_four
#print axioms Pntpp.DivisorPrefix.represents_seven
#print axioms Pntpp.DivisorPrefix.not_represents_two
#print axioms Pntpp.DivisorPrefix.not_represents_five
#print axioms Pntpp.DivisorPrefix.two_and_five_impossible

-- Statement.lean

-- SubsetSums.lean
#print axioms Pntpp.DivisorPrefix.subsetSum_interval_extension
#print axioms Pntpp.DivisorPrefix.subsetSum_extension_chain
#print axioms Pntpp.DivisorPrefix.isSubsetSumExtensionChain_of_bounded_list
#print axioms Pntpp.DivisorPrefix.subsetSum_extend_bounded_list
#print axioms Pntpp.DivisorPrefix.subsetSum_bertrand_extension
