/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/ExplicitBridge.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.AsymptoticBridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.KernelNumerics
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.SubsetSums

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

set_option exponentiation.threshold 10000
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The primes in the natural interval $(a,b]$.  These finite batches are the analytic
certificates used to extend the large seed. -/
def primeBatch (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter Nat.Prime

/-- The cardinality of a prime batch is the difference of the two prime-counting functions. -/
theorem primeBatch_card (a b : ℕ) (hab : a ≤ b) :
    (primeBatch a b).card = b.primeCounting - a.primeCounting := by
  have hsub : (Finset.range (a + 1)).filter Nat.Prime ⊆
      (Finset.range (b + 1)).filter Nat.Prime := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  rw [show primeBatch a b =
      (Finset.range (b + 1)).filter Nat.Prime \ (Finset.range (a + 1)).filter Nat.Prime by
    ext n
    simp only [primeBatch, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨han, hnb⟩, hp⟩
      exact ⟨⟨by omega, hp⟩, fun h ↦ (not_le_of_gt han) (by omega)⟩
    · rintro ⟨⟨hnb, hp⟩, hnot⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra han
      exact hnot ⟨by omega, hp⟩
    , Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr hsub]
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- Every prime in a batch is at least its left endpoint, hence its sum dominates the endpoint
times its cardinality. -/
theorem primeBatch_left_mul_card_le_sum (a b : ℕ) :
    a * (primeBatch a b).card ≤ (primeBatch a b).sum id := by
  simpa [nsmul_eq_mul, Nat.mul_comm] using
    (primeBatch a b).card_nsmul_le_sum id a fun p hp ↦ (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hp).1).1.le

/-- A prime batch whose endpoint fits the current width extends a covered subset-sum interval. -/
theorem subsetSum_extend_primeBatch
    {A : Finset ℕ} {C U a b : ℕ}
    (hCU : C ≤ U)
    (hcover : ∀ n, C ≤ n → n ≤ U → IsSubsetSum A n)
    (hdisjoint : Disjoint A (primeBatch a b))
    (hwidth : b ≤ U - C + 1) :
    ∀ n, C ≤ n → n ≤ U + (primeBatch a b).sum id →
      IsSubsetSum (A ∪ primeBatch a b) n := by
  have hresult := subsetSum_extend_bounded_list (primeBatch a b).toList hCU hcover
    (by simpa using hdisjoint) (primeBatch a b).nodup_toList (by
      intro p hp
      have hp' : p ∈ primeBatch a b := by simpa using hp
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp').1).2.trans hwidth)
  simpa using hresult

/-- Finset form of bounded-list extension, retaining the finite set rather than its enumeration. -/
theorem subsetSum_extend_bounded_finset
    {A S : Finset ℕ} {C U : ℕ}
    (hCU : C ≤ U)
    (hcover : ∀ n, C ≤ n → n ≤ U → IsSubsetSum A n)
    (hdisjoint : Disjoint A S)
    (hbound : ∀ p ∈ S, p ≤ U - C + 1) :
    ∀ n, C ≤ n → n ≤ U + S.sum id → IsSubsetSum (A ∪ S) n := by
  have hresult := subsetSum_extend_bounded_list S.toList hCU hcover
    (by simpa using hdisjoint) S.nodup_toList (by
      intro p hp
      exact hbound p (by simpa using hp))
  simpa using hresult

/-- A finset bounded by the left endpoint of a new prime batch is disjoint from that batch. -/
theorem disjoint_primeBatch_of_upper {S : Finset ℕ} {a b : ℕ}
    (hupper : ∀ p ∈ S, p ≤ a) : Disjoint S (primeBatch a b) := by
  rw [Finset.disjoint_left]
  intro p hpS hpBatch
  exact (not_le_of_gt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpBatch).1).1) (hupper p hpS)

/-- Every element of a prime batch is bounded by its right endpoint. -/
theorem primeBatch_upper (a b : ℕ) : ∀ p ∈ primeBatch a b, p ≤ b := by
  intro p hp
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2

theorem primeBatch_prime (a b : ℕ) : ∀ p ∈ primeBatch a b, p.Prime := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem primeBatch_left_lt (a b : ℕ) : ∀ p ∈ primeBatch a b, a < p := by
  intro p hp
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1

/-- After adjoining a prime batch, every selected prime is bounded by that batch's endpoint. -/
theorem upper_union_primeBatch {S : Finset ℕ} {a b : ℕ}
    (hab : a ≤ b) (hupper : ∀ p ∈ S, p ≤ a) :
    ∀ p ∈ S ∪ primeBatch a b, p ≤ b := by
  intro p hp
  rcases Finset.mem_union.mp hp with hpS | hpBatch
  · exact (hupper p hpS).trans hab
  · exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpBatch).1).2

/-- The real PNT+ counting function agrees with the natural prime-counting function at a natural
argument. -/
theorem pnt_pi_nat (n : ℕ) : pi (n : ℝ) = n.primeCounting := by
  simp [pi]

/-- A numerical lower bound on the explicit PNT+ interval estimate gives the corresponding
natural lower bound on the cardinality of a prime batch. -/
theorem primeBatch_card_lower [DusartBounds] {a b k : ℕ} (ha : 17 ≤ a) (hb : 17 ≤ b) (hab : a ≤ b)
    (hbound : (k : ℝ) ≤ (b : ℝ) / Real.log b -
      1.2551 * ((a : ℝ) / Real.log a)) :
    k ≤ (primeBatch a b).card := by
  have hcount := pnt_explicit_prime_count_interval_lower
    (a := (a : ℝ)) (b := (b : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)
  rw [pnt_pi_nat, pnt_pi_nat] at hcount
  have hmono : a.primeCounting ≤ b.primeCounting := Nat.monotone_primeCounting hab
  rw [← Nat.cast_sub hmono] at hcount
  rw [primeBatch_card a b hab]
  exact_mod_cast hbound.trans hcount

/-- Logarithm enclosures reduce a concrete prime-batch estimate to a rational calculation. -/
theorem primeBatch_card_lower_of_log_bounds [DusartBounds] {a b k : ℕ} {la lb : ℝ}
    (ha : 17 ≤ a) (hb : 17 ≤ b) (hab : a ≤ b)
    (hla : 0 < la) (hlb : 0 < lb)
    (hloga : la ≤ Real.log a) (hlogb : Real.log b ≤ lb)
    (hcheck : (k : ℝ) ≤ (b : ℝ) / lb - 1.2551 * ((a : ℝ) / la)) :
    k ≤ (primeBatch a b).card := by
  apply primeBatch_card_lower ha hb hab
  have hlogaPos : 0 < Real.log a := hla.trans_le hloga
  have hlogbPos : 0 < Real.log b := Real.log_pos (by exact_mod_cast show 1 < b by omega)
  have hLower : (b : ℝ) / lb ≤ (b : ℝ) / Real.log b := by
    rw [div_le_div_iff₀ hlb hlogbPos]
    nlinarith
  have hUpper : (a : ℝ) / Real.log a ≤ (a : ℝ) / la := by
    rw [div_le_div_iff₀ hlogaPos hla]
    nlinarith
  nlinarith

/-- The first finite prime batch has at least two million elements. -/
theorem primeBatch_one_card_lower [DusartBounds] :
    2000000 ≤ (primeBatch 40000003 91000004).card := by
  apply primeBatch_card_lower (by norm_num) (by norm_num) (by norm_num)
  have hloga : (17.5 : ℝ) ≤ Real.log 40000003 := by
    convert KernelNumerics.log_lower_of_power 35 2 40000003
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hlogb : Real.log 91000004 ≤ (18.34 : ℝ) := by
    convert KernelNumerics.log_upper_of_power 917 50 91000004
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hlogaPos : 0 < Real.log 40000003 := by linarith
  have hlogbPos : 0 < Real.log 91000004 := Real.log_pos (by norm_num)
  have hLower : (91000004 : ℝ) / 18.34 ≤ (91000004 : ℝ) / Real.log 91000004 := by
    rw [div_le_div_iff₀ (by norm_num) hlogbPos]
    nlinarith
  have hUpper : (40000003 : ℝ) / Real.log 40000003 ≤ (40000003 : ℝ) / 17.5 := by
    rw [div_le_div_iff₀ hlogaPos (by norm_num)]
    nlinarith
  nlinarith

/-- The second finite prime batch has at least two trillion elements. -/
theorem primeBatch_two_card_lower [DusartBounds] :
    2000000000000 ≤ (primeBatch 91000004 80000097000004).card := by
  apply primeBatch_card_lower (by norm_num) (by norm_num) (by norm_num)
  have hloga : (18.32 : ℝ) ≤ Real.log 91000004 := by
    convert KernelNumerics.log_lower_of_power 458 25 91000004
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hlogb : Real.log 80000097000004 ≤ (32.02 : ℝ) := by
    convert KernelNumerics.log_upper_of_power 1601 50 80000097000004
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hlogaPos : 0 < Real.log 91000004 := by linarith
  have hlogbPos : 0 < Real.log 80000097000004 := Real.log_pos (by norm_num)
  have hLower : (80000097000004 : ℝ) / 32.02 ≤
      (80000097000004 : ℝ) / Real.log 80000097000004 := by
    rw [div_le_div_iff₀ (by norm_num) hlogbPos]
    nlinarith
  have hUpper : (91000004 : ℝ) / Real.log 91000004 ≤ (91000004 : ℝ) / 18.32 := by
    rw [div_le_div_iff₀ hlogaPos (by norm_num)]
    nlinarith
  nlinarith

/-- Explicit PNT+ bounds for the fifteen blocks that carry the large bridge's prime mass. -/
theorem largeBridgeBlock0_card_lower [DusartBounds] :
    7816043 ≤ (primeBatch 91000004 273000012).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 18.32) (lb := 19.43)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 458 25 91000004
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1943 100 273000012
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock1_card_lower [DusartBounds] :
    22249055 ≤ (primeBatch 273000012 819000036).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 19.42) (lb := 20.53)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 971 50 273000012
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 2053 100 819000036
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock2_card_lower [DusartBounds] :
    63498332 ≤ (primeBatch 819000036 2457000108).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 20.52) (lb := 21.63)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 513 25 819000036
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 2163 100 2457000108
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock3_card_lower [DusartBounds] :
    181649538 ≤ (primeBatch 2457000108 7371000324).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 21.62) (lb := 22.73)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 1081 50 2457000108
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 2273 100 7371000324
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock4_card_lower [DusartBounds] :
    521148201 ≤ (primeBatch 7371000324 22113000972).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 22.72) (lb := 23.82)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 568 25 7371000324
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1191 50 22113000972
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock5_card_lower [DusartBounds] :
    1496432925 ≤ (primeBatch 22113000972 66339002916).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 23.81) (lb := 24.92)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 2381 100 22113000972
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 623 25 66339002916
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock6_card_lower [DusartBounds] :
    4306100423 ≤ (primeBatch 66339002916 199017008748).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 24.91) (lb := 26.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 2491 100 66339002916
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1301 50 199017008748
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock7_card_lower [DusartBounds] :
    12411686104 ≤ (primeBatch 199017008748 597051026244).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 26.01) (lb := 27.12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 2601 100 199017008748
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 678 25 597051026244
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock8_card_lower [DusartBounds] :
    35829637341 ≤ (primeBatch 597051026244 1791153078732).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 27.11) (lb := 28.22)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 2711 100 597051026244
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1411 50 1791153078732
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock9_card_lower [DusartBounds] :
    103578658520 ≤ (primeBatch 1791153078732 5373459236196).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 28.21) (lb := 29.32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 2821 100 1791153078732
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 733 25 5373459236196
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock10_card_lower [DusartBounds] :
    299827025273 ≤ (primeBatch 5373459236196 16120377708588).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 29.31) (lb := 30.42)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 2931 100 5373459236196
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1521 50 16120377708588
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock11_card_lower [DusartBounds] :
    869456808510 ≤ (primeBatch 16120377708588 48361133125764).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 30.41) (lb := 31.51)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 3041 100 16120377708588
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 3151 100 48361133125764
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock12_card_lower [DusartBounds] :
    571519023209 ≤ (primeBatch 48361133125764 80000097000004).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 31.50) (lb := 32.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 63 2 48361133125764
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1601 50 80000097000004
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock13_card_lower [DusartBounds] :
    4109612035042 ≤ (primeBatch 80000097000004 240000291000012).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 32.01) (lb := 33.12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 3201 100 80000097000004
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 828 25 240000291000012
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

theorem largeBridgeBlock14_card_lower [DusartBounds] :
    2770250302992 ≤ (primeBatch 240000291000012 399000000000000).card := by
  apply primeBatch_card_lower_of_log_bounds (la := 33.11) (lb := 33.62)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · convert KernelNumerics.log_lower_of_power 3311 100 240000291000012
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert KernelNumerics.log_upper_of_power 1681 50 399000000000000
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · norm_num

/-- Two high-end blocks that fit after the first prime batch and already supply enough mass. -/
def largeBridgePhaseTwo : Finset ℕ :=
  primeBatch 16120377708588 48361133125764 ∪
    primeBatch 48361133125764 80000097000004

/-- The final two blocks remain below the protected-window ceiling. -/
def largeBridgePhaseThree : Finset ℕ :=
  primeBatch 80000097000004 240000291000012 ∪
    primeBatch 240000291000012 399000000000000

theorem largeBridgePhaseTwo_upper [DusartBounds] :
    ∀ p ∈ largeBridgePhaseTwo, p ≤ 80000097000004 := by
  intro p hp
  simp only [largeBridgePhaseTwo, primeBatch, Finset.mem_union, Finset.mem_filter,
    Finset.mem_Ioc] at hp
  omega

theorem largeBridgePhaseThree_upper [DusartBounds] :
    ∀ p ∈ largeBridgePhaseThree, p ≤ 399000000000000 := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (primeBatch_upper _ _ p hp).trans (by norm_num)
  · exact primeBatch_upper _ _ p hp

theorem largeBridgePhaseTwo_prime [DusartBounds] : ∀ p ∈ largeBridgePhaseTwo, p.Prime := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact primeBatch_prime _ _ p hp
  · exact primeBatch_prime _ _ p hp

theorem largeBridgePhaseThree_prime [DusartBounds] : ∀ p ∈ largeBridgePhaseThree, p.Prime := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact primeBatch_prime _ _ p hp
  · exact primeBatch_prime _ _ p hp

theorem largeBridgePhaseTwo_lower [DusartBounds] :
    ∀ p ∈ largeBridgePhaseTwo, 20000000 < p := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (by norm_num : 20000000 < 16120377708588).trans (primeBatch_left_lt _ _ p hp)
  · exact (by norm_num : 20000000 < 48361133125764).trans (primeBatch_left_lt _ _ p hp)

theorem largeBridgePhaseThree_lower [DusartBounds] :
    ∀ p ∈ largeBridgePhaseThree, 20000000 < p := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (by norm_num : 20000000 < 80000097000004).trans (primeBatch_left_lt _ _ p hp)
  · exact (by norm_num : 20000000 < 240000291000012).trans (primeBatch_left_lt _ _ p hp)

theorem largeBridgePhaseThree_mass [DusartBounds] :
    80000097000004 * 4109612035042 + 240000291000012 * 2770250302992 ≤
      largeBridgePhaseThree.sum id := by
  have hdisjoint : Disjoint (primeBatch 80000097000004 240000291000012)
      (primeBatch 240000291000012 399000000000000) := by
    apply disjoint_primeBatch_of_upper
    exact primeBatch_upper _ _
  have h13 : 80000097000004 * 4109612035042 ≤
      (primeBatch 80000097000004 240000291000012).sum id :=
    (Nat.mul_le_mul_left _ largeBridgeBlock13_card_lower).trans
      (primeBatch_left_mul_card_le_sum _ _)
  have h14 : 240000291000012 * 2770250302992 ≤
      (primeBatch 240000291000012 399000000000000).sum id :=
    (Nat.mul_le_mul_left _ largeBridgeBlock14_card_lower).trans
      (primeBatch_left_mul_card_le_sum _ _)
  change 80000097000004 * 4109612035042 ≤
    ∑ x ∈ primeBatch 80000097000004 240000291000012, x at h13
  change 240000291000012 * 2770250302992 ≤
    ∑ x ∈ primeBatch 240000291000012 399000000000000, x at h14
  rw [largeBridgePhaseThree, Finset.sum_union hdisjoint]
  exact (Nat.add_le_add h13 h14).trans_eq (by simp)

theorem largeBridgePhaseTwo_mass [DusartBounds] :
    16120377708588 * 869456808510 + 48361133125764 * 571519023209 ≤
      largeBridgePhaseTwo.sum id := by
  have hdisjoint : Disjoint (primeBatch 16120377708588 48361133125764)
      (primeBatch 48361133125764 80000097000004) := by
    apply disjoint_primeBatch_of_upper
    exact primeBatch_upper _ _
  have h11 : 16120377708588 * 869456808510 ≤
      (primeBatch 16120377708588 48361133125764).sum id :=
    (Nat.mul_le_mul_left _ largeBridgeBlock11_card_lower).trans
      (primeBatch_left_mul_card_le_sum _ _)
  have h12 : 48361133125764 * 571519023209 ≤
      (primeBatch 48361133125764 80000097000004).sum id :=
    (Nat.mul_le_mul_left _ largeBridgeBlock12_card_lower).trans
      (primeBatch_left_mul_card_le_sum _ _)
  change 16120377708588 * 869456808510 ≤
    ∑ x ∈ primeBatch 16120377708588 48361133125764, x at h11
  change 48361133125764 * 571519023209 ≤
    ∑ x ∈ primeBatch 48361133125764 80000097000004, x at h12
  rw [largeBridgePhaseTwo, Finset.sum_union hdisjoint]
  exact (Nat.add_le_add h11 h12).trans_eq (by simp)

set_option maxRecDepth 100000 in
theorem largeBridgePhaseTwo_mass_reaches_final_batch [DusartBounds] :
    399000000000000 ≤ 16120377708588 * 869456808510 + 48361133125764 * 571519023209 := by
  norm_num

set_option maxRecDepth 100000 in
theorem largeBridge_total_mass_reaches_tail [DusartBounds] :
    1000000000000000000100000000 ≤
      156000000 + 40000003 + 40000003 * 2000000 +
        (16120377708588 * 869456808510 + 48361133125764 * 571519023209) +
          (80000097000004 * 4109612035042 + 240000291000012 * 2770250302992) + 1 := by
  norm_num

end Pntpp.DivisorPrefix
