import Pntpp.DivisorPrefix.DivisorList

namespace Pntpp.DivisorPrefix

theorem represents_one : Represents 1 := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩ <;>
    norm_num [divisorList, prefixDivisorSum, Nat.divisors_one]

theorem represents_three : Represents 3 := by
  refine ⟨2, 2, by norm_num, by norm_num, ?_, ?_⟩
  · rw [divisorList_prime (p := 2) (by norm_num)]
    norm_num
  · simp only [prefixDivisorSum]
    rw [divisorList_prime (p := 2) (by norm_num)]
    norm_num

theorem represents_four : Represents 4 := by
  refine ⟨3, 2, by norm_num, by norm_num, ?_, ?_⟩
  · rw [divisorList_prime (p := 3) (by norm_num)]
    norm_num
  · simp only [prefixDivisorSum]
    rw [divisorList_prime (p := 3) (by norm_num)]
    norm_num

theorem represents_seven : Represents 7 := by
  refine ⟨4, 3, by norm_num, by norm_num, ?_, ?_⟩ <;>
    simp [divisorList_four, prefixDivisorSum]

theorem not_represents_two : ¬Represents 2 := by
  rintro ⟨m, k, hm, hk, hklen, hsum⟩
  have hk2 : k ≤ 2 := by
    simpa [hsum] using prefix_length_le_sum hklen
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · rw [prefixDivisorSum_one hm] at hsum
    omega
  · have hthree := three_le_prefixDivisorSum_two hm hklen
    omega

theorem not_represents_five : ¬Represents 5 := by
  rintro ⟨m, k, hm, hk, hklen, hsum⟩
  by_cases hk2 : k ≤ 2
  · have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl
    · rw [prefixDivisorSum_one hm] at hsum
      omega
    · exact prefixDivisorSum_two_ne_five hm hklen hsum
  · have hk3 : 3 ≤ k := by omega
    have hthreeLen : 3 ≤ (divisorList m).length := hk3.trans hklen
    have hsix : 6 ≤ prefixDivisorSum m 3 :=
      six_le_prefixDivisorSum_three hm hthreeLen
    have hmono : prefixDivisorSum m 3 ≤ prefixDivisorSum m k := by
      exact List.monotone_sum_take (divisorList m) hk3
    omega

theorem two_and_five_impossible : ¬Represents 2 ∧ ¬Represents 5 :=
  ⟨not_represents_two, not_represents_five⟩

end Pntpp.DivisorPrefix
