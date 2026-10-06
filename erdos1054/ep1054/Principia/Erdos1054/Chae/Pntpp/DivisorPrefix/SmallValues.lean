/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/SmallValues.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.DivisorList

set_option autoImplicit false
set_option maxRecDepth 100000

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
