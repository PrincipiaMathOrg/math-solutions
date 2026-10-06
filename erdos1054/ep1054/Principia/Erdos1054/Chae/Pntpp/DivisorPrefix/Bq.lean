/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Bq.lean`,
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

theorem divisorList_mul_prime_of_lt
    {B q : ℕ} (hB : 0 < B) (hq : q.Prime) (hBq : B < q) :
    divisorList (B * q) =
      divisorList B ++ (divisorList B).map (q * ·) := by
  have hleftSorted : (divisorList B).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp (divisorList_sorted B)
  have hrightSorted :
      ((divisorList B).map (q * ·)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hleftSorted.imp fun hab => (Nat.mul_lt_mul_left hq.pos).2 hab
  have hcross :
      ∀ a ∈ divisorList B, ∀ b ∈ (divisorList B).map (q * ·), a < b := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    have haB : a ≤ B :=
      Nat.le_of_dvd hB (mem_divisorList.mp ha).1
    have hdpos : 0 < d := positive_of_mem_divisorList hd
    have hqle : q ≤ q * d := by
      nlinarith
    omega
  have hcandidateSorted :
      (divisorList B ++ (divisorList B).map (q * ·)).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    exact ⟨hleftSorted, hrightSorted, hcross⟩
  have htargetSorted : (divisorList (B * q)).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp (divisorList_sorted (B * q))
  have hperm :
      List.Perm (divisorList (B * q))
        (divisorList B ++ (divisorList B).map (q * ·)) := by
    apply List.perm_ext_iff_of_nodup
      (divisorList_nodup (B * q)) hcandidateSorted.nodup |>.2
    intro d
    simp only [divisorList, Finset.mem_sort, List.mem_append, List.mem_map]
    rw [Nat.divisors_mul, hq.divisors]
    constructor
    · intro hd
      rw [Finset.mem_mul] at hd
      obtain ⟨a, ha, b, hb, rfl⟩ := hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · left
        simpa using ha
      · right
        exact ⟨a, ha, by simp [mul_comm]⟩
    · intro hd
      rw [Finset.mem_mul]
      rcases hd with hd | ⟨a, ha, hqa⟩
      · exact ⟨d, hd, 1, by simp, by simp⟩
      · subst d
        exact ⟨a, ha, q, by simp, by simp [mul_comm]⟩
  exact hperm.eq_of_pairwise
    (fun a b _ _ hab hba => by omega) htargetSorted hcandidateSorted

theorem divisorList_mul_prime_take
    {B q k : ℕ} (hB : 0 < B) (hq : q.Prime) (hBq : B < q) :
    (divisorList (B * q)).take ((divisorList B).length + k) =
      divisorList B ++ ((divisorList B).take k).map (q * ·) := by
  rw [divisorList_mul_prime_of_lt hB hq hBq]
  simp [List.take_append]

theorem prefixDivisorSum_mul_prime_add
    {B q k : ℕ} (hB : 0 < B) (hq : q.Prime) (hBq : B < q) :
    prefixDivisorSum (B * q) ((divisorList B).length + k) =
      (divisorList B).sum + q * prefixDivisorSum B k := by
  unfold prefixDivisorSum
  rw [divisorList_mul_prime_take hB hq hBq, List.sum_append,
    List.sum_map_mul_left]
  simp

theorem represents_divisorSum_add_prime_mul_prefix
    {B q k : ℕ} (hB : 0 < B) (hq : q.Prime) (hBq : B < q)
    (hk : k ≤ (divisorList B).length) :
    Represents ((divisorList B).sum + q * prefixDivisorSum B k) := by
  refine ⟨B * q, (divisorList B).length + k, Nat.mul_pos hB hq.pos, ?_, ?_, ?_⟩
  · have hlenPos : 0 < (divisorList B).length :=
      List.length_pos_iff_ne_nil.mpr (divisorList_nonempty hB)
    omega
  · rw [divisorList_mul_prime_of_lt hB hq hBq]
    simp
    omega
  · exact prefixDivisorSum_mul_prime_add hB hq hBq

end Pntpp.DivisorPrefix
