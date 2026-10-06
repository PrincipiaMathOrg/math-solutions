import Pntpp.DivisorPrefix.Bq
import Pntpp.DivisorPrefix.SmallValues
import Pntpp.DivisorPrefix.Computation.SmallSeedKernel

namespace Pntpp.DivisorPrefix.Computation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A checked finite Bq witness. -/
structure SmallBqWitness where
  B : ℕ
  q : ℕ
  k : ℕ
  deriving DecidableEq, Repr

def SmallBqWitness.Valid (n : ℕ) (w : SmallBqWitness) : Prop :=
  0 < w.B ∧ w.q.Prime ∧ w.B < w.q ∧
  w.k ≤ (divisorList w.B).length ∧
  (divisorList w.B).sum + w.q * prefixDivisorSum w.B w.k = n

theorem SmallBqWitness.represents {n : ℕ} {w : SmallBqWitness} (hw : w.Valid n) :
    Represents n := by
  rcases hw with ⟨hB, hq, hBq, hk, heq⟩
  rw [← heq]
  exact represents_divisorSum_add_prime_mul_prefix hB hq hBq hk

private theorem divisor_list_1 : divisorList 1 = [1] := by
  apply (divisorList_sorted 1).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 1 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    subst d
    norm_num

private theorem divisor_list_2 : divisorList 2 = [1, 2] := by
  apply (divisorList_sorted 2).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl <;> norm_num

private theorem divisor_list_3 : divisorList 3 = [1, 3] := by
  apply (divisorList_sorted 3).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl <;> norm_num

private theorem divisor_list_4 : divisorList 4 = [1, 2, 4] := by
  apply (divisorList_sorted 4).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl <;> norm_num

private theorem divisor_list_5 : divisorList 5 = [1, 5] := by
  apply (divisorList_sorted 5).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 5 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl <;> norm_num

private theorem divisor_list_6 : divisorList 6 = [1, 2, 3, 6] := by
  apply (divisorList_sorted 6).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num

private theorem divisor_list_7 : divisorList 7 = [1, 7] := by
  apply (divisorList_sorted 7).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 7 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl <;> norm_num

private theorem divisor_list_8 : divisorList 8 = [1, 2, 4, 8] := by
  apply (divisorList_sorted 8).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num

private theorem divisor_list_9 : divisorList 9 = [1, 3, 9] := by
  apply (divisorList_sorted 9).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 9 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl <;> norm_num

private theorem divisor_list_10 : divisorList 10 = [1, 2, 5, 10] := by
  apply (divisorList_sorted 10).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 10 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num

private theorem divisor_list_12 : divisorList 12 = [1, 2, 3, 4, 6, 12] := by
  apply (divisorList_sorted 12).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 12 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem divisor_list_13 : divisorList 13 = [1, 13] := by
  apply (divisorList_sorted 13).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 13 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl <;> norm_num

private theorem divisor_list_15 : divisorList 15 = [1, 3, 5, 15] := by
  apply (divisorList_sorted 15).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 15 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num

private theorem divisor_list_18 : divisorList 18 = [1, 2, 3, 6, 9, 18] := by
  apply (divisorList_sorted 18).eq_of_mem_iff (by decide)
  intro d
  rw [mem_divisorList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hd, _⟩
    have hlo : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hhi : d ≤ 18 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The only per-value search data needed: 6 through334, with7 handled explicitly. -/
theorem tinyBq_representation :
    ∀ n, 6 ≤ n → n ≤ 334 → Represents n := by
  intro n hlo hhi
  interval_cases n
  · exact SmallBqWitness.represents (w := ⟨1, 5, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact represents_seven
  · exact SmallBqWitness.represents (w := ⟨1, 7, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 5, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 7, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 7, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 11, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 7, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 13, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 11, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 13, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 13, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 17, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 13, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 19, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 17, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 19, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 19, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 23, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 19, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 23, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 23, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 7, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 23, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 29, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 19, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 31, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 29, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 31, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 31, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 11, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨5, 31, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 37, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 31, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨2, 37, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 37, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 41, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 37, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 43, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 41, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 43, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 43, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 47, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 43, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 47, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 47, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨8, 37, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨5, 47, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 53, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 43, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 53, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 53, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 17, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 53, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 59, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 53, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨1, 61, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 59, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 61, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 61, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 59, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 61, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 67, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 19, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 67, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 67, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 71, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 67, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 73, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 71, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 73, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 73, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 71, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 73, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 79, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 23, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 79, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 79, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 83, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 79, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 83, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 83, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨8, 73, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨5, 83, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 89, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 79, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 89, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 89, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 29, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 89, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 31, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨7, 89, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨1, 97, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 29, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 97, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 97, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 101, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 97, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 103, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 101, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 103, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 103, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 107, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 103, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 107, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 113, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 113, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 113, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 37, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 113, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨3, 29, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨6, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨8, 107, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨6, 37, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨8, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨6, 113, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 41, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨10, 109, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_10])
  · exact SmallBqWitness.represents (w := ⟨1, 127, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨9, 29, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_9])
  · exact SmallBqWitness.represents (w := ⟨2, 127, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 127, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 131, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 127, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 131, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 131, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 43, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 131, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 137, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 127, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 137, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 47, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨5, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨4, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨7, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨4, 47, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨6, 137, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 149, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 139, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 151, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 149, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 151, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 151, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 149, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 151, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 157, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 151, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨2, 157, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 157, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 53, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨5, 157, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 163, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 157, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨2, 163, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 163, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 167, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 163, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 167, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 167, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨8, 157, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨5, 167, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 173, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 163, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 173, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 173, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨8, 163, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨5, 173, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 179, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 173, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨1, 181, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 179, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 181, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 181, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 61, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨5, 181, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨4, 181, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨6, 59, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨4, 61, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨6, 179, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 191, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 181, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 193, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 191, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 193, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 193, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 197, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 193, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 197, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 67, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨5, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨4, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨7, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨4, 67, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨6, 197, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨4, 29, 3⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨6, 199, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 67, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 71, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨5, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨4, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨7, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨4, 71, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨12, 193, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_12])
  · exact SmallBqWitness.represents (w := ⟨2, 73, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨6, 211, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 223, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 71, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 223, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 223, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 227, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 223, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 229, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 227, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 229, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 229, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 233, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 229, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 233, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 233, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨8, 223, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨5, 233, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 239, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 229, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 241, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 239, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 241, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 241, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 239, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 241, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨3, 61, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨6, 79, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨10, 29, 3⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_10])
  · exact SmallBqWitness.represents (w := ⟨6, 239, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 251, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 241, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 251, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 251, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 83, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 251, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 257, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 251, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨2, 257, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 257, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨18, 223, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_18])
  · exact SmallBqWitness.represents (w := ⟨5, 257, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 263, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 257, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨2, 263, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 263, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨15, 61, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_15])
  · exact SmallBqWitness.represents (w := ⟨5, 263, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 269, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨7, 263, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨1, 271, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 269, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 271, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 271, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 269, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 271, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 277, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 89, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 277, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 277, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 281, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 277, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 281, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨3, 71, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨5, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨4, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨7, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨8, 277, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨6, 281, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨1, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 283, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨4, 97, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨5, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨4, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨7, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨8, 41, 3⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨6, 97, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨7, 37, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_7])
  · exact SmallBqWitness.represents (w := ⟨6, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 101, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨13, 293, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_13])
  · exact SmallBqWitness.represents (w := ⟨1, 307, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨10, 97, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_10])
  · exact SmallBqWitness.represents (w := ⟨2, 307, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 307, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 311, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 307, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨1, 313, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨3, 311, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨2, 313, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 313, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨1, 317, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨5, 313, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 317, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨3, 317, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_3])
  · exact SmallBqWitness.represents (w := ⟨8, 307, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨5, 317, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_5])
  · exact SmallBqWitness.represents (w := ⟨2, 107, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨6, 313, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨8, 311, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_8])
  · exact SmallBqWitness.represents (w := ⟨10, 103, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_10])
  · exact SmallBqWitness.represents (w := ⟨4, 107, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_4])
  · exact SmallBqWitness.represents (w := ⟨6, 317, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 109, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])
  · exact SmallBqWitness.represents (w := ⟨10, 313, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_10])
  · exact SmallBqWitness.represents (w := ⟨1, 331, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_1])
  · exact SmallBqWitness.represents (w := ⟨6, 107, 2⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_6])
  · exact SmallBqWitness.represents (w := ⟨2, 331, 1⟩)
      (by norm_num [SmallBqWitness.Valid, prefixDivisorSum, divisor_list_2])

/-- Complete finite initial range, using tiny Bq witnesses and a checked prime window. -/
theorem smallBq_representation :
    ∀ n, 6 ≤ n → n ≤ 469615 → Represents n := by
  intro n hlo hhi
  by_cases hs : n ≤ 334
  · exact tinyBq_representation n hlo hs
  · exact smallKernel_representation n (by omega) hhi

end Pntpp.DivisorPrefix.Computation
