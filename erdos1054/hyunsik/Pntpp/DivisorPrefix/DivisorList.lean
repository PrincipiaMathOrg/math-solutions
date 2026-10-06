import Pntpp.DivisorPrefix.Statement

namespace Pntpp.DivisorPrefix

@[simp]
theorem mem_divisorList {d m : ℕ} : d ∈ divisorList m ↔ d ∣ m ∧ m ≠ 0 := by
  simp [divisorList, Nat.mem_divisors]

theorem divisorList_sorted (m : ℕ) : (divisorList m).SortedLT := by
  exact (Nat.divisors m).sortedLT_sort

theorem divisorList_nodup (m : ℕ) : (divisorList m).Nodup :=
  (divisorList_sorted m).nodup

theorem positive_of_mem_divisorList {d m : ℕ} (hd : d ∈ divisorList m) : 0 < d :=
  Nat.pos_of_mem_divisors ((Finset.mem_sort (· ≤ ·)).mp hd)

theorem divisorList_eq_one_cons {m : ℕ} (hm : 0 < m) :
    divisorList m = 1 :: ((Nat.divisors m).erase 1).sort (· ≤ ·) := by
  have hmem : 1 ∈ Nat.divisors m := Nat.one_mem_divisors.mpr hm.ne'
  have hle : ∀ d ∈ (Nat.divisors m).erase 1, 1 ≤ d := by
    intro d hd
    exact Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd)
  simpa [divisorList, Finset.insert_erase hmem] using
    (Finset.sort_insert (r := (· ≤ ·)) hle (by simp))

@[simp]
theorem prefixDivisorSum_one {m : ℕ} (hm : 0 < m) : prefixDivisorSum m 1 = 1 := by
  simp [prefixDivisorSum, divisorList_eq_one_cons hm]

theorem divisorList_nonempty {m : ℕ} (hm : 0 < m) : divisorList m ≠ [] := by
  rw [divisorList_eq_one_cons hm]
  simp

theorem divisorList_prime {p : ℕ} (hp : p.Prime) : divisorList p = [1, p] := by
  rw [divisorList, hp.divisors]
  rw [Finset.sort_insert]
  · simp
  · intro d hd
    simp only [Finset.mem_singleton] at hd
    subst d
    exact hp.one_lt.le
  · simpa only [Finset.mem_singleton] using hp.ne_one.symm

theorem divisorList_four : divisorList 4 = [1, 2, 4] := by
  have hdiv : Nat.divisors 4 = {1, 2, 4} := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, _⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
      have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      interval_cases d <;> norm_num at *
    · rintro (rfl | rfl | rfl) <;> norm_num
  rw [divisorList, hdiv]
  rw [Finset.sort_insert]
  · rw [Finset.sort_insert]
    · simp
    · simp
    · simp
  · simp
  · simp

private theorem length_le_sum_of_pos
    (l : List ℕ) (hpos : ∀ d ∈ l, 0 < d) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons d l ih =>
      simp only [List.length_cons, List.sum_cons]
      have hd : 0 < d := hpos d (by simp)
      have hl : ∀ e ∈ l, 0 < e := by
        intro e he
        exact hpos e (by simp [he])
      have hih := ih hl
      omega

theorem prefix_length_le_sum {m k : ℕ} (hk : k ≤ (divisorList m).length) :
    k ≤ prefixDivisorSum m k := by
  have hpos : ∀ d ∈ (divisorList m).take k, 0 < d := by
    intro d hd
    exact positive_of_mem_divisorList (List.mem_of_mem_take hd)
  calc
    k = ((divisorList m).take k).length := by simp [hk]
    _ ≤ ((divisorList m).take k).sum := length_le_sum_of_pos _ hpos
    _ = prefixDivisorSum m k := rfl

theorem three_le_prefixDivisorSum_two {m : ℕ}
    (hm : 0 < m) (hlen : 2 ≤ (divisorList m).length) :
    3 ≤ prefixDivisorSum m 2 := by
  let rest := ((Nat.divisors m).erase 1).sort (· ≤ ·)
  have hlist : divisorList m = 1 :: rest := divisorList_eq_one_cons hm
  have hrest : rest ≠ [] := by
    intro h
    rw [hlist, h] at hlen
    simp at hlen
  obtain ⟨d, ds, hrestEq⟩ := List.exists_cons_of_ne_nil hrest
  have hlist' : divisorList m = 1 :: d :: ds := by
    rw [hlist, hrestEq]
  have hsorted : (1 :: d :: ds).SortedLT := by
    rw [← hlist']
    exact divisorList_sorted m
  have hd : 1 < d := by
    have hpair : (1 :: d :: ds).Pairwise (· < ·) :=
      List.sortedLT_iff_pairwise.mp hsorted
    exact (List.pairwise_cons.mp hpair).1 d (by simp)
  simp [prefixDivisorSum, hlist']
  omega

theorem six_le_prefixDivisorSum_three {m : ℕ}
    (hm : 0 < m) (hlen : 3 ≤ (divisorList m).length) :
    6 ≤ prefixDivisorSum m 3 := by
  let rest := ((Nat.divisors m).erase 1).sort (· ≤ ·)
  have hlist : divisorList m = 1 :: rest := divisorList_eq_one_cons hm
  have hrestTwo : 2 ≤ rest.length := by
    simpa [hlist] using hlen
  have hrest : rest ≠ [] := by
    intro h
    simp [h] at hrestTwo
  obtain ⟨d, tail, hrestEq⟩ := List.exists_cons_of_ne_nil hrest
  have htail : tail ≠ [] := by
    intro h
    simp [hrestEq, h] at hrestTwo
  obtain ⟨e, ds, htailEq⟩ := List.exists_cons_of_ne_nil htail
  have hlist' : divisorList m = 1 :: d :: e :: ds := by
    rw [hlist, hrestEq, htailEq]
  have hsorted : (1 :: d :: e :: ds).SortedLT := by
    rw [← hlist']
    exact divisorList_sorted m
  have hpair : (1 :: d :: e :: ds).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp hsorted
  have hd : 1 < d := (List.pairwise_cons.mp hpair).1 d (by simp)
  have hde : d < e := by
    have htailPair := (List.pairwise_cons.mp hpair).2
    exact (List.pairwise_cons.mp htailPair).1 e (by simp)
  simp [prefixDivisorSum, hlist']
  omega

theorem prefixDivisorSum_two_ne_five {m : ℕ}
    (hm : 0 < m) (hlen : 2 ≤ (divisorList m).length) :
    prefixDivisorSum m 2 ≠ 5 := by
  let rest := ((Nat.divisors m).erase 1).sort (· ≤ ·)
  have hlist : divisorList m = 1 :: rest := divisorList_eq_one_cons hm
  have hrest : rest ≠ [] := by
    intro h
    rw [hlist, h] at hlen
    simp at hlen
  obtain ⟨d, ds, hrestEq⟩ := List.exists_cons_of_ne_nil hrest
  have hlist' : divisorList m = 1 :: d :: ds := by
    rw [hlist, hrestEq]
  intro hsum
  have hdFour : d = 4 := by
    have hone : 1 + d = 5 := by
      simpa [prefixDivisorSum, hlist'] using hsum
    omega
  have hdmem : d ∈ divisorList m := by simp [hlist']
  have hddiv : d ∣ m := (mem_divisorList.mp hdmem).1
  have htwoDiv : 2 ∣ m := by
    rw [hdFour] at hddiv
    exact (by norm_num : 2 ∣ 4).trans hddiv
  have htwoMem : 2 ∈ divisorList m := mem_divisorList.mpr ⟨htwoDiv, hm.ne'⟩
  have htwoTail : 2 ∈ ds := by
    rw [hlist', hdFour] at htwoMem
    simpa using htwoMem
  have hsorted : (1 :: d :: ds).SortedLT := by
    rw [← hlist']
    exact divisorList_sorted m
  have hpair : (1 :: d :: ds).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp hsorted
  have hdTwo : d < 2 := by
    have htailPair := (List.pairwise_cons.mp hpair).2
    exact (List.pairwise_cons.mp htailPair).1 2 htwoTail
  omega

end Pntpp.DivisorPrefix
