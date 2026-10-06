import Pntpp.DivisorPrefix.DivisorList
import Pntpp.DivisorPrefix.SubsetSums

namespace Pntpp.DivisorPrefix

private theorem takeWhile_le_eq_filter
    (l : List ℕ) (X : ℕ) (hsorted : l.SortedLT) :
    l.takeWhile (fun d => d ≤ X) = l.filter (fun d => d ≤ X) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hpair : (a :: l).Pairwise (· < ·) :=
        List.sortedLT_iff_pairwise.mp hsorted
      have htail : l.SortedLT :=
        List.sortedLT_iff_pairwise.mpr (List.pairwise_cons.mp hpair).2
      by_cases ha : a ≤ X
      · simp [ha, ih htail]
      · have hnone : ∀ b ∈ l, X < b := by
          intro b hb
          have hab : a < b := (List.pairwise_cons.mp hpair).1 b hb
          omega
        have hfilterNil : l.filter (fun b => b ≤ X) = [] :=
          List.filter_eq_nil_iff.mpr (by
            intro b hb
            simp [hnone b hb])
        simp [ha, hfilterNil]

theorem small_divisor_of_prime_product
    (ps : List ℕ) (M X d : ℕ)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hlower : ∀ p ∈ ps, M < p)
    (hwindow : X < M * M)
    (hdvd : d ∣ ps.prod)
    (hdX : d ≤ X) :
    d = 1 ∨ d ∈ ps := by
  have hprod : 0 < ps.prod := List.prod_pos fun p hp => (hprime p hp).pos
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hprod
  by_cases hdOne : d = 1
  · exact Or.inl hdOne
  let p := d.minFac
  have hpPrime : p.Prime := Nat.minFac_prime hdOne
  have hpDvdD : p ∣ d := Nat.minFac_dvd d
  have hpMem : p ∈ ps :=
    mem_list_primes_of_dvd_prod hpPrime.prime
      (fun q hq => (hprime q hq).prime) (hpDvdD.trans hdvd)
  by_cases hdPrime : d = p
  · exact Or.inr (hdPrime ▸ hpMem)
  let e := d / p
  have hpe : p * e = d := Nat.mul_div_cancel' hpDvdD
  have hpPos : 0 < p := hpPrime.pos
  have hpLeD : p ≤ d := Nat.le_of_dvd hdpos hpDvdD
  have hePos : 0 < e := Nat.div_pos hpLeD hpPos
  have heOne : e ≠ 1 := by
    intro he
    apply hdPrime
    simpa [he] using hpe.symm
  let q := e.minFac
  have hqPrime : q.Prime := Nat.minFac_prime heOne
  have hqDvdE : q ∣ e := Nat.minFac_dvd e
  have hpqDvdD : p * q ∣ d := by
    rw [← hpe]
    exact Nat.mul_dvd_mul_left p hqDvdE
  have hqDvdD : q ∣ d := by
    rw [← hpe]
    exact dvd_mul_of_dvd_right hqDvdE p
  have hqMem : q ∈ ps :=
    mem_list_primes_of_dvd_prod hqPrime.prime
      (fun r hr => (hprime r hr).prime) (hqDvdD.trans hdvd)
  have hMp : M < p := hlower p hpMem
  have hMq : M < q := hlower q hqMem
  have hpqLeD : p * q ≤ d := Nat.le_of_dvd hdpos hpqDvdD
  nlinarith

theorem prime_window_prefix
    (ps : List ℕ) (M X : ℕ)
    (hsorted : ps.SortedLT)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hlower : ∀ p ∈ ps, M < p)
    (hupper : ∀ p ∈ ps, p ≤ X)
    (hwindow : X < M * M) :
    (divisorList ps.prod).take (ps.length + 1) = 1 :: ps := by
  by_cases hps : ps = []
  · subst ps
    simp [divisorList]
  have hprod : 0 < ps.prod := List.prod_pos fun p hp => (hprime p hp).pos
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil ps hps
  have hX : 1 ≤ X := (hprime a ha).one_lt.le.trans (hupper a ha)
  let l := divisorList ps.prod
  have hlSorted : l.SortedLT := divisorList_sorted ps.prod
  have hlNodup : l.Nodup := hlSorted.nodup
  have htargetSorted : (1 :: ps).SortedLT := by
    rw [List.sortedLT_iff_pairwise]
    exact List.pairwise_cons.mpr
      ⟨fun p hp => (hprime p hp).one_lt, List.sortedLT_iff_pairwise.mp hsorted⟩
  have hfilterSorted : (l.filter (fun d => d ≤ X)).SortedLT :=
    List.sortedLT_iff_pairwise.mpr
      ((List.sortedLT_iff_pairwise.mp hlSorted).filter (fun d => d ≤ X))
  have hfilterNodup : (l.filter (fun d => d ≤ X)).Nodup :=
    hlNodup.filter _
  have htargetNodup : (1 :: ps).Nodup := htargetSorted.nodup
  have hfilterMem :
      ∀ d, d ∈ l.filter (fun e => e ≤ X) ↔ d ∈ 1 :: ps := by
    intro d
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨hdl, hdX⟩
      have hdvd : d ∣ ps.prod := (mem_divisorList.mp hdl).1
      exact small_divisor_of_prime_product ps M X d hprime hlower hwindow hdvd hdX
    · rintro (rfl | hdps)
      · exact ⟨mem_divisorList.mpr ⟨one_dvd _, hprod.ne'⟩, hX⟩
      · exact
          ⟨mem_divisorList.mpr ⟨List.dvd_prod hdps, hprod.ne'⟩,
            hupper d hdps⟩
  have hfilterPerm : List.Perm (l.filter (fun d => d ≤ X)) (1 :: ps) :=
    (List.perm_ext_iff_of_nodup hfilterNodup htargetNodup).2 hfilterMem
  have hfilter :
      l.filter (fun d => d ≤ X) = 1 :: ps :=
    hfilterPerm.eq_of_pairwise'
      (List.sortedLT_iff_pairwise.mp hfilterSorted)
      (List.sortedLT_iff_pairwise.mp htargetSorted)
  have htakeWhile :
      l.takeWhile (fun d => d ≤ X) = 1 :: ps := by
    rw [takeWhile_le_eq_filter l X hlSorted, hfilter]
  have hprefix : 1 :: ps <+: l := by
    rw [← htakeWhile]
    exact List.takeWhile_prefix _
  have htake := List.prefix_iff_eq_take.mp hprefix
  simpa [l] using htake.symm

theorem represents_one_add_sum_of_prefix
    (ps : List ℕ)
    (hprod : 0 < ps.prod)
    (hprefix :
      (divisorList ps.prod).take (ps.length + 1) = 1 :: ps) :
    Represents (1 + ps.sum) := by
  refine ⟨ps.prod, ps.length + 1, hprod, by omega, ?_, ?_⟩
  · have hlength := congrArg List.length hprefix
    simpa using hlength
  · simp [prefixDivisorSum, hprefix]

theorem represents_one_add_sum_of_prime_finset
    (s : Finset ℕ) (M X : ℕ)
    (hprime : ∀ p ∈ s, p.Prime)
    (hlower : ∀ p ∈ s, M < p)
    (hupper : ∀ p ∈ s, p ≤ X)
    (hwindow : X < M * M) :
    Represents (1 + ∑ p ∈ s, p) := by
  let ps := s.sort (· ≤ ·)
  have hpsSorted : ps.SortedLT := s.sortedLT_sort
  have hpsPrime : ∀ p ∈ ps, p.Prime := by
    intro p hp
    exact hprime p (by simpa [ps] using hp)
  have hpsLower : ∀ p ∈ ps, M < p := by
    intro p hp
    exact hlower p (by simpa [ps] using hp)
  have hpsUpper : ∀ p ∈ ps, p ≤ X := by
    intro p hp
    exact hupper p (by simpa [ps] using hp)
  have hpsProd : 0 < ps.prod := List.prod_pos fun p hp => (hpsPrime p hp).pos
  have hprefix :=
    prime_window_prefix ps M X hpsSorted hpsPrime hpsLower hpsUpper hwindow
  have hrep := represents_one_add_sum_of_prefix ps hpsProd hprefix
  have hsum : ps.sum = ∑ p ∈ s, p := by
    calc
      ps.sum = s.toList.sum := (Finset.sort_perm_toList s (· ≤ ·)).sum_eq
      _ = ∑ p ∈ s, p := Finset.sum_toList s
  rw [← hsum]
  exact hrep

theorem represents_succ_of_subsetSum_prime_window
    (A : Finset ℕ) (M X n : ℕ)
    (hprime : ∀ p ∈ A, p.Prime)
    (hlower : ∀ p ∈ A, M < p)
    (hupper : ∀ p ∈ A, p ≤ X)
    (hwindow : X < M * M)
    (hn : IsSubsetSum A n) :
    Represents (n + 1) := by
  obtain ⟨s, hsA, hsum⟩ := hn
  have hsPrime : ∀ p ∈ s, p.Prime := fun p hp => hprime p (hsA hp)
  have hsLower : ∀ p ∈ s, M < p := fun p hp => hlower p (hsA hp)
  have hsUpper : ∀ p ∈ s, p ≤ X := fun p hp => hupper p (hsA hp)
  have hrep :=
    represents_one_add_sum_of_prime_finset s M X hsPrime hsLower hsUpper hwindow
  simpa [hsum, Nat.add_comm] using hrep

end Pntpp.DivisorPrefix
