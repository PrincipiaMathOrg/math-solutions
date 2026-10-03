/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs

set_option autoImplicit false

/-!
# Erdős 1054 — elementary foundations (EP1054 §1–§2)

Ported verbatim (proofs unchanged, namespace renamed) from the comparator-certified master
`Erdos1054_3rdMomentProof.lean`, namespace `Represented`, lines ~31730–31930 and 33492:

* `reflection` — paper **Lemma 2.1** (`eq:reflection`): `F_e(d) = e d · g_e(e d)`.
* the sorted-prefix bridges `prefixSumDivisors ↔ Fdiv`,
* `mem_R_iff_exists_F` — `N ∈ 𝓡 ↔ ∃ e d ≥ 1, N = F e d`,
* `f_mem_Fform` — for `N ∈ 𝓡` the minimiser `f N` is `e d` for a representation `N = F e d`,
* `F_ge` — `d ≤ F e d` (the paper's "the final divisor occurs in its own prefix").
-/

namespace Principia.Erdos1054

open Finset

/-- **Lemma 2.1 (reflection).** `F_e(d) = e d · g_e(e d)` for `e, d ≥ 1`. -/
theorem reflection (e d : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) :
    (F e d : ℝ) = (e * d : ℝ) * g e (e * d) := by
  set m := e * d with hm
  have hmpos : 0 < m := by rw [hm]; exact Nat.mul_pos he hd
  have hF : (F e d : ℝ) = ∑ r ∈ m.divisors, (if r ≤ d then (r : ℝ) else 0) := by
    rw [F, ← hm, Nat.cast_sum, Finset.sum_filter]
  have hg : (m : ℝ) * g e m = ∑ r ∈ m.divisors, (if e ≤ r then (m : ℝ) / r else 0) := by
    simp only [g, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs with h
    · rw [mul_one_div]
    · rw [mul_zero]
  have hrefl :
      (∑ r ∈ m.divisors, (if (m / r) ≤ d then ((m / r : ℕ) : ℝ) else 0))
        = ∑ r ∈ m.divisors, (if r ≤ d then (r : ℝ) else 0) :=
    Nat.sum_div_divisors m (fun r => if r ≤ d then (r : ℝ) else 0)
  have hterm : (∑ r ∈ m.divisors, (if (m / r) ≤ d then ((m / r : ℕ) : ℝ) else 0))
        = ∑ r ∈ m.divisors, (if e ≤ r then (m : ℝ) / r else 0) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.mem_divisors] at hr
    obtain ⟨hdvd, _⟩ := hr
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hdvd hmpos
    have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hval : ((m / r : ℕ) : ℝ) = (m : ℝ) / r := Nat.cast_div hdvd hrne
    have hmul : m / r * r = m := Nat.div_mul_cancel hdvd
    have hcond : (m / r ≤ d) ↔ (e ≤ r) := by
      constructor
      · intro h
        have h1 : m / r * r ≤ d * r := by gcongr
        rw [hmul] at h1
        have h2 : e * d ≤ r * d := by rw [hm, mul_comm d r] at h1; exact h1
        exact le_of_mul_le_mul_right h2 (by omega)
      · intro h
        have h1 : e * d ≤ r * d := by gcongr
        have h2 : m / r * r ≤ d * r := by rw [hmul, hm, mul_comm d r]; exact h1
        exact le_of_mul_le_mul_right h2 hrpos
    by_cases h : e ≤ r
    · rw [if_pos (hcond.mpr h), if_pos h, hval]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [hF, ← hrefl, hterm, ← hg, hm]
  push_cast
  ring

/-- Sum of divisors of `m` that are `≤ d`. -/
def Fdiv (m d : ℕ) : ℕ := ∑ q ∈ m.divisors.filter (· ≤ d), q

lemma F_eq_Fdiv {m d : ℕ} (hd : d ∣ m) : F (m / d) d = Fdiv m d := by
  unfold F Fdiv
  rw [Nat.div_mul_cancel hd]

/-- The `toFinset` of the first `k` sorted divisors is exactly the divisors `≤` the `k`-th one. -/
lemma take_sort_toFinset (m k : ℕ) (hidx : k - 1 < (m.divisors.sort (· ≤ ·)).length)
    (hk1 : 1 ≤ k) :
    ((m.divisors.sort (· ≤ ·)).take k).toFinset
      = m.divisors.filter (· ≤ (m.divisors.sort (· ≤ ·))[k - 1]) := by
  classical
  have hslt : (m.divisors.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort m.divisors
  ext a
  simp only [List.mem_toFinset, Finset.mem_filter, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hiL : i < (m.divisors.sort (· ≤ ·)).length := lt_of_lt_of_le hi (min_le_right _ _)
    have hik : i ≤ k - 1 := by have := lt_of_lt_of_le hi (min_le_left _ _); omega
    refine ⟨by rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hiL, ?_⟩
    rw [hslt.getElem_le_getElem_iff]; exact hik
  · rintro ⟨haD, hale⟩
    have haL : a ∈ m.divisors.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact haD
    obtain ⟨i, hiL, rfl⟩ := List.getElem_of_mem haL
    have hik : i ≤ k - 1 := by
      rw [← hslt.getElem_le_getElem_iff (hi := hiL) (hj := hidx)]; exact hale
    refine ⟨i, lt_of_le_of_lt hik (by omega), ?_⟩
    simp

/-- For a nodup list, the list sum equals the `Finset` sum over its `toFinset`. -/
lemma list_sum_eq_toFinset_sum : ∀ {l : List ℕ}, l.Nodup → l.sum = ∑ q ∈ l.toFinset, q := by
  classical
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    rw [List.sum_cons, List.toFinset_cons,
      Finset.sum_insert (by simpa using (List.nodup_cons.1 h).1), ih (List.nodup_cons.1 h).2]

/-- **Sorted-prefix bridge (forward).** -/
lemma prefixSumDivisors_eq_Fdiv (m k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ m.divisors.card) :
    ∃ d, d ∈ m.divisors ∧ prefixSumDivisors m k = Fdiv m d := by
  classical
  have hlen : (m.divisors.sort (· ≤ ·)).length = m.divisors.card := Finset.length_sort _
  have hidx : k - 1 < (m.divisors.sort (· ≤ ·)).length := by rw [hlen]; omega
  refine ⟨(m.divisors.sort (· ≤ ·))[k - 1], ?_, ?_⟩
  · rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hidx
  · rw [prefixSumDivisors, Fdiv, ← take_sort_toFinset m k hidx hk1,
      list_sum_eq_toFinset_sum ((m.divisors.sort_nodup (· ≤ ·)).take)]

/-- **Sorted-prefix bridge (backward).** -/
lemma Fdiv_eq_prefixSumDivisors (m d : ℕ) (hd : d ∈ m.divisors) :
    ∃ k, 1 ≤ k ∧ k ≤ m.divisors.card ∧ Fdiv m d = prefixSumDivisors m k := by
  classical
  have hdL : d ∈ m.divisors.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact hd
  obtain ⟨i, hiL, hdi⟩ := List.getElem_of_mem hdL
  have hlen : (m.divisors.sort (· ≤ ·)).length = m.divisors.card := Finset.length_sort _
  refine ⟨i + 1, by omega, by rw [← hlen]; omega, ?_⟩
  have hidx : (i + 1) - 1 < (m.divisors.sort (· ≤ ·)).length := by omega
  have hdeq : (m.divisors.sort (· ≤ ·))[(i + 1) - 1] = d := by simp [hdi]
  rw [prefixSumDivisors, Fdiv, ← hdeq, ← take_sort_toFinset m (i + 1) hidx (by omega),
    list_sum_eq_toFinset_sum ((m.divisors.sort_nodup (· ≤ ·)).take)]

/-- A prefix representation of `N` by `m` is exactly `N = F (m/d) d` for a divisor `d ∣ m`. -/
lemma isRep_iff_exists_divisor (N m : ℕ) :
    IsRep N m ↔ ∃ d, d ∈ m.divisors ∧ N = F (m / d) d := by
  constructor
  · rintro ⟨k, hk1, hk2, hN⟩
    obtain ⟨d, hd, hpd⟩ := prefixSumDivisors_eq_Fdiv m k hk1 hk2
    exact ⟨d, hd, by rw [hN, hpd, F_eq_Fdiv (Nat.dvd_of_mem_divisors hd)]⟩
  · rintro ⟨d, hd, hN⟩
    obtain ⟨k, hk1, hk2, hpd⟩ := Fdiv_eq_prefixSumDivisors m d hd
    exact ⟨k, hk1, hk2, by rw [hN, F_eq_Fdiv (Nat.dvd_of_mem_divisors hd), hpd]⟩

/-- The `f`-minimisation set, re-expressed via the `F e d` parametrisation. -/
lemma f_set_eq (N : ℕ) :
    {m | 1 ≤ m ∧ IsRep N m}
      = {m | ∃ e d, 1 ≤ e ∧ 1 ≤ d ∧ m = e * d ∧ N = F e d} := by
  ext m
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hm, hrep⟩
    rw [isRep_iff_exists_divisor N m] at hrep
    obtain ⟨d, hd, hN⟩ := hrep
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    refine ⟨m / d, d, ?_, hdpos, (Nat.div_mul_cancel hdvd).symm, hN⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
  · rintro ⟨e, d, he, hd, hme, hN⟩
    subst hme
    have hpos : 0 < e * d := Nat.mul_pos he hd
    have hed : (e * d) / d = e := by
      rw [Nat.mul_div_assoc e (dvd_refl d), Nat.div_self (by omega), mul_one]
    refine ⟨hpos, ?_⟩
    rw [isRep_iff_exists_divisor N (e * d)]
    refine ⟨d, ?_, ?_⟩
    · rw [Nat.mem_divisors]; exact ⟨dvd_mul_left d e, hpos.ne'⟩
    · rw [hed, hN]

/-- Membership in `𝓡` is exactly the `F e d` parametrisation. -/
theorem mem_R_iff_exists_F (N : ℕ) :
    N ∈ R ↔ ∃ e d, 1 ≤ e ∧ 1 ≤ d ∧ N = F e d := by
  constructor
  · rintro ⟨m, hm, hrep⟩
    have hmem : m ∈ {m | 1 ≤ m ∧ IsRep N m} := ⟨hm, hrep⟩
    rw [f_set_eq] at hmem
    obtain ⟨e, d, he, hd, _, hN⟩ := hmem
    exact ⟨e, d, he, hd, hN⟩
  · rintro ⟨e, d, he, hd, hN⟩
    have hpos : 0 < e * d := Nat.mul_pos he hd
    have hmem : (e * d) ∈ {m | 1 ≤ m ∧ IsRep N m} := by
      rw [f_set_eq]; exact ⟨e, d, he, hd, rfl, hN⟩
    exact ⟨e * d, hpos, hmem.2⟩

/-- For represented `N`, the minimiser `f N` is realised by a concrete pair `(e, d)`. -/
theorem f_mem_Fform (N : ℕ) (hN : N ∈ R) :
    ∃ e d, 1 ≤ e ∧ 1 ≤ d ∧ f N = e * d ∧ N = F e d := by
  have hne : {m | 1 ≤ m ∧ IsRep N m}.Nonempty := hN
  have hmem : f N ∈ {m | 1 ≤ m ∧ IsRep N m} := Nat.sInf_mem hne
  rw [f_set_eq] at hmem
  exact hmem

/-- `f N ≤ e d` for every representation `N = F e d` — the minimiser is below every witness. -/
theorem f_le_of_F (e d N : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) (hN : N = F e d) : f N ≤ e * d := by
  apply Nat.sInf_le
  rw [f_set_eq]
  exact ⟨e, d, he, hd, rfl, hN⟩

/-- `d ≤ F e d` (the divisor `d` itself is one of the summands). -/
theorem F_ge (e d : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) : d ≤ F e d := by
  rw [F]
  refine Finset.single_le_sum (fun i _ => Nat.zero_le i) ?_
  rw [Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨dvd_mul_left d e, by positivity⟩, le_refl d⟩

end Principia.Erdos1054
