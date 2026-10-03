/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

/-!
# EP1054 `lem:kovac-moment` (paper lines 990–1116)

Proves every obligation of the package `Kovac` of the spine:

* `leaf_KovacMoment_reflection` — divisor reflection `σ_j(n)/n = ∑_{i > j} 1/r_i` (lines 1003–1009),
  via the rank `#{d ∣ n : d < r}`: the first `k` sorted divisors are the divisors of rank `< k`
  (`sort_take_toFinset`), and `rank(d) + rank(n/d) + 1 = τ(n)` (`rank_add_rank_div`).
* `link_KovacMoment_identity` — the counting identity (lines 1010–1019); it holds for every `q`,
  the hypothesis `q ≥ 3` is not used. The sum over `j < τ(n)` is reindexed by the divisor of rank
  `j`, and the `q`-th power is expanded over `q`-tuples (`pow_sum_eq_sum_pi`).
* `link_KovacMoment_reduction` — summing over `n ≤ x`; the number of `n ≤ ⌊x⌋` divisible by
  `lcm(r, a_1, …, a_q)` is `⌊x⌋ / lcm ≤ x / lcm` (lines 1020–1022).
* `leaf_KovacS_le_S1S2` — `S ≤ S' S''` at every truncation level (lines 1028–1053), through the
  injection `a ↦ (gcd(r, a_i), a_i / gcd(r, a_i))_i`, `r · lcm(c) ≤ lcm(r, a)` (`mul_lcm_le`) and
  `r ∏ a_i^{(q-1)/q} ≤ ∏ a_i` (`r_mul_prod_rpow_le`, equivalent to the paper's termwise inequality
  `1/c_i ≤ 1/(b_i^{1-β} c_i^β)`).
* `link_Eq_KSprime`, `link_Eq_KSsecond` — the Euler-product bounds (lines 1056–1111) from
  `Std_Mertens2`. Truncated sums are bounded by finite Euler products through the injection
  `x ↦ (v_p(x))_{p ≤ B}` (`sum_le_prod_sum`); the local factors are bounded by
  `exp(8q/p)` (resp. `exp(9q/p)`) for `p ≤ q` and by `exp(O(p^{-3/2} + q p^{-2}))` (resp.
  `exp(O(p^{-2}))`) for `p > q` (`mu_le_exp`, `psi_le_exp`); Mertens gives
  `∑_{p ≤ q} 1/p ≤ log log q + c₀` (`mertens_upper`), and `final_bound` absorbs constants using
  `log log q ≥ log log 3 > 0`. For `p > q` the paper's mean-value-theorem estimate is replaced by
  `M_p ≤ 1 + p^{-1}(A^q - 1)` (every nonzero exponent vector has `max ≥ 1`) and the uniform bound
  `∑_{p > q} q p^{-2+1/q} ≪ 1` by Bernoulli's inequality `p^{1/q} ≤ 1 + (2/q)(p^{1/2} - 1)`.
* `link_Eq_KS`, `link_Lem_KovacMoment` — the two compositions (lines 1023–1027, 1114–1116).
-/

namespace Principia.Erdos1054.Proofs.Kovac

open Finset
open Principia.Erdos1054

/-- The `i`-th element of the sorted list of `s` has exactly `i` elements of `s` below it. -/
lemma card_filter_lt_sort_getElem (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≤ ·)).length) :
    (s.filter (· < (s.sort (· ≤ ·))[i])).card = i := by
  have hslt : (s.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort s
  have hset : s.filter (· < (s.sort (· ≤ ·))[i]) = ((s.sort (· ≤ ·)).take i).toFinset := by
    ext a
    simp only [List.mem_toFinset, Finset.mem_filter, List.mem_take_iff_getElem]
    constructor
    · rintro ⟨haS, hlt⟩
      have haL : a ∈ s.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact haS
      obtain ⟨j, hjL, rfl⟩ := List.getElem_of_mem haL
      have hji : j < i := (hslt.getElem_lt_getElem_iff (hi := hjL) (hj := hi)).mp hlt
      exact ⟨j, lt_min hji hjL, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hjL : j < (s.sort (· ≤ ·)).length := lt_of_lt_of_le hj (min_le_right _ _)
      have hji : j < i := lt_of_lt_of_le hj (min_le_left _ _)
      refine ⟨by rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hjL, ?_⟩
      exact (hslt.getElem_lt_getElem_iff (hi := hjL) (hj := hi)).mpr hji
  rw [hset, List.toFinset_card_of_nodup ((s.sort_nodup (· ≤ ·)).take), List.length_take]
  omega

/-- The first `k` sorted elements of `s` are exactly those with fewer than `k` elements below. -/
lemma sort_take_toFinset (s : Finset ℕ) (k : ℕ) :
    ((s.sort (· ≤ ·)).take k).toFinset = s.filter (fun r => (s.filter (· < r)).card < k) := by
  ext a
  simp only [List.mem_toFinset, Finset.mem_filter, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hiL : i < (s.sort (· ≤ ·)).length := lt_of_lt_of_le hi (min_le_right _ _)
    refine ⟨by rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hiL, ?_⟩
    rw [card_filter_lt_sort_getElem s i hiL]
    exact lt_of_lt_of_le hi (min_le_left _ _)
  · rintro ⟨haS, hk⟩
    have haL : a ∈ s.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact haS
    obtain ⟨i, hiL, rfl⟩ := List.getElem_of_mem haL
    rw [card_filter_lt_sort_getElem s i hiL] at hk
    exact ⟨i, lt_min hk hiL, rfl⟩

lemma prefixSumDivisors_eq_sum (m k : ℕ) :
    prefixSumDivisors m k =
      ∑ d ∈ m.divisors.filter (fun r => (m.divisors.filter (· < r)).card < k), d := by
  rw [prefixSumDivisors, list_sum_eq_toFinset_sum ((m.divisors.sort_nodup (· ≤ ·)).take),
    sort_take_toFinset]

lemma sigmaPrefix_eq_sum (j n : ℕ) :
    sigmaPrefix j n = ∑ d ∈ n.divisors.filter
      (fun r => (n.divisors.filter (· < r)).card < n.divisors.card - j), d := by
  unfold sigmaPrefix
  split_ifs with h
  · exact prefixSumDivisors_eq_sum n _
  · have h0 : n.divisors.card - j = 0 := by omega
    rw [h0]
    simp

/-- Divisor reflection for ranks: `rank(d) + rank(n/d) + 1 = τ(n)`. -/
lemma rank_add_rank_div (n d : ℕ) (hn : n ≠ 0) (hd : d ∈ n.divisors) :
    (n.divisors.filter (· < d)).card + (n.divisors.filter (· < n / d)).card + 1 =
      n.divisors.card := by
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have h1 : (n.divisors.filter (· < n / d)).card = (n.divisors.filter (d < ·)).card := by
    apply Finset.card_bij' (fun e _ => n / e) (fun e _ => n / e)
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
      obtain ⟨⟨hen, -⟩, hlt⟩ := he
      refine ⟨⟨Nat.div_dvd_of_dvd hen, hn⟩, ?_⟩
      rw [Nat.lt_div_iff_mul_lt' hen, Nat.mul_comm]
      exact (Nat.lt_div_iff_mul_lt' hdn e).mp hlt
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
      obtain ⟨⟨hen, -⟩, hlt⟩ := he
      refine ⟨⟨Nat.div_dvd_of_dvd hen, hn⟩, ?_⟩
      rw [Nat.lt_div_iff_mul_lt' hdn, Nat.mul_comm]
      have h' : d < n / (n / e) := by rw [Nat.div_div_self hen hn]; exact hlt
      exact (Nat.lt_div_iff_mul_lt' (Nat.div_dvd_of_dvd hen) d).mp h'
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he
      exact Nat.div_div_self he.1.1 hn
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he
      exact Nat.div_div_self he.1.1 hn
  have h2 : n.divisors.filter (fun e => ¬ e < d) = insert d (n.divisors.filter (d < ·)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
    constructor
    · rintro ⟨he, hde⟩
      rcases hde.lt_or_eq with h | h
      · exact Or.inr ⟨he, h⟩
      · exact Or.inl h.symm
    · rintro (rfl | ⟨he, h⟩)
      · exact ⟨hd, le_rfl⟩
      · exact ⟨he, h.le⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := n.divisors) (· < d)
  rw [h2, Finset.card_insert_of_notMem (by simp)] at h3
  omega

/-- Strict monotonicity of the rank. -/
lemma rank_lt_rank {s : Finset ℕ} {a b : ℕ} (ha : a ∈ s) (hab : a < b) :
    (s.filter (· < a)).card < (s.filter (· < b)).card := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨a, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hab⟩
  · simp only [Finset.mem_filter]
    exact ⟨ha, hab⟩
  · simp

lemma rank_le_rank {s : Finset ℕ} {a b : ℕ} (hab : a ≤ b) :
    (s.filter (· < a)).card ≤ (s.filter (· < b)).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 hab⟩

lemma rank_le_rank_iff {s : Finset ℕ} {a b : ℕ} (hb : b ∈ s) :
    (s.filter (· < a)).card ≤ (s.filter (· < b)).card ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hba
    exact absurd h (not_le.mpr (rank_lt_rank hb (not_le.mp hba)))
  · exact rank_le_rank

lemma rank_lt_card {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : (s.filter (· < a)).card < s.card := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨a, ha, ?_⟩
  simp

lemma exists_rank_eq {s : Finset ℕ} {j : ℕ} (hj : j < s.card) :
    ∃ a ∈ s, (s.filter (· < a)).card = j := by
  have hlen : (s.sort (· ≤ ·)).length = s.card := Finset.length_sort _
  have hjL : j < (s.sort (· ≤ ·)).length := by rw [hlen]; exact hj
  refine ⟨(s.sort (· ≤ ·))[j], ?_, card_filter_lt_sort_getElem s j hjL⟩
  rw [← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem hjL

/-- Expansion of a `q`-th power of a finite sum over `q`-tuples. -/
lemma pow_sum_eq_sum_pi (T : Finset ℕ) (q : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ T, f r) ^ q = ∑ a ∈ Fintype.piFinset (fun _ : Fin q => T), ∏ i, f (a i) := by
  rw [← Fin.prod_const q (∑ r ∈ T, f r), Finset.prod_univ_sum]

lemma piFinset_filter_le (s : Finset ℕ) (q r0 : ℕ) :
    Fintype.piFinset (fun _ : Fin q => s.filter (r0 ≤ ·)) =
      (Fintype.piFinset fun _ : Fin q => s).filter (fun a => ∀ i, r0 ≤ a i) := by
  ext a
  simp only [Fintype.mem_piFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

lemma lcm_univ_pos {q : ℕ} (a : Fin q → ℕ) (ha : ∀ i, 1 ≤ a i) :
    0 < (Finset.univ : Finset (Fin q)).lcm a := by
  rw [Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨i, -, hi⟩
  have := ha i
  omega

/-- `r · lcm(c) ≤ lcm(r, a_1, …, a_q)` for `c_i = a_i / gcd(r, a_i)` (EP1054 line 1034). -/
lemma mul_lcm_le (q r : ℕ) (hr : 1 ≤ r) (a : Fin q → ℕ) (ha : ∀ i, 1 ≤ a i) :
    r * (Finset.univ : Finset (Fin q)).lcm (fun i => a i / Nat.gcd r (a i)) ≤
      Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) := by
  have hLpos : 0 < Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) :=
    Nat.lcm_pos (by omega) (lcm_univ_pos a ha)
  obtain ⟨y, hy⟩ := Nat.dvd_lcm_left r ((Finset.univ : Finset (Fin q)).lcm a)
  apply Nat.le_of_dvd hLpos
  rw [hy]
  apply Nat.mul_dvd_mul_left
  apply Finset.lcm_dvd
  intro i _
  have hai : a i ∣ r * y := by
    rw [← hy]
    exact dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) (Nat.dvd_lcm_right _ _)
  have hg : 0 < Nat.gcd r (a i) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hga : Nat.gcd r (a i) * (a i / Nat.gcd r (a i)) = a i :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right r (a i))
  have hgr : Nat.gcd r (a i) * (r / Nat.gcd r (a i)) = r :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left r (a i))
  have hcop : Nat.Coprime (a i / Nat.gcd r (a i)) (r / Nat.gcd r (a i)) :=
    (Nat.coprime_div_gcd_div_gcd hg).symm
  have hai' : Nat.gcd r (a i) * (a i / Nat.gcd r (a i)) ∣
      Nat.gcd r (a i) * (r / Nat.gcd r (a i) * y) := by
    rw [hga, ← Nat.mul_assoc, hgr]
    exact hai
  exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg hai')

lemma rpow_beta_add (x : ℝ) (hx : 0 < x) (q : ℕ) (hq : 1 ≤ q) :
    x ^ (((q : ℝ) - 1) / q) * x ^ ((1 : ℝ) / q) = x := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_add hx, ← add_div, sub_add_cancel, div_self hq0, Real.rpow_one]

/-- `r ∏ a_i^β ≤ ∏ a_i` when `r ≤ a_i` for all `i`, `β = (q-1)/q` (the step `1/c_i ≤ 1/(b_i^{1-β} c_i^β)`
of EP1054 line 1040, in the equivalent form `r ≤ (∏ a_i)^{1/q}`). -/
lemma r_mul_prod_rpow_le (q : ℕ) (hq : 1 ≤ q) (r : ℕ) (a : Fin q → ℕ) (ha : ∀ i, 1 ≤ a i)
    (hra : ∀ i, r ≤ a i) :
    (r : ℝ) * ∏ i, (a i : ℝ) ^ (((q : ℝ) - 1) / q) ≤ ∏ i, (a i : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hapos : ∀ i, (0 : ℝ) < a i := fun i => by
    have := ha i
    exact_mod_cast (by omega : 0 < a i)
  have hsplit : ∏ i, (a i : ℝ) =
      (∏ i, (a i : ℝ) ^ (((q : ℝ) - 1) / q)) * ∏ i, (a i : ℝ) ^ ((1 : ℝ) / q) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [rpow_beta_add _ (hapos i) q hq]
  have hr : (r : ℝ) ≤ ∏ i, (a i : ℝ) ^ ((1 : ℝ) / q) := by
    calc (r : ℝ) = ∏ _i : Fin q, (r : ℝ) ^ ((1 : ℝ) / q) := by
          rw [Fin.prod_const, ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
            one_div_mul_cancel hq0, Real.rpow_one]
      _ ≤ ∏ i, (a i : ℝ) ^ ((1 : ℝ) / q) := by
          apply Finset.prod_le_prod
          · intro i _
            positivity
          · intro i _
            exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hra i) (by positivity)
  rw [hsplit, mul_comm (r : ℝ)]
  exact mul_le_mul_of_nonneg_left hr (by positivity)

/-- The termwise inequality behind `S ≤ S' S''` (EP1054 lines 1028–1044). -/
lemma term_le (q : ℕ) (hq : 1 ≤ q) (r : ℕ) (hr : 1 ≤ r) (a : Fin q → ℕ) (ha : ∀ i, 1 ≤ a i)
    (hra : ∀ i, r ≤ a i) :
    1 / ((∏ i, (a i : ℝ)) * (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ)) ≤
      (1 / (r : ℝ) ^ 2 * ∏ i, 1 / ((Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
        (1 / ((∏ i, ((a i / Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
          (((Finset.univ : Finset (Fin q)).lcm (fun i => a i / Nat.gcd r (a i)) : ℕ) : ℝ))) := by
  have hc : ∀ i, 1 ≤ a i / Nat.gcd r (a i) := by
    intro i
    have hg : 0 < Nat.gcd r (a i) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hai := ha i
    exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right r (a i))) hg
  have hML : (r : ℝ) * (((Finset.univ : Finset (Fin q)).lcm (fun i => a i / Nat.gcd r (a i)) :
      ℕ) : ℝ) ≤ (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ) := by
    exact_mod_cast mul_lcm_le q r hr a ha
  have hMpos : (0 : ℝ) < (((Finset.univ : Finset (Fin q)).lcm
      (fun i => a i / Nat.gcd r (a i)) : ℕ) : ℝ) := by
    exact_mod_cast lcm_univ_pos _ hc
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hapos : ∀ i, (0 : ℝ) < a i := fun i => by
    have := ha i
    exact_mod_cast (by omega : 0 < a i)
  have hDC : (∏ i, ((Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
      (∏ i, ((a i / Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) =
      ∏ i, (a i : ℝ) ^ (((q : ℝ) - 1) / q) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right r (a i))]
  have hRQ := r_mul_prod_rpow_le q hq r a ha hra
  have hrhs : (1 / (r : ℝ) ^ 2 * ∏ i, 1 / ((Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
        (1 / ((∏ i, ((a i / Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
          (((Finset.univ : Finset (Fin q)).lcm (fun i => a i / Nat.gcd r (a i)) : ℕ) : ℝ))) =
      1 / (((r : ℝ) * ∏ i, (a i : ℝ) ^ (((q : ℝ) - 1) / q)) *
        ((r : ℝ) * (((Finset.univ : Finset (Fin q)).lcm (fun i => a i / Nat.gcd r (a i)) :
          ℕ) : ℝ))) := by
    rw [← hDC, Finset.prod_div_distrib, Finset.prod_const_one]
    ring
  rw [hrhs]
  apply one_div_le_one_div_of_le
  · exact mul_pos (mul_pos hrpos (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hapos i) _)))
      (mul_pos hrpos hMpos)
  · exact mul_le_mul hRQ hML (by positivity) (by positivity)

/-! ### A generic Euler-product upper bound -/

/-- If `F x ≤ ∏_{p ∈ P} φ_p(E x p)` and `x ↦ (E x p)_{p ∈ P}` is injective on `S` with values in
`∏_p T p`, then `∑_{x ∈ S} F x ≤ ∏_{p ∈ P} ∑_{η ∈ T p} φ_p(η)`. -/
lemma sum_le_prod_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (P : Finset ℕ) (E : α → ℕ → β) (T : ℕ → Finset β)
    (φ : ℕ → β → ℝ) (F : α → ℝ)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, (∀ p ∈ P, E x p = E y p) → x = y)
    (hT : ∀ x ∈ S, ∀ p ∈ P, E x p ∈ T p)
    (hφ : ∀ p ∈ P, ∀ η ∈ T p, 0 ≤ φ p η)
    (hF : ∀ x ∈ S, F x ≤ ∏ p ∈ P, φ p (E x p)) :
    ∑ x ∈ S, F x ≤ ∏ p ∈ P, ∑ η ∈ T p, φ p η := by
  classical
  have h1 : ∑ x ∈ S, F x ≤ ∑ x ∈ S, ∏ p : P, φ p.1 (E x p.1) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    calc F x ≤ ∏ p ∈ P, φ p (E x p) := hF x hx
      _ = ∏ p : P, φ p.1 (E x p.1) :=
        (Finset.prod_coe_sort (s := P) (f := fun p => φ p (E x p))).symm
  have h2 : ∑ x ∈ S, ∏ p : P, φ p.1 (E x p.1) =
      ∑ g ∈ S.image (fun x : α => fun p : P => E x p.1), ∏ p : P, φ p.1 (g p) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hinj x hx y hy (fun p hp => congrFun hxy ⟨p, hp⟩)
  have h3 : ∑ g ∈ S.image (fun x : α => fun p : P => E x p.1), ∏ p : P, φ p.1 (g p) ≤
      ∑ g ∈ Fintype.piFinset (fun p : P => T p.1), ∏ p : P, φ p.1 (g p) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro g hg
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
      rw [Fintype.mem_piFinset]
      intro p
      exact hT x hx p.1 p.2
    · intro g hg _
      rw [Fintype.mem_piFinset] at hg
      exact Finset.prod_nonneg (fun p _ => hφ p.1 p.2 (g p) (hg p))
  have h4 : ∑ g ∈ Fintype.piFinset (fun p : P => T p.1), ∏ p : P, φ p.1 (g p) =
      ∏ p ∈ P, ∑ η ∈ T p, φ p η := by
    rw [← Finset.prod_coe_sort (s := P) (f := fun p => ∑ η ∈ T p, φ p η)]
    exact (Finset.prod_univ_sum (fun p : P => T p.1) (fun p η => φ p.1 η)).symm
  linarith

/-! ### Factorisations over a finite set of primes -/

lemma prod_pow_factorization_of_subset {x : ℕ} (hx : x ≠ 0) {P : Finset ℕ}
    (hP : x.primeFactors ⊆ P) : ∏ p ∈ P, p ^ x.factorization p = x := by
  calc ∏ p ∈ P, p ^ x.factorization p = x.factorization.prod (fun p k => p ^ k) :=
        (Finsupp.prod_of_support_subset x.factorization
          (by rw [Nat.support_factorization]; exact hP) (fun p k => p ^ k)
          (fun p _ => pow_zero p)).symm
    _ = x := Nat.prod_factorization_pow_eq_self hx

lemma rpow_eq_prod_primes {x : ℕ} (hx : x ≠ 0) {P : Finset ℕ} (hP : x.primeFactors ⊆ P)
    (s : ℝ) : (x : ℝ) ^ s = ∏ p ∈ P, ((p : ℝ) ^ s) ^ x.factorization p := by
  have h := prod_pow_factorization_of_subset hx hP
  have hcast : (x : ℝ) = ∏ p ∈ P, (p : ℝ) ^ x.factorization p := by exact_mod_cast h.symm
  rw [hcast, ← Real.finsetProd_rpow P (fun p => (p : ℝ) ^ x.factorization p)
    (fun p _ => by positivity) s]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _), ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
    mul_comm]

lemma eq_of_factorization_eq_on {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) {P : Finset ℕ}
    (hxP : x.primeFactors ⊆ P) (hyP : y.primeFactors ⊆ P)
    (h : ∀ p ∈ P, x.factorization p = y.factorization p) : x = y := by
  calc x = ∏ p ∈ P, p ^ x.factorization p := (prod_pow_factorization_of_subset hx hxP).symm
    _ = ∏ p ∈ P, p ^ y.factorization p := Finset.prod_congr rfl (fun p hp => by rw [h p hp])
    _ = y := prod_pow_factorization_of_subset hy hyP

/-- The primes `≤ B`. -/
def primesLe (B : ℕ) : Finset ℕ := (Finset.range (B + 1)).filter Nat.Prime

lemma prime_of_mem_primesLe {B p : ℕ} (hp : p ∈ primesLe B) : p.Prime :=
  (Finset.mem_filter.mp hp).2

lemma primeFactors_subset_primesLe {x B : ℕ} (hxB : x ≤ B) : x.primeFactors ⊆ primesLe B := by
  intro p hp
  unfold primesLe
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := Nat.le_of_mem_primeFactors hp; omega, Nat.prime_of_mem_primeFactors hp⟩

lemma prod_prime_pow_dvd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (k : ℕ → ℕ) (n : ℕ)
    (h : ∀ p ∈ P, p ^ k p ∣ n) : ∏ p ∈ P, p ^ k p ∣ n := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime (a ^ k a) (∏ p ∈ s, p ^ k p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes (hP a (Finset.mem_insert_self a s))
        (hP p (Finset.mem_insert_of_mem hp))).mpr (fun hap => ha (by rw [hap]; exact hp))
    exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_insert_self a s))
      (ih (fun p hp => hP p (Finset.mem_insert_of_mem hp))
        (fun p hp => h p (Finset.mem_insert_of_mem hp)))

lemma prod_pow_sup_le_lcm {q : ℕ} (c : Fin q → ℕ) (hc : ∀ i, c i ≠ 0) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, p ^ ((Finset.univ : Finset (Fin q)).sup fun i => (c i).factorization p) ≤
      (Finset.univ : Finset (Fin q)).lcm c := by
  apply Nat.le_of_dvd
  · apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨i, -, hi⟩
    exact hc i hi
  apply prod_prime_pow_dvd hP
  intro p _
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin q)) with he | hne
  · simp [he]
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup _ hne (fun i => (c i).factorization p)
    rw [hi]
    exact dvd_trans (Nat.ordProj_dvd (c i) p) (Finset.dvd_lcm (Finset.mem_univ i))

/-! ### The Euler-product majorants of `S'` and `S''` -/

/-- `p^{-(q-1)/q}`. -/
noncomputable def tq (q p : ℕ) : ℝ := 1 / (p : ℝ) ^ (((q : ℝ) - 1) / q)

/-- The local factor of `S''` at `p` (truncated). -/
noncomputable def mu (q B p : ℕ) : ℝ :=
  ∑ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)),
    (∏ i, tq q p ^ (γ i)) * (1 / (p : ℝ)) ^ ((Finset.univ : Finset (Fin q)).sup γ)

/-- The local factor of `S'` at `p` (truncated). -/
noncomputable def psi (q B p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (B + 1),
    (1 / (p : ℝ) ^ 2) ^ k * (∑ g ∈ Finset.range (k + 1), tq q p ^ g) ^ q

lemma kovacS2_le_prod (q : ℕ) (B : ℕ) :
    S4a.kovacS2 q B ≤ ∏ p ∈ primesLe B, mu q B p := by
  unfold S4a.kovacS2
  refine sum_le_prod_sum (Fintype.piFinset (fun _ : Fin q => Finset.Icc 1 B)) (primesLe B)
    (fun c p => fun i => (c i).factorization p)
    (fun _ => Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)))
    (fun p γ => (∏ i, tq q p ^ (γ i)) * (1 / (p : ℝ)) ^ ((Finset.univ : Finset (Fin q)).sup γ))
    _ ?_ ?_ ?_ ?_
  · intro x hx y hy hxy
    rw [Fintype.mem_piFinset] at hx hy
    funext i
    have hxi := Finset.mem_Icc.mp (hx i)
    have hyi := Finset.mem_Icc.mp (hy i)
    exact eq_of_factorization_eq_on (by omega) (by omega)
      (primeFactors_subset_primesLe hxi.2) (primeFactors_subset_primesLe hyi.2)
      (fun p hp => congrFun (hxy p hp) i)
  · intro x hx p _
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hx
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hxi := hx i
    have := Nat.factorization_lt p (show x i ≠ 0 by omega)
    omega
  · intro p _ η _
    show 0 ≤ (∏ i, tq q p ^ (η i)) * (1 / (p : ℝ)) ^ ((Finset.univ : Finset (Fin q)).sup η)
    unfold tq
    positivity
  · intro c hc
    show 1 / ((∏ i, (c i : ℝ) ^ (((q : ℝ) - 1) / q)) *
        (((Finset.univ : Finset (Fin q)).lcm c : ℕ) : ℝ)) ≤
      ∏ p ∈ primesLe B, (∏ i, tq q p ^ ((c i).factorization p)) *
        (1 / (p : ℝ)) ^ ((Finset.univ : Finset (Fin q)).sup fun i => (c i).factorization p)
    rw [Fintype.mem_piFinset] at hc
    have hc0 : ∀ i, c i ≠ 0 := fun i => by have := (Finset.mem_Icc.mp (hc i)).1; omega
    have hcP : ∀ i, (c i).primeFactors ⊆ primesLe B :=
      fun i => primeFactors_subset_primesLe (Finset.mem_Icc.mp (hc i)).2
    have hp0 : ∀ p ∈ primesLe B, (0 : ℝ) < p :=
      fun p hp => by exact_mod_cast (prime_of_mem_primesLe hp).pos
    have hnum : ∏ i, (c i : ℝ) ^ (((q : ℝ) - 1) / q) = ∏ p ∈ primesLe B,
        ∏ i, ((p : ℝ) ^ (((q : ℝ) - 1) / q)) ^ ((c i).factorization p) := by
      rw [Finset.prod_comm]
      exact Finset.prod_congr rfl (fun i _ => rpow_eq_prod_primes (hc0 i) (hcP i) _)
    have hL : (∏ p ∈ primesLe B,
        (p : ℝ) ^ ((Finset.univ : Finset (Fin q)).sup fun i => (c i).factorization p)) ≤
        (((Finset.univ : Finset (Fin q)).lcm c : ℕ) : ℝ) := by
      exact_mod_cast prod_pow_sup_le_lcm c hc0 (fun p hp => prime_of_mem_primesLe hp)
    have hpos1 : 0 < ∏ p ∈ primesLe B,
        ∏ i, ((p : ℝ) ^ (((q : ℝ) - 1) / q)) ^ ((c i).factorization p) :=
      Finset.prod_pos (fun p hp => Finset.prod_pos
        (fun i _ => pow_pos (Real.rpow_pos_of_pos (hp0 p hp) _) _))
    have hpos2 : 0 < ∏ p ∈ primesLe B,
        (p : ℝ) ^ ((Finset.univ : Finset (Fin q)).sup fun i => (c i).factorization p) :=
      Finset.prod_pos (fun p hp => pow_pos (hp0 p hp) _)
    rw [hnum]
    calc _ ≤ 1 / ((∏ p ∈ primesLe B,
            ∏ i, ((p : ℝ) ^ (((q : ℝ) - 1) / q)) ^ ((c i).factorization p)) *
          ∏ p ∈ primesLe B,
            (p : ℝ) ^ ((Finset.univ : Finset (Fin q)).sup fun i => (c i).factorization p)) :=
          one_div_le_one_div_of_le (mul_pos hpos1 hpos2) (mul_le_mul_of_nonneg_left hL hpos1.le)
      _ = _ := by
          unfold tq
          simp only [one_div, inv_pow, Finset.prod_inv_distrib, mul_inv, Finset.prod_mul_distrib]

lemma sum_divisors_rpow_le (q r : ℕ) (hr : r ≠ 0) {P : Finset ℕ} (hP : r.primeFactors ⊆ P) :
    ∑ d ∈ r.divisors, 1 / (d : ℝ) ^ (((q : ℝ) - 1) / q) ≤
      ∏ p ∈ P, ∑ g ∈ Finset.range (r.factorization p + 1), tq q p ^ g := by
  refine sum_le_prod_sum r.divisors P (fun d p => d.factorization p)
    (fun p => Finset.range (r.factorization p + 1)) (fun p g => tq q p ^ g) _ ?_ ?_ ?_ ?_
  · intro x hx y hy hxy
    have hx0 : x ≠ 0 := (Nat.pos_of_mem_divisors hx).ne'
    have hy0 : y ≠ 0 := (Nat.pos_of_mem_divisors hy).ne'
    exact eq_of_factorization_eq_on hx0 hy0
      ((Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hx) hr).trans hP)
      ((Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hy) hr).trans hP) hxy
  · intro x hx p _
    simp only [Finset.mem_range]
    have := (Nat.factorization_le_iff_dvd (Nat.pos_of_mem_divisors hx).ne' hr).mpr
      (Nat.dvd_of_mem_divisors hx) p
    omega
  · intro p _ g _
    show 0 ≤ tq q p ^ g
    unfold tq
    positivity
  · intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    apply le_of_eq
    show 1 / (d : ℝ) ^ (((q : ℝ) - 1) / q) = ∏ p ∈ P, tq q p ^ d.factorization p
    rw [rpow_eq_prod_primes hd0 ((Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hr).trans hP)]
    unfold tq
    simp only [one_div, inv_pow, Finset.prod_inv_distrib]

lemma kovacS1_le_prod (q B : ℕ) : S4a.kovacS1 q B ≤ ∏ p ∈ primesLe B, psi q B p := by
  unfold S4a.kovacS1
  refine sum_le_prod_sum (Finset.Icc 1 B) (primesLe B) (fun r p => r.factorization p)
    (fun _ => Finset.range (B + 1))
    (fun p k => (1 / (p : ℝ) ^ 2) ^ k * (∑ g ∈ Finset.range (k + 1), tq q p ^ g) ^ q)
    _ ?_ ?_ ?_ ?_
  · intro x hx y hy hxy
    have hxi := Finset.mem_Icc.mp hx
    have hyi := Finset.mem_Icc.mp hy
    exact eq_of_factorization_eq_on (by omega) (by omega)
      (primeFactors_subset_primesLe hxi.2) (primeFactors_subset_primesLe hyi.2) hxy
  · intro x hx p _
    have hxi := Finset.mem_Icc.mp hx
    simp only [Finset.mem_range]
    have := Nat.factorization_lt p (show x ≠ 0 by omega)
    omega
  · intro p _ k _
    show 0 ≤ (1 / (p : ℝ) ^ 2) ^ k * (∑ g ∈ Finset.range (k + 1), tq q p ^ g) ^ q
    unfold tq
    positivity
  · intro r hr
    show 1 / (r : ℝ) ^ 2 * (∑ d ∈ r.divisors, 1 / (d : ℝ) ^ (((q : ℝ) - 1) / q)) ^ q ≤
      ∏ p ∈ primesLe B, (1 / (p : ℝ) ^ 2) ^ (r.factorization p) *
        (∑ g ∈ Finset.range (r.factorization p + 1), tq q p ^ g) ^ q
    have hri := Finset.mem_Icc.mp hr
    have hr0 : r ≠ 0 := by omega
    have hrP := primeFactors_subset_primesLe (B := B) hri.2
    have h1 := sum_divisors_rpow_le q r hr0 hrP
    have h2 : 1 / (r : ℝ) ^ 2 = ∏ p ∈ primesLe B, (1 / (p : ℝ) ^ 2) ^ (r.factorization p) := by
      have hn := prod_pow_factorization_of_subset hr0 hrP
      have hc : (r : ℝ) = ∏ p ∈ primesLe B, (p : ℝ) ^ r.factorization p := by
        exact_mod_cast hn.symm
      rw [hc, ← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [one_div, inv_pow, pow_right_comm]
    rw [Finset.prod_mul_distrib, ← h2, Finset.prod_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 q) (by positivity)

/-! ### Local factor bounds -/

lemma geom_le_exp (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 4) (n : ℕ) :
    ∑ g ∈ Finset.range n, t ^ g ≤ Real.exp (4 * t) := by
  have h1t : 0 < 1 - t := by linarith
  have hgs := geom_sum_mul t n
  have htn : 0 ≤ t ^ n := pow_nonneg ht0 n
  have he := Real.add_one_le_exp (4 * t)
  have key : (∑ g ∈ Finset.range n, t ^ g) * (1 - t) ≤ Real.exp (4 * t) * (1 - t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) h1t.le,
      mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 3 - 4 * t)]
  exact le_of_mul_le_mul_right key h1t

lemma exp_sub_one_le_mul_exp (s : ℝ) : Real.exp s - 1 ≤ s * Real.exp s := by
  have h := Real.add_one_le_exp (-s)
  have h2 : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 := Real.exp_pos s
  nlinarith [mul_le_mul_of_nonneg_right h h3.le]

lemma mu_bounds (q B : ℕ) (t u : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 4) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    (∑ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)),
        (∏ i, t ^ (γ i)) * u ^ ((Finset.univ : Finset (Fin q)).sup γ)) ≤
        Real.exp (4 * q * t) ∧
    (∑ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)),
        (∏ i, t ^ (γ i)) * u ^ ((Finset.univ : Finset (Fin q)).sup γ)) ≤
      1 + u * (Real.exp (4 * q * t) - 1) := by
  have hA := geom_le_exp t ht0 ht1 (B + 1)
  have hA0 : 0 ≤ ∑ g ∈ Finset.range (B + 1), t ^ g :=
    Finset.sum_nonneg (fun g _ => pow_nonneg ht0 g)
  have hAq : (∑ g ∈ Finset.range (B + 1), t ^ g) ^ q ≤ Real.exp (4 * q * t) := by
    calc (∑ g ∈ Finset.range (B + 1), t ^ g) ^ q ≤ (Real.exp (4 * t)) ^ q :=
          pow_le_pow_left₀ hA0 hA q
      _ = Real.exp (4 * q * t) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hw : ∑ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)), ∏ i, t ^ (γ i) =
      (∑ g ∈ Finset.range (B + 1), t ^ g) ^ q := (pow_sum_eq_sum_pi _ q (fun g => t ^ g)).symm
  constructor
  · calc _ ≤ ∑ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)),
            ∏ i, t ^ (γ i) := by
          refine Finset.sum_le_sum (fun γ _ => ?_)
          exact mul_le_of_le_one_right (Finset.prod_nonneg (fun i _ => pow_nonneg ht0 _))
            (pow_le_one₀ hu0 hu1)
      _ ≤ Real.exp (4 * q * t) := by rw [hw]; exact hAq
  · have hterm : ∀ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)),
        (∏ i, t ^ (γ i)) * u ^ ((Finset.univ : Finset (Fin q)).sup γ) ≤
          u * ∏ i, t ^ (γ i) + (if γ = 0 then 1 - u else 0) := by
      intro γ _
      by_cases hγ : γ = 0
      · subst hγ
        have hs0 : (Finset.univ : Finset (Fin q)).sup (0 : Fin q → ℕ) = 0 :=
          Nat.eq_zero_of_le_zero (Finset.sup_le (fun i _ => le_refl 0))
        rw [hs0, if_pos rfl]
        simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one]
        linarith
      · rw [if_neg hγ, add_zero]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hγ
        have hsup : 1 ≤ (Finset.univ : Finset (Fin q)).sup γ := by
          have h1 := Finset.le_sup (f := γ) (Finset.mem_univ i)
          have h2 : γ i ≠ 0 := hi
          omega
        have hu : u ^ ((Finset.univ : Finset (Fin q)).sup γ) ≤ u := by
          calc u ^ ((Finset.univ : Finset (Fin q)).sup γ) ≤ u ^ 1 :=
                pow_le_pow_of_le_one hu0 hu1 hsup
            _ = u := pow_one u
        rw [mul_comm u]
        exact mul_le_mul_of_nonneg_left hu (Finset.prod_nonneg (fun i _ => pow_nonneg ht0 _))
    have h0mem : (0 : Fin q → ℕ) ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)) := by
      rw [Fintype.mem_piFinset]
      intro i
      simp
    calc _ ≤ ∑ γ ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (B + 1)),
            (u * ∏ i, t ^ (γ i) + (if γ = 0 then 1 - u else 0)) := Finset.sum_le_sum hterm
      _ = u * (∑ g ∈ Finset.range (B + 1), t ^ g) ^ q + (1 - u) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw, Finset.sum_ite_eq', if_pos h0mem]
      _ ≤ 1 + u * (Real.exp (4 * q * t) - 1) := by
          nlinarith [mul_le_mul_of_nonneg_left hAq hu0]

lemma psi_bound (q B : ℕ) (t v : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 3 / 4) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1 / 2) :
    ∑ k ∈ Finset.range (B + 1), v ^ k * (∑ g ∈ Finset.range (k + 1), t ^ g) ^ q ≤
      1 + 2 * v * Real.exp (4 * q * t) := by
  have hAk : ∀ k : ℕ, (∑ g ∈ Finset.range (k + 1), t ^ g) ^ q ≤ Real.exp (4 * q * t) := by
    intro k
    calc (∑ g ∈ Finset.range (k + 1), t ^ g) ^ q ≤ (Real.exp (4 * t)) ^ q :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun g _ => pow_nonneg ht0 g))
            (geom_le_exp t ht0 ht1 (k + 1)) q
      _ = Real.exp (4 * q * t) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hterm : ∀ k ∈ Finset.range (B + 1), v ^ k * (∑ g ∈ Finset.range (k + 1), t ^ g) ^ q ≤
      (if k = 0 then 1 - Real.exp (4 * q * t) else 0) + Real.exp (4 * q * t) * v ^ k := by
    intro k _
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      simp only [pow_zero, zero_add, Finset.range_one, Finset.sum_singleton, one_pow,
        mul_one]
      linarith
    · rw [if_neg hk, zero_add, mul_comm (Real.exp (4 * q * t))]
      exact mul_le_mul_of_nonneg_left (hAk k) (pow_nonneg hv0 k)
  have hgeom : ∑ k ∈ Finset.range (B + 1), v ^ k ≤ 1 + 2 * v := by
    have hgs := geom_sum_mul v (B + 1)
    have hvn : 0 ≤ v ^ (B + 1) := pow_nonneg hv0 _
    have h1v : 0 < 1 - v := by linarith
    have key : (∑ k ∈ Finset.range (B + 1), v ^ k) * (1 - v) ≤ (1 + 2 * v) * (1 - v) := by
      nlinarith [mul_nonneg hv0 (by linarith : (0 : ℝ) ≤ 1 - 2 * v)]
    exact le_of_mul_le_mul_right key h1v
  have hY0 : 0 ≤ Real.exp (4 * q * t) := (Real.exp_pos _).le
  calc _ ≤ ∑ k ∈ Finset.range (B + 1),
          ((if k = 0 then 1 - Real.exp (4 * q * t) else 0) + Real.exp (4 * q * t) * v ^ k) :=
        Finset.sum_le_sum hterm
    _ = (1 - Real.exp (4 * q * t)) + Real.exp (4 * q * t) * ∑ k ∈ Finset.range (B + 1), v ^ k := by
        have h0 : (0 : ℕ) ∈ Finset.range (B + 1) := by simp
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos h0, Finset.mul_sum]
    _ ≤ 1 + 2 * v * Real.exp (4 * q * t) := by
        nlinarith [mul_le_mul_of_nonneg_left hgeom hY0]

/-- The elementary bounds on `t = p^{-(q-1)/q}` used in EP1054 lines 1066–1106. -/
lemma t_bounds (p q : ℕ) (hp : 2 ≤ p) (hq : 3 ≤ q) :
    0 < tq q p ∧ tq q p ≤ 3 / 4 ∧ (p ≤ q → tq q p ≤ 2 / p) ∧
    (q ≤ p → (q : ℝ) * tq q p ≤ 2) ∧
    (q : ℝ) * tq q p * (1 / p) ≤
      2 * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) + (q : ℝ) / (p : ℝ) ^ 2 := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 < (p : ℝ) ^ ((1 : ℝ) / q) := Real.rpow_pos_of_pos hp0 _
  have hs1 : 1 ≤ (p : ℝ) ^ ((1 : ℝ) / q) := Real.one_le_rpow (by linarith) (by positivity)
  have hid : (p : ℝ) ^ (((q : ℝ) - 1) / q) * (p : ℝ) ^ ((1 : ℝ) / q) = p :=
    rpow_beta_add _ hp0 q hq1
  have hpβ : (p : ℝ) ^ (((q : ℝ) - 1) / q) = p / (p : ℝ) ^ ((1 : ℝ) / q) :=
    eq_div_of_mul_eq hs0.ne' hid
  have ht : tq q p = (p : ℝ) ^ ((1 : ℝ) / q) / p := by
    unfold tq
    rw [hpβ, one_div_div]
  have hs2 : ((p : ℝ) ^ ((1 : ℝ) / q)) ^ 2 ≤ p := by
    have hexp : (1 : ℝ) / q + 1 / q ≤ 1 := by
      rw [← add_div, div_le_one hqpos]
      linarith
    calc ((p : ℝ) ^ ((1 : ℝ) / q)) ^ 2 = (p : ℝ) ^ ((1 : ℝ) / q + 1 / q) := by
          rw [sq, ← Real.rpow_add hp0]
      _ ≤ (p : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
      _ = p := Real.rpow_one _
  have hqq : (q : ℝ) ^ ((1 : ℝ) / q) ≤ 2 := by
    have h2q : (q : ℝ) ≤ 2 ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
    calc (q : ℝ) ^ ((1 : ℝ) / q) ≤ ((2 : ℝ) ^ q) ^ ((1 : ℝ) / q) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h2q (by positivity)
      _ = 2 := by
          rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_one_div_cancel hq0,
            Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    exact div_pos hs0 hp0
  · rw [ht]
    have hw0 : 0 ≤ (p : ℝ) ^ ((1 : ℝ) / q) / p := div_nonneg hs0.le hp0.le
    have htsq : ((p : ℝ) ^ ((1 : ℝ) / q) / p) ^ 2 ≤ 1 / 2 := by
      rw [div_pow, div_le_iff₀ (pow_pos hp0 2)]
      nlinarith [mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ p - 2)]
    nlinarith
  · intro hpq
    rw [ht]
    have hsq : (p : ℝ) ^ ((1 : ℝ) / q) ≤ 2 := by
      calc (p : ℝ) ^ ((1 : ℝ) / q) ≤ (q : ℝ) ^ ((1 : ℝ) / q) :=
            Real.rpow_le_rpow hp0.le (by exact_mod_cast hpq) (by positivity)
        _ ≤ 2 := hqq
    exact div_le_div_of_nonneg_right hsq hp0.le
  · intro hqp
    have hqβ : (q : ℝ) ^ (((q : ℝ) - 1) / q) * (q : ℝ) ^ ((1 : ℝ) / q) = q :=
      rpow_beta_add _ hqpos q hq1
    have hqβpos : 0 < (q : ℝ) ^ (((q : ℝ) - 1) / q) := Real.rpow_pos_of_pos hqpos _
    have hβ0 : (0 : ℝ) ≤ ((q : ℝ) - 1) / q := div_nonneg (by linarith) hqpos.le
    have hle : (q : ℝ) ^ (((q : ℝ) - 1) / q) ≤ (p : ℝ) ^ (((q : ℝ) - 1) / q) :=
      Real.rpow_le_rpow hqpos.le (by exact_mod_cast hqp) hβ0
    have hX : (q : ℝ) ^ ((1 : ℝ) / q) = q / (q : ℝ) ^ (((q : ℝ) - 1) / q) :=
      eq_div_of_mul_eq hqβpos.ne' (by rw [mul_comm]; exact hqβ)
    unfold tq
    calc (q : ℝ) * (1 / (p : ℝ) ^ (((q : ℝ) - 1) / q)) ≤
          (q : ℝ) * (1 / (q : ℝ) ^ (((q : ℝ) - 1) / q)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hqβpos hle) hqpos.le
      _ = (q : ℝ) ^ ((1 : ℝ) / q) := by rw [mul_one_div, hX]
      _ ≤ 2 := hqq
  · rw [ht]
    have hbern : (p : ℝ) ^ ((1 : ℝ) / q) ≤ 1 + 2 / q * ((p : ℝ) ^ ((1 : ℝ) / 2) - 1) := by
      have hsq0 : 0 ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by positivity
      have h := rpow_one_add_le_one_add_mul_self (s := (p : ℝ) ^ ((1 : ℝ) / 2) - 1)
        (by linarith) (p := 2 / q) (by positivity) (by rw [div_le_one hqpos]; linarith)
      have e1 : 1 + ((p : ℝ) ^ ((1 : ℝ) / 2) - 1) = (p : ℝ) ^ ((1 : ℝ) / 2) := by ring
      have e2 : (1 : ℝ) / 2 * (2 / q) = 1 / q := by ring
      rw [e1, ← Real.rpow_mul hp0.le, e2] at h
      exact h
    have hqs : (q : ℝ) * (p : ℝ) ^ ((1 : ℝ) / q) ≤ 2 * (p : ℝ) ^ ((1 : ℝ) / 2) + q := by
      have h1 := mul_le_mul_of_nonneg_left hbern hqpos.le
      have e : (q : ℝ) * (2 / q) = 2 := mul_div_cancel₀ 2 hq0
      rw [mul_add, mul_one, ← mul_assoc, e] at h1
      linarith
    have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos hp0 2
    rw [show (q : ℝ) * ((p : ℝ) ^ ((1 : ℝ) / q) / p) * (1 / p) =
        ((q : ℝ) * (p : ℝ) ^ ((1 : ℝ) / q)) / (p : ℝ) ^ 2 by ring,
      show 2 * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) + (q : ℝ) / (p : ℝ) ^ 2 =
        (2 * (p : ℝ) ^ ((1 : ℝ) / 2) + q) / (p : ℝ) ^ 2 by ring]
    exact div_le_div_of_nonneg_right hqs hp2pos.le

lemma mu_le_exp (q B p : ℕ) (hp : p.Prime) (hq : 3 ≤ q) :
    mu q B p ≤ Real.exp (if p ≤ q then 8 * q * (1 / p) else
      4 * Real.exp 8 * (2 * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) + q / (p : ℝ) ^ 2)) := by
  obtain ⟨ht0, ht1, hle, hge, hamgm⟩ := t_bounds p q hp.two_le hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hu0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hu1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]
    exact_mod_cast hp.one_lt.le
  obtain ⟨hmu1, hmu2⟩ := mu_bounds q B (tq q p) (1 / p) ht0.le ht1 hu0 hu1
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  split_ifs with hpq
  · refine le_trans hmu1 (Real.exp_le_exp.mpr ?_)
    have := mul_le_mul_of_nonneg_left (hle hpq) hq0
    have e : (q : ℝ) * (2 / p) = 2 * (q * (1 / p)) := by ring
    nlinarith
  · have hqp : q ≤ p := by omega
    have hqt := hge hqp
    have hs : 4 * (q : ℝ) * tq q p ≤ 8 := by linarith
    have hqt0 : 0 ≤ 4 * (q : ℝ) * tq q p := mul_nonneg (by positivity) ht0.le
    have hE : Real.exp (4 * q * tq q p) - 1 ≤ 4 * q * tq q p * Real.exp 8 := by
      calc Real.exp (4 * q * tq q p) - 1 ≤ 4 * q * tq q p * Real.exp (4 * q * tq q p) :=
            exp_sub_one_le_mul_exp _
        _ ≤ 4 * q * tq q p * Real.exp 8 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) hqt0
    have hE' : 1 / (p : ℝ) * (Real.exp (4 * q * tq q p) - 1) ≤
        1 / (p : ℝ) * (4 * q * tq q p * Real.exp 8) := mul_le_mul_of_nonneg_left hE hu0
    have hA := mul_le_mul_of_nonneg_left hamgm (by positivity : (0 : ℝ) ≤ 4 * Real.exp 8)
    have e2 : 1 / (p : ℝ) * (4 * q * tq q p * Real.exp 8) =
        4 * Real.exp 8 * ((q : ℝ) * tq q p * (1 / p)) := by ring
    have hexp := Real.add_one_le_exp (1 / (p : ℝ) * (4 * q * tq q p * Real.exp 8))
    calc mu q B p ≤ 1 + 1 / p * (Real.exp (4 * q * tq q p) - 1) := hmu2
      _ ≤ Real.exp (1 / (p : ℝ) * (4 * q * tq q p * Real.exp 8)) := by linarith
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [e2]; exact hA)

lemma psi_le_exp (q B p : ℕ) (hp : p.Prime) (hq : 3 ≤ q) :
    psi q B p ≤ Real.exp (if p ≤ q then 9 * q * (1 / p) else 2 * Real.exp 8 * (1 / (p : ℝ) ^ 2)) := by
  obtain ⟨ht0, ht1, hle, hge, -⟩ := t_bounds p q hp.two_le hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hv0 : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
  have hv1 : 1 / (p : ℝ) ^ 2 ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hpsi := psi_bound q B (tq q p) (1 / (p : ℝ) ^ 2) ht0.le ht1 hv0 hv1
  have hY0 : 0 ≤ Real.exp (4 * q * tq q p) := (Real.exp_pos _).le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  split_ifs with hpq
  · have hqt0 : 0 ≤ 4 * (q : ℝ) * tq q p := mul_nonneg (by positivity) ht0.le
    have hY1 : 1 ≤ Real.exp (4 * q * tq q p) := Real.one_le_exp hqt0
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2v : 2 * (1 / (p : ℝ) ^ 2) ≤ 1 := by linarith
    have hqp : (1 : ℝ) ≤ q * (1 / p) := by
      rw [mul_one_div, le_div_iff₀ hp0, one_mul]
      exact_mod_cast hpq
    have htq := mul_le_mul_of_nonneg_left (hle hpq) hq0
    have hstep : 1 + 2 * (1 / (p : ℝ) ^ 2) * Real.exp (4 * q * tq q p) ≤
        Real.exp 1 * Real.exp (4 * q * tq q p) := by
      nlinarith [mul_le_mul_of_nonneg_right h2v hY0, mul_le_mul_of_nonneg_right h2e hY0]
    calc psi q B p ≤ 1 + 2 * (1 / (p : ℝ) ^ 2) * Real.exp (4 * q * tq q p) := hpsi
      _ ≤ Real.exp 1 * Real.exp (4 * q * tq q p) := hstep
      _ = Real.exp (1 + 4 * q * tq q p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (9 * q * (1 / p)) := by
          apply Real.exp_le_exp.mpr
          have e : (q : ℝ) * (2 / p) = 2 * (q * (1 / p)) := by ring
          nlinarith
  · have hqp : q ≤ p := by omega
    have hqt := hge hqp
    have hY : Real.exp (4 * q * tq q p) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
    have hexp := Real.add_one_le_exp (2 * Real.exp 8 * (1 / (p : ℝ) ^ 2))
    calc psi q B p ≤ 1 + 2 * (1 / (p : ℝ) ^ 2) * Real.exp (4 * q * tq q p) := hpsi
      _ ≤ 1 + 2 * Real.exp 8 * (1 / (p : ℝ) ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 2 * (1 / (p : ℝ) ^ 2))]
      _ ≤ Real.exp (2 * Real.exp 8 * (1 / (p : ℝ) ^ 2)) := by linarith

/-! ### Sums over primes -/

lemma sum_primes_small (q B : ℕ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ p ∈ (primesLe B).filter (fun p => p ≤ q), f p ≤
      ∑ p ∈ (Finset.Iic q).filter Nat.Prime, f p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    unfold primesLe at hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Iic] at hp ⊢
    exact ⟨hp.2, hp.1.2⟩
  · intro p _ _
    exact hf p

lemma sum_primes_large_inv_sq (q B : ℕ) :
    ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q), 1 / (p : ℝ) ^ 2 ≤ (2 : ℝ) / ((q : ℝ) + 1) := by
  calc ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q), 1 / (p : ℝ) ^ 2
      ≤ ∑ i ∈ Finset.Ioo q (B + 1), 1 / (i : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          unfold primesLe at hp
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo] at hp ⊢
          obtain ⟨⟨h1, -⟩, h2⟩ := hp
          omega
        · intro i _ _
          positivity
    _ = ∑ i ∈ Finset.Ioo q (B + 1), ((i : ℝ) ^ 2)⁻¹ :=
        Finset.sum_congr rfl (fun i _ => one_div _)
    _ ≤ (2 : ℝ) / ((q : ℝ) + 1) := sum_Ioo_inv_sq_le q (B + 1)

lemma sum_rpow_le_tsum (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    ∑ p ∈ S, (p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2 ≤ ∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  calc ∑ p ∈ S, (p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2 = ∑ p ∈ S, ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hS p hp
        rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_sub hp0, ← Real.rpow_neg hp0.le]
        congr 1
        norm_num
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := hsum.sum_le_tsum S (fun n _ => by positivity)

lemma mertens_upper (hM : Std_Mertens2) : ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ q : ℕ, 3 ≤ q →
    ∑ p ∈ (Finset.Iic q).filter Nat.Prime, (1 : ℝ) / p ≤ Real.log (Real.log q) + c0 := by
  obtain ⟨M, C, h⟩ := hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|M| + |C| / Real.log 2, add_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) hlog2.le),
    fun q hq => ?_⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
  have hx := h q hq2
  rw [Nat.floor_natCast] at hx
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hlogq0 : 0 < Real.log q := lt_of_lt_of_le hlog2 hlogq
  have hCq : C / Real.log q ≤ |C| / Real.log 2 := by
    rw [div_le_div_iff₀ hlogq0 hlog2]
    nlinarith [mul_le_mul_of_nonneg_left hlogq (abs_nonneg C),
      mul_le_mul_of_nonneg_right (le_abs_self C) hlog2.le]
  have h2 := (abs_le.mp hx).2
  linarith [le_abs_self M]

lemma final_bound (X : ℕ → ℕ → ℝ) (A a c0 : ℝ) (ha : 0 ≤ a) (hc0 : 0 ≤ c0)
    (h : ∀ q : ℕ, 3 ≤ q → ∀ B : ℕ,
      X q B ≤ Real.exp (A + a * q * (Real.log (Real.log q) + c0))) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ B : ℕ,
      X q B ≤ K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ))) := by
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hl0 : 0 < Real.log (Real.log 3) := Real.log_pos hl3
  have hC0 : 0 ≤ a * c0 / Real.log (Real.log 3) := div_nonneg (mul_nonneg ha hc0) hl0.le
  refine ⟨a + a * c0 / Real.log (Real.log 3) + 1, by linarith, Real.exp A,
    fun q hq B => le_trans (h q hq B) ?_⟩
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : Real.log (Real.log 3) ≤ Real.log (Real.log q) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) hq3)
  have hLpos : 0 < Real.log (Real.log q) := lt_of_lt_of_le hl0 hL
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have key : a * c0 ≤ a * c0 / Real.log (Real.log 3) * Real.log (Real.log q) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl0]
    exact mul_le_mul_of_nonneg_left hL (mul_nonneg ha hc0)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left key hq0, mul_nonneg hq0 hLpos.le]

end Principia.Erdos1054.Proofs.Kovac

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.Kovac in
/-- **`KovacMoment_reflection`** (EP1054 lines 1003–1009): divisor reflection
`σ_j(n)/n = ∑_{i > j} 1/r_i`, the index `i` of a divisor `r` being `1 + #{d ∣ n : d < r}`. -/
theorem Principia.Erdos1054.Proofs.leaf_KovacMoment_reflection :
    Principia.Erdos1054.KovacMoment_reflection := by
  intro n hn j
  have hn0 : n ≠ 0 := by omega
  rw [sigmaPrefix_eq_sum, Nat.cast_sum, Finset.sum_div, Finset.sum_filter, Finset.sum_filter]
  have key := Nat.sum_div_divisors n
    (fun r => if j ≤ (n.divisors.filter (· < r)).card then (1 : ℝ) / r else 0)
  refine Eq.trans ?_ key
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hrr := rank_add_rank_div n d hn0 hd
  have hiff : (n.divisors.filter (· < d)).card < n.divisors.card - j ↔
      j ≤ (n.divisors.filter (· < n / d)).card := by omega
  have hdpos : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  by_cases h : j ≤ (n.divisors.filter (· < n / d)).card
  · rw [if_pos (hiff.mpr h), if_pos h, Nat.cast_div hdn hdpos, one_div_div]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.Kovac in
/-- **`KovacMoment_identity`** from `KovacMoment_reflection` (EP1054 lines 1010–1019). -/
theorem Principia.Erdos1054.Proofs.link_KovacMoment_identity :
    Principia.Erdos1054.Spine.Link_KovacMoment_identity := by
  intro hrefl q _hq n hn
  unfold S4a.prefixMoment
  have h1 : ∀ j ∈ Finset.range n.divisors.card, ((sigmaPrefix j n : ℝ) / n) ^ q
      = (∑ r ∈ n.divisors.filter (fun r => j ≤ (n.divisors.filter (· < r)).card),
          (1 : ℝ) / r) ^ q := by
    intro j _
    rw [hrefl n hn j]
  rw [Finset.sum_congr rfl h1]
  symm
  refine Finset.sum_bij (fun r0 _ => (n.divisors.filter (· < r0)).card)
    (fun r0 hr0 => Finset.mem_range.mpr (rank_lt_card hr0)) ?_ ?_ ?_
  · intro a ha b hb hab
    exact le_antisymm ((rank_le_rank_iff hb).mp hab.le) ((rank_le_rank_iff ha).mp hab.ge)
  · intro j hj
    obtain ⟨a, ha, hja⟩ := exists_rank_eq (Finset.mem_range.mp hj)
    exact ⟨a, ha, hja⟩
  · intro r0 hr0
    have hfil : n.divisors.filter (fun r => (n.divisors.filter (· < r0)).card ≤
        (n.divisors.filter (· < r)).card) = n.divisors.filter (r0 ≤ ·) :=
      Finset.filter_congr (fun r hr => rank_le_rank_iff hr)
    rw [hfil, pow_sum_eq_sum_pi, ← piFinset_filter_le]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.prod_div_distrib, Finset.prod_const_one]

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.Kovac in
/-- **`KovacMoment_reduction`** from `KovacMoment_identity` (EP1054 lines 1020–1022). -/
theorem Principia.Erdos1054.Proofs.link_KovacMoment_reduction :
    Principia.Erdos1054.Spine.Link_KovacMoment_reduction := by
  intro hid q hq x hx
  have hBx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have step1 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, S4a.prefixMoment q n =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, ∑ a ∈ (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 ⌊x⌋₊).filter
          (fun a => ∀ i, r ≤ a i),
        (if Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) ∣ n then 1 / ∏ i, (a i : ℝ)
          else 0) := by
    intro n hnB
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnB).1
    have hnB' : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hnB).2
    have hn0 : n ≠ 0 := by omega
    rw [hid q hq n hn1]
    have hsub : n.divisors ⊆ Finset.Icc 1 ⌊x⌋₊ := by
      intro d hd
      have h1 := Nat.divisor_le hd
      have h2 := Nat.pos_of_mem_divisors hd
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine Eq.trans ?_ (Finset.sum_subset hsub ?_)
    · refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrn : r ∣ n := Nat.dvd_of_mem_divisors hr
      have hsub2 : (Fintype.piFinset fun _ : Fin q => n.divisors).filter (fun a => ∀ i, r ≤ a i) ⊆
          (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 ⌊x⌋₊).filter
            (fun a => ∀ i, r ≤ a i) := by
        intro a ha
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at ha ⊢
        exact ⟨fun i => hsub (ha.1 i), ha.2⟩
      refine Eq.trans ?_ (Finset.sum_subset hsub2 ?_)
      · refine Finset.sum_congr rfl (fun a ha => ?_)
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at ha
        rw [if_pos]
        rw [Nat.lcm_dvd_iff, Finset.lcm_dvd_iff]
        exact ⟨hrn, fun i _ => Nat.dvd_of_mem_divisors (ha.1 i)⟩
      · intro a ha hna
        rw [if_neg]
        intro hL
        rw [Nat.lcm_dvd_iff, Finset.lcm_dvd_iff] at hL
        apply hna
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at ha ⊢
        exact ⟨fun i => Nat.mem_divisors.mpr ⟨hL.2 i (Finset.mem_univ _), hn0⟩, ha.2⟩
    · intro r _ hr
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      intro hL
      exact hr (Nat.mem_divisors.mpr ⟨(Nat.lcm_dvd_iff.mp hL).1, hn0⟩)
  rw [Finset.sum_congr rfl step1, Finset.sum_comm, S4a.kovacS, Finset.mul_sum]
  refine Finset.sum_le_sum (fun r _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun a ha => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  have hP : 0 ≤ 1 / ∏ i, (a i : ℝ) := by positivity
  calc (((⌊x⌋₊ / Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℕ) : ℝ) *
        (1 / ∏ i, (a i : ℝ)))
      ≤ ((⌊x⌋₊ : ℝ) / (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ)) *
          (1 / ∏ i, (a i : ℝ)) := mul_le_mul_of_nonneg_right Nat.cast_div_le hP
    _ ≤ (x / (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ)) *
          (1 / ∏ i, (a i : ℝ)) := by gcongr
    _ = x * (1 / ((∏ i, (a i : ℝ)) *
          (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ))) := by ring

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.Kovac in
/-- **`KovacS_le_S1S2`** (EP1054 lines 1028–1053): `S ≤ S' S''` at every truncation level. -/
theorem Principia.Erdos1054.Proofs.leaf_KovacS_le_S1S2 :
    Principia.Erdos1054.KovacS_le_S1S2 := by
  intro q hq B
  have hq1 : 1 ≤ q := by omega
  unfold S4a.kovacS S4a.kovacS1 S4a.kovacS2
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun r hr => ?_)
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrB : r ≤ B := (Finset.mem_Icc.mp hr).2
  have hR : 1 / (r : ℝ) ^ 2 * (∑ d ∈ r.divisors, 1 / (d : ℝ) ^ (((q : ℝ) - 1) / q)) ^ q *
      ∑ c ∈ Fintype.piFinset (fun _ : Fin q => Finset.Icc 1 B),
        1 / ((∏ i, (c i : ℝ) ^ (((q : ℝ) - 1) / q)) *
          (((Finset.univ : Finset (Fin q)).lcm c : ℕ) : ℝ)) =
      ∑ p ∈ (Fintype.piFinset fun _ : Fin q => r.divisors) ×ˢ
          (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B),
        (1 / (r : ℝ) ^ 2 * ∏ i, 1 / ((p.1 i : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
          (1 / ((∏ i, ((p.2 i : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
            (((Finset.univ : Finset (Fin q)).lcm p.2 : ℕ) : ℝ))) := by
    rw [pow_sum_eq_sum_pi, Finset.mul_sum (s := Fintype.piFinset fun _ : Fin q => r.divisors),
      Finset.sum_mul_sum, Finset.sum_product]
  rw [hR]
  have hinj : Set.InjOn (fun a : Fin q → ℕ =>
      ((fun i => Nat.gcd r (a i)), (fun i => a i / Nat.gcd r (a i))))
      ((Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B).filter (fun a => ∀ i, r ≤ a i) :
        Set (Fin q → ℕ)) := by
    intro a _ b _ hab
    funext i
    have h1 : Nat.gcd r (a i) = Nat.gcd r (b i) := congrFun (congrArg Prod.fst hab) i
    have h2 : a i / Nat.gcd r (a i) = b i / Nat.gcd r (b i) :=
      congrFun (congrArg Prod.snd hab) i
    calc a i = Nat.gcd r (a i) * (a i / Nat.gcd r (a i)) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right r (a i))).symm
      _ = Nat.gcd r (b i) * (b i / Nat.gcd r (b i)) := congrArg₂ (· * ·) h1 h2
      _ = b i := Nat.mul_div_cancel' (Nat.gcd_dvd_right r (b i))
  have hsub : ((Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B).filter
      (fun a => ∀ i, r ≤ a i)).image (fun a : Fin q → ℕ =>
        ((fun i => Nat.gcd r (a i)), (fun i => a i / Nat.gcd r (a i)))) ⊆
      (Fintype.piFinset fun _ : Fin q => r.divisors) ×ˢ
        (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at ha
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
    refine ⟨fun i => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left r (a i), by omega⟩, fun i => ?_⟩
    have hai := (ha.1 i).1
    have haB := (ha.1 i).2
    have hg : 0 < Nat.gcd r (a i) := Nat.gcd_pos_of_pos_left _ (by omega)
    refine Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right r (a i))) hg,
      le_trans (Nat.div_le_self _ _) haB⟩
  calc ∑ a ∈ (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B).filter (fun a => ∀ i, r ≤ a i),
        1 / ((∏ i, (a i : ℝ)) * (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ))
      ≤ ∑ a ∈ (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B).filter (fun a => ∀ i, r ≤ a i),
        (1 / (r : ℝ) ^ 2 * ∏ i, 1 / ((Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
          (1 / ((∏ i, ((a i / Nat.gcd r (a i) : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
            (((Finset.univ : Finset (Fin q)).lcm (fun i => a i / Nat.gcd r (a i)) : ℕ) : ℝ))) := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at ha
        exact term_le q hq1 r hr1 a (fun i => (ha.1 i).1) ha.2
    _ = ∑ p ∈ ((Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B).filter
          (fun a => ∀ i, r ≤ a i)).image (fun a : Fin q → ℕ =>
            ((fun i => Nat.gcd r (a i)), (fun i => a i / Nat.gcd r (a i)))),
        (1 / (r : ℝ) ^ 2 * ∏ i, 1 / ((p.1 i : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
          (1 / ((∏ i, ((p.2 i : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
            (((Finset.univ : Finset (Fin q)).lcm p.2 : ℕ) : ℝ))) :=
        (Finset.sum_image (f := fun p : (Fin q → ℕ) × (Fin q → ℕ) =>
          (1 / (r : ℝ) ^ 2 * ∏ i, 1 / ((p.1 i : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
            (1 / ((∏ i, ((p.2 i : ℕ) : ℝ) ^ (((q : ℝ) - 1) / q)) *
              (((Finset.univ : Finset (Fin q)).lcm p.2 : ℕ) : ℝ)))) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)

open Finset Principia.Erdos1054 in
/-- **`eq:k-S`** from `KovacS_le_S1S2`, `eq:k-Sprime`, `eq:k-Ssecond` (EP1054 line 1114). -/
theorem Principia.Erdos1054.Proofs.link_Eq_KS : Principia.Erdos1054.Spine.Link_Eq_KS := by
  intro hS h1 h2
  obtain ⟨C1, hC1, K1, hK1⟩ := h1
  obtain ⟨C2, hC2, K2, hK2⟩ := h2
  refine ⟨C1 + C2, by linarith, K1 * K2, fun q hq B => ?_⟩
  have hS1nn : 0 ≤ S4a.kovacS1 q B := by
    unfold S4a.kovacS1
    positivity
  have hS2nn : 0 ≤ S4a.kovacS2 q B := by
    unfold S4a.kovacS2
    positivity
  have e1 := hK1 q hq B
  have e2 := hK2 q hq B
  calc S4a.kovacS q B ≤ S4a.kovacS1 q B * S4a.kovacS2 q B := hS q hq B
    _ ≤ (K1 * Real.exp (C1 * (q : ℝ) * Real.log (Real.log (q : ℝ)))) *
        (K2 * Real.exp (C2 * (q : ℝ) * Real.log (Real.log (q : ℝ)))) :=
        mul_le_mul e1 e2 hS2nn (le_trans hS1nn e1)
    _ = K1 * K2 * Real.exp ((C1 + C2) * (q : ℝ) * Real.log (Real.log (q : ℝ))) := by
        rw [show (C1 + C2) * (q : ℝ) * Real.log (Real.log (q : ℝ)) =
          C1 * (q : ℝ) * Real.log (Real.log (q : ℝ)) +
            C2 * (q : ℝ) * Real.log (Real.log (q : ℝ)) by ring, Real.exp_add]
        ring

open Finset Principia.Erdos1054 in
/-- **`lem:kovac-moment`** from `KovacMoment_reduction` and `eq:k-S` (EP1054 lines 990–1116). -/
theorem Principia.Erdos1054.Proofs.link_Lem_KovacMoment :
    Principia.Erdos1054.Spine.Link_Lem_KovacMoment := by
  intro hred hKS
  obtain ⟨C, hC, K, hK⟩ := hKS
  refine ⟨C, hC, K, fun q hq x hx => ?_⟩
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, S4a.prefixMoment q n ≤ x * S4a.kovacS q ⌊x⌋₊ := hred q hq x hx
    _ ≤ x * (K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hK q hq ⌊x⌋₊) (by linarith)
    _ = K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ))) * x := by ring

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.Kovac in
/-- **`eq:k-Ssecond`** from Mertens' second theorem (EP1054 lines 1082–1111). -/
theorem Principia.Erdos1054.Proofs.link_Eq_KSsecond :
    Principia.Erdos1054.Spine.Link_Eq_KSsecond := by
  intro hM
  obtain ⟨c0, hc0, hmert⟩ := mertens_upper hM
  apply final_bound S4a.kovacS2
    (4 * Real.exp 8 * (2 * (∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) + 2)) 8 c0 (by norm_num) hc0
  intro q hq B
  have hPprime : ∀ p ∈ primesLe B, p.Prime := fun p hp => prime_of_mem_primesLe hp
  calc S4a.kovacS2 q B ≤ ∏ p ∈ primesLe B, mu q B p := kovacS2_le_prod q B
    _ ≤ ∏ p ∈ primesLe B, Real.exp (if p ≤ q then 8 * q * (1 / p) else
          4 * Real.exp 8 * (2 * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) + q / (p : ℝ) ^ 2)) :=
        Finset.prod_le_prod (fun p _ => by unfold mu tq; positivity)
          (fun p hp => mu_le_exp q B p (hPprime p hp) hq)
    _ = Real.exp (∑ p ∈ primesLe B, (if p ≤ q then 8 * q * (1 / p) else
          4 * Real.exp 8 * (2 * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) + q / (p : ℝ) ^ 2))) :=
        (Real.exp_sum _ _).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_ite]
        have h1 : ∑ p ∈ (primesLe B).filter (fun p => p ≤ q), 8 * (q : ℝ) * (1 / p) ≤
            8 * q * (Real.log (Real.log q) + c0) := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (sum_primes_small q B (fun p => 1 / (p : ℝ)) (fun p => by positivity))
            (hmert q hq)
        have h2 : ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q),
            4 * Real.exp 8 * (2 * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) + q / (p : ℝ) ^ 2) ≤
            4 * Real.exp 8 * (2 * (∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) + 2) := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          have hZ := sum_rpow_le_tsum ((primesLe B).filter (fun p => ¬ p ≤ q))
            (fun p hp => (hPprime p (Finset.mem_filter.mp hp).1).pos)
          have hq2 : ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q), (q : ℝ) / (p : ℝ) ^ 2 ≤ 2 := by
            have hqpos : (0 : ℝ) < q + 1 := by positivity
            calc ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q), (q : ℝ) / (p : ℝ) ^ 2 =
                  (q : ℝ) * ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q), 1 / (p : ℝ) ^ 2 := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
              _ ≤ (q : ℝ) * ((2 : ℝ) / ((q : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_left (sum_primes_large_inv_sq q B) (Nat.cast_nonneg _)
              _ ≤ 2 := by
                  rw [mul_div_assoc', div_le_iff₀ hqpos]
                  linarith
          linarith
        linarith

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.Kovac in
/-- **`eq:k-Sprime`** from Mertens' second theorem (EP1054 lines 1056–1078). -/
theorem Principia.Erdos1054.Proofs.link_Eq_KSprime :
    Principia.Erdos1054.Spine.Link_Eq_KSprime := by
  intro hM
  obtain ⟨c0, hc0, hmert⟩ := mertens_upper hM
  apply final_bound S4a.kovacS1 (2 * Real.exp 8) 9 c0 (by norm_num) hc0
  intro q hq B
  have hPprime : ∀ p ∈ primesLe B, p.Prime := fun p hp => prime_of_mem_primesLe hp
  calc S4a.kovacS1 q B ≤ ∏ p ∈ primesLe B, psi q B p := kovacS1_le_prod q B
    _ ≤ ∏ p ∈ primesLe B, Real.exp (if p ≤ q then 9 * q * (1 / p) else
          2 * Real.exp 8 * (1 / (p : ℝ) ^ 2)) :=
        Finset.prod_le_prod (fun p _ => by unfold psi tq; positivity)
          (fun p hp => psi_le_exp q B p (hPprime p hp) hq)
    _ = Real.exp (∑ p ∈ primesLe B, (if p ≤ q then 9 * q * (1 / p) else
          2 * Real.exp 8 * (1 / (p : ℝ) ^ 2))) :=
        (Real.exp_sum _ _).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_ite]
        have h1 : ∑ p ∈ (primesLe B).filter (fun p => p ≤ q), 9 * (q : ℝ) * (1 / p) ≤
            9 * q * (Real.log (Real.log q) + c0) := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (sum_primes_small q B (fun p => 1 / (p : ℝ)) (fun p => by positivity))
            (hmert q hq)
        have h2 : ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q),
            2 * Real.exp 8 * (1 / (p : ℝ) ^ 2) ≤ 2 * Real.exp 8 := by
          rw [← Finset.mul_sum]
          have hs := sum_primes_large_inv_sq q B
          have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
          have hq' : (2 : ℝ) / (q + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith
          have he : (0 : ℝ) ≤ 2 * Real.exp 8 := by positivity
          calc 2 * Real.exp 8 * ∑ p ∈ (primesLe B).filter (fun p => ¬ p ≤ q), 1 / (p : ℝ) ^ 2
              ≤ 2 * Real.exp 8 * 1 := mul_le_mul_of_nonneg_left (hs.trans hq') he
            _ = 2 * Real.exp 8 := mul_one _
        linarith
