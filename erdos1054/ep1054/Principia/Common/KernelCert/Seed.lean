/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.KernelCert.SubsetSum
import Principia.Common.KernelCert.Prime
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# The large seed: every integer of `[1.05·10^8, 1.56·10^8]` is a sum of four or five distinct
primes in `(2·10^7, 4·10^7)`

`seed_four_five` is the statement verbatim (`Comp_Verifier_largeSeed` of Erdős 1054, check 3 of
`verify.rs`); `seed_cover` is its subset-sum form, `N ∈ {∑ S : S ⊆ primes of (2·10^7, 4·10^7]}`.

## Why not one big subset-sum programme

The subset sums of every 1000th prime of `(2·10^7, 4·10^7)` (1164 primes) do cover the interval,
but a programme over them runs on a `1.56·10^8`-bit bitset and the kernel retains ~58 MB per
step (measured at 10, 30 and 60 steps: 0.70, 1.82 and 3.58 GB), i.e. ~68 GB for the whole
list. The certificate below never holds a bitset wider than 9·10^4 bits.

## The certificate

* **Fine level.** `seedFineLo` is the list of all 1799 primes of `(2·10^7, 2·10^7 + 3·10^4)`
  (`coprimeScan`, prime by construction). A subset-sum programme with weights `(p − d)/2`,
  `d = 19 940 021`, on a 89 096-bit bitset (`seedFineLo_dp`) shows, by `ksum_cover`, that every
  even number of `[40 002 028, 40 058 232]` is a sum of two distinct such primes. Same for
  `seedFineHi` (1778 primes of `(3.96·10^7, 3.963·10^7)`), even numbers of
  `[79 202 358, 79 258 700]`.
* **Coarse levels.** `seedCoarse` is 358 primes of `(2.003·10^7, 4·10^7)` with consecutive gaps
  `≤ 56 204` (the width of the fine window), checked prime by `primeUpTo 6325`; adjoining it
  (`Cov2.extend_list`) gives all odd numbers of `[60 032 039, 80 010 271]` as 3-prime sums. Three
  further primes (gaps `≤ 2·10^7`, `seedQ4`) give the even numbers of `[80 132 062, 120 005 288]`
  as 4-prime sums; three more (`seedQ5`) the odd numbers of `[100 332 075, 160 001 311]` as
  5-prime sums. From the high fine window, the first 351 coarse primes and `seedQ4b` give the
  even numbers of `[119 332 392, 158 810 118]` as 4-prime sums.

The whole file (seven `decide +kernel` certificates, which Lean checks in parallel) compiles in
~50 s wall-clock with a 1.6 GB peak; `seedFineLo_dp` alone: ~15 s, +0.55 GB over the import
baseline.

The windows, the coarse step `55 804` and the primes of `seedQ4`, `seedQ5`, `seedQ4b` were chosen
offline; the proof depends on none of that search, because every fact it uses is re-checked here
by `decide +kernel`.
-/

namespace Principia.Common.KernelCert

open Finset

/-! ## The lists -/

/-- All primes of `[20 000 001, 20 029 999]` (odd `n` there with `gcd(n, 6325!) = 1`). -/
def seedFineLo : List ℕ := coprimeScan (sieveProd 6325) 2 15000 20000001

/-- All primes of `[39 600 001, 39 629 999]`. -/
def seedFineHi : List ℕ := coprimeScan (sieveProd 6325) 2 15000 39600001

/-- 358 primes: the first number coprime to `6325!` at or after `20 030 001 + 55 804 i`. -/
def seedCoarse : List ℕ :=
  (List.range 358).map (fun i => nextCoprime (sieveProd 6325) 1000 (20030001 + i * 55804))

/-- The first 351 coarse primes, all below `39 600 001`. -/
def seedCoarseB : List ℕ := seedCoarse.take 351

/-- Three primes of the second coarse level. -/
def seedQ4 : List ℕ := [20100023, 30000001, 39995017]

/-- Three primes of the third coarse level. -/
def seedQ5 : List ℕ := [20200013, 30100003, 39996023]

/-- Three primes of the second level above the high fine window. -/
def seedQ4b : List ℕ := [20100023, 30000001, 39990011]

/-- The per-element test of a coarse list. -/
def seedElt (q : ℕ) : Bool :=
  primeUpTo 6325 q && q % 2 == 1 && decide (20030000 < q) && decide (q < 40000000)

/-! ## The kernel checks -/

/-- The low fine window (the only large computation: 1799 programme steps). -/
theorem seedFineLo_dp :
    allOnes (ssBitsW (fun p => (p - 19940021) / 2) seedFineLo 89095) 60993 89095 = true := by
  decide +kernel

/-- The high fine window. -/
theorem seedFineHi_dp :
    allOnes (ssBitsW (fun p => (p - 39540045) / 2) seedFineHi 89305) 61134 89305 = true := by
  decide +kernel

theorem seedCoarse_ok :
    (seedCoarse.head? == some 20030011 && chainTo 56204 39952039 seedCoarse &&
      seedCoarse.all seedElt) = true := by
  decide +kernel

theorem seedCoarseB_ok :
    (seedCoarseB.head? == some 20030011 && chainTo 56342 39561407 seedCoarseB &&
      seedCoarseB.all (fun q => decide (q < 39600001))) = true := by
  decide +kernel

theorem seedQ4_ok :
    (chainTo 19978232 39995017 seedQ4 &&
      seedQ4.all (fun q => seedElt q && !seedCoarse.contains q)) = true := by
  decide +kernel

theorem seedQ5_ok :
    (chainTo 39873226 39996023 seedQ5 &&
      seedQ5.all (fun q => seedElt q && !seedCoarse.contains q && !seedQ4.contains q)) = true := by
  decide +kernel

theorem seedQ4b_ok :
    (chainTo 19587738 39990011 seedQ4b &&
      seedQ4b.all (fun q => seedElt q && !seedCoarseB.contains q &&
        (decide (q < 39600001) || decide (39630000 < q)))) = true := by
  decide +kernel

/-! ## Facts about the lists -/

theorem mem_seedFineLo {p : ℕ} (hp : p ∈ seedFineLo) :
    p.Prime ∧ 20000001 ≤ p ∧ p ≤ 20029999 ∧ p % 2 = 1 := by
  have hpr := coprimeScan_prime (k := 6325) (by norm_num) (by norm_num) hp
  obtain ⟨-, h1, -, i, hic, hi⟩ :=
    mem_coprimeScan (P := sieveProd 6325) (s := 2) 15000 20000001 p hp
  exact ⟨hpr, h1, by omega, by omega⟩

theorem mem_seedFineHi {p : ℕ} (hp : p ∈ seedFineHi) :
    p.Prime ∧ 39600001 ≤ p ∧ p ≤ 39629999 ∧ p % 2 = 1 := by
  have hpr := coprimeScan_prime (k := 6325) (by norm_num) (by norm_num) hp
  obtain ⟨-, h1, -, i, hic, hi⟩ :=
    mem_coprimeScan (P := sieveProd 6325) (s := 2) 15000 39600001 p hp
  exact ⟨hpr, h1, by omega, by omega⟩

theorem seedElt_spec {q : ℕ} (h : seedElt q = true) :
    q.Prime ∧ q % 2 = 1 ∧ 20030000 < q ∧ q < 40000000 := by
  simp only [seedElt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨primeUpTo_sound h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem mem_seedCoarse {q : ℕ} (hq : q ∈ seedCoarse) :
    q.Prime ∧ q % 2 = 1 ∧ 20030000 < q ∧ q < 40000000 := by
  have h := seedCoarse_ok
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact seedElt_spec (h.2 q hq)

theorem mem_seedCoarseB {q : ℕ} (hq : q ∈ seedCoarseB) : q ∈ seedCoarse ∧ q < 39600001 := by
  have h := seedCoarseB_ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨List.mem_of_mem_take hq, h.2 q hq⟩

/-- The primes the certificate is allowed to use. -/
def SeedGood (p : ℕ) : Prop := p.Prime ∧ 20000000 < p ∧ p < 40000000

/-! ## The levels -/

theorem seed_fineLo : Cov2 seedFineLo.toFinset 2 40002028 40058232 :=
  cov2_of_ksum (F := seedFineLo) (d := 19940021) (k := 2) (n0 := 60993) (n1 := 89095)
    (ksum_cover (coprimeScan_nodup (by norm_num) 15000 20000001) (lo := 29990) (hi := 44989)
      (fun p hp => by
        have := mem_seedFineLo hp
        omega)
      (by norm_num) (by norm_num) seedFineLo_dp)

theorem seed_fineHi : Cov2 seedFineHi.toFinset 2 79202358 79258700 :=
  cov2_of_ksum (F := seedFineHi) (d := 39540045) (k := 2) (n0 := 61134) (n1 := 89305)
    (ksum_cover (coprimeScan_nodup (by norm_num) 15000 39600001) (lo := 29978) (hi := 44977)
      (fun p hp => by
        have := mem_seedFineHi hp
        omega)
      (by norm_num) (by norm_num) seedFineHi_dp)

/-- Odd numbers of `[60 032 039, 80 010 271]`: three primes. -/
theorem seed_L1 :
    Cov2 (seedFineLo.toFinset ∪ seedCoarse.toFinset) 3 60032039 80010271 := by
  have h := seedCoarse_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact seed_fineLo.extend_list (by norm_num) h.1.1 h.1.2
    (fun y hy => by
      have := mem_seedCoarse hy
      omega)
    (fun y hy hyF => by
      have h1 := mem_seedCoarse hy
      have h2 := mem_seedFineLo (List.mem_toFinset.1 hyF)
      omega)

/-- Even numbers of `[80 132 062, 120 005 288]`: four primes. -/
theorem seed_L2 :
    Cov2 (seedFineLo.toFinset ∪ seedCoarse.toFinset ∪ seedQ4.toFinset) 4 80132062 120005288 := by
  have h := seedQ4_ok
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact seed_L1.extend_list (by norm_num) (lo := 20100023) rfl h.1
    (fun y hy => by
      have := (seedElt_spec (h.2 y hy).1).2.1
      omega)
    (fun y hy hyP => by
      have hy' := h.2 y hy
      rcases Finset.mem_union.1 hyP with hF | hC
      · have h1 := seedElt_spec hy'.1
        have h2 := mem_seedFineLo (List.mem_toFinset.1 hF)
        omega
      · have := List.contains_iff_mem.2 (List.mem_toFinset.1 hC)
        rw [hy'.2] at this
        exact Bool.false_ne_true this)

/-- Odd numbers of `[100 332 075, 160 001 311]`: five primes. -/
theorem seed_L3 :
    Cov2 (seedFineLo.toFinset ∪ seedCoarse.toFinset ∪ seedQ4.toFinset ∪ seedQ5.toFinset) 5
      100332075 160001311 := by
  have h := seedQ5_ok
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact seed_L2.extend_list (by norm_num) (lo := 20200013) rfl h.1
    (fun y hy => by
      have := (seedElt_spec (h.2 y hy).1.1).2.1
      omega)
    (fun y hy hyP => by
      have hy' := h.2 y hy
      rcases Finset.mem_union.1 hyP with hFC | h4
      · rcases Finset.mem_union.1 hFC with hF | hC
        · have h1 := seedElt_spec hy'.1.1
          have h2 := mem_seedFineLo (List.mem_toFinset.1 hF)
          omega
        · have := List.contains_iff_mem.2 (List.mem_toFinset.1 hC)
          rw [hy'.1.2] at this
          exact Bool.false_ne_true this
      · have := List.contains_iff_mem.2 (List.mem_toFinset.1 h4)
        rw [hy'.2] at this
        exact Bool.false_ne_true this)

/-- Odd numbers of `[99 232 369, 118 820 107]` from the high fine window: three primes. -/
theorem seed_L1b :
    Cov2 (seedFineHi.toFinset ∪ seedCoarseB.toFinset) 3 99232369 118820107 := by
  have h := seedCoarseB_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact seed_fineHi.extend_list (by norm_num) h.1.1 h.1.2
    (fun y hy => by
      have := mem_seedCoarse (mem_seedCoarseB hy).1
      omega)
    (fun y hy hyF => by
      have h1 := (mem_seedCoarseB hy).2
      have h2 := mem_seedFineHi (List.mem_toFinset.1 hyF)
      omega)

/-- Even numbers of `[119 332 392, 158 810 118]`: four primes. -/
theorem seed_L2b :
    Cov2 (seedFineHi.toFinset ∪ seedCoarseB.toFinset ∪ seedQ4b.toFinset) 4 119332392
      158810118 := by
  have h := seedQ4b_ok
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    decide_eq_true_eq] at h
  exact seed_L1b.extend_list (by norm_num) (lo := 20100023) rfl h.1
    (fun y hy => by
      have := (seedElt_spec (h.2 y hy).1.1).2.1
      omega)
    (fun y hy hyP => by
      have hy' := h.2 y hy
      rcases Finset.mem_union.1 hyP with hF | hC
      · have h2 := mem_seedFineHi (List.mem_toFinset.1 hF)
        omega
      · have := List.contains_iff_mem.2 (List.mem_toFinset.1 hC)
        rw [hy'.1.2] at this
        exact Bool.false_ne_true this)

/-! ## Every prime used is admissible -/

theorem seedGood_fineLo {p : ℕ} (hp : p ∈ seedFineLo.toFinset) : SeedGood p := by
  have := mem_seedFineLo (List.mem_toFinset.1 hp)
  exact ⟨this.1, by omega, by omega⟩

theorem seedGood_fineHi {p : ℕ} (hp : p ∈ seedFineHi.toFinset) : SeedGood p := by
  have := mem_seedFineHi (List.mem_toFinset.1 hp)
  exact ⟨this.1, by omega, by omega⟩

theorem seedGood_coarse {p : ℕ} (hp : p ∈ seedCoarse.toFinset) : SeedGood p := by
  have := mem_seedCoarse (List.mem_toFinset.1 hp)
  exact ⟨this.1, by omega, by omega⟩

theorem seedGood_coarseB {p : ℕ} (hp : p ∈ seedCoarseB.toFinset) : SeedGood p :=
  seedGood_coarse (List.mem_toFinset.2 (mem_seedCoarseB (List.mem_toFinset.1 hp)).1)

theorem seedGood_list {l : List ℕ} (hl : ∀ q ∈ l, seedElt q = true) {p : ℕ}
    (hp : p ∈ l.toFinset) : SeedGood p := by
  have := seedElt_spec (hl p (List.mem_toFinset.1 hp))
  exact ⟨this.1, by omega, this.2.2.2⟩

theorem seedQ4_elt : ∀ q ∈ seedQ4, seedElt q = true := by
  have h := seedQ4_ok
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact fun q hq => (h.2 q hq).1

theorem seedQ5_elt : ∀ q ∈ seedQ5, seedElt q = true := by
  have h := seedQ5_ok
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact fun q hq => (h.2 q hq).1.1

theorem seedQ4b_elt : ∀ q ∈ seedQ4b, seedElt q = true := by
  have h := seedQ4b_ok
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact fun q hq => (h.2 q hq).1.1

/-! ## The seed -/

/-- **The large seed** (`Comp_Verifier_largeSeed`, verbatim): every integer of
`[105 000 000, 156 000 000]` is a sum of four (even) or five (odd) distinct primes in
`(20 000 000, 40 000 000)`. -/
theorem seed_four_five : ∀ N : ℕ, 105000000 ≤ N → N ≤ 156000000 →
    ∃ S : Finset ℕ, (S.card = 4 ∨ S.card = 5) ∧
      (∀ p ∈ S, p.Prime ∧ 20000000 < p ∧ p < 40000000) ∧ ∑ p ∈ S, p = N := by
  intro N h1 h2
  by_cases hodd : N % 2 = 1
  · obtain ⟨S, hS, hc, hs⟩ := seed_L3 N (by omega) (by omega) (by omega)
    refine ⟨S, Or.inr hc, fun p hp => ?_, hs⟩
    rcases Finset.mem_union.1 (hS hp) with h | h5
    · rcases Finset.mem_union.1 h with h | h4
      · rcases Finset.mem_union.1 h with hF | hC
        · exact seedGood_fineLo hF
        · exact seedGood_coarse hC
      · exact seedGood_list seedQ4_elt h4
    · exact seedGood_list seedQ5_elt h5
  · by_cases hlow : N ≤ 120005288
    · obtain ⟨S, hS, hc, hs⟩ := seed_L2 N (by omega) hlow (by omega)
      refine ⟨S, Or.inl hc, fun p hp => ?_, hs⟩
      rcases Finset.mem_union.1 (hS hp) with h | h4
      · rcases Finset.mem_union.1 h with hF | hC
        · exact seedGood_fineLo hF
        · exact seedGood_coarse hC
      · exact seedGood_list seedQ4_elt h4
    · obtain ⟨S, hS, hc, hs⟩ := seed_L2b N (by omega) (by omega) (by omega)
      refine ⟨S, Or.inl hc, fun p hp => ?_, hs⟩
      rcases Finset.mem_union.1 (hS hp) with h | h4
      · rcases Finset.mem_union.1 h with hF | hC
        · exact seedGood_fineHi hF
        · exact seedGood_coarseB hC
      · exact seedGood_list seedQ4b_elt h4

/-- **The large seed, subset-sum form**: every integer of `[105 000 000, 156 000 000]` is a sum
of distinct primes of `(20 000 000, 40 000 000]`. -/
theorem seed_cover : ∀ N : ℕ, 105000000 ≤ N → N ≤ 156000000 →
    ∃ S ⊆ (Finset.Ioc 20000000 40000000).filter Nat.Prime, ∑ p ∈ S, p = N := by
  intro N h1 h2
  obtain ⟨S, -, hS, hs⟩ := seed_four_five N h1 h2
  refine ⟨S, fun p hp => ?_, hs⟩
  obtain ⟨hpp, hp1, hp2⟩ := hS p hp
  rw [Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hp1, hp2.le⟩, hpp⟩

end Principia.Common.KernelCert
