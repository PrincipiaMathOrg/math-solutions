/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PrimeSumExact.Window

set_option autoImplicit false

/-!
# Subset sums of the `94` primes of `(10000, 10883]` cover `[469615, 480503]`

**`subsetSums_primes_Ioc_10000_10883`**: every `N ∈ [469615, 480503]` is `∑ p ∈ S, p` for some
`S ⊆ (Ioc 10000 10883).filter Nat.Prime`.

The subset sums of a list `L` are held as ONE bitset, `dpBits L` (bit `n` set iff `n` is a subset
sum), built by `B ↦ B ||| (B <<< p)` — the recurrence `S_j = S_{j−1} ∪ (S_{j−1} + p_j)`; `coverOK`
tests a run of consecutive set bits with one shift, one mask and one `Nat.beq`. `dpBits_sound`
(for a duplicate-free list) and `coverOK_sound` are proved in general; the numbers are
`decide +kernel` evaluations. Primality of the `94` listed numbers is read off the exact sieve of
`PrimeSumExact/Sieve.lean` (`testBit_sieveBits_prime`), not re-proved one by one.
-/

namespace Principia.Common.PrimeSumExact

open Finset

/-- The subset sums of `L` as a bitset: bit `n` is set iff `n` is the sum of a sub-list. -/
def dpBits : List ℕ → ℕ
  | [] => 1
  | p :: L => dpBits L ||| (dpBits L <<< p)

/-- **Every set bit of `dpBits L` is a subset sum** (for a duplicate-free `L`). -/
theorem dpBits_sound : ∀ (L : List ℕ), L.Nodup → ∀ n, (dpBits L).testBit n = true →
    ∃ S ⊆ L.toFinset, ∑ p ∈ S, p = n
  | [], _, n, h => by
    have h1 : (2 ^ 0).testBit n = true := h
    rw [Nat.testBit_two_pow] at h1
    have h2 : 0 = n := of_decide_eq_true h1
    exact ⟨∅, by simp, by simp [← h2]⟩
  | p :: L, hnd, n, h => by
    rw [List.nodup_cons] at hnd
    have h' : ((dpBits L).testBit n || (decide (n ≥ p) && (dpBits L).testBit (n - p))) = true := by
      have e : dpBits (p :: L) = dpBits L ||| (dpBits L <<< p) := rfl
      rw [e, Nat.testBit_or, Nat.testBit_shiftLeft] at h
      exact h
    rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h'
    rcases h' with h1 | ⟨h1, h2⟩
    · obtain ⟨S, hS, hsum⟩ := dpBits_sound L hnd.2 n h1
      refine ⟨S, fun x hx => ?_, hsum⟩
      have := hS hx
      simp only [List.mem_toFinset] at this ⊢
      exact List.mem_cons_of_mem _ this
    · obtain ⟨S, hS, hsum⟩ := dpBits_sound L hnd.2 (n - p) h2
      have hpS : p ∉ S := fun hp => hnd.1 (List.mem_toFinset.mp (hS hp))
      refine ⟨insert p S, fun x hx => ?_, ?_⟩
      · rcases mem_insert.mp hx with rfl | hx
        · simp
        · have := hS hx
          simp only [List.mem_toFinset] at this ⊢
          exact List.mem_cons_of_mem _ this
      · rw [sum_insert hpS, hsum]
        omega

/-- Are bits `lo, lo + 1, …, lo + len − 1` of `B` all set? -/
def coverOK (B lo len : ℕ) : Bool := Nat.beq ((B >>> lo) &&& (2 ^ len - 1)) (2 ^ len - 1)

theorem coverOK_sound (B lo len : ℕ) (h : coverOK B lo len = true) (n : ℕ) (h1 : lo ≤ n)
    (h2 : n < lo + len) : B.testBit n = true := by
  have e : (B >>> lo) &&& (2 ^ len - 1) = 2 ^ len - 1 := Nat.eq_of_beq_eq_true h
  have t := congrArg (fun x => Nat.testBit x (n - lo)) e
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at t
  rw [show lo + (n - lo) = n by omega] at t
  have hlt : n - lo < len := by omega
  simpa [hlt] using t

/-- The `94` primes of `(10000, 10883]`. -/
def primes94 : List ℕ :=
  [10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111,
    10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243,
    10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333,
    10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459, 10463,
    10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607,
    10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723,
    10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859,
    10861, 10867, 10883]

theorem nodup_primes94 : primes94.Nodup := by
  decide +kernel

/-- Range and primality certificate: every entry lies in `(10000, 10883]` and survives the exact
sieve of `[10001, 10884)`. -/
theorem check_primes94 :
    primes94.all (fun p => Nat.blt 10000 p && Nat.ble p 10883 &&
      (sieveBits 883 10001 primesTo9949).testBit (p - 10001)) = true := by
  decide +kernel

theorem mem_primes94 (p : ℕ) (hp : p ∈ primes94) :
    p ∈ (Finset.Ioc 10000 10883).filter Nat.Prime := by
  have h := List.all_eq_true.mp check_primes94 p hp
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hpr := ((testBit_sieveBits_prime 883 10001 primesTo9949 (by decide) (by decide)
    (sieving_bounds 10001 (by decide))
    (fun q hq hqq => mem_primesTo9949_of_sq_lt q hq (by omega)) (p - 10001)).mp h3).2
  rw [show 10001 + (p - 10001) = p by omega] at hpr
  simp only [mem_filter, mem_Ioc]
  exact ⟨⟨h1, h2⟩, hpr⟩

/-- The subset-sum cover, evaluated by the kernel. -/
theorem coverOK_primes94 : coverOK (dpBits primes94) 469615 10889 = true := by
  decide +kernel

/-- **Every `N ∈ [469615, 480503]` is a sum of distinct primes of `(10000, 10883]`.** -/
theorem subsetSums_primes_Ioc_10000_10883 (N : ℕ) (h1 : 469615 ≤ N) (h2 : N ≤ 480503) :
    ∃ S ⊆ (Finset.Ioc 10000 10883).filter Nat.Prime, ∑ p ∈ S, p = N := by
  obtain ⟨S, hS, hsum⟩ := dpBits_sound primes94 nodup_primes94 N
    (coverOK_sound _ _ _ coverOK_primes94 N h1 (by omega))
  exact ⟨S, fun x hx => mem_primes94 x (List.mem_toFinset.mp (hS hx)), hsum⟩

end Principia.Common.PrimeSumExact
