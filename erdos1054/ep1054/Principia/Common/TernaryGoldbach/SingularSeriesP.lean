/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SingularSeries

set_option autoImplicit false

/-!
# `𝔖₃(N) ≥ 1.3198` for odd `N` — the singular-series peel extended to the primes below `1000`

`SingularSeries.sing3_ge_sharp` certifies `𝔖₃(N) ≥ 131/100` by evaluating the Euler product
exactly on the thirteen primes `≤ 41` and applying Weierstrass to the tail. The true infimum over
odd `N` is `2·∏_{p≥3}(1 − 1/(p−1)²) = 1.3203236…`, so that route leaves `0.0103` on the table,
and on the major arcs every `0.001` of `C₀` is worth `≈ 0.0008` of the major constant.

This file runs the SAME route with the prefix enlarged to all `168` primes below `1000`:

* **prefix** (`prefix_boundP`): `2·∏_{3≤p<1000}(1 − 1/(p−1)²) = 1.3204914879…`, computed EXACTLY
  in `ℚ` by the kernel (`prefixQ`, `decide +kernel`; numerator and denominator have `411`
  digits) and transported to `ℝ` by `Rat.cast` (`prod_bigPrimes_eq`);
* **tail** (`sum_tail_inv_sq_le_K`): for primes `p ≥ 1000`, `p − 1 = 2·(p/2)` with `p/2 ≥ 500`
  distinct, so `∑ 1/(p−1)² ≤ (1/4)·∑_{m≥500} 1/m² ≤ 1/(4·499) = 1/1996` — the parity trick of
  `SingularSeries.sum_tail_inv_sq_le`, copied by counted substitution;
* **the certified constant**: `1.3204914879…·(1 − 1/1996) = 1.3198299190… ≥ 1.3198` (margin
  `2.99·10⁻⁵`); `sing3_ge_P : Odd N → 1.3198 ≤ sing3 N`.

The loss against the true infimum is now `5.0·10⁻⁴` (was `1.03·10⁻²`), almost all of it the
`1/1996` overestimate of the true tail `∑_{p>1000}1/(p−1)² ≈ 1.26·10⁻⁴`.

**Which numbers are the primes below `1000`** is settled without `Nat.Prime`'s decision procedure,
by trial division by the primes `≤ 31` (`sieveOK`; `32² > 1000`). Two kernel computations
(`decide +kernel`, no extra axiom): every listed number passes it (`primesK_sieve`), and every
`n ∈ [2, 1000)` that passes it is listed (`sieve_complete`). Two proved bridges connect the check
to `Nat.Prime`: a composite below `1000` has a prime factor `≤ 31` (`prime_of_sieveOK`, via
`Nat.minFac_sq_le_self`), and a prime passes (`sieveOK_of_prime`).

The per-prime factor bound (`one_add_sing3Local_ge`), the factor at `2` (`one_add_sing3Local_two`),
`eulerLow`, the Euler product (`sing3_hasProd`) and the Weierstrass inequality (`prod_one_sub_ge`)
are REUSED from `SingularSeries.lean` and `Goldbach/MajorArc.lean`, not restated.
-/

namespace Principia.Common.TernaryGoldbach.SSP

open Principia.Common.TernaryGoldbach.SingularSeries
open Principia.Common.Goldbach.MajorArcMainTerm

/-! ### The primes below `1000` -/

/-- The `168` primes below `1000`, as an explicit list. -/
def primesK : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
    307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
    421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
    547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
    659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
    797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
    929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

/-- The peeled prefix as a `Finset ℕ`. -/
def bigPrimes : Finset ℕ := primesK.toFinset

/-- The same set inside `Nat.Primes`, the index type of the Euler product. -/
def bigPrimesSub : Finset Nat.Primes := bigPrimes.subtype Nat.Prime

/-- `primesK` has no repeated entry (so the `Finset` product is the list product). -/
theorem primesK_nodup : primesK.Nodup := by
  decide +kernel

/-- Trial division by the primes `≤ 31`: `n` has none of them as a factor, except itself. Since
`32² > 1000`, for `2 ≤ n < 1000` this is equivalent to primality (`prime_of_sieveOK`,
`sieveOK_of_prime`). -/
def sieveOK (n : ℕ) : Bool :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31].all (fun q => n % q != 0 || n == q)

/-- **Soundness of the sieve below `1000`**: a composite `n < 1000` has `minFac n ^ 2 ≤ n`, so its
least prime factor is a prime `≤ 31`, which the sieve would have caught. -/
theorem prime_of_sieveOK (n : ℕ) (h2 : 2 ≤ n) (hlt : n < 1000) (hs : sieveOK n = true) :
    n.Prime := by
  by_contra hnp
  obtain ⟨m, hm⟩ : ∃ m, Nat.minFac n = m := ⟨_, rfl⟩
  have hmp : m.Prime := hm ▸ Nat.minFac_prime (by omega)
  have hsq : m ^ 2 ≤ n := hm ▸ Nat.minFac_sq_le_self (by omega) hnp
  have hmod : n % m = 0 := Nat.mod_eq_zero_of_dvd (hm ▸ Nat.minFac_dvd n)
  have hne : m ≠ n := fun h => hnp (h ▸ hmp)
  have hle : m ≤ 31 := by nlinarith
  have hm2 : 2 ≤ m := hmp.two_le
  have hall := List.all_eq_true.mp hs
  interval_cases m
  · exact absurd (hall 2 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd (hall 3 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 5 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 7 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 11 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 13 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 17 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 19 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 23 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 29 (by simp)) (by simp [hmod, Ne.symm hne])
  · exact absurd hmp (by norm_num)
  · exact absurd (hall 31 (by simp)) (by simp [hmod, Ne.symm hne])

/-- Every listed number passes the sieve and lies in `[2, 1000)` — a kernel computation. -/
theorem primesK_sieve :
    primesK.all (fun n => decide (2 ≤ n) && decide (n < 1000) && sieveOK n) = true := by
  decide +kernel

/-- **Every listed number is prime.** -/
theorem primesK_prime : ∀ n ∈ primesK, n.Prime := by
  intro n hn
  have h := List.all_eq_true.mp primesK_sieve n hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact prime_of_sieveOK n h.1.1 h.1.2 h.2

/-- Every member of the prefix is prime. -/
theorem prime_of_mem_bigPrimes (n : ℕ) (hn : n ∈ bigPrimes) : n.Prime :=
  primesK_prime n (List.mem_toFinset.mp hn)

/-- **Completeness of the list, by a kernel computation**: every `n < 1000` with `n ≥ 2` that
passes trial division by the primes `≤ 31` is in `primesK`. -/
theorem sieve_complete : (List.range 1000).all
    (fun n => decide (n < 2) || !sieveOK n || primesK.contains n) = true := by
  decide +kernel

/-- A prime passes trial division: for a prime `n`, `q ∣ n` with `q ≥ 2` forces `q = n`. -/
theorem sieveOK_of_prime (n : ℕ) (hp : n.Prime) : sieveOK n = true := by
  unfold sieveOK
  rw [List.all_eq_true]
  intro q hq
  have hq2 : 2 ≤ q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    omega
  by_cases hd : n % q = 0
  · rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hd) with h1 | h1
    · omega
    · subst h1
      simp
  · simp [hd]

/-- **Every prime below `1000` is in `bigPrimes`** — the fact that makes the complement of the
prefix start at `1000`. -/
theorem mem_big_of_prime_lt (n : ℕ) (hp : n.Prime) (hlt : n < 1000) : n ∈ bigPrimes := by
  have h := List.all_eq_true.mp sieve_complete n (List.mem_range.mpr hlt)
  have h2 : decide (n < 2) = false := decide_eq_false (by have := hp.two_le; omega)
  rw [h2, sieveOK_of_prime n hp] at h
  simpa [bigPrimes] using h

/-! ### The prefix, exactly, in `ℚ` -/

/-- The comparison factor in `ℚ`: `2` at `2`, `1 − 1/(n−1)²` elsewhere (`eulerLow`'s rational
twin). -/
def eulerQ (n : ℕ) : ℚ := if n = 2 then 2 else 1 - 1 / ((n : ℚ) - 1) ^ 2

theorem eulerLow_eq_cast (n : ℕ) : eulerLow n = ((eulerQ n : ℚ) : ℝ) := by
  unfold eulerLow eulerQ
  split_ifs <;> norm_num

/-- The real prefix product is the cast of the rational list product. -/
theorem prod_bigPrimes_eq :
    ∏ n ∈ bigPrimes, eulerLow n = (((primesK.map eulerQ).prod : ℚ) : ℝ) := by
  rw [Finset.prod_congr rfl (fun n _ => eulerLow_eq_cast n), ← Rat.cast_prod, bigPrimes,
    List.prod_toFinset _ primesK_nodup]

/-- **The prefix, certified by the kernel in exact rational arithmetic**:
`2·∏_{3≤p<1000}(1−1/(p−1)²)·(1 − 1/1996) = 1.3198299190… ≥ 1.3198`. -/
theorem prefixQ : (13198 / 10000 : ℚ) ≤ (1 - 1 / 1996) * (primesK.map eulerQ).prod := by
  decide +kernel

/-- **The prefix bound** in `ℝ`, the form the partial-product argument consumes. -/
theorem prefix_boundP : (1.3198 : ℝ) ≤ (1 - 1 / 1996) * ∏ n ∈ bigPrimes, eulerLow n := by
  have hc : (((1 - 1 / 1996 : ℚ)) : ℝ) = 1 - 1 / 1996 := by norm_num
  rw [prod_bigPrimes_eq, ← hc, ← Rat.cast_mul]
  calc (1.3198 : ℝ) = ((13198 / 10000 : ℚ) : ℝ) := by norm_num
    _ ≤ _ := Rat.cast_le.mpr prefixQ

/-! ### The tail: `∑_{p ≥ 1000} 1/(p−1)² ≤ 1/1996` (copied from `sum_tail_inv_sq_le`) -/

/-- **The tail estimate.** For any finite set `U` of primes `≥ 1000`,
`∑_{p ∈ U} 1/(p−1)² ≤ 1/1996`: each such `p` is odd, so `p − 1 = 2·(p/2)` with `p/2 ≥ 500`
distinct, and `(1/4)·∑_{m≥500}1/m² ≤ (1/4)/499` (`sum_inv_sq_tail_le`, reused). -/
theorem sum_tail_inv_sq_le_K (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ 1000 ≤ p) :
    ∑ p ∈ U, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 1996 := by
  have hodd : ∀ p ∈ U, p % 2 = 1 := by
    intro p hp
    obtain ⟨hpp, hge⟩ := hU p hp
    have h2 : p ≠ 2 := by omega
    exact Nat.odd_iff.mp (hpp.odd_of_ne_two h2)
  have hrw : ∀ p ∈ U, 1 / ((p : ℝ) - 1) ^ 2 = (1 / 4) * (1 / ((p / 2 : ℕ) : ℝ) ^ 2) := by
    intro p hp
    have hp1 : p - 1 = 2 * (p / 2) := by have := hodd p hp; omega
    have hge : 1000 ≤ p := (hU p hp).2
    have hcast : ((p : ℝ) - 1) = 2 * ((p / 2 : ℕ) : ℝ) := by
      have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        have h1 : 1 ≤ p := by omega
        push_cast [Nat.cast_sub h1]; ring
      rw [← hc, hp1]; push_cast; ring
    rw [hcast]
    have hp2 : (0 : ℝ) < ((p / 2 : ℕ) : ℝ) := by
      have : 0 < p / 2 := by omega
      exact_mod_cast this
    field_simp
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun p : ℕ => p / 2) ↑U := by
    intro x hx y hy h
    have h1 := hodd x (Finset.mem_coe.mp hx)
    have h2 := hodd y (Finset.mem_coe.mp hy)
    simp only at h
    omega
  have himg : ∑ m ∈ U.image (fun p : ℕ => p / 2), 1 / ((m : ℝ)) ^ 2
      = ∑ p ∈ U, 1 / (((p / 2 : ℕ)) : ℝ) ^ 2 :=
    Finset.sum_image hinj
  rw [← himg]
  have hge500 : ∀ m ∈ U.image (fun p : ℕ => p / 2), 500 ≤ m := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have := (hU p hp).2
    omega
  have h := sum_inv_sq_tail_le 500 (by norm_num) (U.image (fun p : ℕ => p / 2)) hge500
  have h499 : (1 : ℝ) / (((500 : ℕ) : ℝ) - 1) = 1 / 499 := by norm_num
  rw [h499] at h
  linarith

/-! ### The partial-product bound and the deliverable (copied from `partial_prod_sing3_ge`) -/

/-- **Every partial Euler product over a finite set of primes containing all primes below `1000`
is `≥ 1.3198`**, for every odd `N`: the prefix `bigPrimes` is evaluated exactly
(`prefix_boundP`) and Weierstrass (`prod_one_sub_ge`) is applied only on the complement, where
the tail estimate gives `1/1996`. -/
theorem partial_prod_ge_P (N : ℕ) (hN : Odd N) (S : Finset Nat.Primes)
    (hS : bigPrimesSub ⊆ S) :
    (1.3198 : ℝ) ≤ ∏ p ∈ S, (1 + sing3Local (p : ℕ) N) := by
  classical
  set T : Finset ℕ := S.image (fun p : Nat.Primes => (p : ℕ)) with hTdef
  have himg : ∏ n ∈ T, (1 + sing3Local n N)
      = ∏ p ∈ S, (1 + sing3Local ((p : ℕ)) N) := by
    rw [hTdef]
    exact Finset.prod_image (fun _ _ _ _ h => Subtype.ext h)
  have hprodT : ∏ p ∈ S, (1 + sing3Local (p : ℕ) N) = ∏ n ∈ T, (1 + sing3Local n N) := himg.symm
  have hTprime : ∀ n ∈ T, n.Prime := by
    intro n hn
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
    exact p.2
  have hsub : bigPrimes ⊆ T := by
    intro n hn
    exact Finset.mem_image.mpr ⟨⟨n, prime_of_mem_bigPrimes n hn⟩,
      hS (Finset.mem_subtype.mpr hn), rfl⟩
  rw [hprodT, ← Finset.prod_sdiff hsub]
  -- the prefix
  have hbig : (∏ n ∈ bigPrimes, eulerLow n) ≤ ∏ n ∈ bigPrimes, (1 + sing3Local n N) := by
    refine Finset.prod_le_prod (fun n hn => eulerLow_nonneg n (prime_of_mem_bigPrimes n hn))
      (fun n hn => ?_)
    have hp : n.Prime := prime_of_mem_bigPrimes n hn
    rw [eulerLow]
    by_cases h2 : n = 2
    · rw [if_pos h2, h2, one_add_sing3Local_two N hN]
    · rw [if_neg h2]
      exact one_add_sing3Local_ge n N hp
  have hbig0 : (0 : ℝ) ≤ ∏ n ∈ bigPrimes, eulerLow n :=
    Finset.prod_nonneg (fun n hn => eulerLow_nonneg n (prime_of_mem_bigPrimes n hn))
  -- the tail
  have hge1000 : ∀ n ∈ T \ bigPrimes, n.Prime ∧ 1000 ≤ n := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    have hp : n.Prime := hTprime n hn.1
    refine ⟨hp, ?_⟩
    by_contra hlt
    exact hn.2 (mem_big_of_prime_lt n hp (by omega))
  have hfacnn : ∀ n ∈ T \ bigPrimes, (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) - 1) ^ 2 := by
    intro n hn
    obtain ⟨hp, hge⟩ := hge1000 n hn
    have h1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (pow_pos hpos 2)]
      nlinarith
    linarith
  have ha01 : ∀ n ∈ T \ bigPrimes, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
    intro n hn
    have := hfacnn n hn
    linarith
  have ha00 : ∀ n ∈ T \ bigPrimes, (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) ^ 2 := by
    intro n hn
    exact div_nonneg zero_le_one (sq_nonneg _)
  have hw : 1 - ∑ n ∈ T \ bigPrimes, 1 / ((n : ℝ) - 1) ^ 2
      ≤ ∏ n ∈ T \ bigPrimes, (1 - 1 / ((n : ℝ) - 1) ^ 2) :=
    prod_one_sub_ge (T \ bigPrimes) (fun n => 1 / ((n : ℝ) - 1) ^ 2) ha00 ha01
  have hstep : ∏ n ∈ T \ bigPrimes, (1 - 1 / ((n : ℝ) - 1) ^ 2)
      ≤ ∏ n ∈ T \ bigPrimes, (1 + sing3Local n N) :=
    Finset.prod_le_prod hfacnn (fun n hn => one_add_sing3Local_ge n N (hge1000 n hn).1)
  have htailsum : ∑ n ∈ T \ bigPrimes, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 1996 :=
    sum_tail_inv_sq_le_K (T \ bigPrimes) hge1000
  have htail : (1 : ℝ) - 1 / 1996 ≤ ∏ n ∈ T \ bigPrimes, (1 + sing3Local n N) := by
    linarith
  have htail0 : (0 : ℝ) ≤ ∏ n ∈ T \ bigPrimes, (1 + sing3Local n N) := by
    refine Finset.prod_nonneg (fun n hn => ?_)
    have h1 := hfacnn n hn
    have h2 := one_add_sing3Local_ge n N (hge1000 n hn).1
    linarith
  calc (1.3198 : ℝ) ≤ (1 - 1 / 1996) * ∏ n ∈ bigPrimes, eulerLow n := prefix_boundP
    _ ≤ (∏ n ∈ T \ bigPrimes, (1 + sing3Local n N)) * ∏ n ∈ bigPrimes,
          (1 + sing3Local n N) := mul_le_mul htail hbig hbig0 htail0

/-- **THE DELIVERABLE.** `𝔖₃(N) ≥ 1.3198` for every odd `N` — the peel-to-`997` route, whose
exact value is `2·∏_{3≤p<1000}(1−1/(p−1)²)·(1−1/1996) = 1.3198299…`. The true infimum is
`1.3203236…`; the `131/100` of `SingularSeries.sing3_ge_sharp` is improved by `0.0098`. -/
theorem sing3_ge_P (N : ℕ) (hN : Odd N) : (1.3198 : ℝ) ≤ sing3 N := by
  have hN1 : 1 ≤ N := by
    obtain ⟨k, rfl⟩ := hN
    omega
  exact ge_of_tendsto (sing3_hasProd N hN1)
    (Filter.eventually_atTop.mpr ⟨bigPrimesSub, fun S hS => partial_prod_ge_P N hN S hS⟩)

/-- **`sing3_ge_P` implies `SingularSeries.sing3_ge_sharp`** (`131/100 < 1.3198`). -/
theorem sing3_ge_sharp_of_P (N : ℕ) (hN : Odd N) : (131 : ℝ) / 100 ≤ sing3 N :=
  le_trans (by norm_num) (sing3_ge_P N hN)

end Principia.Common.TernaryGoldbach.SSP
