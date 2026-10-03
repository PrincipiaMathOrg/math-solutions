/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PrimeSumExact.CertsA
import Principia.Common.PrimeSumExact.CertsB

set_option autoImplicit false

/-!
# The exact sum of the primes of `(10883, 98999987]`

**`sum_primes_window1`**:
```
∑ r ∈ (Ioc 10883 98999987).filter Nat.Prime, r = 273803744799153 − 480503 = 273803744318650.
```
The window `[10884, 98999988)` is cut into 94 segments of width `2^20` from `10884` and a last
segment `[98577028, 98999988)` of width `422960`. Each segment's prime sum is one kernel
evaluation (`CertsA`, `CertsB`); `segSum_eq` / `allSeg_sum` (`PrimeSumExact/Sieve.lean`) turn them
into the sum of the primes, the sieving list being the primes up to `9949 = ⌊√98999987⌋`
(complete by `mem_primesTo9949`). The `5 705 800` primes involved are never listed.

Also: `card_primes_Ioc_10000_10883` (there are `94` primes in `(10000, 10883]`) and
`sum_primes_Ioc_10000_10883` (their sum is `980884`), by the same machinery with `K = 10`.
The value was re-derived independently by a numpy sieve before the certificate was built.
-/

namespace Principia.Common.PrimeSumExact

open Finset

/-- The sums of the primes of the 94 segments `[10884 + j·2^20, 10884 + (j+1)·2^20)`. -/
def window1Sums : List ℕ :=
  [41969259156, 116210427596, 186544369850, 255218746741, 322836345939, 388826182261,
    454771530473, 519677994127, 584575078603, 648563859586, 712973860590, 776340438066,
    838095786348, 902447459503, 964353548419, 1026465069858, 1090661147970, 1150919871070,
    1212270913183, 1273518327023, 1337805033799, 1395298682070, 1455181535457, 1520537801778,
    1578178784106, 1640552617025, 1702790015915, 1758837524979, 1825696797958, 1877673176387,
    1941889095776, 2002876172432, 2053879558812, 2119110533123, 2178604423475, 2240114986179,
    2303532394689, 2363945087582, 2417105323939, 2471849404568, 2533151154179, 2594549148900,
    2655966294743, 2716991998491, 2771933474707, 2820853065628, 2888722504888, 2953391923418,
    3005684898893, 3063251801301, 3120763896753, 3175336156913, 3235482053894, 3300586910895,
    3363470156786, 3410906706803, 3467731048912, 3534986337981, 3578449409286, 3646158416175,
    3709824604716, 3752110923648, 3820702469325, 3881263825370, 3939951634916, 3984910232105,
    4053749600350, 4103736608385, 4176422291988, 4215419126977, 4275451876273, 4341258427197,
    4390629108199, 4444983769626, 4500265380340, 4562962742855, 4620040150229, 4691133412032,
    4740971969277, 4788294636822, 4839331362444, 4908974368729, 4964003691989, 5021672263376,
    5075547014364, 5127290191281, 5196669771629, 5245248389318, 5295908957952, 5362882035316,
    5428965126267, 5469728438047, 5538849758807, 5592142000670]

theorem window1Sums_length : window1Sums.length = 94 := rfl

/-- The 94 segment certificates, chained. -/
theorem allSeg_window1 : AllSeg 20 1048576 primesTo9949 10884 window1Sums :=
  allSeg_cons _ _ _ _ _ _ seg_window1_00 (allSeg_cons _ _ _ _ _ _ seg_window1_01 (allSeg_cons _ _
    _ _ _ _ seg_window1_02 (allSeg_cons _ _ _ _ _ _ seg_window1_03 (allSeg_cons _ _ _ _ _ _
    seg_window1_04 (allSeg_cons _ _ _ _ _ _ seg_window1_05 (allSeg_cons _ _ _ _ _ _ seg_window1_06
    (allSeg_cons _ _ _ _ _ _ seg_window1_07 (allSeg_cons _ _ _ _ _ _ seg_window1_08 (allSeg_cons _
    _ _ _ _ _ seg_window1_09 (allSeg_cons _ _ _ _ _ _ seg_window1_10 (allSeg_cons _ _ _ _ _ _
    seg_window1_11 (allSeg_cons _ _ _ _ _ _ seg_window1_12 (allSeg_cons _ _ _ _ _ _ seg_window1_13
    (allSeg_cons _ _ _ _ _ _ seg_window1_14 (allSeg_cons _ _ _ _ _ _ seg_window1_15 (allSeg_cons _
    _ _ _ _ _ seg_window1_16 (allSeg_cons _ _ _ _ _ _ seg_window1_17 (allSeg_cons _ _ _ _ _ _
    seg_window1_18 (allSeg_cons _ _ _ _ _ _ seg_window1_19 (allSeg_cons _ _ _ _ _ _ seg_window1_20
    (allSeg_cons _ _ _ _ _ _ seg_window1_21 (allSeg_cons _ _ _ _ _ _ seg_window1_22 (allSeg_cons _
    _ _ _ _ _ seg_window1_23 (allSeg_cons _ _ _ _ _ _ seg_window1_24 (allSeg_cons _ _ _ _ _ _
    seg_window1_25 (allSeg_cons _ _ _ _ _ _ seg_window1_26 (allSeg_cons _ _ _ _ _ _ seg_window1_27
    (allSeg_cons _ _ _ _ _ _ seg_window1_28 (allSeg_cons _ _ _ _ _ _ seg_window1_29 (allSeg_cons _
    _ _ _ _ _ seg_window1_30 (allSeg_cons _ _ _ _ _ _ seg_window1_31 (allSeg_cons _ _ _ _ _ _
    seg_window1_32 (allSeg_cons _ _ _ _ _ _ seg_window1_33 (allSeg_cons _ _ _ _ _ _ seg_window1_34
    (allSeg_cons _ _ _ _ _ _ seg_window1_35 (allSeg_cons _ _ _ _ _ _ seg_window1_36 (allSeg_cons _
    _ _ _ _ _ seg_window1_37 (allSeg_cons _ _ _ _ _ _ seg_window1_38 (allSeg_cons _ _ _ _ _ _
    seg_window1_39 (allSeg_cons _ _ _ _ _ _ seg_window1_40 (allSeg_cons _ _ _ _ _ _ seg_window1_41
    (allSeg_cons _ _ _ _ _ _ seg_window1_42 (allSeg_cons _ _ _ _ _ _ seg_window1_43 (allSeg_cons _
    _ _ _ _ _ seg_window1_44 (allSeg_cons _ _ _ _ _ _ seg_window1_45 (allSeg_cons _ _ _ _ _ _
    seg_window1_46 (allSeg_cons _ _ _ _ _ _ seg_window1_47 (allSeg_cons _ _ _ _ _ _ seg_window1_48
    (allSeg_cons _ _ _ _ _ _ seg_window1_49 (allSeg_cons _ _ _ _ _ _ seg_window1_50 (allSeg_cons _
    _ _ _ _ _ seg_window1_51 (allSeg_cons _ _ _ _ _ _ seg_window1_52 (allSeg_cons _ _ _ _ _ _
    seg_window1_53 (allSeg_cons _ _ _ _ _ _ seg_window1_54 (allSeg_cons _ _ _ _ _ _ seg_window1_55
    (allSeg_cons _ _ _ _ _ _ seg_window1_56 (allSeg_cons _ _ _ _ _ _ seg_window1_57 (allSeg_cons _
    _ _ _ _ _ seg_window1_58 (allSeg_cons _ _ _ _ _ _ seg_window1_59 (allSeg_cons _ _ _ _ _ _
    seg_window1_60 (allSeg_cons _ _ _ _ _ _ seg_window1_61 (allSeg_cons _ _ _ _ _ _ seg_window1_62
    (allSeg_cons _ _ _ _ _ _ seg_window1_63 (allSeg_cons _ _ _ _ _ _ seg_window1_64 (allSeg_cons _
    _ _ _ _ _ seg_window1_65 (allSeg_cons _ _ _ _ _ _ seg_window1_66 (allSeg_cons _ _ _ _ _ _
    seg_window1_67 (allSeg_cons _ _ _ _ _ _ seg_window1_68 (allSeg_cons _ _ _ _ _ _ seg_window1_69
    (allSeg_cons _ _ _ _ _ _ seg_window1_70 (allSeg_cons _ _ _ _ _ _ seg_window1_71 (allSeg_cons _
    _ _ _ _ _ seg_window1_72 (allSeg_cons _ _ _ _ _ _ seg_window1_73 (allSeg_cons _ _ _ _ _ _
    seg_window1_74 (allSeg_cons _ _ _ _ _ _ seg_window1_75 (allSeg_cons _ _ _ _ _ _ seg_window1_76
    (allSeg_cons _ _ _ _ _ _ seg_window1_77 (allSeg_cons _ _ _ _ _ _ seg_window1_78 (allSeg_cons _
    _ _ _ _ _ seg_window1_79 (allSeg_cons _ _ _ _ _ _ seg_window1_80 (allSeg_cons _ _ _ _ _ _
    seg_window1_81 (allSeg_cons _ _ _ _ _ _ seg_window1_82 (allSeg_cons _ _ _ _ _ _ seg_window1_83
    (allSeg_cons _ _ _ _ _ _ seg_window1_84 (allSeg_cons _ _ _ _ _ _ seg_window1_85 (allSeg_cons _
    _ _ _ _ _ seg_window1_86 (allSeg_cons _ _ _ _ _ _ seg_window1_87 (allSeg_cons _ _ _ _ _ _
    seg_window1_88 (allSeg_cons _ _ _ _ _ _ seg_window1_89 (allSeg_cons _ _ _ _ _ _ seg_window1_90
    (allSeg_cons _ _ _ _ _ _ seg_window1_91 (allSeg_cons _ _ _ _ _ _ seg_window1_92 (allSeg_cons _
    _ _ _ _ _ seg_window1_93 (allSeg_nil _ _ _
    _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Every prime `q` with `q * q < 98999988` is a sieving prime. -/
theorem mem_primesTo9949_of_sq_lt (q : ℕ) (hq : q.Prime) (hqq : q * q < 98999988) :
    q ∈ primesTo9949 := by
  apply mem_primesTo9949 q hq
  by_contra h
  have : 9950 * 9950 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem sieving_bounds (lo : ℕ) (hlo : 9950 ≤ lo) : ∀ p ∈ primesTo9949, 2 ≤ p ∧ p < lo :=
  fun p hp => by have := primesTo9949_mem p hp; omega

/-- Splitting the prime sum over `Ico a c` at `b`. Stated with VARIABLE endpoints on purpose: in
a goal holding several prime sums over large literal intervals, `rw`/unification that compares
two different sums (or two `0`s from different instance paths, as `sum_filter` produces) falls back
to unfolding `Finset.sum` and evaluating ~10^8 terms (measured: > 3 GB, or "maximum recursion
depth"). With free endpoints nothing can be evaluated, and the instances below line up
syntactically with the literal statements. -/
theorem sum_filter_prime_split (a b c A B : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (hA : ∑ m ∈ Ico a b, (if m.Prime then m else 0) = A)
    (hB : ∑ m ∈ Ico b c, (if m.Prime then m else 0) = B) :
    ∑ r ∈ (Ico a c).filter Nat.Prime, r = A + B := by
  rw [sum_filter, ← sum_Ico_consecutive _ hab hbc]
  exact congrArg₂ (· + ·) hA hB

/-- **The exact sum of the primes of `(10883, 98999987]`.** -/
theorem sum_primes_window1 :
    ∑ r ∈ (Finset.Ioc 10883 98999987).filter Nat.Prime, r = 273803744799153 - 480503 := by
  have hA := allSeg_sum 20 1048576 primesTo9949 (by decide) (by decide) window1Sums 10884
    allSeg_window1 (by decide) (sieving_bounds 10884 (by decide))
    (fun q hq hqq => mem_primesTo9949_of_sq_lt q hq (by rw [window1Sums_length] at hqq; omega))
  have hA' : ∑ m ∈ Ico 10884 98577028, (if m.Prime then m else 0) = window1Sums.sum := by
    have e : 10884 + window1Sums.length * 1048576 = 98577028 := by
      rw [window1Sums_length]
    rw [e] at hA
    exact hA
  have hB := segSum_eq 20 422960 98577028 primesTo9949 (by decide) (by decide) (by decide)
    (sieving_bounds 98577028 (by decide))
    (fun q hq hqq => mem_primesTo9949_of_sq_lt q hq (by omega))
  have hB' : ∑ m ∈ Ico 98577028 98999988, (if m.Prime then m else 0) = 2251381631874 := by
    have e : 98577028 + 422960 = 98999988 := rfl
    rw [e, seg_window1_last] at hB
    exact hB.symm
  have hIoc : Ioc 10883 98999987 = Ico 10884 98999988 := by
    ext m
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hIoc]
  exact (sum_filter_prime_split 10884 98577028 98999988 _ _ (by decide) (by decide) hA' hB').trans
    (by decide +kernel)

theorem segCount_window0 : segCount 10 883 10001 primesTo9949 = 94 := by
  decide +kernel

theorem segSum_window0 : segSum 10 883 10001 primesTo9949 = 980884 := by
  decide +kernel

theorem Ioc_10000_10883 : Ioc 10000 10883 = Ico 10001 (10001 + 883) := by
  ext m
  simp only [mem_Ioc, mem_Ico]
  omega

/-- **There are `94` primes in `(10000, 10883]`.** -/
theorem card_primes_Ioc_10000_10883 : ((Finset.Ioc 10000 10883).filter Nat.Prime).card = 94 := by
  rw [Ioc_10000_10883, ← segCount_eq 10 883 10001 primesTo9949 (by decide) (by decide)
    (by decide) (sieving_bounds 10001 (by decide))
    (fun q hq hqq => mem_primesTo9949_of_sq_lt q hq (by omega)), segCount_window0]

/-- **The `94` primes of `(10000, 10883]` sum to `980884`.** -/
theorem sum_primes_Ioc_10000_10883 :
    ∑ r ∈ (Finset.Ioc 10000 10883).filter Nat.Prime, r = 980884 := by
  rw [Ioc_10000_10883, sum_filter, ← segSum_eq 10 883 10001 primesTo9949 (by decide)
    (by decide) (by decide) (sieving_bounds 10001 (by decide))
    (fun q hq hqq => mem_primesTo9949_of_sq_lt q hq (by omega)), segSum_window0]

end Principia.Common.PrimeSumExact
