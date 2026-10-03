/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# A kernel-checkable segmented sieve that sums the primes of an interval

For a segment `[lo, lo + W)` and a list `ps` of sieving primes, `segSum K W lo ps` computes, with
nothing but the natural-number operations the Lean kernel evaluates natively (GMP `+ - * / %`,
`&&& ||| ^^^ <<< >>>`, `Nat.ble`, `Nat.beq`, `^`), the sum of the primes of the segment:

* **the sieve** (`sieveBits`) holds the segment in ONE natural number, bit `i` standing for
  `lo + i`; for each `p ∈ ps` the mask of multiples of `p` (`mulMask`, built by repeated doubling
  `x ↦ x ||| x <<< len` from the first multiple) is cleared with `s ^^^ (s &&& mask)`;
* **the sum of the set bits** (`swarGo`) is a weighted popcount by field halving ("SWAR"): at level
  `k` the number `c` holds, in fields of width `2^k`, the number of set bits of each block of `2^k`
  positions, and `s` the sum of their positions inside the block; one level costs a constant number
  of big-number operations (`mskLo` is the mask of the low halves of the width-`2^(k+1)` fields).

So a segment costs `O(|ps| log W + log W)` kernel steps instead of one step per prime.

`segSum_eq` proves, for `W ≤ 2^K ≤ 2^64`, `2 ≤ lo`, every `p ∈ ps` satisfying `2 ≤ p < lo`, and
every prime `q` with `q * q < lo + W` lying in `ps`:
```
segSum K W lo ps = ∑ m ∈ (Ico lo (lo + W)).filter Nat.Prime, m,
```
and `segCount_eq` the same for the number of primes. `allSeg_sum` chains consecutive segments.
The numerical value of `segSum` for concrete arguments is one `decide +kernel`
(see `PrimeSumExact/SmallPrimes.lean` and `PrimeSumExact/Window.lean`).
-/

namespace Principia.Common.PrimeSumExact

open Finset

/-! ## 1. Periodic masks by doubling -/

/-- Repeat the pattern `x` of length `len` by doubling (`x ||| x <<< len`, `len + len`) until the
length reaches `W`, or the fuel `f` runs out. -/
def dblPat (W f : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun x _ => x)
    (fun _ ih x len => bif Nat.ble W len then x else ih (x ||| (x <<< len)) (len + len)) f

theorem dblPat_zero (W x len : ℕ) : dblPat W 0 x len = x := rfl

theorem dblPat_succ (W f x len : ℕ) :
    dblPat W (f + 1) x len =
      bif Nat.ble W len then x else dblPat W f (x ||| (x <<< len)) (len + len) := rfl

/-- `PatSpec r p len x`: the set bits of `x` are exactly the `i ∈ [r, r + len)` with
`p ∣ i − r`. -/
def PatSpec (r p len x : ℕ) : Prop :=
  ∀ i, x.testBit i = true ↔ (r ≤ i ∧ i < r + len ∧ p ∣ i - r)

theorem patSpec_init (r p : ℕ) (hp : 0 < p) : PatSpec r p p (1 <<< r) := by
  intro i
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_iff]
  constructor
  · rintro rfl
    exact ⟨le_rfl, by omega, by simp⟩
  · rintro ⟨h1, h2, h3⟩
    have h0 : i - r = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega

theorem patSpec_step {r p len x : ℕ} (h : PatSpec r p len x) (hd : p ∣ len) :
    PatSpec r p (len + len) (x ||| (x <<< len)) := by
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, h i, h (i - len)]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩)
    · exact ⟨h1, by omega, h3⟩
    · refine ⟨by omega, by omega, ?_⟩
      have e : i - r = (i - len - r) + len := by omega
      rw [e]
      exact Nat.dvd_add h3 hd
  · rintro ⟨h1, h2, h3⟩
    by_cases hi : i < r + len
    · exact Or.inl ⟨h1, hi, h3⟩
    · refine Or.inr ⟨by omega, by omega, by omega, ?_⟩
      have e : i - r = (i - len - r) + len := by omega
      rw [e] at h3
      have h4 := Nat.dvd_sub h3 hd
      rwa [Nat.add_sub_cancel] at h4

theorem patSpec_dblPat (W r p : ℕ) :
    ∀ (f x len : ℕ), PatSpec r p len x → p ∣ len → 0 < len →
      ∃ L, min W (len * 2 ^ f) ≤ L ∧ PatSpec r p L (dblPat W f x len) := by
  intro f
  induction f with
  | zero =>
    intro x len h _ _
    exact ⟨len, by simp, h⟩
  | succ f ih =>
    intro x len h hd hl
    rw [dblPat_succ]
    cases hb : Nat.ble W len
    · obtain ⟨L, hL, hs⟩ := ih _ _ (patSpec_step h hd) (Nat.dvd_add hd hd) (by omega)
      refine ⟨L, ?_, hs⟩
      have e : (len + len) * 2 ^ f = len * 2 ^ (f + 1) := by ring
      rw [e] at hL
      exact hL
    · exact ⟨len, le_trans (min_le_left _ _) (Nat.le_of_ble_eq_true hb), h⟩

/-- The position, relative to `lo`, of the first multiple of `p` at or above `lo`. -/
def offs (lo p : ℕ) : ℕ := (p - lo % p) % p

theorem offs_dvd (lo p : ℕ) (hp : 0 < p) : p ∣ lo + offs lo p := by
  unfold offs
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_mod]
  have hs : lo % p < p := Nat.mod_lt _ hp
  rcases Nat.eq_zero_or_pos (lo % p) with h0 | hpos
  · simp [h0]
  · rw [Nat.mod_eq_of_lt (show p - lo % p < p by omega),
      show lo % p + (p - lo % p) = p by omega, Nat.mod_self]

/-- `p ∣ lo + i` exactly when `i` is a multiple of `p` beyond the offset. -/
theorem offs_spec (lo p i : ℕ) (hp : 0 < p) :
    (offs lo p ≤ i ∧ p ∣ i - offs lo p) ↔ p ∣ lo + i := by
  have hd := offs_dvd lo p hp
  have hlt : offs lo p < p := Nat.mod_lt _ hp
  constructor
  · rintro ⟨h1, h2⟩
    have e : lo + i = (lo + offs lo p) + (i - offs lo p) := by omega
    rw [e]
    exact Nat.dvd_add hd h2
  · intro h
    have hri : offs lo p ≤ i := by
      by_contra hcon
      have h3 : p ∣ (lo + offs lo p) - (lo + i) := Nat.dvd_sub hd h
      have e : (lo + offs lo p) - (lo + i) = offs lo p - i := by omega
      rw [e] at h3
      have := Nat.le_of_dvd (by omega) h3
      omega
    refine ⟨hri, ?_⟩
    have h3 := Nat.dvd_sub h hd
    have e : lo + i - (lo + offs lo p) = i - offs lo p := by omega
    rwa [e] at h3

/-- The multiples of `p` in the segment `[lo, lo + W)`, as a bit mask (bit `i` ↔ `lo + i`). -/
def mulMask (W lo p : ℕ) : ℕ := dblPat W 64 (1 <<< offs lo p) p

theorem mulMask_testBit (W lo p i : ℕ) (hp : 0 < p) (hW : W ≤ 2 ^ 64) (hi : i < W) :
    (mulMask W lo p).testBit i = true ↔ p ∣ lo + i := by
  obtain ⟨L, hL, hs⟩ := patSpec_dblPat W (offs lo p) p 64 (1 <<< offs lo p) p
    (patSpec_init _ p hp) (dvd_refl p) hp
  have hWL : W ≤ L :=
    le_trans (le_min le_rfl (le_trans hW (Nat.le_mul_of_pos_left _ hp))) hL
  unfold mulMask
  rw [hs i, ← offs_spec lo p i hp]
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, by omega, h3⟩

/-! ## 2. The sieve -/

/-- Clear the multiples of `p` from the segment bits `s`. -/
def clearMult (W lo s p : ℕ) : ℕ := s ^^^ (s &&& mulMask W lo p)

/-- The segment `[lo, lo + W)` with the multiples of every `p ∈ ps` cleared. -/
def sieveBits (W lo : ℕ) (ps : List ℕ) : ℕ := ps.foldl (clearMult W lo) (2 ^ W - 1)

theorem testBit_clearMult (W lo s p i : ℕ) :
    (clearMult W lo s p).testBit i = (s.testBit i && !(mulMask W lo p).testBit i) := by
  unfold clearMult
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases s.testBit i <;> cases (mulMask W lo p).testBit i <;> rfl

theorem testBit_foldl (W lo i : ℕ) : ∀ (ps : List ℕ) (s : ℕ),
    (ps.foldl (clearMult W lo) s).testBit i = true ↔
      (s.testBit i = true ∧ ∀ p ∈ ps, (mulMask W lo p).testBit i = false)
  | [], s => by simp
  | p :: ps, s => by
    rw [List.foldl_cons, testBit_foldl W lo i ps, testBit_clearMult]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.mem_cons, forall_eq_or_imp]
    tauto

theorem testBit_sieveBits (W lo : ℕ) (ps : List ℕ) (hW : W ≤ 2 ^ 64) (hps : ∀ p ∈ ps, 0 < p)
    (i : ℕ) : (sieveBits W lo ps).testBit i = true ↔ (i < W ∧ ∀ p ∈ ps, ¬ p ∣ lo + i) := by
  unfold sieveBits
  rw [testBit_foldl, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun p hp hdvd => ?_⟩
    have h1 := (mulMask_testBit W lo p i (hps p hp) hW hi).mpr hdvd
    rw [h p hp] at h1
    exact Bool.false_ne_true h1
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun p hp => ?_⟩
    by_contra hne
    have h1 : (mulMask W lo p).testBit i = true := by simpa using hne
    exact h p hp ((mulMask_testBit W lo p i (hps p hp) hW hi).mp h1)

/-- **The sieve is exact**: bit `i` survives iff `i < W` and `lo + i` is prime, provided the
sieving list consists of numbers in `[2, lo)` and contains every prime `q` with
`q * q < lo + W`. -/
theorem testBit_sieveBits_prime (W lo : ℕ) (ps : List ℕ) (hW : W ≤ 2 ^ 64) (hlo : 2 ≤ lo)
    (hps : ∀ p ∈ ps, 2 ≤ p ∧ p < lo) (hcomp : ∀ q, q.Prime → q * q < lo + W → q ∈ ps)
    (i : ℕ) : (sieveBits W lo ps).testBit i = true ↔ (i < W ∧ (lo + i).Prime) := by
  rw [testBit_sieveBits W lo ps hW (fun p hp => by have := hps p hp; omega)]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    by_contra hnp
    have hq := Nat.minFac_sq_le_self (show 0 < lo + i by omega) hnp
    have hqp : (lo + i).minFac.Prime := Nat.minFac_prime (by omega)
    have hsq : (lo + i).minFac * (lo + i).minFac ≤ lo + i := by rw [← pow_two]; exact hq
    exact h _ (hcomp _ hqp (lt_of_le_of_lt hsq (by omega))) (Nat.minFac_dvd _)
  · rintro ⟨hi, hpr⟩
    refine ⟨hi, fun p hp hdvd => ?_⟩
    have := hps p hp
    rcases hpr.eq_one_or_self_of_dvd p hdvd with h1 | h1 <;> omega

theorem sieveBits_lt (W lo : ℕ) (ps : List ℕ) (hW : W ≤ 2 ^ 64) (hps : ∀ p ∈ ps, 0 < p) :
    sieveBits W lo ps < 2 ^ W := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_contra hne
  have h1 : (sieveBits W lo ps).testBit i = true := by simpa using hne
  have := ((testBit_sieveBits W lo ps hW hps i).mp h1).1
  omega

/-! ## 3. Packed fields -/

/-- `pack w f n = ∑_{j<n} f j · 2^(w j)`: the number whose width-`w` fields are `f 0, …, f (n−1)`
(when every `f j < 2^w`). -/
def pack (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, f j * 2 ^ (w * j)

theorem pack_zero (w : ℕ) (f : ℕ → ℕ) : pack w f 0 = 0 := by
  simp [pack]

theorem pack_succ (w : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    pack w f (n + 1) = pack w f n + f n * 2 ^ (w * n) := by
  simp [pack, sum_range_succ]

theorem pack_one (w : ℕ) (f : ℕ → ℕ) : pack w f 1 = f 0 := by
  simp [pack]

theorem pack_add (w : ℕ) (f g : ℕ → ℕ) (n : ℕ) :
    pack w f n + pack w g n = pack w (fun j => f j + g j) n := by
  simp only [pack, ← sum_add_distrib, add_mul]

theorem pack_mul (w c : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    c * pack w f n = pack w (fun j => c * f j) n := by
  simp only [pack, mul_sum, mul_assoc]

theorem pack_lt (w : ℕ) (f : ℕ → ℕ) :
    ∀ n, (∀ j < n, f j < 2 ^ w) → pack w f n < 2 ^ (w * n)
  | 0, _ => by simp [pack_zero]
  | n + 1, h => by
    rw [pack_succ]
    have h1 := pack_lt w f n (fun j hj => h j (by omega))
    have h2 : f n + 1 ≤ 2 ^ w := h n (by omega)
    calc pack w f n + f n * 2 ^ (w * n) < 2 ^ (w * n) + f n * 2 ^ (w * n) :=
          Nat.add_lt_add_right h1 _
      _ = (f n + 1) * 2 ^ (w * n) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (w * (n + 1)) := by ring

/-- Pairing adjacent width-`w` fields into width-`2w` fields. -/
theorem pack_split (w : ℕ) (f : ℕ → ℕ) :
    ∀ n, pack w f (2 * n) = pack (2 * w) (fun j => f (2 * j) + 2 ^ w * f (2 * j + 1)) n
  | 0 => by simp [pack_zero]
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [pack_succ, pack_split w f n]
    ring

theorem land_split (m a b c d : ℕ) (hb : b < 2 ^ m) (hd : d < 2 ^ m) :
    (2 ^ m * a + b) &&& (2 ^ m * c + d) = 2 ^ m * (a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add a hb, Nat.testBit_two_pow_mul_add c hd,
    Nat.testBit_two_pow_mul_add (a &&& c) (Nat.and_lt_two_pow b hd)]
  split_ifs <;> simp [Nat.testBit_and]

/-- `&&&` of two packed numbers acts field by field. -/
theorem pack_land (w : ℕ) (a b : ℕ → ℕ) :
    ∀ n, (∀ j < n, a j < 2 ^ w) → (∀ j < n, b j < 2 ^ w) →
      pack w a n &&& pack w b n = pack w (fun j => a j &&& b j) n
  | 0, _, _ => by simp [pack_zero]
  | n + 1, ha, hb => by
    have iha := pack_land w a b n (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    have hla := pack_lt w a n (fun j hj => ha j (by omega))
    have hlb := pack_lt w b n (fun j hj => hb j (by omega))
    rw [pack_succ, pack_succ, pack_succ,
      show pack w a n + a n * 2 ^ (w * n) = 2 ^ (w * n) * a n + pack w a n by ring,
      show pack w b n + b n * 2 ^ (w * n) = 2 ^ (w * n) * b n + pack w b n by ring,
      land_split _ _ _ _ _ hla hlb, iha]
    ring

theorem pack_shiftLeft (w v : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    pack w f n <<< v = pack w (fun j => 2 ^ v * f j) n := by
  rw [Nat.shiftLeft_eq, mul_comm, pack_mul]

theorem pack_shiftRight (w v : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    pack w (fun j => 2 ^ v * f j) n >>> v = pack w f n := by
  rw [Nat.shiftRight_eq_div_pow, ← pack_mul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos v)]

theorem pack_congr (w n : ℕ) (f g : ℕ → ℕ) (h : ∀ j < n, f j = g j) :
    pack w f n = pack w g n := by
  unfold pack
  exact sum_congr rfl (fun j hj => by rw [h j (mem_range.mp hj)])

theorem two_fields_lt (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    a + 2 ^ w * b < 2 ^ (2 * w) := by
  have e : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  rw [e]
  calc a + 2 ^ w * b < 2 ^ w + 2 ^ w * b := Nat.add_lt_add_right ha _
    _ = 2 ^ w * (b + 1) := by ring
    _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ hb

/-- The low half of every width-`2w` field. -/
theorem lowFields (w n : ℕ) (f : ℕ → ℕ) (hf : ∀ j < 2 * n, f j < 2 ^ w) :
    pack w f (2 * n) &&& pack (2 * w) (fun _ => 2 ^ w - 1) n =
      pack (2 * w) (fun j => f (2 * j)) n := by
  rw [pack_split, pack_land]
  · apply pack_congr
    intro j hj
    show (f (2 * j) + 2 ^ w * f (2 * j + 1)) &&& (2 ^ w - 1) = f (2 * j)
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hf (2 * j) (by omega))
  · intro j hj
    exact two_fields_lt w _ _ (hf _ (by omega)) (hf _ (by omega))
  · intro j _
    have : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.two_pow_pos w
    omega

/-- The high half of every width-`2w` field, moved down. -/
theorem highFields (w n : ℕ) (f : ℕ → ℕ) (hf : ∀ j < 2 * n, f j < 2 ^ w) :
    (pack w f (2 * n) &&& (pack (2 * w) (fun _ => 2 ^ w - 1) n <<< w)) >>> w =
      pack (2 * w) (fun j => f (2 * j + 1)) n := by
  have hw : 0 < 2 ^ w := Nat.two_pow_pos w
  have key : pack w f (2 * n) &&& (pack (2 * w) (fun _ => 2 ^ w - 1) n <<< w) =
      pack (2 * w) (fun j => 2 ^ w * f (2 * j + 1)) n := by
    rw [pack_shiftLeft, pack_split, pack_land]
    · apply pack_congr
      intro j hj
      show (f (2 * j) + 2 ^ w * f (2 * j + 1)) &&& 2 ^ w * (2 ^ w - 1) = 2 ^ w * f (2 * j + 1)
      have h := land_split w (f (2 * j + 1)) (f (2 * j)) (2 ^ w - 1) 0 (hf _ (by omega)) hw
      simp only [Nat.add_zero, Nat.and_zero, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (hf (2 * j + 1) (by omega))] at h
      rw [add_comm]
      exact h
    · intro j hj
      exact two_fields_lt w _ _ (hf _ (by omega)) (hf _ (by omega))
    · intro j _
      have e : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
      rw [e]
      exact (Nat.mul_lt_mul_left hw).mpr (by omega)
  rw [key, pack_shiftRight]

/-! ## 4. The weighted popcount -/

/-- The mask of the low halves of the width-`2^(k+1)` fields of a `2^K`-bit number. -/
def mskLo (K k : ℕ) : ℕ := (2 ^ 2 ^ k - 1) * ((2 ^ 2 ^ K - 1) / (2 ^ (2 * 2 ^ k) - 1))

theorem mskLo_eq (K k : ℕ) (hk : k < K) :
    mskLo K k = pack (2 * 2 ^ k) (fun _ => 2 ^ 2 ^ k - 1) (2 ^ (K - k - 1)) := by
  have hB : 2 ≤ 2 ^ (2 * 2 ^ k) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * 2 ^ k) :=
        Nat.pow_le_pow_right (by norm_num) (by have := Nat.two_pow_pos k; omega)
  have hK : 2 ^ 2 ^ K = (2 ^ (2 * 2 ^ k)) ^ 2 ^ (K - k - 1) := by
    rw [← pow_mul]
    congr 1
    rw [show 2 * 2 ^ k * 2 ^ (K - k - 1) = 2 ^ (1 + k + (K - k - 1)) by ring]
    congr 1
    omega
  unfold mskLo pack
  rw [hK, ← Nat.geomSum_eq hB, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [← pow_mul]

/-- The popcount iteration: `m` levels from level `k`, on the block counts `c` and the block
position sums `s` (fields of width `2^k`). -/
def swarGo (K m : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ c s => (c, s))
    (fun _ ih k c s =>
      ih (k + 1) ((c &&& mskLo K k) + ((c &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k))
        ((s &&& mskLo K k) + ((s &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k) +
          (((c &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k) <<< k))) m

theorem swarGo_zero (K k c s : ℕ) : swarGo K 0 k c s = (c, s) := rfl

theorem swarGo_succ (K m k c s : ℕ) :
    swarGo K (m + 1) k c s =
      swarGo K m (k + 1) ((c &&& mskLo K k) + ((c &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k))
        ((s &&& mskLo K k) + ((s &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k) +
          (((c &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k) <<< k)) := rfl

/-- Bit `i` of `x`, as `0` or `1`. -/
def bitv (x i : ℕ) : ℕ := x / 2 ^ i % 2

/-- The number of set bits of `x` in the `j`-th block of `2^k` positions. -/
def blkCnt (x k j : ℕ) : ℕ := ∑ t ∈ range (2 ^ k), bitv x (2 ^ k * j + t)

/-- The sum of the in-block positions of the set bits of `x` in the `j`-th block of `2^k`. -/
def blkPos (x k j : ℕ) : ℕ := ∑ t ∈ range (2 ^ k), t * bitv x (2 ^ k * j + t)

theorem bitv_le (x i : ℕ) : bitv x i ≤ 1 := by
  unfold bitv
  omega

theorem bitv_eq (x i : ℕ) : bitv x i = if x.testBit i then 1 else 0 := by
  unfold bitv
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem blkCnt_succ (x k j : ℕ) :
    blkCnt x (k + 1) j = blkCnt x k (2 * j) + blkCnt x k (2 * j + 1) := by
  unfold blkCnt
  rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by ring, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro t _
    rw [show (2 ^ k + 2 ^ k) * j + t = 2 ^ k * (2 * j) + t by ring]
  · apply sum_congr rfl
    intro t _
    rw [show (2 ^ k + 2 ^ k) * j + (2 ^ k + t) = 2 ^ k * (2 * j + 1) + t by ring]

theorem blkPos_succ (x k j : ℕ) :
    blkPos x (k + 1) j =
      blkPos x k (2 * j) + blkPos x k (2 * j + 1) + 2 ^ k * blkCnt x k (2 * j + 1) := by
  have e1 : ∑ t ∈ range (2 ^ k), t * bitv x ((2 ^ k + 2 ^ k) * j + t) = blkPos x k (2 * j) := by
    unfold blkPos
    apply sum_congr rfl
    intro t _
    rw [show (2 ^ k + 2 ^ k) * j + t = 2 ^ k * (2 * j) + t by ring]
  have e2 : ∑ t ∈ range (2 ^ k), (2 ^ k + t) * bitv x ((2 ^ k + 2 ^ k) * j + (2 ^ k + t)) =
      blkPos x k (2 * j + 1) + 2 ^ k * blkCnt x k (2 * j + 1) := by
    unfold blkPos blkCnt
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro t _
    rw [show (2 ^ k + 2 ^ k) * j + (2 ^ k + t) = 2 ^ k * (2 * j + 1) + t by ring]
    ring
  rw [blkPos]
  rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by ring, sum_range_add, e1, e2]
  ring

theorem two_mul_le_two_pow : ∀ k : ℕ, 2 * k ≤ 2 ^ k
  | 0 => by norm_num
  | k + 1 => by
    have ih := two_mul_le_two_pow k
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      norm_num
    · have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega

theorem blkCnt_lt (x k j : ℕ) : blkCnt x k j < 2 ^ 2 ^ k := by
  have h : blkCnt x k j ≤ 2 ^ k := by
    unfold blkCnt
    calc ∑ t ∈ range (2 ^ k), bitv x (2 ^ k * j + t) ≤ ∑ _t ∈ range (2 ^ k), 1 :=
          sum_le_sum (fun t _ => bitv_le _ _)
      _ = 2 ^ k := by simp
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

theorem blkPos_lt (x k j : ℕ) : blkPos x k j < 2 ^ 2 ^ k := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have h : blkPos x k j ≤ 2 ^ k * (2 ^ k - 1) := by
    unfold blkPos
    calc ∑ t ∈ range (2 ^ k), t * bitv x (2 ^ k * j + t) ≤ ∑ _t ∈ range (2 ^ k), (2 ^ k - 1) :=
          sum_le_sum (fun t ht => by
            have h1 := mem_range.mp ht
            have h2 := bitv_le x (2 ^ k * j + t)
            calc t * bitv x (2 ^ k * j + t) ≤ t * 1 := Nat.mul_le_mul_left _ h2
              _ ≤ 2 ^ k - 1 := by omega)
      _ = 2 ^ k * (2 ^ k - 1) := by simp
  have h2 : 2 ^ k * (2 ^ k - 1) < 2 ^ k * 2 ^ k := (Nat.mul_lt_mul_left hk).mpr (by omega)
  have h3 : 2 ^ k * 2 ^ k ≤ 2 ^ 2 ^ k := by
    rw [← pow_add, ← two_mul]
    exact Nat.pow_le_pow_right (by norm_num) (two_mul_le_two_pow k)
  omega

/-- One level of the popcount: counts and position sums of the blocks of `2^(k+1)`. -/
theorem swar_level (x K k : ℕ) (hk : k < K) :
    ((pack (2 ^ k) (blkCnt x k) (2 ^ (K - k)) &&& mskLo K k) +
        ((pack (2 ^ k) (blkCnt x k) (2 ^ (K - k)) &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k) =
      pack (2 ^ (k + 1)) (blkCnt x (k + 1)) (2 ^ (K - (k + 1)))) ∧
    ((pack (2 ^ k) (blkPos x k) (2 ^ (K - k)) &&& mskLo K k) +
        ((pack (2 ^ k) (blkPos x k) (2 ^ (K - k)) &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k) +
        (((pack (2 ^ k) (blkCnt x k) (2 ^ (K - k)) &&& (mskLo K k <<< 2 ^ k)) >>> 2 ^ k)
          <<< k) =
      pack (2 ^ (k + 1)) (blkPos x (k + 1)) (2 ^ (K - (k + 1)))) := by
  have hn : 2 ^ (K - k) = 2 * 2 ^ (K - k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hn' : K - (k + 1) = K - k - 1 := by omega
  have hw : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
  rw [hn, hn', hw, mskLo_eq K k hk]
  have hc : ∀ j < 2 * 2 ^ (K - k - 1), blkCnt x k j < 2 ^ 2 ^ k := fun j _ => blkCnt_lt x k j
  have hp : ∀ j < 2 * 2 ^ (K - k - 1), blkPos x k j < 2 ^ 2 ^ k := fun j _ => blkPos_lt x k j
  rw [lowFields _ _ _ hc, highFields _ _ _ hc, lowFields _ _ _ hp, highFields _ _ _ hp,
    pack_shiftLeft, pack_add, pack_add, pack_add]
  constructor
  · apply pack_congr
    intro j _
    rw [blkCnt_succ]
  · apply pack_congr
    intro j _
    rw [blkPos_succ]

theorem swarGo_spec (x K : ℕ) : ∀ m k, k + m = K →
    swarGo K m k (pack (2 ^ k) (blkCnt x k) (2 ^ (K - k)))
      (pack (2 ^ k) (blkPos x k) (2 ^ (K - k))) = (blkCnt x K 0, blkPos x K 0) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have e : k = K := by omega
    subst e
    rw [swarGo_zero, Nat.sub_self, pow_zero, pack_one, pack_one]
  | succ m ih =>
    intro k hk
    rw [swarGo_succ, (swar_level x K k (by omega)).1, (swar_level x K k (by omega)).2]
    exact ih (k + 1) (by omega)

theorem pack_bitv (x : ℕ) : ∀ N, pack 1 (fun j => bitv x j) N = x % 2 ^ N
  | 0 => by simp [pack_zero, Nat.mod_one]
  | N + 1 => by
    rw [pack_succ, pack_bitv x N, Nat.mod_pow_succ]
    unfold bitv
    ring

/-- **The popcount is exact**: for `x < 2^(2^K)`, `swarGo` returns the number of set bits and
the sum of their positions. -/
theorem swarGo_eq (x K : ℕ) (hx : x < 2 ^ 2 ^ K) :
    swarGo K K 0 x 0 =
      (∑ t ∈ range (2 ^ K), bitv x t, ∑ t ∈ range (2 ^ K), t * bitv x t) := by
  have h := swarGo_spec x K K 0 (by omega)
  have hc : pack (2 ^ 0) (blkCnt x 0) (2 ^ (K - 0)) = x := by
    rw [pow_zero, Nat.sub_zero, pack_congr 1 _ _ (fun j => bitv x j) (fun j _ => by
      simp [blkCnt]), pack_bitv, Nat.mod_eq_of_lt hx]
  have hs : pack (2 ^ 0) (blkPos x 0) (2 ^ (K - 0)) = 0 := by
    unfold pack
    simp [blkPos]
  rw [hc, hs] at h
  rw [h]
  simp [blkCnt, blkPos]

/-! ## 5. One segment, and a chain of segments -/

/-- **The sum of the primes of `[lo, lo + W)`**, computed by the sieve and the popcount
(`2^K ≥ W` bits). -/
def segSum (K W lo : ℕ) (ps : List ℕ) : ℕ :=
  lo * (swarGo K K 0 (sieveBits W lo ps) 0).1 + (swarGo K K 0 (sieveBits W lo ps) 0).2

/-- The number of primes of `[lo, lo + W)`, computed the same way. -/
def segCount (K W lo : ℕ) (ps : List ℕ) : ℕ := (swarGo K K 0 (sieveBits W lo ps) 0).1

theorem sum_range_cut (K W : ℕ) (hW : W ≤ 2 ^ K) (g : ℕ → ℕ) :
    ∑ t ∈ range (2 ^ K), (if t < W then g t else 0) = ∑ t ∈ range W, g t := by
  rw [show 2 ^ K = W + (2 ^ K - W) by omega, sum_range_add]
  rw [sum_eq_zero (s := range (2 ^ K - W)) (fun t _ => by simp), add_zero]
  apply sum_congr rfl
  intro t ht
  simp [mem_range.mp ht]

theorem bitv_sieveBits (W lo : ℕ) (ps : List ℕ) (hW : W ≤ 2 ^ 64) (hlo : 2 ≤ lo)
    (hps : ∀ p ∈ ps, 2 ≤ p ∧ p < lo) (hcomp : ∀ q, q.Prime → q * q < lo + W → q ∈ ps)
    (t : ℕ) : bitv (sieveBits W lo ps) t = if t < W ∧ (lo + t).Prime then 1 else 0 := by
  rw [bitv_eq]
  by_cases h : t < W ∧ (lo + t).Prime
  · rw [if_pos ((testBit_sieveBits_prime W lo ps hW hlo hps hcomp t).mpr h), if_pos h]
  · rw [if_neg h, if_neg]
    rw [testBit_sieveBits_prime W lo ps hW hlo hps hcomp t]
    exact h

theorem sieveBits_lt_pow (K W lo : ℕ) (ps : List ℕ) (hWK : W ≤ 2 ^ K) (hW : W ≤ 2 ^ 64)
    (hps : ∀ p ∈ ps, 2 ≤ p ∧ p < lo) : sieveBits W lo ps < 2 ^ 2 ^ K :=
  lt_of_lt_of_le (sieveBits_lt W lo ps hW (fun p hp => by have := hps p hp; omega))
    (Nat.pow_le_pow_right (by norm_num) hWK)

/-- **`segSum` is the sum of the primes of the segment.** -/
theorem segSum_eq (K W lo : ℕ) (ps : List ℕ) (hWK : W ≤ 2 ^ K) (hW : W ≤ 2 ^ 64)
    (hlo : 2 ≤ lo) (hps : ∀ p ∈ ps, 2 ≤ p ∧ p < lo)
    (hcomp : ∀ q, q.Prime → q * q < lo + W → q ∈ ps) :
    segSum K W lo ps = ∑ m ∈ Ico lo (lo + W), if m.Prime then m else 0 := by
  unfold segSum
  rw [swarGo_eq _ K (sieveBits_lt_pow K W lo ps hWK hW hps)]
  simp only [bitv_sieveBits W lo ps hW hlo hps hcomp]
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, mul_sum, ← sum_add_distrib,
    ← sum_range_cut K W hWK]
  apply sum_congr rfl
  intro t _
  by_cases h1 : t < W <;> by_cases h2 : (lo + t).Prime <;> simp [h1, h2]

/-- **`segCount` is the number of primes of the segment.** -/
theorem segCount_eq (K W lo : ℕ) (ps : List ℕ) (hWK : W ≤ 2 ^ K) (hW : W ≤ 2 ^ 64)
    (hlo : 2 ≤ lo) (hps : ∀ p ∈ ps, 2 ≤ p ∧ p < lo)
    (hcomp : ∀ q, q.Prime → q * q < lo + W → q ∈ ps) :
    segCount K W lo ps = ((Ico lo (lo + W)).filter Nat.Prime).card := by
  unfold segCount
  rw [swarGo_eq _ K (sieveBits_lt_pow K W lo ps hWK hW hps)]
  simp only [bitv_sieveBits W lo ps hW hlo hps hcomp]
  rw [card_filter, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← sum_range_cut K W hWK]
  apply sum_congr rfl
  intro t _
  by_cases h1 : t < W <;> by_cases h2 : (lo + t).Prime <;> simp [h1, h2]

/-- `AllSeg K W ps lo cs`: the consecutive width-`W` segments from `lo` have `segSum`s `cs`. -/
def AllSeg (K W : ℕ) (ps : List ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | lo, c :: cs => segSum K W lo ps = c ∧ AllSeg K W ps (lo + W) cs

theorem allSeg_nil (K W : ℕ) (ps : List ℕ) (lo : ℕ) : AllSeg K W ps lo [] := trivial

theorem allSeg_cons (K W : ℕ) (ps : List ℕ) (lo c : ℕ) (cs : List ℕ)
    (h1 : segSum K W lo ps = c) (h2 : AllSeg K W ps (lo + W) cs) : AllSeg K W ps lo (c :: cs) :=
  And.intro h1 h2

/-- **A chain of certified segments** sums the primes of their union. -/
theorem allSeg_sum (K W : ℕ) (ps : List ℕ) (hWK : W ≤ 2 ^ K) (hW : W ≤ 2 ^ 64) :
    ∀ (cs : List ℕ) (lo : ℕ), AllSeg K W ps lo cs → 2 ≤ lo → (∀ p ∈ ps, 2 ≤ p ∧ p < lo) →
      (∀ q, q.Prime → q * q < lo + cs.length * W → q ∈ ps) →
      ∑ m ∈ Ico lo (lo + cs.length * W), (if m.Prime then m else 0) = cs.sum
  | [], lo, _, _, _, _ => by simp
  | c :: cs, lo, h, hlo, hps, hcomp => by
    obtain ⟨h1, h2⟩ := h
    have e : lo + (c :: cs).length * W = lo + W + cs.length * W := by
      simp only [List.length_cons]
      ring
    have ih := allSeg_sum K W ps hWK hW cs (lo + W) h2 (by omega)
      (fun p hp => by have := hps p hp; omega)
      (fun q hq hqq => hcomp q hq (by rw [e]; exact hqq))
    rw [e, ← sum_Ico_consecutive _ (show lo ≤ lo + W by omega)
      (show lo + W ≤ lo + W + cs.length * W by omega), ih,
      ← segSum_eq K W lo ps hWK hW hlo hps
        (fun q hq hqq => hcomp q hq (by rw [e]; omega)), h1, List.sum_cons]

end Principia.Common.PrimeSumExact
