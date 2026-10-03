/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.KernelCert.Bits
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

/-!
# Kernel certificates: the prime bitset `primeBits L`

`primeBits L` is the natural number whose bit `n` is set exactly when `n ≤ L` and `n` is prime
(`testBit_primeBits`, both directions). It is an Eratosthenes sieve done with whole-bitset
operations: start from the bits `[2, L]`; for `d = 2, 3, …` while `d² ≤ L`, clear the multiples
`2d, 3d, …` with one `and`/`xor` against a pattern of multiples of `d`, which is itself built by
doubling (`p ↦ p ||| (p <<< len)`, `O(log(L/d))` operations). Every operation is kernel-native.

Soundness never depends on fuel: `sieveLoop` returns `0` (no primes) if its fuel runs out before
`d² > L`, and the fuel `L` given by `primeBits` is always enough (`testBit_primeBits` proves
both directions).

## Use

A certificate that needs "`q` is prime" for many `q ≤ L` can test all of them against one
`primeBits L` in bulk (`&&&`, `allOnes`), then read primality off with `testBit_primeBits`.
A single `Nat.testBit (primeBits L) q` in the kernel is one shift of an `L`-bit number, and the
kernel retains every such intermediate, so prefer bulk operations over many single tests.

## Measured (kernel, v4.31.0)

`primeBits L % (2^61 − 1)` by `decide +kernel`, matched against a numpy sieve (so the whole
bitset was checked, not only its low bits). Increments over the import baseline (0.82 GB, 9 s):

| `L` | 10^4 | 10^5 | 469 615 | 10^6 | 2·10^6 |
|---|---|---|---|---|---|
| peak memory | +0.03 GB | +0.13 GB | ≤ +0.54 GB | +1.2 GB | +3.0 GB |
| time | < 1 s | < 1 s | ~2 s | ~3 s | ~5 s |

Memory grows faster than `L` (about `L^1.3`: `√L` sieve rounds, each retaining a few `L`-bit
values), so `L ≈ 2·10^6` is the practical ceiling for one declaration on a 16 GB machine.
-/

namespace Principia.Common.KernelCert

/-- Double the pattern `cur` of the multiples of `d` below `len` until `L < len`. -/
def multsDbl (L : ℕ) : ℕ → ℕ → ℕ → ℕ
  | cur, _, 0 => cur
  | cur, len, f + 1 => if L < len then cur else multsDbl L (cur ||| (cur <<< len)) (len + len) f

/-- The bitset of the multiples of `d` (including `0`) below some bound `> L`. -/
def mults (d L : ℕ) : ℕ := multsDbl L 1 d L

/-- Clear the multiples `2d, 3d, …` of `d` from `bits`. -/
def sieveStep (L bits d : ℕ) : ℕ := bits ^^^ (bits &&& (mults d L <<< (d + d)))

/-- Sieve by `d, d + 1, …` while `d² ≤ L`; `0` if the fuel runs out first. -/
def sieveLoop (L : ℕ) : ℕ → ℕ → ℕ → ℕ
  | bits, d, 0 => if L < d * d then bits else 0
  | bits, d, f + 1 => if L < d * d then bits else sieveLoop L (sieveStep L bits d) (d + 1) f

/-- The bits `2, …, L`. -/
def initBits (L : ℕ) : ℕ := lowMask (L - 1) <<< 2

/-- **The prime bitset**: bit `n` is set iff `n ≤ L` and `n` is prime (`testBit_primeBits`). -/
def primeBits (L : ℕ) : ℕ := sieveLoop L (initBits L) 2 L

theorem multsDbl_spec {L d : ℕ} :
    ∀ f cur len, 0 < len → d ∣ len → (∀ i, cur.testBit i = decide (d ∣ i ∧ i < len)) →
      ∃ len', d ∣ len' ∧ (L < len * 2 ^ f → L < len') ∧
        ∀ i, (multsDbl L cur len f).testBit i = decide (d ∣ i ∧ i < len')
  | 0, cur, len, _, hd, hc => ⟨len, hd, by simp, by simpa [multsDbl] using hc⟩
  | f + 1, cur, len, hlen, hd, hc => by
      simp only [multsDbl]
      split_ifs with hL
      · exact ⟨len, hd, fun _ => hL, hc⟩
      · obtain ⟨len', h1, h2, h3⟩ := multsDbl_spec f (cur ||| (cur <<< len)) (len + len)
          (by omega) (Nat.dvd_add hd hd) (by
            intro i
            rw [Nat.testBit_or, Nat.testBit_shiftLeft, hc, hc]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
              · exact ⟨h1, by omega⟩
              · exact ⟨(Nat.dvd_sub_iff_left h1 hd).1 h2, by omega⟩
            · rintro ⟨h1, h2⟩
              by_cases hi : i < len
              · exact Or.inl ⟨h1, hi⟩
              · exact Or.inr ⟨by omega, (Nat.dvd_sub_iff_left (by omega) hd).2 h1, by omega⟩)
        refine ⟨len', h1, fun h => h2 ?_, h3⟩
        rw [pow_succ] at h
        have : len * (2 ^ f * 2) = (len + len) * 2 ^ f := by
          rw [Nat.mul_comm (2 ^ f) 2, ← Nat.mul_assoc, Nat.mul_two]
        omega

theorem mults_spec {d L : ℕ} (hd : 0 < d) :
    ∃ len', L < len' ∧ ∀ i, (mults d L).testBit i = decide (d ∣ i ∧ i < len') := by
  obtain ⟨len', -, h2, h3⟩ := multsDbl_spec (L := L) (d := d) L 1 d hd (dvd_refl d) (by
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_eq]
    constructor
    · rintro rfl
      exact ⟨dvd_zero d, hd⟩
    · rintro ⟨h1, h2⟩
      exact Nat.eq_zero_of_dvd_of_lt h1 h2)
  refine ⟨len', h2 ?_, h3⟩
  have h1 : L < 2 ^ L := Nat.lt_two_pow_self
  have h2 : 2 ^ L ≤ d * 2 ^ L := Nat.le_mul_of_pos_left _ hd
  omega

theorem testBit_sieveStep {L bits d : ℕ} (hd : 0 < d) (i : ℕ) (hi : i ≤ L) :
    (sieveStep L bits d).testBit i = (bits.testBit i && !decide (d + d ≤ i ∧ d ∣ i)) := by
  obtain ⟨len', hlen, hm⟩ := mults_spec (d := d) (L := L) hd
  simp only [sieveStep, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, hm]
  by_cases h2 : d + d ≤ i
  · have hdv : d ∣ i - (d + d) ↔ d ∣ i := by
      rw [Nat.dvd_sub_iff_left h2 (Nat.dvd_add (dvd_refl d) (dvd_refl d))]
    have hlt : i - (d + d) < len' := by omega
    cases hb : bits.testBit i <;> by_cases hdi : d ∣ i <;> simp [h2, hdv, hlt, hdi]
  · cases hb : bits.testBit i <;> simp [h2]

theorem testBit_initBits (L i : ℕ) : (initBits L).testBit i = decide (2 ≤ i ∧ i ≤ L) := by
  simp only [initBits, Nat.testBit_shiftLeft, testBit_lowMask]
  by_cases h : 2 ≤ i
  · have : (i - 2 < L - 1) ↔ i ≤ L := by omega
    simp [h, this]
  · simp [h]

/-- Invariant of the sieve: a set bit `n` lies in `[2, L]` and has no divisor `e ∈ [2, d)` with
`2e ≤ n`. -/
theorem sieveLoop_sound {L : ℕ} :
    ∀ f bits d, 2 ≤ d →
      (∀ n, bits.testBit n = true →
        2 ≤ n ∧ n ≤ L ∧ ∀ e, 2 ≤ e → e < d → e ∣ n → n < e + e) →
      ∀ n, (sieveLoop L bits d f).testBit n = true → n ≤ L ∧ n.Prime := by
  have final : ∀ bits d : ℕ, L < d * d →
      (∀ n, bits.testBit n = true →
        2 ≤ n ∧ n ≤ L ∧ ∀ e, 2 ≤ e → e < d → e ∣ n → n < e + e) →
      ∀ n, bits.testBit n = true → n ≤ L ∧ n.Prime := by
    intro bits d hLd hinv n hn
    obtain ⟨h2, hL, hno⟩ := hinv n hn
    refine ⟨hL, ?_⟩
    by_contra hnp
    have hmf : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hmd : n.minFac < d := by
      by_contra hc
      have : d * d ≤ n.minFac ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul (by omega) (by omega)
      omega
    have hlt := hno n.minFac hmf.two_le hmd (Nat.minFac_dvd n)
    obtain ⟨c, hc⟩ := Nat.minFac_dvd n
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [Nat.mul_zero] at hc
      omega
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [Nat.mul_one] at hc
      exact hnp (by rw [hc]; exact hmf)
    have hc2 : 2 ≤ c := by omega
    have : n.minFac * 2 ≤ n.minFac * c := Nat.mul_le_mul_left _ hc2
    omega
  intro f
  induction f with
  | zero =>
    intro bits d _ hinv n hn
    simp only [sieveLoop] at hn
    split_ifs at hn with hLd
    · exact final bits d hLd hinv n hn
    · simp at hn
  | succ f ih =>
    intro bits d hd hinv n hn
    simp only [sieveLoop] at hn
    split_ifs at hn with hLd
    · exact final bits d hLd hinv n hn
    · refine ih (sieveStep L bits d) (d + 1) (by omega) ?_ n hn
      intro m hm
      have hmL : m ≤ L := by
        by_contra hc
        have hmask : (sieveStep L bits d).testBit m = true → bits.testBit m = true := by
          intro h
          simp only [sieveStep, Nat.testBit_xor, Nat.testBit_and] at h
          cases hb : bits.testBit m <;> simp_all
        exact hc (hinv m (hmask hm)).2.1
      rw [testBit_sieveStep (by omega) m hmL] at hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hm
      obtain ⟨hb, hnd⟩ := hm
      obtain ⟨h2, hL, hno⟩ := hinv m hb
      refine ⟨h2, hL, fun e he1 he2 hed => ?_⟩
      rcases Nat.lt_or_ge e d with h | h
      · exact hno e he1 h hed
      · have : e = d := by omega
        subst this
        by_contra hc
        exact hnd ⟨by omega, hed⟩

/-- Completeness of the sieve: a prime `≤ L` survives, provided the fuel reaches `d² > L`. -/
theorem sieveLoop_complete {L p : ℕ} (hp : p.Prime) (hpL : p ≤ L) :
    ∀ f bits d, 2 ≤ d → L < (d + f) * (d + f) → bits.testBit p = true →
      (sieveLoop L bits d f).testBit p = true := by
  intro f
  induction f with
  | zero =>
    intro bits d _ hf hb
    simp only [sieveLoop, Nat.add_zero] at hf ⊢
    rw [if_pos hf]
    exact hb
  | succ f ih =>
    intro bits d hd hf hb
    simp only [sieveLoop]
    split_ifs with hLd
    · exact hb
    · apply ih _ (d + 1) (by omega) (by rw [show d + 1 + f = d + (f + 1) by omega]; exact hf)
      rw [testBit_sieveStep (by omega) p hpL, hb]
      simp only [Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]
      rintro ⟨h1, h2⟩
      rcases (Nat.dvd_prime hp).1 h2 with h | h
      · omega
      · omega

/-- **The prime bitset is exact**: `testBit (primeBits L) n = true ↔ n ≤ L ∧ n.Prime`. -/
theorem testBit_primeBits (L n : ℕ) : (primeBits L).testBit n = true ↔ n ≤ L ∧ n.Prime := by
  constructor
  · intro h
    refine sieveLoop_sound L (initBits L) 2 le_rfl (fun m hm => ?_) n h
    rw [testBit_initBits] at hm
    simp only [decide_eq_true_eq] at hm
    exact ⟨hm.1, hm.2, fun e h1 h2 _ => by omega⟩
  · rintro ⟨hL, hp⟩
    apply sieveLoop_complete hp hL L (initBits L) 2 le_rfl
      (Nat.lt_of_lt_of_le (by omega : L < 2 + L) (Nat.le_mul_of_pos_left _ (by omega)))
    rw [testBit_initBits]
    simp [hp.two_le, hL]

end Principia.Common.KernelCert
