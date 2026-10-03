/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false

/-!
# Kernel certificates: bitsets held in one natural number

A finite set `X ⊆ ℕ` is stored as the single natural `∑_{i ∈ X} 2^i`; membership is
`Nat.testBit`. The Lean 4 kernel (v4.31.0) evaluates `+ - * / % gcd == ≤ &&& ||| ^^^ <<< >>>` on
natural-number literals with GMP, so a bitset of millions of bits is manipulated in the kernel at
native speed by `decide +kernel`, which leaves no `ofReduceBool` in the footprint.

## Measured kernel facts (v4.31.0, 2026-09-26; each probe a one-line `decide +kernel` example)

* `<<<` with a shift of `4·10⁷` bits and `>>>`: native (a few seconds, ~0.2 GB).
* `Nat.gcd` on two 10⁶-bit numbers: native (instant).
* `Nat.pow`: native only for exponents `≤ 2^24`; `2 ^ (2^24 + 1)` falls back to unfolding and
  passed 3 GB in 23 s. **Build powers of two as `1 <<< w`** (as `lowMask` does).
* `Nat.log2` is **not** kernel-native: `Nat.log2 (1 <<< 100000)` timed out at 120 s. Never let the
  kernel evaluate it.
* The kernel caches every intermediate `whnf` result for the whole declaration, so **every value a
  certificate computes stays in memory until the declaration is checked**: a subset-sum step on a
  `1.56·10^8`-bit bitset retains ~58 MB (measured, 10, 30 and 60 steps: 0.70, 1.82, 3.58 GB
  peak), so 1164 such steps would need ~68 GB. Keep bitsets narrow, or split the work over
  several declarations.
* In a function the kernel unfolds, write a numeric step as `Nat.add x 2` (or `x + 1 + 1`), not
  `x + 2`: a scan written with `x + 2` ran 15× slower (97 s against 6.5 s, reproduced) than the
  same scan with `Nat.add x 2`. `x + 1` is fast.

## This file

`lowMask w = 2^w − 1` and the interval test `allOnes bits a b` (every bit in `[a, b]` is set),
with its soundness theorem `allOnes_sound`.
-/

namespace Principia.Common.KernelCert

/-- `lowMask w = 2^w − 1`, the bitset `{0, …, w − 1}`, computed as `(1 <<< w) - 1`. -/
def lowMask (w : ℕ) : ℕ := (1 <<< w) - 1

theorem testBit_lowMask (w i : ℕ) : (lowMask w).testBit i = decide (i < w) := by
  unfold lowMask
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

/-- `allOnes bits a b`: every position of `[a, b]` is a set bit of `bits`. One shift, one `and`
and one comparison, all kernel-native. -/
def allOnes (bits a b : ℕ) : Bool :=
  (bits >>> a) &&& lowMask (b + 1 - a) == lowMask (b + 1 - a)

/-- **Soundness of `allOnes`.** -/
theorem allOnes_sound {bits a b : ℕ} (h : allOnes bits a b = true) {n : ℕ} (han : a ≤ n)
    (hnb : n ≤ b) : bits.testBit n = true := by
  unfold allOnes at h
  have he : (bits >>> a) &&& lowMask (b + 1 - a) = lowMask (b + 1 - a) := by
    simpa using h
  have hbit := congrArg (fun x => x.testBit (n - a)) he
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lowMask] at hbit
  have hlt : n - a < b + 1 - a := by omega
  have hna : a + (n - a) = n := by omega
  rw [hna] at hbit
  simpa [hlt] using hbit

end Principia.Common.KernelCert
