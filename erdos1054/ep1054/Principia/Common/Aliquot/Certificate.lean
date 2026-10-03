/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Aliquot.Main
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD

set_option autoImplicit false

/-!
# The certificate: the untouchable numbers have lower density `≥ 0.0604`

Chen–Zhao take `2M = 2^7 · 3^5 · 5^4 · 7^3 · 11^2 · 13 · 17 ⋯ 41` and report `g_M > 0.0602757`;
numerically `g_M = 0.06027578…`, a margin of `8·10⁻⁸`, too thin for a rounded certificate. We
add the primes `43, 47, 53, 59`:
```
Q* = 2^7 · 3^5 · 5^4 · 7^3 · 11^2 · 13 · 17 · 19 · 23 · 29 · 31 · 37 · 41 · 43 · 47 · 53 · 59
   = 671566353019062156873257040000,
```
whose Chen–Zhao constant is `czConst Q* = 0.0608116…` (floating point, over its 10 321 920 even
classes). The rounded programme `dp` of `Aliquot/DP.lean` (abundancy scale `HS = 2^30`, grid
step `2^21` with factor-2 bands, weight scale `WS = 2^64`) evaluates, in one `decide +kernel`
(`dp_czList`, about 15 s of kernel time), to `1115780034229924130`, so by `dp_le`
```
czConst Q* ≥ 1115780034229924130 / 2^64 = 0.0604865…      (czConst_czQ_ge).
```
With `chenZhao_count` at `ε = 0.00008`: **`untouchable_count_ge`**, eventually
`0.0604 X ≤ #{N ≤ X : N untouchable}`. This is Chen–Zhao's Theorem 1 at a larger modulus; it is
not new mathematics.
-/

namespace Principia.Common.Aliquot

open Finset

/-- The odd prime powers of `Q*` (every `lo = 0`). -/
def czTail : List (ℕ × ℕ × ℕ) :=
  [(3, 5, 0), (5, 4, 0), (7, 3, 0), (11, 2, 0), (13, 1, 0), (17, 1, 0), (19, 1, 0), (23, 1, 0),
    (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 1, 0), (47, 1, 0), (53, 1, 0),
    (59, 1, 0)]

/-- The prime powers of `Q*`; the head `(2, 7, 1)` keeps the even classes only. -/
def czList : List (ℕ × ℕ × ℕ) := (2, 7, 1) :: czTail

/-- The modulus `Q* = 2^7 · 3^5 · 5^4 · 7^3 · 11^2 · 13 ⋯ 59`. -/
def czQ : ℕ := QL czList

theorem czQ_eq : czQ = 671566353019062156873257040000 := by
  decide +kernel

theorem czQ_pos : 0 < czQ := by
  rw [czQ_eq]
  norm_num

/-- **The kernel evaluation of the rounded programme.** -/
theorem dp_czList :
    dp (band (2 ^ 30) (2 ^ 21)) (2 ^ 30) (2 ^ 64) czList = 1115780034229924130 := by
  decide +kernel

theorem validTail_czTail : ValidTail czTail := by
  norm_num [czTail, ValidTail, QL]

theorem coprime_two_czTail : Nat.Coprime 2 (QL czTail) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  decide +kernel

/-- `Ex czList cz = czConst Q*`. -/
theorem Ex_czList : Ex czList cz = czConst czQ := by
  unfold czConst czQ czList
  rw [Ex_head_eq 2 7 1 czTail Nat.prime_two coprime_two_czTail validTail_czTail, pow_one]

/-- **`czConst Q* ≥ 1115780034229924130 / 2^64 = 0.0604865…`** (`2^64 = 18446744073709551616`). -/
theorem czConst_czQ_ge :
    (1115780034229924130 : ℝ) / 18446744073709551616 ≤ czConst czQ := by
  have h := dp_le (band (2 ^ 30) (2 ^ 21)) (band_le _ _) (2 ^ 30) (2 ^ 64) (by positivity) czList
  rw [dp_czList, Ex_czList] at h
  push_cast at h
  rw [div_le_iff₀ (by norm_num)]
  linarith

open Classical in
/-- **The untouchable numbers up to `X` number at least `0.0604 X`, for all large `X`.** -/
theorem untouchable_count_ge :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (0.0604 : ℝ) * X ≤ (#{N ∈ Icc 1 X | N ∈ Untouchable} : ℝ) := by
  obtain ⟨X₀, hX₀⟩ := chenZhao_count czQ czQ_pos 0.00008 (by norm_num)
  refine ⟨X₀, fun X hX => ?_⟩
  have hc : (0.0604 : ℝ) ≤ czConst czQ - 0.00008 := by
    have := czConst_czQ_ge
    norm_num at this ⊢
    linarith
  calc (0.0604 : ℝ) * X ≤ (czConst czQ - 0.00008) * X :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
    _ ≤ _ := hX₀ X hX

end Principia.Common.Aliquot
