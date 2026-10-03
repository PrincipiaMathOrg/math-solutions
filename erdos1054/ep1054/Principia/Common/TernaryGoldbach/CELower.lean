/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.CoeurSpine
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

/-!
# `c_E ≥ 1.25`, elementarily — and the `c⁻` it supports

`OC.CoeurY` carries the denominator `log √x − 1.306476`. That constant is
`c⁻ = −(log 14 − c_E)` at Rosser–Schoenfeld's enclosure `c_E ≥ 1.3325822` (`OC.cminus_le`,
`CoeurSpine.b_le_h`), which is a precision-`10⁻⁷` numeric input (`CY.CERange`, named).

It is not needed at that precision. At the corrected minarcs constants `(0.811, 45.7575)`, moving
`c⁻` from `−1.306476` to `−1.39` takes the sup of `M̃` (at `x = 4.9·10²⁶`) from `0.81849` to
`0.82010`. That is `+0.0016`, including the `c⁻`-dependence of `coefC`'s jump constant
`−2(log(3/8) + c⁺ − (8/15)c⁻)`, and it is set against the budget `0.84` of the weight-aware split
(`Alt7.FromWeights`). A first pricing that held the jump constant at `−3.538215` gave `+0.0025`. This file proves `c_E ≥ 1.25` from Mathlib's
`H₂₀ − log 21 < γ`, the seven primes `≤ 17`, and log bounds by power comparison (the `cminus_le`
technique): `3¹² ≥ 2¹⁹`, `5²⁸ ≥ 2⁶⁵`, `7⁵ ≥ 2¹⁴`, `11¹¹ ≥ 2³⁸`, `13¹⁰ ≥ 2³⁷`, `17¹² ≥ 2⁴⁹`,
`21³³ ≤ 2¹⁴⁵`, `14²⁶ ≤ 2⁹⁹`. The bound it reaches is `1.25686`.

* `summable_cE`: `∑_p log p/(p(p−1))` converges (`log n ≤ 2√n`, so the terms are `≤ 4n^{−3/2}`).
* `gamma_ge`: `γ > H₂₀ − log 21 ≥ 0.55209`.
* `primes_ge`: `∑_p log p/(p(p−1)) ≥ 0.70476` (the primes `≤ 17`).
* `cE_ge`: `1.25 ≤ c_E`.
* `cminus_139`: `−1.39 ≤ log 2 − log 28 + c_E` (`log 14 ≤ 99/26 · log 2`), the analogue of
  `OC.cminus_le` at `c⁻ = −1.39`.
-/

namespace Principia.Common.TernaryGoldbach.CEL

/-- `log n/(n(n−1)) ≤ 4 (n^{3/2})⁻¹` for every `n : ℕ`. -/
theorem term_le (n : ℕ) :
    Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 4 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set t := (n : ℝ) ^ ((1 : ℝ) / 2) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) = n * t := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one]
  have hsq : t ^ 2 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hl : Real.log n ≤ t / (1 / 2) := Real.log_le_rpow_div hn0.le (by norm_num)
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [h32, div_le_iff₀ hden]
  have hnt : 0 < (n : ℝ) * t := mul_pos hn0 ht0
  have e : 4 * ((n : ℝ) * t)⁻¹ * ((n : ℝ) * ((n : ℝ) - 1)) = 4 * ((n : ℝ) - 1) / t := by
    field_simp
  rw [e, le_div_iff₀ ht0]
  have hl2 : Real.log n ≤ 2 * t := by linarith
  nlinarith

/-- **`∑_p log p/(p(p−1))` converges.** -/
theorem summable_cE :
    Summable (fun p : Nat.Primes => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hg : Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) term_le
      ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4)
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
  exact hg.comp_injective Subtype.val_injective

/-- `a log p ≥ b log 2` from `p^a ≥ 2^b`. -/
theorem log_ge_of_pow (p : ℝ) (a b : ℕ) (hp : 0 < p) (h : (2 : ℝ) ^ b ≤ p ^ a) :
    (b : ℝ) * Real.log 2 ≤ a * Real.log p := by
  have g := Real.log_le_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at g

/-- `a log p ≤ b log 2` from `p^a ≤ 2^b`. -/
theorem log_le_of_pow (p : ℝ) (a b : ℕ) (hp : 0 < p) (h : p ^ a ≤ (2 : ℝ) ^ b) :
    (a : ℝ) * Real.log p ≤ b * Real.log 2 := by
  have g := Real.log_le_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at g

/-- **`γ > H₂₀ − log 21 ≥ 0.55209`**: `eulerMascheroniSeq 20 < γ`, `H₂₀ = 55835135/15519504`,
`33 log 21 ≤ 145 log 2`. -/
theorem gamma_ge : (0.55209 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h0 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 20
  have hq : harmonic 20 = 55835135 / 15519504 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have e : Real.eulerMascheroniSeq 20 = 55835135 / 15519504 - Real.log 21 := by
    rw [Real.eulerMascheroniSeq, hq]
    norm_num
  have h21 := log_le_of_pow 21 33 145 (by norm_num) (by norm_num)
  have hl2 := Real.log_two_lt_d9
  push_cast at h21
  rw [e] at h0
  linarith

/-- **`∑_p log p/(p(p−1)) ≥ 0.70476`**, from the primes `≤ 17`. -/
theorem primes_ge :
    (0.70476 : ℝ) ≤ ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hs := summable_cE
  let S : Finset Nat.Primes := {⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨5, by norm_num⟩,
    ⟨7, by norm_num⟩, ⟨11, by norm_num⟩, ⟨13, by norm_num⟩, ⟨17, by norm_num⟩}
  have hle := hs.sum_le_tsum S (fun p _ => by
    have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith))
  have hsum : ∑ p ∈ S, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) =
      Real.log 2 / 2 + (Real.log 3 / 6 + (Real.log 5 / 20 + (Real.log 7 / 42 +
        (Real.log 11 / 110 + (Real.log 13 / 156 + Real.log 17 / 272))))) := by
    simp only [S]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  have l2 := Real.log_two_gt_d9
  have l3 := log_ge_of_pow 3 12 19 (by norm_num) (by norm_num)
  have l5 := log_ge_of_pow 5 28 65 (by norm_num) (by norm_num)
  have l7 := log_ge_of_pow 7 5 14 (by norm_num) (by norm_num)
  have l11 := log_ge_of_pow 11 11 38 (by norm_num) (by norm_num)
  have l13 := log_ge_of_pow 13 10 37 (by norm_num) (by norm_num)
  have l17 := log_ge_of_pow 17 12 49 (by norm_num) (by norm_num)
  push_cast at l3 l5 l7 l11 l13 l17
  rw [hsum] at hle
  linarith

/-- **`1.25 ≤ c_E`** (`CY.cE = γ + ∑_p log p/(p(p−1))`): `0.55209 + 0.70476 = 1.25685`. -/
theorem cE_ge : (1.25 : ℝ) ≤ CY.cE := by
  have hg := gamma_ge
  have hp := primes_ge
  unfold CY.cE
  linarith

/-- **`c⁻ = −1.39`**: `−1.39 ≤ log 2 − log 28 + c_E`, from `c_E ≥ 1.25` and
`log 14 ≤ (99/26) log 2 = 2.6392912` (`14²⁶ ≤ 2⁹⁹`). The analogue of `OC.cminus_le`. -/
theorem cminus_139 : (-1.39 : ℝ) ≤ Real.log 2 - Real.log 28 + CY.cE := by
  have hc := cE_ge
  have h14 := log_le_of_pow 14 26 99 (by norm_num) (by norm_num)
  have e : Real.log 28 = Real.log 2 + Real.log 14 := by
    rw [show (28 : ℝ) = 2 * 14 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hl2 := Real.log_two_lt_d9
  push_cast at h14
  linarith

end Principia.Common.TernaryGoldbach.CEL
