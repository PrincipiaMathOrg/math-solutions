/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinorW
import Principia.Common.TernaryGoldbach.RegWHelf

set_option autoImplicit false

/-!
# `eq:lamber` on Helfgott's `φ`: `MinW.LamberNumW HW.phi`, proved

`MinW.LamberNumW φ` asks for `C_{φ,3}(K)·(s − p) ≤ 3.6·10⁻⁴` at every `x ≥ 4.9·10²⁶`, every
`s ≤ felipa(x) = 0.640209 log x − 0.021095` and every `p ≥ 8.6129`, with `K = log(x/49)/2`.

* `φ(w) = w²e^{−w²/2} ≤ w²`, so `∫₀^{1/K}|φ| ≤ 1/(3K³)` (`int_absPhi_le`), and with
  `|φ|₁ = √(π/2)` (`RW.phiL1_helf`) this gives `C_{φ,3}(K) ≤ 0.278/K³` (`cPhi3_le`). Helfgott
  prints `0.2779/K³`; `0.278` needs only `π > 3.141592`.
* The rest is one cubic inequality in `w = log(x/49) ≥ 57.558`, from `2^8866 ≤ (4.9·10²⁶)^100` and
  `49^100 ≤ 2^562` (`log_ge_of`, `log_49_le`).

`lamber_at` is parametric in the floor `p₀` and the constant `c`, so a restated floor is a new
instance, not a new proof. At `p₀ = 8.6129`, `c = 3.6·10⁻⁴` the margin is `0.5 %`
(`lamberNumW_helf`). At `p₀ = 8.36` the constant `3.6·10⁻⁴` is FALSE (ratio `1.0031`) and
`3.62·10⁻⁴` holds with `0.25 %` (`lamber_836`).
-/

namespace Principia.Common.TernaryGoldbach.LW

open MeasureTheory Set

/-- **`∫₀^b |φ| ≤ b³/3`** for `b ≥ 0`, from `φ(w) = w²e^{−w²/2} ≤ w²`. -/
theorem int_absPhi_le (b : ℝ) (hb : 0 ≤ b) :
    ∫ w in (0 : ℝ)..b, |HW.phi w| ≤ b ^ 3 / 3 := by
  have hmono : ∫ w in (0 : ℝ)..b, |HW.phi w| ≤ ∫ w in (0 : ℝ)..b, w ^ 2 := by
    apply intervalIntegral.integral_mono_on hb
    · exact HW.continuous_phi.abs.intervalIntegrable _ _
    · exact (continuous_pow 2).intervalIntegrable _ _
    · intro w _
      rw [abs_of_nonneg (HW.phi_nonneg w)]
      unfold HW.phi
      have h1 : Real.exp (-w ^ 2 / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg w]
      calc w ^ 2 * Real.exp (-w ^ 2 / 2) ≤ w ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg w)
        _ = w ^ 2 := mul_one _
  have hint : ∫ w in (0 : ℝ)..b, w ^ 2 = b ^ 3 / 3 := by
    rw [integral_pow]
    norm_num
  linarith

/-- **`1.04488/0.834 ≤ √(π/2)`**, from `π > 3.141592` (`(1.04488/0.834)² = 1.5696424`). -/
theorem sqrt_pi_half_ge : (1.04488 : ℝ) / 0.834 ≤ Real.sqrt (Real.pi / 2) := by
  have hpi := Real.pi_gt_d6
  have h : ((1.04488 : ℝ) / 0.834) ^ 2 ≤ Real.pi / 2 := by
    norm_num
    linarith
  calc (1.04488 : ℝ) / 0.834 = Real.sqrt (((1.04488 : ℝ) / 0.834) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_le_sqrt h

/-- **`C_{φ,3}(K) ≥ 0`** for `K > 0`. -/
theorem cPhi3_nonneg (K : ℝ) (hK : 0 < K) : 0 ≤ MinSp.cPhi3 HW.phi K := by
  unfold MinSp.cPhi3
  have hl : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  rw [hl]
  apply mul_nonneg
  · positivity
  · exact intervalIntegral.integral_nonneg (one_div_nonneg.2 hK.le) fun w _ => abs_nonneg _

/-- **`C_{φ,3}(K) ≤ 0.278/K³`** for `K > 0` (`eq:malus`; Helfgott: `0.2779/K³`). -/
theorem cPhi3_le (K : ℝ) (hK : 0 < K) : MinSp.cPhi3 HW.phi K ≤ 0.278 / K ^ 3 := by
  unfold MinSp.cPhi3
  have hl : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  rw [hl]
  have hI := int_absPhi_le (1 / K) (one_div_nonneg.2 hK.le)
  have hs := sqrt_pi_half_ge
  have hspos : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 ≤ (1 / K) ^ 3 / 3 := div_nonneg (pow_nonneg (one_div_nonneg.2 hK.le) 3) (by norm_num)
  have hq : (1.04488 : ℝ) / Real.sqrt (Real.pi / 2) ≤ 0.834 := by
    rw [div_le_iff₀ hspos]
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.834)).1 hs
    linarith
  calc (1.04488 : ℝ) / Real.sqrt (Real.pi / 2) * ∫ w in (0 : ℝ)..(1 / K), |HW.phi w|
      ≤ 1.04488 / Real.sqrt (Real.pi / 2) * ((1 / K) ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ 0.834 * ((1 / K) ^ 3 / 3) := mul_le_mul_of_nonneg_right hq hb
    _ = 0.278 / K ^ 3 := by ring

set_option exponentiation.threshold 9000 in
/-- **`log x ≥ 61.4544`** for `x ≥ 4.9·10²⁶`, from `2^8866 ≤ (4.9·10²⁶)^100`
(`88.66·0.6931471803 = 61.454429`). -/
theorem log_ge_of (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 61.4544 ≤ Real.log x := by
  have hx0 : (0 : ℝ) < 49 * 10 ^ 25 := by norm_num
  have hN : (2 : ℕ) ^ 8866 ≤ (49 * 10 ^ 25) ^ 100 := by decide
  have hpow : (2 : ℝ) ^ 8866 ≤ x ^ 100 :=
    calc (2 : ℝ) ^ 8866 ≤ (49 * 10 ^ 25) ^ 100 := by exact_mod_cast hN
      _ ≤ x ^ 100 := pow_le_pow_left₀ hx0.le hx 100
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have := Real.log_two_gt_d9
  linarith

set_option exponentiation.threshold 600 in
/-- **`log 49 ≤ 3.8955`**, from `49^100 ≤ 2^562` (`5.62·0.6931471808 = 3.8954872`). -/
theorem log_49_le : Real.log 49 ≤ 3.8955 := by
  have hN : (49 : ℕ) ^ 100 ≤ 2 ^ 562 := by decide
  have hpow : (49 : ℝ) ^ 100 ≤ 2 ^ 562 := by exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have := Real.log_two_lt_d9
  linarith

/-- **`eq:lamber` at any floor `p₀` and constant `c`**, given the one cubic inequality in
`w = log(x/49) ≥ 57.558` (with `L = log 49 ∈ [0, 3.8955]`) that it reduces to. -/
theorem lamber_at (p₀ c : ℝ) (hc : 0 ≤ c)
    (hkey : ∀ w L : ℝ, 57.558 ≤ w → 0 ≤ L → L ≤ 3.8955 →
      0.278 * (0.640209 * (w + L) - 0.021095 - p₀) ≤ c * (w / 2) ^ 3) :
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 → p₀ ≤ p →
      MinSp.cPhi3 HW.phi (MinSp.kK (x / 49)) * (s - p) ≤ c := by
  intro x hx s p hs hp
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlogx := log_ge_of x hx
  have h49 := log_49_le
  have h49' : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  have hK : MinSp.kK (x / 49) = (Real.log x - Real.log 49) / 2 := by
    rw [MinSp.kK, Real.log_div hx0.ne' (by norm_num : (49 : ℝ) ≠ 0)]
  have hKpos : 0 < MinSp.kK (x / 49) := by
    rw [hK]
    linarith
  have hc3 := cPhi3_le _ hKpos
  have hc0 := cPhi3_nonneg _ hKpos
  rcases le_or_gt (s - p) 0 with hsp | hsp
  · have h0 := mul_le_mul_of_nonneg_left hsp hc0
    rw [mul_zero] at h0
    linarith
  · have hN : s - p ≤ 0.640209 * Real.log x - 0.021095 - p₀ := by linarith
    have hw : 57.558 ≤ Real.log x - Real.log 49 := by linarith
    have hk := hkey (Real.log x - Real.log 49) (Real.log 49) hw h49' h49
    have e : Real.log x - Real.log 49 + Real.log 49 = Real.log x := by ring
    rw [e] at hk
    calc MinSp.cPhi3 HW.phi (MinSp.kK (x / 49)) * (s - p)
        ≤ 0.278 / MinSp.kK (x / 49) ^ 3 * (s - p) := mul_le_mul_of_nonneg_right hc3 hsp.le
      _ ≤ 0.278 / MinSp.kK (x / 49) ^ 3 * (0.640209 * Real.log x - 0.021095 - p₀) :=
          mul_le_mul_of_nonneg_left hN (div_nonneg (by norm_num) (pow_pos hKpos 3).le)
      _ ≤ c := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hKpos 3), hK]
          linarith

/-- **`MinW.LamberNumW HW.phi`** — `eq:lamber` at `p ≥ 8.6129`, `3.6·10⁻⁴`: PROVED
(the cubic has a `0.5 %` margin at `w = 57.558`). -/
theorem lamberNumW_helf : MinW.LamberNumW HW.phi := by
  refine lamber_at 8.6129 3.6e-4 (by norm_num) fun w L hw hL0 hL => ?_
  have hd := sub_nonneg.2 hw
  nlinarith [mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd]

/-- **`eq:lamber` at the lower floor `p ≥ 8.36`**: `3.62·10⁻⁴` holds (`0.25 %` margin); at this
floor `3.6·10⁻⁴` is FALSE (ratio `1.0031` at the threshold). -/
theorem lamber_836 :
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 → 8.36 ≤ p →
      MinSp.cPhi3 HW.phi (MinSp.kK (x / 49)) * (s - p) ≤ 3.62e-4 := by
  refine lamber_at 8.36 3.62e-4 (by norm_num) fun w L hw hL0 hL => ?_
  have hd := sub_nonneg.2 hw
  nlinarith [mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd]

end Principia.Common.TernaryGoldbach.LW
