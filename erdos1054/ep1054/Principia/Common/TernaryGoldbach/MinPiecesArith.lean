/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPieces
import Principia.Common.TernaryGoldbach.MNumProofs

set_option autoImplicit false

/-!
# The NUMERIC links of `MinPieces.lean`, proved

* `coexistArith` : `MPc.CoexistArith` — PROVED. In the coexisting-approximation branch of
  `MPc.minMain2L_of`, the first-case bound `krawAt 0.811 45.7575` at `δ₀q ≈ x^{1/3}/3` is at most
  the second-case bound `0.3409x^{5/6}(log x)^{3/2} + 1522.5x^{2/3}log x`, for EVERY `x ≥ 3.4·10²³`
  (not just a sampled range): with `u = x^{1/6}`, `ℓ = log u`, `w = ℓ^{1/4}`, every quantity is
  bounded by a polynomial in `w` — `log ℓ ≤ 4w/e`, `ϝ(x^{1/3}/6) ≤ 2.2421 + 2.6314w`,
  `C_{x,t} ≤ log ℓ`, `log t ≤ 2w⁴ − 1` — and the comparison is a degree-6 polynomial inequality in
  `w ≥ 1.69` with leading coefficients `0.700` against `5.009`.
-/

namespace Principia.Common.TernaryGoldbach.MPA

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc

/-- `log y ≤ y/e` for `y > 0`. -/
theorem log_le_div_e (y : ℝ) (hy : 0 < y) : Real.log y ≤ 0.36788 * y := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  have he := Real.exp_one_gt_d9
  have h1 : y / Real.exp 1 ≤ 0.36788 * y := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  linarith

/-- `exp 2.5 ≤ 12.2`. -/
theorem exp_25_le : Real.exp 2.5 ≤ 12.2 := by
  have he := Real.exp_one_lt_d9
  have hh : Real.exp 0.5 * Real.exp 0.5 = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos 0.5
  have h05 : Real.exp 0.5 ≤ 1.65 := by nlinarith
  have e : Real.exp 2.5 = Real.exp 1 * Real.exp 1 * Real.exp 0.5 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [e]
  have h1 : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 := by
    have := Real.exp_pos 1
    nlinarith
  nlinarith [Real.exp_pos 1]

/-- **The `w`-variables**: for `u ≥ 8000`, `ℓ = log u ≥ 8.3`, `w = √√ℓ ≥ 1.69`, `w⁴ = ℓ`,
`log ℓ ≤ 1.4716w`. -/
theorem w_facts (u : ℝ) (hu : 8000 ≤ u) :
    8.3 ≤ Real.log u ∧ 1.69 ≤ Real.sqrt (Real.sqrt (Real.log u)) ∧
      Real.sqrt (Real.sqrt (Real.log u)) ^ 4 = Real.log u ∧
      Real.log (Real.log u) ≤ 1.4716 * Real.sqrt (Real.sqrt (Real.log u)) := by
  have hl2 := Real.log_two_gt_d9
  have hlu : 8.3 ≤ Real.log u := by
    have h1 : Real.log 4096 ≤ Real.log u := Real.log_le_log (by norm_num) (by linarith)
    have h2 : Real.log 4096 = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    linarith
  set ℓ := Real.log u with hℓ
  set w := Real.sqrt (Real.sqrt ℓ) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = Real.sqrt ℓ := Real.sq_sqrt (Real.sqrt_nonneg ℓ)
  have hw4 : w ^ 4 = ℓ := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2, Real.sq_sqrt (by linarith)]
  refine ⟨hlu, ?_, hw4, ?_⟩
  · by_contra h
    push Not at h
    have : w ^ 4 < 1.69 ^ 4 := pow_lt_pow_left₀ h hw0 (by norm_num)
    norm_num at this
    linarith
  · have hwpos : 0 < w := by
      rcases hw0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hw4; norm_num at hw4; linarith
    have e : Real.log ℓ = 4 * Real.log w := by
      rw [← hw4, Real.log_pow]; norm_num
    rw [e]
    have := log_le_div_e w hwpos
    linarith

/-- **`ϝ(u²/6) ≤ 2.2421 + 2.6314w`** for `u ≥ 8000` (`e^γ ≤ 1.7881`, `log log(u²/6) ≥ 2.5`,
`log log(u²/6) ≤ log 2ℓ`). -/
theorem bigF_le_w (u : ℝ) (hu : 8000 ≤ u) :
    MinSp.bigF (u ^ 2 / 6) ≤ 2.2421 + 2.6314 * Real.sqrt (Real.sqrt (Real.log u)) := by
  obtain ⟨hlu, hw, hw4, hll⟩ := w_facts u hu
  set ℓ := Real.log u
  set w := Real.sqrt (Real.sqrt ℓ)
  have hu0 : 0 < u := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  -- `log(u²/6) = 2ℓ − log 6`, between `14.5` and `2ℓ`
  have hr : Real.log (u ^ 2 / 6) = 2 * ℓ - Real.log 6 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
  have hl6 : Real.log 6 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hl6' : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hA : 14.5 ≤ Real.log (u ^ 2 / 6) := by rw [hr]; linarith
  have hB : Real.log (u ^ 2 / 6) ≤ 2 * ℓ := by rw [hr]; linarith
  have hC : 2.5 ≤ Real.log (Real.log (u ^ 2 / 6)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [exp_25_le]
  have hD : Real.log (Real.log (u ^ 2 / 6)) ≤ Real.log 2 + Real.log ℓ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hB
  have hg := MN.exp_gamma_le
  have hg0 := Real.exp_pos Real.eulerMascheroniConstant
  unfold MinSp.bigF
  have h1 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (u ^ 2 / 6)) ≤
      1.7881 * (0.6932 + 1.4716 * w) := by
    have hlog0 : 0 ≤ Real.log (Real.log (u ^ 2 / 6)) := by linarith
    calc Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (u ^ 2 / 6))
        ≤ 1.7881 * Real.log (Real.log (u ^ 2 / 6)) := mul_le_mul_of_nonneg_right hg hlog0
      _ ≤ 1.7881 * (0.6932 + 1.4716 * w) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
  have h2 : 2.50637 / Real.log (Real.log (u ^ 2 / 6)) ≤ 1.00255 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-- **`C_{x,t} ≤ log(1 + log(4t)/4)`** for `2 ≤ t ≤ x^{1/3}/3` (there `9x^{1/3}/(2.004t) ≥ e²`). -/
theorem cXT_le_log (x t : ℝ) (hx : 0 < x) (ht : 2 ≤ t) (htx : t ≤ x ^ ((1 : ℝ) / 3) / 3) :
    cXT x t ≤ Real.log (1 + Real.log (4 * t) / 4) := by
  have hc : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx _
  have ht0 : 0 < t := by linarith
  unfold cXT
  have hr : 13.47 ≤ 9 * x ^ ((1 : ℝ) / 3) / (2.004 * t) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [e]
    nlinarith [Real.exp_pos 1]
  have hD : 2 ≤ Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hN : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hu1 : Real.log (4 * t) / (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))) ≤
      Real.log (4 * t) / 4 := by
    apply div_le_div_of_nonneg_left hN (by norm_num)
    linarith
  have hu0 : 0 ≤ Real.log (4 * t) / (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))) :=
    div_nonneg hN (by linarith)
  exact Real.log_le_log (by linarith) (by linarith)

/-- **Term 1 of `eq:kraw`**, abstractly: `(R·log t + 0.811)/√(δ₀φ(q))·x ≤ A(w)·B(w)·1.73208u⁵`. -/
theorem term1_le (R lt D Y st sF w u : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 0.3992 * w + 0.41415)
    (hlt0 : 0 ≤ lt) (hlt : lt ≤ 2 * w ^ 4 - 1) (hY : 0 < Y) (hst : 0 < st) (hsF : 0 < sF)
    (hsFle : sF ≤ 1.7312 + 0.50605 * w) (hD : st / sF ≤ D) (hYst : Y / st ≤ 1.73208 * u ^ 5) :
    (R * lt + 0.811) / D * Y ≤ ((0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.811) *
      (1.7312 + 0.50605 * w) * (1.73208 * u ^ 5) := by
  have hA0 : 0 ≤ R * lt + 0.811 := by positivity
  have hAle : R * lt + 0.811 ≤ (0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.811 := by
    have := mul_le_mul hR hlt hlt0 (by linarith)
    linarith
  have hsd : 0 < st / sF := div_pos hst hsF
  have e1 : (R * lt + 0.811) / D * Y ≤ (R * lt + 0.811) / (st / sF) * Y :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hA0 hsd hD) hY.le
  have e2 : (R * lt + 0.811) / (st / sF) * Y = (R * lt + 0.811) * sF * (Y / st) := by
    field_simp
  rw [e2] at e1
  refine e1.trans ?_
  have hY0 : 0 ≤ Y / st := div_nonneg hY.le hst.le
  have hB0 : 0 ≤ (0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.811 := le_trans hA0 hAle
  exact mul_le_mul (mul_le_mul hAle hsFle hsF.le hB0) hYst hY0
    (mul_nonneg hB0 (le_trans hsF.le hsFle))

/-- **The degree-6 polynomial inequality** in `w ≥ 1.69`. -/
theorem poly_le (w : ℝ) (hw : 1.69 ≤ w) :
    ((0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.811) * (1.7312 + 0.50605 * w) * 1.73208 +
      2.5 * 1.73208 + 3.2 + 0.01 * w ^ 6 ≤ 0.3409 * 14.694 * w ^ 6 := by
  have hq2 : 4.4 ≤ 4.29 * w ^ 2 - 3.13 * w - 2.49 := by nlinarith [sq_nonneg (w - 1.69)]
  have hw0 : 0 ≤ w := by linarith
  have hw2 : 2.85 ≤ w ^ 2 := by nlinarith
  have hw4' : 8.1 ≤ w ^ 4 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ w ^ 4)
  nlinarith [pow_nonneg hw0 5, pow_nonneg hw0 6, pow_nonneg hw0 4, pow_nonneg hw0 2]

/-- **Term 3 of `eq:kraw`** fits in `9135w⁴u⁴ + 0.01w⁶u⁵`. -/
theorem term3_le (w u : ℝ) (hw : 1.69 ≤ w) (hu : 8000 ≤ u) :
    2 * (3.0001 * u ^ 4) *
      ((2.2421 + 2.6314 * w) * (6.5 * w ^ 4 + 80 / 9) + 27.3032 * w ^ 4 + 45.7575) ≤
      9135 * w ^ 4 * u ^ 4 + 0.01 * w ^ 6 * u ^ 5 := by
  have hwu : 13000 ≤ w * u := by nlinarith
  have hu4 : 0 < u ^ 4 := by positivity
  have hw5 : 102.7 * w ^ 5 ≤ 0.01 * w ^ 6 * u := by
    have := mul_le_mul_of_nonneg_left hwu (by positivity : (0 : ℝ) ≤ 0.01 * w ^ 5)
    nlinarith [pow_pos (by linarith : (0 : ℝ) < w) 5]
  have hw2 : 2.85 ≤ w ^ 2 := by nlinarith
  have hw4' : 8.1 ≤ w ^ 4 := by nlinarith
  have hlow' : 251.3 * w ^ 4 + 140.4 * w + 394.2 ≤ 9135 * w ^ 4 := by nlinarith
  have hsum : 2 * 3.0001 * ((2.2421 + 2.6314 * w) * (6.5 * w ^ 4 + 80 / 9) + 27.3032 * w ^ 4 +
      45.7575) ≤ 102.7 * w ^ 5 + 251.3 * w ^ 4 + 140.4 * w + 394.2 := by nlinarith
  have hA := mul_le_mul_of_nonneg_right hsum hu4.le
  have hB := mul_le_mul_of_nonneg_right hw5 hu4.le
  have hC := mul_le_mul_of_nonneg_right hlow' hu4.le
  have e : 0.01 * w ^ 6 * u ^ 5 = 0.01 * w ^ 6 * u * u ^ 4 := by ring
  rw [e]
  nlinarith

/-- **`L_{δ,q} ≤ F(6.5w⁴ + 80/9) + 27.3032w⁴ + 45.7575`** given `log t ≤ 2w⁴ − 1`. -/
theorem ltosca_le (d : ℝ) (q : ℕ) (w : ℝ) (hd : 2 ≤ d) (hq : 1 ≤ q)
    (hlt : Real.log (d * q) ≤ 2 * w ^ 4 - 1) (hqφ : (q : ℝ) / Nat.totient q ≤ 2.2421 + 2.6314 * w) :
    lToscaAt 45.7575 d q ≤
      (2.2421 + 2.6314 * w) * (6.5 * w ^ 4 + 80 / 9) + 27.3032 * w ^ 4 + 45.7575 ∧
      0 ≤ lToscaAt 45.7575 d q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd0 : 0 < d := by linarith
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hlt' : Real.log (d * q) = Real.log d + Real.log q := Real.log_mul hd0.ne' (by linarith)
  have e1 : Real.log (d ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log d + 13 / 4 * Real.log q := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hd0 _).ne' (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow hd0, Real.log_rpow (by linarith)]
  have e2 : Real.log ((q : ℝ) ^ (13.6516 : ℝ) * d ^ (1.7984 : ℝ)) =
      13.6516 * Real.log q + 1.7984 * Real.log d := by
    rw [Real.log_mul (Real.rpow_pos_of_pos (by linarith) _).ne' (Real.rpow_pos_of_pos hd0 _).ne',
      Real.log_rpow (by linarith), Real.log_rpow hd0]
  unfold lToscaAt
  rw [e1, e2]
  have e : (7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9) / ((Nat.totient q : ℝ) / q) =
      (7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9) * ((q : ℝ) / Nat.totient q) := by
    field_simp
  rw [e]
  have hq0 : 0 ≤ (q : ℝ) / Nat.totient q := div_nonneg (by linarith) hφ0.le
  have hX : 7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9 ≤ 6.5 * w ^ 4 + 80 / 9 := by
    nlinarith
  have hX0 : 0 ≤ 7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9 := by positivity
  have hM := mul_le_mul hX hqφ hq0 (le_trans hX0 hX)
  constructor
  · nlinarith
  · have := mul_nonneg hX0 hq0
    nlinarith

/-- **The first-choice geometry of the coexisting branch**: `t = δ₀q ∈ [u²/3 − 1/4, u²/3]`,
`x/√t ≤ 1.73208u⁵`, `x/t ≤ 3.0001u⁴`, `log t ≤ 2w⁴ − 1`. -/
theorem t_facts (δ : ℝ) (q : ℕ) (u : ℝ) (hu : 8000 ≤ u) (hq : 1 ≤ q)
    (hy : (q : ℝ) ≤ u ^ 2 / 6) (hdq : |δ| * q ≤ 4 / 3 * u ^ 2)
    (hlow : 4 / 3 * u ^ 2 - 1 ≤ |δ| * q) :
    2 ≤ OC.dz δ * q ∧ OC.dz δ * q ≤ u ^ 2 / 3 ∧
      u ^ 6 / Real.sqrt (OC.dz δ * q) ≤ 1.73208 * u ^ 5 ∧
      u ^ 6 / (OC.dz δ * q) ≤ 3.0001 * u ^ 4 ∧
      Real.log (OC.dz δ * q) ≤ 2 * Real.log u - 1 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  have hu0 : 0 < u := by linarith
  have ht2 : 2 ≤ OC.dz δ * q := by nlinarith
  have htx : OC.dz δ * q ≤ u ^ 2 / 3 := by
    have := dz_q_le δ (u ^ 2) q hdq hy
    linarith
  have htl : u ^ 2 / 3 - 1 / 4 ≤ OC.dz δ * q := by
    have h1 : |δ| / 4 ≤ OC.dz δ := le_max_right _ _
    have h2 : |δ| / 4 * q ≤ OC.dz δ * q := mul_le_mul_of_nonneg_right h1 (by linarith)
    nlinarith
  have hu2 : 64000000 ≤ u ^ 2 := by nlinarith
  have hst : u / 1.73208 ≤ Real.sqrt (OC.dz δ * q) := by
    rw [Real.le_sqrt (by positivity) (by linarith), div_pow, div_le_iff₀ (by norm_num)]
    nlinarith
  have hsqt0 : 0 < Real.sqrt (OC.dz δ * q) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨ht2, htx, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hsqt0]
    have := mul_le_mul_of_nonneg_left hst (by positivity : (0 : ℝ) ≤ 1.73208 * u ^ 5)
    have e : 1.73208 * u ^ 5 * (u / 1.73208) = u ^ 6 := by field_simp
    linarith
  · rw [div_le_iff₀ (by linarith)]
    have hu4 : 0 ≤ u ^ 4 := by positivity
    have h1 := mul_le_mul_of_nonneg_left htl hu4
    have h2 : 0.75 * u ^ 4 ≤ 0.0000334 * (u ^ 4 * u ^ 2) := by nlinarith
    have e : u ^ 6 = u ^ 4 * u ^ 2 := by ring
    rw [e]
    nlinarith
  · have hl3 : 1 ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have h1 : Real.log (OC.dz δ * q) ≤ Real.log (u ^ 2 / 3) := Real.log_le_log (by linarith) htx
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1
    linarith

/-- **`C_{x,t} ≤ log ℓ ≤ 1.4716w`** on the coexisting branch. -/
theorem cXT_le_w (Y t u : ℝ) (hY0 : 0 < Y) (e13 : Y ^ ((1 : ℝ) / 3) = u ^ 2) (hu : 8000 ≤ u)
    (ht2 : 2 ≤ t) (htx : t ≤ u ^ 2 / 3) :
    cXT Y t ≤ 1.4716 * Real.sqrt (Real.sqrt (Real.log u)) := by
  obtain ⟨hlu, -, -, hll⟩ := w_facts u hu
  have hu0 : 0 < u := by linarith
  refine (cXT_le_log Y t hY0 ht2 (by rw [e13]; exact htx)).trans ?_
  have h4t : Real.log (4 * t) ≤ Real.log 2 + 2 * Real.log u := by
    have h1 : Real.log (4 * t) ≤ Real.log (2 * u ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul (x := 2) (y := u ^ 2) (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1; linarith
  have hl2 := Real.log_two_lt_d9
  have h1 : 1 + Real.log (4 * t) / 4 ≤ Real.log u := by linarith
  have hpos : 0 < 1 + Real.log (4 * t) / 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * t by linarith); linarith
  exact (Real.log_le_log hpos h1).trans hll

/-- `(log x)^{3/2} ≥ 14.694w⁶` for `log x = 6w⁴`. -/
theorem logY_pow_ge (L w : ℝ) (hL : L = 6 * w ^ 4) :
    14.694 * w ^ 6 ≤ L ^ ((3 : ℝ) / 2) := by
  have hs6 : 2.449 ≤ Real.sqrt 6 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [log_pow_three_halves _ (by rw [hL]; positivity), hL]
  have e : Real.sqrt (6 * w ^ 4) = Real.sqrt 6 * w ^ 2 := by
    rw [Real.sqrt_mul (by norm_num), show w ^ 4 = (w ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [e]
  have := mul_le_mul_of_nonneg_left hs6 (by positivity : (0 : ℝ) ≤ 6 * w ^ 4 * w ^ 2)
  nlinarith

/-- `√F ≤ 1.7312 + 0.50605w` from `F ≤ 2.2421 + 2.6314w` (AM-GM at `2.6`). -/
theorem sqrtF_le (F w : ℝ) (hF0 : 0 ≤ F) (hF : F ≤ 2.2421 + 2.6314 * w) :
    Real.sqrt F ≤ 1.7312 + 0.50605 * w := by
  have h := Real.sqrt_nonneg F
  have hsq := Real.sq_sqrt hF0
  nlinarith [sq_nonneg (Real.sqrt F - 2.6)]

/-- `√t/√F ≤ √(δ₀φ(q))` from `q/φ(q) ≤ F`. -/
theorem den_ge (d : ℝ) (q : ℕ) (F : ℝ) (hd : 0 < d) (hq : 1 ≤ q) (hF0 : 0 < F)
    (hF : (q : ℝ) / Nat.totient q ≤ F) :
    Real.sqrt (d * q) / Real.sqrt F ≤ Real.sqrt (d * Nat.totient q) := by
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [← Real.sqrt_div (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hF0]
  have h1 : (q : ℝ) ≤ F * Nat.totient q := by
    rw [div_le_iff₀ hφ0] at hF; linarith
  have := mul_le_mul_of_nonneg_left h1 hd.le
  nlinarith

/-- **`CoexistArith`, PROVED.** -/
theorem coexistArith : CoexistArith := by
  intro Y hY δ q hq hy hdq hlow hF
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, e56, e13, eY, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hlu, hw, hw4, -⟩ := w_facts _ hu
  have hFw := bigF_le_w _ hu
  rw [e13] at hy hdq hlow hF
  obtain ⟨ht2, htx, hYst, hYt, hlogt⟩ :=
    t_facts δ q (Y ^ ((1 : ℝ) / 6)) hu hq hy hdq hlow
  have hC := cXT_le_w Y _ _ hY0 e13 hu ht2 htx
  have hC0 : 0 ≤ cXT Y (OC.dz δ * q) := (cXT_bounds Y _ hY0 ht2 (by rw [e13]; exact htx)).1
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set w := Real.sqrt (Real.sqrt (Real.log u)) with hw_def
  set t := OC.dz δ * q with ht_def
  have hwlt : Real.log t ≤ 2 * w ^ 4 - 1 := by rw [hw4]; exact hlogt
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hR : MinSp.rR Y t ≤ 0.3992 * w + 0.41415 := by
    have e : MinSp.rR Y t = 0.27125 * cXT Y t + 0.41415 := rfl
    rw [e]; linarith
  have hR0 : 0 ≤ MinSp.rR Y t := by
    have e : MinSp.rR Y t = 0.27125 * cXT Y t + 0.41415 := rfl
    rw [e]; linarith
  have hF0 : 0 < MinSp.bigF (u ^ 2 / 6) := by
    have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    exact lt_of_lt_of_le (div_pos hqR hφ0) hF
  have hqφ : (q : ℝ) / Nat.totient q ≤ 2.2421 + 2.6314 * w := hF.trans hFw
  have hd0 : 0 < OC.dz δ := by linarith [dz_ge δ]
  have hT1 := term1_le (MinSp.rR Y t) (Real.log t) (Real.sqrt (OC.dz δ * Nat.totient q)) Y
    (Real.sqrt t) (Real.sqrt (MinSp.bigF (u ^ 2 / 6))) w u hR0 hR hlogt0 hwlt hY0
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hF0)
    (sqrtF_le _ w hF0.le hFw) (den_ge _ q _ hd0 hq hF0 hF) (by rw [eY]; exact hYst)
  obtain ⟨hLT, hLT0⟩ := ltosca_le (OC.dz δ) q w (dz_ge δ) hq hwlt hqφ
  have hT3 : 2 * Y / t * lToscaAt 45.7575 (OC.dz δ) q ≤
      2 * (3.0001 * u ^ 4) *
        ((2.2421 + 2.6314 * w) * (6.5 * w ^ 4 + 80 / 9) + 27.3032 * w ^ 4 + 45.7575) := by
    rw [mul_div_assoc]
    exact mul_le_mul (by rw [eY]; linarith) hLT hLT0 (by positivity)
  have hT2 : 2.5 * Y / Real.sqrt t ≤ 2.5 * (1.73208 * u ^ 5) := by
    rw [mul_div_assoc, eY]; linarith
  have hL : Real.log Y = 6 * w ^ 4 := by rw [eL, hw4]
  have hLp := logY_pow_ge (Real.log Y) w hL
  have hpoly := poly_le w hw
  have hT3' := term3_le w u hw hu
  have hP : 0 ≤ u ^ 5 := by positivity
  have hpolyu := mul_le_mul_of_nonneg_left hpoly hP
  have hRHS : 0.3409 * u ^ 5 * (14.694 * w ^ 6) ≤ 0.3409 * u ^ 5 * Real.log Y ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hLp (by positivity)
  unfold krawAt
  rw [e56, e23, hL]
  rw [hL] at hRHS
  linarith [hT1, hT2, hT3, hT3', hpolyu, hRHS]

end Principia.Common.TernaryGoldbach.MPA
