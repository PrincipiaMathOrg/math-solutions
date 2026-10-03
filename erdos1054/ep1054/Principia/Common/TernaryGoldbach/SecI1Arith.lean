/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinGen
import Principia.Common.TernaryGoldbach.MNumProofs

set_option autoImplicit false

/-!
# `MPG.SecI1Arith` PROVED — `S_{I,1}` at the second choice

`secI1Arith : MPG.SecI1Arith`: at `U = 500√6x^{1/3}`, `Q = x/U`, for every admissible `(q, δ)`
(`q > y` or `|δ|q > 8y`) and μ-sums obeying `eq:grara`, `eq:ronsard`, `eq:meproz` at modulus `2q`,
the corrected `lem:bostb1` bound is at most `2.4719x^{2/3}log x + 0.00289x^{2/3}(log x)²`.

With `u = x^{1/6}`, `λ = log u`, `S = 500√6`:
* **prefactors** (`pref`): `x/2q·min(1, c₀/(πδ)²) ≤ 3u⁴` and
  `x/2q·(2 - log 4)·min(1, k'/δ²) ≤ 1.842u⁴` — from `q > y` directly, and from `|δ| > 8`,
  `qδ² ≥ (32/3)u²` in the other case;
* **the μ-sums**: `|s₁| ≤ log(x/U) + 1.00303·2q/φ(2q)`, `log(x/U) = log Q = 4λ - log S ≤ 4λ - 7`,
  `2q/φ(2q) ≤ 2ϝ(Q) ≤ 2(3.6544 + 0.15003 log Q)` (`MN.bigF_le`);
* **`eq:kuche2`** (`kuche2_sec`): the `q`-terms at `q ≤ Q`,
  `max(1, log(c₀e³q²/(4π|η'|₁x))) ≤ 2λ - 11`, the rest `O(λu²)`, `O(λu³)`;
* the total is `u⁴(0.0346λ² + 15.442λ - 3.349)` against `u⁴(0.10404λ² + 14.8314λ)`, whose
  difference has negative discriminant.

Scoped worst ratio of the left side to the right: `0.910` (`scratchpad/trig/sec_check.py`).
-/

namespace Principia.Common.TernaryGoldbach.MPS1

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPI1

/-! ## (1) Constants -/

/-- `log(500√6) ≥ 7`. -/
theorem logS_ge : 7 ≤ Real.log (500 * Real.sqrt 6) := by
  obtain ⟨hs1, -⟩ := sqrt6_bounds
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have e : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : Real.exp 1 ^ 7 ≤ 2.7182818286 ^ 7 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 7
  nlinarith

/-- `log u ≤ 8 + u/8000` for `u ≥ 8000`. -/
theorem lam_le (u : ℝ) (hu : 8000 ≤ u) : Real.log u ≤ 8 + u / 8000 := by
  have hu0 : 0 < u := by linarith
  have h1 : Real.log 8000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have e : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : 2.7182818283 ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he.le 9
    nlinarith
  have h2 := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num : (0 : ℝ) < 8000))
  rw [Real.log_div hu0.ne' (by norm_num)] at h2
  linarith

/-- `0.6137 ≤ 2 - log 4 ≤ 0.6138`. -/
theorem two_sub_log4 : 0.6137 ≤ 2 - Real.log 4 ∧ 2 - Real.log 4 ≤ 0.6138 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have a := Real.log_two_lt_d9
  have b := Real.log_two_gt_d9
  constructor <;> linarith

/-- `c₀/π² ≤ 3.1938` and `96 log 2/π² ≤ 6.7422`. -/
theorem cpi_bounds : c0 / Real.pi ^ 2 ≤ 3.1938 ∧ 96 * Real.log 2 / Real.pi ^ 2 ≤ 6.7422 := by
  obtain ⟨p1, -⟩ := pi_sq_bounds
  have a := Real.log_two_lt_d9
  constructor
  · rw [div_le_iff₀ (by linarith)]; unfold c0; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- `min(1, c/δ²) ≤ 1`. -/
theorem cap_le_one (c δ : ℝ) (hc : 0 < c) : capM c δ ≤ 1 := by
  unfold capM; rw [div_le_one (lt_of_lt_of_le hc (le_max_left _ _))]; exact le_max_left _ _

/-- `0 ≤ min(1, c/δ²)`. -/
theorem cap_nonneg (c δ : ℝ) (hc : 0 < c) : 0 ≤ capM c δ := by
  unfold capM; exact div_nonneg hc.le (le_trans hc.le (le_max_left _ _))

/-- `min(1, c/δ²) ≤ c/δ²` for `c ≤ δ²`. -/
theorem cap_le_div (c δ : ℝ) (hδ : c ≤ δ ^ 2) : capM c δ ≤ c / δ ^ 2 := by
  unfold capM; rw [max_eq_right hδ]

/-! ## (2) The prefactors -/

/-- `c₀/π² > 0` and `k' = 96 log 2/π²/(2 - log 4) > 0`. -/
theorem caps_pos : 0 < c0 / Real.pi ^ 2 ∧
    0 < 96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4) := by
  obtain ⟨hl1, -⟩ := two_sub_log4
  have := Real.log_two_gt_d9
  exact ⟨by unfold c0; positivity, div_pos (div_pos (by linarith) (by positivity)) (by linarith)⟩

/-- The prefactors when `q > y`: `x/2q ≤ 3u⁴`. -/
theorem pref_big (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y)
    (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ ≤ 3 * (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧
      Y / (2 * q) * ((2 - Real.log 4) *
        capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) ≤
        1.842 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hqR : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hqy
  obtain ⟨hl1, hl2⟩ := two_sub_log4
  obtain ⟨hc0, hk0⟩ := caps_pos
  have hY2 : 0 ≤ Y / (2 * q) := by positivity
  have hpre : Y / (2 * q) ≤ 3 * u ^ 4 := by
    rw [div_le_iff₀ (by positivity), eY]
    nlinarith [mul_lt_mul_of_pos_left hqy (by positivity : (0 : ℝ) < u ^ 4)]
  constructor
  · calc Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ ≤ Y / (2 * q) * 1 :=
          mul_le_mul_of_nonneg_left (cap_le_one _ δ hc0) hY2
      _ ≤ 3 * u ^ 4 := by linarith
  · have h1 : (2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ ≤
        0.6138 := by
      have := cap_le_one _ δ hk0
      have := cap_nonneg _ δ hk0
      nlinarith
    calc Y / (2 * q) * ((2 - Real.log 4) *
          capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) ≤
          Y / (2 * q) * 0.6138 := mul_le_mul_of_nonneg_left h1 hY2
      _ ≤ 1.842 * u ^ 4 := by nlinarith

/-- `x/2q·(c/δ²) ≤ (3c/64)u⁴` when `qδ² ≥ (32/3)u²`. -/
theorem pref_div (Y δ c : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hc : 0 ≤ c)
    (hqd : 32 / 3 * (Y ^ ((1 : ℝ) / 6)) ^ 2 ≤ q * δ ^ 2) :
    Y / (2 * q) * (c / δ ^ 2) ≤ 3 * c / 64 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd0 : 0 < δ ^ 2 := by
    have : 0 < q * δ ^ 2 := lt_of_lt_of_le (by positivity) hqd
    exact pos_of_mul_pos_right this hqR.le
  rw [div_mul_div_comm, div_le_iff₀ (by positivity), eY]
  have e : 3 * c / 64 * u ^ 4 * (2 * q * δ ^ 2) = 3 * c / 32 * u ^ 4 * (q * δ ^ 2) := by ring
  rw [e]
  have h := mul_le_mul_of_nonneg_left hqd (by positivity : (0 : ℝ) ≤ 3 * c / 32 * u ^ 4)
  have e2 : 3 * c / 32 * u ^ 4 * (32 / 3 * u ^ 2) = c * u ^ 6 := by ring
  linarith

/-- The prefactors when `q ≤ y` and `|δ|q > (4/3)u²`. -/
theorem pref_small (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hqy : (q : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6)
    (hdq : 4 / 3 * (Y ^ ((1 : ℝ) / 6)) ^ 2 < |δ| * q) :
    Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ ≤ 3 * (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧
      Y / (2 * q) * ((2 - Real.log 4) *
        capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) ≤
        1.842 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hl1, hl2⟩ := two_sub_log4
  obtain ⟨hc1, hc2⟩ := cpi_bounds
  obtain ⟨hc0, hk0⟩ := caps_pos
  have hY2 : 0 ≤ Y / (2 * q) := by positivity
  have h8 : 8 ≤ |δ| := by
    by_contra hc
    have h' : |δ| < 8 := not_le.mp hc
    have : |δ| * q < 8 * q := mul_lt_mul_of_pos_right h' hqR
    nlinarith
  have hd2 : 64 ≤ δ ^ 2 := by rw [← sq_abs δ]; nlinarith
  have hqd : 32 / 3 * u ^ 2 ≤ q * δ ^ 2 := by
    rw [← sq_abs δ]
    have := mul_le_mul hdq.le h8 (by norm_num) (by positivity)
    nlinarith
  constructor
  · have hcap := cap_le_div (c0 / Real.pi ^ 2) δ (by linarith)
    calc Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ ≤ Y / (2 * q) * (c0 / Real.pi ^ 2 / δ ^ 2) :=
          mul_le_mul_of_nonneg_left hcap hY2
      _ ≤ 3 * (c0 / Real.pi ^ 2) / 64 * u ^ 4 := pref_div Y δ _ q hY hq hc0.le hqd
      _ ≤ 3 * u ^ 4 := by nlinarith [pow_pos hu0 4]
  · have hk1 : 96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4) ≤ δ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hcap := cap_le_div _ δ hk1
    have e : (2 - Real.log 4) * (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4) / δ ^ 2) =
        96 * Real.log 2 / Real.pi ^ 2 / δ ^ 2 := by
      field_simp
    have h1 : (2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ ≤
        96 * Real.log 2 / Real.pi ^ 2 / δ ^ 2 := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hcap (by linarith)
    have h96 : 0 ≤ 96 * Real.log 2 / Real.pi ^ 2 := by
      have := Real.log_two_gt_d9; positivity
    calc Y / (2 * q) * ((2 - Real.log 4) *
          capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) ≤
          Y / (2 * q) * (96 * Real.log 2 / Real.pi ^ 2 / δ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hY2
      _ ≤ 3 * (96 * Real.log 2 / Real.pi ^ 2) / 64 * u ^ 4 := pref_div Y δ _ q hY hq h96 hqd
      _ ≤ 1.842 * u ^ 4 := by nlinarith [pow_pos hu0 4]

/-- **The prefactors**: `x/2q·min(1, c₀/(πδ)²) ≤ 3u⁴` and
`x/2q·(2 - log 4)·min(1, k'/δ²) ≤ 1.842u⁴` at every second-choice `(q, δ)`. -/
theorem pref (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hA : Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) :
    Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ ≤ 3 * (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧
      Y / (2 * q) * ((2 - Real.log 4) *
        capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) ≤
        1.842 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  rw [e13] at hA
  by_cases hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q
  · exact pref_big Y δ q hY hqy
  · rcases hA with h | h
    · exact absurd h hqy
    · exact pref_small Y δ q hY hq (not_lt.mp hqy) h

/-! ## (3) `log Q` and `ϝ(Q)` -/

/-- `log(x/U) = log Q = 4λ - log S ≤ 4λ - 7`, `log Q ≥ 0`, `Q ≥ 150000`. -/
theorem logQ_facts (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    Real.log (q2 Y) ≤ 4 * Real.log (Y ^ ((1 : ℝ) / 6)) - 7 ∧ 0 ≤ Real.log (q2 Y) ∧
      150000 ≤ q2 Y ∧ q2 Y ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.5 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, hq2⟩ := sec_eqs Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  obtain ⟨hs1, hs2⟩ := sqrt6_bounds
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have hL := logS_ge
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hQ : 150000 ≤ q2 Y := by
    rw [hq2, le_div_iff₀ hS]; nlinarith
  refine ⟨?_, Real.log_nonneg (by linarith), hQ, ?_⟩
  · rw [hq2, Real.log_div (by positivity) hS.ne', Real.log_pow]; push_cast; linarith
  · rw [hq2]; exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

/-- `ϝ(Q) ≤ 2.60419 + 0.60012λ`. -/
theorem bigF_Q (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    MinSp.bigF (q2 Y) ≤ 2.60419 + 0.60012 * Real.log (Y ^ ((1 : ℝ) / 6)) := by
  obtain ⟨h1, -, h3, -⟩ := logQ_facts Y hY
  have := MN.bigF_le (q2 Y) h3
  linarith

/-! ## (4) The lower-order terms -/

/-- `c₁ = 1 + |η'|₁U/x ≤ 1.000001` at `D = U = 500√6x^{1/3}`. -/
theorem c1_sec (Y : ℝ) (hY : 3.4e23 ≤ Y) : c1 Y (u2 Y) ≤ 1.000001 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu2, -, -⟩ := sec_eqs Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  obtain ⟨-, hs2⟩ := sqrt6_bounds
  obtain ⟨-, he2⟩ := eta1_bounds
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  unfold c1
  rw [hu2, eY]
  have he0 : 0 < eta1 := by unfold eta1; have := Real.log_two_gt_d9; positivity
  rw [show eta1 * (500 * Real.sqrt 6 * u ^ 2) / u ^ 6 =
    eta1 * (500 * Real.sqrt 6) / u ^ 4 by field_simp]
  have : eta1 * (500 * Real.sqrt 6) / u ^ 4 ≤ 0.000001 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **The `O*` term**: `errI1 ≤ 0.001u⁴` at the second choice. -/
theorem err_sec (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) :
    errI1 Y q (u2 Y) ≤ 0.001 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, eL⟩ := rpow_facts Y hY0
  obtain ⟨hu2, -, hq2⟩ := sec_eqs Y hY0
  obtain ⟨hlQ, hlQ0, -, -⟩ := logQ_facts Y hY
  have hu := u_ge Y hY
  have hlam := lam_le _ hu
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  obtain ⟨-, hs2⟩ := sqrt6_bounds
  obtain ⟨p1, p2⟩ := pi_sq_bounds
  obtain ⟨hse, -, hie⟩ := e_facts
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hU : 0 < u2 Y := by unfold u2; positivity
  have hu2' : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  -- `log(√e·x/U) = 1/2 + log Q`
  have hlog : Real.log (Real.sqrt (Real.exp 1) * Y / u2 Y) = 1 / 2 + Real.log (q2 Y) := by
    have e : Real.sqrt (Real.exp 1) * Y / u2 Y = Real.sqrt (Real.exp 1) * q2 Y := by
      unfold q2; ring
    rw [e, Real.log_mul (by positivity) (by unfold q2; positivity), Real.log_sqrt
      (Real.exp_pos 1).le, Real.log_exp]
  -- `U²/(4qx) ≤ S²/(4u²) ≤ 0.00587`
  have hfrac : u2 Y ^ 2 / (4 * q * Y) ≤ 0.00587 := by
    rw [div_le_iff₀ (by positivity), hu2, eY]
    have h66 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
    have e : (500 * Real.sqrt 6 * u ^ 2) ^ 2 = 1500000 * u ^ 4 := by
      rw [show (500 * Real.sqrt 6 * u ^ 2) ^ 2 = 250000 * (Real.sqrt 6 * Real.sqrt 6) * u ^ 4
        by ring, h66]; ring
    rw [e]
    have : (1 : ℝ) * u ^ 6 ≤ q * u ^ 6 := mul_le_mul_of_nonneg_right hqR (by positivity)
    have h6 : u ^ 6 = u ^ 2 * u ^ 4 := by ring
    nlinarith [mul_le_mul_of_nonneg_right hu2' (pow_pos hu0 4).le, pow_pos hu0 4]
  have hcoef : c0 * (1 / 2 - 2 / Real.pi ^ 2) ≤ 9.3731 := by
    have : 2 / Real.pi ^ 2 ≥ 0.20264 := by rw [ge_iff_le, le_div_iff₀ (by linarith)]; nlinarith
    unfold c0; nlinarith
  have hcoef0 : 0 ≤ c0 * (1 / 2 - 2 / Real.pi ^ 2) := by
    have : 2 / Real.pi ^ 2 ≤ 0.2027 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    unfold c0; nlinarith
  have hin : u2 Y ^ 2 / (4 * q * Y) * Real.log (Real.sqrt (Real.exp 1) * Y / u2 Y) +
      1 / Real.exp 1 ≤ 0.00587 * (1 / 2 + 4 * (8 + u / 8000)) + 0.36788 := by
    rw [hlog]
    have h0 : 0 ≤ u2 Y ^ 2 / (4 * q * Y) := by positivity
    have h1 : 1 / 2 + Real.log (q2 Y) ≤ 1 / 2 + 4 * (8 + u / 8000) := by linarith
    have := mul_le_mul hfrac h1 (by linarith) (by norm_num)
    linarith
  unfold errI1
  calc c0 * (1 / 2 - 2 / Real.pi ^ 2) *
        (u2 Y ^ 2 / (4 * q * Y) * Real.log (Real.sqrt (Real.exp 1) * Y / u2 Y) + 1 / Real.exp 1)
      ≤ 9.3731 * (0.00587 * (1 / 2 + 4 * (8 + u / 8000)) + 0.36788) :=
        mul_le_mul hcoef hin (by
          have : 0 ≤ u2 Y ^ 2 / (4 * q * Y) * Real.log (Real.sqrt (Real.exp 1) * Y / u2 Y) := by
            rw [hlog]; positivity
          have := Real.exp_pos 1
          positivity) (by norm_num)
    _ ≤ 0.001 * u ^ 4 := by
        have hu3 : (8000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
        nlinarith [pow_pos hu0 3]

/-! ## (5) `eq:kuche2` at the second choice -/

/-- The second-choice data used by every `eq:kuche2` piece. -/
theorem kdata (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    0 < u2 Y ∧ u2 Y ≤ 1225 * (Y ^ ((1 : ℝ) / 6)) ^ 2 ∧ u2 Y * q2 Y = Y ∧
      8.3 ≤ Real.log (Y ^ ((1 : ℝ) / 6)) ∧
      Real.log (Y ^ ((1 : ℝ) / 6)) ≤ 8 + Y ^ ((1 : ℝ) / 6) / 8000 ∧
      (8000 : ℝ) ^ 2 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hu2, -, -⟩ := sec_eqs Y hY0
  have hu := u_ge Y hY
  obtain ⟨-, hs2⟩ := sqrt6_bounds
  have hU : 0 < u2 Y := by unfold u2; positivity
  refine ⟨hU, ?_, ?_, (MPA.w_facts _ hu).1, lam_le _ hu, pow_le_pow_left₀ (by norm_num) hu 2⟩
  · rw [hu2]; nlinarith [pow_pos (show (0 : ℝ) < Y ^ ((1 : ℝ) / 6) by linarith) 2]
  · unfold q2; field_simp

/-- `λu² ≤ u⁴/6.4·10⁷·8 + u⁴/8000·(1/8000)`-type absorption: `c·λ·u² ≤ c·(8/6.4e7 + 1/6.4e7)·u⁴`
for `u ≥ 8000`, `λ ≤ 8 + u/8000`. -/
theorem lam_u2 (u lam c : ℝ) (hu : 8000 ≤ u) (hlam : lam ≤ 8 + u / 8000) (hc : 0 ≤ c) :
    c * lam * u ^ 2 ≤ c * (1.5e-7 * u ^ 4) := by
  have hu0 : 0 < u := by linarith
  have hu2 : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  have h1 : lam * u ^ 2 ≤ 1.5e-7 * u ^ 4 := by
    have a : lam * u ^ 2 ≤ (8 + u / 8000) * u ^ 2 := mul_le_mul_of_nonneg_right hlam (by positivity)
    have b : (8 + u / 8000) * u ^ 2 ≤ 1.5e-7 * u ^ 4 := by
      have e4 : u ^ 4 = u ^ 2 * u ^ 2 := by ring
      have hc3 : u * u ^ 2 ≤ u ^ 2 * u ^ 2 / 8000 := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right hu (pow_pos hu0 2).le]
      have hc2 : (8000 : ℝ) ^ 2 * u ^ 2 ≤ u ^ 2 * u ^ 2 :=
        mul_le_mul_of_nonneg_right hu2 (pow_pos hu0 2).le
      have e : (8 + u / 8000) * u ^ 2 = 8 * u ^ 2 + u * u ^ 2 / 8000 := by ring
      rw [e, e4]
      nlinarith [pow_pos hu0 2]
    linarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 hc

/-- **(K1)** `k·U·log(ex/U) ≤ 0.0025u⁴`. -/
theorem k1_sec (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * u2 Y *
      Real.log (Real.exp 1 * Y / u2 Y) ≤ 0.0027 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hU, hU2, hUQ, hl1, hl2, hu2'⟩ := kdata Y hY
  obtain ⟨hlQ, hlQ0, -, -⟩ := logQ_facts Y hY
  have hu := u_ge Y hY
  have hk := k_coef _ (c1_sec Y hY)
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi := by positivity
  have hlog : Real.log (Real.exp 1 * Y / u2 Y) = 1 + Real.log (q2 Y) := by
    rw [show Real.exp 1 * Y / u2 Y = Real.exp 1 * q2 Y by unfold q2; ring,
      Real.log_mul (Real.exp_pos 1).ne' (by unfold q2; positivity), Real.log_exp]
  rw [hlog]
  have h1 : 1 + Real.log (q2 Y) ≤ 4 * lam := by linarith
  have h2 : 0 ≤ 1 + Real.log (q2 Y) := by linarith
  calc 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * u2 Y * (1 + Real.log (q2 Y))
      ≤ 3.5743 * (1225 * u ^ 2) * (4 * lam) :=
        mul_le_mul (mul_le_mul hk hU2 hU.le (by norm_num)) h1 h2 (by positivity)
    _ = 17514.07 * lam * u ^ 2 := by ring
    _ ≤ 17514.07 * (1.5e-7 * u ^ 4) := lam_u2 u lam _ hu hl2 (by norm_num)
    _ ≤ 0.0027 * u ^ 4 := by nlinarith [pow_pos (show (0 : ℝ) < u by linarith) 4]

/-- `log(1/c₂) ≤ 0.4894` and `0 < log(q/c₂) ≤ 4λ - 6.5` for `1 ≤ q ≤ Q`. -/
theorem logqc2 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    Real.log (1 / c2) ≤ 0.4895 ∧ 0 < Real.log (q / c2) ∧
      Real.log (q / c2) ≤ 4 * Real.log (Y ^ ((1 : ℝ) / 6)) - 6.5 := by
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨hlQ, -, -, -⟩ := logQ_facts Y hY
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 : 0 < c2 := by linarith
  have h1c : Real.log (1 / c2) ≤ 0.4895 := by
    have := Real.log_le_sub_one_of_pos (one_div_pos.mpr hc0)
    have h2 : 1 / c2 ≤ 1.4895 := by rw [div_le_iff₀ hc0]; nlinarith
    linarith
  refine ⟨h1c, Real.log_pos (by rw [lt_div_iff₀ hc0]; linarith), ?_⟩
  have e : Real.log (q / c2) = Real.log q + Real.log (1 / c2) := by
    rw [div_eq_mul_one_div, Real.log_mul (by linarith) (by positivity)]
  have hq' : Real.log q ≤ Real.log (q2 Y) := Real.log_le_log (by linarith) hQ
  linarith

/-- **(K2)** `(3c₁/2)(x/q)log⁺(U/(c₂x/q))log(q/c₂) ≤ 0.00076u⁴`: the `log⁺` vanishes unless
`q > c₂x/U`, and then `x/q < U/c₂`, `log⁺ ≤ log(1/c₂)` (`UQ = x`). -/
theorem k2_sec (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    3 * c1 Y (u2 Y) / 2 * (Y / q) * logp (u2 Y / (c2 * Y / q)) * Real.log (q / c2) ≤
      0.00081 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hU, hU2, hUQ, hl1, hl2, hu2'⟩ := kdata Y hY
  obtain ⟨h1c, hlq0, hlq⟩ := logqc2 Y q hY hq hQ
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have hu := u_ge Y hY
  have hc1 := c1_sec Y hY
  have hc1' : 1 ≤ c1 Y (u2 Y) := by
    unfold c1; have := eta1_bounds.1; have : 0 ≤ eta1 * u2 Y / Y := by positivity
    linarith
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 : 0 < c2 := by linarith
  have hR : 0 ≤ 0.00081 * u ^ 4 := by positivity
  have hYp : 0 < c2 * Y := by positivity
  have eqv : u2 Y / (c2 * Y / q) = u2 Y * q / (c2 * Y) := div_div_eq_mul_div _ _ _
  by_cases hle : u2 Y / (c2 * Y / q) ≤ 1
  · have : logp (u2 Y / (c2 * Y / q)) = 0 := by
      unfold logp; exact max_eq_right (Real.log_nonpos (by positivity) hle)
    rw [this, mul_zero, zero_mul]; exact hR
  · have hgt : 1 < u2 Y / (c2 * Y / q) := not_le.mp hle
    rw [eqv] at hgt
    have hlp : logp (u2 Y / (c2 * Y / q)) ≤ 0.4895 := by
      unfold logp
      refine max_le ?_ (by norm_num)
      have hle1 : u2 Y / (c2 * Y / q) ≤ 1 / c2 := by
        rw [eqv, div_le_div_iff₀ hYp hc0]
        have : u2 Y * q ≤ u2 Y * q2 Y := mul_le_mul_of_nonneg_left hQ hU.le
        nlinarith
      exact (Real.log_le_log (by rw [eqv]; linarith) hle1).trans h1c
    have hlp0 : 0 ≤ logp (u2 Y / (c2 * Y / q)) := le_max_right _ _
    have hYq : Y / q ≤ u2 Y / c2 := by
      rw [lt_div_iff₀ hYp] at hgt
      rw [div_le_div_iff₀ hqR hc0]
      nlinarith
    have hU' : u2 Y / c2 ≤ 1824.6 * u ^ 2 := by
      rw [div_le_iff₀ hc0]; nlinarith [pow_pos (show (0 : ℝ) < u by linarith) 2]
    have hl0 : 0 ≤ lam * u ^ 2 := mul_nonneg (by linarith) (sq_nonneg u)
    calc 3 * c1 Y (u2 Y) / 2 * (Y / q) * logp (u2 Y / (c2 * Y / q)) * Real.log (q / c2)
        ≤ 3 * 1.000001 / 2 * (1824.6 * u ^ 2) * 0.4895 * (4 * lam) := by
          apply mul_le_mul _ (by linarith) hlq0.le (by positivity)
          apply mul_le_mul _ hlp hlp0 (by positivity)
          apply mul_le_mul (by linarith) (hYq.trans hU') (by positivity) (by positivity)
      _ ≤ 5360 * lam * u ^ 2 := by nlinarith
      _ ≤ 5360 * (1.5e-7 * u ^ 4) := lam_u2 u lam _ hu hl2 (by norm_num)
      _ ≤ 0.00081 * u ^ 4 := by nlinarith [pow_pos (show (0 : ℝ) < u by linarith) 4]

/-- `max(1, log(c₀e³q²/(4π|η'|₁x))) ≤ 2λ - 11` for `1 ≤ q ≤ Q`. -/
theorem k3_max_sec (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) ≤
      2 * Real.log (Y ^ ((1 : ℝ) / 6)) - 11 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨-, -, hq2⟩ := sec_eqs Y hY0
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hu := u_ge Y hY
  have hL := logS_ge
  obtain ⟨he1, -⟩ := eta1_bounds
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpi := Real.pi_gt_d2
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  refine max_le (by linarith) ?_
  have hX : c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y) ≤
      Real.exp 3 * (u ^ 2 / (500 * Real.sqrt 6) ^ 2) := by
    have hq2' : (q : ℝ) ^ 2 ≤ (u ^ 4 / (500 * Real.sqrt 6)) ^ 2 := by
      rw [← hq2]; exact pow_le_pow_left₀ (by linarith) hQ 2
    rw [div_le_iff₀ (by positivity), eY]
    have hc : c0 ≤ 4 * Real.pi * eta1 := by unfold c0; nlinarith
    have e : Real.exp 3 * (u ^ 2 / (500 * Real.sqrt 6) ^ 2) * (4 * Real.pi * eta1 * u ^ 6) =
        Real.exp 3 * (4 * Real.pi * eta1) * ((u ^ 4 / (500 * Real.sqrt 6)) ^ 2) := by
      field_simp
    rw [e]
    have h3 := Real.exp_pos 3
    have := mul_le_mul hc hq2' (by positivity) (by positivity)
    nlinarith
  have hpos : 0 < c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y) := by
    unfold c0; have : 0 < eta1 := by linarith
    positivity
  calc Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))
      ≤ Real.log (Real.exp 3 * (u ^ 2 / (500 * Real.sqrt 6) ^ 2)) := Real.log_le_log hpos hX
    _ = 3 + 2 * Real.log u - 2 * Real.log (500 * Real.sqrt 6) := by
        rw [Real.log_mul (Real.exp_pos 3).ne' (by positivity), Real.log_exp,
          Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        push_cast; ring
    _ ≤ 2 * Real.log u - 11 := by linarith

/-- `q·log⁺(2U/q) ≤ 0.73576·U`. -/
theorem qlogp_le (U : ℝ) (q : ℕ) (hU : 0 < U) (hq : 1 ≤ q) :
    (q : ℝ) * logp (U / (q / 2)) ≤ 0.73576 * U := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold logp
  rcases le_total (Real.log (U / (q / 2))) 0 with h | h
  · rw [max_eq_right h, mul_zero]; positivity
  · rw [max_eq_left h]
    have := MPA.log_le_div_e (U / (q / 2)) (by positivity)
    have e : (q : ℝ) * (0.36788 * (U / (q / 2))) = 0.73576 * U := by field_simp; ring
    calc (q : ℝ) * Real.log (U / (q / 2)) ≤ q * (0.36788 * (U / (q / 2))) :=
          mul_le_mul_of_nonneg_left this hqR.le
      _ = 0.73576 * U := e

/-- The polynomial behind the `q`-terms: `0.0172983λ(2λ - 11) + 0.0050559(4λ - 6.5)`. -/
theorem k3_poly (lam u : ℝ) (hl : 8.3 ≤ lam) (hu4 : 0 ≤ u ^ 4) :
    3.5303 * (2 * lam - 11) * (6 * lam) * (u ^ 4 / 1224.5) +
      3.5743 * 1.73206 * (4 * lam - 6.5) * (u ^ 4 / 1224.5) ≤
      u ^ 4 * (0.0346 * lam ^ 2 - 0.1902 * lam + 0.02023 * lam - 0.03286) := by
  have e1 : 3.5303 * (2 * lam - 11) * (6 * lam) * (u ^ 4 / 1224.5) +
      3.5743 * 1.73206 * (4 * lam - 6.5) * (u ^ 4 / 1224.5) =
      u ^ 4 * (3.5303 * 12 / 1224.5 * lam ^ 2 - 3.5303 * 66 / 1224.5 * lam +
        3.5743 * 1.73206 * 4 / 1224.5 * lam - 3.5743 * 1.73206 * 6.5 / 1224.5) := by ring
  have e2 : 3.5303 * 12 / 1224.5 * lam ^ 2 - 3.5303 * 66 / 1224.5 * lam +
      3.5743 * 1.73206 * 4 / 1224.5 * lam - 3.5743 * 1.73206 * 6.5 / 1224.5 ≤
      0.0346 * lam ^ 2 - 0.1902 * lam + 0.02023 * lam - 0.03286 := by
    nlinarith [sq_nonneg lam]
  rw [e1]
  exact mul_le_mul_of_nonneg_left e2 hu4

/-- **(K3, max term)** `(2|η'|₁/π)·max(1, …)·log x·q ≤ 3.5303(2λ - 11)(6λ)(u⁴/1224.5)`. -/
theorem k3_t1 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    2 * eta1 / Real.pi *
        max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
        Real.log Y * q ≤
      3.5303 * (2 * Real.log (Y ^ ((1 : ℝ) / 6)) - 11) * (6 * Real.log (Y ^ ((1 : ℝ) / 6))) *
        ((Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.5) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  obtain ⟨-, -, -, hQu⟩ := logQ_facts Y hY
  have hmax := k3_max_sec Y q hY hq hQ
  obtain ⟨-, he2⟩ := eta1_bounds
  have hpi := Real.pi_gt_d6
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have heta : 2 * eta1 / Real.pi ≤ 3.5303 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmax0 : 0 ≤ max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) :=
    le_trans zero_le_one (le_max_left _ _)
  rw [eL]
  apply mul_le_mul _ (hQ.trans hQu) (by linarith)
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
  exact mul_le_mul (mul_le_mul heta hmax hmax0 (by norm_num)) le_rfl (by linarith)
    (mul_nonneg (by norm_num) (by linarith))

/-- **(K3, `√3` term)** `k√3·log(q/c₂)·q ≤ 3.5743·1.73206(4λ - 6.5)(u⁴/1224.5)`. -/
theorem k3_t2 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * Real.sqrt 3 * Real.log (q / c2) * q ≤
      3.5743 * 1.73206 * (4 * Real.log (Y ^ ((1 : ℝ) / 6)) - 6.5) *
        ((Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.5) := by
  obtain ⟨-, -, -, hQu⟩ := logQ_facts Y hY
  obtain ⟨-, hlq0, hlq⟩ := logqc2 Y q hY hq hQ
  have hk := k_coef _ (c1_sec Y hY)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h3 : Real.sqrt 3 ≤ 1.73206 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi := by positivity
  apply mul_le_mul _ (hQ.trans hQu) (by linarith) (mul_nonneg (by norm_num) (by linarith))
  exact mul_le_mul (mul_le_mul hk h3 (Real.sqrt_nonneg _) (by norm_num)) hlq hlq0.le
    (by positivity)

/-- **(K3, `log⁺` term)** `k·(log⁺(2U/q)/2)·log(q/c₂)·q ≤ 0.001u⁴`. -/
theorem k3_t3 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * (logp (u2 Y / (q / 2)) / 2) *
      Real.log (q / c2) * q ≤ 0.001 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  obtain ⟨hU, hU2, -, hl1, hl2, -⟩ := kdata Y hY
  obtain ⟨-, hlq0, hlq⟩ := logqc2 Y q hY hq hQ
  have hk := k_coef _ (c1_sec Y hY)
  have hql := qlogp_le (u2 Y) q hU hq
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi := by positivity
  have hlp0 : 0 ≤ logp (u2 Y / (q / 2)) := le_max_right _ _
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have e : 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * (logp (u2 Y / (q / 2)) / 2) *
      Real.log (q / c2) * q = 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi / 2 *
      ((q : ℝ) * logp (u2 Y / (q / 2))) * Real.log (q / c2) := by ring
  rw [e]
  have hql' : (q : ℝ) * logp (u2 Y / (q / 2)) ≤ 0.73576 * (1225 * u ^ 2) := by
    have := mul_le_mul_of_nonneg_left hU2 (by norm_num : (0 : ℝ) ≤ 0.73576)
    linarith
  have t : 2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi / 2 *
      ((q : ℝ) * logp (u2 Y / (q / 2))) * Real.log (q / c2) ≤
      3.5743 / 2 * (0.73576 * (1225 * u ^ 2)) * (4 * lam) := by
    apply mul_le_mul _ (by linarith) hlq0.le (by positivity)
    exact mul_le_mul (by linarith) hql' (mul_nonneg hqR hlp0) (by positivity)
  have t' : 3.5743 / 2 * (0.73576 * (1225 * u ^ 2)) * (4 * lam) ≤ 0.001 * u ^ 4 := by
    have h := lam_u2 u lam (3.5743 / 2 * 0.73576 * 1225 * 4) hu hl2 (by norm_num)
    have e2 : 3.5743 / 2 * (0.73576 * (1225 * u ^ 2)) * (4 * lam) =
        3.5743 / 2 * 0.73576 * 1225 * 4 * lam * u ^ 2 := by ring
    rw [e2]
    have hu4 : 0 ≤ u ^ 4 := by positivity
    linarith
  linarith

/-- **(K3)** the `q`-terms of `eq:kuche2` at `q ≤ Q`. -/
theorem k3_sec (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    (2 * eta1 / Real.pi *
          max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
          Real.log Y +
        2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi *
          (Real.sqrt 3 + logp (u2 Y / (q / 2)) / 2) * Real.log (q / c2)) * q ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 *
        (0.0346 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 - 0.1902 * Real.log (Y ^ ((1 : ℝ) / 6)) +
          0.02023 * Real.log (Y ^ ((1 : ℝ) / 6)) - 0.03286 + 0.001) := by
  have t1 := k3_t1 Y q hY hq hQ
  have t2 := k3_t2 Y q hY hq hQ
  have t3 := k3_t3 Y q hY hq hQ
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hp := k3_poly (Real.log (Y ^ ((1 : ℝ) / 6))) (Y ^ ((1 : ℝ) / 6)) hl1 (by positivity)
  have e : (2 * eta1 / Real.pi *
          max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
          Real.log Y +
        2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi *
          (Real.sqrt 3 + logp (u2 Y / (q / 2)) / 2) * Real.log (q / c2)) * q =
      2 * eta1 / Real.pi *
        max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
        Real.log Y * q +
      2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * Real.sqrt 3 * Real.log (q / c2) * q +
      2 * Real.sqrt (c0 * c1 Y (u2 Y)) / Real.pi * (logp (u2 Y / (q / 2)) / 2) *
        Real.log (q / c2) * q := by ring
  rw [e]
  have e2 : (Y ^ ((1 : ℝ) / 6)) ^ 4 *
      (0.0346 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 - 0.1902 * Real.log (Y ^ ((1 : ℝ) / 6)) +
        0.02023 * Real.log (Y ^ ((1 : ℝ) / 6)) - 0.03286 + 0.001) =
      (Y ^ ((1 : ℝ) / 6)) ^ 4 *
        (0.0346 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 - 0.1902 * Real.log (Y ^ ((1 : ℝ) / 6)) +
          0.02023 * Real.log (Y ^ ((1 : ℝ) / 6)) - 0.03286) + 0.001 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
    ring
  rw [e2]
  linarith

/-- **`eq:kuche2` at the second choice**: `≤ u⁴(0.0346λ² - 0.16997λ + 0.1363)`. -/
theorem kuche2_sec (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    kuche2 Y q (u2 Y) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 *
      (0.0346 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 - 0.16997 * Real.log (Y ^ ((1 : ℝ) / 6)) +
        0.1363) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have k1 := k1_sec Y hY
  have k2 := k2_sec Y q hY hq hQ
  have k3 := k3_sec Y q hY hq hQ
  have k45 := k45_le Y (c1 Y (u2 Y)) hY (c1_sec Y hY)
  obtain ⟨-, -, -, hl1, hl2, -⟩ := kdata Y hY
  have hu := u_ge Y hY
  have hsq : Y ^ ((1 : ℝ) / 2) = (Y ^ ((1 : ℝ) / 6)) ^ 3 := by
    rw [← Real.sqrt_eq_rpow, sqrt_eq_u3 Y hY0]
  rw [hsq] at k45
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have k45' : u ^ 3 * (136.9 * lam + 84.3) ≤ 0.1646 * u ^ 4 := by
    have hu3 : (8000 : ℝ) * u ^ 3 ≤ u ^ 4 := by
      have := mul_le_mul_of_nonneg_right hu (pow_pos hu0 3).le
      nlinarith
    have hlu : u ^ 3 * lam ≤ u ^ 3 * (8 + u / 8000) := mul_le_mul_of_nonneg_left hl2 (by positivity)
    have e : u ^ 3 * (8 + u / 8000) = 8 * u ^ 3 + u ^ 4 / 8000 := by ring
    nlinarith [pow_pos hu0 3, pow_pos hu0 4]
  have g : u ^ 4 * (0.0346 * lam ^ 2 - 0.1902 * lam + 0.02023 * lam - 0.03286 + 0.001) +
      0.0027 * u ^ 4 + 0.00081 * u ^ 4 + 0.1646 * u ^ 4 ≤
      u ^ 4 * (0.0346 * lam ^ 2 - 0.16997 * lam + 0.1363) := by
    have e : u ^ 4 * (0.0346 * lam ^ 2 - 0.1902 * lam + 0.02023 * lam - 0.03286 + 0.001) +
        0.0027 * u ^ 4 + 0.00081 * u ^ 4 + 0.1646 * u ^ 4 =
        u ^ 4 * (0.0346 * lam ^ 2 - 0.16997 * lam + 0.13625) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold kuche2
  linarith

/-! ## (6) Assembly -/

/-- The final comparison: `u⁴(0.0346λ² + 15.4421λ - 3.3482) ≤ u⁴(14.8314λ + 0.10404λ²)`. -/
theorem final_ineq (u lam A B E K : ℝ) (hu4 : 0 ≤ u ^ 4)
    (hA : A ≤ u ^ 4 * (15.6117 * lam - 5.3275)) (hB : B ≤ 1.842 * u ^ 4)
    (hE : E ≤ 0.001 * u ^ 4) (hK : K ≤ u ^ 4 * (0.0346 * lam ^ 2 - 0.16997 * lam + 0.1363)) :
    A + B + E + K ≤ 2.4719 * u ^ 4 * (6 * lam) + 0.00289 * u ^ 4 * (6 * lam) ^ 2 := by
  have hq : 0 ≤ 0.06944 * lam ^ 2 - 0.61033 * lam + 3.3482 := by nlinarith [sq_nonneg (lam - 4.4)]
  nlinarith [mul_nonneg hu4 hq]

/-- **`MPG.SecI1Arith`, PROVED.** -/
theorem secI1Arith : SecI1Arith := by
  intro Y hY δ q hq hQ hdq hA hF s0 s1 hs0 hron hmep
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨pf1, pf2⟩ := pref Y δ q hY hq hA
  obtain ⟨hlQ, hlQ0, -, -⟩ := logQ_facts Y hY
  have hFQ := bigF_Q Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hR2 := R2_le q hq
  have hE := err_sec Y q hY hq
  have hK := kuche2_sec Y q hY hq hQ
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu4 : 0 ≤ u ^ 4 := by positivity
  -- `|s₁| ≤ log Q + 1.00303·2q/φ(2q)`
  have hl : Real.log (Y / u2 Y) = Real.log (q2 Y) := rfl
  have hs1 : |s1| ≤ 5.20388 * lam - 1.77586 := by
    have h1 : |s1| ≤ |s1 - Real.log (Y / u2 Y) * s0| + |Real.log (Y / u2 Y) * s0| := by
      have := abs_add_le (s1 - Real.log (Y / u2 Y) * s0) (Real.log (Y / u2 Y) * s0)
      rwa [sub_add_cancel] at this
    have h2 : |Real.log (Y / u2 Y) * s0| ≤ Real.log (q2 Y) := by
      rw [abs_mul, hl, abs_of_nonneg hlQ0]
      exact mul_le_of_le_one_right hlQ0 hs0
    have h3 : ((2 * q : ℕ) : ℝ) / Nat.totient (2 * q) ≤ 2 * (2.60419 + 0.60012 * lam) := by
      linarith
    nlinarith
  have hcap1 : 0 ≤ Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ := by
    have := (caps_pos).1
    have : 0 ≤ capM (c0 / Real.pi ^ 2) δ := cap_nonneg _ δ this
    positivity
  have hAb : Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ * |s1| ≤
      u ^ 4 * (15.6117 * lam - 5.3275) := by
    have := mul_le_mul pf1 hs1 (abs_nonneg _) (by positivity)
    nlinarith
  have hBb : Y / (2 * q) *
      ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) * |s0| ≤
      1.842 * u ^ 4 := by
    have h0 : 0 ≤ Y / (2 * q) *
        ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) := by
      have := (two_sub_log4).1
      have := cap_nonneg _ δ (caps_pos).2
      have : (0 : ℝ) < q := by exact_mod_cast hq
      positivity
    calc Y / (2 * q) *
          ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) * |s0|
        ≤ Y / (2 * q) *
          ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) * 1 :=
          mul_le_mul_of_nonneg_left hs0 h0
      _ ≤ 1.842 * u ^ 4 := by linarith
  rw [e23, eL]
  exact final_ineq u lam _ _ _ _ hu4 hAb hBb hE hK

/-! ## (7) The Main Theorem on nine links -/

/-- **`MPc.SecI1At` from `lem:bostb1` alone** (plus the cited μ-bounds and `RS62Thm15`). -/
theorem secI1At_of_gen (hb : Bostb1Eta2) (hg : Grara) (hr : Ronsard) (hm : Meproz)
    (h15 : GS.RS62Thm15) : SecI1At :=
  secI1At_of hb hg hr hm h15 secI1Arith

/-- **`OP.MinMainP 0.811 45.7575` from nine open links**: `MPI2.minMainP_of_ten` with `Bostb1At`
and `SecI1At` both supplied by the one generic `lem:bostb1` link `Bostb1Eta2`. Application
only. -/
theorem minMainP_of_nine (hb1 : Bostb1Eta2) (hgr : Grara) (hro : Ronsard) (hme : Meproz)
    (hb2 : Bosta2Eta2) (hv1 : Vinland1At) (her : EriksagaAt) (hs2 : SecI2At) (hs3 : SecIIAt)
    (h15 : GS.RS62Thm15) : OP.MinMainP 0.811 45.7575 :=
  MPI2.minMainP_of_ten (bostb1At_of_gen hb1) hgr hro hme hb2 hv1 her
    (secI1At_of_gen hb1 hgr hro hme h15) hs2 hs3 h15

end Principia.Common.TernaryGoldbach.MPS1
