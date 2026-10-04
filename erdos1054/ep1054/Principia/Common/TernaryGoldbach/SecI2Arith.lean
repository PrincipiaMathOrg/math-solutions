/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SecI1Arith

set_option autoImplicit false

/-!
# `MPG.SecI2Arith` PROVED — `S_{I,2}` at the second choice

`secI2Arith : MPG.SecI2Arith`: at `U = 500√6x^{1/3}`, `V = x^{1/3}/3`, `Q = x/U`, for every
admissible `(q, δ)` (`q > y` or `|δ|q > 8y`, `|δ|q ≤ U`) the `lem:bogus` bound (`eq:cupcake3`
plus `eq:piececake` for `|δ| ≤ 1/2c₂`, plus `eq:tvorog` at `ε = 0.01` otherwise) is at most
`1230.9x^{2/3}log x + 0.0006406x^{2/3}(log x)²`. Hence `secI2At_of_gen : BogusEta2 → SecI2At`.

With `u = x^{1/6}`, `λ = log u`, `S = 500√6` (so `UV = (S/3)u⁴`, `Q = u⁴/S`, `2UV/Q = 10⁶`):
* `eq:cupcake3` (`cup_le`): `≤ u⁴(18λ - 23.88)`, its main term by `MPS1.pref`;
* `eq:piececake` (`pc_le`, `|δ| ≤ 1/2c₂` forces `q > y`, `q_gt_y`): the `D log D` term dominates
  (`pc_P1`); `q·log⁺(2UV/q) ≤ Q log(2UV/Q)` (`tlog_le`), `(x/q)log(q/q₀) ≤ (x/y)log(y/q₀)`
  (`xlog_le`); the `q·max(1, …)·log(q/2)` term carries the `λ²` coefficient
  `0.0230591 ≤ 0.0230616` (`pc_P3`) — the one tight constant of the file;
* `eq:tvorog` (`tvo_le`): `K = x/(|δ|q) ∈ [Q, 8.058u⁴]` (`K_bounds`, from `dq_lower`),
  `(K + 1)log((K + 1)/√2)` is increasing (`tlogc_mono`), `(K + 1)log(A/K)` is bounded at the top
  of the range (`klog_le`).

Totals (`fin1`, `fin2`): `u⁴(0.0230591λ² + 6022.61λ + 8313.88)` and `u⁴(6287.7λ + 7918.32)`
against `u⁴(0.0230616λ² + 7385.4λ)`; both differences are positive for `λ ≥ 8.3`.
Scoped worst ratio: `0.97` at `x = 3.4·10²³` (`scratchpad/trig/sec_check.py`).
-/

namespace Principia.Common.TernaryGoldbach.MPS2

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPI1
  Principia.Common.TernaryGoldbach.MPS1

/-! ## (1) Constants -/

/-- `1224.7445 ≤ S = 500√6 ≤ 1224.745` and `S² = 1500000`. -/
theorem S_bounds : 1224.7445 ≤ 500 * Real.sqrt 6 ∧ 500 * Real.sqrt 6 ≤ 1224.745 ∧
    (500 * Real.sqrt 6) ^ 2 = 1500000 := by
  have h66 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, by rw [mul_pow, h66]; norm_num⟩
  · have h2 : (2.449489 : ℝ) ≤ Real.sqrt 6 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  · have : Real.sqrt 6 ≤ 2.44949 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith

/-- `log x ≤ k log 2 + (x/2ᵏ - 1)`. -/
theorem log_le_pow2 (x : ℝ) (k : ℕ) (hx : 0 < x) :
    Real.log x ≤ k * Real.log 2 + (x / 2 ^ k - 1) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (by positivity : (0 : ℝ) < 2 ^ k))
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h
  linarith

/-- `k log 2 + (1 - 2ᵏ/x) ≤ log x`. -/
theorem log_ge_pow2 (x : ℝ) (k : ℕ) (hx : 0 < x) :
    k * Real.log 2 + (1 - 2 ^ k / x) ≤ Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx (by positivity : (0 : ℝ) < 2 ^ k))
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow, inv_div] at h
  linarith

/-- `√2 ≥ 1.41421`. -/
theorem sqrt2_ge : (1.41421 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

/-- The logarithms of the constants. -/
theorem logs_S :
    Real.log (500 * Real.sqrt 6 / 3) ≤ 6.04 ∧ 8 ≤ Real.log (3 * (500 * Real.sqrt 6)) ∧
      7.78 ≤ Real.log (2 * (500 * Real.sqrt 6)) ∧ Real.log 1000000 ≤ 13.82 := by
  obtain ⟨hS1, hS2, -⟩ := S_bounds
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := log_le_pow2 (500 * Real.sqrt 6 / 3) 9 (by positivity)
    norm_num at this ⊢; nlinarith
  · have := log_ge_pow2 (3 * (500 * Real.sqrt 6)) 11 (by positivity)
    have h : (2 : ℝ) ^ 11 / (3 * (500 * Real.sqrt 6)) ≤ 2048 / 3674 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num; nlinarith
    push_cast at this; nlinarith
  · have := log_ge_pow2 (2 * (500 * Real.sqrt 6)) 11 (by positivity)
    have h : (2 : ℝ) ^ 11 / (2 * (500 * Real.sqrt 6)) ≤ 2048 / 2449.489 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num; nlinarith
    push_cast at this; nlinarith
  · have := log_le_pow2 1000000 20 (by norm_num)
    norm_num at this ⊢; nlinarith

/-- `log(S/3) ≥ 5.9`. -/
theorem logS3_ge : 5.9 ≤ Real.log (500 * Real.sqrt 6 / 3) := by
  obtain ⟨hS1, -, -⟩ := S_bounds
  have l2 := Real.log_two_gt_d9
  have := log_ge_pow2 (500 * Real.sqrt 6 / 3) 8 (by positivity)
  have h : (2 : ℝ) ^ 8 / (500 * Real.sqrt 6 / 3) ≤ 256 / 408.24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num; nlinarith
  push_cast at this; nlinarith

/-- `log(8.059/√2) ≤ 1.8` and `0 ≤ log(S/24.174) ≤ 3.96`. -/
theorem logs_K : Real.log (8.059 / Real.sqrt 2) ≤ 1.8 ∧
    0 ≤ Real.log (500 * Real.sqrt 6 / 24.174) ∧ Real.log (500 * Real.sqrt 6 / 24.174) ≤ 3.96 := by
  obtain ⟨hS1, hS2, -⟩ := S_bounds
  have hs2 := sqrt2_ge
  have l2 := Real.log_two_lt_d9
  refine ⟨?_, Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith), ?_⟩
  · have := log_le_pow2 (8.059 / Real.sqrt 2) 3 (by positivity)
    have h : 8.059 / Real.sqrt 2 / 2 ^ 3 ≤ 0.7124 := by
      rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
    push_cast at this; nlinarith
  · have := log_le_pow2 (500 * Real.sqrt 6 / 24.174) 6 (by positivity)
    have h : 500 * Real.sqrt 6 / 24.174 / 2 ^ 6 ≤ 0.7917 := by
      rw [div_div, div_le_iff₀ (by norm_num)]; nlinarith
    push_cast at this; nlinarith

/-- The logarithms involving `c₂`. -/
theorem logs_c2 :
    Real.log (500 * Real.sqrt 6 / (18 * c2)) ≤ 4.65 ∧
      1 ≤ Real.log (500 * Real.sqrt 6 / (18 * c2)) ∧ Real.log (6 * c2) ≤ 1.4 := by
  obtain ⟨hS1, hS2, -⟩ := S_bounds
  obtain ⟨hc1, hc2⟩ := c2_bounds
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  refine ⟨?_, ?_, ?_⟩
  · have := log_le_pow2 (500 * Real.sqrt 6 / (18 * c2)) 7 (by positivity)
    have h : 500 * Real.sqrt 6 / (18 * c2) ≤ 101.35 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    push_cast at this; nlinarith
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have h : (2.72 : ℝ) ≤ 500 * Real.sqrt 6 / (18 * c2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  · have := log_le_pow2 (6 * c2) 2 (by positivity)
    push_cast at this; nlinarith

/-- `2|η'|₁/π ≤ 3.53018`. -/
theorem eta_pi : 2 * eta1 / Real.pi ≤ 3.53018 := by
  have hpi := Real.pi_gt_d6
  have l2 := Real.log_two_lt_d9
  rw [div_le_iff₀ (by linarith)]
  unfold eta1; nlinarith

/-- `2√(c₀c)/π ≤ 3.5744` for `c ≤ 1.00002`. -/
theorem kb_coef (c : ℝ) (hc : c ≤ 1.00002) : 2 * Real.sqrt (c0 * c) / Real.pi ≤ 3.5744 := by
  have p1 := Real.pi_gt_d6
  have hs : Real.sqrt (c0 * c) ≤ 5.6145 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold c0; nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `0 ≤ (2c₂)^{3/2} ≤ 1.5564`. -/
theorem rpow32 : 0 ≤ (2 * c2) ^ ((3 : ℝ) / 2) ∧ (2 * c2) ^ ((3 : ℝ) / 2) ≤ 1.5564 := by
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have h0 : (0 : ℝ) ≤ 2 * c2 := by linarith
  rw [log_pow_three_halves (2 * c2) h0]
  have hs : Real.sqrt (2 * c2) ≤ 1.15889 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hs0 := Real.sqrt_nonneg (2 * c2)
  refine ⟨mul_nonneg h0 hs0, ?_⟩
  have := mul_le_mul (show 2 * c2 ≤ 1.343 by linarith) hs hs0 (by norm_num)
  linarith

/-! ## (2) The second choice in `u`; monotonicity lemmas -/

/-- The data: `UV = (S/3)u⁴`, `Q ≤ u⁴/1224.7445`, `c₁ ≤ 1.00002`, and the `λ`-absorptions. -/
theorem sdata (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    u2 Y * v2 Y = 500 * Real.sqrt 6 / 3 * (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧
      q2 Y ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.7445 ∧
      c1b Y (u2 Y * v2 Y) ≤ 1.00002 ∧
      Real.log (Y ^ ((1 : ℝ) / 6)) * (Y ^ ((1 : ℝ) / 6)) ^ 3 ≤
        0.001125 * (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧
      Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 * (Y ^ ((1 : ℝ) / 6)) ^ 3 ≤
        0.0243 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu2, hv2, hq2⟩ := sec_eqs Y hY0
  obtain ⟨hS1, hS2, hSS⟩ := S_bounds
  have hu := u_ge Y hY
  have hlam := lam_le _ hu
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have hUV : u2 Y * v2 Y = 500 * Real.sqrt 6 / 3 * u ^ 4 := by rw [hu2, hv2]; ring
  refine ⟨hUV, ?_, ?_, ?_, ?_⟩
  · rw [hq2]; exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hS1
  · unfold c1b
    rw [hUV, eY]
    obtain ⟨-, he2⟩ := eta1_bounds
    have he0 : 0 < eta1 := by unfold eta1; have := Real.log_two_gt_d9; positivity
    have hu2' : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
    have e : eta1 * (500 * Real.sqrt 6 / 3 * u ^ 4) / (2 * u ^ 6) =
        eta1 * (500 * Real.sqrt 6) / (6 * u ^ 2) := by field_simp; ring
    rw [e]
    have : eta1 * (500 * Real.sqrt 6) / (6 * u ^ 2) ≤ 0.00002 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · have hl3 : Real.log u * u ^ 3 ≤ (8 + u / 8000) * u ^ 3 :=
      mul_le_mul_of_nonneg_right hlam (by positivity)
    have hu3 : (8000 : ℝ) * u ^ 3 ≤ u ^ 4 := by
      have := mul_le_mul_of_nonneg_right hu (pow_pos hu0 3).le
      nlinarith
    nlinarith [pow_pos hu0 3, pow_pos hu0 4]
  · -- `λ = 4 log w ≤ 1.47152w`, `w = √√u`, `w² = √u ≥ 89.4`
    set w := Real.sqrt (Real.sqrt u) with hw
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hw2 : w ^ 2 = Real.sqrt u := Real.sq_sqrt (Real.sqrt_nonneg u)
    have hw4 : w ^ 4 = u := by
      rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2, Real.sq_sqrt hu0.le]
    have hsu : (89.4 : ℝ) ≤ Real.sqrt u := by
      rw [Real.le_sqrt (by norm_num) hu0.le]; linarith
    have hwpos : 0 < w := by
      rcases hw0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hw2; nlinarith
    have hlw : Real.log u = 4 * Real.log w := by rw [← hw4, Real.log_pow]; norm_num
    have hlw2 := MPA.log_le_div_e w hwpos
    have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hlam1 : Real.log u ≤ 1.47152 * w := by rw [hlw]; linarith
    have hlam2 : Real.log u ^ 2 ≤ 2.1654 * w ^ 2 := by nlinarith
    have hwu : w ^ 2 * 89.4 ≤ u := by
      rw [← hw4, show w ^ 4 = w ^ 2 * w ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (hw2 ▸ hsu) (sq_nonneg w)
    have h1 : Real.log u ^ 2 * u ^ 3 ≤ 2.1654 * w ^ 2 * u ^ 3 :=
      mul_le_mul_of_nonneg_right hlam2 (by positivity)
    have h2 : w ^ 2 * u ^ 3 ≤ u / 89.4 * u ^ 3 :=
      mul_le_mul_of_nonneg_right (by rw [le_div_iff₀ (by norm_num)]; linarith) (by positivity)
    nlinarith [pow_pos hu0 4]

/-- **`q·log⁺(A/q) ≤ Q log(A/Q)`** for `0 < q ≤ Q`, `log(A/Q) ≥ 1`. -/
theorem tlog_le (A Q t : ℝ) (hA : 0 < A) (ht : 0 < t) (htQ : t ≤ Q)
    (hAQ : 1 ≤ Real.log (A / Q)) : t * logp (A / t) ≤ Q * Real.log (A / Q) := by
  have hQ : 0 < Q := lt_of_lt_of_le ht htQ
  unfold logp
  rcases le_total (Real.log (A / t)) 0 with h | h
  · rw [max_eq_right h, mul_zero]; nlinarith
  · rw [max_eq_left h]
    have e : Real.log (A / t) = Real.log (A / Q) + Real.log (Q / t) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h2 := Real.log_le_sub_one_of_pos (div_pos hQ ht)
    rw [e]
    have h3 : t * Real.log (Q / t) ≤ Q - t := by
      have := mul_le_mul_of_nonneg_left h2 ht.le
      have e2 : t * (Q / t - 1) = Q - t := by field_simp
      linarith
    nlinarith

/-- **`(x/q)log(q/q₀) ≤ (x/y)log(y/q₀)`** for `y ≤ q`, `log(y/q₀) ≥ 1`. -/
theorem xlog_le (x y q q0 : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hyq : y ≤ q) (hq0 : 0 < q0)
    (hl : 1 ≤ Real.log (y / q0)) : x / q * Real.log (q / q0) ≤ x / y * Real.log (y / q0) := by
  have hq : 0 < q := lt_of_lt_of_le hy hyq
  have e : Real.log (q / q0) = Real.log (y / q0) + Real.log (q / y) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have h2 := Real.log_le_sub_one_of_pos (div_pos hq hy)
  rw [e]
  have h3 : x / q * (Real.log (y / q0) + Real.log (q / y)) ≤
      x / q * (Real.log (y / q0) - 1) + x / y := by
    have h4 : x / q * Real.log (q / y) ≤ x / q * (q / y - 1) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e2 : x / q * (q / y - 1) = x / y - x / q := by field_simp
    linarith
  have h5 : x / q * (Real.log (y / q0) - 1) ≤ x / y * (Real.log (y / q0) - 1) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hx hy hyq) (by linarith)
  linarith

/-- **`(K + 1)log(A/K) ≤ (K₀ + 1)log(A/K₀) - 1 + K₀/K`** for `0 < K ≤ K₀`, `log(A/K₀) ≥ 1`. -/
theorem klog_le (A K K0 : ℝ) (hK : 0 < K) (hKK : K ≤ K0) (hl : 1 ≤ Real.log (A / K0))
    (hA : 0 < A) :
    (K + 1) * Real.log (A / K) ≤ (K0 + 1) * Real.log (A / K0) - 1 + K0 / K := by
  have hK0 : 0 < K0 := lt_of_lt_of_le hK hKK
  have e : Real.log (A / K) = Real.log (A / K0) + Real.log (K0 / K) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have h2 := Real.log_le_sub_one_of_pos (div_pos hK0 hK)
  rw [e]
  have h3 : (K + 1) * Real.log (K0 / K) ≤ (K + 1) * (K0 / K - 1) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have e2 : (K + 1) * (K0 / K - 1) = K0 - K + K0 / K - 1 := by field_simp; ring
  have h4 : (K + 1) * (Real.log (A / K0) - 1) ≤ (K0 + 1) * (Real.log (A / K0) - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- **`t log(t/c)` is increasing** on `t ≤ t₀` when `log(t₀/c) ≥ 0`. -/
theorem tlogc_mono (t t0 c : ℝ) (hc : 0 < c) (ht : 0 < t) (htt : t ≤ t0)
    (hl : 0 ≤ Real.log (t0 / c)) : t * Real.log (t / c) ≤ t0 * Real.log (t0 / c) := by
  have h1 : Real.log (t / c) ≤ Real.log (t0 / c) :=
    Real.log_le_log (div_pos ht hc) (div_le_div_of_nonneg_right htt hc.le)
  calc t * Real.log (t / c) ≤ t * Real.log (t0 / c) := mul_le_mul_of_nonneg_left h1 ht.le
    _ ≤ t0 * Real.log (t0 / c) := mul_le_mul_of_nonneg_right htt hl

/-! ## (3) `eq:cupcake3` -/

/-- The main term of `eq:cupcake3` at the second choice: `≤ 3u⁴(6λ - 8)`. -/
theorem cup_main (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y)
    (hA : Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) :
    Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ * Real.log (v2 Y * q) ≤
      3 * (Y ^ ((1 : ℝ) / 6)) ^ 4 * (6 * Real.log (Y ^ ((1 : ℝ) / 6)) - 8) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, hv2, hq2⟩ := sec_eqs Y hY0
  obtain ⟨-, h3S, -, -⟩ := logs_S
  obtain ⟨pf1, -⟩ := pref Y δ q hY hq hA
  obtain ⟨-, -, -, -, -, -, -, -, hV1, -, -⟩ := sec_hyps Y hY
  have hu := u_ge Y hY
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have hVq : 1 ≤ v2 Y * q := one_le_mul_of_one_le_of_one_le hV1 hqR
  have hlVq : Real.log (v2 Y * q) ≤ 6 * Real.log (Y ^ ((1 : ℝ) / 6)) - 8 := by
    have h1 : v2 Y * q ≤ v2 Y * q2 Y := mul_le_mul_of_nonneg_left hQ (by linarith)
    have e : v2 Y * q2 Y = (Y ^ ((1 : ℝ) / 6)) ^ 6 / (3 * (500 * Real.sqrt 6)) := by
      rw [hv2, hq2]; ring
    have h2 := Real.log_le_log (by linarith) h1
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow] at h2
    push_cast at h2; linarith
  exact mul_le_mul pf1 hlVq (Real.log_nonneg hVq) (by positivity)

/-- The `O*` term of `eq:cupcake3` at the second choice: `≤ 0.12u⁴`. -/
theorem cup_err (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    (1 / 4 - 1 / Real.pi ^ 2) * c0 *
        ((u2 Y * v2 Y) ^ 2 * Real.log (v2 Y) / (2 * q * Y) + 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) +
          (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) * Real.log q) ≤
      0.12 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu2, hv2, -⟩ := sec_eqs Y hY0
  obtain ⟨-, hS2, hSS⟩ := S_bounds
  obtain ⟨hlQ, -, -, -⟩ := logQ_facts Y hY
  obtain ⟨-, -, -, hl1, hl2, -⟩ := kdata Y hY
  obtain ⟨-, -, -, -, -, -, -, hU1, hV1, -, -⟩ := sec_hyps Y hY
  obtain ⟨p1, p2⟩ := pi_sq_bounds
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set LV := Real.log (v2 Y) with hLV
  have hlV : LV ≤ 2 * lam := by
    rw [hLV, hv2, Real.log_div (by positivity) (by norm_num), Real.log_pow]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); push_cast; linarith
  have hlV0 : 0 ≤ LV := Real.log_nonneg hV1
  -- (a1) `(UV)²log V/(2qx) ≤ (500000/3)λu²`
  have hUV2 : (u2 Y * v2 Y) ^ 2 = 500000 / 3 * u ^ 8 := by
    rw [hu2, hv2]
    have e : (500 * Real.sqrt 6 * u ^ 2 * (u ^ 2 / 3)) ^ 2 =
        (500 * Real.sqrt 6) ^ 2 / 9 * u ^ 8 := by ring
    rw [e, hSS]; ring
  have a1 : (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) ≤ 500000 / 3 * lam * u ^ 2 := by
    have n0 : 0 ≤ (u2 Y * v2 Y) ^ 2 * LV := mul_nonneg (sq_nonneg _) hlV0
    have hqY : 2 * Y ≤ 2 * q * Y := by
      have := mul_le_mul_of_nonneg_right hqR hY0.le
      linarith
    calc (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) ≤ (u2 Y * v2 Y) ^ 2 * LV / (2 * Y) :=
          div_le_div_of_nonneg_left n0 (by positivity) hqY
      _ = 250000 / 3 * u ^ 2 * LV := by
          rw [hUV2, eY, div_eq_iff (by positivity)]; ring
      _ ≤ 250000 / 3 * u ^ 2 * (2 * lam) := mul_le_mul_of_nonneg_left hlV (by positivity)
      _ = 500000 / 3 * lam * u ^ 2 := by ring
  -- (a2) `(3c₄/2)UV²/x ≤ 213`
  have a2 : 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) ≤ 213 := by
    have e : u2 Y * v2 Y ^ 2 / Y = 500 * Real.sqrt 6 / 9 := by
      rw [hu2, hv2, eY, div_eq_iff (by positivity)]; ring
    rw [e]; unfold c4; linarith
  -- (a3) `(U + 1)²V/(2x)·log q ≤ 10⁶·4λ`
  have a3 : (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) * Real.log q ≤ 1000000 * (4 * lam) := by
    have hlq : Real.log q ≤ 4 * lam := by
      have := Real.log_le_log (by linarith) hQ; linarith
    have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqR
    have hfr : (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) ≤ 1000000 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (u2 Y + 1) ^ 2 ≤ 4 * u2 Y ^ 2 := by
        have := sq_nonneg (u2 Y - 1); linarith
      have e : 4 * u2 Y ^ 2 * v2 Y = 1000000 * (2 * Y) := by
        rw [hu2, hv2, eY]
        have e2 : 4 * (500 * Real.sqrt 6 * u ^ 2) ^ 2 * (u ^ 2 / 3) =
            4 * (500 * Real.sqrt 6) ^ 2 / 3 * u ^ 6 := by ring
        rw [e2, hSS]; ring
      have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ v2 Y)
      linarith
    calc (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) * Real.log q ≤ 1000000 * Real.log q :=
          mul_le_mul_of_nonneg_right hfr hlq0
      _ ≤ 1000000 * (4 * lam) := by linarith
  have a1' : 500000 / 3 * lam * u ^ 2 ≤ 500000 / 3 * (1.5e-7 * u ^ 4) :=
    lam_u2 u lam _ hu hl2 (by norm_num)
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu1 : 8000 ^ 3 * u ≤ u ^ 4 := by
    have h3 : (8000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    calc (8000 : ℝ) ^ 3 * u ≤ u ^ 3 * u := mul_le_mul_of_nonneg_right h3 hu0.le
      _ = u ^ 4 := by ring
  have hsum : (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) + 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) +
      (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) * Real.log q ≤ 0.0256 * u ^ 4 := by
    linarith
  have hsum0 : 0 ≤ (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) + 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) +
      (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) * Real.log q := by
    have h1 : 0 ≤ (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) :=
      div_nonneg (mul_nonneg (sq_nonneg _) hlV0) (by positivity)
    have h2 : 0 ≤ 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) := by
      have : 0 ≤ u2 Y := by linarith
      unfold c4; positivity
    have h3 : 0 ≤ (u2 Y + 1) ^ 2 * v2 Y / (2 * Y) * Real.log q :=
      mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity))
        (Real.log_nonneg hqR)
    linarith
  have hcoef : (1 / 4 - 1 / Real.pi ^ 2) * c0 ≤ 4.687 := by
    have : 0.10132 ≤ 1 / Real.pi ^ 2 := by rw [le_div_iff₀ (by linarith)]; linarith
    unfold c0; linarith
  calc _ ≤ 4.687 * (0.0256 * u ^ 4) := mul_le_mul hcoef hsum hsum0 (by norm_num)
    _ ≤ 0.12 * u ^ 4 := by nlinarith [pow_pos hu0 4]

/-- **`eq:cupcake3` at the second choice**: `≤ u⁴(18λ - 23.88)`. -/
theorem cup_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y)
    (hA : Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) :
    cupcake3 Y δ q (u2 Y) (v2 Y) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (18 * Real.log (Y ^ ((1 : ℝ) / 6)) - 23.88) := by
  have h1 := cup_main Y δ q hY hq hQ hA
  have h2 := cup_err Y q hY hq hQ
  unfold cupcake3
  linarith

/-! ## (4) `eq:piececake` (`|δ| ≤ 1/2c₂`, so `q > y`) -/

/-- `UV log(UV/√e) ∈ [0, 408.25u⁴(4λ + 5.54)]`. -/
theorem x1_le (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    0 ≤ u2 Y * v2 Y * Real.log (u2 Y * v2 Y / Real.sqrt (Real.exp 1)) ∧
      u2 Y * v2 Y * Real.log (u2 Y * v2 Y / Real.sqrt (Real.exp 1)) ≤
        408.25 * (Y ^ ((1 : ℝ) / 6)) ^ 4 * (4 * Real.log (Y ^ ((1 : ℝ) / 6)) + 5.54) := by
  obtain ⟨hUV, -, -, -, -⟩ := sdata Y hY
  obtain ⟨hlS3, -, -, -⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨-, hS2, -⟩ := S_bounds
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hlog : Real.log (u2 Y * v2 Y / Real.sqrt (Real.exp 1)) =
      Real.log (500 * Real.sqrt 6 / 3) + 4 * lam - 1 / 2 := by
    rw [hUV, Real.log_div (by positivity) (by positivity), Real.log_sqrt (Real.exp_pos 1).le,
      Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hlog, hUV]
  have h0 : 0 ≤ Real.log (500 * Real.sqrt 6 / 3) + 4 * lam - 1 / 2 := by linarith
  have h1 : 500 * Real.sqrt 6 / 3 * u ^ 4 ≤ 408.25 * u ^ 4 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact ⟨mul_nonneg (by positivity) h0, mul_le_mul h1 (by linarith) h0 (by positivity)⟩

/-- `q√3·log(c₂x/q) ∈ [0, (u⁴/1224.7445)·1.73206(4λ + 1.4)]` for `y < q ≤ Q`. -/
theorem x2_le (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hQ : (q : ℝ) ≤ q2 Y)
    (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    0 ≤ (q : ℝ) * (Real.sqrt 3 * Real.log (c2 * Y / q)) ∧
      (q : ℝ) * (Real.sqrt 3 * Real.log (c2 * Y / q)) ≤
        (Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.7445 *
          (1.73206 * (4 * Real.log (Y ^ ((1 : ℝ) / 6)) + 1.4)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨-, hQu, -, -, -⟩ := sdata Y hY
  obtain ⟨-, -, hl6c⟩ := logs_c2
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hc20 : 0 < c2 := by linarith
  have hqR : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hqy
  have h3 : Real.sqrt 3 ≤ 1.73206 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hlc : Real.log (c2 * Y / q) ≤ 4 * lam + 1.4 := by
    have h1 : c2 * Y / q ≤ 6 * c2 * u ^ 4 := by
      rw [div_le_iff₀ hqR, eY]
      have := mul_lt_mul_of_pos_left hqy (by positivity : (0 : ℝ) < 6 * c2 * u ^ 4)
      have e : 6 * c2 * u ^ 4 * (u ^ 2 / 6) = c2 * u ^ 6 := by ring
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
    push_cast at h2; linarith
  have hq' : (q : ℝ) ≤ u ^ 4 / 1224.7445 := hQ.trans hQu
  have hlc0 : 0 ≤ Real.log (c2 * Y / q) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hqR, eY]
    have hu2b : (1 : ℝ) ≤ u ^ 2 := by nlinarith
    have h4 : u ^ 4 ≤ u ^ 6 := by
      calc u ^ 4 = u ^ 4 * 1 := by ring
        _ ≤ u ^ 4 * u ^ 2 := mul_le_mul_of_nonneg_left hu2b (by positivity)
        _ = u ^ 6 := by ring
    have h6 : 0.6714 * u ^ 6 ≤ c2 * u ^ 6 := mul_le_mul_of_nonneg_right hc2a (by positivity)
    have h7 : 0 ≤ u ^ 6 := by positivity
    have hq2 : (q : ℝ) * 1224.7445 ≤ u ^ 4 := (le_div_iff₀ (by norm_num)).mp hq'
    linarith
  refine ⟨mul_nonneg hqR.le (mul_nonneg (Real.sqrt_nonneg _) hlc0), ?_⟩
  exact mul_le_mul hq' (mul_le_mul h3 hlc hlc0 (by norm_num))
    (mul_nonneg (Real.sqrt_nonneg _) hlc0) (by positivity)

/-- `q·(log UV/2)·log⁺(2UV/q) ∈ [0, ((4λ + 6.04)/2)·(u⁴/1224.7445)·13.82]` for `q ≤ Q`. -/
theorem x3_le (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    0 ≤ (q : ℝ) * (Real.log (u2 Y * v2 Y) / 2 * logp (u2 Y * v2 Y / (q / 2))) ∧
      (q : ℝ) * (Real.log (u2 Y * v2 Y) / 2 * logp (u2 Y * v2 Y / (q / 2))) ≤
        (4 * Real.log (Y ^ ((1 : ℝ) / 6)) + 6.04) / 2 *
          ((Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.7445 * 13.82) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, hq2⟩ := sec_eqs Y hY0
  obtain ⟨hlS3, -, -, hl6⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨hUV, hQu, -, -, -⟩ := sdata Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have h66 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have hUV0 : 0 < u2 Y * v2 Y := by rw [hUV]; positivity
  have hlUV : Real.log (u2 Y * v2 Y) = Real.log (500 * Real.sqrt 6 / 3) + 4 * lam := by
    rw [hUV, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have e : u2 Y * v2 Y / (q / 2) = 2 * (u2 Y * v2 Y) / q := by ring
  have hA : 2 * (u2 Y * v2 Y) / q2 Y = 1000000 := by
    rw [hUV, hq2, div_div_eq_mul_div, div_eq_iff (by positivity)]
    linear_combination (500000 / 3 * u ^ 4) * h66
  have hAQ : 1 ≤ Real.log (2 * (u2 Y * v2 Y) / q2 Y) := by
    rw [hA, Real.le_log_iff_exp_le (by norm_num)]
    have he := Real.exp_one_lt_d9
    linarith
  have ht := tlog_le (2 * (u2 Y * v2 Y)) (q2 Y) q (by positivity) (by linarith) hQ hAQ
  rw [hA] at ht
  have hlp : (q : ℝ) * logp (2 * (u2 Y * v2 Y) / q) ≤ u ^ 4 / 1224.7445 * 13.82 := by
    have hQl : q2 Y * Real.log 1000000 ≤ u ^ 4 / 1224.7445 * 13.82 :=
      mul_le_mul hQu hl6 (Real.log_nonneg (by norm_num)) (by positivity)
    linarith
  have hlp0 : 0 ≤ (q : ℝ) * logp (2 * (u2 Y * v2 Y) / q) :=
    mul_nonneg (by positivity) (le_max_right _ _)
  rw [e]
  have e3 : (q : ℝ) * (Real.log (u2 Y * v2 Y) / 2 * logp (2 * (u2 Y * v2 Y) / q)) =
      Real.log (u2 Y * v2 Y) / 2 * (q * logp (2 * (u2 Y * v2 Y) / q)) := by ring
  rw [e3]
  have hl0 : 0 ≤ Real.log (u2 Y * v2 Y) / 2 := by rw [hlUV]; linarith
  exact ⟨mul_nonneg hl0 hlp0, mul_le_mul (by rw [hlUV]; linarith) hlp hlp0 (by linarith)⟩

/-- **(P1)** the `D`-terms of `eq:piececake`: `≤ u⁴(5837.2λ + 8084.5)`. -/
theorem pc_P1 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y)
    (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi *
        (u2 Y * v2 Y * Real.log (u2 Y * v2 Y / Real.sqrt (Real.exp 1)) +
          q * (Real.sqrt 3 * Real.log (c2 * Y / q) +
            Real.log (u2 Y * v2 Y) / 2 * logp (u2 Y * v2 Y / (q / 2)))) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (5837.2 * Real.log (Y ^ ((1 : ℝ) / 6)) + 8084.5) := by
  obtain ⟨-, -, hc1, -, -⟩ := sdata Y hY
  obtain ⟨a0, a1⟩ := x1_le Y hY
  obtain ⟨b0, b1⟩ := x2_le Y q hY hQ hqy
  obtain ⟨d0, d1⟩ := x3_le Y q hY hq hQ
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hk := kb_coef _ hc1
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  rw [mul_add (q : ℝ)]
  have hin0 := add_nonneg a0 (add_nonneg b0 d0)
  have hin := add_le_add a1 (add_le_add b1 d1)
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  have hw : u ^ 4 / 1224.7445 * 1224.7445 = u ^ 4 := div_mul_cancel₀ _ (by norm_num)
  have hwl : u ^ 4 / 1224.7445 * lam * 1224.7445 = u ^ 4 * lam := by rw [← hw]; ring
  calc _ ≤ 3.5744 * (408.25 * u ^ 4 * (4 * lam + 5.54) +
          (u ^ 4 / 1224.7445 * (1.73206 * (4 * lam + 1.4)) +
            (4 * lam + 6.04) / 2 * (u ^ 4 / 1224.7445 * 13.82))) :=
        mul_le_mul hk hin hin0 (by norm_num)
    _ ≤ u ^ 4 * (5837.2 * lam + 8084.5) := by linarith

/-- **(P2)** `(3c₁/2)(x/q)log(UV)log⁺(UV/(c₂x/q)) ≤ u⁴(167.41λ + 252.79)` for `q > y`. -/
theorem pc_P2 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    3 * c1b Y (u2 Y * v2 Y) / 2 * (Y / q) * Real.log (u2 Y * v2 Y) *
        logp (u2 Y * v2 Y / (c2 * Y / q)) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (167.41 * Real.log (Y ^ ((1 : ℝ) / 6)) + 252.79) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hlS3, -, -, -⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨hl18, hl18', -⟩ := logs_c2
  obtain ⟨hUV, -, hc1, -, -⟩ := sdata Y hY
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hc20 : 0 < c2 := by linarith
  have hqR : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hqy
  have hUV0 : 0 < u2 Y * v2 Y := by rw [hUV]; positivity
  have hc1' : 1 ≤ c1b Y (u2 Y * v2 Y) := by
    unfold c1b
    have := eta1_bounds.1
    have : 0 ≤ eta1 * (u2 Y * v2 Y) / (2 * Y) := by positivity
    linarith
  have hlUV : Real.log (u2 Y * v2 Y) = Real.log (500 * Real.sqrt 6 / 3) + 4 * lam := by
    rw [hUV, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  -- `(x/q)log⁺(q/q₀) ≤ 6u⁴·4.65`, `q₀ = c₂x/UV`
  set q0 := c2 * Y / (u2 Y * v2 Y) with hq0_def
  have hq0 : 0 < q0 := by positivity
  have earg : u2 Y * v2 Y / (c2 * Y / q) = q / q0 := by
    rw [hq0_def, div_div_eq_mul_div, div_div_eq_mul_div, mul_comm (u2 Y * v2 Y)]
  have hyq0 : u ^ 2 / 6 / q0 = 500 * Real.sqrt 6 / (18 * c2) := by
    rw [hq0_def, hUV, eY, div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have eYy : Y / (u ^ 2 / 6) = 6 * u ^ 4 := by
    rw [eY, div_eq_iff (by positivity)]; ring
  have hxl : Y / q * logp (u2 Y * v2 Y / (c2 * Y / q)) ≤ 6 * u ^ 4 * 4.65 := by
    rw [earg]
    unfold logp
    rcases le_total (Real.log (q / q0)) 0 with h | h
    · rw [max_eq_right h, mul_zero]; positivity
    · rw [max_eq_left h]
      have hx := xlog_le Y (u ^ 2 / 6) q q0 hY0.le (by positivity) hqy.le hq0
        (by rw [hyq0]; exact hl18')
      rw [hyq0, eYy] at hx
      have := mul_le_mul_of_nonneg_left hl18 (by positivity : (0 : ℝ) ≤ 6 * u ^ 4)
      linarith
  have hk : 3 * c1b Y (u2 Y * v2 Y) / 2 ≤ 1.50003 := by linarith
  have hlUVb : Real.log (u2 Y * v2 Y) ≤ 4 * lam + 6.04 := by rw [hlUV]; linarith
  have hlUV0 : 0 ≤ Real.log (u2 Y * v2 Y) := by rw [hlUV]; linarith
  have hxl0 : 0 ≤ Y / q * logp (u2 Y * v2 Y / (c2 * Y / q)) :=
    mul_nonneg (by positivity) (le_max_right _ _)
  have e : 3 * c1b Y (u2 Y * v2 Y) / 2 * (Y / q) * Real.log (u2 Y * v2 Y) *
      logp (u2 Y * v2 Y / (c2 * Y / q)) = 3 * c1b Y (u2 Y * v2 Y) / 2 * Real.log (u2 Y * v2 Y) *
      (Y / q * logp (u2 Y * v2 Y / (c2 * Y / q))) := by ring
  rw [e]
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  calc _ ≤ 1.50003 * (4 * lam + 6.04) * (6 * u ^ 4 * 4.65) :=
        mul_le_mul (mul_le_mul hk hlUVb hlUV0 (by norm_num)) hxl hxl0 (by positivity)
    _ ≤ u ^ 4 * (167.41 * lam + 252.79) := by linarith

/-- **(P3)** `(2|η'|₁/π)·q·max(1, …)·log(q/2) ≤ u⁴(0.0230591λ² + 0.247)` for `q ≤ Q`. -/
theorem pc_P3 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    2 * eta1 / Real.pi * q *
        max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
        Real.log (q / 2) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (0.0230591 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 + 0.247) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, hq2⟩ := sec_eqs Y hY0
  obtain ⟨-, -, h2S, -⟩ := logs_S
  obtain ⟨-, hQu, -, -, -⟩ := sdata Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hmax := k3_max_sec Y q hY hq hQ
  have heta := eta_pi
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have hlq : Real.log (q / 2) ≤ 4 * lam - 7.78 := by
    have h1 : (q : ℝ) / 2 ≤ u ^ 4 / (2 * (500 * Real.sqrt 6)) := by
      have : q2 Y / 2 = u ^ 4 / (2 * (500 * Real.sqrt 6)) := by rw [hq2]; ring
      linarith
    have h2 := Real.log_le_log (by linarith) h1
    have e : Real.log (u ^ 4 / (2 * (500 * Real.sqrt 6))) =
        4 * lam - Real.log (2 * (500 * Real.sqrt 6)) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    rw [e] at h2; linarith
  have hlq0 : 0 ≤ 4 * lam - 7.78 := by linarith
  have hmax0 : 0 ≤ max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) :=
    le_trans zero_le_one (le_max_left _ _)
  have heta0 : 0 ≤ 2 * eta1 / Real.pi := by
    unfold eta1; have := Real.log_two_gt_d9; positivity
  have hqu : (q : ℝ) ≤ u ^ 4 / 1224.7445 := hQ.trans hQu
  have hA0 : 0 ≤ 2 * eta1 / Real.pi * q *
      max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) := by
    positivity
  have hA : 2 * eta1 / Real.pi * q *
      max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) ≤
      3.53018 * (u ^ 4 / 1224.7445) * (2 * lam - 11) :=
    mul_le_mul (mul_le_mul heta hqu (by positivity) (by norm_num)) hmax hmax0 (by positivity)
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  have hul2 : 0 ≤ u ^ 4 * lam ^ 2 := mul_nonneg (by positivity) (sq_nonneg lam)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  calc _ ≤ 2 * eta1 / Real.pi * q *
          max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
          (4 * lam - 7.78) := mul_le_mul_of_nonneg_left hlq hA0
    _ ≤ 3.53018 * (u ^ 4 / 1224.7445) * (2 * lam - 11) * (4 * lam - 7.78) :=
        mul_le_mul_of_nonneg_right hA hlq0
    _ = u ^ 4 * (3.53018 / 1224.7445 * ((2 * lam - 11) * (4 * lam - 7.78))) := by ring
    _ ≤ u ^ 4 * (0.0230591 * lam ^ 2 + 0.247) := by
        refine mul_le_mul_of_nonneg_left ?_ hu4
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
        nlinarith [sq_nonneg lam]

/-- **(P4 + P5)** the `√x`-terms of `eq:piececake`: `≤ 0.22u⁴`. -/
theorem pc_P45 (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    3 * c1b Y (u2 Y * v2 Y) / (2 * Real.sqrt (2 * c2)) * Real.sqrt Y * Real.log (c2 * Y / 2) +
        25 * c0 / (4 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2) * Real.sqrt Y * Real.log Y ≤
      0.22 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨hUV, -, hc1, hl3, -⟩ := sdata Y hY
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨r0, r1⟩ := rpow32
  obtain ⟨p1, -⟩ := pi_sq_bounds
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hsq := sqrt_eq_u3 Y hY0
  have hu := u_ge Y hY
  have hc20 : 0 < c2 := by linarith
  have hc1' : 1 ≤ c1b Y (u2 Y * v2 Y) := by
    unfold c1b
    have := eta1_bounds.1
    have : 0 ≤ eta1 * (u2 Y * v2 Y) / (2 * Y) := by rw [hUV]; positivity
    linarith
  have hlc0 : 0 ≤ Real.log (c2 * Y / 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by norm_num)]
    have : 0.6714 * Y ≤ c2 * Y := mul_le_mul_of_nonneg_right hc2a hY0.le
    linarith
  have hlc : Real.log (c2 * Y / 2) ≤ Real.log Y := by
    refine Real.log_le_log (by positivity) ?_
    have : c2 * Y ≤ 1 * Y := mul_le_mul_of_nonneg_right (by linarith) hY0.le
    linarith
  have hs2 : 1.1587 ≤ Real.sqrt (2 * c2) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have k4 : 3 * c1b Y (u2 Y * v2 Y) / (2 * Real.sqrt (2 * c2)) ≤ 1.2946 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have k5 : 25 * c0 / (4 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2) ≤ 31.07 := by
    have h : 25 * c0 / (4 * Real.pi ^ 2) ≤ 19.962 := by
      rw [div_le_iff₀ (by positivity)]; unfold c0; linarith
    have := mul_le_mul h r1 r0 (by norm_num)
    linarith
  rw [hsq]
  rw [eL] at hlc ⊢
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have t4 : 3 * c1b Y (u2 Y * v2 Y) / (2 * Real.sqrt (2 * c2)) * u ^ 3 * Real.log (c2 * Y / 2) ≤
      1.2946 * u ^ 3 * (6 * lam) :=
    mul_le_mul (mul_le_mul_of_nonneg_right k4 (by positivity)) hlc hlc0 (by positivity)
  have t5 : 25 * c0 / (4 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2) * u ^ 3 * (6 * lam) ≤
      31.07 * u ^ 3 * (6 * lam) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k5 (by positivity)) (by linarith)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  linarith

/-- **`eq:piececake` at the second choice**: `≤ u⁴(0.0230591λ² + 6004.61λ + 8337.76)`. -/
theorem pc_le (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y)
    (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    piececake Y q (u2 Y) (v2 Y) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 *
      (0.0230591 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 +
        6004.61 * Real.log (Y ^ ((1 : ℝ) / 6)) + 8337.76) := by
  have h1 := pc_P1 Y q hY hq hQ hqy
  have h2 := pc_P2 Y q hY hqy
  have h3 := pc_P3 Y q hY hq hQ
  have h45 := pc_P45 Y hY
  have hu4 : (0 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
  unfold piececake
  linarith

/-! ## (5) `eq:tvorog` at `ε = 0.01` (`|δ| > 1/2c₂`) -/

/-- **(T1)** `k·UV·log(UV/e) ≤ u⁴(5837λ + 7354.7)`. -/
theorem tv_T1 (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi * (u2 Y * v2 Y) *
        Real.log (u2 Y * v2 Y / Real.exp 1) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (5837 * Real.log (Y ^ ((1 : ℝ) / 6)) + 7354.7) := by
  obtain ⟨hUV, -, hc1, -, -⟩ := sdata Y hY
  obtain ⟨hlS3, -, -, -⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨-, hS2, -⟩ := S_bounds
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hk := kb_coef _ hc1
  have hu := u_ge Y hY
  set k := 2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi with hk_def
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hk0 : 0 ≤ k := by rw [hk_def]; positivity
  have hlog : Real.log (u2 Y * v2 Y / Real.exp 1) =
      Real.log (500 * Real.sqrt 6 / 3) + 4 * lam - 1 := by
    rw [hUV, Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hlog, hUV]
  have h1 : k * (500 * Real.sqrt 6 / 3 * u ^ 4) ≤ 3.5744 * (408.25 * u ^ 4) :=
    mul_le_mul hk (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
      (by norm_num)
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  calc _ ≤ 3.5744 * (408.25 * u ^ 4) * (4 * lam + 5.04) :=
        mul_le_mul h1 (by linarith) (by linarith) (by positivity)
    _ ≤ u ^ 4 * (5837 * lam + 7354.7) := by linarith

/-- `|δ|q ≥ u²/(12c₂)` when `|δ| > 1/2c₂` (second choice). -/
theorem dq_lower (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y)
    (hA : Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q)
    (hd : 1 / (2 * c2) < |δ|) : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ |δ| * q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have hu := u_ge Y hY
  rw [e13] at hA
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hc0 : 0 < c2 := by linarith
  rcases hA with h | h
  · have h1 : 1 / (2 * c2) * (u ^ 2 / 6) ≤ |δ| * q :=
      mul_le_mul hd.le h.le (by positivity) (abs_nonneg δ)
    have e : 1 / (2 * c2) * (u ^ 2 / 6) = u ^ 2 / (12 * c2) := by ring
    linarith
  · have h1 : u ^ 2 / (12 * c2) ≤ 4 / 3 * u ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hc2a (sq_nonneg u)
      nlinarith [sq_nonneg u]
    linarith

/-- **The range of `K = x/(|δ|q)`**: `u⁴/1224.745 ≤ K ≤ 8.058u⁴` when `u²/(12c₂) ≤ |δ|q ≤ U`. -/
theorem K_bounds (Y D : ℝ) (hY : 3.4e23 ≤ Y) (hdq : D ≤ u2 Y)
    (hD : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ D) :
    0 < D ∧ (Y ^ ((1 : ℝ) / 6)) ^ 4 / 1224.745 ≤ Y / D ∧
      Y / D ≤ 8.058 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu2, -, -⟩ := sec_eqs Y hY0
  obtain ⟨-, hS2, -⟩ := S_bounds
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hc0 : 0 < c2 := by linarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  refine ⟨hD0, ?_, ?_⟩
  · rw [le_div_iff₀ hD0, eY]
    have h1 : D ≤ 1224.745 * u ^ 2 := by
      rw [hu2] at hdq
      have : 500 * Real.sqrt 6 * u ^ 2 ≤ 1224.745 * u ^ 2 :=
        mul_le_mul_of_nonneg_right hS2 (by positivity)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ u ^ 4 / 1224.745)
    have e : u ^ 4 / 1224.745 * (1224.745 * u ^ 2) = u ^ 6 := by ring
    linarith
  · rw [div_le_iff₀ hD0, eY]
    have h1 := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 8.058 * u ^ 4)
    have e : 8.058 * u ^ 4 * (u ^ 2 / (12 * c2)) = 8.058 / (12 * c2) * u ^ 6 := by ring
    have h3 : 1 ≤ 8.058 / (12 * c2) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h4 : u ^ 6 ≤ 8.058 / (12 * c2) * u ^ 6 := le_mul_of_one_le_left (by positivity) h3
    linarith

/-- The arithmetic core of (T2), over abstract reals: `s = √3.02`, `L = log UV`,
`P = log((K + 1)/√2)`, `R = log⁺(A/K)`. -/
theorem tv2_core (k s L K P R u lam : ℝ) (hk0 : 0 ≤ k) (hk : k ≤ 3.5744) (hs0 : 1 ≤ s)
    (hs : s ≤ 1.73782) (hL : L ≤ 4 * lam + 6.04)
    (hP : (K + 1) * P ≤ 8.059 * u ^ 4 * (4 * lam + 1.8)) (hR0 : 0 ≤ (K + 1) * R)
    (hR : (K + 1) * R ≤ 8.059 * u ^ 4 * 5.96 + 9869) (hu : 8000 ≤ u) (hl : 8.3 ≤ lam) :
    k * (1 + 0.01) * (K + 1) * ((s - 1) * P + L / 2 * R) ≤ u ^ 4 * (432.7 * lam + 562.4) := by
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu0 : 0 ≤ u ^ 4 := by positivity
  have hl0 : 0 ≤ lam := by linarith
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg hu0 hl0
  have hul8 : (8000 : ℝ) ^ 4 * lam ≤ u ^ 4 * lam := mul_le_mul_of_nonneg_right hu4 hl0
  have e : k * (1 + 0.01) * (K + 1) * ((s - 1) * P + L / 2 * R) =
      k * (1 + 0.01) * ((s - 1) * ((K + 1) * P) + L / 2 * ((K + 1) * R)) := by ring
  rw [e]
  have hB : 0 ≤ 8.059 * u ^ 4 * (4 * lam + 1.8) := mul_nonneg (by positivity) (by linarith)
  have i1 : (s - 1) * ((K + 1) * P) ≤ 0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) :=
    (mul_le_mul_of_nonneg_left hP (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hB)
  have i2 : L / 2 * ((K + 1) * R) ≤ (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 5.96 + 9869) :=
    mul_le_mul (by linarith) hR hR0 (by linarith)
  have hI2 : 0 ≤ (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 5.96 + 9869) :=
    mul_nonneg (by linarith) (by positivity)
  have hk1 : k * (1 + 0.01) ≤ 3.5744 * 1.01 := by linarith
  have hk10 : 0 ≤ k * (1 + 0.01) := mul_nonneg hk0 (by norm_num)
  have e2 : 3.5744 * 1.01 * (0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) +
      (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 5.96 + 9869)) =
      3.5744 * 1.01 * (0.73782 * 8.059 * 4 + 2 * 8.059 * 5.96) * (u ^ 4 * lam) +
        3.5744 * 1.01 * (0.73782 * 8.059 * 1.8 + 3.02 * 8.059 * 5.96) * u ^ 4 +
        3.5744 * 1.01 * (2 * 9869) * lam + 3.5744 * 1.01 * (3.02 * 9869) := by ring
  calc _ ≤ k * (1 + 0.01) * (0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) +
          (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 5.96 + 9869)) :=
        mul_le_mul_of_nonneg_left (add_le_add i1 i2) hk10
    _ ≤ 3.5744 * 1.01 * (0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) +
          (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 5.96 + 9869)) :=
        mul_le_mul_of_nonneg_right hk1 (add_nonneg (mul_nonneg (by norm_num) hB) hI2)
    _ ≤ u ^ 4 * (432.7 * lam + 562.4) := by rw [e2]; linarith

/-- **(T2)** the `K`-terms of `eq:tvorog` at `ε = 0.01`: `≤ u⁴(432.7λ + 562.4)`. -/
theorem tv_T2 (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hdq : |δ| * q ≤ u2 Y)
    (hD : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ |δ| * q) :
    2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi * (1 + 0.01) * (Y / (|δ| * q) + 1) *
        ((Real.sqrt (3 + 2 * 0.01) - 1) * Real.log ((Y / (|δ| * q) + 1) / Real.sqrt 2) +
          Real.log (u2 Y * v2 Y) / 2 * logp (Real.exp 2 * (u2 Y * v2 Y) / (Y / (|δ| * q)))) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (432.7 * Real.log (Y ^ ((1 : ℝ) / 6)) + 562.4) := by
  obtain ⟨hD0, hKlo, hKhi⟩ := K_bounds Y (|δ| * q) hY hdq hD
  obtain ⟨hUV, -, hc1, -, -⟩ := sdata Y hY
  obtain ⟨hlS3, -, -, -⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨hK8, hK24a, hK24b⟩ := logs_K
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hk := kb_coef _ hc1
  have hu := u_ge Y hY
  set k := 2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi with hk_def
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  set K := Y / (|δ| * q) with hK_def
  have hu0 : 0 < u := by linarith
  have hk0 : 0 ≤ k := by rw [hk_def]; positivity
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hKlo
  have hUV0 : 0 < u2 Y * v2 Y := by rw [hUV]; positivity
  have hsq : Real.sqrt (3 + 2 * 0.01) ≤ 1.73782 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq1 : 1 ≤ Real.sqrt (3 + 2 * 0.01) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hlUV : Real.log (u2 Y * v2 Y) = Real.log (500 * Real.sqrt 6 / 3) + 4 * lam := by
    rw [hUV, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  -- (A) `(K + 1)log((K + 1)/√2) ≤ 8.059u⁴(4λ + 1.8)`
  have hK1 : K + 1 ≤ 8.059 * u ^ 4 := by linarith
  have hlg8 : Real.log (8.059 * u ^ 4 / Real.sqrt 2) =
      Real.log (8.059 / Real.sqrt 2) + 4 * lam := by
    rw [show 8.059 * u ^ 4 / Real.sqrt 2 = 8.059 / Real.sqrt 2 * u ^ 4 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlg80 : 0 ≤ Real.log (8.059 * u ^ 4 / Real.sqrt 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hTA := tlogc_mono (K + 1) (8.059 * u ^ 4) (Real.sqrt 2) (by positivity) (by linarith)
    hK1 hlg80
  have hTA' : (K + 1) * Real.log ((K + 1) / Real.sqrt 2) ≤ 8.059 * u ^ 4 * (4 * lam + 1.8) := by
    refine hTA.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hlg8]; linarith
  -- (B) `(K + 1)log⁺(A/K) ≤ 8.059u⁴·5.96 + 9869`, `A = e²UV`
  set A := Real.exp 2 * (u2 Y * v2 Y) with hA_def
  have hA0 : 0 < A := by rw [hA_def]; positivity
  have hAK : A / (8.058 * u ^ 4) = Real.exp 2 * (500 * Real.sqrt 6 / 24.174) := by
    rw [hA_def, hUV, div_eq_iff (by positivity)]; ring
  have hlAK : Real.log (A / (8.058 * u ^ 4)) = 2 + Real.log (500 * Real.sqrt 6 / 24.174) := by
    rw [hAK, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hkl := klog_le A K (8.058 * u ^ 4) hK0 hKhi (by rw [hlAK]; linarith) hA0
  have hKK : 8.058 * u ^ 4 / K ≤ 9870 := by
    rw [div_le_iff₀ hK0]
    have h1 := mul_le_mul_of_nonneg_left hKlo (by norm_num : (0 : ℝ) ≤ 9870)
    have e : 9870 * (u ^ 4 / 1224.745) = 9870 / 1224.745 * u ^ 4 := by ring
    have h2 : 8.058 * u ^ 4 ≤ 9870 / 1224.745 * u ^ 4 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hlogK : 0 ≤ Real.log (A / K) := by
    have h1 : A / (8.058 * u ^ 4) ≤ A / K := div_le_div_of_nonneg_left hA0.le hK0 hKhi
    have h2 := Real.log_le_log (by positivity) h1
    rw [hlAK] at h2; linarith
  have hlp : logp (A / K) = Real.log (A / K) := max_eq_left hlogK
  have hTB : (K + 1) * logp (A / K) ≤ 8.059 * u ^ 4 * 5.96 + 9869 := by
    rw [hlp]
    have h3 : (8.058 * u ^ 4 + 1) * Real.log (A / (8.058 * u ^ 4)) ≤ 8.059 * u ^ 4 * 5.96 := by
      rw [hlAK]
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    linarith
  have hTB0 : 0 ≤ (K + 1) * logp (A / K) := mul_nonneg (by linarith) (le_max_right _ _)
  exact tv2_core k _ _ K _ _ u lam hk0 hk hsq1 hsq (by rw [hlUV]; linarith) hTA' hTB0 hTB hu hl1

/-- **(T3)** the `√x`-terms of `eq:tvorog` at `ε = 0.01`: `≤ 25.1u⁴`. -/
theorem tv_T3 (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    (3 * c1b Y (u2 Y * v2 Y) / 2 * (1 / 2 + 3 * (1 + 0.01) / (16 * 0.01) * Real.log Y) +
        20 * c0 / (3 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2)) * Real.sqrt Y * Real.log Y ≤
      25.1 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨-, -, hc1, hl3, hl4⟩ := sdata Y hY
  obtain ⟨r0, r1⟩ := rpow32
  obtain ⟨p1, -⟩ := pi_sq_bounds
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hsq := sqrt_eq_u3 Y hY0
  have hu := u_ge Y hY
  rw [hsq, eL]
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have e3 : (3 : ℝ) * (1 + 0.01) / (16 * 0.01) = 18.9375 := by norm_num
  rw [e3]
  have hcoef : 3 * c1b Y (u2 Y * v2 Y) / 2 * (1 / 2 + 18.9375 * (6 * lam)) +
      20 * c0 / (3 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2) ≤ 170.441 * lam + 33.8901 := by
    have h1 : 3 * c1b Y (u2 Y * v2 Y) / 2 * (1 / 2 + 18.9375 * (6 * lam)) ≤
        1.50003 * (1 / 2 + 18.9375 * (6 * lam)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : 20 * c0 / (3 * Real.pi ^ 2) ≤ 21.292 := by
      rw [div_le_iff₀ (by positivity)]; unfold c0; linarith
    have h3 : 20 * c0 / (3 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2) ≤ 21.292 * 1.5564 :=
      mul_le_mul h2 r1 r0 (by norm_num)
    linarith
  have hb0 : 0 ≤ u ^ 3 * (6 * lam) := mul_nonneg (by positivity) (by linarith)
  calc _ = (3 * c1b Y (u2 Y * v2 Y) / 2 * (1 / 2 + 18.9375 * (6 * lam)) +
          20 * c0 / (3 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2)) * (u ^ 3 * (6 * lam)) := by
        ring
    _ ≤ (170.441 * lam + 33.8901) * (u ^ 3 * (6 * lam)) := mul_le_mul_of_nonneg_right hcoef hb0
    _ ≤ 25.1 * u ^ 4 := by linarith

/-- **`eq:tvorog` at the second choice, `ε = 0.01`**: `≤ u⁴(6269.7λ + 7942.2)`. -/
theorem tvo_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hdq : |δ| * q ≤ u2 Y)
    (hD : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ |δ| * q) :
    tvorog Y δ q (u2 Y) (v2 Y) 0.01 ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (6269.7 * Real.log (Y ^ ((1 : ℝ) / 6)) + 7942.2) := by
  have h1 := tv_T1 Y hY
  have h2 := tv_T2 Y δ q hY hdq hD
  have h3 := tv_T3 Y hY
  unfold tvorog
  linarith

/-! ## (6) Assembly -/

/-- `|δ| ≤ 1/2c₂` forces `q > y` at the second choice. -/
theorem q_gt_y (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y)
    (hA : Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q)
    (hd : |δ| ≤ 1 / (2 * c2)) : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  obtain ⟨hc2a, -⟩ := c2_bounds
  rw [e13] at hA
  rcases hA with h | h
  · exact h
  · have hc : 1 / (2 * c2) ≤ 0.7448 := by rw [div_le_iff₀ (by linarith)]; linarith
    have h1 : |δ| * q ≤ 0.7448 * q := mul_le_mul_of_nonneg_right (hd.trans hc) (by positivity)
    have hu2 : 0 < (Y ^ ((1 : ℝ) / 6)) ^ 2 := by positivity
    linarith

/-- The final comparison for `|δ| ≤ 1/2c₂`. -/
theorem fin1 (u lam C P : ℝ) (hu4 : 0 ≤ u ^ 4) (hl : 8.3 ≤ lam)
    (hC : C ≤ u ^ 4 * (18 * lam - 23.88))
    (hP : P ≤ u ^ 4 * (0.0230591 * lam ^ 2 + 6004.61 * lam + 8337.76)) :
    C + P ≤ 1230.9 * u ^ 4 * (6 * lam) + 0.0006406 * u ^ 4 * (6 * lam) ^ 2 := by
  have h : 0 ≤ u ^ 4 * (0.0000025 * lam ^ 2 + 1362.79 * lam - 8313.88) :=
    mul_nonneg hu4 (by nlinarith [sq_nonneg lam])
  linarith

/-- The final comparison for `|δ| > 1/2c₂`. -/
theorem fin2 (u lam C T : ℝ) (hu4 : 0 ≤ u ^ 4) (hl : 8.3 ≤ lam)
    (hC : C ≤ u ^ 4 * (18 * lam - 23.88))
    (hT : T ≤ u ^ 4 * (6269.7 * lam + 7942.2)) :
    C + T ≤ 1230.9 * u ^ 4 * (6 * lam) + 0.0006406 * u ^ 4 * (6 * lam) ^ 2 := by
  have h : 0 ≤ u ^ 4 * (0.0230616 * lam ^ 2 + 1097.7 * lam - 7918.32) :=
    mul_nonneg hu4 (by nlinarith [sq_nonneg lam])
  linarith

/-- **`MPG.SecI2Arith`, PROVED.** -/
theorem secI2Arith : SecI2Arith := by
  intro Y hY δ q hq hQ hdq hA
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hc := cup_le Y δ q hY hq hQ hA
  have hu4 : (0 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
  rw [e23, eL]
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · exact fin1 _ _ _ _ hu4 hl1 hc (pc_le Y q hY hq hQ (q_gt_y Y δ q hY hA hd))
  · exact fin2 _ _ _ _ hu4 hl1 hc (tvo_le Y δ q hY hdq (dq_lower Y δ q hY hA hd))

/-! ## (7) `SecI2At` from `lem:bogus` alone -/

/-- **`MPc.SecI2At` from `lem:bogus` alone, PROVED** (application of `MPG.secI2At_of`). -/
theorem secI2At_of_gen (hb : BogusEta2) : SecI2At :=
  secI2At_of hb secI2Arith

/-- **`OP.MinMainP 0.811 45.7575` with both Type I second-choice pieces from the source
lemmas**: `MPS1.minMainP_of_nine` with `SecI2At` supplied by `BogusEta2` (`lem:bogus` verbatim).
Open: `Bostb1Eta2`, `BogusEta2`, `Bosta2Eta2`, `Vinland1At`, `EriksagaAt`, `SecIIAt`; cited:
`Grara`, `Ronsard`, `Meproz`, `RS62Thm15`. Application only. -/
theorem minMainP_of_gen (hb1 : Bostb1Eta2) (hbg : BogusEta2) (hgr : Grara) (hro : Ronsard)
    (hme : Meproz) (hb2 : Bosta2Eta2) (hv1 : Vinland1At) (her : EriksagaAt) (hs3 : SecIIAt)
    (h15 : GS.RS62Thm15) : OP.MinMainP 0.811 45.7575 :=
  minMainP_of_nine hb1 hgr hro hme hb2 hv1 her (secI2At_of_gen hbg) hs3 h15

end Principia.Common.TernaryGoldbach.MPS2
