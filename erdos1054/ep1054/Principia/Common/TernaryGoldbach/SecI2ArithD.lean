/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BogusEta2D

set_option autoImplicit false

/-!
# `SecI2At` from the CORRECTED `lem:bogus` (`MPBD.BogusEta2D`) — the arithmetic still closes

`secI2ArithD : SecI2ArithD`: at the second choice (`U = 500√6x^{1/3}`, `V = x^{1/3}/3`,
`Q₀ = x/U`), for every admissible `(q, δ)`,

* `|δ| ≤ 1/2c₂` (so `q > y`): `cupcake3C + log(UV)·eq:keks(UV)` `≤ u⁴(0.0230591λ² + 6022.6λ
  + 9043.3)` (`kk_le`, `cup_leC`);
* `|δ| > 1/2c₂`: `cupcake3C + tvorogD(0.01)` `≤ u⁴(6328.5λ + 8157.2)` (`tvD_le`, `cup_leC`);

both against the `SecI2At` budget `u⁴(0.0230616λ² + 7385.4λ)` for `λ = log x^{1/6} ≥ 8.3`
(margins `≥ 2267u⁴` and `≥ 615u⁴` at `λ = 8.3`, growing with `λ`). The three corrections cost:
`eq:etoile` `(3/2)×` on a term of size `O(u²λ)` (absorbed in `0.12u⁴`); `c₁ = 1 + |η'|₁D/x`
(`c₁ ≤ 1.00004`, still `2√(c₀c₁)/π ≤ 3.5744`); the crude `log(UV)·eq:keks` branch `≈ 730u⁴`.
Numerically (`scratchpad/bogusD/num3.py`, exact formulas, `x ∈ [3.4·10²³, 10²⁰⁰]`) the worst
ratios are `0.946` and `0.970`, both at `x = 3.4·10²³`.

```
 SecI2At ← BogusEta2D ← TrompaisEta2, MainBogusEta2C, EsthelBogusKD (PROVED), EsthelBogusED
          (secI2At_of_genD; secI2ArithD PROVED)
```
-/

namespace Principia.Common.TernaryGoldbach.MPSD

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPI1
  Principia.Common.TernaryGoldbach.MPS1 Principia.Common.TernaryGoldbach.MPS2
  Principia.Common.TernaryGoldbach.MPBC Principia.Common.TernaryGoldbach.MPBD
  Principia.Common.TernaryGoldbach.MPB2

/-! ## (1) Constants -/

/-- `1 ≤ c₁ = 1 + |η'|₁UV/x ≤ 1.00004` at the second choice. -/
theorem c1_sec (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    1 ≤ c1 Y (u2 Y * v2 Y) ∧ c1 Y (u2 Y * v2 Y) ≤ 1.00004 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hUV, -, -, -, -⟩ := sdata Y hY
  obtain ⟨-, hS2, -⟩ := S_bounds
  obtain ⟨he1, he2⟩ := eta1_bounds
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hu2' : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  have hS0 : 0 ≤ 500 * Real.sqrt 6 := by positivity
  have he0 : 0 ≤ eta1 := by linarith
  unfold c1
  rw [hUV, eY]
  have e : eta1 * (500 * Real.sqrt 6 / 3 * u ^ 4) / u ^ 6 =
      eta1 * (500 * Real.sqrt 6) / (3 * u ^ 2) := by field_simp
  rw [e]
  have h0 : 0 ≤ eta1 * (500 * Real.sqrt 6) / (3 * u ^ 2) :=
    div_nonneg (mul_nonneg he0 hS0) (by positivity)
  have h1 : eta1 * (500 * Real.sqrt 6) ≤ 5.5452 * 1224.745 :=
    mul_le_mul he2 hS2 hS0 (by norm_num)
  have h2 : eta1 * (500 * Real.sqrt 6) / (3 * u ^ 2) ≤ 0.00004 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  constructor <;> linarith

/-- `2√(c₀c)/π ≤ 3.5744` for `c ≤ 1.00004`. -/
theorem kb_coefD (c : ℝ) (hc : c ≤ 1.00004) : 2 * Real.sqrt (c0 * c) / Real.pi ≤ 3.5744 := by
  have p1 := Real.pi_gt_d6
  have hs : Real.sqrt (c0 * c) ≤ 5.6145 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold c0; nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **`t·log⁺(A/t)` is increasing** on `0 < t ≤ t₀` when `log(A/t₀) ≥ 1`. -/
theorem tlogA (A t t0 : ℝ) (hA : 0 < A) (ht : 0 < t) (htt : t ≤ t0)
    (hl : 1 ≤ Real.log (A / t0)) : t * logp (A / t) ≤ t0 * Real.log (A / t0) := by
  have ht0 : 0 < t0 := lt_of_lt_of_le ht htt
  have e : Real.log (A / t) = Real.log (A / t0) + Real.log (t0 / t) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hlt : 0 ≤ Real.log (t0 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hp : logp (A / t) = Real.log (A / t) := max_eq_left (by rw [e]; linarith)
  rw [hp, e]
  have h2 := Real.log_le_sub_one_of_pos (div_pos ht0 ht)
  have h3 : t * Real.log (t0 / t) ≤ t0 - t := by
    have := mul_le_mul_of_nonneg_left h2 ht.le
    have e2 : t * (t0 / t - 1) = t0 - t := by field_simp
    linarith
  nlinarith

/-! ## (2) `cupcake3C` -/

/-- The `O*` term of `cupcake3C` at the second choice: `≤ 0.12u⁴`. -/
theorem cup_errC (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    (1 / 4 - 1 / Real.pi ^ 2) * c0 *
        ((u2 Y * v2 Y) ^ 2 * Real.log (v2 Y) / (2 * q * Y) + 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) +
          3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) * Real.log q) ≤
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
  have a2 : 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) ≤ 213 := by
    have e : u2 Y * v2 Y ^ 2 / Y = 500 * Real.sqrt 6 / 9 := by
      rw [hu2, hv2, eY, div_eq_iff (by positivity)]; ring
    rw [e]; unfold c4; linarith
  -- (a3) `(3/4)(U + 1)²V/x·log q ≤ 1.5·10⁶·4λ` (the corrected `eq:etoile`)
  have a3 : 3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) * Real.log q ≤ 1500000 * (4 * lam) := by
    have hlq : Real.log q ≤ 4 * lam := by
      have := Real.log_le_log (by linarith) hQ; linarith
    have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqR
    have hfr : 3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) ≤ 1500000 := by
      have hfr0 : (u2 Y + 1) ^ 2 * v2 Y / Y ≤ 2000000 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : (u2 Y + 1) ^ 2 ≤ 4 * u2 Y ^ 2 := by
          have := sq_nonneg (u2 Y - 1); linarith
        have e : 4 * u2 Y ^ 2 * v2 Y = 2000000 * Y := by
          rw [hu2, hv2, eY]
          have e2 : 4 * (500 * Real.sqrt 6 * u ^ 2) ^ 2 * (u ^ 2 / 3) =
              4 * (500 * Real.sqrt 6) ^ 2 / 3 * u ^ 6 := by ring
          rw [e2, hSS]; ring
        have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ v2 Y)
        linarith
      linarith
    calc 3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) * Real.log q ≤ 1500000 * Real.log q :=
          mul_le_mul_of_nonneg_right hfr hlq0
      _ ≤ 1500000 * (4 * lam) := by linarith
  have a1' : 500000 / 3 * lam * u ^ 2 ≤ 500000 / 3 * (1.5e-7 * u ^ 4) :=
    lam_u2 u lam _ hu hl2 (by norm_num)
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu1 : 8000 ^ 3 * u ≤ u ^ 4 := by
    have h3 : (8000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    calc (8000 : ℝ) ^ 3 * u ≤ u ^ 3 * u := mul_le_mul_of_nonneg_right h3 hu0.le
      _ = u ^ 4 := by ring
  have hsum : (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) + 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) +
      3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) * Real.log q ≤ 0.0256 * u ^ 4 := by
    linarith
  have hsum0 : 0 ≤ (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) + 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) +
      3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) * Real.log q := by
    have h1 : 0 ≤ (u2 Y * v2 Y) ^ 2 * LV / (2 * q * Y) :=
      div_nonneg (mul_nonneg (sq_nonneg _) hlV0) (by positivity)
    have h2 : 0 ≤ 3 * c4 / 2 * (u2 Y * v2 Y ^ 2 / Y) := by
      have : 0 ≤ u2 Y := by linarith
      unfold c4; positivity
    have h3 : 0 ≤ 3 / 4 * ((u2 Y + 1) ^ 2 * v2 Y / Y) * Real.log q :=
      mul_nonneg (mul_nonneg (by norm_num)
        (div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)))
        (Real.log_nonneg hqR)
    linarith
  have hcoef : (1 / 4 - 1 / Real.pi ^ 2) * c0 ≤ 4.687 := by
    have : 0.10132 ≤ 1 / Real.pi ^ 2 := by rw [le_div_iff₀ (by linarith)]; linarith
    unfold c0; linarith
  calc _ ≤ 4.687 * (0.0256 * u ^ 4) := mul_le_mul hcoef hsum hsum0 (by norm_num)
    _ ≤ 0.12 * u ^ 4 := by nlinarith [pow_pos hu0 4]

/-- **`cupcake3C` at the second choice**: `≤ u⁴(18λ - 23.88)` (as `MPS2.cup_le`). -/
theorem cup_leC (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y)
    (hA : Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) :
    cupcake3C Y δ q (u2 Y) (v2 Y) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (18 * Real.log (Y ^ ((1 : ℝ) / 6)) - 23.88) := by
  have h1 := cup_main Y δ q hY hq hQ hA
  have h2 := cup_errC Y q hY hq hQ
  unfold cupcake3C
  linarith

/-! ## (3) `log(UV)·eq:keks(UV)` (`|δ| ≤ 1/2c₂`, so `q > y`) -/

/-- `log UV = log(S/3) + 4λ ∈ [4λ + 5.9, 4λ + 6.04]` and `UV ≤ 408.25u⁴`. -/
theorem logUV (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    0 < u2 Y * v2 Y ∧ u2 Y * v2 Y ≤ 408.25 * (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧
      4 * Real.log (Y ^ ((1 : ℝ) / 6)) + 5.9 ≤ Real.log (u2 Y * v2 Y) ∧
      Real.log (u2 Y * v2 Y) ≤ 4 * Real.log (Y ^ ((1 : ℝ) / 6)) + 6.04 := by
  obtain ⟨hUV, -, -, -, -⟩ := sdata Y hY
  obtain ⟨hlS3, -, -, -⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨-, hS2, -⟩ := S_bounds
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hlUV : Real.log (u2 Y * v2 Y) = Real.log (500 * Real.sqrt 6 / 3) + 4 * Real.log u := by
    rw [hUV, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  refine ⟨by rw [hUV]; positivity, ?_, by rw [hlUV]; linarith, by rw [hlUV]; linarith⟩
  rw [hUV]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **(K1)** `log(UV)·(2√(c₀c₁)/π)UV ≤ u⁴(5837λ + 8814)`. -/
theorem kk_D (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    Real.log (u2 Y * v2 Y) *
        (2 * Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi * (u2 Y * v2 Y)) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (5837 * Real.log (Y ^ ((1 : ℝ) / 6)) + 8814) := by
  obtain ⟨hD0, hD, hL0, hL⟩ := logUV Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  obtain ⟨-, hc1⟩ := c1_sec Y hY
  have hk := kb_coefD _ hc1
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi := by positivity
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  calc _ ≤ (4 * lam + 6.04) * (3.5744 * (408.25 * u ^ 4)) :=
        mul_le_mul hL (mul_le_mul hk hD hD0.le (by norm_num)) (mul_nonneg hk0 hD0.le)
          (by linarith)
    _ ≤ u ^ 4 * (5837 * lam + 8814) := by nlinarith

/-- **(K2)** `log(UV)·(3c₁/2)(x/q)log⁺(UV/(c₂x/q)) ≤ u⁴(167.41λ + 252.79)` for `q > y`. -/
theorem kk_X (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    Real.log (u2 Y * v2 Y) *
        (3 * c1 Y (u2 Y * v2 Y) / 2 * (Y / q) * logp (u2 Y * v2 Y / (c2 * Y / q))) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (167.41 * Real.log (Y ^ ((1 : ℝ) / 6)) + 252.79) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hl18, hl18', -⟩ := logs_c2
  obtain ⟨hUV, -, -, -, -⟩ := sdata Y hY
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  obtain ⟨hUV0, -, hL0', hlUVb⟩ := logUV Y hY
  obtain ⟨hc1', hc1⟩ := c1_sec Y hY
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hc20 : 0 < c2 := by linarith
  have hqR : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hqy
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
  have hk : 3 * c1 Y (u2 Y * v2 Y) / 2 ≤ 1.50006 := by linarith
  have hlUV0 : 0 ≤ Real.log (u2 Y * v2 Y) := by linarith
  have hxl0 : 0 ≤ Y / q * logp (u2 Y * v2 Y / (c2 * Y / q)) :=
    mul_nonneg (by positivity) (le_max_right _ _)
  have e : Real.log (u2 Y * v2 Y) *
      (3 * c1 Y (u2 Y * v2 Y) / 2 * (Y / q) * logp (u2 Y * v2 Y / (c2 * Y / q))) =
      3 * c1 Y (u2 Y * v2 Y) / 2 * Real.log (u2 Y * v2 Y) *
        (Y / q * logp (u2 Y * v2 Y / (c2 * Y / q))) := by ring
  rw [e]
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  calc _ ≤ 1.50006 * (4 * lam + 6.04) * (6 * u ^ 4 * 4.65) :=
        mul_le_mul (mul_le_mul hk hlUVb hlUV0 (by norm_num)) hxl hxl0 (by positivity)
    _ ≤ u ^ 4 * (167.41 * lam + 252.79) := by linarith

/-- **(K3)** `log(UV)·(√(c₀c₁)/π)·q·log⁺(UV/(q/2)) ≤ u⁴(0.0807λ + 0.1219)` for `q ≤ Q`. -/
theorem kk_Q (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    Real.log (u2 Y * v2 Y) *
        (Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi * q * logp (u2 Y * v2 Y / (q / 2))) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (0.0807 * Real.log (Y ^ ((1 : ℝ) / 6)) + 0.1219) := by
  obtain ⟨d0, d1⟩ := x3_le Y q hY hq hQ
  obtain ⟨-, hc1⟩ := c1_sec Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hk := kb_coefD _ hc1
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi := by positivity
  have e : Real.log (u2 Y * v2 Y) *
      (Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi * q * logp (u2 Y * v2 Y / (q / 2))) =
      2 * Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi *
        ((q : ℝ) * (Real.log (u2 Y * v2 Y) / 2 * logp (u2 Y * v2 Y / (q / 2)))) := by ring
  rw [e]
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  calc _ ≤ 3.5744 * ((4 * lam + 6.04) / 2 * (u ^ 4 / 1224.7445 * 13.82)) :=
        mul_le_mul hk d1 d0 (by norm_num)
    _ ≤ u ^ 4 * (0.0807 * lam + 0.1219) := by ring_nf; linarith

/-- **(K4)** `log(UV)·(2|η'|₁/π)·q·max(1, …) ≤ 0.0230591u⁴λ²` for `q ≤ Q`. -/
theorem kk_M (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    Real.log (u2 Y * v2 Y) * (2 * eta1 / Real.pi * q *
        max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y)))) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (0.0230591 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2) := by
  obtain ⟨-, hQu, -, -, -⟩ := sdata Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  obtain ⟨-, -, hL0', hL⟩ := logUV Y hY
  have hmax := k3_max_sec Y q hY hq hQ
  have heta := eta_pi
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
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
  have hu4 : 0 ≤ u ^ 4 := by positivity
  have hL0 : 0 ≤ Real.log (u2 Y * v2 Y) := by linarith
  calc _ ≤ (4 * lam + 6.04) * (3.53018 * (u ^ 4 / 1224.7445) * (2 * lam - 11)) :=
        mul_le_mul hL hA hA0 (by linarith)
    _ = u ^ 4 * (3.53018 / 1224.7445 * ((4 * lam + 6.04) * (2 * lam - 11))) := by ring
    _ ≤ u ^ 4 * (0.0230591 * lam ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hu4
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
        nlinarith [sq_nonneg lam]

/-- **(K5)** `log(UV)·(2√(3c₀c₁)/π + 3c₁/2c₂ + 55c₀c₂/6π²)·q ≤ u⁴(0.0922λ + 0.1391)`. -/
theorem kk_R (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y) :
    Real.log (u2 Y * v2 Y) *
        ((2 * Real.sqrt (3 * c0 * c1 Y (u2 Y * v2 Y)) / Real.pi +
            3 * c1 Y (u2 Y * v2 Y) / (2 * c2) + 55 * c0 * c2 / (6 * Real.pi ^ 2)) * q) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (0.0922 * Real.log (Y ^ ((1 : ℝ) / 6)) + 0.1391) := by
  obtain ⟨-, hQu, -, -, -⟩ := sdata Y hY
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  obtain ⟨-, -, hL0', hL⟩ := logUV Y hY
  obtain ⟨hc1', hc1⟩ := c1_sec Y hY
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨p1, p2⟩ := pi_sq_bounds
  have hpi := Real.pi_gt_d6
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  have hu0 : 0 < u := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqu : (q : ℝ) ≤ u ^ 4 / 1224.7445 := hQ.trans hQu
  have hs : Real.sqrt (3 * c0 * c1 Y (u2 Y * v2 Y)) ≤ 9.73 := by
    rw [Real.sqrt_le_left (by norm_num)]; unfold c0; nlinarith
  have k1 : 2 * Real.sqrt (3 * c0 * c1 Y (u2 Y * v2 Y)) / Real.pi ≤ 6.2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have k2 : 3 * c1 Y (u2 Y * v2 Y) / (2 * c2) ≤ 2.235 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have k3 : 55 * c0 * c2 / (6 * Real.pi ^ 2) ≤ 19.7 := by
    rw [div_le_iff₀ (by linarith)]; unfold c0; nlinarith
  have hcoef0 : 0 ≤ 2 * Real.sqrt (3 * c0 * c1 Y (u2 Y * v2 Y)) / Real.pi +
      3 * c1 Y (u2 Y * v2 Y) / (2 * c2) + 55 * c0 * c2 / (6 * Real.pi ^ 2) := by
    have k2' : 0 ≤ 3 * c1 Y (u2 Y * v2 Y) / (2 * c2) := div_nonneg (by linarith) (by linarith)
    have k3' : 0 ≤ 55 * c0 * c2 / (6 * Real.pi ^ 2) :=
      div_nonneg (by unfold c0; nlinarith) (by positivity)
    have k1' : 0 ≤ 2 * Real.sqrt (3 * c0 * c1 Y (u2 Y * v2 Y)) / Real.pi := by positivity
    linarith
  have hcq : (2 * Real.sqrt (3 * c0 * c1 Y (u2 Y * v2 Y)) / Real.pi +
      3 * c1 Y (u2 Y * v2 Y) / (2 * c2) + 55 * c0 * c2 / (6 * Real.pi ^ 2)) * q ≤
      28.2 * (u ^ 4 / 1224.7445) :=
    mul_le_mul (by linarith) hqu (by positivity) (by norm_num)
  have hL0 : 0 ≤ Real.log (u2 Y * v2 Y) := by linarith
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg (by positivity) (by linarith)
  have hu4 : 0 ≤ u ^ 4 := by positivity
  calc _ ≤ (4 * lam + 6.04) * (28.2 * (u ^ 4 / 1224.7445)) :=
        mul_le_mul hL hcq (mul_nonneg hcoef0 (by positivity)) (by linarith)
    _ ≤ u ^ 4 * (0.0922 * lam + 0.1391) := by ring_nf; linarith

/-- **`log(UV)·eq:keks(UV)` at the second choice** (`y < q ≤ Q`):
`≤ u⁴(0.0230591λ² + 6004.6λ + 9067.1)`. -/
theorem kk_le (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hQ : (q : ℝ) ≤ q2 Y)
    (hqy : (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 < q) :
    Real.log (u2 Y * v2 Y) * keks Y q (u2 Y * v2 Y) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 *
      (0.0230591 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 +
        6004.6 * Real.log (Y ^ ((1 : ℝ) / 6)) + 9067.1) := by
  have h1 := kk_D Y hY
  have h2 := kk_X Y q hY hqy
  have h3 := kk_Q Y q hY hq hQ
  have h4 := kk_M Y q hY hq hQ
  have h5 := kk_R Y q hY hq hQ
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hu4 : (0 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
  have hul : (0 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 * Real.log (Y ^ ((1 : ℝ) / 6)) :=
    mul_nonneg hu4 (by linarith)
  unfold keks
  rw [mul_add, mul_add, mul_add, mul_add]
  linarith

/-! ## (4) `tvorogD` at `ε = 0.01` (`|δ| > 1/2c₂`) -/

set_option maxHeartbeats 800000 in
-- seven nonlinear bounds on one large expression, each closed by `linarith`
/-- **`tvorogD` at the second choice, `ε = 0.01`**: `≤ u⁴(6310.5λ + 8181)`. -/
theorem tvD_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hQ : (q : ℝ) ≤ q2 Y)
    (hdq : |δ| * q ≤ u2 Y) (hD : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ |δ| * q) :
    tvorogD Y δ q (u2 Y) (v2 Y) 0.01 ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (6310.5 * Real.log (Y ^ ((1 : ℝ) / 6)) + 8181) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hdq0, hKlo, hKhi⟩ := K_bounds Y (|δ| * q) hY hdq hD
  obtain ⟨hUV, hQu, -, -, -⟩ := sdata Y hY
  obtain ⟨hS1, hS2, hSS⟩ := S_bounds
  obtain ⟨-, hU2, -, hl1, -, hu8⟩ := kdata Y hY
  obtain ⟨hD0, hDle, hL0', hL⟩ := logUV Y hY
  obtain ⟨hc1a, hc1⟩ := c1_sec Y hY
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨p1, p2⟩ := pi_sq_bounds
  have hk := kb_coefD _ hc1
  have hu := u_ge Y hY
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  unfold tvorogD
  set k := 2 * Real.sqrt (c0 * c1 Y (u2 Y * v2 Y)) / Real.pi with hk_def
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  set K := Y / (|δ| * q) with hK_def
  set D := u2 Y * v2 Y with hD_def
  set L := Real.log D with hL_def
  set P := logp (2 * D / K) with hP_def
  set Lm := Real.log (min D ((3 + 2 * 0.01) * K / 2)) with hLm_def
  have hu0 : 0 < u := by linarith
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu40 : 0 ≤ u ^ 4 := by positivity
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg hu40 (by linarith)
  have hk0 : 0 ≤ k := by rw [hk_def]; positivity
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hKlo
  have hL0 : 0 ≤ L := by linarith
  have hP0 : 0 ≤ P := le_max_right _ _
  -- `D log(D/e) = D(L - 1) ∈ [0, 408.25u⁴(4λ + 5.04)]`
  have hDe : D * Real.log (D / Real.exp 1) = D * (L - 1) := by
    rw [Real.log_div hD0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have b1 : D * Real.log (D / Real.exp 1) ≤ 408.25 * u ^ 4 * (4 * lam + 5.04) := by
    rw [hDe]; exact mul_le_mul hDle (by linarith) (by linarith) (by positivity)
  have b10 : 0 ≤ D * Real.log (D / Real.exp 1) := by
    rw [hDe]; exact mul_nonneg hD0.le (by linarith)
  -- `0 ≤ Lm ≤ 4λ + 2.61`
  have hD1 : 1 ≤ D := by
    rw [hUV]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hK1 : (1 : ℝ) ≤ u ^ 4 / 1224.745 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hmin1 : 1 ≤ min D ((3 + 2 * 0.01) * K / 2) := le_min hD1 (by linarith)
  have hLm0 : 0 ≤ Lm := Real.log_nonneg hmin1
  have hLm : Lm ≤ 4 * lam + 2.61 := by
    have h1 : min D ((3 + 2 * 0.01) * K / 2) ≤ 12.16758 * u ^ 4 :=
      (min_le_right _ _).trans (by linarith)
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
    have h3 := log_le_pow2 12.16758 3 (by norm_num)
    norm_num at h2 h3
    linarith
  have b3 : K * Lm ≤ 8.058 * u ^ 4 * (4 * lam + 2.61) :=
    mul_le_mul hKhi hLm hLm0 (by positivity)
  -- `K·P ≤ 8.058u⁴·4.65`
  have hA0 : 0 < 2 * D := by linarith
  have hlA : Real.log (2 * D / (8.058 * u ^ 4)) ≤ 4.65 ∧
      1 ≤ Real.log (2 * D / (8.058 * u ^ 4)) := by
    have e : 2 * D / (8.058 * u ^ 4) = 2 * (500 * Real.sqrt 6 / 3) / 8.058 := by
      rw [hUV, div_eq_div_iff (by positivity) (by norm_num)]; ring
    rw [e]
    refine ⟨?_, ?_⟩
    · have := log_le_pow2 (2 * (500 * Real.sqrt 6 / 3) / 8.058) 7 (by positivity)
      norm_num at this ⊢; linarith
    · rw [Real.le_log_iff_exp_le (by positivity)]
      have : (2.72 : ℝ) ≤ 2 * (500 * Real.sqrt 6 / 3) / 8.058 := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
  have b4 : K * P ≤ 8.058 * u ^ 4 * 4.65 := by
    have := tlogA (2 * D) K (8.058 * u ^ 4) hA0 hK0 hKhi hlA.2
    have h2 := mul_le_mul_of_nonneg_left hlA.1 (by positivity : (0 : ℝ) ≤ 8.058 * u ^ 4)
    linarith
  have b40 : 0 ≤ K * P := mul_nonneg hK0.le hP0
  -- `P ≤ 13.82` (`K ≥ Q`)
  have hP : P ≤ 13.82 := by
    have h1 : 2 * D / K ≤ 1000001 := by
      rw [div_le_iff₀ hK0]
      have h2 : 2 * D = 2 * (500 * Real.sqrt 6 / 3) * u ^ 4 := by rw [hUV]; ring
      have h3 : 2 * (500 * Real.sqrt 6 / 3) * u ^ 4 ≤ 1000001 * (u ^ 4 / 1224.745) := by
        rw [show 1000001 * (u ^ 4 / 1224.745) = 1000001 / 1224.745 * u ^ 4 by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) hu40
      have h4 := mul_le_mul_of_nonneg_left hKlo (by norm_num : (0 : ℝ) ≤ 1000001)
      linarith
    have h0 : 0 < 2 * D / K := div_pos hA0 hK0
    have h6 := Real.log_le_log h0 h1
    have h7 := log_le_pow2 1000001 20 (by norm_num)
    norm_num at h7
    exact max_le (by linarith) (by norm_num)
  -- the `√x`-free remainders
  have hdq' : |δ| * q ≤ 1225 * u ^ 2 := hdq.trans hU2
  have hu2u4 : u ^ 2 ≤ u ^ 4 / 6.4e7 := by
    rw [le_div_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hu8 (sq_nonneg u)
    nlinarith
  have b6 : 3 * c1 Y D * (|δ| * q) * L * (1 + (1 + 0.01) / (2 * 0.01) * P) ≤
      u ^ 4 * (0.161 * lam + 0.243) := by
    have e50 : (1 + 0.01 : ℝ) / (2 * 0.01) = 50.5 := by norm_num
    have hq1 : 1 + (1 + 0.01) / (2 * 0.01) * P ≤ 698.91 := by rw [e50]; linarith
    have hq10 : 0 ≤ 1 + (1 + 0.01) / (2 * 0.01) * P := by rw [e50]; linarith
    have hc : 3 * c1 Y D ≤ 3.00012 := by linarith
    calc 3 * c1 Y D * (|δ| * q) * L * (1 + (1 + 0.01) / (2 * 0.01) * P) ≤
          3.00012 * (1225 * u ^ 2) * (4 * lam + 6.04) * 698.91 :=
          mul_le_mul (mul_le_mul (mul_le_mul hc hdq' (by positivity) (by norm_num)) hL hL0
            (by positivity)) hq1 hq10 (mul_nonneg (by positivity) (by linarith))
      _ = 3.00012 * 1225 * 698.91 * (u ^ 2 * (4 * lam + 6.04)) := by ring
      _ ≤ 3.00012 * 1225 * 698.91 * (u ^ 4 / 6.4e7 * (4 * lam + 6.04)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right hu2u4 (by linarith)
      _ ≤ u ^ 4 * (0.161 * lam + 0.243) := by linarith
  have b7 : 35 * c0 * c2 / (3 * Real.pi ^ 2) * q * L ≤ u ^ 4 * (0.082 * lam + 0.124) := by
    have hc : 35 * c0 * c2 / (3 * Real.pi ^ 2) ≤ 25.1 := by
      rw [div_le_iff₀ (by linarith)]; unfold c0; nlinarith
    have hc0 : 0 ≤ 35 * c0 * c2 / (3 * Real.pi ^ 2) := by
      have : 0 ≤ c2 := by linarith
      unfold c0; positivity
    have hqu : (q : ℝ) ≤ u ^ 4 / 1224.7445 := hQ.trans hQu
    calc 35 * c0 * c2 / (3 * Real.pi ^ 2) * q * L ≤
          25.1 * (u ^ 4 / 1224.7445) * (4 * lam + 6.04) :=
          mul_le_mul (mul_le_mul hc hqu (by positivity) (by norm_num)) hL hL0 (by positivity)
      _ ≤ u ^ 4 * (0.082 * lam + 0.124) := by ring_nf; linarith
  -- the bracket
  have hs3 : Real.sqrt (3 + 2 * 0.01) ≤ 1.73782 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs30 : 0 ≤ Real.sqrt (3 + 2 * 0.01) := Real.sqrt_nonneg _
  have c1' : (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm) ≤
      1.01 * (1.73782 * (8.058 * u ^ 4 * (4 * lam + 2.61))) := by
    have h := mul_le_mul hs3 b3 (mul_nonneg hK0.le hLm0) (by norm_num)
    calc (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm) =
          1.01 * (Real.sqrt (3 + 2 * 0.01) * (K * Lm)) := by ring
      _ ≤ 1.01 * (1.73782 * (8.058 * u ^ 4 * (4 * lam + 2.61))) := by linarith
  have c2' : (1 + 0.01) * K * (2 * P + L / 2 * P) ≤
      1.01 * (2 + (4 * lam + 6.04) / 2) * (8.058 * u ^ 4 * 4.65) := by
    have e : (1 + 0.01) * K * (2 * P + L / 2 * P) = 1.01 * (2 + L / 2) * (K * P) := by ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) b4 b40
      (by linarith)
  have hbrk : D * Real.log (D / Real.exp 1) + K / 2 +
      (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm + 2 * P + L / 2 * P) ≤
      u ^ 4 * (1765.3 * lam + 2288.6) := by
    have e : (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm + 2 * P + L / 2 * P) =
        (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm) +
          (1 + 0.01) * K * (2 * P + L / 2 * P) := by ring
    rw [e]
    linarith
  have hbrk0 : 0 ≤ D * Real.log (D / Real.exp 1) + K / 2 +
      (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm + 2 * P + L / 2 * P) := by
    have h1 : 0 ≤ Real.sqrt (3 + 2 * 0.01) * Lm + 2 * P + L / 2 * P := by
      have h2 := mul_nonneg hs30 hLm0
      have h3 : 0 ≤ L / 2 * P := mul_nonneg (by linarith) hP0
      linarith
    have : 0 ≤ (1 + 0.01) * K * (Real.sqrt (3 + 2 * 0.01) * Lm + 2 * P + L / 2 * P) :=
      mul_nonneg (by linarith) h1
    linarith
  have hkb := mul_le_mul hk hbrk hbrk0 (by norm_num)
  linarith

/-! ## (5) The totals -/

/-- The final comparison for `|δ| ≤ 1/2c₂`. -/
theorem fin1D (u lam C P : ℝ) (hu4 : 0 ≤ u ^ 4) (hl : 8.3 ≤ lam)
    (hC : C ≤ u ^ 4 * (18 * lam - 23.88))
    (hP : P ≤ u ^ 4 * (0.0230591 * lam ^ 2 + 6004.6 * lam + 9067.1)) :
    C + P ≤ 1230.9 * u ^ 4 * (6 * lam) + 0.0006406 * u ^ 4 * (6 * lam) ^ 2 := by
  have h : 0 ≤ u ^ 4 * (0.0000025 * lam ^ 2 + 1362.8 * lam - 9043.22) :=
    mul_nonneg hu4 (by nlinarith [sq_nonneg lam])
  linarith

/-- The final comparison for `|δ| > 1/2c₂`. -/
theorem fin2D (u lam C T : ℝ) (hu4 : 0 ≤ u ^ 4) (hl : 8.3 ≤ lam)
    (hC : C ≤ u ^ 4 * (18 * lam - 23.88))
    (hT : T ≤ u ^ 4 * (6310.5 * lam + 8181)) :
    C + T ≤ 1230.9 * u ^ 4 * (6 * lam) + 0.0006406 * u ^ 4 * (6 * lam) ^ 2 := by
  have h : 0 ≤ u ^ 4 * (0.0230616 * lam ^ 2 + 1056.9 * lam - 8157.12) :=
    mul_nonneg hu4 (by nlinarith [sq_nonneg lam])
  linarith

/-- **Link [SecI2ArithD] — NUMERIC: `S_{I,2}` at the second choice from the CORRECTED
`lem:bogus`** (`MPBD.BogusEta2D`'s two bounds at `U = u2`, `V = v2`, `ε = 0.01`). -/
def SecI2ArithD : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y → |δ| * q ≤ u2 Y →
    (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) →
      (|δ| ≤ 1 / (2 * c2) →
        cupcake3C Y δ q (u2 Y) (v2 Y) +
            Real.log (u2 Y * v2 Y) * keks Y q (u2 Y * v2 Y) ≤
          1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y +
            0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2) ∧
      (1 / (2 * c2) < |δ| →
        cupcake3C Y δ q (u2 Y) (v2 Y) + tvorogD Y δ q (u2 Y) (v2 Y) 0.01 ≤
          1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y +
            0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2)

/-- **`SecI2ArithD`, PROVED.** -/
theorem secI2ArithD : SecI2ArithD := by
  intro Y hY δ q hq hQ hdq hA
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hc := cup_leC Y δ q hY hq hQ hA
  have hu4 : (0 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [e23, eL]
    exact fin1D _ _ _ _ hu4 hl1 hc (kk_le Y q hY hq hQ (q_gt_y Y δ q hY hA hd))
  · rw [e23, eL]
    exact fin2D _ _ _ _ hu4 hl1 hc (tvD_le Y δ q hY hQ hdq (dq_lower Y δ q hY hA hd))

/-! ## (6) `SecI2At` from the corrected `lem:bogus` -/

/-- **`MPc.SecI2At` from `BogusEta2D` and `SecI2ArithD`, PROVED.** -/
theorem secI2At_ofD (hb : BogusEta2D) (ha : SecI2ArithD) : SecI2At := by
  intro Y hY α δ a q ⟨hq, hga, h2, hQ, hδ, hA⟩
  obtain ⟨h16, -, hsqQ, -, -, -, he2, hU1, hV1, hUV, -⟩ := sec_hyps Y hY
  have hdq := dq_le_u2 Y δ q hY hq hδ
  obtain ⟨hk, ht⟩ := hb Y α δ (q2 Y) (u2 Y) (v2 Y) a q hq hga h2 hδ hQ h16 hsqQ he2 hU1 hV1
    hUV
  obtain ⟨hak, hat⟩ := ha Y hY δ q hq hQ hdq hA
  rcases le_or_gt |δ| (1 / (2 * c2)) with hd | hd
  · exact (hk (Or.inl hd)).trans (hak hd)
  · exact (ht hd.le 0.01 (by norm_num) (by norm_num)).trans (hat hd)

/-- **`MPc.SecI2At` from the corrected `lem:bogus` alone, PROVED.** -/
theorem secI2At_of_genD (hb : BogusEta2D) : SecI2At :=
  secI2At_ofD hb secI2ArithD

/-- **`MPc.SecI2At` from `TrompaisEta2`, `MainBogusEta2C` and `EsthelBogusED`, PROVED**
(`EsthelBogusKD` is `MPBD.esthelBogusKD_holds`). -/
theorem secI2At_of_linksD (h1 : TrompaisEta2) (h2 : MainBogusEta2C) (he : EsthelBogusED) :
    SecI2At :=
  secI2At_of_genD (bogusEta2D_of h1 h2 esthelBogusKD_holds he)

end Principia.Common.TernaryGoldbach.MPSD
