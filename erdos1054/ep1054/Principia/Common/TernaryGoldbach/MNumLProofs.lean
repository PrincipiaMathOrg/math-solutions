/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumL

set_option autoImplicit false

/-!
# `OL.MNumL HW.phi 8.54 0.8095 0.6406` — the discharges (`mnumL_proved`)

GENERATED numerics (`scratchpad/mnl/gen_mnl.py`) around hand-written far-regime lemmas; the
evaluation-point logarithms are `MC`'s (`MC.lgp…`), reused by import.

* **`GTNonnegL`**: `ML.gTL_nonneg_r0`.
* **`G0EnvL`, `T1BlkL`**: a corrected region envelope `envLR…` at `r₀` or at
  `r₁(y) ∈ [r̲, r̄]`, evaluated on a box by `MC.envF_le_box`.
* **`IGBlkL`**: `∫_{r₀}^{r₁(y)} g̃_L/r` split over the regions (`MC.intBnd_add`), each bounded by
  the exact antiderivative of its envelope (`MC.intBnd_region`), `envG` from above/below at the
  ends and increasing (`MC.envG_mono`) up to `r̄ ≥ r₁(y)`.
* **The far regime `x ≥ 4.9·10²⁸`** (`far_T1L`, `far_IGL`): `MC.far_T1`/`MC.far_IG` on `gTL`, with
  `felipa(x) ≤ 1.36073·K` at slope `0.6406` (`far_felL`).
-/

namespace Principia.Common.TernaryGoldbach.ML

open MinSp MeasureTheory Set MC

/-- **Link [g̃_L ≥ 0] DISCHARGED** (`gTL_nonneg_r0`). -/
theorem gtNonnegL : GTNonnegL := fun y hy => gTL_nonneg_r0 y hy

/-! ## The far regime `x ≥ 4.9·10²⁸` at slope `0.6406` -/

/-- **`felipa(x) ≤ 1.36073·K(x/49)`** at slope `0.6406` for `x ≥ 4.9·10²⁸`
(`0.6406·log 49 − 0.021095 ≤ 0.039765·62.169796`, `MC.log49_le`, `MN.log_1e27`). -/
theorem far_felL (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) : felL x ≤ 1.36073 * kK (x / 49) := by
  have hyY : 10 ^ 27 ≤ x / 49 := MN.y_ge_of x _ hx
  have hy0 : 0 < x / 49 := lt_of_lt_of_le (by norm_num) hyY
  obtain ⟨hYl, -⟩ := MN.log_1e27
  have hv : 62.169796 ≤ Real.log (x / 49) := hYl.trans (Real.log_le_log (by norm_num) hyY)
  have h49 := log49_le
  have hlx : Real.log x = Real.log 49 + Real.log (x / 49) := by
    rw [← Real.log_mul (by norm_num) hy0.ne']
    congr 1
    ring
  unfold felL kK
  rw [hlx]
  linarith

set_option maxHeartbeats 1000000 in
-- `far_T1L` chains ~20 nonlinear steps through `gcongr` and `linarith` (as `MC.far_T1`)
/-- **The far `T₁` on the corrected `L`**, generic in a far envelope with nonnegative coefficients
(quadratic `P`): `coefC(x)·felipa(x)·g̃_L(x/49, r₁) ≤ (7/15)·1.36073·(…)` for `x ≥ 4.9·10²⁸`, from
`coefC ≤ 7/15` (`MC.coefC_far`), `felipa ≤ 1.36073K` (`far_felL`), `ℓ = log r₁ ≤ (8/15)K`,
`√r₁ ≥ 0.61237t`, `r₁ ≥ (3/8)·3981·t` and `MC.far_kp`. -/
theorem far_T1L (p0 p1 p2 q0 q1 q2 zF : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hz : 0 ≤ zF)
    (henv : ∀ y : ℝ, 10 ^ 27 ≤ y →
      OL.gTL HW.phi y (r1y y) ≤ envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y))
    (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    OC.coefC x * felL x * OL.gTL HW.phi (x / 49) (r1y (x / 49)) ≤
      7 / 15 * 1.36073 * ((p0 * (7.54482 / 31.084898 ^ 2) + p1 * (8 / 15) * (7.54482 / 31.084898) +
        p2 * (8 / 15) ^ 2 * 7.54482) / 0.61237 +
        (q0 * (7.54482 / 31.084898 ^ 2) + q1 * (8 / 15) * (7.54482 / 31.084898) +
          q2 * (8 / 15) ^ 2 * 7.54482) / (3 / 8 * 3981) +
        zF * (7.54482 / 31.084898 ^ 2 / 7.9)) := by
  have hyY : 10 ^ 27 ≤ x / 49 := MN.y_ge_of x _ hx
  set y := x / 49 with hyd
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  obtain ⟨hsY, hr1, -⟩ := MN.far_s y hyY
  obtain ⟨k1, k2, k3, k4, hK⟩ := far_kp y hyY
  obtain ⟨hc0, hc1⟩ := coefC_far x hx
  have hfel := far_felL x hx
  have hfel0 : 0 ≤ felL x := by
    have := LW.log_ge_of x (le_trans (by norm_num) hx)
    unfold felL
    linarith
  set t := y ^ ((2 : ℝ) / 15) with htd
  set K := kK y with hKd
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < r1y y := by rw [hr1]; positivity
  have hl0 : 0 ≤ Real.log (r1y y) := Real.log_nonneg (by rw [hr1]; nlinarith)
  have hlK : Real.log (r1y y) ≤ 8 / 15 * K := by
    rw [MN.log_r1y y hy0]
    have : Real.log (3 / 8) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    rw [hKd]
    unfold kK
    linarith
  have hsq : 0.61237 * t ≤ Real.sqrt (r1y y) := by
    rw [hr1, Real.sqrt_mul (by norm_num) (t ^ 2), Real.sqrt_sq ht0.le]
    have : (0.61237 : ℝ) ≤ Real.sqrt (3 / 8) := MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)
    nlinarith
  have hr1s : 3 / 8 * 3981 * t ≤ r1y y := by
    rw [hr1]
    nlinarith
  set l := Real.log (r1y y) with hld
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  have hE := henv y hyY
  have hPl : K * (p0 + p1 * l + p2 * l ^ 2) ≤
      p0 * K + p1 * (8 / 15) * K ^ 2 + p2 * (8 / 15) ^ 2 * K ^ 3 := by
    have a1 : K * (p1 * l) ≤ K * (p1 * (8 / 15 * K)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlK hp1) hK0.le
    have a2 : K * (p2 * l ^ 2) ≤ K * (p2 * (8 / 15 * K) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hl0 hlK 2) hp2) hK0.le
    nlinarith
  have hQl : K * (q0 + q1 * l + q2 * l ^ 2) ≤
      q0 * K + q1 * (8 / 15) * K ^ 2 + q2 * (8 / 15) ^ 2 * K ^ 3 := by
    have a1 : K * (q1 * l) ≤ K * (q1 * (8 / 15 * K)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlK hq1) hK0.le
    have a2 : K * (q2 * l ^ 2) ≤ K * (q2 * (8 / 15 * K) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hl0 hlK 2) hq2) hK0.le
    nlinarith
  have hP0 : 0 ≤ p0 + p1 * l + p2 * l ^ 2 := by positivity
  have hQ0 : 0 ≤ q0 + q1 * l + q2 * l ^ 2 := by positivity
  have hsr0 : 0 < Real.sqrt (r1y y) := lt_of_lt_of_le (by positivity) hsq
  have tP : K * ((p0 + p1 * l + p2 * l ^ 2) / Real.sqrt (r1y y)) ≤
      (p0 * (K / t) + p1 * (8 / 15) * (K ^ 2 / t) + p2 * (8 / 15) ^ 2 * (K ^ 3 / t)) / 0.61237 := by
    rw [← mul_div_assoc]
    calc K * (p0 + p1 * l + p2 * l ^ 2) / Real.sqrt (r1y y) ≤
          (p0 * K + p1 * (8 / 15) * K ^ 2 + p2 * (8 / 15) ^ 2 * K ^ 3) / (0.61237 * t) :=
          div_le_div₀ (by positivity) hPl (by positivity) hsq
      _ = _ := by ring
  have tQ : K * ((q0 + q1 * l + q2 * l ^ 2) / r1y y) ≤
      (q0 * (K / t) + q1 * (8 / 15) * (K ^ 2 / t) + q2 * (8 / 15) ^ 2 * (K ^ 3 / t)) /
        (3 / 8 * 3981) := by
    rw [← mul_div_assoc]
    calc K * (q0 + q1 * l + q2 * l ^ 2) / r1y y ≤
          (q0 * K + q1 * (8 / 15) * K ^ 2 + q2 * (8 / 15) ^ 2 * K ^ 3) / (3 / 8 * 3981 * t) :=
          div_le_div₀ (by positivity) hQl (by positivity) hr1s
      _ = _ := by ring
  have tP2 : (p0 * (K / t) + p1 * (8 / 15) * (K ^ 2 / t) + p2 * (8 / 15) ^ 2 * (K ^ 3 / t)) /
      0.61237 ≤ (p0 * (7.54482 / 31.084898 ^ 2) + p1 * (8 / 15) * (7.54482 / 31.084898) +
        p2 * (8 / 15) ^ 2 * 7.54482) / 0.61237 := by
    gcongr
  have tQ2 : (q0 * (K / t) + q1 * (8 / 15) * (K ^ 2 / t) + q2 * (8 / 15) ^ 2 * (K ^ 3 / t)) /
      (3 / 8 * 3981) ≤ (q0 * (7.54482 / 31.084898 ^ 2) + q1 * (8 / 15) * (7.54482 / 31.084898) +
        q2 * (8 / 15) ^ 2 * 7.54482) / (3 / 8 * 3981) := by
    gcongr
  have tZ : K * (zF * y ^ (-(1 : ℝ) / 6)) ≤ zF * (7.54482 / 31.084898 ^ 2 / 7.9) := by
    have := mul_le_mul_of_nonneg_left k4 hz
    linarith
  have hEn : envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) =
      (p0 + p1 * l + p2 * l ^ 2) / Real.sqrt (r1y y) + (q0 + q1 * l + q2 * l ^ 2) / r1y y +
        zF * y ^ (-(1 : ℝ) / 6) := by
    unfold envF
    ring
  have hE0 : 0 ≤ envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) := by
    rw [hEn]
    positivity
  have hKE : K * envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) ≤
      (p0 * (7.54482 / 31.084898 ^ 2) + p1 * (8 / 15) * (7.54482 / 31.084898) +
        p2 * (8 / 15) ^ 2 * 7.54482) / 0.61237 +
        (q0 * (7.54482 / 31.084898 ^ 2) + q1 * (8 / 15) * (7.54482 / 31.084898) +
          q2 * (8 / 15) ^ 2 * 7.54482) / (3 / 8 * 3981) +
        zF * (7.54482 / 31.084898 ^ 2 / 7.9) := by
    rw [hEn, mul_add, mul_add]
    linarith
  have hcf : OC.coefC x * felL x ≤ 7 / 15 * (1.36073 * K) :=
    mul_le_mul hc1 hfel hfel0 (by norm_num)
  calc OC.coefC x * felL x * OL.gTL HW.phi y (r1y y) ≤
        OC.coefC x * felL x * envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg hc0 hfel0)
    _ ≤ 7 / 15 * (1.36073 * K) *
          envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) :=
        mul_le_mul_of_nonneg_right hcf hE0
    _ = 7 / 15 * 1.36073 *
          (K * envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hKE (by norm_num)

/-- **The far `∫ g̃_L/r`**: `[r₀, 5.94·10⁶]` by the base regions (`hbase`), then the far envelope
up to `r₁(y)`: `envG(r₁) ≤ z·log r₁` (its `S, T ≥ 0`), `envG(r_F) ≥ −2S̄/s̲ − T̄/r_F`, and
`z·log r₁ ≤ z_F·(8/15)K·y^{−1/6}` (`MC.far_kp`); the proof of `MC.far_IG` on `OL.intGTL`. -/
theorem far_IGL (p0 p1 p2 q0 q1 q2 zF Ib Sh Th sl : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (hp2 : 0 ≤ p2) (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hz : 0 ≤ zF)
    (henv : ∀ y r : ℝ, 10 ^ 27 ≤ y → 5940000 ≤ r → r ≤ r1y y →
      OL.gTL HW.phi y r ≤ envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) r)
    (hbase : ∀ y : ℝ, 10 ^ 27 ≤ y →
      IntBnd (fun r => OL.gTL HW.phi y r / r) 150000 5940000 Ib)
    (hsl0 : 0 < sl) (hsl : sl ≤ Real.sqrt 5940000)
    (hS : (p0 + 2 * p1 + 8 * p2 + 48 * 0 + 384 * 0) +
      (p1 + 4 * p2 + 24 * 0 + 192 * 0) * Real.log 5940000 +
      (p2 + 6 * 0 + 48 * 0) * Real.log 5940000 ^ 2 + (0 + 8 * 0) * Real.log 5940000 ^ 3 +
      0 * Real.log 5940000 ^ 4 ≤ Sh) (hSh : 0 ≤ Sh)
    (hT : (q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log 5940000 + q2 * Real.log 5940000 ^ 2 ≤ Th)
    (y : ℝ) (hyY : 10 ^ 27 ≤ y) :
    OL.intGTL HW.phi y ≤ Ib + (2 * (Sh / sl) + Th / 5940000) +
      zF * (8 / 15 * (7.54482 / 31.084898 ^ 2 / 7.9)) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  have hr1 : 5940000 ≤ r1y y := MN.r1_ge_of y 5940000 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hyY 4))
  have hY6 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  have hzy : 0 ≤ zF * y ^ (-(1 : ℝ) / 6) := mul_nonneg hz hY6
  have hpos : ∀ r ∈ Icc (5940000 : ℝ) (r1y y),
      0 ≤ envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) r := by
    intro r hr
    have hl : 0 ≤ Real.log r := Real.log_nonneg (by linarith [hr.1])
    exact envF_nonneg _ _ _ _ _ _ _ _ _ r (by linarith [hr.1]) (by positivity) (by positivity) hzy
  have hreg := intBnd_region (OL.gTL HW.phi y) 5940000 (r1y y) p0 p1 p2 0 0 q0 q1 q2
    (zF * y ^ (-(1 : ℝ) / 6)) (by norm_num) hr1 (fun r hr => henv y r hyY hr.1 hr.2) hpos
  have hsum := intBnd_add _ _ _ _ _ _ (hbase y hyY) hreg
  have hI := le_of_intBnd _ _ _ _ hsum
  have hr0 : 0 < r1y y := by linarith
  have hl1 : 0 ≤ Real.log (r1y y) := Real.log_nonneg (by linarith)
  have hu := envG_ub p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y)
    (Real.sqrt (r1y y)) 0 0 (Real.log (r1y y)) hr0 le_rfl (by positivity) le_rfl
    (by positivity) hzy le_rfl
  have hl := envG_lb p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) 5940000 sl Sh Th 0
    (by norm_num) hsl0 hsl hS hSh hT hzy (Real.log_nonneg (by norm_num))
  obtain ⟨-, -, -, k4, hK⟩ := far_kp y hyY
  have hlK : Real.log (r1y y) ≤ 8 / 15 * kK y := by
    rw [MN.log_r1y y hy0]
    have : Real.log (3 / 8) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    unfold kK
    linarith
  have hzl : zF * y ^ (-(1 : ℝ) / 6) * Real.log (r1y y) ≤
      zF * (8 / 15 * (7.54482 / 31.084898 ^ 2 / 7.9)) := by
    have a1 := mul_le_mul_of_nonneg_left hlK hzy
    have a2 := mul_le_mul_of_nonneg_left k4 hz
    nlinarith
  have z1 : (0 : ℝ) / Real.sqrt (r1y y) = 0 := zero_div _
  have z2 : (0 : ℝ) / r1y y = 0 := zero_div _
  unfold OL.intGTL
  linarith

/-! ## The region integrals, `G0EnvL`, the blocks, the far regime -/

/-- **`∫_{150000}^{520000} g̃_L(y,r)/r dr ≤ 0.0414870396825`** (`envLR0`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR0L (y : ℝ) (hy : (10 ^ 25) ≤ y) :
    IntBnd (fun r => OL.gTL HW.phi y r / r) 150000 520000 0.0414870396825 := by
  have hu : envG 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633 0.0000297025673079
      64.1333331084 30.8744819896 0.545031222151 0.000210527045125 520000 ≤ (-0.0607946984409457) :=
      by
    refine (envG_ub 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633
        0.0000297025673079 64.1333331084 30.8744819896 0.545031222151 0.000210527045125 520000
        721.1102551 22.495089240173 611.216201520846 13.1615840952 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU16).trans (by norm_num)
    · have h0 : 13.1615840856 ≤ Real.log 520000 := lgpL15
      have h1 : Real.log 520000 ≤ 13.1615840952 := lgpU16
      have hl0 : 0 ≤ Real.log 520000 := by linarith
      have := tm_ge_pos 0.7269125431311568 13.1615840856 (Real.log 520000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0181758027395392 13.1615840856 (Real.log 520000) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0019692592947932 13.1615840856 (Real.log 520000) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000297025673079 13.1615840856 (Real.log 520000) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 13.1615840856 ≤ Real.log 520000 := lgpL15
      have h1 : Real.log 520000 ≤ 13.1615840952 := lgpU16
      have hl0 : 0 ≤ Real.log 520000 := by linarith
      have := tm_ge_pos 31.964544433902 13.1615840856 (Real.log 520000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.545031222151 13.1615840856 (Real.log 520000) 2 (by norm_num) (by norm_num)
          h0
      linarith
  have hl : (-0.1022817381234) ≤ envG 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633
      0.0000297025673079 64.1333331084 30.8744819896 0.545031222151 0.000210527045125 150000 := by
    refine le_trans (by norm_num) (envG_lb 2.94428873212 0.654209332173 0.00636024697078
        0.00173163875633 0.0000297025673079 64.1333331084 30.8744819896 0.545031222151
        0.000210527045125 150000 387.2983346 19.5768306732186 554.484416276102 11.9183905686
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL1)
    · have h0 : 11.9183905686 ≤ Real.log 150000 := lgpL1
      have h1 : Real.log 150000 ≤ 11.9183905772 := lgpU2
      have hl0 : 0 ≤ Real.log 150000 := by linarith
      have := tm_le_pos 0.7269125431311568 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0181758027395392 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0019692592947932 11.9183905772 (Real.log 150000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000297025673079 11.9183905772 (Real.log 150000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 11.9183905686 ≤ Real.log 150000 := lgpL1
      have h1 : Real.log 150000 ≤ 11.9183905772 := lgpU2
      have hl0 : 0 ≤ Real.log 150000 := by linarith
      have := tm_le_pos 31.964544433902 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.545031222151 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OL.gTL HW.phi y) 150000 520000 2.94428873212
      0.654209332173 0.00636024697078 0.00173163875633 0.0000297025673079 64.1333331084
      30.8744819896 0.545031222151 0.000210527045125 (by norm_num)
    (by norm_num) (fun r hr => envLR0 y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envLR0_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`∫_{520000}^{1740000} g̃_L(y,r)/r dr ≤ 0.024356574654`** (`envLR1`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR1L (y : ℝ) (hy : (10 ^ 25) ≤ y) :
    IntBnd (fun r => OL.gTL HW.phi y r / r) 520000 1740000 0.024356574654 := by
  have hu : envG 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033
      0.0000299846672039 66.3432584969 31.4275359512 0.475003664868 0.000211099791842 1740000 ≤
      (-0.0363422621537451) := by
    refine (envG_ub 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033
        0.0000299846672039 66.3432584969 31.4275359512 0.475003664868 0.000211099791842 1740000
        1319.090596 25.7190697529685 662.045066188943 14.3693956763 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU18).trans (by norm_num)
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_ge_pos 0.7395723839693488 14.3693956657 (Real.log 1740000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0125863551860872 14.3693956657 (Real.log 1740000) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0022744286779612 14.3693956657 (Real.log 1740000) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000299846672039 14.3693956657 (Real.log 1740000) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_ge_pos 32.377543280936 14.3693956657 (Real.log 1740000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.475003664868 14.3693956657 (Real.log 1740000) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0606988368076644) ≤ envG 2.98733358573 0.689226963225 (-0.00106021688168)
      0.00203455134033 0.0000299846672039 66.3432584969 31.4275359512 0.475003664868
      0.000211099791842 520000 := by
    refine le_trans (by norm_num) (envG_lb 2.98733358573 0.689226963225 (-0.00106021688168)
        0.00203455134033 0.0000299846672039 66.3432584969 31.4275359512 0.475003664868
        0.000211099791842 520000 721.110255 22.4660672412579 607.144160871162 13.1615840856
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL15)
    · have h0 : 13.1615840856 ≤ Real.log 520000 := lgpL15
      have h1 : Real.log 520000 ≤ 13.1615840952 := lgpU16
      have hl0 : 0 ≤ Real.log 520000 := by linarith
      have := tm_le_pos 0.7395723839693488 13.1615840952 (Real.log 520000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0125863551860872 13.1615840952 (Real.log 520000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0022744286779612 13.1615840952 (Real.log 520000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000299846672039 13.1615840952 (Real.log 520000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 13.1615840856 ≤ Real.log 520000 := lgpL15
      have h1 : Real.log 520000 ≤ 13.1615840952 := lgpU16
      have hl0 : 0 ≤ Real.log 520000 := by linarith
      have := tm_le_pos 32.377543280936 13.1615840952 (Real.log 520000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.475003664868 13.1615840952 (Real.log 520000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OL.gTL HW.phi y) 520000 1740000 2.98733358573
      0.689226963225 (-0.00106021688168) 0.00203455134033 0.0000299846672039 66.3432584969
      31.4275359512 0.475003664868 0.000211099791842 (by norm_num)
    (by norm_num) (fun r hr => envLR1 y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envLR1_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`∫_{1740000}^{3216000} g̃_L(y,r)/r dr ≤ 0.00856244316589`** (`envLR2a`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR2aL (y : ℝ) (hy : (10 ^ 25) ≤ y) :
    IntBnd (fun r => OL.gTL HW.phi y r / r) 1740000 3216000 0.00856244316589 := by
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 3216000 ≤
      (-0.0283008195435355) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 3216000
        1793.320942 28.013065979841 687.354014269796 14.9836489146 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU20).trans (by norm_num)
    · have h0 : 14.9836489035 ≤ Real.log 3216000 := lgpL19
      have h1 : Real.log 3216000 ≤ 14.9836489146 := lgpU20
      have hl0 : 0 ≤ Real.log 3216000 := by linarith
      have := tm_ge_pos 0.7186550723600464 14.9836489035 (Real.log 3216000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0074835678997616 14.9836489035 (Real.log 3216000) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0027792586469136 14.9836489035 (Real.log 3216000) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000353941790317 14.9836489035 (Real.log 3216000) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.9836489035 ≤ Real.log 3216000 := lgpL19
      have h1 : Real.log 3216000 ≤ 14.9836489146 := lgpU20
      have hl0 : 0 ≤ Real.log 3216000 := by linarith
      have := tm_ge_pos 32.461076586892 14.9836489035 (Real.log 3216000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.9836489035 (Real.log 3216000) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0368632627094223) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 659.255076987925 14.3693956657
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL17)
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 0.7186550723600464 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0074835678997616 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0027792586469136 14.3693956763 (Real.log 1740000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000353941790317 14.3693956763 (Real.log 1740000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 32.461076586892 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OL.gTL HW.phi y) 1740000 3216000 2.99415982257
      0.688720800761 (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.9050831691
      31.5559712457 0.452552670596 0.000210527045125 (by norm_num)
    (by norm_num) (fun r hr => envLR2a y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envLR2a_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`∫_{3216000}^{5940000} g̃_L(y,r)/r dr ≤ 0.0065109827539`** (`envLR2b`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR2bL (y : ℝ) (hy : (10 ^ 26) ≤ y) :
    IntBnd (fun r => OL.gTL HW.phi y r / r) 3216000 5940000 0.0065109827539 := by
  have hu : envG 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
      0.0000310866337797 67.6946571766 31.7581107855 0.431143061793 0.000143820551574 5940000 ≤
      (-0.0215299898547254) := by
    refine (envG_ub 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 67.6946571766 31.7581107855 0.431143061793 0.000143820551574 5940000
        2437.211522 28.8236705767554 713.98812989128 15.5972196969 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU22).trans (by norm_num)
    · have h0 : 15.5972196853 ≤ Real.log 5940000 := lgpL21
      have h1 : Real.log 5940000 ≤ 15.5972196969 := lgpU22
      have hl0 : 0 ≤ Real.log 5940000 := by linarith
      have := tm_ge_pos 0.7239920050511024 15.5972196853 (Real.log 5940000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0059015303442756 15.5972196853 (Real.log 5940000) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0025826401079776 15.5972196853 (Real.log 5940000) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000310866337797 15.5972196853 (Real.log 5940000) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 15.5972196853 ≤ Real.log 5940000 := lgpL21
      have h1 : Real.log 5940000 ≤ 15.5972196969 := lgpU22
      have hl0 : 0 ≤ Real.log 5940000 := by linarith
      have := tm_ge_pos 32.620396909086 15.5972196853 (Real.log 5940000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.431143061793 15.5972196853 (Real.log 5940000) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0280409726086176) ≤ envG 3.00843946276 0.700385883674 (-0.00959431030359)
      0.00233394703774 0.0000310866337797 67.6946571766 31.7581107855 0.431143061793
      0.000143820551574 3216000 := by
    refine le_trans (by norm_num) (envG_lb 3.00843946276 0.700385883674 (-0.00959431030359)
        0.00233394703774 0.0000310866337797 67.6946571766 31.7581107855 0.431143061793
        0.000143820551574 3216000 1793.320941 26.8842633715161 685.883443288613 14.9836489035
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL19)
    · have h0 : 14.9836489035 ≤ Real.log 3216000 := lgpL19
      have h1 : Real.log 3216000 ≤ 14.9836489146 := lgpU20
      have hl0 : 0 ≤ Real.log 3216000 := by linarith
      have := tm_le_pos 0.7239920050511024 14.9836489146 (Real.log 3216000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0059015303442756 14.9836489146 (Real.log 3216000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0025826401079776 14.9836489146 (Real.log 3216000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000310866337797 14.9836489146 (Real.log 3216000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.9836489035 ≤ Real.log 3216000 := lgpL19
      have h1 : Real.log 3216000 ≤ 14.9836489146 := lgpU20
      have hl0 : 0 ≤ Real.log 3216000 := by linarith
      have := tm_le_pos 32.620396909086 14.9836489146 (Real.log 3216000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.431143061793 14.9836489146 (Real.log 3216000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OL.gTL HW.phi y) 3216000 5940000 3.00843946276
      0.700385883674 (-0.00959431030359) 0.00233394703774 0.0000310866337797 67.6946571766
      31.7581107855 0.431143061793 0.000143820551574 (by norm_num)
    (by norm_num) (fun r hr => envLR2b y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envLR2b_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`G0EnvL`**: `g̃_L(y, r₀) ≤ 0.0427913` for `y ≥ 10²⁵` (`envLR0` at `r₀ = 150000`). -/
theorem g0EnvL : G0EnvL 0.0427913 := by
  intro y hy
  have h0 : 11.9183905686 ≤ Real.log 150000 := lgpL1
  have h1 : Real.log 150000 ≤ 11.9183905772 := lgpU2
  have hl0 : 0 ≤ Real.log 150000 := by linarith
  refine (envLR0 y 150000 hy le_rfl (by norm_num)).trans ((envF_le_box 2.94428873212 0.654209332173
      0.00636024697078 0.00173163875633 0.0000297025673079 64.1333331084 30.8744819896
      0.545031222151 0.000210527045125 150000 387.2983346 15.1758360978999 509.528081877471
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.654209332173 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.00636024697078 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
    have := tm_le_pos 0.00173163875633 11.9183905772 (Real.log 150000) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000297025673079 11.9183905772 (Real.log 150000) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 30.8744819896 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.545031222151 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
    linarith

/-- **`T1BlkL`, block 0**: `g̃_L(y, r₁(y)) ≤ 0.0157963` on `y ∈ [(10 ^ 25), (13 * 10 ^ 24)]`
    (`envLR2a` at `r₁(y) ∈ [1740595, 1866736]`). -/
theorem t1BlkL0 : T1BlkL (10 ^ 25) (13 * 10 ^ 24) 0.0157963 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1740595 ≤ r1y y := MN.r1_ge_of y 1740595 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 1866736 := MN.r1Le_of y 1866736 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.3697375613 ≤ Real.log (r1y y) := lgpL3.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.4397020143 := (Real.log_le_log (by linarith) hru).trans lgpU6
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envLR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 (r1y y)
        1319.31611 20.0949231409736 616.9233967146 (by norm_num) (le_trans (by norm_num) hrl) ?_ ?_
        (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.4397020143 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.3697375613 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.4397020143 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.4397020143 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 31.5559712457 14.4397020143 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.4397020143 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlkL`, block 0**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ 0.0669295` on `y ∈ [(10 ^ 25), (13 * 10 ^
    24)]`. -/
theorem iGBlkL0 : IGBlkL (10 ^ 25) (13 * 10 ^ 24) 0.0669295 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1740595 ≤ r1y y := MN.r1_ge_of y 1740595 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 1866736 := MN.r1Le_of y 1866736 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 1866736 ≤
      (-0.0357774396843503) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 1866736
        1366.285476 26.2753875561082 662.453924237231 14.4397020143 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU6).trans (by norm_num)
    · have h0 : 14.4397020037 ≤ Real.log 1866736 := lgpL24
      have h1 : Real.log 1866736 ≤ 14.4397020143 := lgpU6
      have hl0 : 0 ≤ Real.log 1866736 := by linarith
      have := tm_ge_pos 0.7186550723600464 14.4397020037 (Real.log 1866736) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0074835678997616 14.4397020037 (Real.log 1866736) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0027792586469136 14.4397020037 (Real.log 1866736) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000353941790317 14.4397020037 (Real.log 1866736) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.4397020037 ≤ Real.log 1866736 := lgpL24
      have h1 : Real.log 1866736 ≤ 14.4397020143 := lgpU6
      have hl0 : 0 ≤ Real.log 1866736 := by linarith
      have := tm_ge_pos 32.461076586892 14.4397020037 (Real.log 1866736) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.4397020037 (Real.log 1866736) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0368632627094223) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 659.255076987925 14.3693956657
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL17)
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 0.7186550723600464 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0074835678997616 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0027792586469136 14.3693956763 (Real.log 1740000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000353941790317 14.3693956763 (Real.log 1740000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 32.461076586892 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OL.gTL HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envLR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envLR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 1866736 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envLR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00108582302508 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0L y hyA) (igR1L y hyA)) hlast
  unfold OL.intGTL
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1BlkL`, block 1**: `g̃_L(y, r₁(y)) ≤ 0.0154199` on `y ∈ [(13 * 10 ^ 24), (184 * 10 ^ 23)]`
    (`envLR2a` at `r₁(y) ∈ [1866735, 2047935]`). -/
theorem t1BlkL1 : T1BlkL (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0154199 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1866735 ≤ r1y y := MN.r1_ge_of y 1866735 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2047935 := MN.r1Le_of y 2047935 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.439701468 ≤ Real.log (r1y y) := lgpL7.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.5323425314 := (Real.log_le_log (by linarith) hru).trans lgpU8
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envLR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 (r1y y)
        1366.285109 20.3256432555094 621.061402873135 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.5323425314 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.439701468 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.5323425314 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.5323425314 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 31.5559712457 14.5323425314 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.5323425314 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlkL`, block 1**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ 0.0683159` on `y ∈ [(13 * 10 ^ 24), (184 *
    10 ^ 23)]`. -/
theorem iGBlkL1 : IGBlkL (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0683159 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1866735 ≤ r1y y := MN.r1_ge_of y 1866735 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2047935 := MN.r1Le_of y 2047935 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 2047935 ≤
      (-0.0343910031312344) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 2047935
        1431.060796 26.5640078159622 666.675779821715 14.5323425314 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU8).trans (by norm_num)
    · have h0 : 14.5323425208 ≤ Real.log 2047935 := lgpL25
      have h1 : Real.log 2047935 ≤ 14.5323425314 := lgpU8
      have hl0 : 0 ≤ Real.log 2047935 := by linarith
      have := tm_ge_pos 0.7186550723600464 14.5323425208 (Real.log 2047935) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0074835678997616 14.5323425208 (Real.log 2047935) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0027792586469136 14.5323425208 (Real.log 2047935) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000353941790317 14.5323425208 (Real.log 2047935) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.5323425208 ≤ Real.log 2047935 := lgpL25
      have h1 : Real.log 2047935 ≤ 14.5323425314 := lgpU8
      have hl0 : 0 ≤ Real.log 2047935 := by linarith
      have := tm_ge_pos 32.461076586892 14.5323425208 (Real.log 2047935) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.5323425208 (Real.log 2047935) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0368632627094223) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 659.255076987925 14.3693956657
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL17)
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 0.7186550723600464 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0074835678997616 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0027792586469136 14.3693956763 (Real.log 1740000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000353941790317 14.3693956763 (Real.log 1740000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 32.461076586892 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OL.gTL HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envLR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envLR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 2047935 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envLR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00247225957819 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0L y hyA) (igR1L y hyA)) hlast
  unfold OL.intGTL
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1BlkL`, block 2**: `g̃_L(y, r₁(y)) ≤ 0.0150526` on `y ∈ [(184 * 10 ^ 23), (365 * 10 ^ 23)]`
    (`envLR2a` at `r₁(y) ∈ [2047934, 2458345]`). -/
theorem t1BlkL2 : T1BlkL (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0150526 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2047934 ≤ r1y y := MN.r1_ge_of y 2047934 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2458345 := MN.r1Le_of y 2458345 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.5323420326 ≤ Real.log (r1y y) := lgpL9.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.7149989224 := (Real.log_le_log (by linarith) hru).trans lgpU10
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envLR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 (r1y y)
        1431.060445 20.8001538869589 629.242935833885 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.7149989224 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.5323420326 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.7149989224 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.7149989224 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 31.5559712457 14.7149989224 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.7149989224 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlkL`, block 2**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ 0.0709086` on `y ∈ [(184 * 10 ^ 23), (365 *
    10 ^ 23)]`. -/
theorem iGBlkL2 : IGBlkL (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0709086 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2047934 ≤ r1y y := MN.r1_ge_of y 2047934 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2458345 := MN.r1Le_of y 2458345 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 2458345 ≤
      (-0.0317983087410922) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 2458345
        1567.911031 27.1418176430167 675.02263605581 14.7149989224 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU10).trans (by norm_num)
    · have h0 : 14.7149989118 ≤ Real.log 2458345 := lgpL26
      have h1 : Real.log 2458345 ≤ 14.7149989224 := lgpU10
      have hl0 : 0 ≤ Real.log 2458345 := by linarith
      have := tm_ge_pos 0.7186550723600464 14.7149989118 (Real.log 2458345) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0074835678997616 14.7149989118 (Real.log 2458345) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0027792586469136 14.7149989118 (Real.log 2458345) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000353941790317 14.7149989118 (Real.log 2458345) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.7149989118 ≤ Real.log 2458345 := lgpL26
      have h1 : Real.log 2458345 ≤ 14.7149989224 := lgpU10
      have hl0 : 0 ≤ Real.log 2458345 := by linarith
      have := tm_ge_pos 32.461076586892 14.7149989118 (Real.log 2458345) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.7149989118 (Real.log 2458345) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0368632627094223) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 659.255076987925 14.3693956657
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL17)
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 0.7186550723600464 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0074835678997616 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0027792586469136 14.3693956763 (Real.log 1740000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000353941790317 14.3693956763 (Real.log 1740000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 32.461076586892 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OL.gTL HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envLR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envLR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 2458345 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envLR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00506495396834 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0L y hyA) (igR1L y hyA)) hlast
  unfold OL.intGTL
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1BlkL`, block 3**: `g̃_L(y, r₁(y)) ≤ 0.0141869` on `y ∈ [(365 * 10 ^ 23), (10 ^ 26)]`
    (`envLR2a` at `r₁(y) ∈ [2458344, 3216360]`). -/
theorem t1BlkL3 : T1BlkL (365 * 10 ^ 23) (10 ^ 26) 0.0141869 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2458344 ≤ r1y y := MN.r1_ge_of y 2458344 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 3216360 := MN.r1Le_of y 3216360 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.714998505 ≤ Real.log (r1y y) := lgpL11.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.9837608486 := (Real.log_le_log (by linarith) hru).trans lgpU12
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envLR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 (r1y y)
        1567.910711 21.5045437703677 641.336207746721 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.9837608486 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.714998505 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.9837608486 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.9837608486 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 31.5559712457 14.9837608486 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.9837608486 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlkL`, block 3**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ 0.0744075` on `y ∈ [(365 * 10 ^ 23),
    (10 ^ 26)]`. -/
theorem iGBlkL3 : IGBlkL (365 * 10 ^ 23) (10 ^ 26) 0.0744075 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2458344 ≤ r1y y := MN.r1_ge_of y 2458344 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 3216360 := MN.r1Le_of y 3216360 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 3216360 ≤
      (-0.0282994360242523) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 3216360
        1793.421312 28.013434366941 687.359165797969 14.9837608486 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU12).trans (by norm_num)
    · have h0 : 14.9837608375 ≤ Real.log 3216360 := lgpL27
      have h1 : Real.log 3216360 ≤ 14.9837608486 := lgpU12
      have hl0 : 0 ≤ Real.log 3216360 := by linarith
      have := tm_ge_pos 0.7186550723600464 14.9837608375 (Real.log 3216360) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0074835678997616 14.9837608375 (Real.log 3216360) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0027792586469136 14.9837608375 (Real.log 3216360) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000353941790317 14.9837608375 (Real.log 3216360) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.9837608375 ≤ Real.log 3216360 := lgpL27
      have h1 : Real.log 3216360 ≤ 14.9837608486 := lgpU12
      have hl0 : 0 ≤ Real.log 3216360 := by linarith
      have := tm_ge_pos 32.461076586892 14.9837608375 (Real.log 3216360) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.9837608375 (Real.log 3216360) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0368632627094223) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 659.255076987925 14.3693956657
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL17)
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 0.7186550723600464 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0074835678997616 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0027792586469136 14.3693956763 (Real.log 1740000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000353941790317 14.3693956763 (Real.log 1740000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.3693956657 ≤ Real.log 1740000 := lgpL17
      have h1 : Real.log 1740000 ≤ 14.3693956763 := lgpU18
      have hl0 : 0 ≤ Real.log 1740000 := by linarith
      have := tm_le_pos 32.461076586892 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OL.gTL HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envLR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envLR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 3216360 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.9050831691 31.5559712457 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envLR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00856382668517 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0L y hyA) (igR1L y hyA)) hlast
  unfold OL.intGTL
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1BlkL`, block 4**: `g̃_L(y, r₁(y)) ≤ 0.0128839` on `y ∈ [(10 ^ 26), (10 ^ 27)]`
    (`envLR2b` at `r₁(y) ∈ [3216359, 5943350]`). -/
theorem t1BlkL4 : T1BlkL (10 ^ 26) (10 ^ 27) 0.0128839 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 3216359 ≤ r1y y := MN.r1_ge_of y 3216359 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 5943350 := MN.r1Le_of y 5943350 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.9837605266 ≤ Real.log (r1y y) := lgpL13.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 15.597783511 := (Real.log_le_log (by linarith) hru).trans lgpU14
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envLR2b y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 67.6946571766 31.7581107855 0.431143061793 0.000143820551574 (r1y y)
        1793.421032 22.4757477524735 667.943956099017 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.700385883674 15.597783511 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00959431030359) 14.9837605266 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00233394703774 15.597783511 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000310866337797 15.597783511 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 31.7581107855 15.597783511 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.431143061793 15.597783511 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlkL`, block 4**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ 0.0809224` on `y ∈ [(10 ^ 26), (10 ^ 27)]`. -/
theorem iGBlkL4 : IGBlkL (10 ^ 26) (10 ^ 27) 0.0809224 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 3216359 ≤ r1y y := MN.r1_ge_of y 3216359 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 5943350 := MN.r1Le_of y 5943350 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (3216000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
      0.0000310866337797 67.6946571766 31.7581107855 0.431143061793 0.000143820551574 5943350 ≤
      (-0.0215246885142489) := by
    refine (envG_ub 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 67.6946571766 31.7581107855 0.431143061793 0.000143820551574 5943350
        2437.898686 28.8255113534785 714.014104753922 15.597783511 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU14).trans (by norm_num)
    · have h0 : 15.5977834994 ≤ Real.log 5943350 := lgpL28
      have h1 : Real.log 5943350 ≤ 15.597783511 := lgpU14
      have hl0 : 0 ≤ Real.log 5943350 := by linarith
      have := tm_ge_pos 0.7239920050511024 15.5977834994 (Real.log 5943350) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0059015303442756 15.5977834994 (Real.log 5943350) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0025826401079776 15.5977834994 (Real.log 5943350) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000310866337797 15.5977834994 (Real.log 5943350) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 15.5977834994 ≤ Real.log 5943350 := lgpL28
      have h1 : Real.log 5943350 ≤ 15.597783511 := lgpU14
      have hl0 : 0 ≤ Real.log 5943350 := by linarith
      have := tm_ge_pos 32.620396909086 15.5977834994 (Real.log 5943350) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.431143061793 15.5977834994 (Real.log 5943350) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0280409726086176) ≤ envG 3.00843946276 0.700385883674 (-0.00959431030359)
      0.00233394703774 0.0000310866337797 67.6946571766 31.7581107855 0.431143061793
      0.000143820551574 3216000 := by
    refine le_trans (by norm_num) (envG_lb 3.00843946276 0.700385883674 (-0.00959431030359)
        0.00233394703774 0.0000310866337797 67.6946571766 31.7581107855 0.431143061793
        0.000143820551574 3216000 1793.320941 26.8842633715161 685.883443288613 14.9836489035
        (by norm_num) (by norm_num)
      (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num) lgpL19)
    · have h0 : 14.9836489035 ≤ Real.log 3216000 := lgpL19
      have h1 : Real.log 3216000 ≤ 14.9836489146 := lgpU20
      have hl0 : 0 ≤ Real.log 3216000 := by linarith
      have := tm_le_pos 0.7239920050511024 14.9836489146 (Real.log 3216000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.0059015303442756 14.9836489146 (Real.log 3216000) 2 (by norm_num) hl0 h1
      have := tm_le_pos 0.0025826401079776 14.9836489146 (Real.log 3216000) 3 (by norm_num) hl0 h1
      have := tm_le_pos 0.0000310866337797 14.9836489146 (Real.log 3216000) 4 (by norm_num) hl0 h1
      linarith
    · have h0 : 14.9836489035 ≤ Real.log 3216000 := lgpL19
      have h1 : Real.log 3216000 ≤ 14.9836489146 := lgpU20
      have hl0 : 0 ≤ Real.log 3216000 := by linarith
      have := tm_le_pos 32.620396909086 14.9836489146 (Real.log 3216000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.431143061793 14.9836489146 (Real.log 3216000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OL.gTL HW.phi y) 3216000 (r1y y) 3.00843946276 0.700385883674
      (-0.00959431030359) 0.00233394703774 0.0000310866337797 67.6946571766 31.7581107855
      0.431143061793 0.000143820551574 (by norm_num) hr1
    (fun r hr => envLR2b y r (le_trans (by norm_num) hy1) hr.1 (hr.2.trans (hru.trans
        (by norm_num))))
    (fun r hr => envLR2b_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 5943350 3.00843946276 0.700385883674 (-0.00959431030359)
      0.00233394703774 0.0000310866337797 67.6946571766 31.7581107855 0.431143061793
      0.000143820551574 (by linarith) hru
    (fun r hr => envLR2b_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00651628409437 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _
      (intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0L y hyA) (igR1L y hyA)) (igR2aL y hyA))
      hlast
  unfold OL.intGTL
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1FarL`**: `cfL(x)·g̃_L(x/49, r₁) ≤ 0.206372` for `x ≥ 4.9·10²⁸` (`far_T1L` on `envLRF`). -/
theorem t1FarL : T1FarL 0.206372 := by
  intro x hx
  have h := far_T1L 3.26627202061 1.1187151769 0.0114351675071 69.8799339884 32.360963423
      0.381494368499 3.09852175891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun y hy => envLRF y (r1y y) hy (MN.r1_ge_of y 5940000 (le_trans (by norm_num) hy)
      (by norm_num) (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy 4))) le_rfl) x hx
  unfold cfL
  exact h.trans (by norm_num)

/-- **`IGFarL`**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ 0.104449` for `y ≥ 10²⁷` (`far_IGL`). -/
theorem iGFarL : IGFarL 0.104449 := by
  intro y hy
  have h0 : 15.5972196853 ≤ Real.log 5940000 := lgpL21
  have h1 : Real.log 5940000 ≤ 15.5972196969 := lgpU22
  have hl0 : 0 ≤ Real.log 5940000 := by linarith
  have hS : (3.26627202061 + 2 * 1.1187151769 + 8 * 0.0114351675071 + 48 * 0 + 384 * 0) +
      (1.1187151769 + 4 * 0.0114351675071 + 24 * 0 + 192 * 0) * Real.log 5940000 + (0.0114351675071
      + 6 * 0 + 48 * 0) * Real.log 5940000 ^ 2 + (0 + 8 * 0) * Real.log 5940000 ^ 3 + 0 * Real.log
      5940000 ^ 4 ≤ 26.5393278904435 := by
    have := tm_le_pos 1.1644558469284 15.5972196969 (Real.log 5940000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.0114351675071 15.5972196969 (Real.log 5940000) 2 (by norm_num) hl0 h1
    linarith
  have hT : (69.8799339884 + 32.360963423 + 2 * 0.381494368499) + (32.360963423 + 2 *
      0.381494368499) * Real.log 5940000 + 0.381494368499 * Real.log 5940000 ^ 2 ≤ 712.452824781162
      := by
    have := tm_le_pos 33.123952159998 15.5972196969 (Real.log 5940000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.381494368499 15.5972196969 (Real.log 5940000) 2 (by norm_num) hl0 h1
    linarith
  have hb := fun y (hy : (10 ^ 27 : ℝ) ≤ y) => intBnd_add _ _ _ _ _ _
    (intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _
      (igR0L y (le_trans (by norm_num) hy)) (igR1L y (le_trans (by norm_num) hy)))
      (igR2aL y (le_trans (by norm_num) hy))) (igR2bL y (le_trans (by norm_num) hy))
  refine (far_IGL 3.26627202061 1.1187151769 0.0114351675071 69.8799339884 32.360963423
      0.381494368499 3.09852175891 _ 26.5393278904435 712.452824781162 2437.211521 (by norm_num)
      (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) envLRF hb (by norm_num)
    (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) hS (by norm_num) hT y hy).trans ?_
  norm_num

/-! ## THE RESULT -/

/-- **`OL.MNumL HW.phi 8.54 0.8095 0.6406` — PROVED.** The spine `mnumL_of_links` with every link
    discharged. -/
theorem mnumL_proved : OL.MNumL HW.phi 8.54 0.8095 0.6406 :=
  mnumL_of_links gtNonnegL g0EnvL t1BlkL0 t1BlkL1 t1BlkL2 t1BlkL3 t1BlkL4 iGBlkL0 iGBlkL1 iGBlkL2
      iGBlkL3 iGBlkL4 t1FarL iGFarL

end Principia.Common.TernaryGoldbach.ML
