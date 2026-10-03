/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumC
import Principia.Common.TernaryGoldbach.MNumCR0Hi
import Principia.Common.TernaryGoldbach.MNumCR1Hi
import Principia.Common.TernaryGoldbach.MNumCR2aHi
import Principia.Common.TernaryGoldbach.MNumCR2bHi
import Principia.Common.TernaryGoldbach.MNumCRFHi

set_option autoImplicit false

/-!
# `OC.MNumC HW.phi 8.54 0.791` — the discharges (`mnumC_proved`)

GENERATED numerics (`scratchpad/mnc/gen/gen_spine.py`) around hand-written far-regime lemmas.

* **`GTNonneg`**: every integrand of `g̃(y, r₀)` is `≥ 0` (`gT_nonneg_r0`).
* **`G0Env`, `T1Blk`**: a region envelope `envR…` at `r₀` or at `r₁(y) ∈ [r̲, r̄]`, evaluated on a
  box by `envF_le_box` (certified `log r̲`, `log r̄`, `√r̲`).
* **`IGBlk`**: `∫_{r₀}^{r₁(y)} g̃/r` split over the regions (`intBnd_add`), each bounded by the
  exact antiderivative of its envelope (`intBnd_region`), `envG` evaluated from above/below at the
  ends (`envG_ub`, `envG_lb`) and increasing (`envG_mono`) up to `r̄ ≥ r₁(y)`.
* **The far regime `x ≥ 4.9·10²⁸`** (`far_T1`, `far_IG`): the far envelope has nonnegative
  coefficients and `z ∝ y^{−1/6}`; at `r₁ = (3/8)t²`, `t = y^{2/15}`, every term is a power
  `K^j/t` (`K = (log y)/2`) bounded by `K³/t ≤ 7.54482` (`MN.far_q1`) and `K ≥ 31.084898`, and
  `y^{−1/6} ≤ 1/(7.9t)`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set

/-! ## Certified logarithms of the evaluation points -/

theorem lgpL1 : 11.9183905686 ≤ Real.log 150000 := by
  have h := MN.le_log_series 150000 (-0.1444091796875) 17 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU2 : Real.log 150000 ≤ 11.9183905772 := by
  have h := MN.log_le_series 150000 (-0.1444091796875) 17 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL3 : 14.3697375613 ≤ Real.log 1740595 := by
  have h := MN.le_log_series 1740595 0.170019626617431640625 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU4 : Real.log 1781060 ≤ 14.3927192557 := by
  have h := MN.log_le_series 1781060 0.1507244110107421875 21 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL5 : 14.3927186837 ≤ Real.log 1781059 := by
  have h := MN.le_log_series 1781059 0.150724887847900390625 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU6 : Real.log 1866736 ≤ 14.4397020143 := by
  have h := MN.log_le_series 1866736 0.10987091064453125 21 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL7 : 14.439701468 ≤ Real.log 1866735 := by
  have h := MN.le_log_series 1866735 0.109871387481689453125 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU8 : Real.log 2047935 ≤ 14.5323425314 := by
  have h := MN.log_le_series 2047935 0.023468494415283203125 21 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL9 : 14.5323420326 ≤ Real.log 2047934 := by
  have h := MN.le_log_series 2047934 0.02346897125244140625 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU10 : Real.log 2458345 ≤ 14.7149989224 := by
  have h := MN.log_le_series 2458345 (-0.172230243682861328125) 21 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL11 : 14.714998505 ≤ Real.log 2458344 := by
  have h := MN.le_log_series 2458344 (-0.172229766845703125) 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU12 : Real.log 3216360 ≤ 14.9837608486 := by
  have h := MN.log_le_series 3216360 0.2331600189208984375 22 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL13 : 14.9837605266 ≤ Real.log 3216359 := by
  have h := MN.le_log_series 3216359 0.2331602573394775390625 22 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU14 : Real.log 5943350 ≤ 15.597783511 := by
  have h := MN.log_le_series 5943350 0.2914974689483642578125 23 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL15 : 13.1615840856 ≤ Real.log 520000 := by
  have h := MN.le_log_series 520000 0.0081787109375 19 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU16 : Real.log 520000 ≤ 13.1615840952 := by
  have h := MN.log_le_series 520000 0.0081787109375 19 61 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL17 : 14.3693956657 ≤ Real.log 1740000 := by
  have h := MN.le_log_series 1740000 0.1703033447265625 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU18 : Real.log 1740000 ≤ 14.3693956763 := by
  have h := MN.log_le_series 1740000 0.1703033447265625 21 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL19 : 14.9836489035 ≤ Real.log 3216000 := by
  have h := MN.le_log_series 3216000 0.233245849609375 22 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU20 : Real.log 3216000 ≤ 14.9836489146 := by
  have h := MN.log_le_series 3216000 0.233245849609375 22 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL21 : 15.5972196853 ≤ Real.log 5940000 := by
  have h := MN.le_log_series 5940000 0.291896820068359375 23 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpU22 : Real.log 5940000 ≤ 15.5972196969 := by
  have h := MN.log_le_series 5940000 0.291896820068359375 23 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL23 : 14.3927192451 ≤ Real.log 1781060 := by
  have h := MN.le_log_series 1781060 0.1507244110107421875 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL24 : 14.4397020037 ≤ Real.log 1866736 := by
  have h := MN.le_log_series 1866736 0.10987091064453125 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL25 : 14.5323425208 ≤ Real.log 2047935 := by
  have h := MN.le_log_series 2047935 0.023468494415283203125 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL26 : 14.7149989118 ≤ Real.log 2458345 := by
  have h := MN.le_log_series 2458345 (-0.172230243682861328125) 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL27 : 14.9837608375 ≤ Real.log 3216360 := by
  have h := MN.le_log_series 3216360 0.2331600189208984375 22 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgpL28 : 15.5977834994 ≤ Real.log 5943350 := by
  have h := MN.le_log_series 5943350 0.2914974689483642578125 23 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-! ## `coefC` on the far regime, and `g̃(r₀) ≥ 0` -/

/-- `0 ≤ coefC ≤ 7/15` on `x ≥ 4.9·10²⁸`. -/
theorem coefC_far (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    0 ≤ OC.coefC x ∧ OC.coefC x ≤ 7 / 15 :=
  coefC_bounds x (le_trans (by norm_num) hx)

/-- **Link [g̃ ≥ 0] DISCHARGED** (`gT_nonneg_r0`). -/
theorem gtNonneg : GTNonneg := fun y hy => gT_nonneg_r0 y hy

/-! ## The far regime `x ≥ 4.9·10²⁸` (`y ≥ 10²⁷`): `K`-power bounds -/

/-- `y^{−1/6} ≤ 1/(7.9·y^{2/15})` for `y ≥ 10²⁷` (`y^{1/30} ≥ 7.9`). -/
theorem far_y6 (y : ℝ) (hyY : 10 ^ 27 ≤ y) :
    y ^ (-(1 : ℝ) / 6) ≤ 1 / (7.9 * y ^ ((2 : ℝ) / 15)) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  have h30 : 7.9 ≤ y ^ ((1 : ℝ) / 30) := by
    have h := MN.le_rpow_of_pow y 7.9 1 30 (by norm_num) hy0.le (by norm_num)
      (le_trans (by norm_num : (7.9 : ℝ) ^ 30 ≤ 10 ^ 27) (by rw [pow_one]; exact hyY))
    rwa [show ((1 : ℕ) : ℝ) / ((30 : ℕ) : ℝ) = 1 / 30 by norm_num] at h
  have e : y ^ (-(1 : ℝ) / 6) * (y ^ ((1 : ℝ) / 30) * y ^ ((2 : ℝ) / 15)) = 1 := by
    rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]
    norm_num
  have ht : 0 < y ^ ((2 : ℝ) / 15) := Real.rpow_pos_of_pos hy0 _
  rw [le_div_iff₀ (by positivity)]
  calc y ^ (-(1 : ℝ) / 6) * (7.9 * y ^ ((2 : ℝ) / 15)) ≤
        y ^ (-(1 : ℝ) / 6) * (y ^ ((1 : ℝ) / 30) * y ^ ((2 : ℝ) / 15)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h30 ht.le)
          (Real.rpow_nonneg hy0.le _)
    _ = 1 := e

/-- **The `K`-powers over `t = y^{2/15}`** for `y ≥ 10²⁷`: `K/t`, `K²/t`, `K³/t` (`MN.far_q1`,
`K ≥ 31.084898`), and `K·y^{−1/6} ≤ (K/t)/7.9`. -/
theorem far_kp (y : ℝ) (hyY : 10 ^ 27 ≤ y) :
    kK y / y ^ ((2 : ℝ) / 15) ≤ 7.54482 / 31.084898 ^ 2 ∧
      kK y ^ 2 / y ^ ((2 : ℝ) / 15) ≤ 7.54482 / 31.084898 ∧
      kK y ^ 3 / y ^ ((2 : ℝ) / 15) ≤ 7.54482 ∧
      kK y * y ^ (-(1 : ℝ) / 6) ≤ 7.54482 / 31.084898 ^ 2 / 7.9 ∧ 31.084898 ≤ kK y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  obtain ⟨hYl, -⟩ := MN.log_1e27
  have hv : 62.169796 ≤ Real.log y := hYl.trans (Real.log_le_log (by norm_num) hyY)
  have hK : 31.084898 ≤ kK y := by
    unfold kK
    linarith
  have hK0 : 0 < kK y := by linarith
  have ht : 0 < y ^ ((2 : ℝ) / 15) := Real.rpow_pos_of_pos hy0 _
  have h3 := MN.far_q1 y hyY
  set t := y ^ ((2 : ℝ) / 15) with htd
  set K := kK y with hKd
  have e1 : K / t = K ^ 3 / t / K ^ 2 := by
    field_simp
  have e2 : K ^ 2 / t = K ^ 3 / t / K := by
    field_simp
  have hq0 : 0 ≤ K ^ 3 / t := by positivity
  have h1 : K / t ≤ 7.54482 / 31.084898 ^ 2 := by
    rw [e1]
    exact div_le_div₀ (by norm_num) h3 (by norm_num) (pow_le_pow_left₀ (by norm_num) hK 2)
  have h2 : K ^ 2 / t ≤ 7.54482 / 31.084898 := by
    rw [e2]
    exact div_le_div₀ (by norm_num) h3 (by norm_num) hK
  have h6 := far_y6 y hyY
  have h4 : K * y ^ (-(1 : ℝ) / 6) ≤ 7.54482 / 31.084898 ^ 2 / 7.9 := by
    have := mul_le_mul_of_nonneg_left h6 hK0.le
    have e3 : K * (1 / (7.9 * t)) = K / t / 7.9 := by
      field_simp
    rw [e3] at this
    have := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 7.9)
    linarith
  exact ⟨h1, h2, h3, h4, hK⟩

set_option maxHeartbeats 1000000 in
-- `far_T1` chains ~20 nonlinear steps through `field_simp`, `gcongr` and `linarith`
/-- **The far `T₁`**, generic in a far envelope with nonnegative coefficients (quadratic `P`):
`coefC(x)·felipa(x)·g̃(x/49, r₁) ≤ (7/15)·1.36065·(…)` for `x ≥ 4.9·10²⁸`, from
`coefC ≤ 7/15`, `felipa ≤ 1.36065K` (`MN.far_cf`), `ℓ = log r₁ ≤ (8/15)K`, `√r₁ ≥ 0.61237t`,
`r₁ ≥ (3/8)·3981·t` and `far_kp`. -/
theorem far_T1 (p0 p1 p2 q0 q1 q2 zF : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hz : 0 ≤ zF)
    (hcoef : ∀ x : ℝ, 49 * 10 ^ 27 ≤ x → 0 ≤ OC.coefC x ∧ OC.coefC x ≤ 7 / 15)
    (henv : ∀ y : ℝ, 10 ^ 27 ≤ y →
      OC.gT HW.phi y (r1y y) ≤ envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y))
    (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    OC.coefC x * MN.fel x * OC.gT HW.phi (x / 49) (r1y (x / 49)) ≤
      7 / 15 * 1.36065 * ((p0 * (7.54482 / 31.084898 ^ 2) + p1 * (8 / 15) * (7.54482 / 31.084898) +
        p2 * (8 / 15) ^ 2 * 7.54482) / 0.61237 +
        (q0 * (7.54482 / 31.084898 ^ 2) + q1 * (8 / 15) * (7.54482 / 31.084898) +
          q2 * (8 / 15) ^ 2 * 7.54482) / (3 / 8 * 3981) +
        zF * (7.54482 / 31.084898 ^ 2 / 7.9)) := by
  have hyY : 10 ^ 27 ≤ x / 49 := MN.y_ge_of x _ hx
  set y := x / 49 with hyd
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  obtain ⟨hsY, hr1, -⟩ := MN.far_s y hyY
  obtain ⟨k1, k2, k3, k4, hK⟩ := far_kp y hyY
  obtain ⟨hc0, hc1⟩ := hcoef x hx
  have hfel := (MN.far_cf x hx).2
  have hfel0 : 0 ≤ MN.fel x := by
    have := LW.log_ge_of x (le_trans (by norm_num) hx)
    unfold MN.fel
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
  -- the envelope at r₁
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
  -- K·E ≤ …
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
  have hcf : OC.coefC x * MN.fel x ≤ 7 / 15 * (1.36065 * K) :=
    mul_le_mul hc1 hfel hfel0 (by norm_num)
  calc OC.coefC x * MN.fel x * OC.gT HW.phi y (r1y y) ≤
        OC.coefC x * MN.fel x * envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg hc0 hfel0)
    _ ≤ 7 / 15 * (1.36065 * K) *
          envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y) :=
        mul_le_mul_of_nonneg_right hcf hE0
    _ = 7 / 15 * 1.36065 *
          (K * envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) (r1y y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hKE (by norm_num)

/-- **The far `∫ g̃/r`**: `[r₀, 5.94·10⁶]` by the base regions (`hbase`), then the far envelope
up to `r₁(y)`: `envG(r₁) ≤ z·log r₁` (its `S, T ≥ 0`), `envG(r_F) ≥ −2S̄/s̲ − T̄/r_F`, and
`z·log r₁ ≤ z_F·(8/15)K·y^{−1/6}` (`far_kp`). -/
theorem far_IG (p0 p1 p2 q0 q1 q2 zF Ib Sh Th sl : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (hp2 : 0 ≤ p2) (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hz : 0 ≤ zF)
    (henv : ∀ y r : ℝ, 10 ^ 27 ≤ y → 5940000 ≤ r → r ≤ r1y y →
      OC.gT HW.phi y r ≤ envF p0 p1 p2 0 0 q0 q1 q2 (zF * y ^ (-(1 : ℝ) / 6)) r)
    (hbase : ∀ y : ℝ, 10 ^ 27 ≤ y →
      IntBnd (fun r => OC.gT HW.phi y r / r) 150000 5940000 Ib)
    (hsl0 : 0 < sl) (hsl : sl ≤ Real.sqrt 5940000)
    (hS : (p0 + 2 * p1 + 8 * p2 + 48 * 0 + 384 * 0) +
      (p1 + 4 * p2 + 24 * 0 + 192 * 0) * Real.log 5940000 +
      (p2 + 6 * 0 + 48 * 0) * Real.log 5940000 ^ 2 + (0 + 8 * 0) * Real.log 5940000 ^ 3 +
      0 * Real.log 5940000 ^ 4 ≤ Sh) (hSh : 0 ≤ Sh)
    (hT : (q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log 5940000 + q2 * Real.log 5940000 ^ 2 ≤ Th)
    (y : ℝ) (hyY : 10 ^ 27 ≤ y) :
    OC.intGT HW.phi y ≤ Ib + (2 * (Sh / sl) + Th / 5940000) +
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
  have hreg := intBnd_region (OC.gT HW.phi y) 5940000 (r1y y) p0 p1 p2 0 0 q0 q1 q2
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
  unfold OC.intGT
  linarith

/-! ## The region integrals, `G0Env`, the blocks, the far regime -/

/-- **`∫_{150000}^{520000} g̃(y,r)/r dr ≤ 0.0411149748359`** (`envR0`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR0 (y : ℝ) (hy : (10 ^ 25) ≤ y) :
    IntBnd (fun r => OC.gT HW.phi y r / r) 150000 520000 0.0411149748359 := by
  have hu : envG 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633 0.0000297025673079
      63.3868846831 24.6165165572 0.545031222151 0.000210527045125 520000 ≤ (-0.0606228346869053) :=
      by
    refine (envG_ub 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633
        0.0000297025673079 63.3868846831 24.6165165572 0.545031222151 0.000210527045125 520000
        721.1102551 22.495089240173 521.847049419835 13.1615840952 (by norm_num)
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
      have := tm_ge_pos 25.706579001502 13.1615840856 (Real.log 520000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.545031222151 13.1615840856 (Real.log 520000) 2 (by norm_num) (by norm_num)
          h0
      linarith
  have hl : (-0.101737809522735) ≤ envG 2.94428873212 0.654209332173 0.00636024697078
      0.00173163875633 0.0000297025673079 63.3868846831 24.6165165572 0.545031222151
      0.000210527045125 150000 := by
    refine le_trans (by norm_num) (envG_lb 2.94428873212 0.654209332173 0.00636024697078
        0.00173163875633 0.0000297025673079 63.3868846831 24.6165165572 0.545031222151
        0.000210527045125 150000 387.2983346 19.5768306732186 472.895126176442 11.9183905686
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
      have := tm_le_pos 25.706579001502 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.545031222151 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OC.gT HW.phi y) 150000 520000 2.94428873212
      0.654209332173 0.00636024697078 0.00173163875633 0.0000297025673079 63.3868846831
      24.6165165572 0.545031222151 0.000210527045125 (by norm_num)
    (by norm_num) (fun r hr => envR0 y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envR0_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`∫_{520000}^{1740000} g̃(y,r)/r dr ≤ 0.0242404164143`** (`envR1`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR1 (y : ℝ) (hy : (10 ^ 25) ≤ y) :
    IntBnd (fun r => OC.gT HW.phi y r / r) 520000 1740000 0.0242404164143 := by
  have hu : envG 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033
      0.0000299846672039 65.5968100716 25.1695705188 0.475003664868 0.000211099791842 1740000 ≤
      (-0.036286556639252) := by
    refine (envG_ub 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033
        0.0000299846672039 65.5968100716 25.1695705188 0.475003664868 0.000211099791842 1740000
        1319.090596 25.7190697529685 565.117470970814 14.3693956763 (by norm_num)
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
      have := tm_ge_pos 26.119577848536 14.3693956657 (Real.log 1740000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.475003664868 14.3693956657 (Real.log 1740000) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0605269730535084) ≤ envG 2.98733358573 0.689226963225 (-0.00106021688168)
      0.00203455134033 0.0000299846672039 65.5968100716 25.1695705188 0.475003664868
      0.000211099791842 520000 := by
    refine le_trans (by norm_num) (envG_lb 2.98733358573 0.689226963225 (-0.00106021688168)
        0.00203455134033 0.0000299846672039 65.5968100716 25.1695705188 0.475003664868
        0.000211099791842 520000 721.110255 22.4660672412579 517.775008710075 13.1615840856
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
      have := tm_le_pos 26.119577848536 13.1615840952 (Real.log 520000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.475003664868 13.1615840952 (Real.log 520000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OC.gT HW.phi y) 520000 1740000 2.98733358573
      0.689226963225 (-0.00106021688168) 0.00203455134033 0.0000299846672039 65.5968100716
      25.1695705188 0.475003664868 0.000211099791842 (by norm_num)
    (by norm_num) (fun r hr => envR1 y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envR1_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`∫_{1740000}^{3216000} g̃(y,r)/r dr ≤ 0.008538072095`** (`envR2a`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR2a (y : ℝ) (hy : (10 ^ 25) ≤ y) :
    IntBnd (fun r => OC.gT HW.phi y r / r) 1740000 3216000 0.008538072095 := by
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 3216000 ≤
      (-0.0282694850998952) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 3216000
        1793.320942 28.013065979841 586.582443522775 14.9836489146 (by norm_num)
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
      have := tm_ge_pos 26.203111154492 14.9836489035 (Real.log 3216000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.9836489035 (Real.log 3216000) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.036807557194891) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 562.327481703462 14.3693956657
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
      have := tm_le_pos 26.203111154492 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OC.gT HW.phi y) 1740000 3216000 2.99415982257
      0.688720800761 (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.1586347438
      25.2980058133 0.452552670596 0.000210527045125 (by norm_num)
    (by norm_num) (fun r hr => envR2a y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envR2a_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`∫_{3216000}^{5940000} g̃(y,r)/r dr ≤ 0.00649725963608`** (`envR2b`, `intBnd_region`,
    `envG` at the ends). -/
theorem igR2b (y : ℝ) (hy : (10 ^ 26) ≤ y) :
    IntBnd (fun r => OC.gT HW.phi y r / r) 3216000 5940000 0.00649725963608 := by
  have hu : envG 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
      0.0000310866337797 66.9482087513 25.5001453531 0.431143061793 0.000143820551574 5940000 ≤
      (-0.0215123785288854) := by
    refine (envG_ub 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 66.9482087513 25.5001453531 0.431143061793 0.000143820551574 5940000
        2437.211522 28.8236705767554 609.376854401423 15.5972196969 (by norm_num)
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
      have := tm_ge_pos 26.362431476686 15.5972196853 (Real.log 5940000) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.431143061793 15.5972196853 (Real.log 5940000) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0280096381649558) ≤ envG 3.00843946276 0.700385883674 (-0.00959431030359)
      0.00233394703774 0.0000310866337797 66.9482087513 25.5001453531 0.431143061793
      0.000143820551574 3216000 := by
    refine le_trans (by norm_num) (envG_lb 3.00843946276 0.700385883674 (-0.00959431030359)
        0.00233394703774 0.0000310866337797 66.9482087513 25.5001453531 0.431143061793
        0.000143820551574 3216000 1793.320941 26.8842633715161 585.111872472129 14.9836489035
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
      have := tm_le_pos 26.362431476686 14.9836489146 (Real.log 3216000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.431143061793 14.9836489146 (Real.log 3216000) 2 (by norm_num) hl0 h1
      linarith
  refine intBnd_mono _ _ _ _ _ (intBnd_region (OC.gT HW.phi y) 3216000 5940000 3.00843946276
      0.700385883674 (-0.00959431030359) 0.00233394703774 0.0000310866337797 66.9482087513
      25.5001453531 0.431143061793 0.000143820551574 (by norm_num)
    (by norm_num) (fun r hr => envR2b y r (le_trans (by norm_num) hy) (le_trans (by norm_num) hr.1)
        (le_trans hr.2 (by norm_num)))
    (fun r hr => envR2b_pos r (le_trans (by norm_num) hr.1) (le_trans hr.2 (by norm_num)))) ?_
  linarith

/-- **`G0Env`**: `g̃(y, r₀) ≤ 0.0422891` for `y ≥ 10²⁵` (`envR0` at `r₀ = 150000`). -/
theorem g0Env : G0Env 0.0422891 := by
  intro y hy
  have h0 : 11.9183905686 ≤ Real.log 150000 := lgpL1
  have h1 : Real.log 150000 ≤ 11.9183905772 := lgpU2
  have hl0 : 0 ≤ Real.log 150000 := by linarith
  refine (envR0 y 150000 hy le_rfl (by norm_num)).trans ((envF_le_box 2.94428873212 0.654209332173
      0.00636024697078 0.00173163875633 0.0000297025673079 63.3868846831 24.6165165572
      0.545031222151 0.000210527045125 150000 387.2983346 15.1758360978999 434.196757210212
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.654209332173 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.00636024697078 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
    have := tm_le_pos 0.00173163875633 11.9183905772 (Real.log 150000) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000297025673079 11.9183905772 (Real.log 150000) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 24.6165165572 11.9183905772 (Real.log 150000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.545031222151 11.9183905772 (Real.log 150000) 2 (by norm_num) hl0 h1
    linarith

/-- **`T1Blk`, block 0**: `g̃(y, r₁(y)) ≤ 0.0156479` on `y ∈ [(10 ^ 25), (109 * 10 ^ 23)]`
    (`envR2a` at `r₁(y) ∈ [1740595, 1781060]`). -/
theorem t1Blk0 : T1Blk (10 ^ 25) (109 * 10 ^ 23) 0.0156479 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1740595 ≤ r1y y := MN.r1_ge_of y 1740595 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 1781060 := MN.r1Le_of y 1781060 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.3697375613 ≤ Real.log (r1y y) := lgpL3.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.3927192557 := (Real.log_le_log (by linarith) hru).trans lgpU4
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 (r1y y)
        1319.31611 19.9695180036081 524.012182203978 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.3927192557 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.3697375613 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.3927192557 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.3927192557 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 25.2980058133 14.3927192557 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.3927192557 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlk`, block 0**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.0657177` on `y ∈ [(10 ^ 25), (109 * 10 ^
    23)]`. -/
theorem iGBlk0 : IGBlk (10 ^ 25) (109 * 10 ^ 23) 0.0657177 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1740595 ≤ r1y y := MN.r1_ge_of y 1740595 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 1781060 := MN.r1Le_of y 1781060 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 1781060 ≤
      (-0.0364452674444547) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 1781060
        1334.5636 26.1301441978742 563.242220015242 14.3927192557 (by norm_num)
      (MN.sqrt_le_of _ _ (by norm_num) (by norm_num)) ?_ (by norm_num) ?_ (by norm_num)
          lgpU4).trans (by norm_num)
    · have h0 : 14.3927192451 ≤ Real.log 1781060 := lgpL23
      have h1 : Real.log 1781060 ≤ 14.3927192557 := lgpU4
      have hl0 : 0 ≤ Real.log 1781060 := by linarith
      have := tm_ge_pos 0.7186550723600464 14.3927192451 (Real.log 1781060) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0074835678997616 14.3927192451 (Real.log 1781060) 2 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0027792586469136 14.3927192451 (Real.log 1781060) 3 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.0000353941790317 14.3927192451 (Real.log 1781060) 4 (by norm_num)
          (by norm_num) h0
      linarith
    · have h0 : 14.3927192451 ≤ Real.log 1781060 := lgpL23
      have h1 : Real.log 1781060 ≤ 14.3927192557 := lgpU4
      have hl0 : 0 ≤ Real.log 1781060 := by linarith
      have := tm_ge_pos 26.203111154492 14.3927192451 (Real.log 1781060) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.3927192451 (Real.log 1781060) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.036807557194891) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 562.327481703462 14.3693956657
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
      have := tm_le_pos 26.203111154492 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OC.gT HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 1781060 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.000362289750437 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0 y hyA) (igR1 y hyA)) hlast
  unfold OC.intGT
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1Blk`, block 1**: `g̃(y, r₁(y)) ≤ 0.0155586` on `y ∈ [(109 * 10 ^ 23), (13 * 10 ^ 24)]`
    (`envR2a` at `r₁(y) ∈ [1781059, 1866736]`). -/
theorem t1Blk1 : T1Blk (109 * 10 ^ 23) (13 * 10 ^ 24) 0.0155586 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1781059 ≤ r1y y := MN.r1_ge_of y 1781059 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 1866736 := MN.r1Le_of y 1866736 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.3927186837 ≤ Real.log (r1y y) := lgpL5.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.4397020143 := (Real.log_le_log (by linarith) hru).trans lgpU6
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 (r1y y)
        1334.563224 20.0888472990569 525.813792229654 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.4397020143 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.3927186837 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.4397020143 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.4397020143 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 25.2980058133 14.4397020143 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.4397020143 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlk`, block 1**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.0664377` on `y ∈ [(109 * 10 ^ 23), (13 *
    10 ^ 24)]`. -/
theorem iGBlk1 : IGBlk (109 * 10 ^ 23) (13 * 10 ^ 24) 0.0664377 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1781059 ≤ r1y y := MN.r1_ge_of y 1781059 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 1866736 := MN.r1Le_of y 1866736 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 1866736 ≤
      (-0.0357252804235598) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 1866736
        1366.285476 26.2753875561082 565.086354386219 14.4397020143 (by norm_num)
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
      have := tm_ge_pos 26.203111154492 14.4397020037 (Real.log 1866736) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.4397020037 (Real.log 1866736) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.036807557194891) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 562.327481703462 14.3693956657
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
      have := tm_le_pos 26.203111154492 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OC.gT HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 1866736 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00108227677134 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0 y hyA) (igR1 y hyA)) hlast
  unfold OC.intGT
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1Blk`, block 2**: `g̃(y, r₁(y)) ≤ 0.0153707` on `y ∈ [(13 * 10 ^ 24), (184 * 10 ^ 23)]`
    (`envR2a` at `r₁(y) ∈ [1866735, 2047935]`). -/
theorem t1Blk2 : T1Blk (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0153707 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1866735 ≤ r1y y := MN.r1_ge_of y 1866735 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2047935 := MN.r1Le_of y 2047935 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.439701468 ≤ Real.log (r1y y) := lgpL7.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.5323425314 := (Real.log_le_log (by linarith) hru).trans lgpU8
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 (r1y y)
        1366.285109 20.3256432555094 529.372057234537 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.5323425314 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.439701468 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.5323425314 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.5323425314 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 25.2980058133 14.5323425314 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.5323425314 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlk`, block 2**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.0678198` on `y ∈ [(13 * 10 ^ 24), (184 *
    10 ^ 23)]`. -/
theorem iGBlk2 : IGBlk (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0678198 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 1866735 ≤ r1y y := MN.r1_ge_of y 1866735 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2047935 := MN.r1Le_of y 2047935 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 2047935 ≤
      (-0.0343431757778249) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 2047935
        1431.060796 26.5640078159622 568.728468817052 14.5323425314 (by norm_num)
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
      have := tm_ge_pos 26.203111154492 14.5323425208 (Real.log 2047935) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.5323425208 (Real.log 2047935) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.036807557194891) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 562.327481703462 14.3693956657
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
      have := tm_le_pos 26.203111154492 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OC.gT HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 2047935 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00246438141707 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0 y hyA) (igR1 y hyA)) hlast
  unfold OC.intGT
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1Blk`, block 3**: `g̃(y, r₁(y)) ≤ 0.0150073` on `y ∈ [(184 * 10 ^ 23), (365 * 10 ^ 23)]`
    (`envR2a` at `r₁(y) ∈ [2047934, 2458345]`). -/
theorem t1Blk3 : T1Blk (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0150073 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2047934 ≤ r1y y := MN.r1_ge_of y 2047934 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2458345 := MN.r1Le_of y 2458345 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.5323420326 ≤ Real.log (r1y y) := lgpL9.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.7149989224 := (Real.log_le_log (by linarith) hru).trans lgpU10
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 (r1y y)
        1431.060445 20.8001538869589 536.410532814402 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.7149989224 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.5323420326 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.7149989224 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.7149989224 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 25.2980058133 14.7149989224 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.7149989224 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlk`, block 3**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.070405` on `y ∈ [(184 * 10 ^ 23), (365 *
    10 ^ 23)]`. -/
theorem iGBlk3 : IGBlk (184 * 10 ^ 23) (365 * 10 ^ 23) 0.070405 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2047934 ≤ r1y y := MN.r1_ge_of y 2047934 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 2458345 := MN.r1Le_of y 2458345 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 2458345 ≤
      (-0.0317580009859213) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 2458345
        1567.911031 27.1418176430167 575.932267670262 14.7149989224 (by norm_num)
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
      have := tm_ge_pos 26.203111154492 14.7149989118 (Real.log 2458345) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.7149989118 (Real.log 2458345) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.036807557194891) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 562.327481703462 14.3693956657
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
      have := tm_le_pos 26.203111154492 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OC.gT HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 2458345 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00504955620897 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0 y hyA) (igR1 y hyA)) hlast
  unfold OC.intGT
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1Blk`, block 4**: `g̃(y, r₁(y)) ≤ 0.0141484` on `y ∈ [(365 * 10 ^ 23), (10 ^ 26)]`
    (`envR2a` at `r₁(y) ∈ [2458344, 3216360]`). -/
theorem t1Blk4 : T1Blk (365 * 10 ^ 23) (10 ^ 26) 0.0141484 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2458344 ≤ r1y y := MN.r1_ge_of y 2458344 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 3216360 := MN.r1Le_of y 3216360 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.714998505 ≤ Real.log (r1y y) := lgpL11.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 14.9837608486 := (Real.log_le_log (by linarith) hru).trans lgpU12
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envR2a y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 (r1y y)
        1567.910711 21.5045437703677 546.821901883534 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.688720800761 14.9837608486 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00919198398172) 14.714998505 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00249610521466 14.9837608486 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000353941790317 14.9837608486 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 25.2980058133 14.9837608486 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.452552670596 14.9837608486 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlk`, block 4**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.0738949` on `y ∈ [(365 * 10 ^ 23), (10 ^
    26)]`. -/
theorem iGBlk4 : IGBlk (365 * 10 ^ 23) (10 ^ 26) 0.0738949 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 2458344 ≤ r1y y := MN.r1_ge_of y 2458344 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 3216360 := MN.r1Le_of y 3216360 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (1740000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
      0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 3216360 ≤
      (-0.0282681048700202) := by
    refine (envG_ub 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.1586347438 25.2980058133 0.452552670596 0.000210527045125 3216360
        1793.421312 28.013434366941 586.586894571845 14.9837608486 (by norm_num)
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
      have := tm_ge_pos 26.203111154492 14.9837608375 (Real.log 3216360) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.452552670596 14.9837608375 (Real.log 3216360) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.036807557194891) ≤ envG 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 1740000 := by
    refine le_trans (by norm_num) (envG_lb 2.99415982257 0.688720800761 (-0.00919198398172)
        0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
        0.000210527045125 1740000 1319.090595 26.0583226674089 562.327481703462 14.3693956657
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
      have := tm_le_pos 26.203111154492 14.3693956763 (Real.log 1740000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.452552670596 14.3693956763 (Real.log 1740000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OC.gT HW.phi y) 1740000 (r1y y) 2.99415982257 0.688720800761
      (-0.00919198398172) 0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133
      0.452552670596 0.000210527045125 (by norm_num) hr1
    (fun r hr => envR2a y r hyA hr.1 (hr.2.trans (hru.trans (by norm_num))))
    (fun r hr => envR2a_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 3216360 2.99415982257 0.688720800761 (-0.00919198398172)
      0.00249610521466 0.0000353941790317 66.1586347438 25.2980058133 0.452552670596
      0.000210527045125 (by linarith) hru
    (fun r hr => envR2a_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.00853945232488 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0 y hyA) (igR1 y hyA)) hlast
  unfold OC.intGT
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1Blk`, block 5**: `g̃(y, r₁(y)) ≤ 0.0128533` on `y ∈ [(10 ^ 26), (10 ^ 27)]`
    (`envR2b` at `r₁(y) ∈ [3216359, 5943350]`). -/
theorem t1Blk5 : T1Blk (10 ^ 26) (10 ^ 27) 0.0128533 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 3216359 ≤ r1y y := MN.r1_ge_of y 3216359 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 5943350 := MN.r1Le_of y 5943350 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have h0 : 14.9837605266 ≤ Real.log (r1y y) := lgpL13.trans (Real.log_le_log (by norm_num) hrl)
  have h1 : Real.log (r1y y) ≤ 15.597783511 := (Real.log_le_log (by linarith) hru).trans lgpU14
  have hl0 : 0 ≤ Real.log (r1y y) := by linarith
  refine (envR2b y (r1y y) (le_trans (by norm_num) hy1) (by linarith) (by linarith)).trans
    ((envF_le_box 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 66.9482087513 25.5001453531 0.431143061793 0.000143820551574 (r1y y)
        1793.421032 22.4757477524735 569.58711763982 (by norm_num) (le_trans (by norm_num) hrl) ?_
        ?_ (by norm_num) (by norm_num)).trans (by norm_num))
  · have := tm_le_pos 0.700385883674 15.597783511 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_neg (-0.00959431030359) 14.9837605266 (Real.log (r1y y)) 2 (by norm_num)
        (by norm_num) h0
    have := tm_le_pos 0.00233394703774 15.597783511 (Real.log (r1y y)) 3 (by norm_num) hl0 h1
    have := tm_le_pos 0.0000310866337797 15.597783511 (Real.log (r1y y)) 4 (by norm_num) hl0 h1
    linarith
  · have := tm_le_pos 25.5001453531 15.597783511 (Real.log (r1y y)) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.431143061793 15.597783511 (Real.log (r1y y)) 2 (by norm_num) hl0 h1
    linarith

/-- **`IGBlk`, block 5**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.0803961` on `y ∈ [(10 ^ 26), (10 ^ 27)]`. -/
theorem iGBlk5 : IGBlk (10 ^ 26) (10 ^ 27) 0.0803961 := by
  intro y hy1 hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hrl : 3216359 ≤ r1y y := MN.r1_ge_of y 3216359 hy0.le (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy1 4))
  have hru : r1y y ≤ 5943350 := MN.r1Le_of y 5943350 hy0.le (by norm_num)
    (le_trans (pow_le_pow_left₀ hy0.le hy2 4) (by norm_num))
  have hyA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy1
  have hr1 : (3216000 : ℝ) ≤ r1y y := le_trans (by norm_num) hrl
  have hu : envG 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
      0.0000310866337797 66.9482087513 25.5001453531 0.431143061793 0.000143820551574 5943350 ≤
      (-0.0215070865214639) := by
    refine (envG_ub 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 66.9482087513 25.5001453531 0.431143061793 0.000143820551574 5943350
        2437.898686 28.8255113534785 609.399300934917 15.597783511 (by norm_num)
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
      have := tm_ge_pos 26.362431476686 15.5977834994 (Real.log 5943350) 1 (by norm_num)
          (by norm_num) h0
      have := tm_ge_pos 0.431143061793 15.5977834994 (Real.log 5943350) 2 (by norm_num)
          (by norm_num) h0
      linarith
  have hl : (-0.0280096381649558) ≤ envG 3.00843946276 0.700385883674 (-0.00959431030359)
      0.00233394703774 0.0000310866337797 66.9482087513 25.5001453531 0.431143061793
      0.000143820551574 3216000 := by
    refine le_trans (by norm_num) (envG_lb 3.00843946276 0.700385883674 (-0.00959431030359)
        0.00233394703774 0.0000310866337797 66.9482087513 25.5001453531 0.431143061793
        0.000143820551574 3216000 1793.320941 26.8842633715161 585.111872472129 14.9836489035
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
      have := tm_le_pos 26.362431476686 14.9836489146 (Real.log 3216000) 1 (by norm_num) hl0 h1
      have := tm_le_pos 0.431143061793 14.9836489146 (Real.log 3216000) 2 (by norm_num) hl0 h1
      linarith
  have hreg := intBnd_region (OC.gT HW.phi y) 3216000 (r1y y) 3.00843946276 0.700385883674
      (-0.00959431030359) 0.00233394703774 0.0000310866337797 66.9482087513 25.5001453531
      0.431143061793 0.000143820551574 (by norm_num) hr1
    (fun r hr => envR2b y r (le_trans (by norm_num) hy1) hr.1 (hr.2.trans (hru.trans
        (by norm_num))))
    (fun r hr => envR2b_pos r hr.1 (hr.2.trans (hru.trans (by norm_num))))
  have hmono := envG_mono (r1y y) 5943350 3.00843946276 0.700385883674 (-0.00959431030359)
      0.00233394703774 0.0000310866337797 66.9482087513 25.5001453531 0.431143061793
      0.000143820551574 (by linarith) hru
    (fun r hr => envR2b_pos r (hr1.trans hr.1) (hr.2.trans (by norm_num)))
  have hlast := intBnd_mono _ _ _ _ _ hreg (show _ ≤ (0.0065025516435 : ℝ) by linarith)
  have hall := intBnd_add _ _ _ _ _ _
      (intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _ (igR0 y hyA) (igR1 y hyA)) (igR2a y hyA))
      hlast
  unfold OC.intGT
  exact (le_of_intBnd _ _ _ _ hall).trans (by norm_num)

/-- **`T1Far`**: `cfC(x)·g̃(x/49, r₁) ≤ 0.206012` for `x ≥ 4.9·10²⁸` (`far_T1` on `envRF`). -/
theorem t1Far : T1Far 0.206012 := by
  intro x hx
  have h := far_T1 3.26627202061 1.1187151769 0.0114351675071 69.1334855631 26.1029979906
      0.381494368499 3.09852175891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) coefC_far
    (fun y hy => envRF y (r1y y) hy (MN.r1_ge_of y 5940000 (le_trans (by norm_num) hy)
      (by norm_num) (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy 4))) le_rfl) x hx
  unfold cfC
  exact h.trans (by norm_num)

/-- **`IGFar`**: `∫_{r₀}^{r₁(y)} g̃/r ≤ 0.103905` for `y ≥ 10²⁷` (`far_IG`). -/
theorem iGFar : IGFar 0.103905 := by
  intro y hy
  have hA : (10 ^ 25 : ℝ) ≤ y := le_trans (by norm_num) hy
  have hB : (10 ^ 26 : ℝ) ≤ y := le_trans (by norm_num) hy
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
  have hT : (69.1334855631 + 26.1029979906 + 2 * 0.381494368499) + (26.1029979906 + 2 *
      0.381494368499) * Real.log 5940000 + 0.381494368499 * Real.log 5940000 ^ 2 ≤ 607.841549218713
      := by
    have := tm_le_pos 26.865986727598 15.5972196969 (Real.log 5940000) 1 (by norm_num) hl0 h1
    have := tm_le_pos 0.381494368499 15.5972196969 (Real.log 5940000) 2 (by norm_num) hl0 h1
    linarith
  have hb := fun y (hy : (10 ^ 27 : ℝ) ≤ y) => intBnd_add _ _ _ _ _ _
    (intBnd_add _ _ _ _ _ _ (intBnd_add _ _ _ _ _ _
      (igR0 y (le_trans (by norm_num) hy)) (igR1 y (le_trans (by norm_num) hy)))
      (igR2a y (le_trans (by norm_num) hy))) (igR2b y (le_trans (by norm_num) hy))
  refine (far_IG 3.26627202061 1.1187151769 0.0114351675071 69.1334855631 26.1029979906
      0.381494368499 3.09852175891 _ 26.5393278904435 607.841549218713 2437.211521 (by norm_num)
      (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) envRF hb (by norm_num)
    (MN.sqrt_ge_of _ _ (by norm_num) (by norm_num)) hS (by norm_num) hT y hy).trans ?_
  norm_num

/-! ## THE RESULT -/

/-- **`OC.MNumC HW.phi 8.54 0.791` — PROVED.** The spine `mnumC_of_links` with every link
    discharged. -/
theorem mnumC_proved : OC.MNumC HW.phi 8.54 0.791 :=
  mnumC_of_links gtNonneg g0Env t1Blk0 t1Blk1 t1Blk2 t1Blk3 t1Blk4 t1Blk5 iGBlk0 iGBlk1 iGBlk2
      iGBlk3 iGBlk4 iGBlk5 t1Far iGFar

end Principia.Common.TernaryGoldbach.MC
