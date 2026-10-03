/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.I2Sum

set_option autoImplicit false

/-!
# `MPc.I2Arith`, part 3: the `eq:kallervo2` sum (`|δ| > 1/2c₂`)

The coprime `eq:kallervo2` factor `Gc` is summed by Abel (`I2Sum.sg_abel`); its two
`v`-dependent pieces `S_min = ∑ min(K/n, 2U)` and `S_√ = ∑ √(2U min(K/n, 2U))` are bounded here
and allocated between `W₁ = x/s` and `W₂ = x/s²`:

* `S_regime`: for `z = |δ|q/s ≥ 1`, `S_min ≤ K(1.000112 + log z)`, `S_√ ≤ K(1 + 2√z)`
  (split at `a = ⌊K/(2U)⌋ = ⌊V/z⌋ ≥ 9000`);
* `h_mono`: `h(z)/z` is non-increasing on `[1, ∞)` for `h = A + B log z + C√z`, `A ≥ B ≥ 0`;
* the three regimes `R1_alloc` (`|δ| < 8`, `s ≤ 2.6863`), `R2_alloc` (`|δ| < 8`, `s > 2.6863`),
  `R3_alloc` (`|δ| ≥ 8`), each `4.24378√c₊(1.7721 S_min + 0.36788 S_√) ≤ 0.40 W₁ + B₂ W₂`;
* `B_alloc`: the Chebyshev additive constant and the non-coprime `v` cost `≤ 0.0605 W₁`.
-/

namespace Principia.Common.TernaryGoldbach.I2A

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA Principia.Common.TernaryGoldbach.MPI1
open Finset

/-! ## (1) Monotonicity of `h(z)/z` -/

/-- **`z₀ h(z) ≤ z h(z₀)`** for `1 ≤ z₀ ≤ z`, `h = A + B log + C√`, `0 ≤ B ≤ A`, `0 ≤ C`. -/
theorem h_mono (A B C z0 z : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hAB : B ≤ A) (hz0 : 1 ≤ z0)
    (hz : z0 ≤ z) :
    z0 * (A + B * Real.log z + C * Real.sqrt z) ≤ z * (A + B * Real.log z0 + C * Real.sqrt z0) := by
  have hz00 : 0 < z0 := by linarith
  have hzz : 0 < z := by linarith
  have hl0 : 0 ≤ Real.log z0 := Real.log_nonneg hz0
  have hlog : Real.log z ≤ Real.log z0 + (z / z0 - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hzz hz00)
    rw [Real.log_div hzz.ne' hz00.ne'] at h
    linarith
  have h1 : z0 * Real.log z ≤ z0 * Real.log z0 + (z - z0) := by
    have := mul_le_mul_of_nonneg_left hlog hz00.le
    have e : z0 * (Real.log z0 + (z / z0 - 1)) = z0 * Real.log z0 + (z - z0) := by
      field_simp
    linarith
  have h2 : z0 * Real.log z0 ≤ z * Real.log z0 := mul_le_mul_of_nonneg_right hz hl0
  have hsq0 : Real.sqrt z0 ≤ Real.sqrt z := Real.sqrt_le_sqrt hz
  have hs0 := Real.sqrt_nonneg z0
  have hss0 : Real.sqrt z0 * Real.sqrt z0 = z0 := Real.mul_self_sqrt hz00.le
  have hss : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hzz.le
  have h3 : z0 * Real.sqrt z ≤ z * Real.sqrt z0 := by
    have hsz := Real.sqrt_nonneg z
    have e1 : z0 * Real.sqrt z = Real.sqrt z0 * (Real.sqrt z0 * Real.sqrt z) := by
      rw [← mul_assoc, hss0]
    have e2 : z * Real.sqrt z0 = Real.sqrt z * (Real.sqrt z0 * Real.sqrt z) := by
      have : Real.sqrt z * (Real.sqrt z0 * Real.sqrt z) = (Real.sqrt z * Real.sqrt z) *
          Real.sqrt z0 := by ring
      rw [this, hss]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hsq0 (mul_nonneg hs0 hsz)
  nlinarith [mul_le_mul_of_nonneg_left h1 hB, mul_le_mul_of_nonneg_left h2 hB,
    mul_le_mul_of_nonneg_left h3 hC, mul_le_mul_of_nonneg_right (sub_nonneg.mpr hz)
      (sub_nonneg.mpr hAB)]

/-! ## (2) The two sums for `z ≥ 1` -/

/-- **`S_min ≤ K(1.000112 + log z)`, `S_√ ≤ K(1 + 2√z)`** for `1 ≤ z ≤ 4s`, `s ≤ u`. -/
theorem S_regime (u s K U z : ℝ) (hu : 8000 ≤ u) (hs : 0 < s) (hsu : s ≤ u)
    (hU : U = u ^ 4 / (9 * s)) (hK0 : 0 ≤ K) (hKz : K * z = u ^ 6 / s) (hz1 : 1 ≤ z)
    (hz4 : z ≤ 4 * s) :
    ∑ n ∈ Ioc 1 ⌊4.5 * u ^ 2⌋₊, min (K / n) (2 * U) ≤ K * (1.000112 + Real.log z) ∧
      ∑ n ∈ Ioc 1 ⌊4.5 * u ^ 2⌋₊, Real.sqrt (2 * U * min (K / n) (2 * U)) ≤
        K * (1 + 2 * Real.sqrt z) := by
  have hu0 : 0 < u := by linarith
  have hz0 : 0 < z := by linarith
  have hU0 : 0 < U := by rw [hU]; positivity
  set V : ℝ := 4.5 * u ^ 2 with hV
  have hV0 : 0 < V := by positivity
  have h2UV : 2 * U * V = K * z := by rw [hKz, hU, hV]; field_simp; ring
  have hKU : K / (2 * U) = V / z := by
    rw [div_eq_div_iff (by positivity) hz0.ne']; linarith
  -- `V/z ≥ 9000`
  have hVz : 9000 ≤ V / z := by
    rw [le_div_iff₀ hz0, hV]
    have : 36000 * u ≤ 4.5 * u ^ 2 := by nlinarith
    linarith
  set a := ⌊V / z⌋₊ with ha_def
  set N := ⌊V⌋₊ with hN_def
  have ha1 : 1 ≤ a := Nat.le_floor (by norm_num; linarith)
  have haN : a ≤ N := Nat.floor_le_floor (div_le_self hV0.le hz1)
  have haR : (a : ℝ) ≤ V / z := Nat.floor_le (by positivity)
  have haR' : V / z - 1 < a := by
    have := Nat.lt_floor_add_one (V / z); linarith
  have hKa : 2 * U * a ≤ K := by
    have : 2 * U * a ≤ 2 * U * (V / z) := mul_le_mul_of_nonneg_left haR (by positivity)
    have e : 2 * U * (V / z) = K := by rw [← hKU]; field_simp
    linarith
  have hN1 : 1 ≤ N := le_trans ha1 haN
  have hNR : (N : ℝ) ≤ V := Nat.floor_le hV0.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  constructor
  · have h := smin_le2 K U hU0.le N a ha1 haN hKa
    -- `log N − log a ≤ log z + 0.000112`
    have hlN : Real.log N ≤ Real.log V := Real.log_le_log hN0 hNR
    have hla : Real.log (V / z) - 0.000112 ≤ Real.log a := by
      have hlow : (V / z) * 0.9998888 ≤ a := by nlinarith
      have h1 : Real.log ((V / z) * 0.9998888) ≤ Real.log a :=
        Real.log_le_log (by positivity) hlow
      rw [Real.log_mul (by positivity) (by norm_num)] at h1
      have h2 : -0.000112 ≤ Real.log 0.9998888 := by
        have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.9998888 by norm_num)
        have h3 : (1 : ℝ) - 0.9998888⁻¹ ≥ -0.000112 := by norm_num
        linarith
      linarith
    have hlVz : Real.log (V / z) = Real.log V - Real.log z :=
      Real.log_div hV0.ne' hz0.ne'
    have : Real.log N - Real.log a ≤ Real.log z + 0.000112 := by linarith
    calc ∑ n ∈ Ioc 1 N, min (K / n) (2 * U) ≤ K + K * (Real.log N - Real.log a) := h
      _ ≤ K + K * (Real.log z + 0.000112) := by
          have := mul_le_mul_of_nonneg_left this hK0; linarith
      _ = K * (1.000112 + Real.log z) := by ring
  · have h := ssq_le2 K U hU0.le N a ha1 haN hKa
    have hsN : Real.sqrt (2 * U * K) * Real.sqrt N ≤ K * Real.sqrt z := by
      rw [← Real.sqrt_mul (by positivity)]
      have h1 : 2 * U * K * N ≤ K * K * z := by
        have : 2 * U * K * N ≤ 2 * U * K * V := mul_le_mul_of_nonneg_left hNR (by positivity)
        nlinarith
      calc Real.sqrt (2 * U * K * N) ≤ Real.sqrt (K * K * z) := Real.sqrt_le_sqrt h1
        _ = K * Real.sqrt z := by
            rw [Real.sqrt_mul (mul_self_nonneg K), Real.sqrt_mul_self hK0]
    have hsa := Real.sqrt_nonneg (a : ℝ)
    have hs2 := Real.sqrt_nonneg (2 * U * K)
    calc ∑ n ∈ Ioc 1 N, Real.sqrt (2 * U * min (K / n) (2 * U))
        ≤ K + 2 * Real.sqrt (2 * U * K) * (Real.sqrt N - Real.sqrt a) := h
      _ ≤ K * (1 + 2 * Real.sqrt z) := by nlinarith [mul_nonneg hs2 hsa]

/-! ## (3) The three regimes -/

/-- **(R1)** `|δ| < 8`, `s ≤ 2.6863`: `S_min, S_√ ≤ W₁ = sW₂`, and `√c₊·s ≤ 3.8295`. -/
theorem R1_alloc (s cpr e W2 Sm Sq : ℝ) (hs1 : 1.41421 ≤ s) (hs : s ≤ 2.6863) (hcpr0 : 0 ≤ cpr)
    (hcpr2 : cpr ^ 2 = 1 + e / (2 * s)) (he0 : 0 ≤ e) (he : e ≤ 5.5452) (hW2 : 0 ≤ W2)
    (hSm : Sm ≤ s * W2) (hSq : Sq ≤ s * W2) :
    4.24378 * cpr * (1.7721 * Sm + 0.36788 * Sq) ≤ 34.8 * W2 := by
  have hs0 : 0 < s := by linarith
  have hcs : cpr * s ≤ 3.8295 := by
    have h1 : (cpr * s) ^ 2 ≤ 3.8295 ^ 2 := by
      rw [mul_pow, hcpr2]
      have e1 : (1 + e / (2 * s)) * s ^ 2 = s ^ 2 + e * s / 2 := by field_simp
      rw [e1]
      nlinarith
    nlinarith [sq_nonneg (cpr * s - 3.8295), mul_nonneg hcpr0 hs0.le]
  have h2 : 1.7721 * Sm + 0.36788 * Sq ≤ 2.13998 * (s * W2) := by linarith
  have h3 : 4.24378 * cpr * (1.7721 * Sm + 0.36788 * Sq) ≤ 4.24378 * cpr * (2.13998 * (s * W2)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : 4.24378 * cpr * (2.13998 * (s * W2)) = 4.24378 * 2.13998 * (cpr * s) * W2 := by ring
  rw [e2] at h3
  have h4 : 4.24378 * 2.13998 * (cpr * s) * W2 ≤ 4.24378 * 2.13998 * 3.8295 * W2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs (by norm_num)) hW2
  have h5 : (4.24378 * 2.13998 * 3.8295 : ℝ) ≤ 34.8 := by norm_num
  nlinarith

/-- The scalar inequality of (R2). -/
theorem R2_scalar (s cpr : ℝ) (hs : 2.6863 ≤ s) (hcpr : cpr ≤ 1 + 1.3863 / s) :
    cpr * (11.7162 + 20.1999 * Real.log s + 5.1175 * Real.sqrt s) ≤
      0.40 * s + 65.83 + 53.6064 * Real.log s := by
  have hs0 : 0 < s := by linarith
  have hl0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hls : Real.log s ≤ 0.36788 * s := log_le_div_e s hs0
  have hss := Real.sq_sqrt hs0.le
  have hsq : 1.6389 ≤ Real.sqrt s := by
    rw [Real.le_sqrt (by norm_num) hs0.le]; nlinarith
  set t := Real.sqrt s with ht
  have hcs : cpr * s ≤ s + 1.3863 := by
    have := mul_le_mul_of_nonneg_right hcpr hs0.le
    have e : (1 + 1.3863 / s) * s = s + 1.3863 := by field_simp
    linarith
  have hc1 : cpr ≤ 1.5161 := by
    have : 1.3863 / s ≤ 0.5161 := by rw [div_le_iff₀ hs0]; nlinarith
    linarith
  -- each piece
  have p1 : cpr * 11.7162 ≤ 17.7633 := by nlinarith
  have p2 : cpr * (20.1999 * Real.log s) ≤ 20.1999 * Real.log s + 10.302 := by
    have h1 : cpr * Real.log s * s ≤ (s + 1.3863) * Real.log s := by
      have := mul_le_mul_of_nonneg_right hcs hl0
      nlinarith
    have h2 : cpr * Real.log s ≤ Real.log s + 1.3863 * 0.36788 := by
      have h3 : (s + 1.3863) * Real.log s ≤ s * Real.log s + 1.3863 * (0.36788 * s) := by
        nlinarith
      have h4 : cpr * Real.log s * s ≤ (Real.log s + 1.3863 * 0.36788) * s := by nlinarith
      exact le_of_mul_le_mul_right h4 hs0
    nlinarith
  have p3 : cpr * (5.1175 * t) ≤ 5.1175 * t + 4.329 := by
    have h1 : cpr * t * (t * t) ≤ (t * t + 1.3863) * t := by
      have e : t * t = s := by rw [ht]; exact Real.mul_self_sqrt hs0.le
      rw [e]
      have := mul_le_mul_of_nonneg_right hcs (show (0 : ℝ) ≤ t by linarith)
      nlinarith
    have h2 : cpr * t ≤ t + 1.3863 / t := by
      have ht0 : 0 < t := by linarith
      rw [show t + 1.3863 / t = (t * t + 1.3863) / t by field_simp, le_div_iff₀ ht0]
      have h3 : cpr * t * (t * t) ≤ (t * t + 1.3863) * t := h1
      nlinarith
    have h3 : 1.3863 / t ≤ 0.8459 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have p4 : 5.1175 * t ≤ 0.40 * s + 16.369 := by
    nlinarith [sq_nonneg (0.63246 * t - 4.0457), hss]
  nlinarith

/-- **(R2)** `|δ| < 8`, `s > 2.6863`: `z ≥ 0.3723s ≥ 1`, `K z = W₁ = s W₂`. -/
theorem R2_alloc (s cpr K z Sm Sq W2 : ℝ) (hs : 2.6863 ≤ s) (hcpr0 : 0 ≤ cpr)
    (hcpr : cpr ≤ 1 + 1.3863 / s) (hK : 0 ≤ K) (hKz : K * z = s * W2) (hz : 0.3723 * s ≤ z)
    (hW2 : 0 ≤ W2) (hSm : Sm ≤ K * (1.000112 + Real.log z))
    (hSq : Sq ≤ K * (1 + 2 * Real.sqrt z)) :
    4.24378 * cpr * (1.7721 * Sm + 0.36788 * Sq) ≤
      0.40 * (s * W2) + (65.83 + 53.6064 * Real.log s) * W2 := by
  have hs0 : 0 < s := by linarith
  set z0 := 0.3723 * s with hz0
  have hz01 : 1 ≤ z0 := by rw [hz0]; linarith
  have hzpos : 0 < z := by linarith
  -- `1.7721 S_min + 0.36788 S_√ ≤ K h(z)`
  have hh : 1.7721 * Sm + 0.36788 * Sq ≤
      K * (2.14018 + 1.7721 * Real.log z + 0.73576 * Real.sqrt z) := by
    have h1 := mul_le_mul_of_nonneg_left hSm (by norm_num : (0 : ℝ) ≤ 1.7721)
    have h2 := mul_le_mul_of_nonneg_left hSq (by norm_num : (0 : ℝ) ≤ 0.36788)
    nlinarith
  -- monotonicity: `z₀ h(z) ≤ z h(z₀)`
  have hm := h_mono 2.14018 1.7721 0.73576 z0 z (by norm_num) (by norm_num) (by norm_num) hz01 hz
  have hKh : K * (2.14018 + 1.7721 * Real.log z + 0.73576 * Real.sqrt z) * z0 ≤
      s * W2 * (2.14018 + 1.7721 * Real.log z0 + 0.73576 * Real.sqrt z0) := by
    have := mul_le_mul_of_nonneg_left hm hK
    rw [← hKz]
    nlinarith
  -- `h(z₀) ≤ 1.02783 + 1.7721 log s + 0.44894 √s`
  have hlz0 : Real.log z0 ≤ -0.6277 + Real.log s := by
    rw [hz0, Real.log_mul (by norm_num) hs0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 0.3723 by norm_num)
    linarith
  have hsz0 : Real.sqrt z0 ≤ 0.61017 * Real.sqrt s := by
    rw [hz0, Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg s)
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hhz0 : 2.14018 + 1.7721 * Real.log z0 + 0.73576 * Real.sqrt z0 ≤
      1.02784 + 1.7721 * Real.log s + 0.44895 * Real.sqrt s := by
    nlinarith [Real.sqrt_nonneg s]
  have hKh2 : K * (2.14018 + 1.7721 * Real.log z + 0.73576 * Real.sqrt z) ≤
      W2 / 0.3723 * (1.02784 + 1.7721 * Real.log s + 0.44895 * Real.sqrt s) := by
    have hz00 : 0 < z0 := by linarith
    rw [← le_div_iff₀ hz00] at hKh
    refine hKh.trans ?_
    rw [hz0]
    have e : s * W2 * (2.14018 + 1.7721 * Real.log (0.3723 * s) +
        0.73576 * Real.sqrt (0.3723 * s)) / (0.3723 * s) =
        W2 / 0.3723 * (2.14018 + 1.7721 * Real.log (0.3723 * s) +
          0.73576 * Real.sqrt (0.3723 * s)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hhz0 (by positivity)
  have hsc := R2_scalar s cpr hs hcpr
  have hstep : 4.24378 * cpr * (1.7721 * Sm + 0.36788 * Sq) ≤
      4.24378 * cpr * (W2 / 0.3723 * (1.02784 + 1.7721 * Real.log s + 0.44895 * Real.sqrt s)) :=
    mul_le_mul_of_nonneg_left (hh.trans hKh2) (by positivity)
  have e2 : 4.24378 * cpr * (W2 / 0.3723 * (1.02784 + 1.7721 * Real.log s + 0.44895 *
      Real.sqrt s)) = cpr * (4.24378 / 0.3723 * 1.02784 + 4.24378 / 0.3723 * 1.7721 *
        Real.log s + 4.24378 / 0.3723 * 0.44895 * Real.sqrt s) * W2 := by
    field_simp
  rw [e2] at hstep
  have hc1 : (4.24378 / 0.3723 * 1.02784 : ℝ) ≤ 11.7162 := by norm_num
  have hc2 : (4.24378 / 0.3723 * 1.7721 : ℝ) ≤ 20.1999 := by norm_num
  have hc3 : (4.24378 / 0.3723 * 0.44895 : ℝ) ≤ 5.1175 := by norm_num
  have hl0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hsq0 := Real.sqrt_nonneg s
  have hle : cpr * (4.24378 / 0.3723 * 1.02784 + 4.24378 / 0.3723 * 1.7721 * Real.log s +
      4.24378 / 0.3723 * 0.44895 * Real.sqrt s) ≤
      cpr * (11.7162 + 20.1999 * Real.log s + 5.1175 * Real.sqrt s) := by
    apply mul_le_mul_of_nonneg_left _ hcpr0
    nlinarith
  have hfin := mul_le_mul_of_nonneg_right (hle.trans hsc) hW2
  nlinarith

/-- **(R3)** `|δ| ≥ 8`: `z = 4s`, `K = W₂/4`. -/
theorem R3_alloc (s cpr Sm Sq W2 : ℝ) (hs : 1.41421 ≤ s) (hcpr0 : 0 ≤ cpr) (hcpr : cpr ≤ 1.7207)
    (hW2 : 0 ≤ W2) (hSm : Sm ≤ W2 / 4 * (1.000112 + Real.log (4 * s)))
    (hSq : Sq ≤ W2 / 4 * (1 + 2 * Real.sqrt (4 * s))) :
    4.24378 * cpr * (1.7721 * Sm + 0.36788 * Sq) ≤
      0.40 * (s * W2) + (81.917 + 7.19352 * Real.log s) * W2 := by
  have hs0 : 0 < s := by linarith
  have hl4 : Real.log (4 * s) ≤ 1.3863 + Real.log s := by
    rw [Real.log_mul (by norm_num) hs0.ne']; linarith [log4_le]
  have hs4 : Real.sqrt (4 * s) = 2 * Real.sqrt s := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4] at hSq
  have hl0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hss := Real.sq_sqrt hs0.le
  have hsq0 := Real.sqrt_nonneg s
  have hh : 1.7721 * Sm + 0.36788 * Sq ≤
      W2 / 4 * (4.5969 + 1.7721 * Real.log s + 1.47152 * Real.sqrt s) := by
    have h1 := mul_le_mul_of_nonneg_left hSm (by norm_num : (0 : ℝ) ≤ 1.7721)
    have h2 := mul_le_mul_of_nonneg_left hSq (by norm_num : (0 : ℝ) ≤ 0.36788)
    have h3 : W2 / 4 * (1.000112 + Real.log (4 * s)) ≤ W2 / 4 * (2.386412 + Real.log s) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hstep := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 4.24378 * cpr)
  have hbound : cpr * (4.5969 + 1.7721 * Real.log s + 1.47152 * Real.sqrt s) ≤
      1.7207 * (4.5969 + 1.7721 * Real.log s + 1.47152 * Real.sqrt s) :=
    mul_le_mul_of_nonneg_right hcpr (by positivity)
  have hamgm : 1.7207 * 1.47152 * 4.24378 / 4 * Real.sqrt s ≤ 0.40 * s + 4.52 := by
    nlinarith [sq_nonneg (0.63246 * Real.sqrt s - 2.124), hss]
  have e : 4.24378 * cpr * (W2 / 4 * (4.5969 + 1.7721 * Real.log s + 1.47152 * Real.sqrt s)) =
      4.24378 / 4 * (cpr * (4.5969 + 1.7721 * Real.log s + 1.47152 * Real.sqrt s)) * W2 := by
    ring
  rw [e] at hstep
  have h4 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4.24378 / 4)) hW2
  have h5 : 4.24378 / 4 * (1.7207 * (4.5969 + 1.7721 * Real.log s + 1.47152 * Real.sqrt s)) ≤
      0.40 * s + 81.917 + 7.19352 * Real.log s := by nlinarith
  have h6 := mul_le_mul_of_nonneg_right h5 hW2
  nlinarith

/-! ## (4) The Chebyshev constant and the non-coprime `v` -/

/-- `U = W₁/(9u²)`. -/
theorem U_eq_W1 (u s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    u ^ 4 / (9 * s) = u ^ 6 / s / (9 * u ^ 2) := by
  field_simp

/-- **(T1)** `3.8246√c₊·(A+B)·4.27996U ≤ 0.05624 W₁`. -/
theorem bT1 (u W1 U cpr : ℝ) (hu : 8000 ≤ u) (hUW : U = W1 / (9 * u ^ 2)) (hW1 : 0 ≤ W1)
    (hcpr : cpr ≤ 1.7207) :
    3.8246 * cpr * ((1.1096 + 1150000) * (4.27996 * U)) ≤ 0.05624 * W1 := by
  have hu2 : (64000000 : ℝ) ≤ u ^ 2 := by nlinarith
  rw [hUW]
  have h1 : 3.8246 * cpr * ((1.1096 + 1150000) * (4.27996 * (W1 / (9 * u ^ 2)))) ≤
      6.581 * ((1.1096 + 1150000) * (4.27996 * (W1 / (9 * u ^ 2)))) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have e : 6.581 * ((1.1096 + 1150000) * (4.27996 * (W1 / (9 * u ^ 2)))) =
      (6.581 * (1.1096 + 1150000) * 4.27996 / 9) * W1 / u ^ 2 := by field_simp
  rw [e] at h1
  have h2 : (6.581 * (1.1096 + 1150000) * 4.27996 / 9) * W1 / u ^ 2 ≤ 0.05624 * W1 := by
    rw [div_le_iff₀ (by positivity)]
    have : (6.581 * (1.1096 + 1150000) * 4.27996 / 9 : ℝ) ≤ 0.05624 * 64000000 := by norm_num
    nlinarith
  linarith

/-- **(T2)** `3.8246√c₊·(A+B)(1.7721 + log⁺z/2) ≤ 0.0001 W₁`. -/
theorem bT2 (u W1 cpr lzv : ℝ) (hu : 8000 ≤ u) (hW1u : u ^ 5 ≤ W1)
    (hcpr : cpr ≤ 1.7207) (hlz0 : 0 ≤ lzv) (hb : 1.7721 + lzv / 2 ≤ 6.2024 + u / 16000) :
    3.8246 * cpr * ((1.1096 + 1150000) * (1.7721 + lzv / 2)) ≤ 0.0001 * W1 := by
  have hu0 : 0 < u := by linarith
  have hu2 : (64000000 : ℝ) ≤ u ^ 2 := by nlinarith
  have hu4 : (4096000000000000 : ℝ) ≤ u ^ 4 := by
    have := mul_le_mul hu2 hu2 (by norm_num) (by positivity)
    nlinarith
  have h1 : 3.8246 * cpr * ((1.1096 + 1150000) * (1.7721 + lzv / 2)) ≤
      6.581 * ((1.1096 + 1150000) * (6.2024 + u / 16000)) :=
    mul_le_mul (by nlinarith) (mul_le_mul_of_nonneg_left hb (by norm_num)) (by positivity)
      (by norm_num)
  have h2 : 6.581 * ((1.1096 + 1150000) * (6.2024 + u / 16000)) ≤ 0.0001 * u ^ 5 := by
    have e : u ^ 5 = u * u ^ 4 := by ring
    rw [e]
    nlinarith
  linarith

/-- **(T3)** `3.8246√c₊·A(N−1)(1.7721 + log⁺z/2) ≤ 0.0001 W₁`. -/
theorem bT3 (u W1 cpr lzv N : ℝ) (hu : 8000 ≤ u) (hW1u : u ^ 5 ≤ W1)
    (hcpr : cpr ≤ 1.7207) (hlz0 : 0 ≤ lzv) (hb : 1.7721 + lzv / 2 ≤ 6.2024 + u / 16000)
    (hN1 : 1 ≤ N) (hN : N ≤ 4.5 * u ^ 2) :
    3.8246 * cpr * (1.1096 * (N - 1) * (1.7721 + lzv / 2)) ≤ 0.0001 * W1 := by
  have hu0 : 0 < u := by linarith
  have h1 : 3.8246 * cpr * (1.1096 * (N - 1) * (1.7721 + lzv / 2)) ≤
      6.581 * (1.1096 * (4.5 * u ^ 2) * (6.2024 + u / 16000)) :=
    mul_le_mul (by nlinarith) (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
      hb (by linarith) (by positivity)) (by positivity) (by norm_num)
  have h2 : 6.581 * (1.1096 * (4.5 * u ^ 2) * (6.2024 + u / 16000)) ≤ 0.0001 * u ^ 5 := by
    have e : 6.581 * (1.1096 * (4.5 * u ^ 2) * (6.2024 + u / 16000)) =
        u ^ 2 * (6.581 * 1.1096 * 4.5 * 6.2024 + 6.581 * 1.1096 * 4.5 / 16000 * u) := by ring
    have e2 : 0.0001 * u ^ 5 = u ^ 2 * (0.0001 * u ^ 3) := by ring
    rw [e, e2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hu3 : 512000000000 ≤ u ^ 3 := by nlinarith
    nlinarith
  linarith

/-- **(T4)** the non-coprime `v`: `3.8246√c₊·2U(1.7721 + log⁺z/2)(log q/log 3)(log N) ≤
0.00301 W₁`. -/
theorem bT4 (u W1 U cpr lzv lam Lq LN l3 : ℝ) (hu : 8000 ≤ u) (hUW : U = W1 / (9 * u ^ 2))
    (hW1 : 0 ≤ W1) (hcpr : cpr ≤ 1.7207) (hlz : lzv ≤ lam + 0.8496)
    (hlz0 : 0 ≤ lzv) (hlam : 8.3 ≤ lam) (hlamU : lam ≤ 8.011 + u / 8000)
    (hlam2 : lam ^ 2 ≤ 0.5414 * u) (hLq0 : 0 ≤ Lq) (hLq : Lq ≤ 2 * lam) (hLN0 : 0 ≤ LN)
    (hLN : LN ≤ 2 * lam + 1.6555) (hl3 : 1 ≤ l3) :
    3.8246 * cpr * (2 * U * (1.7721 + lzv / 2) * (Lq / l3 * LN)) ≤ 0.00301 * W1 := by
  have hu0 : 0 < u := by linarith
  have hU0 : 0 ≤ U := by rw [hUW]; positivity
  have hLq3 : Lq / l3 ≤ 2 * lam := (div_le_self hLq0 hl3).trans hLq
  have hLq30 : 0 ≤ Lq / l3 := div_nonneg hLq0 (by linarith)
  have hp1 : 1.7721 + lzv / 2 ≤ 0.7647 * lam := by linarith
  have hp2 : Lq / l3 * LN ≤ 2 * lam * (2.19946 * lam) :=
    mul_le_mul hLq3 (by linarith) hLN0 (by linarith)
  have hp3 : (1.7721 + lzv / 2) * (Lq / l3 * LN) ≤ 0.7647 * lam * (2 * lam * (2.19946 * lam)) :=
    mul_le_mul hp1 hp2 (mul_nonneg hLq30 hLN0) (by linarith)
  have hl3c : lam ^ 3 ≤ 0.00060983 * u ^ 2 := by
    have h1 : lam ^ 3 ≤ (8.011 + u / 8000) * (0.5414 * u) := by
      rw [show lam ^ 3 = lam * lam ^ 2 by ring]
      exact mul_le_mul hlamU hlam2 (by positivity) (by positivity)
    nlinarith
  have hA : 3.8246 * cpr * (2 * U * (1.7721 + lzv / 2) * (Lq / l3 * LN)) ≤
      6.581 * (2 * U * (0.7647 * lam * (2 * lam * (2.19946 * lam)))) := by
    have e : 3.8246 * cpr * (2 * U * (1.7721 + lzv / 2) * (Lq / l3 * LN)) =
        3.8246 * cpr * (2 * U * ((1.7721 + lzv / 2) * (Lq / l3 * LN))) := by ring
    rw [e]
    exact mul_le_mul (by nlinarith) (mul_le_mul_of_nonneg_left hp3 (by positivity))
      (by positivity) (by norm_num)
  have hB : 6.581 * (2 * U * (0.7647 * lam * (2 * lam * (2.19946 * lam)))) =
      6.581 * 2 * 0.7647 * 2 * 2.19946 / 9 * lam ^ 3 * W1 / u ^ 2 := by
    rw [hUW]; field_simp
  rw [hB] at hA
  have hC : 6.581 * 2 * 0.7647 * 2 * 2.19946 / 9 * lam ^ 3 * W1 / u ^ 2 ≤ 0.00301 * W1 := by
    rw [div_le_iff₀ (by positivity)]
    have hk : (6.581 * 2 * 0.7647 * 2 * 2.19946 / 9 * 0.00060983 : ℝ) ≤ 0.00301 := by norm_num
    have h1 := mul_le_mul_of_nonneg_left hl3c (by positivity :
      (0 : ℝ) ≤ 6.581 * 2 * 0.7647 * 2 * 2.19946 / 9 * W1)
    nlinarith
  linarith

/-- **The leftover `eq:kallervo2` terms cost `≤ 0.0605 W₁`.** -/
theorem B_alloc (u s lam U N cpr lzv Lq LN l3 : ℝ) (hu : 8000 ≤ u) (hs : 1.41421 ≤ s)
    (hsu : s ≤ u) (hU : U = u ^ 4 / (9 * s)) (hcpr : cpr ≤ 1.7207)
    (hlz0 : 0 ≤ lzv) (hlz : lzv ≤ lam + 0.8496) (hlam : 8.3 ≤ lam)
    (hlamU : lam ≤ 8.011 + u / 8000) (hlam2 : lam ^ 2 ≤ 0.5414 * u) (hN1 : 1 ≤ N)
    (hN : N ≤ 4.5 * u ^ 2) (hLq0 : 0 ≤ Lq) (hLq : Lq ≤ 2 * lam) (hLN0 : 0 ≤ LN)
    (hLN : LN ≤ 2 * lam + 1.6555) (hl3 : 1 ≤ l3) :
    3.8246 * cpr * ((1.1096 + 1150000) * (4.27996 * U + 1.7721 + lzv / 2) +
        1.1096 * (N - 1) * (1.7721 + lzv / 2) + 2 * U * (1.7721 + lzv / 2) * (Lq / l3 * LN)) ≤
      0.0605 * (u ^ 6 / s) := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hUW : U = u ^ 6 / s / (9 * u ^ 2) := by rw [hU]; exact U_eq_W1 u s hu0 hs0
  have hW1u : u ^ 5 ≤ u ^ 6 / s := by
    rw [le_div_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left hsu (by positivity : (0 : ℝ) ≤ u ^ 5)
    nlinarith
  have hW10 : 0 ≤ u ^ 6 / s := by positivity
  have hb : 1.7721 + lzv / 2 ≤ 6.2024 + u / 16000 := by linarith
  have t1 := bT1 u (u ^ 6 / s) U cpr hu hUW hW10 hcpr
  have t2 := bT2 u (u ^ 6 / s) cpr lzv hu hW1u hcpr hlz0 hb
  have t3 := bT3 u (u ^ 6 / s) cpr lzv N hu hW1u hcpr hlz0 hb hN1 hN
  have t4 := bT4 u (u ^ 6 / s) U cpr lzv lam Lq LN l3 hu hUW hW10 hcpr hlz hlz0 hlam
    hlamU hlam2 hLq0 hLq hLN0 hLN hl3
  have e : 3.8246 * cpr * ((1.1096 + 1150000) * (4.27996 * U + 1.7721 + lzv / 2) +
      1.1096 * (N - 1) * (1.7721 + lzv / 2) + 2 * U * (1.7721 + lzv / 2) * (Lq / l3 * LN)) =
      3.8246 * cpr * ((1.1096 + 1150000) * (4.27996 * U)) +
        3.8246 * cpr * ((1.1096 + 1150000) * (1.7721 + lzv / 2)) +
        3.8246 * cpr * (1.1096 * (N - 1) * (1.7721 + lzv / 2)) +
        3.8246 * cpr * (2 * U * (1.7721 + lzv / 2) * (Lq / l3 * LN)) := by ring
  rw [e]
  linarith

end Principia.Common.TernaryGoldbach.I2A
