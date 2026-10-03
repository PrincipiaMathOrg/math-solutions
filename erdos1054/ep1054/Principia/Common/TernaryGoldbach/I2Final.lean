/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.I2Sum

set_option autoImplicit false

/-!
# `MPc.I2Arith` PROVED: the Totals algebra of `S_{I,2}`

`I2Sum.sum_le_tot` bounds `∑_{v ≤ V} Λ(v) f(v) T(v)` by an explicit total `TOT`; here
`TOT ≤ MT.bI2` (`eq:cleson` as corrected in Helfgott's book) for every admissible `(x, δ, q)`.
With `u = x^{1/6} ≥ 8000`, `s = √(δ₀q)`, `W₁ = x/s`, `W₂ = x/s²`:

* the `μ`-sum part meets `min(1, 4c₀'/δ²)(3/2 log q + 2.74107)x/φ(q)` up to `(0.5 log q +
  6.1864)W₂` (`a1_alloc`), via `mR·(ℓ* + c) ≤ 1.6(q/φ(q)) + c`;
* the main term `3.5743·U·ψ(V) ≤ 1.99018 W₁ + 2.759 W₂` (`m_alloc`, Chebyshev's `1.1096`);
* `|δ| ≤ 1/2c₂`: the `t log⁺(B/t) ≤ B/e` term adds `0.45764 W₁` (`keks_alloc`): `2.44782 ≤ 2.49157`;
* `|δ| > 1/2c₂`: the `eq:kallervo2` factor, summed by Abel, costs `≤ 0.40 W₁ + B₂ W₂`
  (`kall_K_alloc`), split three ways: `|δ| < 8, s ≤ 2.6863` (everything into `W₂`), `|δ| < 8,
  s > 2.6863` (`z = |δ|s/2 ≥ 0.3723 s ≥ 1`, monotonicity of `h(z)/z`, AM-GM on `√s`), and
  `|δ| ≥ 8` (`z = 4s`, `K = W₂/4`).

Scoped (`scratchpad/i2a/model2.py`): the chain's worst ratio is `0.979` (`|δ| ≤ 1/2c₂`,
`x → ∞`, where only the linear `W₁` coefficients matter) and `0.816` (`|δ| > 1/2c₂`).
-/

namespace Principia.Common.TernaryGoldbach.I2A

open ArithmeticFunction
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA Principia.Common.TernaryGoldbach.MPI1
open Finset

/-! ## (1) Abstract allocations -/

/-- **The `μ`-sum part.** `Y2q = x/(2q)`, so `x/φ(q) = 2·Y2q·R` and `x/(qδ₀) = 2·Y2q/δ₀`. -/
theorem a1_alloc (capA cap4 d0 R m Lq ls LN Y2q : ℝ) (hc0 : 0 ≤ capA) (hc4 : capA ≤ cap4)
    (hd0 : 0 < d0) (hcd : capA ≤ 2 / d0) (hR : 1 ≤ R) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hml : m * ls ≤ 1.6 * R) (hLN : LN ≤ ls + 2 * Lq + 4.6822) (hLq : 0 ≤ Lq) (hY : 0 ≤ Y2q) :
    capA * Y2q * (m * (LN + 5.3863) + 3 / 2 * Lq) ≤
      cap4 * (2 * Y2q * R) * (3 / 2 * Lq + 2.74107) + (0.5 * Lq + 6.1864) * (2 * Y2q / d0) := by
  have h1 : m * (LN + 5.3863) ≤ 1.6 * R + 2 * Lq + 10.0685 := by
    have : m * LN ≤ m * (ls + 2 * Lq + 4.6822) := mul_le_mul_of_nonneg_left hLN hm0
    have h2 : m * (2 * Lq + 10.0685) ≤ 2 * Lq + 10.0685 :=
      mul_le_of_le_one_left (by linarith) hm1
    nlinarith
  have hX : capA * (m * (LN + 5.3863) + 3 / 2 * Lq) ≤
      cap4 * R * (3 * Lq + 5.48214) + capA * (0.5 * Lq + 6.1864) := by
    have hA : capA * (m * (LN + 5.3863) + 3 / 2 * Lq) ≤ capA * (1.6 * R + 3.5 * Lq + 10.0685) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    have hB : capA * (1.6 * R + 3 * Lq + 3.88214) ≤ cap4 * R * (3 * Lq + 5.48214) := by
      have hc4R : capA ≤ cap4 * R := hc4.trans (by nlinarith)
      have hcR : capA * R ≤ cap4 * R := mul_le_mul_of_nonneg_right hc4 (by linarith)
      nlinarith [mul_nonneg hc0 hLq, mul_nonneg (sub_nonneg.mpr hR) hLq]
    nlinarith
  have hD : capA * (0.5 * Lq + 6.1864) ≤ (2 / d0) * (0.5 * Lq + 6.1864) :=
    mul_le_mul_of_nonneg_right hcd (by linarith)
  have e1 : capA * Y2q * (m * (LN + 5.3863) + 3 / 2 * Lq) =
      Y2q * (capA * (m * (LN + 5.3863) + 3 / 2 * Lq)) := by ring
  have e2 : cap4 * (2 * Y2q * R) * (3 / 2 * Lq + 2.74107) + (0.5 * Lq + 6.1864) * (2 * Y2q / d0) =
      Y2q * (cap4 * R * (3 * Lq + 5.48214) + (2 / d0) * (0.5 * Lq + 6.1864)) := by
    field_simp; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (by linarith) hY

/-- **`A2`**: `2.3433(U² + 2U + q)/x·(NΨ) ≤ 0.6524 W₂ + 9u²`. -/
theorem a2_alloc (u s U N P q : ℝ) (hu : 8000 ≤ u) (hs : 1.41421 ≤ s) (hU : U = u ^ 4 / (9 * s))
    (hN : N ≤ 4.5 * u ^ 2) (hP0 : 0 ≤ P) (hP : P ≤ 5.0112 * u ^ 2) (hq0 : 0 ≤ q)
    (hq : q ≤ u ^ 2 / 6) :
    2.3433 * (U ^ 2 + 2 * U + q) / u ^ 6 * (N * P) ≤ 0.6524 * (u ^ 6 / s ^ 2) + 9 * u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hNP : N * P ≤ 4.5 * u ^ 2 * (5.0112 * u ^ 2) := mul_le_mul hN hP hP0 (by positivity)
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hpos : 0 ≤ 2.3433 * (U ^ 2 + 2 * U + q) / u ^ 6 := by positivity
  have h1 : 2.3433 * (U ^ 2 + 2 * U + q) / u ^ 6 * (N * P) ≤
      2.3433 * (U ^ 2 + 2 * U + q) / u ^ 6 * (4.5 * u ^ 2 * (5.0112 * u ^ 2)) :=
    mul_le_mul_of_nonneg_left hNP hpos
  have e2 : 2.3433 * (U ^ 2 + 2 * U + q) / u ^ 6 * (4.5 * u ^ 2 * (5.0112 * u ^ 2)) =
      (2.3433 * 4.5 * 5.0112) * (U ^ 2 / u ^ 2) + (2.3433 * 4.5 * 5.0112) * 2 * (U / u ^ 2) +
        (2.3433 * 4.5 * 5.0112) * (q / u ^ 2) := by
    field_simp
  have hU2 : U ^ 2 / u ^ 2 = u ^ 6 / s ^ 2 / 81 := by rw [hU]; field_simp; norm_num
  have hU1 : U / u ^ 2 ≤ 0.70711 * u ^ 2 / 9 := by
    rw [hU, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_pos hu0 2, pow_pos hu0 4, pow_pos hu0 6]
  have hq2 : q / u ^ 2 ≤ 1 / 6 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hW2 : 0 ≤ u ^ 6 / s ^ 2 := by positivity
  have hu2 : (64000000 : ℝ) ≤ u ^ 2 := by nlinarith
  rw [e2, hU2] at h1
  nlinarith

/-- **The main term**: `3.5743·U·(Ψ + |η'|₁U/(2x)·NΨ) ≤ 1.99018 W₁ + 2.759 W₂`. -/
theorem m_alloc (u s U N P e : ℝ) (hu : 8000 ≤ u) (hs : 1.41421 ≤ s) (hU : U = u ^ 4 / (9 * s))
    (hN0 : 0 ≤ N) (hN : N ≤ 4.5 * u ^ 2) (hP0 : 0 ≤ P) (hP : P ≤ 5.0112 * u ^ 2) (he0 : 0 ≤ e)
    (he : e ≤ 5.5452) :
    3.5743 * U * (P + e * U / (2 * u ^ 6) * (N * P)) ≤
      1.99018 * (u ^ 6 / s) + 2.759 * (u ^ 6 / s ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hUP : U * P ≤ 0.5568 * (u ^ 6 / s) := by
    rw [hU]
    calc u ^ 4 / (9 * s) * P ≤ u ^ 4 / (9 * s) * (5.0112 * u ^ 2) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 0.5568 * (u ^ 6 / s) := by field_simp; ring
  have hc : e * U * N / (2 * u ^ 6) ≤ 1.3863 / s := by
    rw [hU, div_le_div_iff₀ (by positivity) hs0]
    have h1 : e * (u ^ 4 / (9 * s)) * N * s = e * N * u ^ 4 / 9 := by field_simp
    rw [h1]
    have h2 : e * N ≤ 5.5452 * (4.5 * u ^ 2) := mul_le_mul he hN hN0 (by norm_num)
    nlinarith [pow_pos hu0 4]
  have hc0 : 0 ≤ e * U * N / (2 * u ^ 6) := by positivity
  have e1 : 3.5743 * U * (P + e * U / (2 * u ^ 6) * (N * P)) =
      3.5743 * (U * P) * (1 + e * U * N / (2 * u ^ 6)) := by field_simp
  rw [e1]
  have hUP0 : 0 ≤ U * P := mul_nonneg hU0 hP0
  have hW1 : 0 ≤ u ^ 6 / s := by positivity
  have hW2 : 0 ≤ u ^ 6 / s ^ 2 := by positivity
  calc 3.5743 * (U * P) * (1 + e * U * N / (2 * u ^ 6))
      ≤ 3.5743 * (0.5568 * (u ^ 6 / s)) * (1 + 1.3863 / s) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    _ = 1.99017024 * (u ^ 6 / s) + 1.99017024 * 1.3863 * (u ^ 6 / s ^ 2) := by
        field_simp; ring
    _ ≤ 1.99018 * (u ^ 6 / s) + 2.759 * (u ^ 6 / s ^ 2) := by
        have : (1.99017024 * 1.3863 : ℝ) ≤ 2.759 := by norm_num
        nlinarith

/-- `U·Ψ ≤ 0.5568 W₁`. -/
theorem UP_le (u s U P : ℝ) (hs : 0 < s) (hU : U = u ^ 4 / (9 * s)) (hP : P ≤ 5.0112 * u ^ 2) :
    U * P ≤ 0.5568 * (u ^ 6 / s) := by
  rw [hU]
  calc u ^ 4 / (9 * s) * P ≤ u ^ 4 / (9 * s) * (5.0112 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = 0.5568 * (u ^ 6 / s) := by field_simp; ring

/-- **`|δ| ≤ 1/2c₂`**: `(0.8219c₊U + k_q q)Ψ ≤ 0.45764 W₁ + 1.269 W₂ + (10.28λ + 32)u⁴`. -/
theorem keks_alloc (u s U P q cp kqv lam e : ℝ) (hs : 1.41421 ≤ s) (hU : U = u ^ 4 / (9 * s))
    (hP0 : 0 ≤ P) (hP : P ≤ 5.0112 * u ^ 2) (hq0 : 0 ≤ q) (hq : q ≤ u ^ 2 / 6)
    (hcp : cp = 1 + e / (2 * s)) (he0 : 0 ≤ e) (he : e ≤ 5.5452)
    (hk : kqv ≤ 12.3006 * lam + 38.07) (hlam : 0 ≤ lam) :
    (0.8219 * cp * U + kqv * q) * P ≤
      0.45764 * (u ^ 6 / s) + 1.269 * (u ^ 6 / s ^ 2) + (10.28 * lam + 32) * u ^ 4 := by
  have hs0 : 0 < s := by linarith
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hUP := UP_le u s U P hs0 hU hP
  have hcp1 : cp ≤ 1 + 2.7726 / s := by
    rw [hcp]
    have : e / (2 * s) ≤ 2.7726 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]; nlinarith
    linarith
  have hcp0 : 0 ≤ cp := by rw [hcp]; positivity
  have hW1 : 0 ≤ u ^ 6 / s := by positivity
  have h1 : 0.8219 * cp * U * P ≤ 0.8219 * (1 + 2.7726 / s) * (0.5568 * (u ^ 6 / s)) := by
    have := mul_le_mul hcp1 hUP (mul_nonneg hU0 hP0) (by positivity)
    nlinarith
  have e1 : 0.8219 * (1 + 2.7726 / s) * (0.5568 * (u ^ 6 / s)) =
      0.45763392 * (u ^ 6 / s) + 0.45763392 * 2.7726 * (u ^ 6 / s ^ 2) := by field_simp; ring
  have hqP : q * P ≤ u ^ 2 / 6 * (5.0112 * u ^ 2) := mul_le_mul hq hP hP0 (by positivity)
  have h2 : kqv * q * P ≤ (12.3006 * lam + 38.07) * (u ^ 2 / 6 * (5.0112 * u ^ 2)) := by
    have := mul_le_mul hk hqP (mul_nonneg hq0 hP0) (by linarith)
    nlinarith
  have hW2 : 0 ≤ u ^ 6 / s ^ 2 := by positivity
  have e3 : (12.3006 * lam + 38.07) * (u ^ 2 / 6 * (5.0112 * u ^ 2)) =
      (10.27346112 * lam + 31.796064) * u ^ 4 := by ring
  have hu4 : 0 ≤ u ^ 4 := by positivity
  nlinarith [mul_nonneg hlam hu4]

/-- `log(4s) ≤ 1.2256 s` for `s ≥ 1.41421`. -/
theorem log4s_le (s : ℝ) (hs : 1.41421 ≤ s) : Real.log (4 * s) ≤ 1.2256 * s := by
  have hs0 : 0 < s := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < s / 1.41421 by positivity)
  rw [Real.log_div hs0.ne' (by norm_num)] at h1
  have h2 : Real.log 1.41421 ≤ 0.34658 := by
    have h3 : Real.log (1.41421 ^ 2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h3
    have := Real.log_two_lt_d9
    push_cast at h3
    linarith
  have h4 := log4_le
  rw [Real.log_mul (by norm_num) hs0.ne']
  have h5 : s / 1.41421 ≤ 0.70711 * s := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

/-- **`|δ| > 1/2c₂`, the `eq:kallervo2` `(3/2)c₁` line and `35c₀c₂/(3π²)`**:
`≤ (137.887λ + 411.424)u⁴ + 0.035 W₁`. -/
theorem L_alloc (u s lam cp lzv P q e : ℝ) (hu : 8000 ≤ u) (hs : 1.41421 ≤ s)
    (hs3 : 3 * s ^ 2 ≤ u ^ 2) (hcp : cp = 1 + e / (2 * s)) (he0 : 0 ≤ e) (he : e ≤ 5.5452)
    (hlz0 : 0 ≤ lzv) (hlz : lzv ≤ Real.log (4 * s)) (hlam : Real.log u = lam)
    (hlamU : lam ≤ 8.011 + u / 8000) (hP0 : 0 ≤ P) (hP : P ≤ 5.0112 * u ^ 2)
    (hq : q ≤ u ^ 2 / 6) :
    (2 * cp * u ^ 2 * (2 + 15.2858 * lzv) + 25.03 * q) * P ≤
      (137.887 * lam + 411.424) * u ^ 4 + 0.035 * (u ^ 6 / s) := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  -- `4s ≤ 2.30941u`, so `log(4s) ≤ λ + 0.8496`
  have h4s : 4 * s ≤ 2.30941 * u := by nlinarith
  have hl4s : Real.log (4 * s) ≤ lam + 0.8496 := by
    have h1 : Real.log (4 * s) ≤ Real.log (2.30941 * u) := Real.log_le_log (by positivity) h4s
    rw [Real.log_mul (by norm_num) hu0.ne', hlam] at h1
    have := log_le_div_e 2.30941 (by norm_num)
    linarith
  have hcl : cp * lzv ≤ lzv + 3.3981 := by
    rw [hcp]
    have h1 := log4s_le s hs
    have h2 : e / (2 * s) * lzv ≤ 2.7726 * 1.2256 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : lzv ≤ 1.2256 * s := hlz.trans h1
      nlinarith
    nlinarith
  have hcp1 : cp ≤ 2.9606 := by
    rw [hcp]
    have : e / (2 * s) ≤ 1.9606 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hcp0 : 0 ≤ cp := by rw [hcp]; positivity
  have hA : cp * (2 + 15.2858 * lzv) ≤ 15.2858 * lam + 70.86 := by nlinarith
  have hA0 : 0 ≤ cp * (2 + 15.2858 * lzv) := by positivity
  have hB : 2 * cp * u ^ 2 * (2 + 15.2858 * lzv) * P ≤
      2 * u ^ 2 * (15.2858 * lam + 70.86) * (5.0112 * u ^ 2) := by
    have e : 2 * cp * u ^ 2 * (2 + 15.2858 * lzv) * P =
        2 * u ^ 2 * (cp * (2 + 15.2858 * lzv)) * P := by ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hP hP0 (by nlinarith)
  have hC : 25.03 * q * P ≤ 25.03 * (u ^ 2 / 6) * (5.0112 * u ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hP hP0 (by positivity)
  -- the excess `(15.32λ + 320)u⁴ ≤ 0.035 u⁶/s`
  have hsu : s ≤ 0.57736 * u := by nlinarith
  have hex : (15.32 * lam + 320) * u ^ 4 ≤ 0.035 * (u ^ 6 / s) := by
    rw [show 0.035 * (u ^ 6 / s) = 0.035 * u ^ 6 / s by ring, le_div_iff₀ hs0, mul_comm]
    have h1 : 15.32 * lam + 320 ≤ 0.06062 * u := by nlinarith
    have h2 : s * ((15.32 * lam + 320) * u ^ 4) ≤ 0.57736 * u * (0.06062 * u * u ^ 4) := by
      have h0 : 0 ≤ 15.32 * lam + 320 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ u by linarith)
        rw [hlam] at this
        linarith
      apply mul_le_mul hsu (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
        (by positivity)
    nlinarith [pow_pos hu0 4, pow_pos hu0 6]
  nlinarith [pow_pos hu0 4]

end Principia.Common.TernaryGoldbach.I2A
