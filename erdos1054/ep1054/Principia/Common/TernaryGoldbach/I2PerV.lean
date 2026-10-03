/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPiecesII

set_option autoImplicit false

/-!
# `MPc.I2Arith`, part 1: the per-`v` majorant of `lem:bosta2`

`MPc.I2Arith` sums `Λ(v) f(v) T(v)` over `v ≤ V = (9/2)x^{1/3}`, each `T(v)` bounded by
`MPc.b2v` — `eq:asparto` at `(x/v, q_v, D = U)` plus `eq:keks` (`|δ| ≤ 1/2c₂`) or `eq:kallervo2`
(`ε = 0.07`, `Q₀ = Q/v`). This file bounds each of those three expressions, for one `v`, by an
explicit majorant in which `v` enters only through simple shapes (`v`, `1/v`, `min(K/v, 2U)`), so
that the sum over `v` (`I2Sum.lean`) needs nothing but Chebyshev's `ψ(n) ≤ 1.1096 n + 1150000`.

With `U = x^{2/3}/(9√(δ₀q))`, `s = √(δ₀q)`, `c₊ = 1 + |η₂'|₁/(2s)` (`c₁(x/v, U) ≤ c₊` for
`v ≤ V`, since `UV/x = 1/(2s)`):

* `eq:keks` ≤ `3.5743(1 + |η'|₁Uv/(2x))U + 0.8219c₊U + k_q·q` (`keks_v`), where the
  `log⁺(U/(c₂x/(vq_v)))` term is cut by `t log⁺(B/t) ≤ B/e`, and `max(1, log(…)) = 1`.
* `eq:kallervo2` ≤ `3.5743(1 + |η'|₁Uv/(2x))U + 3.8246√c₊·m(1.7721 + log⁺(2U/X)/2) +
  2c₊(x/v)^{…}…` (`kall_v`), `X = (x/v)/(|δ|q_v)`, `m = min(⌊X⌋ + 1, 2U)`;
  then `m(1.7721 + log⁺(2U/X)/2) ≤ 1.7721 min(X, 2U) + 0.36788√(2U min(X, 2U)) + 1.7721 +
  log⁺(z)/2` (`phi_le`), `z = |δ|q/s`, from `log y ≤ (2/e)√y`.
* `eq:asparto` ≤ the `μ`-sum part plus `2.3433 (v/x)(U² + 2U + q)` (`asp_v`).
-/

namespace Principia.Common.TernaryGoldbach.I2A

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA Principia.Common.TernaryGoldbach.MPI1

/-! ## (0) Definitions and constants -/

/-- `s = √(δ₀q)`. -/
noncomputable def sq (δ : ℝ) (q : ℕ) : ℝ := Real.sqrt (OC.dz δ * q)

/-- `c₊ = 1 + |η₂'|₁/(2s)`. -/
noncomputable def cP (δ : ℝ) (q : ℕ) : ℝ := 1 + eta1 / (2 * sq δ q)

/-- The `q`-coefficient of the `eq:keks` majorant. -/
noncomputable def kq (δ : ℝ) (q : ℕ) (U : ℝ) : ℝ :=
  1.78715 * Real.sqrt (cP δ q) * Real.log (2 * U) + 3.5302 + 6.1908 * Real.sqrt (cP δ q) +
    2.2342 * cP δ q + 19.663

/-- `π > 3.141592`, `√c₀ ≤ 5.61436`: `2√c₀/π ≤ 3.5743`. -/
theorem two_sqrt_c0 : 2 * Real.sqrt c0 / Real.pi ≤ 3.5743 := by
  have p1 := Real.pi_gt_d6
  obtain ⟨-, h⟩ := sqrt_c0
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `√c ≤ (1 + c)/2`. -/
theorem sqrt_le_half (c : ℝ) (hc : 0 ≤ c) : Real.sqrt c ≤ (1 + c) / 2 := by
  have h := Real.sq_sqrt hc
  nlinarith [sq_nonneg (Real.sqrt c - 1)]

/-- **`2√(c₀c)/π ≤ 3.5743√c`.** -/
theorem coef_sqrt (c : ℝ) :
    2 * Real.sqrt (c0 * c) / Real.pi ≤ 3.5743 * Real.sqrt c := by
  rw [Real.sqrt_mul (by unfold c0; norm_num)]
  have e : 2 * (Real.sqrt c0 * Real.sqrt c) / Real.pi =
      2 * Real.sqrt c0 / Real.pi * Real.sqrt c := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right two_sqrt_c0 (Real.sqrt_nonneg c)

/-- **`t · log⁺(B/t) ≤ B/e`** (`t log(B/t)` peaks at `t = B/e`). -/
theorem t_logp_le (t B : ℝ) (ht : 0 < t) (hB : 0 ≤ B) : t * logp (B / t) ≤ 0.36788 * B := by
  unfold logp
  rcases eq_or_lt_of_le hB with h0 | hB0
  · rw [← h0, zero_div, Real.log_zero, max_self, mul_zero]
    linarith
  · rcases le_total (Real.log (B / t)) 0 with h | h
    · rw [max_eq_right h, mul_zero]; positivity
    · rw [max_eq_left h]
      have := log_le_div_e (B / t) (div_pos hB0 ht)
      have e : t * (0.36788 * (B / t)) = 0.36788 * B := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left this ht.le]

/-- **`log y ≤ (2/e)√y`.** -/
theorem log_le_sqrt (y : ℝ) (hy : 0 < y) : Real.log y ≤ 0.73576 * Real.sqrt y := by
  have h := log_le_div_e (Real.sqrt y) (Real.sqrt_pos.mpr hy)
  rw [Real.log_sqrt hy.le] at h
  linarith

/-! ## (1) Geometry at one `v` -/

/-- `1 ≤ q_v ≤ q`. -/
theorem qv_bounds (q v : ℕ) (hq : 1 ≤ q) (hv : 1 ≤ v) : 1 ≤ qv q v ∧ qv q v ≤ q := by
  have hg0 : 0 < Nat.gcd v q := Nat.gcd_pos_of_pos_left q hv
  have hgq : Nat.gcd v q ∣ q := Nat.gcd_dvd_right v q
  refine ⟨?_, Nat.div_le_self q _⟩
  unfold qv
  exact Nat.div_pos (Nat.le_of_dvd (by omega) hgq) hg0

/-- **`Uv/x ≤ 1/(2s)`** for `v ≤ V` (`UV/x = 1/(2s)`, `MPII.xUV`). -/
theorem uv_le (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) (v : ℝ)
    (hvV : v ≤ vA Y) : uA Y δ q * v / Y ≤ 1 / (2 * sq δ q) := by
  have hU := uA_pos Y δ q hY0 hq
  have hx := MPII.xUV Y δ q hY0 hq
  have hV0 : 0 < vA Y := by unfold vA; have := Real.rpow_pos_of_pos hY0 ((1 : ℝ) / 3); positivity
  have hs : 0 < sq δ q := by
    unfold sq
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact Real.sqrt_pos.mpr (by nlinarith [dz_ge δ])
  have e : 1 / (2 * sq δ q) = uA Y δ q * vA Y / Y := by
    unfold sq
    rw [← hx]
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hY0.le
  exact mul_le_mul_of_nonneg_left hvV hU.le

/-- `c₁(x/v, U) = 1 + |η'|₁Uv/x`, and `1 ≤ c₁ ≤ c₊` for `v ≤ V`. -/
theorem c1_v (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) (v : ℝ) (hv : 0 < v)
    (hvV : v ≤ vA Y) :
    c1 (Y / v) (uA Y δ q) = 1 + eta1 * (uA Y δ q * v / Y) ∧ 1 ≤ c1 (Y / v) (uA Y δ q) ∧
      c1 (Y / v) (uA Y δ q) ≤ cP δ q := by
  have hU := uA_pos Y δ q hY0 hq
  have he0 : 0 < eta1 := by unfold eta1; have := Real.log_two_gt_d9; linarith
  have e : c1 (Y / v) (uA Y δ q) = 1 + eta1 * (uA Y δ q * v / Y) := by
    unfold c1
    field_simp
  have h := uv_le Y δ q hY0 hq v hvV
  refine ⟨e, ?_, ?_⟩
  · rw [e]; have : 0 ≤ uA Y δ q * v / Y := by positivity
    nlinarith
  · rw [e]
    unfold cP
    have : eta1 * (uA Y δ q * v / Y) ≤ eta1 * (1 / (2 * sq δ q)) :=
      mul_le_mul_of_nonneg_left h he0.le
    have e2 : eta1 * (1 / (2 * sq δ q)) = eta1 / (2 * sq δ q) := by ring
    linarith

/-- `s ≥ √2`, `s ≤ u`, `c₊ ≤ 2.9606`, `√c₊ ≤ 1.7207`, `c₊ ≥ 1`. -/
theorem s_facts (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    1.41421 ≤ sq δ q ∧ sq δ q ≤ Y ^ ((1 : ℝ) / 6) ∧ 1 ≤ cP δ q ∧ cP δ q ≤ 2.9606 ∧
      Real.sqrt (cP δ q) ≤ 1.7207 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := dz_ge δ
  obtain ⟨-, hsu⟩ := sqrt_dq Y δ q hY hq hdq hy
  have hs2 : 1.41421 ≤ sq δ q := by
    unfold sq
    rw [Real.le_sqrt (by norm_num) (by nlinarith)]
    nlinarith
  obtain ⟨-, he⟩ := eta1_bounds
  have he0 : 0 < eta1 := by unfold eta1; have := Real.log_two_gt_d9; linarith
  have hc1 : 1 ≤ cP δ q := by
    unfold cP
    have : 0 ≤ eta1 / (2 * sq δ q) := by positivity
    linarith
  have hc2 : cP δ q ≤ 2.9606 := by
    unfold cP
    have : eta1 / (2 * sq δ q) ≤ 1.9606 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  refine ⟨hs2, hsu, hc1, hc2, ?_⟩
  rw [Real.sqrt_le_left (by norm_num)]
  linarith

/-! ## (2) The five terms of `eq:keks`, abstractly -/

/-- **(k1)** `2√(c₀c)/π·U ≤ 3.5743(1 + a/2)U` for `c = 1 + a`. -/
theorem kk1 (c U a : ℝ) (hc : 0 ≤ c) (hca : c = 1 + a) (hU : 0 ≤ U) :
    2 * Real.sqrt (c0 * c) / Real.pi * U ≤ 3.5743 * (1 + a / 2) * U := by
  have h := coef_sqrt c
  have h2 := sqrt_le_half c hc
  have h3 : Real.sqrt c ≤ 1 + a / 2 := by linarith
  have h4 : 2 * Real.sqrt (c0 * c) / Real.pi ≤ 3.5743 * (1 + a / 2) := by nlinarith
  exact mul_le_mul_of_nonneg_right h4 hU

/-- **(k2)** `(3c/2)·t·log⁺(U/(c₂t)) ≤ 0.8219·c₊·U`. -/
theorem kk2 (c U t cp : ℝ) (ht : 0 < t) (hU : 0 ≤ U) (hc : 1 ≤ c) (hcp : c ≤ cp) :
    3 * c / 2 * t * logp (U / (c2 * t)) ≤ 0.8219 * cp * U := by
  obtain ⟨hc2a, -⟩ := c2_bounds
  have e : U / (c2 * t) = (U / c2) / t := by rw [div_div, mul_comm]
  rw [e]
  have h := t_logp_le t (U / c2) ht (div_nonneg hU (by linarith))
  have hUc : U / c2 ≤ U / 0.6714 := div_le_div_of_nonneg_left hU (by norm_num) hc2a
  have h3 : 0 ≤ 3 * c / 2 := by linarith
  have h5 : t * logp ((U / c2) / t) ≤ 0.36788 * (U / 0.6714) := h.trans (by nlinarith)
  calc 3 * c / 2 * t * logp ((U / c2) / t) = 3 * c / 2 * (t * logp ((U / c2) / t)) := by ring
    _ ≤ 3 * c / 2 * (0.36788 * (U / 0.6714)) := mul_le_mul_of_nonneg_left h5 h3
    _ ≤ 0.8219 * cp * U := by
        have e2 : 3 * c / 2 * (0.36788 * (U / 0.6714)) = c * U * (3 * 0.36788 / (2 * 0.6714)) := by
          ring
        rw [e2]
        have hcU : c * U ≤ cp * U := mul_le_mul_of_nonneg_right hcp hU
        have hk : (3 * 0.36788 / (2 * 0.6714) : ℝ) ≤ 0.8219 := by norm_num
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c) hU]

/-- **(k3)** `√(c₀c)/π·n·log⁺(U/(n/2)) ≤ 1.78715√c₊·log(2U)·q` for `1 ≤ n ≤ q`, `U ≥ 1`. -/
theorem kk3 (c U n q cp : ℝ) (hn1 : 1 ≤ n) (hnq : n ≤ q) (hU1 : 1 ≤ U) (hcp : c ≤ cp) :
    Real.sqrt (c0 * c) / Real.pi * n * logp (U / (n / 2)) ≤
      1.78715 * Real.sqrt cp * Real.log (2 * U) * q := by
  have hl2U : 0 ≤ Real.log (2 * U) := Real.log_nonneg (by linarith)
  have hlp : logp (U / (n / 2)) ≤ Real.log (2 * U) := by
    unfold logp
    apply max_le _ hl2U
    have hpos : 0 < U / (n / 2) := div_pos (by linarith) (by linarith)
    apply Real.log_le_log hpos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlp0 : 0 ≤ logp (U / (n / 2)) := le_max_right _ _
  have h := coef_sqrt c
  have hsc : Real.sqrt c ≤ Real.sqrt cp := Real.sqrt_le_sqrt hcp
  have h' : Real.sqrt (c0 * c) / Real.pi ≤ 1.78715 * Real.sqrt cp := by
    have e : Real.sqrt (c0 * c) / Real.pi = (2 * Real.sqrt (c0 * c) / Real.pi) / 2 := by ring
    rw [e]
    nlinarith
  have h0 : 0 ≤ Real.sqrt (c0 * c) / Real.pi := by have := Real.pi_pos; positivity
  calc Real.sqrt (c0 * c) / Real.pi * n * logp (U / (n / 2))
      ≤ 1.78715 * Real.sqrt cp * q * Real.log (2 * U) :=
        mul_le_mul (mul_le_mul h' hnq (by linarith) (by positivity)) hlp hlp0
          (mul_nonneg (by positivity) (by linarith))
    _ = 1.78715 * Real.sqrt cp * Real.log (2 * U) * q := by ring

/-- **(k4)** `2|η'|₁/π·n·max(1, log a) ≤ 3.5302 q` when `0 ≤ a ≤ 2`, `n ≤ q`. -/
theorem kk4 (n q a : ℝ) (hn : 0 ≤ n) (hnq : n ≤ q) (ha0 : 0 ≤ a) (ha : a ≤ 2) :
    2 * eta1 / Real.pi * n * max 1 (Real.log a) ≤ 3.5302 * q := by
  have hmax : max 1 (Real.log a) = 1 := by
    apply max_eq_left
    rcases eq_or_lt_of_le ha0 with h0 | h0
    · rw [← h0, Real.log_zero]; norm_num
    · have := Real.log_le_sub_one_of_pos h0
      linarith
  rw [hmax, mul_one]
  obtain ⟨-, he1b⟩ := eta1_bounds
  have p1 := Real.pi_gt_d6
  have he0 : 0 < eta1 := by unfold eta1; have := Real.log_two_gt_d9; linarith
  have h1 : 2 * eta1 / Real.pi ≤ 3.5302 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h0 : 0 ≤ 2 * eta1 / Real.pi := by positivity
  nlinarith

/-- **(k5)** the remaining `q`-coefficient of `eq:keks`. -/
theorem kk5 (c n q cp : ℝ) (hn : 0 ≤ n) (hnq : n ≤ q) (hc : 0 ≤ c) (hcp : c ≤ cp) :
    (2 * Real.sqrt (3 * c0 * c) / Real.pi + 3 * c / (2 * c2) +
        55 * c0 * c2 / (6 * Real.pi ^ 2)) * n ≤
      (6.1908 * Real.sqrt cp + 2.2342 * cp + 19.663) * q := by
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have p1 := Real.pi_gt_d6
  have hsc : Real.sqrt c ≤ Real.sqrt cp := Real.sqrt_le_sqrt hcp
  have hsc0 := Real.sqrt_nonneg c
  have h1 : 2 * Real.sqrt (3 * c0 * c) / Real.pi ≤ 6.1908 * Real.sqrt cp := by
    rw [Real.sqrt_mul (by unfold c0; norm_num)]
    have hs3 : Real.sqrt (3 * c0) ≤ 9.72436 := by
      rw [Real.sqrt_le_left (by norm_num)]; unfold c0; norm_num
    rw [div_le_iff₀ (by linarith)]
    have := Real.sqrt_nonneg (3 * c0)
    nlinarith [mul_le_mul hs3 hsc hsc0 (by norm_num)]
  have h2 : 3 * c / (2 * c2) ≤ 2.2342 * cp := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 55 * c0 * c2 / (6 * Real.pi ^ 2) ≤ 19.663 := by
    obtain ⟨hp1, -⟩ := pi_sq_bounds
    rw [div_le_iff₀ (by positivity)]; unfold c0; nlinarith
  have hcp0 : 0 ≤ 6.1908 * Real.sqrt cp + 2.2342 * cp + 19.663 := by
    have := Real.sqrt_nonneg cp; nlinarith
  calc (2 * Real.sqrt (3 * c0 * c) / Real.pi + 3 * c / (2 * c2) +
        55 * c0 * c2 / (6 * Real.pi ^ 2)) * n
      ≤ (6.1908 * Real.sqrt cp + 2.2342 * cp + 19.663) * n :=
        mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ (6.1908 * Real.sqrt cp + 2.2342 * cp + 19.663) * q :=
        mul_le_mul_of_nonneg_left hnq hcp0

/-- The argument of `max(1, log ·)` in `eq:keks` at `(x/v, q_v)` is at most `2`. -/
theorem keks_arg (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (v n : ℝ) (hv0 : 0 < v) (hvV : v ≤ vA Y) (hn : 0 ≤ n) (hnq : n ≤ q) :
    0 ≤ c0 * Real.exp 3 * n ^ 2 / (4 * Real.pi * eta1 * (Y / v)) ∧
      c0 * Real.exp 3 * n ^ 2 / (4 * Real.pi * eta1 * (Y / v)) ≤ 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨-, he3, -⟩ := e_facts
  obtain ⟨he1a, -⟩ := eta1_bounds
  have p1 := Real.pi_gt_d6
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hvV' : v ≤ 9 / 2 * u ^ 2 := by unfold vA at hvV; rw [e13] at hvV; exact hvV
  have hy' : (q : ℝ) ≤ u ^ 2 / 6 := by rw [e13] at hy; exact hy
  have hn2 : n ^ 2 ≤ (u ^ 2 / 6) ^ 2 := pow_le_pow_left₀ hn (hnq.trans hy') 2
  have hx0 : 0 < Y / v := div_pos hY0 hv0
  have hden : 0 < 4 * Real.pi * eta1 * (Y / v) := by
    have : 0 < eta1 := by linarith
    have := Real.pi_pos
    positivity
  refine ⟨div_nonneg (by unfold c0; positivity) hden.le, ?_⟩
  rw [div_le_iff₀ hden]
  have hA : c0 * Real.exp 3 * n ^ 2 ≤ 31.521 * 20.1 * (u ^ 2 / 6) ^ 2 := by
    unfold c0
    exact mul_le_mul (mul_le_mul_of_nonneg_left he3 (by norm_num)) hn2 (sq_nonneg _)
      (by norm_num)
  have hB : 69 * (Y / v) ≤ 4 * Real.pi * eta1 * (Y / v) := by
    apply mul_le_mul_of_nonneg_right _ hx0.le; nlinarith
  have hC : 2 * u ^ 4 ≤ 9 * (Y / v) := by
    rw [mul_div_assoc', le_div_iff₀ hv0, eY]
    have h4 : 0 < u ^ 4 := by positivity
    nlinarith
  have h4 : 0 < u ^ 4 := by positivity
  linarith

/-! ## (3) `eq:keks` at one `v` -/

/-- **`eq:keks` at `(x/v, q_v, U)`, bounded.** -/
theorem keks_v (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (v : ℕ) (hv1 : 1 ≤ v) (hvV : (v : ℝ) ≤ vA Y) :
    keks (Y / v) (qv q v) (uA Y δ q) ≤
      3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q + 0.8219 * cP δ q * uA Y δ q +
        kq δ q (uA Y δ q) * q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  have hU := uA_pos Y δ q hY0 hq
  have hU1 := uA_ge_one Y δ q hY hq hdq hy
  obtain ⟨hn1, hnq⟩ := qv_bounds q v hq hv1
  have hnR : (1 : ℝ) ≤ (qv q v : ℕ) := by exact_mod_cast hn1
  have hnqR : ((qv q v : ℕ) : ℝ) ≤ q := by exact_mod_cast hnq
  obtain ⟨hce, hc1, hcP⟩ := c1_v Y δ q hY0 hq v hv0 hvV
  have ht : 0 < Y / v / ((qv q v : ℕ) : ℝ) := by positivity
  have e2 : c2 * (Y / v) / ((qv q v : ℕ) : ℝ) = c2 * (Y / v / ((qv q v : ℕ) : ℝ)) := by ring
  have t1 := kk1 _ (uA Y δ q) _ (by linarith) hce hU.le
  have t2 := kk2 _ (uA Y δ q) _ (cP δ q) ht hU.le hc1 hcP
  have t3 := kk3 _ (uA Y δ q) _ (q : ℝ) (cP δ q) hnR hnqR hU1 hcP
  obtain ⟨ha0, ha2⟩ := keks_arg Y q hY hy v _ hv0 hvV (by linarith) hnqR
  have t4 := kk4 _ (q : ℝ) _ (by linarith) hnqR ha0 ha2
  have t5 := kk5 _ _ (q : ℝ) (cP δ q) (by linarith) hnqR (by linarith) hcP
  unfold keks kq
  rw [e2]
  linarith [t1, t2, t3, t4, t5]

/-! ## (4) `eq:kallervo2` at one `v` -/

/-- `log⁺ z`, `z = |δ|q/s`. -/
noncomputable def lz (δ : ℝ) (q : ℕ) : ℝ := logp (|δ| * q / sq δ q)

/-- **(l1)** the `2√(c₀c₁)/π` line of `eq:kallervo2` at `ε = 0.07`. -/
theorem kl1 (c U a cp m L : ℝ) (hc : 0 ≤ c) (hca : c = 1 + a) (hcp : c ≤ cp) (hU : 0 ≤ U)
    (hm : 0 ≤ m) (hL : 0 ≤ L) :
    2 * Real.sqrt (c0 * c) / Real.pi *
        (U + (1 + 0.07) * m * (Real.sqrt (3 + 2 * 0.07) + L / 2)) ≤
      3.5743 * (1 + a / 2) * U + 3.8246 * Real.sqrt cp * (m * (1.7721 + L / 2)) := by
  have h1 := kk1 c U a hc hca hU
  have h := coef_sqrt c
  have hsc : Real.sqrt c ≤ Real.sqrt cp := Real.sqrt_le_sqrt hcp
  have hs : Real.sqrt (3 + 2 * 0.07) ≤ 1.7721 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hmL : 0 ≤ m * (Real.sqrt (3 + 2 * 0.07) + L / 2) := by positivity
  have hmL' : m * (Real.sqrt (3 + 2 * 0.07) + L / 2) ≤ m * (1.7721 + L / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  have hk : 2 * Real.sqrt (c0 * c) / Real.pi * (1 + 0.07) ≤ 3.8246 * Real.sqrt cp := by
    have := Real.sqrt_nonneg c
    nlinarith
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c) / Real.pi := by have := Real.pi_pos; positivity
  have e : 2 * Real.sqrt (c0 * c) / Real.pi *
      (U + (1 + 0.07) * m * (Real.sqrt (3 + 2 * 0.07) + L / 2)) =
      2 * Real.sqrt (c0 * c) / Real.pi * U +
        2 * Real.sqrt (c0 * c) / Real.pi * (1 + 0.07) *
          (m * (Real.sqrt (3 + 2 * 0.07) + L / 2)) := by ring
  rw [e]
  have h2 : 2 * Real.sqrt (c0 * c) / Real.pi * (1 + 0.07) *
      (m * (Real.sqrt (3 + 2 * 0.07) + L / 2)) ≤ 3.8246 * Real.sqrt cp * (m * (1.7721 + L / 2)) :=
    mul_le_mul hk hmL' hmL (by positivity)
  linarith

/-- **(l2)** the `(3/2)c₁(2 + ((1+ε)/ε) log⁺)` line, with `x/Q₀ = (4/3)u²`. -/
theorem kl2 (c cp L Lz w : ℝ) (hc : 0 ≤ c) (hcp : c ≤ cp) (hL : 0 ≤ L) (hLz : L ≤ Lz)
    (hw : 0 ≤ w) :
    3 / 2 * c * (2 + (1 + 0.07) / 0.07 * L) * (4 / 3 * w) ≤ 2 * cp * w * (2 + 15.2858 * Lz) := by
  have hk : (1 + 0.07) / 0.07 * L ≤ 15.2858 * Lz := by
    have : (1 + 0.07 : ℝ) / 0.07 ≤ 15.2858 := by norm_num
    nlinarith
  have h0 : 0 ≤ 2 + (1 + 0.07) / 0.07 * L := by positivity
  have e : 3 / 2 * c * (2 + (1 + 0.07) / 0.07 * L) * (4 / 3 * w) =
      2 * c * w * (2 + (1 + 0.07) / 0.07 * L) := by ring
  rw [e]
  have hcw : 2 * c * w ≤ 2 * cp * w := by nlinarith
  calc 2 * c * w * (2 + (1 + 0.07) / 0.07 * L) ≤ 2 * cp * w * (2 + (1 + 0.07) / 0.07 * L) :=
        mul_le_mul_of_nonneg_right hcw h0
    _ ≤ 2 * cp * w * (2 + 15.2858 * Lz) :=
        mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)

/-- **(l3)** `35c₀c₂/(3π²)·n ≤ 25.03 q`. -/
theorem kl3 (n q : ℝ) (hn : 0 ≤ n) (hnq : n ≤ q) :
    35 * c0 * c2 / (3 * Real.pi ^ 2) * n ≤ 25.03 * q := by
  obtain ⟨-, hc2b⟩ := c2_bounds
  obtain ⟨hc2a, -⟩ := c2_bounds
  obtain ⟨hp1, -⟩ := pi_sq_bounds
  have h : 35 * c0 * c2 / (3 * Real.pi ^ 2) ≤ 25.03 := by
    rw [div_le_iff₀ (by positivity)]; unfold c0; nlinarith
  have h0 : 0 ≤ 35 * c0 * c2 / (3 * Real.pi ^ 2) := by
    unfold c0; have : 0 < c2 := by linarith
    positivity
  nlinarith

/-- `x/Q₀ = (Y/v)/((3/4)Y^{2/3}/v) = (4/3)Y^{1/3}`. -/
theorem xQ_eq (Y v : ℝ) (hY0 : 0 < Y) (hv : 0 < v) :
    Y / v / (3 / 4 * Y ^ ((2 : ℝ) / 3) / v) = 4 / 3 * Y ^ ((1 : ℝ) / 3) := by
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu : 0 < Y ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hY0 _
  rw [e23, e13]
  nth_rw 1 [eY]
  field_simp

/-- **`2U/X ≤ z`**, `X = (x/v)/(|δ|q_v)`, `z = |δ|q/s`. -/
theorem twoU_X_le (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) (v n : ℝ) (hv : 0 < v)
    (hvV : v ≤ vA Y) (hn : 0 < n) (hnq : n ≤ q) (hδ : 0 < |δ|) :
    2 * uA Y δ q / (Y / v / (|δ| * n)) ≤ |δ| * q / sq δ q := by
  have hU := uA_pos Y δ q hY0 hq
  have h := uv_le Y δ q hY0 hq v hvV
  have hs : 0 < sq δ q := by
    unfold sq
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact Real.sqrt_pos.mpr (by nlinarith [dz_ge δ])
  have e : 2 * uA Y δ q / (Y / v / (|δ| * n)) = 2 * (uA Y δ q * v / Y) * (|δ| * n) := by
    field_simp
  rw [e]
  have e2 : |δ| * q / sq δ q = 2 * (1 / (2 * sq δ q)) * (|δ| * q) := by field_simp
  rw [e2]
  apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hnq hδ.le) (by positivity)
    (by positivity)

/-- **`eq:kallervo2` at `(x/v, q_v, U, Q/v, 0.07)`, bounded.** -/
theorem kall_v (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) (hδ : 0 < |δ|) (v : ℕ)
    (hv1 : 1 ≤ v) (hvV : (v : ℝ) ≤ vA Y) :
    kallervo2 (Y / v) δ (qv q v) (uA Y δ q) (3 / 4 * Y ^ ((2 : ℝ) / 3) / v) 0.07 ≤
      3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q +
        3.8246 * Real.sqrt (cP δ q) *
          (min ((⌊Y / v / (|δ| * ((qv q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * uA Y δ q) *
            (1.7721 + logp (2 * uA Y δ q / (Y / v / (|δ| * ((qv q v : ℕ) : ℝ)))) / 2)) +
        2 * cP δ q * Y ^ ((1 : ℝ) / 3) * (2 + 15.2858 * lz δ q) + 25.03 * q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  have hU := uA_pos Y δ q hY0 hq
  obtain ⟨hn1, hnq⟩ := qv_bounds q v hq hv1
  have hnR : (1 : ℝ) ≤ (qv q v : ℕ) := by exact_mod_cast hn1
  have hnqR : ((qv q v : ℕ) : ℝ) ≤ q := by exact_mod_cast hnq
  obtain ⟨hce, hc1, hcP⟩ := c1_v Y δ q hY0 hq v hv0 hvV
  have hX : 0 < Y / v / (|δ| * ((qv q v : ℕ) : ℝ)) := by positivity
  have hm0 : 0 ≤ min ((⌊Y / v / (|δ| * ((qv q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * uA Y δ q) :=
    le_min (by positivity) (by linarith)
  have hL0 : 0 ≤ logp (2 * uA Y δ q / (Y / v / (|δ| * ((qv q v : ℕ) : ℝ)))) := le_max_right _ _
  have hLz : logp (2 * uA Y δ q / (Y / v / (|δ| * ((qv q v : ℕ) : ℝ)))) ≤ lz δ q := by
    unfold lz logp
    apply max_le_max_right
    apply Real.log_le_log (by positivity)
    exact twoU_X_le Y δ q hY0 hq v _ hv0 hvV (by linarith) hnqR hδ
  have hw : 0 ≤ Y ^ ((1 : ℝ) / 3) := (Real.rpow_pos_of_pos hY0 _).le
  have t1 := kl1 _ (uA Y δ q) _ (cP δ q) _ _ (by linarith) hce hcP hU.le hm0 hL0
  have t2 := kl2 _ (cP δ q) _ (lz δ q) _ (by linarith) hcP hL0 hLz hw
  have t3 := kl3 _ (q : ℝ) (by linarith) hnqR
  unfold kallervo2
  rw [xQ_eq Y v hY0 hv0]
  linarith [t1, t2, t3]

/-! ## (5) The `m(1.7721 + log⁺/2)` factor -/

/-- **`m(c + log⁺(2U/X)/2) ≤ c·min(X,2U) + 0.36788√(2U min(X,2U)) + c + L/2`**, `m =
min(⌊X⌋ + 1, 2U)`, from `X log(2U/X)/2 ≤ (1/e)√(2UX)`. -/
theorem phi_le (X U Lz : ℝ) (hX : 0 < X) (hU : 0 < U)
    (hLz : logp (2 * U / X) ≤ Lz) :
    min ((⌊X⌋₊ : ℝ) + 1) (2 * U) * (1.7721 + logp (2 * U / X) / 2) ≤
      1.7721 * min X (2 * U) + 0.36788 * Real.sqrt (2 * U * min X (2 * U)) + 1.7721 + Lz / 2 := by
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX.le
  have hL0 : 0 ≤ logp (2 * U / X) := le_max_right _ _
  have hsq0 := Real.sqrt_nonneg (2 * U * min X (2 * U))
  rcases le_total (2 * U) X with h | h
  · -- `X ≥ 2U`: the `log⁺` vanishes
    have hl : logp (2 * U / X) = 0 := by
      unfold logp
      apply max_eq_right
      exact Real.log_nonpos (by positivity) (by rw [div_le_one hX]; exact h)
    rw [hl, min_eq_right h, zero_div, add_zero]
    have hm : min ((⌊X⌋₊ : ℝ) + 1) (2 * U) ≤ 2 * U := min_le_right _ _
    have hsq1 := Real.sqrt_nonneg (2 * U * (2 * U))
    have hLz0 : 0 ≤ Lz := hL0.trans hLz
    nlinarith
  · -- `X ≤ 2U`
    rw [min_eq_left h]
    have hm : min ((⌊X⌋₊ : ℝ) + 1) (2 * U) ≤ X + 1 := (min_le_left _ _).trans (by linarith)
    have hm0 : 0 ≤ min ((⌊X⌋₊ : ℝ) + 1) (2 * U) := le_min (by positivity) (by linarith)
    have hlog : logp (2 * U / X) = Real.log (2 * U / X) := by
      unfold logp
      exact max_eq_left (Real.log_nonneg (by rw [le_div_iff₀ hX]; linarith))
    have hls := log_le_sqrt (2 * U / X) (by positivity)
    have hsqX : X * Real.sqrt (2 * U / X) = Real.sqrt (2 * U * X) := by
      rw [show 2 * U * X = (2 * U / X) * X ^ 2 by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hX.le, mul_comm]
    have hXl : X * logp (2 * U / X) / 2 ≤ 0.36788 * Real.sqrt (2 * U * X) := by
      rw [hlog, ← hsqX]
      nlinarith
    calc min ((⌊X⌋₊ : ℝ) + 1) (2 * U) * (1.7721 + logp (2 * U / X) / 2)
        ≤ (X + 1) * (1.7721 + logp (2 * U / X) / 2) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
      _ = 1.7721 * X + X * logp (2 * U / X) / 2 + 1.7721 + logp (2 * U / X) / 2 := by ring
      _ ≤ 1.7721 * X + 0.36788 * Real.sqrt (2 * U * X) + 1.7721 + Lz / 2 := by linarith

/-! ## (6) `eq:asparto` at one `v` -/

/-- **`eq:asparto` at `(x/v, q_v, U)`**: the `μ`-sum term plus `≤ 2.3433(v/x)(U² + 2U + q)`. -/
theorem asp_v (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) (v : ℕ) (hv1 : 1 ≤ v) (s : ℝ) :
    asparto (Y / v) δ (qv q v) (uA Y δ q) s ≤
      Y / v / (2 * ((qv q v : ℕ) : ℝ)) * capM (c0 / Real.pi ^ 2) δ * |s| +
        2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  have hU := uA_pos Y δ q hY0 hq
  obtain ⟨hn1, hnq⟩ := qv_bounds q v hq hv1
  have hnR : (1 : ℝ) ≤ (qv q v : ℕ) := by exact_mod_cast hn1
  have hnqR : ((qv q v : ℕ) : ℝ) ≤ q := by exact_mod_cast hnq
  obtain ⟨-, hp2⟩ := pi_sq_bounds
  have hk : c0 * (1 / 8 - 1 / (2 * Real.pi ^ 2)) ≤ 2.3433 := by
    have : 1 / (2 * 9.869607) ≤ 1 / (2 * Real.pi ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    unfold c0; nlinarith
  have hk0 : 0 ≤ c0 * (1 / 8 - 1 / (2 * Real.pi ^ 2)) := by
    obtain ⟨hp1, -⟩ := pi_sq_bounds
    have : 1 / (2 * Real.pi ^ 2) ≤ 1 / (2 * 9.8696) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    unfold c0; nlinarith
  set n : ℝ := ((qv q v : ℕ) : ℝ) with hn_def
  set U := uA Y δ q with hU_def
  have hpoly : n * (U / n + 1) ^ 2 ≤ U ^ 2 + 2 * U + q := by
    have e : n * (U / n + 1) ^ 2 = U ^ 2 / n + 2 * U + n := by field_simp; ring
    rw [e]
    have : U ^ 2 / n ≤ U ^ 2 := div_le_self (sq_nonneg U) hnR
    linarith
  unfold asparto
  have e : c0 * n / (Y / v) * (1 / 8 - 1 / (2 * Real.pi ^ 2)) * (U / n + 1) ^ 2 =
      c0 * (1 / 8 - 1 / (2 * Real.pi ^ 2)) * (v / Y) * (n * (U / n + 1) ^ 2) := by
    field_simp
  rw [e]
  have h1 : c0 * (1 / 8 - 1 / (2 * Real.pi ^ 2)) * (v / Y) * (n * (U / n + 1) ^ 2) ≤
      2.3433 * (v / Y) * (U ^ 2 + 2 * U + q) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hk (by positivity)) hpoly (by positivity)
      (by positivity)
  linarith

end Principia.Common.TernaryGoldbach.I2A
