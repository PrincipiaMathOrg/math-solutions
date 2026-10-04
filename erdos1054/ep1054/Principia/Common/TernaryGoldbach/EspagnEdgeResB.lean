/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeResA

set_option autoImplicit false

/-!
# Regime B of `EE.EspagnEdgeRes`: Cover B holds on `[70000, 1.2·10¹⁰)`

From `q ≥ 70000` the second and third terms of `ϖ(q)` are `< 1` (`K − log q ≤ 12.106 − 11.15`,
`t₃ ≤ 1`), so `ϖ(q) > 1` forces `ϖ = ϖ₀ > 1` and the branch of `ϖ₀` to be taken. Write
`A = c(1.36)q^τ`, `ℓ = log q`, `D = A − ℓ > 1`, `b = τ/(1 − τ)`, `E = A − ℓ/D^b`, so
`ϖ₀ = E^{1/(1−τ)}`.

**The core** (`cb_core`, pure real analysis). `ϖ₀ + ℓ ≤ Aϖ₀^τ` always (`E ≥ D`), and
`ϖ₀ + 1 + ℓ ≤ A(ϖ₀ + 1)^τ` as soon as
`(1 − τ)/E^b + ℓ/(ϖ₀ + 1)^τ ≤ ℓ/D^b`. Proof: with `x = (ϖ₀ + 1)^{1−τ}` the claim is
`x + ℓ/(ϖ₀ + 1)^τ ≤ A = E + ℓ/D^b`, and Bernoulli (`rpow_one_add_le_one_add_mul_self`) gives
`x ≤ E + (1 − τ)/E^b`. Then Cover B at `N ∈ (ϖ₀, ϖ₀ + 1]` is `EE.region_concave`.

**The condition, two ways.**
* Near the branch threshold (`D ≤ 1.25`): `E ≥ 1`, `ϖ₀ + 1 ≥ 2`, so it suffices that
  `(1 − τ) + ℓ/2^τ ≤ ℓ/1.25^b` (`hC_near`), true for `ℓ ≥ 11.15` with margin `0.13`.
* Otherwise it follows from `(E/D)^b ≥ 1 + (1 − τ)/ℓ` (`hC_of_ratio`), and `E/D = 1 + u`,
  `u = (ℓ/D)(1 − D^{−b})`. **`ℓ/D` is non-increasing and `D` non-decreasing in `ℓ`**
  (`ratio_mono`, `D_mono`), so on a cell `[L₁, L₂]` it is enough to know `A(L₁)` from below and
  `A(L₂)` from above (`cell_of`); `log(1 + u) ≥ 2u/(2 + u)` and
  `log(1 + x) ≤ x − x²/2 + x³/(1 − x)` turn the cell into one rational inequality. Eight cells,
  `[11.15, 12.5, 15, 18, 20.5, 22, 22.8, 23.1, 23.21]`, margins `11.8%, 30.9%, 35.8%, 16.5%,
  7.1%, 1.9%, 1.3%, 1.1%` (`scratchpad/er/mkB.py`). Every transcendental value is certified by
  `exp_lo`/`exp_hi` (`decide +kernel` on `ℚ`).

The edge round's float scan found Cover B failing only beyond `q ≈ 1.4997·10¹⁰`; the cell method
reaches `log q ≈ 23.31` (`q ≈ 1.33·10¹⁰`), and `1.2·10¹⁰` is where Regime L takes over.
-/

namespace Principia.Common.TernaryGoldbach.ER

open Principia.Common.TernaryGoldbach.HC (omegaE tauE cSig cRho2 varpi0 varpiE)

/-! ## (1) Two logarithm inequalities -/

/-- `log(1 + u) ≥ 2u/(2 + u)` for `u ≥ 0` (first term of the `artanh` series). -/
theorem log_one_add_ge (u : ℝ) (hu : 0 ≤ u) : 2 * u / (2 + u) ≤ Real.log (1 + u) := by
  rcases hu.eq_or_lt with h | h
  · rw [← h]
    simp
  · have hs := Real.hasSum_log_one_add_inv (inv_pos.mpr h)
    have h1 := sum_le_hasSum (Finset.range 1) (fun i _ => by positivity) hs
    rw [Finset.sum_range_one, inv_inv] at h1
    have e : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * u⁻¹ + 1)) ^ (2 * 0 + 1) =
        2 * u / (2 + u) := by
      have e1 : 2 * u⁻¹ + 1 = (2 + u) / u := by field_simp
      rw [e1]
      simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, mul_one, one_div_div]
      ring
    linarith

/-- `log(1 + x) ≤ x − x²/2 + x³/(1 − x)` for `0 ≤ x < 1`. -/
theorem log_one_add_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / (1 - x) := by
  have hax : |(-x)| < 1 := by rw [abs_neg, abs_of_nonneg hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le hax 2
  rw [abs_neg, abs_of_nonneg hx0, sub_neg_eq_add] at h
  have h' := (abs_le.mp h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h'
  norm_num at h'
  linarith

/-! ## (2) The core: Cover B at `ϖ₀` and `ϖ₀ + 1` -/

/-- **`ϖ₀ + ℓ ≤ Aϖ₀^τ`, and `ϖ₀ + 1 + ℓ ≤ A(ϖ₀ + 1)^τ` under the condition `hC`.** -/
theorem cb_core (A l τ D E v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hl : 0 ≤ l)
    (hDd : D = A - l) (hD1 : 1 < D) (hEd : E = A - l / D ^ (τ / (1 - τ)))
    (hvd : v = E ^ (1 / (1 - τ)))
    (hC : (1 - τ) / E ^ (τ / (1 - τ)) + l / (v + 1) ^ τ ≤ l / D ^ (τ / (1 - τ))) :
    v + l ≤ A * v ^ τ ∧ v + 1 + l ≤ A * (v + 1) ^ τ := by
  have h1τ : 0 < 1 - τ := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = τ / (1 - τ) := ⟨_, rfl⟩
  rw [← hb] at hEd hC
  have hb0 : 0 < b := by rw [hb]; exact div_pos hτ0 h1τ
  have hDb : 1 ≤ D ^ b := Real.one_le_rpow hD1.le hb0.le
  have hDb0 : 0 < D ^ b := by linarith
  have hED : D ≤ E := by
    have : l / D ^ b ≤ l := div_le_self hl hDb
    rw [hEd]
    linarith
  have hE1 : 1 < E := by linarith
  have hE0 : 0 < E := by linarith
  have hEb : 0 < E ^ b := Real.rpow_pos_of_pos hE0 _
  have hDEb : D ^ b ≤ E ^ b := Real.rpow_le_rpow (by linarith) hED hb0.le
  have hA : A = E + l / D ^ b := by rw [hEd]; ring
  -- `v^τ = E^b`, `v = E·E^b`, `v^{1−τ} = E`
  have hvτ : v ^ τ = E ^ b := by
    rw [hvd, ← Real.rpow_mul hE0.le, hb]
    congr 1
    field_simp
  have hvE : v = E * E ^ b := by
    rw [hvd, show 1 / (1 - τ) = 1 + b by rw [hb]; field_simp; ring, Real.rpow_add hE0,
      Real.rpow_one]
  have hv1 : 1 ≤ v := by rw [hvd]; exact Real.one_le_rpow hE1.le (by positivity)
  have hv0 : 0 < v := by linarith
  have hv1τ : v ^ (1 - τ) = E := by
    rw [hvd, ← Real.rpow_mul hE0.le]
    rw [show 1 / (1 - τ) * (1 - τ) = 1 by field_simp, Real.rpow_one]
  constructor
  · -- `v + ℓ ≤ A·v^τ`
    rw [hvτ, hA, hvE]
    have h1 : l ≤ l / D ^ b * E ^ b := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hDb0]
      exact mul_le_mul_of_nonneg_left hDEb hl
    nlinarith
  · -- `v + 1 + ℓ ≤ A·(v + 1)^τ`
    have hR0 : 0 < v + 1 := by linarith
    have hRτ : 0 < (v + 1) ^ τ := Real.rpow_pos_of_pos hR0 _
    -- `x = (v + 1)^{1−τ} ≤ E + (1 − τ)/E^b`
    have hx : (v + 1) ^ (1 - τ) ≤ E + (1 - τ) / E ^ b := by
      have hsplit : v + 1 = v * (1 + 1 / v) := by field_simp
      have hbern := rpow_one_add_le_one_add_mul_self (s := 1 / v)
        (by have := one_div_pos.mpr hv0; linarith) h1τ.le (by linarith)
      rw [hsplit, Real.mul_rpow hv0.le (by positivity), hv1τ]
      have hvinv : E * ((1 - τ) * (1 / v)) = (1 - τ) / E ^ b := by
        rw [hvE]
        field_simp
      have := mul_le_mul_of_nonneg_left hbern hE0.le
      rw [mul_add, mul_one, hvinv] at this
      exact this
    have hRsplit : v + 1 = (v + 1) ^ (1 - τ) * (v + 1) ^ τ := by
      rw [← Real.rpow_add hR0, show 1 - τ + τ = 1 by ring, Real.rpow_one]
    have hkey : (v + 1) ^ (1 - τ) + l / (v + 1) ^ τ ≤ A := by
      rw [hA]
      linarith
    have := mul_le_mul_of_nonneg_right hkey hRτ.le
    rw [add_mul, div_mul_cancel₀ _ hRτ.ne', ← hRsplit] at this
    linarith

/-- **The condition from the ratio** `(E/D)^b ≥ 1 + (1 − τ)/ℓ` (`ϖ₀ + 1 ≥ ϖ₀`). -/
theorem hC_of_ratio (l τ D E v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hl : 0 < l) (hD1 : 1 < D)
    (hDE : D ≤ E) (hvd : v = E ^ (1 / (1 - τ)))
    (hr : 1 + (1 - τ) / l ≤ (E / D) ^ (τ / (1 - τ))) :
    (1 - τ) / E ^ (τ / (1 - τ)) + l / (v + 1) ^ τ ≤ l / D ^ (τ / (1 - τ)) := by
  have h1τ : 0 < 1 - τ := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = τ / (1 - τ) := ⟨_, rfl⟩
  rw [← hb] at hr ⊢
  have hb0 : 0 < b := by rw [hb]; exact div_pos hτ0 h1τ
  have hE0 : 0 < E := by linarith
  have hDb0 : 0 < D ^ b := Real.rpow_pos_of_pos (by linarith) _
  have hEb0 : 0 < E ^ b := Real.rpow_pos_of_pos hE0 _
  have hvτ : v ^ τ = E ^ b := by
    rw [hvd, ← Real.rpow_mul hE0.le, hb]
    congr 1
    field_simp
  have hv0 : 0 ≤ v := by rw [hvd]; exact Real.rpow_nonneg hE0.le _
  have hmono : E ^ b ≤ (v + 1) ^ τ := by
    rw [← hvτ]
    exact Real.rpow_le_rpow hv0 (by linarith) hτ0.le
  have h1 : l / (v + 1) ^ τ ≤ l / E ^ b := div_le_div_of_nonneg_left hl.le hEb0 hmono
  rw [Real.div_rpow hE0.le (by linarith)] at hr
  have h2 : (1 + (1 - τ) / l) * D ^ b ≤ E ^ b := by
    rw [le_div_iff₀ hDb0] at hr
    exact hr
  have h3 : (1 - τ) / E ^ b + l / E ^ b ≤ l / D ^ b := by
    rw [← add_div, div_le_div_iff₀ hEb0 hDb0]
    have e : (1 + (1 - τ) / l) * D ^ b * l = (1 - τ + l) * D ^ b := by field_simp; ring
    nlinarith
  linarith

/-- **The condition near the threshold**: `E ≥ 1`, `ϖ₀ ≥ 1` and `(1 − τ) + ℓ/2^τ ≤ ℓ/D^b`. -/
theorem hC_near (l τ D E v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hl : 0 ≤ l) (hE1 : 1 ≤ E)
    (hvd : v = E ^ (1 / (1 - τ)))
    (h : (1 - τ) + l / 2 ^ τ ≤ l / D ^ (τ / (1 - τ))) :
    (1 - τ) / E ^ (τ / (1 - τ)) + l / (v + 1) ^ τ ≤ l / D ^ (τ / (1 - τ)) := by
  have h1τ : 0 < 1 - τ := by linarith
  have hEb : 1 ≤ E ^ (τ / (1 - τ)) := Real.one_le_rpow hE1 (div_pos hτ0 h1τ).le
  have hv1 : 1 ≤ v := by rw [hvd]; exact Real.one_le_rpow hE1 (by positivity)
  have h1 : (1 - τ) / E ^ (τ / (1 - τ)) ≤ 1 - τ := div_le_self h1τ.le hEb
  have h2 : l / (v + 1) ^ τ ≤ l / 2 ^ τ :=
    div_le_div_of_nonneg_left hl (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) (by linarith) hτ0.le)
  linarith

/-! ## (3) The cells -/

/-- **The ratio condition from three bounds**: `D ≥ D₀ ≥ 1`, `D₀^{b₀} ≥ P ≥ 1`, `ℓ/D ≥ R₀ ≥ 0`,
`ℓ ≥ L₁`, and one rational check (`b₀ = 0.22458372/(1 − 0.22458372)`). -/
theorem ratio_of (l τ D D0 P R0 L1 : ℝ) (hτlo : 0.22458372 ≤ τ) (hτhi : τ ≤ 0.22461816)
    (hD : D0 ≤ D) (hD0 : 1 ≤ D0) (hP : P ≤ D0 ^ (0.22458372 / (1 - 0.22458372) : ℝ))
    (hP1 : 1 ≤ P) (hR : R0 ≤ l / D) (hR0 : 0 ≤ R0) (hL1 : L1 ≤ l) (hL1p : 0 < L1)
    (hx1 : (1 - 0.22458372) / L1 < 1)
    (hchk : (1 - 0.22458372) / L1 - ((1 - 0.22458372) / L1) ^ 2 / 2 +
        ((1 - 0.22458372) / L1) ^ 3 / (1 - (1 - 0.22458372) / L1) ≤
      0.22458372 / (1 - 0.22458372) * (2 * (R0 * (1 - 1 / P)) / (2 + R0 * (1 - 1 / P)))) :
    1 + (1 - τ) / l ≤ ((D + l - l / D ^ (τ / (1 - τ))) / D) ^ (τ / (1 - τ)) := by
  have hl0 : 0 < l := by linarith
  have hDp : 0 < D := by linarith
  have h1τ : 0 < 1 - τ := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = τ / (1 - τ) := ⟨_, rfl⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℝ, b0 = 0.22458372 / (1 - 0.22458372) := ⟨_, rfl⟩
  rw [← hb]
  rw [← hb0] at hP hchk
  have hbb : b0 ≤ b := by
    rw [hb, hb0, div_le_div_iff₀ (by norm_num) h1τ]
    nlinarith
  have hb00 : 0 ≤ b0 := by rw [hb0]; norm_num
  -- `D^b ≥ P`
  have hDb : P ≤ D ^ b := by
    have h1 : D0 ^ b0 ≤ D ^ b0 := Real.rpow_le_rpow (by linarith) hD hb00
    have h2 : D ^ b0 ≤ D ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) hbb
    linarith
  have hDb0 : 0 < D ^ b := lt_of_lt_of_le (by linarith) hDb
  -- `u ≥ R₀(1 − 1/P)`
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = l / D * (1 - 1 / D ^ b) := ⟨_, rfl⟩
  have hw : 1 - 1 / P ≤ 1 - 1 / D ^ b := by
    have : 1 / D ^ b ≤ 1 / P := one_div_le_one_div_of_le (by linarith) hDb
    linarith
  have hw0 : 0 ≤ 1 - 1 / P := by
    have : 1 / P ≤ 1 := by rw [div_le_one (by linarith)]; exact hP1
    linarith
  have hu0 : R0 * (1 - 1 / P) ≤ u := by rw [hu]; exact mul_le_mul hR hw hw0 (le_trans hR0 hR)
  have hu00 : 0 ≤ R0 * (1 - 1 / P) := mul_nonneg hR0 hw0
  have hED : (D + l - l / D ^ b) / D = 1 + u := by
    rw [hu]
    field_simp
    ring
  rw [hED]
  have hu' : 0 ≤ u := le_trans hu00 hu0
  have hlog1 := log_one_add_ge u hu'
  have hmono : 2 * (R0 * (1 - 1 / P)) / (2 + R0 * (1 - 1 / P)) ≤ 2 * u / (2 + u) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  -- `log(1 + (1 − τ)/ℓ)` against the cubic at `x = (1 − τ₀)/L₁`
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (1 - 0.22458372) / L1 := ⟨_, rfl⟩
  rw [← hx] at hchk hx1
  have hx0 : 0 ≤ x := by rw [hx]; exact div_nonneg (by norm_num) hL1p.le
  have hy : (1 - τ) / l ≤ x := by
    rw [hx]
    exact div_le_div₀ (by norm_num) (by linarith) hL1p hL1
  have hy0 : 0 ≤ (1 - τ) / l := div_nonneg h1τ.le hl0.le
  have hlog2 : Real.log (1 + (1 - τ) / l) ≤ x - x ^ 2 / 2 + x ^ 3 / (1 - x) :=
    le_trans (Real.log_le_log (by linarith) (by linarith)) (log_one_add_le x hx0 hx1)
  have hq0 : 0 ≤ 2 * (R0 * (1 - 1 / P)) / (2 + R0 * (1 - 1 / P)) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : b0 * (2 * (R0 * (1 - 1 / P)) / (2 + R0 * (1 - 1 / P))) ≤ b * Real.log (1 + u) :=
    mul_le_mul hbb (le_trans hmono hlog1) hq0 (by linarith)
  have hb_log : Real.log (1 + (1 - τ) / l) ≤ Real.log (1 + u) * b := by
    rw [mul_comm]
    linarith
  have hpos : 0 < 1 + u := by linarith
  rw [Real.rpow_def_of_pos hpos]
  calc 1 + (1 - τ) / l = Real.exp (Real.log (1 + (1 - τ) / l)) :=
        (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (Real.log (1 + u) * b) := Real.exp_le_exp.mpr hb_log

/-- `P ≤ D₀^{b₀}` from a certified `e^{LD} ≤ D₀` and `P ≤ e^{b₀·LD}`. -/
theorem rpow_ge_of (D0 LD P : ℝ) (hD0 : 0 < D0) (hLD : Real.exp LD ≤ D0)
    (hP : P ≤ Real.exp (0.22458372 / (1 - 0.22458372) * LD)) :
    P ≤ D0 ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
  rw [Real.rpow_def_of_pos hD0]
  have hl := log_ge_of hD0 hLD
  refine le_trans hP (Real.exp_le_exp.mpr ?_)
  have hb : (0 : ℝ) ≤ 0.22458372 / (1 - 0.22458372) := by norm_num
  nlinarith

/-- **One cell `[L₁, L₂]`**: `A(L₁) ≥ A₁`, `A(L₂) ≤ A₂`, `(A₁ − L₁)^{b₀} ≥ P`, and the rational
check, give the ratio condition for every `ℓ ∈ [L₁, L₂]` (`D_mono`, `ratio_mono`). -/
theorem cell_of (l L1 L2 A1 A2 P : ℝ) (hL1 : L1 ≤ l) (hL2 : l ≤ L2) (hL15 : 5 ≤ L1)
    (hA1 : A1 ≤ Af L1) (hA2 : Af L2 ≤ A2) (hA15 : 5 ≤ A1) (hD0 : 1 ≤ A1 - L1)
    (hP : P ≤ (A1 - L1) ^ (0.22458372 / (1 - 0.22458372) : ℝ)) (hP1 : 1 ≤ P)
    (hDh : 0 < A2 - L2) (hx1 : (1 - 0.22458372) / L1 < 1)
    (hchk : (1 - 0.22458372) / L1 - ((1 - 0.22458372) / L1) ^ 2 / 2 +
        ((1 - 0.22458372) / L1) ^ 3 / (1 - (1 - 0.22458372) / L1) ≤
      0.22458372 / (1 - 0.22458372) * (2 * (L2 / (A2 - L2) * (1 - 1 / P)) /
        (2 + L2 / (A2 - L2) * (1 - 1 / P)))) :
    1 + (1 - tauE) / l ≤ ((Af l - l + l - l / (Af l - l) ^ (tauE / (1 - tauE))) / (Af l - l)) ^
      (tauE / (1 - tauE)) := by
  obtain ⟨hτlo, hτhi⟩ := tau_bounds
  have hl0 : 0 < l := by linarith
  have hDm := D_mono L1 l hL1 (by nlinarith)
  have hD : A1 - L1 ≤ Af l - l := by linarith
  have hRm := ratio_mono l L2 hl0 hL2 (by nlinarith)
  have hDp : 0 < Af l - l := by linarith
  have hR : L2 / (A2 - L2) ≤ l / (Af l - l) := by
    rw [div_le_div_iff₀ hDh hDp]
    nlinarith
  exact ratio_of l tauE (Af l - l) (A1 - L1) P (L2 / (A2 - L2)) L1 hτlo hτhi hD hD0 hP hP1 hR
    (div_nonneg (by linarith) hDh.le) hL1 (by linarith) hx1 hchk

/-! ## (4) Regime B -/

/-- `A(L) ≤ B` from a certified upper exponential at `0.5615454((2/5)L − 3371/20500)`. -/
theorem Af_hi_of (L : ℝ) (y : ℚ) (B : ℚ) (hL : 3371 / 20500 ≤ 2 / 5 * L) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hx : 0.5615454 * (2 / 5 * L - 3371 / 20500) ≤ (8 : ℕ) * (y : ℝ))
    (h : (tayQ y 12 + remQ y 12) ^ 8 ≤ B) : Af L ≤ (B : ℝ) :=
  le_trans (Af_le L L le_rfl hL) (exp_hi _ y 12 8 B hy hy1 (by norm_num) hx h)

/-- `A(L) ≥ B` from a certified lower exponential at `0.5614593((2/5)L − 3371/20500)`. -/
theorem Af_lo_of (L : ℝ) (y : ℚ) (B : ℚ) (hL : 3371 / 20500 ≤ 2 / 5 * L) (hy : 0 ≤ y)
    (hx : (8 : ℕ) * (y : ℝ) ≤ 0.5614593 * (2 / 5 * L - 3371 / 20500))
    (h : B ≤ tayQ y 14 ^ 8) : (B : ℝ) ≤ Af L :=
  le_trans (exp_lo _ y 14 8 B hy hx h) (Af_ge L L le_rfl hL)

/-- `(A₁ − L₁)^{b₀} ≥ P` from certified `e^{LD} ≤ D₀` and `P ≤ e^{b₀LD}`. -/
theorem Dpow_of (D0 LD : ℝ) (y1 y2 : ℚ) (P D0q : ℚ) (hD0 : (D0q : ℝ) = D0) (hD0p : 0 < D0)
    (hy1 : 0 ≤ y1) (hy11 : y1 ≤ 1) (hx1 : LD ≤ (8 : ℕ) * (y1 : ℝ))
    (h1 : (tayQ y1 12 + remQ y1 12) ^ 8 ≤ D0q) (hy2 : 0 ≤ y2)
    (hx2 : (8 : ℕ) * (y2 : ℝ) ≤ 0.22458372 / (1 - 0.22458372) * LD) (h2 : P ≤ tayQ y2 14 ^ 8) :
    (P : ℝ) ≤ D0 ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
  have e1 := exp_hi LD y1 12 8 D0q hy1 hy11 (by norm_num) hx1 h1
  rw [hD0] at e1
  exact rpow_ge_of D0 LD P hD0p e1 (exp_lo _ y2 14 8 P hy2 hx2 h2)

/-! ## (5) The numeric cells -/

/-- The ratio condition at `ℓ` on the curve `D = A(ℓ) − ℓ`. -/
def RatioCond (l : ℝ) : Prop :=
  1 + (1 - tauE) / l ≤ ((Af l - l + l - l / (Af l - l) ^ (tauE / (1 - tauE))) / (Af l - l)) ^
    (tauE / (1 - tauE))

/-- `log q ∈ [11.15, 23.21]` on Regime B's range. -/
theorem logq_B (q : ℕ) (h7 : 70000 ≤ q) (hQ : (q : ℝ) < 1.2e10) :
    11.15 ≤ Real.log q ∧ Real.log q ≤ 23.21 := by
  have h7r : (70000 : ℝ) ≤ q := by exact_mod_cast h7
  have hq0 : (0 : ℝ) < q := by linarith
  constructor
  · have h := exp_hi 11.15 (223 / 320) 12 16 70000 (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    have e : ((70000 : ℚ) : ℝ) = 70000 := by norm_num
    rw [e] at h
    exact le_trans (log_ge_of (by norm_num) h) (Real.log_le_log (by norm_num) h7r)
  · have h := exp_lo 23.21 (2321 / 800) 14 8 12000000000 (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    have e : ((12000000000 : ℚ) : ℝ) = 1.2e10 := by norm_num
    rw [e] at h
    exact le_trans (Real.log_le_log hq0 hQ.le) (log_le_of (by norm_num) h)

/-- **Near the threshold**: `ℓ ≥ 11.15`, `1 ≤ D ≤ 1.25` ⟹ `(1 − τ) + ℓ/2^τ ≤ ℓ/D^b`
(`2^τ ≥ 1.16844`, `1.25^b ≤ 1.06678`). -/
theorem near_num (l D : ℝ) (hl : 11.15 ≤ l) (hD1 : 1 ≤ D) (hD : D ≤ 1.25) :
    (1 - tauE) + l / 2 ^ tauE ≤ l / D ^ (tauE / (1 - tauE)) := by
  obtain ⟨hτlo, hτhi⟩ := tau_bounds
  have h1τ : 0 < 1 - tauE := by linarith
  have hT2 : (29211 / 25000 : ℝ) ≤ 2 ^ tauE := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hl2 := Real.log_two_gt_d9
    have hm : (0.6931471803 : ℝ) * 0.22458372 ≤ Real.log 2 * tauE :=
      mul_le_mul hl2.le hτlo (by norm_num) (by linarith)
    have h := exp_lo (Real.log 2 * tauE) (2432337 / 125000000) 14 8 (29211 / 25000)
      (by norm_num) (by push_cast; linarith) (by decide +kernel)
    push_cast at h
    exact h
  have hb0 : 0 ≤ tauE / (1 - tauE) := div_nonneg (by linarith) h1τ.le
  have hb : tauE / (1 - tauE) ≤ 0.22461816 / (1 - 0.22461816) := by
    rw [div_le_div_iff₀ h1τ (by norm_num)]
    nlinarith
  have hl125 : Real.log 1.25 ≤ 0.22315 := by
    have h := exp_lo 0.22315 (4463 / 160000) 14 8 (5 / 4) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    have e : ((5 / 4 : ℚ) : ℝ) = 1.25 := by norm_num
    rw [e] at h
    exact log_le_of (by norm_num) h
  have hl1250 : 0 ≤ Real.log 1.25 := Real.log_nonneg (by norm_num)
  have hT125 : D ^ (tauE / (1 - tauE)) ≤ 53339 / 50000 := by
    have h1 : D ^ (tauE / (1 - tauE)) ≤ (1.25 : ℝ) ^ (tauE / (1 - tauE)) :=
      Real.rpow_le_rpow (by linarith) hD hb0
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1.25)] at h1
    have hm : Real.log 1.25 * (tauE / (1 - tauE)) ≤ 0.22315 * (0.22461816 / (1 - 0.22461816)) :=
      mul_le_mul hl125 hb hb0 (by norm_num)
    have h := exp_hi (Real.log 1.25 * (tauE / (1 - tauE))) (4040231 / 500000000) 12 8
      (53339 / 50000) (by norm_num) (by norm_num) (by norm_num) (by push_cast; linarith)
      (by decide +kernel)
    push_cast at h
    linarith
  have hDb : 0 < D ^ (tauE / (1 - tauE)) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : l / (53339 / 50000) ≤ l / D ^ (tauE / (1 - tauE)) :=
    div_le_div_of_nonneg_left (by linarith) hDb hT125
  have h2 : l / 2 ^ tauE ≤ l / (29211 / 25000) :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hT2
  have e : l / (53339 / 50000) - l / (29211 / 25000) = l * (50000 / 53339 - 25000 / 29211) := by
    ring
  have h3 : (11.15 : ℝ) * 0.0815 ≤ l * (50000 / 53339 - 25000 / 29211) :=
    mul_le_mul hl (by norm_num) (by norm_num) (by linarith)
  linarith

/-- **Cell `[11.15, 12.5]`**, `D > 1.25` (the threshold side is `near_num`). -/
theorem cell0 (l : ℝ) (h1 : 11.15 ≤ l) (h2 : l ≤ 12.5) (hD : 1.25 ≤ Af l - l) :
    RatioCond l := by
  obtain ⟨hτlo, hτhi⟩ := tau_bounds
  have hl0 : 0 < l := by linarith
  have hA2 : Af 12.5 ≤ (15111 / 1000 : ℝ) := by
    have h := Af_hi_of 12.5 (169711689 / 500000000) (15111 / 1000) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (26669 / 25000 : ℝ) ≤ (1.25 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of 1.25 0.22314 (11157 / 400000) (8078501 / 1000000000) (26669 / 25000) (5 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel) (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hRm := ratio_mono l 12.5 hl0 h2 (by nlinarith)
  have hDp : 0 < Af l - l := by linarith
  have hR : 12.5 / (15111 / 1000 - 12.5) ≤ l / (Af l - l) := by
    rw [div_le_div_iff₀ (by norm_num) hDp]
    nlinarith
  exact ratio_of l tauE (Af l - l) 1.25 (26669 / 25000) (12.5 / (15111 / 1000 - 12.5)) 11.15 hτlo
    hτhi hD (by norm_num) hP (by norm_num) hR (by norm_num) h1 (by norm_num) (by norm_num)
    (by norm_num)

/-- **Cell `[12.5, 15]`.** -/
theorem cell1 (l : ℝ) (h1 : 12.5 ≤ l) (h2 : l ≤ 15) : RatioCond l := by
  have hA1 : (1888 / 125 : ℝ) ≤ Af 12.5 := by
    have h := Af_lo_of 12.5 (67874267 / 200000000) (1888 / 125) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 15 ≤ (5299 / 200 : ℝ) := by
    have h := Af_hi_of 15 (409616553 / 1000000000) (5299 / 200) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (13193 / 10000 : ℝ) ≤
      (1888 / 125 - 12.5 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (1888 / 125 - 12.5) 0.957 (957 / 8000) (34646973 / 1000000000)
      (13193 / 10000) (651 / 250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 12.5 15 (1888 / 125) (5299 / 200) (13193 / 10000) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Cell `[15, 18]`.** -/
theorem cell2 (l : ℝ) (h1 : 15 ≤ l) (h2 : l ≤ 18) : RatioCond l := by
  have hA1 : (26481 / 1000 : ℝ) ≤ Af 15 := by
    have h := Af_lo_of 15 (409553747 / 1000000000) (26481 / 1000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 18 ≤ (51977 / 1000 : ℝ) := by
    have h := Af_hi_of 18 (493848363 / 1000000000) (51977 / 1000) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (5069 / 2500 : ℝ) ≤
      (26481 / 1000 - 15 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (26481 / 1000 - 15) 2.4406 (12203 / 40000) (44179417 / 500000000)
      (5069 / 2500) (11481 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 15 18 (26481 / 1000) (51977 / 1000) (5069 / 2500) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Cell `[18, 20.5]`.** -/
theorem cell3 (l : ℝ) (h1 : 18 ≤ l) (h2 : l ≤ 20.5) : RatioCond l := by
  have hA1 : (6493 / 125 : ℝ) ≤ Af 18 := by
    have h := Af_lo_of 18 (246886321 / 500000000) (6493 / 125) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 20.5 ≤ (18227 / 200 : ℝ) := by
    have h := Af_hi_of 20.5 (282020769 / 500000000) (18227 / 200) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (5551 / 2000 : ℝ) ≤
      (6493 / 125 - 18 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (6493 / 125 - 18) 3.5247 (35247 / 80000) (63803651 / 500000000)
      (5551 / 2000) (4243 / 125) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 18 20.5 (6493 / 125) (18227 / 200) (5551 / 2000) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Cell `[20.5, 22]`.** -/
theorem cell4 (l : ℝ) (h1 : 20.5 ≤ l) (h2 : l ≤ 22) : RatioCond l := by
  have hA1 : (91071 / 1000 : ℝ) ≤ Af 20.5 := by
    have h := Af_lo_of 20.5 (112791011 / 200000000) (91071 / 1000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 22 ≤ (63823 / 500 : ℝ) := by
    have h := Af_hi_of 22 (606157443 / 1000000000) (63823 / 500) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (34309 / 10000 : ℝ) ≤
      (91071 / 1000 - 20.5 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (91071 / 1000 - 20.5) 4.2566 (21283 / 40000) (30820963 / 200000000)
      (34309 / 10000) (70571 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 20.5 22 (91071 / 1000) (63823 / 500) (34309 / 10000) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Cell `[22, 22.8]`.** -/
theorem cell5 (l : ℝ) (h1 : 22 ≤ l) (h2 : l ≤ 22.8) : RatioCond l := by
  have hA1 : (2551 / 20 : ℝ) ≤ Af 22 := by
    have h := Af_lo_of 22 (303032251 / 500000000) (2551 / 20) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 22.8 ≤ (76387 / 500 : ℝ) := by
    have h := Af_hi_of 22.8 (628619259 / 1000000000) (76387 / 500) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (38551 / 10000 : ℝ) ≤
      (2551 / 20 - 22 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (2551 / 20 - 22) 4.6591 (46591 / 80000) (84338409 / 500000000)
      (38551 / 10000) (2111 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 22 22.8 (2551 / 20) (76387 / 500) (38551 / 10000) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Cell `[22.8, 23.1]`.** -/
theorem cell6 (l : ℝ) (h1 : 22.8 ≤ l) (h2 : l ≤ 23.1) : RatioCond l := by
  have hA1 : (30531 / 200 : ℝ) ≤ Af 22.8 := by
    have h := Af_lo_of 22.8 (314261437 / 500000000) (30531 / 200) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 23.1 ≤ (163423 / 1000 : ℝ) := by
    have h := Af_hi_of 23.1 (15926061 / 25000000) (163423 / 1000) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (40937 / 10000 : ℝ) ≤
      (30531 / 200 - 22.8 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (30531 / 200 - 22.8) 4.8664 (6083 / 10000) (44045463 / 250000000)
      (40937 / 10000) (25971 / 200) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 22.8 23.1 (30531 / 200) (163423 / 1000) (40937 / 10000) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Cell `[23.1, 23.21]`.** -/
theorem cell7 (l : ℝ) (h1 : 23.1 ≤ l) (h2 : l ≤ 23.21) : RatioCond l := by
  have hA1 : (81647 / 500 : ℝ) ≤ Af 23.1 := by
    have h := Af_lo_of 23.1 (159236191 / 250000000) (81647 / 500) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hA2 : Af 23.21 ≤ (167511 / 1000 : ℝ) := by
    have h := Af_hi_of 23.21 (32006547 / 50000000) (167511 / 1000) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    push_cast at h
    exact h
  have hP : (8371 / 2000 : ℝ) ≤
      (81647 / 500 - 23.1 : ℝ) ^ (0.22458372 / (1 - 0.22458372) : ℝ) := by
    have h := Dpow_of (81647 / 500 - 23.1) 4.943 (4943 / 8000) (89477529 / 500000000)
      (8371 / 2000) (70097 / 500) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    push_cast at h
    exact h
  exact cell_of l 23.1 23.21 (81647 / 500) (167511 / 1000) (8371 / 2000) h1 h2 (by norm_num) hA1
    hA2 (by norm_num) (by norm_num) hP (by norm_num) (by norm_num) (by norm_num) (by norm_num)


/-- **The ratio condition on all of `[11.15, 23.21]`** (where `D > 1.25`). -/
theorem ratio_all (l : ℝ) (h1 : 11.15 ≤ l) (h2 : l ≤ 23.21) (hD : 1.25 ≤ Af l - l) :
    RatioCond l := by
  rcases le_or_gt l 12.5 with c | c
  · exact cell0 l h1 c hD
  rcases le_or_gt l 15 with c' | c'
  · exact cell1 l c.le c'
  rcases le_or_gt l 18 with c | c
  · exact cell2 l c'.le c
  rcases le_or_gt l 20.5 with c' | c'
  · exact cell3 l c.le c'
  rcases le_or_gt l 22 with c | c
  · exact cell4 l c'.le c
  rcases le_or_gt l 22.8 with c' | c'
  · exact cell5 l c.le c'
  rcases le_or_gt l 23.1 with c | c
  · exact cell6 l c'.le c
  · exact cell7 l c.le h2

/-! ## (6) Regime B -/

/-- **Regime B, PROVED** (`70000 ≤ q < 1.2·10¹⁰`, `ϖ(q) > 1`): Cover B holds. -/
theorem regB (cer : CY.CERange) : RegB := by
  intro q h7 hQ hv1
  obtain ⟨hl1, hl2⟩ := logq_B q h7 hQ
  have h7r : (70000 : ℝ) ≤ q := by exact_mod_cast h7
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨hτlo, hτhi⟩ := tau_bounds
  have hτ0 : 0 < tauE := by linarith
  have hτ1 : tauE < 1 := by linarith
  have hK2 := Kc_hi
  -- `ϖ = ϖ₀ > 1`, and the branch of `ϖ₀` is taken
  have ht2 : Kc - Real.log q < 1 := by linarith
  have ht3 := t3_le_one cer q (by omega)
  have hvar := varpiE_eq q
  have hv0 : 1 < varpi0 q := by
    by_contra h
    push Not at h
    have : varpiE q ≤ 1 := by rw [hvar]; exact max_le h (max_le ht2.le ht3)
    linarith
  have hveq : varpiE q = varpi0 q := by
    rw [hvar]
    exact max_eq_left (le_trans (max_le ht2.le ht3) hv0.le)
  have hbr : Real.log q + 1 < cSig 1.36 * (q : ℝ) ^ tauE := by
    by_contra h
    unfold varpi0 at hv0
    rw [if_neg h] at hv0
    linarith
  have hv0eq : varpi0 q = (cSig 1.36 * (q : ℝ) ^ tauE - Real.log q /
      (cSig 1.36 * (q : ℝ) ^ tauE - Real.log q) ^ (tauE / (1 - tauE))) ^ (1 / (1 - tauE)) := by
    unfold varpi0
    rw [if_pos hbr]
  have hAf := cq_eq q hq0
  rw [hAf] at hbr hv0eq
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log q := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Af l - l := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Af l - l / D ^ (tauE / (1 - tauE)) := ⟨_, rfl⟩
  rw [← hl] at hbr hv0eq hl1 hl2
  rw [← hD] at hv0eq
  rw [← hE] at hv0eq
  have hD1 : 1 < D := by rw [hD]; linarith
  have hl0 : 0 < l := by linarith
  have hEe : E = D + l - l / D ^ (tauE / (1 - tauE)) := by rw [hE, hD]; ring
  have hDb1 : 1 ≤ D ^ (tauE / (1 - tauE)) :=
    Real.one_le_rpow hD1.le (div_pos hτ0 (by linarith)).le
  have hDE : D ≤ E := by
    have := div_le_self hl0.le hDb1
    rw [hEe]
    linarith
  -- the condition of the core
  have hC : (1 - tauE) / E ^ (tauE / (1 - tauE)) + l / (varpi0 q + 1) ^ tauE ≤
      l / D ^ (tauE / (1 - tauE)) := by
    rcases le_or_gt D 1.25 with hDs | hDs
    · exact hC_near l tauE D E (varpi0 q) hτ0 hτ1 hl0.le (by linarith) hv0eq
        (near_num l D hl1 hD1.le hDs)
    · refine hC_of_ratio l tauE D E (varpi0 q) hτ0 hτ1 hl0 hD1 hDE hv0eq ?_
      have hr := ratio_all l hl1 hl2 (by rw [← hD]; exact hDs.le)
      unfold RatioCond at hr
      rw [← hD] at hr
      rw [hEe]
      exact hr
  obtain ⟨h1, h2⟩ := cb_core (Af l) l tauE D E (varpi0 q) hτ0 hτ1 hl0.le hD hD1 hE hv0eq hC
  -- Cover B
  have hmul : ∀ R : ℝ, 0 ≤ R → cSig 1.36 * ((q : ℝ) * R) ^ tauE = Af l * R ^ tauE := by
    intro R hR
    rw [Real.mul_rpow hq0.le hR, ← mul_assoc, hAf, hl]
  have hv0' : 0 ≤ varpi0 q := by linarith
  have h1' : varpi0 q + Real.log q ≤ cSig 1.36 * ((q : ℝ) * varpi0 q) ^ tauE := by
    rw [hmul _ hv0', ← hl]
    exact h1
  have h2' : varpi0 q + 1 + Real.log q ≤ cSig 1.36 * ((q : ℝ) * (varpi0 q + 1)) ^ tauE := by
    rw [hmul _ (by linarith), ← hl]
    exact h2
  have hNe : ((EE.edgeN q : ℕ) : ℝ) = (⌊varpi0 q⌋₊ : ℝ) + 1 := by
    unfold EE.edgeN
    rw [hveq]
    push_cast
    rfl
  have hvN : varpi0 q ≤ (EE.edgeN q : ℝ) := by
    rw [hNe]
    exact (Nat.lt_floor_add_one _).le
  have hNv : (EE.edgeN q : ℝ) ≤ varpi0 q + 1 := by
    rw [hNe]
    linarith [Nat.floor_le hv0']
  unfold EE.CoverB
  rw [hveq]
  exact ⟨h1', EE.region_concave q hv0' (by linarith) hvN hNv h1' h2'⟩

end Principia.Common.TernaryGoldbach.ER
