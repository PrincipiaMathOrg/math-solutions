/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LargeQHipo
import Principia.Common.TernaryGoldbach.SuspiroWrap

set_option autoImplicit false

/-!
# `LQ.Varpi0Mono`, `eq:drolo`, `eq:mutuso`: the analysis of `prop:espagn`'s large-`q` tail

* **`varpi0Mono`** (`ternvin.tex` 3129-3144): `ϖ₀` is non-decreasing from `3.3·10⁹` on. With
  `A = c(1.36)q^τ`, `ℓ = log q`, `D = A − ℓ`: `A₂ − A₁ = A₁(e^{τ(ℓ₂−ℓ₁)} − 1) ≥ τA₁(ℓ₂ − ℓ₁) ≥
  ℓ₂ − ℓ₁` (`τA₁ ≥ 1`), so `D` increases, and then `A − ℓ/D^{τ/(1−τ)}` does too (`D ≥ 1`).
* **`drolo`** (`eq:drolo`, 3155-3158): `q^{0.2797} ≤ ϖ₀(q)` for `q ≥ Π_{p≤31} p`. Rather than
  Helfgott's rounded `(0.911q^{0.224} − log q)^{1.289}`, it is proved from `τ ≥ 0.22458`,
  `c(1.36) ≥ 0.90766` and `y = log q ≥ 26`: `A − ℓ ≥ 1.107e^{0.2169y} − y ≥ e^{0.2169y}` and
  `0.2169/(1 − τ) ≥ 0.2797`.
* **`mutuso`** (`eq:mutuso`, 3163-3173):
  `190.272(log t)³e^{2.24742t^{1/3}} ≤ e^{0.224t}(0.8009t − log t + 0.07354)³` for `t ≥ 31`, by
  Helfgott's route (`0.8009t − log t + 0.07354 ≥ 0.6924t`, then `3 log log t − 3 log t` decreases
  and `2.24742t^{1/3} − 0.224t` decreases); margin `0.109` in logarithms at `t = 31`.
* **`mutusoWo`** — the `210 ∤ q` case (3203-3208), CORRECTED: from `log q ≥ θ(p₁) − log 7` the
  denominator of `eq:hipowo` is `(0.8009t − log 7 − log t + 0.35152)³`, not Helfgott's
  `(0.8009t − log t + 0.07354)³`, and `ϖ₀ ≥ q^{0.2797} ≥ e^{0.224t}/7^{0.2797}` (he divides by `7`).
  The corrected inequality `84.351·1.73·(log t)³e^{2.24742t^{1/3}} ≤ e^{0.224t}(…)³` holds for
  `t ≥ 37` with margin `1.53` in logarithms; the printed conclusion stands.
-/

namespace Principia.Common.TernaryGoldbach.LQ

open Principia.Common.TernaryGoldbach.HC (tauE cSig varpi0)

/-! ## (1) Numerics -/

/-- `e⁵ ≥ 148.41`. -/
theorem exp5_ge : (148.41 : ℝ) ≤ Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  rw [← Real.exp_nat_mul] at this
  norm_num at this ⊢
  linarith

/-- `e³ ≤ 20.0856`. -/
theorem exp3_le : Real.exp 3 ≤ 20.0856 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 3
  rw [← Real.exp_nat_mul] at this
  norm_num at this ⊢
  linarith

/-- `e³ ≥ 20.0855`. -/
theorem exp3_ge : (20.0855 : ℝ) ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
  rw [← Real.exp_nat_mul] at this
  norm_num at this ⊢
  linarith

/-- The Taylor lower bound `Σ_{m<n} x^m/m! ≤ e^x`, expanded. -/
theorem exp_ge_taylor (x : ℝ) (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040 ≤
      Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- The Taylor upper bound on `[0, 1]`, six terms. -/
theorem exp_le_taylor (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 * 7 / 4320 := by
  have h := Real.exp_bound' hx hx1 (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `3.433 ≤ log 31` (`e^{3.433} ≤ 30.97`). -/
theorem log31_ge : (3.433 : ℝ) ≤ Real.log 31 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 3.433 = Real.exp 3 * Real.exp 0.433 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_le_taylor 0.433 (by norm_num) (by norm_num)
  norm_num at h2
  have h3 := exp3_le
  rw [h1]
  have := mul_le_mul h3 h2 (Real.exp_pos _).le (by norm_num)
  linarith

/-- `log 31 ≤ 3.434` (`e^{3.434} ≥ 31.0005`). -/
theorem log31_le : Real.log 31 ≤ 3.434 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 3.434 = Real.exp 3 * Real.exp 0.434 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_ge_taylor 0.434 (by norm_num)
  norm_num at h2
  have h3 := exp3_ge
  rw [h1]
  have := mul_le_mul h3 h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `log 3.433 ≤ 1.24`. -/
theorem log3433_le : Real.log 3.433 ≤ 1.24 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 1.24 = Real.exp 1 * Real.exp 0.24 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_ge_taylor 0.24 (by norm_num)
  norm_num at h2
  have h3 := Real.exp_one_gt_d9
  rw [h1]
  have := mul_le_mul h3.le h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `log 190.272 ≤ 5.25`. -/
theorem log190_le : Real.log 190.272 ≤ 5.25 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 5.25 = Real.exp 5 * Real.exp 0.25 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_ge_taylor 0.25 (by norm_num)
  norm_num at h2
  have h3 := exp5_ge
  rw [h1]
  have := mul_le_mul h3 h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `−0.368 ≤ log 0.6924`. -/
theorem log6924_ge : (-0.368 : ℝ) ≤ Real.log 0.6924 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h2 := exp_ge_taylor 0.368 (by norm_num)
  have hinv : Real.exp (-0.368) = (Real.exp 0.368)⁻¹ := Real.exp_neg _
  rw [hinv, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num at h2 ⊢
  linarith

/-- `3.61 ≤ log 37` (`e^{3.61} ≤ 36.97`). -/
theorem log37_ge : (3.61 : ℝ) ≤ Real.log 37 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 3.61 = Real.exp 3 * Real.exp 0.61 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_le_taylor 0.61 (by norm_num) (by norm_num)
  norm_num at h2
  have h3 := exp3_le
  rw [h1]
  have := mul_le_mul h3 h2 (Real.exp_pos _).le (by norm_num)
  linarith

/-- `log 37 ≤ 3.611`. -/
theorem log37_le : Real.log 37 ≤ 3.611 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 3.611 = Real.exp 3 * Real.exp 0.611 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_ge_taylor 0.611 (by norm_num)
  norm_num at h2
  have h3 := exp3_ge
  rw [h1]
  have := mul_le_mul h3 h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `log 3.61 ≤ 1.285`. -/
theorem log361_le : Real.log 3.61 ≤ 1.285 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 1.285 = Real.exp 1 * Real.exp 0.285 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_ge_taylor 0.285 (by norm_num)
  norm_num at h2
  have h3 := Real.exp_one_gt_d9
  rw [h1]
  have := mul_le_mul h3.le h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `log(84.351·1.73) ≤ 4.99` (`e^{4.99} ≥ 0.99e⁵`). -/
theorem log146_le : Real.log (84.351 * 1.73) ≤ 4.99 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 4.99 = Real.exp 5 * Real.exp (-0.01) := by rw [← Real.exp_add]; norm_num
  have h2 := Real.add_one_le_exp (-0.01)
  have h3 := exp5_ge
  rw [h1]
  have := mul_le_mul h3 h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `−0.416 ≤ log 0.66`. -/
theorem log066_ge : (-0.416 : ℝ) ≤ Real.log 0.66 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h2 := exp_ge_taylor 0.416 (by norm_num)
  have hinv : Real.exp (-0.416) = (Real.exp 0.416)⁻¹ := Real.exp_neg _
  rw [hinv, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num at h2 ⊢
  linarith

/-- `1.9459 ≤ log 7 ≤ 1.946` (`log 7 = 3 log 2 + log(1 − 1/8)`). -/
theorem log7_bounds : (1.9459 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ 1.946 := by
  have hb := Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 1 / 8) (by norm_num)
    (by norm_num) 8
  have h7 : Real.log 7 = 3 * Real.log 2 - -Real.log (1 - 1 / 8) := by
    rw [show (7 : ℝ) = 2 ^ 3 * (1 - 1 / 8) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h7]
  norm_num at h2 h2' ⊢
  constructor <;> linarith [hb.1, hb.2]

/-- `e^{0.5444} ≤ 1.73`. -/
theorem exp5444_le : Real.exp 0.5444 ≤ 1.73 := by
  have h := exp_le_taylor 0.5444 (by norm_num) (by norm_num)
  norm_num at h
  linarith

/-- `7^{0.2797} ≤ 1.73`. -/
theorem seven_pow_le : (7 : ℝ) ^ (0.2797 : ℝ) ≤ 1.73 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h := log7_bounds.2
  have h1 : Real.exp (Real.log 7 * 0.2797) ≤ Real.exp 0.5444 :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith [exp5444_le]

/-- `26 ≤ log(Π_{p≤31} p)` (`e^{26} ≤ 2.7182818286^{26} ≤ 2.0056·10¹¹`). -/
theorem logQ31_ge : (26 : ℝ) ≤ Real.log 200560490130 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 1 ^ 26 ≤ (2.7182818286 : ℝ) ^ 26 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 26
  rw [← Real.exp_nat_mul] at this
  norm_num at this ⊢
  linarith

/-- `e^{0.2169·26} ≥ 280`. -/
theorem exp5639_ge : (280 : ℝ) ≤ Real.exp (0.2169 * 26) := by
  have h1 : Real.exp (0.2169 * 26) = Real.exp 5 * Real.exp 0.6394 := by
    rw [← Real.exp_add]; norm_num
  have h2 := exp_ge_taylor 0.6394 (by norm_num)
  norm_num at h2
  have h3 := exp5_ge
  rw [h1]
  have := mul_le_mul h3 h2 (by norm_num) (Real.exp_pos _).le
  linarith

/-- `0.22458 ≤ τ ≤ 0.2247` (`τ = 0.4e^{−γ}`, `1.7808 ≤ e^γ ≤ 1.7810727`). -/
theorem tauE_bounds : (0.22458 : ℝ) ≤ tauE ∧ tauE ≤ 0.2247 := by
  have hg1 := Principia.Erdos1054.Proofs.SmallRatio.exp_gamma_le
  have hg2 := HX.expG_ge
  have he : Real.exp (-Real.eulerMascheroniConstant) =
      (Real.exp Real.eulerMascheroniConstant)⁻¹ := Real.exp_neg _
  unfold tauE
  rw [he]
  have hpos : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    nlinarith
  · rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith

/-- `c(1.36) ≥ 0.90766` (`c = exp(−0.164439e^{−γ})`, `e^{−γ} ≤ 1/1.7808`). -/
theorem cSig_ge : (0.90766 : ℝ) ≤ cSig 1.36 := by
  unfold cSig
  have hg2 := HX.expG_ge
  have he : Real.exp (-Real.eulerMascheroniConstant) =
      (Real.exp Real.eulerMascheroniConstant)⁻¹ := Real.exp_neg _
  have hpos : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have hinv : (Real.exp Real.eulerMascheroniConstant)⁻¹ ≤ 1 / 1.7808 := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hg2
  have hinv0 : 0 ≤ (Real.exp Real.eulerMascheroniConstant)⁻¹ := inv_nonneg.mpr hpos.le
  have hx : -0.09234 ≤ Real.exp (-Real.eulerMascheroniConstant) *
      (1.36 - 1.36 ^ 2 / 5.248 - 1.172) := by
    rw [he]
    have hk : (1.36 : ℝ) - 1.36 ^ 2 / 5.248 - 1.172 = -(3371 / 20500 : ℝ) := by
      norm_num
    rw [hk]
    have : (3371 / 20500 : ℝ) * (Real.exp Real.eulerMascheroniConstant)⁻¹ ≤
        3371 / 20500 * (1 / 1.7808) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    norm_num at this ⊢
    linarith
  have h1 := Real.add_one_le_exp (Real.exp (-Real.eulerMascheroniConstant) *
    (1.36 - 1.36 ^ 2 / 5.248 - 1.172))
  linarith

/-! ## (2) `ϖ₀` is non-decreasing -/

/-- **`LQ.Varpi0Mono`, PROVED** (`ternvin.tex` 3129-3144). -/
theorem varpi0Mono : Varpi0Mono := by
  intro q1 q2 h1 h12 hpos
  have hq1 : 0 < q1 := by linarith
  have hq2 : 0 < q2 := by linarith
  obtain ⟨hτ, -⟩ := tauE_bounds
  have hτ1 := HX.tauE_lt_one
  have hbr1 : Real.log q1 + 1 < cSig 1.36 * q1 ^ tauE := by
    by_contra h
    unfold varpi0 at hpos
    rw [if_neg h] at hpos
    exact lt_irrefl 0 hpos
  have hl1 : 3.5 ≤ Real.log q1 := by
    rw [Real.le_log_iff_exp_le hq1]
    have : Real.exp 3.5 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
    have h4 : Real.exp 4 ≤ 81 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp 1 ^ 4 ≤ (3 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 4
      rw [← Real.exp_nat_mul] at this
      norm_num at this ⊢
      linarith
    linarith
  have hl12 : Real.log q1 ≤ Real.log q2 := Real.log_le_log hq1 h12
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = cSig 1.36 * q1 ^ tauE := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = cSig 1.36 * q2 ^ tauE := ⟨_, rfl⟩
  obtain ⟨l1, hl1d⟩ : ∃ l1, l1 = Real.log q1 := ⟨_, rfl⟩
  obtain ⟨l2, hl2d⟩ : ∃ l2, l2 = Real.log q2 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = tauE / (1 - tauE) := ⟨_, rfl⟩
  have hbr1' : l1 + 1 < A1 := by rw [hA1, hl1d]; exact hbr1
  have hl1' : 3.5 ≤ l1 := by rw [hl1d]; exact hl1
  have hl12' : l1 ≤ l2 := by rw [hl1d, hl2d]; exact hl12
  have hτA : 1 ≤ tauE * A1 := by nlinarith
  have hA2e : A2 = A1 * Real.exp (tauE * (l2 - l1)) := by
    have e : Real.log q2 * tauE = Real.log q1 * tauE + tauE * (Real.log q2 - Real.log q1) := by
      ring
    rw [hA1, hA2, hl1d, hl2d, Real.rpow_def_of_pos hq1, Real.rpow_def_of_pos hq2, mul_assoc,
      ← Real.exp_add, ← e]
  have hA : l2 - l1 ≤ A2 - A1 := by
    have he := Real.add_one_le_exp (tauE * (l2 - l1))
    have hA10 : 0 ≤ A1 := by linarith
    have : A1 * (tauE * (l2 - l1) + 1) ≤ A1 * Real.exp (tauE * (l2 - l1)) :=
      mul_le_mul_of_nonneg_left he hA10
    nlinarith
  have hD1 : 1 < A1 - l1 := by linarith
  have hD2 : A1 - l1 ≤ A2 - l2 := by linarith
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg (by linarith) (by linarith)
  have hD1k : 1 ≤ (A1 - l1) ^ κ := Real.one_le_rpow hD1.le hκ0
  have hD12k : (A1 - l1) ^ κ ≤ (A2 - l2) ^ κ := Real.rpow_le_rpow (by linarith) hD2 hκ0
  have hl2 : 0 ≤ l2 := by linarith
  have hE1 : A1 - l1 ≤ A1 - l1 / (A1 - l1) ^ κ := by
    have : l1 / (A1 - l1) ^ κ ≤ l1 := div_le_self (by linarith) hD1k
    linarith
  have hE : A1 - l1 / (A1 - l1) ^ κ ≤ A2 - l2 / (A2 - l2) ^ κ := by
    have h1 : l2 / (A2 - l2) ^ κ ≤ l2 / (A1 - l1) ^ κ :=
      div_le_div_of_nonneg_left hl2 (by linarith) hD12k
    have h2 : (l2 - l1) / (A1 - l1) ^ κ ≤ l2 - l1 := div_le_self (by linarith) hD1k
    have e : l2 / (A1 - l1) ^ κ - l1 / (A1 - l1) ^ κ = (l2 - l1) / (A1 - l1) ^ κ := by ring
    linarith
  have hbr2 : l2 + 1 < A2 := by linarith
  have hbr2' : Real.log q2 + 1 < cSig 1.36 * q2 ^ tauE := by rw [← hA2, ← hl2d]; exact hbr2
  unfold varpi0
  rw [if_pos hbr1, if_pos hbr2', ← hA1, ← hA2, ← hl1d, ← hl2d, ← hκ]
  exact Real.rpow_le_rpow (by linarith) hE (div_nonneg (by norm_num) (by linarith))

/-! ## (3) `eq:drolo` -/

/-- **`eq:drolo`, PROVED**: `q^{0.2797} ≤ ϖ₀(q)` for `q ≥ Π_{p≤31} p = 200560490130`. -/
theorem drolo (q : ℝ) (hq : 200560490130 ≤ q) : q ^ (0.2797 : ℝ) ≤ varpi0 q := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hτ, hτu⟩ := tauE_bounds
  have hc := cSig_ge
  obtain ⟨y, hy⟩ : ∃ y, y = Real.log q := ⟨_, rfl⟩
  have hy26 : 26 ≤ y := by rw [hy]; exact le_trans logQ31_ge (Real.log_le_log (by norm_num) hq)
  obtain ⟨E, hEdef⟩ : ∃ E, E = Real.exp (0.2169 * y) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  -- `q^τ ≥ 1.2196 E`
  have hqτ : q ^ tauE = E * Real.exp ((tauE - 0.2169) * y) := by
    have e : Real.log q * tauE = 0.2169 * y + (tauE - 0.2169) * y := by rw [← hy]; ring
    rw [Real.rpow_def_of_pos hq0, hEdef, ← Real.exp_add, e]
  have hx : 0.19968 ≤ (tauE - 0.2169) * y := by nlinarith
  have hq2 := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ (tauE - 0.2169) * y)
  have hexp : (1.2196 : ℝ) ≤ Real.exp ((tauE - 0.2169) * y) := by nlinarith
  have hA : 1.106 * E ≤ cSig 1.36 * q ^ tauE := by
    rw [hqτ]
    have h1 : 1.2196 * E ≤ E * Real.exp ((tauE - 0.2169) * y) := by nlinarith
    have h2 := mul_le_mul hc h1 (by positivity) (by linarith)
    nlinarith
  -- `0.106 E ≥ y`
  have hEy : y ≤ 0.106 * E := by
    have h1 : E = Real.exp (0.2169 * 26) * Real.exp (0.2169 * (y - 26)) := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      ring
    have h2 := Real.add_one_le_exp (0.2169 * (y - 26))
    have h3 := exp5639_ge
    have h4 : 280 * (0.2169 * (y - 26) + 1) ≤ E := by
      rw [h1]
      exact mul_le_mul h3 h2 (by nlinarith) (Real.exp_pos _).le
    nlinarith
  have hD : E ≤ cSig 1.36 * q ^ tauE - y := by linarith
  have hbr : y + 1 < cSig 1.36 * q ^ tauE := by nlinarith
  have hD1 : 1 ≤ cSig 1.36 * q ^ tauE - y := by nlinarith
  have hτ1 : tauE < 1 := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = tauE / (1 - tauE) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg (by linarith) (by linarith)
  have hDk : 1 ≤ (cSig 1.36 * q ^ tauE - y) ^ κ := Real.one_le_rpow hD1 hκ0
  have hy0 : 0 ≤ y := by linarith
  have hB : E ≤ cSig 1.36 * q ^ tauE - y / (cSig 1.36 * q ^ tauE - y) ^ κ := by
    have : y / (cSig 1.36 * q ^ tauE - y) ^ κ ≤ y := div_le_self hy0 hDk
    linarith
  have hbr' : Real.log q + 1 < cSig 1.36 * q ^ tauE := by rw [← hy]; exact hbr
  unfold varpi0
  rw [if_pos hbr', ← hy, ← hκ]
  have hmono : E ^ (1 / (1 - tauE)) ≤ (cSig 1.36 * q ^ tauE - y /
      (cSig 1.36 * q ^ tauE - y) ^ κ) ^ (1 / (1 - tauE)) :=
    Real.rpow_le_rpow hE0.le hB (div_nonneg (by norm_num) (by linarith))
  refine le_trans ?_ hmono
  -- `q^{0.2797} = e^{0.2797y} ≤ e^{0.2169y/(1−τ)} = E^{1/(1−τ)}`
  have hq' : q ^ (0.2797 : ℝ) = Real.exp (0.2797 * y) := by
    rw [Real.rpow_def_of_pos hq0, hy, mul_comm]
  have hE' : E ^ (1 / (1 - tauE)) = Real.exp (0.2169 * y * (1 / (1 - tauE))) := by
    rw [hEdef, ← Real.exp_mul]
  rw [hq', hE']
  apply Real.exp_le_exp.mpr
  have h1τ : 0 < 1 - tauE := by linarith
  have hk : 0.2797 ≤ 0.2169 * (1 / (1 - tauE)) := by
    rw [mul_one_div, le_div_iff₀ h1τ]
    nlinarith
  nlinarith

/-! ## (4) `eq:mutuso` -/

/-- `3 log L − 3L` is non-increasing on `L ≥ 1`: bounded by its value at `L₀ ≤ L`. -/
theorem logL_sub_le {L L0 : ℝ} (h0 : 1 ≤ L0) (h : L0 ≤ L) :
    3 * Real.log L - 3 * L ≤ 3 * Real.log L0 - 3 * L0 := by
  have hL0 : 0 < L0 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < L) hL0)
  rw [Real.log_div (by linarith) hL0.ne'] at h1
  have h2 : L / L0 - 1 ≤ L - L0 := by
    rw [div_sub_one hL0.ne', div_le_iff₀ hL0]
    nlinarith
  linarith

/-- `a t^{1/3} − b t` is non-increasing on `t ≥ t₀` when `3b·t₀^{2/3} ≥ a`, in the form used:
`a(u − u₀) ≤ b(u³ − u₀³)` for `u ≥ u₀ ≥ 0`, `3b u₀² ≥ a`. -/
theorem cbrt_lin_le {a b u u0 : ℝ} (hb : 0 ≤ b) (hu0 : 0 ≤ u0) (hu : u0 ≤ u)
    (hab : a ≤ 3 * b * u0 ^ 2) : a * (u - u0) ≤ b * (u ^ 3 - u0 ^ 3) := by
  have e : u ^ 3 - u0 ^ 3 = 3 * u0 ^ 2 * (u - u0) + (u - u0) ^ 2 * (u + 2 * u0) := by ring
  rw [e]
  have h1 : 0 ≤ (u - u0) ^ 2 * (u + 2 * u0) := mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : a * (u - u0) ≤ 3 * b * u0 ^ 2 * (u - u0) :=
    mul_le_mul_of_nonneg_right hab (by linarith)
  nlinarith [mul_nonneg hb h1]

/-- **`eq:mutuso`, PROVED** (`ternvin.tex` 3163-3173):
`190.272(log t)³e^{2.24742t^{1/3}} ≤ e^{0.224t}(0.8009t − log t + 0.07354)³` for `t ≥ 31`. -/
theorem mutuso (t : ℝ) (ht : 31 ≤ t) :
    190.272 * Real.log t ^ 3 * Real.exp (2.24742 * t ^ ((1 : ℝ) / 3)) ≤
      Real.exp (0.224 * t) * (0.8009 * t - Real.log t + 0.07354) ^ 3 := by
  have ht0 : 0 < t := by linarith
  set L := Real.log t with hLdef
  have hL31 : Real.log 31 ≤ L := Real.log_le_log (by norm_num) ht
  have hL : 3.433 ≤ L := le_trans log31_ge hL31
  have hL0 : 0 < L := by linarith
  -- `L ≤ log 31 + (t − 31)/31`
  have hLu : L ≤ 3.434 + (t / 31 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 31))
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    linarith [log31_le]
  have hW : 0.6924 * t ≤ 0.8009 * t - L + 0.07354 := by linarith
  have hW0 : 0 < 0.8009 * t - L + 0.07354 := by linarith
  -- the cube-root term
  set u := t ^ ((1 : ℝ) / 3) with hudef
  have hu3 : u ^ 3 = t := cube_cbrt ht0.le
  have hu31 : (31 : ℝ) ^ ((1 : ℝ) / 3) ≤ u := Real.rpow_le_rpow (by norm_num) ht (by norm_num)
  have hc31 : (31 : ℝ) ^ ((1 : ℝ) / 3) ≤ 3.1414 := cbrt_le (by norm_num) (by norm_num) (by norm_num)
  have hc31' : (3.1 : ℝ) ≤ (31 : ℝ) ^ ((1 : ℝ) / 3) := le_cbrt (by norm_num) (by norm_num)
  have hcube31 : ((31 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 31 := cube_cbrt (by norm_num)
  have hcl := cbrt_lin_le (a := 2.24742) (b := 0.224) (by norm_num) (by linarith) hu31
    (by nlinarith)
  rw [hu3, hcube31] at hcl
  -- the logarithmic inequality
  have hlog : Real.log 190.272 + 3 * Real.log L + 2.24742 * u ≤
      0.224 * t + 3 * Real.log (0.8009 * t - L + 0.07354) := by
    have h1 : Real.log (0.6924 * t) ≤ Real.log (0.8009 * t - L + 0.07354) :=
      Real.log_le_log (by positivity) hW
    rw [Real.log_mul (by norm_num) ht0.ne', ← hLdef] at h1
    have h2 := logL_sub_le (by norm_num : (1 : ℝ) ≤ 3.433) hL
    have h3 := log3433_le
    have h4 := log190_le
    have h5 := log6924_ge
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)] at hexp
  have hL3 : Real.exp (3 * Real.log L) = L ^ 3 := by
    have e : Real.log (L ^ 3) = 3 * Real.log L := by rw [Real.log_pow]; push_cast; ring
    rw [← e, Real.exp_log (by positivity)]
  have hW3 : Real.exp (3 * Real.log (0.8009 * t - L + 0.07354)) =
      (0.8009 * t - L + 0.07354) ^ 3 := by
    have e : Real.log ((0.8009 * t - L + 0.07354) ^ 3) =
        3 * Real.log (0.8009 * t - L + 0.07354) := by rw [Real.log_pow]; push_cast; ring
    rw [← e, Real.exp_log (by positivity)]
  rw [hL3, hW3] at hexp
  linarith

/-- **`eq:mutuso` for `210 ∤ q`, CORRECTED and PROVED** (`ternvin.tex` 3203-3208; module
docstring): `84.351·1.73·(log t)³e^{2.24742t^{1/3}} ≤
e^{0.224t}(0.8009t − log 7 − log t + 0.35152)³` for `t ≥ 37`. -/
theorem mutusoWo (t : ℝ) (ht : 37 ≤ t) :
    84.351 * 1.73 * Real.log t ^ 3 * Real.exp (2.24742 * t ^ ((1 : ℝ) / 3)) ≤
      Real.exp (0.224 * t) * (0.8009 * t - Real.log 7 - Real.log t + 0.35152) ^ 3 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨h7l, h7u⟩ := log7_bounds
  set L := Real.log t with hLdef
  have hL37 : Real.log 37 ≤ L := Real.log_le_log (by norm_num) ht
  have hL : 3.61 ≤ L := le_trans log37_ge hL37
  have hL0 : 0 < L := by linarith
  have hLu : L ≤ 3.611 + (t / 37 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 37))
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    linarith [log37_le]
  have hW : 0.66 * t ≤ 0.8009 * t - Real.log 7 - L + 0.35152 := by linarith
  have hW0 : 0 < 0.8009 * t - Real.log 7 - L + 0.35152 := by linarith
  set u := t ^ ((1 : ℝ) / 3) with hudef
  have hu3 : u ^ 3 = t := cube_cbrt ht0.le
  have hu37 : (37 : ℝ) ^ ((1 : ℝ) / 3) ≤ u := Real.rpow_le_rpow (by norm_num) ht (by norm_num)
  have hc37 : (37 : ℝ) ^ ((1 : ℝ) / 3) ≤ 3.3323 := cbrt_le (by norm_num) (by norm_num) (by norm_num)
  have hc37' : (3.3 : ℝ) ≤ (37 : ℝ) ^ ((1 : ℝ) / 3) := le_cbrt (by norm_num) (by norm_num)
  have hcube37 : ((37 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 37 := cube_cbrt (by norm_num)
  have hcl := cbrt_lin_le (a := 2.24742) (b := 0.224) (by norm_num) (by linarith) hu37
    (by nlinarith)
  rw [hu3, hcube37] at hcl
  have hlog : Real.log (84.351 * 1.73) + 3 * Real.log L + 2.24742 * u ≤
      0.224 * t + 3 * Real.log (0.8009 * t - Real.log 7 - L + 0.35152) := by
    have h1 : Real.log (0.66 * t) ≤ Real.log (0.8009 * t - Real.log 7 - L + 0.35152) :=
      Real.log_le_log (by positivity) hW
    rw [Real.log_mul (by norm_num) ht0.ne', ← hLdef] at h1
    have h2 := logL_sub_le (by norm_num : (1 : ℝ) ≤ 3.61) hL
    have h3 := log361_le
    have h4 := log146_le
    have h5 := log066_ge
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)] at hexp
  have hL3 : Real.exp (3 * Real.log L) = L ^ 3 := by
    have e : Real.log (L ^ 3) = 3 * Real.log L := by rw [Real.log_pow]; push_cast; ring
    rw [← e, Real.exp_log (by positivity)]
  have hW3 : Real.exp (3 * Real.log (0.8009 * t - Real.log 7 - L + 0.35152)) =
      (0.8009 * t - Real.log 7 - L + 0.35152) ^ 3 := by
    have e : Real.log ((0.8009 * t - Real.log 7 - L + 0.35152) ^ 3) =
        3 * Real.log (0.8009 * t - Real.log 7 - L + 0.35152) := by
      rw [Real.log_pow]; push_cast; ring
    rw [← e, Real.exp_log (by positivity)]
  rw [hL3, hW3] at hexp
  linarith

end Principia.Common.TernaryGoldbach.LQ
