/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MonoP
import Principia.Common.TernaryGoldbach.MonoTop

set_option autoImplicit false

/-!
# The top step at `(c05, C)`: `OSP.TopStepP` PROVED for `c05 ≥ 0`, `0 ≤ C ≤ 45.7575`

`TopStepP` does NOT follow from `OS.TopStepL`: `√r·gYP = √r·gYL + (c05 − 0.5)√ϝ/√2 +
(C − 22.7538)/√r`, and the last summand DEcreases. It is re-proved by regenerating
`MonoTop.lean`'s argument (`scratchpad/ostopp/gen_monotopp.py`, counted substitution):

* `sqrt_gYP`, `lLcP_step`, `topAP`, `topHP`, `conf_lowP`, `conf_highP`, `topStepP_of`: the
  generic steps, where `c05` enters only as `c05 ≥ 0` (`topAP`: the growth of
  `A = (R log 2t + c05)√ϝ + 2.5` is at least `R₀√ϝ₀ε` for every `c05 ≥ 0`) and `C` cancels
  (`lLcP_step`);
* **condition (C)** `L_{t₀} − 1.99(13/4·ϝ + 13.6516) ≤ √(2t₀)R√ϝ` is where `C` is priced: `L`
  rises by `C − 22.7538 ≤ 23.0037`, so `rhs_leP`'s constant is `11.3241 + 23.0037 = 34.3278`, and
  the certified closings (`condC_AP`, `condC_BP`) keep margins `5.58` (regime A, `t₀ = 1.5·10⁵`:
  `439.26` against `433.68`) and `12.2` (regime B).

Float re-check before claiming (`scratchpad/ostopp/topstep_check.py`, `topstep_check.out`): at
the true `R`, `ϝ` condition (C) has ratio ≥ 1.2 on every sampled pair, and the top step itself
holds at `y = 10²⁵, 10²⁶, 10³⁰, 10⁴⁰`.
-/

namespace Principia.Common.TernaryGoldbach.MTOP

open Set MeasureTheory
open Principia.Common.TernaryGoldbach.MO
open Principia.Common.TernaryGoldbach.OP

/-! ## (1) Condition (C) at `C ≤ 45.7575` -/

/-- **The right side of condition (C) at `C ≤ 45.7575`**: `MO.rhs_le` with `L` raised by
`C − 22.7538 ≤ 23.0037` (`OP.lLcP_eq`). -/
theorem rhs_leP (C t : ℝ) (hC : C ≤ 45.7575) (ht : 32768 ≤ t) :
    lLcP C t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) ≤
      0.528125 * Real.log t ^ 2 + 27.2 * Real.log t + 34.3278 := by
  have h := rhs_le t ht
  rw [lLcP_eq]
  linarith

/-- **Condition (C), regime A, at `C ≤ 45.7575`** (generated from `MO.condC_A`:
`11.3241 ↦ 34.3278`). -/
theorem condC_AP (C t R : ℝ) (hC : C ≤ 45.7575) (ht : 1.5e5 ≤ t) (hR : 0.41415 ≤ R) :
    lLcP C t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) ≤
      Real.sqrt (2 * t) * R * Real.sqrt (MinSp.bigF t) := by
  have hrhs := rhs_leP C t hC (by linarith)
  have hg := sqrt_grow t 1.5e5 (by norm_num) ht
  have hl2 := Real.log_two_lt_d9
  have hT : Real.log 1.5e5 ≤ 11.92214 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < (1.5e5) ^ 5)
      (by norm_num : ((1.5e5 : ℝ)) ^ 5 ≤ 2 ^ 86)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    generalize Real.log 1.5e5 = c at h ⊢
    generalize Real.log 2 = b at h hl2
    linarith
  have hS0 : 387.29 ≤ Real.sqrt 1.5e5 := by
    rw [show (387.29 : ℝ) = Real.sqrt (387.29 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2 : 1.41421 ≤ Real.sqrt 2 := by
    rw [show (1.41421 : ℝ) = Real.sqrt (1.41421 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hF := GS.bigF_gt t (by linarith)
  have hsF : 1.93649 ≤ Real.sqrt (MinSp.bigF t) := by
    rw [show (1.93649 : ℝ) = Real.sqrt (1.93649 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs : 0 ≤ Real.log t - Real.log 1.5e5 := by
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 1.5e5) ht]
  have hc0 : 0 ≤ Real.log 1.5e5 := Real.log_nonneg (by norm_num)
  rw [Real.sqrt_mul' 2 (by linarith)]
  -- `LHS ≥ 1.41421·S·0.41415·1.93649`
  have hS : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hL1 : 1.41421 * Real.sqrt t ≤ Real.sqrt 2 * Real.sqrt t := mul_le_mul_of_nonneg_right hs2 hS
  have hL2 : 1.41421 * Real.sqrt t * 0.41415 ≤ Real.sqrt 2 * Real.sqrt t * R :=
    mul_le_mul hL1 hR (by norm_num) (by positivity)
  have hL3 : 1.41421 * Real.sqrt t * 0.41415 * 1.93649 ≤
      Real.sqrt 2 * Real.sqrt t * R * Real.sqrt (MinSp.bigF t) :=
    mul_le_mul hL2 hsF (by norm_num) (by positivity)
  generalize Real.sqrt 2 * Real.sqrt t * R * Real.sqrt (MinSp.bigF t) = LHS at hL3 ⊢
  generalize lLcP C t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) = RHS at hrhs ⊢
  generalize Real.log 1.5e5 = c at hT hg hs hc0
  generalize Real.log t = l at hrhs hg hs
  generalize Real.sqrt t = S at hg hL3 hS
  generalize Real.sqrt 1.5e5 = S0 at hg hS0
  obtain ⟨d, rfl⟩ : ∃ d : ℝ, l = c + d := ⟨l - c, by ring⟩
  have hd : 0 ≤ d := by linarith
  have hB0 : 0 ≤ 1 + (c + d - c) / 2 + (c + d - c) ^ 2 / 8 := by nlinarith
  have hB : 387.29 * (1 + (c + d - c) / 2 + (c + d - c) ^ 2 / 8) ≤ S :=
    le_trans (mul_le_mul_of_nonneg_right hS0 hB0) hg
  have e : (1 + (c + d - c) / 2 + (c + d - c) ^ 2 / 8) = 1 + d / 2 + d ^ 2 / 8 := by ring
  rw [e] at hB
  have h1 := mul_nonneg hc0 (sub_nonneg.2 hT)
  have h2 := mul_nonneg hd (sub_nonneg.2 hT)
  have key : 0.528125 * (c + d) ^ 2 + 27.2 * (c + d) + 34.3278 ≤
      1.41421 * 0.41415 * 1.93649 * (387.29 * (1 + d / 2 + d ^ 2 / 8)) := by
    nlinarith
  nlinarith

/-- **Condition (C), regime B, at `C ≤ 45.7575`** (generated from `MO.condC_B`:
`11.3241 ↦ 34.3278`). -/
theorem condC_BP (C t R : ℝ) (hC : C ≤ 45.7575) (ht : 5.9e4 ≤ t) (ht' : t ≤ 1.6e5)
    (hR : 0.5697 ≤ R) :
    lLcP C t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) ≤
      Real.sqrt (2 * t) * R * Real.sqrt (MinSp.bigF t) := by
  have ht0 : 0 < t := by linarith
  have hrhs := rhs_leP C t hC (by linarith)
  have hg := sqrt_grow t 5.9e4 (by norm_num) ht
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl3 := log3_le
  have hT : Real.log 5.9e4 ≤ 11.09036 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 5.9e4) (by norm_num : (5.9e4 : ℝ) ≤ 2 ^ 16)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 5.9e4 = c at h ⊢
    generalize Real.log 2 = b at h hl2
    linarith
  have hS0 : 242.89 ≤ Real.sqrt 5.9e4 := by
    rw [show (242.89 : ℝ) = Real.sqrt (242.89 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2 : 1.41421 ≤ Real.sqrt 2 := by
    rw [show (1.41421 : ℝ) = Real.sqrt (1.41421 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- `ϝ(t) ≥ 4.458`
  have hlt : 10.39 ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 15) (le_trans (by norm_num) ht)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 2 = b at h hl2'
    linarith
  have hlt12 : Real.log t ≤ 12 := by
    rw [Real.log_le_iff_le_exp ht0]
    have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have : (2.7182818283 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12
    have : (1.6e5 : ℝ) ≤ 2.7182818283 ^ 12 := by norm_num
    rw [h12]
    linarith
  have hm : 2.3 ≤ Real.log (Real.log t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [exp23_le]
  have hm' : Real.log (Real.log t) ≤ 2.4857693 := by
    have h1 : Real.log (Real.log t) ≤ Real.log 12 := Real.log_le_log (by linarith) hlt12
    have h2 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    generalize Real.log 3 = a at h1 hl3
    generalize Real.log 2 = b at h1 hl2
    linarith
  have hF : 4.4582 ≤ MinSp.bigF t := by
    unfold MinSp.bigF
    have hg1 := GS.exp_gamma_gt
    have h1 := mul_le_mul_of_nonneg_right hg1.le (by linarith : (0 : ℝ) ≤ Real.log (Real.log t))
    have h2 : 2.50637 / 2.4857693 ≤ 2.50637 / Real.log (Real.log t) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hm'
    nlinarith
  have hsF : 2.1114 ≤ Real.sqrt (MinSp.bigF t) := by
    rw [show (2.1114 : ℝ) = Real.sqrt (2.1114 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs : 0 ≤ Real.log t - Real.log 5.9e4 := by
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 5.9e4) ht]
  have hc0 : 0 ≤ Real.log 5.9e4 := Real.log_nonneg (by norm_num)
  rw [Real.sqrt_mul' 2 ht0.le]
  have hS : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hL1 : 1.41421 * Real.sqrt t ≤ Real.sqrt 2 * Real.sqrt t := mul_le_mul_of_nonneg_right hs2 hS
  have hL2 : 1.41421 * Real.sqrt t * 0.5697 ≤ Real.sqrt 2 * Real.sqrt t * R :=
    mul_le_mul hL1 hR (by norm_num) (by positivity)
  have hL3 : 1.41421 * Real.sqrt t * 0.5697 * 2.1114 ≤
      Real.sqrt 2 * Real.sqrt t * R * Real.sqrt (MinSp.bigF t) :=
    mul_le_mul hL2 hsF (by norm_num) (by positivity)
  generalize Real.sqrt 2 * Real.sqrt t * R * Real.sqrt (MinSp.bigF t) = LHS at hL3 ⊢
  generalize lLcP C t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) = RHS at hrhs ⊢
  generalize Real.log 5.9e4 = c at hT hg hs hc0
  generalize Real.log t = l at hrhs hg hs hlt hlt12 hm hm'
  generalize Real.sqrt t = S at hg hL3 hS
  generalize Real.sqrt 5.9e4 = S0 at hg hS0
  obtain ⟨d, rfl⟩ : ∃ d : ℝ, l = c + d := ⟨l - c, by ring⟩
  have hd : 0 ≤ d := by linarith
  have hB0 : 0 ≤ 1 + (c + d - c) / 2 + (c + d - c) ^ 2 / 8 := by nlinarith
  have hB : 242.89 * (1 + (c + d - c) / 2 + (c + d - c) ^ 2 / 8) ≤ S :=
    le_trans (mul_le_mul_of_nonneg_right hS0 hB0) hg
  have e : (1 + (c + d - c) / 2 + (c + d - c) ^ 2 / 8) = 1 + d / 2 + d ^ 2 / 8 := by ring
  rw [e] at hB
  have h1 := mul_nonneg hc0 (sub_nonneg.2 hT)
  have h2 := mul_nonneg hd (sub_nonneg.2 hT)
  have key : 0.528125 * (c + d) ^ 2 + 27.2 * (c + d) + 34.3278 ≤
      1.41421 * 0.5697 * 2.1114 * (242.89 * (1 + d / 2 + d ^ 2 / 8)) := by
    nlinarith
  nlinarith

/-! ## (2) The generic steps -/

/-- `√t·gYP = A/√2 + L_t/√t + 3.2Y^{−1/6}√t` (generated from `MO.sqrt_gYL`). -/
theorem sqrt_gYP (c05 C Y t : ℝ) (ht : 0 < t) :
    Real.sqrt t * gYP c05 C Y t =
      ((MinSp.rR Y (2 * t) * Real.log (2 * t) + c05) * Real.sqrt (MinSp.bigF t) + 2.5) /
          Real.sqrt 2 + lLcP C t / Real.sqrt t + 3.2 * Y ^ (-(1 : ℝ) / 6) * Real.sqrt t := by
  have hs := Real.sqrt_pos.2 ht
  have hs2 := Real.sqrt_pos.2 (two_pos : (0 : ℝ) < 2)
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  unfold gYP
  rw [Real.sqrt_mul' 2 ht.le]
  generalize (MinSp.rR Y (2 * t) * Real.log (2 * t) + c05) * Real.sqrt (MinSp.bigF t) + 2.5 = A
  generalize lLcP C t = L
  generalize 3.2 * Y ^ (-(1 : ℝ) / 6) = Z
  generalize Real.sqrt 2 = q at hs2 ⊢
  generalize Real.sqrt t = s at hs htt ⊢
  subst htt
  field_simp

/-- **`L_{t₁} ≥ L_{t₀} + (13/4·ϝ(t₀) + 13.6516)(log t₁ − log t₀)`** at every `C` (generated from
`MO.lLc_step`; `C` cancels). -/
theorem lLcP_step (C t0 t1 : ℝ) (h0 : 50 ≤ t0) (h01 : t0 ≤ t1) :
    lLcP C t0 + (13 / 4 * MinSp.bigF t0 + 13.6516) * (Real.log t1 - Real.log t0) ≤
      lLcP C t1 := by
  have ht0 : 0 < t0 := by linarith
  have ht1 : 0 < t1 := by linarith
  have hF := GS.bigF_mono t0 t1 h0 h01
  have hl2 := Real.log_pos one_lt_two
  have hlt1 : 0 ≤ Real.log t1 := Real.log_nonneg (by linarith)
  have hK1 : 0 ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log t1 + 80 / 9 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hF hK1
  unfold lLcP
  rw [OL.log_two_rpow_mul _ _ t0 ht0, OL.log_two_rpow_mul _ _ t0 ht0,
    OL.log_two_rpow_mul _ _ t1 ht1, OL.log_two_rpow_mul _ _ t1 ht1]
  have e : MinSp.bigF t0 * (7 / 4 * Real.log 2 + 13 / 4 * Real.log t0 + 80 / 9) +
      (1.7984 * Real.log 2 + 13.6516 * Real.log t0) + C +
      (13 / 4 * MinSp.bigF t0 + 13.6516) * (Real.log t1 - Real.log t0) =
      MinSp.bigF t0 * (7 / 4 * Real.log 2 + 13 / 4 * Real.log t1 + 80 / 9) +
        (1.7984 * Real.log 2 + 13.6516 * Real.log t1) + C := by ring
  rw [e]
  linarith

/-- **The increase of `A = (R log 2t + c05)√ϝ + 2.5`** for `c05 ≥ 0` (generated from `MO.topA`). -/
theorem topAP (c05 : ℝ) (hc05 : 0 ≤ c05) (Y t0 t1 : ℝ) (hY : 0 < Y) (h0 : 1000 ≤ t0)
    (h01 : t0 ≤ t1)
    (h1 : t1 ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0) * (Real.log t1 - Real.log t0) ≤
      ((MinSp.rR Y (2 * t1) * Real.log (2 * t1) + c05) * Real.sqrt (MinSp.bigF t1) + 2.5) -
        ((MinSp.rR Y (2 * t0) * Real.log (2 * t0) + c05) * Real.sqrt (MinSp.bigF t0) + 2.5) := by
  have ht0 : 0 < t0 := by linarith
  have ht1 : 0 < t1 := by linarith
  have hR01 := rR_mono Y t0 t1 hY (by linarith) h01 h1
  have hR0 := GS.rR_ge Y (2 * t0) hY (by linarith) (by linarith)
  have hsF01 : Real.sqrt (MinSp.bigF t0) ≤ Real.sqrt (MinSp.bigF t1) :=
    Real.sqrt_le_sqrt (GS.bigF_mono t0 t1 (by linarith) h01)
  have hsF0 : 0 ≤ Real.sqrt (MinSp.bigF t0) := Real.sqrt_nonneg _
  have hx : Real.log (2 * t1) - Real.log (2 * t0) = Real.log t1 - Real.log t0 := by
    rw [Real.log_mul two_ne_zero ht1.ne', Real.log_mul two_ne_zero ht0.ne']
    ring
  have hx1 : 0 ≤ Real.log (2 * t1) := Real.log_nonneg (by linarith)
  have k1 : MinSp.rR Y (2 * t0) * Real.log (2 * t1) ≤ MinSp.rR Y (2 * t1) * Real.log (2 * t1) :=
    mul_le_mul_of_nonneg_right hR01 hx1
  have k0 : 0 ≤ MinSp.rR Y (2 * t0) * Real.log (2 * t1) + c05 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.rR Y (2 * t0)) hx1
    linarith
  have k2 : (MinSp.rR Y (2 * t0) * Real.log (2 * t1) + c05) * Real.sqrt (MinSp.bigF t0) ≤
      (MinSp.rR Y (2 * t1) * Real.log (2 * t1) + c05) * Real.sqrt (MinSp.bigF t1) :=
    mul_le_mul (by linarith) hsF01 hsF0 (by linarith)
  have e : (MinSp.rR Y (2 * t0) * Real.log (2 * t1) + c05) * Real.sqrt (MinSp.bigF t0) -
      (MinSp.rR Y (2 * t0) * Real.log (2 * t0) + c05) * Real.sqrt (MinSp.bigF t0) =
      MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0) *
        (Real.log (2 * t1) - Real.log (2 * t0)) := by ring
  rw [hx] at e
  linarith

/-- **The top step at one scale** at `(c05, C)` (generated from `MO.topH`). -/
theorem topHP (c05 C : ℝ) (hc05 : 0 ≤ c05) (Y t0 t1 : ℝ) (hY : 0 < Y) (h0 : 1000 ≤ t0)
    (h01 : t0 ≤ t1)
    (h1 : t1 ≤ Y ^ ((1 : ℝ) / 3) / 6) (hρ : t1 ≤ 1.01 * t0)
    (hC : lLcP C t0 - 1.99 * (13 / 4 * MinSp.bigF t0 + 13.6516) ≤
      Real.sqrt (2 * t0) * MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0)) :
    Real.sqrt t0 * gYP c05 C Y t0 ≤ Real.sqrt t1 * gYP c05 C Y t1 := by
  have ht0 : 0 < t0 := by linarith
  have ht1 : 0 < t1 := by linarith
  have hR0 := GS.rR_ge Y (2 * t0) hY (by linarith) (by linarith)
  have hF0 := GS.bigF_gt t0 (by linarith)
  have hL := lLcP_step C t0 t1 (by linarith) h01
  have hA := topAP c05 hc05 Y t0 t1 hY h0 h01 h1
  have hsF0 : 0 ≤ Real.sqrt (MinSp.bigF t0) := Real.sqrt_nonneg _
  have hS0 : 0 < Real.sqrt t0 := Real.sqrt_pos.2 ht0
  have hq : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨ρ, hS1ρ, hρ1, hρ2, hε⟩ := rho_facts t0 t1 ht0 h01 hρ
  have hC' : lLcP C t0 - 1.99 * (13 / 4 * MinSp.bigF t0 + 13.6516) ≤
      Real.sqrt 2 * Real.sqrt t0 * (MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0)) := by
    rw [Real.sqrt_mul' 2 ht0.le] at hC
    linarith [mul_assoc (Real.sqrt 2 * Real.sqrt t0) (MinSp.rR Y (2 * t0))
      (Real.sqrt (MinSp.bigF t0))]
  have hZ : 3.2 * Y ^ (-(1 : ℝ) / 6) * Real.sqrt t0 ≤ 3.2 * Y ^ (-(1 : ℝ) / 6) * Real.sqrt t1 :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h01) (by positivity)
  have key := top_core _ _ (lLcP C t0) (lLcP C t1) (Real.sqrt t0) ρ (Real.log t1 - Real.log t0)
    (MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0)) (13 / 4 * MinSp.bigF t0 + 13.6516)
    (Real.sqrt 2) _ _ hS0 hρ1 hρ2 hε hq hq2 hA (mul_nonneg (by linarith) hsF0) (by linarith)
    (by linarith) hC' hZ
  rw [sqrt_gYP c05 C Y t0 ht0, sqrt_gYP c05 C Y t1 ht1, hS1ρ]
  rw [hS1ρ] at key
  exact key

/-- **The top step at `w ∈ [1/K, 1]`** at `(c05, C)`, `C ≤ 45.7575` (generated from
`MO.conf_low`). -/
theorem conf_lowP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC : C ≤ 45.7575) (v w R0 : ℝ)
    (hv : 46.41 ≤ v) (hy : (10 : ℝ) ^ 25 ≤ v ^ 15)
    (hR0 : 0.37499 * v ^ 4 ≤ R0)
    (hR0u : R0 ≤ 3 / 8 * v ^ 4)
    (hk : 5.9e4 * (15 * Real.log v) ≤ 2 * R0) (hw : 1 / MinSp.kK (v ^ 15) ≤ w) (hw1 : w ≤ 1) :
    Real.sqrt (w * R0) * gYP c05 C (w * v ^ 15) (w * R0) ≤
      Real.sqrt (w * (3 / 8 * v ^ 4)) * gYP c05 C (w * v ^ 15) (w * (3 / 8 * v ^ 4)) := by
  have hv0 : 0 < v := by linarith
  have hlv0 : 0 < Real.log v := Real.log_pos (by linarith)
  have hkK : 1 / MinSp.kK (v ^ 15) = 2 / (15 * Real.log v) := by
    unfold MinSp.kK
    rw [Real.log_pow]
    push_cast
    field_simp
  have hK0 : 0 < 1 / MinSp.kK (v ^ 15) := by rw [hkK]; positivity
  have hw0 : 0 < w := lt_of_lt_of_le hK0 hw
  have hY := GS.scale_ge (v ^ 15) w hy hw
  have hY0 : 0 < w * v ^ 15 := by positivity
  have hr1 : MinSp.r1y (v ^ 15) = 3 / 8 * v ^ 4 := by
    unfold MinSp.r1y
    rw [pow15_rpow v hv0 (4 / 15) 4 (by norm_num)]
  have harg := GS.arg_le_r1y (v ^ 15) w (3 / 8 * v ^ 4) (by positivity) hw0 hr1.symm.le
  rw [min_eq_left hw1] at harg
  have htop : w * (3 / 8 * v ^ 4) ≤ (w * v ^ 15) ^ ((1 : ℝ) / 3) / 6 :=
    le_trans harg (GS.r1y_le_third _ hY)
  have hlw : 2 / 15 ≤ Real.log v * w := by
    rw [hkK, div_le_iff₀ (by positivity)] at hw
    linarith
  have ht0 : 5.9e4 ≤ w * R0 := by
    have h1 : 2 / (15 * Real.log v) * R0 ≤ w * R0 :=
      mul_le_mul_of_nonneg_right (hkK ▸ hw) (le_trans (by positivity) hR0)
    have h2 : 5.9e4 ≤ 2 / (15 * Real.log v) * R0 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  have h01 : w * R0 ≤ w * (3 / 8 * v ^ 4) := mul_le_mul_of_nonneg_left hR0u hw0.le
  have hρw : w * (3 / 8 * v ^ 4) ≤ 1.01 * (w * R0) := by nlinarith
  refine topHP c05 C hc05 (w * v ^ 15) (w * R0) (w * (3 / 8 * v ^ 4)) hY0 (by linarith) h01
    htop hρw ?_
  have hRg := GS.rR_ge (w * v ^ 15) (2 * (w * R0)) hY0 (by linarith) (by linarith)
  by_cases h : 1.5e5 ≤ w * R0
  · exact condC_AP C _ _ hC h hRg
  · exact condC_BP C _ _ hC ht0 (by linarith)
      (rR_regB v w R0 hv hw0 hlw hR0 (lt_of_not_ge h) ht0 (le_trans h01 htop))

/-- **The top step at `w > 1`** at `(c05, C)`, `C ≤ 45.7575` (generated from `MO.conf_high`). -/
theorem conf_highP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC : C ≤ 45.7575) (v w R0 : ℝ)
    (hv : 46.41 ≤ v) (hy : (10 : ℝ) ^ 25 ≤ v ^ 15)
    (hR0u : R0 ≤ 3 / 8 * v ^ 4)
    (hρ : 3 / 8 * v ^ 4 ≤ 1.01 * R0) (hR0b : 1.5e5 ≤ R0) (hw : 1 < w) :
    Real.sqrt R0 * gYP c05 C (w * v ^ 15) R0 ≤
      Real.sqrt (3 / 8 * v ^ 4) * gYP c05 C (w * v ^ 15) (3 / 8 * v ^ 4) := by
  have hv0 : 0 < v := by linarith
  have hY : 3.4e23 ≤ w * v ^ 15 := by nlinarith
  have hY0 : 0 < w * v ^ 15 := by linarith
  have hr1 : MinSp.r1y (v ^ 15) = 3 / 8 * v ^ 4 := by
    unfold MinSp.r1y
    rw [pow15_rpow v hv0 (4 / 15) 4 (by norm_num)]
  have harg := GS.arg_le_r1y (v ^ 15) w (3 / 8 * v ^ 4) (by positivity) (by linarith)
    hr1.symm.le
  rw [min_eq_right hw.le, one_mul] at harg
  have htop : 3 / 8 * v ^ 4 ≤ (w * v ^ 15) ^ ((1 : ℝ) / 3) / 6 :=
    le_trans harg (GS.r1y_le_third _ hY)
  have hRg := GS.rR_ge (w * v ^ 15) (2 * R0) hY0 (by linarith) (by linarith)
  exact topHP c05 C hc05 (w * v ^ 15) R0 (3 / 8 * v ^ 4) hY0 (by linarith) hR0u htop hρ
    (condC_AP C _ _ hC hR0b hRg)

/-- **[TopStepP] PROVED for every `φ ≥ 0` in `L¹(0,∞)`, `c05 ≥ 0`, `0 ≤ C ≤ 45.7575`** (generated
from `MO.topStepL_of`). -/
theorem topStepP_of (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (hC : C ≤ 45.7575)
    (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (hφi : IntegrableOn φ (Ioi 0)) :
    OSP.TopStepP c05 C φ := by
  intro y hy
  obtain ⟨v, hv0, hyv, hv⟩ := scale_data y hy
  have hr1 : MinSp.r1y y = 3 / 8 * v ^ 4 := by
    rw [hyv]
    unfold MinSp.r1y
    rw [pow15_rpow v hv0 (4 / 15) 4 (by norm_num)]
  obtain ⟨hR0, hR0u, hρ, hR0b, h7500, hk59⟩ := top_data v hv
  have hlv0 : 0 < Real.log v := Real.log_pos (by linarith)
  have hkK : 1 / MinSp.kK y = 2 / (15 * Real.log v) := by
    rw [hyv]
    unfold MinSp.kK
    rw [Real.log_pow]
    push_cast
    field_simp
  have hK0 : 0 < 1 / MinSp.kK y := by rw [hkK]; positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    have hl17 := GS.log_gt y hy
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  have hint0 := GSP.gtlIntP c05 C hc05 hC0 φ hφi y hy (⌊3 / 8 * v ^ 4⌋₊ : ℝ) (by linarith)
    (by rw [hr1]; exact hR0u)
  have hint1 := GSP.gtlIntP c05 C hc05 hC0 φ hφi y hy (3 / 8 * v ^ 4) (by linarith)
    hr1.symm.le
  rw [hr1]
  obtain ⟨R0, hR0def⟩ : ∃ R0 : ℝ, R0 = (⌊3 / 8 * v ^ 4⌋₊ : ℝ) := ⟨_, rfl⟩
  rw [← hR0def] at hR0 hR0u hρ hR0b h7500 hk59 hint0 ⊢
  have hR0p : 0 < R0 := by linarith
  have hm0 : max (1 / MinSp.kK y) (1000 / R0) = 1 / MinSp.kK y := by
    refine max_eq_left ?_
    rw [hkK, div_le_div_iff₀ hR0p (by positivity)]
    linarith
  have hm1 : max (1 / MinSp.kK y) (1000 / (3 / 8 * v ^ 4)) = 1 / MinSp.kK y := by
    refine max_eq_left ?_
    rw [hkK, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [hm0] at hint0
  rw [hm1] at hint1
  unfold gTP
  simp only [hm0, hm1, intervalIntegral.integral_same, mul_zero, add_zero]
  rw [← mul_div_assoc, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (MajSp.l1_nonneg φ)
  rw [mul_add, mul_add, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 1 / MinSp.kK y := ⟨_, rfl⟩
  rw [← hk] at hK0 hK1 hint0 hint1 hkK ⊢
  refine add_le_add ?_ ?_
  · refine intervalIntegral.integral_mono_on hK1
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hK1).mpr hint0.1).const_mul _)
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hK1).mpr hint1.1).const_mul _)
      fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hK0 hw.1
    have hwk : 1 / MinSp.kK (v ^ 15) ≤ w := by rw [← hyv, ← hk]; exact hw.1
    have hc := conf_lowP c05 C hc05 hC v w R0 hv (hyv ▸ hy) hR0 hR0u hk59 hwk hw.2
    rw [Real.sqrt_mul hw0.le, Real.sqrt_mul hw0.le, mul_assoc, mul_assoc] at hc
    have hc' := le_of_mul_le_mul_left hc (Real.sqrt_pos.2 hw0)
    rw [← hyv] at hc'
    have := mul_le_mul_of_nonneg_right hc' (hφ0 w hw0.le)
    linarith [mul_assoc (Real.sqrt R0) (gYP c05 C (w * y) (w * R0)) (φ w),
      mul_assoc (Real.sqrt (3 / 8 * v ^ 4)) (gYP c05 C (w * y) (w * (3 / 8 * v ^ 4))) (φ w)]
  · refine setIntegral_mono_on (hint0.2.const_mul _) (hint1.2.const_mul _) measurableSet_Ioi
      fun w (hw : 1 < w) => ?_
    have hc := conf_highP c05 C hc05 hC v w R0 hv (hyv ▸ hy) hR0u hρ hR0b hw
    rw [← hyv] at hc
    have := mul_le_mul_of_nonneg_right hc (hφ0 w (by linarith))
    linarith [mul_assoc (Real.sqrt R0) (gYP c05 C (w * y) R0) (φ w),
      mul_assoc (Real.sqrt (3 / 8 * v ^ 4)) (gYP c05 C (w * y) (3 / 8 * v ^ 4)) (φ w)]

/-- **[TopStepP] on Helfgott's `φ` at `(0.811, 45.7575)`, PROVED**. -/
theorem topStepP_helf : OSP.TopStepP 0.811 45.7575 HW.phi :=
  topStepP_of 0.811 45.7575 (by norm_num) (by norm_num) (by norm_num) HW.phi
    (fun t _ => HW.phi_nonneg t) MinSp.phi_integrableOn

end Principia.Common.TernaryGoldbach.MTOP
