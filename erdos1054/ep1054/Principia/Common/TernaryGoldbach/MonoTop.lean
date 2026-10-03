/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MonoLinks
import Principia.Common.TernaryGoldbach.OstopSpine

set_option autoImplicit false

/-!
# The top step of `prop:palan`: `OS.TopStepL` PROVED

`OS.TopStepL φ`: `√⌊r₁⌋·g̃(y,⌊r₁⌋) ≤ √r₁·g̃(y,r₁)` for every `y ≥ 10²⁵` (defect D1 of
`OstopSpine`: the proof bounds the tail by `g̃(⌊r₁⌋)`, `M̃` types `g̃(r₁)`). Proved here for every
`φ ≥ 0` in `L¹(0,∞)` (`topStepL_of`), hence on Helfgott's `φ` (`topStepL_helf`). With
`MonoLinks.lean` this closes all four numeric layer-2 links of the corrected `thm:ostop`.

## The argument

* **The sliver vanishes at the top** (`top_data`): at `y = v¹⁵` (`v ≥ 46.41`) the level
  `R₀ = ⌊r₁⌋ ≥ 0.37499v⁴ ≥ 7500 log v`, so both cutoffs `max(1/K, 1000/r)` equal `1/K` and
  `√r·g̃(y,r)|φ|₁ = ∫_{1/K}^1 √r·gYL(wy,wr)φ + ∫_1^∞ √r·gYL(wy,r)φ` at `r ∈ {R₀, r₁}`.
* **Pointwise in `w`** (`conf_low`, `conf_high`) it suffices that `H(t) = √t·gYL(Y,t)` does not
  decrease from `t₀ = wR₀` to `t₁ = wr₁` (resp. `R₀`, `r₁`), `t₁ ≤ 1.01t₀`.
* **One-point reduction** (`topH`, `top_core`): `H = A/√2 + L_t/√t + 3.2Y^{−1/6}√t` with
  `A = (R_{Y,2t}log 2t + 1/2)√ϝ(t) + 2.5` (`sqrt_gYL`); `A` grows by `≥ R₀√ϝ₀·ε`
  (`topA`, `rR_mono`, `GS.bigF_mono`), `L` by `≥ (13/4·ϝ₀ + 13.6516)ε` (`lLc_step`),
  `ε = log t₁ − log t₀`, `ρ = √(t₁/t₀) ≤ 1.005` (`rho_facts`). So `H(t₀) ≤ H(t₁)` follows from
  **condition (C)** at `t₀` alone: `L_{t₀} − 1.99(13/4·ϝ(t₀) + 13.6516) ≤ √(2t₀)·R_{Y,2t₀}·√ϝ(t₀)`.
* **(C), regime A** (`condC_A`, `t₀ ≥ 1.5·10⁵`, any `R ≥ 0.41415`, `ϝ > 3.75`): the right side
  of (C) is `≤ 0.528125ℓ² + 27.2ℓ + 11.3241` (`rhs_le`, `e^γ ≤ 1.95`), the left `≥ 439.27(1 + s/2 +
  s²/8)` (`sqrt_grow`, `s = ℓ − log 1.5·10⁵`): at `s = 0`, `439.27` against `410.67`.
* **(C), regime B** (`condC_B`, `5.9·10⁴ ≤ t₀ < 1.5·10⁵`, which happens only for `w` near `1/K`
  and `y ≤ 60¹⁵`): `R_{Y,2t₀} ≥ 0.5697` (`rR_regB`: `v < 60`, `log 8t₀ ≥ 12.9965`,
  `log(9Y^{1/3}/(4.008t₀)) ≤ 8.1757`, ratio `u ≥ 7/9`, `log(16/9) ≥ 0.57363`) and `ϝ ≥ 4.4582`:
  left side `≥ 413.18(1 + s/2 + s²/8)` against right `≤ 377.94 + 38.91s + 0.53s²`.

## Pricing (`scratchpad/mono/topstep_price.py`, floats; NOT the proof)

Condition (C) at the true `R`, `ϝ`: minimum ratio (left/right) `1.300` at `y = 10²⁵`, `w = 1/K`,
increasing in `y` (`1.66` at `10²⁶`, `4.47` at `10³⁰`). With the certified crude constants
(`R = 0.41415`, `e^γ ∈ [1.5, 1.95]`) the ratio crosses `1` near `t₀ = 10⁵`, which is why regime B
needs the sharper `R`: certified `0.5697` there against a requirement of `0.521`. The tightest
certified step is `u ≥ 7/9` (`9·12.9965 = 116.97` against `14·8.1757 = 114.46`).
-/

namespace Principia.Common.TernaryGoldbach.MO

open Set MeasureTheory

/-- `log 3 ≤ 1.0994749` (`3²⁹ ≤ 2⁴⁶`). -/
theorem log3_le : Real.log 3 ≤ 1.0994749 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 29) (by norm_num : (3 : ℝ) ^ 29 ≤ 2 ^ 46)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  have := Real.log_two_lt_d9
  generalize Real.log 3 = a at h ⊢
  generalize Real.log 2 = b at h this
  linarith

/-- `e^{2.3} ≤ 10.28` (`e^{0.3} ≤ 1.39`). -/
theorem exp23_le : Real.exp 2.3 ≤ 10.28 := by
  have h1 : Real.exp 2.3 = Real.exp 1 ^ 2 * Real.exp 0.3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have h2 := Real.abs_exp_sub_one_sub_id_le (show |(0.3 : ℝ)| ≤ 1 by norm_num)
  rw [abs_le] at h2
  have h3 : Real.exp 0.3 ≤ 1.39 := by nlinarith [h2.2]
  have he : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  rw [h1]
  have := mul_le_mul he.le h3 (Real.exp_pos _).le (by norm_num)
  linarith

/-- **The right side of condition (C) is at most a quadratic in `ℓ = log t`** for `t ≥ 2¹⁵`:
`L_t − 1.99(13/4·ϝ(t) + 13.6516) ≤ 0.528125ℓ² + 27.2ℓ + 11.3241` (`e^γ ≤ 1.95`,
`log log t ∈ [2.3, log 12 + ℓ/12 − 1]`). -/
theorem rhs_le (t : ℝ) (ht : 32768 ≤ t) :
    OL.lLc t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) ≤
      0.528125 * Real.log t ^ 2 + 27.2 * Real.log t + 11.3241 := by
  have ht0 : 0 < t := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl3 := log3_le
  have hlt : 10.39 ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 15) (le_trans (by norm_num) ht)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 2 = b at h hl2'
    linarith
  have hm : 2.3 ≤ Real.log (Real.log t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [exp23_le]
  have hm' : Real.log (Real.log t) ≤ 2 * Real.log 2 + Real.log 3 + Real.log t / 12 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log t / 12 by linarith)
    rw [Real.log_div (by linarith) (by norm_num),
      show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hEg := exp_gamma_le
  have hEg0 := Real.exp_pos Real.eulerMascheroniConstant
  have hF : MinSp.bigF t ≤ 1.95 * Real.log (Real.log t) + 2.50637 / 2.3 := by
    unfold MinSp.bigF
    have h1 := mul_le_mul_of_nonneg_right hEg (by linarith : (0 : ℝ) ≤ Real.log (Real.log t))
    have h2 : 2.50637 / Real.log (Real.log t) ≤ 2.50637 / 2.3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
    linarith
  unfold OL.lLc
  rw [OL.log_two_rpow_mul _ _ _ ht0, OL.log_two_rpow_mul _ _ _ ht0]
  have hK : 0 ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9 - 6.4675 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hF hK
  generalize Real.log (Real.log t) = m at hm hm' h1
  generalize MinSp.bigF t = F at h1 ⊢
  generalize Real.log 3 = a at hl3 hm'
  generalize Real.log t = l at hlt hm' h1 ⊢
  generalize Real.log 2 = b at hl2 hl2' hm' hK h1 ⊢
  have h2 := mul_le_mul_of_nonneg_right hm' hK
  nlinarith

/-- `√T₀·(1 + s/2 + s²/8) ≤ √t` for `0 < T₀ ≤ t`, `s = log t − log T₀`. -/
theorem sqrt_grow (t T0 : ℝ) (hT0 : 0 < T0) (h : T0 ≤ t) :
    Real.sqrt T0 * (1 + (Real.log t - Real.log T0) / 2 + (Real.log t - Real.log T0) ^ 2 / 8) ≤
      Real.sqrt t := by
  have ht0 : 0 < t := lt_of_lt_of_le hT0 h
  have hs : 0 ≤ Real.log t - Real.log T0 := by linarith [Real.log_le_log hT0 h]
  have e : Real.sqrt t = Real.sqrt T0 * Real.exp ((Real.log t - Real.log T0) / 2) := by
    rw [← sqrt_exp, ← Real.sqrt_mul hT0.le, ← Real.log_div ht0.ne' hT0.ne',
      Real.exp_log (div_pos ht0 hT0)]
    congr 1
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (Real.log t - Real.log T0) / 2 by linarith)
  nlinarith

/-- **Condition (C), regime A** (`t ≥ 1.5·10⁵`, any `R ≥ 0.41415`, `ϝ > 3.75`):
`L_t − 1.99(13/4·ϝ + 13.6516) ≤ √(2t)·R·√ϝ(t)`. -/
theorem condC_A (t R : ℝ) (ht : 1.5e5 ≤ t) (hR : 0.41415 ≤ R) :
    OL.lLc t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) ≤
      Real.sqrt (2 * t) * R * Real.sqrt (MinSp.bigF t) := by
  have hrhs := rhs_le t (by linarith)
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
  generalize OL.lLc t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) = RHS at hrhs ⊢
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
  have key : 0.528125 * (c + d) ^ 2 + 27.2 * (c + d) + 11.3241 ≤
      1.41421 * 0.41415 * 1.93649 * (387.29 * (1 + d / 2 + d ^ 2 / 8)) := by
    nlinarith
  nlinarith


/-- **Condition (C), regime B** (`5.9·10⁴ ≤ t ≤ 1.6·10⁵`, `R ≥ 0.5697`): `ϝ(t) ≥ 4.458` there
(`e^γ > 3/2`, `log log t ∈ [2.3, log 12]`). -/
theorem condC_B (t R : ℝ) (ht : 5.9e4 ≤ t) (ht' : t ≤ 1.6e5) (hR : 0.5697 ≤ R) :
    OL.lLc t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) ≤
      Real.sqrt (2 * t) * R * Real.sqrt (MinSp.bigF t) := by
  have ht0 : 0 < t := by linarith
  have hrhs := rhs_le t (by linarith)
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
  generalize OL.lLc t - 1.99 * (13 / 4 * MinSp.bigF t + 13.6516) = RHS at hrhs ⊢
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
  have key : 0.528125 * (c + d) ^ 2 + 27.2 * (c + d) + 11.3241 ≤
      1.41421 * 0.5697 * 2.1114 * (242.89 * (1 + d / 2 + d ^ 2 / 8)) := by
    nlinarith
  nlinarith

/-- `√t·gYL(Y,t) = A/√2 + L_t/√t + 3.2Y^{−1/6}√t`, `A = (R_{Y,2t}log 2t + 1/2)√ϝ(t) + 2.5`. -/
theorem sqrt_gYL (Y t : ℝ) (ht : 0 < t) :
    Real.sqrt t * OL.gYL Y t =
      ((MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5) * Real.sqrt (MinSp.bigF t) + 2.5) /
          Real.sqrt 2 + OL.lLc t / Real.sqrt t + 3.2 * Y ^ (-(1 : ℝ) / 6) * Real.sqrt t := by
  have hs := Real.sqrt_pos.2 ht
  have hs2 := Real.sqrt_pos.2 (two_pos : (0 : ℝ) < 2)
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  unfold OL.gYL
  rw [Real.sqrt_mul' 2 ht.le]
  generalize (MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5) * Real.sqrt (MinSp.bigF t) + 2.5 = A
  generalize OL.lLc t = L
  generalize 3.2 * Y ^ (-(1 : ℝ) / 6) = Z
  generalize Real.sqrt 2 = q at hs2 ⊢
  generalize Real.sqrt t = s at hs htt ⊢
  subst htt
  field_simp

/-- **The top step, algebra**: with `S₁ = ρS₀`, `1 ≤ ρ ≤ 1.005`, `ερ ≥ 2(ρ − 1)`, `q² = 2`, the
increase `A₁ − A₀ ≥ Rₛε`, `L₁ ≥ L₀ + Nε` and condition (C) `L₀ − 1.99N ≤ qS₀Rₛ` give
`A₀/q + L₀/S₀ + Z₀ ≤ A₁/q + L₁/(ρS₀) + Z₁`. -/
theorem top_core (A0 A1 L0 L1 S0 ρ ε Rs N q Z0 Z1 : ℝ) (hS0 : 0 < S0) (hρ1 : 1 ≤ ρ)
    (hρ2 : ρ ≤ 1.005) (hε : 2 * (ρ - 1) ≤ ε * ρ) (hq : 0 < q) (hq2 : q * q = 2)
    (hA : Rs * ε ≤ A1 - A0) (hRs : 0 ≤ Rs) (hN : 0 ≤ N) (hL : L0 + N * ε ≤ L1)
    (hC : L0 - 1.99 * N ≤ q * S0 * Rs) (hZ : Z0 ≤ Z1) :
    A0 / q + L0 / S0 + Z0 ≤ A1 / q + L1 / (ρ * S0) + Z1 := by
  have hρ0 : 0 < ρ := by linarith
  have hρS : 0 < ρ * S0 := mul_pos hρ0 hS0
  have hε0 : 0 ≤ ε := by nlinarith
  -- `(A₁ − A₀)/q ≥ Rₛεq/2`
  have h1 : Rs * ε * q / 2 ≤ (A1 - A0) / q := by
    rw [le_div_iff₀ hq]
    have e : Rs * ε * q / 2 * q = Rs * ε * (q * q) / 2 := by ring
    rw [e, hq2]
    linarith
  -- `L₁/(ρS₀) ≥ (L₀ + Nε)/(ρS₀)`
  have h2 : (L0 + N * ε) / (ρ * S0) ≤ L1 / (ρ * S0) := div_le_div_of_nonneg_right hL hρS.le
  -- the core: `Rₛεq/2 + (L₀ + Nε)/(ρS₀) − L₀/S₀ ≥ 0`
  have h3 : 0 ≤ Rs * ε * q / 2 + (L0 + N * ε) / (ρ * S0) - L0 / S0 := by
    have e : Rs * ε * q / 2 + (L0 + N * ε) / (ρ * S0) - L0 / S0 =
        (Rs * q * S0 * (ε * ρ) / 2 + L0 + N * ε - ρ * L0) / (ρ * S0) := by
      field_simp
      ring
    rw [e]
    refine div_nonneg ?_ hρS.le
    have k1 : Rs * q * S0 * (2 * (ρ - 1)) ≤ Rs * q * S0 * (ε * ρ) :=
      mul_le_mul_of_nonneg_left hε (by positivity)
    have k2 : 2 * (ρ - 1) * N ≤ ε * ρ * N := mul_le_mul_of_nonneg_right hε hN
    have k3 : ε * ρ * N ≤ ε * 1.005 * N := by
      have := mul_le_mul_of_nonneg_left hρ2 (mul_nonneg hε0 hN)
      nlinarith
    have k4 : (ρ - 1) * (L0 - 1.99 * N) ≤ (ρ - 1) * (q * S0 * Rs) :=
      mul_le_mul_of_nonneg_left hC (by linarith)
    have k5 : 0 ≤ (ρ - 1) * N := mul_nonneg (by linarith) hN
    nlinarith
  have e2 : (A1 - A0) / q = A1 / q - A0 / q := sub_div _ _ _
  linarith


/-- **`R_{Y,2t}` is non-decreasing in `t`** on `[1, Y^{1/3}/6]` (the inner ratio's numerator
`log 8t` grows, its denominator `log(9Y^{1/3}/(4.008t)) > 0` shrinks). -/
theorem rR_mono (Y t0 t1 : ℝ) (hY : 0 < Y) (h0 : 1 ≤ t0) (h01 : t0 ≤ t1)
    (h1 : t1 ≤ Y ^ ((1 : ℝ) / 3) / 6) : MinSp.rR Y (2 * t0) ≤ MinSp.rR Y (2 * t1) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Real.rpow_pos_of_pos hY _
  have ht0 : 0 < t0 := by linarith
  have ht1 : 0 < t1 := by linarith
  rw [← hc] at h1
  unfold MinSp.rR
  rw [← hc]
  have hd0 : 0 < 2.004 * (2 * t0) := by positivity
  have hd1 : 0 < 2.004 * (2 * t1) := by positivity
  have hb1 : 0 < Real.log (9 * c / (2.004 * (2 * t1))) :=
    Real.log_pos (by rw [one_lt_div hd1]; linarith)
  have hb : Real.log (9 * c / (2.004 * (2 * t1))) ≤ Real.log (9 * c / (2.004 * (2 * t0))) :=
    Real.log_le_log (div_pos (by positivity) hd1)
      (div_le_div_of_nonneg_left (by positivity) hd0 (by linarith))
  have ha : Real.log (4 * (2 * t0)) ≤ Real.log (4 * (2 * t1)) :=
    Real.log_le_log (by positivity) (by linarith)
  have ha0 : 0 ≤ Real.log (4 * (2 * t0)) := Real.log_nonneg (by linarith)
  generalize Real.log (9 * c / (2.004 * (2 * t1))) = b1 at hb1 hb ⊢
  generalize Real.log (9 * c / (2.004 * (2 * t0))) = b0 at hb ⊢
  generalize Real.log (4 * (2 * t0)) = a0 at ha ha0 ⊢
  generalize Real.log (4 * (2 * t1)) = a1 at ha ⊢
  have hu : a0 / (2 * b0) ≤ a1 / (2 * b1) :=
    calc a0 / (2 * b0) ≤ a0 / (2 * b1) := div_le_div_of_nonneg_left ha0 (by linarith) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right ha (by linarith)
  have hu0 : 0 ≤ a0 / (2 * b0) := div_nonneg ha0 (by linarith)
  have hl := Real.log_le_log (by linarith)
    (show 1 + a0 / (2 * b0) ≤ 1 + a1 / (2 * b1) by linarith)
  generalize Real.log (1 + a0 / (2 * b0)) = p at hl ⊢
  generalize Real.log (1 + a1 / (2 * b1)) = p' at hl ⊢
  linarith

/-- **`L_{t₁} ≥ L_{t₀} + (13/4·ϝ(t₀) + 13.6516)(log t₁ − log t₀)`** for `50 ≤ t₀ ≤ t₁` (`ϝ`
non-decreasing and non-negative, the bracket of `L` grows by `13/4·(log t₁ − log t₀)`). -/
theorem lLc_step (t0 t1 : ℝ) (h0 : 50 ≤ t0) (h01 : t0 ≤ t1) :
    OL.lLc t0 + (13 / 4 * MinSp.bigF t0 + 13.6516) * (Real.log t1 - Real.log t0) ≤
      OL.lLc t1 := by
  have ht0 : 0 < t0 := by linarith
  have ht1 : 0 < t1 := by linarith
  have hF := GS.bigF_mono t0 t1 h0 h01
  have hl2 := Real.log_pos one_lt_two
  have hlt1 : 0 ≤ Real.log t1 := Real.log_nonneg (by linarith)
  have hK1 : 0 ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log t1 + 80 / 9 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hF hK1
  unfold OL.lLc
  rw [OL.log_two_rpow_mul _ _ t0 ht0, OL.log_two_rpow_mul _ _ t0 ht0,
    OL.log_two_rpow_mul _ _ t1 ht1, OL.log_two_rpow_mul _ _ t1 ht1]
  have e : MinSp.bigF t0 * (7 / 4 * Real.log 2 + 13 / 4 * Real.log t0 + 80 / 9) +
      (1.7984 * Real.log 2 + 13.6516 * Real.log t0) + 22.7538 +
      (13 / 4 * MinSp.bigF t0 + 13.6516) * (Real.log t1 - Real.log t0) =
      MinSp.bigF t0 * (7 / 4 * Real.log 2 + 13 / 4 * Real.log t1 + 80 / 9) +
        (1.7984 * Real.log 2 + 13.6516 * Real.log t1) + 22.7538 := by ring
  rw [e]
  linarith

/-- **The increase of `A = (R_{Y,2t}log 2t + 1/2)√ϝ(t) + 2.5`** from `t₀` to `t₁`:
`A₁ − A₀ ≥ R₀√ϝ₀·(log t₁ − log t₀)` (`R`, `ϝ` non-decreasing). -/
theorem topA (Y t0 t1 : ℝ) (hY : 0 < Y) (h0 : 1000 ≤ t0) (h01 : t0 ≤ t1)
    (h1 : t1 ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0) * (Real.log t1 - Real.log t0) ≤
      ((MinSp.rR Y (2 * t1) * Real.log (2 * t1) + 0.5) * Real.sqrt (MinSp.bigF t1) + 2.5) -
        ((MinSp.rR Y (2 * t0) * Real.log (2 * t0) + 0.5) * Real.sqrt (MinSp.bigF t0) + 2.5) := by
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
  have k0 : 0 ≤ MinSp.rR Y (2 * t0) * Real.log (2 * t1) + 0.5 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.rR Y (2 * t0)) hx1
    linarith
  have k2 : (MinSp.rR Y (2 * t0) * Real.log (2 * t1) + 0.5) * Real.sqrt (MinSp.bigF t0) ≤
      (MinSp.rR Y (2 * t1) * Real.log (2 * t1) + 0.5) * Real.sqrt (MinSp.bigF t1) :=
    mul_le_mul (by linarith) hsF01 hsF0 (by linarith)
  have e : (MinSp.rR Y (2 * t0) * Real.log (2 * t1) + 0.5) * Real.sqrt (MinSp.bigF t0) -
      (MinSp.rR Y (2 * t0) * Real.log (2 * t0) + 0.5) * Real.sqrt (MinSp.bigF t0) =
      MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0) *
        (Real.log (2 * t1) - Real.log (2 * t0)) := by ring
  rw [hx] at e
  linarith

/-- **`ρ = √t₁/√t₀`**: `√t₁ = ρ√t₀`, `1 ≤ ρ ≤ 1.005` and `(log t₁ − log t₀)ρ ≥ 2(ρ − 1)` for
`0 < t₀ ≤ t₁ ≤ 1.01t₀` (`log ρ ≥ 1 − 1/ρ`). -/
theorem rho_facts (t0 t1 : ℝ) (ht0 : 0 < t0) (h01 : t0 ≤ t1) (hρ : t1 ≤ 1.01 * t0) :
    ∃ ρ : ℝ, Real.sqrt t1 = ρ * Real.sqrt t0 ∧ 1 ≤ ρ ∧ ρ ≤ 1.005 ∧
      2 * (ρ - 1) ≤ (Real.log t1 - Real.log t0) * ρ := by
  have ht1 : 0 < t1 := by linarith
  have hS0 : 0 < Real.sqrt t0 := Real.sqrt_pos.2 ht0
  have hS1 : 0 < Real.sqrt t1 := Real.sqrt_pos.2 ht1
  refine ⟨Real.sqrt t1 / Real.sqrt t0, by field_simp, ?_, ?_, ?_⟩
  · rw [one_le_div hS0]
    exact Real.sqrt_le_sqrt h01
  · rw [div_le_iff₀ hS0]
    have h1 : Real.sqrt t1 ≤ Real.sqrt ((1.005 * Real.sqrt t0) ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [mul_pow, Real.sq_sqrt ht0.le]
      linarith
    rwa [Real.sqrt_sq (by positivity)] at h1
  · have hρ0 : 0 < Real.sqrt t1 / Real.sqrt t0 := div_pos hS1 hS0
    have hlr : Real.log (Real.sqrt t1 / Real.sqrt t0) = (Real.log t1 - Real.log t0) / 2 := by
      rw [Real.log_div hS1.ne' hS0.ne', Real.log_sqrt ht1.le, Real.log_sqrt ht0.le]
      ring
    have h1' := Real.one_sub_inv_le_log_of_pos hρ0
    rw [hlr] at h1'
    generalize Real.sqrt t1 / Real.sqrt t0 = ρ at hρ0 h1' ⊢
    have : ρ * (1 - ρ⁻¹) = ρ - 1 := by field_simp
    nlinarith

/-- **The top step at one scale**: for `1000 ≤ t₀ ≤ t₁ ≤ Y^{1/3}/6`, `t₁ ≤ 1.01t₀`, condition (C)
at `t₀` gives `√t₀·gYL(Y,t₀) ≤ √t₁·gYL(Y,t₁)`. `A = (Rx + 1/2)√ϝ + 2.5` grows by at least
`R₀√ϝ₀·ε` (`topA`, `ε = log t₁ − log t₀`), `L` grows by at least `(13/4·ϝ₀ + 13.6516)ε`
(`lLc_step`), the `Y^{−1/6}√t` term grows; `top_core` closes with `ρ = √(t₁/t₀)`
(`rho_facts`). -/
theorem topH (Y t0 t1 : ℝ) (hY : 0 < Y) (h0 : 1000 ≤ t0) (h01 : t0 ≤ t1)
    (h1 : t1 ≤ Y ^ ((1 : ℝ) / 3) / 6) (hρ : t1 ≤ 1.01 * t0)
    (hC : OL.lLc t0 - 1.99 * (13 / 4 * MinSp.bigF t0 + 13.6516) ≤
      Real.sqrt (2 * t0) * MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0)) :
    Real.sqrt t0 * OL.gYL Y t0 ≤ Real.sqrt t1 * OL.gYL Y t1 := by
  have ht0 : 0 < t0 := by linarith
  have ht1 : 0 < t1 := by linarith
  have hR0 := GS.rR_ge Y (2 * t0) hY (by linarith) (by linarith)
  have hF0 := GS.bigF_gt t0 (by linarith)
  have hL := lLc_step t0 t1 (by linarith) h01
  have hA := topA Y t0 t1 hY h0 h01 h1
  have hsF0 : 0 ≤ Real.sqrt (MinSp.bigF t0) := Real.sqrt_nonneg _
  have hS0 : 0 < Real.sqrt t0 := Real.sqrt_pos.2 ht0
  have hq : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨ρ, hS1ρ, hρ1, hρ2, hε⟩ := rho_facts t0 t1 ht0 h01 hρ
  have hC' : OL.lLc t0 - 1.99 * (13 / 4 * MinSp.bigF t0 + 13.6516) ≤
      Real.sqrt 2 * Real.sqrt t0 * (MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0)) := by
    rw [Real.sqrt_mul' 2 ht0.le] at hC
    linarith [mul_assoc (Real.sqrt 2 * Real.sqrt t0) (MinSp.rR Y (2 * t0))
      (Real.sqrt (MinSp.bigF t0))]
  have hZ : 3.2 * Y ^ (-(1 : ℝ) / 6) * Real.sqrt t0 ≤ 3.2 * Y ^ (-(1 : ℝ) / 6) * Real.sqrt t1 :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h01) (by positivity)
  have key := top_core _ _ (OL.lLc t0) (OL.lLc t1) (Real.sqrt t0) ρ (Real.log t1 - Real.log t0)
    (MinSp.rR Y (2 * t0) * Real.sqrt (MinSp.bigF t0)) (13 / 4 * MinSp.bigF t0 + 13.6516)
    (Real.sqrt 2) _ _ hS0 hρ1 hρ2 hε hq hq2 hA (mul_nonneg (by linarith) hsF0) (by linarith)
    (by linarith) hC' hZ
  rw [sqrt_gYL Y t0 ht0, sqrt_gYL Y t1 ht1, hS1ρ]
  rw [hS1ρ] at key
  exact key


/-- `log v ≤ 2.8720637 + v/48` (`log(v/48) ≤ v/48 − 1`, `log 48 ≤ 3.8720637`). -/
theorem log_le_48 (v : ℝ) (hv : 0 < v) : Real.log v ≤ 2.8720637 + v / 48 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < v / 48 by positivity)
  rw [Real.log_div hv.ne' (by norm_num), show (48 : ℝ) = 2 ^ 4 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h
  push_cast at h
  have := Real.log_two_lt_d9
  have := log3_le
  generalize Real.log 3 = a at *
  generalize Real.log 2 = b at *
  linarith

/-- `log v ≤ 3.1588832 + v/64` (`log 64 = 6 log 2`). -/
theorem log_le_64 (v : ℝ) (hv : 0 < v) : Real.log v ≤ 3.1588832 + v / 64 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < v / 64 by positivity)
  rw [Real.log_div hv.ne' (by norm_num), show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow] at h
  push_cast at h
  have := Real.log_two_lt_d9
  generalize Real.log 2 = b at *
  linarith

/-- **The inner ratio of `R` in regime B**: for `v ∈ [46.41, 60)`-type data the cube of
`X = 9Y^{1/3}/(4.008t)` at `Y = wv¹⁵`, `t = wR₀` is at most `12100λ²v³` (`λ = log v`),
from `λw ≥ 2/15` and `R₀ ≥ 0.37499v⁴`. -/
theorem regB_cube (v w R0 lv : ℝ) (hv : 0 < v) (hw : 0 < w) (hlw : 2 / 15 ≤ lv * w)
    (hR0 : 0.37499 * v ^ 4 ≤ R0) :
    (9 * (w * v ^ 15) ^ ((1 : ℝ) / 3) / (2.004 * (2 * (w * R0)))) ^ 3 ≤ 12100 * lv ^ 2 * v ^ 3 := by
  have hR0p : 0 < R0 := lt_of_lt_of_le (by positivity) hR0
  have hc3 : ((w * v ^ 15) ^ ((1 : ℝ) / 3)) ^ 3 = w * v ^ 15 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hD : 0 < 2.004 * (2 * (w * R0)) := by positivity
  rw [div_pow, mul_pow, hc3, div_le_iff₀ (pow_pos hD 3)]
  have h1 : 4 / 225 ≤ (lv * w) ^ 2 := by nlinarith
  have h2 : 0.05273 * v ^ 12 ≤ R0 ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hR0 3
    have e : (0.37499 * v ^ 4) ^ 3 = 0.37499 ^ 3 * v ^ 12 := by ring
    rw [e] at this
    have : (0.05273 : ℝ) ≤ 0.37499 ^ 3 := by norm_num
    nlinarith [pow_pos hv 12]
  have h3 : 4 / 225 * (0.05273 * v ^ 12) ≤ (lv * w) ^ 2 * R0 ^ 3 :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have e : 12100 * lv ^ 2 * v ^ 3 * (2.004 * (2 * (w * R0))) ^ 3 =
      12100 * 4.008 ^ 3 * (w * v ^ 3) * ((lv * w) ^ 2 * R0 ^ 3) := by ring
  rw [e]
  have h4 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ 12100 * 4.008 ^ 3 * (w * v ^ 3))
  have e2 : 12100 * 4.008 ^ 3 * (w * v ^ 3) * (4 / 225 * (0.05273 * v ^ 12)) =
      (12100 * 4.008 ^ 3 * 4 / 225 * 0.05273) * (w * v ^ 15) := by ring
  rw [e2] at h4
  have h5 : (729 : ℝ) ≤ 12100 * 4.008 ^ 3 * 4 / 225 * 0.05273 := by norm_num
  have h6 : 729 * (w * v ^ 15) ≤ (12100 * 4.008 ^ 3 * 4 / 225 * 0.05273) * (w * v ^ 15) :=
    mul_le_mul_of_nonneg_right h5 (by positivity)
  have e3 : (9 : ℝ) ^ 3 * (w * v ^ 15) = 729 * (w * v ^ 15) := by norm_num
  rw [e3]
  linarith

/-- **`R_{Y,2t} ≥ 0.5697` in regime B**: at `Y = wv¹⁵`, `t = wR₀` with `λw ≥ 2/15`
(`w ≥ 1/K`), `R₀ ≥ 0.37499v⁴`, `5.9·10⁴ ≤ t < 1.5·10⁵`, `t ≤ Y^{1/3}/6`: then `v < 60`,
`log 8t ≥ 14 log 2 + 3 log 3 ≥ 12.9965`, `log X ≤ 8.1758` (`regB_cube`,
`log λ ≤ 2 log 2 − 1 + λ/4`), so the ratio `u ≥ 7/9` and `log(1 + u) ≥ log(16/9)`. -/
theorem rR_regB (v w R0 : ℝ) (hv : 46.41 ≤ v) (hw : 0 < w) (hlw : 2 / 15 ≤ Real.log v * w)
    (hR0 : 0.37499 * v ^ 4 ≤ R0) (ht : w * R0 < 1.5e5) (ht0 : 5.9e4 ≤ w * R0)
    (htop : w * R0 ≤ (w * v ^ 15) ^ ((1 : ℝ) / 3) / 6) :
    0.5697 ≤ MinSp.rR (w * v ^ 15) (2 * (w * R0)) := by
  have hv0 : 0 < v := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl3 := log3_le
  have hl3' := log3_ge
  have hlv0 : 0 < Real.log v := Real.log_pos (by linarith)
  -- `v < 60`, hence `λ ≤ 4.0963832`
  have hlv64 := log_le_64 v hv0
  have hv60 : v < 60 := by
    by_contra h
    have h60 : 60 ≤ v := le_of_not_gt h
    have hR0p : 0 < R0 := lt_of_lt_of_le (by positivity) hR0
    have h1 : 2 / 15 * R0 ≤ Real.log v * w * R0 := mul_le_mul_of_nonneg_right hlw hR0p.le
    have h2 : Real.log v * w * R0 < Real.log v * 1.5e5 := by
      rw [mul_assoc]
      exact mul_lt_mul_of_pos_left ht hlv0
    have h3 : v ^ 4 ≥ 216000 * v := by nlinarith [pow_le_pow_left₀ (by norm_num) h60 3]
    nlinarith
  have hlv : Real.log v ≤ 4.0963832 := by linarith
  -- the numerator `log 8t ≥ 12.9965`
  have hA : 12.9965 ≤ Real.log (4 * (2 * (w * R0))) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 14 * 3 ^ 3)
      (show (2 : ℝ) ^ 14 * 3 ^ 3 ≤ 4 * (2 * (w * R0)) by norm_num; linarith)
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at h
    push_cast at h
    generalize Real.log (4 * (2 * (w * R0))) = A at h ⊢
    generalize Real.log 3 = a at h hl3'
    generalize Real.log 2 = b at h hl2'
    linarith
  -- the denominator `log X ≤ 8.1758`, `X ≥ 13.47`
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 9 * (w * v ^ 15) ^ ((1 : ℝ) / 3) / (2.004 * (2 * (w * R0))) :=
    ⟨_, rfl⟩
  have hD : 0 < 2.004 * (2 * (w * R0)) := by positivity
  have hX1 : 13 ≤ X := by
    rw [hX, le_div_iff₀ hD]
    linarith
  have hcube := regB_cube v w R0 (Real.log v) hv0 hw hlw hR0
  rw [← hX] at hcube
  have hlogX : 3 * Real.log X ≤ Real.log 12100 + 2 * Real.log (Real.log v) + 3 * Real.log v := by
    have h := Real.log_le_log (by positivity) hcube
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have h12100 : Real.log 12100 ≤ 9.4172412 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 12100)
      (by norm_num : (12100 : ℝ) ≤ 2 ^ 12 * 3)
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h
    push_cast at h
    generalize Real.log 12100 = c at h ⊢
    generalize Real.log 3 = a at h hl3
    generalize Real.log 2 = b at h hl2
    linarith
  have hll : Real.log (Real.log v) ≤ 0.3862944 + Real.log v / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log v / 4 by positivity)
    rw [Real.log_div hlv0.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    push_cast at h
    generalize Real.log (Real.log v) = m at h ⊢
    generalize Real.log 2 = b at h hl2
    linarith
  have hB : Real.log X ≤ 8.17573 := by
    generalize Real.log (Real.log v) = m at hlogX hll
    generalize Real.log 12100 = c at hlogX h12100
    generalize Real.log v = l at hlogX hll hlv
    linarith
  have hB0 : 0 < Real.log X := Real.log_pos (by linarith)
  -- `u ≥ 7/9`, `log(1 + u) ≥ log(16/9) ≥ 0.5736388`
  have hu : 7 / 9 ≤ Real.log (4 * (2 * (w * R0))) / (2 * Real.log X) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h169 : 0.5736388 ≤ Real.log (16 / 9) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num,
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    generalize Real.log 3 = a at hl3
    generalize Real.log 2 = b at hl2'
    linarith
  have hmono : Real.log (16 / 9) ≤
      Real.log (1 + Real.log (4 * (2 * (w * R0))) / (2 * Real.log X)) :=
    Real.log_le_log (by norm_num) (by linarith)
  unfold MinSp.rR
  rw [← hX]
  generalize Real.log (1 + Real.log (4 * (2 * (w * R0))) / (2 * Real.log X)) = p at hmono ⊢
  generalize Real.log (16 / 9) = q at h169 hmono
  linarith


/-- `(v¹⁵)^a = vⁿ` when `15a = n`, `v > 0`. -/
theorem pow15_rpow (v : ℝ) (hv : 0 < v) (a : ℝ) (n : ℕ) (h : 15 * a = n) :
    (v ^ 15) ^ a = v ^ n := by
  rw [← Real.rpow_natCast v 15, ← Real.rpow_mul hv.le, ← Real.rpow_natCast,
    show ((15 : ℕ) : ℝ) * a = n by push_cast; linarith]

/-- **The scale of `TopStepL`**: `y ≥ 10²⁵` is `v¹⁵` with `v ≥ 46.41` (`46.41¹⁵ ≤ 10²⁵`). -/
theorem scale_data (y : ℝ) (hy : 10 ^ 25 ≤ y) : ∃ v : ℝ, 0 < v ∧ y = v ^ 15 ∧ 46.41 ≤ v := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  refine ⟨y ^ ((1 : ℝ) / 15), Real.rpow_pos_of_pos hy0 _, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  · exact le_rpow_inv 46.41 y 15 (by norm_num) (by norm_num) (le_trans (by norm_num) hy)

/-- **The top level `R₀ = ⌊r₁⌋` at `r₁ = (3/8)v⁴`, `v ≥ 46.41`**: `R₀ ≥ 0.37499v⁴ ≥ 1.5·10⁵`,
`r₁ ≤ 1.01R₀`, `R₀ ≥ 7500 log v` (so `1000/R₀ ≤ 1/K`) and `R₀/K ≥ 5.9·10⁴`
(`log v ≤ 2.8720637 + v/48`). -/
theorem top_data (v : ℝ) (hv : 46.41 ≤ v) :
    0.37499 * v ^ 4 ≤ (⌊3 / 8 * v ^ 4⌋₊ : ℝ) ∧ (⌊3 / 8 * v ^ 4⌋₊ : ℝ) ≤ 3 / 8 * v ^ 4 ∧
      3 / 8 * v ^ 4 ≤ 1.01 * (⌊3 / 8 * v ^ 4⌋₊ : ℝ) ∧ 1.5e5 ≤ (⌊3 / 8 * v ^ 4⌋₊ : ℝ) ∧
      7500 * Real.log v ≤ (⌊3 / 8 * v ^ 4⌋₊ : ℝ) ∧
      5.9e4 * (15 * Real.log v) ≤ 2 * (⌊3 / 8 * v ^ 4⌋₊ : ℝ) := by
  have hv0 : 0 < v := by linarith
  have hr0 : 0 ≤ 3 / 8 * v ^ 4 := by positivity
  have hfl := Nat.floor_le hr0
  have hlt := Nat.lt_floor_add_one (3 / 8 * v ^ 4)
  have h4 : 46.41 ^ 3 * v ≤ v ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hv 3
    nlinarith
  have hv4 : (4.6e6 : ℝ) ≤ v ^ 4 := by nlinarith
  have hlog := log_le_48 v hv0
  have hR0 : 0.37499 * v ^ 4 ≤ (⌊3 / 8 * v ^ 4⌋₊ : ℝ) := by linarith
  refine ⟨hR0, hfl, by linarith, by linarith, by nlinarith, by nlinarith⟩

/-- **The top step at a scale `w ∈ [1/K, 1]`**: with `Y = wv¹⁵`, `t₀ = wR₀`, `t₁ = wr₁`:
`√t₀·gYL(Y,t₀) ≤ √t₁·gYL(Y,t₁)` (`topH`; condition (C) from `condC_A` when `t₀ ≥ 1.5·10⁵`,
else from `condC_B` with `rR_regB`). -/
theorem conf_low (v w R0 : ℝ) (hv : 46.41 ≤ v) (hy : (10 : ℝ) ^ 25 ≤ v ^ 15)
    (hR0 : 0.37499 * v ^ 4 ≤ R0)
    (hR0u : R0 ≤ 3 / 8 * v ^ 4)
    (hk : 5.9e4 * (15 * Real.log v) ≤ 2 * R0) (hw : 1 / MinSp.kK (v ^ 15) ≤ w) (hw1 : w ≤ 1) :
    Real.sqrt (w * R0) * OL.gYL (w * v ^ 15) (w * R0) ≤
      Real.sqrt (w * (3 / 8 * v ^ 4)) * OL.gYL (w * v ^ 15) (w * (3 / 8 * v ^ 4)) := by
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
  refine topH (w * v ^ 15) (w * R0) (w * (3 / 8 * v ^ 4)) hY0 (by linarith) h01 htop hρw ?_
  have hRg := GS.rR_ge (w * v ^ 15) (2 * (w * R0)) hY0 (by linarith) (by linarith)
  by_cases h : 1.5e5 ≤ w * R0
  · exact condC_A _ _ h hRg
  · exact condC_B _ _ ht0 (by linarith)
      (rR_regB v w R0 hv hw0 hlw hR0 (lt_of_not_ge h) ht0 (le_trans h01 htop))

/-- **The top step at a scale `w > 1`**: `√R₀·gYL(wv¹⁵, R₀) ≤ √r₁·gYL(wv¹⁵, r₁)` (`topH`;
`R₀ ≥ 1.5·10⁵`, regime A). -/
theorem conf_high (v w R0 : ℝ) (hv : 46.41 ≤ v) (hy : (10 : ℝ) ^ 25 ≤ v ^ 15)
    (hR0u : R0 ≤ 3 / 8 * v ^ 4)
    (hρ : 3 / 8 * v ^ 4 ≤ 1.01 * R0) (hR0b : 1.5e5 ≤ R0) (hw : 1 < w) :
    Real.sqrt R0 * OL.gYL (w * v ^ 15) R0 ≤
      Real.sqrt (3 / 8 * v ^ 4) * OL.gYL (w * v ^ 15) (3 / 8 * v ^ 4) := by
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
  exact topH (w * v ^ 15) R0 (3 / 8 * v ^ 4) hY0 (by linarith) hR0u htop hρ
    (condC_A _ _ hR0b hRg)

/-- **[TopStepL] PROVED for every `φ ≥ 0` in `L¹(0,∞)`**: at `y = v¹⁵ ≥ 10²⁵` both cutoffs are
`1/K` (`R₀ ≥ 7500 log v`), so the sliver `∫_{1/K}^{1/K}|φ|` vanishes at `⌊r₁⌋` and at `r₁`, and
`√r·g̃(y,r)|φ|₁` is the integral of `√r·gYL(wy, min(w,1)r)φ(w)`, which does not decrease from
`⌊r₁⌋` to `r₁` pointwise in `w` (`conf_low`, `conf_high`). -/
theorem topStepL_of (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Ioi 0)) : OS.TopStepL φ := by
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
  have hint0 := GS.gtlInt φ hφi y hy (⌊3 / 8 * v ^ 4⌋₊ : ℝ) (by linarith) (by rw [hr1]; exact hR0u)
  have hint1 := GS.gtlInt φ hφi y hy (3 / 8 * v ^ 4) (by linarith) hr1.symm.le
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
  unfold OL.gTL
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
    have hc := conf_low v w R0 hv (hyv ▸ hy) hR0 hR0u hk59 hwk hw.2
    rw [Real.sqrt_mul hw0.le, Real.sqrt_mul hw0.le, mul_assoc, mul_assoc] at hc
    have hc' := le_of_mul_le_mul_left hc (Real.sqrt_pos.2 hw0)
    rw [← hyv] at hc'
    have := mul_le_mul_of_nonneg_right hc' (hφ0 w hw0.le)
    linarith [mul_assoc (Real.sqrt R0) (OL.gYL (w * y) (w * R0)) (φ w),
      mul_assoc (Real.sqrt (3 / 8 * v ^ 4)) (OL.gYL (w * y) (w * (3 / 8 * v ^ 4))) (φ w)]
  · refine setIntegral_mono_on (hint0.2.const_mul _) (hint1.2.const_mul _) measurableSet_Ioi
      fun w (hw : 1 < w) => ?_
    have hc := conf_high v w R0 hv (hyv ▸ hy) hR0u hρ hR0b hw
    rw [← hyv] at hc
    have := mul_le_mul_of_nonneg_right hc (hφ0 w (by linarith))
    linarith [mul_assoc (Real.sqrt R0) (OL.gYL (w * y) R0) (φ w),
      mul_assoc (Real.sqrt (3 / 8 * v ^ 4)) (OL.gYL (w * y) (3 / 8 * v ^ 4)) (φ w)]

/-- **[TopStepL] on Helfgott's `φ`, PROVED** (`topStepL_of`). -/
theorem topStepL_helf : OS.TopStepL HW.phi :=
  topStepL_of HW.phi (fun t _ => HW.phi_nonneg t) MinSp.phi_integrableOn

end Principia.Common.TernaryGoldbach.MO
