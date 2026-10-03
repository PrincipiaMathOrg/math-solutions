/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopSpineP
import Principia.Common.TernaryGoldbach.MonoLinks
import Principia.Common.TernaryGoldbach.CoprarLProof

set_option autoImplicit false

/-!
# The proved numeric links carried across to `(c05, C) = (0.811, 45.7575)`

`gYP c05 C = gYL + dP c05 C` (`OP.gYP_eq`) with
`dP(r) = (c05 − 0.5)√ϝ(r)/√(2r) + (C − 22.7538)/r ≥ 0` for `c05 ≥ 0.5`, `C ≥ 22.7538`. So:

* **links where a LARGER `g` is WEAKER transfer by monotonicity** from the proved `L` versions:
  - `hLeGP_of` : `GS.HLeG → GSP.HLeGP c05 C` (`h′(Y) ≤ gYL·Y ≤ gYP·Y`); `hLeGP` from `MO.hLeG`;
  - `coprarP_of_L` : `OL.CoprarL → OP.CoprarP c05 C` through `gTL_le_gTP` (`g̃_L ≤ g̃_P`
    pointwise under the integrals, both integrable: `GS.gtlInt`, `GSP.gtlIntP`);
    `coprarP_of_R` from `CP.coprarL_of_R` (the retyped major arcs);
* **links that need `g` ANTITONE transfer because `dP` is antitone on `[175, ∞)`** (`dP_anti`):
  `ϝ(r)/r = qL(log r)e^{−0.86 log r}` with `MO.qL_anti` (`bigF_div_anti`), and `1/r`:
  - `gYMonoP_of` : `GS.GYMono → GSP.GYMonoP c05 C`; `gYMonoP` from `MO.gYMono`;
  - `gtMonoP_of` (generated from `MO.gtMonoL_of`): `GYMonoP` plus the sliver swap
    `gYP(Y, 1000) ≤ 1.04488` (`gYP_1000_le`: `gYL(Y,1000) ≤ 0.6` (`MO.gYL_1000_le`) and
    `dP(1000) ≤ 0.311·4/44 + 23.0037/1000 ≤ 0.0514`); `gtMonoP_helf`.

`TopStepP` is re-proved, not transferred (`MonoTopP.lean`): `dP`'s `(C − 22.7538)/r` summand makes
`√r·g` DEcrease, so it does not follow from `TopStepL`.
-/

namespace Principia.Common.TernaryGoldbach.MOP

open Set MeasureTheory
open Principia.Common.TernaryGoldbach.OP

/-! ## (1) `dP` is antitone on `[175, ∞)` -/

/-- `ϝ(r)/r = qL(log r)·e^{−0.86 log r}` for `r > 0` (`ϝ(e^ℓ) = fL(ℓ)`, `qL = fL·e^{−0.14ℓ}`). -/
theorem bigF_div_eq (r : ℝ) (hr : 0 < r) :
    MinSp.bigF r / r = MO.qL (Real.log r) * Real.exp (-0.86 * Real.log r) := by
  have e1 : MinSp.bigF r = MO.fL (Real.log r) := rfl
  have e2 : Real.exp (-0.14 * Real.log r) * Real.exp (-0.86 * Real.log r) = r⁻¹ := by
    rw [← Real.exp_add, show -0.14 * Real.log r + -0.86 * Real.log r = -Real.log r by ring,
      Real.exp_neg, Real.exp_log hr]
  unfold MO.qL
  rw [e1, mul_assoc, e2, div_eq_mul_inv]

/-- **`ϝ(r)/r` is antitone on `[175, ∞)`** (`MO.qL_anti` at `log r ≥ log 175 ≥ 5`). -/
theorem bigF_div_anti (r r' : ℝ) (hr : 175 ≤ r) (hrr : r ≤ r') :
    MinSp.bigF r' / r' ≤ MinSp.bigF r / r := by
  have hr0 : 0 < r := by linarith
  have hr'0 : 0 < r' := by linarith
  have hl5 : 5 ≤ Real.log r := le_trans MO.log175_ge (Real.log_le_log (by norm_num) hr)
  have hll : Real.log r ≤ Real.log r' := Real.log_le_log hr0 hrr
  rw [bigF_div_eq r hr0, bigF_div_eq r' hr'0]
  have hQ : MO.qL (Real.log r') ≤ MO.qL (Real.log r) :=
    MO.qL_anti (Real.log r) (Real.log r') hl5 ⟨le_rfl, hll⟩ ⟨hll, le_rfl⟩ hll
  have hQ0 : 0 ≤ MO.qL (Real.log r') := by
    unfold MO.qL
    exact mul_nonneg (MO.fL_nonneg _ (by linarith)) (Real.exp_pos _).le
  have hE : Real.exp (-0.86 * Real.log r') ≤ Real.exp (-0.86 * Real.log r) :=
    Real.exp_le_exp.2 (by linarith)
  exact mul_le_mul hQ hE (Real.exp_pos _).le (le_trans hQ0 hQ)

/-- **`√ϝ(r)/√(2r)` is antitone on `[175, ∞)`**. -/
theorem sqrtF_anti (r r' : ℝ) (hr : 175 ≤ r) (hrr : r ≤ r') :
    Real.sqrt (MinSp.bigF r') / Real.sqrt (2 * r') ≤
      Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) := by
  rw [← Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ 2 * r'),
    ← Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ 2 * r)]
  apply Real.sqrt_le_sqrt
  have h := bigF_div_anti r r' hr hrr
  have e1 : MinSp.bigF r' / (2 * r') = MinSp.bigF r' / r' / 2 := by ring
  have e2 : MinSp.bigF r / (2 * r) = MinSp.bigF r / r / 2 := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- **`dP c05 C` is antitone on `[175, ∞)`** for `c05 ≥ 0.5`, `C ≥ 22.7538`. -/
theorem dP_anti (c05 C r r' : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (hr : 175 ≤ r)
    (hrr : r ≤ r') : dP c05 C r' ≤ dP c05 C r := by
  have hr0 : 0 < r := by linarith
  have h1 := sqrtF_anti r r' hr hrr
  have h2 : 1 / r' ≤ 1 / r := one_div_le_one_div_of_le hr0 hrr
  have k1 : (c05 - 0.5) * (Real.sqrt (MinSp.bigF r') / Real.sqrt (2 * r')) ≤
      (c05 - 0.5) * (Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have k2 : (C - 22.7538) * (1 / r') ≤ (C - 22.7538) * (1 / r) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  unfold dP
  calc (c05 - 0.5) * Real.sqrt (MinSp.bigF r') / Real.sqrt (2 * r') + (C - 22.7538) / r'
      = (c05 - 0.5) * (Real.sqrt (MinSp.bigF r') / Real.sqrt (2 * r')) +
          (C - 22.7538) * (1 / r') := by ring
    _ ≤ (c05 - 0.5) * (Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r)) +
          (C - 22.7538) * (1 / r) := add_le_add k1 k2
    _ = (c05 - 0.5) * Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) + (C - 22.7538) / r := by
          ring

/-! ## (2) `GYMonoP` and `HLeGP` transferred -/

/-- **[GYMonoP] from [GYMono]**: `gYP = gYL + dP`, both antitone on `[175, Y^{1/3}/6]`. -/
theorem gYMonoP_of (c05 C : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (hmo : GS.GYMono) :
    GSP.GYMonoP c05 C := by
  intro Y hY r hr r' hr' hrr'
  rw [gYP_eq, gYP_eq]
  have h1 := hmo Y hY hr hr' hrr'
  have h2 := dP_anti c05 C r r' hc hC hr.1 hrr'
  linarith

/-- **[GYMonoP] at `(0.811, 45.7575)`, PROVED** (`MO.gYMono`). -/
theorem gYMonoP : GSP.GYMonoP 0.811 45.7575 :=
  gYMonoP_of 0.811 45.7575 (by norm_num) (by norm_num) MO.gYMono

/-- **[HLeGP] from [HLeG]**: `h′(Y) ≤ gYL(Y, r₁)Y ≤ gYP(Y, r₁)Y`. -/
theorem hLeGP_of (c05 C : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (hhl : GS.HLeG) :
    GSP.HLeGP c05 C := by
  intro Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have h1 := hhl Y hY
  have hr : 0 ≤ MinSp.r1y Y := OS.r1y_nonneg Y hY0.le
  have h2 := mul_le_mul_of_nonneg_right (gYL_le_gYP c05 C Y (MinSp.r1y Y) hc hC hr) hY0.le
  linarith

/-- **[HLeGP] at `(0.811, 45.7575)`, PROVED** (`MO.hLeG`). -/
theorem hLeGP : GSP.HLeGP 0.811 45.7575 :=
  hLeGP_of 0.811 45.7575 (by norm_num) (by norm_num) MO.hLeG

/-! ## (3) `GTMonoP` -/

/-- `ϝ(1000) ≤ 15` (`log 1000 ∈ [6.2, 7]`, `log log 1000 ∈ [1, 6]`, `e^γ ≤ 1.95`). -/
theorem bigF_1000_le : MinSp.bigF 1000 ≤ 15 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have h1 : Real.log 1000 ≤ 7 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1000) (by norm_num : (1000 : ℝ) ≤ 2 ^ 10)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 1000 = x at h ⊢
    generalize Real.log 2 = b at h hl2
    linarith
  have h2 : 6.2 ≤ Real.log 1000 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 9) (by norm_num : (2 : ℝ) ^ 9 ≤ 1000)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 1000 = x at h ⊢
    generalize Real.log 2 = b at h hl2'
    linarith
  have hll1 : 1 ≤ Real.log (Real.log 1000) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hll2 : Real.log (Real.log 1000) ≤ Real.log 1000 - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hEg := MO.exp_gamma_le
  unfold MinSp.bigF
  have k1 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 1000) ≤ 1.95 * 6 :=
    mul_le_mul hEg (by linarith) (by linarith) (by norm_num)
  have k2 : 2.50637 / Real.log (Real.log 1000) ≤ 2.50637 := div_le_self (by norm_num) hll1
  generalize Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 1000) = A at k1 ⊢
  generalize 2.50637 / Real.log (Real.log 1000) = B at k2 ⊢
  linarith

/-- **The sliver swap at `(0.811, 45.7575)`**: `gYP(Y, 1000) ≤ 1.04488` for `Y ≥ 3.4·10²³`
(`gYL(Y,1000) ≤ 0.6`, `dP(1000) ≤ 0.311·4/44 + 23.0037/1000 ≤ 0.0514`). -/
theorem gYP_1000_le (Y : ℝ) (hY : 3.4e23 ≤ Y) : gYP 0.811 45.7575 Y 1000 ≤ 1.04488 := by
  rw [gYP_eq]
  have h1 := MO.gYL_1000_le Y hY
  have hF := bigF_1000_le
  have hF0 : 0 ≤ MinSp.bigF 1000 := le_trans (by norm_num) (GS.bigF_gt 1000 (by norm_num)).le
  have hsF : Real.sqrt (MinSp.bigF 1000) ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs2000 : 44 ≤ Real.sqrt (2 * 1000) := by
    rw [show (44 : ℝ) = Real.sqrt (44 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have k1 : (0.811 - 0.5) * Real.sqrt (MinSp.bigF 1000) / Real.sqrt (2 * 1000) ≤
      0.311 * 4 / 44 :=
    calc (0.811 - 0.5) * Real.sqrt (MinSp.bigF 1000) / Real.sqrt (2 * 1000)
        ≤ 0.311 * 4 / Real.sqrt (2 * 1000) := by
          apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
          nlinarith [Real.sqrt_nonneg (MinSp.bigF 1000)]
      _ ≤ 0.311 * 4 / 44 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2000
  have k2 : ((45.7575 : ℝ) - 22.7538) / 1000 ≤ 0.0231 := by norm_num
  have k3 : (0.311 : ℝ) * 4 / 44 ≤ 0.0283 := by norm_num
  have hd : dP 0.811 45.7575 1000 ≤ 0.0514 := by
    unfold dP
    generalize (0.811 - 0.5) * Real.sqrt (MinSp.bigF 1000) / Real.sqrt (2 * 1000) = A at k1 ⊢
    generalize ((45.7575 : ℝ) - 22.7538) / 1000 = B at k2 ⊢
    linarith
  linarith

/-- **[GTMonoP] from [GYMonoP] and the sliver swap**, for every `φ ≥ 0` in `L¹(0,∞)` and
`c05, C ≥ 0` (generated from `MO.gtMonoL_of`: `gYL_1000_le ↦ hsl`). -/
theorem gtMonoP_of (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC : 0 ≤ C) (φ : ℝ → ℝ)
    (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (hφi : IntegrableOn φ (Ioi 0)) (hmo : GSP.GYMonoP c05 C)
    (hsl : ∀ Y : ℝ, 3.4e23 ≤ Y → gYP c05 C Y 1000 ≤ 1.04488) : GTMonoP c05 C φ := by
  intro y hy r hr r' hr' hrr'
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hr'0, hr'1⟩ := hr'
  have hrp : 0 < r := by linarith
  have hr'p : 0 < r' := by linarith
  have hl17 := GS.log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  have hint := GSP.gtlIntP c05 C hc05 hC φ hφi y hy r hr0 hr1
  have hint' := GSP.gtlIntP c05 C hc05 hC φ hφi y hy r' hr'0 hr'1
  have hφa : IntegrableOn (fun w => |φ w|) (Ioi 0) := hφi.abs
  unfold gTP
  refine div_le_div_of_nonneg_right ?_ (MajSp.l1_nonneg φ)
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 1 / MinSp.kK y := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = max k (1000 / r) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = max k (1000 / r') := ⟨_, rfl⟩
  rw [← hk, ← ha, ← ha']
  rw [← hk] at hK0 hK1 hint hint'
  rw [← ha] at hint
  rw [← ha'] at hint'
  have haa : a' ≤ a := by
    rw [ha, ha']
    exact max_le_max le_rfl (div_le_div_of_nonneg_left (by norm_num) hrp hrr')
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact max_le hK1 (by rw [div_le_one hrp]; linarith)
  have hka : k ≤ a := by rw [ha]; exact le_max_left _ _
  have hka' : k ≤ a' := by rw [ha']; exact le_max_left _ _
  have hra : 1000 / r ≤ a := by rw [ha]; exact le_max_right _ _
  have hra' : 1000 / r' ≤ a' := by rw [ha']; exact le_max_right _ _
  have hscale : ∀ w : ℝ, k ≤ w → 3.4e23 ≤ w * y := fun w hw =>
    GS.scale_ge y w hy (by rw [← hk]; exact hw)
  -- integrability
  have hI1'a : IntervalIntegrable (fun w => gYP c05 C (w * y) (w * r') * φ w) volume a' a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haa).mpr
      (hint'.1.mono_set (Ioc_subset_Ioc_right ha1))
  have hI1'b : IntervalIntegrable (fun w => gYP c05 C (w * y) (w * r') * φ w) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).mpr
      (hint'.1.mono_set (Ioc_subset_Ioc_left haa))
  have hI1 : IntervalIntegrable (fun w => gYP c05 C (w * y) (w * r) * φ w) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).mpr hint.1
  have hS1 : IntervalIntegrable (fun w => |φ w|) volume k a' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hka').mpr
      (hφa.mono_set fun w hw => lt_of_lt_of_le hK0 hw.1.le)
  have hS2 : IntervalIntegrable (fun w => |φ w|) volume a' a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haa).mpr
      (hφa.mono_set fun w hw => lt_of_lt_of_le hK0 (le_trans hka' hw.1.le))
  have split1 := intervalIntegral.integral_add_adjacent_intervals hI1'a hI1'b
  have split2 := intervalIntegral.integral_add_adjacent_intervals hS1 hS2
  -- the moved piece
  have b1 : (∫ w in a'..a, gYP c05 C (w * y) (w * r') * φ w) ≤ ∫ w in a'..a, 1.04488 * |φ w| := by
    refine intervalIntegral.integral_mono_on haa hI1'a (hS2.const_mul 1.04488) fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hK0 (le_trans hka' hw.1)
    have hw1 : w ≤ 1 := le_trans hw.2 ha1
    have hY := hscale w (le_trans hka' hw.1)
    have h1000 : 1000 ≤ w * r' := by
      have := le_trans hra' hw.1
      rwa [div_le_iff₀ hr'p] at this
    have harg := GS.arg_le_r1y y w r' hy0 hw0 hr'1
    rw [min_eq_left hw1] at harg
    have hth := GS.r1y_le_third (w * y) hY
    have hg : gYP c05 C (w * y) (w * r') ≤ gYP c05 C (w * y) 1000 :=
      hmo (w * y) hY ⟨by norm_num, by linarith⟩ ⟨by linarith, le_trans harg hth⟩ h1000
    have hg6 := hsl (w * y) hY
    have hφw := hφ0 w hw0.le
    rw [abs_of_nonneg hφw]
    exact mul_le_mul_of_nonneg_right (by linarith) hφw
  have b1c : (∫ w in a'..a, 1.04488 * |φ w|) = 1.04488 * ∫ w in a'..a, |φ w| :=
    intervalIntegral.integral_const_mul _ _
  -- the integrand decreases on `[a, 1]`
  have b2 : (∫ w in a..1, gYP c05 C (w * y) (w * r') * φ w) ≤
      ∫ w in a..1, gYP c05 C (w * y) (w * r) * φ w := by
    refine intervalIntegral.integral_mono_on ha1 hI1'b hI1 fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hK0 (le_trans hka hw.1)
    have hY := hscale w (le_trans hka hw.1)
    have h1000 : 1000 ≤ w * r := by
      have := le_trans hra hw.1
      rwa [div_le_iff₀ hrp] at this
    have hle : w * r ≤ w * r' := mul_le_mul_of_nonneg_left hrr' hw0.le
    have harg := GS.arg_le_r1y y w r' hy0 hw0 hr'1
    rw [min_eq_left hw.2] at harg
    have hth := GS.r1y_le_third (w * y) hY
    exact mul_le_mul_of_nonneg_right
      (hmo (w * y) hY ⟨by linarith, by linarith⟩ ⟨by linarith, le_trans harg hth⟩ hle)
      (hφ0 w hw0.le)
  -- the integrand decreases on `(1, ∞)`
  have b3 : (∫ w in Ioi 1, gYP c05 C (w * y) r' * φ w) ≤
      ∫ w in Ioi 1, gYP c05 C (w * y) r * φ w := by
    refine setIntegral_mono_on hint'.2 hint.2 measurableSet_Ioi fun w (hw : 1 < w) => ?_
    have hY : 3.4e23 ≤ w * y := by nlinarith
    have harg := GS.arg_le_r1y y w r' hy0 (by linarith) hr'1
    rw [min_eq_right hw.le, one_mul] at harg
    have hth := GS.r1y_le_third (w * y) hY
    exact mul_le_mul_of_nonneg_right
      (hmo (w * y) hY ⟨by linarith, by linarith⟩ ⟨by linarith, le_trans harg hth⟩ hrr')
      (hφ0 w (by linarith))
  rw [← split1, ← split2]
  linarith

/-- **[GTMonoP] on Helfgott's `φ` at `(0.811, 45.7575)`, PROVED**. -/
theorem gtMonoP_helf : GTMonoP 0.811 45.7575 HW.phi :=
  gtMonoP_of 0.811 45.7575 (by norm_num) (by norm_num) HW.phi (fun t _ => HW.phi_nonneg t)
    MinSp.phi_integrableOn gYMonoP gYP_1000_le

/-! ## (4) `CoprarP` transferred -/

/-- **`g̃_L ≤ g̃_P`** on `[150000, r₁(y)]` for `φ ≥ 0` in `L¹(0,∞)`, `c05 ≥ 0.5`, `C ≥ 22.7538`:
the sliver is identical and the two integrands increase pointwise (`OP.gYL_le_gYP`). -/
theorem gTL_le_gTP (c05 C : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (φ : ℝ → ℝ)
    (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (hφi : IntegrableOn φ (Ioi 0)) (y : ℝ) (hy : 10 ^ 25 ≤ y)
    (r : ℝ) (hr : 150000 ≤ r) (hr1 : r ≤ MinSp.r1y y) : OL.gTL φ y r ≤ gTP c05 C φ y r := by
  have hr0 : 0 < r := by linarith
  have hl17 := GS.log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  have hw1 : max (1 / MinSp.kK y) (1000 / r) ≤ 1 :=
    max_le hK1 (by rw [div_le_one hr0]; linarith)
  have hw0 : 0 < max (1 / MinSp.kK y) (1000 / r) := lt_of_lt_of_le hK0 (le_max_left _ _)
  obtain ⟨iL1, iL2⟩ := GS.gtlInt φ hφi y hy r hr hr1
  obtain ⟨iP1, iP2⟩ := GSP.gtlIntP c05 C (by linarith) (by linarith) φ hφi y hy r hr hr1
  unfold OL.gTL gTP
  refine div_le_div_of_nonneg_right ?_ (MajSp.l1_nonneg φ)
  have b1 : (∫ w in (max (1 / MinSp.kK y) (1000 / r))..1, OL.gYL (w * y) (w * r) * φ w) ≤
      ∫ w in (max (1 / MinSp.kK y) (1000 / r))..1, gYP c05 C (w * y) (w * r) * φ w := by
    refine intervalIntegral.integral_mono_on hw1
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw1).mpr iL1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw1).mpr iP1) fun w hw => ?_
    have hw0' : 0 < w := lt_of_lt_of_le hw0 hw.1
    exact mul_le_mul_of_nonneg_right
      (gYL_le_gYP c05 C _ _ hc hC (mul_pos hw0' hr0).le) (hφ0 w hw0'.le)
  have b2 : (∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * φ w) ≤
      ∫ w in Ioi (1 : ℝ), gYP c05 C (w * y) r * φ w := by
    refine setIntegral_mono_on iL2 iP2 measurableSet_Ioi fun w (hw : 1 < w) => ?_
    exact mul_le_mul_of_nonneg_right (gYL_le_gYP c05 C _ _ hc hC hr0.le) (hφ0 w (by linarith))
  linarith

/-- **[CoprarP] from [CoprarL]** for `c05 ≥ 0.5`, `C ≥ 22.7538`: the bound at `r₀ = 150000`
only grows (`gTL_le_gTP`; `r₀ ≤ r₁(x/49)` by `OS.floor_big`). -/
theorem coprarP_of_L (c05 C : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (ηs φ : ℝ → ℝ)
    (h : OL.CoprarL ηs φ) : CoprarP c05 C ηs φ := by
  intro hη hφ0 hφi x hx α hα
  have hy := MinSp.y_ge x hx
  have hy0 : 0 ≤ x / 49 := le_trans (by norm_num) hy
  have hRb := OS.floor_big x hx
  have hDh := OS.dh_pos x hx
  have hfl : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) :=
    Nat.floor_le (OS.r1y_nonneg _ hy0)
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hg := gTL_le_gTP c05 C hc hC φ hφ0 hφi (x / 49) hy 150000 le_rfl (by linarith)
  have hL := h hη hφ0 hφi x hx α hα
  have hl1 := MajSp.l1_nonneg φ
  refine le_trans hL ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hl1) hy0

/-- **[CoprarP] at `(0.811, 45.7575)` on Helfgott's weights, from the retyped major arcs**
(`CP.coprarL_of_R`, `coprarP_of_L`). -/
theorem coprarP_of_R (pf : RT.PlattFull)
    (hm : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) :
    CoprarP 0.811 45.7575 HW.etaStar HW.phi :=
  coprarP_of_L 0.811 45.7575 (by norm_num) (by norm_num) HW.etaStar HW.phi (CP.coprarL_of_R pf hm)

end Principia.Common.TernaryGoldbach.MOP
