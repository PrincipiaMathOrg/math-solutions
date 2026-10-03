/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumLProofs
import Principia.Common.TernaryGoldbach.MonoP

set_option autoImplicit false

/-!
# `OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406` PROVED

The `M̃` link at the corrected constants. `MNumL.lean` composes `OL.MNumL HW.phi 8.54 0.8095 0.6406`
from links about `g̃_L` on six `y`-blocks (`ML.mnumL_of_links`), all DISCHARGED
(`MNumLProofs.lean`). Here each link is RAISED by the increment `g̃_P − g̃_L` and the same six
blocks are re-closed at `0.84`:

* **the increment** (`gTP_le`): `g̃_P(y,r) ≤ g̃_L(y,r) + 1.31395·dP(r)`, `dP = OP.dP 0.811 45.7575`
  — `ML.gTL_le`'s argument with `dP` in place of `(L_c − L)/r`: on `w ≤ 1`,
  `dP(wr)φ(w) ≤ dP(r)·w e^{−w²/2}` (`dPlo_le`: `ϝ(wr) ≤ ϝ(r)`, `w^{3/2} ≤ w`), whose integral is
  `≤ 1 − e^{−1/2}`; on `w > 1`, `∫φ ≤ |φ|₁`; `(1 − 0.6065306597)/√(π/2) ≤ 0.31395`;
* **the integral** (`intGTP_le`): `dP(r) ≤ dP(r₀)e^{−0.43(log r − log r₀)}` for `r ≥ r₀`
  (`ϝ(r)/r = qL(log r)e^{−0.86 log r}`, `MO.qL_anti`), so `∫_{r₀}^{r₁} dP/r ≤ a S₀/0.43 + b/r₀
  ≤ 0.0032345` (`a = 0.311`, `b = 23.0037`, `S₀ = √ϝ(r₀)/√(2r₀) ≤ 0.0042596`);
* **the far regime** (`far_le`): `cf(x)·dP(r₁) ≤ 0.0065` for `x ≥ 4.9·10²⁸` (`cf ≤ (7/15)·0.6406
  log x`, the decay above, and `L e^{−ε(L − L₀)} ≤ L₀` for `εL₀ ≥ 1`, `decayL`);
* the numbers: `dP(r₀) ≤ 0.001479`, `dP(r₁(y)) ≤ dP(1.5·10⁶) ≤ 0.00045` (`MOP.dP_anti`,
  `r₁ ≥ 1.5·10⁶`), `ϝ(r) ≤ 3.6544 + 0.15003 log r` (`MN.bigF_le`).

Raised links (`L`-value + increment): `G₀ 0.0427913 ↦ 0.0447364`, `T₁` `+0.000592`, `∫g̃/r`
`+0.004251`, far `T₁ 0.206372 ↦ 0.214913`. Certified block values against `0.84`
(`scratchpad/ostopp/mnump_cert_price.py`): `0.83523, 0.83200, 0.83200, 0.82531, 0.81911` and far
`0.81123`; the smallest margin is `0.0048` (first block), against the float `sup M̃ = 0.818495`.
-/

namespace Principia.Common.TernaryGoldbach.MNP

open MinSp MeasureTheory Set MC
open Principia.Common.TernaryGoldbach.ML
open Principia.Common.TernaryGoldbach.OP

-- `g̃` and `∫g̃/r` at `(0.811, 45.7575)` on Helfgott's `φ`
local notation "gPh" => gTP 0.811 45.7575 HW.phi
local notation "iPh" => intGTP 0.811 45.7575 HW.phi

/-! ## (1) The increment `g̃_P − g̃_L ≤ 1.31395·dP(r)` -/

/-- **The `w ≤ 1` increment, pointwise**: for `0 < w ≤ 1`, `wr ≥ 50`,
`dP(wr)·φ(w) ≤ dP(r)·w e^{−w²/2}` (`ϝ(wr) ≤ ϝ(r)`, `w²/√w ≤ w`, `w²/w = w`). -/
theorem dPlo_le (c05 C r w : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (hr : 0 < r) (hw : 0 < w)
    (hw1 : w ≤ 1) (hwr : 50 ≤ w * r) :
    dP c05 C (w * r) * HW.phi w ≤ dP c05 C r * (w ^ 1 * Real.exp (-w ^ 2 / 2)) := by
  have hwrr : w * r ≤ r := by nlinarith
  have hF := GS.bigF_mono (w * r) r hwr hwrr
  have hsF : Real.sqrt (MinSp.bigF (w * r)) ≤ Real.sqrt (MinSp.bigF r) := Real.sqrt_le_sqrt hF
  have hsF0 : 0 ≤ Real.sqrt (MinSp.bigF (w * r)) := Real.sqrt_nonneg _
  have hsw : Real.sqrt (2 * (w * r)) = Real.sqrt w * Real.sqrt (2 * r) := by
    rw [show 2 * (w * r) = w * (2 * r) by ring, Real.sqrt_mul hw.le]
  have hs0 : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hss : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw.le
  have hs1 : Real.sqrt w ≤ 1 := Real.sqrt_le_one.mpr hw1
  have hQ0 : 0 < Real.sqrt (2 * r) := Real.sqrt_pos.2 (by linarith)
  have hE0 : 0 < Real.exp (-w ^ 2 / 2) := Real.exp_pos _
  unfold dP HW.phi
  rw [hsw]
  generalize Real.sqrt (MinSp.bigF (w * r)) = f1 at hsF hsF0 ⊢
  generalize Real.sqrt (MinSp.bigF r) = f2 at hsF ⊢
  generalize Real.sqrt (2 * r) = Q at hQ0 ⊢
  generalize Real.exp (-w ^ 2 / 2) = E at hE0 ⊢
  generalize Real.sqrt w = s at hs0 hss hs1 ⊢
  subst hss
  have hA : 0 ≤ c05 - 0.5 := by linarith
  have hB : 0 ≤ C - 22.7538 := by linarith
  have e1 : ((c05 - 0.5) * f1 / (s * Q) + (C - 22.7538) / (s * s * r)) * ((s * s) ^ 2 * E) =
      ((c05 - 0.5) * f1 / Q * s + (C - 22.7538) / r) * (s * s * E) := by
    field_simp
  have e2 : ((c05 - 0.5) * f2 / Q + (C - 22.7538) / r) * ((s * s) ^ 1 * E) =
      ((c05 - 0.5) * f2 / Q + (C - 22.7538) / r) * (s * s * E) := by ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have k1 : (c05 - 0.5) * f1 / Q * s ≤ (c05 - 0.5) * f1 / Q := by
    have : 0 ≤ (c05 - 0.5) * f1 / Q := div_nonneg (mul_nonneg hA hsF0) hQ0.le
    nlinarith
  have k2 : (c05 - 0.5) * f1 / Q ≤ (c05 - 0.5) * f2 / Q :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsF hA) hQ0.le
  linarith

/-- **The `w ≤ 1` integral**: `∫_{w₁}^1 gYP(wy,wr)φ ≤ ∫_{w₁}^1 gYL(wy,wr)φ +
dP(r)(1 − 0.6065306597)` (`w₁ = max(1/K, 1000/r)`; both integrands integrable, `GS.gtlInt`,
`GSP.gtlIntP`). -/
theorem lo_leP (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 150000 ≤ r) (hr1 : r ≤ r1y y) :
    ∫ w in (max (1 / kK y) (1000 / r))..1, gYP 0.811 45.7575 (w * y) (w * r) * HW.phi w ≤
      (∫ w in (max (1 / kK y) (1000 / r))..1, OL.gYL (w * y) (w * r) * HW.phi w) +
        dP 0.811 45.7575 r * (1 - 0.6065306597) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨-, -, hm1⟩ := w1_facts y r hy (by linarith)
  have hw1 : 1000 / r ≤ max (1 / kK y) (1000 / r) := le_max_right _ _
  have hw11 : max (1 / kK y) (1000 / r) ≤ 1 := hm1.trans (by norm_num)
  have hw10 : 0 < max (1 / kK y) (1000 / r) := lt_of_lt_of_le (by positivity) hw1
  obtain ⟨iL, -⟩ := GS.gtlInt HW.phi MinSp.phi_integrableOn y hy r hr hr1
  obtain ⟨iP, -⟩ := GSP.gtlIntP 0.811 45.7575 (by norm_num) (by norm_num) HW.phi
    MinSp.phi_integrableOn y hy r hr hr1
  have hIL : IntervalIntegrable (fun w => OL.gYL (w * y) (w * r) * HW.phi w) volume
      (max (1 / kK y) (1000 / r)) 1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hw11).mpr iL
  have hIP : IntervalIntegrable (fun w => gYP 0.811 45.7575 (w * y) (w * r) * HW.phi w) volume
      (max (1 / kK y) (1000 / r)) 1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hw11).mpr iP
  have hD0 : 0 ≤ dP 0.811 45.7575 r := dP_nonneg _ _ r (by norm_num) (by norm_num) hr0.le
  have hmi : IntervalIntegrable
      (fun w : ℝ => dP 0.811 45.7575 r * (w ^ 1 * Real.exp (-w ^ 2 / 2))) volume
      (max (1 / kK y) (1000 / r)) 1 :=
    ((continuous_mom 1).const_mul _).intervalIntegrable _ _
  have h1 : ∫ w in (max (1 / kK y) (1000 / r))..1,
      (gYP 0.811 45.7575 (w * y) (w * r) * HW.phi w - OL.gYL (w * y) (w * r) * HW.phi w) ≤
      ∫ w in (max (1 / kK y) (1000 / r))..1,
        dP 0.811 45.7575 r * (w ^ 1 * Real.exp (-w ^ 2 / 2)) := by
    refine intervalIntegral.integral_mono_on hw11 (hIP.sub hIL) hmi fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hw10 hw.1
    have hwr : 1000 ≤ w * r := by
      have h := mul_le_mul_of_nonneg_right (hw1.trans hw.1) hr0.le
      rwa [div_mul_cancel₀ _ hr0.ne'] at h
    have hk := dPlo_le 0.811 45.7575 r w (by norm_num) (by norm_num) hr0 hw0 hw.2 (by linarith)
    calc gYP 0.811 45.7575 (w * y) (w * r) * HW.phi w - OL.gYL (w * y) (w * r) * HW.phi w
        = dP 0.811 45.7575 (w * r) * HW.phi w := by rw [gYP_eq]; ring
      _ ≤ _ := hk
  rw [intervalIntegral.integral_sub hIP hIL, intervalIntegral.integral_const_mul] at h1
  have hJ : ∫ w in (max (1 / kK y) (1000 / r))..1, w ^ 1 * Real.exp (-w ^ 2 / 2) =
      mJ (max (1 / kK y) (1000 / r)) 1 1 := rfl
  rw [hJ, mJ_one] at h1
  have he1 : Real.exp (-(max (1 / kK y) (1000 / r)) ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg (max (1 / kK y) (1000 / r))]
  have he2 := ex_1.1
  have hk : Real.exp (-(max (1 / kK y) (1000 / r)) ^ 2 / 2) - Real.exp (-1 ^ 2 / 2) ≤
      1 - 0.6065306597 := by linarith
  have h2 := mul_le_mul_of_nonneg_left hk hD0
  linarith

/-- **The `w > 1` integral**: `∫_{w>1} gYP(wy,r)φ ≤ ∫_{w>1} gYL(wy,r)φ + dP(r)√(π/2)`
(`EN.int_phi`; `ML.hi_le` with `dP` for `(L_c − L)/r`). -/
theorem hi_leP (y r : ℝ) (hr : 150000 ≤ r) :
    ∫ w in Ioi (1 : ℝ), gYP 0.811 45.7575 (w * y) r * HW.phi w ≤
      (∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * HW.phi w) +
        dP 0.811 45.7575 r * Real.sqrt (Real.pi / 2) := by
  have hr0 : 0 < r := by linarith
  set D := dP 0.811 45.7575 r with hD
  have hDn : 0 ≤ D := dP_nonneg _ _ r (by norm_num) (by norm_num) hr0.le
  have hs0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  set fC : ℝ → ℝ := fun w => OL.gYL (w * y) r * HW.phi w with hfC
  have hsplit : (fun w => gYP 0.811 45.7575 (w * y) r * HW.phi w) =
      fun w => fC w + D * HW.phi w := by
    funext w
    rw [hfC, hD, gYP_eq]
    ring
  have hpi : IntegrableOn HW.phi (Ioi (1 : ℝ)) :=
    MinSp.phi_integrableOn.mono_set (Ioi_subset_Ioi zero_le_one)
  have hphi : ∫ w in Ioi (1 : ℝ), HW.phi w ≤ Real.sqrt (Real.pi / 2) := by
    rw [← EN.int_phi]
    exact setIntegral_mono_set MinSp.phi_integrableOn
      (Filter.Eventually.of_forall fun w => HW.phi_nonneg w)
      (Ioi_subset_Ioi zero_le_one).eventuallyLE
  have hphi0 : 0 ≤ ∫ w in Ioi (1 : ℝ), HW.phi w :=
    setIntegral_nonneg measurableSet_Ioi fun w _ => HW.phi_nonneg w
  have hDI : ∫ w in Ioi (1 : ℝ), D * HW.phi w ≤ D * Real.sqrt (Real.pi / 2) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hphi hDn
  have hB0 : 0 ≤ D * Real.sqrt (Real.pi / 2) := mul_nonneg hDn hs0
  rw [hsplit]
  by_cases hfi : IntegrableOn fC (Ioi (1 : ℝ))
  · rw [integral_add hfi (hpi.const_mul D)]
    linarith
  · have hnot : ¬ IntegrableOn (fun w => fC w + D * HW.phi w) (Ioi (1 : ℝ)) := by
      intro h
      apply hfi
      have h' : IntegrableOn (fun w => fC w + D * HW.phi w - D * HW.phi w) (Ioi (1 : ℝ)) :=
        h.sub (hpi.const_mul D)
      simpa using h'
    rw [integral_undef hnot, integral_undef hfi]
    linarith

/-- **THE INCREMENT**: `g̃_P(y, r) ≤ g̃_L(y, r) + 1.31395·dP(r)` on `[150000, r₁(y)]`, `y ≥ 10²⁵`
(`lo_leP`, `hi_leP`, `|φ|₁ = √(π/2) ≥ 1.2533139`; `ML.gTL_le`'s closing). -/
theorem gTP_le (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 150000 ≤ r) (hr1 : r ≤ r1y y) :
    gPh y r ≤ OL.gTL HW.phi y r + 1.31395 * dP 0.811 45.7575 r := by
  have hr0 : 0 < r := by linarith
  have h1 := lo_leP y r hy hr hr1
  have h2 := hi_leP y r hr
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  obtain ⟨hs1, -⟩ := MajSp.sqrt_pi_half
  have hD0 : 0 ≤ dP 0.811 45.7575 r := dP_nonneg _ _ r (by norm_num) (by norm_num) hr0.le
  unfold gTP OL.gTL
  rw [hl1]
  set Sq := Real.sqrt (Real.pi / 2) with hSq
  set D := dP 0.811 45.7575 r with hD
  have hSq0 : 0 < Sq := lt_of_lt_of_le (by norm_num) hs1
  set IP := ∫ w in (max (1 / kK y) (1000 / r))..1, gYP 0.811 45.7575 (w * y) (w * r) * HW.phi w
  set IH := ∫ w in Ioi (1 : ℝ), gYP 0.811 45.7575 (w * y) r * HW.phi w
  set JL := ∫ w in (max (1 / kK y) (1000 / r))..1, OL.gYL (w * y) (w * r) * HW.phi w
  set JH := ∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * HW.phi w
  set S := 1.04488 * ∫ w in (1 / kK y)..(max (1 / kK y) (1000 / r)), |HW.phi w|
  have hk : D * (1 - 0.6065306597) / Sq ≤ D * 0.31395 := by
    rw [div_le_iff₀ hSq0]
    nlinarith
  calc (IP + IH + S) / Sq ≤ (JL + JH + S + D * (1 - 0.6065306597) + D * Sq) / Sq :=
        div_le_div_of_nonneg_right (by linarith) hSq0.le
    _ = (JL + JH + S) / Sq + D * (1 - 0.6065306597) / Sq + D := by
        field_simp
    _ ≤ (JL + JH + S) / Sq + 1.31395 * D := by linarith

/-! ## (2) The numbers `dP(r₀)`, `dP(r₁)` and the decay of `dP` -/

/-- `log 150000 ≤ 11.92214` (`150000⁵ ≤ 2⁸⁶`). -/
theorem log150_le : Real.log 150000 ≤ 11.92214 := by
  have hl2 := Real.log_two_lt_d9
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 150000 ^ 5)
    (by norm_num : ((150000 : ℝ)) ^ 5 ≤ 2 ^ 86)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  generalize Real.log 150000 = c at h ⊢
  generalize Real.log 2 = b at h hl2
  linarith

/-- `√ϝ(r₀)/√(2r₀) ≤ 0.0042596` (`ϝ(r₀) ≤ 3.6544 + 0.15003·11.92214 ≤ 5.4431`, `MN.bigF_le`). -/
theorem s0_le : Real.sqrt (MinSp.bigF 150000) / Real.sqrt (2 * 150000) ≤ 0.0042596 := by
  have hF := MN.bigF_le 150000 le_rfl
  have hl := log150_le
  have hF1 : MinSp.bigF 150000 ≤ 2.33305 ^ 2 := by nlinarith
  have hs : Real.sqrt (MinSp.bigF 150000) ≤ 2.33305 := by
    rw [show (2.33305 : ℝ) = Real.sqrt (2.33305 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt hF1
  have hq : 547.7225 ≤ Real.sqrt (2 * 150000) := by
    rw [show (547.7225 : ℝ) = Real.sqrt (547.7225 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hq0 : 0 < Real.sqrt (2 * 150000) := lt_of_lt_of_le (by norm_num) hq
  rw [div_le_iff₀ hq0]
  nlinarith

/-- **`dP(r₀) ≤ 0.001479`** at `(0.811, 45.7575)`: `0.311·0.0042596 + 23.0037/150000`. -/
theorem dP_r0_le : dP 0.811 45.7575 150000 ≤ 0.001479 := by
  have h := s0_le
  unfold dP
  rw [mul_div_assoc]
  generalize Real.sqrt (MinSp.bigF 150000) / Real.sqrt (2 * 150000) = S at h ⊢
  norm_num
  linarith

/-- `r₁(y) ≥ 1.5·10⁶` for `y ≥ 10²⁵` (`OS.rpow_ge_4e6`). -/
theorem r1y_ge (y : ℝ) (hy : 10 ^ 25 ≤ y) : 1.5e6 ≤ r1y y := by
  have h := OS.rpow_ge_4e6 y hy
  unfold MinSp.r1y
  linarith

/-- **`dP(r₁(y)) ≤ 0.00045`** for `y ≥ 10²⁵` (`dP` antitone, `dP(1.5·10⁶) ≤ 0.00045`:
`ϝ ≤ 3.6544 + 0.15003·21 log 2`). -/
theorem dP_r1_le (y : ℝ) (hy : 10 ^ 25 ≤ y) : dP 0.811 45.7575 (r1y y) ≤ 0.00045 := by
  have hr := r1y_ge y hy
  have hanti := MOP.dP_anti 0.811 45.7575 1.5e6 (r1y y) (by norm_num) (by norm_num) (by norm_num)
    hr
  refine hanti.trans ?_
  have hF := MN.bigF_le 1.5e6 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hl : Real.log 1.5e6 ≤ 14.5561 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1.5e6) (by norm_num : (1.5e6 : ℝ) ≤ 2 ^ 21)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 1.5e6 = c at h ⊢
    generalize Real.log 2 = b at h hl2
    linarith
  have hF1 : MinSp.bigF 1.5e6 ≤ 2.4163 ^ 2 := by nlinarith
  have hs : Real.sqrt (MinSp.bigF 1.5e6) ≤ 2.4163 := by
    rw [show (2.4163 : ℝ) = Real.sqrt (2.4163 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt hF1
  have hq : 1732.05 ≤ Real.sqrt (2 * 1.5e6) := by
    rw [show (1732.05 : ℝ) = Real.sqrt (1732.05 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hq0 : 0 < Real.sqrt (2 * 1.5e6) := lt_of_lt_of_le (by norm_num) hq
  have hS : Real.sqrt (MinSp.bigF 1.5e6) / Real.sqrt (2 * 1.5e6) ≤ 0.0013951 := by
    rw [div_le_iff₀ hq0]
    nlinarith
  unfold dP
  rw [mul_div_assoc]
  generalize Real.sqrt (MinSp.bigF 1.5e6) / Real.sqrt (2 * 1.5e6) = S at hS ⊢
  norm_num
  linarith

/-- **The decay of `√ϝ/√(2r)`**: `√ϝ(r)/√(2r) ≤ √ϝ(r₀)/√(2r₀)·e^{−0.43(log r − log r₀)}` for
`r ≥ r₀ = 150000` (`ϝ(r)/r = qL(log r)e^{−0.86 log r}`, `MO.qL_anti`). -/
theorem sqrtF_decay (r : ℝ) (hr : 150000 ≤ r) :
    Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) ≤
      Real.sqrt (MinSp.bigF 150000) / Real.sqrt (2 * 150000) *
        Real.exp (-0.43 * (Real.log r - Real.log 150000)) := by
  have hr0 : 0 < r := by linarith
  have hl5 : 5 ≤ Real.log 150000 :=
    le_trans MO.log175_ge (Real.log_le_log (by norm_num) (by norm_num))
  have hll : Real.log 150000 ≤ Real.log r := Real.log_le_log (by norm_num) hr
  have hQ : MO.qL (Real.log r) ≤ MO.qL (Real.log 150000) :=
    MO.qL_anti (Real.log 150000) (Real.log r) hl5 ⟨le_rfl, hll⟩ ⟨hll, le_rfl⟩ hll
  have h1 : MinSp.bigF r / r ≤
      MinSp.bigF 150000 / 150000 * Real.exp (-0.86 * (Real.log r - Real.log 150000)) := by
    rw [MOP.bigF_div_eq r hr0, MOP.bigF_div_eq 150000 (by norm_num)]
    have e : Real.exp (-0.86 * Real.log 150000) *
        Real.exp (-0.86 * (Real.log r - Real.log 150000)) = Real.exp (-0.86 * Real.log r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, e]
    exact mul_le_mul_of_nonneg_right hQ (Real.exp_pos _).le
  have hF0 : 0 ≤ MinSp.bigF 150000 / (2 * 150000) :=
    div_nonneg (le_trans (by norm_num) (GS.bigF_gt 150000 (by norm_num)).le) (by norm_num)
  rw [← Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ 2 * r),
    ← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 * 150000)]
  have e2 : Real.exp (-0.43 * (Real.log r - Real.log 150000)) =
      Real.sqrt (Real.exp (-0.86 * (Real.log r - Real.log 150000))) := by
    rw [MO.sqrt_exp]
    congr 1
    ring
  rw [e2, ← Real.sqrt_mul hF0]
  apply Real.sqrt_le_sqrt
  have e3 : MinSp.bigF r / (2 * r) = MinSp.bigF r / r / 2 := by ring
  have e4 : MinSp.bigF 150000 / (2 * 150000) *
      Real.exp (-0.86 * (Real.log r - Real.log 150000)) =
      MinSp.bigF 150000 / 150000 * Real.exp (-0.86 * (Real.log r - Real.log 150000)) / 2 := by
    ring
  rw [e3, e4]
  exact div_le_div_of_nonneg_right h1 (by norm_num)

/-- **The decay of `dP`**: `dP(r) ≤ dP(r₀)·e^{−0.43(log r − log r₀)}` for `r ≥ r₀` (the `1/r`
summand decays like `e^{−(log r − log r₀)}`, faster). -/
theorem dP_decay (r : ℝ) (hr : 150000 ≤ r) :
    dP 0.811 45.7575 r ≤
      dP 0.811 45.7575 150000 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) := by
  have hr0 : 0 < r := by linarith
  have hs := sqrtF_decay r hr
  have hll : Real.log 150000 ≤ Real.log r := Real.log_le_log (by norm_num) hr
  have hinv : 1 / r ≤ 1 / 150000 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) := by
    have e : 1 / r = 1 / 150000 * Real.exp (-(Real.log r - Real.log 150000)) := by
      rw [Real.exp_neg, Real.exp_sub, Real.exp_log hr0, Real.exp_log (by norm_num)]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num)
  unfold dP
  rw [mul_div_assoc, mul_div_assoc, div_eq_mul_one_div (45.7575 - 22.7538) r,
    div_eq_mul_one_div (45.7575 - 22.7538) 150000]
  have k1 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 0.811 - 0.5)
  have k2 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 45.7575 - 22.7538)
  generalize Real.exp (-0.43 * (Real.log r - Real.log 150000)) = E at k1 k2 ⊢
  generalize Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) = S at k1 ⊢
  generalize Real.sqrt (MinSp.bigF 150000) / Real.sqrt (2 * 150000) = S0 at k1 ⊢
  generalize (1 : ℝ) / r = u at k2 ⊢
  nlinarith

/-- **The split decay of `dP`**: `dP(r) ≤ 0.311·0.0042596·e^{−0.43(log r − log r₀)} + 23.0037/r`
(`sqrtF_decay`, `s0_le`). -/
theorem dP_le_decay (r : ℝ) (hr : 150000 ≤ r) :
    dP 0.811 45.7575 r ≤ 0.311 * 0.0042596 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) +
      (45.7575 - 22.7538) * (1 / r) := by
  have hs := sqrtF_decay r hr
  have h0 := s0_le
  have hE0 := Real.exp_pos (-0.43 * (Real.log r - Real.log 150000))
  unfold dP
  rw [mul_div_assoc, div_eq_mul_one_div (45.7575 - 22.7538) r]
  have k : (0.811 - 0.5) * (Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r)) ≤
      0.311 * 0.0042596 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) := by
    have k1 := mul_le_mul_of_nonneg_right h0 hE0.le
    have k2 : (0.811 - 0.5 : ℝ) = 0.311 := by norm_num
    rw [k2]
    nlinarith
  linarith

/-! ## (3) `∫ g̃_P/r ≤ ∫ g̃_L/r + 1.31395·0.0032345` -/

/-- `∫_{r₀}^b e^{−0.43(log r − log r₀)}/r dr ≤ 1/0.43` (antiderivative `−e^{…}/0.43`). -/
theorem int_decay (b : ℝ) (hb : 150000 ≤ b) :
    ∫ r in (150000 : ℝ)..b, Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r ≤ 1 / 0.43 := by
  have hpos : ∀ r ∈ Set.uIcc (150000 : ℝ) b, 0 < r := fun r hr => by
    rw [Set.uIcc_of_le hb] at hr
    exact lt_of_lt_of_le (by norm_num) hr.1
  have hderiv : ∀ r ∈ Set.uIcc (150000 : ℝ) b,
      HasDerivAt (fun r => -(1 / 0.43) * Real.exp (-0.43 * (Real.log r - Real.log 150000)))
        (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) r := by
    intro r hr
    have hr0 := hpos r hr
    have h1 : HasDerivAt (fun r => -0.43 * (Real.log r - Real.log 150000)) (-0.43 * r⁻¹) r :=
      ((Real.hasDerivAt_log hr0.ne').sub_const (Real.log 150000)).const_mul (-0.43)
    refine (h1.exp.const_mul (-(1 / 0.43))).congr_deriv ?_
    rw [div_eq_mul_inv]
    ring
  have hcont : ContinuousOn (fun r => Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r)
      (Set.uIcc 150000 b) := by
    refine ContinuousOn.div ?_ continuousOn_id fun r hr => (hpos r hr).ne'
    refine Real.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact (Real.continuousOn_log.mono fun r hr => (hpos r hr).ne').sub continuousOn_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have key : ∀ E : ℝ, 0 < E → -(1 / 0.43) * E -
      -(1 / 0.43) * Real.exp (-0.43 * (Real.log 150000 - Real.log 150000)) ≤ 1 / 0.43 :=
    fun E hE => by
      rw [sub_self, mul_zero, Real.exp_zero]
      have e : -(1 / 0.43) * E - -(1 / 0.43) * 1 = (1 - E) / 0.43 := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  exact key _ (Real.exp_pos _)

/-- `∫_{r₀}^b dr/r² ≤ 1/r₀` (antiderivative `−1/r`). -/
theorem int_inv_sq (b : ℝ) (hb : 150000 ≤ b) : ∫ r in (150000 : ℝ)..b, 1 / r ^ 2 ≤ 1 / 150000 := by
  have hpos : ∀ r ∈ Set.uIcc (150000 : ℝ) b, 0 < r := fun r hr => by
    rw [Set.uIcc_of_le hb] at hr
    exact lt_of_lt_of_le (by norm_num) hr.1
  have hderiv : ∀ r ∈ Set.uIcc (150000 : ℝ) b,
      HasDerivAt (fun r : ℝ => -1 * r⁻¹) (1 / r ^ 2) r := by
    intro r hr
    refine ((hasDerivAt_inv (hpos r hr).ne').const_mul (-1)).congr_deriv ?_
    rw [one_div]
    ring
  have hcont : ContinuousOn (fun r : ℝ => 1 / r ^ 2) (Set.uIcc 150000 b) :=
    continuousOn_const.div (continuousOn_id.pow 2) fun r hr => pow_ne_zero 2 (hpos r hr).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have key : ∀ u : ℝ, 0 < u → -1 * u - -1 * (150000 : ℝ)⁻¹ ≤ 1 / 150000 := fun u hu => by
    norm_num
    linarith
  exact key _ (inv_pos.2 (by linarith))

/-- **`∫_{r₀}^{r₁} g̃_P/r ≤ ∫_{r₀}^{r₁} g̃_L/r + 1.31395·0.0032345`** for `y ≥ 10²⁵`: `gTP_le`,
`dP_le_decay`, `int_decay`, `int_inv_sq` (`0.311·0.0042596/0.43 + 23.0037/150000 ≤ 0.0032345`). Both
integrands are antitone, hence integrable (`MOP.gtMonoP_helf`, `MO.gtMonoL_helf`, `OS.gdiv_int`). -/
theorem intGTP_le (y : ℝ) (hy : 10 ^ 25 ≤ y) :
    iPh y ≤ OL.intGTL HW.phi y + 1.31395 * 0.0032345 := by
  have hab : (150000 : ℝ) ≤ r1y y := le_trans (by norm_num) (r1y_ge y hy)
  have iP := OS.gdiv_int _ _ _ (by norm_num) hab (MOP.gtMonoP_helf y hy)
  have iL := OS.gdiv_int _ _ _ (by norm_num) hab (MO.gtMonoL_helf y hy)
  have hpos : ∀ r ∈ Set.uIcc (150000 : ℝ) (r1y y), 0 < r := fun r hr => by
    rw [Set.uIcc_of_le hab] at hr
    exact lt_of_lt_of_le (by norm_num) hr.1
  have iE : IntervalIntegrable (fun r => Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r)
      volume 150000 (r1y y) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div ?_ continuousOn_id fun r hr => (hpos r hr).ne'
    refine Real.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact (Real.continuousOn_log.mono fun r hr => (hpos r hr).ne').sub continuousOn_const
  have iQ : IntervalIntegrable (fun r : ℝ => 1 / r ^ 2) volume 150000 (r1y y) :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      fun r hr => pow_ne_zero 2 (hpos r hr).ne').intervalIntegrable
  have iB := iL.add ((iE.const_mul (1.31395 * (0.311 * 0.0042596))).add
    (iQ.const_mul (1.31395 * (45.7575 - 22.7538))))
  have hle := intervalIntegral.integral_mono_on hab iP iB fun r hr => by
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
    have hr0' : r ≠ 0 := hr0.ne'
    have hg := gTP_le y r hy hr.1 hr.2
    have hd := dP_le_decay r hr.1
    show gPh y r / r ≤ OL.gTL HW.phi y r / r +
      (1.31395 * (0.311 * 0.0042596) *
          (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) +
        1.31395 * (45.7575 - 22.7538) * (1 / r ^ 2))
    have e : (0.311 * 0.0042596 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) +
        (45.7575 - 22.7538) * (1 / r)) / r =
        0.311 * 0.0042596 * (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) +
          (45.7575 - 22.7538) * (1 / r ^ 2) := by
      field_simp
    have hdr : dP 0.811 45.7575 r / r ≤
        0.311 * 0.0042596 * (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) +
          (45.7575 - 22.7538) * (1 / r ^ 2) := by
      rw [← e]
      exact div_le_div_of_nonneg_right hd hr0.le
    calc gPh y r / r ≤ (OL.gTL HW.phi y r + 1.31395 * dP 0.811 45.7575 r) / r :=
          div_le_div_of_nonneg_right hg hr0.le
      _ = OL.gTL HW.phi y r / r + 1.31395 * (dP 0.811 45.7575 r / r) := by ring
      _ ≤ _ := by linarith
  unfold intGTP OL.intGTL
  refine le_trans hle ?_
  rw [intervalIntegral.integral_add iL ((iE.const_mul _).add (iQ.const_mul _)),
    intervalIntegral.integral_add (iE.const_mul _) (iQ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h1 := int_decay (r1y y) hab
  have h2 := int_inv_sq (r1y y) hab
  generalize ∫ r in (150000 : ℝ)..r1y y,
    Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r = A at h1 ⊢
  generalize ∫ r in (150000 : ℝ)..r1y y, 1 / r ^ 2 = B at h2 ⊢
  norm_num at h1 h2 ⊢
  linarith

/-! ## (4) The far regime: `cf(x)·dP(r₁) ≤ 0.0065` for `x ≥ 4.9·10²⁸` -/

/-- **`L e^{−ε(L − L₀)} ≤ L₀`** for `L ≥ L₀ ≥ 0`, `εL₀ ≥ 1` (`e^t ≥ 1 + t`). -/
theorem decayL (L L0 ε : ℝ) (hL0 : 1 ≤ ε * L0) (hL : L0 ≤ L) (h0 : 0 ≤ L0) :
    L * Real.exp (-(ε * (L - L0))) ≤ L0 := by
  have he := Real.add_one_le_exp (ε * (L - L0))
  have hE : 0 < Real.exp (ε * (L - L0)) := Real.exp_pos _
  have k1 := mul_le_mul_of_nonneg_left he h0
  have k2 : 0 ≤ (ε * L0 - 1) * (L - L0) := mul_nonneg (by linarith) (by linarith)
  have key : L ≤ L0 * Real.exp (ε * (L - L0)) := by nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  linarith

/-- `e^{−1.549417} ≤ 0.2164` (`e^{1.549417} ≥ e·(1 + t + t²/2) ≥ 4.622`, `t = 0.549417`). -/
theorem exp_far_le : Real.exp (-1.549417) ≤ 0.2164 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.549417 by norm_num)
  have e : Real.exp 1.549417 = Real.exp 1 * Real.exp 0.549417 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : 4.622 ≤ Real.exp 1.549417 := by
    rw [e]
    nlinarith [Real.exp_pos 0.549417]
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- **The far regime**: `cf(x)·dP(r₁(x/49)) ≤ 0.0065` for `x ≥ 4.9·10²⁸`:
`cf ≤ (7/15)·0.6406 log x`, `dP(r₁) ≤ dP(r₀)e^{−0.43(log r₁ − log r₀)}`,
`log r₁ = log(3/8) + (4/15)(log x − log 49)`, and
`log x·e^{−(0.43·4/15)(log x − L₀)} ≤ L₀ = log(4.9·10²⁸) ≤ 66.0616179` (`decayL`). -/
theorem far_le (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    cfL x * dP 0.811 45.7575 (r1y (x / 49)) ≤ 0.0065 := by
  have hx26 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy := y_ge x hx26
  have hy0 : 0 < x / 49 := by positivity
  obtain ⟨-, hc1⟩ := coefC_bounds x hx26
  have hLg := LW.log_ge_of x hx26
  have hfel0 : 0 ≤ felL x := by unfold felL; linarith
  have hcf : cfL x ≤ 7 / 15 * (0.6406 * Real.log x) := by
    unfold cfL
    have hf : felL x ≤ 0.6406 * Real.log x := by unfold felL; linarith
    calc OC.coefC x * felL x ≤ 7 / 15 * felL x := mul_le_mul_of_nonneg_right hc1 hfel0
      _ ≤ 7 / 15 * (0.6406 * Real.log x) := by linarith
  have hcf0 := cfL_nonneg x hx26
  have hr1 := r1y_ge (x / 49) hy
  have hd := dP_decay (r1y (x / 49)) (by linarith)
  have hd0 := dP_r0_le
  have hdn : 0 ≤ dP 0.811 45.7575 (r1y (x / 49)) :=
    dP_nonneg _ _ _ (by norm_num) (by norm_num) (by linarith)
  have hlr1 : Real.log (r1y (x / 49)) =
      Real.log (3 / 8) + 4 / 15 * (Real.log x - Real.log 49) := by
    unfold MinSp.r1y
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hy0 _).ne', Real.log_rpow hy0,
      Real.log_div hx0.ne' (by norm_num)]
  have hL0 := lgsL13
  have hL0u := lgsU12
  have hLx : Real.log 49000000000000000000000000000 ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by norm_num at hx ⊢; linarith)
  have hl3 := MO.log3_ge
  have hl2 := Real.log_two_lt_d9
  have hl49 := OS.log49_le
  have hl150 := log150_le
  have hl38 : Real.log (3 / 8) = Real.log 3 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  -- the exponent splits into a constant part and the decaying part
  set L := Real.log x with hL
  set L0 := Real.log 49000000000000000000000000000 with hL0d
  set A := Real.log (3 / 8) + 4 / 15 * (L0 - Real.log 49) - Real.log 150000 with hA
  have hA3 : 3.603297 ≤ A := by
    rw [hA, hl38]
    generalize Real.log 3 = a at hl3 ⊢
    generalize Real.log 2 = b at hl2 hl49 ⊢
    generalize Real.log 49 = c at hl49 ⊢
    generalize Real.log 150000 = d at hl150 ⊢
    linarith
  have hsplit : Real.exp (-0.43 * (Real.log (r1y (x / 49)) - Real.log 150000)) =
      Real.exp (-0.43 * A) * Real.exp (-(0.43 * 4 / 15 * (L - L0))) := by
    rw [← Real.exp_add, hlr1, hA]
    congr 1
    ring
  have hdecay := decayL L L0 (0.43 * 4 / 15) (by nlinarith) hLx (by linarith)
  have hexpA : Real.exp (-0.43 * A) ≤ 0.2164 :=
    (Real.exp_le_exp.2 (by linarith)).trans exp_far_le
  have hEA0 : 0 ≤ Real.exp (-0.43 * A) := (Real.exp_pos _).le
  have hL00 : 0 ≤ L := by linarith
  -- assemble
  calc cfL x * dP 0.811 45.7575 (r1y (x / 49))
      ≤ 7 / 15 * (0.6406 * L) * dP 0.811 45.7575 (r1y (x / 49)) :=
        mul_le_mul_of_nonneg_right hcf hdn
    _ ≤ 7 / 15 * (0.6406 * L) * (0.001479 * (Real.exp (-0.43 * A) *
          Real.exp (-(0.43 * 4 / 15 * (L - L0))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hsplit]
        exact hd.trans (mul_le_mul_of_nonneg_right hd0 (Real.exp_pos _).le)
    _ = 7 / 15 * 0.6406 * 0.001479 * Real.exp (-0.43 * A) *
          (L * Real.exp (-(0.43 * 4 / 15 * (L - L0)))) := by ring
    _ ≤ 7 / 15 * 0.6406 * 0.001479 * 0.2164 * 66.0616179 := by
        have hLd : L * Real.exp (-(0.43 * 4 / 15 * (L - L0))) ≤ 66.0616179 :=
          hdecay.trans (hL0u.trans (by norm_num))
        have k : Real.exp (-0.43 * A) * (L * Real.exp (-(0.43 * 4 / 15 * (L - L0)))) ≤
            0.2164 * 66.0616179 :=
          mul_le_mul hexpA hLd (mul_nonneg hL00 (Real.exp_pos _).le) (by norm_num)
        have hc : (0 : ℝ) ≤ 7 / 15 * 0.6406 * 0.001479 := by norm_num
        calc 7 / 15 * 0.6406 * 0.001479 * Real.exp (-0.43 * A) *
              (L * Real.exp (-(0.43 * 4 / 15 * (L - L0))))
            = 7 / 15 * 0.6406 * 0.001479 *
                (Real.exp (-0.43 * A) * (L * Real.exp (-(0.43 * 4 / 15 * (L - L0))))) := by ring
          _ ≤ 7 / 15 * 0.6406 * 0.001479 * (0.2164 * 66.0616179) :=
              mul_le_mul_of_nonneg_left k hc
          _ = _ := by ring
    _ ≤ 0.0065 := by norm_num

/-! ## (5) The raised links, PROVED from `MNumLProofs`' -/

/-- **Link [g̃_P ≥ 0]**. -/
def GTNonnegP : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → 0 ≤ gPh y 150000

/-- **Link [g̃_P(r₀)]**. -/
def G0EnvP (G : ℝ) : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → gPh y 150000 ≤ G

/-- **Link [g̃_P(r₁)] on a block**. -/
def T1BlkP (ya yb T : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → gPh y (r1y y) ≤ T

/-- **Link [∫g̃_P/r] on a block**. -/
def IGBlkP (ya yb I : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → iPh y ≤ I

/-- **Link [far g̃_P(r₁)]**. -/
def T1FarP (T : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 27 ≤ x → cfL x * gPh (x / 49) (r1y (x / 49)) ≤ T

/-- **Link [far ∫g̃_P/r]**. -/
def IGFarP (I : ℝ) : Prop := ∀ y : ℝ, 10 ^ 27 ≤ y → iPh y ≤ I

/-- `150000 ≤ r₁(y)` for `y ≥ 10²⁵`. -/
theorem r0_le_r1 (y : ℝ) (hy : 10 ^ 25 ≤ y) : (150000 : ℝ) ≤ r1y y :=
  le_trans (by norm_num) (r1y_ge y hy)

/-- **[g̃_P ≥ 0]** from `ML.gtNonnegL` and `g̃_L ≤ g̃_P` (`MOP.gTL_le_gTP`). -/
theorem gtNonnegP : GTNonnegP := fun y hy =>
  le_trans (gtNonnegL y hy) (MOP.gTL_le_gTP 0.811 45.7575 (by norm_num) (by norm_num) HW.phi
    (fun t _ => HW.phi_nonneg t) MinSp.phi_integrableOn y hy 150000 le_rfl (r0_le_r1 y hy))

/-- **[g̃_P(r₀)] at `0.0447364`**: `0.0427913 + 1.31395·0.001479`. -/
theorem g0EnvP : G0EnvP 0.0447364 := fun y hy => by
  have h1 := gTP_le y 150000 hy le_rfl (r0_le_r1 y hy)
  have h2 := g0EnvL y hy
  have h3 := dP_r0_le
  linarith

/-- The `T₁` increment on every block: `g̃_P(y, r₁) ≤ g̃_L(y, r₁) + 0.000592`. -/
theorem t1_step (y : ℝ) (hy : 10 ^ 25 ≤ y) :
    gPh y (r1y y) ≤ OL.gTL HW.phi y (r1y y) + 0.000592 := by
  have h1 := gTP_le y (r1y y) hy (r0_le_r1 y hy) le_rfl
  have h2 := dP_r1_le y hy
  linarith

/-- The `∫g̃/r` increment: `∫g̃_P/r ≤ ∫g̃_L/r + 0.004251`. -/
theorem ig_step (y : ℝ) (hy : 10 ^ 25 ≤ y) : iPh y ≤ OL.intGTL HW.phi y + 0.004251 := by
  have h := intGTP_le y hy
  linarith

/-- **[g̃_P(r₁)] on block 0**: `0.0157963 + 0.000592` (`ML.t1BlkL0`, `t1_step`). -/
theorem t1BlkP0 : T1BlkP (10 ^ 25) (13 * 10 ^ 24) 0.0163883 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_step y hy
  have b := t1BlkL0 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 0**: `0.0669295 + 0.004251` (`ML.iGBlkL0`, `ig_step`). -/
theorem iGBlkP0 : IGBlkP (10 ^ 25) (13 * 10 ^ 24) 0.0711805 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_step y hy
  have b := iGBlkL0 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 1**: `0.0154199 + 0.000592` (`ML.t1BlkL1`, `t1_step`). -/
theorem t1BlkP1 : T1BlkP (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0160119 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_step y hy
  have b := t1BlkL1 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 1**: `0.0683159 + 0.004251` (`ML.iGBlkL1`, `ig_step`). -/
theorem iGBlkP1 : IGBlkP (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0725669 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_step y hy
  have b := iGBlkL1 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 2**: `0.0150526 + 0.000592` (`ML.t1BlkL2`, `t1_step`). -/
theorem t1BlkP2 : T1BlkP (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0156446 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_step y hy
  have b := t1BlkL2 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 2**: `0.0709086 + 0.004251` (`ML.iGBlkL2`, `ig_step`). -/
theorem iGBlkP2 : IGBlkP (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0751596 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_step y hy
  have b := iGBlkL2 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 3**: `0.0141869 + 0.000592` (`ML.t1BlkL3`, `t1_step`). -/
theorem t1BlkP3 : T1BlkP (365 * 10 ^ 23) (10 ^ 26) 0.0147789 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_step y hy
  have b := t1BlkL3 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 3**: `0.0744075 + 0.004251` (`ML.iGBlkL3`, `ig_step`). -/
theorem iGBlkP3 : IGBlkP (365 * 10 ^ 23) (10 ^ 26) 0.0786585 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_step y hy
  have b := iGBlkL3 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 4**: `0.0128839 + 0.000592` (`ML.t1BlkL4`, `t1_step`). -/
theorem t1BlkP4 : T1BlkP (10 ^ 26) (10 ^ 27) 0.0134759 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_step y hy
  have b := t1BlkL4 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 4**: `0.0809224 + 0.004251` (`ML.iGBlkL4`, `ig_step`). -/
theorem iGBlkP4 : IGBlkP (10 ^ 26) (10 ^ 27) 0.0851734 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_step y hy
  have b := iGBlkL4 y h1 h2
  linarith

/-- **[far g̃_P(r₁)] at `0.214913`**: `0.206372 + 1.31395·0.0065` (`ML.t1FarL`, `far_le`). -/
theorem t1FarP : T1FarP 0.214913 := fun x hx => by
  have hx26 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hy := y_ge x hx26
  have h1 := gTP_le (x / 49) (r1y (x / 49)) hy (r0_le_r1 _ hy) le_rfl
  have hcf0 := cfL_nonneg x hx26
  have h2 := t1FarL x hx
  have h3 := far_le x hx
  have h4 := mul_le_mul_of_nonneg_left h1 hcf0
  nlinarith

/-- **[far ∫g̃_P/r] at `0.1087`**: `0.104449 + 0.004251` (`ML.iGFarL`). -/
theorem iGFarP : IGFarP 0.1087 := fun y hy => by
  have h1 := ig_step y (le_trans (by norm_num) hy)
  have h2 := iGFarL y hy
  linarith

/-! ## (6) THE COMPOSITION at `0.84` (generated from `MNumL.lean`) -/

/-- **The affine reduction** for `g̃_P` (generated from `ML.mnumL_of_felipa`). -/
theorem mnumP_of_felipa (p0 c : ℝ) (hp0 : 0 ≤ p0) (hc : 0 ≤ c) (hg : GTNonnegP)
    (hM : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      gPh (x / 49) 150000 * (hsL x - p0) +
        cfL x * gPh (x / 49) (r1y (x / 49)) + casL x * iPh (x / 49) ≤
          c) :
    MNumP 0.811 45.7575 HW.phi p0 c 0.6406 := by
  intro x hx s p hs0 hs1 hp
  refine MN.affine_step _ _ _ _ s p p0 c (hg (x / 49) (y_ge x hx)) hp0 hs0 hs1 hp hc ?_
  have e : gPh (x / 49) 150000 * (hsL x - p0) +
        cfL x * gPh (x / 49) (r1y (x / 49)) + casL x * iPh (x / 49) =
      gPh (x / 49) 150000 * (OC.hR0C x * (0.6406 * Real.log x - 0.021095) - p0) +
        (2 / (Real.log x - 2 * 1.306476) * iPh (x / 49) +
          OC.coefC x * gPh (x / 49) (r1y (x / 49))) *
          (0.6406 * Real.log x - 0.021095) := by
    unfold hsL cfL casL felL
    ring
  rw [← e]
  exact hM x hx

/-- **THE SPINE of `OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406`** (generated from
`ML.mnumL_of_links`: every link raised, every block closed at `0.84`). -/
theorem mnumP_of_links (g0 : GTNonnegP) (e0 : G0EnvP 0.0447364)
    (t0 : T1BlkP (10 ^ 25) (13 * 10 ^ 24) 0.0163883)
    (t1 : T1BlkP (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0160119)
    (t2 : T1BlkP (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0156446)
    (t3 : T1BlkP (365 * 10 ^ 23) (10 ^ 26) 0.0147789) (t4 : T1BlkP (10 ^ 26) (10 ^ 27) 0.0134759)
    (i0 : IGBlkP (10 ^ 25) (13 * 10 ^ 24) 0.0711805)
    (i1 : IGBlkP (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0725669)
    (i2 : IGBlkP (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0751596)
    (i3 : IGBlkP (365 * 10 ^ 23) (10 ^ 26) 0.0786585) (i4 : IGBlkP (10 ^ 26) (10 ^ 27) 0.0851734)
    (tf : T1FarP 0.214913) (ifr : IGFarP 0.1087) :
    MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406 := by
  refine mnumP_of_felipa 8.54 0.84 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hx0 := x_pos x hx
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hg := e0 (x / 49) (y_ge x hx)
  have hh0 := hsL_ge x hx
  have hca0 := casL_nonneg x hx
  have hcf0 := cfL_nonneg x hx
  rcases le_or_gt x 637000000000000000000000000 with hb0 | hb0
  · have hlo : (490000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hx
    have hL : 61.4564475 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL1.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 61.718812 :=
      ((Real.log_le_log hx0 hb0).trans lgsU4).trans (by norm_num)
    have hya : (10 ^ 25) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (13 * 10 ^ 24) := MN.y_le_of x _ (le_trans hb0 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.68522 (17.46297 * 0.0163883) 1.337375 0.0711805 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t0 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i0 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 901600000000000000000000000 with hb1 | hb1
  · have hlo : (637000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb0.le
    have hL : 61.7188118 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL5.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.0662133 :=
      ((Real.log_le_log hx0 hb1).trans lgsU6).trans (by norm_num)
    have hya : (13 * 10 ^ 24) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (184 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb1 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.68173 (17.56706 * 0.0160119) 1.337126 0.0725669 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t1 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i1 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 1788500000000000000000000000 with hb2 | hb2
  · have hlo : (901600000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb1.le
    have hL : 62.0662131 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL7.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.7511749 :=
      ((Real.log_le_log hx0 hb2).trans lgsU8).trans (by norm_num)
    have hya : (184 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (365 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb2 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.67717 (17.77229 * 0.0156446) 1.336799 0.0751596 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t2 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i2 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 4900000000000000000000000000 with hb3 | hb3
  · have hlo : (1788500000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb2.le
    have hL : 62.7511747 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL9.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 63.7590328 :=
      ((Real.log_le_log hx0 hb3).trans lgsU10).trans (by norm_num)
    have hya : (365 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 26) := MN.y_le_of x _ (le_trans hb3 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.66832 (18.07425 * 0.0147789) 1.336166 0.0786585 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t3 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i3 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 49000000000000000000000000000 with hb4 | hb4
  · have hlo : (4900000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb3.le
    have hL : 63.7590326 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL11.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 66.0616179 :=
      ((Real.log_le_log hx0 hb4).trans lgsU12).trans (by norm_num)
    have hya : (10 ^ 26) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 27) := MN.y_le_of x _ (le_trans hb4 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.65566 (18.76404 * 0.0134759) 1.33526 0.0851734 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t4 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i4 _ hya hyb)
      (by norm_num) (by norm_num)
  have hlo : (49000000000000000000000000000 : ℝ) ≤ x := hb4.le
  have hL : 66.0616177 ≤ Real.log x :=
    le_trans (by norm_num) (lgsL13.trans (Real.log_le_log (by norm_num) hlo))
  exact MN.blk 8.54 0.84 0.0447364 18.62825 0.214913 1.333298 0.1087 _ _ _ _ _ hg0 hg hh0
    ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
    (tf x (le_trans (by norm_num) hlo)) hca0
    ((casL_le_of x _ hL (by norm_num)).trans (by norm_num))
    (ifr _ (MN.y_ge_of x _ (le_trans (by norm_num) hlo))) (by norm_num) (by norm_num)

/-- **`OP.MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406`, PROVED.** -/
theorem mnumP_proved : MNumP 0.811 45.7575 HW.phi 8.54 0.84 0.6406 :=
  mnumP_of_links gtNonnegP g0EnvP t1BlkP0 t1BlkP1 t1BlkP2 t1BlkP3 t1BlkP4 iGBlkP0 iGBlkP1
    iGBlkP2 iGBlkP3 iGBlkP4 t1FarP iGFarP

end Principia.Common.TernaryGoldbach.MNP
