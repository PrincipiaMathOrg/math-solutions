/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumPm
import Principia.Common.TernaryGoldbach.MonoTopP

set_option autoImplicit false

/-!
# `OPm.MNumPm 0.896 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406` PROVED (`eq:passi` erratum)

The minor-arc Main Theorem at the erratum's constants is `OP.MinMainP 0.896 45.7575`
(`MTC.minMainPC_of_open`): the Totals constant rises `0.811 ↦ 0.896` because `eq:passi` is false
and `κ₇ ↦ 0.1743` (`TypeIISpineC`). Every consumer of the constant is generic in `c05` except the
`M̃` certificate; this file re-closes it.

**The old certificate does not survive.** `MNP`/`MNPm` raise `MNumL`'s `g̃_L` links by
`1.31395·dP(r)`, `dP = (c05 − 0.5)√ϝ(r)/√(2r) + (C − 22.7538)/r`. At `c05 = 0.896` that gives
worst blocks `0.84415` (`c⁻ = −1.306476`) and `0.84580` (`c⁻ = −1.39`): above `0.84`.

**The fix: a sharper increment, `1.1157` for `1.31395`.** The factor is
`1 + (∫_0^1 w e^{−w²/2} + ∫_1^∞ φ − |φ|₁)/|φ|₁`; `MNP.hi_leP` bounded `∫_1^∞ φ` by `|φ|₁`.
Here `∫_1^∞ φ = √(π/2) − ∫_0^1 w²e^{−w²/2}` (`intervalIntegral.integral_Ioi_sub_Ioi`,
`EN.int_phi`) and `∫_0^1 w²e^{−w²/2} ≥ 1/3 − 1/10 + 1/56 − 1/432 − 5/16896 ≥ 0.24857`
(`phi_head_ge`: the degree-4 Taylor bound of `e^{−v}`, `MC.exp_taylor_cert`), so
`(1 − e^{−1/2} − 0.24857)/√(π/2) ≤ 0.1157` (`gTP_leC`).

Generated from `MNumP.lean` (sections 1-5) and `MNumPm.lean` (sections 2-3) by COUNTED
substitution (`scratchpad/erratum/gen_mnumpc.py`): `0.811 ↦ 0.896`, `0.311 ↦ 0.396`,
`1.31395 ↦ 1.1157`, and the raised numbers

* `dP(r₀) ≤ 0.0018402` (`0.396·0.0042596 + 23.0037/150000`), `dP(r₁) ≤ 0.000568`,
  `∫dP/r ≤ 0.0040762`, far `cf·dP(r₁) ≤ 0.0079`;
* `G₀ 0.0448445`, `T₁` `+0.0006338`, `∫g̃/r` `+0.0045479`, far `T₁ 0.215187`, far `I 0.108997`.

Certified block values against `0.84` at `c⁻ = −1.39` (the `x`-side constants are `MNPm`'s):
`0.83910, 0.83590, 0.83592, 0.82927, 0.82317`, far `0.81550` — smallest margin `0.0009` (first
block). The float `sup M̃` at `0.896` is `0.8266` (`x = 4.9·10²⁶`).

Also supplied at `0.896` for the composition above it: `gYMonoPC`, `hLeGPC`, `gtMonoPC`,
`topStepPC`, `coprarPC_of_R` (the generic `MOP`/`MTOP` lemmas instantiated).
-/

namespace Principia.Common.TernaryGoldbach.MNPC

open MinSp MeasureTheory Set MC Finset
open Principia.Common.TernaryGoldbach.ML
open Principia.Common.TernaryGoldbach.OP
open Principia.Common.TernaryGoldbach.OPm
open Principia.Common.TernaryGoldbach.MNP
open Principia.Common.TernaryGoldbach.MNPm

-- `g̃` and `∫g̃/r` at `(0.896, 45.7575)` on Helfgott's `φ`
local notation "gPh" => gTP 0.896 45.7575 HW.phi
local notation "iPh" => intGTP 0.896 45.7575 HW.phi

/-! ## (0) `∫_1^∞ φ ≤ √(π/2) − 0.24857`, and the monotonicity links at `0.896` -/

/-- **`e^{−v} ≥ 1 − v + v²/2 − v³/6 − (5/96)v⁴`** for `0 ≤ v ≤ 1` (`MC.exp_taylor_cert`,
`n = 4`). -/
theorem exp_quartic (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    1 - v + v ^ 2 / 2 - v ^ 3 / 6 - v ^ 4 * (5 / 96) ≤ Real.exp (-v) := by
  have h := (exp_taylor_cert v 4 hv0 hv1 (by norm_num)).1
  have e : (∑ i ∈ range 4, (-v) ^ i / (i.factorial : ℝ)) -
      v ^ 4 * (((Nat.succ 4 : ℕ) : ℝ) / (((Nat.factorial 4 : ℕ) : ℝ) * (4 : ℕ))) =
      1 - v + v ^ 2 / 2 - v ^ 3 / 6 - v ^ 4 * (5 / 96) := by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    push_cast
    ring
  linarith

/-- **`∫_0^1 w²e^{−w²/2} ≥ 0.24857`** (`w²·exp_quartic(w²/2)` integrated:
`1/3 − 1/10 + 1/56 − 1/432 − 5/16896 = 0.2485797…`). -/
theorem phi_head_ge : 0.24857 ≤ ∫ w in (0 : ℝ)..1, HW.phi w := by
  set cs : List ℝ := [0, 0, 1, 0, -1 / 2, 0, 1 / 8, 0, -1 / 48, 0, -5 / 1536] with hcs
  have hp : ∀ w : ℝ, pevR cs w =
      w ^ 2 - w ^ 4 / 2 + w ^ 6 / 8 - w ^ 8 / 48 - 5 / 1536 * w ^ 10 := by
    intro w
    simp only [hcs, pevR, List.length_cons, List.length_nil, sum_range_succ, sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero]
    ring
  have hle : ∀ w ∈ Icc (0 : ℝ) 1, pevR cs w ≤ HW.phi w := by
    intro w hw
    have hv0 : 0 ≤ w ^ 2 / 2 := by positivity
    have hv1 : w ^ 2 / 2 ≤ 1 := by nlinarith [hw.1, hw.2]
    have h := mul_le_mul_of_nonneg_left (exp_quartic (w ^ 2 / 2) hv0 hv1) (sq_nonneg w)
    rw [hp]
    unfold HW.phi
    have e : -w ^ 2 / 2 = -(w ^ 2 / 2) := by ring
    rw [e]
    have e3 : w ^ 2 - w ^ 4 / 2 + w ^ 6 / 8 - w ^ 8 / 48 - 5 / 1536 * w ^ 10 =
        w ^ 2 * (1 - w ^ 2 / 2 + (w ^ 2 / 2) ^ 2 / 2 - (w ^ 2 / 2) ^ 3 / 6 -
          (w ^ 2 / 2) ^ 4 * (5 / 96)) := by ring
    rw [e3]
    exact h
  have hmono : ∫ w in (0 : ℝ)..1, pevR cs w ≤ ∫ w in (0 : ℝ)..1, HW.phi w :=
    intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      ((continuous_pevR cs).intervalIntegrable _ _)
      ((continuous_mom 2).intervalIntegrable (μ := volume) 0 1) hle
  have hI : ∫ w in (0 : ℝ)..1, pevR cs w = 1 / 3 - 1 / 10 + 1 / 56 - 1 / 432 - 5 / 16896 := by
    rw [int_pevR]
    simp only [hcs, List.length_cons, List.length_nil, sum_range_succ, sum_range_zero,
      List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hI] at hmono
  linarith

/-- **`∫_1^∞ φ ≤ √(π/2) − 0.24857`** (`EN.int_phi`, `phi_head_ge`). -/
theorem phi_tail_le : ∫ w in Ioi (1 : ℝ), HW.phi w ≤ Real.sqrt (Real.pi / 2) - 0.24857 := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi MinSp.phi_integrableOn
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [EN.int_phi] at h
  have := phi_head_ge
  linarith

/-- **The sliver swap at `(0.896, 45.7575)`**: `gYP(Y, 1000) ≤ 1.04488` (`MOP.gYP_1000_le` with
`dP(1000) ≤ 0.396·4/44 + 23.0037/1000 ≤ 0.0591`). -/
theorem gYP_1000_leC (Y : ℝ) (hY : 3.4e23 ≤ Y) : gYP 0.896 45.7575 Y 1000 ≤ 1.04488 := by
  rw [gYP_eq]
  have h1 := MO.gYL_1000_le Y hY
  have hF := MOP.bigF_1000_le
  have hF0 : 0 ≤ MinSp.bigF 1000 := le_trans (by norm_num) (GS.bigF_gt 1000 (by norm_num)).le
  have hsF : Real.sqrt (MinSp.bigF 1000) ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs2000 : 44 ≤ Real.sqrt (2 * 1000) := by
    rw [show (44 : ℝ) = Real.sqrt (44 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have k1 : (0.896 - 0.5) * Real.sqrt (MinSp.bigF 1000) / Real.sqrt (2 * 1000) ≤
      0.396 * 4 / 44 :=
    calc (0.896 - 0.5) * Real.sqrt (MinSp.bigF 1000) / Real.sqrt (2 * 1000)
        ≤ 0.396 * 4 / Real.sqrt (2 * 1000) := by
          apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
          nlinarith [Real.sqrt_nonneg (MinSp.bigF 1000)]
      _ ≤ 0.396 * 4 / 44 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2000
  have k2 : ((45.7575 : ℝ) - 22.7538) / 1000 ≤ 0.0231 := by norm_num
  have k3 : (0.396 : ℝ) * 4 / 44 ≤ 0.036 := by norm_num
  have hd : dP 0.896 45.7575 1000 ≤ 0.0591 := by
    unfold dP
    generalize (0.896 - 0.5) * Real.sqrt (MinSp.bigF 1000) / Real.sqrt (2 * 1000) = A at k1 ⊢
    generalize ((45.7575 : ℝ) - 22.7538) / 1000 = B at k2 ⊢
    linarith
  linarith

/-- **[GYMonoP] at `(0.896, 45.7575)`** (`MOP.gYMonoP_of`, `MO.gYMono`). -/
theorem gYMonoPC : GSP.GYMonoP 0.896 45.7575 :=
  MOP.gYMonoP_of 0.896 45.7575 (by norm_num) (by norm_num) MO.gYMono

/-- **[HLeGP] at `(0.896, 45.7575)`** (`MOP.hLeGP_of`, `MO.hLeG`). -/
theorem hLeGPC : GSP.HLeGP 0.896 45.7575 :=
  MOP.hLeGP_of 0.896 45.7575 (by norm_num) (by norm_num) MO.hLeG

/-- **[GTMonoP] at `(0.896, 45.7575)` on Helfgott's `φ`** (`MOP.gtMonoP_of`). -/
theorem gtMonoPC : GTMonoP 0.896 45.7575 HW.phi :=
  MOP.gtMonoP_of 0.896 45.7575 (by norm_num) (by norm_num) HW.phi (fun t _ => HW.phi_nonneg t)
    MinSp.phi_integrableOn gYMonoPC gYP_1000_leC

/-- **[TopStepP] at `(0.896, 45.7575)`** (`MTOP.topStepP_of`). -/
theorem topStepPC : OSP.TopStepP 0.896 45.7575 HW.phi :=
  MTOP.topStepP_of 0.896 45.7575 (by norm_num) (by norm_num) (by norm_num) HW.phi
    (fun t _ => HW.phi_nonneg t) MinSp.phi_integrableOn

/-- **[CoprarP] at `(0.896, 45.7575)`** from the retyped major arcs (`MOP.coprarP_of_L`). -/
theorem coprarPC_of_R (pf : RT.PlattFull)
    (hm : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) :
    CoprarP 0.896 45.7575 HW.etaStar HW.phi :=
  MOP.coprarP_of_L 0.896 45.7575 (by norm_num) (by norm_num) HW.etaStar HW.phi
    (CP.coprarL_of_R pf hm)

/-! ## (1) The increment `g̃_P − g̃_L ≤ 1.1157·dP(r)` -/
/-- **The `w ≤ 1` integral**: `∫_{w₁}^1 gYP(wy,wr)φ ≤ ∫_{w₁}^1 gYL(wy,wr)φ +
dP(r)(1 − 0.6065306597)` (`w₁ = max(1/K, 1000/r)`; both integrands integrable, `GS.gtlInt`,
`GSP.gtlIntP`). -/
theorem lo_lePC (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 150000 ≤ r) (hr1 : r ≤ r1y y) :
    ∫ w in (max (1 / kK y) (1000 / r))..1, gYP 0.896 45.7575 (w * y) (w * r) * HW.phi w ≤
      (∫ w in (max (1 / kK y) (1000 / r))..1, OL.gYL (w * y) (w * r) * HW.phi w) +
        dP 0.896 45.7575 r * (1 - 0.6065306597) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨-, -, hm1⟩ := w1_facts y r hy (by linarith)
  have hw1 : 1000 / r ≤ max (1 / kK y) (1000 / r) := le_max_right _ _
  have hw11 : max (1 / kK y) (1000 / r) ≤ 1 := hm1.trans (by norm_num)
  have hw10 : 0 < max (1 / kK y) (1000 / r) := lt_of_lt_of_le (by positivity) hw1
  obtain ⟨iL, -⟩ := GS.gtlInt HW.phi MinSp.phi_integrableOn y hy r hr hr1
  obtain ⟨iP, -⟩ := GSP.gtlIntP 0.896 45.7575 (by norm_num) (by norm_num) HW.phi
    MinSp.phi_integrableOn y hy r hr hr1
  have hIL : IntervalIntegrable (fun w => OL.gYL (w * y) (w * r) * HW.phi w) volume
      (max (1 / kK y) (1000 / r)) 1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hw11).mpr iL
  have hIP : IntervalIntegrable (fun w => gYP 0.896 45.7575 (w * y) (w * r) * HW.phi w) volume
      (max (1 / kK y) (1000 / r)) 1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hw11).mpr iP
  have hD0 : 0 ≤ dP 0.896 45.7575 r := dP_nonneg _ _ r (by norm_num) (by norm_num) hr0.le
  have hmi : IntervalIntegrable
      (fun w : ℝ => dP 0.896 45.7575 r * (w ^ 1 * Real.exp (-w ^ 2 / 2))) volume
      (max (1 / kK y) (1000 / r)) 1 :=
    ((continuous_mom 1).const_mul _).intervalIntegrable _ _
  have h1 : ∫ w in (max (1 / kK y) (1000 / r))..1,
      (gYP 0.896 45.7575 (w * y) (w * r) * HW.phi w - OL.gYL (w * y) (w * r) * HW.phi w) ≤
      ∫ w in (max (1 / kK y) (1000 / r))..1,
        dP 0.896 45.7575 r * (w ^ 1 * Real.exp (-w ^ 2 / 2)) := by
    refine intervalIntegral.integral_mono_on hw11 (hIP.sub hIL) hmi fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hw10 hw.1
    have hwr : 1000 ≤ w * r := by
      have h := mul_le_mul_of_nonneg_right (hw1.trans hw.1) hr0.le
      rwa [div_mul_cancel₀ _ hr0.ne'] at h
    have hk := dPlo_le 0.896 45.7575 r w (by norm_num) (by norm_num) hr0 hw0 hw.2 (by linarith)
    calc gYP 0.896 45.7575 (w * y) (w * r) * HW.phi w - OL.gYL (w * y) (w * r) * HW.phi w
        = dP 0.896 45.7575 (w * r) * HW.phi w := by rw [gYP_eq]; ring
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

/-- **The `w > 1` integral, sharpened**: `∫_{w>1} gYP(wy,r)φ ≤ ∫_{w>1} gYL(wy,r)φ +
dP(r)(√(π/2) − 0.24857)` (`MNP.hi_leP` with `phi_tail_le` for `∫_1^∞ φ ≤ |φ|₁`). -/
theorem hi_lePC (y r : ℝ) (hr : 150000 ≤ r) :
    ∫ w in Ioi (1 : ℝ), gYP 0.896 45.7575 (w * y) r * HW.phi w ≤
      (∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * HW.phi w) +
        dP 0.896 45.7575 r * (Real.sqrt (Real.pi / 2) - 0.24857) := by
  have hr0 : 0 < r := by linarith
  set D := dP 0.896 45.7575 r with hD
  have hDn : 0 ≤ D := dP_nonneg _ _ r (by norm_num) (by norm_num) hr0.le
  obtain ⟨hs1, -⟩ := MajSp.sqrt_pi_half
  have hs0 : 0 ≤ Real.sqrt (Real.pi / 2) - 0.24857 := by linarith
  set fC : ℝ → ℝ := fun w => OL.gYL (w * y) r * HW.phi w with hfC
  have hsplit : (fun w => gYP 0.896 45.7575 (w * y) r * HW.phi w) =
      fun w => fC w + D * HW.phi w := by
    funext w
    rw [hfC, hD, gYP_eq]
    ring
  have hpi : IntegrableOn HW.phi (Ioi (1 : ℝ)) :=
    MinSp.phi_integrableOn.mono_set (Ioi_subset_Ioi zero_le_one)
  have hDI : ∫ w in Ioi (1 : ℝ), D * HW.phi w ≤ D * (Real.sqrt (Real.pi / 2) - 0.24857) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left phi_tail_le hDn
  have hB0 : 0 ≤ D * (Real.sqrt (Real.pi / 2) - 0.24857) := mul_nonneg hDn hs0
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

/-- **THE INCREMENT, sharpened**: `g̃_P(y, r) ≤ g̃_L(y, r) + 1.1157·dP(r)` on `[150000, r₁(y)]`,
`y ≥ 10²⁵` (`lo_lePC`, `hi_lePC`: `(1 − 0.6065306597 − 0.24857)/1.2533139 ≤ 0.1157`). -/
theorem gTP_leC (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 150000 ≤ r) (hr1 : r ≤ r1y y) :
    gPh y r ≤ OL.gTL HW.phi y r + 1.1157 * dP 0.896 45.7575 r := by
  have hr0 : 0 < r := by linarith
  have h1 := lo_lePC y r hy hr hr1
  have h2 := hi_lePC y r hr
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  obtain ⟨hs1, -⟩ := MajSp.sqrt_pi_half
  have hD0 : 0 ≤ dP 0.896 45.7575 r := dP_nonneg _ _ r (by norm_num) (by norm_num) hr0.le
  unfold gTP OL.gTL
  rw [hl1]
  set Sq := Real.sqrt (Real.pi / 2) with hSq
  set D := dP 0.896 45.7575 r with hD
  have hSq0 : 0 < Sq := lt_of_lt_of_le (by norm_num) hs1
  set IP := ∫ w in (max (1 / kK y) (1000 / r))..1, gYP 0.896 45.7575 (w * y) (w * r) * HW.phi w
  set IH := ∫ w in Ioi (1 : ℝ), gYP 0.896 45.7575 (w * y) r * HW.phi w
  set JL := ∫ w in (max (1 / kK y) (1000 / r))..1, OL.gYL (w * y) (w * r) * HW.phi w
  set JH := ∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * HW.phi w
  set S := 1.04488 * ∫ w in (1 / kK y)..(max (1 / kK y) (1000 / r)), |HW.phi w|
  have hk : D * (1 - 0.6065306597 - 0.24857) / Sq ≤ D * 0.1157 := by
    rw [div_le_iff₀ hSq0]
    nlinarith
  calc (IP + IH + S) / Sq ≤ (JL + JH + S + D * (1 - 0.6065306597) + D * (Sq - 0.24857)) / Sq :=
        div_le_div_of_nonneg_right (by linarith) hSq0.le
    _ = (JL + JH + S) / Sq + D * (1 - 0.6065306597 - 0.24857) / Sq + D := by
        field_simp
        ring
    _ ≤ (JL + JH + S) / Sq + 1.1157 * D := by linarith

/-! ## (2) The numbers at `0.896` -/
/-- **`dP(r₀) ≤ 0.0018402`** at `(0.896, 45.7575)`: `0.396·0.0042596 + 23.0037/150000`. -/
theorem dP_r0_leC : dP 0.896 45.7575 150000 ≤ 0.0018402 := by
  have h := s0_le
  unfold dP
  rw [mul_div_assoc]
  generalize Real.sqrt (MinSp.bigF 150000) / Real.sqrt (2 * 150000) = S at h ⊢
  norm_num
  linarith

/-- **`dP(r₁(y)) ≤ 0.000568`** for `y ≥ 10²⁵` (`dP` antitone, `dP(1.5·10⁶) ≤ 0.000568`:
`ϝ ≤ 3.6544 + 0.15003·21 log 2`). -/
theorem dP_r1_leC (y : ℝ) (hy : 10 ^ 25 ≤ y) : dP 0.896 45.7575 (r1y y) ≤ 0.000568 := by
  have hr := r1y_ge y hy
  have hanti := MOP.dP_anti 0.896 45.7575 1.5e6 (r1y y) (by norm_num) (by norm_num) (by norm_num)
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

/-- **The decay of `dP`**: `dP(r) ≤ dP(r₀)·e^{−0.43(log r − log r₀)}` for `r ≥ r₀` (the `1/r`
summand decays like `e^{−(log r − log r₀)}`, faster). -/
theorem dP_decayC (r : ℝ) (hr : 150000 ≤ r) :
    dP 0.896 45.7575 r ≤
      dP 0.896 45.7575 150000 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) := by
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
  have k1 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 0.896 - 0.5)
  have k2 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 45.7575 - 22.7538)
  generalize Real.exp (-0.43 * (Real.log r - Real.log 150000)) = E at k1 k2 ⊢
  generalize Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) = S at k1 ⊢
  generalize Real.sqrt (MinSp.bigF 150000) / Real.sqrt (2 * 150000) = S0 at k1 ⊢
  generalize (1 : ℝ) / r = u at k2 ⊢
  nlinarith

/-- **The split decay of `dP`**: `dP(r) ≤ 0.396·0.0042596·e^{−0.43(log r − log r₀)} + 23.0037/r`
(`sqrtF_decay`, `s0_le`). -/
theorem dP_le_decayC (r : ℝ) (hr : 150000 ≤ r) :
    dP 0.896 45.7575 r ≤ 0.396 * 0.0042596 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) +
      (45.7575 - 22.7538) * (1 / r) := by
  have hs := sqrtF_decay r hr
  have h0 := s0_le
  have hE0 := Real.exp_pos (-0.43 * (Real.log r - Real.log 150000))
  unfold dP
  rw [mul_div_assoc, div_eq_mul_one_div (45.7575 - 22.7538) r]
  have k : (0.896 - 0.5) * (Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r)) ≤
      0.396 * 0.0042596 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) := by
    have k1 := mul_le_mul_of_nonneg_right h0 hE0.le
    have k2 : (0.896 - 0.5 : ℝ) = 0.396 := by norm_num
    rw [k2]
    nlinarith
  linarith

/-- **`∫_{r₀}^{r₁} g̃_P/r ≤ ∫_{r₀}^{r₁} g̃_L/r + 1.1157·0.0040762`** for `y ≥ 10²⁵`: `gTP_leC`,
`dP_le_decayC`, `int_decay`, `int_inv_sq`
(`0.396·0.0042596/0.43 + 23.0037/150000 ≤ 0.0040762`). Both
integrands are antitone, hence integrable (`gtMonoPC`, `MO.gtMonoL_helf`, `OS.gdiv_int`). -/
theorem intGTP_leC (y : ℝ) (hy : 10 ^ 25 ≤ y) :
    iPh y ≤ OL.intGTL HW.phi y + 1.1157 * 0.0040762 := by
  have hab : (150000 : ℝ) ≤ r1y y := le_trans (by norm_num) (r1y_ge y hy)
  have iP := OS.gdiv_int _ _ _ (by norm_num) hab (gtMonoPC y hy)
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
  have iB := iL.add ((iE.const_mul (1.1157 * (0.396 * 0.0042596))).add
    (iQ.const_mul (1.1157 * (45.7575 - 22.7538))))
  have hle := intervalIntegral.integral_mono_on hab iP iB fun r hr => by
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
    have hr0' : r ≠ 0 := hr0.ne'
    have hg := gTP_leC y r hy hr.1 hr.2
    have hd := dP_le_decayC r hr.1
    change gPh y r / r ≤ OL.gTL HW.phi y r / r +
      (1.1157 * (0.396 * 0.0042596) *
          (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) +
        1.1157 * (45.7575 - 22.7538) * (1 / r ^ 2))
    have e : (0.396 * 0.0042596 * Real.exp (-0.43 * (Real.log r - Real.log 150000)) +
        (45.7575 - 22.7538) * (1 / r)) / r =
        0.396 * 0.0042596 * (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) +
          (45.7575 - 22.7538) * (1 / r ^ 2) := by
      field_simp
    have hdr : dP 0.896 45.7575 r / r ≤
        0.396 * 0.0042596 * (Real.exp (-0.43 * (Real.log r - Real.log 150000)) / r) +
          (45.7575 - 22.7538) * (1 / r ^ 2) := by
      rw [← e]
      exact div_le_div_of_nonneg_right hd hr0.le
    calc gPh y r / r ≤ (OL.gTL HW.phi y r + 1.1157 * dP 0.896 45.7575 r) / r :=
          div_le_div_of_nonneg_right hg hr0.le
      _ = OL.gTL HW.phi y r / r + 1.1157 * (dP 0.896 45.7575 r / r) := by ring
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

/-- **The far regime**: `cf(x)·dP(r₁(x/49)) ≤ 0.0079` for `x ≥ 4.9·10²⁸`:
`cf ≤ (7/15)·0.6406 log x`, `dP(r₁) ≤ dP(r₀)e^{−0.43(log r₁ − log r₀)}`,
`log r₁ = log(3/8) + (4/15)(log x − log 49)`, and
`log x·e^{−(0.43·4/15)(log x − L₀)} ≤ L₀ = log(4.9·10²⁸) ≤ 66.0616179` (`decayL`). -/
theorem far_leC (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    cfL x * dP 0.896 45.7575 (r1y (x / 49)) ≤ 0.0079 := by
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
  have hd := dP_decayC (r1y (x / 49)) (by linarith)
  have hd0 := dP_r0_leC
  have hdn : 0 ≤ dP 0.896 45.7575 (r1y (x / 49)) :=
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
  calc cfL x * dP 0.896 45.7575 (r1y (x / 49))
      ≤ 7 / 15 * (0.6406 * L) * dP 0.896 45.7575 (r1y (x / 49)) :=
        mul_le_mul_of_nonneg_right hcf hdn
    _ ≤ 7 / 15 * (0.6406 * L) * (0.0018402 * (Real.exp (-0.43 * A) *
          Real.exp (-(0.43 * 4 / 15 * (L - L0))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hsplit]
        exact hd.trans (mul_le_mul_of_nonneg_right hd0 (Real.exp_pos _).le)
    _ = 7 / 15 * 0.6406 * 0.0018402 * Real.exp (-0.43 * A) *
          (L * Real.exp (-(0.43 * 4 / 15 * (L - L0)))) := by ring
    _ ≤ 7 / 15 * 0.6406 * 0.0018402 * 0.2164 * 66.0616179 := by
        have hLd : L * Real.exp (-(0.43 * 4 / 15 * (L - L0))) ≤ 66.0616179 :=
          hdecay.trans (hL0u.trans (by norm_num))
        have k : Real.exp (-0.43 * A) * (L * Real.exp (-(0.43 * 4 / 15 * (L - L0)))) ≤
            0.2164 * 66.0616179 :=
          mul_le_mul hexpA hLd (mul_nonneg hL00 (Real.exp_pos _).le) (by norm_num)
        have hc : (0 : ℝ) ≤ 7 / 15 * 0.6406 * 0.0018402 := by norm_num
        calc 7 / 15 * 0.6406 * 0.0018402 * Real.exp (-0.43 * A) *
              (L * Real.exp (-(0.43 * 4 / 15 * (L - L0))))
            = 7 / 15 * 0.6406 * 0.0018402 *
                (Real.exp (-0.43 * A) * (L * Real.exp (-(0.43 * 4 / 15 * (L - L0))))) := by ring
          _ ≤ 7 / 15 * 0.6406 * 0.0018402 * (0.2164 * 66.0616179) :=
              mul_le_mul_of_nonneg_left k hc
          _ = _ := by ring
    _ ≤ 0.0079 := by norm_num

/-- **Link [g̃_P ≥ 0]**. -/
def GTNonnegPC : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → 0 ≤ gPh y 150000

/-- **Link [g̃_P(r₀)]**. -/
def G0EnvPC (G : ℝ) : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → gPh y 150000 ≤ G

/-- **Link [g̃_P(r₁)] on a block**. -/
def T1BlkPC (ya yb T : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → gPh y (r1y y) ≤ T

/-- **Link [∫g̃_P/r] on a block**. -/
def IGBlkPC (ya yb I : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → iPh y ≤ I

/-- **Link [far g̃_P(r₁)]**. -/
def T1FarPC (T : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 27 ≤ x → cfL x * gPh (x / 49) (r1y (x / 49)) ≤ T

/-- **Link [far ∫g̃_P/r]**. -/
def IGFarPC (I : ℝ) : Prop := ∀ y : ℝ, 10 ^ 27 ≤ y → iPh y ≤ I

/-- **[g̃_P ≥ 0]** from `ML.gtNonnegL` and `g̃_L ≤ g̃_P` (`MOP.gTL_le_gTP`). -/
theorem gtNonnegPC : GTNonnegPC := fun y hy =>
  le_trans (gtNonnegL y hy) (MOP.gTL_le_gTP 0.896 45.7575 (by norm_num) (by norm_num) HW.phi
    (fun t _ => HW.phi_nonneg t) MinSp.phi_integrableOn y hy 150000 le_rfl (r0_le_r1 y hy))

/-- **[g̃_P(r₀)] at `0.0448445`**: `0.0427913 + 1.1157·0.0018402`. -/
theorem g0EnvPC : G0EnvPC 0.0448445 := fun y hy => by
  have h1 := gTP_leC y 150000 hy le_rfl (r0_le_r1 y hy)
  have h2 := g0EnvL y hy
  have h3 := dP_r0_leC
  linarith

/-- The `T₁` increment on every block: `g̃_P(y, r₁) ≤ g̃_L(y, r₁) + 0.0006338`. -/
theorem t1_stepC (y : ℝ) (hy : 10 ^ 25 ≤ y) :
    gPh y (r1y y) ≤ OL.gTL HW.phi y (r1y y) + 0.0006338 := by
  have h1 := gTP_leC y (r1y y) hy (r0_le_r1 y hy) le_rfl
  have h2 := dP_r1_leC y hy
  linarith

/-- The `∫g̃/r` increment: `∫g̃_P/r ≤ ∫g̃_L/r + 0.0045479`. -/
theorem ig_stepC (y : ℝ) (hy : 10 ^ 25 ≤ y) : iPh y ≤ OL.intGTL HW.phi y + 0.0045479 := by
  have h := intGTP_leC y hy
  linarith

/-- **[g̃_P(r₁)] on block 0**: `0.0157963 + 0.0006338` (`ML.t1BlkL0`, `t1_stepC`). -/
theorem t1BlkP0C : T1BlkPC (10 ^ 25) (13 * 10 ^ 24) 0.0164301 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_stepC y hy
  have b := t1BlkL0 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 0**: `0.0669295 + 0.0045479` (`ML.iGBlkL0`, `ig_stepC`). -/
theorem iGBlkP0C : IGBlkPC (10 ^ 25) (13 * 10 ^ 24) 0.0714774 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_stepC y hy
  have b := iGBlkL0 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 1**: `0.0154199 + 0.0006338` (`ML.t1BlkL1`, `t1_stepC`). -/
theorem t1BlkP1C : T1BlkPC (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0160537 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_stepC y hy
  have b := t1BlkL1 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 1**: `0.0683159 + 0.0045479` (`ML.iGBlkL1`, `ig_stepC`). -/
theorem iGBlkP1C : IGBlkPC (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0728638 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_stepC y hy
  have b := iGBlkL1 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 2**: `0.0150526 + 0.0006338` (`ML.t1BlkL2`, `t1_stepC`). -/
theorem t1BlkP2C : T1BlkPC (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0156864 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_stepC y hy
  have b := t1BlkL2 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 2**: `0.0709086 + 0.0045479` (`ML.iGBlkL2`, `ig_stepC`). -/
theorem iGBlkP2C : IGBlkPC (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0754565 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_stepC y hy
  have b := iGBlkL2 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 3**: `0.0141869 + 0.0006338` (`ML.t1BlkL3`, `t1_stepC`). -/
theorem t1BlkP3C : T1BlkPC (365 * 10 ^ 23) (10 ^ 26) 0.0148207 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_stepC y hy
  have b := t1BlkL3 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 3**: `0.0744075 + 0.0045479` (`ML.iGBlkL3`, `ig_stepC`). -/
theorem iGBlkP3C : IGBlkPC (365 * 10 ^ 23) (10 ^ 26) 0.0789554 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_stepC y hy
  have b := iGBlkL3 y h1 h2
  linarith

/-- **[g̃_P(r₁)] on block 4**: `0.0128839 + 0.0006338` (`ML.t1BlkL4`, `t1_stepC`). -/
theorem t1BlkP4C : T1BlkPC (10 ^ 26) (10 ^ 27) 0.0135177 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := t1_stepC y hy
  have b := t1BlkL4 y h1 h2
  linarith

/-- **[∫g̃_P/r] on block 4**: `0.0809224 + 0.0045479` (`ML.iGBlkL4`, `ig_stepC`). -/
theorem iGBlkP4C : IGBlkPC (10 ^ 26) (10 ^ 27) 0.0854703 := fun y h1 h2 => by
  have hy : 10 ^ 25 ≤ y := le_trans (by norm_num) h1
  have a := ig_stepC y hy
  have b := iGBlkL4 y h1 h2
  linarith

/-- **[far g̃_P(r₁)] at `0.215187`**: `0.206372 + 1.1157·0.0079` (`ML.t1FarL`, `far_leC`). -/
theorem t1FarPC : T1FarPC 0.215187 := fun x hx => by
  have hx26 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hy := y_ge x hx26
  have h1 := gTP_leC (x / 49) (r1y (x / 49)) hy (r0_le_r1 _ hy) le_rfl
  have hcf0 := cfL_nonneg x hx26
  have h2 := t1FarL x hx
  have h3 := far_leC x hx
  have h4 := mul_le_mul_of_nonneg_left h1 hcf0
  nlinarith

/-- **[far ∫g̃_P/r] at `0.108997`**: `0.104449 + 0.0045479` (`ML.iGFarL`). -/
theorem iGFarPC : IGFarPC 0.108997 := fun y hy => by
  have h1 := ig_stepC y (le_trans (by norm_num) hy)
  have h2 := iGFarL y hy
  linarith

/-- **The far `g̃_P(r₁)` link at `c⁻ = −1.39`** from `MNP.T1FarP`: `cfLm ≤ cfL` and
`g̃_P(r₁) ≥ 0` (`OSP.gTP_nonneg`, `r₁ ≥ 1.5·10⁶`). -/
theorem t1FarPmC_of (T : ℝ) (tf : T1FarPC T) (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    cfLm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49)) ≤ T := by
  have hx26 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hy := y_ge x hx26
  have hr1 := MNP.r1y_ge (x / 49) hy
  have hg : 0 ≤ gPh (x / 49) (r1y (x / 49)) :=
    OSP.gTP_nonneg 0.896 45.7575 (by norm_num) (by norm_num) HW.phi (fun t _ => HW.phi_nonneg t)
      _ _ hy (by linarith) le_rfl
  exact (mul_le_mul_of_nonneg_right (cfLm_le_cfL x hx26) hg).trans (tf x hx)

/-- **The affine reduction** at `(1.39, −3.627308)` (generated from `MNP.mnumP_of_felipa`). -/
theorem mnumPmC_of_felipa (p0 c : ℝ) (hp0 : 0 ≤ p0) (hc : 0 ≤ c) (hg : GTNonnegPC)
    (hM : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      gPh (x / 49) 150000 * (hsLm 1.39 x - p0) +
        cfLm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49)) + casLm 1.39 x * iPh (x / 49) ≤
          c) :
    MNumPm 0.896 45.7575 1.39 (-3.627308) HW.phi p0 c 0.6406 := by
  intro x hx s p hs0 hs1 hp
  refine MN.affine_step _ _ _ _ s p p0 c (hg (x / 49) (y_ge x hx)) hp0 hs0 hs1 hp hc ?_
  have e : gPh (x / 49) 150000 * (hsLm 1.39 x - p0) +
        cfLm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49)) + casLm 1.39 x * iPh (x / 49) =
      gPh (x / 49) 150000 * (hR0Cm 1.39 x * (0.6406 * Real.log x - 0.021095) - p0) +
        (2 / (Real.log x - 2 * 1.39) * iPh (x / 49) +
          coefCm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49))) *
          (0.6406 * Real.log x - 0.021095) := by
    unfold hsLm cfLm casLm felL
    ring
  rw [← e]
  exact hM x hx

/-- **THE SPINE of `OPm.MNumPm 0.896 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406`**
(generated from `MNP.mnumP_of_links`: the SAME `g̃_P` links, every block re-closed with the
`x`-side at `c⁻ = −1.39`). -/
theorem mnumPmC_of_links (g0 : GTNonnegPC) (e0 : G0EnvPC 0.0448445)
    (t0 : T1BlkPC (10 ^ 25) (13 * 10 ^ 24) 0.0164301)
    (t1 : T1BlkPC (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0160537)
    (t2 : T1BlkPC (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0156864)
    (t3 : T1BlkPC (365 * 10 ^ 23) (10 ^ 26) 0.0148207) (t4 : T1BlkPC (10 ^ 26) (10 ^ 27) 0.0135177)
    (i0 : IGBlkPC (10 ^ 25) (13 * 10 ^ 24) 0.0714774)
    (i1 : IGBlkPC (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0728638)
    (i2 : IGBlkPC (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0754565)
    (i3 : IGBlkPC (365 * 10 ^ 23) (10 ^ 26) 0.0789554) (i4 : IGBlkPC (10 ^ 26) (10 ^ 27) 0.0854703)
    (tf : T1FarPC 0.215187) (ifr : IGFarPC 0.108997) :
    MNumPm 0.896 45.7575 1.39 (-3.627308) HW.phi 8.54 0.84 0.6406 := by
  refine mnumPmC_of_felipa 8.54 0.84 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hx0 := x_pos x hx
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hg := e0 (x / 49) (y_ge x hx)
  have hh0 := hsLm_ge x hx
  have hca0 := casLm_nonneg x hx
  have hcf0 := cfLm_nonneg x hx
  rcases le_or_gt x 637000000000000000000000000 with hb0 | hb0
  · have hlo : (490000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hx
    have hL : 61.4564475 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL1.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 61.718812 :=
      ((Real.log_le_log hx0 hb0).trans lgsU4).trans (by norm_num)
    have hya : (10 ^ 25) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (13 * 10 ^ 24) := MN.y_le_of x _ (le_trans hb0 (by norm_num))
    exact MN.blk 8.54 0.84 0.0448445 18.73841 (17.40046 * 0.0164301) 1.341183 0.0714774 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t0 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i0 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 901600000000000000000000000 with hb1 | hb1
  · have hlo : (637000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb0.le
    have hL : 61.7188118 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL5.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.0662133 :=
      ((Real.log_le_log hx0 hb1).trans lgsU6).trans (by norm_num)
    have hya : (13 * 10 ^ 24) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (184 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb1 (by norm_num))
    exact MN.blk 8.54 0.84 0.0448445 18.73468 (17.50459 * 0.0160537) 1.340916 0.0728638 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t1 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i1 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 1788500000000000000000000000 with hb2 | hb2
  · have hlo : (901600000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb1.le
    have hL : 62.0662131 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL7.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.7511749 :=
      ((Real.log_le_log hx0 hb2).trans lgsU8).trans (by norm_num)
    have hya : (184 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (365 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb2 (by norm_num))
    exact MN.blk 8.54 0.84 0.0448445 18.72979 (17.70988 * 0.0156864) 1.340566 0.0754565 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t2 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i2 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 4900000000000000000000000000 with hb3 | hb3
  · have hlo : (1788500000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb2.le
    have hL : 62.7511747 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL9.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 63.7590328 :=
      ((Real.log_le_log hx0 hb3).trans lgsU10).trans (by norm_num)
    have hya : (365 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 26) := MN.y_le_of x _ (le_trans hb3 (by norm_num))
    exact MN.blk 8.54 0.84 0.0448445 18.72032 (18.01193 * 0.0148207) 1.339888 0.0789554 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t3 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i3 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 49000000000000000000000000000 with hb4 | hb4
  · have hlo : (4900000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb3.le
    have hL : 63.7590326 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL11.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 66.0616179 :=
      ((Real.log_le_log hx0 hb4).trans lgsU12).trans (by norm_num)
    have hya : (10 ^ 26) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 27) := MN.y_le_of x _ (le_trans hb4 (by norm_num))
    exact MN.blk 8.54 0.84 0.0448445 18.70677 (18.70191 * 0.0135177) 1.338918 0.0854703 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t4 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i4 _ hya hyb)
      (by norm_num) (by norm_num)
  have hlo : (49000000000000000000000000000 : ℝ) ≤ x := hb4.le
  have hL : 66.0616177 ≤ Real.log x :=
    le_trans (by norm_num) (lgsL13.trans (Real.log_le_log (by norm_num) hlo))
  exact MN.blk 8.54 0.84 0.0448445 18.67743 0.215187 1.336818 0.108997 _ _ _ _ _ hg0 hg hh0
    ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
    (t1FarPmC_of _ tf x (le_trans (by norm_num) hlo)) hca0
    ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num))
    (ifr _ (MN.y_ge_of x _ (le_trans (by norm_num) hlo))) (by norm_num) (by norm_num)

/-- **`OPm.MNumPm 0.896 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406`, PROVED** from
the sharpened links above; smallest certified margin `0.0009` (first block). -/
theorem mnumPmC_proved : MNumPm 0.896 45.7575 1.39 (-3.627308) HW.phi 8.54 0.84 0.6406 :=
  mnumPmC_of_links gtNonnegPC g0EnvPC t1BlkP0C t1BlkP1C t1BlkP2C t1BlkP3C t1BlkP4C iGBlkP0C iGBlkP1C
    iGBlkP2C iGBlkP3C iGBlkP4C t1FarPC iGFarPC

end Principia.Common.TernaryGoldbach.MNPC
