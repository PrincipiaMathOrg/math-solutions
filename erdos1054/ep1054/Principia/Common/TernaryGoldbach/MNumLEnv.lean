/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopL
import Principia.Common.TernaryGoldbach.MNumCProofs

set_option autoImplicit false

/-!
# `MNumL` toolkit: the corrected `L` as an additive `1/r` term on `MC`'s envelopes

`OL.gYL` is `OC.gY` with `OL.lLc` in place of `MinSp.lL` and nothing else changed, and
`lLc t − lL t = (1.7984 − 16/9) log 2 + (13.6516 − 80/9) log t + (22.7538 − 111/5)` (`dL_eq`), at
most `0.568095 + 4.762712 log t` for `t ≥ 1` (`dL_bounds`). So the corrected `g̃` is the printed one
plus the `φ`-average of a term `(a + b log(·))/(·)`:

* **`gTL_le`**: `gTL(y, r) ≤ gT(y, r) + 1.31395 (0.568095 + 4.762712 log r)/r` for `y ≥ 10²⁵`,
  `r ≥ 150000`. The `w ≤ 1` part costs at most `(1 − e^{−1/2})/|φ|₁ ≤ 0.31395` of `D̄(r)/r`
  (`log w ≤ 0` is dropped, then `∫ w e^{−w²/2} = e^{−w₁²/2} − e^{−1/2}`, `MC.mJ_one`, `MC.ex_1`),
  the `w > 1` part at most `1` (`∫_{w>1} φ ≤ |φ|₁`). No continuity of `g_Y` is used: when the
  printed integrand is not integrable, neither is the corrected one, and both integrals are `0`.
* **`envL_of`**: so every region envelope `MC.envR…` of the printed `g̃` (`P(ℓ)/√r + Q(ℓ)/r + z`)
  is an envelope of the corrected `g̃` once `q₀ += 1.31395·0.568095`, `q₁ += 1.31395·4.762712`;
  `envL_pos_of` keeps its nonnegativity. The five instances `envLR0` … `envLRF` are generated.
* **`gTL_nonneg_r0`**: `g̃_L(y, r₀) ≥ 0`, every integrand being `≥ 0` (`gYL_nonneg`).

The exact size of the correction's average is `≈ 1.1152 D̄(r)/r`; the bound `1.31395` gives away
`≈ 0.2 D̄(r)/r`, about `0.001` of `M̃` at `x = 4.9·10²⁶`.
-/

namespace Principia.Common.TernaryGoldbach.ML

open MinSp MeasureTheory Set MC

/-! ## (1) The correction of `L` -/

/-- **`g_Y` on the corrected `L` is `OC.gY` plus `(L_c(r) − L(r))/r`** (`OL.gYL_eq_at`,
`OL.gY_eq_at`: the two differ in the `L` summand only). -/
theorem gYL_eq (Y r : ℝ) : OL.gYL Y r = OC.gY Y r + (OL.lLc r - lL r) / r := by
  rw [OL.gYL_eq_at, OL.gY_eq_at]
  unfold OL.gYAt
  ring

/-- **`L_c(t) − L(t)`** in closed form for `t > 0` (`OL.lLc_eq`). -/
theorem dL_eq (t : ℝ) (ht : 0 < t) :
    OL.lLc t - lL t = (1.7984 - 16 / 9) * Real.log 2 + (13.6516 - 80 / 9) * Real.log t +
      (22.7538 - 111 / 5) := by
  rw [OL.lLc_eq, OL.log_two_rpow_mul _ _ t ht, OL.log_two_rpow_mul _ _ t ht]
  ring

/-- **`0 ≤ L_c(t) − L(t) ≤ 0.568095 + 4.762712 log t`** for `t ≥ 1` (`log 2 < 0.6931471808`). -/
theorem dL_bounds (t : ℝ) (ht : 1 ≤ t) :
    0 ≤ OL.lLc t - lL t ∧ OL.lLc t - lL t ≤ 0.568095 + 4.762712 * Real.log t := by
  have hl := Real.log_nonneg ht
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  rw [dL_eq t (by linarith)]
  constructor <;> linarith

/-- **The `w ≤ 1` correction, pointwise**: for `0 < w ≤ 1`, `wr ≥ 1`,
`(L_c(wr) − L(wr))/(wr)·φ(w) ≤ D̄(r)/r · w e^{−w²/2}`, `D̄(r) = 0.568095 + 4.762712 log r`. -/
theorem dlo_le (r w : ℝ) (hr : 0 < r) (hw : 0 < w) (hw1 : w ≤ 1) (hwr : 1 ≤ w * r) :
    (OL.lLc (w * r) - lL (w * r)) / (w * r) * HW.phi w ≤
      (0.568095 + 4.762712 * Real.log r) / r * (w ^ 1 * Real.exp (-w ^ 2 / 2)) := by
  have hlw : Real.log w ≤ 0 := Real.log_nonpos hw.le hw1
  have hr1 : 1 ≤ r := by nlinarith
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have h2 := Real.log_two_lt_d9
  rw [dL_eq (w * r) (mul_pos hw hr), Real.log_mul hw.ne' hr.ne']
  unfold HW.phi
  set X := (1.7984 - 16 / 9) * Real.log 2 + (13.6516 - 80 / 9) * (Real.log w + Real.log r) +
    (22.7538 - 111 / 5) with hX
  have key : X ≤ 0.568095 + 4.762712 * Real.log r := by
    rw [hX]
    linarith
  have e : X / (w * r) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) =
      X / r * (w ^ 1 * Real.exp (-w ^ 2 / 2)) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right key hr.le) (by positivity)

/-- **The `w ≤ 1` integral**: `∫_{w₁}^1 g_{wy}(wr)φ` on the corrected `L` exceeds the printed one
by at most `D̄(r)/r·(1 − 0.6065306597)`, for `1000/r ≤ w₁ ≤ 1`. -/
theorem lo_le (y r w1 : ℝ) (hr : 150000 ≤ r) (hw1 : 1000 / r ≤ w1) (hw11 : w1 ≤ 1) :
    ∫ w in w1..1, OL.gYL (w * y) (w * r) * HW.phi w ≤
      (∫ w in w1..1, OC.gY (w * y) (w * r) * HW.phi w) +
        (0.568095 + 4.762712 * Real.log r) / r * (1 - 0.6065306597) := by
  have hr0 : 0 < r := by linarith
  have hlr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hw10 : 0 < w1 := lt_of_lt_of_le (by positivity) hw1
  set C := (0.568095 + 4.762712 * Real.log r) / r with hC
  have hC0 : 0 ≤ C := div_nonneg (by linarith) hr0.le
  set d : ℝ → ℝ := fun w => (OL.lLc (w * r) - lL (w * r)) / (w * r) * HW.phi w with hd
  set fC : ℝ → ℝ := fun w => OC.gY (w * y) (w * r) * HW.phi w with hfC
  have hsplit : (fun w => OL.gYL (w * y) (w * r) * HW.phi w) = fun w => fC w + d w := by
    funext w
    rw [hfC, hd, gYL_eq]
    ring
  have hmem : ∀ w ∈ uIcc w1 1, 0 < w ∧ w ≤ 1 ∧ 1 ≤ w * r := by
    intro w hw
    rw [uIcc_of_le hw11] at hw
    have hw0 : 0 < w := lt_of_lt_of_le hw10 hw.1
    have h1 : 1000 / r * r ≤ w * r := mul_le_mul_of_nonneg_right (hw1.trans hw.1) hr0.le
    rw [div_mul_cancel₀ _ hr0.ne'] at h1
    exact ⟨hw0, hw.2, by linarith⟩
  have hdc : ContinuousOn d (uIcc w1 1) := by
    have hg : ContinuousOn (fun w : ℝ => ((1.7984 - 16 / 9) * Real.log 2 +
        (13.6516 - 80 / 9) * Real.log (w * r) + (22.7538 - 111 / 5)) / (w * r) * HW.phi w)
        (uIcc w1 1) := by
      refine ContinuousOn.mul (ContinuousOn.div ?_ ?_ ?_) HW.continuous_phi.continuousOn
      · refine ContinuousOn.add (ContinuousOn.add continuousOn_const
          (ContinuousOn.mul continuousOn_const ?_)) continuousOn_const
        exact ContinuousOn.log (continuousOn_id.mul continuousOn_const)
          fun w hw => (mul_pos (hmem w hw).1 hr0).ne'
      · exact continuousOn_id.mul continuousOn_const
      · exact fun w hw => (mul_pos (hmem w hw).1 hr0).ne'
    refine hg.congr fun w hw => ?_
    rw [hd]
    simp only
    rw [dL_eq (w * r) (mul_pos (hmem w hw).1 hr0)]
  have hdi : IntervalIntegrable d volume w1 1 := hdc.intervalIntegrable
  have hmi : IntervalIntegrable (fun w : ℝ => C * (w ^ 1 * Real.exp (-w ^ 2 / 2))) volume w1 1 :=
    ((continuous_mom 1).const_mul C).intervalIntegrable _ _
  have hdle : ∫ w in w1..1, d w ≤ C * (1 - 0.6065306597) := by
    have h1 : ∫ w in w1..1, d w ≤ ∫ w in w1..1, C * (w ^ 1 * Real.exp (-w ^ 2 / 2)) := by
      refine intervalIntegral.integral_mono_on hw11 hdi hmi fun w hw => ?_
      have hw' : w ∈ uIcc w1 1 := by rw [uIcc_of_le hw11]; exact hw
      obtain ⟨hw0, hw1', hwr⟩ := hmem w hw'
      exact dlo_le r w hr0 hw0 hw1' hwr
    rw [intervalIntegral.integral_const_mul] at h1
    have hJ : ∫ w in w1..1, w ^ 1 * Real.exp (-w ^ 2 / 2) = mJ w1 1 1 := rfl
    rw [hJ, mJ_one] at h1
    have he1 : Real.exp (-w1 ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg w1]
    have he2 := ex_1.1
    have hk : Real.exp (-w1 ^ 2 / 2) - Real.exp (-1 ^ 2 / 2) ≤ 1 - 0.6065306597 := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hk hC0)
  rw [hsplit]
  by_cases hfi : IntervalIntegrable fC volume w1 1
  · rw [intervalIntegral.integral_add hfi hdi]
    linarith
  · have hnot : ¬ IntervalIntegrable (fun w => fC w + d w) volume w1 1 := by
      intro h
      apply hfi
      have := h.sub hdi
      simpa using this
    rw [intervalIntegral.integral_undef hnot, intervalIntegral.integral_undef hfi]
    have : 0 ≤ C * (1 - 0.6065306597) := mul_nonneg hC0 (by norm_num)
    linarith

/-- **The `w > 1` integral**: `∫_{w>1} g_{wy}(r)φ` on the corrected `L` exceeds the printed one by
at most `D̄(r)/r·√(π/2)` (`∫_{w>1} φ ≤ ∫_{w>0} φ = √(π/2)`, `EN.int_phi`). -/
theorem hi_le (y r : ℝ) (hr : 150000 ≤ r) :
    ∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * HW.phi w ≤
      (∫ w in Ioi (1 : ℝ), OC.gY (w * y) r * HW.phi w) +
        (0.568095 + 4.762712 * Real.log r) / r * Real.sqrt (Real.pi / 2) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hD0, hD1⟩ := dL_bounds r (by linarith)
  set D := (OL.lLc r - lL r) / r with hD
  have hDn : 0 ≤ D := div_nonneg hD0 hr0.le
  have hDle : D ≤ (0.568095 + 4.762712 * Real.log r) / r :=
    div_le_div_of_nonneg_right hD1 hr0.le
  have hs0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  set fC : ℝ → ℝ := fun w => OC.gY (w * y) r * HW.phi w with hfC
  have hsplit : (fun w => OL.gYL (w * y) r * HW.phi w) = fun w => fC w + D * HW.phi w := by
    funext w
    rw [hfC, gYL_eq]
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
  have hDI : ∫ w in Ioi (1 : ℝ), D * HW.phi w ≤
      (0.568095 + 4.762712 * Real.log r) / r * Real.sqrt (Real.pi / 2) := by
    rw [integral_const_mul]
    exact mul_le_mul hDle hphi hphi0 (hDn.trans hDle)
  have hB0 : 0 ≤ (0.568095 + 4.762712 * Real.log r) / r * Real.sqrt (Real.pi / 2) :=
    mul_nonneg (hDn.trans hDle) hs0
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

/-- **THE CORRECTION BOUND**: `g̃_L(y, r) ≤ g̃(y, r) + 1.31395·(0.568095 + 4.762712 log r)/r` for
`y ≥ 10²⁵`, `r ≥ 150000` (`lo_le`, `hi_le`, `|φ|₁ = √(π/2) ≥ 1.2533139`). -/
theorem gTL_le (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 150000 ≤ r) :
    OL.gTL HW.phi y r ≤
      OC.gT HW.phi y r + 1.31395 * ((0.568095 + 4.762712 * Real.log r) / r) := by
  have hr0 : 0 < r := by linarith
  have hlr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  obtain ⟨-, -, hm1⟩ := w1_facts y r hy (by linarith)
  have h1 := lo_le y r _ hr (le_max_right _ _) (hm1.trans (by norm_num))
  have h2 := hi_le y r hr
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  obtain ⟨hs1, -⟩ := MajSp.sqrt_pi_half
  unfold OL.gTL OC.gT
  rw [hl1]
  set Sq := Real.sqrt (Real.pi / 2) with hSq
  set C := (0.568095 + 4.762712 * Real.log r) / r with hC
  have hC0 : 0 ≤ C := div_nonneg (by linarith) hr0.le
  have hSq0 : 0 < Sq := lt_of_lt_of_le (by norm_num) hs1
  set IL := ∫ w in (max (1 / kK y) (1000 / r))..1, OL.gYL (w * y) (w * r) * HW.phi w
  set IH := ∫ w in Ioi (1 : ℝ), OL.gYL (w * y) r * HW.phi w
  set JL := ∫ w in (max (1 / kK y) (1000 / r))..1, OC.gY (w * y) (w * r) * HW.phi w
  set JH := ∫ w in Ioi (1 : ℝ), OC.gY (w * y) r * HW.phi w
  set S := 1.04488 * ∫ w in (1 / kK y)..(max (1 / kK y) (1000 / r)), |HW.phi w|
  have hk : C * (1 - 0.6065306597) / Sq ≤ C * 0.31395 := by
    rw [div_le_iff₀ hSq0]
    nlinarith
  calc (IL + IH + S) / Sq ≤ (JL + JH + S + C * (1 - 0.6065306597) + C * Sq) / Sq :=
        div_le_div_of_nonneg_right (by linarith) hSq0.le
    _ = (JL + JH + S) / Sq + C * (1 - 0.6065306597) / Sq + C := by
        field_simp
    _ ≤ (JL + JH + S) / Sq + 1.31395 * C := by linarith

/-! ## (2) Envelopes transfer -/

/-- **An envelope of the printed `g̃` is an envelope of the corrected one** once `q₀` and `q₁`
absorb `1.31395·0.568095` and `1.31395·4.762712` (`gTL_le`, `log r ≥ 0`). -/
theorem envL_of (y r p0 p1 p2 p3 p4 q0 q1 q2 z Q0 Q1 : ℝ) (hy : 10 ^ 25 ≤ y)
    (hr : 150000 ≤ r) (h : OC.gT HW.phi y r ≤ envF p0 p1 p2 p3 p4 q0 q1 q2 z r)
    (h0 : q0 + 1.31395 * 0.568095 ≤ Q0) (h1 : q1 + 1.31395 * 4.762712 ≤ Q1) :
    OL.gTL HW.phi y r ≤ envF p0 p1 p2 p3 p4 Q0 Q1 q2 z r := by
  have hr0 : 0 < r := by linarith
  have hl : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  refine (gTL_le y r hy hr).trans ?_
  have e : envF p0 p1 p2 p3 p4 Q0 Q1 q2 z r = envF p0 p1 p2 p3 p4 q0 q1 q2 z r +
      ((Q0 - q0) + (Q1 - q1) * Real.log r) / r := by
    unfold envF
    ring
  rw [e, ← mul_div_assoc]
  have k : 1.31395 * (0.568095 + 4.762712 * Real.log r) ≤ (Q0 - q0) + (Q1 - q1) * Real.log r := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hl]
  have := div_le_div_of_nonneg_right k hr0.le
  linarith

/-- **Nonnegativity survives raising `q₀, q₁`** (`log r ≥ 0`). -/
theorem envL_pos_of (p0 p1 p2 p3 p4 q0 q1 q2 z Q0 Q1 r : ℝ) (hr : 1 ≤ r)
    (h : 0 ≤ envF p0 p1 p2 p3 p4 q0 q1 q2 z r) (h0 : q0 ≤ Q0) (h1 : q1 ≤ Q1) :
    0 ≤ envF p0 p1 p2 p3 p4 Q0 Q1 q2 z r := by
  have hr0 : 0 < r := by linarith
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have e : envF p0 p1 p2 p3 p4 Q0 Q1 q2 z r = envF p0 p1 p2 p3 p4 q0 q1 q2 z r +
      ((Q0 - q0) + (Q1 - q1) * Real.log r) / r := by
    unfold envF
    ring
  rw [e]
  have : 0 ≤ ((Q0 - q0) + (Q1 - q1) * Real.log r) / r :=
    div_nonneg (add_nonneg (by linarith) (mul_nonneg (by linarith) hl)) hr0.le
  linarith

/-! ## (3) `g̃_L(y, r₀) ≥ 0` -/

/-- **`g_Y(t) ≥ 0` on the corrected `L`** once `t ≥ 1000` and `log(9Y^{1/3}/(4.008t)) > 0`
(`MC.gY_nonneg`, `dL_bounds`). -/
theorem gYL_nonneg (Y t : ℝ) (hY : 0 < Y) (ht : 1000 ≤ t)
    (hD : 0 < Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * t)))) : 0 ≤ OL.gYL Y t := by
  rw [gYL_eq]
  have h1 := gY_nonneg Y t hY ht hD
  have h2 := div_nonneg (dL_bounds t (by linarith)).1 (by linarith : (0 : ℝ) ≤ t)
  linarith

/-- **`g̃_L(y, r₀) ≥ 0`** for `y ≥ 10²⁵` (every integrand of `gTL` is `≥ 0`; the proof of
`MC.gT_nonneg_r0` with `gYL_nonneg`). -/
theorem gTL_nonneg_r0 (y : ℝ) (hy : 10 ^ 25 ≤ y) : 0 ≤ OL.gTL HW.phi y 150000 := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hly : 57.564626 ≤ Real.log y := MN.lya_ge_1.trans (Real.log_le_log (by norm_num) hy)
  have h9 := MN.log9_ge
  have h20 : Real.log 601200 ≤ 20 * 0.6931471808 := by
    have := Real.log_le_log (by norm_num) (show (601200 : ℝ) ≤ 2 ^ 20 by norm_num)
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_lt_d9]
  obtain ⟨hy1, hm0, hm1⟩ := w1_facts y 150000 hy (by norm_num)
  have hlo : ∀ w ∈ Icc (max (1 / kK y) (1000 / 150000)) 1,
      0 ≤ OL.gYL (w * y) (w * 150000) * HW.phi w := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hw.1
    have hwr := wr_ge y 150000 w (by norm_num) hw.1
    have hlw : Real.log w ≤ 0 := Real.log_nonpos hw0.le hw.2
    refine mul_nonneg (gYL_nonneg _ _ (mul_pos hw0 hy0) hwr ?_) (HW.phi_nonneg w)
    rw [MN.logD_eq _ _ (mul_pos hw0 hy0) (by positivity), Real.log_mul hw0.ne' hy0.ne',
      show (2.004 : ℝ) * (2 * (w * 150000)) = w * 601200 by ring,
      Real.log_mul hw0.ne' (by norm_num)]
    linarith
  have hhi : ∀ w ∈ Ioi (1 : ℝ), 0 ≤ OL.gYL (w * y) 150000 * HW.phi w := by
    intro w hw
    have hw1 : (1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hlw : 0 ≤ Real.log w := Real.log_nonneg hw1.le
    refine mul_nonneg (gYL_nonneg _ _ (mul_pos hw0 hy0) (by norm_num) ?_) (HW.phi_nonneg w)
    rw [MN.logD_eq _ _ (mul_pos hw0 hy0) (by positivity), Real.log_mul hw0.ne' hy0.ne',
      show (2.004 : ℝ) * (2 * (150000 : ℝ)) = 601200 by norm_num]
    linarith
  have h1 : 0 ≤ ∫ w in (max (1 / kK y) (1000 / 150000))..1,
      OL.gYL (w * y) (w * 150000) * HW.phi w :=
    intervalIntegral.integral_nonneg (hm1.trans (by norm_num)) hlo
  have h2 : 0 ≤ ∫ w in Ioi (1 : ℝ), OL.gYL (w * y) 150000 * HW.phi w :=
    setIntegral_nonneg measurableSet_Ioi hhi
  have h3 : 0 ≤ ∫ w in (1 / kK y)..(max (1 / kK y) (1000 / 150000)), |HW.phi w| :=
    intervalIntegral.integral_nonneg (le_max_left _ _) (fun w _ => abs_nonneg _)
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  unfold OL.gTL
  rw [hl1]
  positivity

/-! ## (4) The five region envelopes on the corrected `L` (GENERATED)

`MC.envR…` with `q₀ ↦ q₀ + 1.31395·0.568095` and `q₁ ↦ q₁ + 1.31395·4.762712`, rounded up to 12
significant digits (`scratchpad/mnl/gen_mnl.py`). -/

/-- **`envLR0`**: `g̃_L(y, r) ≤ envF … r` for `r ∈ [150000, 520000]`, `y ≥ 10 ^ 25` (`MC.envR0`,
    `envL_of`). -/
theorem envLR0 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    OL.gTL HW.phi y r ≤ envF 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633
        0.0000297025673079 64.1333331084 30.8744819896 0.545031222151 0.000210527045125 r :=
  envL_of y r _ _ _ _ _ _ _ _ _ _ _ hy hr0 (envR0 y r hy hr0 hr1) (by norm_num) (by norm_num)

/-- **`envLR0` is `≥ 0`** (`MC.envR0_pos`, `envL_pos_of`). -/
theorem envLR0_pos (r : ℝ) (hr0 : 150000 ≤ r) (hr1 : r ≤ 520000) :
    0 ≤ envF 2.94428873212 0.654209332173 0.00636024697078 0.00173163875633 0.0000297025673079
        64.1333331084 30.8744819896 0.545031222151 0.000210527045125 r :=
  envL_pos_of _ _ _ _ _ _ _ _ _ _ _ r (by linarith) (envR0_pos r hr0 hr1) (by norm_num)
      (by norm_num)

/-- **`envLR1`**: `g̃_L(y, r) ≤ envF … r` for `r ∈ [520000, 1740000]`, `y ≥ 10 ^ 25` (`MC.envR1`,
    `envL_of`). -/
theorem envLR1 (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    OL.gTL HW.phi y r ≤ envF 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033
        0.0000299846672039 66.3432584969 31.4275359512 0.475003664868 0.000211099791842 r :=
  envL_of y r _ _ _ _ _ _ _ _ _ _ _ hy (le_trans (by norm_num) hr0) (envR1 y r hy hr0 hr1)
      (by norm_num) (by norm_num)

/-- **`envLR1` is `≥ 0`** (`MC.envR1_pos`, `envL_pos_of`). -/
theorem envLR1_pos (r : ℝ) (hr0 : 520000 ≤ r) (hr1 : r ≤ 1740000) :
    0 ≤ envF 2.98733358573 0.689226963225 (-0.00106021688168) 0.00203455134033 0.0000299846672039
        66.3432584969 31.4275359512 0.475003664868 0.000211099791842 r :=
  envL_pos_of _ _ _ _ _ _ _ _ _ _ _ r (by linarith) (envR1_pos r hr0 hr1) (by norm_num)
      (by norm_num)

/-- **`envLR2a`**: `g̃_L(y, r) ≤ envF … r` for `r ∈ [1740000, 3216400]`, `y ≥ 10 ^ 25` (`MC.envR2a`,
    `envL_of`). -/
theorem envLR2a (y r : ℝ) (hy : (10 ^ 25) ≤ y) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    OL.gTL HW.phi y r ≤ envF 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466
        0.0000353941790317 66.9050831691 31.5559712457 0.452552670596 0.000210527045125 r :=
  envL_of y r _ _ _ _ _ _ _ _ _ _ _ hy (le_trans (by norm_num) hr0) (envR2a y r hy hr0 hr1)
      (by norm_num) (by norm_num)

/-- **`envLR2a` is `≥ 0`** (`MC.envR2a_pos`, `envL_pos_of`). -/
theorem envLR2a_pos (r : ℝ) (hr0 : 1740000 ≤ r) (hr1 : r ≤ 3216400) :
    0 ≤ envF 2.99415982257 0.688720800761 (-0.00919198398172) 0.00249610521466 0.0000353941790317
        66.9050831691 31.5559712457 0.452552670596 0.000210527045125 r :=
  envL_pos_of _ _ _ _ _ _ _ _ _ _ _ r (by linarith) (envR2a_pos r hr0 hr1) (by norm_num)
      (by norm_num)

/-- **`envLR2b`**: `g̃_L(y, r) ≤ envF … r` for `r ∈ [3216000, 5950000]`, `y ≥ 10 ^ 26` (`MC.envR2b`,
    `envL_of`). -/
theorem envLR2b (y r : ℝ) (hy : (10 ^ 26) ≤ y) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    OL.gTL HW.phi y r ≤ envF 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774
        0.0000310866337797 67.6946571766 31.7581107855 0.431143061793 0.000143820551574 r :=
  envL_of y r _ _ _ _ _ _ _ _ _ _ _ (le_trans (by norm_num) hy) (le_trans (by norm_num) hr0)
      (envR2b y r hy hr0 hr1) (by norm_num) (by norm_num)

/-- **`envLR2b` is `≥ 0`** (`MC.envR2b_pos`, `envL_pos_of`). -/
theorem envLR2b_pos (r : ℝ) (hr0 : 3216000 ≤ r) (hr1 : r ≤ 5950000) :
    0 ≤ envF 3.00843946276 0.700385883674 (-0.00959431030359) 0.00233394703774 0.0000310866337797
        67.6946571766 31.7581107855 0.431143061793 0.000143820551574 r :=
  envL_pos_of _ _ _ _ _ _ _ _ _ _ _ r (by linarith) (envR2b_pos r hr0 hr1) (by norm_num)
      (by norm_num)

/-- **`envLRF`**: `g̃_L(y, r) ≤ envF … r` for `r ∈ [5940000, r₁(y)]`, `y ≥ 10 ^ 27` (`MC.envRF`,
    `envL_of`). -/
theorem envLRF (y r : ℝ) (hy : (10 ^ 27) ≤ y) (hr0 : 5940000 ≤ r) (hr1 : r ≤ r1y y) :
    OL.gTL HW.phi y r ≤ envF 3.26627202061 1.1187151769 0.0114351675071 0 0 69.8799339884
        32.360963423 0.381494368499 (3.09852175891 * y ^ (-(1 : ℝ) / 6)) r :=
  envL_of y r _ _ _ _ _ _ _ _ _ _ _ (le_trans (by norm_num) hy) (le_trans (by norm_num) hr0)
      (envRF y r hy hr0 hr1) (by norm_num) (by norm_num)

/-- **`envLRF` is `≥ 0`** (`MC.envRF_pos`, `envL_pos_of`). -/
theorem envLRF_pos (y r : ℝ) (hy : 0 < y) (hr0 : 5940000 ≤ r) :
    0 ≤ envF 3.26627202061 1.1187151769 0.0114351675071 0 0 69.8799339884 32.360963423
        0.381494368499 (3.09852175891 * y ^ (-(1 : ℝ) / 6)) r :=
  envL_pos_of _ _ _ _ _ _ _ _ _ _ _ r (by linarith) (envRF_pos y r hy hr0) (by norm_num)
      (by norm_num)

end Principia.Common.TernaryGoldbach.ML
