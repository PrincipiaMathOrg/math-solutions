/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EasyCirc

set_option autoImplicit false

/-!
# `|η∘'''|₁ ≤ 40`

The last numerical conjunct of `EN.NormsE` about `η∘` alone (Helfgott: `32.5023`, `eq:ronsard`; the
true value is `32.5022605`).

**The third derivative, explicitly.** With `u = t − 1`, on `(0, 2)` Helfgott's `η∘` is
`G₀(u) = (1−u²)³e^{−u²/2}`, and `(p·e^{−u²/2})' = (p' − u p)·e^{−u²/2}` (`hasDerivAt_pE`) gives
`G₀' = P₁e^{−u²/2}`, `G₀'' = P₂e^{−u²/2}`, `G₀''' = P₃e^{−u²/2}` with
`P₁ = u⁷ − 9u⁵ + 15u³ − 7u`, `P₂ = −u⁸ + 16u⁶ − 60u⁴ + 52u² − 7`,
`P₃ = u⁹ − 24u⁷ + 156u⁵ − 292u³ + 111u` (`iteratedDeriv_G0`). Mathlib's
`iteratedDeriv_comp_sub_const` and `EventuallyEq.iteratedDeriv_eq` carry this to `η∘` on `(0, 2)`
(`third_eq`); on `(2, ∞)` `η∘ ≡ 0` near every point (`third_zero`). The one point `t = 2`, where
`η∘'''` jumps, is Lebesgue-null.

**The bound.** `|P₃e^{−u²/2}| ≤ (P₃²e^{−u²} + 18²)/36` (AM–GM) and `e^{−u²} ≤ T₄(u²) + u¹⁰/100`
(`EN.exp_sq_taylor`), so `|η∘'''|₁ ≤ ∫₋₁¹ (P₃²(T₄(u²) + u¹⁰/100) + 324)/36 = 36.4183 ≤ 40`
(`int_B3`). Dropping the Gaussian factor instead would give `44.6`, which does not close.
-/

namespace Principia.Common.TernaryGoldbach.EN

open MeasureTheory Set Filter
open scoped Topology

/-! ## The polynomials and `G₀ … G₃` -/

/-- `P₀(u) = (1 − u²)³`. -/
noncomputable def P0 (u : ℝ) : ℝ := (1 - u ^ 2) ^ 3

/-- `P₁ = P₀' − uP₀ = u⁷ − 9u⁵ + 15u³ − 7u`. -/
noncomputable def P1 (u : ℝ) : ℝ := u ^ 7 - 9 * u ^ 5 + 15 * u ^ 3 - 7 * u

/-- `P₂ = P₁' − uP₁ = −u⁸ + 16u⁶ − 60u⁴ + 52u² − 7`. -/
noncomputable def P2 (u : ℝ) : ℝ := -u ^ 8 + 16 * u ^ 6 - 60 * u ^ 4 + 52 * u ^ 2 - 7

/-- `P₃ = P₂' − uP₂ = u⁹ − 24u⁷ + 156u⁵ − 292u³ + 111u`. -/
noncomputable def P3 (u : ℝ) : ℝ := u ^ 9 - 24 * u ^ 7 + 156 * u ^ 5 - 292 * u ^ 3 + 111 * u

/-- `G₀(u) = P₀(u)e^{−u²/2}`: `η∘(t) = G₀(t − 1)` on `[0, 2]`. -/
noncomputable def G0 (u : ℝ) : ℝ := P0 u * Real.exp (-u ^ 2 / 2)

/-- `G₁ = P₁e^{−u²/2}`. -/
noncomputable def G1 (u : ℝ) : ℝ := P1 u * Real.exp (-u ^ 2 / 2)

/-- `G₂ = P₂e^{−u²/2}`. -/
noncomputable def G2 (u : ℝ) : ℝ := P2 u * Real.exp (-u ^ 2 / 2)

/-- `G₃ = P₃e^{−u²/2}`. -/
noncomputable def G3 (u : ℝ) : ℝ := P3 u * Real.exp (-u ^ 2 / 2)

/-- **`(p·e^{−u²/2})' = (p' − u p)·e^{−u²/2}`.** -/
theorem hasDerivAt_pE {p : ℝ → ℝ} {p' u : ℝ} (hp : HasDerivAt p p' u) :
    HasDerivAt (fun x => p x * Real.exp (-x ^ 2 / 2)) ((p' - u * p u) * Real.exp (-u ^ 2 / 2))
      u := by
  have hE := ((hasDerivAt_sq' u).fun_neg.div_const 2).exp
  refine (hp.fun_mul hE).congr_deriv ?_
  ring

/-- `P₀' = −6u(1 − u²)²`. -/
theorem hasDerivAt_P0 (u : ℝ) : HasDerivAt P0 (-6 * u * (1 - u ^ 2) ^ 2) u := by
  have hi := hasDerivAt_id' u
  have ha := (hi.fun_mul hi).const_sub 1
  have h := (ha.fun_mul ha).fun_mul ha
  have e : P0 = fun x => (1 - x * x) * (1 - x * x) * (1 - x * x) := by
    funext x
    unfold P0
    ring
  rw [e]
  exact h.congr_deriv (by ring)

/-- `P₁' = 7u⁶ − 45u⁴ + 45u² − 7`. -/
theorem hasDerivAt_P1 (u : ℝ) : HasDerivAt P1 (7 * u ^ 6 - 45 * u ^ 4 + 45 * u ^ 2 - 7) u := by
  have hi := hasDerivAt_id' u
  have hw := hi.fun_mul hi
  have h := hi.fun_mul (((hw.fun_mul ((hw.fun_mul (hw.sub_const 9)).add_const 15))).sub_const 7)
  have e : P1 = fun x => x * ((x * x) * ((x * x) * (x * x - 9) + 15) - 7) := by
    funext x
    unfold P1
    ring
  rw [e]
  exact h.congr_deriv (by ring)

/-- `P₂' = −8u⁷ + 96u⁵ − 240u³ + 104u`. -/
theorem hasDerivAt_P2 (u : ℝ) :
    HasDerivAt P2 (-8 * u ^ 7 + 96 * u ^ 5 - 240 * u ^ 3 + 104 * u) u := by
  have hi := hasDerivAt_id' u
  have hw := hi.fun_mul hi
  have h := ((hw.fun_mul ((hw.fun_mul (hw.const_sub 16)).sub_const 60)).add_const 52)
  have h' := (hw.fun_mul h).sub_const 7
  have e : P2 = fun x => (x * x) * ((x * x) * ((x * x) * (16 - x * x) - 60) + 52) - 7 := by
    funext x
    unfold P2
    ring
  rw [e]
  exact h'.congr_deriv (by ring)

/-- `G₀' = G₁`. -/
theorem hasDerivAt_G0 (u : ℝ) : HasDerivAt G0 (G1 u) u := by
  refine (hasDerivAt_pE (hasDerivAt_P0 u)).congr_deriv ?_
  unfold G1 P0 P1
  ring

/-- `G₁' = G₂`. -/
theorem hasDerivAt_G1 (u : ℝ) : HasDerivAt G1 (G2 u) u := by
  refine (hasDerivAt_pE (hasDerivAt_P1 u)).congr_deriv ?_
  unfold G2 P1 P2
  ring

/-- `G₂' = G₃`. -/
theorem hasDerivAt_G2 (u : ℝ) : HasDerivAt G2 (G3 u) u := by
  refine (hasDerivAt_pE (hasDerivAt_P2 u)).congr_deriv ?_
  unfold G3 P2 P3
  ring

/-- **`G₀''' = G₃`.** -/
theorem iteratedDeriv_G0 : iteratedDeriv 3 G0 = G3 := by
  have d0 : deriv G0 = G1 := funext fun u => (hasDerivAt_G0 u).deriv
  have d1 : deriv G1 = G2 := funext fun u => (hasDerivAt_G1 u).deriv
  have d2 : deriv G2 = G3 := funext fun u => (hasDerivAt_G2 u).deriv
  change iteratedDeriv (2 + 1) G0 = G3
  rw [iteratedDeriv_succ]
  change deriv (iteratedDeriv (1 + 1) G0) = G3
  rw [iteratedDeriv_succ, iteratedDeriv_one, d0, d1, d2]

/-! ## `η∘'''` -/

/-- On `(0, 2)`, `η∘ = G₀(· − 1)` near every point. -/
theorem etaCirc_ev {t : ℝ} (h0 : 0 < t) (h2 : t < 2) :
    HW.etaCirc =ᶠ[𝓝 t] fun z => G0 (z - 1) := by
  filter_upwards [Ioo_mem_nhds h0 h2] with z hz
  rw [HW.etaCirc_eq hz.1.le hz.2.le]
  unfold G0 P0
  ring

/-- **`η∘'''(t) = G₃(t − 1)` on `(0, 2)`.** -/
theorem third_eq {t : ℝ} (h0 : 0 < t) (h2 : t < 2) :
    iteratedDeriv 3 HW.etaCirc t = G3 (t - 1) := by
  rw [(etaCirc_ev h0 h2).iteratedDeriv_eq 3]
  have h := congrFun (iteratedDeriv_comp_sub_const 3 G0 1) t
  rw [h, iteratedDeriv_G0]

/-- **`η∘''' = 0` on `(2, ∞)`.** -/
theorem third_zero {t : ℝ} (ht : 2 < t) : iteratedDeriv 3 HW.etaCirc t = 0 := by
  have hev : HW.etaCirc =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with z hz
    exact etaCirc_of_two_lt hz
  rw [hev.iteratedDeriv_eq 3, iteratedDeriv_fun_const_zero]

/-! ## The majorant -/

/-- `B₃(u) = (P₃(u)²(T₄(u²) + u¹⁰/100) + 18²)/36`. -/
noncomputable def B3 (u : ℝ) : ℝ := (P3 u ^ 2 * (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100) + 324) / 36

/-- **`|G₃(u)| ≤ B₃(u)` on `[−1, 1]`**: AM–GM `a ≤ (a² + 18²)/36`, then the Taylor bound. -/
theorem G3_le {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) : |G3 u| ≤ B3 u := by
  have he := (exp_sq_taylor hu).2
  have hsq : |G3 u| ^ 2 = P3 u ^ 2 * Real.exp (-u ^ 2) := by
    rw [sq_abs, G3, mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  have ha : |G3 u| ≤ (|G3 u| ^ 2 + 324) / 36 := by nlinarith [sq_nonneg (|G3 u| - 18)]
  have hb : P3 u ^ 2 * Real.exp (-u ^ 2) ≤ P3 u ^ 2 * (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100) :=
    mul_le_mul_of_nonneg_left he (sq_nonneg _)
  rw [hsq] at ha
  unfold B3
  linarith

/-- `∫₋₁¹ B₃ = 275261930145802/7558343533125 = 36.4183`. -/
theorem int_B3 : ∫ u in (-1 : ℝ)..1, B3 u = 275261930145802 / 7558343533125 := by
  have h : EqOn B3 (fun u => ∑ k : Fin 29, (![9, 0, 1369/4, 0, -25715/12, 0, 381761/72, 0,
      -501587/72, 0, 550057/96, 0, -35226737/10800, 0, 1824991/1350, 0, -355501/900, 0,
      744379/10800, 0, -18539/5400, 0, -587/600, 0, 1007/5400, 0, -263/21600, 0, 1/3600] :
        Fin 29 → ℝ) k * u ^ (k : ℕ)) (uIcc (-1) 1) := by
    intro u _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, B3, P3, T4]
    ring
  rw [intervalIntegral.integral_congr h, int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- The majorant on `(0, ∞)`: `B₃(t − 1)` on `(0, 2]`, `0` beyond. -/
noncomputable def g3 (t : ℝ) : ℝ := if t ≤ 2 then B3 (t - 1) else 0

/-- `B₃` is continuous. -/
theorem continuous_B3 : Continuous B3 := by
  unfold B3 P3 T4
  fun_prop

/-- `∫₀^∞ g₃ = ∫₋₁¹ B₃`. -/
theorem int_g3 : ∫ t in Ioi (0 : ℝ), g3 t = 275261930145802 / 7558343533125 := by
  rw [setInt_Ioi_02 _ fun t ht => by rw [g3, if_neg (not_le.mpr ht)]]
  have hc : EqOn g3 (fun t => B3 (t - 1)) (uIcc 0 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    rw [g3, if_pos ht.2]
  rw [intervalIntegral.integral_congr hc]
  calc ∫ t in (0 : ℝ)..2, B3 (t - 1) = ∫ u in (0 - 1 : ℝ)..(2 - 1), B3 u :=
        intervalIntegral.integral_comp_sub_right B3 1
    _ = ∫ u in (-1 : ℝ)..1, B3 u := by norm_num
    _ = 275261930145802 / 7558343533125 := int_B3

/-- `g₃` is integrable on `(0, ∞)`. -/
theorem integrable_g3 : Integrable g3 (volume.restrict (Ioi 0)) := by
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := Ioc 0 2) ?_ measurableSet_Ioi
    fun t ht => ?_
  · have hc : IntegrableOn (fun t => B3 (t - 1)) (Ioc 0 2) :=
      ((continuous_B3.comp (continuous_id.sub continuous_const)).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    refine hc.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [g3, if_pos ht.2]
  · obtain ⟨h1, h2⟩ := ht
    have h2' : 2 < t := by
      by_contra hc
      exact h2 ⟨h1, not_lt.mp hc⟩
    rw [g3, if_neg (not_le.mpr h2')]

/-- **`|η∘'''|₁ ≤ 40`** (bound `36.4183`; truth `32.5022605`). -/
theorem l1_third_le : MajSp.l1 (iteratedDeriv 3 HW.etaCirc) ≤ 40 := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |iteratedDeriv 3 HW.etaCirc t| ≤ g3 t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hne] with t ht1 ht2
    have ht1' : 0 < t := ht1
    have ht2' : t ≠ 2 := ht2
    rcases lt_or_gt_of_ne ht2' with hlt | hgt
    · rw [third_eq ht1' hlt, g3, if_pos hlt.le]
      exact G3_le ⟨by linarith, by linarith⟩
    · rw [third_zero hgt, g3, if_neg (not_le.mpr hgt)]
      simp
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) integrable_g3 hpt
  rw [int_g3] at hI
  unfold MajSp.l1
  have hn : (275261930145802 : ℝ) / 7558343533125 ≤ 40 := by norm_num
  linarith

end Principia.Common.TernaryGoldbach.EN
