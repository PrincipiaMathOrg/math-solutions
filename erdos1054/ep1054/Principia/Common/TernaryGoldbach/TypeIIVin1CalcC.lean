/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIVin1Calc
import Principia.Common.TernaryGoldbach.TypeIISpineC

set_option autoImplicit false

/-!
# `T2SC.Vin1CalcC` PROVED from the cited `eq:notung` — `eq:vinland1` at the erratum's `κ₇`

`vin1CalcC_of : HC.NotungCited → T2SC.Vin1CalcC`: `T2S.vin1Calc_of`'s argument with the corrected
`eq:velib` (`T2SC.HOkC`: `∫_1^T H₂ ds/s ≤ 0.15107 log T + 0.0231`). Only two steps move:

* `i3`: `∫_V^{x/U} H₂(x/WU) dW/W = ∫_1^{x/UV} H₂ ds/s ≤ 0.15107 L₀ + 0.0231` (`int_subst`);
* `main_algC`: the extra `β⁻¹·0.0231·x/(4√φ)·4` joins `eq:curious`'s error, so the AM-GM runs at
  `B' = κ₆L₀ + 2κ₇'` with `2κ₇'/4 = 0.0231 + 0.0639 ≥ 0.0231 + 45.2836·3.062·10⁻⁴`
  (`κ₇' = 0.1743`). The conclusion is `T2SC.vin1C`, the book's display at `κ₇'` exactly.

Every other step (the `x/√U` term with `eq:notung`, the `x/√V` term, integrability, the pointwise
bounds) is `T2S`'s, reused verbatim. No computation of ours stands in for a proof step.
-/

namespace Principia.Common.TernaryGoldbach.T2SC

open MeasureTheory Set
open scoped Interval
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
open Principia.Common.TernaryGoldbach.T2S

/-- The main term after integration, with the erratum's `+0.0231`: AM-GM at the optimal `β`
gives `eq:valmont` at `κ₇' = 0.1743`. -/
theorem main_algC (Y φ U V L0 F ℓ β : ℝ) (hY : 0 < Y) (hφ : 0 < φ) (hL0 : 0 < L0) (hF : 0 ≤ F)
    (hℓ : 0 ≤ ℓ) (hcurV : Real.sqrt Y / U / Real.sqrt V ≤ 3.062e-4)
    (hβ : β = Real.sqrt (kap6 * L0 + 2 * kap7C) / Real.sqrt (2 * (L0 + ℓ * F))) :
    4 * (Y / (4 * Real.sqrt φ) * (β / 2) * L0 +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * F +
      Y / (4 * Real.sqrt φ) * (1 / β) * (0.15107 * L0 + 0.0231) +
      Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) * (2 / Real.sqrt V)) ≤
      Y / Real.sqrt (2 * φ) * Real.sqrt ((L0 + ℓ * F) * (kap6 * L0 + 2 * kap7C)) := by
  set A' := L0 + ℓ * F with hA'
  set B' := kap6 * L0 + 2 * kap7C with hB'
  have hA0 : 0 < A' := by positivity
  have hB0 : 0 < B' := by
    simp only [hB', kap6, kap7C]
    positivity
  have hβ0 : 0 < β := by
    rw [hβ]
    exact div_pos (Real.sqrt_pos.mpr hB0) (Real.sqrt_pos.mpr (by positivity))
  have hsφ : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ
  have hE : 22.6418 * Real.sqrt Y / U * (2 / Real.sqrt V) ≤ 2 * kap7C / 4 - 0.0231 := by
    have e : 22.6418 * Real.sqrt Y / U * (2 / Real.sqrt V) =
        45.2836 * (Real.sqrt Y / U / Real.sqrt V) := by ring
    rw [e]
    simp only [kap7C]
    linarith
  have hL : 0.15107 * L0 = kap6 * L0 / 4 := by simp only [kap6]; ring
  have step : 4 * (Y / (4 * Real.sqrt φ) * (β / 2) * L0 +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * F +
      Y / (4 * Real.sqrt φ) * (1 / β) * (0.15107 * L0 + 0.0231) +
      Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) * (2 / Real.sqrt V)) ≤
      Y / Real.sqrt φ * (β * A' / 2 + B' / 4 / β) := by
    have e : 4 * (Y / (4 * Real.sqrt φ) * (β / 2) * L0 +
        Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * F +
        Y / (4 * Real.sqrt φ) * (1 / β) * (0.15107 * L0 + 0.0231) +
        Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) * (2 / Real.sqrt V)) =
        Y / Real.sqrt φ * (β * A' / 2 + (0.15107 * L0 + 0.0231 +
          22.6418 * Real.sqrt Y / U * (2 / Real.sqrt V)) / β) := by
      simp only [hA']
      field_simp
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    refine div_le_div_of_nonneg_right ?_ hβ0.le
    rw [hB', hL]
    linarith
  refine step.trans (le_of_eq ?_)
  set a := Real.sqrt A' with ha
  set b := Real.sqrt B' with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hA0
  have hb0 : 0 < b := Real.sqrt_pos.mpr hB0
  have ha2 : a ^ 2 = A' := Real.sq_sqrt hA0.le
  have hb2 : b ^ 2 = B' := Real.sq_sqrt hB0.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs20 : 0 < Real.sqrt 2 := by positivity
  have e1 : Real.sqrt (2 * A') = Real.sqrt 2 * a := Real.sqrt_mul (by norm_num) _
  have e2 : Real.sqrt (2 * φ) = Real.sqrt 2 * Real.sqrt φ := Real.sqrt_mul (by norm_num) _
  have e3 : Real.sqrt (A' * B') = a * b := Real.sqrt_mul hA0.le _
  rw [hβ, e1, e2, e3, ← ha2, ← hb2]
  field_simp
  rw [hs2]
  ring

set_option maxHeartbeats 1000000 in
-- One long proof assembling six integrals and three pointwise bounds; the default 200000
-- heartbeats run out in the final elaboration, not in any single tactic.
theorem vin1CalcC_of (hn : HC.NotungCited) : Vin1CalcC := by
  intro Y hY δ q hq hdq hy H s1f s2f s3f hH hpt
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hU0, hV0, h27, hVX, hQ, hS3c, hcur, hxuv⟩ := first_facts Y δ q hY hq hdq hy
  set U := uA Y δ q with hUdef
  set V := vA Y with hVdef
  set X := Y / U with hXdef
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set φ := (Nat.totient q : ℝ) with hφdef
  have hφ0 : 0 < φ := by linarith
  set ρ := (q : ℝ) / φ with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  set c := 2 * (q : ℝ) with hcdef
  have hc0 : 0 < c := by positivity
  set ℓ := Real.log c with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hVc : 13.5 ≤ V / c := by
    rw [le_div_iff₀ hc0]
    linarith
  have hX0 : 0 < X := by linarith
  have hUV : 0 < U * V := mul_pos hU0 hV0
  set L0 := Real.log (Y / (U * V)) with hL0
  have hL0pos : 0 < L0 := Real.log_pos (by linarith)
  set lV := Real.log (V / c) with hlV
  have hlV0 : 0 < lV := Real.log_pos (by linarith)
  set Φ := ℓ * Real.log (1 + L0 / lV) with hΦdef
  have hΦ0 : 0 ≤ Φ := mul_nonneg hℓ0 (Real.log_nonneg (by
    have : 0 ≤ L0 / lV := by positivity
    linarith))
  set A' := L0 + Φ with hA'
  set B' := kap6 * L0 + 2 * kap7C with hB'
  have hA0 : 0 < A' := by positivity
  have hB0 : 0 < B' := by
    simp only [hB', kap6, kap7C]
    positivity
  set β := Real.sqrt B' / Real.sqrt (2 * A') with hβdef
  have hβ0 : 0 < β := div_pos (Real.sqrt_pos.mpr hB0) (Real.sqrt_pos.mpr (by positivity))
  have hXV : X / V = Y / (U * V) := by
    simp only [hXdef]
    rw [div_div]
  set T := X / c with hTdef
  have hTc : V / c ≤ T := div_le_div_of_nonneg_right hVX hc0.le
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log T = lV + L0 := by
    rw [hTdef, show X / c = V / c * (X / V) by field_simp, Real.log_mul (by positivity)
      (by positivity), hXV]
  have hlogT0 : 0 < Real.log T := by rw [hlogT]; positivity
  -- pointwise facts on `[V, X]`
  have hpos : ∀ W ∈ Icc V X, 0 < W ∧ 0 < Real.log (W / c) ∧ 1 ≤ Y / (W * U) := by
    intro W hW
    have hW0 : 0 < W := lt_of_lt_of_le hV0 hW.1
    refine ⟨hW0, Real.log_pos ?_, ?_⟩
    · have : V / c ≤ W / c := div_le_div_of_nonneg_right hW.1 hc0.le
      linarith
    · rw [le_div_iff₀ (mul_pos hW0 hU0), one_mul]
      have := hW.2
      rw [hXdef, le_div_iff₀ hU0] at this
      linarith
  set G : ℝ → ℝ := fun W =>
    Y / (4 * Real.sqrt φ) * (β * (1 + ℓ / Real.log (W / c)) / 2 +
      (H (Y / (W * U)) + 22.6418 * (Real.sqrt (Y / W) / U)) / β) / W +
    Real.sqrt (0.1048 * ρ * Y) * (1 + Real.sqrt (ℓ / Real.log (W / c))) / Real.sqrt W +
    0.4618 * Y / (W * Real.sqrt W) with hG
  set G' : ℝ → ℝ := fun W =>
    Y / (4 * Real.sqrt φ) * (β / 2) * (1 / W) +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * (1 / Real.log (W / c) / W) +
      Y / (4 * Real.sqrt φ) * (1 / β) * (H (Y / (W * U)) / W) +
      (Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y) *
        (1 / (W * Real.sqrt W)) +
      Real.sqrt (0.1048 * ρ * Y) * (1 / Real.sqrt W) +
      Real.sqrt (0.1048 * ρ * Y) * (1 / Real.sqrt W * Real.sqrt (ℓ / Real.log (W / c)))
    with hG'
  have hGG' : ∀ W ∈ uIcc V X, G W = G' W := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    obtain ⟨hW0, hLW, -⟩ := hpos W hW
    exact g_expand Y φ β ℓ (Real.log (W / c)) (H (Y / (W * U))) U W _ hW0 hφ0 hβ0
      hLW.ne' hU0.ne'
  have hpt' : ∀ W ∈ Icc V X, 0 ≤ secI s1f s2f s3f W ∧ secI s1f s2f s3f W ≤ G W := by
    intro W hW
    obtain ⟨hW0, hLW, hs⟩ := hpos W hW
    obtain ⟨h1n, h2n, h3n, hS1, hK, hS3⟩ := hpt W hW
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
    have hnn : 0 ≤ secI s1f s2f s3f W := by
      unfold secI
      positivity
    refine ⟨hnn, ?_⟩
    -- `S₁`
    set P := H (Y / (W * U)) + 22.6418 * (Real.sqrt (Y / W) / U) with hP
    have hH0 := (hH.1 _ hs).1
    have hH1 := (hH.1 _ hs).2
    have hcw := cur_le Y U V W hY0 hU0 hV0 hW.1 hcur
    have hP0 : 0 ≤ P := by positivity
    have hs1P : s1f W ≤ Y / W * P := by
      have e : (Y / W) ^ ((3 : ℝ) / 2) = Y / W * Real.sqrt (Y / W) :=
        log_pow_three_halves (Y / W) (by positivity)
      unfold S1Bd at hS1
      rw [e] at hS1
      have : Y / W * P = Y / W * H (Y / (W * U)) + 22.6418 * (Y / W * Real.sqrt (Y / W)) / U := by
        simp only [hP]
        ring
      linarith
    have hs1c : s1f W ≤ 0.2096 * (Y / W) := by
      have hP' : P ≤ 0.2096 := by
        have := two_div_pi_sq
        simp only [hP]
        linarith
      calc s1f W ≤ Y / W * P := hs1P
        _ ≤ Y / W * 0.2096 := mul_le_mul_of_nonneg_left hP' (by positivity)
        _ = 0.2096 * (Y / W) := by ring
    -- `S₂` by `eq:garn1a`
    have hqW : (q : ℝ) < W / 2 := by linarith [hW.1]
    have h35 : 3.5 * W ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) := by
      have := mul_le_mul_of_nonneg_left hW.2 (by norm_num : (0 : ℝ) ≤ 3.5)
      linarith
    have hs2 := hK.2.1 hqW h35
    set L := Real.log (W / c) with hLdef
    have hlogW : Real.log W = L + ℓ := by
      rw [hLdef, hℓdef, Real.log_div hW0.ne' hc0.ne']
      ring
    have hs2' : s2f W ≤ Y * W * (1 + ℓ / L) / (8 * φ) + ρ * W ^ 2 * (L + ℓ) / (2 * L) := by
      have e : (Y / (4 * φ) / Real.log (W / (2 * q)) +
          (q : ℝ) / φ * W / Real.log (W / (2 * q))) * (1 / 2 * W * Real.log W) =
          Y * W * (1 + ℓ / L) / (8 * φ) + ρ * W ^ 2 * (L + ℓ) / (2 * L) := by
        have hLq : Real.log (W / (2 * q)) = L := rfl
        rw [hlogW, hLq]
        simp only [hρdef]
        field_simp
        ring
      rw [← e]
      exact hs2
    -- the three pointwise terms
    have hA := ptA (s1f W) P Y W φ (1 + ℓ / L) β hY0 hW0 hφ0 (by positivity) hβ0 hP0 hs1P
    have hB := ptB (s1f W) ρ Y W ℓ L hY0 hW0 hρ0 hℓ0 hLW hs1c
    have hC := ptC (s1f W) (s3f W) Y W hY0 hW0 hs1c h3n (by
      have : 2.0341 * W ≤ 0.0001 * Y := by
        have := mul_le_mul_of_nonneg_left hW.2 (by norm_num : (0 : ℝ) ≤ 2.0341)
        linarith
      linarith)
    have ha0 : 0 ≤ Y * W * (1 + ℓ / L) / (8 * φ) := by positivity
    have hb0 : 0 ≤ ρ * W ^ 2 * (L + ℓ) / (2 * L) := by positivity
    have hsplit : Real.sqrt (s1f W * s2f W) ≤ Real.sqrt (s1f W * (Y * W * (1 + ℓ / L) / (8 * φ)))
        + Real.sqrt (s1f W * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) := by
      refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs2' h1n)).trans ?_
      rw [mul_add]
      exact sqrt_add_le' _ _ (mul_nonneg h1n ha0) (mul_nonneg h1n hb0)
    have hsec : secI s1f s2f s3f W ≤
        Real.sqrt (s1f W * (Y * W * (1 + ℓ / L) / (8 * φ))) / W +
          Real.sqrt (s1f W * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) / W +
          Real.sqrt (s1f W * s3f W) / W := by
      unfold secI
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hW0.le
    refine hsec.trans ?_
    simp only [hG, ← hLdef, ← hP]
    linarith
  -- integrability of the pieces
  have hcont_logc : ContinuousOn (fun W => Real.log (W / c)) (uIcc V X) :=
    Real.continuousOn_log.comp (continuousOn_id.div_const c) fun W hW => by
      rw [uIcc_of_le hVX] at hW
      exact (div_pos (hpos W hW).1 hc0).ne'
  have hii1 : IntervalIntegrable (fun W : ℝ => 1 / W) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div continuousOn_id fun W hW => by
      rw [uIcc_of_le hVX] at hW
      exact (hpos W hW).1.ne'
  have hii2 : IntervalIntegrable (fun W => 1 / Real.log (W / c) / W) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div (continuousOn_const.div hcont_logc fun W hW => ?_) continuousOn_id
      fun W hW => ?_
    · rw [uIcc_of_le hVX] at hW
      exact (hpos W hW).2.1.ne'
    · rw [uIcc_of_le hVX] at hW
      exact (hpos W hW).1.ne'
  have hT1 : 1 ≤ Y / (U * V) := by linarith
  obtain ⟨hii3, hsub⟩ := int_subst H Y U V hY0 hU0 hV0 hVX (hH.2.1 _ hT1)
  rw [← hXdef] at hii3 hsub
  have hii4 : IntervalIntegrable (fun W : ℝ => 1 / (W * Real.sqrt W)) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      fun W hW => by
        rw [uIcc_of_le hVX] at hW
        have := (hpos W hW).1
        exact (mul_pos this (Real.sqrt_pos.mpr this)).ne'
  have hii5 : IntervalIntegrable (fun W : ℝ => 1 / Real.sqrt W) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div Real.continuous_sqrt.continuousOn fun W hW => by
      rw [uIcc_of_le hVX] at hW
      exact (Real.sqrt_pos.mpr (hpos W hW).1).ne'
  have hii6 : IntervalIntegrable (fun W => 1 / Real.sqrt W * Real.sqrt (ℓ / Real.log (W / c)))
      volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (continuousOn_const.div Real.continuous_sqrt.continuousOn
      fun W hW => ?_) ((continuousOn_const.div hcont_logc fun W hW => ?_).sqrt)
    · rw [uIcc_of_le hVX] at hW
      exact (Real.sqrt_pos.mpr (hpos W hW).1).ne'
    · rw [uIcc_of_le hVX] at hW
      exact (hpos W hW).2.1.ne'
  have hGi' : IntervalIntegrable G' volume V X :=
    ((((((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)).add
      (hii4.const_mul _)).add (hii5.const_mul _)).add (hii6.const_mul _))
  have hGi : IntervalIntegrable G volume V X :=
    (intervalIntegrable_congr fun W hW => (hGG' W (uIoc_subset_uIcc hW)).symm).mp hGi'
  -- `∫ secI ≤ ∫ G`
  have hmono : ∫ W in V..X, secI s1f s2f s3f W ≤ ∫ W in V..X, G W := by
    rw [intervalIntegral.integral_of_le hVX, intervalIntegral.integral_of_le hVX]
    refine integral_mono_of_nonneg ?_ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hVX).mp hGi)
      ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun W hW =>
        (hpt' W (Ioc_subset_Icc_self hW)).1
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun W hW =>
        (hpt' W (Ioc_subset_Icc_self hW)).2
  -- `∫ G`, piece by piece
  have hGint : ∫ W in V..X, G W = ∫ W in V..X, G' W := intervalIntegral.integral_congr hGG'
  have hGint' : ∫ W in V..X, G' W =
      Y / (4 * Real.sqrt φ) * (β / 2) * (∫ W in V..X, 1 / W) +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * (∫ W in V..X, 1 / Real.log (W / c) / W) +
      Y / (4 * Real.sqrt φ) * (1 / β) * (∫ W in V..X, H (Y / (W * U)) / W) +
      (Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y) *
        (∫ W in V..X, 1 / (W * Real.sqrt W)) +
      Real.sqrt (0.1048 * ρ * Y) * (∫ W in V..X, 1 / Real.sqrt W) +
      Real.sqrt (0.1048 * ρ * Y) *
        (∫ W in V..X, 1 / Real.sqrt W * Real.sqrt (ℓ / Real.log (W / c))) := by
    simp only [hG']
    rw [intervalIntegral.integral_add _ (hii6.const_mul _),
      intervalIntegral.integral_add _ (hii5.const_mul _),
      intervalIntegral.integral_add _ (hii4.const_mul _),
      intervalIntegral.integral_add _ (hii3.const_mul _),
      intervalIntegral.integral_add (hii1.const_mul _) (hii2.const_mul _)]
    · simp only [intervalIntegral.integral_const_mul]
    · exact (hii1.const_mul _).add (hii2.const_mul _)
    · exact ((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)
    · exact (((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)).add
        (hii4.const_mul _)
    · exact ((((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)).add
        (hii4.const_mul _)).add (hii5.const_mul _)
  -- the six integrals
  have i1 : ∫ W in V..X, 1 / W = L0 := by rw [int_inv V X hV0 hVX, hXV]
  have i2 : ∫ W in V..X, 1 / Real.log (W / c) / W = Real.log (1 + L0 / lV) := by
    rw [int_loglog c V X hc0 (by linarith) hVX, ← hTdef, hlogT,
      ← Real.log_div (by positivity) hlV0.ne']
    congr 1
    field_simp
  have i3 : ∫ W in V..X, H (Y / (W * U)) / W ≤ 0.15107 * L0 + 0.0231 := by
    rw [hsub]
    exact hH.2.2 _ hT1
  have i4 := int_rsqrt3 V X hV0 hVX
  have i5 := int_rsqrt V X hV0 hVX
  have i6 : ∫ W in V..X, 1 / Real.sqrt W * Real.sqrt (ℓ / Real.log (W / c)) ≤
      Real.sqrt c * Real.sqrt ℓ * (2.3 * Real.sqrt (T / Real.log T) + 0.2) := by
    rw [int_scale c ℓ V X hc0 (by linarith) hVX]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have he : Real.exp 1 ≤ V / c := by
      have := Real.exp_one_lt_d9
      linarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((notung_cont (Real.exp 1) (V / c) le_rfl).intervalIntegrable_of_Icc (μ := volume) he)
      ((notung_cont (V / c) T he).intervalIntegrable_of_Icc (μ := volume) hTc)
    have hnn : 0 ≤ ∫ t in (Real.exp 1)..(V / c), 1 / Real.sqrt (t * Real.log t) :=
      intervalIntegral.integral_nonneg he fun t _ => by positivity
    have := notung_all hn T (he.trans hTc)
    linarith
  -- assembly
  have hsφ : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ0
  have hk : 0 ≤ Y / (4 * Real.sqrt φ) := by positivity
  have hcurV : Real.sqrt Y / U / Real.sqrt V ≤ 3.062e-4 := by
    have := cur_le Y U V V hY0 hU0 hV0 le_rfl hcur
    rwa [Real.sqrt_div' Y hV0.le, div_div, mul_comm, ← div_div] at this
  have hmain := main_algC Y φ U V L0 (Real.log (1 + L0 / lV)) ℓ β hY0 hφ0 hL0pos
    (Real.log_nonneg (by
      have : 0 ≤ L0 / lV := by positivity
      linarith)) hℓ0 hcurV hβdef
  have hB := b_alg Y U ρ c ℓ X T hY0 hU0 hρ0 hc0 hXdef hTdef hT0 hlogT0
  -- the `x/√V` term
  have hC : 4 * (0.4618 * Y * (2 / Real.sqrt V)) ≤ kap9 * (Y / Real.sqrt V) := by
    simp only [kap9]
    have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
    have : 0 ≤ Y / Real.sqrt V := by positivity
    have e : 4 * (0.4618 * Y * (2 / Real.sqrt V)) = 3.6944 * (Y / Real.sqrt V) := by ring
    rw [e]
    nlinarith
  -- conclude
  refine (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans ?_
  rw [hGint, hGint', i1, i2]
  have hk3 : 0 ≤ Y / (4 * Real.sqrt φ) * (1 / β) := by positivity
  have hk4 : 0 ≤ Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y := by
    positivity
  have hk5 : 0 ≤ Real.sqrt (0.1048 * ρ * Y) := Real.sqrt_nonneg _
  have b3 := mul_le_mul_of_nonneg_left i3 hk3
  have b4 := mul_le_mul_of_nonneg_left i4 hk4
  have b5 := mul_le_mul_of_nonneg_left i5 hk5
  have b6 := mul_le_mul_of_nonneg_left i6 hk5
  have hvin : vin1C Y U V q = Y / Real.sqrt (2 * φ) * Real.sqrt (A' * B') +
      Real.sqrt 2 * kap2 * Real.sqrt ρ * (1 + 1.15 * Real.sqrt (ℓ / Real.log T)) *
        (Y / Real.sqrt U) + kap9 * (Y / Real.sqrt V) := by
    unfold vin1C
    have eT2 : Y / (2 * U * q) = T := by
      simp only [hTdef, hXdef, hcdef]
      field_simp
    rw [eT2]
  rw [hvin]
  linarith [hmain, hB, hC]


/-- **`Vinland1AtC` from the deep links** (`SecInt` and `Vin1CalcC` discharged). -/
theorem vinland1AtC_of_deep (hm : Menson2C) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) (hn : HC.NotungCited) : Vinland1AtC :=
  vinland1AtC_of secInt_holds hm hk hc hl h13 (vin1CalcC_of hn)

end Principia.Common.TernaryGoldbach.T2SC
