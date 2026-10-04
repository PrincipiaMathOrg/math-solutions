/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIErikCalc
import Principia.Common.TernaryGoldbach.TypeIIVin1CalcC

set_option autoImplicit false

/-!
# `T2SC.ErikCalcC` PROVED — `eq:eriksaga` at the erratum's `κ₇`

`erikCalcC_holds : T2SC.ErikCalcC`: `T2S.erikCalc_holds`'s argument with the corrected `eq:velib`
(`T2SC.HOkC`). As in `TypeIIVin1CalcC`, only `i3` (`≤ 0.15107 L₀ + 0.0231`) and the AM-GM
(`T2SC.main_algC`, `κ₇' = 0.1743`) move; the conclusion is `T2SC.erikC`, the book's display at
`κ₇'` exactly. No cited input.
-/

namespace Principia.Common.TernaryGoldbach.T2SC

open MeasureTheory Set
open scoped Interval
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
open Principia.Common.TernaryGoldbach.T2S

set_option maxHeartbeats 1000000 in
-- One long proof assembling five integrals and three pointwise bounds; the default 200000
-- heartbeats run out in the final elaboration, not in any single tactic.
/-- **`T2SC.ErikCalcC`, PROVED** — the integral calculus of `eq:eriksaga` at `κ₇'`. -/
theorem erikCalcC_holds : ErikCalcC := by
  intro Y hY δ q hq hdq hy h8 H s1f s2f s3f hH hpt
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hU0, hV0, h27, hVX, hQ, hS3c, hcur, hxuv⟩ := first_facts Y δ q hY hq hdq hy
  set U := uA Y δ q with hUdef
  set V := vA Y with hVdef
  set Q := 3 / 4 * Y ^ ((2 : ℝ) / 3) with hQdef
  set X := Y / U with hXdef
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set φ := (Nat.totient q : ℝ) with hφdef
  have hφ0 : 0 < φ := by linarith
  set ρ := (q : ℝ) / φ with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h, abs_zero] at h8
    norm_num at h8
  have had : 0 < |δ| := by linarith
  -- `q ≤ x/8Q`
  have hqQ : 8 * Q * q ≤ Y := by
    obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
    have h1 : 8 * (q : ℝ) ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) := by
      have : 8 * (q : ℝ) ≤ |δ| * q := mul_le_mul_of_nonneg_right h8 (by positivity)
      linarith
    have hQe : Q = 3 / 4 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by rw [hQdef, e23]
    rw [e13] at h1
    rw [hQe]
    set u := Y ^ ((1 : ℝ) / 6) with hu
    have h4 : 0 ≤ u ^ 4 := by positivity
    have h5 := mul_le_mul_of_nonneg_left h1 h4
    have e6 : u ^ 4 * (4 / 3 * u ^ 2) = 4 / 3 * Y := by rw [eY]; ring
    have e7 : 8 * (3 / 4 * u ^ 4) * q = 3 / 4 * (u ^ 4 * (8 * q)) := by ring
    rw [e7]
    linarith
  set ε := Y / (2 * U * Q) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 7 := by
    have e : ε = X / (2 * Q) := by
      simp only [hεdef, hXdef]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  set κ := |δ| * q * (1 + Y / (2 * U * Q)) / 4 with hκdef
  have hκ2 : 2 ≤ κ := by
    simp only [hκdef]
    rw [← hεdef]
    have : 8 * 1 ≤ |δ| * q := mul_le_mul h8 hqR (by norm_num) had.le
    have h2 := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + ε)
      (by positivity : (0 : ℝ) ≤ |δ| * q)
    linarith
  have hκ0 : 0 < κ := by linarith
  have hκh : κ ≤ |δ| * q / 2 := by
    simp only [hκdef]
    rw [← hεdef]
    have : 0 ≤ |δ| * q := by positivity
    have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + ε ≤ (2 : ℝ)) this
    linarith
  set ℓ := Real.log κ with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  -- `2V/|δq| ≥ 6.75`, `V/κ > 1`
  have hdV : 6.75 * (|δ| * q) ≤ 2 * V := by
    obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
    simp only [hVdef, vA]
    rw [e13] at hdq ⊢
    linarith
  have hdq0 : 0 < |δ| * q := by positivity
  have hVk : 1 < V / κ := by
    rw [lt_div_iff₀ hκ0]
    linarith
  have hUV : 0 < U * V := mul_pos hU0 hV0
  set L0 := Real.log (Y / (U * V)) with hL0
  have hL0pos : 0 < L0 := Real.log_pos (by linarith)
  set lV := Real.log (V / κ) with hlV
  have hlV0 : 0 < lV := Real.log_pos hVk
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
  set φ' := |δ| * φ / 8 with hφ'def
  have hφ'0 : 0 < φ' := by positivity
  have hXV : X / V = Y / (U * V) := by
    simp only [hXdef]
    rw [div_div]
  -- the maximum `m` of `√(log W/log(W/κ))`
  set lV2 := Real.log (2 * V / (|δ| * q)) with hlV2
  have hlV20 : 0 < lV2 := Real.log_pos (by rw [lt_div_iff₀ hdq0]; linarith)
  have hlogV : 0 < Real.log V := Real.log_pos (by linarith)
  set m := Real.sqrt (Real.log V / Real.log (2 * V / (|δ| * q))) with hmdef
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hm2 : m ^ 2 = Real.log V / lV2 := Real.sq_sqrt (by positivity)
  have hlV2le : lV2 ≤ lV := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hdq0 hκ0]
    have := mul_le_mul_of_nonneg_left hκh (by positivity : (0 : ℝ) ≤ 2 * V)
    linarith
  have hlVsum : lV2 + ℓ ≤ Real.log V := by
    rw [hlV2, hℓdef, ← Real.log_mul (by positivity) hκ0.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hdq0]
    have := mul_le_mul_of_nonneg_left hκh (by positivity : (0 : ℝ) ≤ 2 * V)
    linarith
  -- pointwise facts on `[V, X]`
  have hpos : ∀ W ∈ Icc V X, 0 < W ∧ 0 < Real.log (W / κ) ∧ 1 ≤ Y / (W * U) ∧
      lV ≤ Real.log (W / κ) := by
    intro W hW
    have hW0 : 0 < W := lt_of_lt_of_le hV0 hW.1
    have hVW : V / κ ≤ W / κ := div_le_div_of_nonneg_right hW.1 hκ0.le
    refine ⟨hW0, Real.log_pos (lt_of_lt_of_le hVk hVW), ?_,
      Real.log_le_log (by positivity) hVW⟩
    rw [le_div_iff₀ (mul_pos hW0 hU0), one_mul]
    have := hW.2
    rw [hXdef, le_div_iff₀ hU0] at this
    linarith
  set G : ℝ → ℝ := fun W =>
    Y / (4 * Real.sqrt φ') * (β * (1 + ℓ / Real.log (W / κ)) / 2 +
      (H (Y / (W * U)) + 22.6418 * (Real.sqrt (Y / W) / U)) / β) / W +
    Real.sqrt (0.1048 * ρ * Y) * m / Real.sqrt W +
    0.4618 * Y / (W * Real.sqrt W) with hG
  set G' : ℝ → ℝ := fun W =>
    Y / (4 * Real.sqrt φ') * (β / 2) * (1 / W) +
      Y / (4 * Real.sqrt φ') * (β / 2 * ℓ) * (1 / Real.log (W / κ) / W) +
      Y / (4 * Real.sqrt φ') * (1 / β) * (H (Y / (W * U)) / W) +
      (Y / (4 * Real.sqrt φ') * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y) *
        (1 / (W * Real.sqrt W)) +
      Real.sqrt (0.1048 * ρ * Y) * m * (1 / Real.sqrt W) with hG'
  have hGG' : ∀ W ∈ uIcc V X, G W = G' W := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    obtain ⟨hW0, hLW, -, -⟩ := hpos W hW
    exact g_expand2 Y φ' β ℓ (Real.log (W / κ)) (H (Y / (W * U))) U W _ hW0 hφ'0 hβ0
      hLW.ne' hU0.ne'
  have hpt' : ∀ W ∈ Icc V X, 0 ≤ secI s1f s2f s3f W ∧ secI s1f s2f s3f W ≤ G W := by
    intro W hW
    obtain ⟨hW0, hLW, hs, hlVW⟩ := hpos W hW
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
    -- `S₂` by `eq:procida2`
    set L := Real.log (W / κ) with hLdef
    have hlogW : Real.log W = L + ℓ := by
      rw [hLdef, hℓdef, Real.log_div hW0.ne' hκ0.ne']
      ring
    have hR : W / κ ≤ Y / (|δ| * q) / (q + Y / (4 * W)) := by
      rw [div_le_div_iff₀ hκ0 (by positivity)]
      have hWq : 4 * W * q ≤ ε * Y := by
        have h1 : W * U ≤ Y := by
          have := hW.2
          rw [hXdef, le_div_iff₀ hU0] at this
          linarith
        simp only [hεdef]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have h2 := mul_le_mul h1 hqQ (by positivity) hY0.le
        calc 4 * W * q * (2 * U * Q) = W * U * (8 * Q * q) := by ring
          _ ≤ Y * Y := h2
      have e : Y / (|δ| * q) * κ = (1 + ε) * Y / 4 := by
        simp only [hκdef]
        rw [← hεdef]
        field_simp
      rw [e]
      have : W * (q + Y / (4 * W)) = W * q + Y / 4 := by field_simp
      rw [this]
      have e8 : (1 + ε) * Y / 4 = Y / 4 + ε * Y / 4 := by ring
      rw [e8]
      linarith
    have h1R : 1 < Y / (|δ| * q) / (q + Y / (4 * W)) := by
      have : 1 < W / κ := lt_of_lt_of_le hVk (div_le_div_of_nonneg_right hW.1 hκ0.le)
      linarith
    have hcond : Y / (4 * W) + q < Y / (|δ| * q) := by
      rw [one_lt_div (by positivity)] at h1R
      linarith
    have hs2 := hK.2.2.2.1 hδ0 hcond
    have hlogR : L ≤ Real.log (Y / (|δ| * q) / (q + Y / (4 * W))) :=
      Real.log_le_log (by positivity) hR
    have hmin : min 1 (2 * ((q : ℝ) / φ) / Real.log (Y / (|δ| * q) / (q + Y / (4 * W)))) ≤
        2 * ρ / L :=
      (min_le_right _ _).trans (div_le_div_of_nonneg_left (by positivity) hLW hlogR)
    have hlW0 : 0 ≤ 1 / 2 * W * Real.log W := by
      rw [hlogW]
      positivity
    have hs2' : s2f W ≤ Y * W * (1 + ℓ / L) / (8 * φ') + ρ * W ^ 2 * (L + ℓ) / (2 * L) := by
      have h1 : s2f W ≤ 2 * ρ / L * (Y / (|δ| * q) + W / 2) * (1 / 2 * W * Real.log W) := by
        refine hs2.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hlW0
        exact mul_le_mul_of_nonneg_right hmin (by positivity)
      have e : 2 * ρ / L * (Y / (|δ| * q) + W / 2) * (1 / 2 * W * Real.log W) =
          Y * W * (1 + ℓ / L) / (8 * φ') + ρ * W ^ 2 * (L + ℓ) / (2 * L) := by
        rw [hlogW]
        simp only [hρdef, hφ'def]
        field_simp
      linarith
    -- the three pointwise terms
    have hA := ptA (s1f W) P Y W φ' (1 + ℓ / L) β hY0 hW0 hφ'0 (by positivity) hβ0 hP0 hs1P
    have hLm : (L + ℓ) / L ≤ m ^ 2 := by
      rw [hm2, div_le_div_iff₀ hLW hlV20]
      have h1 : lV2 ≤ L := hlV2le.trans hlVW
      have ha := mul_le_mul_of_nonneg_left h1 hℓ0
      have hb := mul_le_mul_of_nonneg_left hlVsum hLW.le
      calc (L + ℓ) * lV2 = L * lV2 + ℓ * lV2 := by ring
        _ ≤ L * lV2 + ℓ * L := by linarith
        _ = L * (lV2 + ℓ) := by ring
        _ ≤ L * Real.log V := hb
        _ = Real.log V * L := by ring
    have hB := ptB2 (s1f W) ρ Y W ℓ L m hY0 hW0 hρ0 hℓ0 hLW hm0 hLm hs1c
    have hC := ptC (s1f W) (s3f W) Y W hY0 hW0 hs1c h3n (by
      have : 2.0341 * W ≤ 0.0001 * Y := by
        have := mul_le_mul_of_nonneg_left hW.2 (by norm_num : (0 : ℝ) ≤ 2.0341)
        linarith
      linarith)
    have ha0 : 0 ≤ Y * W * (1 + ℓ / L) / (8 * φ') := by positivity
    have hb0 : 0 ≤ ρ * W ^ 2 * (L + ℓ) / (2 * L) := by positivity
    have hsplit : Real.sqrt (s1f W * s2f W) ≤ Real.sqrt (s1f W * (Y * W * (1 + ℓ / L) / (8 * φ')))
        + Real.sqrt (s1f W * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) := by
      refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs2' h1n)).trans ?_
      rw [mul_add]
      exact sqrt_add_le' _ _ (mul_nonneg h1n ha0) (mul_nonneg h1n hb0)
    have hsec : secI s1f s2f s3f W ≤
        Real.sqrt (s1f W * (Y * W * (1 + ℓ / L) / (8 * φ'))) / W +
          Real.sqrt (s1f W * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) / W +
          Real.sqrt (s1f W * s3f W) / W := by
      unfold secI
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hW0.le
    refine hsec.trans ?_
    simp only [hG, ← hLdef, ← hP]
    linarith
  -- integrability of the pieces
  have hcont_logc : ContinuousOn (fun W => Real.log (W / κ)) (uIcc V X) :=
    Real.continuousOn_log.comp (continuousOn_id.div_const κ) fun W hW => by
      rw [uIcc_of_le hVX] at hW
      exact (div_pos (hpos W hW).1 hκ0).ne'
  have hii1 : IntervalIntegrable (fun W : ℝ => 1 / W) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div continuousOn_id fun W hW => by
      rw [uIcc_of_le hVX] at hW
      exact (hpos W hW).1.ne'
  have hii2 : IntervalIntegrable (fun W => 1 / Real.log (W / κ) / W) volume V X := by
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
  have hGi' : IntervalIntegrable G' volume V X :=
    (((((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)).add
      (hii4.const_mul _)).add (hii5.const_mul _))
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
      Y / (4 * Real.sqrt φ') * (β / 2) * (∫ W in V..X, 1 / W) +
      Y / (4 * Real.sqrt φ') * (β / 2 * ℓ) * (∫ W in V..X, 1 / Real.log (W / κ) / W) +
      Y / (4 * Real.sqrt φ') * (1 / β) * (∫ W in V..X, H (Y / (W * U)) / W) +
      (Y / (4 * Real.sqrt φ') * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y) *
        (∫ W in V..X, 1 / (W * Real.sqrt W)) +
      Real.sqrt (0.1048 * ρ * Y) * m * (∫ W in V..X, 1 / Real.sqrt W) := by
    simp only [hG']
    rw [intervalIntegral.integral_add _ (hii5.const_mul _),
      intervalIntegral.integral_add _ (hii4.const_mul _),
      intervalIntegral.integral_add _ (hii3.const_mul _),
      intervalIntegral.integral_add (hii1.const_mul _) (hii2.const_mul _)]
    · simp only [intervalIntegral.integral_const_mul]
    · exact (hii1.const_mul _).add (hii2.const_mul _)
    · exact ((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)
    · exact (((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)).add
        (hii4.const_mul _)
  -- the five integrals
  have i1 : ∫ W in V..X, 1 / W = L0 := by rw [int_inv V X hV0 hVX, hXV]
  have hlogXk : Real.log (X / κ) = lV + L0 := by
    rw [show X / κ = V / κ * (X / V) by field_simp, Real.log_mul (by positivity)
      (by positivity), hXV]
  have i2 : ∫ W in V..X, 1 / Real.log (W / κ) / W = Real.log (1 + L0 / lV) := by
    rw [int_loglog κ V X hκ0 hVk hVX, hlogXk, ← Real.log_div (by positivity) hlV0.ne']
    congr 1
    field_simp
  have i3 : ∫ W in V..X, H (Y / (W * U)) / W ≤ 0.15107 * L0 + 0.0231 := by
    rw [hsub]
    exact hH.2.2 _ hT1
  have i4 := int_rsqrt3 V X hV0 hVX
  have i5 := int_rsqrt V X hV0 hVX
  -- assembly
  have hcurV : Real.sqrt Y / U / Real.sqrt V ≤ 3.062e-4 := by
    have := cur_le Y U V V hY0 hU0 hV0 le_rfl hcur
    rwa [Real.sqrt_div' Y hV0.le, div_div, mul_comm, ← div_div] at this
  have hmain := main_algC Y φ' U V L0 (Real.log (1 + L0 / lV)) ℓ β hY0 hφ'0 hL0pos
    (Real.log_nonneg (by
      have : 0 ≤ L0 / lV := by positivity
      linarith)) hℓ0 hcurV hβdef
  have hB : 4 * (Real.sqrt (0.1048 * ρ * Y) * m * (2 * Real.sqrt X)) ≤
      kap2 * Real.sqrt (2 * q / φ) * m * (Y / Real.sqrt U) := by
    have e0 : Real.sqrt (0.1048 * ρ * Y) = Real.sqrt 0.1048 * Real.sqrt ρ * Real.sqrt Y := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    have e2 : Real.sqrt (2 * q / φ) = Real.sqrt 2 * Real.sqrt ρ := by
      rw [mul_div_assoc, Real.sqrt_mul (by norm_num)]
    have eYU : Real.sqrt Y * Real.sqrt X = Y / Real.sqrt U := by
      rw [hXdef, Real.sqrt_div' Y hU0.le]
      have := Real.mul_self_sqrt hY0.le
      have hsU : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU0
      field_simp
      linarith
    have h01 : Real.sqrt 0.1048 ≤ 0.323729 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hs2 : 1.41421 ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hc : 8 * Real.sqrt 0.1048 ≤ kap2 * Real.sqrt 2 := by
      simp only [kap2]
      linarith
    have hrest : 0 ≤ Real.sqrt ρ * m * (Y / Real.sqrt U) := by positivity
    have e4 : 4 * (Real.sqrt (0.1048 * ρ * Y) * m * (2 * Real.sqrt X)) =
        8 * Real.sqrt 0.1048 * (Real.sqrt ρ * m * (Y / Real.sqrt U)) := by
      rw [e0, ← eYU]
      ring
    rw [e4, e2]
    have := mul_le_mul_of_nonneg_right hc hrest
    have e5 : kap2 * (Real.sqrt 2 * Real.sqrt ρ) * m * (Y / Real.sqrt U) =
        kap2 * Real.sqrt 2 * (Real.sqrt ρ * m * (Y / Real.sqrt U)) := by ring
    rw [e5]
    exact this
  have hC : 4 * (0.4618 * Y * (2 / Real.sqrt V)) ≤ kap9 * (Y / Real.sqrt V) := by
    simp only [kap9]
    have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
    have : 0 ≤ Y / Real.sqrt V := by positivity
    have e : 4 * (0.4618 * Y * (2 / Real.sqrt V)) = 3.6944 * (Y / Real.sqrt V) := by ring
    rw [e]
    linarith
  -- conclude
  refine (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans ?_
  rw [hGint, hGint', i1, i2]
  have hk3 : 0 ≤ Y / (4 * Real.sqrt φ') * (1 / β) := by positivity
  have hk4 : 0 ≤ Y / (4 * Real.sqrt φ') * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y := by
    positivity
  have hk5 : 0 ≤ Real.sqrt (0.1048 * ρ * Y) * m := by positivity
  have b3 := mul_le_mul_of_nonneg_left i3 hk3
  have b4 := mul_le_mul_of_nonneg_left i4 hk4
  have b5 := mul_le_mul_of_nonneg_left i5 hk5
  have hfirst : Y / Real.sqrt (2 * φ') * Real.sqrt (A' * B') =
      2 * Y / Real.sqrt (|δ| * φ) * Real.sqrt A' * Real.sqrt B' := by
    have e1 : 2 * φ' = |δ| * φ / 4 := by simp only [hφ'def]; ring
    have hs : Real.sqrt (|δ| * φ / 4) = Real.sqrt (|δ| * φ) / 2 := by
      rw [Real.sqrt_div' _ (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have hsd : 0 < Real.sqrt (|δ| * φ) := Real.sqrt_pos.mpr (by positivity)
    rw [e1, hs, Real.sqrt_mul hA0.le]
    field_simp
  have herik : erikC Y U V Q δ q = 2 * Y / Real.sqrt (|δ| * φ) * Real.sqrt A' * Real.sqrt B' +
      kap2 * Real.sqrt (2 * q / φ) * m * (Y / Real.sqrt U) + kap9 * (Y / Real.sqrt V) := by
    unfold erikC
    have e5 : 4 * V / (|δ| * (1 + Y / (2 * U * Q)) * q) = V / κ := by
      simp only [hκdef]
      field_simp
    rw [e5]
  rw [herik, ← hfirst]
  linarith [hmain, hB, hC]

/-- **`EriksagaAtC` from the deep links** (`SecInt` and `ErikCalcC` discharged). -/
theorem eriksagaAtC_of_deep (hm : Menson2C) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) : EriksagaAtC :=
  eriksagaAtC_of secInt_holds hm hk hc hl h13 erikCalcC_holds

end Principia.Common.TernaryGoldbach.T2SC
