/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIVin1Calc
import Principia.Common.TernaryGoldbach.TypeIISpineC

set_option autoImplicit false

/-!
# `T2SC.SecIICalcC` PROVED — the second-choice Type II calculus, without `eq:garn1a`

`secIICalcC_holds : T2SC.SecIICalcC`, with NO hypotheses: no cited computation, no literature
input (in particular no `GS.RS62Thm15` for `q/φ(q)`), and no `eq:garn1a`. Hence
`secIIAtC_of_deep : Menson2C → Kraken → HC.KastCited → KastLarge → EB.RS62Thm13 → SecIIAt`.

**The route differs from the book's, and is stronger.** `minarctotals.tex` 1977-2235 runs case
(a) through `eq:vinland2` (i.e. `eq:garn1a`, whose `x/4φ(q)` costs the factor `ϝ(q) ≈ e^γ log t`)
and case (b) through `eq:vinlandsaga`, reaching `0.275964`. Here both cases go through ONE uniform
bound on the `prop:kraken` factor (`kbound`), for every `W ∈ [V, x/U]`:

```
 S₂(W) ≤ (0.75325538 x^{2/3} + 1.5x/W) · ½W log W
   case (a) q > x^{1/3}/6:            eq:garn1b at ρ = q/Q   (x/8q < (3/4)x^{2/3}, max(1,2ρ) ≤ 1+2ρ)
   case (b) q ≤ x^{1/3}/6 < (3/4)|δ|q: eq:procida3 at ρ = 1/2 (x/|δ|q < (3/4)x^{2/3})
```

and the rest is the `T2S.Vin1Calc` pattern: `√(S₁S₂)` split, AM-GM in `β = 1.819√(log x)` against
`∫_1^{x/UV} H₂ ds/s ≤ 0.15107 log(x/UV) + 0.0231` (`HOkC`, the `eq:passi` erratum absorbed) and
`∫_V^{x/U} log W dW/W ≤ (log x)²/6`; the `x/W`, `S₃` and `eq:menson2` error parts by
`∫_V^∞ W^{-3/2} = 2/√V`. Total (`t = log x ≥ 54`, `x^{5/6}t^{3/2}` units):
`0.11243 + 0.11246 + 4.74876/t + 6.77328/t^{3/2} ≤ 0.3299 ≤ 0.34`. The same bound with exact
logarithms and the optimal `β` peaks at `0.2369` (`t = log 3.4·10²³`), tending to `0.2247`
(`scratchpad/secII/num.py`), below the book's own `0.275964`.

**Consequences for the spine.** (1) The `TypeIISpine` finding (the book applies `eq:garn1a` at the
second choice outside its `3.5W ≤ Q` hypothesis) no longer touches `SecIIAt`: `eq:garn1a` is not
used here at all. (2) `T2X.SecIICaseA1`/`A2`/`B` are superseded (each is an instance of
`SecIICalcC`). (3) `T2S.SecIICalc` (printed `eq:velib`) follows too (`secIICalc_holds`).
-/

namespace Principia.Common.TernaryGoldbach.T2SII

open MeasureTheory Set
open scoped Interval
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
open Principia.Common.TernaryGoldbach.T2S Principia.Common.TernaryGoldbach.T2SC

/-- AM-GM: `√(pl) ≤ (kp + l/k)/2` for `k > 0`. -/
theorem sqrt_mul_le_amgm (p l k : ℝ) (hp : 0 ≤ p) (hl : 0 ≤ l) (hk : 0 < k) :
    Real.sqrt (p * l) ≤ (k * p + l / k) / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  have e : ((k * p + l / k) / 2) ^ 2 = ((k * p - l / k) / 2) ^ 2 + p * l := by
    field_simp
    ring
  rw [e]
  nlinarith [sq_nonneg ((k * p - l / k) / 2)]

/-- `∫_V^X log W dW/W = (log² X − log² V)/2`. -/
theorem int_logdiv (V X : ℝ) (hV : 0 < V) (hVX : V ≤ X) :
    ∫ W in V..X, Real.log W / W = (Real.log X ^ 2 - Real.log V ^ 2) / 2 := by
  have hd : ∀ W ∈ uIcc V X, HasDerivAt (fun W => Real.log W ^ 2 / 2) (Real.log W / W) W := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    have hW0 : 0 < W := lt_of_lt_of_le hV hW.1
    have h := ((hasDerivAt_pow 2 (Real.log W)).comp W (Real.hasDerivAt_log hW0.ne')).div_const 2
    refine h.congr_deriv ?_
    norm_num
    ring
  have hc : ContinuousOn (fun W : ℝ => Real.log W / W) (uIcc V X) := by
    rw [uIcc_of_le hVX]
    exact (Real.continuousOn_log.mono fun W hW => (lt_of_lt_of_le hV hW.1).ne').div
      continuousOn_id fun W hW => (lt_of_lt_of_le hV hW.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- `0.115106 s³ ≥ 4.74876 s + 6.77328` for `s ≥ 7.34`, scaled by `w > 0`. -/
theorem final_sum (w s A B C : ℝ) (hw : 0 < w) (hs : 7.34 ≤ s)
    (hA : A ≤ 0.112431 * w * s ^ 3) (hB : B ≤ 0.112463 * w * s ^ 3)
    (hC : C ≤ (4.74876 * s + 6.77328) * w) : A + B + C ≤ 0.34 * w * s ^ 3 := by
  have hs2 : 53.8 ≤ s ^ 2 := by nlinarith
  have h1 : 6.19 * s ≤ 0.115106 * s ^ 3 := by nlinarith
  have h2 : 4.74876 * s + 6.77328 ≤ 0.115106 * s ^ 3 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hw.le
  nlinarith

/-- **The uniform `S₂` factor at the second choice**: in case (a) `q > u²/6` by `eq:garn1b` at
`ρ = q/Q`, in case (b) `q ≤ u²/6 < (3/4)|δ|q` by `eq:procida3` at `ρ = 1/2`, the `prop:kraken`
factor is at most `0.75325538u⁴ + 1.5Y/W` (`Y = u⁶`, `U = cu²`, `Q = X = u⁴/c`, `W ≤ X`). No
`eq:garn1a`, no `φ(q)`. -/
theorem kbound (Y u c X W δ P S : ℝ) (q : ℕ) (hu : 8000 ≤ u) (hc1 : 1224.5 ≤ c)
    (hc2 : c ≤ 1224.75) (hY : Y = u ^ 6) (hX : X = u ^ 4 / c) (hW0 : 0 < W) (hWX : W ≤ X)
    (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ X) (hP : 0 ≤ P)
    (hcase : u ^ 2 / 6 < q ∨ 4 / 3 * u ^ 2 < |δ| * q) (hk : KrakenAt Y X δ q W P S) :
    S ≤ (0.75325538 * u ^ 4 + 1.5 * (Y / W)) * P := by
  have hu0 : 0 < u := by linarith
  have hc0 : 0 < c := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hX0 : 0 < X := by rw [hX]; positivity
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hu2 : 6.4e7 ≤ u ^ 2 := by nlinarith
  have hYW : 0 ≤ Y / W := by positivity
  have e4 : Y / (4 * X) = c * u ^ 2 / 4 := by
    rw [hX, hY]
    field_simp
  have htiny : c * u ^ 2 / 4 ≤ 0.000005 * u ^ 4 := by
    have h1 : c * u ^ 2 / 4 ≤ 306.2 * u ^ 2 := by nlinarith
    nlinarith
  have hX4 : X ≤ 0.00081667 * u ^ 4 := by
    rw [hX, div_le_iff₀ hc0]
    nlinarith [pow_pos hu0 4]
  have eW : Y / (2 * W) = Y / W / 2 := by
    field_simp
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_refl _) hP)
  rcases lt_or_ge (u ^ 2 / 6) (q : ℝ) with hA | hB
  · -- case (a): `eq:garn1b` at `ρ = q/Q`
    set ρ := (q : ℝ) / X with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hX0]; exact hqX
    have hρQ : (q : ℝ) ≤ ρ * X := by rw [hρ, div_mul_cancel₀ _ hX0.ne']
    have h := hk.1 ρ hρ0 hρ1 hρQ
    have hm : max 1 (2 * ρ) ≤ 1 + 2 * ρ := max_le (by linarith) (by linarith)
    have hpos : 0 ≤ Y / (8 * q) + Y / (2 * W) := by positivity
    have hF : max 1 (2 * ρ) * (Y / (8 * q) + Y / (2 * W)) ≤
        (1 + 2 * ρ) * (Y / (8 * q) + Y / (2 * W)) := mul_le_mul_of_nonneg_right hm hpos
    have e1 : (1 + 2 * ρ) * (Y / (8 * q) + Y / (2 * W)) =
        Y / (8 * q) + Y / (4 * X) + Y / (2 * W) + ρ * (Y / W) := by
      rw [hρ]
      field_simp
      ring
    have hρY : ρ * (Y / W) ≤ Y / W := mul_le_of_le_one_left hYW hρ1
    have h8q : Y / (8 * q) ≤ 0.75 * u ^ 4 := by
      have h6 : 0 < u ^ 2 / 6 := by positivity
      calc Y / (8 * q) ≤ Y / (8 * (u ^ 2 / 6)) :=
            div_le_div_of_nonneg_left hY0.le (by positivity) (by linarith)
        _ = 0.75 * u ^ 4 := by
            rw [hY]
            field_simp
            ring
    have hfac : (max 1 (2 * ρ) * (Y / (8 * q) + Y / (2 * W)) + W / 2 + 2 * q) ≤
        0.75325538 * u ^ 4 + 1.5 * (Y / W) := by
      rw [e1, e4, eW] at hF
      rw [eW]
      have hq2 : (q : ℝ) ≤ X := hqX
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right hfac hP)
  · -- case (b): `eq:procida3` at `ρ = 1/2`
    have hdq : 4 / 3 * u ^ 2 < |δ| * q := by
      rcases hcase with h | h
      · exact absurd hB (not_le.mpr h)
      · exact h
    have hδ : δ ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul] at hdq
      have : 0 < 4 / 3 * u ^ 2 := by positivity
      linarith
    have hqh : (q : ℝ) ≤ 1 / 2 * X := by
      have : u ^ 2 / 6 ≤ 1 / 2 * X := by
        rw [hX, show 1 / 2 * (u ^ 4 / c) = u ^ 4 / (2 * c) by ring,
          le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have h := hk.2.2.2.2 hδ (1 / 2) (by norm_num) (by norm_num) hqh
    have hdq0 : 0 < |δ| * q := lt_trans (by positivity) hdq
    have h1 : Y / (|δ| * q) ≤ 0.75 * u ^ 4 := by
      calc Y / (|δ| * q) ≤ Y / (4 / 3 * u ^ 2) :=
            div_le_div_of_nonneg_left hY0.le (by positivity) hdq.le
        _ = 0.75 * u ^ 4 := by
            rw [hY]
            field_simp
            ring
    have e2 : Y / (8 * (1 - 1 / 2) * X) = Y / (4 * X) := by ring_nf
    have e3 : Y / (4 * (1 - 1 / 2) * W) = Y / W / 2 := by
      field_simp
      ring
    have hfac : Y / (|δ| * q) + W / 2 + Y / (8 * (1 - 1 / 2) * X) + Y / (4 * (1 - 1 / 2) * W) ≤
        0.75325538 * u ^ 4 + 1.5 * (Y / W) := by
      rw [e2, e4, e3]
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right hfac hP)

/-- `2.449 ≤ √6 ≤ 2.4495`, so `1224.5 ≤ 500√6 ≤ 1224.75`. -/
theorem c_bounds : 1224.5 ≤ 500 * Real.sqrt 6 ∧ 500 * Real.sqrt 6 ≤ 1224.75 := by
  have h1 : (2.449 : ℝ) ≤ Real.sqrt 6 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h2 : Real.sqrt 6 ≤ 2.4495 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  constructor <;> linarith

/-- `log Y ≥ 54` for `Y ≥ 3.4·10²³` (`2⁷⁸ ≤ 3.4·10²³`, `78 log 2 ≥ 54.06`). -/
theorem log_ge_54 (Y : ℝ) (hY : 3.4e23 ≤ Y) : 54 ≤ Real.log Y := by
  have h2 : (2 : ℝ) ^ 78 ≤ Y := le_trans (by norm_num) hY
  have h := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h
  push_cast at h
  have := Real.log_two_gt_d9
  linarith

set_option maxHeartbeats 1000000 in
-- One long proof assembling three integrals and the pointwise bounds; the default 200000
-- heartbeats run out in the final elaboration, not in any single tactic.
/-- **`T2SC.SecIICalcC`, PROVED**: the second-choice Type II calculus closes at `0.34` with the
corrected `eq:velib` (`HOkC`), from `eq:garn1b` (case (a)) and `eq:procida3` (case (b)) only. -/
theorem secIICalcC_holds : SecIICalcC := by
  intro Y hY δ q hq hqQ hδ hcase H s1f s2f s3f hH hpt
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, e56, e13, eY, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hudef
  have hu0 : 0 < u := by linarith
  have hu2 : 6.4e7 ≤ u ^ 2 := by nlinarith
  obtain ⟨hc1, hc2⟩ := c_bounds
  set c := 500 * Real.sqrt 6 with hcdef
  have hc0 : 0 < c := by linarith
  set U := u2 Y with hUdef
  have hUe : U = c * u ^ 2 := by
    rw [hUdef, hcdef]
    unfold u2
    rw [e13]
  set V := v2 Y with hVdef
  have hVe : V = u ^ 2 / 3 := by
    rw [hVdef]
    unfold v2
    rw [e13]
  have hU0 : 0 < U := by rw [hUe]; positivity
  have hV0 : 0 < V := by rw [hVe]; positivity
  have hV1 : 1 ≤ V := by rw [hVe]; linarith
  have hq2 : q2 Y = Y / U := rfl
  set X := Y / U with hXdef
  have hXe : X = u ^ 4 / c := by
    rw [hXdef, hUe, eY]
    field_simp
  have hX0 : 0 < X := by rw [hXe]; positivity
  have hVX : V ≤ X := by
    rw [hVe, hXe, div_le_div_iff₀ (by norm_num) hc0]
    have := mul_le_mul_of_nonneg_left (show c ≤ 3 * u ^ 2 by linarith) (sq_nonneg u)
    linarith
  rw [hq2] at hqQ hpt
  rw [e13] at hcase
  -- `t = log Y`, `s = √t`
  set t := Real.log Y with htdef
  have ht : 54 ≤ t := log_ge_54 Y hY
  set s := Real.sqrt t with hsdef
  have hst : s ^ 2 = t := Real.sq_sqrt (by linarith)
  have hs7 : 7.34 ≤ s := by
    rw [hsdef, Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hs0 : 0 < s := by linarith
  -- the logarithms
  have hlX : Real.log X ≤ 2 / 3 * t := by
    have h1 : X ≤ u ^ 4 := by
      rw [hXe]
      exact div_le_self (by positivity) (by linarith)
    have h2 := Real.log_le_log hX0 h1
    rw [Real.log_pow] at h2
    push_cast at h2
    rw [eL]
    linarith
  have hlV0 : 0 ≤ Real.log V := Real.log_nonneg hV1
  have hlVX : Real.log V ≤ Real.log X := Real.log_le_log hV0 hVX
  have hsum : Real.log X + Real.log V ≤ t := by
    rw [← Real.log_mul hX0.ne' hV0.ne', htdef]
    refine Real.log_le_log (by positivity) ?_
    rw [hXe, hVe, eY]
    rw [show u ^ 4 / c * (u ^ 2 / 3) = u ^ 6 / (3 * c) by ring]
    exact div_le_self (by positivity) (by linarith)
  set L0 := Real.log (Y / (U * V)) with hL0def
  have eUV : Y / (U * V) = u ^ 2 * (3 / c) := by
    rw [eY, hUe, hVe]
    field_simp
  have hL0 : L0 ≤ t / 3 - 0.99 := by
    rw [hL0def, eUV, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / c by positivity)
    have h4 : 3 / c ≤ 0.01 := by
      rw [div_le_iff₀ hc0]
      linarith
    push_cast
    rw [eL]
    linarith
  have hdiff : Real.log X - Real.log V = L0 := by
    rw [← Real.log_div hX0.ne' hV0.ne', hL0def, hXdef, div_div]
  have hM : (Real.log X ^ 2 - Real.log V ^ 2) / 2 ≤ t ^ 2 / 6 := by
    have e : Real.log X ^ 2 - Real.log V ^ 2 =
        (Real.log X - Real.log V) * (Real.log X + Real.log V) := by ring
    have h1 : Real.log X - Real.log V ≤ t / 3 := by linarith
    have h2 := mul_le_mul h1 hsum (by linarith) (by linarith)
    rw [e]
    linarith
  -- `κ = 22.6418√Y/U`
  set κ := 22.6418 * Real.sqrt Y / U with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hsY : Real.sqrt Y = u ^ 3 := by
    rw [eY, show u ^ 6 = (u ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsV : Real.sqrt V = u / Real.sqrt 3 := by
    rw [hVe, Real.sqrt_div' _ (by norm_num), Real.sqrt_sq hu0.le]
  have hs3a : Real.sqrt 3 ≤ 1.73206 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs3p : 0 < Real.sqrt 3 := by positivity
  have hsV0 : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  have hκV : κ / Real.sqrt V ≤ 0.03203 := by
    have e : κ / Real.sqrt V = 22.6418 * Real.sqrt 3 / c := by
      rw [hκdef, hsY, hsV, hUe]
      field_simp
    rw [e, div_le_iff₀ hc0]
    linarith
  have hYV : Y / Real.sqrt V ≤ 1.7321 * u ^ 5 := by
    have e : Y / Real.sqrt V = Real.sqrt 3 * u ^ 5 := by
      rw [hsV, eY]
      field_simp
    rw [e]
    have : 0 < u ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_right hs3a this.le
    linarith
  have hXY : 2.0341 * X ≤ 0.0001 * Y := by
    have hU2 : 20341 ≤ U := by
      rw [hUe]
      have := mul_le_mul hc1 hu2 (by norm_num) hc0.le
      linarith
    rw [hXdef, ← mul_div_assoc, div_le_iff₀ hU0]
    have := mul_le_mul_of_nonneg_left hU2 hY0.le
    linarith
  -- the constants
  set r := 0.6137 * u ^ 5 with hrdef
  have hr0 : 0 < r := by positivity
  set k := 1.819 * s with hkdef
  have hk0 : 0 < k := by positivity
  -- pointwise facts on `[V, X]`
  have hpos : ∀ W ∈ Icc V X, 0 < W ∧ 1 ≤ Y / (W * U) ∧ 0 ≤ Real.log W ∧
      Real.log W ≤ Real.log X := by
    intro W hW
    have hW0 : 0 < W := lt_of_lt_of_le hV0 hW.1
    refine ⟨hW0, ?_, Real.log_nonneg (le_trans hV1 hW.1), Real.log_le_log hW0 hW.2⟩
    rw [le_div_iff₀ (mul_pos hW0 hU0), one_mul]
    have := hW.2
    rw [hXdef, le_div_iff₀ hU0] at this
    linarith
  set G : ℝ → ℝ := fun W =>
    r * k / 2 * (H (Y / (W * U)) / W) + r / (2 * k) * (Real.log W / W) +
      (r * k * κ / 2 + 0.3427 * Y * s + 0.4888 * Y) * (1 / (W * Real.sqrt W)) with hG
  have hpt' : ∀ W ∈ Icc V X, 0 ≤ secI s1f s2f s3f W ∧ secI s1f s2f s3f W ≤ G W := by
    intro W hW
    obtain ⟨hW0, hs1, hlW0, hlWX⟩ := hpos W hW
    obtain ⟨h1n, h2n, h3n, hS1, hK, hS3⟩ := hpt W hW
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
    have hnn : 0 ≤ secI s1f s2f s3f W := by
      unfold secI
      positivity
    refine ⟨hnn, ?_⟩
    set P := H (Y / (W * U)) + κ / Real.sqrt W with hP
    have hH0 := (hH.1 _ hs1).1
    have hH1 := (hH.1 _ hs1).2
    have hκW : κ / Real.sqrt W ≤ 0.03203 :=
      (div_le_div_of_nonneg_left hκ0 hsV0 (Real.sqrt_le_sqrt hW.1)).trans hκV
    have hP0 : 0 ≤ P := by positivity
    have hPle : P ≤ 0.2348 := by
      have := two_div_pi_sq
      linarith
    -- `S₁`
    have hs1P : s1f W ≤ Y / W * P := by
      unfold S1Bd at hS1
      rw [log_pow_three_halves (Y / W) (by positivity), Real.sqrt_div' Y hW0.le] at hS1
      have e : Y / W * P = Y / W * H (Y / (W * U)) +
          22.6418 * (Y / W * (Real.sqrt Y / Real.sqrt W)) / U := by
        rw [hP, hκdef]
        field_simp
      linarith
    -- `S₂`, uniform over the two cases
    have hs2K := kbound Y u c X W δ (1 / 2 * W * Real.log W) (s2f W) q hu hc1 hc2 eY hXe hW0
      hW.2 hq hqQ (by positivity) hcase hK
    -- `S₃`
    have hs3' : s3f W ≤ 1.0172 * Y := by
      have := mul_le_mul_of_nonneg_left hW.2 (by norm_num : (0 : ℝ) ≤ 2.0341)
      linarith
    -- `√(S₁S₂)`
    have h12 : s1f W * s2f W ≤
        r ^ 2 * (P * Real.log W) + 0.75 * Y ^ 2 * (P * Real.log W) / W := by
      have h := mul_le_mul hs1P hs2K h2n (by positivity)
      have e : Y / W * P * ((0.75325538 * u ^ 4 + 1.5 * (Y / W)) * (1 / 2 * W * Real.log W)) =
          r ^ 2 * (P * Real.log W) + 0.75 * Y ^ 2 * (P * Real.log W) / W := by
        rw [hrdef, eY]
        field_simp
        ring
      linarith
    have hPl : P * Real.log W ≤ 0.2348 * (2 / 3 * t) :=
      mul_le_mul hPle (hlWX.trans hlX) hlW0 (by norm_num)
    have e1 : Real.sqrt (r ^ 2 * (P * Real.log W)) = r * Real.sqrt (P * Real.log W) := by
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le]
    have e2 : Real.sqrt (0.75 * Y ^ 2 * (P * Real.log W) / W) ≤
        0.3427 * Y * s / Real.sqrt W := by
      rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, mul_pow, Real.sq_sqrt hW0.le, hst]
      refine div_le_div_of_nonneg_right ?_ hW0.le
      have hY2 : 0 ≤ Y ^ 2 := sq_nonneg Y
      linarith [mul_le_mul_of_nonneg_left hPl hY2, mul_nonneg hY2 (by linarith : (0 : ℝ) ≤ t)]
    have h12' : Real.sqrt (s1f W * s2f W) ≤
        r * Real.sqrt (P * Real.log W) + 0.3427 * Y * s / Real.sqrt W := by
      refine (Real.sqrt_le_sqrt h12).trans ?_
      refine (sqrt_add_le' _ _ (by positivity) (by positivity)).trans ?_
      rw [e1]
      linarith
    have hA : r * Real.sqrt (P * Real.log W) ≤ r * ((k * P + Real.log W / k) / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_le_amgm P (Real.log W) k hP0 hlW0 hk0) hr0.le
    -- `√(S₁S₃)`
    have hC : Real.sqrt (s1f W * s3f W) ≤ 0.4888 * Y / Real.sqrt W := by
      rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, Real.sq_sqrt hW0.le]
      have h1 : s1f W ≤ Y / W * 0.2348 :=
        hs1P.trans (mul_le_mul_of_nonneg_left hPle (by positivity))
      have h := mul_le_mul h1 hs3' h3n (by positivity)
      have e : Y / W * 0.2348 * (1.0172 * Y) = 0.23883856 * Y ^ 2 / W := by
        field_simp
        ring
      rw [e] at h
      refine h.trans (div_le_div_of_nonneg_right ?_ hW0.le)
      linarith [sq_nonneg Y]
    have hsec : secI s1f s2f s3f W ≤
        (r * ((k * P + Real.log W / k) / 2) + 0.3427 * Y * s / Real.sqrt W +
          0.4888 * Y / Real.sqrt W) / W := by
      unfold secI
      exact div_le_div_of_nonneg_right (by linarith) hW0.le
    have eG : (r * ((k * P + Real.log W / k) / 2) + 0.3427 * Y * s / Real.sqrt W +
          0.4888 * Y / Real.sqrt W) / W = G W := by
      simp only [hG, hP]
      field_simp
      ring
    rw [← eG]
    exact hsec
  -- integrability
  have hT1 : 1 ≤ Y / (U * V) := by
    rw [le_div_iff₀ (mul_pos hU0 hV0), one_mul]
    have := hVX
    rw [hXdef, le_div_iff₀ hU0] at this
    linarith
  obtain ⟨hii1, hsub⟩ := int_subst H Y U V hY0 hU0 hV0 hVX (hH.2.1 _ hT1)
  rw [← hXdef] at hii1 hsub
  have hii2 : IntervalIntegrable (fun W : ℝ => Real.log W / W) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hVX]
    exact (Real.continuousOn_log.mono fun W hW => (lt_of_lt_of_le hV0 hW.1).ne').div
      continuousOn_id fun W hW => (lt_of_lt_of_le hV0 hW.1).ne'
  have hii3 : IntervalIntegrable (fun W : ℝ => 1 / (W * Real.sqrt W)) volume V X := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hVX]
    exact continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      fun W hW => by
        have := lt_of_lt_of_le hV0 hW.1
        exact (mul_pos this (Real.sqrt_pos.mpr this)).ne'
  have hGi : IntervalIntegrable G volume V X :=
    ((hii1.const_mul _).add (hii2.const_mul _)).add (hii3.const_mul _)
  have hmono : ∫ W in V..X, secI s1f s2f s3f W ≤ ∫ W in V..X, G W := by
    rw [intervalIntegral.integral_of_le hVX, intervalIntegral.integral_of_le hVX]
    refine integral_mono_of_nonneg ?_
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hVX).mp hGi) ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun W hW =>
        (hpt' W (Ioc_subset_Icc_self hW)).1
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun W hW =>
        (hpt' W (Ioc_subset_Icc_self hW)).2
  have hGint : ∫ W in V..X, G W =
      r * k / 2 * (∫ W in V..X, H (Y / (W * U)) / W) +
        r / (2 * k) * (∫ W in V..X, Real.log W / W) +
        (r * k * κ / 2 + 0.3427 * Y * s + 0.4888 * Y) *
          (∫ W in V..X, 1 / (W * Real.sqrt W)) := by
    simp only [hG]
    rw [intervalIntegral.integral_add ((hii1.const_mul _).add (hii2.const_mul _))
      (hii3.const_mul _), intervalIntegral.integral_add (hii1.const_mul _) (hii2.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  have i1 : ∫ W in V..X, H (Y / (W * U)) / W ≤ 0.15107 * L0 + 0.0231 := by
    rw [hsub]
    exact hH.2.2 _ hT1
  have i2 := int_logdiv V X hV0 hVX
  have i3 := int_rsqrt3 V X hV0 hVX
  -- assembly
  rw [e56, log_pow_three_halves t (by linarith)]
  refine (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans ?_
  rw [hGint, i2]
  set J := 2 / Real.sqrt V with hJ
  have hJ0 : 0 ≤ J := by positivity
  have hκJ : κ * J ≤ 0.06406 := by
    have e : κ * J = 2 * (κ / Real.sqrt V) := by rw [hJ]; ring
    rw [e]
    linarith
  have hYJ : Y * J ≤ 3.4642 * u ^ 5 := by
    have e : Y * J = 2 * (Y / Real.sqrt V) := by rw [hJ]; ring
    rw [e]
    linarith
  have hw : 0 < u ^ 5 := by positivity
  have hw3 : 0 ≤ u ^ 5 * s ^ 3 := by positivity
  have hc1' : 0 ≤ r * k / 2 := by positivity
  have hc2' : 0 ≤ r / (2 * k) := by positivity
  have hc3' : 0 ≤ r * k * κ / 2 + 0.3427 * Y * s + 0.4888 * Y := by positivity
  have bI1 : r * k / 2 * (∫ W in V..X, H (Y / (W * U)) / W) ≤
      r * k / 2 * (0.0503567 * t - 0.12646) := by
    refine (mul_le_mul_of_nonneg_left i1 hc1').trans (mul_le_mul_of_nonneg_left ?_ hc1')
    linarith
  have bM : r / (2 * k) * ((Real.log X ^ 2 - Real.log V ^ 2) / 2) ≤ r / (2 * k) * (t ^ 2 / 6) :=
    mul_le_mul_of_nonneg_left hM hc2'
  have bI3 : (r * k * κ / 2 + 0.3427 * Y * s + 0.4888 * Y) *
      (∫ W in V..X, 1 / (W * Real.sqrt W)) ≤
        r * k / 2 * (κ * J) + 0.3427 * s * (Y * J) + 0.4888 * (Y * J) := by
    refine (mul_le_mul_of_nonneg_left i3 hc3').trans (le_of_eq ?_)
    rw [hJ]
    ring
  have bA : 4 * (r * k / 2 * (0.0503567 * t - 0.12646) + r * k / 2 * (κ * J)) ≤
      0.112431 * u ^ 5 * s ^ 3 := by
    have h1 : r * k / 2 * (κ * J) ≤ r * k / 2 * 0.06406 := mul_le_mul_of_nonneg_left hκJ hc1'
    have h2 : 4 * (r * k / 2 * (0.0503567 * t - 0.12646) + r * k / 2 * (κ * J)) ≤
        2 * (r * k) * (0.0503567 * t) := by linarith
    have h3 : 2 * (r * k) * (0.0503567 * t) = 0.11242841290202 * (u ^ 5 * s ^ 3) := by
      rw [hrdef, hkdef, ← hst]
      ring
    linarith
  have bB : 4 * (r / (2 * k) * (t ^ 2 / 6)) ≤ 0.112463 * u ^ 5 * s ^ 3 := by
    have h3 : 4 * (r / (2 * k) * (t ^ 2 / 6)) = 2.4548 / 21.828 * (u ^ 5 * s ^ 3) := by
      rw [hrdef, hkdef, ← hst]
      field_simp
      ring
    rw [h3]
    have : 2.4548 / 21.828 ≤ (0.112463 : ℝ) := by norm_num
    linarith [mul_le_mul_of_nonneg_right this hw3]
  have bC : 4 * (0.3427 * s * (Y * J) + 0.4888 * (Y * J)) ≤ (4.74876 * s + 6.77328) * u ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hYJ hs0.le
    linarith [mul_nonneg hs0.le hw.le, hw]
  have hfin := final_sum (u ^ 5) s
    (4 * (r * k / 2 * (0.0503567 * t - 0.12646) + r * k / 2 * (κ * J)))
    (4 * (r / (2 * k) * (t ^ 2 / 6))) (4 * (0.3427 * s * (Y * J) + 0.4888 * (Y * J))) hw hs7
    bA bB bC
  have e3 : 0.34 * u ^ 5 * (t * s) = 0.34 * u ^ 5 * s ^ 3 := by
    rw [← hst]
    ring
  rw [e3]
  linarith

/-- **`MPc.SecIIAt` from the deep links** (`SecInt` and `SecIICalcC` discharged): the Type II
link at the second choice needs only `Menson2C`, `Kraken`, `eq:kast` and RS62 Thm 13. -/
theorem secIIAtC_of_deep (hm : Menson2C) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) : SecIIAt :=
  secIIAtC_of secInt_holds hm hk hc hl h13 secIICalcC_holds

/-- **`T2S.SecIICalc` (printed `eq:velib`), PROVED**: `HOk → HOkC`. -/
theorem secIICalc_holds : SecIICalc := fun Y hY δ q hq hqQ hδ hc H s1f s2f s3f hH hpt =>
  secIICalcC_holds Y hY δ q hq hqQ hδ hc H s1f s2f s3f (hOkC_of_hOk H hH) hpt

end Principia.Common.TernaryGoldbach.T2SII
