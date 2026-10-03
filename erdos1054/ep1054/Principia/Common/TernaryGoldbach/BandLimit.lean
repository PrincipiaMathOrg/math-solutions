/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfWeights
import Principia.Common.SincIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

/-!
# `BandUniform` PROVED: `|h₂₀₀(t) − h(t)| ≤ 0.13` for every `t > 0`

This discharges `HW.BandUniform`, the only analytic content left in link 0 of the Helfgott chain,
so `HW.cite_band3` loses a hypothesis: `cite_two : PlattGRH → MajorLowerSmooth η₊ η_* →
MinorUpperSmooth η₊ η_* → Cite_Helfgott_weighted`, on Helfgott's own weights.

## The route (one integration by parts in `y`, split at `y = 1`)

Fix `t > 0`, `H = 200`, `a = min(t/2, 1/2)`, and write `u(y) = h(t/y)`, `S(y) = Si(H log y)`, so
the integrand of `h_H(t) = ∫_{(0,∞)} h(t/y) F_H(y) dy/y` is `u · S'/π` and vanishes on `(0, a]`.
Integrating by parts on `[a, 1]` against `(S + π/2)/π` and on `[1, A]` against `(S − π/2)/π`
(`vm`, `vp`; both have derivative `F_H(y)/y`, and they take the values `±1/2` at `y = 1`, where
the two pieces meet) gives, EXACTLY (`window_bound`),
`∫ₐᴬ − h(t) = u(A)vp(A) − ∫ₐ¹ u'·vm − ∫₁ᴬ u'·vp`,
and `|vm|, |vp| = |π/2 − Si(H|log y|)|/π`. Then three bounds, each UNIFORM in `t`:

* **kernel** (`tail_le_kk`): `|π/2 − Si w| ≤ k(w) = min(π/2, 1/w + 2/w²)` for `w ≥ 0`, from the
  ported Dirichlet integral and two integrations by parts (`SincIntegral.tail_le_sharp`);
* **derivative** (`abs_du_le`): `|u'(y)| ≤ σ/y`, `σ = 3e^{1/2}`, from `x|h'(x)| ≤ 3e^{1/2}`
  (`sigma_bound`; true sup `4.2475` against `σ = 4.9462`);
* **total variation** (`tv_le`): `∫ₐᴬ |u'| ≤ 2h(1) = 2e^{1/2}` (`u` rises on `[a,t]`, falls after).

Splitting `k ≤ κ + max(k − κ, 0)` with `κ = k(80)`: the `κ` part costs `κ·TV`, and the rest is
supported on `|log y| ≤ 2/5` and is computed in the variable `v = ±log y` (`subst_pos`,
`subst_neg`, `int_fk_le`): `∫₀^∞ max(k(200v) − κ, 0) dv ≤ C_n`. Result (`band_bound`):
`|h₂₀₀(t) − h(t)| ≤ B₀ = (κ/π)·2e^{1/2} + (σ/π)·2C_n = 0.11850 ≤ 0.13` (`B0_le`).

## Why this is NOT Helfgott's `eq:havana`

Helfgott bounds `|h_H − h|/t`, which is false as `t → 0` (see `HW.BandUniform`). His error is on
the `w < 0` half (here: `y < 1`), where the factor `t e^{|w|/H}` grows up to `2`. Here that half is
bounded by `|u'(y)| ≤ σ/y` — no factor `t` is extracted anywhere — and by the total variation of
`u`, which is `2e^{1/2}` for EVERY `t`. Nothing is divided by `t`.

## Numbers (checked before any Lean, at `t ∈ {1e-15, 1e-12, 1e-9, 1e-6, 1e-3}`, 43 points of
`[0.001, 2.1]`, and `t = 2.5, 5, 100`; every intermediate holds at every point)

* the IBP identity matches an independent Mellin-inversion evaluation of `h_H − h` to within
  `3·10⁻¹²` at every grid point;
* the true first-order remainder `(1/π)∫|u'||π/2 − Si(H|log y|)|` peaks at `0.04317` (`t ≈ 1.52`);
* `(1/π)(κ·∫|u'| + σ·∫ max(k(H|log y|) − κ, 0) dy/y)` is `0.11761` at every `t` (the variation
  integral is exactly `2e^{1/2}` for every `t`); the closed form is `B₀ = 0.11850`;
* `|h_H − h|` is largest near `t = 2` (`1.136·10⁻⁵` there on this grid), so `0.13` has slack
  `~10⁴` and `B₀` sits well inside it.
-/

namespace Principia.Common.TernaryGoldbach.BL

open MeasureTheory Set Filter Real
open scoped Topology
open Principia.Common.SincIntegral (Si hasDerivAt_Si Si_neg Si_zero tail_le_pi_div_two
  tail_le_sharp integral_inv_sq)

/-! ## `h` is `C¹` on `ℝ`: its derivative `hD` -/

/-- The polynomial-exponential piece `x²(2−x)³e^{x−1/2}` of `h`, on all of `ℝ`. -/
noncomputable def hP (x : ℝ) : ℝ := x ^ 2 * (2 - x) ^ 3 * Real.exp (x - 1 / 2)

/-- Its derivative `x(2−x)²(1−x)(4+x)e^{x−1/2}`. -/
noncomputable def hDP (x : ℝ) : ℝ :=
  x * (2 - x) ^ 2 * (1 - x) * (4 + x) * Real.exp (x - 1 / 2)

/-- **`h'`**: `hDP` on `[0, 2]`, `0` elsewhere (`hasDerivAt_hFun`). -/
noncomputable def hD (x : ℝ) : ℝ := if 0 ≤ x ∧ x ≤ 2 then hDP x else 0

/-- `hP' = hDP`. -/
theorem hasDerivAt_hP (x : ℝ) : HasDerivAt hP (hDP x) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  have hm : HasDerivAt (fun y : ℝ => 2 - y) (-1) x := hi.const_sub 2
  have he : HasDerivAt (fun y : ℝ => Real.exp (y - 1 / 2)) (Real.exp (x - 1 / 2) * 1) x :=
    (hi.sub_const (1 / 2)).exp
  have h := ((hi.mul hi).mul ((hm.mul hm).mul hm)).mul he
  have e : hP = fun y => y * y * ((2 - y) * (2 - y) * (2 - y)) * Real.exp (y - 1 / 2) := by
    funext y
    unfold hP
    ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold hDP
  ring

/-- On `[0, 2]`, `h = hP`. -/
theorem hFun_eq_hP {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : HW.hFun x = hP x := by
  change (if 0 ≤ x ∧ x ≤ 2 then hP x else 0) = hP x
  rw [if_pos ⟨h0, h2⟩]

/-- On `[0, 2]`, `hD = hDP`. -/
theorem hD_eq {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : hD x = hDP x := if_pos ⟨h0, h2⟩

/-- **`h` is differentiable on all of `ℝ` with derivative `hD`** (at `0` and `2` both one-sided
derivatives vanish). -/
theorem hasDerivAt_hFun (x : ℝ) : HasDerivAt HW.hFun (hD x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hd : hD x = 0 := if_neg fun h => absurd h.1 (not_le.mpr hx)
    rw [hd]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact HW.hFun_of_nonpos (le_of_lt hy)
  · have hd : hD 0 = 0 := by
      rw [hD_eq le_rfl (by norm_num)]
      simp [hDP]
    rw [hd]
    have hl : HasDerivWithinAt HW.hFun 0 (Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        (fun y hy => HW.hFun_of_nonpos hy) self_mem_Iic
    have hr : HasDerivWithinAt HW.hFun 0 (Ici 0) 0 := by
      have h := (hasDerivAt_hP 0).hasDerivWithinAt (s := Ici 0)
      have h0 : hDP 0 = 0 := by simp [hDP]
      rw [h0] at h
      refine h.congr_of_eventuallyEq ?_ (hFun_eq_hP le_rfl (by norm_num))
      filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ))
        (Iio_mem_nhds (show (0 : ℝ) < 2 by norm_num))] with y hy
      exact hFun_eq_hP hy.1 hy.2.le
    have h := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h
  · rcases lt_trichotomy x 2 with hx2 | rfl | hx2
    · rw [hD_eq hx.le hx2.le]
      refine (hasDerivAt_hP x).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx hx2] with y hy
      exact hFun_eq_hP hy.1.le hy.2.le
    · have hd : hD 2 = 0 := by
        rw [hD_eq (by norm_num) le_rfl]
        simp [hDP]
      rw [hd]
      have hl : HasDerivWithinAt HW.hFun 0 (Iic 2) 2 := by
        have h := (hasDerivAt_hP 2).hasDerivWithinAt (s := Iic 2)
        have h0 : hDP 2 = 0 := by simp [hDP]
        rw [h0] at h
        refine h.congr_of_eventuallyEq ?_ (hFun_eq_hP (by norm_num) le_rfl)
        filter_upwards [inter_mem_nhdsWithin (Iic (2 : ℝ))
          (Ioi_mem_nhds (show (0 : ℝ) < 2 by norm_num))] with y hy
        exact hFun_eq_hP (le_of_lt hy.2) hy.1
      have hr : HasDerivWithinAt HW.hFun 0 (Ici 2) 2 :=
        (hasDerivAt_const (2 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
          (fun y hy => HW.hFun_of_two_le hy) self_mem_Ici
      have h := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h
    · have hd : hD x = 0 := if_neg fun h => absurd h.2 (not_le.mpr hx2)
      rw [hd]
      refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx2] with y hy
      exact HW.hFun_of_two_le (le_of_lt hy)

/-- `hD = hDP ∘ clamp` (`hDP` vanishes at `0` and `2`). -/
theorem hD_clamp (x : ℝ) : hD x = hDP (max 0 (min x 2)) := by
  unfold hD
  split_ifs with h
  · rw [min_eq_left h.2, max_eq_right h.1]
  · rcases not_and_or.mp h with h' | h'
    · have hx : x < 0 := not_le.mp h'
      rw [min_eq_left (by linarith), max_eq_left hx.le]
      simp [hDP]
    · have hx : 2 < x := not_le.mp h'
      rw [min_eq_right hx.le, max_eq_right (by norm_num)]
      simp [hDP]

/-- `hD` is continuous. -/
theorem continuous_hD : Continuous hD := by
  have e : hD = fun x => hDP (max 0 (min x 2)) := funext hD_clamp
  have hc : Continuous hDP := by
    unfold hDP
    fun_prop
  rw [e]
  exact hc.comp (continuous_const.max (continuous_id.min continuous_const))

/-- `h` is continuous. -/
theorem continuous_hFun : Continuous HW.hFun :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_hFun x).continuousAt

/-- `h ≥ 0`. -/
theorem hFun_nonneg (x : ℝ) : 0 ≤ HW.hFun x := by
  unfold HW.hFun
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (sq_nonneg x) (pow_nonneg (by linarith [h.2]) 3))
      (Real.exp_pos _).le
  · exact le_rfl

/-- `h' ≥ 0` on `(−∞, 1]` (`h` rises to its maximum at `1`). -/
theorem hD_nonneg {x : ℝ} (h1 : x ≤ 1) : 0 ≤ hD x := by
  unfold hD
  split_ifs with h
  · unfold hDP
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h.1 (sq_nonneg _)) (by linarith))
      (by linarith)) (Real.exp_pos _).le
  · exact le_rfl

/-- `h' ≤ 0` on `[1, ∞)`. -/
theorem hD_nonpos {x : ℝ} (h1 : 1 ≤ x) : hD x ≤ 0 := by
  unfold hD
  split_ifs with h
  · have e : hDP x = -(x * (2 - x) ^ 2 * (x - 1) * (4 + x) * Real.exp (x - 1 / 2)) := by
      unfold hDP
      ring
    rw [e, neg_nonpos]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h.1 (sq_nonneg _)) (by linarith))
      (by linarith)) (Real.exp_pos _).le
  · exact le_rfl

/-! ## `σ = 3e^{1/2}` bounds `x|h'(x)|` (true sup `4.2475`) -/

/-- `eˢ ≤ 1 + s + s²/2 + (2/9)s³` on `[0, 1]` (Taylor with Mathlib's `Real.exp_bound`, `n = 3`). -/
theorem exp_le_cubic {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Real.exp s ≤ 1 + s + s ^ 2 / 2 + 2 / 9 * s ^ 3 := by
  have hb : |Real.exp s - (1 + s + s ^ 2 / 2)| ≤ |s| ^ 3 * (4 / 18) := by
    have h := Real.exp_bound (x := s) (by rw [abs_of_nonneg h0]; exact h1) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    convert h using 2
    ring
  rw [abs_of_nonneg h0] at hb
  linarith [(abs_le.mp hb).2]

/-- `(1−s²)²s(5−s) ≤ 3` on `[0, 1]` (Bernstein coefficients `≤ 1.8`). -/
theorem poly_left {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : (1 - s ^ 2) ^ 2 * s * (5 - s) ≤ 3 := by
  have hb : 0 ≤ 1 - s := by linarith
  linarith [mul_nonneg (pow_nonneg h0 0) (pow_nonneg hb 6),
    mul_nonneg (pow_nonneg h0 1) (pow_nonneg hb 5), mul_nonneg (pow_nonneg h0 2) (pow_nonneg hb 4),
    mul_nonneg (pow_nonneg h0 3) (pow_nonneg hb 3), mul_nonneg (pow_nonneg h0 4) (pow_nonneg hb 2),
    mul_nonneg (pow_nonneg h0 5) (pow_nonneg hb 1), mul_nonneg (pow_nonneg h0 6) (pow_nonneg hb 0)]

/-- `(1−s²)²s(5+s)(1+s+s²/2+2s³/9) ≤ 3` on `[0, 1/2]` (max `2.556`). -/
theorem poly_lo {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    (1 - s ^ 2) ^ 2 * s * (5 + s) * (1 + s + s ^ 2 / 2 + 2 / 9 * s ^ 3) ≤ 3 := by
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1), pow_nonneg h0 2, pow_nonneg h0 3,
    pow_nonneg h0 4, pow_nonneg h0 5, pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8,
    pow_nonneg h0 9]

/-- `(1−s²)²s(5+s)(1+s+s²/2+2s³/9) ≤ 3` on `[1/2, 1]` (Bernstein coefficients `≤ 2.631`). -/
theorem poly_hi {s : ℝ} (h0 : 1 / 2 ≤ s) (h1 : s ≤ 1) :
    (1 - s ^ 2) ^ 2 * s * (5 + s) * (1 + s + s ^ 2 / 2 + 2 / 9 * s ^ 3) ≤ 3 := by
  have ha : 0 ≤ s - 1 / 2 := by linarith
  have hb : 0 ≤ 1 - s := by linarith
  linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 9),
    mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 8), mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 7),
    mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 6), mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 5),
    mul_nonneg (pow_nonneg ha 5) (pow_nonneg hb 4), mul_nonneg (pow_nonneg ha 6) (pow_nonneg hb 3),
    mul_nonneg (pow_nonneg ha 7) (pow_nonneg hb 2), mul_nonneg (pow_nonneg ha 8) (pow_nonneg hb 1),
    mul_nonneg (pow_nonneg ha 9) (pow_nonneg hb 0)]

/-- **`x·|h'(x)| ≤ 3e^{1/2}` for every real `x`** (true sup `4.2475` at `x ≈ 1.539`). -/
theorem sigma_bound (x : ℝ) : x * |hD x| ≤ 3 * Real.exp (1 / 2) := by
  have hE : 0 < Real.exp (1 / 2) := Real.exp_pos _
  by_cases h : 0 ≤ x ∧ x ≤ 2
  · obtain ⟨h0, h2⟩ := h
    have hsplit : Real.exp (x - 1 / 2) = Real.exp (x - 1) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hD_eq h0 h2]
    rcases le_total x 1 with h1 | h1
    · have hn : 0 ≤ hDP x := by
        have := hD_nonneg h1
        rwa [hD_eq h0 h2] at this
      have e : x * |hDP x| = (1 - (1 - x) ^ 2) ^ 2 * (1 - x) * (5 - (1 - x)) *
          Real.exp (x - 1) * Real.exp (1 / 2) := by
        rw [abs_of_nonneg hn]
        unfold hDP
        rw [hsplit]
        ring
      have hA0 : 0 ≤ (1 - (1 - x) ^ 2) ^ 2 * (1 - x) * (5 - (1 - x)) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
      have hA := poly_left (s := 1 - x) (by linarith) (by linarith)
      have hex : Real.exp (x - 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      rw [e]
      calc (1 - (1 - x) ^ 2) ^ 2 * (1 - x) * (5 - (1 - x)) * Real.exp (x - 1) * Real.exp (1 / 2)
          ≤ 3 * 1 * Real.exp (1 / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hA hex (Real.exp_pos _).le (by norm_num))
              hE.le
        _ = 3 * Real.exp (1 / 2) := by ring
    · have hn : hDP x ≤ 0 := by
        have := hD_nonpos h1
        rwa [hD_eq h0 h2] at this
      have e : x * |hDP x| = (1 - (x - 1) ^ 2) ^ 2 * (x - 1) * (5 + (x - 1)) *
          Real.exp (x - 1) * Real.exp (1 / 2) := by
        rw [abs_of_nonpos hn]
        unfold hDP
        rw [hsplit]
        ring
      have hA0 : 0 ≤ (1 - (x - 1) ^ 2) ^ 2 * (x - 1) * (5 + (x - 1)) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
      have hex := exp_le_cubic (s := x - 1) (by linarith) (by linarith)
      have hA : (1 - (x - 1) ^ 2) ^ 2 * (x - 1) * (5 + (x - 1)) *
          (1 + (x - 1) + (x - 1) ^ 2 / 2 + 2 / 9 * (x - 1) ^ 3) ≤ 3 := by
        rcases le_total (x - 1) (1 / 2) with h3 | h3
        · exact poly_lo (by linarith) h3
        · exact poly_hi h3 (by linarith)
      rw [e]
      calc (1 - (x - 1) ^ 2) ^ 2 * (x - 1) * (5 + (x - 1)) * Real.exp (x - 1) *
            Real.exp (1 / 2)
          ≤ (1 - (x - 1) ^ 2) ^ 2 * (x - 1) * (5 + (x - 1)) *
            (1 + (x - 1) + (x - 1) ^ 2 / 2 + 2 / 9 * (x - 1) ^ 3) * Real.exp (1 / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex hA0) hE.le
        _ ≤ 3 * Real.exp (1 / 2) := mul_le_mul_of_nonneg_right hA hE.le
  · have hd : hD x = 0 := if_neg h
    rw [hd, abs_zero, mul_zero]
    positivity

/-! ## The kernel `k(w) = min(π/2, 1/w + 2/w²)` and its near part `max(k(200v) − κ, 0)` -/

/-- `κ = 1/80 + 2/80²`, the value of `1/w + 2/w²` at `w = 80 = 200·(2/5)`. -/
noncomputable def kap : ℝ := 1 / 80 + 2 / 80 ^ 2

/-- **The kernel majorant** `k(w) = min(π/2, 1/m + 2/m²)`, `m = max(w, 1/2)` (continuous). -/
noncomputable def kk (u : ℝ) : ℝ := min (π / 2) (1 / max u (1 / 2) + 2 / max u (1 / 2) ^ 2)

/-- **The near part** `f(v) = max(k(200v) − κ, 0)`; it vanishes for `v ≥ 2/5` (`fk_eq_zero`). -/
noncomputable def fk (v : ℝ) : ℝ := max (kk (200 * v) - kap) 0

/-- `k` is continuous. -/
theorem continuous_kk : Continuous kk := by
  have hm : Continuous fun u : ℝ => max u (1 / 2) := continuous_id.max continuous_const
  have hne : ∀ u : ℝ, max u (1 / 2) ≠ 0 := fun u =>
    (lt_of_lt_of_le (by norm_num) (le_max_right u (1 / 2))).ne'
  unfold kk
  exact continuous_const.min ((continuous_const.div hm hne).add
    (continuous_const.div (hm.pow 2) fun u => pow_ne_zero 2 (hne u)))

/-- `f` is continuous. -/
theorem continuous_fk : Continuous fk :=
  ((continuous_kk.comp (continuous_const.mul continuous_id)).sub continuous_const).max
    continuous_const

/-- **The kernel bound**: `|π/2 − Si w| ≤ k(w)` for `w ≥ 0`. -/
theorem tail_le_kk {u : ℝ} (hu : 0 ≤ u) : |π / 2 - Si u| ≤ kk u := by
  have hpi := tail_le_pi_div_two hu
  unfold kk
  refine le_min hpi ?_
  rcases le_total u (1 / 2) with h | h
  · rw [max_eq_right h]
    have e : (1 : ℝ) / (1 / 2) + 2 / (1 / 2) ^ 2 = 10 := by norm_num
    rw [e]
    linarith [Real.pi_le_four]
  · rw [max_eq_left h]
    have hu0 : 0 < u := by linarith
    have e : 1 / u + 2 / u ^ 2 = u⁻¹ + 2 * (u ^ 2)⁻¹ := by ring
    rw [e]
    exact tail_le_sharp hu0

/-- `f ≥ 0`. -/
theorem fk_nonneg (v : ℝ) : 0 ≤ fk v := le_max_right _ _

/-- `f ≤ π/2 − κ`. -/
theorem fk_le_const (v : ℝ) : fk v ≤ π / 2 - kap := by
  have h1 : kk (200 * v) ≤ π / 2 := min_le_left _ _
  have h2 : kap ≤ π / 2 := by
    unfold kap
    linarith [Real.pi_gt_three]
  exact max_le (by linarith) (by linarith)

/-- On `[1/160, 2/5]`: `f(v) ≤ (1/200)v⁻¹ + (1/20000)(v²)⁻¹ − κ`. -/
theorem fk_le_tail {v : ℝ} (h1 : 1 / 160 ≤ v) (h2 : v ≤ 2 / 5) :
    fk v ≤ 1 / 200 * v⁻¹ + 1 / 20000 * (v ^ 2)⁻¹ - kap := by
  have hv : 0 < v := by linarith
  have hm : 1 / 2 ≤ 200 * v := by linarith
  have hk : kk (200 * v) ≤ 1 / (200 * v) + 2 / (200 * v) ^ 2 := by
    unfold kk
    rw [max_eq_left hm]
    exact min_le_right _ _
  have e : 1 / (200 * v) + 2 / (200 * v) ^ 2 = 1 / 200 * v⁻¹ + 1 / 20000 * (v ^ 2)⁻¹ := by
    ring
  have hge : kap ≤ 1 / (200 * v) + 2 / (200 * v) ^ 2 := by
    have a1 : 1 / 80 ≤ 1 / (200 * v) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have a2 : 2 / 80 ^ 2 ≤ 2 / (200 * v) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 2)
    unfold kap
    linarith
  rw [← e]
  exact max_le (by linarith) (by linarith)

/-- `f(v) = 0` for `v ≥ 2/5`. -/
theorem fk_eq_zero {v : ℝ} (h : 2 / 5 ≤ v) : fk v = 0 := by
  have hm : 1 / 2 ≤ 200 * v := by linarith
  have hk : kk (200 * v) ≤ 1 / (200 * v) + 2 / (200 * v) ^ 2 := by
    unfold kk
    rw [max_eq_left hm]
    exact min_le_right _ _
  have hle : 1 / (200 * v) + 2 / (200 * v) ^ 2 ≤ kap := by
    have a1 : 1 / (200 * v) ≤ 1 / 80 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have a2 : 2 / (200 * v) ^ 2 ≤ 2 / 80 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) (by linarith) 2)
    unfold kap
    linarith
  exact max_eq_right (by linarith)

/-- `C_n = π/320 + (log 64)/200 + 63/8000 − (2/5)κ`, the bound on `∫₀^∞ f` (`0.0333619`). -/
noncomputable def Cn : ℝ := π / 320 + Real.log 64 / 200 + 63 / 8000 - 2 / 5 * kap

/-- **`∫₀^V f ≤ C_n` for every `V ≥ 0`**: `f ≤ π/2 − κ` on `[0, 1/160]`, the explicit `1/v`, `1/v²`
bound on `[1/160, 2/5]`, and `f = 0` beyond. -/
theorem int_fk_le {V : ℝ} (hV : 0 ≤ V) : ∫ v in (0 : ℝ)..V, fk v ≤ Cn := by
  have hfi : ∀ p q : ℝ, IntervalIntegrable fk volume p q := fun p q =>
    continuous_fk.intervalIntegrable p q
  have hW1 : (2 / 5 : ℝ) ≤ max V (2 / 5) := le_max_right _ _
  have h1 : ∫ v in (0 : ℝ)..V, fk v ≤ ∫ v in (0 : ℝ)..max V (2 / 5), fk v :=
    intervalIntegral.integral_mono_interval le_rfl hV (le_max_left _ _)
      (Eventually.of_forall fun v => fk_nonneg v) (hfi _ _)
  have hsplit : ∫ v in (0 : ℝ)..max V (2 / 5), fk v = (∫ v in (0 : ℝ)..(1 / 160), fk v)
      + (∫ v in (1 / 160 : ℝ)..(2 / 5), fk v) + ∫ v in (2 / 5 : ℝ)..max V (2 / 5), fk v := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
  have h3 : ∫ v in (2 / 5 : ℝ)..max V (2 / 5), fk v = 0 := by
    have hz : EqOn fk (fun _ => (0 : ℝ)) (uIcc (2 / 5) (max V (2 / 5))) := by
      intro v hv
      rw [uIcc_of_le hW1] at hv
      exact fk_eq_zero hv.1
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
  have h2a : ∫ v in (0 : ℝ)..(1 / 160), fk v ≤ (1 / 160 - 0) * (π / 2 - kap) := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 160) (hfi _ _)
      ((continuous_const : Continuous fun _ : ℝ => π / 2 - kap).intervalIntegrable
        (μ := volume) _ _) fun v _ => fk_le_const v
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  have hpos : ∀ v ∈ uIcc (1 / 160 : ℝ) (2 / 5), v ≠ 0 := fun v hv =>
    (HW.uIcc_pos (by norm_num) (by norm_num) hv).ne'
  have hc1 : IntervalIntegrable (fun v : ℝ => v⁻¹) volume (1 / 160) (2 / 5) :=
    (continuousOn_inv₀.mono fun v hv => hpos v hv).intervalIntegrable
  have hc2 : IntervalIntegrable (fun v : ℝ => (v ^ 2)⁻¹) volume (1 / 160) (2 / 5) :=
    ((continuousOn_pow 2).inv₀ fun v hv => pow_ne_zero 2 (hpos v hv)).intervalIntegrable
  have hc3 : IntervalIntegrable (fun _ : ℝ => kap) volume (1 / 160) (2 / 5) :=
    (continuous_const : Continuous fun _ : ℝ => kap).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun v : ℝ => 1 / 200 * v⁻¹ + 1 / 20000 * (v ^ 2)⁻¹ - kap)
      volume (1 / 160) (2 / 5) :=
    ((hc1.const_mul (1 / 200)).add (hc2.const_mul (1 / 20000))).sub hc3
  have h2b : ∫ v in (1 / 160 : ℝ)..(2 / 5), fk v ≤
      1 / 200 * Real.log 64 + 1 / 20000 * (160 - 5 / 2) - (2 / 5 - 1 / 160) * kap := by
    refine (intervalIntegral.integral_mono_on (by norm_num) (hfi _ _) hg
      fun v hv => fk_le_tail hv.1 hv.2).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_sub ((hc1.const_mul _).add (hc2.const_mul _)) hc3,
      intervalIntegral.integral_add (hc1.const_mul _) (hc2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by norm_num) (by norm_num), integral_inv_sq (by norm_num) (by norm_num),
      intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  calc ∫ v in (0 : ℝ)..V, fk v ≤ ∫ v in (0 : ℝ)..max V (2 / 5), fk v := h1
    _ ≤ (1 / 160 - 0) * (π / 2 - kap)
        + (1 / 200 * Real.log 64 + 1 / 20000 * (160 - 5 / 2) - (2 / 5 - 1 / 160) * kap) + 0 := by
      rw [hsplit, h3]
      linarith
    _ = Cn := by
      unfold Cn
      ring

/-- **Substitution `v = log y`** on `[1, A]`: `∫₁ᴬ f(log y) dy/y = ∫₀^{log A} f`. -/
theorem subst_pos {A : ℝ} (hA : 1 ≤ A) :
    ∫ y in (1 : ℝ)..A, fk (Real.log y) * y⁻¹ = ∫ v in (0 : ℝ)..Real.log A, fk v := by
  have hpos : ∀ y ∈ uIcc 1 A, 0 < y := fun y hy => HW.uIcc_pos one_pos (by linarith) hy
  have h := intervalIntegral.integral_comp_mul_deriv (a := 1) (b := A) (f := Real.log)
    (f' := fun y => y⁻¹) (g := fk) (fun y hy => Real.hasDerivAt_log (hpos y hy).ne')
    (continuousOn_inv₀.mono fun y hy => (hpos y hy).ne') continuous_fk
  rw [Real.log_one] at h
  exact h

/-- **Substitution `v = −log y`** on `[a, 1]`: `∫ₐ¹ f(−log y) dy/y = ∫₀^{−log a} f`. -/
theorem subst_neg {a : ℝ} (ha : 0 < a) :
    ∫ y in a..1, fk (-Real.log y) * y⁻¹ = ∫ v in (0 : ℝ)..-Real.log a, fk v := by
  have hpos : ∀ y ∈ uIcc a 1, 0 < y := fun y hy => HW.uIcc_pos ha one_pos hy
  have h := intervalIntegral.integral_comp_mul_deriv (a := a) (b := 1)
    (f := fun y => -Real.log y) (f' := fun y => -y⁻¹) (g := fk)
    (fun y hy => (Real.hasDerivAt_log (hpos y hy).ne').neg)
    ((continuousOn_inv₀.mono fun y hy => (hpos y hy).ne').neg) continuous_fk
  have e : ∫ y in a..1, fk (-Real.log y) * y⁻¹ =
      -∫ y in a..1, (fk ∘ fun y => -Real.log y) y * -y⁻¹ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => ?_
    change fk (-Real.log y) * y⁻¹ = -(fk (-Real.log y) * -y⁻¹)
    ring
  rw [e, h, Real.log_one, neg_zero, intervalIntegral.integral_symm (-Real.log a) 0]

/-! ## `u(y) = h(t/y)`: derivative, the bound `|u'| ≤ σ/y`, and total variation `2e^{1/2}` -/

/-- `u'(y) = h'(t/y)·(−t/y²)` for `u(y) = h(t/y)`. -/
noncomputable def du (t y : ℝ) : ℝ := hD (t / y) * (-t / y ^ 2)

/-- `u' = du` on `(0, ∞)`. -/
theorem hasDerivAt_u (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => HW.hFun (t / y)) (du t y) y := by
  have h1 : HasDerivAt (fun y : ℝ => t / y) (-t / y ^ 2) y := by
    have h := (hasDerivAt_const y t).div (hasDerivAt_id' y) hy.ne'
    exact h.congr_deriv (by ring)
  exact (hasDerivAt_hFun (t / y)).comp y h1

/-- `du t` is continuous on `(0, ∞)`. -/
theorem continuousOn_du (t : ℝ) : ContinuousOn (du t) (Ioi 0) := by
  have hne : ∀ y ∈ Ioi (0 : ℝ), y ≠ 0 := fun y hy => (mem_Ioi.mp hy).ne'
  exact (continuous_hD.comp_continuousOn (continuousOn_const.div continuousOn_id hne)).mul
    (continuousOn_const.div (continuousOn_pow 2) fun y hy => pow_ne_zero 2 (hne y hy))

/-- **`|u'(y)| ≤ σ/y`**, `σ = 3e^{1/2}`: `|u'(y)| = (t/y)|h'(t/y)|/y` and `sigma_bound`. -/
theorem abs_du_le {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    |du t y| ≤ 3 * Real.exp (1 / 2) * y⁻¹ := by
  have hs := sigma_bound (t / y)
  have e : |du t y| = t / y * |hD (t / y)| * y⁻¹ := by
    unfold du
    rw [abs_mul, neg_div, abs_neg, abs_div, abs_of_pos ht, abs_of_pos (pow_pos hy 2)]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hy.le)

/-- `u' ≥ 0` on `(0, t]`. -/
theorem du_nonneg {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (hyt : y ≤ t) : 0 ≤ du t y := by
  have hd := hD_nonpos ((one_le_div hy).mpr hyt)
  have e : du t y = -hD (t / y) * (t / y ^ 2) := by
    unfold du
    ring
  rw [e]
  exact mul_nonneg (neg_nonneg.mpr hd) (div_nonneg ht.le (sq_nonneg y))

/-- `u' ≤ 0` on `[t, ∞)`. -/
theorem du_nonpos {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (hty : t ≤ y) : du t y ≤ 0 := by
  have hd := hD_nonneg ((div_le_one hy).mpr hty)
  have e : du t y = -(hD (t / y) * (t / y ^ 2)) := by
    unfold du
    ring
  rw [e, neg_nonpos]
  exact mul_nonneg hd (div_nonneg ht.le (sq_nonneg y))

/-- **Total variation**: `∫ₐᴬ |u'| ≤ 2h(1) = 2e^{1/2}` whenever `0 < a ≤ t/2` and `t ≤ A`. -/
theorem tv_le {t a A : ℝ} (ht : 0 < t) (ha : 0 < a) (hat : a ≤ t / 2) (htA : t ≤ A) :
    ∫ y in a..A, |du t y| ≤ 2 * Real.exp (1 / 2) := by
  have hat' : a ≤ t := by linarith
  have hA0 : 0 < A := ht.trans_le htA
  have hint : ∀ {p q : ℝ}, 0 < p → 0 < q → IntervalIntegrable (du t) volume p q :=
    fun hp hq => ((continuousOn_du t).mono (HW.uIcc_pos hp hq)).intervalIntegrable
  have hintabs : ∀ {p q : ℝ}, 0 < p → 0 < q →
      IntervalIntegrable (fun y => |du t y|) volume p q :=
    fun hp hq => ((continuousOn_du t).mono (HW.uIcc_pos hp hq)).abs.intervalIntegrable
  have hder : ∀ {p q : ℝ}, 0 < p → 0 < q → ∀ y ∈ uIcc p q,
      HasDerivAt (fun y => HW.hFun (t / y)) (du t y) y :=
    fun hp hq y hy => hasDerivAt_u t (HW.uIcc_pos hp hq hy)
  have h1 : ∫ y in a..t, |du t y| = HW.hFun (t / t) - HW.hFun (t / a) := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (hder ha ht) (hint ha ht)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hat'] at hy
    exact abs_of_nonneg (du_nonneg ht (ha.trans_le hy.1) hy.2)
  have h2 : ∫ y in t..A, |du t y| = HW.hFun (t / t) - HW.hFun (t / A) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (hder ht hA0) (hint ht hA0)
    rw [show HW.hFun (t / t) - HW.hFun (t / A) = -(HW.hFun (t / A) - HW.hFun (t / t)) by ring,
      ← h, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le htA] at hy
    exact abs_of_nonpos (du_nonpos ht (ht.trans_le hy.1) hy.1)
  have hta : HW.hFun (t / a) = 0 := HW.hFun_of_two_le (by rw [le_div_iff₀ ha]; linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hintabs ha ht) (hintabs ht hA0), h1, h2,
    div_self ht.ne', HW.hFun_one, hta]
  linarith [hFun_nonneg (t / A)]

/-! ## The two antiderivatives of `F_H(y)/y`, and their sizes -/

/-- `(Si(200 log y) + π/2)/π`: the antiderivative of `F_H(y)/y` used on `(0, 1]`. -/
noncomputable def vm (y : ℝ) : ℝ := (Si (200 * Real.log y) + π / 2) / π

/-- `(Si(200 log y) − π/2)/π`: the antiderivative of `F_H(y)/y` used on `[1, ∞)`. -/
noncomputable def vp (y : ℝ) : ℝ := (Si (200 * Real.log y) - π / 2) / π

/-- `vm' = F_H(y)/y`. -/
theorem hasDerivAt_vm {y : ℝ} (hy : 0 < y) : HasDerivAt vm (HW.FH 200 y / y) y := by
  have h1 : HasDerivAt (fun y => 200 * Real.log y) (200 * y⁻¹) y :=
    (Real.hasDerivAt_log hy.ne').const_mul 200
  have h2 : HasDerivAt vm (Real.sinc (200 * Real.log y) * (200 * y⁻¹) / π) y :=
    (((hasDerivAt_Si (200 * Real.log y)).comp y h1).add_const (π / 2)).div_const π
  refine h2.congr_deriv ?_
  unfold HW.FH
  ring

/-- `vp' = F_H(y)/y`. -/
theorem hasDerivAt_vp {y : ℝ} (hy : 0 < y) : HasDerivAt vp (HW.FH 200 y / y) y := by
  have h1 : HasDerivAt (fun y => 200 * Real.log y) (200 * y⁻¹) y :=
    (Real.hasDerivAt_log hy.ne').const_mul 200
  have h2 : HasDerivAt vp (Real.sinc (200 * Real.log y) * (200 * y⁻¹) / π) y :=
    (((hasDerivAt_Si (200 * Real.log y)).comp y h1).sub_const (π / 2)).div_const π
  refine h2.congr_deriv ?_
  unfold HW.FH
  ring

/-- `vm(1) = 1/2`. -/
theorem vm_one : vm 1 = 1 / 2 := by
  unfold vm
  rw [Real.log_one, mul_zero, Si_zero, zero_add, div_div, div_eq_iff (by positivity)]
  ring

/-- `vp(1) = −1/2`. -/
theorem vp_one : vp 1 = -(1 / 2) := by
  unfold vp
  rw [Real.log_one, mul_zero, Si_zero, zero_sub, neg_div, div_div, neg_inj,
    div_eq_iff (by positivity)]
  ring

/-- **On `(0, 1]`: `|vm y| ≤ (κ + f(−log y))/π`** (`Si` is odd, then `tail_le_kk`). -/
theorem abs_vm_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    |vm y| ≤ (kap + fk (-Real.log y)) / π := by
  have hl : Real.log y ≤ 0 := Real.log_nonpos hy.le hy1
  have hw : 0 ≤ 200 * -Real.log y := by linarith
  have e : vm y = (π / 2 - Si (200 * -Real.log y)) / π := by
    unfold vm
    rw [mul_neg, Si_neg]
    ring
  rw [e, abs_div, abs_of_pos Real.pi_pos]
  refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
  have h1 := tail_le_kk hw
  have h2 : kk (200 * -Real.log y) - kap ≤ fk (-Real.log y) := le_max_left _ _
  linarith

/-- **On `[1, ∞)`: `|vp y| ≤ (κ + f(log y))/π`**. -/
theorem abs_vp_le {y : ℝ} (hy1 : 1 ≤ y) : |vp y| ≤ (kap + fk (Real.log y)) / π := by
  have hw : 0 ≤ 200 * Real.log y := by linarith [Real.log_nonneg hy1]
  have e : vp y = -((π / 2 - Si (200 * Real.log y)) / π) := by
    unfold vp
    ring
  rw [e, abs_neg, abs_div, abs_of_pos Real.pi_pos]
  refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
  have h1 := tail_le_kk hw
  have h2 : kk (200 * Real.log y) - kap ≤ fk (Real.log y) := le_max_left _ _
  linarith

/-- `|vp y| ≤ 1` on `[1, ∞)`. -/
theorem abs_vp_le_one {y : ℝ} (hy1 : 1 ≤ y) : |vp y| ≤ 1 := by
  have hw : 0 ≤ 200 * Real.log y := by linarith [Real.log_nonneg hy1]
  have h := tail_le_pi_div_two hw
  have e : vp y = -((π / 2 - Si (200 * Real.log y)) / π) := by
    unfold vp
    ring
  rw [e, abs_neg, abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
  linarith [Real.pi_pos]

/-! ## The bound on a window `[a, A]`, then the limit `A → ∞` -/

/-- **The constant**: `B₀ = (κ/π)·2e^{1/2} + (3e^{1/2}/π)·2C_n` (`= 0.118499`). -/
noncomputable def B0 : ℝ :=
  kap / π * (2 * Real.exp (1 / 2)) + 3 * Real.exp (1 / 2) / π * (2 * Cn)

/-- **The window bound**: for `0 < a ≤ min(1, t/2)` and `max(1, t) ≤ A`,
`|∫ₐᴬ h(t/y)F_H(y)dy/y − h(t)| ≤ |h(t/A)| + B₀`. The integration by parts is EXACT; the only
inequalities are the three uniform bounds (kernel, `|u'| ≤ σ/y`, total variation). -/
theorem window_bound {t a A : ℝ} (ht : 0 < t) (ha : 0 < a) (ha1 : a ≤ 1) (hat : a ≤ t / 2)
    (hA : 1 ≤ A) (htA : t ≤ A) :
    |(∫ y in a..A, HW.hFun (t / y) * HW.FH 200 y / y) - HW.hFun t| ≤
      |HW.hFun (t / A)| + B0 := by
  have hA0 : 0 < A := by linarith
  have hne : ∀ y ∈ Ioi (0 : ℝ), y ≠ 0 := fun y hy => (mem_Ioi.mp hy).ne'
  have hpos1 : ∀ y ∈ uIcc a 1, 0 < y := fun y hy => HW.uIcc_pos ha one_pos hy
  have hpos2 : ∀ y ∈ uIcc 1 A, 0 < y := fun y hy => HW.uIcc_pos one_pos hA0 hy
  -- continuity on `(0, ∞)` of everything that is integrated
  have cF : ContinuousOn (fun y => HW.hFun (t / y) * HW.FH 200 y / y) (Ioi 0) :=
    ((continuous_hFun.comp_continuousOn (continuousOn_const.div continuousOn_id hne)).mul
      (HW.FH_contOn 200)).div continuousOn_id hne
  have cW : ContinuousOn (fun y => HW.FH 200 y / y) (Ioi 0) :=
    (HW.FH_contOn 200).div continuousOn_id hne
  have cN : ContinuousOn (fun y => fk (-Real.log y) * y⁻¹) (Ioi 0) :=
    (continuous_fk.comp_continuousOn (Real.continuousOn_log.mono fun _ hy =>
      (mem_Ioi.mp hy).ne').neg).mul (continuousOn_inv₀.mono fun _ hy => (mem_Ioi.mp hy).ne')
  have cP : ContinuousOn (fun y => fk (Real.log y) * y⁻¹) (Ioi 0) :=
    (continuous_fk.comp_continuousOn (Real.continuousOn_log.mono fun _ hy =>
      (mem_Ioi.mp hy).ne')).mul (continuousOn_inv₀.mono fun _ hy => (mem_Ioi.mp hy).ne')
  have iv : ∀ {g : ℝ → ℝ}, ContinuousOn g (Ioi 0) → ∀ {p q : ℝ}, 0 < p → 0 < q →
      IntervalIntegrable g volume p q :=
    fun hg _ _ hp hq => (hg.mono (HW.uIcc_pos hp hq)).intervalIntegrable
  -- the two integrations by parts
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => hasDerivAt_u t (hpos1 y hy)) (fun y hy => hasDerivAt_vm (hpos1 y hy))
    (iv (continuousOn_du t) ha one_pos) (iv cW ha one_pos)
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => hasDerivAt_u t (hpos2 y hy)) (fun y hy => hasDerivAt_vp (hpos2 y hy))
    (iv (continuousOn_du t) one_pos hA0) (iv cW one_pos hA0)
  have eF : ∀ p q : ℝ, ∫ y in p..q, HW.hFun (t / y) * HW.FH 200 y / y =
      ∫ y in p..q, HW.hFun (t / y) * (HW.FH 200 y / y) := fun p q =>
    intervalIntegral.integral_congr fun y _ => mul_div_assoc _ _ _
  have hta : HW.hFun (t / a) = 0 := HW.hFun_of_two_le (by rw [le_div_iff₀ ha]; linarith)
  rw [div_one] at ibp1 ibp2
  have hid : (∫ y in a..A, HW.hFun (t / y) * HW.FH 200 y / y) - HW.hFun t =
      HW.hFun (t / A) * vp A - (∫ y in a..1, du t y * vm y) - ∫ y in (1 : ℝ)..A, du t y * vp y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (iv cF ha one_pos) (iv cF one_pos hA0),
      eF, eF, ibp1, ibp2, hta, vm_one, vp_one]
    ring
  -- the pointwise majorants
  have hb1 : ‖∫ y in a..1, du t y * vm y‖ ≤ ∫ y in a..1,
      (kap / π * |du t y| + 3 * Real.exp (1 / 2) / π * (fk (-Real.log y) * y⁻¹)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le ha1
      (Eventually.of_forall fun y hy => ?_)
      (((iv (continuousOn_du t).abs ha one_pos).const_mul _).add ((iv cN ha one_pos).const_mul _))
    have hy0 : 0 < y := ha.trans hy.1
    have h1 := abs_vm_le hy0 hy.2
    have h2 := abs_du_le ht hy0
    have h3 := fk_nonneg (-Real.log y)
    rw [Real.norm_eq_abs, abs_mul]
    calc |du t y| * |vm y| ≤ |du t y| * ((kap + fk (-Real.log y)) / π) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = kap / π * |du t y| + |du t y| * fk (-Real.log y) / π := by ring
      _ ≤ kap / π * |du t y| + 3 * Real.exp (1 / 2) * y⁻¹ * fk (-Real.log y) / π :=
          add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h3)
            Real.pi_pos.le)
      _ = kap / π * |du t y| + 3 * Real.exp (1 / 2) / π * (fk (-Real.log y) * y⁻¹) := by ring
  have hb2 : ‖∫ y in (1 : ℝ)..A, du t y * vp y‖ ≤ ∫ y in (1 : ℝ)..A,
      (kap / π * |du t y| + 3 * Real.exp (1 / 2) / π * (fk (Real.log y) * y⁻¹)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hA
      (Eventually.of_forall fun y hy => ?_)
      (((iv (continuousOn_du t).abs one_pos hA0).const_mul _).add
        ((iv cP one_pos hA0).const_mul _))
    have hy0 : 0 < y := one_pos.trans hy.1
    have h1 := abs_vp_le hy.1.le
    have h2 := abs_du_le ht hy0
    have h3 := fk_nonneg (Real.log y)
    rw [Real.norm_eq_abs, abs_mul]
    calc |du t y| * |vp y| ≤ |du t y| * ((kap + fk (Real.log y)) / π) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = kap / π * |du t y| + |du t y| * fk (Real.log y) / π := by ring
      _ ≤ kap / π * |du t y| + 3 * Real.exp (1 / 2) * y⁻¹ * fk (Real.log y) / π :=
          add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h3)
            Real.pi_pos.le)
      _ = kap / π * |du t y| + 3 * Real.exp (1 / 2) / π * (fk (Real.log y) * y⁻¹) := by ring
  -- integrate the majorants
  rw [intervalIntegral.integral_add ((iv (continuousOn_du t).abs ha one_pos).const_mul _)
      ((iv cN ha one_pos).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, subst_neg ha, Real.norm_eq_abs] at hb1
  rw [intervalIntegral.integral_add ((iv (continuousOn_du t).abs one_pos hA0).const_mul _)
      ((iv cP one_pos hA0).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, subst_pos hA, Real.norm_eq_abs] at hb2
  have hkp : 0 ≤ kap / π := div_nonneg (by unfold kap; norm_num) Real.pi_pos.le
  have hsp : 0 ≤ 3 * Real.exp (1 / 2) / π := by positivity
  have hT : kap / π * (∫ y in a..1, |du t y|) + kap / π * (∫ y in (1 : ℝ)..A, |du t y|) ≤
      kap / π * (2 * Real.exp (1 / 2)) := by
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
      (iv (continuousOn_du t).abs ha one_pos) (iv (continuousOn_du t).abs one_pos hA0)]
    exact mul_le_mul_of_nonneg_left (tv_le ht ha hat htA) hkp
  have hC1 := int_fk_le (V := -Real.log a) (by linarith [Real.log_nonpos ha.le ha1])
  have hC2 := int_fk_le (V := Real.log A) (Real.log_nonneg hA)
  have hS : 3 * Real.exp (1 / 2) / π * (∫ v in (0 : ℝ)..-Real.log a, fk v) +
      3 * Real.exp (1 / 2) / π * (∫ v in (0 : ℝ)..Real.log A, fk v) ≤
      3 * Real.exp (1 / 2) / π * (2 * Cn) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) hsp
  have hX : |HW.hFun (t / A) * vp A| ≤ |HW.hFun (t / A)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_vp_le_one hA)
  rw [hid, B0]
  have k1 := abs_le.mp hX
  have k2 := abs_le.mp hb1
  have k3 := abs_le.mp hb2
  rw [abs_le]
  constructor
  · linarith [abs_nonneg (HW.hFun (t / A) * vp A), abs_nonneg (∫ y in a..1, du t y * vm y),
      abs_nonneg (∫ y in (1 : ℝ)..A, du t y * vp y), neg_abs_le (HW.hFun (t / A) * vp A),
      neg_abs_le (∫ y in a..1, du t y * vm y), neg_abs_le (∫ y in (1 : ℝ)..A, du t y * vp y)]
  · linarith [le_abs_self (HW.hFun (t / A) * vp A), le_abs_self (∫ y in a..1, du t y * vm y),
      le_abs_self (∫ y in (1 : ℝ)..A, du t y * vp y)]

/-- **The uniform band-limiting bound, with the explicit constant**: for every `t > 0`,
`|h₂₀₀(t) − h(t)| ≤ B₀`. The window `[a, A]`, `a = min(t/2, 1/2)`, exhausts `h_H`'s integral
(which vanishes on `(0, t/2]`), and the boundary term `|h(t/A)| → h(0) = 0`. -/
theorem band_bound {t : ℝ} (ht : 0 < t) : |HW.hH 200 t - HW.hFun t| ≤ B0 := by
  have ha : 0 < min (t / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have ha1 : min (t / 2) (1 / 2) ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hat : min (t / 2) (1 / 2) ≤ t / 2 := min_le_left _ _
  have hint : IntegrableOn (fun y => HW.hFun (t / y) * HW.FH 200 y / y)
      (Ioi (min (t / 2) (1 / 2))) :=
    (HW.hH_integrable (by norm_num) ht).mono_set (Ioi_subset_Ioi ha.le)
  have hH_eq : HW.hH 200 t =
      ∫ y in Ioi (min (t / 2) (1 / 2)), HW.hFun (t / y) * HW.FH 200 y / y := by
    unfold HW.hH HW.mconv
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi ha.le) fun y hy => ?_
    obtain ⟨hy0, hy1⟩ := hy
    have hy0' : 0 < y := hy0
    have hya : y ≤ min (t / 2) (1 / 2) := not_lt.mp hy1
    have h2 : 2 ≤ t / y := by
      rw [le_div_iff₀ hy0']
      linarith
    rw [HW.hFun_of_two_le h2]
    ring
  have hlim : Tendsto (fun A => ∫ y in min (t / 2) (1 / 2)..A,
      HW.hFun (t / y) * HW.FH 200 y / y) atTop (𝓝 (HW.hH 200 t)) := by
    rw [hH_eq]
    exact intervalIntegral_tendsto_integral_Ioi _ hint tendsto_id
  have hzero : Tendsto (fun A => |HW.hFun (t / A)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun A : ℝ => t / A) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (continuous_hFun.tendsto 0).comp h1
    rw [HW.hFun_of_nonpos le_rfl] at h2
    simpa using h2.abs
  have hfin := ((hlim.sub_const (HW.hFun t)).abs).sub hzero
  rw [sub_zero] at hfin
  refine le_of_tendsto hfin ?_
  filter_upwards [eventually_ge_atTop (max t 1)] with A hA
  have h := window_bound ht ha ha1 hat (le_of_max_le_right hA) (le_of_max_le_left hA)
  linarith

/-- `e^{1/2} ≤ 1.6488` (truth `1.6487213`), from `e < 2.7182818286`. -/
theorem exp_half_le : Real.exp (1 / 2) ≤ 1.6488 := by
  have he := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **`B₀ ≤ 0.13`** (`B₀ = 0.118499`): `e^{1/2} ≤ 1.6488`, `log 2 < 0.6931471808`,
`π > 3.141592`. -/
theorem B0_le : B0 ≤ 0.13 := by
  have hX := exp_half_le
  have hX0 := Real.exp_pos (1 / 2)
  have hpi := Real.pi_gt_d6
  have hpi0 := Real.pi_pos
  have hl2 := Real.log_two_lt_d9
  have hl64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have e : B0 = (2 * kap * Real.exp (1 / 2) + 6 * Real.exp (1 / 2) * Cn) / π := by
    unfold B0
    ring
  rw [e, div_le_iff₀ hpi0]
  unfold Cn kap
  rw [hl64]
  have h1 : Real.exp (1 / 2) * π ≤ 1.6488 * π := mul_le_mul_of_nonneg_right hX hpi0.le
  have h2 : Real.exp (1 / 2) * Real.log 2 ≤ 1.6488 * 0.6931471808 :=
    mul_le_mul hX hl2.le (Real.log_nonneg (by norm_num)) (by norm_num)
  linarith

/-! ## The corollaries: link 0 of the Helfgott chain is closed -/

/-- **`HW.BandUniform` holds**: `∀ t > 0, |h₂₀₀(t) − h(t)| ≤ 0.13`. -/
theorem band_uniform : HW.BandUniform := fun _ ht => (band_bound ht).trans B0_le

/-- **`HW.EtaPlusSup` holds**: `|η₊|_∞ ≤ 1.079955` (Helfgott's (7.3), by a correct route). -/
theorem etaPlusSup : HW.EtaPlusSup := HW.etaPlusSup_of_band band_uniform

/-- **Link 0 on Helfgott's own weights, unconditionally**: `SupBounds η₊ η_*`. -/
theorem supBounds_helf : Smooth.SupBounds HW.etaPlus HW.etaStar := HW.supBounds_helf etaPlusSup

/-- **THE CHAIN at TWO links on Helfgott's own weights**: `PlattGRH → MajorLowerSmooth η₊ η_* →
MinorUpperSmooth η₊ η_* → Cite_Helfgott_weighted` (`HW.cite_band3` with `band_uniform`). -/
theorem cite_two (grh : Spine.PlattGRH) (mj : Smooth.MajorLowerSmooth HW.etaPlus HW.etaStar)
    (mn : Smooth.MinorUpperSmooth HW.etaPlus HW.etaStar) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  HW.cite_band3 grh band_uniform mj mn

end Principia.Common.TernaryGoldbach.BL
