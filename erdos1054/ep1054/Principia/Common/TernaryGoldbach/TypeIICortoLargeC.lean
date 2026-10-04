/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIICortoLarge

set_option autoImplicit false

/-!
# `M2H.CortoLarge` re-spined to CORRECTED `lem:yutto` links

`M2L.cortoLarge_of_links` (`TypeIICortoLarge.lean`) consumes Helfgott's printed `lem:yutto`
constants for `v = 2`, and both printed proofs are defective (that module's header):

* `YuttoMid2` (`|g₂(x)| ≤ (1634.34 + 817.168 log x)/x` on `[10⁶, 10¹⁰)`): the printed Rankin step
  drops `(x/2)^{2/log x} ≈ 6.7`; optimising `ε` recovers only `≈ 1.4` of it, so the printed
  method honestly gives `≈ 4.8×` the constant, and that spine tolerates only `≈ 1.25×`.
* `YuttoBig2` (`x ≥ 10¹⁰`): the last printed step is false at `x = 10¹⁰`.

This module replaces both by statements a CORRECTED argument plausibly reaches, and re-does the
tail bookkeeping so the budget still closes:

```
 YuttoMid2C   |g₂(x)| ≤ 1.5·(1634.34 + 817.168 log x)/x  on [10⁶, 10¹⁰)       LINK (corrected)
 YuttoBig2C   |g₂(x)| ≤ 0.038128/log²x + 3/√x            on [10¹⁰, ∞)          LINK (corrected)
 jint         ∫_{1/2}^{1} 1[c < u]/u du ≤ min(log 2, log(1/c))                PROVED
 tail_sC      the mid range charged only on u > 10⁶s/S (s = 1 near S = 10⁶)  PROVED
 tel_log      ∑_{1 ≤ k < n} log(X/(2k+1)) ≤ (X − 1)/2   (t(log(X/t)+1) telescoped)   PROVED
 cortoLarge_of_linksC : M2H.CortoLarge                                        PROVED
   from YuttoMid2C, YuttoBig2C, M2L.WeightEM + HC.YuttoSmallCited, HC.CortoC0Cited
```

Bound reached: `0.37210` at worst (`S = 2·10⁶`) against `0.37273`.

**Provenance of the corrected constants (why they are the right targets).** *YuttoBig2C*:
Helfgott's own three-term bound with the dropped factor restored, `0.038128/log²x +
25.607/(√x log x) + e²(1634.34 + 817.168 log x)/x`, is `≤ 2.62/√x + 0.038128/log²x` for
`x ≥ 10¹⁰` (each of `0.038128`, `25.607`, `55.768` re-evaluated from `eq:tausend` and agrees).
*YuttoMid2C*: the third clause of `HC.RamareCited` (`|∑_{n ≤ t} μ(n)/n| ≤ 1/(2√t)` on
`[3, 7727068587]`) replaces `√(2/t)` in `eq:kustor` by `t^{−1/2}/2`, a factor `1/8` after
squaring; with `ε = 1/(2 log x)` the Rankin part is `≈ 0.64×` the printed constant. What that
argument still owes is the `t < 3` terms (`dd'd'' > x/3`, where `|∑ μ(n)/n| ≤ 1`) and, for
`x > 7727068587`, the single `d = d' = d'' = 1` term — both `O(1/x)` without the `log x`, and
`1.5×` leaves `0.86×` of the printed constant for them. The bookkeeping here tolerates up to
`≈ 1.6×` (the old one `≈ 1.25×`).
-/

namespace Principia.Common.TernaryGoldbach.M2LC

open MeasureTheory Set

/-! ## (0) Corrected links and coefficients -/

/-- **Link [YuttoMid2C] — `lem:yutto`, `v = 2`, middle range, CORRECTED constant** (`1.5×`
Helfgott's printed `1634.34 + 817.168 log x`, which his printed proof does not establish):
`|g₂(x)| ≤ (2451.51 + 1225.752 log x)/x` for `10⁶ ≤ x < 10¹⁰`. Route: `HC.RamareCited`'s third
clause in `eq:kustor` (module header). OPEN. -/
def YuttoMid2C : Prop :=
  ∀ x : ℝ, 1000000 ≤ x → x < 10000000000 →
    |HC.gYutto 2 x| ≤ (2451.51 + 1225.752 * Real.log x) / x

/-- **Link [YuttoBig2C] — `lem:yutto`, `v = 2`, large range, CORRECTED constant** (the printed
`0.2046/√x` rests on a step false at `x = 10¹⁰`): `|g₂(x)| ≤ 0.038128/(log x)² + 3/√x` for
`x ≥ 10¹⁰`. Helfgott's own three terms with the dropped `e²` restored give `2.62/√x`. OPEN. -/
def YuttoBig2C : Prop :=
  ∀ x : ℝ, 10000000000 ≤ x → |HC.gYutto 2 x| ≤ 0.038128 / Real.log x ^ 2 + 3 / Real.sqrt x

/-- The `10⁶ < uS/s < 10¹⁰` height (`YuttoMid2C`, with `log(uS/s) ≤ log(S/s)`). -/
noncomputable def a2C (S : ℝ) (s : ℕ) : ℝ :=
  if (s : ℝ) ≤ S / 1000000 then 2451.51 + 1225.752 * Real.log (S / s) else 0

/-- The length factor of the middle range: `∫_{1/2}^{1} 1[u > 10⁶s/S] du/u ≤ ell`. -/
noncomputable def ell (S : ℝ) (s : ℕ) : ℝ :=
  min (Real.log 2) (Real.log (S / (1000000 * s)))

/-- The `uS/s ≥ 10¹⁰` majorant (`YuttoBig2C`, with `uS/s ≥ S/2s`). -/
noncomputable def bC3 (S : ℝ) (s : ℕ) : ℝ :=
  if (s : ℝ) ≤ S / 10000000000 then
    0.038128 / Real.log (S / (2 * s)) ^ 2 + 3 / Real.sqrt (S / (2 * s))
  else 0

/-- `1[c < u]/u`. -/
noncomputable def jk (c u : ℝ) : ℝ := if c < u then 1 / u else 0

theorem a2C_nonneg (S : ℝ) (s : ℕ) (hs : 1 ≤ s) : 0 ≤ a2C S s := by
  unfold a2C
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  split_ifs with h
  · have h1 : 1 ≤ S / s := by
      rw [le_div_iff₀ hs0]
      have := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mp h
      linarith
    have := Real.log_nonneg h1
    nlinarith
  · exact le_rfl

theorem bC3_nonneg (S : ℝ) (s : ℕ) : 0 ≤ bC3 S s := by
  unfold bC3
  split_ifs
  · positivity
  · exact le_rfl

theorem ell_nonneg (S : ℝ) (s : ℕ) (hs : 1 ≤ s) (h : (s : ℝ) ≤ S / 1000000) : 0 ≤ ell S s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : 1 ≤ S / (1000000 * s) := by
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mp h
    linarith
  exact le_min (Real.log_nonneg (by norm_num)) (Real.log_nonneg h1)

theorem ea_nonneg (S : ℝ) (s : ℕ) (hs : 1 ≤ s) : 0 ≤ ell S s * a2C S s := by
  by_cases h : (s : ℝ) ≤ S / 1000000
  · exact mul_nonneg (ell_nonneg S s hs h) (a2C_nonneg S s hs)
  · unfold a2C
    rw [if_neg h, mul_zero]

/-! ## (1) The middle-range kernel -/

theorem jk_nonneg (c u : ℝ) (hu : 0 < u) : 0 ≤ jk c u := by
  unfold jk
  split_ifs
  · positivity
  · exact le_rfl

theorem jk_le (c u : ℝ) (hu : 0 < u) : jk c u ≤ 1 / u := by
  unfold jk
  split_ifs
  · exact le_rfl
  · positivity

theorem meas_jk (c : ℝ) : Measurable fun u : ℝ => jk c u :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_const.div measurable_id) measurable_const

theorem ii_jk (c a b : ℝ) (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable (fun u : ℝ => jk c u) volume a b := by
  refine M2H.ii_of_bdd _ (meas_jk c) (1 / a) a b hab fun u hu => ?_
  have hu0 : 0 < u := lt_trans ha hu.1
  rw [abs_of_nonneg (jk_nonneg c u hu0)]
  exact (jk_le c u hu0).trans (one_div_le_one_div_of_le ha hu.1.le)

/-- **`∫_{1/2}^{1} 1[c < u] du/u ≤ min(log 2, log(1/c))`** for `0 < c ≤ 1`. -/
theorem jint (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ u in (1 / 2 : ℝ)..1, jk c u ≤ min (Real.log 2) (Real.log (1 / c)) := by
  have hle : ∀ a b : ℝ, 0 < a → a ≤ b → ∫ u in a..b, jk c u ≤ Real.log (b / a) := by
    intro a b ha hab
    rw [← integral_one_div_of_pos ha (by linarith)]
    have hc : ContinuousOn (fun u : ℝ => 1 / u) (uIcc a b) := by
      refine continuousOn_const.div continuousOn_id fun u hu => ?_
      rw [uIcc_of_le hab] at hu
      exact ne_of_gt (by linarith [hu.1])
    refine intervalIntegral.integral_mono_on hab (ii_jk c a b hab ha) hc.intervalIntegrable
      fun u hu => jk_le c u (by linarith [hu.1])
  rcases le_or_gt c (1 / 2) with h | h
  · have h1 := hle (1 / 2) 1 (by norm_num) (by norm_num)
    have e : Real.log (1 / (1 / 2 : ℝ)) = Real.log 2 := by norm_num
    rw [e] at h1
    have h2 : Real.log 2 ≤ Real.log (1 / c) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hc0]; linarith)
    rw [min_eq_left h2]
    exact h1
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
      (ii_jk c _ _ h.le (by norm_num)) (ii_jk c _ _ hc1 hc0)]
    have h0 : ∫ u in (1 / 2 : ℝ)..c, jk c u = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
      · simp
      · rw [uIcc_of_le h.le] at hu
        simp only [jk]
        rw [if_neg (not_lt.mpr hu.2)]
    have h1 := hle c 1 hc0 hc1
    have h2 : Real.log (1 / c) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by rw [div_le_iff₀ hc0]; linarith)
    rw [min_eq_right h2, h0, zero_add]
    exact h1

/-! ## (2) The tail, one `s` at a time -/

/-- **Pointwise tail majorant** on `u ∈ [1/2, 1]`, the middle range carried by `jk`. -/
theorem tl_ptC (ys : HC.YuttoSmallCited) (ym : YuttoMid2C) (yb : YuttoBig2C) (S : ℝ)
    (hS : 0 < S) (s : ℕ) (hs : 1 ≤ s) (u : ℝ) (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 1) :
    |M2L.tl (u * S / s)| ≤ M2L.a1 S s * ((s : ℝ) / S / u) +
      a2C S s * ((s : ℝ) / S * jk (1000000 * s / S) u) + bC3 S s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < u * S / s := by positivity
  have hxr : 1 / (u * S / s) = (s : ℝ) / S / u := by field_simp
  have hxS : u * S / s ≤ S / s := by
    rw [div_le_div_iff_of_pos_right hs0]
    nlinarith
  have hxS2 : S / (2 * s) ≤ u * S / s := by
    rw [div_le_div_iff₀ (by positivity) hs0]
    have : 0 ≤ (2 * u - 1) * (S * s) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have h1a := M2L.a1_nonneg S s
  have h2a := a2C_nonneg S s hs
  have hb := bC3_nonneg S s
  have hr0 : 0 ≤ (s : ℝ) / S / u := by positivity
  have hj0 : 0 ≤ a2C S s * ((s : ℝ) / S * jk (1000000 * s / S) u) :=
    mul_nonneg h2a (mul_nonneg (by positivity) (jk_nonneg _ u hu0))
  have h1r : 0 ≤ M2L.a1 S s * ((s : ℝ) / S / u) := mul_nonneg h1a hr0
  have hcond : ∀ c : ℝ, 0 < c → c ≤ u * S / s → (s : ℝ) ≤ S / c := by
    intro c hc h
    have h' := le_trans h hxS
    rw [le_div_iff₀ hs0] at h'
    rw [le_div_iff₀ hc]
    linarith
  unfold M2L.tl
  split_ifs with h1
  swap
  · rw [abs_zero]
    linarith
  rcases le_or_gt (u * S / s) 1000000 with h2 | h2
  · have hg := (ys (u * S / s) (by linarith) h2).2
    have hc : M2L.a1 S s = 2.1 := by
      unfold M2L.a1
      rw [if_pos (hcond 10001 (by norm_num) h1)]
    have : |HC.gYutto 2 (u * S / s)| ≤ M2L.a1 S s * ((s : ℝ) / S / u) := by
      calc |HC.gYutto 2 (u * S / s)| ≤ 2.1 / (u * S / s) := hg
        _ = 2.1 * (1 / (u * S / s)) := by ring
        _ = M2L.a1 S s * ((s : ℝ) / S / u) := by rw [hxr, hc]
    linarith
  rcases lt_or_ge (u * S / s) 10000000000 with h3 | h3
  · have hg := ym (u * S / s) h2.le h3
    have hc : a2C S s = 2451.51 + 1225.752 * Real.log (S / s) := by
      unfold a2C
      rw [if_pos (hcond 1000000 (by norm_num) h2.le)]
    have hj : jk (1000000 * s / S) u = 1 / u := by
      unfold jk
      rw [if_pos]
      rw [div_lt_iff₀ hS]
      have := (lt_div_iff₀ hs0).mp h2
      linarith
    have hlog : Real.log (u * S / s) ≤ Real.log (S / s) := Real.log_le_log hx0 hxS
    have hm : |HC.gYutto 2 (u * S / s)| ≤
        a2C S s * ((s : ℝ) / S * jk (1000000 * s / S) u) := by
      calc |HC.gYutto 2 (u * S / s)|
          ≤ (2451.51 + 1225.752 * Real.log (u * S / s)) / (u * S / s) := hg
        _ = (2451.51 + 1225.752 * Real.log (u * S / s)) * (1 / (u * S / s)) := by ring
        _ = (2451.51 + 1225.752 * Real.log (u * S / s)) * ((s : ℝ) / S / u) := by rw [hxr]
        _ ≤ a2C S s * ((s : ℝ) / S / u) :=
            mul_le_mul_of_nonneg_right (by rw [hc]; linarith) hr0
        _ = a2C S s * ((s : ℝ) / S * jk (1000000 * s / S) u) := by rw [hj]; ring
    linarith
  · have hg := yb (u * S / s) h3
    have hc := hcond 10000000000 (by norm_num) h3
    have hS2 : 1 < S / (2 * s) := by
      rw [lt_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by norm_num)] at hc
      linarith
    have hL : 0 < Real.log (S / (2 * s)) := Real.log_pos hS2
    have hlog : Real.log (S / (2 * s)) ≤ Real.log (u * S / s) :=
      Real.log_le_log (by linarith) hxS2
    have e1 : 0.038128 / Real.log (u * S / s) ^ 2 ≤ 0.038128 / Real.log (S / (2 * s)) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hL.le hlog 2)
    have e2 : 3 / Real.sqrt (u * S / s) ≤ 3 / Real.sqrt (S / (2 * s)) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by linarith))
        (Real.sqrt_le_sqrt hxS2)
    have hbC : bC3 S s = 0.038128 / Real.log (S / (2 * s)) ^ 2 +
        3 / Real.sqrt (S / (2 * s)) := by
      unfold bC3
      rw [if_pos hc]
    linarith

/-- **One summand of the tail**:
`(1/s)∫_{1/2}^{1} tl(uS/s) du ≤ (log 2/S)a₁ + (1/S)·ell·a₂ + bC/(2s)`. -/
theorem tail_sC (ys : HC.YuttoSmallCited) (ym : YuttoMid2C) (yb : YuttoBig2C) (S : ℝ)
    (hS : 0 < S) (s : ℕ) (hs : 1 ≤ s) :
    1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, M2L.tl (u * S / s) ≤
      Real.log 2 / S * M2L.a1 S s + 1 / S * (ell S s * a2C S s) + 1 / (2 * s) * bC3 S s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  set c := 1000000 * (s : ℝ) / S with hcdef
  have hiiA : IntervalIntegrable (fun u : ℝ => M2L.a1 S s * ((s : ℝ) / S / u))
      volume (1 / 2) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_const.div continuousOn_id ?_)
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    exact ne_of_gt (by linarith [hu.1])
  have hiiB : IntervalIntegrable (fun u : ℝ => a2C S s * ((s : ℝ) / S * jk c u))
      volume (1 / 2) 1 :=
    ((ii_jk c (1 / 2) 1 (by norm_num) (by norm_num)).const_mul _).const_mul _
  have hinv : ∫ u in (1 / 2 : ℝ)..1, (s : ℝ) / S / u = (s : ℝ) / S * Real.log 2 := by
    have h : ∀ u : ℝ, (s : ℝ) / S / u = (s : ℝ) / S * u⁻¹ := fun u => by ring
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  set J := ∫ u in (1 / 2 : ℝ)..1, jk c u with hJ
  have hint : ∫ u in (1 / 2 : ℝ)..1, (M2L.a1 S s * ((s : ℝ) / S / u) +
      a2C S s * ((s : ℝ) / S * jk c u) + bC3 S s) =
      M2L.a1 S s * ((s : ℝ) / S * Real.log 2) + a2C S s * ((s : ℝ) / S * J) + bC3 S s / 2 := by
    rw [intervalIntegral.integral_add (hiiA.add hiiB) intervalIntegrable_const,
      intervalIntegral.integral_add hiiA hiiB, intervalIntegral.integral_const_mul, hinv,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have key : a2C S s * J ≤ ell S s * a2C S s := by
    by_cases h : (s : ℝ) ≤ S / 1000000
    · have hc1 : c ≤ 1 := by
        rw [hcdef, div_le_one hS]
        have := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mp h
        linarith
      have hj := jint c (by positivity) hc1
      rw [hcdef, one_div_div] at hj
      calc a2C S s * J ≤ a2C S s * min (Real.log 2) (Real.log (S / (1000000 * s))) :=
            mul_le_mul_of_nonneg_left hj (a2C_nonneg S s hs)
        _ = ell S s * a2C S s := by unfold ell; ring
    · unfold a2C
      rw [if_neg h]
      simp
  have h1 : |∫ u in (1 / 2 : ℝ)..1, M2L.tl (u * S / s)| ≤
      ∫ u in (1 / 2 : ℝ)..1, |M2L.tl (u * S / s)| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have h2 : ∫ u in (1 / 2 : ℝ)..1, |M2L.tl (u * S / s)| ≤
      ∫ u in (1 / 2 : ℝ)..1, (M2L.a1 S s * ((s : ℝ) / S / u) +
        a2C S s * ((s : ℝ) / S * jk c u) + bC3 S s) :=
    intervalIntegral.integral_mono_on (by norm_num) (M2L.ii_tl S hS.le s hs).abs
      ((hiiA.add hiiB).add intervalIntegrable_const)
      fun u hu => tl_ptC ys ym yb S hS s hs u hu.1 hu.2
  rw [hint] at h2
  have hsS : 0 ≤ (s : ℝ) / S := by positivity
  have h3 : a2C S s * ((s : ℝ) / S * J) ≤ (s : ℝ) / S * (ell S s * a2C S s) := by
    calc a2C S s * ((s : ℝ) / S * J) = (s : ℝ) / S * (a2C S s * J) := by ring
      _ ≤ (s : ℝ) / S * (ell S s * a2C S s) := mul_le_mul_of_nonneg_left key hsS
  have hpos : 0 ≤ 1 / (s : ℝ) := by positivity
  calc 1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, M2L.tl (u * S / s)
      ≤ 1 / (s : ℝ) * |∫ u in (1 / 2 : ℝ)..1, M2L.tl (u * S / s)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hpos
    _ ≤ 1 / (s : ℝ) * (M2L.a1 S s * ((s : ℝ) / S * Real.log 2) +
          (s : ℝ) / S * (ell S s * a2C S s) + bC3 S s / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = Real.log 2 / S * M2L.a1 S s + 1 / S * (ell S s * a2C S s) + 1 / (2 * s) * bC3 S s := by
        field_simp

/-! ## (3) The middle-range sum over odd `s` -/

/-- `Φ(t) = t(log(X/t) + 1)`, an antiderivative of `log(X/t)`. -/
noncomputable def phi (X t : ℝ) : ℝ := t * (Real.log (X / t) + 1)

theorem phi_le (X t : ℝ) (hX : 0 < X) (ht : 0 < t) : phi X t ≤ X := by
  unfold phi
  have h := Real.log_le_sub_one_of_pos (show 0 < X / t by positivity)
  have e : t * (X / t - 1) = X - t := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h ht.le]

/-- One telescoping step: `log(X/q) ≤ (Φ(q) − Φ(q − 2))/2`, `q = p + 2`. -/
theorem phi_step (X p : ℝ) (hX : 0 < X) (hp : 0 < p) :
    Real.log (X / (p + 2)) ≤ (phi X (p + 2) - phi X p) / 2 := by
  unfold phi
  have hq : 0 < p + 2 := by linarith
  have e : Real.log (X / p) = Real.log (X / (p + 2)) + Real.log ((p + 2) / p) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hl := Real.log_le_sub_one_of_pos (show 0 < (p + 2) / p by positivity)
  have e2 : p * ((p + 2) / p - 1) = 2 := by field_simp; ring
  have h3 := mul_le_mul_of_nonneg_left hl hp.le
  rw [e]
  nlinarith

/-- **`∑_{k < n} log(X/(2k+3)) ≤ (X − 1)/2`** for `X ≥ 1`. -/
theorem tel_log (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.log (X / (2 * (k : ℝ) + 3)) ≤ (X - 1) / 2 := by
  have hX0 : 0 < X := by linarith
  have h : ∀ n : ℕ, ∑ k ∈ Finset.range n, Real.log (X / (2 * (k : ℝ) + 3)) ≤
      (phi X (2 * n + 1) - phi X 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := phi_step X (2 * (n : ℝ) + 1) hX0 (by positivity)
      have e1 : (2 * (n : ℝ) + 1 + 2) = 2 * (n : ℝ) + 3 := by ring
      have e2 : (2 * ((n + 1 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by push_cast; ring
      rw [e1] at hs
      rw [e2]
      linarith
  have h1 := phi_le X (2 * n + 1) hX0 (by positivity)
  have h2 : phi X 1 = Real.log X + 1 := by simp [phi]
  have h3 := Real.log_nonneg hX
  linarith [h n]

theorem log_1e6u : Real.log 1000000 ≤ 13.862943616 := by
  have h : (1000000 : ℝ) ≤ 2 ^ 20 := by norm_num
  have h2 := Real.log_le_log (by norm_num) h
  rw [Real.log_pow] at h2
  have := Real.log_two_lt_d9
  push_cast at h2
  linarith

/-- **The middle-range sum**: `∑_{s ≤ S odd} ell·a₂ ≤ ell(1)(A + B log S) + log 2·(nA'' +
B(X − 1)/2)` with `X = S/10⁶`, `2n + 1 ≤ X`. -/
theorem sum_mid (S : ℝ) (hS : 1000000 ≤ S) :
    ∃ n : ℕ, 2 * (n : ℝ) + 1 ≤ S / 1000000 ∧
      ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2), ell S s * a2C S s ≤
        ell S 1 * (2451.51 + 1225.752 * Real.log S) + Real.log 2 *
          (n * (2451.51 + 1225.752 * 13.862943616) + 1225.752 * ((S / 1000000 - 1) / 2)) := by
  have hS0 : 0 < S := by linarith
  set X := S / 1000000 with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ (by norm_num)]; linarith
  have hodd := M2L.odd_sum_le ⌊S⌋₊ X (fun s => ell S s * a2C S s) (fun s hs => by
      unfold a2C
      rw [if_neg (not_le.mpr hs), mul_zero])
    (fun k _ => ea_nonneg S _ (by omega))
  set K := ⌊(X + 1) / 2⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by push_cast; linarith)
  have hKle : (K : ℝ) ≤ (X + 1) / 2 := Nat.floor_le (by positivity)
  obtain ⟨n, hn⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  have hnX : 2 * (n : ℝ) + 1 ≤ X := by
    rw [hn] at hKle
    push_cast at hKle
    linarith
  refine ⟨n, hnX, hodd.trans ?_⟩
  rw [hn, Finset.sum_range_succ']
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ Finset.range n, ell S (2 * (k + 1) + 1) * a2C S (2 * (k + 1) + 1) ≤
      Real.log 2 * ((2451.51 + 1225.752 * 13.862943616) +
        1225.752 * Real.log (X / (2 * (k : ℝ) + 3))) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.mp hk
      exact_mod_cast this
    have hsX : 2 * (k : ℝ) + 3 ≤ X := by linarith
    have hcast : ((2 * (k + 1) + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 3 := by push_cast; ring
    have hcond : ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤ S / 1000000 := by rw [hcast]; exact hsX
    have ha : a2C S (2 * (k + 1) + 1) = 2451.51 + 1225.752 * Real.log (S / (2 * (k : ℝ) + 3)) := by
      unfold a2C
      rw [if_pos hcond, hcast]
    have hsplit : Real.log (S / (2 * (k : ℝ) + 3)) =
        Real.log 1000000 + Real.log (X / (2 * (k : ℝ) + 3)) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      rw [hXdef]
      field_simp
    have hlX : 0 ≤ Real.log (X / (2 * (k : ℝ) + 3)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
    have hell : ell S (2 * (k + 1) + 1) ≤ Real.log 2 := min_le_left _ _
    have hell0 := ell_nonneg S (2 * (k + 1) + 1) (by omega) hcond
    have h6 := log_1e6u
    have ha0 := a2C_nonneg S (2 * (k + 1) + 1) (by omega)
    have hab : a2C S (2 * (k + 1) + 1) ≤ (2451.51 + 1225.752 * 13.862943616) +
        1225.752 * Real.log (X / (2 * (k : ℝ) + 3)) := by
      rw [ha, hsplit]
      nlinarith
    calc ell S (2 * (k + 1) + 1) * a2C S (2 * (k + 1) + 1)
        ≤ Real.log 2 * a2C S (2 * (k + 1) + 1) := mul_le_mul_of_nonneg_right hell ha0
      _ ≤ _ := mul_le_mul_of_nonneg_left hab hl20.le
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have htel := tel_log X hX1 n
  have hfirst : ell S (2 * 0 + 1) * a2C S (2 * 0 + 1) ≤
      ell S 1 * (2451.51 + 1225.752 * Real.log S) := by
    have hc : ((1 : ℕ) : ℝ) ≤ S / 1000000 := by push_cast; exact hX1
    have ha : a2C S 1 = 2451.51 + 1225.752 * Real.log S := by
      unfold a2C
      rw [if_pos hc]
      norm_num
    change ell S 1 * a2C S 1 ≤ _
    rw [ha]
  have hmid : Real.log 2 * (n * (2451.51 + 1225.752 * 13.862943616) +
      1225.752 * ∑ k ∈ Finset.range n, Real.log (X / (2 * (k : ℝ) + 3))) ≤
      Real.log 2 * (n * (2451.51 + 1225.752 * 13.862943616) + 1225.752 * ((X - 1) / 2)) := by
    apply mul_le_mul_of_nonneg_left _ hl20.le
    linarith
  linarith

/-- **The middle range, numerically**: `∑ ell·a₂ ≤ 10863.61·S/10⁶` for `S ≥ 10⁶`
(worst at `S = 2·10⁶`; for `S ≤ 2·10⁶` via `log X = t`, `X ≥ 1 + t + t²/2`). -/
theorem mid_le (S : ℝ) (hS : 1000000 ≤ S) :
    ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2), ell S s * a2C S s ≤
      10863.61 * (S / 1000000) := by
  obtain ⟨n, hn, h⟩ := sum_mid S hS
  set X := S / 1000000 with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ (by norm_num)]; linarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the `n`-part: `log 2·(nA'' + B(X−1)/2) ≤ 7163.61(X − 1)`
  have hn' : (n : ℝ) ≤ (X - 1) / 2 := by linarith
  have hpart : Real.log 2 * (n * (2451.51 + 1225.752 * 13.862943616) +
      1225.752 * ((X - 1) / 2)) ≤ 7163.61 * (X - 1) := by
    have h1 : n * (2451.51 + 1225.752 * 13.862943616) + 1225.752 * ((X - 1) / 2) ≤
        (X - 1) / 2 * (2451.51 + 1225.752 * 13.862943616 + 1225.752) := by nlinarith
    have h0 : 0 ≤ (X - 1) / 2 * (2451.51 + 1225.752 * 13.862943616 + 1225.752) := by
      have : 0 ≤ X - 1 := by linarith
      positivity
    calc Real.log 2 * (n * (2451.51 + 1225.752 * 13.862943616) + 1225.752 * ((X - 1) / 2))
        ≤ Real.log 2 * ((X - 1) / 2 * (2451.51 + 1225.752 * 13.862943616 + 1225.752)) :=
          mul_le_mul_of_nonneg_left h1 hl20.le
      _ ≤ 0.6931471808 * ((X - 1) / 2 * (2451.51 + 1225.752 * 13.862943616 + 1225.752)) :=
          mul_le_mul_of_nonneg_right hl2.le h0
      _ ≤ 7163.61 * (X - 1) := by nlinarith
  -- the `s = 1` part: `ell(1)(A + B log S) ≤ 3700X + 7163.61`
  have hlogS : Real.log S = Real.log 1000000 + Real.log X := by
    rw [← Real.log_mul (by norm_num) (by positivity), hXdef]
    congr 1
    field_simp
  have h6 := log_1e6u
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hA : 2451.51 + 1225.752 * Real.log S ≤
      2451.51 + 1225.752 * 13.862943616 + 1225.752 * Real.log X := by
    rw [hlogS]
    linarith
  have hA0 : 0 ≤ 2451.51 + 1225.752 * Real.log S := by
    rw [hlogS]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1000000 by norm_num)
    linarith
  have hell1 : ell S 1 = min (Real.log 2) (Real.log X) := by
    unfold ell
    rw [hXdef]
    norm_num
  have hell0 : 0 ≤ ell S 1 := by
    rw [hell1]
    exact le_min hl20.le hlX0
  have hone : ell S 1 * (2451.51 + 1225.752 * Real.log S) ≤ 3700 * X + 7163.61 := by
    have hstep : ell S 1 * (2451.51 + 1225.752 * Real.log S) ≤
        ell S 1 * (2451.51 + 1225.752 * 13.862943616 + 1225.752 * Real.log X) :=
      mul_le_mul_of_nonneg_left hA hell0
    rcases le_or_gt X 2 with hX2 | hX2
    · -- `t = log X ∈ [0, log 2]`, `X = e^t ≥ 1 + t + t²/2`
      set t := Real.log X with htdef
      have ht2 : t ≤ Real.log 2 := Real.log_le_log (by linarith) hX2
      have hellt : ell S 1 ≤ t := by rw [hell1]; exact min_le_right _ _
      have hexp : 1 + t + t ^ 2 / 2 ≤ X := by
        have := Real.quadratic_le_exp_of_nonneg hlX0
        rwa [htdef, Real.exp_log (by linarith)] at this
      have hin : 0 ≤ 2451.51 + 1225.752 * 13.862943616 + 1225.752 * t := by linarith
      have h2 : ell S 1 * (2451.51 + 1225.752 * 13.862943616 + 1225.752 * t) ≤
          t * (2451.51 + 1225.752 * 13.862943616 + 1225.752 * t) :=
        mul_le_mul_of_nonneg_right hellt hin
      nlinarith [sq_nonneg (t - 0.69)]
    · have hellL : ell S 1 ≤ Real.log 2 := by rw [hell1]; exact min_le_left _ _
      have hlogX : Real.log X ≤ Real.log 2 + (X - 2) / 2 := by
        have h := Real.log_le_sub_one_of_pos (show 0 < X / 2 by linarith)
        rw [Real.log_div (by linarith) (by norm_num)] at h
        linarith
      have hin : 0 ≤ 2451.51 + 1225.752 * 13.862943616 + 1225.752 * Real.log X := by linarith
      have h2 : ell S 1 * (2451.51 + 1225.752 * 13.862943616 + 1225.752 * Real.log X) ≤
          Real.log 2 * (2451.51 + 1225.752 * 13.862943616 + 1225.752 * Real.log X) :=
        mul_le_mul_of_nonneg_right hellL hin
      have h3 : Real.log 2 * (2451.51 + 1225.752 * 13.862943616 + 1225.752 * Real.log X) ≤
          Real.log 2 * (2451.51 + 1225.752 * 13.862943616 +
            1225.752 * (Real.log 2 + (X - 2) / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hl20.le
      have hin2 : 0 ≤ 2451.51 + 1225.752 * 13.862943616 +
          1225.752 * (Real.log 2 + (X - 2) / 2) := by linarith
      have h4 : Real.log 2 * (2451.51 + 1225.752 * 13.862943616 +
            1225.752 * (Real.log 2 + (X - 2) / 2)) ≤
          0.6931471808 * (2451.51 + 1225.752 * 13.862943616 +
            1225.752 * (0.6931471808 + (X - 2) / 2)) := by
        apply mul_le_mul hl2.le (by linarith) hin2 (by norm_num)
      nlinarith
  linarith

/-! ## (4) The large-range sum with the corrected `3/√x` -/

theorem sq_termC (S s : ℝ) (hS : 0 < S) (hs : 0 < s) :
    1 / (2 * s) * (3 / Real.sqrt (S / (2 * s))) =
      3 * (1 / Real.sqrt (2 * S) * (1 / Real.sqrt s)) := by
  have h := M2L.sq_term S s hS hs
  have e1 : 1 / (2 * s) * (3 / Real.sqrt (S / (2 * s))) =
      3 / 0.2046 * (1 / (2 * s) * (0.2046 / Real.sqrt (S / (2 * s)))) := by
    field_simp
  rw [e1, h]
  field_simp

/-- **The `S/s ≥ 10¹⁰` sum**: `≤ 0.019064(1/484 + 0.54/22) + 3/10⁵`. -/
theorem sum3C (S : ℝ) (hS : 0 < S) (K : ℕ)
    (hK : ∀ k ∈ Finset.range K, 2 * (k : ℝ) + 1 ≤ S / 10000000000)
    (hK2 : 2 * (K : ℝ) ≤ S / 10000000000 + 1) :
    ∑ k ∈ Finset.range K, 1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) * bC3 S (2 * k + 1) ≤
      0.019064 * (1 / 484 + 0.54 / 22) + 3 / 100000 := by
  rcases K with _ | n
  · simp only [Finset.range_zero, Finset.sum_empty]
    norm_num
  have hterm : ∀ k ∈ Finset.range (n + 1),
      1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) * bC3 S (2 * k + 1) =
      0.019064 * (1 / (2 * (k : ℝ) + 1) * (1 / M2L.lg S k ^ 2)) +
        3 * (1 / Real.sqrt (2 * S) * (1 / Real.sqrt (2 * (k : ℝ) + 1))) := by
    intro k hk
    have hc := hK k hk
    unfold bC3
    push_cast
    rw [if_pos hc, mul_add, sq_termC S _ hS (by positivity)]
    unfold M2L.lg
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have h1 := M2L.tel S n (hK n (by simp))
  have hLn := M2L.lg_ge S n (hK n (by simp))
  have hL0 := M2L.lg_ge S 0 (hK 0 (by simp))
  have h1n : 1 / M2L.lg S n ≤ 1 / 22 := one_div_le_one_div_of_le (by norm_num) hLn
  have h10 : 0 ≤ 1 / M2L.lg S 0 := by
    have : 0 < M2L.lg S 0 := by linarith
    positivity
  have h2 := M2L.inv_sqrt_sum (n + 1)
  have hq : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * S) / 100000 := by
    have e : Real.sqrt (2 * S) / 100000 = Real.sqrt (2 * S / 10000000000) := by
      rw [Real.sqrt_div' _ (by norm_num)]
      congr 1
      rw [show (10000000000 : ℝ) = 100000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.sqrt_le_sqrt
    push_cast at hK2 ⊢
    have hX : 1 ≤ S / 10000000000 := by
      have := hK 0 (by simp)
      push_cast at this
      linarith
    have : S / 10000000000 + 1 ≤ 2 * S / 10000000000 := by
      rw [mul_div_assoc]
      linarith
    linarith
  have hS2 : 0 < Real.sqrt (2 * S) := Real.sqrt_pos.2 (by linarith)
  have h3 : 1 / Real.sqrt (2 * S) * ∑ k ∈ Finset.range (n + 1),
      1 / Real.sqrt (2 * (k : ℝ) + 1) ≤ 1 / 100000 := by
    calc 1 / Real.sqrt (2 * S) * ∑ k ∈ Finset.range (n + 1), 1 / Real.sqrt (2 * (k : ℝ) + 1)
        ≤ 1 / Real.sqrt (2 * S) * (Real.sqrt (2 * S) / 100000) :=
          mul_le_mul_of_nonneg_left (h2.trans hq) (by positivity)
      _ = 1 / 100000 := by field_simp
  nlinarith

/-! ## (5) `M2H.CortoLarge` from the corrected links -/

/-- **`M2H.CortoLarge` from the CORRECTED `lem:yutto` links `YuttoMid2C`, `YuttoBig2C`,
`M2L.WeightEM`, and the cited `HC.YuttoSmallCited`, `HC.CortoC0Cited`, PROVED.** Bound reached
`0.37210` (worst `S = 2·10⁶`) against `0.37273`. -/
theorem cortoLarge_of_linksC (ym : YuttoMid2C) (yb : YuttoBig2C) (em : M2L.WeightEM)
    (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited) : M2H.CortoLarge := by
  intro S hS
  have hS0 : 0 < S := by linarith
  rw [M2L.corto_split S hS0.le]
  have hA := M2L.main_le em c0 S hS
  set F := (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2) with hF
  have hs1 : ∀ s ∈ F, 1 ≤ s := fun s hs => (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hB : ∑ s ∈ F, 1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, M2L.tl (u * S / s) ≤
      Real.log 2 / S * (∑ s ∈ F, M2L.a1 S s) + 1 / S * (∑ s ∈ F, ell S s * a2C S s) +
        ∑ s ∈ F, 1 / (2 * (s : ℝ)) * bC3 S s := by
    refine (Finset.sum_le_sum fun s hs => tail_sC ys ym yb S hS0 s (hs1 s hs)).trans
      (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  set K1 := ⌊(S / 10001 + 1) / 2⌋₊ with hK1def
  set K3 := ⌊(S / 10000000000 + 1) / 2⌋₊ with hK3def
  have h1 : ∑ s ∈ F, M2L.a1 S s ≤ K1 * 2.1 := by
    refine (M2L.odd_sum_le ⌊S⌋₊ (S / 10001) (M2L.a1 S) (fun s hs => ?_)
      (fun k _ => M2L.a1_nonneg S _)).trans ?_
    · unfold M2L.a1
      rw [if_neg (not_le.mpr hs)]
    · have := Finset.sum_le_card_nsmul (Finset.range K1) (fun k => M2L.a1 S (2 * k + 1)) 2.1
        (fun k _ => by
          unfold M2L.a1
          split_ifs <;> norm_num)
      rw [Finset.card_range, nsmul_eq_mul] at this
      exact this
  have h3 : ∑ s ∈ F, 1 / (2 * (s : ℝ)) * bC3 S s ≤
      0.019064 * (1 / 484 + 0.54 / 22) + 3 / 100000 := by
    refine (M2L.odd_sum_le ⌊S⌋₊ (S / 10000000000) (fun s => 1 / (2 * (s : ℝ)) * bC3 S s)
      (fun s hs => ?_) (fun k _ => mul_nonneg (by positivity) (bC3_nonneg S _))).trans
      (sum3C S hS0 K3 (fun k hk => M2L.range_le _ (by positivity) k hk) ?_)
    · unfold bC3
      rw [if_neg (not_le.mpr hs), mul_zero]
    · have := Nat.floor_le (show 0 ≤ (S / 10000000000 + 1) / 2 by positivity)
      linarith
  have hK1 : (K1 : ℝ) ≤ (S / 10001 + 1) / 2 := Nat.floor_le (by positivity)
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsa1 : Real.log 2 / S * (∑ s ∈ F, M2L.a1 S s) ≤
      0.6931471808 * (1.05 / 10001 + 1.05 / S) := by
    have hq : (∑ s ∈ F, M2L.a1 S s) / S ≤ 1.05 / 10001 + 1.05 / S := by
      rw [div_le_iff₀ hS0]
      have e : (1.05 / 10001 + 1.05 / S) * S = 1.05 / 10001 * S + 1.05 := by field_simp
      rw [e]
      linarith
    have hq0 : 0 ≤ (∑ s ∈ F, M2L.a1 S s) / S :=
      div_nonneg (Finset.sum_nonneg fun s _ => M2L.a1_nonneg S s) hS0.le
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul hl2.le hq hq0 (by norm_num)
  have hinvS : 1.05 / S ≤ 1.05 / 100000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hS
  rcases lt_or_ge S 1000000 with hS6 | hS6
  · have hz : ∑ s ∈ F, ell S s * a2C S s = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have h1s : (1 : ℝ) ≤ s := by exact_mod_cast hs1 s hs
      have hn : ¬ (s : ℝ) ≤ S / 1000000 := by
        rw [le_div_iff₀ (by norm_num)]
        linarith
      unfold a2C
      rw [if_neg hn, mul_zero]
    rw [hz, mul_zero, add_zero] at hB
    have hP : 47734020.6 / S ^ 2 ≤ 0.00477340206 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have hm := mid_le S hS6
    have hm' : 1 / S * (∑ s ∈ F, ell S s * a2C S s) ≤ 10863.61 / 1000000 := by
      rw [one_div_mul_eq_div, div_le_iff₀ hS0]
      have e : 10863.61 / 1000000 * S = 10863.61 * (S / 1000000) := by ring
      rw [e]
      exact hm
    have hinvS6 : 1.05 / S ≤ 1.05 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hS6
    have hP : 47734020.6 / S ^ 2 ≤ 0.0000477340206 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end Principia.Common.TernaryGoldbach.M2LC
