/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIISecInt

set_option autoImplicit false

/-!
# `T2S.Vin1Calc` PROVED from the cited `eq:notung`

`vin1Calc_of : HC.NotungCited → T2S.Vin1Calc` — the integral calculus that turns the pointwise
bounds (`eq:menson2` + `eq:velib` + `eq:demimond` for `S₁`, `eq:garn1a` + `eq:immer` for `S₂`,
`eq:negli` for `S₃`) into `eq:vinland1` at the first choice, EXACTLY the book's display `vin1`
(`minarctotals.tex` 525-830; `eq:senorburns` has zero main-term slack against it).

* **Main term — exact.** AM-GM in `β` on `√(2(H₂ + E)·log W/log(W/2q))`, `∫H₂(x/WU)dW/W =
  ∫_1^{x/UV}H₂(s)ds/s ≤ 0.15107·log(x/UV)` (the substitution `s = x/WU`, `int_subst`),
  `∫dW/(W log(W/2q)) = log(1 + log(x/UV)/log(V/2q))` (`int_loglog`), and the optimal
  `β = √(κ₆L₀ + 2κ₇)/√(2(L₀ + Φ))` (`main_alg`) give `x/√(2φ(q))·√((L₀ + Φ)(κ₆L₀ + 2κ₇))`. The
  error part of `eq:menson2` costs `45.2836·√(x/V)/U ≤ 0.0139 ≤ κ₇/2` (`eq:curious` holds with
  `x/(VU²) ≤ 6/x^{1/3}`, `first_facts`).
* **`x/√U` term.** `S₁ ≤ 0.2096x/W` (`H₂ ≤ 2/π² ≤ 0.2026425` plus the error part),
  `√(log W/log(W/2q)) ≤ 1 + √(log 2q/log(W/2q))`, the scaling `W = 2qt` (`int_scale`), and
  `eq:notung` (`notung_all`, below) give `√ρ(x/√U)(2.58983 + 3.13543√r) ≤ √2κ₂√ρ(1 + 1.15√r)(x/√U)`.
* **`x/√V` term.** `8√(0.2096·1.0172) ≤ 3.6944 ≤ κ₉`.

## `eq:notung` (`notung_all`)

`∫_e^T dt/√(t log t) ≤ 2.3√(T/log T) + 0.2` for every `T ≥ e`, from the CITED range `[e, 2135.94]`
(`HC.NotungCited`, Helfgott's computation at his exact statement), the book's derivative argument
on `[2160, ∞)` (`log 2160 ≥ 23/3`, `notung_tail`), and the trivial bound on `[2135.94, 2160]`. The
book's threshold `T₀ = e^{23/3} = 2135.9497…` lies strictly above the cited range's end, so
neither half reaches across alone; the `+0.2` is absorbed by the `κ₁` slack above. No computation
of ours stands in for a proof step: the only numeric input is the cited one.

With `SecInt` (`TypeIISecInt.lean`) this leaves `Vinland1At` on `Menson2`, `Kraken`, `KastLarge`
and the cited `HC.KastCited`, `EB.RS62Thm13`, `HC.NotungCited` (`vinland1At_of_deep`).
-/

namespace Principia.Common.TernaryGoldbach.T2S

open MeasureTheory Set
open scoped Interval
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc

/-! ## (1) `eq:notung` for every `T ≥ e`, from the cited range -/

/-- `t ↦ t/log t` is non-decreasing on `[e, ∞)`. -/
theorem div_log_mono (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : 0 < b := by linarith
  have hla : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0]
    exact ha
  have hlb : 1 ≤ Real.log b := hla.trans (Real.log_le_log ha0 hab)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hlr : Real.log b ≤ Real.log a + (b / a - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    linarith
  have e1 : a * (b / a - 1) = b - a := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlr ha0.le]

/-- `log 2160 ≥ 23/3`. -/
theorem log_2160 : 23 / 3 ≤ Real.log 2160 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 1 ^ 23 < 2.7182818286 ^ 23 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h2 : Real.exp (23 / 3) ^ 3 = Real.exp 1 ^ 23 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h3 : Real.exp (23 / 3) ^ 3 < (2160 : ℝ) ^ 3 := by
    rw [h2]
    exact h1.trans (by norm_num)
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).mp h3 |>.le

/-- `log 2135.94 ≥ 7.6`. -/
theorem log_2135 : 7.6 ≤ Real.log 2135.94 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 1 ^ 38 < 2.7182818286 ^ 38 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h2 : Real.exp 7.6 ^ 5 = Real.exp 1 ^ 38 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h3 : Real.exp 7.6 ^ 5 < (2135.94 : ℝ) ^ 5 := by
    rw [h2]
    exact h1.trans (by norm_num)
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).mp h3 |>.le

/-- The integrand of `eq:notung` is continuous on `[e, ∞)`. -/
theorem notung_cont (a b : ℝ) (ha : Real.exp 1 ≤ a) :
    ContinuousOn (fun t : ℝ => 1 / Real.sqrt (t * Real.log t)) (Icc a b) := by
  have hpos : ∀ t ∈ Icc a b, 0 < t * Real.log t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) (ha.trans ht.1)
    have hl : 1 ≤ Real.log t := by
      rw [Real.le_log_iff_exp_le ht0]
      exact ha.trans ht.1
    positivity
  refine continuousOn_const.div ?_ fun t ht => (Real.sqrt_pos.mpr (hpos t ht)).ne'
  refine (ContinuousOn.mul continuousOn_id ?_).sqrt
  exact Real.continuousOn_log.mono fun t ht =>
    (lt_of_lt_of_le (Real.exp_pos 1) (ha.trans ht.1)).ne'

/-- **The derivative argument of `eq:notung`** (`minarcs.tex` 4307-4312): for `t ≥ 2160`
(`log t ≥ 23/3`), `1/√(t log t) ≤ (2.3√(t/log t))'`, so the integral over `[2160, T]` is at most
`2.3√(T/log T) − 2.3√(2160/log 2160)`. -/
theorem notung_tail (T : ℝ) (hT : 2160 ≤ T) :
    ∫ t in (2160 : ℝ)..T, 1 / Real.sqrt (t * Real.log t) ≤
      2.3 * Real.sqrt (T / Real.log T) - 2.3 * Real.sqrt (2160 / Real.log 2160) := by
  have he : Real.exp 1 ≤ 2160 := by
    have := Real.exp_one_lt_d9
    linarith
  have hl : ∀ t : ℝ, 2160 ≤ t → 23 / 3 ≤ Real.log t := fun t ht =>
    log_2160.trans (Real.log_le_log (by norm_num) ht)
  set g : ℝ → ℝ := fun t => 2.3 * Real.sqrt (t / Real.log t) with hg
  set g' : ℝ → ℝ := fun t => 2.3 * (((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) /
    (2 * Real.sqrt (t / Real.log t))) with hg'
  have hder : ∀ t : ℝ, 2160 ≤ t → HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := by linarith [hl t ht]
    have h1 : HasDerivAt (fun t : ℝ => t / Real.log t)
        ((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) t :=
      (hasDerivAt_id t).div (Real.hasDerivAt_log ht0.ne') hlt.ne'
    exact (h1.sqrt (div_pos ht0 hlt).ne').const_mul 2.3
  have hcont : ContinuousOn g (Icc 2160 T) := fun t ht =>
    (hder t ht.1).continuousAt.continuousWithinAt
  refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT hcont
    (fun t ht => (hder t ht.1.le).hasDerivWithinAt) ?_ ?_
  · exact (notung_cont 2160 T he).integrableOn_Icc
  · intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt := hl t ht.1.le
    have hl0 : 0 < Real.log t := by linarith
    have es : Real.sqrt (t * Real.log t) = Real.sqrt t * Real.sqrt (Real.log t) :=
      Real.sqrt_mul ht0.le _
    have ed : Real.sqrt (t / Real.log t) = Real.sqrt t / Real.sqrt (Real.log t) :=
      Real.sqrt_div' t hl0.le
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsl : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hl0
    have hsq : Real.sqrt (Real.log t) ^ 2 = Real.log t := Real.sq_sqrt hl0.le
    simp only [hg']
    rw [es, ed, mul_inv_cancel₀ ht0.ne', one_mul]
    rw [div_le_iff₀ (by positivity)]
    have key : Real.log t ≤ 1.15 * (Real.log t - 1) := by linarith
    have e2a : 2.3 * ((Real.log t - 1) / Real.log t ^ 2 /
        (2 * (Real.sqrt t / Real.sqrt (Real.log t)))) * (Real.sqrt t * Real.sqrt (Real.log t)) =
        1.15 * (Real.log t - 1) / Real.log t ^ 2 * Real.sqrt (Real.log t) ^ 2 := by
      field_simp
      ring
    have e2 : 2.3 * ((Real.log t - 1) / Real.log t ^ 2 /
        (2 * (Real.sqrt t / Real.sqrt (Real.log t)))) * (Real.sqrt t * Real.sqrt (Real.log t)) =
        1.15 * (Real.log t - 1) / Real.log t := by
      rw [e2a, hsq]
      field_simp
    rw [e2, le_div_iff₀ hl0]
    linarith

/-- **`eq:notung` on all of `[e, ∞)`, up to `+0.2`**, from the CITED range `[e, 2135.94]`
(`HC.NotungCited`), the derivative argument on `[2160, ∞)`, and the trivial bound
`24.06/√(2135.94·7.6) ≤ 0.2` on the gap `[2135.94, 2160]` (`T₀ = e^{23/3} = 2135.9497…` lies in
it, so neither half reaches across it alone). -/
theorem notung_all (hn : HC.NotungCited) (T : ℝ) (hT : Real.exp 1 ≤ T) :
    ∫ t in (Real.exp 1)..T, 1 / Real.sqrt (t * Real.log t) ≤
      2.3 * Real.sqrt (T / Real.log T) + 0.2 := by
  have he9 := Real.exp_one_lt_d9
  set f : ℝ → ℝ := fun t => 1 / Real.sqrt (t * Real.log t) with hf
  have hii : ∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → IntervalIntegrable f volume a b :=
    fun a b ha hab => (notung_cont a b ha).intervalIntegrable_of_Icc hab
  rcases le_or_gt T 2135.94 with h1 | h1
  · linarith [hn T hT h1]
  have hgap : ∀ b : ℝ, 2135.94 ≤ b → b ≤ 2160 → ∫ t in (2135.94 : ℝ)..b, f t ≤ 0.2 := by
    intro b hb1 hb2
    have hb : ∀ t ∈ Ι (2135.94 : ℝ) b, ‖f t‖ ≤ 0.00785 := by
      intro t ht
      rw [uIoc_of_le hb1] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hlt : 7.6 ≤ Real.log t := log_2135.trans (Real.log_le_log (by norm_num) ht.1.le)
      have hprod : 16233 ≤ t * Real.log t := by
        have := mul_le_mul ht.1.le hlt (by norm_num) ht0.le
        linarith
      have hs : 127.4 ≤ Real.sqrt (t * Real.log t) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        linarith
      simp only [hf]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
      have : 0.00785 * 127.4 ≤ 0.00785 * Real.sqrt (t * Real.log t) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [abs_of_nonneg (by linarith)] at this
    have h' := (Real.le_norm_self _).trans this
    have : 0.00785 * (b - 2135.94) ≤ 0.00785 * 24.06 :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hc := hn 2135.94 (by linarith) le_rfl
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hii (Real.exp 1) 2135.94 le_rfl (by linarith)) (hii 2135.94 T (by linarith) h1.le)
  rcases le_or_gt T 2160 with h2 | h2
  · have hmono : Real.sqrt (2135.94 / Real.log 2135.94) ≤ Real.sqrt (T / Real.log T) :=
      Real.sqrt_le_sqrt (div_log_mono _ _ (by linarith) h1.le)
    have := hgap T h1.le h2
    simp only [hf] at hsplit1 this hc
    rw [← hsplit1]
    linarith
  · have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (hii 2135.94 2160 (by linarith) (by norm_num)) (hii 2160 T (by linarith) h2.le)
    have hmono : Real.sqrt (2135.94 / Real.log 2135.94) ≤ Real.sqrt (2160 / Real.log 2160) :=
      Real.sqrt_le_sqrt (div_log_mono _ _ (by linarith) (by norm_num))
    have ht := notung_tail T h2.le
    have hg := hgap 2160 (by norm_num) le_rfl
    simp only [hf] at hsplit1 hsplit2 ht hg hc
    rw [← hsplit1, ← hsplit2]
    linarith

/-- **The first choice, numerically** (`u = x^{1/6} ≥ 8000`, `t = δ₀q ∈ [2, u²/3]`):
`U, V > 0`; `27q ≤ V`; `V ≤ x/U`; `3.5·x/U ≤ Q`; `2.0341·x/U ≤ 10⁻⁴x`;
`x/(VU²) ≤ 9.375·10⁻⁸` (`eq:curious`, with room); `x/(UV) = 2√t ≥ 2`. -/
theorem first_facts (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    0 < uA Y δ q ∧ 0 < vA Y ∧ 27 * (q : ℝ) ≤ vA Y ∧ vA Y ≤ Y / uA Y δ q ∧
      3.5 * (Y / uA Y δ q) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) ∧
      2.0341 * (Y / uA Y δ q) ≤ 0.0001 * Y ∧ Y / (vA Y * uA Y δ q ^ 2) ≤ 9.375e-8 ∧
      2 ≤ Y / (uA Y δ q * vA Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  set t := OC.dz δ * q with ht_def
  have ht2 : 2 ≤ t := by nlinarith
  have htx : t ≤ u ^ 2 / 3 := by
    have := dz_q_le δ _ q hdq hy
    rw [e13] at this
    exact this
  set s := Real.sqrt t with hs_def
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hss : s ^ 2 = t := Real.sq_sqrt (by linarith)
  have hsu : s ≤ u := by nlinarith
  have hU : uA Y δ q = u ^ 4 / (9 * s) := uA_eq Y δ q hY0
  have hV : vA Y = 9 / 2 * u ^ 2 := by
    unfold vA
    rw [e13]
  have hU0 : 0 < uA Y δ q := by
    rw [hU]
    positivity
  have hX : Y / uA Y δ q = 9 * s * u ^ 2 := by
    rw [hU, eY]
    field_simp
  have hu0 : 0 < u := by linarith
  refine ⟨hU0, by rw [hV]; positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV]
    rw [e13] at hy
    linarith
  · rw [hX, hV]
    nlinarith [sq_nonneg u]
  · rw [hX, e23]
    have : 31.5 * u ^ 3 ≤ 0.75 * u ^ 4 := by
      have h3 : 0 < u ^ 3 := by positivity
      nlinarith
    nlinarith [pow_pos hu0 2, pow_pos hu0 3]
  · rw [hX]
    nth_rw 1 [eY]
    have h3 : 0 < u ^ 3 := by positivity
    have : (8000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    nlinarith [pow_pos hu0 2]
  · rw [hV, hU, eY]
    have e : u ^ 6 / (9 / 2 * u ^ 2 * (u ^ 4 / (9 * s)) ^ 2) = 18 * t / u ^ 2 / u ^ 2 := by
      rw [← hss]
      field_simp
      ring
    rw [e, div_div, div_le_iff₀ (by positivity)]
    have : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
    nlinarith [pow_pos hu0 2]
  · rw [div_mul_eq_div_div, hX, hV]
    have e : 9 * s * u ^ 2 / (9 / 2 * u ^ 2) = 2 * s := by
      field_simp
    rw [e]
    linarith

/-! ## (3) Five integrals over `[V, X]` -/

theorem int_rsqrt (V X : ℝ) (hV : 0 < V) (hVX : V ≤ X) :
    ∫ W in V..X, 1 / Real.sqrt W ≤ 2 * Real.sqrt X := by
  have hd : ∀ W ∈ uIcc V X, HasDerivAt (fun W => 2 * Real.sqrt W) (1 / Real.sqrt W) W := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    have hW0 : 0 < W := lt_of_lt_of_le hV hW.1
    have := (Real.hasDerivAt_sqrt hW0.ne').const_mul 2
    refine this.congr_deriv ?_
    field_simp
  have hc : ContinuousOn (fun W : ℝ => 1 / Real.sqrt W) (uIcc V X) := by
    rw [uIcc_of_le hVX]
    exact continuousOn_const.div Real.continuous_sqrt.continuousOn fun W hW =>
      (Real.sqrt_pos.mpr (lt_of_lt_of_le hV hW.1)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  linarith [Real.sqrt_nonneg V]

theorem int_rsqrt3 (V X : ℝ) (hV : 0 < V) (hVX : V ≤ X) :
    ∫ W in V..X, 1 / (W * Real.sqrt W) ≤ 2 / Real.sqrt V := by
  have hd : ∀ W ∈ uIcc V X, HasDerivAt (fun W => -2 / Real.sqrt W) (1 / (W * Real.sqrt W)) W := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    have hW0 : 0 < W := lt_of_lt_of_le hV hW.1
    have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
    have := (hasDerivAt_const W (-2 : ℝ)).div (Real.hasDerivAt_sqrt hW0.ne') hs.ne'
    refine this.congr_deriv ?_
    have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
    rw [hsq]
    field_simp
    ring
  have hc : ContinuousOn (fun W : ℝ => 1 / (W * Real.sqrt W)) (uIcc V X) := by
    rw [uIcc_of_le hVX]
    exact continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      fun W hW => by
        have hW0 : 0 < W := lt_of_lt_of_le hV hW.1
        exact (mul_pos hW0 (Real.sqrt_pos.mpr hW0)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  have : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  have : 0 ≤ 2 / Real.sqrt X := by positivity
  have e : -2 / Real.sqrt X = -(2 / Real.sqrt X) := by ring
  have e2 : -2 / Real.sqrt V = -(2 / Real.sqrt V) := by ring
  linarith

theorem int_inv (V X : ℝ) (hV : 0 < V) (hVX : V ≤ X) :
    ∫ W in V..X, 1 / W = Real.log (X / V) :=
  integral_one_div_of_pos hV (by linarith)

/-- `∫_V^X dW/(W log(W/c)) = log log(X/c) − log log(V/c)` for `V/c > 1`. -/
theorem int_loglog (c V X : ℝ) (hc : 0 < c) (hV : 1 < V / c) (hVX : V ≤ X) :
    ∫ W in V..X, 1 / Real.log (W / c) / W =
      Real.log (Real.log (X / c)) - Real.log (Real.log (V / c)) := by
  have hV0 : 0 < V := by
    have := (one_lt_div hc).mp hV
    linarith
  have hpos : ∀ W ∈ uIcc V X, 0 < W ∧ 0 < Real.log (W / c) := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    have hW0 : 0 < W := lt_of_lt_of_le hV0 hW.1
    refine ⟨hW0, Real.log_pos (lt_of_lt_of_le hV ?_)⟩
    exact div_le_div_of_nonneg_right hW.1 hc.le
  have hd : ∀ W ∈ uIcc V X, HasDerivAt (fun W => Real.log (Real.log (W / c)))
      (1 / Real.log (W / c) / W) W := by
    intro W hW
    obtain ⟨hW0, hl⟩ := hpos W hW
    have h1 : HasDerivAt (fun W => W / c) (1 / c) W := (hasDerivAt_id W).div_const c
    have h2 := (h1.log (div_pos hW0 hc).ne').log hl.ne'
    convert h2 using 1
    field_simp
  have hcont : ContinuousOn (fun W => 1 / Real.log (W / c) / W) (uIcc V X) := by
    refine ContinuousOn.div (continuousOn_const.div ?_ fun W hW => (hpos W hW).2.ne')
      continuousOn_id fun W hW => (hpos W hW).1.ne'
    exact (Real.continuousOn_log.comp (continuousOn_id.div_const c) fun W hW =>
      (div_pos (hpos W hW).1 hc).ne')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable

/-- **The substitution `s = x/(WU)`**: `∫_V^X H(x/(WU))/W dW = ∫_1^{x/(UV)} H(s)/s ds`
(`X = x/U`), and the left integrand is integrable when `H` is on `[1, x/(UV)]`. -/
theorem int_subst (H : ℝ → ℝ) (x U V : ℝ) (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hVX : V ≤ x / U) (hH : IntervalIntegrable H volume 1 (x / (U * V))) :
    IntervalIntegrable (fun W => H (x / (W * U)) / W) volume V (x / U) ∧
      ∫ W in V..(x / U), H (x / (W * U)) / W = ∫ s in (1 : ℝ)..(x / (U * V)), H s / s := by
  set φ : ℝ → ℝ := fun W => x / (W * U) with hφ
  set φ' : ℝ → ℝ := fun W => -(x / U) / W ^ 2 with hφ'
  set g : ℝ → ℝ := fun s => H s / s with hg
  have hpos : ∀ W ∈ uIcc V (x / U), 0 < W := by
    intro W hW
    rw [uIcc_of_le hVX] at hW
    exact lt_of_lt_of_le hV hW.1
  have hcont : ContinuousOn φ (uIcc V (x / U)) :=
    continuousOn_const.div (continuousOn_id.mul continuousOn_const) fun W hW =>
      (mul_pos (hpos W hW) hU).ne'
  have hIoo : ∀ W ∈ Ioo (min V (x / U)) (max V (x / U)), 0 < W := by
    intro W hW
    rw [min_eq_left hVX] at hW
    exact lt_trans hV hW.1
  have hder : ∀ W ∈ Ioo (min V (x / U)) (max V (x / U)), HasDerivAt φ (φ' W) W := by
    intro W hW
    have hW0 := hIoo W hW
    have : HasDerivAt (fun W => x / U * W⁻¹) (x / U * (-(W ^ 2)⁻¹)) W :=
      (hasDerivAt_inv hW0.ne').const_mul (x / U)
    convert this using 1
    · ext W
      simp only [hφ]
      field_simp
    · simp only [hφ']
      field_simp
  have hneg : ∀ W ∈ Ioo (min V (x / U)) (max V (x / U)), φ' W ≤ 0 := by
    intro W hW
    have := hIoo W hW
    simp only [hφ']
    have : 0 < x / U := div_pos hx hU
    have : 0 < W ^ 2 := by positivity
    rw [neg_div]
    exact neg_nonpos.mpr (by positivity)
  have hφV : φ V = x / (U * V) := by simp only [hφ]; ring_nf
  have hφX : φ (x / U) = 1 := by
    simp only [hφ]
    field_simp
  have hfun : (fun W => H (x / (W * U)) / W) = fun W => -((g ∘ φ) W * φ' W) := by
    ext W
    simp only [hg, hφ, hφ', Function.comp]
    by_cases hW : W = 0
    · simp [hW]
    · field_simp
  have hgi : IntervalIntegrable g volume (φ V) (φ (x / U)) := by
    rw [hφV, hφX]
    have eg : g = fun s => H s * s⁻¹ := by
      ext s
      simp only [hg, div_eq_mul_inv]
    rw [eg]
    refine hH.symm.mul_continuousOn (ContinuousOn.inv₀ continuousOn_id fun s hs => ?_)
    have h1 : 1 ≤ x / (U * V) := by
      rw [le_div_iff₀ (mul_pos hU hV)]
      rw [le_div_iff₀ hU] at hVX
      linarith
    rw [uIcc_of_ge h1] at hs
    linarith [hs.1]
  have hint := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos hcont hder
    hneg).mpr hgi
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hint.neg
  · rw [hfun, intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos hcont hder hneg, hφV, hφX,
      intervalIntegral.integral_symm]
    simp only [hg, neg_neg]


/-! ## (4) The substitution `W = ct` in the `x/√U` term -/

/-- `∫_V^X W^{-1/2}√(ℓ/log(W/c)) dW = √c·√ℓ·∫_{V/c}^{X/c} dt/√(t log t)` for `V/c > 1`. -/
theorem int_scale (c ℓ V X : ℝ) (hc : 0 < c) (hV : 1 < V / c) (hVX : V ≤ X) :
    ∫ W in V..X, 1 / Real.sqrt W * Real.sqrt (ℓ / Real.log (W / c)) =
      Real.sqrt c * Real.sqrt ℓ * ∫ t in (V / c)..(X / c), 1 / Real.sqrt (t * Real.log t) := by
  set f : ℝ → ℝ := fun W => 1 / Real.sqrt W * Real.sqrt (ℓ / Real.log (W / c)) with hf
  have h := intervalIntegral.integral_comp_mul_left f (c := c) hc.ne' (a := V / c) (b := X / c)
  have e1 : c * (V / c) = V := by field_simp
  have e2 : c * (X / c) = X := by field_simp
  rw [e1, e2] at h
  have hVc : V / c ≤ X / c := div_le_div_of_nonneg_right hVX hc.le
  have hcongr : ∫ t in (V / c)..(X / c), f (c * t) =
      ∫ t in (V / c)..(X / c), c⁻¹ * (Real.sqrt c * Real.sqrt ℓ) *
        (1 / Real.sqrt (t * Real.log t)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hVc] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hV ht.1
    have ht0 : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos ht1
    have hcs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    simp only [hf]
    have e3 : c * t / c = t := by field_simp
    rw [e3, Real.sqrt_mul hc.le, Real.sqrt_div' ℓ hl.le, Real.sqrt_mul ht0.le]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsl : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hl
    have hcs2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
    field_simp
    rw [hcs2]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul] at h
  have hc0 : c ≠ 0 := hc.ne'
  rw [smul_eq_mul, mul_assoc] at h
  exact (mul_left_cancel₀ (inv_ne_zero hc0) h).symm

/-! ## (5) The pointwise bounds -/

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The `S₃` term (`eq:crudo` × `eq:negli`). -/
theorem ptC (s1 s3 Y W : ℝ) (hY : 0 < Y) (hW : 0 < W)
    (h1' : s1 ≤ 0.2096 * (Y / W)) (h3 : 0 ≤ s3) (h3' : s3 ≤ 1.0172 * Y) :
    Real.sqrt (s1 * s3) / W ≤ 0.4618 * Y / (W * Real.sqrt W) := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hle : Real.sqrt (s1 * s3) ≤ 0.4618 * Y / Real.sqrt W := by
    rw [Real.sqrt_le_left (by positivity)]
    have hp : s1 * s3 ≤ 0.2096 * (Y / W) * (1.0172 * Y) :=
      mul_le_mul h1' h3' h3 (by positivity)
    have e : (0.4618 * Y / Real.sqrt W) ^ 2 = 0.21325924 * Y ^ 2 / W := by
      rw [div_pow, hsq]
      ring
    rw [e]
    have e2 : 0.2096 * (Y / W) * (1.0172 * Y) = 0.21320512 * Y ^ 2 / W := by ring
    rw [e2] at hp
    have : 0.21320512 * Y ^ 2 / W ≤ 0.21325924 * Y ^ 2 / W :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg Y]) hW.le
    linarith
  calc Real.sqrt (s1 * s3) / W ≤ 0.4618 * Y / Real.sqrt W / W :=
        div_le_div_of_nonneg_right hle hW.le
    _ = 0.4618 * Y / (W * Real.sqrt W) := by
        field_simp

/-- The `x/√U` term (`eq:vivaldi`, before integration). -/
theorem ptB (s1 ρ Y W ℓ L : ℝ) (hY : 0 < Y) (hW : 0 < W) (hρ : 0 ≤ ρ) (hℓ : 0 ≤ ℓ)
    (hL : 0 < L) (h1' : s1 ≤ 0.2096 * (Y / W)) :
    Real.sqrt (s1 * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) / W ≤
      Real.sqrt (0.1048 * ρ * Y) * (1 + Real.sqrt (ℓ / L)) / Real.sqrt W := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  set r := Real.sqrt (ℓ / L) with hr
  have hr2 : r ^ 2 = ℓ / L := Real.sq_sqrt (div_nonneg hℓ hL.le)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hle : Real.sqrt (s1 * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) ≤
      Real.sqrt (0.1048 * ρ * Y) * (1 + r) * Real.sqrt W := by
    rw [Real.sqrt_le_left (by positivity)]
    have hb : 0 ≤ ρ * W ^ 2 * (L + ℓ) / (2 * L) := by positivity
    have hp : s1 * (ρ * W ^ 2 * (L + ℓ) / (2 * L)) ≤
        0.2096 * (Y / W) * (ρ * W ^ 2 * (L + ℓ) / (2 * L)) := mul_le_mul_of_nonneg_right h1' hb
    have e1 : 0.2096 * (Y / W) * (ρ * W ^ 2 * (L + ℓ) / (2 * L)) =
        0.1048 * ρ * Y * W * (1 + ℓ / L) := by
      field_simp
      ring
    have e2 : (Real.sqrt (0.1048 * ρ * Y) * (1 + r) * Real.sqrt W) ^ 2 =
        0.1048 * ρ * Y * W * (1 + r) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hsq]
      ring
    rw [e2]
    rw [e1] at hp
    have h0 : 0 ≤ 0.1048 * ρ * Y * W := by positivity
    have : 1 + ℓ / L ≤ (1 + r) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  calc Real.sqrt (s1 * (ρ * W ^ 2 * (L + ℓ) / (2 * L))) / W ≤
        Real.sqrt (0.1048 * ρ * Y) * (1 + r) * Real.sqrt W / W :=
        div_le_div_of_nonneg_right hle hW.le
    _ = Real.sqrt (0.1048 * ρ * Y) * (1 + r) / Real.sqrt W := by
        field_simp
        rw [hsq]

/-- The main term (`eq:soledad`, AM-GM in `β`, before integration). -/
theorem ptA (s1 P Y W φ R β : ℝ) (hY : 0 < Y) (hW : 0 < W) (hφ : 0 < φ) (hR : 0 < R)
    (hβ : 0 < β) (hP : 0 ≤ P) (h1' : s1 ≤ Y / W * P) :
    Real.sqrt (s1 * (Y * W * R / (8 * φ))) / W ≤
      Y / (4 * Real.sqrt φ) * (β * R / 2 + P / β) / W := by
  have hsφ : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  refine div_le_div_of_nonneg_right ?_ hW.le
  rw [Real.sqrt_le_left (by positivity)]
  have ha : 0 ≤ Y * W * R / (8 * φ) := by positivity
  have hp : s1 * (Y * W * R / (8 * φ)) ≤ Y / W * P * (Y * W * R / (8 * φ)) :=
    mul_le_mul_of_nonneg_right h1' ha
  have e1 : Y / W * P * (Y * W * R / (8 * φ)) = Y ^ 2 / (16 * φ) * (2 * P * R) := by
    field_simp
    ring
  have e2 : (Y / (4 * Real.sqrt φ) * (β * R / 2 + P / β)) ^ 2 =
      Y ^ 2 / (16 * φ) * (β * R / 2 + P / β) ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, hsq]
    ring
  rw [e2]
  rw [e1] at hp
  have amgm : 2 * P * R ≤ (β * R / 2 + P / β) ^ 2 := by
    have e3 : (β * R / 2 + P / β) ^ 2 = (β * R / 2 - P / β) ^ 2 + 2 * P * R := by
      field_simp
      ring
    rw [e3]
    nlinarith [sq_nonneg (β * R / 2 - P / β)]
  have hc : 0 ≤ Y ^ 2 / (16 * φ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left amgm hc]

/-! ## (6) `Vin1Calc`, PROVED from the cited `eq:notung` -/

/-- `√(Y/W)/U ≤ 3.062·10⁻⁴` on `[V, ∞)` from `x/(VU²) ≤ 9.375·10⁻⁸`. -/
theorem cur_le (Y U V W : ℝ) (hY : 0 < Y) (hU : 0 < U) (hV : 0 < V) (hVW : V ≤ W)
    (hcur : Y / (V * U ^ 2) ≤ 9.375e-8) : Real.sqrt (Y / W) / U ≤ 3.062e-4 := by
  have hW : 0 < W := by linarith
  rw [div_le_iff₀ hU, Real.sqrt_le_left (by positivity)]
  have h1 : Y / W ≤ Y / V := div_le_div_of_nonneg_left hY.le hV hVW
  have h2 : Y / V = Y / (V * U ^ 2) * U ^ 2 := by field_simp
  have h3 : Y / (V * U ^ 2) * U ^ 2 ≤ 9.375e-8 * U ^ 2 :=
    mul_le_mul_of_nonneg_right hcur (sq_nonneg U)
  nlinarith [sq_nonneg U]

/-- `2/π² ≤ 0.2026425`. -/
theorem two_div_pi_sq : 2 / Real.pi ^ 2 ≤ 0.2026425 := by
  have h := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]
  have h2 : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := by gcongr
  norm_num at h2
  linarith

/-- `log T / T ≤ 0.368` for `T > 0`. -/
theorem log_div_le (T : ℝ) (hT : 0 < T) : Real.log T / T ≤ 0.368 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hT (Real.exp_pos 1))
  rw [Real.log_div hT.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  have he : 2.7182 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  rw [div_le_iff₀ hT]
  have : T / Real.exp 1 ≤ T / 2.7182 := div_le_div_of_nonneg_left hT.le (by norm_num) he.le
  have : T / 2.7182 ≤ 0.368 * T := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- The bound function, expanded into its six integrable pieces. -/
theorem g_expand (Y φ β ℓ Lw Hv U W k : ℝ) (hW : 0 < W) (hφ : 0 < φ)
    (hβ : 0 < β) (hL : Lw ≠ 0) (hU : U ≠ 0) :
    Y / (4 * Real.sqrt φ) * (β * (1 + ℓ / Lw) / 2 + (Hv + 22.6418 * (Real.sqrt (Y / W) / U)) / β)
        / W + k * (1 + Real.sqrt (ℓ / Lw)) / Real.sqrt W + 0.4618 * Y / (W * Real.sqrt W) =
      Y / (4 * Real.sqrt φ) * (β / 2) * (1 / W) +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * (1 / Lw / W) +
      Y / (4 * Real.sqrt φ) * (1 / β) * (Hv / W) +
      (Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) + 0.4618 * Y) *
        (1 / (W * Real.sqrt W)) +
      k * (1 / Real.sqrt W) + k * (1 / Real.sqrt W * Real.sqrt (ℓ / Lw)) := by
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hsφ : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ
  rw [Real.sqrt_div' Y hW.le]
  field_simp
  ring

/-- The main term after integration: AM-GM at the optimal `β` gives `eq:valmont`. -/
theorem main_alg (Y φ U V L0 F ℓ β : ℝ) (hY : 0 < Y) (hφ : 0 < φ) (hL0 : 0 < L0) (hF : 0 ≤ F)
    (hℓ : 0 ≤ ℓ) (hcurV : Real.sqrt Y / U / Real.sqrt V ≤ 3.062e-4)
    (hβ : β = Real.sqrt (kap6 * L0 + 2 * kap7) / Real.sqrt (2 * (L0 + ℓ * F))) :
    4 * (Y / (4 * Real.sqrt φ) * (β / 2) * L0 +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * F +
      Y / (4 * Real.sqrt φ) * (1 / β) * (0.15107 * L0) +
      Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) * (2 / Real.sqrt V)) ≤
      Y / Real.sqrt (2 * φ) * Real.sqrt ((L0 + ℓ * F) * (kap6 * L0 + 2 * kap7)) := by
  set A' := L0 + ℓ * F with hA'
  set B' := kap6 * L0 + 2 * kap7 with hB'
  have hA0 : 0 < A' := by positivity
  have hB0 : 0 < B' := by
    simp only [hB', kap6, kap7]
    positivity
  have hβ0 : 0 < β := by
    rw [hβ]
    exact div_pos (Real.sqrt_pos.mpr hB0) (Real.sqrt_pos.mpr (by positivity))
  have hsφ : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ
  have hE : 22.6418 * Real.sqrt Y / U * (2 / Real.sqrt V) ≤ 2 * kap7 / 4 := by
    have e : 22.6418 * Real.sqrt Y / U * (2 / Real.sqrt V) =
        45.2836 * (Real.sqrt Y / U / Real.sqrt V) := by ring
    rw [e]
    simp only [kap7]
    linarith
  have hL : 0.15107 * L0 = kap6 * L0 / 4 := by simp only [kap6]; ring
  have step : 4 * (Y / (4 * Real.sqrt φ) * (β / 2) * L0 +
      Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * F +
      Y / (4 * Real.sqrt φ) * (1 / β) * (0.15107 * L0) +
      Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) * (2 / Real.sqrt V)) ≤
      Y / Real.sqrt φ * (β * A' / 2 + B' / 4 / β) := by
    have e : 4 * (Y / (4 * Real.sqrt φ) * (β / 2) * L0 +
        Y / (4 * Real.sqrt φ) * (β / 2 * ℓ) * F +
        Y / (4 * Real.sqrt φ) * (1 / β) * (0.15107 * L0) +
        Y / (4 * Real.sqrt φ) * (1 / β * 22.6418 * Real.sqrt Y / U) * (2 / Real.sqrt V)) =
        Y / Real.sqrt φ * (β * A' / 2 + (0.15107 * L0 +
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

/-- The `x/√U` term after integration (`eq:vivaldi` with `eq:notung`). -/
theorem b_alg (Y U ρ c ℓ X T : ℝ) (hY : 0 < Y) (hU : 0 < U) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hX : X = Y / U) (hT : T = X / c) (hT0 : 0 < T)
    (hlogT0 : 0 < Real.log T) :
    4 * (Real.sqrt (0.1048 * ρ * Y) * (2 * Real.sqrt X) +
      Real.sqrt (0.1048 * ρ * Y) * (Real.sqrt c * Real.sqrt ℓ *
        (2.3 * Real.sqrt (T / Real.log T) + 0.2))) ≤
      Real.sqrt 2 * kap2 * Real.sqrt ρ * (1 + 1.15 * Real.sqrt (ℓ / Real.log T)) *
        (Y / Real.sqrt U) := by
  have hX0 : 0 < X := by rw [hX]; positivity
  have hsX : Real.sqrt X = Real.sqrt Y / Real.sqrt U := by rw [hX]; exact Real.sqrt_div' Y hU.le
  have hsU : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hslT : 0 < Real.sqrt (Real.log T) := Real.sqrt_pos.mpr hlogT0
  have hcT : Real.sqrt c * Real.sqrt T = Real.sqrt X := by
    rw [← Real.sqrt_mul hc.le, hT]
    congr 1
    field_simp
  have hlt : Real.sqrt (Real.log T) / Real.sqrt T ≤ 0.6067 := by
    rw [← Real.sqrt_div' _ hT0.le, Real.sqrt_le_left (by norm_num)]
    have := log_div_le T hT0
    norm_num
    linarith
  set z := Real.sqrt (ℓ / Real.log T) with hz
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have ezl : Real.sqrt ℓ = z * Real.sqrt (Real.log T) := by
    rw [hz, Real.sqrt_div' ℓ hlogT0.le]
    field_simp
  have e0 : Real.sqrt (0.1048 * ρ * Y) = Real.sqrt 0.1048 * Real.sqrt ρ * Real.sqrt Y := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have eYU : Real.sqrt Y * Real.sqrt X = Y / Real.sqrt U := by
    rw [hsX]
    have := Real.mul_self_sqrt hY.le
    field_simp
    linarith
  have eT : Real.sqrt (T / Real.log T) = Real.sqrt T / Real.sqrt (Real.log T) :=
    Real.sqrt_div' T hlogT0.le
  have hcl : Real.sqrt c * Real.sqrt ℓ * (2.3 * Real.sqrt (T / Real.log T) + 0.2) ≤
      2.42134 * z * Real.sqrt X := by
    rw [eT, ezl, ← hcT]
    have e : Real.sqrt c * (z * Real.sqrt (Real.log T)) *
        (2.3 * (Real.sqrt T / Real.sqrt (Real.log T)) + 0.2) =
        z * (Real.sqrt c * Real.sqrt T) * (2.3 + 0.2 * (Real.sqrt (Real.log T) /
          Real.sqrt T)) := by
      field_simp
    rw [e]
    have h0 : 0 ≤ z * (Real.sqrt c * Real.sqrt T) := by positivity
    have : 2.3 + 0.2 * (Real.sqrt (Real.log T) / Real.sqrt T) ≤ 2.42134 := by linarith
    have := mul_le_mul_of_nonneg_left this h0
    linarith
  have h01 : Real.sqrt 0.1048 ≤ 0.323729 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs2 : 1.41421 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hkp : 0 ≤ Real.sqrt (0.1048 * ρ * Y) := Real.sqrt_nonneg _
  have hYU : 0 ≤ Y / Real.sqrt U := by positivity
  have hr : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hcl hkp
  have hcoef : Real.sqrt 0.1048 * (8 + 9.68536 * z) ≤ Real.sqrt 2 * kap2 * (1 + 1.15 * z) := by
    simp only [kap2]
    have : 0 ≤ Real.sqrt 0.1048 := Real.sqrt_nonneg _
    nlinarith
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hr) hYU
  have e4 : 4 * (Real.sqrt (0.1048 * ρ * Y) * (2 * Real.sqrt X) +
      Real.sqrt (0.1048 * ρ * Y) * (2.42134 * z * Real.sqrt X)) =
      Real.sqrt 0.1048 * (8 + 9.68536 * z) * Real.sqrt ρ * (Y / Real.sqrt U) := by
    rw [e0, ← eYU]
    ring
  calc _ ≤ 4 * (Real.sqrt (0.1048 * ρ * Y) * (2 * Real.sqrt X) +
          Real.sqrt (0.1048 * ρ * Y) * (2.42134 * z * Real.sqrt X)) := by linarith
    _ = Real.sqrt 0.1048 * (8 + 9.68536 * z) * Real.sqrt ρ * (Y / Real.sqrt U) := e4
    _ ≤ Real.sqrt 2 * kap2 * (1 + 1.15 * z) * Real.sqrt ρ * (Y / Real.sqrt U) := h2
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- One long proof assembling six integrals and three pointwise bounds; the default 200000
-- heartbeats run out in the final elaboration, not in any single tactic.
theorem vin1Calc_of (hn : HC.NotungCited) : Vin1Calc := by
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
  set B' := kap6 * L0 + 2 * kap7 with hB'
  have hA0 : 0 < A' := by positivity
  have hB0 : 0 < B' := by
    simp only [hB', kap6, kap7]
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
  have i3 : ∫ W in V..X, H (Y / (W * U)) / W ≤ 0.15107 * L0 := by
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
  have hmain := main_alg Y φ U V L0 (Real.log (1 + L0 / lV)) ℓ β hY0 hφ0 hL0pos
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
  have hvin : vin1 Y U V q = Y / Real.sqrt (2 * φ) * Real.sqrt (A' * B') +
      Real.sqrt 2 * kap2 * Real.sqrt ρ * (1 + 1.15 * Real.sqrt (ℓ / Real.log T)) *
        (Y / Real.sqrt U) + kap9 * (Y / Real.sqrt V) := by
    unfold vin1
    have eT2 : Y / (2 * U * q) = T := by
      simp only [hTdef, hXdef, hcdef]
      field_simp
    rw [eT2]
  rw [hvin]
  linarith [hmain, hB, hC]


/-- **`MPc.Vinland1At` from the deep links** (`SecInt` and `Vin1Calc` discharged). -/
theorem vinland1At_of_deep (hm : Menson2) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) (hn : HC.NotungCited) : Vinland1At :=
  vinland1At_of_rest hm hk hc hl h13 (vin1Calc_of hn)

end Principia.Common.TernaryGoldbach.T2S
