/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BandLimit
import Principia.Common.TernaryGoldbach.EasyBand

set_option autoImplicit false

/-!
# `BandSharp` PROVED: `|h₂₀₀(t) − h(t)| ≤ 2.24·10⁻⁴` for all `t > 0` (third-order IBP)

`BL.band_uniform` proved `|h₂₀₀ − h| ≤ 0.1185` by one integration by parts against `Si`. This
module takes the same route to third order: `band_bound`, `Bnd_le` give, for every `t > 0`,
`|h₂₀₀(t) − h(t)| ≤ B = 2.23795·10⁻⁴ ≤ 2.24·10⁻⁴` (`band_le`). Corollaries:

* `band_sharp` — the briefed target `∀ t > 0, |h₂₀₀(t) − h(t)| ≤ 2.7·10⁻⁴`;
* `l2_band` — `|η₊ − η∘|₂ ≤ 0.6657·2.7·10⁻⁴`, the form of `MajSp.Norms`'s third conjunct, via
  `l2_diff_sharp` (`(∫₀^∞ t²e^{−t²})^{1/2} = (√π/4)^{1/2} = 0.665669… ≤ 0.6657`);
* `bandSharp25` — `EN.BandSharp25` (`2.5·10⁻⁴`) holds, so `EN.NormsB` holds on Helfgott's weights
  (`normsB_proved`) and `EN.helfgottAt_band25` loses its band hypothesis (`helfgottAt_bs`; it
  still carries `MajSp.Reg`, which `e3d6e31b` measured FALSE for `η₊` — see its docstring).

## The identity (exact; `ibp3`, `window_le2`, `window_ge2`)

Write `u(y) = h(t/y)` and `D = s d/ds`. Then `y u' = −(Dh)(t/y)` (`u1`), `y (y u')' = (D²h)(t/y)`
(`u2`) and `u2' = −(D³h)(t/y)/y` (`du2`). On `y ≥ t/2` (i.e. `t/y ≤ 2`) `h = hP`, the
polynomial-exponential, so all three are smooth there; `h`'s kink in `h'''` at `s = 2` sits at the
window's end `y = t/2`. The kernel `F_H(y)/y` has three successive antiderivatives in `y`, one
family per side of `y = 1`:
* `vm`, `vp` (`BL`): `v' = F_H/y`;
* `M2m`, `M2p` `= G(∓200 log y)/(200π)`: `M₂' = v/y`, with `G(a) = cos a − a(π/2 − Si a)`,
  `G' = −(π/2 − Si)` (`hasDerivAt_Gk`);
* `M3m`, `M3p` `= ±Γ(∓200 log y)/(200²π)`: `M₃' = M₂/y`, with
  `Γ(a) = (a²(π/2 − Si a) − a cos a − sin a)/2 = −a²∫ₐ^∞ sin x/x³ dx`, `Γ' = −G`
  (`hasDerivAt_Gm`) — defined in closed form, so no improper integral of `G` is needed.

At `y = 1`: `vm − vp = 1`, `M2m = M2p`, and `M3m = M3p = 0` because `Γ(0) = 0`, so the third
integration by parts has NO boundary term there and the terms at `y = 1` collapse to `h(t)`. At
`y = t/2` everything vanishes (`h, Dh, D²h` vanish at `2`). Hence for `0 < t ≤ 2`, `A ≥ 1`,
`∫_{t/2}^A h(t/y)F_H(y)dy/y − h(t) = [boundary at A] − ∫_{t/2}^1 u2'·M3m − ∫_1^A u2'·M3p`,
and for `t ≥ 2` the same with the single window `[t/2, A] ⊂ [1, ∞)`.

## The bound (uniform in `t`; nothing is divided by `t`)

Pointwise AM-GM — Cauchy–Schwarz with a fixed weight `μ = 32·10⁻⁸/9` (`amgm_pt`) — and the kernel
majorant `Γ(a)² ≤ 16/(a+4)²` (`Gm_sq_le`, from `|Γ| ≤ 1/2` and `|Γ| ≤ 2/a`, i.e.
`|∫ₐ^∞ sin x/x³| ≤ 1/(2a²)` and `≤ 2/a³`):
`|u2'·M₃| ≤ (1/(2π))(μ·u2'²·y + (9/32)/(y(200|log y| + 4)²))`.
Both terms have explicit antiderivatives: `−F(t/y)`, where `F(s) = Q(s)e^{2s−1}` with
`Q' + 2Q = s q₂(s)²`, i.e. `F' = (D³h)²/s` (`Qn` is `32Q`, degree 15), and `Φ`, `Ψ`. Over the
window they sum to at most `B = (1/(2π))(μ(F(2) − F(0)) + (9/32)/400)` (`F` is nondecreasing on
`[0, ∞)`, `Fw_ge_zero`), where
`F(2) − F(0) = W₃ = ∫₀² (D³h)²/s ds = (13108701e⁻¹ − 208593e³)/32 = 19772.4748`.

## Deviation from the design (recorded)

The design split the kernel majorant `k₃ ≤ κ + (k₃ − κ)⁺` at `A₀ = 10` and needed three proved
numbers, `V₃ = ∫₀²|D³h|ds/s = 81.97`, `σ₃ = sup|D³h|` and `Cn₃`, for `2.43·10⁻⁴` with 11% margin.
(`σ₃` is `192e^{3/2} = 860.48`, attained at `s = 2⁻`; the design's `859.54` came from a grid that
stopped short of `2`.) The Cauchy–Schwarz form needs only `W₃` — the integral of a polynomial times
`e^{2s}` with NO absolute value, exact by one antiderivative — and `∫Γ²`, and reaches `2.238·10⁻⁴`
(17% under `2.7·10⁻⁴`). Same third-order identity; a different last inequality.

## Numbers (checked before any Lean: `scratchpad/bs3/check2.py`, `mellin.py`)

* At 51 values of `t` — `10⁻¹⁵, 10⁻¹², 10⁻⁹, 10⁻⁶, 10⁻³`, 42 more points of `[0.001, 2.1]`, and
  `2.0004, 2.5, 5, 100` — all of the following hold: the first-order form (`BL`'s) and this
  module's third-order identity agree to `≤ 4·10⁻²⁰`; the true third-order remainder
  `(1/π)∫|u'''||Γ|` is at most `4.4·10⁻⁵` (at `t ≈ 1.95`); the AM-GM chain at that `t` is at
  most `2.2366·10⁻⁴ ≤ B`; and `∫u2'²y = W₃` for every `t`. An independent Mellin-inversion value
  of `h₂₀₀ − h` (no `Si`, no integration by parts) matches at the 13 points compared.
* `|Γ|` against its majorants on `a ∈ [10⁻⁴, 10⁵]`: `max 2|Γ| = 0.768`, `max a|Γ|/2 = 0.49998`,
  `max |Γ|(a+4)/4 = 0.473` (each `≤ 1`); `Γ' = −G` and `G' = −(π/2 − Si)` to `10⁻³⁰`.
* `sup_t |h₂₀₀(t) − h(t)| = 1.138·10⁻⁵` (at `t ≈ 2.0004`), so `B` sits `~20×` above the truth.
-/

namespace Principia.Common.TernaryGoldbach.BS

open MeasureTheory Set Filter Real
open scoped Topology
open Principia.Common.SincIntegral (Si hasDerivAt_Si Si_neg Si_zero continuous_Si tendsto_Si
  integral_sinc_eq sinc_tail_ibp2 abs_div_le_inv tail_le_two_div integral_inv_cube)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## The kernel: `G` (second antiderivative) and `Γ` (third), and `Γ² ≤ 16/(a+4)²` -/

/-- `x · sinc x = sin x` for every real `x`. -/
theorem mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

/-- **`G(a) = cos a − a(π/2 − Si a)`**, the second antiderivative of the kernel. -/
noncomputable def Gk (a : ℝ) : ℝ := Real.cos a - a * (π / 2 - Si a)

/-- **`Γ(a) = (a²(π/2 − Si a) − a cos a − sin a)/2`**, the third antiderivative; it equals
`−a²∫ₐ^∞ sin x/x³ dx` (`gm_window`) and vanishes at `0`. -/
noncomputable def Gm (a : ℝ) : ℝ := (a ^ 2 * (π / 2 - Si a) - a * Real.cos a - Real.sin a) / 2

/-- `G' = −(π/2 − Si)`. -/
theorem hasDerivAt_Gk (a : ℝ) : HasDerivAt Gk (-(π / 2 - Si a)) a := by
  have h2 : HasDerivAt (fun x => π / 2 - Si x) (-Real.sinc a) a := (hasDerivAt_Si a).const_sub _
  have h := (Real.hasDerivAt_cos a).sub ((hasDerivAt_id' a).mul h2)
  refine h.congr_deriv ?_
  linarith [mul_sinc a]

/-- **`Γ' = −G`**. -/
theorem hasDerivAt_Gm (a : ℝ) : HasDerivAt Gm (-Gk a) a := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
  have h2 : HasDerivAt (fun x => π / 2 - Si x) (-Real.sinc a) a := (hasDerivAt_Si a).const_sub _
  have h := (((hsq.mul h2).sub ((hasDerivAt_id' a).mul (Real.hasDerivAt_cos a))).sub
    (Real.hasDerivAt_sin a)).div_const 2
  refine h.congr_deriv ?_
  have e : a ^ 2 * Real.sinc a = a * Real.sin a := by rw [sq, mul_assoc, mul_sinc]
  unfold Gk
  linear_combination (-1 / 2 : ℝ) * e

/-- `G(0) = 1`. -/
theorem Gk_zero : Gk 0 = 1 := by simp [Gk]

/-- `Γ(0) = 0`: the third integration by parts has no boundary term at `w = 0`. -/
theorem Gm_zero : Gm 0 = 0 := by simp [Gm]

/-- `d/dy (y³)⁻¹ = −3/y⁴`. -/
theorem hasDerivAt_inv_cube {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y ^ 3)⁻¹) (-3 / x ^ 4) x := by
  have h : HasDerivAt (fun y : ℝ => (y ^ 3)⁻¹) (-(↑3 * x ^ (3 - 1)) / (x ^ 3) ^ 2) x :=
    (hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx)
  refine h.congr_deriv ?_
  field_simp

/-- **One more integration by parts**: `∫ₐᵇ sin x/x³ = cos a/a³ − cos b/b³ − 3∫ₐᵇ cos x/x⁴`. -/
theorem sin_cube_ibp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sin x / x ^ 3 = Real.cos a / a ^ 3 - Real.cos b / b ^ 3
      - 3 * ∫ x in a..b, Real.cos x / x ^ 4 := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => HW.uIcc_pos ha (ha.trans_le hab) hx
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun y : ℝ => (y ^ 3)⁻¹) (-3 / x ^ 4) x :=
    fun x hx => hasDerivAt_inv_cube (hpos x hx).ne'
  have hv : ∀ x ∈ uIcc a b, HasDerivAt (fun y => -Real.cos y) (Real.sin x) x := fun x _ => by
    have h : HasDerivAt (fun y : ℝ => -Real.cos y) (-(-Real.sin x)) x := (Real.hasDerivAt_cos x).neg
    rwa [neg_neg] at h
  have hu' : IntervalIntegrable (fun x : ℝ => -3 / x ^ 4) volume a b :=
    (continuousOn_const.div (continuousOn_pow 4) fun x hx =>
      pow_ne_zero 4 (hpos x hx).ne').intervalIntegrable
  have hv' : IntervalIntegrable Real.sin volume a b := Real.continuous_sin.intervalIntegrable a b
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : ∫ x in a..b, Real.sin x / x ^ 3 = ∫ x in a..b, (x ^ 3)⁻¹ * Real.sin x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have e2 : ∫ x in a..b, -3 / x ^ 4 * -Real.cos x = 3 * ∫ x in a..b, Real.cos x / x ^ 4 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [e1, hIBP, e2]
  ring

/-- `∫ₐᵇ x⁻⁴ = ((a³)⁻¹ − (b³)⁻¹)/3` for `0 < a ≤ b`. -/
theorem integral_inv_pow4 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (x ^ 4)⁻¹ = ((a ^ 3)⁻¹ - (b ^ 3)⁻¹) / 3 := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => HW.uIcc_pos ha (ha.trans_le hab) hx
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun y : ℝ => (y ^ 3)⁻¹) (-3 / x ^ 4) x :=
    fun x hx => hasDerivAt_inv_cube (hpos x hx).ne'
  have hu' : IntervalIntegrable (fun x : ℝ => -3 / x ^ 4) volume a b :=
    (continuousOn_const.div (continuousOn_pow 4) fun x hx =>
      pow_ne_zero 4 (hpos x hx).ne').intervalIntegrable
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hu hu'
  have e : ∫ x in a..b, -3 / x ^ 4 = -3 * ∫ x in a..b, (x ^ 4)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [e] at hI
  linarith

/-- `|∫ₐᵇ sin x/x³| ≤ ((a²)⁻¹ − (b²)⁻¹)/2`. -/
theorem abs_sin_cube_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ x in a..b, Real.sin x / x ^ 3| ≤ ((a ^ 2)⁻¹ - (b ^ 2)⁻¹) / 2 := by
  have hpos : ∀ x ∈ Icc a b, 0 < x := fun x hx => ha.trans_le hx.1
  rw [← integral_inv_cube ha hab, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun x hx => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_div_le_inv (pow_pos (ha.trans hx.1) 3) (Real.abs_sin_le_one x)
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 3).inv₀ fun x hx => pow_ne_zero 3 (hpos x hx).ne'

/-- `|∫ₐᵇ cos x/x⁴| ≤ ((a³)⁻¹ − (b³)⁻¹)/3`. -/
theorem abs_cos_pow4_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ x in a..b, Real.cos x / x ^ 4| ≤ ((a ^ 3)⁻¹ - (b ^ 3)⁻¹) / 3 := by
  have hpos : ∀ x ∈ Icc a b, 0 < x := fun x hx => ha.trans_le hx.1
  rw [← integral_inv_pow4 ha hab, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun x hx => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_div_le_inv (pow_pos (ha.trans hx.1) 4) (Real.abs_cos_le_one x)
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 4).inv₀ fun x hx => pow_ne_zero 4 (hpos x hx).ne'

/-- **`Γ` on a window**: `a²(Si b − Si a) − a cos a − sin a = −a²cos b/b − a²sin b/b² −
2a²∫ₐᵇ sin x/x³` (two integrations by parts, `sinc_tail_ibp2`). -/
theorem gm_window {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a ^ 2 * (Si b - Si a) - a * Real.cos a - Real.sin a =
      -(a ^ 2 * (Real.cos b / b)) - a ^ 2 * (Real.sin b / b ^ 2)
        - 2 * a ^ 2 * ∫ x in a..b, Real.sin x / x ^ 3 := by
  have h1 := sinc_tail_ibp2 ha hab
  rw [integral_sinc_eq] at h1
  rw [h1]
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  field_simp
  ring

/-- The window majorant `|−a²cos b/b − a²sin b/b²| ≤ 2a²/b` for `b ≥ 1`. -/
theorem abs_bdry_le {a b : ℝ} (hb : 1 ≤ b) :
    |-(a ^ 2 * (Real.cos b / b)) - a ^ 2 * (Real.sin b / b ^ 2)| ≤ 2 * a ^ 2 * b⁻¹ := by
  have hb0 : 0 < b := by linarith
  have h1 := abs_div_le_inv hb0 (Real.abs_cos_le_one b)
  have h2 := abs_div_le_inv (pow_pos hb0 2) (Real.abs_sin_le_one b)
  have hbb : (b ^ 2)⁻¹ ≤ b⁻¹ := by
    rw [sq]
    exact inv_anti₀ hb0 (le_mul_of_one_le_left hb0.le hb)
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left e1.1 ha2, mul_le_mul_of_nonneg_left e1.2 ha2,
    mul_le_mul_of_nonneg_left e2.1 ha2, mul_le_mul_of_nonneg_left e2.2 ha2,
    mul_le_mul_of_nonneg_left hbb ha2]

/-- **The limit step**: if the window expression is `≤ c + 2a²/b` for all large `b`, then
`|2Γ(a)| ≤ c`. -/
theorem abs_two_gm_le {a c : ℝ}
    (hw : ∀ b : ℝ, max a 1 ≤ b →
      |a ^ 2 * (Si b - Si a) - a * Real.cos a - Real.sin a| ≤ c + 2 * a ^ 2 * b⁻¹) :
    |2 * Gm a| ≤ c := by
  have e : 2 * Gm a = a ^ 2 * (π / 2 - Si a) - a * Real.cos a - Real.sin a := by
    unfold Gm
    ring
  have hlim : Tendsto (fun b => |a ^ 2 * (Si b - Si a) - a * Real.cos a - Real.sin a|
      - 2 * a ^ 2 * b⁻¹) atTop (𝓝 (|2 * Gm a| - 2 * a ^ 2 * 0)) := by
    rw [e]
    exact (((((tendsto_Si.sub_const (Si a)).const_mul (a ^ 2)).sub_const _).sub_const _).abs).sub
      (tendsto_inv_atTop_zero.const_mul _)
  rw [mul_zero, sub_zero] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (max a 1)] with b hb
  linarith [hw b hb]

/-- **`|Γ(a)| ≤ 1/2`** for `a ≥ 0` (from `|∫ₐ^∞ sin x/x³| ≤ 1/(2a²)`). -/
theorem abs_Gm_le_half {a : ℝ} (ha : 0 ≤ a) : |Gm a| ≤ 1 / 2 := by
  rcases ha.eq_or_lt with h | ha'
  · rw [← h, Gm_zero, abs_zero]
    norm_num
  have h2 : |2 * Gm a| ≤ 1 := by
    refine abs_two_gm_le fun b hb => ?_
    have hab : a ≤ b := (le_max_left a 1).trans hb
    have hb1 : 1 ≤ b := (le_max_right a 1).trans hb
    rw [gm_window ha' hab]
    have hB := abs_bdry_le (a := a) hb1
    have hE := abs_sin_cube_le ha' hab
    have hpos : 0 ≤ (b ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg b)
    have hinv : a ^ 2 * (a ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 ha'.ne')
    have hE2 : |2 * a ^ 2 * ∫ x in a..b, Real.sin x / x ^ 3| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc 2 * a ^ 2 * |∫ x in a..b, Real.sin x / x ^ 3|
          ≤ 2 * a ^ 2 * (((a ^ 2)⁻¹ - (b ^ 2)⁻¹) / 2) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg a) hpos]
    calc |-(a ^ 2 * (Real.cos b / b)) - a ^ 2 * (Real.sin b / b ^ 2)
          - 2 * a ^ 2 * ∫ x in a..b, Real.sin x / x ^ 3|
        ≤ |-(a ^ 2 * (Real.cos b / b)) - a ^ 2 * (Real.sin b / b ^ 2)|
          + |2 * a ^ 2 * ∫ x in a..b, Real.sin x / x ^ 3| := abs_sub _ _
      _ ≤ 1 + 2 * a ^ 2 * b⁻¹ := by linarith
  rw [abs_mul, abs_two] at h2
  linarith

/-- **`|Γ(a)| ≤ 2/a`** for `a > 0` (one more integration by parts: `|∫ₐ^∞ sin x/x³| ≤ 2/a³`). -/
theorem abs_Gm_le_two_div {a : ℝ} (ha : 0 < a) : |Gm a| ≤ 2 / a := by
  have h2 : |2 * Gm a| ≤ 4 / a := by
    refine abs_two_gm_le fun b hb => ?_
    have hab : a ≤ b := (le_max_left a 1).trans hb
    have hb1 : 1 ≤ b := (le_max_right a 1).trans hb
    have hb0 : 0 < b := ha.trans_le hab
    rw [gm_window ha hab, sin_cube_ibp ha hab]
    have hB := abs_bdry_le (a := a) hb1
    have hC := abs_cos_pow4_le ha hab
    have h1 := abs_le.mp (abs_div_le_inv (pow_pos ha 3) (Real.abs_cos_le_one a))
    have h3 := abs_le.mp (abs_div_le_inv (pow_pos hb0 3) (Real.abs_cos_le_one b))
    have hC' := abs_le.mp hC
    have hpos : 0 ≤ (b ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hb0.le 3)
    have hE : |Real.cos a / a ^ 3 - Real.cos b / b ^ 3 - 3 * ∫ x in a..b, Real.cos x / x ^ 4| ≤
        2 * (a ^ 3)⁻¹ := by
      rw [abs_le]
      constructor <;> linarith
    have hinv : a ^ 2 * (a ^ 3)⁻¹ = a⁻¹ := by
      field_simp
    have hE2 : |2 * a ^ 2 * (Real.cos a / a ^ 3 - Real.cos b / b ^ 3
        - 3 * ∫ x in a..b, Real.cos x / x ^ 4)| ≤ 4 / a := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc 2 * a ^ 2 * |Real.cos a / a ^ 3 - Real.cos b / b ^ 3
            - 3 * ∫ x in a..b, Real.cos x / x ^ 4|
          ≤ 2 * a ^ 2 * (2 * (a ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hE (by positivity)
        _ = 4 / a := by
            rw [div_eq_mul_inv, ← hinv]
            ring
    calc |-(a ^ 2 * (Real.cos b / b)) - a ^ 2 * (Real.sin b / b ^ 2)
          - 2 * a ^ 2 * (Real.cos a / a ^ 3 - Real.cos b / b ^ 3
            - 3 * ∫ x in a..b, Real.cos x / x ^ 4)|
        ≤ |-(a ^ 2 * (Real.cos b / b)) - a ^ 2 * (Real.sin b / b ^ 2)|
          + |2 * a ^ 2 * (Real.cos a / a ^ 3 - Real.cos b / b ^ 3
            - 3 * ∫ x in a..b, Real.cos x / x ^ 4)| := abs_sub _ _
      _ ≤ 4 / a + 2 * a ^ 2 * b⁻¹ := by linarith
  rw [abs_mul, abs_two] at h2
  have e : 4 / a = 2 * (2 / a) := by ring
  linarith

/-- **The kernel majorant `Γ(a)² ≤ 16/(a+4)²`** for `a ≥ 0` (`|Γ| ≤ min(1/2, 2/a) ≤ 4/(a+4)`). -/
theorem Gm_sq_le {a : ℝ} (ha : 0 ≤ a) : Gm a ^ 2 ≤ 16 / (a + 4) ^ 2 := by
  have h4 : 0 < a + 4 := by linarith
  have hb : |Gm a| ≤ 4 / (a + 4) := by
    rcases le_total a 4 with h | h
    · refine (abs_Gm_le_half ha).trans ?_
      rw [le_div_iff₀ h4]
      linarith
    · have ha0 : 0 < a := by linarith
      refine (abs_Gm_le_two_div ha0).trans ?_
      rw [div_le_div_iff₀ ha0 h4]
      linarith
  have e : 16 / (a + 4) ^ 2 = (4 / (a + 4)) ^ 2 := by
    rw [div_pow]
    norm_num
  rw [e, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hb 2

/-- `|G(a)| ≤ 3` for `a ≥ 0` (`|π/2 − Si a| ≤ 2/a`). -/
theorem abs_Gk_le {a : ℝ} (ha : 0 ≤ a) : |Gk a| ≤ 3 := by
  rcases ha.eq_or_lt with h | ha'
  · rw [← h, Gk_zero]
    norm_num
  have h1 := tail_le_two_div ha'
  have h2 : |a * (π / 2 - Si a)| ≤ 2 := by
    rw [abs_mul, abs_of_pos ha']
    calc a * |π / 2 - Si a| ≤ a * (2 / a) := mul_le_mul_of_nonneg_left h1 ha'.le
      _ = 2 := by field_simp
  have h3 := Real.abs_cos_le_one a
  unfold Gk
  calc |Real.cos a - a * (π / 2 - Si a)| ≤ |Real.cos a| + |a * (π / 2 - Si a)| := abs_sub _ _
    _ ≤ 3 := by linarith

/-! ## The polynomial side: `D h`, `D² h`, `D³ h` on `[0, 2]`, extended as polynomials -/

/-- `q₁(s) = −s⁶ − 5s⁵ + 17s⁴ + 20s³ − 68s² + 32s`: `(s·h'(s))' = q₁(s)e^{s−1/2}` on `[0, 2]`. -/
noncomputable def q1 (s : ℝ) : ℝ :=
  -s ^ 6 - 5 * s ^ 5 + 17 * s ^ 4 + 20 * s ^ 3 - 68 * s ^ 2 + 32 * s

/-- `q₂(s) = −s⁷ − 12s⁶ − 13s⁵ + 105s⁴ + 12s³ − 172s² + 64s`: `(s·q₁(s)e^{s−1/2})' =
q₂(s)e^{s−1/2}`, so `(D³h)(s) = s·q₂(s)e^{s−1/2}` on `[0, 2]`. -/
noncomputable def q2 (s : ℝ) : ℝ :=
  -s ^ 7 - 12 * s ^ 6 - 13 * s ^ 5 + 105 * s ^ 4 + 12 * s ^ 3 - 172 * s ^ 2 + 64 * s

/-- `(Dh)(s) = s·h'(s)`, as the polynomial-exponential `s·hDP(s)` on all of `ℝ`. -/
noncomputable def D1P (s : ℝ) : ℝ := s * BL.hDP s

/-- `(D²h)(s) = s·q₁(s)e^{s−1/2}` on all of `ℝ`. -/
noncomputable def D2P (s : ℝ) : ℝ := s * q1 s * Real.exp (s - 1 / 2)

/-- `32·Q(s)`, where `Q' + 2Q = s·q₂²`, so `(Q(s)e^{2s−1})' = (D³h)(s)²/s`. -/
noncomputable def Qn (s : ℝ) : ℝ :=
  -13108701 + 26217402 * s - 26217402 * s ^ 2 + 17478268 * s ^ 3 - 8706366 * s ^ 4
    + 3341644 * s ^ 5 - 947908 * s ^ 6 + 313400 * s ^ 7 - 228910 * s ^ 8 + 70268 * s ^ 9
    + 33028 * s ^ 10 - 13784 * s ^ 11 - 4036 * s ^ 12 + 872 * s ^ 13 + 264 * s ^ 14 + 16 * s ^ 15

/-- **`F(s) = Q(s)e^{2s−1}`**, the antiderivative of `(D³h)(s)²/s = s q₂(s)² e^{2s−1}`. -/
noncomputable def Fw (s : ℝ) : ℝ := Qn s / 32 * (Real.exp (s - 1 / 2) * Real.exp (s - 1 / 2))

/-- `(c xⁿ⁺¹)' = c(n+1)xⁿ`. -/
theorem hd_pow (c s : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => c * x ^ (n + 1)) (c * ((n + 1) * s ^ n)) s := by
  simpa using (hasDerivAt_pow (n + 1) s).const_mul c

/-- `(p(x)e^{x−1/2})' = (p' + p)e^{x−1/2}`. -/
theorem hasDerivAt_mexp {p : ℝ → ℝ} {p' s : ℝ} (hp : HasDerivAt p p' s) :
    HasDerivAt (fun x => p x * Real.exp (x - 1 / 2)) ((p' + p s) * Real.exp (s - 1 / 2)) s := by
  have he : HasDerivAt (fun x => Real.exp (x - 1 / 2)) (Real.exp (s - 1 / 2)) s :=
    ((hasDerivAt_id' s).sub_const (1 / 2)).exp.congr_deriv (mul_one _)
  exact (hp.mul he).congr_deriv (by ring)

/-- `(D h)' = q₁ e^{s−1/2}`. -/
theorem hasDerivAt_D1P (s : ℝ) : HasDerivAt D1P (q1 s * Real.exp (s - 1 / 2)) s := by
  have h := hasDerivAt_mexp (((((hd_pow (-1) s 5).add (hd_pow 1 s 4)).add
    (hd_pow 12 s 3)).add (hd_pow (-28) s 2)).add (hd_pow 16 s 1))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · simp only [Pi.add_apply]
    unfold q1
    ring
  · simp only [Pi.add_apply]
    unfold D1P BL.hDP
    ring

/-- `(D² h)' = q₂ e^{s−1/2}`. -/
theorem hasDerivAt_D2P (s : ℝ) : HasDerivAt D2P (q2 s * Real.exp (s - 1 / 2)) s := by
  have h := hasDerivAt_mexp ((((((hd_pow (-1) s 6).add (hd_pow (-5) s 5)).add
    (hd_pow 17 s 4)).add (hd_pow 20 s 3)).add (hd_pow (-68) s 2)).add (hd_pow 32 s 1))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · simp only [Pi.add_apply]
    unfold q2
    ring
  · simp only [Pi.add_apply]
    unfold D2P q1
    ring

/-- **`F' = s q₂² e^{2s−1}`** (the identity `Q' + 2Q = s q₂²`). -/
theorem hasDerivAt_Fw (s : ℝ) :
    HasDerivAt Fw (s * q2 s ^ 2 * (Real.exp (s - 1 / 2) * Real.exp (s - 1 / 2))) s := by
  have h0 := hasDerivAt_const s (-13108701 : ℝ)
  have h1 := h0.add (hd_pow (26217402) s 0)
  have h2 := h1.add (hd_pow (-26217402) s 1)
  have h3 := h2.add (hd_pow (17478268) s 2)
  have h4 := h3.add (hd_pow (-8706366) s 3)
  have h5 := h4.add (hd_pow (3341644) s 4)
  have h6 := h5.add (hd_pow (-947908) s 5)
  have h7 := h6.add (hd_pow (313400) s 6)
  have h8 := h7.add (hd_pow (-228910) s 7)
  have h9 := h8.add (hd_pow (70268) s 8)
  have h10 := h9.add (hd_pow (33028) s 9)
  have h11 := h10.add (hd_pow (-13784) s 10)
  have h12 := h11.add (hd_pow (-4036) s 11)
  have h13 := h12.add (hd_pow (872) s 12)
  have h14 := h13.add (hd_pow (264) s 13)
  have h15 := h14.add (hd_pow (16) s 14)
  have he : HasDerivAt (fun x => Real.exp (x - 1 / 2)) (Real.exp (s - 1 / 2)) s :=
    ((hasDerivAt_id' s).sub_const (1 / 2)).exp.congr_deriv (mul_one _)
  have h := (h15.div_const 32).mul (he.mul he)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · simp only [Pi.add_apply, Pi.mul_apply]
    unfold q2
    ring
  · simp only [Pi.add_apply, Pi.mul_apply]
    unfold Fw Qn
    ring

/-- `F` is nondecreasing on `[0, ∞)`: `F(x) ≥ F(0)` for `x ≥ 0` (`F' ≥ 0` there). -/
theorem Fw_ge_zero {x : ℝ} (hx : 0 ≤ x) : Fw 0 ≤ Fw x := by
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun y _ => hasDerivAt_Fw y) (by
      apply Continuous.intervalIntegrable
      unfold q2
      fun_prop)
  have hn : 0 ≤ ∫ y in (0 : ℝ)..x,
      y * q2 y ^ 2 * (Real.exp (y - 1 / 2) * Real.exp (y - 1 / 2)) :=
    intervalIntegral.integral_nonneg hx fun y hy =>
      mul_nonneg (mul_nonneg hy.1 (sq_nonneg _)) (by positivity)
  linarith

/-! ## `u(y) = h(t/y)` and its `D`-derivatives in `y` -/

/-- `t/y` has derivative `−t/y²`. -/
theorem hasDerivAt_div {t y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => t / y) (-t / y ^ 2) y :=
  ((hasDerivAt_const y t).div (hasDerivAt_id' y) hy).congr_deriv (by ring)

/-- `−(Dh)(t/y) = y·u'(y)`. -/
noncomputable def u1 (t y : ℝ) : ℝ := -D1P (t / y)

/-- `(D²h)(t/y) = y·(y·u')'(y)`. -/
noncomputable def u2 (t y : ℝ) : ℝ := D2P (t / y)

/-- `u'(y)` for `u(y) = hP(t/y)`. -/
noncomputable def du0 (t y : ℝ) : ℝ := BL.hDP (t / y) * (-t / y ^ 2)

/-- The derivative of `u1 t`. -/
noncomputable def du1 (t y : ℝ) : ℝ := -(q1 (t / y) * Real.exp (t / y - 1 / 2) * (-t / y ^ 2))

/-- The derivative of `u2 t`: `−(D³h)(t/y)/y`. -/
noncomputable def du2 (t y : ℝ) : ℝ := q2 (t / y) * Real.exp (t / y - 1 / 2) * (-t / y ^ 2)

/-- `(hP(t/y))' = du0`. -/
theorem hasDerivAt_uP (t : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => BL.hP (t / y)) (du0 t y) y :=
  (BL.hasDerivAt_hP (t / y)).comp y (hasDerivAt_div hy)

/-- `(u1 t)' = du1`. -/
theorem hasDerivAt_u1 (t : ℝ) {y : ℝ} (hy : y ≠ 0) : HasDerivAt (u1 t) (du1 t y) y :=
  ((hasDerivAt_D1P (t / y)).comp y (hasDerivAt_div hy)).neg

/-- `(u2 t)' = du2`. -/
theorem hasDerivAt_u2 (t : ℝ) {y : ℝ} (hy : y ≠ 0) : HasDerivAt (u2 t) (du2 t y) y :=
  (hasDerivAt_D2P (t / y)).comp y (hasDerivAt_div hy)

/-- `y ↦ g(t/y)·(−t/y²)` is continuous on `(0, ∞)` for continuous `g`. -/
theorem contOn_chain (t : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun y => g (t / y) * (-t / y ^ 2)) (Ioi 0) := by
  have hne : ∀ y ∈ Ioi (0 : ℝ), y ≠ 0 := fun y hy => (mem_Ioi.mp hy).ne'
  exact (hg.comp_continuousOn (continuousOn_const.div continuousOn_id hne)).mul
    (continuousOn_const.div (continuousOn_pow 2) fun y hy => pow_ne_zero 2 (hne y hy))

/-- `du0 t` is continuous on `(0, ∞)`. -/
theorem contOn_du0 (t : ℝ) : ContinuousOn (du0 t) (Ioi 0) :=
  contOn_chain t (by unfold BL.hDP; fun_prop)

/-- `du1 t` is continuous on `(0, ∞)`. -/
theorem contOn_du1 (t : ℝ) : ContinuousOn (du1 t) (Ioi 0) :=
  (contOn_chain t (g := fun s => q1 s * Real.exp (s - 1 / 2)) (by unfold q1; fun_prop)).neg

/-- `du2 t` is continuous on `(0, ∞)`. -/
theorem contOn_du2 (t : ℝ) : ContinuousOn (du2 t) (Ioi 0) :=
  contOn_chain t (g := fun s => q2 s * Real.exp (s - 1 / 2)) (by unfold q2; fun_prop)

/-! ## The kernel's antiderivatives in `y`, on each side of `y = 1` -/

/-- `G(−200 log y)/(200π)`: `(M2m)' = vm/y`. -/
noncomputable def M2m (y : ℝ) : ℝ := Gk (-(200 * Real.log y)) / (π * 200)

/-- `G(200 log y)/(200π)`: `(M2p)' = vp/y`. -/
noncomputable def M2p (y : ℝ) : ℝ := Gk (200 * Real.log y) / (π * 200)

/-- `Γ(−200 log y)/(200²π)`: `(M3m)' = M2m/y`. -/
noncomputable def M3m (y : ℝ) : ℝ := Gm (-(200 * Real.log y)) / (π * 200 ^ 2)

/-- `−Γ(200 log y)/(200²π)`: `(M3p)' = M2p/y`. -/
noncomputable def M3p (y : ℝ) : ℝ := -(Gm (200 * Real.log y) / (π * 200 ^ 2))

/-- `(−200 log y)' = −200/y`. -/
theorem hasDerivAt_nlog {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => -(200 * Real.log y)) (-(200 * y⁻¹)) y :=
  ((Real.hasDerivAt_log hy.ne').const_mul 200).neg

/-- `(200 log y)' = 200/y`. -/
theorem hasDerivAt_plog {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => 200 * Real.log y) (200 * y⁻¹) y :=
  (Real.hasDerivAt_log hy.ne').const_mul 200

/-- `(M2m)' = vm/y`. -/
theorem hasDerivAt_M2m {y : ℝ} (hy : 0 < y) : HasDerivAt M2m (BL.vm y / y) y := by
  have h := ((hasDerivAt_Gk _).comp y (hasDerivAt_nlog hy)).div_const (π * 200)
  refine h.congr_deriv ?_
  unfold BL.vm
  rw [Si_neg]
  field_simp
  ring

/-- `(M2p)' = vp/y`. -/
theorem hasDerivAt_M2p {y : ℝ} (hy : 0 < y) : HasDerivAt M2p (BL.vp y / y) y := by
  have h := ((hasDerivAt_Gk _).comp y (hasDerivAt_plog hy)).div_const (π * 200)
  refine h.congr_deriv ?_
  unfold BL.vp
  field_simp
  ring

/-- `(M3m)' = M2m/y`. -/
theorem hasDerivAt_M3m {y : ℝ} (hy : 0 < y) : HasDerivAt M3m (M2m y / y) y := by
  have h := ((hasDerivAt_Gm _).comp y (hasDerivAt_nlog hy)).div_const (π * 200 ^ 2)
  refine h.congr_deriv ?_
  unfold M2m
  field_simp

/-- `(M3p)' = M2p/y`. -/
theorem hasDerivAt_M3p {y : ℝ} (hy : 0 < y) : HasDerivAt M3p (M2p y / y) y := by
  have h := (((hasDerivAt_Gm _).comp y (hasDerivAt_plog hy)).div_const (π * 200 ^ 2)).neg
  refine h.congr_deriv ?_
  unfold M2p
  field_simp

/-! ## The third-order integration by parts on a window -/

/-- **Three integrations by parts on `[p, q] ⊂ (0, ∞)`**, against any kernel family
`(v, M₂, M₃)` with `v' = F_H/y`, `M₂' = v/y`, `M₃' = M₂/y` (exact). -/
theorem ibp3 (t : ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (v M2 M3 : ℝ → ℝ)
    (hv : ∀ y, 0 < y → HasDerivAt v (HW.FH 200 y / y) y)
    (h2 : ∀ y, 0 < y → HasDerivAt M2 (v y / y) y)
    (h3 : ∀ y, 0 < y → HasDerivAt M3 (M2 y / y) y) :
    ∫ y in p..q, BL.hP (t / y) * (HW.FH 200 y / y) =
      (BL.hP (t / q) * v q - BL.hP (t / p) * v p) - (u1 t q * M2 q - u1 t p * M2 p)
        + (u2 t q * M3 q - u2 t p * M3 p) - ∫ y in p..q, du2 t y * M3 y := by
  have hsub : uIcc p q ⊆ Ioi 0 := HW.uIcc_pos hp (hp.trans_le hpq)
  have hpos : ∀ y ∈ uIcc p q, 0 < y := fun y hy => hsub hy
  have cv : ContinuousOn v (uIcc p q) := fun y hy =>
    (hv y (hpos y hy)).continuousAt.continuousWithinAt
  have c2 : ContinuousOn M2 (uIcc p q) := fun y hy =>
    (h2 y (hpos y hy)).continuousAt.continuousWithinAt
  have iF : IntervalIntegrable (fun y => HW.FH 200 y / y) volume p q :=
    (((HW.FH_contOn 200).mono hsub).div continuousOn_id fun y hy =>
      (hpos y hy).ne').intervalIntegrable
  have iv : IntervalIntegrable (fun y => v y / y) volume p q :=
    (cv.div continuousOn_id fun y hy => (hpos y hy).ne').intervalIntegrable
  have i2 : IntervalIntegrable (fun y => M2 y / y) volume p q :=
    (c2.div continuousOn_id fun y hy => (hpos y hy).ne').intervalIntegrable
  have ibp0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => hasDerivAt_uP t (hpos y hy).ne') (fun y hy => hv y (hpos y hy))
    ((contOn_du0 t).mono hsub).intervalIntegrable iF
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => hasDerivAt_u1 t (hpos y hy).ne') (fun y hy => h2 y (hpos y hy))
    ((contOn_du1 t).mono hsub).intervalIntegrable iv
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => hasDerivAt_u2 t (hpos y hy).ne') (fun y hy => h3 y (hpos y hy))
    ((contOn_du2 t).mono hsub).intervalIntegrable i2
  have e1 : ∫ y in p..q, du0 t y * v y = ∫ y in p..q, u1 t y * (v y / y) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : y ≠ 0 := (hpos y hy).ne'
    simp only [du0, u1, D1P]
    field_simp
  have e2 : ∫ y in p..q, du1 t y * M2 y = ∫ y in p..q, u2 t y * (M2 y / y) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : y ≠ 0 := (hpos y hy).ne'
    simp only [du1, u2, D2P]
    field_simp
  rw [ibp0, e1, ibp1, e2, ibp2]
  ring

/-! ## Cauchy–Schwarz, pointwise: AM-GM with the weight `μ = 32·10⁻⁸/9` -/

/-- The AM-GM weight `μ = 32·10⁻⁸/9`, chosen so that `16/(1.6·10⁹ μ) = 9/32`. -/
noncomputable def mu : ℝ := 32e-8 / 9

/-- `μ > 0`. -/
theorem mu_pos : 0 < mu := by
  unfold mu
  norm_num

/-- **AM-GM against the kernel majorant**: if `g² ≤ 16/D²` then
`|x||g|/(200²π) ≤ (1/(2π))(μx²y + (9/32)/(yD²))` for `y, D > 0`. -/
theorem amgm_pt {x g y D : ℝ} (hy : 0 < y) (hD : 0 < D) (hg : g ^ 2 ≤ 16 / D ^ 2) :
    |x| * |g| / (π * 200 ^ 2) ≤ 1 / (2 * π) * (mu * x ^ 2 * y + 9 / 32 / (y * D ^ 2)) := by
  have hπ := Real.pi_pos
  have hm := mu_pos
  have hc : 0 < 40000 * mu * y := by positivity
  have h1 : 2 * |x| * |g| * (40000 * mu * y) ≤ (40000 * mu * y) ^ 2 * x ^ 2 + g ^ 2 := by
    nlinarith [sq_nonneg (40000 * mu * y * |x| - |g|), sq_abs x, sq_abs g]
  have h2 : g ^ 2 * D ^ 2 ≤ 16 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < D ^ 2)).mp hg
    linarith
  have key : |x| * |g| ≤ 20000 * mu * y * x ^ 2 + g ^ 2 / (80000 * mu * y) := by
    have e : 20000 * mu * y * x ^ 2 + g ^ 2 / (80000 * mu * y) =
        ((40000 * mu * y) ^ 2 * x ^ 2 + g ^ 2) / (2 * (40000 * mu * y)) := by
      field_simp
      ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have h3 : g ^ 2 / (80000 * mu * y) ≤ 5625 / (y * D ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    unfold mu
    linarith [mul_le_mul_of_nonneg_left h2 hy.le]
  have e2 : 1 / (2 * π) * (mu * x ^ 2 * y + 9 / 32 / (y * D ^ 2)) * (π * 200 ^ 2) =
      20000 * mu * y * x ^ 2 + 5625 / (y * D ^ 2) := by
    field_simp
    ring
  rw [div_le_iff₀ (by positivity), e2]
  linarith

/-- `Φ(y) = −1/(200(200 log y + 4))`, an antiderivative of `1/(y(200 log y + 4)²)` on `y ≥ 1`. -/
noncomputable def Phi (y : ℝ) : ℝ := -(200 * (200 * Real.log y + 4))⁻¹

/-- `Ψ(y) = 1/(200(4 − 200 log y))`, an antiderivative of `1/(y(4 − 200 log y)²)` on `y ≤ 1`. -/
noncomputable def Psi (y : ℝ) : ℝ := (200 * (-(200 * Real.log y) + 4))⁻¹

/-- `Φ' = 1/(y(200 log y + 4)²)`. -/
theorem hasDerivAt_Phi {y : ℝ} (hy : 0 < y) (hD : 0 < 200 * Real.log y + 4) :
    HasDerivAt Phi (1 / (y * (200 * Real.log y + 4) ^ 2)) y := by
  have h := (((hasDerivAt_plog hy).add_const 4).const_mul 200).inv (by positivity)
  refine h.neg.congr_deriv ?_
  field_simp

/-- `Ψ' = 1/(y(4 − 200 log y)²)`. -/
theorem hasDerivAt_Psi {y : ℝ} (hy : 0 < y) (hD : 0 < -(200 * Real.log y) + 4) :
    HasDerivAt Psi (1 / (y * (-(200 * Real.log y) + 4) ^ 2)) y := by
  have h := (((hasDerivAt_nlog hy).add_const 4).const_mul 200).inv (by positivity)
  refine h.congr_deriv ?_
  field_simp

/-- The majorant's antiderivative on `y ≥ 1`: `(1/(2π))(−μF(t/y) + (9/32)Φ(y))`. -/
noncomputable def MP (t y : ℝ) : ℝ := 1 / (2 * π) * (mu * -Fw (t / y) + 9 / 32 * Phi y)

/-- The majorant's antiderivative on `y ≤ 1`: `(1/(2π))(−μF(t/y) + (9/32)Ψ(y))`. -/
noncomputable def MM (t y : ℝ) : ℝ := 1 / (2 * π) * (mu * -Fw (t / y) + 9 / 32 * Psi y)

/-- `(−F(t/y))' = u2'(y)²·y`. -/
theorem hasDerivAt_nFw (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => -Fw (t / y)) (du2 t y ^ 2 * y) y := by
  have h := ((hasDerivAt_Fw (t / y)).comp y (hasDerivAt_div hy.ne')).neg
  refine h.congr_deriv ?_
  unfold du2
  field_simp

/-- `(MP t)' = (1/(2π))(μ u2'² y + (9/32)/(y(200 log y + 4)²))`. -/
theorem hasDerivAt_MP (t : ℝ) {y : ℝ} (hy : 0 < y) (hD : 0 < 200 * Real.log y + 4) :
    HasDerivAt (MP t)
      (1 / (2 * π) * (mu * du2 t y ^ 2 * y + 9 / 32 / (y * (200 * Real.log y + 4) ^ 2))) y := by
  have h := (((hasDerivAt_nFw t hy).const_mul mu).add
    ((hasDerivAt_Phi hy hD).const_mul (9 / 32))).const_mul (1 / (2 * π))
  refine h.congr_deriv ?_
  ring

/-- `(MM t)' = (1/(2π))(μ u2'² y + (9/32)/(y(4 − 200 log y)²))`. -/
theorem hasDerivAt_MM (t : ℝ) {y : ℝ} (hy : 0 < y) (hD : 0 < -(200 * Real.log y) + 4) :
    HasDerivAt (MM t)
      (1 / (2 * π) * (mu * du2 t y ^ 2 * y + 9 / 32 / (y * (-(200 * Real.log y) + 4) ^ 2))) y := by
  have h := (((hasDerivAt_nFw t hy).const_mul mu).add
    ((hasDerivAt_Psi hy hD).const_mul (9 / 32))).const_mul (1 / (2 * π))
  refine h.congr_deriv ?_
  ring

/-! ## The remainder on each side of `y = 1` -/

/-- **The remainder on `[p, q] ⊂ [1, ∞)`**: `|∫ₚ^q u2'·M3p| ≤ MP(q) − MP(p)`. -/
theorem piece_p (t : ℝ) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    |∫ y in p..q, du2 t y * M3p y| ≤ MP t q - MP t p := by
  have hsub : Icc p q ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le one_pos (hp.trans hy.1)
  have hD : ∀ y ∈ Icc p q, 0 < 200 * Real.log y + 4 := fun y hy => by
    have := Real.log_nonneg (hp.trans hy.1)
    linarith
  have hd : ∀ y ∈ Icc p q, HasDerivAt (MP t)
      (1 / (2 * π) * (mu * du2 t y ^ 2 * y + 9 / 32 / (y * (200 * Real.log y + 4) ^ 2))) y :=
    fun y hy => hasDerivAt_MP t (hsub hy) (hD y hy)
  have hc : ContinuousOn (fun y => |du2 t y * M3p y|) (Icc p q) :=
    (((contOn_du2 t).mono hsub).mul fun y hy =>
      (hasDerivAt_M3p (hsub hy)).continuousAt.continuousWithinAt).abs
  refine (intervalIntegral.abs_integral_le_integral_abs hpq).trans ?_
  refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hpq
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (Ioo_subset_Icc_self hy)).hasDerivWithinAt) hc.integrableOn_Icc
    fun y hy => ?_
  have hy := Ioo_subset_Icc_self hy
  have hL : 0 ≤ 200 * Real.log y := by
    have := Real.log_nonneg (hp.trans hy.1)
    linarith
  have hb := amgm_pt (x := du2 t y) (hsub hy) (hD y hy) (Gm_sq_le hL)
  unfold M3p
  rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < π * 200 ^ 2),
    ← mul_div_assoc]
  exact hb

/-- **The remainder on `[p, q] ⊂ (0, 1]`**: `|∫ₚ^q u2'·M3m| ≤ MM(q) − MM(p)`. -/
theorem piece_m (t : ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ 1) :
    |∫ y in p..q, du2 t y * M3m y| ≤ MM t q - MM t p := by
  have hsub : Icc p q ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le hp hy.1
  have hL : ∀ y ∈ Icc p q, 0 ≤ -(200 * Real.log y) := fun y hy => by
    have := Real.log_nonpos (hsub hy).le (hy.2.trans hq)
    linarith
  have hD : ∀ y ∈ Icc p q, 0 < -(200 * Real.log y) + 4 := fun y hy => by
    have := hL y hy
    linarith
  have hd : ∀ y ∈ Icc p q, HasDerivAt (MM t)
      (1 / (2 * π) * (mu * du2 t y ^ 2 * y + 9 / 32 / (y * (-(200 * Real.log y) + 4) ^ 2))) y :=
    fun y hy => hasDerivAt_MM t (hsub hy) (hD y hy)
  have hc : ContinuousOn (fun y => |du2 t y * M3m y|) (Icc p q) :=
    (((contOn_du2 t).mono hsub).mul fun y hy =>
      (hasDerivAt_M3m (hsub hy)).continuousAt.continuousWithinAt).abs
  refine (intervalIntegral.abs_integral_le_integral_abs hpq).trans ?_
  refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hpq
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (Ioo_subset_Icc_self hy)).hasDerivWithinAt) hc.integrableOn_Icc
    fun y hy => ?_
  have hy := Ioo_subset_Icc_self hy
  have hb := amgm_pt (x := du2 t y) (hsub hy) (hD y hy) (Gm_sq_le (hL y hy))
  unfold M3m
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < π * 200 ^ 2), ← mul_div_assoc]
  exact hb

/-! ## The window `[t/2, A]`: exact identity, then the bound -/

/-- The boundary term at `A`: `|h(t/A)| + |(Dh)(t/A)| + |(D²h)(t/A)|` (it tends to `0`). -/
noncomputable def bd (t A : ℝ) : ℝ := |BL.hP (t / A)| + |D1P (t / A)| + |D2P (t / A)|

/-- **The uniform constant** `B = (1/(2π))(μ(F(2) − F(0)) + (9/32)/400)` (`= 2.23795·10⁻⁴`). -/
noncomputable def Bnd : ℝ := 1 / (2 * π) * (mu * (Fw 2 - Fw 0) + 9 / 32 * (1 / 400))

/-- `h(2) = 0`. -/
theorem hP_two : BL.hP 2 = 0 := by simp [BL.hP]

/-- `(Dh)(2) = 0`. -/
theorem D1P_two : D1P 2 = 0 := by simp [D1P, BL.hDP]

/-- `(D²h)(2) = 0`. -/
theorem D2P_two : D2P 2 = 0 := by norm_num [D2P, q1]

/-- `M2m(1) = M2p(1)`: the second antiderivative is continuous across `y = 1`. -/
theorem M2m_one : M2m 1 = M2p 1 := by simp [M2m, M2p]

/-- `M3m(1) = 0` (`Γ(0) = 0`). -/
theorem M3m_one : M3m 1 = 0 := by simp [M3m, Gm_zero]

/-- `M3p(1) = 0` (`Γ(0) = 0`). -/
theorem M3p_one : M3p 1 = 0 := by simp [M3p, Gm_zero]

/-- `|M2p(y)| ≤ 1` for `y ≥ 1` (`|G| ≤ 3`). -/
theorem abs_M2p_le {y : ℝ} (hy : 1 ≤ y) : |M2p y| ≤ 1 := by
  have hL : 0 ≤ 200 * Real.log y := by
    have := Real.log_nonneg hy
    linarith
  have h := abs_Gk_le hL
  have hpi := Real.pi_gt_three
  unfold M2p
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < π * 200), div_le_one (by positivity)]
  nlinarith

/-- `|M3p(y)| ≤ 1` for `y ≥ 1` (`|Γ| ≤ 1/2`). -/
theorem abs_M3p_le {y : ℝ} (hy : 1 ≤ y) : |M3p y| ≤ 1 := by
  have hL : 0 ≤ 200 * Real.log y := by
    have := Real.log_nonneg hy
    linarith
  have h := abs_Gm_le_half hL
  have hpi := Real.pi_gt_three
  unfold M3p
  rw [abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < π * 200 ^ 2),
    div_le_one (by positivity)]
  nlinarith

/-- `y ↦ h(t/y)F_H(y)/y` is continuous on `(0, ∞)`. -/
theorem contOn_integrand (t : ℝ) :
    ContinuousOn (fun y => BL.hP (t / y) * (HW.FH 200 y / y)) (Ioi 0) := by
  have hne : ∀ y ∈ Ioi (0 : ℝ), y ≠ 0 := fun y hy => (mem_Ioi.mp hy).ne'
  have cP : Continuous BL.hP := by
    unfold BL.hP
    fun_prop
  exact (cP.comp_continuousOn (continuousOn_const.div continuousOn_id hne)).mul
    ((HW.FH_contOn 200).div continuousOn_id hne)

/-- On `[t/2, ∞)`, `h(t/y) = hP(t/y)`, so the window integral may use the polynomial. -/
theorem window_conv {t A : ℝ} (ht : 0 < t) (hA : t / 2 ≤ A) :
    ∫ y in t / 2..A, HW.hFun (t / y) * HW.FH 200 y / y =
      ∫ y in t / 2..A, BL.hP (t / y) * (HW.FH 200 y / y) := by
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hA] at hy
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
  have hty : t / y ≤ 2 := by
    rw [div_le_iff₀ hy0]
    linarith [hy.1]
  rw [BL.hFun_eq_hP (div_nonneg ht.le hy0.le) hty, mul_div_assoc]

/-- **The window bound for `0 < t ≤ 2`**: the three integrations by parts on `[t/2, 1]` (kernel
family `vm, M2m, M3m`) and `[1, A]` (`vp, M2p, M3p`) are exact; `h(t)` comes out at `y = 1`, the
boundary terms at `t/2` vanish (`h, Dh, D²h` vanish at `2`), and the remainders are bounded. -/
theorem window_le2 {t A : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) (hA : 1 ≤ A) :
    |(∫ y in t / 2..A, HW.hFun (t / y) * HW.FH 200 y / y) - HW.hFun t| ≤ bd t A + Bnd := by
  have ht0 : 0 < t / 2 := by positivity
  have ht1 : t / 2 ≤ 1 := by linarith
  have hA0 : 0 < A := by linarith
  have e1 : t / (t / 2) = 2 := by field_simp
  have f1 : BL.hP (t / (t / 2)) = 0 := by rw [e1, hP_two]
  have f2 : u1 t (t / 2) = 0 := by
    unfold u1
    rw [e1, D1P_two, neg_zero]
  have f3 : u2 t (t / 2) = 0 := by
    unfold u2
    rw [e1, D2P_two]
  have i1 : IntervalIntegrable (fun y => BL.hP (t / y) * (HW.FH 200 y / y)) volume (t / 2) 1 :=
    ((contOn_integrand t).mono (HW.uIcc_pos ht0 one_pos)).intervalIntegrable
  have i2 : IntervalIntegrable (fun y => BL.hP (t / y) * (HW.FH 200 y / y)) volume 1 A :=
    ((contOn_integrand t).mono (HW.uIcc_pos one_pos hA0)).intervalIntegrable
  rw [window_conv ht (by linarith), ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    ibp3 t ht0 ht1 BL.vm M2m M3m (fun y hy => BL.hasDerivAt_vm hy) (fun y hy => hasDerivAt_M2m hy)
      (fun y hy => hasDerivAt_M3m hy),
    ibp3 t one_pos hA BL.vp M2p M3p (fun y hy => BL.hasDerivAt_vp hy)
      (fun y hy => hasDerivAt_M2p hy) (fun y hy => hasDerivAt_M3p hy),
    f1, f2, f3, BL.vm_one, BL.vp_one, M2m_one, M3m_one, M3p_one, div_one,
    BL.hFun_eq_hP ht.le ht2]
  have hIm := piece_m t ht0 ht1 le_rfl
  have hIp := piece_p t le_rfl hA
  have hb1 : |BL.hP (t / A) * BL.vp A| ≤ |BL.hP (t / A)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (BL.abs_vp_le_one hA)
  have hb2 : |u1 t A * M2p A| ≤ |D1P (t / A)| := by
    rw [abs_mul]
    unfold u1
    rw [abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_M2p_le hA)
  have hb3 : |u2 t A * M3p A| ≤ |D2P (t / A)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_M3p_le hA)
  have hM : MM t 1 - MM t (t / 2) + (MP t A - MP t 1) ≤ Bnd := by
    have hF := Fw_ge_zero (div_nonneg ht.le hA0.le)
    have hPsi : 0 ≤ Psi (t / 2) := by
      have := Real.log_nonpos ht0.le ht1
      unfold Psi
      exact inv_nonneg.mpr (by linarith)
    have hPhi : Phi A ≤ 0 := by
      have := Real.log_nonneg hA
      unfold Phi
      exact neg_nonpos.mpr (inv_nonneg.mpr (by linarith))
    have hPsi1 : Psi 1 = 1 / 800 := by
      unfold Psi
      rw [Real.log_one]
      norm_num
    have hPhi1 : Phi 1 = -(1 / 800) := by
      unfold Phi
      rw [Real.log_one]
      norm_num
    have inner : mu * (Fw 2 - Fw (t / A)) + 9 / 32 * (Psi 1 - Psi (t / 2) + Phi A - Phi 1) ≤
        mu * (Fw 2 - Fw 0) + 9 / 32 * (1 / 400) := by
      rw [hPsi1, hPhi1]
      nlinarith [mul_le_mul_of_nonneg_left hF mu_pos.le]
    have e : MM t 1 - MM t (t / 2) + (MP t A - MP t 1) = 1 / (2 * π) *
        (mu * (Fw 2 - Fw (t / A)) + 9 / 32 * (Psi 1 - Psi (t / 2) + Phi A - Phi 1)) := by
      unfold MM MP
      rw [div_one, e1]
      ring
    rw [e]
    unfold Bnd
    exact mul_le_mul_of_nonneg_left inner (by positivity)
  unfold bd
  have k1 := abs_le.mp hIm
  have k2 := abs_le.mp hIp
  have k3 := abs_le.mp hb1
  have k4 := abs_le.mp hb2
  have k5 := abs_le.mp hb3
  rw [abs_le]
  constructor <;> linarith

/-- **The window bound for `t ≥ 2`**: one piece `[t/2, A] ⊂ [1, ∞)`, `h(t) = 0`. -/
theorem window_ge2 {t A : ℝ} (ht2 : 2 ≤ t) (hA : t ≤ A) :
    |(∫ y in t / 2..A, HW.hFun (t / y) * HW.FH 200 y / y) - HW.hFun t| ≤ bd t A + Bnd := by
  have ht : 0 < t := by linarith
  have ht0 : 0 < t / 2 := by positivity
  have ht1 : 1 ≤ t / 2 := by linarith
  have htA : t / 2 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have e1 : t / (t / 2) = 2 := by field_simp
  have f1 : BL.hP (t / (t / 2)) = 0 := by rw [e1, hP_two]
  have f2 : u1 t (t / 2) = 0 := by
    unfold u1
    rw [e1, D1P_two, neg_zero]
  have f3 : u2 t (t / 2) = 0 := by
    unfold u2
    rw [e1, D2P_two]
  rw [window_conv ht htA, ibp3 t ht0 htA BL.vp M2p M3p (fun y hy => BL.hasDerivAt_vp hy)
      (fun y hy => hasDerivAt_M2p hy) (fun y hy => hasDerivAt_M3p hy),
    f1, f2, f3, HW.hFun_of_two_le ht2]
  have hIp := piece_p t ht1 htA
  have hb1 : |BL.hP (t / A) * BL.vp A| ≤ |BL.hP (t / A)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (BL.abs_vp_le_one hA1)
  have hb2 : |u1 t A * M2p A| ≤ |D1P (t / A)| := by
    rw [abs_mul]
    unfold u1
    rw [abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_M2p_le hA1)
  have hb3 : |u2 t A * M3p A| ≤ |D2P (t / A)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_M3p_le hA1)
  have hM : MP t A - MP t (t / 2) ≤ Bnd := by
    have hF := Fw_ge_zero (div_nonneg ht.le hA0.le)
    have hPhi : Phi A ≤ 0 := by
      have := Real.log_nonneg hA1
      unfold Phi
      exact neg_nonpos.mpr (inv_nonneg.mpr (by linarith))
    have hPhi2 : -(1 / 800) ≤ Phi (t / 2) := by
      have hl := Real.log_nonneg ht1
      unfold Phi
      rw [neg_le_neg_iff, one_div]
      exact inv_anti₀ (by norm_num) (by linarith)
    have inner : mu * (Fw 2 - Fw (t / A)) + 9 / 32 * (Phi A - Phi (t / 2)) ≤
        mu * (Fw 2 - Fw 0) + 9 / 32 * (1 / 400) := by
      nlinarith [mul_le_mul_of_nonneg_left hF mu_pos.le]
    have e : MP t A - MP t (t / 2) = 1 / (2 * π) *
        (mu * (Fw 2 - Fw (t / A)) + 9 / 32 * (Phi A - Phi (t / 2))) := by
      unfold MP
      rw [e1]
      ring
    rw [e]
    unfold Bnd
    exact mul_le_mul_of_nonneg_left inner (by positivity)
  unfold bd
  have k2 := abs_le.mp hIp
  have k3 := abs_le.mp hb1
  have k4 := abs_le.mp hb2
  have k5 := abs_le.mp hb3
  rw [abs_le]
  constructor <;> linarith

/-- **The window bound**, every `t > 0`, `A ≥ max(1, t)`. -/
theorem window {t A : ℝ} (ht : 0 < t) (hA1 : 1 ≤ A) (htA : t ≤ A) :
    |(∫ y in t / 2..A, HW.hFun (t / y) * HW.FH 200 y / y) - HW.hFun t| ≤ bd t A + Bnd := by
  rcases le_total t 2 with h | h
  · exact window_le2 ht h hA1
  · exact window_ge2 h htA

/-! ## The limit `A → ∞` and the constant -/

/-- **`|h₂₀₀(t) − h(t)| ≤ B` for every `t > 0`**, `B = (1/(2π))(μ(F(2) − F(0)) + (9/32)/400)`: the
window `[t/2, A]` exhausts `h_H`'s integral (which vanishes on `(0, t/2]`), and `bd t A → 0`. -/
theorem band_bound {t : ℝ} (ht : 0 < t) : |HW.hH 200 t - HW.hFun t| ≤ Bnd := by
  have ht0 : 0 < t / 2 := by positivity
  have hint : IntegrableOn (fun y => HW.hFun (t / y) * HW.FH 200 y / y) (Ioi (t / 2)) :=
    (HW.hH_integrable (by norm_num) ht).mono_set (Ioi_subset_Ioi ht0.le)
  have hH_eq : HW.hH 200 t = ∫ y in Ioi (t / 2), HW.hFun (t / y) * HW.FH 200 y / y := by
    unfold HW.hH HW.mconv
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi ht0.le) fun y hy => ?_
    obtain ⟨hy0, hy1⟩ := hy
    have hy0' : 0 < y := hy0
    have hya : y ≤ t / 2 := not_lt.mp hy1
    have h2 : 2 ≤ t / y := by
      rw [le_div_iff₀ hy0']
      linarith
    rw [HW.hFun_of_two_le h2]
    ring
  have hlim : Tendsto (fun A => ∫ y in t / 2..A, HW.hFun (t / y) * HW.FH 200 y / y) atTop
      (𝓝 (HW.hH 200 t)) := by
    rw [hH_eq]
    exact intervalIntegral_tendsto_integral_Ioi _ hint tendsto_id
  have hzero : Tendsto (bd t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun A : ℝ => t / A) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have cP : Continuous BL.hP := by
      unfold BL.hP
      fun_prop
    have c1 : Continuous D1P := by
      unfold D1P BL.hDP
      fun_prop
    have c2 : Continuous D2P := by
      unfold D2P q1
      fun_prop
    have h := ((((cP.tendsto 0).comp h1).abs.add ((c1.tendsto 0).comp h1).abs).add
      ((c2.tendsto 0).comp h1).abs)
    have e : |BL.hP 0| + |D1P 0| + |D2P 0| = 0 := by simp [BL.hP, D1P, BL.hDP, D2P]
    rw [e] at h
    exact h
  have hfin := ((hlim.sub_const (HW.hFun t)).abs).sub hzero
  rw [sub_zero] at hfin
  refine le_of_tendsto hfin ?_
  filter_upwards [eventually_ge_atTop (max t 1)] with A hA
  have h := window ht (le_of_max_le_right hA) (le_of_max_le_left hA)
  linarith

/-- **`B ≤ 2.24·10⁻⁴`** (`B = 2.23795·10⁻⁴`): `F(2) − F(0) = (13108701e⁻¹ − 208593e³)/32`, with
`2.7182818283 < e` and `π > 3.141592`. -/
theorem Bnd_le : Bnd ≤ 2.24e-4 := by
  have he1 := Real.exp_one_gt_d9
  have hpi := Real.pi_gt_d6
  have hpi0 := Real.pi_pos
  have hE3 : Real.exp (2 - 1 / 2) * Real.exp (2 - 1 / 2) = Real.exp 1 ^ 3 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    norm_num
  have hE0 : Real.exp (0 - 1 / 2) * Real.exp (0 - 1 / 2) = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    norm_num
  have hQ2 : Qn 2 = -208593 := by norm_num [Qn]
  have hQ0 : Qn 0 = -13108701 := by norm_num [Qn]
  have hcube : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  have hinv : (Real.exp 1)⁻¹ < (2.7182818283 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) he1
  have hL : 32e-8 / 9 * (-208593 / 32 * Real.exp 1 ^ 3 - -13108701 / 32 * (Real.exp 1)⁻¹) +
      9 / 32 * (1 / 400) ≤ 2.24e-4 * (2 * π) := by
    norm_num at hcube hinv ⊢
    linarith
  unfold Bnd Fw mu
  rw [hE3, hE0, hQ2, hQ0]
  calc 1 / (2 * π) * (32e-8 / 9 * (-208593 / 32 * Real.exp 1 ^ 3 - -13108701 / 32 *
        (Real.exp 1)⁻¹) + 9 / 32 * (1 / 400))
      ≤ 1 / (2 * π) * (2.24e-4 * (2 * π)) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 2.24e-4 := by field_simp

/-! ## The corollaries -/

/-- **The sharpest numeric form**: `|h₂₀₀(t) − h(t)| ≤ 2.24·10⁻⁴` for every `t > 0`. -/
theorem band_le : ∀ t : ℝ, 0 < t → |HW.hH 200 t - HW.hFun t| ≤ 2.24e-4 :=
  fun _ ht => (band_bound ht).trans Bnd_le

/-- **`band_sharp`: `|h₂₀₀(t) − h(t)| ≤ 2.7·10⁻⁴` for every `t > 0`**, by the third-order
integration by parts (`band_bound`, `Bnd_le`: `2.24·10⁻⁴`). -/
theorem band_sharp : ∀ t : ℝ, 0 < t → |HW.hH 200 t - HW.hFun t| ≤ 2.7e-4 :=
  fun _ ht => (band_bound ht).trans (Bnd_le.trans (by norm_num))

/-- **`EN.BandSharp25` holds** (`2.24·10⁻⁴ ≤ 2.5·10⁻⁴`). -/
theorem bandSharp25 : EN.BandSharp25 :=
  fun _ ht => (band_bound ht).trans (Bnd_le.trans (by norm_num))

/-- **For ANY `g` with `|g − h| ≤ c` on `t > 0`**: `|g·t·e^{−t²/2} − η∘|₂ ≤ 0.6657·c`, since
`|g·t·e^{−t²/2} − η∘|₂² ≤ c²∫₀^∞t²e^{−t²} = c²√π/4 ≤ 0.6657²c²` (`EN.l2_diff_of_unif` at the
sharper constant `(√π/4)^{1/2} = 0.665669…`). -/
theorem l2_diff_sharp (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ t : ℝ, 0 < t → |g t - HW.hFun t| ≤ c) :
    MajSp.l2 (fun t => g t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t) ≤ 0.6657 * c := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (g t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t) ^ 2 ≤
      c ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    intro t ht
    have e1 : g t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t =
        (g t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)) := by
      unfold HW.etaCirc
      ring
    have e2 : (t * Real.exp (-t ^ 2 / 2)) ^ 2 = t ^ 2 * Real.exp (-t ^ 2) := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have h1 : (g t - HW.hFun t) ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hg t ht) 2
    rw [e1, mul_pow, e2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _)
    (EN.integrable_t2_exp.const_mul (c ^ 2)) (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_const_mul, EN.int_t2_exp] at hI
  have hq := EN.sqrt_pi_quarter_le
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have h3 : c ^ 2 * (Real.sqrt Real.pi / 4) ≤ c ^ 2 * 0.44314 := mul_le_mul_of_nonneg_left hq hc2
  unfold MajSp.l2
  rw [Real.sqrt_le_left (mul_nonneg (by norm_num) hc)]
  nlinarith

/-- **The `L²` band-limiting error**: `|η₊ − η∘|₂ ≤ 0.6657·2.7·10⁻⁴`, the form of
`MajSp.Norms`'s third conjunct. -/
theorem l2_band : MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) ≤ 0.6657 * 2.7e-4 :=
  l2_diff_sharp (HW.hH 200) 2.7e-4 (by norm_num) band_sharp

/-- **`EN.NormsB` holds on Helfgott's own weights, unconditionally.** -/
theorem normsB_proved : EN.NormsB HW.etaPlus HW.etaStar HW.etaCirc :=
  EN.normsB_helf bandSharp25

/-- **`HelfgottAt 0.00032` on Helfgott's own weights, band hypothesis discharged**:
`EN.helfgottAt_band25` with `bandSharp25`. CAVEAT: it still carries that composition's other
links, among them `MajSp.Reg`, which the coordinator measured FALSE for `η₊` (`e3d6e31b`: `η₊''` is
not in `L²` near `0`), so as stated it is conditional on a false hypothesis until the chain is
re-routed through the planned `RegW`; the reusable part is `bandSharp25` / `band_sharp`. -/
theorem helfgottAt_bs (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (dj : EN.DrujalE HW.etaPlus)
    (cl : EN.CLowerE HW.etaCirc HW.etaStar)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  EN.helfgottAt_band25 pf hm rg nf dj cl bandSharp25 mn

end Principia.Common.TernaryGoldbach.BS
