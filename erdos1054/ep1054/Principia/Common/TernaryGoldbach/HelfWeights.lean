/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SmoothPP
import Principia.Common.TernaryGoldbach.SmoothCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

/-!
# Helfgott's two smoothing weights, defined faithfully, and link 0 of the smoothed spine

`Smooth.SupBounds ηp ηs` (link 0 of `Smoothed.lean`) is weight-specific, and the SAME weights must
later satisfy `CircleIdSmooth`, `MajorLowerSmooth` and `MinorUpperSmooth`, which are Helfgott's
own papers about HIS functions. A pair that merely meets the sup bounds (the constant `1` does,
`SmPP.supBounds_one`) is useless for the chain. This file defines the two weights exactly as
Helfgott does and proves what can be proved about their sup norms.

## The definitions (all as printed; map §2.4)

* `mconv f g t = ∫_{(0,∞)} f(t/y) g(y) dy/y` — multiplicative (Mellin) convolution, a Lebesgue
  integral over `Ioi 0` (majarcs `eq:dirich2`: `h_H(t) = ∫_0^∞ h(ty⁻¹) F_H(y) dy/y`).
* `eta2 t = 4 max(log 2 − |log 2t|, 0)` for `t > 0`, and `0` for `t ≤ 0` (minarcs `eq:eqeta`;
  support `[1/4, 1]`). `phi t = t² e^{−t²/2}`. `etaStar t = (η₂ ∗_M φ)(49 t)` (ternvin §7).
* `hFun t = t²(2−t)³e^{t−1/2}` on `[0,2]`, `0` elsewhere (majarcs `eq:hortor`).
* `FH H y = (H/π)·sinc(H log y)`, i.e. `sin(H log y)/(π log y)` for `y > 0, y ≠ 1` (`FH_eq`), with
  the removable singularity filled by `H/π` (`FH_one`), which IS the limit (`FH_tendsto`).
* `hH H = hFun ∗_M FH H`, `etaPlus t = h_200(t)·t·e^{−t²/2}` (majarcs `eq:patra2`).
* `etaCirc t = h(t)·t·e^{−t²/2}`, the UNtruncated weight; `etaCirc_eq` shows it is Helfgott's
  `η_∘(t) = t³(2−t)³e^{−(t−1)²/2}` (majarcs `eq:cleo2`).

**Nonpositive arguments.** Helfgott's weights live on `(0,∞)`. Here `eta2` and `hFun` vanish on
`(−∞,0]`, so `etaStar` and `etaPlus` vanish there too (`etaStar_of_nonpos`, `etaPlus_of_nonpos`) —
proved, not assumed, and consistent with `S_η(α,x) = ∑ Λ(n)η(n/x)` only ever sampling `n/x ≥ 0`.
`SupBounds` quantifies over ALL real `u`, and every bound below is for all real `u`.

## (1) `η_*`: DONE, unconditionally

`etaStar_le : ∀ t, |etaStar t| ≤ 1.414`, by Helfgott's one-line Hölder bound (7.19) `eq:macadam`:
`|η₂ ∗_M φ|_∞ ≤ |η₂(t)/t|₁·|φ|_∞ = 4(log 2)²·(2/e) = 1.4139903 ≤ 1.414`. The `L¹` norm is computed
exactly by the fundamental theorem of calculus on `[s,2s]` and `[2s,4s]` (`int_lo`, `int_hi`,
`int_eta2`: `2(log 2)² + 2(log 2)²`); `max φ = 2/e` is `phi_le` (from `x + 1 ≤ eˣ`), attained at
`√2` (`phi_at_sqrt_two`). **Not the zero function**: `etaStar_pos` proves `η_*(t) > 0` for EVERY
`t > 0` (the integrand is continuous and positive on `(49t, 196t)`).

## (2) `η₊`: defined faithfully; the sup bound REDUCED to one named analytic statement

`EtaPlusSup : ∀ u, |etaPlus u| ≤ 1.079955` is not proved in THIS file; it is proved downstream as
`BL.etaPlusSup` (`BandLimit.lean`, from `BL.band_uniform`). What this file proves:

* **the easy half**, `etaCirc_le : ∀ t, |h(t)·t·e^{−t²/2}| ≤ 1`, sharp (`etaCirc_one`), via
  `t(2−t) = 1 − (t−1)² ∈ [0,1]` on `[0,2]`;
* **the non-junk check**, `hH_integrable`: for `t > 0` the integrand of `h_H(t)` is Lebesgue
  integrable on `(0,∞)` (zero for `y ≤ t/2`, `O(y⁻³)` beyond), so `hH` is Helfgott's integral and
  not Mathlib's junk `0` — without this `EtaPlusSup` could hold vacuously;
* **the reduction to one uniform analytic bound**: `etaPlusSup_of_band : BandUniform →
  EtaPlusSup`, where `BandUniform : ∀ t > 0, |h_200(t) − h(t)| ≤ 0.13`, through `jorat_unif`
  (for ANY `g`): `|η₊|_∞ ≤ |η_∘|_∞ + |h − h_H|_∞·|t e^{−t²/2}|_∞ ≤ 1 + 0.13·e^{−1/2} = 1.07885`.

**HELFGOTT'S OWN ROUTE IS BROKEN, AND THIS FILE ONCE TRANSCRIBED IT.** majarcs App. B.5 bounds
`|(h − h_H)/t|_∞` (`eq:havana`) and multiplies by `|t²e^{−t²/2}|_∞ = 2/e` (`eq:jorat`). The first
version of this file stated that as `Havana : ∀ t > 0, |h_200(t) − h(t)| ≤ t·bandConst`, a
faithful transcription — and **it is false**: `h_H(t)` decays only like `1/|log t|` as `t → 0`,
so `|h_H − h|/t → ∞` (`72×` the bound at `t = 10⁻⁹`; details on `BandUniform`). Every theorem
proved from it was vacuous; they have been removed. Helfgott's CONCLUSION `|η₊|_∞ ≤ 1.079955` is
true (the sup is `≈ 1.00000007`); so is `BandUniform`, numerically, with slack `~10⁴`
(`sup |h_H − h| = 1.138·10⁻⁵`, at `t ≈ 2.0004`). The same `/t` factor feeds his `eq:rasal`,
`eq:dalida`, `eq:gobmark` and `eq:shchedrin` (the sup norms of `η₊·log t`, `η₊/t`, `η₊·t`), whose
conclusions are therefore unproved by his argument, though numerically they look true.
`jorat`, `bandConst`, `malgache`, `sazar` and `plus_const_le` are kept: they certify Helfgott's
App. B.5 arithmetic, which is correct.

**`BandUniform` is PROVED downstream**, as `BL.band_uniform` (`BandLimit.lean`, `569323f2`), with
the constant `0.1185`, by integration by parts against `Si` on BOTH halves with the `w < 0` factor
bounded correctly (total variation of `y ↦ h(t/y)`, which is `2e^{1/2}` for every `t`). The
Dirichlet integral it needs was PORTED from PrimeNumberTheoremAnd (`Common/SincIntegral.lean`);
Mathlib does not have it. No Mellin inversion was needed.

**Every new `Prop` constrains.** `EtaPlusSup` and `BandUniform` are about FIXED functions shown to
be genuine integrals (`hH_integrable`); under `BandUniform`, `η₊(1) > 0` (`etaPlus_one_pos`), so
the obligation cannot be met by a degenerate `η₊`; and `plusSup_tight` shows the `1.079955` bound
already fails for `1.08·η_∘`, i.e. it is a real constraint on shape. The parametric hypotheses of
`jorat` and `jorat_unif` are discharged once by `g = h` itself (`jorat_self`, `jorat_unif_self`).

## (3) The reduction

`supBounds_helf : EtaPlusSup → Smooth.SupBounds etaPlus etaStar` (general form `supBounds_of`,
discharged once by the real weight `η_∘`: `supBounds_circ`), and the chain
`cite_helf : PlattGRH → EtaPlusSup → CircleIdSmooth etaPlus etaStar → MajorLowerSmooth etaPlus
etaStar → MinorUpperSmooth etaPlus etaStar → Cite_Helfgott_weighted` via `SmPP.cite5_no_summ`;
`cite_band` is the same with `BandUniform` in place of `EtaPlusSup`.

## Numbers (mpmath, 40 digits), all clearing

* `4(log 2)²(2/e) = 1.41399029015 ≤ 1.414` (margin `9.7·10⁻⁶`); with the Lean bounds
  `log 2 < 0.6931471808`, `e > 2.7182818283` it is `1.41399029122`.
* `∫_0^∞ η₂(t) dt/t = 1.92181205567 = 4(log 2)²`. `max φ = φ(√2) = 2/e = 0.73575888234`. The true
  `|η_*|_∞ ≈ 1.2267` (at `49t ≈ 0.66`), so `1.414` is Helfgott's bound, not the truth.
* `|η_∘|_∞ = η_∘(1) = 1`. `|h'|_∞ = 2.80582037967 at t = 1.48777169` (Helfgott: `2.805820379671`).
* `(2/e)·2.80582038 = 2.0644072668 ≤ 2.06440727` (margin `3.2·10⁻⁹`; Lean: `e > 2.7182818283`).
* `1 + 2.06440727(1 + (4/π) log 200)/200 = 1.07995477424 ≤ 1.079955` (margin `2.26·10⁻⁷`); Lean uses
  `π > 3.141592` and `log 200 < 5.29832` (`log_200_lt`, truth `5.2983174`; allowed `5.2983334`).

## A transcription error in the proof map (harmless here)

Map §2.4 (and ternvin §7's display, as extracted) writes `η₁ = 2·I_{[−1/2,1/2]}` with
`η₂ = η₁ ∗_M η₁`. Under MULTIPLICATIVE convolution that is wrong: restricted to `(0,∞)` it is
`2·I_{(0,1/2]}`, whose self-convolution is `4 log(1/(4t))` on `(0,1/4]` — unbounded, and not `η₂`.
Helfgott's own introduction (ternvin §1: "`η₂ = (2I_{[1/2,1]}) ∗_M (2I_{[1/2,1]})`") has the right
factor `η₁ = 2·I_{[1/2,1]}`, whose self-convolution IS the closed form (checked at `t = 0.3, 0.5,
0.7, 0.9` to 40 digits). This file uses the closed form, so the chain is unaffected.
-/

namespace Principia.Common.TernaryGoldbach.HW

open MeasureTheory Set

/-! ## The Mellin convolution and `η_*` -/

/-- **Multiplicative (Mellin) convolution** `(f ∗_M g)(t) = ∫_0^∞ f(t/y) g(y) dy/y`, a Lebesgue
integral over `(0,∞)` (majarcs `eq:dirich2`). -/
noncomputable def mconv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f (t / y) * g y / y

/-- **`η₂(t) = 4 max(log 2 − |log 2t|, 0)`** (minarcs `eq:eqeta`), support `[1/4, 1]`; set to `0`
for `t ≤ 0`, where Helfgott's weights are not defined. -/
noncomputable def eta2 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

/-- **`φ(t) = t² e^{−t²/2}`** (ternvin §7). -/
noncomputable def phi (t : ℝ) : ℝ := t ^ 2 * Real.exp (-t ^ 2 / 2)

/-- **Helfgott's `η_*(t) = (η₂ ∗_M φ)(κt)`, `κ = 49`** (ternvin §7). -/
noncomputable def etaStar (t : ℝ) : ℝ := mconv eta2 phi (49 * t)

/-- `η₂ ≥ 0`. -/
theorem eta2_nonneg (t : ℝ) : 0 ≤ eta2 t := by
  unfold eta2
  split_ifs
  · exact mul_nonneg (by norm_num) (le_max_right _ _)
  · exact le_refl 0

/-- `η₂` vanishes on `(−∞, 0]` (by definition). -/
theorem eta2_of_nonpos {t : ℝ} (ht : t ≤ 0) : eta2 t = 0 := by
  simp [eta2, not_lt.mpr ht]

/-- `η₂` vanishes on `[1, ∞)`. -/
theorem eta2_of_one_le {t : ℝ} (ht : 1 ≤ t) : eta2 t = 0 := by
  have h0 : 0 < t := by linarith
  have hl : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
  have hle : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by linarith [le_abs_self (Real.log (2 * t))]
  simp [eta2, h0, max_eq_right hle]

/-- `η₂` vanishes on `(0, 1/4]`. -/
theorem eta2_of_le_quarter {t : ℝ} (h0 : 0 < t) (ht : t ≤ 1 / 4) : eta2 t = 0 := by
  have hl : Real.log (2 * t) ≤ Real.log (2⁻¹) :=
    Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [Real.log_inv] at hl
  have hle : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by linarith [neg_abs_le (Real.log (2 * t))]
  simp [eta2, h0, max_eq_right hle]

/-- `log (2 (s/y)) = log 2 + log s − log y`. -/
theorem log_two_div {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    Real.log (2 * (s / y)) = Real.log 2 + Real.log s - Real.log y := by
  rw [Real.log_mul two_ne_zero (div_pos hs hy).ne', Real.log_div hs.ne' hy.ne']
  ring

/-- On `y ∈ [s, 2s]`: `η₂(s/y) = 4 (log y − log s)`. -/
theorem eta2_lo {s y : ℝ} (hs : 0 < s) (h1 : s ≤ y) (h2 : y ≤ 2 * s) :
    eta2 (s / y) = 4 * (Real.log y - Real.log s) := by
  have hy : 0 < y := lt_of_lt_of_le hs h1
  have ha : Real.log y ≤ Real.log 2 + Real.log s := by
    rw [← Real.log_mul two_ne_zero hs.ne']
    exact Real.log_le_log hy h2
  have hb : Real.log s ≤ Real.log y := Real.log_le_log hs h1
  rw [eta2, if_pos (div_pos hs hy), log_two_div hs hy,
    abs_of_nonneg (by linarith), max_eq_left (by linarith)]
  ring

/-- On `y ∈ [2s, 4s]`: `η₂(s/y) = 4 (2 log 2 + log s − log y)`. -/
theorem eta2_hi {s y : ℝ} (hs : 0 < s) (h1 : 2 * s ≤ y) (h2 : y ≤ 4 * s) :
    eta2 (s / y) = 4 * (2 * Real.log 2 + Real.log s - Real.log y) := by
  have hy : 0 < y := by linarith
  have ha : Real.log 2 + Real.log s ≤ Real.log y := by
    rw [← Real.log_mul two_ne_zero hs.ne']
    exact Real.log_le_log (by positivity) h1
  have h4 : Real.log (4 * s) = 2 * Real.log 2 + Real.log s := by
    rw [show (4 : ℝ) * s = 2 * (2 * s) by ring, Real.log_mul two_ne_zero (by positivity),
      Real.log_mul two_ne_zero hs.ne']
    ring
  have hb : Real.log y ≤ 2 * Real.log 2 + Real.log s := by
    rw [← h4]
    exact Real.log_le_log hy h2
  rw [eta2, if_pos (div_pos hs hy), log_two_div hs hy,
    abs_of_nonpos (by linarith), max_eq_left (by linarith)]
  ring

/-- Outside `(s, 4s)` the factor `η₂(s/y)` vanishes. -/
theorem eta2_div_zero {s y : ℝ} (hs : 0 < s) (hy : 0 < y) (h : y ≤ s ∨ 4 * s ≤ y) :
    eta2 (s / y) = 0 := by
  rcases h with h | h
  · exact eta2_of_one_le ((one_le_div hy).mpr h)
  · refine eta2_of_le_quarter (div_pos hs hy) ?_
    rw [div_le_iff₀ hy]
    linarith

/-- An interval with positive endpoints lies in `(0, ∞)`. -/
theorem uIcc_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : uIcc a b ⊆ Ioi 0 := by
  intro y hy
  rcases Set.mem_uIcc.mp hy with h | h
  · exact lt_of_lt_of_le ha h.1
  · exact lt_of_lt_of_le hb h.1

/-- `y ↦ η₂(s/y)` is continuous on `(0, ∞)` for `s > 0`. -/
theorem eta2_div_contOn {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun y => eta2 (s / y)) (Ioi 0) := by
  have hE : Continuous fun v : ℝ => 4 * max (Real.log 2 - |v|) 0 :=
    continuous_const.mul ((continuous_const.sub continuous_abs).max continuous_const)
  have hL : ContinuousOn (fun y : ℝ => Real.log (2 * (s / y))) (Ioi 0) :=
    ContinuousOn.log (continuousOn_const.mul
      (continuousOn_const.div continuousOn_id fun y hy => (mem_Ioi.mp hy).ne'))
      fun y hy => (mul_pos two_pos (div_pos hs (mem_Ioi.mp hy))).ne'
  refine (hE.comp_continuousOn hL).congr fun y hy => ?_
  simp only [Function.comp, eta2, if_pos (div_pos hs (mem_Ioi.mp hy))]

/-- `φ` is continuous. -/
theorem continuous_phi : Continuous phi := by
  unfold phi
  fun_prop

/-- `φ ≥ 0`. -/
theorem phi_nonneg (t : ℝ) : 0 ≤ phi t := by
  unfold phi
  positivity

/-- **`|φ|_∞ ≤ 2/e`**, from `x + 1 ≤ eˣ` at `x = t²/2 − 1`. -/
theorem phi_le (t : ℝ) : phi t ≤ 2 / Real.exp 1 := by
  have h1 : Real.exp (t ^ 2 / 2) = Real.exp 1 * Real.exp (t ^ 2 / 2 - 1) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : t ^ 2 / 2 - 1 + 1 ≤ Real.exp (t ^ 2 / 2 - 1) := Real.add_one_le_exp _
  have h3 : Real.exp (-t ^ 2 / 2) = (Real.exp (t ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hE : 0 < Real.exp (t ^ 2 / 2) := Real.exp_pos _
  rw [phi, h3, ← div_eq_mul_inv, div_le_div_iff₀ hE he]
  rw [h1]
  nlinarith [sq_nonneg t]

/-- The bound `2/e` is attained, at `t = √2`: it is `|φ|_∞`, not a loose majorant. -/
theorem phi_at_sqrt_two : phi (Real.sqrt 2) = 2 / Real.exp 1 := by
  rw [phi, Real.sq_sqrt (by norm_num), show -(2 : ℝ) / 2 = -1 by norm_num, Real.exp_neg]
  ring

/-- At a positive point the Mellin convolution against `η₂` is an integral over `(s, 4s)`. -/
theorem mconv_eta2 (g : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    mconv eta2 g s = ∫ y in s..4 * s, eta2 (s / y) * g y / y := by
  rw [mconv, intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun y hy => lt_trans hs hy.1) fun y hy => ?_
  obtain ⟨hy0, hy1⟩ := hy
  have hy0' : 0 < y := hy0
  have hor : y ≤ s ∨ 4 * s ≤ y := by
    by_contra hc
    push Not at hc
    exact hy1 ⟨hc.1, hc.2.le⟩
  rw [eta2_div_zero hs hy0' hor]
  ring

/-- `∫_s^{2s} η₂(s/y) dy/y = 2 (log 2)²`, by the fundamental theorem of calculus. -/
theorem int_lo {s : ℝ} (hs : 0 < s) :
    ∫ y in s..2 * s, eta2 (s / y) / y = 2 * Real.log 2 ^ 2 := by
  have hle : s ≤ 2 * s := by linarith
  have hsub : uIcc s (2 * s) ⊆ Ioi 0 := uIcc_pos hs (by linarith)
  have hcongr : EqOn (fun y => eta2 (s / y) / y) (fun y => 4 * (Real.log y - Real.log s) / y)
      (uIcc s (2 * s)) := by
    intro y hy
    rw [uIcc_of_le hle] at hy
    simp only [eta2_lo hs hy.1 hy.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ y ∈ uIcc s (2 * s), HasDerivAt
      (fun y => 2 * ((Real.log y - Real.log s) * (Real.log y - Real.log s)))
      (4 * (Real.log y - Real.log s) / y) y := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    have h := (Real.hasDerivAt_log hy0.ne').sub_const (Real.log s)
    refine ((h.mul h).const_mul 2).congr_deriv ?_
    ring
  have hi : IntervalIntegrable (fun y => 4 * (Real.log y - Real.log s) / y) volume s (2 * s) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div (continuousOn_const.mul
      ((Real.continuousOn_log.mono fun y hy => ?_).sub continuousOn_const)) continuousOn_id
      fun y hy => (hsub hy).ne'
    exact (hsub hy).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, Real.log_mul two_ne_zero hs.ne']
  ring

/-- `∫_{2s}^{4s} η₂(s/y) dy/y = 2 (log 2)²`, by the fundamental theorem of calculus. -/
theorem int_hi {s : ℝ} (hs : 0 < s) :
    ∫ y in 2 * s..4 * s, eta2 (s / y) / y = 2 * Real.log 2 ^ 2 := by
  have hle : 2 * s ≤ 4 * s := by linarith
  have hsub : uIcc (2 * s) (4 * s) ⊆ Ioi 0 := uIcc_pos (by linarith) (by linarith)
  have hcongr : EqOn (fun y => eta2 (s / y) / y)
      (fun y => 4 * (2 * Real.log 2 + Real.log s - Real.log y) / y) (uIcc (2 * s) (4 * s)) := by
    intro y hy
    rw [uIcc_of_le hle] at hy
    simp only [eta2_hi hs hy.1 hy.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ y ∈ uIcc (2 * s) (4 * s), HasDerivAt
      (fun y => -2 * ((2 * Real.log 2 + Real.log s - Real.log y) *
        (2 * Real.log 2 + Real.log s - Real.log y)))
      (4 * (2 * Real.log 2 + Real.log s - Real.log y) / y) y := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    have h := (Real.hasDerivAt_log hy0.ne').const_sub (2 * Real.log 2 + Real.log s)
    refine ((h.mul h).const_mul (-2)).congr_deriv ?_
    ring
  have hi : IntervalIntegrable (fun y => 4 * (2 * Real.log 2 + Real.log s - Real.log y) / y)
      volume (2 * s) (4 * s) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div (continuousOn_const.mul
      (continuousOn_const.sub (Real.continuousOn_log.mono fun y hy => ?_))) continuousOn_id
      fun y hy => (hsub hy).ne'
    exact (hsub hy).ne'
  have h4 : Real.log (4 * s) = 2 * Real.log 2 + Real.log s := by
    rw [show (4 : ℝ) * s = 2 * (2 * s) by ring, Real.log_mul two_ne_zero (by positivity),
      Real.log_mul two_ne_zero hs.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, h4, Real.log_mul two_ne_zero hs.ne']
  ring

/-- **`|η₂(t)/t|₁ = 4 (log 2)²`**: `∫_0^∞ η₂(s/y) dy/y = 4 (log 2)²` at every scale `s > 0`. -/
theorem int_eta2 {s : ℝ} (hs : 0 < s) :
    ∫ y in s..4 * s, eta2 (s / y) / y = 4 * Real.log 2 ^ 2 := by
  have hc : ContinuousOn (fun y => eta2 (s / y) / y) (Ioi 0) :=
    (eta2_div_contOn hs).div continuousOn_id fun y hy => (mem_Ioi.mp hy).ne'
  have h1 : IntervalIntegrable (fun y => eta2 (s / y) / y) volume s (2 * s) :=
    (hc.mono (uIcc_pos hs (by linarith))).intervalIntegrable
  have h2 : IntervalIntegrable (fun y => eta2 (s / y) / y) volume (2 * s) (4 * s) :=
    (hc.mono (uIcc_pos (by linarith) (by linarith))).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, int_lo hs, int_hi hs]
  ring

/-- **Helfgott's one-line Hölder bound** (7.19) `eq:macadam`: `|(η₂ ∗_M φ)(s)| ≤ |η₂(t)/t|₁·|φ|_∞
= 4 (log 2)²·(2/e)`, for EVERY real `s` (for `s ≤ 0` the convolution is `0`). -/
theorem abs_mconv_le (s : ℝ) : |mconv eta2 phi s| ≤ 4 * Real.log 2 ^ 2 * (2 / Real.exp 1) := by
  have hC : 0 ≤ 4 * Real.log 2 ^ 2 * (2 / Real.exp 1) := by positivity
  rcases le_or_gt s 0 with hs | hs
  · have h0 : mconv eta2 phi s = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [eta2_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs (mem_Ioi.mp hy).le)]
      ring
    rw [h0, abs_zero]
    exact hC
  · rw [mconv_eta2 phi hs]
    have hc : ContinuousOn (fun y => 2 / Real.exp 1 * (eta2 (s / y) / y)) (Ioi 0) :=
      continuousOn_const.mul
        ((eta2_div_contOn hs).div continuousOn_id fun y hy => (mem_Ioi.mp hy).ne')
    have hG : IntervalIntegrable (fun y => 2 / Real.exp 1 * (eta2 (s / y) / y)) volume s (4 * s) :=
      (hc.mono (uIcc_pos hs (by linarith))).intervalIntegrable
    have hb : ‖∫ y in s..4 * s, eta2 (s / y) * phi y / y‖ ≤
        ∫ y in s..4 * s, 2 / Real.exp 1 * (eta2 (s / y) / y) := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall fun y hy => ?_) hG
      have hy0 : 0 < y := lt_trans hs hy.1
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (eta2_nonneg _)
        (phi_nonneg y)) hy0.le)]
      have hm : eta2 (s / y) * phi y ≤ eta2 (s / y) * (2 / Real.exp 1) :=
        mul_le_mul_of_nonneg_left (phi_le y) (eta2_nonneg _)
      calc eta2 (s / y) * phi y / y ≤ eta2 (s / y) * (2 / Real.exp 1) / y :=
            div_le_div_of_nonneg_right hm hy0.le
        _ = 2 / Real.exp 1 * (eta2 (s / y) / y) := by ring
    rw [intervalIntegral.integral_const_mul, int_eta2 hs, Real.norm_eq_abs] at hb
    linarith

/-- **The constant of (7.19)**: `4 (log 2)²(2/e) = 1.4139903… ≤ 1.414`. -/
theorem holder_const_le : 4 * Real.log 2 ^ 2 * (2 / Real.exp 1) ≤ 1.414 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he := Real.exp_one_gt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hL2 : Real.log 2 ^ 2 ≤ 0.6931471808 ^ 2 := pow_le_pow_left₀ hl0 hl.le 2
  rw [show 4 * Real.log 2 ^ 2 * (2 / Real.exp 1) = 8 * Real.log 2 ^ 2 / Real.exp 1 by ring,
    div_le_iff₀ he0]
  nlinarith

/-- **(1) `|η_*|_∞ ≤ 1.414`, for ALL real `t`** — the second conjunct of `SupBounds`. The dilation
by `κ = 49` does not change a sup norm. -/
theorem etaStar_le (t : ℝ) : |etaStar t| ≤ 1.414 :=
  (abs_mconv_le (49 * t)).trans holder_const_le

/-- `η_*` vanishes on `(−∞, 0]`. -/
theorem etaStar_of_nonpos {t : ℝ} (ht : t ≤ 0) : etaStar t = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  rw [eta2_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (mem_Ioi.mp hy).le)]
  ring

/-- `η₂(s/y) > 0` strictly inside `(s, 4s)`. -/
theorem eta2_div_pos {s y : ℝ} (hs : 0 < s) (h1 : s < y) (h2 : y < 4 * s) : 0 < eta2 (s / y) := by
  rcases le_or_gt y (2 * s) with h | h
  · rw [eta2_lo hs h1.le h]
    have := Real.log_lt_log hs h1
    linarith
  · rw [eta2_hi hs h.le h2.le]
    have h4 : Real.log (4 * s) = 2 * Real.log 2 + Real.log s := by
      rw [show (4 : ℝ) * s = 2 * (2 * s) by ring, Real.log_mul two_ne_zero (by positivity),
        Real.log_mul two_ne_zero hs.ne']
      ring
    have := Real.log_lt_log (by linarith) h2
    linarith

/-- **(1) `η_*` is not the zero function**: `η_*(t) > 0` for EVERY `t > 0`. -/
theorem etaStar_pos {t : ℝ} (ht : 0 < t) : 0 < etaStar t := by
  have hs : 0 < 49 * t := by positivity
  rw [etaStar, mconv_eta2 phi hs]
  have hc : ContinuousOn (fun y => eta2 (49 * t / y) * phi y / y) (Ioi 0) :=
    ((eta2_div_contOn hs).mul continuous_phi.continuousOn).div continuousOn_id
      fun y hy => (mem_Ioi.mp hy).ne'
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (hc.mono (uIcc_pos hs (by linarith))).intervalIntegrable (fun y hy => ?_) (by linarith)
  have hy0 : 0 < y := lt_trans hs hy.1
  exact div_pos (mul_pos (eta2_div_pos hs hy.1 hy.2) (mul_pos (pow_pos hy0 2)
    (Real.exp_pos _))) hy0

/-! ## `η₊`: the definitions -/

/-- **Helfgott's `h(t) = t²(2−t)³e^{t−1/2}` on `[0,2]`, `0` elsewhere** (majarcs `eq:hortor`). -/
noncomputable def hFun (t : ℝ) : ℝ :=
  if 0 ≤ t ∧ t ≤ 2 then t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) else 0

/-- **`F_H(y) = sin(H log y)/(π log y)`** (majarcs `eq:dirich2`), written `(H/π)·sinc(H log y)`
so that the removable singularity at `y = 1` carries its limit `H/π` (`FH_eq`, `FH_one`,
`FH_tendsto`). Only `y > 0` is ever sampled by `mconv`. -/
noncomputable def FH (H y : ℝ) : ℝ := H / Real.pi * Real.sinc (H * Real.log y)

/-- **`h_H = h ∗_M F_H`** (majarcs `eq:dirich2`), the Mellin band-limited truncation of `h`. -/
noncomputable def hH (H t : ℝ) : ℝ := mconv hFun (FH H) t

/-- **Helfgott's `η₊(t) = h_H(t)·t·e^{−t²/2}`, `H = 200`** (majarcs `eq:patra2`, ternvin §7). -/
noncomputable def etaPlus (t : ℝ) : ℝ := hH 200 t * t * Real.exp (-t ^ 2 / 2)

/-- **The untruncated weight `η_∘(t) = h(t)·t·e^{−t²/2}`** (majarcs `eq:cleo2`, via `etaCirc_eq`).
NOT a substitute for `η₊`: it is the object `η₊` approximates, used for the easy half only. -/
noncomputable def etaCirc (t : ℝ) : ℝ := hFun t * t * Real.exp (-t ^ 2 / 2)

/-- `F_H(y) = sin(H log y)/(π log y)` for `y > 0`, `y ≠ 1`, `H ≠ 0`: the printed formula. -/
theorem FH_eq {H y : ℝ} (hH0 : H ≠ 0) (hy : 0 < y) (h1 : y ≠ 1) :
    FH H y = Real.sin (H * Real.log y) / (Real.pi * Real.log y) := by
  have hl : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy h1
  rw [FH, Real.sinc_of_ne_zero (mul_ne_zero hH0 hl)]
  field_simp

/-- `F_H(1) = H/π`. -/
theorem FH_one (H : ℝ) : FH H 1 = H / Real.pi := by
  simp [FH, Real.sinc_zero]

/-- `F_H` is continuous on `(0, ∞)`, across the removable singularity. -/
theorem FH_contOn (H : ℝ) : ContinuousOn (FH H) (Ioi 0) :=
  continuousOn_const.mul (Real.continuous_sinc.comp_continuousOn
    (continuousOn_const.mul (Real.continuousOn_log.mono fun _ hy =>
      (mem_Ioi.mp hy).ne')))

/-- **The removable singularity is filled correctly**: `sin(H log y)/(π log y) → H/π` as `y → 1`,
`y ≠ 1`; so `FH` is the continuous extension of the printed formula. -/
theorem FH_tendsto {H : ℝ} (hH0 : H ≠ 0) :
    Filter.Tendsto (fun y => Real.sin (H * Real.log y) / (Real.pi * Real.log y))
      (nhdsWithin 1 {1}ᶜ) (nhds (H / Real.pi)) := by
  have hc : ContinuousAt (FH H) 1 :=
    (FH_contOn H).continuousAt (Ioi_mem_nhds one_pos)
  rw [← FH_one H]
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hpos : ∀ᶠ y in nhdsWithin (1 : ℝ) {1}ᶜ, 0 < y :=
    nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)
  filter_upwards [hpos, self_mem_nhdsWithin] with y hy hy1
  exact FH_eq hH0 hy hy1

/-- `|F_H| ≤ H/π` (from `|sinc| ≤ 1`). -/
theorem abs_FH_le {H : ℝ} (hH0 : 0 ≤ H) (y : ℝ) : |FH H y| ≤ H / Real.pi := by
  rw [FH, abs_mul, abs_of_nonneg (div_nonneg hH0 Real.pi_pos.le)]
  exact mul_le_of_le_one_right (div_nonneg hH0 Real.pi_pos.le) (Real.abs_sinc_le_one _)

/-- `h` vanishes on `(−∞, 0]`. -/
theorem hFun_of_nonpos {t : ℝ} (ht : t ≤ 0) : hFun t = 0 := by
  unfold hFun
  split_ifs with h
  · rw [le_antisymm ht h.1]
    ring
  · rfl

/-- `h` vanishes on `[2, ∞)`. -/
theorem hFun_of_two_le {t : ℝ} (ht : 2 ≤ t) : hFun t = 0 := by
  unfold hFun
  split_ifs with h
  · rw [le_antisymm h.2 ht]
    ring
  · rfl

/-- `h(1) = e^{1/2}`. -/
theorem hFun_one : hFun 1 = Real.exp (1 / 2) := by
  rw [hFun, if_pos ⟨by norm_num, by norm_num⟩]
  norm_num

/-- `|h(v)| ≤ 8 e^{3/2} v²` for all real `v`. -/
theorem abs_hFun_le (v : ℝ) : |hFun v| ≤ 8 * Real.exp (3 / 2) * v ^ 2 := by
  unfold hFun
  split_ifs with h
  · obtain ⟨h0, h2⟩ := h
    rw [abs_of_nonneg (by positivity)]
    have hp : (2 - v) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have he : Real.exp (v - 1 / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by linarith)
    have hv : 0 ≤ v ^ 2 := sq_nonneg v
    calc v ^ 2 * (2 - v) ^ 3 * Real.exp (v - 1 / 2)
        ≤ v ^ 2 * 2 ^ 3 * Real.exp (3 / 2) := by gcongr
      _ = 8 * Real.exp (3 / 2) * v ^ 2 := by ring
  · rw [abs_zero]
    positivity

/-- `h` is measurable. -/
theorem measurable_hFun : Measurable hFun := by
  unfold hFun
  exact Measurable.ite measurableSet_Icc (by fun_prop) measurable_const

/-- `F_H` is measurable. -/
theorem measurable_FH (H : ℝ) : Measurable (FH H) := by
  unfold FH
  exact measurable_const.mul (Real.continuous_sinc.measurable.comp
    (measurable_const.mul Real.measurable_log))

/-- **`h_H` is a genuine Lebesgue integral, not Mathlib's junk `0`**: for `t > 0`, `H ≥ 0`, the
integrand `h(t/y) F_H(y)/y` is integrable on `(0,∞)` — it vanishes for `y ≤ t/2` and is at most
`8e^{3/2} t² (H/π) y⁻³` beyond (even though `F_H` itself is NOT integrable against `dy/y`). -/
theorem hH_integrable {H t : ℝ} (hH0 : 0 ≤ H) (ht : 0 < t) :
    IntegrableOn (fun y => hFun (t / y) * FH H y / y) (Ioi 0) := by
  have ht2 : 0 < t / 2 := by positivity
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := Ioi (t / 2)) ?_ measurableSet_Ioi
    fun y hy => ?_
  · have hg : IntegrableOn (fun y : ℝ => 8 * Real.exp (3 / 2) * t ^ 2 * (H / Real.pi) *
        y ^ (-3 : ℝ)) (Ioi (t / 2)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) ht2).const_mul _
    refine Integrable.mono' hg ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
    · exact (((measurable_hFun.comp (measurable_const.div measurable_id)).mul
        (measurable_FH H)).div measurable_id).aestronglyMeasurable
    · have hy0 : 0 < y := lt_trans ht2 hy
      have h1 := abs_hFun_le (t / y)
      have h2 := abs_FH_le hH0 y
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_natCast,
        Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hy0]
      calc |hFun (t / y)| * |FH H y| / y
          ≤ 8 * Real.exp (3 / 2) * (t / y) ^ 2 * (H / Real.pi) / y := by
            gcongr
        _ = 8 * Real.exp (3 / 2) * t ^ 2 * (H / Real.pi) * (y ^ 3)⁻¹ := by
            field_simp
  · obtain ⟨hy0, hy1⟩ := hy
    have hy0' : 0 < y := hy0
    have hyle : y ≤ t / 2 := not_lt.mp hy1
    have h2 : 2 ≤ t / y := by
      rw [le_div_iff₀ hy0']
      linarith
    rw [hFun_of_two_le h2]
    ring

/-- `h_H` vanishes on `(−∞, 0]`. -/
theorem hH_of_nonpos (H : ℝ) {t : ℝ} (ht : t ≤ 0) : hH H t = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  rw [hFun_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht (mem_Ioi.mp hy).le)]
  ring

/-- `η₊` vanishes on `(−∞, 0]`. -/
theorem etaPlus_of_nonpos {t : ℝ} (ht : t ≤ 0) : etaPlus t = 0 := by
  rw [etaPlus, hH_of_nonpos 200 ht]
  ring

/-- **`h(t)·t·e^{−t²/2} = t³(2−t)³e^{−(t−1)²/2}` on `[0,2]`**: Helfgott's `η_∘` (majarcs
`eq:cleo2`), the function `η₊` is built to approximate. -/
theorem etaCirc_eq {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    etaCirc t = t ^ 3 * (2 - t) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) := by
  rw [etaCirc, hFun, if_pos ⟨h0, h2⟩,
    show -(t - 1) ^ 2 / 2 = (t - 1 / 2) + -t ^ 2 / 2 by ring, Real.exp_add]
  ring

/-- **(2) The easy half: `|h(t)·t·e^{−t²/2}| ≤ 1` for ALL real `t`** (`|η_∘|_∞ = 1`, majarcs
App. B.5), via `t(2−t) = 1 − (t−1)² ∈ [0,1]` on `[0,2]`. -/
theorem etaCirc_le (t : ℝ) : |etaCirc t| ≤ 1 := by
  by_cases h : 0 ≤ t ∧ t ≤ 2
  · obtain ⟨h0, h2⟩ := h
    rw [etaCirc_eq h0 h2, show t ^ 3 * (2 - t) ^ 3 = (t * (2 - t)) ^ 3 by ring]
    have hw0 : 0 ≤ t * (2 - t) := mul_nonneg h0 (by linarith)
    have hw1 : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have hp : (t * (2 - t)) ^ 3 ≤ 1 := pow_le_one₀ hw0 hw1
    have he : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t - 1)])
    rw [abs_of_nonneg (by positivity)]
    calc (t * (2 - t)) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 * 1 :=
          mul_le_mul hp he (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
  · rw [etaCirc, hFun, if_neg h]
    simp

/-- The easy half is sharp: `η_∘(1) = 1`. -/
theorem etaCirc_one : etaCirc 1 = 1 := by
  rw [etaCirc_eq (by norm_num) (by norm_num)]
  norm_num

/-! ## `η₊`: the named obligation, and its reduction to a UNIFORM band-limiting bound -/

/-- **THE NAMED OBLIGATION (7.3)**: `|η₊|_∞ ≤ 1.079955`, the first conjunct of `SupBounds` for
Helfgott's `η₊`. Reduced here to `BandUniform` (`etaPlusSup_of_band`); PROVED as `BL.etaPlusSup`. -/
def EtaPlusSup : Prop := ∀ u : ℝ, |etaPlus u| ≤ 1.079955

/-- `|h'|_∞·(1 + (4/π) log H)/H` at `H = 200`, with Helfgott's `|h'|_∞ ≤ 2.80582038`
(majarcs `eq:morno`: `|h'|_∞ = 2.805820379671…`). Numerically `0.1086698`. Kept to certify
Helfgott's App. B.5 arithmetic (`plus_const_le`); the route it belongs to is broken — see
`BandUniform`. -/
noncomputable def bandConst : ℝ := 2.80582038 * ((1 + 4 / Real.pi * Real.log 200) / 200)

/-- **THE ANALYTIC CORE THAT REMAINS**: the band-limiting error of `h_H` is UNIFORMLY small,
`|h_200(t) − h(t)| ≤ 0.13` for every `t > 0`. PROVED downstream as `BL.band_uniform`. The true
sup is `1.138·10⁻⁵`, at `t ≈ 2.0004` (two independent quadratures agreeing to `10⁻¹⁵`), so the
constant has slack `~10⁴`.

**Why not Helfgott's own `eq:havana`.** It bounds `|h_H(t) − h(t)|/t` uniformly, and that is FALSE:
band-limiting in Mellin space destroys `h`'s `t²` vanishing at `0`, and `h_H(t)` decays only like
`|Mh(±iH)|/(π|log t|)` (`|Mh(−200i)| = 5.367·10⁻⁷`). At `t = 10⁻⁹`, `h_H = −7.86·10⁻⁹`, which is
`72×` the bound `t·bandConst`; at `t = 10⁻¹²` it is `3.4·10⁴×`. First failure near `t ≈ 10⁻⁷`.
Found by the weights round's verifier and reproduced by the coordinator with a different method.
The defect is in the `w < 0` half of Helfgott's integration by parts, where the factor
`t·e^{−w/H}` GROWS (up to `2`, by the support of `h`) but is integrated as if it decayed.
His conclusion `|η₊|_∞ ≤ 1.079955` is still TRUE (the sup is `≈ 1.00000007` at `t ≈ 1`); only the
route through `/t` is broken. A uniform bound needs no division by `t`, and `jorat_unif` turns it
into the sup bound through `|t e^{−t²/2}|_∞ = e^{−1/2}` instead of `|t² e^{−t²/2}|_∞ = 2/e`. -/
def BandUniform : Prop := ∀ t : ℝ, 0 < t → |hH 200 t - hFun t| ≤ 0.13

/-- `bandConst ≥ 0`. -/
theorem bandConst_nonneg : 0 ≤ bandConst := by
  have : 0 ≤ Real.log 200 := Real.log_nonneg (by norm_num)
  unfold bandConst
  have := Real.pi_pos
  positivity

/-- **majarcs `eq:jorat`, for ANY `g`**: if `|g(t) − h(t)| ≤ M·|t|` for all `t`, then
`|g(u)·u·e^{−u²/2}| ≤ |η_∘|_∞ + M·|t²e^{−t²/2}|_∞ ≤ 1 + (2/e)·M`. True, but it can never be
applied to `g = h_200`, for any `M`: `|h_200(t)|/t → ∞` as `t → 0` (see `BandUniform`). The chain
uses `jorat_unif` instead. -/
theorem jorat (g : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hg : ∀ t : ℝ, |g t - hFun t| ≤ M * |t|)
    (u : ℝ) : |g u * u * Real.exp (-u ^ 2 / 2)| ≤ 1 + 2 / Real.exp 1 * M := by
  have hsplit : g u * u * Real.exp (-u ^ 2 / 2) =
      etaCirc u + (g u - hFun u) * (u * Real.exp (-u ^ 2 / 2)) := by
    rw [etaCirc]
    ring
  have hu : |u| * |u| = u ^ 2 := by rw [abs_mul_abs_self, sq]
  rw [hsplit]
  calc |etaCirc u + (g u - hFun u) * (u * Real.exp (-u ^ 2 / 2))|
      ≤ |etaCirc u| + |g u - hFun u| * |u * Real.exp (-u ^ 2 / 2)| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ 1 + M * |u| * |u * Real.exp (-u ^ 2 / 2)| :=
        add_le_add (etaCirc_le u) (mul_le_mul_of_nonneg_right (hg u) (abs_nonneg _))
    _ = 1 + M * phi u := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _), phi]
        linear_combination M * Real.exp (-u ^ 2 / 2) * hu
    _ ≤ 1 + 2 / Real.exp 1 * M := by
        have := mul_le_mul_of_nonneg_left (phi_le u) hM
        linarith

/-- `jorat`'s hypothesis discharged once, by a real function: `g = h` itself, `M = 0`. -/
theorem jorat_self (u : ℝ) : |etaCirc u| ≤ 1 + 2 / Real.exp 1 * 0 :=
  jorat hFun 0 le_rfl (fun t => by simp) u

/-- `BandUniform` extends to all real `t` (both sides vanish for `t ≤ 0`). -/
theorem band_all (hb : BandUniform) (t : ℝ) : |hH 200 t - hFun t| ≤ 0.13 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [hH_of_nonpos 200 ht, hFun_of_nonpos ht, sub_zero, abs_zero]
    norm_num
  · exact hb t ht

/-- `|u|·e^{−u²/2} ≤ e^{−1/2}` for every real `u`: `|u| ≤ (u² + 1)/2 ≤ e^{(u²−1)/2}`. -/
theorem abs_mul_exp_le (u : ℝ) : |u| * Real.exp (-u ^ 2 / 2) ≤ Real.exp (-1 / 2) := by
  have h1 : |u| ≤ (u ^ 2 - 1) / 2 + 1 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have h2 : |u| ≤ Real.exp ((u ^ 2 - 1) / 2) := h1.trans (Real.add_one_le_exp _)
  have h3 : Real.exp ((u ^ 2 - 1) / 2) * Real.exp (-u ^ 2 / 2) = Real.exp (-1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |u| * Real.exp (-u ^ 2 / 2) ≤ Real.exp ((u ^ 2 - 1) / 2) * Real.exp (-u ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-1 / 2) := h3

/-- `e^{1/2} > 1.64`, from `e > 2.7182818283` and `1.64² = 2.6896`. -/
theorem exp_half_gt : (1.64 : ℝ) < Real.exp (1 / 2) := by
  have he := Real.exp_one_gt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **`eq:jorat` without the division by `t`, for ANY `g`**: if `|g(t) − h(t)| ≤ c` for all `t`,
then `|g(u)·u·e^{−u²/2}| ≤ |η_∘|_∞ + c·|t e^{−t²/2}|_∞ = 1 + c·e^{−1/2}`. -/
theorem jorat_unif (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ t : ℝ, |g t - hFun t| ≤ c)
    (u : ℝ) : |g u * u * Real.exp (-u ^ 2 / 2)| ≤ 1 + c * Real.exp (-1 / 2) := by
  have hsplit : g u * u * Real.exp (-u ^ 2 / 2) =
      etaCirc u + (g u - hFun u) * (u * Real.exp (-u ^ 2 / 2)) := by
    rw [etaCirc]
    ring
  rw [hsplit]
  calc |etaCirc u + (g u - hFun u) * (u * Real.exp (-u ^ 2 / 2))|
      ≤ |etaCirc u| + |g u - hFun u| * |u * Real.exp (-u ^ 2 / 2)| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ 1 + c * Real.exp (-1 / 2) := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact add_le_add (etaCirc_le u)
          (mul_le_mul (hg u) (abs_mul_exp_le u) (by positivity) hc)

/-- `jorat_unif`'s hypothesis discharged once, by a real function: `g = h` itself, `c = 0`. -/
theorem jorat_unif_self (u : ℝ) : |etaCirc u| ≤ 1 + 0 * Real.exp (-1 / 2) :=
  jorat_unif hFun 0 le_rfl (fun t => by simp) u

/-- `1 + 0.13·e^{−1/2} ≤ 1.079955` (`1.0788490…`; margin `1.1·10⁻³`), from `e^{1/2} > 1.64`. -/
theorem unif_const_le : 1 + 0.13 * Real.exp (-1 / 2) ≤ 1.079955 := by
  have hinv : Real.exp (-1 / 2) = 1 / Real.exp (1 / 2) := by
    rw [one_div, ← Real.exp_neg]
    norm_num
  have hle : 0.13 * Real.exp (-1 / 2) ≤ 0.13 / 1.64 := by
    rw [hinv, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) exp_half_gt.le
  have hnum : (0.13 : ℝ) / 1.64 ≤ 0.079955 := by norm_num
  linarith

/-- `log 200 < 5.29832` (truth `5.2983174`), via `200 = 2⁷·(4/5)⁻²` and ten terms of the
series of `log(1 − x)` at `x = 1/5`. -/
theorem log_200_lt : Real.log 200 < 5.29832 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 5) (by norm_num) 10
  have h' := (abs_le.mp h).1
  have e45 : (1 : ℝ) - 1 / 5 = 4 / 5 := by norm_num
  rw [e45] at h'
  norm_num [Finset.sum_range_succ] at h'
  have hlog : Real.log 200 = 7 * Real.log 2 - 2 * Real.log (4 / 5) := by
    rw [show (200 : ℝ) = 2 ^ 7 / (4 / 5) ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hlog]
  linarith [Real.log_two_lt_d9]

/-- **majarcs `eq:malgache`, second inequality**: `(2/e)·2.80582038 ≤ 2.06440727`
(`2.0644072668…`; margin `3.2·10⁻⁹`). -/
theorem malgache : 2 / Real.exp 1 * 2.80582038 ≤ 2.06440727 := by
  have he := Real.exp_one_gt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [div_mul_eq_mul_div, div_le_iff₀ he0]
  linarith

/-- **ternvin (7.3), last inequality**: `1 + 2.06440727·(1 + (4/π) log 200)/200 ≤ 1.079955`
(`1.07995477…`; margin `2.3·10⁻⁷`). -/
theorem sazar : 1 + 2.06440727 * ((1 + 4 / Real.pi * Real.log 200) / 200) ≤ 1.079955 := by
  have hp := Real.pi_gt_d6
  have hp0 : 0 < Real.pi := Real.pi_pos
  have hl := log_200_lt
  have hl0 : 0 ≤ Real.log 200 := Real.log_nonneg (by norm_num)
  have h4 : 4 / Real.pi * Real.log 200 ≤ 4 / 3.141592 * 5.29832 := by
    have ha : 4 / Real.pi ≤ 4 / 3.141592 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      hp.le
    exact mul_le_mul ha hl.le hl0 (by norm_num)
  nlinarith

/-- `1 + (2/e)·bandConst ≤ 1.079955`: `malgache` then `sazar`. -/
theorem plus_const_le : 1 + 2 / Real.exp 1 * bandConst ≤ 1.079955 := by
  have hq : 0 ≤ (1 + 4 / Real.pi * Real.log 200) / 200 := by
    have : 0 ≤ Real.log 200 := Real.log_nonneg (by norm_num)
    have := Real.pi_pos
    positivity
  have h1 : 2 / Real.exp 1 * bandConst ≤ 2.06440727 * ((1 + 4 / Real.pi * Real.log 200) / 200) := by
    rw [bandConst, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right malgache hq
  linarith [sazar]

/-- **(2) THE REDUCTION: `BandUniform → EtaPlusSup`**, by `jorat_unif`: `|η_∘|_∞ = 1`
(`etaCirc_le`), `|t e^{−t²/2}|_∞ = e^{−1/2}` (`abs_mul_exp_le`), and `1 + 0.13·e^{−1/2} ≤ 1.079955`
(`unif_const_le`). -/
theorem etaPlusSup_of_band (hb : BandUniform) : EtaPlusSup := fun u =>
  (jorat_unif (hH 200) 0.13 (by norm_num) (band_all hb) u).trans unif_const_le

/-- **The obligation cannot be met by a degenerate `η₊`**: under `BandUniform`, `η₊(1) > 0`
(`h_H(1) ≥ e^{1/2} − 0.13 > 1.5`). -/
theorem etaPlus_one_pos (hb : BandUniform) : 0 < etaPlus 1 := by
  have h := hb 1 one_pos
  rw [hFun_one] at h
  have hx : 1 / 2 + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have hpos : 0 < hH 200 1 := by linarith [(abs_le.mp h).1]
  rw [etaPlus]
  positivity

/-- **The `1.079955` bound is a real constraint on shape**: it already fails for `1.08·η_∘`. -/
theorem plusSup_tight : ¬ ∀ u : ℝ, |1.08 * etaCirc u| ≤ 1.079955 := by
  intro h
  have h1 := h 1
  rw [etaCirc_one] at h1
  norm_num at h1

/-! ## (3) The reduction of link 0 -/

/-- **`SupBounds` for any `f` with `η₊`'s sup bound, paired with the REAL `η_*`.** -/
theorem supBounds_of (f : ℝ → ℝ) (hf : ∀ u : ℝ, |f u| ≤ 1.079955) :
    Smooth.SupBounds f etaStar :=
  ⟨hf, etaStar_le⟩

/-- `supBounds_of`'s hypothesis discharged once, by a real Helfgott weight: `(η_∘, η_*)`. -/
theorem supBounds_circ : Smooth.SupBounds etaCirc etaStar :=
  supBounds_of etaCirc fun u => (etaCirc_le u).trans (by norm_num)

/-- **(3) `supBounds_helf : EtaPlusSup → SupBounds η₊ η_*`** — link 0 for Helfgott's own weights,
with the `η_*` half PROVED and the `η₊` half the named obligation. -/
theorem supBounds_helf (hp : EtaPlusSup) : Smooth.SupBounds etaPlus etaStar :=
  supBounds_of etaPlus hp

/-- Link 0 for Helfgott's weights from `BandUniform`, the uniform band-limiting bound. -/
theorem supBounds_band (hb : BandUniform) : Smooth.SupBounds etaPlus etaStar :=
  supBounds_helf (etaPlusSup_of_band hb)

/-- **THE CHAIN, on Helfgott's own weights**: `PlattGRH → EtaPlusSup → CircleIdSmooth η₊ η_* →
MajorLowerSmooth η₊ η_* → MinorUpperSmooth η₊ η_* → Cite_Helfgott_weighted`
(`SmPP.cite5_no_summ` with link 0 supplied by `supBounds_helf`). -/
theorem cite_helf (grh : Spine.PlattGRH) (hp : EtaPlusSup)
    (ci : Smooth.CircleIdSmooth etaPlus etaStar) (mj : Smooth.MajorLowerSmooth etaPlus etaStar)
    (mn : Smooth.MinorUpperSmooth etaPlus etaStar) : Principia.Erdos1054.Cite_Helfgott_weighted :=
  SmPP.cite5_no_summ etaPlus etaStar grh (supBounds_helf hp) ci mj mn

/-- The chain with `BandUniform` in place of `EtaPlusSup`. -/
theorem cite_band (grh : Spine.PlattGRH) (hb : BandUniform)
    (ci : Smooth.CircleIdSmooth etaPlus etaStar) (mj : Smooth.MajorLowerSmooth etaPlus etaStar)
    (mn : Smooth.MinorUpperSmooth etaPlus etaStar) : Principia.Erdos1054.Cite_Helfgott_weighted :=
  cite_helf grh (etaPlusSup_of_band hb) ci mj mn

/-- **THE CHAIN on Helfgott's own weights, at THREE links**: `PlattGRH → BandUniform →
MajorLowerSmooth η₊ η_* → MinorUpperSmooth η₊ η_* → Cite_Helfgott_weighted`. The circle identity is
discharged by `SmCI.cite4_no_summ` (summability comes from the major-arc link). -/
theorem cite_band3 (grh : Spine.PlattGRH) (hb : BandUniform)
    (mj : Smooth.MajorLowerSmooth etaPlus etaStar) (mn : Smooth.MinorUpperSmooth etaPlus etaStar) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  SmCI.cite4_no_summ etaPlus etaStar grh (supBounds_band hb) mj mn

end Principia.Common.TernaryGoldbach.HW
