/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajSpine
import Principia.Common.TernaryGoldbach.HelfgottCited
import Principia.Common.TernaryGoldbach.HelfgottWrap
import Principia.Common.FourierBessel
import Principia.Common.PNT.Medium.MellinCalculus
import Principia.Common.PNT.Medium.ResidueCalcOnRectangles
import Principia.Common.PNT.Medium.SmoothExistence
import Principia.Common.SW.Perron

set_option autoImplicit false

/-!
# `lem:agamon` (the explicit formula) and the CORRECTED `lem:crepe`, as spines of named links

**`agamon_of_links` PROVES `HM.ExplicitFormula` FROM SIX NAMED LINKS, and
`crepeC_of_named` PROVES `CrepeC` (the corrected `lem:crepe`) FROM `HM.ExplicitFormula`, two cited
lemmas and two named facts about the mollified `η₂`. THE LINKS ARE OPEN.** Nothing here proves
an explicit formula, a zero count, or a bound on `L'/L`. What is proved is that the survey's
route composes to EXACTLY `HM.ExplicitFormula` (`agamon_statement`, by `rfl` against the
body transcribed from `HelfMajSpine.lean` 200-206), and that `CrepeC` feeds the only consumer of
`HC.Crepe`, `GS.Austeria` (`austeria_of_citedC`, the conclusion of `HC.austeria_of_cited`).

Sources: `majarcs.tex` (arXiv 1305.2897 v4) 2884-3189 (`lem:agamon`); `ternvin.tex`
(arXiv 1312.7748 v2) 5454-5528 (`lem:crepe`), 5530-5560 (`cor:austeria`).

## The spine of `HM.ExplicitFormula` (application only at every level)

```
 startLine_holds (EF3, PROVED)   Rectangle (EF4)   Horizontal (EF5, THE RISK)
 Continuation (EF1) ─► phi_diff       MollDecay (EF2)   mollReg_holds (EF2, PROVED)
        └──────── bookkeeping (PROVED, generic in Ψ) ────────┘
                         ▼
 mollCore_of_links : MollCore      the approximate formula for f_ε = f ∗_M ν_ε
                         ▼  + MollLimit (EF9); |Mν(ερ)| ≤ 1 + ε, Mν(0) = 1, Mν entire (PROVED)
 core_of_moll : Core               |x·err + R − I| ≤ ∑_ρ |G(ρ)| x^{Re ρ}   (in ℝ≥0∞)
                         ▼  + |R| ≤ c₀ (g0_le, PROVED)
                         ▼  + |I| ≤ (log q + 8)(|η'|₂ + 2π|δ||η|₂)/√x (ileft_le, PROVED
                         ▼    from LeftLD, Mellin–Plancherel (PROVED), Cauchy–Schwarz, Minkowski)
 agamon_of_core ─► HM.ExplicitFormula
```

`f(t) = η(t)e(δt)`, `G = M f = HM.Gm η δ`, `ν` a smooth mollifier on `[1/2, 2]` with
`∫ν(t)dt/t = 1` (PNT+ `SmoothExistence`), `ν_ε(t) = ν(t^{1/ε})/ε` (PNT+ `DeltaSpike`),
`Φ_ε = G_cont · Mν(ε·)`, `Ψ = −(L'/L)·Φ·x^s`. `R = [χ even, q ≠ 1]·G(0)` (the trivial zero at `0`),
`I = (1/2π)∫ Ψ(−1/2 + iτ)dτ` with `Φ = G`.

| link | survey | regime | what it asserts |
|---|---|---|---|
| `Rectangle` | EF4 | PORT | residue theorem on `[−1/2,3/2]×[−T,T]` + the zero map of `L(s,χ)` |
| `Horizontal` | EF5 | DEEP | admissible heights with small horizontal integrals — THE RISK |
| `Continuation` | EF1 | BUILD | `G_cont` holomorphic on `−1 < Re s < b`, `b > 3/2` |
| `MollDecay` | EF2 | BUILD | `Φ_ε` decays faster than every power of `|Im s|` on the strip |
| `MollLimit` | EF9 | BUILD | `∑Λχ f_ε(n/x) → ∑Λχ f(n/x)` as `ε → 0⁺` |
| `LeftLD` | EF6-7 | BUILD | `(1/2π)∫|L'/L(−1/2 + iτ)|²/|s|² dτ ≤ (log q + 8)²` |

PROVED here (no link): the start line (`startLine_holds`: Mellin inversion on `Re s = 3/2`,
`−L'/L = ∑Λχ n^{−s}` there, `integral_tsum`; ported from our `pnt/PsiChi.lean`, reusing
`SW.neg_logDeriv_LFunction_eq` and `SW.cpow_ratio`), the regularity of `f_ε` (`mollReg_holds`:
`f_ε` continuous on `(0, ∞)`,
`M f_ε = G·Mν(ε·)` on `Re s = 3/2`, from the Mellin convolution theorem `mellin_mconv`, which
discharges the Tonelli hypothesis of PNT+ `MellinConvolutionTransform`), Mellin–Plancherel on
`Re s = 1/2` (`mellinPlancherel_holds`, from
`FourierBessel.bessel`), `|G(0)| ≤ c₀` with `|log t| ≤ (2/3)(√t + 1/√t)` (`g0_le`, `abs_log_le`,
the direction `eq:hutterite` uses), the left-line Cauchy–Schwarz + Minkowski (`lint_ileft_le`), the
contour bookkeeping (`bookkeeping`, `rect_split`), the `ε → 0⁺` limit (`core_of_moll`), and the
mollifier facts (`differentiable_Mnu`, `Mnu_zero`, `norm_Mnu_le`, `norm_Mnu_strip`).
`HM.ZeroCount` is NOT used (finding F-C): the zero sum enters only as an `ℝ≥0∞` upper bound
(`sum_le_zsum`), so neither its convergence nor a zero count is needed.

Also PROVED, for both spines: the Mellin convolution theorem `mellin_mconv` (for `f, g`
continuous on `(0, ∞)` with Mellin transforms convergent at `s`), continuity of Mellin
convolutions (`continuousOn_mconv`), `M η₂(s) = 4((1 − 2^{−s})/s)²` (`mellin_eta2`, by the
fundamental theorem of calculus), and `η₂ ∗_M ν_ε → η₂` (`eta2e_sub_le`).

## The spine of `CrepeC` (the corrected `lem:crepe`)

```
 HM.ExplicitFormula at (η₂ ∗_M ν_ε, q = 1, χ = 1, δ = 0)   Eta2Reg, Eta2Norms (named)
   M(η₂ ∗_M ν_ε) = M η₂ · Mν(ε·), M η₂ = 4((1 − 2^{−s})/s)²   (Eta2Mellin, Eta2Main: PROVED)
   low zeros:  RH to T₀ (PC.ZetaRHTo, grhTo_one) + RosserL17          κ = 0.0463
   high zeros: x^{Re ρ} ≤ x + RamareSaouterL2 (rs_value ≤ 2.5·10⁻¹⁰)
        ▼ crepe_eps (one scale ε)   ▼ ε → 0⁺ (Eta2Conv: PROVED, |η₂ ∗_M ν_ε − η₂| ≤ 4ε log 2)
 crepeC_of_named : CrepeC ─► austeria_of_citedC : GS.Austeria
```

## FINDINGS (numerics in `scratchpad/efsp/num1.py`)

* **F-A. `HC.Crepe` is transcribed from a printed error, and is heuristically FALSE.** `eq:envy`
  prints `M η₂(s) = ((1 − 2^{−s})/s)²`, but `η₂ = η₁ ∗_M η₁` with `η₁ = 2·1_{[1/2,1]}`, so
  `M η₂ = 4((1 − 2^{−s})/s)²`: at `s = 1`, `∫η₂ = 1` (mpmath `1.0`) against the printed `1/4`,
  and at `ρ₁ = 1/2 + 14.1347i` the quadrature matches `4((1 − 2^{−s})/s)²` to 30 digits.
  Helfgott's `0.135 = (3/2 + √2)·κ₁` is the printed formula's constant; the true one is `0.5397`.
  Under linear independence of the ordinates `limsup (S(x) − x)/√x = ∑|M η₂(ρ)|`, and 200 zero
  pairs already give `0.348 > 0.135` (survey). Typechecked: `mellin_eta2` (the correct formula)
  and `envy_printed_one` (the printed one is `1/4` at `s = 1`, `M η₂(1) = 1`).
  **So `HC.Crepe` is NOT proved here.** `CrepeC`
  states the corrected bound `(1 + 4.1·10⁻⁹)x + 0.8√x`; it is IMPLIED by `HC.Crepe`
  (`crepeC_of_crepe`), so no consumer loses anything, and `GS.Austeria` needs only `0.8 ≤ 2.007`.
* **F-B. `lem:agamon`'s proof needs mollification.** Fubini on `Re s = 3/2` needs `G ∈ L¹` there,
  which `AgamonReg` does not give (`G` is only bounded). The spine runs the contour argument on
  `f_ε = f ∗_M ν_ε` and takes `ε → 0⁺` in the INEQUALITY (`core_of_moll`), legitimate because the
  zero sum is an `ℝ≥0∞` absolute sum.
* **F-C.** Neither `HM.ZeroCount` nor convergence of `∑_ρ` is needed for `HM.ExplicitFormula`.
* **F-D.** `CrepeC` is not a separate deep link: it is `HM.ExplicitFormula` at `η₂ ∗_M ν_ε` plus
  the two cited zero-sum lemmas (`crepeC_of_links`).
* **F-E.** `eq:hutterite` is printed with the inequality reversed; the direction used,
  `|log t| ≤ (2/3)(√t + 1/√t)` (maximal ratio `0.66274`), is `abs_log_le`, PROVED.

## Junk values

`MajSp.twSum` is a `tsum` (junk `0` if not summable), `Ileft` a Bochner integral (junk `0` if not
integrable); both make `Core` HARDER, never vacuous. `LeftLD`, `MellinPlancherel` and the
zero sums are `lintegral`/`ℝ≥0∞` statements (no junk). `Gcont`'s value at `0` is `G0`, an explicit
integral; `HM.Gm` at a zero is the Lebesgue Mellin integral, convergent there under `AgamonReg`.

## Ported (with credit)

PNT+ (Kontorovich–Tao et al., `C:/Users/Christian/pnt`, commit `d963a6e`), via the in-library
ports `Principia.Common.PNT.Medium`: `MellinConvolution`, `DeltaSpike`, `SmoothExistence`,
`RectangleIntegral`/`HIntegral`/`VIntegral` (the objects the contour links are stated with),
`Filter.BigO_zero_at*_of_support_in_Icc`. Mathlib's private `rexp_neg_*_aux`/`rexp_cexp_aux`
(`Mathlib/Analysis/MellinInversion.lean`) are re-proved here as `rexp_neg_deriv'`,
`rexp_neg_image'`, `rexp_neg_injOn'`, `rexp_cexp'`. Constants are all explicit numerals except
inside the named links' existentials (`MollDecay`'s `C`, which only feeds `Horizontal`).
-/

namespace Principia.Common.TernaryGoldbach.EF

open MeasureTheory Set Filter Topology Principia.Common.Goldbach
open scoped ENNReal ArithmeticFunction ContDiff

/-! ## (1) Objects -/

/-- **The twisted weight** `f(t) = η(t)·e(δt)`; `HM.Gm η δ` is its Mellin transform. -/
noncomputable def fw (η : ℝ → ℝ) (δ : ℝ) (t : ℝ) : ℂ := ((η t : ℝ) : ℂ) * e (δ * t)

/-- `HM.Gm η δ = M f` (definitional). -/
theorem gm_eq (η : ℝ → ℝ) (δ : ℝ) : HM.Gm η δ = mellin (fw η δ) := rfl

/-- **`G(0)` of the continuation**: `−∫₀^∞ f'(t) log t dt`. -/
noncomputable def G0 (η : ℝ → ℝ) (δ : ℝ) : ℂ :=
  -∫ t in Ioi (0 : ℝ), deriv (fw η δ) t * ((Real.log t : ℝ) : ℂ)

/-- The left line: `−1/2 + iτ`. -/
noncomputable def sL (τ : ℝ) : ℂ := -1 / 2 + τ * Complex.I

/-- The line `1/2 + iτ` (where `M f'` is taken). -/
noncomputable def sH (τ : ℝ) : ℂ := 1 / 2 + τ * Complex.I

/-- **`G` on the left line**: `G(−1/2 + iτ) = −(M f')(1/2 + iτ)/(−1/2 + iτ)`. -/
noncomputable def Gleft (η : ℝ → ℝ) (δ : ℝ) (τ : ℝ) : ℂ :=
  -mellin (deriv (fw η δ)) (sH τ) / sL τ

open Classical in
/-- **The residue at `s = 0`**: `G(0)` for an even `χ` of modulus `q ≠ 1`, else `0`. -/
noncomputable def Rres (η : ℝ → ℝ) (δ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  if q ≠ 1 ∧ χ.Even then G0 η δ else 0

/-- `(L'/L)(s, χ)`. -/
noncomputable def LD {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  logDeriv (DirichletCharacter.LFunction χ) s

/-- **The left-line integral** `I = (1/2π) ∫ −(L'/L)(s) G(s) x^s dτ`, `s = −1/2 + iτ`. -/
noncomputable def Ileft (η : ℝ → ℝ) (δ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ, -LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ

/-! ## (2) The top level -/

/-- **`Core` (derived: `core_of_moll`)**: the explicit formula as an inequality with the residue
at `0` and the left-line integral kept: `|x·err + R − I| ≤ ∑_ρ m(ρ)|G(ρ)|x^{Re ρ}` (an `ℝ≥0∞` sum,
so a divergent zero sum makes it trivially true, exactly as in `HM.ExplicitFormula`). -/
def Core : Prop :=
  ∀ η : ℝ → ℝ, HM.AgamonReg η → η 0 = 0 →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ δ x : ℝ, 0 < x →
      ENNReal.ofReal ‖(x : ℂ) * MajSp.err η χ δ x + Rres η δ χ - Ileft η δ χ x‖ ≤
        HM.zsum χ univ (fun ρ => ENNReal.ofReal (‖HM.Gm η δ ρ‖ * x ^ ρ.re))

/-- **The last step, PROVED**: `x|err| ≤ |x·err + R − I| + |R| + |I|`. -/
theorem ef_of_parts {η : ℝ → ℝ} {δ x : ℝ} (hx : 0 < x) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {Z : ℝ≥0∞} {B : ℝ}
    (hC : ENNReal.ofReal ‖(x : ℂ) * MajSp.err η χ δ x + Rres η δ χ - Ileft η δ χ x‖ ≤ Z)
    (hR : ‖Rres η δ χ‖ ≤ HM.c0 η δ) (hI : ‖Ileft η δ χ x‖ ≤ B) :
    ENNReal.ofReal (x * ‖MajSp.err η χ δ x‖) ≤ Z + ENNReal.ofReal (HM.c0 η δ + B) := by
  set A := (x : ℂ) * MajSp.err η χ δ x + Rres η δ χ - Ileft η δ χ x with hAdef
  have hA : x * ‖MajSp.err η χ δ x‖ ≤ ‖A‖ + (HM.c0 η δ + B) := by
    have e1 : (x : ℂ) * MajSp.err η χ δ x = A - Rres η δ χ + Ileft η δ χ x := by
      rw [hAdef]; ring
    have n1 : ‖(x : ℂ) * MajSp.err η χ δ x‖ = x * ‖MajSp.err η χ δ x‖ := by
      rw [norm_mul, Complex.norm_of_nonneg hx.le]
    have t1 := norm_add_le (A - Rres η δ χ) (Ileft η δ χ x)
    have t2 := norm_sub_le A (Rres η δ χ)
    rw [← e1, n1] at t1
    linarith
  calc ENNReal.ofReal (x * ‖MajSp.err η χ δ x‖)
      ≤ ENNReal.ofReal (‖A‖ + (HM.c0 η δ + B)) := ENNReal.ofReal_le_ofReal hA
    _ ≤ ENNReal.ofReal ‖A‖ + ENNReal.ofReal (HM.c0 η δ + B) := ENNReal.ofReal_add_le
    _ ≤ Z + ENNReal.ofReal (HM.c0 η δ + B) := add_le_add_left hC _

/-! ## Residue bound -/

/-- `‖e x‖ = 1` (copied from `Goldbach.norm_e`, `Harc.lean`, which this file does not import). -/
theorem norm_e_eq (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℝ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- `f' = η' e(δt) + η · 2πiδ e(δt)`. -/
theorem hasDerivAt_fw {η : ℝ → ℝ} {t : ℝ} (h : DifferentiableAt ℝ η t) (δ : ℝ) :
    HasDerivAt (fw η δ) (((deriv η t : ℝ) : ℂ) * e (δ * t) +
      ((η t : ℝ) : ℂ) * (2 * Real.pi * Complex.I * δ * e (δ * t))) t :=
  h.hasDerivAt.ofReal_comp.mul (MajorArcMainTerm.hasDerivAt_e δ t)

/-- `|f'| ≤ |η'| + 2π|δ||η|`. -/
theorem norm_deriv_fw_le {η : ℝ → ℝ} {t : ℝ} (h : DifferentiableAt ℝ η t) (δ : ℝ) :
    ‖deriv (fw η δ) t‖ ≤ |deriv η t| + 2 * Real.pi * |δ| * |η t| := by
  rw [(hasDerivAt_fw h δ).deriv]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  have h2 : ‖(2 * Real.pi * Complex.I * (δ : ℂ) : ℂ)‖ = 2 * Real.pi * |δ| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
    ring
  rw [norm_mul, norm_mul, norm_mul, h2, norm_e_eq, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  ring

/-- **`log s ≤ (s + 1/s)/3`** for every `s > 0`: the tangent line of `log` at `3.3`
(`log 3.3 ≤ 1.2`), and `s/3.3 + 0.2 ≤ (s + 1/s)/3` (a quadratic with negative discriminant). -/
theorem log_le_third {s : ℝ} (hs : 0 < s) : Real.log s ≤ (s + 1 / s) / 3 := by
  have h33 : Real.log 3.3 ≤ 1.2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have e1 := Real.exp_one_gt_d9
    have e2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.2 by norm_num)
    have e3 : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by
      rw [← Real.exp_add]; norm_num
    rw [e3]
    nlinarith [Real.exp_pos 0.2]
  have htan : Real.log s ≤ Real.log 3.3 + s / 3.3 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < s / 3.3 by positivity)
    rw [Real.log_div hs.ne' (by norm_num)] at h1
    linarith
  have hu : s * (1 / s) = 1 := mul_one_div_cancel hs.ne'
  have h5 : 0 ≤ s * (s / 33 + (1 / s) / 3 - 0.2) := by nlinarith [sq_nonneg (s - 3.3), hu]
  have h6 : 0 ≤ s / 33 + (1 / s) / 3 - 0.2 := by
    by_contra hneg
    have := mul_neg_of_pos_of_neg hs (not_le.mp hneg)
    linarith
  have e : (s + 1 / s) / 3 - (s / 3.3 + 0.2) = s / 33 + 1 / s / 3 - 0.2 := by ring
  linarith

/-- **`|log t| ≤ (2/3)(√t + 1/√t)`** (the direction `eq:hutterite` uses; maximal ratio
`0.66274`). -/
theorem abs_log_le {t : ℝ} (ht : 0 < t) :
    |Real.log t| ≤ 2 / 3 * (Real.sqrt t + 1 / Real.sqrt t) := by
  have hs := Real.sqrt_pos.mpr ht
  have h1 := log_le_third hs
  have h2 : -Real.log (Real.sqrt t) ≤ (Real.sqrt t + 1 / Real.sqrt t) / 3 := by
    have h := log_le_third (one_div_pos.mpr hs)
    rw [one_div_one_div, one_div, Real.log_inv] at h
    rw [one_div]
    linarith
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht.le]; ring
  rw [hlog, abs_mul, abs_two]
  have := abs_le.mpr ⟨by linarith, h1⟩
  linarith

/-- `η t^{−1/2} ∈ L¹(0,∞)` gives `|η|/√t ∈ L¹(0,∞)`. -/
theorem integrableOn_h {g : ℝ → ℝ}
    (hI : IntegrableOn (fun t => g t * t ^ ((1 / 2 : ℝ) - 1)) (Ioi 0)) :
    IntegrableOn (fun t => |g t| / Real.sqrt t) (Ioi 0) := by
  have h0 : IntegrableOn (fun t => ‖g t * t ^ ((1 / 2 : ℝ) - 1)‖) (Ioi 0) := hI.norm
  refine h0.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_pos (Real.rpow_pos_of_pos ht' _), show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
    Real.rpow_neg ht'.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- `η t^{1/2} ∈ L¹(0,∞)` gives `|η|√t ∈ L¹(0,∞)`. -/
theorem integrableOn_s {g : ℝ → ℝ}
    (hI : IntegrableOn (fun t => g t * t ^ ((3 / 2 : ℝ) - 1)) (Ioi 0)) :
    IntegrableOn (fun t => |g t| * Real.sqrt t) (Ioi 0) := by
  have h0 : IntegrableOn (fun t => ‖g t * t ^ ((3 / 2 : ℝ) - 1)‖) (Ioi 0) := hI.norm
  refine h0.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_pos (Real.rpow_pos_of_pos ht' _), show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]

/-- The four weighted `L¹` norms of `c₀` are finite under `AgamonReg` (`σ = 1/2, 3/2`). -/
theorem agamon_int {η : ℝ → ℝ} (hreg : HM.AgamonReg η) :
    IntegrableOn (fun t => |η t| / Real.sqrt t) (Ioi 0) ∧
      IntegrableOn (fun t => |η t| * Real.sqrt t) (Ioi 0) ∧
      IntegrableOn (fun t => |deriv η t| / Real.sqrt t) (Ioi 0) ∧
      IntegrableOn (fun t => |deriv η t| * Real.sqrt t) (Ioi 0) := by
  obtain ⟨-, -, -, a, b, ha, hb, hab⟩ := hreg
  have h1 := hab (1 / 2) ⟨by linarith, by linarith⟩
  have h3 := hab (3 / 2) ⟨by linarith, by linarith⟩
  exact ⟨integrableOn_h h1.1, integrableOn_s h3.1, integrableOn_h h1.2, integrableOn_s h3.2⟩

/-- `η` is differentiable at every `t > 0` under `AgamonReg`. -/
theorem agamon_diff {η : ℝ → ℝ} (hreg : HM.AgamonReg η) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ η t :=
  (hreg.1.differentiableOn one_ne_zero).differentiableAt (Ici_mem_nhds ht)

/-- **`|G(0)| ≤ c₀`** (`eq:marenostrum`, 2909–2912): `|∫ f' log t| ≤ ∫ |f'| |log t|`,
`|f'| ≤ |η'| + 2π|δ||η|` and `|log t| ≤ (2/3)(√t + 1/√t)`. -/
theorem g0_le {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) : ‖G0 η δ‖ ≤ HM.c0 η δ := by
  obtain ⟨i1, i2, i3, i4⟩ := agamon_int hreg
  have i34 : IntegrableOn (fun t => |deriv η t| / Real.sqrt t + |deriv η t| * Real.sqrt t)
      (Ioi 0) := i3.add i4
  have i12 : IntegrableOn (fun t => |η t| / Real.sqrt t + |η t| * Real.sqrt t) (Ioi 0) :=
    i1.add i2
  have i12c : IntegrableOn (fun t => 2 * Real.pi * |δ| *
      (|η t| / Real.sqrt t + |η t| * Real.sqrt t)) (Ioi 0) := i12.const_mul _
  have iall : IntegrableOn (fun t => (|deriv η t| / Real.sqrt t + |deriv η t| * Real.sqrt t) +
      2 * Real.pi * |δ| * (|η t| / Real.sqrt t + |η t| * Real.sqrt t)) (Ioi 0) := i34.add i12c
  have hgi : IntegrableOn (fun t => 2 / 3 * ((|deriv η t| / Real.sqrt t +
      |deriv η t| * Real.sqrt t) + 2 * Real.pi * |δ| * (|η t| / Real.sqrt t +
      |η t| * Real.sqrt t))) (Ioi 0) := iall.const_mul _
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖deriv (fw η δ) t * ((Real.log t : ℝ) : ℂ)‖ ≤
      2 / 3 * ((|deriv η t| / Real.sqrt t + |deriv η t| * Real.sqrt t) +
        2 * Real.pi * |δ| * (|η t| / Real.sqrt t + |η t| * Real.sqrt t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hs := Real.sqrt_pos.mpr ht'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA := norm_deriv_fw_le (agamon_diff hreg ht') δ
    have hB := abs_log_le ht'
    calc ‖deriv (fw η δ) t‖ * |Real.log t|
        ≤ (|deriv η t| + 2 * Real.pi * |δ| * |η t|) *
            (2 / 3 * (Real.sqrt t + 1 / Real.sqrt t)) :=
          mul_le_mul hA hB (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have key := norm_integral_le_of_norm_le hgi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  rw [integral_const_mul, integral_add i34 i12c,
    integral_add i3 i4, integral_const_mul, integral_add i1 i2] at key
  rw [G0, norm_neg]
  exact key

theorem rres_le {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ‖Rres η δ χ‖ ≤ HM.c0 η δ := by
  unfold Rres
  split_ifs
  · exact g0_le hreg δ
  · rw [norm_zero]; exact HM.c0_nonneg η δ

/-! ## Left line -/

/-- **LINK [LeftLD] (EF6 + EF7) — BUILD, explicit**: for every primitive `χ` mod `q` (`q = 1`
included), `∫_ℝ |L'/L(−1/2 + iτ, χ)|²/|−1/2 + iτ|² dτ ≤ 2π(log q + 8)²`. Route (survey): the
log-derivative of the functional equation, digamma reflection/duplication, `|ψ(z) − log z| ≤ 10/27`
on `Re z = 3/2`, `∑Λ(n)n^{−3/2} ≤ 1.63`; Minkowski against `∫dτ/|s|² = 2π` gives
`log q + √(I(c)/2π)` with `c = 6.8551`, i.e. `7.573 ≤ 8` (the printed `6.01` drops `|arg| ≤ π/2`,
flag F6). Numerically `2.18 ≤ 64` at `q = 1` (`num1.py`). -/
def LeftLD : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∫⁻ τ : ℝ, ENNReal.ofReal ((‖LD χ (sL τ)‖ / ‖sL τ‖) ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi * (Real.log q + 8) ^ 2)

/-- **Mellin–Plancherel on `Re s = 1/2`, as an inequality** (PROVED: `mellinPlancherel_holds`):
if `M F` converges on `Re s = 1/2` then `τ ↦ M F(1/2 + iτ)` is continuous and
`∫|M F(1/2 + iτ)|² dτ ≤ 2π ∫_0^∞ |F|²`. -/
def MellinPlancherel : Prop :=
  ∀ F : ℝ → ℂ, MellinConvergent F (1 / 2 : ℂ) →
    Continuous (fun τ : ℝ => mellin F (sH τ)) ∧
      ∫⁻ τ : ℝ, ENNReal.ofReal (‖mellin F (sH τ)‖ ^ 2) ≤
        ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖F t‖ ^ 2)

/-- `∫⁻_{(0,∞)} (c|g|)² = (c|g|₂)²` for `g ∈ L²(0,∞)`. -/
theorem lint_sq {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Ioi 0))) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * |g t|) ^ (2 : ℝ) =
      ENNReal.ofReal ((c * MajSp.l2 g) ^ 2) := by
  have hi : Integrable (fun t => c ^ 2 * g t ^ 2) (volume.restrict (Ioi 0)) :=
    hg.integrable_sq.const_mul _
  have h1 : ∀ t : ℝ, ENNReal.ofReal (c * |g t|) ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2 * g t ^ 2) := by
    intro t
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), mul_pow, sq_abs]
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => by positivity),
    integral_const_mul, mul_pow, MajSp.l2,
    Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg (g t))]

/-- `(X^{1/2})^2 = X` in `ℝ≥0∞`, used to undo the `L²` normalisation. -/
theorem le_sq_of_rpow_half_le {X Y : ℝ≥0∞} (h : X ^ (1 / 2 : ℝ) ≤ Y) : X ≤ Y ^ (2 : ℝ) := by
  have h2 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2

/-- `(ofReal (X²))^{1/2} = ofReal X` for `X ≥ 0`. -/
theorem ofReal_sq_rpow_half {X : ℝ} (hX : 0 ≤ X) :
    ENNReal.ofReal (X ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal X := by
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg X) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hX]

/-- **Minkowski**: `∫_0^∞ |f'|² ≤ (|η'|₂ + 2π|δ||η|₂)²`. -/
theorem mink_bound {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖deriv (fw η δ) t‖ ^ 2) ≤
      ENNReal.ofReal ((MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η) ^ 2) := by
  have hc : 0 ≤ 2 * Real.pi * |δ| := by positivity
  have m1 : MemLp (deriv η) 2 (volume.restrict (Ioi 0)) := hreg.2.2.1
  have m0 : MemLp η 2 (volume.restrict (Ioi 0)) := hreg.2.1
  have hu : AEMeasurable (fun t => ENNReal.ofReal (1 * |deriv η t|))
      (volume.restrict (Ioi 0)) :=
    ((continuous_abs.measurable.comp_aemeasurable m1.aestronglyMeasurable.aemeasurable).const_mul
      1).ennreal_ofReal
  have hv : AEMeasurable (fun t => ENNReal.ofReal (2 * Real.pi * |δ| * |η t|))
      (volume.restrict (Ioi 0)) :=
    ((continuous_abs.measurable.comp_aemeasurable m0.aestronglyMeasurable.aemeasurable).const_mul
      _).ennreal_ofReal
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (‖deriv (fw η δ) t‖ ^ 2) ≤
      ((fun t => ENNReal.ofReal (1 * |deriv η t|)) +
        (fun t => ENNReal.ofReal (2 * Real.pi * |δ| * |η t|))) t ^ (2 : ℝ) := by
    intro t ht
    have hb := norm_deriv_fw_le (agamon_diff hreg ht) δ
    simp only [Pi.add_apply]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_pow (by positivity), one_mul]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hb 2)
  have hint := setLIntegral_mono' (μ := volume) measurableSet_Ioi hpt
  have hmk := ENNReal.lintegral_Lp_add_le hu hv (show (1 : ℝ) ≤ 2 by norm_num)
  rw [lint_sq m1 zero_le_one, lint_sq m0 hc, one_mul, ofReal_sq_rpow_half (MajSp.l2_nonneg _),
    ofReal_sq_rpow_half (mul_nonneg hc (MajSp.l2_nonneg _)),
    ← ENNReal.ofReal_add (MajSp.l2_nonneg _) (mul_nonneg hc (MajSp.l2_nonneg _))] at hmk
  have h3 := le_sq_of_rpow_half_le hmk
  rw [ENNReal.ofReal_rpow_of_nonneg
    (add_nonneg (MajSp.l2_nonneg _) (mul_nonneg hc (MajSp.l2_nonneg _))) (by norm_num),
    Real.rpow_two] at h3
  exact hint.trans h3

/-- `f' t^{−1/2} ∈ L¹(0,∞)`: `M f'` converges on `Re s = 1/2`. -/
theorem mellinConv_deriv_fw {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    MellinConvergent (deriv (fw η δ)) (1 / 2 : ℂ) := by
  obtain ⟨i1, -, i3, -⟩ := agamon_int hreg
  have hdom : IntegrableOn (fun t => |deriv η t| / Real.sqrt t +
      2 * Real.pi * |δ| * (|η t| / Real.sqrt t)) (Ioi 0) := i3.add (i1.const_mul _)
  refine Integrable.mono' hdom ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (Complex.measurable_ofReal.pow_const _).smul (measurable_deriv _)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have hs := Real.sqrt_pos.mpr ht'
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht']
    have hre : ((1 / 2 : ℂ) - 1).re = -(1 / 2) := by norm_num
    rw [hre, Real.rpow_neg ht'.le, ← Real.sqrt_eq_rpow]
    have hb := norm_deriv_fw_le (agamon_diff hreg ht') δ
    calc (Real.sqrt t)⁻¹ * ‖deriv (fw η δ) t‖
        ≤ (Real.sqrt t)⁻¹ * (|deriv η t| + 2 * Real.pi * |δ| * |η t|) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

/-- `L'/L` is measurable (it is `deriv L / L`, `L` continuous off `1`). -/
theorem measurable_LD {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Measurable (LD χ) := by
  have hL : Measurable (DirichletCharacter.LFunction χ) :=
    measurable_of_continuousOn_compl_singleton 1 fun s hs =>
      (DirichletCharacter.differentiableAt_LFunction χ s
        (Or.inl hs)).continuousAt.continuousWithinAt
  exact (measurable_deriv _).div hL

/-- `sL` is measurable. -/
theorem measurable_sL : Measurable sL := by
  unfold sL
  fun_prop

/-- `‖sL τ‖ > 0`. -/
theorem sL_ne_zero (τ : ℝ) : sL τ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [sL] at this

/-- **The left-line integrand in `L¹`, with its bound**: Cauchy–Schwarz between `(L'/L)/s`
(LINK `LeftLD`) and `s G = −M f'(s + 1)` (Mellin–Plancherel), and Minkowski. -/
theorem lint_ileft_le (hLD : LeftLD) (hPl : MellinPlancherel) {η : ℝ → ℝ}
    (hreg : HM.AgamonReg η) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫⁻ τ : ℝ, ENNReal.ofReal ‖-LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ‖ ≤
      ENNReal.ofReal (x ^ (-(1 / 2) : ℝ) * (2 * Real.pi * ((Real.log q + 8) *
        (MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η)))) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set L := MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η with hLdef
  have hL0 : 0 ≤ L := add_nonneg (MajSp.l2_nonneg _)
    (mul_nonneg (by positivity) (MajSp.l2_nonneg _))
  have hpi : 0 < 2 * Real.pi := by positivity
  obtain ⟨hcont, hpl⟩ := hPl _ (mellinConv_deriv_fw hreg δ)
  have hB : ∫⁻ τ : ℝ, ENNReal.ofReal (‖mellin (deriv (fw η δ)) (sH τ)‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi * L ^ 2) := by
    refine hpl.trans (le_of_le_of_eq (mul_le_mul_right (mink_bound hreg δ) _) ?_)
    rw [← ENNReal.ofReal_mul hpi.le]
  have hA := hLD q χ hχ
  set a : ℝ → ℝ := fun τ => ‖LD χ (sL τ)‖ / ‖sL τ‖ with hadef
  set b : ℝ → ℝ := fun τ => ‖mellin (deriv (fw η δ)) (sH τ)‖ with hbdef
  have ha0 : ∀ τ, 0 ≤ a τ := fun τ => div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb0 : ∀ τ, 0 ≤ b τ := fun τ => norm_nonneg _
  have hAm : AEMeasurable (fun τ => ENNReal.ofReal (a τ)) volume :=
    ((((measurable_LD χ).comp measurable_sL).norm.div
      measurable_sL.norm)).ennreal_ofReal.aemeasurable
  have hBm : AEMeasurable (fun τ => ENNReal.ofReal (b τ)) volume :=
    hcont.norm.measurable.ennreal_ofReal.aemeasurable
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hAm hBm
  have e2 : ∀ (g : ℝ → ℝ), (∀ τ, 0 ≤ g τ) →
      (fun τ => ENNReal.ofReal (g τ) ^ (2 : ℝ)) = fun τ => ENNReal.ofReal (g τ ^ 2) := by
    intro g hg
    funext τ
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hg τ)]
  rw [e2 a ha0, e2 b hb0] at hcs
  have hA' := ENNReal.rpow_le_rpow hA (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hB' := ENNReal.rpow_le_rpow hB (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hprod : ∫⁻ τ : ℝ, ENNReal.ofReal (a τ) * ENNReal.ofReal (b τ) ≤
      ENNReal.ofReal (2 * Real.pi * ((Real.log q + 8) * L)) := by
    refine hcs.trans ((mul_le_mul' hA' hB').trans (le_of_eq ?_))
    have k1 : 2 * Real.pi * (Real.log q + 8) ^ 2 =
        (Real.sqrt (2 * Real.pi) * (Real.log q + 8)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpi.le]
    have k2 : 2 * Real.pi * L ^ 2 = (Real.sqrt (2 * Real.pi) * L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpi.le]
    rw [k1, k2, ofReal_sq_rpow_half (by positivity), ofReal_sq_rpow_half (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have := Real.mul_self_sqrt hpi.le
    nlinarith [this]
  have hnorm : ∀ τ : ℝ, ENNReal.ofReal ‖-LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ‖ =
      ENNReal.ofReal (x ^ (-(1 / 2) : ℝ)) * (ENNReal.ofReal (a τ) * ENNReal.ofReal (b τ)) := by
    intro τ
    rw [← ENNReal.ofReal_mul (ha0 τ), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hre : (sL τ).re = -(1 / 2) := by simp [sL]; norm_num
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Gleft,
      norm_div, norm_neg]
    simp only [hadef, hbdef]
    ring
  simp_rw [hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _)]
  exact mul_le_mul_right hprod _

/-- **`|I| ≤ (log q + 8)(|η'|₂ + 2π|δ||η|₂)/√x`**, from `lint_ileft_le`. -/
theorem ileft_le (hLD : LeftLD) (hPl : MellinPlancherel) {η : ℝ → ℝ} (hreg : HM.AgamonReg η)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (δ : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ‖Ileft η δ χ x‖ ≤
      (Real.log q + 8) * (MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η) / Real.sqrt x := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set L := MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η with hLdef
  have hL0 : 0 ≤ L := add_nonneg (MajSp.l2_nonneg _)
    (mul_nonneg (by positivity) (MajSp.l2_nonneg _))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hI := (norm_integral_le_lintegral_norm
    (fun τ : ℝ => -LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ)).trans
      (ENNReal.toReal_le_of_le_ofReal (by positivity) (lint_ileft_le hLD hPl hreg hχ δ hx))
  unfold Ileft
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpi)]
  calc (2 * Real.pi)⁻¹ * ‖∫ τ : ℝ, -LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ‖
      ≤ (2 * Real.pi)⁻¹ * (x ^ (-(1 / 2) : ℝ) * (2 * Real.pi * ((Real.log q + 8) * L))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (Real.log q + 8) * L / Real.sqrt x := by
        rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
        field_simp

/-- `G` on the left line is measurable. -/
theorem measurable_gleft (hPl : MellinPlancherel) {η : ℝ → ℝ} (hreg : HM.AgamonReg η)
    (δ : ℝ) : Measurable (Gleft η δ) := by
  have hc := (hPl _ (mellinConv_deriv_fw hreg δ)).1
  exact hc.measurable.neg.div measurable_sL

/-- **The left-line integrand is in `L¹`.** -/
theorem integrable_ileft (hLD : LeftLD) (hPl : MellinPlancherel) {η : ℝ → ℝ}
    (hreg : HM.AgamonReg η) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun τ : ℝ => -LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ) := by
  refine ⟨?_, (hasFiniteIntegral_iff_norm _).mpr
    (lt_of_le_of_lt (lint_ileft_le hLD hPl hreg hχ δ hx) ENNReal.ofReal_lt_top)⟩
  have hsL : Continuous sL := by unfold sL; fun_prop
  have hxs : Continuous fun τ : ℝ => (x : ℂ) ^ sL τ :=
    hsL.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact ((((measurable_LD χ).comp measurable_sL).neg.mul (measurable_gleft hPl hreg δ)).mul
    hxs.measurable).aestronglyMeasurable

/-- **`HM.ExplicitFormula` from `Core`, `LeftLD` and Mellin–Plancherel** (PROVED):
`|x·err| ≤ |x·err + R − I| + |R| + |I|` with `|R| ≤ c₀` (`rres_le`) and the left-line bound
(`ileft_le`). -/
theorem agamon_of_core (hC : Core) (hLD : LeftLD) (hPl : MellinPlancherel) :
    HM.ExplicitFormula := by
  intro η hreg h0 q _ χ hχ δ x hx
  exact ef_of_parts hx (hC η hreg h0 q χ hχ δ x hx) (rres_le hreg δ χ)
    (ileft_le hLD hPl hreg hχ δ hx)

/-! ## (3) The mollification level -/

/-- A mollifier: smooth, `≥ 0`, supported in `[1/2, 2]`, `∫₀^∞ ν(t) dt/t = 1`. -/
def MollData (ν : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ν ∧ (∀ t, 0 ≤ ν t) ∧ Function.support ν ⊆ Icc (1 / 2) 2 ∧
    ∫ t in Ioi (0 : ℝ), ν t / t = 1

/-- A mollifier exists (PNT+ `SmoothExistence`). -/
theorem exists_mollData : ∃ ν : ℝ → ℝ, MollData ν := by
  obtain ⟨ν, h1, h2, h3, h4⟩ := SmoothExistence
  exact ⟨ν, h1, h2, h3, by rwa [integral_Ici_eq_integral_Ioi] at h4⟩

/-- `ν` as a complex function. -/
noncomputable def nuC (ν : ℝ → ℝ) (t : ℝ) : ℂ := ((ν t : ℝ) : ℂ)

/-- **`M ν`**, the Mellin transform of the mollifier (entire: `differentiable_Mnu`). -/
noncomputable def Mnu (ν : ℝ → ℝ) (s : ℂ) : ℂ := mellin (nuC ν) s

/-- **The mollified weight** `f_ε = f ∗_M ν_ε`, `ν_ε(t) = ν(t^{1/ε})/ε` (PNT+ `DeltaSpike`). -/
noncomputable def Fe (η : ℝ → ℝ) (δ : ℝ) (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℂ :=
  MellinConvolution (fw η δ) (nuC (DeltaSpike ν ε))

/-- **The twisted sum of a complex weight**: `∑ Λ(n) χ(n) F(n/x)`. -/
noncomputable def twF {q : ℕ} (F : ℝ → ℂ) (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * F ((n : ℝ) / x)

open Classical in
/-- **The continuation of `G`** to `Re s > −1`: `G(s)` for `Re s > 0`, `G(0)` at `0`, and
`−M f'(s + 1)/s` otherwise (integration by parts; `η(0) = 0` removes the pole at `0`). -/
noncomputable def Gcont (η : ℝ → ℝ) (δ : ℝ) (s : ℂ) : ℂ :=
  if 0 < s.re then HM.Gm η δ s else
    if s = 0 then G0 η δ else -mellin (deriv (fw η δ)) (s + 1) / s

/-- **`Φ_ε = G · Mν(ε ·)`**, the continued Mellin transform of `f_ε`. -/
noncomputable def Phi (η : ℝ → ℝ) (δ : ℝ) (ν : ℝ → ℝ) (ε : ℝ) (s : ℂ) : ℂ :=
  Gcont η δ s * Mnu ν (ε * s)

/-- `Ψ(s) = −(L'/L)(s) Φ(s) x^s`. -/
noncomputable def Psi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Φ : ℂ → ℂ) (x : ℝ)
    (s : ℂ) : ℂ :=
  -LD χ s * Φ s * (x : ℂ) ^ s

open Classical in
/-- **The residues of `Ψ` in `[−1/2, 3/2] × [−T, T]`**: `Φ(1)x` from the pole of `ζ` (`q = 1`),
`−m Φ(ρ) x^ρ` at each non-trivial zero in `S`, and `−Φ(0)` from the trivial zero at `0` of an even
`χ` with `q ≠ 1`. -/
noncomputable def resSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Φ : ℂ → ℂ) (x : ℝ)
    (S : Finset ℂ) : ℂ :=
  (if q = 1 then Φ 1 * x else 0) -
    ∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * Φ ρ * (x : ℂ) ^ ρ -
    (if q ≠ 1 ∧ χ.Even then Φ 0 else 0)

/-- **The approximate explicit formula for the mollified weight** (derived: `mollCore_of_links`):
the twisted sum minus the residues minus the left-line integral is as small as we like, for
suitable finite sets of zeros. -/
def MollCore : Prop :=
  ∀ η : ℝ → ℝ, HM.AgamonReg η → η 0 = 0 → ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ δ x : ℝ, 0 < x →
      ∀ θ : ℝ, 0 < θ → ∃ S : Finset ℂ, (↑S : Set ℂ) ⊆ HM.zeroSet χ ∧
        ‖twF (Fe η δ ν ε) χ x - resSum χ (Phi η δ ν ε) x S -
          ((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ, Psi χ (Phi η δ ν ε) x (sL τ)‖ ≤ θ

/-- **LINK [MollLimit] (EF9) — BUILD**: `∑Λ(n)χ(n)f_ε(n/x) → ∑Λ(n)χ(n)f(n/x)` as `ε → 0⁺`
(a weighted-`L¹` approximate identity for `f` and `f'` plus the sum-versus-integral bound). -/
def MollLimit : Prop :=
  ∀ η : ℝ → ℝ, HM.AgamonReg η → η 0 = 0 → ∀ ν : ℝ → ℝ, MollData ν →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ x : ℝ), 0 < x →
      Tendsto (fun ε => twF (Fe η δ ν ε) χ x) (𝓝[>] 0) (𝓝 (MajSp.twSum η χ x (δ / x)))

/-- The support of `ν` as a complex function. -/
theorem nuC_support {ν : ℝ → ℝ} (hν : MollData ν) : Function.support (nuC ν) ⊆ Icc (1 / 2) 2 :=
  fun t ht => hν.2.2.1 (by
    simp only [Function.mem_support, nuC, ne_eq, Complex.ofReal_eq_zero] at ht ⊢
    exact ht)

/-- **`M ν` is entire** (compact support in `(0, ∞)`). -/
theorem differentiable_Mnu {ν : ℝ → ℝ} (hν : MollData ν) : Differentiable ℂ (Mnu ν) := by
  intro s
  have hsupp := nuC_support hν
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) ?_ ?_
    (by linarith) ?_ (by linarith)
  · exact (Complex.continuous_ofReal.comp hν.1.continuous).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · exact (Filter.BigO_zero_atTop_of_support_in_Icc _ hsupp).trans (Asymptotics.isBigO_zero _ _)
  · exact (Filter.BigO_zero_atZero_of_support_in_Icc _ (by norm_num) hsupp).trans
      (Asymptotics.isBigO_zero _ _)

/-- **`M ν(0) = ∫ ν(t) dt/t = 1`.** -/
theorem Mnu_zero {ν : ℝ → ℝ} (hν : MollData ν) : Mnu ν 0 = 1 := by
  unfold Mnu mellin
  have h : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ ((0 : ℂ) - 1) • nuC ν t = ((ν t / t : ℝ) : ℂ) := by
    intro t _
    rw [zero_sub, Complex.cpow_neg_one, smul_eq_mul, nuC]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_complex_ofReal, hν.2.2.2,
    Complex.ofReal_one]

/-- `t^σ ≤ 2^{|σ|}` on `[1/2, 2]`. -/
theorem rpow_le_two_rpow_abs {t σ : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 2) : t ^ σ ≤ 2 ^ |σ| := by
  have ht0 : 0 < t := by linarith [ht.1]
  rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log t ≤ Real.log 2 := Real.log_le_log ht0 ht.2
  have h2 : -Real.log 2 ≤ Real.log t := by
    have := Real.log_le_log (by norm_num) ht.1
    rwa [one_div, Real.log_inv] at this
  rcases le_or_gt 0 σ with hs | hs
  · rw [abs_of_nonneg hs]
    nlinarith
  · rw [abs_of_neg hs]
    nlinarith

/-- **`|M ν(s)| ≤ 2^{|Re s|}`.** -/
theorem norm_Mnu_le {ν : ℝ → ℝ} (hν : MollData ν) (s : ℂ) : ‖Mnu ν s‖ ≤ 2 ^ |s.re| := by
  have hint : Integrable (fun t => ν t / t) (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [hν.2.2.2]; norm_num)
  have hb : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • nuC ν t‖ ≤ 2 ^ |s.re| * (ν t / t) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hν0 := hν.2.1 t
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', nuC, Complex.norm_real,
      Real.norm_of_nonneg hν0, Complex.sub_re, Complex.one_re, Real.rpow_sub_one ht'.ne']
    by_cases h0 : ν t = 0
    · rw [h0]
      simp
    · have hmem : t ∈ Icc (1 / 2 : ℝ) 2 := hν.2.2.1 h0
      have := rpow_le_two_rpow_abs (σ := s.re) hmem
      calc t ^ s.re / t * ν t = t ^ s.re * (ν t / t) := by ring
        _ ≤ 2 ^ |s.re| * (ν t / t) := mul_le_mul_of_nonneg_right this (div_nonneg hν0 ht'.le)
  unfold Mnu mellin
  calc ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • nuC ν t‖
      ≤ ∫ t in Ioi (0 : ℝ), 2 ^ |s.re| * (ν t / t) :=
        norm_integral_le_of_norm_le (hint.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hb))
    _ = 2 ^ |s.re| := by rw [integral_const_mul, hν.2.2.2, mul_one]

/-- `2^u ≤ 1 + u` for `0 ≤ u ≤ 1` (Bernoulli). -/
theorem two_rpow_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : (2 : ℝ) ^ u ≤ 1 + u := by
  have h := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) h0 h1
  norm_num at h
  linarith

/-- **`|M ν(ερ)| ≤ 1 + ε`** in the critical strip, `0 < ε ≤ 1`. -/
theorem norm_Mnu_strip {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ‖Mnu ν (ε * ρ)‖ ≤ 1 + ε := by
  refine (norm_Mnu_le hν _).trans ?_
  have hre : ((ε : ℂ) * ρ).re = ε * ρ.re := by simp
  rw [hre, abs_of_nonneg (by positivity)]
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (two_rpow_le hε0.le hε1)
  nlinarith

/-- `G(1) = ∫₀^∞ η(t) e(δt) dt`, the main term. -/
theorem gm_one (η : ℝ → ℝ) (δ : ℝ) : HM.Gm η δ 1 = MajSp.mainFT η δ := by
  rw [HM.Gm, MajSp.mainFT, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [sub_self, Complex.cpow_zero, one_smul]

/-- `sL τ + 1 = sH τ`. -/
theorem sL_add_one (τ : ℝ) : sL τ + 1 = sH τ := by
  unfold sL sH
  ring

/-- **The continuation on the left line is `Gleft`.** -/
theorem gcont_sL (η : ℝ → ℝ) (δ : ℝ) (τ : ℝ) : Gcont η δ (sL τ) = Gleft η δ τ := by
  have hre : (sL τ).re = -(1 / 2) := by simp [sL]; norm_num
  unfold Gcont Gleft
  rw [if_neg (by rw [hre]; norm_num), if_neg (sL_ne_zero τ), sL_add_one]

/-- A finite set of zeros sums to at most the zero sum. -/
theorem sum_le_zsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {A : Set ℂ} {S : Finset ℂ}
    (hS : (↑S : Set ℂ) ⊆ HM.zeroSet χ ∩ A) (w : ℂ → ℝ≥0∞) :
    ∑ ρ ∈ S, HM.zmult χ ρ * w ρ ≤ HM.zsum χ A w := by
  classical
  rw [← Finset.sum_subtype_of_mem (fun ρ => HM.zmult χ ρ * w ρ)
    (p := fun ρ => ρ ∈ HM.zeroSet χ ∩ A) (fun ρ hρ => hS hρ)]
  exact ENNReal.sum_le_tsum _

/-- **The residue sum over `S` is bounded by the zero sum**, with the mollifier's `1 + ε`. -/
theorem norm_sum_le_zsum {η : ℝ → ℝ} {δ : ℝ} {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {x : ℝ}
    (hx : 0 < x) {S : Finset ℂ} (hS : (↑S : Set ℂ) ⊆ HM.zeroSet χ)
    (hZ : HM.zsum χ univ (fun ρ => ENNReal.ofReal (‖HM.Gm η δ ρ‖ * x ^ ρ.re)) ≠ ⊤) :
    ‖∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
        Phi η δ ν ε ρ * (x : ℂ) ^ ρ‖ ≤
      (1 + ε) * (HM.zsum χ univ (fun ρ => ENNReal.ofReal (‖HM.Gm η δ ρ‖ * x ^ ρ.re))).toReal := by
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
  have hterm : ∀ ρ ∈ S, ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
      Phi η δ ν ε ρ * (x : ℂ) ^ ρ‖ ≤ (1 + ε) * (m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re)) := by
    intro ρ hρ
    have hz := hS hρ
    have hP : Phi η δ ν ε ρ = HM.Gm η δ ρ * Mnu ν (ε * ρ) := by
      unfold Phi Gcont
      rw [if_pos hz.2.1]
    rw [hP, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hM := norm_Mnu_strip hν hε0 hε1 hz.2.1 hz.2.2
    have hm0 : 0 ≤ m ρ := Nat.cast_nonneg _
    have hg0 : 0 ≤ ‖HM.Gm η δ ρ‖ * x ^ ρ.re := by positivity
    calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
          (‖HM.Gm η δ ρ‖ * ‖Mnu ν (ε * ρ)‖) * x ^ ρ.re
        = m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re) * ‖Mnu ν (ε * ρ)‖ := by ring
      _ ≤ m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re) * (1 + ε) :=
          mul_le_mul_of_nonneg_left hM (mul_nonneg hm0 hg0)
      _ = (1 + ε) * (m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re)) := by ring
  have hsum : ∑ ρ ∈ S, m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re) ≤
      (HM.zsum χ univ (fun ρ => ENNReal.ofReal (‖HM.Gm η δ ρ‖ * x ^ ρ.re))).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hZ,
      ENNReal.ofReal_sum_of_nonneg (fun ρ _ => by positivity)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
      (sum_le_zsum χ (fun ρ hρ => ⟨hS hρ, mem_univ ρ⟩) _)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, HM.zmult]
  calc _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
        Phi η δ ν ε ρ * (x : ℂ) ^ ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, (1 + ε) * (m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re)) := Finset.sum_le_sum hterm
    _ = (1 + ε) * ∑ ρ ∈ S, m ρ * (‖HM.Gm η δ ρ‖ * x ^ ρ.re) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by linarith)

/-- **`Core` from the mollified formula and the limit `ε → 0⁺`** (PROVED): at scale `ε` the
twisted sum minus the main term, the residue at `0` and the left-line integral is within
`(1 + ε)·∑_ρ` of `0`; each piece converges (`MollLimit` for the sum, `M ν` continuous with
`M ν(0) = 1` for the rest, dominated by the `L¹` left-line integrand). -/
theorem core_of_moll (hM : MollCore) (hL : MollLimit) (hLD : LeftLD) (hPl : MellinPlancherel) :
    Core := by
  classical
  intro η hreg h0 q _ χ hχ δ x hx
  set Z := HM.zsum χ univ (fun ρ => ENNReal.ofReal (‖HM.Gm η δ ρ‖ * x ^ ρ.re)) with hZdef
  rcases eq_or_ne Z ⊤ with hZt | hZt
  · rw [hZt]
    exact le_top
  obtain ⟨ν, hν⟩ := exists_mollData
  set Zr := Z.toReal with hZr
  have hZr0 : 0 ≤ Zr := ENNReal.toReal_nonneg
  set hI : ℝ → ℂ := fun τ => -LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ with hIdef
  set Y : ℝ → ℂ := fun ε => twF (Fe η δ ν ε) χ x -
      (if q = 1 then Phi η δ ν ε 1 * x else 0) + Rres η δ χ -
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ, hI τ * Mnu ν (ε * sL τ) with hYdef
  -- `Psi` on the left line
  have hPsiL : ∀ ε τ, Psi χ (Phi η δ ν ε) x (sL τ) = hI τ * Mnu ν (ε * sL τ) := by
    intro ε τ
    rw [Psi, Phi, gcont_sL, hIdef]
    ring
  -- `Φ_ε(0) = G(0)`
  have hPhi0 : ∀ ε, Phi η δ ν ε 0 = G0 η δ := by
    intro ε
    unfold Phi Gcont
    rw [if_neg (by simp), if_pos rfl, mul_zero, Mnu_zero hν, mul_one]
  -- the bound at each scale
  have hYb : ∀ ε, 0 < ε → ε ≤ 1 → ‖Y ε‖ ≤ (1 + ε) * Zr := by
    intro ε hε0 hε1
    refine le_of_forall_pos_le_add fun θ hθ => ?_
    obtain ⟨S, hS, hb⟩ := hM η hreg h0 ν hν ε hε0 q χ hχ δ x hx θ hθ
    have hsum := norm_sum_le_zsum (η := η) (δ := δ) hν hε0 hε1 hx hS hZt
    have heq : Y ε = (twF (Fe η δ ν ε) χ x - resSum χ (Phi η δ ν ε) x S -
        ((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ, Psi χ (Phi η δ ν ε) x (sL τ)) -
        ∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
          Phi η δ ν ε ρ * (x : ℂ) ^ ρ := by
      simp only [hYdef, resSum, hPsiL, Rres, hPhi0]
      split_ifs <;> ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    linarith
  -- the limit
  have hMc : Continuous (Mnu ν) := (differentiable_Mnu hν).continuous
  have hM0 : Tendsto (fun w : ℂ => Mnu ν w) (𝓝 0) (𝓝 1) := by
    have := hMc.tendsto 0
    rwa [Mnu_zero hν] at this
  have hεC : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0)
    rw [Complex.ofReal_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hA : Tendsto (fun ε : ℝ => if q = 1 then Phi η δ ν ε 1 * x else 0) (𝓝[>] 0)
      (𝓝 (if q = 1 then MajSp.mainFT η δ * x else 0)) := by
    split_ifs
    · have h1 : ∀ ε : ℝ, Phi η δ ν ε 1 * x = HM.Gm η δ 1 * x * Mnu ν ((ε : ℂ) * 1) := by
        intro ε
        unfold Phi Gcont
        rw [if_pos (by norm_num)]
        ring
      simp_rw [h1, gm_one]
      have h3 := hεC.mul_const (1 : ℂ)
      rw [zero_mul] at h3
      have h2 := (hM0.comp h3).const_mul (HM.Gm η δ 1 * x)
      rw [mul_one, gm_one] at h2
      exact h2
    · exact tendsto_const_nhds
  have hB : Tendsto (fun ε : ℝ => ∫ τ : ℝ, hI τ * Mnu ν (ε * sL τ)) (𝓝[>] 0)
      (𝓝 (∫ τ : ℝ, hI τ)) := by
    have hint := integrable_ileft hLD hPl hreg hχ δ hx
    refine tendsto_integral_filter_of_dominated_convergence (fun τ => 2 * ‖hI τ‖) ?_ ?_
      (hint.norm.const_mul 2) ?_
    · refine Eventually.of_forall fun ε => ?_
      have hsL : Continuous sL := by unfold sL; fun_prop
      exact hint.aestronglyMeasurable.mul
        (hMc.comp (continuous_const.mul hsL)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      refine Eventually.of_forall fun τ => ?_
      rw [norm_mul, mul_comm 2]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_Mnu_le hν _).trans ?_
      have hre : ((ε : ℂ) * sL τ).re = -(ε / 2) := by simp [sL]; ring
      rw [hre, abs_neg, abs_of_pos (by linarith [hε.1])]
      calc (2 : ℝ) ^ (ε / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hε.2])
        _ = 2 := Real.rpow_one 2
    · refine Eventually.of_forall fun τ => ?_
      have h3 := hεC.mul_const (sL τ)
      rw [zero_mul] at h3
      have h1 := (hM0.comp h3).const_mul (hI τ)
      rw [mul_one] at h1
      exact h1
  have hTw := hL η hreg h0 ν hν q χ δ x hx
  have hYlim : Tendsto Y (𝓝[>] 0) (𝓝 ((x : ℂ) * MajSp.err η χ δ x + Rres η δ χ -
      Ileft η δ χ x)) := by
    have hlim := ((hTw.sub hA).add_const (Rres η δ χ)).sub (hB.const_smul ((2 * Real.pi)⁻¹ : ℝ))
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hxe : (x : ℂ) * MajSp.err η χ δ x =
        MajSp.twSum η χ x (δ / x) - (if q = 1 then MajSp.mainFT η δ * x else 0) := by
      have h1 : (x : ℂ) * (MajSp.twSum η χ x (δ / x) / x) = MajSp.twSum η χ x (δ / x) := by
        field_simp
      unfold MajSp.err
      rw [mul_sub, h1]
      split_ifs <;> ring
    have hval : MajSp.twSum η χ x (δ / x) - (if q = 1 then MajSp.mainFT η δ * x else 0) +
        Rres η δ χ - ((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ, hI τ =
        (x : ℂ) * MajSp.err η χ δ x + Rres η δ χ - Ileft η δ χ x := by
      rw [hxe]
      rfl
    rw [hval] at hlim
    exact hlim
  have hbd : Tendsto (fun ε : ℝ => (1 + ε) * Zr) (𝓝[>] 0) (𝓝 ((1 + 0) * Zr)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.add continuous_id).mul continuous_const).continuousAt.tendsto
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖Y ε‖ ≤ (1 + ε) * Zr := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hYb ε hε.1 hε.2.le
  have hle := le_of_tendsto_of_tendsto hYlim.norm hbd hev
  rw [add_zero, one_mul] at hle
  calc ENNReal.ofReal ‖(x : ℂ) * MajSp.err η χ δ x + Rres η δ χ - Ileft η δ χ x‖
      ≤ ENNReal.ofReal Zr := ENNReal.ofReal_le_ofReal hle
    _ = Z := ENNReal.ofReal_toReal hZt

/-! ## (4) The contour level -/

/-- **`StartLine` (EF3) — PROVED (`startLine_holds`)**: for a weight `F` continuous on `(0, ∞)`
whose Mellin transform converges on `Re s = 3/2`, equals `Φ` there and is integrable along the
line, `∫_{−T}^{T} Ψ(3/2 + iτ) dτ → 2π ∑Λ(n)χ(n)F(n/x)`: Mellin inversion (Mathlib
`mellinInv_mellin_eq`), `−L'/L = ∑Λχ n^{−s}` for `Re s > 1` (`LSeries_twist_vonMangoldt_eq`), and
`integral_tsum`. Templates: `SW/PerronKernel`, `pnt/PsiChi.lean`. -/
def StartLine : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ (F : ℝ → ℂ) (Φ : ℂ → ℂ), ContinuousOn F (Ioi 0) → MellinConvergent F (3 / 2 : ℂ) →
      (∀ τ : ℝ, Φ (3 / 2 + τ * Complex.I) = mellin F (3 / 2 + τ * Complex.I)) →
      Integrable (fun τ : ℝ => Φ (3 / 2 + τ * Complex.I)) →
      ∀ x : ℝ, 0 < x → Tendsto (fun T : ℝ => ∫ τ in (-T)..T, Psi χ Φ x (3 / 2 + τ * Complex.I))
        atTop (𝓝 (2 * Real.pi * twF F χ x))

/-- **LINK [Rectangle] (EF4) — PORT + zero map**: for `Φ` holomorphic on `−1 < Re s < b`,
`b > 3/2`, and a height `T > 0` that is no zero ordinate, the finitely many zeros with `|γ| < T`
form a `Finset` `S` and `∮ Ψ = 2πi·resSum`: residue `Φ(1)x` at the pole of `ζ` (`q = 1`),
`−m(ρ)Φ(ρ)x^ρ` at each zero, `−Φ(0)` at the simple trivial zero `0` of an even `χ` with `q ≠ 1`, and
no other zero of `L` in `[−1/2, 3/2]` (functional equation, `L(1) ≠ 0`,
`LFunction_ne_zero_of_one_le_re`). Port: PNT+ `RectangleIntegral'_eq_sumResiduesIn`. -/
def Rectangle : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ Φ : ℂ → ℂ, (∃ b : ℝ, 3 / 2 < b ∧ DifferentiableOn ℂ Φ {s | -1 < s.re ∧ s.re < b}) →
      ∀ x : ℝ, 0 < x → ∀ T : ℝ, 0 < T → (∀ ρ ∈ HM.zeroSet χ, |ρ.im| ≠ T) →
        ∃ S : Finset ℂ, (↑S : Set ℂ) = {ρ | ρ ∈ HM.zeroSet χ ∧ |ρ.im| < T} ∧
          RectangleIntegral (Psi χ Φ x) (-1 / 2 - T * Complex.I) (3 / 2 + T * Complex.I) =
            2 * Real.pi * Complex.I * resSum χ Φ x S

/-- **LINK [Horizontal] (EF5) — DEEP, THE REAL RISK**: for `Φ` decaying faster than every power
of `|Im s|` on `−1/2 ≤ Re s ≤ 3/2`, every `T₀` has an admissible height `T ≥ T₀` (no zero ordinate)
with `|∫_{−1/2}^{3/2} Ψ(σ − iT) − Ψ(σ + iT) dσ| ≤ θ`. Needs only the crude statement
`∫|L'/L(σ ± iT)|dσ ≤ C(q + T₀)^A` for some `T ∈ [T₀, T₀ + 1]` (Landau/Jensen at `2 + iT₀`,
pigeonhole); proved nowhere (PNT+ `kadiri_thm_3_1_q1_top_horizontal_vanishes` is open even for
`ζ`). -/
def Horizontal : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ Φ : ℂ → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
        ‖Φ s‖ ≤ C / (1 + |s.im|) ^ k) →
      ∀ x : ℝ, 0 < x → ∀ θ : ℝ, 0 < θ → ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 0 < T ∧
        (∀ ρ ∈ HM.zeroSet χ, |ρ.im| ≠ T) ∧
        ‖HIntegral (Psi χ Φ x) (-1 / 2) (3 / 2) (-T) -
          HIntegral (Psi χ Φ x) (-1 / 2) (3 / 2) T‖ ≤ θ

/-- **LINK [Continuation] (EF1) — BUILD**: `Gcont` is holomorphic on `−1 < Re s < b` for some
`b > 3/2`: `M f` is holomorphic where it converges, `−M f'(s + 1)/s` on `−1 < Re s < b − 1`, they
agree there (integration by parts; the boundary terms vanish since `η(0) = 0`), and the singularity
at `0` is removable with value `G(0) = −∫f' log t` (`M f'(1) = ∫f' = 0`). -/
def Continuation : Prop :=
  ∀ η : ℝ → ℝ, HM.AgamonReg η → η 0 = 0 → ∀ δ : ℝ,
    ∃ b : ℝ, 3 / 2 < b ∧ DifferentiableOn ℂ (Gcont η δ) {s | -1 < s.re ∧ s.re < b}

/-- **LINK [MollDecay] (EF2) — BUILD**: `Φ_ε = G_cont·Mν(ε·)` decays faster than every power of
`|Im s|` on `−1/2 ≤ Re s ≤ 3/2`: `G_cont` is bounded there and `ν` is smooth with compact support
(`k` integrations by parts; PNT+ `MellinOfPsi` is the case `k = 1`). -/
def MollDecay : Prop :=
  ∀ η : ℝ → ℝ, HM.AgamonReg η → η 0 = 0 → ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε →
    ∀ (δ : ℝ) (k : ℕ), ∃ C : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖Phi η δ ν ε s‖ ≤ C / (1 + |s.im|) ^ k

/-- **`MollReg` (EF2) — PROVED (`mollReg_holds`)**: `f_ε` is continuous on `(0, ∞)`, its Mellin
transform converges on `Re s = 3/2` and equals `G(s)·Mν(εs)` there (`mellin_mconv` with PNT+
`MellinOfDeltaSpike`). -/
def MollReg : Prop :=
  ∀ η : ℝ → ℝ, HM.AgamonReg η → ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ,
    ContinuousOn (Fe η δ ν ε) (Ioi 0) ∧ MellinConvergent (Fe η δ ν ε) (3 / 2 : ℂ) ∧
      ∀ τ : ℝ, mellin (Fe η δ ν ε) (3 / 2 + τ * Complex.I) =
        HM.Gm η δ (3 / 2 + τ * Complex.I) * Mnu ν (ε * (3 / 2 + τ * Complex.I))

/-- **The rectangle integral, edge by edge.** -/
theorem rect_split (Ψ : ℂ → ℂ) (T : ℝ) :
    RectangleIntegral Ψ (-1 / 2 - T * Complex.I) (3 / 2 + T * Complex.I) =
      HIntegral Ψ (-1 / 2) (3 / 2) (-T) - HIntegral Ψ (-1 / 2) (3 / 2) T +
        Complex.I * (∫ τ in (-T)..T, Ψ (3 / 2 + τ * Complex.I)) -
        Complex.I * ∫ τ in (-T)..T, Ψ (sL τ) := by
  have hzre : (-1 / 2 - (T : ℂ) * Complex.I).re = -1 / 2 := by simp
  have hzim : (-1 / 2 - (T : ℂ) * Complex.I).im = -T := by simp
  have hwre : (3 / 2 + (T : ℂ) * Complex.I).re = 3 / 2 := by simp
  have hwim : (3 / 2 + (T : ℂ) * Complex.I).im = T := by simp
  unfold RectangleIntegral VIntegral
  rw [hzre, hzim, hwre, hwim]
  norm_num [sL]

/-- **Contour bookkeeping** (generic): the right line tends to `2πA`, the left line to `2πB`, the
rectangle identity holds at every admissible height, and admissible heights with small
horizontal integrals exist beyond every bound; then `A − R(S) − B` is as small as we like. -/
theorem bookkeeping {Ψ : ℂ → ℂ} {A B : ℂ} {P : Finset ℂ → Prop} {R : Finset ℂ → ℂ}
    {good : ℝ → Prop}
    (hR : Tendsto (fun T : ℝ => ∫ τ in (-T)..T, Ψ (3 / 2 + τ * Complex.I)) atTop
      (𝓝 (2 * Real.pi * A)))
    (hL : Tendsto (fun T : ℝ => ∫ τ in (-T)..T, Ψ (sL τ)) atTop (𝓝 (2 * Real.pi * B)))
    (hRect : ∀ T : ℝ, good T → ∃ S : Finset ℂ, P S ∧
      RectangleIntegral Ψ (-1 / 2 - T * Complex.I) (3 / 2 + T * Complex.I) =
        2 * Real.pi * Complex.I * R S)
    (hH : ∀ θ : ℝ, 0 < θ → ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ good T ∧
      ‖HIntegral Ψ (-1 / 2) (3 / 2) (-T) - HIntegral Ψ (-1 / 2) (3 / 2) T‖ ≤ θ) :
    ∀ θ : ℝ, 0 < θ → ∃ S : Finset ℂ, P S ∧ ‖A - R S - B‖ ≤ θ := by
  intro θ hθ
  have hc : 0 < 2 * Real.pi := by positivity
  have hθ3 : 0 < 2 * Real.pi * θ / 3 := by positivity
  obtain ⟨T1, hT1⟩ := Metric.tendsto_atTop.mp hR _ hθ3
  obtain ⟨T2, hT2⟩ := Metric.tendsto_atTop.mp hL _ hθ3
  obtain ⟨T, hT, hgood, hHT⟩ := hH _ hθ3 (max T1 T2)
  obtain ⟨S, hPS, hrect⟩ := hRect T hgood
  refine ⟨S, hPS, ?_⟩
  have h1 := hT1 T (le_trans (le_max_left _ _) hT)
  have h2 := hT2 T (le_trans (le_max_right _ _) hT)
  rw [dist_eq_norm] at h1 h2
  rw [rect_split] at hrect
  have key : 2 * (Real.pi : ℂ) * Complex.I * (A - R S - B) =
      Complex.I * (2 * Real.pi * A - ∫ τ in (-T)..T, Ψ (3 / 2 + τ * Complex.I)) -
        Complex.I * (2 * Real.pi * B - ∫ τ in (-T)..T, Ψ (sL τ)) -
        (HIntegral Ψ (-1 / 2) (3 / 2) (-T) - HIntegral Ψ (-1 / 2) (3 / 2) T) := by
    linear_combination hrect
  have hn : ‖2 * (Real.pi : ℂ) * Complex.I * (A - R S - B)‖ = 2 * Real.pi * ‖A - R S - B‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
    ring
  have hb : 2 * Real.pi * ‖A - R S - B‖ ≤ 2 * Real.pi * θ := by
    rw [← hn, key]
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖Complex.I * (2 * Real.pi * A - ∫ τ in (-T)..T, Ψ (3 / 2 + τ * Complex.I))‖ =
        ‖(∫ τ in (-T)..T, Ψ (3 / 2 + τ * Complex.I)) - 2 * Real.pi * A‖ := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_sub_rev]
    have e2 : ‖Complex.I * (2 * Real.pi * B - ∫ τ in (-T)..T, Ψ (sL τ))‖ =
        ‖(∫ τ in (-T)..T, Ψ (sL τ)) - 2 * Real.pi * B‖ := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_sub_rev]
    have h3 := norm_sub_le
      (Complex.I * (2 * Real.pi * A - ∫ τ in (-T)..T, Ψ (3 / 2 + τ * Complex.I)))
      (Complex.I * (2 * Real.pi * B - ∫ τ in (-T)..T, Ψ (sL τ)))
    rw [e1, e2] at h3
    linarith
  exact le_of_mul_le_mul_left hb hc

/-- `Φ_ε` is holomorphic on the strip. -/
theorem phi_diff (hCo : Continuation) {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (h0 : η 0 = 0)
    {ν : ℝ → ℝ} (hν : MollData ν) (ε δ : ℝ) :
    ∃ b : ℝ, 3 / 2 < b ∧ DifferentiableOn ℂ (Phi η δ ν ε) {s | -1 < s.re ∧ s.re < b} := by
  obtain ⟨b, hb, hd⟩ := hCo η hreg h0 δ
  refine ⟨b, hb, hd.mul ?_⟩
  exact ((differentiable_Mnu hν).comp (differentiable_id.const_mul (ε : ℂ))).differentiableOn

/-- `Ψ` on the left line: the `Ileft` integrand times `M ν(ε s)`. -/
theorem psi_sL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (η : ℝ → ℝ) (δ : ℝ)
    (ν : ℝ → ℝ) (ε x τ : ℝ) :
    Psi χ (Phi η δ ν ε) x (sL τ) =
      (-LD χ (sL τ) * Gleft η δ τ * (x : ℂ) ^ sL τ) * Mnu ν (ε * sL τ) := by
  rw [Psi, Phi, gcont_sL]
  ring

/-- **`MollCore` from the contour links** (PROVED): `bookkeeping` with `StartLine` (right line),
`Rectangle` (residues), `Horizontal` (horizontal edges) and the `L¹` left line. -/
theorem mollCore_of_links (hSL : StartLine) (hRe : Rectangle) (hHo : Horizontal)
    (hCo : Continuation) (hDe : MollDecay) (hMR : MollReg) (hLD : LeftLD)
    (hPl : MellinPlancherel) : MollCore := by
  intro η hreg h0 ν hν ε hε q _ χ hχ δ x hx θ hθ
  obtain ⟨b, hb, hdiff⟩ := phi_diff hCo hreg h0 hν ε δ
  obtain ⟨hcont, hconv, hmel⟩ := hMR η hreg ν hν ε hε δ
  have hdec := hDe η hreg h0 ν hν ε hε δ
  -- the right line
  have hline : Continuous fun τ : ℝ => Phi η δ ν ε (3 / 2 + τ * Complex.I) := by
    refine hdiff.continuousOn.comp_continuous (by fun_prop) fun τ => ?_
    have hre : (3 / 2 + (τ : ℂ) * Complex.I).re = 3 / 2 := by simp
    rw [Set.mem_setOf_eq, hre]
    exact ⟨by norm_num, hb⟩
  have hint3 : Integrable fun τ : ℝ => Phi η δ ν ε (3 / 2 + τ * Complex.I) := by
    obtain ⟨C, hC⟩ := hdec 2
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul |C|)
      hline.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    have hs := hC (3 / 2 + τ * Complex.I) (by norm_num) (by norm_num)
    have him : (3 / 2 + (τ : ℂ) * Complex.I).im = τ := by simp
    rw [him] at hs
    have hp : 0 < (1 + |τ|) ^ 2 := by positivity
    have hq : (1 + τ ^ 2) ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ, sq_abs τ]
    calc ‖Phi η δ ν ε (3 / 2 + τ * Complex.I)‖ ≤ C / (1 + |τ|) ^ 2 := hs
      _ ≤ |C| / (1 + |τ|) ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) hp.le
      _ ≤ |C| / (1 + τ ^ 2) := div_le_div_of_nonneg_left (abs_nonneg C) (by positivity) hq
      _ = |C| * (1 + τ ^ 2)⁻¹ := div_eq_mul_inv _ _
  have hΦeq : ∀ τ : ℝ, Phi η δ ν ε (3 / 2 + τ * Complex.I) =
      mellin (Fe η δ ν ε) (3 / 2 + τ * Complex.I) := by
    intro τ
    rw [hmel τ]
    unfold Phi Gcont
    rw [if_pos (by norm_num)]
  have hR := hSL q χ hχ (Fe η δ ν ε) (Phi η δ ν ε) hcont hconv hΦeq hint3 x hx
  -- the left line
  have hintL : Integrable fun τ : ℝ => Psi χ (Phi η δ ν ε) x (sL τ) := by
    have hI := integrable_ileft hLD hPl hreg hχ δ hx
    have hsL : Continuous sL := by unfold sL; fun_prop
    have hMc : Continuous fun τ : ℝ => Mnu ν (ε * sL τ) :=
      (differentiable_Mnu hν).continuous.comp (continuous_const.mul hsL)
    simp_rw [psi_sL]
    refine Integrable.mono' (hI.norm.const_mul ((2 : ℝ) ^ (ε / 2)))
      (hI.aestronglyMeasurable.mul hMc.aestronglyMeasurable) (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_Mnu_le hν _).trans (le_of_eq ?_)
    have hre : ((ε : ℂ) * sL τ).re = -(ε / 2) := by simp [sL]; ring
    rw [hre, abs_neg, abs_of_pos (by linarith)]
  have hL : Tendsto (fun T : ℝ => ∫ τ in (-T)..T, Psi χ (Phi η δ ν ε) x (sL τ)) atTop
      (𝓝 (2 * Real.pi * (((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ, Psi χ (Phi η δ ν ε) x (sL τ)))) := by
    have h := intervalIntegral_tendsto_integral hintL tendsto_neg_atTop_atBot tendsto_id
    have e : (2 * (Real.pi : ℂ)) * (((2 * Real.pi)⁻¹ : ℝ) • ∫ τ : ℝ,
        Psi χ (Phi η δ ν ε) x (sL τ)) = ∫ τ : ℝ, Psi χ (Phi η δ ν ε) x (sL τ) := by
      rw [Complex.real_smul, ← mul_assoc]
      have : (2 * (Real.pi : ℂ)) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
        push_cast
        field_simp
      rw [this, one_mul]
    rw [e]
    exact h
  -- rectangle and horizontal
  have hRect : ∀ T : ℝ, (0 < T ∧ ∀ ρ ∈ HM.zeroSet χ, |ρ.im| ≠ T) →
      ∃ S : Finset ℂ, (↑S : Set ℂ) ⊆ HM.zeroSet χ ∧
        RectangleIntegral (Psi χ (Phi η δ ν ε) x) (-1 / 2 - T * Complex.I)
          (3 / 2 + T * Complex.I) = 2 * Real.pi * Complex.I * resSum χ (Phi η δ ν ε) x S := by
    intro T hT
    obtain ⟨S, hS, he⟩ := hRe q χ hχ (Phi η δ ν ε) ⟨b, hb, hdiff⟩ x hx T hT.1 hT.2
    refine ⟨S, ?_, he⟩
    rw [hS]
    exact fun ρ hρ => hρ.1
  have hH : ∀ θ' : ℝ, 0 < θ' → ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧
      (0 < T ∧ ∀ ρ ∈ HM.zeroSet χ, |ρ.im| ≠ T) ∧
      ‖HIntegral (Psi χ (Phi η δ ν ε) x) (-1 / 2) (3 / 2) (-T) -
        HIntegral (Psi χ (Phi η δ ν ε) x) (-1 / 2) (3 / 2) T‖ ≤ θ' := by
    intro θ' hθ' T₀
    obtain ⟨T, h1, h2, h3, h4⟩ := hHo q χ hχ (Phi η δ ν ε) hdec x hx θ' hθ' T₀
    exact ⟨T, h1, ⟨h2, h3⟩, h4⟩
  exact bookkeeping hR hL hRect hH θ hθ

/-! ## (8) The Mellin convolution theorem (PROVED) -/

/-- `(x/y)`-rescaling of a Mellin integrand: for `x, y > 0`,
`f(y) g(x/y)/y · x^{s−1} = (f(y) y^{s−1}/y) · (x/y)^{s−1} g(x/y)`. -/
theorem mconv_factor (f g : ℝ → ℂ) (s : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1) =
      (f y * (y : ℂ) ^ (s - 1) / y) * ((x / y : ℝ) : ℂ) ^ (s - 1) * g (x / y) := by
  have hxy : x = y * (x / y) := by field_simp
  have hc : (x : ℂ) ^ (s - 1) = (y : ℂ) ^ (s - 1) * ((x / y : ℝ) : ℂ) ^ (s - 1) := by
    conv_lhs => rw [hxy]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (div_pos hx hy).le]
  rw [hc]
  ring

/-- **The Mellin convolution theorem** (Tonelli): for `f, g` continuous on `(0, ∞)` whose Mellin
transforms converge at `s`, `M(f ∗_M g)` converges at `s` and equals `M f(s)·M g(s)`. PNT+
`MellinConvolutionTransform` with its integrability hypothesis discharged: after `x = uy` the
double integrand factors, and `integrable_prod_iff'` reduces to the two single integrals. -/
theorem mellin_mconv {f g : ℝ → ℂ} {s : ℂ} (hfc : ContinuousOn f (Ioi 0))
    (hgc : ContinuousOn g (Ioi 0)) (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (MellinConvolution f g) s ∧
      mellin (MellinConvolution f g) s = mellin f s * mellin g s := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  -- continuity of the double integrand on the open quadrant
  have hFc : ContinuousOn (fun p : ℝ × ℝ => f p.2 * g (p.1 / p.2) / (p.2 : ℂ) *
      (p.1 : ℂ) ^ (s - 1)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    have h2 : (0 : ℝ) < p.2 := hp.2
    have hm2 : MapsTo Prod.snd (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (Ioi (0 : ℝ)) := fun q hq => hq.2
    have hmd : MapsTo (fun q : ℝ × ℝ => q.1 / q.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (Ioi 0) :=
      fun q hq => mem_Ioi.mpr (div_pos hq.1 hq.2)
    have cf : ContinuousWithinAt (fun q : ℝ × ℝ => f q.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) p :=
      (hfc p.2 h2).comp continuousWithinAt_snd hm2
    have cdiv : ContinuousWithinAt (fun q : ℝ × ℝ => q.1 / q.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) p :=
      (continuousAt_fst.div continuousAt_snd h2.ne').continuousWithinAt
    have cg : ContinuousWithinAt (fun q : ℝ × ℝ => g (q.1 / q.2)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
        p :=
      ContinuousWithinAt.comp (g := g) (hgc (p.1 / p.2) (div_pos h1 h2)) cdiv hmd
    have cy : ContinuousWithinAt (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
        p := (Complex.continuous_ofReal.comp continuous_snd).continuousWithinAt
    have cx : ContinuousWithinAt (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) ^ (s - 1))
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) p :=
      ((Complex.continuousAt_ofReal_cpow_const p.1 (s - 1) (Or.inr h1.ne')).comp
        continuous_fst.continuousAt).continuousWithinAt
    exact ((cf.mul cg).div cy (Complex.ofReal_ne_zero.mpr h2.ne')).mul cx
  have hFm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * g (p.1 / p.2) / (p.2 : ℂ) *
      (p.1 : ℂ) ^ (s - 1)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi 0))) := by
    rw [← hprod]
    exact hFc.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  -- the single integrals
  have hGi : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * g u) (Ioi 0) := by
    have := hg
    unfold MellinConvergent at this
    simpa [smul_eq_mul] using this
  have hxint : ∀ y ∈ Ioi (0 : ℝ), Integrable (fun x : ℝ => f (x, y).2 * g ((x, y).1 / (x, y).2) /
      ((x, y).2 : ℂ) * ((x, y).1 : ℂ) ^ (s - 1)) (volume.restrict (Ioi 0)) := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have hsc : IntegrableOn (fun x : ℝ => ((x * y⁻¹ : ℝ) : ℂ) ^ (s - 1) * g (x * y⁻¹))
        (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_right_iff (fun u : ℝ => (u : ℂ) ^ (s - 1) * g u) 0
        (inv_pos.mpr hy'), zero_mul]
      exact hGi
    refine IntegrableOn.congr_fun (hsc.const_mul (f y * (y : ℂ) ^ (s - 1) / y))
      (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    simp only
    rw [mconv_factor f g s hx' hy', ← div_eq_mul_inv]
    ring
  have hynorm : ∀ y ∈ Ioi (0 : ℝ), ∫ x : ℝ, ‖f (x, y).2 * g ((x, y).1 / (x, y).2) /
      ((x, y).2 : ℂ) * ((x, y).1 : ℂ) ^ (s - 1)‖ ∂(volume.restrict (Ioi 0)) =
      (∫ u in Ioi (0 : ℝ), ‖(u : ℂ) ^ (s - 1) * g u‖) * ‖(y : ℂ) ^ (s - 1) • f y‖ := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have e1 : ∫ x : ℝ, ‖f (x, y).2 * g ((x, y).1 / (x, y).2) / ((x, y).2 : ℂ) *
        ((x, y).1 : ℂ) ^ (s - 1)‖ ∂(volume.restrict (Ioi 0)) = ∫ x in Ioi (0 : ℝ),
        ‖f y * (y : ℂ) ^ (s - 1) / y‖ *
          ‖((x * y⁻¹ : ℝ) : ℂ) ^ (s - 1) * g (x * y⁻¹)‖ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx' : (0 : ℝ) < x := hx
      simp only
      rw [mconv_factor f g s hx' hy', ← norm_mul, ← div_eq_mul_inv, mul_assoc]
    rw [e1, integral_const_mul, integral_comp_mul_right_Ioi
      (fun u : ℝ => ‖(u : ℂ) ^ (s - 1) * g u‖) 0 (inv_pos.mpr hy'), zero_mul, inv_inv,
      smul_eq_mul, norm_smul, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy'.le]
    field_simp
  have hF : Integrable (fun p : ℝ × ℝ => f p.2 * g (p.1 / p.2) / (p.2 : ℂ) *
      (p.1 : ℂ) ^ (s - 1)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hxint), ?_⟩
    refine IntegrableOn.congr_fun
      (hf.norm.const_mul (∫ u in Ioi (0 : ℝ), ‖(u : ℂ) ^ (s - 1) * g u‖))
      (fun y hy => ?_) measurableSet_Ioi
    exact (hynorm y hy).symm
  have hF' : IntegrableOn (fun x y => f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0) := by
    rw [IntegrableOn, hprod]
    exact hF
  refine ⟨?_, MellinConvolutionTransform f g s hF'⟩
  -- `M (f ∗ g)` converges: `x ↦ ∫_y F(x, y)` is integrable
  refine IntegrableOn.congr_fun hF.integral_prod_left (fun x _ => ?_) measurableSet_Ioi
  simp only [MellinConvolution, smul_eq_mul]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  exact mul_comm _ _

/-- **`f ∗_M g` is continuous on `(0, ∞)`** when `f` is, and `g` is continuous with support in a
compact `[c, d] ⊂ (0, ∞)` (on `(0, ∞)`): the symmetric form `∫ g(y) f(x/y) dy/y`
(`MellinConvolutionSymmetric`) is dominated near `x₀` by `M·1_{[c,d]}`. -/
theorem continuousOn_mconv {f g : ℝ → ℂ} {c d : ℝ} (hc : 0 < c) (hfc : ContinuousOn f (Ioi 0))
    (hgc : Continuous g) (hgs : ∀ y : ℝ, 0 < y → y ∉ Icc c d → g y = 0) :
    ContinuousOn (MellinConvolution f g) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  refine ContinuousAt.continuousWithinAt ?_
  have heq : (fun x => ∫ y in Ioi (0 : ℝ), g y * f (x / y) / (y : ℂ)) =ᶠ[𝓝 x₀]
      MellinConvolution f g := by
    filter_upwards [Ioi_mem_nhds hx₀'] with x hx
    exact (MellinConvolutionSymmetric f g hx).symm
  refine ContinuousAt.congr ?_ heq
  set K := Icc (x₀ / 2) (2 * x₀) ×ˢ Icc c d with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKpos : ∀ p ∈ K, 0 < p.1 ∧ 0 < p.2 := fun p hp =>
    ⟨lt_of_lt_of_le (by linarith) hp.1.1, lt_of_lt_of_le hc hp.2.1⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => g p.2 * f (p.1 / p.2) / (p.2 : ℂ)) K := by
    intro p hp
    obtain ⟨h1, h2⟩ := hKpos p hp
    have cdiv : ContinuousWithinAt (fun q : ℝ × ℝ => q.1 / q.2) K p :=
      (continuousAt_fst.div continuousAt_snd h2.ne').continuousWithinAt
    have cf : ContinuousWithinAt (fun q : ℝ × ℝ => f (q.1 / q.2)) K p :=
      ContinuousWithinAt.comp (g := f) (hfc (p.1 / p.2) (div_pos h1 h2)) cdiv
        (fun q hq => mem_Ioi.mpr (div_pos (hKpos q hq).1 (hKpos q hq).2))
    have cg : ContinuousWithinAt (fun q : ℝ × ℝ => g q.2) K p :=
      (hgc.comp continuous_snd).continuousWithinAt
    have cy : ContinuousWithinAt (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) K p :=
      (Complex.continuous_ofReal.comp continuous_snd).continuousWithinAt
    exact (cg.mul cf).div cy (Complex.ofReal_ne_zero.mpr h2.ne')
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine continuousAt_of_dominated (bound := fun y => max M 0 * (Icc c d).indicator 1 y) ?_ ?_
    ?_ ?_
  · filter_upwards [Ioi_mem_nhds hx₀'] with x hx
    have hx' : (0 : ℝ) < x := hx
    refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) measurableSet_Ioi
    have hy' : (0 : ℝ) < y := hy
    have cf : ContinuousWithinAt (fun y : ℝ => f (x / y)) (Ioi 0) y :=
      ContinuousWithinAt.comp (g := f) (hfc (x / y) (div_pos hx' hy'))
        (continuousAt_const.div continuousAt_id hy'.ne').continuousWithinAt
        (fun z hz => mem_Ioi.mpr (div_pos hx' hz))
    exact (hgc.continuousWithinAt.mul cf).div
      Complex.continuous_ofReal.continuousWithinAt (Complex.ofReal_ne_zero.mpr hy'.ne')
  · filter_upwards [Icc_mem_nhds (show x₀ / 2 < x₀ by linarith)
      (show x₀ < 2 * x₀ by linarith)] with x hx
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    by_cases hyc : y ∈ Icc c d
    · rw [indicator_of_mem hyc, Pi.one_apply, mul_one]
      exact (hM (x, y) ⟨hx, hyc⟩).trans (le_max_left _ _)
    · rw [hgs y hy' hyc, zero_mul, zero_div, norm_zero]
      exact mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · exact ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (measure_Icc_lt_top.ne) (by simp))).const_mul _ |>.restrict
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    have cf : ContinuousAt (fun x : ℝ => f (x / y)) x₀ :=
      ContinuousAt.comp (g := f) ((hfc (x₀ / y) (div_pos hx₀' hy')).continuousAt
        (Ioi_mem_nhds (div_pos hx₀' hy'))) (continuousAt_id.div_const y)
    exact (continuousAt_const.mul cf).div_const _

/-- **`M ν_ε` converges everywhere** (`ν_ε` continuous, supported in `[2^{−ε}, 2^ε]`). -/
theorem mellinConv_spike {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    MellinConvergent (nuC (DeltaSpike ν ε)) s := by
  have hcont : Continuous (nuC (DeltaSpike ν ε)) :=
    DeltaSpikeOfRealContinuous hε (hν.1.of_le (by simp))
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • nuC (DeltaSpike ν ε) t)
      (Icc (2 ^ (-ε)) (2 ^ ε)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) ht.1
    exact ((Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht'.ne')).smul
      hcont.continuousAt).continuousWithinAt
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht.1
  have h0 : DeltaSpike ν ε t = 0 := DeltaSpikeSupport hε ht0 hν.2.2.1 ht.2
  simp [nuC, h0]

/-- `f = η e(δ ·)` is continuous on `(0, ∞)` under `AgamonReg`. -/
theorem continuousOn_fw {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    ContinuousOn (fw η δ) (Ioi 0) := by
  intro t ht
  have hd := agamon_diff hreg ht
  exact (hasDerivAt_fw hd δ).continuousAt.continuousWithinAt

/-- `M f` converges on `Re s = 3/2` under `AgamonReg` (`η t^{1/2} ∈ L¹`). -/
theorem mellinConv_fw {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ τ : ℝ) :
    MellinConvergent (fw η δ) (3 / 2 + τ * Complex.I) := by
  obtain ⟨-, i2, -, -⟩ := agamon_int hreg
  refine Integrable.mono' i2 ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  · exact ContinuousOn.aestronglyMeasurable (fun t ht =>
      ((Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).continuousWithinAt).smul
        (continuousOn_fw hreg δ t ht)) measurableSet_Ioi
  · have ht' : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', fw, norm_mul, norm_e_eq, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    have hre : (3 / 2 + (τ : ℂ) * Complex.I - 1).re = 1 / 2 := by simp; norm_num
    rw [hre, ← Real.sqrt_eq_rpow, mul_comm]

/-- **`MollReg` HOLDS** (so it is not a link): continuity of `f_ε` on `(0, ∞)`
(`continuousOn_mconv`), and on `Re s = 3/2` convergence of `M f_ε` and
`M f_ε = G·Mν(ε·)` (`mellin_mconv` with PNT+ `MellinOfDeltaSpike`). -/
theorem mollReg_holds : MollReg := by
  intro η hreg ν hν ε hε δ
  have hfc := continuousOn_fw hreg δ
  have hgc : Continuous (nuC (DeltaSpike ν ε)) :=
    DeltaSpikeOfRealContinuous hε (hν.1.of_le (by simp))
  have hsupp : ∀ y : ℝ, 0 < y → y ∉ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε) →
      nuC (DeltaSpike ν ε) y = 0 := by
    intro y hy hyn
    simp [nuC, DeltaSpikeSupport hε hy.le hν.2.2.1 hyn]
  refine ⟨continuousOn_mconv (by positivity) hfc hgc hsupp, ?_, fun τ => ?_⟩
  · have h := (mellin_mconv hfc hgc.continuousOn (mellinConv_fw hreg δ 0)
      (mellinConv_spike hν hε _)).1
    unfold Fe
    simpa using h
  · unfold Fe
    rw [(mellin_mconv hfc hgc.continuousOn (mellinConv_fw hreg δ τ)
      (mellinConv_spike hν hε _)).2]
    rw [HM.Gm, Mnu]
    congr 1
    exact MellinOfDeltaSpike ν hε _

/-! ## Mellin–Plancherel on `Re s = 1/2` (PROVED) -/

section Plancherel

open scoped FourierTransform

/-- `u ↦ e^{−u}` has derivative `−e^{−u}` (copied from Mathlib's private
`rexp_neg_deriv_aux`, `Mathlib/Analysis/MellinInversion.lean`). -/
theorem rexp_neg_deriv' :
    ∀ x ∈ univ, HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

/-- `u ↦ e^{−u}` maps `ℝ` onto `(0, ∞)` (Mathlib's private `rexp_neg_image_aux`). -/
theorem rexp_neg_image' : Real.exp ∘ Neg.neg '' univ = Ioi (0 : ℝ) := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ,
    Real.range_exp]

/-- `u ↦ e^{−u}` is injective (Mathlib's private `rexp_neg_injOn_aux`). -/
theorem rexp_neg_injOn' : univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- The Jacobian identity behind `mellin_eq_fourier`, for `ℂ`-valued functions (Mathlib's
private `rexp_cexp_aux`, re-proved for `E = ℂ`). -/
theorem rexp_cexp' (x : ℝ) (s f : ℂ) :
    Real.exp (-x) • Complex.exp (-↑x) ^ (s - 1) • f = Complex.exp (-s * ↑x) • f := by
  rw [Complex.real_smul, smul_eq_mul, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg), ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- **`M F` on `Re s = σ` is the Fourier transform of `g(u) = e^{−σu} F(e^{−u})`, and `g ∈ L¹`**
(the first half of Mathlib's proof of `mellinInv_mellin_eq`). -/
theorem integrable_gSigma (σ : ℝ) {F : ℝ → ℂ} (hF : MellinConvergent F σ) :
    Integrable fun u : ℝ => Real.exp (-σ * u) • F (Real.exp (-u)) := by
  have hf := hF
  rw [MellinConvergent, ← rexp_neg_image', integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv' rexp_neg_injOn', integrableOn_univ] at hf
  refine hf.congr (ae_of_all _ fun u => ?_)
  simp only [Function.comp_apply]
  rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.ofReal_exp, Complex.ofReal_neg,
    rexp_cexp', Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
  push_cast
  try ring

/-- `g(u) = e^{−u/2} F(e^{−u})`. -/
noncomputable def gHalf (F : ℝ → ℂ) (u : ℝ) : ℂ := Real.exp (-(1 / 2 : ℝ) * u) • F (Real.exp (-u))

/-- **`M F(1/2 + iτ) = 𝓕 g(τ/2π)`** (Mathlib `mellin_eq_fourier`). -/
theorem mellin_sH_eq (F : ℝ → ℂ) (τ : ℝ) :
    mellin F (sH τ) = 𝓕 (gHalf F) (τ / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hre : (sH τ).re = 1 / 2 := by simp [sH]
  have him : (sH τ).im = τ := by simp [sH]
  rw [hre, him]
  rfl

/-- `|g(u)|² = e^{−u}|F(e^{−u})|²`. -/
theorem norm_sq_gHalf (F : ℝ → ℂ) (u : ℝ) :
    ‖gHalf F u‖ ^ 2 = Real.exp (-u) * ‖F (Real.exp (-u))‖ ^ 2 := by
  rw [gHalf, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, sq (Real.exp _),
    ← Real.exp_add]
  congr 2
  ring

/-- `∫ |g|² = ∫_0^∞ |F|²` (the substitution `t = e^{−u}`). -/
theorem lint_gHalf (F : ℝ → ℂ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (‖gHalf F u‖ ^ 2) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖F t‖ ^ 2) := by
  rw [← rexp_neg_image', lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    rexp_neg_deriv' rexp_neg_injOn', Measure.restrict_univ]
  refine lintegral_congr fun u => ?_
  rw [norm_sq_gHalf, abs_neg, abs_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

/-- **Mellin–Plancherel on `Re s = 1/2`, PROVED** (so `MellinPlancherel` is a theorem): the
Fourier side (`mellin_sH_eq`), Bessel's inequality on every band (`FourierBessel.bessel`),
`integrable_of_intervalIntegral_norm_bounded`, the rescaling `τ = 2πξ`, and `∫|g|² = ∫|F|²`. -/
theorem mellinPlancherel_holds : MellinPlancherel := by
  intro F hF
  have hpi : 0 < 2 * Real.pi := by positivity
  have hg : Integrable (gHalf F) := by
    have hF' : MellinConvergent F ((1 / 2 : ℝ) : ℂ) := by
      have e : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
      rw [e]
      exact hF
    exact integrable_gSigma (1 / 2) hF'
  have hFc : Continuous (𝓕 (gHalf F)) := FourierBessel.continuous_fourier _ hg
  have hcont : Continuous fun τ : ℝ => mellin F (sH τ) := by
    simp_rw [mellin_sH_eq]
    exact hFc.comp (continuous_id.div_const _)
  refine ⟨hcont, ?_⟩
  rw [← lint_gHalf]
  by_cases htop : ∫⁻ u : ℝ, ENNReal.ofReal (‖gHalf F u‖ ^ 2) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpi).ne']
    exact le_top
  have hg2 : Integrable fun u => ‖gHalf F u‖ ^ 2 := by
    refine ⟨hg.aestronglyMeasurable.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => by positivity)]
    exact lt_top_iff_ne_top.mpr htop
  have hb : ∀ w : ℝ, 0 ≤ w → ∫ ξ in (-w)..w, ‖𝓕 (gHalf F) ξ‖ ^ 2 ≤ ∫ u, ‖gHalf F u‖ ^ 2 :=
    fun w hw => FourierBessel.bessel _ hg hg2 w hw
  have hFi : Integrable fun ξ => ‖𝓕 (gHalf F) ξ‖ ^ 2 := by
    refine integrable_of_intervalIntegral_norm_bounded (∫ u, ‖gHalf F u‖ ^ 2)
      (fun i => (hFc.norm.pow 2).integrableOn_Ioc) tendsto_neg_atTop_atBot tendsto_id ?_
    filter_upwards [eventually_ge_atTop 0] with w hw
    simp only [id, norm_pow, norm_norm]
    exact hb w hw
  have hFint : ∫ ξ, ‖𝓕 (gHalf F) ξ‖ ^ 2 ≤ ∫ u, ‖gHalf F u‖ ^ 2 :=
    le_of_tendsto (intervalIntegral_tendsto_integral hFi tendsto_neg_atTop_atBot tendsto_id)
      (eventually_atTop.mpr ⟨0, fun w hw => hb w hw⟩)
  have hsc : ∫ τ : ℝ, ‖mellin F (sH τ)‖ ^ 2 = 2 * Real.pi * ∫ ξ, ‖𝓕 (gHalf F) ξ‖ ^ 2 := by
    simp_rw [mellin_sH_eq]
    rw [Measure.integral_comp_div (fun ξ => ‖𝓕 (gHalf F) ξ‖ ^ 2) (2 * Real.pi), smul_eq_mul,
      abs_of_pos hpi]
  have hMi : Integrable fun τ : ℝ => ‖mellin F (sH τ)‖ ^ 2 := by
    simp_rw [mellin_sH_eq]
    exact hFi.comp_div hpi.ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hMi (ae_of_all _ fun _ => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal hg2 (ae_of_all _ fun _ => by positivity),
    ← ENNReal.ofReal_mul hpi.le, hsc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hFint hpi.le)

end Plancherel

/-! ## (10) `StartLine` (EF3), PROVED: Mellin inversion on `Re s = 3/2` -/

/-- **`−L'/L = ∑ χ(n)Λ(n)n^{−s}`** on `Re s > 1` (from `SW.neg_logDeriv_LFunction_eq`; the tsum
form follows ours in `pnt/PsiChi.lean`, `LogDerivativeDirichletChi`). -/
theorem neg_LD_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -LD χ s = ∑' n : ℕ, χ (n : ZMod q) * (Λ n : ℂ) / (n : ℂ) ^ s := by
  rw [LD, logDeriv_apply, ← neg_div, SW.neg_logDeriv_LFunction_eq χ hs, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]

/-- `∑ Λ(n)/n^σ < ∞` for `σ > 1` (as in `pnt/PsiChi.lean`). -/
theorem summable_vM {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => Λ n / (n : ℝ) ^ σ := by
  have h2 := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simp only [Complex.ofReal_re]; linarith)).norm
  refine Summable.of_nonneg_of_le (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_) h2
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [norm_div, show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The point `3/2 + iτ`. -/
theorem re_three_halves (τ : ℝ) : ((3 / 2 : ℂ) + τ * Complex.I).re = 3 / 2 := by simp

/-- **`StartLine` HOLDS** (EF3): `Ψ(3/2 + iτ) = ∑_n χ(n)Λ(n)n^{−s}Φ(s)x^s`; each summand
integrates to `2π χ(n)Λ(n)F(n/x)` by Mellin inversion (`mellinInv_mellin_eq`) at `y = n/x`, the
exchange of `∫` and `∑` is dominated by `∑Λ(n)n^{−3/2}·x^{3/2}·|Φ|` (`integral_tsum`), and the
truncated integrals converge (`intervalIntegral_tendsto_integral`). -/
theorem startLine_holds : StartLine := by
  intro q _ χ _ F Φ hFc hFm hΦ hΦi x hx
  have h32 : ((3 / 2 : ℝ) : ℂ) = (3 / 2 : ℂ) := by push_cast; ring
  set term : ℕ → ℝ → ℂ := fun n τ => χ (n : ZMod q) * (Λ n : ℂ) /
      (n : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I) * Φ (3 / 2 + τ * Complex.I) *
        (x : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I) with htermdef
  have hPsi : ∀ τ : ℝ, Psi χ Φ x (3 / 2 + τ * Complex.I) = ∑' n, term n τ := by
    intro τ
    rw [Psi, neg_LD_eq_tsum χ (by rw [re_three_halves]; norm_num), ← tsum_mul_right,
      ← tsum_mul_right]
  -- pointwise bound
  have hbound : ∀ (n : ℕ) (τ : ℝ), ‖term n τ‖ ≤
      Λ n / (n : ℝ) ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) * ‖Φ (3 / 2 + τ * Complex.I)‖ := by
    intro n τ
    rcases eq_or_ne n 0 with rfl | hn
    · simp [htermdef]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnorm_n : ‖(n : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I)‖ = (n : ℝ) ^ (3 / 2 : ℝ) := by
        rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hn0, re_three_halves]
      have hnorm_x : ‖(x : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I)‖ = x ^ (3 / 2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, re_three_halves]
      have hχ1 : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      have hΛ : ‖(Λ n : ℂ)‖ = Λ n := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simp only [htermdef]
      rw [norm_mul, norm_mul, norm_div, norm_mul, hnorm_n, hnorm_x, hΛ]
      have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have hnp : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
      have hxp : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.le _
      have hΦ0 := norm_nonneg (Φ (3 / 2 + τ * Complex.I))
      have h1 : ‖χ (n : ZMod q)‖ * Λ n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ Λ n / (n : ℝ) ^ (3 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith) hnp.le
      calc ‖χ (n : ZMod q)‖ * Λ n / (n : ℝ) ^ (3 / 2 : ℝ) * ‖Φ (3 / 2 + τ * Complex.I)‖ *
            x ^ (3 / 2 : ℝ)
          ≤ Λ n / (n : ℝ) ^ (3 / 2 : ℝ) * ‖Φ (3 / 2 + τ * Complex.I)‖ * x ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hΦ0) hxp
        _ = _ := by ring
  -- measurability of the summands
  have hΦm : AEStronglyMeasurable (fun τ : ℝ => Φ (3 / 2 + τ * Complex.I)) volume :=
    hΦi.aestronglyMeasurable
  have hline : Continuous fun τ : ℝ => (3 / 2 : ℂ) + τ * Complex.I := by fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (term n) volume := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [htermdef, ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero,
        zero_div, zero_mul]
      exact aestronglyMeasurable_const
    · have hc1 : Continuous fun τ : ℝ => (n : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I) :=
        hline.const_cpow (Or.inl (by exact_mod_cast hn))
      have hc2 : Continuous fun τ : ℝ => (x : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I) :=
        hline.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      exact ((continuous_const.div hc1 fun τ => by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
        exact Complex.exp_ne_zero _).aestronglyMeasurable.mul hΦm).mul
          hc2.aestronglyMeasurable
  -- the summable majorant
  have hsum : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (3 / 2 : ℝ) := summable_vM (by norm_num)
  set K : ℝ := (∑' n : ℕ, Λ n / (n : ℝ) ^ (3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) with hK
  have hlint : ∑' n : ℕ, ∫⁻ τ : ℝ, ‖term n τ‖ₑ ≠ ⊤ := by
    have h1 : ∀ n : ℕ, ∫⁻ τ : ℝ, ‖term n τ‖ₑ ≤ ENNReal.ofReal (Λ n / (n : ℝ) ^ (3 / 2 : ℝ) *
        x ^ (3 / 2 : ℝ)) * ∫⁻ τ : ℝ, ‖Φ (3 / 2 + τ * Complex.I)‖ₑ := by
      intro n
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun τ => ?_
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul
        (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hx.le _))]
      exact ENNReal.ofReal_le_ofReal (hbound n τ)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hx.le _))
      (hsum.mul_right _)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦi.hasFiniteIntegral.ne
  -- each summand integrates to `2π χ(n)Λ(n)F(n/x)`
  have hterm : ∀ n : ℕ, ∫ τ : ℝ, term n τ =
      2 * Real.pi * ((Λ n : ℂ) * χ (n : ZMod q) * F ((n : ℝ) / x)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [htermdef]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hy : (0 : ℝ) < (n : ℝ) / x := div_pos hn0 hx
      have hconv : MellinConvergent F ((3 / 2 : ℝ) : ℂ) := by rw [h32]; exact hFm
      have hvert : Complex.VerticalIntegrable (mellin F) (3 / 2 : ℝ) := by
        refine hΦi.congr (Eventually.of_forall fun τ => ?_)
        simp only [h32]
        exact hΦ τ
      have hinv := mellinInv_mellin_eq (3 / 2 : ℝ) F hy hconv hvert
        ((hFc _ hy).continuousAt (Ioi_mem_nhds hy))
      rw [mellinInv, h32] at hinv
      -- the summand, as `χ(n)Λ(n)·(n/x)^{−s}·M F(s)`
      have hsummand : ∀ τ : ℝ, term n τ = χ (n : ZMod q) * (Λ n : ℂ) *
          ((((n : ℝ) / x : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + τ * Complex.I)) •
            mellin F ((3 / 2 : ℂ) + τ * Complex.I)) := by
        intro τ
        have hr := SW.cpow_ratio x n hx hn0 ((3 / 2 : ℂ) + τ * Complex.I)
        rw [smul_eq_mul, Complex.cpow_neg, ← hΦ τ]
        have hxn : (((n : ℝ) / x : ℝ) : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I) =
            ((((x : ℝ) / n : ℝ) : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I))⁻¹ := by
          rw [← Complex.inv_cpow _ _ (by
            rw [Complex.arg_ofReal_of_nonneg (by positivity)]
            exact Real.pi_ne_zero.symm)]
          congr 1
          rw [Complex.ofReal_div, Complex.ofReal_div, inv_div]
        rw [hxn, inv_inv, ← hr]
        simp only [htermdef]
        rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring]
        ring
      rw [integral_congr_ae (Eventually.of_forall hsummand), integral_const_mul]
      have hI : ∫ τ : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + τ * Complex.I)) •
          mellin F ((3 / 2 : ℂ) + τ * Complex.I) = 2 * Real.pi * F ((n : ℝ) / x) := by
        rw [← hinv, Complex.real_smul, ← mul_assoc]
        have hc : 2 * (Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ)) : ℂ) = 1 := by
          have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
          push_cast
          field_simp
        rw [hc, one_mul]
      rw [hI]
      ring
  -- assemble
  have hPsiInt : Integrable fun τ : ℝ => Psi χ Φ x (3 / 2 + τ * Complex.I) := by
    refine Integrable.mono' (hΦi.norm.const_mul K) ?_ (Eventually.of_forall fun τ => ?_)
    · have hc2 : Continuous fun τ : ℝ => (x : ℂ) ^ ((3 / 2 : ℂ) + τ * Complex.I) :=
        hline.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      exact ((((measurable_LD χ).comp hline.measurable).aestronglyMeasurable.neg.mul
        hΦm).mul hc2.aestronglyMeasurable)
    · have hsn : Summable fun n : ℕ => ‖term n τ‖ :=
        Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbound n τ)
          ((hsum.mul_right _).mul_right _)
      rw [hPsi]
      refine (norm_tsum_le_tsum_norm hsn).trans ?_
      refine (Summable.tsum_le_tsum (fun n => hbound n τ) hsn
        ((hsum.mul_right _).mul_right _)).trans (le_of_eq ?_)
      rw [tsum_mul_right, tsum_mul_right, hK]
  have hlim := intervalIntegral_tendsto_integral hPsiInt tendsto_neg_atTop_atBot tendsto_id
  have hval : ∫ τ : ℝ, Psi χ Φ x (3 / 2 + τ * Complex.I) = 2 * Real.pi * twF F χ x := by
    simp_rw [hPsi]
    rw [integral_tsum hmeas hlint]
    simp_rw [hterm]
    rw [tsum_mul_left]
    rfl
  rw [hval] at hlim
  exact hlim

/-! ## (6) The headline and its pin -/

/-- **`HM.ExplicitFormula` (`lem:agamon`, majarcs 2884-3189) FROM SIX NAMED LINKS**, by
application only: `mollCore_of_links` → `core_of_moll` → `agamon_of_core`, with the start line
(`startLine_holds`), Mellin–Plancherel (`mellinPlancherel_holds`) and the regularity of `f_ε`
(`mollReg_holds`) PROVED. -/
theorem agamon_of_links (hRe : Rectangle) (hHo : Horizontal) (hCo : Continuation)
    (hDe : MollDecay) (hML : MollLimit) (hLD : LeftLD) : HM.ExplicitFormula :=
  agamon_of_core
    (core_of_moll (mollCore_of_links startLine_holds hRe hHo hCo hDe mollReg_holds hLD
      mellinPlancherel_holds) hML hLD mellinPlancherel_holds) hLD mellinPlancherel_holds

/-- **The pin**: `HM.ExplicitFormula` is, by `rfl`, the statement transcribed from
`HelfMajSpine.lean` 200-206 (so the headline above proves exactly that statement). -/
theorem agamon_statement : HM.ExplicitFormula = (∀ η : ℝ → ℝ, HM.AgamonReg η →
    η 0 = 0 → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ δ x : ℝ, 0 < x →
        ENNReal.ofReal (x * ‖MajSp.err η χ δ x‖) ≤
          HM.zsum χ univ (fun ρ => ENNReal.ofReal (‖HM.Gm η δ ρ‖ * x ^ ρ.re)) +
            ENNReal.ofReal (HM.c0 η δ + (Real.log q + 8) *
              (MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η) / Real.sqrt x)) := rfl

/-! ## (7) `lem:crepe`, corrected (`ternvin.tex` 5454-5528) -/

/-- **`η₂ ∗_M ν_ε`**, the mollified `η₂` (`η₂` has kinks at `1/4, 1/2, 1`, so it is not `C¹` and
`HM.ExplicitFormula` cannot take it directly; the mollified weight is smooth on `(0, ∞)` and
vanishes near `0`). -/
noncomputable def eta2e (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution HW.eta2 (DeltaSpike ν ε)

/-- **LINK [RosserL17] — Rosser 1941, Lemma 17, CITED (an OWNER question)**, as Helfgott uses it
(`κ₁ = 0.0463`): the zeros of `ζ` with `|γ| ≤ T₀ = 3.061·10¹⁰`, counted with multiplicity, have
`∑ 1/|ρ|² ≤ 0.0463` (true value `0.046191…`: under RH to `T₀` each term is `1/(ρ(1−ρ))`, all
terms of `∑_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π` have positive real part). Stated with the RH input as
a hypothesis, which only weakens it; `PC.PlattTrudgian` supplies it. -/
def RosserL17 : Prop :=
  PC.ZetaRHTo 3.061e10 →
    HM.zsum (1 : DirichletCharacter ℂ 1) {s | |s.im| ≤ 3.061e10}
      (fun ρ => ENNReal.ofReal (1 / ‖ρ‖ ^ 2)) ≤ ENNReal.ofReal 0.0463

/-- **LINK [RamareSaouterL2] — Ramaré–Saouter 2003, Lemma 2, CITED (an OWNER question)**, at
`T₀ = 3.061·10¹⁰`, `m = 1`, in the form Helfgott derives from it for `eq:shim`:
`∑_{|γ| > T₀} 1/|ρ|² ≤ (1/(πT₀) + 5.36/T₀²)·log(eT₀/2π)` (`= 2.4237·10⁻¹⁰`; `rs_value` bounds it
by `2.5·10⁻¹⁰`). Restricted to the one instance used. -/
def RamareSaouterL2 : Prop :=
  HM.zsum (1 : DirichletCharacter ℂ 1) {s | 3.061e10 < |s.im|}
      (fun ρ => ENNReal.ofReal (1 / ‖ρ‖ ^ 2)) ≤
    ENNReal.ofReal ((1 / (Real.pi * 3.061e10) + 5.36 / 3.061e10 ^ 2) *
      Real.log (Real.exp 1 * 3.061e10 / (2 * Real.pi)))

/-- **LINK [Eta2Reg] — BUILD**: `η₂ ∗_M ν_ε` satisfies `lem:agamon`'s hypotheses and vanishes at
`0` (its support is `[2^{−ε}/4, 2^ε]`; `C^∞` on `(0, ∞)` since `ν_ε` is). -/
def Eta2Reg : Prop :=
  ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    HM.AgamonReg (eta2e ν ε) ∧ eta2e ν ε 0 = 0

/-- **LINK [Eta2Norms] — BUILD**: `c₀(η₂ ∗_M ν_ε, 0) ≤ 8(1 + ε)` and `|(η₂ ∗_M ν_ε)'|₂ ≤ 7(1 + ε)`.
For `η₂` itself `c₀ = (2/3)(8 + 4) = 8` and `|η₂'|₂ = 4√3 = 6.928` (mpmath); Mellin convolution
with `ν_ε` (mass `1`, support `[2^{−ε}, 2^ε]`) multiplies each weighted norm by at most
`2^{ε/2} ≤ 1 + ε` (Minkowski). -/
def Eta2Norms : Prop :=
  ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    HM.c0 (eta2e ν ε) 0 ≤ 8 * (1 + ε) ∧ MajSp.l2 (deriv (eta2e ν ε)) ≤ 7 * (1 + ε)

/-- **`Eta2Mellin` — PROVED (`eta2Mellin_holds`)**: in the critical strip
`|M(η₂ ∗_M ν_ε)(s)| ≤ (1 + ε)·4|1 − 2^{−s}|²/|s|²`: `M η₂ = 4((1 − 2^{−s})/s)²` (NOT `eq:envy`'s
printed `((1 − 2^{−s})/s)²`, finding F-A) and `|Mν_ε(s)| = |Mν(εs)| ≤ 2^{ε Re s} ≤ 1 + ε`
(`norm_Mnu_strip`). -/
def Eta2Mellin : Prop :=
  ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ‖HM.Gm (eta2e ν ε) 0 s‖ ≤ (1 + ε) * (4 * ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2)

/-- **`Eta2Main` — PROVED (`eta2Main_holds`)**: the main term
`∫₀^∞ η₂ ∗_M ν_ε = (∫η₂)·Mν(ε) = Mν(ε) ≤ 1 + ε` (`∫η₂ = 1`). -/
def Eta2Main : Prop :=
  ∀ ν : ℝ → ℝ, MollData ν → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (MajSp.mainFT (eta2e ν ε) 0).re ≤ 1 + ε

/-- **`Eta2Conv` — PROVED (`eta2Conv_holds`)**: `∑Λ(n)(η₂ ∗_M ν_ε)(n/x) → ∑Λ(n)η₂(n/x)` as
`ε → 0⁺` (finitely many `n`; `|η₂ ∗_M ν_ε − η₂| ≤ 4ε log 2`). -/
def Eta2Conv : Prop :=
  ∀ ν : ℝ → ℝ, MollData ν → ∀ x : ℝ, 0 < x →
    Tendsto (fun ε => ∑' n : ℕ, Λ n * eta2e ν ε ((n : ℝ) / x)) (𝓝[>] 0) (𝓝 (GS.sEta2 x))

/-- **`lem:crepe`, CORRECTED** (finding F-A): with RH to `T₀ = 3.061·10¹⁰`, for `x ≥ 2000`,
`S(x) = ∑Λ(n)η₂(n/x) ≤ (1 + 4.1·10⁻⁹)x + 0.8√x`. The true constants of the argument are
`4(3/2 + √2)κ₁ = 0.5397` on `√x` and `16·2.5·10⁻¹⁰` on `x`, plus the `O(1)` of
`HM.ExplicitFormula` (`c₀ + 8|η₂'|₂/√x ≤ 8 + 56/√x`), absorbed at `x ≥ 2000`. Implied by
`HC.Crepe` (`crepeC_of_crepe`). -/
def CrepeC : Prop :=
  PC.ZetaRHTo 3.061e10 → ∀ x : ℝ, 2000 ≤ x →
    GS.sEta2 x ≤ (1 + 4.1e-9) * x + 0.8 * Real.sqrt x

/-- **`GS.Austeria` from the corrected `lem:crepe`** — `HC.austeria_of_cited` with `CrepeC` in
place of `HC.Crepe` (`0.8√x ≤ 0.0448x` once `√x ≥ 44`). -/
theorem austeria_of_citedC (z : PC.PlattTrudgian) (gr : HC.AusteriaGridCited)
    (wi : HC.AusteriaWindowCited) (lp : HC.AusteriaLip) (cr : CrepeC) : GS.Austeria := by
  intro Y hY
  rcases lt_or_ge Y 2000 with h | h
  · by_cases hw : Y ∈ HC.austW
    · exact wi Y hw
    · obtain ⟨k, hk, hs⟩ := gr Y hY h hw
      have := lp Y hY k hk
      linarith
  · have hz : PC.ZetaRHTo 3.061e10 := PC.zetaRHTo_mono (T := 3 * 10 ^ 12) (by norm_num) z
    have hc := cr hz Y h
    have hs44 : (44 : ℝ) ≤ Real.sqrt Y := by
      have h1 : Real.sqrt (44 ^ 2) ≤ Real.sqrt Y := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by norm_num)] at h1
    have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt (by linarith)
    have h0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    have h1 : 0.8 * Real.sqrt Y ≤ 0.0448 * Y := by nlinarith
    linarith

/-- `ZetaRHTo T` is `GRHTo 1 T` (`L(s, 1 mod 1) = ζ(s)`). -/
theorem grhTo_one {T : ℝ} (h : PC.ZetaRHTo T) : HM.GRHTo (1 : DirichletCharacter ℂ 1) T := by
  intro s hs hT
  rw [HM.zeroSet, Set.mem_setOf_eq, DirichletCharacter.LFunction_modOne_eq] at hs
  exact h s hs.1 hs.2.1 hs.2.2 hT

/-- The Ramaré–Saouter tail at `T₀ = 3.061·10¹⁰`, as a number: `≤ 2.5·10⁻¹⁰`. -/
theorem rs_value : (1 / (Real.pi * 3.061e10) + 5.36 / 3.061e10 ^ 2) *
    Real.log (Real.exp 1 * 3.061e10 / (2 * Real.pi)) ≤ 2.5e-10 := by
  have hpi := Real.pi_gt_d6
  have hlog : Real.log (Real.exp 1 * 3.061e10 / (2 * Real.pi)) ≤ 24 := by
    have hy : 0 < Real.exp 1 * 3.061e10 / (2 * Real.pi) := by positivity
    have h := HM.log_le_nat 24 hy ?_
    · exact_mod_cast h
    have he := Real.exp_one_lt_d9
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hl0 : 0 ≤ Real.log (Real.exp 1 * 3.061e10 / (2 * Real.pi)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have he := Real.exp_one_gt_d9
    nlinarith [Real.pi_lt_d6]
  have hA : 1 / (Real.pi * 3.061e10) + 5.36 / 3.061e10 ^ 2 ≤ 1.0399e-11 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hA0 : 0 ≤ 1 / (Real.pi * 3.061e10) + 5.36 / 3.061e10 ^ 2 := by positivity
  calc (1 / (Real.pi * 3.061e10) + 5.36 / 3.061e10 ^ 2) *
        Real.log (Real.exp 1 * 3.061e10 / (2 * Real.pi))
      ≤ 1.0399e-11 * 24 := mul_le_mul hA hlog hl0 (by norm_num)
    _ ≤ 2.5e-10 := by norm_num

/-- `(1 + 2^{−1/2})² ≤ 2.91422`. -/
theorem one_add_rpow_half_sq : (1 + (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 ≤ 2.91422 := by
  set r := (2 : ℝ) ^ (-(1 / 2) : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr2 : r ^ 2 = 1 / 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hr1 : r ≤ 0.70711 := by nlinarith
  nlinarith

/-- `‖1 − 2^{−ρ}‖ ≤ 1 + 2^{−Re ρ}`. -/
theorem norm_one_sub_two_cpow (ρ : ℂ) : ‖1 - (2 : ℂ) ^ (-ρ)‖ ≤ 1 + (2 : ℝ) ^ (-ρ.re) := by
  have h := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (-ρ))
  have h2 : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 2 by norm_num) (-ρ)
    rw [Complex.neg_re] at this
    exact_mod_cast this
  rw [norm_one, h2] at h
  exact h

/-- A zero `ρ` of the strip is not `0`. -/
theorem norm_pos_of_zeroSet {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : ρ ∈ HM.zeroSet χ) : 0 < ‖ρ‖ := by
  rw [norm_pos_iff]
  intro h0
  have := h.2.1
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- **`lem:crepe` at one mollification scale** (every step PROVED from the links). -/
theorem crepe_eps (hEF : HM.ExplicitFormula) (hR : RosserL17) (hRS : RamareSaouterL2)
    (h1 : Eta2Reg) (h2 : Eta2Norms) (h3 : Eta2Mellin) (h4 : Eta2Main) {ν : ℝ → ℝ}
    (hν : MollData ν) (hz : PC.ZetaRHTo 3.061e10) {x : ℝ} (hx : 2000 ≤ x) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∑' n : ℕ, Λ n * eta2e ν ε ((n : ℝ) / x) ≤
      (1 + ε) * ((1 + 4e-9) * x + 0.54 * Real.sqrt x + 8 + 56 / Real.sqrt x) := by
  obtain ⟨hreg, h0⟩ := h1 ν hν ε hε0 hε1
  obtain ⟨hc0, hl2⟩ := h2 ν hν ε hε0 hε1
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hε' : 0 ≤ 1 + ε := by linarith
  set S := ∑' n : ℕ, Λ n * eta2e ν ε ((n : ℝ) / x) with hS
  have key := hEF (eta2e ν ε) hreg h0 1 1 DirichletCharacter.isPrimitive_one_level_one 0 x hx0
  have he0 : ∀ y : ℝ, y = 0 → e y = 1 := fun y hy => by
    rw [hy]
    simp [e]
  have htw : MajSp.twSum (eta2e ν ε) (1 : DirichletCharacter ℂ 1) x (0 / x) = (S : ℂ) := by
    rw [zero_div, hS, Complex.ofReal_tsum]
    unfold MajSp.twSum
    congr 1
    funext n
    rw [MulChar.one_apply (isUnit_of_subsingleton _), he0 _ (mul_zero _)]
    push_cast
    ring
  have herr : MajSp.err (eta2e ν ε) (1 : DirichletCharacter ℂ 1) 0 x =
      ((S / x : ℝ) : ℂ) - MajSp.mainFT (eta2e ν ε) 0 := by
    unfold MajSp.err
    rw [htw, if_pos (rfl : (1 : ℕ) = 1), Complex.ofReal_div]
  have hre : S ≤ x * ‖MajSp.err (eta2e ν ε) (1 : DirichletCharacter ℂ 1) 0 x‖ +
      x * (1 + ε) := by
    have h5 := Complex.re_le_norm (MajSp.err (eta2e ν ε) (1 : DirichletCharacter ℂ 1) 0 x)
    have h5' : (MajSp.err (eta2e ν ε) (1 : DirichletCharacter ℂ 1) 0 x).re =
        S / x - (MajSp.mainFT (eta2e ν ε) 0).re := by
      rw [herr, Complex.sub_re, Complex.ofReal_re]
    rw [h5'] at h5
    have h6 := h4 ν hν ε hε0 hε1
    have h7 : x * (S / x) = S := by field_simp
    have h8 := mul_le_mul_of_nonneg_left h5 hx0.le
    have h9 := mul_le_mul_of_nonneg_left h6 hx0.le
    rw [mul_sub, h7] at h8
    linarith
  set c := (1 + ε) * 11.6569 with hc
  have hlowb : ∀ ρ ∈ HM.zeroSet (1 : DirichletCharacter ℂ 1) ∩ {s : ℂ | |s.im| ≤ 3.061e10},
      ENNReal.ofReal ‖HM.Gm (eta2e ν ε) 0 ρ‖ ≤
        ENNReal.ofReal c * ENNReal.ofReal (1 / ‖ρ‖ ^ 2) := by
    intro ρ hρ
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hre2 : ρ.re = 1 / 2 := grhTo_one hz ρ hρ.1 hρ.2
    have hb := h3 ν hν ε hε0 hε1 ρ hρ.1.2.1 hρ.1.2.2
    have hn := norm_one_sub_two_cpow ρ
    rw [hre2] at hn
    have hsq : ‖1 - (2 : ℂ) ^ (-ρ)‖ ^ 2 ≤ 2.91422 :=
      (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans one_add_rpow_half_sq
    have hp : 0 < ‖ρ‖ ^ 2 := by have := norm_pos_of_zeroSet hρ.1; positivity
    refine hb.trans ?_
    rw [hc, mul_one_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hp]
    nlinarith
  have hhighb : ∀ ρ ∈ HM.zeroSet (1 : DirichletCharacter ℂ 1) ∩ {s : ℂ | 3.061e10 < |s.im|},
      ENNReal.ofReal ‖HM.Gm (eta2e ν ε) 0 ρ‖ ≤
        ENNReal.ofReal ((1 + ε) * 16) * ENNReal.ofReal (1 / ‖ρ‖ ^ 2) := by
    intro ρ hρ
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := h3 ν hν ε hε0 hε1 ρ hρ.1.2.1 hρ.1.2.2
    have hn := norm_one_sub_two_cpow ρ
    have h2r : (2 : ℝ) ^ (-ρ.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [hρ.1.2.1])
    have hsq : ‖1 - (2 : ℂ) ^ (-ρ)‖ ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ (norm_nonneg _)
        (hn.trans (by linarith : 1 + (2 : ℝ) ^ (-ρ.re) ≤ 2)) 2
      linarith
    have hp : 0 < ‖ρ‖ ^ 2 := by have := norm_pos_of_zeroSet hρ.1; positivity
    refine hb.trans ?_
    rw [mul_one_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hp]
    nlinarith
  have hZ : HM.zsum (1 : DirichletCharacter ℂ 1) univ
      (fun ρ => ENNReal.ofReal (‖HM.Gm (eta2e ν ε) 0 ρ‖ * x ^ ρ.re)) ≤
      ENNReal.ofReal (Real.sqrt x * (c * 0.0463) + x * ((1 + ε) * 16 * 2.5e-10)) := by
    have hsplit := HM.zsum_split (1 : DirichletCharacter ℂ 1) 3.061e10
      (fun ρ => ENNReal.ofReal (‖HM.Gm (eta2e ν ε) 0 ρ‖ * x ^ ρ.re))
    have hlow := HM.zsum_low (1 : DirichletCharacter ℂ 1) (HM.Gm (eta2e ν ε) 0) (x := x)
      (grhTo_one hz)
    have hhigh := HM.zsum_high (1 : DirichletCharacter ℂ 1) (HM.Gm (eta2e ν ε) 0)
      (T := 3.061e10) hx1
    have hl2' : HM.zsum (1 : DirichletCharacter ℂ 1) {s | |s.im| ≤ 3.061e10}
        (fun ρ => ENNReal.ofReal ‖HM.Gm (eta2e ν ε) 0 ρ‖) ≤
        ENNReal.ofReal c * ENNReal.ofReal 0.0463 := by
      refine (HM.zsum_mono _ hlowb).trans ?_
      rw [HM.zsum_const_mul]
      exact mul_le_mul_right (hR hz) _
    have hh2 : HM.zsum (1 : DirichletCharacter ℂ 1) {s | 3.061e10 < |s.im|}
        (fun ρ => ENNReal.ofReal ‖HM.Gm (eta2e ν ε) 0 ρ‖) ≤
        ENNReal.ofReal ((1 + ε) * 16) * ENNReal.ofReal 2.5e-10 := by
      refine (HM.zsum_mono _ hhighb).trans ?_
      rw [HM.zsum_const_mul]
      exact mul_le_mul_right (hRS.trans (ENNReal.ofReal_le_ofReal rs_value)) _
    refine hsplit.trans ((add_le_add (hlow.trans (mul_le_mul_right hl2' _))
      (hhigh.trans (mul_le_mul_right hh2 _))).trans (le_of_eq ?_))
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have h16 : 0 ≤ (1 + ε) * 16 := by positivity
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hsx.le,
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hx0.le, ENNReal.ofReal_mul h16]
  have hB : HM.c0 (eta2e ν ε) 0 + (Real.log ((1 : ℕ) : ℝ) + 8) *
      (MajSp.l2 (deriv (eta2e ν ε)) + 2 * Real.pi * |(0 : ℝ)| * MajSp.l2 (eta2e ν ε)) /
        Real.sqrt x ≤ 8 * (1 + ε) + 56 * (1 + ε) / Real.sqrt x := by
    rw [Nat.cast_one, Real.log_one, abs_zero, mul_zero, zero_mul, add_zero, zero_add]
    have : 8 * MajSp.l2 (deriv (eta2e ν ε)) / Real.sqrt x ≤ 56 * (1 + ε) / Real.sqrt x := by
      apply div_le_div_of_nonneg_right _ hsx.le
      linarith
    linarith
  have hB0 : 0 ≤ HM.c0 (eta2e ν ε) 0 + (Real.log ((1 : ℕ) : ℝ) + 8) *
      (MajSp.l2 (deriv (eta2e ν ε)) + 2 * Real.pi * |(0 : ℝ)| * MajSp.l2 (eta2e ν ε)) /
        Real.sqrt x := by
    rw [Nat.cast_one, Real.log_one, abs_zero, mul_zero, zero_mul, add_zero, zero_add]
    exact add_nonneg (HM.c0_nonneg _ _)
      (div_nonneg (mul_nonneg (by norm_num) (MajSp.l2_nonneg _)) hsx.le)
  have hk := key.trans (add_le_add hZ le_rfl)
  rw [← ENNReal.ofReal_add (by positivity) hB0,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hk
  have e1 : (1 + ε) * ((1 + 4e-9) * x + 0.54 * Real.sqrt x + 8 + 56 / Real.sqrt x) =
      x * (1 + ε) + (1 + ε) * (4e-9 * x) + (1 + ε) * (0.54 * Real.sqrt x) + 8 * (1 + ε) +
        56 * (1 + ε) / Real.sqrt x := by ring
  rw [e1]
  have e2 : Real.sqrt x * (c * 0.0463) ≤ (1 + ε) * (0.54 * Real.sqrt x) := by
    rw [hc]
    nlinarith
  have e3 : x * ((1 + ε) * 16 * 2.5e-10) = (1 + ε) * (4e-9 * x) := by ring
  linarith

/-- **`CrepeC` from the named links** (`ExplicitFormula`, `RosserL17`, `RamareSaouterL2` and the
five facts about the mollified `η₂`): let the mollification scale `ε → 0⁺`. -/
theorem crepeC_of_links (hEF : HM.ExplicitFormula) (hR : RosserL17) (hRS : RamareSaouterL2)
    (h1 : Eta2Reg) (h2 : Eta2Norms) (h3 : Eta2Mellin) (h4 : Eta2Main) (h5 : Eta2Conv) :
    CrepeC := by
  intro hz x hx
  obtain ⟨ν, hν⟩ := exists_mollData
  have hx0 : 0 < x := by linarith
  have hsx : (44 : ℝ) ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt (show (44 : ℝ) ^ 2 ≤ x by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h
  set K := (1 + 4e-9) * x + 0.54 * Real.sqrt x + 8 + 56 / Real.sqrt x with hK
  have hlim : Tendsto (fun ε : ℝ => (1 + ε) * K) (𝓝[>] 0) (𝓝 ((1 + 0) * K)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.add continuous_id).mul continuous_const).continuousAt.tendsto
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∑' n : ℕ, Λ n * eta2e ν ε ((n : ℝ) / x) ≤ (1 + ε) * K := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact crepe_eps hEF hR hRS h1 h2 h3 h4 hν hz hx hε.1 hε.2.le
  have hle := le_of_tendsto_of_tendsto (h5 ν hν x hx0) hlim hev
  rw [add_zero, one_mul] at hle
  refine hle.trans ?_
  rw [hK]
  have h56 : 56 / Real.sqrt x ≤ 56 / 44 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsx
  nlinarith

/-! ## (9) The Mellin transform of `η₂`, and three of the `η₂` links (PROVED) -/

/-- `η₂` as a complex function. -/
noncomputable def eta2C (t : ℝ) : ℂ := ((HW.eta2 t : ℝ) : ℂ)

/-- `d/dt (t^s/s) = t^{s−1}` for `t > 0`. -/
theorem hasDerivAt_Q {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ s / s) ((t : ℂ) ^ (s - 1)) t := by
  have h := ((Complex.hasStrictDerivAt_cpow_const (c := s)
    (Complex.ofReal_mem_slitPlane.mpr ht)).hasDerivAt.comp_ofReal).div_const s
  exact h.congr_deriv (mul_div_cancel_left₀ _ hs)

/-- `d/dt (t^s (log t/s − 1/s²)) = t^{s−1} log t` for `t > 0`. -/
theorem hasDerivAt_P {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ s * ((Real.log u : ℂ) / s - 1 / s ^ 2))
      ((t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) t := by
  have h1 := (Complex.hasStrictDerivAt_cpow_const (c := s)
    (Complex.ofReal_mem_slitPlane.mpr ht)).hasDerivAt.comp_ofReal
  have h2 := ((Real.hasDerivAt_log ht.ne').ofReal_comp.div_const s).sub_const (1 / s ^ 2)
  have h : HasDerivAt (fun u : ℝ => (u : ℂ) ^ s * ((Real.log u : ℂ) / s - 1 / s ^ 2))
      (s * (t : ℂ) ^ (s - 1) * ((Real.log t : ℂ) / s - 1 / s ^ 2) +
        (t : ℂ) ^ s * (((t⁻¹ : ℝ) : ℂ) / s)) t := h1.mul h2
  refine h.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hc : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * t := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
    field_simp
  rw [hc]
  push_cast
  field_simp
  try ring

/-- `(1/2)^s = 2^{−s}` and `(1/4)^s = (2^{−s})²` (positive real bases). -/
theorem half_cpow (s : ℂ) : ((1 / 2 : ℝ) : ℂ) ^ s = (2 : ℂ) ^ (-s) := by
  rw [Complex.cpow_neg, show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring,
    Complex.inv_cpow _ _ (by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm)]

theorem quarter_cpow (s : ℂ) : ((1 / 4 : ℝ) : ℂ) ^ s = ((2 : ℂ) ^ (-s)) ^ 2 := by
  rw [show ((1 / 4 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), half_cpow, sq]

/-- `η₂` vanishes on `(0, ∞)` outside `[1/4, 1]`. -/
theorem eta2_zero_off {t : ℝ} (ht : 0 < t) (hn : t ∉ Icc (1 / 4 : ℝ) 1) : HW.eta2 t = 0 := by
  rcases le_or_gt t (1 / 4) with hq | hq
  · exact HW.eta2_of_le_quarter ht hq
  · exact HW.eta2_of_one_le (le_of_lt (not_le.mp fun h => hn ⟨hq.le, h⟩))

/-- **`M η₂` converges everywhere** (continuous, supported in `[1/4, 1]`). -/
theorem mellinConv_eta2 (s : ℂ) : MellinConvergent eta2C s := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • eta2C t) (Icc (1 / 4) 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    exact ((Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht'.ne')).smul
      ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (EN.eta2_contOn t ht')).continuousAt (Ioi_mem_nhds ht'))).continuousWithinAt
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht => ?_
  simp [eta2C, eta2_zero_off ht.1 ht.2]

/-- **`M η₂(s) = 4((1 − 2^{−s})/s)²`** for `s ≠ 0`: `η₂ = 4 log 4t` on `[1/4, 1/2]` and
`−4 log t` on `[1/2, 1]` (`EN.eta2_left/right`), and the fundamental theorem of calculus with
`t^s/s` and `t^s(log t/s − 1/s²)`. (`eq:envy` prints `((1 − 2^{−s})/s)²`: finding F-A.) -/
theorem mellin_eta2 {s : ℂ} (hs : s ≠ 0) :
    mellin eta2C s = 4 * ((1 - (2 : ℂ) ^ (-s)) / s) ^ 2 := by
  set L : ℂ := ((Real.log 2 : ℝ) : ℂ) with hL
  have hsupp : mellin eta2C s = ∫ t in (1 / 4 : ℝ)..1, (t : ℂ) ^ (s - 1) * eta2C t := by
    rw [intervalIntegral.integral_of_le (by norm_num), mellin]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num) ht.1) fun t ht => ?_
    have h0 : (0 : ℝ) < t := ht.1
    have hz : HW.eta2 t = 0 := by
      rcases le_or_gt t (1 / 4) with hq | hq
      · exact HW.eta2_of_le_quarter h0 hq
      · exact HW.eta2_of_one_le (le_of_lt (not_le.mp fun h => ht.2 ⟨hq, h⟩))
    simp [eta2C, hz]
  have hcont : ∀ a b : ℝ, 0 < a → 0 < b →
      ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * eta2C t) (uIcc a b) := by
    intro a b ha hb t ht
    have ht' : (0 : ℝ) < t := HW.uIcc_pos ha hb ht
    exact ((Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht'.ne')).mul
      ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (EN.eta2_contOn t ht')).continuousAt (Ioi_mem_nhds ht'))).continuousWithinAt
  have hi1 := (hcont (1 / 4) (1 / 2) (by norm_num) (by norm_num)).intervalIntegrable
    (μ := volume)
  have hi2 := (hcont (1 / 2) 1 (by norm_num) (by norm_num)).intervalIntegrable (μ := volume)
  -- the left piece
  have hA : ∫ t in (1 / 4 : ℝ)..(1 / 2), (t : ℂ) ^ (s - 1) * eta2C t =
      (4 * (2 * L * ((((1 / 2 : ℝ) : ℂ) ^ s) / s) + ((1 / 2 : ℝ) : ℂ) ^ s *
        ((Real.log (1 / 2) : ℂ) / s - 1 / s ^ 2))) -
      (4 * (2 * L * ((((1 / 4 : ℝ) : ℂ) ^ s) / s) + ((1 / 4 : ℝ) : ℂ) ^ s *
        ((Real.log (1 / 4) : ℂ) / s - 1 / s ^ 2))) := by
    have heq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * eta2C t)
        (fun t : ℝ => 4 * (2 * L * (t : ℂ) ^ (s - 1) + (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)))
        (uIcc (1 / 4) (1 / 2)) := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      simp only [eta2C, EN.eta2_left ht.1 ht.2, hL]
      push_cast
      ring
    rw [intervalIntegral.integral_congr heq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ =>
      4 * (2 * L * ((u : ℂ) ^ s / s) + (u : ℂ) ^ s * ((Real.log u : ℂ) / s - 1 / s ^ 2)))
      (fun t ht => ?_) (hi1.congr (heq.mono uIoc_subset_uIcc))
    have ht' : (0 : ℝ) < t := HW.uIcc_pos (by norm_num) (by norm_num) ht
    exact (((hasDerivAt_Q hs ht').const_mul (2 * L)).add (hasDerivAt_P hs ht')).const_mul 4
  -- the right piece
  have hB : ∫ t in (1 / 2 : ℝ)..1, (t : ℂ) ^ (s - 1) * eta2C t =
      (-4 * (((1 : ℝ) : ℂ) ^ s * ((Real.log 1 : ℂ) / s - 1 / s ^ 2))) -
      (-4 * (((1 / 2 : ℝ) : ℂ) ^ s * ((Real.log (1 / 2) : ℂ) / s - 1 / s ^ 2))) := by
    have heq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * eta2C t)
        (fun t : ℝ => -4 * ((t : ℂ) ^ (s - 1) * (Real.log t : ℂ))) (uIcc (1 / 2) 1) := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      simp only [eta2C, EN.eta2_right ht.1 ht.2]
      push_cast
      ring
    rw [intervalIntegral.integral_congr heq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ =>
      -4 * ((u : ℂ) ^ s * ((Real.log u : ℂ) / s - 1 / s ^ 2)))
      (fun t ht => ?_) (hi2.congr (heq.mono uIoc_subset_uIcc))
    have ht' : (0 : ℝ) < t := HW.uIcc_pos (by norm_num) (by norm_num) ht
    exact (hasDerivAt_P hs ht').const_mul (-4)
  have l12 : ((Real.log (1 / 2) : ℝ) : ℂ) = -L := by
    rw [one_div, Real.log_inv, Complex.ofReal_neg]
  have l14 : ((Real.log (1 / 4) : ℝ) : ℂ) = -2 * L := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow, hL]
    push_cast
    ring
  have l1 : ((Real.log 1 : ℝ) : ℂ) = 0 := by rw [Real.log_one, Complex.ofReal_zero]
  have o1 : (((1 : ℝ) : ℂ)) ^ s = 1 := by rw [Complex.ofReal_one, Complex.one_cpow]
  rw [hsupp, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hA, hB, half_cpow,
    quarter_cpow, l12, l14, l1, o1]
  ring

/-- `‖M η₂(s)‖ = 4‖1 − 2^{−s}‖²/‖s‖²`. -/
theorem norm_mellin_eta2 {s : ℂ} (hs : s ≠ 0) :
    ‖mellin eta2C s‖ = 4 * ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2 := by
  rw [mellin_eta2 hs, norm_mul, norm_pow, norm_div, Complex.norm_ofNat]
  ring

/-- **`M η₂(1) = 1 = ∫η₂`** — against `eq:envy`'s printed `((1 − 2^{−1})/1)² = 1/4` (F-A). -/
theorem mellin_eta2_one : mellin eta2C 1 = 1 := by
  rw [mellin_eta2 one_ne_zero, Complex.cpow_neg_one]
  norm_num

/-- **The printed `eq:envy` at `s = 1` is `1/4`, not `M η₂(1) = 1`** (finding F-A, typechecked). -/
theorem envy_printed_one : ((1 - (2 : ℂ) ^ (-(1 : ℂ))) / 1) ^ 2 = 1 / 4 ∧ mellin eta2C 1 = 1 := by
  refine ⟨?_, mellin_eta2_one⟩
  rw [Complex.cpow_neg_one]
  norm_num

/-- `η₂ ∗_M ν_ε` as a complex Mellin convolution. -/
theorem eta2e_ofReal (ν : ℝ → ℝ) (ε t : ℝ) :
    ((eta2e ν ε t : ℝ) : ℂ) = MellinConvolution eta2C (nuC (DeltaSpike ν ε)) t := by
  unfold eta2e MellinConvolution
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp only [eta2C, nuC, RCLike.ofReal_real_eq_id, id_eq]
  push_cast
  rfl

/-- **`M(η₂ ∗_M ν_ε)(s) = M η₂(s)·Mν(εs)`**, and it converges. -/
theorem mellin_eta2e {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    mellin (fun t => ((eta2e ν ε t : ℝ) : ℂ)) s = mellin eta2C s * Mnu ν (ε * s) := by
  have hfc : ContinuousOn eta2C (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn EN.eta2_contOn
  have hgc : Continuous (nuC (DeltaSpike ν ε)) :=
    DeltaSpikeOfRealContinuous hε (hν.1.of_le (by simp))
  have h := (mellin_mconv hfc hgc.continuousOn (mellinConv_eta2 s)
    (mellinConv_spike hν hε s)).2
  have hfun : (fun t => ((eta2e ν ε t : ℝ) : ℂ)) =
      MellinConvolution eta2C (nuC (DeltaSpike ν ε)) := funext (eta2e_ofReal ν ε)
  rw [hfun, h, Mnu]
  congr 1
  exact MellinOfDeltaSpike ν hε s

/-- `e(0·t) = 1`. -/
theorem e_zero_mul (t : ℝ) : e (0 * t) = 1 := by
  simp [e]

/-- `e(0) = 1`. -/
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- **`Eta2Mellin` HOLDS.** -/
theorem eta2Mellin_holds : Eta2Mellin := by
  intro ν hν ε hε0 hε1 s h0 h1
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
  have hG : HM.Gm (eta2e ν ε) 0 s = mellin eta2C s * Mnu ν (ε * s) := by
    rw [← mellin_eta2e hν hε0 s, HM.Gm]
    congr 1
    funext t
    rw [e_zero_mul, mul_one]
  rw [hG, norm_mul, norm_mellin_eta2 hs, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_Mnu_strip hν hε0 hε1 h0 h1) (by positivity)

/-- **`Eta2Main` HOLDS**: the main term is `M η₂(1)·Mν(ε) = Mν(ε)`, of real part
`≤ 2^ε ≤ 1 + ε`. -/
theorem eta2Main_holds : Eta2Main := by
  intro ν hν ε hε0 hε1
  have hM : MajSp.mainFT (eta2e ν ε) 0 = Mnu ν ε := by
    have h := mellin_eta2e hν hε0 1
    rw [mellin_eta2_one, one_mul, mul_one] at h
    rw [← h, MajSp.mainFT, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [zero_mul, e_zero, mul_one, sub_self, Complex.cpow_zero, one_smul]
  rw [hM]
  refine (Complex.re_le_norm _).trans ((norm_Mnu_le hν _).trans ?_)
  have hre : ((ε : ℂ)).re = ε := Complex.ofReal_re ε
  rw [hre, abs_of_pos hε0]
  exact two_rpow_le hε0.le hε1

/-- `|log y| ≤ ε log 2` on the support `[2^{−ε}, 2^ε]` of `ν_ε`. -/
theorem abs_log_le_of_mem {ε y : ℝ} (hy : y ∈ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε)) :
    |Real.log y| ≤ ε * Real.log 2 := by
  have h0 : (0 : ℝ) < 2 ^ (-ε) := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le h0 hy.1
  have h1 := Real.log_le_log hy0 hy.2
  have h2 := Real.log_le_log h0 hy.1
  rw [Real.log_rpow (by norm_num)] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- `ν_ε(y)/y` is integrable on `(0, ∞)` (its integral is `1`). -/
theorem integrable_spike_div {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y => DeltaSpike ν ε y / y) (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [DeltaSpikeMass hν.2.2.2 hε]; norm_num)

/-- **`|η₂ ∗_M ν_ε − η₂| ≤ 4ε log 2`** on `(0, ∞)`: `η₂` is `4`-Lipschitz in `log t`
(`HX.eta2_sub_le`), `ν_ε` has mass `1` (`DeltaSpikeMass`) and lives on `[2^{−ε}, 2^ε]`. -/
theorem eta2e_sub_le {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    |eta2e ν ε t - HW.eta2 t| ≤ 4 * (ε * Real.log 2) := by
  have hsym : eta2e ν ε t = ∫ y in Ioi (0 : ℝ), DeltaSpike ν ε y * HW.eta2 (t / y) / y := by
    unfold eta2e
    rw [MellinConvolutionSymmetric _ _ ht]
    rfl
  have hint1 : IntegrableOn (fun y => DeltaSpike ν ε y * HW.eta2 (t / y) / y) (Ioi 0) := by
    refine ((integrable_spike_div hν hε).mul_const (4 * Real.log 2)).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) measurableSet_Ioi
      have hy' : (0 : ℝ) < y := hy
      have c1 : ContinuousWithinAt (fun y => DeltaSpike ν ε y) (Ioi 0) y :=
        (DeltaSpikeContinuous hε (hν.1.of_le (by simp))).continuousWithinAt
      have c2 : ContinuousWithinAt (fun y => HW.eta2 (t / y)) (Ioi 0) y :=
        ContinuousWithinAt.comp (g := HW.eta2) (EN.eta2_contOn (t / y) (div_pos ht hy'))
          (continuousAt_const.div continuousAt_id hy'.ne').continuousWithinAt
          (fun z hz => mem_Ioi.mpr (div_pos ht hz))
      exact (c1.mul c2).div continuousWithinAt_id hy'.ne'
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
      have hy' : (0 : ℝ) < y := hy
      have hd : 0 ≤ DeltaSpike ν ε y := div_nonneg (hν.2.1 _) hε.le
      have he0 := HW.eta2_nonneg (t / y)
      have he3 := GS.eta2_le (t / y)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hd he0) hy'.le)]
      calc DeltaSpike ν ε y * HW.eta2 (t / y) / y = DeltaSpike ν ε y / y * HW.eta2 (t / y) := by
            ring
        _ ≤ DeltaSpike ν ε y / y * (4 * Real.log 2) :=
            mul_le_mul_of_nonneg_left he3 (div_nonneg hd hy'.le)
  have hint2 : IntegrableOn (fun y => DeltaSpike ν ε y / y * HW.eta2 t) (Ioi 0) :=
    (integrable_spike_div hν hε).mul_const _
  have hdiff : eta2e ν ε t - HW.eta2 t = ∫ y in Ioi (0 : ℝ),
      (DeltaSpike ν ε y * HW.eta2 (t / y) / y - DeltaSpike ν ε y / y * HW.eta2 t) := by
    rw [hsym, integral_sub hint1 hint2, integral_mul_const, DeltaSpikeMass hν.2.2.2 hε, one_mul]
  rw [hdiff, ← Real.norm_eq_abs]
  have hb : IntegrableOn (fun y => 4 * (ε * Real.log 2) * (DeltaSpike ν ε y / y)) (Ioi 0) :=
    (integrable_spike_div hν hε).const_mul _
  refine (norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun y hy => ?_))).trans (le_of_eq ?_)
  · have hy' : (0 : ℝ) < y := hy
    have hd : 0 ≤ DeltaSpike ν ε y := div_nonneg (hν.2.1 _) hε.le
    rw [Real.norm_eq_abs]
    have e : DeltaSpike ν ε y * HW.eta2 (t / y) / y - DeltaSpike ν ε y / y * HW.eta2 t =
        DeltaSpike ν ε y / y * (HW.eta2 (t / y) - HW.eta2 t) := by ring
    rw [e]
    by_cases h0 : DeltaSpike ν ε y = 0
    · simp [h0]
    · rw [abs_mul, abs_of_nonneg (div_nonneg hd hy'.le), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hd hy'.le)
      have hmem : y ∈ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε) := DeltaSpikeSupport' hε hy'.le hν.2.2.1 h0
      have hl := HX.eta2_sub_le (div_pos ht hy') ht
      have hl' := HX.eta2_sub_le ht (div_pos ht hy')
      have hlog : Real.log (t / y) - Real.log t = -Real.log y := by
        rw [Real.log_div ht.ne' hy'.ne']
        ring
      have hlog2 : Real.log t - Real.log (t / y) = Real.log y := by
        rw [Real.log_div ht.ne' hy'.ne']
        ring
      rw [hlog, abs_neg] at hl
      rw [hlog2] at hl'
      have hb := abs_log_le_of_mem hmem
      rw [abs_le]
      constructor <;> linarith
  · rw [integral_const_mul, DeltaSpikeMass hν.2.2.2 hε, mul_one]

/-- `η₂ ∗_M ν_ε` vanishes beyond `2` (`ε ≤ 1`): `η₂` lives on `[1/4, 1]`, `ν_ε` on
`[2^{−ε}, 2^ε]`. -/
theorem eta2e_zero_of_ge {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {t : ℝ} (ht : 2 < t) : eta2e ν ε t = 0 := by
  unfold eta2e MellinConvolution
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  have hy' : (0 : ℝ) < y := hy
  by_cases hy1 : y ∈ Icc (1 / 4 : ℝ) 1
  · have h2 : (2 : ℝ) ^ ε ≤ 2 := by
      calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
        _ = 2 := Real.rpow_one 2
    have hty : t ≤ t / y := by
      rw [le_div_iff₀ hy']
      nlinarith [hy1.2]
    have hn : t / y ∉ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε) := fun h => by linarith [h.2]
    rw [DeltaSpikeSupport hε0 (by positivity) hν.2.2.1 hn]
    simp
  · rw [eta2_zero_off hy' hy1]
    simp

/-- **`Eta2Conv` HOLDS**: both sums run over `n ≤ 2x`, and each term converges since
`|η₂ ∗_M ν_ε − η₂| ≤ 4ε log 2` (`eta2e_sub_le`). -/
theorem eta2Conv_holds : Eta2Conv := by
  intro ν hν x hx
  set N := ⌈2 * x⌉₊ + 1 with hN
  have hbig : ∀ n : ℕ, n ∉ Finset.range N → 2 < (n : ℝ) / x := by
    intro n hn
    have h1 : N ≤ n := by simpa using hn
    have h2 : 2 * x ≤ (⌈2 * x⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (N : ℝ) ≤ n := by exact_mod_cast h1
    rw [hN] at h3
    push_cast at h3
    rw [lt_div_iff₀ hx]
    linarith
  have hfin : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∑' n : ℕ, Λ n * eta2e ν ε ((n : ℝ) / x) =
      ∑ n ∈ Finset.range N, Λ n * eta2e ν ε ((n : ℝ) / x) := by
    intro ε h0 h1
    refine tsum_eq_sum fun n hn => ?_
    rw [eta2e_zero_of_ge hν h0 h1 (hbig n hn), mul_zero]
  have hfin2 : GS.sEta2 x = ∑ n ∈ Finset.range N, Λ n * HW.eta2 ((n : ℝ) / x) := by
    unfold GS.sEta2
    refine tsum_eq_sum fun n hn => ?_
    rw [HW.eta2_of_one_le (by linarith [hbig n hn]), mul_zero]
  rw [hfin2]
  have hsum : Tendsto (fun ε : ℝ => ∑ n ∈ Finset.range N, Λ n * eta2e ν ε ((n : ℝ) / x))
      (𝓝[>] 0) (𝓝 (∑ n ∈ Finset.range N, Λ n * HW.eta2 ((n : ℝ) / x))) := by
    refine tendsto_finsetSum _ fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ArithmeticFunction.map_zero, zero_mul]
      exact tendsto_const_nhds
    · have ht : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hn) hx
      refine tendsto_const_nhds.mul ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have ha : Tendsto (fun ε : ℝ => 4 * (ε * Real.log 2)) (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous fun ε : ℝ => 4 * (ε * Real.log 2) := by fun_prop
        have h := hc.tendsto 0
        simp only [zero_mul, mul_zero] at h
        exact tendsto_nhdsWithin_of_tendsto_nhds h
      refine squeeze_zero_norm' ?_ ha
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [norm_norm, Real.norm_eq_abs]
      exact eta2e_sub_le hν hε ht
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (hfin ε hε.1 hε.2.le).symm

/-- **The pin for `HC.Crepe`, the statement NOT proved here** (finding F-A): by `rfl`, the body of
`HelfgottCited.lean` 467-468, whose `0.135` is `(3/2 + √2)·κ₁` computed from `eq:envy`'s formula
for `M η₂`, which is off by the factor `4`. -/
theorem crepe_statement : HC.Crepe = (PC.ZetaRHTo 3.061e10 → ∀ x : ℝ, 2000 ≤ x →
    GS.sEta2 x ≤ (1 + 2.73e-10) * x + 0.135 * Real.sqrt x) := rfl

/-- **`CrepeC` is WEAKER than `HC.Crepe`**: replacing the printed `lem:crepe` by the corrected one
costs no consumer anything. -/
theorem crepeC_of_crepe (h : HC.Crepe) : CrepeC := by
  intro hz x hx
  have h1 := h hz x hx
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

/-- **The pin for the consumer**: `GS.Austeria` is, by `rfl`, the body of `GorshSpine.lean` 112;
`austeria_of_citedC` proves exactly it. -/
theorem austeria_statement :
    GS.Austeria = (∀ Y : ℝ, 1 ≤ Y → GS.sEta2 Y ≤ 1.04488 * Y) := rfl

/-- **`CrepeC` FROM `HM.ExplicitFormula`, THE TWO CITED LEMMAS AND TWO NAMED LINKS**
(`Eta2Reg`, `Eta2Norms`): `crepeC_of_links` with `Eta2Mellin`, `Eta2Main`, `Eta2Conv` PROVED. -/
theorem crepeC_of_named (hEF : HM.ExplicitFormula) (hR : RosserL17) (hRS : RamareSaouterL2)
    (h1 : Eta2Reg) (h2 : Eta2Norms) : CrepeC :=
  crepeC_of_links hEF hR hRS h1 h2 eta2Mellin_holds eta2Main_holds eta2Conv_holds

/-- **`GS.Austeria` from the whole chain**: the six explicit-formula links, the two cited
zero-sum lemmas, the two named facts about `η₂ ∗_M ν_ε`, and Helfgott's cited computations below
`2000` with Platt–Trudgian. Application only. -/
theorem austeria_of_links (hRe : Rectangle) (hHo : Horizontal)
    (hCo : Continuation) (hDe : MollDecay) (hML : MollLimit) (hLD : LeftLD)
    (hR : RosserL17) (hRS : RamareSaouterL2) (e1 : Eta2Reg) (e2 : Eta2Norms)
    (z : PC.PlattTrudgian) (gr : HC.AusteriaGridCited) (wi : HC.AusteriaWindowCited)
    (lp : HC.AusteriaLip) : GS.Austeria :=
  austeria_of_citedC z gr wi lp
    (crepeC_of_named (agamon_of_links hRe hHo hCo hDe hML hLD) hR hRS e1 e2)

end Principia.Common.TernaryGoldbach.EF
