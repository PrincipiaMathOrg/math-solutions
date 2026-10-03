/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorR

set_option autoImplicit false

/-!
# The corrected `thm:ostop` with the Main Theorem's two constants as PARAMETERS (`OstopP`)

`OstopL.lean` hard-codes two constants of Helfgott's minarcs Main Theorem that an adversarially
verified round found UNREACHABLE from the book's pieces (`MinMainTotals.lean`):

* `0.5`, the main-term constant of `g_Y` (`OL.gYL`) and of `eq:kraw` (`OL.krawL`): the
  Conclusion's AM-GM halves a summand, and the pieces give `0.81019`, typed `0.811`
  (`MT.amgm_main`, `MT.not_arith_05`);
* `22.7538`, the constant of `L`'s `1/q` part (`OL.lLc`, `OL.lToscaL`): `lem:bosta2` at scale
  `x/v` needs `c_+`, and the book's `eq:cleson` gives `45.7575` (`MT.not_arith_typedL`).

Here every `g`-carrying object of `OstopL.lean` is restated with those two constants as
parameters `(c05, C)`. The substitution is COUNTED (`scratchpad/ostopp/gen_ostopp.py` asserts
every replacement count) and touches `0.5` ONLY in `gY` and `kraw`, `22.7538` ONLY in `lLc` and
`lTosca`; each object is PINNED to its `OL` original at `(0.5, 22.7538)` by `rfl` (section 2).

## The spine

```
 gYP c05 C = OL.gYL + dP c05 C          dP(r) = (c05 − 0.5)√ϝ(r)/√(2r) + (C − 22.7538)/r
 lLcP, gYP, gTP, intGTP, mMCP           (generated; pinned: *_pin, by rfl)
 OstopP, MNumP, lToscaP, krawP, MinMainP, GorshP, GTMonoP, CoprarP   (generated; pinned)
 minor_of_mnum_P : MR.minor_of_mnum_LR with OstopL ↦ OstopP c05 C, MNumL ↦ MNumP c05 C
 minorAt_ostopP_helfR : RT.MinorUpperAt c η₊ η*, generic in (c05, C, c, cM, J₀, p₀, fs)
```

The layer-1 composition does not look at the constants: `minor_of_mnum_P` uses `OstopP` and
`MNumP` only through `mMCP`, which it unfolds and never evaluates. The positivity of `g_Y`
(`gYP_pos`) is the one place a SIGN of the constants is used (`0 ≤ c05`, `0 ≤ C`).
-/

namespace Principia.Common.TernaryGoldbach.OP

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Common.TernaryGoldbach.MinSp

/-! ## (1) The quantities, parametric in `(c05, C)` -/

/-- **`L_t` with its `1/q` constant a parameter** (generated from `OL.lLc`: `22.7538 ↦ C`). -/
noncomputable def lLcP (C t : ℝ) : ℝ :=
  MinSp.bigF t * (Real.log (2 ^ ((7 : ℝ) / 4) * t ^ ((13 : ℝ) / 4)) + 80 / 9) +
    Real.log (2 ^ (1.7984 : ℝ) * t ^ (13.6516 : ℝ)) + C

/-- **`g_Y(r)` with both constants parameters** (generated from `OL.gYL`: `0.5 ↦ c05`,
`lLc ↦ lLcP C`). -/
noncomputable def gYP (c05 C Y r : ℝ) : ℝ :=
  ((MinSp.rR Y (2 * r) * Real.log (2 * r) + c05) * Real.sqrt (MinSp.bigF r) + 2.5) /
      Real.sqrt (2 * r) + lLcP C r / r + 3.2 * Y ^ (-(1 : ℝ) / 6)

/-- **`g̃_{y,φ}(r)`** on `gYP c05 C` (generated from `OL.gTL`). -/
noncomputable def gTP (c05 C : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ((∫ w in (max (1 / MinSp.kK y) (1000 / r))..1, gYP c05 C (w * y) (w * r) * φ w) +
      (∫ w in Set.Ioi (1 : ℝ), gYP c05 C (w * y) r * φ w) +
      1.04488 * ∫ w in (1 / MinSp.kK y)..(max (1 / MinSp.kK y) (1000 / r)), |φ w|) /
    MajSp.l1 φ

/-- **`∫_{r₀}^{r₁} g̃(r)/r dr`** on `gTP c05 C` (generated from `OL.intGTL`). -/
noncomputable def intGTP (c05 C : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ r in (150000 : ℝ)..MinSp.r1y y, gTP c05 C φ y r / r

/-- **`M̃`** on `gTP c05 C` (generated from `OL.mMCL`). -/
noncomputable def mMCP (c05 C : ℝ) (φ η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  gTP c05 C φ (x / 49) 150000 * (OC.hR0C x * MinSp.sPr η x - MinSp.pJE η b x) +
    (2 / (Real.log x - 2 * 1.306476) * intGTP c05 C φ (x / 49) +
      OC.coefC x * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) * MinSp.sPr η x

/-- **Link [ostopP] — the corrected `thm:ostop` at `(c05, C)`** (generated from `OL.OstopL`). -/
def OstopP (c05 C : ℝ) (ηp ηs φ : ℝ → ℝ) : Prop :=
  MinSp.OstopHyp ηp ηs φ → ∀ b : ℝ → ℝ, MinSp.SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    MinSp.zMin ηp ηs x ≤
      (Real.sqrt (MajSp.l1 φ * x / 49 * (mMCP c05 C φ ηp b x + MinSp.tT φ ηp b x)) +
        Real.sqrt (MinSp.sStar ηs x * MinSp.eBig b x)) ^ 2

/-- **Link [M̃] at `(c05, C)`** (generated from `OL.MNumL`). -/
def MNumP (c05 C : ℝ) (φ : ℝ → ℝ) (p₀ c fs : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ fs * Real.log x - 0.021095 →
    p₀ ≤ p →
      gTP c05 C φ (x / 49) 150000 * (OC.hR0C x * s - p) +
          (2 / (Real.log x - 2 * 1.306476) * intGTP c05 C φ (x / 49) +
            OC.coefC x * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) * s ≤ c

/-- **`L_{δ,q}` with its `1/q` constant a parameter** (generated from `OL.lToscaL`:
`22.7538 ↦ C`). -/
noncomputable def lToscaP (C δ : ℝ) (q : ℕ) : ℝ :=
  (Real.log (δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) + 80 / 9) /
      ((Nat.totient q : ℝ) / q) +
    Real.log ((q : ℝ) ^ (13.6516 : ℝ) * δ ^ (1.7984 : ℝ)) + C

/-- **The right side of `eq:kraw` at `(c05, C)`** (generated from `OL.krawL`: `0.5 ↦ c05`,
`lToscaL ↦ lToscaP C`). -/
noncomputable def krawP (c05 C x δ : ℝ) (q : ℕ) : ℝ :=
  (MinSp.rR x (OC.dz δ * q) * Real.log (OC.dz δ * q) + c05) /
      Real.sqrt (OC.dz δ * Nat.totient q) * x +
    2.5 * x / Real.sqrt (OC.dz δ * q) + 2 * x / (OC.dz δ * q) * lToscaP C (OC.dz δ) q +
    3.2 * x ^ ((5 : ℝ) / 6)

/-- **Layer 2 [MinMainP] — the minarcs Main Theorem at `(c05, C)`** (generated from
`OL.MinMainL`). At `(0.811, 45.7575)` its first case is what the book's Totals deliver from the
three named piece bounds (`MMP.minMainP_of_pieces`). -/
def MinMainP (c05 C : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) →
      ((q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ‖Smooth.smSum HW.eta2 Y α‖ ≤ krawP c05 C Y δ q) ∧
      (Y ^ ((1 : ℝ) / 3) / 6 < q → ‖Smooth.smSum HW.eta2 Y α‖ ≤
        0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
          1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y)

/-- **Layer 2 [GorshP]** — `prop:gorsh` on `gTP c05 C` (generated from `OL.GorshL`). -/
def GorshP (c05 C : ℝ) (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    MeasureTheory.IntegrableOn φ (Set.Ioi 0) →
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) ≤ MinSp.r1y (x / 49) →
    ∀ α : ℝ, α ∉ Smooth.arcs 8 r (x / 49) →
      ‖Smooth.smSum ηs x α‖ ≤
        (gTP c05 C φ (x / 49) r + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

/-- **Layer 2 [GTMonoP]** — `gTP c05 C (y, ·)` non-increasing on `[r₀, r₁]` (generated from
`OL.GTMonoL`). -/
def GTMonoP (c05 C : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 10 ^ 25 ≤ y → AntitoneOn (gTP c05 C φ y) (Set.Icc 150000 (MinSp.r1y y))

/-- **Layer 2 [CoprarP]** — the annulus `A₀` on `gTP c05 C` (generated from `OL.CoprarL`). -/
def CoprarP (c05 C : ℝ) (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    MeasureTheory.IntegrableOn φ (Set.Ioi 0) →
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ α : ℝ, α ∈ OC.annA0 x →
    ‖Smooth.smSum ηs x α‖ ≤
      (gTP c05 C φ (x / 49) 150000 + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

/-! ## (2) The pins: at `(0.5, 22.7538)` every object IS its `OL` original, by `rfl`

These prove the substitution touched the two constants and nothing else. -/

theorem lLcP_pin : lLcP 22.7538 = OL.lLc :=
  rfl

theorem gYP_pin : gYP 0.5 22.7538 = OL.gYL :=
  rfl

theorem gTP_pin : gTP 0.5 22.7538 = OL.gTL :=
  rfl

theorem intGTP_pin : intGTP 0.5 22.7538 = OL.intGTL :=
  rfl

theorem mMCP_pin : mMCP 0.5 22.7538 = OL.mMCL :=
  rfl

theorem ostopP_pin (ηp ηs φ : ℝ → ℝ) : OstopP 0.5 22.7538 ηp ηs φ ↔ OL.OstopL ηp ηs φ :=
  Iff.rfl

theorem mnumP_pin (φ : ℝ → ℝ) (p₀ c fs : ℝ) :
    MNumP 0.5 22.7538 φ p₀ c fs ↔ OL.MNumL φ p₀ c fs :=
  Iff.rfl

theorem lToscaP_pin : lToscaP 22.7538 = OL.lToscaL :=
  rfl

theorem krawP_pin : krawP 0.5 22.7538 = OL.krawL :=
  rfl

theorem minMainP_pin : MinMainP 0.5 22.7538 ↔ OL.MinMainL :=
  Iff.rfl

theorem gorshP_pin (ηs φ : ℝ → ℝ) : GorshP 0.5 22.7538 ηs φ ↔ OL.GorshL ηs φ :=
  Iff.rfl

theorem gtMonoP_pin (φ : ℝ → ℝ) : GTMonoP 0.5 22.7538 φ ↔ OL.GTMonoL φ :=
  Iff.rfl

theorem coprarP_pin (ηs φ : ℝ → ℝ) : CoprarP 0.5 22.7538 ηs φ ↔ OL.CoprarL ηs φ :=
  Iff.rfl

/-! ## (3) The decomposition `gYP = gYL + dP` -/

/-- **The increment of `g_Y`**: `dP(r) = (c05 − 0.5)√ϝ(r)/√(2r) + (C − 22.7538)/r`. -/
noncomputable def dP (c05 C r : ℝ) : ℝ :=
  (c05 - 0.5) * Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) + (C - 22.7538) / r

/-- `lLcP C = OL.lLc + (C − 22.7538)`. -/
theorem lLcP_eq (C t : ℝ) : lLcP C t = OL.lLc t + (C - 22.7538) := by
  unfold lLcP OL.lLc
  ring

/-- **`gYP c05 C Y r = gYL Y r + dP c05 C r`**, for every `Y`, `r`. -/
theorem gYP_eq (c05 C Y r : ℝ) : gYP c05 C Y r = OL.gYL Y r + dP c05 C r := by
  unfold gYP OL.gYL dP
  rw [lLcP_eq]
  ring

/-- `dP ≥ 0` when both constants are raised (`c05 ≥ 0.5`, `C ≥ 22.7538`) and `r ≥ 0`. -/
theorem dP_nonneg (c05 C r : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (hr : 0 ≤ r) :
    0 ≤ dP c05 C r := by
  unfold dP
  have h1 : 0 ≤ (c05 - 0.5) * Real.sqrt (MinSp.bigF r) / Real.sqrt (2 * r) :=
    div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (C - 22.7538) / r := div_nonneg (by linarith) hr
  linarith

/-- **Raising the constants raises `g_Y`**: `gYL ≤ gYP c05 C` for `c05 ≥ 0.5`, `C ≥ 22.7538`. -/
theorem gYL_le_gYP (c05 C Y r : ℝ) (hc : 0.5 ≤ c05) (hC : 22.7538 ≤ C) (hr : 0 ≤ r) :
    OL.gYL Y r ≤ gYP c05 C Y r := by
  rw [gYP_eq]
  linarith [dP_nonneg c05 C r hc hC hr]

/-- **`gYP c05 C Y r > 0` on `lem:vinc`'s range** for `c05, C ≥ 0` (generated from
`OL.gYL_pos`; the two `≥ 0` hypotheses are the ONLY use of the constants' values in the generic
compositions). -/
theorem gYP_pos (c05 C Y r : ℝ) (hc05 : 0 ≤ c05) (hC : 0 ≤ C) (hY : 0 < Y) (hr : 175 ≤ r)
    (hrY : r ≤ Y ^ ((1 : ℝ) / 3) / 6) : 0 < gYP c05 C Y r := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < Y ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY _
  have hl2 := Real.log_two_gt_d9
  have hlr1 : 1 < Real.log r := by
    rw [Real.lt_log_iff_exp_lt hr0]
    linarith [Real.exp_one_lt_d9]
  have hll : 0 < Real.log (Real.log r) := Real.log_pos hlr1
  have hF : 0 < MinSp.bigF r := by
    unfold MinSp.bigF
    have h1 := mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hll
    have h2 := div_pos (by norm_num : (0 : ℝ) < 2.50637) hll
    linarith
  have hR : 0.41415 ≤ MinSp.rR Y (2 * r) := by
    unfold MinSp.rR
    have h4 : 0 < Real.log (4 * (2 * r)) := Real.log_pos (by linarith)
    have hq : 1 < 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r)) := by
      rw [one_lt_div (by linarith : (0 : ℝ) < 2.004 * (2 * r))]
      linarith
    have hl : 0 < Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))) := Real.log_pos hq
    have hfr : 0 ≤ Real.log (4 * (2 * r)) /
        (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r)))) :=
      div_nonneg h4.le (by linarith)
    have hlg : 0 ≤ Real.log (1 + Real.log (4 * (2 * r)) /
        (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))))) :=
      Real.log_nonneg (by linarith)
    linarith
  have hlog2r : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (2 * r) := Real.sqrt_pos.2 (by linarith)
  have hA : 0 ≤ (MinSp.rR Y (2 * r) * Real.log (2 * r) + c05) * Real.sqrt (MinSp.bigF r) :=
    mul_nonneg (add_nonneg (mul_nonneg (by linarith) hlog2r.le) hc05)
      (Real.sqrt_nonneg _)
  have hL : 0 < lLcP C r := by
    unfold lLcP
    rw [OL.log_two_rpow_mul _ _ r hr0, OL.log_two_rpow_mul _ _ r hr0]
    have hX : 0 < (7 : ℝ) / 4 * Real.log 2 + (13 : ℝ) / 4 * Real.log r + 80 / 9 := by
      linarith
    have hP := mul_pos hF hX
    linarith
  have h1 : 0 < ((MinSp.rR Y (2 * r) * Real.log (2 * r) + c05) * Real.sqrt (MinSp.bigF r) +
      2.5) / Real.sqrt (2 * r) := div_pos (by linarith) hs
  have h2 : 0 < lLcP C r / r := div_pos hL hr0
  have h3 : 0 < 3.2 * Y ^ (-(1 : ℝ) / 6) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hY _)
  unfold gYP
  exact add_pos (add_pos h1 h2) h3

/-- **`OstopP` is met by `η₊ = 0`** (generated from `OL.ostopL_zero`). -/
theorem ostopP_zero (c05 C : ℝ) (ηs φ : ℝ → ℝ) : OstopP c05 C 0 ηs φ := by
  intro _ b _ x _
  have hz : zMin 0 ηs x = 0 := by simp [zMin, Smooth.smSum_zero]
  rw [hz]
  exact sq_nonneg _

/-! ## (4) The monotonicities of `MNumP` -/

/-- (generated from `OL.mnumL_floor_mono`) -/
theorem mnumP_floor_mono (c05 C : ℝ) (φ : ℝ → ℝ) (p₀ p₁ c fs : ℝ) (h01 : p₀ ≤ p₁)
    (h : MNumP c05 C φ p₀ c fs) : MNumP c05 C φ p₁ c fs :=
  fun x hx s p hs0 hs hp => h x hx s p hs0 hs (le_trans h01 hp)

/-- (generated from `OL.mnumL_const_mono`) -/
theorem mnumP_const_mono (c05 C : ℝ) (φ : ℝ → ℝ) (p₀ c c' fs : ℝ) (hc : c ≤ c')
    (h : MNumP c05 C φ p₀ c fs) : MNumP c05 C φ p₀ c' fs :=
  fun x hx s p hs0 hs hp => le_trans (h x hx s p hs0 hs hp) hc

/-- (generated from `OL.mnumL_slope_mono`) -/
theorem mnumP_slope_mono (c05 C : ℝ) (φ : ℝ → ℝ) (p₀ c fs fs' : ℝ) (hf : fs' ≤ fs)
    (h : MNumP c05 C φ p₀ c fs) : MNumP c05 C φ p₀ c fs' := by
  intro x hx s p hs0 hs hp
  have hL := MajSp.log_ge_one x hx
  have h1 : fs' * Real.log x ≤ fs * Real.log x := mul_le_mul_of_nonneg_right hf (by linarith)
  exact h x hx s p hs0 (by linarith) hp

/-! ## (5) THE LAYER-1 COMPOSITION, generic in `(c05, C)` -/

section MinorP

open Principia.Common.TernaryGoldbach.OL
open Principia.Common.TernaryGoldbach.MR

/-- **`M̃ ≤ cM·x`** from `MNumP c05 C φ p₀ cM fs` (generated from `OL.m_le_L`). -/
theorem m_le_P (c05 C : ℝ) (φ η b : ℝ → ℝ) (p₀ cM fs x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hmn : MNumP c05 C φ p₀ cM fs)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (fs * Real.log x - 0.021095) * x)
    (hP : p₀ * x ≤ pJE η b x) : mMCP c05 C φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mMCP
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **THE SPINE of (7.48) at `(c05, C)` on `HelfMajR`** (generated from `MR.minor_of_mnum_LR`:
`OstopL ↦ OstopP c05 C`, `MNumL ↦ MNumP c05 C`, `m_le_L ↦ m_le_P`). The constants are never
evaluated. Application only. -/
theorem minor_of_mnum_P (c05 C c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : HelfMajR ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hfe : FelipaAt fs ηp) (hos : OstopP c05 C ηp ηs φ) (hdl : DrujalLowPR J₀ ηp ηo)
    (hl1 : MajSp.l1 ηp ≤ 0.8673) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumL φ fs) (hmn : MNumP c05 C φ p₀ cM fs) :
    RT.MinorUpperAt c ηp ηs := by
  intro N _ hN
  obtain ⟨mp, cp, -⟩ := hm hpf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, hl1s, -, -, -⟩ := hnm
  have hx := MajSp.helfX_big N hN
  have hx0 := x_pos (helfgottX N) hx
  obtain ⟨b, hb⟩ := exists_supFn ηp hoh.2.2.2.2.1
  have hZ := hos hoh b hb (helfgottX N) hx
  have hS := hfe (helfgottX N) hx
  have hS0 := sPr_nonneg ηp (helfgottX N)
  have hE := hdu hsn.1 hsn.2.1 b hb (helfgottX N) hx
  have hA := hdl hrg.1 hsn.1 hl1 hrg.2.2.2.2.1 hrg.2.2.2.2.2.1 hrg.2.2.2.2.2.2
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (et_plusR ηp mp _ hx) (eb_plusR ηp mp _ hx)
  have hP := OC.pje_le_p J₀ p₀ ηp b (helfgottX N) hx0.le hJ0 hp hA hE
  have hM := m_le_P c05 C φ ηp b p₀ cM fs (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le_L φ ηp b fs (helfgottX N) hx hla hS
    (le_trans (mul_le_mul_of_nonneg_right hp0 hx0.le) hP)
  have hSt := sstar_leR ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact DS.z_close_d _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (DS.mt_le_d _ _ cM _ hM hT) hcM hSE hc

/-- **`RT.MinorUpperAt c η₊ η*` on Helfgott's weights at `HelfMajR`, generic in
`(c05, C, c, cM, J₀, p₀, fs)`** (generated from `MR.minorAt_ostopL_helfR`). Application only. -/
theorem minorAt_ostopP_helfR (c05 C c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (pf : RT.PlattFull) (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : FelipaAt fs HW.etaPlus) (hos : OstopP c05 C HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLowPR J₀ HW.etaPlus HW.etaCirc) (hla : LamberNumL HW.phi fs)
    (hmn : MNumP c05 C HW.phi p₀ cM fs) : RT.MinorUpperAt c HW.etaPlus HW.etaStar :=
  minor_of_mnum_P c05 C c cM J₀ p₀ fs hc hcM hJ0 hp hp0 HW.etaPlus HW.etaStar HW.etaCirc
    (HW.mconv HW.eta2 HW.phi) HW.phi hm pf RT.starScale_helf RW.regW_helf
    (EN.normsB27_helf BS.band_sharp) EN.supN_helf RW.ostopHyp_helf_full hfe hos hdl
    DS.l1_etaPlus_sharp (DB.dubistdie_all HW.etaPlus) RW.phiL1_helf hla hmn

end MinorP

end Principia.Common.TernaryGoldbach.OP
