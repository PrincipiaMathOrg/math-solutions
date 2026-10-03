/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopP

set_option autoImplicit false

/-!
# `M̃` with `c⁻` and `coefC`'s jump constant as PARAMETERS (`OstopPm`)

`OP.mMCP` carries `cor:coeur`'s `c⁻ = −1.306476` in three of its four sites: `OC.hR0C`
(`log √x − 1.306476`), the weight `2/(log x − 2·1.306476)`, and `OC.coefC`'s denominator. The
fourth site is `coefC`'s jump constant `−3.538215`, the value at `c⁻ = −1.306476` of
`−2(log(3/8) + c⁺ − (8/15)c⁻)` (`OC.jump_le`, 3905–3916). `1.306476` itself exists only because
`c_E ≥ 1.3325822` (`OC.cminus_le`); at `c⁻ = −1.39` the enclosure is PROVED (`CEL.cminus_139`) and
`CoeurY` follows from `EspagnWin 1.36` alone (`CYm.coeurY139_closed`).

Here `cm` (for `−c⁻`) and `jc` (the jump constant) are parameters. Generated from `OC.hR0C`,
`OC.coefC`, `OP.mMCP`, `OP.OstopP`, `OP.MNumP` and `OP`'s layer-1 composition by COUNTED
substitution (`scratchpad/ostoppm/gen_ostoppm.py`: `1.306476 ↦ cm` at the three sites,
`−3.538215 ↦ jc`, `OC.hR0C ↦ hR0Cm cm`, `OC.coefC ↦ coefCm cm jc`), each object PINNED to its
original at `(cm, jc) = (1.306476, −3.538215)` by `rfl` (section 2).

## The jump constant at `c⁻ = −1.39`

`−2(log(3/8) + 2.05315 + (8/15)·1.39) = −3.62730816` (mpmath, 30 digits). It is rounded UP, the
safe direction (a larger `coefC` is a larger `M̃`), to `−3.627308` (`jump_le_139`, from
`2¹⁰⁵⁴ ≤ 3⁶⁶⁵` and `log 2 < 0.6931471808`, the proof of `OC.jump_le` with `1.306476 ↦ 1.39`).
The value `−3.627309` lies BELOW the exact constant and is not a bound.

## The spine

```
 hR0Cm cm, coefCm cm jc, mMCPm c05 C cm jc          (generated; pinned: *_pin, by rfl)
 OstopPm c05 C cm jc, MNumPm c05 C cm jc            (generated; pinned: Iff.rfl)
 jump_le_139 : −2(log(3/8) + 2.05315 − (8/15)(−1.39)) ≤ −3.627308                  PROVED
 minor_of_mnum_Pm, minorAt_ostopPm_helfR : OP's layer 1 with OstopP ↦ OstopPm, MNumP ↦ MNumPm
```

Layer 1 never evaluates `cm` or `jc`: `m_le_Pm` unfolds `mMCPm` and matches it against
`MNumPm`, exactly as `OP.m_le_P` does. `minorAt_ostopP_helfR_pin` re-derives
`OP.minorAt_ostopP_helfR` from the parametric one at the pin.
-/

namespace Principia.Common.TernaryGoldbach.OPm

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Common.TernaryGoldbach.MinSp
open Principia.Common.TernaryGoldbach.OP

/-! ## (1) The quantities, parametric in `(cm, jc)` -/

/-- **`H̃(r₀) = (log(r₀+1) + c⁺)/(log √x − cm)`** (generated from `OC.hR0C`:
`1.306476 ↦ cm`). -/
noncomputable def hR0Cm (cm x : ℝ) : ℝ :=
  (Real.log 150001 + 2.05315) / (Real.log (Real.sqrt x) - cm)

/-- **`coefC` at `(cm, jc)`**: `7/15 + (jc + (8/15) log 49)/(log x − 2cm)` (generated from
`OC.coefC`: `−3.538215 ↦ jc`, `1.306476 ↦ cm`). -/
noncomputable def coefCm (cm jc x : ℝ) : ℝ :=
  7 / 15 + (jc + 8 / 15 * Real.log 49) / (Real.log x - 2 * cm)

/-- **`M̃` at `(c05, C, cm, jc)`** (generated from `OP.mMCP`: all three `c⁻` sites and the jump
constant). -/
noncomputable def mMCPm (c05 C cm jc : ℝ) (φ η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  gTP c05 C φ (x / 49) 150000 * (hR0Cm cm x * MinSp.sPr η x - MinSp.pJE η b x) +
    (2 / (Real.log x - 2 * cm) * intGTP c05 C φ (x / 49) +
      coefCm cm jc x * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) * MinSp.sPr η x

/-- **Link [ostopPm] — the corrected `thm:ostop` at `(c05, C, cm, jc)`** (generated from
`OP.OstopP`). -/
def OstopPm (c05 C cm jc : ℝ) (ηp ηs φ : ℝ → ℝ) : Prop :=
  MinSp.OstopHyp ηp ηs φ → ∀ b : ℝ → ℝ, MinSp.SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    MinSp.zMin ηp ηs x ≤
      (Real.sqrt (MajSp.l1 φ * x / 49 * (mMCPm c05 C cm jc φ ηp b x + MinSp.tT φ ηp b x)) +
        Real.sqrt (MinSp.sStar ηs x * MinSp.eBig b x)) ^ 2

/-- **Link [M̃] at `(c05, C, cm, jc)`** (generated from `OP.MNumP`). -/
def MNumPm (c05 C cm jc : ℝ) (φ : ℝ → ℝ) (p₀ c fs : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ fs * Real.log x - 0.021095 →
    p₀ ≤ p →
      gTP c05 C φ (x / 49) 150000 * (hR0Cm cm x * s - p) +
          (2 / (Real.log x - 2 * cm) * intGTP c05 C φ (x / 49) +
            coefCm cm jc x * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) * s ≤ c

/-! ## (2) The pins: at `(1.306476, −3.538215)` every object IS its original, by `rfl` -/

theorem hR0Cm_pin : hR0Cm 1.306476 = OC.hR0C :=
  rfl

theorem coefCm_pin : coefCm 1.306476 (-3.538215) = OC.coefC :=
  rfl

theorem mMCPm_pin (c05 C : ℝ) : mMCPm c05 C 1.306476 (-3.538215) = mMCP c05 C :=
  rfl

theorem ostopPm_pin (c05 C : ℝ) (ηp ηs φ : ℝ → ℝ) :
    OstopPm c05 C 1.306476 (-3.538215) ηp ηs φ ↔ OstopP c05 C ηp ηs φ :=
  Iff.rfl

theorem mnumPm_pin (c05 C : ℝ) (φ : ℝ → ℝ) (p₀ c fs : ℝ) :
    MNumPm c05 C 1.306476 (-3.538215) φ p₀ c fs ↔ MNumP c05 C φ p₀ c fs :=
  Iff.rfl

/-! ## (3) The jump constant at `c⁻ = −1.39` -/

set_option exponentiation.threshold 2000 in
/-- **The jump constant at `c⁻ = −1.39`, rounded UP**: `−2(log(3/8) + c⁺ − (8/15)c⁻) ≤ −3.627308`
at `c⁺ = 2.05315`, `c⁻ = −1.39` (exact `−3.62730816`), from `2¹⁰⁵⁴ ≤ 3⁶⁶⁵` and
`log 2 < 0.6931471808` (generated from `OC.jump_le`: `1.306476 ↦ 1.39`,
`−3.538215 ↦ −3.627308`). -/
theorem jump_le_139 :
    -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-1.39)) ≤ (-3.627308 : ℝ) := by
  have h1 : (2 : ℝ) ^ 1054 ≤ 3 ^ 665 := by norm_num
  have g1 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at g1
  push_cast at g1
  have h8 : Real.log (3 / 8) = Real.log 3 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hl2 := Real.log_two_lt_d9
  have hl1 := Real.log_two_gt_d9
  rw [h8]
  linarith

/-- **`OstopPm` is met by `η₊ = 0`** (generated from `OP.ostopP_zero`). -/
theorem ostopPm_zero (c05 C cm jc : ℝ) (ηs φ : ℝ → ℝ) : OstopPm c05 C cm jc 0 ηs φ := by
  intro _ b _ x _
  have hz : zMin 0 ηs x = 0 := by simp [zMin, Smooth.smSum_zero]
  rw [hz]
  exact sq_nonneg _

/-! ## (4) The monotonicities of `MNumPm` -/

/-- (generated from `OP.mnumP_floor_mono`) -/
theorem mnumPm_floor_mono (c05 C cm jc : ℝ) (φ : ℝ → ℝ) (p₀ p₁ c fs : ℝ) (h01 : p₀ ≤ p₁)
    (h : MNumPm c05 C cm jc φ p₀ c fs) : MNumPm c05 C cm jc φ p₁ c fs :=
  fun x hx s p hs0 hs hp => h x hx s p hs0 hs (le_trans h01 hp)

/-- (generated from `OP.mnumP_const_mono`) -/
theorem mnumPm_const_mono (c05 C cm jc : ℝ) (φ : ℝ → ℝ) (p₀ c c' fs : ℝ) (hc : c ≤ c')
    (h : MNumPm c05 C cm jc φ p₀ c fs) : MNumPm c05 C cm jc φ p₀ c' fs :=
  fun x hx s p hs0 hs hp => le_trans (h x hx s p hs0 hs hp) hc

/-- (generated from `OP.mnumP_slope_mono`) -/
theorem mnumPm_slope_mono (c05 C cm jc : ℝ) (φ : ℝ → ℝ) (p₀ c fs fs' : ℝ) (hf : fs' ≤ fs)
    (h : MNumPm c05 C cm jc φ p₀ c fs) : MNumPm c05 C cm jc φ p₀ c fs' := by
  intro x hx s p hs0 hs hp
  have hL := MajSp.log_ge_one x hx
  have h1 : fs' * Real.log x ≤ fs * Real.log x := mul_le_mul_of_nonneg_right hf (by linarith)
  exact h x hx s p hs0 (by linarith) hp

/-! ## (5) THE LAYER-1 COMPOSITION, generic in `(c05, C, cm, jc)` -/

section MinorPm

open Principia.Common.TernaryGoldbach.OL
open Principia.Common.TernaryGoldbach.MR

/-- **`M̃ ≤ cM·x`** from `MNumPm c05 C cm jc φ p₀ cM fs` (generated from `OP.m_le_P`). -/
theorem m_le_Pm (c05 C cm jc : ℝ) (φ η b : ℝ → ℝ) (p₀ cM fs x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hmn : MNumPm c05 C cm jc φ p₀ cM fs)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (fs * Real.log x - 0.021095) * x)
    (hP : p₀ * x ≤ pJE η b x) : mMCPm c05 C cm jc φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mMCPm
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **THE SPINE of (7.48) at `(c05, C, cm, jc)` on `HelfMajR`** (generated from
`OP.minor_of_mnum_P`: `OstopP ↦ OstopPm`, `MNumP ↦ MNumPm`, `m_le_P ↦ m_le_Pm`). The constants
are never evaluated. Application only. -/
theorem minor_of_mnum_Pm (c05 C cm jc c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : HelfMajR ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hfe : FelipaAt fs ηp) (hos : OstopPm c05 C cm jc ηp ηs φ) (hdl : DrujalLowPR J₀ ηp ηo)
    (hl1 : MajSp.l1 ηp ≤ 0.8673) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumL φ fs) (hmn : MNumPm c05 C cm jc φ p₀ cM fs) :
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
  have hM := m_le_Pm c05 C cm jc φ ηp b p₀ cM fs (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le_L φ ηp b fs (helfgottX N) hx hla hS
    (le_trans (mul_le_mul_of_nonneg_right hp0 hx0.le) hP)
  have hSt := sstar_leR ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact DS.z_close_d _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (DS.mt_le_d _ _ cM _ hM hT) hcM hSE hc

/-- **`RT.MinorUpperAt c η₊ η*` on Helfgott's weights at `HelfMajR`, generic in
`(c05, C, cm, jc, c, cM, J₀, p₀, fs)`** (generated from `OP.minorAt_ostopP_helfR`). Application
only. -/
theorem minorAt_ostopPm_helfR (c05 C cm jc c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (pf : RT.PlattFull) (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : FelipaAt fs HW.etaPlus) (hos : OstopPm c05 C cm jc HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLowPR J₀ HW.etaPlus HW.etaCirc) (hla : LamberNumL HW.phi fs)
    (hmn : MNumPm c05 C cm jc HW.phi p₀ cM fs) : RT.MinorUpperAt c HW.etaPlus HW.etaStar :=
  minor_of_mnum_Pm c05 C cm jc c cM J₀ p₀ fs hc hcM hJ0 hp hp0 HW.etaPlus HW.etaStar
    HW.etaCirc
    (HW.mconv HW.eta2 HW.phi) HW.phi hm pf RT.starScale_helf RW.regW_helf
    (EN.normsB27_helf BS.band_sharp) EN.supN_helf RW.ostopHyp_helf_full hfe hos hdl
    DS.l1_etaPlus_sharp (DB.dubistdie_all HW.etaPlus) RW.phiL1_helf hla hmn

/-- **The pin, at the level of the composition**: `OP.minorAt_ostopP_helfR`'s statement is
`minorAt_ostopPm_helfR` at `(1.306476, −3.538215)`, through `ostopPm_pin`, `mnumPm_pin`. -/
theorem minorAt_pin (c05 C c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (pf : RT.PlattFull) (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : FelipaAt fs HW.etaPlus) (hos : OstopP c05 C HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLowPR J₀ HW.etaPlus HW.etaCirc) (hla : LamberNumL HW.phi fs)
    (hmn : MNumP c05 C HW.phi p₀ cM fs) : RT.MinorUpperAt c HW.etaPlus HW.etaStar :=
  minorAt_ostopPm_helfR c05 C 1.306476 (-3.538215) c cM J₀ p₀ fs hc hcM hJ0 hp hp0 pf hm hfe
    ((ostopPm_pin c05 C _ _ _).mpr hos) hdl hla ((mnumPm_pin c05 C _ _ _ _).mpr hmn)

end MinorPm

end Principia.Common.TernaryGoldbach.OPm
