/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopSpineP
import Principia.Common.TernaryGoldbach.OstopPm
import Principia.Common.TernaryGoldbach.CoeurCm

set_option autoImplicit false

/-!
# The spine of `thm:ostop` at `(c05, C, cm, jc)`: `OPm.OstopPm` from `CYm.CoeurYcm 2.05315 cm`

`OstopSpineP.lean` composes `OP.OstopP c05 C` from its layer-2 links, with `cor:coeur` typed as
`OC.CoeurY` (denominator `log √x − 1.306476`). Here the `c⁻`-dependent half is regenerated at a
PARAMETRIC `cm` (`scratchpad/ostoppm/gen_ostopspinepm.py`, counted substitution of
`OstopSpineP.lean` and of `OS`'s `H`, jump and top lemmas). The `CoeurY` input becomes
`CYm.CoeurYcm 2.05315 cm`, which at `cm = 1.39` is `CYm.coeurY139_closed` (from `EspagnWin 1.36`
ALONE: no `c_E` enclosure).

## Where the four `c⁻` sites go

* `H(r) = (log(r+1) + c⁺)/(log √x − cm)` (`hCm`, pinned to `OS.hC`), so `CoeurYcm` IS the level
  bound `C(r) ≤ H(r)S` (`coeurYcm_iff_h`) and `H(r₀) = OPm.hR0Cm cm` (`hCm_r0`);
* the weight `2/(log x − 2cm)` of `∫g̃/r` (`top_lePm`, the sum-to-integral step);
* `coefCm cm jc`'s denominator, and its jump constant `jc`: `jump_le_coefCm_of` prices the jump
  `1 − H(t)` at every `t ≥ r₁` whenever `−2(log(3/8) + c⁺ − (8/15)(−cm)) ≤ jc` (`hjm`).

## The side conditions (all four discharged at `(1.39, −3.627308)`)

* `hcm : 1.306476 ≤ cm` — `⌊r₁⌋ ≥ 150001(7D_h/30 + 1)` (`floor_big_m`, from `OS.floor_big`: a
  larger `cm` is a smaller `D_h = log √x − cm`);
* `hcm8 : cm ≤ 8` — `D_h > 0` (`dhm_pos`, from `OS.dh_pos`: `log √x − 1.306476 > 7`);
* `hjc : jc ≤ −3` — `coefCm ≤ 7/15` (`coefCm_le`);
* `hjm` — the jump constant is an upper bound for the exact one (`OPm.jump_le_139` at `1.39`).

```
 top_lePm, z1_boundPm        (generated from OSP.top_leP, OSP.z1_boundP)                 PROVED
 ostopPm_of_open : CoeurYcm 2.05315 cm → MinMainP → RS62Thm15 → GYMonoP → HLeGP → Austeria →
                   GTMonoP → CoprarP → EBound2 → JgeE → TopStepP → OPm.OstopPm c05 C cm jc
 ostopP_of_open_pin : OSP.ostopP_of_open re-derived at (1.306476, −3.538215)
```
-/

namespace Principia.Common.TernaryGoldbach.OSPm

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Common.TernaryGoldbach.OS
open Principia.Common.TernaryGoldbach.OP
open Principia.Common.TernaryGoldbach.OPm
open Principia.Common.TernaryGoldbach.OSP

/-! ## (1) `H` at `cm`, and `CoeurYcm` as the level bound -/

/-- **`H(r) = (log(r+1) + c⁺)/(log √x − cm)`** (generated from `OS.hC`: `1.306476 ↦ cm`). -/
noncomputable def hCm (cm x : ℝ) (r : ℕ) : ℝ :=
  (Real.log ((r : ℝ) + 1) + 2.05315) / (Real.log (Real.sqrt x) - cm)

/-- **The pin**: `hCm 1.306476` IS `OS.hC`. -/
theorem hCm_pin : hCm 1.306476 = OS.hC :=
  rfl

/-- **`H(r₀) = OPm.hR0Cm cm x`** (generated from `OS.hC_r0`). -/
theorem hCm_r0 (cm x : ℝ) : hCm cm x 150000 = hR0Cm cm x := by
  unfold hCm hR0Cm
  norm_num

/-- **`CYm.CoeurYcm 2.05315 cm` IS the bound `C(r) ≤ H(r)S`**, by `Iff.rfl` (generated from
`OS.coeurY_iff`). -/
theorem coeurYcm_iff_h (cm : ℝ) (ηp : ℝ → ℝ) : CYm.CoeurYcm 2.05315 cm ηp ↔
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) < MinSp.r1y (x / 49) →
      ∫ α in Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49), ‖OC.s1Sum ηp x α‖ ^ 2 ≤
        hCm cm x r * MinSp.sPr ηp x :=
  Iff.rfl

/-! ## (2) The side conditions -/

/-- **`D_h = log √x − cm > 0`** for `cm ≤ 8`, `x ≥ 4.9·10²⁶` (`OS.dh_pos`:
`log √x − 1.306476 > 7`). -/
theorem dhm_pos (cm : ℝ) (hcm8 : cm ≤ 8) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 < Real.log (Real.sqrt x) - cm := by
  have h := dh_pos x hx
  linarith

/-- **`coefCm ≤ 7/15`** for `jc ≤ −3` (generated from `OS.coefC_le`: `−3.538215 ↦ jc`). -/
theorem coefCm_le (cm jc : ℝ) (hcm8 : cm ≤ 8) (hjc : jc ≤ -3) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : coefCm cm jc x ≤ 7 / 15 := by
  unfold coefCm
  have hl2 := Real.log_two_lt_d9
  have h49 := log49_le
  have hD : 0 < Real.log x - 2 * cm := by
    have h := dhm_pos cm hcm8 x hx
    rw [Real.log_sqrt (MinSp.x_pos x hx).le] at h
    linarith
  have hn : jc + 8 / 15 * Real.log 49 ≤ 0 := by linarith
  have h := div_nonpos_iff.mpr (Or.inr ⟨hn, hD.le⟩)
  linarith

/-- **The jump at ANY `t ≥ r₁`, at `(cm, jc)`**: `1 − (log t + c⁺)/(log √x − cm) ≤ coefCm cm jc x`
whenever `jc` bounds the exact jump constant (generated from `OS.jump_le_coefC_of`:
`OC.jump_le ↦ hjm`, `log x ≥ 3 ↦ log x ≥ 16.6`). -/
theorem jump_le_coefCm_of (cm jc : ℝ) (hcm8 : cm ≤ 8)
    (hjm : -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-cm)) ≤ jc) (x t : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) (ht : MinSp.r1y (x / 49) ≤ t) :
    1 - (Real.log t + 2.05315) / (Real.log (Real.sqrt x) - cm) ≤ coefCm cm jc x := by
  have hx0 : 0 < x := MinSp.x_pos x hx
  have hL : 16.6 ≤ Real.log x := by
    have h := dh_pos x hx
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hr1 : 0 < MinSp.r1y (x / 49) := by
    unfold MinSp.r1y
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hy0 _)
  have hlr : Real.log (MinSp.r1y (x / 49)) =
      Real.log (3 / 8) + 4 / 15 * (Real.log x - Real.log 49) := by
    unfold MinSp.r1y
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hy0 _).ne', Real.log_rpow hy0,
      Real.log_div hx0.ne' (by norm_num)]
  have hmono : Real.log (MinSp.r1y (x / 49)) ≤ Real.log t := Real.log_le_log hr1 ht
  have hD : 0 < Real.log x - 2 * cm := by linarith
  have hsq : Real.log (Real.sqrt x) - cm = (Real.log x - 2 * cm) / 2 := by
    rw [Real.log_sqrt hx0.le]
    ring
  rw [hsq]
  unfold coefCm
  refine OC.jump_alg _ _ _ hD ?_
  rw [hlr] at hmono
  linarith

/-- **The integer top level is high enough at `cm ≥ 1.306476`**: `OS.floor_big`, since `D_h`
decreases in `cm`. -/
theorem floor_big_m (cm : ℝ) (hcm : 1.306476 ≤ cm) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    150001 * (7 * (Real.log (Real.sqrt x) - cm) / 30 + 1) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
  have h := floor_big x hx
  linarith

/-! ## (3) The top of `prop:palan`, `Z₁`, and the composition at `(c05, C, cm, jc)` -/

/-- **The top of `prop:palan`** at `(c05, C, cm, jc)` (generated from `OSP.top_leP`). -/
theorem top_lePm (c05 C cm jc : ℝ) (hcm : 1.306476 ≤ cm) (hcm8 : cm ≤ 8) (hjc : jc ≤ -3)
    (hjm : -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-cm)) ≤ jc) (φ : ℝ → ℝ) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x)
    (hanti : AntitoneOn (gTP c05 C φ (x / 49)) (Set.Icc 150000 (MinSp.r1y (x / 49))))
    (hg1 : 0 ≤ gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)))
    (hts : Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) * gTP c05 C φ (x / 49) ⌊MinSp.r1y (x / 49)⌋₊ ≤
      Real.sqrt (MinSp.r1y (x / 49)) * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) :
    ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (hCm cm x (r + 1) - hCm cm x r) * gNP c05 C φ x (r + 1) +
        (1 - hCm cm x ⌊MinSp.r1y (x / 49)⌋₊) * gNP c05 C φ x ⌊MinSp.r1y (x / 49)⌋₊ ≤
      2 / (Real.log x - 2 * cm) * intGTP c05 C φ (x / 49) +
        coefCm cm jc x * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)) := by
  have hx0 := MinSp.x_pos x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hDh := dhm_pos cm hcm8 x hx
  have hRb := floor_big_m cm hcm x hx
  have hr10 := r1y_nonneg (x / 49) hy0.le
  have hRr1 : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) := Nat.floor_le hr10
  have hr1R : MinSp.r1y (x / 49) < (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hRn : 150000 ≤ ⌊MinSp.r1y (x / 49)⌋₊ := by
    have h : (150000 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by linarith
    exact_mod_cast h
  have e150 : ((150000 : ℕ) : ℝ) = 150000 := by norm_num
  have hantiR : AntitoneOn (gTP c05 C φ (x / 49))
      (Set.Icc ((150000 : ℕ) : ℝ) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ)) := by
    rw [e150]
    exact hanti.mono (Set.Icc_subset_Icc le_rfl hRr1)
  have hgR1 : gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)) ≤
      gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) :=
    hanti ⟨by linarith, hRr1⟩ ⟨by linarith, le_rfl⟩ hRr1
  have hgR : 0 ≤ gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := le_trans hg1 hgR1
  have hsh := sum_int_sharp 150000 ⌊MinSp.r1y (x / 49)⌋₊ (by norm_num) hRn
    (gTP c05 C φ (x / 49)) hantiR
  have hext : ∫ u in ((150000 : ℕ) : ℝ)..(⌊MinSp.r1y (x / 49)⌋₊ : ℝ),
      gTP c05 C φ (x / 49) u / u ≤
      intGTP c05 C φ (x / 49) := by
    rw [e150]
    unfold intGTP
    have hint1 : IntervalIntegrable (fun u => gTP c05 C φ (x / 49) u / u) volume 150000
        (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) :=
      gdiv_int _ _ _ (by norm_num) (by linarith) (hanti.mono (Set.Icc_subset_Icc le_rfl hRr1))
    have hint2 : IntervalIntegrable (fun u => gTP c05 C φ (x / 49) u / u) volume
        (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) (MinSp.r1y (x / 49)) :=
      gdiv_int _ _ _ (by linarith) hRr1 (hanti.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hnn : 0 ≤ ∫ u in (⌊MinSp.r1y (x / 49)⌋₊ : ℝ)..(MinSp.r1y (x / 49)),
        gTP c05 C φ (x / 49) u / u := by
      refine intervalIntegral.integral_nonneg hRr1 fun u hu => ?_
      have hu0 : 0 < u := by linarith [hu.1]
      exact div_nonneg (le_trans hg1 (hanti ⟨by linarith [hu.1], hu.2⟩ ⟨by linarith, le_rfl⟩
        hu.2)) hu0.le
    linarith
  have hsum : ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      (hCm cm x (r + 1) - hCm cm x r) * gNP c05 C φ x (r + 1) =
      (∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (Real.log ((r : ℝ) + 2) - Real.log ((r : ℝ) + 1)) * gTP c05 C φ (x / 49) ((r : ℝ) + 1)) /
        (Real.log (Real.sqrt x) - cm) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold hCm gNP
    have e1 : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    have e2 : (r : ℝ) + 1 + 1 = (r : ℝ) + 2 := by ring
    rw [e1, e2]
    field_simp
    ring
  have hj : 1 - hCm cm x ⌊MinSp.r1y (x / 49)⌋₊ ≤ coefCm cm jc x := by
    unfold hCm
    exact jump_le_coefCm_of cm jc hcm8 hjm x _ hx hr1R.le
  have hstep : 2 * (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) *
      (gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) -
        gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) ≤
      gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
    have hs0 : 0 < Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hst : Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ Real.sqrt (MinSp.r1y (x / 49)) :=
      Real.sqrt_le_sqrt hRr1
    have h1 : Real.sqrt (MinSp.r1y (x / 49)) ^ 2 -
        Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ^ 2 ≤ 1 := by
      rw [Real.sq_sqrt hr10, Real.sq_sqrt (by linarith)]
      linarith
    have h := top_step_alg _ _ _ _ hs0 hst h1 hgR hts
    rwa [Real.sq_sqrt (by linarith)] at h
  have hTel := tel_bound 150000 ⌊MinSp.r1y (x / 49)⌋₊ (by norm_num) (by omega)
  have hRb' : (((150000 : ℕ) : ℝ) + 1) * (7 * (Real.log (Real.sqrt x) - cm) / 30 + 1) ≤
      (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
    rw [e150]
    norm_num
    linarith
  have hD2 : 2 / (Real.log x - 2 * cm) * intGTP c05 C φ (x / 49) =
      intGTP c05 C φ (x / 49) / (Real.log (Real.sqrt x) - cm) := by
    rw [Real.log_sqrt hx0.le]
    have hD : Real.log x - 2 * cm ≠ 0 := by
      have h := hDh
      rw [Real.log_sqrt hx0.le] at h
      intro h0
      linarith
    field_simp
  have hgN : gNP c05 C φ x ⌊MinSp.r1y (x / 49)⌋₊ =
      gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := rfl
  rw [hsum, hD2, hgN]
  exact top_combine _ _ _ _ _ _ _ _ _ _ _ (by linarith) (by positivity) hsh hext hj
    (coefCm_le cm jc hcm8 hjc x hx) hgR hgR1 hstep hTel hRb'

/-- **`Z₁ ≤ |φ|₁(x/49)(M̃ + T)`** at `(c05, C, cm, jc)` on `CoeurYcm 2.05315 cm` (generated from
`OSP.z1_boundP`). -/
theorem z1_boundPm (c05 C cm jc : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (hcm : 1.306476 ≤ cm)
    (hcm8 : cm ≤ 8) (hjc : jc ≤ -3)
    (hjm : -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-cm)) ≤ jc) (ηp ηs φ b : ℝ → ℝ)
    (hpal : PalanLink) (hi0 : I0SLink) (hco : CYm.CoeurYcm 2.05315 cm ηp)
    (hgo : GorshP c05 C ηs φ)
    (hgm : GTMonoP c05 C φ) (hcp : CoprarP c05 C ηs φ) (hts : TopStepP c05 C φ)
    (hsd : ∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Set.Ioi 0)) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hsum : Summable fun n => ‖aP ηp x n‖) (hE2 : s2Sq ηp x ≤ MinSp.eBig b x)
    (hEJ : MinSp.eBig b x ≤ x * MajSp.amaj ηp x) :
    ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      MajSp.l1 φ * x / 49 * (mMCPm c05 C cm jc φ ηp b x + MinSp.tT φ ηp b x) := by
  have hx0 := MinSp.x_pos x hx
  have hy := MinSp.y_ge x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hanti := hgm (x / 49) hy
  have hr10 := r1y_nonneg (x / 49) hy0.le
  have hRb := floor_big_m cm hcm x hx
  have hDh := dhm_pos cm hcm8 x hx
  have hRr1 : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) := Nat.floor_le hr10
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hRn : 150000 + 1 ≤ ⌊MinSp.r1y (x / 49)⌋₊ := by exact_mod_cast hR150
  have hg1 : 0 ≤ gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)) :=
    gTP_nonneg c05 C hc05 hC0 φ hφ0 _ _ hy (by linarith) le_rfl
  have e150 : ((150000 : ℕ) : ℝ) = 150000 := by norm_num
  have hga : 0 ≤ gTP c05 C φ (x / 49) ((150000 : ℕ) : ℝ) := by
    rw [e150]
    exact le_trans hg1 (hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith))
  have hK0 : 0 ≤ 1 / MinSp.kK (x / 49) := by
    unfold MinSp.kK
    have := GS.log_gt (x / 49) hy
    positivity
  have hc3 := cPhi3_nonneg φ (MinSp.kK (x / 49)) hK0
  have hLy : 0 ≤ MajSp.l1 φ * (x / 49) := mul_nonneg (MajSp.l1_nonneg φ) hy0.le
  have hS0 := MinSp.sPr_nonneg ηp x
  have hGanti : ∀ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      gGP c05 C φ x (r + 1) ≤ gGP c05 C φ x r := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hr0 : (150000 : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by exact_mod_cast hr.2
    have hrr : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h := hanti ⟨hr0, by linarith⟩ ⟨by linarith, by linarith⟩ hrr
    unfold gGP
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (MajSp.l1_nonneg φ)) hy0.le
  have hlev : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ ≤
      gGP c05 C φ x ⌊MinSp.r1y (x / 49)⌋₊ + ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (gGP c05 C φ x r - gGP c05 C φ x (r + 1)) *
          (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun _ => (1 : ℝ)) α := by
    intro α hα
    refine level_bound (fun s => Smooth.arcs 8 s (x / 49)) 150000 _ hRn
      (fun s s' _ h => arcs_mono_r 8 (by norm_num) s s' h _ hy0) (gGP c05 C φ x) hGanti _ α
      (fun s hs1 hs2 hsα => ?_) (fun hin => ?_)
    · have hs : (s : ℝ) ≤ MinSp.r1y (x / 49) :=
        le_trans (by exact_mod_cast hs2) hRr1
      exact hgo hsd hφ0 hφi x hx s hs1 hs α hsα
    · have hA0 : α ∈ OC.annA0 x := ⟨hα.1, hin, hα.2⟩
      have h := hcp hsd hφ0 hφi x hx α hA0
      unfold gGP
      rw [e150]
      exact h
  have hstep1 := z1_le ηp ηs x hx _ (gGP c05 C φ x) hsum hlev
  have hΦ : ∀ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      cumC ηp x r - jOne ηp x ≤ hCm cm x r * MinSp.sPr ηp x - jOne ηp x := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hrl : (r : ℝ) < MinSp.r1y (x / 49) :=
      lt_of_lt_of_le (by exact_mod_cast hr.2) hRr1
    exact sub_le_sub_right (hco x hx r hr.1 hrl) _
  have htop := top_lePm c05 C cm jc hcm hcm8 hjc hjm φ x hx hanti hg1 (hts (x / 49) hy)
  have hJ := hi0 ηp b x hx hsum hE2 hEJ
  have hZ := z1_assemble hpal 150000 _ (by omega) (gGP c05 C φ x) (gNP c05 C φ x) (hCm cm x)
    (fun r => cumC ηp x r - jOne ηp x) (MinSp.cPhi3 φ (MinSp.kK (x / 49))) (MajSp.l1 φ)
    (x / 49) (MinSp.sPr ηp x) (jOne ηp x) _ _ (hR0Cm cm x) (MinSp.pJE ηp b x) (fun r => rfl)
    hGanti hΦ hstep1 htop (hCm_r0 cm x) hJ hLy hS0 hga hc3
  refine le_trans hZ (le_of_eq ?_)
  unfold mMCPm MinSp.tT gNP
  push_cast
  ring

/-- **`OPm.OstopPm c05 C cm jc η₊ η* φ` from its layer-2 links** (generated from
`OSP.ostopP_of_links`). Generic in `(η₊, η*, φ)`. -/
theorem ostopPm_of_links (c05 C cm jc : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C)
    (hcm : 1.306476 ≤ cm) (hcm8 : cm ≤ 8) (hjc : jc ≤ -3)
    (hjm : -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-cm)) ≤ jc) (ηp ηs φ : ℝ → ℝ)
    (hpal : PalanLink) (hspl : SplitLink) (hi0 : I0SLink) (hco : CYm.CoeurYcm 2.05315 cm ηp)
    (hgo : GorshP c05 C ηs φ) (hgm : GTMonoP c05 C φ) (hcp : CoprarP c05 C ηs φ)
    (heb : EBound2 ηp)
    (hs1 : ∀ t : ℝ, 0 ≤ t → |ηp t| ≤ 1.079955) (hs2 : ∀ t : ℝ, 0 ≤ t → |ηp t * t| ≤ 1.19073)
    (hjE : JgeE ηp) (hts : TopStepP c05 C φ) : OstopPm c05 C cm jc ηp ηs φ := by
  intro hoh b hb x hx
  obtain ⟨hsd, -, hφ0, hφi, -, -, -⟩ := hoh
  by_cases hsum : Summable fun n => ‖aP ηp x n‖
  swap
  · have h0 : MinSp.zMin ηp ηs x = 0 := by
      unfold MinSp.zMin
      simp [smSum_eq, eSum_junk _ hsum]
    rw [h0]
    positivity
  have hηs0 : ∀ t : ℝ, 0 ≤ ηs t := etaS_nonneg ηs φ hsd hφ0
  have hmin : MeasurableSet (Smooth.minorSet x) :=
    measurableSet_Ioc.diff (measurableSet_arcs _ _ _)
  have hsubm : Smooth.minorSet x ⊆ Set.Icc 0 1 := fun α h => Set.Ioc_subset_Icc_self h.1
  have hcs : Continuous fun α => ‖Smooth.smSum ηs x α‖ := (eSum_continuous (aP ηs x)).norm
  have hE2 := heb hs1 hs2 b hb x hx
  have hZ1 := z1_boundPm c05 C cm jc hc05 hC0 hcm hcm8 hjc hjm ηp ηs φ b hpal hi0 hco hgo hgm
    hcp hts hsd hφ0 hφi x hx
    hsum hE2 (hjE b hb x hx)
  have hZ2 := z2_le ηp ηs x hsum hηs0 _ hE2
  have hZ1n : 0 ≤ ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hZ2n : 0 ≤ ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hF : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2 ≤
      ‖Smooth.smSum ηs x α‖ * (‖OC.s1Sum ηp x α‖ + ‖s2Sum ηp x α‖) ^ 2 := by
    intro α _
    rw [hspl ηp x hsum α]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2) (norm_nonneg _)
  refine le_sq_of_forall_t _ _ _ (le_trans hZ1n hZ1) (le_trans hZ2n hZ2) fun t ht => ?_
  have hm := mink (Smooth.minorSet x) hmin hsubm (fun α => ‖Smooth.smSum ηs x α‖)
    (fun α => ‖OC.s1Sum ηp x α‖) (fun α => ‖s2Sum ηp x α‖)
    (fun α => ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2) hcs (s1_cont ηp x)
    (s2_cont ηp x) (fun α => norm_nonneg _) (fun α _ => mul_nonneg (norm_nonneg _)
      (sq_nonneg _)) hF t ht
  have h1t : 0 ≤ 1 + t := by linarith
  have h2t : 0 ≤ 1 + 1 / t := by positivity
  calc MinSp.zMin ηp ηs x
      ≤ (1 + t) * (∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2) +
        (1 + 1 / t) * ∫ α in Smooth.minorSet x,
          ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 := hm
    _ ≤ (1 + t) * (MajSp.l1 φ * x / 49 * (mMCPm c05 C cm jc φ ηp b x + MinSp.tT φ ηp b x)) +
        (1 + 1 / t) * (MinSp.sStar ηs x * MinSp.eBig b x) :=
      add_le_add (mul_le_mul_of_nonneg_left hZ1 h1t) (mul_le_mul_of_nonneg_left hZ2 h2t)

/-- **`OPm.OstopPm` on Helfgott's weights from the named layer-2 links** (generated from
`OSP.ostopP_of_layer2`). Application only. -/
theorem ostopPm_of_layer2 (c05 C cm jc : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C)
    (hcm : 1.306476 ≤ cm) (hcm8 : cm ≤ 8) (hjc : jc ≤ -3)
    (hjm : -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-cm)) ≤ jc)
    (hco : CYm.CoeurYcm 2.05315 cm HW.etaPlus)
    (hgo : GorshP c05 C HW.etaStar HW.phi) (hgm : GTMonoP c05 C HW.phi)
    (hcp : CoprarP c05 C HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus)
    (hjE : JgeE HW.etaPlus) (hts : TopStepP c05 C HW.phi) :
    OstopPm c05 C cm jc HW.etaPlus HW.etaStar HW.phi :=
  ostopPm_of_links c05 C cm jc hc05 hC0 hcm hcm8 hjc hjm HW.etaPlus HW.etaStar HW.phi palanLink
    splitLink i0sLink hco
    hgo hgm hcp heb
    EN.supN_helf.1 EN.supN_helf.2.1 hjE hts

/-- **`OPm.OstopPm` with `GorshP` itself composed** (generated from `OSP.ostopP_of_open`).
Application only. -/
theorem ostopPm_of_open (c05 C cm jc : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C)
    (hcm : 1.306476 ≤ cm) (hcm8 : cm ≤ 8) (hjc : jc ≤ -3)
    (hjm : -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-cm)) ≤ jc)
    (hco : CYm.CoeurYcm 2.05315 cm HW.etaPlus)
    (hmm : MinMainP c05 C) (h15 : GS.RS62Thm15) (hmo : GSP.GYMonoP c05 C)
    (hhl : GSP.HLeGP c05 C) (hau : GS.Austeria) (hgm : GTMonoP c05 C HW.phi)
    (hcp : CoprarP c05 C HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus) (hjE : JgeE HW.etaPlus)
    (hts : TopStepP c05 C HW.phi) : OstopPm c05 C cm jc HW.etaPlus HW.etaStar HW.phi :=
  ostopPm_of_layer2 c05 C cm jc hc05 hC0 hcm hcm8 hjc hjm hco
    (GSP.gorshP_of_open c05 C hc05 hC0 HW.etaStar HW.phi hmm h15 hmo hhl hau) hgm hcp heb
    hjE hts

/-- **The pin, at the level of the composition**: `OSP.ostopP_of_open`'s statement is
`ostopPm_of_open` at `(1.306476, −3.538215)` — `OC.CoeurY` IS `CoeurYcm 2.05315 1.306476`, and the
jump side condition is `OC.jump_le`. -/
theorem ostopP_of_open_pin (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C)
    (hco : OC.CoeurY HW.etaPlus) (hmm : MinMainP c05 C) (h15 : GS.RS62Thm15)
    (hmo : GSP.GYMonoP c05 C) (hhl : GSP.HLeGP c05 C) (hau : GS.Austeria)
    (hgm : GTMonoP c05 C HW.phi) (hcp : CoprarP c05 C HW.etaStar HW.phi)
    (heb : EBound2 HW.etaPlus) (hjE : JgeE HW.etaPlus) (hts : TopStepP c05 C HW.phi) :
    OstopP c05 C HW.etaPlus HW.etaStar HW.phi :=
  (ostopPm_pin c05 C _ _ _).mp (ostopPm_of_open c05 C 1.306476 (-3.538215) hc05 hC0 le_rfl
    (by norm_num) (by norm_num) OC.jump_le hco hmm h15 hmo hhl hau hgm hcp heb hjE hts)

/-- **The instance's side conditions at `(cm, jc) = (1.39, −3.627308)`**. -/
theorem side_139 : (1.306476 : ℝ) ≤ 1.39 ∧ (1.39 : ℝ) ≤ 8 ∧ (-3.627308 : ℝ) ≤ -3 ∧
    -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-1.39)) ≤ (-3.627308 : ℝ) :=
  ⟨by norm_num, by norm_num, by norm_num, jump_le_139⟩

end Principia.Common.TernaryGoldbach.OSPm
