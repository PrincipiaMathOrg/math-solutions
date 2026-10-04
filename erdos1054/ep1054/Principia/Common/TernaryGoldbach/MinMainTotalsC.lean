/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPiecesIIC
import Principia.Common.TernaryGoldbach.MinMainP

set_option autoImplicit false

/-!
# The minor-arc Main Theorem at the erratum's constants: `OP.MinMainP 0.896 45.7575`

`eq:passi` is false (`TypeIISpineC`); absorbing it additively turns `eq:senorburns`' factor
`√(0.30214 log δ₀q + 0.67506)` into `√(0.30214 log δ₀q + 0.76746)` (`MPIIC.bIIC`). The Totals'
AM-GM (book `minarctotals.tex` 2257-2288, corrected in `MT.amgm_main`) then has the constant

`log 2/(2√ρ) + 0.002·0.723/(2√ρ) + √ρ·0.76746/2 = 0.8957679` at `√ρ = 1.8434` (`≤ 0.896`),

against `0.8102106` (`≤ 0.811`) before. The `ℓ`-coefficients `0.27125`, `0.41415` (i.e. `MinSp.rR`)
do not involve the constant and are KEPT; re-optimising `√ρ` buys `≈ 10⁻⁴` of `M̃` (the optimum is
`√ρ ≈ 1.874` at `x = 4.9·10²⁶`) and would change `MinSp.rR`, so it is not done.

* `amgm_mainC`, `main_leC`, `arithW_896 : ArithAtWC 0.896 45.7575` — PROVED (`MT.amgm_main`,
  `MT.main_le`, `MMP.arith_811W` at the new factor and constant);
* `minMain1_of_arithWC` — the Totals spine with `MPIIC.TypeIIC` (application);
* `coexistArithC : CoexistArithC` — PROVED (`MPA.coexistArith` at `0.896`: the degree-6 polynomial
  inequality keeps a slack of `≈ 30` at `w = 1.69` against an increase `≤ 0.39`);
* `minMain2L_ofC` — `MPc.minMain2L_of` with the first case at `0.896` (application);
* **`minMainPC_of_links`**, **`minMainPC_of_open`** : `OP.MinMainP 0.896 45.7575` from the links
  with `Vinland1At`/`EriksagaAt` replaced by `T2SC.Vinland1AtC`/`T2SC.EriksagaAtC`.

## Downstream (priced this round, NOT certified here)

Every consumer of `OP.MinMainP c05 C` above it is generic in `c05` (`MOP.gYMonoP_of`,
`MOP.hLeGP_of`, `MOP.gtMonoP_of`, `MOP.coprarP_of_L`, `MTOP.topStepP_of`, `OSPm.ostopPm_of_open`,
all under `0.5 ≤ c05`) EXCEPT the `M̃` certificate `OPm.MNumPm 0.811 …`/`OP.MNumP 0.811 …`. `M̃` is
affine in `c05`: at `x = 4.9·10²⁶`, `∂M̃/∂c05 = 0.0769`, so the float `sup M̃` moves
`0.8201 ↦ 0.8266` (`c⁻ = −1.39`) and `0.8185 ↦ 0.8250` (`c⁻ = −1.306476`), inside `0.84`. The
CERTIFIED route of `MNP` (`g̃_P ≤ g̃_L + 1.31395·dP`) does NOT close at `0.896`: worst block
`0.84415` (`−1.306476`), `0.84580` (`−1.39`). With the increment factor sharpened to `1.1154`
(`∫_1^∞ w²e^{−w²/2} = √(π/2) − ∫_0^1`, `∫_0^1 ≥ 1/3 − 1/10 + 1/56 − 1/432`) it closes:
`0.83740` (margin `0.0026`, `c⁻ = −1.306476`) and `0.83903` (margin `0.00097`, `c⁻ = −1.39`).
(`scratchpad/erratum/cert.py`, `price.py`, `basis.py`.)
-/

namespace Principia.Common.TernaryGoldbach.MTC

open ArithmeticFunction Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MMP Principia.Common.TernaryGoldbach.MPA
  Principia.Common.TernaryGoldbach.T2SC Principia.Common.TernaryGoldbach.MPIIC

/-- **The Totals arithmetic at the erratum's factor** (`MMP.ArithAtW` with `bII ↦ bIIC`). -/
def ArithAtWC (m cL : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      bI1W Y δ q + bI2 Y δ q + bIIC Y δ q + 3 * (Real.log Y + 1) ≤ krawAt m cL Y δ q

/-- **Link [CoexistArithC]** — `MPc.CoexistArith` with the first-case constant `0.896`. -/
def CoexistArithC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) → 4 / 3 * Y ^ ((1 : ℝ) / 3) - 1 ≤ |δ| * q →
    (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) →
      krawAt 0.896 45.7575 Y δ q ≤
        0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
          1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y

/-- **Link A10 CORRECTED — the AM-GM of `minarcs.tex` 5549-5566 (book 2257-2288)**, at
`√ρ = 1.8434`: `√(C(ℓ+0.002) + (log 4 + ℓ)/2)·√(0.30214ℓ + 0.76746) ≤ (0.27125C + 0.41415)ℓ
+ 0.896` (`MT.amgm_main` at the erratum's `0.76746`: the constant is `0.8957679`). -/
theorem amgm_mainC (C l L4 : ℝ) (hC0 : 0 ≤ C) (hl : 0 ≤ l) (hC : C ≤ 0.723 + 0.0625 * l)
    (hL0 : 0 ≤ L4) (hL : L4 ≤ 1.3863) :
    Real.sqrt (C * (l + 0.002) + (L4 + l) / 2) * Real.sqrt (0.30214 * l + 0.76746) ≤
      (0.27125 * C + 0.41415) * l + 0.896 := by
  have hA0 : 0 ≤ C * (l + 0.002) + (L4 + l) / 2 :=
    add_nonneg (mul_nonneg hC0 (by linarith)) (by linarith)
  have hB0 : (0 : ℝ) ≤ 0.30214 * l + 0.76746 := by linarith
  have hsA := Real.sq_sqrt hA0
  have hsB := Real.sq_sqrt hB0
  have hkey : 2 * 1.8434 * (Real.sqrt (C * (l + 0.002) + (L4 + l) / 2) *
        Real.sqrt (0.30214 * l + 0.76746)) ≤
      C * (l + 0.002) + (L4 + l) / 2 + 1.8434 ^ 2 * (0.30214 * l + 0.76746) := by
    nlinarith [sq_nonneg (Real.sqrt (C * (l + 0.002) + (L4 + l) / 2) -
      1.8434 * Real.sqrt (0.30214 * l + 0.76746))]
  have hCl : 0 ≤ C * l := mul_nonneg hC0 hl
  nlinarith [hkey, hCl]

/-- **The main term (Link A3's first line) under the corrected A10**: at most
`(R_{x,δ₀q} log δ₀q + 0.896)/√(δ₀φ(q)) · x`. -/
theorem main_leC (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q)
    (htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3) :
    Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.76746)) ≤
      (MinSp.rR Y (OC.dz δ * q) * Real.log (OC.dz δ * q) + 0.896) /
        Real.sqrt (OC.dz δ * Nat.totient q) * Y := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  have ht2 : 2 ≤ OC.dz δ * q := by nlinarith
  have ht0 : 0 < OC.dz δ * q := by linarith
  obtain ⟨hC0, hC1⟩ := cXT_bounds Y (OC.dz δ * q) hY0 ht2 htx
  have hl : 0 ≤ Real.log (OC.dz δ * q) := Real.log_nonneg (by linarith)
  have hl4 : Real.log (4 * (OC.dz δ * q)) = Real.log 4 + Real.log (OC.dz δ * q) :=
    Real.log_mul (by norm_num) ht0.ne'
  have hR : MinSp.rR Y (OC.dz δ * q) = 0.27125 * cXT Y (OC.dz δ * q) + 0.41415 := rfl
  rw [hl4, hR]
  have key := amgm_mainC (cXT Y (OC.dz δ * q)) (Real.log (OC.dz δ * q)) (Real.log 4) hC0 hl hC1
    (Real.log_nonneg (by norm_num)) log4_le
  have hpos : 0 ≤ Y / Real.sqrt (OC.dz δ * Nat.totient q) :=
    div_nonneg hY0.le (Real.sqrt_nonneg _)
  calc _ ≤ Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        ((0.27125 * cXT Y (OC.dz δ * q) + 0.41415) * Real.log (OC.dz δ * q) + 0.896) :=
        mul_le_mul_of_nonneg_left key hpos
    _ = _ := by ring


/-- **THE ARITHMETIC with `bI1W`, PROVED at `(0.896, 45.7575)`** (generated from
`MT.arith_811`). -/
theorem arithW_896 : ArithAtWC 0.896 45.7575 := by
  intro Y hY δ q hq hdq hqy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hqy
  have hdq1 : (1 : ℝ) ≤ OC.dz δ * q := by nlinarith [dz_ge δ]
  have hs : 1 ≤ Real.sqrt (OC.dz δ * q) := Real.one_le_sqrt.mpr hdq1
  have hM := main_leC Y δ q hY0 hq htx
  have hN : 2.49157 * Y / Real.sqrt (OC.dz δ * q) ≤ 2.5 * Y / Real.sqrt (OC.dz δ * q) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hL := lterms_leW Y δ q hY0 hq
  have hE := low_le Y (Real.sqrt (OC.dz δ * q)) hY hs
  unfold bI1W bI2 bIIC krawAt
  linarith

/-- **The Totals spine with `TypeI1W`** (generated from `MT.minMain1_of_arith`). -/
theorem minMain1_of_arithWC (m cL : ℝ) (hA : ArithAtWC m cL) (h1 : TypeI1W) (h2 : TypeI2)
    (h3 : TypeIIC) : MinMain1At m cL := by
  intro Y hY α δ a q hq hg h2α hqQ hδ hqy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hsplit := vaughan_split Y α (uA Y δ q) (vA Y) hY0
  rw [s0i_eq_zero Y α (vA Y) hY0 (vA_lt Y hY), add_zero] at hsplit
  have e1 := h1 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e2 := h2 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e3 := h3 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e4 := s02_norm_le Y α (by linarith)
  have hk := hA Y hY δ q hq hdq hqy
  rw [hsplit]
  have n1 := norm_add_le (sI1 Y α (uA Y δ q) - sI2 Y α (uA Y δ q) (vA Y) +
    sII Y α (uA Y δ q) (vA Y)) (s02 Y α)
  have n2 := norm_add_le (sI1 Y α (uA Y δ q) - sI2 Y α (uA Y δ q) (vA Y))
    (sII Y α (uA Y δ q) (vA Y))
  have n3 := norm_sub_le (sI1 Y α (uA Y δ q)) (sI2 Y α (uA Y δ q) (vA Y))
  linarith


/-- **Term 1 of `eq:kraw`**, abstractly: `(R·log t + 0.896)/√(δ₀φ(q))·x ≤ A(w)·B(w)·1.73208u⁵`. -/
theorem term1_leC (R lt D Y st sF w u : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 0.3992 * w + 0.41415)
    (hlt0 : 0 ≤ lt) (hlt : lt ≤ 2 * w ^ 4 - 1) (hY : 0 < Y) (hst : 0 < st) (hsF : 0 < sF)
    (hsFle : sF ≤ 1.7312 + 0.50605 * w) (hD : st / sF ≤ D) (hYst : Y / st ≤ 1.73208 * u ^ 5) :
    (R * lt + 0.896) / D * Y ≤ ((0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.896) *
      (1.7312 + 0.50605 * w) * (1.73208 * u ^ 5) := by
  have hA0 : 0 ≤ R * lt + 0.896 := by positivity
  have hAle : R * lt + 0.896 ≤ (0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.896 := by
    have := mul_le_mul hR hlt hlt0 (by linarith)
    linarith
  have hsd : 0 < st / sF := div_pos hst hsF
  have e1 : (R * lt + 0.896) / D * Y ≤ (R * lt + 0.896) / (st / sF) * Y :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hA0 hsd hD) hY.le
  have e2 : (R * lt + 0.896) / (st / sF) * Y = (R * lt + 0.896) * sF * (Y / st) := by
    field_simp
  rw [e2] at e1
  refine e1.trans ?_
  have hY0 : 0 ≤ Y / st := div_nonneg hY.le hst.le
  have hB0 : 0 ≤ (0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.896 := le_trans hA0 hAle
  exact mul_le_mul (mul_le_mul hAle hsFle hsF.le hB0) hYst hY0
    (mul_nonneg hB0 (le_trans hsF.le hsFle))

/-- **The degree-6 polynomial inequality** in `w ≥ 1.69`. -/
theorem poly_leC (w : ℝ) (hw : 1.69 ≤ w) :
    ((0.3992 * w + 0.41415) * (2 * w ^ 4 - 1) + 0.896) * (1.7312 + 0.50605 * w) * 1.73208 +
      2.5 * 1.73208 + 3.2 + 0.01 * w ^ 6 ≤ 0.3409 * 14.694 * w ^ 6 := by
  have hq2 : 4.4 ≤ 4.29 * w ^ 2 - 3.13 * w - 2.49 := by nlinarith [sq_nonneg (w - 1.69)]
  have hw0 : 0 ≤ w := by linarith
  have hw2 : 2.85 ≤ w ^ 2 := by nlinarith
  have hw4' : 8.1 ≤ w ^ 4 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ w ^ 4)
  nlinarith [pow_nonneg hw0 5, pow_nonneg hw0 6, pow_nonneg hw0 4, pow_nonneg hw0 2]


/-- **`CoexistArithC`, PROVED.** -/
theorem coexistArithC : CoexistArithC := by
  intro Y hY δ q hq hy hdq hlow hF
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, e56, e13, eY, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hlu, hw, hw4, -⟩ := w_facts _ hu
  have hFw := bigF_le_w _ hu
  rw [e13] at hy hdq hlow hF
  obtain ⟨ht2, htx, hYst, hYt, hlogt⟩ :=
    t_facts δ q (Y ^ ((1 : ℝ) / 6)) hu hq hy hdq hlow
  have hC := cXT_le_w Y _ _ hY0 e13 hu ht2 htx
  have hC0 : 0 ≤ cXT Y (OC.dz δ * q) := (cXT_bounds Y _ hY0 ht2 (by rw [e13]; exact htx)).1
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set w := Real.sqrt (Real.sqrt (Real.log u)) with hw_def
  set t := OC.dz δ * q with ht_def
  have hwlt : Real.log t ≤ 2 * w ^ 4 - 1 := by rw [hw4]; exact hlogt
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hR : MinSp.rR Y t ≤ 0.3992 * w + 0.41415 := by
    have e : MinSp.rR Y t = 0.27125 * cXT Y t + 0.41415 := rfl
    rw [e]; linarith
  have hR0 : 0 ≤ MinSp.rR Y t := by
    have e : MinSp.rR Y t = 0.27125 * cXT Y t + 0.41415 := rfl
    rw [e]; linarith
  have hF0 : 0 < MinSp.bigF (u ^ 2 / 6) := by
    have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    exact lt_of_lt_of_le (div_pos hqR hφ0) hF
  have hqφ : (q : ℝ) / Nat.totient q ≤ 2.2421 + 2.6314 * w := hF.trans hFw
  have hd0 : 0 < OC.dz δ := by linarith [dz_ge δ]
  have hT1 := term1_leC (MinSp.rR Y t) (Real.log t) (Real.sqrt (OC.dz δ * Nat.totient q)) Y
    (Real.sqrt t) (Real.sqrt (MinSp.bigF (u ^ 2 / 6))) w u hR0 hR hlogt0 hwlt hY0
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hF0)
    (sqrtF_le _ w hF0.le hFw) (den_ge _ q _ hd0 hq hF0 hF) (by rw [eY]; exact hYst)
  obtain ⟨hLT, hLT0⟩ := ltosca_le (OC.dz δ) q w (dz_ge δ) hq hwlt hqφ
  have hT3 : 2 * Y / t * lToscaAt 45.7575 (OC.dz δ) q ≤
      2 * (3.0001 * u ^ 4) *
        ((2.2421 + 2.6314 * w) * (6.5 * w ^ 4 + 80 / 9) + 27.3032 * w ^ 4 + 45.7575) := by
    rw [mul_div_assoc]
    exact mul_le_mul (by rw [eY]; linarith) hLT hLT0 (by positivity)
  have hT2 : 2.5 * Y / Real.sqrt t ≤ 2.5 * (1.73208 * u ^ 5) := by
    rw [mul_div_assoc, eY]; linarith
  have hL : Real.log Y = 6 * w ^ 4 := by rw [eL, hw4]
  have hLp := logY_pow_ge (Real.log Y) w hL
  have hpoly := poly_leC w hw
  have hT3' := term3_le w u hw hu
  have hP : 0 ≤ u ^ 5 := by positivity
  have hpolyu := mul_le_mul_of_nonneg_left hpoly hP
  have hRHS : 0.3409 * u ^ 5 * (14.694 * w ^ 6) ≤ 0.3409 * u ^ 5 * Real.log Y ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hLp (by positivity)
  unfold krawAt
  rw [e56, e23, hL]
  rw [hL] at hRHS
  linarith [hT1, hT2, hT3, hT3', hpolyu, hRHS]

/-- **`MinMain2L` from its links, PROVED.** Dirichlet at `Q' = x^{2/3}/(500√6)`
(`Real.exists_rat_abs_sub_le_and_den_le`) gives `a'/q'`. **Case A** (`q' > y` or `|δ'|q' > 8y`):
the vaughan split at the second choice and `sec_sum_le`. **Case B** (the gap): `a'/q'` is a
first-choice approximation coexisting with `a/q`, the first case applies at it, and
`coexist_lower` + `CoexistArithC` close. -/
theorem minMain2L_ofC (h1 : SecI1At) (h2 : SecI2At) (h3 : SecIIAt)
    (hm : MinMain1At 0.896 45.7575) (h15 : GS.RS62Thm15) (hc : CoexistArithC) : MinMain2L := by
  intro Y hY α δ a q hq hg h2α hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hs6 : Real.sqrt 6 ≤ 2.5 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs60 : 0 < Real.sqrt 6 := by positivity
  -- `Q' = x^{2/3}/(500√6) ≥ 1`
  have hU2 : 0 < u2 Y := by unfold u2; positivity
  have hq2 : q2 Y = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (500 * Real.sqrt 6) := by
    unfold q2 u2
    rw [e13]
    nth_rw 1 [eY]
    field_simp
  have hq2ge : 1 ≤ q2 Y := by
    rw [hq2, le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hu 4]
  set n := ⌊q2 Y⌋₊ with hn_def
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hq2ge)
  obtain ⟨r, hr, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le (2 * α) (n_pos := hn1)
  set q' := r.den with hq'_def
  set a' := r.num with ha'_def
  have hq'1 : 1 ≤ q' := r.pos
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'1
  have hr_eq : (r : ℝ) = a' / q' := by
    rw [Rat.cast_def]
  have hg' : Int.gcd a' q' = 1 := r.reduced
  set δ' := Y * (2 * α - a' / q') with hδ'_def
  have h2' : 2 * α = a' / q' + δ' / Y := by
    rw [hδ'_def]
    field_simp
    ring
  have hnQ : (n : ℝ) ≤ q2 Y := Nat.floor_le (by linarith)
  have hQn : q2 Y < n + 1 := Nat.lt_floor_add_one _
  have hq'Q : (q' : ℝ) ≤ q2 Y := le_trans (by exact_mod_cast hrden) hnQ
  have hδ'Y : |δ' / Y| ≤ 1 / (q' * q2 Y) := by
    have e : δ' / Y = 2 * α - a' / q' := by rw [hδ'_def]; field_simp
    rw [e, ← hr_eq]
    refine hr.trans (one_div_le_one_div_of_le (by positivity) ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hQn.le (by positivity)
  by_cases hA : Y ^ ((1 : ℝ) / 3) / 6 < q' ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ'| * q'
  · -- Case A: the second choice
    have hadm : Adm2 Y α δ' a' q' := ⟨hq'1, hg', h2', hq'Q, hδ'Y, hA⟩
    have hsplit := vaughan_split Y α (u2 Y) (v2 Y) hY0
    rw [s0i_eq_zero Y α (v2 Y) hY0 (v2_lt Y hY), add_zero] at hsplit
    rw [hsplit]
    have n1 := norm_add_le (sI1 Y α (u2 Y) - sI2 Y α (u2 Y) (v2 Y) + sII Y α (u2 Y) (v2 Y))
      (s02 Y α)
    have n2 := norm_add_le (sI1 Y α (u2 Y) - sI2 Y α (u2 Y) (v2 Y)) (sII Y α (u2 Y) (v2 Y))
    have n3 := norm_sub_le (sI1 Y α (u2 Y)) (sI2 Y α (u2 Y) (v2 Y))
    have hsum := sec_sum_le Y hY _ _ _ _ (h1 Y hY α δ' a' q' hadm) (h2 Y hY α δ' a' q' hadm)
      (h3 Y hY α δ' a' q' hadm) (s02_norm_le Y α (by linarith))
    linarith
  · -- Case B: a first-choice approximation coexisting with `a/q`
    simp only [not_or, not_lt] at hA
    obtain ⟨hy', hdq'⟩ := hA
    have hqQ' : (q' : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) := by
      refine hy'.trans ?_
      rw [e13, e23]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hu 2]
    have hadm1 := adm_of_dq Y δ' q' hY0 hq'1 hdq'
    have hk := hm Y hY α δ' a' q' hq'1 hg' h2' hqQ' hadm1 hy'
    have hδq : |2 * α - a / q| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) := by
      have e : 2 * α - a / q = δ / Y := by rw [h2α]; ring
      rw [e]
      exact hδ
    have hlow := coexist_lower Y α hY a a' q q' hq hq'1 hg hQ hδq hy hy'
    have hF : (q' : ℝ) / Nat.totient q' ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) :=
      (GS.merkel_of_rs62 h15 q' hq'1 _ (y_ge Y hY) hy').le
    exact hk.trans (hc Y hY δ' q' hq'1 hy' hdq' hlow hF)


/-- **THE SPINE OF THE MAIN THEOREM AT THE ERRATUM'S CONSTANTS, PROVED (application only)**:
`MPc.minMainP_of_links` with `Vinland1AtC`, `EriksagaAtC`, `IIArithC`, `CoexistArithC`. -/
theorem minMainPC_of_links (hb1 : Bostb1At) (hgr : Grara) (hro : Ronsard) (hme : Meproz)
    (hA1 : I1Arith) (hb2 : Bosta2Eta2) (hA2 : I2Arith) (hv1 : Vinland1AtC) (her : EriksagaAtC)
    (hA3 : IIArithC) (hs1 : SecI1At) (hs2 : SecI2At) (hs3 : SecIIAt) (hco : CoexistArithC)
    (h15 : GS.RS62Thm15) : OP.MinMainP 0.896 45.7575 := by
  have t1 := MPc.typeI1W_of hb1 hgr hro hme hA1
  have t2 := typeI2_of hb2 hgr hro hA2
  have t3 := typeIIC_of hv1 her hA3 h15
  have m1 : MinMain1At 0.896 45.7575 := minMain1_of_arithWC 0.896 45.7575 arithW_896 t1 t2 t3
  exact (minMainP_iff 0.896 45.7575).2 ⟨m1, minMain2L_ofC hs1 hs2 hs3 m1 h15 hco⟩

/-- **`OP.MinMainP 0.896 45.7575` from the links still open**, the numeric links supplied
(`MPI1.i1Arith`, `iiArithC`, `coexistArithC`). Open: `Bostb1At`, `Bosta2Eta2`, `I2Arith`,
`Vinland1AtC`, `EriksagaAtC`, `SecI1At`, `SecI2At`, `SecIIAt`, `Grara`, `Ronsard`, `Meproz`,
`GS.RS62Thm15`. -/
theorem minMainPC_of_open (hb1 : Bostb1At) (hgr : Grara) (hro : Ronsard) (hme : Meproz)
    (hb2 : Bosta2Eta2) (hA2 : I2Arith) (hv1 : Vinland1AtC) (her : EriksagaAtC) (hs1 : SecI1At)
    (hs2 : SecI2At) (hs3 : SecIIAt) (h15 : GS.RS62Thm15) : OP.MinMainP 0.896 45.7575 :=
  minMainPC_of_links hb1 hgr hro hme MPI1.i1Arith hb2 hA2 hv1 her iiArithC hs1 hs2 hs3
    coexistArithC h15

end Principia.Common.TernaryGoldbach.MTC
