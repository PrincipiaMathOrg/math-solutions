/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumLEnv

set_option autoImplicit false

/-!
# THE SPINE of `OL.MNumL HW.phi 8.54 0.8095 0.6406` (the corrected-`L` `eq:bustier`)

`OL.MNumL φ p₀ c fs`: for every `x ≥ 4.9·10²⁶`, `s ∈ [0, fs log x − 0.021095]`, `p ≥ p₀`,
`g̃_L(x/49, r₀)(H̃(r₀)s − p) + (2∫_{r₀}^{r₁} g̃_L/r /(log x + 2c⁻) + coefC(x)g̃_L(r₁))s ≤ c`, with
`g̃_L = OL.gTL` on Helfgott's CORRECTED `L` (`OL.lLc`) and felipa slope `fs = 0.6406`.

* **Affine reduction** (`mnumL_of_felipa`, DISCHARGED): affine in `p` (slope `−g̃_L(y, r₀) ≤ 0`)
  and in `s`, so it suffices at `s = 0.6406 log x − 0.021095`, `p = p₀`, given `GTNonnegL`.
* **The `x`-side at slope `0.6406`** (DISCHARGED, section (3)): `hsL`, `casL` DECREASE in `x`,
  `cfL` INCREASES; each is bounded from a certified `log x` at the block's end (`MC.lgs…`, reused
  by import: the partition points are a subset of `MC.mnumC_of_links`'s).
* **The links** are named `Prop`s about `g̃_L` alone: `GTNonnegL`, `G0EnvL`, `T1BlkL`, `IGBlkL`,
  and for `x ≥ 4.9·10²⁸` `T1FarL` (with `cfL` inside) and `IGFarL`.
* **The composition** (`mnumL_of_links`): the `y`-blocks
  `[10²⁵, 1.3·10²⁵, 1.84·10²⁵, 3.65·10²⁵, 10²⁶, 10²⁷]` and the far regime, each closed by
  `MN.blk` (`G(H − 8.54) + cf·T + k·I ≤ 0.8095`); the certified values leave margins
  0.010013, 0.013293, 0.013408, 0.020258, 0.026831, 0.032177.

Every link is DISCHARGED in `MNumLProofs.lean` (`mnumL_proved`) from the corrected-`L` region
envelopes of `MNumLEnv.lean`, which are `MC`'s envelopes of the printed `g̃` (reused by import) with
the correction `gTL ≤ gT + 1.31395(0.568095 + 4.762712 log r)/r` (`ML.gTL_le`) absorbed into `Q`.
-/

namespace Principia.Common.TernaryGoldbach.ML

open MinSp MeasureTheory Set MC

/-! ## (1) The `x`-side coefficients at `s = felipa(x)`, felipa slope `0.6406` -/

/-- **`felipa` at slope `0.6406`**: `0.6406 log x − 0.021095`, the `S/x` bound of
`OL.FelipaAt 0.6406`. -/
noncomputable def felL (x : ℝ) : ℝ := 0.6406 * Real.log x - 0.021095

/-- **`H̃(r₀)·felipa(x)`** at slope `0.6406`. -/
noncomputable def hsL (x : ℝ) : ℝ := OC.hR0C x * felL x

/-- **`2 felipa(x)/(log x + 2c⁻)`** at slope `0.6406`, `c⁻ = −1.306476`. -/
noncomputable def casL (x : ℝ) : ℝ := 2 / (Real.log x - 2 * 1.306476) * felL x

/-- **`coefC(x)·felipa(x)`** at slope `0.6406`. -/
noncomputable def cfL (x : ℝ) : ℝ := OC.coefC x * felL x

/-! ## (2) THE LINKS — named hypotheses about the corrected `g̃` (all discharged in
`MNumLProofs`) -/

/-- **Link [g̃_L ≥ 0]**: `g̃_L(y, r₀) ≥ 0` for `y ≥ 10²⁵`. -/
def GTNonnegL : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → 0 ≤ OL.gTL HW.phi y 150000

/-- **Link [g̃_L(r₀)]**: `g̃_L(y, r₀) ≤ G` for `y ≥ 10²⁵`. -/
def G0EnvL (G : ℝ) : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → OL.gTL HW.phi y 150000 ≤ G

/-- **Link [g̃_L(r₁)] on a block**: `g̃_L(y, r₁(y)) ≤ T` for `y ∈ [y_a, y_b]`. -/
def T1BlkL (ya yb T : ℝ) : Prop :=
  ∀ y : ℝ, ya ≤ y → y ≤ yb → OL.gTL HW.phi y (r1y y) ≤ T

/-- **Link [∫g̃_L/r] on a block**: `∫_{r₀}^{r₁(y)} g̃_L(y, r)/r dr ≤ I` for `y ∈ [y_a, y_b]`. -/
def IGBlkL (ya yb I : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → OL.intGTL HW.phi y ≤ I

/-- **Link [far g̃_L(r₁)]**: `cfL(x)·g̃_L(x/49, r₁(x/49)) ≤ T` for `x ≥ 4.9·10²⁸`. -/
def T1FarL (T : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 27 ≤ x → cfL x * OL.gTL HW.phi (x / 49) (r1y (x / 49)) ≤ T

/-- **Link [far ∫g̃_L/r]**: `∫_{r₀}^{r₁(y)} g̃_L/r ≤ I` for `y ≥ 10²⁷`. -/
def IGFarL (I : ℝ) : Prop := ∀ y : ℝ, 10 ^ 27 ≤ y → OL.intGTL HW.phi y ≤ I

/-! ## (3) DISCHARGED: the `x`-side at slope `0.6406` -/

/-- **`hsL` in closed form**: `(log 150001 + 2.05315)(0.6406L − 0.021095)/(L/2 − 1.306476)`. -/
theorem hsL_eq (x : ℝ) (hx : 0 ≤ x) :
    hsL x = (Real.log 150001 + 2.05315) *
      ((0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476)) := by
  unfold hsL OC.hR0C felL
  rw [Real.log_sqrt hx]
  ring

/-- **`hsL` decreases**: `hsL(x) ≤ 13.97156·f(L₀)` once `61 ≤ L₀ ≤ log x`. -/
theorem hsL_le_of (x Llo : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hL : Llo ≤ Real.log x) (h61 : 61 ≤ Llo) :
    hsL x ≤ 13.97156 * ((0.6406 * Llo - 0.021095) / (Llo / 2 - 1.306476)) := by
  have hx0 := x_pos x hx
  have hN := MN.log_150001_le
  have hf : (0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476) ≤
      (0.6406 * Llo - 0.021095) / (Llo / 2 - 1.306476) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hf0 : 0 ≤ (0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476) :=
    div_nonneg (by linarith) (by linarith)
  rw [hsL_eq x hx0.le]
  exact mul_le_mul (by linarith) hf hf0 (by norm_num)

/-- **`hsL ≥ 8.54`** on `x ≥ 4.9·10²⁶` (it is `≥ 17.7`). -/
theorem hsL_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 8.54 ≤ hsL x := by
  have hx0 := x_pos x hx
  have hL := LW.log_ge_of x hx
  have hN0 := MN.log_150001_ge
  have hf : 1.28 ≤ (0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [hsL_eq x hx0.le]
  calc (8.54 : ℝ) ≤ 13.83665 * 1.28 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith) hf (by norm_num) (by linarith)

/-- **`casL` in closed form**. -/
theorem casL_eq (x : ℝ) :
    casL x = 2 * (0.6406 * Real.log x - 0.021095) / (Real.log x - 2 * 1.306476) := by
  unfold casL felL
  ring

/-- **`casL` decreases**: `casL(x) ≤ 2(0.6406L₀ − 0.021095)/(L₀ − 2.612952)`. -/
theorem casL_le_of (x Llo : ℝ) (hL : Llo ≤ Real.log x) (h61 : 61 ≤ Llo) :
    casL x ≤ 2 * (0.6406 * Llo - 0.021095) / (Llo - 2 * 1.306476) := by
  rw [casL_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `casL ≥ 0`. -/
theorem casL_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ casL x := by
  have hL := LW.log_ge_of x hx
  rw [casL_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **`cfL` increases**: `cfL(x) ≤ (7/15 + d̄/(L₁ − 2.612952))(0.6406L₁ − 0.021095)` for
`log x ≤ L₁`, `d̄ = −3.538215 + (8/15)·3.891821` (`MC.coefC_bounds`, `MC.log49_le`). -/
theorem cfL_le_of (x Lhi : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hU : Real.log x ≤ Lhi) :
    cfL x ≤ (7 / 15 + (-3.538215 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.306476)) *
      (0.6406 * Lhi - 0.021095) := by
  have hL := LW.log_ge_of x hx
  have h49 := log49_le
  have hD : 0 < Real.log x - 2 * 1.306476 := by linarith
  obtain ⟨hc0, -⟩ := coefC_bounds x hx
  have hc : OC.coefC x ≤ 7 / 15 + (-3.538215 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.306476) := by
    unfold OC.coefC
    have a1 : (-3.538215 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.306476) ≤
        (-3.538215 + 8 / 15 * 3.891821) / (Real.log x - 2 * 1.306476) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    have a2 : (-3.538215 + 8 / 15 * 3.891821) / (Real.log x - 2 * 1.306476) ≤
        (-3.538215 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.306476) := by
      rw [div_le_div_iff₀ hD (by linarith)]
      nlinarith
    linarith
  have hf : felL x ≤ 0.6406 * Lhi - 0.021095 := by
    unfold felL
    linarith
  have hf0 : 0 ≤ felL x := by
    unfold felL
    linarith
  unfold cfL
  exact mul_le_mul hc hf hf0 (hc0.trans hc)

/-- `cfL ≥ 0`. -/
theorem cfL_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ cfL x := by
  have hL := LW.log_ge_of x hx
  have hf0 : 0 ≤ felL x := by
    unfold felL
    linarith
  unfold cfL
  exact mul_nonneg (coefC_bounds x hx).1 hf0

/-! ## (4) DISCHARGED: the affine reduction -/

/-- **The affine reduction**: `OL.MNumL HW.phi p₀ c 0.6406` from `g̃_L(r₀) ≥ 0`, `p₀, c ≥ 0` and
the bound at `s = felipa(x)`, `p = p₀` (`MN.affine_step`). -/
theorem mnumL_of_felipa (p0 c : ℝ) (hp0 : 0 ≤ p0) (hc : 0 ≤ c) (hg : GTNonnegL)
    (hM : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      OL.gTL HW.phi (x / 49) 150000 * (hsL x - p0) +
        cfL x * OL.gTL HW.phi (x / 49) (r1y (x / 49)) + casL x * OL.intGTL HW.phi (x / 49) ≤
          c) :
    OL.MNumL HW.phi p0 c 0.6406 := by
  intro x hx s p hs0 hs1 hp
  refine MN.affine_step _ _ _ _ s p p0 c (hg (x / 49) (y_ge x hx)) hp0 hs0 hs1 hp hc ?_
  have e : OL.gTL HW.phi (x / 49) 150000 * (hsL x - p0) +
        cfL x * OL.gTL HW.phi (x / 49) (r1y (x / 49)) + casL x * OL.intGTL HW.phi (x / 49) =
      OL.gTL HW.phi (x / 49) 150000 * (OC.hR0C x * (0.6406 * Real.log x - 0.021095) - p0) +
        (2 / (Real.log x - 2 * 1.306476) * OL.intGTL HW.phi (x / 49) +
          OC.coefC x * OL.gTL HW.phi (x / 49) (r1y (x / 49))) *
          (0.6406 * Real.log x - 0.021095) := by
    unfold hsL cfL casL felL
    ring
  rw [← e]
  exact hM x hx

/-! ## (5) THE COMPOSITION (the partition logarithms are `MC.lgs…`) -/

/-- **THE SPINE of `OL.MNumL HW.phi 8.54 0.8095 0.6406`**: the links on the five `y`-blocks and the
    far regime, closed by `MN.blk`. Application and arithmetic only. -/
theorem mnumL_of_links (g0 : GTNonnegL) (e0 : G0EnvL 0.0427913) (t0 : T1BlkL (10 ^ 25) (13 *
    10 ^ 24) 0.0157963) (t1 : T1BlkL (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0154199) (t2 : T1BlkL (184 *
    10 ^ 23) (365 * 10 ^ 23) 0.0150526) (t3 : T1BlkL (365 * 10 ^ 23) (10 ^ 26) 0.0141869)
    (t4 : T1BlkL (10 ^ 26) (10 ^ 27) 0.0128839) (i0 : IGBlkL (10 ^ 25) (13 * 10 ^ 24) 0.0669295)
    (i1 : IGBlkL (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0683159) (i2 : IGBlkL (184 * 10 ^ 23) (365 *
    10 ^ 23) 0.0709086) (i3 : IGBlkL (365 * 10 ^ 23) (10 ^ 26) 0.0744075)
    (i4 : IGBlkL (10 ^ 26) (10 ^ 27) 0.0809224) (tf : T1FarL 0.206372) (ifr : IGFarL 0.104449) :
    OL.MNumL HW.phi 8.54 0.8095 0.6406 := by
  refine mnumL_of_felipa 8.54 0.8095 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hx0 := x_pos x hx
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hg := e0 (x / 49) (y_ge x hx)
  have hh0 := hsL_ge x hx
  have hca0 := casL_nonneg x hx
  have hcf0 := cfL_nonneg x hx
  rcases le_or_gt x 637000000000000000000000000 with hb0 | hb0
  · have hlo : (490000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hx
    have hL : 61.4564475 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL1.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 61.718812 :=
      ((Real.log_le_log hx0 hb0).trans lgsU4).trans (by norm_num)
    have hya : (10 ^ 25) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (13 * 10 ^ 24) := MN.y_le_of x _ (le_trans hb0 (by norm_num))
    exact MN.blk 8.54 0.8095 0.0427913 18.68522 (17.46297 * 0.0157963) 1.337375 0.0669295 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t0 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i0 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 901600000000000000000000000 with hb1 | hb1
  · have hlo : (637000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb0.le
    have hL : 61.7188118 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL5.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.0662133 :=
      ((Real.log_le_log hx0 hb1).trans lgsU6).trans (by norm_num)
    have hya : (13 * 10 ^ 24) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (184 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb1 (by norm_num))
    exact MN.blk 8.54 0.8095 0.0427913 18.68173 (17.56706 * 0.0154199) 1.337126 0.0683159 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t1 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i1 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 1788500000000000000000000000 with hb2 | hb2
  · have hlo : (901600000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb1.le
    have hL : 62.0662131 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL7.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.7511749 :=
      ((Real.log_le_log hx0 hb2).trans lgsU8).trans (by norm_num)
    have hya : (184 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (365 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb2 (by norm_num))
    exact MN.blk 8.54 0.8095 0.0427913 18.67717 (17.77229 * 0.0150526) 1.336799 0.0709086 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t2 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i2 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 4900000000000000000000000000 with hb3 | hb3
  · have hlo : (1788500000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb2.le
    have hL : 62.7511747 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL9.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 63.7590328 :=
      ((Real.log_le_log hx0 hb3).trans lgsU10).trans (by norm_num)
    have hya : (365 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 26) := MN.y_le_of x _ (le_trans hb3 (by norm_num))
    exact MN.blk 8.54 0.8095 0.0427913 18.66832 (18.07425 * 0.0141869) 1.336166 0.0744075 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t3 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i3 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 49000000000000000000000000000 with hb4 | hb4
  · have hlo : (4900000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb3.le
    have hL : 63.7590326 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL11.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 66.0616179 :=
      ((Real.log_le_log hx0 hb4).trans lgsU12).trans (by norm_num)
    have hya : (10 ^ 26) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 27) := MN.y_le_of x _ (le_trans hb4 (by norm_num))
    exact MN.blk 8.54 0.8095 0.0427913 18.65566 (18.76404 * 0.0128839) 1.33526 0.0809224 _ _ _ _ _
        hg0 hg hh0
      ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfL_le_of x _ hx hU).trans (by norm_num))
        (t4 _ hya hyb) (by norm_num))
      hca0 ((casL_le_of x _ hL (by norm_num)).trans (by norm_num)) (i4 _ hya hyb)
      (by norm_num) (by norm_num)
  have hlo : (49000000000000000000000000000 : ℝ) ≤ x := hb4.le
  have hL : 66.0616177 ≤ Real.log x :=
    le_trans (by norm_num) (lgsL13.trans (Real.log_le_log (by norm_num) hlo))
  exact MN.blk 8.54 0.8095 0.0427913 18.62825 0.206372 1.333298 0.104449 _ _ _ _ _ hg0 hg hh0
    ((hsL_le_of x _ hx hL (by norm_num)).trans (by norm_num))
    (tf x (le_trans (by norm_num) hlo)) hca0
    ((casL_le_of x _ hL (by norm_num)).trans (by norm_num))
    (ifr _ (MN.y_ge_of x _ (le_trans (by norm_num) hlo))) (by norm_num) (by norm_num)

end Principia.Common.TernaryGoldbach.ML
