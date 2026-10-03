/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopC
import Principia.Common.TernaryGoldbach.MNumProofs

set_option autoImplicit false

/-!
# THE SPINE of `OC.MNumC HW.phi 8.54 0.791` (the corrected `eq:bustier`)

`OC.MNumC φ p₀ c`: for every `x ≥ 4.9·10²⁶`, `s ∈ [0, felipa(x)]`, `p ≥ p₀`,
`g̃(x/49, r₀)(H̃(r₀)s − p) + (2∫_{r₀}^{r₁} g̃/r /(log x + 2c⁻) + coefC(x)g̃(r₁))s ≤ c`.

* **Affine reduction** (`mnumC_of_felipa`, DISCHARGED): the bound is affine in `p` (slope
  `−g̃(y, r₀) ≤ 0`) and in `s`, so it suffices at `s = felipa(x)`, `p = p₀`, given `GTNonneg`.
* **The `x`-side at `s = felipa(x)`** (DISCHARGED): `hsC = H̃·felipa` and
  `casC = 2felipa/(log x + 2c⁻)` DECREASE in `x` (`c⁻ = −1.306476 < 0`), `cfC = coefC·felipa`
  INCREASES; each is bounded from a certified `log x` at the block's end (`hsC_le_of`,
  `casC_le_of`, `cfC_le_of`).
* **The links** are named `Prop`s about `g̃` alone: `GTNonneg`, `G0Env G` (`g̃(y, r₀) ≤ G`),
  `T1Blk y_a y_b T` (`g̃(y, r₁(y)) ≤ T`), `IGBlk y_a y_b I` (`∫_{r₀}^{r₁(y)} g̃/r ≤ I`), and for
  `x ≥ 4.9·10²⁸` `T1Far T` (with `cfC` inside) and `IGFar I`.
* **The composition** (`mnumC_of_links`): the `y`-blocks
  `[10²⁵, 1.09·10²⁵, 1.3·10²⁵, 1.84·10²⁵, 3.65·10²⁵, 10²⁶, 10²⁷]` and the far regime, each closed by
  `MN.blk` (`G(H − 8.54) + cf·T + k·I ≤ 0.791`); the certified values leave margins
  0.002348, 0.002173, 0.002116, 0.002180, 0.008923, 0.015383, 0.020394.

Every link is DISCHARGED in `MNumCProofs.lean` (`mnumC_proved`), from the region envelopes
`MNumCR0Hi` … `MNumCRFHi` (the analysis is in `MNumCEnv`, the certified data in `MNumCData`).
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set


/-! ## (1) The `x`-side coefficients at `s = felipa(x)` -/

/-- **`H̃(r₀)·felipa(x)`**: the coefficient of `g̃(r₀)` at `s = felipa(x)`. -/
noncomputable def hsC (x : ℝ) : ℝ := OC.hR0C x * MN.fel x

/-- **`2 felipa(x)/(log x + 2c⁻)`**, `c⁻ = −1.306476`. -/
noncomputable def casC (x : ℝ) : ℝ := 2 / (Real.log x - 2 * 1.306476) * MN.fel x

/-- **`coefC(x)·felipa(x)`**: the coefficient of `g̃(r₁)` at `s = felipa(x)`. -/
noncomputable def cfC (x : ℝ) : ℝ := OC.coefC x * MN.fel x

/-! ## (2) THE LINKS — named hypotheses about `g̃` (all discharged in `MNumCProofs`) -/

/-- **Link [g̃ ≥ 0]**: `g̃(y, r₀) ≥ 0` for `y ≥ 10²⁵`. -/
def GTNonneg : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → 0 ≤ OC.gT HW.phi y 150000

/-- **Link [g̃(r₀)]**: `g̃(y, r₀) ≤ G` for `y ≥ 10²⁵`. -/
def G0Env (G : ℝ) : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → OC.gT HW.phi y 150000 ≤ G

/-- **Link [g̃(r₁)] on a block**: `g̃(y, r₁(y)) ≤ T` for `y ∈ [y_a, y_b]`. -/
def T1Blk (ya yb T : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → OC.gT HW.phi y (r1y y) ≤ T

/-- **Link [∫g̃/r] on a block**: `∫_{r₀}^{r₁(y)} g̃(y, r)/r dr ≤ I` for `y ∈ [y_a, y_b]`. -/
def IGBlk (ya yb I : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → OC.intGT HW.phi y ≤ I

/-- **Link [far g̃(r₁)]**: `cfC(x)·g̃(x/49, r₁(x/49)) ≤ T` for `x ≥ 4.9·10²⁸`. -/
def T1Far (T : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 27 ≤ x → cfC x * OC.gT HW.phi (x / 49) (r1y (x / 49)) ≤ T

/-- **Link [far ∫g̃/r]**: `∫_{r₀}^{r₁(y)} g̃/r ≤ I` for `y ≥ 10²⁷`. -/
def IGFar (I : ℝ) : Prop := ∀ y : ℝ, 10 ^ 27 ≤ y → OC.intGT HW.phi y ≤ I

/-! ## (3) DISCHARGED: the `x`-side -/

/-- `log 49 ≤ 3.891821` (truth `3.8918203`): `49 = 2⁶(1 − 15/64)`. -/
theorem log49_le : Real.log 49 ≤ 3.891821 := by
  have h := MN.log_le_series 49 (15 / 64) 6 20 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **`hsC` in closed form**: `(log 150001 + 2.05315)(0.640209L − 0.021095)/(L/2 − 1.306476)`. -/
theorem hsC_eq (x : ℝ) (hx : 0 ≤ x) :
    hsC x = (Real.log 150001 + 2.05315) *
      ((0.640209 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476)) := by
  unfold hsC OC.hR0C MN.fel
  rw [Real.log_sqrt hx]
  ring

/-- **`hsC` decreases**: `hsC(x) ≤ 13.97156·f(L₀)` once `61 ≤ L₀ ≤ log x`. -/
theorem hsC_le_of (x Llo : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hL : Llo ≤ Real.log x) (h61 : 61 ≤ Llo) :
    hsC x ≤ 13.97156 * ((0.640209 * Llo - 0.021095) / (Llo / 2 - 1.306476)) := by
  have hx0 := x_pos x hx
  have hN := MN.log_150001_le
  have hf : (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476) ≤
      (0.640209 * Llo - 0.021095) / (Llo / 2 - 1.306476) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hf0 : 0 ≤ (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476) :=
    div_nonneg (by linarith) (by linarith)
  rw [hsC_eq x hx0.le]
  exact mul_le_mul (by linarith) hf hf0 (by norm_num)

/-- **`hsC ≥ 8.54`** on `x ≥ 4.9·10²⁶` (it is `≥ 17.7`). -/
theorem hsC_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 8.54 ≤ hsC x := by
  have hx0 := x_pos x hx
  have hL := LW.log_ge_of x hx
  have hN0 := MN.log_150001_ge
  have hf : 1.28 ≤ (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 - 1.306476) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [hsC_eq x hx0.le]
  calc (8.54 : ℝ) ≤ 13.83665 * 1.28 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith) hf (by norm_num) (by linarith)

/-- **`casC` in closed form**. -/
theorem casC_eq (x : ℝ) :
    casC x = 2 * (0.640209 * Real.log x - 0.021095) / (Real.log x - 2 * 1.306476) := by
  unfold casC MN.fel
  ring

/-- **`casC` decreases**: `casC(x) ≤ 2(0.640209L₀ − 0.021095)/(L₀ − 2.612952)`. -/
theorem casC_le_of (x Llo : ℝ) (hL : Llo ≤ Real.log x) (h61 : 61 ≤ Llo) :
    casC x ≤ 2 * (0.640209 * Llo - 0.021095) / (Llo - 2 * 1.306476) := by
  rw [casC_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `casC ≥ 0`. -/
theorem casC_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ casC x := by
  have hL := LW.log_ge_of x hx
  rw [casC_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **`0 ≤ coefC ≤ 7/15`** on `x ≥ 4.9·10²⁶` (`−3.538215 + (8/15)log 49 < 0`). -/
theorem coefC_bounds (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 ≤ OC.coefC x ∧ OC.coefC x ≤ 7 / 15 := by
  have hL := LW.log_ge_of x hx
  have h49 := log49_le
  have h49' : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  have hD : 0 < Real.log x - 2 * 1.306476 := by linarith
  unfold OC.coefC
  constructor
  · have a1 : -3.538215 / (Real.log x - 2 * 1.306476) ≤
        (-3.538215 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.306476) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    have a2 : -1 / 15 ≤ -3.538215 / (Real.log x - 2 * 1.306476) := by
      rw [le_div_iff₀ hD]
      linarith
    linarith
  · have a1 : (-3.538215 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.306476) ≤ 0 := by
      rw [div_le_iff₀ hD]
      linarith
    linarith

/-- **`cfC` increases**: `cfC(x) ≤ (7/15 + d̄/(L₁ − 2.612952))(0.640209L₁ − 0.021095)` for
`log x ≤ L₁`, `d̄ = −3.538215 + (8/15)·3.891821 ≥ −3.538215 + (8/15)log 49`. -/
theorem cfC_le_of (x Lhi : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hU : Real.log x ≤ Lhi) :
    cfC x ≤ (7 / 15 + (-3.538215 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.306476)) *
      (0.640209 * Lhi - 0.021095) := by
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
  have hf : MN.fel x ≤ 0.640209 * Lhi - 0.021095 := by
    unfold MN.fel
    linarith
  have hf0 : 0 ≤ MN.fel x := by
    unfold MN.fel
    linarith
  unfold cfC
  exact mul_le_mul hc hf hf0 (hc0.trans hc)

/-- `cfC ≥ 0`. -/
theorem cfC_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ cfC x := by
  have hL := LW.log_ge_of x hx
  have hf0 : 0 ≤ MN.fel x := by
    unfold MN.fel
    linarith
  unfold cfC
  exact mul_nonneg (coefC_bounds x hx).1 hf0

/-- `a·g ≤ A·T` from `0 ≤ a ≤ A`, `g ≤ T`, `T ≥ 0`. -/
theorem mul_le_of (a A g T : ℝ) (ha : 0 ≤ a) (hA : a ≤ A) (hg : g ≤ T) (hT : 0 ≤ T) :
    a * g ≤ A * T :=
  (mul_le_mul_of_nonneg_left hg ha).trans (mul_le_mul_of_nonneg_right hA hT)

/-! ## (4) DISCHARGED: the affine reduction -/

/-- **The affine reduction**: `MNumC p₀ c` from `g̃(r₀) ≥ 0`, `p₀, c ≥ 0` and the bound at
`s = felipa(x)`, `p = p₀` (`MN.affine_step`). -/
theorem mnumC_of_felipa (p0 c : ℝ) (hp0 : 0 ≤ p0) (hc : 0 ≤ c) (hg : GTNonneg)
    (hM : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      OC.gT HW.phi (x / 49) 150000 * (hsC x - p0) +
        cfC x * OC.gT HW.phi (x / 49) (r1y (x / 49)) + casC x * OC.intGT HW.phi (x / 49) ≤ c) :
    OC.MNumC HW.phi p0 c := by
  intro x hx s p hs0 hs1 hp
  refine MN.affine_step _ _ _ _ s p p0 c (hg (x / 49) (y_ge x hx)) hp0 hs0 hs1 hp hc ?_
  have e : OC.gT HW.phi (x / 49) 150000 * (hsC x - p0) +
        cfC x * OC.gT HW.phi (x / 49) (r1y (x / 49)) + casC x * OC.intGT HW.phi (x / 49) =
      OC.gT HW.phi (x / 49) 150000 * (OC.hR0C x * (0.640209 * Real.log x - 0.021095) - p0) +
        (2 / (Real.log x - 2 * 1.306476) * OC.intGT HW.phi (x / 49) +
          OC.coefC x * OC.gT HW.phi (x / 49) (r1y (x / 49))) *
          (0.640209 * Real.log x - 0.021095) := by
    unfold hsC cfC casC MN.fel
    ring
  rw [← e]
  exact hM x hx

/-! ## (5) The partition logarithms (DISCHARGED) -/

theorem lgsL1 : 61.4564475998 ≤ Real.log 490000000000000000000000000 := by
  have h := MN.le_log_series 490000000000000000000000000 ((208362304392610233033222 * 10 ^ 40 +
      1501674183627983438782393932342529296875) / 10 ^ 64) 89 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsU2 : Real.log 534100000000000000000000000 ≤ 61.5426253406 := by
  have h := MN.log_le_series 534100000000000000000000000 ((13711491178794515400621214 * 10 ^ 40 +
      3682486015450194827280938625335693359375) / 10 ^ 66) 89 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsL3 : 61.542625296 ≤ Real.log 534100000000000000000000000 := by
  have h := MN.le_log_series 534100000000000000000000000 ((13711491178794515400621214 * 10 ^ 40 +
      3682486015450194827280938625335693359375) / 10 ^ 66) 89 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsU4 : Real.log 637000000000000000000000000 ≤ 61.7188119088 := by
  have h := MN.log_le_series 637000000000000000000000000 (-((291290042896066970568112 * 10 ^ 40 +
      478235612836215295828878879547119140625) / 10 ^ 65)) 89 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsL5 : 61.7188118642 ≤ Real.log 637000000000000000000000000 := by
  have h := MN.le_log_series 637000000000000000000000000 (-((291290042896066970568112 * 10 ^ 40 +
      478235612836215295828878879547119140625) / 10 ^ 65)) 89 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsU6 : Real.log 901600000000000000000000000 ≤ 62.0662132162 := by
  have h := MN.log_le_series 901600000000000000000000000 ((271693320041201414390564 * 10 ^ 40 +
      3781540248937744763679802417755126953125) / 10 ^ 64) 90 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsL7 : 62.0662131711 ≤ Real.log 901600000000000000000000000 := by
  have h := MN.le_log_series 901600000000000000000000000 ((271693320041201414390564 * 10 ^ 40 +
      3781540248937744763679802417755126953125) / 10 ^ 64) 90 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsU8 : Real.log 1788500000000000000000000000 ≤ 62.7511748125 := by
  have h := MN.log_le_series 1788500000000000000000000000 ((2776306027582568376428152120 * 10 ^ 40 +
      2776925605348878889344632625579833984375) / 10 ^ 68) 91 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsL9 : 62.7511747669 ≤ Real.log 1788500000000000000000000000 := by
  have h := MN.le_log_series 1788500000000000000000000000 ((2776306027582568376428152120 * 10 ^ 40 +
      2776925605348878889344632625579833984375) / 10 ^ 68) 91 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsU10 : Real.log 4900000000000000000000000000 ≤ 63.7590327381 := by
  have h := MN.log_le_series 4900000000000000000000000000 ((1045288049076279129152768 * 10 ^ 40 +
      7709272953497929847799241542816162109375) / 10 ^ 66) 92 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsL11 : 63.759032692 ≤ Real.log 4900000000000000000000000000 := by
  have h := MN.le_log_series 4900000000000000000000000000 ((1045288049076279129152768 * 10 ^ 40 +
      7709272953497929847799241542816162109375) / 10 ^ 66) 92 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsU12 : Real.log 49000000000000000000000000000 ≤ 66.0616178318 := by
  have h := MN.log_le_series 49000000000000000000000000000 (-((2369338993865465108855903903 *
      10 ^ 40 + 6340880812758769025094807147979736328125) / 10 ^ 68)) 95 61 (by norm_num)
      (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgsL13 : 66.0616177842 ≤ Real.log 49000000000000000000000000000 := by
  have h := MN.le_log_series 49000000000000000000000000000 (-((2369338993865465108855903903 *
      10 ^ 40 + 6340880812758769025094807147979736328125) / 10 ^ 68)) 95 61 (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-! ## (6) THE COMPOSITION -/

/-- **THE SPINE of `OC.MNumC HW.phi 8.54 0.791`**: the links on the six `y`-blocks and the far
    regime, closed by `MN.blk`. Application and arithmetic only. -/
theorem mnumC_of_links (g0 : GTNonneg) (e0 : G0Env 0.0422891) (t0 : T1Blk (10 ^ 25) (109 *
    10 ^ 23) 0.0156479) (t1 : T1Blk (109 * 10 ^ 23) (13 * 10 ^ 24) 0.0155586) (t2 : T1Blk (13 *
    10 ^ 24) (184 * 10 ^ 23) 0.0153707) (t3 : T1Blk (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0150073)
    (t4 : T1Blk (365 * 10 ^ 23) (10 ^ 26) 0.0141484) (t5 : T1Blk (10 ^ 26) (10 ^ 27) 0.0128533)
    (i0 : IGBlk (10 ^ 25) (109 * 10 ^ 23) 0.0657177) (i1 : IGBlk (109 * 10 ^ 23) (13 *
    10 ^ 24) 0.0664377) (i2 : IGBlk (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0678198) (i3 : IGBlk (184 *
    10 ^ 23) (365 * 10 ^ 23) 0.070405) (i4 : IGBlk (365 * 10 ^ 23) (10 ^ 26) 0.0738949)
    (i5 : IGBlk (10 ^ 26) (10 ^ 27) 0.0803961) (tf : T1Far 0.206012) (ifr : IGFar 0.103905) :
    OC.MNumC HW.phi 8.54 0.791 := by
  refine mnumC_of_felipa 8.54 0.791 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hx0 := x_pos x hx
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hg := e0 (x / 49) (y_ge x hx)
  have hh0 := hsC_ge x hx
  have hca0 := casC_nonneg x hx
  have hcf0 := cfC_nonneg x hx
  rcases le_or_gt x 534100000000000000000000000 with hb0 | hb0
  · have hlo : (490000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hx
    have hL : 61.4564475 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL1.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 61.5426254 :=
      ((Real.log_le_log hx0 hb0).trans lgsU2).trans (by norm_num)
    have hya : (10 ^ 25) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (109 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb0 (by norm_num))
    exact MN.blk 8.54 0.791 0.0422891 18.67381 (17.39954 * 0.0156479) 1.336559 0.0657177 _ _ _ _ _
        hg0 hg hh0
      ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfC_le_of x _ hx hU).trans (by norm_num))
        (t0 _ hya hyb) (by norm_num))
      hca0 ((casC_le_of x _ hL (by norm_num)).trans (by norm_num)) (i0 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 637000000000000000000000000 with hb1 | hb1
  · have hlo : (534100000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb0.le
    have hL : 61.5426252 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL3.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 61.718812 :=
      ((Real.log_le_log hx0 hb1).trans lgsU4).trans (by norm_num)
    have hya : (109 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (13 * 10 ^ 24) := MN.y_le_of x _ (le_trans hb1 (by norm_num))
    exact MN.blk 8.54 0.791 0.0422891 18.67266 (17.4523 * 0.0155586) 1.336477 0.0664377 _ _ _ _ _
        hg0 hg hh0
      ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfC_le_of x _ hx hU).trans (by norm_num))
        (t1 _ hya hyb) (by norm_num))
      hca0 ((casC_le_of x _ hL (by norm_num)).trans (by norm_num)) (i1 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 901600000000000000000000000 with hb2 | hb2
  · have hlo : (637000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb1.le
    have hL : 61.7188118 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL5.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.0662133 :=
      ((Real.log_le_log hx0 hb2).trans lgsU6).trans (by norm_num)
    have hya : (13 * 10 ^ 24) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (184 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb2 (by norm_num))
    exact MN.blk 8.54 0.791 0.0422891 18.67033 (17.55633 * 0.0153707) 1.336309 0.0678198 _ _ _ _ _
        hg0 hg hh0
      ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfC_le_of x _ hx hU).trans (by norm_num))
        (t2 _ hya hyb) (by norm_num))
      hca0 ((casC_le_of x _ hL (by norm_num)).trans (by norm_num)) (i2 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 1788500000000000000000000000 with hb3 | hb3
  · have hlo : (901600000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb2.le
    have hL : 62.0662131 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL7.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.7511749 :=
      ((Real.log_le_log hx0 hb3).trans lgsU8).trans (by norm_num)
    have hya : (184 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (365 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb3 (by norm_num))
    exact MN.blk 8.54 0.791 0.0422891 18.66576 (17.76144 * 0.0150073) 1.335983 0.070405 _ _ _ _ _
        hg0 hg hh0
      ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfC_le_of x _ hx hU).trans (by norm_num))
        (t3 _ hya hyb) (by norm_num))
      hca0 ((casC_le_of x _ hL (by norm_num)).trans (by norm_num)) (i3 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 4900000000000000000000000000 with hb4 | hb4
  · have hlo : (1788500000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb3.le
    have hL : 62.7511747 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL9.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 63.7590328 :=
      ((Real.log_le_log hx0 hb4).trans lgsU10).trans (by norm_num)
    have hya : (365 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 26) := MN.y_le_of x _ (le_trans hb4 (by norm_num))
    exact MN.blk 8.54 0.791 0.0422891 18.65692 (18.06321 * 0.0141484) 1.33535 0.0738949 _ _ _ _ _
        hg0 hg hh0
      ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfC_le_of x _ hx hU).trans (by norm_num))
        (t4 _ hya hyb) (by norm_num))
      hca0 ((casC_le_of x _ hL (by norm_num)).trans (by norm_num)) (i4 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 49000000000000000000000000000 with hb5 | hb5
  · have hlo : (4900000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb4.le
    have hL : 63.7590326 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL11.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 66.0616179 :=
      ((Real.log_le_log hx0 hb5).trans lgsU12).trans (by norm_num)
    have hya : (10 ^ 26) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 27) := MN.y_le_of x _ (le_trans hb5 (by norm_num))
    exact MN.blk 8.54 0.791 0.0422891 18.64427 (18.75258 * 0.0128533) 1.334445 0.0803961 _ _ _ _ _
        hg0 hg hh0
      ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfC_le_of x _ hx hU).trans (by norm_num))
        (t5 _ hya hyb) (by norm_num))
      hca0 ((casC_le_of x _ hL (by norm_num)).trans (by norm_num)) (i5 _ hya hyb)
      (by norm_num) (by norm_num)
  have hlo : (49000000000000000000000000000 : ℝ) ≤ x := hb5.le
  have hL : 66.0616177 ≤ Real.log x :=
    le_trans (by norm_num) (lgsL13.trans (Real.log_le_log (by norm_num) hlo))
  exact MN.blk 8.54 0.791 0.0422891 18.61688 0.206012 1.332484 0.103905 _ _ _ _ _ hg0 hg hh0
    ((hsC_le_of x _ hx hL (by norm_num)).trans (by norm_num))
    (tf x (le_trans (by norm_num) hlo)) hca0
    ((casC_le_of x _ hL (by norm_num)).trans (by norm_num))
    (ifr _ (MN.y_ge_of x _ (le_trans (by norm_num) hlo))) (by norm_num) (by norm_num)

end Principia.Common.TernaryGoldbach.MC
