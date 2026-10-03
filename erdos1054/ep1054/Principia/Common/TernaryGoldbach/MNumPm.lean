/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumP
import Principia.Common.TernaryGoldbach.OstopPm

set_option autoImplicit false

/-!
# `OPm.MNumPm 0.811 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406` PROVED

The `M̃` link at `c⁻ = −1.39`. `MNP.mnumP_proved` closes `OP.MNumP … 0.84` at `c⁻ = −1.306476`
from links about `g̃_P` alone (`G0EnvP`, `T1BlkP`, `IGBlkP`, `IGFarP`, all PROVED in `MNumP.lean`)
and the far link `T1FarP` (which carries `ML.cfL`). `c⁻` enters `M̃` only through the `x`-side
coefficients, never through `g̃`. So here the SAME links close the SAME six blocks with the
`x`-side recomputed at `(cm, jc) = (1.39, −3.627308)`:

* `hsLm 1.39 = H̃(r₀)·felipa` — decreasing in `x`, bounded at each block's LOW `log x`; it RISES
  with `cm` (`log √x − cm` shrinks), e.g. `18.68522 ↦ 18.73841` on the first block;
* `casLm 1.39 = 2 felipa/(log x − 2cm)` — decreasing, at the low end: `1.337375 ↦ 1.341183`;
* `cfLm 1.39 (−3.627308) = coefCm·felipa` — increasing, at the high end: `17.46297 ↦ 17.40046`
  (the jump constant moved DOWN by `0.089093`, which lowers `coefC`);
* the far regime reuses `MNP.t1FarP` through `cfLm ≤ cfL` (`coefCm_le_coefC`) and `g̃_P ≥ 0`.

Each `x`-side lemma is generated from `ML`'s (and `MC.coefC_bounds`) by COUNTED substitution
(`scratchpad/ostoppm/gen_mnumpm.py`: `1.306476 ↦ 1.39`, `−3.538215 ↦ −3.627308`); the
coefficients are pinned to `ML.hsL`, `ML.casL`, `ML.cfL` at `(1.306476, −3.538215)` by `rfl`.

## The certificate (exact rationals, `scratchpad/ostoppm/mnumpm_cert_price.py`)

| block (`y`) | `H` | `cf` | `k` | value | margin to `0.84` |
|---|---|---|---|---|---|
| `[10²⁵, 1.3·10²⁵]` | `18.73841` | `17.40046` | `1.341183` | `0.8368702` | `0.0031298` |
| `[1.3, 1.84]·10²⁵` | `18.73468` | `17.50459` | `1.340916` | `0.8336611` | `0.0063389` |
| `[1.84, 3.65]·10²⁵` | `18.72979` | `17.70988` | `1.340566` | `0.8336749` | `0.0063251` |
| `[3.65·10²⁵, 10²⁶]` | `18.72032` | `18.01193` | `1.339888` | `0.8270210` | `0.0129790` |
| `[10²⁶, 10²⁷]` | `18.70677` | `18.70191` | `1.338918` | `0.8208900` | `0.0191100` |
| far `y ≥ 10²⁷` | `18.67743` | (`T₁ ≤ 0.214913`) | `1.336818` | `0.8137372` | `0.0262628` |

The same script at `(1.306476, −3.538215)` reproduces `MNP`'s constants digit for digit. The
float price of `sup M̃` at `c⁻ = −1.39` is `0.8201` (at `x = 4.9·10²⁶`), so the PROOF LOSS of the
certificate is `0.8368702 − 0.8201 ≈ 0.0168`, the same block structure and the same `g̃_P` links as
`MNP` (whose loss is `0.83524 − 0.81849 ≈ 0.0168`).
-/

namespace Principia.Common.TernaryGoldbach.MNPm

open MinSp MeasureTheory Set MC
open Principia.Common.TernaryGoldbach.ML
open Principia.Common.TernaryGoldbach.OP
open Principia.Common.TernaryGoldbach.OPm
open Principia.Common.TernaryGoldbach.MNP

-- `g̃` and `∫g̃/r` at `(0.811, 45.7575)` on Helfgott's `φ`
local notation "gPh" => gTP 0.811 45.7575 HW.phi
local notation "iPh" => intGTP 0.811 45.7575 HW.phi

/-! ## (1) The `x`-side coefficients at `cm` (and `jc`), pinned -/

/-- **`H̃(r₀)·felipa(x)`** at `cm` (generated from `ML.hsL`). -/
noncomputable def hsLm (cm x : ℝ) : ℝ := hR0Cm cm x * felL x

/-- **`2 felipa(x)/(log x − 2cm)`** (generated from `ML.casL`). -/
noncomputable def casLm (cm x : ℝ) : ℝ := 2 / (Real.log x - 2 * cm) * felL x

/-- **`coefCm(x)·felipa(x)`** at `(cm, jc)` (generated from `ML.cfL`). -/
noncomputable def cfLm (cm jc x : ℝ) : ℝ := coefCm cm jc x * felL x

theorem hsLm_pin : hsLm 1.306476 = hsL :=
  rfl

theorem casLm_pin : casLm 1.306476 = casL :=
  rfl

theorem cfLm_pin : cfLm 1.306476 (-3.538215) = cfL :=
  rfl

/-! ## (2) The `x`-side at `(1.39, −3.627308)` (generated from `ML`, `MC`) -/

/-- **`hsLm` in closed form** (generated from `ML.hsL_eq`). -/
theorem hsLm_eq (x : ℝ) (hx : 0 ≤ x) :
    hsLm 1.39 x = (Real.log 150001 + 2.05315) *
      ((0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.39)) := by
  unfold hsLm hR0Cm felL
  rw [Real.log_sqrt hx]
  ring

/-- **`hsLm` decreases**: `hsLm(x) ≤ 13.97156·f(L₀)` once `61 ≤ L₀ ≤ log x` (generated from
`ML.hsL_le_of`). -/
theorem hsLm_le_of (x Llo : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hL : Llo ≤ Real.log x) (h61 : 61 ≤ Llo) :
    hsLm 1.39 x ≤ 13.97156 * ((0.6406 * Llo - 0.021095) / (Llo / 2 - 1.39)) := by
  have hx0 := x_pos x hx
  have hN := MN.log_150001_le
  have hf : (0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.39) ≤
      (0.6406 * Llo - 0.021095) / (Llo / 2 - 1.39) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hf0 : 0 ≤ (0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.39) :=
    div_nonneg (by linarith) (by linarith)
  rw [hsLm_eq x hx0.le]
  exact mul_le_mul (by linarith) hf hf0 (by norm_num)

/-- **`hsLm ≥ 8.54`** on `x ≥ 4.9·10²⁶` (generated from `ML.hsL_ge`). -/
theorem hsLm_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 8.54 ≤ hsLm 1.39 x := by
  have hx0 := x_pos x hx
  have hL := LW.log_ge_of x hx
  have hN0 := MN.log_150001_ge
  have hf : 1.28 ≤ (0.6406 * Real.log x - 0.021095) / (Real.log x / 2 - 1.39) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [hsLm_eq x hx0.le]
  calc (8.54 : ℝ) ≤ 13.83665 * 1.28 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith) hf (by norm_num) (by linarith)

/-- **`casLm` in closed form** (generated from `ML.casL_eq`). -/
theorem casLm_eq (x : ℝ) :
    casLm 1.39 x = 2 * (0.6406 * Real.log x - 0.021095) / (Real.log x - 2 * 1.39) := by
  unfold casLm felL
  ring

/-- **`casLm` decreases** (generated from `ML.casL_le_of`). -/
theorem casLm_le_of (x Llo : ℝ) (hL : Llo ≤ Real.log x) (h61 : 61 ≤ Llo) :
    casLm 1.39 x ≤ 2 * (0.6406 * Llo - 0.021095) / (Llo - 2 * 1.39) := by
  rw [casLm_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `casLm ≥ 0` (generated from `ML.casL_nonneg`). -/
theorem casLm_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ casLm 1.39 x := by
  have hL := LW.log_ge_of x hx
  rw [casLm_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **`0 ≤ coefCm ≤ 7/15`** on `x ≥ 4.9·10²⁶` at `(1.39, −3.627308)` (generated from
`MC.coefC_bounds`). -/
theorem coefCm_bounds (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 ≤ coefCm 1.39 (-3.627308) x ∧ coefCm 1.39 (-3.627308) x ≤ 7 / 15 := by
  have hL := LW.log_ge_of x hx
  have h49 := log49_le
  have h49' : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  have hD : 0 < Real.log x - 2 * 1.39 := by linarith
  unfold coefCm
  constructor
  · have a1 : -3.627308 / (Real.log x - 2 * 1.39) ≤
        (-3.627308 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.39) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    have a2 : -1 / 15 ≤ -3.627308 / (Real.log x - 2 * 1.39) := by
      rw [le_div_iff₀ hD]
      linarith
    linarith
  · have a1 : (-3.627308 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.39) ≤ 0 := by
      rw [div_le_iff₀ hD]
      linarith
    linarith

/-- **`cfLm` increases**: `cfLm(x) ≤ (7/15 + d̄/(L₁ − 2.78))(0.6406L₁ − 0.021095)` for
`log x ≤ L₁`, `d̄ = −3.627308 + (8/15)·3.891821` (generated from `ML.cfL_le_of`). -/
theorem cfLm_le_of (x Lhi : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hU : Real.log x ≤ Lhi) :
    cfLm 1.39 (-3.627308) x ≤ (7 / 15 + (-3.627308 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.39)) *
      (0.6406 * Lhi - 0.021095) := by
  have hL := LW.log_ge_of x hx
  have h49 := log49_le
  have hD : 0 < Real.log x - 2 * 1.39 := by linarith
  obtain ⟨hc0, -⟩ := coefCm_bounds x hx
  have hc : coefCm 1.39 (-3.627308) x ≤
      7 / 15 + (-3.627308 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.39) := by
    unfold coefCm
    have a1 : (-3.627308 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.39) ≤
        (-3.627308 + 8 / 15 * 3.891821) / (Real.log x - 2 * 1.39) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    have a2 : (-3.627308 + 8 / 15 * 3.891821) / (Real.log x - 2 * 1.39) ≤
        (-3.627308 + 8 / 15 * 3.891821) / (Lhi - 2 * 1.39) := by
      rw [div_le_div_iff₀ hD (by linarith)]
      nlinarith
    linarith
  have hf : felL x ≤ 0.6406 * Lhi - 0.021095 := by
    unfold felL
    linarith
  have hf0 : 0 ≤ felL x := by
    unfold felL
    linarith
  unfold cfLm
  exact mul_le_mul hc hf hf0 (hc0.trans hc)

/-- `cfLm ≥ 0` (generated from `ML.cfL_nonneg`). -/
theorem cfLm_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ cfLm 1.39 (-3.627308) x := by
  have hL := LW.log_ge_of x hx
  have hf0 : 0 ≤ felL x := by
    unfold felL
    linarith
  unfold cfLm
  exact mul_nonneg (coefCm_bounds x hx).1 hf0

/-- **`coefC` at `c⁻ = −1.39` is BELOW `coefC` at `−1.306476`**: with `a = (8/15) log 49`,
`(−3.627308 + a)(L − 2.612952) ≤ (−3.538215 + a)(L − 2.78)` is
`0 ≤ 0.089093L + 0.35815 − 0.167048a`, true for `L ≥ 0`, `log 49 ≤ 3.891821`. -/
theorem coefCm_le_coefC (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    coefCm 1.39 (-3.627308) x ≤ OC.coefC x := by
  have hL := LW.log_ge_of x hx
  have h49 := log49_le
  have h49' : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  have hD1 : 0 < Real.log x - 2 * 1.39 := by linarith
  have hD2 : 0 < Real.log x - 2 * 1.306476 := by linarith
  unfold coefCm OC.coefC
  have h : (-3.627308 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.39) ≤
      (-3.538215 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.306476) := by
    rw [div_le_div_iff₀ hD1 hD2]
    nlinarith
  linarith

/-- **`cfLm ≤ cfL`** on `x ≥ 4.9·10²⁶`. -/
theorem cfLm_le_cfL (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : cfLm 1.39 (-3.627308) x ≤ cfL x := by
  have hL := LW.log_ge_of x hx
  have hf0 : 0 ≤ felL x := by
    unfold felL
    linarith
  unfold cfLm cfL
  exact mul_le_mul_of_nonneg_right (coefCm_le_coefC x hx) hf0

/-- **The far `g̃_P(r₁)` link at `c⁻ = −1.39`** from `MNP.T1FarP`: `cfLm ≤ cfL` and
`g̃_P(r₁) ≥ 0` (`OSP.gTP_nonneg`, `r₁ ≥ 1.5·10⁶`). -/
theorem t1FarPm_of (T : ℝ) (tf : T1FarP T) (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    cfLm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49)) ≤ T := by
  have hx26 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hy := y_ge x hx26
  have hr1 := MNP.r1y_ge (x / 49) hy
  have hg : 0 ≤ gPh (x / 49) (r1y (x / 49)) :=
    OSP.gTP_nonneg 0.811 45.7575 (by norm_num) (by norm_num) HW.phi (fun t _ => HW.phi_nonneg t)
      _ _ hy (by linarith) le_rfl
  exact (mul_le_mul_of_nonneg_right (cfLm_le_cfL x hx26) hg).trans (tf x hx)

/-! ## (3) THE COMPOSITION at `0.84` (generated from `MNumP.lean`) -/

/-- **The affine reduction** at `(1.39, −3.627308)` (generated from `MNP.mnumP_of_felipa`). -/
theorem mnumPm_of_felipa (p0 c : ℝ) (hp0 : 0 ≤ p0) (hc : 0 ≤ c) (hg : GTNonnegP)
    (hM : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      gPh (x / 49) 150000 * (hsLm 1.39 x - p0) +
        cfLm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49)) + casLm 1.39 x * iPh (x / 49) ≤
          c) :
    MNumPm 0.811 45.7575 1.39 (-3.627308) HW.phi p0 c 0.6406 := by
  intro x hx s p hs0 hs1 hp
  refine MN.affine_step _ _ _ _ s p p0 c (hg (x / 49) (y_ge x hx)) hp0 hs0 hs1 hp hc ?_
  have e : gPh (x / 49) 150000 * (hsLm 1.39 x - p0) +
        cfLm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49)) + casLm 1.39 x * iPh (x / 49) =
      gPh (x / 49) 150000 * (hR0Cm 1.39 x * (0.6406 * Real.log x - 0.021095) - p0) +
        (2 / (Real.log x - 2 * 1.39) * iPh (x / 49) +
          coefCm 1.39 (-3.627308) x * gPh (x / 49) (r1y (x / 49))) *
          (0.6406 * Real.log x - 0.021095) := by
    unfold hsLm cfLm casLm felL
    ring
  rw [← e]
  exact hM x hx

/-- **THE SPINE of `OPm.MNumPm 0.811 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406`**
(generated from `MNP.mnumP_of_links`: the SAME `g̃_P` links, every block re-closed with the
`x`-side at `c⁻ = −1.39`). -/
theorem mnumPm_of_links (g0 : GTNonnegP) (e0 : G0EnvP 0.0447364)
    (t0 : T1BlkP (10 ^ 25) (13 * 10 ^ 24) 0.0163883)
    (t1 : T1BlkP (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0160119)
    (t2 : T1BlkP (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0156446)
    (t3 : T1BlkP (365 * 10 ^ 23) (10 ^ 26) 0.0147789) (t4 : T1BlkP (10 ^ 26) (10 ^ 27) 0.0134759)
    (i0 : IGBlkP (10 ^ 25) (13 * 10 ^ 24) 0.0711805)
    (i1 : IGBlkP (13 * 10 ^ 24) (184 * 10 ^ 23) 0.0725669)
    (i2 : IGBlkP (184 * 10 ^ 23) (365 * 10 ^ 23) 0.0751596)
    (i3 : IGBlkP (365 * 10 ^ 23) (10 ^ 26) 0.0786585) (i4 : IGBlkP (10 ^ 26) (10 ^ 27) 0.0851734)
    (tf : T1FarP 0.214913) (ifr : IGFarP 0.1087) :
    MNumPm 0.811 45.7575 1.39 (-3.627308) HW.phi 8.54 0.84 0.6406 := by
  refine mnumPm_of_felipa 8.54 0.84 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hx0 := x_pos x hx
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hg := e0 (x / 49) (y_ge x hx)
  have hh0 := hsLm_ge x hx
  have hca0 := casLm_nonneg x hx
  have hcf0 := cfLm_nonneg x hx
  rcases le_or_gt x 637000000000000000000000000 with hb0 | hb0
  · have hlo : (490000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hx
    have hL : 61.4564475 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL1.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 61.718812 :=
      ((Real.log_le_log hx0 hb0).trans lgsU4).trans (by norm_num)
    have hya : (10 ^ 25) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (13 * 10 ^ 24) := MN.y_le_of x _ (le_trans hb0 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.73841 (17.40046 * 0.0163883) 1.341183 0.0711805 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t0 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i0 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 901600000000000000000000000 with hb1 | hb1
  · have hlo : (637000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb0.le
    have hL : 61.7188118 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL5.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.0662133 :=
      ((Real.log_le_log hx0 hb1).trans lgsU6).trans (by norm_num)
    have hya : (13 * 10 ^ 24) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (184 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb1 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.73468 (17.50459 * 0.0160119) 1.340916 0.0725669 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t1 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i1 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 1788500000000000000000000000 with hb2 | hb2
  · have hlo : (901600000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb1.le
    have hL : 62.0662131 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL7.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 62.7511749 :=
      ((Real.log_le_log hx0 hb2).trans lgsU8).trans (by norm_num)
    have hya : (184 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (365 * 10 ^ 23) := MN.y_le_of x _ (le_trans hb2 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.72979 (17.70988 * 0.0156446) 1.340566 0.0751596 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t2 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i2 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 4900000000000000000000000000 with hb3 | hb3
  · have hlo : (1788500000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb2.le
    have hL : 62.7511747 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL9.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 63.7590328 :=
      ((Real.log_le_log hx0 hb3).trans lgsU10).trans (by norm_num)
    have hya : (365 * 10 ^ 23) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 26) := MN.y_le_of x _ (le_trans hb3 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.72032 (18.01193 * 0.0147789) 1.339888 0.0786585 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t3 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i3 _ hya hyb)
      (by norm_num) (by norm_num)
  rcases le_or_gt x 49000000000000000000000000000 with hb4 | hb4
  · have hlo : (4900000000000000000000000000 : ℝ) ≤ x := le_trans (by norm_num) hb3.le
    have hL : 63.7590326 ≤ Real.log x :=
      le_trans (by norm_num) (lgsL11.trans (Real.log_le_log (by norm_num) hlo))
    have hU : Real.log x ≤ 66.0616179 :=
      ((Real.log_le_log hx0 hb4).trans lgsU12).trans (by norm_num)
    have hya : (10 ^ 26) ≤ x / 49 := MN.y_ge_of x _ (le_trans (by norm_num) hlo)
    have hyb : x / 49 ≤ (10 ^ 27) := MN.y_le_of x _ (le_trans hb4 (by norm_num))
    exact MN.blk 8.54 0.84 0.0447364 18.70677 (18.70191 * 0.0134759) 1.338918 0.0851734 _ _ _ _ _
        hg0 hg hh0
      ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
      (mul_le_of _ _ _ _ hcf0 ((cfLm_le_of x _ hx hU).trans (by norm_num))
        (t4 _ hya hyb) (by norm_num))
      hca0 ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num)) (i4 _ hya hyb)
      (by norm_num) (by norm_num)
  have hlo : (49000000000000000000000000000 : ℝ) ≤ x := hb4.le
  have hL : 66.0616177 ≤ Real.log x :=
    le_trans (by norm_num) (lgsL13.trans (Real.log_le_log (by norm_num) hlo))
  exact MN.blk 8.54 0.84 0.0447364 18.67743 0.214913 1.336818 0.1087 _ _ _ _ _ hg0 hg hh0
    ((hsLm_le_of x _ hx hL (by norm_num)).trans (by norm_num))
    (t1FarPm_of _ tf x (le_trans (by norm_num) hlo)) hca0
    ((casLm_le_of x _ hL (by norm_num)).trans (by norm_num))
    (ifr _ (MN.y_ge_of x _ (le_trans (by norm_num) hlo))) (by norm_num) (by norm_num)

/-- **`OPm.MNumPm 0.811 45.7575 1.39 (−3.627308) HW.phi 8.54 0.84 0.6406`, PROVED** from
`MNumP.lean`'s proved links; smallest certified margin `0.0031298` (first block). -/
theorem mnumPm_proved : MNumPm 0.811 45.7575 1.39 (-3.627308) HW.phi 8.54 0.84 0.6406 :=
  mnumPm_of_links gtNonnegP g0EnvP t1BlkP0 t1BlkP1 t1BlkP2 t1BlkP3 t1BlkP4 iGBlkP0 iGBlkP1
    iGBlkP2 iGBlkP3 iGBlkP4 t1FarP iGFarP

end Principia.Common.TernaryGoldbach.MNPm
