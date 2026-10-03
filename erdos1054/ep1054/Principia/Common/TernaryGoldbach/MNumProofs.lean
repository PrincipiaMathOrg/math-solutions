/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumSpine

set_option autoImplicit false

/-!
# Discharges for the `MNumAt` spine: `MinW.MNumW HW.phi 0.785` is PROVED

**`mnumW_proved : MinW.MNumW HW.phi 0.785`** and **`mnumAt_proved : MNumAt 8.36 0.785`**, with no
hypotheses: every link of `MNumSpine.lean`'s envelope route is discharged here.

| sub-link | how | § |
|---|---|---|
| `EnvDeriv` | `PhiQ` differentiated in `ℓ = log r` (`quad·e^{kℓ}`) | (2) |
| `F2Anti` | `(K/y)^{1/6}`, `log y/y` decreasing | (3) |
| `g0Env_of`, `t1Num_of`, `igBlk_of`, `igTail_of` | FTC inequality; junk: `integral_undef` | (4) |
| `R1Le` ×7 | `y⁴ ≤ (8R/3)¹⁵` | (5) |
| `EnvPt` | tangents of `√·`, `log`; `e^γ ≤ 1.7881` (`H₁₂₈`) | (6) |
| `C_{φ,2,K} ∈ [0,1/9]`, `RKMono`, `G0Nonneg` | FTC; `R` monotone; `y/K` increasing | (7) |
| `RKNum` ×11, `G0Num` ×4, `IBlkNum` ×3, `ITailNum`, `T1EnvNum` ×4 | `log` series | (9)–(10) |
| `F2Tail`, `RKTail` | `K⁷/y` decreasing; the ratio inside `R` is `≤ 2.08` | (12) |
| `EnvAnti`, `T1Reg` ×3, `T1Far` | `envQ` falls; `coefC·felipa` rises; `K⁴⁵/y²` falls | (13) |

`T1Anti` (exact monotonicity of `t1`) is NOT proved and NOT needed: `T₁` is bounded region by region
through the envelope instead (`MN.mnumAt_of_links2`); `mnumAt_of_t1Anti` records the older route.
Numerics are generated and pre-checked in exact rationals by `scratchpad/lean/gen_mnum_num.py`,
`t1_consts.py`; the design by `scratchpad/minsp/mn_design.py`, `mn_final.py`, `t1_env_blocks.py`.
-/

namespace Principia.Common.TernaryGoldbach.MN

open MinSp MeasureTheory Set Finset

/-! ## (1) Elementary facts -/

/-- `y ≥ 10²⁵ ⇒ log y ≥ 1`. -/
theorem log_ge_one_y (y : ℝ) (hy : 10 ^ 25 ≤ y) : 1 ≤ Real.log y := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  linarith

/-- `felipa(x) ≥ 0` on `x ≥ 4.9·10²⁶`. -/
theorem fel_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ fel x := by
  have := MajSp.log_ge_one x hx
  unfold fel
  linarith

/-- `coefC(x) ≥ 0` on `x ≥ 4.9·10²⁶` (`7/15 − 2.14938/(log x + 1.2588)`). -/
theorem coefC_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ coefC x := by
  have hL := LW.log_ge_of x hx
  have h49 : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  unfold coefC
  have hd : 0 < Real.log x + 2 * 0.6294 := by linarith
  have h1 : -2.14938 / (Real.log x + 2 * 0.6294) ≤
      (-2.14938 + 8 / 15 * Real.log 49) / (Real.log x + 2 * 0.6294) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have h2 : -(2.14938 / 60) ≤ -2.14938 / (Real.log x + 2 * 0.6294) := by
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

/-- `r₁ = (3/8)y^{4/15}` increases. -/
theorem r1y_mono (y y' : ℝ) (hy : 0 ≤ y) (h : y ≤ y') : r1y y ≤ r1y y' := by
  unfold r1y
  have := Real.rpow_le_rpow hy h (by norm_num : (0 : ℝ) ≤ 4 / 15)
  linarith

/-- `y^{m/n} ≥ q` from `q^n ≤ y^m` (`q, y ≥ 0`, `n ≠ 0`). -/
theorem le_rpow_of_pow (y q : ℝ) (m n : ℕ) (hn : n ≠ 0) (hy : 0 ≤ y) (hq : 0 ≤ q)
    (h : q ^ n ≤ y ^ m) : q ≤ y ^ ((m : ℝ) / n) := by
  have e1 : y ^ ((m : ℝ) / n) = (y ^ m) ^ ((n : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hy, Real.rpow_natCast]
  have e2 : q = (q ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hq hn).symm
  rw [e1]
  calc q = (q ^ n) ^ ((n : ℝ)⁻¹) := e2
    _ ≤ (y ^ m) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (pow_nonneg hq n) h (by positivity)

/-- `y^{m/n} ≤ q` from `y^m ≤ q^n`. -/
theorem rpow_le_of_pow (y q : ℝ) (m n : ℕ) (hn : n ≠ 0) (hy : 0 ≤ y) (hq : 0 ≤ q)
    (h : y ^ m ≤ q ^ n) : y ^ ((m : ℝ) / n) ≤ q := by
  have e1 : y ^ ((m : ℝ) / n) = (y ^ m) ^ ((n : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hy, Real.rpow_natCast]
  have e2 : q = (q ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hq hn).symm
  rw [e1]
  calc (y ^ m) ^ ((n : ℝ)⁻¹) ≤ (q ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (pow_nonneg hy m) h (by positivity)
    _ = q := e2.symm

/-- `r₁(y) ≥ r₀ = 150000` for `y ≥ 10²⁵` (`(10²⁵)^{4/15} ≥ 400000`). -/
theorem r1y_ge (y : ℝ) (hy : 10 ^ 25 ≤ y) : 150000 ≤ r1y y := by
  have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) hy
  have h := le_rpow_of_pow y 400000 4 15 (by norm_num) hy0 (by norm_num)
    (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy 4))
  unfold r1y
  have e : ((4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ) = 4 / 15 := by norm_num
  rw [e] at h
  linarith

/-- `envQ ρ r ≥ 0` for `ρ ≥ 0`, `r ≥ 1`. -/
theorem envQ_nonneg (ρ r : ℝ) (hρ : 0 ≤ ρ) (hr : 1 ≤ r) : 0 ≤ envQ ρ r := by
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have hp : 0 ≤ pA ρ (Real.log r) := by
    unfold pA
    have : 0 ≤ ρ * (0.6931471808 + Real.log r) + 0.5 := by positivity
    positivity
  have hq : 0 ≤ qA (Real.log r) := by
    unfold qA
    positivity
  unfold envQ
  have : 0 < r := by linarith
  positivity

/-- `PhiQ ρ r ≤ 0` for `ρ ≥ 0`, `r ≥ 1` (all its coefficients are nonnegative). -/
theorem PhiQ_nonpos (ρ r : ℝ) (hρ : 0 ≤ ρ) (hr : 1 ≤ r) : PhiQ ρ r ≤ 0 := by
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have hS : 0 ≤ pA ρ (Real.log r) + 2 * dpA ρ (Real.log r) + 4 * ddpA ρ := by
    unfold pA dpA ddpA
    have : 0 ≤ ρ * (0.6931471808 + Real.log r) + 0.5 := by positivity
    positivity
  have hT : 0 ≤ qA (Real.log r) + dqA (Real.log r) + ddqA := by
    unfold qA dqA ddqA
    positivity
  have hr0 : 0 < r := by linarith
  unfold PhiQ
  have h1 : 0 ≤ (2 * 0.70711) * (pA ρ (Real.log r) + 2 * dpA ρ (Real.log r) + 4 * ddpA ρ) /
      Real.sqrt r := by positivity
  have h2 : 0 ≤ (qA (Real.log r) + dqA (Real.log r) + ddqA) / r := by positivity
  rw [neg_mul, neg_div]
  linarith

/-- `f₂(y) ≥ 0` for `y ≥ 1`. -/
theorem f2_nonneg (y : ℝ) (hy : 1 ≤ y) : 0 ≤ f2 y := by
  have hK : 0 ≤ kK y := by
    unfold kK
    have := Real.log_nonneg hy
    positivity
  unfold f2
  have := Real.rpow_nonneg hK ((1 : ℝ) / 6)
  have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ y) (-(1 : ℝ) / 6)
  positivity

/-! ## (2) DISCHARGED: `EnvDeriv`, the closed form -/

/-- A quadratic times an exponential. -/
theorem hasDerivAt_quad_exp (a b c k l : ℝ) :
    HasDerivAt (fun l => (a + b * l + c * l ^ 2) * Real.exp (k * l))
      ((b + 2 * c * l + k * (a + b * l + c * l ^ 2)) * Real.exp (k * l)) l := by
  have h1 : HasDerivAt (fun l => a + b * l + c * l ^ 2) (b + 2 * c * l) l :=
    ((((hasDerivAt_id' (x := l)).const_mul b).const_add a).add
      ((hasDerivAt_pow 2 l).const_mul c)).congr_deriv (by push_cast; ring)
  have h2 : HasDerivAt (fun l => Real.exp (k * l)) (Real.exp (k * l) * k) l :=
    (((hasDerivAt_id' (x := l)).const_mul k).exp).congr_deriv (by ring)
  exact (h1.mul h2).congr_deriv (by ring)

/-- `1/√r = e^{−ℓ/2}` for `r > 0`. -/
theorem inv_sqrt_eq (r : ℝ) (hr : 0 < r) :
    (Real.sqrt r)⁻¹ = Real.exp (-(1 / 2) * Real.log r) := by
  rw [show -(1 / 2) * Real.log r = -(Real.log r * (1 / 2)) by ring, Real.exp_neg,
    ← Real.rpow_def_of_pos hr, ← Real.sqrt_eq_rpow]

/-- `1/r = e^{−ℓ}` for `r > 0`. -/
theorem inv_eq_exp (r : ℝ) (hr : 0 < r) : r⁻¹ = Real.exp (-1 * Real.log r) := by
  rw [show -1 * Real.log r = -Real.log r by ring, Real.exp_neg, Real.exp_log hr]

/-- `PhiQ` in the variable `ℓ = log r`: two quadratics times `e^{−ℓ/2}`, `e^{−ℓ}`. -/
theorem PhiQ_eq (ρ r : ℝ) (hr : 0 < r) :
    PhiQ ρ r =
      -(2 * 0.70711) * (((ρ * 0.6931471808 + 0.5) * 1.949682 + 2.5 +
            2 * (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156) + 8 * ρ * 0.032156 +
          (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156 + 4 * ρ * 0.032156) *
            Real.log r + ρ * 0.032156 * Real.log r ^ 2) *
          Real.exp (-(1 / 2) * Real.log r)) -
        ((3.6544 * (7 / 4 * 0.6931471808 + 80 / 9) + 16 / 9 * 0.6931471808 + 111 / 5 +
            (0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 13 / 4 * 3.6544 + 80 / 9) +
            2 * 0.15003 * (13 / 4) +
          (3.6544 * (13 / 4) + 0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 80 / 9 +
            13 / 2 * 0.15003) * Real.log r + 0.15003 * (13 / 4) * Real.log r ^ 2) *
          Real.exp (-1 * Real.log r)) := by
  unfold PhiQ pA dpA ddpA qA dqA ddqA
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_sqrt_eq r hr, inv_eq_exp r hr]
  ring

/-- `envQ` in the variable `ℓ = log r`. -/
theorem envQ_eq (ρ r : ℝ) (hr : 0 < r) :
    envQ ρ r = 0.70711 * pA ρ (Real.log r) * Real.exp (-(1 / 2) * Real.log r) +
      qA (Real.log r) * Real.exp (-1 * Real.log r) := by
  unfold envQ
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_sqrt_eq r hr, inv_eq_exp r hr]

/-- **[EnvDeriv] DISCHARGED**: `d/dr PhiQ ρ r = envQ ρ r / r` for `r > 0`. In `ℓ = log r`,
`PhiQ = −2c·S(ℓ)e^{−ℓ/2} − T(ℓ)e^{−ℓ}` with `S = P + 2P′ + 4P″`, `T = Q + Q′ + Q″`, whose
`ℓ`-derivative is `c(S − 2S′)e^{−ℓ/2} + (T − T′)e^{−ℓ} = cP e^{−ℓ/2} + Q e^{−ℓ}`. -/
theorem envDeriv : EnvDeriv := by
  intro ρ r hr
  have hG := ((hasDerivAt_quad_exp
      ((ρ * 0.6931471808 + 0.5) * 1.949682 + 2.5 +
        2 * (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156) + 8 * ρ * 0.032156)
      (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156 + 4 * ρ * 0.032156)
      (ρ * 0.032156) (-(1 / 2)) (Real.log r)).const_mul (-(2 * 0.70711))).sub
    (hasDerivAt_quad_exp
      (3.6544 * (7 / 4 * 0.6931471808 + 80 / 9) + 16 / 9 * 0.6931471808 + 111 / 5 +
        (0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 13 / 4 * 3.6544 + 80 / 9) +
        2 * 0.15003 * (13 / 4))
      (3.6544 * (13 / 4) + 0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 80 / 9 +
        13 / 2 * 0.15003)
      (0.15003 * (13 / 4)) (-1) (Real.log r))
  have hc := hG.comp r (Real.hasDerivAt_log hr.ne')
  have heq : PhiQ ρ =ᶠ[nhds r] (fun l => -(2 * 0.70711) *
      (((ρ * 0.6931471808 + 0.5) * 1.949682 + 2.5 +
            2 * (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156) + 8 * ρ * 0.032156 +
          (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156 + 4 * ρ * 0.032156) * l +
            ρ * 0.032156 * l ^ 2) * Real.exp (-(1 / 2) * l)) -
        ((3.6544 * (7 / 4 * 0.6931471808 + 80 / 9) + 16 / 9 * 0.6931471808 + 111 / 5 +
            (0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 13 / 4 * 3.6544 + 80 / 9) +
            2 * 0.15003 * (13 / 4) +
          (3.6544 * (13 / 4) + 0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 80 / 9 +
            13 / 2 * 0.15003) * l + 0.15003 * (13 / 4) * l ^ 2) * Real.exp (-1 * l))) ∘
      Real.log := by
    filter_upwards [lt_mem_nhds hr] with u hu
    exact PhiQ_eq ρ u hu
  refine (hc.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [envQ_eq ρ r hr, div_eq_mul_inv]
  unfold pA qA
  ring

/-! ## (3) DISCHARGED: `F2Anti` -/

/-- `log y'/y' ≤ log y/y` for `log y ≥ 1`, `y ≤ y'` (`log(y'/y) ≤ y'/y − 1`). -/
theorem logdiv_anti (y y' : ℝ) (hy0 : 0 < y) (hl : 1 ≤ Real.log y) (h : y ≤ y') :
    Real.log y' / y' ≤ Real.log y / y := by
  have hy1 : 0 < y' := lt_of_lt_of_le hy0 h
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy1 hy0)
  rw [Real.log_div hy1.ne' hy0.ne'] at h1
  have h2 : y * (Real.log y' - Real.log y) ≤ y * (y' / y - 1) :=
    mul_le_mul_of_nonneg_left h1 hy0.le
  have h3 : y * (y' / y - 1) = y' - y := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_left hl (sub_nonneg.2 h)
  rw [div_le_div_iff₀ hy1 hy0]
  nlinarith

/-- `f₂(y) = 3.2 (K/y)^{1/6}` for `y ≥ 1`. -/
theorem f2_eq (y : ℝ) (hy : 1 ≤ y) : f2 y = 3.2 * (kK y / y) ^ ((1 : ℝ) / 6) := by
  have hy0 : 0 ≤ y := by linarith
  have hK : 0 ≤ kK y := by
    unfold kK
    have := Real.log_nonneg hy
    positivity
  unfold f2
  rw [Real.div_rpow hK hy0, show -(1 : ℝ) / 6 = -((1 : ℝ) / 6) by ring, Real.rpow_neg hy0]
  ring

/-- **[F2Anti] DISCHARGED**: `f₂ = 3.2(K/y)^{1/6}` decreases on `y ≥ 10²⁵`. -/
theorem f2Anti : F2Anti := by
  intro y y' hy h
  have hy1 : 1 ≤ y := le_trans (by norm_num) hy
  have hy0 : 0 < y := by linarith
  have hl := log_ge_one_y y hy
  rw [f2_eq y hy1, f2_eq y' (hy1.trans h)]
  have hq : kK y' / y' ≤ kK y / y := by
    unfold kK
    rw [div_div, div_div, mul_comm 2 y', mul_comm 2 y, ← div_div, ← div_div]
    exact div_le_div_of_nonneg_right (logdiv_anti y y' hy0 hl h) (by norm_num)
  have hq0 : 0 ≤ kK y' / y' := by
    have hl' : 0 ≤ Real.log y' := Real.log_nonneg (hy1.trans h)
    unfold kK
    have : 0 < y' := by linarith
    positivity
  have := Real.rpow_le_rpow hq0 hq (by norm_num : (0 : ℝ) ≤ 1 / 6)
  linarith

/-! ## (4) The reductions: level-2 sub-links → level-1 links -/

/-- **`G0Env` from `RKBnd` at `t_b = 2r₀`, `EnvPt`, `F2Anti`, `G0Num`.** -/
theorem g0Env_of (ya ρ G : ℝ) (hρ : 0 ≤ ρ) (hya : 10 ^ 25 ≤ ya) (hrk : RKBnd ya 300000 ρ)
    (hen : EnvPt) (hf2 : F2Anti) (hn : G0Num ya ρ G) : G0Env ya G := by
  intro y hy
  have h1 : rRK HW.phi y (2 * 150000) ≤ ρ := by
    rw [show (2 : ℝ) * 150000 = 300000 by norm_num]
    exact hrk y 300000 hy (by norm_num) le_rfl
  have h2 := hen ρ y 150000 hρ le_rfl h1
  have h3 := hf2 ya y hya hy
  unfold G0Num at hn
  linarith

/-- **`T1Num` from `RKBnd` covering `t = 2r₁(y_a)`, `EnvPt` at `r = r₁(y_a)`, `T1EnvNum`.** -/
theorem t1Num_of (xa tb ρ T : ℝ) (hρ : 0 ≤ ρ) (hxa : 49 * 10 ^ 25 ≤ xa)
    (hrk : RKBnd (xa / 49) tb ρ) (hr1 : 2 * r1y (xa / 49) ≤ tb) (hen : EnvPt)
    (hn : T1EnvNum xa ρ T) : T1Num xa T := by
  have hy := y_ge xa hxa
  have hr0 := r1y_ge _ hy
  have h1 := hrk (xa / 49) (2 * r1y (xa / 49)) le_rfl (by linarith) hr1
  have h2 := hen ρ (xa / 49) (r1y (xa / 49)) hρ hr0 h1
  have hcf : 0 ≤ coefC xa * fel xa := mul_nonneg (coefC_nonneg xa hxa) (fel_nonneg xa hxa)
  unfold T1Num t1
  unfold T1EnvNum at hn
  calc coefC xa * gB HW.phi (xa / 49) (r1y (xa / 49)) * fel xa
      = (coefC xa * fel xa) * gB HW.phi (xa / 49) (r1y (xa / 49)) := by ring
    _ ≤ (coefC xa * fel xa) * (envQ ρ (r1y (xa / 49)) + f2 (xa / 49)) :=
        mul_le_mul_of_nonneg_left h2 hcf
    _ = coefC xa * (envQ ρ (r1y (xa / 49)) + f2 (xa / 49)) * fel xa := by ring
    _ ≤ T := hn

/-- **The integral, bounded by the antiderivative**: with `R_{y,K,φ,2r} ≤ ρ` on `[r₀, r₁(y)]`
and `r₁(y) ≤ R`, `∫_{r₀}^{r₁(y)} g/r ≤ PhiQ ρ R − PhiQ ρ r₀ + f₂(y)(log R − log r₀)`
(`integral_le_sub_of_hasDeriv_right_of_le` when `g/r` is integrable on `[r₀, r₁]`; otherwise the
integral is `0` and the right side is `≥ 0` because the antiderivative increases). -/
theorem intG_le (y ρ R : ℝ) (hρ : 0 ≤ ρ) (h0 : 150000 ≤ r1y y) (hR : r1y y ≤ R)
    (hf : 0 ≤ f2 y) (hrk : ∀ r : ℝ, 150000 ≤ r → r ≤ r1y y → rRK HW.phi y (2 * r) ≤ ρ)
    (hen : EnvPt) :
    intG HW.phi y ≤ PhiQ ρ R - PhiQ ρ 150000 + f2 y * (Real.log R - Real.log 150000) := by
  have hGd : ∀ r : ℝ, 0 < r →
      HasDerivAt (fun r => PhiQ ρ r + f2 y * Real.log r) (envQ ρ r / r + f2 y * r⁻¹) r :=
    fun r hr => (envDeriv ρ r hr).add ((Real.hasDerivAt_log hr.ne').const_mul (f2 y))
  have hGd0 : ∀ r : ℝ, 150000 ≤ r → 0 ≤ envQ ρ r / r + f2 y * r⁻¹ := fun r hr => by
    have := envQ_nonneg ρ r hρ (by linarith)
    have hr0 : 0 < r := by linarith
    positivity
  have hmono : MonotoneOn (fun r => PhiQ ρ r + f2 y * Real.log r) (Ici 150000) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro r hr
      exact (hGd r (by simp only [Set.mem_Ici] at hr; linarith)).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      exact (hGd r (by simp only [Set.mem_Ioi] at hr; linarith)).differentiableAt
        |>.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      simp only [Set.mem_Ioi] at hr
      rw [(hGd r (by linarith)).deriv]
      exact hGd0 r hr.le
  have hGR := hmono (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr (h0.trans hR)) hR
  have hG0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h0) h0
  simp only at hGR hG0
  unfold intG
  by_cases hint : IntegrableOn (fun r => gB HW.phi y r / r) (Icc 150000 (r1y y))
  · have hle := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le h0
      (fun r hr => (hGd r (by linarith [hr.1])).continuousAt.continuousWithinAt)
      (fun r hr => (hGd r (by linarith [hr.1])).hasDerivWithinAt) hint
      (fun r hr => by
        have hr0 : 0 < r := by linarith [hr.1]
        have := hen ρ y r hρ hr.1.le (hrk r hr.1.le hr.2.le)
        rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
        exact mul_le_mul_of_nonneg_right this (inv_nonneg.mpr hr0.le))
    linarith
  · have hni : ¬ IntervalIntegrable (fun r => gB HW.phi y r / r) volume 150000 (r1y y) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0,
        ← integrableOn_Icc_iff_integrableOn_Ioc]
      exact hint
    rw [intervalIntegral.integral_undef hni]
    linarith

/-- **`IGBlk` from `RKBnd` at `t_b = 2R`, `R1Le y_b R`, `EnvPt`, `F2Anti`, `IBlkNum`** (and
`EnvDeriv`, proved). -/
theorem igBlk_of (ya yb ρ R I : ℝ) (hρ : 0 ≤ ρ) (hya : 10 ^ 25 ≤ ya)
    (hrk : RKBnd ya (2 * R) ρ) (hR : R1Le yb R) (hen : EnvPt) (hf2 : F2Anti)
    (hn : IBlkNum ya ρ R I) : IGBlk ya yb I := by
  intro y hy hyb
  have hy25 : 10 ^ 25 ≤ y := hya.trans hy
  have h0 := r1y_ge y hy25
  have hRy : r1y y ≤ R := (r1y_mono y yb (by linarith) hyb).trans hR
  have h := intG_le y ρ R hρ h0 hRy (f2_nonneg y (by linarith))
    (fun r hr1 hr2 => hrk y (2 * r) hy (by linarith) (by linarith)) hen
  have hf := hf2 ya y hya hy
  have hl : 0 ≤ Real.log R - Real.log 150000 := by
    have := Real.log_le_log (by norm_num) (h0.trans hRy)
    linarith
  have := mul_le_mul_of_nonneg_right hf hl
  unfold IBlkNum at hn
  linarith

/-- **`IGTail` from `RKTail`, `EnvPt`, `F2Tail`, `ITailNum`** (and `EnvDeriv`, `PhiQ ≤ 0`,
proved). -/
theorem igTail_of (ya ρ B I : ℝ) (hρ : 0 ≤ ρ) (hya : 10 ^ 25 ≤ ya) (hrk : RKTail ya ρ)
    (hen : EnvPt) (hft : F2Tail ya B) (hn : ITailNum ρ B I) : IGTail ya I := by
  intro y hy
  have hy25 : 10 ^ 25 ≤ y := hya.trans hy
  have h0 := r1y_ge y hy25
  have h := intG_le y ρ (r1y y) hρ h0 le_rfl (f2_nonneg y (by linarith))
    (fun r hr1 hr2 => hrk y r hy hr1 hr2) hen
  have hP := PhiQ_nonpos ρ (r1y y) hρ (by linarith)
  have hB := hft y hy
  unfold ITailNum at hn
  linarith

/-- `t1Num_of` with the block's `y_a` and the ceiling `t_b = 2r₁^{hi}` named. -/
theorem t1Num_of' (xa ya r1hi ρ T : ℝ) (hρ : 0 ≤ ρ) (hxa : 49 * 10 ^ 25 ≤ xa)
    (hxy : xa / 49 = ya) (hrk : RKBnd ya (2 * r1hi) ρ) (hr1 : R1Le ya r1hi) (hen : EnvPt)
    (hn : T1EnvNum xa ρ T) : T1Num xa T := by
  subst hxy
  unfold R1Le at hr1
  exact t1Num_of xa (2 * r1hi) ρ T hρ hxa hrk (by linarith) hen hn

/-! ## (5) DISCHARGED: `R1Le` at the seven points -/

/-- `r₁(y) ≤ R` from `y⁴ ≤ (8R/3)¹⁵`. -/
theorem r1Le_of (y R : ℝ) (hy : 0 ≤ y) (hR : 0 ≤ R) (h : y ^ 4 ≤ (8 * R / 3) ^ 15) :
    R1Le y R := by
  have h1 := rpow_le_of_pow y (8 * R / 3) 4 15 (by norm_num) hy (by positivity) h
  have e : ((4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ) = 4 / 15 := by norm_num
  rw [e] at h1
  unfold R1Le r1y
  linarith

/-- `r₁(10²⁵) = 1740595.8 ≤ 1740600`. -/
theorem r1Le_1 : R1Le (10 ^ 25) 1740600 := r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-- `r₁(3·10²⁵) = 2333083.4 ≤ 2333100`. -/
theorem r1Le_2 : R1Le (3 * 10 ^ 25) 2333100 :=
  r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-- `r₁(10²⁶) = 3216359.6 ≤ 3216400`. -/
theorem r1Le_3 : R1Le (10 ^ 26) 3216400 := r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-- `r₁(2·10²⁶) = 3869361.2 ≤ 3869400`. -/
theorem r1Le_4 : R1Le (2 * 10 ^ 26) 3869400 :=
  r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-- `r₁(3·10²⁵) ≤ 2.34·10⁶`. -/
theorem r1Le_b1 : R1Le (3 * 10 ^ 25) 2340000 :=
  r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-- `r₁(10²⁶) ≤ 3.22·10⁶`. -/
theorem r1Le_b2 : R1Le (10 ^ 26) 3220000 := r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-- `r₁(2·10²⁶) ≤ 3.87·10⁶`. -/
theorem r1Le_b3 : R1Le (2 * 10 ^ 26) 3870000 :=
  r1Le_of _ _ (by norm_num) (by norm_num) (by norm_num)

/-! ## (6) DISCHARGED: `EnvPt`, the pointwise envelope -/

/-- `H₁₂₈ ≤ 5.4331471` (exact rational arithmetic). -/
theorem harmonic_128_le : (harmonic 128 : ℚ) ≤ 5.4331471 := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **`γ < 0.581117`** (`γ < H₁₂₈ − log 128`, Mathlib's `eulerMascheroniSeq'` bound). -/
theorem gamma_lt : Real.eulerMascheroniConstant < 0.581117 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have hh : ((harmonic 128 : ℚ) : ℝ) ≤ ((5.4331471 : ℚ) : ℝ) := Rat.cast_le.mpr harmonic_128_le
  rw [show ((5.4331471 : ℚ) : ℝ) = 5.4331471 by norm_num] at hh
  have hl : (128 : ℝ) = 2 ^ 7 := by norm_num
  have hlog : Real.log (128 : ℕ) = 7 * Real.log 2 := by
    rw [Nat.cast_ofNat, hl, Real.log_pow]
    norm_num
  unfold Real.eulerMascheroniSeq' at h
  rw [if_neg (by norm_num), hlog] at h
  have := Real.log_two_gt_d9
  linarith

/-- **`e^γ ≤ 1.7881`** (truth `1.7810724`). -/
theorem exp_gamma_le : Real.exp Real.eulerMascheroniConstant ≤ 1.7881 := by
  have h1 := Real.exp_le_exp.mpr gamma_lt.le
  have h2 := Real.exp_bound' (x := 0.581117) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  linarith

/-- `log 150000 ≥ 11.9183905` (truth `11.91839057`). -/
theorem log_r0_ge : 11.9183905 ≤ Real.log 150000 := by
  have h := le_log_series 150000 (-1183 / 8192) 17 12 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 150000 ≤ 11.9183906`. -/
theorem log_r0_le : Real.log 150000 ≤ 11.9183906 := by
  have h := log_le_series 150000 (-1183 / 8192) 17 12 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 11.91839 ≥ 2.47808` (truth `2.4780826`). -/
theorem log_ll_ge : 2.47808 ≤ Real.log 11.91839 := by
  have h := le_log_series 11.91839 0.2551007 4 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 11.9184 ≤ 2.47809` (truth `2.4780834`). -/
theorem log_ll_le : Real.log 11.9184 ≤ 2.47809 := by
  have h := log_le_series 11.9184 0.2551 4 15 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **`F(r) ≤ 3.6544 + 0.15003 log r`** for `r ≥ r₀` (`eq:koop`): `log log r` by its tangent at
`11.9184`, `2.50637/log log r ≤ 2.50637/2.47808`, `e^γ ≤ 1.7881`. -/
theorem bigF_le (r : ℝ) (hr : 150000 ≤ r) : bigF r ≤ 3.6544 + 0.15003 * Real.log r := by
  have hl : 11.9183905 ≤ Real.log r := log_r0_ge.trans (Real.log_le_log (by norm_num) hr)
  have hll : 2.47808 ≤ Real.log (Real.log r) :=
    log_ll_ge.trans (Real.log_le_log (by norm_num) (by linarith))
  have htan : Real.log (Real.log r) ≤ 2.47809 + Real.log r / 11.9184 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < Real.log r)
      (by norm_num : (0 : ℝ) < 11.9184))
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith [log_ll_le]
  have h1 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) ≤
      1.7881 * Real.log (Real.log r) := mul_le_mul_of_nonneg_right exp_gamma_le (by linarith)
  have h2 : 2.50637 / Real.log (Real.log r) ≤ 2.50637 / 2.47808 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hll
  have h3 : 1.7881 * Real.log (Real.log r) ≤ 1.7881 * (2.47809 + Real.log r / 11.9184 - 1) :=
    mul_le_mul_of_nonneg_left htan (by norm_num)
  have h4 : (2.50637 : ℝ) / 2.47808 ≤ 1.011417 := by norm_num
  have h5 : 1.7881 * (2.47809 + Real.log r / 11.9184 - 1) + 1.011417 ≤
      3.6544 + 0.15003 * Real.log r := by
    have : Real.log r / 11.9184 = Real.log r * (1 / 11.9184) := by ring
    rw [this]
    nlinarith
  unfold bigF
  linarith

/-- **`√F(r) ≤ 1.949682 + 0.032156 log r`** for `r ≥ r₀` (AM–GM at `2.3329`). -/
theorem sqrtF_le (r : ℝ) (hr : 150000 ≤ r) :
    Real.sqrt (bigF r) ≤ 1.949682 + 0.032156 * Real.log r := by
  have hl : 11.9183905 ≤ Real.log r := log_r0_ge.trans (Real.log_le_log (by norm_num) hr)
  have hu0 : 0 ≤ 3.6544 + 0.15003 * Real.log r := by linarith
  have h1 := Real.sqrt_le_sqrt (bigF_le r hr)
  have hs := Real.sq_sqrt hu0
  have hs0 := Real.sqrt_nonneg (3.6544 + 0.15003 * Real.log r)
  have h2 : Real.sqrt (3.6544 + 0.15003 * Real.log r) ≤
      (3.6544 + 0.15003 * Real.log r + 2.3329 ^ 2) / (2 * 2.3329) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [sq_nonneg (Real.sqrt (3.6544 + 0.15003 * Real.log r) - 2.3329)]
  have h3 : (3.6544 + 0.15003 * Real.log r + 2.3329 ^ 2) / (2 * 2.3329) ≤
      1.949682 + 0.032156 * Real.log r := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- **`L_r ≤ Q(log r)`** for `r ≥ r₀` (`eq:veror`, `F ≤ 3.6544 + 0.15003ℓ`,
`log 2 ≤ 0.6931471808`). -/
theorem lL_le (r : ℝ) (hr : 150000 ≤ r) : lL r ≤ qA (Real.log r) := by
  have hr0 : 0 < r := by linarith
  have hl : 11.9183905 ≤ Real.log r := log_r0_ge.trans (Real.log_le_log (by norm_num) hr)
  have h2 := Real.log_two_lt_d9
  have h20 := Real.log_two_gt_d9
  have e1 : Real.log (2 ^ ((7 : ℝ) / 4) * r ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log 2 + 13 / 4 * Real.log r := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hr0]
  have e2 : Real.log (2 ^ ((16 : ℝ) / 9) * r ^ ((80 : ℝ) / 9)) =
      16 / 9 * Real.log 2 + 80 / 9 * Real.log r := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hr0]
  unfold lL qA
  rw [e1, e2]
  have hF := bigF_le r hr
  have hm : 0 ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log r + 80 / 9 := by linarith
  have hu : 0 ≤ 3.6544 + 0.15003 * Real.log r := by linarith
  have k1 := mul_le_mul_of_nonneg_right hF hm
  have k2 : (3.6544 + 0.15003 * Real.log r) * (7 / 4 * Real.log 2 + 13 / 4 * Real.log r + 80 / 9)
      ≤ (3.6544 + 0.15003 * Real.log r) *
        (7 / 4 * 0.6931471808 + 13 / 4 * Real.log r + 80 / 9) :=
    mul_le_mul_of_nonneg_left (by linarith) hu
  linarith

/-- `√2 ≥ 1.41421`. -/
theorem sqrt_two_ge : 1.41421 ≤ Real.sqrt 2 := by
  have h := Real.sqrt_le_sqrt (show (1.41421 : ℝ) ^ 2 ≤ 2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num)] at h

/-- **[EnvPt] DISCHARGED**: `g(y,r) ≤ envQ ρ r + f₂(y)` whenever `ρ ≥ 0`, `r ≥ r₀`,
`R_{y,K,φ,2r} ≤ ρ`. -/
theorem envPt : EnvPt := by
  intro ρ y r hρ hr hrk
  have hr0 : 0 < r := by linarith
  have hl : 11.9183905 ≤ Real.log r := log_r0_ge.trans (Real.log_le_log (by norm_num) hr)
  have h2 := Real.log_two_lt_d9
  have h20 := Real.log_two_gt_d9
  have hl2 : Real.log (2 * r) = Real.log 2 + Real.log r :=
    Real.log_mul (by norm_num) hr0.ne'
  have hsF := sqrtF_le r hr
  have hsF0 := Real.sqrt_nonneg (bigF r)
  set sF := Real.sqrt (bigF r)
  set RK := rRK HW.phi y (2 * r)
  -- the numerator
  have hm1 : RK * Real.log (2 * r) + 0.5 ≤ ρ * (0.6931471808 + Real.log r) + 0.5 := by
    have a1 : RK * Real.log (2 * r) ≤ ρ * Real.log (2 * r) :=
      mul_le_mul_of_nonneg_right hrk (by rw [hl2]; linarith)
    have a2 : ρ * Real.log (2 * r) ≤ ρ * (0.6931471808 + Real.log r) :=
      mul_le_mul_of_nonneg_left (by rw [hl2]; linarith) hρ
    linarith
  have hM1 : 0 ≤ ρ * (0.6931471808 + Real.log r) + 0.5 := by positivity
  have hN : (RK * Real.log (2 * r) + 0.5) * sF + 2.5 ≤ pA ρ (Real.log r) := by
    have b1 := mul_le_mul_of_nonneg_right hm1 hsF0
    have b2 := mul_le_mul_of_nonneg_left hsF hM1
    unfold pA
    linarith
  have hpA : 0 ≤ pA ρ (Real.log r) := by
    unfold pA
    have : 0 ≤ 1.949682 + 0.032156 * Real.log r := by linarith
    positivity
  -- the first term
  have hsr := Real.sqrt_pos.mpr hr0
  have hs2 := sqrt_two_ge
  have hT1 : ((RK * Real.log (2 * r) + 0.5) * sF + 2.5) / Real.sqrt (2 * r) ≤
      0.70711 * pA ρ (Real.log r) / Real.sqrt r := by
    rw [Real.sqrt_mul (by norm_num) r, div_le_div_iff₀ (by positivity) hsr]
    have c1 : 1 ≤ 0.70711 * Real.sqrt 2 := by linarith
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 c1) hpA) hsr.le,
      mul_nonneg (sub_nonneg.2 hN) hsr.le]
  -- the second term
  have hT2 : lL r / r ≤ qA (Real.log r) / r := div_le_div_of_nonneg_right (lL_le r hr) hr0.le
  unfold gB envQ f2
  linarith

/-! ## (7) DISCHARGED: `C_{φ,2,K} ∈ [0, 1/9]`, the monotonicity of `R`, `RKMono`, `G0Nonneg` -/

/-- `φ(w) ≤ w²` (`e^{−w²/2} ≤ 1`). -/
theorem phi_le_sq (w : ℝ) : HW.phi w ≤ w ^ 2 := by
  unfold HW.phi
  have h1 : Real.exp (-w ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg w]
  calc w ^ 2 * Real.exp (-w ^ 2 / 2) ≤ w ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg w)
    _ = w ^ 2 := mul_one _

/-- **`C_{φ,2,K} ≥ 0`** for `K ≥ 1`: `−φ(w) log w ≥ 0` on `[1/K, 1]`. -/
theorem cPhi2_nonneg (K : ℝ) (hK : 1 ≤ K) : 0 ≤ cPhi2 HW.phi K := by
  have hK0 : 0 < K := by linarith
  have ha : 0 < 1 / K := one_div_pos.mpr hK0
  unfold cPhi2
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_nonneg (by rw [div_le_one hK0]; exact hK) fun w hw => ?_
  have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
  have hl : Real.log w ≤ 0 := Real.log_nonpos hw0.le hw.2
  have := HW.phi_nonneg w
  nlinarith

/-- **`C_{φ,2,K} ≤ 1/9`** for `K ≥ 1` (`eq:cecidad`): `φ(w) ≤ w²` and
`∫_{1/K}^1 −w² log w dw = 1/9 − (1 + 3 log K)/(9K³)`. -/
theorem cPhi2_le (K : ℝ) (hK : 1 ≤ K) : cPhi2 HW.phi K ≤ 1 / 9 := by
  have hK0 : 0 < K := by linarith
  have ha : 0 < 1 / K := one_div_pos.mpr hK0
  have hab : 1 / K ≤ 1 := by rw [div_le_one hK0]; exact hK
  have hlog : ContinuousOn Real.log (Icc (1 / K) 1) :=
    Real.continuousOn_log.mono fun w hw => (lt_of_lt_of_le ha hw.1).ne'
  have hc1 : ContinuousOn (fun w => -(HW.phi w * Real.log w)) (Icc (1 / K) 1) :=
    (HW.continuous_phi.continuousOn.mul hlog).neg
  have hc2 : ContinuousOn (fun w => -(w ^ 2 * Real.log w)) (Icc (1 / K) 1) :=
    ((continuous_pow 2).continuousOn.mul hlog).neg
  have hmono : ∫ w in (1 / K)..1, -(HW.phi w * Real.log w) ≤
      ∫ w in (1 / K)..1, -(w ^ 2 * Real.log w) := by
    refine intervalIntegral.integral_mono_on hab (hc1.intervalIntegrable_of_Icc hab)
      (hc2.intervalIntegrable_of_Icc hab) fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
    have hl : Real.log w ≤ 0 := Real.log_nonpos hw0.le hw.2
    have hp := phi_le_sq w
    nlinarith
  have hint : ∫ w in (1 / K)..1, -(w ^ 2 * Real.log w) =
      ((1 : ℝ) ^ 3 / 9 - 1 ^ 3 / 3 * Real.log 1) -
        ((1 / K) ^ 3 / 9 - (1 / K) ^ 3 / 3 * Real.log (1 / K)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun w => w ^ 3 / 9 - w ^ 3 / 3 * Real.log w) (fun w hw => ?_)
      (hc2.intervalIntegrable_of_Icc hab)
    rw [uIcc_of_le hab] at hw
    have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
    exact (((hasDerivAt_pow 3 w).div_const 9).sub (((hasDerivAt_pow 3 w).div_const 3).mul
      (Real.hasDerivAt_log hw0.ne'))).congr_deriv (by field_simp; ring)
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlinv : Real.log (1 / K) = -Real.log K := by rw [one_div, Real.log_inv]
  rw [Real.log_one, hlinv] at hint
  have hK3 : 0 < (1 / K) ^ 3 := by positivity
  have hrest : 0 ≤ (1 / K) ^ 3 / 9 - (1 / K) ^ 3 / 3 * -Real.log K := by
    have := mul_nonneg hK3.le hlK
    nlinarith
  unfold cPhi2
  rw [← intervalIntegral.integral_neg]
  linarith

/-- **`R_{z,t}` decreases in `z` and increases in `t`** (`eq:veror`), while
`log(9z^{1/3}/(2.004t)) > 0` at the smaller `z` and larger `t`. -/
theorem rR_mono (z z' t t' : ℝ) (hz : 0 < z) (hzz : z ≤ z') (ht' : 1 / 4 ≤ t') (htt : t' ≤ t)
    (hD : 0 < Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) : rR z' t' ≤ rR z t := by
  have ht0' : 0 < t' := by linarith
  have ht0 : 0 < t := by linarith
  have hz' : 0 < z' := lt_of_lt_of_le hz hzz
  have hD' : Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t)) ≤
      Real.log (9 * z' ^ ((1 : ℝ) / 3) / (2.004 * t')) := by
    refine Real.log_le_log (by positivity) (div_le_div₀ (by positivity) ?_ (by positivity)
      (by linarith))
    have := Real.rpow_le_rpow hz.le hzz (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith
  have h4 : 0 ≤ Real.log (4 * t') := Real.log_nonneg (by linarith)
  have h4' : Real.log (4 * t') ≤ Real.log (4 * t) := Real.log_le_log (by linarith) (by linarith)
  have hq : Real.log (4 * t') / (2 * Real.log (9 * z' ^ ((1 : ℝ) / 3) / (2.004 * t'))) ≤
      Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) :=
    div_le_div₀ (by linarith) h4' (by linarith) (by linarith)
  have hq0 : 0 ≤ Real.log (4 * t') / (2 * Real.log (9 * z' ^ ((1 : ℝ) / 3) / (2.004 * t'))) :=
    div_nonneg h4 (by linarith)
  unfold rR
  set q' := Real.log (4 * t') / (2 * Real.log (9 * z' ^ ((1 : ℝ) / 3) / (2.004 * t')))
  set q := Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t)))
  have hl := Real.log_le_log (by linarith) (by linarith : 1 + q' ≤ 1 + q)
  linarith

/-- **`R_{z,t} ≥ 0.41415`** while `log(9z^{1/3}/(2.004t)) > 0`. -/
theorem rR_ge (z t : ℝ) (ht : 1 / 4 ≤ t) (hD : 0 < Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) :
    0.41415 ≤ rR z t := by
  have h4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hq0 : 0 ≤ Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) :=
    div_nonneg h4 (by linarith)
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤
    1 + Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))))
  unfold rR
  linarith

/-- `log y ≥ 57.53` for `y ≥ 10²⁵` (`10²⁵ ≥ 2⁸³`), so `K = (log y)/2 ≥ 28`. -/
theorem kK_ge (y : ℝ) (hy : 10 ^ 25 ≤ y) : 28 ≤ kK y := by
  have h := Real.log_le_log (by norm_num) (le_trans (by norm_num : (2 : ℝ) ^ 83 ≤ 10 ^ 25) hy)
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  unfold kK
  linarith

/-- `log K ≥ 2.77` for `K ≥ 28` (`28 ≥ 2⁴`). -/
theorem logK_ge (y : ℝ) (hy : 10 ^ 25 ≤ y) : 2.77 ≤ Real.log (kK y) := by
  have h := Real.log_le_log (by norm_num) (le_trans (by norm_num : (2 : ℝ) ^ 4 ≤ 28) (kK_ge y hy))
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

/-- **`y/K(y)` increases** on `y ≥ 10²⁵` (`log y/y` decreases). -/
theorem yK_mono (y y' : ℝ) (hy : 10 ^ 25 ≤ y) (h : y ≤ y') : y / kK y ≤ y' / kK y' := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hy1 : 0 < y' := lt_of_lt_of_le hy0 h
  have hK := kK_ge y hy
  have hK' := kK_ge y' (hy.trans h)
  have hd := logdiv_anti y y' hy0 (log_ge_one_y y hy) h
  unfold kK at hK hK' ⊢
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  rw [div_le_div_iff₀ hy1 hy0] at hd
  nlinarith

/-- **The mixing weight** `c(y) = C_{φ,2,K}/|φ|₁/log K` lies in `[0, (1/9)/(√(π/2) log K_a)]` for
`y ≥ y_a ≥ 10²⁵`, and that ceiling is `≤ 1`. -/
theorem cmix_le (ya y : ℝ) (hya : 10 ^ 25 ≤ ya) (hy : ya ≤ y) :
    0 ≤ cPhi2 HW.phi (kK y) / MajSp.l1 HW.phi / Real.log (kK y) ∧
      cPhi2 HW.phi (kK y) / MajSp.l1 HW.phi / Real.log (kK y) ≤
        1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) ∧
      1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) ≤ 1 := by
  have hy25 : 10 ^ 25 ≤ y := hya.trans hy
  have hK := kK_ge y hy25
  have hLa := logK_ge ya hya
  have hLy : Real.log (kK ya) ≤ Real.log (kK y) := by
    apply Real.log_le_log (by linarith [kK_ge ya hya])
    unfold kK
    have := Real.log_le_log (lt_of_lt_of_le (by norm_num) hya) hy
    linarith
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  have hs := MajSp.sqrt_pi_half.1
  have hc0 := cPhi2_nonneg (kK y) (by linarith)
  have hc1 := cPhi2_le (kK y) (by linarith)
  rw [hl1]
  have hs0 : 0 < Real.sqrt (Real.pi / 2) := by linarith
  have hLa0 : 0 < Real.log (kK ya) := by linarith
  refine ⟨div_nonneg (div_nonneg hc0 hs0.le) (by linarith), ?_, ?_⟩
  · calc cPhi2 HW.phi (kK y) / Real.sqrt (Real.pi / 2) / Real.log (kK y)
        ≤ 1 / 9 / Real.sqrt (Real.pi / 2) / Real.log (kK y) :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hc1 hs0.le) (by linarith)
      _ ≤ 1 / 9 / Real.sqrt (Real.pi / 2) / Real.log (kK ya) :=
          div_le_div_of_nonneg_left (by positivity) hLa0 hLy
      _ = 1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) := by rw [div_div]
  · rw [div_le_one (by positivity)]
    nlinarith

/-- **The preconditions of every `RKCeil` instance**: `(y_a/K_a)^{1/3} ≥ 2·10⁶` for
`y_a ≥ 10²⁵` (`log 10²⁵ = 25 log 10 ≤ 225`, so `y_a/K_a ≥ 10²⁵/112.5 ≥ 8·10¹⁸`). -/
theorem cube_ge (ya : ℝ) (hya : 10 ^ 25 ≤ ya) : 2000000 ≤ (ya / kK ya) ^ ((1 : ℝ) / 3) := by
  have h10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    linarith
  have hK : kK (10 ^ 25) ≤ 112.5 := by
    unfold kK
    rw [Real.log_pow]
    push_cast
    linarith
  have hK0 := kK_ge (10 ^ 25) le_rfl
  have hz : (8 : ℝ) * 10 ^ 18 ≤ ya / kK ya := by
    refine le_trans ?_ (yK_mono (10 ^ 25) ya le_rfl hya)
    rw [le_div_iff₀ (by linarith)]
    calc (8 : ℝ) * 10 ^ 18 * kK (10 ^ 25) ≤ 8 * 10 ^ 18 * 112.5 :=
          mul_le_mul_of_nonneg_left hK (by norm_num)
      _ ≤ 10 ^ 25 := by norm_num
  have h := le_rpow_of_pow (ya / kK ya) 2000000 1 3 (by norm_num)
    (le_trans (by norm_num) hz) (by norm_num) (by rw [pow_one]; linarith)
  have e : ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 1 / 3 := by norm_num
  rwa [e] at h

/-- `RKCeil`'s first half, for every instance used (`2.004 t_b < 1.8·10⁷`). -/
theorem pre_ok (ya tb : ℝ) (hya : 10 ^ 25 ≤ ya) (htb : 2.004 * tb < 18000000) :
    2.004 * tb < 9 * (ya / kK ya) ^ ((1 : ℝ) / 3) := by
  have := cube_ge ya hya
  linarith

/-- **[RKMono] DISCHARGED**: the block ceiling `rKB y_a t_b` bounds `R_{y,K,φ,t}` for every
`y ≥ y_a`, `1 ≤ t ≤ t_b`. `R_{y,t} ≤ R_{y_a,t_b}`, `R_{y/K,t} ≤ R_{y_a/K_a,t_b}` (`y/K` increases),
`R_{y_a,t_b} ≤ R_{y_a/K_a,t_b}`, and the mixing weight `c ∈ [0, c_max(y_a)] ⊆ [0, 1]`. -/
theorem rkMono : RKMono := by
  rintro ya tb ρ hya htb ⟨hpre, hceil⟩ y t hy ht1 htb'
  have hy25 : 10 ^ 25 ≤ y := hya.trans hy
  have hya0 : 0 < ya := lt_of_lt_of_le (by norm_num) hya
  have hKa := kK_ge ya hya
  have hza : ya / kK ya ≤ y / kK y := yK_mono ya y hya hy
  have hza0 : 0 < ya / kK ya := div_pos hya0 (by linarith)
  have hzle : ya / kK ya ≤ ya := div_le_self hya0.le (by linarith)
  have hDB : 0 < Real.log (9 * (ya / kK ya) ^ ((1 : ℝ) / 3) / (2.004 * tb)) :=
    Real.log_pos (by rw [one_lt_div (by positivity)]; exact hpre)
  have hDA : 0 < Real.log (9 * ya ^ ((1 : ℝ) / 3) / (2.004 * tb)) := by
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    have := Real.rpow_le_rpow hza0.le hzle (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith
  have hR1 : rR y t ≤ rR ya tb := rR_mono ya y tb t hya0 hy (by linarith) htb' hDA
  have hR2 : rR (y / kK y) t ≤ rR (ya / kK ya) tb :=
    rR_mono _ _ tb t hza0 hza (by linarith) htb' hDB
  have hAB : rR ya tb ≤ rR (ya / kK ya) tb := rR_mono _ _ tb tb hza0 hzle (by linarith) le_rfl hDB
  obtain ⟨hc0, hc1, hcm⟩ := cmix_le ya y hya hy
  unfold rRK
  unfold rKB at hceil
  set c := cPhi2 HW.phi (kK y) / MajSp.l1 HW.phi / Real.log (kK y)
  set cm := 1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya))
  nlinarith [mul_nonneg (sub_nonneg.2 (hc1.trans hcm)) (sub_nonneg.2 hR1),
    mul_nonneg hc0 (sub_nonneg.2 hR2), mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hAB)]

/-- **[G0Nonneg] DISCHARGED**: `g(y, r₀) ≥ 0` for `y ≥ 10²⁵`. `R_{y,2r₀}, R_{y/K,2r₀} ≥ 0.41415`
(both inner logarithms are positive: `cube_ge`), the mixing weight is in `[0, 1]`, so every term
of `g` is nonnegative (`F(r₀) > 0` since `log log r₀ > 0`). -/
theorem g0Nonneg : G0Nonneg := by
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hK := kK_ge y hy
  have hz0 : 0 < y / kK y := div_pos hy0 (by linarith)
  have hzle : y / kK y ≤ y := div_le_self hy0.le (by linarith)
  have hpre := pre_ok y 300000 hy (by norm_num)
  have hD2 : 0 < Real.log (9 * (y / kK y) ^ ((1 : ℝ) / 3) / (2.004 * 300000)) :=
    Real.log_pos (by rw [one_lt_div (by positivity)]; exact hpre)
  have hD1 : 0 < Real.log (9 * y ^ ((1 : ℝ) / 3) / (2.004 * 300000)) := by
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    have := Real.rpow_le_rpow hz0.le hzle (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith
  have hR1 := rR_ge y 300000 (by norm_num) hD1
  have hR2 := rR_ge (y / kK y) 300000 (by norm_num) hD2
  obtain ⟨hc0, hc1, hcm⟩ := cmix_le y y hy le_rfl
  have hRK : 0 ≤ rRK HW.phi y (2 * 150000) := by
    rw [show (2 : ℝ) * 150000 = 300000 by norm_num]
    unfold rRK
    set c := cPhi2 HW.phi (kK y) / MajSp.l1 HW.phi / Real.log (kK y)
    nlinarith [mul_nonneg (sub_nonneg.2 (hc1.trans hcm)) (by linarith : (0 : ℝ) ≤ rR y 300000),
      mul_nonneg hc0 (by linarith : (0 : ℝ) ≤ rR (y / kK y) 300000)]
  have hl0 := log_r0_ge
  have hll : 2.47808 ≤ Real.log (Real.log 150000) :=
    log_ll_ge.trans (Real.log_le_log (by norm_num) (by linarith))
  have hF : 0 ≤ bigF 150000 := by
    unfold bigF
    have := Real.exp_pos Real.eulerMascheroniConstant
    have : 0 ≤ 2.50637 / Real.log (Real.log 150000) := div_nonneg (by norm_num) (by linarith)
    have : 0 ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 150000) :=
      mul_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  have hL : 0 ≤ lL 150000 := by
    have e1 : Real.log (2 ^ ((7 : ℝ) / 4) * (150000 : ℝ) ^ ((13 : ℝ) / 4)) =
        7 / 4 * Real.log 2 + 13 / 4 * Real.log 150000 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
        Real.log_rpow (by norm_num)]
    have e2 : Real.log (2 ^ ((16 : ℝ) / 9) * (150000 : ℝ) ^ ((80 : ℝ) / 9)) =
        16 / 9 * Real.log 2 + 80 / 9 * Real.log 150000 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
        Real.log_rpow (by norm_num)]
    have h2 := Real.log_two_gt_d9
    unfold lL
    rw [e1, e2]
    have : 0 ≤ bigF 150000 * (7 / 4 * Real.log 2 + 13 / 4 * Real.log 150000 + 80 / 9) :=
      mul_nonneg hF (by linarith)
    linarith
  have hf2 := f2_nonneg y (by linarith)
  have hl3 : 0 ≤ Real.log (2 * 150000) := Real.log_nonneg (by norm_num)
  unfold f2 at hf2
  unfold gB
  have h1 : 0 ≤ ((rRK HW.phi y (2 * 150000) * Real.log (2 * 150000) + 0.5) *
      Real.sqrt (bigF 150000) + 2.5) / Real.sqrt (2 * 150000) := by
    have := mul_nonneg hRK hl3
    have := Real.sqrt_nonneg (bigF 150000)
    positivity
  have h2 : 0 ≤ lL 150000 / 150000 := by positivity
  linarith

/-! ## (8) THE LEVEL-2 COMPOSITION -/

/-- **`MNumAt 8.36 0.785` from the level-2 sub-links** (`EnvDeriv` and `F2Anti` are DISCHARGED
above and supplied here). Application only: `mnumAt_of_links` with `G0Env`, `T1Num`, `IGBlk`,
`IGTail` supplied by `g0Env_of`, `t1Num_of'`, `igBlk_of`, `igTail_of`. The ceilings `t_b` are
`2r₀ = 300000`, `2R` for the blocks (`R = 2.34·10⁶, 3.22·10⁶, 3.87·10⁶`), and `2r₁^{hi}` for `t1`
(`r₁^{hi} = 1740600, 2333100, 3216400, 3869400`). -/
theorem mnumAt_of_sublinks (g0 : G0Nonneg) (rkm : RKMono) (env : EnvPt) (ta : T1Anti)
    (rkt : RKTail (2 * 10 ^ 26) 0.72)
    (c01 : RKCeil (10 ^ 25) 300000 0.5845) (c02 : RKCeil (3 * 10 ^ 25) 300000 0.579)
    (c03 : RKCeil (10 ^ 26) 300000 0.5735) (c04 : RKCeil (2 * 10 ^ 26) 300000 0.5705)
    (c11 : RKCeil (10 ^ 25) 4680000 0.672) (c12 : RKCeil (3 * 10 ^ 25) 6440000 0.674)
    (c13 : RKCeil (10 ^ 26) 7740000 0.669)
    (c21 : RKCeil (10 ^ 25) 3481200 0.66) (c22 : RKCeil (3 * 10 ^ 25) 4666200 0.661)
    (c23 : RKCeil (10 ^ 26) 6432800 0.6615) (c24 : RKCeil (2 * 10 ^ 26) 7738800 0.662)
    (g1 : G0Num (10 ^ 25) 0.5845 0.0412) (g2 : G0Num (3 * 10 ^ 25) 0.579 0.0409)
    (g3 : G0Num (10 ^ 26) 0.5735 0.0406) (g4 : G0Num (2 * 10 ^ 26) 0.5705 0.0404)
    (s1 : R1Le (10 ^ 25) 1740600) (s2 : R1Le (3 * 10 ^ 25) 2333100)
    (s3 : R1Le (10 ^ 26) 3216400) (s4 : R1Le (2 * 10 ^ 26) 3869400)
    (u1 : T1EnvNum (49 * 10 ^ 25) 0.66 0.2865) (u2 : T1EnvNum (147 * 10 ^ 25) 0.661 0.2565)
    (u3 : T1EnvNum (49 * 10 ^ 26) 0.6615 0.227) (u4 : T1EnvNum (98 * 10 ^ 26) 0.662 0.2115)
    (b1 : R1Le (3 * 10 ^ 25) 2340000) (b2 : R1Le (10 ^ 26) 3220000)
    (b3 : R1Le (2 * 10 ^ 26) 3870000)
    (i1 : IBlkNum (10 ^ 25) 0.672 2340000 0.074) (i2 : IBlkNum (3 * 10 ^ 25) 0.674 3220000 0.0785)
    (i3 : IBlkNum (10 ^ 26) 0.669 3870000 0.08)
    (ft : F2Tail (2 * 10 ^ 26) 0.0039) (it : ITailNum 0.72 0.0039 0.115) :
    MNumAt 8.36 0.785 := by
  have rk : ∀ ya tb ρ tb' : ℝ, 10 ^ 25 ≤ ya → tb' = tb → 1 ≤ tb → RKCeil ya tb ρ →
      RKBnd ya tb' ρ := fun ya tb ρ tb' hya e htb hc => e ▸ rkm ya tb ρ hya htb hc
  refine mnumAt_of_links g0 ?_ ?_ ?_ ?_ ta ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact g0Env_of _ _ _ (by norm_num) le_rfl (rk _ _ _ _ le_rfl rfl (by norm_num) c01) env
      f2Anti g1
  · exact g0Env_of _ _ _ (by norm_num) (by norm_num) (rk _ _ _ _ (by norm_num) rfl (by norm_num)
      c02) env f2Anti g2
  · exact g0Env_of _ _ _ (by norm_num) (by norm_num) (rk _ _ _ _ (by norm_num) rfl (by norm_num)
      c03) env f2Anti g3
  · exact g0Env_of _ _ _ (by norm_num) (by norm_num) (rk _ _ _ _ (by norm_num) rfl (by norm_num)
      c04) env f2Anti g4
  · exact t1Num_of' _ _ _ _ _ (by norm_num) le_rfl (by norm_num)
      (rk _ _ _ _ le_rfl (by norm_num) (by norm_num) c21) s1 env u1
  · exact t1Num_of' _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (rk _ _ _ _ (by norm_num) (by norm_num) (by norm_num) c22) s2 env u2
  · exact t1Num_of' _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (rk _ _ _ _ (by norm_num) (by norm_num) (by norm_num) c23) s3 env u3
  · exact t1Num_of' _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (rk _ _ _ _ (by norm_num) (by norm_num) (by norm_num) c24) s4 env u4
  · exact igBlk_of _ _ _ _ _ (by norm_num) le_rfl
      (rk _ _ _ _ le_rfl (by norm_num) (by norm_num) c11) b1 env f2Anti i1
  · exact igBlk_of _ _ _ _ _ (by norm_num) (by norm_num)
      (rk _ _ _ _ (by norm_num) (by norm_num) (by norm_num) c12) b2 env f2Anti i2
  · exact igBlk_of _ _ _ _ _ (by norm_num) (by norm_num)
      (rk _ _ _ _ (by norm_num) (by norm_num) (by norm_num) c13) b3 env f2Anti i3
  · exact igTail_of _ _ _ _ (by norm_num) (by norm_num) rkt env ft it

/-- `RKCeil` from its numeric half (`pre_ok` supplies the other). -/
theorem rkCeil_of (ya tb ρ : ℝ) (hya : 10 ^ 25 ≤ ya) (htb : 2.004 * tb < 18000000)
    (h : RKNum ya tb ρ) : RKCeil ya tb ρ :=
  ⟨pre_ok ya tb hya htb, h⟩

/-- **`MNumAt 8.36 0.785` from the links still OPEN**: `mnumAt_of_sublinks` with `G0Nonneg`,
`RKMono`, `EnvPt`, the seven `R1Le` and every `RKCeil` precondition supplied by the proofs above.
Application only. -/
theorem mnumAt_of_open (ta : T1Anti) (rkt : RKTail (2 * 10 ^ 26) 0.72)
    (c01 : RKNum (10 ^ 25) 300000 0.5845) (c02 : RKNum (3 * 10 ^ 25) 300000 0.579)
    (c03 : RKNum (10 ^ 26) 300000 0.5735) (c04 : RKNum (2 * 10 ^ 26) 300000 0.5705)
    (c11 : RKNum (10 ^ 25) 4680000 0.672) (c12 : RKNum (3 * 10 ^ 25) 6440000 0.674)
    (c13 : RKNum (10 ^ 26) 7740000 0.669)
    (c21 : RKNum (10 ^ 25) 3481200 0.66) (c22 : RKNum (3 * 10 ^ 25) 4666200 0.661)
    (c23 : RKNum (10 ^ 26) 6432800 0.6615) (c24 : RKNum (2 * 10 ^ 26) 7738800 0.662)
    (g1 : G0Num (10 ^ 25) 0.5845 0.0412) (g2 : G0Num (3 * 10 ^ 25) 0.579 0.0409)
    (g3 : G0Num (10 ^ 26) 0.5735 0.0406) (g4 : G0Num (2 * 10 ^ 26) 0.5705 0.0404)
    (u1 : T1EnvNum (49 * 10 ^ 25) 0.66 0.2865) (u2 : T1EnvNum (147 * 10 ^ 25) 0.661 0.2565)
    (u3 : T1EnvNum (49 * 10 ^ 26) 0.6615 0.227) (u4 : T1EnvNum (98 * 10 ^ 26) 0.662 0.2115)
    (i1 : IBlkNum (10 ^ 25) 0.672 2340000 0.074) (i2 : IBlkNum (3 * 10 ^ 25) 0.674 3220000 0.0785)
    (i3 : IBlkNum (10 ^ 26) 0.669 3870000 0.08)
    (ft : F2Tail (2 * 10 ^ 26) 0.0039) (it : ITailNum 0.72 0.0039 0.115) :
    MNumAt 8.36 0.785 :=
  mnumAt_of_sublinks g0Nonneg rkMono envPt ta rkt
    (rkCeil_of _ _ _ le_rfl (by norm_num) c01) (rkCeil_of _ _ _ (by norm_num) (by norm_num) c02)
    (rkCeil_of _ _ _ (by norm_num) (by norm_num) c03)
    (rkCeil_of _ _ _ (by norm_num) (by norm_num) c04)
    (rkCeil_of _ _ _ le_rfl (by norm_num) c11) (rkCeil_of _ _ _ (by norm_num) (by norm_num) c12)
    (rkCeil_of _ _ _ (by norm_num) (by norm_num) c13)
    (rkCeil_of _ _ _ le_rfl (by norm_num) c21) (rkCeil_of _ _ _ (by norm_num) (by norm_num) c22)
    (rkCeil_of _ _ _ (by norm_num) (by norm_num) c23)
    (rkCeil_of _ _ _ (by norm_num) (by norm_num) c24)
    g1 g2 g3 g4 r1Le_1 r1Le_2 r1Le_3 r1Le_4 u1 u2 u3 u4 r1Le_b1 r1Le_b2 r1Le_b3 i1 i2 i3 ft it

/-- **`MinW.MNumW HW.phi 0.785` from the links still OPEN.** Application only. -/
theorem mnumW_of_open (ta : T1Anti) (rkt : RKTail (2 * 10 ^ 26) 0.72)
    (c01 : RKNum (10 ^ 25) 300000 0.5845) (c02 : RKNum (3 * 10 ^ 25) 300000 0.579)
    (c03 : RKNum (10 ^ 26) 300000 0.5735) (c04 : RKNum (2 * 10 ^ 26) 300000 0.5705)
    (c11 : RKNum (10 ^ 25) 4680000 0.672) (c12 : RKNum (3 * 10 ^ 25) 6440000 0.674)
    (c13 : RKNum (10 ^ 26) 7740000 0.669)
    (c21 : RKNum (10 ^ 25) 3481200 0.66) (c22 : RKNum (3 * 10 ^ 25) 4666200 0.661)
    (c23 : RKNum (10 ^ 26) 6432800 0.6615) (c24 : RKNum (2 * 10 ^ 26) 7738800 0.662)
    (g1 : G0Num (10 ^ 25) 0.5845 0.0412) (g2 : G0Num (3 * 10 ^ 25) 0.579 0.0409)
    (g3 : G0Num (10 ^ 26) 0.5735 0.0406) (g4 : G0Num (2 * 10 ^ 26) 0.5705 0.0404)
    (u1 : T1EnvNum (49 * 10 ^ 25) 0.66 0.2865) (u2 : T1EnvNum (147 * 10 ^ 25) 0.661 0.2565)
    (u3 : T1EnvNum (49 * 10 ^ 26) 0.6615 0.227) (u4 : T1EnvNum (98 * 10 ^ 26) 0.662 0.2115)
    (i1 : IBlkNum (10 ^ 25) 0.672 2340000 0.074) (i2 : IBlkNum (3 * 10 ^ 25) 0.674 3220000 0.0785)
    (i3 : IBlkNum (10 ^ 26) 0.669 3870000 0.08)
    (ft : F2Tail (2 * 10 ^ 26) 0.0039) (it : ITailNum 0.72 0.0039 0.115) :
    MinW.MNumW HW.phi 0.785 :=
  mnumW_of_at (mnumAt_of_open ta rkt c01 c02 c03 c04 c11 c12 c13 c21 c22 c23 c24 g1 g2 g3 g4
    u1 u2 u3 u4 i1 i2 i3 ft it)

/-! ## (9) Certified numerics: the generic bounds -/

/-- `S(ℓ) = P + 2P′ + 4P″`, the `√r`-numerator of `PhiQ`. -/
noncomputable def sP (ρ l : ℝ) : ℝ := pA ρ l + 2 * dpA ρ l + 4 * ddpA ρ

/-- `T(ℓ) = Q + Q′ + Q″`, the `r`-numerator of `PhiQ`. -/
noncomputable def tQ (l : ℝ) : ℝ := qA l + dqA l + ddqA

/-- `PhiQ` through `sP`, `tQ`. -/
theorem PhiQ_eq_sP (ρ r : ℝ) :
    PhiQ ρ r = -(2 * 0.70711) * sP ρ (Real.log r) / Real.sqrt r - tQ (Real.log r) / r := rfl

/-- `P` is nonnegative and increasing on `ℓ ≥ 0` (for `ρ ≥ 0`). -/
theorem pA_mono (ρ l l' : ℝ) (hρ : 0 ≤ ρ) (hl : 0 ≤ l) (h : l ≤ l') :
    0 ≤ pA ρ l ∧ pA ρ l ≤ pA ρ l' := by
  have a0 : 0 ≤ ρ * (0.6931471808 + l) + 0.5 := by
    have := mul_nonneg hρ (by linarith : (0 : ℝ) ≤ 0.6931471808 + l)
    linarith
  have a1 : ρ * (0.6931471808 + l) + 0.5 ≤ ρ * (0.6931471808 + l') + 0.5 := by
    have := mul_le_mul_of_nonneg_left (by linarith : 0.6931471808 + l ≤ 0.6931471808 + l') hρ
    linarith
  have b0 : 0 ≤ 1.949682 + 0.032156 * l := by linarith
  have b1 : 1.949682 + 0.032156 * l ≤ 1.949682 + 0.032156 * l' := by linarith
  unfold pA
  constructor
  · have := mul_nonneg a0 b0
    linarith
  · have := mul_le_mul a1 b1 b0 (a0.trans a1)
    linarith

/-- `Q` is nonnegative and increasing on `ℓ ≥ 0`. -/
theorem qA_mono (l l' : ℝ) (hl : 0 ≤ l) (h : l ≤ l') : 0 ≤ qA l ∧ qA l ≤ qA l' := by
  have a0 : 0 ≤ 3.6544 + 0.15003 * l := by linarith
  have a1 : 3.6544 + 0.15003 * l ≤ 3.6544 + 0.15003 * l' := by linarith
  have b0 : 0 ≤ 7 / 4 * 0.6931471808 + 13 / 4 * l + 80 / 9 := by linarith
  have b1 : 7 / 4 * 0.6931471808 + 13 / 4 * l + 80 / 9 ≤
      7 / 4 * 0.6931471808 + 13 / 4 * l' + 80 / 9 := by linarith
  unfold qA
  constructor
  · have := mul_nonneg a0 b0
    linarith
  · have := mul_le_mul a1 b1 b0 (a0.trans a1)
    linarith

/-- `S` is nonnegative and increasing on `ℓ ≥ 0`. -/
theorem sP_mono (ρ l l' : ℝ) (hρ : 0 ≤ ρ) (hl : 0 ≤ l) (h : l ≤ l') :
    0 ≤ sP ρ l ∧ sP ρ l ≤ sP ρ l' := by
  obtain ⟨p0, p1⟩ := pA_mono ρ l l' hρ hl h
  have d0 : 0 ≤ dpA ρ l := by
    unfold dpA
    have := mul_nonneg hρ (by linarith : (0 : ℝ) ≤ 1.949682 + 0.032156 * l)
    have := mul_nonneg hρ (by linarith : (0 : ℝ) ≤ 0.6931471808 + l)
    nlinarith
  have d1 : dpA ρ l ≤ dpA ρ l' := by
    unfold dpA
    nlinarith [mul_nonneg hρ (sub_nonneg.2 h)]
  have e0 : 0 ≤ ddpA ρ := by
    unfold ddpA
    positivity
  unfold sP
  constructor <;> linarith

/-- `T` is nonnegative and increasing on `ℓ ≥ 0`. -/
theorem tQ_mono (l l' : ℝ) (hl : 0 ≤ l) (h : l ≤ l') : 0 ≤ tQ l ∧ tQ l ≤ tQ l' := by
  obtain ⟨q0, q1⟩ := qA_mono l l' hl h
  have d0 : 0 ≤ dqA l := by
    unfold dqA
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 3.6544 + 0.15003 * l)
      (by norm_num : (0 : ℝ) ≤ 13 / 4)
    nlinarith
  have d1 : dqA l ≤ dqA l' := by
    unfold dqA
    nlinarith
  have e0 : 0 ≤ ddqA := by
    unfold ddqA
    norm_num
  unfold tQ
  constructor <;> linarith

/-- **`envQ` from above** by `log r ≤ ℓ_u`, `√r ≥ s`, `r ≥ r_l`. -/
theorem envQ_le (ρ r lu s rl : ℝ) (hρ : 0 ≤ ρ) (hr : 1 ≤ r) (hl : Real.log r ≤ lu)
    (hs : 0 < s) (hsr : s ≤ Real.sqrt r) (hrl : 0 < rl) (hrr : rl ≤ r) :
    envQ ρ r ≤ 0.70711 * pA ρ lu / s + qA lu / rl := by
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg hr
  obtain ⟨p0, p1⟩ := pA_mono ρ _ _ hρ hl0 hl
  obtain ⟨q0, q1⟩ := qA_mono _ _ hl0 hl
  unfold envQ
  have h1 : 0.70711 * pA ρ (Real.log r) / Real.sqrt r ≤ 0.70711 * pA ρ lu / s :=
    div_le_div₀ (by linarith) (by linarith) hs hsr
  have h2 : qA (Real.log r) / r ≤ qA lu / rl := div_le_div₀ (by linarith) q1 hrl hrr
  linarith

/-- **`−PhiQ ρ r` from above** by `log r ≤ ℓ_u`, `√r ≥ s`. -/
theorem negPhiQ_le (ρ r lu s : ℝ) (hρ : 0 ≤ ρ) (hr : 1 ≤ r) (hl : Real.log r ≤ lu)
    (hs : 0 < s) (hsr : s ≤ Real.sqrt r) :
    -PhiQ ρ r ≤ 2 * 0.70711 * sP ρ lu / s + tQ lu / r := by
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg hr
  obtain ⟨p0, p1⟩ := sP_mono ρ _ _ hρ hl0 hl
  obtain ⟨q0, q1⟩ := tQ_mono _ _ hl0 hl
  rw [PhiQ_eq_sP]
  have h1 : 2 * 0.70711 * sP ρ (Real.log r) / Real.sqrt r ≤ 2 * 0.70711 * sP ρ lu / s :=
    div_le_div₀ (by linarith) (by linarith) hs hsr
  have h2 : tQ (Real.log r) / r ≤ tQ lu / r :=
    div_le_div_of_nonneg_right q1 (by linarith)
  have e : -(-(2 * 0.70711) * sP ρ (Real.log r) / Real.sqrt r - tQ (Real.log r) / r) =
      2 * 0.70711 * sP ρ (Real.log r) / Real.sqrt r + tQ (Real.log r) / r := by ring
  rw [e]
  linarith

/-- **`PhiQ ρ r` from above** by `0 ≤ ℓ_l ≤ log r`, `√r ≤ s_h`. -/
theorem PhiQ_le (ρ r ll sh : ℝ) (hρ : 0 ≤ ρ) (hr : 1 ≤ r) (hll : 0 ≤ ll)
    (hl : ll ≤ Real.log r) (hsh : Real.sqrt r ≤ sh) :
    PhiQ ρ r ≤ -(2 * 0.70711) * sP ρ ll / sh - tQ ll / r := by
  obtain ⟨p0, p1⟩ := sP_mono ρ _ _ hρ hll hl
  obtain ⟨q0, q1⟩ := tQ_mono _ _ hll hl
  have hsr := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < r)
  rw [PhiQ_eq_sP]
  have h1 : 2 * 0.70711 * sP ρ ll / sh ≤ 2 * 0.70711 * sP ρ (Real.log r) / Real.sqrt r :=
    div_le_div₀ (by linarith) (by linarith) hsr hsh
  have h2 : tQ ll / r ≤ tQ (Real.log r) / r := div_le_div_of_nonneg_right q1 (by linarith)
  have e1 : -(2 * 0.70711) * sP ρ (Real.log r) / Real.sqrt r =
      -(2 * 0.70711 * sP ρ (Real.log r) / Real.sqrt r) := by ring
  have e2 : -(2 * 0.70711) * sP ρ ll / sh = -(2 * 0.70711 * sP ρ ll / sh) := by ring
  rw [e1, e2]
  linarith

/-- **`f₂(y) ≤ 3.2q`** from `log y ≤ L_u` and `(L_u/2)/y ≤ q⁶`. -/
theorem f2_le (y Lu q : ℝ) (hy : 1 ≤ y) (hL : Real.log y ≤ Lu) (hq : 0 ≤ q)
    (h : Lu / 2 / y ≤ q ^ 6) : f2 y ≤ 3.2 * q := by
  have hy0 : 0 < y := by linarith
  have hK0 : 0 ≤ kK y / y := by
    unfold kK
    have := Real.log_nonneg hy
    positivity
  have hKy : kK y / y ≤ q ^ 6 := by
    refine le_trans ?_ h
    unfold kK
    exact div_le_div_of_nonneg_right (by linarith) hy0.le
  have h1 := rpow_le_of_pow (kK y / y) q 1 6 (by norm_num) hK0 hq (by rw [pow_one]; exact hKy)
  have e : ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 6 := by norm_num
  rw [e] at h1
  rw [f2_eq y hy]
  linarith

/-- **`coefC(x)` from above** by `log x ≤ L_u` (its numerator `−2.14938 + (8/15) log 49 < 0`). -/
theorem coefC_le (x Lu : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hL : Real.log x ≤ Lu) :
    coefC x ≤ 7 / 15 + (-2.14938 + 8 / 15 * 3.8955) / (Lu + 2 * 0.6294) := by
  have hL0 := LW.log_ge_of x hx
  have h49 := LW.log_49_le
  unfold coefC
  have hd : 0 < Real.log x + 2 * 0.6294 := by linarith
  have hd' : 0 < Lu + 2 * 0.6294 := by linarith
  have h1 : (-2.14938 + 8 / 15 * Real.log 49) / (Real.log x + 2 * 0.6294) ≤
      (-2.14938 + 8 / 15 * 3.8955) / (Real.log x + 2 * 0.6294) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have h2 : (-2.14938 + 8 / 15 * 3.8955) / (Real.log x + 2 * 0.6294) ≤
      (-2.14938 + 8 / 15 * 3.8955) / (Lu + 2 * 0.6294) := by
    rw [div_le_div_iff₀ hd hd']
    nlinarith
  linarith

/-- `r₁(y) ≥ r_l` from `(8r_l/3)¹⁵ ≤ y⁴`. -/
theorem r1_ge_of (y rl : ℝ) (hy : 0 ≤ y) (hrl : 0 ≤ rl) (h : (8 * rl / 3) ^ 15 ≤ y ^ 4) :
    rl ≤ r1y y := by
  have h1 := le_rpow_of_pow y (8 * rl / 3) 4 15 (by norm_num) hy (by positivity) h
  have e : ((4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ) = 4 / 15 := by norm_num
  rw [e] at h1
  unfold r1y
  linarith

/-- `√r ≥ s` from `s² ≤ r`. -/
theorem sqrt_ge_of (r s : ℝ) (hs : 0 ≤ s) (h : s ^ 2 ≤ r) : s ≤ Real.sqrt r := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hs] at this

/-- `√r ≤ s` from `r ≤ s²`. -/
theorem sqrt_le_of (r s : ℝ) (hs : 0 ≤ s) (h : r ≤ s ^ 2) : Real.sqrt r ≤ s := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hs] at this

/-- `log(9z^{1/3}/(2.004t)) = log 9 + (log z)/3 − log(2.004t)`. -/
theorem logD_eq (z t : ℝ) (hz : 0 < z) (ht : 0 < t) :
    Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t)) =
      Real.log 9 + Real.log z / 3 - Real.log (2.004 * t) := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow hz]
  ring

/-- **`R_{z,t}` from above** by `log 4t ≤ A₁`, `log(9z^{1/3}/(2.004t)) ≥ D₁ > 0` and
`log(1 + A₁/(2D₁)) ≤ U`. -/
theorem rR_le (z t A1 D1 U : ℝ) (ht : 1 / 4 ≤ t) (hA : Real.log (4 * t) ≤ A1) (hD1 : 0 < D1)
    (hD : D1 ≤ Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t)))
    (hU : Real.log (1 + A1 / (2 * D1)) ≤ U) : rR z t ≤ 0.27125 * U + 0.41415 := by
  have h4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hq : Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) ≤
      A1 / (2 * D1) := div_le_div₀ (by linarith) hA (by linarith) (by linarith)
  have hq0 : 0 ≤ Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) :=
    div_nonneg h4 (by linarith)
  unfold rR
  set q := Real.log (4 * t) / (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t)))
  have hl := Real.log_le_log (by linarith) (by linarith : 1 + q ≤ 1 + A1 / (2 * D1))
  linarith

/-- **`rKB y_a t_b` from above** by `R_{y_a,t_b} ≤ A_u ≤ B_u ≥ R_{y_a/K_a,t_b}` and
`c_max(y_a) ≤ c_u`. -/
theorem rKB_le (ya tb Au Bu cu : ℝ) (hya : 10 ^ 25 ≤ ya) (hA : rR ya tb ≤ Au)
    (hB : rR (ya / kK ya) tb ≤ Bu) (hAB : Au ≤ Bu)
    (hc : 1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) ≤ cu) :
    rKB ya tb ≤ Au + cu * (Bu - Au) := by
  obtain ⟨-, -, hcm⟩ := cmix_le ya ya hya le_rfl
  have hc0 : 0 ≤ 1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) := by
    have := logK_ge ya hya
    have := Real.sqrt_nonneg (Real.pi / 2)
    positivity
  unfold rKB
  set c := 1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya))
  nlinarith [mul_nonneg (sub_nonneg.2 hcm) (sub_nonneg.2 hA), mul_nonneg hc0 (sub_nonneg.2 hB),
    mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hAB)]

/-- `c_max(y_a) ≤ (1/9)/(1.2533139 L)` from `log K_a ≥ L > 0`. -/
theorem cmax_le (ya L : ℝ) (hL : 0 < L) (h : L ≤ Real.log (kK ya)) :
    1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) ≤ 1 / 9 / (1.2533139 * L) := by
  have hs := MajSp.sqrt_pi_half.1
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul hs h hL.le (by linarith)

/-- `log(kK y)` from below: `log y ≥ 2K_l` and `log K_l ≥ L`. -/
theorem logK_ge_of (y Kl L : ℝ) (hKl : 0 < Kl) (hy : 2 * Kl ≤ Real.log y)
    (hL : L ≤ Real.log Kl) : L ≤ Real.log (kK y) := by
  refine hL.trans (Real.log_le_log hKl ?_)
  unfold kK
  linarith

/-- `log(kK y)` from above: `log y ≤ 2K_u` and `log K_u ≤ L`. -/
theorem logK_le_of (y Ku L : ℝ) (hy1 : 1 < y) (hy : Real.log y ≤ 2 * Ku)
    (hL : Real.log Ku ≤ L) : Real.log (kK y) ≤ L := by
  have hK0 : 0 < kK y := by
    unfold kK
    have := Real.log_pos hy1
    positivity
  refine le_trans (Real.log_le_log hK0 ?_) hL
  unfold kK
  linarith

/-! ## (10) Certified numerics: the instances (GENERATED by `gen_mnum_num.py`, every
inequality pre-checked there in exact rationals) -/

/-- `√150000 ≥ 387.2983`. -/
theorem sqrt_r0_ge : 387.2983 ≤ Real.sqrt 150000 := sqrt_ge_of _ _ (by norm_num) (by norm_num)

/-- `log 9` from below (truth `2.197224577`). -/
theorem log9_ge : 2.1972245 ≤ Real.log (9) := by
  have h := le_log_series (9) (-0.125) 3 12 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from below (truth `57.564627325`). -/
theorem lya_ge_1 : 57.564626 ≤ Real.log (10 ^ 25) := by
  have h := le_log_series (10 ^ 25) (-0.033975) 83 7 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from above (truth `57.564627325`). -/
theorem lya_le_1 : Real.log (10 ^ 25) ≤ 57.564628 := by
  have h := log_le_series (10 ^ 25) (-0.033976) 83 7 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_l` from below (truth `3.359761067`). -/
theorem lKl_ge_1 : 3.35976 ≤ Real.log (28.782313) := by
  have h := le_log_series (28.782313) (0.100553) 5 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_u` from above (truth `3.359761101`). -/
theorem lKu_le_1 : Real.log (28.782314) ≤ 3.359762 := by
  have h := log_le_series (28.782314) (0.100552) 5 11 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from below (truth `58.663239614`). -/
theorem lya_ge_2 : 58.663238 ≤ Real.log (3 * 10 ^ 25) := by
  have h := le_log_series (3 * 10 ^ 25) (0.224519) 85 17 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from above (truth `58.663239614`). -/
theorem lya_le_2 : Real.log (3 * 10 ^ 25) ≤ 58.66324 := by
  have h := log_le_series (3 * 10 ^ 25) (0.224518) 85 17 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_l` from below (truth `3.378666081`). -/
theorem lKl_ge_2 : 3.378665 ≤ Real.log (29.331619) := by
  have h := le_log_series (29.331619) (0.083387) 5 10 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_u` from above (truth `3.378666115`). -/
theorem lKu_le_2 : Real.log (29.33162) ≤ 3.378668 := by
  have h := log_le_series (29.33162) (0.083386) 5 10 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from below (truth `59.867212418`). -/
theorem lya_ge_3 : 59.867211 ≤ Real.log (10 ^ 26) := by
  have h := le_log_series (10 ^ 26) (-0.292469) 86 20 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from above (truth `59.867212418`). -/
theorem lya_le_3 : Real.log (10 ^ 26) ≤ 59.867213 := by
  have h := log_le_series (10 ^ 26) (-0.29247) 86 20 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_l` from below (truth `3.398981779`). -/
theorem lKl_ge_3 : 3.398981 ≤ Real.log (29.9336055) := by
  have h := le_log_series (29.9336055) (0.064575) 5 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_u` from above (truth `3.398981812`). -/
theorem lKu_le_3 : Real.log (29.9336065) ≤ 3.398983 := by
  have h := log_le_series (29.9336065) (0.064574) 5 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from below (truth `60.560359598`). -/
theorem lya_ge_4 : 60.560359 ≤ Real.log (2 * 10 ^ 26) := by
  have h := le_log_series (2 * 10 ^ 26) (-0.292469) 87 20 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log y_a` from above (truth `60.560359598`). -/
theorem lya_le_4 : Real.log (2 * 10 ^ 26) ≤ 60.56036 := by
  have h := log_le_series (2 * 10 ^ 26) (-0.29247) 87 20 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_l` from below (truth `3.410493357`). -/
theorem lKl_ge_4 : 3.410492 ≤ Real.log (30.2801795) := by
  have h := le_log_series (30.2801795) (0.053745) 5 8 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log K_u` from above (truth `3.410493373`). -/
theorem lKu_le_4 : Real.log (30.28018) ≤ 3.410494 := by
  have h := log_le_series (30.28018) (0.053744) 5 8 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `13.997832115`). -/
theorem l4tb_le_300000 : Real.log (4 * 300000) ≤ 13.997833 := by
  have h := log_le_series (4 * 300000) (-0.14441) 20 13 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `13.306682937`). -/
theorem l2tb_le_300000 : Real.log (2.004 * 300000) ≤ 13.306683 := by
  have h := log_le_series (2.004 * 300000) (-0.146698) 19 13 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `16.745103029`). -/
theorem l4tb_le_4680000 : Real.log (4 * 4680000) ≤ 16.745104 := by
  have h := log_le_series (4 * 4680000) (-0.115799) 24 11 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `16.053953851`). -/
theorem l2tb_le_4680000 : Real.log (2.004 * 4680000) ≤ 16.053955 := by
  have h := log_le_series (2.004 * 4680000) (-0.118031) 23 11 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `17.064333459`). -/
theorem l4tb_le_6440000 : Real.log (4 * 6440000) ≤ 17.064334 := by
  have h := log_le_series (4 * 6440000) (0.232292) 25 17 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `16.373184281`). -/
theorem l2tb_le_6440000 : Real.log (2.004 * 6440000) ≤ 16.373186 := by
  have h := log_le_series (2.004 * 6440000) (0.230756) 24 17 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `17.248206607`). -/
theorem l4tb_le_7740000 : Real.log (4 * 7740000) ≤ 17.248207 := by
  have h := log_le_series (4 * 7740000) (0.07732) 25 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `16.557057429`). -/
theorem l2tb_le_7740000 : Real.log (2.004 * 7740000) ≤ 16.557059 := by
  have h := log_le_series (2.004 * 7740000) (0.075474) 24 9 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `16.449181981`). -/
theorem l4tb_le_3481200 : Real.log (4 * 3481200) ≤ 16.449183 := by
  have h := log_le_series (4 * 3481200) (0.170017) 24 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `15.758032803`). -/
theorem l2tb_le_3481200 : Real.log (2.004 * 3481200) ≤ 15.758034 := by
  have h := log_le_series (2.004 * 3481200) (0.168357) 23 14 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `16.742149955`). -/
theorem l4tb_le_4666200 : Real.log (4 * 4666200) ≤ 16.742151 := by
  have h := log_le_series (4 * 4666200) (-0.112509) 24 11 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `16.051000777`). -/
theorem l2tb_le_4666200 : Real.log (2.004 * 4666200) ≤ 16.051001 := by
  have h := log_le_series (2.004 * 4666200) (-0.114734) 23 11 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `17.063214821`). -/
theorem l4tb_le_6432800 : Real.log (4 * 6432800) ≤ 17.063216 := by
  have h := log_le_series (4 * 6432800) (0.23315) 25 17 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `16.372065643`). -/
theorem l2tb_le_6432800 : Real.log (2.004 * 6432800) ≤ 16.372067 := by
  have h := log_le_series (2.004 * 6432800) (0.231616) 24 17 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 4t_b` from above (truth `17.248051556`). -/
theorem l4tb_le_7738800 : Real.log (4 * 7738800) ≤ 17.248052 := by
  have h := log_le_series (4 * 7738800) (0.077463) 25 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 2.004t_b` from above (truth `16.556902378`). -/
theorem l2tb_le_7738800 : Real.log (2.004 * 7738800) ≤ 16.556903 := by
  have h := log_le_series (2.004 * 7738800) (0.075618) 24 9 (by norm_num) (by norm_num) (by
      norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #01 (truth `0.623977452`). -/
theorem lu1_01 : Real.log (1 + 13.997833 / (2 * 8.07875)) ≤ 0.6239783 := by
  have h := log_le_series (1 + 13.997833 / (2 * 8.07875)) (0.066831) 1 9 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #01 (truth `0.696023374`). -/
theorem lu2_01 : Real.log (1 + 13.997833 / (2 * 6.958829)) ≤ 0.6960241 := by
  have h := log_le_series (1 + 13.997833 / (2 * 6.958829)) (-0.002881) 1 4 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(10 ^ 25, 300000, 0.5845)`: `rKB ≤ 0.5839198`. -/
theorem rkNum_01 : RKNum (10 ^ 25) 300000 0.5845 := by
  have hya : (0 : ℝ) < 10 ^ 25 := by norm_num
  have hD : 8.07875 ≤ Real.log (9 * (10 ^ 25) ^ ((1 : ℝ) / 3) / (2.004 * 300000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_1, l2tb_le_300000]
  have hKu := logK_le_of (10 ^ 25) 28.782314 3.359762 (by norm_num) (by linarith [lya_le_1])
      lKu_le_1
  have hKl := logK_ge_of (10 ^ 25) 28.782313 3.35976 (by norm_num) (by linarith [lya_ge_1]) lKl_ge_1
  have hK0 : 0 < kK (10 ^ 25) := by linarith [kK_ge (10 ^ 25) (by norm_num)]
  have hDz : 6.958829 ≤ Real.log (9 * ((10 ^ 25) / kK (10 ^ 25)) ^ ((1 : ℝ) / 3) / (2.004 *
      300000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_1, l2tb_le_300000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hD lu1_01
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hDz lu2_01
  have hc := cmax_le (10 ^ 25) 3.35976 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #02 (truth `0.603643090`). -/
theorem lu1_02 : Real.log (1 + 13.997833 / (2 * 8.444954)) ≤ 0.6036437 := by
  have h := log_le_series (1 + 13.997833 / (2 * 8.444954)) (0.085615) 1 10 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #02 (truth `0.671055915`). -/
theorem lu2_02 : Real.log (1 + 13.997833 / (2 * 7.318731)) ≤ 0.671056 := by
  have h := log_le_series (1 + 13.997833 / (2 * 7.318731)) (0.021849) 1 6 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(3 * 10 ^ 25, 300000, 0.579)`: `rKB ≤ 0.5783682`. -/
theorem rkNum_02 : RKNum (3 * 10 ^ 25) 300000 0.579 := by
  have hya : (0 : ℝ) < 3 * 10 ^ 25 := by norm_num
  have hD : 8.444954 ≤ Real.log (9 * (3 * 10 ^ 25) ^ ((1 : ℝ) / 3) / (2.004 * 300000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_2, l2tb_le_300000]
  have hKu := logK_le_of (3 * 10 ^ 25) 29.33162 3.378668 (by norm_num) (by linarith [lya_le_2])
      lKu_le_2
  have hKl := logK_ge_of (3 * 10 ^ 25) 29.331619 3.378665 (by norm_num) (by linarith [lya_ge_2])
      lKl_ge_2
  have hK0 : 0 < kK (3 * 10 ^ 25) := by linarith [kK_ge (3 * 10 ^ 25) (by norm_num)]
  have hDz : 7.318731 ≤ Real.log (9 * ((3 * 10 ^ 25) / kK (3 * 10 ^ 25)) ^ ((1 : ℝ) / 3) / (2.004
      * 300000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_2, l2tb_le_300000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hD lu1_02
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hDz lu2_02
  have hc := cmax_le (3 * 10 ^ 25) 3.378665 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #03 (truth `0.582869463`). -/
theorem lu1_03 : Real.log (1 + 13.997833 / (2 * 8.846278)) ≤ 0.5828702 := by
  have h := log_le_series (1 + 13.997833 / (2 * 8.846278)) (0.104414) 1 11 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #03 (truth `0.645733078`). -/
theorem lu2_03 : Real.log (1 + 13.997833 / (2 * 7.713284)) ≤ 0.6457338 := by
  have h := log_le_series (1 + 13.997833 / (2 * 7.713284)) (0.046307) 1 8 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(10 ^ 26, 300000, 0.5735)`: `rKB ≤ 0.5726983`. -/
theorem rkNum_03 : RKNum (10 ^ 26) 300000 0.5735 := by
  have hya : (0 : ℝ) < 10 ^ 26 := by norm_num
  have hD : 8.846278 ≤ Real.log (9 * (10 ^ 26) ^ ((1 : ℝ) / 3) / (2.004 * 300000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_3, l2tb_le_300000]
  have hKu := logK_le_of (10 ^ 26) 29.9336065 3.398983 (by norm_num) (by linarith [lya_le_3])
      lKu_le_3
  have hKl := logK_ge_of (10 ^ 26) 29.9336055 3.398981 (by norm_num) (by linarith [lya_ge_3])
      lKl_ge_3
  have hK0 : 0 < kK (10 ^ 26) := by linarith [kK_ge (10 ^ 26) (by norm_num)]
  have hDz : 7.713284 ≤ Real.log (9 * ((10 ^ 26) / kK (10 ^ 26)) ^ ((1 : ℝ) / 3) / (2.004 *
      300000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_3, l2tb_le_300000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hD lu1_03
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hDz lu2_03
  have hc := cmax_le (10 ^ 26) 3.398981 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #04 (truth `0.571562857`). -/
theorem lu1_04 : Real.log (1 + 13.997833 / (2 * 9.077327)) ≤ 0.5715636 := by
  have h := log_le_series (1 + 13.997833 / (2 * 9.077327)) (0.114483) 1 11 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #04 (truth `0.632027113`). -/
theorem lu2_04 : Real.log (1 + 13.997833 / (2 * 7.940496)) ≤ 0.6320279 := by
  have h := log_le_series (1 + 13.997833 / (2 * 7.940496)) (0.059289) 1 8 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(2 * 10 ^ 26, 300000, 0.5705)`: `rKB ≤ 0.5696130`. -/
theorem rkNum_04 : RKNum (2 * 10 ^ 26) 300000 0.5705 := by
  have hya : (0 : ℝ) < 2 * 10 ^ 26 := by norm_num
  have hD : 9.077327 ≤ Real.log (9 * (2 * 10 ^ 26) ^ ((1 : ℝ) / 3) / (2.004 * 300000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_4, l2tb_le_300000]
  have hKu := logK_le_of (2 * 10 ^ 26) 30.28018 3.410494 (by norm_num) (by linarith [lya_le_4])
      lKu_le_4
  have hKl := logK_ge_of (2 * 10 ^ 26) 30.2801795 3.410492 (by norm_num) (by linarith [lya_ge_4])
      lKl_ge_4
  have hK0 : 0 < kK (2 * 10 ^ 26) := by linarith [kK_ge (2 * 10 ^ 26) (by norm_num)]
  have hDz : 7.940496 ≤ Real.log (9 * ((2 * 10 ^ 26) / kK (2 * 10 ^ 26)) ^ ((1 : ℝ) / 3) / (2.004
      * 300000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_4, l2tb_le_300000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hD lu1_04
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_300000 (by norm_num) hDz lu2_04
  have hc := cmax_le (2 * 10 ^ 26) 3.410492 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #11 (truth `0.944061452`). -/
theorem lu1_11 : Real.log (1 + 16.745104 / (2 * 5.331478)) ≤ 0.9440616 := by
  have h := log_le_series (1 + 16.745104 / (2 * 5.331478)) (-0.2852) 1 20 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #11 (truth `1.094602414`). -/
theorem lu2_11 : Real.log (1 + 16.745104 / (2 * 4.211557)) ≤ 1.094603 := by
  have h := log_le_series (1 + 16.745104 / (2 * 4.211557)) (0.253001) 2 18 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(10 ^ 25, 4680000, 0.672)`: `rKB ≤ 0.6713042`. -/
theorem rkNum_11 : RKNum (10 ^ 25) 4680000 0.672 := by
  have hya : (0 : ℝ) < 10 ^ 25 := by norm_num
  have hD : 5.331478 ≤ Real.log (9 * (10 ^ 25) ^ ((1 : ℝ) / 3) / (2.004 * 4680000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_1, l2tb_le_4680000]
  have hKu := logK_le_of (10 ^ 25) 28.782314 3.359762 (by norm_num) (by linarith [lya_le_1])
      lKu_le_1
  have hKl := logK_ge_of (10 ^ 25) 28.782313 3.35976 (by norm_num) (by linarith [lya_ge_1]) lKl_ge_1
  have hK0 : 0 < kK (10 ^ 25) := by linarith [kK_ge (10 ^ 25) (by norm_num)]
  have hDz : 4.211557 ≤ Real.log (9 * ((10 ^ 25) / kK (10 ^ 25)) ^ ((1 : ℝ) / 3) / (2.004 *
      4680000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_1, l2tb_le_4680000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_4680000 (by norm_num) hD lu1_11
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_4680000 (by norm_num) hDz lu2_11
  have hc := cmax_le (10 ^ 25) 3.35976 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #12 (truth `0.950252019`). -/
theorem lu1_12 : Real.log (1 + 17.064334 / (2 * 5.378451)) ≤ 0.9502523 := by
  have h := log_le_series (1 + 17.064334 / (2 * 5.378451)) (-0.293181) 1 20 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #12 (truth `1.100782206`). -/
theorem lu2_12 : Real.log (1 + 17.064334 / (2 * 4.252228)) ≤ 1.1007833 := by
  have h := log_le_series (1 + 17.064334 / (2 * 4.252228)) (0.24837) 2 18 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(3 * 10 ^ 25, 6440000, 0.674)`: `rKB ≤ 0.6729773`. -/
theorem rkNum_12 : RKNum (3 * 10 ^ 25) 6440000 0.674 := by
  have hya : (0 : ℝ) < 3 * 10 ^ 25 := by norm_num
  have hD : 5.378451 ≤ Real.log (9 * (3 * 10 ^ 25) ^ ((1 : ℝ) / 3) / (2.004 * 6440000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_2, l2tb_le_6440000]
  have hKu := logK_le_of (3 * 10 ^ 25) 29.33162 3.378668 (by norm_num) (by linarith [lya_le_2])
      lKu_le_2
  have hKl := logK_ge_of (3 * 10 ^ 25) 29.331619 3.378665 (by norm_num) (by linarith [lya_ge_2])
      lKl_ge_2
  have hK0 : 0 < kK (3 * 10 ^ 25) := by linarith [kK_ge (3 * 10 ^ 25) (by norm_num)]
  have hDz : 4.252228 ≤ Real.log (9 * ((3 * 10 ^ 25) / kK (3 * 10 ^ 25)) ^ ((1 : ℝ) / 3) / (2.004
      * 6440000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_2, l2tb_le_6440000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_6440000 (by norm_num) hD lu1_12
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_6440000 (by norm_num) hDz lu2_12
  have hc := cmax_le (3 * 10 ^ 25) 3.378665 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #13 (truth `0.932615267`). -/
theorem lu1_13 : Real.log (1 + 17.248207 / (2 * 5.595902)) ≤ 0.932616 := by
  have h := log_le_series (1 + 17.248207 / (2 * 5.595902)) (-0.270574) 1 19 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #13 (truth `1.075819678`). -/
theorem lu2_13 : Real.log (1 + 17.248207 / (2 * 4.462908)) ≤ 1.0758199 := by
  have h := log_le_series (1 + 17.248207 / (2 * 4.462908)) (0.266901) 2 19 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(10 ^ 26, 7740000, 0.669)`: `rKB ≤ 0.6681352`. -/
theorem rkNum_13 : RKNum (10 ^ 26) 7740000 0.669 := by
  have hya : (0 : ℝ) < 10 ^ 26 := by norm_num
  have hD : 5.595902 ≤ Real.log (9 * (10 ^ 26) ^ ((1 : ℝ) / 3) / (2.004 * 7740000)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_3, l2tb_le_7740000]
  have hKu := logK_le_of (10 ^ 26) 29.9336065 3.398983 (by norm_num) (by linarith [lya_le_3])
      lKu_le_3
  have hKl := logK_ge_of (10 ^ 26) 29.9336055 3.398981 (by norm_num) (by linarith [lya_ge_3])
      lKl_ge_3
  have hK0 : 0 < kK (10 ^ 26) := by linarith [kK_ge (10 ^ 26) (by norm_num)]
  have hDz : 4.462908 ≤ Real.log (9 * ((10 ^ 26) / kK (10 ^ 26)) ^ ((1 : ℝ) / 3) / (2.004 *
      7740000)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_3, l2tb_le_7740000]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_7740000 (by norm_num) hD lu1_13
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_7740000 (by norm_num) hDz lu2_13
  have hc := cmax_le (10 ^ 26) 3.398981 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #21 (truth `0.900781595`). -/
theorem lu1_21 : Real.log (1 + 16.449183 / (2 * 5.627399)) ≤ 0.9007823 := by
  have h := log_le_series (1 + 16.449183 / (2 * 5.627399)) (-0.230764) 1 17 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #21 (truth `1.038386173`). -/
theorem lu2_21 : Real.log (1 + 16.449183 / (2 * 4.507478)) ≤ 1.0383866 := by
  have h := log_le_series (1 + 16.449183 / (2 * 4.507478)) (-0.412328) 1 29 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(10 ^ 25, 3481200, 0.66)`: `rKB ≤ 0.6594721`. -/
theorem rkNum_21 : RKNum (10 ^ 25) 3481200 0.66 := by
  have hya : (0 : ℝ) < 10 ^ 25 := by norm_num
  have hD : 5.627399 ≤ Real.log (9 * (10 ^ 25) ^ ((1 : ℝ) / 3) / (2.004 * 3481200)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_1, l2tb_le_3481200]
  have hKu := logK_le_of (10 ^ 25) 28.782314 3.359762 (by norm_num) (by linarith [lya_le_1])
      lKu_le_1
  have hKl := logK_ge_of (10 ^ 25) 28.782313 3.35976 (by norm_num) (by linarith [lya_ge_1]) lKl_ge_1
  have hK0 : 0 < kK (10 ^ 25) := by linarith [kK_ge (10 ^ 25) (by norm_num)]
  have hDz : 4.507478 ≤ Real.log (9 * ((10 ^ 25) / kK (10 ^ 25)) ^ ((1 : ℝ) / 3) / (2.004 *
      3481200)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_1, l2tb_le_3481200]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_3481200 (by norm_num) hD lu1_21
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_3481200 (by norm_num) hDz lu2_21
  have hc := cmax_le (10 ^ 25) 3.35976 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #22 (truth `0.903588758`). -/
theorem lu1_22 : Real.log (1 + 16.742151 / (2 * 5.700636)) ≤ 0.9035889 := by
  have h := log_le_series (1 + 16.742151 / (2 * 5.700636)) (-0.234223) 1 17 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #22 (truth `1.040268965`). -/
theorem lu2_22 : Real.log (1 + 16.742151 / (2 * 4.574413)) ≤ 1.0402697 := by
  have h := log_le_series (1 + 16.742151 / (2 * 4.574413)) (0.292505) 2 20 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(3 * 10 ^ 25, 4666200, 0.661)`: `rKB ≤ 0.6602213`. -/
theorem rkNum_22 : RKNum (3 * 10 ^ 25) 4666200 0.661 := by
  have hya : (0 : ℝ) < 3 * 10 ^ 25 := by norm_num
  have hD : 5.700636 ≤ Real.log (9 * (3 * 10 ^ 25) ^ ((1 : ℝ) / 3) / (2.004 * 4666200)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_2, l2tb_le_4666200]
  have hKu := logK_le_of (3 * 10 ^ 25) 29.33162 3.378668 (by norm_num) (by linarith [lya_le_2])
      lKu_le_2
  have hKl := logK_ge_of (3 * 10 ^ 25) 29.331619 3.378665 (by norm_num) (by linarith [lya_ge_2])
      lKl_ge_2
  have hK0 : 0 < kK (3 * 10 ^ 25) := by linarith [kK_ge (3 * 10 ^ 25) (by norm_num)]
  have hDz : 4.574413 ≤ Real.log (9 * ((3 * 10 ^ 25) / kK (3 * 10 ^ 25)) ^ ((1 : ℝ) / 3) / (2.004
      * 4666200)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_2, l2tb_le_4666200]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_4666200 (by norm_num) hD lu1_22
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_4666200 (by norm_num) hDz lu2_22
  have hc := cmax_le (3 * 10 ^ 25) 3.378665 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #23 (truth `0.906575079`). -/
theorem lu1_23 : Real.log (1 + 17.063216 / (2 * 5.780894)) ≤ 0.9065757 := by
  have h := log_le_series (1 + 17.063216 / (2 * 5.780894)) (-0.237915) 1 17 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #23 (truth `1.042247694`). -/
theorem lu2_23 : Real.log (1 + 17.063216 / (2 * 4.6479)) ≤ 1.042248 := by
  have h := log_le_series (1 + 17.063216 / (2 * 4.6479)) (0.291104) 2 20 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(10 ^ 26, 6432800, 0.6615)`: `rKB ≤ 0.6610185`. -/
theorem rkNum_23 : RKNum (10 ^ 26) 6432800 0.6615 := by
  have hya : (0 : ℝ) < 10 ^ 26 := by norm_num
  have hD : 5.780894 ≤ Real.log (9 * (10 ^ 26) ^ ((1 : ℝ) / 3) / (2.004 * 6432800)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_3, l2tb_le_6432800]
  have hKu := logK_le_of (10 ^ 26) 29.9336065 3.398983 (by norm_num) (by linarith [lya_le_3])
      lKu_le_3
  have hKl := logK_ge_of (10 ^ 26) 29.9336055 3.398981 (by norm_num) (by linarith [lya_ge_3])
      lKl_ge_3
  have hK0 : 0 < kK (10 ^ 26) := by linarith [kK_ge (10 ^ 26) (by norm_num)]
  have hDz : 4.6479 ≤ Real.log (9 * ((10 ^ 26) / kK (10 ^ 26)) ^ ((1 : ℝ) / 3) / (2.004 *
      6432800)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_3, l2tb_le_6432800]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_6432800 (by norm_num) hD lu1_23
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_6432800 (by norm_num) hDz lu2_23
  have hc := cmax_le (10 ^ 26) 3.398981 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `log(1 + A₁/(2D₁))` at `(y_a, t_b)` #24 (truth `0.908252169`). -/
theorem lu1_24 : Real.log (1 + 17.248052 / (2 * 5.827107)) ≤ 0.908253 := by
  have h := log_le_series (1 + 17.248052 / (2 * 5.827107)) (-0.239993) 1 17 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(1 + A₁/(2D₁))` at `(y_a/K_a, t_b)` #24 (truth `1.043347366`). -/
theorem lu2_24 : Real.log (1 + 17.248052 / (2 * 4.690276)) ≤ 1.0433477 := by
  have h := log_le_series (1 + 17.248052 / (2 * 4.690276)) (0.290324) 2 20 (by norm_num) (by
      norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[RKNum] DISCHARGED** at `(2 * 10 ^ 26, 7738800, 0.662)`: `rKB ≤ 0.6614662`. -/
theorem rkNum_24 : RKNum (2 * 10 ^ 26) 7738800 0.662 := by
  have hya : (0 : ℝ) < 2 * 10 ^ 26 := by norm_num
  have hD : 5.827107 ≤ Real.log (9 * (2 * 10 ^ 26) ^ ((1 : ℝ) / 3) / (2.004 * 7738800)) := by
    rw [logD_eq _ _ hya (by norm_num)]
    linarith [log9_ge, lya_ge_4, l2tb_le_7738800]
  have hKu := logK_le_of (2 * 10 ^ 26) 30.28018 3.410494 (by norm_num) (by linarith [lya_le_4])
      lKu_le_4
  have hKl := logK_ge_of (2 * 10 ^ 26) 30.2801795 3.410492 (by norm_num) (by linarith [lya_ge_4])
      lKl_ge_4
  have hK0 : 0 < kK (2 * 10 ^ 26) := by linarith [kK_ge (2 * 10 ^ 26) (by norm_num)]
  have hDz : 4.690276 ≤ Real.log (9 * ((2 * 10 ^ 26) / kK (2 * 10 ^ 26)) ^ ((1 : ℝ) / 3) / (2.004
      * 7738800)) := by
    rw [logD_eq _ _ (div_pos hya hK0) (by norm_num), Real.log_div hya.ne' hK0.ne']
    linarith [log9_ge, lya_ge_4, l2tb_le_7738800]
  have hA := rR_le _ _ _ _ _ (by norm_num) l4tb_le_7738800 (by norm_num) hD lu1_24
  have hB := rR_le _ _ _ _ _ (by norm_num) l4tb_le_7738800 (by norm_num) hDz lu2_24
  have hc := cmax_le (2 * 10 ^ 26) 3.410492 (by norm_num) hKl
  refine (rKB_le _ _ _ _ _ (by norm_num) hA hB (by norm_num) hc).trans ?_
  norm_num

/-- `f₂(10 ^ 25) ≤ 3.2·0.000119267181`. -/
theorem f2_le_1 : f2 (10 ^ 25) ≤ 3.2 * 0.000119267181 :=
  f2_le _ _ _ (by norm_num) lya_le_1 (by norm_num) (by norm_num)

/-- `f₂(3 * 10 ^ 25) ≤ 3.2·0.000099625184`. -/
theorem f2_le_2 : f2 (3 * 10 ^ 25) ≤ 3.2 * 0.000099625184 :=
  f2_le _ _ _ (by norm_num) lya_le_2 (by norm_num) (by norm_num)

/-- `f₂(10 ^ 26) ≤ 3.2·0.000081788676`. -/
theorem f2_le_3 : f2 (10 ^ 26) ≤ 3.2 * 0.000081788676 :=
  f2_le _ _ _ (by norm_num) lya_le_3 (by norm_num) (by norm_num)

/-- `f₂(2 * 10 ^ 26) ≤ 3.2·0.00007300536`. -/
theorem f2_le_4 : f2 (2 * 10 ^ 26) ≤ 3.2 * 0.00007300536 :=
  f2_le _ _ _ (by norm_num) lya_le_4 (by norm_num) (by norm_num)

/-- **[G0Num] DISCHARGED** at `(10 ^ 25, 0.5845, 0.0412)` (value `≤ 0.0411077`). -/
theorem g0Num_1 : G0Num (10 ^ 25) 0.5845 0.0412 := by
  have h1 := envQ_le 0.5845 150000 11.9183906 387.2983 150000 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge (by norm_num) le_rfl
  have h2 := f2_le_1
  have h3 : 0.70711 * pA 0.5845 11.9183906 / 387.2983 + qA 11.9183906 / 150000 + 3.2 *
      0.000119267181 ≤ 0.0412 := by
    unfold pA qA
    norm_num
  unfold G0Num
  linarith

/-- **[G0Num] DISCHARGED** at `(3 * 10 ^ 25, 0.579, 0.0409)` (value `≤ 0.0407494`). -/
theorem g0Num_2 : G0Num (3 * 10 ^ 25) 0.579 0.0409 := by
  have h1 := envQ_le 0.579 150000 11.9183906 387.2983 150000 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge (by norm_num) le_rfl
  have h2 := f2_le_2
  have h3 : 0.70711 * pA 0.579 11.9183906 / 387.2983 + qA 11.9183906 / 150000 + 3.2 *
      0.000099625184 ≤ 0.0409 := by
    unfold pA qA
    norm_num
  unfold G0Num
  linarith

/-- **[G0Num] DISCHARGED** at `(10 ^ 26, 0.5735, 0.0406)` (value `≤ 0.0403969`). -/
theorem g0Num_3 : G0Num (10 ^ 26) 0.5735 0.0406 := by
  have h1 := envQ_le 0.5735 150000 11.9183906 387.2983 150000 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge (by norm_num) le_rfl
  have h2 := f2_le_3
  have h3 : 0.70711 * pA 0.5735 11.9183906 / 387.2983 + qA 11.9183906 / 150000 + 3.2 *
      0.000081788676 ≤ 0.0406 := by
    unfold pA qA
    norm_num
  unfold G0Num
  linarith

/-- **[G0Num] DISCHARGED** at `(2 * 10 ^ 26, 0.5705, 0.0404)` (value `≤ 0.0402076`). -/
theorem g0Num_4 : G0Num (2 * 10 ^ 26) 0.5705 0.0404 := by
  have h1 := envQ_le 0.5705 150000 11.9183906 387.2983 150000 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge (by norm_num) le_rfl
  have h2 := f2_le_4
  have h3 : 0.70711 * pA 0.5705 11.9183906 / 387.2983 + qA 11.9183906 / 150000 + 3.2 *
      0.00007300536 ≤ 0.0404 := by
    unfold pA qA
    norm_num
  unfold G0Num
  linarith

/-- `log R` from below (truth `14.665661487`). -/
theorem lR_ge_1 : 14.66566 ≤ Real.log (2340000) := by
  have h := le_log_series (2340000) (-0.115798) 21 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log R` from above (truth `14.665661487`). -/
theorem lR_le_1 : Real.log (2340000) ≤ 14.665662 := by
  have h := log_le_series (2340000) (-0.115799) 21 11 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `√2340000 ≤ 1529.706`. -/
theorem sqrtR_le_1 : Real.sqrt 2340000 ≤ 1529.706 := sqrt_le_of _ _ (by norm_num) (by norm_num)

/-- **[IBlkNum] DISCHARGED** at `(10 ^ 25, 0.672, 2340000, 0.074)` (value `≤ 0.0731150`). -/
theorem iBlkNum_1 : IBlkNum (10 ^ 25) 0.672 2340000 0.074 := by
  have h1 := PhiQ_le 0.672 2340000 14.66566 1529.706 (by norm_num) (by norm_num) (by norm_num)
      lR_ge_1
    sqrtR_le_1
  have h2 := negPhiQ_le 0.672 150000 11.9183906 387.2983 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge
  have h3 := f2_le_1
  have h4 := f2_nonneg (10 ^ 25) (by norm_num)
  have h5 : Real.log 2340000 - Real.log 150000 ≤ 14.665662 - 11.9183905 := by
    linarith [lR_le_1, log_r0_ge]
  have h6 : 0 ≤ Real.log 2340000 - Real.log 150000 := by linarith [lR_ge_1, log_r0_le]
  have h7 := mul_le_mul h3 h5 h6 (by norm_num)
  have h8 : -(2 * 0.70711) * sP 0.672 14.66566 / 1529.706 - tQ 14.66566 / 2340000 +
      (2 * 0.70711 * sP 0.672 11.9183906 / 387.2983 + tQ 11.9183906 / 150000) + 3.2 *
          0.000119267181 * (14.665662 - 11.9183905) ≤ 0.074 := by
    unfold sP tQ pA dpA ddpA qA dqA ddqA
    norm_num
  unfold IBlkNum
  linarith

/-- `log R` from below (truth `14.984891918`). -/
theorem lR_ge_2 : 14.98489 ≤ Real.log (3220000) := by
  have h := le_log_series (3220000) (0.232293) 22 17 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log R` from above (truth `14.984891918`). -/
theorem lR_le_2 : Real.log (3220000) ≤ 14.984893 := by
  have h := log_le_series (3220000) (0.232292) 22 17 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `√3220000 ≤ 1794.436`. -/
theorem sqrtR_le_2 : Real.sqrt 3220000 ≤ 1794.436 := sqrt_le_of _ _ (by norm_num) (by norm_num)

/-- **[IBlkNum] DISCHARGED** at `(3 * 10 ^ 25, 0.674, 3220000, 0.0785)` (value `≤ 0.0772457`). -/
theorem iBlkNum_2 : IBlkNum (3 * 10 ^ 25) 0.674 3220000 0.0785 := by
  have h1 := PhiQ_le 0.674 3220000 14.98489 1794.436 (by norm_num) (by norm_num) (by norm_num)
      lR_ge_2
    sqrtR_le_2
  have h2 := negPhiQ_le 0.674 150000 11.9183906 387.2983 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge
  have h3 := f2_le_2
  have h4 := f2_nonneg (3 * 10 ^ 25) (by norm_num)
  have h5 : Real.log 3220000 - Real.log 150000 ≤ 14.984893 - 11.9183905 := by
    linarith [lR_le_2, log_r0_ge]
  have h6 : 0 ≤ Real.log 3220000 - Real.log 150000 := by linarith [lR_ge_2, log_r0_le]
  have h7 := mul_le_mul h3 h5 h6 (by norm_num)
  have h8 : -(2 * 0.70711) * sP 0.674 14.98489 / 1794.436 - tQ 14.98489 / 3220000 +
      (2 * 0.70711 * sP 0.674 11.9183906 / 387.2983 + tQ 11.9183906 / 150000) + 3.2 *
          0.000099625184 * (14.984893 - 11.9183905) ≤ 0.0785 := by
    unfold sP tQ pA dpA ddpA qA dqA ddqA
    norm_num
  unfold IBlkNum
  linarith

/-- `log R` from below (truth `15.168765065`). -/
theorem lR_ge_3 : 15.168764 ≤ Real.log (3870000) := by
  have h := le_log_series (3870000) (0.077321) 22 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log R` from above (truth `15.168765065`). -/
theorem lR_le_3 : Real.log (3870000) ≤ 15.168766 := by
  have h := log_le_series (3870000) (0.07732) 22 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `√3870000 ≤ 1967.232`. -/
theorem sqrtR_le_3 : Real.sqrt 3870000 ≤ 1967.232 := sqrt_le_of _ _ (by norm_num) (by norm_num)

/-- **[IBlkNum] DISCHARGED** at `(10 ^ 26, 0.669, 3870000, 0.08)` (value `≤ 0.0787129`). -/
theorem iBlkNum_3 : IBlkNum (10 ^ 26) 0.669 3870000 0.08 := by
  have h1 := PhiQ_le 0.669 3870000 15.168764 1967.232 (by norm_num) (by norm_num) (by norm_num)
      lR_ge_3
    sqrtR_le_3
  have h2 := negPhiQ_le 0.669 150000 11.9183906 387.2983 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge
  have h3 := f2_le_3
  have h4 := f2_nonneg (10 ^ 26) (by norm_num)
  have h5 : Real.log 3870000 - Real.log 150000 ≤ 15.168766 - 11.9183905 := by
    linarith [lR_le_3, log_r0_ge]
  have h6 : 0 ≤ Real.log 3870000 - Real.log 150000 := by linarith [lR_ge_3, log_r0_le]
  have h7 := mul_le_mul h3 h5 h6 (by norm_num)
  have h8 : -(2 * 0.70711) * sP 0.669 15.168764 / 1967.232 - tQ 15.168764 / 3870000 +
      (2 * 0.70711 * sP 0.669 11.9183906 / 387.2983 + tQ 11.9183906 / 150000) + 3.2 *
          0.000081788676 * (15.168766 - 11.9183905) ≤ 0.08 := by
    unfold sP tQ pA dpA ddpA qA dqA ddqA
    norm_num
  unfold IBlkNum
  linarith

/-- **[ITailNum] DISCHARGED** at `(0.72, 0.0039, 0.115)` (value `≤ 0.1127005`). -/
theorem iTailNum : ITailNum 0.72 0.0039 0.115 := by
  have h := negPhiQ_le 0.72 150000 11.9183906 387.2983 (by norm_num) (by norm_num) log_r0_le
    (by norm_num) sqrt_r0_ge
  have h8 : 2 * 0.70711 * sP 0.72 11.9183906 / 387.2983 + tQ 11.9183906 / 150000 + 0.0039 ≤ 0.115
      := by
    unfold sP tQ pA dpA ddpA qA dqA ddqA
    norm_num
  unfold ITailNum
  linarith

/-- `log(4.9·10²⁶)` from above (truth `61.456447623`). -/
theorem lxa_le_1 : Real.log (49 * 10 ^ 25) ≤ 61.456449 := by
  have h := log_le_series (49 * 10 ^ 25) (0.208362) 89 16 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log r₁^{hi}` from above (truth `14.369740439`). -/
theorem lr1_le_1 : Real.log (1740600) ≤ 14.369741 := by
  have h := log_le_series (1740600) (0.170017) 21 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[T1EnvNum] DISCHARGED** at `(49 * 10 ^ 25, 0.66, 0.2865)` (value `≤ 0.2836527`). -/
theorem t1EnvNum_1 : T1EnvNum (49 * 10 ^ 25) 0.66 0.2865 := by
  have e : (49 * 10 ^ 25 : ℝ) / 49 = 10 ^ 25 := by norm_num
  unfold T1EnvNum
  rw [e]
  have hr1 : r1y (10 ^ 25) ≤ 1740600 := r1Le_1
  have hrl : (1740595 : ℝ) ≤ r1y (10 ^ 25) := r1_ge_of _ _ (by norm_num) (by norm_num) (by norm_num)
  have hlr : Real.log (r1y (10 ^ 25)) ≤ 14.369741 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_1
  have hs : 1319.316 ≤ Real.sqrt (r1y (10 ^ 25)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1319.316 : ℝ) ^ 2 ≤ 1740595)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.66 (r1y (10 ^ 25)) 14.369741 1319.316 1740595 (by norm_num) (by linarith) hlr
    (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.66 (r1y (10 ^ 25)) (by norm_num) (by linarith)
  have hF := f2_le_1
  have hF0 := f2_nonneg (10 ^ 25) (by norm_num)
  have hC := coefC_le (49 * 10 ^ 25) 61.456449 (by norm_num) lxa_le_1
  have hC0 := coefC_nonneg (49 * 10 ^ 25) (by norm_num)
  have hL : fel (49 * 10 ^ 25) ≤ 0.640209 * 61.456449 - 0.021095 := by
    unfold fel
    linarith [lxa_le_1]
  have hL0 := fel_nonneg (49 * 10 ^ 25) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- `log r₁^{hi}` from above (truth `14.662708413`). -/
theorem lr1_le_2 : Real.log (2333100) ≤ 14.662709 := by
  have h := log_le_series (2333100) (-0.112509) 21 11 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[T1EnvNum] DISCHARGED** at `(147 * 10 ^ 25, 0.661, 0.2565)` (value `≤ 0.2538804`). -/
theorem t1EnvNum_2 : T1EnvNum (147 * 10 ^ 25) 0.661 0.2565 := by
  have e : (147 * 10 ^ 25 : ℝ) / 49 = 3 * 10 ^ 25 := by norm_num
  unfold T1EnvNum
  rw [e]
  have hr1 : r1y (3 * 10 ^ 25) ≤ 2333100 := r1Le_2
  have hrl : (2333083 : ℝ) ≤ r1y (3 * 10 ^ 25) := r1_ge_of _ _ (by norm_num) (by norm_num) (by
      norm_num)
  have hlr : Real.log (r1y (3 * 10 ^ 25)) ≤ 14.662709 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_2
  have hs : 1527.443 ≤ Real.sqrt (r1y (3 * 10 ^ 25)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1527.443 : ℝ) ^ 2 ≤ 2333083)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.661 (r1y (3 * 10 ^ 25)) 14.662709 1527.443 2333083 (by norm_num) (by
      linarith) hlr
    (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.661 (r1y (3 * 10 ^ 25)) (by norm_num) (by linarith)
  have hF := f2_le_2
  have hF0 := f2_nonneg (3 * 10 ^ 25) (by norm_num)
  have hC := coefC_le (147 * 10 ^ 25) 62.5552 (by norm_num) log_147e25_le
  have hC0 := coefC_nonneg (147 * 10 ^ 25) (by norm_num)
  have hL : fel (147 * 10 ^ 25) ≤ 0.640209 * 62.5552 - 0.021095 := by
    unfold fel
    linarith [log_147e25_le]
  have hL0 := fel_nonneg (147 * 10 ^ 25) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- `log r₁^{hi}` from above (truth `14.983773280`). -/
theorem lr1_le_3 : Real.log (3216400) ≤ 14.983774 := by
  have h := log_le_series (3216400) (0.23315) 22 17 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[T1EnvNum] DISCHARGED** at `(49 * 10 ^ 26, 0.6615, 0.227)` (value `≤ 0.2246102`). -/
theorem t1EnvNum_3 : T1EnvNum (49 * 10 ^ 26) 0.6615 0.227 := by
  have e : (49 * 10 ^ 26 : ℝ) / 49 = 10 ^ 26 := by norm_num
  unfold T1EnvNum
  rw [e]
  have hr1 : r1y (10 ^ 26) ≤ 3216400 := r1Le_3
  have hrl : (3216359 : ℝ) ≤ r1y (10 ^ 26) := r1_ge_of _ _ (by norm_num) (by norm_num) (by norm_num)
  have hlr : Real.log (r1y (10 ^ 26)) ≤ 14.983774 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_3
  have hs : 1793.421 ≤ Real.sqrt (r1y (10 ^ 26)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1793.421 : ℝ) ^ 2 ≤ 3216359)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.6615 (r1y (10 ^ 26)) 14.983774 1793.421 3216359 (by norm_num) (by linarith)
      hlr
    (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.6615 (r1y (10 ^ 26)) (by norm_num) (by linarith)
  have hF := f2_le_3
  have hF0 := f2_nonneg (10 ^ 26) (by norm_num)
  have hC := coefC_le (49 * 10 ^ 26) 63.7592 (by norm_num) log_49e26_le
  have hC0 := coefC_nonneg (49 * 10 ^ 26) (by norm_num)
  have hL : fel (49 * 10 ^ 26) ≤ 0.640209 * 63.7592 - 0.021095 := by
    unfold fel
    linarith [log_49e26_le]
  have hL0 := fel_nonneg (49 * 10 ^ 26) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- `log r₁^{hi}` from above (truth `15.168610014`). -/
theorem lr1_le_4 : Real.log (3869400) ≤ 15.168611 := by
  have h := log_le_series (3869400) (0.077463) 22 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[T1EnvNum] DISCHARGED** at `(98 * 10 ^ 26, 0.662, 0.2115)` (value `≤ 0.2093469`). -/
theorem t1EnvNum_4 : T1EnvNum (98 * 10 ^ 26) 0.662 0.2115 := by
  have e : (98 * 10 ^ 26 : ℝ) / 49 = 2 * 10 ^ 26 := by norm_num
  unfold T1EnvNum
  rw [e]
  have hr1 : r1y (2 * 10 ^ 26) ≤ 3869400 := r1Le_4
  have hrl : (3869361 : ℝ) ≤ r1y (2 * 10 ^ 26) := r1_ge_of _ _ (by norm_num) (by norm_num) (by
      norm_num)
  have hlr : Real.log (r1y (2 * 10 ^ 26)) ≤ 15.168611 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_4
  have hs : 1967.069 ≤ Real.sqrt (r1y (2 * 10 ^ 26)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1967.069 : ℝ) ^ 2 ≤ 3869361)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.662 (r1y (2 * 10 ^ 26)) 15.168611 1967.069 3869361 (by norm_num) (by
      linarith) hlr
    (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.662 (r1y (2 * 10 ^ 26)) (by norm_num) (by linarith)
  have hF := f2_le_4
  have hF0 := f2_nonneg (2 * 10 ^ 26) (by norm_num)
  have hC := coefC_le (98 * 10 ^ 26) 64.4523 (by norm_num) log_98e26_le
  have hC0 := coefC_nonneg (98 * 10 ^ 26) (by norm_num)
  have hL : fel (98 * 10 ^ 26) ≤ 0.640209 * 64.4523 - 0.021095 := by
    unfold fel
    linarith [log_98e26_le]
  have hL0 := fel_nonneg (98 * 10 ^ 26) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-! ## (11) What is still OPEN: `T1Anti`, `RKTail`, `F2Tail` -/

/-- **`MNumAt 8.36 0.785` from the three links still OPEN**: `mnumAt_of_open` with every numeric
sub-link supplied by the certified evaluations of section (10). Application only. -/
theorem mnumAt_of_open3 (ta : T1Anti) (rkt : RKTail (2 * 10 ^ 26) 0.72)
    (ft : F2Tail (2 * 10 ^ 26) 0.0039) : MNumAt 8.36 0.785 :=
  mnumAt_of_open ta rkt rkNum_01 rkNum_02 rkNum_03 rkNum_04 rkNum_11 rkNum_12 rkNum_13 rkNum_21
    rkNum_22 rkNum_23 rkNum_24 g0Num_1 g0Num_2 g0Num_3 g0Num_4 t1EnvNum_1 t1EnvNum_2 t1EnvNum_3
    t1EnvNum_4 iBlkNum_1 iBlkNum_2 iBlkNum_3 ft iTailNum

/-- **`MinW.MNumW HW.phi 0.785` from the three links still OPEN.** Application only. -/
theorem mnumW_of_open3 (ta : T1Anti) (rkt : RKTail (2 * 10 ^ 26) 0.72)
    (ft : F2Tail (2 * 10 ^ 26) 0.0039) : MinW.MNumW HW.phi 0.785 :=
  mnumW_of_at (mnumAt_of_open3 ta rkt ft)

/-! ## (12) DISCHARGED: `F2Tail` and `RKTail` -/

/-- `log r₁(y) = log(3/8) + (4/15) log y`. -/
theorem log_r1y (y : ℝ) (hy : 0 < y) :
    Real.log (r1y y) = Real.log (3 / 8) + 4 / 15 * Real.log y := by
  unfold r1y
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hy]

/-- **`K⁷/y` decreases** on `y ≥ y_X` once `log y_X ≥ 14` (`log(K/K_X) ≤ K/K_X − 1`). -/
theorem k7_anti (yX y : ℝ) (hX : 0 < yX) (h14 : 14 ≤ Real.log yX) (h : yX ≤ y) :
    kK y ^ 7 / y ≤ kK yX ^ 7 / yX := by
  have hy : 0 < y := lt_of_lt_of_le hX h
  have hv : Real.log yX ≤ Real.log y := Real.log_le_log hX h
  have hK0 : 0 < kK yX := by
    unfold kK
    linarith
  have hK : 0 < kK y := by
    unfold kK
    linarith
  have hv0 : Real.log yX ≠ 0 := (by linarith : (0 : ℝ) < Real.log yX).ne'
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_div (by positivity) hy.ne',
    Real.log_div (by positivity) hX.ne', Real.log_pow, Real.log_pow]
  have h1 := Real.log_le_sub_one_of_pos (div_pos hK hK0)
  rw [Real.log_div hK.ne' hK0.ne'] at h1
  have e : kK y / kK yX - 1 = (Real.log y - Real.log yX) / Real.log yX := by
    unfold kK
    field_simp
  rw [e] at h1
  have h2 : (Real.log y - Real.log yX) / Real.log yX ≤ (Real.log y - Real.log yX) / 14 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) h14
  push_cast
  linarith

/-- **[F2Tail] DISCHARGED** at `(2·10²⁶, 0.0039)`: `log(r₁/r₀) ≤ (8/15)K`, and
`(K/y)^{1/6}K = (K⁷/y)^{1/6}` with `K⁷/y` decreasing, `≤ 1.1663·10⁻¹⁶ ≤ 0.002285⁶` at `2·10²⁶`:
`3.2·(8/15)·0.002285 = 0.0038997`. -/
theorem f2Tail : F2Tail (2 * 10 ^ 26) 0.0039 := by
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hy25 : (10 : ℝ) ^ 25 ≤ y := le_trans (by norm_num) hy
  have hl := log_ge_one_y y hy25
  have hK0 : 0 ≤ kK y := by
    unfold kK
    linarith
  have hKy0 : 0 ≤ kK y / y := div_nonneg hK0 hy0.le
  have hbr : Real.log (r1y y) - Real.log 150000 ≤ 8 / 15 * kK y := by
    rw [log_r1y y hy0]
    have h1 : Real.log (3 / 8) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    have h2 : 0 ≤ Real.log 150000 := Real.log_nonneg (by norm_num)
    unfold kK
    linarith
  have hX := lya_le_4
  have hXl := lya_ge_4
  have hKX0 : 0 ≤ kK (2 * 10 ^ 26) := by
    unfold kK
    linarith
  have hKX : kK (2 * 10 ^ 26) ≤ 60.56036 / 2 := by
    unfold kK
    linarith
  have hnum : kK (2 * 10 ^ 26) ^ 7 / (2 * 10 ^ 26) ≤ 0.002285 ^ 6 := by
    calc kK (2 * 10 ^ 26) ^ 7 / (2 * 10 ^ 26) ≤ (60.56036 / 2) ^ 7 / (2 * 10 ^ 26) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hKX0 hKX 7) (by norm_num)
      _ ≤ 0.002285 ^ 6 := by norm_num
  have hK7 := (k7_anti (2 * 10 ^ 26) y (by norm_num) (le_trans (by norm_num) hXl) hy).trans hnum
  have hq : (kK y / y) ^ ((1 : ℝ) / 6) * kK y ≤ 0.002285 := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by norm_num) ?_
    rw [mul_pow, show (1 : ℝ) / 6 = ((6 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow hKy0 (by norm_num)]
    calc kK y / y * kK y ^ 6 = kK y ^ 7 / y := by ring
      _ ≤ 0.002285 ^ 6 := hK7
  rw [f2_eq y (by linarith)]
  have hf0 : 0 ≤ 3.2 * (kK y / y) ^ ((1 : ℝ) / 6) := by
    have := Real.rpow_nonneg hKy0 ((1 : ℝ) / 6)
    positivity
  calc 3.2 * (kK y / y) ^ ((1 : ℝ) / 6) * (Real.log (r1y y) - Real.log 150000)
      ≤ 3.2 * (kK y / y) ^ ((1 : ℝ) / 6) * (8 / 15 * kK y) :=
        mul_le_mul_of_nonneg_left hbr hf0
    _ = 3.2 * (8 / 15) * ((kK y / y) ^ ((1 : ℝ) / 6) * kK y) := by ring
    _ ≤ 3.2 * (8 / 15) * 0.002285 := mul_le_mul_of_nonneg_left hq (by norm_num)
    _ ≤ 0.0039 := by norm_num

/-- `log 3 ≤ 1.0986123` (truth `1.09861229`). -/
theorem log3_le : Real.log 3 ≤ 1.0986123 := by
  have h := log_le_series 3 0.25 2 15 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 1.503 ≤ 0.4074632` (truth `0.40746311`). -/
theorem log1503_le : Real.log 1.503 ≤ 0.4074632 := by
  have h := log_le_series 1.503 0.2485 1 15 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 130 ≤ 4.8675345` (truth `4.86753445`). -/
theorem log130_le : Real.log 130 ≤ 4.8675345 := by
  have h := log_le_series 130 (-0.015625) 7 6 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 3.08 ≤ 1.12494` (truth `1.12492960`). -/
theorem log308_le : Real.log 3.08 ≤ 1.12494 := by
  have h := log_le_series 3.08 0.23 2 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **One `R` on the tail**: `R_{z,2r} ≤ 0.72` when `r₀ ≤ r ≤ r₁(y)`, `log z ≥ L_z` and
`D_l = log 9 − log 1.503 + L_z/3 − (4/15)log y` satisfies `0 < D_l`,
`log 3 + (4/15)log y ≤ 4.16D_l` (then the ratio inside `R` is `≤ 2.08`, and
`0.27125 log 3.08 + 0.41415 = 0.71929`). -/
theorem rR_tail (z y r Lz : ℝ) (hy1 : 1 ≤ y) (hz : 0 < z) (hr0 : 150000 ≤ r)
    (hr : r ≤ r1y y) (hLz : Lz ≤ Real.log z)
    (hpos : 0 < Real.log 9 - Real.log 1.503 + Lz / 3 - 4 / 15 * Real.log y)
    (hmain : Real.log 3 + 4 / 15 * Real.log y ≤
      4.16 * (Real.log 9 - Real.log 1.503 + Lz / 3 - 4 / 15 * Real.log y)) :
    rR z (2 * r) ≤ 0.72 := by
  have hy : 0 < y := by linarith
  have hr0' : 0 < r := by linarith
  have hry : 0 < y ^ ((4 : ℝ) / 15) := by positivity
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hA : Real.log (4 * (2 * r)) ≤ Real.log 3 + 4 / 15 * Real.log y := by
    have h1 : 4 * (2 * r) ≤ 3 * y ^ ((4 : ℝ) / 15) := by
      unfold r1y at hr
      linarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by norm_num) hry.ne', Real.log_rpow hy] at this
  have hE : Real.log (2.004 * (2 * r)) ≤ Real.log 1.503 + 4 / 15 * Real.log y := by
    have h1 : 2.004 * (2 * r) ≤ 1.503 * y ^ ((4 : ℝ) / 15) := by
      unfold r1y at hr
      linarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by norm_num) hry.ne', Real.log_rpow hy] at this
  set A1 := Real.log 3 + 4 / 15 * Real.log y with hA1
  set D1 := Real.log 9 - Real.log 1.503 + Lz / 3 - 4 / 15 * Real.log y with hD1
  have hD : D1 ≤ Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))) := by
    rw [logD_eq z _ hz (by positivity)]
    linarith [hD1]
  have hq : A1 / (2 * D1) ≤ 2.08 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [hA1, hD1]
  have hq0 : 0 ≤ A1 / (2 * D1) := div_nonneg (by linarith [hA1]) (by linarith)
  have hU : Real.log (1 + A1 / (2 * D1)) ≤ 1.12494 :=
    (Real.log_le_log (by linarith) (by linarith : 1 + A1 / (2 * D1) ≤ 3.08)).trans log308_le
  have := rR_le z (2 * r) A1 D1 1.12494 (by linarith) hA hpos hD hU
  linarith

/-- **[RKTail] DISCHARGED** at `(2·10²⁶, 0.72)`: for `y ≥ 2·10²⁶`, `r₀ ≤ r ≤ r₁(y)`, both
`R_{y,2r}` and `R_{y/K,2r}` are `≤ 0.72` (`rR_tail`; for `y/K` with `log K ≤ log 130 − 1 +
(log y)/260`, the tangent of `log` at `130`), and the mixing weight is in `[0, 1]`. -/
theorem rkTail : RKTail (2 * 10 ^ 26) 0.72 := by
  intro y r hy hr0 hr
  have hy25 : (10 : ℝ) ^ 25 ≤ y := le_trans (by norm_num) hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hy1 : 1 ≤ y := le_trans (by norm_num) hy
  have hK := kK_ge y hy25
  have hl9 := log9_ge
  have hl3 := log3_le
  have hl15 := log1503_le
  have hv := lya_ge_4.trans (Real.log_le_log (by norm_num) hy)
  have hRy : rR y (2 * r) ≤ 0.72 :=
    rR_tail y y r (Real.log y) hy1 hy0 hr0 hr le_rfl (by linarith) (by linarith)
  have hKpos : 0 < kK y := by linarith
  have hlogK : Real.log (kK y) ≤ 4.8675345 - 1 + Real.log y / 260 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hKpos (by norm_num : (0 : ℝ) < 130))
    rw [Real.log_div hKpos.ne' (by norm_num)] at h1
    have h130 := log130_le
    unfold kK at h1 ⊢
    linarith
  have hz0 : 0 < y / kK y := div_pos hy0 hKpos
  have hLz : Real.log y - (4.8675345 - 1 + Real.log y / 260) ≤ Real.log (y / kK y) := by
    rw [Real.log_div hy0.ne' hKpos.ne']
    linarith
  have hRz : rR (y / kK y) (2 * r) ≤ 0.72 :=
    rR_tail _ y r _ hy1 hz0 hr0 hr hLz (by linarith) (by linarith)
  obtain ⟨hc0, hc1, hcm⟩ := cmix_le y y hy25 le_rfl
  unfold rRK
  set c := cPhi2 HW.phi (kK y) / MajSp.l1 HW.phi / Real.log (kK y)
  nlinarith [mul_nonneg (sub_nonneg.2 (hc1.trans hcm)) (sub_nonneg.2 hRy),
    mul_nonneg hc0 (sub_nonneg.2 hRz)]

/-- **`MNumAt 8.36 0.785` from the ONE link still OPEN, `T1Anti`.** Application only. -/
theorem mnumAt_of_t1Anti (ta : T1Anti) : MNumAt 8.36 0.785 := mnumAt_of_open3 ta rkTail f2Tail

/-- **`MinW.MNumW HW.phi 0.785` from `T1Anti`.** Application only. -/
theorem mnumW_of_t1Anti (ta : T1Anti) : MinW.MNumW HW.phi 0.785 :=
  mnumW_of_at (mnumAt_of_t1Anti ta)

/-! ## (13) The `T₁` envelope route: `EnvAnti`, the region bounds, the far tail -/

/-- `envQ` in the variable `ℓ = log r`. -/
noncomputable def envE (ρ l : ℝ) : ℝ :=
  0.70711 * pA ρ l * Real.exp (-(1 / 2) * l) + qA l * Real.exp (-1 * l)

/-- The `ℓ`-derivative of `envE`: `0.70711(P′ − P/2)e^{−ℓ/2} + (Q′ − Q)e^{−ℓ}`. -/
theorem hasDerivAt_envE (ρ l : ℝ) :
    HasDerivAt (envE ρ) (0.70711 * (dpA ρ l - pA ρ l / 2) * Real.exp (-(1 / 2) * l) +
      (dqA l - qA l) * Real.exp (-1 * l)) l := by
  have h1 := (hasDerivAt_quad_exp ((ρ * 0.6931471808 + 0.5) * 1.949682 + 2.5)
    (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156) (ρ * 0.032156) (-(1 / 2)) l).const_mul
    0.70711
  have h2 := hasDerivAt_quad_exp
    (3.6544 * (7 / 4 * 0.6931471808 + 80 / 9) + 16 / 9 * 0.6931471808 + 111 / 5)
    (3.6544 * (13 / 4) + 0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 80 / 9)
    (0.15003 * (13 / 4)) (-1) l
  have e : envE ρ = fun l => 0.70711 * (((ρ * 0.6931471808 + 0.5) * 1.949682 + 2.5 +
      (ρ * 1.949682 + (ρ * 0.6931471808 + 0.5) * 0.032156) * l + ρ * 0.032156 * l ^ 2) *
        Real.exp (-(1 / 2) * l)) +
      ((3.6544 * (7 / 4 * 0.6931471808 + 80 / 9) + 16 / 9 * 0.6931471808 + 111 / 5 +
        (3.6544 * (13 / 4) + 0.15003 * (7 / 4 * 0.6931471808 + 80 / 9) + 80 / 9) * l +
          0.15003 * (13 / 4) * l ^ 2) * Real.exp (-1 * l)) := by
    funext l
    unfold envE pA qA
    ring
  rw [e]
  refine (h1.add h2).congr_deriv ?_
  unfold dpA pA dqA qA
  ring

/-- `envQ ρ r = envE ρ (log r)` for `r > 0`. -/
theorem envQ_eq_E (ρ r : ℝ) (hr : 0 < r) : envQ ρ r = envE ρ (Real.log r) := envQ_eq ρ r hr

/-- **The derivative of `envE` is `≤ 0`** for `ℓ ≥ 11`, `ρ ≥ 0`. -/
theorem envE_deriv_nonpos (ρ l : ℝ) (hρ0 : 0 ≤ ρ) (hl : 11 ≤ l) :
    0.70711 * (dpA ρ l - pA ρ l / 2) * Real.exp (-(1 / 2) * l) +
      (dqA l - qA l) * Real.exp (-1 * l) ≤ 0 := by
  have key : 0 ≤ (0.6931471808 + l) * ((1.949682 + 0.032156 * l) / 2 - 0.032156) -
      (1.949682 + 0.032156 * l) := by nlinarith
  have hP : dpA ρ l - pA ρ l / 2 ≤ 0 := by
    unfold dpA pA
    nlinarith [mul_nonneg hρ0 key]
  have hQ : dqA l - qA l ≤ 0 := by
    unfold dqA qA
    nlinarith
  have e1 := Real.exp_pos (-(1 / 2) * l)
  have e2 := Real.exp_pos (-1 * l)
  have t1 : 0.70711 * (dpA ρ l - pA ρ l / 2) * Real.exp (-(1 / 2) * l) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) e1.le
  have t2 : (dqA l - qA l) * Real.exp (-1 * l) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hQ e2.le
  linarith

/-- **[EnvAnti] DISCHARGED**: `envQ ρ` decreases on `r ≥ r₀` for every `ρ ≥ 0`. -/
theorem envAnti : EnvAnti := by
  intro ρ r r' hρ0 hr h
  have hr0 : 0 < r := by linarith
  have hl : 11 ≤ Real.log r := le_trans (by norm_num) (log_r0_ge.trans
    (Real.log_le_log (by norm_num) hr))
  have hll : Real.log r ≤ Real.log r' := Real.log_le_log hr0 h
  have hanti : AntitoneOn (envE ρ) (Set.Ici 11) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro l _
      exact (hasDerivAt_envE ρ l).continuousAt.continuousWithinAt
    · intro l _
      exact (hasDerivAt_envE ρ l).differentiableAt.differentiableWithinAt
    · intro l hl'
      rw [interior_Ici] at hl'
      simp only [Set.mem_Ioi] at hl'
      rw [(hasDerivAt_envE ρ l).deriv]
      exact envE_deriv_nonpos ρ l hρ0 hl'.le
  rw [envQ_eq_E ρ r hr0, envQ_eq_E ρ r' (by linarith)]
  exact hanti (Set.mem_Ici.mpr hl) (Set.mem_Ici.mpr (hl.trans hll)) hll

/-- `felipa` increases in `x`. -/
theorem fel_mono (x x' : ℝ) (hx : 0 < x) (h : x ≤ x') : fel x ≤ fel x' := by
  have := Real.log_le_log hx h
  unfold fel
  linarith

/-- `coefC` increases in `x` on `x ≥ 4.9·10²⁶` (its numerator `−2.14938 + (8/15) log 49` is
negative). -/
theorem coefC_mono (x x' : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (h : x ≤ x') : coefC x ≤ coefC x' := by
  have hL := LW.log_ge_of x hx
  have hL' := Real.log_le_log (lt_of_lt_of_le (by norm_num) hx) h
  have h49 := LW.log_49_le
  unfold coefC
  have hd : 0 < Real.log x + 2 * 0.6294 := by linarith
  have hd' : 0 < Real.log x' + 2 * 0.6294 := by linarith
  have : (-2.14938 + 8 / 15 * Real.log 49) / (Real.log x + 2 * 0.6294) ≤
      (-2.14938 + 8 / 15 * Real.log 49) / (Real.log x' + 2 * 0.6294) := by
    rw [div_le_div_iff₀ hd hd']
    nlinarith
  linarith

/-- **The region bound for `T₁` from the envelope**: for `x ∈ [49y_a, 49y_b]`,
`t1(x) ≤ coefC(x_b)(envQ ρ r₁(y_a) + f₂(y_a)) felipa(x_b)` once `R_{y,K,φ,2r₁(y)} ≤ ρ` on the
block (`EnvPt` at `r = r₁(y)`, `EnvAnti`, `F2Anti`, `coefC`, `felipa` increasing). -/
theorem t1Reg_of_env (xa xb ya yb ρ T : ℝ) (hxa : xa = 49 * ya) (hxb : xb = 49 * yb)
    (hya : 10 ^ 25 ≤ ya) (hρ0 : 0 ≤ ρ)
    (hrk : ∀ y : ℝ, ya ≤ y → y ≤ yb → rRK HW.phi y (2 * r1y y) ≤ ρ)
    (hn : T1BNum xb ya ρ T) : T1Reg xa xb T := by
  intro x hx1 hx2
  have hya' : ya ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hyb' : x / 49 ≤ yb := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hy25 : 10 ^ 25 ≤ x / 49 := hya.trans hya'
  have hx : 49 * 10 ^ 25 ≤ x := by
    have := (le_div_iff₀ (by norm_num : (0 : ℝ) < 49)).mp hy25
    linarith
  have hr0 := r1y_ge (x / 49) hy25
  have hg := envPt ρ (x / 49) (r1y (x / 49)) hρ0 hr0 (hrk (x / 49) hya' hyb')
  have hE := envAnti ρ (r1y ya) (r1y (x / 49)) hρ0 (r1y_ge ya hya)
    (r1y_mono ya (x / 49) (by linarith) hya')
  have hF := f2Anti ya (x / 49) hya hya'
  have hC := coefC_mono x xb hx hx2
  have hL := fel_mono x xb (by linarith) hx2
  have hC0 := coefC_nonneg x hx
  have hL0 := fel_nonneg x hx
  have hEy0 : 0 ≤ envQ ρ (r1y ya) + f2 ya :=
    add_nonneg (envQ_nonneg ρ _ hρ0 (by linarith [r1y_ge ya hya])) (f2_nonneg ya (by linarith))
  unfold T1BNum at hn
  unfold t1
  calc coefC x * gB HW.phi (x / 49) (r1y (x / 49)) * fel x
      = (coefC x * fel x) * gB HW.phi (x / 49) (r1y (x / 49)) := by ring
    _ ≤ (coefC x * fel x) * (envQ ρ (r1y ya) + f2 ya) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hL0)
    _ ≤ (coefC xb * fel xb) * (envQ ρ (r1y ya) + f2 ya) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hC hL hL0 (le_trans hC0 hC)) hEy0
    _ = coefC xb * (envQ ρ (r1y ya) + f2 ya) * fel xb := by ring
    _ ≤ T := hn

/-- The ceiling `R ≤ ρ` at `t = 2r₁(y)` on a block, from `RKBnd y_a t_b ρ` and `r₁(y_b) ≤ t_b/2`. -/
theorem rk_r1 (ya yb tb R ρ : ℝ) (hya : 10 ^ 25 ≤ ya) (hb : RKBnd ya tb ρ)
    (hR : R1Le yb R) (htb : 2 * R ≤ tb) :
    ∀ y : ℝ, ya ≤ y → y ≤ yb → rRK HW.phi y (2 * r1y y) ≤ ρ := by
  intro y hy hyb
  unfold R1Le at hR
  have h0 := r1y_ge y (hya.trans hy)
  have h1 := r1y_mono y yb (by linarith) hyb
  exact hb y (2 * r1y y) hy (by linarith) (by linarith)

/-- `log(4.9·10²⁸) ≤ 66.061618` (truth `66.0616178`). -/
theorem log_4927_le : Real.log (49 * 10 ^ 27) ≤ 66.061618 := by
  have h := log_le_series (49 * 10 ^ 27) (-0.236934) 95 17 (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **[T1BNum] DISCHARGED** at `(1.47·10²⁷, 10²⁵, 0.672, 0.2955)` (value `≤ 0.2930928`). -/
theorem t1BNum_1 : T1BNum (147 * 10 ^ 25) (10 ^ 25) 0.672 0.2955 := by
  unfold T1BNum
  have hr1 : r1y (10 ^ 25) ≤ 1740600 := r1Le_1
  have hrl : (1740595 : ℝ) ≤ r1y (10 ^ 25) :=
    r1_ge_of _ _ (by norm_num) (by norm_num) (by norm_num)
  have hlr : Real.log (r1y (10 ^ 25)) ≤ 14.369741 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_1
  have hs : 1319.316 ≤ Real.sqrt (r1y (10 ^ 25)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1319.316 : ℝ) ^ 2 ≤ 1740595)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.672 (r1y (10 ^ 25)) 14.369741 1319.316 1740595 (by norm_num)
    (by linarith) hlr (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.672 (r1y (10 ^ 25)) (by norm_num) (by linarith)
  have hF := f2_le_1
  have hF0 := f2_nonneg (10 ^ 25) (by norm_num)
  have hC := coefC_le (147 * 10 ^ 25) 62.5552 (by norm_num) log_147e25_le
  have hL : fel (147 * 10 ^ 25) ≤ 0.640209 * 62.5552 - 0.021095 := by
    unfold fel
    linarith [log_147e25_le]
  have hL0 := fel_nonneg (147 * 10 ^ 25) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- **[T1BNum] DISCHARGED** at `(4.9·10²⁷, 3·10²⁵, 0.674, 0.2665)` (value `≤ 0.2630309`). -/
theorem t1BNum_2 : T1BNum (49 * 10 ^ 26) (3 * 10 ^ 25) 0.674 0.2665 := by
  unfold T1BNum
  have hr1 : r1y (3 * 10 ^ 25) ≤ 2333100 := r1Le_2
  have hrl : (2333083 : ℝ) ≤ r1y (3 * 10 ^ 25) :=
    r1_ge_of _ _ (by norm_num) (by norm_num) (by norm_num)
  have hlr : Real.log (r1y (3 * 10 ^ 25)) ≤ 14.662709 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_2
  have hs : 1527.443 ≤ Real.sqrt (r1y (3 * 10 ^ 25)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1527.443 : ℝ) ^ 2 ≤ 2333083)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.674 (r1y (3 * 10 ^ 25)) 14.662709 1527.443 2333083 (by norm_num)
    (by linarith) hlr (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.674 (r1y (3 * 10 ^ 25)) (by norm_num) (by linarith)
  have hF := f2_le_2
  have hF0 := f2_nonneg (3 * 10 ^ 25) (by norm_num)
  have hC := coefC_le (49 * 10 ^ 26) 63.7592 (by norm_num) log_49e26_le
  have hL : fel (49 * 10 ^ 26) ≤ 0.640209 * 63.7592 - 0.021095 := by
    unfold fel
    linarith [log_49e26_le]
  have hL0 := fel_nonneg (49 * 10 ^ 26) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- **[T1BNum] DISCHARGED** at `(9.8·10²⁷, 10²⁶, 0.669, 0.2325)` (value `≤ 0.2292232`). -/
theorem t1BNum_3 : T1BNum (98 * 10 ^ 26) (10 ^ 26) 0.669 0.2325 := by
  unfold T1BNum
  have hr1 : r1y (10 ^ 26) ≤ 3216400 := r1Le_3
  have hrl : (3216359 : ℝ) ≤ r1y (10 ^ 26) :=
    r1_ge_of _ _ (by norm_num) (by norm_num) (by norm_num)
  have hlr : Real.log (r1y (10 ^ 26)) ≤ 14.983774 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_3
  have hs : 1793.421 ≤ Real.sqrt (r1y (10 ^ 26)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1793.421 : ℝ) ^ 2 ≤ 3216359)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.669 (r1y (10 ^ 26)) 14.983774 1793.421 3216359 (by norm_num)
    (by linarith) hlr (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.669 (r1y (10 ^ 26)) (by norm_num) (by linarith)
  have hF := f2_le_3
  have hF0 := f2_nonneg (10 ^ 26) (by norm_num)
  have hC := coefC_le (98 * 10 ^ 26) 64.4523 (by norm_num) log_98e26_le
  have hL : fel (98 * 10 ^ 26) ≤ 0.640209 * 64.4523 - 0.021095 := by
    unfold fel
    linarith [log_98e26_le]
  have hL0 := fel_nonneg (98 * 10 ^ 26) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- **[T1BNum] DISCHARGED** at `(4.9·10²⁸, 2·10²⁶, 0.72, 0.235)` (value `≤ 0.2304542`). -/
theorem t1BNum_4 : T1BNum (49 * 10 ^ 27) (2 * 10 ^ 26) 0.72 0.235 := by
  unfold T1BNum
  have hr1 : r1y (2 * 10 ^ 26) ≤ 3869400 := r1Le_4
  have hrl : (3869361 : ℝ) ≤ r1y (2 * 10 ^ 26) :=
    r1_ge_of _ _ (by norm_num) (by norm_num) (by norm_num)
  have hlr : Real.log (r1y (2 * 10 ^ 26)) ≤ 15.168611 :=
    (Real.log_le_log (by linarith) hr1).trans lr1_le_4
  have hs : 1967.069 ≤ Real.sqrt (r1y (2 * 10 ^ 26)) :=
    (sqrt_ge_of _ _ (by norm_num) (by norm_num : (1967.069 : ℝ) ^ 2 ≤ 3869361)).trans
      (Real.sqrt_le_sqrt hrl)
  have hE := envQ_le 0.72 (r1y (2 * 10 ^ 26)) 15.168611 1967.069 3869361 (by norm_num)
    (by linarith) hlr (by norm_num) hs (by norm_num) hrl
  have hE0 := envQ_nonneg 0.72 (r1y (2 * 10 ^ 26)) (by norm_num) (by linarith)
  have hF := f2_le_4
  have hF0 := f2_nonneg (2 * 10 ^ 26) (by norm_num)
  have hC := coefC_le (49 * 10 ^ 27) 66.061618 (by norm_num) log_4927_le
  have hL : fel (49 * 10 ^ 27) ≤ 0.640209 * 66.061618 - 0.021095 := by
    unfold fel
    linarith [log_4927_le]
  have hL0 := fel_nonneg (49 * 10 ^ 27) (by norm_num)
  have hS := add_le_add hE hF
  have hP := mul_le_mul (mul_le_mul hC hS (add_nonneg hE0 hF0) (by norm_num)) hL hL0
    (by unfold pA qA; norm_num)
  refine hP.trans ?_
  unfold pA qA
  norm_num

/-- **`K^m/y^n` decreases** on `y ≥ y_X` once `m ≤ n log y_X` (`log(K/K_X) ≤ K/K_X − 1`). -/
theorem km_anti (m n : ℕ) (yX y : ℝ) (hX : 0 < yX) (h1 : 1 ≤ Real.log yX)
    (hm : (m : ℝ) ≤ n * Real.log yX) (h : yX ≤ y) :
    kK y ^ m / y ^ n ≤ kK yX ^ m / yX ^ n := by
  have hy : 0 < y := lt_of_lt_of_le hX h
  have hv : Real.log yX ≤ Real.log y := Real.log_le_log hX h
  have hK0 : 0 < kK yX := by
    unfold kK
    linarith
  have hK : 0 < kK y := by
    unfold kK
    linarith
  have hv0 : Real.log yX ≠ 0 := (by linarith : (0 : ℝ) < Real.log yX).ne'
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_div (by positivity)
    (by positivity), Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow]
  have ht := Real.log_le_sub_one_of_pos (div_pos hK hK0)
  rw [Real.log_div hK.ne' hK0.ne'] at ht
  have e : kK y / kK yX - 1 = (Real.log y - Real.log yX) / Real.log yX := by
    unfold kK
    field_simp
  rw [e] at ht
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 : (m : ℝ) * ((Real.log y - Real.log yX) / Real.log yX) ≤
      n * (Real.log y - Real.log yX) := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hm (sub_nonneg.2 hv)]
  have h3 := mul_le_mul_of_nonneg_left ht hm0
  linarith

/-- `log 10²⁷ ∈ [62.169796, 62.169799]` (truth `62.1697975`). -/
theorem log_1e27 : 62.169796 ≤ Real.log (10 ^ 27) ∧ Real.log (10 ^ 27) ≤ 62.169799 := by
  constructor
  · have h := le_log_series (10 ^ 27) 0.192207 90 15 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  · have h := log_le_series (10 ^ 27) 0.192206 90 15 (by norm_num) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith

/-- `P(ℓ) ≤ 0.126ℓ²` at `ρ = 0.72` for `ℓ ≥ 16.5786`. -/
theorem pA_quad_le (l : ℝ) (hl : 16.5786 ≤ l) : pA 0.72 l ≤ 0.126 * l ^ 2 := by
  unfold pA
  nlinarith [sq_nonneg (l - 16.5786)]

/-- `Q(ℓ) ≤ 2.052ℓ²` for `ℓ ≥ 16.5786`. -/
theorem qA_quad_le (l : ℝ) (hl : 16.5786 ≤ l) : qA l ≤ 2.052 * l ^ 2 := by
  unfold qA
  nlinarith [sq_nonneg (l - 16.5786)]

/-- `s = y^{2/15}` facts for `y ≥ 10²⁷`: `s ≥ 3981`, `r₁(y) = (3/8)s²`, `s¹⁵ = y²`. -/
theorem far_s (y : ℝ) (hyY : 10 ^ 27 ≤ y) :
    3981 ≤ y ^ ((2 : ℝ) / 15) ∧ r1y y = 3 / 8 * (y ^ ((2 : ℝ) / 15)) ^ 2 ∧
      (y ^ ((2 : ℝ) / 15)) ^ 15 = y ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  refine ⟨?_, ?_, ?_⟩
  · have h := le_rpow_of_pow y 3981 2 15 (by norm_num) hy0.le (by norm_num)
      (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hyY 2))
    rwa [show ((2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ) = 2 / 15 by norm_num] at h
  · unfold r1y
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num

/-- **The envelope on the far tail**: `envQ 0.72 r₁(y) ≤ C(64/225)K²/y^{2/15}` for `y ≥ 10²⁷`,
`C = 0.70711·0.126/0.61237 + 2.052/((3/8)3981)`. -/
theorem far_env (y : ℝ) (hyY : 10 ^ 27 ≤ y) :
    envQ 0.72 (r1y y) ≤ (0.70711 * 0.126 / 0.61237 + 2.052 / (3 / 8 * 3981)) * (64 / 225) *
      kK y ^ 2 / y ^ ((2 : ℝ) / 15) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  have hy25 : 10 ^ 25 ≤ y := le_trans (by norm_num) hyY
  have hr0 := r1y_ge y hy25
  obtain ⟨hsY, hr1, -⟩ := far_s y hyY
  obtain ⟨hYl, -⟩ := log_1e27
  have hv : 62.169796 ≤ Real.log y := hYl.trans (Real.log_le_log (by norm_num) hyY)
  have hK : 31.084898 ≤ kK y := by
    unfold kK
    linarith
  have hs0 : 0 < y ^ ((2 : ℝ) / 15) := by linarith
  have hsq : 0.61237 * y ^ ((2 : ℝ) / 15) ≤ Real.sqrt (r1y y) := by
    rw [hr1, Real.sqrt_mul (by norm_num) ((y ^ ((2 : ℝ) / 15)) ^ 2), Real.sqrt_sq hs0.le]
    have : (0.61237 : ℝ) ≤ Real.sqrt (3 / 8) := sqrt_ge_of _ _ (by norm_num) (by norm_num)
    nlinarith
  have hr1s : 3 / 8 * 3981 * y ^ ((2 : ℝ) / 15) ≤ r1y y := by
    rw [hr1]
    nlinarith
  have hl0 : 0 ≤ Real.log (r1y y) := Real.log_nonneg (by linarith)
  have hlK : Real.log (r1y y) ≤ 8 / 15 * kK y := by
    rw [log_r1y y hy0]
    have : Real.log (3 / 8) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    unfold kK
    linarith
  have hlam : 16.5786 ≤ 8 / 15 * kK y := by linarith
  obtain ⟨hp0, hp⟩ := pA_mono 0.72 _ _ (by norm_num) hl0 hlK
  obtain ⟨hq0, hq⟩ := qA_mono _ _ hl0 hlK
  have haP := pA_quad_le _ hlam
  have haQ := qA_quad_le _ hlam
  unfold envQ
  have t1 : 0.70711 * pA 0.72 (Real.log (r1y y)) / Real.sqrt (r1y y) ≤
      0.70711 * (0.126 * (8 / 15 * kK y) ^ 2) / (0.61237 * y ^ ((2 : ℝ) / 15)) :=
    div_le_div₀ (by positivity) (by linarith) (by positivity) hsq
  have t2 : qA (Real.log (r1y y)) / r1y y ≤
      2.052 * (8 / 15 * kK y) ^ 2 / (3 / 8 * 3981 * y ^ ((2 : ℝ) / 15)) :=
    div_le_div₀ (by positivity) (by linarith) (by positivity) hr1s
  have e : 0.70711 * (0.126 * (8 / 15 * kK y) ^ 2) / (0.61237 * y ^ ((2 : ℝ) / 15)) +
      2.052 * (8 / 15 * kK y) ^ 2 / (3 / 8 * 3981 * y ^ ((2 : ℝ) / 15)) =
      (0.70711 * 0.126 / 0.61237 + 2.052 / (3 / 8 * 3981)) * (64 / 225) * kK y ^ 2 /
        y ^ ((2 : ℝ) / 15) := by
    ring
  linarith

/-- **`K³/y^{2/15} ≤ 7.54482`** for `y ≥ 10²⁷` (`K⁴⁵/y²` decreases). -/
theorem far_q1 (y : ℝ) (hyY : 10 ^ 27 ≤ y) : kK y ^ 3 / y ^ ((2 : ℝ) / 15) ≤ 7.54482 := by
  obtain ⟨-, -, hs15⟩ := far_s y hyY
  obtain ⟨hYl, hYu⟩ := log_1e27
  have hK45 : kK y ^ 45 / y ^ 2 ≤ kK (10 ^ 27) ^ 45 / (10 ^ 27) ^ 2 :=
    km_anti 45 2 (10 ^ 27) y (by norm_num) (le_trans (by norm_num) hYl)
      (by push_cast; exact le_trans (by norm_num) (mul_le_mul_of_nonneg_left hYl (by norm_num)))
      hyY
  have hKY0 : 0 ≤ kK (10 ^ 27) := by
    unfold kK
    linarith
  have hKYu : kK (10 ^ 27) ≤ 62.169799 / 2 := by
    unfold kK
    linarith
  refine le_of_pow_le_pow_left₀ (by norm_num : (15 : ℕ) ≠ 0) (by norm_num) ?_
  rw [div_pow, hs15, ← pow_mul]
  calc kK y ^ (3 * 15) / y ^ 2 ≤ kK (10 ^ 27) ^ 45 / (10 ^ 27) ^ 2 := hK45
    _ ≤ (62.169799 / 2) ^ 45 / (10 ^ 27) ^ 2 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hKY0 hKYu 45) (by norm_num)
    _ ≤ 7.54482 ^ 15 := by norm_num

/-- **`K(K/y)^{1/6} ≤ 0.00174305`** for `y ≥ 10²⁷` (`K⁷/y` decreases). -/
theorem far_q2 (y : ℝ) (hyY : 10 ^ 27 ≤ y) : (kK y / y) ^ ((1 : ℝ) / 6) * kK y ≤ 0.00174305 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hyY
  obtain ⟨hYl, hYu⟩ := log_1e27
  have hv : 62.169796 ≤ Real.log y := hYl.trans (Real.log_le_log (by norm_num) hyY)
  have hK0 : 0 ≤ kK y := by
    unfold kK
    linarith
  have hKY0 : 0 ≤ kK (10 ^ 27) := by
    unfold kK
    linarith
  have hKYu : kK (10 ^ 27) ≤ 62.169799 / 2 := by
    unfold kK
    linarith
  have hK7 : kK y ^ 7 / y ≤ kK (10 ^ 27) ^ 7 / 10 ^ 27 :=
    k7_anti (10 ^ 27) y (by norm_num) (le_trans (by norm_num) hYl) hyY
  have hKy0 : 0 ≤ kK y / y := div_nonneg hK0 hy0.le
  refine le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by norm_num) ?_
  rw [mul_pow, show (1 : ℝ) / 6 = ((6 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_natCast_pow hKy0 (by norm_num)]
  calc kK y / y * kK y ^ 6 = kK y ^ 7 / y := by ring
    _ ≤ kK (10 ^ 27) ^ 7 / 10 ^ 27 := hK7
    _ ≤ (62.169799 / 2) ^ 7 / 10 ^ 27 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hKY0 hKYu 7) (by norm_num)
    _ ≤ 0.00174305 ^ 6 := by norm_num

/-- **`coefC ≤ 7/15` and `felipa(x) ≤ 1.36065·K(x/49)`** for `x ≥ 4.9·10²⁸`. -/
theorem far_cf (x : ℝ) (hx : 49 * 10 ^ 27 ≤ x) :
    coefC x ≤ 7 / 15 ∧ fel x ≤ 1.36065 * kK (x / 49) := by
  have hx25 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hyY : 10 ^ 27 ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hy0 : 0 < x / 49 := lt_of_lt_of_le (by norm_num) hyY
  obtain ⟨hYl, -⟩ := log_1e27
  have hv : 62.169796 ≤ Real.log (x / 49) := hYl.trans (Real.log_le_log (by norm_num) hyY)
  have h49 := LW.log_49_le
  have hLx := LW.log_ge_of x hx25
  constructor
  · unfold coefC
    have : (-2.14938 + 8 / 15 * Real.log 49) / (Real.log x + 2 * 0.6294) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hlx : Real.log x = Real.log 49 + Real.log (x / 49) := by
      rw [← Real.log_mul (by norm_num) hy0.ne']
      congr 1
      ring
    unfold fel kK
    rw [hlx]
    linarith

/-- **The far tail of `T₁`, DISCHARGED**: `t1(x) ≤ 0.235` for `x ≥ 4.9·10²⁸`: with `K = (log y)/2`,
`coefC ≤ 7/15`, `felipa ≤ 1.36065K` (`far_cf`), `envQ 0.72 r₁ ≤ CK²/y^{2/15}` (`far_env`),
`K³/y^{2/15} ≤ 7.54482` (`far_q1`), `K(K/y)^{1/6} ≤ 0.00174305` (`far_q2`): value `0.2036785`. -/
theorem t1Far_crude : T1Far (49 * 10 ^ 27) 0.235 := by
  intro x hx
  have hx25 : 49 * 10 ^ 25 ≤ x := le_trans (by norm_num) hx
  have hyY : 10 ^ 27 ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hy0 : 0 < x / 49 := lt_of_lt_of_le (by norm_num) hyY
  have hy2 : 2 * 10 ^ 26 ≤ x / 49 := le_trans (by norm_num) hyY
  have hr0 := r1y_ge (x / 49) (le_trans (by norm_num) hyY)
  have hg := envPt 0.72 (x / 49) (r1y (x / 49)) (by norm_num) hr0
    (rkTail (x / 49) (r1y (x / 49)) hy2 hr0 le_rfl)
  have hE := far_env (x / 49) hyY
  have hq1 := far_q1 (x / 49) hyY
  have hq2 := far_q2 (x / 49) hyY
  obtain ⟨hC, hL⟩ := far_cf x hx
  have hC0 := coefC_nonneg x hx25
  have hL0 := fel_nonneg x hx25
  have hK0 : 0 ≤ kK (x / 49) := by
    have := log_ge_one_y (x / 49) (le_trans (by norm_num) hyY)
    unfold kK
    linarith
  have hKy0 : 0 ≤ kK (x / 49) / (x / 49) := div_nonneg hK0 hy0.le
  have hs0 : 0 < (x / 49) ^ ((2 : ℝ) / 15) := Real.rpow_pos_of_pos hy0 _
  have hf2 : f2 (x / 49) = 3.2 * (kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6) :=
    f2_eq (x / 49) (by linarith)
  set A : ℝ := (0.70711 * 0.126 / 0.61237 + 2.052 / (3 / 8 * 3981)) * (64 / 225) with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    norm_num
  have hsum : gB HW.phi (x / 49) (r1y (x / 49)) ≤
      A * kK (x / 49) ^ 2 / (x / 49) ^ ((2 : ℝ) / 15) +
        3.2 * (kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6) := by
    rw [← hf2]
    linarith
  have hsum0 : 0 ≤ A * kK (x / 49) ^ 2 / (x / 49) ^ ((2 : ℝ) / 15) +
      3.2 * (kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6) := by
    have := Real.rpow_nonneg hKy0 ((1 : ℝ) / 6)
    positivity
  have e : 7 / 15 * (1.36065 * kK (x / 49)) *
      (A * kK (x / 49) ^ 2 / (x / 49) ^ ((2 : ℝ) / 15) +
        3.2 * (kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6)) =
      7 / 15 * 1.36065 * (A * (kK (x / 49) ^ 3 / (x / 49) ^ ((2 : ℝ) / 15)) +
        3.2 * ((kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6) * kK (x / 49))) := by
    ring
  have h1 := mul_le_mul_of_nonneg_left hq1 hA0
  have h2 := mul_le_mul_of_nonneg_left hq2 (by norm_num : (0 : ℝ) ≤ 3.2)
  have hfin : 7 / 15 * 1.36065 * (A * 7.54482 + 3.2 * 0.00174305) ≤ 0.235 := by
    rw [hA]
    norm_num
  unfold t1
  calc coefC x * gB HW.phi (x / 49) (r1y (x / 49)) * fel x
      = coefC x * fel x * gB HW.phi (x / 49) (r1y (x / 49)) := by ring
    _ ≤ coefC x * fel x * (A * kK (x / 49) ^ 2 / (x / 49) ^ ((2 : ℝ) / 15) +
          3.2 * (kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hL0)
    _ ≤ 7 / 15 * (1.36065 * kK (x / 49)) *
          (A * kK (x / 49) ^ 2 / (x / 49) ^ ((2 : ℝ) / 15) +
            3.2 * (kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hC hL hL0 (by norm_num)) hsum0
    _ = 7 / 15 * 1.36065 * (A * (kK (x / 49) ^ 3 / (x / 49) ^ ((2 : ℝ) / 15)) +
          3.2 * ((kK (x / 49) / (x / 49)) ^ ((1 : ℝ) / 6) * kK (x / 49))) := e
    _ ≤ 7 / 15 * 1.36065 * (A * 7.54482 + 3.2 * 0.00174305) := by
        have hB : (0 : ℝ) ≤ 7 / 15 * 1.36065 := by norm_num
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hB
    _ ≤ 0.235 := hfin

/-- **`T1Far` from `9.8·10²⁷`**: the block `[9.8·10²⁷, 4.9·10²⁸]` (`ρ = 0.72` by `RKTail`) and the
far tail. -/
theorem t1Far_4 : T1Far (98 * 10 ^ 26) 0.235 := by
  intro x hx
  rcases le_or_gt x (49 * 10 ^ 27) with h | h
  · exact t1Reg_of_env (98 * 10 ^ 26) (49 * 10 ^ 27) (2 * 10 ^ 26) (10 ^ 27) 0.72 0.235
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun y hy _ => rkTail y (r1y y) hy (r1y_ge y (le_trans (by norm_num) hy)) le_rfl)
      t1BNum_4 x hx h
  · exact t1Far_crude x h.le

/-- `T1Reg` on `[4.9·10²⁶, 1.47·10²⁷]` (`ρ = 0.672`, `RKNum` at `4.68·10⁶`). -/
theorem t1Reg_1 : T1Reg (49 * 10 ^ 25) (147 * 10 ^ 25) 0.2955 :=
  t1Reg_of_env _ _ (10 ^ 25) (3 * 10 ^ 25) 0.672 _ (by norm_num) (by norm_num) le_rfl
    (by norm_num)
    (rk_r1 _ _ 4680000 2340000 _ le_rfl (rkMono _ _ _ le_rfl (by norm_num)
      (rkCeil_of _ _ _ le_rfl (by norm_num) rkNum_11))
      r1Le_b1 (by norm_num)) t1BNum_1

/-- `T1Reg` on `[1.47·10²⁷, 4.9·10²⁷]` (`ρ = 0.674`, `RKNum` at `6.44·10⁶`). -/
theorem t1Reg_2 : T1Reg (147 * 10 ^ 25) (49 * 10 ^ 26) 0.2665 :=
  t1Reg_of_env _ _ (3 * 10 ^ 25) (10 ^ 26) 0.674 _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (rk_r1 _ _ 6440000 3220000 _ (by norm_num) (rkMono _ _ _ (by norm_num) (by norm_num)
      (rkCeil_of _ _ _ (by norm_num) (by norm_num) rkNum_12))
      r1Le_b2 (by norm_num)) t1BNum_2

/-- `T1Reg` on `[4.9·10²⁷, 9.8·10²⁷]` (`ρ = 0.669`, `RKNum` at `7.74·10⁶`). -/
theorem t1Reg_3 : T1Reg (49 * 10 ^ 26) (98 * 10 ^ 26) 0.2325 :=
  t1Reg_of_env _ _ (10 ^ 26) (2 * 10 ^ 26) 0.669 _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (rk_r1 _ _ 7740000 3870000 _ (by norm_num) (rkMono _ _ _ (by norm_num) (by norm_num)
      (rkCeil_of _ _ _ (by norm_num) (by norm_num) rkNum_13))
      r1Le_b3 (by norm_num)) t1BNum_3

/-! ## (14) THE LINK IS PROVED: `MNumAt 8.36 0.785` and `MinW.MNumW HW.phi 0.785` -/

/-- `RKBnd` from a certified `RKNum` (`RKMono`, `pre_ok`), with `t_b` written two ways. -/
theorem rkBnd_of (ya tb tb' ρ : ℝ) (hya : 10 ^ 25 ≤ ya) (htb : 1 ≤ tb)
    (htb2 : 2.004 * tb < 18000000) (e : tb' = tb) (h : RKNum ya tb ρ) : RKBnd ya tb' ρ :=
  e ▸ rkMono ya tb ρ hya htb (rkCeil_of ya tb ρ hya htb2 h)

/-- **[G0Env] DISCHARGED** at `(10²⁵, 0.0412)`. -/
theorem g0Env_1 : G0Env (10 ^ 25) 0.0412 :=
  g0Env_of _ 0.5845 _ (by norm_num) le_rfl
    (rkBnd_of _ _ _ _ le_rfl (by norm_num) (by norm_num) rfl rkNum_01) envPt f2Anti g0Num_1

/-- **[G0Env] DISCHARGED** at `(3·10²⁵, 0.0409)`. -/
theorem g0Env_2 : G0Env (3 * 10 ^ 25) 0.0409 :=
  g0Env_of _ 0.579 _ (by norm_num) (by norm_num)
    (rkBnd_of _ _ _ _ (by norm_num) (by norm_num) (by norm_num) rfl rkNum_02) envPt f2Anti
    g0Num_2

/-- **[G0Env] DISCHARGED** at `(10²⁶, 0.0406)`. -/
theorem g0Env_3 : G0Env (10 ^ 26) 0.0406 :=
  g0Env_of _ 0.5735 _ (by norm_num) (by norm_num)
    (rkBnd_of _ _ _ _ (by norm_num) (by norm_num) (by norm_num) rfl rkNum_03) envPt f2Anti
    g0Num_3

/-- **[G0Env] DISCHARGED** at `(2·10²⁶, 0.0404)`. -/
theorem g0Env_4 : G0Env (2 * 10 ^ 26) 0.0404 :=
  g0Env_of _ 0.5705 _ (by norm_num) (by norm_num)
    (rkBnd_of _ _ _ _ (by norm_num) (by norm_num) (by norm_num) rfl rkNum_04) envPt f2Anti
    g0Num_4

/-- **[IGBlk] DISCHARGED** on `[10²⁵, 3·10²⁵]` (`≤ 0.074`). -/
theorem igBlk_1 : IGBlk (10 ^ 25) (3 * 10 ^ 25) 0.074 :=
  igBlk_of _ _ 0.672 2340000 _ (by norm_num) le_rfl
    (rkBnd_of _ 4680000 _ _ le_rfl (by norm_num) (by norm_num) (by norm_num) rkNum_11)
    r1Le_b1 envPt f2Anti iBlkNum_1

/-- **[IGBlk] DISCHARGED** on `[3·10²⁵, 10²⁶]` (`≤ 0.0785`). -/
theorem igBlk_2 : IGBlk (3 * 10 ^ 25) (10 ^ 26) 0.0785 :=
  igBlk_of _ _ 0.674 3220000 _ (by norm_num) (by norm_num)
    (rkBnd_of _ 6440000 _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) rkNum_12)
    r1Le_b2 envPt f2Anti iBlkNum_2

/-- **[IGBlk] DISCHARGED** on `[10²⁶, 2·10²⁶]` (`≤ 0.080`). -/
theorem igBlk_3 : IGBlk (10 ^ 26) (2 * 10 ^ 26) 0.08 :=
  igBlk_of _ _ 0.669 3870000 _ (by norm_num) (by norm_num)
    (rkBnd_of _ 7740000 _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) rkNum_13)
    r1Le_b3 envPt f2Anti iBlkNum_3

/-- **[IGTail] DISCHARGED** on `y ≥ 2·10²⁶` (`≤ 0.115`). -/
theorem igTail_4 : IGTail (2 * 10 ^ 26) 0.115 :=
  igTail_of _ 0.72 0.0039 _ (by norm_num) (by norm_num) rkTail envPt f2Tail iTailNum

/-- **`MNumAt 8.36 0.785`, PROVED** (`eq:bustier` on Helfgott's `φ` at the floor `p ≥ 8.36`):
`mnumAt_of_links2` with every link discharged above. No hypotheses. -/
theorem mnumAt_proved : MNumAt 8.36 0.785 :=
  mnumAt_of_links2 g0Nonneg g0Env_1 g0Env_2 g0Env_3 g0Env_4 t1Reg_1 t1Reg_2 t1Reg_3 t1Far_4
    igBlk_1 igBlk_2 igBlk_3 igTail_4

/-- **`MinW.MNumW HW.phi 0.785`, PROVED.** -/
theorem mnumW_proved : MinW.MNumW HW.phi 0.785 := mnumW_of_at mnumAt_proved

end Principia.Common.TernaryGoldbach.MN
