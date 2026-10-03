/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.GorshSpine
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

/-!
# The monotonicity links of the corrected `thm:ostop`: `GYMono`, `GTMonoL`, `HLeG` PROVED

Three of the four numeric layer-2 links named in `GorshSpine.lean` / `OstopL.lean` are
discharged here, for every scale, with no floating point in the proofs:

* **`GS.GYMono`** (`gYMono`) — `lem:vinc` at `K = 1` on the CORRECTED `L` (`OL.lLc`): `gYL(Y,·)`
  is non-increasing on `[175, Y^{1/3}/6]`. In `ℓ = log r`, `M = log(9Y^{1/3}/4.008)`,
  `x = ℓ + log 2` (`gYL_exp`):
  `gYL(Y,e^ℓ) = P(ℓ)√Q(ℓ)/√2 + 2.5/√(2e^ℓ) + L(ℓ) + 3.2Y^{−1/6}`,
  `P = (R x + 1/2)e^{−0.43ℓ}`, `Q = ϝ e^{−0.14ℓ}`, `L = L_{e^ℓ}e^{−ℓ}`. Each of `P`, `Q`, `L` has a
  nonpositive derivative on `[log 175, log(Y^{1/3}/6)]` (Mathlib's
  `antitoneOn_of_hasDerivWithinAt_nonpos`):
  - `P' ≤ 0` (`pL_anti`) from `R' = 0.27125·(A+B)/(B(2B+A)) ≤ 0.27125/2` (`B = M − ℓ ≥ 2`,
    `dD_bound`), `R ≥ 0.41415` and `x ≥ 5.69`: the bracket is `≤ −0.04246x + 0.19915 < 0`;
  - `Q' ≤ 0` (`qL_anti`) from `ϝ' ≤ e^γ/ℓ ≤ 0.14ϝ` (`1 ≤ 0.14ℓ log ℓ` at `ℓ ≥ 5`);
  - `L' ≤ 0` (`lLL_anti`) from `ϝ' ≤ 0.14ϝ` again.
  The float scoping (`scratchpad/mono/mono_price.py`): `max d log P/dℓ = −0.264`,
  `max d log Q/dℓ = −0.103`, `max d log L/dℓ = −0.848` over 8 scales `Y ∈ [3.4·10²³, 10^{10000}]`.
  The decomposition itself agrees with `gYL` to 20 digits at three points.
* **`OL.GTMonoL`** (`gtMonoL_of`, `gtMonoL_helf`) — derived from `GYMono` for every `φ ≥ 0` in
  `L¹(0,∞)`: for `r ≤ r'` the cutoff `w₁ = max(1/K, 1000/r)` moves down to `w₁'`, and the piece
  `∫_{w₁'}^{w₁} gYL(wy,wr')φ` that leaves the sliver is at most `1.04488∫_{w₁'}^{w₁}|φ|` because
  `gYL(wy, wr') ≤ gYL(wy, 1000) ≤ 0.6` (`gYL_1000_le`; float `0.538`); on `[w₁, 1]` and `(1,∞)`
  the integrands decrease by `GYMono` at scale `wy`.
* **`GS.HLeG`** (`hLeG`) — `h′(Y) ≤ gYL(Y, r₁(Y))·Y` for every `Y ≥ 3.4·10²³`. With
  `v = Y^{1/30} ≥ 6.08` and `λ = log v ∈ [1.78, 0.79263 + v/6]`:
  `h′/v²⁵ ≤ 20.8715λ² + 43.1λ` (`hL_pow30_le`) and `gYL·Y/v²⁵ ≥ (11.5723λ + 3.5222)v + 3.2`
  (`gYL_pow30_ge`, from `R_{Y,2r₁} ≥ 0.647` (`rR_pow30_ge`), `log 2r₁ ≥ 8λ − 1/3`, `ϝ ≥ 3.75`,
  `√(3/4) ≤ 0.8661`); the closing quadratic (`hLeG_key`) has root `1.745 < 1.78`. Float
  (`scratchpad/mono/hleg_price.py`): the certified gap is `≥ 5.8` (about `4%`) at the worst
  corner `v = 6.08`; the true ratio is `1.2997` at `Y = 3.4·10²³`.

`OS.TopStepL` (the fourth numeric link, `√⌊r₁⌋·g̃(⌊r₁⌋) ≤ √r₁·g̃(r₁)`) is NOT discharged here.

Every log of a numeral is `generalize`d before `linarith` (linarith does not see through
`Real.log` of a numeral); every constant rounding is in the direction that weakens the claim
being proved.
-/

namespace Principia.Common.TernaryGoldbach.MO

open Set MeasureTheory

/-- `u(ℓ) = (log 8 + ℓ)/(2(M − ℓ))`. -/
noncomputable def uL (M l : ℝ) : ℝ := (Real.log 8 + l) / (2 * (M - l))

/-- `R` in the variable `ℓ = log r`. -/
noncomputable def rL (M l : ℝ) : ℝ := 0.27125 * Real.log (1 + uL M l) + 0.41415

/-- `(R x + 1/2) e^{−0.43ℓ}`, `x = ℓ + log 2`. -/
noncomputable def pL (M l : ℝ) : ℝ := (rL M l * (l + Real.log 2) + 0.5) * Real.exp (-0.43 * l)

/-- `ϝ` in the variable `ℓ = log r`. -/
noncomputable def fL (l : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log l + 2.50637 / Real.log l

/-- `ϝ e^{−0.14ℓ}`. -/
noncomputable def qL (l : ℝ) : ℝ := fL l * Real.exp (-0.14 * l)

/-- `L_r/r` in the variable `ℓ = log r`. -/
noncomputable def lLL (l : ℝ) : ℝ :=
  (fL l * (7 / 4 * Real.log 2 + 13 / 4 * l + 80 / 9) + 1.7984 * Real.log 2 + 13.6516 * l +
    22.7538) * Real.exp (-l)

/-- A function with a nonpositive derivative on `[a, b]` is antitone there. -/
theorem anti_of_deriv (f f' : ℝ → ℝ) (a b : ℝ) (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc a b, f' x ≤ 0) : AntitoneOn f (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hd x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact hn x (Ioo_subset_Icc_self hx)

theorem hasDerivAt_uL (M l : ℝ) (h : l < M) :
    HasDerivAt (uL M) ((Real.log 8 + l + (M - l)) / (2 * (M - l) ^ 2)) l := by
  have h1 : HasDerivAt (fun l : ℝ => Real.log 8 + l) 1 l := (hasDerivAt_id' l).const_add _
  have h2 : HasDerivAt (fun l : ℝ => 2 * (M - l)) (2 * -1) l :=
    ((hasDerivAt_id' l).const_sub M).const_mul 2
  have hne : 2 * (M - l) ≠ 0 := by
    have : 0 < 2 * (M - l) := by linarith
    exact this.ne'
  have h3 : HasDerivAt (fun l : ℝ => (Real.log 8 + l) / (2 * (M - l)))
      ((1 * (2 * (M - l)) - (Real.log 8 + l) * (2 * -1)) / (2 * (M - l)) ^ 2) l :=
    h1.div h2 hne
  have hB : M - l ≠ 0 := by
    have : 0 < M - l := by linarith
    exact this.ne'
  refine h3.congr_deriv ?_
  field_simp
  ring

/-- `0 ≤ D ≤ 1/2` for `D = ((A + B)/(2B²))/(1 + A/(2B))`, `A ≥ 0`, `B ≥ 2`: the log-derivative of
`1 + u` is at most `1/(M − ℓ)`. -/
theorem dD_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 2 ≤ B) :
    0 ≤ (A + B) / (2 * B ^ 2) / (1 + A / (2 * B)) ∧
      (A + B) / (2 * B ^ 2) / (1 + A / (2 * B)) ≤ 1 / 2 := by
  have hB0 : 0 < B := by linarith
  have e : (A + B) / (2 * B ^ 2) / (1 + A / (2 * B)) = (A + B) / (B * (2 * B + A)) := by
    field_simp
  rw [e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem hasDerivAt_rL (M l : ℝ) (h : l + 2 ≤ M) (hl : 0 ≤ Real.log 8 + l) :
    HasDerivAt (rL M)
      (0.27125 * ((Real.log 8 + l + (M - l)) / (2 * (M - l) ^ 2) / (1 + uL M l))) l := by
  have hu := hasDerivAt_uL M l (by linarith)
  have h1 : HasDerivAt (fun l : ℝ => 1 + uL M l)
      ((Real.log 8 + l + (M - l)) / (2 * (M - l) ^ 2)) l := hu.const_add 1
  have hpos : 0 < 1 + uL M l := by
    unfold uL
    have := div_nonneg hl (by linarith : (0 : ℝ) ≤ 2 * (M - l))
    linarith
  have h2 := h1.log hpos.ne'
  exact (h2.const_mul 0.27125).add_const 0.41415

theorem hasDerivAt_pL (M l : ℝ) (h : l + 2 ≤ M) (hl : 0 ≤ Real.log 8 + l) :
    HasDerivAt (pL M)
      ((0.27125 * ((Real.log 8 + l + (M - l)) / (2 * (M - l) ^ 2) / (1 + uL M l)) *
          (l + Real.log 2) + rL M l - 0.43 * (rL M l * (l + Real.log 2) + 0.5)) *
        Real.exp (-0.43 * l)) l := by
  have hR := hasDerivAt_rL M l h hl
  have hx : HasDerivAt (fun l : ℝ => l + Real.log 2) 1 l := (hasDerivAt_id' l).add_const _
  have hA := (hR.mul hx).add_const 0.5
  have hE : HasDerivAt (fun l : ℝ => Real.exp (-0.43 * l)) (Real.exp (-0.43 * l) * (-0.43 * 1))
      l := ((hasDerivAt_id' l).const_mul (-0.43)).exp
  have := hA.mul hE
  exact this.congr_deriv (by simp only [Pi.mul_apply]; ring)

/-- `R ≥ 0.41415` wherever `u ≥ 0`. -/
theorem rL_ge (M l : ℝ) (h : l + 2 ≤ M) (hl : 0 ≤ Real.log 8 + l) : 0.41415 ≤ rL M l := by
  unfold rL
  have hu : 0 ≤ uL M l := by
    unfold uL
    exact div_nonneg hl (by linarith)
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + uL M l)
  linarith

/-- **`(R x + 1/2)e^{−0.43ℓ}` is antitone** on `[a, b]` for `a ≥ 5`, `b ≤ M − 2`. -/
theorem pL_anti (M a b : ℝ) (ha : 5 ≤ a) (hb : b + 2 ≤ M) : AntitoneOn (pL M) (Icc a b) := by
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hl2 := Real.log_two_gt_d9
  refine anti_of_deriv _ _ a b (fun l hl => hasDerivAt_pL M l (by linarith [hl.2])
    (by linarith [hl.1])) fun l hl => ?_
  have hlM : l + 2 ≤ M := by linarith [hl.2]
  have hl0 : 0 ≤ Real.log 8 + l := by linarith [hl.1]
  obtain ⟨hD0, hD1⟩ := dD_bound (Real.log 8 + l) (M - l) hl0 (by linarith)
  have hR := rL_ge M l hlM hl0
  have hx : 5.69 ≤ l + Real.log 2 := by linarith [hl.1]
  refine mul_nonpos_of_nonpos_of_nonneg ?_ (Real.exp_pos _).le
  have hD : (Real.log 8 + l + (M - l)) / (2 * (M - l) ^ 2) / (1 + uL M l) ≤ 1 / 2 := hD1
  have h1 := mul_le_mul_of_nonneg_right hD (by linarith : (0 : ℝ) ≤ l + Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right hR (by linarith : (0 : ℝ) ≤ 0.43 * (l + Real.log 2) - 1)
  nlinarith

theorem hasDerivAt_fL (l : ℝ) (hl : 1 < l) :
    HasDerivAt fL (Real.exp Real.eulerMascheroniConstant / l - 2.50637 / (l * Real.log l ^ 2))
      l := by
  have hl0 : l ≠ 0 := by positivity
  have hlog : Real.log l ≠ 0 := (Real.log_pos hl).ne'
  have h1 := (Real.hasDerivAt_log hl0).const_mul (Real.exp Real.eulerMascheroniConstant)
  have h2 : HasDerivAt (fun l : ℝ => (2.50637 : ℝ) / Real.log l)
      ((0 * Real.log l - 2.50637 * l⁻¹) / Real.log l ^ 2) l :=
    (hasDerivAt_const l (2.50637 : ℝ)).div (Real.hasDerivAt_log hl0) hlog
  exact (h1.add h2).congr_deriv (by field_simp; ring)

/-- `ϝ' ≤ 0.14ϝ` for `ℓ ≥ 5` (`1 ≤ 0.14ℓ log ℓ`), with `log ℓ ≥ 1.5`. -/
theorem fL_deriv_le (l : ℝ) (hl : 5 ≤ l) (hlog : 1.5 ≤ Real.log l) :
    Real.exp Real.eulerMascheroniConstant / l - 2.50637 / (l * Real.log l ^ 2) ≤ 0.14 * fL l := by
  have hl0 : 0 < l := by linarith
  have hE := Real.exp_pos Real.eulerMascheroniConstant
  have h1 : Real.exp Real.eulerMascheroniConstant / l ≤
      0.14 * (Real.exp Real.eulerMascheroniConstant * Real.log l) := by
    rw [div_le_iff₀ hl0]
    have hm : 7.5 ≤ l * Real.log l := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hm hE.le]
  have h2 : 0 ≤ 2.50637 / (l * Real.log l ^ 2) := by positivity
  have h3 : 0 ≤ 2.50637 / Real.log l := by positivity
  unfold fL
  linarith

/-- `log ℓ ≥ 1.5` for `ℓ ≥ 5` (`e³ < 25`). -/
theorem log_ge_15 (l : ℝ) (hl : 5 ≤ l) : 1.5 ≤ Real.log l := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h3 : Real.exp 1.5 * Real.exp 1.5 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have h27 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := pow_lt_pow_left₀ he he0.le (by norm_num)
  nlinarith [Real.exp_pos 1.5]

/-- `fL ≥ 0` for `ℓ > 1`. -/
theorem fL_nonneg (l : ℝ) (hl : 1 < l) : 0 ≤ fL l := by
  have h := (Real.log_pos hl).le
  unfold fL
  positivity

/-- **`ϝ e^{−0.14ℓ}` is antitone** on `[a, b]`, `a ≥ 5`. -/
theorem qL_anti (a b : ℝ) (ha : 5 ≤ a) : AntitoneOn qL (Icc a b) := by
  refine anti_of_deriv _
    (fun l => (Real.exp Real.eulerMascheroniConstant / l - 2.50637 / (l * Real.log l ^ 2) -
      0.14 * fL l) * Real.exp (-0.14 * l)) a b (fun l hl => ?_) fun l hl => ?_
  · have hF := hasDerivAt_fL l (by linarith [hl.1])
    have hE : HasDerivAt (fun l : ℝ => Real.exp (-0.14 * l)) (Real.exp (-0.14 * l) * (-0.14 * 1))
        l := ((hasDerivAt_id' l).const_mul (-0.14)).exp
    exact (hF.mul hE).congr_deriv (by ring)
  · refine mul_nonpos_of_nonpos_of_nonneg ?_ (Real.exp_pos _).le
    have := fL_deriv_le l (by linarith [hl.1]) (log_ge_15 l (by linarith [hl.1]))
    linarith

/-- **`L_r/r` in `ℓ` is antitone** on `[a, b]`, `a ≥ 5`. -/
theorem lLL_anti (a b : ℝ) (ha : 5 ≤ a) : AntitoneOn lLL (Icc a b) := by
  have hl2 := Real.log_two_gt_d9
  refine anti_of_deriv _
    (fun l => ((Real.exp Real.eulerMascheroniConstant / l - 2.50637 / (l * Real.log l ^ 2)) *
        (7 / 4 * Real.log 2 + 13 / 4 * l + 80 / 9) + fL l * (13 / 4) + 13.6516 -
      (fL l * (7 / 4 * Real.log 2 + 13 / 4 * l + 80 / 9) + 1.7984 * Real.log 2 + 13.6516 * l +
        22.7538)) * Real.exp (-l)) a b (fun l hl => ?_) fun l hl => ?_
  · have hF := hasDerivAt_fL l (by linarith [hl.1])
    have hK : HasDerivAt (fun l : ℝ => 7 / 4 * Real.log 2 + 13 / 4 * l + 80 / 9) (13 / 4 * 1) l :=
      (((hasDerivAt_id' l).const_mul (13 / 4)).const_add _).add_const _
    have hN : HasDerivAt (fun l : ℝ => 13.6516 * l) (13.6516 * 1) l :=
      (hasDerivAt_id' l).const_mul _
    have hS := (((hF.mul hK).add_const (1.7984 * Real.log 2)).add hN).add_const 22.7538
    have hE : HasDerivAt (fun l : ℝ => Real.exp (-l)) (Real.exp (-l) * (-1)) l :=
      (hasDerivAt_id' l).neg.exp
    exact (hS.mul hE).congr_deriv (by simp only [Pi.mul_apply, Pi.add_apply]; ring)
  · refine mul_nonpos_of_nonpos_of_nonneg ?_ (Real.exp_pos _).le
    have hl5 : 5 ≤ l := by linarith [hl.1]
    have hq := fL_deriv_le l hl5 (log_ge_15 l hl5)
    have hf0 := fL_nonneg l (by linarith)
    have hK0 : 0 ≤ 7 / 4 * Real.log 2 + 13 / 4 * l + 80 / 9 := by linarith
    have h1 := mul_le_mul_of_nonneg_right hq hK0
    have h2 := mul_nonneg hf0 (by linarith :
      (0 : ℝ) ≤ 0.86 * (7 / 4 * Real.log 2 + 13 / 4 * l + 80 / 9) - 13 / 4)
    nlinarith

/-- `√(e^a) = e^{a/2}`. -/
theorem sqrt_exp (a : ℝ) : Real.sqrt (Real.exp a) = Real.exp (a / 2) := by
  have e : Real.exp a = Real.exp (a / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [e]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- **`gYL` in the variable `ℓ = log r`**: for `Y > 0`, with `M = log(9Y^{1/3}/4.008)`,
`gYL(Y, e^ℓ) = P(ℓ)√Q(ℓ)/√2 + 2.5/√(2e^ℓ) + L(ℓ) + 3.2Y^{−1/6}`. -/
theorem gYL_exp (Y l : ℝ) (hY : 0 < Y) :
    OL.gYL Y (Real.exp l) =
      pL (Real.log (9 * Y ^ ((1 : ℝ) / 3) / 4.008)) l * Real.sqrt (qL l) / Real.sqrt 2 +
        2.5 / Real.sqrt (2 * Real.exp l) + lLL l + 3.2 * Y ^ (-(1 : ℝ) / 6) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Real.rpow_pos_of_pos hY _
  have hE := Real.exp_pos l
  have e1 : Real.log (2 * Real.exp l) = l + Real.log 2 := by
    rw [Real.log_mul two_ne_zero hE.ne', Real.log_exp]
    ring
  have e2 : MinSp.rR Y (2 * Real.exp l) = rL (Real.log (9 * c / 4.008)) l := by
    unfold MinSp.rR rL uL
    rw [← hc]
    have ea : Real.log (4 * (2 * Real.exp l)) = Real.log 8 + l := by
      rw [show 4 * (2 * Real.exp l) = 8 * Real.exp l by ring,
        Real.log_mul (by norm_num) hE.ne', Real.log_exp]
    have eb : Real.log (9 * c / (2.004 * (2 * Real.exp l))) = Real.log (9 * c / 4.008) - l := by
      rw [show 9 * c / (2.004 * (2 * Real.exp l)) = 9 * c / 4.008 / Real.exp l by
          field_simp
          ring,
        Real.log_div (by positivity) hE.ne', Real.log_exp]
    rw [ea, eb]
  have e3 : MinSp.bigF (Real.exp l) = fL l := by
    unfold MinSp.bigF fL
    rw [Real.log_exp]
  have e4 : OL.lLc (Real.exp l) / Real.exp l = lLL l := by
    unfold OL.lLc lLL
    rw [OL.log_two_rpow_mul _ _ _ hE, OL.log_two_rpow_mul _ _ _ hE, Real.log_exp, e3,
      Real.exp_neg, div_eq_mul_inv]
    ring
  have e5 : Real.sqrt (2 * Real.exp l) = Real.sqrt 2 * Real.exp (l / 2) := by
    rw [Real.sqrt_mul' 2 hE.le, sqrt_exp]
  have e6 : Real.sqrt (qL l) = Real.sqrt (fL l) * Real.exp (-0.07 * l) := by
    unfold qL
    rw [Real.sqrt_mul' _ (Real.exp_pos _).le, sqrt_exp]
    ring_nf
  have hk : Real.exp (-0.43 * l) * Real.exp (-0.07 * l) = (Real.exp (l / 2))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    ring_nf
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hE2 := Real.exp_pos (l / 2)
  unfold OL.gYL
  rw [e2, e1, e3, e4, e5, ← hc]
  unfold pL
  rw [e6]
  generalize Real.exp (-0.43 * l) = a at hk ⊢
  generalize Real.exp (-0.07 * l) = b at hk ⊢
  have key : (rL (Real.log (9 * c / 4.008)) l * (l + Real.log 2) + 0.5) * a *
      (Real.sqrt (fL l) * b) / Real.sqrt 2 =
      (rL (Real.log (9 * c / 4.008)) l * (l + Real.log 2) + 0.5) * Real.sqrt (fL l) *
        (a * b) / Real.sqrt 2 := by ring
  rw [key, hk, add_div]
  field_simp

/-- `e⁵ < 175`. -/
theorem log175_ge : 5 ≤ Real.log 175 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have h27 : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h5]
  have : (2.7182818286 : ℝ) ^ 5 ≤ 175 := by norm_num
  linarith

/-- `log(54/4.008) ≥ 2` (`e² < 13.47`). -/
theorem log_top_ge : 2 ≤ Real.log (54 / 4.008) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have h27 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h2]
  have : (2.7182818286 : ℝ) ^ 2 ≤ 54 / 4.008 := by norm_num
  linarith

/-- **[GYMono] PROVED — `lem:vinc` at `K = 1` on the corrected `L`**: `gYL(Y,·)` is
non-increasing on `[175, Y^{1/3}/6]` for every `Y ≥ 3.4·10²³` (only `Y > 0` is used). In
`ℓ = log r` the four summands are `P√Q/√2`, `2.5/√(2e^ℓ)`, `L(ℓ)` and a constant, with
`P = (Rx + 1/2)e^{−0.43ℓ}` (`pL_anti`: `R' ≤ 0.27125/2`, `R ≥ 0.41415`, `x ≥ 5.69`),
`Q = ϝe^{−0.14ℓ}` (`qL_anti`: `1 ≤ 0.14ℓ log ℓ`) and `L` (`lLL_anti`) each antitone. -/
theorem gYMono : GS.GYMono := by
  intro Y hY r hr r' hr' hrr'
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Real.rpow_pos_of_pos hY0 _
  rw [← hc] at hr hr'
  have hr0 : 0 < r := by linarith [hr.1]
  have hr'0 : 0 < r' := by linarith [hr'.1]
  rw [← Real.exp_log hr0, ← Real.exp_log hr'0, gYL_exp Y _ hY0, gYL_exp Y _ hY0, ← hc]
  have hll : Real.log r ≤ Real.log r' := Real.log_le_log hr0 hrr'
  have hl5 : 5 ≤ Real.log r := le_trans log175_ge (Real.log_le_log (by norm_num) hr.1)
  have hlM : Real.log r' + 2 ≤ Real.log (9 * c / 4.008) := by
    have h1 : Real.log r' ≤ Real.log (c / 6) := Real.log_le_log hr'0 hr'.2
    have h2 : Real.log (9 * c / 4.008) = Real.log (54 / 4.008) + Real.log (c / 6) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
      ring
    linarith [log_top_ge]
  have hmem : Real.log r ∈ Icc (Real.log r) (Real.log r') := ⟨le_rfl, hll⟩
  have hmem' : Real.log r' ∈ Icc (Real.log r) (Real.log r') := ⟨hll, le_rfl⟩
  have hP := pL_anti (Real.log (9 * c / 4.008)) _ _ hl5 hlM hmem hmem' hll
  have hQ := qL_anti _ _ hl5 hmem hmem' hll
  have hL := lLL_anti _ _ hl5 hmem hmem' hll
  have hP0 : 0 ≤ pL (Real.log (9 * c / 4.008)) (Real.log r) := by
    have hl2 := Real.log_two_gt_d9
    have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
    have hR := rL_ge (Real.log (9 * c / 4.008)) (Real.log r) (by linarith) (by linarith)
    unfold pL
    refine mul_nonneg ?_ (Real.exp_pos _).le
    nlinarith
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hT1 : pL (Real.log (9 * c / 4.008)) (Real.log r') * Real.sqrt (qL (Real.log r')) /
      Real.sqrt 2 ≤
      pL (Real.log (9 * c / 4.008)) (Real.log r) * Real.sqrt (qL (Real.log r)) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul hP (Real.sqrt_le_sqrt hQ) (Real.sqrt_nonneg _) hP0) hs2.le
  have hT2 : 2.5 / Real.sqrt (2 * Real.exp (Real.log r')) ≤
      2.5 / Real.sqrt (2 * Real.exp (Real.log r)) := by
    rw [Real.exp_log hr0, Real.exp_log hr'0]
    exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by linarith))
      (Real.sqrt_le_sqrt (by linarith))
  linarith

/-- `e^γ ≤ 1.95` (`γ < 2/3`, `e² < 1.95³`). -/
theorem exp_gamma_le : Real.exp Real.eulerMascheroniConstant ≤ 1.95 := by
  have h1 : Real.exp Real.eulerMascheroniConstant ≤ Real.exp (2 / 3) :=
    Real.exp_le_exp.2 Real.eulerMascheroniConstant_lt_two_thirds.le
  have h2 : Real.exp (2 / 3) ^ 3 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have he : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h3 : Real.exp (2 / 3) ≤ 1.95 := by
    by_contra h
    have h4 : (1.95 : ℝ) ^ 3 < Real.exp (2 / 3) ^ 3 :=
      pow_lt_pow_left₀ (lt_of_not_ge h) (by norm_num) (by norm_num)
    have : (2.7182818286 : ℝ) ^ 2 ≤ 1.95 ^ 3 := by norm_num
    linarith
  linarith

/-- `(a^n)^{1/n}`-type lower bound: `b ≤ Y^{1/n}` from `b^n ≤ Y`, `b ≥ 0`. -/
theorem le_rpow_inv (b Y : ℝ) (n : ℕ) (hn : 0 < n) (hb : 0 ≤ b) (h : b ^ n ≤ Y) :
    b ≤ Y ^ ((1 : ℝ) / n) := by
  have h2 := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ 1 / n)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb] at h2
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (n : ℝ) * (1 / n) = 1 by field_simp, Real.rpow_one] at h2
  exact h2

/-- **The sliver swap is favourable**: `gYL(Y, 1000) ≤ 0.6 < 1.04488` for `Y ≥ 3.4·10²³`
(`R_{Y,2000} ≤ 0.52512`, `ϝ(1000) ≤ 5.571`, `L_{1000} ≤ 300.5`, `3.2Y^{−1/6} ≤ 0.0032`; the float
value is `0.5384`). -/
theorem gYL_1000_le (Y : ℝ) (hY : 3.4e23 ≤ Y) : OL.gYL Y 1000 ≤ 0.6 := by
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have he1 := Real.exp_one_gt_d9
  have he1' := Real.exp_one_lt_d9
  have hc : 6.9e7 ≤ Y ^ ((1 : ℝ) / 3) := by
    have := le_rpow_inv 6.9e7 Y 3 (by norm_num) (by norm_num) (le_trans (by norm_num) hY)
    exact_mod_cast this
  have h6 : 1000 ≤ Y ^ ((1 : ℝ) / 6) := by
    have := le_rpow_inv 1000 Y 6 (by norm_num) (by norm_num) (le_trans (by norm_num) hY)
    exact_mod_cast this
  have hT3 : 3.2 * Y ^ (-(1 : ℝ) / 6) ≤ 0.0032 := by
    rw [neg_div, Real.rpow_neg hY0.le]
    have : (Y ^ ((1 : ℝ) / 6))⁻¹ ≤ 1 / 1000 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h6
    linarith
  have e8 : (4 : ℝ) * (2 * 1000) = 8000 := by norm_num
  have hl8000 : Real.log 8000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h9]
    have : (2.7182818283 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he1.le 9
    have : (8000 : ℝ) ≤ 2.7182818283 ^ 9 := by norm_num
    linarith
  have hl8000' : 0 ≤ Real.log 8000 := Real.log_nonneg (by norm_num)
  have hq : 11 ≤ Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000))) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h11 : Real.exp 11 = Real.exp 1 ^ 11 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h1 : Real.exp 1 ^ 11 < 2.7182818286 ^ 11 :=
      pow_lt_pow_left₀ he1' (Real.exp_pos 1).le (by norm_num)
    have h2 : (2.7182818286 : ℝ) ^ 11 ≤ 9 * 6.9e7 / (2.004 * (2 * 1000)) := by norm_num
    have h3 : 9 * 6.9e7 / (2.004 * (2 * 1000)) ≤ 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000)) := by
      gcongr
    rw [h11]
    linarith
  have hR : MinSp.rR Y (2 * 1000) ≤ 0.52512 := by
    unfold MinSp.rR
    rw [e8]
    have hu0 : 0 ≤ Real.log 8000 / (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000)))) :=
      div_nonneg hl8000' (by linarith)
    have hu : Real.log 8000 / (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000)))) ≤
        9 / 22 := by
      rw [div_le_iff₀ (by linarith)]
      generalize Real.log 8000 = a at hl8000 hl8000' ⊢
      generalize Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000))) = q at hq ⊢
      nlinarith
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 +
      Real.log 8000 / (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000)))) by linarith)
    generalize Real.log 8000 / (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * 1000)))) = u
      at hu0 hu hlog ⊢
    linarith
  have hR0 : 0.41415 ≤ MinSp.rR Y (2 * 1000) :=
    GS.rR_ge Y (2 * 1000) hY0 (by norm_num) (by linarith)
  have hlog2000 : Real.log (2 * 1000) ≤ 7.6247 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 * 1000)
      (by norm_num : (2 : ℝ) * 1000 ≤ 2 ^ 11)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log (2 * 1000) = x at h ⊢
    linarith
  have hlog2000' : 0 ≤ Real.log (2 * 1000) := Real.log_nonneg (by norm_num)
  have hl1000 : Real.log 1000 ≤ 6.9315 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1000) (by norm_num : (1000 : ℝ) ≤ 2 ^ 10)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 1000 = x at h ⊢
    linarith
  have hl1000' : 6.238 ≤ Real.log 1000 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 9) (by norm_num : (2 : ℝ) ^ 9 ≤ 1000)
    rw [Real.log_pow] at h
    push_cast at h
    generalize Real.log 1000 = x at h ⊢
    linarith
  have hll : Real.log (Real.log 1000) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he1.le 2
    rw [h2]
    generalize Real.log 1000 = x at hl1000 ⊢
    nlinarith
  have hll' : 1.5 ≤ Real.log (Real.log 1000) := log_ge_15 _ (by linarith)
  have hEg := exp_gamma_le
  have hF : MinSp.bigF 1000 ≤ 5.571 := by
    unfold MinSp.bigF
    have h1 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 1000) ≤ 1.95 * 2 :=
      mul_le_mul hEg hll (by linarith) (by norm_num)
    have h2 : 2.50637 / Real.log (Real.log 1000) ≤ 2.50637 / 1.5 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hll'
    linarith
  have hF0 : 0 ≤ MinSp.bigF 1000 := le_trans (by norm_num) (GS.bigF_gt 1000 (by norm_num)).le
  have hsF : Real.sqrt (MinSp.bigF 1000) ≤ 2.3603 := by
    rw [show (2.3603 : ℝ) = Real.sqrt (2.3603 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs2000 : 44.72 ≤ Real.sqrt (2 * 1000) := by
    rw [show (44.72 : ℝ) = Real.sqrt (44.72 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hA : MinSp.rR Y (2 * 1000) * Real.log (2 * 1000) + 0.5 ≤ 0.52512 * 7.6247 + 0.5 := by
    have := mul_le_mul hR hlog2000 hlog2000' (by norm_num)
    generalize MinSp.rR Y (2 * 1000) * Real.log (2 * 1000) = x at this ⊢
    linarith
  have hN : (MinSp.rR Y (2 * 1000) * Real.log (2 * 1000) + 0.5) * Real.sqrt (MinSp.bigF 1000) +
      2.5 ≤ (0.52512 * 7.6247 + 0.5) * 2.3603 + 2.5 := by
    have := mul_le_mul hA hsF (Real.sqrt_nonneg _) (by norm_num)
    generalize (MinSp.rR Y (2 * 1000) * Real.log (2 * 1000) + 0.5) *
      Real.sqrt (MinSp.bigF 1000) = x at this ⊢
    linarith
  have hT1 : ((MinSp.rR Y (2 * 1000) * Real.log (2 * 1000) + 0.5) *
      Real.sqrt (MinSp.bigF 1000) + 2.5) / Real.sqrt (2 * 1000) ≤
      ((0.52512 * 7.6247 + 0.5) * 2.3603 + 2.5) / 44.72 :=
    calc _ ≤ ((0.52512 * 7.6247 + 0.5) * 2.3603 + 2.5) / Real.sqrt (2 * 1000) :=
          div_le_div_of_nonneg_right hN (Real.sqrt_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2000
  have hL : OL.lLc 1000 ≤ 300.5 := by
    unfold OL.lLc
    rw [OL.log_two_rpow_mul _ _ _ (by norm_num), OL.log_two_rpow_mul _ _ _ (by norm_num)]
    generalize Real.log 1000 = x at hl1000 hl1000' ⊢
    have := mul_le_mul hF
      (show 7 / 4 * Real.log 2 + 13 / 4 * x + 80 / 9 ≤
        7 / 4 * 0.6931471808 + 13 / 4 * 6.9315 + 80 / 9 by linarith)
      (by linarith) (by norm_num)
    linarith
  have hT2 : OL.lLc 1000 / 1000 ≤ 0.3005 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  unfold OL.gYL
  generalize ((MinSp.rR Y (2 * 1000) * Real.log (2 * 1000) + 0.5) *
      Real.sqrt (MinSp.bigF 1000) + 2.5) / Real.sqrt (2 * 1000) = A at hT1 ⊢
  generalize OL.lLc 1000 / 1000 = B at hT2 ⊢
  generalize Y ^ (-(1 : ℝ) / 6) = C at hT3 ⊢
  norm_num at hT1 ⊢
  linarith

/-- **[GTMonoL] from [GYMono]**, for every `φ ≥ 0` in `L¹(0,∞)`: for `r ≤ r'` in
`[150000, r₁(y)]`, with `w₁' = w₁(r') ≤ w₁(r)`, the piece `∫_{w₁'}^{w₁}gYL(wy,wr')φ` moved from the
sliver is at most `1.04488∫_{w₁'}^{w₁}|φ|` (`gYL(wy,wr') ≤ gYL(wy,1000) ≤ 0.6`), and on `[w₁,1]`
and `(1,∞)` the integrands decrease (`GYMono` at scale `wy`: the arguments stay in
`[1000, r₁(wy)] ⊆ [175, (wy)^{1/3}/6]`). -/
theorem gtMonoL_of (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Ioi 0)) (hmo : GS.GYMono) : OL.GTMonoL φ := by
  intro y hy r hr r' hr' hrr'
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hr'0, hr'1⟩ := hr'
  have hrp : 0 < r := by linarith
  have hr'p : 0 < r' := by linarith
  have hl17 := GS.log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  have hint := GS.gtlInt φ hφi y hy r hr0 hr1
  have hint' := GS.gtlInt φ hφi y hy r' hr'0 hr'1
  have hφa : IntegrableOn (fun w => |φ w|) (Ioi 0) := hφi.abs
  unfold OL.gTL
  refine div_le_div_of_nonneg_right ?_ (MajSp.l1_nonneg φ)
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 1 / MinSp.kK y := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = max k (1000 / r) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = max k (1000 / r') := ⟨_, rfl⟩
  rw [← hk, ← ha, ← ha']
  rw [← hk] at hK0 hK1 hint hint'
  rw [← ha] at hint
  rw [← ha'] at hint'
  have haa : a' ≤ a := by
    rw [ha, ha']
    exact max_le_max le_rfl (div_le_div_of_nonneg_left (by norm_num) hrp hrr')
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact max_le hK1 (by rw [div_le_one hrp]; linarith)
  have hka : k ≤ a := by rw [ha]; exact le_max_left _ _
  have hka' : k ≤ a' := by rw [ha']; exact le_max_left _ _
  have hra : 1000 / r ≤ a := by rw [ha]; exact le_max_right _ _
  have hra' : 1000 / r' ≤ a' := by rw [ha']; exact le_max_right _ _
  have hscale : ∀ w : ℝ, k ≤ w → 3.4e23 ≤ w * y := fun w hw =>
    GS.scale_ge y w hy (by rw [← hk]; exact hw)
  -- integrability
  have hI1'a : IntervalIntegrable (fun w => OL.gYL (w * y) (w * r') * φ w) volume a' a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haa).mpr
      (hint'.1.mono_set (Ioc_subset_Ioc_right ha1))
  have hI1'b : IntervalIntegrable (fun w => OL.gYL (w * y) (w * r') * φ w) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).mpr
      (hint'.1.mono_set (Ioc_subset_Ioc_left haa))
  have hI1 : IntervalIntegrable (fun w => OL.gYL (w * y) (w * r) * φ w) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).mpr hint.1
  have hS1 : IntervalIntegrable (fun w => |φ w|) volume k a' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hka').mpr
      (hφa.mono_set fun w hw => lt_of_lt_of_le hK0 hw.1.le)
  have hS2 : IntervalIntegrable (fun w => |φ w|) volume a' a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haa).mpr
      (hφa.mono_set fun w hw => lt_of_lt_of_le hK0 (le_trans hka' hw.1.le))
  have split1 := intervalIntegral.integral_add_adjacent_intervals hI1'a hI1'b
  have split2 := intervalIntegral.integral_add_adjacent_intervals hS1 hS2
  -- the moved piece
  have b1 : (∫ w in a'..a, OL.gYL (w * y) (w * r') * φ w) ≤ ∫ w in a'..a, 1.04488 * |φ w| := by
    refine intervalIntegral.integral_mono_on haa hI1'a (hS2.const_mul 1.04488) fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hK0 (le_trans hka' hw.1)
    have hw1 : w ≤ 1 := le_trans hw.2 ha1
    have hY := hscale w (le_trans hka' hw.1)
    have h1000 : 1000 ≤ w * r' := by
      have := le_trans hra' hw.1
      rwa [div_le_iff₀ hr'p] at this
    have harg := GS.arg_le_r1y y w r' hy0 hw0 hr'1
    rw [min_eq_left hw1] at harg
    have hth := GS.r1y_le_third (w * y) hY
    have hg : OL.gYL (w * y) (w * r') ≤ OL.gYL (w * y) 1000 :=
      hmo (w * y) hY ⟨by norm_num, by linarith⟩ ⟨by linarith, le_trans harg hth⟩ h1000
    have hg6 := gYL_1000_le (w * y) hY
    have hφw := hφ0 w hw0.le
    rw [abs_of_nonneg hφw]
    exact mul_le_mul_of_nonneg_right (by linarith) hφw
  have b1c : (∫ w in a'..a, 1.04488 * |φ w|) = 1.04488 * ∫ w in a'..a, |φ w| :=
    intervalIntegral.integral_const_mul _ _
  -- the integrand decreases on `[a, 1]`
  have b2 : (∫ w in a..1, OL.gYL (w * y) (w * r') * φ w) ≤
      ∫ w in a..1, OL.gYL (w * y) (w * r) * φ w := by
    refine intervalIntegral.integral_mono_on ha1 hI1'b hI1 fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hK0 (le_trans hka hw.1)
    have hY := hscale w (le_trans hka hw.1)
    have h1000 : 1000 ≤ w * r := by
      have := le_trans hra hw.1
      rwa [div_le_iff₀ hrp] at this
    have hle : w * r ≤ w * r' := mul_le_mul_of_nonneg_left hrr' hw0.le
    have harg := GS.arg_le_r1y y w r' hy0 hw0 hr'1
    rw [min_eq_left hw.2] at harg
    have hth := GS.r1y_le_third (w * y) hY
    exact mul_le_mul_of_nonneg_right
      (hmo (w * y) hY ⟨by linarith, by linarith⟩ ⟨by linarith, le_trans harg hth⟩ hle)
      (hφ0 w hw0.le)
  -- the integrand decreases on `(1, ∞)`
  have b3 : (∫ w in Ioi 1, OL.gYL (w * y) r' * φ w) ≤ ∫ w in Ioi 1, OL.gYL (w * y) r * φ w := by
    refine setIntegral_mono_on hint'.2 hint.2 measurableSet_Ioi fun w (hw : 1 < w) => ?_
    have hY : 3.4e23 ≤ w * y := by nlinarith
    have harg := GS.arg_le_r1y y w r' hy0 (by linarith) hr'1
    rw [min_eq_right hw.le, one_mul] at harg
    have hth := GS.r1y_le_third (w * y) hY
    exact mul_le_mul_of_nonneg_right
      (hmo (w * y) hY ⟨by linarith, by linarith⟩ ⟨by linarith, le_trans harg hth⟩ hrr')
      (hφ0 w (by linarith))
  rw [← split1, ← split2]
  linarith

/-- **[GTMonoL] on Helfgott's `φ`, PROVED** (`gtMonoL_of`, `gYMono`). -/
theorem gtMonoL_helf : OL.GTMonoL HW.phi :=
  gtMonoL_of HW.phi (fun t _ => HW.phi_nonneg t) MinSp.phi_integrableOn gYMono


/-- `log 3 ≥ 1.097483` (`2¹⁹ ≤ 3¹²`). -/
theorem log3_ge : 1.097483 ≤ Real.log 3 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 19) (by norm_num : (2 : ℝ) ^ 19 ≤ 3 ^ 12)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  have := Real.log_two_gt_d9
  generalize Real.log 3 = a at h ⊢
  generalize Real.log 2 = b at h this
  linarith

/-- `log 6 ≤ 1.79263` (`3²⁹ ≤ 2⁴⁶`). -/
theorem log6_le : Real.log 6 ≤ 1.79263 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 29) (by norm_num : (3 : ℝ) ^ 29 ≤ 2 ^ 46)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have := Real.log_two_lt_d9
  rw [h6]
  generalize Real.log 3 = a at h ⊢
  generalize Real.log 2 = b at h this ⊢
  linarith

/-- `(v³⁰)^a = vⁿ` when `30a = n`, `v > 0`. -/
theorem pow30_rpow (v : ℝ) (hv : 0 < v) (a : ℝ) (n : ℕ) (h : 30 * a = n) :
    (v ^ 30) ^ a = v ^ n := by
  rw [← Real.rpow_natCast v 30, ← Real.rpow_mul hv.le, ← Real.rpow_natCast,
    show ((30 : ℕ) : ℝ) * a = n by push_cast; linarith]

/-- `r₁(v³⁰) = (3/8)v⁸`. -/
theorem r1y_pow30 (v : ℝ) (hv : 0 < v) : MinSp.r1y (v ^ 30) = 3 / 8 * v ^ 8 := by
  unfold MinSp.r1y
  rw [pow30_rpow v hv (4 / 15) 8 (by norm_num)]

/-- **[HLeG] the `h′` side**: `h′(v³⁰) ≤ v²⁵(20.8715λ² + 43.1λ)` for `v ≥ 6.08`, `λ = log v ≥ 0`
(`√(30λ) ≤ (30λ + 54.0225)/14.7`, `v⁵ ≥ 8290`). -/
theorem hL_pow30_le (v lv : ℝ) (hv0 : 0 < v) (hv6 : 6.08 ≤ v) (hlv : lv = Real.log v)
    (hlv0 : 0 ≤ lv) : GS.hL (v ^ 30) ≤ v ^ 25 * (20.8715 * lv ^ 2 + 43.1 * lv) := by
  have hlogY : Real.log (v ^ 30) = 30 * lv := by
    rw [Real.log_pow, hlv]
    push_cast
    ring
  have hv5 : 8290 ≤ v ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hv6 5
    have h5 : (8290 : ℝ) ≤ 6.08 ^ 5 := by norm_num
    linarith
  have h30 : 0 ≤ 30 * lv := by linarith
  have hsq : Real.sqrt (30 * lv) ≤ (30 * lv + 54.0225) / 14.7 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [Real.sq_sqrt h30, Real.sqrt_nonneg (30 * lv), sq_nonneg (Real.sqrt (30 * lv) - 7.35)]
  have h32 : (30 * lv) ^ ((3 : ℝ) / 2) = 30 * lv * Real.sqrt (30 * lv) := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add' h30 (by norm_num), Real.rpow_one]
  unfold GS.hL
  rw [pow30_rpow v hv0 (5 / 6) 25 (by norm_num), pow30_rpow v hv0 (2 / 3) 20 (by norm_num), hlogY,
    h32]
  have hA : 30 * lv * Real.sqrt (30 * lv) ≤ 30 * lv * ((30 * lv + 54.0225) / 14.7) :=
    mul_le_mul_of_nonneg_left hsq h30
  have hv20 : 0 ≤ v ^ 20 := by positivity
  have hB : 45675 * lv * v ^ 20 ≤ 5.51 * lv * (v ^ 20 * v ^ 5) := by
    have := mul_le_mul_of_nonneg_left hv5 (mul_nonneg hlv0 hv20)
    nlinarith
  have e25 : v ^ 25 = v ^ 20 * v ^ 5 := by ring
  have hv25 : 0 ≤ v ^ 25 := by positivity
  have hA' := mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.3409) hv25)
  have hP0 : 0 ≤ v ^ 20 * v ^ 5 := by positivity
  rw [e25] at hA' ⊢
  generalize Real.sqrt (30 * lv) = s at hA' ⊢
  generalize v ^ 20 * v ^ 5 = P at hA' hB hP0 ⊢
  have h1 := mul_nonneg hP0 (sq_nonneg lv)
  have h2 := mul_nonneg hP0 hlv0
  have e1 : 0.3409 * P * (30 * lv * ((30 * lv + 54.0225) / 14.7)) =
      0.3409 * 30 * 30 / 14.7 * (P * lv ^ 2) + 0.3409 * 30 * 54.0225 / 14.7 * (P * lv) := by ring
  have e2 : P * (20.8715 * lv ^ 2 + 43.1 * lv) = 20.8715 * (P * lv ^ 2) + 43.1 * (P * lv) := by
    ring
  have e3 : 1522.5 * v ^ 20 * (30 * lv) = 45675 * lv * v ^ 20 := by ring
  have e4 : 5.51 * lv * P = 5.51 * (P * lv) := by ring
  rw [e1] at hA'
  rw [e2, e3]
  rw [e4] at hB
  generalize P * lv ^ 2 = X at h1 hA' ⊢
  generalize P * lv = Z at h2 hA' hB ⊢
  linarith

/-- **[HLeG] `R_{Y,2r₁(Y)} ≥ 0.647`** at `Y = v³⁰`, `λ = log v ≥ 1.78`: the inner ratio is
`(log 3 + 8λ)/(2(log(9/1.503) + 2λ)) ≥ 1.4` and `log 2.4 ≥ log 2 + 1 − 1/1.2 ≥ 0.8598`. -/
theorem rR_pow30_ge (v lv : ℝ) (hv0 : 0 < v) (hlv : lv = Real.log v) (hlv1 : 1.78 ≤ lv) :
    0.647 ≤ MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) := by
  have hl6 := log6_le
  have hl3 := log3_ge
  unfold MinSp.rR
  rw [pow30_rpow v hv0 (1 / 3) 10 (by norm_num)]
  have ea : Real.log (4 * (2 * (3 / 8 * v ^ 8))) = Real.log 3 + 8 * lv := by
    rw [show 4 * (2 * (3 / 8 * v ^ 8)) = 3 * v ^ 8 by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlv]
    push_cast
    ring
  have eb : Real.log (9 * v ^ 10 / (2.004 * (2 * (3 / 8 * v ^ 8)))) =
      Real.log (9 / 1.503) + 2 * lv := by
    rw [show 9 * v ^ 10 / (2.004 * (2 * (3 / 8 * v ^ 8))) = 9 / 1.503 * v ^ 2 by
        field_simp
        ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlv]
    push_cast
    ring
  have h96 : Real.log (9 / 1.503) ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
  have h960 : 0 ≤ Real.log (9 / 1.503) := Real.log_nonneg (by norm_num)
  have hl24 : 0.8598 ≤ Real.log 2.4 := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.2 by norm_num)
    have h2 : Real.log 2.4 = Real.log 2 + Real.log 1.2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have := Real.log_two_gt_d9
    rw [h2]
    generalize Real.log 1.2 = p at h1 ⊢
    generalize Real.log 2 = q at this ⊢
    norm_num at h1
    linarith
  rw [ea, eb]
  generalize Real.log (9 / 1.503) = m at h96 h960
  generalize Real.log 6 = c at h96 hl6
  generalize Real.log 3 = a at hl3
  have hu : 1.4 ≤ (a + 8 * lv) / (2 * (m + 2 * lv)) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hmono : Real.log 2.4 ≤ Real.log (1 + (a + 8 * lv) / (2 * (m + 2 * lv))) :=
    Real.log_le_log (by norm_num) (by linarith)
  generalize Real.log 2.4 = p at hl24 hmono
  generalize Real.log (1 + (a + 8 * lv) / (2 * (m + 2 * lv))) = q at hmono ⊢
  linarith

/-- **[HLeG] the `g` side**: `v²⁵((11.5723λ + 3.5222)v + 3.2) ≤ gYL(v³⁰, (3/8)v⁸)·v³⁰` for
`v ≥ 6.08`, `λ = log v ≥ 1.78` (`R ≥ 0.647`, `log 2r₁ ≥ 8λ − 1/3`, `ϝ ≥ 3.75`, `√(3/4) ≤ 0.8661`,
`L ≥ 0`). -/
theorem gYL_pow30_ge (v lv : ℝ) (hv0 : 0 < v) (hv6 : 6.08 ≤ v) (hlv : lv = Real.log v)
    (hlv1 : 1.78 ≤ lv) :
    v ^ 25 * ((11.5723 * lv + 3.5222) * v + 3.2) ≤ OL.gYL (v ^ 30) (3 / 8 * v ^ 8) * v ^ 30 := by
  have hv4 : 0 < v ^ 4 := by positivity
  have hv8 : 1000 ≤ 3 / 8 * v ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) hv6 8]
  have hRlo := rR_pow30_ge v lv hv0 hlv hlv1
  have hx : 8 * lv - 1 / 3 ≤ Real.log (2 * (3 / 8 * v ^ 8)) := by
    rw [show 2 * (3 / 8 * v ^ 8) = 3 / 4 * v ^ 8 by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hlv]
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
    push_cast
    generalize Real.log (3 / 4) = p at h1 ⊢
    norm_num at h1
    linarith
  have hF := GS.bigF_gt (3 / 8 * v ^ 8) (by linarith)
  have hsF : 1.9364 ≤ Real.sqrt (MinSp.bigF (3 / 8 * v ^ 8)) := by
    rw [show (1.9364 : ℝ) = Real.sqrt (1.9364 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs2t : Real.sqrt (2 * (3 / 8 * v ^ 8)) ≤ 0.8661 * v ^ 4 := by
    rw [show 2 * (3 / 8 * v ^ 8) = 3 / 4 * (v ^ 4) ^ 2 by ring, Real.sqrt_mul' _ (by positivity),
      Real.sqrt_sq hv4.le]
    have : Real.sqrt (3 / 4) ≤ 0.8661 := by
      rw [show (0.8661 : ℝ) = Real.sqrt (0.8661 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right this hv4.le
  have hs2t0 : 0 < Real.sqrt (2 * (3 / 8 * v ^ 8)) := Real.sqrt_pos.2 (by positivity)
  have hN : 0.8661 * (11.5723 * lv + 3.5222) ≤
      (MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) * Real.log (2 * (3 / 8 * v ^ 8)) + 0.5) *
        Real.sqrt (MinSp.bigF (3 / 8 * v ^ 8)) + 2.5 := by
    have h1 : 0.647 * (8 * lv - 1 / 3) ≤
        MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) * Real.log (2 * (3 / 8 * v ^ 8)) :=
      mul_le_mul hRlo hx (by linarith) (by linarith)
    have h2 := mul_le_mul (show 0.647 * (8 * lv - 1 / 3) + 0.5 ≤
      MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) * Real.log (2 * (3 / 8 * v ^ 8)) + 0.5 by linarith)
      hsF (by norm_num) (by linarith)
    generalize (MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) * Real.log (2 * (3 / 8 * v ^ 8)) + 0.5) *
      Real.sqrt (MinSp.bigF (3 / 8 * v ^ 8)) = X at h2 ⊢
    linarith
  have hT1 : (11.5723 * lv + 3.5222) / v ^ 4 ≤
      ((MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) * Real.log (2 * (3 / 8 * v ^ 8)) + 0.5) *
        Real.sqrt (MinSp.bigF (3 / 8 * v ^ 8)) + 2.5) / Real.sqrt (2 * (3 / 8 * v ^ 8)) := by
    rw [div_le_div_iff₀ hv4 hs2t0]
    have hK0 : 0 ≤ 11.5723 * lv + 3.5222 := by linarith
    calc (11.5723 * lv + 3.5222) * Real.sqrt (2 * (3 / 8 * v ^ 8))
        ≤ (11.5723 * lv + 3.5222) * (0.8661 * v ^ 4) := mul_le_mul_of_nonneg_left hs2t hK0
      _ = 0.8661 * (11.5723 * lv + 3.5222) * v ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hN hv4.le
  have hT2 : 0 ≤ OL.lLc (3 / 8 * v ^ 8) / (3 / 8 * v ^ 8) :=
    div_nonneg (GS.lLc_nonneg _ hv8) (by positivity)
  have e : ((11.5723 * lv + 3.5222) / v ^ 4 + 3.2 * (v ^ 5)⁻¹) * v ^ 30 =
      v ^ 25 * ((11.5723 * lv + 3.5222) * v + 3.2) := by
    field_simp
  unfold OL.gYL
  rw [neg_div, Real.rpow_neg (by positivity), pow30_rpow v hv0 (1 / 6) 5 (by norm_num), ← e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  generalize ((MinSp.rR (v ^ 30) (2 * (3 / 8 * v ^ 8)) * Real.log (2 * (3 / 8 * v ^ 8)) + 0.5) *
    Real.sqrt (MinSp.bigF (3 / 8 * v ^ 8)) + 2.5) / Real.sqrt (2 * (3 / 8 * v ^ 8)) = A at hT1 ⊢
  generalize OL.lLc (3 / 8 * v ^ 8) / (3 / 8 * v ^ 8) = B at hT2 ⊢
  linarith

/-- **[HLeG] the closing polynomial inequality**: `20.8715λ² + 43.1λ ≤ (11.5723λ + 3.5222)v + 3.2`
for `λ ≥ 1.78`, `v ≥ 6(λ − 0.79263)` (the quadratic `48.56λ² − 77.0λ − 13.55` is `≥ 3.2` at
`λ = 1.78` and increasing). -/
theorem hLeG_key (v lv : ℝ) (hlv1 : 1.78 ≤ lv) (hlv2 : lv ≤ 0.79263 + v / 6) :
    20.8715 * lv ^ 2 + 43.1 * lv ≤ (11.5723 * lv + 3.5222) * v + 3.2 := by
  have h1 : 0 ≤ (11.5723 * lv + 3.5222) * (v - 6 * (lv - 0.79263)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hlv1) (sub_nonneg.2 hlv1)]

/-- **[HLeG] PROVED — the second case fits under `g`**: `h′(Y) ≤ gYL(Y, r₁(Y))·Y` for every
`Y ≥ 3.4·10²³`. With `v = Y^{1/30} ≥ 6.08` (`6.08³⁰ ≤ 3.4·10²³`) and `λ = log v ∈ [1.78,
0.79263 + v/6]`: `hL_pow30_le`, `hLeG_key`, `gYL_pow30_ge` (float: worst certified gap `5.8` at
`v = 6.08`, i.e. about `4%`; the true ratio is `1.2997`). -/
theorem hLeG : GS.HLeG := by
  intro Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  obtain ⟨v, hv0, hYv⟩ : ∃ v : ℝ, 0 < v ∧ Y = v ^ 30 :=
    ⟨Y ^ ((1 : ℝ) / 30), Real.rpow_pos_of_pos hY0 _, by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num⟩
  subst hYv
  have hv6 : 6.08 ≤ v := by
    by_contra h
    have h1 : v ^ 30 < 6.08 ^ 30 := pow_lt_pow_left₀ (lt_of_not_ge h) hv0.le (by norm_num)
    have : (6.08 : ℝ) ^ 30 ≤ 3.4e23 := by norm_num
    linarith
  obtain ⟨lv, hlv⟩ : ∃ lv : ℝ, lv = Real.log v := ⟨_, rfl⟩
  have hlv1 : 1.78 ≤ lv := by
    rw [hlv, Real.le_log_iff_exp_le hv0]
    have h2 : Real.exp 1.78 * Real.exp 0.22 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      norm_num
    have he : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have h22 : 1.22 ≤ Real.exp 0.22 := by
      have := Real.add_one_le_exp (0.22 : ℝ)
      linarith
    have hp := Real.exp_pos 1.78
    nlinarith
  have hlv2 : lv ≤ 0.79263 + v / 6 := by
    have hl6 := log6_le
    have h1 := Real.log_le_sub_one_of_pos (show 0 < v / 6 by positivity)
    rw [Real.log_div hv0.ne' (by norm_num), ← hlv] at h1
    generalize Real.log 6 = c at h1 hl6
    linarith
  rw [r1y_pow30 v hv0]
  calc GS.hL (v ^ 30) ≤ v ^ 25 * (20.8715 * lv ^ 2 + 43.1 * lv) :=
        hL_pow30_le v lv hv0 hv6 hlv (by linarith)
    _ ≤ v ^ 25 * ((11.5723 * lv + 3.5222) * v + 3.2) :=
        mul_le_mul_of_nonneg_left (hLeG_key v lv hlv1 hlv2) (by positivity)
    _ ≤ _ := gYL_pow30_ge v lv hv0 hv6 hlv hlv1

end Principia.Common.TernaryGoldbach.MO
