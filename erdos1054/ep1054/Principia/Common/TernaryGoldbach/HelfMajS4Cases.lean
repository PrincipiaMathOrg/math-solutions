/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajS4Moment

set_option autoImplicit false

/-!
# S4, links `Cases2` and `Cases1` PROVED: the choice of ray

`cases2_holds : Cases2` and `cases1_holds : Cases1`. With `T = |Im w|`, `A = 2π|δ|`, `B = T/A`
(so Helfgott's `ρ = |τ|/(πδ)² = 4T/A²` and `(T/πδ)² = 4B²`, `sqB`):

* **S** (`T < 0.3375A²`, i.e. `ρ < 1.35`): the ray `θ = 0.76B/A = 0.19ρ`. `sin θ ≤ θ` and
  `cos 2θ ≥ 1 − 2θ² ≥ 0.8684` give the exponent `−Tθ + (A sin θ)²/2cos 2θ ≤ −0.426B²`
  (`caseS_data`), the GAUSSIAN term of `HM.fphi` / `f1`.
* **L1** (`0.3375A² ≤ T ≤ 0.375A²`): the FIXED ray `θ₁ = arccos(1/υ(1.5))/2` (`th1`), whose
  exponent is `−Tθ₁ + A²(υ₁ − 1)/4` EXACTLY (`caseL_facts`: `cos 2θ₁ = 1/υ₁`,
  `sin²θ₁ = (1 − 1/υ₁)/2`); with `θ₁ = E(1.5) + (υ₁ − 1)/1.5` (`th1_eq`) and the CITED
  `E(1.5) ≥ 0.1598` it is `≤ −0.426B²` (`L1_ineq`, a convex quadratic in `T/A²` that is negative
  at both ends of `[0.3375, 0.375]`; the margin at `0.375` is `1.9·10⁻⁵`), the Gaussian term again.
* **L2** (`T > 0.375A²`, i.e. `ρ > 1.5`, including `δ = 0`): the same fixed ray; now
  `A²(υ₁ − 1)/4 ≤ T(υ₁ − 1)/1.5`, so the exponent is `≤ −0.1598T`, the EXPONENTIAL term.

The only citation used is the second conjunct of `HC.AmanitaBisectCited` (`0.1598 ≤ E(1.5)`); the
bisection conjunct on `[1.19, 1.5]` is not used. The prefactors come from `Moment2` / `Moment1`
with `√(2π/c) ≤ 2.69` (S) or `≤ 2.7274` (L), `1/c ≤ 1.1516` (S) or `= υ₁ ≤ 1.18381` (L), and
`r₀ = b/c ≤ 0.8752B` (S) or `r₀² = A²υ₁(υ₁ − 1)/2` (L). Every inequality has slack except
`L1_ineq` (exact rational arithmetic).
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set Filter

/-! ## (1) The fixed ray `θ₁ = arccos(1/υ(1.5))/2` -/

theorem sqrt325_lo : 1.802775 ≤ Real.sqrt (1 + (1.5 : ℝ) ^ 2) := by
  rw [show (1.802775 : ℝ) = Real.sqrt (1.802775 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem sqrt325_hi : Real.sqrt (1 + (1.5 : ℝ) ^ 2) ≤ 1.802776 := by
  rw [show (1.802776 : ℝ) = Real.sqrt (1.802776 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- `υ(1.5) ≥ 1.1838`. -/
theorem ups_lo : 1.1838 ≤ HC.upsE 1.5 := by
  unfold HC.upsE
  rw [show (1.1838 : ℝ) = Real.sqrt (1.1838 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt
  have := sqrt325_lo
  linarith

/-- `υ(1.5) ≤ 1.18381`. -/
theorem ups_hi : HC.upsE 1.5 ≤ 1.18381 := by
  unfold HC.upsE
  rw [show (1.18381 : ℝ) = Real.sqrt (1.18381 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt
  have := sqrt325_hi
  linarith

/-- **The fixed ray** `θ₁ = arccos(1/υ(1.5))/2` (Helfgott's `θ₀ = α/2` at `ρ = 1.5`). -/
noncomputable def th1 : ℝ := Real.arccos (1 / HC.upsE 1.5) / 2

theorem x1_pos : 0 < 1 / HC.upsE 1.5 := by
  have := ups_lo
  positivity

theorem x1_lt : 1 / HC.upsE 1.5 < 1 := by
  have := ups_lo
  rw [div_lt_one (by linarith)]
  linarith

theorem cos_two_th1 : Real.cos (2 * th1) = 1 / HC.upsE 1.5 := by
  have e : 2 * th1 = Real.arccos (1 / HC.upsE 1.5) := by
    unfold th1
    ring
  rw [e, Real.cos_arccos (by linarith [x1_pos]) x1_lt.le]

theorem th1_pos : 0 < th1 := by
  unfold th1
  have := Real.arccos_pos.mpr x1_lt
  linarith

theorem th1_lt : th1 < Real.pi / 4 := by
  unfold th1
  have := Real.arccos_lt_pi_div_two.mpr x1_pos
  linarith

theorem sin_th1_nonneg : 0 ≤ Real.sin th1 :=
  Real.sin_nonneg_of_nonneg_of_le_pi th1_pos.le (by linarith [th1_lt, Real.pi_pos])

theorem sin_th1_sq : Real.sin th1 ^ 2 = (1 - 1 / HC.upsE 1.5) / 2 := by
  have h := Real.cos_two_mul th1
  have h2 := Real.cos_sq_add_sin_sq th1
  rw [cos_two_th1] at h
  linarith

/-- **The fixed ray is `E(1.5)` plus `(υ₁ − 1)/1.5`** — definitional. -/
theorem th1_eq : th1 = HC.eRho 1.5 + (HC.upsE 1.5 - 1) / 1.5 := by
  unfold th1 HC.eRho
  ring

/-- With the cited `E(1.5) ≥ 0.1598`: `θ₁ ≥ 0.1598 + (υ₁ − 1)/1.5`. -/
theorem th1_ge (hc : HC.AmanitaBisectCited) : 0.1598 + (HC.upsE 1.5 - 1) / 1.5 ≤ th1 := by
  rw [th1_eq]
  linarith [hc.2]

/-! ## (2) From a ray to a bound: the `k = 2` and `k = 1` cores -/

/-- `k = 2`: if both moment shapes are `≤ C`, then `|F_δ(w)| ≤ e^{−|τ|θ + b²/2c} C`. -/
theorem core2 (hR : RayBound) (hM : Moment2) {δ θ c b C : ℝ} {w : ℂ} (h2 : 2 < w.re)
    (h3 : w.re < 3) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 4) (hcd : c = Real.cos (2 * θ))
    (hbd : b = 2 * Real.pi * |δ| * Real.sin θ) (hX1 : b / c * gw c + 2 / c ≤ C)
    (hX2 : (b / c) ^ 2 * gw c + gw c / c ≤ C) :
    ‖Fd δ w‖ ≤ Real.exp (-(|w.im| * θ) + b ^ 2 / (2 * c)) * C := by
  have hpi := Real.pi_pos
  have hc : 0 < c := by
    rw [hcd]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  have hb : 0 ≤ b := by rw [hbd]; positivity
  have h1 := hR δ w θ (by linarith) hθ0 hθ1
  rw [← hcd, ← hbd] at h1
  have h2' := hM (w.re - 1) c b (by linarith) (by linarith) hc hb
  have hX : (2 - (w.re - 1)) * (b / c * gw c + 2 / c) +
      (w.re - 1 - 1) * ((b / c) ^ 2 * gw c + gw c / c) ≤ C := by
    have e1 := mul_le_mul_of_nonneg_left hX1 (by linarith : (0 : ℝ) ≤ 2 - (w.re - 1))
    have e2 := mul_le_mul_of_nonneg_left hX2 (by linarith : (0 : ℝ) ≤ w.re - 1 - 1)
    linarith
  rw [Real.exp_add]
  calc ‖Fd δ w‖ ≤ Real.exp (-(|w.im| * θ)) * rayInt (w.re - 1) c b := h1
    _ ≤ Real.exp (-(|w.im| * θ)) * (Real.exp (b ^ 2 / (2 * c)) *
          ((2 - (w.re - 1)) * (b / c * gw c + 2 / c) +
            (w.re - 1 - 1) * ((b / c) ^ 2 * gw c + gw c / c))) :=
        mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
    _ ≤ Real.exp (-(|w.im| * θ)) * (Real.exp (b ^ 2 / (2 * c)) * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = _ := by ring

/-- `k = 1`: if `√(2π/c) ≤ C` and `r₀√(2π/c) + 2/c ≤ C`, then `|F_δ(w)| ≤ e^{−|τ|θ + b²/2c} C`. -/
theorem core1 (hR : RayBound) (hM : Moment1) {δ θ c b C : ℝ} {w : ℂ} (h1' : 1 < w.re)
    (h2 : w.re < 2) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 4) (hcd : c = Real.cos (2 * θ))
    (hbd : b = 2 * Real.pi * |δ| * Real.sin θ) (hX0 : gw c ≤ C)
    (hX1 : b / c * gw c + 2 / c ≤ C) :
    ‖Fd δ w‖ ≤ Real.exp (-(|w.im| * θ) + b ^ 2 / (2 * c)) * C := by
  have hpi := Real.pi_pos
  have hc : 0 < c := by
    rw [hcd]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  have hb : 0 ≤ b := by rw [hbd]; positivity
  have h1 := hR δ w θ (by linarith) hθ0 hθ1
  rw [← hcd, ← hbd] at h1
  have h2' := hM (w.re - 1) c b (by linarith) (by linarith) hc hb
  have hX : (1 - (w.re - 1)) * gw c + (w.re - 1) * (b / c * gw c + 2 / c) ≤ C := by
    have e1 := mul_le_mul_of_nonneg_left hX0 (by linarith : (0 : ℝ) ≤ 1 - (w.re - 1))
    have e2 := mul_le_mul_of_nonneg_left hX1 (by linarith : (0 : ℝ) ≤ w.re - 1)
    linarith
  rw [Real.exp_add]
  calc ‖Fd δ w‖ ≤ Real.exp (-(|w.im| * θ)) * rayInt (w.re - 1) c b := h1
    _ ≤ Real.exp (-(|w.im| * θ)) * (Real.exp (b ^ 2 / (2 * c)) *
          ((1 - (w.re - 1)) * gw c + (w.re - 1) * (b / c * gw c + 2 / c))) :=
        mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
    _ ≤ Real.exp (-(|w.im| * θ)) * (Real.exp (b ^ 2 / (2 * c)) * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = _ := by ring

/-! ## (3) The data of the rays -/

/-- `(T/πδ)² = 4(T/2π|δ|)²`. -/
theorem sqB (T δ : ℝ) : (T / (Real.pi * δ)) ^ 2 = 4 * (T / (2 * Real.pi * |δ|)) ^ 2 := by
  have e1 : (T / (Real.pi * δ)) ^ 2 = (T / (Real.pi * |δ|)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  rw [e1]
  ring

/-- `2π|δ| > 0` once `T ≤ c(2π|δ|)²` for some `T ≥ 100`. -/
theorem A_pos {δ T c : ℝ} (hT : 100 ≤ T) (h : T ≤ c * (2 * Real.pi * |δ|) ^ 2) :
    0 < 2 * Real.pi * |δ| := by
  rcases (abs_nonneg δ).lt_or_eq with h0 | h0
  · exact mul_pos (by positivity) h0
  · rw [← h0, mul_zero, zero_pow two_ne_zero, mul_zero] at h
    linarith

/-- `B = T/2π|δ| ≥ 6.283` from `4π²|δ| ≤ T` (that is, `B ≥ 2π`). -/
theorem B_ge {δ T : ℝ} (hA : 0 < 2 * Real.pi * |δ|) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ T) :
    6.283 ≤ T / (2 * Real.pi * |δ|) := by
  have hpi := Real.pi_gt_d6
  have h0 : 0 ≤ Real.pi * |δ| := mul_nonneg Real.pi_pos.le (abs_nonneg δ)
  rw [le_div_iff₀ hA]
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hpi.le)]

/-- **Case S** (`T < 0.3375A²`): the ray `θ = 0.76B/A` (`= 0.19ρ`). -/
theorem caseS_data {T A θ : ℝ} (hA : 0 < A) (hT : 0 < T) (hS : T < 0.3375 * A ^ 2)
    (hθ : θ = 0.76 * (T / A) / A) :
    0 < θ ∧ θ < Real.pi / 4 ∧ 0.8684 ≤ Real.cos (2 * θ) ∧
      -(T * θ) + (A * Real.sin θ) ^ 2 / (2 * Real.cos (2 * θ)) ≤ -(0.426 * (T / A) ^ 2) ∧
      A * Real.sin θ / Real.cos (2 * θ) ≤ 0.8752 * (T / A) ∧
      0 ≤ A * Real.sin θ / Real.cos (2 * θ) := by
  have hpi := Real.pi_gt_three
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = T / A := ⟨_, rfl⟩
  rw [← hBd] at hθ ⊢
  have hB0 : 0 < B := by rw [hBd]; positivity
  have hTB : T = B * A := (div_eq_iff hA.ne').mp hBd.symm
  have hBA : B < 0.3375 * A := by
    rw [hTB] at hS
    nlinarith
  have hθA : θ * A = 0.76 * B := (eq_div_iff hA.ne').mp hθ
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθl : θ < 0.2565 := by nlinarith
  have hc : 0.8684 ≤ Real.cos (2 * θ) := by
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * θ)
    nlinarith
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  have hsb : A * Real.sin θ ≤ 0.76 * B := by
    have := mul_le_mul_of_nonneg_left (Real.sin_le hθ0.le) hA.le
    linarith
  have hAs0 : 0 ≤ A * Real.sin θ := mul_nonneg hA.le hs0
  have hTθ : T * θ = 0.76 * B ^ 2 := by
    rw [hTB]
    linear_combination B * hθA
  have hcpos : 0 < Real.cos (2 * θ) := by linarith
  refine ⟨hθ0, by linarith, hc, ?_, ?_, div_nonneg hAs0 hcpos.le⟩
  · have hb2 := pow_le_pow_left₀ hAs0 hsb 2
    have he : (A * Real.sin θ) ^ 2 / (2 * Real.cos (2 * θ)) ≤ 0.3326 * B ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg B)]
    nlinarith [sq_nonneg B]
  · rw [div_le_iff₀ hcpos]
    nlinarith [mul_nonneg hB0.le (sub_nonneg.mpr hc)]

/-- **Case L** facts for the fixed ray: `b²/2c = A²(υ₁ − 1)/4`, `(b/c)² = A²υ₁(υ₁ − 1)/2`,
`√(2π/c) ≤ 2.7274`, `1/c = υ₁`. -/
theorem caseL_facts (A : ℝ) :
    (A * Real.sin th1) ^ 2 / (2 * Real.cos (2 * th1)) = A ^ 2 * (HC.upsE 1.5 - 1) / 4 ∧
      (A * Real.sin th1 / Real.cos (2 * th1)) ^ 2 =
        A ^ 2 * HC.upsE 1.5 * (HC.upsE 1.5 - 1) / 2 ∧
      gw (Real.cos (2 * th1)) ≤ 2.7274 ∧ 1 / Real.cos (2 * th1) = HC.upsE 1.5 ∧
      0 < Real.cos (2 * th1) := by
  have hu := ups_lo
  have hu' := ups_hi
  have hu0 : HC.upsE 1.5 ≠ 0 := by linarith
  have hpi := Real.pi_lt_d6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cos_two_th1, mul_pow, sin_th1_sq]
    field_simp
    ring
  · rw [cos_two_th1, div_pow, mul_pow, sin_th1_sq]
    field_simp
  · rw [cos_two_th1, gw, show (2.7274 : ℝ) = Real.sqrt (2.7274 ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    rw [div_div_eq_mul_div, div_one]
    nlinarith
  · rw [cos_two_th1, one_div_one_div]
  · rw [cos_two_th1]
    exact x1_pos

/-- **Case L1** exponent (`0.3375A² ≤ T ≤ 0.375A²`): `−Tθ + A²κ/4 ≤ −0.1065·4(T/A)²` given
`θ ≥ 0.1598 + κ/1.5`, `κ ≤ 0.18381`. The quadratic in `T/A²` is negative on `[0.3375, 0.375]`. -/
theorem L1_ineq {T A κ θ : ℝ} (hA : 0 < A) (h1 : 0.3375 * A ^ 2 ≤ T) (h2 : T ≤ 0.375 * A ^ 2)
    (hκ : κ ≤ 0.18381) (hθ : 0.1598 + κ / 1.5 ≤ θ) :
    -(T * θ) + A ^ 2 * κ / 4 ≤ -0.1065 * (4 * (T / A) ^ 2) := by
  have hP : 0 < A ^ 2 := pow_pos hA 2
  have hT : 0 < T := by linarith
  have hθ' : 0.1598 + κ * (2 / 3) ≤ θ := by
    have e : κ / 1.5 = κ * (2 / 3) := by ring
    linarith
  have hd : (0 : ℝ) ≤ A ^ 2 / 4 - T * (2 / 3) := by linarith
  have key : (-(T * θ) + A ^ 2 * κ / 4) * A ^ 2 ≤ -(0.426 * T ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hθ' (mul_pos hT hP).le,
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr hκ) (mul_nonneg hP.le hd),
      mul_nonneg hP.le (sub_nonneg.mpr h2), mul_pos hP hP]
  have e : -0.1065 * (4 * (T / A) ^ 2) = -(0.426 * T ^ 2) / A ^ 2 := by
    rw [div_pow]
    ring
  rw [e, le_div_iff₀ hP]
  exact key

/-! ## (4) The fixed ray as a bound -/

/-- **The fixed ray, `k = 2`**: `‖F_δ(w)‖ ≤ e^{−Tθ₁ + A²(υ₁−1)/4}·C` once `C` dominates both moment
shapes for every admissible `r₀`, `g = √(2π/c)`. -/
theorem fixed2 (hR : RayBound) (hM : Moment2) {δ C : ℝ} {w : ℂ} (h2 : 2 < w.re)
    (h3 : w.re < 3)
    (hC : ∀ r g : ℝ, 0 ≤ r → 0 ≤ g → g ≤ 2.7274 →
      r ^ 2 = (2 * Real.pi * |δ|) ^ 2 * HC.upsE 1.5 * (HC.upsE 1.5 - 1) / 2 →
        r * g + 2 * HC.upsE 1.5 ≤ C ∧ r ^ 2 * g + g * HC.upsE 1.5 ≤ C) :
    ‖Fd δ w‖ ≤
      Real.exp (-(|w.im| * th1) + (2 * Real.pi * |δ|) ^ 2 * (HC.upsE 1.5 - 1) / 4) * C := by
  obtain ⟨hE, hr2, hg, hinv, hc⟩ := caseL_facts (2 * Real.pi * |δ|)
  have hb : 0 ≤ 2 * Real.pi * |δ| * Real.sin th1 :=
    mul_nonneg (by positivity) sin_th1_nonneg
  have hr0 : 0 ≤ 2 * Real.pi * |δ| * Real.sin th1 / Real.cos (2 * th1) := div_nonneg hb hc.le
  have hg0 : 0 ≤ gw (Real.cos (2 * th1)) := Real.sqrt_nonneg _
  obtain ⟨hX1, hX2⟩ := hC _ _ hr0 hg0 hg hr2
  have e2 : 2 / Real.cos (2 * th1) = 2 * HC.upsE 1.5 := by
    rw [← hinv]
    ring
  have e3 : gw (Real.cos (2 * th1)) / Real.cos (2 * th1) =
      gw (Real.cos (2 * th1)) * HC.upsE 1.5 := by
    rw [← hinv]
    ring
  have hY1 : 2 * Real.pi * |δ| * Real.sin th1 / Real.cos (2 * th1) * gw (Real.cos (2 * th1)) +
      2 / Real.cos (2 * th1) ≤ C := by
    rw [e2]
    exact hX1
  have hY2 : (2 * Real.pi * |δ| * Real.sin th1 / Real.cos (2 * th1)) ^ 2 *
      gw (Real.cos (2 * th1)) + gw (Real.cos (2 * th1)) / Real.cos (2 * th1) ≤ C := by
    rw [e3]
    exact hX2
  have key := core2 hR hM (δ := δ) (C := C) h2 h3 th1_pos th1_lt rfl rfl hY1 hY2
  rw [hE] at key
  exact key

/-- **The fixed ray, `k = 1`**. -/
theorem fixed1 (hR : RayBound) (hM : Moment1) {δ C : ℝ} {w : ℂ} (h1 : 1 < w.re)
    (h2 : w.re < 2)
    (hC : ∀ r g : ℝ, 0 ≤ r → 0 ≤ g → g ≤ 2.7274 →
      r ^ 2 = (2 * Real.pi * |δ|) ^ 2 * HC.upsE 1.5 * (HC.upsE 1.5 - 1) / 2 →
        g ≤ C ∧ r * g + 2 * HC.upsE 1.5 ≤ C) :
    ‖Fd δ w‖ ≤
      Real.exp (-(|w.im| * th1) + (2 * Real.pi * |δ|) ^ 2 * (HC.upsE 1.5 - 1) / 4) * C := by
  obtain ⟨hE, hr2, hg, hinv, hc⟩ := caseL_facts (2 * Real.pi * |δ|)
  have hb : 0 ≤ 2 * Real.pi * |δ| * Real.sin th1 :=
    mul_nonneg (by positivity) sin_th1_nonneg
  have hr0 : 0 ≤ 2 * Real.pi * |δ| * Real.sin th1 / Real.cos (2 * th1) := div_nonneg hb hc.le
  have hg0 : 0 ≤ gw (Real.cos (2 * th1)) := Real.sqrt_nonneg _
  obtain ⟨hX0, hX1⟩ := hC _ _ hr0 hg0 hg hr2
  have e2 : 2 / Real.cos (2 * th1) = 2 * HC.upsE 1.5 := by
    rw [← hinv]
    ring
  have hY1 : 2 * Real.pi * |δ| * Real.sin th1 / Real.cos (2 * th1) * gw (Real.cos (2 * th1)) +
      2 / Real.cos (2 * th1) ≤ C := by
    rw [e2]
    exact hX1
  have key := core1 hR hM (δ := δ) (C := C) h1 h2 th1_pos th1_lt rfl rfl hX0 hY1
  rw [hE] at key
  exact key

/-- `υ₁(υ₁ − 1) ∈ [0, 0.2176]`. -/
theorem ups_prod : 0 ≤ HC.upsE 1.5 * (HC.upsE 1.5 - 1) ∧
    HC.upsE 1.5 * (HC.upsE 1.5 - 1) ≤ 0.2176 := by
  have hu := ups_lo
  have hu' := ups_hi
  refine ⟨mul_nonneg (by linarith) (by linarith), ?_⟩
  have := mul_le_mul hu' (by linarith : HC.upsE 1.5 - 1 ≤ 0.18381) (by linarith)
    (by norm_num : (0 : ℝ) ≤ 1.18381)
  linarith

/-- In case L1, `r₀² ≤ 0.9552B²`. -/
theorem r0_L1 {T A r : ℝ} (hA : 0 < A) (hT : 0 < T) (h1 : 0.3375 * A ^ 2 ≤ T)
    (hr2 : r ^ 2 = A ^ 2 * HC.upsE 1.5 * (HC.upsE 1.5 - 1) / 2) :
    r ^ 2 ≤ 0.9552 * (T / A) ^ 2 := by
  obtain ⟨hk0, hk1⟩ := ups_prod
  have hA2 : A ^ 2 ≤ 80 / 27 * T := by linarith
  have hBT : 0.3375 * T ≤ (T / A) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos hA 2)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hT.le]
  have := mul_le_mul hA2 hk1 hk0 (by positivity)
  rw [hr2]
  linarith

/-- In case L2, `r₀² ≤ 0.29014T`. -/
theorem r0_L2 {T A r : ℝ} (hT : 0 < T) (h1 : 0.375 * A ^ 2 < T)
    (hr2 : r ^ 2 = A ^ 2 * HC.upsE 1.5 * (HC.upsE 1.5 - 1) / 2) :
    r ^ 2 ≤ 0.29014 * T := by
  obtain ⟨hk0, hk1⟩ := ups_prod
  have hA2 : A ^ 2 ≤ 8 / 3 * T := by linarith
  have := mul_le_mul hA2 hk1 hk0 (by positivity)
  rw [hr2]
  linarith

/-- The L2 exponent: `−Tθ₁ + A²(υ₁ − 1)/4 ≤ −0.1598T` when `A² < T/0.375`. -/
theorem L2_ineq (hc : HC.AmanitaBisectCited) {T A : ℝ} (hT : 0 < T) (h1 : 0.375 * A ^ 2 < T) :
    -(T * th1) + A ^ 2 * (HC.upsE 1.5 - 1) / 4 ≤ -0.1598 * T := by
  have hθ0 := th1_ge hc
  have hu := ups_lo
  have hθ : 0.1598 + (HC.upsE 1.5 - 1) * (2 / 3) ≤ th1 := by
    have e : (HC.upsE 1.5 - 1) / 1.5 = (HC.upsE 1.5 - 1) * (2 / 3) := by ring
    linarith
  have hA2 : A ^ 2 ≤ 8 / 3 * T := by linarith
  have e1 := mul_le_mul_of_nonneg_left hθ hT.le
  have e2 := mul_le_mul_of_nonneg_right hA2 (by linarith : (0 : ℝ) ≤ HC.upsE 1.5 - 1)
  linarith

/-! ## (5) `k = 2`: the three cases and `Cases2` -/

theorem decay2_S (hR : RayBound) (hM : Moment2) {δ : ℝ} {w : ℂ} (h2 : 2 < w.re)
    (h3 : w.re < 3) (hT : 100 ≤ |w.im|) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ |w.im|)
    (hS : |w.im| < 0.3375 * (2 * Real.pi * |δ|) ^ 2) :
    ‖Fd δ w‖ ≤ 3.262 * ((|w.im| / (2 * Real.pi * |δ|)) ^ 2 *
      Real.exp (-0.1065 * (|w.im| / (Real.pi * δ)) ^ 2)) := by
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have hA := A_pos hT hS.le
  have hB := B_ge hA hTd
  rw [sqB]
  obtain ⟨T, hTd'⟩ : ∃ T : ℝ, T = |w.im| := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = 2 * Real.pi * |δ| := ⟨_, rfl⟩
  rw [← hTd'] at hT hS hB ⊢
  rw [← hAd] at hS hA hB ⊢
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = 0.76 * (T / A) / A := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1, hc, he, hr, hr0⟩ := caseS_data hA (by linarith) hS hθd
  have hcpos : 0 < Real.cos (2 * θ) := by linarith
  have hg : gw (Real.cos (2 * θ)) ≤ 2.69 := by
    rw [gw, show (2.69 : ℝ) = Real.sqrt (2.69 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hcpos]
    nlinarith
  have hg0 : 0 ≤ gw (Real.cos (2 * θ)) := Real.sqrt_nonneg _
  have hic : 1 / Real.cos (2 * θ) ≤ 1.1516 := by
    rw [div_le_iff₀ hcpos]
    linarith
  have hic0 : 0 ≤ 1 / Real.cos (2 * θ) := div_nonneg zero_le_one hcpos.le
  have hBB : 6.283 * (T / A) ≤ (T / A) ^ 2 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hB (by linarith)
  have hbA : 2 * Real.pi * |δ| * Real.sin θ = A * Real.sin θ := by rw [hAd]
  have hX1 : A * Real.sin θ / Real.cos (2 * θ) * gw (Real.cos (2 * θ)) +
      2 / Real.cos (2 * θ) ≤ 3.262 * (T / A) ^ 2 := by
    have h1 : A * Real.sin θ / Real.cos (2 * θ) * gw (Real.cos (2 * θ)) ≤
        0.8752 * (T / A) * 2.69 :=
      mul_le_mul hr hg hg0 (by linarith)
    have h2' : 2 / Real.cos (2 * θ) = 2 * (1 / Real.cos (2 * θ)) := by ring
    rw [h2']
    linarith
  have hX2 : (A * Real.sin θ / Real.cos (2 * θ)) ^ 2 * gw (Real.cos (2 * θ)) +
      gw (Real.cos (2 * θ)) / Real.cos (2 * θ) ≤ 3.262 * (T / A) ^ 2 := by
    have h1 : (A * Real.sin θ / Real.cos (2 * θ)) ^ 2 * gw (Real.cos (2 * θ)) ≤
        (0.8752 * (T / A)) ^ 2 * 2.69 :=
      mul_le_mul (pow_le_pow_left₀ hr0 hr 2) hg hg0 (by positivity)
    have h2' : gw (Real.cos (2 * θ)) / Real.cos (2 * θ) ≤ 2.69 * 1.1516 := by
      rw [show gw (Real.cos (2 * θ)) / Real.cos (2 * θ) =
        gw (Real.cos (2 * θ)) * (1 / Real.cos (2 * θ)) by ring]
      exact mul_le_mul hg hic hic0 (by norm_num)
    nlinarith
  have key := core2 hR hM (C := 3.262 * (T / A) ^ 2) h2 h3 hθ0 hθ1 rfl hbA.symm hX1 hX2
  rw [← hTd'] at key
  calc ‖Fd δ w‖ ≤ _ := key
    _ ≤ Real.exp (-0.1065 * (4 * (T / A) ^ 2)) * (3.262 * (T / A) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
        linarith
    _ = _ := by ring

theorem decay2_L1 (hc : HC.AmanitaBisectCited) (hR : RayBound) (hM : Moment2) {δ : ℝ}
    {w : ℂ} (h2 : 2 < w.re) (h3 : w.re < 3) (hT : 100 ≤ |w.im|)
    (hTd : 4 * Real.pi ^ 2 * |δ| ≤ |w.im|) (hL1 : 0.3375 * (2 * Real.pi * |δ|) ^ 2 ≤ |w.im|)
    (hL2 : |w.im| ≤ 0.375 * (2 * Real.pi * |δ|) ^ 2) :
    ‖Fd δ w‖ ≤ 3.262 * ((|w.im| / (2 * Real.pi * |δ|)) ^ 2 *
      Real.exp (-0.1065 * (|w.im| / (Real.pi * δ)) ^ 2)) := by
  have hu := ups_lo
  have hu' := ups_hi
  have hA := A_pos hT hL2
  have hB := B_ge hA hTd
  rw [sqB]
  have key := fixed2 hR hM (δ := δ) (C := 3.262 * (|w.im| / (2 * Real.pi * |δ|)) ^ 2) h2 h3
    fun r g hr hg hg' hr2 => by
      have hr2' := r0_L1 hA (by linarith) hL1 hr2
      have hBB : 6.283 * (|w.im| / (2 * Real.pi * |δ|)) ≤ (|w.im| / (2 * Real.pi * |δ|)) ^ 2 := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hB (by linarith)
      have hr1 : r ≤ (1 + r ^ 2) / 2 := by nlinarith [sq_nonneg (r - 1)]
      have h5 : r * g ≤ (1 + 0.9552 * (|w.im| / (2 * Real.pi * |δ|)) ^ 2) / 2 * 2.7274 :=
        (mul_le_mul_of_nonneg_right hr1 hg).trans
          (mul_le_mul (by linarith) hg' hg (by positivity))
      have h6 : r ^ 2 * g ≤ 0.9552 * (|w.im| / (2 * Real.pi * |δ|)) ^ 2 * 2.7274 :=
        mul_le_mul hr2' hg' hg (by positivity)
      have h7 : g * HC.upsE 1.5 ≤ 2.7274 * 1.18381 :=
        mul_le_mul hg' hu' (by linarith) (by norm_num)
      constructor <;> nlinarith
  have hex := L1_ineq hA hL1 hL2 (by linarith : HC.upsE 1.5 - 1 ≤ 0.18381) (th1_ge hc)
  calc ‖Fd δ w‖ ≤ _ := key
    _ ≤ Real.exp (-0.1065 * (4 * (|w.im| / (2 * Real.pi * |δ|)) ^ 2)) *
          (3.262 * (|w.im| / (2 * Real.pi * |δ|)) ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hex) (by positivity)
    _ = _ := by ring

theorem decay2_L2 (hc : HC.AmanitaBisectCited) (hR : RayBound) (hM : Moment2) {δ : ℝ}
    {w : ℂ} (h2 : 2 < w.re) (h3 : w.re < 3) (hT : 100 ≤ |w.im|)
    (hL : 0.375 * (2 * Real.pi * |δ|) ^ 2 < |w.im|) :
    ‖Fd δ w‖ ≤ 3.262 * (|w.im| * Real.exp (-0.1598 * |w.im|)) := by
  have hu := ups_lo
  have hu' := ups_hi
  have key := fixed2 hR hM (δ := δ) (C := 3.262 * |w.im|) h2 h3 fun r g hr hg hg' hr2 => by
    have hr2' := r0_L2 (by linarith) hL hr2
    have hr1 : r ≤ (1 + r ^ 2) / 2 := by nlinarith [sq_nonneg (r - 1)]
    have h5 : r * g ≤ (1 + 0.29014 * |w.im|) / 2 * 2.7274 :=
      (mul_le_mul_of_nonneg_right hr1 hg).trans (mul_le_mul (by linarith) hg' hg (by positivity))
    have h6 : r ^ 2 * g ≤ 0.29014 * |w.im| * 2.7274 := mul_le_mul hr2' hg' hg (by positivity)
    have h7 : g * HC.upsE 1.5 ≤ 2.7274 * 1.18381 := mul_le_mul hg' hu' (by linarith) (by norm_num)
    constructor <;> nlinarith
  have hex := L2_ineq hc (by linarith) hL
  calc ‖Fd δ w‖ ≤ _ := key
    _ ≤ Real.exp (-0.1598 * |w.im|) * (3.262 * |w.im|) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hex) (by positivity)
    _ = _ := by ring

/-- **LINK [Cases2] PROVED** — `cor:amanita1` at `k = 2` with `c₂ = 3.262`, from the two rays. -/
theorem cases2_holds : Cases2 := by
  intro hc hR hM δ w h2 h3 hT hTd
  have hpos1 : 0 ≤ |w.im| * Real.exp (-0.1598 * |w.im|) := by positivity
  have hpos2 : 0 ≤ (|w.im| / (2 * Real.pi * |δ|)) ^ 2 *
      Real.exp (-0.1065 * (|w.im| / (Real.pi * δ)) ^ 2) := by positivity
  unfold HM.fphi
  rcases lt_or_ge |w.im| (0.3375 * (2 * Real.pi * |δ|) ^ 2) with hS | hS
  · have := decay2_S hR hM h2 h3 hT hTd hS
    linarith
  · rcases le_or_gt |w.im| (0.375 * (2 * Real.pi * |δ|) ^ 2) with hL | hL
    · have := decay2_L1 hc hR hM h2 h3 hT hTd hS hL
      linarith
    · have := decay2_L2 hc hR hM h2 h3 hT hL
      linarith

/-! ## (6) `k = 1`: the three cases and `Cases1` -/

theorem decay1_S (hR : RayBound) (hM : Moment1) {δ : ℝ} {w : ℂ} (h1 : 1 < w.re)
    (h2 : w.re < 2) (hT : 100 ≤ |w.im|) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ |w.im|)
    (hS : |w.im| < 0.3375 * (2 * Real.pi * |δ|) ^ 2) :
    ‖Fd δ w‖ ≤ 3.1 * (|w.im| / (2 * Real.pi * |δ|) *
      Real.exp (-0.1065 * (|w.im| / (Real.pi * δ)) ^ 2)) := by
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have hA := A_pos hT hS.le
  have hB := B_ge hA hTd
  rw [sqB]
  obtain ⟨T, hTd'⟩ : ∃ T : ℝ, T = |w.im| := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = 2 * Real.pi * |δ| := ⟨_, rfl⟩
  rw [← hTd'] at hT hS hB ⊢
  rw [← hAd] at hS hA hB ⊢
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = 0.76 * (T / A) / A := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1, hc, he, hr, hr0⟩ := caseS_data hA (by linarith) hS hθd
  have hcpos : 0 < Real.cos (2 * θ) := by linarith
  have hg : gw (Real.cos (2 * θ)) ≤ 2.69 := by
    rw [gw, show (2.69 : ℝ) = Real.sqrt (2.69 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hcpos]
    nlinarith
  have hg0 : 0 ≤ gw (Real.cos (2 * θ)) := Real.sqrt_nonneg _
  have hic : 1 / Real.cos (2 * θ) ≤ 1.1516 := by
    rw [div_le_iff₀ hcpos]
    linarith
  have hbA : 2 * Real.pi * |δ| * Real.sin θ = A * Real.sin θ := by rw [hAd]
  have hX0 : gw (Real.cos (2 * θ)) ≤ 3.1 * (T / A) := by linarith
  have hX1 : A * Real.sin θ / Real.cos (2 * θ) * gw (Real.cos (2 * θ)) +
      2 / Real.cos (2 * θ) ≤ 3.1 * (T / A) := by
    have h1' : A * Real.sin θ / Real.cos (2 * θ) * gw (Real.cos (2 * θ)) ≤
        0.8752 * (T / A) * 2.69 :=
      mul_le_mul hr hg hg0 (by linarith)
    have h2' : 2 / Real.cos (2 * θ) = 2 * (1 / Real.cos (2 * θ)) := by ring
    rw [h2']
    linarith
  have key := core1 hR hM (C := 3.1 * (T / A)) h1 h2 hθ0 hθ1 rfl hbA.symm hX0 hX1
  rw [← hTd'] at key
  calc ‖Fd δ w‖ ≤ _ := key
    _ ≤ Real.exp (-0.1065 * (4 * (T / A) ^ 2)) * (3.1 * (T / A)) := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by linarith)
        linarith
    _ = _ := by ring

theorem decay1_L1 (hc : HC.AmanitaBisectCited) (hR : RayBound) (hM : Moment1) {δ : ℝ}
    {w : ℂ} (h1 : 1 < w.re) (h2 : w.re < 2) (hT : 100 ≤ |w.im|)
    (hTd : 4 * Real.pi ^ 2 * |δ| ≤ |w.im|) (hL1 : 0.3375 * (2 * Real.pi * |δ|) ^ 2 ≤ |w.im|)
    (hL2 : |w.im| ≤ 0.375 * (2 * Real.pi * |δ|) ^ 2) :
    ‖Fd δ w‖ ≤ 3.1 * (|w.im| / (2 * Real.pi * |δ|) *
      Real.exp (-0.1065 * (|w.im| / (Real.pi * δ)) ^ 2)) := by
  have hu := ups_lo
  have hu' := ups_hi
  have hA := A_pos hT hL2
  have hB := B_ge hA hTd
  rw [sqB]
  have key := fixed1 hR hM (δ := δ) (C := 3.1 * (|w.im| / (2 * Real.pi * |δ|))) h1 h2
    fun r g hr hg hg' hr2 => by
      have hr2' := r0_L1 hA (by linarith) hL1 hr2
      have hrB : r ≤ 0.9774 * (|w.im| / (2 * Real.pi * |δ|)) := by
        refine le_of_pow_le_pow_left₀ two_ne_zero (by linarith) ?_
        rw [mul_pow]
        nlinarith [sq_nonneg (|w.im| / (2 * Real.pi * |δ|))]
      have h5 : r * g ≤ 0.9774 * (|w.im| / (2 * Real.pi * |δ|)) * 2.7274 :=
        mul_le_mul hrB hg' hg (by linarith)
      constructor <;> nlinarith
  have hex := L1_ineq hA hL1 hL2 (by linarith : HC.upsE 1.5 - 1 ≤ 0.18381) (th1_ge hc)
  calc ‖Fd δ w‖ ≤ _ := key
    _ ≤ Real.exp (-0.1065 * (4 * (|w.im| / (2 * Real.pi * |δ|)) ^ 2)) *
          (3.1 * (|w.im| / (2 * Real.pi * |δ|))) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hex) (by positivity)
    _ = _ := by ring

theorem decay1_L2 (hc : HC.AmanitaBisectCited) (hR : RayBound) (hM : Moment1) {δ : ℝ}
    {w : ℂ} (h1 : 1 < w.re) (h2 : w.re < 2) (hT : 100 ≤ |w.im|)
    (hL : 0.375 * (2 * Real.pi * |δ|) ^ 2 < |w.im|) :
    ‖Fd δ w‖ ≤ 3.1 * (Real.sqrt |w.im| * Real.exp (-0.1598 * |w.im|)) := by
  have hu := ups_lo
  have hu' := ups_hi
  have hq : 10 ≤ Real.sqrt |w.im| := by
    rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hqq : Real.sqrt |w.im| ^ 2 = |w.im| := Real.sq_sqrt (abs_nonneg _)
  have key := fixed1 hR hM (δ := δ) (C := 3.1 * Real.sqrt |w.im|) h1 h2
    fun r g hr hg hg' hr2 => by
      have hr2' := r0_L2 (by linarith) hL hr2
      have hrq : r ≤ 0.5387 * Real.sqrt |w.im| := by
        refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
        rw [mul_pow, hqq]
        nlinarith
      have h5 : r * g ≤ 0.5387 * Real.sqrt |w.im| * 2.7274 :=
        mul_le_mul hrq hg' hg (by positivity)
      constructor <;> nlinarith
  have hex := L2_ineq hc (by linarith) hL
  calc ‖Fd δ w‖ ≤ _ := key
    _ ≤ Real.exp (-0.1598 * |w.im|) * (3.1 * Real.sqrt |w.im|) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hex) (by positivity)
    _ = _ := by ring

/-- **LINK [Cases1] PROVED** — the `k = 1` decay with prefactor `3.1`, from the two rays. -/
theorem cases1_holds : Cases1 := by
  intro hc hR hM δ w h1 h2 hT hTd
  have hpos1 : 0 ≤ Real.sqrt |w.im| * Real.exp (-0.1598 * |w.im|) := by positivity
  have hpos2 : 0 ≤ |w.im| / (2 * Real.pi * |δ|) *
      Real.exp (-0.1065 * (|w.im| / (Real.pi * δ)) ^ 2) := by positivity
  unfold f1
  rcases lt_or_ge |w.im| (0.3375 * (2 * Real.pi * |δ|) ^ 2) with hS | hS
  · have := decay1_S hR hM h1 h2 hT hTd hS
    linarith
  · rcases le_or_gt |w.im| (0.375 * (2 * Real.pi * |δ|) ^ 2) with hL | hL
    · have := decay1_L1 hc hR hM h1 h2 hT hTd hS hL
      linarith
    · have := decay1_L2 hc hR hM h1 h2 hT hL
      linarith

/-! ## (7) `PhiShift` and `HM.PhiDecay` -/

/-- `G_δ^φ(s) = F_δ(s + 2)`: `φ(t) = t²e^{−t²/2}` and `mellin (t^a f) s = mellin f (s + a)`. -/
theorem Gm_phi_eq (δ : ℝ) (s : ℂ) : HM.Gm HW.phi δ s = Fd δ (s + 2) := by
  rw [Fd, ← mellin_cpow_smul, HM.Gm]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, HW.phi]
  rw [show ((t : ℂ) ^ (2 : ℂ)) = (t : ℂ) ^ (2 : ℕ) from Complex.cpow_ofNat _ 2]
  push_cast
  ring

/-- **LINK [PhiShift] PROVED**. -/
theorem phiShift_holds : PhiShift := by
  intro hD δ s h0 h1 hT hTd
  have hre : (s + 2).re = s.re + 2 := by simp
  have him : (s + 2).im = s.im := by simp
  rw [Gm_phi_eq, ← him]
  exact hD δ (s + 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hT)
    (by rw [him]; exact hTd)

/-- **`HM.PhiDecay` PROVED** — `cor:amanita1` at `k = 2` with Helfgott's `c₂ = 3.262`, from the
CITED `E(1.5) ≥ 0.1598` (`HC.AmanitaBisectCited`, its second conjunct) and nothing else. -/
theorem phiDecay_holds (hc : HC.AmanitaBisectCited) : HM.PhiDecay :=
  phiDecay_of_links hc rayBound_holds moment2_holds cases2_holds phiShift_holds

end Principia.Common.TernaryGoldbach.S4
