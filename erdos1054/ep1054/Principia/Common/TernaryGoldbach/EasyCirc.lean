/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BandLimit
import Principia.Common.TernaryGoldbach.MajorSpine
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

set_option autoImplicit false

/-!
# The elementary norms of Helfgott's `η∘`, and `BandSharp`

Five of `EN.NormsE`'s nine conjuncts, on Helfgott's FIXED weights, each checked numerically first
(`scratchpad/easy_numbers.py`, `easy_polys.py`):

* `l2_circ_lo`, `l2_circ_hi` — `0.8 ≤ |η∘|₂ ≤ 0.8002`. With `u = t − 1`,
  `|η∘|₂² = ∫₋₁¹ (1−u²)⁶e^{−u²} du` (`circ_sq_int`), and `|e^{−v} − T₄(v)| ≤ v⁵/100` on `[0,1]`
  (`exp_neg_taylor`, `Real.exp_bound` at `n = 5`) squeezes it between two exact polynomial
  integrals: `0.64020538 ≤ |η∘|₂² ≤ 0.64021089` (truth `0.64020600`).
* `l2_deriv_sq_le` — `|η∘'|₂² ≤ 3`: `η∘' = −u(1−u²)²(7−u²)e^{−u²/2}` on `[0,2]` (`dCirc_eq`, from
  `BL.hasDerivAt_hFun`), so `|η∘'|₂² ≤ ∫₋₁¹ u²(1−u²)⁴(7−u²)²(T₄(u²) + u¹⁰/100) = 2.7379531`
  (truth `2.7375293`).
* `l1_etaPlus_le` — `|η₊|₁ ≤ 1.2`, from `BL.band_uniform` alone: `|η₊| ≤ |η∘| + 0.13·te^{−t²/2}`,
  `|η∘|₁ ≤ ∫₋₁¹(1−u²)³ = 32/35`, `∫₀^∞ te^{−t²/2} = 1`: `32/35 + 0.13 = 1.0443`.
* `BandSharp` — **the ONE analytic obligation left in `NormsE`'s band-limiting conjuncts**:
  `|h₂₀₀(t) − h(t)| ≤ 4.5·10⁻⁵` for `t > 0` (true sup `1.138·10⁻⁵` at `t ≈ 2.0004`;
  `BL.band_uniform` proves `0.1185`). `l2_diff_band : BandSharp → |η₊ − η∘|₂ ≤ 3·10⁻⁵` via
  `|η₊ − η∘|₂ ≤ c·(∫t²e^{−t²})^{1/2} = c·(√π/4)^{1/2} ≤ 0.6666c`, and
  `l2_plus_band : BandSharp → |η₊|₂ ≤ 0.81` via `|η₊|₂² ≤ |η∘|₂² + 2c + c²√π/4`. Both go through
  generic statements for ANY `g` with `|g − h| ≤ c` (`l2_diff_of_unif`, `l2_plus_of_unif`), whose
  hypothesis is discharged once by `g = h` itself (`l2_diff_self`, `l2_plus_self`).

Tools: `int_poly` (the exact integral of `∑ c_k u^k`), `setInt_Ioi_02` (a weight vanishing past
`2` integrates over `[0,2]`), `gauss_moment` (`∫₀^∞ x^q e^{−bx²}` from Mathlib's Gamma integral).
-/

namespace Principia.Common.TernaryGoldbach.EN

open MeasureTheory Set Filter

/-! ## Tools -/

/-- `T₄(v) = 1 − v + v²/2 − v³/6 + v⁴/24`, the fourth Taylor polynomial of `e^{−v}`. -/
noncomputable def T4 (v : ℝ) : ℝ := 1 - v + v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 24

/-- **`|e^{−v} − T₄(v)| ≤ v⁵/100` on `[0, 1]`** (`Real.exp_bound`, `n = 5`: `6/(5!·5) = 1/100`). -/
theorem exp_neg_taylor {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    T4 v - v ^ 5 / 100 ≤ Real.exp (-v) ∧ Real.exp (-v) ≤ T4 v + v ^ 5 / 100 := by
  have hb : |-v| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound hb (n := 5) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h' := abs_le.mp h
  unfold T4
  constructor <;> linarith [h'.1, h'.2]

/-- **The exact integral of a polynomial** `∑_{k<n} c_k u^k` over `[a, b]`. -/
theorem int_poly {n : ℕ} (c : Fin n → ℝ) (a b : ℝ) :
    ∫ u in a..b, ∑ k : Fin n, c k * u ^ (k : ℕ) =
      ∑ k : Fin n, c k * ((b ^ ((k : ℕ) + 1) - a ^ ((k : ℕ) + 1)) / (((k : ℕ) : ℝ) + 1)) := by
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      IntervalIntegrable (fun u : ℝ => c k * u ^ (k : ℕ)) volume a b := fun k _ =>
    (continuous_const.mul (continuous_pow (k : ℕ))).intervalIntegrable a b
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]

/-- A function vanishing on `(2, ∞)` integrates over `(0, ∞)` as over `[0, 2]`. -/
theorem setInt_Ioi_02 (f : ℝ → ℝ) (hf : ∀ t : ℝ, 2 < t → f t = 0) :
    ∫ t in Ioi (0 : ℝ), f t = ∫ t in (0 : ℝ)..2, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun t ht => hf t ?_
  obtain ⟨h1, h2⟩ := ht
  by_contra hc
  exact h2 ⟨h1, not_lt.mp hc⟩

/-- A continuous function vanishing on `(2, ∞)` is integrable on `(0, ∞)`. -/
theorem integrableOn_of_cont (f : ℝ → ℝ) (hc : Continuous f) (hf : ∀ t : ℝ, 2 < t → f t = 0) :
    IntegrableOn f (Ioi 0) := by
  refine IntegrableOn.of_forall_sdiff_eq_zero
    ((hc.integrableOn_Icc (a := 0) (b := 2)).mono_set Ioc_subset_Icc_self) measurableSet_Ioi
    fun t ht => hf t ?_
  obtain ⟨h1, h2⟩ := ht
  by_contra hcon
  exact h2 ⟨h1, not_lt.mp hcon⟩

/-- **Gaussian moments** `∫₀^∞ x^q e^{−bx²} = b^{−(q+1)/2}·Γ((q+1)/2)/2` (Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` at `p = 2`). -/
theorem gauss_moment (q b : ℝ) (hq : -1 < q) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-b * x ^ 2) =
      b ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (by norm_num) hq hb
  simp_rw [Real.rpow_two] at h
  exact h

/-- `Γ(3/2) = √π/2`. -/
theorem gamma_three_half : Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 2 := by
  rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

/-- **`∫₀^∞ t e^{−t²/2} dt = 1`.** -/
theorem int_t_exp : ∫ t in Ioi (0 : ℝ), t * Real.exp (-t ^ 2 / 2) = 1 := by
  have h := gauss_moment 1 (1 / 2) (by norm_num) (by norm_num)
  have e : (fun t : ℝ => t * Real.exp (-t ^ 2 / 2)) =
      fun t => t ^ (1 : ℝ) * Real.exp (-(1 / 2) * t ^ 2) := by
    funext t
    rw [Real.rpow_one]
    congr 2
    ring
  rw [e, h, show -((1 : ℝ) + 1) / 2 = -1 by norm_num, show ((1 : ℝ) + 1) / 2 = 1 by norm_num,
    Real.rpow_neg_one, Real.Gamma_one]
  norm_num

/-- `t e^{−t²/2}` is integrable on `(0, ∞)` (its integral is `1 ≠ 0`). -/
theorem integrable_t_exp :
    Integrable (fun t : ℝ => t * Real.exp (-t ^ 2 / 2)) (volume.restrict (Ioi 0)) :=
  Integrable.of_integral_ne_zero (by rw [int_t_exp]; norm_num)

/-- **`∫₀^∞ t² e^{−t²} dt = √π/4`.** -/
theorem int_t2_exp : ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-t ^ 2) = Real.sqrt Real.pi / 4 := by
  have h := gauss_moment 2 1 (by norm_num) (by norm_num)
  have e : (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2)) =
      fun t => t ^ (2 : ℝ) * Real.exp (-1 * t ^ 2) := by
    funext t
    rw [Real.rpow_two, neg_one_mul]
  rw [e, h, gamma_three_half, Real.one_rpow]
  ring

/-- `t² e^{−t²}` is integrable on `(0, ∞)` (its integral is `√π/4 ≠ 0`). -/
theorem integrable_t2_exp :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2)) (volume.restrict (Ioi 0)) :=
  Integrable.of_integral_ne_zero (by
    rw [int_t2_exp]
    positivity)

/-- `√π/4 ≤ 0.44314` (truth `0.4431135`), from `π < 3.141593`. -/
theorem sqrt_pi_quarter_le : Real.sqrt Real.pi / 4 ≤ 0.44314 := by
  have h : Real.sqrt Real.pi ≤ 1.77256 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith [Real.pi_lt_d6]
  linarith

/-! ## `η∘` on `[0, 2]` -/

/-- `η∘` vanishes on `(2, ∞)`. -/
theorem etaCirc_of_two_lt {t : ℝ} (ht : 2 < t) : HW.etaCirc t = 0 := by
  rw [HW.etaCirc, HW.hFun_of_two_le ht.le]
  ring

/-- `η∘` is continuous. -/
theorem continuous_etaCirc : Continuous HW.etaCirc :=
  (BL.continuous_hFun.mul continuous_id).mul (by fun_prop)

/-- `η∘(t)² = (1 − (t−1)²)⁶ e^{−(t−1)²}` on `[0, 2]`. -/
theorem etaCirc_sq_eq {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    HW.etaCirc t ^ 2 = (1 - (t - 1) ^ 2) ^ 6 * Real.exp (-(t - 1) ^ 2) := by
  have he : Real.exp (-(t - 1) ^ 2 / 2) ^ 2 = Real.exp (-(t - 1) ^ 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [HW.etaCirc_eq h0 h2]
  calc (t ^ 3 * (2 - t) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2)) ^ 2
      = (t * (2 - t)) ^ 6 * Real.exp (-(t - 1) ^ 2 / 2) ^ 2 := by ring
    _ = (1 - (t - 1) ^ 2) ^ 6 * Real.exp (-(t - 1) ^ 2) := by rw [he]; ring

/-- **`|η∘|₂² = ∫₋₁¹ (1−u²)⁶e^{−u²} du`** (`u = t − 1`). -/
theorem circ_sq_int : ∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2 =
    ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2) := by
  rw [setInt_Ioi_02 _ fun t ht => by rw [etaCirc_of_two_lt ht]; ring]
  have hc : EqOn (fun t => HW.etaCirc t ^ 2)
      (fun t => (1 - (t - 1) ^ 2) ^ 6 * Real.exp (-(t - 1) ^ 2)) (uIcc 0 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact etaCirc_sq_eq ht.1 ht.2
  rw [intervalIntegral.integral_congr hc]
  calc ∫ t in (0 : ℝ)..2, (1 - (t - 1) ^ 2) ^ 6 * Real.exp (-(t - 1) ^ 2)
      = ∫ u in (0 - 1 : ℝ)..(2 - 1), (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2) :=
        intervalIntegral.integral_comp_sub_right (fun u => (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2)) 1
    _ = ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2) := by norm_num

/-- `∫₋₁¹ (1−u²)⁶(T₄(u²) − u¹⁰/100) = 3213568256/5019589575 = 0.64020538`. -/
theorem int_Plo : ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * (T4 (u ^ 2) - (u ^ 2) ^ 5 / 100) =
    3213568256 / 5019589575 := by
  have h : EqOn (fun u : ℝ => (1 - u ^ 2) ^ 6 * (T4 (u ^ 2) - (u ^ 2) ^ 5 / 100))
      (fun u => ∑ k : Fin 23, (![1, 0, -7, 0, 43/2, 0, -229/6, 0, 1045/24, 0, -844/25, 0,
        11111/600, 0, -449/60, 0, 93/40, 0, -17/30, 0, 61/600, 0, -1/100] : Fin 23 → ℝ) k *
          u ^ (k : ℕ)) (uIcc (-1) 1) := by
    intro u _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, T4]
    ring
  rw [intervalIntegral.integral_congr h, int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- `∫₋₁¹ (1−u²)⁶(T₄(u²) + u¹⁰/100) = 3213595904/5019589575 = 0.64021089`. -/
theorem int_Phi : ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100) =
    3213595904 / 5019589575 := by
  have h : EqOn (fun u : ℝ => (1 - u ^ 2) ^ 6 * (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100))
      (fun u => ∑ k : Fin 23, (![1, 0, -7, 0, 43/2, 0, -229/6, 0, 1045/24, 0, -1687/50, 0,
        11039/600, 0, -431/60, 0, 77/40, 0, -4/15, 0, -11/600, 0, 1/100] : Fin 23 → ℝ) k *
          u ^ (k : ℕ)) (uIcc (-1) 1) := by
    intro u _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, T4]
    ring
  rw [intervalIntegral.integral_congr h, int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- For `u ∈ [−1, 1]`: `T₄(u²) − u¹⁰/100 ≤ e^{−u²} ≤ T₄(u²) + u¹⁰/100`. -/
theorem exp_sq_taylor {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    T4 (u ^ 2) - (u ^ 2) ^ 5 / 100 ≤ Real.exp (-u ^ 2) ∧
      Real.exp (-u ^ 2) ≤ T4 (u ^ 2) + (u ^ 2) ^ 5 / 100 :=
  exp_neg_taylor (sq_nonneg u) (by nlinarith [hu.1, hu.2])

/-- **`0.64 ≤ ∫₋₁¹ (1−u²)⁶e^{−u²} ≤ 0.64032`.** -/
theorem G6_bounds : 0.64 ≤ ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2) ∧
    ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2) ≤ 0.64032 := by
  have hG : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2)) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ => (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2)).intervalIntegrable
      _ _
  have hlo : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ 6 * (T4 (u ^ 2) - (u ^ 2) ^ 5 / 100))
      volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold T4
    fun_prop
  have hhi : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ 6 * (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100))
      volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold T4
    fun_prop
  have h6 : ∀ u : ℝ, 0 ≤ (1 - u ^ 2) ^ 6 := fun u => by positivity
  constructor
  · have h := intervalIntegral.integral_mono_on (by norm_num) hlo hG fun u hu =>
      mul_le_mul_of_nonneg_left (exp_sq_taylor hu).1 (h6 u)
    rw [int_Plo] at h
    have hn : (0.64 : ℝ) ≤ 3213568256 / 5019589575 := by norm_num
    linarith
  · have h := intervalIntegral.integral_mono_on (by norm_num) hG hhi fun u hu =>
      mul_le_mul_of_nonneg_left (exp_sq_taylor hu).2 (h6 u)
    rw [int_Phi] at h
    have hn : (3213595904 : ℝ) / 5019589575 ≤ 0.64032 := by norm_num
    linarith

/-- **`|η∘|₂ ≥ 0.8`** (truth `0.8001287`). -/
theorem l2_circ_lo : 0.8 ≤ MajSp.l2 HW.etaCirc := by
  have h := G6_bounds.1
  have e : (0.8 : ℝ) ^ 2 = 0.64 := by norm_num
  unfold MajSp.l2
  rw [circ_sq_int, Real.le_sqrt (by norm_num) (by linarith), e]
  exact h

/-- **`|η∘|₂ ≤ 0.8002`** (truth `0.8001287`). -/
theorem l2_circ_hi : MajSp.l2 HW.etaCirc ≤ 0.8002 := by
  have h := G6_bounds.2
  have e : (0.8002 : ℝ) ^ 2 = 0.64032004 := by norm_num
  unfold MajSp.l2
  rw [circ_sq_int, Real.sqrt_le_left (by norm_num), e]
  linarith

/-! ## `η∘'` -/

/-- **`η∘'`, everywhere**: `h'(t)·t·e^{−t²/2} + h(t)(1 − t²)e^{−t²/2}` (`h` is `C¹`). -/
noncomputable def dCirc (t : ℝ) : ℝ :=
  BL.hD t * t * Real.exp (-t ^ 2 / 2) + HW.hFun t * ((1 - t ^ 2) * Real.exp (-t ^ 2 / 2))

/-- `d/dt t² = 2t`. -/
theorem hasDerivAt_sq' (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
  simpa using hasDerivAt_pow 2 t

/-- **`η∘' = dCirc`**, from `BL.hasDerivAt_hFun`. -/
theorem hasDerivAt_etaCirc (t : ℝ) : HasDerivAt HW.etaCirc (dCirc t) t := by
  have he := ((hasDerivAt_sq' t).neg.div_const 2).exp
  have h := ((BL.hasDerivAt_hFun t).mul (hasDerivAt_id' t)).mul he
  refine h.congr_deriv ?_
  unfold dCirc
  simp only [Pi.mul_apply, Pi.neg_apply]
  ring

/-- `deriv η∘ = dCirc`. -/
theorem deriv_etaCirc : deriv HW.etaCirc = dCirc :=
  funext fun t => (hasDerivAt_etaCirc t).deriv

/-- **`η∘'(t) = −u(1−u²)²(7−u²)e^{−u²/2}`, `u = t − 1`, on `[0, 2]`.** -/
theorem dCirc_eq {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    dCirc t = -((t - 1) * (1 - (t - 1) ^ 2) ^ 2 * (7 - (t - 1) ^ 2)) *
      Real.exp (-(t - 1) ^ 2 / 2) := by
  have hE : Real.exp (-(t - 1) ^ 2 / 2) = Real.exp (t - 1 / 2) * Real.exp (-t ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold dCirc
  rw [BL.hD_eq h0 h2, BL.hFun_eq_hP h0 h2, hE]
  unfold BL.hDP BL.hP
  ring

/-- `η∘'` vanishes on `(2, ∞)`. -/
theorem dCirc_of_two_lt {t : ℝ} (ht : 2 < t) : dCirc t = 0 := by
  have hd : BL.hD t = 0 := if_neg fun h => absurd h.2 (not_le.mpr ht)
  rw [dCirc, hd, HW.hFun_of_two_le ht.le]
  ring

/-- `η∘'(t)² = u²(1−u²)⁴(7−u²)²e^{−u²}`, `u = t − 1`, on `[0, 2]`. -/
theorem dCirc_sq_eq {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    dCirc t ^ 2 = (t - 1) ^ 2 * (1 - (t - 1) ^ 2) ^ 4 * (7 - (t - 1) ^ 2) ^ 2 *
      Real.exp (-(t - 1) ^ 2) := by
  have he : Real.exp (-(t - 1) ^ 2 / 2) ^ 2 = Real.exp (-(t - 1) ^ 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [dCirc_eq h0 h2]
  calc (-((t - 1) * (1 - (t - 1) ^ 2) ^ 2 * (7 - (t - 1) ^ 2)) *
        Real.exp (-(t - 1) ^ 2 / 2)) ^ 2
      = (t - 1) ^ 2 * (1 - (t - 1) ^ 2) ^ 4 * (7 - (t - 1) ^ 2) ^ 2 *
          Real.exp (-(t - 1) ^ 2 / 2) ^ 2 := by ring
    _ = (t - 1) ^ 2 * (1 - (t - 1) ^ 2) ^ 4 * (7 - (t - 1) ^ 2) ^ 2 *
          Real.exp (-(t - 1) ^ 2) := by rw [he]

/-- **`|η∘'|₂² = ∫₋₁¹ u²(1−u²)⁴(7−u²)²e^{−u²} du`.** -/
theorem deriv_sq_int : ∫ t in Ioi (0 : ℝ), deriv HW.etaCirc t ^ 2 =
    ∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 * Real.exp (-u ^ 2) := by
  rw [deriv_etaCirc, setInt_Ioi_02 _ fun t ht => by rw [dCirc_of_two_lt ht]; ring]
  have hc : EqOn (fun t => dCirc t ^ 2) (fun t => (t - 1) ^ 2 * (1 - (t - 1) ^ 2) ^ 4 *
      (7 - (t - 1) ^ 2) ^ 2 * Real.exp (-(t - 1) ^ 2)) (uIcc 0 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact dCirc_sq_eq ht.1 ht.2
  rw [intervalIntegral.integral_congr hc]
  calc ∫ t in (0 : ℝ)..2, (t - 1) ^ 2 * (1 - (t - 1) ^ 2) ^ 4 * (7 - (t - 1) ^ 2) ^ 2 *
        Real.exp (-(t - 1) ^ 2)
      = ∫ u in (0 - 1 : ℝ)..(2 - 1), u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 *
          Real.exp (-u ^ 2) :=
        intervalIntegral.integral_comp_sub_right
          (fun u => u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 * Real.exp (-u ^ 2)) 1
    _ = ∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 * Real.exp (-u ^ 2) := by
        norm_num

/-- `∫₋₁¹ u²(1−u²)⁴(7−u²)²(T₄(u²) + u¹⁰/100) = 343585016704/125489739375 = 2.7379531`. -/
theorem int_Dhi : ∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 *
    (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100) = 343585016704 / 125489739375 := by
  have h : EqOn (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 *
      (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100))
      (fun u => ∑ k : Fin 25, (![0, 0, 49, 0, -259, 0, 1171/2, 0, -4489/6, 0, 14581/24, 0,
        -8444/25, 0, 16123/120, 0, -11047/300, 0, 1057/200, 0, 29/150, 0, -83/600, 0, 1/100] :
          Fin 25 → ℝ) k * u ^ (k : ℕ)) (uIcc (-1) 1) := by
    intro u _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, T4]
    ring
  rw [intervalIntegral.integral_congr h, int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- **`|η∘'|₂² ≤ 3`** (truth `2.7375293`; the bound is `2.7379531`). -/
theorem l2_deriv_sq_le : MajSp.l2 (deriv HW.etaCirc) ^ 2 ≤ 3 := by
  have hD : IntervalIntegrable (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 *
      Real.exp (-u ^ 2)) volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have hhi : IntervalIntegrable (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ 4 * (7 - u ^ 2) ^ 2 *
      (T4 (u ^ 2) + (u ^ 2) ^ 5 / 100)) volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold T4
    fun_prop
  have h := intervalIntegral.integral_mono_on (by norm_num) hD hhi fun u hu =>
    mul_le_mul_of_nonneg_left (exp_sq_taylor hu).2 (by positivity)
  rw [int_Dhi] at h
  unfold MajSp.l2
  rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), deriv_sq_int]
  have hn : (343585016704 : ℝ) / 125489739375 ≤ 3 := by norm_num
  linarith

/-! ## `|η₊|₁ ≤ 1.2`, from `BL.band_uniform` -/

/-- `∫₋₁¹ (1−u²)³ du = 32/35`. -/
theorem int_C3 : ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 3 = 32 / 35 := by
  have h : EqOn (fun u : ℝ => (1 - u ^ 2) ^ 3)
      (fun u => ∑ k : Fin 7, (![1, 0, -3, 0, 3, 0, -1] : Fin 7 → ℝ) k * u ^ (k : ℕ))
      (uIcc (-1) 1) := by
    intro u _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ]
    ring
  rw [intervalIntegral.integral_congr h, int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- **`|η∘|₁ ≤ 32/35`** (from `e^{−(t−1)²/2} ≤ 1`). -/
theorem l1_circ_le : ∫ t in Ioi (0 : ℝ), |HW.etaCirc t| ≤ 32 / 35 := by
  rw [setInt_Ioi_02 _ fun t ht => by rw [etaCirc_of_two_lt ht, abs_zero]]
  have hA : IntervalIntegrable (fun t => |HW.etaCirc t|) volume 0 2 :=
    continuous_etaCirc.abs.intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t : ℝ => (1 - (t - 1) ^ 2) ^ 3) volume 0 2 :=
    (by fun_prop : Continuous fun t : ℝ => (1 - (t - 1) ^ 2) ^ 3).intervalIntegrable _ _
  have hpt : ∀ t ∈ Icc (0 : ℝ) 2, |HW.etaCirc t| ≤ (1 - (t - 1) ^ 2) ^ 3 := by
    intro t ht
    rw [HW.etaCirc_eq ht.1 ht.2]
    have h20 : 0 ≤ 2 - t := by linarith [ht.2]
    have hp0 : 0 ≤ t ^ 3 * (2 - t) ^ 3 := mul_nonneg (pow_nonneg ht.1 3) (pow_nonneg h20 3)
    have he : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t - 1)])
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.exp_pos _).le)]
    calc t ^ 3 * (2 - t) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) ≤ t ^ 3 * (2 - t) ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left he hp0
      _ = (1 - (t - 1) ^ 2) ^ 3 := by ring
  have h := intervalIntegral.integral_mono_on (by norm_num) hA hB hpt
  have hsub : ∫ t in (0 : ℝ)..2, (1 - (t - 1) ^ 2) ^ 3 = 32 / 35 :=
    calc ∫ t in (0 : ℝ)..2, (1 - (t - 1) ^ 2) ^ 3
        = ∫ u in (0 - 1 : ℝ)..(2 - 1), (1 - u ^ 2) ^ 3 :=
          intervalIntegral.integral_comp_sub_right (fun u => (1 - u ^ 2) ^ 3) 1
      _ = ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 3 := by norm_num
      _ = 32 / 35 := int_C3
  linarith

/-- **`|η₊|₁ ≤ 1.2`**, from `BL.band_uniform`: `|η₊| ≤ |η∘| + 0.13·te^{−t²/2}`, so
`|η₊|₁ ≤ 32/35 + 0.13 = 1.0443`. -/
theorem l1_etaPlus_le : MajSp.l1 HW.etaPlus ≤ 1.2 := by
  have hA : Integrable (fun t => |HW.etaCirc t|) (volume.restrict (Ioi 0)) :=
    integrableOn_of_cont _ continuous_etaCirc.abs fun t ht => by
      rw [etaCirc_of_two_lt ht, abs_zero]
  have hg : Integrable (fun t => |HW.etaCirc t| + 0.13 * (t * Real.exp (-t ^ 2 / 2)))
      (volume.restrict (Ioi 0)) := hA.add (integrable_t_exp.const_mul 0.13)
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      |HW.etaPlus t| ≤ |HW.etaCirc t| + 0.13 * (t * Real.exp (-t ^ 2 / 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t * Real.exp (-t ^ 2 / 2) := mul_nonneg (le_of_lt ht) (Real.exp_pos _).le
    have hsplit : HW.etaPlus t =
        HW.etaCirc t + (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)) := by
      rw [HW.etaPlus, HW.etaCirc]
      ring
    have hb := HW.band_all BL.band_uniform t
    rw [hsplit]
    calc |HW.etaCirc t + (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))|
        ≤ |HW.etaCirc t| + |HW.hH 200 t - HW.hFun t| * (t * Real.exp (-t ^ 2 / 2)) := by
          rw [← abs_of_nonneg ht0, ← abs_mul, abs_of_nonneg ht0]
          exact abs_add_le _ _
      _ ≤ |HW.etaCirc t| + 0.13 * (t * Real.exp (-t ^ 2 / 2)) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hb ht0) _
  have h := integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg (HW.etaPlus t)) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add hA (integrable_t_exp.const_mul 0.13), integral_const_mul, int_t_exp] at h
  have hc := l1_circ_le
  unfold MajSp.l1
  linarith

/-! ## `BandSharp`: the one analytic obligation behind the band-limiting conjuncts -/

/-- **THE NAMED OBLIGATION**: the band-limiting error of `h₂₀₀` is uniformly below `4.5·10⁻⁵`.
True sup `1.138·10⁻⁵` (at `t ≈ 2.0004`); `BL.band_uniform` proves `0.1185` by one integration by
parts. OPEN. -/
def BandSharp : Prop := ∀ t : ℝ, 0 < t → |HW.hH 200 t - HW.hFun t| ≤ 4.5e-5

/-- `BandSharp` is STRONGER than the proved `HW.BandUniform` (`0.13`). -/
theorem bandSharp_uniform (hb : BandSharp) : HW.BandUniform :=
  fun t ht => (hb t ht).trans (by norm_num)

/-- **For ANY `g` with `|g − h| ≤ c` on `t > 0`**: `|g·t·e^{−t²/2} − η∘|₂ ≤ 0.6666·c`, since
`|g·t·e^{−t²/2} − η∘|₂² ≤ c²∫₀^∞t²e^{−t²} = c²√π/4 ≤ 0.6666²c²`. -/
theorem l2_diff_of_unif (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ t : ℝ, 0 < t → |g t - HW.hFun t| ≤ c) :
    MajSp.l2 (fun t => g t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t) ≤ 0.6666 * c := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (g t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t) ^ 2 ≤
      c ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    intro t ht
    have e1 : g t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t =
        (g t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)) := by
      unfold HW.etaCirc
      ring
    have e2 : (t * Real.exp (-t ^ 2 / 2)) ^ 2 = t ^ 2 * Real.exp (-t ^ 2) := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have h1 : (g t - HW.hFun t) ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hg t ht) 2
    rw [e1, mul_pow, e2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _)
    (integrable_t2_exp.const_mul (c ^ 2)) (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_const_mul, int_t2_exp] at hI
  have hq := sqrt_pi_quarter_le
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have h3 : c ^ 2 * (Real.sqrt Real.pi / 4) ≤ c ^ 2 * 0.44314 := mul_le_mul_of_nonneg_left hq hc2
  unfold MajSp.l2
  rw [Real.sqrt_le_left (mul_nonneg (by norm_num) hc)]
  nlinarith

/-- `l2_diff_of_unif`'s hypothesis discharged once, by a real function: `g = h`, `c = 0`. -/
theorem l2_diff_self :
    MajSp.l2 (fun t => HW.hFun t * t * Real.exp (-t ^ 2 / 2) - HW.etaCirc t) ≤ 0.6666 * 0 :=
  l2_diff_of_unif HW.hFun 0 le_rfl fun t _ => by simp

/-- **For ANY `g` with `|g − h| ≤ c ≤ 0.001` on `t > 0`**: `|g·t·e^{−t²/2}|₂ ≤ 0.81`, since
`(g·t·e^{−t²/2})² ≤ η∘² + 2c·te^{−t²/2} + c²t²e^{−t²}` (`|η∘| ≤ 1`), whose integral is at most
`0.64032 + 0.002 + 4.5·10⁻⁷ ≤ 0.81²`. -/
theorem l2_plus_of_unif (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 0.001)
    (hg : ∀ t : ℝ, 0 < t → |g t - HW.hFun t| ≤ c) :
    MajSp.l2 (fun t => g t * t * Real.exp (-t ^ 2 / 2)) ≤ 0.81 := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (g t * t * Real.exp (-t ^ 2 / 2)) ^ 2 ≤
      HW.etaCirc t ^ 2 + 2 * c * (t * Real.exp (-t ^ 2 / 2)) +
        c ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    intro t ht
    set a := HW.etaCirc t with ha_def
    set w := t * Real.exp (-t ^ 2 / 2) with hw_def
    set d := g t - HW.hFun t with hd_def
    have hw0 : 0 ≤ w := mul_nonneg (le_of_lt ht) (Real.exp_pos _).le
    have e1 : g t * t * Real.exp (-t ^ 2 / 2) = a + d * w := by
      rw [ha_def, hd_def, hw_def]
      unfold HW.etaCirc
      ring
    have e2 : w ^ 2 = t ^ 2 * Real.exp (-t ^ 2) := by
      rw [hw_def, mul_pow, sq (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have ha1 : |a| ≤ 1 := HW.etaCirc_le t
    have hd1 : |d| ≤ c := hg t ht
    have hab : 2 * a * (d * w) ≤ 2 * c * w := by
      have h1 : |a * d| ≤ c := by
        rw [abs_mul]
        calc |a| * |d| ≤ 1 * c := mul_le_mul ha1 hd1 (abs_nonneg _) zero_le_one
          _ = c := one_mul c
      have h2 : a * d ≤ c := (le_abs_self _).trans h1
      nlinarith [mul_le_mul_of_nonneg_right h2 hw0]
    have hdd : (d * w) ^ 2 ≤ c ^ 2 * w ^ 2 := by
      rw [mul_pow]
      have : d ^ 2 ≤ c ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg w)
    rw [e1, ← e2]
    nlinarith [hab, hdd]
  have hA : Integrable (fun t => HW.etaCirc t ^ 2) (volume.restrict (Ioi 0)) :=
    integrableOn_of_cont _ (continuous_etaCirc.pow 2) fun t ht => by
      rw [etaCirc_of_two_lt ht]
      ring
  have hB := integrable_t_exp.const_mul (2 * c)
  have hC := integrable_t2_exp.const_mul (c ^ 2)
  have hAB : Integrable (fun t => HW.etaCirc t ^ 2 + 2 * c * (t * Real.exp (-t ^ 2 / 2)))
      (volume.restrict (Ioi 0)) := hA.add hB
  have hg : Integrable (fun t => HW.etaCirc t ^ 2 + 2 * c * (t * Real.exp (-t ^ 2 / 2)) +
      c ^ 2 * (t ^ 2 * Real.exp (-t ^ 2))) (volume.restrict (Ioi 0)) := hAB.add hC
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul,
    int_t_exp, int_t2_exp, circ_sq_int] at hI
  have hG := G6_bounds.2
  have hq := sqrt_pi_quarter_le
  have hc2 : c ^ 2 ≤ 0.000001 := by nlinarith
  have h3 : c ^ 2 * (Real.sqrt Real.pi / 4) ≤ 0.000001 * 0.44314 :=
    mul_le_mul hc2 hq (by positivity) (by norm_num)
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith

/-- `l2_plus_of_unif`'s hypothesis discharged once, by a real function: `g = h`, `c = 0`. -/
theorem l2_plus_self : MajSp.l2 (fun t => HW.hFun t * t * Real.exp (-t ^ 2 / 2)) ≤ 0.81 :=
  l2_plus_of_unif HW.hFun 0 le_rfl (by norm_num) fun t _ => by simp

/-- **`BandSharp → |η₊ − η∘|₂ ≤ 3·10⁻⁵`** (`0.6666·4.5·10⁻⁵ = 2.9997·10⁻⁵`). -/
theorem l2_diff_band (hb : BandSharp) :
    MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) ≤ 3e-5 :=
  le_trans (l2_diff_of_unif (HW.hH 200) 4.5e-5 (by norm_num) hb) (by norm_num)

/-- **`BandSharp → |η₊|₂ ≤ 0.81`.** -/
theorem l2_plus_band (hb : BandSharp) : MajSp.l2 HW.etaPlus ≤ 0.81 :=
  l2_plus_of_unif (HW.hH 200) 4.5e-5 (by norm_num) (by norm_num) hb

end Principia.Common.TernaryGoldbach.EN
