/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EasyStar
import Principia.Common.TernaryGoldbach.EasyNorms
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-!
# `CLower` and `CLowerE` PROVED on Helfgott's weights: a second-order bound on `η∘ ∗ η∘`

`MajSp.CLower HW.etaCirc HW.etaStar` (`eq:barbar`, Helfgott's constant `0.000834`) and
`EN.CLowerE HW.etaCirc HW.etaStar` (the loosened `0.000914`, `|η∘'|₂² ≤ 3`) are THEOREMS here
(`clower_helf`, `clowerE_helf`), axiom-clean. Helfgott's `lem:gosor` (factor `2.71`) is not used.

## The route (each step checked numerically first, `scratchpad/ct_check.py`)

`C(y) = MajSp.ccon η∘ η* y = ∫∫_{t₁,t₂>0} η∘(t₁)η∘(t₂)η*(y − t₁ − t₂)`, `y = N/x = 2 + a`,
`a = 9/(196√(2π))` (`y_helf`).

1. **Fubini** (`ccon_eq`): `C(y) = ∫ F(y − v)η*(v) dv`, `F = η∘ ∗ η∘` (`selfConv`), after the
   substitution `t₂ = y − t₁ − v` and one swap (`integrable_kernel`: `|η∘| ≤ 1`, `η* ∈ L¹`).
2. **Symmetry** (`circ_symm`: `η∘(2 − t) = η∘(t)`) turns `F(2 + s)` into the autocorrelation
   `∫ η∘(t)η∘(t − s)`, hence `F(2 + s) = |η∘|₂² − ½∫(η∘(t) − η∘(t − s))²` (`conv_two_add`).
3. **The segment bound** (`circ_diff_sq_le`): `∫(η∘(t) − η∘(t − s))² ≤ s²·|η∘'|₂²`, from
   `η∘(t) − η∘(t − s) = ∫₀¹ s·η∘'(t − s + θs) dθ` (`circ_sub_eq`), `(∫₀¹ f)² ≤ ∫₀¹ f²`
   (`sq_integral_le`) and one Fubini swap on a compact box. No second derivative is needed, so
   `η∘ ∈ C¹` (`EN.hasDerivAt_etaCirc`) suffices. Hence `F(u) ≥ |η∘|₂² − (D/2)(u − 2)²` for EVERY
   real `u` (`conv_ge`), `D = |η∘'|₂²` — no tail term: the bound is used on all of `v ≥ 0`.
4. **Moments of `η*`** (`quad_star`): `∫η* = √(π/2)/49` (`EN.int_etaStar`),
   `∫vη* = (9/16)·2/49²`, `∫v²η* = (49/144)·B₂/49³`, by Fubini on the Mellin convolution
   (`mconv_mom`: `∫ sᵏ(η₂ ∗_M φ) = (∫ rᵏη₂)(∫ yᵏφ)`), `∫ rη₂ = 9/16`, `∫ r²η₂ = 49/144`
   (`A1_eq`, `A2_eq`, fundamental theorem of calculus on `[1/4,1/2]`, `[1/2,1]`), `∫ yφ = 2`,
   `B₂ = ∫ y²φ = (3/2)√2√π = 3√(π/2)` (`B1_eq`, `B2_eq`, `EN.gauss_moment`).
5. **Arithmetic** (`close_gen`): since `a` is the mean of `η*` (`a·√(π/2) = 9/392`), the
   quadratic moment is `m₂ − 9a/19208 ≤ m₂ ≤ (49/144)·3.77/49³`, so the loss is at most
   `(D/2)·(49/144)·3.77/49³`: `1.4925e-5` at `D = 2.7375293` against `0.000834/49 = 1.7020e-5`,
   `1.6356e-5` at `D = 3` against `0.000914/49 = 1.8653e-5`.

Both targets are stated with Helfgott's `|η∘'|₂²` bound as their OWN antecedent (`MajSp.CLower`
takes `l2 (deriv η∘)² ≤ 2.7375293`, `EN.CLowerE` takes `≤ 3`); the proofs use exactly that
antecedent as `D` (`l2_dcirc_sq` identifies it with `∫ η∘'²` over `ℝ`). The exact value of the
lower bound is `ccon_lower`; the true constant is `0.80222559/49`, the bound here `0.80222553/49`.
-/

namespace Principia.Common.TernaryGoldbach.CT

open MeasureTheory Set Filter
open Principia.Erdos1054 (helfgottX)

/-! ## `η∘`, `η∘'`: support, symmetry, continuity -/

/-- `η∘` vanishes on `(−∞, 0]`. -/
theorem circ_of_nonpos {t : ℝ} (ht : t ≤ 0) : HW.etaCirc t = 0 := by
  rw [HW.etaCirc, HW.hFun_of_nonpos ht]
  ring

/-- `η∘` vanishes outside `[0, 2]`. -/
theorem circ_of_not_mem {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 2) : HW.etaCirc t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · exact circ_of_nonpos h.le
  · exact EN.etaCirc_of_two_lt h

/-- **`η∘(2 − t) = η∘(t)`**: `t³(2−t)³e^{−(t−1)²/2}` is symmetric about `1`. -/
theorem circ_symm (t : ℝ) : HW.etaCirc (2 - t) = HW.etaCirc t := by
  by_cases h : t ∈ Icc (0 : ℝ) 2
  · obtain ⟨h0, h2⟩ := h
    rw [HW.etaCirc_eq (by linarith) (by linarith), HW.etaCirc_eq h0 h2,
      show -(2 - t - 1) ^ 2 / 2 = -(t - 1) ^ 2 / 2 by ring, show 2 - (2 - t) = t by ring]
    ring
  · have h' : 2 - t ∉ Icc (0 : ℝ) 2 := fun h1 => h ⟨by linarith [h1.2], by linarith [h1.1]⟩
    rw [circ_of_not_mem h, circ_of_not_mem h']

/-- `η∘'` vanishes on `(−∞, 0)`. -/
theorem dCirc_of_neg {t : ℝ} (ht : t < 0) : EN.dCirc t = 0 := by
  have hd : BL.hD t = 0 := if_neg fun h => absurd h.1 (not_le.mpr ht)
  rw [EN.dCirc, hd, HW.hFun_of_nonpos ht.le]
  ring

/-- `η∘'` vanishes on `(−∞, 0]`. -/
theorem dCirc_of_nonpos {t : ℝ} (ht : t ≤ 0) : EN.dCirc t = 0 := by
  rcases ht.lt_or_eq with h | h
  · exact dCirc_of_neg h
  · rw [h, EN.dCirc, HW.hFun_of_nonpos le_rfl]
    ring

/-- `η∘'` vanishes outside `[0, 2]`. -/
theorem dCirc_of_not_mem {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 2) : EN.dCirc t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · exact dCirc_of_neg h
  · exact EN.dCirc_of_two_lt h

/-- `η∘'` is continuous (`h ∈ C¹`, `BL.continuous_hD`). -/
theorem continuous_dCirc : Continuous EN.dCirc :=
  ((BL.continuous_hD.mul continuous_id).mul (by fun_prop)).add
    (BL.continuous_hFun.mul (by fun_prop))

/-- `η∘` has compact support. -/
theorem hcs_circ : HasCompactSupport HW.etaCirc :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => circ_of_not_mem ht

/-- `η∘'` has compact support. -/
theorem hcs_dCirc : HasCompactSupport EN.dCirc :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => dCirc_of_not_mem ht

/-- `η∘ ∈ L¹(ℝ)`. -/
theorem integrable_circ : Integrable HW.etaCirc :=
  EN.continuous_etaCirc.integrable_of_hasCompactSupport hcs_circ

/-- `η∘·g ∈ L¹(ℝ)` for continuous `g`. -/
theorem integrable_circ_mul {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => HW.etaCirc t * g t) :=
  (EN.continuous_etaCirc.mul hg).integrable_of_hasCompactSupport hcs_circ.mul_right

/-- `η∘² ∈ L¹(ℝ)`. -/
theorem integrable_circ_sq : Integrable fun t => HW.etaCirc t ^ 2 :=
  (integrable_circ_mul EN.continuous_etaCirc).congr (ae_of_all _ fun _ => (sq _).symm)

/-! ## The segment bound `∫ (η∘(t) − η∘(t − s))² ≤ s²·|η∘'|₂²` -/

/-- `θ ↦ η∘'(t − s + θs)` is continuous. -/
theorem cont_seg (t s : ℝ) : Continuous fun θ : ℝ => EN.dCirc (t - s + θ * s) :=
  continuous_dCirc.comp (by fun_prop : Continuous fun θ : ℝ => t - s + θ * s)

/-- **FTC along the segment**: `η∘(t) − η∘(t − s) = ∫₀¹ s·η∘'(t − s + θs) dθ`. -/
theorem circ_sub_eq (t s : ℝ) :
    HW.etaCirc t - HW.etaCirc (t - s) = ∫ θ in (0 : ℝ)..1, s * EN.dCirc (t - s + θ * s) := by
  have hd : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun θ => HW.etaCirc (t - s + θ * s))
      (s * EN.dCirc (t - s + θ * s)) θ := by
    intro θ _
    have hl : HasDerivAt (fun x : ℝ => t - s + x * s) s θ :=
      (hasDerivAt_mul_const s).const_add (t - s)
    have h := (EN.hasDerivAt_etaCirc (t - s + θ * s)).comp θ hl
    rw [mul_comm] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul (cont_seg t s)).intervalIntegrable _ _)]
  simp

/-- **`(∫₀¹ f)² ≤ ∫₀¹ f²`** for continuous `f` (from `f² ≥ 2mf − m²`, `m = ∫₀¹ f`). -/
theorem sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ θ in (0 : ℝ)..1, f θ) ^ 2 ≤ ∫ θ in (0 : ℝ)..1, f θ ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ θ in (0 : ℝ)..1, f θ := ⟨_, rfl⟩
  have hfi : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume 0 1 := intervalIntegrable_const
  have h1 : IntervalIntegrable (fun θ => 2 * m * f θ - m ^ 2) volume 0 1 :=
    (hfi.const_mul (2 * m)).sub hc
  have hle := intervalIntegral.integral_mono_on zero_le_one h1
    ((hf.pow 2).intervalIntegrable 0 1) fun θ _ => by nlinarith [sq_nonneg (f θ - m)]
  rw [intervalIntegral.integral_sub (hfi.const_mul (2 * m)) hc,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    ← hm] at hle
  rw [← hm]
  nlinarith [hle]

/-- Pointwise: `(η∘(t) − η∘(t − s))² ≤ ∫₀¹ s²·η∘'(t − s + θs)² dθ`. -/
theorem circ_sub_sq_le (t s : ℝ) :
    (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2 ≤
      ∫ θ in (0 : ℝ)..1, s ^ 2 * EN.dCirc (t - s + θ * s) ^ 2 := by
  rw [circ_sub_eq]
  refine le_of_le_of_eq (sq_integral_le (f := fun θ => s * EN.dCirc (t - s + θ * s))
    (continuous_const.mul (cont_seg t s))) ?_
  exact intervalIntegral.integral_congr fun θ _ => mul_pow s _ 2

/-- **The segment bound**: `∫ (η∘(t) − η∘(t − s))² dt ≤ s²·∫ η∘'²`, for every real `s`. The
`(t, θ)`-integrand lives on the box `[−|s|, 2 + |s|] × (0, 1]`, where it is bounded, so the swap
is on a finite measure. -/
theorem circ_diff_sq_le (s : ℝ) :
    ∫ t, (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2 ≤ s ^ 2 * ∫ t, EN.dCirc t ^ 2 := by
  obtain ⟨M, hM⟩ := continuous_dCirc.bounded_above_of_compact_support hcs_dCirc
  have hs1 := le_abs_self s
  have hs2 := neg_abs_le s
  have hL : ∀ t ∉ Icc (-|s|) (2 + |s|), (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2 = 0 := by
    intro t ht
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    have ha : t ∉ Icc (0 : ℝ) 2 := by
      rw [mem_Icc, not_and_or, not_le, not_le]
      rcases ht with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hb : t - s ∉ Icc (0 : ℝ) 2 := by
      rw [mem_Icc, not_and_or, not_le, not_le]
      rcases ht with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    simp [circ_of_not_mem ha, circ_of_not_mem hb]
  have hG : ∀ θ ∈ Ioc (0 : ℝ) 1, ∀ t ∉ Icc (-|s|) (2 + |s|),
      s ^ 2 * EN.dCirc (t - s + θ * s) ^ 2 = 0 := by
    intro θ hθ t ht
    obtain ⟨hθ0, hθ1⟩ := hθ
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    have e1 : -s + θ * s ≤ |s| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (by linarith : (0 : ℝ) ≤ |s| + s),
        mul_nonneg hθ0.le (abs_nonneg s)]
    have e2 : s - θ * s ≤ |s| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (by linarith : (0 : ℝ) ≤ |s| - s),
        mul_nonneg hθ0.le (abs_nonneg s)]
    have hr : t - s + θ * s ∉ Icc (0 : ℝ) 2 := by
      rw [mem_Icc, not_and_or, not_le, not_le]
      rcases ht with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rw [dCirc_of_not_mem hr]
    ring
  have hcont : Continuous fun p : ℝ × ℝ => s ^ 2 * EN.dCirc (p.1 - s + p.2 * s) ^ 2 :=
    continuous_const.mul ((continuous_dCirc.comp
      (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 - s + p.2 * s)).pow 2)
  have hint : Integrable (Function.uncurry fun t θ : ℝ => s ^ 2 * EN.dCirc (t - s + θ * s) ^ 2)
      ((volume.restrict (Icc (-|s|) (2 + |s|))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine ⟨hcont.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := s ^ 2 * M ^ 2)
      (ae_of_all _ fun p => ?_)⟩
    have h1 := hM (p.1 - s + p.2 * s)
    rw [Real.norm_eq_abs] at h1
    change ‖s ^ 2 * EN.dCirc (p.1 - s + p.2 * s) ^ 2‖ ≤ s ^ 2 * M ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : EN.dCirc (p.1 - s + p.2 * s) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
  have hLi : Integrable (fun t => (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2)
      (volume.restrict (Icc (-|s|) (2 + |s|))) :=
    ((EN.continuous_etaCirc.sub (EN.continuous_etaCirc.comp
      (continuous_sub_right s))).pow 2).integrableOn_Icc
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hL]
  calc ∫ t in Icc (-|s|) (2 + |s|), (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2
      ≤ ∫ t in Icc (-|s|) (2 + |s|), ∫ θ in Ioc (0 : ℝ) 1,
          s ^ 2 * EN.dCirc (t - s + θ * s) ^ 2 :=
        integral_mono hLi hint.integral_prod_left fun t => by
          have h := circ_sub_sq_le t s
          rwa [intervalIntegral.integral_of_le zero_le_one] at h
    _ = ∫ θ in Ioc (0 : ℝ) 1, ∫ t in Icc (-|s|) (2 + |s|),
          s ^ 2 * EN.dCirc (t - s + θ * s) ^ 2 :=
        integral_integral_swap hint
    _ = ∫ θ in Ioc (0 : ℝ) 1, s ^ 2 * ∫ t, EN.dCirc t ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hG θ hθ), integral_const_mul]
        have e : ∫ t, EN.dCirc (t - s + θ * s) ^ 2 = ∫ t, EN.dCirc (t + (θ * s - s)) ^ 2 :=
          integral_congr_ae (ae_of_all _ fun t => by
            change EN.dCirc (t - s + θ * s) ^ 2 = EN.dCirc (t + (θ * s - s)) ^ 2
            rw [show t - s + θ * s = t + (θ * s - s) by ring])
        rw [e, integral_add_right_eq_self (fun t => EN.dCirc t ^ 2) (θ * s - s)]
    _ = s ^ 2 * ∫ t, EN.dCirc t ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le zero_le_one]
        simp

/-! ## The self-convolution `F = η∘ ∗ η∘` and its second-order lower bound -/

/-- **The self-convolution** `F(u) = (η∘ ∗ η∘)(u) = ∫ η∘(t)η∘(u − t) dt` (over `ℝ`). -/
noncomputable def selfConv (u : ℝ) : ℝ := ∫ t, HW.etaCirc t * HW.etaCirc (u - t)

/-- **`F(2 + s) = |η∘|₂² − ½∫(η∘(t) − η∘(t − s))²`**: symmetry makes `F(2 + s)` the
autocorrelation `∫ η∘(t)η∘(t − s)`; expand the square, `∫ η∘(t − s)² = ∫ η∘²`. -/
theorem conv_two_add (s : ℝ) :
    selfConv (2 + s) = (∫ t, HW.etaCirc t ^ 2) -
      (∫ t, (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2) / 2 := by
  have h1 := integrable_circ_sq
  have h2 : Integrable fun t => HW.etaCirc t * HW.etaCirc (t - s) :=
    integrable_circ_mul (EN.continuous_etaCirc.comp (continuous_sub_right s))
  have h3 : Integrable fun t => HW.etaCirc (t - s) ^ 2 := h1.comp_sub_right s
  have h2' : Integrable fun t => 2 * (HW.etaCirc t * HW.etaCirc (t - s)) := h2.const_mul 2
  have h12 : Integrable fun t =>
      HW.etaCirc t ^ 2 - 2 * (HW.etaCirc t * HW.etaCirc (t - s)) := h1.sub h2'
  have hF : selfConv (2 + s) = ∫ t, HW.etaCirc t * HW.etaCirc (t - s) :=
    integral_congr_ae (ae_of_all _ fun t => by
      change HW.etaCirc t * HW.etaCirc (2 + s - t) = HW.etaCirc t * HW.etaCirc (t - s)
      rw [show 2 + s - t = 2 - (t - s) by ring, circ_symm])
  have e : (fun t => (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2) = fun t =>
      HW.etaCirc t ^ 2 - 2 * (HW.etaCirc t * HW.etaCirc (t - s)) + HW.etaCirc (t - s) ^ 2 := by
    funext t
    ring
  have hE : ∫ t, (HW.etaCirc t - HW.etaCirc (t - s)) ^ 2 =
      (∫ t, HW.etaCirc t ^ 2) - 2 * (∫ t, HW.etaCirc t * HW.etaCirc (t - s)) +
        ∫ t, HW.etaCirc (t - s) ^ 2 := by
    rw [e, integral_add h12 h3, integral_sub h1 h2', integral_const_mul]
  have hT : ∫ t, HW.etaCirc (t - s) ^ 2 = ∫ t, HW.etaCirc t ^ 2 :=
    integral_sub_right_eq_self (fun t => HW.etaCirc t ^ 2) s
  rw [hF, hE, hT]
  ring

/-- **`F(u) ≥ |η∘|₂² − (D/2)(u − 2)²` for EVERY real `u`**, `D = ∫ η∘'²`. -/
theorem conv_ge (u : ℝ) :
    (∫ t, HW.etaCirc t ^ 2) - (∫ t, EN.dCirc t ^ 2) / 2 * (u - 2) ^ 2 ≤ selfConv u := by
  have h := conv_two_add (u - 2)
  rw [show 2 + (u - 2) = u by ring] at h
  have hd := circ_diff_sq_le (u - 2)
  rw [h]
  nlinarith [hd]

/-! ## Fubini: `C(y) = ∫ F(y − v) η*(v) dv` -/

/-- `η*` vanishes off `(0, ∞)`. -/
theorem star_zero : ∀ t ∉ Ioi (0 : ℝ), HW.etaStar t = 0 := fun _ ht =>
  HW.etaStar_of_nonpos (not_lt.mp ht)

/-- `η* ≥ 0`. -/
theorem star_nonneg (v : ℝ) : 0 ≤ HW.etaStar v := by
  rcases le_or_gt v 0 with h | h
  · exact le_of_eq (HW.etaStar_of_nonpos h).symm
  · exact (HW.etaStar_pos h).le

/-- `η* ∈ L¹(ℝ)`. -/
theorem integrable_star : Integrable HW.etaStar :=
  (integrableOn_iff_integrable_of_support_subset fun t ht => by
      by_contra h
      exact ht (star_zero t h)).mp
    (Integrable.of_integral_ne_zero (by rw [EN.int_etaStar]; positivity))

/-- `∫_ℝ η* = √(π/2)/49`. -/
theorem star_int : ∫ v, HW.etaStar v = Real.sqrt (Real.pi / 2) / 49 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero star_zero]
  exact EN.int_etaStar

/-- `𝟙_{[0,∞)}·η* = η*`. -/
theorem star_indicator (u : ℝ) : Set.indicator (Ici (0 : ℝ)) HW.etaStar u = HW.etaStar u := by
  by_cases hu : 0 ≤ u
  · exact indicator_of_mem (mem_Ici.mpr hu) _
  · rw [indicator_of_notMem (fun h => hu (mem_Ici.mp h)),
      HW.etaStar_of_nonpos (le_of_lt (not_le.mp hu))]

/-- **The kernel after `t₂ = y − t₁ − v` is integrable on `ℝ²`**: `≤ |η∘(t₁)|·η*(v)`. -/
theorem integrable_kernel (y : ℝ) : Integrable (Function.uncurry fun t v : ℝ =>
    HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v) (volume.prod volume) := by
  have hb : Integrable (fun p : ℝ × ℝ => |HW.etaCirc p.1| * HW.etaStar p.2)
      (volume.prod volume) :=
    integrable_circ.abs.mul_prod integrable_star
  have hc : Continuous fun p : ℝ × ℝ => HW.etaCirc p.1 * HW.etaCirc (y - p.1 - p.2) :=
    (EN.continuous_etaCirc.comp continuous_fst).mul
      (EN.continuous_etaCirc.comp (by fun_prop : Continuous fun p : ℝ × ℝ => y - p.1 - p.2))
  refine hb.mono' (hc.aestronglyMeasurable.mul integrable_star.aestronglyMeasurable.comp_snd)
    (ae_of_all _ fun p => ?_)
  change ‖HW.etaCirc p.1 * HW.etaCirc (y - p.1 - p.2) * HW.etaStar p.2‖ ≤
    |HW.etaCirc p.1| * HW.etaStar p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (star_nonneg p.2)]
  calc |HW.etaCirc p.1| * |HW.etaCirc (y - p.1 - p.2)| * HW.etaStar p.2
      ≤ |HW.etaCirc p.1| * 1 * HW.etaStar p.2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (HW.etaCirc_le _) (abs_nonneg _))
          (star_nonneg _)
    _ = |HW.etaCirc p.1| * HW.etaStar p.2 := by ring

/-- The inner integral is `F(y − v)η*(v)`. -/
theorem inner_kernel (y v : ℝ) :
    ∫ t, HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v =
      selfConv (y - v) * HW.etaStar v := by
  rw [integral_mul_const]
  have e : ∫ t, HW.etaCirc t * HW.etaCirc (y - t - v) = selfConv (y - v) :=
    integral_congr_ae (ae_of_all _ fun t => by
      change HW.etaCirc t * HW.etaCirc (y - t - v) = HW.etaCirc t * HW.etaCirc (y - v - t)
      rw [show y - t - v = y - v - t by ring])
  rw [e]

/-- `v ↦ F(y − v)η*(v) ∈ L¹(ℝ)`. -/
theorem integrable_conv_star (y : ℝ) : Integrable fun v => selfConv (y - v) * HW.etaStar v :=
  (integrable_kernel y).integral_prod_right.congr (ae_of_all _ fun v => inner_kernel y v)

/-- **Fubini**: `C_{η∘,η*}(y) = ∫ F(y − v)η*(v) dv`. -/
theorem ccon_eq (y : ℝ) :
    MajSp.ccon HW.etaCirc HW.etaStar y = ∫ v, selfConv (y - v) * HW.etaStar v := by
  unfold MajSp.ccon
  simp_rw [star_indicator]
  have hin : ∀ t, ∫ u in Ioi (0 : ℝ), HW.etaCirc t * HW.etaCirc u * HW.etaStar (y - (t + u)) =
      ∫ v, HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v := by
    intro t
    have hz' : ∀ u ∉ Ioi (0 : ℝ),
        HW.etaCirc t * HW.etaCirc u * HW.etaStar (y - (t + u)) = 0 := fun u hu => by
      simp [circ_of_nonpos (not_lt.mp hu)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz']
    calc ∫ u, HW.etaCirc t * HW.etaCirc u * HW.etaStar (y - (t + u))
        = ∫ v, HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar (y - (t + (y - t - v))) :=
          (integral_sub_left_eq_self
            (fun u => HW.etaCirc t * HW.etaCirc u * HW.etaStar (y - (t + u))) volume
              (y - t)).symm
      _ = ∫ v, HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v :=
          integral_congr_ae (ae_of_all _ fun v => by
            change HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar (y - (t + (y - t - v))) =
              HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v
            rw [show y - (t + (y - t - v)) = v by ring])
  have hz : ∀ t ∉ Ioi (0 : ℝ),
      ∫ u in Ioi (0 : ℝ), HW.etaCirc t * HW.etaCirc u * HW.etaStar (y - (t + u)) = 0 := by
    intro t ht
    simp [circ_of_nonpos (not_lt.mp ht)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc ∫ t, ∫ u in Ioi (0 : ℝ), HW.etaCirc t * HW.etaCirc u * HW.etaStar (y - (t + u))
      = ∫ t, ∫ v, HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v :=
        integral_congr_ae (ae_of_all _ hin)
    _ = ∫ v, ∫ t, HW.etaCirc t * HW.etaCirc (y - t - v) * HW.etaStar v :=
        integral_integral_swap (integrable_kernel y)
    _ = ∫ v, selfConv (y - v) * HW.etaStar v :=
        integral_congr_ae (ae_of_all _ fun v => inner_kernel y v)

/-! ## The moments of `η*` -/

/-- `A_k = ∫₀^∞ rᵏη₂(r) dr`. -/
noncomputable def Ak (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * HW.eta2 r

/-- `B_k = ∫₀^∞ yᵏφ(y) dy`. -/
noncomputable def Bk (k : ℕ) : ℝ := ∫ y in Ioi (0 : ℝ), y ^ k * HW.phi y

/-- **`∫₀^∞ sᵏη₂(s/y) ds = y^{k+1}A_k`** (`s = yr`). -/
theorem pow_eta2_scale (k : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ s in Ioi (0 : ℝ), s ^ k * HW.eta2 (s / y) = y ^ (k + 1) * Ak k := by
  have h := integral_comp_mul_left_Ioi (fun r => r ^ k * HW.eta2 r) 0 (inv_pos.mpr hy)
  rw [mul_zero, smul_eq_mul, inv_inv] at h
  have e : ∀ s : ℝ, s ^ k * HW.eta2 (s / y) = y ^ k * ((y⁻¹ * s) ^ k * HW.eta2 (y⁻¹ * s)) := by
    intro s
    have hs : y ^ k * (y⁻¹ * s) ^ k = s ^ k := by
      rw [← mul_pow, mul_inv_cancel_left₀ hy.ne']
    rw [div_eq_inv_mul, ← hs, mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi fun s _ => e s, integral_const_mul, h, pow_succ]
  unfold Ak
  ring

/-- **Fubini on the Mellin convolution**: `∫₀^∞ sᵏ(η₂ ∗_M φ)(s) ds = A_k·B_k`. -/
theorem mconv_mom (k : ℕ) (hA : IntegrableOn (fun r => r ^ k * HW.eta2 r) (Ioi 0))
    (hB : IntegrableOn (fun y => y ^ k * HW.phi y) (Ioi 0)) :
    IntegrableOn (fun s => s ^ k * HW.mconv HW.eta2 HW.phi s) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), s ^ k * HW.mconv HW.eta2 HW.phi s = Ak k * Bk k := by
  have hslice : ∀ y ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), s ^ k * (HW.eta2 (s / y) * HW.phi y / y) =
      Ak k * (y ^ k * HW.phi y) := by
    intro y hy
    have hy0 : 0 < y := hy
    have hc : y * (HW.phi y / y) = HW.phi y := mul_div_cancel₀ _ hy0.ne'
    calc ∫ s in Ioi (0 : ℝ), s ^ k * (HW.eta2 (s / y) * HW.phi y / y)
        = ∫ s in Ioi (0 : ℝ), s ^ k * HW.eta2 (s / y) * (HW.phi y / y) :=
          setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
      _ = y ^ (k + 1) * Ak k * (HW.phi y / y) := by
          rw [integral_mul_const, pow_eta2_scale k hy0]
      _ = Ak k * (y ^ k * HW.phi y) := by
          rw [pow_succ]
          linear_combination (y ^ k * Ak k) * hc
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun s y : ℝ => s ^ k * (HW.eta2 (s / y) * HW.phi y / y))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    ((measurable_fst.pow_const k).mul (((EN.measurable_eta2.comp
      (measurable_fst.div measurable_snd)).mul (HW.continuous_phi.measurable.comp
        measurable_snd)).div measurable_snd)).aestronglyMeasurable
  have hint : Integrable
      (Function.uncurry fun s y : ℝ => s ^ k * (HW.eta2 (s / y) * HW.phi y / y))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
      have hy0 : 0 < y := hy
      have h1 : IntegrableOn (fun s => (y⁻¹ * s) ^ k * HW.eta2 (y⁻¹ * s)) (Ioi 0) := by
        rw [integrableOn_Ioi_comp_mul_left_iff (fun r => r ^ k * HW.eta2 r) 0
          (inv_pos.mpr hy0), mul_zero]
        exact hA
      refine (h1.const_mul (y ^ k * (HW.phi y / y))).congr (ae_of_all _ fun s => ?_)
      have hs : y ^ k * (y⁻¹ * s) ^ k = s ^ k := by
        rw [← mul_pow, mul_inv_cancel_left₀ hy0.ne']
      change y ^ k * (HW.phi y / y) * ((y⁻¹ * s) ^ k * HW.eta2 (y⁻¹ * s)) =
        s ^ k * (HW.eta2 (s / y) * HW.phi y / y)
      rw [div_eq_inv_mul s y, ← hs]
      ring
    · refine (hB.const_mul (Ak k)).congr ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := hy
      change Ak k * (y ^ k * HW.phi y) =
        ∫ s in Ioi (0 : ℝ), ‖s ^ k * (HW.eta2 (s / y) * HW.phi y / y)‖
      rw [← hslice y hy]
      refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := hs
      exact (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0.le k) (div_nonneg
        (mul_nonneg (HW.eta2_nonneg _) (HW.phi_nonneg y)) hy0.le))).symm
  refine ⟨?_, ?_⟩
  · refine hint.integral_prod_left.congr (ae_of_all _ fun s => ?_)
    change ∫ y in Ioi (0 : ℝ), s ^ k * (HW.eta2 (s / y) * HW.phi y / y) =
      s ^ k * ∫ y in Ioi (0 : ℝ), HW.eta2 (s / y) * HW.phi y / y
    exact integral_const_mul _ _
  · calc ∫ s in Ioi (0 : ℝ), s ^ k * HW.mconv HW.eta2 HW.phi s
        = ∫ s in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), s ^ k * (HW.eta2 (s / y) * HW.phi y / y) :=
          setIntegral_congr_fun measurableSet_Ioi fun s _ => (integral_const_mul _ _).symm
      _ = ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), s ^ k * (HW.eta2 (s / y) * HW.phi y / y) :=
          integral_integral_swap hint
      _ = ∫ y in Ioi (0 : ℝ), Ak k * (y ^ k * HW.phi y) :=
          setIntegral_congr_fun measurableSet_Ioi fun y hy => hslice y hy
      _ = Ak k * Bk k := integral_const_mul _ _

/-- **`∫₀^∞ tᵏη*(t) dt = A_k B_k/49^{k+1}`** (`η*(t) = (η₂ ∗_M φ)(49t)`). -/
theorem mom_Ioi (k : ℕ) (hA : IntegrableOn (fun r => r ^ k * HW.eta2 r) (Ioi 0))
    (hB : IntegrableOn (fun y => y ^ k * HW.phi y) (Ioi 0)) :
    IntegrableOn (fun t => t ^ k * HW.etaStar t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ k * HW.etaStar t = Ak k * Bk k / 49 ^ (k + 1) := by
  obtain ⟨hI, hE⟩ := mconv_mom k hA hB
  have h49 : (49 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have e : ∀ t : ℝ, t ^ k * HW.etaStar t =
      (49 ^ k)⁻¹ * ((49 * t) ^ k * HW.mconv HW.eta2 HW.phi (49 * t)) := by
    intro t
    have h1 : ((49 : ℝ) ^ k)⁻¹ * ((49 * t) ^ k * HW.mconv HW.eta2 HW.phi (49 * t)) =
        ((49 : ℝ) ^ k)⁻¹ * 49 ^ k * (t ^ k * HW.mconv HW.eta2 HW.phi (49 * t)) := by
      rw [mul_pow]
      ring
    change t ^ k * HW.mconv HW.eta2 HW.phi (49 * t) = _
    rw [h1, inv_mul_cancel₀ h49, one_mul]
  have hsc := integral_comp_mul_left_Ioi (fun s => s ^ k * HW.mconv HW.eta2 HW.phi s) 0
    (by norm_num : (0 : ℝ) < 49)
  rw [mul_zero, smul_eq_mul] at hsc
  have hI2 : IntegrableOn (fun t => (49 * t) ^ k * HW.mconv HW.eta2 HW.phi (49 * t)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff (fun s => s ^ k * HW.mconv HW.eta2 HW.phi s) 0
      (by norm_num : (0 : ℝ) < 49), mul_zero]
    exact hI
  refine ⟨IntegrableOn.congr_fun (hI2.const_mul (49 ^ k)⁻¹) (fun t _ => (e t).symm)
    measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => e t, integral_const_mul, hsc, hE,
    pow_succ, div_eq_mul_inv, mul_inv]
  ring

/-- The same over `ℝ` (`η* = 0` on `(−∞, 0]`). -/
theorem mom_R (k : ℕ) (hA : IntegrableOn (fun r => r ^ k * HW.eta2 r) (Ioi 0))
    (hB : IntegrableOn (fun y => y ^ k * HW.phi y) (Ioi 0)) :
    Integrable (fun t => t ^ k * HW.etaStar t) ∧
      ∫ t, t ^ k * HW.etaStar t = Ak k * Bk k / 49 ^ (k + 1) := by
  obtain ⟨hI, hE⟩ := mom_Ioi k hA hB
  have hz : ∀ t ∉ Ioi (0 : ℝ), t ^ k * HW.etaStar t = 0 := fun t ht => by
    rw [star_zero t ht, mul_zero]
  refine ⟨(integrableOn_iff_integrable_of_support_subset fun t ht => ?_).mp hI, ?_⟩
  · by_contra h
    exact ht (hz t h)
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact hE

/-- `∫₀^∞ rᵏη₂ = ∫_{1/4}^{1/2} + ∫_{1/2}^{1}` (`supp η₂ = [1/4, 1]`). -/
theorem A_split (k : ℕ) : Ak k = (∫ r in (1 / 4 : ℝ)..(1 / 2), r ^ k * HW.eta2 r) +
    ∫ r in (1 / 2 : ℝ)..1, r ^ k * HW.eta2 r := by
  have h : Ak k = ∫ r in (1 / 4 : ℝ)..1, r ^ k * HW.eta2 r := by
    unfold Ak
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num) ht.1) fun t ht => ?_
    obtain ⟨h0, h1⟩ := ht
    have h0' : 0 < t := h0
    change t ^ k * HW.eta2 t = 0
    rcases le_or_gt t (1 / 4) with hq | hq
    · rw [HW.eta2_of_le_quarter h0' hq, mul_zero]
    · rw [HW.eta2_of_one_le (le_of_lt (not_le.mp fun h => h1 ⟨hq, h⟩)), mul_zero]
  have hc : ContinuousOn (fun r : ℝ => r ^ k * HW.eta2 r) (Ioi 0) :=
    (continuous_pow k).continuousOn.mul EN.eta2_contOn
  have hi1 : IntervalIntegrable (fun r : ℝ => r ^ k * HW.eta2 r) volume (1 / 4) (1 / 2) :=
    (hc.mono (HW.uIcc_pos (by norm_num) (by norm_num))).intervalIntegrable
  have hi2 : IntervalIntegrable (fun r : ℝ => r ^ k * HW.eta2 r) volume (1 / 2) 1 :=
    (hc.mono (HW.uIcc_pos (by norm_num) (by norm_num))).intervalIntegrable
  rw [h, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]

/-- `log(1/4) = −2 log 2`. -/
theorem log_quarter : Real.log (1 / 4) = -(2 * Real.log 2) := by
  rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
  norm_num

/-- `d/dx x³ = 3x²`. -/
theorem hasDerivAt_cube (r : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
  simpa using hasDerivAt_pow 3 r

/-- `∫_{1/4}^{1/2} r·η₂ = (log 2)/2 − 3/16`. -/
theorem A1_left : ∫ r in (1 / 4 : ℝ)..(1 / 2), r ^ 1 * HW.eta2 r = Real.log 2 / 2 - 3 / 16 := by
  have hsub : uIcc (1 / 4 : ℝ) (1 / 2) ⊆ Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hcongr : EqOn (fun r : ℝ => r ^ 1 * HW.eta2 r)
      (fun r => r * (4 * (2 * Real.log 2 + Real.log r))) (uIcc (1 / 4) (1 / 2)) := by
    intro r hr
    rw [uIcc_of_le (by norm_num)] at hr
    change r ^ 1 * HW.eta2 r = r * (4 * (2 * Real.log 2 + Real.log r))
    rw [pow_one, EN.eta2_left hr.1 hr.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ r ∈ uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt
      (fun r => 4 * Real.log 2 * r ^ 2 + 2 * (r ^ 2 * Real.log r) - r ^ 2)
      (r * (4 * (2 * Real.log 2 + Real.log r))) r := by
    intro r hr
    have hr0 : 0 < r := hsub hr
    have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    refine ((((EN.hasDerivAt_sq' r).const_mul (4 * Real.log 2)).add
      (((EN.hasDerivAt_sq' r).mul (Real.hasDerivAt_log hr0.ne')).const_mul 2)).sub
        (EN.hasDerivAt_sq' r)).congr_deriv ?_
    linear_combination (2 * r) * hi
  have hi : IntervalIntegrable (fun r => r * (4 * (2 * Real.log 2 + Real.log r))) volume
      (1 / 4) (1 / 2) :=
    (continuousOn_id.mul (continuousOn_const.mul (continuousOn_const.add
      (Real.continuousOn_log.mono fun r hr => (hsub hr).ne')))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, EN.log_half, log_quarter]
  ring

/-- `∫_{1/2}^{1} r·η₂ = 3/4 − (log 2)/2`. -/
theorem A1_right : ∫ r in (1 / 2 : ℝ)..1, r ^ 1 * HW.eta2 r = 3 / 4 - Real.log 2 / 2 := by
  have hsub : uIcc (1 / 2 : ℝ) 1 ⊆ Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hcongr : EqOn (fun r : ℝ => r ^ 1 * HW.eta2 r) (fun r => r * (-4 * Real.log r))
      (uIcc (1 / 2) 1) := by
    intro r hr
    rw [uIcc_of_le (by norm_num)] at hr
    change r ^ 1 * HW.eta2 r = r * (-4 * Real.log r)
    rw [pow_one, EN.eta2_right hr.1 hr.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ r ∈ uIcc (1 / 2 : ℝ) 1, HasDerivAt
      (fun r => -2 * (r ^ 2 * Real.log r) + r ^ 2) (r * (-4 * Real.log r)) r := by
    intro r hr
    have hr0 : 0 < r := hsub hr
    have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    refine ((((EN.hasDerivAt_sq' r).mul (Real.hasDerivAt_log hr0.ne')).const_mul (-2)).add
      (EN.hasDerivAt_sq' r)).congr_deriv ?_
    linear_combination (-2 * r) * hi
  have hi : IntervalIntegrable (fun r => r * (-4 * Real.log r)) volume (1 / 2) 1 :=
    (continuousOn_id.mul (continuousOn_const.mul
      (Real.continuousOn_log.mono fun r hr => (hsub hr).ne'))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, EN.log_half, Real.log_one]
  ring

/-- `∫_{1/4}^{1/2} r²·η₂ = (log 2)/6 − 7/144`. -/
theorem A2_left : ∫ r in (1 / 4 : ℝ)..(1 / 2), r ^ 2 * HW.eta2 r = Real.log 2 / 6 - 7 / 144 := by
  have hsub : uIcc (1 / 4 : ℝ) (1 / 2) ⊆ Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hcongr : EqOn (fun r : ℝ => r ^ 2 * HW.eta2 r)
      (fun r => r ^ 2 * (4 * (2 * Real.log 2 + Real.log r))) (uIcc (1 / 4) (1 / 2)) := by
    intro r hr
    rw [uIcc_of_le (by norm_num)] at hr
    change r ^ 2 * HW.eta2 r = r ^ 2 * (4 * (2 * Real.log 2 + Real.log r))
    rw [EN.eta2_left hr.1 hr.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ r ∈ uIcc (1 / 4 : ℝ) (1 / 2), HasDerivAt
      (fun r => 8 / 3 * Real.log 2 * r ^ 3 + 4 / 3 * (r ^ 3 * Real.log r) - 4 / 9 * r ^ 3)
      (r ^ 2 * (4 * (2 * Real.log 2 + Real.log r))) r := by
    intro r hr
    have hr0 : 0 < r := hsub hr
    have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    refine ((((hasDerivAt_cube r).const_mul (8 / 3 * Real.log 2)).add
      (((hasDerivAt_cube r).mul (Real.hasDerivAt_log hr0.ne')).const_mul (4 / 3))).sub
        ((hasDerivAt_cube r).const_mul (4 / 9))).congr_deriv ?_
    linear_combination (4 / 3 * r ^ 2) * hi
  have hi : IntervalIntegrable (fun r => r ^ 2 * (4 * (2 * Real.log 2 + Real.log r))) volume
      (1 / 4) (1 / 2) :=
    ((continuous_pow 2).continuousOn.mul (continuousOn_const.mul (continuousOn_const.add
      (Real.continuousOn_log.mono fun r hr => (hsub hr).ne')))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, EN.log_half, log_quarter]
  ring

/-- `∫_{1/2}^{1} r²·η₂ = 7/18 − (log 2)/6`. -/
theorem A2_right : ∫ r in (1 / 2 : ℝ)..1, r ^ 2 * HW.eta2 r = 7 / 18 - Real.log 2 / 6 := by
  have hsub : uIcc (1 / 2 : ℝ) 1 ⊆ Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hcongr : EqOn (fun r : ℝ => r ^ 2 * HW.eta2 r) (fun r => r ^ 2 * (-4 * Real.log r))
      (uIcc (1 / 2) 1) := by
    intro r hr
    rw [uIcc_of_le (by norm_num)] at hr
    change r ^ 2 * HW.eta2 r = r ^ 2 * (-4 * Real.log r)
    rw [EN.eta2_right hr.1 hr.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ r ∈ uIcc (1 / 2 : ℝ) 1, HasDerivAt
      (fun r => -4 / 3 * (r ^ 3 * Real.log r) + 4 / 9 * r ^ 3)
      (r ^ 2 * (-4 * Real.log r)) r := by
    intro r hr
    have hr0 : 0 < r := hsub hr
    have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    refine ((((hasDerivAt_cube r).mul (Real.hasDerivAt_log hr0.ne')).const_mul (-4 / 3)).add
      ((hasDerivAt_cube r).const_mul (4 / 9))).congr_deriv ?_
    linear_combination (-4 / 3 * r ^ 2) * hi
  have hi : IntervalIntegrable (fun r => r ^ 2 * (-4 * Real.log r)) volume (1 / 2) 1 :=
    ((continuous_pow 2).continuousOn.mul (continuousOn_const.mul
      (Real.continuousOn_log.mono fun r hr => (hsub hr).ne'))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, EN.log_half, Real.log_one]
  ring

/-- **`A₁ = ∫ rη₂ = 9/16`.** -/
theorem A1_eq : Ak 1 = 9 / 16 := by
  rw [A_split, A1_left, A1_right]
  ring

/-- **`A₂ = ∫ r²η₂ = 49/144`.** -/
theorem A2_eq : Ak 2 = 49 / 144 := by
  rw [A_split, A2_left, A2_right]
  ring

/-- **`B₁ = ∫₀^∞ y³e^{−y²/2} = 2`** (`EN.gauss_moment` at `q = 3`, `b = 1/2`). -/
theorem B1_eq : Bk 1 = 2 := by
  have h := EN.gauss_moment 3 (1 / 2) (by norm_num) (by norm_num)
  have e : (fun y : ℝ => y ^ 1 * HW.phi y) =
      fun y => y ^ (3 : ℝ) * Real.exp (-(1 / 2) * y ^ 2) := by
    funext y
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, HW.phi,
      show -(1 / 2) * y ^ 2 = -y ^ 2 / 2 by ring]
    ring
  rw [Bk, e, h, show -((3 : ℝ) + 1) / 2 = -2 by norm_num,
    show ((3 : ℝ) + 1) / 2 = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_two]
  norm_num

/-- **`B₂ = ∫₀^∞ y⁴e^{−y²/2} = (3/2)√2√π`** (`= 3√(π/2)`; `q = 4`, `b = 1/2`). -/
theorem B2_eq : Bk 2 = 3 / 2 * Real.sqrt 2 * Real.sqrt Real.pi := by
  have h := EN.gauss_moment 4 (1 / 2) (by norm_num) (by norm_num)
  have e : (fun y : ℝ => y ^ 2 * HW.phi y) =
      fun y => y ^ (4 : ℝ) * Real.exp (-(1 / 2) * y ^ 2) := by
    funext y
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, HW.phi,
      show -(1 / 2) * y ^ 2 = -y ^ 2 / 2 by ring]
    ring
  have hr : (1 / 2 : ℝ) ^ (-((4 : ℝ) + 1) / 2) = 4 * Real.sqrt 2 := by
    rw [show -((4 : ℝ) + 1) / 2 = -(2 + 1 / 2) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2), show (1 / 2 : ℝ)⁻¹ = 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_two, ← Real.sqrt_eq_rpow]
    norm_num
  have hg : Real.Gamma (((4 : ℝ) + 1) / 2) = 3 / 4 * Real.sqrt Real.pi := by
    rw [show ((4 : ℝ) + 1) / 2 = 3 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0),
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  rw [Bk, e, h, hr, hg]
  ring

/-- `B₂ ≤ 3.77` (truth `3.7599`), from `√2 ≤ 1.415`, `√π ≤ 1.7725`. -/
theorem B2_le : Bk 2 ≤ 3.77 := by
  have h2 : Real.sqrt 2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hp : Real.sqrt Real.pi ≤ 1.7725 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith [Real.pi_lt_d6]
  have h := mul_le_mul h2 hp (Real.sqrt_nonneg _) (by norm_num)
  rw [B2_eq]
  linarith

/-- `∫_ℝ v·η* = (9/8)/49²`. -/
theorem mom1 : Integrable (fun t => t ^ 1 * HW.etaStar t) ∧
    ∫ t, t ^ 1 * HW.etaStar t = 9 / 8 / 49 ^ 2 := by
  obtain ⟨hI, hE⟩ := mom_R 1 (Integrable.of_integral_ne_zero (by
      change Ak 1 ≠ 0
      rw [A1_eq]
      norm_num))
    (Integrable.of_integral_ne_zero (by
      change Bk 1 ≠ 0
      rw [B1_eq]
      norm_num))
  refine ⟨hI, ?_⟩
  rw [hE, A1_eq, B1_eq]
  norm_num

/-- `∫_ℝ v²·η* = (49/144)·B₂/49³`. -/
theorem mom2 : Integrable (fun t => t ^ 2 * HW.etaStar t) ∧
    ∫ t, t ^ 2 * HW.etaStar t = 49 / 144 * Bk 2 / 49 ^ 3 := by
  obtain ⟨hI, hE⟩ := mom_R 2 (Integrable.of_integral_ne_zero (by
      change Ak 2 ≠ 0
      rw [A2_eq]
      norm_num))
    (Integrable.of_integral_ne_zero (by
      change Bk 2 ≠ 0
      rw [B2_eq]
      positivity))
  refine ⟨hI, ?_⟩
  rw [hE, A2_eq]

/-- **The quadratic moments of `η*`**: `∫(c₀ + c₁v + c₂v²)η* = c₀m₀ + c₁m₁ + c₂m₂`. -/
theorem quad_star (c0 c1 c2 : ℝ) :
    Integrable (fun v => (c0 + c1 * v + c2 * v ^ 2) * HW.etaStar v) ∧
      ∫ v, (c0 + c1 * v + c2 * v ^ 2) * HW.etaStar v =
        c0 * (Real.sqrt (Real.pi / 2) / 49) + c1 * (9 / 8 / 49 ^ 2) +
          c2 * (49 / 144 * Bk 2 / 49 ^ 3) := by
  obtain ⟨I1, E1⟩ := mom1
  obtain ⟨I2, E2⟩ := mom2
  have I0' : Integrable fun v => c0 * HW.etaStar v := integrable_star.const_mul c0
  have I1' : Integrable fun v => c1 * (v ^ 1 * HW.etaStar v) := I1.const_mul c1
  have I2' : Integrable fun v => c2 * (v ^ 2 * HW.etaStar v) := I2.const_mul c2
  have I01 : Integrable fun v => c0 * HW.etaStar v + c1 * (v ^ 1 * HW.etaStar v) := I0'.add I1'
  have I012 : Integrable fun v =>
      c0 * HW.etaStar v + c1 * (v ^ 1 * HW.etaStar v) + c2 * (v ^ 2 * HW.etaStar v) :=
    I01.add I2'
  have e : (fun v => (c0 + c1 * v + c2 * v ^ 2) * HW.etaStar v) = fun v =>
      c0 * HW.etaStar v + c1 * (v ^ 1 * HW.etaStar v) + c2 * (v ^ 2 * HW.etaStar v) := by
    funext v
    ring
  rw [e]
  refine ⟨I012, ?_⟩
  rw [integral_add I01 I2', integral_add I0' I1', integral_const_mul, integral_const_mul,
    integral_const_mul, star_int, E1, E2]

/-! ## `C ≥ |η∘|₂²m₀ − (D/2)(a²m₀ − 2am₁ + m₂)` -/

/-- **The pointwise bound integrated**: with `a = y − 2`,
`C(y) ≥ ∫ (|η∘|₂² − (D/2)(y − v − 2)²)η*(v) dv`, the integrand written as a quadratic in `v`. -/
theorem ccon_ge (y : ℝ) :
    ∫ v, ((∫ t, HW.etaCirc t ^ 2) - (∫ t, EN.dCirc t ^ 2) / 2 * (y - 2) ^ 2 +
      (∫ t, EN.dCirc t ^ 2) * (y - 2) * v + -((∫ t, EN.dCirc t ^ 2) / 2) * v ^ 2) *
        HW.etaStar v ≤ MajSp.ccon HW.etaCirc HW.etaStar y := by
  rw [ccon_eq]
  refine integral_mono (quad_star _ _ _).1 (integrable_conv_star y) fun v => ?_
  refine mul_le_mul_of_nonneg_right (le_of_eq_of_le ?_ (conv_ge (y - v))) (star_nonneg v)
  ring

/-- **The route's output at any `y`**: `C(y) ≥ L·m₀ − (D/2)((y−2)²m₀ − 2(y−2)m₁ + m₂)`,
`L = ∫ η∘²`, `D = ∫ η∘'²`. -/
theorem ccon_quad (y : ℝ) :
    (∫ t, HW.etaCirc t ^ 2) * (Real.sqrt (Real.pi / 2) / 49) - (∫ t, EN.dCirc t ^ 2) / 2 *
      ((y - 2) ^ 2 * (Real.sqrt (Real.pi / 2) / 49) - 2 * (y - 2) * (9 / 8 / 49 ^ 2) +
        49 / 144 * Bk 2 / 49 ^ 3) ≤ MajSp.ccon HW.etaCirc HW.etaStar y := by
  have h := ccon_ge y
  rw [(quad_star _ _ _).2] at h
  refine le_of_eq_of_le ?_ h
  ring

/-! ## The instance `y = N/x`, the norms, and the closing arithmetic -/

/-- `a = N/x − 2 = 9/(196√(2π)) = c₁/49`, the mean of `η*`. -/
noncomputable def a_helf : ℝ := 9 / (196 * Real.sqrt (2 * Real.pi))

/-- **`N/x = 2 + a`** at `x = helfgottX N`, `N ≥ 1`. -/
theorem y_helf (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) / helfgottX N = 2 + a_helf := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold a_helf
  rw [helfgottX, div_div_cancel₀ hN0]

/-- `|η∘|₂² = ∫_ℝ η∘²`. -/
theorem l2_circ_sq : MajSp.l2 HW.etaCirc ^ 2 = ∫ t, HW.etaCirc t ^ 2 := by
  unfold MajSp.l2
  rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
    simp [circ_of_nonpos (not_lt.mp ht)]

/-- `|η∘'|₂² = ∫_ℝ η∘'²` (`deriv η∘ = EN.dCirc`). -/
theorem l2_dcirc_sq : MajSp.l2 (deriv HW.etaCirc) ^ 2 = ∫ t, EN.dCirc t ^ 2 := by
  unfold MajSp.l2
  rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), EN.deriv_etaCirc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
    simp [dCirc_of_nonpos (not_lt.mp ht)]

/-- **The exact lower bound at `x = helfgottX N`**, in the norms of `MajSp`. -/
theorem ccon_lower (N : ℕ) (hN : 1 ≤ N) :
    MajSp.l2 HW.etaCirc ^ 2 * (Real.sqrt (Real.pi / 2) / 49) -
      MajSp.l2 (deriv HW.etaCirc) ^ 2 / 2 * (a_helf ^ 2 * (Real.sqrt (Real.pi / 2) / 49) -
        2 * a_helf * (9 / 8 / 49 ^ 2) + 49 / 144 * Bk 2 / 49 ^ 3) ≤
      MajSp.ccon HW.etaCirc HW.etaStar ((N : ℝ) / helfgottX N) := by
  have h := ccon_quad ((N : ℝ) / helfgottX N)
  have hy : (N : ℝ) / helfgottX N - 2 = a_helf := by
    rw [y_helf N hN]
    ring
  rw [hy] at h
  rw [l2_circ_sq, l2_dcirc_sq]
  exact h

/-- **The closing arithmetic**: `a·√(π/2) = 9/392` makes `a²m₀ − 2am₁ = −9a/19208 ≤ 0`, so the
loss is at most `(D/2)·(49/144)·3.77/49³`; `hK` compares it with the constant `K`. -/
theorem close_gen (L D Dm K B2 : ℝ) (hD0 : 0 ≤ D) (hD : D ≤ Dm) (hB : B2 ≤ 3.77)
    (hK : Dm * (49 * 3.77) ≤ 2 * K * 144 * 49 ^ 2) :
    (Real.sqrt (Real.pi / 2) * L - K) / 49 ≤
      L * (Real.sqrt (Real.pi / 2) / 49) - D / 2 * (a_helf ^ 2 * (Real.sqrt (Real.pi / 2) / 49) -
        2 * a_helf * (9 / 8 / 49 ^ 2) + 49 / 144 * B2 / 49 ^ 3) := by
  have ha0 : 0 ≤ a_helf := by
    unfold a_helf
    positivity
  have h2 : Real.sqrt (2 * Real.pi) = 2 * Real.sqrt (Real.pi / 2) := by
    rw [show 2 * Real.pi = 2 ^ 2 * (Real.pi / 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have has : a_helf * Real.sqrt (Real.pi / 2) = 9 / 392 := by
    unfold a_helf
    rw [h2, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  have e : a_helf ^ 2 * (Real.sqrt (Real.pi / 2) / 49) = a_helf * (9 / 392) / 49 := by
    rw [← has]
    ring
  have hQ : a_helf ^ 2 * (Real.sqrt (Real.pi / 2) / 49) - 2 * a_helf * (9 / 8 / 49 ^ 2) +
      49 / 144 * B2 / 49 ^ 3 ≤ 49 / 144 * 3.77 / 49 ^ 3 := by
    rw [e]
    linarith
  have hDQ : D / 2 * (a_helf ^ 2 * (Real.sqrt (Real.pi / 2) / 49) -
      2 * a_helf * (9 / 8 / 49 ^ 2) + 49 / 144 * B2 / 49 ^ 3) ≤
      Dm / 2 * (49 / 144 * 3.77 / 49 ^ 3) :=
    calc _ ≤ D / 2 * (49 / 144 * 3.77 / 49 ^ 3) := mul_le_mul_of_nonneg_left hQ (by linarith)
      _ ≤ Dm / 2 * (49 / 144 * 3.77 / 49 ^ 3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  have hK' : Dm / 2 * (49 / 144 * 3.77 / 49 ^ 3) ≤ K / 49 := by
    linarith
  have e2 : (Real.sqrt (Real.pi / 2) * L - K) / 49 =
      L * (Real.sqrt (Real.pi / 2) / 49) - K / 49 := by
    ring
  rw [e2]
  linarith

/-! ## THE TARGETS -/

/-- **`MajSp.CLower HW.etaCirc HW.etaStar` — PROVED** (`eq:barbar`, Helfgott's `0.000834`):
at `|η∘'|₂² ≤ 2.7375293` the loss is `≤ 1.4925e-5` against `0.000834/49 = 1.7020e-5`. -/
theorem clower_helf : MajSp.CLower HW.etaCirc HW.etaStar := by
  intro hD N _ hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  exact le_trans (close_gen (MajSp.l2 HW.etaCirc ^ 2) (MajSp.l2 (deriv HW.etaCirc) ^ 2)
    2.7375293 0.000834 (Bk 2) (sq_nonneg _) hD B2_le (by norm_num)) (ccon_lower N hN1)

/-- **`EN.CLowerE HW.etaCirc HW.etaStar` — PROVED** (the loosened `0.000914`): at
`|η∘'|₂² ≤ 3` the loss is `≤ 1.6356e-5` against `0.000914/49 = 1.8653e-5`. -/
theorem clowerE_helf : EN.CLowerE HW.etaCirc HW.etaStar := by
  intro hD N _ hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  exact le_trans (close_gen (MajSp.l2 HW.etaCirc ^ 2) (MajSp.l2 (deriv HW.etaCirc) ^ 2)
    3 0.000914 (Bk 2) (sq_nonneg _) hD B2_le (by norm_num)) (ccon_lower N hN1)

end Principia.Common.TernaryGoldbach.CT
