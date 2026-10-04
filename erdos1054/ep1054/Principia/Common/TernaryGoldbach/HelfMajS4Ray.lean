/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajS4Spine
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

set_option autoImplicit false

/-!
# S4, link `RayBound` PROVED: the contour of `F_δ` rotated to a ray

`rayBound_holds : RayBound`: for `Re w > 0` and `0 < θ < π/4`,
`|F_δ(w)| ≤ e^{−|Im w|θ} ∫₀^∞ r^{Re w − 1} e^{−cos(2θ) r²/2 + 2π|δ| sin(θ) r} dr`.

**The route.** In log coordinates `t = e^{−u}` (`integral_Ioi_eq_exp`, Mathlib's
`integral_image_eq_integral_abs_deriv_smul`), `F_δ(w) = ∫_ℝ G(u) du` with the ENTIRE function
`G(z) = exp(−wz − e^{−2z}/2 + 2πiδe^{−z})` (`Gf_real`). Shifting the line of integration to
`Im z = y = ∓θ` (`strip_shift`: Cauchy–Goursat on rectangles, Mathlib's
`integral_boundary_rect_eq_zero_of_differentiableOn`, with the vertical sides killed by a dominator
`K e^{−a|u|}`, `norm_Gf_dom`) is the rotation of the ray `t ∈ (0, ∞)` to `arg t = ±θ`. On the
shifted line `|G(u + iy)| = exp(−σu + τy − e^{−2u}cos 2y/2 + 2πδe^{−u} sin y)` (`norm_Gf`), and
choosing the sign of `y` against `τ` gives `τy = −|τ|θ` and `2πδ sin y ≤ 2π|δ| sin θ` for EVERY sign
of `δ` (`norm_Gf_line`); substituting back gives the real ray integral. No Gamma function, no
saddle point and no case split on `sgn δ` enter here.
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set Filter Complex
open scoped Topology

/-- `e^{−a|u|}` is integrable on `ℝ` for `a > 0`. -/
theorem integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => Real.exp (-a * |u|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · refine (integrableOn_exp_mul_Iic ha 0).congr_fun (fun u hu => ?_) measurableSet_Iic
    simp only [mem_Iic] at hu
    simp only
    rw [abs_of_nonpos hu, neg_mul_neg]
  · refine (exp_neg_integrableOn_Ioi 0 ha).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [mem_Ioi] at hu
    simp only
    rw [abs_of_pos hu]

/-- **A strip shift**: an entire `G` dominated by `K e^{−a|u|}` on the strip between `Im = 0` and
`Im = y` has the same integral along both edges. -/
theorem strip_shift {G : ℂ → ℂ} (hG : Differentiable ℂ G) {y K a : ℝ} (ha : 0 < a)
    (hb : ∀ u v : ℝ, v ∈ uIcc 0 y → ‖G (u + v * I)‖ ≤ K * Real.exp (-a * |u|)) :
    ∫ u : ℝ, G u = ∫ u : ℝ, G (u + y * I) := by
  have hint : ∀ v ∈ uIcc 0 y, Integrable (fun u : ℝ => G (u + v * I)) := fun v hv =>
    ((integrable_exp_neg_abs ha).const_mul K).mono'
      (hG.continuous.comp (continuous_ofReal.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun u => hb u v hv)
  have hint0 : Integrable (fun u : ℝ => G u) := by
    simpa using hint 0 left_mem_uIcc
  have hinty := hint y right_mem_uIcc
  have hvert : ∀ T : ℝ, 0 ≤ T → ∀ s : ℝ, |s| = T →
      ‖∫ v in (0 : ℝ)..y, G (s + v * I)‖ ≤ K * Real.exp (-a * T) * |y - 0| := by
    intro T _ s hs
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_
    rw [← hs]
    exact hb s v (uIoc_subset_uIcc hv)
  have C : ∀ T : ℝ, (∫ x in (-T)..T, G x) - (∫ x in (-T)..T, G (x + y * I)) +
      I * (∫ v in (0 : ℝ)..y, G (T + v * I)) - I * (∫ v in (0 : ℝ)..y, G (-T + v * I)) = 0 := by
    intro T
    have := integral_boundary_rect_eq_zero_of_differentiableOn G (((-T : ℝ)) : ℂ) (T + y * I)
      hG.differentiableOn
    simpa only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re,
      ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, tsub_zero, add_im, mul_im,
      mul_one, zero_add, smul_eq_mul, ofReal_neg] using this
  set V : ℝ → ℂ := fun T => I * (∫ v in (0 : ℝ)..y, G (T + v * I)) -
    I * (∫ v in (0 : ℝ)..y, G (-T + v * I)) with hV
  have hI1 : (fun T : ℝ => ∫ x in (-T)..T, G (x + y * I)) =
      fun T => (∫ x in (-T)..T, G x) + V T := by
    funext T
    have := C T
    simp only [hV]
    linear_combination -this
  have hVt : Tendsto V atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => 2 * (K * Real.exp (-a * T) * |y - 0|)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun T : ℝ => Real.exp (-a * T)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by linarith)).mpr
          tendsto_id)
      simpa using ((h1.const_mul K).mul_const |y - 0|).const_mul 2
    refine squeeze_zero_norm' ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => ?_) hlim
    simp only [hV]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_I, one_mul, one_mul, two_mul]
    refine add_le_add (hvert T hT T (abs_of_nonneg hT)) ?_
    have := hvert T hT (-T) (by rw [abs_neg, abs_of_nonneg hT])
    simpa using this
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral hint0 tendsto_neg_atTop_atBot
    tendsto_id) ?_
  have h2 := intervalIntegral_tendsto_integral hinty tendsto_neg_atTop_atBot tendsto_id
  simp only [id] at h2 ⊢
  rw [hI1] at h2
  have h3 := h2.sub hVt
  simpa using h3

/-- `∫_{(0,∞)} g = ∫_ℝ e^{−u} g(e^{−u})`. -/
theorem integral_Ioi_eq_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ t in Ioi (0 : ℝ), g t = ∫ u : ℝ, Real.exp (-u) • g (Real.exp (-u)) := by
  have himg : (Real.exp ∘ Neg.neg) '' univ = Ioi (0 : ℝ) := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ,
      Real.range_exp]
  have hderiv : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have hinj : InjOn (Real.exp ∘ Neg.neg) univ :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    Measure.restrict_univ]
  simp only [Function.comp, abs_neg, abs_of_pos (Real.exp_pos _)]

/-- Integrability transfers along the same substitution. -/
theorem integrable_exp_iff {g : ℝ → ℝ} :
    IntegrableOn g (Ioi 0) ↔ Integrable (fun u : ℝ => Real.exp (-u) • g (Real.exp (-u))) := by
  have himg : (Real.exp ∘ Neg.neg) '' univ = Ioi (0 : ℝ) := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ,
      Real.range_exp]
  have hderiv : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have hinj : InjOn (Real.exp ∘ Neg.neg) univ :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    integrableOn_univ]
  simp only [Function.comp, abs_neg, abs_of_pos (Real.exp_pos _)]


/-- The integrand of `F_δ` in log coordinates, continued to `ℂ`. -/
noncomputable def Gf (δ : ℝ) (w z : ℂ) : ℂ :=
  Complex.exp (-(w * z) - Complex.exp (-(2 * z)) / 2 + 2 * Real.pi * I * δ * Complex.exp (-z))

/-- `G` is entire. -/
theorem differentiable_Gf (δ : ℝ) (w : ℂ) : Differentiable ℂ (Gf δ w) := by
  unfold Gf
  fun_prop

/-- On the real line `G` is the log-coordinate integrand of `F_δ`:
`e^{−u}·(e^{−u})^{w−1}f(e^{−u})`. -/
theorem Gf_real (δ : ℝ) (w : ℂ) (u : ℝ) :
    Real.exp (-u) • (((Real.exp (-u) : ℝ) : ℂ) ^ (w - 1) •
      (((Real.exp (-Real.exp (-u) ^ 2 / 2) : ℝ) : ℂ) *
        Principia.Common.Goldbach.e (δ * Real.exp (-u)))) = Gf δ w u := by
  have hpos : ((Real.exp (-u) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have h1 : ((Real.exp (-u) : ℝ) : ℂ) ^ (w - 1) = Complex.exp ((w - 1) * (-u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hpos, ← Complex.ofReal_log (Real.exp_pos _).le,
      Real.log_exp]
    push_cast
    ring_nf
  have h2 : Complex.exp (-(u : ℂ)) ^ 2 = Complex.exp (-(2 * (u : ℂ))) := by
    rw [sq, ← Complex.exp_add]
    congr 1
    ring
  rw [Complex.real_smul, smul_eq_mul, h1]
  unfold Principia.Common.Goldbach.e Gf
  push_cast
  rw [h2, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- `|G(u + iv)| = exp(−σu + τv − e^{−2u}cos 2v/2 + 2πδe^{−u} sin v)`. -/
theorem norm_Gf (δ : ℝ) (w : ℂ) (u v : ℝ) :
    ‖Gf δ w (u + v * I)‖ = Real.exp (-(w.re * u) + w.im * v -
      Real.exp (-(2 * u)) * Real.cos (2 * v) / 2 +
        2 * Real.pi * δ * Real.exp (-u) * Real.sin v) := by
  rw [Gf, Complex.norm_exp]
  congr 1
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  ring_nf

/-- AM-GM: `A s ≤ A²/c + c s²/4`. -/
theorem amgm {A s c : ℝ} (hc : 0 < c) : A * s ≤ A ^ 2 / c + c * s ^ 2 / 4 := by
  have h : 0 ≤ (c * s / 2 - A) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have e : A ^ 2 / c + c * s ^ 2 / 4 - A * s = (c * s / 2 - A) ^ 2 / c := by
    field_simp
    ring
  linarith

/-- The ray integrand is integrable on `(0, ∞)` for `m > −1`, `c > 0`. -/
theorem integrableOn_ray {m c b : ℝ} (hm : -1 < m) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(c * t ^ 2) / 2 + b * t)) (Ioi 0) := by
  have hi := (integrableOn_rpow_mul_exp_neg_mul_sq (b := c / 4) (by positivity) hm).const_mul
    (Real.exp (b ^ 2 / c))
  refine hi.mono' (by fun_prop : Measurable fun t : ℝ =>
      t ^ m * Real.exp (-(c * t ^ 2) / 2 + b * t)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : Real.exp (-(c * t ^ 2) / 2 + b * t) ≤
      Real.exp (b ^ 2 / c) * Real.exp (-(c / 4) * t ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := amgm (A := b) (s := t) hc
    nlinarith
  calc t ^ m * Real.exp (-(c * t ^ 2) / 2 + b * t)
      ≤ t ^ m * (Real.exp (b ^ 2 / c) * Real.exp (-(c / 4) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le _)
    _ = Real.exp (b ^ 2 / c) * (t ^ m * Real.exp (-(c / 4) * t ^ 2)) := by ring

/-- The real inequality behind the strip dominator `K e^{−a|u|}`. -/
theorem dom_exponent {σ B c a : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) (hc : 0 < c) (hea1 : a ≤ σ)
    (hea2 : a ≤ c / 4) (u : ℝ) :
    -(σ * u) - Real.exp (-(2 * u)) * c / 2 + B * Real.exp (-u) ≤
      B + (σ + B) ^ 2 / c + -a * |u| := by
  have he1 := Real.exp_pos (-u)
  have hsq : 0 ≤ (σ + B) ^ 2 / c := by positivity
  rcases le_or_gt 0 u with hu | hu
  · have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonneg hu]
    have : a * u ≤ σ * u := mul_le_mul_of_nonneg_right hea1 hu
    have : B * Real.exp (-u) ≤ B := by nlinarith
    have : 0 ≤ Real.exp (-(2 * u)) * c / 2 := by positivity
    linarith
  · rw [abs_of_neg hu]
    obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = Real.exp (-u) := ⟨_, rfl⟩
    have hs1 : 1 - u ≤ s := by
      have := Real.add_one_le_exp (-u)
      rw [hsd]
      linarith
    have hs2 : Real.exp (-(2 * u)) = s ^ 2 := by
      rw [hsd, sq, ← Real.exp_add]
      ring_nf
    rw [hs2, ← hsd]
    have hau : c / 4 * u ≤ a * u := mul_le_mul_of_nonpos_right hea2 hu.le
    have hamgm : σ * s + B * s ≤ (σ + B) ^ 2 / c + c * s ^ 2 / 4 := by
      have := amgm (A := σ + B) (s := s) hc
      linarith [show (σ + B) * s = σ * s + B * s by ring]
    have h5 : -(σ * u) ≤ σ * s - σ := by nlinarith
    have h6 : 0 ≤ c * s ^ 2 - c * s + c := by nlinarith [sq_nonneg (s - 1 / 2)]
    have h7 : c / 4 - c / 4 * s ≤ c / 4 * u := by nlinarith
    have h8 : -a * -u = a * u := by ring
    rw [h8]
    linarith

/-- The strip dominator. -/
theorem norm_Gf_dom {δ θ c B a : ℝ} {w : ℂ} (hσ : 0 < w.re) (hθ1 : θ < Real.pi / 4)
    (hcd : c = Real.cos (2 * θ)) (hc : 0 < c) (hBd : B = 2 * Real.pi * |δ|) (hB : 0 ≤ B)
    (hea1 : a ≤ w.re) (hea2 : a ≤ c / 4) (u v : ℝ) (hvθ : |v| ≤ θ) :
    ‖Gf δ w (u + v * I)‖ ≤
      Real.exp (|w.im| * θ + B + (w.re + B) ^ 2 / c) * Real.exp (-a * |u|) := by
  have hpi := Real.pi_pos
  rw [norm_Gf, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : w.im * v ≤ |w.im| * θ :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hvθ (abs_nonneg _))
  have h2 : c ≤ Real.cos (2 * v) := by
    rw [← Real.cos_abs (2 * v), hcd]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
    rw [abs_mul, abs_two]
    linarith
  have he1 := Real.exp_pos (-u)
  have he2 := Real.exp_pos (-(2 * u))
  have h3 : 2 * Real.pi * δ * Real.exp (-u) * Real.sin v ≤ B * Real.exp (-u) := by
    have hab : 2 * Real.pi * δ * Real.sin v ≤ B := by
      have h := le_abs_self (2 * Real.pi * δ * Real.sin v)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
      have := Real.abs_sin_le_one v
      have := abs_nonneg δ
      rw [hBd]
      nlinarith
    nlinarith
  have h4 : Real.exp (-(2 * u)) * c ≤ Real.exp (-(2 * u)) * Real.cos (2 * v) :=
    mul_le_mul_of_nonneg_left h2 he2.le
  have key := dom_exponent hσ hB hc hea1 hea2 u
  linarith

/-- The pointwise bound on the shifted line. -/
theorem norm_Gf_line {δ θ c b y : ℝ} {w : ℂ} (hy1 : w.im * y = -(|w.im| * θ))
    (hy2 : Real.cos (2 * y) = c) (hsin : |Real.sin y| = Real.sin θ)
    (hbd : b = 2 * Real.pi * |δ| * Real.sin θ) (u : ℝ) :
    ‖Gf δ w (u + y * I)‖ ≤ Real.exp (-(|w.im| * θ)) *
      (Real.exp (-u) • (Real.exp (-u) ^ (w.re - 1) *
        Real.exp (-(c * Real.exp (-u) ^ 2) / 2 + b * Real.exp (-u)))) := by
  have hpi := Real.pi_pos
  rw [norm_Gf, smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : Real.exp (-u) ^ 2 = Real.exp (-(2 * u)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hsq, hy2]
  have he1 := Real.exp_pos (-u)
  have h3 : 2 * Real.pi * δ * Real.exp (-u) * Real.sin y ≤ b * Real.exp (-u) := by
    have hab : 2 * Real.pi * δ * Real.sin y ≤ b := by
      have := le_abs_self (2 * Real.pi * δ * Real.sin y)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), hsin] at this
      rw [hbd]
      linarith
    nlinarith
  linarith

/-- **LINK [RayBound] PROVED** — the contour rotation, as a strip shift in log coordinates. -/
theorem rayBound_holds : RayBound := by
  intro δ w θ hσ hθ0 hθ1
  have hpi := Real.pi_pos
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = Real.cos (2 * θ) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = 2 * Real.pi * |δ| * Real.sin θ := ⟨_, rfl⟩
  rw [← hcd, ← hbd]
  have hc : 0 < c := by
    rw [hcd]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  obtain ⟨y, hyd⟩ : ∃ y : ℝ, y = if 0 ≤ w.im then -θ else θ := ⟨_, rfl⟩
  have hyabs : |y| = θ := by
    rcases le_or_gt 0 w.im with h | h
    · rw [hyd, if_pos h, abs_neg, abs_of_pos hθ0]
    · rw [hyd, if_neg (not_le.mpr h), abs_of_pos hθ0]
  have hy1 : w.im * y = -(|w.im| * θ) := by
    rcases le_or_gt 0 w.im with h | h
    · rw [hyd, if_pos h, abs_of_nonneg h]
      ring
    · rw [hyd, if_neg (not_le.mpr h), abs_of_neg h]
      ring
  have hy2 : Real.cos (2 * y) = c := by
    rw [← Real.cos_abs, abs_mul, abs_two, hyabs, hcd]
  have hsin : |Real.sin y| = Real.sin θ := by
    rcases le_or_gt 0 w.im with h | h
    · rw [hyd, if_pos h, Real.sin_neg, abs_neg, abs_of_nonneg hsθ]
    · rw [hyd, if_neg (not_le.mpr h), abs_of_nonneg hsθ]
  have e1 : Fd δ w = ∫ u : ℝ, Gf δ w u := by
    rw [Fd, mellin, integral_Ioi_eq_exp]
    congr 1
    funext u
    exact Gf_real δ w u
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = 2 * Real.pi * |δ| := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBd]; positivity
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = min w.re (c / 4) := ⟨_, rfl⟩
  have ha : 0 < a := by rw [had]; exact lt_min hσ (by positivity)
  have hea1 : a ≤ w.re := by rw [had]; exact min_le_left _ _
  have hea2 : a ≤ c / 4 := by rw [had]; exact min_le_right _ _
  have e2 := strip_shift (differentiable_Gf δ w) ha (y := y) fun u v hv =>
    norm_Gf_dom hσ hθ1 hcd hc hBd hB hea1 hea2 u v (by
      have := abs_sub_left_of_mem_uIcc hv
      rw [sub_zero, sub_zero, hyabs] at this
      exact this)
  have hk : IntegrableOn (fun t : ℝ => t ^ (w.re - 1) * Real.exp (-(c * t ^ 2) / 2 + b * t))
      (Ioi 0) := integrableOn_ray (by linarith) hc
  have hK := integrable_exp_iff.mp hk
  rw [e1, e2]
  calc ‖∫ u : ℝ, Gf δ w (u + y * I)‖
      ≤ ∫ u : ℝ, Real.exp (-(|w.im| * θ)) * (Real.exp (-u) • (Real.exp (-u) ^ (w.re - 1) *
          Real.exp (-(c * Real.exp (-u) ^ 2) / 2 + b * Real.exp (-u)))) :=
        norm_integral_le_of_norm_le (hK.const_mul _)
          (Eventually.of_forall (norm_Gf_line hy1 hy2 hsin hbd))
    _ = Real.exp (-(|w.im| * θ)) * rayInt (w.re - 1) c b := by
        rw [integral_const_mul, rayInt, integral_Ioi_eq_exp]

end Principia.Common.TernaryGoldbach.S4
