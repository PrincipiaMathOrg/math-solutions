/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.FourierBessel
import Principia.Common.TernaryGoldbach.DrujalSpine
import Principia.Common.TernaryGoldbach.RegWHelf
import Principia.Common.TernaryGoldbach.ClowerTaylor

set_option autoImplicit false

/-!
# The three Plancherel links of `lem:drujal`, PROVED: `MardiQ`, `BandQ`, `TailQ`

`DS.MardiQ`, `DS.BandQ` and `DS.TailQ` (`DrujalSpine.lean`) are facts about the Fourier integral
`MajSp.mainFT η δ = ∫_0^∞ η(t) e(δt) dt` and `DS.iQ η w = ∫_{−w}^{w} |mainFT η β|² dβ`. Here each
is reduced to the generic `Principia.Common.FourierBessel`, through `zext η` (`η` on `(0, ∞)`,
`0` elsewhere): `mainFT η β = 𝓕 (zext η) (−β)` (`mainFT_eq`), so
`iQ η w = ∫_{−w}^{w} |𝓕 (zext η)|²` (`iQ_eq`) and `‖zext η‖₂² = |η|₂²` (`integral_zext_sq`).

* **`mardiQ_of`** — `MardiQ η` for EVERY `η ∈ L¹ ∩ L²` on `(0, ∞)` (`FourierBessel.bessel`);
  **`mardiQ_helf`** at `η₊` (`RW.integrable_etaPlus`, `RW.memLp_etaPlus_two`).
* **`bandQ_of`** — `BandQ η η∘` for every pair in `L¹ ∩ L²`: `𝓕` is additive
  (`fourier_zext_add`), `FourierBessel.band_lower` is Cauchy–Schwarz in `L²([−w, w])`, and
  `MardiQ` bounds both band norms by the time-domain norms; **`bandQ_helf`** at `(η₊, η∘)`.
* **`tailQ_helf`** — `TailQ η∘` at Helfgott's `η∘ = t³(2−t)³e^{−(t−1)²/2}` on `[0, 2]`:
  `𝓕 η∘ = ∫_0^2 G₀(t−1)e(−tξ)` (`fourier_circ`), three integrations by parts with
  `G₀, G₁, G₂` vanishing at `t = 0, 2` give `|𝓕 η∘(ξ)| ≤ l3/(2π|ξ|)³` (`decay_circ`),
  `l3 = ∫_0^2 |G₃(t−1)| ≤ |η∘'''|₁` (`l3_le`); so `𝓕 η∘ ∈ L¹` (`integrable_ft_circ`),
  Parseval holds (`parseval_circ`), and the tails beyond `±w` cost `≤ l3²/(160π⁶w⁵)`.

The source's `TailQ` needs `η∘, η∘', η∘''` to vanish at the ends of the support, which its
printed hypotheses do not say; for Helfgott's `η∘` it is checked here (`G0`, `G1`, `G2` at `±1`).
-/

namespace Principia.Common.TernaryGoldbach.DP

open MeasureTheory Complex Set Real
open scoped FourierTransform

/-! ## `mainFT` as a Fourier transform -/

/-- **`η` on `(0, ∞)`, `0` elsewhere**, as a complex function on `ℝ`. -/
noncomputable def zext (η : ℝ → ℝ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator fun t => ((η t : ℝ) : ℂ)

/-- **`mainFT η β = 𝓕 (zext η) (−β)`.** -/
theorem mainFT_eq (η : ℝ → ℝ) (β : ℝ) : MajSp.mainFT η β = 𝓕 (zext η) (-β) := by
  rw [FourierBessel.fourier_eq_exp, MajSp.mainFT, ← integral_indicator measurableSet_Ioi]
  congr 1
  ext y
  by_cases hy : y ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hy, zext, indicator_of_mem hy, Goldbach.e, mul_comm]
    congr 2
    push_cast
    ring
  · rw [indicator_of_notMem hy, zext, indicator_of_notMem hy, mul_zero]

/-- **`iQ η w = ∫_{−w}^{w} |𝓕 (zext η)|²`.** -/
theorem iQ_eq (η : ℝ → ℝ) (w : ℝ) : DS.iQ η w = ∫ ξ in (-w)..w, ‖𝓕 (zext η) ξ‖ ^ 2 := by
  have h : ∫ x in (-w)..w, ‖𝓕 (zext η) (-x)‖ ^ 2 = ∫ x in (-w)..w, ‖𝓕 (zext η) x‖ ^ 2 := by
    simpa using intervalIntegral.integral_comp_neg (a := -w) (b := w)
      (fun ξ => ‖𝓕 (zext η) ξ‖ ^ 2)
  rw [← h]
  unfold DS.iQ
  congr 1
  ext β
  rw [mainFT_eq]

/-- `zext η ∈ L¹(ℝ)` when `η ∈ L¹(0, ∞)`. -/
theorem integrable_zext (η : ℝ → ℝ) (h : Integrable η (volume.restrict (Ioi 0))) :
    Integrable (zext η) :=
  (integrable_indicator_iff measurableSet_Ioi).2 h.ofReal

/-- `|zext η|² = 1_{(0,∞)}·η²`. -/
theorem norm_zext_sq (η : ℝ → ℝ) :
    (fun t => ‖zext η t‖ ^ 2) = (Ioi (0 : ℝ)).indicator fun t => η t ^ 2 := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp [zext, ht]
  · simp [zext, ht]

/-- `|zext η|² ∈ L¹(ℝ)` when `η² ∈ L¹(0, ∞)`. -/
theorem integrable_zext_sq (η : ℝ → ℝ)
    (h : Integrable (fun t => η t ^ 2) (volume.restrict (Ioi 0))) :
    Integrable fun t => ‖zext η t‖ ^ 2 := by
  rw [norm_zext_sq]
  exact (integrable_indicator_iff measurableSet_Ioi).2 h

/-- `‖zext η‖₂² = ∫_0^∞ η²`. -/
theorem integral_zext_sq (η : ℝ → ℝ) : ∫ t, ‖zext η t‖ ^ 2 = ∫ t in Ioi 0, η t ^ 2 := by
  rw [norm_zext_sq, integral_indicator measurableSet_Ioi]

/-- `|η|₂² = ∫_0^∞ η²` (no integrability needed: the integral is `≥ 0`). -/
theorem l2_sq (η : ℝ → ℝ) : MajSp.l2 η ^ 2 = ∫ t in Ioi 0, η t ^ 2 := by
  unfold MajSp.l2
  exact Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _)

/-- `η ∈ L²(0, ∞)` gives `η² ∈ L¹(0, ∞)`. -/
theorem sq_integrable_of_memLp (η : ℝ → ℝ) (h : MemLp η 2 (volume.restrict (Ioi 0))) :
    Integrable (fun t => η t ^ 2) (volume.restrict (Ioi 0)) :=
  (memLp_two_iff_integrable_sq h.1).1 h

/-! ## `MardiQ` -/

/-- **`MardiQ η` for every `η ∈ L¹ ∩ L²` on `(0, ∞)`**: `∫_{−w}^{w}|η̂|² ≤ |η|₂²`. -/
theorem mardiQ_of (η : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Ioi 0)))
    (h2 : Integrable (fun t => η t ^ 2) (volume.restrict (Ioi 0))) : DS.MardiQ η := by
  intro w hw
  rw [iQ_eq, l2_sq, ← integral_zext_sq]
  exact FourierBessel.bessel (zext η) (integrable_zext η h1) (integrable_zext_sq η h2) w hw

/-- **`MardiQ` at Helfgott's `η₊`.** -/
theorem mardiQ_helf : DS.MardiQ HW.etaPlus :=
  mardiQ_of _ RW.integrable_etaPlus (sq_integrable_of_memLp _ RW.memLp_etaPlus_two)

/-! ## `BandQ` -/

/-- `zext η = zext η∘ + zext (η − η∘)`. -/
theorem zext_add (η ηo : ℝ → ℝ) :
    zext η = fun t => zext ηo t + zext (fun t => η t - ηo t) t := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [zext, indicator_of_mem ht]
    push_cast
    ring
  · simp only [zext, indicator_of_notMem ht, add_zero]

/-- **`𝓕` is additive** on `zext` of `L¹(0, ∞)` weights. -/
theorem fourier_zext_add (η ηo : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Ioi 0)))
    (h1o : Integrable ηo (volume.restrict (Ioi 0))) (ξ : ℝ) :
    𝓕 (zext η) ξ = 𝓕 (zext ηo) ξ + 𝓕 (zext (fun t => η t - ηo t)) ξ := by
  have hc : Continuous fun y : ℝ => cexp (↑(-2 * π * y * ξ) * I) := by fun_prop
  have hb : ∀ y : ℝ, ‖cexp (↑(-2 * π * y * ξ) * I)‖ ≤ 1 := fun y =>
    (Complex.norm_exp_ofReal_mul_I _).le
  have hA := (integrable_zext ηo h1o).bdd_mul hc.aestronglyMeasurable (ae_of_all _ hb)
  have hB := (integrable_zext (fun t => η t - ηo t) (h1.sub h1o)).bdd_mul
    hc.aestronglyMeasurable (ae_of_all _ hb)
  rw [zext_add η ηo, FourierBessel.fourier_eq_exp, FourierBessel.fourier_eq_exp,
    FourierBessel.fourier_eq_exp, ← integral_add hA hB]
  congr 1
  ext y
  ring

/-- **`BandQ η η∘` for every pair in `L¹ ∩ L²` on `(0, ∞)`**: Cauchy–Schwarz in `L²([−w, w])`
(`FourierBessel.band_lower`) and `MardiQ` for `η∘` and `η − η∘`. -/
theorem bandQ_of (η ηo : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Ioi 0)))
    (h1o : Integrable ηo (volume.restrict (Ioi 0))) (h2 : MemLp η 2 (volume.restrict (Ioi 0)))
    (h2o : MemLp ηo 2 (volume.restrict (Ioi 0))) : DS.BandQ η ηo := by
  intro w hw
  have hd1 : Integrable (fun t => η t - ηo t) (volume.restrict (Ioi 0)) := h1.sub h1o
  have hd2 : Integrable (fun t => (η t - ηo t) ^ 2) (volume.restrict (Ioi 0)) :=
    sq_integrable_of_memLp _ (h2.sub h2o)
  have mo := mardiQ_of ηo h1o (sq_integrable_of_memLp _ h2o) w hw
  have md := mardiQ_of _ hd1 hd2 w hw
  have hb := FourierBessel.band_lower (𝓕 (zext ηo)) (𝓕 (zext (fun t => η t - ηo t)))
    (FourierBessel.continuous_fourier _ (integrable_zext _ h1o))
    (FourierBessel.continuous_fourier _ (integrable_zext _ hd1)) w hw
  have hsum : ∫ ξ in (-w)..w, ‖𝓕 (zext ηo) ξ + 𝓕 (zext (fun t => η t - ηo t)) ξ‖ ^ 2 =
      DS.iQ η w := by
    rw [iQ_eq]
    congr 1
    ext ξ
    rw [fourier_zext_add η ηo h1 h1o ξ]
  rw [← iQ_eq, ← iQ_eq, hsum] at hb
  have sa : Real.sqrt (DS.iQ ηo w) ≤ MajSp.l2 ηo := by
    rw [← Real.sqrt_sq (MajSp.l2_nonneg ηo)]
    exact Real.sqrt_le_sqrt mo
  have sb : Real.sqrt (DS.iQ (fun t => η t - ηo t) w) ≤ MajSp.l2 (fun t => η t - ηo t) := by
    rw [← Real.sqrt_sq (MajSp.l2_nonneg _)]
    exact Real.sqrt_le_sqrt md
  have hp : 2 * Real.sqrt (DS.iQ ηo w) * Real.sqrt (DS.iQ (fun t => η t - ηo t) w) ≤
      2 * MajSp.l2 ηo * MajSp.l2 (fun t => η t - ηo t) := by
    have := mul_le_mul sa sb (Real.sqrt_nonneg _) (MajSp.l2_nonneg _)
    linarith
  nlinarith [sq_nonneg (MajSp.l2 (fun t => η t - ηo t))]

/-- **`BandQ` at Helfgott's `(η₊, η∘)`.** -/
theorem bandQ_helf : DS.BandQ HW.etaPlus HW.etaCirc :=
  bandQ_of _ _ RW.integrable_etaPlus CT.integrable_circ.integrableOn RW.memLp_etaPlus_two
    RW.memLp_etaCirc_two

/-! ## `TailQ` at `η∘` -/

/-- `zext η∘ = η∘` (it vanishes on `(−∞, 0]`). -/
theorem zext_circ : zext HW.etaCirc = fun t => ((HW.etaCirc t : ℝ) : ℂ) := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [zext, indicator_of_mem ht]
  · rw [zext, indicator_of_notMem ht, CT.circ_of_nonpos (not_lt.mp ht), Complex.ofReal_zero]

/-- `η∘ ∈ L¹(ℝ)`. -/
theorem integrable_zext_circ : Integrable (zext HW.etaCirc) := by
  rw [zext_circ]
  exact CT.integrable_circ.ofReal

/-- `η∘` is continuous. -/
theorem continuous_zext_circ : Continuous (zext HW.etaCirc) := by
  rw [zext_circ]
  exact Complex.continuous_ofReal.comp EN.continuous_etaCirc

/-- `η∘(t) = G₀(t − 1)` on `[0, 2]`. -/
theorem circ_eq_G0 {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : HW.etaCirc t = EN.G0 (t - 1) := by
  rw [HW.etaCirc_eq h0 h2]
  unfold EN.G0 EN.P0
  ring

/-- **`𝓕 η∘(ξ) = ∫_0^2 G₀(t − 1) e(−tξ) dt`.** -/
theorem fourier_circ (ξ : ℝ) :
    𝓕 (zext HW.etaCirc) ξ =
      ∫ t in (0 : ℝ)..2, ((EN.G0 (t - 1) : ℝ) : ℂ) * cexp (↑(-2 * π * t * ξ) * I) := by
  have hz : ∀ t, t ∉ Ioc (0 : ℝ) 2 →
      cexp (↑(-2 * π * t * ξ) * I) * ((HW.etaCirc t : ℝ) : ℂ) = 0 := by
    intro t ht
    rcases le_or_gt t 0 with h | h
    · rw [CT.circ_of_nonpos h, Complex.ofReal_zero, mul_zero]
    · have h2 : 2 < t := lt_of_not_ge fun h2 => ht ⟨h, h2⟩
      rw [EN.etaCirc_of_two_lt h2, Complex.ofReal_zero, mul_zero]
  rw [zext_circ, FourierBessel.fourier_eq_exp, intervalIntegral.integral_of_le (by norm_num),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [circ_eq_G0 ht.1.le ht.2, mul_comm]

/-- **`l3 = ∫_0^2 |G₃(t − 1)|`**, the mass of `η∘'''` on `(0, 2)`. -/
noncomputable def l3 : ℝ := ∫ t in (0 : ℝ)..2, |EN.G3 (t - 1)|

/-- `l3 ≥ 0`. -/
theorem l3_nonneg : 0 ≤ l3 :=
  intervalIntegral.integral_nonneg (by norm_num) fun t _ => abs_nonneg _

/-- **`l3 ≤ |η∘'''|₁`** (`η∘''' = G₃(· − 1)` on `(0, 2)`, `EN.third_eq`). -/
theorem l3_le : l3 ≤ MajSp.l1 (iteratedDeriv 3 HW.etaCirc) := by
  unfold l3 MajSp.l1
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hc : ∫ t in Ioo (0 : ℝ) 2, |EN.G3 (t - 1)| =
      ∫ t in Ioo (0 : ℝ) 2, |iteratedDeriv 3 HW.etaCirc t| :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [EN.third_eq ht.1 ht.2]
  rw [hc]
  exact setIntegral_mono_set RW.integrable_third.abs (ae_of_all _ fun t => abs_nonneg _)
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 2 ⊆ Ioi 0).eventuallyLE

/-- **`eq:madge`: `|𝓕 η∘(ξ)| ≤ l3/(2π|ξ|)³`**, by three integrations by parts
(`G₀, G₁, G₂` vanish at `±1`). -/
theorem decay_circ (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (zext HW.etaCirc) ξ‖ ≤ l3 / (2 * π * |ξ|) ^ 3 := by
  rw [fourier_circ]
  exact FourierBessel.decay3 0 2 ξ (by norm_num) hξ (fun t => EN.G0 (t - 1))
    (fun t => EN.G1 (t - 1)) (fun t => EN.G2 (t - 1)) (fun t => EN.G3 (t - 1))
    (fun t => (EN.hasDerivAt_G0 (t - 1)).comp_sub_const t 1)
    (fun t => (EN.hasDerivAt_G1 (t - 1)).comp_sub_const t 1)
    (fun t => (EN.hasDerivAt_G2 (t - 1)).comp_sub_const t 1)
    (by unfold EN.G3 EN.P3; fun_prop)
    (by norm_num [EN.G0, EN.P0]) (by norm_num [EN.G0, EN.P0])
    (by norm_num [EN.G1, EN.P1]) (by norm_num [EN.G1, EN.P1])
    (by norm_num [EN.G2, EN.P2]) (by norm_num [EN.G2, EN.P2])

/-- **`𝓕 η∘ ∈ L¹`**: `|𝓕 η∘(ξ)| ≤ (2|η∘|₁ + 2·l3)/(1 + ξ²)`. -/
theorem integrable_ft_circ : Integrable (𝓕 (zext HW.etaCirc)) := by
  set A := ∫ y, ‖zext HW.etaCirc y‖ with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hbd : ∀ ξ : ℝ, ‖𝓕 (zext HW.etaCirc) ξ‖ ≤ (2 * A + 2 * l3) * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have hF0 := norm_nonneg (𝓕 (zext HW.etaCirc) ξ)
    have hA := FourierBessel.norm_fourier_le (zext HW.etaCirc) ξ
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rcases le_or_gt |ξ| 1 with h | h
    · have h1 : ξ ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg ξ]
      have h2 := mul_le_mul_of_nonneg_left h1 hF0
      nlinarith [l3_nonneg]
    · have hξ : ξ ≠ 0 := fun h0 => by
        rw [h0, abs_zero] at h
        linarith
      have hd := decay_circ ξ hξ
      rw [le_div_iff₀ (by positivity)] at hd
      have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
      have ha : |ξ| ≤ 2 * π * |ξ| := le_mul_of_one_le_left (abs_nonneg ξ) hpi
      have h3 : |ξ| ^ 3 ≤ (2 * π * |ξ|) ^ 3 := pow_le_pow_left₀ (abs_nonneg ξ) ha 3
      have hsq : ξ ^ 2 ≤ |ξ| ^ 3 := by
        rw [← sq_abs]
        nlinarith [mul_nonneg (sq_nonneg |ξ|) (sub_pos.2 h).le]
      have h1 : 1 ≤ ξ ^ 2 := by
        rw [← sq_abs]
        nlinarith
      have e0 := mul_le_mul_of_nonneg_left h1 hF0
      have e1 := mul_le_mul_of_nonneg_left hsq hF0
      have e2 := mul_le_mul_of_nonneg_left h3 hF0
      nlinarith
  exact (integrable_inv_one_add_sq.const_mul (2 * A + 2 * l3)).mono'
    (FourierBessel.continuous_fourier _ integrable_zext_circ).aestronglyMeasurable
    (ae_of_all _ hbd)

/-- `|𝓕 η∘|² ∈ L¹`. -/
theorem integrable_ft_circ_sq : Integrable fun ξ => ‖𝓕 (zext HW.etaCirc) ξ‖ ^ 2 := by
  refine (integrable_ft_circ.norm.const_mul (∫ y, ‖zext HW.etaCirc y‖)).mono'
    ((FourierBessel.continuous_fourier _ integrable_zext_circ).norm.pow 2).aestronglyMeasurable
    (ae_of_all _ fun ξ => ?_)
  change ‖‖𝓕 (zext HW.etaCirc) ξ‖ ^ 2‖ ≤
    (∫ y, ‖zext HW.etaCirc y‖) * ‖𝓕 (zext HW.etaCirc) ξ‖
  have hA := FourierBessel.norm_fourier_le (zext HW.etaCirc) ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)

/-- **Parseval for `η∘`**: `∫ |𝓕 η∘|² = |η∘|₂²`. -/
theorem parseval_circ : ∫ ξ, ‖𝓕 (zext HW.etaCirc) ξ‖ ^ 2 = MajSp.l2 HW.etaCirc ^ 2 := by
  rw [FourierBessel.parseval _ continuous_zext_circ integrable_zext_circ integrable_ft_circ,
    integral_zext_sq, l2_sq]

/-- **`TailQ` at Helfgott's `η∘`**: `I_q(η∘) ≥ |η∘|₂² − |η∘'''|₁²/(160π⁶w⁵)`. -/
theorem tailQ_helf : DS.TailQ HW.etaCirc := by
  intro w hw
  have ht := FourierBessel.tail_bound _ integrable_ft_circ_sq l3 decay_circ w hw
  rw [parseval_circ] at ht
  rw [iQ_eq]
  have hl : l3 ^ 2 ≤ MajSp.l1 (iteratedDeriv 3 HW.etaCirc) ^ 2 :=
    pow_le_pow_left₀ l3_nonneg l3_le 2
  have hd : l3 ^ 2 / (160 * π ^ 6 * w ^ 5) ≤
      MajSp.l1 (iteratedDeriv 3 HW.etaCirc) ^ 2 / (160 * π ^ 6 * w ^ 5) :=
    div_le_div_of_nonneg_right hl (by positivity)
  linarith

end Principia.Common.TernaryGoldbach.DP
