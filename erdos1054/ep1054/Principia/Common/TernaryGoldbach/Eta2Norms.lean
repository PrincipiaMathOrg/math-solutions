/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Eta2Reg

set_option autoImplicit false

/-!
# `EF.Eta2Norms` PROVED: `c₀(η₂ ∗_M ν_ε, 0) ≤ 8(1 + ε)` and `|(η₂ ∗_M ν_ε)'|₂ ≤ 7(1 + ε)`

**`eta2Norms_holds : EF.Eta2Norms`** — no named hypothesis. With `EF.eta2Reg_holds`
(`Eta2Reg.lean`) both named links of `EF.crepeC_of_named` are discharged, so the corrected
`lem:crepe` (`EF.CrepeC`) rests on `HM.ExplicitFormula` and the two cited zero-sum lemmas only.

## Route

By `hasDerivAt_eta2e`, `(η₂ ∗_M ν_ε)'(x) = D(x) = ∫₀^∞ ν_ε(u) e2d(x/u) du/u²` on `(0, ∞)`, with
`e2d = η₂'` a.e. Write `p(u) = ν_ε(u)/u` (a probability density on `(0, ∞)`, `DeltaSpikeMass`).

* **Weighted `L¹`** (`lint_D_le`): `|D(x)| x^α ≤ ∫ ν_ε(u) u^{α−2} · |e2d(x/u)| (x/u)^α du`
  (`D_pt_le`); Tonelli in `ℝ≥0∞` (`tonelli_div`, no integrability needed) and the scaling
  `∫₀^∞ ψ(x/u) dx = u ∫₀^∞ ψ` (`lint_comp_div`) factor the double integral as
  `(∫ p(u) u^α du) · ∫ |e2d(v)| v^α dv`, and `u^α ≤ 2^{ε|α|}` on `supp ν_ε = [2^{−ε}, 2^ε]`
  (`lint_spike_le`). For `α = ∓1/2` the second factor is `8` and `4` (`psi1_le`, `psi2_le`:
  `∫_{1/4}^1 4v^{α−1} dv` by `integral_rpow`), so `c₀ = (2/3)(n1h + n1s) ≤ (2/3)·12·2^{ε/2}
  = 8·2^{ε/2} ≤ 8(1 + ε/2)`.
* **`L²`** (`lint_Dsq_le`): pointwise Cauchy–Schwarz against `p` (`sq_integral_le`, from
  `2m|h| ≤ h² + m²`) gives `D(x)² ≤ ∫ ν_ε(u) u^{−3} e2d(x/u)² du` (`D_sq_le`), and the same
  Tonelli/scaling gives `∫ D² ≤ 2^ε ∫ e2d² = 48·2^ε` (`psi3_le`). So
  `|D|₂ ≤ √(48·2^ε) = 4√3·2^{ε/2} ≤ 7(1 + ε)` (`48(1 + ε) ≤ 49(1 + ε)²`).

Constants for `η₂` itself (mpmath and `scratchpad/e2links/num.py`): `c₀(η₂, 0) = (2/3)(8 + 4) = 8`,
`|η₂'|₂ = 4√3 = 6.928`; for a concrete bump `ν` the mollified values are `c₀ = 5.46, 6.70, 7.74`
and `|D|₂ = 3.98, 5.53, 6.66` at `ε = 1, 1/2, 1/10` — inside `8·2^{ε/2}`, `4√3·2^{ε/2}`.

## Junk values

`HM.n1h`, `HM.n1s` and `MajSp.l2` are Bochner integrals (junk `0` when not integrable). They are
evaluated here through `integral_eq_lintegral_of_nonneg_ae`, which holds with or without
integrability, against the `ℝ≥0∞` bounds above; the bounds are therefore about the real
integrals (which are finite: `D` is continuous and supported in `[1/8, 2]`, `Eta2Reg.lean`).
-/

namespace Principia.Common.TernaryGoldbach.E2

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {ν : ℝ → ℝ} {ε : ℝ}

/-! ## Tonelli for Mellin convolutions -/

/-- `∫₀^∞ ψ(x/u) dx = u ∫₀^∞ ψ` (`u > 0`), from `Real.map_volume_mul_right`. -/
theorem lint_comp_div {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) {u : ℝ} (hu : 0 < u) :
    ∫⁻ x in Ioi (0 : ℝ), ψ (x / u) = ENNReal.ofReal u * ∫⁻ v in Ioi (0 : ℝ), ψ v := by
  have hui : (0 : ℝ) < u⁻¹ := inv_pos.mpr hu
  have hind : ∀ x : ℝ, (Ioi (0 : ℝ)).indicator (fun x => ψ (x / u)) x =
      (Ioi (0 : ℝ)).indicator ψ (x * u⁻¹) := by
    intro x
    by_cases hx : (0 : ℝ) < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
        indicator_of_mem (show x * u⁻¹ ∈ Ioi (0 : ℝ) from mul_pos hx hui), div_eq_mul_inv]
    · have hx' : ¬ (0 : ℝ) < x * u⁻¹ := fun h => hx (by nlinarith)
      rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
        indicator_of_notMem (show x * u⁻¹ ∉ Ioi (0 : ℝ) from hx')]
  have hmap := lintegral_map (μ := volume) (hψ.indicator (s := Ioi (0 : ℝ)) measurableSet_Ioi)
    (measurable_mul_const u⁻¹)
  rw [Real.map_volume_mul_right hui.ne', lintegral_smul_measure, inv_inv, abs_of_pos hu] at hmap
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  simp_rw [hind]
  rw [← hmap]
  rfl

/-- **Tonelli for a Mellin convolution**:
`∫₀^∞ ∫₀^∞ φ(u) ψ(x/u) du dx = (∫₀^∞ φ(u) u du)·∫₀^∞ ψ`. -/
theorem tonelli_div {φ ψ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫⁻ x in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), φ u * ψ (x / u) =
      (∫⁻ u in Ioi (0 : ℝ), φ u * ENNReal.ofReal u) * ∫⁻ v in Ioi (0 : ℝ), ψ v := by
  rw [lintegral_lintegral_swap (f := fun x u => φ u * ψ (x / u))
    ((hφ.comp measurable_snd).mul (hψ.comp (measurable_fst.div measurable_snd))).aemeasurable]
  rw [← lintegral_mul_const _ (hφ.mul ENNReal.measurable_ofReal)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hm : Measurable fun x : ℝ => ψ (x / u) := hψ.comp (measurable_id.div_const u)
  rw [lintegral_const_mul _ hm, lint_comp_div hψ hu, mul_assoc]

/-! ## The spike's weighted mass -/

/-- `u^β ≤ 2^{ε|β|}` on the support `[2^{−ε}, 2^ε]` of `ν_ε`. -/
theorem rpow_le_of_mem {u β : ℝ} (hu : u ∈ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε)) :
    u ^ β ≤ 2 ^ (ε * |β|) := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
  have hl := EF.abs_log_le_of_mem hu
  rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log u * β ≤ |Real.log u| * |β| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h2 : |Real.log u| * |β| ≤ ε * Real.log 2 * |β| :=
    mul_le_mul_of_nonneg_right hl (abs_nonneg _)
  have e : ε * Real.log 2 * |β| = Real.log 2 * (ε * |β|) := by ring
  linarith

/-- **`∫₀^∞ ν_ε(u) u^{β−1} du ≤ 2^{ε|β|}`**, in the shape the Tonelli step produces. -/
theorem lint_spike_le (hν : EF.MollData ν) (hε : 0 < ε) (β : ℝ) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ β) * ENNReal.ofReal u ≤
      ENNReal.ofReal (2 ^ (ε * |β|)) := by
  have hg0 := spike_nonneg hν hε
  have hgm := (spike_cont hν hε).measurable
  have h1 : ∀ u ∈ Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ β) *
      ENNReal.ofReal u ≤
        ENNReal.ofReal (2 ^ (ε * |β|)) * ENNReal.ofReal (DeltaSpike ν ε u / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hgu : 0 ≤ DeltaSpike ν ε u / u := div_nonneg (hg0 u) hu0.le
    have hA : 0 ≤ DeltaSpike ν ε u / u ^ 2 * u ^ β :=
      mul_nonneg (div_nonneg (hg0 u) (by positivity)) (Real.rpow_nonneg hu0.le _)
    have hB : (0 : ℝ) ≤ 2 ^ (ε * |β|) := by positivity
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB]
    apply ENNReal.ofReal_le_ofReal
    have e : DeltaSpike ν ε u / u ^ 2 * u ^ β * u = u ^ β * (DeltaSpike ν ε u / u) := by
      field_simp
    rw [e]
    by_cases h0 : DeltaSpike ν ε u = 0
    · rw [h0, zero_div, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right
        (rpow_le_of_mem (DeltaSpikeSupport' hε hu0.le hν.2.2.1 h0)) hgu
  calc ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ β) * ENNReal.ofReal u
      ≤ ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (2 ^ (ε * |β|)) *
          ENNReal.ofReal (DeltaSpike ν ε u / u) := setLIntegral_mono' measurableSet_Ioi h1
    _ = ENNReal.ofReal (2 ^ (ε * |β|)) *
          ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u) :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hgm.div measurable_id))
    _ = ENNReal.ofReal (2 ^ (ε * |β|)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (EF.integrable_spike_div hν hε)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
            div_nonneg (hg0 u) (le_of_lt hu))), DeltaSpikeMass hν.2.2.2 hε, ENNReal.ofReal_one,
          mul_one]

/-! ## The norms of `η₂'` -/

/-- `|e2d v|·v^α ≤ 4 v^{α−1}` for `v > 0`. -/
theorem abs_e2d_mul_le {v : ℝ} (hv : 0 < v) (α : ℝ) : |e2d v| * v ^ α ≤ 4 * v ^ (α - 1) := by
  rw [Real.rpow_sub_one hv.ne']
  calc |e2d v| * v ^ α ≤ 4 / v * v ^ α :=
        mul_le_mul_of_nonneg_right (abs_e2d_le hv) (Real.rpow_nonneg hv.le _)
    _ = 4 * (v ^ α / v) := by ring

/-- A function on `(0, ∞)` dominated by `c t^r` on `(1/4, 1]` and `0` elsewhere. -/
theorem lint_Ioc_le {ψ : ℝ → ℝ≥0∞} {c r : ℝ}
    (h1 : ∀ v, v ∈ Ioc (1 / 4 : ℝ) 1 → ψ v ≤ ENNReal.ofReal (c * v ^ r))
    (h2 : ∀ v, 0 < v → v ∉ Ioc (1 / 4 : ℝ) 1 → ψ v = 0) :
    ∫⁻ v in Ioi (0 : ℝ), ψ v ≤ ∫⁻ v in Ioc (1 / 4 : ℝ) 1, ENNReal.ofReal (c * v ^ r) := by
  calc ∫⁻ v in Ioi (0 : ℝ), ψ v ≤ ∫⁻ v in Ioi (0 : ℝ),
        (Ioc (1 / 4 : ℝ) 1).indicator (fun v => ENNReal.ofReal (c * v ^ r)) v := by
        refine setLIntegral_mono' measurableSet_Ioi fun v hv => ?_
        by_cases hm : v ∈ Ioc (1 / 4 : ℝ) 1
        · rw [indicator_of_mem hm]
          exact h1 v hm
        · rw [h2 v hv hm]
          exact zero_le
    _ ≤ ∫⁻ v, (Ioc (1 / 4 : ℝ) 1).indicator (fun v => ENNReal.ofReal (c * v ^ r)) v :=
        setLIntegral_le_lintegral _ _
    _ = _ := lintegral_indicator measurableSet_Ioc _

/-- `∫_{1/4}^1 c t^r dt` (`r ≠ −1`). -/
theorem lint_rpow (c r : ℝ) (hc : 0 ≤ c) (hr : r ≠ -1) :
    ∫⁻ v in Ioc (1 / 4 : ℝ) 1, ENNReal.ofReal (c * v ^ r) =
      ENNReal.ofReal (c * (((1 : ℝ) ^ (r + 1) - (1 / 4 : ℝ) ^ (r + 1)) / (r + 1))) := by
  have hcont : ContinuousOn (fun v : ℝ => c * v ^ r) (Icc (1 / 4) 1) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun v hv =>
      Or.inl (ne_of_gt (by linarith [hv.1] : (0 : ℝ) < v)))
  have hint : IntegrableOn (fun v : ℝ => c * v ^ r) (Ioc (1 / 4) 1) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hcont).mono_set Ioc_subset_Icc_self
  have h0 : (0 : ℝ) ∉ uIcc (1 / 4) 1 := fun h => by
    rw [uIcc_of_le (by norm_num)] at h
    linarith [h.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).mpr
    (Eventually.of_forall fun v hv => mul_nonneg hc (Real.rpow_nonneg (by linarith [hv.1]) _))),
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨hr, h0⟩)]

theorem quarter_rpow_half : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
  rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- `∫₀^∞ |η₂'(v)| v^{−1/2} dv ≤ 8`. -/
theorem psi1_le :
    ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (|e2d v| * v ^ (-1 / 2 : ℝ)) ≤ ENNReal.ofReal 8 := by
  refine (lint_Ioc_le (c := 4) (r := -1 / 2 - 1) (fun v hv => ENNReal.ofReal_le_ofReal
    (abs_e2d_mul_le (by linarith [hv.1]) _)) (fun v _ hn => ?_)).trans (le_of_eq ?_)
  · rw [e2d_off (fun hm => hn ⟨hm.1, hm.2.le⟩), abs_zero, zero_mul, ENNReal.ofReal_zero]
  · rw [lint_rpow 4 (-1 / 2 - 1) (by norm_num) (by norm_num), sub_add_cancel, Real.one_rpow,
      show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num), quarter_rpow_half]
    norm_num

/-- `∫₀^∞ |η₂'(v)| v^{1/2} dv ≤ 4`. -/
theorem psi2_le :
    ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (|e2d v| * v ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal 4 := by
  refine (lint_Ioc_le (c := 4) (r := 1 / 2 - 1) (fun v hv => ENNReal.ofReal_le_ofReal
    (abs_e2d_mul_le (by linarith [hv.1]) _)) (fun v _ hn => ?_)).trans (le_of_eq ?_)
  · rw [e2d_off (fun hm => hn ⟨hm.1, hm.2.le⟩), abs_zero, zero_mul, ENNReal.ofReal_zero]
  · rw [lint_rpow 4 (1 / 2 - 1) (by norm_num) (by norm_num), sub_add_cancel, Real.one_rpow,
      quarter_rpow_half]
    norm_num

/-- `∫₀^∞ η₂'(v)² dv ≤ 48`. -/
theorem psi3_le : ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (e2d v ^ 2) ≤ ENNReal.ofReal 48 := by
  refine (lint_Ioc_le (c := 16) (r := -2) (fun v hv => ENNReal.ofReal_le_ofReal ?_)
    (fun v _ hn => ?_)).trans (le_of_eq ?_)
  · have hv0 : 0 < v := by linarith [hv.1]
    have h := abs_e2d_le hv0
    have hs : e2d v ^ 2 ≤ (4 / v) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [Real.rpow_neg hv0.le, Real.rpow_two]
    calc e2d v ^ 2 ≤ (4 / v) ^ 2 := hs
      _ = 16 * (v ^ 2)⁻¹ := by ring
  · rw [e2d_off (fun hm => hn ⟨hm.1, hm.2.le⟩), ENNReal.ofReal_eq_zero]
    norm_num
  · rw [lint_rpow 16 (-2) (by norm_num) (by norm_num), show (-2 : ℝ) + 1 = -1 by norm_num,
      Real.one_rpow, Real.rpow_neg_one]
    norm_num

/-! ## Pointwise bounds on `D = (η₂ ∗_M ν_ε)'` -/

/-- **Weighted `L¹` pointwise**: `|D(x)| x^α ≤ ∫ ν_ε(u) u^{α−2} · |η₂'(x/u)| (x/u)^α du`. -/
theorem D_pt_le (hν : EF.MollData ν) (hε : 0 < ε) (α : ℝ) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (|Dfun ν ε x| * x ^ α) ≤ ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ α) *
        ENNReal.ofReal (|e2d (x / u)| * (x / u) ^ α) := by
  have hg0 := spike_nonneg hν hε
  rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]
  calc ‖Dfun ν ε x‖ₑ * ENNReal.ofReal (x ^ α)
      ≤ (∫⁻ u in Ioi (0 : ℝ), ‖DeltaSpike ν ε u * (e2d (x / u) / u) / u‖ₑ) *
          ENNReal.ofReal (x ^ α) := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ u in Ioi (0 : ℝ), ‖DeltaSpike ν ε u * (e2d (x / u) / u) / u‖ₑ *
          ENNReal.ofReal (x ^ α) := (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu0 : (0 : ℝ) < u := hu
        have hxu : 0 < x / u := div_pos hx hu0
        have hA : 0 ≤ DeltaSpike ν ε u / u ^ 2 * u ^ α :=
          mul_nonneg (div_nonneg (hg0 u) (by positivity)) (Real.rpow_nonneg hu0.le _)
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_mul hA]
        congr 1
        have hux : u * (x / u) = x := by field_simp
        have hx' : x ^ α = u ^ α * (x / u) ^ α := by
          rw [← Real.mul_rpow hu0.le hxu.le, hux]
        rw [hx', abs_div, abs_mul, abs_div, abs_of_nonneg (hg0 u), abs_of_pos hu0]
        ring

/-- **Cauchy–Schwarz against a probability density**: `(∫ p h)² ≤ ∫ p h²` when `p ≥ 0`,
`∫ p = 1` (from `2m|h| ≤ h² + m²` integrated against `p`). -/
theorem sq_integral_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {p h : X → ℝ}
    (hp : Integrable p μ) (hp0 : ∀ᵐ a ∂μ, 0 ≤ p a) (hp1 : ∫ a, p a ∂μ = 1)
    (h1 : Integrable (fun a => p a * h a) μ) (h2 : Integrable (fun a => p a * h a ^ 2) μ) :
    (∫ a, p a * h a ∂μ) ^ 2 ≤ ∫ a, p a * h a ^ 2 ∂μ := by
  set m := ∫ a, p a * h a ∂μ with hm
  have hle : ∫ a, 2 * m * (p a * h a) ∂μ ≤ ∫ a, (p a * h a ^ 2 + m ^ 2 * p a) ∂μ := by
    refine integral_mono_ae (h1.const_mul _) (h2.add (hp.const_mul _)) ?_
    filter_upwards [hp0] with a ha
    nlinarith [mul_nonneg ha (sq_nonneg (h a - m))]
  rw [integral_const_mul, integral_add h2 (hp.const_mul _), integral_const_mul, hp1, ← hm]
    at hle
  nlinarith

/-- **`L²` pointwise**: `D(x)² ≤ ∫ ν_ε(u) u^{−3} η₂'(x/u)² du` (Cauchy–Schwarz against the
probability density `ν_ε(u)/u`). -/
theorem D_sq_le (hν : EF.MollData ν) (hε : 0 < ε) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (Dfun ν ε x ^ 2) ≤ ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ (-1 : ℝ)) *
        ENNReal.ofReal (e2d (x / u) ^ 2) := by
  have hg0 := spike_nonneg hν hε
  have hgm := (spike_cont hν hε).measurable
  have hp := EF.integrable_spike_div hν hε
  have hhm : Measurable (fun u : ℝ => e2d (x / u) / u) :=
    (measurable_e2d.comp (measurable_const.div measurable_id)).div measurable_id
  have hb : ∀ u ∈ Ioi (0 : ℝ), |e2d (x / u) / u| ≤ 4 / x := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [abs_div, abs_of_pos hu0]
    calc |e2d (x / u)| / u ≤ 4 / (x / u) / u := by
          gcongr
          exact abs_e2d_le (div_pos hx hu0)
      _ = 4 / x := by field_simp
  have h1 : Integrable (fun u => DeltaSpike ν ε u / u * (e2d (x / u) / u))
      (volume.restrict (Ioi 0)) := by
    refine (hp.mul_const (4 / x)).mono' ((hgm.div measurable_id).mul hhm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (hg0 u) hu0.le)]
    exact mul_le_mul_of_nonneg_left (hb u hu) (div_nonneg (hg0 u) hu0.le)
  have h2 : Integrable (fun u => DeltaSpike ν ε u / u * (e2d (x / u) / u) ^ 2)
      (volume.restrict (Ioi 0)) := by
    refine (hp.mul_const ((4 / x) ^ 2)).mono'
      ((hgm.div measurable_id).mul (hhm.pow_const 2)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (hg0 u) hu0.le), abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hb u hu) 2)
      (div_nonneg (hg0 u) hu0.le)
  have hp0 : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ DeltaSpike ν ε u / u :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => div_nonneg (hg0 u) (le_of_lt hu))
  have hcs := sq_integral_le hp hp0 (DeltaSpikeMass hν.2.2.2 hε) h1 h2
  have hD : Dfun ν ε x = ∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u / u * (e2d (x / u) / u) := by
    unfold Dfun
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [hD]
  calc ENNReal.ofReal ((∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u / u * (e2d (x / u) / u)) ^ 2)
      ≤ ENNReal.ofReal (∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u / u * (e2d (x / u) / u) ^ 2) :=
        ENNReal.ofReal_le_ofReal hcs
    _ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u * (e2d (x / u) / u) ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal h2 ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun u hu =>
            mul_nonneg (div_nonneg (hg0 u) (le_of_lt hu)) (sq_nonneg _)))
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu0 : (0 : ℝ) < u := hu
        have hA : 0 ≤ DeltaSpike ν ε u / u ^ 2 * u ^ (-1 : ℝ) :=
          mul_nonneg (div_nonneg (hg0 u) (by positivity)) (Real.rpow_nonneg hu0.le _)
        rw [← ENNReal.ofReal_mul hA, Real.rpow_neg_one]
        congr 1
        ring

/-! ## The integrated bounds -/

/-- **`∫₀^∞ |D(x)| x^α dx ≤ 2^{ε|α|} · ∫₀^∞ |η₂'(v)| v^α dv`** (Tonelli + scaling). -/
theorem lint_D_le (hν : EF.MollData ν) (hε : 0 < ε) (α : ℝ) {K : ℝ}
    (hK : ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (|e2d v| * v ^ α) ≤ ENNReal.ofReal K) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (|Dfun ν ε x| * x ^ α) ≤
      ENNReal.ofReal (2 ^ (ε * |α|)) * ENNReal.ofReal K := by
  have hgm := (spike_cont hν hε).measurable
  have hφ : Measurable fun u : ℝ => ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ α) :=
    ENNReal.measurable_ofReal.comp ((hgm.div (measurable_id.pow_const 2)).mul
      (measurable_id.pow_const α))
  have hψ : Measurable fun v : ℝ => ENNReal.ofReal (|e2d v| * v ^ α) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp measurable_e2d).mul
      (measurable_id.pow_const α))
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (|Dfun ν ε x| * x ^ α)
      ≤ ∫⁻ x in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ α) *
            ENNReal.ofReal (|e2d (x / u)| * (x / u) ^ α) :=
        setLIntegral_mono' measurableSet_Ioi fun x hx => D_pt_le hν hε α hx
    _ = (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ α) *
          ENNReal.ofReal u) * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (|e2d v| * v ^ α) :=
        tonelli_div hφ hψ
    _ ≤ ENNReal.ofReal (2 ^ (ε * |α|)) * ENNReal.ofReal K :=
        mul_le_mul' (lint_spike_le hν hε α) hK

/-- **`∫₀^∞ D(x)² dx ≤ 48 · 2^ε`** (pointwise Cauchy–Schwarz + Tonelli + scaling). -/
theorem lint_Dsq_le (hν : EF.MollData ν) (hε : 0 < ε) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Dfun ν ε x ^ 2) ≤
      ENNReal.ofReal (2 ^ ε) * ENNReal.ofReal 48 := by
  have hgm := (spike_cont hν hε).measurable
  have hφ : Measurable fun u : ℝ => ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ (-1 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((hgm.div (measurable_id.pow_const 2)).mul
      (measurable_id.pow_const (-1 : ℝ)))
  have hψ : Measurable fun v : ℝ => ENNReal.ofReal (e2d v ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_e2d.pow_const 2)
  have hs := lint_spike_le hν hε (-1)
  rw [abs_neg, abs_one, mul_one] at hs
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Dfun ν ε x ^ 2)
      ≤ ∫⁻ x in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ (-1 : ℝ)) *
            ENNReal.ofReal (e2d (x / u) ^ 2) :=
        setLIntegral_mono' measurableSet_Ioi fun x hx => D_sq_le hν hε hx
    _ = (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (DeltaSpike ν ε u / u ^ 2 * u ^ (-1 : ℝ)) *
          ENNReal.ofReal u) * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (e2d v ^ 2) :=
        tonelli_div hφ hψ
    _ ≤ ENNReal.ofReal (2 ^ ε) * ENNReal.ofReal 48 := mul_le_mul' hs psi3_le

/-- **LINK `EF.Eta2Norms` — PROVED**: `c₀(η₂ ∗_M ν_ε, 0) ≤ 8·2^{ε/2} ≤ 8(1 + ε)` and
`|(η₂ ∗_M ν_ε)'|₂ ≤ √(48·2^ε) ≤ 7(1 + ε)`. -/
theorem eta2Norms_holds : EF.Eta2Norms := by
  intro ν hν ε hε0 hε1
  have hD : ∀ t ∈ Ioi (0 : ℝ), deriv (EF.eta2e ν ε) t = Dfun ν ε t :=
    fun t ht => (hasDerivAt_eta2e hν hε0 ht).deriv
  have hDc := continuousOn_D hν hε0
  have hmD : ∀ β : ℝ, AEStronglyMeasurable (fun t => |Dfun ν ε t| * t ^ β)
      (volume.restrict (Ioi 0)) := fun β =>
    (hDc.abs.mul (continuousOn_id.rpow_const fun t ht =>
      Or.inl (ne_of_gt ht))).aestronglyMeasurable measurableSet_Ioi
  have hnn : ∀ β : ℝ, 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => |Dfun ν ε t| * t ^ β :=
    fun β => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _))
  have h1 : HM.n1h (deriv (EF.eta2e ν ε)) ≤ 2 ^ (ε / 2) * 8 := by
    have e : HM.n1h (deriv (EF.eta2e ν ε)) =
        ∫ t in Ioi (0 : ℝ), |Dfun ν ε t| * t ^ (-1 / 2 : ℝ) := by
      unfold HM.n1h
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := ht
      rw [hD t ht, Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
        Real.rpow_neg ht0.le, div_eq_mul_inv]
    have ha : ε * |(-1 / 2 : ℝ)| = ε / 2 := by
      rw [abs_of_neg (by norm_num)]
      ring
    rw [e, integral_eq_lintegral_of_nonneg_ae (hnn _) (hmD _)]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (lint_D_le hν hε0 (-1 / 2) psi1_le).trans (le_of_eq ?_)
    rw [ha, ← ENNReal.ofReal_mul (by positivity)]
  have h2 : HM.n1s (deriv (EF.eta2e ν ε)) ≤ 2 ^ (ε / 2) * 4 := by
    have e : HM.n1s (deriv (EF.eta2e ν ε)) =
        ∫ t in Ioi (0 : ℝ), |Dfun ν ε t| * t ^ (1 / 2 : ℝ) := by
      unfold HM.n1s
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [hD t ht, Real.sqrt_eq_rpow]
    have ha : ε * |(1 / 2 : ℝ)| = ε / 2 := by
      rw [abs_of_pos (by norm_num)]
      ring
    rw [e, integral_eq_lintegral_of_nonneg_ae (hnn _) (hmD _)]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (lint_D_le hν hε0 (1 / 2) psi2_le).trans (le_of_eq ?_)
    rw [ha, ← ENNReal.ofReal_mul (by positivity)]
  have hb2 := EF.two_rpow_le (u := ε / 2) (by positivity) (by linarith)
  have hc0 : HM.c0 (EF.eta2e ν ε) 0 ≤ 8 * (1 + ε) := by
    unfold HM.c0
    rw [abs_zero, mul_zero, zero_mul, add_zero]
    linarith
  have hl2 : MajSp.l2 (deriv (EF.eta2e ν ε)) ≤ 7 * (1 + ε) := by
    have e : ∫ t in Ioi (0 : ℝ), deriv (EF.eta2e ν ε) t ^ 2 =
        ∫ t in Ioi (0 : ℝ), Dfun ν ε t ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hD t ht]
    have hI : ∫ t in Ioi (0 : ℝ), Dfun ν ε t ^ 2 ≤ 2 ^ ε * 48 := by
      rw [integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t _ => sq_nonneg _))
        ((hDc.pow 2).aestronglyMeasurable measurableSet_Ioi)]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      rw [ENNReal.ofReal_mul (by positivity)]
      exact lint_Dsq_le hν hε0
    have hb := EF.two_rpow_le hε0.le hε1
    unfold MajSp.l2
    rw [e, Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) (by linarith : (0 : ℝ) ≤ 1 + 49 * ε)]
  exact ⟨hc0, hl2⟩

end Principia.Common.TernaryGoldbach.E2
