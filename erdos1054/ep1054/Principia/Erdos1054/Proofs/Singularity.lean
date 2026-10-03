/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Metrizable.Real
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false

/-!
# EP1054 §7: every subsequential law is singular; heavy tails (the `Singularity` package)

Discharges eighteen obligations of `Principia.Erdos1054.Spine` for
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 2835–3026 (`thm:dadd:universal-singularity`,
its proof steps, and the heavy-tail corollary with its proof steps).

Leaves (from the definitions, `Basic` and Mathlib alone):
* `leaf_Step_DaddWitnessDomination`, `leaf_Step_DaddCountDomination` — the minimal witness
  `f(N) = ed` (`f_mem_Fform`) is one of the Dirac masses of `𝒲_X` (lines 2904–2909, 2918–2924).

Links (from exactly the dependencies the spine names):
* `link_Step_DaddSingularCarrier` — Erdős singularity + inner regularity
  (`MeasurableSet.exists_isCompact_lt_add`).
* `link_Step_DaddWitnessCarrier` — `ν_{a,e} ≤ 𝒟`; `h ↦ 1/(h − c)` is differentiable off `c`, so
  it maps null sets to null sets (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`).
* `link_Step_DaddEmpiricalWitnessVague` — `𝒲_X([0,t]) = (1/X)∑ r_t(N)` exactly; the restrictions
  to `[0, c]` converge as finite measures by the π-system criterion on the intervals `[0,t]`,
  `(u,t]` (`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`, after normalising masses).
* `link_Step_DaddLimitDomination` — open sets by Urysohn bumps and inner regularity of `ν`; Borel
  sets by outer regularity of `𝒲` on the open region where `𝒲` is locally finite. On the rest of
  `(0, ∞)` `ν` vanishes: there a bump `φ` has `∫⁻ φ d𝒲 = ∞`, so the Bochner integral in
  `Step_DaddEmpiricalWitnessVague` is `0` and forces `∫ φ dν ≤ 0`. (The paper instead uses that
  `𝒲` is locally finite, `Step_DaddWitnessMeasureMass`, which this link does not list; in the
  real situation that region is empty.)
* `link_Thm_DaddUniversalSingularity_Carrier`, `_FinitePart`, `_Tight` — portmanteau in both
  directions on `[0, ∞]` (`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`,
  `…limsup_measure_closed_le_of_tendsto`; `ℝ≥0∞` is metrizable).
* `link_Step_DaddXoverR`, `link_Step_DaddLowerTailUniform`, `link_Eq_DaddSubsequentialTail`,
  `link_Cor_DaddHeavyTails_{PosMoments, LogMeans, InvMoments, InvMomentConv, GeomMean, Tight}` —
  discrete layer cakes: `log⁻ x ≤ #{j : x < e^{-j}}`, `x^{-s} ≤ 1 + e^s ∑_j e^{sj} 1[x < e^{-j}]`,
  and `∑_{k<K} (e^{k+1} − e^k) 1[x > exp(e^{k+1})] ≤ log⁺ x` (whose weights against
  `L(exp(e^{k+1}))` are `(1 − e^{-1}) log(k+1)/(k+1)`, a divergent series).

The helper `nuX_isProb` (`ν_X` is a probability measure for `X ≥ 1`) is the definitional fact
`EmpiricalMeasures_isProbability`; it is re-proved here, not taken from another package.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Principia.Erdos1054.Proofs.Singularity

open Principia.Erdos1054 Principia.Erdos1054.Limits

/-! ## The empirical measures `ν_X` and `𝒲_X` -/

/-- `1 ∈ 𝓡` (`1 = F_1(1)`). -/
theorem one_mem_R : (1 : ℕ) ∈ R := (mem_R_iff_exists_F 1).2 ⟨1, 1, le_rfl, le_rfl, by decide⟩

/-- `R(X) ≥ 1` for `X ≥ 1`. -/
theorem one_le_Rcnt {X : ℝ} (hX : 1 ≤ X) : 1 ≤ Rcnt X := by
  have h1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  show 1 ≤ cnt R X
  unfold cnt
  exact Finset.card_pos.2 ⟨1, mem_cntFinset.2 ⟨⟨le_rfl, h1⟩, one_mem_R⟩⟩

/-- `R(X) ≤ X` for `X ≥ 0`. -/
theorem Rcnt_le {X : ℝ} (hX : 0 ≤ X) : (Rcnt X : ℝ) ≤ X :=
  (Nat.cast_le.2 (cnt_le_floor R X)).trans (Nat.floor_le hX)

/-- `f N ≥ 1` on `𝓡`. -/
theorem one_le_f {N : ℕ} (hN : N ∈ R) : 1 ≤ f N := by
  obtain ⟨e, d, he, hd, hf, _⟩ := f_mem_Fform N hN
  rw [hf]
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

/-- `N ≥ 1` on `𝓡`. -/
theorem one_le_of_mem_R {N : ℕ} (hN : N ∈ R) : 1 ≤ N := by
  obtain ⟨e, d, he, hd, hF⟩ := (mem_R_iff_exists_F N).1 hN
  rw [hF]
  exact le_trans hd (F_ge e d he hd)

/-- `ν_X` is a probability measure for `X ≥ 1`. -/
theorem nuX_isProb {X : ℝ} (hX : 1 ≤ X) : IsProbabilityMeasure (nuX X) := by
  constructor
  rw [nuX, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  change (Rcnt X : ℝ≥0∞)⁻¹ * (Rcnt X : ℝ≥0∞) = 1
  have h1 := one_le_Rcnt hX
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : Rcnt X ≠ 0))
    (ENNReal.natCast_ne_top _)

open Classical in
/-- `ν_X(s) = R(X)⁻¹ · #{N ≤ X : N ∈ 𝓡, f(N)/N ∈ s}`. -/
theorem nuX_apply (X : ℝ) (s : Set ℝ≥0∞) :
    nuX X s = (Rcnt X : ℝ≥0∞)⁻¹ * (cnt {N : ℕ | N ∈ R ∧ ratioE N ∈ s} X : ℝ≥0∞) := by
  rw [nuX, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  simp only [Measure.dirac_apply]
  unfold cnt
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  by_cases h1 : N ∈ R <;> by_cases h2 : ratioE N ∈ s <;>
    simp [Set.indicator, h1, h2]

open Classical in
/-- The lower Lebesgue integral against `ν_X`. -/
theorem lintegral_nuX (X : ℝ) (g : ℝ≥0∞ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(nuX X) =
      (Rcnt X : ℝ≥0∞)⁻¹ * ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), g (ratioE N) := by
  rw [nuX, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
  simp only [lintegral_dirac]

open Classical in
/-- The Bochner integral against `ν_X`. -/
theorem integral_nuX (X : ℝ) (φ : ℝ≥0∞ → ℝ) :
    ∫ x, φ x ∂(nuX X) =
      (Rcnt X : ℝ)⁻¹ * ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), φ (ratioE N) := by
  rw [nuX, integral_smul_measure, integral_finsetSum_measure
    (fun N _ => integrable_dirac enorm_lt_top), smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  simp only [integral_dirac]

/-- Every measurable real function is `ν_X`-integrable (finitely many atoms). -/
theorem integrable_nuX {X : ℝ} (hX : 1 ≤ X) {φ : ℝ≥0∞ → ℝ} (hφ : Measurable φ) :
    Integrable φ (nuX X) := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖φ x‖ₑ ∂(nuX X) < ⊤
  rw [lintegral_nuX]
  have hR : (Rcnt X : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by have := one_le_Rcnt hX; omega)
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hR))
    (ENNReal.sum_lt_top.2 (fun N _ => enorm_lt_top))

/-- The lower Lebesgue integral against `𝒲_X`. -/
theorem lintegral_empWitness (X : ℝ) (g : ℝ≥0∞ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(empWitness X) =
      ENNReal.ofReal (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ∑' p : ℕ × ℕ,
        (if 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ F p.1 p.2 = N then
          g (ENNReal.ofReal (((p.1 * p.2 : ℕ) : ℝ) / (N : ℝ))) else 0) := by
  rw [empWitness, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [lintegral_sum_measure]
  refine tsum_congr (fun p => ?_)
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _

/-- `(X / R(X)) · (1/X) = R(X)⁻¹` in `ℝ≥0∞`. -/
theorem ofReal_ratio_mul {X : ℝ} (hX : 1 ≤ X) :
    ENNReal.ofReal (X / (Rcnt X : ℝ)) * ENNReal.ofReal (1 / X) = (Rcnt X : ℝ≥0∞)⁻¹ := by
  have hXpos : 0 < X := by linarith
  have hR : (0 : ℝ) < Rcnt X := by exact_mod_cast one_le_Rcnt hX
  rw [← ENNReal.ofReal_mul (div_nonneg hXpos.le hR.le)]
  have : X / (Rcnt X : ℝ) * (1 / X) = (Rcnt X : ℝ)⁻¹ := by
    field_simp
  rw [this, ENNReal.ofReal_inv_of_pos hR, ENNReal.ofReal_natCast]

open Classical in
/-- **Minimal-witness domination** for an arbitrary `[0, ∞]`-valued test function. -/
theorem lintegral_nuX_le (g : ℝ≥0∞ → ℝ≥0∞) {X : ℝ} (hX : 1 ≤ X) :
    ∫⁻ x, g x ∂(nuX X) ≤
      ENNReal.ofReal (X / (Rcnt X : ℝ)) * ∫⁻ x, g x ∂(empWitness X) := by
  rw [lintegral_nuX, lintegral_empWitness, ← mul_assoc, ofReal_ratio_mul hX]
  gcongr
  calc ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), g (ratioE N)
      ≤ ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), ∑' p : ℕ × ℕ,
          (if 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ F p.1 p.2 = N then
            g (ENNReal.ofReal (((p.1 * p.2 : ℕ) : ℝ) / (N : ℝ))) else 0) := by
        refine Finset.sum_le_sum (fun N hN => ?_)
        have hNR : N ∈ R := (Finset.mem_filter.1 hN).2
        obtain ⟨e, d, he, hd, hf, hF⟩ := f_mem_Fform N hNR
        refine le_trans ?_ (ENNReal.le_tsum (e, d))
        rw [if_pos ⟨he, hd, hF.symm⟩, ratioE, hf]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- `ν_X([0, δ]) = #{N ≤ X : N ∈ 𝓡, f(N) ≤ δN} / R(X)` for `δ > 0`, `X ≥ 1`. -/
theorem nuX_Iic (X : ℝ) (hX : 1 ≤ X) {δ : ℝ} (hδ : 0 < δ) :
    nuX X (Set.Iic (ENNReal.ofReal δ)) =
      ENNReal.ofReal ((cnt (smallRatioSet δ) X : ℝ) / Rcnt X) := by
  have hset : {N : ℕ | N ∈ R ∧ ratioE N ∈ Set.Iic (ENNReal.ofReal δ)} = smallRatioSet δ := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_Iic, smallRatioSet, ratioE]
    constructor
    · rintro ⟨hN, h⟩
      refine ⟨hN, ?_⟩
      have hNpos : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hN
      rw [ENNReal.ofReal_le_ofReal_iff hδ.le, div_le_iff₀ hNpos] at h
      exact h
    · rintro ⟨hN, h⟩
      refine ⟨hN, ?_⟩
      have hNpos : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hN
      rw [ENNReal.ofReal_le_ofReal_iff hδ.le, div_le_iff₀ hNpos]
      exact h
  have hR : (0 : ℝ) < Rcnt X := by exact_mod_cast one_le_Rcnt hX
  rw [nuX_apply, hset, ENNReal.ofReal_div_of_pos hR, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

/-- `ν_X(s) ≥ #(S ∩ [1, X])/X` for any `S` of represented targets with ratio in `s`. -/
theorem ofReal_cnt_div_le_nuX {X : ℝ} (hX : 1 ≤ X) {S : Set ℕ} {s : Set ℝ≥0∞}
    (hS : ∀ N ∈ S, N ∈ R ∧ ratioE N ∈ s) :
    ENNReal.ofReal ((cnt S X : ℝ) / X) ≤ nuX X s := by
  have hX0 : 0 < X := by linarith
  rw [nuX_apply, ENNReal.ofReal_div_of_pos hX0, ENNReal.ofReal_natCast, div_eq_mul_inv,
    mul_comm]
  refine mul_le_mul' ?_ ?_
  · rw [ENNReal.inv_le_inv, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Rcnt_le hX0.le)
  · exact_mod_cast cnt_mono (fun N hN => hS N hN) X

/-- The large-ratio targets of `thm:almost-log-tail` have ratio in `(T, ∞]`. -/
theorem largeSet_sub {T : ℝ} (hT : 0 ≤ T) :
    ∀ N ∈ {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * N < (f N : ℝ)},
      N ∈ R ∧ ratioE N ∈ Set.Ioi (ENNReal.ofReal T) := by
  rintro N ⟨hN, _, hlt⟩
  refine ⟨hN, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hN
  have h1 : T < (f N : ℝ) / N := by rw [lt_div_iff₀ hNpos]; exact hlt
  show ENNReal.ofReal T < ENNReal.ofReal ((f N : ℝ) / N)
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hT h1)).2 h1

/-- The large-ratio targets have ratio in `(T, ∞)`. -/
theorem largeSet_sub_Ioo {T : ℝ} (hT : 0 ≤ T) :
    ∀ N ∈ {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * N < (f N : ℝ)},
      N ∈ R ∧ ratioE N ∈ Set.Ioo (ENNReal.ofReal T) ⊤ := by
  rintro N ⟨hN, _, hlt⟩
  refine ⟨hN, ?_, ENNReal.ofReal_lt_top⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hN
  have h1 : T < (f N : ℝ) / N := by rw [lt_div_iff₀ hNpos]; exact hlt
  show ENNReal.ofReal T < ENNReal.ofReal ((f N : ℝ) / N)
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hT h1)).2 h1

/-- `R(X)/X → 1`, from `R(X) = ⌊X⌋ − 2` (`X ≥ 5`). -/
theorem tendsto_Rcnt_div (hRF : Intro_RcntFormula) :
    Tendsto (fun X : ℝ => (Rcnt X : ℝ) / X) atTop (𝓝 1) := by
  have h1 : Tendsto (fun X : ℝ => (⌊X⌋₊ : ℝ) / X - 2 / X) atTop (𝓝 (1 - 0)) :=
    tendsto_nat_floor_div_atTop.sub (tendsto_const_nhds.div_atTop tendsto_id)
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (5 : ℝ)] with X hX
  rw [hRF X hX]
  have h5 : 5 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [Nat.cast_sub (by omega), sub_div]
  norm_num

/-- `X/R(X) → 1`. -/
theorem tendsto_X_div_Rcnt (hRF : Intro_RcntFormula) :
    Tendsto (fun X : ℝ => X / (Rcnt X : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_Rcnt_div hRF).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X _
  rw [inv_div]

/-! ## Weak convergence on `[0, ∞]` -/

/-- **Portmanteau along `X_j`.** A weak limit `ν` of `ν_{X_j}` (in the sense of `WeakConvAlong`)
satisfies the open-set and closed-set inequalities. -/
theorem portmanteau {ν : Measure ℝ≥0∞} [IsProbabilityMeasure ν] {X : ℕ → ℝ}
    (hW : WeakConvAlong X ν) :
    (∀ G : Set ℝ≥0∞, IsOpen G → ν G ≤ liminf (fun j => nuX (X j) G) atTop) ∧
    (∀ F : Set ℝ≥0∞, IsClosed F → limsup (fun j => nuX (X j) F) atTop ≤ ν F) := by
  let μs : ℕ → ProbabilityMeasure ℝ≥0∞ :=
    fun j => ⟨nuX (max (X j) 1), nuX_isProb (le_max_right _ _)⟩
  let μ : ProbabilityMeasure ℝ≥0∞ := ⟨ν, inferInstance⟩
  have hev : ∀ᶠ j in atTop, max (X j) 1 = X j :=
    (hW.1.eventually_ge_atTop 1).mono (fun j hj => max_eq_left hj)
  have hcoe : ∀ j, (μs j : Measure ℝ≥0∞) = nuX (max (X j) 1) := fun j => rfl
  have hlim : Tendsto μs atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    refine (hW.2 f).congr' ?_
    filter_upwards [hev] with j hj
    rw [hcoe, hj]
  refine ⟨fun G hG => ?_, fun F hF => ?_⟩
  · have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
    refine h.trans (le_of_eq (liminf_congr ?_))
    filter_upwards [hev] with j hj
    rw [hcoe, hj]
  · have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
    refine le_trans (le_of_eq (limsup_congr ?_)) h
    filter_upwards [hev] with j hj
    rw [hcoe, hj]

/-- `ν_{max(Y,1)}` as a `ProbabilityMeasure`. -/
noncomputable def nuXP (Y : ℝ) : ProbabilityMeasure ℝ≥0∞ :=
  ⟨nuX (max Y 1), nuX_isProb (le_max_right _ _)⟩

/-- A probability measure on `[0, ∞]` as a `ProbabilityMeasure`. -/
noncomputable def toPM (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] : ProbabilityMeasure ℝ≥0∞ :=
  ⟨ν, inferInstance⟩

/-- `ν_{X_j} → ν` as probability measures (the paper's weak convergence, in Mathlib's form). -/
theorem weak_tendsto {ν : Measure ℝ≥0∞} [IsProbabilityMeasure ν] {X : ℕ → ℝ}
    (hW : WeakConvAlong X ν) :
    Tendsto (fun j => nuXP (X j)) atTop (𝓝 (toPM ν)) := by
  have hev : ∀ᶠ j in atTop, max (X j) 1 = X j :=
    (hW.1.eventually_ge_atTop 1).mono (fun j hj => max_eq_left hj)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  refine (hW.2 f).congr' ?_
  filter_upwards [hev] with j hj
  show ∫ x, f x ∂(nuX (X j)) = ∫ x, f x ∂(nuX (max (X j) 1))
  rw [hj]

/-- Weak convergence tested against bounded continuous `ℝ≥0`-valued functions. -/
theorem weak_lintegral {ν : Measure ℝ≥0∞} [IsProbabilityMeasure ν] {X : ℕ → ℝ}
    (hW : WeakConvAlong X ν) (f : ℝ≥0∞ →ᵇ ℝ≥0) :
    Tendsto (fun j => ∫⁻ x, (f x : ℝ≥0∞) ∂(nuX (X j))) atTop (𝓝 (∫⁻ x, (f x : ℝ≥0∞) ∂ν)) := by
  have hev : ∀ᶠ j in atTop, max (X j) 1 = X j :=
    (hW.1.eventually_ge_atTop 1).mono (fun j hj => max_eq_left hj)
  have h := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 (weak_tendsto hW) f
  refine h.congr' ?_
  filter_upwards [hev] with j hj
  show ∫⁻ x, (f x : ℝ≥0∞) ∂(nuX (max (X j) 1)) = ∫⁻ x, (f x : ℝ≥0∞) ∂(nuX (X j))
  rw [hj]

/-- `finitePart ν s = ν({x ≠ ∞} ∩ toReal⁻¹ s)` on measurable `s`. -/
theorem finitePart_apply (ν : Measure ℝ≥0∞) {s : Set ℝ} (hs : MeasurableSet s) :
    finitePart ν s = ν ({⊤}ᶜ ∩ ENNReal.toReal ⁻¹' s) := by
  rw [finitePart, Measure.map_apply ENNReal.measurable_toReal hs,
    Measure.restrict_apply (ENNReal.measurable_toReal hs), Set.inter_comm]

/-! ## Carriers -/

/-- σ-compact subsets of `ℝ` are measurable. -/
theorem IsSigmaCompact.measurableSet' {Z : Set ℝ} (hZ : IsSigmaCompact Z) : MeasurableSet Z := by
  obtain ⟨K, hK, rfl⟩ := hZ
  exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)

/-- A σ-compact set meets a closed set in a σ-compact set. -/
theorem IsSigmaCompact.inter_isClosed' {s t : Set ℝ} (hs : IsSigmaCompact s) (ht : IsClosed t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, rfl⟩ := hs
  refine ⟨fun n => K n ∩ t, fun n => (hK n).inter_right ht, ?_⟩
  rw [Set.iUnion_inter]

/-- `σ(n)/n ≥ 1` for `n ≥ 1`. -/
theorem one_le_abundancy {n : ℕ} (hn : 1 ≤ n) : 1 ≤ abundancy n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h : n ≤ sig n := by
    show n ≤ ArithmeticFunction.sigma 1 n
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le i)
      (Nat.mem_divisors_self n (by omega))
  rw [abundancy, le_div_iff₀ hnpos, one_mul]
  exact_mod_cast h

/-- The Davenport law gives no mass to `(-∞, 1)`. -/
theorem davenport_Iio_one {D : Measure ℝ} [IsFiniteMeasure D]
    (hdens : ∀ u : ℝ, HasDens {n : ℕ | abundancy n ≤ u} (D.real (Set.Iic u))) :
    D (Set.Iio 1) = 0 := by
  have hIic : ∀ u : ℝ, u < 1 → D (Set.Iic u) = 0 := by
    intro u hu
    have hsub : {n : ℕ | abundancy n ≤ u} ⊆ {0} := by
      intro n hn
      by_contra h0
      have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 h0
      have := one_le_abundancy h1
      have hn' : abundancy n ≤ u := hn
      linarith
    have h0 : HasDens {n : ℕ | abundancy n ≤ u} 0 :=
      densZero_of_finite ((Set.finite_singleton 0).subset hsub)
    have := (hdens u).unique h0
    rwa [measureReal_eq_zero_iff] at this
  refine measure_mono_null (t := ⋃ n : ℕ, Set.Iic (1 - 1 / ((n : ℝ) + 1))) ?_
    (measure_iUnion_null (fun n => hIic _ (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)))
  intro x hx
  have hx1 : x < 1 := hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx1)
  exact Set.mem_iUnion.2 ⟨n, by show x ≤ 1 - 1 / ((n : ℝ) + 1); linarith⟩

/-- A point `1/(h - c)` of the carrier, for `h ∈ K`, `h > c`. -/
theorem mem_witnessCarrier {K : Set ℝ} {e' a : ℕ} (ha : a ∈ witnessResidues (e' + 1))
    {h : ℝ} (hK : h ∈ K) (hc : cRes (e' + 1) a < h) :
    1 / (h - cRes (e' + 1) a) ∈ witnessCarrier K := by
  set c := cRes (e' + 1) a with hcdef
  have hpos : 0 < h - c := sub_pos.2 hc
  set j' := ⌈h⌉₊ + ⌈1 / (h - c)⌉₊ with hj'
  have hj1 : h ≤ (⌈h⌉₊ : ℝ) := Nat.le_ceil _
  have hj2 : 1 / (h - c) ≤ (⌈1 / (h - c)⌉₊ : ℝ) := Nat.le_ceil _
  have hj0 : (0 : ℝ) ≤ (⌈h⌉₊ : ℝ) := Nat.cast_nonneg _
  have hj0' : (0 : ℝ) ≤ (⌈1 / (h - c)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hjc : (j' : ℝ) = (⌈h⌉₊ : ℝ) + (⌈1 / (h - c)⌉₊ : ℝ) := by rw [hj']; push_cast; ring
  have hA : h ≤ (j' : ℝ) + 1 := by linarith
  have hB : 1 / (h - c) ≤ (j' : ℝ) + 1 := by linarith
  have hB' : 1 / ((j' : ℝ) + 1) ≤ h - c := (one_div_le (by positivity) hpos).2 hB
  simp only [witnessCarrier, Set.mem_iUnion]
  exact ⟨e', a, ha, j', h, ⟨hK, by rw [← hcdef]; linarith, hA⟩, rfl⟩

/-! ## Tails: moments and layer cakes -/

/-- `L(e^{e^{e^y}}) = y / (e^{e^y} e^y)`. -/
theorem Lscale_exp3 (y : ℝ) :
    Lscale (Real.exp (Real.exp (Real.exp y))) = y / (Real.exp (Real.exp y) * Real.exp y) := by
  simp [Lscale, logIt, Real.log_exp]

/-- `T^s L(T) ≥ s³ y / 6` at `T = e^{e^{e^y}}`, `y ≥ 1`. -/
theorem rpow_Lscale_ge {s y : ℝ} (hs : 0 < s) (hy : 1 ≤ y) :
    s ^ 3 * y / 6 ≤
      Real.exp (Real.exp (Real.exp y)) ^ s * Lscale (Real.exp (Real.exp (Real.exp y))) := by
  rw [Lscale_exp3, ← Real.exp_mul]
  set z := Real.exp (Real.exp y) with hz
  have hey : Real.exp y ≤ z := by
    have := Real.add_one_le_exp (Real.exp y)
    linarith
  have hey0 : 0 < Real.exp y := Real.exp_pos y
  have hz1 : 1 ≤ z := by
    have := Real.add_one_le_exp y
    linarith
  have hz0 : 0 < z := by linarith
  have hy0 : 0 < y := by linarith
  have hexp : (z * s) ^ 3 / 6 ≤ Real.exp (z * s) := by
    have := Real.pow_div_factorial_le_exp (x := z * s) (by positivity) 3
    norm_num [Nat.factorial] at this
    linarith
  have h1 : y / (z * z) ≤ y / (z * Real.exp y) :=
    div_le_div_of_nonneg_left hy0.le (by positivity) (mul_le_mul_of_nonneg_left hey hz0.le)
  calc s ^ 3 * y / 6 ≤ s ^ 3 * y / 6 * z := le_mul_of_one_le_right (by positivity) hz1
    _ = (z * s) ^ 3 / 6 * (y / (z * z)) := by field_simp
    _ ≤ Real.exp (z * s) * (y / (z * Real.exp y)) :=
        mul_le_mul hexp h1 (by positivity) (Real.exp_pos _).le

/-- `x^s ≥ T^s` on `(T, ∞]`. -/
theorem lintegral_rpow_ge (μ : Measure ℝ≥0∞) {T s : ℝ} (hT : 0 ≤ T) (hs : 0 ≤ s) :
    ENNReal.ofReal (T ^ s) * μ (Set.Ioi (ENNReal.ofReal T)) ≤ ∫⁻ x, x ^ s ∂μ := by
  rw [← lintegral_indicator_const measurableSet_Ioi]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ Set.Ioi (ENNReal.ofReal T)
  · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_rpow_of_nonneg hT hs]
    exact ENNReal.rpow_le_rpow (le_of_lt hx) hs
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

/-- The bound `sup_X ν_X([0, e^{-j}]) ≤ β_j` supplied by the uniform lower tail. -/
noncomputable def betaSeq (c C u₀ : ℝ) (j : ℕ) : ℝ :=
  if u₀ ≤ (j : ℝ) then max C 0 * Real.exp (-Real.exp (Real.exp (c * j))) else 1

theorem betaSeq_nonneg (c C u₀ : ℝ) (j : ℕ) : 0 ≤ betaSeq c C u₀ j := by
  unfold betaSeq
  split_ifs
  · exact mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  · exact zero_le_one

/-- `∑_j e^{sj} β_j < ∞`: the double-exponential decay beats every exponential. -/
theorem summable_betaSeq {c : ℝ} (hc : 0 < c) (C u₀ : ℝ) (s : ℝ) :
    Summable (fun j : ℕ => Real.exp (s * j) * betaSeq c C u₀ j) := by
  refine Summable.of_norm_bounded_eventually_nat
    (Real.summable_exp_neg_nat.mul_left (max C 0)) ?_
  have hJ : ∀ᶠ j : ℕ in atTop, u₀ ≤ (j : ℝ) ∧ 2 * (s + 1) / c ^ 2 ≤ (j : ℝ) := by
    refine (tendsto_natCast_atTop_atTop.eventually_ge_atTop u₀).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)
  filter_upwards [hJ] with j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (betaSeq_nonneg _ _ _ _)),
    betaSeq, if_pos hj.1]
  have hq : (c * j) ^ 2 / 2 ≤ Real.exp (Real.exp (c * j)) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := c * j) (by positivity)
    have h2 := Real.add_one_le_exp (Real.exp (c * j))
    have h3 : 0 ≤ c * j := by positivity
    linarith
  have hlin : (s + 1) * j ≤ (c * j) ^ 2 / 2 := by
    have h1 := hj.2
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  have hexp : Real.exp (s * j) * Real.exp (-Real.exp (Real.exp (c * j))) ≤
      Real.exp (-(j : ℝ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (s * j) * (max C 0 * Real.exp (-Real.exp (Real.exp (c * j))))
      = max C 0 * (Real.exp (s * j) * Real.exp (-Real.exp (Real.exp (c * j)))) := by ring
    _ ≤ max C 0 * Real.exp (-(j : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp (le_max_right _ _)

/-- The uniform lower tail, in the open form used below. -/
theorem nuX_Iio_le_beta {c C u₀ : ℝ}
    (hU : ∀ u : ℝ, u₀ ≤ u → ∀ X : ℝ, 1 ≤ X →
      (nuX X).real (Set.Iic (ENNReal.ofReal (Real.exp (-u)))) ≤
        C * Real.exp (-Real.exp (Real.exp (c * u))))
    {X : ℝ} (hX : 1 ≤ X) (j : ℕ) :
    nuX X (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))) ≤
      ENNReal.ofReal (betaSeq c C u₀ j) := by
  haveI := nuX_isProb hX
  unfold betaSeq
  split_ifs with hj
  · refine (measure_mono Set.Iio_subset_Iic_self).trans ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    refine (hU j hj X hX).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · rw [ENNReal.ofReal_one]
    exact prob_le_one

/-- The uniform lower tail passes to every weak limit (open-set portmanteau). -/
theorem limit_Iio_le_beta {c C u₀ : ℝ}
    (hU : ∀ u : ℝ, u₀ ≤ u → ∀ X : ℝ, 1 ≤ X →
      (nuX X).real (Set.Iic (ENNReal.ofReal (Real.exp (-u)))) ≤
        C * Real.exp (-Real.exp (Real.exp (c * u))))
    {ν : Measure ℝ≥0∞} (hν : IsWeakSubseqLimit ν) (j : ℕ) :
    ν (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))) ≤ ENNReal.ofReal (betaSeq c C u₀ j) := by
  obtain ⟨hprob, X, hW⟩ := hν
  haveI := hprob
  refine ((portmanteau hW).1 _ isOpen_Iio).trans ?_
  apply liminf_le_of_frequently_le'
  refine ((hW.1.eventually_ge_atTop 1).mono (fun i hi => ?_)).frequently
  exact nuX_Iio_le_beta hU hi j

/-- `log⁻ x ≤ #{j : x < e^{-j}}`. -/
theorem logNegE_le_tsum (x : ℝ≥0∞) :
    logNegE x ≤ ∑' j : ℕ, (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator 1 x := by
  by_cases hx0 : x = 0
  · have hall : ∀ j : ℕ,
        (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x = 1 := by
      intro j
      rw [Set.indicator_of_mem]
      · rfl
      · rw [hx0, Set.mem_Iio]
        exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
    rw [tsum_congr hall, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    exact le_top
  rw [logNegE, if_neg hx0]
  by_cases hxt : x = ⊤
  · rw [hxt, ENNReal.toReal_top, Real.log_zero, neg_zero, ENNReal.ofReal_zero]
    exact zero_le
  set r := x.toReal with hr
  have hrpos : 0 < r := ENNReal.toReal_pos hx0 hxt
  have hxr : x = ENNReal.ofReal r := (ENNReal.ofReal_toReal hxt).symm
  rcases le_or_gt (-Real.log r) 0 with hy | hy
  · rw [ENNReal.ofReal_of_nonpos hy]
    exact zero_le
  set n := ⌈-Real.log r⌉₊ with hn
  refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range n))
  have hterm : ∀ j ∈ Finset.range n,
      (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x = 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjy : (j : ℝ) < -Real.log r := Nat.lt_ceil.1 hj
    rw [Set.indicator_of_mem]
    · rfl
    · rw [hxr, Set.mem_Iio, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
      rw [← Real.exp_log hrpos]
      exact Real.exp_lt_exp.2 (by linarith)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)

/-- `x^{-s} ≤ 1 + e^s ∑_j e^{sj} 1[x < e^{-j}]`. -/
theorem rpow_neg_le_tsum {s : ℝ} (hs : 0 < s) (x : ℝ≥0∞) :
    x ^ (-s) ≤ 1 + ENNReal.ofReal (Real.exp s) * ∑' j : ℕ,
      ENNReal.ofReal (Real.exp (s * j)) *
        (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator 1 x := by
  have hneg : -s < 0 := by linarith
  by_cases hx0 : x = 0
  · have hall : ∀ j : ℕ, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (s * j)) *
        (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x := by
      intro j
      rw [Set.indicator_of_mem]
      · rw [Pi.one_apply, mul_one, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
      · rw [hx0, Set.mem_Iio]
        exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
    have htop : ∑' j : ℕ, ENNReal.ofReal (Real.exp (s * j)) *
        (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
      exact ENNReal.tsum_le_tsum hall
    rw [htop, ENNReal.mul_top (by simpa using Real.exp_pos s), add_top]
    exact le_top
  by_cases hxt : x = ⊤
  · rw [hxt, ENNReal.top_rpow_of_neg hneg]
    exact zero_le
  set r := x.toReal with hr
  have hrpos : 0 < r := ENNReal.toReal_pos hx0 hxt
  have hxr : x = ENNReal.ofReal r := (ENNReal.ofReal_toReal hxt).symm
  rcases le_or_gt 1 x with h1 | h1
  · exact (ENNReal.rpow_le_one_of_one_le_of_neg h1 hneg).trans le_self_add
  have hr1 : r < 1 := by
    have := (ENNReal.toReal_lt_toReal hxt ENNReal.one_ne_top).2 h1
    simpa using this
  set y := -Real.log r with hy
  have hy0 : 0 < y := by
    have := Real.log_neg hrpos hr1
    linarith
  set n := ⌈y⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by
    rw [hn, Ne, Nat.ceil_eq_zero, not_le]
    exact hy0)
  set j₀ := n - 1 with hj₀
  have hj₀lt : (j₀ : ℝ) < y := by
    have := Nat.ceil_lt_add_one hy0.le
    rw [← hn] at this
    have hc : (j₀ : ℝ) = (n : ℝ) - 1 := by
      rw [hj₀, Nat.cast_sub hn1]
      norm_num
    linarith
  have hyn : y ≤ (j₀ : ℝ) + 1 := by
    have hc : (j₀ : ℝ) + 1 = (n : ℝ) := by
      rw [hj₀, Nat.cast_sub hn1]
      norm_num
    rw [hc]
    exact Nat.le_ceil _
  have hind : (Set.Iio (ENNReal.ofReal (Real.exp (-(j₀ : ℝ))))).indicator
      (1 : ℝ≥0∞ → ℝ≥0∞) x = 1 := by
    rw [Set.indicator_of_mem]
    · rfl
    · rw [hxr, Set.mem_Iio, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
      rw [← Real.exp_log hrpos]
      exact Real.exp_lt_exp.2 (by linarith)
  have hxs : x ^ (-s) = ENNReal.ofReal (Real.exp (s * y)) := by
    rw [hxr, ENNReal.ofReal_rpow_of_pos hrpos, Real.rpow_def_of_pos hrpos, hy]
    ring_nf
  rw [hxs]
  refine le_trans ?_ le_add_self
  refine le_trans ?_ (mul_le_mul_right (ENNReal.le_tsum j₀) _)
  rw [hind, mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  nlinarith

/-- `∫ log⁻ dμ ≤ ∑_j β_j` under `μ([0, e^{-j})) ≤ β_j`. -/
theorem lintegral_logNeg_le (μ : Measure ℝ≥0∞) {β : ℕ → ℝ}
    (hβ : ∀ j : ℕ, μ (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))) ≤ ENNReal.ofReal (β j))
    (hβ0 : ∀ j, 0 ≤ β j) (hsum : Summable β) :
    ∫⁻ x, logNegE x ∂μ ≤ ENNReal.ofReal (∑' j, β j) := by
  refine (lintegral_mono (fun x => logNegE_le_tsum x)).trans ?_
  have hm : ∀ j : ℕ, AEMeasurable (fun x : ℝ≥0∞ =>
      (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x) μ :=
    fun j => (measurable_one.indicator measurableSet_Iio).aemeasurable
  rw [lintegral_tsum hm, ENNReal.ofReal_tsum_of_nonneg hβ0 hsum]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  rw [lintegral_indicator_one measurableSet_Iio]
  exact hβ j

/-- `∫ x^{-s} dμ ≤ 1 + e^s ∑_j e^{sj} β_j` under `μ(univ) ≤ 1`, `μ([0, e^{-j})) ≤ β_j`. -/
theorem lintegral_rpow_neg_le (μ : Measure ℝ≥0∞) (hμ : μ Set.univ ≤ 1) {β : ℕ → ℝ}
    (hβ : ∀ j : ℕ, μ (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))) ≤ ENNReal.ofReal (β j))
    (hβ0 : ∀ j, 0 ≤ β j) {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun j : ℕ => Real.exp (s * j) * β j)) :
    ∫⁻ x, x ^ (-s) ∂μ ≤
      1 + ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (∑' j : ℕ, Real.exp (s * j) * β j) := by
  refine (lintegral_mono (fun x => rpow_neg_le_tsum hs x)).trans ?_
  have hm : ∀ j : ℕ, AEMeasurable (fun x : ℝ≥0∞ => ENNReal.ofReal (Real.exp (s * j)) *
      (Set.Iio (ENNReal.ofReal (Real.exp (-(j : ℝ))))).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x) μ :=
    fun j => ((measurable_one.indicator measurableSet_Iio).const_mul _).aemeasurable
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hm,
    ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (Real.exp_pos _).le (hβ0 j)) hsum]
  refine add_le_add hμ (mul_le_mul_right (ENNReal.tsum_le_tsum (fun j => ?_)) _)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one measurableSet_Iio,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul_right (hβ j) _

/-- The truncation `min(x^{-s}, n)` as a bounded continuous function on `[0, ∞]`. -/
noncomputable def truncRpow (s : ℝ) (n : ℕ) : ℝ≥0∞ →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (min (x ^ (-s)) (n : ℝ≥0∞)).toNNReal, by
      refine ENNReal.continuousOn_toNNReal.comp_continuous
        ((ENNReal.continuous_rpow_const).min continuous_const) (fun x => ?_)
      exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)⟩

theorem truncRpow_apply (s : ℝ) (n : ℕ) (x : ℝ≥0∞) :
    ((truncRpow s n x : ℝ≥0) : ℝ≥0∞) = min (x ^ (-s)) (n : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))

/-- `a ≤ min(a, n) + a² / n` for `n ≥ 1`. -/
theorem le_min_add_sq (a : ℝ≥0∞) {n : ℕ} (hn : 1 ≤ n) :
    a ≤ min a (n : ℝ≥0∞) + a ^ 2 * (n : ℝ≥0∞)⁻¹ := by
  rcases le_total a n with h | h
  · rw [min_eq_left h]
    exact le_self_add
  · rw [min_eq_right h]
    refine le_trans ?_ le_add_self
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hge : 1 ≤ a * (n : ℝ≥0∞)⁻¹ := by
      rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hn0)
        (Or.inl (ENNReal.natCast_ne_top n)), one_mul]
      exact h
    calc a = a * 1 := (mul_one a).symm
      _ ≤ a * (a * (n : ℝ≥0∞)⁻¹) := mul_le_mul' le_rfl hge
      _ = a ^ 2 * (n : ℝ≥0∞)⁻¹ := by ring

/-- The weight `w_k = e^{k+1} − e^k`. -/
noncomputable def wt (k : ℕ) : ℝ := Real.exp ((k : ℝ) + 1) - Real.exp (k : ℝ)

/-- The threshold `T_k = exp(e^{k+1})`. -/
noncomputable def Tk (k : ℕ) : ℝ := Real.exp (Real.exp ((k : ℝ) + 1))

theorem wt_nonneg (k : ℕ) : 0 ≤ wt k := by
  unfold wt
  have := Real.exp_le_exp.2 (by linarith : (k : ℝ) ≤ k + 1)
  linarith

theorem Tk_pos (k : ℕ) : 0 < Tk k := Real.exp_pos _

/-- `∑_{k<K} w_k 1[y > T_k] ≤ max(min(log y, e^K) − 1, 0)`. -/
theorem sum_wt_le (y : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, wt k * (if Tk k < y then 1 else 0) ≤
      max (min (Real.log y) (Real.exp (K : ℝ)) - 1) 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hKK : Real.exp (K : ℝ) ≤ Real.exp ((K : ℝ) + 1) := Real.exp_le_exp.2 (by linarith)
    have hc : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    by_cases h : Tk K < y
    · rw [if_pos h, mul_one]
      have hy : 0 < y := lt_trans (Tk_pos K) h
      have hlog : Real.exp ((K : ℝ) + 1) < Real.log y := by
        rw [Real.lt_log_iff_exp_lt hy]
        exact h
      have h1 : 1 ≤ Real.exp (K : ℝ) := Real.one_le_exp (Nat.cast_nonneg K)
      have hmin1 : min (Real.log y) (Real.exp (K : ℝ)) = Real.exp K := min_eq_right (by linarith)
      have hmin2 : min (Real.log y) (Real.exp ((K + 1 : ℕ) : ℝ)) = Real.exp ((K : ℝ) + 1) := by
        rw [hc]
        exact min_eq_right hlog.le
      rw [hmin1, max_eq_left (by linarith)] at ih
      rw [hmin2, max_eq_left (by linarith)]
      have hw : wt K = Real.exp ((K : ℝ) + 1) - Real.exp (K : ℝ) := rfl
      linarith
    · rw [if_neg h, mul_zero, add_zero]
      refine ih.trans (max_le_max ?_ le_rfl)
      have : Real.exp (K : ℝ) ≤ Real.exp ((K + 1 : ℕ) : ℝ) := by rw [hc]; exact hKK
      exact sub_le_sub_right (min_le_min_left _ this) 1

/-- The `ν_X` form: `∑_{k₀≤k<K} w_k 1[T_k < x < ∞] ≤ log⁺ x`. -/
theorem sum_wt_Ioo_le (k₀ K : ℕ) (x : ℝ≥0∞) :
    ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) *
        (Set.Ioo (ENNReal.ofReal (Tk k)) ⊤).indicator 1 x ≤
      ENNReal.ofReal (Real.log x.toReal) := by
  by_cases hx : x = ⊤
  · rw [Finset.sum_eq_zero]
    · exact zero_le
    intro k _
    rw [Set.indicator_of_notMem (by rw [hx]; exact fun h => lt_irrefl _ h.2), mul_zero]
  have hterm : ∀ k : ℕ, ENNReal.ofReal (wt k) *
      (Set.Ioo (ENNReal.ofReal (Tk k)) ⊤).indicator (1 : ℝ≥0∞ → ℝ≥0∞) x =
        ENNReal.ofReal (wt k * (if Tk k < x.toReal then 1 else 0)) := by
    intro k
    by_cases h : Tk k < x.toReal
    · rw [if_pos h, mul_one, Set.indicator_of_mem, Pi.one_apply, mul_one]
      exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal (Tk_pos k).le hx).2 h, lt_top_iff_ne_top.2 hx⟩
    · rw [if_neg h, mul_zero, ENNReal.ofReal_zero, Set.indicator_of_notMem, mul_zero]
      exact fun hm => h ((ENNReal.ofReal_lt_iff_lt_toReal (Tk_pos k).le hx).1 hm.1)
  have hnn : ∀ k : ℕ, 0 ≤ wt k * (if Tk k < x.toReal then (1 : ℝ) else 0) := by
    intro k
    refine mul_nonneg (wt_nonneg k) ?_
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k)]
  have hsub : Finset.Ico k₀ K ⊆ Finset.range K := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    exact hk.2
  calc ENNReal.ofReal (∑ k ∈ Finset.Ico k₀ K, wt k * (if Tk k < x.toReal then 1 else 0))
      ≤ ENNReal.ofReal (∑ k ∈ Finset.range K, wt k * (if Tk k < x.toReal then 1 else 0)) :=
        ENNReal.ofReal_le_ofReal
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hnn k))
    _ ≤ ENNReal.ofReal (max (Real.log x.toReal) 0) := by
        apply ENNReal.ofReal_le_ofReal
        refine (sum_wt_le _ K).trans (max_le_max ?_ le_rfl)
        linarith [min_le_left (Real.log x.toReal) (Real.exp (K : ℝ))]
    _ = ENNReal.ofReal (Real.log x.toReal) := by
        rcases le_total (Real.log x.toReal) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

/-- The `ν` form: `∑_{k₀≤k<K} w_k 1[x > T_k] ≤ log⁺ x` on `[0, ∞]`. -/
theorem sum_wt_Ioi_le (k₀ K : ℕ) (x : ℝ≥0∞) :
    ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) *
        (Set.Ioi (ENNReal.ofReal (Tk k))).indicator 1 x ≤ logPosE x := by
  by_cases hx : x = ⊤
  · rw [hx, logPosE, if_pos rfl]
    exact le_top
  rw [logPosE, if_neg hx]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_))) (sum_wt_Ioo_le k₀ K x)
  congr 1
  by_cases h : x ∈ Set.Ioi (ENNReal.ofReal (Tk k))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem
      (show x ∈ Set.Ioo (ENNReal.ofReal (Tk k)) ⊤ from ⟨h, lt_top_iff_ne_top.2 hx⟩)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
      (show x ∉ Set.Ioo (ENNReal.ofReal (Tk k)) ⊤ from fun hm => h hm.1)]

/-- Integrating the layer cake. -/
theorem lintegral_sum_wt (μ : Measure ℝ≥0∞) (k₀ K : ℕ) (A : ℕ → Set ℝ≥0∞)
    (hA : ∀ k, MeasurableSet (A k)) :
    ∫⁻ x, ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) * (A k).indicator 1 x ∂μ =
      ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) * μ (A k) := by
  rw [lintegral_finsetSum _ (fun k _ => (measurable_one.indicator (hA k)).const_mul _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one (hA k)]

/-- `w_k L(T_k) = (1 − e^{-1}) log(k+1)/(k+1)`. -/
theorem wt_mul_Lscale (k : ℕ) :
    wt k * Lscale (Tk k) = (1 - Real.exp (-1)) * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) := by
  have hL : Lscale (Tk k) =
      Real.log ((k : ℝ) + 1) / (Real.exp ((k : ℝ) + 1) * ((k : ℝ) + 1)) := by
    simp [Lscale, logIt, Tk, Real.log_exp]
  have he : Real.exp (k : ℝ) = Real.exp ((k : ℝ) + 1) * Real.exp (-1) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hL, wt, he]
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : 0 < Real.exp ((k : ℝ) + 1) := Real.exp_pos _
  field_simp

/-- `w_k L(T_k) ≥ (1 − e^{-1})/(k+1)` for `k ≥ 2`. -/
theorem wt_mul_Lscale_ge {k : ℕ} (hk : 2 ≤ k) :
    (1 - Real.exp (-1)) * (1 / ((k : ℝ) + 1)) ≤ wt k * Lscale (Tk k) := by
  rw [wt_mul_Lscale]
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : 1 ≤ Real.log ((k : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le h1]
    have h3 : (3 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have := Real.exp_one_lt_d9
    linarith
  have hpos : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    linarith
  apply mul_le_mul_of_nonneg_left _ hpos.le
  exact div_le_div_of_nonneg_right hlog h1.le

/-- The harmonic tails diverge. -/
theorem harmonic_Ico_unbounded (k₀ : ℕ) (M : ℝ) :
    ∃ K : ℕ, k₀ ≤ K ∧ M ≤ ∑ k ∈ Finset.Ico k₀ K, 1 / ((k : ℝ) + 1) := by
  obtain ⟨K, hK⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop
    (M + ∑ k ∈ Finset.range k₀, 1 / ((k : ℝ) + 1))).and (eventually_ge_atTop k₀) |>.exists
  refine ⟨K, hK.2, ?_⟩
  have := Finset.sum_range_add_sum_Ico (fun k : ℕ => 1 / ((k : ℝ) + 1)) hK.2
  linarith [hK.1]

/-! ## Witness domination in the limit -/

/-- `𝒲_X` integrates every `φ ∈ C_c((0,∞))` finitely: only the pairs with `ed ≤ bN` count. -/
theorem lintegral_empWitness_lt_top {φ : ℝ≥0∞ → ℝ} (hφ : IsCcPos φ) (X : ℝ) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂(empWitness X) < ⊤ := by
  obtain ⟨_, a, b, ha, hsupp⟩ := hφ
  rw [lintegral_empWitness]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 (fun N hN => ?_))
  have hNpos : (0 : ℝ) < N := by
    have := (Finset.mem_Icc.1 hN).1
    exact_mod_cast this
  rw [tsum_eq_sum (s := Finset.range (⌊b * N⌋₊ + 1) ×ˢ Finset.range (⌊b * N⌋₊ + 1)) ?_]
  · refine ENNReal.sum_lt_top.2 (fun p _ => ?_)
    split_ifs
    · exact ENNReal.ofReal_lt_top
    · exact ENNReal.zero_lt_top
  · intro p hp
    split_ifs with hc
    · by_contra hne
      have hφne : φ (ENNReal.ofReal (((p.1 * p.2 : ℕ) : ℝ) / (N : ℝ))) ≠ 0 := by
        intro h0
        rw [h0, ENNReal.ofReal_zero] at hne
        exact hne rfl
      have hb := (hsupp _ hφne).2
      have hed : (1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      have hpos : 0 < ((p.1 * p.2 : ℕ) : ℝ) / N := by positivity
      rcases (ENNReal.ofReal_le_ofReal_iff' (p := ((p.1 * p.2 : ℕ) : ℝ) / N) (q := b)).1 hb
        with h | h
      · rw [div_le_iff₀ hNpos] at h
        have h1 : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_right _ hc.2.1
        have h2 : (p.2 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_left _ hc.1
        apply hp
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith)),
          Nat.lt_succ_of_le (Nat.le_floor (by linarith))⟩
      · linarith
    · rfl

/-- A continuous bump `0 ≤ φ ≤ 1`, `φ = 1` on the compact `K`, supported in the open
`U ⊆ (0, ∞)`. -/
theorem exists_ccPos_bump {K U : Set ℝ≥0∞} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUO : U ⊆ Set.Ioo 0 ⊤) :
    ∃ φ : ℝ≥0∞ → ℝ, IsCcPos φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x ∈ K, φ x = 1) ∧
      (∀ x, x ∉ U → φ x = 0) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨fun _ => 0, ⟨continuous_const, 1, 1, one_pos, fun x hx => absurd rfl hx⟩,
      fun _ => le_rfl, fun _ => zero_le_one, ?_, fun _ _ => rfl⟩
    rw [hKe]
    intro x hx
    exact absurd hx (Set.notMem_empty x)
  have hmin := hK.sInf_mem hKne
  have hmax := hK.sSup_mem hKne
  have h0 : 0 < sInf K := (hUO (hKU hmin)).1
  have hIt : sInf K ≠ ⊤ := (hUO (hKU hmin)).2.ne
  have hSt : sSup K ≠ ⊤ := (hUO (hKU hmax)).2.ne
  set a := (sInf K).toReal / 2 with hadef
  set b := (sSup K).toReal + 1 with hbdef
  have hIpos : 0 < (sInf K).toReal := ENNReal.toReal_pos h0.ne' hIt
  have ha : 0 < a := by positivity
  have haK : ENNReal.ofReal a < sInf K :=
    (ENNReal.ofReal_lt_iff_lt_toReal ha.le hIt).2 (by linarith)
  have hbK : sSup K < ENNReal.ofReal b := (ENNReal.lt_ofReal_iff_toReal_lt hSt).2 (by linarith)
  set F := Uᶜ ∪ (Set.Iic (ENNReal.ofReal a) ∪ Set.Ici (ENNReal.ofReal b)) with hFdef
  have hF : IsClosed F := hU.isClosed_compl.union (isClosed_Iic.union isClosed_Ici)
  have hdisj : Disjoint F K := by
    rw [Set.disjoint_left]
    intro x hxF hxK
    rcases hxF with h | h | h
    · exact h (hKU hxK)
    · have h1 : sInf K ≤ x := sInf_le hxK
      have h2 : x ≤ ENNReal.ofReal a := h
      exact absurd (lt_of_le_of_lt (h1.trans h2) haK) (lt_irrefl _)
    · have h1 : x ≤ sSup K := le_sSup hxK
      have h2 : ENNReal.ofReal b ≤ x := h
      exact absurd (lt_of_le_of_lt (h2.trans h1) hbK) (lt_irrefl _)
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hF hK.isClosed hdisj
  refine ⟨f, ⟨f.continuous, a, b, ha, fun x hx => ?_⟩, fun x => (hf01 x).1,
    fun x => (hf01 x).2, fun x hx => hf1 hx, fun x hx => hf0 (Or.inl hx)⟩
  by_contra hcon
  apply hx
  apply hf0
  rcases le_or_gt (ENNReal.ofReal a) x with h1 | h1
  · have h2 : ENNReal.ofReal b < x := by
      by_contra h3
      exact hcon ⟨h1, not_lt.1 h3⟩
    exact Or.inr (Or.inr h2.le)
  · exact Or.inr (Or.inl h1.le)

theorem measure_le_lintegral_bump (μ : Measure ℝ≥0∞) {A : Set ℝ≥0∞} (hA : MeasurableSet A)
    {φ : ℝ≥0∞ → ℝ} (hφA : ∀ x ∈ A, φ x = 1) :
    μ A ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂μ := by
  rw [← lintegral_indicator_one hA]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, hφA x hx, ENNReal.ofReal_one]
    rfl
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

theorem lintegral_bump_le (μ : Measure ℝ≥0∞) {U : Set ℝ≥0∞} (hU : MeasurableSet U)
    {φ : ℝ≥0∞ → ℝ} (hφ1 : ∀ x, φ x ≤ 1) (hφU : ∀ x, x ∉ U → φ x = 0) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≤ μ U := by
  rw [← lintegral_indicator_one hU]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.ofReal_le_one.2 (hφ1 x)
  · rw [hφU x hx, ENNReal.ofReal_zero]
    exact zero_le

/-- **Passing the witness domination to the limit.** For `0 ≤ φ ∈ C_c((0,∞))`,
`∫ φ dν ≤ ∫ φ d𝒲` (the right side a Bochner integral). -/
theorem limit_le_integral {ν : Measure ℝ≥0∞} (hν : IsWeakSubseqLimit ν)
    (hWD : Step_DaddWitnessDomination) (hEV : Step_DaddEmpiricalWitnessVague)
    (hRF : Intro_RcntFormula) {φ : ℝ≥0∞ → ℝ} (hφ : IsCcPos φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ ENNReal.ofReal (∫ x, φ x ∂witnessMeasure) := by
  obtain ⟨hprob, X, hW⟩ := hν
  haveI := hprob
  have hc := hφ.1
  let Φ : ℝ≥0∞ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ, hc⟩
  have h1 : Tendsto (fun j => ∫ x, φ x ∂(nuX (X j))) atTop (𝓝 (∫ x, φ x ∂ν)) := hW.2 Φ
  have h2 : Tendsto (fun j => (X j / Rcnt (X j)) * ∫ x, φ x ∂(empWitness (X j))) atTop
      (𝓝 (1 * ∫ x, φ x ∂witnessMeasure)) :=
    ((tendsto_X_div_Rcnt hRF).comp hW.1).mul ((hEV φ hφ).comp hW.1)
  rw [one_mul] at h2
  have hle : ∀ᶠ j in atTop, ∫ x, φ x ∂(nuX (X j)) ≤
      (X j / Rcnt (X j)) * ∫ x, φ x ∂(empWitness (X j)) := by
    filter_upwards [hW.1.eventually_ge_atTop 1] with j hj
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφ0) hc.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφ0) hc.aestronglyMeasurable]
    have hfin := lintegral_empWitness_lt_top hφ (X j)
    have hdom := hWD φ hφ hφ0 (X j) hj
    have hR : 0 ≤ X j / Rcnt (X j) := div_nonneg (by linarith) (Nat.cast_nonneg _)
    calc (∫⁻ x, ENNReal.ofReal (φ x) ∂(nuX (X j))).toReal
        ≤ (ENNReal.ofReal (X j / Rcnt (X j)) *
            ∫⁻ x, ENNReal.ofReal (φ x) ∂(empWitness (X j))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hdom
      _ = X j / Rcnt (X j) * (∫⁻ x, ENNReal.ofReal (φ x) ∂(empWitness (X j))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hR]
  have hmain := le_of_tendsto_of_tendsto h1 h2 hle
  have hint : Integrable φ ν := Φ.integrable ν
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ0)]
  exact ENNReal.ofReal_le_ofReal hmain

/-! ## Vague convergence of `𝒲_X` -/

/-- `𝒲_X([0, t]) = (1/X) ∑_{N ≤ X} r_t(N)` (the witnesses with ratio `≤ t` are the pairs counted
by `r_t`). -/
theorem empWitness_Iic (X : ℝ) {t : ℝ} (ht : 0 < t) :
    empWitness X (Set.Iic (ENNReal.ofReal t)) =
      ENNReal.ofReal (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rt t N : ℝ≥0∞) := by
  rw [← lintegral_indicator_one measurableSet_Iic, lintegral_empWitness]
  congr 1
  refine Finset.sum_congr rfl (fun N hN => ?_)
  have hNpos : (0 : ℝ) < N := by
    have := (Finset.mem_Icc.1 hN).1
    exact_mod_cast this
  have hmem : ∀ p : ℕ × ℕ, ENNReal.ofReal (((p.1 * p.2 : ℕ) : ℝ) / (N : ℝ)) ∈
      Set.Iic (ENNReal.ofReal t) ↔ ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N := by
    intro p
    rw [Set.mem_Iic, ENNReal.ofReal_le_ofReal_iff ht.le, div_le_iff₀ hNpos]
  unfold rt
  rw [Finset.card_filter, Nat.cast_sum]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊t * N⌋₊ ×ˢ Finset.Icc 1 ⌊t * N⌋₊) ?_]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    by_cases hF : F p.1 p.2 = N
    · rw [if_pos ⟨hp.1.1, hp.2.1, hF⟩]
      by_cases hle : ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N
      · rw [Set.indicator_of_mem ((hmem p).2 hle), if_pos ⟨hF, hle⟩]
        simp
      · rw [Set.indicator_of_notMem (fun h => hle ((hmem p).1 h)), if_neg (fun h => hle h.2)]
        simp
    · rw [if_neg (fun h => hF h.2.2), if_neg (fun h => hF h.1)]
      simp
  · intro p hp
    split_ifs with hc
    · rw [Set.indicator_of_notMem]
      intro hm
      apply hp
      have hle := (hmem p).1 hm
      have h1 : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_right _ hc.2.1
      have h2 : (p.2 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left _ hc.1
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨hc.1, Nat.le_floor (by linarith)⟩, ⟨hc.2.1, Nat.le_floor (by linarith)⟩⟩
    · rfl

/-- `𝒲_X` has no atom at `0`. -/
theorem empWitness_zero (X : ℝ) : empWitness X {0} = 0 := by
  rw [← lintegral_indicator_one (measurableSet_singleton 0), lintegral_empWitness]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun N hN => ?_))
  have hNpos : (0 : ℝ) < N := by
    have := (Finset.mem_Icc.1 hN).1
    exact_mod_cast this
  refine ENNReal.tsum_eq_zero.2 (fun p => ?_)
  split_ifs with hc
  · rw [Set.indicator_of_notMem]
    rw [Set.mem_singleton_iff, ENNReal.ofReal_eq_zero, not_le]
    have hed : (1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    positivity
  · rfl

/-- **Distribution functions converge** at every finite point of `[0, ∞]`. -/
theorem tendsto_empWitness_Iic (hWM : Prop_DaddWitnessMeans) (hMM : Step_DaddWitnessMeasureMass)
    {τ : ℝ≥0∞} (hτ : τ ≠ ⊤) :
    Tendsto (fun X : ℝ => empWitness X (Set.Iic τ)) atTop (𝓝 (witnessMeasure (Set.Iic τ))) ∧
      witnessMeasure (Set.Iic τ) ≠ ⊤ := by
  rcases eq_or_ne τ 0 with h0 | h0
  · have hI : Set.Iic τ = {0} := by
      rw [h0]
      ext x
      simp
    rw [hI, hMM.2 0]
    refine ⟨?_, ENNReal.zero_ne_top⟩
    simp only [empWitness_zero]
    exact tendsto_const_nhds
  set r := τ.toReal with hr
  have hrpos : 0 < r := ENNReal.toReal_pos h0 hτ
  have hτr : τ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hτ).symm
  have hW : witnessMeasure (Set.Iic τ) = ENNReal.ofReal (Wfun r) := by
    have hsplit : Set.Iic τ = {0} ∪ Set.Ioc 0 τ := by
      ext x
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
      constructor
      · intro hx
        rcases eq_or_ne x 0 with hx0 | hx0
        · exact Or.inl hx0
        · exact Or.inr ⟨pos_iff_ne_zero.2 hx0, hx⟩
      · rintro (hx | hx)
        · rw [hx]
          exact zero_le
        · exact hx.2
    have hIoc := hMM.1 r hrpos
    rw [← hτr] at hIoc
    refine le_antisymm ?_ ?_
    · rw [hsplit]
      refine (measure_union_le _ _).trans ?_
      rw [hMM.2 0, zero_add, hIoc]
    · rw [← hIoc]
      exact measure_mono (fun x hx => hx.2)
  refine ⟨?_, by rw [hW]; exact ENNReal.ofReal_ne_top⟩
  rw [hW]
  have hlim := ENNReal.tendsto_ofReal ((hWM.1 r hrpos).1)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [hτr, empWitness_Iic X hrpos, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun N _ => Nat.cast_nonneg _)]
  simp only [ENNReal.ofReal_natCast]

/-- `𝒲_X` is finite on every `[0, τ]`, `τ < ∞`. -/
theorem empWitness_Iic_ne_top (X : ℝ) {τ : ℝ≥0∞} (hτ : τ ≠ ⊤) :
    empWitness X (Set.Iic τ) ≠ ⊤ := by
  rcases eq_or_ne τ 0 with h0 | h0
  · have hI : Set.Iic τ = {0} := by
      rw [h0]
      ext x
      simp
    rw [hI, empWitness_zero]
    exact ENNReal.zero_ne_top
  · have hr := ENNReal.toReal_pos h0 hτ
    rw [← ENNReal.ofReal_toReal hτ, empWitness_Iic X hr]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 (fun N _ => ENNReal.natCast_ne_top _))

/-- The same for the restriction to `[0, c]`, on the sets `[0, t]` and `(u, t]`. -/
theorem tendsto_restrict_Ioc (hWM : Prop_DaddWitnessMeans) (hMM : Step_DaddWitnessMeasureMass)
    {c' : ℝ≥0∞} (hc' : c' ≠ ⊤) (u t : ℝ≥0∞) :
    Tendsto (fun X : ℝ => (empWitness X).restrict (Set.Iic c') (Set.Ioc u t)) atTop
      (𝓝 (witnessMeasure.restrict (Set.Iic c') (Set.Ioc u t))) := by
  set τ := min t c' with hτ
  have hτt : τ ≠ ⊤ := ne_top_of_le_ne_top hc' (min_le_right _ _)
  have hστ : min u τ ≠ ⊤ := ne_top_of_le_ne_top hτt (min_le_right _ _)
  have hset : Set.Ioc u t ∩ Set.Iic c' = Set.Iic τ \ Set.Iic (min u τ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨le_min h2 h3, fun h => absurd h1 (not_lt.2 (h.trans (min_le_left _ _)))⟩
    · rintro ⟨h1, h2⟩
      have hxt : x ≤ t := h1.trans (min_le_left _ _)
      have hxc : x ≤ c' := h1.trans (min_le_right _ _)
      refine ⟨⟨?_, hxt⟩, hxc⟩
      by_contra hux
      exact h2 (le_min (not_lt.1 hux) h1)
  have hsub : Set.Iic (min u τ) ⊆ Set.Iic τ := Set.Iic_subset_Iic.2 (min_le_right _ _)
  obtain ⟨h1, h1f⟩ := tendsto_empWitness_Iic hWM hMM hτt
  obtain ⟨h2, h2f⟩ := tendsto_empWitness_Iic hWM hMM hστ
  rw [Measure.restrict_apply measurableSet_Ioc, hset,
    measure_sdiff hsub measurableSet_Iic.nullMeasurableSet
      (ne_top_of_le_ne_top h2f (le_refl _))]
  have hev : ∀ X : ℝ, (empWitness X).restrict (Set.Iic c') (Set.Ioc u t) =
      empWitness X (Set.Iic τ) - empWitness X (Set.Iic (min u τ)) := by
    intro X
    rw [Measure.restrict_apply measurableSet_Ioc, hset,
      measure_sdiff hsub measurableSet_Iic.nullMeasurableSet (empWitness_Iic_ne_top X hστ)]
  simp only [hev]
  exact ENNReal.Tendsto.sub h1 h2 (Or.inl h1f)

/-- The restriction of a measure to `[0, c']`, as a finite measure. -/
noncomputable def resFM (μ : Measure ℝ≥0∞) (c' : ℝ≥0∞) (h : μ (Set.Iic c') ≠ ⊤) :
    FiniteMeasure ℝ≥0∞ :=
  ⟨μ.restrict (Set.Iic c'), ⟨by rw [Measure.restrict_apply_univ]; exact h.lt_top⟩⟩

end Principia.Erdos1054.Proofs.Singularity

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054 Principia.Erdos1054.Limits Singularity

/-- Witness domination (EP1054.tex lines 2904–2909). -/
theorem leaf_Step_DaddWitnessDomination : Principia.Erdos1054.Step_DaddWitnessDomination := by
  intro φ _ _ X hX
  exact lintegral_nuX_le (fun x => ENNReal.ofReal (φ x)) hX

/-- Witness domination near `0` (EP1054.tex lines 2918–2924). -/
theorem leaf_Step_DaddCountDomination : Principia.Erdos1054.Step_DaddCountDomination := by
  intro t ht X hX
  have hmeas : MeasurableSet (Set.Iio (ENNReal.ofReal t)) := measurableSet_Iio
  refine ⟨?_, ?_⟩
  · have h := lintegral_nuX_le ((Set.Iio (ENNReal.ofReal t)).indicator 1) hX
    rwa [lintegral_indicator_one hmeas, lintegral_indicator_one hmeas] at h
  · rw [← lintegral_indicator_one hmeas, lintegral_empWitness]
    have hXpos : 0 < X := by linarith
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun N _ => Nat.cast_nonneg _)]
    gcongr with N hN
    rw [ENNReal.ofReal_natCast]
    have hNpos : (0 : ℝ) < N := by
      have := (Finset.mem_Icc.1 hN).1
      exact_mod_cast this
    unfold rt
    rw [Finset.card_filter, Nat.cast_sum]
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊t * N⌋₊ ×ˢ Finset.Icc 1 ⌊t * N⌋₊) ?_]
    · refine Finset.sum_le_sum (fun p _ => ?_)
      by_cases hc : 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ F p.1 p.2 = N
      · rw [if_pos hc]
        by_cases hm : ENNReal.ofReal (((p.1 * p.2 : ℕ) : ℝ) / N) ∈ Set.Iio (ENNReal.ofReal t)
        · rw [Set.indicator_of_mem hm]
          have hle : ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N := by
            rw [Set.mem_Iio, ENNReal.ofReal_lt_ofReal_iff ht, div_lt_iff₀ hNpos] at hm
            exact hm.le
          rw [if_pos ⟨hc.2.2, hle⟩]
          simp
        · rw [Set.indicator_of_notMem hm]
          exact zero_le
      · rw [if_neg hc]
        exact zero_le
    · intro p hp
      by_cases hc : 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ F p.1 p.2 = N
      · rw [if_pos hc, Set.indicator_of_notMem]
        intro hm
        apply hp
        rw [Set.mem_Iio, ENNReal.ofReal_lt_ofReal_iff ht, div_lt_iff₀ hNpos] at hm
        have h1 : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_right _ hc.2.1
        have h2 : (p.2 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_left _ hc.1
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨hc.1, Nat.le_floor (by linarith)⟩, ⟨hc.2.1, Nat.le_floor (by linarith)⟩⟩
      · rw [if_neg hc]

/-- `X / R(X) ≤ 3` (EP1054.tex line 3001), from `𝓡 = ℕ ∖ {2, 5}`. -/
theorem link_Step_DaddXoverR : Principia.Erdos1054.Spine.Link_Step_DaddXoverR := by
  intro hR X hX
  set n := ⌊X⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hX)
  have hXlt : X < n + 1 := Nat.lt_floor_add_one X
  have hRc : Rcnt X = (((Finset.Icc 1 n).erase 2).erase 5).card := by
    show cnt R X = _
    rw [hR]
    unfold cnt
    congr 1
    ext N
    rw [mem_cntFinset, Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc, Set.mem_setOf_eq]
    omega
  have h1 : 1 ≤ Rcnt X := one_le_Rcnt hX
  have h2 : n - 2 ≤ Rcnt X := by
    rw [hRc]
    have a := Finset.pred_card_le_card_erase (s := (Finset.Icc 1 n).erase 2) (a := 5)
    have b := Finset.pred_card_le_card_erase (s := Finset.Icc 1 n) (a := 2)
    rw [Nat.card_Icc] at b
    omega
  have h3 : 3 ≤ n → 2 ≤ Rcnt X := by
    intro h
    rw [hRc]
    have hsub : ({1, 3} : Finset ℕ) ⊆ ((Finset.Icc 1 n).erase 2).erase 5 := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc]
      omega
    exact le_trans (by decide) (Finset.card_le_card hsub)
  rcases Nat.lt_or_ge n 3 with h | h
  · have : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    have : (1 : ℝ) ≤ Rcnt X := by exact_mod_cast h1
    linarith
  · rcases Nat.lt_or_ge n 4 with h' | h'
    · have hn3 : (n : ℝ) = 3 := by exact_mod_cast (by omega : n = 3)
      have : (2 : ℝ) ≤ Rcnt X := by exact_mod_cast h3 h
      linarith
    · have : ((n - 2 : ℕ) : ℝ) ≤ Rcnt X := by exact_mod_cast h2
      have e : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have : (4 : ℝ) ≤ n := by exact_mod_cast h'
      linarith

/-- The uniform lower tail (EP1054.tex lines 3001–3006). -/
theorem link_Step_DaddLowerTailUniform :
    Principia.Erdos1054.Spine.Link_Step_DaddLowerTailUniform := by
  rintro ⟨c, hc, C, δ₀, hδ₀, hU⟩ hXR
  refine ⟨c, hc, 3 * max C 0, -Real.log δ₀, fun u hu X hX => ?_⟩
  have hδ : 0 < Real.exp (-u) := Real.exp_pos _
  have hδle : Real.exp (-u) ≤ δ₀ := by
    rw [← Real.exp_log hδ₀]
    exact Real.exp_le_exp.2 (by linarith)
  have hcnt := hU _ hδ hδle X hX
  have hR1 : (1 : ℝ) ≤ Rcnt X := by exact_mod_cast one_le_Rcnt hX
  have hRpos : (0 : ℝ) < Rcnt X := by linarith
  have hset : {N : ℕ | N ∈ R ∧ ratioE N ∈ Set.Iic (ENNReal.ofReal (Real.exp (-u)))} =
      smallRatioSet (Real.exp (-u)) := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_Iic, smallRatioSet, ratioE]
    constructor
    · rintro ⟨hN, h⟩
      refine ⟨hN, ?_⟩
      have hNpos : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hN
      rw [ENNReal.ofReal_le_ofReal_iff hδ.le, div_le_iff₀ hNpos] at h
      exact h
    · rintro ⟨hN, h⟩
      refine ⟨hN, ?_⟩
      have hNpos : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hN
      rw [ENNReal.ofReal_le_ofReal_iff hδ.le, div_le_iff₀ hNpos]
      exact h
  have hreal : (nuX X).real (Set.Iic (ENNReal.ofReal (Real.exp (-u)))) =
      (cnt (smallRatioSet (Real.exp (-u))) X : ℝ) / Rcnt X := by
    rw [measureReal_def, nuX_apply, hset, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    ring
  rw [hreal, div_le_iff₀ hRpos]
  have hpow : (1 / Real.exp (-u)) ^ c = Real.exp (c * u) := by
    rw [one_div, ← Real.exp_neg, neg_neg, ← Real.exp_mul, mul_comm u c]
  rw [hpow] at hcnt
  have hE : 0 ≤ Real.exp (-Real.exp (Real.exp (c * u))) := (Real.exp_pos _).le
  have hX3 := hXR X hX
  have hX0 : 0 ≤ X := by linarith
  calc (cnt (smallRatioSet (Real.exp (-u))) X : ℝ)
      ≤ C * X * Real.exp (-Real.exp (Real.exp (c * u))) := hcnt
    _ ≤ max C 0 * X * Real.exp (-Real.exp (Real.exp (c * u))) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (3 * Rcnt X) * Real.exp (-Real.exp (Real.exp (c * u))) := by
        gcongr
    _ = 3 * max C 0 * Real.exp (-Real.exp (Real.exp (c * u))) * Rcnt X := by ring

/-- A σ-compact Lebesgue-null carrier of the Davenport law in `[1, ∞)` (EP1054.tex lines
2858–2862), from Erdős's singularity theorem and inner regularity. -/
theorem link_Step_DaddSingularCarrier :
    Principia.Erdos1054.Spine.Link_Step_DaddSingularCarrier := by
  rintro ⟨hD, -, -⟩ hErd
  obtain ⟨hprob, hdens⟩ := hD
  haveI := hprob
  set D := davenportLaw with hDdef
  obtain ⟨S, hSm, hDS, hvolS⟩ := hErd D hprob hdens
  have hIio : D (Set.Iio 1) = 0 := davenport_Iio_one hdens
  set T := Sᶜ ∩ Set.Ici (1 : ℝ) with hTdef
  have hTm : MeasurableSet T := hSm.compl.inter measurableSet_Ici
  have hTc : D Tᶜ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hDS hIio)
    intro x hx
    rw [hTdef, Set.compl_inter, compl_compl] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simpa using hx)
  have hT1 : D T = 1 := by
    have h := prob_compl_eq_one_sub (μ := D) hTm.compl
    rw [compl_compl, hTc, tsub_zero] at h
    exact h
  have hK : ∀ n : ℕ, ∃ K ⊆ T, IsCompact K ∧ D T < D K + (n : ℝ≥0∞)⁻¹ :=
    fun n => hTm.exists_isCompact_lt_add (measure_ne_top _ _)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose K hKT hKc hKlt using hK
  refine ⟨⋃ n, K n, ?_, isSigmaCompact_iUnion_of_isCompact _ hKc, ?_, ?_⟩
  · exact Set.iUnion_subset (fun n => (hKT n).trans Set.inter_subset_right)
  · exact measure_mono_null (Set.iUnion_subset (fun n => (hKT n).trans Set.inter_subset_left))
      hvolS
  · refine le_antisymm prob_le_one (ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_))
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    calc (1 : ℝ≥0∞) = D T := hT1.symm
      _ ≤ D (K n) + (n : ℝ≥0∞)⁻¹ := (hKlt n).le
      _ ≤ D (⋃ n, K n) + ε := add_le_add (measure_mono (Set.subset_iUnion K n)) hn.le

/-- The witness measure is carried by a σ-compact Lebesgue-null set (EP1054.tex lines
2880–2892). -/
theorem link_Step_DaddWitnessCarrier :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessCarrier := by
  rintro ⟨⟨hprob, -⟩, -, -⟩ hdom K _ hKsc hKnull hDK
  haveI := hprob
  have hKm : MeasurableSet K := hKsc.measurableSet'
  have hDKc : davenportLaw Kᶜ = 0 := by
    rw [prob_compl_eq_one_sub hKm, hDK, tsub_self]
  have hsc : IsSigmaCompact (witnessCarrier K) := by
    apply isSigmaCompact_iUnion
    intro e'
    apply isSigmaCompact_iUnion
    intro a
    by_cases ha : a ∈ witnessResidues (e' + 1)
    · simp only [ha, Set.iUnion_true]
      apply isSigmaCompact_iUnion
      intro j'
      apply IsSigmaCompact.image_of_continuousOn (hKsc.inter_isClosed' isClosed_Icc)
      refine ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const) ?_
      rintro h ⟨_, h1, _⟩
      have : 0 < 1 / ((j' : ℝ) + 1) := by positivity
      have : 0 < h - cRes (e' + 1) a := by linarith
      exact this.ne'
    · simp only [ha, Set.iUnion_false, isSigmaCompact_empty]
  refine ⟨?_, hsc, ?_, ?_⟩
  · intro x hx
    simp only [witnessCarrier, Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨e', a, _, j', h, ⟨_, hh1, _⟩, rfl⟩ := hx
    show 0 < 1 / (h - cRes (e' + 1) a)
    have : 0 < 1 / ((j' : ℝ) + 1) := by positivity
    have : 0 < h - cRes (e' + 1) a := by linarith
    positivity
  · apply measure_iUnion_null
    intro e'
    apply measure_iUnion_null
    intro a
    apply measure_iUnion_null
    intro _
    apply measure_iUnion_null
    intro j'
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    · refine DifferentiableOn.div (differentiableOn_const 1)
        (differentiableOn_id.sub (differentiableOn_const _)) ?_
      rintro h ⟨_, h1, _⟩
      have : 0 < 1 / ((j' : ℝ) + 1) := by positivity
      have : 0 < h - cRes (e' + 1) a := by linarith
      exact this.ne'
    · exact measure_mono_null Set.inter_subset_left hKnull
  · have hZm : MeasurableSet (witnessCarrier K) := hsc.measurableSet'
    have hBm : MeasurableSet {x : ℝ≥0∞ | x = 0 ∨ x = ⊤ ∨ x.toReal ∉ witnessCarrier K} :=
      (measurableSet_singleton 0).union
        ((measurableSet_singleton ⊤).union (ENNReal.measurable_toReal hZm.compl))
    rw [witnessMeasure, Measure.sum_apply_eq_zero]
    intro e'
    rw [Measure.finsetSum_apply]
    refine Finset.sum_eq_zero (fun a ha => ?_)
    set c := cRes (e' + 1) a with hcdef
    have hpsi : Measurable (psiE c) :=
      ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.sub_const c))
    rw [witnessPiece, Measure.map_apply hpsi hBm]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (hpsi hBm)]
    have hle : progLaw (e' + 1) a Kᶜ = 0 :=
      nonpos_iff_eq_zero.1
        ((Measure.le_iff'.1 ((hdom (e' + 1) (by omega)).2 a) Kᶜ).trans_eq hDKc)
    refine measure_mono_null ?_ hle
    rintro h ⟨hB, hhc⟩ hK
    have hhc' : c < h := hhc
    have hpos : 0 < 1 / (h - c) := one_div_pos.2 (sub_pos.2 hhc')
    have hmem := mem_witnessCarrier ha hK hhc'
    simp only [Set.mem_preimage, Set.mem_setOf_eq, psiE] at hB
    rcases hB with h0 | htop | hZ
    · rw [ENNReal.ofReal_eq_zero] at h0
      linarith
    · exact ENNReal.ofReal_ne_top htop
    · rw [ENNReal.toReal_ofReal hpos.le] at hZ
      exact hZ hmem

/-- `𝒲_X → 𝒲` vaguely on `(0, ∞)` (EP1054.tex lines 2901–2903): the distribution functions
converge at every point, so the restrictions to `[0, c]` converge weakly (π-system criterion on
the intervals `[0, t]`, `(u, t]`, after normalising the masses). -/
theorem link_Step_DaddEmpiricalWitnessVague :
    Principia.Erdos1054.Spine.Link_Step_DaddEmpiricalWitnessVague := by
  intro hWM hMM φ hφ
  obtain ⟨hφc, a, b, _, hsupp⟩ := hφ
  set c' : ℝ≥0∞ := ENNReal.ofReal (max b 1) with hc'
  have hc'top : c' ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨hlimc, hfinc⟩ := tendsto_empWitness_Iic hWM hMM hc'top
  set μs : ℝ → FiniteMeasure ℝ≥0∞ :=
    fun X => resFM (empWitness X) c' (empWitness_Iic_ne_top X hc'top) with hμs
  set μ : FiniteMeasure ℝ≥0∞ := resFM witnessMeasure c' hfinc with hμ
  have hcoeX : ∀ X, (μs X : Measure ℝ≥0∞) = (empWitness X).restrict (Set.Iic c') :=
    fun X => rfl
  have hcoe : (μ : Measure ℝ≥0∞) = witnessMeasure.restrict (Set.Iic c') := rfl
  set S : Set (Set ℝ≥0∞) :=
    {s | ∃ t : ℝ≥0∞, s = Set.Iic t} ∪ {s | ∃ u t : ℝ≥0∞, s = Set.Ioc u t} with hSdef
  have hSmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro s (⟨t, rfl⟩ | ⟨u, t, rfl⟩)
    · exact measurableSet_Iic
    · exact measurableSet_Ioc
  have hpi : IsPiSystem S := by
    rintro s (⟨t, rfl⟩ | ⟨u, t, rfl⟩) s' (⟨t', rfl⟩ | ⟨u', t', rfl⟩) _
    · refine Or.inl ⟨min t t', ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, le_min_iff]
    · refine Or.inr ⟨u', min t t', ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
      tauto
    · refine Or.inr ⟨u, min t t', ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
      tauto
    · refine Or.inr ⟨max u u', min t t', ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, le_min_iff, max_lt_iff]
      tauto
  have hnhds : ∀ U : Set ℝ≥0∞, IsOpen U → ∀ x ∈ U, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ U := by
    intro U hU x hx
    have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
    rcases eq_or_ne x 0 with h0 | h0
    · rw [h0] at hUx
      obtain ⟨ε, hε, hεU⟩ := ENNReal.nhds_zero_basis.mem_iff.1 hUx
      obtain ⟨t, ht0, htε⟩ := exists_between hε
      refine ⟨Set.Iic t, Or.inl ⟨t, rfl⟩, ?_, fun y hy => hεU (lt_of_le_of_lt hy htε)⟩
      rw [h0]
      exact mem_of_superset (isOpen_Iio.mem_nhds ht0) Set.Iio_subset_Iic_self
    rcases eq_or_ne x ⊤ with ht | ht
    · rw [ht] at hUx
      obtain ⟨l, hl, hlU⟩ := exists_Ioc_subset_of_mem_nhds hUx ⟨0, ENNReal.zero_lt_top⟩
      refine ⟨Set.Ioc l ⊤, Or.inr ⟨l, ⊤, rfl⟩, ?_, hlU⟩
      rw [Set.Ioc_top, ht]
      exact isOpen_Ioi.mem_nhds hl
    · obtain ⟨l, u', hxlu, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset'
        ⟨0, pos_iff_ne_zero.2 h0⟩ ⟨⊤, lt_top_iff_ne_top.2 ht⟩).1 hUx
      obtain ⟨r, hxr, hru⟩ := exists_between hxlu.2
      exact ⟨Set.Ioc l r, Or.inr ⟨l, r, rfl⟩,
        mem_of_superset (isOpen_Ioo.mem_nhds ⟨hxlu.1, hxr⟩) Set.Ioo_subset_Ioc_self,
        fun y hy => hsub ⟨hy.1, lt_of_le_of_lt hy.2 hru⟩⟩
  -- convergence on `S`, in `ℝ≥0∞`
  have hSE : ∀ s ∈ S, Tendsto (fun X => (μs X : Measure ℝ≥0∞) s) atTop
      (𝓝 ((μ : Measure ℝ≥0∞) s)) := by
    rintro s (⟨t, rfl⟩ | ⟨u, t, rfl⟩)
    · have hτ : min t c' ≠ ⊤ := ne_top_of_le_ne_top hc'top (min_le_right _ _)
      have hr : ∀ ν : Measure ℝ≥0∞,
          ν.restrict (Set.Iic c') (Set.Iic t) = ν (Set.Iic (min t c')) := by
        intro ν
        rw [Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Iic]
      simp only [hcoeX, hcoe, hr]
      exact (tendsto_empWitness_Iic hWM hMM hτ).1
    · simp only [hcoeX, hcoe]
      exact tendsto_restrict_Ioc hWM hMM hc'top u t
  -- and in `ℝ≥0`
  have hSN : ∀ s ∈ S, Tendsto (fun X => μs X s) atTop (𝓝 (μ s)) := by
    intro s hs
    exact (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure ℝ≥0∞) s)).comp (hSE s hs)
  have hmass : Tendsto (fun X => (μs X).mass) atTop (𝓝 μ.mass) := by
    have hE : Tendsto (fun X => (μs X : Measure ℝ≥0∞) Set.univ) atTop
        (𝓝 ((μ : Measure ℝ≥0∞) Set.univ)) := by
      simp only [hcoeX, hcoe, Measure.restrict_apply_univ]
      exact hlimc
    exact (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure ℝ≥0∞) _)).comp hE
  have hconv : Tendsto μs atTop (𝓝 μ) := by
    by_cases h0 : μ = 0
    · have hm0 : μ.mass = 0 := (FiniteMeasure.mass_zero_iff μ).2 h0
      rw [hm0] at hmass
      rw [h0]
      exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
    · have hm0 : μ.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff μ).2 h0
      refine (FiniteMeasure.tendsto_normalize_iff_tendsto h0).1 ⟨?_, hmass⟩
      refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem hpi hSmeas hnhds ?_
      intro s hs
      have hev : ∀ᶠ X in atTop, μs X ≠ 0 :=
        (hmass.eventually_ne hm0).mono (fun X hX => (FiniteMeasure.mass_nonzero_iff _).1 hX)
      rw [FiniteMeasure.normalize_eq_of_nonzero μ h0 s]
      refine Tendsto.congr' ?_ ((hmass.inv₀ hm0).mul (hSN s hs))
      filter_upwards [hev] with X hX
      rw [FiniteMeasure.normalize_eq_of_nonzero (μs X) hX s]
  have hint := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hconv)
    (BoundedContinuousFunction.mkOfCompact ⟨φ, hφc⟩)
  have hzero : ∀ x, x ∉ Set.Iic c' → φ x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    refine (hsupp x hne).2.trans ?_
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hint' : Tendsto (fun X => ∫ x in Set.Iic c', φ x ∂(empWitness X)) atTop
      (𝓝 (∫ x in Set.Iic c', φ x ∂witnessMeasure)) := hint
  simp only [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hint'
  exact hint'

/-- `ν|_{(0,∞)} ≤ 𝒲` for every subsequential limit (EP1054.tex lines 2910–2916). The link's
`Step_DaddWitnessMeasureMass` hypothesis (LEAN-PROGRESS F3) is not used here: the Bochner
encoding of `Step_DaddEmpiricalWitnessVague` already forces `ν` to vanish off the locally finite
region. -/
theorem link_Step_DaddLimitDomination :
    Principia.Erdos1054.Spine.Link_Step_DaddLimitDomination := by
  intro hWD hEV hRF _hWM ν hν
  have hprob := hν.1
  haveI := hprob
  set W := witnessMeasure with hWdef
  set O : Set ℝ≥0∞ := Set.Ioo 0 ⊤ with hOdef
  -- (P) for nonnegative `φ ∈ C_c((0,∞))`
  have hPa : ∀ φ : ℝ≥0∞ → ℝ, IsCcPos φ → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂W := by
    intro φ hφ hφ0
    refine (limit_le_integral hν hWD hEV hRF hφ hφ0).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφ0)
      hφ.1.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  have hPb : ∀ φ : ℝ≥0∞ → ℝ, IsCcPos φ → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂W = ⊤ → ∫⁻ x, ENNReal.ofReal (φ x) ∂ν = 0 := by
    intro φ hφ hφ0 htop
    have h := limit_le_integral hν hWD hEV hRF hφ hφ0
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφ0)
      hφ.1.aestronglyMeasurable, htop, ENNReal.toReal_top, ENNReal.ofReal_zero] at h
    exact nonpos_iff_eq_zero.1 h
  -- (B) open sets
  have hB : ∀ U : Set ℝ≥0∞, IsOpen U → U ⊆ O → ν U ≤ W U := by
    intro U hU hUO
    by_contra hcon
    obtain ⟨F, hFU, hFc, hlt⟩ := hU.exists_lt_isClosed (not_le.1 hcon)
    obtain ⟨φ, hφ, hφ0, hφ1, hφK, hφU⟩ := exists_ccPos_bump hFc.isCompact hU hFU hUO
    have h1 := measure_le_lintegral_bump ν hFc.measurableSet hφK
    have h2 := lintegral_bump_le W hU.measurableSet hφ1 hφU
    exact absurd ((h1.trans (hPa φ hφ hφ0)).trans h2) (not_le.2 hlt)
  -- the good region
  set G : Set ℝ≥0∞ := {x | ∃ V : Set ℝ≥0∞, IsOpen V ∧ V ⊆ O ∧ W V < ⊤ ∧ x ∈ V} with hGdef
  have hGo : IsOpen G := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, hVo, hVO, hVW, hxV⟩
    exact ⟨V, fun y hy => ⟨V, hVo, hVO, hVW, hy⟩, hVo, hxV⟩
  -- (C) bad points are `ν`-null
  have hS : ν (O \ G) = 0 := by
    apply measure_null_of_locally_null
    rintro x ⟨hxO, hxG⟩
    have hx0 : x ≠ 0 := hxO.1.ne'
    have hxt : x ≠ ⊤ := hxO.2.ne
    set r := x.toReal with hrdef
    have hr : 0 < r := ENNReal.toReal_pos hx0 hxt
    have hxr : x = ENNReal.ofReal r := (ENNReal.ofReal_toReal hxt).symm
    set N₁ := Set.Ioo (ENNReal.ofReal (r / 2)) (ENNReal.ofReal (3 * r / 2)) with hN₁
    set K := Set.Icc (ENNReal.ofReal (r / 2)) (ENNReal.ofReal (3 * r / 2)) with hKdef
    set U := Set.Ioo (ENNReal.ofReal (r / 4)) (ENNReal.ofReal (2 * r)) with hUdef
    have hxN : x ∈ N₁ := by
      rw [hxr]
      exact ⟨(ENNReal.ofReal_lt_ofReal_iff hr).2 (by linarith),
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)⟩
    have hUO : U ⊆ O := by
      intro y hy
      exact ⟨lt_of_le_of_lt zero_le hy.1, lt_of_lt_of_le hy.2 le_top⟩
    have hKU : K ⊆ U := by
      intro y hy
      exact ⟨lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)) hy.1,
        lt_of_le_of_lt hy.2 ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))⟩
    have hNK : N₁ ⊆ K := Set.Ioo_subset_Icc_self
    have hWN : W N₁ = ⊤ := by
      by_contra hne
      exact hxG ⟨N₁, isOpen_Ioo, hNK.trans (hKU.trans hUO), lt_top_iff_ne_top.2 hne, hxN⟩
    obtain ⟨φ, hφ, hφ0, _, hφK, _⟩ := exists_ccPos_bump isCompact_Icc isOpen_Ioo hKU hUO
    have hφN : ∀ y ∈ N₁, φ y = 1 := fun y hy => hφK y (hNK hy)
    have hWφ : ∫⁻ y, ENNReal.ofReal (φ y) ∂W = ⊤ :=
      eq_top_iff.2 (hWN ▸ measure_le_lintegral_bump W isOpen_Ioo.measurableSet hφN)
    have hνφ := hPb φ hφ hφ0 hWφ
    refine ⟨N₁, mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hxN), ?_⟩
    exact nonpos_iff_eq_zero.1
      ((measure_le_lintegral_bump ν isOpen_Ioo.measurableSet hφN).trans hνφ.le)
  -- (D) compact sets in the good region
  have hD : ∀ K : Set ℝ≥0∞, IsCompact K → K ⊆ G → ν K ≤ W K := by
    intro K hK hKG
    have hex : ∀ x ∈ K, ∃ V : Set ℝ≥0∞, IsOpen V ∧ V ⊆ O ∧ W V < ⊤ ∧ x ∈ V :=
      fun x hx => hKG hx
    choose! V hVo hVO hVW hxV using hex
    obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover V (fun x hx => (hVo x hx).mem_nhds (hxV x hx))
    set V' := ⋃ x ∈ t, V x with hV'def
    have hV'o : IsOpen V' := isOpen_biUnion (fun x hx => hVo x (htK x hx))
    have hV'O : V' ⊆ O := Set.iUnion₂_subset (fun x hx => hVO x (htK x hx))
    have hV'W : W V' < ⊤ := (measure_biUnion_finset_le t V).trans_lt
      (ENNReal.sum_lt_top.2 (fun x hx => hVW x (htK x hx)))
    haveI : IsFiniteMeasure (W.restrict V') :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hV'W⟩
    by_contra hcon
    have h1 : W.restrict V' K < ν K := by
      rw [Measure.restrict_apply' hV'o.measurableSet, Set.inter_eq_left.2 hKt]
      exact not_le.1 hcon
    obtain ⟨U, hKU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt K (ν K) h1
    rw [Measure.restrict_apply hUo.measurableSet] at hU
    have h2 := hB (U ∩ V') (hUo.inter hV'o) (Set.inter_subset_right.trans hV'O)
    have h3 : ν K ≤ ν (U ∩ V') := measure_mono (Set.subset_inter hKU hKt)
    exact absurd (h3.trans h2) (not_le.2 hU)
  -- (E) all measurable sets
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.restrict_apply hA]
  have hsplit : ν (A ∩ O) ≤ ν (A ∩ O ∩ G) := by
    calc ν (A ∩ O) ≤ ν (A ∩ O ∩ G ∪ O \ G) := by
          apply measure_mono
          intro x hx
          by_cases hxG : x ∈ G
          · exact Or.inl ⟨hx, hxG⟩
          · exact Or.inr ⟨hx.2, hxG⟩
      _ ≤ ν (A ∩ O ∩ G) + ν (O \ G) := measure_union_le _ _
      _ = ν (A ∩ O ∩ G) := by rw [hS, add_zero]
  refine hsplit.trans (le_of_forall_lt (fun q hq => ?_))
  have hm : MeasurableSet (A ∩ O ∩ G) :=
    (hA.inter isOpen_Ioo.measurableSet).inter hGo.measurableSet
  obtain ⟨F, hFsub, hFc, hqF⟩ := hm.exists_lt_isClosed_of_ne_top (measure_ne_top _ _) hq
  calc q < ν F := hqF
    _ ≤ W F := hD F hFc.isCompact (hFsub.trans Set.inter_subset_right)
    _ ≤ W A := measure_mono (hFsub.trans (Set.inter_subset_left.trans Set.inter_subset_left))

/-- **Theorem `thm:dadd:universal-singularity`, main display** (EP1054.tex lines 2839–2848,
proof 2857–2934). -/
theorem link_Thm_DaddUniversalSingularity_Carrier :
    Principia.Erdos1054.Spine.Link_Thm_DaddUniversalSingularity_Carrier := by
  intro hSC hWC hLD hWMM hCD hRF hWM hSV _
  obtain ⟨K, hK1, hKsc, hKnull, hDK⟩ := hSC
  obtain ⟨hZpos, hZsc, hZnull, hZW⟩ := hWC K hK1 hKsc hKnull hDK
  refine ⟨witnessCarrier K, hZpos, hZsc, hZnull, fun ν hν => ?_⟩
  have hdom := hLD ν hν
  obtain ⟨hprob, X, hW⟩ := hν
  haveI := hprob
  have hport := portmanteau hW
  have hXev : ∀ᶠ j in atTop, 1 ≤ X j := hW.1.eventually_ge_atTop 1
  have hrestr : ∀ s ⊆ Set.Ioo (0 : ℝ≥0∞) ⊤, ν s ≤ witnessMeasure s := by
    intro s hs
    calc ν s = ν.restrict (Set.Ioo 0 ⊤) s := (Measure.restrict_eq_self ν hs).symm
      _ ≤ witnessMeasure s := Measure.le_iff'.1 hdom s
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `0 ∈ supp ν`, via Theorem 1.2 and closed-set portmanteau
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := ENNReal.nhds_zero_basis.mem_iff.1 hU
    obtain ⟨δ, _, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
    obtain ⟨c, hc, X₀, hX₀⟩ := hSV δ hδ
    have hev : ∀ᶠ j in atTop, ENNReal.ofReal c ≤ nuX (X j) (Set.Iic (ENNReal.ofReal δ)) := by
      filter_upwards [hXev, hW.1.eventually_ge_atTop X₀] with j hj1 hj0
      rw [nuX_Iic (X j) hj1 hδ]
      apply ENNReal.ofReal_le_ofReal
      have hR : (0 : ℝ) < Rcnt (X j) := by exact_mod_cast one_le_Rcnt hj1
      rw [le_div_iff₀ hR]
      have h1 := hX₀ (X j) hj0
      have h2 := Rcnt_le (X := X j) (by linarith)
      nlinarith
    have hlim : ENNReal.ofReal c ≤ ν (Set.Iic (ENNReal.ofReal δ)) :=
      (le_limsup_of_frequently_le' hev.frequently).trans (hport.2 _ isClosed_Iic)
    have hsub : Set.Iic (ENNReal.ofReal δ) ⊆ U := fun x hx => hεU (lt_of_le_of_lt hx hδε)
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc) (hlim.trans (measure_mono hsub))
  · -- `ν{0} = 0`, via witness domination near `0` and open-set portmanteau
    have hbound : ∀ t : ℝ, 0 < t → ν {0} ≤ ENNReal.ofReal (Wfun t) := by
      intro t ht
      have hA : Tendsto (fun Y : ℝ =>
          (Y / (Rcnt Y : ℝ)) * ((1 / Y) * ∑ N ∈ Finset.Icc 1 ⌊Y⌋₊, (rt t N : ℝ))) atTop
          (𝓝 (1 * Wfun t)) :=
        (tendsto_X_div_Rcnt hRF).mul (hWM.1 t ht).1
      rw [one_mul] at hA
      have hB := (ENNReal.tendsto_ofReal hA).comp hW.1
      have hev : ∀ᶠ j in atTop, nuX (X j) (Set.Iio (ENNReal.ofReal t)) ≤
          ENNReal.ofReal ((X j / (Rcnt (X j) : ℝ)) *
            ((1 / X j) * ∑ N ∈ Finset.Icc 1 ⌊X j⌋₊, (rt t N : ℝ))) := by
        filter_upwards [hXev] with j hj
        obtain ⟨h1, h2⟩ := hCD t ht (X j) hj
        have hR : (0 : ℝ) < Rcnt (X j) := by exact_mod_cast one_le_Rcnt hj
        rw [ENNReal.ofReal_mul (div_nonneg (by linarith) hR.le)]
        exact h1.trans (mul_le_mul_right h2 _)
      calc ν {0} ≤ ν (Set.Iio (ENNReal.ofReal t)) := by
            apply measure_mono
            intro x hx
            rw [Set.mem_singleton_iff] at hx
            rw [hx, Set.mem_Iio]
            exact ENNReal.ofReal_pos.2 ht
        _ ≤ liminf (fun j => nuX (X j) (Set.Iio (ENNReal.ofReal t))) atTop :=
            hport.1 _ isOpen_Iio
        _ ≤ liminf (fun j => ENNReal.ofReal ((X j / (Rcnt (X j) : ℝ)) *
              ((1 / X j) * ∑ N ∈ Finset.Icc 1 ⌊X j⌋₊, (rt t N : ℝ)))) atTop :=
            liminf_le_liminf hev
        _ = ENNReal.ofReal (Wfun t) := hB.liminf_eq
    have hW0 : Tendsto (fun t => ENNReal.ofReal (Wfun t)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal hWM.2.2.2.2
    rw [ENNReal.ofReal_zero] at hW0
    exact nonpos_iff_eq_zero.1 (ge_of_tendsto hW0
      (eventually_nhdsWithin_of_forall (fun t ht => hbound t ht)))
  · -- no mass off the carrier in `(0, ∞)`
    have hsub : {x : ℝ≥0∞ | x ≠ 0 ∧ x ≠ ⊤ ∧ x.toReal ∉ witnessCarrier K} ⊆ Set.Ioo 0 ⊤ :=
      fun x hx => ⟨pos_iff_ne_zero.2 hx.1, lt_top_iff_ne_top.2 hx.2.1⟩
    refine nonpos_iff_eq_zero.1 ((hrestr _ hsub).trans ?_)
    rw [← hZW]
    apply measure_mono
    intro x hx
    exact Or.inr (Or.inr hx.2.2)
  · -- no finite positive atoms
    intro x hx0 hxt
    have hsub : ({x} : Set ℝ≥0∞) ⊆ Set.Ioo 0 ⊤ := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨pos_iff_ne_zero.2 hx0, lt_top_iff_ne_top.2 hxt⟩
    exact nonpos_iff_eq_zero.1 ((hrestr _ hsub).trans (hWMM.2 x).le)

/-- The finite part of every subsequential limit is nonzero, atomless and singular
(EP1054.tex lines 2849–2850, 2934–2935). -/
theorem link_Thm_DaddUniversalSingularity_FinitePart :
    Principia.Erdos1054.Spine.Link_Thm_DaddUniversalSingularity_FinitePart := by
  rintro ⟨Z, _, hZsc, hZnull, hZ⟩ ν hν
  obtain ⟨hsupp, h0, hoff, hatom⟩ := hZ ν hν
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : 0 < ν (Set.Iio 1) :=
      (Measure.mem_support_iff_forall _).1 hsupp _ (Iio_mem_nhds zero_lt_one)
    have h2 : ν (Set.Iio 1) ≤ finitePart ν (Set.Iio 1) := by
      rw [finitePart_apply ν measurableSet_Iio]
      apply measure_mono
      intro x hx
      have hx1 : x < 1 := hx
      have hxt : x ≠ ⊤ := ne_top_of_lt hx1
      refine ⟨hxt, ?_⟩
      show x.toReal < 1
      have := (ENNReal.toReal_lt_toReal hxt ENNReal.one_ne_top).2 hx1
      simpa using this
    rw [h, Measure.coe_zero, Pi.zero_apply] at h2
    exact absurd (le_antisymm h2 zero_le) h1.ne'
  · constructor
    intro r
    rw [finitePart_apply ν (measurableSet_singleton r)]
    rcases lt_trichotomy r 0 with hr | hr | hr
    · apply measure_mono_null _ measure_empty
      rintro x ⟨_, hx2⟩
      have : x.toReal = r := hx2
      have := ENNReal.toReal_nonneg (a := x)
      exact absurd hr (by linarith)
    · apply measure_mono_null _ h0
      rintro x ⟨hx1, hx2⟩
      have hx2' : x.toReal = 0 := by rw [← hr]; exact hx2
      rcases (ENNReal.toReal_eq_zero_iff x).1 hx2' with h | h
      · exact h
      · exact absurd h hx1
    · have hne0 : ENNReal.ofReal r ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hr
      apply measure_mono_null _ (hatom (ENNReal.ofReal r) hne0 ENNReal.ofReal_ne_top)
      rintro x ⟨hx1, hx2⟩
      have hx2' : x.toReal = r := hx2
      show x = ENNReal.ofReal r
      rw [← hx2', ENNReal.ofReal_toReal hx1]
  · have hZm : MeasurableSet Z := hZsc.measurableSet'
    refine Measure.MutuallySingular.mk (s := Zᶜ) (t := Z) ?_ hZnull
      (by
        intro x _
        by_cases hx : x ∈ Z
        · exact Or.inr hx
        · exact Or.inl hx)
    rw [finitePart_apply ν hZm.compl]
    apply measure_mono_null _ (measure_union_null h0 hoff)
    rintro x ⟨hx1, hx2⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr ⟨hx0, hx1, hx2⟩

/-- Under the tightness criterion every subsequential limit is a singular continuous probability
law on `[0, ∞)` (EP1054.tex lines 2850–2854, 2935–2937). -/
theorem link_Thm_DaddUniversalSingularity_Tight :
    Principia.Erdos1054.Spine.Link_Thm_DaddUniversalSingularity_Tight := by
  intro hTE hFP _ hcrit ν hν
  have hν' := hν
  obtain ⟨hprob, X, hW⟩ := hν
  have hNT : Coverage.NuTight := hTE.1.2 hcrit
  have hport := portmanteau hW
  have hXev : ∀ᶠ j in atTop, 1 ≤ X j := hW.1.eventually_ge_atTop 1
  have hbound : ∀ T : ℝ,
      ν {⊤} ≤ ⨆ (Y : ℝ) (_ : 1 ≤ Y), nuX Y (Set.Ioi (ENNReal.ofReal T)) := by
    intro T
    calc ν {⊤} ≤ ν (Set.Ioi (ENNReal.ofReal T)) := by
          apply measure_mono
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact ENNReal.ofReal_lt_top
      _ ≤ liminf (fun j => nuX (X j) (Set.Ioi (ENNReal.ofReal T))) atTop := hport.1 _ isOpen_Ioi
      _ ≤ ⨆ (Y : ℝ) (_ : 1 ≤ Y), nuX Y (Set.Ioi (ENNReal.ofReal T)) := by
          apply liminf_le_of_frequently_le'
          refine (hXev.mono (fun j hj => ?_)).frequently
          exact le_iSup₂ (f := fun (Y : ℝ) (_ : 1 ≤ Y) => nuX Y (Set.Ioi (ENNReal.ofReal T)))
            (X j) hj
  have htop : ν {⊤} = 0 :=
    nonpos_iff_eq_zero.1 (ge_of_tendsto hNT (Eventually.of_forall hbound))
  obtain ⟨_, hNA, hsing⟩ := hFP ν hν'
  have hprobFP : IsProbabilityMeasure (finitePart ν) := by
    constructor
    rw [finitePart_apply ν MeasurableSet.univ, Set.preimage_univ, Set.inter_univ,
      prob_compl_eq_one_sub (measurableSet_singleton _), htop, tsub_zero]
  refine ⟨htop, hprobFP, hNA, hsing, ?_⟩
  rintro ⟨ρ, hρ⟩
  have hac : finitePart ν ≪ volume := by
    rw [hρ]
    exact withDensity_absolutelyContinuous _ _
  have h0 := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hac hsing
  have h1 := hprobFP.measure_univ
  rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- `eq:dadd:subsequential-tail` (EP1054.tex lines 2942–2950, proof 2977–2985). -/
theorem link_Eq_DaddSubsequentialTail :
    Principia.Erdos1054.Spine.Link_Eq_DaddSubsequentialTail := by
  intro hALT hCar _ ν hν ε hε
  obtain ⟨Z, _, _, _, hZ⟩ := hCar
  obtain ⟨_, _, _, hatom⟩ := hZ ν hν
  obtain ⟨hprob, X, hW⟩ := hν
  haveI := hprob
  have hport := portmanteau hW
  have hXev : ∀ᶠ j in atTop, 1 ≤ X j := hW.1.eventually_ge_atTop 1
  obtain ⟨T₀, hT₀⟩ := hALT ε hε
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  set S := {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * N < (f N : ℝ)} with hSdef
  have hL := hT₀ T (le_trans (le_max_left _ _) hT)
  have hIci : ν (Set.Ici (ENNReal.ofReal T)) = ν (Set.Ioi (ENNReal.ofReal T)) := by
    refine le_antisymm ?_ (measure_mono Set.Ioi_subset_Ici_self)
    rw [← Set.Ioi_insert, Set.insert_eq]
    refine (measure_union_le _ _).trans ?_
    have hne0 : ENNReal.ofReal T ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hTpos
    rw [hatom _ hne0 ENNReal.ofReal_ne_top, zero_add]
  have key : ∀ η : ℝ, 0 < η →
      ENNReal.ofReal (lowerDens S - η) ≤ ν (Set.Ioi (ENNReal.ofReal T)) := by
    intro η hη
    obtain ⟨X₀, hX₀⟩ := exists_mul_le_cnt_of_lt_lowerDens (S := S) (c := lowerDens S - η)
      (by linarith)
    have hev : ∀ᶠ j in atTop,
        ENNReal.ofReal (lowerDens S - η) ≤ nuX (X j) (Set.Ici (ENNReal.ofReal T)) := by
      filter_upwards [hXev, hW.1.eventually_ge_atTop X₀] with j hj1 hj0
      have hX0 : 0 < X j := by linarith
      refine le_trans ?_ ((ofReal_cnt_div_le_nuX hj1 (largeSet_sub hTpos.le)).trans
        (measure_mono Set.Ioi_subset_Ici_self))
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hX0]
      exact hX₀ (X j) hj0
    rw [← hIci]
    exact (le_limsup_of_frequently_le' hev.frequently).trans (hport.2 _ isClosed_Ici)
  have hmain : ENNReal.ofReal (lowerDens S) ≤ ν (Set.Ioi (ENNReal.ofReal T)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun η hη _ => ?_)
    calc ENNReal.ofReal (lowerDens S)
        ≤ ENNReal.ofReal (lowerDens S - η + η) := by rw [sub_add_cancel]
      _ ≤ ENNReal.ofReal (lowerDens S - η) + ENNReal.ofReal η := ENNReal.ofReal_add_le
      _ ≤ ν (Set.Ioi (ENNReal.ofReal T)) + η := by
          rw [ENNReal.ofReal_coe_nnreal]
          exact add_le_add (key η (by exact_mod_cast hη)) le_rfl
  have hreal : lowerDens S ≤ ν.real (Set.Ioi (ENNReal.ofReal T)) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hmain
  exact hL.trans hreal

/-- Divergence of positive moments (EP1054.tex lines 2951–2956, proof 2986–2988). -/
theorem link_Cor_DaddHeavyTails_PosMoments :
    Principia.Erdos1054.Spine.Link_Cor_DaddHeavyTails_PosMoments := by
  intro hALT hST s hs
  set κ : ℝ := Real.exp (-eulerGamma) / 4 with hκ
  have hκpos : 0 < κ := by positivity
  have hκeq : Real.exp (-eulerGamma) / 2 - κ = κ := by rw [hκ]; ring
  refine ⟨?_, ?_⟩
  · rw [ENNReal.tendsto_nhds_top_iff_nnreal]
    intro r
    obtain ⟨T₀, hT₀⟩ := hALT κ hκpos
    set y : ℝ := max (max 1 T₀) (12 * ((r : ℝ) + 1) / (κ * s ^ 3)) with hy
    have hy1 : 1 ≤ y := le_trans (le_max_left _ _) (le_max_left _ _)
    set T : ℝ := Real.exp (Real.exp (Real.exp y)) with hT
    have hTy : y ≤ T := by
      have h1 := Real.add_one_le_exp y
      have h2 := Real.add_one_le_exp (Real.exp y)
      have h3 := Real.add_one_le_exp (Real.exp (Real.exp y))
      rw [hT]
      linarith
    have hTT₀ : T₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTy
    have hT0 : 0 ≤ T := by linarith
    set S := {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * N < (f N : ℝ)} with hSdef
    have hL : κ * Lscale T ≤ lowerDens S := by
      have := hT₀ T hTT₀
      rwa [hκeq] at this
    have hLs : 0 < Lscale T := by
      rw [hT, Lscale_exp3]
      have : 0 < y := by linarith
      positivity
    have hLpos : 0 < κ * Lscale T := mul_pos hκpos hLs
    obtain ⟨X₀, hX₀⟩ := exists_mul_le_cnt_of_lt_lowerDens (S := S) (c := κ * Lscale T / 2)
      (by linarith)
    have hbig := rpow_Lscale_ge hs hy1
    rw [← hT] at hbig
    filter_upwards [eventually_ge_atTop (max X₀ 1)] with Z hZ
    have hZ1 : 1 ≤ Z := le_trans (le_max_right _ _) hZ
    have hZ0 : 0 < Z := by linarith
    have hnu : ENNReal.ofReal (κ * Lscale T / 2) ≤ nuX Z (Set.Ioi (ENNReal.ofReal T)) := by
      refine le_trans ?_ (ofReal_cnt_div_le_nuX hZ1 (largeSet_sub hT0))
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hZ0]
      exact hX₀ Z (le_trans (le_max_left _ _) hZ)
    refine lt_of_lt_of_le ?_ ((mul_le_mul_right hnu _).trans (lintegral_rpow_ge _ hT0 hs.le))
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hyr : 12 * ((r : ℝ) + 1) / (κ * s ^ 3) ≤ y := le_max_right _ _
    have hks : 0 < κ * s ^ 3 := by positivity
    rw [div_le_iff₀ hks] at hyr
    nlinarith
  · intro ν hν
    haveI := hν.1
    obtain ⟨T₀, hT₀⟩ := hST ν hν κ hκpos
    refine ENNReal.eq_top_of_forall_nnreal_le (fun r => ?_)
    set y : ℝ := max (max 1 T₀) (6 * (r : ℝ) / (κ * s ^ 3)) with hy
    have hy1 : 1 ≤ y := le_trans (le_max_left _ _) (le_max_left _ _)
    set T : ℝ := Real.exp (Real.exp (Real.exp y)) with hT
    have hTy : y ≤ T := by
      have h1 := Real.add_one_le_exp y
      have h2 := Real.add_one_le_exp (Real.exp y)
      have h3 := Real.add_one_le_exp (Real.exp (Real.exp y))
      rw [hT]
      linarith
    have hTT₀ : T₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTy
    have hT0 : 0 ≤ T := by linarith
    have hL : κ * Lscale T ≤ ν.real (Set.Ioi (ENNReal.ofReal T)) := by
      have := hT₀ T hTT₀
      rwa [hκeq] at this
    have hnu : ENNReal.ofReal (κ * Lscale T) ≤ ν (Set.Ioi (ENNReal.ofReal T)) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hL
    have hbig := rpow_Lscale_ge hs hy1
    rw [← hT] at hbig
    refine le_trans ?_ ((mul_le_mul_right hnu _).trans (lintegral_rpow_ge _ hT0 hs.le))
    have hLs : 0 < Lscale T := by
      rw [hT, Lscale_exp3]
      have : 0 < y := by linarith
      positivity
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hyr : 6 * (r : ℝ) / (κ * s ^ 3) ≤ y := le_max_right _ _
    have hks : 0 < κ * s ^ 3 := by positivity
    rw [div_le_iff₀ hks] at hyr
    nlinarith

/-- Logarithmic means diverge (EP1054.tex lines 2957–2962, proof 2990–3013). -/
theorem link_Cor_DaddHeavyTails_LogMeans :
    Principia.Erdos1054.Spine.Link_Cor_DaddHeavyTails_LogMeans := by
  intro hALT hST hLTU
  obtain ⟨c, hc, C, u₀, hU⟩ := hLTU
  set κ : ℝ := Real.exp (-eulerGamma) / 4 with hκ
  have hκpos : 0 < κ := by positivity
  have hκeq : Real.exp (-eulerGamma) / 2 - κ = κ := by rw [hκ]; ring
  have hq : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    linarith
  have hβsum : Summable (fun j => betaSeq c C u₀ j) :=
    (summable_betaSeq hc C u₀ 0).congr (fun j => by simp)
  set B : ℝ := ∑' j, betaSeq c C u₀ j with hB
  have hB0 : 0 ≤ B := tsum_nonneg (betaSeq_nonneg c C u₀)
  have hLpos : ∀ k : ℕ, 2 ≤ k → 0 < Lscale (Tk k) := by
    intro k hk
    have h1 := wt_mul_Lscale_ge hk
    have h2 : 0 < (1 - Real.exp (-1)) * (1 / ((k : ℝ) + 1)) := by positivity
    by_contra hcon
    have : wt k * Lscale (Tk k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (wt_nonneg k) (not_lt.1 hcon)
    linarith
  have hTk : ∀ T₀ : ℝ, ∀ k : ℕ, ⌈T₀⌉₊ ≤ k → T₀ ≤ Tk k := by
    intro T₀ k hk
    have h1 : T₀ ≤ k := (Nat.le_ceil T₀).trans (by exact_mod_cast hk)
    have h2 := Real.add_one_le_exp ((k : ℝ) + 1)
    have h3 := Real.add_one_le_exp (Real.exp ((k : ℝ) + 1))
    unfold Tk
    linarith
  -- the layer-cake lower bound, summed with weights `a • L(T_k)`
  have hsumlow : ∀ (k₀ K : ℕ) (a V : ℝ), 2 ≤ k₀ → 0 < a →
      V / (a * (1 - Real.exp (-1))) ≤ ∑ k ∈ Finset.Ico k₀ K, 1 / ((k : ℝ) + 1) →
      V ≤ ∑ k ∈ Finset.Ico k₀ K, wt k * (a * Lscale (Tk k)) := by
    intro k₀ K a V hk₀ ha hK
    have hA : (a * (1 - Real.exp (-1))) * ∑ k ∈ Finset.Ico k₀ K, 1 / ((k : ℝ) + 1) ≤
        ∑ k ∈ Finset.Ico k₀ K, wt k * (a * Lscale (Tk k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have := wt_mul_Lscale_ge (k := k) (le_trans hk₀ (Finset.mem_Ico.1 hk).1)
      calc a * (1 - Real.exp (-1)) * (1 / ((k : ℝ) + 1))
          = a * ((1 - Real.exp (-1)) * (1 / ((k : ℝ) + 1))) := by ring
        _ ≤ a * (wt k * Lscale (Tk k)) := mul_le_mul_of_nonneg_left this ha.le
        _ = wt k * (a * Lscale (Tk k)) := by ring
    rw [div_le_iff₀ (by positivity)] at hK
    linarith
  refine ⟨?_, fun ν hν => ⟨?_, ?_⟩⟩
  · rw [tendsto_atTop]
    intro M
    obtain ⟨T₀, hT₀⟩ := hALT κ hκpos
    set k₀ := max 2 ⌈T₀⌉₊ with hk₀
    obtain ⟨K, _, hK⟩ := harmonic_Ico_unbounded k₀ ((M + B + 1) / (κ / 2 * (1 - Real.exp (-1))))
    have hev : ∀ᶠ X : ℝ in atTop, ∀ k ∈ Finset.Ico k₀ K,
        κ / 2 * Lscale (Tk k) * X ≤
          cnt {N : ℕ | N ∈ R ∧ Squarefree N ∧ Tk k * N < (f N : ℝ)} X := by
      rw [eventually_all_finset]
      intro k hk
      have hk' : k₀ ≤ k := (Finset.mem_Ico.1 hk).1
      have h2 : 2 ≤ k := le_trans (le_max_left _ _) hk'
      have hL : κ * Lscale (Tk k) ≤
          lowerDens {N : ℕ | N ∈ R ∧ Squarefree N ∧ Tk k * N < (f N : ℝ)} := by
        have := hT₀ (Tk k) (hTk T₀ k (le_trans (le_max_right _ _) hk'))
        rwa [hκeq] at this
      have hLk := hLpos k h2
      obtain ⟨X₀, hX₀⟩ := exists_mul_le_cnt_of_lt_lowerDens
        (S := {N : ℕ | N ∈ R ∧ Squarefree N ∧ Tk k * N < (f N : ℝ)})
        (c := κ / 2 * Lscale (Tk k)) (by nlinarith)
      exact eventually_atTop.2 ⟨X₀, hX₀⟩
    filter_upwards [hev, eventually_ge_atTop 1] with X hX hX1
    have hX0 : 0 < X := by linarith
    have hmeas : Measurable (fun x : ℝ≥0∞ => Real.log x.toReal) :=
      Real.measurable_log.comp ENNReal.measurable_toReal
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_nuX hX1 hmeas)]
    have hR : (Rcnt X : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by have := one_le_Rcnt hX1; omega)
    have hPfin : ∫⁻ x, ENNReal.ofReal (Real.log x.toReal) ∂(nuX X) ≠ ⊤ := by
      rw [lintegral_nuX]
      exact (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hR))
        (ENNReal.sum_lt_top.2 (fun N _ => ENNReal.ofReal_lt_top))).ne
    have hQ : ∫⁻ x, ENNReal.ofReal (-Real.log x.toReal) ∂(nuX X) ≤ ENNReal.ofReal B := by
      refine (lintegral_mono (fun x => ?_)).trans (lintegral_logNeg_le _
        (nuX_Iio_le_beta hU hX1) (betaSeq_nonneg c C u₀) hβsum)
      by_cases hx0 : x = 0
      · rw [hx0, logNegE, if_pos rfl]
        exact le_top
      · rw [logNegE, if_neg hx0]
    have hP : ENNReal.ofReal (M + B + 1) ≤ ∫⁻ x, ENNReal.ofReal (Real.log x.toReal) ∂(nuX X) := by
      have hlow := hsumlow k₀ K (κ / 2) (M + B + 1) (le_max_left _ _) (by positivity) hK
      calc ENNReal.ofReal (M + B + 1)
          ≤ ENNReal.ofReal (∑ k ∈ Finset.Ico k₀ K, wt k * (κ / 2 * Lscale (Tk k))) :=
            ENNReal.ofReal_le_ofReal hlow
        _ = ∑ k ∈ Finset.Ico k₀ K,
              ENNReal.ofReal (wt k) * ENNReal.ofReal (κ / 2 * Lscale (Tk k)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => mul_nonneg (wt_nonneg k)
              (mul_nonneg (by positivity)
                (hLpos k (le_trans (le_max_left _ _) (Finset.mem_Ico.1 hk).1)).le))]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [ENNReal.ofReal_mul (wt_nonneg k)]
        _ ≤ ∑ k ∈ Finset.Ico k₀ K,
              ENNReal.ofReal (wt k) * nuX X (Set.Ioo (ENNReal.ofReal (Tk k)) ⊤) := by
            refine Finset.sum_le_sum (fun k hk => mul_le_mul' le_rfl ?_)
            refine le_trans ?_ (ofReal_cnt_div_le_nuX hX1 (largeSet_sub_Ioo (Tk_pos k).le))
            apply ENNReal.ofReal_le_ofReal
            rw [le_div_iff₀ hX0]
            exact hX k hk
        _ = ∫⁻ x, ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) *
              (Set.Ioo (ENNReal.ofReal (Tk k)) ⊤).indicator 1 x ∂(nuX X) :=
            (lintegral_sum_wt _ _ _ _ (fun k => measurableSet_Ioo)).symm
        _ ≤ ∫⁻ x, ENNReal.ofReal (Real.log x.toReal) ∂(nuX X) :=
            lintegral_mono (fun x => sum_wt_Ioo_le k₀ K x)
    have h1 := (ENNReal.ofReal_le_iff_le_toReal hPfin).1 hP
    have h2 := ENNReal.toReal_le_of_le_ofReal hB0 hQ
    linarith
  · haveI := hν.1
    obtain ⟨T₀, hT₀⟩ := hST ν hν κ hκpos
    set k₀ := max 2 ⌈T₀⌉₊ with hk₀
    refine ENNReal.eq_top_of_forall_nnreal_le (fun r => ?_)
    obtain ⟨K, _, hK⟩ := harmonic_Ico_unbounded k₀ ((r : ℝ) / (κ * (1 - Real.exp (-1))))
    have hlow := hsumlow k₀ K κ r (le_max_left _ _) hκpos hK
    calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal (∑ k ∈ Finset.Ico k₀ K, wt k * (κ * Lscale (Tk k))) :=
          ENNReal.ofReal_le_ofReal hlow
      _ = ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) * ENNReal.ofReal (κ * Lscale (Tk k)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => mul_nonneg (wt_nonneg k)
            (mul_nonneg hκpos.le
              (hLpos k (le_trans (le_max_left _ _) (Finset.mem_Ico.1 hk).1)).le))]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [ENNReal.ofReal_mul (wt_nonneg k)]
      _ ≤ ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) * ν (Set.Ioi (ENNReal.ofReal (Tk k))) := by
          refine Finset.sum_le_sum (fun k hk => mul_le_mul' le_rfl ?_)
          have hk' : k₀ ≤ k := (Finset.mem_Ico.1 hk).1
          have := hT₀ (Tk k) (hTk T₀ k (le_trans (le_max_right _ _) hk'))
          rw [hκeq] at this
          exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 this
      _ = ∫⁻ x, ∑ k ∈ Finset.Ico k₀ K, ENNReal.ofReal (wt k) *
            (Set.Ioi (ENNReal.ofReal (Tk k))).indicator 1 x ∂ν :=
          (lintegral_sum_wt _ _ _ _ (fun k => measurableSet_Ioi)).symm
      _ ≤ ∫⁻ x, logPosE x ∂ν := lintegral_mono (fun x => sum_wt_Ioi_le k₀ K x)
  · exact (lintegral_logNeg_le ν (limit_Iio_le_beta hU hν) (betaSeq_nonneg c C u₀)
      hβsum).trans_lt ENNReal.ofReal_lt_top

/-- Finiteness of inverse moments (EP1054.tex lines 2963–2969, proof 3015–3020). -/
theorem link_Cor_DaddHeavyTails_InvMoments :
    Principia.Erdos1054.Spine.Link_Cor_DaddHeavyTails_InvMoments := by
  rintro ⟨c, hc, C, u₀, hU⟩ s hs
  have hsum := summable_betaSeq hc C u₀ s
  have hfin : 1 + ENNReal.ofReal (Real.exp s) *
      ENNReal.ofReal (∑' j : ℕ, Real.exp (s * j) * betaSeq c C u₀ j) < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  refine ⟨lt_of_le_of_lt (iSup₂_le (fun X hX => ?_)) hfin, fun ν hν => ?_⟩
  · haveI := nuX_isProb hX
    exact lintegral_rpow_neg_le (nuX X) prob_le_one (nuX_Iio_le_beta hU hX)
      (betaSeq_nonneg c C u₀) hs hsum
  · haveI := hν.1
    exact lt_of_le_of_lt (lintegral_rpow_neg_le ν prob_le_one (limit_Iio_le_beta hU hν)
      (betaSeq_nonneg c C u₀) hs hsum) hfin

/-- Convergence of inverse moments along weakly convergent sequences (EP1054.tex lines 2969–2970,
proof 3021–3025): truncation plus the uniform bound on the `2s`-th inverse moments. -/
theorem link_Cor_DaddHeavyTails_InvMomentConv :
    Principia.Erdos1054.Spine.Link_Cor_DaddHeavyTails_InvMomentConv := by
  intro hInv ν X hprob hW s hs
  haveI := hprob
  obtain ⟨hK, -⟩ := hInv (2 * s) (by positivity)
  set K := ⨆ (Y : ℝ) (_ : 1 ≤ Y), ∫⁻ x, x ^ (-(2 * s)) ∂(nuX Y) with hKdef
  have hXev : ∀ᶠ j in atTop, 1 ≤ X j := hW.1.eventually_ge_atTop 1
  have hmeas : Measurable (fun x : ℝ≥0∞ => x ^ (-s)) := ENNReal.continuous_rpow_const.measurable
  have hB : ∀ n : ℕ, Tendsto (fun j => ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂(nuX (X j))) atTop
      (𝓝 (∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂ν)) := by
    intro n
    have h := weak_lintegral hW (truncRpow s n)
    simp only [truncRpow_apply] at h
    exact h
  have hpt : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ≥0∞,
      x ^ (-s) ≤ min (x ^ (-s)) (n : ℝ≥0∞) + x ^ (-(2 * s)) * (n : ℝ≥0∞)⁻¹ := by
    intro n hn x
    have ha2 : x ^ (-(2 * s)) = (x ^ (-s)) ^ 2 := by
      rw [show -(2 * s) = (-s) * 2 by ring, ENNReal.rpow_mul, ENNReal.rpow_two]
    rw [ha2]
    exact le_min_add_sq _ hn
  have hsup : ∀ a : ℝ≥0∞, (⨆ n : ℕ, min a (n : ℝ≥0∞)) = a := by
    intro a
    refine le_antisymm (iSup_le (fun n => min_le_left _ _)) ?_
    by_cases ha : a = ⊤
    · rw [ha]
      have : ∀ n : ℕ, min (⊤ : ℝ≥0∞) (n : ℝ≥0∞) = n := fun n => min_eq_right le_top
      simp only [this, ENNReal.iSup_natCast, le_refl]
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
      exact le_iSup_of_le n (le_of_eq (min_eq_left hn.le).symm)
  have hlow : ∫⁻ x, x ^ (-s) ∂ν ≤ liminf (fun j => ∫⁻ x, x ^ (-s) ∂(nuX (X j))) atTop := by
    have hA : ∫⁻ x, x ^ (-s) ∂ν = ⨆ n : ℕ, ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂ν := by
      rw [← lintegral_iSup (fun n => hmeas.min measurable_const)
        (fun m n hmn x => min_le_min le_rfl (Nat.cast_le.2 hmn))]
      simp only [hsup]
    rw [hA]
    refine iSup_le (fun n => ?_)
    rw [← (hB n).liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall
      (fun j => lintegral_mono (fun x => min_le_left _ _)))
  have hup : limsup (fun j => ∫⁻ x, x ^ (-s) ∂(nuX (X j))) atTop ≤ ∫⁻ x, x ^ (-s) ∂ν := by
    refine ENNReal.le_of_forall_pos_le_add (fun η hη _ => ?_)
    have hlim0 : Tendsto (fun n : ℕ => K * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hK.ne)
      rwa [mul_zero] at this
    have hη' : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
    obtain ⟨n, hn, hn1⟩ :=
      ((hlim0.eventually (gt_mem_nhds hη')).and (eventually_ge_atTop 1)).exists
    have hev : ∀ᶠ j in atTop, ∫⁻ x, x ^ (-s) ∂(nuX (X j)) ≤
        ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂(nuX (X j)) + K * (n : ℝ≥0∞)⁻¹ := by
      filter_upwards [hXev] with j hj
      calc ∫⁻ x, x ^ (-s) ∂(nuX (X j))
          ≤ ∫⁻ x, (min (x ^ (-s)) (n : ℝ≥0∞) + x ^ (-(2 * s)) * (n : ℝ≥0∞)⁻¹) ∂(nuX (X j)) :=
            lintegral_mono (hpt n hn1)
        _ = ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂(nuX (X j)) +
              (∫⁻ x, x ^ (-(2 * s)) ∂(nuX (X j))) * (n : ℝ≥0∞)⁻¹ := by
            rw [lintegral_add_left (hmeas.min measurable_const),
              lintegral_mul_const _ ENNReal.continuous_rpow_const.measurable]
        _ ≤ ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂(nuX (X j)) + K * (n : ℝ≥0∞)⁻¹ := by
            refine add_le_add le_rfl (mul_le_mul' ?_ le_rfl)
            exact le_iSup₂ (f := fun (Y : ℝ) (_ : 1 ≤ Y) => ∫⁻ x, x ^ (-(2 * s)) ∂(nuX Y))
              (X j) hj
    calc limsup (fun j => ∫⁻ x, x ^ (-s) ∂(nuX (X j))) atTop
        ≤ limsup (fun j => ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂(nuX (X j)) +
            K * (n : ℝ≥0∞)⁻¹) atTop := limsup_le_limsup hev
      _ = ∫⁻ x, min (x ^ (-s)) (n : ℝ≥0∞) ∂ν + K * (n : ℝ≥0∞)⁻¹ :=
          ((hB n).add tendsto_const_nhds).limsup_eq
      _ ≤ ∫⁻ x, x ^ (-s) ∂ν + η :=
          add_le_add (lintegral_mono (fun x => min_le_left _ _)) hn.le
  exact tendsto_of_le_liminf_of_limsup_le hlow hup

open Classical in
/-- The geometric means of `f(N)/N` tend to infinity (EP1054.tex lines 2971–2972). -/
theorem link_Cor_DaddHeavyTails_GeomMean :
    Principia.Erdos1054.Spine.Link_Cor_DaddHeavyTails_GeomMean := by
  rintro ⟨hlog, -⟩
  refine (Real.tendsto_exp_atTop.comp hlog).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hpos : ∀ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), 0 < (f N : ℝ) / N := by
    intro N hN
    have hNR : N ∈ R := (Finset.mem_filter.1 hN).2
    have h1 : (0 : ℝ) < f N := by exact_mod_cast one_le_f hNR
    have h2 : (0 : ℝ) < N := by exact_mod_cast one_le_of_mem_R hNR
    positivity
  have hprod : 0 < ∏ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), (f N : ℝ) / N :=
    Finset.prod_pos hpos
  rw [Function.comp_apply, integral_nuX, Real.rpow_def_of_pos hprod,
    Real.log_prod (fun N hN => (hpos N hN).ne')]
  congr 1
  rw [Finset.sum_congr rfl (fun N hN => by
    rw [ratioE, ENNReal.toReal_ofReal (hpos N hN).le])]
  ring

/-- The tight case of the heavy-tail corollary (EP1054.tex lines 2972–2973). -/
theorem link_Cor_DaddHeavyTails_Tight :
    Principia.Erdos1054.Spine.Link_Cor_DaddHeavyTails_Tight := by
  intro hT hPos hLog hcrit ν hν
  exact ⟨(hT hcrit ν hν).1, hLog.2 ν hν, fun s hs => (hPos s hs).2 ν hν⟩

end Principia.Erdos1054.Proofs

