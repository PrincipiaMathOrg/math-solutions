/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Principia.Erdos1054.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §7 — the progression laws and `prop:dadd:witness-means`

Proves, for the package `WitnessMeans` of `Campaigns/Erdos-1054/LEAN-WORKLIST.md` (paper lines
2729–2833), every obligation as the spine link `Spine.Link_X` itself:

* `link_Cite_Davenport` — the `Q = 1`, `a = 0` case of `Cite_PollackAP`;
* `link_Fact_DaddDavenportLaw`, `link_Fact_DaddProgressionLaws` — the laws `𝒟`, `ν_{a,e}` are the
  Stieltjes measures (`StieltjesFunction.measure`) of the distribution functions `D`, `D/Λ(e)`
  (monotone as limits of monotone counting ratios, `0` below `1` because `h(n) ≥ 1`), unique by
  `Measure.ext_of_Iic`, atomless by continuity of `D`. The continuity-set clause is a portmanteau
  argument: the empirical laws `empP` converge on the π-system of intervals `Ioc c d` (differences
  of distribution functions) and in total mass (the residue-class density), hence weakly
  (`fm_tendsto_of_piSystem`, via Mathlib's `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`
  after normalising), hence on every null-frontier set (`fm_measureReal_tendsto`);
* `link_Eq_DaddProgressionDomination` — the `Λ(e)` classes partition `ℕ` (`cnt_eq_sum_classes`), so
  `∑_a ν_{a,e}` has the Davenport distribution function; `ν_{a,e} = ν_{a mod Λ(e), e}` is one of
  the summands;
* `link_Step_DaddWitnessIdentity` — `g_e(n) = h(n) − c_e(a)` for `n ≡ a`, `e ∣ a`
  (`witness_identity`: every `r < e` divides `Λ(e)`), `F_e(n/e) = n g_e(n)` from `eq:reflection`;
* `link_Step_DaddWitnessSupport` — the continuity set `Iio (c_e(a) + 1/e)` has no source;
* `link_Step_DaddWitnessJointLimit` — the joint empirical measures `empJ` converge on the π-system
  of boxes `Ioc × Ioc` (quadrants `Iic s ×ˢ Ioc c d` are single rescaled counts,
  `hasDens_scaled`), hence weakly (`joint_tendsto`);
* `link_Step_DaddWitnessCount` — the joint limit in `FiniteMeasure` form, applied to the witness
  region `{h − c ≥ 1/t, u (h − c) ≤ 1}`, whose frontier is product-null (`witnessRegion_frontier`:
  a horizontal line and a hyperbola); Tonelli (`Measure.prod_apply_symm`) evaluates the limit
  (`witnessRegion_measure`);
* `link_Step_DaddWitnessCofactorTail` — the triples `(N, e, d)` inject into the pairs `(n, e)` of
  `eq:moment` at `Z = tX`, each weighted by `(t g_e(n))^k ≥ 1`;
* `link_Step_DaddWitnessPieceBounds` — dominated convergence off the null boundary point
  (`piece_continuousAt`), and the integrand is `≤ t` on its domain;
* `link_Prop_DaddWitnessMeans` — the averages are cofactor sums of the counts of `Step_DaddWitnessCount`
  (`sum_pairs_eq`, `cntE_eq_sum_classes`), and the uniform cofactor tail interchanges the sum with
  the `X`-limit (`limit_interchange`); uniform convergence on `(0, T]` gives continuity;
* `link_Step_DaddWitnessMeasureMass` — pushforward/`withDensity` evaluation of each piece of `𝒲`
  (`witnessPiece_Ioc`, `witnessPiece_singleton`);
* `link_Rem_DaddWitnessMeanGrowth` — `lamLower 1 0 = W` on `(0, ∞)`, `w_1(t) = ∫_{h ≥ 1/t} dν_{0,1}/h ≤ 1`
  (`ν_{0,1}` has mass `1` and is carried by `h ≥ 1`), and `W* = W − w_1`.

All helpers live in `Principia.Erdos1054.Proofs.WitnessMeans`.
-/


namespace Principia.Erdos1054.Proofs.WitnessMeans

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction
open Principia.Erdos1054 Principia.Erdos1054.Limits

theorem one_le_abundancy {n : ℕ} (hn : 1 ≤ n) : 1 ≤ abundancy n := by
  unfold abundancy
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn', one_mul]
  have : n ≤ sig n := by
    unfold sig
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n (by omega))
  exact_mod_cast this

theorem hasDens_le_of_subset {A B : Set ℕ} {a b : ℝ} (hAB : A ⊆ B) (hA : HasDens A a)
    (hB : HasDens B b) : a ≤ b :=
  le_of_tendsto_of_tendsto' hA hB (fun X => cnt_div_mono hAB X)

theorem hasDens_nonneg {A : Set ℕ} {a : ℝ} (hA : HasDens A a) : 0 ≤ a :=
  ge_of_tendsto' hA (fun X => cnt_div_nonneg A X)

theorem cnt_eq_zero_of_forall {A : Set ℕ} (hA : ∀ n ∈ A, n = 0) (X : ℝ) : cnt A X = 0 := by
  unfold cnt
  refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun n hn => ?_)
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  have := hA n hn.2
  omega

theorem hasDens_eq_zero_of_forall {A : Set ℕ} {d : ℝ} (hA : ∀ n ∈ A, n = 0) (h : HasDens A d) :
    d = 0 := by
  have h0 : HasDens A 0 := by
    unfold HasDens
    simp only [cnt_eq_zero_of_forall hA, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  exact h.unique h0

theorem exists_measure_of_cdf (D : ℝ → ℝ) (hc : Continuous D) (hm : Monotone D) {l : ℝ}
    (hbot : Tendsto D atBot (𝓝 0)) (htop : Tendsto D atTop (𝓝 l)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ u, μ (Iic u) = ENNReal.ofReal (D u)) ∧
      μ univ = ENNReal.ofReal l ∧ NoAtoms μ := by
  let F : StieltjesFunction ℝ := ⟨D, hm, fun x => hc.continuousWithinAt⟩
  refine ⟨F.measure, F.isFiniteMeasure hbot htop, fun u => ?_, ?_, ⟨fun x => ?_⟩⟩
  · rw [F.measure_Iic hbot u, sub_zero]
  · rw [F.measure_univ hbot htop, sub_zero]
  · have hl : Function.leftLim F x = F x :=
      ContinuousWithinAt.leftLim_eq (hc.continuousWithinAt : ContinuousWithinAt F (Iic x) x)
    rw [F.measure_singleton, hl, sub_self, ENNReal.ofReal_zero]

theorem measure_eq_of_real_Iic (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ u, μ.real (Iic u) = ν.real (Iic u)) : μ = ν := by
  refine Measure.ext_of_Iic μ ν fun u => ?_
  rw [← ofReal_measureReal (μ := μ), ← ofReal_measureReal (μ := ν), h u]

/-! ### A finite-measure portmanteau criterion -/

section Portmanteau

variable {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]

/-- A finite measure, bundled. -/
def toFM (μ : Measure Ω) [IsFiniteMeasure μ] : FiniteMeasure Ω := ⟨μ, inferInstance⟩

omit [TopologicalSpace Ω] in
theorem fm_mass_ne_zero (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0) :
    (toFM μ).mass ≠ 0 := by
  intro h
  apply hμ
  have h2 : (((toFM μ).mass : ℝ≥0) : ℝ≥0∞) = 0 := by
    rw [h, ENNReal.coe_zero]
  rwa [FiniteMeasure.ennreal_mass] at h2

/-- Finite measures converging on a π-system of arbitrarily small neighbourhoods, with converging
total masses and a nonzero limit, converge weakly. -/
theorem fm_tendsto_of_piSystem [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] [Nonempty Ω]
    {S : Set (Set Ω)} (hS : IsPiSystem S) (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hnhds : ∀ u : Set Ω, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    {l : Filter ι} [l.IsCountablyGenerated]
    (μs : ι → Measure Ω) [∀ i, IsFiniteMeasure (μs i)] (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0)
    (hconv : ∀ s ∈ S, Tendsto (fun i => (μs i).real s) l (𝓝 (μ.real s)))
    (hmass : Tendsto (fun i => (μs i).real univ) l (𝓝 (μ.real univ))) :
    Tendsto (fun i => toFM (μs i)) l
      (𝓝 (toFM μ)) := by
  set ms : ι → FiniteMeasure Ω := fun i => toFM (μs i) with hms
  set m : FiniteMeasure Ω := toFM μ with hm
  have hmass' : Tendsto (fun i => (ms i).mass) l (𝓝 m.mass) := NNReal.tendsto_coe.1 hmass
  have hmass0 : m.mass ≠ 0 := fm_mass_ne_zero μ hμ
  have hm0 : m ≠ 0 := (FiniteMeasure.mass_nonzero_iff m).1 hmass0
  refine (FiniteMeasure.tendsto_normalize_iff_tendsto hm0).1 ⟨?_, hmass'⟩
  have hev : ∀ᶠ i in l, ms i ≠ 0 :=
    (hmass'.eventually_ne hmass0).mono fun i hi => (FiniteMeasure.mass_nonzero_iff _).1 hi
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem hS hmeas hnhds fun s hs => ?_
  have hconv' : Tendsto (fun i => ms i s) l (𝓝 (m s)) := NNReal.tendsto_coe.1 (hconv s hs)
  rw [FiniteMeasure.normalize_eq_of_nonzero m hm0 s]
  refine ((hmass'.inv₀ hmass0).mul hconv').congr' ?_
  filter_upwards [hev] with i hi
  rw [FiniteMeasure.normalize_eq_of_nonzero _ hi s]

theorem fm_integral_tendsto [OpensMeasurableSpace Ω] {l : Filter ι}
    (μs : ι → Measure Ω) [∀ i, IsFiniteMeasure (μs i)] (μ : Measure Ω) [IsFiniteMeasure μ]
    (h : Tendsto (fun i => toFM (μs i)) l
      (𝓝 (toFM μ))) (φ : Ω →ᵇ ℝ) :
    Tendsto (fun i => ∫ x, φ x ∂(μs i)) l (𝓝 (∫ x, φ x ∂μ)) :=
  FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 h φ

theorem fm_measureReal_tendsto [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [Nonempty Ω]
    {l : Filter ι} (μs : ι → Measure Ω) [∀ i, IsFiniteMeasure (μs i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (h : Tendsto (fun i => toFM (μs i)) l
      (𝓝 (toFM μ))) {E : Set Ω} (hE : μ (frontier E) = 0) :
    Tendsto (fun i => (μs i).real E) l (𝓝 (μ.real E)) := by
  set ms : ι → FiniteMeasure Ω := fun i => toFM (μs i) with hms
  set m : FiniteMeasure Ω := toFM μ with hm
  have hmass0 : m.mass ≠ 0 := fm_mass_ne_zero μ hμ
  have hm0 : m ≠ 0 := (FiniteMeasure.mass_nonzero_iff m).1 hmass0
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto h hm0
  have hE' : m.normalize (frontier E) = 0 := by
    rw [FiniteMeasure.normalize_eq_of_nonzero m hm0,
      (FiniteMeasure.null_iff_toMeasure_null m _).2 hE, mul_zero]
  have k := (h.mass).mul (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hE')
  have k' : Tendsto (fun i => ms i E) l (𝓝 (m E)) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using k
  exact NNReal.tendsto_coe.2 k'

end Portmanteau

/-! ### The one-dimensional empirical laws -/

/-- The normalised empirical measure `(1/X) ∑_{1 ≤ n ≤ X, n ≡ a (mod L)} δ_{h(n)}`. -/
noncomputable def empP (L a X : ℕ) : Measure ℝ :=
  ((X : ℝ≥0)⁻¹) • ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % L = a % L),
    Measure.dirac (abundancy n)

instance (L a X : ℕ) : IsFiniteMeasure (empP L a X) := by
  unfold empP
  infer_instance

theorem empP_apply (L a X : ℕ) (B : Set ℝ) :
    empP L a X B = (((X : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
      ((cnt {n : ℕ | n % L = a % L ∧ abundancy n ∈ B} (X : ℝ) : ℕ) : ℝ≥0∞) := by
  classical
  rw [empP, Measure.coe_nnreal_smul_apply, Measure.finsetSum_apply, cnt_natCast]
  congr 1
  simp only [Measure.dirac_apply, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, Finset.filter_filter]
  congr 2
  ext n
  simp only [Finset.mem_filter, Set.mem_setOf_eq]

theorem empP_real (L a X : ℕ) (B : Set ℝ) :
    (empP L a X).real B = (cnt {n : ℕ | n % L = a % L ∧ abundancy n ∈ B} (X : ℝ) : ℝ) / X := by
  rw [measureReal_def, empP_apply, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast,
    NNReal.coe_inv, NNReal.coe_natCast, div_eq_inv_mul]

theorem lcmUpTo_pos (e : ℕ) : 0 < lcmUpTo (e : ℝ) := by
  unfold lcmUpTo
  apply Nat.pos_of_ne_zero
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

/-- The π-system of half-open intervals of `ℝ`. -/
def iocSys : Set (Set ℝ) := {s | ∃ c d : ℝ, s = Ioc c d}

theorem isPiSystem_iocSys : IsPiSystem iocSys := by
  rintro s ⟨c, d, rfl⟩ t ⟨c', d', rfl⟩ _
  refine ⟨max c c', min d d', ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, max_lt_iff, le_min_iff]
  tauto

theorem measurableSet_of_iocSys : ∀ s ∈ iocSys, MeasurableSet s := by
  rintro s ⟨c, d, rfl⟩
  exact measurableSet_Ioc

theorem iocSys_nhds : ∀ u : Set ℝ, IsOpen u → ∀ x ∈ u, ∃ s ∈ iocSys, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu x hx
  refine ⟨Ioc (x - ε / 2) (x + ε / 2), ⟨_, _, rfl⟩, Ioc_mem_nhds (by linarith) (by linarith),
    fun y hy => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

theorem Ioc_eq_Iic_sdiff (c d : ℝ) : Ioc c d = Iic (max c d) \ Iic c := by
  ext x
  simp only [Set.mem_Ioc, Set.mem_sdiff, Set.mem_Iic, not_le, le_max_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr h2, h1⟩
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 (not_le.2 h2)
    · exact ⟨h2, h1⟩

theorem measureReal_Ioc_eq (ν : Measure ℝ) [IsFiniteMeasure ν] (c d : ℝ) :
    ν.real (Ioc c d) = ν.real (Iic (max c d)) - ν.real (Iic c) := by
  rw [Ioc_eq_Iic_sdiff, measureReal_sdiff (Iic_subset_Iic.2 (le_max_left c d)) measurableSet_Iic]

end Principia.Erdos1054.Proofs.WitnessMeans

namespace Principia.Erdos1054.Proofs

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Proofs.WitnessMeans

theorem link_Cite_Davenport : Principia.Erdos1054.Spine.Link_Cite_Davenport := by
  intro h
  obtain ⟨D, hc, ht, hd⟩ := h 1 one_pos 0
  exact ⟨D, hc, ht, fun u => by simpa [Nat.mod_one] using hd u⟩

theorem link_Fact_DaddDavenportLaw : Principia.Erdos1054.Spine.Link_Fact_DaddDavenportLaw := by
  intro hD
  obtain ⟨D, hc, htop, hd⟩ := hD
  have hm : Monotone D := fun u v huv =>
    hasDens_le_of_subset (fun n (hn : abundancy n ≤ u) => (hn.trans huv : abundancy n ≤ v))
      (hd u) (hd v)
  have hz : ∀ u < 1, D u = 0 := fun u hu =>
    hasDens_eq_zero_of_forall (fun n (hn : abundancy n ≤ u) => by
      by_contra h0
      have := one_le_abundancy (Nat.one_le_iff_ne_zero.2 h0)
      linarith) (hd u)
  have hbot : Tendsto D atBot (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_lt_atBot 1).mono fun u hu => (hz u hu).symm)
  obtain ⟨μ, hfin, hIic, huniv, hna⟩ := exists_measure_of_cdf D hc hm hbot htop
  have hμD : IsDavenportLaw μ := by
    refine ⟨⟨by rw [huniv, ENNReal.ofReal_one]⟩, fun u => ?_⟩
    rw [measureReal_def, hIic u, ENNReal.toReal_ofReal (hasDens_nonneg (hd u))]
    exact hd u
  have hex : ∃ μ : Measure ℝ, IsDavenportLaw μ := ⟨μ, hμD⟩
  have hdl : IsDavenportLaw davenportLaw := by
    unfold davenportLaw
    rw [dif_pos hex]
    exact hex.choose_spec
  have huniq : ∀ ν : Measure ℝ, IsDavenportLaw ν → ν = davenportLaw := by
    intro ν hν
    haveI := hν.1
    haveI := hdl.1
    exact measure_eq_of_real_Iic ν davenportLaw fun u => (hν.2 u).unique (hdl.2 u)
  refine ⟨hdl, huniq, ?_⟩
  rw [← huniq μ hμD]
  exact hna

theorem link_Fact_DaddProgressionLaws :
    Principia.Erdos1054.Spine.Link_Fact_DaddProgressionLaws := by
  intro hP e _he a
  set L : ℕ := lcmUpTo (e : ℝ) with hLdef
  have hL : 0 < L := lcmUpTo_pos e
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨D, hc, htop, hd⟩ := hP L hL a
  set D' : ℝ → ℝ := fun u => D u / L with hD'
  have hd' : ∀ u, HasDens {n : ℕ | n % L = a % L ∧ abundancy n ≤ u} (D' u) := hd
  have hm : Monotone D' := fun u v huv =>
    hasDens_le_of_subset
      (fun n (hn : n % L = a % L ∧ abundancy n ≤ u) =>
        (⟨hn.1, hn.2.trans huv⟩ : n % L = a % L ∧ abundancy n ≤ v)) (hd' u) (hd' v)
  have hz : ∀ u < 1, D' u = 0 := fun u hu =>
    hasDens_eq_zero_of_forall (fun n (hn : n % L = a % L ∧ abundancy n ≤ u) => by
      by_contra h0
      have := one_le_abundancy (Nat.one_le_iff_ne_zero.2 h0)
      linarith [hn.2]) (hd' u)
  have hbot : Tendsto D' atBot (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_lt_atBot 1).mono fun u hu => (hz u hu).symm)
  have htop' : Tendsto D' atTop (𝓝 (1 / L)) := htop.div_const _
  have hc' : Continuous D' := hc.div_const _
  obtain ⟨μ, hfin, hIic, huniv, hna⟩ := exists_measure_of_cdf D' hc' hm hbot htop'
  have hIicR : ∀ u, μ.real (Iic u) = D' u := fun u => by
    rw [measureReal_def, hIic u, ENNReal.toReal_ofReal (hasDens_nonneg (hd' u))]
  have hμP : IsProgLaw e a μ := ⟨hfin, fun u => by rw [hIicR u]; exact hd' u⟩
  have hex : ∃ μ : Measure ℝ, IsProgLaw e a μ := ⟨μ, hμP⟩
  have hpl : IsProgLaw e a (progLaw e a) := by
    unfold progLaw
    rw [dif_pos hex]
    exact hex.choose_spec
  have huniq : ∀ ν : Measure ℝ, IsProgLaw e a ν → ν = progLaw e a := by
    intro ν hν
    haveI := hν.1
    haveI := hpl.1
    exact measure_eq_of_real_Iic ν (progLaw e a) fun u => (hν.2 u).unique (hpl.2 u)
  have hμeq : progLaw e a = μ := (huniq μ hμP).symm
  refine ⟨hpl, huniq, by rw [hμeq]; exact hna, ?_, ?_⟩
  · rw [hμeq, huniv, one_div, ENNReal.ofReal_inv_of_pos hLR, ENNReal.ofReal_natCast]
  · intro B _hB hfr
    rw [hμeq] at hfr ⊢
    have hμ0 : μ univ ≠ 0 := by
      rw [huniv]
      exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hIicconv : ∀ u, Tendsto (fun X : ℕ => (empP L a X).real (Iic u)) atTop
        (𝓝 (μ.real (Iic u))) := fun u => by
      simp only [empP_real]
      rw [hIicR u]
      exact hd' u
    have hmassD : HasDens {n : ℕ | n % L ∈ ({a % L} : Finset ℕ)}
        ((({a % L} : Finset ℕ).card : ℝ) / L) :=
      hasDens_mod_mem hL {a % L} (by simp [Nat.mod_lt _ hL])
    have hset : {n : ℕ | n % L = a % L ∧ abundancy n ∈ (univ : Set ℝ)} =
        {n : ℕ | n % L ∈ ({a % L} : Finset ℕ)} := by
      ext n
      simp
    have hconv := fm_tendsto_of_piSystem isPiSystem_iocSys measurableSet_of_iocSys iocSys_nhds
      (l := atTop) (fun X : ℕ => empP L a X) μ hμ0 (by
        rintro s ⟨c, d, rfl⟩
        simp only [measureReal_Ioc_eq]
        exact (hIicconv _).sub (hIicconv _)) (by
        simp only [empP_real, hset]
        rw [measureReal_def, huniv, ENNReal.toReal_ofReal (by positivity)]
        simpa [HasDens] using hmassD)
    have := fm_measureReal_tendsto _ μ hμ0 hconv hfr
    unfold HasDens
    simpa only [empP_real] using this

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.WitnessMeans

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits

theorem cnt_eq_sum_classes (L : ℕ) (hL : 0 < L) (S : Set ℕ) (X : ℝ) :
    (cnt S X : ℝ) = ∑ a ∈ Finset.range L, (cnt {n : ℕ | n % L = a % L ∧ n ∈ S} X : ℝ) := by
  classical
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => n % L) (t := Finset.range L)
    (fun n _ => Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt n hL)))]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  have haL : a % L = a := Nat.mod_eq_of_lt (Finset.mem_range.1 ha)
  refine congrArg (fun s : Finset ℕ => (s.card : ℝ)) ?_
  ext n
  simp only [Finset.mem_filter, Set.mem_setOf_eq, haL]
  tauto

theorem dvd_lcmUpTo {e j : ℕ} (hj1 : 1 ≤ j) (hje : j ≤ e) : j ∣ lcmUpTo (e : ℝ) := by
  unfold lcmUpTo
  rw [Nat.floor_natCast]
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨hj1, hje⟩)

theorem abundancy_eq_sum {n : ℕ} (hn : 1 ≤ n) :
    abundancy n = ∑ r ∈ n.divisors, (1 : ℝ) / r := by
  unfold abundancy sig
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div,
    ← Nat.sum_div_divisors n (fun r => (1 : ℝ) / r)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mem_divisors] at hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
  rw [Nat.cast_div hd.1 (by exact_mod_cast hdpos.ne'), one_div_div]

theorem g_nonneg' (e n : ℕ) : 0 ≤ g e n := Finset.sum_nonneg (fun r _ => by positivity)

theorem witness_identity {e n a : ℕ} (he : 1 ≤ e) (hn : 1 ≤ n)
    (hmod : n % lcmUpTo (e : ℝ) = a % lcmUpTo (e : ℝ)) (hea : e ∣ a) :
    e ∣ n ∧ g e n = abundancy n - cRes e a ∧ 1 / (e : ℝ) ≤ g e n := by
  have hmod' : n ≡ a [MOD lcmUpTo (e : ℝ)] := hmod
  have hen : e ∣ n := (hmod'.dvd_iff (dvd_lcmUpTo he le_rfl)).2 hea
  refine ⟨hen, ?_, ?_⟩
  · have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun r => e ≤ r)
      (fun r => (1 : ℝ) / r)
    have hc : n.divisors.filter (fun r => ¬ e ≤ r) = (Finset.Ico 1 e).filter (· ∣ a) := by
      ext r
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ico, not_le]
      constructor
      · rintro ⟨⟨hrn, -⟩, hre⟩
        have hr1 : 1 ≤ r := Nat.pos_of_dvd_of_pos hrn (by omega)
        exact ⟨⟨hr1, hre⟩, (hmod'.dvd_iff (dvd_lcmUpTo hr1 hre.le)).1 hrn⟩
      · rintro ⟨⟨hr1, hre⟩, hra⟩
        exact ⟨⟨(hmod'.dvd_iff (dvd_lcmUpTo hr1 hre.le)).2 hra, by omega⟩, hre⟩
    rw [abundancy_eq_sum hn, ← hsplit, hc]
    unfold g cRes
    ring
  · unfold g
    have hmem : e ∈ n.divisors.filter (fun r => e ≤ r) :=
      Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hen, by omega⟩, le_rfl⟩
    exact Finset.single_le_sum (f := fun r : ℕ => (1 : ℝ) / r)
      (fun r _ => div_nonneg zero_le_one (Nat.cast_nonneg r)) hmem

end Principia.Erdos1054.Proofs.WitnessMeans

namespace Principia.Erdos1054.Proofs

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Proofs.WitnessMeans

theorem link_Eq_DaddProgressionDomination :
    Principia.Erdos1054.Spine.Link_Eq_DaddProgressionDomination := by
  intro hDL hPL e he
  set L : ℕ := lcmUpTo (e : ℝ) with hLdef
  have hL : 0 < L := lcmUpTo_pos e
  haveI hfin : ∀ a, IsFiniteMeasure (progLaw e a) := fun a => (hPL e he a).1.1
  set ν : Measure ℝ := ∑ a ∈ Finset.range L, progLaw e a with hν
  have hνIic : ∀ u, ν.real (Iic u) = ∑ a ∈ Finset.range L, (progLaw e a).real (Iic u) := by
    intro u
    rw [hν, measureReal_def, Measure.finsetSum_apply,
      ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    rfl
  have hνD : IsDavenportLaw ν := by
    refine ⟨⟨?_⟩, fun u => ?_⟩
    · rw [hν, Measure.finsetSum_apply, Finset.sum_congr rfl (fun a _ => (hPL e he a).2.2.2.1),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.mul_inv_cancel (by exact_mod_cast hL.ne') (ENNReal.natCast_ne_top L)]
    · rw [hνIic u]
      unfold HasDens
      have := tendsto_finsetSum (Finset.range L) (fun a _ => (hPL e he a).1.2 u)
      refine this.congr (fun X => ?_)
      rw [cnt_eq_sum_classes L hL {n : ℕ | abundancy n ≤ u} X, Finset.sum_div]
      rfl
  have heq : ν = davenportLaw := hDL.2.1 ν hνD
  refine ⟨heq, fun a => ?_⟩
  have hmod : progLaw e a = progLaw e (a % L) := by
    have h1 : IsProgLaw e a (progLaw e (a % L)) := by
      have h := (hPL e he (a % L)).1
      simpa only [IsProgLaw, hLdef, Nat.mod_mod] using h
    exact ((hPL e he a).2.1 _ h1).symm
  rw [hmod, ← heq, Measure.le_iff']
  intro s
  rw [hν, Measure.finsetSum_apply]
  exact Finset.single_le_sum (f := fun b => progLaw e b s) (fun b _ => zero_le)
    (Finset.mem_range.2 (Nat.mod_lt a hL))

theorem link_Step_DaddWitnessIdentity :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessIdentity := by
  intro hR _hFD e n a he hn hmod hea
  obtain ⟨hen, hg, hge⟩ := witness_identity he hn hmod hea
  refine ⟨?_, hg, hge⟩
  obtain ⟨d, rfl⟩ := hen
  have hd : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
  rw [Nat.mul_div_cancel_left d (by omega), hR e d he hd, Nat.cast_mul]

theorem link_Step_DaddWitnessSupport :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessSupport := by
  intro hId hPL e a he hea
  obtain ⟨⟨hfin, -⟩, -, hna, -, hcs⟩ := hPL e he a
  set c := cRes e a with hcdef
  have hB : {h : ℝ | h - c < 1 / (e : ℝ)} = Iio (c + 1 / e) := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor <;> intro h' <;> linarith
  rw [hB]
  have hfr : progLaw e a (frontier (Iio (c + 1 / e))) = 0 := by
    rw [frontier_Iio]
    exact measure_singleton _
  have hd := hcs _ measurableSet_Iio hfr
  have h0 := hasDens_eq_zero_of_forall (fun n (hn : n % lcmUpTo (e : ℝ) = a % lcmUpTo (e : ℝ) ∧
      abundancy n ∈ Iio (c + 1 / e)) => by
      by_contra h0
      obtain ⟨-, hg, hge⟩ := hId e n a he (Nat.one_le_iff_ne_zero.2 h0) hn.1 hea
      have h2 := hn.2
      simp only [Set.mem_Iio] at h2
      linarith) hd
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0

theorem link_Step_DaddWitnessCofactorTail :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessCofactorTail := by
  intro hLM hR k hk
  obtain ⟨Ck, ⟨hCk, -⟩, hMom, -⟩ := hLM k hk
  refine ⟨Ck, fun t ht E hE X hX => ?_⟩
  classical
  have hX0 : 0 < X := by linarith
  have hE0 : 0 < E := by linarith
  set T3 : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.Icc 1 ⌊X⌋₊).sigma (fun N =>
    ((Finset.Icc 1 ⌊t * N⌋₊) ×ˢ (Finset.Icc 1 ⌊t * N⌋₊)).filter
      (fun p => E < (p.1 : ℝ) ∧ F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N)) with hT3
  have hsum : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t E N : ℝ) = (T3.card : ℝ) := by
    rw [hT3, Finset.card_sigma, Nat.cast_sum]
    rfl
  set M := ⌊t * X⌋₊ with hM
  set T : Finset (Σ _ : ℕ, ℕ) := (Finset.Icc 1 M).sigma
    (fun n => n.divisors.filter (fun e => E < (e : ℝ) ∧ 1 ≤ t * g e n)) with hT
  have hinj : T3.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun q => (⟨q.2.1 * q.2.2, q.2.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
    · rintro ⟨N, e, d⟩ hq
      simp only [hT3, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hN1, hNX⟩, ⟨⟨he1, -⟩, hd1, -⟩, hEe, hF, hed⟩ := hq
      have hNXr : (N : ℝ) ≤ X := (Nat.cast_le.mpr hNX).trans (Nat.floor_le hX0.le)
      have hed0 : (0 : ℝ) < (e : ℝ) * d := by
        have : (1 : ℝ) ≤ e := by exact_mod_cast he1
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        nlinarith
      have hrefl := hR e d he1 hd1
      simp only [hT, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
        Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_floor ?_⟩,
        ⟨⟨dvd_mul_right e d, by positivity⟩, hEe, ?_⟩⟩
      · push_cast at hed ⊢
        calc (e : ℝ) * d ≤ t * N := hed
          _ ≤ t * X := mul_le_mul_of_nonneg_left hNXr ht.le
      · have key : (e : ℝ) * d * 1 ≤ (e : ℝ) * d * (t * g e (e * d)) := by
          rw [mul_one]
          push_cast at hed
          calc (e : ℝ) * d ≤ t * N := hed
            _ = t * (F e d : ℝ) := by rw [hF]
            _ = (e : ℝ) * d * (t * g e (e * d)) := by rw [hrefl]; ring
        exact le_of_mul_le_mul_left key hed0
    · rintro ⟨N, e, d⟩ hq ⟨N', e', d'⟩ hq' heq
      simp only [hT3, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_product] at hq hq'
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨h1, rfl⟩ := heq
      have he1 : 1 ≤ e := hq.2.1.1.1
      have hdd : d = d' := Nat.eq_of_mul_eq_mul_left (by omega) h1
      subst hdd
      have hN : N = N' := hq.2.2.2.1.symm.trans hq'.2.2.2.1
      subst hN
      rfl
  have hT_le : (T.card : ℝ) ≤ t ^ k * momentSum k E (t * X) := by
    rw [hT, Finset.card_sigma, Nat.cast_sum]
    unfold momentSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [Finset.mul_sum]
    rw [show n.divisors.filter (fun e : ℕ => E < (e : ℝ) ∧ 1 ≤ t * g e n)
        = (n.divisors.filter (fun e : ℕ => E < (e : ℝ))).filter (fun e : ℕ => 1 ≤ t * g e n) from
        (Finset.filter_filter _ _ _).symm]
    rw [← Finset.sum_boole]
    apply Finset.sum_le_sum
    intro e _
    rw [← mul_pow]
    split_ifs with h
    · exact one_le_pow₀ h
    · exact pow_nonneg (mul_nonneg ht.le (g_nonneg' e n)) _
  have hRHS : 0 ≤ Ck * t ^ (k + 1) * E ^ (1 - (k : ℝ)) := by positivity
  rw [hsum]
  by_cases htX : 1 ≤ t * X
  · have h3 := hMom E (t * X) hE htX
    calc 1 / X * (T3.card : ℝ) ≤ 1 / X * (t ^ k * (Ck * (t * X) * E ^ (1 - (k : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (T3.card : ℝ) ≤ T.card := by exact_mod_cast hinj
            _ ≤ t ^ k * momentSum k E (t * X) := hT_le
            _ ≤ t ^ k * (Ck * (t * X) * E ^ (1 - (k : ℝ))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Ck * t ^ (k + 1) * E ^ (1 - (k : ℝ)) := by
          field_simp
          ring
  · have hM0 : M = 0 := Nat.floor_eq_zero.2 (by linarith)
    have hT0 : T.card = 0 := by
      rw [hT, hM0]
      simp
    have : T3.card = 0 := Nat.eq_zero_of_le_zero (hT0 ▸ hinj)
    rw [this, Nat.cast_zero, mul_zero]
    exact hRHS

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.WitnessMeans

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits

/-! ### One witness piece `∫_{h - c ≥ 1/t} dν(h)/(h - c)` -/

theorem piece_bound {c t h : ℝ} (ht : 0 < t) (hh : 1 / t ≤ h - c) :
    0 < 1 / (h - c) ∧ 1 / (h - c) ≤ t := by
  have hpos : 0 < h - c := lt_of_lt_of_le (by positivity) hh
  refine ⟨by positivity, ?_⟩
  calc 1 / (h - c) ≤ 1 / (1 / t) := one_div_le_one_div_of_le (by positivity) hh
    _ = t := one_div_one_div t

theorem measurableSet_pieceSet (c t : ℝ) : MeasurableSet {h : ℝ | 1 / t ≤ h - c} :=
  measurableSet_le measurable_const (measurable_id.sub_const c)

theorem measurable_pieceFun (c : ℝ) : Measurable fun h : ℝ => 1 / (h - c) :=
  measurable_const.div (measurable_id.sub_const c)

theorem piece_integrableOn (ν : Measure ℝ) [IsFiniteMeasure ν] (c t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun h : ℝ => 1 / (h - c)) {h : ℝ | 1 / t ≤ h - c} ν := by
  refine Measure.integrableOn_of_bounded (M := t) (measure_ne_top _ _)
    (measurable_pieceFun c).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (measurableSet_pieceSet c t) fun h hh => ?_
  obtain ⟨h1, h2⟩ := piece_bound ht hh
  rw [Real.norm_eq_abs, abs_of_pos h1]
  exact h2

theorem piece_nonneg (ν : Measure ℝ) (c t : ℝ) (ht : 0 < t) :
    0 ≤ ∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν :=
  setIntegral_nonneg (measurableSet_pieceSet c t) fun _ hh => (piece_bound ht hh).1.le

theorem piece_le (ν : Measure ℝ) [IsFiniteMeasure ν] (c t : ℝ) (ht : 0 < t) :
    ∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν ≤ t * ν.real univ := by
  have h1 : ‖∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν‖ ≤
      t * ν.real {h : ℝ | 1 / t ≤ h - c} := by
    refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun h hh => ?_
    obtain ⟨h1, h2⟩ := piece_bound ht hh
    rw [Real.norm_eq_abs, abs_of_pos h1]
    exact h2
  calc ∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν
      ≤ ‖∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν‖ := Real.le_norm_self _
    _ ≤ t * ν.real {h : ℝ | 1 / t ≤ h - c} := h1
    _ ≤ t * ν.real univ := mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)) ht.le

theorem piece_continuousAt (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] (c t0 : ℝ)
    (ht0 : 0 < t0) :
    ContinuousAt (fun t => ∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν) t0 := by
  have hfun : (fun t => ∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν) =
      fun t => ∫ h, {h : ℝ | 1 / t ≤ h - c}.indicator (fun h => 1 / (h - c)) h ∂ν :=
    funext fun t => (integral_indicator (measurableSet_pieceSet c t)).symm
  rw [ContinuousAt, hfun, ← integral_indicator (measurableSet_pieceSet c t0)]
  refine tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝 t0)
    (F := fun t h => {h : ℝ | 1 / t ≤ h - c}.indicator (fun h => 1 / (h - c)) h)
    (f := {h : ℝ | 1 / t0 ≤ h - c}.indicator (fun h => 1 / (h - c)))
    (fun _ => 2 * t0) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun t =>
      ((measurable_pieceFun c).indicator (measurableSet_pieceSet c t)).aestronglyMeasurable
  · have hev : ∀ᶠ t in 𝓝 t0, t0 / 2 < t ∧ t < 2 * t0 :=
      (tendsto_id.eventually_const_lt (show t0 / 2 < t0 by linarith)).and
        (tendsto_id.eventually_lt_const (show t0 < 2 * t0 by linarith))
    filter_upwards [hev] with t ht
    refine Eventually.of_forall fun h => ?_
    by_cases hh : h ∈ {h : ℝ | 1 / t ≤ h - c}
    · rw [Set.indicator_of_mem hh]
      obtain ⟨h1, h2⟩ := piece_bound (by linarith [ht.1]) hh
      rw [Real.norm_eq_abs, abs_of_pos h1]
      linarith [ht.2]
    · rw [Set.indicator_of_notMem hh, norm_zero]
      positivity
  · have hnull : ∀ᵐ h ∂ν, h ≠ c + 1 / t0 := by
      have : ν {c + 1 / t0} = 0 := measure_singleton _
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with h hh
      exact hh
    have hinv : Tendsto (fun t : ℝ => 1 / t) (𝓝 t0) (𝓝 (1 / t0)) :=
      (continuousAt_const.div continuousAt_id ht0.ne').tendsto
    filter_upwards [hnull] with h hh
    have hne : h - c ≠ 1 / t0 := fun h' => hh (by linarith)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [Set.indicator_of_notMem (show h ∉ {h : ℝ | 1 / t0 ≤ h - c} from not_le.2 hlt)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hinv.eventually_const_lt hlt] with t ht
      rw [Set.indicator_of_notMem (show h ∉ {h : ℝ | 1 / t ≤ h - c} from not_le.2 ht)]
    · rw [Set.indicator_of_mem (show h ∈ {h : ℝ | 1 / t0 ≤ h - c} from hlt.le)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hinv.eventually_lt_const hlt] with t ht
      rw [Set.indicator_of_mem (show h ∈ {h : ℝ | 1 / t ≤ h - c} from ht.le)]

/-! ### The pushed-forward witness pieces -/

theorem measurable_psiE (c : ℝ) : Measurable (psiE c) :=
  ENNReal.measurable_ofReal.comp (measurable_pieceFun c)

theorem witnessPiece_apply (e a : ℕ) {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    witnessPiece e a s =
      ∫⁻ h in psiE (cRes e a) ⁻¹' s ∩ Ioi (cRes e a), ENNReal.ofReal (1 / (h - cRes e a))
        ∂(progLaw e a) := by
  rw [witnessPiece, Measure.map_apply (measurable_psiE _) hs,
    withDensity_apply _ ((measurable_psiE _) hs), Measure.restrict_restrict ((measurable_psiE _) hs)]

theorem psiE_preimage_Ioc (c t : ℝ) (ht : 0 < t) :
    psiE c ⁻¹' Ioc 0 (ENNReal.ofReal t) ∩ Ioi c = {h : ℝ | 1 / t ≤ h - c} := by
  ext h
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, Set.mem_Ioi, Set.mem_setOf_eq,
    psiE]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    have hpos : 0 < h - c := by linarith
    rw [ENNReal.ofReal_le_ofReal_iff ht.le] at h2
    rw [div_le_iff₀ hpos] at h2
    rw [div_le_iff₀ ht]
    linarith
  · intro hh
    obtain ⟨h1, h2⟩ := piece_bound ht hh
    have hpos : 0 < h - c := lt_of_lt_of_le (by positivity) hh
    exact ⟨⟨ENNReal.ofReal_pos.2 h1, ENNReal.ofReal_le_ofReal h2⟩, by linarith⟩

theorem witnessPiece_Ioc (e a : ℕ) [IsFiniteMeasure (progLaw e a)] (t : ℝ) (ht : 0 < t) :
    witnessPiece e a (Ioc 0 (ENNReal.ofReal t)) =
      ENNReal.ofReal (∫ h in {h : ℝ | 1 / t ≤ h - cRes e a}, 1 / (h - cRes e a) ∂(progLaw e a)) := by
  rw [witnessPiece_apply e a measurableSet_Ioc, psiE_preimage_Ioc _ t ht,
    ofReal_integral_eq_lintegral_ofReal (piece_integrableOn _ _ t ht)]
  exact ae_restrict_of_forall_mem (measurableSet_pieceSet _ t) fun h hh =>
    (piece_bound ht hh).1.le

theorem witnessPiece_singleton (e a : ℕ) [NoAtoms (progLaw e a)] (x : ℝ≥0∞) :
    witnessPiece e a {x} = 0 := by
  rw [witnessPiece_apply e a (measurableSet_singleton x)]
  have hsub : psiE (cRes e a) ⁻¹' {x} ∩ Ioi (cRes e a) ⊆ {cRes e a + 1 / x.toReal} := by
    rintro h ⟨h1, h2⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, psiE] at h1
    simp only [Set.mem_Ioi] at h2
    have hpos : 0 < h - cRes e a := by linarith
    have hx : x.toReal = 1 / (h - cRes e a) := by
      rw [← h1, ENNReal.toReal_ofReal (by positivity)]
    rw [Set.mem_singleton_iff, hx, one_div_one_div]
    ring
  have hnull : progLaw e a (psiE (cRes e a) ⁻¹' {x} ∩ Ioi (cRes e a)) = 0 :=
    measure_mono_null hsub (measure_singleton _)
  exact setLIntegral_measure_zero _ _ hnull

end Principia.Erdos1054.Proofs.WitnessMeans

namespace Principia.Erdos1054.Proofs

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Proofs.WitnessMeans

theorem link_Step_DaddWitnessPieceBounds :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessPieceBounds := by
  intro hPL e he
  have hbound : ∀ t : ℝ, 0 < t →
      wE e t ≤ t * ∑ a ∈ witnessResidues e, (progLaw e a).real univ := by
    intro t ht
    unfold wE
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    haveI := (hPL e he a).1.1
    exact piece_le (progLaw e a) (cRes e a) t ht
  have hnonneg : ∀ t : ℝ, 0 < t → 0 ≤ wE e t := fun t ht =>
    Finset.sum_nonneg fun a _ => piece_nonneg (progLaw e a) (cRes e a) t ht
  refine ⟨?_, hbound, ?_⟩
  · intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold wE
    refine tendsto_finsetSum _ fun a _ => ?_
    haveI := (hPL e he a).1.1
    haveI := (hPL e he a).2.2.1
    exact piece_continuousAt (progLaw e a) (cRes e a) t ht
  · set M := ∑ a ∈ witnessResidues e, (progLaw e a).real univ with hM
    have hup : Tendsto (fun t : ℝ => t * M) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => t * M) (𝓝[>] 0) (𝓝 (0 * M)) :=
        (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const M
      rwa [zero_mul] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht using hnonneg t ht
    · filter_upwards [self_mem_nhdsWithin] with t ht using hbound t ht

theorem link_Step_DaddWitnessMeasureMass :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessMeasureMass := by
  intro hWM hPL
  refine ⟨fun t ht => ?_, fun x => ?_⟩
  · have hsum := ((hWM.1 t ht).2.2.1)
    rw [witnessMeasure, Measure.sum_apply _ measurableSet_Ioc]
    have hterm : ∀ e' : ℕ, (∑ a ∈ witnessResidues (e' + 1), witnessPiece (e' + 1) a)
        (Ioc 0 (ENNReal.ofReal t)) = ENNReal.ofReal (wE (e' + 1) t) := by
      intro e'
      rw [Measure.finsetSum_apply, wE, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => piece_nonneg _ _ t ht)]
      refine Finset.sum_congr rfl fun a _ => ?_
      haveI := (hPL (e' + 1) (by omega) a).1.1
      exact witnessPiece_Ioc (e' + 1) a t ht
    simp only [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun e' : ℕ => wE (e' + 1) t)
      (fun e' => Finset.sum_nonneg fun a _ => piece_nonneg _ _ t ht) hsum.summable, hsum.tsum_eq]
  · rw [witnessMeasure, Measure.sum_apply _ (measurableSet_singleton x)]
    refine ENNReal.tsum_eq_zero.2 fun e' => ?_
    rw [Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    haveI := (hPL (e' + 1) (by omega) a).2.2.1
    exact witnessPiece_singleton (e' + 1) a x

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.WitnessMeans

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits

/-! ### Counting witnesses by cofactor -/

/-- `#{1 ≤ n ≤ tX : e ∣ n, 1/t ≤ g_e(n), n g_e(n) ≤ X}`: the witnesses with cofactor `e`, target
`≤ X` and ratio `≤ t`, indexed by `n = e d`. -/
noncomputable def cntE (e : ℕ) (t X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊t * X⌋₊).filter (fun n => e ∣ n ∧ 1 / t ≤ g e n ∧ (n : ℝ) * g e n ≤ X)).card

theorem cntE_eq_zero_of_lt {e : ℕ} {t X : ℝ} (he : ⌊t * X⌋₊ < e) : cntE e t X = 0 := by
  unfold cntE
  refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun n hn => ?_)
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  have := Nat.le_of_dvd (by omega) hn.2.1
  omega

theorem cntE_eq_sum_classes {e : ℕ} (he : 1 ≤ e) (t X : ℝ) :
    cntE e t X = ∑ a ∈ witnessResidues e,
      ((Finset.Icc 1 ⌊t * X⌋₊).filter (fun n : ℕ =>
        n % lcmUpTo (e : ℝ) = a % lcmUpTo (e : ℝ) ∧ 1 / t ≤ g e n ∧ (n : ℝ) * g e n ≤ X)).card := by
  classical
  unfold cntE
  have hL : 0 < lcmUpTo (e : ℝ) := lcmUpTo_pos e
  have heL : e ∣ lcmUpTo (e : ℝ) := dvd_lcmUpTo he le_rfl
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => n % lcmUpTo (e : ℝ))
    (t := witnessResidues e) ?_]
  · refine Finset.sum_congr rfl fun a ha => ?_
    simp only [witnessResidues, Finset.mem_filter, Finset.mem_range] at ha
    have haL : a % lcmUpTo (e : ℝ) = a := Nat.mod_eq_of_lt ha.1
    congr 1
    ext n
    simp only [Finset.mem_filter, haL]
    constructor
    · rintro ⟨⟨hn, -, h2, h3⟩, h4⟩
      exact ⟨hn, h4, h2, h3⟩
    · rintro ⟨hn, h4, h2, h3⟩
      refine ⟨⟨hn, ?_, h2, h3⟩, h4⟩
      have hmod : n ≡ a [MOD lcmUpTo (e : ℝ)] := by
        rw [Nat.ModEq, haL]
        exact h4
      exact (hmod.dvd_iff heL).2 ha.2
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    rw [Finset.mem_coe]
    simp only [witnessResidues, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hL, (Nat.dvd_mod_iff heL).2 hn.2.1⟩

theorem sum_pairs_eq {t X : ℝ} (ht : 0 < t) (lo : ℕ) (hlo : 1 ≤ lo) (P : ℕ → Prop)
    [DecidablePred P] :
    ∑ N ∈ Finset.Icc 1 ⌊X⌋₊,
      (((Finset.Icc lo ⌊t * N⌋₊) ×ˢ (Finset.Icc 1 ⌊t * N⌋₊)).filter
        (fun p => P p.1 ∧ F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N)).card =
    ∑ e ∈ (Finset.Icc lo ⌊t * X⌋₊).filter P, cntE e t X := by
  classical
  unfold cntE
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  refine Finset.card_nbij' (fun q => (⟨q.2.1, q.2.1 * q.2.2⟩ : Σ _ : ℕ, ℕ))
    (fun q => (⟨F q.1 (q.2 / q.1), (q.1, q.2 / q.1)⟩ : Σ _ : ℕ, ℕ × ℕ)) ?_ ?_ ?_ ?_
  · rintro ⟨N, e, d⟩ hq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨hN1, hNX⟩, ⟨⟨he1, heN⟩, hd1, -⟩, hP, hF, hed⟩ := hq
    have hX1 : 1 ≤ X := Nat.floor_pos.1 (by omega)
    have hNXr : (N : ℝ) ≤ X := (Nat.cast_le.mpr hNX).trans (Nat.floor_le (by linarith))
    have he1' : 1 ≤ e := le_trans hlo he1
    have hrefl := reflection e d he1' hd1
    have he1r : (1 : ℝ) ≤ e := by exact_mod_cast he1'
    have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hed0 : (0 : ℝ) < (e : ℝ) * d := by nlinarith
    push_cast at hed
    have htN : t * N ≤ t * X := mul_le_mul_of_nonneg_left hNXr ht.le
    refine ⟨⟨⟨he1, heN.trans (Nat.floor_mono htN)⟩, hP⟩, ⟨Nat.one_le_iff_ne_zero.2 (by positivity),
      Nat.le_floor ?_⟩, dvd_mul_right e d, ?_, ?_⟩
    · push_cast
      linarith
    · rw [div_le_iff₀ ht]
      have key : (e : ℝ) * d * 1 ≤ (e : ℝ) * d * (g e (e * d) * t) := by
        rw [mul_one]
        calc (e : ℝ) * d ≤ t * N := hed
          _ = t * F e d := by rw [hF]
          _ = (e : ℝ) * d * (g e (e * d) * t) := by rw [hrefl]; ring
      exact le_of_mul_le_mul_left key hed0
    · push_cast
      rw [← hrefl, hF]
      exact hNXr
  · rintro ⟨e, n⟩ hq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨⟨he1, -⟩, hP⟩, ⟨hn1, -⟩, hdvd, hg, hng⟩ := hq
    obtain ⟨d, rfl⟩ := hdvd
    have he1' : 1 ≤ e := le_trans hlo he1
    rw [Nat.mul_div_cancel_left d (by omega)]
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by simp [h] at hn1)
    have hrefl := reflection e d he1' hd1
    have he1r : (1 : ℝ) ≤ e := by exact_mod_cast he1'
    have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    push_cast at hng
    have hFX : (F e d : ℝ) ≤ X := by rw [hrefl]; exact hng
    have htg : 1 ≤ t * g e (e * d) := by
      rw [div_le_iff₀ ht] at hg
      linarith
    have hedF : (e : ℝ) * d ≤ t * F e d := by
      rw [hrefl]
      have h0 : (0 : ℝ) ≤ e * d := by positivity
      nlinarith
    refine ⟨⟨le_trans hd1 (F_ge e d he1' hd1), Nat.le_floor hFX⟩,
      ⟨⟨he1, Nat.le_floor ?_⟩, hd1, Nat.le_floor ?_⟩, hP, trivial, ?_⟩
    · nlinarith
    · nlinarith
    · push_cast
      exact hedF
  · rintro ⟨N, e, d⟩ hq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨-, ⟨⟨he1, -⟩, -⟩, -, hF, -⟩ := hq
    simp only [Nat.mul_div_cancel_left d (show 0 < e by omega), hF]
  · rintro ⟨e, n⟩ hq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_filter] at hq
    obtain ⟨-, -, hdvd, -⟩ := hq
    simp only [Nat.mul_div_cancel' hdvd]

theorem sum_rt_eq {t X : ℝ} (ht : 0 < t) :
    ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, rt t N = ∑ e ∈ Finset.Icc 1 ⌊t * X⌋₊, cntE e t X := by
  classical
  have h := sum_pairs_eq (X := X) ht 1 le_rfl (fun _ => True)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun N _ => ?_
  unfold rt
  congr 1
  ext p
  simp only [Finset.mem_filter, true_and]

theorem sum_rtStar_eq {t X : ℝ} (ht : 0 < t) :
    ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, rtStar t N = ∑ e ∈ Finset.Icc 2 ⌊t * X⌋₊, cntE e t X := by
  classical
  have h := sum_pairs_eq (X := X) ht 2 (by norm_num) (fun _ => True)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun N _ => ?_
  unfold rtStar
  congr 1
  ext p
  simp only [Finset.mem_filter, true_and]

theorem sum_rtTail_eq {t X : ℝ} (ht : 0 < t) (J : ℕ) :
    ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, rtTail t J N =
      ∑ e ∈ (Finset.Icc 1 ⌊t * X⌋₊).filter (fun e : ℕ => (J : ℝ) < e), cntE e t X := by
  classical
  rw [← sum_pairs_eq (X := X) ht 1 le_rfl (fun e : ℕ => (J : ℝ) < e)]
  refine Finset.sum_congr rfl fun N _ => ?_
  unfold rtTail
  congr 1

/-- Splitting the cofactors `e ≥ o` at `o + K`. -/
theorem sum_split (f : ℕ → ℝ) (M o K : ℕ) (ho : 1 ≤ o) (hf : ∀ e, M < e → f e = 0) :
    ∑ e ∈ Finset.Icc o M, f e = ∑ e ∈ Finset.range K, f (e + o) +
      ∑ e ∈ (Finset.Icc 1 M).filter (fun e : ℕ => ((K + o - 1 : ℕ) : ℝ) < e), f e := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc o M) (fun e => e < o + K)]
  congr 1
  · have h1 : ∑ e ∈ Finset.range K, f (e + o) = ∑ e ∈ Finset.Ico o (o + K), f e := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      exact Finset.sum_congr rfl fun e _ => by rw [add_comm]
    rw [h1]
    refine Finset.sum_subset (fun e he => ?_) (fun e he hne => ?_)
    · simp only [Finset.mem_filter, Finset.mem_Icc] at he
      exact Finset.mem_Ico.2 ⟨he.1.1, he.2⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, not_and] at he hne
      exact hf e (by by_contra h; exact absurd (hne ⟨he.1, not_lt.1 h⟩) (not_not.2 he.2))
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt, Nat.cast_lt]
    omega

/-! ### Interchanging the cofactor sum with the `X`-limit -/

theorem limit_interchange {S : ℝ → ℝ} {a : ℕ → ℝ → ℝ} {w : ℕ → ℝ} {B : ℕ → ℝ}
    (ha : ∀ e, Tendsto (a e) atTop (𝓝 (w e)))
    (ha0 : ∀ e X, 1 ≤ X → 0 ≤ a e X)
    (hB : Tendsto B atTop (𝓝 0))
    (htail : ∀ K : ℕ, 1 ≤ K → ∀ X : ℝ, 1 ≤ X →
      0 ≤ S X - ∑ e ∈ Finset.range K, a e X ∧ S X - ∑ e ∈ Finset.range K, a e X ≤ B K) :
    (∀ e, 0 ≤ w e) ∧ (∀ K : ℕ, 1 ≤ K → ∑' e, w (e + K) ≤ B K) ∧ Summable w ∧
      Tendsto S atTop (𝓝 (∑' e, w e)) := by
  have hw0 : ∀ e, 0 ≤ w e := fun e =>
    ge_of_tendsto (ha e) (Filter.eventually_atTop.2 ⟨1, fun X hX => ha0 e X hX⟩)
  have hpart : ∀ K : ℕ, 1 ≤ K → ∀ n : ℕ, ∑ i ∈ Finset.range n, w (i + K) ≤ B K := by
    intro K hK n
    have hlim : Tendsto (fun X => ∑ i ∈ Finset.range n, a (i + K) X) atTop
        (𝓝 (∑ i ∈ Finset.range n, w (i + K))) := tendsto_finsetSum _ fun i _ => ha (i + K)
    refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun X hX => ?_⟩)
    have h1 := (htail (K + n) (by omega) X hX).1
    have h2 := (htail K hK X hX).2
    rw [Finset.sum_range_add] at h1
    have h3 : ∑ i ∈ Finset.range n, a (i + K) X = ∑ x ∈ Finset.range n, a (K + x) X :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    linarith
  have hsum1 : Summable fun e => w (e + 1) :=
    summable_of_sum_range_le (fun e => hw0 _) (hpart 1 le_rfl)
  have hsum : Summable w := (summable_nat_add_iff 1).1 hsum1
  have htsum : ∀ K : ℕ, 1 ≤ K → ∑' e, w (e + K) ≤ B K := fun K hK =>
    Real.tsum_le_of_sum_range_le (fun e => hw0 _) (hpart K hK)
  refine ⟨hw0, htsum, hsum, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := ((hB.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).and
    (eventually_ge_atTop 1)).exists
  have hlimK : Tendsto (fun X => ∑ e ∈ Finset.range K, a e X) atTop
      (𝓝 (∑ e ∈ Finset.range K, w e)) := tendsto_finsetSum _ fun e _ => ha e
  obtain ⟨X0, hX0⟩ := Metric.tendsto_atTop.1 hlimK (ε / 3) (by linarith)
  refine ⟨max X0 1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have h1 := htail K hK.2 X hX1
  have h2 := hX0 X hXX0
  have h3 := hsum.sum_add_tsum_nat_add K
  have h4 := htsum K hK.2
  have h5 : 0 ≤ ∑' e, w (e + K) := tsum_nonneg fun e => hw0 _
  rw [Real.dist_eq, abs_lt] at h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hK.1]

/-- The whole analysis of `prop:dadd:witness-means` at one `t` and one cofactor offset `o`. -/
theorem witness_key (hCount : Step_DaddWitnessCount) (C : ℝ)
    (hC : ∀ t : ℝ, 0 < t → ∀ K : ℕ, 1 ≤ K → ∀ X : ℝ, 1 ≤ X →
      1 / X * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t K N : ℝ) ≤ C * t ^ 3 / K)
    (hC0 : 0 ≤ C) (o : ℕ) (ho : 1 ≤ o) (t : ℝ) (ht : 0 < t) :
    (∀ e, 0 ≤ wE (e + o) t) ∧ (∀ K : ℕ, 1 ≤ K → ∑' e, wE (e + K + o) t ≤ C * t ^ 3 / K) ∧
      Summable (fun e => wE (e + o) t) ∧
      Tendsto (fun X : ℝ => 1 / X * ∑ e ∈ Finset.Icc o ⌊t * X⌋₊, (cntE e t X : ℝ)) atTop
        (𝓝 (∑' e, wE (e + o) t)) := by
  have hmain := limit_interchange (S := fun X : ℝ => 1 / X * ∑ e ∈ Finset.Icc o ⌊t * X⌋₊,
      (cntE e t X : ℝ)) (a := fun e X => 1 / X * (cntE (e + o) t X : ℝ))
    (w := fun e => wE (e + o) t) (B := fun K => C * t ^ 3 / K) ?_ ?_ ?_ ?_
  · refine ⟨hmain.1, fun K hK => ?_, hmain.2.2.1, hmain.2.2.2⟩
    have := hmain.2.1 K hK
    simpa only [add_assoc] using this
  · intro e
    have he : 1 ≤ e + o := by omega
    have hfun : (fun X : ℝ => 1 / X * (cntE (e + o) t X : ℝ)) = fun X : ℝ =>
        ∑ a ∈ witnessResidues (e + o), 1 / X *
          (((Finset.Icc 1 ⌊t * X⌋₊).filter (fun n : ℕ =>
            n % lcmUpTo ((e + o : ℕ) : ℝ) = a % lcmUpTo ((e + o : ℕ) : ℝ) ∧ 1 / t ≤ g (e + o) n ∧
              (n : ℝ) * g (e + o) n ≤ X)).card : ℝ) := by
      funext X
      rw [cntE_eq_sum_classes he, Nat.cast_sum, Finset.mul_sum]
    rw [hfun]
    unfold wE
    refine tendsto_finsetSum _ fun a ha => ?_
    simp only [witnessResidues, Finset.mem_filter] at ha
    exact hCount (e + o) a he ha.2 t ht
  · intro e X hX
    have : (0 : ℝ) < X := by linarith
    positivity
  · exact tendsto_const_div_atTop_nhds_zero_nat (C * t ^ 3)
  · intro K hK X hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hsplit := sum_split (fun e => (cntE e t X : ℝ)) ⌊t * X⌋₊ o K ho
      (fun e he => by rw [cntE_eq_zero_of_lt he, Nat.cast_zero])
    have htail := sum_rtTail_eq (X := X) ht (K + o - 1)
    have hJ : 1 ≤ K + o - 1 := by omega
    have hbd := hC t ht (K + o - 1) hJ X hX
    have hnn : 0 ≤ ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t (K + o - 1 : ℕ) N : ℝ) :=
      Finset.sum_nonneg fun N _ => Nat.cast_nonneg _
    have hcast : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t (K + o - 1 : ℕ) N : ℝ) =
        ∑ e ∈ (Finset.Icc 1 ⌊t * X⌋₊).filter
          (fun e : ℕ => ((K + o - 1 : ℕ) : ℝ) < e), (cntE e t X : ℝ) := by
      rw [← Nat.cast_sum, htail, Nat.cast_sum]
    have hdiff : 1 / X * ∑ e ∈ Finset.Icc o ⌊t * X⌋₊, (cntE e t X : ℝ) -
        ∑ e ∈ Finset.range K, 1 / X * (cntE (e + o) t X : ℝ) =
        1 / X * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t (K + o - 1 : ℕ) N : ℝ) := by
      rw [hcast, hsplit, ← Finset.mul_sum]
      ring
    rw [hdiff]
    refine ⟨by positivity, hbd.trans ?_⟩
    have hK' : (K : ℝ) ≤ ((K + o - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ K + o - 1)
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    exact div_le_div_of_nonneg_left (by positivity) hKpos hK'

end Principia.Erdos1054.Proofs.WitnessMeans

namespace Principia.Erdos1054.Proofs

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Proofs.WitnessMeans

theorem link_Prop_DaddWitnessMeans : Principia.Erdos1054.Spine.Link_Prop_DaddWitnessMeans := by
  intro _hId hCount hTail hPB
  obtain ⟨C, hC2⟩ := hTail 2 le_rfl
  have hC : ∀ t : ℝ, 0 < t → ∀ K : ℕ, 1 ≤ K → ∀ X : ℝ, 1 ≤ X →
      1 / X * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t K N : ℝ) ≤ C * t ^ 3 / K := by
    intro t ht K hK X hX
    have h := hC2 t ht K (by exact_mod_cast hK) X hX
    have hpow : ((K : ℕ) : ℝ) ^ (1 - ((2 : ℕ) : ℝ)) = 1 / (K : ℝ) := by
      rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
    rw [hpow] at h
    calc 1 / X * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t K N : ℝ) ≤ C * t ^ (2 + 1) * (1 / K) := h
      _ = C * t ^ 3 / K := by ring
  have hC0 : 0 ≤ C := by
    have h := hC 1 one_pos 1 le_rfl 1 le_rfl
    have hnn : 0 ≤ 1 / (1 : ℝ) * ∑ N ∈ Finset.Icc 1 ⌊(1 : ℝ)⌋₊, (rtTail 1 (1 : ℕ) N : ℝ) := by
      positivity
    simp only [one_pow, mul_one, Nat.cast_one, div_one, one_mul] at h hnn
    linarith
  have hk := witness_key hCount C hC hC0
  -- the averages are cofactor sums
  have havg : ∀ t : ℝ, 0 < t → ∀ X : ℝ,
      1 / X * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rt t N : ℝ) =
        1 / X * ∑ e ∈ Finset.Icc 1 ⌊t * X⌋₊, (cntE e t X : ℝ) := by
    intro t ht X
    rw [← Nat.cast_sum, sum_rt_eq ht, Nat.cast_sum]
  have havgS : ∀ t : ℝ, 0 < t → ∀ X : ℝ,
      1 / X * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtStar t N : ℝ) =
        1 / X * ∑ e ∈ Finset.Icc 2 ⌊t * X⌋₊, (cntE e t X : ℝ) := by
    intro t ht X
    rw [← Nat.cast_sum, sum_rtStar_eq ht, Nat.cast_sum]
  -- the partial sums are continuous
  have hcont1 : ∀ o : ℕ, 1 ≤ o → ∀ T : ℝ, ∀ E : ℕ,
      ContinuousOn (fun t => ∑ e ∈ Finset.range E, wE (e + o) t) (Set.Ioc 0 T) :=
    fun o ho T E => continuousOn_finsetSum _ fun e _ =>
      ((hPB (e + o) (by omega)).1).mono Set.Ioc_subset_Ioi_self
  -- uniform convergence of the series
  have hunif : ∀ o : ℕ, 1 ≤ o → ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun (E : ℕ) (t : ℝ) => ∑ e ∈ Finset.range E, wE (e + o) t)
        (fun t => ∑' e, wE (e + o) t) atTop (Set.Ioc 0 T) := by
    intro o ho T hT
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨E, hE⟩ := ((tendsto_const_div_atTop_nhds_zero_nat (C * T ^ 3)).eventually
      (gt_mem_nhds hε)).and (eventually_ge_atTop 1) |>.exists_forall_of_atTop
    refine Filter.eventually_atTop.2 ⟨E, fun E' hE' t ht => ?_⟩
    obtain ⟨-, htl, hs, -⟩ := hk o ho t ht.1
    have h3 := hs.sum_add_tsum_nat_add E'
    have hE'1 : 1 ≤ E' := le_trans (hE E le_rfl).2 hE'
    have h4 := htl E' hE'1
    have h5 : 0 ≤ ∑' e, wE (e + E' + o) t :=
      tsum_nonneg fun e => (hk o ho t ht.1).1 (e + E')
    have hE'pos : (0 : ℝ) < E' := by exact_mod_cast hE'1
    have h6 : C * t ^ 3 / E' ≤ C * T ^ 3 / E' := by
      apply div_le_div_of_nonneg_right _ hE'pos.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2 3) hC0
    have h7 := (hE E' hE').1
    rw [Real.dist_eq, ← h3]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcontW : ∀ o : ℕ, 1 ≤ o → ContinuousOn (fun t => ∑' e, wE (e + o) t) (Set.Ioi 0) := by
    intro o ho t ht
    have hT : ContinuousOn (fun t => ∑' e, wE (e + o) t) (Set.Ioc 0 (2 * t)) :=
      (hunif o ho (2 * t) (by linarith [ht.out])).continuousOn
        (Filter.Frequently.of_forall fun E => hcont1 o ho (2 * t) E)
    have hmem : Set.Ioc 0 (2 * t) ∈ 𝓝[Set.Ioi 0] t := by
      have ht0 : (0 : ℝ) < t := ht
      have : Set.Iic (2 * t) ∈ 𝓝 t := Iic_mem_nhds (by linarith)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with s hs1 hs2
      exact ⟨hs1, hs2⟩
    exact (hT t ⟨ht, by linarith [ht.out]⟩).mono_of_mem_nhdsWithin hmem
  refine ⟨fun t ht => ⟨?_, ?_, ?_, ?_⟩, hcontW 1 le_rfl, hcontW 2 (by norm_num),
    fun T hT => ⟨hunif 1 le_rfl T hT, hunif 2 (by norm_num) T hT⟩, ?_⟩
  · rw [show Wfun t = ∑' e, wE (e + 1) t from rfl]
    exact (hk 1 le_rfl t ht).2.2.2.congr fun X => (havg t ht X).symm
  · rw [show WstarFun t = ∑' e, wE (e + 2) t from rfl]
    exact (hk 2 (by norm_num) t ht).2.2.2.congr fun X => (havgS t ht X).symm
  · exact (hk 1 le_rfl t ht).2.2.1.hasSum
  · exact (hk 2 (by norm_num) t ht).2.2.1.hasSum
  · -- `W(t) → 0` as `t ↓ 0`
    have hW : ∀ t : ℝ, 0 < t → 0 ≤ Wfun t ∧ Wfun t ≤ wE 1 t + C * t ^ 3 := by
      intro t ht
      obtain ⟨h0, htl, hs, -⟩ := hk 1 le_rfl t ht
      have h3 := hs.sum_add_tsum_nat_add 1
      have h4 := htl 1 le_rfl
      simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_one,
        div_one] at h3 h4
      refine ⟨tsum_nonneg h0, ?_⟩
      rw [show Wfun t = ∑' e, wE (e + 1) t from rfl, ← h3]
      linarith
    have hup : Tendsto (fun t : ℝ => wE 1 t + C * t ^ 3) (𝓝[>] 0) (𝓝 0) := by
      have h1 := (hPB 1 le_rfl).2.2
      have h2 : Tendsto (fun t : ℝ => C * t ^ 3) (𝓝[>] 0) (𝓝 (C * 0 ^ 3)) :=
        tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const.mul (continuous_pow 3)).tendsto 0)
      have := h1.add h2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht using (hW t ht).1
    · filter_upwards [self_mem_nhdsWithin] with t ht using (hW t ht).2

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.WitnessMeans

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits

/-- The support condition `ν_{a,e}{h − c_e(a) < 1/e} = 0` from the progression laws alone. -/
theorem support_of_PL (hPL : Fact_DaddProgressionLaws) {e a : ℕ} (he : 1 ≤ e) (hea : e ∣ a) :
    progLaw e a {h : ℝ | h - cRes e a < 1 / (e : ℝ)} = 0 := by
  obtain ⟨⟨hfin, -⟩, -, hna, -, hcs⟩ := hPL e he a
  set c := cRes e a with hcdef
  have hB : {h : ℝ | h - c < 1 / (e : ℝ)} = Iio (c + 1 / e) := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor <;> intro h' <;> linarith
  rw [hB]
  have hfr : progLaw e a (frontier (Iio (c + 1 / e))) = 0 := by
    rw [frontier_Iio]
    exact measure_singleton _
  have hd := hcs _ measurableSet_Iio hfr
  have h0 := hasDens_eq_zero_of_forall (fun n (hn : n % lcmUpTo (e : ℝ) = a % lcmUpTo (e : ℝ) ∧
      abundancy n ∈ Iio (c + 1 / e)) => by
      by_contra h0
      obtain ⟨-, hg, hge⟩ := witness_identity he (Nat.one_le_iff_ne_zero.2 h0) hn.1 hea
      have h2 := hn.2
      simp only [Set.mem_Iio] at h2
      linarith) hd
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0

theorem lcmUpTo_one : lcmUpTo ((1 : ℕ) : ℝ) = 1 := by
  simp [lcmUpTo]

theorem lcmUpTo_one_real : lcmUpTo (1 : ℝ) = 1 := by
  simp [lcmUpTo]

end Principia.Erdos1054.Proofs.WitnessMeans

namespace Principia.Erdos1054.Proofs

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Proofs.WitnessMeans

theorem link_Rem_DaddWitnessMeanGrowth :
    Principia.Erdos1054.Spine.Link_Rem_DaddWitnessMeanGrowth := by
  intro hCFM hWM hPL
  -- the lower class mean at `Q = 1` is `W`
  have hlam : ∀ A : ℝ, 0 < A → Coverage.lamLower 1 0 A = Wfun A := by
    intro A hA
    have h := (hWM.1 A hA).1
    have hfilt : ∀ X : ℕ, (Finset.Icc 1 X).filter (fun N : ℕ => N % 1 = 0 % 1) =
        Finset.Icc 1 X := fun X => Finset.filter_true_of_mem fun N _ => by simp [Nat.mod_one]
    unfold Coverage.lamLower
    have h2 : Tendsto (fun X : ℕ => ((1 : ℕ) : ℝ) / X *
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N : ℕ => N % 1 = 0 % 1), (rt A N : ℝ)) atTop
        (𝓝 (Wfun A)) := by
      refine (h.comp tendsto_natCast_atTop_atTop).congr fun X => ?_
      rw [hfilt X, Function.comp_apply, Nat.floor_natCast, Nat.cast_one]
    exact h2.liminf_eq
  -- `w_1(t) ≤ 1`
  have hw1 : ∀ t : ℝ, 0 < t → wE 1 t ≤ 1 := by
    intro t ht
    have hres : witnessResidues 1 = {0} := by
      simp [witnessResidues, lcmUpTo_one_real]
    have hc0 : cRes 1 0 = 0 := by simp [cRes]
    unfold wE
    rw [hres, Finset.sum_singleton, hc0]
    obtain ⟨⟨hfin, -⟩, -, -, hmass, -⟩ := hPL 1 le_rfl 0
    have hsupp := support_of_PL hPL (e := 1) (a := 0) le_rfl (dvd_zero 1)
    rw [hc0] at hsupp
    have hae : ∀ᵐ h ∂(progLaw 1 0), 1 ≤ h := by
      rw [ae_iff]
      have hset : {h : ℝ | ¬ 1 ≤ h} = {h : ℝ | h - 0 < 1 / ((1 : ℕ) : ℝ)} := by
        ext h
        simp
      rw [hset]
      exact hsupp
    calc ∫ h in {h : ℝ | 1 / t ≤ h - 0}, 1 / (h - 0) ∂progLaw 1 0
        ≤ ∫ h in {h : ℝ | 1 / t ≤ h - 0}, (1 : ℝ) ∂progLaw 1 0 := by
          refine setIntegral_mono_on_ae (piece_integrableOn _ 0 t ht)
            (integrable_const (1 : ℝ)).integrableOn (measurableSet_pieceSet 0 t) ?_
          filter_upwards [hae] with h hh _
          rw [sub_zero]
          exact (div_le_one (by linarith)).2 hh
      _ = (progLaw 1 0).real {h : ℝ | 1 / t ≤ h - 0} := by
          rw [setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ (progLaw 1 0).real univ := measureReal_mono (subset_univ _)
      _ = 1 := by
          rw [measureReal_def, hmass, lcmUpTo_one]
          simp
  obtain ⟨c, hc, A₀, hA₀⟩ := hCFM.1 1 le_rfl 0
  have hWlow : ∀ t : ℝ, max A₀ 1 ≤ t → c * t / (Real.log t) ^ 2 ≤ Wfun t := by
    intro t ht
    have ht0 : 0 < t := by linarith [le_max_right A₀ 1]
    rw [← hlam t ht0, mul_div_assoc]
    exact hA₀ t (le_trans (le_max_left _ _) ht)
  refine ⟨⟨c, hc, max A₀ 1, hWlow⟩, hw1, ?_⟩
  -- `W* = W − w_1`
  have hstar : ∀ t : ℝ, 0 < t → WstarFun t = Wfun t - wE 1 t := by
    intro t ht
    obtain ⟨-, -, hW1, hW2⟩ := hWM.1 t ht
    have h' := (hasSum_nat_add_iff' 1).2 hW1
    simp only [Finset.range_one, Finset.sum_singleton, zero_add] at h'
    exact hW2.unique h'
  have hlog := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 (hlog.eventually (gt_mem_nhds (half_pos hc)))
  refine ⟨c / 2, half_pos hc, max (max A₀ 1) (max T₁ 2), fun t ht => ?_⟩
  have ht1 : max A₀ 1 ≤ t := le_trans (le_max_left _ _) ht
  have htT : T₁ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht2 : 2 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log t ^ 2 := by positivity
  have h1 := hT₁ t htT
  simp only [one_mul, add_zero] at h1
  have h3 : Real.log t ^ 2 < c / 2 * t := by
    rw [div_lt_iff₀ ht0] at h1
    linarith
  have h4 : 1 < c / 2 * t / Real.log t ^ 2 := by
    rw [lt_div_iff₀ hl2]
    linarith
  have h5 := hWlow t ht1
  have h6 := hw1 t ht0
  rw [hstar t ht0]
  have h7 : c * t / Real.log t ^ 2 = 2 * (c / 2 * t / Real.log t ^ 2) := by ring
  rw [h7] at h5
  linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.WitnessMeans

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction
open Principia.Erdos1054 Principia.Erdos1054.Limits

/-! ### Densities along the reals, rescaled -/

theorem hasDens_real {S : Set ℕ} {δ : ℝ} (h : HasDens S δ) :
    Tendsto (fun Y : ℝ => (cnt S Y : ℝ) / Y) atTop (𝓝 δ) := by
  have h1 : Tendsto (fun Y : ℝ => (cnt S (⌊Y⌋₊ : ℝ) : ℝ) / (⌊Y⌋₊ : ℝ)) atTop (𝓝 δ) :=
    h.comp tendsto_nat_floor_atTop
  have h2 : Tendsto (fun Y : ℝ => (⌊Y⌋₊ : ℝ) / Y) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  have hfl : (0 : ℝ) < ⌊Y⌋₊ := by exact_mod_cast Nat.floor_pos.2 hY
  have hY0 : (0 : ℝ) < Y := by linarith
  rw [cnt_floor]
  field_simp

theorem hasDens_scaled {S : Set ℕ} {δ : ℝ} (h : HasDens S δ) (s : ℝ) :
    Tendsto (fun X : ℝ => (cnt S (s * X) : ℝ) / X) atTop (𝓝 (max s 0 * δ)) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [max_eq_right hs, zero_mul]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with X hX
    rw [cnt_of_lt_one S (by nlinarith), Nat.cast_zero, zero_div]
  · rw [max_eq_left hs.le]
    have h1 := ((hasDens_real h).comp (tendsto_id.const_mul_atTop hs)).const_mul s
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    simp only [Function.comp, id]
    field_simp

theorem le_floor_iff_one_le {n : ℕ} (hn : 1 ≤ n) (Y : ℝ) : n ≤ ⌊Y⌋₊ ↔ (n : ℝ) ≤ Y := by
  rcases le_or_gt 0 Y with hY | hY
  · exact Nat.le_floor_iff hY
  · rw [Nat.floor_of_nonpos hY.le]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · intro h
      omega
    · intro h
      linarith

theorem frontier_Ioc_subset' (c d : ℝ) : frontier (Ioc c d) ⊆ {c, d} := by
  rcases lt_or_ge c d with h | h
  · rw [frontier_Ioc h]
  · rw [Set.Ioc_eq_empty (not_lt.2 h), frontier_empty]
    exact Set.empty_subset _

/-! ### The joint empirical measures `(1/X) ∑_{n ≤ tX, n ≡ a} δ_{(n/X, h(n))}` -/

/-- The joint empirical measure of the proof of `prop:dadd:witness-means`. -/
noncomputable def empJ (L a : ℕ) (t X : ℝ) : Measure (ℝ × ℝ) :=
  (Real.toNNReal (1 / X)) • ∑ n ∈ (Finset.Icc 1 ⌊t * X⌋₊).filter (fun n => n % L = a % L),
    Measure.dirac (((n : ℝ) / X), abundancy n)

instance (L a : ℕ) (t X : ℝ) : IsFiniteMeasure (empJ L a t X) := by
  unfold empJ
  infer_instance

open Classical in
theorem empJ_apply (L a : ℕ) (t X : ℝ) (E : Set (ℝ × ℝ)) :
    empJ L a t X E = ((Real.toNNReal (1 / X) : ℝ≥0) : ℝ≥0∞) *
      (((Finset.Icc 1 ⌊t * X⌋₊).filter
        (fun n => n % L = a % L ∧ (((n : ℝ) / X), abundancy n) ∈ E)).card : ℝ≥0∞) := by
  classical
  rw [empJ, Measure.coe_nnreal_smul_apply, Measure.finsetSum_apply]
  congr 1
  simp only [Measure.dirac_apply, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, Finset.filter_filter]

open Classical in
theorem empJ_real (L a : ℕ) (t : ℝ) {X : ℝ} (hX : 0 < X) (E : Set (ℝ × ℝ)) :
    (empJ L a t X).real E = 1 / X *
      (((Finset.Icc 1 ⌊t * X⌋₊).filter
        (fun n => n % L = a % L ∧ (((n : ℝ) / X), abundancy n) ∈ E)).card : ℝ) := by
  rw [measureReal_def, empJ_apply, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast,
    Real.coe_toNNReal _ (by positivity)]

theorem empJ_integral (L a : ℕ) (t : ℝ) {X : ℝ} (hX : 0 < X) (φ : ℝ × ℝ →ᵇ ℝ) :
    ∫ p, φ p ∂(empJ L a t X) = 1 / X *
      ∑ n ∈ (Finset.Icc 1 ⌊t * X⌋₊).filter (fun n : ℕ => n % L = a % L),
        φ ((n : ℝ) / X, abundancy n) := by
  rw [empJ, integral_smul_nnreal_measure, integral_finsetSum_measure]
  · simp only [integral_dirac]
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul]
  · intro n _
    exact φ.integrable _

theorem empJ_real_quadrant (L a : ℕ) (t : ℝ) {X : ℝ} (hX : 0 < X) (s : ℝ) (B : Set ℝ) :
    (empJ L a t X).real (Iic s ×ˢ B) =
      (cnt {n : ℕ | n % L = a % L ∧ abundancy n ∈ B} (min s t * X) : ℝ) / X := by
  rw [empJ_real L a t hX, one_div, inv_mul_eq_div]
  refine congrArg (fun k : ℕ => (k : ℝ) / X) ?_
  unfold cnt
  refine congrArg Finset.card ?_
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_prod, Set.mem_Iic, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hn1, hnt⟩, hmod, hs, hB⟩
    refine ⟨⟨hn1, (le_floor_iff_one_le hn1 _).2 ?_⟩, hmod, hB⟩
    rw [div_le_iff₀ hX] at hs
    have h1 := (le_floor_iff_one_le hn1 _).1 hnt
    rw [min_mul_of_nonneg _ _ hX.le]
    exact le_min (by linarith) (by linarith)
  · rintro ⟨⟨hn1, hns⟩, hmod, hB⟩
    have h := (le_floor_iff_one_le hn1 _).1 hns
    rw [min_mul_of_nonneg _ _ hX.le] at h
    have h1 := min_le_left (s * X) (t * X)
    have h2 := min_le_right (s * X) (t * X)
    refine ⟨⟨hn1, (le_floor_iff_one_le hn1 _).2 (by linarith)⟩, hmod, ?_, hB⟩
    rw [div_le_iff₀ hX]
    linarith

theorem empJ_real_univ (L a : ℕ) (t : ℝ) {X : ℝ} (hX : 0 < X) :
    (empJ L a t X).real univ = (cnt {n : ℕ | n % L ∈ ({a % L} : Finset ℕ)} (t * X) : ℝ) / X := by
  rw [empJ_real L a t hX, one_div, inv_mul_eq_div]
  refine congrArg (fun k : ℕ => (k : ℝ) / X) ?_
  unfold cnt
  refine congrArg Finset.card ?_
  ext n
  simp

/-- The π-system of half-open boxes of `ℝ × ℝ`. -/
def boxSys : Set (Set (ℝ × ℝ)) := {E | ∃ p q c d : ℝ, E = Ioc p q ×ˢ Ioc c d}

theorem Ioc_inter_Ioc' (a b c d : ℝ) : Ioc a b ∩ Ioc c d = Ioc (max a c) (min b d) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, max_lt_iff, le_min_iff]
  tauto

theorem isPiSystem_boxSys : IsPiSystem boxSys := by
  rintro s ⟨p, q, c, d, rfl⟩ s' ⟨p', q', c', d', rfl⟩ _
  refine ⟨max p p', min q q', max c c', min d d', ?_⟩
  rw [Set.prod_inter_prod, Ioc_inter_Ioc', Ioc_inter_Ioc']

theorem measurableSet_of_boxSys : ∀ s ∈ boxSys, MeasurableSet s := by
  rintro s ⟨p, q, c, d, rfl⟩
  exact measurableSet_Ioc.prod measurableSet_Ioc

theorem boxSys_nhds : ∀ u : Set (ℝ × ℝ), IsOpen u → ∀ x ∈ u, ∃ s ∈ boxSys, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu x hx
  refine ⟨Ioc (x.1 - ε / 2) (x.1 + ε / 2) ×ˢ Ioc (x.2 - ε / 2) (x.2 + ε / 2), ⟨_, _, _, _, rfl⟩,
    prod_mem_nhds (Ioc_mem_nhds (by linarith) (by linarith))
      (Ioc_mem_nhds (by linarith) (by linarith)), fun y hy => hball ?_⟩
  obtain ⟨h1, h2⟩ := hy
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt]
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

theorem box_eq_sdiff (p q : ℝ) (B : Set ℝ) :
    Ioc p q ×ˢ B = (Iic (max p q) ×ˢ B) \ (Iic p ×ˢ B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_sdiff, Set.mem_Iic, le_max_iff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, hy⟩
    exact ⟨⟨Or.inr h2, hy⟩, fun h _ => absurd h (not_le.2 h1)⟩
  · rintro ⟨⟨h1 | h1, hy⟩, h2⟩
    · exact absurd hy (h2 h1)
    · refine ⟨⟨not_le.1 fun h => h2 h hy, h1⟩, hy⟩

theorem measureReal_box (m : Measure (ℝ × ℝ)) [IsFiniteMeasure m] (p q : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) :
    m.real (Ioc p q ×ˢ B) = m.real (Iic (max p q) ×ˢ B) - m.real (Iic p ×ˢ B) := by
  rw [box_eq_sdiff, measureReal_sdiff (Set.prod_mono (Iic_subset_Iic.2 (le_max_left p q))
    subset_rfl) (measurableSet_Iic.prod hB)]

theorem isFiniteMeasure_restrict_Icc (t : ℝ) :
    IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) t)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩

/-- The joint weak limit, from the progression laws: the finite-measure form. -/
theorem joint_tendsto (hPL : Fact_DaddProgressionLaws) {e : ℕ} (he : 1 ≤ e) (a : ℕ) {t : ℝ}
    (ht : 0 < t) :
    haveI := isFiniteMeasure_restrict_Icc t
    haveI := (hPL e he a).1.1
    Tendsto (fun X => toFM (empJ (lcmUpTo (e : ℝ)) a t X)) atTop
      (𝓝 (toFM ((volume.restrict (Icc 0 t)).prod (progLaw e a)))) := by
  haveI := isFiniteMeasure_restrict_Icc t
  obtain ⟨⟨hfin, -⟩, -, hna, hmass, hcs⟩ := hPL e he a
  set L := lcmUpTo (e : ℝ) with hLdef
  have hL : 0 < L := lcmUpTo_pos e
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  set ν := progLaw e a with hν
  set μ2 : Measure (ℝ × ℝ) := (volume.restrict (Icc 0 t)).prod ν with hμ2
  have hdens : ∀ c d : ℝ,
      HasDens {n : ℕ | n % L = a % L ∧ abundancy n ∈ Ioc c d} (ν.real (Ioc c d)) :=
    fun c d => hcs _ measurableSet_Ioc
      (measure_mono_null (frontier_Ioc_subset' c d) ((Set.toFinite _).measure_zero ν))
  have hquad : ∀ s c d : ℝ, Tendsto (fun X => (empJ L a t X).real (Iic s ×ˢ Ioc c d)) atTop
      (𝓝 (μ2.real (Iic s ×ˢ Ioc c d))) := by
    intro s c d
    have hlim := hasDens_scaled (hdens c d) (min s t)
    have hμq : μ2.real (Iic s ×ˢ Ioc c d) = max (min s t) 0 * ν.real (Ioc c d) := by
      have hI : Iic s ∩ Icc 0 t = Icc 0 (min s t) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
        tauto
      rw [measureReal_def, hμ2, Measure.prod_prod, Measure.restrict_apply measurableSet_Iic, hI,
        Real.volume_Icc, ENNReal.toReal_mul, ENNReal.toReal_ofReal', sub_zero, measureReal_def]
    rw [hμq]
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [empJ_real_quadrant L a t hX]
  have hμ0 : μ2 univ ≠ 0 := by
    rw [hμ2, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, hmass]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 ht).ne' (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top L))
  refine fm_tendsto_of_piSystem isPiSystem_boxSys measurableSet_of_boxSys boxSys_nhds
    (fun X => empJ L a t X) μ2 hμ0 ?_ ?_
  · rintro s ⟨p, q, c, d, rfl⟩
    simp only [measureReal_box _ p q _ measurableSet_Ioc]
    exact (hquad _ c d).sub (hquad p c d)
  · have hmassD : HasDens {n : ℕ | n % L ∈ ({a % L} : Finset ℕ)}
        ((({a % L} : Finset ℕ).card : ℝ) / L) :=
      hasDens_mod_mem hL {a % L} (by simp [Nat.mod_lt _ hL])
    have hlim := hasDens_scaled hmassD t
    have hμu : μ2.real univ = max t 0 * ((({a % L} : Finset ℕ).card : ℝ) / L) := by
      rw [measureReal_def, hμ2, ← Set.univ_prod_univ, Measure.prod_prod,
        Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, hmass, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal', ENNReal.toReal_inv, ENNReal.toReal_natCast]
      simp
    rw [hμu]
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [empJ_real_univ L a t hX]

/-! ### The witness region `{h − c ≥ 1/t, u (h − c) ≤ 1}` -/

/-- The witness region in the `(u, h)`-plane. -/
def witnessRegion (c t : ℝ) : Set (ℝ × ℝ) := {p | 1 / t ≤ p.2 - c ∧ p.1 * (p.2 - c) ≤ 1}

theorem measurableSet_witnessRegion (c t : ℝ) : MeasurableSet (witnessRegion c t) := by
  have h1 : MeasurableSet {p : ℝ × ℝ | 1 / t ≤ p.2 - c} :=
    measurableSet_le measurable_const (measurable_snd.sub_const c)
  have h2 : MeasurableSet {p : ℝ × ℝ | p.1 * (p.2 - c) ≤ 1} :=
    measurableSet_le (measurable_fst.mul (measurable_snd.sub_const c)) measurable_const
  exact h1.inter h2

theorem witnessRegion_slice (c t : ℝ) (ht : 0 < t) (h : ℝ) :
    volume.restrict (Icc 0 t) ((fun u : ℝ => (u, h)) ⁻¹' witnessRegion c t) =
      {h : ℝ | 1 / t ≤ h - c}.indicator (fun h => ENNReal.ofReal (1 / (h - c))) h := by
  rw [Measure.restrict_apply' measurableSet_Icc]
  by_cases hh : h ∈ {h : ℝ | 1 / t ≤ h - c}
  · rw [Set.indicator_of_mem hh]
    obtain ⟨h1, h2⟩ := piece_bound ht hh
    have hpos : 0 < h - c := lt_of_lt_of_le (by positivity) hh
    have hset : (fun u : ℝ => (u, h)) ⁻¹' witnessRegion c t ∩ Icc 0 t = Icc 0 (1 / (h - c)) := by
      ext u
      simp only [witnessRegion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
        Set.mem_Icc]
      have hh' : 1 / t ≤ h - c := hh
      rw [le_div_iff₀ hpos]
      constructor
      · rintro ⟨⟨-, hu⟩, hu0, -⟩
        exact ⟨hu0, by linarith⟩
      · rintro ⟨hu0, hu⟩
        refine ⟨⟨hh', by linarith⟩, hu0, ?_⟩
        have : u ≤ 1 / (h - c) := by rw [le_div_iff₀ hpos]; linarith
        linarith
    rw [hset, Real.volume_Icc, sub_zero]
  · rw [Set.indicator_of_notMem hh]
    have hset : (fun u : ℝ => (u, h)) ⁻¹' witnessRegion c t ∩ Icc 0 t = ∅ := by
      ext u
      simp only [witnessRegion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h1
      exact absurd h1.1 hh
    rw [hset, measure_empty]

theorem witnessRegion_measure (ν : Measure ℝ) [IsFiniteMeasure ν] (c t : ℝ) (ht : 0 < t) :
    ((volume.restrict (Icc 0 t)).prod ν).real (witnessRegion c t) =
      ∫ h in {h : ℝ | 1 / t ≤ h - c}, 1 / (h - c) ∂ν := by
  rw [measureReal_def, Measure.prod_apply_symm (measurableSet_witnessRegion c t)]
  simp only [witnessRegion_slice c t ht]
  rw [lintegral_indicator (measurableSet_pieceSet c t),
    ← ofReal_integral_eq_lintegral_ofReal (piece_integrableOn ν c t ht)
      (ae_restrict_of_forall_mem (measurableSet_pieceSet c t) fun h hh =>
        (piece_bound ht hh).1.le),
    ENNReal.toReal_ofReal (piece_nonneg ν c t ht)]

theorem witnessRegion_frontier (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] (c t : ℝ) :
    ((volume.restrict (Icc 0 t)).prod ν) (frontier (witnessRegion c t)) = 0 := by
  haveI := isFiniteMeasure_restrict_Icc t
  set μ2 := (volume.restrict (Icc 0 t)).prod ν
  have hA : frontier {p : ℝ × ℝ | 1 / t ≤ p.2 - c} ⊆ univ ×ˢ {c + 1 / t} := by
    refine (frontier_le_subset_eq continuous_const (continuous_snd.sub continuous_const)).trans ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and]
    linarith
  have hB : frontier {p : ℝ × ℝ | p.1 * (p.2 - c) ≤ 1} ⊆ {p : ℝ × ℝ | p.1 * (p.2 - c) = 1} :=
    frontier_le_subset_eq (continuous_fst.mul (continuous_snd.sub continuous_const))
      continuous_const
  have hA0 : μ2 (univ ×ˢ {c + 1 / t}) = 0 := by
    rw [Measure.prod_prod, measure_singleton, mul_zero]
  have hB0 : μ2 {p : ℝ × ℝ | p.1 * (p.2 - c) = 1} = 0 := by
    rw [Measure.prod_apply_symm (measurableSet_eq_fun
      (measurable_fst.mul (measurable_snd.sub_const c)) measurable_const)]
    refine (lintegral_congr fun h => ?_).trans lintegral_zero
    rw [Measure.restrict_apply' measurableSet_Icc]
    refine measure_mono_null (Set.inter_subset_left.trans ?_) (measure_singleton (1 / (h - c)))
    intro u hu
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hu
    have hne : h - c ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hu
      exact zero_ne_one hu
    rw [Set.mem_singleton_iff, eq_div_iff hne]
    exact hu
  have hsub : frontier (witnessRegion c t) ⊆ univ ×ˢ {c + 1 / t} ∪
      {p : ℝ × ℝ | p.1 * (p.2 - c) = 1} := by
    refine (frontier_inter_subset _ _).trans ?_
    rintro p (⟨hp, -⟩ | ⟨-, hp⟩)
    · exact Or.inl (hA hp)
    · exact Or.inr (hB hp)
  exact measure_mono_null hsub (measure_union_null hA0 hB0)

end Principia.Erdos1054.Proofs.WitnessMeans

namespace Principia.Erdos1054.Proofs

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Proofs.WitnessMeans

theorem link_Step_DaddWitnessJointLimit :
    Principia.Erdos1054.Spine.Link_Step_DaddWitnessJointLimit := by
  intro hPL e a he t ht φ
  haveI := isFiniteMeasure_restrict_Icc t
  haveI := (hPL e he a).1.1
  have hint := fm_integral_tendsto _ _ (joint_tendsto hPL he a ht) φ
  refine hint.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [empJ_integral _ a t hX]

theorem link_Step_DaddWitnessCount : Principia.Erdos1054.Spine.Link_Step_DaddWitnessCount := by
  intro _hId hJ _hSupp hPL e a he hea t ht
  haveI := isFiniteMeasure_restrict_Icc t
  obtain ⟨⟨hfin, -⟩, -, hna, hmass, -⟩ := hPL e he a
  set L := lcmUpTo (e : ℝ) with hLdef
  set ν := progLaw e a with hν
  set μ2 : Measure (ℝ × ℝ) := (volume.restrict (Icc 0 t)).prod ν with hμ2
  have hμ0 : μ2 univ ≠ 0 := by
    rw [hμ2, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, hmass]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 ht).ne' (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top L))
  -- the weak convergence, from the joint limit
  have hconv : Tendsto (fun X => toFM (empJ L a t X)) atTop (𝓝 (toFM μ2)) := by
    refine FiniteMeasure.tendsto_iff_forall_integral_tendsto.2 fun φ => ?_
    refine (hJ e a he t ht φ).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact (empJ_integral L a t hX φ).symm
  have hreg := fm_measureReal_tendsto _ μ2 hμ0 hconv (witnessRegion_frontier ν (cRes e a) t)
  rw [witnessRegion_measure ν (cRes e a) t ht] at hreg
  refine hreg.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [empJ_real L a t hX]
  refine congrArg (fun s : Finset ℕ => 1 / X * (s.card : ℝ)) ?_
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, witnessRegion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, hmod, h1, h2⟩
    obtain ⟨-, hg, -⟩ := witness_identity he hn.1 hmod hea
    refine ⟨hn, hmod, by rw [hg]; exact h1, ?_⟩
    rw [hg]
    rw [div_mul_eq_mul_div, div_le_one hX] at h2
    exact h2
  · rintro ⟨hn, hmod, h1, h2⟩
    obtain ⟨-, hg, -⟩ := witness_identity he hn.1 hmod hea
    refine ⟨hn, hmod, by rw [← hg]; exact h1, ?_⟩
    rw [← hg, div_mul_eq_mul_div, div_le_one hX]
    exact h2

end Principia.Erdos1054.Proofs
