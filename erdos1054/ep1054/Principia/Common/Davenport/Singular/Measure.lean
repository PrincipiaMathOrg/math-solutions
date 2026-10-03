/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false

/-!
# From an arithmetic covering to mutual singularity

Let `f : ℕ → ℝ` and let `μ` be a probability measure on `ℝ` such that, for every `u`, the
proportion of `1 ≤ n ≤ X` with `f n ≤ u` tends to `μ (Iic u)` (`HasLimitOn f μ (Iic u)`).

* `hasLimitOn_biUnion_Ioc`: the proportion of `n` with `f n` in any **finite union of half-open
  intervals** `U` tends to `μ U` (inclusion–exclusion, by induction on the index set, using
  `Ioc ∩ Ioc = Ioc`).
* `mutuallySingular_of_cover`: if for every `0 < ε ≤ 1` some finite union of `Ioc`s has total
  length `≤ ε` and eventually contains `f n` for at least `(1 − ε) X` of the `n ≤ X`, then
  `μ ⟂ₘ volume`. With `ε_k = 2^{-k}` the sets `U_k` satisfy `∑ μ(U_kᶜ) < ∞` and `∑ vol(U_k) < ∞`;
  Borel–Cantelli makes "`x ∉ U_k` infinitely often" `μ`-null and "`x ∈ U_k` infinitely often"
  Lebesgue-null, and the two cover `ℝ` (`Measure.MutuallySingular.mk`). No weak convergence and no
  purity law are needed.
-/

namespace Principia.Common.Davenport.Singular

open Finset Filter MeasureTheory
open scoped Topology ENNReal

open Classical in
/-- `#{1 ≤ n ≤ X : f n ∈ S}`. -/
noncomputable def countIn (f : ℕ → ℝ) (S : Set ℝ) (X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun n => f n ∈ S)).card

/-- The proportion of `n ≤ X` with `f n ∈ S` tends to `μ S`. -/
def HasLimitOn (f : ℕ → ℝ) (μ : Measure ℝ) (S : Set ℝ) : Prop :=
  Tendsto (fun X : ℕ => (countIn f S X : ℝ) / X) atTop (𝓝 (μ.real S))

theorem countIn_empty (f : ℕ → ℝ) (X : ℕ) : countIn f ∅ X = 0 := by
  unfold countIn
  rw [Finset.card_eq_zero]
  ext n
  simp

theorem countIn_union_add_inter (f : ℕ → ℝ) (A B : Set ℝ) (X : ℕ) :
    countIn f (A ∪ B) X + countIn f (A ∩ B) X = countIn f A X + countIn f B X := by
  classical
  unfold countIn
  have key := Finset.card_union_add_card_inter ((Icc 1 X).filter (fun n => f n ∈ A))
    ((Icc 1 X).filter (fun n => f n ∈ B))
  convert key using 3
  · ext n
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]
    tauto
  · ext n
    simp only [Finset.mem_filter, Finset.mem_inter, Set.mem_inter_iff]
    tauto

theorem hasLimitOn_empty (f : ℕ → ℝ) (μ : Measure ℝ) : HasLimitOn f μ ∅ := by
  unfold HasLimitOn
  simp only [countIn_empty, Nat.cast_zero, zero_div, measureReal_empty]
  exact tendsto_const_nhds

/-- Inclusion–exclusion. -/
theorem hasLimitOn_union {f : ℕ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ] {A B : Set ℝ}
    (hB : MeasurableSet B) (hA' : HasLimitOn f μ A) (hB' : HasLimitOn f μ B)
    (hAB : HasLimitOn f μ (A ∩ B)) : HasLimitOn f μ (A ∪ B) := by
  unfold HasLimitOn at *
  have hμ : μ.real (A ∪ B) = μ.real A + μ.real B - μ.real (A ∩ B) := by
    have := measureReal_union_add_inter (μ := μ) (s := A) hB
    linarith
  rw [hμ]
  refine ((hA'.add hB').sub hAB).congr fun X => ?_
  have h := countIn_union_add_inter f A B X
  have h' : (countIn f (A ∪ B) X : ℝ) =
      (countIn f A X : ℝ) + countIn f B X - countIn f (A ∩ B) X := by
    have : ((countIn f (A ∪ B) X + countIn f (A ∩ B) X : ℕ) : ℝ) =
        ((countIn f A X + countIn f B X : ℕ) : ℝ) := by rw [h]
    push_cast at this
    linarith
  rw [h']
  ring

/-- `Ioc a b` from two `Iic`s. -/
theorem hasLimitOn_Ioc {f : ℕ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hIic : ∀ u, HasLimitOn f μ (Set.Iic u)) (a b : ℝ) : HasLimitOn f μ (Set.Ioc a b) := by
  rcases le_or_gt a b with hab | hab
  · have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx (not_le.2 hx'.1)
    have hunion : Set.Iic a ∪ Set.Ioc a b = Set.Iic b := Set.Iic_union_Ioc_eq_Iic hab
    have hμ : μ.real (Set.Ioc a b) = μ.real (Set.Iic b) - μ.real (Set.Iic a) := by
      have := measureReal_union (μ := μ) hdisj measurableSet_Ioc
      rw [hunion] at this
      linarith
    have hcount : ∀ X, (countIn f (Set.Ioc a b) X : ℝ) =
        countIn f (Set.Iic b) X - countIn f (Set.Iic a) X := by
      intro X
      have h := countIn_union_add_inter f (Set.Iic a) (Set.Ioc a b) X
      rw [hunion, Set.disjoint_iff_inter_eq_empty.1 hdisj, countIn_empty] at h
      have : ((countIn f (Set.Iic b) X + 0 : ℕ) : ℝ) =
          ((countIn f (Set.Iic a) X + countIn f (Set.Ioc a b) X : ℕ) : ℝ) := by rw [h]
      push_cast at this
      linarith
    unfold HasLimitOn at *
    rw [hμ]
    refine ((hIic b).sub (hIic a)).congr fun X => ?_
    rw [hcount X]
    ring
  · rw [Set.Ioc_eq_empty (not_lt.2 hab.le)]
    exact hasLimitOn_empty f μ

/-- **Finite unions of half-open intervals.** -/
theorem hasLimitOn_biUnion_Ioc {f : ℕ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hIic : ∀ u, HasLimitOn f μ (Set.Iic u)) {ι : Type*} (s : Finset ι) :
    ∀ lo hi : ι → ℝ, HasLimitOn f μ (⋃ k ∈ s, Set.Ioc (lo k) (hi k)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro lo hi
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact hasLimitOn_empty f μ
  | insert j s _ ih =>
    intro lo hi
    rw [Finset.set_biUnion_insert]
    have hmeas : MeasurableSet (⋃ k ∈ s, Set.Ioc (lo k) (hi k)) :=
      Finset.measurableSet_biUnion s fun k _ => measurableSet_Ioc
    refine hasLimitOn_union hmeas (hasLimitOn_Ioc hIic _ _) (ih lo hi) ?_
    have hinter : Set.Ioc (lo j) (hi j) ∩ ⋃ k ∈ s, Set.Ioc (lo k) (hi k) =
        ⋃ k ∈ s, Set.Ioc (lo j ⊔ lo k) (hi j ⊓ hi k) := by
      rw [Set.inter_iUnion₂]
      refine Set.iUnion₂_congr fun k _ => ?_
      rw [Set.Ioc_inter_Ioc]
    rw [hinter]
    exact ih (fun k => lo j ⊔ lo k) (fun k => hi j ⊓ hi k)

/-- A covering with proportion `≥ 1 − ε` has measure `≥ 1 − ε`. -/
theorem measureReal_ge_of_eventually {f : ℕ → ℝ} {μ : Measure ℝ} {U : Set ℝ} {ε : ℝ}
    (hU : HasLimitOn f μ U) (hev : ∀ᶠ X : ℕ in atTop, (1 - ε) * X ≤ countIn f U X) :
    1 - ε ≤ μ.real U := by
  refine ge_of_tendsto hU ?_
  filter_upwards [hev, eventually_ge_atTop 1] with X hX hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  rw [le_div_iff₀ hXpos]
  exact hX

/-- The Lebesgue measure of a finite union of `Ioc`s is at most the sum of the lengths. -/
theorem volume_biUnion_Ioc_le {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    (hle : ∀ k ∈ s, lo k ≤ hi k) :
    volume (⋃ k ∈ s, Set.Ioc (lo k) (hi k)) ≤ ENNReal.ofReal (∑ k ∈ s, (hi k - lo k)) := by
  calc volume (⋃ k ∈ s, Set.Ioc (lo k) (hi k))
      ≤ ∑ k ∈ s, volume (Set.Ioc (lo k) (hi k)) := measure_biUnion_finset_le s _
    _ = ∑ k ∈ s, ENNReal.ofReal (hi k - lo k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.volume_Ioc]
    _ = ENNReal.ofReal (∑ k ∈ s, (hi k - lo k)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k hk
        linarith [hle k hk]

/-- **Mutual singularity from coverings.** -/
theorem mutuallySingular_of_cover (f : ℕ → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hIic : ∀ u, HasLimitOn f μ (Set.Iic u))
    (hcover : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (S : Finset ((_ : ℕ) × ℕ)) (lo hi : ((_ : ℕ) × ℕ) → ℝ),
        (∀ k ∈ S, lo k ≤ hi k) ∧ (∑ k ∈ S, (hi k - lo k)) ≤ ε ∧
        ∀ᶠ X : ℕ in atTop, (1 - ε) * X ≤ countIn f (⋃ k ∈ S, Set.Ioc (lo k) (hi k)) X) :
    μ.MutuallySingular volume := by
  have hεpos : ∀ k : ℕ, (0 : ℝ) < (1 / 2) ^ k := fun k => by positivity
  have hεle : ∀ k : ℕ, ((1 : ℝ) / 2) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  choose S lo hi hle hlen hev using fun k : ℕ => hcover ((1 / 2) ^ k) (hεpos k) (hεle k)
  set U : ℕ → Set ℝ := fun k => ⋃ j ∈ S k, Set.Ioc (lo k j) (hi k j) with hUdef
  have hUm : ∀ k, MeasurableSet (U k) := fun k =>
    Finset.measurableSet_biUnion _ fun j _ => measurableSet_Ioc
  -- `μ (U k)ᶜ ≤ 2^{-k}`
  have hcompl : ∀ k, μ (U k)ᶜ ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
    intro k
    have h1 := measureReal_ge_of_eventually (hasLimitOn_biUnion_Ioc hIic (S k) (lo k) (hi k))
      (hev k)
    have h2 : μ.real (U k)ᶜ ≤ (1 / 2) ^ k := by
      rw [measureReal_compl (hUm k), probReal_univ]
      linarith
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal h2
  -- `vol (U k) ≤ 2^{-k}`
  have hvol : ∀ k, volume (U k) ≤ ENNReal.ofReal ((1 / 2) ^ k) := fun k =>
    (volume_biUnion_Ioc_le (S k) (lo k) (hi k) (hle k)).trans (ENNReal.ofReal_le_ofReal (hlen k))
  have hsum : ∑' k : ℕ, ENNReal.ofReal (((1 : ℝ) / 2) ^ k) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hεpos k).le) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have hs : μ {x | ∃ᶠ k in atTop, x ∈ (U k)ᶜ} = 0 := by
    apply measure_setOf_frequently_eq_zero
    refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun k => ?_)
    simpa only [Set.setOf_mem_eq] using hcompl k
  have ht : volume {x | ∃ᶠ k in atTop, x ∈ U k} = 0 := by
    apply measure_setOf_frequently_eq_zero
    refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun k => ?_)
    simpa only [Set.setOf_mem_eq] using hvol k
  refine Measure.MutuallySingular.mk hs ht ?_
  intro x _
  by_cases h : ∃ᶠ k in atTop, x ∈ U k
  · exact Or.inr h
  · left
    rw [Filter.not_frequently] at h
    exact h.frequently

end Principia.Common.Davenport.Singular
