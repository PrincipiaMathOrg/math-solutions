/-
# The pointwise Birkhoff ergodic theorem — PORTED, axiom-free on v4.31.0

PROVENANCE — NOT OUR WORK.  Ported from https://github.com/lua-vr/pointwise-birkhoff
(author: Lua Viana Reis; the `QuasiMeasurePreserving` part carries an Oliver Butterley
copyright header, retained below), a complete 0-sorry Lean 4 formalisation on
`leanprover/lean4:v4.20.0-rc5`.  Our contribution is only the v4.20 -> v4.31 port.

WHY: the owner's standing rule (2026-07-28) is that a Lean statement may not carry deep
hypotheses.  `HRTResonantFibre.heil_speegle_lambda_zero` assumed a package including the
pointwise Birkhoff ergodic theorem, which is NOT in Mathlib (verified against Mathlib
`docs/1000.yaml`: the `Birkhoff's ergodic theorem` entry carries no `decls:`).  This file
discharges that component.

HEADLINE:
  `birkhoffErgodicTheorem'` (hf : MeasurePreserving f mu mu) (hPhi : Integrable Phi mu) :
      for a.e. x, Tendsto (birkhoffAverage R f Phi . x) atTop (nhds (invCondexp mu f Phi x))

VERIFIED 2026-07-28: 0 errors, 0 sorries;
  `birkhoffErgodicTheorem`  -> [propext, Classical.choice, Quot.sound]
  `birkhoffErgodicTheorem'` -> [propext, Classical.choice, Quot.sound]

PORT NOTES (v4.20 -> v4.31), all mechanical:
  * 8 staging lemmas had since been UPSTREAMED and clashed ("already declared") — removed,
    together with their doc-comments (an orphaned `/-- -/` is a parse error) and with five
    `open ... in` lines that were left dangling and would otherwise have scoped over the
    WRONG declaration.
  * `add_partialSups` -> Mathlib's `partialSups_const_add` (upstreamed by the same author
    via `@[to_additive]` on `partialSups_const_mul`).
  * `invariant_of_measurable_invariants` -> `MeasurableSpace.comp_eq_of_measurable_invariants`
    (identical statement, renamed on upstreaming).
  * `lt.not_le` -> `lt.not_ge` (2 sites); `zero_le n` -> `Nat.zero_le n` (argument now implicit);
    `add_le_add_left` now concludes `b + a <= c + a`, so the left-add use became
    `sub_le_sub_left`.
  * TRAP: `partialSups_add_one'` still EXISTS in Mathlib but now means the peel-from-BOTTOM
    decomposition `f bot | partialSups (f . +1) i`; the port's intended
    `partialSups f i | f (i+1)` is now the UNPRIMED `partialSups_add_one`.  A name whose
    meaning shifted between versions — the compile error was a type mismatch, not "unknown".
  * `birkhoffMax_measurable`'s `induction <;> measurability` no longer closes; rewritten as an
    explicit induction peeling `partialSups_add_one` and applying `Measurable.sup`.
-/

import Mathlib
set_option maxHeartbeats 1000000

-- ==================== FilterPR ====================


-- ==================== PartialSupsPR ====================


-- To be added to `Mathlib/Order/PartialSups`.
-- Correct name? I think it should be `comp` not `map`:
-- [https://leanprover-community.github.io/contribute/naming.html#names-of-symbols]
/- Note for curiosity with `partialSups_succ'`: In `partialSups_succ` slightly weaker assumptions on
`ι` are used: `[LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι]`. However using just this
breaks the statement because it can't sythesise `[OrderBot ι]`. These assumptions permit an empty
set and perhaps it can't use the hypothesis to exclude this and guarantee the existence of `⊥`.
The assumptions used here match those of `partialSups_bot` in the same file. -/

-- To be added to `Mathlib/Order/PartialSups`
-- ==================== BirkhoffSumPR ====================


-- To go in `Logic/Function/Iterate`? Name as `iterate_of_invariant`?
/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then `φ` remains invariant under any number of iterations of `f`. -/
lemma invariant_iter (h : φ ∘ f = φ) : ∀ i, φ ∘ f^[i] = φ
  | 0 => rfl
  | n + 1 => by
    change (φ ∘ f^[n]) ∘ f = φ
    rwa [invariant_iter h n]

-- To go in `Dynamics/BirkhoffSum/Basic`
/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff sum of `φ` over `f` for `n` iterations is equal to `n • φ`. -/
theorem birkhoffSum_of_invariant [AddCommMonoid M] {φ : α → M}
    (h : φ ∘ f = φ) : birkhoffSum f φ n = n • φ := by
  funext x
  unfold birkhoffSum
  conv in fun _ => _ => intro k; change (φ ∘ f^[k]) x; rw [invariant_iter h k]
  simp

variable {R α : Type*} [DivisionSemiring R]

-- To go in `Dynamics/BirkhoffSum/Average`
-- Note: `[CharZero R]` required for `Nat.cast_ne_zero`.
/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff average of `φ` over `f` for `n` iterations is equal to `φ`
provided `0 < n`. -/
theorem birkhoffAverage_of_invariant {M : Type*} [AddCommMonoid M] [Module R M] [CharZero R]
    {f : α → α} {φ : α → M} (h : φ ∘ f = φ) {n : ℕ} (hn : 0 < n) : birkhoffAverage R f φ n = φ := by
  funext x
  simp only [birkhoffAverage, birkhoffSum_of_invariant h, Pi.smul_apply]
  refine (inv_smul_eq_iff₀ ?_).mpr (by norm_cast)
  exact Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt hn

-- To go in `Dynamics/BirkhoffSum/Average`
-- Note: need something more than `[AddCommMonoid M]` here to have subtraction.
-- ==================== InvariantsPR ====================


open scoped MeasureTheory

namespace MeasurableSpace


end MeasurableSpace


-- ==================== QuasiMeasurePreservingPR ====================
/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/



/-!
# Birkhoff sum and average for measure preserving maps

This file contains some lemmas about the `birkhoffSum` and `birkhoffAverage` of a map which is
`QuasiMeasurePreserving`.
-/

section QuasiMeasurePreserving

open MeasureTheory Measure Filter

variable {α M : Type*} [AddCommMonoid M] [MeasurableSpace α]
variable {f : α → α} {μ : Measure α} {φ φ' : α → M}

/-- If observables  `φ` and `φ'` are `=ᵐ[μ]` equal then the corresponding `birkhoffSum` are `=ᵐ[μ]`
equal. -/
theorem birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] φ') n :
    birkhoffSum f φ n =ᵐ[μ] birkhoffSum f φ' n := by
  obtain ⟨s, hs, hs'⟩ := eventuallyEq_iff_exists_mem.mp hφ
  let t := {x | ∀ n, f^[n] x ∈ s}
  have ht : t ∈ ae μ := by
    refine mem_ae_iff.mpr ?_
    rw [show tᶜ = ⋃ n, (f^[n])⁻¹' sᶜ by ext x; simp [t]]
    exact measure_iUnion_null_iff.mpr fun n ↦ (hf.iterate n).preimage_null hs
  filter_upwards [ht] with x hx
  exact Finset.sum_congr rfl fun x _ => hs' (hx x)

/-- If observables `φ` and `φ'` are `=ᵐ[μ]` equal then the corresponding `birkhoffAverage` are
`=ᵐ[μ]` equal. -/
theorem birkhoffAverage_ae_eq_of_ae_eq (R : Type*) [DivisionSemiring R] [Module R M]
    (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] φ') n :
    birkhoffAverage R f φ n =ᵐ[μ] birkhoffAverage R f φ' n :=
  EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

end QuasiMeasurePreserving


-- ==================== Main ====================






section BirkhoffMax

variable {α : Type*}

/-- The maximum of `birkhoffSum f φ i` for `i` ranging from `1` to `n + 1`. -/
def birkhoffMax (f : α → α) (φ : α → ℝ) : ℕ →o (α → ℝ) :=
  partialSups (birkhoffSum f φ ∘ .succ)

lemma birkhoffMax_succ : birkhoffMax f φ n.succ x = φ x + 0 ⊔ birkhoffMax f φ n (f x) := by
  have : birkhoffSum f φ ∘ .succ = fun k ↦ φ + birkhoffSum f φ k ∘ f := by
    funext k x; dsimp
    rw [add_comm k 1, birkhoffSum_add f φ 1, birkhoffSum_one];
    rfl
  nth_rw 1 [birkhoffMax, this, partialSups_const_add]
  simp only [Pi.add_apply, add_right_inj]
  rw [Nat.succ_eq_add_one, partialSups_add_one']
  simp only [birkhoffSum_zero', Pi.zero_comp, Pi.sup_apply, Pi.zero_apply]
  simp_rw [Pi.partialSups_apply, Function.comp_apply, ← Pi.partialSups_apply]; rfl

abbrev birkhoffMaxDiff (f : α → α) (φ : α → ℝ) (n : ℕ) (x : α) :=
  birkhoffMax f φ (n + 1) x - birkhoffMax f φ n (f x)

theorem birkhoffMaxDiff_aux : birkhoffMaxDiff f φ n x = φ x - (0 ⊓ birkhoffMax f φ n (f x)) := by
  rw [sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, add_assoc, add_right_inj, max_add_min, zero_add]

lemma birkhoffMaxDiff_antitone : Antitone (birkhoffMaxDiff f φ) := by
  intro m n h x
  rw [birkhoffMaxDiff_aux, birkhoffMaxDiff_aux]
  apply sub_le_sub_left
  simp only [neg_le_neg_iff, le_inf_iff, inf_le_left, inf_le_iff, true_and]
  right
  exact (birkhoffMax f φ).monotone' h _

@[measurability]
lemma birkhoffSum_measurable [MeasurableSpace α]
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSum f φ n) := by
  apply Finset.measurable_sum
  measurability

@[measurability]
lemma birkhoffMax_measurable [MeasurableSpace α]
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffMax f φ n) := by
  induction n with
  | zero => simpa [birkhoffMax] using hφ
  | succ k ih =>
      unfold birkhoffMax at ih ⊢
      rw [partialSups_add_one]
      exact ih.sup (by
        simpa [Function.comp] using birkhoffSum_measurable (n := k + 2) hf hφ)

end BirkhoffMax

noncomputable section BirkhoffThm

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} [msα : MeasurableSpace α] (μ : Measure α := by volume_tac)

/-- The supremum of `birkhoffSum f φ (n + 1) x` over `n : ℕ`. -/
def birkhoffSup (f : α → α) (φ : α → ℝ) (x : α) : EReal := iSup fun n ↦ ↑(birkhoffSum f φ (n + 1) x)

lemma birkhoffSup_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSup f φ) := Measurable.iSup
  (fun _ ↦ Measurable.coe_real_ereal (birkhoffSum_measurable hf hφ))

/-- The set of points `x` for which `birkhoffSup f φ x = ⊤`. -/
def divergentSet (f : α → α) (φ : α → ℝ) : Set α := (birkhoffSup f φ)⁻¹' {⊤}

lemma divergentSet_invariant : f x ∈ divergentSet f φ ↔ x ∈ divergentSet f φ := by
  constructor
  all_goals
    intro hx
    simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at *
    intro M hM
    cases' M using EReal.rec with a
    · use 0; apply EReal.bot_lt_coe
    case top => contradiction
  case mp =>
    cases' hx ↑(- φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
    rw [neg_add_lt_iff_lt_add, ← birkhoffSum_succ'] at hN
    use N + 1
  case mpr =>
    cases' hx ↑(φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
    conv =>
      congr
      intro i
      rw [← add_lt_add_iff_left (φ x), ← birkhoffSum_succ']
    cases' N with N
    · /- ugly case! :( -/
      cases' hx ↑(birkhoffSum f φ 1 x) (EReal.coe_lt_top _) with N hNN
      cases' N with N
      · exfalso; exact (lt_self_iff_false _).mp hNN
      · use N
        norm_cast at hNN
        exact lt_trans hN hNN
    · use N

lemma divergentSet_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet (divergentSet f φ) :=
      measurableSet_preimage (birkhoffSup_measurable hf hφ) (measurableSet_singleton _)

lemma divergentSet_mem_invalg
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet[invariants f] (divergentSet f φ) :=
  /- should be `Set.ext divergentSet_invariant` but it is VERY slow -/
  ⟨divergentSet_measurable hf hφ, funext (fun _ ↦ propext divergentSet_invariant)⟩

lemma birkhoffMax_tendsto_top_mem_divergentSet (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMax f φ · x) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at hx
  cases' hx b (EReal.coe_lt_top _) with N hN
  norm_cast at hN
  use N
  exact fun n hn ↦ le_trans (le_of_lt hN) (le_partialSups_of_le (birkhoffSum f φ ∘ .succ) hn x )

lemma birkhoffMaxDiff_tendsto_of_mem_divergentSet (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMaxDiff f φ · x) atTop (𝓝 (φ x)) := by
  have hx' : f x ∈ divergentSet f φ := divergentSet_invariant.mpr hx
  simp_rw [birkhoffMaxDiff_aux]
  nth_rw 2 [← sub_zero (φ x)]
  apply Tendsto.sub tendsto_const_nhds
  cases' tendsto_atTop_atTop.mp (birkhoffMax_tendsto_top_mem_divergentSet hx') 0 with N hN
  exact tendsto_atTop_of_eventually_const (i₀ := N) fun i hi ↦ inf_of_le_left (hN i hi)

abbrev nonneg : Filter ℝ := ⨅ ε > 0, 𝓟 (Set.Iio ε)

lemma birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
    (hx : x ∉ divergentSet f φ) :
    Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  /- it suffices to show there are upper bounds ≤ ε for all ε > 0 -/
  simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop, ge_iff_le]
  intro ε hε

  /- from `hx` hypothesis, the birkhoff sums are bounded above -/
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top,
    not_forall, not_exists, not_lt, exists_prop] at hx
  rcases hx with ⟨M', M_lt_top, M_is_bound⟩

  /- the upper bound is, in fact, a real number -/
  cases' M' using EReal.rec with M
  case bot => exfalso; exact (EReal.bot_lt_coe _).not_ge (M_is_bound 0)
  case top => contradiction
  norm_cast at M_is_bound

  /- use archimedian property of reals -/
  cases' Archimedean.arch M hε with N hN
  have upperBound (n : ℕ) (hn : N ≤ n) : birkhoffAverage ℝ f φ (n + 1) x < ε
  · have : M < (n + 1) • ε
    · exact hN.trans_lt $ smul_lt_smul_of_pos_right (Nat.lt_succ_of_le hn) hε
    · rw [nsmul_eq_mul] at this
      exact (inv_smul_lt_iff_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ n))).mpr
        ((M_is_bound n).trans_lt this)

  /- conclusion -/
  use N + 1
  intro n hn
  specialize upperBound n.pred (Nat.le_pred_of_lt hn)
  rwa [← Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn)]

/- From now on, assume f is measure-preserving and φ is integrable. -/
variable {f : α → α} (hf : MeasurePreserving f μ μ)
         {φ : α → ℝ} (hφ : Integrable φ μ) (hφ' : Measurable φ) /- seems necessary? -/

lemma iterates_integrable {i : ℕ} (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) :
    Integrable (φ ∘ f^[i]) μ := by
  apply (integrable_map_measure _ _).mp
  · rwa [(hf.iterate i).map_eq]
  · rw [(hf.iterate i).map_eq]
    exact hφ.aestronglyMeasurable
  exact (hf.iterate i).measurable.aemeasurable

lemma birkhoffSum_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) :
    Integrable (birkhoffSum f φ n) μ :=
  integrable_finset_sum _ fun _ _ ↦ iterates_integrable μ hf hφ

lemma birkhoffMax_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) : Integrable (birkhoffMax f φ n) μ := by
  unfold birkhoffMax
  induction' n with n hn
  · simpa
  · simpa using Integrable.sup hn (birkhoffSum_integrable μ hf hφ)

lemma birkhoffMaxDiff_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) :
    Integrable (birkhoffMaxDiff f φ n) μ := by
  apply Integrable.sub (birkhoffMax_integrable μ hf hφ)
  apply (integrable_map_measure _ hf.measurable.aemeasurable).mp <;> rw [hf.map_eq]
  · exact birkhoffMax_integrable μ hf hφ
  · exact (birkhoffMax_integrable μ hf hφ).aestronglyMeasurable

lemma int_birkhoffMaxDiff_in_divergentSet_tendsto (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    Tendsto (fun n ↦ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ) atTop
            (𝓝 $ ∫ x in divergentSet f φ, φ x ∂ μ) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (abs φ ⊔ abs (birkhoffMaxDiff f φ 0))
  · exact fun _ ↦ (birkhoffMaxDiff_integrable μ hf hφ).aestronglyMeasurable.restrict
  · apply Integrable.sup <;> apply Integrable.abs
    · exact hφ.restrict
    · exact (birkhoffMaxDiff_integrable μ hf hφ).restrict
  · intro n
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (by simp [birkhoffMaxDiff_aux])
      (birkhoffMaxDiff_antitone (Nat.zero_le n) _)
  · exact (ae_restrict_iff' (divergentSet_measurable hf.measurable hφ')).mpr
      (ae_of_all _ fun _ hx ↦ birkhoffMaxDiff_tendsto_of_mem_divergentSet hx)

lemma int_birkhoffMaxDiff_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    0 ≤ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ := by
  unfold birkhoffMaxDiff
  have : (μ.restrict (divergentSet f φ)).map f = μ.restrict (divergentSet f φ)
  · nth_rw 1 [
      ← (divergentSet_mem_invalg hf.measurable hφ').2,
      ← μ.restrict_map hf.measurable (divergentSet_measurable hf.measurable hφ'),
      hf.map_eq
    ]
  have mi {n : ℕ} := birkhoffMax_integrable μ hf hφ (n := n)
  have mm {n : ℕ} := birkhoffMax_measurable hf.measurable hφ' (n := n)
  rw [integral_sub, sub_nonneg]
  · rw [← integral_map (hf.aemeasurable.restrict) mm.aestronglyMeasurable, this]
    exact integral_mono mi.restrict mi.restrict ((birkhoffMax f φ).monotone (Nat.le_succ _))
  · exact mi.restrict
  · apply (integrable_map_measure mm.aestronglyMeasurable hf.aemeasurable.restrict).mp
    rw [this]
    exact mi.restrict

lemma int_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) : 0 ≤ ∫ x in divergentSet f φ, φ x ∂μ :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (int_birkhoffMaxDiff_in_divergentSet_tendsto μ hf hφ hφ')
    (fun _ ↦ int_birkhoffMaxDiff_in_divergentSet_nonneg μ hf hφ hφ')

/- these seem to be missing? -/
lemma nullMeasurableSpace_le {μ : Measure α} :
    msα ≤ NullMeasurableSpace.instMeasurableSpace (α := α) (μ := μ) :=
  fun s hs ↦ ⟨s, hs, ae_eq_refl s⟩

variable [hμ : IsProbabilityMeasure μ]

lemma divergentSet_zero_meas_of_condexp_neg
    (h : ∀ᵐ x ∂μ, (μ[φ|invariants f]) x < 0) (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    μ (divergentSet f φ) = 0 := by
  have pos : ∀ᵐ x ∂μ.restrict (divergentSet f φ), 0 < -(μ[φ|invariants f]) x
  · exact ae_restrict_of_ae (h.mono fun _ hx ↦ neg_pos.mpr hx)
  have ds_meas := divergentSet_mem_invalg hf.measurable hφ'
  by_contra hm; simp_rw [← pos_iff_ne_zero] at hm
  have : ∫ x in divergentSet f φ, φ x ∂μ < 0
  · rw [← setIntegral_condExp (invariants_le f) hφ ds_meas,
      ← Left.neg_pos_iff, ← integral_neg, integral_pos_iff_support_of_nonneg_ae]
    · unfold Function.support
      rw [(ae_iff_measure_eq _).mp]
      · rwa [Measure.restrict_apply_univ _]
      · conv in _ ≠ _ => rw [ne_comm]
        exact Eventually.ne_of_lt pos
      · apply measurableSet_support _
        apply (stronglyMeasurable_condExp).measurable.neg.le _
        exact (le_trans (invariants_le f) nullMeasurableSpace_le)
    · exact ae_le_of_ae_lt pos
    · exact integrable_condExp.restrict.neg
  exact this.not_ge (int_in_divergentSet_nonneg μ hf hφ hφ')

lemma limsup_birkhoffAverage_nonpos_of_condexp_neg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) (h : ∀ᵐ x ∂μ, (μ[φ|invariants f]) x < 0) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  apply Eventually.mono _ fun _ ↦ birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
  apply ae_iff.mpr
  simp only [not_not, Set.setOf_mem_eq]
  exact divergentSet_zero_meas_of_condexp_neg μ h hf hφ hφ'

def invCondexp (μ : Measure α := by volume_tac) [IsProbabilityMeasure μ]
    (f : α → α) (φ : α → ℝ) : α → ℝ := μ[φ|invariants f]

theorem birkhoffErgodicTheorem_aux {ε : ℝ} (hε : 0 < ε) (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x - (invCondexp μ f φ x + ε)) atTop nonneg := by
  let ψ := φ - (invCondexp μ f φ + fun _ ↦ ε)
  have ψ_integrable : Integrable ψ μ := hφ.sub (integrable_condExp.add (integrable_const _))
  have ψ_measurable : Measurable ψ := by
    suffices Measurable (invCondexp μ f φ) by measurability
    exact stronglyMeasurable_condExp.measurable.le (invariants_le f)

  have condexpψ_const : invCondexp μ f ψ =ᵐ[μ] - fun _ ↦ ε := calc
    μ[ψ|invariants f]
    _ =ᵐ[μ] _ - _ := condExp_sub hφ (integrable_condExp.add (integrable_const _)) _
    _ =ᵐ[μ] _ - (_ + _) := (condExp_add integrable_condExp (integrable_const _) _).neg.add_left
    _ =ᵐ[μ] _ - (_ + _) := (condExp_condExp_of_le (le_of_eq rfl)
                            (invariants_le f)).add_right.neg.add_left
    _ = - μ[fun _ ↦ ε|invariants f] := by simp
    _ = - fun _ ↦ ε := by rw [condExp_const (invariants_le f)]

  have limsup_nonpos : ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f ψ · x) atTop nonneg
  · suffices ∀ᵐ x ∂μ, invCondexp μ f ψ x < 0 from
      limsup_birkhoffAverage_nonpos_of_condexp_neg μ hf ψ_integrable ψ_measurable this
    exact condexpψ_const.mono fun x hx ↦ by simp [hx, hε]

  refine limsup_nonpos.mono fun x hx => ?_

  suffices ∀ (n : ℕ), 0 < n → birkhoffAverage ℝ f ψ n x = birkhoffAverage ℝ f φ n x - (invCondexp μ f φ x + ε) by
    simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop,
      ge_iff_le] at hx ⊢
    intro r hr
    cases' hx r hr with n hn
    use n + 1
    intro k hk
    rw [← this k (Nat.zero_lt_of_lt hk)]
    exact hn k (Nat.le_of_succ_le hk)

  have condexpφ_invariant : invCondexp μ f φ ∘ f = invCondexp μ f φ :=
    MeasurableSpace.comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable

  intro n hn
  simp [ψ, birkhoffAverage_sub, birkhoffAverage_add, birkhoffAverage_of_invariant
    (show _ = fun _ ↦ ε from rfl) hn, birkhoffAverage_of_invariant condexpφ_invariant hn]

/-- This is the main result but assuming `Measurable φ`. -/
theorem birkhoffErgodicTheorem (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop (𝓝 (invCondexp μ f φ x)) := by
  have : ∀ᵐ x ∂μ, ∀ (k : {k : ℕ // k > 0}),
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f φ n x - (invCondexp μ f φ x)| < (k : ℝ)⁻¹ := by
    apply ae_all_iff.mpr
    rintro ⟨k, hk⟩
    let δ := (k : ℝ)⁻¹/2
    have hδ : δ > 0 := by simpa [δ]
    have p₁ := birkhoffErgodicTheorem_aux μ hδ hf hφ hφ'
    have p₂ := birkhoffErgodicTheorem_aux μ hδ hf hφ.neg hφ'.neg
    have : invCondexp μ f (-φ) =ᵐ[μ] -invCondexp μ f φ := condExp_neg _ _
    refine ((p₁.and p₂).and this).mono fun x ⟨⟨hx₁, hx₂⟩, hx₃⟩ => ?_
    simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop,
      ge_iff_le] at hx₁ hx₂ ⊢
    cases' hx₁ δ hδ with n₁ hn₁
    cases' hx₂ δ hδ with n₂ hn₂
    simp_rw [δ] at hn₁ hn₂ ⊢
    use (max n₁ n₂)
    intro m hm
    apply abs_lt.mpr
    constructor
    · specialize hn₂ m (le_of_max_le_right hm)
      rw [hx₃, birkhoffAverage_neg] at hn₂
      norm_num at hn₂
      linarith
    · specialize hn₁ m (le_of_max_le_left hm)
      linarith

  refine this.mono fun x hx => Metric.tendsto_atTop.mpr fun ε hε => ?_
  cases' Archimedean.arch 1 hε with k hk
  have hk' : 1 < (k + 1) • ε
  · exact hk.trans_lt $ smul_lt_smul_of_pos_right (lt_add_one k) hε
  simp only [eventually_atTop, ge_iff_le, Subtype.forall, gt_iff_lt] at hx
  cases' hx k.succ (Nat.zero_lt_succ k) with N hN
  use N
  intro n hn
  apply (hN n hn).trans
  rw [inv_lt_iff_one_lt_mul₀ (Nat.cast_pos.mpr k.succ_pos)]
  norm_num at hk' ⊢
  linarith

/-- Here we drop the assumption that the observable is `Measurable`. -/
theorem birkhoffErgodicTheorem' {Φ : α → ℝ} (hf : MeasurePreserving f μ μ) (hΦ : Integrable Φ μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f Φ · x) atTop (𝓝 (invCondexp μ f Φ x)) := by
  -- Take `φ` as the measurable approximation to the ae measurable `Φ`.
  let φ := hΦ.left.mk
  have hφ' : Measurable φ := hΦ.left.measurable_mk
  have hΦ' : Φ =ᵐ[μ] φ := hΦ.left.ae_eq_mk
  have hφ : Integrable φ μ := (integrable_congr hΦ.left.ae_eq_mk).mp hΦ
  -- Obtain a full measure set such that the three relevant results hold.
  obtain ⟨s, hs, hs'⟩ : ∃ s ∈ ae μ, Set.EqOn (invCondexp μ f Φ) (invCondexp μ f φ) s :=
    eventuallyEq_iff_exists_mem.mp <| condExp_congr_ae hΦ'
  obtain ⟨t, ht, ht'⟩ := eventually_iff_exists_mem.mp <| birkhoffErgodicTheorem μ hf hφ hφ'
  have := ae_all_iff.mpr <| birkhoffAverage_ae_eq_of_ae_eq ℝ hf.quasiMeasurePreserving hΦ'
  obtain ⟨u, hu, hu'⟩ := eventually_iff_exists_mem.mp this
  -- Apply the three results on the chosen set.
  refine eventually_iff_exists_mem.mpr ⟨s ∩ t ∩ u, inter_mem (inter_mem hs ht) hu, fun y hy ↦ ?_⟩
  simp [hs' hy.1.1, ht' y hy.1.2, hu' y hy.2]

#print axioms birkhoffErgodicTheorem
#print axioms birkhoffErgodicTheorem'

/-! ## The measurable-coboundary mean-zero lemma

The paper's Lemma 2: if `φ` is a coboundary `u ∘ f - u` with `u` merely finite and
measurable (NOT assumed integrable), then `∫ φ = 0`.

Route: the Birkhoff sums of a coboundary telescope to `u ∘ f^[n] - u`, so the averages tend
to `0` **in measure** (because `u ∘ f^[n]` and `u` are equidistributed).  Birkhoff gives a.e.
convergence to `μ[φ|invariants f]`; uniqueness of limits in measure forces that to be `0`,
and `integral_condExp` turns it into `∫ φ = 0`.

Note this needs only `MeasurePreserving`, not ergodicity — the conditional-expectation route
avoids identifying the limit with the mean. -/

section Coboundary

open MeasureTheory Filter Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- The Birkhoff sums of a coboundary telescope. -/
lemma birkhoffSum_coboundary {f : α → α} {u : α → ℝ} (n : ℕ) (x : α) :
    birkhoffSum f (fun y => u (f y) - u y) n x = u (f^[n] x) - u x := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [birkhoffSum_succ, ih, Function.iterate_succ_apply']
      ring

/-- `μ {|u| ≥ t} → 0` as `t → ∞`, for a real-valued (hence everywhere finite) `u`. -/
lemma tendsto_measure_abs_ge_atTop {u : α → ℝ} (hu : Measurable u) :
    Tendsto (fun t : ℝ => μ {x | t ≤ |u x|}) atTop (𝓝 0) := by
  have hmeas : ∀ t : ℝ, NullMeasurableSet {x | t ≤ |u x|} μ := fun t =>
    (measurableSet_le measurable_const hu.abs).nullMeasurableSet
  have hanti : Antitone (fun t : ℝ => {x | t ≤ |u x|}) := fun s t hst x hx => le_trans hst hx
  have hempty : (⋂ t : ℝ, {x | t ≤ |u x|}) = (∅ : Set α) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
    exact ⟨|u x| + 1, by linarith⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at h
  exact h

/-- The normalised coboundary tends to `0` in measure. -/
lemma tendstoInMeasure_coboundary {f : α → α} (hf : MeasurePreserving f μ μ)
    {u : α → ℝ} (hu : Measurable u) :
    TendstoInMeasure μ (fun n : ℕ => fun x => (n : ℝ)⁻¹ * (u (f^[n] x) - u x)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [Pi.zero_apply]
  -- the shifted copy has the same distribution as `u`
  have hshift : ∀ (n : ℕ) (t : ℝ), μ {x | t ≤ |u (f^[n] x)|} = μ {x | t ≤ |u x|} := by
    intro n t
    have hs : NullMeasurableSet {x | t ≤ |u x|} μ :=
      (measurableSet_le measurable_const hu.abs).nullMeasurableSet
    exact (hf.iterate n).measure_preimage hs
  -- pointwise inclusion into two tail events
  have hsub : ∀ n : ℕ,
      {x | ε ≤ ‖(n : ℝ)⁻¹ * (u (f^[n] x) - u x) - 0‖}
        ⊆ {x | (n : ℝ) * ε / 2 ≤ |u (f^[n] x)|} ∪ {x | (n : ℝ) * ε / 2 ≤ |u x|} := by
    intro n x hx
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs, abs_mul, abs_inv,
      Nat.abs_cast] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hn : (0 : ℝ) < (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp at hx; linarith
      · exact_mod_cast hpos
    have habs : |u (f^[n] x) - u x| < (n : ℝ) * ε := by
      calc |u (f^[n] x) - u x| ≤ |u (f^[n] x)| + |u x| := abs_sub _ _
        _ < (n : ℝ) * ε / 2 + (n : ℝ) * ε / 2 := by linarith
        _ = (n : ℝ) * ε := by ring
    have : ((n : ℝ))⁻¹ * |u (f^[n] x) - u x| < ε := by
      rw [inv_mul_lt_iff₀ hn]; linarith
    linarith
  -- squeeze
  have htail : Tendsto (fun n : ℕ => μ {x | (n : ℝ) * ε / 2 ≤ |u x|}) atTop (𝓝 0) :=
    (tendsto_measure_abs_ge_atTop hu).comp
      (Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨⌈2 * b / ε⌉₊ + 1, fun n hn => by
          have h1 : (⌈2 * b / ε⌉₊ : ℝ) ≤ (n : ℝ) := by
            have hnn : (⌈2 * b / ε⌉₊ : ℕ) ≤ n := by omega
            exact_mod_cast hnn
          have h2 : 2 * b / ε ≤ (⌈2 * b / ε⌉₊ : ℝ) := Nat.le_ceil _
          have h3 : 2 * b / ε ≤ (n : ℝ) := le_trans h2 h1
          rw [div_le_iff₀ hε] at h3
          linarith⟩)
  have hbound : Tendsto (fun n : ℕ => 2 * μ {x | (n : ℝ) * ε / 2 ≤ |u x|}) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul htail (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le') (fun n => ?_)
  refine le_trans (measure_mono (hsub n)) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [hshift n, two_mul]


theorem integral_eq_zero_of_coboundary {f : α → α} (hf : MeasurePreserving f μ μ)
    {φ u : α → ℝ} (hφ : Integrable φ μ) (hu : Measurable u)
    (hcob : φ =ᵐ[μ] fun x => u (f x) - u x) :
    ∫ x, φ x ∂μ = 0 := by
  classical
  have hbirk := birkhoffErgodicTheorem' μ hf hφ
  -- the Birkhoff averages are a.e. the normalised coboundary, simultaneously in `n`
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffAverage ℝ f φ n x = (n : ℝ)⁻¹ * (u (f^[n] x) - u x) := by
    refine ae_all_iff.mpr fun n => ?_
    filter_upwards [birkhoffAverage_ae_eq_of_ae_eq ℝ hf.quasiMeasurePreserving hcob n] with x hx
    rw [hx, birkhoffAverage, birkhoffSum_coboundary, smul_eq_mul]
  -- a subsequence of the normalised coboundary converges a.e. to `0`
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_coboundary hf hu).exists_seq_tendsto_ae
  have hzero : (μ[φ|invariants f]) =ᵐ[μ] 0 := by
    filter_upwards [hbirk, hall, hae] with x hx1 hx2 hx3
    have hsub : Tendsto (fun i => birkhoffAverage ℝ f φ (ns i) x) atTop
        (𝓝 (invCondexp μ f φ x)) := hx1.comp hns.tendsto_atTop
    have hzer : Tendsto (fun i => birkhoffAverage ℝ f φ (ns i) x) atTop (𝓝 0) := by
      simpa [hx2] using hx3
    simpa [invCondexp] using tendsto_nhds_unique hsub hzer
  calc ∫ x, φ x ∂μ = ∫ x, (μ[φ|invariants f]) x ∂μ := (integral_condExp (invariants_le f)).symm
    _ = ∫ _x, (0 : ℝ) ∂μ := integral_congr_ae hzero
    _ = 0 := integral_zero _ _

/-! ### From the modulus cocycle to the mean condition

On a LIVE fibre the modulus cocycle `|P| · |G| = d · |G ∘ R|` can be logged, turning
`log|P| − log d` into the coboundary `log|G| ∘ R − log|G|`.  The mean-zero lemma then gives
`∫ log|P| = log d` — which is exactly the `hmean` hypothesis of
`HRTResonant.live_set_subset_four`. -/

/-- **The mean condition.**  On a live fibre, `∫ log|P| = log d`. -/
theorem integral_log_eq_of_modulus_cocycle
    {R : α → α} (hR : MeasurePreserving R μ μ)
    {G P : α → ℝ} {d : ℝ} (hd : 0 < d)
    (hGmeas : Measurable G) (hPmeas : Measurable P)
    (hGne : ∀ᵐ x ∂μ, G x ≠ 0) (hPne : ∀ᵐ x ∂μ, P x ≠ 0)
    (hcoc : ∀ᵐ x ∂μ, |P x| * |G x| = d * |G (R x)|)
    (hint : Integrable (fun x => Real.log |P x|) μ) :
    ∫ x, Real.log |P x| ∂μ = Real.log d := by
  set u : α → ℝ := fun x => Real.log |G x| with hu
  have humeas : Measurable u := (hGmeas.abs.log)
  have hcob : (fun x => Real.log |P x| - Real.log d) =ᵐ[μ] fun x => u (R x) - u x := by
    filter_upwards [hcoc, hGne, hPne] with x hx hGx hPx
    have hGRx : |G (R x)| ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hx
      exact (mul_ne_zero (abs_ne_zero.mpr hPx) (abs_ne_zero.mpr hGx)) hx
    have hlog := congrArg Real.log hx
    rw [Real.log_mul (abs_ne_zero.mpr hPx) (abs_ne_zero.mpr hGx),
      Real.log_mul (ne_of_gt hd) hGRx] at hlog
    simp only [hu]
    linarith [hlog]
  have hint' : Integrable (fun x => Real.log |P x| - Real.log d) μ :=
    hint.sub (integrable_const _)
  have hzero := integral_eq_zero_of_coboundary hR hint' humeas hcob
  rw [integral_sub hint (integrable_const _), integral_const] at hzero
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at hzero
  linarith [hzero]

/-- **Coboundary Birkhoff sums are TIGHT.**

If `φ = u ∘ f - u` for a measurable `u`, its Birkhoff sums telescope to `u (f^[N] x) - u x`, and
since `f` preserves the measure, `u ∘ f^[N]` has the same distribution as `u`.  So the sums are
uniformly bounded in probability: ONE bound `M` works for EVERY `N`.

This is the obstruction that closes the HRT degenerate stratum.  There the cocycle forces
`log |fibre|` to be such a `u`, so the Birkhoff sums of `log |2 sin(πx)|` over rotation by `√2`
would have to be tight — and for quadratic irrationals they are not: they grow like `√N`
(Sudler-product asymptotics / the temporal central limit theorem).  Contradiction, with no von
Neumann algebras anywhere. -/
theorem tight_birkhoffSum_of_coboundary {f : α → α} (hf : MeasurePreserving f μ μ)
    {u : α → ℝ} (hu : Measurable u) {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ M : ℝ, ∀ N : ℕ,
      μ {x | 2 * M < |birkhoffSum f (fun y => u (f y) - u y) N x|} ≤ ε := by
  have hhalfpos : (0 : ENNReal) < ε / 2 := by
    rw [pos_iff_ne_zero]
    simp [ENNReal.div_eq_zero_iff, hε]
  have htend := tendsto_measure_abs_ge_atTop (μ := μ) hu
  have hev : ∀ᶠ t : ℝ in Filter.atTop, μ {x | t ≤ |u x|} < ε / 2 :=
    htend.eventually (gt_mem_nhds hhalfpos)
  obtain ⟨M, hM⟩ := hev.exists
  have hmeas : MeasurableSet {y : α | M ≤ |u y|} := measurableSet_le measurable_const hu.abs
  refine ⟨M, fun N => ?_⟩
  have hsubset : {x | 2 * M < |birkhoffSum f (fun y => u (f y) - u y) N x|}
      ⊆ (f^[N] ⁻¹' {y : α | M ≤ |u y|}) ∪ {x : α | M ≤ |u x|} := by
    intro x hx
    simp only [Set.mem_setOf_eq, birkhoffSum_coboundary] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have : |u (f^[N] x) - u x| ≤ |u (f^[N] x)| + |u x| := abs_sub _ _
    linarith
  calc μ {x | 2 * M < |birkhoffSum f (fun y => u (f y) - u y) N x|}
      ≤ μ ((f^[N] ⁻¹' {y : α | M ≤ |u y|}) ∪ {x : α | M ≤ |u x|}) := measure_mono hsubset
    _ ≤ μ (f^[N] ⁻¹' {y : α | M ≤ |u y|}) + μ {x : α | M ≤ |u x|} := measure_union_le _ _
    _ = μ {y : α | M ≤ |u y|} + μ {x : α | M ≤ |u x|} := by
        rw [(hf.iterate N).measure_preimage hmeas.nullMeasurableSet]
    _ ≤ ε / 2 + ε / 2 := add_le_add hM.le hM.le
    _ = ε := ENNReal.add_halves ε

/-- **Non-tight Birkhoff sums rule out a coboundary.**

The contrapositive of `tight_birkhoffSum_of_coboundary`, and the form the HRT degenerate stratum
consumes: if the Birkhoff sums of `φ` escape every uniform bound in probability, then `φ` is not
`u ∘ f - u` for ANY measurable `u`. -/
theorem not_coboundary_of_not_tight {f : α → α} (hf : MeasurePreserving f μ μ)
    {φ : α → ℝ} {ε : ENNReal} (hε : ε ≠ 0)
    (hnt : ∀ M : ℝ, ∃ N : ℕ, ε < μ {x | 2 * M < |birkhoffSum f φ N x|})
    (u : α → ℝ) (hu : Measurable u) (hcob : ∀ y, φ y = u (f y) - u y) : False := by
  obtain ⟨M, hMbound⟩ := tight_birkhoffSum_of_coboundary hf hu hε
  obtain ⟨N, hN⟩ := hnt M
  have hfun : φ = fun y => u (f y) - u y := funext hcob
  rw [hfun] at hN
  exact absurd (hMbound N) (not_le.mpr hN)

/-- **A multiplicative cocycle exhibits `log P - log d` as a COBOUNDARY.**

From `P(x)·G(x) = d·G(Rx)` with everything positive, taking logs gives
`log P x - log d = log G (R x) - log G x`.  So `u = log ∘ G` is exactly the transfer function whose
existence `not_coboundary_of_not_tight` forbids. -/
theorem coboundary_of_modulus_cocycle {R : α → α} {G P : α → ℝ} {d : ℝ} (hd : 0 < d)
    (hGpos : ∀ x, 0 < G x) (hPpos : ∀ x, 0 < P x)
    (hcoc : ∀ x, P x * G x = d * G (R x)) :
    ∀ x, Real.log (P x) - Real.log d = Real.log (G (R x)) - Real.log (G x) := by
  intro x
  have h := congrArg Real.log (hcoc x)
  rw [Real.log_mul (ne_of_gt (hPpos x)) (ne_of_gt (hGpos x)),
    Real.log_mul (ne_of_gt hd) (ne_of_gt (hGpos (R x)))] at h
  linarith

/-- **A positive multiplicative cocycle is IMPOSSIBLE when the Birkhoff sums are not tight.**

This REDUCES the HRT degenerate stratum to a Diophantine question.  On the stratum the fibre
relation is exactly such a cocycle, with `P = |symbol|` and `d = ‖D‖`, and the transfer function
would have to be `log |fibre|`.  So the stratum closes as soon as the Birkhoff sums of
`log|2 sin(πx)|` over rotation by `√2` are shown NON-TIGHT.

**That input is NOT established, and this file does not assume it.**  It is the hypothesis `hnt`
below, deliberately left as a hypothesis.  Two cautions, recorded so the gap is not mistaken for a
formality:

* For `β = [0; b, b, …]` with `b ≤ 5` — and `√2 - 1 = [0; 2,2,…]` — the Sudler product satisfies
  `liminf P_N(β) > 0` and `limsup P_N(β)/N < ∞`, so `log P_N` is BOUNDED BELOW along the whole
  sequence.  That is evidence against unbounded growth, not for it.
* The `√N`-concentration and temporal-CLT results in the literature concern the value distribution
  as `N` ranges over long intervals, which is a different statement from non-tightness in `x`.

What IS proved here is the implication: a positive multiplicative cocycle whose Birkhoff sums are
non-tight cannot exist.  That is unconditional and useful regardless of how the Diophantine question
resolves — but it is not by itself a proof of the stratum. -/
theorem no_positive_cocycle_of_not_tight {R : α → α} (hR : MeasurePreserving R μ μ)
    {G P : α → ℝ} {d : ℝ} (hd : 0 < d)
    (hGpos : ∀ x, 0 < G x) (hPpos : ∀ x, 0 < P x) (hGmeas : Measurable G)
    {ε : ENNReal} (hε : ε ≠ 0)
    (hnt : ∀ M : ℝ, ∃ N : ℕ, ε < μ {x | 2 * M <
      |birkhoffSum R (fun y => Real.log (P y) - Real.log d) N x|})
    (hcoc : ∀ x, P x * G x = d * G (R x)) : False :=
  not_coboundary_of_not_tight hR hε hnt (fun x => Real.log (G x))
    (Real.measurable_log.comp hGmeas)
    (coboundary_of_modulus_cocycle hd hGpos hPpos hcoc)

end Coboundary

#print axioms birkhoffSum_coboundary
#print axioms tendsto_measure_abs_ge_atTop
#print axioms tendstoInMeasure_coboundary
#print axioms integral_eq_zero_of_coboundary
#print axioms integral_log_eq_of_modulus_cocycle
#print axioms tight_birkhoffSum_of_coboundary
#print axioms not_coboundary_of_not_tight
#print axioms coboundary_of_modulus_cocycle
#print axioms no_positive_cocycle_of_not_tight
