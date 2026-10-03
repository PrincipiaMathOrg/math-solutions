/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt.Unconditional

set_option autoImplicit false

/-!
# EP1054: the §6–§7 headlines from the representability *tail* alone

The exact classification `𝓡 = ℕ ∖ {2, 5}` (`Eq_ExactRepresentability`) rests on Helfgott, Dusart
and the three finite verifier checks (`Comp_Verifier_small`, `Comp_Verifier_window1`,
`Comp_Verifier_largeSeed`). Four headlines consume it, and only as a *normalisation*:

* `Prop_TightnessEquivalence` — through `Link_Coverage_Disp_TailLeCompl` (`Intro_RcntFormula`,
  `R(X) = ⌊X⌋ − 2`) and `Link_Coverage_Disp_ComplLeTail` (`Eq_ExactRepresentability`, used only
  to say that the unrepresented integers are negligible);
* `Thm_DaddUniversalSingularity` — the above, plus `Link_Step_DaddLimitDomination` and
  `Link_Thm_DaddUniversalSingularity_Carrier` (`Intro_RcntFormula`, used only as `X/R(X) → 1`);
* `Cor_DaddHeavyTails` — the above, plus `Link_Step_DaddXoverR` (`Eq_ExactRepresentability`, used
  only for the constant `3` in `X ≤ 3 R(X)`, and that constant only enters an implied constant);
* `Prop_DaddCollisionCriterion` — `Link_Step_DaddCollisionSupport` and
  `Link_Prop_DaddCollisionCriterion` (`Intro_RcntFormula`, used only as `R(X)/X → 1`).

Every one of those uses survives the replacement of the exact classification by **density one of
`𝓡`** (`RepDensityOne`: `ℕ ∖ 𝓡` has density zero), which is weaker than `R(X) ≥ ⌊X⌋ − K`
(`RcntTail`), which follows from the tail `Prop_FraitureTail` (every `n ≥ 10^27 + 10^8` is
represented), which needs only `Cite_Helfgott_weighted` (`Proofs.ep1054_Prop_FraitureTail`):
```
Cite_Helfgott_weighted → Prop_FraitureTail → EventuallyRepresented → RcntTail → RepDensityOne
```

## Contents

1. The normalisation from the tail: `eventuallyRepresented_of_fraitureTail`,
   `rcntTail_of_eventuallyRepresented`, `repDensityOne_of_rcntTail`, `repDensityOne_of_helfgott`;
   the consequences `tendsto_Rcnt_div_of_repDensityOne` (`R(X)/X → 1`),
   `tendsto_X_div_Rcnt_of_repDensityOne`, `eventually_cnt_le_mul_Rcnt`, and
   `stepDaddXoverR_weak_of_repDensityOne` (`X ≤ C·R(X)` for all `X ≥ 1`, some `C`).
2. The re-proved links, each the spine link with its `Intro_RcntFormula` /
   `Eq_ExactRepresentability` binder replaced by `RepDensityOne` (and, for the heavy-tail
   corollary, `Step_DaddXoverR` replaced by `Step_DaddXoverR_weak`). Six of the seven proofs are
   the library's (`Proofs.ThetaTight`, `Proofs.Singularity`, `Proofs.Collision7`) copied with the
   single use of the normalisation re-derived; `Disp_TailLeCompl`'s final estimate is re-done
   through `eventually_cnt_le_mul_Rcnt`, since its original arithmetic was written for `⌊X⌋ − 2`.
   Also `Link_Coverage_Rem_T_iff_Conj` (not a headline; a field of `Spine.DerivedClaims`), whose
   proof used `R(n) = n − 2` quantitatively and is restructured around `R(n) ≤ n` and density
   zero of `ℕ ∖ 𝓡`.
3. The recomposed headlines. The compositions follow `Spine.spine_<X>` link for link, except that
   the replaced links are applied, and inputs already discharged in the library
   (`input_Cite_PollackAP`, `input_Cite_LP_sieve37`, …) are supplied through the round-3 theorems
   of `Alt.Unconditional`. `<x>_of_repDensityOne` takes `RepDensityOne` as a hypothesis;
   `ep1054_<X>_tailOnly` supplies it from Helfgott.
4. What still needs the classification: `Intro_RcntFormula` and
   `Thm_FraitureRepresentability_Ge6` are each *equivalent* to `Eq_ExactRepresentability`
   (`eqExactRepresentability_iff_rcntFormula`, `eqExactRepresentability_iff_ge6`), so they cannot
   be had from anything weaker.

**Remaining hypotheses of the headline theorems here:**
* `ep1054_Prop_TightnessEquivalence_tailOnly`, `coverage_Rem_T_iff_Conj_tailOnly`:
  `Cite_Helfgott_weighted` (round 3: Helfgott, Dusart, three `Comp_*`).
* `ep1054_Thm_DaddUniversalSingularity_tailOnly`, `ep1054_Cor_DaddHeavyTails_tailOnly`,
  `ep1054_Prop_DaddCollisionCriterion_tailOnly`: `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`,
  `Cite_LP_Lemma25`, `Cite_Pollack_Thm14`, `Cite_Helfgott_weighted`, `Cite_Erdos_singular` (round
  3: the same plus Dusart and the three `Comp_*`).

Helfgott enters these headlines only through `RepDensityOne`: the `_of_repDensityOne` forms show
that any proof that `𝓡` has density one (no finite verifier, no explicit constant) would remove it.
Its odd half is already unconditional (`repDensityOne_iff_evenUnrep`: density one of `𝓡` is
exactly density zero of the even unrepresented integers).
-/

namespace Principia.Erdos1054.Alt.TailOnly

open Filter Topology MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction
open Principia.Erdos1054 Principia.Erdos1054.Limits Principia.Erdos1054.Spine
  Principia.Erdos1054.Proofs

/-! ## 1. The normalisation, from the tail -/

/-- Every sufficiently large integer is represented (`𝓡` is cofinite). -/
def EventuallyRepresented : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ R

/-- **`R(X) ≥ ⌊X⌋ − K`** for one constant `K` and every real `X` (stated without truncated
subtraction). -/
def RcntTail : Prop :=
  ∃ K : ℕ, ∀ X : ℝ, ⌊X⌋₊ ≤ Rcnt X + K

/-- **`𝓡` has density one**: the unrepresented integers have density zero. -/
def RepDensityOne : Prop :=
  DensZero Rᶜ

/-- `prop:fraiture-tail` gives `EventuallyRepresented` with `K = 10^27 + 10^8`. -/
theorem eventuallyRepresented_of_fraitureTail (h : Prop_FraitureTail) : EventuallyRepresented :=
  ⟨10 ^ 27 + 10 ^ 8, h⟩

/-- A cofinite `𝓡` misses at most `K` integers of `[1, X]`, so `R(X) ≥ ⌊X⌋ − K`. -/
theorem rcntTail_of_eventuallyRepresented (h : EventuallyRepresented) : RcntTail := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun X => ?_⟩
  have h1 := cnt_add_cnt_compl R X
  have h2 : cnt Rᶜ X ≤ K := by
    unfold cnt
    refine le_trans (Finset.card_le_card (t := Finset.range K) ?_) (Finset.card_range K).le
    intro n hn
    rw [mem_cntFinset] at hn
    rw [Finset.mem_range]
    by_contra h'
    exact hn.2 (hK n (not_lt.1 h'))
  change ⌊X⌋₊ ≤ cnt R X + K
  omega

/-- `R(X) ≥ ⌊X⌋ − K` gives density one. -/
theorem repDensityOne_of_rcntTail (h : RcntTail) : RepDensityOne := by
  obtain ⟨K, hK⟩ := h
  have hb : ∀ X : ℝ, cnt Rᶜ X ≤ K := fun X => by
    have h1 := cnt_add_cnt_compl R X
    have h2 : ⌊X⌋₊ ≤ cnt R X + K := hK X
    omega
  change HasDens Rᶜ 0
  unfold HasDens
  refine squeeze_zero (cnt_div_nonneg _) (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  exact div_le_div_of_nonneg_right (by exact_mod_cast hb n) (Nat.cast_nonneg n)

/-- **Density one of `𝓡` from Helfgott alone** (through `Proofs.ep1054_Prop_FraitureTail`). -/
theorem repDensityOne_of_helfgott (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    RepDensityOne :=
  repDensityOne_of_rcntTail (rcntTail_of_eventuallyRepresented
    (eventuallyRepresented_of_fraitureTail (ep1054_Prop_FraitureTail i_Cite_Helfgott_weighted)))

/-- **The odd half of density one is already unconditional**, so density one of `𝓡` is exactly
density zero of the *even* unrepresented integers. Odd `n ∉ 𝓡` have density zero by
`Alt.oddRepr_densZero_of_goldbach` (`n − 1 = p + q`, `p ≠ q`, gives `n = F p q`) and the
unconditional almost-all binary Goldbach theorem (`Alt.std_GoldbachDensZero_unconditional`). -/
theorem repDensityOne_iff_evenUnrep :
    RepDensityOne ↔ DensZero {n : ℕ | Even n ∧ n ∉ R} := by
  constructor
  · intro hD
    exact densZero_subset hD (fun n hn => hn.2)
  · intro hE
    have hO : DensZero {n : ℕ | Odd n ∧ n ∉ R} :=
      oddRepr_densZero_of_goldbach std_GoldbachDensZero_unconditional
    refine densZero_subset (densZero_union hO hE) ?_
    intro n hn
    rcases Nat.even_or_odd n with h | h
    · exact Or.inr ⟨h, hn⟩
    · exact Or.inl ⟨h, hn⟩

/-- The unrepresented integers up to `X` are `o(X)` along real `X`. -/
theorem tendsto_cntCompl_div (hD : RepDensityOne) :
    Tendsto (fun X : ℝ => (cnt Rᶜ X : ℝ) / X) atTop (𝓝 0) := by
  have hD' : DensZero Rᶜ := hD
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact lt_of_lt_of_le ha (div_nonneg (Nat.cast_nonneg _) hX.le)
  · obtain ⟨X₀, hX₀⟩ := hD'.exists_le_mul (half_pos ha)
    filter_upwards [eventually_ge_atTop X₀, eventually_gt_atTop (0 : ℝ)] with X hX hX0
    rw [div_lt_iff₀ hX0]
    have h1 := hX₀ X hX
    have h2 : a / 2 * X < a * X := by nlinarith
    linarith

/-- **`R(X)/X → 1`** from density one (the spine derives it from `R(X) = ⌊X⌋ − 2`). -/
theorem tendsto_Rcnt_div_of_repDensityOne (hD : RepDensityOne) :
    Tendsto (fun X : ℝ => (Rcnt X : ℝ) / X) atTop (𝓝 1) := by
  have h1 : Tendsto (fun X : ℝ => (⌊X⌋₊ : ℝ) / X - (cnt Rᶜ X : ℝ) / X) atTop (𝓝 (1 - 0)) :=
    (tendsto_nat_floor_div_atTop (R := ℝ)).sub (tendsto_cntCompl_div hD)
  rw [sub_zero] at h1
  refine h1.congr (fun X => ?_)
  have h := cnt_add_cnt_compl R X
  have h' : (cnt R X : ℝ) + (cnt Rᶜ X : ℝ) = (⌊X⌋₊ : ℝ) := by exact_mod_cast h
  have e : (Rcnt X : ℝ) = (⌊X⌋₊ : ℝ) - (cnt Rᶜ X : ℝ) := by
    change (cnt R X : ℝ) = _
    linarith
  rw [e, sub_div]

/-- `X/R(X) → 1` from density one. -/
theorem tendsto_X_div_Rcnt_of_repDensityOne (hD : RepDensityOne) :
    Tendsto (fun X : ℝ => X / (Rcnt X : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_Rcnt_div_of_repDensityOne hD).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X _
  rw [inv_div]

/-- If `upperdens S < a`, then `#(S ∩ [1, X]) ≤ a R(X)` for all large real `X` (density one of
`𝓡` lets `R(X)` replace `X`). -/
theorem eventually_cnt_le_mul_Rcnt (hD : RepDensityOne) {S : Set ℕ} {a : ℝ}
    (ha : upperDens S < a) : ∀ᶠ X : ℝ in atTop, (cnt S X : ℝ) ≤ a * Rcnt X := by
  have hD' : DensZero Rᶜ := hD
  have ha0 : 0 < a := lt_of_le_of_lt (upperDens_nonneg S) ha
  obtain ⟨b, hb1, hba⟩ := exists_between ha
  have hη : 0 < (a - b) / a := div_pos (by linarith) ha0
  have h1 := eventually_cnt_lt_mul_of_upperDens_lt hb1
  have h2 := densZero_iff_eventually_le.1 hD' _ hη
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and h2)
  filter_upwards [eventually_ge_atTop (n₀ : ℝ)] with X hX
  have hn : n₀ ≤ ⌊X⌋₊ := Nat.le_floor hX
  obtain ⟨hS, hC⟩ := hn₀ ⌊X⌋₊ hn
  rw [cnt_floor] at hS hC
  have hsum : (cnt R X : ℝ) + (cnt Rᶜ X : ℝ) = (⌊X⌋₊ : ℝ) := by
    exact_mod_cast cnt_add_cnt_compl R X
  have key : a * ((a - b) / a) = a - b := by field_simp
  have hC' : a * (cnt Rᶜ X : ℝ) ≤ (a - b) * ⌊X⌋₊ := by
    calc a * (cnt Rᶜ X : ℝ) ≤ a * ((a - b) / a * ⌊X⌋₊) :=
          mul_le_mul_of_nonneg_left hC ha0.le
      _ = (a - b) * ⌊X⌋₊ := by rw [← mul_assoc, key]
  change (cnt S X : ℝ) ≤ a * (cnt R X : ℝ)
  have e : a * (cnt R X : ℝ) = a * ⌊X⌋₊ - a * (cnt Rᶜ X : ℝ) := by
    rw [← hsum]
    ring
  rw [e]
  linarith

/-- **Weak `X/R(X)` bound**: `X ≤ C · R(X)` for every `X ≥ 1`, for some constant `C` (the paper's
line 3001 has `C = 3`, which needs the exact classification). -/
def Step_DaddXoverR_weak : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → X ≤ C * Rcnt X

/-- `Step_DaddXoverR_weak` from density one: `R(X) ≥ X/2` for `X ≥ X₀`, and `R(X) ≥ 1` below. -/
theorem stepDaddXoverR_weak_of_repDensityOne (hD : RepDensityOne) : Step_DaddXoverR_weak := by
  have h := tendsto_Rcnt_div_of_repDensityOne hD
  obtain ⟨X₀, hX₀⟩ :=
    eventually_atTop.1 (h.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))
  refine ⟨max 2 X₀, fun X hX => ?_⟩
  have hR1 : (1 : ℝ) ≤ Rcnt X := by exact_mod_cast Singularity.one_le_Rcnt hX
  have hM2 : (2 : ℝ) ≤ max 2 X₀ := le_max_left _ _
  have hMX : X₀ ≤ max 2 X₀ := le_max_right _ _
  have hM0 : (0 : ℝ) ≤ max 2 X₀ := by linarith
  rcases le_or_gt X₀ X with hXX | hXX
  · have h2 := hX₀ X hXX
    have hXpos : 0 < X := by linarith
    rw [lt_div_iff₀ hXpos] at h2
    have h3 : 2 * (Rcnt X : ℝ) ≤ max 2 X₀ * Rcnt X :=
      mul_le_mul_of_nonneg_right hM2 (by linarith)
    linarith
  · have h3 : max 2 X₀ * 1 ≤ max 2 X₀ * Rcnt X := mul_le_mul_of_nonneg_left hR1 hM0
    linarith

/-! ## 2. The re-proved links -/

section Coverage

open Finset Principia.Erdos1054.Proofs.ThetaTight

/-- **Tail ≤ complement** (`Link_Coverage_Disp_TailLeCompl`, EP1054.tex lines 2689–2700) with
`Intro_RcntFormula` replaced by `RepDensityOne`: `ν_X((E, ∞]) ≤ R(X)⁻¹ #{N ≤ X : N ∉ G_E}` and
`#{N ≤ X : N ∉ G_E} ≤ (upperdens + δ) R(X)` for large `X`. -/
theorem link_Coverage_Disp_TailLeCompl_tailOnly :
    RepDensityOne → Coverage.Disp_TailLeCompl := by
  intro hD E _hE
  have hU0 : 0 ≤ upperDens {N : ℕ | N ∉ Gcov E} := upperDens_nonneg _
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := hδ
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hU0 δ.coe_nonneg]
  refine limsup_le_of_le (h := ?_)
  filter_upwards [eventually_cnt_le_mul_Rcnt hD
      (show upperDens {N : ℕ | N ∉ Gcov E} < upperDens {N : ℕ | N ∉ Gcov E} + δ by linarith),
    eventually_ge_atTop (1 : ℝ)] with X hX hX1
  refine (nuX_Ioi_le E X).trans ?_
  have hR : 0 < Rcnt X := by
    have := Singularity.one_le_Rcnt hX1
    omega
  exact inv_mul_natCast_le_ofReal hR hX

/-- **Complement ≤ tail + large cofactors** (`Link_Coverage_Disp_ComplLeTail`, EP1054.tex lines
2706–2713) with `Eq_ExactRepresentability` replaced by `RepDensityOne`. The classification was used
only to put the unrepresented integers in the finite set `{0, 2, 5}`; density zero of `ℕ ∖ 𝓡` is
all the upper-density step needs. -/
theorem link_Coverage_Disp_ComplLeTail_tailOnly :
    Lem_Moment → RepDensityOne → Coverage.Disp_ComplLeTail := by
  intro hMom hD k hk
  have hD' : DensZero Rᶜ := hD
  obtain ⟨Ck, -, -, hLC⟩ := hMom k hk
  refine ⟨Ck, fun T hT E hE => ?_⟩
  have hE' : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hsub : {N : ℕ | N ∉ Gcov E} ⊆
      (largeRatioSet T ∪ largeCofactorSet T E) ∪ Rᶜ := by
    intro N hN
    by_cases hR : N ∈ R
    · left
      by_cases hlt : T * N < (f N : ℝ)
      · exact Or.inl ⟨hR, hlt⟩
      · right
        obtain ⟨e, d, he, hd, hfN, hNF⟩ := f_mem_Fform N hR
        refine ⟨e, d, he, hd, hNF, ?_, ?_⟩
        · by_contra hle
          have hle' : e ≤ E := by exact_mod_cast not_lt.1 hle
          exact hN ⟨e, d, he, hle', hd, hNF⟩
        · have h := not_lt.1 hlt
          rw [hfN] at h
          push_cast at h
          exact h
    · right
      exact hR
  have hB : upperDens (largeCofactorSet T E) ≤ Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)) :=
    upperDens_le_of_forall_ge (X₀ := 1) fun X hX => hLC T X E hT hX hE'
  have h1 : upperDens {N : ℕ | N ∉ Gcov E} ≤
      upperDens (largeRatioSet T) + Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)) := by
    calc upperDens {N : ℕ | N ∉ Gcov E}
        ≤ upperDens ((largeRatioSet T ∪ largeCofactorSet T E) ∪ Rᶜ) :=
          upperDens_mono hsub
      _ = upperDens (largeRatioSet T ∪ largeCofactorSet T E) :=
          upperDens_union_of_densZero _ hD'
      _ ≤ upperDens (largeRatioSet T) + upperDens (largeCofactorSet T E) :=
          upperDens_union_le _ _
      _ ≤ upperDens (largeRatioSet T) + Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)) := by
          linarith
  have h2 : ENNReal.ofReal (upperDens (largeRatioSet T)) ≤
      limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδ' : (0 : ℝ) < δ := hδ
    have hfreq : ∃ᶠ n : ℕ in atTop,
        upperDens (largeRatioSet T) - δ < (cnt (largeRatioSet T) n : ℝ) / n :=
      frequently_lt_of_lt_limsup (isCoboundedUnder_le_cnt_div _)
        (by change upperDens (largeRatioSet T) - δ < upperDens (largeRatioSet T); linarith)
    have hle : ENNReal.ofReal (upperDens (largeRatioSet T) - δ) ≤
        limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop := by
      apply le_limsup_of_frequently_le'
      rw [Filter.frequently_atTop] at hfreq ⊢
      intro X₀
      obtain ⟨n, hn, hlt⟩ := hfreq (max 1 ⌈X₀⌉₊)
      have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
      have hnX : X₀ ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil X₀) (by exact_mod_cast le_trans (le_max_right _ _) hn)
      refine ⟨(n : ℝ), hnX, ?_⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hRle : Rcnt (n : ℝ) ≤ n := by
        have := Rcnt_le_floor (n : ℝ)
        rwa [Nat.floor_natCast] at this
      calc ENNReal.ofReal (upperDens (largeRatioSet T) - δ)
          ≤ ((n : ℝ≥0∞))⁻¹ * (cnt (largeRatioSet T) (n : ℝ) : ℝ≥0∞) :=
            ofReal_le_inv_mul_natCast (by omega) ((lt_div_iff₀ hnpos).1 hlt).le
        _ ≤ ((Rcnt (n : ℝ) : ℝ≥0∞))⁻¹ * (cnt (largeRatioSet T) (n : ℝ) : ℝ≥0∞) :=
            mul_le_mul' (ENNReal.inv_le_inv.2 (by exact_mod_cast hRle)) le_rfl
        _ ≤ nuX (n : ℝ) (Set.Ioi (ENNReal.ofReal T)) := nuX_Ioi_ge T (by linarith) (n : ℝ)
    calc ENNReal.ofReal (upperDens (largeRatioSet T))
        = ENNReal.ofReal ((upperDens (largeRatioSet T) - δ) + δ) := by rw [sub_add_cancel]
      _ ≤ ENNReal.ofReal (upperDens (largeRatioSet T) - δ) + ENNReal.ofReal δ :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (upperDens (largeRatioSet T) - δ) + δ := by
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop + δ :=
          add_le_add hle le_rfl
  calc ENNReal.ofReal (upperDens {N : ℕ | N ∉ Gcov E})
      ≤ ENNReal.ofReal (upperDens (largeRatioSet T) +
          Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ))) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal (upperDens (largeRatioSet T)) +
          ENNReal.ofReal (Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ))) := ENNReal.ofReal_add_le
    _ ≤ limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop +
          ENNReal.ofReal (Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ))) := add_le_add h2 le_rfl

end Coverage

section Singularity

open Principia.Erdos1054.Proofs.Singularity

/-- `Singularity.limit_le_integral` with its `Intro_RcntFormula` hypothesis replaced by the only
consequence the proof uses, `X/R(X) → 1`. -/
theorem limit_le_integral_of_tendsto {ν : Measure ℝ≥0∞} (hν : IsWeakSubseqLimit ν)
    (hWD : Step_DaddWitnessDomination) (hEV : Step_DaddEmpiricalWitnessVague)
    (hXR : Tendsto (fun X : ℝ => X / (Rcnt X : ℝ)) atTop (𝓝 1))
    {φ : ℝ≥0∞ → ℝ} (hφ : IsCcPos φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ ENNReal.ofReal (∫ x, φ x ∂witnessMeasure) := by
  obtain ⟨hprob, X, hW⟩ := hν
  haveI := hprob
  have hc := hφ.1
  let Φ : ℝ≥0∞ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ, hc⟩
  have h1 : Tendsto (fun j => ∫ x, φ x ∂(nuX (X j))) atTop (𝓝 (∫ x, φ x ∂ν)) := hW.2 Φ
  have h2 : Tendsto (fun j => (X j / Rcnt (X j)) * ∫ x, φ x ∂(empWitness (X j))) atTop
      (𝓝 (1 * ∫ x, φ x ∂witnessMeasure)) :=
    (hXR.comp hW.1).mul ((hEV φ hφ).comp hW.1)
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

/-- **`ν|_{(0,∞)} ≤ 𝒲`** (`Link_Step_DaddLimitDomination`, EP1054.tex lines 2910–2916) with
`Intro_RcntFormula` replaced by `RepDensityOne`. The proof is `Singularity`'s, verbatim, except that
`X/R(X) → 1` comes from `tendsto_X_div_Rcnt_of_repDensityOne`. -/
theorem link_Step_DaddLimitDomination_tailOnly :
    Step_DaddWitnessDomination → Step_DaddEmpiricalWitnessVague → RepDensityOne →
      Step_DaddWitnessMeasureMass → Step_DaddLimitDomination := by
  intro hWD hEV hD _hWM ν hν
  have hXR := tendsto_X_div_Rcnt_of_repDensityOne hD
  have hprob := hν.1
  haveI := hprob
  set W := witnessMeasure with hWdef
  set O : Set ℝ≥0∞ := Set.Ioo 0 ⊤ with hOdef
  -- (P) for nonnegative `φ ∈ C_c((0,∞))`
  have hPa : ∀ φ : ℝ≥0∞ → ℝ, IsCcPos φ → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂W := by
    intro φ hφ hφ0
    refine (limit_le_integral_of_tendsto hν hWD hEV hXR hφ hφ0).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφ0)
      hφ.1.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  have hPb : ∀ φ : ℝ≥0∞ → ℝ, IsCcPos φ → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂W = ⊤ → ∫⁻ x, ENNReal.ofReal (φ x) ∂ν = 0 := by
    intro φ hφ hφ0 htop
    have h := limit_le_integral_of_tendsto hν hWD hEV hXR hφ hφ0
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
  have hD2 : ∀ K : Set ℝ≥0∞, IsCompact K → K ⊆ G → ν K ≤ W K := by
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
    _ ≤ W F := hD2 F hFc.isCompact (hFsub.trans Set.inter_subset_right)
    _ ≤ W A := measure_mono (hFsub.trans (Set.inter_subset_left.trans Set.inter_subset_left))

/-- **Theorem `thm:dadd:universal-singularity`, main display**
(`Link_Thm_DaddUniversalSingularity_Carrier`, EP1054.tex lines 2839–2848) with `Intro_RcntFormula`
replaced by `RepDensityOne`. `Singularity`'s proof, verbatim, except that `X/R(X) → 1` comes from
`tendsto_X_div_Rcnt_of_repDensityOne`. -/
theorem link_Thm_DaddUniversalSingularity_Carrier_tailOnly :
    Step_DaddSingularCarrier → Step_DaddWitnessCarrier → Step_DaddLimitDomination →
      Step_DaddWitnessMeasureMass → Step_DaddCountDomination → RepDensityOne →
      Prop_DaddWitnessMeans → Thm_SmallValues → EmpiricalMeasures_isProbability →
      Thm_DaddUniversalSingularity_Carrier := by
  intro hSC hWC hLD hWMM hCD hD hWM hSV _
  have hXR := tendsto_X_div_Rcnt_of_repDensityOne hD
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
        hXR.mul (hWM.1 t ht).1
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

/-- **The uniform lower tail** (`Link_Step_DaddLowerTailUniform`, EP1054.tex lines 3001–3006) from
`Step_DaddXoverR_weak` instead of `Step_DaddXoverR`: the constant `3` of `X/R(X) ≤ 3` enters only
the implied constant `C`, so any constant does. `Singularity`'s proof with `3` replaced by `K`. -/
theorem link_Step_DaddLowerTailUniform_weak :
    Thm_SmallUpper_doubleExp → Step_DaddXoverR_weak → Step_DaddLowerTailUniform := by
  rintro ⟨c, hc, C, δ₀, hδ₀, hU⟩ ⟨K, hXR⟩
  refine ⟨c, hc, K * max C 0, -Real.log δ₀, fun u hu X hX => ?_⟩
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
  have hXK := hXR X hX
  have hX0 : 0 ≤ X := by linarith
  calc (cnt (smallRatioSet (Real.exp (-u))) X : ℝ)
      ≤ C * X * Real.exp (-Real.exp (Real.exp (c * u))) := hcnt
    _ ≤ max C 0 * X * Real.exp (-Real.exp (Real.exp (c * u))) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (K * Rcnt X) * Real.exp (-Real.exp (Real.exp (c * u))) := by
        gcongr
    _ = K * max C 0 * Real.exp (-Real.exp (Real.exp (c * u))) * Rcnt X := by ring

end Singularity

section Collision

open Finset Real Principia.Erdos1054.Proofs.Collision7

/-- `Collision7.tendsto_nuX_sub_cnt` with its `Intro_RcntFormula` hypothesis replaced by the only
consequence the proof uses, `R(X)/X → 1` (positivity of `R(X)` is `Singularity.one_le_Rcnt`). -/
theorem tendsto_nuX_sub_cnt_of_tendsto
    (hR1 : Tendsto (fun X : ℝ => (Rcnt X : ℝ) / X) atTop (𝓝 1)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun X : ℝ => (nuX X).real (Set.Iic (ENNReal.ofReal t)) -
      (cnt (smallRatioSet t) X : ℝ) / X) atTop (𝓝 0) := by
  set A := smallRatioSet t with hAdef
  have hinv : Tendsto (fun X : ℝ => X / (Rcnt X : ℝ) - 1) atTop (𝓝 0) := by
    have := hR1.inv₀ one_ne_zero
    rw [inv_one] at this
    have := this.sub_const 1
    rw [sub_self] at this
    refine this.congr (fun X => ?_)
    rw [inv_div]
  refine squeeze_zero_norm' ?_ (hinv.norm.trans_eq (by rw [norm_zero]))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hRpos : (0 : ℝ) < Rcnt X := by exact_mod_cast Singularity.one_le_Rcnt hX
  have hA0 : (0 : ℝ) ≤ cnt A X := Nat.cast_nonneg _
  have hA1 : (cnt A X : ℝ) ≤ X := by
    have := cnt_le_floor A X
    have h' : (cnt A X : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast this
    linarith [Nat.floor_le hXpos.le]
  rw [nuX_Iic_real X t ht]
  have e : (cnt A X : ℝ) / (Rcnt X : ℝ) - (cnt A X : ℝ) / X =
      ((cnt A X : ℝ) / X) * (X / (Rcnt X : ℝ) - 1) := by
    field_simp
  rw [e, norm_mul]
  have hq : ‖(cnt A X : ℝ) / X‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hA0 hXpos.le)]
    exact (div_le_one hXpos).2 hA1
  calc ‖(cnt A X : ℝ) / X‖ * ‖X / (Rcnt X : ℝ) - 1‖ ≤ 1 * ‖X / (Rcnt X : ℝ) - 1‖ :=
        mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    _ = ‖X / (Rcnt X : ℝ) - 1‖ := one_mul _

/-- **`ν_X([0,t]) = (1/X)#{N ≤ X : r*_t(N) > 0} + o(1)`** (`Link_Step_DaddCollisionSupport`,
EP1054.tex lines 3050–3057) with `Intro_RcntFormula` replaced by `RepDensityOne`.
`Collision7.support_link`'s proof, verbatim, except for the normalisation step. -/
theorem link_Step_DaddCollisionSupport_tailOnly :
    Lem_SigmaRangeZero → RepDensityOne → Coverage.Fact_RtPosIff → Step_DaddCollisionSupport := by
  intro hSR hD _hPos t ht
  set A := smallRatioSet t with hAdef
  set B : Set ℕ := {N : ℕ | 0 < rtStar t N} with hBdef
  set Sg : Set ℕ := {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} with hSgdef
  have hBA : B ⊆ A := fun N hN => smallRatio_of_rtStar_pos hN
  have hAB : A ⊆ B ∪ Sg := by
    intro N hN
    by_cases hB : 0 < rtStar t N
    · exact Or.inl hB
    · exact Or.inr (mem_sigRange_of_smallRatio hN hB)
  -- the count difference is `o(X)`
  have hSgR : Tendsto (fun X : ℝ => (cnt Sg X : ℝ) / X) atTop (𝓝 0) := hasDens_tendsto_real hSR
  have hdiff : Tendsto (fun X : ℝ => (cnt A X : ℝ) / X - (cnt B X : ℝ) / X) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hSgR
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have := cnt_mono hBA X
      have : (cnt B X : ℝ) ≤ cnt A X := by exact_mod_cast this
      rw [← sub_div]
      exact div_nonneg (by linarith) hX.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have h1 := cnt_le_cnt_add_of_subset_union hAB X
      have h1' : (cnt A X : ℝ) ≤ cnt B X + cnt Sg X := by exact_mod_cast h1
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hX.le
  have hnu := tendsto_nuX_sub_cnt_of_tendsto (tendsto_Rcnt_div_of_repDensityOne hD) ht.le
  have hsum := hnu.add hdiff
  rw [add_zero] at hsum
  refine hsum.congr (fun X => ?_)
  rw [cnt_rtStar_pos]
  ring

/-- **Proposition `prop:dadd:collision-criterion`** (`Link_Prop_DaddCollisionCriterion`, EP1054.tex
lines 3032–3072) with `Intro_RcntFormula` replaced by `RepDensityOne`.
`Collision7.propCriterion_link`'s proof, verbatim, except for the normalisation step. -/
theorem link_Prop_DaddCollisionCriterion_tailOnly :
    Eq_DaddCollisionCriterion → RepDensityOne → Thm_DaddUniversalSingularity_Carrier →
      EmpiricalMeasures_isProbability → Prop_DaddCollisionCriterion := by
  intro hEq hD hCar hProb
  obtain ⟨Z, -, -, -, hZ⟩ := hCar
  refine ⟨hEq, ?_, ?_⟩
  · -- the threshold density exists iff `K_X(t)` converges
    intro t ht
    have hK := hEq t ht
    have hν := tendsto_nuX_sub_cnt_of_tendsto (tendsto_Rcnt_div_of_repDensityOne hD) ht.le
    constructor
    · rintro ⟨d, hd⟩
      have hc : Tendsto (fun X : ℝ => (cnt (smallRatioSet t) X : ℝ) / X) atTop (𝓝 d) :=
        hasDens_tendsto_real hd
      refine ⟨WstarFun t - d, ?_⟩
      have h1 := (tendsto_const_nhds (x := WstarFun t)).sub ((hc.add hν).sub hK)
      rw [add_zero, sub_zero] at h1
      refine h1.congr (fun X => ?_)
      ring
    · rintro ⟨L, hL⟩
      refine ⟨WstarFun t - L, hasDens_of_tendsto_real ?_⟩
      have h1 := (((tendsto_const_nhds (x := WstarFun t)).sub hL).add hK).sub hν
      rw [add_zero, sub_zero] at h1
      refine h1.congr (fun X => ?_)
      change WstarFun t - KX X t + ((nuX X).real (Set.Iic (ENNReal.ofReal t)) -
        (WstarFun t - KX X t)) - ((nuX X).real (Set.Iic (ENNReal.ofReal t)) -
          (cnt (smallRatioSet t) X : ℝ) / X) = (cnt (smallRatioSet t) X : ℝ) / X
      ring
  · constructor
    · -- weak convergence ⟹ convergence of every `K_X(q)`
      rintro ⟨ν, hνP, hconv⟩ q hq
      have hWSL : IsWeakSubseqLimit ν :=
        ⟨hνP, fun j : ℕ => (j : ℝ), tendsto_natCast_atTop_atTop,
          fun φ => (hconv φ).comp tendsto_natCast_atTop_atTop⟩
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      have hat : ν {ENNReal.ofReal (q : ℝ)} = 0 :=
        (hZ ν hWSL).2.2.2 _ (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq')
          ENNReal.ofReal_ne_top
      let μ : ProbabilityMeasure ℝ≥0∞ := ⟨ν, hνP⟩
      have hlim : Tendsto (fun X : ℝ => muP hProb X) atTop (𝓝 μ) := by
        rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
        intro φ
        refine (hconv φ).congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
        rw [muP_coe hProb hX]
      have hreal := nuX_real_tendsto_of_muP hProb tendsto_id hlim (q := (q : ℝ)) hat
      refine ⟨WstarFun q - ν.real (Set.Iic (ENNReal.ofReal (q : ℝ))), ?_⟩
      have h1 := ((tendsto_const_nhds (x := WstarFun q)).sub hreal).add (hEq q hq')
      rw [add_zero] at h1
      refine h1.congr (fun X => ?_)
      simp only [id]
      ring
    · -- convergence of every `K_X(q)` ⟹ weak convergence
      intro hKq
      choose! L hL using hKq
      have hnuq : ∀ q : ℚ, 0 < q → Tendsto (fun X : ℝ => (nuX X).real
          (Set.Iic (ENNReal.ofReal (q : ℝ)))) atTop (𝓝 (WstarFun q - L q)) := by
        intro q hq
        have hq' : (0 : ℝ) < q := by exact_mod_cast hq
        have h1 := (hEq q hq').add ((tendsto_const_nhds (x := WstarFun q)).sub (hL q hq))
        rw [zero_add] at h1
        refine h1.congr (fun X => ?_)
        ring
      -- every cluster point has the same values on the `[0, q]`
      have hclus : ∀ ν : ProbabilityMeasure ℝ≥0∞, MapClusterPt ν atTop (muP hProb) →
          ∀ q : ℚ, 0 < q → (ν : Measure ℝ≥0∞) (Set.Iic (ENNReal.ofReal (q : ℝ))) =
            ENNReal.ofReal (WstarFun q - L q) := by
        intro ν hν q hq
        obtain ⟨ψ, hψν, hψ⟩ := hν.exists_seq_tendsto
        have hq' : (0 : ℝ) < q := by exact_mod_cast hq
        have hWSL : IsWeakSubseqLimit (ν : Measure ℝ≥0∞) :=
          ⟨inferInstance, ψ, hψ, fun φ => integral_tendsto_of_muP hProb hψ hψν φ⟩
        have hat : (ν : Measure ℝ≥0∞) {ENNReal.ofReal (q : ℝ)} = 0 :=
          (hZ _ hWSL).2.2.2 _ (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq')
            ENNReal.ofReal_ne_top
        have h1 := nuX_real_tendsto_of_muP hProb hψ hψν hat
        have h2 := (hnuq q hq).comp hψ
        have heq := tendsto_nhds_unique h1 h2
        rw [← heq, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      obtain ⟨ν0, hν0⟩ := exists_clusterPt_of_compactSpace (map (muP hProb) atTop)
      have huniq : ∀ ν : ProbabilityMeasure ℝ≥0∞, MapClusterPt ν atTop (muP hProb) → ν = ν0 := by
        intro ν hν
        apply probMeasure_eq_of_Iic_rat
        intro q hq
        rw [hclus ν hν q hq, hclus ν0 hν0 q hq]
      have hlim := tendsto_nhds_of_unique_mapClusterPt huniq
      exact ⟨(ν0 : Measure ℝ≥0∞), inferInstance,
        fun φ => integral_tendsto_of_muP hProb tendsto_id hlim φ⟩

end Collision

section RemT

open Finset Principia.Erdos1054.Proofs.CoverageEta

/-- `CoverageEta.rt_eq_zero_iff` without `Eq_ExactRepresentability`: the classification was used
only for `1 ≤ N` on `𝓡`, which holds outright (`Singularity.one_le_of_mem_R`). -/
theorem rt_eq_zero_iff_of_mem (hRt : Coverage.Fact_RtPosIff) {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : N ∈ R) : rt A N = 0 ↔ ENNReal.ofReal A < ratioE N := by
  have hN1 : 1 ≤ N := Singularity.one_le_of_mem_R hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  unfold ratioE
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hA.le, lt_div_iff₀ hNpos, ← not_le,
    ← hRt A hA N hN]
  omega

/-- The large-ratio represented targets have `r_A = 0`. -/
theorem big_subset_rt_of_mem (hRt : Coverage.Fact_RtPosIff) {A : ℝ} (hA : 0 < A) :
    {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} ⊆ {N : ℕ | rt A N = 0} := by
  rintro N ⟨hN, hlt⟩
  exact (rt_eq_zero_iff_of_mem hRt hA hN).2 hlt

/-- `r_A(N) = 0` only at large-ratio represented targets and at unrepresented `N` (the spine's
version names the unrepresented set `{0, 2, 5}`). -/
theorem rt_subset_big_union_compl (hRt : Coverage.Fact_RtPosIff) {A : ℝ} (hA : 0 < A) :
    {N : ℕ | rt A N = 0} ⊆ {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} ∪ Rᶜ := by
  intro N hN
  by_cases hR : N ∈ R
  · exact Or.inl ⟨hR, (rt_eq_zero_iff_of_mem hRt hA hR).1 hN⟩
  · exact Or.inr hR

/-- Tight ⟹ `eq:T`, from density one (`CoverageEta.eqT_of_nuTight` used `R(n) = n − 2` and the
finite exceptional set `{0, 2, 5}`; `R(n) ≤ n` and density zero of `ℕ ∖ 𝓡` suffice). -/
theorem eqT_of_nuTight_of_repDensityOne (hRt : Coverage.Fact_RtPosIff) (hD : RepDensityOne)
    (hNT : Coverage.NuTight) : Eq_T := by
  have hD' : DensZero Rᶜ := hD
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ A : ℝ in atTop, upperDens {N : ℕ | rt A N = 0} ≤ ε := by
    intro ε hε
    have h1 := (ENNReal.tendsto_nhds_zero.1 hNT) (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with A hA hA1
    have hA0 : 0 < A := by linarith
    have hbig : upperDens {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} ≤ ε := by
      apply upperDens_le_of_eventually
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hX : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hν : nuX n (Set.Ioi (ENNReal.ofReal A)) ≤ ENNReal.ofReal ε :=
        le_trans (le_iSup₂ (f := fun (X : ℝ) (_ : 1 ≤ X) => nuX X (Set.Ioi (ENNReal.ofReal A)))
          (n : ℝ) hX) hA
      have hR1 := Singularity.one_le_Rcnt hX
      rw [nuX_Ioi, inv_mul_le_ofReal_iff (by omega) hε.le] at hν
      have hRle : (Rcnt (n : ℝ) : ℝ) ≤ n := by
        have := ThetaTight.Rcnt_le_floor (n : ℝ)
        rw [Nat.floor_natCast] at this
        exact_mod_cast this
      have h2 : ε * (Rcnt (n : ℝ) : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_left hRle hε.le
      linarith
    calc upperDens {N : ℕ | rt A N = 0}
        ≤ upperDens ({N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} ∪ Rᶜ) :=
          upperDens_mono (rt_subset_big_union_compl hRt hA0)
      _ = upperDens {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} :=
          upperDens_union_of_densZero _ hD'
      _ ≤ ε := hbig
  rw [Eq_T, tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall (fun A => lt_of_lt_of_le ha (upperDens_nonneg _)),
    fun a ha => ?_⟩
  filter_upwards [key (a / 2) (by linarith)] with A hA
  linarith

/-- `eq:T` ⟹ tight, from density one (`CoverageEta.nuTight_of_eqT` used `R(X) = ⌊X⌋ − 2`; the
bound `R(X) ≥ ⌊X⌋/2` for large `X`, from density one, is all it needs). -/
theorem nuTight_of_eqT_of_repDensityOne (hRt : Coverage.Fact_RtPosIff) (hD : RepDensityOne)
    (hT : Eq_T) : Coverage.NuTight := by
  have hD' : DensZero Rᶜ := hD
  unfold Coverage.NuTight
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' htop, by rw [ENNReal.ofReal_toReal htop]⟩
  have hev := (tendsto_order.1 hT).2 (η / 2) (by linarith)
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.1 hev
  have hAd : upperDens {N : ℕ | rt (max A₁ 1) N = 0} < η / 2 := hA₁ _ (le_max_left _ _)
  have hA0 : (0 : ℝ) < max A₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((eventually_cnt_lt_mul_of_upperDens_lt hAd).and
    (densZero_iff_eventually_le.1 hD' (1 / 2) (by norm_num)))
  filter_upwards [eventually_ge_atTop
    (max (max A₁ 1) (∑ N ∈ Finset.range (max n₀ 1), (f N : ℝ)))] with T hT
  have hTA : max A₁ 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTM : ∑ N ∈ Finset.range (max n₀ 1), (f N : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  refine le_trans (iSup₂_le fun X hX => ?_) hηε
  rw [nuX_Ioi]
  by_cases hn : ⌊X⌋₊ < max n₀ 1
  · have h0 : cnt {N : ℕ | N ∈ R ∧ ENNReal.ofReal T < ratioE N} X = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro N hN
      rw [mem_cntFinset] at hN
      obtain ⟨⟨hN1, hNX⟩, _, hlt⟩ := hN
      have hNr : N ∈ Finset.range (max n₀ 1) := Finset.mem_range.2 (by omega)
      have hfN : (f N : ℝ) ≤ T :=
        le_trans (Finset.single_le_sum (fun i _ => Nat.cast_nonneg (f i)) hNr) hTM
      have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hdiv : (f N : ℝ) / N ≤ T := le_trans (div_le_self (Nat.cast_nonneg _) hN1') hfN
      have := ENNReal.ofReal_le_ofReal hdiv
      unfold ratioE at hlt
      exact absurd hlt (not_lt.2 this)
    rw [h0, Nat.cast_zero, mul_zero]
    exact zero_le
  · rw [not_lt] at hn
    have hR1 := Singularity.one_le_Rcnt hX
    rw [inv_mul_le_ofReal_iff (by omega) hη.le]
    have h1 := cnt_mono (big_anti hTA) X
    have h2 := cnt_mono (big_subset_rt_of_mem hRt hA0) X
    obtain ⟨h3, h4⟩ := hn₀ ⌊X⌋₊ (le_trans (le_max_left _ _) hn)
    rw [cnt_floor] at h3 h4
    have hsum : (cnt R X : ℝ) + (cnt Rᶜ X : ℝ) = (⌊X⌋₊ : ℝ) := by
      exact_mod_cast cnt_add_cnt_compl R X
    have h12 : (cnt {N : ℕ | N ∈ R ∧ ENNReal.ofReal T < ratioE N} X : ℝ) ≤
        (cnt {N : ℕ | rt (max A₁ 1) N = 0} X : ℝ) := by exact_mod_cast le_trans h1 h2
    have hF : (⌊X⌋₊ : ℝ) ≤ 2 * (cnt R X : ℝ) := by linarith
    have hF' : η / 2 * (⌊X⌋₊ : ℝ) ≤ η / 2 * (2 * (cnt R X : ℝ)) :=
      mul_le_mul_of_nonneg_left hF (by linarith)
    change _ ≤ η * (cnt R X : ℝ)
    linarith

/-- **`eq:T` ⟺ the weak bounded-cofactor conjecture** (`Link_Coverage_Rem_T_iff_Conj`, EP1054.tex
lines 2719–2722) with `Eq_ExactRepresentability` and `Intro_RcntFormula` replaced by
`RepDensityOne`. -/
theorem link_Coverage_Rem_T_iff_Conj_tailOnly :
    Coverage.Fact_RtPosIff → RepDensityOne → Prop_TightnessEquivalence →
      Coverage.Rem_T_iff_Conj := by
  intro hRt hD hTE
  unfold Coverage.Rem_T_iff_Conj
  rw [hTE.2.2]
  exact ⟨nuTight_of_eqT_of_repDensityOne hRt hD, eqT_of_nuTight_of_repDensityOne hRt hD⟩

end RemT

/-! ## 3. The recomposed headlines

Each composition is `Spine.spine_<X>`'s `have` chain, applied to the library's proved links and
leaves, with the tail-only links of section 2 in place of the links that consumed
`Intro_RcntFormula`, `Eq_ExactRepresentability` or `Step_DaddXoverR`. The Fraiture sub-DAG
(`Prop_FraitureFinite`, `Thm_FraitureRepresentability`, `Link_Intro_RcntFormula`) is gone from every
composition, and with it `Cite_Dusart_Thm69` and the three `Comp_*` checks. -/

/-- **`prop:tightness-equivalence` from density one of `𝓡`.** The composition is
`Spine.spine_Prop_TightnessEquivalence`'s tail: `Lem_Moment`, the two displays, the equivalence.

**Hypothesis:** `RepDensityOne` only. -/
theorem prop_TightnessEquivalence_of_repDensityOne (hD : RepDensityOne) :
    Prop_TightnessEquivalence :=
  have v_Lem_Moment : Lem_Moment := link_Lem_Moment leaf_Eq_Reflection
  have v_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl :=
    link_Coverage_Disp_TailLeCompl_tailOnly hD
  have v_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail :=
    link_Coverage_Disp_ComplLeTail_tailOnly v_Lem_Moment hD
  link_Prop_TightnessEquivalence v_Coverage_Disp_TailLeCompl v_Coverage_Disp_ComplLeTail
    leaf_Coverage_Fact_UpperDensCompl

/-- **EP1054 `prop:tightness-equivalence` without the exact classification.**

**Remaining hypothesis:** `Cite_Helfgott_weighted`. (Round 3,
`Proofs.ep1054_Prop_TightnessEquivalence`: Helfgott, `Cite_Dusart_Thm69`, `Comp_Verifier_small`,
`Comp_Verifier_window1`, `Comp_Verifier_largeSeed`.) -/
theorem ep1054_Prop_TightnessEquivalence_tailOnly
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Prop_TightnessEquivalence :=
  prop_TightnessEquivalence_of_repDensityOne (repDensityOne_of_helfgott i_Cite_Helfgott_weighted)

/-- **`eq:T` ⟺ `Conj_BoundedCofactorWeak` (`Coverage.Rem_T_iff_Conj`) without the exact
classification.** Not a headline of the spine (it is a field of `Spine.DerivedClaims`), included
because it is the only other derived claim whose link consumes `Eq_ExactRepresentability` and is
not itself a restatement of the classification.

**Remaining hypothesis:** `Cite_Helfgott_weighted`. (Round 3, through `ep1054_all_r3`: Helfgott,
`Cite_Dusart_Thm69` and the three `Comp_*`.) -/
theorem coverage_Rem_T_iff_Conj_tailOnly (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Coverage.Rem_T_iff_Conj :=
  have hD : RepDensityOne := repDensityOne_of_helfgott i_Cite_Helfgott_weighted
  link_Coverage_Rem_T_iff_Conj_tailOnly leaf_Coverage_Fact_RtPosIff hD
    (prop_TightnessEquivalence_of_repDensityOne hD)

/-- **`thm:dadd:universal-singularity` from density one of `𝓡`.** The composition is
`Spine.spine_Thm_DaddUniversalSingularity`'s, with `Thm_SmallValues` from
`Alt.ep1054_Thm_SmallValues_r3` (the sieve discharged), `Prop_DaddWitnessMeans` from
`Alt.ep1054_Prop_DaddWitnessMeans_unconditional` and `Cite_PollackAP` from
`Proofs.input_Cite_PollackAP`; the tightness equivalence, `Step_DaddLimitDomination` and the carrier
link are the tail-only ones.

**Hypotheses:** `RepDensityOne`, `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Erdos_singular`. -/
theorem thm_DaddUniversalSingularity_of_repDensityOne (hD : RepDensityOne)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Thm_DaddUniversalSingularity :=
  have v_Cite_Davenport : Cite_Davenport := link_Cite_Davenport input_Cite_PollackAP
  have v_Thm_SmallValues : Thm_SmallValues :=
    ep1054_Thm_SmallValues_r3 i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25
      i_Cite_Pollack_Thm14
  have v_Prop_TightnessEquivalence : Prop_TightnessEquivalence :=
    prop_TightnessEquivalence_of_repDensityOne hD
  have v_Fact_DaddDavenportLaw : Fact_DaddDavenportLaw :=
    link_Fact_DaddDavenportLaw v_Cite_Davenport
  have v_Fact_DaddProgressionLaws : Fact_DaddProgressionLaws :=
    link_Fact_DaddProgressionLaws input_Cite_PollackAP
  have v_Eq_DaddProgressionDomination : Eq_DaddProgressionDomination :=
    link_Eq_DaddProgressionDomination v_Fact_DaddDavenportLaw v_Fact_DaddProgressionLaws
  have v_Prop_DaddWitnessMeans : Prop_DaddWitnessMeans :=
    ep1054_Prop_DaddWitnessMeans_unconditional
  have v_Step_DaddSingularCarrier : Step_DaddSingularCarrier :=
    link_Step_DaddSingularCarrier v_Fact_DaddDavenportLaw i_Cite_Erdos_singular
  have v_Step_DaddWitnessMeasureMass : Step_DaddWitnessMeasureMass :=
    link_Step_DaddWitnessMeasureMass v_Prop_DaddWitnessMeans v_Fact_DaddProgressionLaws
  have v_Step_DaddWitnessCarrier : Step_DaddWitnessCarrier :=
    link_Step_DaddWitnessCarrier v_Fact_DaddDavenportLaw v_Eq_DaddProgressionDomination
  have v_Step_DaddEmpiricalWitnessVague : Step_DaddEmpiricalWitnessVague :=
    link_Step_DaddEmpiricalWitnessVague v_Prop_DaddWitnessMeans v_Step_DaddWitnessMeasureMass
  have v_Step_DaddLimitDomination : Step_DaddLimitDomination :=
    link_Step_DaddLimitDomination_tailOnly leaf_Step_DaddWitnessDomination
      v_Step_DaddEmpiricalWitnessVague hD v_Step_DaddWitnessMeasureMass
  have v_Thm_DaddUniversalSingularity_Carrier : Thm_DaddUniversalSingularity_Carrier :=
    link_Thm_DaddUniversalSingularity_Carrier_tailOnly v_Step_DaddSingularCarrier
      v_Step_DaddWitnessCarrier v_Step_DaddLimitDomination v_Step_DaddWitnessMeasureMass
      leaf_Step_DaddCountDomination hD v_Prop_DaddWitnessMeans v_Thm_SmallValues
      leaf_EmpiricalMeasures_isProbability
  have v_Thm_DaddUniversalSingularity_FinitePart : Thm_DaddUniversalSingularity_FinitePart :=
    link_Thm_DaddUniversalSingularity_FinitePart v_Thm_DaddUniversalSingularity_Carrier
  have v_Thm_DaddUniversalSingularity_Tight : Thm_DaddUniversalSingularity_Tight :=
    link_Thm_DaddUniversalSingularity_Tight v_Prop_TightnessEquivalence
      v_Thm_DaddUniversalSingularity_FinitePart leaf_EmpiricalMeasures_isProbability
  ⟨v_Thm_DaddUniversalSingularity_Carrier, v_Thm_DaddUniversalSingularity_FinitePart,
    v_Thm_DaddUniversalSingularity_Tight⟩

/-- **EP1054 `thm:dadd:universal-singularity` without the exact classification.**

**Remaining hypotheses:** `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. (Round 3,
`Alt.ep1054_Thm_DaddUniversalSingularity_r3`: the same plus `Cite_Dusart_Thm69` and the three
`Comp_*`.) -/
theorem ep1054_Thm_DaddUniversalSingularity_tailOnly
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Thm_DaddUniversalSingularity :=
  thm_DaddUniversalSingularity_of_repDensityOne (repDensityOne_of_helfgott i_Cite_Helfgott_weighted)
    i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25 i_Cite_Pollack_Thm14
    i_Cite_Erdos_singular

/-- **The heavy-tail corollary from density one of `𝓡`.** The composition is
`Spine.spine_Cor_DaddHeavyTails`'s tail (as in `Alt.ep1054_Cor_DaddHeavyTails_r3`), with the
universal-singularity parts from `thm_DaddUniversalSingularity_of_repDensityOne`, `Eq_AlmostLogTail`
from the unconditional Goldbach route, and `Step_DaddLowerTailUniform` from
`link_Step_DaddLowerTailUniform_weak` and `stepDaddXoverR_weak_of_repDensityOne`.

**Hypotheses:** `RepDensityOne`, `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Erdos_singular`. -/
theorem cor_DaddHeavyTails_of_repDensityOne (hD : RepDensityOne)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Cor_DaddHeavyTails :=
  have v_Univ : Thm_DaddUniversalSingularity :=
    thm_DaddUniversalSingularity_of_repDensityOne hD i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range
      i_Cite_LP_Lemma25 i_Cite_Pollack_Thm14 i_Cite_Erdos_singular
  have v_Carrier : Thm_DaddUniversalSingularity_Carrier := v_Univ.1
  have v_Tight : Thm_DaddUniversalSingularity_Tight := v_Univ.2.2
  have v_Eq_AlmostLogTail : Eq_AlmostLogTail :=
    eq_AlmostLogTail_of_goldbachDensZero std_GoldbachDensZero_unconditional
  have v_Thm_SmallUpper_doubleExp : Thm_SmallUpper_doubleExp := ep1054_Thm_SmallUpper.1
  have v_Step_DaddXoverR_weak : Step_DaddXoverR_weak := stepDaddXoverR_weak_of_repDensityOne hD
  have v_Step_DaddLowerTailUniform : Step_DaddLowerTailUniform :=
    link_Step_DaddLowerTailUniform_weak v_Thm_SmallUpper_doubleExp v_Step_DaddXoverR_weak
  have v_Eq_DaddSubsequentialTail : Eq_DaddSubsequentialTail :=
    link_Eq_DaddSubsequentialTail v_Eq_AlmostLogTail v_Carrier
      leaf_EmpiricalMeasures_isProbability
  have v_PosMoments : Cor_DaddHeavyTails_PosMoments :=
    link_Cor_DaddHeavyTails_PosMoments v_Eq_AlmostLogTail v_Eq_DaddSubsequentialTail
  have v_LogMeans : Cor_DaddHeavyTails_LogMeans :=
    link_Cor_DaddHeavyTails_LogMeans v_Eq_AlmostLogTail v_Eq_DaddSubsequentialTail
      v_Step_DaddLowerTailUniform
  have v_InvMoments : Cor_DaddHeavyTails_InvMoments :=
    link_Cor_DaddHeavyTails_InvMoments v_Step_DaddLowerTailUniform
  have v_InvMomentConv : Cor_DaddHeavyTails_InvMomentConv :=
    link_Cor_DaddHeavyTails_InvMomentConv v_InvMoments
  have v_GeomMean : Cor_DaddHeavyTails_GeomMean := link_Cor_DaddHeavyTails_GeomMean v_LogMeans
  have v_TightTails : Cor_DaddHeavyTails_Tight :=
    link_Cor_DaddHeavyTails_Tight v_Tight v_PosMoments v_LogMeans
  ⟨v_Eq_DaddSubsequentialTail, v_PosMoments, v_LogMeans, v_InvMoments, v_InvMomentConv,
    v_GeomMean, v_TightTails⟩

/-- **EP1054 heavy-tail corollary without the exact classification.**

**Remaining hypotheses:** `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. (Round 3,
`Alt.ep1054_Cor_DaddHeavyTails_r3`: the same plus `Cite_Dusart_Thm69` and the three `Comp_*`.) -/
theorem ep1054_Cor_DaddHeavyTails_tailOnly
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Cor_DaddHeavyTails :=
  cor_DaddHeavyTails_of_repDensityOne (repDensityOne_of_helfgott i_Cite_Helfgott_weighted)
    i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25 i_Cite_Pollack_Thm14
    i_Cite_Erdos_singular

/-- **`prop:dadd:collision-criterion` from density one of `𝓡`.** The composition is
`Spine.spine_Prop_DaddCollisionCriterion`'s tail, with the carrier from
`thm_DaddUniversalSingularity_of_repDensityOne` and the two tail-only links.

**Hypotheses:** `RepDensityOne`, `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Erdos_singular`. -/
theorem prop_DaddCollisionCriterion_of_repDensityOne (hD : RepDensityOne)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Prop_DaddCollisionCriterion :=
  have v_Carrier : Thm_DaddUniversalSingularity_Carrier :=
    (thm_DaddUniversalSingularity_of_repDensityOne hD i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range
      i_Cite_LP_Lemma25 i_Cite_Pollack_Thm14 i_Cite_Erdos_singular).1
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero :=
    link_Lem_SigmaRangeZero (link_Lem_FixedModulusNormality leaf_Std_recipPrimesAP_diverges)
  have v_Step_DaddCollisionSupport : Step_DaddCollisionSupport :=
    link_Step_DaddCollisionSupport_tailOnly v_Lem_SigmaRangeZero hD leaf_Coverage_Fact_RtPosIff
  have v_Eq_DaddCollisionCriterion : Eq_DaddCollisionCriterion :=
    link_Eq_DaddCollisionCriterion v_Step_DaddCollisionSupport
      ep1054_Prop_DaddWitnessMeans_unconditional
  link_Prop_DaddCollisionCriterion_tailOnly v_Eq_DaddCollisionCriterion hD v_Carrier
    leaf_EmpiricalMeasures_isProbability

/-- **EP1054 `prop:dadd:collision-criterion` without the exact classification.**

**Remaining hypotheses:** `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. (Round 3,
`Alt.ep1054_Prop_DaddCollisionCriterion_r3`: the same plus `Cite_Dusart_Thm69` and the three
`Comp_*`.) -/
theorem ep1054_Prop_DaddCollisionCriterion_tailOnly
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Prop_DaddCollisionCriterion :=
  prop_DaddCollisionCriterion_of_repDensityOne (repDensityOne_of_helfgott i_Cite_Helfgott_weighted)
    i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25 i_Cite_Pollack_Thm14
    i_Cite_Erdos_singular

/-! ## 4. What still needs the classification: only its own restatements

After sections 2–3, the links that consume `Eq_ExactRepresentability` or `Intro_RcntFormula` and
still have no tail-only replacement are `Link_Intro_RcntFormula` and
`Link_Thm_FraitureRepresentability_Ge6`. Their conclusions are not weaker than the classification:
given the elementary leaf `Step_FraitureSmallCases`, each *implies* it. So no input weaker than
the one behind `Eq_ExactRepresentability` (Helfgott, Dusart and the three verifier checks) can
deliver them. -/

/-- "`f(N)` is defined for every `N ≥ 6`" is the classification, given the small cases
`1, 3, 4 ∈ 𝓡` and `0, 2, 5 ∉ 𝓡`. -/
theorem eqExactRepresentability_of_ge6 (hS : Step_FraitureSmallCases)
    (h6 : Thm_FraitureRepresentability_Ge6) : Eq_ExactRepresentability := by
  obtain ⟨h1, h3, h4, h2, h5, h0⟩ := hS
  change R = {N : ℕ | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5}
  ext N
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hN
    refine ⟨Nat.pos_of_ne_zero ?_, ?_, ?_⟩
    · rintro rfl
      exact h0 hN
    · rintro rfl
      exact h2 hN
    · rintro rfl
      exact h5 hN
  · rintro ⟨hN1, hN2, hN5⟩
    by_cases hsmall : N < 6
    · have hcases : N = 1 ∨ N = 3 ∨ N = 4 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact ⟨1, le_rfl, h1⟩
      · exact ⟨2, by norm_num, h3⟩
      · exact ⟨3, by norm_num, h4⟩
    · exact h6 N (by omega)

/-- `R(X) = ⌊X⌋ − 2` for `X ≥ 5` forces every `N ≥ 6` into `𝓡`: `R(N) − R(N − 1) = 1`. -/
theorem ge6_of_rcntFormula (hRF : Intro_RcntFormula) : Thm_FraitureRepresentability_Ge6 := by
  intro N hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 5 ≤ M)
  have hM1 : (5 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ M + 1)
  have ha := hRF (M : ℝ) hM
  have hb := hRF ((M + 1 : ℕ) : ℝ) hM1
  rw [Nat.floor_natCast] at ha hb
  change cnt R (M : ℝ) = M - 2 at ha
  change cnt R ((M + 1 : ℕ) : ℝ) = M + 1 - 2 at hb
  have hs := cnt_succ R M
  by_contra hnot
  rw [if_neg hnot] at hs
  omega

/-- **`Intro_RcntFormula` is equivalent to the classification** (forward: the spine link
`Proofs.link_Intro_RcntFormula`; backward: `ge6_of_rcntFormula` and the proved leaf
`Proofs.leaf_Step_FraitureSmallCases`). -/
theorem eqExactRepresentability_iff_rcntFormula :
    Eq_ExactRepresentability ↔ Intro_RcntFormula :=
  ⟨link_Intro_RcntFormula, fun hRF =>
    eqExactRepresentability_of_ge6 leaf_Step_FraitureSmallCases (ge6_of_rcntFormula hRF)⟩

/-- **`Thm_FraitureRepresentability_Ge6` is equivalent to the classification** (forward: the spine
link `Proofs.link_Thm_FraitureRepresentability_Ge6`). -/
theorem eqExactRepresentability_iff_ge6 :
    Eq_ExactRepresentability ↔ Thm_FraitureRepresentability_Ge6 :=
  ⟨link_Thm_FraitureRepresentability_Ge6,
    eqExactRepresentability_of_ge6 leaf_Step_FraitureSmallCases⟩

end Principia.Erdos1054.Alt.TailOnly
