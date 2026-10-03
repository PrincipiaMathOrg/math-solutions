/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt.TailOnly
import Principia.Erdos1054.Rate.Bridge
import Principia.Erdos1054.Proofs.InputsLP21
import Principia.Erdos1054.Proofs.InputsLP22
import Principia.Erdos1054.Proofs.InputsLP25
import Principia.Erdos1054.Proofs.InputsPollack14

set_option autoImplicit false

/-!
# EP1054 headlines after round 4

Round 4 landed five pieces, each a theorem of this library with footprint within
`[propext, Classical.choice, Quot.sound]`:

* `Principia.Erdos1054.Rate.std_GoldbachRate_unconditional` (`Rate/Bridge.lean`, from
  `Principia.Common.GoldbachRate.goldbach_exceptional_rate`): the even numbers `≤ X` that are not a
  sum of two primes number `≪ X / log X`. From it, `Rate.lem_AOR_unconditional` and
  `Rate.thm_SubexpGrowth_unconditional`.
* `Proofs.input_Cite_LP_Lemma21` (`Common/LucaPomerance/Lemma21*.lean`, `MertensAP.lean`,
  `OmegaP.lean`).
* `Proofs.input_Cite_LP_Lemma22_range` (`Common/LucaPomerance/SquareDivisor.lean`).
* `Proofs.input_Cite_LP_Lemma25` (`Common/LucaPomerance/Lemma25.lean`).
* `Proofs.input_Cite_Pollack_Thm14` (`Common/LucaPomerance/{Abundancy,Smooth,AliquotPrimes,
  Pollack14}.lean`).

and one re-routing, `Alt.TailOnly`: the §6–§7 headlines that consumed the exact classification
`𝓡 = ℕ ∖ {0, 2, 5}` use it only as density one of `𝓡` (`TailOnly.RepDensityOne`), which the tail
`Prop_FraitureTail` (Helfgott alone) supplies. That removes `Cite_Dusart_Thm69` and the three
`Comp_Verifier_*` checks from them.

This module feeds all of it into the paper's headlines. Every theorem here states a headline
`Prop` of `Principia.Erdos1054` exactly as the spine does; its hypotheses (listed in each docstring)
are exactly the trusted inputs it still needs, and **none** means an unconditional theorem.

**Newly unconditional:** Theorem 1.2 (`Thm_SmallValues`), Theorem 1.4 (`Thm_SubexpGrowth`),
`Lem_AnalyticOddRepresentability`, `Lem_LPInputs`, `Lem_SvRegular`. With Theorem 1.1 (round 1) and
Theorem 1.3 (round 3), **all four main theorems of §1 of EP1054 (Theorems 1.1–1.4) are
unconditional theorems of this library.** The paper's two other theorems still carry inputs:
`thm:fraiture-representability` (Helfgott, Dusart, the three verifier checks) and
`thm:dadd:universal-singularity` (Helfgott, `Cite_Erdos_singular`; section 3 below).

**Remaining trusted inputs of the whole paper (8):** `Cite_Helfgott_weighted`, `Cite_Dusart_Thm69`,
`Cite_Axler_Cor2`, `Cite_ChenZhao`, `Cite_Erdos_singular`, `Comp_Verifier_small`,
`Comp_Verifier_window1`, `Comp_Verifier_largeSeed` (`ep1054_all_r4`).
-/

namespace Principia.Erdos1054.Alt.Round4

open Principia.Erdos1054 Principia.Erdos1054.Spine Principia.Erdos1054.Proofs

/-! ## 1. Theorem 1.4 and the odd-representability lemma, from the Goldbach rate -/

/-- **`lem:analytic-odd-representability` (both halves), unconditionally**: the odd unrepresented
integers up to `X` number `≤ C (X^{1-c} + X / log X)`, and `o(X / log₃ X)`. From the rated circle
method (`Rate.lem_AOR_unconditional`); the paper takes it from Montgomery–Vaughan.

**Remaining hypotheses: none.** (Round 3: `Cite_Helfgott_weighted` via `Alt.lemAOR_ofHelfgott`, or
`Cite_MV_exceptional` via `Proofs.ep1054_Lem_AnalyticOddRepresentability`.) -/
theorem ep1054_Lem_AnalyticOddRepresentability_unconditional :
    Principia.Erdos1054.Lem_AnalyticOddRepresentability :=
  Principia.Erdos1054.Rate.lem_AOR_unconditional

/-- **EP1054 Theorem 1.4 (`thm:subexp-growth`), unconditionally**, from the Goldbach rate
`Std_GoldbachRate` (`Rate.thm_SubexpGrowth_unconditional`).

**Remaining hypotheses: none.** (Round 3: `Cite_Helfgott_weighted` via
`Alt.ep1054_Thm_SubexpGrowth_ofHelfgott`, or `Cite_MV_exceptional` via
`Proofs.ep1054_Thm_SubexpGrowth`.) -/
theorem ep1054_Thm_SubexpGrowth_unconditional : Principia.Erdos1054.Thm_SubexpGrowth :=
  Principia.Erdos1054.Rate.thm_SubexpGrowth_unconditional

/-! ## 2. Theorem 1.2 and its inputs, with Luca–Pomerance and Pollack discharged -/

/-- **`lem:LP-inputs`, unconditionally**: Luca–Pomerance Lemmas 2.1, 2.2 (range form) and 2.5,
each now a theorem (`Proofs.input_Cite_LP_Lemma21`, `input_Cite_LP_Lemma22_range`,
`input_Cite_LP_Lemma25`).

**Remaining hypotheses: none.** (Round 3: `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`,
`Cite_LP_Lemma25`.) -/
theorem ep1054_Lem_LPInputs_unconditional : Principia.Erdos1054.Lem_LPInputs :=
  ep1054_Lem_LPInputs input_Cite_LP_Lemma21 input_Cite_LP_Lemma22_range input_Cite_LP_Lemma25

/-- **`lem:sv-regular`, unconditionally**: the three Luca–Pomerance inputs and Pollack's
Theorem 1.4 (`Proofs.input_Cite_Pollack_Thm14`) fed into `Proofs.ep1054_Lem_SvRegular`.

**Remaining hypotheses: none.** (Round 3: the three `Cite_LP_*` and `Cite_Pollack_Thm14`.) -/
theorem ep1054_Lem_SvRegular_unconditional : Principia.Erdos1054.Lem_SvRegular :=
  ep1054_Lem_SvRegular input_Cite_LP_Lemma21 input_Cite_LP_Lemma22_range input_Cite_LP_Lemma25
    input_Cite_Pollack_Thm14

/-- **EP1054 Theorem 1.2 (`thm:small-values`), unconditionally**: `Alt.ep1054_Thm_SmallValues_r3`
(the two-dimensional sieve already discharged) with its four remaining inputs supplied by proofs.

**Remaining hypotheses: none.** (Round 3: `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`,
`Cite_LP_Lemma25`, `Cite_Pollack_Thm14`.) -/
theorem ep1054_Thm_SmallValues_unconditional : Principia.Erdos1054.Thm_SmallValues :=
  Alt.ep1054_Thm_SmallValues_r3 input_Cite_LP_Lemma21 input_Cite_LP_Lemma22_range
    input_Cite_LP_Lemma25 input_Cite_Pollack_Thm14

/-! ## 3. The §6–§7 headlines: tail-only, with Luca–Pomerance and Pollack discharged

The `_of_repDensityOne` forms take `TailOnly.RepDensityOne` (the unrepresented integers have
density zero) in place of Helfgott. They show that Helfgott enters these headlines **only** through
density one of `𝓡`, and `TailOnly.repDensityOne_iff_evenUnrep` shows that is exactly density zero
of the *even* unrepresented integers (the odd half is unconditional). -/

/-- **`prop:tightness-equivalence`** from the representability tail
(`TailOnly.ep1054_Prop_TightnessEquivalence_tailOnly`).

**Remaining hypothesis:** `Cite_Helfgott_weighted`. (Round 3: Helfgott, `Cite_Dusart_Thm69` and
the three `Comp_Verifier_*`.) -/
theorem ep1054_Prop_TightnessEquivalence_r4 (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Principia.Erdos1054.Prop_TightnessEquivalence :=
  TailOnly.ep1054_Prop_TightnessEquivalence_tailOnly i_Cite_Helfgott_weighted

/-- **`thm:dadd:universal-singularity` from density one of `𝓡`**, the four Luca–Pomerance/Pollack
inputs supplied by proofs.

**Hypotheses:** `TailOnly.RepDensityOne` (not a trusted input: an open statement, implied by
`Cite_Helfgott_weighted`) and `Cite_Erdos_singular`. -/
theorem thm_DaddUniversalSingularity_of_repDensityOne_r4 (hD : TailOnly.RepDensityOne)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Principia.Erdos1054.Thm_DaddUniversalSingularity :=
  TailOnly.thm_DaddUniversalSingularity_of_repDensityOne hD input_Cite_LP_Lemma21
    input_Cite_LP_Lemma22_range input_Cite_LP_Lemma25 input_Cite_Pollack_Thm14
    i_Cite_Erdos_singular

/-- **EP1054 `thm:dadd:universal-singularity`.**

**Remaining hypotheses:** `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. (Round 3: those two plus
the three `Cite_LP_*`, `Cite_Pollack_Thm14`, `Cite_Dusart_Thm69` and the three `Comp_Verifier_*`,
ten in all.) -/
theorem ep1054_Thm_DaddUniversalSingularity_r4 (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Principia.Erdos1054.Thm_DaddUniversalSingularity :=
  thm_DaddUniversalSingularity_of_repDensityOne_r4
    (TailOnly.repDensityOne_of_helfgott i_Cite_Helfgott_weighted) i_Cite_Erdos_singular

/-- **The heavy-tail corollary from density one of `𝓡`**, the four Luca–Pomerance/Pollack inputs
supplied by proofs.

**Hypotheses:** `TailOnly.RepDensityOne` and `Cite_Erdos_singular`. -/
theorem cor_DaddHeavyTails_of_repDensityOne_r4 (hD : TailOnly.RepDensityOne)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Principia.Erdos1054.Cor_DaddHeavyTails :=
  TailOnly.cor_DaddHeavyTails_of_repDensityOne hD input_Cite_LP_Lemma21
    input_Cite_LP_Lemma22_range input_Cite_LP_Lemma25 input_Cite_Pollack_Thm14
    i_Cite_Erdos_singular

/-- **EP1054 heavy-tail corollary (`Cor_DaddHeavyTails`).**

**Remaining hypotheses:** `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. (Round 3: ten, as for
`ep1054_Thm_DaddUniversalSingularity_r4`.) -/
theorem ep1054_Cor_DaddHeavyTails_r4 (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Principia.Erdos1054.Cor_DaddHeavyTails :=
  cor_DaddHeavyTails_of_repDensityOne_r4
    (TailOnly.repDensityOne_of_helfgott i_Cite_Helfgott_weighted) i_Cite_Erdos_singular

/-- **`prop:dadd:collision-criterion` from density one of `𝓡`**, the four Luca–Pomerance/Pollack
inputs supplied by proofs.

**Hypotheses:** `TailOnly.RepDensityOne` and `Cite_Erdos_singular`. -/
theorem prop_DaddCollisionCriterion_of_repDensityOne_r4 (hD : TailOnly.RepDensityOne)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Principia.Erdos1054.Prop_DaddCollisionCriterion :=
  TailOnly.prop_DaddCollisionCriterion_of_repDensityOne hD input_Cite_LP_Lemma21
    input_Cite_LP_Lemma22_range input_Cite_LP_Lemma25 input_Cite_Pollack_Thm14
    i_Cite_Erdos_singular

/-- **EP1054 `prop:dadd:collision-criterion`.**

**Remaining hypotheses:** `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. (Round 3: ten, as for
`ep1054_Thm_DaddUniversalSingularity_r4`.) -/
theorem ep1054_Prop_DaddCollisionCriterion_r4 (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Principia.Erdos1054.Prop_DaddCollisionCriterion :=
  prop_DaddCollisionCriterion_of_repDensityOne_r4
    (TailOnly.repDensityOne_of_helfgott i_Cite_Helfgott_weighted) i_Cite_Erdos_singular

/-! ## 4. The whole paper

`ep1054_all_r4` is `Alt.ep1054_all_r3`'s application of `Alt.noMV_EP1054`, generated by
`gen_round4.py` (scratchpad `r4/`) with exactly five edits, each asserted to match once: the four
binders `i_Cite_LP_Lemma21`, `i_Cite_LP_Lemma22_range`, `i_Cite_LP_Lemma25`,
`i_Cite_Pollack_Thm14` deleted and their arguments replaced by the `Proofs.input_*` theorems; and
`h_AOR_Bound` taken from the Goldbach rate (`Rate.lem_AOR_unconditional`) instead of from Helfgott.
So Helfgott reaches the whole-paper proof only through the Fraiture/classification fields, never
through Theorem 1.4 or `Lem_AnalyticOddRepresentability`. -/

set_option maxRecDepth 20000 in
/-- **All of EP1054** (`Spine.DerivedClaims`, every derived statement of the paper) from **8**
trusted inputs.

**Remaining hypotheses (8)** (trusted inputs with no Lean proof), with the fields that need them:
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound. Needed by
  `Lem_FraitureBalancedGoldbach`, `Prop_FraitureTail` and the classification. (This capstone proves
  the §6–§7 fields through the classification, as the spine does; section 3 shows that those
  headlines need only Helfgott's consequence `TailOnly.RepDensityOne`.)
* `Cite_Dusart_Thm69` and `Comp_Verifier_small`, `Comp_Verifier_window1`,
  `Comp_Verifier_largeSeed` (Dusart's explicit `π(x)` bounds and the three finite verifier
  computations): `Prop_FraitureFinite`, hence the exact classification
  `Thm_FraitureRepresentability`, `Eq_ExactRepresentability` and its restatements
  `Intro_RcntFormula`, `Thm_FraitureRepresentability_Ge6` (each equivalent to it:
  `TailOnly.eqExactRepresentability_iff_rcntFormula`, `TailOnly.eqExactRepresentability_iff_ge6`).
* `Cite_Axler_Cor2` (explicit Robin-type bound): `Prop_SmallRatioThreshold`.
* `Cite_ChenZhao` (nonaliquot numbers have lower density `≥ 0.0602757`): `Prop_ThetaTwo`,
  `Cor_EtaTwo`.
* `Cite_Erdos_singular` (the Davenport law of `σ(n)/n` is purely singular):
  `Thm_DaddUniversalSingularity`, `Cor_DaddHeavyTails`, `Prop_DaddCollisionCriterion`.

(Round 3's `Alt.ep1054_all_r3` took these eight plus `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`,
`Cite_LP_Lemma25` and `Cite_Pollack_Thm14`; `Proofs.ep1054_all` took 15.) -/
theorem ep1054_all_r4
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Spine.DerivedClaims :=
  noMV_EP1054
    (L_Std_PNT := link_Std_PNT)
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
    (L_Cite_Davenport := link_Cite_Davenport)
    (L_Intro_LiminfZero := link_Intro_LiminfZero)
    (L_Fact_KmodFinite := link_Fact_KmodFinite)
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Rem_RoughInputModulus := link_Rem_RoughInputModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Lem_SigmaRate_OddPrime := link_Lem_SigmaRate_OddPrime)
    (L_Lem_SigmaRate_B2 := link_Lem_SigmaRate_B2)
    (L_Lem_Moment := link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_FraitureSmall := link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover := link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow := link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover := link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum := link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow := link_Eq_FraitureLargeWindow)
    (L_Step_FraitureTailEven := link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd := link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail := link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability := link_Thm_FraitureRepresentability)
    (L_Intro_RcntFormula := link_Intro_RcntFormula)
    (L_Thm_FraitureRepresentability_Ge6 := link_Thm_FraitureRepresentability_Ge6)
    (L_KovacMoment_identity := link_KovacMoment_identity)
    (L_KovacMoment_reduction := link_KovacMoment_reduction)
    (L_Eq_KSprime := link_Eq_KSprime)
    (L_Eq_KSsecond := link_Eq_KSsecond)
    (L_Eq_KS := link_Eq_KS)
    (L_Lem_KovacMoment := link_Lem_KovacMoment)
    (L_SmallUpper_momentStep := link_SmallUpper_momentStep)
    (L_Thm_SmallUpper_doubleExp := link_Thm_SmallUpper_doubleExp)
    (L_Thm_SmallUpper_fixedPower := link_Thm_SmallUpper_fixedPower)
    (L_Thm_SmallUpper_upperDens := link_Thm_SmallUpper_upperDens)
    (L_Intro_LittleO_onlyOnDensityZero := link_Intro_LittleO_onlyOnDensityZero)
    (L_Prop_SmallRatioThreshold := link_Prop_SmallRatioThreshold)
    (L_Rem_Lcm289Witness := link_Rem_Lcm289Witness)
    (L_Eq_SvTwoSided := link_Eq_SvTwoSided)
    (L_SvA0_jSum := link_SvA0_jSum)
    (L_Lem_SvA0Count := link_Lem_SvA0Count)
    (L_Eq_SmoothPartPeriodCount := link_Eq_SmoothPartPeriodCount)
    (L_Lem_SmoothPartInput := link_Lem_SmoothPartInput)
    (L_Lem_SvRegular := link_Lem_SvRegular)
    (L_Lem_SvClasses := link_Lem_SvClasses)
    (L_Eq_SvKReciprocal := link_Eq_SvKReciprocal)
    (L_Eq_SvMReciprocal := link_Eq_SvMReciprocal)
    (L_Claim_SvSigmaDistinct := link_Claim_SvSigmaDistinct)
    (L_Claim_SvSievePairs := link_Claim_SvSievePairs)
    (L_Eq_SvTotient := link_Eq_SvTotient)
    (L_Claim_SvA3Reduction := link_Claim_SvA3Reduction)
    (L_Claim_SvLargeHUnits := link_Claim_SvLargeHUnits)
    (L_Eq_SvLargeHCongruence := link_Eq_SvLargeHCongruence)
    (L_Claim_SvLargeHRigidity := link_Claim_SvLargeHRigidity)
    (L_Claim_SvLargeH := link_Claim_SvLargeH)
    (L_Claim_SvA322Reduction := link_Claim_SvA322Reduction)
    (L_Claim_SvSmallHResidues := link_Claim_SvSmallHResidues)
    (L_Eq_SvIntermediateTotient := link_Eq_SvIntermediateTotient)
    (L_Eq_SvFSum := link_Eq_SvFSum)
    (L_Eq_SvQRSum := link_Eq_SvQRSum)
    (L_Claim_SvSmallH := link_Claim_SvSmallH)
    (L_Eq_SvReducedCollisionSum := link_Eq_SvReducedCollisionSum)
    (L_Prop_SvSecondMoment := link_Prop_SvSecondMoment)
    (L_Claim_SvClassImage := link_Claim_SvClassImage)
    (L_Claim_SvImageCount := link_Claim_SvImageCount)
    (L_Claim_SvWitness := link_Claim_SvWitness)
    (L_SvFamilyTarget := link_SvFamilyTarget)
    (L_Thm_SmallValues := link_Thm_SmallValues)
    (L_Thm_SmallValues_upperDens := link_Thm_SmallValues_upperDens)
    (L_Thm_SmallValues_lowerDens := link_Thm_SmallValues_lowerDens)
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
    (L_Eq_MovingKernelTail := link_Eq_MovingKernelTail)
    (L_UpperTails_Claim_KA_finite := link_UpperTails_Claim_KA_finite)
    (L_UpperTails_Claim_VA_periodic := link_UpperTails_Claim_VA_periodic)
    (L_UpperTails_Claim_VA_density := link_UpperTails_Claim_VA_density)
    (L_Prop_FmEnvelope := link_Prop_FmEnvelope)
    (L_UpperTails_Claim_DeltaPfix := link_UpperTails_Claim_DeltaPfix)
    (L_UpperTails_Claim_RoughNotVA := link_UpperTails_Claim_RoughNotVA)
    (L_Cor_FmEnvelopeTail := link_Cor_FmEnvelopeTail)
    (L_UpperTails_Claim_AlmostLogTail_main := link_UpperTails_Claim_AlmostLogTail_main)
    (L_UpperTails_Claim_AlmostLogTail_fixedJ := link_UpperTails_Claim_AlmostLogTail_fixedJ)
    (L_Eq_AlmostLogTail := link_Eq_AlmostLogTail)
    (L_Thm_AlmostLogTail_posLowerDens := link_Thm_AlmostLogTail_posLowerDens)
    (L_Thm_AlmostLogTail_limsup := link_Thm_AlmostLogTail_limsup)
    (L_Intro_ErdosLittleO_fails := link_Intro_ErdosLittleO_fails)
    (L_Intro_ErdosAlmostAllLittleO_fails := link_Intro_ErdosAlmostAllLittleO_fails)
    (L_Eq_SharpRoughTargetCount := link_Eq_SharpRoughTargetCount)
    (L_Eq_SharpBadSourceCount := link_Eq_SharpBadSourceCount)
    (L_UpperTails_Claim_SubexpBadPairs := link_UpperTails_Claim_SubexpBadPairs)
    (L_UpperTails_Claim_SubexpWitnessStructure := link_UpperTails_Claim_SubexpWitnessStructure)
    (L_Eq_MovingKernelLowerBound := link_Eq_MovingKernelLowerBound)
    (L_UpperTails_Claim_SubexpCoprimeCount := link_UpperTails_Claim_SubexpCoprimeCount)
    (L_UpperTails_Claim_SubexpLowCofactorSum := link_UpperTails_Claim_SubexpLowCofactorSum)
    (L_UpperTails_Claim_SubexpLowCofactor := link_UpperTails_Claim_SubexpLowCofactor)
    (L_UpperTails_Claim_SubexpLargeCofactor := link_UpperTails_Claim_SubexpLargeCofactor)
    (L_UpperTails_Claim_SubexpCore := link_UpperTails_Claim_SubexpCore)
    (L_UpperTails_Claim_SubexpThreshold := link_UpperTails_Claim_SubexpThreshold)
    (L_Eq_SubexpGrowth := link_Eq_SubexpGrowth)
    (L_Eq_PositiveMomentGrowth := link_Eq_PositiveMomentGrowth)
    (L_Eq_He := link_Eq_He)
    (L_Coverage_Step_ClassResidue := link_Coverage_Step_ClassResidue)
    (L_Eq_RepresentingRatio := link_Eq_RepresentingRatio)
    (L_Coverage_Disp_HeMean := link_Coverage_Disp_HeMean)
    (L_Coverage_Step_GeLowerDens := link_Coverage_Step_GeLowerDens)
    (L_Eq_ClassLower := link_Eq_ClassLower)
    (L_Coverage_Disp_MertensCoprimeQ := link_Coverage_Disp_MertensCoprimeQ)
    (L_Coverage_Disp_ClassPrimeSum := link_Coverage_Disp_ClassPrimeSum)
    (L_Prop_ClassFirstMoment_bound := link_Prop_ClassFirstMoment_bound)
    (L_Prop_ClassFirstMoment_tendsto := link_Prop_ClassFirstMoment_tendsto)
    (L_Cor_FmPrimeCeiling_congr := link_Cor_FmPrimeCeiling_congr)
    (L_Cor_FmPrimeCeiling_count := link_Cor_FmPrimeCeiling_count)
    (L_Cor_FmPrimeCeiling_upperDens := link_Cor_FmPrimeCeiling_upperDens)
    (L_Coverage_Rem_SqfreeDefectPos := link_Coverage_Rem_SqfreeDefectPos)
    (L_Cor_FixedCofactorDefect_pos := link_Cor_FixedCofactorDefect_pos)
    (L_Eq_FixedCofactorDefect := link_Eq_FixedCofactorDefect)
    (L_Coverage_Step_KmodSmallPrime := link_Coverage_Step_KmodSmallPrime)
    (L_Coverage_Step_GcovValuesSmallPrime := link_Coverage_Step_GcovValuesSmallPrime)
    (L_Coverage_Fact_GcovCoprimeNull := link_Coverage_Fact_GcovCoprimeNull)
    (L_Coverage_Fact_CoprimeComplementDens := link_Coverage_Fact_CoprimeComplementDens)
    (L_Eq_BoundedCofactorComplement := link_Eq_BoundedCofactorComplement)
    (L_Coverage_Disp_LogPA := link_Coverage_Disp_LogPA)
    (L_Eq_DeltaAAsymptotic := link_Eq_DeltaAAsymptotic)
    (L_Prop_EtaALower_bound := link_Prop_EtaALower_bound)
    (L_Prop_EtaALower_tendsto := link_Prop_EtaALower_tendsto)
    (L_Coverage_Rem_EtaDominates := link_Coverage_Rem_EtaDominates)
    (L_Eq_F2OddNegligible := link_Eq_F2OddNegligible)
    (L_Coverage_Step_EvenUntouchables := link_Coverage_Step_EvenUntouchables)
    (L_Coverage_Disp_F2Count := link_Coverage_Disp_F2Count)
    (L_Prop_ThetaTwo := link_Prop_ThetaTwo)
    (L_Coverage_Step_UpperDensG2 := link_Coverage_Step_UpperDensG2)
    (L_Cor_EtaTwo := link_Cor_EtaTwo)
    (L_Coverage_Rem_ConjEquivEta := link_Coverage_Rem_ConjEquivEta)
    (L_Coverage_Rem_RoughPartBound := link_Coverage_Rem_RoughPartBound)
    (L_Coverage_Rem_ConjEquivSmallPrimePart := link_Coverage_Rem_ConjEquivSmallPrimePart)
    (L_Coverage_Disp_TailLeCompl := link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail := link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence := link_Prop_TightnessEquivalence)
    (L_Coverage_Rem_T_iff_Conj := link_Coverage_Rem_T_iff_Conj)
    (L_Fact_DaddDavenportLaw := link_Fact_DaddDavenportLaw)
    (L_Fact_DaddProgressionLaws := link_Fact_DaddProgressionLaws)
    (L_Eq_DaddProgressionDomination := link_Eq_DaddProgressionDomination)
    (L_Step_DaddWitnessIdentity := link_Step_DaddWitnessIdentity)
    (L_Step_DaddWitnessJointLimit := link_Step_DaddWitnessJointLimit)
    (L_Step_DaddWitnessSupport := link_Step_DaddWitnessSupport)
    (L_Step_DaddWitnessCount := link_Step_DaddWitnessCount)
    (L_Step_DaddWitnessCofactorTail := link_Step_DaddWitnessCofactorTail)
    (L_Step_DaddWitnessPieceBounds := link_Step_DaddWitnessPieceBounds)
    (L_Prop_DaddWitnessMeans := link_Prop_DaddWitnessMeans)
    (L_Rem_DaddWitnessMeanGrowth := link_Rem_DaddWitnessMeanGrowth)
    (L_Step_DaddSingularCarrier := link_Step_DaddSingularCarrier)
    (L_Step_DaddWitnessMeasureMass := link_Step_DaddWitnessMeasureMass)
    (L_Step_DaddWitnessCarrier := link_Step_DaddWitnessCarrier)
    (L_Step_DaddEmpiricalWitnessVague := link_Step_DaddEmpiricalWitnessVague)
    (L_Step_DaddLimitDomination := link_Step_DaddLimitDomination)
    (L_Thm_DaddUniversalSingularity_Carrier := link_Thm_DaddUniversalSingularity_Carrier)
    (L_Thm_DaddUniversalSingularity_FinitePart := link_Thm_DaddUniversalSingularity_FinitePart)
    (L_Thm_DaddUniversalSingularity_Tight := link_Thm_DaddUniversalSingularity_Tight)
    (L_Step_DaddXoverR := link_Step_DaddXoverR)
    (L_Step_DaddLowerTailUniform := link_Step_DaddLowerTailUniform)
    (L_Eq_DaddSubsequentialTail := link_Eq_DaddSubsequentialTail)
    (L_Cor_DaddHeavyTails_PosMoments := link_Cor_DaddHeavyTails_PosMoments)
    (L_Cor_DaddHeavyTails_LogMeans := link_Cor_DaddHeavyTails_LogMeans)
    (L_Cor_DaddHeavyTails_InvMoments := link_Cor_DaddHeavyTails_InvMoments)
    (L_Cor_DaddHeavyTails_InvMomentConv := link_Cor_DaddHeavyTails_InvMomentConv)
    (L_Cor_DaddHeavyTails_GeomMean := link_Cor_DaddHeavyTails_GeomMean)
    (L_Cor_DaddHeavyTails_Tight := link_Cor_DaddHeavyTails_Tight)
    (L_Step_DaddCollisionSupport := link_Step_DaddCollisionSupport)
    (L_Eq_DaddCollisionCriterion := link_Eq_DaddCollisionCriterion)
    (L_Prop_DaddCollisionCriterion := link_Prop_DaddCollisionCriterion)
    (L_Step_DaddCollisionWitness := link_Step_DaddCollisionWitness)
    (L_Step_DaddCollisionFirstMoment := link_Step_DaddCollisionFirstMoment)
    (L_Step_DaddCollisionFirstMomentLaw := link_Step_DaddCollisionFirstMomentLaw)
    (L_Step_DaddCollisionSourceIntensity := link_Step_DaddCollisionSourceIntensity)
    (L_Step_DaddCollisionCylinder := link_Step_DaddCollisionCylinder)
    (L_Step_DaddCollisionPerCore := link_Step_DaddCollisionPerCore)
    (L_Step_DaddCollisionCombine := link_Step_DaddCollisionCombine)
    (L_Step_DaddCollisionExplicit := link_Step_DaddCollisionExplicit)
    (L_Prop_DaddCollisionLowerBound := link_Prop_DaddCollisionLowerBound)
    (hL := {
      c_Std_Mertens1 := leaf_Std_Mertens1,
      c_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges,
      c_EmpiricalMeasures_isProbability := leaf_EmpiricalMeasures_isProbability,
      c_Intro_f_sigma_le := leaf_Intro_f_sigma_le,
      c_Notation_Delta_density := leaf_Notation_Delta_density,
      c_Notation_sigmaPrefix_zero := leaf_Notation_sigmaPrefix_zero,
      c_Disp_FinalDivisor := leaf_Disp_FinalDivisor,
      c_Eq_Reflection := leaf_Eq_Reflection,
      c_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo,
      c_Fact_DsetResidue := leaf_Fact_DsetResidue,
      c_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow,
      c_Lem_FraitureExtension := leaf_Lem_FraitureExtension,
      c_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq,
      c_Step_FraitureSeven := leaf_Step_FraitureSeven,
      c_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes,
      c_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes,
      c_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases,
      c_KovacMoment_reflection := leaf_KovacMoment_reflection,
      c_KovacS_le_S1S2 := leaf_KovacS_le_S1S2,
      c_SmallUpper_emptyCase := leaf_SmallUpper_emptyCase,
      c_SmallUpper_markov := leaf_SmallUpper_markov,
      c_SmallUpper_paramChoice := leaf_SmallUpper_paramChoice,
      c_SmallUpper_doubleExpPower := leaf_SmallUpper_doubleExpPower,
      c_SmallRatio_prefixLeSig := leaf_SmallRatio_prefixLeSig,
      c_SmallRatio_abundancySmall := leaf_SmallRatio_abundancySmall,
      c_SmallRatio_axlerNumeric := leaf_SmallRatio_axlerNumeric,
      c_Rem_Lcm289Abundant := leaf_Rem_Lcm289Abundant,
      c_Rem_Lcm289Values := leaf_Rem_Lcm289Values,
      c_Eq_SvBasic := leaf_Eq_SvBasic,
      c_Eq_SvD := leaf_Eq_SvD,
      c_Lem_SvA0Unique := leaf_Lem_SvA0Unique,
      c_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge,
      c_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic,
      c_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul,
      c_Eq_SvHarmonicDensityZero := leaf_Eq_SvHarmonicDensityZero,
      c_Eq_SvCollision := leaf_Eq_SvCollision,
      c_Claim_SvSmallHSquarefree := leaf_Claim_SvSmallHSquarefree,
      c_Claim_SvResiduePairCount := leaf_Claim_SvResiduePairCount,
      c_Claim_SvCauchySchwarz := leaf_Claim_SvCauchySchwarz,
      c_Eq_RankinKernel := leaf_Eq_RankinKernel,
      c_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms,
      c_UpperTails_Claim_VA_rough := leaf_UpperTails_Claim_VA_rough,
      c_UpperTails_Claim_AlmostLogTail_momentArith :=
        leaf_UpperTails_Claim_AlmostLogTail_momentArith,
      c_UpperTails_Claim_RoughNonsquarefree := leaf_UpperTails_Claim_RoughNonsquarefree,
      c_UpperTails_Claim_LscaleRatio := leaf_UpperTails_Claim_LscaleRatio,
      c_UpperTails_Claim_SubexpFltP := leaf_UpperTails_Claim_SubexpFltP,
      c_UpperTails_Claim_SubexpCofactorOne := leaf_UpperTails_Claim_SubexpCofactorOne,
      c_UpperTails_Claim_SubexpLogT := leaf_UpperTails_Claim_SubexpLogT,
      c_Coverage_Fact_RtPairs := leaf_Coverage_Fact_RtPairs,
      c_Coverage_Fact_RtPosIff := leaf_Coverage_Fact_RtPosIff,
      c_Eq_HGcd := leaf_Eq_HGcd,
      c_Eq_UClass := leaf_Eq_UClass,
      c_Coverage_Step_SeDensity := leaf_Coverage_Step_SeDensity,
      c_Coverage_Step_HeRatio := leaf_Coverage_Step_HeRatio,
      c_Coverage_Step_SeMultiplesDens := leaf_Coverage_Step_SeMultiplesDens,
      c_Coverage_Disp_CoprimeSqTail := leaf_Coverage_Disp_CoprimeSqTail,
      c_Coverage_Step_DistinctPairs := leaf_Coverage_Step_DistinctPairs,
      c_Coverage_Fact_GcovSubsetRtPos := leaf_Coverage_Fact_GcovSubsetRtPos,
      c_Eq_F2Aliquot := leaf_Eq_F2Aliquot,
      c_Coverage_Step_G2Decomp := leaf_Coverage_Step_G2Decomp,
      c_Coverage_Step_P2Values := leaf_Coverage_Step_P2Values,
      c_Coverage_Fact_UpperDensCompl := leaf_Coverage_Fact_UpperDensCompl,
      c_Step_DaddWitnessDomination := leaf_Step_DaddWitnessDomination,
      c_Step_DaddCountDomination := leaf_Step_DaddCountDomination,
      c_Eq_DaddCollisionAffine := leaf_Eq_DaddCollisionAffine,
      c_Step_DaddCollisionCores := leaf_Step_DaddCollisionCores,
      c_Step_DaddCollisionH := leaf_Step_DaddCollisionH,
      c_Step_DaddCollisionArithmetic := leaf_Step_DaddCollisionArithmetic
    })
    (i_Cite_Pollack_Lemma24 := input_Cite_Pollack_Lemma24)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Std_SiegelWalfisz_dyadic := input_Std_SiegelWalfisz_dyadic)
    (i_Std_BrunTitchmarsh := input_Std_BrunTitchmarsh)
    (i_Std_divisorBound := input_Std_divisorBound)
    (i_Std_sigma_odd_iff := input_Std_sigma_odd_iff)
    (i_Std_totient_sigma := input_Std_totient_sigma)
    (h_AOR_Bound := Principia.Erdos1054.Rate.lem_AOR_unconditional.1)
    (h_OddUntouchables := eq_OddUntouchables_unconditional)
    (i_Cite_LP_Lemma21 := input_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := input_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := input_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := input_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := input_Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 := i_Cite_Axler_Cor2)
    (i_Cite_ChenZhao := i_Cite_ChenZhao)
    (i_Cite_PollackAP := input_Cite_PollackAP)
    (i_Cite_Erdos_singular := i_Cite_Erdos_singular)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

end Principia.Erdos1054.Alt.Round4
