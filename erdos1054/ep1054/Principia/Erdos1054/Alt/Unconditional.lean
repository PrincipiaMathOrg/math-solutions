/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.Unconditional
import Principia.Erdos1054.CircleMethod.Bridge
import Principia.Erdos1054.Proofs.InputsLPSieve
import Principia.Erdos1054.Proofs.InputsDavenport
import Principia.Erdos1054.Rate.Routes

set_option autoImplicit false

/-!
# EP1054 headlines after round 3: what the new discharges buy

Round 3 landed four discharges, each a theorem of this library with footprint
`[propext, Classical.choice, Quot.sound]`:

* `Principia.Common.SW.mediumPNTBound : MediumPNTBound` — the explicit prime number theorem
  `|ψ(x) − x| ≤ C·x·exp(−c (log x)^{1/10})`, from the ported PNT+ `MediumPNT`
  (`Principia/Common/PNT/Medium/`);
* `Principia.Erdos1054.CircleMethod.std_GoldbachDensZero_of_mediumPNT` — almost all even numbers are
  sums of two primes, from `MediumPNTBound`, through the ported circle method
  (`Principia/Common/Goldbach/`);
* `Principia.Erdos1054.Proofs.input_Cite_LP_sieve37 : Cite_LP_sieve37` — the two-dimensional
  upper-bound sieve (`Principia/Common/Sieve/TwoDim.lean`);
* `Principia.Erdos1054.Proofs.input_Cite_PollackAP : Cite_PollackAP` — Davenport's theorem in
  progressions (`Principia/Common/Davenport/`).

This module feeds them into the paper's headlines. Every theorem here states a headline `Prop` of
`Principia.Erdos1054` exactly as the spine does; its hypotheses (listed in each docstring) are the
trusted inputs it still needs, and **none** means it is an unconditional theorem of the library.

`Cite_MV_exceptional` (Montgomery–Vaughan) is needed by **no** theorem of this module. It
entered the spine through exactly two link applications, and both now have replacements:

* `Link_Eq_OddUntouchables` (`MV → Eq_OddUntouchables`): `Eq_OddUntouchables` is a density-zero
  statement, and `Rate.eq_OddUntouchables_of_goldbachDensZero` proves it from Goldbach density zero,
  which is now unconditional (`eq_OddUntouchables_unconditional`).
* `Link_Lem_AnalyticOddRepresentability_Bound` (`MV → Lem_AnalyticOddRepresentability_Bound`): the
  bound is a *rate*, which density zero does not give. Its consumers split. Theorem 1.3 and
  everything downstream of `Eq_AlmostLogTail` use it only as density zero of the odd unrepresented
  integers (`Alt.GoldbachRoute`), so they become unconditional. `Lem_AnalyticOddRepresentability`
  itself and Theorem 1.4 need the rate; here it comes from `Prop_FraitureTail` (every
  `n ≥ 10^27 + 10^8` is represented, so the odd unrepresented set is finite), i.e. from
  `Cite_Helfgott_weighted` (`Rate.lemAOR_of_fraitureTail`). That is a trade for those two
  headlines, but `ep1054_all` already carries Helfgott, so for the whole paper it removes MV
  outright.

`noMV_EP1054` is `Assembly.noRS_EP1054` (the whole-paper composition) with those two link
applications replaced by hypotheses of their conclusions. It is generated mechanically from
`Proofs/Assembly.lean` (`gen_unconditional.py`: three binder deletions and two application
replacements, each asserted to match exactly once); regenerate rather than hand-edit.
-/

namespace Principia.Erdos1054.Alt

open Principia.Erdos1054 Principia.Erdos1054.Spine Principia.Erdos1054.Proofs

/-! ## 1. The Goldbach input, unconditionally -/

/-- **Almost every even number is a sum of two primes** (the master's own form: rational `ε`,
count over `0 ≤ n ≤ X`), with no hypothesis: the ported circle method
(`GoldbachReduction.almost_all_binary_goldbach_of_mediumPNT`) applied to the ported explicit prime
number theorem (`Principia.Common.SW.mediumPNTBound`). -/
theorem almost_all_binary_goldbach_unconditional :
    Principia.Common.Goldbach.GoldbachReduction.DensityZero
      Principia.Common.Goldbach.GoldbachReduction.notSumOfTwoPrimes :=
  Principia.Common.Goldbach.GoldbachReduction.almost_all_binary_goldbach_of_mediumPNT
    Principia.Common.SW.mediumPNTBound

/-- **`Std_GoldbachDensZero`, unconditionally**: the even numbers that are not a sum of two primes
have density zero (`Defs.DensZero`). -/
theorem std_GoldbachDensZero_unconditional : Std_GoldbachDensZero :=
  Principia.Erdos1054.CircleMethod.std_GoldbachDensZero_of_mediumPNT
    Principia.Common.SW.mediumPNTBound

/-- **`eq:odd-untouchables`, unconditionally** (`Eq_OddUntouchables`: the odd untouchable numbers
have density zero). The spine takes it from `Cite_MV_exceptional`; the statement needs only
Goldbach density zero (`Rate.eq_OddUntouchables_of_goldbachDensZero`). -/
theorem eq_OddUntouchables_unconditional : Eq_OddUntouchables :=
  Principia.Erdos1054.Rate.eq_OddUntouchables_of_goldbachDensZero
    std_GoldbachDensZero_unconditional

/-- `Eq_BoundedCofactorComplement` (`eq:bounded-cofactor-complement`), composed exactly as
`Spine.spine_Prop_EtaALower` composes it, from proved links and leaves only. It is shared by
`ep1054_Prop_EtaALower_unconditional` and `ep1054_Cor_EtaTwo_r3`.

**Remaining hypotheses: none.** -/
theorem eq_BoundedCofactorComplement_unconditional : Eq_BoundedCofactorComplement :=
  have v_Fact_KmodFinite : Fact_KmodFinite := link_Fact_KmodFinite leaf_Fact_DsetResidue
  have v_Lem_FmModulus : Lem_FmModulus := link_Lem_FmModulus leaf_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality :=
    link_Lem_FixedModulusNormality leaf_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero :=
    link_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_KmodSmallPrime : Coverage.Step_KmodSmallPrime :=
    link_Coverage_Step_KmodSmallPrime leaf_Fact_KmodGeTwo
  have v_GcovValuesSmallPrime : Coverage.Step_GcovValuesSmallPrime :=
    link_Coverage_Step_GcovValuesSmallPrime v_KmodSmallPrime v_Fact_KmodFinite v_Lem_FmModulus
      v_Lem_FixedModulusNormality
  have v_GcovCoprimeNull : Coverage.Fact_GcovCoprimeNull :=
    link_Coverage_Fact_GcovCoprimeNull v_GcovValuesSmallPrime v_Lem_SigmaRangeZero
  have v_CoprimeComplementDens : Coverage.Fact_CoprimeComplementDens :=
    link_Coverage_Fact_CoprimeComplementDens v_GcovCoprimeNull leaf_Notation_Delta_density
  link_Eq_BoundedCofactorComplement v_CoprimeComplementDens leaf_Coverage_Fact_UpperDensCompl

/-! ## 2. Theorem 1.3 and the §6 coverage results -/

/-- **EP1054 Theorem 1.3 (`thm:almost-log-tail`), unconditionally**: the main display and both
consequences, from `Alt.thm_AlmostLogTail_of_goldbachDensZero` and the unconditional Goldbach
input.

**Remaining hypotheses: none.** (The spine's version, `Proofs.ep1054_Thm_AlmostLogTail`, takes
`Cite_MV_exceptional`.) -/
theorem ep1054_Thm_AlmostLogTail_unconditional : Principia.Erdos1054.Thm_AlmostLogTail :=
  thm_AlmostLogTail_of_goldbachDensZero std_GoldbachDensZero_unconditional

/-- **The fixed-cofactor corollary (`Cor_FixedCofactorDefect`), unconditionally**, from
`Alt.cor_FixedCofactorDefect_of_goldbachDensZero`.

**Remaining hypotheses: none.** (Spine version: `Cite_MV_exceptional`.) -/
theorem ep1054_Cor_FixedCofactorDefect_unconditional :
    Principia.Erdos1054.Cor_FixedCofactorDefect :=
  cor_FixedCofactorDefect_of_goldbachDensZero std_GoldbachDensZero_unconditional

/-- **The `η_A` lower bound (`Prop_EtaALower`), unconditionally.** The composition is
`Spine.spine_Prop_EtaALower`'s: `Cite_MV_exceptional` entered it only through `Eq_AlmostLogTail`
(via `Eq_FixedCofactorDefect`), which now comes from `Alt.eq_AlmostLogTail_of_goldbachDensZero`.

**Remaining hypotheses: none.** (Spine version: `Cite_MV_exceptional`.) -/
theorem ep1054_Prop_EtaALower_unconditional : Prop_EtaALower :=
  have v_Std_PNT : Std_PNT := link_Std_PNT InputsPNT.input_Std_PNT_AP
  have v_Eq_FixedCofactorDefect : Eq_FixedCofactorDefect :=
    link_Eq_FixedCofactorDefect
      (eq_AlmostLogTail_of_goldbachDensZero std_GoldbachDensZero_unconditional)
  have v_Coverage_Disp_LogPA : Coverage.Disp_LogPA := link_Coverage_Disp_LogPA v_Std_PNT
  have v_Eq_DeltaAAsymptotic : Eq_DeltaAAsymptotic :=
    link_Eq_DeltaAAsymptotic v_Coverage_Disp_LogPA input_Std_Mertens3
  have v_Prop_EtaALower_bound : Prop_EtaALower_bound :=
    link_Prop_EtaALower_bound v_Eq_FixedCofactorDefect leaf_Coverage_Fact_UpperDensCompl
      v_Eq_DeltaAAsymptotic eq_BoundedCofactorComplement_unconditional
  And.intro v_Prop_EtaALower_bound (link_Prop_EtaALower_tendsto v_Prop_EtaALower_bound)

/-- **`prop:theta-two` (`Prop_ThetaTwo`) without Montgomery–Vaughan.** The composition is
`Spine.spine_Prop_ThetaTwo`'s with `Eq_OddUntouchables` from `eq_OddUntouchables_unconditional`.

**Remaining hypothesis:** `Cite_ChenZhao` (the nonaliquot numbers have lower density
`≥ 0.0602757`). (Spine version: `Cite_MV_exceptional`, `Cite_ChenZhao`.) -/
theorem ep1054_Prop_ThetaTwo_r3 (i_Cite_ChenZhao : Cite_ChenZhao) : Prop_ThetaTwo :=
  have v_Eq_F2OddNegligible : Eq_F2OddNegligible :=
    link_Eq_F2OddNegligible leaf_Eq_F2Aliquot input_Std_sigma_odd_iff
  have v_Coverage_Step_EvenUntouchables : Coverage.Step_EvenUntouchables :=
    link_Coverage_Step_EvenUntouchables eq_OddUntouchables_unconditional i_Cite_ChenZhao
  have v_Coverage_Disp_F2Count : Coverage.Disp_F2Count :=
    link_Coverage_Disp_F2Count leaf_Eq_F2Aliquot v_Eq_F2OddNegligible
      v_Coverage_Step_EvenUntouchables
  link_Prop_ThetaTwo v_Coverage_Disp_F2Count

/-- **The `η_2` corollary (`Cor_EtaTwo`) without Montgomery–Vaughan.** The composition is
`Spine.spine_Cor_EtaTwo`'s, with `Prop_ThetaTwo` from `ep1054_Prop_ThetaTwo_r3`.

**Remaining hypothesis:** `Cite_ChenZhao`. (Spine version: `Cite_MV_exceptional`,
`Cite_ChenZhao`.) -/
theorem ep1054_Cor_EtaTwo_r3 (i_Cite_ChenZhao : Cite_ChenZhao) : Cor_EtaTwo :=
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero :=
    link_Lem_SigmaRangeZero (link_Lem_FixedModulusNormality leaf_Std_recipPrimesAP_diverges)
  have v_Coverage_Step_UpperDensG2 : Coverage.Step_UpperDensG2 :=
    link_Coverage_Step_UpperDensG2 leaf_Coverage_Step_G2Decomp v_Lem_SigmaRangeZero
  link_Cor_EtaTwo eq_BoundedCofactorComplement_unconditional leaf_Coverage_Step_P2Values
    v_Coverage_Step_UpperDensG2 (ep1054_Prop_ThetaTwo_r3 i_Cite_ChenZhao)

/-! ## 3. `Lem_AnalyticOddRepresentability` and Theorem 1.4: the Helfgott trade -/

/-- **`lem:analytic-odd-representability` (both halves) from Helfgott.** `Prop_FraitureTail`
(every `n ≥ 10^27 + 10^8` is represented, `Proofs.ep1054_Prop_FraitureTail`) makes the odd
unrepresented set finite (`Rate.lemAOR_of_fraitureTail`).

**Remaining hypothesis:** `Cite_Helfgott_weighted`. This trades `Cite_MV_exceptional` (the spine's
version, `Proofs.ep1054_Lem_AnalyticOddRepresentability`) for Helfgott; it discharges nothing on
its own. -/
theorem lemAOR_ofHelfgott (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Lem_AnalyticOddRepresentability :=
  Principia.Erdos1054.Rate.lemAOR_of_fraitureTail
    (ep1054_Prop_FraitureTail i_Cite_Helfgott_weighted)

/-- **EP1054 Theorem 1.4 (`thm:subexp-growth`) from Helfgott**, through
`Rate.thm_SubexpGrowth_of_helfgott`.

**Remaining hypothesis:** `Cite_Helfgott_weighted`. A trade, not a discharge: the spine's version
(`Proofs.ep1054_Thm_SubexpGrowth`) takes `Cite_MV_exceptional` instead. Removing every citation from
Theorem 1.4 needs a *rate* for the Goldbach exceptional set (`Rate.Std_GoldbachRate`,
`O(X / log X)`; plan in `Campaigns/Erdos-1054/THM14-RATE-PLAN.md`). -/
theorem ep1054_Thm_SubexpGrowth_ofHelfgott (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Thm_SubexpGrowth :=
  Principia.Erdos1054.Rate.thm_SubexpGrowth_of_helfgott i_Cite_Helfgott_weighted

/-! ## 4. The small-values and §7 headlines with the sieve and Davenport discharged -/

/-- **`Prop_SvSecondMoment`, unconditionally**: its one remaining input, `Cite_LP_sieve37`, is now
`Proofs.input_Cite_LP_sieve37`.

**Remaining hypotheses: none.** -/
theorem ep1054_Prop_SvSecondMoment_unconditional : Prop_SvSecondMoment :=
  ep1054_Prop_SvSecondMoment input_Cite_LP_sieve37

/-- **EP1054 Theorem 1.2 (`thm:small-values`)** with `Cite_LP_sieve37` discharged.

**Remaining hypotheses:** `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25` (Luca–
Pomerance Lemmas 2.1, 2.2 range form, 2.5) and `Cite_Pollack_Thm14` (Pollack Theorem 1.4). -/
theorem ep1054_Thm_SmallValues_r3
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14) :
    Thm_SmallValues :=
  ep1054_Thm_SmallValues i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25
    input_Cite_LP_sieve37 i_Cite_Pollack_Thm14

/-- **`Prop_DaddWitnessMeans`, unconditionally**: its one remaining input, `Cite_PollackAP`, is now
`Proofs.input_Cite_PollackAP`.

**Remaining hypotheses: none.** -/
theorem ep1054_Prop_DaddWitnessMeans_unconditional : Prop_DaddWitnessMeans :=
  ep1054_Prop_DaddWitnessMeans input_Cite_PollackAP

/-- **`Prop_DaddCollisionLowerBound`, unconditionally**: its one remaining input,
`Cite_PollackAP`, is now `Proofs.input_Cite_PollackAP`.

**Remaining hypotheses: none.** -/
theorem ep1054_Prop_DaddCollisionLowerBound_unconditional : Prop_DaddCollisionLowerBound :=
  ep1054_Prop_DaddCollisionLowerBound input_Cite_PollackAP

/-- **`thm:dadd:universal-singularity`** with `Cite_LP_sieve37` and `Cite_PollackAP` discharged.

**Remaining hypotheses:** `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`,
`Cite_Pollack_Thm14`, `Cite_Helfgott_weighted`, `Cite_Dusart_Thm69`, `Cite_Erdos_singular`,
`Comp_Verifier_small`, `Comp_Verifier_window1`, `Comp_Verifier_largeSeed`. -/
theorem ep1054_Thm_DaddUniversalSingularity_r3
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Thm_DaddUniversalSingularity :=
  ep1054_Thm_DaddUniversalSingularity i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range
    i_Cite_LP_Lemma25 input_Cite_LP_sieve37 i_Cite_Pollack_Thm14 i_Cite_Helfgott_weighted
    i_Cite_Dusart_Thm69 input_Cite_PollackAP i_Cite_Erdos_singular i_Comp_Verifier_small
    i_Comp_Verifier_window1 i_Comp_Verifier_largeSeed

/-- **`prop:dadd:collision-criterion`** with `Cite_LP_sieve37` and `Cite_PollackAP` discharged.

**Remaining hypotheses:** the same ten as `ep1054_Thm_DaddUniversalSingularity_r3`. -/
theorem ep1054_Prop_DaddCollisionCriterion_r3
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Prop_DaddCollisionCriterion :=
  ep1054_Prop_DaddCollisionCriterion i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range
    i_Cite_LP_Lemma25 input_Cite_LP_sieve37 i_Cite_Pollack_Thm14 i_Cite_Helfgott_weighted
    i_Cite_Dusart_Thm69 input_Cite_PollackAP i_Cite_Erdos_singular i_Comp_Verifier_small
    i_Comp_Verifier_window1 i_Comp_Verifier_largeSeed

/-- **The heavy-tail corollary (`Cor_DaddHeavyTails`)** with `Cite_MV_exceptional`,
`Cite_LP_sieve37` and `Cite_PollackAP` all gone. The composition is the tail of
`Spine.spine_Cor_DaddHeavyTails`: MV entered it only through `Eq_AlmostLogTail`, which now comes
from `Alt.eq_AlmostLogTail_of_goldbachDensZero`; the universal-singularity parts (`Carrier`,
`Tight`) are read off `ep1054_Thm_DaddUniversalSingularity_r3`, `Thm_SmallUpper_doubleExp` off
`Proofs.ep1054_Thm_SmallUpper`, and `Eq_ExactRepresentability` is
`Proofs.ep1054_Eq_ExactRepresentability`.

**Remaining hypotheses:** the same ten as `ep1054_Thm_DaddUniversalSingularity_r3`. -/
theorem ep1054_Cor_DaddHeavyTails_r3
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Cor_DaddHeavyTails :=
  have v_Univ : Thm_DaddUniversalSingularity :=
    ep1054_Thm_DaddUniversalSingularity_r3 i_Cite_LP_Lemma21 i_Cite_LP_Lemma22_range
      i_Cite_LP_Lemma25 i_Cite_Pollack_Thm14 i_Cite_Helfgott_weighted i_Cite_Dusart_Thm69
      i_Cite_Erdos_singular i_Comp_Verifier_small i_Comp_Verifier_window1
      i_Comp_Verifier_largeSeed
  have v_Carrier : Thm_DaddUniversalSingularity_Carrier := v_Univ.1
  have v_Tight : Thm_DaddUniversalSingularity_Tight := v_Univ.2.2
  have v_Eq_AlmostLogTail : Eq_AlmostLogTail :=
    eq_AlmostLogTail_of_goldbachDensZero std_GoldbachDensZero_unconditional
  have v_Thm_SmallUpper_doubleExp : Thm_SmallUpper_doubleExp := ep1054_Thm_SmallUpper.1
  have v_Step_DaddXoverR : Step_DaddXoverR :=
    link_Step_DaddXoverR
      (ep1054_Eq_ExactRepresentability i_Cite_Helfgott_weighted i_Cite_Dusart_Thm69
        i_Comp_Verifier_small i_Comp_Verifier_window1 i_Comp_Verifier_largeSeed)
  have v_Step_DaddLowerTailUniform : Step_DaddLowerTailUniform :=
    link_Step_DaddLowerTailUniform v_Thm_SmallUpper_doubleExp v_Step_DaddXoverR
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

/-! ## 5. The whole paper

`noMV_EP1054` below is generated from `Proofs/Assembly.lean`'s `Assembly.noRS_EP1054`: its
binders and body are that theorem's except where `gen_unconditional.py` says. -/

set_option maxRecDepth 20000 in
/-- `Assembly.noRS_EP1054` (every derived claim of EP1054) with **both Montgomery–Vaughan link
applications replaced by hypotheses of their conclusions**: `h_AOR_Bound` stands for
`L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional` and `h_OddUntouchables` for
`L_Eq_OddUntouchables i_Cite_MV_exceptional`. The binders `i_Cite_MV_exceptional`,
`L_Lem_AnalyticOddRepresentability_Bound` and `L_Eq_OddUntouchables` are deleted; nothing else
changes. Generated by `gen_unconditional.py`. -/
theorem noMV_EP1054
    (L_Std_PNT : Link_Std_PNT)
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Cite_Davenport : Link_Cite_Davenport)
    (L_Intro_LiminfZero : Link_Intro_LiminfZero)
    (L_Fact_KmodFinite : Link_Fact_KmodFinite)
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Rem_RoughInputModulus : Link_Rem_RoughInputModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Lem_SigmaRate_OddPrime : Link_Lem_SigmaRate_OddPrime)
    (L_Lem_SigmaRate_B2 : Link_Lem_SigmaRate_B2)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (L_Intro_RcntFormula : Link_Intro_RcntFormula)
    (L_Thm_FraitureRepresentability_Ge6 : Link_Thm_FraitureRepresentability_Ge6)
    (L_KovacMoment_identity : Link_KovacMoment_identity)
    (L_KovacMoment_reduction : Link_KovacMoment_reduction)
    (L_Eq_KSprime : Link_Eq_KSprime)
    (L_Eq_KSsecond : Link_Eq_KSsecond)
    (L_Eq_KS : Link_Eq_KS)
    (L_Lem_KovacMoment : Link_Lem_KovacMoment)
    (L_SmallUpper_momentStep : Link_SmallUpper_momentStep)
    (L_Thm_SmallUpper_doubleExp : Link_Thm_SmallUpper_doubleExp)
    (L_Thm_SmallUpper_fixedPower : Link_Thm_SmallUpper_fixedPower)
    (L_Thm_SmallUpper_upperDens : Link_Thm_SmallUpper_upperDens)
    (L_Intro_LittleO_onlyOnDensityZero : Link_Intro_LittleO_onlyOnDensityZero)
    (L_Prop_SmallRatioThreshold : Link_Prop_SmallRatioThreshold)
    (L_Rem_Lcm289Witness : Link_Rem_Lcm289Witness)
    (L_Eq_SvTwoSided : Link_Eq_SvTwoSided)
    (L_SvA0_jSum : Link_SvA0_jSum)
    (L_Lem_SvA0Count : Link_Lem_SvA0Count)
    (L_Eq_SmoothPartPeriodCount : Link_Eq_SmoothPartPeriodCount)
    (L_Lem_SmoothPartInput : Link_Lem_SmoothPartInput)
    (L_Lem_SvRegular : Link_Lem_SvRegular)
    (L_Lem_SvClasses : Link_Lem_SvClasses)
    (L_Eq_SvKReciprocal : Link_Eq_SvKReciprocal)
    (L_Eq_SvMReciprocal : Link_Eq_SvMReciprocal)
    (L_Claim_SvSigmaDistinct : Link_Claim_SvSigmaDistinct)
    (L_Claim_SvSievePairs : Link_Claim_SvSievePairs)
    (L_Eq_SvTotient : Link_Eq_SvTotient)
    (L_Claim_SvA3Reduction : Link_Claim_SvA3Reduction)
    (L_Claim_SvLargeHUnits : Link_Claim_SvLargeHUnits)
    (L_Eq_SvLargeHCongruence : Link_Eq_SvLargeHCongruence)
    (L_Claim_SvLargeHRigidity : Link_Claim_SvLargeHRigidity)
    (L_Claim_SvLargeH : Link_Claim_SvLargeH)
    (L_Claim_SvA322Reduction : Link_Claim_SvA322Reduction)
    (L_Claim_SvSmallHResidues : Link_Claim_SvSmallHResidues)
    (L_Eq_SvIntermediateTotient : Link_Eq_SvIntermediateTotient)
    (L_Eq_SvFSum : Link_Eq_SvFSum)
    (L_Eq_SvQRSum : Link_Eq_SvQRSum)
    (L_Claim_SvSmallH : Link_Claim_SvSmallH)
    (L_Eq_SvReducedCollisionSum : Link_Eq_SvReducedCollisionSum)
    (L_Prop_SvSecondMoment : Link_Prop_SvSecondMoment)
    (L_Claim_SvClassImage : Link_Claim_SvClassImage)
    (L_Claim_SvImageCount : Link_Claim_SvImageCount)
    (L_Claim_SvWitness : Link_Claim_SvWitness)
    (L_SvFamilyTarget : Link_SvFamilyTarget)
    (L_Thm_SmallValues : Link_Thm_SmallValues)
    (L_Thm_SmallValues_upperDens : Link_Thm_SmallValues_upperDens)
    (L_Thm_SmallValues_lowerDens : Link_Thm_SmallValues_lowerDens)
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
    (L_Eq_MovingKernelTail : Link_Eq_MovingKernelTail)
    (L_UpperTails_Claim_KA_finite : Link_UpperTails_Claim_KA_finite)
    (L_UpperTails_Claim_VA_periodic : Link_UpperTails_Claim_VA_periodic)
    (L_UpperTails_Claim_VA_density : Link_UpperTails_Claim_VA_density)
    (L_Prop_FmEnvelope : Link_Prop_FmEnvelope)
    (L_UpperTails_Claim_DeltaPfix : Link_UpperTails_Claim_DeltaPfix)
    (L_UpperTails_Claim_RoughNotVA : Link_UpperTails_Claim_RoughNotVA)
    (L_Cor_FmEnvelopeTail : Link_Cor_FmEnvelopeTail)
    (L_UpperTails_Claim_AlmostLogTail_main : Link_UpperTails_Claim_AlmostLogTail_main)
    (L_UpperTails_Claim_AlmostLogTail_fixedJ : Link_UpperTails_Claim_AlmostLogTail_fixedJ)
    (L_Eq_AlmostLogTail : Link_Eq_AlmostLogTail)
    (L_Thm_AlmostLogTail_posLowerDens : Link_Thm_AlmostLogTail_posLowerDens)
    (L_Thm_AlmostLogTail_limsup : Link_Thm_AlmostLogTail_limsup)
    (L_Intro_ErdosLittleO_fails : Link_Intro_ErdosLittleO_fails)
    (L_Intro_ErdosAlmostAllLittleO_fails : Link_Intro_ErdosAlmostAllLittleO_fails)
    (L_Eq_SharpRoughTargetCount : Link_Eq_SharpRoughTargetCount)
    (L_Eq_SharpBadSourceCount : Link_Eq_SharpBadSourceCount)
    (L_UpperTails_Claim_SubexpBadPairs : Link_UpperTails_Claim_SubexpBadPairs)
    (L_UpperTails_Claim_SubexpWitnessStructure : Link_UpperTails_Claim_SubexpWitnessStructure)
    (L_Eq_MovingKernelLowerBound : Link_Eq_MovingKernelLowerBound)
    (L_UpperTails_Claim_SubexpCoprimeCount : Link_UpperTails_Claim_SubexpCoprimeCount)
    (L_UpperTails_Claim_SubexpLowCofactorSum : Link_UpperTails_Claim_SubexpLowCofactorSum)
    (L_UpperTails_Claim_SubexpLowCofactor : Link_UpperTails_Claim_SubexpLowCofactor)
    (L_UpperTails_Claim_SubexpLargeCofactor : Link_UpperTails_Claim_SubexpLargeCofactor)
    (L_UpperTails_Claim_SubexpCore : Link_UpperTails_Claim_SubexpCore)
    (L_UpperTails_Claim_SubexpThreshold : Link_UpperTails_Claim_SubexpThreshold)
    (L_Eq_SubexpGrowth : Link_Eq_SubexpGrowth)
    (L_Eq_PositiveMomentGrowth : Link_Eq_PositiveMomentGrowth)
    (L_Eq_He : Link_Eq_He)
    (L_Coverage_Step_ClassResidue : Link_Coverage_Step_ClassResidue)
    (L_Eq_RepresentingRatio : Link_Eq_RepresentingRatio)
    (L_Coverage_Disp_HeMean : Link_Coverage_Disp_HeMean)
    (L_Coverage_Step_GeLowerDens : Link_Coverage_Step_GeLowerDens)
    (L_Eq_ClassLower : Link_Eq_ClassLower)
    (L_Coverage_Disp_MertensCoprimeQ : Link_Coverage_Disp_MertensCoprimeQ)
    (L_Coverage_Disp_ClassPrimeSum : Link_Coverage_Disp_ClassPrimeSum)
    (L_Prop_ClassFirstMoment_bound : Link_Prop_ClassFirstMoment_bound)
    (L_Prop_ClassFirstMoment_tendsto : Link_Prop_ClassFirstMoment_tendsto)
    (L_Cor_FmPrimeCeiling_congr : Link_Cor_FmPrimeCeiling_congr)
    (L_Cor_FmPrimeCeiling_count : Link_Cor_FmPrimeCeiling_count)
    (L_Cor_FmPrimeCeiling_upperDens : Link_Cor_FmPrimeCeiling_upperDens)
    (L_Coverage_Rem_SqfreeDefectPos : Link_Coverage_Rem_SqfreeDefectPos)
    (L_Cor_FixedCofactorDefect_pos : Link_Cor_FixedCofactorDefect_pos)
    (L_Eq_FixedCofactorDefect : Link_Eq_FixedCofactorDefect)
    (L_Coverage_Step_KmodSmallPrime : Link_Coverage_Step_KmodSmallPrime)
    (L_Coverage_Step_GcovValuesSmallPrime : Link_Coverage_Step_GcovValuesSmallPrime)
    (L_Coverage_Fact_GcovCoprimeNull : Link_Coverage_Fact_GcovCoprimeNull)
    (L_Coverage_Fact_CoprimeComplementDens : Link_Coverage_Fact_CoprimeComplementDens)
    (L_Eq_BoundedCofactorComplement : Link_Eq_BoundedCofactorComplement)
    (L_Coverage_Disp_LogPA : Link_Coverage_Disp_LogPA)
    (L_Eq_DeltaAAsymptotic : Link_Eq_DeltaAAsymptotic)
    (L_Prop_EtaALower_bound : Link_Prop_EtaALower_bound)
    (L_Prop_EtaALower_tendsto : Link_Prop_EtaALower_tendsto)
    (L_Coverage_Rem_EtaDominates : Link_Coverage_Rem_EtaDominates)
    (L_Eq_F2OddNegligible : Link_Eq_F2OddNegligible)
    (L_Coverage_Step_EvenUntouchables : Link_Coverage_Step_EvenUntouchables)
    (L_Coverage_Disp_F2Count : Link_Coverage_Disp_F2Count)
    (L_Prop_ThetaTwo : Link_Prop_ThetaTwo)
    (L_Coverage_Step_UpperDensG2 : Link_Coverage_Step_UpperDensG2)
    (L_Cor_EtaTwo : Link_Cor_EtaTwo)
    (L_Coverage_Rem_ConjEquivEta : Link_Coverage_Rem_ConjEquivEta)
    (L_Coverage_Rem_RoughPartBound : Link_Coverage_Rem_RoughPartBound)
    (L_Coverage_Rem_ConjEquivSmallPrimePart : Link_Coverage_Rem_ConjEquivSmallPrimePart)
    (L_Coverage_Disp_TailLeCompl : Link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail : Link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence : Link_Prop_TightnessEquivalence)
    (L_Coverage_Rem_T_iff_Conj : Link_Coverage_Rem_T_iff_Conj)
    (L_Fact_DaddDavenportLaw : Link_Fact_DaddDavenportLaw)
    (L_Fact_DaddProgressionLaws : Link_Fact_DaddProgressionLaws)
    (L_Eq_DaddProgressionDomination : Link_Eq_DaddProgressionDomination)
    (L_Step_DaddWitnessIdentity : Link_Step_DaddWitnessIdentity)
    (L_Step_DaddWitnessJointLimit : Link_Step_DaddWitnessJointLimit)
    (L_Step_DaddWitnessSupport : Link_Step_DaddWitnessSupport)
    (L_Step_DaddWitnessCount : Link_Step_DaddWitnessCount)
    (L_Step_DaddWitnessCofactorTail : Link_Step_DaddWitnessCofactorTail)
    (L_Step_DaddWitnessPieceBounds : Link_Step_DaddWitnessPieceBounds)
    (L_Prop_DaddWitnessMeans : Link_Prop_DaddWitnessMeans)
    (L_Rem_DaddWitnessMeanGrowth : Link_Rem_DaddWitnessMeanGrowth)
    (L_Step_DaddSingularCarrier : Link_Step_DaddSingularCarrier)
    (L_Step_DaddWitnessMeasureMass : Link_Step_DaddWitnessMeasureMass)
    (L_Step_DaddWitnessCarrier : Link_Step_DaddWitnessCarrier)
    (L_Step_DaddEmpiricalWitnessVague : Link_Step_DaddEmpiricalWitnessVague)
    (L_Step_DaddLimitDomination : Link_Step_DaddLimitDomination)
    (L_Thm_DaddUniversalSingularity_Carrier : Link_Thm_DaddUniversalSingularity_Carrier)
    (L_Thm_DaddUniversalSingularity_FinitePart : Link_Thm_DaddUniversalSingularity_FinitePart)
    (L_Thm_DaddUniversalSingularity_Tight : Link_Thm_DaddUniversalSingularity_Tight)
    (L_Step_DaddXoverR : Link_Step_DaddXoverR)
    (L_Step_DaddLowerTailUniform : Link_Step_DaddLowerTailUniform)
    (L_Eq_DaddSubsequentialTail : Link_Eq_DaddSubsequentialTail)
    (L_Cor_DaddHeavyTails_PosMoments : Link_Cor_DaddHeavyTails_PosMoments)
    (L_Cor_DaddHeavyTails_LogMeans : Link_Cor_DaddHeavyTails_LogMeans)
    (L_Cor_DaddHeavyTails_InvMoments : Link_Cor_DaddHeavyTails_InvMoments)
    (L_Cor_DaddHeavyTails_InvMomentConv : Link_Cor_DaddHeavyTails_InvMomentConv)
    (L_Cor_DaddHeavyTails_GeomMean : Link_Cor_DaddHeavyTails_GeomMean)
    (L_Cor_DaddHeavyTails_Tight : Link_Cor_DaddHeavyTails_Tight)
    (L_Step_DaddCollisionSupport : Link_Step_DaddCollisionSupport)
    (L_Eq_DaddCollisionCriterion : Link_Eq_DaddCollisionCriterion)
    (L_Prop_DaddCollisionCriterion : Link_Prop_DaddCollisionCriterion)
    (L_Step_DaddCollisionWitness : Link_Step_DaddCollisionWitness)
    (L_Step_DaddCollisionFirstMoment : Link_Step_DaddCollisionFirstMoment)
    (L_Step_DaddCollisionFirstMomentLaw : Link_Step_DaddCollisionFirstMomentLaw)
    (L_Step_DaddCollisionSourceIntensity : Link_Step_DaddCollisionSourceIntensity)
    (L_Step_DaddCollisionCylinder : Link_Step_DaddCollisionCylinder)
    (L_Step_DaddCollisionPerCore : Link_Step_DaddCollisionPerCore)
    (L_Step_DaddCollisionCombine : Link_Step_DaddCollisionCombine)
    (L_Step_DaddCollisionExplicit : Link_Step_DaddCollisionExplicit)
    (L_Prop_DaddCollisionLowerBound : Link_Prop_DaddCollisionLowerBound)
    (hL : LeafClaims)
    (h_AOR_Bound : Lem_AnalyticOddRepresentability_Bound)
    (h_OddUntouchables : Eq_OddUntouchables)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Pollack_Lemma24 : Cite_Pollack_Lemma24)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP)
    (i_Std_SiegelWalfisz_dyadic : Std_SiegelWalfisz_dyadic)
    (i_Std_BrunTitchmarsh : Std_BrunTitchmarsh)
    (i_Std_divisorBound : Std_divisorBound)
    (i_Std_sigma_odd_iff : Std_sigma_odd_iff)
    (i_Std_totient_sigma : Std_totient_sigma)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    DerivedClaims :=
  have h_Std_Mertens1 : Std_Mertens1 := hL.c_Std_Mertens1
  have h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges := hL.c_Std_recipPrimesAP_diverges
  have h_EmpiricalMeasures_isProbability : EmpiricalMeasures_isProbability :=
      hL.c_EmpiricalMeasures_isProbability
  have h_Intro_f_sigma_le : Intro_f_sigma_le := hL.c_Intro_f_sigma_le
  have h_Notation_Delta_density : Notation_Delta_density := hL.c_Notation_Delta_density
  have h_Notation_sigmaPrefix_zero : Notation_sigmaPrefix_zero := hL.c_Notation_sigmaPrefix_zero
  have h_Disp_FinalDivisor : Disp_FinalDivisor := hL.c_Disp_FinalDivisor
  have h_Eq_Reflection : Eq_Reflection := hL.c_Eq_Reflection
  have h_Fact_KmodGeTwo : Fact_KmodGeTwo := hL.c_Fact_KmodGeTwo
  have h_Fact_DsetResidue : Fact_DsetResidue := hL.c_Fact_DsetResidue
  have h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow := hL.c_Lem_FraiturePrimeWindow
  have h_Lem_FraitureExtension : Lem_FraitureExtension := hL.c_Lem_FraitureExtension
  have h_Step_FraitureSmallBq : Step_FraitureSmallBq := hL.c_Step_FraitureSmallBq
  have h_Step_FraitureSeven : Step_FraitureSeven := hL.c_Step_FraitureSeven
  have h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes :=
      hL.c_Step_FraitureTailThreePrimes
  have h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes :=
      hL.c_Step_FraitureTailFourPrimes
  have h_Step_FraitureSmallCases : Step_FraitureSmallCases := hL.c_Step_FraitureSmallCases
  have h_KovacMoment_reflection : KovacMoment_reflection := hL.c_KovacMoment_reflection
  have h_KovacS_le_S1S2 : KovacS_le_S1S2 := hL.c_KovacS_le_S1S2
  have h_SmallUpper_emptyCase : SmallUpper_emptyCase := hL.c_SmallUpper_emptyCase
  have h_SmallUpper_markov : SmallUpper_markov := hL.c_SmallUpper_markov
  have h_SmallUpper_paramChoice : SmallUpper_paramChoice := hL.c_SmallUpper_paramChoice
  have h_SmallUpper_doubleExpPower : SmallUpper_doubleExpPower := hL.c_SmallUpper_doubleExpPower
  have h_SmallRatio_prefixLeSig : SmallRatio_prefixLeSig := hL.c_SmallRatio_prefixLeSig
  have h_SmallRatio_abundancySmall : SmallRatio_abundancySmall := hL.c_SmallRatio_abundancySmall
  have h_SmallRatio_axlerNumeric : SmallRatio_axlerNumeric := hL.c_SmallRatio_axlerNumeric
  have h_Rem_Lcm289Abundant : Rem_Lcm289Abundant := hL.c_Rem_Lcm289Abundant
  have h_Eq_SvBasic : Eq_SvBasic := hL.c_Eq_SvBasic
  have h_Eq_SvD : Eq_SvD := hL.c_Eq_SvD
  have h_Lem_SvA0Unique : Lem_SvA0Unique := hL.c_Lem_SvA0Unique
  have h_Lem_SvA0QLarge : Lem_SvA0QLarge := hL.c_Lem_SvA0QLarge
  have h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic := hL.c_SvA0_sigmaHarmonic
  have h_SvA0_abundancySubmul : SvA0_abundancySubmul := hL.c_SvA0_abundancySubmul
  have h_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero := hL.c_Eq_SvHarmonicDensityZero
  have h_Eq_SvCollision : Eq_SvCollision := hL.c_Eq_SvCollision
  have h_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree := hL.c_Claim_SvSmallHSquarefree
  have h_Claim_SvResiduePairCount : Claim_SvResiduePairCount := hL.c_Claim_SvResiduePairCount
  have h_Claim_SvCauchySchwarz : Claim_SvCauchySchwarz := hL.c_Claim_SvCauchySchwarz
  have h_Eq_RankinKernel : Eq_RankinKernel := hL.c_Eq_RankinKernel
  have h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms :=
      hL.c_UpperTails_Claim_EulerHigherTerms
  have h_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough := hL.c_UpperTails_Claim_VA_rough
  have h_UpperTails_Claim_AlmostLogTail_momentArith : UpperTails.Claim_AlmostLogTail_momentArith :=
      hL.c_UpperTails_Claim_AlmostLogTail_momentArith
  have h_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree :=
      hL.c_UpperTails_Claim_RoughNonsquarefree
  have h_UpperTails_Claim_LscaleRatio : UpperTails.Claim_LscaleRatio :=
      hL.c_UpperTails_Claim_LscaleRatio
  have h_UpperTails_Claim_SubexpFltP : UpperTails.Claim_SubexpFltP :=
      hL.c_UpperTails_Claim_SubexpFltP
  have h_UpperTails_Claim_SubexpCofactorOne : UpperTails.Claim_SubexpCofactorOne :=
      hL.c_UpperTails_Claim_SubexpCofactorOne
  have h_UpperTails_Claim_SubexpLogT : UpperTails.Claim_SubexpLogT :=
      hL.c_UpperTails_Claim_SubexpLogT
  have h_Coverage_Fact_RtPosIff : Coverage.Fact_RtPosIff := hL.c_Coverage_Fact_RtPosIff
  have h_Eq_HGcd : Eq_HGcd := hL.c_Eq_HGcd
  have h_Eq_UClass : Eq_UClass := hL.c_Eq_UClass
  have h_Coverage_Step_SeDensity : Coverage.Step_SeDensity := hL.c_Coverage_Step_SeDensity
  have h_Coverage_Step_HeRatio : Coverage.Step_HeRatio := hL.c_Coverage_Step_HeRatio
  have h_Coverage_Step_SeMultiplesDens : Coverage.Step_SeMultiplesDens :=
      hL.c_Coverage_Step_SeMultiplesDens
  have h_Coverage_Disp_CoprimeSqTail : Coverage.Disp_CoprimeSqTail :=
      hL.c_Coverage_Disp_CoprimeSqTail
  have h_Coverage_Step_DistinctPairs : Coverage.Step_DistinctPairs :=
      hL.c_Coverage_Step_DistinctPairs
  have h_Eq_F2Aliquot : Eq_F2Aliquot := hL.c_Eq_F2Aliquot
  have h_Coverage_Step_G2Decomp : Coverage.Step_G2Decomp := hL.c_Coverage_Step_G2Decomp
  have h_Coverage_Step_P2Values : Coverage.Step_P2Values := hL.c_Coverage_Step_P2Values
  have h_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl :=
      hL.c_Coverage_Fact_UpperDensCompl
  have h_Step_DaddWitnessDomination : Step_DaddWitnessDomination := hL.c_Step_DaddWitnessDomination
  have h_Step_DaddCountDomination : Step_DaddCountDomination := hL.c_Step_DaddCountDomination
  have h_Eq_DaddCollisionAffine : Eq_DaddCollisionAffine := hL.c_Eq_DaddCollisionAffine
  have h_Step_DaddCollisionCores : Step_DaddCollisionCores := hL.c_Step_DaddCollisionCores
  have h_Step_DaddCollisionH : Step_DaddCollisionH := hL.c_Step_DaddCollisionH
  have h_Step_DaddCollisionArithmetic : Step_DaddCollisionArithmetic :=
      hL.c_Step_DaddCollisionArithmetic
  have v_Lem_LPInputs : Lem_LPInputs := And.intro i_Cite_LP_Lemma21 (And.intro
      i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)
  have v_Std_PNT : Std_PNT := L_Std_PNT i_Std_PNT_AP
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
  have v_Cite_Davenport : Cite_Davenport := L_Cite_Davenport i_Cite_PollackAP
  have v_Intro_LiminfZero : Intro_LiminfZero := L_Intro_LiminfZero h_Intro_f_sigma_le
  have v_Fact_KmodFinite : Fact_KmodFinite := L_Fact_KmodFinite h_Fact_DsetResidue
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Rem_RoughInputModulus : Rem_RoughInputModulus := L_Rem_RoughInputModulus h_Fact_DsetResidue
      v_Lem_FmModulus
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_SigmaRate_OddPrime : Lem_SigmaRate_OddPrime := L_Lem_SigmaRate_OddPrime
      i_Cite_Pollack_Lemma24 i_Std_SiegelWalfisz_dyadic
  have v_Lem_SigmaRate_B2 : Lem_SigmaRate_B2 := L_Lem_SigmaRate_B2 i_Std_sigma_odd_iff
  have v_Lem_SigmaRate : Lem_SigmaRate := And.intro v_Lem_SigmaRate_OddPrime v_Lem_SigmaRate_B2
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      h_AOR_Bound
  have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
      L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
  have v_Lem_AnalyticOddRepresentability : Lem_AnalyticOddRepresentability := And.intro
      v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO
  have v_Eq_FraitureSmall : Eq_FraitureSmall := L_Eq_FraitureSmall h_Step_FraitureSmallBq
      h_Step_FraitureSeven i_Comp_Verifier_small
  have v_Step_FraitureFirstWindowCover : Step_FraitureFirstWindowCover :=
      L_Step_FraitureFirstWindowCover h_Lem_FraitureExtension i_Comp_Verifier_window1
  have v_Eq_FraitureFirstWindow : Eq_FraitureFirstWindow := L_Eq_FraitureFirstWindow
      v_Step_FraitureFirstWindowCover h_Lem_FraiturePrimeWindow
  have v_Step_FraitureLargeWindowCover : Step_FraitureLargeWindowCover :=
      L_Step_FraitureLargeWindowCover h_Lem_FraitureExtension i_Comp_Verifier_largeSeed
  have v_Step_FraitureLargePrimeSum : Step_FraitureLargePrimeSum := L_Step_FraitureLargePrimeSum
      i_Cite_Dusart_Thm69
  have v_Eq_FraitureLargeWindow : Eq_FraitureLargeWindow := L_Eq_FraitureLargeWindow
      v_Step_FraitureLargeWindowCover v_Step_FraitureLargePrimeSum h_Lem_FraiturePrimeWindow
  have v_Prop_FraitureFinite : Prop_FraitureFinite := And.intro v_Eq_FraitureSmall (And.intro
      v_Eq_FraitureFirstWindow v_Eq_FraitureLargeWindow)
  have v_Lem_FraitureBalancedGoldbach : Lem_FraitureBalancedGoldbach :=
      (Principia.Erdos1054.Proofs.balancedGoldbach_of_helfgott_noRS i_Cite_Helfgott_weighted)
  have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
  have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
  have v_Prop_FraitureTail : Prop_FraitureTail := L_Prop_FraitureTail v_Step_FraitureTailEven
      v_Step_FraitureTailOdd
  have v_Thm_FraitureRepresentability : Thm_FraitureRepresentability :=
      L_Thm_FraitureRepresentability v_Prop_FraitureFinite v_Prop_FraitureTail
      h_Step_FraitureSmallCases
  have v_Eq_ExactRepresentability : Eq_ExactRepresentability := v_Thm_FraitureRepresentability
  have v_Intro_RcntFormula : Intro_RcntFormula := L_Intro_RcntFormula v_Eq_ExactRepresentability
  have v_Thm_FraitureRepresentability_Ge6 : Thm_FraitureRepresentability_Ge6 :=
      L_Thm_FraitureRepresentability_Ge6 v_Thm_FraitureRepresentability
  have v_KovacMoment_identity : KovacMoment_identity := L_KovacMoment_identity
      h_KovacMoment_reflection
  have v_KovacMoment_reduction : KovacMoment_reduction := L_KovacMoment_reduction
      v_KovacMoment_identity
  have v_Eq_KSprime : Eq_KSprime := L_Eq_KSprime i_Std_Mertens2
  have v_Eq_KSsecond : Eq_KSsecond := L_Eq_KSsecond i_Std_Mertens2
  have v_Eq_KS : Eq_KS := L_Eq_KS h_KovacS_le_S1S2 v_Eq_KSprime v_Eq_KSsecond
  have v_Lem_KovacMoment : Lem_KovacMoment := L_Lem_KovacMoment v_KovacMoment_reduction v_Eq_KS
  have v_SmallUpper_momentStep : SmallUpper_momentStep := L_SmallUpper_momentStep
      h_SmallUpper_markov v_Lem_KovacMoment
  have v_Thm_SmallUpper_doubleExp : Thm_SmallUpper_doubleExp := L_Thm_SmallUpper_doubleExp
      h_SmallUpper_emptyCase v_SmallUpper_momentStep h_SmallUpper_paramChoice
  have v_Thm_SmallUpper_fixedPower : Thm_SmallUpper_fixedPower := L_Thm_SmallUpper_fixedPower
      v_Thm_SmallUpper_doubleExp h_SmallUpper_doubleExpPower
  have v_Thm_SmallUpper : Thm_SmallUpper := And.intro v_Thm_SmallUpper_doubleExp
      v_Thm_SmallUpper_fixedPower
  have v_Thm_SmallUpper_upperDens : Thm_SmallUpper_upperDens := L_Thm_SmallUpper_upperDens
      v_Thm_SmallUpper_doubleExp
  have v_Intro_LittleO_onlyOnDensityZero : Intro_LittleO_onlyOnDensityZero :=
      L_Intro_LittleO_onlyOnDensityZero v_Thm_SmallUpper_upperDens
  have v_Prop_SmallRatioThreshold : Prop_SmallRatioThreshold := L_Prop_SmallRatioThreshold
      h_SmallRatio_prefixLeSig h_SmallRatio_abundancySmall h_SmallRatio_axlerNumeric
      i_Cite_Axler_Cor2
  have v_Rem_Lcm289Witness : Rem_Lcm289Witness := L_Rem_Lcm289Witness h_Rem_Lcm289Abundant
  have v_Eq_SvTwoSided : Eq_SvTwoSided := L_Eq_SvTwoSided h_SvA0_abundancySubmul
  have v_SvA0_jSum : SvA0_jSum := L_SvA0_jSum h_SvA0_sigmaHarmonic
  have v_Lem_SvA0Count : Lem_SvA0Count := L_Lem_SvA0Count v_SvA0_jSum h_Lem_SvA0Unique
      v_Std_primes_dyadic_lower i_Std_Mertens2
  have v_Lem_SvA0 : Lem_SvA0 := And.intro v_Lem_SvA0Count (And.intro h_Lem_SvA0Unique (And.intro
      v_Eq_SvTwoSided h_Lem_SvA0QLarge))
  have v_Eq_SmoothPartPeriodCount : Eq_SmoothPartPeriodCount := L_Eq_SmoothPartPeriodCount
      h_Notation_Delta_density
  have v_Lem_SmoothPartInput : Lem_SmoothPartInput := L_Lem_SmoothPartInput
      v_Eq_SmoothPartPeriodCount h_Std_Mertens1 i_Std_Mertens3
  have v_Lem_SvRegular : Lem_SvRegular := L_Lem_SvRegular v_Lem_SvA0 v_Lem_LPInputs
      h_Eq_SvHarmonicDensityZero i_Cite_Pollack_Thm14 i_Std_Mertens2
  have v_Lem_SvClasses : Lem_SvClasses := L_Lem_SvClasses v_Lem_SmoothPartInput i_Std_Mertens3
  have v_Eq_SvKReciprocal : Eq_SvKReciprocal := L_Eq_SvKReciprocal v_Eq_SmoothPartPeriodCount
      i_Std_Mertens3
  have v_Eq_SvMReciprocal : Eq_SvMReciprocal := L_Eq_SvMReciprocal v_Eq_SvKReciprocal i_Std_Mertens2
  have v_Claim_SvSigmaDistinct : Claim_SvSigmaDistinct := L_Claim_SvSigmaDistinct v_Eq_SvTwoSided
      h_Eq_SvCollision
  have v_Claim_SvSievePairs : Claim_SvSievePairs := L_Claim_SvSievePairs v_Claim_SvSigmaDistinct
      h_Eq_SvCollision v_Eq_SvTwoSided i_Cite_LP_sieve37
  have v_Eq_SvTotient : Eq_SvTotient := L_Eq_SvTotient i_Std_totient_sigma
  have v_Claim_SvA3Reduction : Claim_SvA3Reduction := L_Claim_SvA3Reduction v_Eq_SvTwoSided
      i_Std_Mertens3
  have v_Claim_SvLargeHUnits : Claim_SvLargeHUnits := L_Claim_SvLargeHUnits h_Eq_SvCollision
  have v_Eq_SvLargeHCongruence : Eq_SvLargeHCongruence := L_Eq_SvLargeHCongruence h_Eq_SvCollision
  have v_Claim_SvLargeHRigidity : Claim_SvLargeHRigidity := L_Claim_SvLargeHRigidity
      v_Eq_SvLargeHCongruence v_Eq_SvTwoSided v_Claim_SvLargeHUnits h_Eq_SvCollision
  have v_Claim_SvLargeH : Claim_SvLargeH := L_Claim_SvLargeH v_Claim_SvLargeHRigidity
      i_Std_divisorBound i_Std_Mertens2
  have v_Claim_SvA322Reduction : Claim_SvA322Reduction := L_Claim_SvA322Reduction v_Eq_SvTotient
  have v_Claim_SvSmallHResidues : Claim_SvSmallHResidues := L_Claim_SvSmallHResidues
      h_Eq_SvCollision
  have v_Eq_SvIntermediateTotient : Eq_SvIntermediateTotient := L_Eq_SvIntermediateTotient
      h_Eq_SvCollision i_Std_Mertens2
  have v_Eq_SvFSum : Eq_SvFSum := L_Eq_SvFSum v_Eq_SvTotient i_Std_BrunTitchmarsh
  have v_Eq_SvQRSum : Eq_SvQRSum := L_Eq_SvQRSum v_Eq_SvFSum v_Eq_SvTotient i_Std_BrunTitchmarsh
  have v_Claim_SvSmallH : Claim_SvSmallH := L_Claim_SvSmallH v_Claim_SvA322Reduction
      h_Claim_SvSmallHSquarefree v_Claim_SvSmallHResidues h_Claim_SvResiduePairCount
      v_Eq_SvIntermediateTotient v_Eq_SvQRSum v_Eq_SvKReciprocal v_Eq_SvMReciprocal
      i_Std_divisorBound
  have v_Eq_SvReducedCollisionSum : Eq_SvReducedCollisionSum := L_Eq_SvReducedCollisionSum
      v_Claim_SvLargeH v_Claim_SvSmallH
  have v_Prop_SvSecondMoment : Prop_SvSecondMoment := L_Prop_SvSecondMoment h_Eq_SvCollision
      v_Claim_SvSievePairs v_Eq_SvTotient v_Claim_SvA3Reduction v_Eq_SvReducedCollisionSum
  have v_Claim_SvClassImage : Claim_SvClassImage := L_Claim_SvClassImage h_Claim_SvCauchySchwarz
      v_Prop_SvSecondMoment
  have v_Claim_SvImageCount : Claim_SvImageCount := L_Claim_SvImageCount v_Lem_SvClasses
      v_Claim_SvClassImage
  have v_Claim_SvWitness : Claim_SvWitness := L_Claim_SvWitness h_Eq_SvBasic v_Eq_SvTwoSided
  have v_SvFamilyTarget : SvFamilyTarget := L_SvFamilyTarget h_Eq_SvD v_Lem_SvRegular
      v_Claim_SvImageCount v_Claim_SvWitness
  have v_Thm_SmallValues : Thm_SmallValues := L_Thm_SmallValues v_SvFamilyTarget h_Eq_SvBasic
  have v_Thm_SmallValues_upperDens : Thm_SmallValues_upperDens := L_Thm_SmallValues_upperDens
      v_Thm_SmallValues
  have v_Thm_SmallValues_lowerDens : Thm_SmallValues_lowerDens := L_Thm_SmallValues_lowerDens
      v_Thm_SmallValues
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
  have v_Eq_MovingKernelTail : Eq_MovingKernelTail := L_Eq_MovingKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
  have v_Lem_KernelTails : Lem_KernelTails := And.intro v_Eq_FixedKernelTail v_Eq_MovingKernelTail
  have v_UpperTails_Claim_KA_finite : UpperTails.Claim_KA_finite := L_UpperTails_Claim_KA_finite
      v_Lem_FmModulus h_Fact_KmodGeTwo
  have v_UpperTails_Claim_VA_periodic : UpperTails.Claim_VA_periodic :=
      L_UpperTails_Claim_VA_periodic v_UpperTails_Claim_KA_finite
  have v_UpperTails_Claim_VA_density : UpperTails.Claim_VA_density := L_UpperTails_Claim_VA_density
      v_UpperTails_Claim_KA_finite v_UpperTails_Claim_VA_periodic h_Fact_KmodGeTwo
  have v_Prop_FmEnvelope : Prop_FmEnvelope := L_Prop_FmEnvelope v_Lem_SigmaRangeZero v_Lem_FmModulus
      v_Lem_FixedModulusNormality v_UpperTails_Claim_KA_finite v_UpperTails_Claim_VA_density
  have v_UpperTails_Claim_DeltaPfix : UpperTails.Claim_DeltaPfix := L_UpperTails_Claim_DeltaPfix
      i_Std_Mertens3
  have v_UpperTails_Claim_RoughNotVA : UpperTails.Claim_RoughNotVA := L_UpperTails_Claim_RoughNotVA
      v_Lem_FmModulus h_Fact_KmodGeTwo v_UpperTails_Claim_KA_finite h_Notation_Delta_density
  have v_Cor_FmEnvelopeTail : Cor_FmEnvelopeTail := L_Cor_FmEnvelopeTail h_UpperTails_Claim_VA_rough
      v_UpperTails_Claim_VA_density h_Notation_Delta_density v_UpperTails_Claim_DeltaPfix
      v_UpperTails_Claim_RoughNotVA v_Eq_FixedKernelTail
  have v_UpperTails_Claim_AlmostLogTail_main : UpperTails.Claim_AlmostLogTail_main :=
      L_UpperTails_Claim_AlmostLogTail_main v_Prop_FmEnvelope v_Lem_Moment
      h_UpperTails_Claim_AlmostLogTail_momentArith h_UpperTails_Claim_VA_rough
      h_UpperTails_Claim_RoughNonsquarefree v_Lem_AnalyticOddRepresentability
      v_UpperTails_Claim_VA_density
  have v_UpperTails_Claim_AlmostLogTail_fixedJ : UpperTails.Claim_AlmostLogTail_fixedJ :=
      L_UpperTails_Claim_AlmostLogTail_fixedJ v_UpperTails_Claim_AlmostLogTail_main
      v_Cor_FmEnvelopeTail h_UpperTails_Claim_LscaleRatio
  have v_Eq_AlmostLogTail : Eq_AlmostLogTail := L_Eq_AlmostLogTail
      v_UpperTails_Claim_AlmostLogTail_fixedJ
  have v_Thm_AlmostLogTail_posLowerDens : Thm_AlmostLogTail_posLowerDens :=
      L_Thm_AlmostLogTail_posLowerDens v_Eq_AlmostLogTail
  have v_Thm_AlmostLogTail_limsup : Thm_AlmostLogTail_limsup := L_Thm_AlmostLogTail_limsup
      v_Thm_AlmostLogTail_posLowerDens
  have v_Thm_AlmostLogTail : Thm_AlmostLogTail := And.intro v_Eq_AlmostLogTail (And.intro
      v_Thm_AlmostLogTail_posLowerDens v_Thm_AlmostLogTail_limsup)
  have v_Intro_ErdosLittleO_fails : Intro_ErdosLittleO_fails := L_Intro_ErdosLittleO_fails
      v_Thm_AlmostLogTail_limsup
  have v_Intro_ErdosAlmostAllLittleO_fails : Intro_ErdosAlmostAllLittleO_fails :=
      L_Intro_ErdosAlmostAllLittleO_fails v_Thm_AlmostLogTail_posLowerDens
  have v_Eq_SharpRoughTargetCount : Eq_SharpRoughTargetCount := L_Eq_SharpRoughTargetCount
      h_Notation_Delta_density i_Std_Mertens3
  have v_Eq_SharpBadSourceCount : Eq_SharpBadSourceCount := L_Eq_SharpBadSourceCount v_Lem_SigmaRate
  have v_UpperTails_Claim_SubexpBadPairs : UpperTails.Claim_SubexpBadPairs :=
      L_UpperTails_Claim_SubexpBadPairs v_Eq_SharpBadSourceCount v_Eq_SharpRoughTargetCount
  have v_UpperTails_Claim_SubexpWitnessStructure : UpperTails.Claim_SubexpWitnessStructure :=
      L_UpperTails_Claim_SubexpWitnessStructure v_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Eq_MovingKernelLowerBound : Eq_MovingKernelLowerBound := L_Eq_MovingKernelLowerBound
      v_UpperTails_Claim_SubexpWitnessStructure h_UpperTails_Claim_SubexpFltP i_Std_Mertens3
  have v_UpperTails_Claim_SubexpCoprimeCount : UpperTails.Claim_SubexpCoprimeCount :=
      L_UpperTails_Claim_SubexpCoprimeCount h_Notation_Delta_density
  have v_UpperTails_Claim_SubexpLowCofactorSum : UpperTails.Claim_SubexpLowCofactorSum :=
      L_UpperTails_Claim_SubexpLowCofactorSum v_UpperTails_Claim_SubexpWitnessStructure
      v_Eq_MovingKernelLowerBound v_UpperTails_Claim_SubexpCoprimeCount
      h_UpperTails_Claim_SubexpFltP
  have v_UpperTails_Claim_SubexpLowCofactor : UpperTails.Claim_SubexpLowCofactor :=
      L_UpperTails_Claim_SubexpLowCofactor v_UpperTails_Claim_SubexpLowCofactorSum
      v_Eq_MovingKernelTail
  have v_UpperTails_Claim_SubexpLargeCofactor : UpperTails.Claim_SubexpLargeCofactor :=
      L_UpperTails_Claim_SubexpLargeCofactor i_Std_Mertens3
  have v_UpperTails_Claim_SubexpCore : UpperTails.Claim_SubexpCore := L_UpperTails_Claim_SubexpCore
      v_Eq_SharpRoughTargetCount h_UpperTails_Claim_RoughNonsquarefree
      v_UpperTails_Claim_SubexpBadPairs h_UpperTails_Claim_SubexpCofactorOne
      v_UpperTails_Claim_SubexpLowCofactor v_UpperTails_Claim_SubexpLargeCofactor v_Lem_Moment
      v_Lem_AnalyticOddRepresentability
  have v_UpperTails_Claim_SubexpThreshold : UpperTails.Claim_SubexpThreshold :=
      L_UpperTails_Claim_SubexpThreshold h_UpperTails_Claim_SubexpLogT
  have v_Eq_SubexpGrowth : Eq_SubexpGrowth := L_Eq_SubexpGrowth v_UpperTails_Claim_SubexpCore
      v_UpperTails_Claim_SubexpThreshold
  have v_Eq_PositiveMomentGrowth : Eq_PositiveMomentGrowth := L_Eq_PositiveMomentGrowth
      v_Eq_SubexpGrowth
  have v_Thm_SubexpGrowth : Thm_SubexpGrowth := And.intro v_Eq_SubexpGrowth
      v_Eq_PositiveMomentGrowth
  have v_Eq_He : Eq_He := L_Eq_He h_Coverage_Step_SeDensity
  have v_Coverage_Step_ClassResidue : Coverage.Step_ClassResidue := L_Coverage_Step_ClassResidue
      v_Eq_He
  have v_Eq_RepresentingRatio : Eq_RepresentingRatio := L_Eq_RepresentingRatio v_Eq_He
  have v_Coverage_Disp_HeMean : Coverage.Disp_HeMean := L_Coverage_Disp_HeMean
      h_Coverage_Step_HeRatio h_Coverage_Step_SeDensity h_Coverage_Step_SeMultiplesDens
      h_Coverage_Disp_CoprimeSqTail
  have v_Coverage_Step_GeLowerDens : Coverage.Step_GeLowerDens := L_Coverage_Step_GeLowerDens
      h_Coverage_Step_SeDensity v_Coverage_Disp_HeMean
  have v_Eq_ClassLower : Eq_ClassLower := L_Eq_ClassLower h_Eq_UClass v_Coverage_Step_GeLowerDens
      v_Eq_He v_Coverage_Step_ClassResidue v_Eq_RepresentingRatio h_Coverage_Step_DistinctPairs
      v_Lem_Moment h_Eq_Reflection
  have v_Coverage_Disp_MertensCoprimeQ : Coverage.Disp_MertensCoprimeQ :=
      L_Coverage_Disp_MertensCoprimeQ i_Std_Mertens3
  have v_Coverage_Disp_ClassPrimeSum : Coverage.Disp_ClassPrimeSum := L_Coverage_Disp_ClassPrimeSum
      i_Std_PNT_AP
  have v_Prop_ClassFirstMoment_bound : Prop_ClassFirstMoment_bound := L_Prop_ClassFirstMoment_bound
      h_Eq_HGcd v_Eq_ClassLower v_Coverage_Disp_MertensCoprimeQ v_Coverage_Disp_ClassPrimeSum
  have v_Prop_ClassFirstMoment_tendsto : Prop_ClassFirstMoment_tendsto :=
      L_Prop_ClassFirstMoment_tendsto v_Prop_ClassFirstMoment_bound
  have v_Prop_ClassFirstMoment : Prop_ClassFirstMoment := And.intro v_Prop_ClassFirstMoment_bound
      v_Prop_ClassFirstMoment_tendsto
  have v_Cor_FmPrimeCeiling_congr : Cor_FmPrimeCeiling_congr := L_Cor_FmPrimeCeiling_congr
      v_Lem_FmModulus
  have v_Cor_FmPrimeCeiling_count : Cor_FmPrimeCeiling_count := L_Cor_FmPrimeCeiling_count
      v_Cor_FmPrimeCeiling_congr h_Disp_FinalDivisor v_Lem_FixedModulusNormality
  have v_Cor_FmPrimeCeiling_upperDens : Cor_FmPrimeCeiling_upperDens :=
      L_Cor_FmPrimeCeiling_upperDens v_Cor_FmPrimeCeiling_count
  have v_Cor_FmPrimeCeiling : Cor_FmPrimeCeiling := And.intro v_Cor_FmPrimeCeiling_congr (And.intro
      v_Cor_FmPrimeCeiling_count v_Cor_FmPrimeCeiling_upperDens)
  have v_Coverage_Rem_SqfreeDefectPos : Coverage.Rem_SqfreeDefectPos :=
      L_Coverage_Rem_SqfreeDefectPos v_Eq_AlmostLogTail
  have v_Cor_FixedCofactorDefect_pos : Cor_FixedCofactorDefect_pos := L_Cor_FixedCofactorDefect_pos
      v_Eq_AlmostLogTail
  have v_Eq_FixedCofactorDefect : Eq_FixedCofactorDefect := L_Eq_FixedCofactorDefect
      v_Eq_AlmostLogTail
  have v_Cor_FixedCofactorDefect : Cor_FixedCofactorDefect := And.intro
      v_Cor_FixedCofactorDefect_pos v_Eq_FixedCofactorDefect
  have v_Coverage_Step_KmodSmallPrime : Coverage.Step_KmodSmallPrime :=
      L_Coverage_Step_KmodSmallPrime h_Fact_KmodGeTwo
  have v_Coverage_Step_GcovValuesSmallPrime : Coverage.Step_GcovValuesSmallPrime :=
      L_Coverage_Step_GcovValuesSmallPrime v_Coverage_Step_KmodSmallPrime v_Fact_KmodFinite
      v_Lem_FmModulus v_Lem_FixedModulusNormality
  have v_Coverage_Fact_GcovCoprimeNull : Coverage.Fact_GcovCoprimeNull :=
      L_Coverage_Fact_GcovCoprimeNull v_Coverage_Step_GcovValuesSmallPrime v_Lem_SigmaRangeZero
  have v_Coverage_Fact_CoprimeComplementDens : Coverage.Fact_CoprimeComplementDens :=
      L_Coverage_Fact_CoprimeComplementDens v_Coverage_Fact_GcovCoprimeNull h_Notation_Delta_density
  have v_Eq_BoundedCofactorComplement : Eq_BoundedCofactorComplement :=
      L_Eq_BoundedCofactorComplement v_Coverage_Fact_CoprimeComplementDens
      h_Coverage_Fact_UpperDensCompl
  have v_Coverage_Disp_LogPA : Coverage.Disp_LogPA := L_Coverage_Disp_LogPA v_Std_PNT
  have v_Eq_DeltaAAsymptotic : Eq_DeltaAAsymptotic := L_Eq_DeltaAAsymptotic v_Coverage_Disp_LogPA
      i_Std_Mertens3
  have v_Prop_EtaALower_bound : Prop_EtaALower_bound := L_Prop_EtaALower_bound
      v_Eq_FixedCofactorDefect h_Coverage_Fact_UpperDensCompl v_Eq_DeltaAAsymptotic
      v_Eq_BoundedCofactorComplement
  have v_Prop_EtaALower_tendsto : Prop_EtaALower_tendsto := L_Prop_EtaALower_tendsto
      v_Prop_EtaALower_bound
  have v_Prop_EtaALower : Prop_EtaALower := And.intro v_Prop_EtaALower_bound
      v_Prop_EtaALower_tendsto
  have v_Coverage_Rem_EtaDominates : Coverage.Rem_EtaDominates := L_Coverage_Rem_EtaDominates
      v_Prop_EtaALower_tendsto v_Eq_DeltaAAsymptotic v_Eq_BoundedCofactorComplement
  have v_Eq_F2OddNegligible : Eq_F2OddNegligible := L_Eq_F2OddNegligible h_Eq_F2Aliquot
      i_Std_sigma_odd_iff
  have v_Eq_OddUntouchables : Eq_OddUntouchables := h_OddUntouchables
  have v_Coverage_Step_EvenUntouchables : Coverage.Step_EvenUntouchables :=
      L_Coverage_Step_EvenUntouchables v_Eq_OddUntouchables i_Cite_ChenZhao
  have v_Coverage_Disp_F2Count : Coverage.Disp_F2Count := L_Coverage_Disp_F2Count h_Eq_F2Aliquot
      v_Eq_F2OddNegligible v_Coverage_Step_EvenUntouchables
  have v_Prop_ThetaTwo : Prop_ThetaTwo := L_Prop_ThetaTwo v_Coverage_Disp_F2Count
  have v_Coverage_Step_UpperDensG2 : Coverage.Step_UpperDensG2 := L_Coverage_Step_UpperDensG2
      h_Coverage_Step_G2Decomp v_Lem_SigmaRangeZero
  have v_Cor_EtaTwo : Cor_EtaTwo := L_Cor_EtaTwo v_Eq_BoundedCofactorComplement
      h_Coverage_Step_P2Values v_Coverage_Step_UpperDensG2 v_Prop_ThetaTwo
  have v_Coverage_Rem_ConjEquivEta : Coverage.Rem_ConjEquivEta := L_Coverage_Rem_ConjEquivEta
      v_Eq_BoundedCofactorComplement v_Eq_DeltaAAsymptotic
  have v_Coverage_Rem_RoughPartBound : Coverage.Rem_RoughPartBound := L_Coverage_Rem_RoughPartBound
      h_Notation_Delta_density
  have v_Coverage_Rem_ConjEquivSmallPrimePart : Coverage.Rem_ConjEquivSmallPrimePart :=
      L_Coverage_Rem_ConjEquivSmallPrimePart v_Coverage_Rem_RoughPartBound
      h_Coverage_Fact_UpperDensCompl
  have v_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl := L_Coverage_Disp_TailLeCompl
      v_Intro_RcntFormula
  have v_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail := L_Coverage_Disp_ComplLeTail
      v_Lem_Moment v_Eq_ExactRepresentability
  have v_Prop_TightnessEquivalence : Prop_TightnessEquivalence := L_Prop_TightnessEquivalence
      v_Coverage_Disp_TailLeCompl v_Coverage_Disp_ComplLeTail h_Coverage_Fact_UpperDensCompl
  have v_Coverage_Rem_T_iff_Conj : Coverage.Rem_T_iff_Conj := L_Coverage_Rem_T_iff_Conj
      h_Coverage_Fact_RtPosIff v_Eq_ExactRepresentability v_Prop_TightnessEquivalence
      v_Intro_RcntFormula
  have v_Fact_DaddDavenportLaw : Fact_DaddDavenportLaw := L_Fact_DaddDavenportLaw v_Cite_Davenport
  have v_Fact_DaddProgressionLaws : Fact_DaddProgressionLaws := L_Fact_DaddProgressionLaws
      i_Cite_PollackAP
  have v_Eq_DaddProgressionDomination : Eq_DaddProgressionDomination :=
      L_Eq_DaddProgressionDomination v_Fact_DaddDavenportLaw v_Fact_DaddProgressionLaws
  have v_Step_DaddWitnessIdentity : Step_DaddWitnessIdentity := L_Step_DaddWitnessIdentity
      h_Eq_Reflection h_Disp_FinalDivisor
  have v_Step_DaddWitnessJointLimit : Step_DaddWitnessJointLimit := L_Step_DaddWitnessJointLimit
      v_Fact_DaddProgressionLaws
  have v_Step_DaddWitnessSupport : Step_DaddWitnessSupport := L_Step_DaddWitnessSupport
      v_Step_DaddWitnessIdentity v_Fact_DaddProgressionLaws
  have v_Step_DaddWitnessCount : Step_DaddWitnessCount := L_Step_DaddWitnessCount
      v_Step_DaddWitnessIdentity v_Step_DaddWitnessJointLimit v_Step_DaddWitnessSupport
      v_Fact_DaddProgressionLaws
  have v_Step_DaddWitnessCofactorTail : Step_DaddWitnessCofactorTail :=
      L_Step_DaddWitnessCofactorTail v_Lem_Moment h_Eq_Reflection
  have v_Step_DaddWitnessPieceBounds : Step_DaddWitnessPieceBounds := L_Step_DaddWitnessPieceBounds
      v_Fact_DaddProgressionLaws
  have v_Prop_DaddWitnessMeans : Prop_DaddWitnessMeans := L_Prop_DaddWitnessMeans
      v_Step_DaddWitnessIdentity v_Step_DaddWitnessCount v_Step_DaddWitnessCofactorTail
      v_Step_DaddWitnessPieceBounds
  have v_Rem_DaddWitnessMeanGrowth : Rem_DaddWitnessMeanGrowth := L_Rem_DaddWitnessMeanGrowth
      v_Prop_ClassFirstMoment v_Prop_DaddWitnessMeans v_Fact_DaddProgressionLaws
  have v_Step_DaddSingularCarrier : Step_DaddSingularCarrier := L_Step_DaddSingularCarrier
      v_Fact_DaddDavenportLaw i_Cite_Erdos_singular
  have v_Step_DaddWitnessMeasureMass : Step_DaddWitnessMeasureMass := L_Step_DaddWitnessMeasureMass
      v_Prop_DaddWitnessMeans v_Fact_DaddProgressionLaws
  have v_Step_DaddWitnessCarrier : Step_DaddWitnessCarrier := L_Step_DaddWitnessCarrier
      v_Fact_DaddDavenportLaw v_Eq_DaddProgressionDomination
  have v_Step_DaddEmpiricalWitnessVague : Step_DaddEmpiricalWitnessVague :=
      L_Step_DaddEmpiricalWitnessVague v_Prop_DaddWitnessMeans v_Step_DaddWitnessMeasureMass
  have v_Step_DaddLimitDomination : Step_DaddLimitDomination := L_Step_DaddLimitDomination
      h_Step_DaddWitnessDomination v_Step_DaddEmpiricalWitnessVague v_Intro_RcntFormula
      v_Step_DaddWitnessMeasureMass
  have v_Thm_DaddUniversalSingularity_Carrier : Thm_DaddUniversalSingularity_Carrier :=
      L_Thm_DaddUniversalSingularity_Carrier v_Step_DaddSingularCarrier v_Step_DaddWitnessCarrier
      v_Step_DaddLimitDomination v_Step_DaddWitnessMeasureMass h_Step_DaddCountDomination
      v_Intro_RcntFormula v_Prop_DaddWitnessMeans v_Thm_SmallValues
      h_EmpiricalMeasures_isProbability
  have v_Thm_DaddUniversalSingularity_FinitePart : Thm_DaddUniversalSingularity_FinitePart :=
      L_Thm_DaddUniversalSingularity_FinitePart v_Thm_DaddUniversalSingularity_Carrier
  have v_Thm_DaddUniversalSingularity_Tight : Thm_DaddUniversalSingularity_Tight :=
      L_Thm_DaddUniversalSingularity_Tight v_Prop_TightnessEquivalence
      v_Thm_DaddUniversalSingularity_FinitePart h_EmpiricalMeasures_isProbability
  have v_Thm_DaddUniversalSingularity : Thm_DaddUniversalSingularity := And.intro
      v_Thm_DaddUniversalSingularity_Carrier (And.intro v_Thm_DaddUniversalSingularity_FinitePart
      v_Thm_DaddUniversalSingularity_Tight)
  have v_Step_DaddXoverR : Step_DaddXoverR := L_Step_DaddXoverR v_Eq_ExactRepresentability
  have v_Step_DaddLowerTailUniform : Step_DaddLowerTailUniform := L_Step_DaddLowerTailUniform
      v_Thm_SmallUpper_doubleExp v_Step_DaddXoverR
  have v_Eq_DaddSubsequentialTail : Eq_DaddSubsequentialTail := L_Eq_DaddSubsequentialTail
      v_Eq_AlmostLogTail v_Thm_DaddUniversalSingularity_Carrier h_EmpiricalMeasures_isProbability
  have v_Cor_DaddHeavyTails_PosMoments : Cor_DaddHeavyTails_PosMoments :=
      L_Cor_DaddHeavyTails_PosMoments v_Eq_AlmostLogTail v_Eq_DaddSubsequentialTail
  have v_Cor_DaddHeavyTails_LogMeans : Cor_DaddHeavyTails_LogMeans := L_Cor_DaddHeavyTails_LogMeans
      v_Eq_AlmostLogTail v_Eq_DaddSubsequentialTail v_Step_DaddLowerTailUniform
  have v_Cor_DaddHeavyTails_InvMoments : Cor_DaddHeavyTails_InvMoments :=
      L_Cor_DaddHeavyTails_InvMoments v_Step_DaddLowerTailUniform
  have v_Cor_DaddHeavyTails_InvMomentConv : Cor_DaddHeavyTails_InvMomentConv :=
      L_Cor_DaddHeavyTails_InvMomentConv v_Cor_DaddHeavyTails_InvMoments
  have v_Cor_DaddHeavyTails_GeomMean : Cor_DaddHeavyTails_GeomMean := L_Cor_DaddHeavyTails_GeomMean
      v_Cor_DaddHeavyTails_LogMeans
  have v_Cor_DaddHeavyTails_Tight : Cor_DaddHeavyTails_Tight := L_Cor_DaddHeavyTails_Tight
      v_Thm_DaddUniversalSingularity_Tight v_Cor_DaddHeavyTails_PosMoments
      v_Cor_DaddHeavyTails_LogMeans
  have v_Cor_DaddHeavyTails : Cor_DaddHeavyTails := And.intro v_Eq_DaddSubsequentialTail (And.intro
      v_Cor_DaddHeavyTails_PosMoments (And.intro v_Cor_DaddHeavyTails_LogMeans (And.intro
      v_Cor_DaddHeavyTails_InvMoments (And.intro v_Cor_DaddHeavyTails_InvMomentConv (And.intro
      v_Cor_DaddHeavyTails_GeomMean v_Cor_DaddHeavyTails_Tight)))))
  have v_Step_DaddCollisionSupport : Step_DaddCollisionSupport := L_Step_DaddCollisionSupport
      v_Lem_SigmaRangeZero v_Intro_RcntFormula h_Coverage_Fact_RtPosIff
  have v_Eq_DaddCollisionCriterion : Eq_DaddCollisionCriterion := L_Eq_DaddCollisionCriterion
      v_Step_DaddCollisionSupport v_Prop_DaddWitnessMeans
  have v_Prop_DaddCollisionCriterion : Prop_DaddCollisionCriterion := L_Prop_DaddCollisionCriterion
      v_Eq_DaddCollisionCriterion v_Intro_RcntFormula v_Thm_DaddUniversalSingularity_Carrier
      h_EmpiricalMeasures_isProbability
  have v_Step_DaddCollisionWitness : Step_DaddCollisionWitness := L_Step_DaddCollisionWitness
      h_Eq_F2Aliquot
  have v_Step_DaddCollisionFirstMoment : Step_DaddCollisionFirstMoment :=
      L_Step_DaddCollisionFirstMoment h_Step_DaddCollisionH h_Step_DaddCollisionCores
  have v_Step_DaddCollisionFirstMomentLaw : Step_DaddCollisionFirstMomentLaw :=
      L_Step_DaddCollisionFirstMomentLaw v_Fact_DaddProgressionLaws h_Step_DaddCollisionCores
      v_Step_DaddCollisionFirstMoment v_Lem_KovacMoment h_Notation_sigmaPrefix_zero
  have v_Step_DaddCollisionSourceIntensity : Step_DaddCollisionSourceIntensity :=
      L_Step_DaddCollisionSourceIntensity h_Eq_DaddCollisionAffine v_Step_DaddWitnessJointLimit
      v_Fact_DaddProgressionLaws v_Step_DaddCollisionFirstMomentLaw
  have v_Step_DaddCollisionCylinder : Step_DaddCollisionCylinder := L_Step_DaddCollisionCylinder
      v_Lem_FixedModulusNormality h_Notation_Delta_density
  have v_Step_DaddCollisionPerCore : Step_DaddCollisionPerCore := L_Step_DaddCollisionPerCore
      v_Step_DaddCollisionSourceIntensity v_Step_DaddCollisionCylinder
  have v_Step_DaddCollisionCombine : Step_DaddCollisionCombine := L_Step_DaddCollisionCombine
      v_Step_DaddCollisionWitness
  have v_Step_DaddCollisionExplicit : Step_DaddCollisionExplicit := L_Step_DaddCollisionExplicit
      v_Step_DaddCollisionPerCore v_Step_DaddCollisionCombine h_Step_DaddCollisionCores
      h_Step_DaddCollisionH h_Step_DaddCollisionArithmetic
  have v_Prop_DaddCollisionLowerBound : Prop_DaddCollisionLowerBound :=
      L_Prop_DaddCollisionLowerBound v_Step_DaddCollisionExplicit h_Step_DaddCollisionArithmetic
  DerivedClaims.mk
    v_Std_PNT
    v_Std_primes_dyadic_lower
    v_Cite_Davenport
    v_Intro_LiminfZero
    v_Fact_KmodFinite
    v_Lem_FmModulus
    v_Rem_RoughInputModulus
    v_Lem_FixedModulusNormality
    v_Lem_SigmaRangeZero
    v_Lem_SigmaRate_OddPrime
    v_Lem_SigmaRate_B2
    v_Lem_SigmaRate
    v_Lem_Moment
    v_Lem_AnalyticOddRepresentability_Bound
    v_Lem_AnalyticOddRepresentability_LittleO
    v_Lem_AnalyticOddRepresentability
    v_Eq_FraitureSmall
    v_Step_FraitureFirstWindowCover
    v_Eq_FraitureFirstWindow
    v_Step_FraitureLargeWindowCover
    v_Step_FraitureLargePrimeSum
    v_Eq_FraitureLargeWindow
    v_Prop_FraitureFinite
    v_Lem_FraitureBalancedGoldbach
    v_Step_FraitureTailEven
    v_Step_FraitureTailOdd
    v_Prop_FraitureTail
    v_Thm_FraitureRepresentability
    v_Eq_ExactRepresentability
    v_Intro_RcntFormula
    v_Thm_FraitureRepresentability_Ge6
    v_KovacMoment_identity
    v_KovacMoment_reduction
    v_Eq_KSprime
    v_Eq_KSsecond
    v_Eq_KS
    v_Lem_KovacMoment
    v_SmallUpper_momentStep
    v_Thm_SmallUpper_doubleExp
    v_Thm_SmallUpper_fixedPower
    v_Thm_SmallUpper
    v_Thm_SmallUpper_upperDens
    v_Intro_LittleO_onlyOnDensityZero
    v_Prop_SmallRatioThreshold
    v_Rem_Lcm289Witness
    v_Eq_SvTwoSided
    v_SvA0_jSum
    v_Lem_SvA0Count
    v_Lem_SvA0
    v_Eq_SmoothPartPeriodCount
    v_Lem_SmoothPartInput
    v_Lem_SvRegular
    v_Lem_SvClasses
    v_Eq_SvKReciprocal
    v_Eq_SvMReciprocal
    v_Claim_SvSigmaDistinct
    v_Claim_SvSievePairs
    v_Eq_SvTotient
    v_Claim_SvA3Reduction
    v_Claim_SvLargeHUnits
    v_Eq_SvLargeHCongruence
    v_Claim_SvLargeHRigidity
    v_Claim_SvLargeH
    v_Claim_SvA322Reduction
    v_Claim_SvSmallHResidues
    v_Eq_SvIntermediateTotient
    v_Eq_SvFSum
    v_Eq_SvQRSum
    v_Claim_SvSmallH
    v_Eq_SvReducedCollisionSum
    v_Prop_SvSecondMoment
    v_Claim_SvClassImage
    v_Claim_SvImageCount
    v_Claim_SvWitness
    v_SvFamilyTarget
    v_Thm_SmallValues
    v_Thm_SmallValues_upperDens
    v_Thm_SmallValues_lowerDens
    v_Eq_SharpPrimeSum
    v_Eq_FixedKernelTail
    v_Eq_MovingKernelTail
    v_Lem_KernelTails
    v_UpperTails_Claim_KA_finite
    v_UpperTails_Claim_VA_periodic
    v_UpperTails_Claim_VA_density
    v_Prop_FmEnvelope
    v_UpperTails_Claim_DeltaPfix
    v_UpperTails_Claim_RoughNotVA
    v_Cor_FmEnvelopeTail
    v_UpperTails_Claim_AlmostLogTail_main
    v_UpperTails_Claim_AlmostLogTail_fixedJ
    v_Eq_AlmostLogTail
    v_Thm_AlmostLogTail_posLowerDens
    v_Thm_AlmostLogTail_limsup
    v_Thm_AlmostLogTail
    v_Intro_ErdosLittleO_fails
    v_Intro_ErdosAlmostAllLittleO_fails
    v_Eq_SharpRoughTargetCount
    v_Eq_SharpBadSourceCount
    v_UpperTails_Claim_SubexpBadPairs
    v_UpperTails_Claim_SubexpWitnessStructure
    v_Eq_MovingKernelLowerBound
    v_UpperTails_Claim_SubexpCoprimeCount
    v_UpperTails_Claim_SubexpLowCofactorSum
    v_UpperTails_Claim_SubexpLowCofactor
    v_UpperTails_Claim_SubexpLargeCofactor
    v_UpperTails_Claim_SubexpCore
    v_UpperTails_Claim_SubexpThreshold
    v_Eq_SubexpGrowth
    v_Eq_PositiveMomentGrowth
    v_Thm_SubexpGrowth
    v_Eq_He
    v_Coverage_Step_ClassResidue
    v_Eq_RepresentingRatio
    v_Coverage_Disp_HeMean
    v_Coverage_Step_GeLowerDens
    v_Eq_ClassLower
    v_Coverage_Disp_MertensCoprimeQ
    v_Coverage_Disp_ClassPrimeSum
    v_Prop_ClassFirstMoment_bound
    v_Prop_ClassFirstMoment_tendsto
    v_Prop_ClassFirstMoment
    v_Cor_FmPrimeCeiling_congr
    v_Cor_FmPrimeCeiling_count
    v_Cor_FmPrimeCeiling_upperDens
    v_Cor_FmPrimeCeiling
    v_Coverage_Rem_SqfreeDefectPos
    v_Cor_FixedCofactorDefect_pos
    v_Eq_FixedCofactorDefect
    v_Cor_FixedCofactorDefect
    v_Coverage_Step_KmodSmallPrime
    v_Coverage_Step_GcovValuesSmallPrime
    v_Coverage_Fact_GcovCoprimeNull
    v_Coverage_Fact_CoprimeComplementDens
    v_Eq_BoundedCofactorComplement
    v_Coverage_Disp_LogPA
    v_Eq_DeltaAAsymptotic
    v_Prop_EtaALower_bound
    v_Prop_EtaALower_tendsto
    v_Prop_EtaALower
    v_Coverage_Rem_EtaDominates
    v_Eq_F2OddNegligible
    v_Eq_OddUntouchables
    v_Coverage_Step_EvenUntouchables
    v_Coverage_Disp_F2Count
    v_Prop_ThetaTwo
    v_Coverage_Step_UpperDensG2
    v_Cor_EtaTwo
    v_Coverage_Rem_ConjEquivEta
    v_Coverage_Rem_RoughPartBound
    v_Coverage_Rem_ConjEquivSmallPrimePart
    v_Coverage_Disp_TailLeCompl
    v_Coverage_Disp_ComplLeTail
    v_Prop_TightnessEquivalence
    v_Coverage_Rem_T_iff_Conj
    v_Fact_DaddDavenportLaw
    v_Fact_DaddProgressionLaws
    v_Eq_DaddProgressionDomination
    v_Step_DaddWitnessIdentity
    v_Step_DaddWitnessJointLimit
    v_Step_DaddWitnessSupport
    v_Step_DaddWitnessCount
    v_Step_DaddWitnessCofactorTail
    v_Step_DaddWitnessPieceBounds
    v_Prop_DaddWitnessMeans
    v_Rem_DaddWitnessMeanGrowth
    v_Step_DaddSingularCarrier
    v_Step_DaddWitnessMeasureMass
    v_Step_DaddWitnessCarrier
    v_Step_DaddEmpiricalWitnessVague
    v_Step_DaddLimitDomination
    v_Thm_DaddUniversalSingularity_Carrier
    v_Thm_DaddUniversalSingularity_FinitePart
    v_Thm_DaddUniversalSingularity_Tight
    v_Thm_DaddUniversalSingularity
    v_Step_DaddXoverR
    v_Step_DaddLowerTailUniform
    v_Eq_DaddSubsequentialTail
    v_Cor_DaddHeavyTails_PosMoments
    v_Cor_DaddHeavyTails_LogMeans
    v_Cor_DaddHeavyTails_InvMoments
    v_Cor_DaddHeavyTails_InvMomentConv
    v_Cor_DaddHeavyTails_GeomMean
    v_Cor_DaddHeavyTails_Tight
    v_Cor_DaddHeavyTails
    v_Step_DaddCollisionSupport
    v_Eq_DaddCollisionCriterion
    v_Prop_DaddCollisionCriterion
    v_Step_DaddCollisionWitness
    v_Step_DaddCollisionFirstMoment
    v_Step_DaddCollisionFirstMomentLaw
    v_Step_DaddCollisionSourceIntensity
    v_Step_DaddCollisionCylinder
    v_Step_DaddCollisionPerCore
    v_Step_DaddCollisionCombine
    v_Step_DaddCollisionExplicit
    v_Prop_DaddCollisionLowerBound

set_option maxRecDepth 20000 in
/-- **All of EP1054** (`Spine.DerivedClaims`, every derived statement of the paper) **without
Montgomery–Vaughan, the two-dimensional sieve or Pollack's Davenport-in-progressions**:
`Proofs.ep1054_all`'s composition retargeted at `noMV_EP1054`, with
`Lem_AnalyticOddRepresentability_Bound` from `lemAOR_ofHelfgott` (Helfgott is already a hypothesis),
`Eq_OddUntouchables` from `eq_OddUntouchables_unconditional`, and `Cite_LP_sieve37`,
`Cite_PollackAP` from their discharges `Proofs.input_Cite_LP_sieve37`,
`Proofs.input_Cite_PollackAP`.

**Remaining hypotheses (12)** (trusted inputs with no Lean proof):
* `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`, `Cite_LP_Lemma25`: Luca–Pomerance Lemmas 2.1,
  2.2 (range form), 2.5.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4.
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound.
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9 (explicit bounds for `π(x)`).
* `Cite_Axler_Cor2`: Axler Corollary 2 (explicit Robin-type bound).
* `Cite_ChenZhao`: Chen–Zhao (nonaliquot numbers have lower density `≥ 0.0602757`).
* `Cite_Erdos_singular`: Erdős, the Davenport law of `σ(n)/n` is purely singular.
* `Comp_Verifier_small`, `Comp_Verifier_window1`, `Comp_Verifier_largeSeed`: the three finite
  verifier computations.

(`Proofs.ep1054_all` takes these twelve plus `Cite_MV_exceptional`, `Cite_LP_sieve37` and
`Cite_PollackAP`.) -/
theorem ep1054_all_r3
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
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
    (h_AOR_Bound := (lemAOR_ofHelfgott i_Cite_Helfgott_weighted).1)
    (h_OddUntouchables := eq_OddUntouchables_unconditional)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := input_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 := i_Cite_Axler_Cor2)
    (i_Cite_ChenZhao := i_Cite_ChenZhao)
    (i_Cite_PollackAP := input_Cite_PollackAP)
    (i_Cite_Erdos_singular := i_Cite_Erdos_singular)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

end Principia.Erdos1054.Alt
