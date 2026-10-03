/-
Copyright (c) 2026 PrincipiaAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PrincipiaAI
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Statements.S1_Main
import Principia.Erdos1054.Statements.S2_Prelim
import Principia.Erdos1054.Statements.S3_Repr
import Principia.Erdos1054.Statements.S4a_SmallUpper
import Principia.Erdos1054.Statements.S4b_SmallValues
import Principia.Erdos1054.Statements.S5_UpperTails
import Principia.Erdos1054.Statements.S6_Coverage
import Principia.Erdos1054.Statements.S7_Limits

/-!
# The spine of EP1054: every inference of the paper, composed as a typing fact

Source: `Campaigns/Erdos-1054/collab-paper/EP1054.tex`. Statements:
  `Principia.Erdos1054.Statements`.
Work-list (the same DAG in topological order): `Campaigns/Erdos-1054/LEAN-WORKLIST.md`.
Both files are GENERATED from one DAG description, so they cannot drift apart: edit
`Campaigns/Erdos-1054/spine-dag/dag.py` and run `python Campaigns/Erdos-1054/spine-dag/gen.py`.

**Nothing here asserts mathematics.** Every step of every proof of the paper is a named
hypothesis, so the composition compiles if and only if the steps line up (project rule: CLAUDE.md,
THE SPINE RULE; worked example `Principia.TwinPrime.Chain.Spine`).

## The four kinds of hypothesis

* `Link_X : Prop := D₁ → ⋯ → Dₖ → X` for every result `X` whose proof uses other statements.
  `D₁ … Dₖ` are exactly the statement `Prop`s and cited inputs the paper's proof of `X` uses
  (Mathlib facts, definitions and the proved `Basic.lean` lemmas are used inside the eventual
  proof and are not listed). An extra `Dᵢ` would make the link weaker than the paper's argument;
  a missing one would make it unprovable.
* A **leaf** is a statement proved from Mathlib and the definitions alone. It enters as a
  hypothesis `h_X : X` and is proved directly.
* An **input** (`Cite_*`, `Std_*`, `Comp_*` of `Statements.Inputs`, sections 1–3) is the trusted
  base. The five *derived* inputs of section 4 are proof obligations, not inputs: `Std_PNT`,
  `Std_primes_dyadic_lower` and `Cite_Davenport` are **links** from `Std_PNT_AP` or
  `Cite_PollackAP`; `Std_Mertens1` is a **leaf** (Chebyshev's bound and partial summation, as the
  paper says at line 1383), and so is `Std_recipPrimesAP_diverges` (Dirichlet's theorem in
  reciprocal form, from Mathlib's pole bound `LSeries_residueClass_lower_bound`; the paper derives
  it from `Std_PNT_AP` at lines 476–478, an edge the spine does not need).
* A result whose statement *is* a conjunction of other results (`Thm_SmallUpper`,
  `Lem_SigmaRate`, …) gets no link: `And.intro` composes it. `Lem_LPInputs` is a conjunction of
  three *inputs*: `And.intro` composes it too, but it is trusted, not claimed.

## Not claimed

`Eq_T` (a question), `Conj_BoundedCofactorWeak` (a conjecture), `Eq_TightnessCriterion` and
`Coverage.NuTight` (a criterion and a definition) are never concluded. The parametrised predicates
`Eq_FmReflection e d`, `Eq_Moment k Ck`, `Eq_SvLP25 X n`, … are components of the results that
contain them, not results. `Note_FraitureVerifierCounts` (lines 839–843) is descriptive verifier
output that no proof consumes and that cannot be discharged without the verifier.
`Rem_FraitureCheckUsage` is a claim about proofs, stated by a signature (next section).

## Input-usage claims: Lean checks "at most", `gen.py` checks "exactly"

`Rem_FraitureCheckUsage` (lines 969–979) says which inputs each representability proof consumes.
As a `Prop` it says nothing, since each conjunct `inputs → X` follows from `X` alone, so it is not a
field of the claims below. Its content is the **signature** of `spine_Rem_FraitureCheckUsage`, which
composes the links of the three sub-DAGs with **only the inputs the remark names** in scope. Lean
therefore checks that each sub-DAG uses **at most** those inputs (an unused binder still
typechecks). That it uses **exactly** those is checked by `gen.py`, by set equality on transitive
closures, and generation fails otherwise.

The paper's other input-usage claims are enforced the same way. The large-value estimates use no
finite representability computation (lines 645–647, 2105–2106, 2223–2224): `gen.py` fixes the
exact trusted inputs of `spine_Thm_AlmostLogTail` and `spine_Thm_SubexpGrowth`, and refuses any DAG
edit that brings the exact classification (`Comp_*`, Dusart, Helfgott, Rosser–Schoenfeld,
`Eq_ExactRepresentability`) into the closure of Theorems 1.1–1.4 or of the introduction's answers
to Erdős's questions.

## Proof style

Every proof is term mode: `have` chains of link applications and `And.intro`, nothing else.
-/

set_option autoImplicit false

namespace Principia.Erdos1054.Spine

/-! ## The links

One per result whose paper proof uses other statements, in topological order (every link's
hypotheses are defined above it). Docstrings give the paper lines of the proof. -/

/-- `Std_PNT`. Paper lines 2530-2533. derived input (Q = 1 of Std_PNT_AP + Chebyshev theta/psi
  comparison). -/
def Link_Std_PNT : Prop :=
    Std_PNT_AP →
    Std_PNT

/-- `Std_primes_dyadic_lower`. Paper lines 1274-1276. derived input (Q = 1 of Std_PNT_AP + Bertrand
  for small t). -/
def Link_Std_primes_dyadic_lower : Prop :=
    Std_PNT_AP →
    Std_primes_dyadic_lower

/-- `Cite_Davenport`. Paper lines 2733-2736. derived input (Q = 1, a = 0 of Cite_PollackAP). -/
def Link_Cite_Davenport : Prop :=
    Cite_PollackAP →
    Cite_Davenport

/-- `Intro_LiminfZero`. Paper lines 105-107. -/
def Link_Intro_LiminfZero : Prop :=
    Intro_f_sigma_le →
    Intro_LiminfZero

/-- `Fact_KmodFinite`. Paper lines 404-405. -/
def Link_Fact_KmodFinite : Prop :=
    Fact_DsetResidue →
    Fact_KmodFinite

/-- `Lem_FmModulus`. Paper lines 406-440. lem:fm-modulus; Fact_KmodGeTwo gives d0 = M/g >= 1 in the
  maximality clause. -/
def Link_Lem_FmModulus : Prop :=
    Fact_KmodGeTwo →
    Lem_FmModulus

/-- `Rem_RoughInputModulus`. Paper lines 441-448. -/
def Link_Rem_RoughInputModulus : Prop :=
    Fact_DsetResidue →
    Lem_FmModulus →
    Rem_RoughInputModulus

/-- `Lem_FixedModulusNormality`. Paper lines 452-480. lem:fixed-modulus-normality. -/
def Link_Lem_FixedModulusNormality : Prop :=
    Std_recipPrimesAP_diverges →
    Lem_FixedModulusNormality

/-- `Lem_SigmaRangeZero`. Paper lines 484-498. lem:sigma-range-zero. -/
def Link_Lem_SigmaRangeZero : Prop :=
    Lem_FixedModulusNormality →
    Lem_SigmaRangeZero

/-- `Lem_SigmaRate_OddPrime`. Paper lines 508-517; proof 521-557. -/
def Link_Lem_SigmaRate_OddPrime : Prop :=
    Cite_Pollack_Lemma24 →
    Std_SiegelWalfisz_dyadic →
    Lem_SigmaRate_OddPrime

/-- `Lem_SigmaRate_B2`. Paper lines 518; proof 558-559. -/
def Link_Lem_SigmaRate_B2 : Prop :=
    Std_sigma_odd_iff →
    Lem_SigmaRate_B2

/-- `Lem_Moment`. Paper lines 565-638. lem:moment; zeta bound from Mathlib ZetaAsymptotics. -/
def Link_Lem_Moment : Prop :=
    Eq_Reflection →
    Lem_Moment

/-- `Lem_AnalyticOddRepresentability_Bound`. Paper lines 651-656; proof 661-670. -/
def Link_Lem_AnalyticOddRepresentability_Bound : Prop :=
    Cite_MV_exceptional →
    Lem_AnalyticOddRepresentability_Bound

/-- `Lem_AnalyticOddRepresentability_LittleO`. Paper lines 658. -/
def Link_Lem_AnalyticOddRepresentability_LittleO : Prop :=
    Lem_AnalyticOddRepresentability_Bound →
    Lem_AnalyticOddRepresentability_LittleO

/-- `Eq_FraitureSmall`. Paper lines 728-731, 746-755. -/
def Link_Eq_FraitureSmall : Prop :=
    Step_FraitureSmallBq →
    Step_FraitureSeven →
    Comp_Verifier_small →
    Eq_FraitureSmall

/-- `Step_FraitureFirstWindowCover`. Paper lines 757-767. -/
def Link_Step_FraitureFirstWindowCover : Prop :=
    Lem_FraitureExtension →
    Comp_Verifier_window1 →
    Step_FraitureFirstWindowCover

/-- `Eq_FraitureFirstWindow`. Paper lines 732-733, 757-769. -/
def Link_Eq_FraitureFirstWindow : Prop :=
    Step_FraitureFirstWindowCover →
    Lem_FraiturePrimeWindow →
    Eq_FraitureFirstWindow

/-- `Step_FraitureLargeWindowCover`. Paper lines 771-792, 820. Bertrand from Mathlib. -/
def Link_Step_FraitureLargeWindowCover : Prop :=
    Lem_FraitureExtension →
    Comp_Verifier_largeSeed →
    Step_FraitureLargeWindowCover

/-- `Step_FraitureLargePrimeSum`. Paper lines 794-819. -/
def Link_Step_FraitureLargePrimeSum : Prop :=
    Cite_Dusart_Thm69 →
    Step_FraitureLargePrimeSum

/-- `Eq_FraitureLargeWindow`. Paper lines 734-735, 771-823. -/
def Link_Eq_FraitureLargeWindow : Prop :=
    Step_FraitureLargeWindowCover →
    Step_FraitureLargePrimeSum →
    Lem_FraiturePrimeWindow →
    Eq_FraitureLargeWindow

/-- `Lem_FraitureBalancedGoldbach`. Paper lines 846-854; proof 856-898.
  lem:fraiture-balanced-goldbach; the paper's reduction of Helfgott's weighted bound (discard
  triples with a coordinate <= z or a repeated coordinate). -/
def Link_Lem_FraitureBalancedGoldbach : Prop :=
    Cite_Helfgott_weighted →
    Cite_RosserSchoenfeld_psi →
    Lem_FraitureBalancedGoldbach

/-- `Step_FraitureTailEven`. Paper lines 912-923. -/
def Link_Step_FraitureTailEven : Prop :=
    Lem_FraitureBalancedGoldbach →
    Step_FraitureTailThreePrimes →
    Step_FraitureTailEven

/-- `Step_FraitureTailOdd`. Paper lines 925-952. Bertrand from Mathlib. -/
def Link_Step_FraitureTailOdd : Prop :=
    Lem_FraitureBalancedGoldbach →
    Step_FraitureTailFourPrimes →
    Step_FraitureTailOdd

/-- `Prop_FraitureTail`. Paper lines 900-953. prop:fraiture-tail. -/
def Link_Prop_FraitureTail : Prop :=
    Step_FraitureTailEven →
    Step_FraitureTailOdd →
    Prop_FraitureTail

/-- `Thm_FraitureRepresentability`. Paper lines 677-684; proof 955-966.
  thm:fraiture-representability; abbrev of Eq_ExactRepresentability (one Link serves both). -/
def Link_Thm_FraitureRepresentability : Prop :=
    Prop_FraitureFinite →
    Prop_FraitureTail →
    Step_FraitureSmallCases →
    Thm_FraitureRepresentability

/-- `Intro_RcntFormula`. Paper lines 230. -/
def Link_Intro_RcntFormula : Prop :=
    Eq_ExactRepresentability →
    Intro_RcntFormula

/-- `Thm_FraitureRepresentability_Ge6`. Paper lines 683. -/
def Link_Thm_FraitureRepresentability_Ge6 : Prop :=
    Thm_FraitureRepresentability →
    Thm_FraitureRepresentability_Ge6

/-- `KovacMoment_identity`. Paper lines 1010-1019. -/
def Link_KovacMoment_identity : Prop :=
    KovacMoment_reflection →
    KovacMoment_identity

/-- `KovacMoment_reduction`. Paper lines 1020-1022. -/
def Link_KovacMoment_reduction : Prop :=
    KovacMoment_identity →
    KovacMoment_reduction

/-- `Eq_KSprime`. Paper lines 1056-1078. -/
def Link_Eq_KSprime : Prop :=
    Std_Mertens2 →
    Eq_KSprime

/-- `Eq_KSsecond`. Paper lines 1082-1111. -/
def Link_Eq_KSsecond : Prop :=
    Std_Mertens2 →
    Eq_KSsecond

/-- `Eq_KS`. Paper lines 1023-1027, 1114. -/
def Link_Eq_KS : Prop :=
    KovacS_le_S1S2 →
    Eq_KSprime →
    Eq_KSsecond →
    Eq_KS

/-- `Lem_KovacMoment`. Paper lines 990-1116. lem:kovac-moment. -/
def Link_Lem_KovacMoment : Prop :=
    KovacMoment_reduction →
    Eq_KS →
    Lem_KovacMoment

/-- `SmallUpper_momentStep`. Paper lines 1129-1133. -/
def Link_SmallUpper_momentStep : Prop :=
    SmallUpper_markov →
    Lem_KovacMoment →
    SmallUpper_momentStep

/-- `Thm_SmallUpper_doubleExp`. Paper lines 140-146; proof 1118-1145. -/
def Link_Thm_SmallUpper_doubleExp : Prop :=
    SmallUpper_emptyCase →
    SmallUpper_momentStep →
    SmallUpper_paramChoice →
    Thm_SmallUpper_doubleExp

/-- `Thm_SmallUpper_fixedPower`. Paper lines 148-149; proof 1145-1147. -/
def Link_Thm_SmallUpper_fixedPower : Prop :=
    Thm_SmallUpper_doubleExp →
    SmallUpper_doubleExpPower →
    Thm_SmallUpper_fixedPower

/-- `Thm_SmallUpper_upperDens`. Paper lines 152-154. -/
def Link_Thm_SmallUpper_upperDens : Prop :=
    Thm_SmallUpper_doubleExp →
    Thm_SmallUpper_upperDens

/-- `Intro_LittleO_onlyOnDensityZero`. Paper lines 79, 152-155. -/
def Link_Intro_LittleO_onlyOnDensityZero : Prop :=
    Thm_SmallUpper_upperDens →
    Intro_LittleO_onlyOnDensityZero

/-- `Prop_SmallRatioThreshold`. Paper lines 1156-1181. unlabeled proposition (f(n) <= n/10 => n >
  10^120). -/
def Link_Prop_SmallRatioThreshold : Prop :=
    SmallRatio_prefixLeSig →
    SmallRatio_abundancySmall →
    SmallRatio_axlerNumeric →
    Cite_Axler_Cor2 →
    Prop_SmallRatioThreshold

/-- `Rem_Lcm289Witness`. Paper lines 1189-1195. -/
def Link_Rem_Lcm289Witness : Prop :=
    Rem_Lcm289Abundant →
    Rem_Lcm289Witness

/-- `Eq_SvTwoSided`. Paper lines 1253-1256; proof 1289-1299. -/
def Link_Eq_SvTwoSided : Prop :=
    SvA0_abundancySubmul →
    Eq_SvTwoSided

/-- `SvA0_jSum`. Paper lines 1267-1273. -/
def Link_SvA0_jSum : Prop :=
    SvA0_sigmaHarmonic →
    SvA0_jSum

/-- `Lem_SvA0Count`. Paper lines 1245-1250; proof 1261-1284. -/
def Link_Lem_SvA0Count : Prop :=
    SvA0_jSum →
    Lem_SvA0Unique →
    Std_primes_dyadic_lower →
    Std_Mertens2 →
    Lem_SvA0Count

/-- `Eq_SmoothPartPeriodCount`. Paper lines 1362-1369. complete periods mod y# give phi(y#)/y#,
  which is Delta y by Notation_Delta_density. -/
def Link_Eq_SmoothPartPeriodCount : Prop :=
    Notation_Delta_density →
    Eq_SmoothPartPeriodCount

/-- `Lem_SmoothPartInput`. Paper lines 1348-1389. lem:smooth-part-input; Std_Mertens1 is derived
  (line 1383), not trusted. -/
def Link_Lem_SmoothPartInput : Prop :=
    Eq_SmoothPartPeriodCount →
    Std_Mertens1 →
    Std_Mertens3 →
    Lem_SmoothPartInput

/-- `Lem_SvRegular`. Paper lines 1394-1480. lem:sv-regular. -/
def Link_Lem_SvRegular : Prop :=
    Lem_SvA0 →
    Lem_LPInputs →
    Eq_SvHarmonicDensityZero →
    Cite_Pollack_Thm14 →
    Std_Mertens2 →
    Lem_SvRegular

/-- `Lem_SvClasses`. Paper lines 1486-1527. lem:sv-classes; the regular family enters as the
  hypothesis SV.RegularFamily, not as Lem_SvRegular. -/
def Link_Lem_SvClasses : Prop :=
    Lem_SmoothPartInput →
    Std_Mertens3 →
    Lem_SvClasses

/-- `Eq_SvKReciprocal`. Paper lines 1545-1552. -/
def Link_Eq_SvKReciprocal : Prop :=
    Eq_SmoothPartPeriodCount →
    Std_Mertens3 →
    Eq_SvKReciprocal

/-- `Eq_SvMReciprocal`. Paper lines 1553-1558. -/
def Link_Eq_SvMReciprocal : Prop :=
    Eq_SvKReciprocal →
    Std_Mertens2 →
    Eq_SvMReciprocal

/-- `Claim_SvSigmaDistinct`. Paper lines 1572-1580. -/
def Link_Claim_SvSigmaDistinct : Prop :=
    Eq_SvTwoSided →
    Eq_SvCollision →
    Claim_SvSigmaDistinct

/-- `Claim_SvSievePairs`. Paper lines 1588-1618. -/
def Link_Claim_SvSievePairs : Prop :=
    Claim_SvSigmaDistinct →
    Eq_SvCollision →
    Eq_SvTwoSided →
    Cite_LP_sieve37 →
    Claim_SvSievePairs

/-- `Eq_SvTotient`. Paper lines 1620-1629. -/
def Link_Eq_SvTotient : Prop :=
    Std_totient_sigma →
    Eq_SvTotient

/-- `Claim_SvA3Reduction`. Paper lines 1631-1646. -/
def Link_Claim_SvA3Reduction : Prop :=
    Eq_SvTwoSided →
    Std_Mertens3 →
    Claim_SvA3Reduction

/-- `Claim_SvLargeHUnits`. Paper lines 1663-1676. -/
def Link_Claim_SvLargeHUnits : Prop :=
    Eq_SvCollision →
    Claim_SvLargeHUnits

/-- `Eq_SvLargeHCongruence`. Paper lines 1677-1684. -/
def Link_Eq_SvLargeHCongruence : Prop :=
    Eq_SvCollision →
    Eq_SvLargeHCongruence

/-- `Claim_SvLargeHRigidity`. Paper lines 1663-1708. Eq_SvCollision: s(n) = q s(l) + sigma(l), lines
  1666, 1717-1718 (F5). -/
def Link_Claim_SvLargeHRigidity : Prop :=
    Eq_SvLargeHCongruence →
    Eq_SvTwoSided →
    Claim_SvLargeHUnits →
    Eq_SvCollision →
    Claim_SvLargeHRigidity

/-- `Claim_SvLargeH`. Paper lines 1710-1731. -/
def Link_Claim_SvLargeH : Prop :=
    Claim_SvLargeHRigidity →
    Std_divisorBound →
    Std_Mertens2 →
    Claim_SvLargeH

/-- `Claim_SvA322Reduction`. Paper lines 1733-1739. -/
def Link_Claim_SvA322Reduction : Prop :=
    Eq_SvTotient →
    Claim_SvA322Reduction

/-- `Claim_SvSmallHResidues`. Paper lines 1749-1758. -/
def Link_Claim_SvSmallHResidues : Prop :=
    Eq_SvCollision →
    Claim_SvSmallHResidues

/-- `Eq_SvIntermediateTotient`. Paper lines 1763-1778. Eq_SvCollision: dh divides sigma(n) -
  sigma(n') because SV.A3 uses floor division, lines 1572-1573 (F4). -/
def Link_Eq_SvIntermediateTotient : Prop :=
    Eq_SvCollision →
    Std_Mertens2 →
    Eq_SvIntermediateTotient

/-- `Eq_SvFSum`. Paper lines 1780-1815. -/
def Link_Eq_SvFSum : Prop :=
    Eq_SvTotient →
    Std_BrunTitchmarsh →
    Eq_SvFSum

/-- `Eq_SvQRSum`. Paper lines 1816-1827. -/
def Link_Eq_SvQRSum : Prop :=
    Eq_SvFSum →
    Eq_SvTotient →
    Std_BrunTitchmarsh →
    Eq_SvQRSum

/-- `Claim_SvSmallH`. Paper lines 1733-1859. -/
def Link_Claim_SvSmallH : Prop :=
    Claim_SvA322Reduction →
    Claim_SvSmallHSquarefree →
    Claim_SvSmallHResidues →
    Claim_SvResiduePairCount →
    Eq_SvIntermediateTotient →
    Eq_SvQRSum →
    Eq_SvKReciprocal →
    Eq_SvMReciprocal →
    Std_divisorBound →
    Claim_SvSmallH

/-- `Eq_SvReducedCollisionSum`. Paper lines 1647-1657. -/
def Link_Eq_SvReducedCollisionSum : Prop :=
    Claim_SvLargeH →
    Claim_SvSmallH →
    Eq_SvReducedCollisionSum

/-- `Prop_SvSecondMoment`. Paper lines 1531-1860. prop:sv-second-moment; diagonal from the
  SV.ClassesAt hypothesis. -/
def Link_Prop_SvSecondMoment : Prop :=
    Eq_SvCollision →
    Claim_SvSievePairs →
    Eq_SvTotient →
    Claim_SvA3Reduction →
    Eq_SvReducedCollisionSum →
    Prop_SvSecondMoment

/-- `Claim_SvClassImage`. Paper lines 1863-1869. -/
def Link_Claim_SvClassImage : Prop :=
    Claim_SvCauchySchwarz →
    Prop_SvSecondMoment →
    Claim_SvClassImage

/-- `Claim_SvImageCount`. Paper lines 1870-1876. -/
def Link_Claim_SvImageCount : Prop :=
    Lem_SvClasses →
    Claim_SvClassImage →
    Claim_SvImageCount

/-- `Claim_SvWitness`. Paper lines 1877-1882. -/
def Link_Claim_SvWitness : Prop :=
    Eq_SvBasic →
    Eq_SvTwoSided →
    Claim_SvWitness

/-- `SvFamilyTarget`. Paper lines 1217-1222. -/
def Link_SvFamilyTarget : Prop :=
    Eq_SvD →
    Lem_SvRegular →
    Claim_SvImageCount →
    Claim_SvWitness →
    SvFamilyTarget

/-- `Thm_SmallValues`. Paper lines 159-164; proof 1217-1222, 1862-1884. thm:small-values (Theorem
  1.2); rescaling X, delta > 1 from delta = 1. -/
def Link_Thm_SmallValues : Prop :=
    SvFamilyTarget →
    Eq_SvBasic →
    Thm_SmallValues

/-- `Thm_SmallValues_upperDens`. Paper lines 169-171. -/
def Link_Thm_SmallValues_upperDens : Prop :=
    Thm_SmallValues →
    Thm_SmallValues_upperDens

/-- `Thm_SmallValues_lowerDens`. Paper lines 79. -/
def Link_Thm_SmallValues_lowerDens : Prop :=
    Thm_SmallValues →
    Thm_SmallValues_lowerDens

/-- `Eq_SharpPrimeSum`. Paper lines 1940-1948. -/
def Link_Eq_SharpPrimeSum : Prop :=
    Std_Mertens2 →
    Eq_SharpPrimeSum

/-- `Eq_FixedKernelTail`. Paper lines 1904-1915, 1927-1977. -/
def Link_Eq_FixedKernelTail : Prop :=
    Eq_RankinKernel →
    Eq_SharpPrimeSum →
    UpperTails.Claim_EulerHigherTerms →
    Eq_FixedKernelTail

/-- `Eq_MovingKernelTail`. Paper lines 1916-1925, 1927-1977. -/
def Link_Eq_MovingKernelTail : Prop :=
    Eq_RankinKernel →
    Eq_SharpPrimeSum →
    UpperTails.Claim_EulerHigherTerms →
    Eq_MovingKernelTail

/-- `UpperTails.Claim_KA_finite`. Paper lines 1989-1991. d0 = M/g has the same D
  (Lem_FmModulus_Divides) and d0 <= M | Lambda(A). -/
def Link_UpperTails_Claim_KA_finite : Prop :=
    Lem_FmModulus →
    Fact_KmodGeTwo →
    UpperTails.Claim_KA_finite

/-- `UpperTails.Claim_VA_periodic`. Paper lines 1995. -/
def Link_UpperTails_Claim_VA_periodic : Prop :=
    UpperTails.Claim_KA_finite →
    UpperTails.Claim_VA_periodic

/-- `UpperTails.Claim_VA_density`. Paper lines 1995-2001. K >= 2 puts every N coprime to W_A in
  V_A. -/
def Link_UpperTails_Claim_VA_density : Prop :=
    UpperTails.Claim_KA_finite →
    UpperTails.Claim_VA_periodic →
    Fact_KmodGeTwo →
    UpperTails.Claim_VA_density

/-- `Prop_FmEnvelope`. Paper lines 2002-2023. prop:fm-envelope. -/
def Link_Prop_FmEnvelope : Prop :=
    Lem_SigmaRangeZero →
    Lem_FmModulus →
    Lem_FixedModulusNormality →
    UpperTails.Claim_KA_finite →
    UpperTails.Claim_VA_density →
    Prop_FmEnvelope

/-- `UpperTails.Claim_DeltaPfix`. Paper lines 2036-2041. -/
def Link_UpperTails_Claim_DeltaPfix : Prop :=
    Std_Mertens3 →
    UpperTails.Claim_DeltaPfix

/-- `UpperTails.Claim_RoughNotVA`. Paper lines 2045-2061. C >= M >= e (Fact_KmodGeTwo), D = {j<e : j
  | M} needs M | ed (Lem_FmModulus). -/
def Link_UpperTails_Claim_RoughNotVA : Prop :=
    Lem_FmModulus →
    Fact_KmodGeTwo →
    UpperTails.Claim_KA_finite →
    Notation_Delta_density →
    UpperTails.Claim_RoughNotVA

/-- `Cor_FmEnvelopeTail`. Paper lines 2025-2062. cor:fm-envelope-tail. -/
def Link_Cor_FmEnvelopeTail : Prop :=
    UpperTails.Claim_VA_rough →
    UpperTails.Claim_VA_density →
    Notation_Delta_density →
    UpperTails.Claim_DeltaPfix →
    UpperTails.Claim_RoughNotVA →
    Eq_FixedKernelTail →
    Cor_FmEnvelopeTail

/-- `UpperTails.Claim_AlmostLogTail_main`. Paper lines 2073-2092. -/
def Link_UpperTails_Claim_AlmostLogTail_main : Prop :=
    Prop_FmEnvelope →
    Lem_Moment →
    UpperTails.Claim_AlmostLogTail_momentArith →
    UpperTails.Claim_VA_rough →
    UpperTails.Claim_RoughNonsquarefree →
    Lem_AnalyticOddRepresentability →
    UpperTails.Claim_VA_density →
    UpperTails.Claim_AlmostLogTail_main

/-- `UpperTails.Claim_AlmostLogTail_fixedJ`. Paper lines 2093-2104. -/
def Link_UpperTails_Claim_AlmostLogTail_fixedJ : Prop :=
    UpperTails.Claim_AlmostLogTail_main →
    Cor_FmEnvelopeTail →
    UpperTails.Claim_LscaleRatio →
    UpperTails.Claim_AlmostLogTail_fixedJ

/-- `Eq_AlmostLogTail`. Paper lines 176-183; proof 2066-2107 (j -> infinity at 2103-2105). -/
def Link_Eq_AlmostLogTail : Prop :=
    UpperTails.Claim_AlmostLogTail_fixedJ →
    Eq_AlmostLogTail

/-- `Thm_AlmostLogTail_posLowerDens`. Paper lines 184-185. -/
def Link_Thm_AlmostLogTail_posLowerDens : Prop :=
    Eq_AlmostLogTail →
    Thm_AlmostLogTail_posLowerDens

/-- `Thm_AlmostLogTail_limsup`. Paper lines 185-188. -/
def Link_Thm_AlmostLogTail_limsup : Prop :=
    Thm_AlmostLogTail_posLowerDens →
    Thm_AlmostLogTail_limsup

/-- `Intro_ErdosLittleO_fails`. Paper lines 108. -/
def Link_Intro_ErdosLittleO_fails : Prop :=
    Thm_AlmostLogTail_limsup →
    Intro_ErdosLittleO_fails

/-- `Intro_ErdosAlmostAllLittleO_fails`. Paper lines 108-109, 155, 192. -/
def Link_Intro_ErdosAlmostAllLittleO_fails : Prop :=
    Thm_AlmostLogTail_posLowerDens →
    Intro_ErdosAlmostAllLittleO_fails

/-- `Eq_SharpRoughTargetCount`. Paper lines 2122-2129. complete periods mod P# give phi(P#)/P# =
  Delta(P). -/
def Link_Eq_SharpRoughTargetCount : Prop :=
    Notation_Delta_density →
    Std_Mertens3 →
    Eq_SharpRoughTargetCount

/-- `Eq_SharpBadSourceCount`. Paper lines 2135-2144. -/
def Link_Eq_SharpBadSourceCount : Prop :=
    Lem_SigmaRate →
    Eq_SharpBadSourceCount

/-- `UpperTails.Claim_SubexpBadPairs`. Paper lines 2145-2153. -/
def Link_UpperTails_Claim_SubexpBadPairs : Prop :=
    Eq_SharpBadSourceCount →
    Eq_SharpRoughTargetCount →
    UpperTails.Claim_SubexpBadPairs

/-- `UpperTails.Claim_SubexpWitnessStructure`. Paper lines 2157-2181. e | L gives g = e, then C >= L
  >= 2 is Fact_KmodGeTwo. -/
def Link_UpperTails_Claim_SubexpWitnessStructure : Prop :=
    Lem_FmModulus →
    Fact_KmodGeTwo →
    UpperTails.Claim_SubexpWitnessStructure

/-- `Eq_MovingKernelLowerBound`. Paper lines 2176-2185. -/
def Link_Eq_MovingKernelLowerBound : Prop :=
    UpperTails.Claim_SubexpWitnessStructure →
    UpperTails.Claim_SubexpFltP →
    Std_Mertens3 →
    Eq_MovingKernelLowerBound

/-- `UpperTails.Claim_SubexpCoprimeCount`. Paper lines 2187-2197. Chebyshev (Mathlib) + complete
  periods (Density.lean); phi(P#)/P# = Delta(P) is Notation_Delta_density. -/
def Link_UpperTails_Claim_SubexpCoprimeCount : Prop :=
    Notation_Delta_density →
    UpperTails.Claim_SubexpCoprimeCount

/-- `UpperTails.Claim_SubexpLowCofactorSum`. Paper lines 2198-2204. -/
def Link_UpperTails_Claim_SubexpLowCofactorSum : Prop :=
    UpperTails.Claim_SubexpWitnessStructure →
    Eq_MovingKernelLowerBound →
    UpperTails.Claim_SubexpCoprimeCount →
    UpperTails.Claim_SubexpFltP →
    UpperTails.Claim_SubexpLowCofactorSum

/-- `UpperTails.Claim_SubexpLowCofactor`. Paper lines 2202-2207. -/
def Link_UpperTails_Claim_SubexpLowCofactor : Prop :=
    UpperTails.Claim_SubexpLowCofactorSum →
    Eq_MovingKernelTail →
    UpperTails.Claim_SubexpLowCofactor

/-- `UpperTails.Claim_SubexpLargeCofactor`. Paper lines 2209-2218. -/
def Link_UpperTails_Claim_SubexpLargeCofactor : Prop :=
    Std_Mertens3 →
    UpperTails.Claim_SubexpLargeCofactor

/-- `UpperTails.Claim_SubexpCore`. Paper lines 2219-2224. -/
def Link_UpperTails_Claim_SubexpCore : Prop :=
    Eq_SharpRoughTargetCount →
    UpperTails.Claim_RoughNonsquarefree →
    UpperTails.Claim_SubexpBadPairs →
    UpperTails.Claim_SubexpCofactorOne →
    UpperTails.Claim_SubexpLowCofactor →
    UpperTails.Claim_SubexpLargeCofactor →
    Lem_Moment →
    Lem_AnalyticOddRepresentability →
    UpperTails.Claim_SubexpCore

/-- `UpperTails.Claim_SubexpThreshold`. Paper lines 2230-2233. -/
def Link_UpperTails_Claim_SubexpThreshold : Prop :=
    UpperTails.Claim_SubexpLogT →
    UpperTails.Claim_SubexpThreshold

/-- `Eq_SubexpGrowth`. Paper lines 196-208; proof 2111-2233. -/
def Link_Eq_SubexpGrowth : Prop :=
    UpperTails.Claim_SubexpCore →
    UpperTails.Claim_SubexpThreshold →
    Eq_SubexpGrowth

/-- `Eq_PositiveMomentGrowth`. Paper lines 209-216; proof 2235-2243. -/
def Link_Eq_PositiveMomentGrowth : Prop :=
    Eq_SubexpGrowth →
    Eq_PositiveMomentGrowth

/-- `Eq_He`. Paper lines 2348-2353. -/
def Link_Eq_He : Prop :=
    Coverage.Step_SeDensity →
    Eq_He

/-- `Coverage.Step_ClassResidue`. Paper lines 2354-2358. -/
def Link_Coverage_Step_ClassResidue : Prop :=
    Eq_He →
    Coverage.Step_ClassResidue

/-- `Eq_RepresentingRatio`. Paper lines 2359-2362. -/
def Link_Eq_RepresentingRatio : Prop :=
    Eq_He →
    Eq_RepresentingRatio

/-- `Coverage.Disp_HeMean`. Paper lines 2372-2382. -/
def Link_Coverage_Disp_HeMean : Prop :=
    Coverage.Step_HeRatio →
    Coverage.Step_SeDensity →
    Coverage.Step_SeMultiplesDens →
    Coverage.Disp_CoprimeSqTail →
    Coverage.Disp_HeMean

/-- `Coverage.Step_GeLowerDens`. Paper lines 2389-2394. -/
def Link_Coverage_Step_GeLowerDens : Prop :=
    Coverage.Step_SeDensity →
    Coverage.Disp_HeMean →
    Coverage.Step_GeLowerDens

/-- `Eq_ClassLower`. Paper lines 2396-2417. u from Eq_UClass; Lem_Moment with Eq_Reflection bounds
  the pair count, so the sequence is bounded and Mathlib liminf is genuine. -/
def Link_Eq_ClassLower : Prop :=
    Eq_UClass →
    Coverage.Step_GeLowerDens →
    Eq_He →
    Coverage.Step_ClassResidue →
    Eq_RepresentingRatio →
    Coverage.Step_DistinctPairs →
    Lem_Moment →
    Eq_Reflection →
    Eq_ClassLower

/-- `Coverage.Disp_MertensCoprimeQ`. Paper lines 2418-2423. -/
def Link_Coverage_Disp_MertensCoprimeQ : Prop :=
    Std_Mertens3 →
    Coverage.Disp_MertensCoprimeQ

/-- `Coverage.Disp_ClassPrimeSum`. Paper lines 2424-2430. -/
def Link_Coverage_Disp_ClassPrimeSum : Prop :=
    Std_PNT_AP →
    Coverage.Disp_ClassPrimeSum

/-- `Prop_ClassFirstMoment_bound`. Paper lines 2292-2299; proof 2304-2435. h from Eq_HGcd;
  Lem_Moment boundedness is consumed inside Eq_ClassLower, not here. -/
def Link_Prop_ClassFirstMoment_bound : Prop :=
    Eq_HGcd →
    Eq_ClassLower →
    Coverage.Disp_MertensCoprimeQ →
    Coverage.Disp_ClassPrimeSum →
    Prop_ClassFirstMoment_bound

/-- `Prop_ClassFirstMoment_tendsto`. Paper lines 2300-2301. -/
def Link_Prop_ClassFirstMoment_tendsto : Prop :=
    Prop_ClassFirstMoment_bound →
    Prop_ClassFirstMoment_tendsto

/-- `Cor_FmPrimeCeiling_congr`. Paper lines 2448-2450. -/
def Link_Cor_FmPrimeCeiling_congr : Prop :=
    Lem_FmModulus →
    Cor_FmPrimeCeiling_congr

/-- `Cor_FmPrimeCeiling_count`. Paper lines 2451-2454. -/
def Link_Cor_FmPrimeCeiling_count : Prop :=
    Cor_FmPrimeCeiling_congr →
    Disp_FinalDivisor →
    Lem_FixedModulusNormality →
    Cor_FmPrimeCeiling_count

/-- `Cor_FmPrimeCeiling_upperDens`. Paper lines 2455. -/
def Link_Cor_FmPrimeCeiling_upperDens : Prop :=
    Cor_FmPrimeCeiling_count →
    Cor_FmPrimeCeiling_upperDens

/-- `Coverage.Rem_SqfreeDefectPos`. Paper lines 2486. -/
def Link_Coverage_Rem_SqfreeDefectPos : Prop :=
    Eq_AlmostLogTail →
    Coverage.Rem_SqfreeDefectPos

/-- `Cor_FixedCofactorDefect_pos`. Paper lines 2488-2491. -/
def Link_Cor_FixedCofactorDefect_pos : Prop :=
    Eq_AlmostLogTail →
    Cor_FixedCofactorDefect_pos

/-- `Eq_FixedCofactorDefect`. Paper lines 2492-2498. -/
def Link_Eq_FixedCofactorDefect : Prop :=
    Eq_AlmostLogTail →
    Eq_FixedCofactorDefect

/-- `Coverage.Step_KmodSmallPrime`. Paper lines 2513-2516. -/
def Link_Coverage_Step_KmodSmallPrime : Prop :=
    Fact_KmodGeTwo →
    Coverage.Step_KmodSmallPrime

/-- `Coverage.Step_GcovValuesSmallPrime`. Paper lines 2516-2519. -/
def Link_Coverage_Step_GcovValuesSmallPrime : Prop :=
    Coverage.Step_KmodSmallPrime →
    Fact_KmodFinite →
    Lem_FmModulus →
    Lem_FixedModulusNormality →
    Coverage.Step_GcovValuesSmallPrime

/-- `Coverage.Fact_GcovCoprimeNull`. Paper lines 2516-2523. -/
def Link_Coverage_Fact_GcovCoprimeNull : Prop :=
    Coverage.Step_GcovValuesSmallPrime →
    Lem_SigmaRangeZero →
    Coverage.Fact_GcovCoprimeNull

/-- `Coverage.Fact_CoprimeComplementDens`. Paper lines 2524-2526. -/
def Link_Coverage_Fact_CoprimeComplementDens : Prop :=
    Coverage.Fact_GcovCoprimeNull →
    Notation_Delta_density →
    Coverage.Fact_CoprimeComplementDens

/-- `Eq_BoundedCofactorComplement`. Paper lines 2526-2529. -/
def Link_Eq_BoundedCofactorComplement : Prop :=
    Coverage.Fact_CoprimeComplementDens →
    Coverage.Fact_UpperDensCompl →
    Eq_BoundedCofactorComplement

/-- `Coverage.Disp_LogPA`. Paper lines 2530-2532. -/
def Link_Coverage_Disp_LogPA : Prop :=
    Std_PNT →
    Coverage.Disp_LogPA

/-- `Eq_DeltaAAsymptotic`. Paper lines 2530-2535. -/
def Link_Eq_DeltaAAsymptotic : Prop :=
    Coverage.Disp_LogPA →
    Std_Mertens3 →
    Eq_DeltaAAsymptotic

/-- `Prop_EtaALower_bound`. Paper lines 2543-2547. -/
def Link_Prop_EtaALower_bound : Prop :=
    Eq_FixedCofactorDefect →
    Coverage.Fact_UpperDensCompl →
    Eq_DeltaAAsymptotic →
    Eq_BoundedCofactorComplement →
    Prop_EtaALower_bound

/-- `Prop_EtaALower_tendsto`. Paper lines 2547. -/
def Link_Prop_EtaALower_tendsto : Prop :=
    Prop_EtaALower_bound →
    Prop_EtaALower_tendsto

/-- `Coverage.Rem_EtaDominates`. Paper lines 2537-2538, 2559-2562. -/
def Link_Coverage_Rem_EtaDominates : Prop :=
    Prop_EtaALower_tendsto →
    Eq_DeltaAAsymptotic →
    Eq_BoundedCofactorComplement →
    Coverage.Rem_EtaDominates

/-- `Eq_F2OddNegligible`. Paper lines 2587-2594. -/
def Link_Eq_F2OddNegligible : Prop :=
    Eq_F2Aliquot →
    Std_sigma_odd_iff →
    Eq_F2OddNegligible

/-- `Eq_OddUntouchables`. Paper lines 2596-2605. -/
def Link_Eq_OddUntouchables : Prop :=
    Cite_MV_exceptional →
    Eq_OddUntouchables

/-- `Coverage.Step_EvenUntouchables`. Paper lines 2610-2612. -/
def Link_Coverage_Step_EvenUntouchables : Prop :=
    Eq_OddUntouchables →
    Cite_ChenZhao →
    Coverage.Step_EvenUntouchables

/-- `Coverage.Disp_F2Count`. Paper lines 2612-2619. -/
def Link_Coverage_Disp_F2Count : Prop :=
    Eq_F2Aliquot →
    Eq_F2OddNegligible →
    Coverage.Step_EvenUntouchables →
    Coverage.Disp_F2Count

/-- `Prop_ThetaTwo`. Paper lines 2569-2620. prop:theta-two. -/
def Link_Prop_ThetaTwo : Prop :=
    Coverage.Disp_F2Count →
    Prop_ThetaTwo

/-- `Coverage.Step_UpperDensG2`. Paper lines 2635-2636. -/
def Link_Coverage_Step_UpperDensG2 : Prop :=
    Coverage.Step_G2Decomp →
    Lem_SigmaRangeZero →
    Coverage.Step_UpperDensG2

/-- `Cor_EtaTwo`. Paper lines 2623-2645. unlabeled corollary (eta_2). -/
def Link_Cor_EtaTwo : Prop :=
    Eq_BoundedCofactorComplement →
    Coverage.Step_P2Values →
    Coverage.Step_UpperDensG2 →
    Prop_ThetaTwo →
    Cor_EtaTwo

/-- `Coverage.Rem_ConjEquivEta`. Paper lines 2655-2660. -/
def Link_Coverage_Rem_ConjEquivEta : Prop :=
    Eq_BoundedCofactorComplement →
    Eq_DeltaAAsymptotic →
    Coverage.Rem_ConjEquivEta

/-- `Coverage.Rem_RoughPartBound`. Paper lines 2662-2666. Delta(A) -> 0 from
  Nat.Primes.not_summable_one_div (Mathlib). -/
def Link_Coverage_Rem_RoughPartBound : Prop :=
    Notation_Delta_density →
    Coverage.Rem_RoughPartBound

/-- `Coverage.Rem_ConjEquivSmallPrimePart`. Paper lines 2667-2670. -/
def Link_Coverage_Rem_ConjEquivSmallPrimePart : Prop :=
    Coverage.Rem_RoughPartBound →
    Coverage.Fact_UpperDensCompl →
    Coverage.Rem_ConjEquivSmallPrimePart

/-- `Coverage.Disp_TailLeCompl`. Paper lines 2689-2700. normalisation R(X) = X + O(1); the inclusion
  is f_le_of_F + F_ge (Basic). -/
def Link_Coverage_Disp_TailLeCompl : Prop :=
    Intro_RcntFormula →
    Coverage.Disp_TailLeCompl

/-- `Coverage.Disp_ComplLeTail`. Paper lines 2706-2713. only 2, 5 unrepresented; R(X) <= X is
  trivial. -/
def Link_Coverage_Disp_ComplLeTail : Prop :=
    Lem_Moment →
    Eq_ExactRepresentability →
    Coverage.Disp_ComplLeTail

/-- `Prop_TightnessEquivalence`. Paper lines 2674-2717. prop:tightness-equivalence (bounded X:
  finitely many ratios). -/
def Link_Prop_TightnessEquivalence : Prop :=
    Coverage.Disp_TailLeCompl →
    Coverage.Disp_ComplLeTail →
    Coverage.Fact_UpperDensCompl →
    Prop_TightnessEquivalence

/-- `Coverage.Rem_T_iff_Conj`. Paper lines 2719-2722. -/
def Link_Coverage_Rem_T_iff_Conj : Prop :=
    Coverage.Fact_RtPosIff →
    Eq_ExactRepresentability →
    Prop_TightnessEquivalence →
    Intro_RcntFormula →
    Coverage.Rem_T_iff_Conj

/-- `Fact_DaddDavenportLaw`. Paper lines 2733-2736. -/
def Link_Fact_DaddDavenportLaw : Prop :=
    Cite_Davenport →
    Fact_DaddDavenportLaw

/-- `Fact_DaddProgressionLaws`. Paper lines 2734-2743. -/
def Link_Fact_DaddProgressionLaws : Prop :=
    Cite_PollackAP →
    Fact_DaddProgressionLaws

/-- `Eq_DaddProgressionDomination`. Paper lines 2744-2748. -/
def Link_Eq_DaddProgressionDomination : Prop :=
    Fact_DaddDavenportLaw →
    Fact_DaddProgressionLaws →
    Eq_DaddProgressionDomination

/-- `Step_DaddWitnessIdentity`. Paper lines 2774-2781. -/
def Link_Step_DaddWitnessIdentity : Prop :=
    Eq_Reflection →
    Disp_FinalDivisor →
    Step_DaddWitnessIdentity

/-- `Step_DaddWitnessJointLimit`. Paper lines 2787-2797. -/
def Link_Step_DaddWitnessJointLimit : Prop :=
    Fact_DaddProgressionLaws →
    Step_DaddWitnessJointLimit

/-- `Step_DaddWitnessSupport`. Paper lines 2801-2803. -/
def Link_Step_DaddWitnessSupport : Prop :=
    Step_DaddWitnessIdentity →
    Fact_DaddProgressionLaws →
    Step_DaddWitnessSupport

/-- `Step_DaddWitnessCount`. Paper lines 2782-2814. -/
def Link_Step_DaddWitnessCount : Prop :=
    Step_DaddWitnessIdentity →
    Step_DaddWitnessJointLimit →
    Step_DaddWitnessSupport →
    Fact_DaddProgressionLaws →
    Step_DaddWitnessCount

/-- `Step_DaddWitnessCofactorTail`. Paper lines 2815-2824. -/
def Link_Step_DaddWitnessCofactorTail : Prop :=
    Lem_Moment →
    Eq_Reflection →
    Step_DaddWitnessCofactorTail

/-- `Step_DaddWitnessPieceBounds`. Paper lines 2826-2827. -/
def Link_Step_DaddWitnessPieceBounds : Prop :=
    Fact_DaddProgressionLaws →
    Step_DaddWitnessPieceBounds

/-- `Prop_DaddWitnessMeans`. Paper lines 2752-2829. prop:dadd:witness-means. -/
def Link_Prop_DaddWitnessMeans : Prop :=
    Step_DaddWitnessIdentity →
    Step_DaddWitnessCount →
    Step_DaddWitnessCofactorTail →
    Step_DaddWitnessPieceBounds →
    Prop_DaddWitnessMeans

/-- `Rem_DaddWitnessMeanGrowth`. Paper lines 2831-2833. w_1 <= 1 needs nu_{0,1} (mass 1, support h
  >= 1), not Fact_DaddDavenportLaw. -/
def Link_Rem_DaddWitnessMeanGrowth : Prop :=
    Prop_ClassFirstMoment →
    Prop_DaddWitnessMeans →
    Fact_DaddProgressionLaws →
    Rem_DaddWitnessMeanGrowth

/-- `Step_DaddSingularCarrier`. Paper lines 2858-2862. -/
def Link_Step_DaddSingularCarrier : Prop :=
    Fact_DaddDavenportLaw →
    Cite_Erdos_singular →
    Step_DaddSingularCarrier

/-- `Step_DaddWitnessMeasureMass`. Paper lines 2876-2881. -/
def Link_Step_DaddWitnessMeasureMass : Prop :=
    Prop_DaddWitnessMeans →
    Fact_DaddProgressionLaws →
    Step_DaddWitnessMeasureMass

/-- `Step_DaddWitnessCarrier`. Paper lines 2880-2892. -/
def Link_Step_DaddWitnessCarrier : Prop :=
    Fact_DaddDavenportLaw →
    Eq_DaddProgressionDomination →
    Step_DaddWitnessCarrier

/-- `Step_DaddEmpiricalWitnessVague`. Paper lines 2901-2903. -/
def Link_Step_DaddEmpiricalWitnessVague : Prop :=
    Prop_DaddWitnessMeans →
    Step_DaddWitnessMeasureMass →
    Step_DaddEmpiricalWitnessVague

/-- `Step_DaddLimitDomination`. Paper lines 2910-2916. Step_DaddWitnessMeasureMass (lines 2876-2881)
  passes from C_c+ to setwise domination; without it the step fails for a lower-integral encoding of
  the vague limit (F3). -/
def Link_Step_DaddLimitDomination : Prop :=
    Step_DaddWitnessDomination →
    Step_DaddEmpiricalWitnessVague →
    Intro_RcntFormula →
    Step_DaddWitnessMeasureMass →
    Step_DaddLimitDomination

/-- `Thm_DaddUniversalSingularity_Carrier`. Paper lines 2839-2848; proof 2857-2934. portmanteau both
  directions (Mathlib: ProbabilityMeasure) needs nu_X probability. -/
def Link_Thm_DaddUniversalSingularity_Carrier : Prop :=
    Step_DaddSingularCarrier →
    Step_DaddWitnessCarrier →
    Step_DaddLimitDomination →
    Step_DaddWitnessMeasureMass →
    Step_DaddCountDomination →
    Intro_RcntFormula →
    Prop_DaddWitnessMeans →
    Thm_SmallValues →
    EmpiricalMeasures_isProbability →
    Thm_DaddUniversalSingularity_Carrier

/-- `Thm_DaddUniversalSingularity_FinitePart`. Paper lines 2849-2850, 2934-2935. -/
def Link_Thm_DaddUniversalSingularity_FinitePart : Prop :=
    Thm_DaddUniversalSingularity_Carrier →
    Thm_DaddUniversalSingularity_FinitePart

/-- `Thm_DaddUniversalSingularity_Tight`. Paper lines 2850-2854, 2935-2937. portmanteau (open sets
  (T, oo]) needs nu_X probability. -/
def Link_Thm_DaddUniversalSingularity_Tight : Prop :=
    Prop_TightnessEquivalence →
    Thm_DaddUniversalSingularity_FinitePart →
    EmpiricalMeasures_isProbability →
    Thm_DaddUniversalSingularity_Tight

/-- `Step_DaddXoverR`. Paper lines 3001. -/
def Link_Step_DaddXoverR : Prop :=
    Eq_ExactRepresentability →
    Step_DaddXoverR

/-- `Step_DaddLowerTailUniform`. Paper lines 3001-3006. -/
def Link_Step_DaddLowerTailUniform : Prop :=
    Thm_SmallUpper_doubleExp →
    Step_DaddXoverR →
    Step_DaddLowerTailUniform

/-- `Eq_DaddSubsequentialTail`. Paper lines 2942-2950; proof 2977-2985. closed-set portmanteau needs
  nu_X probability. -/
def Link_Eq_DaddSubsequentialTail : Prop :=
    Eq_AlmostLogTail →
    Thm_DaddUniversalSingularity_Carrier →
    EmpiricalMeasures_isProbability →
    Eq_DaddSubsequentialTail

/-- `Cor_DaddHeavyTails_PosMoments`. Paper lines 2951-2956; proof 2986-2988. -/
def Link_Cor_DaddHeavyTails_PosMoments : Prop :=
    Eq_AlmostLogTail →
    Eq_DaddSubsequentialTail →
    Cor_DaddHeavyTails_PosMoments

/-- `Cor_DaddHeavyTails_LogMeans`. Paper lines 2957-2962; proof 2990-3013. -/
def Link_Cor_DaddHeavyTails_LogMeans : Prop :=
    Eq_AlmostLogTail →
    Eq_DaddSubsequentialTail →
    Step_DaddLowerTailUniform →
    Cor_DaddHeavyTails_LogMeans

/-- `Cor_DaddHeavyTails_InvMoments`. Paper lines 2963-2969; proof 3015-3020. -/
def Link_Cor_DaddHeavyTails_InvMoments : Prop :=
    Step_DaddLowerTailUniform →
    Cor_DaddHeavyTails_InvMoments

/-- `Cor_DaddHeavyTails_InvMomentConv`. Paper lines 2969-2970; proof 3021-3025. -/
def Link_Cor_DaddHeavyTails_InvMomentConv : Prop :=
    Cor_DaddHeavyTails_InvMoments →
    Cor_DaddHeavyTails_InvMomentConv

/-- `Cor_DaddHeavyTails_GeomMean`. Paper lines 2971-2972. -/
def Link_Cor_DaddHeavyTails_GeomMean : Prop :=
    Cor_DaddHeavyTails_LogMeans →
    Cor_DaddHeavyTails_GeomMean

/-- `Cor_DaddHeavyTails_Tight`. Paper lines 2972-2973. -/
def Link_Cor_DaddHeavyTails_Tight : Prop :=
    Thm_DaddUniversalSingularity_Tight →
    Cor_DaddHeavyTails_PosMoments →
    Cor_DaddHeavyTails_LogMeans →
    Cor_DaddHeavyTails_Tight

/-- `Step_DaddCollisionSupport`. Paper lines 3050-3057. -/
def Link_Step_DaddCollisionSupport : Prop :=
    Lem_SigmaRangeZero →
    Intro_RcntFormula →
    Coverage.Fact_RtPosIff →
    Step_DaddCollisionSupport

/-- `Eq_DaddCollisionCriterion`. Paper lines 3038-3042; proof 3058-3061. -/
def Link_Eq_DaddCollisionCriterion : Prop :=
    Step_DaddCollisionSupport →
    Prop_DaddWitnessMeans →
    Eq_DaddCollisionCriterion

/-- `Prop_DaddCollisionCriterion`. Paper lines 3032-3072. prop:dadd:collision-criterion; compactness
  and portmanteau need nu_X probability. -/
def Link_Prop_DaddCollisionCriterion : Prop :=
    Eq_DaddCollisionCriterion →
    Intro_RcntFormula →
    Thm_DaddUniversalSingularity_Carrier →
    EmpiricalMeasures_isProbability →
    Prop_DaddCollisionCriterion

/-- `Step_DaddCollisionWitness`. Paper lines 3095-3096. -/
def Link_Step_DaddCollisionWitness : Prop :=
    Eq_F2Aliquot →
    Step_DaddCollisionWitness

/-- `Step_DaddCollisionFirstMoment`. Paper lines 3099-3105. -/
def Link_Step_DaddCollisionFirstMoment : Prop :=
    Step_DaddCollisionH →
    Step_DaddCollisionCores →
    Step_DaddCollisionFirstMoment

/-- `Step_DaddCollisionFirstMomentLaw`. Paper lines 3098-3108. Kovac at q = 3 bounds sum h(n)^3
  through its j = 0 term, sigma_0 = sigma. -/
def Link_Step_DaddCollisionFirstMomentLaw : Prop :=
    Fact_DaddProgressionLaws →
    Step_DaddCollisionCores →
    Step_DaddCollisionFirstMoment →
    Lem_KovacMoment →
    Notation_sigmaPrefix_zero →
    Step_DaddCollisionFirstMomentLaw

/-- `Step_DaddCollisionSourceIntensity`. Paper lines 3109-3118. joint limit at e = 5 for the 16
  classes a mod 60 coprime to 30 (no e | a), t = 1. -/
def Link_Step_DaddCollisionSourceIntensity : Prop :=
    Eq_DaddCollisionAffine →
    Step_DaddWitnessJointLimit →
    Fact_DaddProgressionLaws →
    Step_DaddCollisionFirstMomentLaw →
    Step_DaddCollisionSourceIntensity

/-- `Step_DaddCollisionCylinder`. Paper lines 3120-3136. d(T_D) = Delta(5)/D via the density of
  integers coprime to 5# = 30. -/
def Link_Step_DaddCollisionCylinder : Prop :=
    Lem_FixedModulusNormality →
    Notation_Delta_density →
    Step_DaddCollisionCylinder

/-- `Step_DaddCollisionPerCore`. Paper lines 3137-3145. -/
def Link_Step_DaddCollisionPerCore : Prop :=
    Step_DaddCollisionSourceIntensity →
    Step_DaddCollisionCylinder →
    Step_DaddCollisionPerCore

/-- `Step_DaddCollisionCombine`. Paper lines 3146-3154. -/
def Link_Step_DaddCollisionCombine : Prop :=
    Step_DaddCollisionWitness →
    Step_DaddCollisionCombine

/-- `Step_DaddCollisionExplicit`. Paper lines 3161-3170. -/
def Link_Step_DaddCollisionExplicit : Prop :=
    Step_DaddCollisionPerCore →
    Step_DaddCollisionCombine →
    Step_DaddCollisionCores →
    Step_DaddCollisionH →
    Step_DaddCollisionArithmetic →
    Step_DaddCollisionExplicit

/-- `Prop_DaddCollisionLowerBound`. Paper lines 3076-3174. unlabeled proposition (liminf K_X(t) >
  1/9). -/
def Link_Prop_DaddCollisionLowerBound : Prop :=
    Step_DaddCollisionExplicit →
    Step_DaddCollisionArithmetic →
    Prop_DaddCollisionLowerBound

/-! ## One spine per paper result

For each theorem, lemma, proposition, corollary or remark environment of the paper whose proof
uses other statements, the composition from the links, leaves and inputs of its own sub-DAG.
A leaf environment (`Eq_Reflection`, `Lem_FraiturePrimeWindow`, `Lem_FraitureExtension`) has no
spine: it is its own obligation. -/

set_option maxRecDepth 20000 in
/-- **Lem_LPInputs** — lem:LP-inputs; the body IS the conjunction of the three LP inputs, so it is
  trusted input, not a Claims field. Paper lines 1316-1344. A conjunction of trusted inputs: nothing
  to prove, and not a claim. -/
theorem spine_Lem_LPInputs
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25) :
    Lem_LPInputs :=
  And.intro i_Cite_LP_Lemma21 (And.intro i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)

set_option maxRecDepth 20000 in
/-- **Lem_FmModulus** — lem:fm-modulus; Fact_KmodGeTwo gives d0 = M/g >= 1 in the maximality clause.
  Paper lines 406-440. -/
theorem spine_Lem_FmModulus
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo) :
    Lem_FmModulus :=
  L_Lem_FmModulus h_Fact_KmodGeTwo

set_option maxRecDepth 20000 in
/-- **Lem_FixedModulusNormality** — lem:fixed-modulus-normality. Paper lines 452-480. -/
theorem spine_Lem_FixedModulusNormality
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges) :
    Lem_FixedModulusNormality :=
  L_Lem_FixedModulusNormality h_Std_recipPrimesAP_diverges

set_option maxRecDepth 20000 in
/-- **Lem_SigmaRangeZero** — lem:sigma-range-zero. Paper lines 484-498. -/
theorem spine_Lem_SigmaRangeZero
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges) :
    Lem_SigmaRangeZero :=
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality

set_option maxRecDepth 20000 in
/-- **Lem_SigmaRate** — lem:sigma-rate. Paper lines 508-560. -/
theorem spine_Lem_SigmaRate
    (L_Lem_SigmaRate_OddPrime : Link_Lem_SigmaRate_OddPrime)
    (L_Lem_SigmaRate_B2 : Link_Lem_SigmaRate_B2)
    (i_Cite_Pollack_Lemma24 : Cite_Pollack_Lemma24)
    (i_Std_SiegelWalfisz_dyadic : Std_SiegelWalfisz_dyadic)
    (i_Std_sigma_odd_iff : Std_sigma_odd_iff) :
    Lem_SigmaRate :=
  have v_Lem_SigmaRate_OddPrime : Lem_SigmaRate_OddPrime := L_Lem_SigmaRate_OddPrime
      i_Cite_Pollack_Lemma24 i_Std_SiegelWalfisz_dyadic
  have v_Lem_SigmaRate_B2 : Lem_SigmaRate_B2 := L_Lem_SigmaRate_B2 i_Std_sigma_odd_iff
  And.intro v_Lem_SigmaRate_OddPrime v_Lem_SigmaRate_B2

set_option maxRecDepth 20000 in
/-- **Lem_Moment** — lem:moment; zeta bound from Mathlib ZetaAsymptotics. Paper lines 565-638. -/
theorem spine_Lem_Moment
    (L_Lem_Moment : Link_Lem_Moment)
    (h_Eq_Reflection : Eq_Reflection) :
    Lem_Moment :=
  L_Lem_Moment h_Eq_Reflection

set_option maxRecDepth 20000 in
/-- **Lem_AnalyticOddRepresentability** — lem:analytic-odd-representability. Paper lines 651-670. -/
theorem spine_Lem_AnalyticOddRepresentability
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (i_Cite_MV_exceptional : Cite_MV_exceptional) :
    Lem_AnalyticOddRepresentability :=
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
  have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
      L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
  And.intro v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO

set_option maxRecDepth 20000 in
/-- **Prop_FraitureFinite** — prop:fraiture-finite. Paper lines 726-823. -/
theorem spine_Prop_FraitureFinite
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Prop_FraitureFinite :=
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
  And.intro v_Eq_FraitureSmall (And.intro v_Eq_FraitureFirstWindow v_Eq_FraitureLargeWindow)

set_option maxRecDepth 20000 in
/-- **Lem_FraitureBalancedGoldbach** — lem:fraiture-balanced-goldbach; the paper's reduction of
  Helfgott's weighted bound (discard triples with a coordinate <= z or a repeated coordinate). Paper
  lines 846-854; proof 856-898. -/
theorem spine_Lem_FraitureBalancedGoldbach
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Lem_FraitureBalancedGoldbach :=
  L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi

set_option maxRecDepth 20000 in
/-- **Prop_FraitureTail** — prop:fraiture-tail. Paper lines 900-953. -/
theorem spine_Prop_FraitureTail
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Prop_FraitureTail :=
  have v_Lem_FraitureBalancedGoldbach : Lem_FraitureBalancedGoldbach :=
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
  have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
  have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
  L_Prop_FraitureTail v_Step_FraitureTailEven v_Step_FraitureTailOdd

set_option maxRecDepth 20000 in
/-- **Thm_FraitureRepresentability** — thm:fraiture-representability; abbrev of
  Eq_ExactRepresentability (one Link serves both). Paper lines 677-684; proof 955-966. -/
theorem spine_Thm_FraitureRepresentability
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Thm_FraitureRepresentability :=
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
  have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
  have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
  have v_Prop_FraitureTail : Prop_FraitureTail := L_Prop_FraitureTail v_Step_FraitureTailEven
      v_Step_FraitureTailOdd
  L_Thm_FraitureRepresentability v_Prop_FraitureFinite v_Prop_FraitureTail h_Step_FraitureSmallCases

set_option maxRecDepth 20000 in
/-- **Eq_ExactRepresentability** — eq:exact-representability; SAME Prop as
  Thm_FraitureRepresentability (abbrev). Paper lines 114-115 (proved as
  thm:fraiture-representability). -/
theorem spine_Eq_ExactRepresentability
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Eq_ExactRepresentability :=
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
  have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
  have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
  have v_Prop_FraitureTail : Prop_FraitureTail := L_Prop_FraitureTail v_Step_FraitureTailEven
      v_Step_FraitureTailOdd
  have v_Thm_FraitureRepresentability : Thm_FraitureRepresentability :=
      L_Thm_FraitureRepresentability v_Prop_FraitureFinite v_Prop_FraitureTail
      h_Step_FraitureSmallCases
  v_Thm_FraitureRepresentability

set_option maxRecDepth 20000 in
/-- **Rem_FraitureCheckUsage** — remark environment, a META-CLAIM about proofs (not a Claims field:
  as a Prop it follows from the three conclusions and says nothing); its content is the signature of
  its spine, which composes the links of the three sub-DAGs with only the named inputs in scope, so
  Lean checks each sub-DAG uses AT MOST those inputs and gen.py checks EXACTLY those. Paper lines
  969-979. **The content of this theorem is its signature**: no input is in scope except the ones
  each part binds, so Lean checks that each sub-DAG uses at most those inputs, and `gen.py` checks
  that it uses exactly those. Its conclusion alone would follow from the three conclusions and say
  nothing. -/
theorem spine_Rem_FraitureCheckUsage
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases) :
    Rem_FraitureCheckUsage :=
  And.intro (fun (i_Comp_Verifier_small : Comp_Verifier_small) (i_Comp_Verifier_window1 :
      Comp_Verifier_window1) (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
      (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69) (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
      (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) =>
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
          L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
      have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
          v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
      have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
          v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
      have v_Prop_FraitureTail : Prop_FraitureTail := L_Prop_FraitureTail v_Step_FraitureTailEven
          v_Step_FraitureTailOdd
      L_Thm_FraitureRepresentability v_Prop_FraitureFinite v_Prop_FraitureTail
          h_Step_FraitureSmallCases)
  (And.intro (fun (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) (i_Cite_RosserSchoenfeld_psi :
      Cite_RosserSchoenfeld_psi) =>
      have v_Lem_FraitureBalancedGoldbach : Lem_FraitureBalancedGoldbach :=
          L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
      have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
          v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
      have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
          v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
      L_Prop_FraitureTail v_Step_FraitureTailEven v_Step_FraitureTailOdd)
  (fun (i_Cite_MV_exceptional : Cite_MV_exceptional) =>
      have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
          L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
      have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
          L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
      And.intro v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO))

set_option maxRecDepth 20000 in
/-- **Lem_KovacMoment** — lem:kovac-moment. Paper lines 990-1116. -/
theorem spine_Lem_KovacMoment
    (L_KovacMoment_identity : Link_KovacMoment_identity)
    (L_KovacMoment_reduction : Link_KovacMoment_reduction)
    (L_Eq_KSprime : Link_Eq_KSprime)
    (L_Eq_KSsecond : Link_Eq_KSsecond)
    (L_Eq_KS : Link_Eq_KS)
    (L_Lem_KovacMoment : Link_Lem_KovacMoment)
    (h_KovacMoment_reflection : KovacMoment_reflection)
    (h_KovacS_le_S1S2 : KovacS_le_S1S2)
    (i_Std_Mertens2 : Std_Mertens2) :
    Lem_KovacMoment :=
  have v_KovacMoment_identity : KovacMoment_identity := L_KovacMoment_identity
      h_KovacMoment_reflection
  have v_KovacMoment_reduction : KovacMoment_reduction := L_KovacMoment_reduction
      v_KovacMoment_identity
  have v_Eq_KSprime : Eq_KSprime := L_Eq_KSprime i_Std_Mertens2
  have v_Eq_KSsecond : Eq_KSsecond := L_Eq_KSsecond i_Std_Mertens2
  have v_Eq_KS : Eq_KS := L_Eq_KS h_KovacS_le_S1S2 v_Eq_KSprime v_Eq_KSsecond
  L_Lem_KovacMoment v_KovacMoment_reduction v_Eq_KS

set_option maxRecDepth 20000 in
/-- **Thm_SmallUpper** — thm:small-upper (Theorem 1.1). Paper lines 140-149; proof 1118-1148. -/
theorem spine_Thm_SmallUpper
    (L_KovacMoment_identity : Link_KovacMoment_identity)
    (L_KovacMoment_reduction : Link_KovacMoment_reduction)
    (L_Eq_KSprime : Link_Eq_KSprime)
    (L_Eq_KSsecond : Link_Eq_KSsecond)
    (L_Eq_KS : Link_Eq_KS)
    (L_Lem_KovacMoment : Link_Lem_KovacMoment)
    (L_SmallUpper_momentStep : Link_SmallUpper_momentStep)
    (L_Thm_SmallUpper_doubleExp : Link_Thm_SmallUpper_doubleExp)
    (L_Thm_SmallUpper_fixedPower : Link_Thm_SmallUpper_fixedPower)
    (h_KovacMoment_reflection : KovacMoment_reflection)
    (h_KovacS_le_S1S2 : KovacS_le_S1S2)
    (h_SmallUpper_emptyCase : SmallUpper_emptyCase)
    (h_SmallUpper_markov : SmallUpper_markov)
    (h_SmallUpper_paramChoice : SmallUpper_paramChoice)
    (h_SmallUpper_doubleExpPower : SmallUpper_doubleExpPower)
    (i_Std_Mertens2 : Std_Mertens2) :
    Thm_SmallUpper :=
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
  And.intro v_Thm_SmallUpper_doubleExp v_Thm_SmallUpper_fixedPower

set_option maxRecDepth 20000 in
/-- **Prop_SmallRatioThreshold** — unlabeled proposition (f(n) <= n/10 => n > 10^120). Paper lines
  1156-1181. -/
theorem spine_Prop_SmallRatioThreshold
    (L_Prop_SmallRatioThreshold : Link_Prop_SmallRatioThreshold)
    (h_SmallRatio_prefixLeSig : SmallRatio_prefixLeSig)
    (h_SmallRatio_abundancySmall : SmallRatio_abundancySmall)
    (h_SmallRatio_axlerNumeric : SmallRatio_axlerNumeric)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2) :
    Prop_SmallRatioThreshold :=
  L_Prop_SmallRatioThreshold h_SmallRatio_prefixLeSig h_SmallRatio_abundancySmall
      h_SmallRatio_axlerNumeric i_Cite_Axler_Cor2

set_option maxRecDepth 20000 in
/-- **Lem_SvA0** — unlabeled lemma on A_0(X). Paper lines 1245-1302. -/
theorem spine_Lem_SvA0
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Eq_SvTwoSided : Link_Eq_SvTwoSided)
    (L_SvA0_jSum : Link_SvA0_jSum)
    (L_Lem_SvA0Count : Link_Lem_SvA0Count)
    (h_Lem_SvA0Unique : Lem_SvA0Unique)
    (h_Lem_SvA0QLarge : Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_PNT_AP : Std_PNT_AP) :
    Lem_SvA0 :=
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
  have v_Eq_SvTwoSided : Eq_SvTwoSided := L_Eq_SvTwoSided h_SvA0_abundancySubmul
  have v_SvA0_jSum : SvA0_jSum := L_SvA0_jSum h_SvA0_sigmaHarmonic
  have v_Lem_SvA0Count : Lem_SvA0Count := L_Lem_SvA0Count v_SvA0_jSum h_Lem_SvA0Unique
      v_Std_primes_dyadic_lower i_Std_Mertens2
  And.intro v_Lem_SvA0Count (And.intro h_Lem_SvA0Unique (And.intro v_Eq_SvTwoSided
      h_Lem_SvA0QLarge))

set_option maxRecDepth 20000 in
/-- **Lem_SmoothPartInput** — lem:smooth-part-input; Std_Mertens1 is derived (line 1383), not
  trusted. Paper lines 1348-1389. -/
theorem spine_Lem_SmoothPartInput
    (L_Eq_SmoothPartPeriodCount : Link_Eq_SmoothPartPeriodCount)
    (L_Lem_SmoothPartInput : Link_Lem_SmoothPartInput)
    (h_Std_Mertens1 : Std_Mertens1)
    (h_Notation_Delta_density : Notation_Delta_density)
    (i_Std_Mertens3 : Std_Mertens3) :
    Lem_SmoothPartInput :=
  have v_Eq_SmoothPartPeriodCount : Eq_SmoothPartPeriodCount := L_Eq_SmoothPartPeriodCount
      h_Notation_Delta_density
  L_Lem_SmoothPartInput v_Eq_SmoothPartPeriodCount h_Std_Mertens1 i_Std_Mertens3

set_option maxRecDepth 20000 in
/-- **Lem_SvRegular** — lem:sv-regular. Paper lines 1394-1480. -/
theorem spine_Lem_SvRegular
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Eq_SvTwoSided : Link_Eq_SvTwoSided)
    (L_SvA0_jSum : Link_SvA0_jSum)
    (L_Lem_SvA0Count : Link_Lem_SvA0Count)
    (L_Lem_SvRegular : Link_Lem_SvRegular)
    (h_Lem_SvA0Unique : Lem_SvA0Unique)
    (h_Lem_SvA0QLarge : Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_PNT_AP : Std_PNT_AP) :
    Lem_SvRegular :=
  have v_Lem_LPInputs : Lem_LPInputs := And.intro i_Cite_LP_Lemma21 (And.intro
      i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
  have v_Eq_SvTwoSided : Eq_SvTwoSided := L_Eq_SvTwoSided h_SvA0_abundancySubmul
  have v_SvA0_jSum : SvA0_jSum := L_SvA0_jSum h_SvA0_sigmaHarmonic
  have v_Lem_SvA0Count : Lem_SvA0Count := L_Lem_SvA0Count v_SvA0_jSum h_Lem_SvA0Unique
      v_Std_primes_dyadic_lower i_Std_Mertens2
  have v_Lem_SvA0 : Lem_SvA0 := And.intro v_Lem_SvA0Count (And.intro h_Lem_SvA0Unique (And.intro
      v_Eq_SvTwoSided h_Lem_SvA0QLarge))
  L_Lem_SvRegular v_Lem_SvA0 v_Lem_LPInputs h_Eq_SvHarmonicDensityZero i_Cite_Pollack_Thm14
      i_Std_Mertens2

set_option maxRecDepth 20000 in
/-- **Lem_SvClasses** — lem:sv-classes; the regular family enters as the hypothesis
  SV.RegularFamily, not as Lem_SvRegular. Paper lines 1486-1527. -/
theorem spine_Lem_SvClasses
    (L_Eq_SmoothPartPeriodCount : Link_Eq_SmoothPartPeriodCount)
    (L_Lem_SmoothPartInput : Link_Lem_SmoothPartInput)
    (L_Lem_SvClasses : Link_Lem_SvClasses)
    (h_Std_Mertens1 : Std_Mertens1)
    (h_Notation_Delta_density : Notation_Delta_density)
    (i_Std_Mertens3 : Std_Mertens3) :
    Lem_SvClasses :=
  have v_Eq_SmoothPartPeriodCount : Eq_SmoothPartPeriodCount := L_Eq_SmoothPartPeriodCount
      h_Notation_Delta_density
  have v_Lem_SmoothPartInput : Lem_SmoothPartInput := L_Lem_SmoothPartInput
      v_Eq_SmoothPartPeriodCount h_Std_Mertens1 i_Std_Mertens3
  L_Lem_SvClasses v_Lem_SmoothPartInput i_Std_Mertens3

set_option maxRecDepth 20000 in
/-- **Prop_SvSecondMoment** — prop:sv-second-moment; diagonal from the SV.ClassesAt hypothesis.
  Paper lines 1531-1860. -/
theorem spine_Prop_SvSecondMoment
    (L_Eq_SvTwoSided : Link_Eq_SvTwoSided)
    (L_Eq_SmoothPartPeriodCount : Link_Eq_SmoothPartPeriodCount)
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
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (h_Eq_SvCollision : Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount : Claim_SvResiduePairCount)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_BrunTitchmarsh : Std_BrunTitchmarsh)
    (i_Std_divisorBound : Std_divisorBound)
    (i_Std_totient_sigma : Std_totient_sigma) :
    Prop_SvSecondMoment :=
  have v_Eq_SvTwoSided : Eq_SvTwoSided := L_Eq_SvTwoSided h_SvA0_abundancySubmul
  have v_Eq_SmoothPartPeriodCount : Eq_SmoothPartPeriodCount := L_Eq_SmoothPartPeriodCount
      h_Notation_Delta_density
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
  L_Prop_SvSecondMoment h_Eq_SvCollision v_Claim_SvSievePairs v_Eq_SvTotient v_Claim_SvA3Reduction
      v_Eq_SvReducedCollisionSum

set_option maxRecDepth 20000 in
/-- **Thm_SmallValues** — thm:small-values (Theorem 1.2); rescaling X, delta > 1 from delta = 1.
  Paper lines 159-164; proof 1217-1222, 1862-1884. -/
theorem spine_Thm_SmallValues
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
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
    (h_Std_Mertens1 : Std_Mertens1)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Eq_SvBasic : Eq_SvBasic)
    (h_Eq_SvD : Eq_SvD)
    (h_Lem_SvA0Unique : Lem_SvA0Unique)
    (h_Lem_SvA0QLarge : Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision : Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount : Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz : Claim_SvCauchySchwarz)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP)
    (i_Std_BrunTitchmarsh : Std_BrunTitchmarsh)
    (i_Std_divisorBound : Std_divisorBound)
    (i_Std_totient_sigma : Std_totient_sigma) :
    Thm_SmallValues :=
  have v_Lem_LPInputs : Lem_LPInputs := And.intro i_Cite_LP_Lemma21 (And.intro
      i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
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
  L_Thm_SmallValues v_SvFamilyTarget h_Eq_SvBasic

set_option maxRecDepth 20000 in
/-- **Lem_KernelTails** — lem:kernel-tails. Paper lines 1898-1977. -/
theorem spine_Lem_KernelTails
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
    (L_Eq_MovingKernelTail : Link_Eq_MovingKernelTail)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (i_Std_Mertens2 : Std_Mertens2) :
    Lem_KernelTails :=
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
  have v_Eq_MovingKernelTail : Eq_MovingKernelTail := L_Eq_MovingKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
  And.intro v_Eq_FixedKernelTail v_Eq_MovingKernelTail

set_option maxRecDepth 20000 in
/-- **Prop_FmEnvelope** — prop:fm-envelope. Paper lines 2002-2023. -/
theorem spine_Prop_FmEnvelope
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_UpperTails_Claim_KA_finite : Link_UpperTails_Claim_KA_finite)
    (L_UpperTails_Claim_VA_periodic : Link_UpperTails_Claim_VA_periodic)
    (L_UpperTails_Claim_VA_density : Link_UpperTails_Claim_VA_density)
    (L_Prop_FmEnvelope : Link_Prop_FmEnvelope)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo) :
    Prop_FmEnvelope :=
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_UpperTails_Claim_KA_finite : UpperTails.Claim_KA_finite := L_UpperTails_Claim_KA_finite
      v_Lem_FmModulus h_Fact_KmodGeTwo
  have v_UpperTails_Claim_VA_periodic : UpperTails.Claim_VA_periodic :=
      L_UpperTails_Claim_VA_periodic v_UpperTails_Claim_KA_finite
  have v_UpperTails_Claim_VA_density : UpperTails.Claim_VA_density := L_UpperTails_Claim_VA_density
      v_UpperTails_Claim_KA_finite v_UpperTails_Claim_VA_periodic h_Fact_KmodGeTwo
  L_Prop_FmEnvelope v_Lem_SigmaRangeZero v_Lem_FmModulus v_Lem_FixedModulusNormality
      v_UpperTails_Claim_KA_finite v_UpperTails_Claim_VA_density

set_option maxRecDepth 20000 in
/-- **Cor_FmEnvelopeTail** — cor:fm-envelope-tail. Paper lines 2025-2062. -/
theorem spine_Cor_FmEnvelopeTail
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
    (L_UpperTails_Claim_KA_finite : Link_UpperTails_Claim_KA_finite)
    (L_UpperTails_Claim_VA_periodic : Link_UpperTails_Claim_VA_periodic)
    (L_UpperTails_Claim_VA_density : Link_UpperTails_Claim_VA_density)
    (L_UpperTails_Claim_DeltaPfix : Link_UpperTails_Claim_DeltaPfix)
    (L_UpperTails_Claim_RoughNotVA : Link_UpperTails_Claim_RoughNotVA)
    (L_Cor_FmEnvelopeTail : Link_Cor_FmEnvelopeTail)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3) :
    Cor_FmEnvelopeTail :=
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
  have v_UpperTails_Claim_KA_finite : UpperTails.Claim_KA_finite := L_UpperTails_Claim_KA_finite
      v_Lem_FmModulus h_Fact_KmodGeTwo
  have v_UpperTails_Claim_VA_periodic : UpperTails.Claim_VA_periodic :=
      L_UpperTails_Claim_VA_periodic v_UpperTails_Claim_KA_finite
  have v_UpperTails_Claim_VA_density : UpperTails.Claim_VA_density := L_UpperTails_Claim_VA_density
      v_UpperTails_Claim_KA_finite v_UpperTails_Claim_VA_periodic h_Fact_KmodGeTwo
  have v_UpperTails_Claim_DeltaPfix : UpperTails.Claim_DeltaPfix := L_UpperTails_Claim_DeltaPfix
      i_Std_Mertens3
  have v_UpperTails_Claim_RoughNotVA : UpperTails.Claim_RoughNotVA := L_UpperTails_Claim_RoughNotVA
      v_Lem_FmModulus h_Fact_KmodGeTwo v_UpperTails_Claim_KA_finite h_Notation_Delta_density
  L_Cor_FmEnvelopeTail h_UpperTails_Claim_VA_rough v_UpperTails_Claim_VA_density
      h_Notation_Delta_density v_UpperTails_Claim_DeltaPfix v_UpperTails_Claim_RoughNotVA
      v_Eq_FixedKernelTail

set_option maxRecDepth 20000 in
/-- **Thm_AlmostLogTail** — thm:almost-log-tail (Theorem 1.3). Paper lines 176-188; proof 2066-2107.
  Its trusted inputs are exactly `Cite_MV_exceptional`, `Std_Mertens2`, `Std_Mertens3`: no finite
  representability computation (paper lines 645-647, 2105-2106). `gen.py` refuses any DAG edit that
  changes this set. -/
theorem spine_Thm_AlmostLogTail
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
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
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith : UpperTails.Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio : UpperTails.Claim_LscaleRatio)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3) :
    Thm_AlmostLogTail :=
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
  have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
      L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
  have v_Lem_AnalyticOddRepresentability : Lem_AnalyticOddRepresentability := And.intro
      v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
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
  And.intro v_Eq_AlmostLogTail (And.intro v_Thm_AlmostLogTail_posLowerDens
      v_Thm_AlmostLogTail_limsup)

set_option maxRecDepth 20000 in
/-- **Thm_SubexpGrowth** — thm:subexp-growth (Theorem 1.4). Paper lines 196-216; proof 2111-2244.
  Its trusted inputs are exactly `Cite_MV_exceptional`, `Cite_Pollack_Lemma24`,
  `Std_SiegelWalfisz_dyadic`, `Std_sigma_odd_iff`, `Std_Mertens2`, `Std_Mertens3`: no finite
  representability computation (paper lines 645-647, 2223-2224). `gen.py` refuses any DAG edit that
  changes this set. -/
theorem spine_Thm_SubexpGrowth
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_SigmaRate_OddPrime : Link_Lem_SigmaRate_OddPrime)
    (L_Lem_SigmaRate_B2 : Link_Lem_SigmaRate_B2)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_MovingKernelTail : Link_Eq_MovingKernelTail)
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
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (h_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_SubexpFltP : UpperTails.Claim_SubexpFltP)
    (h_UpperTails_Claim_SubexpCofactorOne : UpperTails.Claim_SubexpCofactorOne)
    (h_UpperTails_Claim_SubexpLogT : UpperTails.Claim_SubexpLogT)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_Pollack_Lemma24 : Cite_Pollack_Lemma24)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_SiegelWalfisz_dyadic : Std_SiegelWalfisz_dyadic)
    (i_Std_sigma_odd_iff : Std_sigma_odd_iff) :
    Thm_SubexpGrowth :=
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_SigmaRate_OddPrime : Lem_SigmaRate_OddPrime := L_Lem_SigmaRate_OddPrime
      i_Cite_Pollack_Lemma24 i_Std_SiegelWalfisz_dyadic
  have v_Lem_SigmaRate_B2 : Lem_SigmaRate_B2 := L_Lem_SigmaRate_B2 i_Std_sigma_odd_iff
  have v_Lem_SigmaRate : Lem_SigmaRate := And.intro v_Lem_SigmaRate_OddPrime v_Lem_SigmaRate_B2
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
  have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
      L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
  have v_Lem_AnalyticOddRepresentability : Lem_AnalyticOddRepresentability := And.intro
      v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_MovingKernelTail : Eq_MovingKernelTail := L_Eq_MovingKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
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
  And.intro v_Eq_SubexpGrowth v_Eq_PositiveMomentGrowth

set_option maxRecDepth 20000 in
/-- **Prop_ClassFirstMoment** — prop:class-first-moment. Paper lines 2292-2435. -/
theorem spine_Prop_ClassFirstMoment
    (L_Lem_Moment : Link_Lem_Moment)
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
    (h_Eq_Reflection : Eq_Reflection)
    (h_Eq_HGcd : Eq_HGcd)
    (h_Eq_UClass : Eq_UClass)
    (h_Coverage_Step_SeDensity : Coverage.Step_SeDensity)
    (h_Coverage_Step_HeRatio : Coverage.Step_HeRatio)
    (h_Coverage_Step_SeMultiplesDens : Coverage.Step_SeMultiplesDens)
    (h_Coverage_Disp_CoprimeSqTail : Coverage.Disp_CoprimeSqTail)
    (h_Coverage_Step_DistinctPairs : Coverage.Step_DistinctPairs)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP) :
    Prop_ClassFirstMoment :=
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
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
  And.intro v_Prop_ClassFirstMoment_bound v_Prop_ClassFirstMoment_tendsto

set_option maxRecDepth 20000 in
/-- **Cor_FmPrimeCeiling** — corollary (label cor:fm-prime-ceiling commented out). Paper lines
  2448-2470. -/
theorem spine_Cor_FmPrimeCeiling
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Cor_FmPrimeCeiling_congr : Link_Cor_FmPrimeCeiling_congr)
    (L_Cor_FmPrimeCeiling_count : Link_Cor_FmPrimeCeiling_count)
    (L_Cor_FmPrimeCeiling_upperDens : Link_Cor_FmPrimeCeiling_upperDens)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Disp_FinalDivisor : Disp_FinalDivisor)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo) :
    Cor_FmPrimeCeiling :=
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Cor_FmPrimeCeiling_congr : Cor_FmPrimeCeiling_congr := L_Cor_FmPrimeCeiling_congr
      v_Lem_FmModulus
  have v_Cor_FmPrimeCeiling_count : Cor_FmPrimeCeiling_count := L_Cor_FmPrimeCeiling_count
      v_Cor_FmPrimeCeiling_congr h_Disp_FinalDivisor v_Lem_FixedModulusNormality
  have v_Cor_FmPrimeCeiling_upperDens : Cor_FmPrimeCeiling_upperDens :=
      L_Cor_FmPrimeCeiling_upperDens v_Cor_FmPrimeCeiling_count
  And.intro v_Cor_FmPrimeCeiling_congr (And.intro v_Cor_FmPrimeCeiling_count
      v_Cor_FmPrimeCeiling_upperDens)

set_option maxRecDepth 20000 in
/-- **Cor_FixedCofactorDefect** — unlabeled corollary. Paper lines 2488-2505. -/
theorem spine_Cor_FixedCofactorDefect
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
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
    (L_Cor_FixedCofactorDefect_pos : Link_Cor_FixedCofactorDefect_pos)
    (L_Eq_FixedCofactorDefect : Link_Eq_FixedCofactorDefect)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith : UpperTails.Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio : UpperTails.Claim_LscaleRatio)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3) :
    Cor_FixedCofactorDefect :=
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
  have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
      L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
  have v_Lem_AnalyticOddRepresentability : Lem_AnalyticOddRepresentability := And.intro
      v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
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
  have v_Cor_FixedCofactorDefect_pos : Cor_FixedCofactorDefect_pos := L_Cor_FixedCofactorDefect_pos
      v_Eq_AlmostLogTail
  have v_Eq_FixedCofactorDefect : Eq_FixedCofactorDefect := L_Eq_FixedCofactorDefect
      v_Eq_AlmostLogTail
  And.intro v_Cor_FixedCofactorDefect_pos v_Eq_FixedCofactorDefect

set_option maxRecDepth 20000 in
/-- **Prop_EtaALower** — unlabeled proposition (eta_A lower bound). Paper lines 2543-2558. -/
theorem spine_Prop_EtaALower
    (L_Std_PNT : Link_Std_PNT)
    (L_Fact_KmodFinite : Link_Fact_KmodFinite)
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
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
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Fact_DsetResidue : Fact_DsetResidue)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith : UpperTails.Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio : UpperTails.Claim_LscaleRatio)
    (h_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP) :
    Prop_EtaALower :=
  have v_Std_PNT : Std_PNT := L_Std_PNT i_Std_PNT_AP
  have v_Fact_KmodFinite : Fact_KmodFinite := L_Fact_KmodFinite h_Fact_DsetResidue
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
  have v_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO :=
      L_Lem_AnalyticOddRepresentability_LittleO v_Lem_AnalyticOddRepresentability_Bound
  have v_Lem_AnalyticOddRepresentability : Lem_AnalyticOddRepresentability := And.intro
      v_Lem_AnalyticOddRepresentability_Bound v_Lem_AnalyticOddRepresentability_LittleO
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
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
  have v_Eq_FixedCofactorDefect : Eq_FixedCofactorDefect := L_Eq_FixedCofactorDefect
      v_Eq_AlmostLogTail
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
  And.intro v_Prop_EtaALower_bound v_Prop_EtaALower_tendsto

set_option maxRecDepth 20000 in
/-- **Prop_ThetaTwo** — prop:theta-two. Paper lines 2569-2620. -/
theorem spine_Prop_ThetaTwo
    (L_Eq_F2OddNegligible : Link_Eq_F2OddNegligible)
    (L_Eq_OddUntouchables : Link_Eq_OddUntouchables)
    (L_Coverage_Step_EvenUntouchables : Link_Coverage_Step_EvenUntouchables)
    (L_Coverage_Disp_F2Count : Link_Coverage_Disp_F2Count)
    (L_Prop_ThetaTwo : Link_Prop_ThetaTwo)
    (h_Eq_F2Aliquot : Eq_F2Aliquot)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Std_sigma_odd_iff : Std_sigma_odd_iff) :
    Prop_ThetaTwo :=
  have v_Eq_F2OddNegligible : Eq_F2OddNegligible := L_Eq_F2OddNegligible h_Eq_F2Aliquot
      i_Std_sigma_odd_iff
  have v_Eq_OddUntouchables : Eq_OddUntouchables := L_Eq_OddUntouchables i_Cite_MV_exceptional
  have v_Coverage_Step_EvenUntouchables : Coverage.Step_EvenUntouchables :=
      L_Coverage_Step_EvenUntouchables v_Eq_OddUntouchables i_Cite_ChenZhao
  have v_Coverage_Disp_F2Count : Coverage.Disp_F2Count := L_Coverage_Disp_F2Count h_Eq_F2Aliquot
      v_Eq_F2OddNegligible v_Coverage_Step_EvenUntouchables
  L_Prop_ThetaTwo v_Coverage_Disp_F2Count

set_option maxRecDepth 20000 in
/-- **Cor_EtaTwo** — unlabeled corollary (eta_2). Paper lines 2623-2645. -/
theorem spine_Cor_EtaTwo
    (L_Fact_KmodFinite : Link_Fact_KmodFinite)
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Coverage_Step_KmodSmallPrime : Link_Coverage_Step_KmodSmallPrime)
    (L_Coverage_Step_GcovValuesSmallPrime : Link_Coverage_Step_GcovValuesSmallPrime)
    (L_Coverage_Fact_GcovCoprimeNull : Link_Coverage_Fact_GcovCoprimeNull)
    (L_Coverage_Fact_CoprimeComplementDens : Link_Coverage_Fact_CoprimeComplementDens)
    (L_Eq_BoundedCofactorComplement : Link_Eq_BoundedCofactorComplement)
    (L_Eq_F2OddNegligible : Link_Eq_F2OddNegligible)
    (L_Eq_OddUntouchables : Link_Eq_OddUntouchables)
    (L_Coverage_Step_EvenUntouchables : Link_Coverage_Step_EvenUntouchables)
    (L_Coverage_Disp_F2Count : Link_Coverage_Disp_F2Count)
    (L_Prop_ThetaTwo : Link_Prop_ThetaTwo)
    (L_Coverage_Step_UpperDensG2 : Link_Coverage_Step_UpperDensG2)
    (L_Cor_EtaTwo : Link_Cor_EtaTwo)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Fact_DsetResidue : Fact_DsetResidue)
    (h_Eq_F2Aliquot : Eq_F2Aliquot)
    (h_Coverage_Step_G2Decomp : Coverage.Step_G2Decomp)
    (h_Coverage_Step_P2Values : Coverage.Step_P2Values)
    (h_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Std_sigma_odd_iff : Std_sigma_odd_iff) :
    Cor_EtaTwo :=
  have v_Fact_KmodFinite : Fact_KmodFinite := L_Fact_KmodFinite h_Fact_DsetResidue
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
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
  have v_Eq_F2OddNegligible : Eq_F2OddNegligible := L_Eq_F2OddNegligible h_Eq_F2Aliquot
      i_Std_sigma_odd_iff
  have v_Eq_OddUntouchables : Eq_OddUntouchables := L_Eq_OddUntouchables i_Cite_MV_exceptional
  have v_Coverage_Step_EvenUntouchables : Coverage.Step_EvenUntouchables :=
      L_Coverage_Step_EvenUntouchables v_Eq_OddUntouchables i_Cite_ChenZhao
  have v_Coverage_Disp_F2Count : Coverage.Disp_F2Count := L_Coverage_Disp_F2Count h_Eq_F2Aliquot
      v_Eq_F2OddNegligible v_Coverage_Step_EvenUntouchables
  have v_Prop_ThetaTwo : Prop_ThetaTwo := L_Prop_ThetaTwo v_Coverage_Disp_F2Count
  have v_Coverage_Step_UpperDensG2 : Coverage.Step_UpperDensG2 := L_Coverage_Step_UpperDensG2
      h_Coverage_Step_G2Decomp v_Lem_SigmaRangeZero
  L_Cor_EtaTwo v_Eq_BoundedCofactorComplement h_Coverage_Step_P2Values v_Coverage_Step_UpperDensG2
      v_Prop_ThetaTwo

set_option maxRecDepth 20000 in
/-- **Prop_TightnessEquivalence** — prop:tightness-equivalence (bounded X: finitely many ratios).
  Paper lines 2674-2717. -/
theorem spine_Prop_TightnessEquivalence
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (L_Intro_RcntFormula : Link_Intro_RcntFormula)
    (L_Coverage_Disp_TailLeCompl : Link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail : Link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence : Link_Prop_TightnessEquivalence)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases)
    (h_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Prop_TightnessEquivalence :=
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
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
  have v_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl := L_Coverage_Disp_TailLeCompl
      v_Intro_RcntFormula
  have v_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail := L_Coverage_Disp_ComplLeTail
      v_Lem_Moment v_Eq_ExactRepresentability
  L_Prop_TightnessEquivalence v_Coverage_Disp_TailLeCompl v_Coverage_Disp_ComplLeTail
      h_Coverage_Fact_UpperDensCompl

set_option maxRecDepth 20000 in
/-- **Prop_DaddWitnessMeans** — prop:dadd:witness-means. Paper lines 2752-2829. -/
theorem spine_Prop_DaddWitnessMeans
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Fact_DaddProgressionLaws : Link_Fact_DaddProgressionLaws)
    (L_Step_DaddWitnessIdentity : Link_Step_DaddWitnessIdentity)
    (L_Step_DaddWitnessJointLimit : Link_Step_DaddWitnessJointLimit)
    (L_Step_DaddWitnessSupport : Link_Step_DaddWitnessSupport)
    (L_Step_DaddWitnessCount : Link_Step_DaddWitnessCount)
    (L_Step_DaddWitnessCofactorTail : Link_Step_DaddWitnessCofactorTail)
    (L_Step_DaddWitnessPieceBounds : Link_Step_DaddWitnessPieceBounds)
    (L_Prop_DaddWitnessMeans : Link_Prop_DaddWitnessMeans)
    (h_Disp_FinalDivisor : Disp_FinalDivisor)
    (h_Eq_Reflection : Eq_Reflection)
    (i_Cite_PollackAP : Cite_PollackAP) :
    Prop_DaddWitnessMeans :=
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Fact_DaddProgressionLaws : Fact_DaddProgressionLaws := L_Fact_DaddProgressionLaws
      i_Cite_PollackAP
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
  L_Prop_DaddWitnessMeans v_Step_DaddWitnessIdentity v_Step_DaddWitnessCount
      v_Step_DaddWitnessCofactorTail v_Step_DaddWitnessPieceBounds

set_option maxRecDepth 20000 in
/-- **Thm_DaddUniversalSingularity** — thm:dadd:universal-singularity. Paper lines 2839-2938. -/
theorem spine_Thm_DaddUniversalSingularity
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Cite_Davenport : Link_Cite_Davenport)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (L_Intro_RcntFormula : Link_Intro_RcntFormula)
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
    (L_Coverage_Disp_TailLeCompl : Link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail : Link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence : Link_Prop_TightnessEquivalence)
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
    (L_Step_DaddSingularCarrier : Link_Step_DaddSingularCarrier)
    (L_Step_DaddWitnessMeasureMass : Link_Step_DaddWitnessMeasureMass)
    (L_Step_DaddWitnessCarrier : Link_Step_DaddWitnessCarrier)
    (L_Step_DaddEmpiricalWitnessVague : Link_Step_DaddEmpiricalWitnessVague)
    (L_Step_DaddLimitDomination : Link_Step_DaddLimitDomination)
    (L_Thm_DaddUniversalSingularity_Carrier : Link_Thm_DaddUniversalSingularity_Carrier)
    (L_Thm_DaddUniversalSingularity_FinitePart : Link_Thm_DaddUniversalSingularity_FinitePart)
    (L_Thm_DaddUniversalSingularity_Tight : Link_Thm_DaddUniversalSingularity_Tight)
    (h_Std_Mertens1 : Std_Mertens1)
    (h_EmpiricalMeasures_isProbability : EmpiricalMeasures_isProbability)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Disp_FinalDivisor : Disp_FinalDivisor)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases)
    (h_Eq_SvBasic : Eq_SvBasic)
    (h_Eq_SvD : Eq_SvD)
    (h_Lem_SvA0Unique : Lem_SvA0Unique)
    (h_Lem_SvA0QLarge : Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision : Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount : Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz : Claim_SvCauchySchwarz)
    (h_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl)
    (h_Step_DaddWitnessDomination : Step_DaddWitnessDomination)
    (h_Step_DaddCountDomination : Step_DaddCountDomination)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP)
    (i_Std_BrunTitchmarsh : Std_BrunTitchmarsh)
    (i_Std_divisorBound : Std_divisorBound)
    (i_Std_totient_sigma : Std_totient_sigma)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Thm_DaddUniversalSingularity :=
  have v_Lem_LPInputs : Lem_LPInputs := And.intro i_Cite_LP_Lemma21 (And.intro
      i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
  have v_Cite_Davenport : Cite_Davenport := L_Cite_Davenport i_Cite_PollackAP
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
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
  have v_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl := L_Coverage_Disp_TailLeCompl
      v_Intro_RcntFormula
  have v_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail := L_Coverage_Disp_ComplLeTail
      v_Lem_Moment v_Eq_ExactRepresentability
  have v_Prop_TightnessEquivalence : Prop_TightnessEquivalence := L_Prop_TightnessEquivalence
      v_Coverage_Disp_TailLeCompl v_Coverage_Disp_ComplLeTail h_Coverage_Fact_UpperDensCompl
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
  And.intro v_Thm_DaddUniversalSingularity_Carrier (And.intro
      v_Thm_DaddUniversalSingularity_FinitePart v_Thm_DaddUniversalSingularity_Tight)

set_option maxRecDepth 20000 in
/-- **Cor_DaddHeavyTails** — unlabeled corollary (heavy tails). Paper lines 2942-3026. -/
theorem spine_Cor_DaddHeavyTails
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Cite_Davenport : Link_Cite_Davenport)
    (L_Lem_FmModulus : Link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (L_Intro_RcntFormula : Link_Intro_RcntFormula)
    (L_KovacMoment_identity : Link_KovacMoment_identity)
    (L_KovacMoment_reduction : Link_KovacMoment_reduction)
    (L_Eq_KSprime : Link_Eq_KSprime)
    (L_Eq_KSsecond : Link_Eq_KSsecond)
    (L_Eq_KS : Link_Eq_KS)
    (L_Lem_KovacMoment : Link_Lem_KovacMoment)
    (L_SmallUpper_momentStep : Link_SmallUpper_momentStep)
    (L_Thm_SmallUpper_doubleExp : Link_Thm_SmallUpper_doubleExp)
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
    (L_Eq_SharpPrimeSum : Link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail : Link_Eq_FixedKernelTail)
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
    (L_Coverage_Disp_TailLeCompl : Link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail : Link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence : Link_Prop_TightnessEquivalence)
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
    (h_Std_Mertens1 : Std_Mertens1)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_EmpiricalMeasures_isProbability : EmpiricalMeasures_isProbability)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Disp_FinalDivisor : Disp_FinalDivisor)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Fact_KmodGeTwo : Fact_KmodGeTwo)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases)
    (h_KovacMoment_reflection : KovacMoment_reflection)
    (h_KovacS_le_S1S2 : KovacS_le_S1S2)
    (h_SmallUpper_emptyCase : SmallUpper_emptyCase)
    (h_SmallUpper_markov : SmallUpper_markov)
    (h_SmallUpper_paramChoice : SmallUpper_paramChoice)
    (h_Eq_SvBasic : Eq_SvBasic)
    (h_Eq_SvD : Eq_SvD)
    (h_Lem_SvA0Unique : Lem_SvA0Unique)
    (h_Lem_SvA0QLarge : Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision : Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount : Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz : Claim_SvCauchySchwarz)
    (h_Eq_RankinKernel : Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith : UpperTails.Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio : UpperTails.Claim_LscaleRatio)
    (h_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl)
    (h_Step_DaddWitnessDomination : Step_DaddWitnessDomination)
    (h_Step_DaddCountDomination : Step_DaddCountDomination)
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP)
    (i_Std_BrunTitchmarsh : Std_BrunTitchmarsh)
    (i_Std_divisorBound : Std_divisorBound)
    (i_Std_totient_sigma : Std_totient_sigma)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Cor_DaddHeavyTails :=
  have v_Lem_LPInputs : Lem_LPInputs := And.intro i_Cite_LP_Lemma21 (And.intro
      i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
  have v_Cite_Davenport : Cite_Davenport := L_Cite_Davenport i_Cite_PollackAP
  have v_Lem_FmModulus : Lem_FmModulus := L_Lem_FmModulus h_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
  have v_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound :=
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
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
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := L_Eq_SharpPrimeSum i_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail := L_Eq_FixedKernelTail h_Eq_RankinKernel
      v_Eq_SharpPrimeSum h_UpperTails_Claim_EulerHigherTerms
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
  have v_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl := L_Coverage_Disp_TailLeCompl
      v_Intro_RcntFormula
  have v_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail := L_Coverage_Disp_ComplLeTail
      v_Lem_Moment v_Eq_ExactRepresentability
  have v_Prop_TightnessEquivalence : Prop_TightnessEquivalence := L_Prop_TightnessEquivalence
      v_Coverage_Disp_TailLeCompl v_Coverage_Disp_ComplLeTail h_Coverage_Fact_UpperDensCompl
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
  And.intro v_Eq_DaddSubsequentialTail (And.intro v_Cor_DaddHeavyTails_PosMoments (And.intro
      v_Cor_DaddHeavyTails_LogMeans (And.intro v_Cor_DaddHeavyTails_InvMoments (And.intro
      v_Cor_DaddHeavyTails_InvMomentConv (And.intro v_Cor_DaddHeavyTails_GeomMean
      v_Cor_DaddHeavyTails_Tight)))))

set_option maxRecDepth 20000 in
/-- **Prop_DaddCollisionCriterion** — prop:dadd:collision-criterion; compactness and portmanteau
  need nu_X probability. Paper lines 3032-3072. -/
theorem spine_Prop_DaddCollisionCriterion
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Cite_Davenport : Link_Cite_Davenport)
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero : Link_Lem_SigmaRangeZero)
    (L_Lem_Moment : Link_Lem_Moment)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability : Link_Thm_FraitureRepresentability)
    (L_Intro_RcntFormula : Link_Intro_RcntFormula)
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
    (L_Step_DaddSingularCarrier : Link_Step_DaddSingularCarrier)
    (L_Step_DaddWitnessMeasureMass : Link_Step_DaddWitnessMeasureMass)
    (L_Step_DaddWitnessCarrier : Link_Step_DaddWitnessCarrier)
    (L_Step_DaddEmpiricalWitnessVague : Link_Step_DaddEmpiricalWitnessVague)
    (L_Step_DaddLimitDomination : Link_Step_DaddLimitDomination)
    (L_Thm_DaddUniversalSingularity_Carrier : Link_Thm_DaddUniversalSingularity_Carrier)
    (L_Step_DaddCollisionSupport : Link_Step_DaddCollisionSupport)
    (L_Eq_DaddCollisionCriterion : Link_Eq_DaddCollisionCriterion)
    (L_Prop_DaddCollisionCriterion : Link_Prop_DaddCollisionCriterion)
    (h_Std_Mertens1 : Std_Mertens1)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_EmpiricalMeasures_isProbability : EmpiricalMeasures_isProbability)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Disp_FinalDivisor : Disp_FinalDivisor)
    (h_Eq_Reflection : Eq_Reflection)
    (h_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension : Lem_FraitureExtension)
    (h_Step_FraitureSmallBq : Step_FraitureSmallBq)
    (h_Step_FraitureSeven : Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases : Step_FraitureSmallCases)
    (h_Eq_SvBasic : Eq_SvBasic)
    (h_Eq_SvD : Eq_SvD)
    (h_Lem_SvA0Unique : Lem_SvA0Unique)
    (h_Lem_SvA0QLarge : Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul : SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision : Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount : Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz : Claim_SvCauchySchwarz)
    (h_Coverage_Fact_RtPosIff : Coverage.Fact_RtPosIff)
    (h_Step_DaddWitnessDomination : Step_DaddWitnessDomination)
    (h_Step_DaddCountDomination : Step_DaddCountDomination)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Std_Mertens2 : Std_Mertens2)
    (i_Std_Mertens3 : Std_Mertens3)
    (i_Std_PNT_AP : Std_PNT_AP)
    (i_Std_BrunTitchmarsh : Std_BrunTitchmarsh)
    (i_Std_divisorBound : Std_divisorBound)
    (i_Std_totient_sigma : Std_totient_sigma)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
    Prop_DaddCollisionCriterion :=
  have v_Lem_LPInputs : Lem_LPInputs := And.intro i_Cite_LP_Lemma21 (And.intro
      i_Cite_LP_Lemma22_range i_Cite_LP_Lemma25)
  have v_Std_primes_dyadic_lower : Std_primes_dyadic_lower := L_Std_primes_dyadic_lower i_Std_PNT_AP
  have v_Cite_Davenport : Cite_Davenport := L_Cite_Davenport i_Cite_PollackAP
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero := L_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_Moment : Lem_Moment := L_Lem_Moment h_Eq_Reflection
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
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
  have v_Step_DaddCollisionSupport : Step_DaddCollisionSupport := L_Step_DaddCollisionSupport
      v_Lem_SigmaRangeZero v_Intro_RcntFormula h_Coverage_Fact_RtPosIff
  have v_Eq_DaddCollisionCriterion : Eq_DaddCollisionCriterion := L_Eq_DaddCollisionCriterion
      v_Step_DaddCollisionSupport v_Prop_DaddWitnessMeans
  L_Prop_DaddCollisionCriterion v_Eq_DaddCollisionCriterion v_Intro_RcntFormula
      v_Thm_DaddUniversalSingularity_Carrier h_EmpiricalMeasures_isProbability

set_option maxRecDepth 20000 in
/-- **Prop_DaddCollisionLowerBound** — unlabeled proposition (liminf K_X(t) > 1/9). Paper lines
  3076-3174. -/
theorem spine_Prop_DaddCollisionLowerBound
    (L_Lem_FixedModulusNormality : Link_Lem_FixedModulusNormality)
    (L_KovacMoment_identity : Link_KovacMoment_identity)
    (L_KovacMoment_reduction : Link_KovacMoment_reduction)
    (L_Eq_KSprime : Link_Eq_KSprime)
    (L_Eq_KSsecond : Link_Eq_KSsecond)
    (L_Eq_KS : Link_Eq_KS)
    (L_Lem_KovacMoment : Link_Lem_KovacMoment)
    (L_Fact_DaddProgressionLaws : Link_Fact_DaddProgressionLaws)
    (L_Step_DaddWitnessJointLimit : Link_Step_DaddWitnessJointLimit)
    (L_Step_DaddCollisionWitness : Link_Step_DaddCollisionWitness)
    (L_Step_DaddCollisionFirstMoment : Link_Step_DaddCollisionFirstMoment)
    (L_Step_DaddCollisionFirstMomentLaw : Link_Step_DaddCollisionFirstMomentLaw)
    (L_Step_DaddCollisionSourceIntensity : Link_Step_DaddCollisionSourceIntensity)
    (L_Step_DaddCollisionCylinder : Link_Step_DaddCollisionCylinder)
    (L_Step_DaddCollisionPerCore : Link_Step_DaddCollisionPerCore)
    (L_Step_DaddCollisionCombine : Link_Step_DaddCollisionCombine)
    (L_Step_DaddCollisionExplicit : Link_Step_DaddCollisionExplicit)
    (L_Prop_DaddCollisionLowerBound : Link_Prop_DaddCollisionLowerBound)
    (h_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density : Notation_Delta_density)
    (h_Notation_sigmaPrefix_zero : Notation_sigmaPrefix_zero)
    (h_KovacMoment_reflection : KovacMoment_reflection)
    (h_KovacS_le_S1S2 : KovacS_le_S1S2)
    (h_Eq_F2Aliquot : Eq_F2Aliquot)
    (h_Eq_DaddCollisionAffine : Eq_DaddCollisionAffine)
    (h_Step_DaddCollisionCores : Step_DaddCollisionCores)
    (h_Step_DaddCollisionH : Step_DaddCollisionH)
    (h_Step_DaddCollisionArithmetic : Step_DaddCollisionArithmetic)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Std_Mertens2 : Std_Mertens2) :
    Prop_DaddCollisionLowerBound :=
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality := L_Lem_FixedModulusNormality
      h_Std_recipPrimesAP_diverges
  have v_KovacMoment_identity : KovacMoment_identity := L_KovacMoment_identity
      h_KovacMoment_reflection
  have v_KovacMoment_reduction : KovacMoment_reduction := L_KovacMoment_reduction
      v_KovacMoment_identity
  have v_Eq_KSprime : Eq_KSprime := L_Eq_KSprime i_Std_Mertens2
  have v_Eq_KSsecond : Eq_KSsecond := L_Eq_KSsecond i_Std_Mertens2
  have v_Eq_KS : Eq_KS := L_Eq_KS h_KovacS_le_S1S2 v_Eq_KSprime v_Eq_KSsecond
  have v_Lem_KovacMoment : Lem_KovacMoment := L_Lem_KovacMoment v_KovacMoment_reduction v_Eq_KS
  have v_Fact_DaddProgressionLaws : Fact_DaddProgressionLaws := L_Fact_DaddProgressionLaws
      i_Cite_PollackAP
  have v_Step_DaddWitnessJointLimit : Step_DaddWitnessJointLimit := L_Step_DaddWitnessJointLimit
      v_Fact_DaddProgressionLaws
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
  L_Prop_DaddCollisionLowerBound v_Step_DaddCollisionExplicit h_Step_DaddCollisionArithmetic

/-! ## The whole paper

Every statement EP1054 asserts is a field of exactly one of two structures. `LeafClaims` holds
the leaves, which are proved directly from Mathlib; `DerivedClaims` holds every result and
step whose proof uses other statements (links, conjunctions and aliases, including the three
derived inputs that are links). Neither holds a trusted input, `Lem_LPInputs` (a conjunction of
inputs), the meta-claim `Rem_FraitureCheckUsage` or an unasserted `Prop`. `spine_EP1054` derives
`DerivedClaims` from the links, `LeafClaims` and the trusted inputs, so none of its conclusion's
fields is one of its hypotheses. -/

/-- The statements of EP1054 that are proved directly (from Mathlib, the definitions, `Basic` and
`Density`), one field each. -/
structure LeafClaims : Prop where
  c_Std_Mertens1 : Std_Mertens1
  c_Std_recipPrimesAP_diverges : Std_recipPrimesAP_diverges
  c_EmpiricalMeasures_isProbability : EmpiricalMeasures_isProbability
  c_Intro_f_sigma_le : Intro_f_sigma_le
  c_Notation_Delta_density : Notation_Delta_density
  c_Notation_sigmaPrefix_zero : Notation_sigmaPrefix_zero
  c_Disp_FinalDivisor : Disp_FinalDivisor
  c_Eq_Reflection : Eq_Reflection
  c_Fact_KmodGeTwo : Fact_KmodGeTwo
  c_Fact_DsetResidue : Fact_DsetResidue
  c_Lem_FraiturePrimeWindow : Lem_FraiturePrimeWindow
  c_Lem_FraitureExtension : Lem_FraitureExtension
  c_Step_FraitureSmallBq : Step_FraitureSmallBq
  c_Step_FraitureSeven : Step_FraitureSeven
  c_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes
  c_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes
  c_Step_FraitureSmallCases : Step_FraitureSmallCases
  c_KovacMoment_reflection : KovacMoment_reflection
  c_KovacS_le_S1S2 : KovacS_le_S1S2
  c_SmallUpper_emptyCase : SmallUpper_emptyCase
  c_SmallUpper_markov : SmallUpper_markov
  c_SmallUpper_paramChoice : SmallUpper_paramChoice
  c_SmallUpper_doubleExpPower : SmallUpper_doubleExpPower
  c_SmallRatio_prefixLeSig : SmallRatio_prefixLeSig
  c_SmallRatio_abundancySmall : SmallRatio_abundancySmall
  c_SmallRatio_axlerNumeric : SmallRatio_axlerNumeric
  c_Rem_Lcm289Abundant : Rem_Lcm289Abundant
  c_Rem_Lcm289Values : Rem_Lcm289Values
  c_Eq_SvBasic : Eq_SvBasic
  c_Eq_SvD : Eq_SvD
  c_Lem_SvA0Unique : Lem_SvA0Unique
  c_Lem_SvA0QLarge : Lem_SvA0QLarge
  c_SvA0_sigmaHarmonic : SvA0_sigmaHarmonic
  c_SvA0_abundancySubmul : SvA0_abundancySubmul
  c_Eq_SvHarmonicDensityZero : Eq_SvHarmonicDensityZero
  c_Eq_SvCollision : Eq_SvCollision
  c_Claim_SvSmallHSquarefree : Claim_SvSmallHSquarefree
  c_Claim_SvResiduePairCount : Claim_SvResiduePairCount
  c_Claim_SvCauchySchwarz : Claim_SvCauchySchwarz
  c_Eq_RankinKernel : Eq_RankinKernel
  c_UpperTails_Claim_EulerHigherTerms : UpperTails.Claim_EulerHigherTerms
  c_UpperTails_Claim_VA_rough : UpperTails.Claim_VA_rough
  c_UpperTails_Claim_AlmostLogTail_momentArith : UpperTails.Claim_AlmostLogTail_momentArith
  c_UpperTails_Claim_RoughNonsquarefree : UpperTails.Claim_RoughNonsquarefree
  c_UpperTails_Claim_LscaleRatio : UpperTails.Claim_LscaleRatio
  c_UpperTails_Claim_SubexpFltP : UpperTails.Claim_SubexpFltP
  c_UpperTails_Claim_SubexpCofactorOne : UpperTails.Claim_SubexpCofactorOne
  c_UpperTails_Claim_SubexpLogT : UpperTails.Claim_SubexpLogT
  c_Coverage_Fact_RtPairs : Coverage.Fact_RtPairs
  c_Coverage_Fact_RtPosIff : Coverage.Fact_RtPosIff
  c_Eq_HGcd : Eq_HGcd
  c_Eq_UClass : Eq_UClass
  c_Coverage_Step_SeDensity : Coverage.Step_SeDensity
  c_Coverage_Step_HeRatio : Coverage.Step_HeRatio
  c_Coverage_Step_SeMultiplesDens : Coverage.Step_SeMultiplesDens
  c_Coverage_Disp_CoprimeSqTail : Coverage.Disp_CoprimeSqTail
  c_Coverage_Step_DistinctPairs : Coverage.Step_DistinctPairs
  c_Coverage_Fact_GcovSubsetRtPos : Coverage.Fact_GcovSubsetRtPos
  c_Eq_F2Aliquot : Eq_F2Aliquot
  c_Coverage_Step_G2Decomp : Coverage.Step_G2Decomp
  c_Coverage_Step_P2Values : Coverage.Step_P2Values
  c_Coverage_Fact_UpperDensCompl : Coverage.Fact_UpperDensCompl
  c_Step_DaddWitnessDomination : Step_DaddWitnessDomination
  c_Step_DaddCountDomination : Step_DaddCountDomination
  c_Eq_DaddCollisionAffine : Eq_DaddCollisionAffine
  c_Step_DaddCollisionCores : Step_DaddCollisionCores
  c_Step_DaddCollisionH : Step_DaddCollisionH
  c_Step_DaddCollisionArithmetic : Step_DaddCollisionArithmetic

/-- The statements of EP1054 whose proofs use other statements, one field each. -/
structure DerivedClaims : Prop where
  c_Std_PNT : Std_PNT
  c_Std_primes_dyadic_lower : Std_primes_dyadic_lower
  c_Cite_Davenport : Cite_Davenport
  c_Intro_LiminfZero : Intro_LiminfZero
  c_Fact_KmodFinite : Fact_KmodFinite
  c_Lem_FmModulus : Lem_FmModulus
  c_Rem_RoughInputModulus : Rem_RoughInputModulus
  c_Lem_FixedModulusNormality : Lem_FixedModulusNormality
  c_Lem_SigmaRangeZero : Lem_SigmaRangeZero
  c_Lem_SigmaRate_OddPrime : Lem_SigmaRate_OddPrime
  c_Lem_SigmaRate_B2 : Lem_SigmaRate_B2
  c_Lem_SigmaRate : Lem_SigmaRate
  c_Lem_Moment : Lem_Moment
  c_Lem_AnalyticOddRepresentability_Bound : Lem_AnalyticOddRepresentability_Bound
  c_Lem_AnalyticOddRepresentability_LittleO : Lem_AnalyticOddRepresentability_LittleO
  c_Lem_AnalyticOddRepresentability : Lem_AnalyticOddRepresentability
  c_Eq_FraitureSmall : Eq_FraitureSmall
  c_Step_FraitureFirstWindowCover : Step_FraitureFirstWindowCover
  c_Eq_FraitureFirstWindow : Eq_FraitureFirstWindow
  c_Step_FraitureLargeWindowCover : Step_FraitureLargeWindowCover
  c_Step_FraitureLargePrimeSum : Step_FraitureLargePrimeSum
  c_Eq_FraitureLargeWindow : Eq_FraitureLargeWindow
  c_Prop_FraitureFinite : Prop_FraitureFinite
  c_Lem_FraitureBalancedGoldbach : Lem_FraitureBalancedGoldbach
  c_Step_FraitureTailEven : Step_FraitureTailEven
  c_Step_FraitureTailOdd : Step_FraitureTailOdd
  c_Prop_FraitureTail : Prop_FraitureTail
  c_Thm_FraitureRepresentability : Thm_FraitureRepresentability
  c_Eq_ExactRepresentability : Eq_ExactRepresentability
  c_Intro_RcntFormula : Intro_RcntFormula
  c_Thm_FraitureRepresentability_Ge6 : Thm_FraitureRepresentability_Ge6
  c_KovacMoment_identity : KovacMoment_identity
  c_KovacMoment_reduction : KovacMoment_reduction
  c_Eq_KSprime : Eq_KSprime
  c_Eq_KSsecond : Eq_KSsecond
  c_Eq_KS : Eq_KS
  c_Lem_KovacMoment : Lem_KovacMoment
  c_SmallUpper_momentStep : SmallUpper_momentStep
  c_Thm_SmallUpper_doubleExp : Thm_SmallUpper_doubleExp
  c_Thm_SmallUpper_fixedPower : Thm_SmallUpper_fixedPower
  c_Thm_SmallUpper : Thm_SmallUpper
  c_Thm_SmallUpper_upperDens : Thm_SmallUpper_upperDens
  c_Intro_LittleO_onlyOnDensityZero : Intro_LittleO_onlyOnDensityZero
  c_Prop_SmallRatioThreshold : Prop_SmallRatioThreshold
  c_Rem_Lcm289Witness : Rem_Lcm289Witness
  c_Eq_SvTwoSided : Eq_SvTwoSided
  c_SvA0_jSum : SvA0_jSum
  c_Lem_SvA0Count : Lem_SvA0Count
  c_Lem_SvA0 : Lem_SvA0
  c_Eq_SmoothPartPeriodCount : Eq_SmoothPartPeriodCount
  c_Lem_SmoothPartInput : Lem_SmoothPartInput
  c_Lem_SvRegular : Lem_SvRegular
  c_Lem_SvClasses : Lem_SvClasses
  c_Eq_SvKReciprocal : Eq_SvKReciprocal
  c_Eq_SvMReciprocal : Eq_SvMReciprocal
  c_Claim_SvSigmaDistinct : Claim_SvSigmaDistinct
  c_Claim_SvSievePairs : Claim_SvSievePairs
  c_Eq_SvTotient : Eq_SvTotient
  c_Claim_SvA3Reduction : Claim_SvA3Reduction
  c_Claim_SvLargeHUnits : Claim_SvLargeHUnits
  c_Eq_SvLargeHCongruence : Eq_SvLargeHCongruence
  c_Claim_SvLargeHRigidity : Claim_SvLargeHRigidity
  c_Claim_SvLargeH : Claim_SvLargeH
  c_Claim_SvA322Reduction : Claim_SvA322Reduction
  c_Claim_SvSmallHResidues : Claim_SvSmallHResidues
  c_Eq_SvIntermediateTotient : Eq_SvIntermediateTotient
  c_Eq_SvFSum : Eq_SvFSum
  c_Eq_SvQRSum : Eq_SvQRSum
  c_Claim_SvSmallH : Claim_SvSmallH
  c_Eq_SvReducedCollisionSum : Eq_SvReducedCollisionSum
  c_Prop_SvSecondMoment : Prop_SvSecondMoment
  c_Claim_SvClassImage : Claim_SvClassImage
  c_Claim_SvImageCount : Claim_SvImageCount
  c_Claim_SvWitness : Claim_SvWitness
  c_SvFamilyTarget : SvFamilyTarget
  c_Thm_SmallValues : Thm_SmallValues
  c_Thm_SmallValues_upperDens : Thm_SmallValues_upperDens
  c_Thm_SmallValues_lowerDens : Thm_SmallValues_lowerDens
  c_Eq_SharpPrimeSum : Eq_SharpPrimeSum
  c_Eq_FixedKernelTail : Eq_FixedKernelTail
  c_Eq_MovingKernelTail : Eq_MovingKernelTail
  c_Lem_KernelTails : Lem_KernelTails
  c_UpperTails_Claim_KA_finite : UpperTails.Claim_KA_finite
  c_UpperTails_Claim_VA_periodic : UpperTails.Claim_VA_periodic
  c_UpperTails_Claim_VA_density : UpperTails.Claim_VA_density
  c_Prop_FmEnvelope : Prop_FmEnvelope
  c_UpperTails_Claim_DeltaPfix : UpperTails.Claim_DeltaPfix
  c_UpperTails_Claim_RoughNotVA : UpperTails.Claim_RoughNotVA
  c_Cor_FmEnvelopeTail : Cor_FmEnvelopeTail
  c_UpperTails_Claim_AlmostLogTail_main : UpperTails.Claim_AlmostLogTail_main
  c_UpperTails_Claim_AlmostLogTail_fixedJ : UpperTails.Claim_AlmostLogTail_fixedJ
  c_Eq_AlmostLogTail : Eq_AlmostLogTail
  c_Thm_AlmostLogTail_posLowerDens : Thm_AlmostLogTail_posLowerDens
  c_Thm_AlmostLogTail_limsup : Thm_AlmostLogTail_limsup
  c_Thm_AlmostLogTail : Thm_AlmostLogTail
  c_Intro_ErdosLittleO_fails : Intro_ErdosLittleO_fails
  c_Intro_ErdosAlmostAllLittleO_fails : Intro_ErdosAlmostAllLittleO_fails
  c_Eq_SharpRoughTargetCount : Eq_SharpRoughTargetCount
  c_Eq_SharpBadSourceCount : Eq_SharpBadSourceCount
  c_UpperTails_Claim_SubexpBadPairs : UpperTails.Claim_SubexpBadPairs
  c_UpperTails_Claim_SubexpWitnessStructure : UpperTails.Claim_SubexpWitnessStructure
  c_Eq_MovingKernelLowerBound : Eq_MovingKernelLowerBound
  c_UpperTails_Claim_SubexpCoprimeCount : UpperTails.Claim_SubexpCoprimeCount
  c_UpperTails_Claim_SubexpLowCofactorSum : UpperTails.Claim_SubexpLowCofactorSum
  c_UpperTails_Claim_SubexpLowCofactor : UpperTails.Claim_SubexpLowCofactor
  c_UpperTails_Claim_SubexpLargeCofactor : UpperTails.Claim_SubexpLargeCofactor
  c_UpperTails_Claim_SubexpCore : UpperTails.Claim_SubexpCore
  c_UpperTails_Claim_SubexpThreshold : UpperTails.Claim_SubexpThreshold
  c_Eq_SubexpGrowth : Eq_SubexpGrowth
  c_Eq_PositiveMomentGrowth : Eq_PositiveMomentGrowth
  c_Thm_SubexpGrowth : Thm_SubexpGrowth
  c_Eq_He : Eq_He
  c_Coverage_Step_ClassResidue : Coverage.Step_ClassResidue
  c_Eq_RepresentingRatio : Eq_RepresentingRatio
  c_Coverage_Disp_HeMean : Coverage.Disp_HeMean
  c_Coverage_Step_GeLowerDens : Coverage.Step_GeLowerDens
  c_Eq_ClassLower : Eq_ClassLower
  c_Coverage_Disp_MertensCoprimeQ : Coverage.Disp_MertensCoprimeQ
  c_Coverage_Disp_ClassPrimeSum : Coverage.Disp_ClassPrimeSum
  c_Prop_ClassFirstMoment_bound : Prop_ClassFirstMoment_bound
  c_Prop_ClassFirstMoment_tendsto : Prop_ClassFirstMoment_tendsto
  c_Prop_ClassFirstMoment : Prop_ClassFirstMoment
  c_Cor_FmPrimeCeiling_congr : Cor_FmPrimeCeiling_congr
  c_Cor_FmPrimeCeiling_count : Cor_FmPrimeCeiling_count
  c_Cor_FmPrimeCeiling_upperDens : Cor_FmPrimeCeiling_upperDens
  c_Cor_FmPrimeCeiling : Cor_FmPrimeCeiling
  c_Coverage_Rem_SqfreeDefectPos : Coverage.Rem_SqfreeDefectPos
  c_Cor_FixedCofactorDefect_pos : Cor_FixedCofactorDefect_pos
  c_Eq_FixedCofactorDefect : Eq_FixedCofactorDefect
  c_Cor_FixedCofactorDefect : Cor_FixedCofactorDefect
  c_Coverage_Step_KmodSmallPrime : Coverage.Step_KmodSmallPrime
  c_Coverage_Step_GcovValuesSmallPrime : Coverage.Step_GcovValuesSmallPrime
  c_Coverage_Fact_GcovCoprimeNull : Coverage.Fact_GcovCoprimeNull
  c_Coverage_Fact_CoprimeComplementDens : Coverage.Fact_CoprimeComplementDens
  c_Eq_BoundedCofactorComplement : Eq_BoundedCofactorComplement
  c_Coverage_Disp_LogPA : Coverage.Disp_LogPA
  c_Eq_DeltaAAsymptotic : Eq_DeltaAAsymptotic
  c_Prop_EtaALower_bound : Prop_EtaALower_bound
  c_Prop_EtaALower_tendsto : Prop_EtaALower_tendsto
  c_Prop_EtaALower : Prop_EtaALower
  c_Coverage_Rem_EtaDominates : Coverage.Rem_EtaDominates
  c_Eq_F2OddNegligible : Eq_F2OddNegligible
  c_Eq_OddUntouchables : Eq_OddUntouchables
  c_Coverage_Step_EvenUntouchables : Coverage.Step_EvenUntouchables
  c_Coverage_Disp_F2Count : Coverage.Disp_F2Count
  c_Prop_ThetaTwo : Prop_ThetaTwo
  c_Coverage_Step_UpperDensG2 : Coverage.Step_UpperDensG2
  c_Cor_EtaTwo : Cor_EtaTwo
  c_Coverage_Rem_ConjEquivEta : Coverage.Rem_ConjEquivEta
  c_Coverage_Rem_RoughPartBound : Coverage.Rem_RoughPartBound
  c_Coverage_Rem_ConjEquivSmallPrimePart : Coverage.Rem_ConjEquivSmallPrimePart
  c_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl
  c_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail
  c_Prop_TightnessEquivalence : Prop_TightnessEquivalence
  c_Coverage_Rem_T_iff_Conj : Coverage.Rem_T_iff_Conj
  c_Fact_DaddDavenportLaw : Fact_DaddDavenportLaw
  c_Fact_DaddProgressionLaws : Fact_DaddProgressionLaws
  c_Eq_DaddProgressionDomination : Eq_DaddProgressionDomination
  c_Step_DaddWitnessIdentity : Step_DaddWitnessIdentity
  c_Step_DaddWitnessJointLimit : Step_DaddWitnessJointLimit
  c_Step_DaddWitnessSupport : Step_DaddWitnessSupport
  c_Step_DaddWitnessCount : Step_DaddWitnessCount
  c_Step_DaddWitnessCofactorTail : Step_DaddWitnessCofactorTail
  c_Step_DaddWitnessPieceBounds : Step_DaddWitnessPieceBounds
  c_Prop_DaddWitnessMeans : Prop_DaddWitnessMeans
  c_Rem_DaddWitnessMeanGrowth : Rem_DaddWitnessMeanGrowth
  c_Step_DaddSingularCarrier : Step_DaddSingularCarrier
  c_Step_DaddWitnessMeasureMass : Step_DaddWitnessMeasureMass
  c_Step_DaddWitnessCarrier : Step_DaddWitnessCarrier
  c_Step_DaddEmpiricalWitnessVague : Step_DaddEmpiricalWitnessVague
  c_Step_DaddLimitDomination : Step_DaddLimitDomination
  c_Thm_DaddUniversalSingularity_Carrier : Thm_DaddUniversalSingularity_Carrier
  c_Thm_DaddUniversalSingularity_FinitePart : Thm_DaddUniversalSingularity_FinitePart
  c_Thm_DaddUniversalSingularity_Tight : Thm_DaddUniversalSingularity_Tight
  c_Thm_DaddUniversalSingularity : Thm_DaddUniversalSingularity
  c_Step_DaddXoverR : Step_DaddXoverR
  c_Step_DaddLowerTailUniform : Step_DaddLowerTailUniform
  c_Eq_DaddSubsequentialTail : Eq_DaddSubsequentialTail
  c_Cor_DaddHeavyTails_PosMoments : Cor_DaddHeavyTails_PosMoments
  c_Cor_DaddHeavyTails_LogMeans : Cor_DaddHeavyTails_LogMeans
  c_Cor_DaddHeavyTails_InvMoments : Cor_DaddHeavyTails_InvMoments
  c_Cor_DaddHeavyTails_InvMomentConv : Cor_DaddHeavyTails_InvMomentConv
  c_Cor_DaddHeavyTails_GeomMean : Cor_DaddHeavyTails_GeomMean
  c_Cor_DaddHeavyTails_Tight : Cor_DaddHeavyTails_Tight
  c_Cor_DaddHeavyTails : Cor_DaddHeavyTails
  c_Step_DaddCollisionSupport : Step_DaddCollisionSupport
  c_Eq_DaddCollisionCriterion : Eq_DaddCollisionCriterion
  c_Prop_DaddCollisionCriterion : Prop_DaddCollisionCriterion
  c_Step_DaddCollisionWitness : Step_DaddCollisionWitness
  c_Step_DaddCollisionFirstMoment : Step_DaddCollisionFirstMoment
  c_Step_DaddCollisionFirstMomentLaw : Step_DaddCollisionFirstMomentLaw
  c_Step_DaddCollisionSourceIntensity : Step_DaddCollisionSourceIntensity
  c_Step_DaddCollisionCylinder : Step_DaddCollisionCylinder
  c_Step_DaddCollisionPerCore : Step_DaddCollisionPerCore
  c_Step_DaddCollisionCombine : Step_DaddCollisionCombine
  c_Step_DaddCollisionExplicit : Step_DaddCollisionExplicit
  c_Prop_DaddCollisionLowerBound : Prop_DaddCollisionLowerBound

set_option maxRecDepth 20000 in
/-- **All of EP1054**: every derived statement, from the links, the leaves (as `LeafClaims`,
68 fields, 65 of them consumed) and the trusted inputs. 182 links, 25 inputs. -/
theorem spine_EP1054
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
    (L_Lem_AnalyticOddRepresentability_Bound : Link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO : Link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_FraitureSmall : Link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover : Link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow : Link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover : Link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum : Link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow : Link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach : Link_Lem_FraitureBalancedGoldbach)
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
    (L_Eq_OddUntouchables : Link_Eq_OddUntouchables)
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
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed)
    (i_Cite_RosserSchoenfeld_psi : Cite_RosserSchoenfeld_psi) :
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
      L_Lem_AnalyticOddRepresentability_Bound i_Cite_MV_exceptional
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
      L_Lem_FraitureBalancedGoldbach i_Cite_Helfgott_weighted i_Cite_RosserSchoenfeld_psi
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
  have v_Eq_OddUntouchables : Eq_OddUntouchables := L_Eq_OddUntouchables i_Cite_MV_exceptional
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

end Principia.Erdos1054.Spine
