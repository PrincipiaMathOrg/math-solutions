/-
SOLUTION FILE -- the 33 statements of `Challenge.lean`, proved.

Each proof is a direct term assignment from a gated theorem of the vendored development (the
theorem the PrincipiaAI theorem ledger records as the result's verification). A term assignment
makes Lean check that the development theorem's type is the trusted statement constant; there is
no transport lemma and no restatement in between.

`Challenge.lean` and this file import the same statement modules, so the statement constants are
the same declarations on both sides; Comparator, which compares the two files' exports, checks
each theorem's type and every constant it mentions.

The `#print axioms` lines at the bottom are a redundant local audit; Comparator performs the
authoritative axiom check against `Challenge.lean`.
-/
import Principia.Erdos1054.Statements.S1_Main
import Principia.Erdos1054.Statements.S2_Prelim
import Principia.Erdos1054.Statements.S3_Repr
import Principia.Erdos1054.Statements.S4a_SmallUpper
import Principia.Erdos1054.Statements.S4b_SmallValues
import Principia.Erdos1054.Statements.S5_UpperTails
import Principia.Erdos1054.Statements.S6_Coverage
import Principia.Erdos1054.Statements.S7_Limits
import Principia.Erdos1054.Alt.Round4
import Principia.Erdos1054.Alt.Unconditional
import Principia.Erdos1054.Alt5.Round5
import Principia.Erdos1054.Alt6.Round6
import Principia.Erdos1054.Alt7.Round7
import Principia.Erdos1054.Proofs.Assembly

set_option autoImplicit false

namespace EP1054

/-- **Lemma `lem:fm-modulus`.** -/
theorem Lem_FmModulus : Principia.Erdos1054.Lem_FmModulus :=
  Principia.Erdos1054.Proofs.ep1054_Lem_FmModulus

/-- **Lemma `lem:fixed-modulus-normality`.** -/
theorem Lem_FixedModulusNormality : Principia.Erdos1054.Lem_FixedModulusNormality :=
  Principia.Erdos1054.Proofs.ep1054_Lem_FixedModulusNormality

/-- **Lemma `lem:sigma-range-zero`.** -/
theorem Lem_SigmaRangeZero : Principia.Erdos1054.Lem_SigmaRangeZero :=
  Principia.Erdos1054.Proofs.ep1054_Lem_SigmaRangeZero

/-- **Lemma `lem:sigma-rate`.** -/
theorem Lem_SigmaRate : Principia.Erdos1054.Lem_SigmaRate :=
  Principia.Erdos1054.Proofs.ep1054_Lem_SigmaRate

/-- **Lemma `lem:moment`.** -/
theorem Lem_Moment : Principia.Erdos1054.Lem_Moment :=
  Principia.Erdos1054.Proofs.ep1054_Lem_Moment

/-- **Lemma `lem:analytic-odd-representability`.** -/
theorem Lem_AnalyticOddRepresentability : Principia.Erdos1054.Lem_AnalyticOddRepresentability :=
  Principia.Erdos1054.Alt.Round4.ep1054_Lem_AnalyticOddRepresentability_unconditional

/-- **Proposition `prop:fraiture-finite`.** -/
theorem Prop_FraitureFinite : Principia.Erdos1054.Prop_FraitureFinite :=
  Principia.Erdos1054.Alt7.Round7.ep1054_Prop_FraitureFinite_unconditional

/-- **Lemma `lem:kovac-moment`.** -/
theorem Lem_KovacMoment : Principia.Erdos1054.Lem_KovacMoment :=
  Principia.Erdos1054.Proofs.ep1054_Lem_KovacMoment

/-- **Theorem 1.1 (`thm:small-upper`).** -/
theorem Thm_SmallUpper : Principia.Erdos1054.Thm_SmallUpper :=
  Principia.Erdos1054.Proofs.ep1054_Thm_SmallUpper

/-- **Unlabeled proposition: `f(n) <= n/10` forces `n > 10^120`.** -/
theorem Prop_SmallRatioThreshold : Principia.Erdos1054.Prop_SmallRatioThreshold :=
  Principia.Erdos1054.Alt6.Round6.ep1054_Prop_SmallRatioThreshold_unconditional

/-- **Unlabeled lemma on the family `A_0(X)`.** -/
theorem Lem_SvA0 : Principia.Erdos1054.Lem_SvA0 :=
  Principia.Erdos1054.Proofs.ep1054_Lem_SvA0

/-- **Lemma `lem:smooth-part-input`.** -/
theorem Lem_SmoothPartInput : Principia.Erdos1054.Lem_SmoothPartInput :=
  Principia.Erdos1054.Proofs.ep1054_Lem_SmoothPartInput

/-- **Lemma `lem:sv-regular`.** -/
theorem Lem_SvRegular : Principia.Erdos1054.Lem_SvRegular :=
  Principia.Erdos1054.Alt.Round4.ep1054_Lem_SvRegular_unconditional

/-- **Lemma `lem:sv-classes`.** -/
theorem Lem_SvClasses : Principia.Erdos1054.Lem_SvClasses :=
  Principia.Erdos1054.Proofs.ep1054_Lem_SvClasses

/-- **Proposition `prop:sv-second-moment`.** -/
theorem Prop_SvSecondMoment : Principia.Erdos1054.Prop_SvSecondMoment :=
  Principia.Erdos1054.Alt.ep1054_Prop_SvSecondMoment_unconditional

/-- **Theorem 1.2 (`thm:small-values`).** -/
theorem Thm_SmallValues : Principia.Erdos1054.Thm_SmallValues :=
  Principia.Erdos1054.Alt.Round4.ep1054_Thm_SmallValues_unconditional

/-- **Lemma `lem:kernel-tails`.** -/
theorem Lem_KernelTails : Principia.Erdos1054.Lem_KernelTails :=
  Principia.Erdos1054.Proofs.ep1054_Lem_KernelTails

/-- **Proposition `prop:fm-envelope`.** -/
theorem Prop_FmEnvelope : Principia.Erdos1054.Prop_FmEnvelope :=
  Principia.Erdos1054.Proofs.ep1054_Prop_FmEnvelope

/-- **Corollary `cor:fm-envelope-tail`.** -/
theorem Cor_FmEnvelopeTail : Principia.Erdos1054.Cor_FmEnvelopeTail :=
  Principia.Erdos1054.Proofs.ep1054_Cor_FmEnvelopeTail

/-- **Theorem 1.3 (`thm:almost-log-tail`).** -/
theorem Thm_AlmostLogTail : Principia.Erdos1054.Thm_AlmostLogTail :=
  Principia.Erdos1054.Alt.ep1054_Thm_AlmostLogTail_unconditional

/-- **Theorem 1.4 (`thm:subexp-growth`).** -/
theorem Thm_SubexpGrowth : Principia.Erdos1054.Thm_SubexpGrowth :=
  Principia.Erdos1054.Alt.Round4.ep1054_Thm_SubexpGrowth_unconditional

/-- **Proposition `prop:class-first-moment`.** -/
theorem Prop_ClassFirstMoment : Principia.Erdos1054.Prop_ClassFirstMoment :=
  Principia.Erdos1054.Proofs.ep1054_Prop_ClassFirstMoment

/-- **Corollary: prime cofactor ceiling (label commented out in the source).** -/
theorem Cor_FmPrimeCeiling : Principia.Erdos1054.Cor_FmPrimeCeiling :=
  Principia.Erdos1054.Proofs.ep1054_Cor_FmPrimeCeiling

/-- **Unlabeled corollary: fixed-cofactor defect.** -/
theorem Cor_FixedCofactorDefect : Principia.Erdos1054.Cor_FixedCofactorDefect :=
  Principia.Erdos1054.Alt.ep1054_Cor_FixedCofactorDefect_unconditional

/-- **Unlabeled proposition: lower bound for `eta_A`.** -/
theorem Prop_EtaALower : Principia.Erdos1054.Prop_EtaALower :=
  Principia.Erdos1054.Alt.ep1054_Prop_EtaALower_unconditional

/-- **Proposition `prop:theta-two`.** -/
theorem Prop_ThetaTwo : Principia.Erdos1054.Prop_ThetaTwo :=
  Principia.Erdos1054.Alt6.Round6.ep1054_Prop_ThetaTwo_unconditional

/-- **Unlabeled corollary: lower bound for `eta_2`.** -/
theorem Cor_EtaTwo : Principia.Erdos1054.Cor_EtaTwo :=
  Principia.Erdos1054.Alt6.Round6.ep1054_Cor_EtaTwo_unconditional

/-- **Proposition `prop:tightness-equivalence`.** -/
theorem Prop_TightnessEquivalence : Principia.Erdos1054.Prop_TightnessEquivalence :=
  Principia.Erdos1054.Alt5.Round5.ep1054_Prop_TightnessEquivalence_unconditional

/-- **Proposition `prop:dadd:witness-means`.** -/
theorem Prop_DaddWitnessMeans : Principia.Erdos1054.Prop_DaddWitnessMeans :=
  Principia.Erdos1054.Alt.ep1054_Prop_DaddWitnessMeans_unconditional

/-- **Theorem `thm:dadd:universal-singularity`.** -/
theorem Thm_DaddUniversalSingularity : Principia.Erdos1054.Thm_DaddUniversalSingularity :=
  Principia.Erdos1054.Alt5.Round5.ep1054_Thm_DaddUniversalSingularity_unconditional

/-- **Unlabeled corollary: heavy tails of subsequential limits.** -/
theorem Cor_DaddHeavyTails : Principia.Erdos1054.Cor_DaddHeavyTails :=
  Principia.Erdos1054.Alt5.Round5.ep1054_Cor_DaddHeavyTails_unconditional

/-- **Proposition `prop:dadd:collision-criterion`.** -/
theorem Prop_DaddCollisionCriterion : Principia.Erdos1054.Prop_DaddCollisionCriterion :=
  Principia.Erdos1054.Alt5.Round5.ep1054_Prop_DaddCollisionCriterion_unconditional

/-- **Unlabeled proposition: collision lower bound.** -/
theorem Prop_DaddCollisionLowerBound : Principia.Erdos1054.Prop_DaddCollisionLowerBound :=
  Principia.Erdos1054.Alt.ep1054_Prop_DaddCollisionLowerBound_unconditional

#print axioms Lem_FmModulus
#print axioms Lem_FixedModulusNormality
#print axioms Lem_SigmaRangeZero
#print axioms Lem_SigmaRate
#print axioms Lem_Moment
#print axioms Lem_AnalyticOddRepresentability
#print axioms Prop_FraitureFinite
#print axioms Lem_KovacMoment
#print axioms Thm_SmallUpper
#print axioms Prop_SmallRatioThreshold
#print axioms Lem_SvA0
#print axioms Lem_SmoothPartInput
#print axioms Lem_SvRegular
#print axioms Lem_SvClasses
#print axioms Prop_SvSecondMoment
#print axioms Thm_SmallValues
#print axioms Lem_KernelTails
#print axioms Prop_FmEnvelope
#print axioms Cor_FmEnvelopeTail
#print axioms Thm_AlmostLogTail
#print axioms Thm_SubexpGrowth
#print axioms Prop_ClassFirstMoment
#print axioms Cor_FmPrimeCeiling
#print axioms Cor_FixedCofactorDefect
#print axioms Prop_EtaALower
#print axioms Prop_ThetaTwo
#print axioms Cor_EtaTwo
#print axioms Prop_TightnessEquivalence
#print axioms Prop_DaddWitnessMeans
#print axioms Thm_DaddUniversalSingularity
#print axioms Cor_DaddHeavyTails
#print axioms Prop_DaddCollisionCriterion
#print axioms Prop_DaddCollisionLowerBound

end EP1054
