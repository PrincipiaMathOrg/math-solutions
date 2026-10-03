/-
TRUSTED CHALLENGE FILE -- the 33 Lean-verified results of the EP1054 paper, without proofs.

Paper: "On the first occurrence of an integer as a prefix sum of divisors" (H. Chae, J. Fraiture,
E. Hou, V. Kovac, C. Kudeba, A. Shakov, D. Vidal), unpublished manuscript of 2026-09-25, committed
at `paper/EP1054.tex` (sha256-pinned in `paper/SHA256SUMS`). Each result is cited below by its
LaTeX label.

This file is the audit surface, together with the statement modules it imports. Comparator
(github.com/leanprover/comparator) checks that the declarations of the same names in
`Solution.lean` prove EXACTLY these statements and use no axioms beyond `propext`, `Quot.sound`,
`Classical.choice`.

The `sorry`s below are deliberate: 33 of them, one per result, and they are the only `sorry`s in
`erdos1054/ep1054/`. Any `sorry` scan must exclude this file; see `VERIFICATION.md`.

IMPORT CLOSURE. Mathlib, plus exactly ten vendored modules: `Principia/Erdos1054/Defs.lean` and
the nine `Principia/Erdos1054/Statements/*.lean` (`Inputs` arrives through the others). Those ten
files contain 450 `def`/`abbrev`/`structure` declarations and nothing else -- no theorem, no
lemma, no axiom, no instance, no notation -- and each statement below is a single constant of
theirs. They are therefore part of what must be read: `Principia.Erdos1054.Lem_FmModulus` IS the
statement of `lem:fm-modulus`, and its docstring quotes the paper's text beside the encoding.
Each theorem's docstring names the file and line of its `def`.

This differs from the repository's other folders, whose `Challenge.lean` imports only Mathlib
and carries a verbatim copy of its statement module (the Palomar policy). Here the statement layer
is ~6.5k lines; it is imported rather than copied, so there is no second copy to drift. See
`README.md`.

NOT HERE: the four results that rest on Helfgott's weighted ternary Goldbach theorem
(`lem:fraiture-balanced-goldbach`, `prop:fraiture-tail`, `thm:fraiture-representability`,
`eq:exact-representability`). They are not proved unconditionally, so they are not challenged; their
conditional proofs are in `Conditional.lean`, with every hypothesis named.
-/
import Principia.Erdos1054.Statements.S1_Main
import Principia.Erdos1054.Statements.S2_Prelim
import Principia.Erdos1054.Statements.S3_Repr
import Principia.Erdos1054.Statements.S4a_SmallUpper
import Principia.Erdos1054.Statements.S4b_SmallValues
import Principia.Erdos1054.Statements.S5_UpperTails
import Principia.Erdos1054.Statements.S6_Coverage
import Principia.Erdos1054.Statements.S7_Limits

set_option autoImplicit false

namespace EP1054

/-- **Lemma `lem:fm-modulus`.** Statement: `Principia.Erdos1054.Lem_FmModulus`
(`Principia/Erdos1054/Statements/S2_Prelim.lean`, line 206). -/
theorem Lem_FmModulus : Principia.Erdos1054.Lem_FmModulus := by
  sorry

/-- **Lemma `lem:fixed-modulus-normality`.** Statement: `Principia.Erdos1054.Lem_FixedModulusNormality`
(`Principia/Erdos1054/Statements/S2_Prelim.lean`, line 248). -/
theorem Lem_FixedModulusNormality : Principia.Erdos1054.Lem_FixedModulusNormality := by
  sorry

/-- **Lemma `lem:sigma-range-zero`.** Statement: `Principia.Erdos1054.Lem_SigmaRangeZero`
(`Principia/Erdos1054/Statements/S2_Prelim.lean`, line 259). -/
theorem Lem_SigmaRangeZero : Principia.Erdos1054.Lem_SigmaRangeZero := by
  sorry

/-- **Lemma `lem:sigma-rate`.** Statement: `Principia.Erdos1054.Lem_SigmaRate`
(`Principia/Erdos1054/Statements/S2_Prelim.lean`, line 315). -/
theorem Lem_SigmaRate : Principia.Erdos1054.Lem_SigmaRate := by
  sorry

/-- **Lemma `lem:moment`.** Statement: `Principia.Erdos1054.Lem_Moment`
(`Principia/Erdos1054/Statements/S2_Prelim.lean`, line 408). -/
theorem Lem_Moment : Principia.Erdos1054.Lem_Moment := by
  sorry

/-- **Lemma `lem:analytic-odd-representability`.** Statement: `Principia.Erdos1054.Lem_AnalyticOddRepresentability`
(`Principia/Erdos1054/Statements/S3_Repr.lean`, line 87). -/
theorem Lem_AnalyticOddRepresentability : Principia.Erdos1054.Lem_AnalyticOddRepresentability := by
  sorry

/-- **Proposition `prop:fraiture-finite`.** Statement: `Principia.Erdos1054.Prop_FraitureFinite`
(`Principia/Erdos1054/Statements/S3_Repr.lean`, line 248). -/
theorem Prop_FraitureFinite : Principia.Erdos1054.Prop_FraitureFinite := by
  sorry

/-- **Lemma `lem:kovac-moment`.** Statement: `Principia.Erdos1054.Lem_KovacMoment`
(`Principia/Erdos1054/Statements/S4a_SmallUpper.lean`, line 156). -/
theorem Lem_KovacMoment : Principia.Erdos1054.Lem_KovacMoment := by
  sorry

/-- **Theorem 1.1 (`thm:small-upper`).** Statement: `Principia.Erdos1054.Thm_SmallUpper`
(`Principia/Erdos1054/Statements/S1_Main.lean`, line 207). -/
theorem Thm_SmallUpper : Principia.Erdos1054.Thm_SmallUpper := by
  sorry

/-- **Unlabeled proposition: `f(n) <= n/10` forces `n > 10^120`.** Statement: `Principia.Erdos1054.Prop_SmallRatioThreshold`
(`Principia/Erdos1054/Statements/S4a_SmallUpper.lean`, line 351). -/
theorem Prop_SmallRatioThreshold : Principia.Erdos1054.Prop_SmallRatioThreshold := by
  sorry

/-- **Unlabeled lemma on the family `A_0(X)`.** Statement: `Principia.Erdos1054.Lem_SvA0`
(`Principia/Erdos1054/Statements/S4a_SmallUpper.lean`, line 548). -/
theorem Lem_SvA0 : Principia.Erdos1054.Lem_SvA0 := by
  sorry

/-- **Lemma `lem:smooth-part-input`.** Statement: `Principia.Erdos1054.Lem_SmoothPartInput`
(`Principia/Erdos1054/Statements/S4b_SmallValues.lean`, line 312). -/
theorem Lem_SmoothPartInput : Principia.Erdos1054.Lem_SmoothPartInput := by
  sorry

/-- **Lemma `lem:sv-regular`.** Statement: `Principia.Erdos1054.Lem_SvRegular`
(`Principia/Erdos1054/Statements/S4b_SmallValues.lean`, line 363). -/
theorem Lem_SvRegular : Principia.Erdos1054.Lem_SvRegular := by
  sorry

/-- **Lemma `lem:sv-classes`.** Statement: `Principia.Erdos1054.Lem_SvClasses`
(`Principia/Erdos1054/Statements/S4b_SmallValues.lean`, line 387). -/
theorem Lem_SvClasses : Principia.Erdos1054.Lem_SvClasses := by
  sorry

/-- **Proposition `prop:sv-second-moment`.** Statement: `Principia.Erdos1054.Prop_SvSecondMoment`
(`Principia/Erdos1054/Statements/S4b_SmallValues.lean`, line 411). -/
theorem Prop_SvSecondMoment : Principia.Erdos1054.Prop_SvSecondMoment := by
  sorry

/-- **Theorem 1.2 (`thm:small-values`).** Statement: `Principia.Erdos1054.Thm_SmallValues`
(`Principia/Erdos1054/Statements/S1_Main.lean`, line 243). -/
theorem Thm_SmallValues : Principia.Erdos1054.Thm_SmallValues := by
  sorry

/-- **Lemma `lem:kernel-tails`.** Statement: `Principia.Erdos1054.Lem_KernelTails`
(`Principia/Erdos1054/Statements/S5_UpperTails.lean`, line 166). -/
theorem Lem_KernelTails : Principia.Erdos1054.Lem_KernelTails := by
  sorry

/-- **Proposition `prop:fm-envelope`.** Statement: `Principia.Erdos1054.Prop_FmEnvelope`
(`Principia/Erdos1054/Statements/S5_UpperTails.lean`, line 257). -/
theorem Prop_FmEnvelope : Principia.Erdos1054.Prop_FmEnvelope := by
  sorry

/-- **Corollary `cor:fm-envelope-tail`.** Statement: `Principia.Erdos1054.Cor_FmEnvelopeTail`
(`Principia/Erdos1054/Statements/S5_UpperTails.lean`, line 317). -/
theorem Cor_FmEnvelopeTail : Principia.Erdos1054.Cor_FmEnvelopeTail := by
  sorry

/-- **Theorem 1.3 (`thm:almost-log-tail`).** Statement: `Principia.Erdos1054.Thm_AlmostLogTail`
(`Principia/Erdos1054/Statements/S1_Main.lean`, line 314). -/
theorem Thm_AlmostLogTail : Principia.Erdos1054.Thm_AlmostLogTail := by
  sorry

/-- **Theorem 1.4 (`thm:subexp-growth`).** Statement: `Principia.Erdos1054.Thm_SubexpGrowth`
(`Principia/Erdos1054/Statements/S1_Main.lean`, line 376). -/
theorem Thm_SubexpGrowth : Principia.Erdos1054.Thm_SubexpGrowth := by
  sorry

/-- **Proposition `prop:class-first-moment`.** Statement: `Principia.Erdos1054.Prop_ClassFirstMoment`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 216). -/
theorem Prop_ClassFirstMoment : Principia.Erdos1054.Prop_ClassFirstMoment := by
  sorry

/-- **Corollary: prime cofactor ceiling (label commented out in the source).** Statement: `Principia.Erdos1054.Cor_FmPrimeCeiling`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 566). -/
theorem Cor_FmPrimeCeiling : Principia.Erdos1054.Cor_FmPrimeCeiling := by
  sorry

/-- **Unlabeled corollary: fixed-cofactor defect.** Statement: `Principia.Erdos1054.Cor_FixedCofactorDefect`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 628). -/
theorem Cor_FixedCofactorDefect : Principia.Erdos1054.Cor_FixedCofactorDefect := by
  sorry

/-- **Unlabeled proposition: lower bound for `eta_A`.** Statement: `Principia.Erdos1054.Prop_EtaALower`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 767). -/
theorem Prop_EtaALower : Principia.Erdos1054.Prop_EtaALower := by
  sorry

/-- **Proposition `prop:theta-two`.** Statement: `Principia.Erdos1054.Prop_ThetaTwo`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 874). -/
theorem Prop_ThetaTwo : Principia.Erdos1054.Prop_ThetaTwo := by
  sorry

/-- **Unlabeled corollary: lower bound for `eta_2`.** Statement: `Principia.Erdos1054.Cor_EtaTwo`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 906). -/
theorem Cor_EtaTwo : Principia.Erdos1054.Cor_EtaTwo := by
  sorry

/-- **Proposition `prop:tightness-equivalence`.** Statement: `Principia.Erdos1054.Prop_TightnessEquivalence`
(`Principia/Erdos1054/Statements/S6_Coverage.lean`, line 1041). -/
theorem Prop_TightnessEquivalence : Principia.Erdos1054.Prop_TightnessEquivalence := by
  sorry

/-- **Proposition `prop:dadd:witness-means`.** Statement: `Principia.Erdos1054.Prop_DaddWitnessMeans`
(`Principia/Erdos1054/Statements/S7_Limits.lean`, line 449). -/
theorem Prop_DaddWitnessMeans : Principia.Erdos1054.Prop_DaddWitnessMeans := by
  sorry

/-- **Theorem `thm:dadd:universal-singularity`.** Statement: `Principia.Erdos1054.Thm_DaddUniversalSingularity`
(`Principia/Erdos1054/Statements/S7_Limits.lean`, line 649). -/
theorem Thm_DaddUniversalSingularity : Principia.Erdos1054.Thm_DaddUniversalSingularity := by
  sorry

/-- **Unlabeled corollary: heavy tails of subsequential limits.** Statement: `Principia.Erdos1054.Cor_DaddHeavyTails`
(`Principia/Erdos1054/Statements/S7_Limits.lean`, line 776). -/
theorem Cor_DaddHeavyTails : Principia.Erdos1054.Cor_DaddHeavyTails := by
  sorry

/-- **Proposition `prop:dadd:collision-criterion`.** Statement: `Principia.Erdos1054.Prop_DaddCollisionCriterion`
(`Principia/Erdos1054/Statements/S7_Limits.lean`, line 827). -/
theorem Prop_DaddCollisionCriterion : Principia.Erdos1054.Prop_DaddCollisionCriterion := by
  sorry

/-- **Unlabeled proposition: collision lower bound.** Statement: `Principia.Erdos1054.Prop_DaddCollisionLowerBound`
(`Principia/Erdos1054/Statements/S7_Limits.lean`, line 1039). -/
theorem Prop_DaddCollisionLowerBound : Principia.Erdos1054.Prop_DaddCollisionLowerBound := by
  sorry

end EP1054
