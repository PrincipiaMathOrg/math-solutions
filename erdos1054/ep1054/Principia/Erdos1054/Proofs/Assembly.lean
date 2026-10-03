/-
Copyright (c) 2026 PrincipiaAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PrincipiaAI
-/
import Principia.Erdos1054.Proofs.A0Family
import Principia.Erdos1054.Proofs.BalancedNoRS
import Principia.Erdos1054.Proofs.ClassMoment
import Principia.Erdos1054.Proofs.Collision7
import Principia.Erdos1054.Proofs.CoverageEta
import Principia.Erdos1054.Proofs.Envelope
import Principia.Erdos1054.Proofs.FmModulus
import Principia.Erdos1054.Proofs.InputsBT
import Principia.Erdos1054.Proofs.InputsPNT
import Principia.Erdos1054.Proofs.InputsSW
import Principia.Erdos1054.Proofs.InputsStd
import Principia.Erdos1054.Proofs.Intro
import Principia.Erdos1054.Proofs.KernelTails
import Principia.Erdos1054.Proofs.Kovac
import Principia.Erdos1054.Proofs.Moment
import Principia.Erdos1054.Proofs.Normality
import Principia.Erdos1054.Proofs.OddRepr
import Principia.Erdos1054.Proofs.Repr122
import Principia.Erdos1054.Proofs.ReprElementary
import Principia.Erdos1054.Proofs.SigmaRate
import Principia.Erdos1054.Proofs.Singularity
import Principia.Erdos1054.Proofs.SmallRatio
import Principia.Erdos1054.Proofs.SvLargeH
import Principia.Erdos1054.Proofs.SvRegular
import Principia.Erdos1054.Proofs.SvSmallH
import Principia.Erdos1054.Proofs.ThetaTight
import Principia.Erdos1054.Proofs.Thm11
import Principia.Erdos1054.Proofs.Thm12
import Principia.Erdos1054.Proofs.Thm13
import Principia.Erdos1054.Proofs.Thm14
import Principia.Erdos1054.Proofs.WitnessMeans
import Principia.Erdos1054.Alt.GoldbachRoute

/-!
# EP1054 assembled: every headline from the proved links, leaves and inputs

GENERATED from `Spine.lean` by the assembler's `gen_assembly.py` (round 2, 2026-09-26);
regenerate rather than hand-edit when the spine or a proof package changes.

For every `Spine.spine_X` there is one `ep1054_X` (and `ep1054_all` for `spine_EP1054`). It
states the headline `Prop` and takes as hypotheses **exactly** the spine arguments that have
no Lean proof, which are all trusted inputs. Every other argument is supplied by name: a
`link_Y` for `Spine.Link_Y`, a `leaf_Y` for a leaf, an `input_Y` for a discharged input. The
named-argument application is checked by the elaborator, so a provider of the wrong type
cannot slip in.

**Rosser-Schoenfeld.** `Proofs.balancedGoldbach_of_helfgott_noRS` proves
`Cite_Helfgott_weighted -> Lem_FraitureBalancedGoldbach` with Mathlib's
`theta(x) <= x log 4` in place of `Cite_RosserSchoenfeld_psi`. The DAG still records the
paper's argument (which cites RS), so each spine that binds that input is re-composed here as
`Assembly.noRS_X`: a mechanical copy of the spine's proof term with that one application
replaced. Once `dag.py` drops the cite, these copies can go and `ep1054_X` can call the spine.

**Alternative route to Theorem 1.3.** `ep1054_Thm_AlmostLogTail_viaGoldbach` and
`ep1054_Cor_FixedCofactorDefect_viaGoldbach` take only `Alt.Std_GoldbachDensZero` (binary
Goldbach for almost all even numbers, density form), from `Principia.Erdos1054.Alt.GoldbachRoute`.
-/

set_option autoImplicit false

namespace Principia.Erdos1054.Proofs.Assembly

open Principia.Erdos1054 Principia.Erdos1054.Spine

set_option maxRecDepth 20000 in
/-- `Spine.spine_Lem_FraitureBalancedGoldbach` with `Cite_RosserSchoenfeld_psi` removed: a
mechanical copy of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Lem_FraitureBalancedGoldbach
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Lem_FraitureBalancedGoldbach :=
  (Principia.Erdos1054.Proofs.balancedGoldbach_of_helfgott_noRS i_Cite_Helfgott_weighted)

set_option maxRecDepth 20000 in
/-- `Spine.spine_Prop_FraitureTail` with `Cite_RosserSchoenfeld_psi` removed: a mechanical copy of
its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Prop_FraitureTail
    (L_Step_FraitureTailEven : Link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd : Link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail : Link_Prop_FraitureTail)
    (h_Step_FraitureTailThreePrimes : Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes : Step_FraitureTailFourPrimes)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Prop_FraitureTail :=
  have v_Lem_FraitureBalancedGoldbach : Lem_FraitureBalancedGoldbach :=
      (Principia.Erdos1054.Proofs.balancedGoldbach_of_helfgott_noRS i_Cite_Helfgott_weighted)
  have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
  have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
  L_Prop_FraitureTail v_Step_FraitureTailEven v_Step_FraitureTailOdd

set_option maxRecDepth 20000 in
/-- `Spine.spine_Thm_FraitureRepresentability` with `Cite_RosserSchoenfeld_psi` removed: a
mechanical copy of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Thm_FraitureRepresentability
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
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
      (Principia.Erdos1054.Proofs.balancedGoldbach_of_helfgott_noRS i_Cite_Helfgott_weighted)
  have v_Step_FraitureTailEven : Step_FraitureTailEven := L_Step_FraitureTailEven
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailThreePrimes
  have v_Step_FraitureTailOdd : Step_FraitureTailOdd := L_Step_FraitureTailOdd
      v_Lem_FraitureBalancedGoldbach h_Step_FraitureTailFourPrimes
  have v_Prop_FraitureTail : Prop_FraitureTail := L_Prop_FraitureTail v_Step_FraitureTailEven
      v_Step_FraitureTailOdd
  L_Thm_FraitureRepresentability v_Prop_FraitureFinite v_Prop_FraitureTail h_Step_FraitureSmallCases

set_option maxRecDepth 20000 in
/-- `Spine.spine_Eq_ExactRepresentability` with `Cite_RosserSchoenfeld_psi` removed: a mechanical
copy of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Eq_ExactRepresentability
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
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
  v_Thm_FraitureRepresentability

set_option maxRecDepth 20000 in
/-- `Spine.spine_Prop_TightnessEquivalence` with `Cite_RosserSchoenfeld_psi` removed: a mechanical
copy of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Prop_TightnessEquivalence
    (L_Lem_Moment : Link_Lem_Moment)
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
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
  have v_Coverage_Disp_TailLeCompl : Coverage.Disp_TailLeCompl := L_Coverage_Disp_TailLeCompl
      v_Intro_RcntFormula
  have v_Coverage_Disp_ComplLeTail : Coverage.Disp_ComplLeTail := L_Coverage_Disp_ComplLeTail
      v_Lem_Moment v_Eq_ExactRepresentability
  L_Prop_TightnessEquivalence v_Coverage_Disp_TailLeCompl v_Coverage_Disp_ComplLeTail
      h_Coverage_Fact_UpperDensCompl

set_option maxRecDepth 20000 in
/-- `Spine.spine_Thm_DaddUniversalSingularity` with `Cite_RosserSchoenfeld_psi` removed: a
mechanical copy of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Thm_DaddUniversalSingularity
    (L_Std_primes_dyadic_lower : Link_Std_primes_dyadic_lower)
    (L_Cite_Davenport : Link_Cite_Davenport)
    (L_Lem_Moment : Link_Lem_Moment)
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
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
/-- `Spine.spine_Cor_DaddHeavyTails` with `Cite_RosserSchoenfeld_psi` removed: a mechanical copy
of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Cor_DaddHeavyTails
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
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
/-- `Spine.spine_Prop_DaddCollisionCriterion` with `Cite_RosserSchoenfeld_psi` removed: a
mechanical copy of its proof term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_Prop_DaddCollisionCriterion
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
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
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
/-- `Spine.spine_EP1054` with `Cite_RosserSchoenfeld_psi` removed: a mechanical copy of its proof
term (generated from `Spine.lean`). Each application of the link
`L_Lem_FraitureBalancedGoldbach` to Helfgott and Rosser-Schoenfeld (1 here) is replaced by
`Proofs.balancedGoldbach_of_helfgott_noRS` applied to Helfgott alone; nothing else changes. -/
theorem noRS_EP1054
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

end Principia.Erdos1054.Proofs.Assembly

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054 Principia.Erdos1054.Spine

set_option maxRecDepth 20000 in
/-- **Lem_LPInputs** — lem:LP-inputs; the body IS the conjunction of the three LP inputs, so it is
trusted input, not a Claims field. Paper lines 1316-1344. A conjunction of trusted inputs:
nothing to prove, and not a claim.

Supplied from proofs: 0 links, 0 leaves, 0 discharged inputs. Composed by
`Spine.spine_Lem_LPInputs`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.

`Lem_LPInputs` is the conjunction of three trusted inputs, so this theorem is `And.intro`; it
is stated for completeness, not as a claim. -/
theorem ep1054_Lem_LPInputs
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25) :
    Lem_LPInputs :=
  Spine.spine_Lem_LPInputs
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)

set_option maxRecDepth 20000 in
/-- **Lem_FmModulus** — lem:fm-modulus; Fact_KmodGeTwo gives d0 = M/g >= 1 in the maximality
clause. Paper lines 406-440.

Supplied from proofs: 1 links, 1 leaves, 0 discharged inputs. Composed by
`Spine.spine_Lem_FmModulus`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_FmModulus : Lem_FmModulus :=
  Spine.spine_Lem_FmModulus
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)

set_option maxRecDepth 20000 in
/-- **Lem_FixedModulusNormality** — lem:fixed-modulus-normality. Paper lines 452-480.

Supplied from proofs: 1 links, 1 leaves, 0 discharged inputs. Composed by
`Spine.spine_Lem_FixedModulusNormality`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_FixedModulusNormality : Lem_FixedModulusNormality :=
  Spine.spine_Lem_FixedModulusNormality
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)

set_option maxRecDepth 20000 in
/-- **Lem_SigmaRangeZero** — lem:sigma-range-zero. Paper lines 484-498.

Supplied from proofs: 2 links, 1 leaves, 0 discharged inputs. Composed by
`Spine.spine_Lem_SigmaRangeZero`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_SigmaRangeZero : Lem_SigmaRangeZero :=
  Spine.spine_Lem_SigmaRangeZero
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)

set_option maxRecDepth 20000 in
/-- **Lem_SigmaRate** — lem:sigma-rate. Paper lines 508-560.

Supplied from proofs: 2 links, 0 leaves, 3 discharged inputs. Composed by
`Spine.spine_Lem_SigmaRate`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_SigmaRate : Lem_SigmaRate :=
  Spine.spine_Lem_SigmaRate
    (L_Lem_SigmaRate_OddPrime := link_Lem_SigmaRate_OddPrime)
    (L_Lem_SigmaRate_B2 := link_Lem_SigmaRate_B2)
    (i_Cite_Pollack_Lemma24 := input_Cite_Pollack_Lemma24)
    (i_Std_SiegelWalfisz_dyadic := input_Std_SiegelWalfisz_dyadic)
    (i_Std_sigma_odd_iff := input_Std_sigma_odd_iff)

set_option maxRecDepth 20000 in
/-- **Lem_Moment** — lem:moment; zeta bound from Mathlib ZetaAsymptotics. Paper lines 565-638.

Supplied from proofs: 1 links, 1 leaves, 0 discharged inputs. Composed by
`Spine.spine_Lem_Moment`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_Moment : Lem_Moment :=
  Spine.spine_Lem_Moment
    (L_Lem_Moment := link_Lem_Moment)
    (h_Eq_Reflection := leaf_Eq_Reflection)

set_option maxRecDepth 20000 in
/-- **Lem_AnalyticOddRepresentability** — lem:analytic-odd-representability. Paper lines 651-670.

Supplied from proofs: 2 links, 0 leaves, 0 discharged inputs. Composed by
`Spine.spine_Lem_AnalyticOddRepresentability`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes. -/
theorem ep1054_Lem_AnalyticOddRepresentability
    (i_Cite_MV_exceptional : Cite_MV_exceptional) :
    Lem_AnalyticOddRepresentability :=
  Spine.spine_Lem_AnalyticOddRepresentability
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)

set_option maxRecDepth 20000 in
/-- **Prop_FraitureFinite** — prop:fraiture-finite. Paper lines 726-823.

Supplied from proofs: 6 links, 4 leaves, 0 discharged inputs. Composed by
`Spine.spine_Prop_FraitureFinite`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Prop_FraitureFinite
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Prop_FraitureFinite :=
  Spine.spine_Prop_FraitureFinite
    (L_Eq_FraitureSmall := link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover := link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow := link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover := link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum := link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow := link_Eq_FraitureLargeWindow)
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Lem_FraitureBalancedGoldbach** — lem:fraiture-balanced-goldbach; the paper's reduction of
Helfgott's weighted bound (discard triples with a coordinate <= z or a repeated coordinate).
Paper lines 846-854; proof 856-898.

Supplied from proofs: 0 links, 0 leaves, 0 discharged inputs. Composed through
`Assembly.noRS_Lem_FraitureBalancedGoldbach` (the spine with `Cite_RosserSchoenfeld_psi`
removed; Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms). -/
theorem ep1054_Lem_FraitureBalancedGoldbach
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Lem_FraitureBalancedGoldbach :=
  Assembly.noRS_Lem_FraitureBalancedGoldbach
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)

set_option maxRecDepth 20000 in
/-- **Prop_FraitureTail** — prop:fraiture-tail. Paper lines 900-953.

Supplied from proofs: 3 links, 2 leaves, 0 discharged inputs. Composed through
`Assembly.noRS_Prop_FraitureTail` (the spine with `Cite_RosserSchoenfeld_psi` removed;
Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms). -/
theorem ep1054_Prop_FraitureTail
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Prop_FraitureTail :=
  Assembly.noRS_Prop_FraitureTail
    (L_Step_FraitureTailEven := link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd := link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail := link_Prop_FraitureTail)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)

set_option maxRecDepth 20000 in
/-- **Thm_FraitureRepresentability** — thm:fraiture-representability; abbrev of
Eq_ExactRepresentability (one Link serves both). Paper lines 677-684; proof 955-966.

Supplied from proofs: 10 links, 7 leaves, 0 discharged inputs. Composed through
`Assembly.noRS_Thm_FraitureRepresentability` (the spine with `Cite_RosserSchoenfeld_psi`
removed; Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Thm_FraitureRepresentability
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Thm_FraitureRepresentability :=
  Assembly.noRS_Thm_FraitureRepresentability
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
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Eq_ExactRepresentability** — eq:exact-representability; SAME Prop as
Thm_FraitureRepresentability (abbrev). Paper lines 114-115 (proved as
thm:fraiture-representability).

Supplied from proofs: 10 links, 7 leaves, 0 discharged inputs. Composed through
`Assembly.noRS_Eq_ExactRepresentability` (the spine with `Cite_RosserSchoenfeld_psi` removed;
Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Eq_ExactRepresentability
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Eq_ExactRepresentability :=
  Assembly.noRS_Eq_ExactRepresentability
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
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Rem_FraitureCheckUsage** — remark environment, a META-CLAIM about proofs (not a Claims
field: as a Prop it follows from the three conclusions and says nothing); its content is the
signature of its spine, which composes the links of the three sub-DAGs with only the named
inputs in scope, so Lean checks each sub-DAG uses AT MOST those inputs and gen.py checks
EXACTLY those. Paper lines 969-979. **The content of this theorem is its signature**: no input
is in scope except the ones each part binds, so Lean checks that each sub-DAG uses at most
those inputs, and `gen.py` checks that it uses exactly those. Its conclusion alone would
follow from the three conclusions and say nothing.

Supplied from proofs: 13 links, 7 leaves, 0 discharged inputs. Composed by
`Spine.spine_Rem_FraitureCheckUsage`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`).

A meta-claim: as a `Prop` it follows from the three conclusions. Its content is the signature
of `Spine.spine_Rem_FraitureCheckUsage` (each sub-DAG uses at most the inputs the remark
names). -/
theorem ep1054_Rem_FraitureCheckUsage : Rem_FraitureCheckUsage :=
  Spine.spine_Rem_FraitureCheckUsage
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_FraitureSmall := link_Eq_FraitureSmall)
    (L_Step_FraitureFirstWindowCover := link_Step_FraitureFirstWindowCover)
    (L_Eq_FraitureFirstWindow := link_Eq_FraitureFirstWindow)
    (L_Step_FraitureLargeWindowCover := link_Step_FraitureLargeWindowCover)
    (L_Step_FraitureLargePrimeSum := link_Step_FraitureLargePrimeSum)
    (L_Eq_FraitureLargeWindow := link_Eq_FraitureLargeWindow)
    (L_Lem_FraitureBalancedGoldbach := link_Lem_FraitureBalancedGoldbach)
    (L_Step_FraitureTailEven := link_Step_FraitureTailEven)
    (L_Step_FraitureTailOdd := link_Step_FraitureTailOdd)
    (L_Prop_FraitureTail := link_Prop_FraitureTail)
    (L_Thm_FraitureRepresentability := link_Thm_FraitureRepresentability)
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)

set_option maxRecDepth 20000 in
/-- **Lem_KovacMoment** — lem:kovac-moment. Paper lines 990-1116.

Supplied from proofs: 6 links, 2 leaves, 1 discharged inputs. Composed by
`Spine.spine_Lem_KovacMoment`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_KovacMoment : Lem_KovacMoment :=
  Spine.spine_Lem_KovacMoment
    (L_KovacMoment_identity := link_KovacMoment_identity)
    (L_KovacMoment_reduction := link_KovacMoment_reduction)
    (L_Eq_KSprime := link_Eq_KSprime)
    (L_Eq_KSsecond := link_Eq_KSsecond)
    (L_Eq_KS := link_Eq_KS)
    (L_Lem_KovacMoment := link_Lem_KovacMoment)
    (h_KovacMoment_reflection := leaf_KovacMoment_reflection)
    (h_KovacS_le_S1S2 := leaf_KovacS_le_S1S2)
    (i_Std_Mertens2 := input_Std_Mertens2)

set_option maxRecDepth 20000 in
/-- **Thm_SmallUpper** — thm:small-upper (Theorem 1.1). Paper lines 140-149; proof 1118-1148.

Supplied from proofs: 9 links, 6 leaves, 1 discharged inputs. Composed by
`Spine.spine_Thm_SmallUpper`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Thm_SmallUpper : Thm_SmallUpper :=
  Spine.spine_Thm_SmallUpper
    (L_KovacMoment_identity := link_KovacMoment_identity)
    (L_KovacMoment_reduction := link_KovacMoment_reduction)
    (L_Eq_KSprime := link_Eq_KSprime)
    (L_Eq_KSsecond := link_Eq_KSsecond)
    (L_Eq_KS := link_Eq_KS)
    (L_Lem_KovacMoment := link_Lem_KovacMoment)
    (L_SmallUpper_momentStep := link_SmallUpper_momentStep)
    (L_Thm_SmallUpper_doubleExp := link_Thm_SmallUpper_doubleExp)
    (L_Thm_SmallUpper_fixedPower := link_Thm_SmallUpper_fixedPower)
    (h_KovacMoment_reflection := leaf_KovacMoment_reflection)
    (h_KovacS_le_S1S2 := leaf_KovacS_le_S1S2)
    (h_SmallUpper_emptyCase := leaf_SmallUpper_emptyCase)
    (h_SmallUpper_markov := leaf_SmallUpper_markov)
    (h_SmallUpper_paramChoice := leaf_SmallUpper_paramChoice)
    (h_SmallUpper_doubleExpPower := leaf_SmallUpper_doubleExpPower)
    (i_Std_Mertens2 := input_Std_Mertens2)

set_option maxRecDepth 20000 in
/-- **Prop_SmallRatioThreshold** — unlabeled proposition (f(n) <= n/10 => n > 10^120). Paper lines
1156-1181.

Supplied from proofs: 1 links, 3 leaves, 0 discharged inputs. Composed by
`Spine.spine_Prop_SmallRatioThreshold`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Axler_Cor2`: Axler Corollary 2: `sigma(n)/n < (1 + 3.15367e-7) e^gamma log log n`
  for `5040 < n <= 10^119`. -/
theorem ep1054_Prop_SmallRatioThreshold
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2) :
    Prop_SmallRatioThreshold :=
  Spine.spine_Prop_SmallRatioThreshold
    (L_Prop_SmallRatioThreshold := link_Prop_SmallRatioThreshold)
    (h_SmallRatio_prefixLeSig := leaf_SmallRatio_prefixLeSig)
    (h_SmallRatio_abundancySmall := leaf_SmallRatio_abundancySmall)
    (h_SmallRatio_axlerNumeric := leaf_SmallRatio_axlerNumeric)
    (i_Cite_Axler_Cor2 := i_Cite_Axler_Cor2)

set_option maxRecDepth 20000 in
/-- **Lem_SvA0** — unlabeled lemma on A_0(X). Paper lines 1245-1302.

Supplied from proofs: 4 links, 4 leaves, 2 discharged inputs. Composed by
`Spine.spine_Lem_SvA0`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_SvA0 : Lem_SvA0 :=
  Spine.spine_Lem_SvA0
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
    (L_Eq_SvTwoSided := link_Eq_SvTwoSided)
    (L_SvA0_jSum := link_SvA0_jSum)
    (L_Lem_SvA0Count := link_Lem_SvA0Count)
    (h_Lem_SvA0Unique := leaf_Lem_SvA0Unique)
    (h_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)

set_option maxRecDepth 20000 in
/-- **Lem_SmoothPartInput** — lem:smooth-part-input; Std_Mertens1 is derived (line 1383), not
trusted. Paper lines 1348-1389.

Supplied from proofs: 2 links, 2 leaves, 1 discharged inputs. Composed by
`Spine.spine_Lem_SmoothPartInput`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_SmoothPartInput : Lem_SmoothPartInput :=
  Spine.spine_Lem_SmoothPartInput
    (L_Eq_SmoothPartPeriodCount := link_Eq_SmoothPartPeriodCount)
    (L_Lem_SmoothPartInput := link_Lem_SmoothPartInput)
    (h_Std_Mertens1 := leaf_Std_Mertens1)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (i_Std_Mertens3 := input_Std_Mertens3)

set_option maxRecDepth 20000 in
/-- **Lem_SvRegular** — lem:sv-regular. Paper lines 1394-1480.

Supplied from proofs: 5 links, 5 leaves, 2 discharged inputs. Composed by
`Spine.spine_Lem_SvRegular`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4: `s(s(n))/s(n) <= s(n)/n + 1` outside a
  density-zero set. -/
theorem ep1054_Lem_SvRegular
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14) :
    Lem_SvRegular :=
  Spine.spine_Lem_SvRegular
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
    (L_Eq_SvTwoSided := link_Eq_SvTwoSided)
    (L_SvA0_jSum := link_SvA0_jSum)
    (L_Lem_SvA0Count := link_Lem_SvA0Count)
    (L_Lem_SvRegular := link_Lem_SvRegular)
    (h_Lem_SvA0Unique := leaf_Lem_SvA0Unique)
    (h_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero := leaf_Eq_SvHarmonicDensityZero)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)

set_option maxRecDepth 20000 in
/-- **Lem_SvClasses** — lem:sv-classes; the regular family enters as the hypothesis
SV.RegularFamily, not as Lem_SvRegular. Paper lines 1486-1527.

Supplied from proofs: 3 links, 2 leaves, 1 discharged inputs. Composed by
`Spine.spine_Lem_SvClasses`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_SvClasses : Lem_SvClasses :=
  Spine.spine_Lem_SvClasses
    (L_Eq_SmoothPartPeriodCount := link_Eq_SmoothPartPeriodCount)
    (L_Lem_SmoothPartInput := link_Lem_SmoothPartInput)
    (L_Lem_SvClasses := link_Lem_SvClasses)
    (h_Std_Mertens1 := leaf_Std_Mertens1)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (i_Std_Mertens3 := input_Std_Mertens3)

set_option maxRecDepth 20000 in
/-- **Prop_SvSecondMoment** — prop:sv-second-moment; diagonal from the SV.ClassesAt hypothesis.
Paper lines 1531-1860.

Supplied from proofs: 20 links, 5 leaves, 5 discharged inputs. Composed by
`Spine.spine_Prop_SvSecondMoment`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_LP_sieve37`: the two-dimensional upper-bound sieve (Halberstam-Richert Thm 2.2, in
  the form of Luca-Pomerance (3.7)) for two linear forms prime simultaneously. -/
theorem ep1054_Prop_SvSecondMoment
    (i_Cite_LP_sieve37 : Cite_LP_sieve37) :
    Prop_SvSecondMoment :=
  Spine.spine_Prop_SvSecondMoment
    (L_Eq_SvTwoSided := link_Eq_SvTwoSided)
    (L_Eq_SmoothPartPeriodCount := link_Eq_SmoothPartPeriodCount)
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
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (h_Eq_SvCollision := leaf_Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree := leaf_Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount := leaf_Claim_SvResiduePairCount)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_BrunTitchmarsh := input_Std_BrunTitchmarsh)
    (i_Std_divisorBound := input_Std_divisorBound)
    (i_Std_totient_sigma := input_Std_totient_sigma)
    (i_Cite_LP_sieve37 := i_Cite_LP_sieve37)

set_option maxRecDepth 20000 in
/-- **Thm_SmallValues** — thm:small-values (Theorem 1.2); rescaling X, delta > 1 from delta = 1.
Paper lines 159-164; proof 1217-1222, 1862-1884.

Supplied from proofs: 31 links, 13 leaves, 6 discharged inputs. Composed by
`Spine.spine_Thm_SmallValues`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.
* `Cite_LP_sieve37`: the two-dimensional upper-bound sieve (Halberstam-Richert Thm 2.2, in
  the form of Luca-Pomerance (3.7)) for two linear forms prime simultaneously.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4: `s(s(n))/s(n) <= s(n)/n + 1` outside a
  density-zero set. -/
theorem ep1054_Thm_SmallValues
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14) :
    Thm_SmallValues :=
  Spine.spine_Thm_SmallValues
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
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
    (h_Std_Mertens1 := leaf_Std_Mertens1)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Eq_SvBasic := leaf_Eq_SvBasic)
    (h_Eq_SvD := leaf_Eq_SvD)
    (h_Lem_SvA0Unique := leaf_Lem_SvA0Unique)
    (h_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero := leaf_Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision := leaf_Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree := leaf_Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount := leaf_Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz := leaf_Claim_SvCauchySchwarz)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Std_BrunTitchmarsh := input_Std_BrunTitchmarsh)
    (i_Std_divisorBound := input_Std_divisorBound)
    (i_Std_totient_sigma := input_Std_totient_sigma)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := i_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)

set_option maxRecDepth 20000 in
/-- **Lem_KernelTails** — lem:kernel-tails. Paper lines 1898-1977.

Supplied from proofs: 3 links, 2 leaves, 1 discharged inputs. Composed by
`Spine.spine_Lem_KernelTails`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Lem_KernelTails : Lem_KernelTails :=
  Spine.spine_Lem_KernelTails
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
    (L_Eq_MovingKernelTail := link_Eq_MovingKernelTail)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (i_Std_Mertens2 := input_Std_Mertens2)

set_option maxRecDepth 20000 in
/-- **Prop_FmEnvelope** — prop:fm-envelope. Paper lines 2002-2023.

Supplied from proofs: 7 links, 2 leaves, 0 discharged inputs. Composed by
`Spine.spine_Prop_FmEnvelope`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Prop_FmEnvelope : Prop_FmEnvelope :=
  Spine.spine_Prop_FmEnvelope
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_UpperTails_Claim_KA_finite := link_UpperTails_Claim_KA_finite)
    (L_UpperTails_Claim_VA_periodic := link_UpperTails_Claim_VA_periodic)
    (L_UpperTails_Claim_VA_density := link_UpperTails_Claim_VA_density)
    (L_Prop_FmEnvelope := link_Prop_FmEnvelope)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)

set_option maxRecDepth 20000 in
/-- **Cor_FmEnvelopeTail** — cor:fm-envelope-tail. Paper lines 2025-2062.

Supplied from proofs: 9 links, 5 leaves, 2 discharged inputs. Composed by
`Spine.spine_Cor_FmEnvelopeTail`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Cor_FmEnvelopeTail : Cor_FmEnvelopeTail :=
  Spine.spine_Cor_FmEnvelopeTail
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
    (L_UpperTails_Claim_KA_finite := link_UpperTails_Claim_KA_finite)
    (L_UpperTails_Claim_VA_periodic := link_UpperTails_Claim_VA_periodic)
    (L_UpperTails_Claim_VA_density := link_UpperTails_Claim_VA_density)
    (L_UpperTails_Claim_DeltaPfix := link_UpperTails_Claim_DeltaPfix)
    (L_UpperTails_Claim_RoughNotVA := link_UpperTails_Claim_RoughNotVA)
    (L_Cor_FmEnvelopeTail := link_Cor_FmEnvelopeTail)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough := leaf_UpperTails_Claim_VA_rough)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)

set_option maxRecDepth 20000 in
/-- **Thm_AlmostLogTail** — thm:almost-log-tail (Theorem 1.3). Paper lines 176-188; proof
2066-2107. Its trusted inputs are exactly `Cite_MV_exceptional`, `Std_Mertens2`,
`Std_Mertens3`: no finite representability computation (paper lines 645-647, 2105-2106).
`gen.py` refuses any DAG edit that changes this set.

Supplied from proofs: 20 links, 10 leaves, 2 discharged inputs. Composed by
`Spine.spine_Thm_AlmostLogTail`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes. -/
theorem ep1054_Thm_AlmostLogTail
    (i_Cite_MV_exceptional : Cite_MV_exceptional) :
    Thm_AlmostLogTail :=
  Spine.spine_Thm_AlmostLogTail
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Lem_Moment := link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
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
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough := leaf_UpperTails_Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith :=
      leaf_UpperTails_Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree := leaf_UpperTails_Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio := leaf_UpperTails_Claim_LscaleRatio)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)

set_option maxRecDepth 20000 in
/-- **Thm_SubexpGrowth** — thm:subexp-growth (Theorem 1.4). Paper lines 196-216; proof 2111-2244.
Its trusted inputs are exactly `Cite_MV_exceptional`, `Cite_Pollack_Lemma24`,
`Std_SiegelWalfisz_dyadic`, `Std_sigma_odd_iff`, `Std_Mertens2`, `Std_Mertens3`: no finite
representability computation (paper lines 645-647, 2223-2224). `gen.py` refuses any DAG edit
that changes this set.

Supplied from proofs: 21 links, 9 leaves, 5 discharged inputs. Composed by
`Spine.spine_Thm_SubexpGrowth`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes. -/
theorem ep1054_Thm_SubexpGrowth
    (i_Cite_MV_exceptional : Cite_MV_exceptional) :
    Thm_SubexpGrowth :=
  Spine.spine_Thm_SubexpGrowth
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_SigmaRate_OddPrime := link_Lem_SigmaRate_OddPrime)
    (L_Lem_SigmaRate_B2 := link_Lem_SigmaRate_B2)
    (L_Lem_Moment := link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_MovingKernelTail := link_Eq_MovingKernelTail)
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
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (h_UpperTails_Claim_RoughNonsquarefree := leaf_UpperTails_Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_SubexpFltP := leaf_UpperTails_Claim_SubexpFltP)
    (h_UpperTails_Claim_SubexpCofactorOne := leaf_UpperTails_Claim_SubexpCofactorOne)
    (h_UpperTails_Claim_SubexpLogT := leaf_UpperTails_Claim_SubexpLogT)
    (i_Cite_Pollack_Lemma24 := input_Cite_Pollack_Lemma24)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_SiegelWalfisz_dyadic := input_Std_SiegelWalfisz_dyadic)
    (i_Std_sigma_odd_iff := input_Std_sigma_odd_iff)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)

set_option maxRecDepth 20000 in
/-- **Prop_ClassFirstMoment** — prop:class-first-moment. Paper lines 2292-2435.

Supplied from proofs: 11 links, 8 leaves, 2 discharged inputs. Composed by
`Spine.spine_Prop_ClassFirstMoment`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Prop_ClassFirstMoment : Prop_ClassFirstMoment :=
  Spine.spine_Prop_ClassFirstMoment
    (L_Lem_Moment := link_Lem_Moment)
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
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Eq_HGcd := leaf_Eq_HGcd)
    (h_Eq_UClass := leaf_Eq_UClass)
    (h_Coverage_Step_SeDensity := leaf_Coverage_Step_SeDensity)
    (h_Coverage_Step_HeRatio := leaf_Coverage_Step_HeRatio)
    (h_Coverage_Step_SeMultiplesDens := leaf_Coverage_Step_SeMultiplesDens)
    (h_Coverage_Disp_CoprimeSqTail := leaf_Coverage_Disp_CoprimeSqTail)
    (h_Coverage_Step_DistinctPairs := leaf_Coverage_Step_DistinctPairs)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)

set_option maxRecDepth 20000 in
/-- **Cor_FmPrimeCeiling** — corollary (label cor:fm-prime-ceiling commented out). Paper lines
2448-2470.

Supplied from proofs: 5 links, 3 leaves, 0 discharged inputs. Composed by
`Spine.spine_Cor_FmPrimeCeiling`.

**Remaining hypotheses: none.** This is an unconditional theorem of the library (footprint
gated in `Proofs/Gate.lean`). -/
theorem ep1054_Cor_FmPrimeCeiling : Cor_FmPrimeCeiling :=
  Spine.spine_Cor_FmPrimeCeiling
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Cor_FmPrimeCeiling_congr := link_Cor_FmPrimeCeiling_congr)
    (L_Cor_FmPrimeCeiling_count := link_Cor_FmPrimeCeiling_count)
    (L_Cor_FmPrimeCeiling_upperDens := link_Cor_FmPrimeCeiling_upperDens)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Disp_FinalDivisor := leaf_Disp_FinalDivisor)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)

set_option maxRecDepth 20000 in
/-- **Cor_FixedCofactorDefect** — unlabeled corollary. Paper lines 2488-2505.

Supplied from proofs: 20 links, 10 leaves, 2 discharged inputs. Composed by
`Spine.spine_Cor_FixedCofactorDefect`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes. -/
theorem ep1054_Cor_FixedCofactorDefect
    (i_Cite_MV_exceptional : Cite_MV_exceptional) :
    Cor_FixedCofactorDefect :=
  Spine.spine_Cor_FixedCofactorDefect
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Lem_Moment := link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
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
    (L_Cor_FixedCofactorDefect_pos := link_Cor_FixedCofactorDefect_pos)
    (L_Eq_FixedCofactorDefect := link_Eq_FixedCofactorDefect)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough := leaf_UpperTails_Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith :=
      leaf_UpperTails_Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree := leaf_UpperTails_Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio := leaf_UpperTails_Claim_LscaleRatio)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)

set_option maxRecDepth 20000 in
/-- **Prop_EtaALower** — unlabeled proposition (eta_A lower bound). Paper lines 2543-2558.

Supplied from proofs: 30 links, 12 leaves, 3 discharged inputs. Composed by
`Spine.spine_Prop_EtaALower`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes. -/
theorem ep1054_Prop_EtaALower
    (i_Cite_MV_exceptional : Cite_MV_exceptional) :
    Prop_EtaALower :=
  Spine.spine_Prop_EtaALower
    (L_Std_PNT := link_Std_PNT)
    (L_Fact_KmodFinite := link_Fact_KmodFinite)
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Lem_Moment := link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
    (L_Lem_AnalyticOddRepresentability_LittleO := link_Lem_AnalyticOddRepresentability_LittleO)
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
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
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Fact_DsetResidue := leaf_Fact_DsetResidue)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough := leaf_UpperTails_Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith :=
      leaf_UpperTails_Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree := leaf_UpperTails_Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio := leaf_UpperTails_Claim_LscaleRatio)
    (h_Coverage_Fact_UpperDensCompl := leaf_Coverage_Fact_UpperDensCompl)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)

set_option maxRecDepth 20000 in
/-- **Prop_ThetaTwo** — prop:theta-two. Paper lines 2569-2620.

Supplied from proofs: 5 links, 1 leaves, 1 discharged inputs. Composed by
`Spine.spine_Prop_ThetaTwo`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes.
* `Cite_ChenZhao`: Chen-Zhao: the nonaliquot numbers have lower density `>= 0.0602757`. -/
theorem ep1054_Prop_ThetaTwo
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_ChenZhao : Cite_ChenZhao) :
    Prop_ThetaTwo :=
  Spine.spine_Prop_ThetaTwo
    (L_Eq_F2OddNegligible := link_Eq_F2OddNegligible)
    (L_Eq_OddUntouchables := link_Eq_OddUntouchables)
    (L_Coverage_Step_EvenUntouchables := link_Coverage_Step_EvenUntouchables)
    (L_Coverage_Disp_F2Count := link_Coverage_Disp_F2Count)
    (L_Prop_ThetaTwo := link_Prop_ThetaTwo)
    (h_Eq_F2Aliquot := leaf_Eq_F2Aliquot)
    (i_Std_sigma_odd_iff := input_Std_sigma_odd_iff)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)
    (i_Cite_ChenZhao := i_Cite_ChenZhao)

set_option maxRecDepth 20000 in
/-- **Cor_EtaTwo** — unlabeled corollary (eta_2). Paper lines 2623-2645.

Supplied from proofs: 16 links, 8 leaves, 1 discharged inputs. Composed by
`Spine.spine_Cor_EtaTwo`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes.
* `Cite_ChenZhao`: Chen-Zhao: the nonaliquot numbers have lower density `>= 0.0602757`. -/
theorem ep1054_Cor_EtaTwo
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_ChenZhao : Cite_ChenZhao) :
    Cor_EtaTwo :=
  Spine.spine_Cor_EtaTwo
    (L_Fact_KmodFinite := link_Fact_KmodFinite)
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Coverage_Step_KmodSmallPrime := link_Coverage_Step_KmodSmallPrime)
    (L_Coverage_Step_GcovValuesSmallPrime := link_Coverage_Step_GcovValuesSmallPrime)
    (L_Coverage_Fact_GcovCoprimeNull := link_Coverage_Fact_GcovCoprimeNull)
    (L_Coverage_Fact_CoprimeComplementDens := link_Coverage_Fact_CoprimeComplementDens)
    (L_Eq_BoundedCofactorComplement := link_Eq_BoundedCofactorComplement)
    (L_Eq_F2OddNegligible := link_Eq_F2OddNegligible)
    (L_Eq_OddUntouchables := link_Eq_OddUntouchables)
    (L_Coverage_Step_EvenUntouchables := link_Coverage_Step_EvenUntouchables)
    (L_Coverage_Disp_F2Count := link_Coverage_Disp_F2Count)
    (L_Prop_ThetaTwo := link_Prop_ThetaTwo)
    (L_Coverage_Step_UpperDensG2 := link_Coverage_Step_UpperDensG2)
    (L_Cor_EtaTwo := link_Cor_EtaTwo)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Fact_DsetResidue := leaf_Fact_DsetResidue)
    (h_Eq_F2Aliquot := leaf_Eq_F2Aliquot)
    (h_Coverage_Step_G2Decomp := leaf_Coverage_Step_G2Decomp)
    (h_Coverage_Step_P2Values := leaf_Coverage_Step_P2Values)
    (h_Coverage_Fact_UpperDensCompl := leaf_Coverage_Fact_UpperDensCompl)
    (i_Std_sigma_odd_iff := input_Std_sigma_odd_iff)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)
    (i_Cite_ChenZhao := i_Cite_ChenZhao)

set_option maxRecDepth 20000 in
/-- **Prop_TightnessEquivalence** — prop:tightness-equivalence (bounded X: finitely many ratios).
Paper lines 2674-2717.

Supplied from proofs: 15 links, 9 leaves, 0 discharged inputs. Composed through
`Assembly.noRS_Prop_TightnessEquivalence` (the spine with `Cite_RosserSchoenfeld_psi` removed;
Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Prop_TightnessEquivalence
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Prop_TightnessEquivalence :=
  Assembly.noRS_Prop_TightnessEquivalence
    (L_Lem_Moment := link_Lem_Moment)
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
    (L_Coverage_Disp_TailLeCompl := link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail := link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence := link_Prop_TightnessEquivalence)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)
    (h_Coverage_Fact_UpperDensCompl := leaf_Coverage_Fact_UpperDensCompl)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Prop_DaddWitnessMeans** — prop:dadd:witness-means. Paper lines 2752-2829.

Supplied from proofs: 9 links, 2 leaves, 0 discharged inputs. Composed by
`Spine.spine_Prop_DaddWitnessMeans`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_PollackAP`: Pollack: Davenport's theorem in arithmetic progressions (continuous
  distribution function of `sigma(n)/n` in each residue class). -/
theorem ep1054_Prop_DaddWitnessMeans
    (i_Cite_PollackAP : Cite_PollackAP) :
    Prop_DaddWitnessMeans :=
  Spine.spine_Prop_DaddWitnessMeans
    (L_Lem_Moment := link_Lem_Moment)
    (L_Fact_DaddProgressionLaws := link_Fact_DaddProgressionLaws)
    (L_Step_DaddWitnessIdentity := link_Step_DaddWitnessIdentity)
    (L_Step_DaddWitnessJointLimit := link_Step_DaddWitnessJointLimit)
    (L_Step_DaddWitnessSupport := link_Step_DaddWitnessSupport)
    (L_Step_DaddWitnessCount := link_Step_DaddWitnessCount)
    (L_Step_DaddWitnessCofactorTail := link_Step_DaddWitnessCofactorTail)
    (L_Step_DaddWitnessPieceBounds := link_Step_DaddWitnessPieceBounds)
    (L_Prop_DaddWitnessMeans := link_Prop_DaddWitnessMeans)
    (h_Disp_FinalDivisor := leaf_Disp_FinalDivisor)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (i_Cite_PollackAP := i_Cite_PollackAP)

set_option maxRecDepth 20000 in
/-- **Thm_DaddUniversalSingularity** — thm:dadd:universal-singularity. Paper lines 2839-2938.

Supplied from proofs: 65 links, 26 leaves, 6 discharged inputs. Composed through
`Assembly.noRS_Thm_DaddUniversalSingularity` (the spine with `Cite_RosserSchoenfeld_psi`
removed; Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.
* `Cite_LP_sieve37`: the two-dimensional upper-bound sieve (Halberstam-Richert Thm 2.2, in
  the form of Luca-Pomerance (3.7)) for two linear forms prime simultaneously.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4: `s(s(n))/s(n) <= s(n)/n + 1` outside a
  density-zero set.
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Cite_PollackAP`: Pollack: Davenport's theorem in arithmetic progressions (continuous
  distribution function of `sigma(n)/n` in each residue class).
* `Cite_Erdos_singular`: Erdos: the Davenport law of `sigma(n)/n` is purely singular.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Thm_DaddUniversalSingularity
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Thm_DaddUniversalSingularity :=
  Assembly.noRS_Thm_DaddUniversalSingularity
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
    (L_Cite_Davenport := link_Cite_Davenport)
    (L_Lem_Moment := link_Lem_Moment)
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
    (L_Coverage_Disp_TailLeCompl := link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail := link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence := link_Prop_TightnessEquivalence)
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
    (L_Step_DaddSingularCarrier := link_Step_DaddSingularCarrier)
    (L_Step_DaddWitnessMeasureMass := link_Step_DaddWitnessMeasureMass)
    (L_Step_DaddWitnessCarrier := link_Step_DaddWitnessCarrier)
    (L_Step_DaddEmpiricalWitnessVague := link_Step_DaddEmpiricalWitnessVague)
    (L_Step_DaddLimitDomination := link_Step_DaddLimitDomination)
    (L_Thm_DaddUniversalSingularity_Carrier := link_Thm_DaddUniversalSingularity_Carrier)
    (L_Thm_DaddUniversalSingularity_FinitePart := link_Thm_DaddUniversalSingularity_FinitePart)
    (L_Thm_DaddUniversalSingularity_Tight := link_Thm_DaddUniversalSingularity_Tight)
    (h_Std_Mertens1 := leaf_Std_Mertens1)
    (h_EmpiricalMeasures_isProbability := leaf_EmpiricalMeasures_isProbability)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Disp_FinalDivisor := leaf_Disp_FinalDivisor)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)
    (h_Eq_SvBasic := leaf_Eq_SvBasic)
    (h_Eq_SvD := leaf_Eq_SvD)
    (h_Lem_SvA0Unique := leaf_Lem_SvA0Unique)
    (h_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero := leaf_Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision := leaf_Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree := leaf_Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount := leaf_Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz := leaf_Claim_SvCauchySchwarz)
    (h_Coverage_Fact_UpperDensCompl := leaf_Coverage_Fact_UpperDensCompl)
    (h_Step_DaddWitnessDomination := leaf_Step_DaddWitnessDomination)
    (h_Step_DaddCountDomination := leaf_Step_DaddCountDomination)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Std_BrunTitchmarsh := input_Std_BrunTitchmarsh)
    (i_Std_divisorBound := input_Std_divisorBound)
    (i_Std_totient_sigma := input_Std_totient_sigma)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := i_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Cite_PollackAP := i_Cite_PollackAP)
    (i_Cite_Erdos_singular := i_Cite_Erdos_singular)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Cor_DaddHeavyTails** — unlabeled corollary (heavy tails). Paper lines 2942-3026.

Supplied from proofs: 99 links, 39 leaves, 6 discharged inputs. Composed through
`Assembly.noRS_Cor_DaddHeavyTails` (the spine with `Cite_RosserSchoenfeld_psi` removed;
Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes.
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.
* `Cite_LP_sieve37`: the two-dimensional upper-bound sieve (Halberstam-Richert Thm 2.2, in
  the form of Luca-Pomerance (3.7)) for two linear forms prime simultaneously.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4: `s(s(n))/s(n) <= s(n)/n + 1` outside a
  density-zero set.
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Cite_PollackAP`: Pollack: Davenport's theorem in arithmetic progressions (continuous
  distribution function of `sigma(n)/n` in each residue class).
* `Cite_Erdos_singular`: Erdos: the Davenport law of `sigma(n)/n` is purely singular.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Cor_DaddHeavyTails
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
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Cor_DaddHeavyTails :=
  Assembly.noRS_Cor_DaddHeavyTails
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
    (L_Cite_Davenport := link_Cite_Davenport)
    (L_Lem_FmModulus := link_Lem_FmModulus)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Lem_Moment := link_Lem_Moment)
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
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
    (L_KovacMoment_identity := link_KovacMoment_identity)
    (L_KovacMoment_reduction := link_KovacMoment_reduction)
    (L_Eq_KSprime := link_Eq_KSprime)
    (L_Eq_KSsecond := link_Eq_KSsecond)
    (L_Eq_KS := link_Eq_KS)
    (L_Lem_KovacMoment := link_Lem_KovacMoment)
    (L_SmallUpper_momentStep := link_SmallUpper_momentStep)
    (L_Thm_SmallUpper_doubleExp := link_Thm_SmallUpper_doubleExp)
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
    (L_Eq_SharpPrimeSum := link_Eq_SharpPrimeSum)
    (L_Eq_FixedKernelTail := link_Eq_FixedKernelTail)
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
    (L_Coverage_Disp_TailLeCompl := link_Coverage_Disp_TailLeCompl)
    (L_Coverage_Disp_ComplLeTail := link_Coverage_Disp_ComplLeTail)
    (L_Prop_TightnessEquivalence := link_Prop_TightnessEquivalence)
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
    (h_Std_Mertens1 := leaf_Std_Mertens1)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_EmpiricalMeasures_isProbability := leaf_EmpiricalMeasures_isProbability)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Disp_FinalDivisor := leaf_Disp_FinalDivisor)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Fact_KmodGeTwo := leaf_Fact_KmodGeTwo)
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)
    (h_KovacMoment_reflection := leaf_KovacMoment_reflection)
    (h_KovacS_le_S1S2 := leaf_KovacS_le_S1S2)
    (h_SmallUpper_emptyCase := leaf_SmallUpper_emptyCase)
    (h_SmallUpper_markov := leaf_SmallUpper_markov)
    (h_SmallUpper_paramChoice := leaf_SmallUpper_paramChoice)
    (h_Eq_SvBasic := leaf_Eq_SvBasic)
    (h_Eq_SvD := leaf_Eq_SvD)
    (h_Lem_SvA0Unique := leaf_Lem_SvA0Unique)
    (h_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero := leaf_Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision := leaf_Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree := leaf_Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount := leaf_Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz := leaf_Claim_SvCauchySchwarz)
    (h_Eq_RankinKernel := leaf_Eq_RankinKernel)
    (h_UpperTails_Claim_EulerHigherTerms := leaf_UpperTails_Claim_EulerHigherTerms)
    (h_UpperTails_Claim_VA_rough := leaf_UpperTails_Claim_VA_rough)
    (h_UpperTails_Claim_AlmostLogTail_momentArith :=
      leaf_UpperTails_Claim_AlmostLogTail_momentArith)
    (h_UpperTails_Claim_RoughNonsquarefree := leaf_UpperTails_Claim_RoughNonsquarefree)
    (h_UpperTails_Claim_LscaleRatio := leaf_UpperTails_Claim_LscaleRatio)
    (h_Coverage_Fact_UpperDensCompl := leaf_Coverage_Fact_UpperDensCompl)
    (h_Step_DaddWitnessDomination := leaf_Step_DaddWitnessDomination)
    (h_Step_DaddCountDomination := leaf_Step_DaddCountDomination)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Std_BrunTitchmarsh := input_Std_BrunTitchmarsh)
    (i_Std_divisorBound := input_Std_divisorBound)
    (i_Std_totient_sigma := input_Std_totient_sigma)
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := i_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Cite_PollackAP := i_Cite_PollackAP)
    (i_Cite_Erdos_singular := i_Cite_Erdos_singular)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Prop_DaddCollisionCriterion** — prop:dadd:collision-criterion; compactness and portmanteau
need nu_X probability. Paper lines 3032-3072.

Supplied from proofs: 65 links, 27 leaves, 6 discharged inputs. Composed through
`Assembly.noRS_Prop_DaddCollisionCriterion` (the spine with `Cite_RosserSchoenfeld_psi`
removed; Mathlib's `theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.
* `Cite_LP_sieve37`: the two-dimensional upper-bound sieve (Halberstam-Richert Thm 2.2, in
  the form of Luca-Pomerance (3.7)) for two linear forms prime simultaneously.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4: `s(s(n))/s(n) <= s(n)/n + 1` outside a
  density-zero set.
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Cite_PollackAP`: Pollack: Davenport's theorem in arithmetic progressions (continuous
  distribution function of `sigma(n)/n` in each residue class).
* `Cite_Erdos_singular`: Erdos: the Davenport law of `sigma(n)/n` is purely singular.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_Prop_DaddCollisionCriterion
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Prop_DaddCollisionCriterion :=
  Assembly.noRS_Prop_DaddCollisionCriterion
    (L_Std_primes_dyadic_lower := link_Std_primes_dyadic_lower)
    (L_Cite_Davenport := link_Cite_Davenport)
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_Lem_SigmaRangeZero := link_Lem_SigmaRangeZero)
    (L_Lem_Moment := link_Lem_Moment)
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
    (L_Step_DaddSingularCarrier := link_Step_DaddSingularCarrier)
    (L_Step_DaddWitnessMeasureMass := link_Step_DaddWitnessMeasureMass)
    (L_Step_DaddWitnessCarrier := link_Step_DaddWitnessCarrier)
    (L_Step_DaddEmpiricalWitnessVague := link_Step_DaddEmpiricalWitnessVague)
    (L_Step_DaddLimitDomination := link_Step_DaddLimitDomination)
    (L_Thm_DaddUniversalSingularity_Carrier := link_Thm_DaddUniversalSingularity_Carrier)
    (L_Step_DaddCollisionSupport := link_Step_DaddCollisionSupport)
    (L_Eq_DaddCollisionCriterion := link_Eq_DaddCollisionCriterion)
    (L_Prop_DaddCollisionCriterion := link_Prop_DaddCollisionCriterion)
    (h_Std_Mertens1 := leaf_Std_Mertens1)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_EmpiricalMeasures_isProbability := leaf_EmpiricalMeasures_isProbability)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Disp_FinalDivisor := leaf_Disp_FinalDivisor)
    (h_Eq_Reflection := leaf_Eq_Reflection)
    (h_Lem_FraiturePrimeWindow := leaf_Lem_FraiturePrimeWindow)
    (h_Lem_FraitureExtension := leaf_Lem_FraitureExtension)
    (h_Step_FraitureSmallBq := leaf_Step_FraitureSmallBq)
    (h_Step_FraitureSeven := leaf_Step_FraitureSeven)
    (h_Step_FraitureTailThreePrimes := leaf_Step_FraitureTailThreePrimes)
    (h_Step_FraitureTailFourPrimes := leaf_Step_FraitureTailFourPrimes)
    (h_Step_FraitureSmallCases := leaf_Step_FraitureSmallCases)
    (h_Eq_SvBasic := leaf_Eq_SvBasic)
    (h_Eq_SvD := leaf_Eq_SvD)
    (h_Lem_SvA0Unique := leaf_Lem_SvA0Unique)
    (h_Lem_SvA0QLarge := leaf_Lem_SvA0QLarge)
    (h_SvA0_sigmaHarmonic := leaf_SvA0_sigmaHarmonic)
    (h_SvA0_abundancySubmul := leaf_SvA0_abundancySubmul)
    (h_Eq_SvHarmonicDensityZero := leaf_Eq_SvHarmonicDensityZero)
    (h_Eq_SvCollision := leaf_Eq_SvCollision)
    (h_Claim_SvSmallHSquarefree := leaf_Claim_SvSmallHSquarefree)
    (h_Claim_SvResiduePairCount := leaf_Claim_SvResiduePairCount)
    (h_Claim_SvCauchySchwarz := leaf_Claim_SvCauchySchwarz)
    (h_Coverage_Fact_RtPosIff := leaf_Coverage_Fact_RtPosIff)
    (h_Step_DaddWitnessDomination := leaf_Step_DaddWitnessDomination)
    (h_Step_DaddCountDomination := leaf_Step_DaddCountDomination)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Std_Mertens3 := input_Std_Mertens3)
    (i_Std_PNT_AP := InputsPNT.input_Std_PNT_AP)
    (i_Std_BrunTitchmarsh := input_Std_BrunTitchmarsh)
    (i_Std_divisorBound := input_Std_divisorBound)
    (i_Std_totient_sigma := input_Std_totient_sigma)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := i_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Cite_PollackAP := i_Cite_PollackAP)
    (i_Cite_Erdos_singular := i_Cite_Erdos_singular)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

set_option maxRecDepth 20000 in
/-- **Prop_DaddCollisionLowerBound** — unlabeled proposition (liminf K_X(t) > 1/9). Paper lines
3076-3174.

Supplied from proofs: 18 links, 10 leaves, 1 discharged inputs. Composed by
`Spine.spine_Prop_DaddCollisionLowerBound`.

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_PollackAP`: Pollack: Davenport's theorem in arithmetic progressions (continuous
  distribution function of `sigma(n)/n` in each residue class). -/
theorem ep1054_Prop_DaddCollisionLowerBound
    (i_Cite_PollackAP : Cite_PollackAP) :
    Prop_DaddCollisionLowerBound :=
  Spine.spine_Prop_DaddCollisionLowerBound
    (L_Lem_FixedModulusNormality := link_Lem_FixedModulusNormality)
    (L_KovacMoment_identity := link_KovacMoment_identity)
    (L_KovacMoment_reduction := link_KovacMoment_reduction)
    (L_Eq_KSprime := link_Eq_KSprime)
    (L_Eq_KSsecond := link_Eq_KSsecond)
    (L_Eq_KS := link_Eq_KS)
    (L_Lem_KovacMoment := link_Lem_KovacMoment)
    (L_Fact_DaddProgressionLaws := link_Fact_DaddProgressionLaws)
    (L_Step_DaddWitnessJointLimit := link_Step_DaddWitnessJointLimit)
    (L_Step_DaddCollisionWitness := link_Step_DaddCollisionWitness)
    (L_Step_DaddCollisionFirstMoment := link_Step_DaddCollisionFirstMoment)
    (L_Step_DaddCollisionFirstMomentLaw := link_Step_DaddCollisionFirstMomentLaw)
    (L_Step_DaddCollisionSourceIntensity := link_Step_DaddCollisionSourceIntensity)
    (L_Step_DaddCollisionCylinder := link_Step_DaddCollisionCylinder)
    (L_Step_DaddCollisionPerCore := link_Step_DaddCollisionPerCore)
    (L_Step_DaddCollisionCombine := link_Step_DaddCollisionCombine)
    (L_Step_DaddCollisionExplicit := link_Step_DaddCollisionExplicit)
    (L_Prop_DaddCollisionLowerBound := link_Prop_DaddCollisionLowerBound)
    (h_Std_recipPrimesAP_diverges := leaf_Std_recipPrimesAP_diverges)
    (h_Notation_Delta_density := leaf_Notation_Delta_density)
    (h_Notation_sigmaPrefix_zero := leaf_Notation_sigmaPrefix_zero)
    (h_KovacMoment_reflection := leaf_KovacMoment_reflection)
    (h_KovacS_le_S1S2 := leaf_KovacS_le_S1S2)
    (h_Eq_F2Aliquot := leaf_Eq_F2Aliquot)
    (h_Eq_DaddCollisionAffine := leaf_Eq_DaddCollisionAffine)
    (h_Step_DaddCollisionCores := leaf_Step_DaddCollisionCores)
    (h_Step_DaddCollisionH := leaf_Step_DaddCollisionH)
    (h_Step_DaddCollisionArithmetic := leaf_Step_DaddCollisionArithmetic)
    (i_Std_Mertens2 := input_Std_Mertens2)
    (i_Cite_PollackAP := i_Cite_PollackAP)

set_option maxRecDepth 20000 in
/-- **All of EP1054** (`Spine.DerivedClaims`): every derived statement of the paper, instantiating
`Spine.spine_EP1054` with every proved link, the proved leaves (as `LeafClaims`) and every
discharged input.

Supplied from proofs: 181 links, 68 leaves, 9 discharged inputs. Composed through
`Assembly.noRS_EP1054` (the spine with `Cite_RosserSchoenfeld_psi` removed; Mathlib's
`theta(x) <= x log 4` replaces it, see `Proofs.BalancedNoRS`).

**Remaining hypotheses** (trusted inputs with no Lean proof):
* `Cite_MV_exceptional`: Montgomery-Vaughan: at most `C X^{1-c}` even `n <= X` are not a sum
  of two primes.
* `Cite_LP_Lemma21`: Luca-Pomerance Lemma 2.1: outside a density-zero set, the four
  small-prime properties (i)-(iv) of `sigma(n)`, `gcd(n, sigma(n))` and `s(n)`.
* `Cite_LP_Lemma22_range`: Luca-Pomerance Lemma 2.2 (range form): the `n` with `P+(n) >
  n^{7/9}` and `pi^2 | s(n)` for a prime `pi` in the stated range have density zero.
* `Cite_LP_Lemma25`: Luca-Pomerance Lemma 2.5: outside a density-zero set, the reciprocal
  sum of the primes `r | sigma(n)` with `r > (log log n)^2` is at most 1.
* `Cite_LP_sieve37`: the two-dimensional upper-bound sieve (Halberstam-Richert Thm 2.2, in
  the form of Luca-Pomerance (3.7)) for two linear forms prime simultaneously.
* `Cite_Pollack_Thm14`: Pollack Theorem 1.4: `s(s(n))/s(n) <= s(n)/n + 1` outside a
  density-zero set.
* `Cite_Helfgott_weighted`: Helfgott's weighted ternary Goldbach bound (at least `0.000422
  H^2` for odd `H >= 10^27`, with the stated sup norms).
* `Cite_Dusart_Thm69`: Dusart Theorem 6.9: explicit two-sided bounds for `pi(x)`.
* `Cite_Axler_Cor2`: Axler Corollary 2: `sigma(n)/n < (1 + 3.15367e-7) e^gamma log log n`
  for `5040 < n <= 10^119`.
* `Cite_ChenZhao`: Chen-Zhao: the nonaliquot numbers have lower density `>= 0.0602757`.
* `Cite_PollackAP`: Pollack: Davenport's theorem in arithmetic progressions (continuous
  distribution function of `sigma(n)/n` in each residue class).
* `Cite_Erdos_singular`: Erdos: the Davenport law of `sigma(n)/n` is purely singular.
* `Comp_Verifier_small`: verifier check 1 (small sieve through `10^7`; a finite computation
  done by the external verifier).
* `Comp_Verifier_window1`: verifier check 2 (first window, up to `273803744799153`; a finite
  computation).
* `Comp_Verifier_largeSeed`: verifier check 3 (every integer in `[105000000, 156000000]` a
  sum of 4 or 5 distinct primes in `(M, 2M)`; a finite computation). -/
theorem ep1054_all
    (i_Cite_MV_exceptional : Cite_MV_exceptional)
    (i_Cite_LP_Lemma21 : Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range : Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 : Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 : Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 : Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Cite_PollackAP : Cite_PollackAP)
    (i_Cite_Erdos_singular : Cite_Erdos_singular)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Spine.DerivedClaims :=
  Assembly.noRS_EP1054
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
    (L_Lem_AnalyticOddRepresentability_Bound := link_Lem_AnalyticOddRepresentability_Bound)
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
    (L_Eq_OddUntouchables := link_Eq_OddUntouchables)
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
    (i_Cite_MV_exceptional := i_Cite_MV_exceptional)
    (i_Cite_LP_Lemma21 := i_Cite_LP_Lemma21)
    (i_Cite_LP_Lemma22_range := i_Cite_LP_Lemma22_range)
    (i_Cite_LP_Lemma25 := i_Cite_LP_Lemma25)
    (i_Cite_LP_sieve37 := i_Cite_LP_sieve37)
    (i_Cite_Pollack_Thm14 := i_Cite_Pollack_Thm14)
    (i_Cite_Helfgott_weighted := i_Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 := i_Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 := i_Cite_Axler_Cor2)
    (i_Cite_ChenZhao := i_Cite_ChenZhao)
    (i_Cite_PollackAP := i_Cite_PollackAP)
    (i_Cite_Erdos_singular := i_Cite_Erdos_singular)
    (i_Comp_Verifier_small := i_Comp_Verifier_small)
    (i_Comp_Verifier_window1 := i_Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed := i_Comp_Verifier_largeSeed)

/-- **Theorem 1.3 by the Goldbach route** (`Thm_AlmostLogTail`), from
`Alt.thm_AlmostLogTail_of_goldbachDensZero`.

**Remaining hypothesis:** `Alt.Std_GoldbachDensZero`: the even numbers that are not a sum of
two primes have asymptotic density zero. This is strictly weaker than `Cite_MV_exceptional`
(which gives a power saving), and the paper's proof of Theorem 1.3 uses only this much.
It is proved as `almost_all_binary_goldbach_proven` in the project's PNT+ workspace
(`GoldbachChainMaster.lean`, another Mathlib pin, so not importable here). The definitions of
`Alt` are verbatim copies of that file's, so the two halves are joined by a textual
transcription, not by a kernel check. -/
theorem ep1054_Thm_AlmostLogTail_viaGoldbach
    (hG : Principia.Erdos1054.Alt.Std_GoldbachDensZero) : Thm_AlmostLogTail :=
  Principia.Erdos1054.Alt.thm_AlmostLogTail_of_goldbachDensZero hG

/-- **`Cor_FixedCofactorDefect` by the Goldbach route**, from
`Alt.cor_FixedCofactorDefect_of_goldbachDensZero`.

**Remaining hypothesis:** `Alt.Std_GoldbachDensZero` (as for
`ep1054_Thm_AlmostLogTail_viaGoldbach`). -/
theorem ep1054_Cor_FixedCofactorDefect_viaGoldbach
    (hG : Principia.Erdos1054.Alt.Std_GoldbachDensZero) : Cor_FixedCofactorDefect :=
  Principia.Erdos1054.Alt.cor_FixedCofactorDefect_of_goldbachDensZero hG

end Principia.Erdos1054.Proofs
