/-
CONDITIONAL RESULTS -- the four EP1054 results that are NOT proved unconditionally.

    lem:fraiture-balanced-goldbach   `Principia.Erdos1054.Lem_FraitureBalancedGoldbach`
    prop:fraiture-tail               `Principia.Erdos1054.Prop_FraitureTail`
    thm:fraiture-representability    `Principia.Erdos1054.Thm_FraitureRepresentability`
    eq:exact-representability        `Principia.Erdos1054.Eq_ExactRepresentability`

(`thm:fraiture-representability` is the statement `R = N \ {2, 5}`; `eq:exact-representability`
is the same `Prop`.) The paper derives all four from Helfgott's weighted ternary Goldbach bound for
odd `H >= 10^27`. Nothing in this file is a Comparator target, and nothing here should be read as
an unconditional proof. Every hypothesis is an explicit binder; there is no `axiom` and no `sorry`.

LAYER 1 -- one published input. Section 1 proves each of the four from the single hypothesis
`Principia.Erdos1054.Cite_Helfgott_weighted` (`Principia/Erdos1054/Statements/Inputs.lean`):
Helfgott, arXiv:1312.7748, Section 7.4, (7.49)-(7.50) with the sup norms (7.3), (7.19), encoded
with existential weights (weaker than Helfgott's fixed weights; see that definition's docstring).

LAYER 2 -- Helfgott's input itself, formalized down to 35 named hypotheses. Section 2 re-exports
the project's current headline `Principia.Erdos1054.Alt7.FromAtomsZD.ep1054_atomsZD`, which proves
`Principia.Erdos1054.Spine.DerivedClaims` (every derived claim of the paper, including the four
above) WITHOUT `Cite_Helfgott_weighted`, from these 35 hypotheses. Each one's meaning is the
docstring of its definition, in the vendored `Principia/Common/TernaryGoldbach/` modules.

  CITED MACHINE COMPUTATIONS (7) -- linked to, not re-run in Lean:
    p    PC.PlattThm71          Platt, Thm 7.1 (arXiv:1305.3087): zeros of L(s, chi), chi primitive
                                of conductor 2 <= q <= 400000, lie on Re s = 1/2 up to his height
    z    PC.PlattTrudgian       Platt-Trudgian 2021: RH up to height 3*10^12
    chk  HC.EspagnCheckCited    Helfgott's finite check of `prop:espagn`
    sm   HC.EspagnSmallCited    the small checks inside `prop:espagn`'s reduction, bundled
    ch   HC.CharpyCited         Helfgott's `eq:charpy`, 120 <= R <= 4*10^7 (Platt's interval run)
    cp   HX.CharpasCited        Helfgott's `eq:charpas`, 200 <= R <= 1.6*10^8 (same method)
    gr   HC.AusteriaGridCited   Helfgott's grid check behind `cor:austeria`, x < 2000

  CITED PUBLISHED THEOREMS (17) -- cited, not formalized: the same treatment as Platt's
  computations above (project decision, 2026-10-02). Each is a hypothesis here, and its
  definition's docstring records the source and states it as printed in the source, in the
  form Helfgott quotes or derives it, or weaker (e.g. on a sub-range of the printed range),
  never stronger:
    hZC  HM.ZeroCount           explicit zero count N(T, chi) as Helfgott cites it (Rosser 1941,
                                McCurley 1984, Trudgian 2015)
    rs   HX.RS75Theta           Rosser-Schoenfeld 1975, (5.1): theta(n) <= 1.001102 n
    cer  CY.CERange             c_E in [1.3325822, 1.3325823] (Rosser-Schoenfeld 1962, (2.11))
    hm   CY.Malito              Ramare 1995, Lemma 3.4 (`eq:malito`)
    hc   CY.Cante               Ramare 1995, Lemma 3.4 (`eq:cante`): G(R) <= log R + 1.4709
    h15  GS.RS62Thm15           Rosser-Schoenfeld 1962, Theorem 15
    h12  EB.RS62Thm12           Rosser-Schoenfeld 1962, Theorem 12: psi(x) < 1.03883 x
    h13  EB.RS62Thm13           Rosser-Schoenfeld 1962, Theorem 13: psi(x) - theta(x) < 1.42620 sqrt x
    h316 LQ.RS62_316            Rosser-Schoenfeld 1962, (3.16)   } each on a sub-range of the
    h324 LQ.RS62_324            Rosser-Schoenfeld 1962, (3.24)   } printed one, i.e. a weaker
    h330 LQ.RS62_330            Rosser-Schoenfeld 1962, (3.30)   } hypothesis than the
    h332 LQ.RS62_332            Rosser-Schoenfeld 1962, (3.32)   } published statement
    hR   EF.RosserL17           Rosser 1941, Lemma 17
    hRS  EF.RamareSaouterL2     Ramare-Saouter 2003, Lemma 2 (the one instance used)
    hgr  MPc.Grara              Granville-Ramare 1996, Lemma 10.2
    hro  MPc.Ronsard            Ramare 2015 (`eq:ronsard`)
    hme  MPc.Meproz             Ramare 2015 (`eq:meproz`)

  OWED ARGUMENT (11) -- steps of Helfgott's proof not yet proved in Lean:
    hRe  EF.Rectangle           the residue theorem on the rectangle (explicit formula, `lem:agamon`)
    pd   HM.PlusDecay           decay of G_delta on the critical strip, eta_+ weight (saddle point)
    fd   HM.PhiDecay            the same for the second weight
    mm   HM.MalMain             the main term of Helfgott's major-arc Prop. 1.5
    res  EE.EspagnEdgeRes       the residue of `prop:espagn`: the moduli where both analytic
                                covers fail (a computation not yet run)
    hb1  MPG.Bostb1Eta2         `lem:bostb1` for eta_2 (Type I)
    hb2  MPc.Bosta2Eta2         `lem:bosta2` for eta_2 (Type I)
    hv1  MPc.Vinland1At         `eq:vinland1` (Type II)
    her  MPc.EriksagaAt         `eq:eriksaga` (Type II)
    hs2  MPc.SecI2At            |S_{I,2}| at the second parameter choice
    hs3  MPc.SecIIAt            |S_{II}| at the second parameter choice

Several owed links are stated at constants that differ from the ones printed in Helfgott's
papers; each difference is recorded in the docstring of that link's definition.

Section 2 states the 35 hypotheses once, as section variables in the order above, and every
theorem of the section takes all of them.
-/
import Principia.Erdos1054.Proofs.Assembly
import Principia.Erdos1054.Alt7.Round7
import Principia.Erdos1054.Alt7.FromAtomsZD

set_option autoImplicit false

namespace EP1054.Conditional

/-! ## 1. The four results from `Cite_Helfgott_weighted` alone -/

/-- `lem:fraiture-balanced-goldbach`, from Helfgott's weighted ternary Goldbach bound. -/
theorem Lem_FraitureBalancedGoldbach_of_helfgott
    (h : Principia.Erdos1054.Cite_Helfgott_weighted) :
    Principia.Erdos1054.Lem_FraitureBalancedGoldbach :=
  Principia.Erdos1054.Proofs.ep1054_Lem_FraitureBalancedGoldbach h

/-- `prop:fraiture-tail`, from Helfgott's weighted ternary Goldbach bound. -/
theorem Prop_FraitureTail_of_helfgott
    (h : Principia.Erdos1054.Cite_Helfgott_weighted) :
    Principia.Erdos1054.Prop_FraitureTail :=
  Principia.Erdos1054.Proofs.ep1054_Prop_FraitureTail h

/-- `thm:fraiture-representability` (`R = N \ {2, 5}`), from Helfgott's weighted ternary Goldbach
bound. The finite part (`prop:fraiture-finite`) is unconditional and enters as a proved theorem. -/
theorem Thm_FraitureRepresentability_of_helfgott
    (h : Principia.Erdos1054.Cite_Helfgott_weighted) :
    Principia.Erdos1054.Thm_FraitureRepresentability :=
  Principia.Erdos1054.Alt7.Round7.ep1054_Thm_FraitureRepresentability_r7 h

/-- `eq:exact-representability`, from Helfgott's weighted ternary Goldbach bound. -/
theorem Eq_ExactRepresentability_of_helfgott
    (h : Principia.Erdos1054.Cite_Helfgott_weighted) :
    Principia.Erdos1054.Eq_ExactRepresentability :=
  Principia.Erdos1054.Alt7.Round7.ep1054_Eq_ExactRepresentability_r7 h

/-! ## 2. Every derived claim of the paper from 35 named hypotheses, without Helfgott's bound -/

section Atoms

open Principia.Common.TernaryGoldbach

-- cited machine computations (7)
variable (p : PC.PlattThm71) (z : PC.PlattTrudgian)
  (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
  (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited)
-- cited published theorems (17)
variable (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
  (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
  (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
  (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
  (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz)
-- owed argument (11)
variable (hRe : EF.Rectangle) (pd : HM.PlusDecay) (fd : HM.PhiDecay) (mm : HM.MalMain)
  (res : EE.EspagnEdgeRes)
  (hb1 : MPG.Bostb1Eta2) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At)
  (her : MPc.EriksagaAt) (hs2 : MPc.SecI2At) (hs3 : MPc.SecIIAt)

include p z chk sm ch cp gr hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme
  hRe pd fd mm res hb1 hb2 hv1 her hs2 hs3

/-- **Every derived claim of EP1054** (`Principia.Erdos1054.Spine.DerivedClaims`, a structure
with one field per derived claim of the paper) from the 35 hypotheses above. This is
`Principia.Erdos1054.Alt7.FromAtomsZD.ep1054_atomsZD`, restated so that its full signature is
visible here; the proof is that theorem applied to the same hypotheses. -/
theorem derivedClaims_of_atoms : Principia.Erdos1054.Spine.DerivedClaims :=
  Principia.Erdos1054.Alt7.FromAtomsZD.ep1054_atomsZD p z hRe pd fd mm chk sm ch cp gr res
    hb1 hb2 hv1 her hs2 hs3 hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme

/-- `lem:fraiture-balanced-goldbach` from the 35 hypotheses: a field of `derivedClaims_of_atoms`. -/
theorem Lem_FraitureBalancedGoldbach_of_atoms :
    Principia.Erdos1054.Lem_FraitureBalancedGoldbach :=
  (derivedClaims_of_atoms p z chk sm ch cp gr hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332
    hR hRS hgr hro hme hRe pd fd mm res hb1 hb2 hv1 her hs2 hs3).c_Lem_FraitureBalancedGoldbach

/-- `prop:fraiture-tail` from the 35 hypotheses: a field of `derivedClaims_of_atoms`. -/
theorem Prop_FraitureTail_of_atoms : Principia.Erdos1054.Prop_FraitureTail :=
  (derivedClaims_of_atoms p z chk sm ch cp gr hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332
    hR hRS hgr hro hme hRe pd fd mm res hb1 hb2 hv1 her hs2 hs3).c_Prop_FraitureTail

/-- `thm:fraiture-representability` from the 35 hypotheses: a field of `derivedClaims_of_atoms`. -/
theorem Thm_FraitureRepresentability_of_atoms :
    Principia.Erdos1054.Thm_FraitureRepresentability :=
  (derivedClaims_of_atoms p z chk sm ch cp gr hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332
    hR hRS hgr hro hme hRe pd fd mm res hb1 hb2 hv1 her hs2 hs3).c_Thm_FraitureRepresentability

/-- `eq:exact-representability` from the 35 hypotheses: a field of `derivedClaims_of_atoms`. -/
theorem Eq_ExactRepresentability_of_atoms : Principia.Erdos1054.Eq_ExactRepresentability :=
  (derivedClaims_of_atoms p z chk sm ch cp gr hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332
    hR hRS hgr hro hme hRe pd fd mm res hb1 hb2 hv1 her hs2 hs3).c_Eq_ExactRepresentability

end Atoms

#print axioms Lem_FraitureBalancedGoldbach_of_helfgott
#print axioms Prop_FraitureTail_of_helfgott
#print axioms Thm_FraitureRepresentability_of_helfgott
#print axioms Eq_ExactRepresentability_of_helfgott
#print axioms derivedClaims_of_atoms
#print axioms Lem_FraitureBalancedGoldbach_of_atoms
#print axioms Prop_FraitureTail_of_atoms
#print axioms Thm_FraitureRepresentability_of_atoms
#print axioms Eq_ExactRepresentability_of_atoms

end EP1054.Conditional
