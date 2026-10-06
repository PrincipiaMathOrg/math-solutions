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

LAYER 2 -- Helfgott's input itself, formalized down to 41 CITED inputs. Section 2 re-exports the
project's current headline `Principia.Erdos1054.Alt7.FromAtoms896I.ep1054_atoms896I`, which proves
`Principia.Erdos1054.Spine.DerivedClaims` (every derived claim of the paper, including the four
above) WITHOUT `Cite_Helfgott_weighted`, from the 41 hypotheses below. Every one of them is a
cited input -- a published machine computation or a published theorem, linked to its source and,
by owner decision, NOT re-proved in Lean. No step of Helfgott's argument is owed: every analytic
step between these inputs is kernel-checked. Each hypothesis's exact meaning is the docstring of
its definition, in the vendored `Principia/Common/TernaryGoldbach/` modules.

  CITED MACHINE COMPUTATIONS (18) -- linked to, not re-run in Lean:
    p    PC.PlattThm71          Platt, Thm 7.1 (arXiv:1305.3087): zeros of L(s, chi), chi primitive
                                of conductor 2 <= q <= 400000, lie on Re s = 1/2 up to his height
    z    PC.PlattTrudgian       Platt-Trudgian 2021: RH up to height 3*10^12
    chk  HC.EspagnCheckCited    Helfgott's finite check of `prop:espagn`
    sm   HC.EspagnSmallCited    the small checks inside `prop:espagn`'s reduction, bundled
    ch   HC.CharpyCited         Helfgott's `eq:charpy`, 120 <= R <= 4*10^7 (Platt's interval run)
    cp   HX.CharpasCited        Helfgott's `eq:charpas`, 200 <= R <= 1.6*10^8 (same method)
    gr   HC.AusteriaGridCited   Helfgott's grid check behind `cor:austeria`, x < 2000
    mc   HC.MalMainCited        VNODE-LP main-term integrals of Helfgott's major-arc Prop. 1.5
    am   HC.AmanitaBisectCited  `cor:amanita1`'s bisection: E(rho) >= 0.1065 rho on [1.19, 1.5]
    ab   HC.AppBCited           Helfgott's Appendix B: root isolation, C_2, C_3, |h'|_inf
    cg   HC.CameloGridCited     `lem:camelo`'s grid on [0, 655) (Platt's interval arithmetic)
    wo   HC.WollustCited        `lem:wollust`: |4e(-t/4) - 4e(-t/2) + e(-t)| <= 7.87052
    kc   HC.KastCited           `eq:kast`, 117 <= y < 2*758699, by direct computation
    hn   HC.NotungCited         `eq:notung`, e <= T <= 2135.94, by numerical work
    cs   HC.CortoSmallCited     `eq:corto` for S < 10^5 (v = 1: S >= 40; v = 2: S >= 16)
    ys   HC.YuttoSmallCited     `lem:yutto` for 33 <= x <= 10^6, by direct computation
    c0   HC.CortoC0Cited        the C_0 = 10000 sums in the proof of `eq:corto`
    hRc  HC.RamareCited         `eq:ramare`: |sum_{n<=x} mu(n)/n| <= sqrt(2/x) for x <= 10^12, etc.

  CITED PUBLISHED THEOREMS (23) -- cited, not formalized: the same treatment as the computations
  above (owner decision, 2026-10-02). Each is a hypothesis here, and its definition's docstring
  records the source and states it as printed in the source, in the form Helfgott quotes or
  derives it, or weaker (e.g. on a sub-range of the printed range), never stronger:
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
    r75  KLR.RS75Cor2           Rosser-Schoenfeld 1975, Corollary 2, (5.7), on x > 678407
    ls   T2K.LargeSieve         the sharp large sieve, Montgomery-Vaughan 1974, Corollary 1
                                (weaker: 0 < delta <= 1/2)
    mi   T2M.MontgomeryIneq     Montgomery's inequality (Montgomery 1968; Iwaniec-Kowalski L. 7.15)
    hMk  M2Y.RamareMarraki      Ramare 2013 (Acta Arith. 157), Corollary 1.4 (`eq:marraki`)
    mv   T2G.MVWeighted         Montgomery-Vaughan 1973, Theorem 1, (1.6), the weighted large
                                sieve (weaker: any delta_r below the minimal spacing)
    mv8  T2V.MV8Large           Montgomery-Vaughan 1973, Lemma 8, for R >= 100, with Helfgott's
                                constant 0.25068 (the paper prints 0.361; weaker)

Several links of the chain are CORRECTED forms of Helfgott's printed statements (the Main Theorem
constant 0.896 route; corrected `lem:bogus`, `lem:yutto`; 10.25 for `lem:monro`'s 1.27); each
corrected link is implied by, or weaker than, what the source proves, and each is a proved
theorem here, not a hypothesis. See `VERIFICATION.md`.

Section 2 states the 41 hypotheses once, as section variables in the order of
`ep1054_atoms896I`'s signature, and every theorem of the section takes all of them.

LAYER 3 -- Hyunsik Chae's route: a SECOND, independent conditional route to the same
representability result. Section 3 re-exports the modules under `Principia/Erdos1054/Chae/`.
`Chae/Pntpp/` is a port of Hyunsik Chae's own Lean development (`hs-chae/erdos1054_hyunsik`,
commit c065f37, Apache-2.0; see `Chae/Pntpp/LICENSE` and `Chae/Pntpp/CREDITS.md`): every statement
and proof there is his (the port changes only import paths and adds file-level `set_option`s). It
formalizes the divisor-prefix argument of Jimmy Fraiture's Erdos 1054 verifier
(`jif-perso/erdos_1054`). Its finite range is covered by his own kernel certificates and an explicit
prime-batch bridge; only the tail uses the balanced ternary Goldbach statement. His theorem
`Pntpp.DivisorPrefix.erdos1054_conditional` takes two hypotheses, `DusartBounds` and
`HelfgottTailHypothesis`. Principia's connecting modules (`Chae/Bridge.lean`, `Chae/Route.lean`)
prove nothing of his route; they supply his two hypotheses:
  * `HelfgottTailHypothesis` from the same 41 cited inputs as Section 2 (`chae_atoms896I`);
  * `DusartBounds` from TWO FURTHER cited published theorems, stated verbatim as named hypotheses:
      h35  Chae.Cite_RS62_Eq35  Rosser-Schoenfeld 1962, Corollary 1, (3.5): x / log x < pi(x), x >= 17
      h36  Chae.Cite_RS62_Eq36  Rosser-Schoenfeld 1962, Corollary 1, (3.6):
                                pi(x) < 1.25506 x / log x, x > 1
`chae_route_closed` is his proof closed on 41 + 2 = 43 cited inputs; it concludes his
`TargetClassification`, which is definitionally our `eq:exact-representability`
(`Chae.targetClassification_iff`). This route is CONDITIONAL exactly as Sections 1-2 are.
-/
import Principia.Erdos1054.Proofs.Assembly
import Principia.Erdos1054.Alt7.Round7
import Principia.Erdos1054.Alt7.FromAtoms896I
import Principia.Erdos1054.Chae.Route

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

/-! ## 2. Every derived claim of the paper from 41 cited inputs, without Helfgott's bound -/

section Atoms

open Principia.Common.TernaryGoldbach

-- cited machine computations (18)
variable (p : PC.PlattThm71) (z : PC.PlattTrudgian)
  (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
  (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
  (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
  (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
  (cs : HC.CortoSmallCited) (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
  (hRc : HC.RamareCited)
-- cited published theorems (23)
variable (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
  (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
  (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
  (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
  (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
  (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) (hMk : M2Y.RamareMarraki)
  (mv : T2G.MVWeighted) (mv8 : T2V.MV8Large)

include p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc
  hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8

/-- **Every derived claim of EP1054** (`Principia.Erdos1054.Spine.DerivedClaims`, a structure
with one field per derived claim of the paper) from the 41 cited inputs above. This is
`Principia.Erdos1054.Alt7.FromAtoms896I.ep1054_atoms896I`, restated so that its full signature
is visible here; the proof is that theorem applied to the same hypotheses. -/
theorem derivedClaims_of_atoms : Principia.Erdos1054.Spine.DerivedClaims :=
  Principia.Erdos1054.Alt7.FromAtoms896I.ep1054_atoms896I p z chk sm ch cp gr mc am ab cg wo kc
    hn cs ys c0 hRc hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi
    hMk mv mv8

/-- `lem:fraiture-balanced-goldbach` from the 41 cited inputs: a field of
`derivedClaims_of_atoms`. -/
theorem Lem_FraitureBalancedGoldbach_of_atoms :
    Principia.Erdos1054.Lem_FraitureBalancedGoldbach :=
  (derivedClaims_of_atoms p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc hZC rs cer hm hc
    h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv
    mv8).c_Lem_FraitureBalancedGoldbach

/-- `prop:fraiture-tail` from the 41 cited inputs: a field of `derivedClaims_of_atoms`. -/
theorem Prop_FraitureTail_of_atoms : Principia.Erdos1054.Prop_FraitureTail :=
  (derivedClaims_of_atoms p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc hZC rs cer hm hc
    h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8).c_Prop_FraitureTail

/-- `thm:fraiture-representability` from the 41 cited inputs: a field of
`derivedClaims_of_atoms`. -/
theorem Thm_FraitureRepresentability_of_atoms :
    Principia.Erdos1054.Thm_FraitureRepresentability :=
  (derivedClaims_of_atoms p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc hZC rs cer hm hc
    h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv
    mv8).c_Thm_FraitureRepresentability

/-- `eq:exact-representability` from the 41 cited inputs: a field of `derivedClaims_of_atoms`. -/
theorem Eq_ExactRepresentability_of_atoms : Principia.Erdos1054.Eq_ExactRepresentability :=
  (derivedClaims_of_atoms p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc hZC rs cer hm hc
    h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv
    mv8).c_Eq_ExactRepresentability

end Atoms

/-! ## 3. Hyunsik Chae's route

A second, independent conditional route to `R = N \ {2, 5}`. The Lean is **Hyunsik Chae's**
(`hs-chae/erdos1054_hyunsik`, ported under `Principia/Erdos1054/Chae/Pntpp/`, Apache-2.0); the
argument it formalizes is **Jimmy Fraiture's** Erdos 1054 verifier (`jif-perso/erdos_1054`). Its
inputs: the 41 cited inputs of Section 2 (used only for the Goldbach tail) and two further cited
published theorems, Rosser-Schoenfeld 1962, Corollary 1, (3.5) and (3.6) (used for his
`DusartBounds`). -/

/-- **Hyunsik Chae's theorem**, as he states it (his `Solution.lean`, ported verbatim): his
target classification (exactly `2` and `5` are not prefix sums of divisors) from his two explicit
assumptions `DusartBounds` and `HelfgottTailHypothesis`. -/
theorem erdos1054_conditional (dusart : Pntpp.DivisorPrefix.DusartBounds)
    (helfgott : Pntpp.DivisorPrefix.HelfgottTailHypothesis) :
    Pntpp.DivisorPrefix.TargetClassification :=
  Pntpp.DivisorPrefix.erdos1054_conditional dusart helfgott

section ChaeRoute

open Principia.Common.TernaryGoldbach

-- the same 41 cited inputs as Section 2, in the same order
variable (p : PC.PlattThm71) (z : PC.PlattTrudgian)
  (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
  (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
  (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
  (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
  (cs : HC.CortoSmallCited) (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
  (hRc : HC.RamareCited)
variable (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
  (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
  (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
  (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
  (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
  (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) (hMk : M2Y.RamareMarraki)
  (mv : T2G.MVWeighted) (mv8 : T2V.MV8Large)

include p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc
  hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8

/-- Hyunsik Chae's `HelfgottTailHypothesis` and his `TargetClassification` from the 41 cited
inputs of Section 2. This is `Principia.Erdos1054.Chae.chae_atoms896I`: both conjuncts come from
OUR chain (`ep1054_atoms896I`), transported along `Chae/Bridge.lean`'s identifications of his
statements with ours. It is what discharges his tail hypothesis in `chae_route_closed`. -/
theorem chae_atoms896I :
    Principia.Erdos1054.Chae.HelfgottTailHypothesis ∧
      Principia.Erdos1054.Chae.TargetClassification :=
  Principia.Erdos1054.Chae.chae_atoms896I p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc
    hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8

/-- **Hyunsik Chae's route, closed**: his `TargetClassification` BY HIS PROOF
(`erdos1054_conditional`), with `HelfgottTailHypothesis` supplied from the 41 cited inputs and
`DusartBounds` from Rosser-Schoenfeld 1962, Corollary 1, (3.5) (`h35`) and (3.6) (`h36`). This is
`Principia.Erdos1054.Chae.chae_route_closed`. -/
theorem chae_route_closed (h35 : Principia.Erdos1054.Chae.Cite_RS62_Eq35)
    (h36 : Principia.Erdos1054.Chae.Cite_RS62_Eq36) :
    Pntpp.DivisorPrefix.TargetClassification :=
  Principia.Erdos1054.Chae.chae_route_closed p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0
    hRc hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8
    h35 h36

/-- `eq:exact-representability` (equivalently `thm:fraiture-representability`, `R = N \ {2, 5}`)
by Hyunsik Chae's route: `chae_route_closed` transported along
`Principia.Erdos1054.Chae.targetClassification_iff`. Inputs: the 41 cited inputs and
Rosser-Schoenfeld 1962 (3.5), (3.6). -/
theorem Eq_ExactRepresentability_of_chae_route (h35 : Principia.Erdos1054.Chae.Cite_RS62_Eq35)
    (h36 : Principia.Erdos1054.Chae.Cite_RS62_Eq36) :
    Principia.Erdos1054.Eq_ExactRepresentability :=
  Principia.Erdos1054.Chae.targetClassification_iff.mp
    (Principia.Erdos1054.Chae.pntpp_target_iff.mp
      (chae_route_closed p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc hZC rs cer hm hc
        h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8 h35 h36))

end ChaeRoute

#print axioms Lem_FraitureBalancedGoldbach_of_helfgott
#print axioms Prop_FraitureTail_of_helfgott
#print axioms Thm_FraitureRepresentability_of_helfgott
#print axioms Eq_ExactRepresentability_of_helfgott
#print axioms derivedClaims_of_atoms
#print axioms Lem_FraitureBalancedGoldbach_of_atoms
#print axioms Prop_FraitureTail_of_atoms
#print axioms Thm_FraitureRepresentability_of_atoms
#print axioms Eq_ExactRepresentability_of_atoms
#print axioms Principia.Erdos1054.Alt7.FromAtoms896I.ep1054_atoms896I
#print axioms erdos1054_conditional
#print axioms chae_atoms896I
#print axioms chae_route_closed
#print axioms Eq_ExactRepresentability_of_chae_route
#print axioms Pntpp.DivisorPrefix.erdos1054_conditional
#print axioms Principia.Erdos1054.Chae.chae_atoms896I
#print axioms Principia.Erdos1054.Chae.chae_route_closed

end EP1054.Conditional
