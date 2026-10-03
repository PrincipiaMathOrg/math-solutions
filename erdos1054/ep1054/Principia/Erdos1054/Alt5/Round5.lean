/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt5.DensityOne
import Principia.Erdos1054.Alt5.ErdosSingular

set_option autoImplicit false

/-!
# EP1054 headlines after round 5

Round 5 landed two pieces, each a theorem of this library with footprint within
`[propext, Classical.choice, Quot.sound]`:

* `Principia.Erdos1054.Alt5.repDensityOne_unconditional : Alt.TailOnly.RepDensityOne`
  (`Alt5/DensityOne.lean`): `ℕ ∖ 𝓡` has density zero, with no hypothesis. It comes from the new
  library theorem `Principia.Common.BalancedGoldbach.balanced_goldbach` (almost every even `n` is
  `p + q` with primes `3 < p < q < 3p`) and the divisor-prefix identity `F(3p, q) = 4 + p + q`.
  Round 4 had it only from `Cite_Helfgott_weighted`.
* `Principia.Erdos1054.Alt5.input_Cite_Erdos_singular : Cite_Erdos_singular`
  (`Alt5/ErdosSingular.lean`, from `Principia.Common.Davenport.Singular`): the Davenport law of
  `σ(n)/n` is mutually singular with Lebesgue measure.

This module feeds both into the headlines that carried them. Every theorem here states a headline
`Prop` of `Principia.Erdos1054` (or, for the capstone, `Spine.DerivedClaims`) exactly as the spine
does; its hypotheses, listed in each docstring, are exactly the trusted inputs it still needs, and
**none** means an unconditional theorem.

**Newly unconditional:** `Prop_TightnessEquivalence` (#249), `Thm_DaddUniversalSingularity` (#270,
the paper's `thm:dadd:universal-singularity`), `Cor_DaddHeavyTails` (#280),
`Prop_DaddCollisionCriterion` (#283), and the spine field `Coverage.Rem_T_iff_Conj`.

**Remaining trusted inputs of the whole paper (7):** `Cite_Helfgott_weighted`, `Cite_Dusart_Thm69`,
`Cite_Axler_Cor2`, `Cite_ChenZhao`, `Comp_Verifier_small`, `Comp_Verifier_window1`,
`Comp_Verifier_largeSeed` (`ep1054_all_r5`). Every one of them is needed by some field of
`Spine.DerivedClaims` that asserts a statement about *every* integer in a range or an explicit
constant: none of those fields follows from a density statement.
-/

namespace Principia.Erdos1054.Alt5.Round5

open Principia.Erdos1054 Principia.Erdos1054.Spine

/-! ## 1. The §6 headline and the tightness remark -/

/-- **EP1054 `prop:tightness-equivalence` (#249), unconditionally**: density one of `𝓡`
(`Alt5.repDensityOne_unconditional`, balanced Goldbach) fed into
`TailOnly.prop_TightnessEquivalence_of_repDensityOne`.

**Remaining hypotheses: none.** (Round 4: `Cite_Helfgott_weighted`. Round 3: Helfgott,
`Cite_Dusart_Thm69` and the three `Comp_Verifier_*`.) -/
theorem ep1054_Prop_TightnessEquivalence_unconditional :
    Principia.Erdos1054.Prop_TightnessEquivalence :=
  Principia.Erdos1054.Alt5.ep1054_Prop_TightnessEquivalence_unconditional

/-- **`eq:T` ⟺ the weak bounded-cofactor conjecture (`Coverage.Rem_T_iff_Conj`),
unconditionally.** A field of `Spine.DerivedClaims`, not a headline row; neither side of the
equivalence is claimed.

**Remaining hypotheses: none.** (Round 4: `Cite_Helfgott_weighted`.) -/
theorem coverage_Rem_T_iff_Conj_unconditional : Principia.Erdos1054.Coverage.Rem_T_iff_Conj :=
  Principia.Erdos1054.Alt5.coverage_Rem_T_iff_Conj_unconditional

/-! ## 2. The §7 headlines

Round 4's `_of_repDensityOne` forms took `TailOnly.RepDensityOne` and `Cite_Erdos_singular`; round
5 proves both (`Alt5.ErdosSingular`'s `*_of_repDensityOne_r5` already carry the second, and
`Alt5.repDensityOne_unconditional` supplies the first). -/

/-- **EP1054 `thm:dadd:universal-singularity` (#270), unconditionally**:
`Alt5.thm_DaddUniversalSingularity_of_repDensityOne_r5` (which has `Cite_Erdos_singular`
discharged) at `Alt5.repDensityOne_unconditional`.

**Remaining hypotheses: none.** (Round 4: `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. Round 3:
ten.) -/
theorem ep1054_Thm_DaddUniversalSingularity_unconditional :
    Principia.Erdos1054.Thm_DaddUniversalSingularity :=
  Principia.Erdos1054.Alt5.thm_DaddUniversalSingularity_of_repDensityOne_r5
    Principia.Erdos1054.Alt5.repDensityOne_unconditional

/-- **EP1054 heavy-tail corollary (`Cor_DaddHeavyTails`, #280), unconditionally**:
`Alt5.cor_DaddHeavyTails_of_repDensityOne_r5` at `Alt5.repDensityOne_unconditional`.

**Remaining hypotheses: none.** (Round 4: `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. Round 3:
ten.) -/
theorem ep1054_Cor_DaddHeavyTails_unconditional : Principia.Erdos1054.Cor_DaddHeavyTails :=
  Principia.Erdos1054.Alt5.cor_DaddHeavyTails_of_repDensityOne_r5
    Principia.Erdos1054.Alt5.repDensityOne_unconditional

/-- **EP1054 `prop:dadd:collision-criterion` (#283), unconditionally**:
`Alt5.prop_DaddCollisionCriterion_of_repDensityOne_r5` at `Alt5.repDensityOne_unconditional`.

**Remaining hypotheses: none.** (Round 4: `Cite_Helfgott_weighted`, `Cite_Erdos_singular`. Round 3:
ten.) -/
theorem ep1054_Prop_DaddCollisionCriterion_unconditional :
    Principia.Erdos1054.Prop_DaddCollisionCriterion :=
  Principia.Erdos1054.Alt5.prop_DaddCollisionCriterion_of_repDensityOne_r5
    Principia.Erdos1054.Alt5.repDensityOne_unconditional

/-! ## 3. The whole paper -/

/-- **All of EP1054** (`Spine.DerivedClaims`, every derived statement of the paper) from **7**
trusted inputs: `Alt.Round4.ep1054_all_r4` with `Cite_Erdos_singular` supplied by
`Alt5.input_Cite_Erdos_singular`.

**Remaining hypotheses (7)** (trusted inputs with no Lean proof), with the fields that need them:
* `Cite_Helfgott_weighted` (Helfgott's weighted ternary Goldbach bound for every odd
  `H ≥ 10^27`): `Lem_FraitureBalancedGoldbach` (#118), `Prop_FraitureTail` (#121), and through
  them the exact classification `Thm_FraitureRepresentability` (#122), `Eq_ExactRepresentability`
  (#123) and its restatements `Intro_RcntFormula` (#124), `Thm_FraitureRepresentability_Ge6`
  (#125). These assert something of *every* large integer, so the density-one theorem
  `Alt5.repDensityOne_unconditional` cannot replace it.
* `Cite_Dusart_Thm69`, `Comp_Verifier_small`, `Comp_Verifier_window1`, `Comp_Verifier_largeSeed`
  (Dusart's explicit `π(x)` bounds and the three finite verifier computations):
  `Prop_FraitureFinite` (#117), hence #122–#125.
* `Cite_Axler_Cor2` (explicit Robin-type bound for `5040 < m ≤ 10^119`):
  `Prop_SmallRatioThreshold` (#139).
* `Cite_ChenZhao` (nonaliquot numbers have lower density `≥ 0.0602757`): `Prop_ThetaTwo` (#241),
  `Cor_EtaTwo` (#243).

The §6–§7 fields are proved here through the classification, as the spine does; sections 1–2 give
each of them without any input. (Round 4's `ep1054_all_r4` took these seven and
`Cite_Erdos_singular`; round 3 took 12, round 2 took 15.) -/
theorem ep1054_all_r5
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Spine.DerivedClaims :=
  Principia.Erdos1054.Alt.Round4.ep1054_all_r4 i_Cite_Helfgott_weighted i_Cite_Dusart_Thm69
    i_Cite_Axler_Cor2 i_Cite_ChenZhao Principia.Erdos1054.Alt5.input_Cite_Erdos_singular
    i_Comp_Verifier_small i_Comp_Verifier_window1 i_Comp_Verifier_largeSeed

end Principia.Erdos1054.Alt5.Round5
