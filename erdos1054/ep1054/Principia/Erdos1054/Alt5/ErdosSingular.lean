/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt.Round4
import Principia.Common.Davenport.Singular.Cover

set_option autoImplicit false

/-!
# `Cite_Erdos_singular` discharged: the Davenport law of `σ(n)/n` is purely singular

`input_Cite_Erdos_singular : Cite_Erdos_singular` — every probability measure on `ℝ` whose
distribution function is the Davenport density of `{n : σ(n)/n ≤ u}` is mutually singular with
Lebesgue measure. The proof is `Principia.Common.Davenport.Singular`:

* `exists_cover`: for every `ε > 0` a finite union of half-open intervals of total length `≤ ε`
  contains `σ(n)/n` for at least `(1 − ε) X` of the `n ≤ X`, for all large `X` (a multi-scale gap
  argument; CRT independence of the scales replaces the Jessen–Wintner purity law that Erdős's
  1939 argument uses);
* `mutuallySingular_of_cover`: such coverings force `μ ⟂ₘ volume` for the limit law `μ`
  (inclusion–exclusion on finite unions of intervals, then Borel–Cantelli).

Plan and source discussion: `Campaigns/Erdos-1054/ERDOS-SINGULAR-PLAN.md`.

With it the three §7 headlines that carried `Cite_Erdos_singular` lose it, and the whole paper
(`Spine.DerivedClaims`) rests on **7** trusted inputs (`ep1054_all_without_erdosSingular`).

**Names.** The `_of_helfgott_r5` forms are named so as not to clash with the
`ep1054_*_r5` theorems of the sibling module `Alt5/DensityOne.lean` (same namespace), which take
`Cite_Erdos_singular` and prove density one of `𝓡` unconditionally. Composed with that module's
`repDensityOne_unconditional`, the `_of_repDensityOne_r5` forms here are unconditional.
-/

namespace Principia.Erdos1054.Alt5

open Principia.Erdos1054 Principia.Common.Davenport Principia.Common.Davenport.Singular
open Filter

/-- The paper's count of `{n : σ(n)/n ≤ u}` is the library's `countIn abund (Iic u)`. -/
theorem cnt_abundancy_le_eq_countIn (u : ℝ) (X : ℕ) :
    cnt {n : ℕ | abundancy n ≤ u} X = countIn abund (Set.Iic u) X := by
  unfold cnt countIn
  rw [Nat.floor_natCast]
  congr 1

/-- **`Cite_Erdos_singular`, proved.** The Davenport law of `σ(n)/n` is mutually singular with
Lebesgue measure. -/
theorem input_Cite_Erdos_singular : Cite_Erdos_singular := by
  intro μ _ hdens
  refine mutuallySingular_of_cover abund μ ?_ ?_
  · intro u
    unfold HasLimitOn
    refine (hdens u).congr fun X => ?_
    rw [cnt_abundancy_le_eq_countIn]
  · intro ε hε _
    exact exists_cover hε

/-! ## The §7 headlines without `Cite_Erdos_singular` -/

/-- **`thm:dadd:universal-singularity` from density one of `𝓡` alone.**

**Hypothesis:** `TailOnly.RepDensityOne` (not a trusted input; implied by
`Cite_Helfgott_weighted`). (Round 4: also `Cite_Erdos_singular`.) -/
theorem thm_DaddUniversalSingularity_of_repDensityOne_r5 (hD : Alt.TailOnly.RepDensityOne) :
    Thm_DaddUniversalSingularity :=
  Alt.Round4.thm_DaddUniversalSingularity_of_repDensityOne_r4 hD input_Cite_Erdos_singular

/-- **EP1054 `thm:dadd:universal-singularity`.**

**Remaining hypothesis:** `Cite_Helfgott_weighted`. (Round 4: Helfgott, `Cite_Erdos_singular`.) -/
theorem thm_DaddUniversalSingularity_of_helfgott_r5
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Thm_DaddUniversalSingularity :=
  Alt.Round4.ep1054_Thm_DaddUniversalSingularity_r4 i_Cite_Helfgott_weighted
    input_Cite_Erdos_singular

/-- **The heavy-tail corollary from density one of `𝓡` alone.**

**Hypothesis:** `TailOnly.RepDensityOne`. (Round 4: also `Cite_Erdos_singular`.) -/
theorem cor_DaddHeavyTails_of_repDensityOne_r5 (hD : Alt.TailOnly.RepDensityOne) :
    Cor_DaddHeavyTails :=
  Alt.Round4.cor_DaddHeavyTails_of_repDensityOne_r4 hD input_Cite_Erdos_singular

/-- **EP1054 heavy-tail corollary (`Cor_DaddHeavyTails`).**

**Remaining hypothesis:** `Cite_Helfgott_weighted`. (Round 4: Helfgott, `Cite_Erdos_singular`.) -/
theorem cor_DaddHeavyTails_of_helfgott_r5 (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Cor_DaddHeavyTails :=
  Alt.Round4.ep1054_Cor_DaddHeavyTails_r4 i_Cite_Helfgott_weighted input_Cite_Erdos_singular

/-- **`prop:dadd:collision-criterion` from density one of `𝓡` alone.**

**Hypothesis:** `TailOnly.RepDensityOne`. (Round 4: also `Cite_Erdos_singular`.) -/
theorem prop_DaddCollisionCriterion_of_repDensityOne_r5 (hD : Alt.TailOnly.RepDensityOne) :
    Prop_DaddCollisionCriterion :=
  Alt.Round4.prop_DaddCollisionCriterion_of_repDensityOne_r4 hD input_Cite_Erdos_singular

/-- **EP1054 `prop:dadd:collision-criterion`.**

**Remaining hypothesis:** `Cite_Helfgott_weighted`. (Round 4: Helfgott, `Cite_Erdos_singular`.) -/
theorem prop_DaddCollisionCriterion_of_helfgott_r5
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted) :
    Prop_DaddCollisionCriterion :=
  Alt.Round4.ep1054_Prop_DaddCollisionCriterion_r4 i_Cite_Helfgott_weighted
    input_Cite_Erdos_singular

/-- **All of EP1054** (`Spine.DerivedClaims`) from **7** trusted inputs: round 4's eight
(`Alt.Round4.ep1054_all_r4`) minus `Cite_Erdos_singular`.

**Remaining hypotheses (7):** `Cite_Helfgott_weighted`, `Cite_Dusart_Thm69`, `Cite_Axler_Cor2`,
`Cite_ChenZhao`, `Comp_Verifier_small`, `Comp_Verifier_window1`, `Comp_Verifier_largeSeed`. -/
theorem ep1054_all_without_erdosSingular
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2)
    (i_Cite_ChenZhao : Cite_ChenZhao)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Spine.DerivedClaims :=
  Alt.Round4.ep1054_all_r4 i_Cite_Helfgott_weighted i_Cite_Dusart_Thm69 i_Cite_Axler_Cor2
    i_Cite_ChenZhao input_Cite_Erdos_singular i_Comp_Verifier_small i_Comp_Verifier_window1
    i_Comp_Verifier_largeSeed

end Principia.Erdos1054.Alt5
