/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajElem2
import Principia.Common.TernaryGoldbach.HelfMajPlusNorms
import Principia.Common.TernaryGoldbach.HelfMajMalNorms

set_option autoImplicit false

/-!
# `MR.HelfMajR η₊ (η₂ ∗_M φ)` from SIX named links

`helfMajR_of_6` is `helfMajR_of_10` (`HelfMajElem2.lean`) with four more links discharged — two
PROVED at their statements and two REPLACED by proved weaker variants whose consumers were
re-derived:

* `PlusReg` — PROVED, `HP.plusReg_holds` (`η₊ ∈ C¹(ℝ)`, Mellin strip `(0, 2)`;
  `HelfMajPlusReg`);
* `MalReg` — PROVED, `HP.malReg_holds` (`η₊² log(x·) ∈ C¹(ℝ)`; `HelfMajMalReg`);
* `PlusNorms` — REPLACED by the proved `HP.PlusNormsL`; Thm 1.4 re-derived
  (`HP.malporR_of_linksL`; `HelfMajPlusNorms`);
* `MalNorms` — REPLACED by the proved `HP.MalNormsL`; Prop 1.5 re-derived
  (`HP.malheurR_of_linksL`; `HelfMajMalNorms`).

`PlusNormsL` and `MalNormsL` keep the first three conjuncts at Helfgott's (F13-corrected) stated
constants and loosen only the derivative conjuncts, which enter `prop:unease`/`prop:konechno`
through `R/x` alone; the retyped targets still close (margins in those files' docstrings).

The six that remain: `ExplicitFormula` (DEEP, another round), `ZeroCount` (CITED, owner question),
`PlusDecay`, `PhiDecay` (the saddle point of majarcs §3, `cor:amanita1` `k = 1, 2`), `MalDecay`
(the Mellin decay of `η₊,₂`), `MalMain` (`|η₊ − η∘|₂ ≲ 2.4·10⁻⁶` plus the VNODE values).
Application only.
-/

namespace Principia.Common.TernaryGoldbach.HM

/-- **THE HEADLINE, SIX NAMED LINKS**: `helfMajR_of_10` with `PlusReg`, `MalReg` proved and
`PlusNorms`, `MalNorms` replaced by the proved `PlusNormsL`, `MalNormsL`. Application only. -/
theorem helfMajR_of_6 (hEF : ExplicitFormula) (hZC : ZeroCount)
    (pd : PlusDecay) (fd : PhiDecay) (md : MalDecay) (mm : MalMain) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  fun pf => ⟨HP.malporR_of_linksL hEF hZC hausierer_holds garmolaDecr_holds pd plusTailInt_holds pf,
    coprarR_of_linksL hEF hZC hausierer_holds garmolaDecr_holds phiReg_holds phiNormsL_holds fd
      phiTailInt_holds kolona_holds eta2Moments_holds pf,
    HP.malheurR_of_linksL hEF hZC hausierer_holds garmolaDecr_holds md malTailInt_holds mm pf⟩

end Principia.Common.TernaryGoldbach.HM
