/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajElem
import Principia.Common.TernaryGoldbach.HelfMajAbel
import Principia.Common.TernaryGoldbach.RealSym

set_option autoImplicit false

/-!
# `MR.HelfMajR η₊ (η₂ ∗_M φ)` from TEN named links — `Hausierer` discharged

`hausierer_holds : HM.Hausierer` — `lem:hausierer` at the referee's corrected constants (`hbC`,
`hbR`), both the complex and the real bound, given the zero count `ZeroCount` it takes as its own
premise. Its three pieces are all proved:

* Mellin–Plancherel on the critical line (`crit_bessel`) and `τ ↦ G_δ(½+iτ)` differentiable
  (`critDeriv_holds`), `HelfMajHaus`;
* partial summation over the zeros given `ZeroCount` (`abelZeros_holds`), `HelfMajAbel`;
* the zeros of a real `L(s, χ)` symmetric under `s ↦ s̄`, with multiplicity (`RSy.realSym`),
  `RealSym` (`dcb2d4b6`).

`helfMajR_of_10` is `helfMajR_of_11` (`HelfMajElem.lean`) with that link supplied. Application only.

The ten that remain: `ExplicitFormula` (DEEP), `ZeroCount` (CITED, owner question), `PlusReg`,
`PlusNorms`, `PlusDecay`, `PhiDecay`, `MalReg`, `MalNorms`, `MalDecay`, `MalMain`.
-/

namespace Principia.Common.TernaryGoldbach.HM

/-- **`HM.Hausierer` holds** (it keeps `ZeroCount` as its own premise). -/
theorem hausierer_holds : Hausierer :=
  hausierer_of_realSym RSy.realSym

/-- **THE HEADLINE, TEN NAMED LINKS**: `helfMajR_of_11` with `Hausierer` discharged.
Application only. -/
theorem helfMajR_of_10 (hEF : ExplicitFormula) (hZC : ZeroCount)
    (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (fd : PhiDecay)
    (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mm : MalMain) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  helfMajR_of_11 hEF hZC hausierer_holds pr pn pd fd mr mn md mm

end Principia.Common.TernaryGoldbach.HM
