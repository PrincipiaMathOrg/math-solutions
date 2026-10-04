/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajElem5
import Principia.Common.TernaryGoldbach.HelfMajMalMain
import Principia.Common.TernaryGoldbach.HelfgottCited

set_option autoImplicit false

/-!
# `MR.HelfMajR η₊ (η₂ ∗_M φ)` from FOUR named links and the cited VNODE-LP values

`malMain_of_cited`: the STATED `HM.MalMain` from `HC.MalMainCited` (Helfgott's VNODE-LP values,
cited at his exact statement; only the first two conjuncts, `∫η∘²` and `∫η∘² log t`, are used),
through `MM.malMain_of_vnode` (`HelfMajMalMain.lean`: the cross term computed in Mellin space,
`MM.cross_le`). `eq:impath` and its `C₄ = 2013.18` are not used.

`helfMajR_of_4` is `helfMajR_of_5` (`HelfMajElem5.lean`) with `MalMain` supplied. The four links
that remain: `ExplicitFormula` (DEEP), `ZeroCount` (CITED, owner question), `PlusDecay`,
`PhiDecay` (the saddle point, `cor:amanita1` `k = 1, 2`). Application only.
-/

namespace Principia.Common.TernaryGoldbach.HM

/-- **`MalMain` from the cited VNODE-LP values.** -/
theorem malMain_of_cited (hc : HC.MalMainCited) : MalMain :=
  MM.malMain_of_vnode hc.1 hc.2.1

/-- **THE HEADLINE, FOUR NAMED LINKS** (plus the cited `HC.MalMainCited`): `helfMajR_of_5` with
`MalMain` proved. Application only. -/
theorem helfMajR_of_4 (hEF : ExplicitFormula) (hZC : ZeroCount) (pd : PlusDecay)
    (fd : PhiDecay) (mc : HC.MalMainCited) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  helfMajR_of_5 hEF hZC pd fd (malMain_of_cited mc)

end Principia.Common.TernaryGoldbach.HM
