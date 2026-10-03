/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajElem6
import Principia.Common.TernaryGoldbach.HelfMajMalDecay

set_option autoImplicit false

/-!
# `MR.HelfMajR η₊ (η₂ ∗_M φ)` from FIVE named links

`helfMajR_of_5` is `helfMajR_of_6` (`HelfMajElem6.lean`) with `MalDecay` REPLACED by the proved
`HP.MalDecayL` (`|Mη₊,₂(s)| ≤ 5·10⁵·fmal`, `HelfMajMalDecay.lean`: `h_H` band-limited
(`HP.hH_rep`), `Mg = (log x)Γ(z)/2 + Γ'(z)/4`, explicit `Γ`/`Γ'` decay on vertical lines
(`HelfMajGammaV.lean`)), and Prop 1.5 re-derived at it (`HP.malheurR_of_linksL2`: the high-zero
tail `Tm ≤ 7·10⁻⁷ log x` of the `1.05·10⁻⁶ log x` budget).

The five that remain: `ExplicitFormula` (DEEP, another round), `ZeroCount` (CITED, owner
question), `PlusDecay`, `PhiDecay` (the saddle point of majarcs §3, `cor:amanita1` `k = 1, 2`),
`MalMain` (`|η₊ − η∘|₂ ≲ 2.4·10⁻⁶` plus the VNODE values). Application only.
-/

namespace Principia.Common.TernaryGoldbach.HM

/-- **THE HEADLINE, FIVE NAMED LINKS**: `helfMajR_of_6` with `MalDecay` replaced by the proved
`MalDecayL`. Application only. -/
theorem helfMajR_of_5 (hEF : ExplicitFormula) (hZC : ZeroCount)
    (pd : PlusDecay) (fd : PhiDecay) (mm : MalMain) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  fun pf => ⟨HP.malporR_of_linksL hEF hZC hausierer_holds garmolaDecr_holds pd plusTailInt_holds pf,
    coprarR_of_linksL hEF hZC hausierer_holds garmolaDecr_holds phiReg_holds phiNormsL_holds fd
      phiTailInt_holds kolona_holds eta2Moments_holds pf,
    HP.malheurR_of_linksL2 hEF hZC hausierer_holds garmolaDecr_holds mm pf⟩

end Principia.Common.TernaryGoldbach.HM
