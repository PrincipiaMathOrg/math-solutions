/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajTails
import Principia.Common.TernaryGoldbach.HelfMajKolona
import Principia.Common.TernaryGoldbach.HelfMajPhi

set_option autoImplicit false

/-!
# `MR.HelfMajR η₊ (η₂ ∗_M φ)` from ELEVEN named links

`helfMajR_of_11`: HelfMaj Thm 1.4, Cor 1.3 and Prop 1.5 at the retyped constants, by application,
from the eleven links still open after this round. Discharged since `helfMajR_of_16`
(`HelfMajMalTail.lean`):

| link | how | file |
|---|---|---|
| `PhiTailInt` | PROVED, `phiTailInt_holds` (margin `≥ 7 %`) | `HelfMajTails` |
| `PlusTailInt` | PROVED, `plusTailInt_holds` (margin `≥ 11 %`) | `HelfMajTails` |
| `Kolona` | PROVED, `kolona_holds` (an exact identity) | `HelfMajKolona` |
| `PhiReg` | PROVED, `phiReg_holds` | `HelfMajPhi` |
| `PhiNorms` | REPLACED by the proved `PhiNormsL` (see below) | `HelfMajPhi` |

`PhiNorms`' stated constants need `ψ'(5/2)` and `Γ(5/4)` to `10⁻⁵`; the proved `PhiNormsL` feeds
a re-derived Cor 1.3 chain (`coprarR_of_linksL`) that still closes at the retyped constants.

The eleven that remain: `ExplicitFormula` (DEEP), `ZeroCount` (CITED, owner question),
`Hausierer` (ELEM given the zero count and Mellin–Plancherel), `PlusReg`, `PlusNorms`, `PlusDecay`,
`PhiDecay`, `MalReg`, `MalNorms`, `MalDecay`, `MalMain`.
-/

namespace Principia.Common.TernaryGoldbach.HM

/-- **THE HEADLINE, ELEVEN NAMED LINKS**: `GarmolaDecr`, `Eta2Moments`, `MalTailInt`, `PhiTailInt`,
`PlusTailInt`, `Kolona`, `PhiReg` discharged; `PhiNorms` replaced by the proved `PhiNormsL`.
Application only. -/
theorem helfMajR_of_11 (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (fd : PhiDecay)
    (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mm : MalMain) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  fun pf => ⟨malporR_of_links hEF hZC hHs garmolaDecr_holds pr pn pd plusTailInt_holds pf,
    coprarR_of_linksL hEF hZC hHs garmolaDecr_holds phiReg_holds phiNormsL_holds fd
      phiTailInt_holds kolona_holds eta2Moments_holds pf,
    malheurR_of_links hEF hZC hHs garmolaDecr_holds mr mn md malTailInt_holds mm pf⟩

end Principia.Common.TernaryGoldbach.HM
