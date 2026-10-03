/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.FromCheb
import Principia.Common.TernaryGoldbach.OstopL
import Principia.Common.TernaryGoldbach.DrujalLowP

set_option autoImplicit false

/-!
# EP1054 on the Chebyshev reduction with the minor arcs at Helfgott's CORRECTED `L`

`FromCheb.ep1054_cheb_ks` takes the minor arcs as ONE hypothesis, `RT.MinorUpperAt 1.0154 η₊ η*`.
This file supplies it from `OL.minorAt_ostopL_cheb`, the layer-1 composition of the corrected
`thm:ostop` (F6, F7) restated with minarcs' `L` constant corrected (`q³`, one `ε = 0.07`:
`log q^{13.6516}δ₀^{1.7984} + 22.7538`). The `J` floor `8.57476` comes from the lem:drujal spine
(`SF.drujalLowP_of_spine`) with `BandQ`, `TailQ` and `KSmall` proved.

`FelipaAt 0.6406 η₊` stays a hypothesis: the existing chain supplies it only through Helfgott's
printed `Malheur` (`OL.felipaAt_6406_of_helf`), whose cross term is short by a factor 2 (F4).

Open, on Helfgott's fixed weights: `RT.HelfMajFull`, `RW.NefumoW`, `DS.PerArc`, `DS.ArcInt`,
`OL.FelipaAt 0.6406`, `OL.OstopL` (layer 2), `OL.MNumL HW.phi 8.54 0.8095 0.6406` (numerics; exact
corrected `M̃ ≈ 0.7924` against `0.8095`). Cited: `PC.PlattThm71`, `PC.PlattTrudgian`.
-/

namespace Principia.Erdos1054.Alt7.FromOstopL

open Principia.Common.TernaryGoldbach

/-- **EP1054 with the minor arcs at the corrected `L`**, through the Chebyshev reduction
(`K = 0.000205`, minor target `1.0154`). -/
theorem ep1054_ostopL (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (hfe : OL.FelipaAt 0.6406 HW.etaPlus) (hos : OL.OstopL HW.etaPlus HW.etaStar HW.phi)
    (hmn : OL.MNumL HW.phi 8.54 0.8095 0.6406) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  FromCheb.ep1054_cheb_ks p z hm nf pa ai
    (OL.minorAt_ostopL_cheb (PC.plattFull_of_cited p z) hm hfe hos
      (SF.drujalLowP_of_spine HW.etaPlus HW.etaCirc pa ai DP.bandQ_helf DP.tailQ_helf
        KS.ksmall_helf) hmn)

end Principia.Erdos1054.Alt7.FromOstopL
