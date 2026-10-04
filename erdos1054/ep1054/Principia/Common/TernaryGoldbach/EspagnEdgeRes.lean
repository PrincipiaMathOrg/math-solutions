/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeResL

set_option autoImplicit false

/-!
# `EE.EspagnEdgeRes`, PROVED — the last owed piece of `prop:espagn`'s edge

`EE.EspagnEdgeRes` (`EspagnEdgeCover.lean`) was the part of `HX.EspagnEdge` that the two analytic
covers leave: `eq:luce` at `R = ϖ(q)` on the checked `q` where neither cover holds. The edge round
priced it at `41 424` moduli in `[16590, 66239]` and proposed a run over them. **No run is used.**
It is proved here by analysis plus finite EXACT case splits, from `CY.CERange` alone
(`espagnEdgeRes`), along the spine of `EspagnEdgeResSpine.lean`:

| regime | `q` | conclusion | file |
|---|---|---|---|
| W | `< 70000`, `ϖ < 3` | the inequality (`64 × 4` rational cases) | `EspagnEdgeResWin` |
| A | `< 70000`, `ϖ ≥ 3` | Cover A | `EspagnEdgeResA` |
| B | `[70000, 1.2·10¹⁰)` | Cover B (8 cells in `log q`) | `EspagnEdgeResB` |
| L | `[1.2·10¹⁰, 2.2·10¹⁰)` | `λ(q) ≤ 700 ≤ ϖ(q)` | `EspagnEdgeResL` |

Every numeric constant is certified in `ℚ` by `decide +kernel` (`EspagnEdgeResNum`: certified
exponentials, `γ` bounds from `SmallRatio`/`SuspiroWrap`); none of Helfgott's runs and no new
computation over moduli enters. `CY.CERange` (Rosser–Schoenfeld 1962 (2.11), already a binder of
the EP1054 headline) supplies `ω ∈ [0.6273, 0.62732]`, `c_{ρ,2} ≥ e^{0.1109}` and
`c_Δ ≥ 0.02741`; nothing else is assumed.

`espagnRed_of_rs3` is `EE.espagnRed_of_rs2` with the residue supplied: `HC.EspagnRed` from
Rosser–Schoenfeld and the large-`q` fact alone.
-/

namespace Principia.Common.TernaryGoldbach.ER

/-- **`EE.EspagnEdgeRes`, PROVED** from Rosser–Schoenfeld's `c_E` enclosure. -/
theorem espagnEdgeRes (cer : CY.CERange) : EE.EspagnEdgeRes :=
  edgeRes_of_regimes (regWin cer) (regA cer) (regB cer) (regL cer)

/-- **`HC.EspagnRed` with the edge closed**: `lem:suspiro` beyond `8.53` from RS75 and RS62
Thm 15, the large-`q` fact `HX.EspagnLargeQ`; `EE.EspagnEdgeRes` is now a theorem. -/
theorem espagnRed_of_rs3 (rs : HX.RS75Theta) (h15 : GS.RS62Thm15) (lq : HX.EspagnLargeQ) :
    HC.EspagnRed := fun cer =>
  EE.espagnRed_of_rs2 rs h15 (espagnEdgeRes cer) lq cer

end Principia.Common.TernaryGoldbach.ER
