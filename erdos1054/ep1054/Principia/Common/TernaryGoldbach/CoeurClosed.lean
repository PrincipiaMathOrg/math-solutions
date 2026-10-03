/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.CoeurSpine
import Principia.Common.PSieveBellen

set_option autoImplicit false

/-!
# `OC.CoeurY` with `prop:bellen` discharged: two named inputs remain

`CoeurSpine.coeurY_of_links` composed `OC.CoeurY` from `PSieve.BellenG`, `EspagnWin 1.36` and
`c_E ≥ 1.3325822`. `PSieve.bellenG` PROVES the first (`Common/PSieveBellen.lean`, the whole of
`prop:bellen`, `ternvin.tex` 2491-2603, axiom-clean). What is left of `cor:coeur` at `δ₀ = 392`:

* `EspagnWin 1.36` — `prop:espagn` (2870-3301) on the `CoeurY` window, even `q` only; its proof
  ends in a finite machine check (C10-C12; scoped in `CoeurSpine`'s gate header);
* `1.3325822 ≤ cE` — the lower half of Rosser–Schoenfeld 1962 (2.11) (C8).

`coeurY_closed_espagn` takes the PUBLISHED `prop:espagn` instead of its window.
-/

namespace Principia.Common.TernaryGoldbach.CY

/-- **`OC.CoeurY η` for every weight `η`**, from `EspagnWin 1.36` and `c_E ≥ 1.3325822`:
`coeurY_of_links` with `BellenG` discharged by `PSieve.bellenG`. -/
theorem coeurY_closed (hesp : EspagnWin 1.36) (hce : 1.3325822 ≤ cE) (ηp : ℝ → ℝ) :
    OC.CoeurY ηp :=
  coeurY_of_links Principia.Common.PSieve.bellenG hesp hce ηp

/-- **`OC.CoeurY HW.etaPlus`** (Helfgott's `η₊`) from `EspagnWin 1.36` and `c_E ≥ 1.3325822`. -/
theorem coeurY_helf_closed (hesp : EspagnWin 1.36) (hce : 1.3325822 ≤ cE) :
    OC.CoeurY HW.etaPlus :=
  coeurY_closed hesp hce HW.etaPlus

/-- **`OC.CoeurY HW.etaPlus` from the PUBLISHED `prop:espagn`** and `c_E ≥ 1.3325822`. -/
theorem coeurY_closed_espagn (hesp : Espagn) (hce : 1.3325822 ≤ cE) : OC.CoeurY HW.etaPlus :=
  coeurY_of_espagn Principia.Common.PSieve.bellenG hesp hce HW.etaPlus

end Principia.Common.TernaryGoldbach.CY
