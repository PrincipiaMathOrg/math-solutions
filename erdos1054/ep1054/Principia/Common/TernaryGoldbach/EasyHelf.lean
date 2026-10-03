/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EasyNorms
import Principia.Common.TernaryGoldbach.EasySup
import Principia.Common.TernaryGoldbach.EasyStar
import Principia.Common.TernaryGoldbach.EasyThird

set_option autoImplicit false

/-!
# `NormsE` and `SupN` on Helfgott's own weights: all that is left is one band-limiting bound

On `η₊ = HW.etaPlus`, `η* = HW.etaStar`, `η∘ = HW.etaCirc`:

* `MajSp.SupN` is a THEOREM (`EN.supN_helf`).
* Seven of `EN.NormsE`'s nine conjuncts are THEOREMS: `0.8 ≤ |η∘|₂ ≤ 0.8002`, `|η∘'''|₁ ≤ 40`,
  `|η∘'|₂² ≤ 3`, `|η*|₁ = √(π/2)/49`, `|η*|₂² ≤ 2/49`, `|η₊|₁ ≤ 1.2`.
* The remaining two are the band-limiting `L²` norms `|η₊ − η∘|₂ ≤ 3·10⁻⁵` and `|η₊|₂ ≤ 0.81`, and
  `normsE_helf_iff` shows `NormsE` on these weights is EQUIVALENT to exactly those two.
  Both follow from `EN.BandSharp` (`|h₂₀₀ − h| ≤ 4.5·10⁻⁵` on `t > 0`), the one named analytic
  obligation (`normsE_helf`).

So `helfgottAt_band` derives `BalancedK.HelfgottAt 0.00032` from `PlattFull`, HelfMaj, `Reg`,
`Nefumo`, `DrujalE`, `CLowerE`, the two band-limiting norms and the minor arcs: `Norms`/`NormsE`
and `SupN` are gone as links. `helfgottAt_sharp` is the same with `BandSharp` in their place.
-/

namespace Principia.Common.TernaryGoldbach.EN

open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-- **`NormsE` on Helfgott's weights IS its two band-limiting conjuncts**: the other seven are
theorems (`l2_circ_lo`, `l2_circ_hi`, `l1_third_le`, `l2_deriv_sq_le`, `l1_etaStar`,
`l2_etaStar_sq`, `l1_etaPlus_le`). -/
theorem normsE_helf_iff : NormsE HW.etaPlus HW.etaStar HW.etaCirc ↔
    MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) ≤ 3e-5 ∧ MajSp.l2 HW.etaPlus ≤ 0.81 := by
  constructor
  · intro h
    exact ⟨h.2.2.1, h.2.2.2.2.2.2.2.2⟩
  · rintro ⟨hd, hp⟩
    exact ⟨l2_circ_lo, l2_circ_hi, hd, l1_third_le, l2_deriv_sq_le, l1_etaStar, l2_etaStar_sq,
      l1_etaPlus_le, hp⟩

/-- **`BandSharp → NormsE`** on Helfgott's own weights. -/
theorem normsE_helf (hb : BandSharp) : NormsE HW.etaPlus HW.etaStar HW.etaCirc :=
  normsE_helf_iff.mpr ⟨l2_diff_band hb, l2_plus_band hb⟩

/-- **`HelfgottAt 0.00032` with `NormsE` and `SupN` discharged**: the two band-limiting `L²` norms
take their place. -/
theorem helfgottAt_band (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar)
    (hd : MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) ≤ 3e-5)
    (hp : MajSp.l2 HW.etaPlus ≤ 0.81)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  helfgottAt_easy pf hm rg nf dj cl (normsE_helf_iff.mpr ⟨hd, hp⟩) supN_helf mn

/-- **`HelfgottAt 0.00032` with `BandSharp` as the only numerical link.** -/
theorem helfgottAt_sharp (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  helfgottAt_easy pf hm rg nf dj cl (normsE_helf hb) supN_helf mn

end Principia.Common.TernaryGoldbach.EN
