/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SplitCheb
import Principia.Common.TernaryGoldbach.DrujalPlancherel
import Principia.Common.TernaryGoldbach.KSmall
import Principia.Common.TernaryGoldbach.PlattCite
import Principia.Erdos1054.Proofs.BalancedT0
import Principia.Erdos1054.Alt7.Round7Bal

set_option autoImplicit false

/-!
# EP1054 at the Chebyshev reduction: the major-side links, then ONE minor hypothesis at `1.0154`

GENERATED (`scratchpad/cheb/gen_cheb.py`) from `FromC0.ep1054_from_c0` by counted substitution,
with `DS.MardiQ` supplied as `FromPlancherel.ep1054_plancherel` supplies it (`DP.mardiQ_helf`).

The path traced (the current headline): `FromPlancherel.ep1054_plancherel` →
`FromCorrected.ep1054_corrected` → `FromOstopC.ep1054_from_ostopC` → `FromC0.ep1054_from_c0` →
`MC0.helfgottAt_c0` → `Round7Bal.ep1054_all_helfgottAt` (`BalancedK.balanced_of_helfgottAt`,
`K = 0.00032`) → `Round7Bal.ep1054_all_bal`. Regenerated minimal path, three changes:

* **the reduction**: `Round7Bal.ep1054_all_helfgottAt` becomes `Round7Bal.ep1054_all_bal` after
  `BalancedT0.balanced_of_cheb`, which asks only for `HelfgottAt 0.000205`;
* **the split**: `MC0.helfgottAt_c0` becomes `SC.helfgottAt_cheb` (major `1.0563699` unchanged,
  minor `1.0154`, side condition `2.0522929·10⁻⁴ ≥ 0.000205`);
* **the minor side**: `FromOstopC`, `FromCorrected` and `FromPlancherel` reach the minor arcs
  through `OC.OstopC` and `OC.MNumC`, which carry Helfgott's printed minor-arc constant, found
  WRONG (LEAN-PROGRESS 2026-09-30). None of that is copied: the minor arcs enter as ONE
  hypothesis, `RT.MinorUpperAt 1.0154 η₊ η*`. `DS.BandQ` and `DS.TailQ` fed only that route's
  `J` floor (`SF.drujalLowP_of_spine`), so they drop out with it.

`ep1054_cheb_of_old` shows the minor hypothesis is no stronger than `FromC0`'s (`0.9924888`).
`ep1054_cheb_ks` supplies `DS.KSmall η₊` (`KS.ksmall_helf`). Open in `ep1054_cheb_ks`, on
Helfgott's fixed weights: `RT.HelfMajFull`, `RW.NefumoW`, `DS.PerArc`, `DS.ArcInt` (major side),
`RT.MinorUpperAt 1.0154` (minor side), and the cited `PC.PlattThm71`, `PC.PlattTrudgian`.
-/

namespace Principia.Erdos1054.Alt7.FromCheb

open Principia.Common.TernaryGoldbach

/-- **THE CHEBYSHEV HEADLINE.** EP1054 from Platt's Theorem 7.1, Platt–Trudgian, the
major-side links on Helfgott's weights (`MardiQ` supplied by `DP.mardiQ_helf`), and the
minor arcs as ONE hypothesis at `1.0154`. Application only. -/
theorem ep1054_cheb (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (ks : DS.KSmall HW.etaPlus) (mn : RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  Round7Bal.ep1054_all_bal (Proofs.BalancedT0.balanced_of_cheb
    (SC.helfgottAt_cheb (PC.plattFull_of_cited p z) hm RW.regW_helf nf
      (DS.drujalE100_of_spine HW.etaPlus pa ai DP.mardiQ_helf ks) CT.clowerE_helf BS.band_sharp mn))

/-- **The same headline with `DS.KSmall η₊` supplied** by `KS.ksmall_helf` (as
`FromKSmall.ep1054_ksmall_planch` supplies it to the old headline). Application only. -/
theorem ep1054_cheb_ks (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc)
    (pa : DS.PerArc HW.etaPlus) (ai : DS.ArcInt HW.etaPlus)
    (mn : RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar) :
    Principia.Erdos1054.Spine.DerivedClaims :=
  ep1054_cheb p z hm nf pa ai KS.ksmall_helf mn

/-- **The new minor hypothesis is no stronger than the old one**: `RT.MinorUpperAt 0.9924888`
(the minor target of `FromC0.ep1054_from_c0`, hence of every headline built on it) implies
`RT.MinorUpperAt 1.0154`. -/
theorem ep1054_cheb_of_old (ηp ηs : ℝ → ℝ) (h : RT.MinorUpperAt 0.9924888 ηp ηs) :
    RT.MinorUpperAt 1.0154 ηp ηs :=
  RT.minorUpper_le (by norm_num) ηp ηs h

end Principia.Erdos1054.Alt7.FromCheb
