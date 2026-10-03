/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonLDFE
import Principia.Common.TernaryGoldbach.AgamonDigamma
import Principia.Common.TernaryGoldbach.AgamonVM32
import Principia.Common.TernaryGoldbach.AgamonKInt

set_option autoImplicit false

/-!
# `EF.LeftLD` PROVED

**`leftLD_holds : EF.LeftLD`**, with no hypothesis: `AG.leftLD_of_links` applied to its four
sub-links, all PROVED — `ldfe_holds` (the functional equation in log-derivative form,
`AgamonLDFE`), `digammaLine_holds` (`|ψ(z) − log z| ≤ 1/2` on `Re z = 3/2`, `AgamonDigamma`, on the
PNT+ digamma series), `vm32_holds` (`∑Λ(n)n^{−3/2} ≤ 7/4`, `AgamonVM32`) and `kInt_holds`
(`∫K²/|s|² ≤ 2π·8²`, `AgamonKInt`).

So for every primitive `χ` mod `q`,
`∫_ℝ |L'/L(−1/2 + iτ, χ)|²/|−1/2 + iτ|² dτ ≤ 2π(log q + 8)²` — the survey's EF6–7 with the
corrected constant `8` (the printed `6.01` drops `|arg| ≤ π/2`, flag F6).
-/

namespace Principia.Common.TernaryGoldbach.AG

open Principia.Common.TernaryGoldbach.EF

/-- **`EF.LeftLD` HOLDS.** -/
theorem leftLD_holds : LeftLD :=
  leftLD_of_links ldfe_holds digammaLine_holds vm32_holds kInt_holds

end Principia.Common.TernaryGoldbach.AG
