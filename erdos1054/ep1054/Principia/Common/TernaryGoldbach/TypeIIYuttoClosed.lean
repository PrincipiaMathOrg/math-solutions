/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIYuttoAnna
import Principia.Common.TernaryGoldbach.TypeIIYuttoDSum
import Principia.Common.TernaryGoldbach.TypeIIWeightEM

set_option autoImplicit false

/-!
# The corrected `lem:yutto` links PROVED, and `M2H.CortoLarge` from cited inputs only

All six links of `M2Y` are now theorems (`M2YA.anna2`, `M2YC.convK`, `M2YK.kSumH`,
`M2YK.kSumQ`, `M2YD.dSumH`, `M2YD.dSumQ`), so:

```
 yuttoMid2C_holds   : HC.RamareCited → M2LC.YuttoMid2C                          PROVED
 yuttoBig2C_holds   : HC.RamareCited → M2Y.RamareMarraki → M2LC.YuttoBig2C       PROVED
 cortoLarge_of_cited : HC.YuttoSmallCited → HC.CortoC0Cited → HC.RamareCited →
                       M2Y.RamareMarraki → M2H.CortoLarge                        PROVED
```

The remaining inputs are Helfgott's cited computations (`HC.RamareCited` = `eq:ramare`,
`HC.YuttoSmallCited`, `HC.CortoC0Cited`, all at his exact statements) and one published theorem
of another author, `M2Y.RamareMarraki` (Ramaré, Acta Arith. 157 (2013), Cor. 1.4).
-/

namespace Principia.Common.TernaryGoldbach.M2YZ

/-- **[YuttoMid2C] PROVED** from `eq:ramare` alone. -/
theorem yuttoMid2C_holds (hR : HC.RamareCited) : M2LC.YuttoMid2C :=
  M2Y.yuttoMid2C_of_links M2YA.anna2 M2YC.convK M2YK.kSumH M2YD.dSumH hR

/-- **[YuttoBig2C] PROVED** from `eq:ramare` and Ramaré's `eq:marraki`. -/
theorem yuttoBig2C_holds (hR : HC.RamareCited) (hM : M2Y.RamareMarraki) : M2LC.YuttoBig2C :=
  M2Y.yuttoBig2C_of_links M2YA.anna2 M2YC.convK M2YK.kSumH M2YK.kSumQ M2YD.dSumH M2YD.dSumQ
    hR hM

/-- **`M2H.CortoLarge` from cited inputs only.** -/
theorem cortoLarge_of_cited (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
    (hR : HC.RamareCited) (hM : M2Y.RamareMarraki) : M2H.CortoLarge :=
  M2W.cortoLarge_of_yutto (yuttoMid2C_holds hR) (yuttoBig2C_holds hR hM) ys c0

end Principia.Common.TernaryGoldbach.M2YZ
