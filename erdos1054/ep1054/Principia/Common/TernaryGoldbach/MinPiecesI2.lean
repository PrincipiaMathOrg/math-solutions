/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.I2Arith

set_option autoImplicit false

/-!
# The minarcs Main Theorem for `η₂` from the ten links still open

`MPII.minMainP_of_open` reaches `OP.MinMainP 0.811 45.7575` from eleven links and `RS62Thm15`.
`I2A.i2Arith` proves one of them (`MPc.I2Arith`). Application only.
-/

namespace Principia.Common.TernaryGoldbach.MPI2

/-- **`OP.MinMainP 0.811 45.7575` from the ten open links** (`I2Arith` supplied). -/
theorem minMainP_of_ten (hb1 : MPc.Bostb1At) (hgr : MPc.Grara) (hro : MPc.Ronsard)
    (hme : MPc.Meproz) (hb2 : MPc.Bosta2Eta2) (hv1 : MPc.Vinland1At) (her : MPc.EriksagaAt)
    (hs1 : MPc.SecI1At) (hs2 : MPc.SecI2At) (hs3 : MPc.SecIIAt) (h15 : GS.RS62Thm15) :
    OP.MinMainP 0.811 45.7575 :=
  MPII.minMainP_of_open hb1 hgr hro hme hb2 I2A.i2Arith hv1 her hs1 hs2 hs3 h15

end Principia.Common.TernaryGoldbach.MPI2
