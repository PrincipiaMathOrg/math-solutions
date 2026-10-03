/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Alt6.Dusart.Numeric

set_option autoImplicit false

/-!
# `Cite_Dusart_Thm69` removed: `Step_FraitureLargePrimeSum` from Chebyshev's 1852 bound

The paper uses Dusart's Theorem 6.9 (explicit `π(x)` bounds, `Cite_Dusart_Thm69`) once, in
`Link_Step_FraitureLargePrimeSum`, to get the closed inequality

  `Step_FraitureLargePrimeSum : 10^27 + 10^8 < ∑_{4·10^7 < p ≤ 3.99·10^14, p prime} p`

(EP1054.tex lines 794–819; the true value of the sum is about `2.37·10^27`). This module proves
that inequality with no hypothesis (`step_FraitureLargePrimeSum_unconditional`), so the link holds
without its input (`link_Step_FraitureLargePrimeSum_unconditional`).

The mathematics is in `Principia.Erdos1054.Alt6.Dusart.Numeric` (`sum_primes_Ioc_gt`, whose type is
the body of `Step_FraitureLargePrimeSum` verbatim): Chebyshev's lower constant
`A = log(2¹⁴3⁹5⁵)/30 = 0.92129…` (`Principia.Common.Chebyshev.psi_thirty_mul_ge`), Mathlib's
`θ(x) ≤ x log 4`, and discrete Abel summation (`Principia.Common.Chebyshev.sum_primes_ge`) give
`∑_{p ≤ 3.99·10^14} p ≥ 1.067·10^27`. No statement is weakened: the step is the spine's own `Prop`.

With this, `Cite_Dusart_Thm69` has no remaining consumer in the spine: its sole consuming link is
`Link_Step_FraitureLargePrimeSum` (`Spine.lean`).
-/

namespace Principia.Erdos1054.Alt6.Dusart

/-- **`Step_FraitureLargePrimeSum`, unconditionally** (EP1054.tex lines 794–819):
`10^27 + 10^8 < ∑_{4·10^7 < p ≤ 3.99·10^14, p prime} p`.

**Remaining hypotheses: none.** (Rounds 1–5: `Cite_Dusart_Thm69`.) -/
theorem step_FraitureLargePrimeSum_unconditional :
    Principia.Erdos1054.Step_FraitureLargePrimeSum :=
  sum_primes_Ioc_gt

/-- **`Link_Step_FraitureLargePrimeSum` without its input**: the link's conclusion holds
outright, so `Cite_Dusart_Thm69` is never used. -/
theorem link_Step_FraitureLargePrimeSum_unconditional :
    Principia.Erdos1054.Spine.Link_Step_FraitureLargePrimeSum :=
  fun _ => step_FraitureLargePrimeSum_unconditional

end Principia.Erdos1054.Alt6.Dusart
