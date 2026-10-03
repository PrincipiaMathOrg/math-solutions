/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.GoldbachRate.Rate
import Principia.Erdos1054.Rate.Routes

set_option autoImplicit false

/-!
# EP1054 Theorem 1.4, unconditional: the Goldbach rate from the circle method

`Principia.Erdos1054.Rate.Routes` proves Theorem 1.4 (`Thm_SubexpGrowth`) and
`Lem_AnalyticOddRepresentability` from `Std_GoldbachRate`, the bound
`#{n ≤ X : n even, n ≠ p + q} ≤ C X / log X` (Route A of `THM14-RATE-PLAN.md`).
`Principia.Common.GoldbachRate` proves that bound from the ported circle method
(`goldbach_exceptional_rate_of_mediumPNT`), and unconditionally with `MediumPNTBound` discharged
(`goldbach_exceptional_rate`). This module joins the two:

* `std_GoldbachRate_of_mediumPNT`, `std_GoldbachRate_unconditional` — `Std_GoldbachRate`. The
  ported `GoldbachReduction.countUpTo`/`notSumOfTwoPrimes` and the `Alt` copies are the same
  definitions, so the transfer is definitional (as in `CircleMethod.Bridge`);
* `lem_AOR_unconditional` — **`Lem_AnalyticOddRepresentability`, unconditional** (both halves:
  the paper's bound `C (X^{1-c} + X / log X)` and the `o(X / log₃ X)` form);
* `thm_SubexpGrowth_unconditional` — **EP1054 Theorem 1.4 (`thm:subexp-growth`),
  unconditional**: no `Cite_MV_exceptional`, no `Cite_Helfgott_weighted`, no hypothesis at all.

The rate constant is ineffective (Siegel–Walfisz), which Theorem 1.4 does not mind.
-/

namespace Principia.Erdos1054.Rate

open Principia.Common.SW (MediumPNTBound)

/-- `Std_GoldbachRate` from the explicit prime number theorem, through the rated circle method
`Principia.Common.GoldbachRate.goldbach_exceptional_rate_of_mediumPNT`. The master's
`countUpTo`/`notSumOfTwoPrimes` and the `Alt` copies in `Std_GoldbachRate` agree definitionally. -/
theorem std_GoldbachRate_of_mediumPNT (hPNT : MediumPNTBound) : Std_GoldbachRate :=
  Principia.Common.GoldbachRate.goldbach_exceptional_rate_of_mediumPNT hPNT

/-- **`Std_GoldbachRate`, unconditional**: the even numbers `≤ X` that are not a sum of two
primes number `≤ C X / log X` for all large `X`. `MediumPNTBound` is discharged by
`Principia.Common.SW.mediumPNTBound`. -/
theorem std_GoldbachRate_unconditional : Std_GoldbachRate :=
  std_GoldbachRate_of_mediumPNT Principia.Common.SW.mediumPNTBound

/-- `Lem_AnalyticOddRepresentability` from `MediumPNTBound`. -/
theorem lem_AOR_of_mediumPNT (hPNT : MediumPNTBound) :
    Principia.Erdos1054.Lem_AnalyticOddRepresentability :=
  lemAOR_of_goldbachRate (std_GoldbachRate_of_mediumPNT hPNT)

/-- **`Lem_AnalyticOddRepresentability` (both halves), unconditional**, through
`Routes.lemAOR_of_goldbachRate`. The paper takes it from `Cite_MV_exceptional`. -/
theorem lem_AOR_unconditional : Principia.Erdos1054.Lem_AnalyticOddRepresentability :=
  lemAOR_of_goldbachRate std_GoldbachRate_unconditional

/-- Theorem 1.4 (`thm:subexp-growth`) from `MediumPNTBound`. -/
theorem thm_SubexpGrowth_of_mediumPNT (hPNT : MediumPNTBound) :
    Principia.Erdos1054.Thm_SubexpGrowth :=
  thm_SubexpGrowth_of_goldbachRate (std_GoldbachRate_of_mediumPNT hPNT)

/-- **EP1054 Theorem 1.4 (`thm:subexp-growth`), unconditional**, through
`Routes.thm_SubexpGrowth_of_goldbachRate`: every input of its spine is a theorem of this
library. -/
theorem thm_SubexpGrowth_unconditional : Principia.Erdos1054.Thm_SubexpGrowth :=
  thm_SubexpGrowth_of_goldbachRate std_GoldbachRate_unconditional

end Principia.Erdos1054.Rate
