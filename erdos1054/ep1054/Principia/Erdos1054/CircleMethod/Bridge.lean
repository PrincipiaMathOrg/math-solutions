/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.Reduction
import Principia.Erdos1054.Alt.GoldbachRoute

set_option autoImplicit false

/-!
# EP1054: `Std_GoldbachDensZero` from the ported circle method

`Principia.Erdos1054.Alt.GoldbachRoute` proves Theorem 1.3 (`Thm_AlmostLogTail`) and
`Cor_FixedCofactorDefect` from `Std_GoldbachDensZero`, and says where that input comes from: the
master `GoldbachChainMaster.lean` in the PNT+ workspace, which pins another Mathlib and so could
only be linked to this library by a *textual transcription* of four definitions (LEAN-PROGRESS
R2-7).

`Principia.Common.Goldbach` is that master's circle-method half, ported into this library. This
module closes the transcription gap with the kernel:

* `densityZero_notSumOfTwoPrimes_eq` — the port's `DensityZero notSumOfTwoPrimes` and the Alt
  module's verbatim copy are the same proposition, by `rfl`;
* `std_GoldbachDensZero_of_mediumPNT` — `MediumPNTBound → Alt.Std_GoldbachDensZero`;
* `thm_AlmostLogTail_of_mediumPNT`, `cor_FixedCofactorDefect_of_mediumPNT` — Theorem 1.3 and the
  fixed-cofactor corollary from `MediumPNTBound` alone.

The one hypothesis, `Principia.Common.SW.MediumPNTBound` (the explicit prime number theorem
`|ψ(x) − x| ≤ C·x·exp(−c(log x)^{1/10})`), is the one the Siegel–Walfisz port still carries; it
enters the circle method only through Siegel–Walfisz on the major arcs.

This lives outside `Principia/Common/` because it is specific to EP1054: `Common/Goldbach` is
campaign-agnostic and imports nothing of `Erdos1054`.
-/

namespace Principia.Erdos1054.CircleMethod

open Principia.Common.SW (MediumPNTBound)

/-- The ported master's density-zero statement is, definitionally, the one `Alt.GoldbachRoute`
transcribed from the master: the kernel checks the transcription. -/
theorem densityZero_notSumOfTwoPrimes_eq :
    Principia.Common.Goldbach.GoldbachReduction.DensityZero
        Principia.Common.Goldbach.GoldbachReduction.notSumOfTwoPrimes =
      Principia.Erdos1054.Alt.DensityZero Principia.Erdos1054.Alt.notSumOfTwoPrimes :=
  rfl

/-- **Almost-all binary Goldbach in the Alt module's words**, from `MediumPNTBound`. -/
theorem densityZero_notSumOfTwoPrimes_of_mediumPNT (hPNT : MediumPNTBound) :
    Principia.Erdos1054.Alt.DensityZero Principia.Erdos1054.Alt.notSumOfTwoPrimes :=
  densityZero_notSumOfTwoPrimes_eq ▸
    Principia.Common.Goldbach.GoldbachReduction.almost_all_binary_goldbach_of_mediumPNT hPNT

/-- **`Std_GoldbachDensZero` from the explicit prime number theorem.** The even numbers that are
not a sum of two primes have density zero (`Defs.DensZero`), given `MediumPNTBound`. -/
theorem std_GoldbachDensZero_of_mediumPNT (hPNT : MediumPNTBound) :
    Principia.Erdos1054.Alt.Std_GoldbachDensZero :=
  Principia.Erdos1054.Alt.std_GoldbachDensZero_of_densityZero
    (densityZero_notSumOfTwoPrimes_of_mediumPNT hPNT)

/-- **EP1054 Theorem 1.3 (`thm:almost-log-tail`) from `MediumPNTBound` alone**, through
`Alt.thm_AlmostLogTail_of_goldbachDensZero`. -/
theorem thm_AlmostLogTail_of_mediumPNT (hPNT : MediumPNTBound) :
    Principia.Erdos1054.Thm_AlmostLogTail :=
  Principia.Erdos1054.Alt.thm_AlmostLogTail_of_goldbachDensZero
    (std_GoldbachDensZero_of_mediumPNT hPNT)

/-- **The fixed-cofactor corollary from `MediumPNTBound` alone**, through
`Alt.cor_FixedCofactorDefect_of_goldbachDensZero`. -/
theorem cor_FixedCofactorDefect_of_mediumPNT (hPNT : MediumPNTBound) :
    Principia.Erdos1054.Cor_FixedCofactorDefect :=
  Principia.Erdos1054.Alt.cor_FixedCofactorDefect_of_goldbachDensZero
    (std_GoldbachDensZero_of_mediumPNT hPNT)

end Principia.Erdos1054.CircleMethod
