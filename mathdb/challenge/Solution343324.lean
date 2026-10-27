import Principia.MathDB.Problem343324

/-!
# MathDB #343324 — the solution

The same two constants as `Challenge343324`, discharged by direct term assignment from the
development. No tactic proof lives here: every proof is a reference into
`Principia.MathDB.Problem343324`, so this file adds no mathematics of its own and the
comparison is against the banked module.
-/

namespace MathDB343324

theorem arithmetic_core : Principia.MathDB.P343324.ArithmeticCore :=
  fun m n hm hn hdvd => Principia.MathDB.P343324.odd_of_dvd m n hm hn hdvd

theorem conjecture_3_1 : Principia.MathDB.P343324.Conjecture31 :=
  fun p hp a hrule n hn hfix => Principia.MathDB.P343324.main p hp a hrule n hn hfix

end MathDB343324
