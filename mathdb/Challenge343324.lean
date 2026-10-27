import Principia.MathDB.Statements.P343324

/-!
# MathDB #343324 — the challenge

The audit surface: the statements, with `sorry` for every proof. This module imports the
statements module ONLY. It must never import `Principia.MathDB.Problem343324`, because
Comparator's threat model assumes the solution has not been compiled while the challenge was
built -- and an import would compile it.
-/

namespace MathDB343324

theorem arithmetic_core : Principia.MathDB.P343324.ArithmeticCore := sorry

theorem conjecture_3_1 : Principia.MathDB.P343324.Conjecture31 := sorry

end MathDB343324
