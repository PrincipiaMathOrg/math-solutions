/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/RangeCoverage.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.SmallBq
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.FirstWindowBridge

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

theorem represents_six_to_firstWindowBridge :
    ∀ n, 6 ≤ n → n ≤ 178813826 → Represents n := by
  intro n hnLower hnUpper
  by_cases hn : n ≤ 469615
  · exact Computation.smallBq_representation n hnLower hn
  · exact firstWindow_bridge_representation n (by omega) hnUpper

end Pntpp.DivisorPrefix
