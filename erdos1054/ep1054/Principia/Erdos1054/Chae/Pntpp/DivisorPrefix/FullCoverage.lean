/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/FullCoverage.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.GoldbachTail
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.LargeBridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Main
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.RangeCoverage

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

/-- The computed initial range, explicit PNT+ bridge, and conditional Goldbach tail cover every
integer from six onward. -/
theorem represents_six_le_of_helfgott [DusartBounds] (hgoldbach : HelfgottTailHypothesis) :
    ∀ n : ℕ, 6 ≤ n → Represents n := by
  intro n hn
  by_cases hsmall : n ≤ 178813826
  · exact represents_six_to_firstWindowBridge n hn hsmall
  by_cases hbridge : n ≤ 1000000000000000000100000000
  · apply largeSeed_explicitBridge_representation n
      ((by norm_num : 105000001 ≤ 178813827).trans
        (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hsmall))) hbridge
  · apply represents_goldbach_tail hgoldbach n
    have htail : 10 ^ 27 + 10 ^ 8 = 1000000000000000000100000000 := by norm_num
    omega

/-- Conditional final classification for the Erdos 1054 divisor-prefix problem. -/
theorem targetClassification_of_helfgott [DusartBounds] (hgoldbach : HelfgottTailHypothesis) :
    TargetClassification :=
  targetClassification_of_six_le (represents_six_le_of_helfgott hgoldbach)

end Pntpp.DivisorPrefix
