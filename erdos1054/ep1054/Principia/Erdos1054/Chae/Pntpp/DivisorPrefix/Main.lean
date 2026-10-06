/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Main.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Bq
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.SmallValues

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

theorem targetClassification_of_six_le
    (hlarge : ∀ n : ℕ, 6 ≤ n → Represents n) :
    TargetClassification := by
  intro n hn
  constructor
  · intro hrep
    constructor
    · intro hnTwo
      subst n
      exact not_represents_two hrep
    · intro hnFive
      subst n
      exact not_represents_five hrep
  · rintro ⟨hnTwo, hnFive⟩
    by_cases hlargeN : 6 ≤ n
    · exact hlarge n hlargeN
    · have hnUpper : n ≤ 5 := by omega
      interval_cases n
      · exact represents_one
      · exact (hnTwo rfl).elim
      · exact represents_three
      · exact represents_four
      · exact (hnFive rfl).elim

end Pntpp.DivisorPrefix
