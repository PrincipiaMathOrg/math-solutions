import Pntpp.DivisorPrefix.Bq
import Pntpp.DivisorPrefix.SmallValues

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
