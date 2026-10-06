import Pntpp.DivisorPrefix.Computation.SmallBq
import Pntpp.DivisorPrefix.FirstWindowBridge

namespace Pntpp.DivisorPrefix

theorem represents_six_to_firstWindowBridge :
    ∀ n, 6 ≤ n → n ≤ 178813826 → Represents n := by
  intro n hnLower hnUpper
  by_cases hn : n ≤ 469615
  · exact Computation.smallBq_representation n hnLower hn
  · exact firstWindow_bridge_representation n (by omega) hnUpper

end Pntpp.DivisorPrefix
