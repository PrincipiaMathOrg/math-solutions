import Pntpp.DivisorPrefix.GoldbachTail
import Pntpp.DivisorPrefix.LargeBridge
import Pntpp.DivisorPrefix.Main
import Pntpp.DivisorPrefix.RangeCoverage

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
