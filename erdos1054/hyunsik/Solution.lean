import Pntpp.DivisorPrefix.FullCoverage

namespace Pntpp.DivisorPrefix

/-- The precise advertised conditional theorem. -/
theorem erdos1054_conditional (dusart : DusartBounds) (helfgott : HelfgottTailHypothesis) :
    TargetClassification := by
  letI := dusart
  exact targetClassification_of_helfgott helfgott

end Pntpp.DivisorPrefix
