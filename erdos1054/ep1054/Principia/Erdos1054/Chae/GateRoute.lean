/-
Copyright (c) 2026 PrincipiaAI. Released under the Apache License, Version 2.0.
-/
import Principia.Erdos1054.Chae.Route

set_option autoImplicit false

/-!
# Axiom gate for `Principia/Erdos1054/Chae/Route.lean`

Every declaration of `Route.lean`: Hyunsik Chae's `erdos1054_conditional` (his `Solution.lean`,
ported), the three definitional identifications with `Bridge.lean`, the two Rosser--Schoenfeld
literature hypotheses (definitions), `dusartBounds_of_rs62`, and the closed `chae_route_closed`.
Acceptance: each reads `[propext, Classical.choice, Quot.sound]` or a subset.
(Kept separate from `Gate.lean`, which audits `Bridge.lean`; the coverage checker reads every
`Gate*.lean` in the directory.)
-/

#print axioms Pntpp.DivisorPrefix.erdos1054_conditional
#print axioms Principia.Erdos1054.Chae.pntpp_represents_iff
#print axioms Principia.Erdos1054.Chae.pntpp_target_iff
#print axioms Principia.Erdos1054.Chae.pntpp_helfgott_iff
#print axioms Principia.Erdos1054.Chae.Cite_RS62_Eq35
#print axioms Principia.Erdos1054.Chae.Cite_RS62_Eq36
#print axioms Principia.Erdos1054.Chae.dusartBounds_of_rs62
#print axioms Principia.Erdos1054.Chae.chae_route_closed
