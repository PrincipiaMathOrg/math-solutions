import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

/-!
# PNT+ port: `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean`

Ported from PrimeNumberTheoremAnd (PNT+, Kontorovich-Tao et al., Apache 2.0), file
`PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` at commit d963a6e694a05cd82e5f9b9ae7f4d94123e85393
(built there against Mathlib db127794; here against the Mathlib v4.31.0 tag).
Port changes: LeanArchitect `@[blueprint ...]` attributes removed (titles and statements
kept as docstrings), `blueprint_comment` turned into module docstrings, imports of
`PrimeNumberTheoremAnd.*` rewired to `Principia.Common.PNT.*`.  Declaration names and
namespaces are unchanged.

Outside the closure of `WeakPNT_AP` / `WeakPNT` (computed in the PNT+ environment) and dropped here: `isLittleO_const_id_cocompact`, `isLittleO_const_id_atTop2`, `isLittleO_const_id_atBot2`, `Filter.Eventually.natCast`.

Contents: `Asymptotics.IsBigO.natCast`.
-/

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']



-- to replace existing `isLittleO_const_id_atTop`

-- to replace existing `isLittleO_const_id_atBot`


theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics
