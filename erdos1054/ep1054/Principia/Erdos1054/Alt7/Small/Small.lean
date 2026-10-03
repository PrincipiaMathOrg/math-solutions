/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Alt7.Small.Cert
import Principia.Erdos1054.Proofs.ReprElementary

set_option autoImplicit false

/-!
# `eq:fraiture-small` without `Comp_Verifier_small`

The spine proves `Eq_FraitureSmall` (EP1054 lines 728–755, every `N ∈ [6, 10^7]` is represented)
by `Link_Eq_FraitureSmall`, whose binders are the leaves `Step_FraitureSmallBq`,
`Step_FraitureSeven` and the trusted input `Comp_Verifier_small` (check 1 of `verify.rs`, a
sieve through `10^7`). Here the input is replaced:

* on `[6, 469 615]` by the kernel certificate of `Cert.lean` (`smallSieveMarked_le`: check 1
  itself on that range);
* on `[469 616, 10^7]` by `Eq_FraitureFirstWindow` (`[469 616, 273 803 744 799 154] ⊆ 𝓡`), a
  conclusion of the spine that does not depend on `Eq_FraitureSmall`
  (`Link_Eq_FraitureFirstWindow` takes `Step_FraitureFirstWindowCover` and
  `Lem_FraiturePrimeWindow` only).

* **`mem_R_le_469615 : ∀ N, 6 ≤ N → N ≤ 469615 → N ∈ R`** — no hypothesis.
* **`eq_FraitureSmall_of_firstWindow : Eq_FraitureFirstWindow → Eq_FraitureSmall`** — the one
  remaining hypothesis is the second interval of `prop:fraiture-finite`. So `Eq_FraitureSmall`
  is unconditional as soon as `Eq_FraitureFirstWindow` is, and `Comp_Verifier_small` leaves the
  paper once the assembly uses this theorem in place of the `v_Eq_FraitureSmall` step.
-/

namespace Principia.Erdos1054.Alt7.Small

open Principia.Erdos1054 Principia.Erdos1054.Proofs

/-- **Every `N ∈ [6, 469 615]` is represented**, unconditionally: `mem_R_le_of_leaves` at the
spine's leaves `leaf_Step_FraitureSmallBq`, `leaf_Step_FraitureSeven`.

**Remaining hypotheses: none.** -/
theorem mem_R_le_469615 : ∀ N : ℕ, 6 ≤ N → N ≤ 469615 → N ∈ R :=
  mem_R_le_of_leaves leaf_Step_FraitureSmallBq leaf_Step_FraitureSeven

/-- **EP1054 `eq:fraiture-small` (`Eq_FraitureSmall`) without `Comp_Verifier_small`**: every
`N ∈ [6, 10^7]` is represented, given the first prime window.

**Remaining hypothesis:** `Eq_FraitureFirstWindow`. (Rounds 1–6: `Comp_Verifier_small`.) -/
theorem eq_FraitureSmall_of_firstWindow (hW : Eq_FraitureFirstWindow) : Eq_FraitureSmall :=
  eq_FraitureSmall_of_leaves leaf_Step_FraitureSmallBq leaf_Step_FraitureSeven hW

end Principia.Erdos1054.Alt7.Small
