/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Common.PNT.PiAP

set_option autoImplicit false

/-!
# EP1054: the prime number theorem inputs — the `InputsPNT` package of the spine

Discharges, for `Principia.Erdos1054.Spine` (paper `Campaigns/Erdos-1054/collab-paper/EP1054.tex`),
the prime-number-theorem inputs of `Principia.Erdos1054.Statements.Inputs`, from the PNT+ port
`Principia.Common.PNT` (PrimeNumberTheoremAnd d963a6e: Wiener–Ikehara, `WeakPNT`, `WeakPNT_AP`)
and Principia's `π`-form bridge `Principia.Common.PNT.PiAP`. Nothing here is new mathematics.

* `input_Std_PNT_AP` — `Std_PNT_AP` (trusted input, section (2) of `Inputs.lean`): for every
  `Q ≥ 1`, `π(x; Q, Q − 1) · log x / x → 1/φ(Q)`. This is
  `Principia.Common.PNT.tendsto_primeCountingAP_mul_log_div` at `a = Q − 1`, which is coprime to
  `Q` (`coprime_pred_self`; for `Q = 1` it is `gcd 0 1 = 1`); `piAP x Q (Q − 1)` unfolds to
  exactly the count used there (`Finset.Iic ⌊x⌋₊`, `p % Q = (Q − 1) % Q`).
* `input_Std_PNT` — `Std_PNT` (derived input, section (4)): `ψ(x)/x → 1`, which is
  `Principia.Common.PNT.tendsto_psi_div_self` verbatim. (It is also `link_Std_PNT
  input_Std_PNT_AP` via `Proofs.InputsStd`; the direct route avoids that import.)
-/

namespace Principia.Erdos1054.Proofs.InputsPNT

open Filter Topology

/-- `Q − 1` is coprime to `Q` for `Q ≥ 1` (for `Q = 1`: `gcd 0 1 = 1`). -/
lemma coprime_pred_self {Q : ℕ} (hQ : 1 ≤ Q) : (Q - 1).Coprime Q :=
  (Nat.coprime_self_sub_left hQ).2 (Nat.coprime_one_left Q)

/-- **`Std_PNT_AP`**: the prime number theorem in arithmetic progressions, class `−1`, fixed
modulus `Q ≥ 1`, in the paper's `π`-form. -/
theorem input_Std_PNT_AP : Principia.Erdos1054.Std_PNT_AP := by
  intro Q hQ
  exact Principia.Common.PNT.tendsto_primeCountingAP_mul_log_div hQ (coprime_pred_self hQ)

/-- **`Std_PNT`**: the prime number theorem `ψ(x)/x → 1`. -/
theorem input_Std_PNT : Principia.Erdos1054.Std_PNT :=
  Principia.Common.PNT.tendsto_psi_div_self

end Principia.Erdos1054.Proofs.InputsPNT
