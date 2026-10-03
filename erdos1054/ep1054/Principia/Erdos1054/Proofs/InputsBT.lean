/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Common.Sieve.BrunTitchmarshAP

set_option autoImplicit false

/-!
# EP1054: the Brun–Titchmarsh input — the `InputsBT` package of the spine

Discharges `Principia.Erdos1054.Std_BrunTitchmarsh` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, `prop:sv-second-moment`, lines 1788–1815: the
reciprocal prime sums over progressions to moduli `q₀h ≤ X^{10/33} log X < X^{7/20−ε₀}`):

`∃ C, ∀ m a, 1 ≤ m → Coprime a m → ∀ x > m, π(x; m, a) ≤ C x / (φ(m) log (x/m))`.

It is proved for **every** modulus `1 ≤ m < x` — not only the paper's range — with `C = 2008`,
and without using `Coprime a m` (`brunTitchmarsh_2008`). The proof is
`Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap`: Selberg's Λ² sieve (ported from PNT+ into
`Principia/Common/Sieve/`) applied to the progression `{n ≤ x : n ≡ a (mod m)}`, sifting the
primes `p ≤ √(x/m)` with `p ∤ m`. Nothing here is new mathematics: this is the textbook sieve
proof of Brun–Titchmarsh (Montgomery–Vaughan obtain the constant `2`).

`piAP x m a` is by definition the card that `brun_titchmarsh_ap` bounds, so the bridge is `rfl`.
-/

namespace Principia.Erdos1054.Proofs.InputsBT

/-- `Std_BrunTitchmarsh` with the explicit constant `2008`, for every residue `a` (coprimality
with the modulus is not needed for this upper bound). -/
theorem brunTitchmarsh_2008 (m a : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : (m : ℝ) < x) :
    (Principia.Erdos1054.piAP x m a : ℝ) ≤ 2008 * x / ((m.totient : ℝ) * Real.log (x / m)) :=
  Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap m a hm x hx

end Principia.Erdos1054.Proofs.InputsBT

namespace Principia.Erdos1054.Proofs

/-- **`Std_BrunTitchmarsh`**, discharged with `C = 2008`. -/
theorem input_Std_BrunTitchmarsh : Principia.Erdos1054.Std_BrunTitchmarsh :=
  ⟨2008, fun m a hm _ x hx => InputsBT.brunTitchmarsh_2008 m a hm x hx⟩

end Principia.Erdos1054.Proofs
