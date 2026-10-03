/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Common.Sieve.TwoDim

set_option autoImplicit false

/-!
# EP1054: the two-dimensional sieve input — the `InputsLPSieve` package of the spine

Discharges `Principia.Erdos1054.Cite_LP_sieve37` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, `prop:sv-second-moment`, lines 1588–1618: the
upper-bound sieve for the prime pairs `p = p₀ + A₂ t`, `p' = p₀' + A₁ t`, "in the form used in
[LP, (3.7)]", i.e. Halberstam–Richert, *Sieve Methods*, Theorem 2.2 for two linear forms):

for coprime `a₁, a₂ ≥ 1`, `D = a₁ b₂ − a₂ b₁ ≠ 0`, every `u ∈ ℤ` and every real `T ≥ 2`,
`#{t ∈ [u, u + ⌊T⌋] : a₁ t + b₁, a₂ t + b₂ both prime}
  ≤ C · T/(log T)² · a₁/φ(a₁) · a₂/φ(a₂) · |D|/φ(|D|)`.

It is proved with `C = 2^28` by `Principia.Common.TwoDimSieve.two_dim_sieve`: Selberg's Λ² sieve
(the PNT+ port in `Principia/Common/Sieve/`) applied to the values `|(a₁ t + b₁)(a₂ t + b₂)|`,
sifting the odd primes `p ≤ √T` with the density `ν(p) = ρ(p)/p`, where `ρ(p) ∈ {1, 2}` is the
number of roots modulo `p` (computed in `ZMod p`; multiplicative by the Chinese remainder theorem).
The main term is bounded below by a product of two harmonic sums, one of them avoiding the primes of
`2 a₁ a₂ |D|`; this gives the singular-series factor to the first power. A form `a t + b` with
`gcd(a, b) > 1` takes at most one prime value, which is the degenerate case. Nothing here is new
mathematics: this is the textbook sieve proof of Halberstam–Richert Theorem 2.2 for `g = 2`.
-/

namespace Principia.Erdos1054.Proofs

/-- **`Cite_LP_sieve37`**, discharged with `C = 2^28`. -/
theorem input_Cite_LP_sieve37 : Principia.Erdos1054.Cite_LP_sieve37 :=
  ⟨2 ^ 28, fun a₁ a₂ b₁ b₂ ha₁ ha₂ hcop hD u T hT =>
    Principia.Common.TwoDimSieve.two_dim_sieve a₁ a₂ b₁ b₂ ha₁ ha₂ hcop hD u T hT⟩

end Principia.Erdos1054.Proofs
