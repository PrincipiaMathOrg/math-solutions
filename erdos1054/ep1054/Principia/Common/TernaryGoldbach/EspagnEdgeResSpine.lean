/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeResNum

set_option autoImplicit false

/-!
# `EE.EspagnEdgeRes`: the spine (four regimes in `q`, composed by case analysis)

`EE.EspagnEdgeRes` (`EspagnEdgeCover.lean`) asks for `eq:luce` at the real point `R = ϖ(q)` for
every checked `q` with `1 < ϖ(q) < λ(q)`, `ϖ(q)` not an integer, where neither analytic cover
holds. It is closed here by ANALYSIS plus a finite EXACT case split, with no computation over the
moduli: the residue's hypotheses force `q` into one of four regimes, and each regime either
proves the inequality or contradicts one of the hypotheses.

```
 q < 70000, ϖ(q) < 3        RegWin  the inequality itself, uniformly        (ER.regWin)
 q < 70000, ϖ(q) ≥ 3        RegA    Cover A holds  — contradicts ¬CoverA    (ER.regA)
 70000 ≤ q < 1.2·10¹⁰       RegB    Cover B holds  — contradicts ¬CoverB    (ER.regB)
 1.2·10¹⁰ ≤ q < 2.2·10¹⁰    RegL    λ(q) ≤ ϖ(q)   — contradicts ϖ < λ      (ER.regL)
```

`q ≥ 1.2·10¹⁰` in the checked range forces `q < 2.2·10¹⁰` (the range is `q < 3.3·10⁹` or
`q < 2.2·10¹⁰ ∧ 210 ∣ q`); Regime L holds there for every `q`, so `210 ∣ q` is not even used.
`edgeRes_of_regimes` is the composition.
-/

namespace Principia.Common.TernaryGoldbach.ER

open Principia.Common.TernaryGoldbach.HC (omegaE kappaE lambdaE varpiE errE)

/-- The residue's conclusion at `q`: `eq:luce` at `R = ϖ(q)` with the `tR`-term of
`eq:agammen`. -/
def ResIneq (q : ℕ) : Prop :=
  errE q (varpiE q) + omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤
    (q.totient : ℝ) / q * kappaE q

/-- **Regime W** — below `70000` with `ϖ(q) < 3` the inequality holds outright. -/
def RegWin : Prop :=
  ∀ q : ℕ, 1 ≤ q → q < 70000 → 1 < varpiE q → varpiE q < 3 → ResIneq q

/-- **Regime A** — below `70000` with `ϖ(q) ≥ 3`, Cover A holds. -/
def RegA : Prop := ∀ q : ℕ, 1 ≤ q → q < 70000 → 3 ≤ varpiE q → EE.CoverA q

/-- **Regime B** — on `[70000, 1.2·10¹⁰)` with `ϖ(q) > 1`, Cover B holds. -/
def RegB : Prop := ∀ q : ℕ, 70000 ≤ q → (q : ℝ) < 1.2e10 → 1 < varpiE q → EE.CoverB q

/-- **Regime L** — on `[1.2·10¹⁰, 2.2·10¹⁰)`, `λ(q) ≤ ϖ(q)` (for every `q` there; the residue only
reaches this range with `210 ∣ q`). -/
def RegL : Prop :=
  ∀ q : ℕ, (1.2e10 : ℝ) ≤ q → (q : ℝ) < 2.2e10 → lambdaE q ≤ varpiE q

/-- **`EE.EspagnEdgeRes` from the four regimes.** -/
theorem edgeRes_of_regimes (w : RegWin) (a : RegA) (b : RegB) (l : RegL) :
    EE.EspagnEdgeRes := by
  intro q hq hr _ hv1 hvl hA hB
  rcases Nat.lt_or_ge q 70000 with h7 | h7
  · rcases lt_or_ge (varpiE q) 3 with h3 | h3
    · exact w q hq h7 hv1 h3
    · exact absurd (a q hq h7 h3) hA
  · rcases lt_or_ge (q : ℝ) 1.2e10 with hQ | hQ
    · exact absurd (b q h7 hQ hv1) hB
    · have h2 : (q : ℝ) < 2.2e10 := by
        rcases hr with h | h
        · exact absurd h (by linarith)
        · exact h.1
      exact absurd (l q hQ h2) (not_le.mpr hvl)

end Principia.Common.TernaryGoldbach.ER
