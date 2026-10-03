/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Density
import Principia.Common.LucaPomerance.Lemma21

set_option autoImplicit false

/-!
# EP1054: Luca–Pomerance Lemma 2.1 — the `InputsLP21` package of the spine

Discharges `Principia.Erdos1054.Cite_LP_Lemma21` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, `lem:LP-inputs` (i)–(iv), lines 1317–1325):
outside a set of density zero, with `y = y(n) = log log n / log log log n`,
(i) `v_p(n) < v_p(σ(n))` for every prime `p ≤ y`; (ii) `gcd(n, σ(n))` is `y`-smooth;
(iii) every prime `p ≤ y` divides `σ(n)/gcd(n, σ(n))`; (iv) `s(n)/gcd(n, σ(n))` is `y`-rough.

This is a bridge: the mathematics is `Principia.Common.LucaPomerance.LP21.lucaPomerance_lemma21`,
stated there with `σ₁` and an explicit counting form of density zero. The identifications are
definitional (`yLP = lpY`, `sig = σ₁`, `aliquot n = σ₁ n − n`, `IsSmooth`/`IsRough` unfold to the
Common conclusions), and `cnt E N` is the counted `Finset` by `cnt_natCast`.
Nothing here is new mathematics: Luca–Pomerance, Acta Arith. 168 (2015), Lemma 2.1; the plan of
the proof is `Campaigns/Erdos-1054/LP21-PLAN.md`.
-/

namespace Principia.Erdos1054.Proofs

open Principia.Common.LucaPomerance.LP21

/-- The paper's `y(n)` is the Common `lpY n`. -/
theorem yLP_eq_lpY (n : ℕ) : yLP n = lpY n := rfl

/-- **`Cite_LP_Lemma21`** (Luca–Pomerance 2015, Lemma 2.1), proved. -/
theorem input_Cite_LP_Lemma21 : Principia.Erdos1054.Cite_LP_Lemma21 := by
  obtain ⟨E, hE, hpt⟩ := lucaPomerance_lemma21
  refine ⟨E, ?_, fun n hn => hpt n hn⟩
  rw [densZero_iff_eventually_le]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hE ε hε
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  rw [cnt_natCast]
  exact hN₀ N hN

end Principia.Erdos1054.Proofs
