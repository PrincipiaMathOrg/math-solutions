/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Aliquot.Certificate
import Principia.Erdos1054.Alt.Unconditional
import Principia.Erdos1054.Alt5.Round5

set_option autoImplicit false

/-!
# EP1054 round 6: `Cite_ChenZhao` proved

`input_Cite_ChenZhao : Cite_ChenZhao` is the input **exactly as stated** in
`Statements/Inputs.lean`:
```
0.0602757 ≤ lowerDens {N : ℕ | ∀ m : ℕ, 1 ≤ m → aliquot m ≠ N}.
```
It comes from the campaign-agnostic `Principia.Common.Aliquot.untouchable_count_ge` (eventually
`0.0604 X ≤ #{N ≤ X untouchable}`), which is Chen–Zhao's Theorem 1 (Publ. Math. Debrecen 78
(2011) 439–442) proved in Lean for every modulus (`Common/Aliquot/Main.lean`) and evaluated at
the modulus `2^7 · 3^5 · 5^4 · 7^3 · 11^2 · 13 ⋯ 59` by a kernel-checked rounded computation
(`Common/Aliquot/Certificate.lean`). The proof in fact gives `0.0604 ≤ lowerDens`
(`lowerDens_untouchable_ge`); the input's constant `0.0602757` follows.

The set is the same as `Coverage.untouchable` and as `Common.Aliquot.Untouchable` (`aliquot` and
`aliq` are both `σ(m) − m` with Mathlib's `σ`), by `rfl`.

Consequences (the input's sole consumer is `Link_Coverage_Step_EvenUntouchables`):
* `ep1054_Prop_ThetaTwo_unconditional : Prop_ThetaTwo` (#241) and
  `ep1054_Cor_EtaTwo_unconditional : Cor_EtaTwo` (#243), with no hypothesis;
* `ep1054_all_r6 : 6 inputs → Spine.DerivedClaims` — `Alt5.Round5.ep1054_all_r5` with
  `Cite_ChenZhao` supplied.
-/

namespace Principia.Erdos1054.Alt6.ChenZhao

open Principia.Erdos1054 Filter

/-- The input's set is `Common.Aliquot.Untouchable`. -/
theorem untouchable_eq :
    {N : ℕ | ∀ m : ℕ, 1 ≤ m → aliquot m ≠ N} = Principia.Common.Aliquot.Untouchable := rfl

/-- **The untouchable numbers have lower density `≥ 0.0604`.** -/
theorem lowerDens_untouchable_ge :
    (0.0604 : ℝ) ≤ lowerDens {N : ℕ | ∀ m : ℕ, 1 ≤ m → aliquot m ≠ N} := by
  obtain ⟨X₀, hX₀⟩ := Principia.Common.Aliquot.untouchable_count_ge
  apply le_lowerDens_of_eventually
  filter_upwards [eventually_ge_atTop X₀] with n hn
  have h := hX₀ n hn
  unfold cnt
  rw [Nat.floor_natCast, untouchable_eq]
  convert h using 3

/-- **`Cite_ChenZhao`, exactly as stated in `Statements/Inputs.lean`.** -/
theorem input_Cite_ChenZhao : Principia.Erdos1054.Cite_ChenZhao := by
  unfold Cite_ChenZhao
  have h := lowerDens_untouchable_ge
  have h' : (0.0602757 : ℝ) ≤ 0.0604 := by norm_num
  exact h'.trans h

/-- **EP1054 `prop:theta-two` (#241), unconditionally**: `Alt.ep1054_Prop_ThetaTwo_r3` at
`input_Cite_ChenZhao`.

**Remaining hypotheses: none.** (Rounds 3–5: `Cite_ChenZhao`.) -/
theorem ep1054_Prop_ThetaTwo_unconditional : Principia.Erdos1054.Prop_ThetaTwo :=
  Principia.Erdos1054.Alt.ep1054_Prop_ThetaTwo_r3 input_Cite_ChenZhao

/-- **EP1054 `Cor_EtaTwo` (#243), unconditionally**: `Alt.ep1054_Cor_EtaTwo_r3` at
`input_Cite_ChenZhao`.

**Remaining hypotheses: none.** (Rounds 3–5: `Cite_ChenZhao`.) -/
theorem ep1054_Cor_EtaTwo_unconditional : Principia.Erdos1054.Cor_EtaTwo :=
  Principia.Erdos1054.Alt.ep1054_Cor_EtaTwo_r3 input_Cite_ChenZhao

/-- **All of EP1054** (`Spine.DerivedClaims`) from **6** trusted inputs:
`Alt5.Round5.ep1054_all_r5` with `Cite_ChenZhao` supplied by `input_Cite_ChenZhao`.

**Remaining hypotheses (6):** `Cite_Helfgott_weighted`, `Cite_Dusart_Thm69`, `Cite_Axler_Cor2`,
`Comp_Verifier_small`, `Comp_Verifier_window1`, `Comp_Verifier_largeSeed`. -/
theorem ep1054_all_r6
    (i_Cite_Helfgott_weighted : Cite_Helfgott_weighted)
    (i_Cite_Dusart_Thm69 : Cite_Dusart_Thm69)
    (i_Cite_Axler_Cor2 : Cite_Axler_Cor2)
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1)
    (i_Comp_Verifier_largeSeed : Comp_Verifier_largeSeed) :
    Spine.DerivedClaims :=
  Principia.Erdos1054.Alt5.Round5.ep1054_all_r5 i_Cite_Helfgott_weighted i_Cite_Dusart_Thm69
    i_Cite_Axler_Cor2 input_Cite_ChenZhao i_Comp_Verifier_small i_Comp_Verifier_window1
    i_Comp_Verifier_largeSeed

end Principia.Erdos1054.Alt6.ChenZhao
