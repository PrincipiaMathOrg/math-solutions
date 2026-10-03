/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Common.LucaPomerance.Lemma25

set_option autoImplicit false

/-!
# EP1054: Luca–Pomerance Lemma 2.5 — the `InputsLP25` package

Discharges `Principia.Erdos1054.Cite_LP_Lemma25` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, `lem:LP-inputs` final assertion, lines 1331–1334,
and `eq:sv-LP25`, in the corrected **prime-divisor** form recorded in the input's docstring):

`∃ E, DensZero E ∧ ∀ n ∉ E, ∑_{r ∣ σ(n), r prime, r > (log log n)^2} 1/r ≤ 1`.

The exceptional set is the obvious one, `E = {n : the sum exceeds 1}`; its density is zero by
`Principia.Common.LucaPomerance.Lemma25.lp_lemma25_density` (the campaign-agnostic proof: first
moment of the large-prime reciprocal sum, Brun–Titchmarsh in dyadic blocks, Markov). The bridge is
definitional: `logIt 2 x = log (log x)` and `sig = σ 1` unfold by `rfl`, and `⌊(X : ℝ)⌋₊ = X`.
-/

namespace Principia.Erdos1054.Proofs.InputsLP25

open Filter
open scoped Topology

/-- The exceptional set of `Cite_LP_Lemma25`: the `n` whose large-prime reciprocal sum exceeds
`1`. -/
def lp25Exc : Set ℕ :=
  {n | 1 < ∑ r ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 (n : ℝ)) ^ 2 < (r : ℝ)),
    (1 : ℝ) / r}

/-- The library's `lpSum` is the sum in `Cite_LP_Lemma25`, definitionally. -/
theorem lpSum_eq (n : ℕ) : Principia.Common.LucaPomerance.Lemma25.lpSum n =
    ∑ r ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 (n : ℝ)) ^ 2 < (r : ℝ)),
      (1 : ℝ) / r := rfl

/-- The paper's counting function of `lp25Exc` at an integer `X` is the library's count. -/
theorem cnt_lp25Exc (X : ℕ) :
    cnt lp25Exc (X : ℝ) =
      ((Finset.Icc 1 X).filter
        (fun n => 1 < Principia.Common.LucaPomerance.Lemma25.lpSum n)).card := by
  unfold cnt
  rw [Nat.floor_natCast]
  congr 1

/-- `lp25Exc` has density zero. -/
theorem densZero_lp25Exc : DensZero lp25Exc := by
  unfold DensZero HasDens
  refine (Principia.Common.LucaPomerance.Lemma25.lp_lemma25_density).congr (fun X => ?_)
  rw [cnt_lp25Exc]

end Principia.Erdos1054.Proofs.InputsLP25

namespace Principia.Erdos1054.Proofs

/-- **`Cite_LP_Lemma25`**, discharged: outside the density-zero set `lp25Exc`,
`∑_{r ∣ σ(n), r prime, r > (log log n)^2} 1/r ≤ 1`. -/
theorem input_Cite_LP_Lemma25 : Principia.Erdos1054.Cite_LP_Lemma25 :=
  ⟨InputsLP25.lp25Exc, InputsLP25.densZero_lp25Exc, fun n hn => by
    simp only [InputsLP25.lp25Exc, Set.mem_setOf_eq, not_lt] at hn
    exact hn⟩

end Principia.Erdos1054.Proofs
