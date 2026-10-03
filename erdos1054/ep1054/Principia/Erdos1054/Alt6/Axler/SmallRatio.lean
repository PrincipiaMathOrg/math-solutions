/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.SmallRatio
import Principia.Common.SmallAbundancy.TenBound

set_option autoImplicit false

/-!
# EP1054 line 1156 without Axler: `f(n) ≤ n/10 ⟹ n > 10^{120}`, unconditionally

The spine proves `Prop_SmallRatioThreshold` (EP1054.tex lines 1156–1181) by
`Link_Prop_SmallRatioThreshold`, whose binders are `SmallRatio_prefixLeSig`,
`SmallRatio_abundancySmall`, `SmallRatio_axlerNumeric` and the trusted input `Cite_Axler_Cor2`
(Axler's explicit Robin-type bound `σ(m)/m < (1 + 3.15367·10⁻⁷) e^γ log log m`). The proof uses
Axler and the numeric evaluation together for one thing only: `σ(m)/m < 10` on
`5040 < m ≤ 10^{119}` (`SmallRatio_abundancyMid` below; `abundancyMid_of_axler` shows the pair
gives exactly that). That statement is now a theorem of the library,
`Principia.Common.SmallAbundancy.sigma_div_lt_ten` (`σ(m)/m < 10` for all `1 ≤ m ≤ 10^{119}`,
from the colossally-abundant bound at `ε = 1/1480`, all arithmetic exact and kernel-checked), so
the link is re-proved with the pair replaced by it.

* `abundancy_lt_ten_of_le` — `σ(m)/m < 10` for `1 ≤ m ≤ 10^{119}`, in EP1054's `abundancy`.
* `SmallRatio_abundancyMid`, `smallRatio_abundancyMid` — the consumer's need, and its proof.
* `abundancyMid_of_axler` — the replaced pair implies it (the replacement attaches: nothing
  stronger than what the consumer used is being supplied).
* `link_Prop_SmallRatioThreshold_ofMid` — the spine link with (`SmallRatio_axlerNumeric`,
  `Cite_Axler_Cor2`) replaced by `SmallRatio_abundancyMid`; the rest of the argument is the
  library's (`Proofs.link_Prop_SmallRatioThreshold`).
* **`ep1054_Prop_SmallRatioThreshold_unconditional : Prop_SmallRatioThreshold`** — no hypothesis.
* `link_Prop_SmallRatioThreshold_noAxler : Spine.Link_Prop_SmallRatioThreshold` — the spine's link
  type, inhabited without using its `Cite_Axler_Cor2` binder.

**Remaining hypotheses of `ep1054_Prop_SmallRatioThreshold_unconditional`: none.** (Rounds 1–5:
`Cite_Axler_Cor2`.) `Cite_Axler_Cor2` has no other consumer, so it leaves the paper once the
capstone assembly is regenerated with this theorem in place of the `v_Prop_SmallRatioThreshold`
step.
-/

namespace Principia.Erdos1054.Alt6.Axler

open Principia.Erdos1054 Principia.Erdos1054.Proofs

/-- **`σ(m)/m < 10` for every `1 ≤ m ≤ 10^{119}`** (`Common.SmallAbundancy.sigma_div_lt_ten`). -/
theorem abundancy_lt_ten_of_le : ∀ m : ℕ, 1 ≤ m → m ≤ 10 ^ 119 → abundancy m < 10 := by
  intro m hm hmX
  show ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) / (m : ℝ) < 10
  exact Principia.Common.SmallAbundancy.sigma_div_lt_ten hm hmX

/-- What the proposition at EP1054.tex line 1156 takes from Axler's bound and the numeric
evaluation (lines 1172–1178): `σ(m)/m < 10` for `5040 < m ≤ 10^{119}`. -/
def SmallRatio_abundancyMid : Prop :=
  ∀ m : ℕ, 5040 < m → m ≤ 10 ^ 119 → abundancy m < 10

/-- `SmallRatio_abundancyMid`, proved (`abundancy_lt_ten_of_le`). -/
theorem smallRatio_abundancyMid : SmallRatio_abundancyMid :=
  fun m hm hmX => abundancy_lt_ten_of_le m (by omega) hmX

/-- The pair the spine uses (`SmallRatio_axlerNumeric`, `Cite_Axler_Cor2`) gives
`SmallRatio_abundancyMid`: the paper's own derivation, lines 1172–1178. -/
theorem abundancyMid_of_axler (hNum : SmallRatio_axlerNumeric) (hAx : Cite_Axler_Cor2) :
    SmallRatio_abundancyMid := by
  intro m hbig hm119
  have hA := hAx m hbig hm119
  have hm1r : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlogpos : 0 < Real.log m := Real.log_pos hm1r
  have hmle : (m : ℝ) ≤ (10 : ℝ) ^ 119 := by exact_mod_cast hm119
  have hlog : Real.log m ≤ Real.log ((10 : ℝ) ^ 119) := Real.log_le_log (by positivity) hmle
  have hloglog : Real.log (Real.log m) ≤ Real.log (Real.log ((10 : ℝ) ^ 119)) :=
    Real.log_le_log hlogpos hlog
  have hcpos : (0 : ℝ) ≤ (1 + 3.15367e-7) * Real.exp eulerGamma := by positivity
  calc abundancy m
      < (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log m) := hA
    _ ≤ (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log ((10 : ℝ) ^ 119)) :=
        mul_le_mul_of_nonneg_left hloglog hcpos
    _ ≤ 9.99745 := hNum
    _ < 10 := by norm_num

/-- **EP1054.tex lines 1156–1181, re-proved**: `Link_Prop_SmallRatioThreshold` with
(`SmallRatio_axlerNumeric`, `Cite_Axler_Cor2`) replaced by `SmallRatio_abundancyMid`. The
argument is `Proofs.link_Prop_SmallRatioThreshold`'s: `n ≤ σ(f(n))` and `10 f(n) ≤ n` give
`σ(f(n))/f(n) ≥ 10`, while `n ≤ 10^{120}` gives `f(n) ≤ 10^{119}`. -/
theorem link_Prop_SmallRatioThreshold_ofMid (hPre : SmallRatio_prefixLeSig)
    (hSmall : SmallRatio_abundancySmall) (hMid : SmallRatio_abundancyMid) :
    Principia.Erdos1054.Prop_SmallRatioThreshold := by
  intro n hn hf
  have hmem : f n ∈ {m | 1 ≤ m ∧ IsRep n m} := Nat.sInf_mem hn
  have hm1 : 1 ≤ f n := hmem.1
  have hle : n ≤ sig (f n) := hPre n (f n) hmem.2
  have hmpos : (0 : ℝ) < f n := by exact_mod_cast hm1
  have h10 : (10 : ℝ) * f n ≤ n := by
    have := hf
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)] at this
    linarith
  have hab : 10 ≤ abundancy (f n) := by
    rw [abundancy, le_div_iff₀ hmpos]
    have : (n : ℝ) ≤ sig (f n) := by exact_mod_cast hle
    linarith
  by_contra hcon
  have hn120 : n ≤ 10 ^ 120 := Nat.le_of_not_lt hcon
  have h10n : 10 * f n ≤ n := by exact_mod_cast h10
  have hm119 : f n ≤ 10 ^ 119 := by
    have h : 10 * f n ≤ 10 * 10 ^ 119 := by
      calc 10 * f n ≤ n := h10n
        _ ≤ 10 ^ 120 := hn120
        _ = 10 * 10 ^ 119 := by norm_num
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  rcases Nat.lt_or_ge 5040 (f n) with hbig | hsmall
  · have := hMid (f n) hbig hm119
    linarith
  · have := hSmall (f n) hm1 hsmall
    linarith

/-- **EP1054, the proposition at line 1156 (`Prop_SmallRatioThreshold`), unconditionally**: if
`n ∈ 𝓡` and `f(n) ≤ n/10` then `n > 10^{120}`. From `link_Prop_SmallRatioThreshold_ofMid` with
`Proofs.leaf_SmallRatio_prefixLeSig`, `Proofs.leaf_SmallRatio_abundancySmall` and
`smallRatio_abundancyMid`.

**Remaining hypotheses: none.** (Rounds 1–5: `Cite_Axler_Cor2`.) -/
theorem ep1054_Prop_SmallRatioThreshold_unconditional :
    Principia.Erdos1054.Prop_SmallRatioThreshold :=
  link_Prop_SmallRatioThreshold_ofMid leaf_SmallRatio_prefixLeSig leaf_SmallRatio_abundancySmall
    smallRatio_abundancyMid

/-- The spine's link type `Link_Prop_SmallRatioThreshold`, inhabited without using any of its four
binders (in particular not `Cite_Axler_Cor2`). A drop-in for `Proofs.link_Prop_SmallRatioThreshold`
in a regenerated assembly; the assembly must still stop *passing* `Cite_Axler_Cor2` to it. -/
theorem link_Prop_SmallRatioThreshold_noAxler : Spine.Link_Prop_SmallRatioThreshold :=
  fun _ _ _ _ => ep1054_Prop_SmallRatioThreshold_unconditional

end Principia.Erdos1054.Alt6.Axler
