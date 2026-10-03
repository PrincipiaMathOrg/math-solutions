/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorSpine

set_option autoImplicit false

/-!
# `RegW`: `prop:nefumo` without the vestigial `η₊ ∈ C²`, `η₊'' ∈ L²`

`MajSp.Reg` transcribes the hypotheses of `prop:nefumo` verbatim (`ternvin.tex` 1614–1618). Two of
them — `η₊ ∈ C²` on `[0,∞)` and `η₊'' ∈ L²` — are **false for Helfgott's own `η₊`** (coordinator,
`scratchpad/eta2nd.py`: near `0`, `t|log t|·|η₊''| ≈ 6·10⁻³` and `∫|η₊''|²` diverges), so every
theorem taking `MajSp.Reg HW.etaPlus …` could never be discharged.

**They are vestigial in the source — checked by reading `prop:nefumo`'s live proof** (§3,
`ternvin.tex` 966–1676, Lean agent 2026-09-29). `η₊` enters that proof only through:
* `|η₊ − η∘|₂` and Plancherel (`eq:pommes`, 1078–1098) — `η₊ ∈ L²`;
* `|η̂*|_∞ ≤ |η*|₁` and `|η̂*|₂ = |η*|₂` (`eq:pommes`, `eq:thaddeus`) — `η* ∈ L¹ ∩ L²`;
* `B₊ = 2.82643|η₊|₂²` and `A_{η₊}` via `eq:bfpink`/`eq:mardi` (`lem:drujal`, whose own hypotheses
  are `η ∈ L¹ ∩ L^∞` — no derivative), and the `LS`, `Z` sums of `eq:joko`.
Every derivative in the live text is of `η∘` (`eq:madge` at `k = 3`, 1130–1142, 1366–1374). The
only occurrences of `η₊''` (1154, 1158, 1188, 1192) are in COMMENTED-OUT blocks (an earlier version
bounded the completion error with `|η₊''|₁`; the live text replaced it by the `η∘` device). Line
1615 states the hypothesis and nothing consumes it.

So `NefumoW := RegW → NefumoBody` is what the live proof establishes, and it is STRONGER than
`MajSp.Nefumo` (`nefumo_of_W`) — the weakening of the hypothesis is faithful, not a relaxation.

**GENERATED** (`scratchpad/integ/gen_regw.py`): `RegW`'s body is `MajSp.Reg`'s from its third
conjunct on and `NefumoBody` is `MajSp.Nefumo`'s after `Reg ηp ηs ηo → `, both cut from
`MajorSpine.lean` by exact anchors; `reg_iff` (`Iff.rfl`) and `nefumo_pin` (`rfl`) check that the
kernel sees the same propositions.

`RegW` constrains (`regW_const_one`: the constant `1` is not in `L¹(0,∞)`); it is DISCHARGED on
Helfgott's weights in `RegWHelf.lean`.
-/

namespace Principia.Common.TernaryGoldbach.RW

open MeasureTheory Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.MajSp

/-- **`prop:nefumo`'s hypotheses as its live proof uses them**: `MajSp.Reg` without `η₊ ∈ C²` and
`η₊'' ∈ L²` — `η₊, η* ∈ L¹ ∩ L²`, `η∘` thrice differentiable off finitely many points, `η∘''' ∈ L¹`,
`η∘ ∈ L²`. The text is `MajSp.Reg`'s, verbatim (`reg_iff`). -/
def RegW (ηp ηs ηo : ℝ → ℝ) : Prop :=
  MemLp ηp 1 (volume.restrict (Set.Ioi 0)) ∧ MemLp ηp 2 (volume.restrict (Set.Ioi 0)) ∧
    MemLp ηs 1 (volume.restrict (Set.Ioi 0)) ∧ MemLp ηs 2 (volume.restrict (Set.Ioi 0)) ∧
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) ∧
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) ∧
    MemLp ηo 2 (volume.restrict (Set.Ioi 0))

/-- **`MajSp.Nefumo`'s conclusion**, verbatim: the text after `Reg ηp ηs ηo → ` (`nefumo_pin`). -/
def NefumoBody (ηp ηs ηo : ℝ → ℝ) : Prop :=
  ∀ ε₀ : ℝ, 0 ≤ ε₀ → l2 (fun t => ηp t - ηo t) < ε₀ * l2 ηo →
    ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      ∀ Ep Es : ℝ, EBound ηp x Ep → EBound ηs x Es →
        ∀ Lp Ls : ℝ, LSBound ηp x Lp → LSBound ηs x Ls →
          ‖(∫ α in Smooth.majorSet x, Smooth.kernS ηp ηs N x α) -
              ((SingularSeries.sing3 N * ccon ηo ηs (N / x) * x ^ 2 : ℝ) : ℂ)‖ ≤
            (2.82643 * l2 ηo ^ 2 * (2 + ε₀) * ε₀ +
                (4.31004 * l2 ηo ^ 2 + 0.0012 * l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) / 150000) *
              l1 ηs * x ^ 2 +
            (Es * amaj ηp x + Ep * 1.6812 * (Real.sqrt (amaj ηp x) + 1.6812 * l2 ηp) * l2 ηs) *
              x ^ 2 +
            (2 * zk (fun t => ηp t ^ 2) 2 x * Ls +
                4 * Real.sqrt (zk (fun t => ηp t ^ 2) 2 x * zk (fun t => ηs t ^ 2) 2 x) * Lp) * x

/-- **Link [nefumo], faithful to the live proof**: `RegW → NefumoBody`. OPEN (Helfgott's
`prop:nefumo`); stronger than `MajSp.Nefumo` (`nefumo_of_W`). -/
def NefumoW (ηp ηs ηo : ℝ → ℝ) : Prop := RegW ηp ηs ηo → NefumoBody ηp ηs ηo

/-- **`MajSp.Reg` IS the two dropped conjuncts plus `RegW`**, by `Iff.rfl`: the generator removed
exactly those two and nothing else. -/
theorem reg_iff (ηp ηs ηo : ℝ → ℝ) : MajSp.Reg ηp ηs ηo ↔
    (ContDiffOn ℝ 2 ηp (Set.Ici 0) ∧
      MemLp (iteratedDeriv 2 ηp) 2 (volume.restrict (Set.Ioi 0)) ∧ RegW ηp ηs ηo) :=
  Iff.rfl

/-- **THE PIN: `MajSp.Nefumo` is `MajSp.Reg → NefumoBody`**, by `rfl`. -/
theorem nefumo_pin (ηp ηs ηo : ℝ → ℝ) :
    MajSp.Nefumo ηp ηs ηo = (MajSp.Reg ηp ηs ηo → NefumoBody ηp ηs ηo) :=
  rfl

/-- `Reg → RegW`: drop the two `η₊` smoothness conjuncts. -/
theorem regW_of_reg (ηp ηs ηo : ℝ → ℝ) (rg : MajSp.Reg ηp ηs ηo) : RegW ηp ηs ηo :=
  rg.2.2

/-- **`NefumoW → MajSp.Nefumo`**: the faithful link is the stronger one. -/
theorem nefumo_of_W (ηp ηs ηo : ℝ → ℝ) (h : NefumoW ηp ηs ηo) : MajSp.Nefumo ηp ηs ηo :=
  fun rg => h (regW_of_reg ηp ηs ηo rg)

/-- **`RegW` constrains**: the constant weight `1` is not in `L¹(0,∞)`, so `RegW (fun _ => 1) 0 0`
fails (its first conjunct). -/
theorem regW_const_one : ¬ RegW (fun _ => (1 : ℝ)) 0 0 := by
  intro h
  have h1 := memLp_one_iff_integrable.mp h.1
  rcases integrable_const_iff.mp h1 with h0 | hf
  · exact one_ne_zero h0
  · have hlt := hf.measure_univ_lt_top
    rw [Measure.restrict_apply_univ, Real.volume_Ioi] at hlt
    exact lt_irrefl _ hlt

end Principia.Common.TernaryGoldbach.RW
