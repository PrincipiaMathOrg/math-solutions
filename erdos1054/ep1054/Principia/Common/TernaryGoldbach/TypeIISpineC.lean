/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIISpine

set_option autoImplicit false

/-!
# The Type II spine with the `eq:passi` ERRATUM absorbed: `H₂` admissible ADDITIVELY

**Finding (refereed 2026-10-03, independent, faithful transcription checked; reproduced this
round by `scratchpad/menson_ref.py`).** `eq:passi` at `v = 2` is FALSE: the true supremum of
`(∫_1^T G₂(S) dS/S)/log T` is `0.39691` at `T ≈ 8.15`, above the printed `0.37273` for every
`T ≳ 3.4`. Hence `eq:velib` (`∫_1^T H₂(s) ds/s ≤ 0.15107 log T` for all `T ≥ 1`) is false for
Helfgott's `H₂ = (4/π²)G₂` (below `16`), and `T2S.Menson2` — which asks for ONE `H` with `T2S.HOk H`
that also bounds every `S₁` — is unsatisfiable. Every `T2S` theorem stays PROVED (each takes
`Menson2` or `HOk` as a hypothesis), but the chain through `Menson2` is dead.

**The fix that keeps the zero-slack main term: ADDITIVE.** With `H₂ = (4/π²)G₂` on `[1, 16]` and
`0.15107` above (Helfgott's own splice), `∫_1^T H₂/s − 0.15107 log T` peaks at `0.023051` at
`T = 16` and is constant beyond; so `∫_1^T H₂(s) ds/s ≤ 0.15107 log T + 0.0231` for all `T ≥ 1`
(`HOkC`). In `eq:quartma` (`minarctotals.tex` 681-686) the extra `β⁻¹·0.0231` joins
`eq:curious`'s `β⁻¹κ₇/2`, i.e. `κ₇ ↦ κ₇ + 2·0.0231 = 0.1743` (`kap7C`); `κ₆ = 0.60428` and the
`x^{5/6}` terms are untouched.

```
 HOkC        H₂ admissible with the additive 0.0231                         (DEFINITION)
 Menson2C    eq:menson2 with HOkC                                     DEEP; OPEN (named)
 Vin1CalcC   the vinland1 calculus, conclusion vin1C (κ₇ ↦ 0.1743)            ANALYSIS
 ErikCalcC   the eriksaga calculus, conclusion erikC                          ANALYSIS
 SecIICalcC  the second choice with HOkC, conclusion still 0.34x^{5/6}(log x)^{3/2}   OPEN
 vinland1AtC_of, eriksagaAtC_of, secIIAtC_of            PROVED (application, as in T2S)
 menson2C_of : Menson2 → Menson2C                           PROVED (HOkC is weaker than HOk)
```

**`SecIICalcC` keeps `0.34`.** At the second choice `eq:quan`'s first line carries
`κ₆t/3 − 4.214`; the erratum adds `4·0.0231 = 0.0924`, raising that line by `≤ 0.69%` at
`t = log(3.4·10²³)` (less above), i.e. `0.275964 ↦ ≤ 0.2779`, inside the `0.34` that `SecIIAt`
was loosened to (the module finding of `TypeIISpine` costs a further `≈ 0.024`). Scoping, not
certified; `SecIICalcC` is OPEN as `SecIICalc` was.
-/

namespace Principia.Common.TernaryGoldbach.T2SC

open MeasureTheory
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
open Principia.Common.TernaryGoldbach.T2S

/-- **`H₂` admissible, the erratum form**: `0 ≤ H₂ ≤ 2/π²` (`eq:demimond`), integrable, and
`∫_1^T H₂(s) ds/s ≤ 0.15107 log T + 0.0231` for every `T ≥ 1` (`eq:velib` corrected). -/
def HOkC (H : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 1 ≤ s → 0 ≤ H s ∧ H s ≤ 2 / Real.pi ^ 2) ∧
    (∀ T : ℝ, 1 ≤ T → IntervalIntegrable H volume 1 T) ∧
      ∀ T : ℝ, 1 ≤ T → ∫ s in (1 : ℝ)..T, H s / s ≤ 0.15107 * Real.log T + 0.0231

/-- `HOk` (the printed `eq:velib`) implies `HOkC`. -/
theorem hOkC_of_hOk (H : ℝ → ℝ) (h : HOk H) : HOkC H :=
  ⟨h.1, h.2.1, fun T hT => (h.2.2 T hT).trans (by linarith)⟩

/-- **Link [Menson2C] — `eq:menson2` with the corrected `eq:velib`**: one `H₂` with `HOkC` bounds
every `S₁(U, W)`. DEEP (`lem:monro`, `lem:yutto`, `eq:corto`, `eq:crusto`; the computations
`HC.YuttoSmallCited`, `HC.RamareCited`, `HC.OdmalickaCited`, `HC.CortoC0Cited`,
`HC.CortoSmallCited`); OPEN. -/
def Menson2C : Prop :=
  ∃ H : ℝ → ℝ, HOkC H ∧
    ∀ x U W : ℝ, 1 ≤ U → 1 ≤ W → U * W ≤ x → S1Bd H x U W (s1 x U W)

/-- `Menson2 → Menson2C` (the corrected link is weaker). -/
theorem menson2C_of (h : Menson2) : Menson2C := by
  obtain ⟨H, hH, hm⟩ := h
  exact ⟨H, hOkC_of_hOk H hH, hm⟩

/-- `κ₇ + 2·0.0231 = 0.1743`: `eq:curious`'s `κ₇ = 0.1281` plus the erratum's additive term. -/
noncomputable def kap7C : ℝ := 0.1743

/-- **`eq:vinland1` at the corrected `κ₇`** (`MPc.vin1` with `kap7 ↦ kap7C`). -/
noncomputable def vin1C (x U V : ℝ) (q : ℕ) : ℝ :=
  x / Real.sqrt (2 * Nat.totient q) *
      Real.sqrt ((Real.log (x / (U * V)) + Real.log (2 * q) *
          Real.log (1 + Real.log (x / (U * V)) / Real.log (V / (2 * q)))) *
        (kap6 * Real.log (x / (U * V)) + 2 * kap7C)) +
    Real.sqrt 2 * kap2 * Real.sqrt ((q : ℝ) / Nat.totient q) *
      (1 + 1.15 * Real.sqrt (Real.log (2 * q) / Real.log (x / (2 * U * q)))) * (x / Real.sqrt U) +
    kap9 * (x / Real.sqrt V)

/-- **`eq:eriksaga` at the corrected `κ₇`** (`MPc.erik` with `kap7 ↦ kap7C`). -/
noncomputable def erikC (x U V Q δ : ℝ) (q : ℕ) : ℝ :=
  2 * x / Real.sqrt (|δ| * Nat.totient q) *
      Real.sqrt (Real.log (x / (U * V)) + Real.log (|δ| * q * (1 + x / (2 * U * Q)) / 4) *
        Real.log (1 + Real.log (x / (U * V)) /
          Real.log (4 * V / (|δ| * (1 + x / (2 * U * Q)) * q)))) *
      Real.sqrt (kap6 * Real.log (x / (U * V)) + 2 * kap7C) +
    kap2 * Real.sqrt (2 * q / Nat.totient q) *
      Real.sqrt (Real.log V / Real.log (2 * V / (|δ| * q))) * (x / Real.sqrt U) +
    kap9 * (x / Real.sqrt V)

/-- **Link [Vinland1AtC] — `eq:vinland1` at the first choice, corrected `κ₇`.** OPEN (as
`MPc.Vinland1At`). -/
def Vinland1AtC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sII Y α (uA Y δ q) (vA Y)‖ ≤ vin1C Y (uA Y δ q) (vA Y) q

/-- **Link [EriksagaAtC] — `eq:eriksaga` at the first choice, corrected `κ₇`.** OPEN. -/
def EriksagaAtC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    8 ≤ |δ| →
      ‖sII Y α (uA Y δ q) (vA Y)‖ ≤ erikC Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q

/-- **Link [Vin1CalcC]** — `T2S.Vin1Calc` with `HOkC` for `HOk` and `vin1C` for `vin1`. -/
def Vin1CalcC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ∀ H s1f s2f s3f : ℝ → ℝ, HOkC H →
      PtBds Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q H s1f s2f s3f →
        4 * ∫ W in (vA Y)..(Y / uA Y δ q), secI s1f s2f s3f W ≤ vin1C Y (uA Y δ q) (vA Y) q

/-- **Link [ErikCalcC]** — `T2S.ErikCalc` with `HOkC` for `HOk` and `erikC` for `erik`. -/
def ErikCalcC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → 8 ≤ |δ| → ∀ H s1f s2f s3f : ℝ → ℝ, HOkC H →
      PtBds Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q H s1f s2f s3f →
        4 * ∫ W in (vA Y)..(Y / uA Y δ q), secI s1f s2f s3f W ≤
          erikC Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q

/-- **Link [SecIICalcC]** — `T2S.SecIICalc` with `HOkC` for `HOk`, conclusion unchanged (`0.34`;
module note). OPEN. -/
def SecIICalcC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y →
    |δ / Y| ≤ 1 / (q * q2 Y) →
    (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) →
      ∀ H s1f s2f s3f : ℝ → ℝ, HOkC H → PtBds Y (u2 Y) (v2 Y) (q2 Y) δ q H s1f s2f s3f →
        4 * ∫ W in (v2 Y)..(Y / u2 Y), secI s1f s2f s3f W ≤
          0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2)

/-- **`Vinland1AtC` from its links, PROVED** (`T2S.vinland1At_of` verbatim, `Menson2C`). -/
theorem vinland1AtC_of (hs : SecInt) (hm : Menson2C) (hk : Kraken) (hc : HC.KastCited)
    (hl : KastLarge) (h13 : EB.RS62Thm13) (hv : Vin1CalcC) : Vinland1AtC := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy
  obtain ⟨H, hH, hm⟩ := hm
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hU := uA_ge_one Y δ q hY hq hdq hy
  have hUV := uA_mul_vA Y δ q hY hq hdq hy
  have hV := vA_ge Y hY
  refine (hs Y α (uA Y δ q) (vA Y) hY0 (by linarith) (by linarith) (by linarith)).trans ?_
  exact hv Y hY δ q hq hdq hy H _ _ _ hH
    (ptBds_of H hm hk hc hl h13 Y α _ _ _ δ a q hY0 hU hV hq hg h2 hδ hQ)

/-- **`EriksagaAtC` from its links, PROVED.** -/
theorem eriksagaAtC_of (hs : SecInt) (hm : Menson2C) (hk : Kraken) (hc : HC.KastCited)
    (hl : KastLarge) (h13 : EB.RS62Thm13) (he : ErikCalcC) : EriksagaAtC := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy h8
  obtain ⟨H, hH, hm⟩ := hm
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hU := uA_ge_one Y δ q hY hq hdq hy
  have hUV := uA_mul_vA Y δ q hY hq hdq hy
  have hV := vA_ge Y hY
  refine (hs Y α (uA Y δ q) (vA Y) hY0 (by linarith) (by linarith) (by linarith)).trans ?_
  exact he Y hY δ q hq hdq hy h8 H _ _ _ hH
    (ptBds_of H hm hk hc hl h13 Y α _ _ _ δ a q hY0 hU hV hq hg h2 hδ hQ)

/-- **`MPc.SecIIAt` from the corrected links, PROVED.** -/
theorem secIIAtC_of (hs : SecInt) (hm : Menson2C) (hk : Kraken) (hc : HC.KastCited)
    (hl : KastLarge) (h13 : EB.RS62Thm13) (h2c : SecIICalcC) : SecIIAt := by
  intro Y hY α δ a q hadm
  obtain ⟨hq, hg, h2, hqQ, hδ, hcase⟩ := hadm
  obtain ⟨H, hH, hm⟩ := hm
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hU, hV, hVU, -⟩ := second_facts Y hY
  refine (hs Y α (u2 Y) (v2 Y) hY0 (by linarith) (by linarith) hVU).trans ?_
  exact h2c Y hY δ q hq hqQ hδ hcase H _ _ _ hH
    (ptBds_of H hm hk hc hl h13 Y α _ _ _ δ a q hY0 hU hV hq hg h2 hδ hqQ)

end Principia.Common.TernaryGoldbach.T2SC
