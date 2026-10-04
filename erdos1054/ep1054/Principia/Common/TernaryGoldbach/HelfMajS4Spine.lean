/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajBandRep
import Principia.Common.TernaryGoldbach.HelfgottCited

set_option autoImplicit false

/-!
# S4 — the saddle-point bound for `F_δ`, as a spine to `HM.PhiDecay` and `HM.PlusDecay`

`F_δ(w) = ∫₀^∞ e^{−t²/2} e(δt) t^{w−1} dt` (`Fd`, majarcs §3). `HM.PhiDecay` is a bound on
`F_δ(s + 2)` and `HM.PlusDecay` one on `(1/2π)∫_{−200}^{200} A(r) F_δ(s + 1 + ir) dr`
(`HP.mellin_hH_mul`). This file names the pieces and composes them; **application only**.

## The route (not Helfgott's; his `thm:princo` is not reproduced)

1. **`RayBound`** (the only complex analysis): rotate the contour of `F_δ` to the ray
   `arg t = ∓θ`, `0 < θ < π/4` (a strip shift in log coordinates). On the ray
   `|e^{−t²/2}e(δt)t^{w−1}| ≤ e^{−|τ|θ} r^{σ−1} e^{−cos(2θ) r²/2 + 2π|δ| sin(θ) r}` for every sign
   of `τ`, `δ` — no "easy sign" case is needed.
2. **`Moment1`, `Moment2`**: the real ray integral `∫₀^∞ r^m e^{−cr²/2 + br} dr` bounded by
   completing the square, Bernoulli (`r^m ≤ (1−m) + mr`, resp. `r·((2−m) + (m−1)r)`) and the
   Gaussian moments `√(2π/c)`, `2/c`, `√(2π/c)/c`.
3. **`Cases2`, `Cases1`**: the choice of ray. With `D = π²δ²`, `ρ = |τ|/D`:
   * `ρ < 1.35`: the ray `θ = 0.19ρ` (`sin θ ≤ θ`, `cos 2θ ≥ 1 − 2θ²`): exponent `≥ 0.1065ρ|τ|`;
   * `ρ ≥ 1.35` (also `δ = 0`): the FIXED ray `θ₁ = arccos(1/υ(1.5))/2`, whose exponent is
     `θ₁ − (υ₁ − 1)/ρ = E(1.5) + (υ₁ − 1)(2/3 − 1/ρ)` EXACTLY (`cos 2θ₁ = 1/υ₁`,
     `sin²θ₁/cos 2θ₁ = (υ₁ − 1)/2`); `E(1.5) ≥ 0.1598` is the second conjunct of the CITED
     `HC.AmanitaBisectCited`. That gives `≥ 0.1598|τ|` for `ρ ≥ 1.5`, and `≥ 0.1065ρ|τ|` on
     `[1.35, 1.5)` by a quadratic inequality in `ρ`. The bisection conjunct on `[1.19, 1.5]` is NOT
     used.
   Constants (`scratchpad/s4/consts.py`): `k = 2` needs `2.687 ≤ 3.262` (Helfgott's `c₂`); `k = 1`
   needs `3.042 ≤ 3.1` (`f1`).
4. **`PhiShift`**: `G_δ^φ(s) = F_δ(s + 2)`.
5. **`AC0`, `AC1`, `AC2`, `AIntOf`**: `|A(r)| ≤ min(2.03, 3.2975/|r|, 10.7920/r²)`
   (`C₀ = 92e^{−1/2} − 12e^{3/2}`, `C₁ = 2e^{1/2}`, `C₂ = ∫|h''|t ≤ 10.79195821038`, the latter
   CITED from `HC.AppBCited`), so `∫_{−200}^{200}|A| ≤ 18.2` (the truth with these constants is
   `17.70`).
6. **`PlusBand`**: `|G_δ^{η₊}(s)| ≤ (1/2π)·18.2·f1(|τ| − 200) ≤ fplus` by monotonicity of `f1`.
-/

namespace Principia.Common.TernaryGoldbach.S4

open MeasureTheory Set

/-- **`F_δ(w)`**: the Mellin transform of `e^{−t²/2} e(δt)` (majarcs §3, `thm:princo`). -/
noncomputable def Fd (δ : ℝ) (w : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * Principia.Common.Goldbach.e (δ * t)) w

/-- The real ray integral `∫₀^∞ r^m e^{−cr²/2 + br} dr`. -/
noncomputable def rayInt (m c b : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (-(c * t ^ 2) / 2 + b * t)

/-- **LINK [RayBound]** — the contour rotation: for `Re w > 0`, `0 < θ < π/4`,
`|F_δ(w)| ≤ e^{−|Im w|θ} ∫₀^∞ r^{Re w − 1} e^{−cos(2θ)r²/2 + 2π|δ| sin(θ) r} dr`. -/
def RayBound : Prop :=
  ∀ (δ : ℝ) (w : ℂ) (θ : ℝ), 0 < w.re → 0 < θ → θ < Real.pi / 4 →
    ‖Fd δ w‖ ≤ Real.exp (-(|w.im| * θ)) *
      rayInt (w.re - 1) (Real.cos (2 * θ)) (2 * Real.pi * |δ| * Real.sin θ)

/-- `√(2π/c)`, the Gaussian width. -/
noncomputable def gw (c : ℝ) : ℝ := Real.sqrt (2 * Real.pi / c)

/-- **LINK [Moment2]** — for `m ∈ [1, 2]`, `c > 0`, `b ≥ 0`, with `r₀ = b/c`:
`rayInt m c b ≤ e^{b²/2c}((2 − m)(r₀√(2π/c) + 2/c) + (m − 1)(r₀²√(2π/c) + √(2π/c)/c))`. -/
def Moment2 : Prop :=
  ∀ m c b : ℝ, 1 ≤ m → m ≤ 2 → 0 < c → 0 ≤ b →
    rayInt m c b ≤ Real.exp (b ^ 2 / (2 * c)) *
      ((2 - m) * (b / c * gw c + 2 / c) + (m - 1) * ((b / c) ^ 2 * gw c + gw c / c))

/-- **LINK [Moment1]** — for `m ∈ [0, 1]`, `c > 0`, `b ≥ 0`:
`rayInt m c b ≤ e^{b²/2c}((1 − m)√(2π/c) + m(r₀√(2π/c) + 2/c))`. -/
def Moment1 : Prop :=
  ∀ m c b : ℝ, 0 ≤ m → m ≤ 1 → 0 < c → 0 ≤ b →
    rayInt m c b ≤ Real.exp (b ^ 2 / (2 * c)) * ((1 - m) * gw c + m * (b / c * gw c + 2 / c))

/-- **`S4` at `k = 2`** — `cor:amanita1`'s bound on `F_δ(s + 2)`, with Helfgott's `c₂ = 3.262` and
the two cases SUMMED (`HM.fphi`). -/
def Decay2 : Prop :=
  ∀ (δ : ℝ) (w : ℂ), 2 < w.re → w.re < 3 → 100 ≤ |w.im| → 4 * Real.pi ^ 2 * |δ| ≤ |w.im| →
    ‖Fd δ w‖ ≤ HM.fphi δ |w.im|

/-- The `k = 1` decay, `3.1·(√T e^{−0.1598T} + (T/2π|δ|) e^{−0.1065(T/πδ)²})` (`c₁ = 3.516` is
Helfgott's; `3.1` is what this route's moments need, so `|A|₁` may be `18.2`). -/
noncomputable def f1 (δ T : ℝ) : ℝ :=
  3.1 * (Real.sqrt T * Real.exp (-0.1598 * T) +
    T / (2 * Real.pi * |δ|) * Real.exp (-0.1065 * (T / (Real.pi * δ)) ^ 2))

/-- **`S4` at `k = 1`** — the bound on `F_δ(s + 1 + ir)`. -/
def Decay1 : Prop :=
  ∀ (δ : ℝ) (w : ℂ), 1 < w.re → w.re < 2 → 100 ≤ |w.im| → 4 * Real.pi ^ 2 * |δ| ≤ |w.im| →
    ‖Fd δ w‖ ≤ f1 δ |w.im|

/-- **LINK [Cases2]** — the choice of ray at `k = 2` (real-variable numerics only). -/
def Cases2 : Prop := HC.AmanitaBisectCited → RayBound → Moment2 → Decay2

/-- **LINK [Cases1]** — the choice of ray at `k = 1`. -/
def Cases1 : Prop := HC.AmanitaBisectCited → RayBound → Moment1 → Decay1

/-- **LINK [PhiShift]** — `G_δ^φ(s) = F_δ(s + 2)`, so `Decay2` is `HM.PhiDecay`. -/
def PhiShift : Prop := Decay2 → HM.PhiDecay

/-- **LINK [AC0]** — `|A(r)| ≤ ∫₀² h(u)du/u = 92e^{−1/2} − 12e^{3/2} ≤ 2.03`. -/
def AC0 : Prop := ∀ r : ℝ, ‖HP.Ah r‖ ≤ 2.03

/-- **LINK [AC1]** — one integration by parts: `|r||A(r)| ≤ ∫₀²|h'| = 2e^{1/2} ≤ 3.2975`. -/
def AC1 : Prop := ∀ r : ℝ, ‖HP.Ah r‖ * |r| ≤ 3.2975

/-- **LINK [AC2]** — two integrations by parts: `r²|A(r)| ≤ ∫₀²|h''(u)|u du = C₂`, with
`C₂ ≤ 10.79195821038` the CITED `HC.AppBCited`. -/
def AC2 : Prop := HC.AppBCited → ∀ r : ℝ, ‖HP.Ah r‖ * r ^ 2 ≤ 10.792

/-- **`|A|₁ ≤ 18.2` on `[−200, 200]`**. -/
def AInt : Prop := ∫ r in (-200 : ℝ)..200, ‖HP.Ah r‖ ≤ 18.2

/-- **LINK [AIntOf]** — integrating `min(2.03, 3.2975/|r|, 10.792/r²)` over `[−200, 200]`
(split at `1.6`, `3.2`): `2(2.03·1.6 + 3.2975 log 2 + 10.792(1/3.2 − 1/200)) ≤ 17.71`. -/
def AIntOf : Prop := AC0 → AC1 → (∀ r : ℝ, ‖HP.Ah r‖ * r ^ 2 ≤ 10.792) → AInt

/-- **LINK [PlusBand]** — `HP.mellin_hH_mul`, `Decay1` at `s + 1 + ir`, `|A|₁ ≤ 18.2`, and the
monotonicity of `f1` in `T ≥ |τ| − 200`: `18.2·3.1/2π ≤ 9.062`. -/
def PlusBand : Prop := Decay1 → AInt → HM.PlusDecay

/-- **`HM.PhiDecay` FROM THE S4 LINKS** (citation: `E(1.5) ≥ 0.1598`). Application only. -/
theorem phiDecay_of_links (hc : HC.AmanitaBisectCited) (hR : RayBound) (hM : Moment2)
    (hK : Cases2) (hS : PhiShift) : HM.PhiDecay :=
  hS (hK hc hR hM)

/-- **`HM.PlusDecay` FROM THE S4 LINKS** (citations: `E(1.5) ≥ 0.1598`, `C₂`). Application
only. -/
theorem plusDecay_of_links (hc : HC.AmanitaBisectCited) (hb : HC.AppBCited) (hR : RayBound)
    (hM : Moment1) (hK : Cases1) (h0 : AC0) (h1 : AC1) (h2 : AC2) (hI : AIntOf)
    (hB : PlusBand) : HM.PlusDecay :=
  hB (hK hc hR hM) (hI h0 h1 (h2 hb))

end Principia.Common.TernaryGoldbach.S4
