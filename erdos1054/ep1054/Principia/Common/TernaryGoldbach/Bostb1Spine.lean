/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Bosta2Spine
import Principia.Common.TernaryGoldbach.MinGen

set_option autoImplicit false

/-!
# `MPG.Bostb1Eta2` spined to the three pieces of the proof of `lem:bostb1`

`lem:bostb1` (book `typeI.tex` 1153-1478) bounds `S_{I,1} = ∑_{m ≤ D odd} μ(m) T^{log}_{m,∘}(α)`,
`T^{log}_{m,∘}(α) = ∑_{n odd} (log n) e(αmn)η₂(mn/x)`. Its proof (1223-1478) is `lem:bosta2`'s
with `η` replaced by `η_{(x/m)}(t) = log(xt/m)η(t)` and `eq:puella` at `ρ = x/m`:

```
 Bostb1Eta2 ← TrompaisLogEta2  the per-m estimate (1279-1295): log(x/m) × eq:trompais,
                               for d ≤ x/4 (ρ = x/d ≥ ρ₀ = 4); owes eq:puella for η₂
            ← MainLogEta2      the m odd, q | m, m ≤ M terms (1231-1277) ≤ mainI1(M) + errI1(D),
                               the main term CORRECTED (x/2q, −δ/2, (m, 2q) = 1; finding T6)
            ← EsthelLogEta2    eq:esthel2 in the eq:kuche2 branch (1399-1466), for ANY T obeying
                               the per-m estimate: eq:bobo, eq:bocio, eq:binbed (lem:thina,
                               lem:couscous, lem:gotog)
            sI1_split, sI1_le : PROVED;  bostb1Eta2_of : PROVED (application, M = MPB2.mR)
```

`eq:puella`'s first two parts hold for `η₂` at every `ρ ≥ 4` (`log(ρt) ∈ [0, log ρ]` on
`supp η₂ = [1/4, 1]`, and `log(ρt)η₂(t)` is unimodal with peak at most `log ρ·max η₂`); its third
part, `|η̂₂_{(ρ)}''|_∞ ≤ c₀ log ρ` at `c₀ = 31.521`, is NOT justified by the printed argument (the
`eq:cloclo` route is too weak at that `c₀`) and needs its own proof: it is the analytic content of
`TrompaisLogEta2`, together with Poisson / `eq:ra` / `lem:areval`.
-/

namespace Principia.Common.TernaryGoldbach.MPB1

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPB2

/-! ## (1) The inner sum and the decomposition, PROVED -/

/-- **`T^{log}_{d,∘}(α) = ∑_{m odd} (log m) e(αdm)η₂(dm/x)`**, truncated at `dm ≤ x`. -/
noncomputable def tlo (x α : ℝ) (d : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / d), ((Real.log m * fOdd m : ℝ) : ℂ) * wt x α (d * m)

/-- **`S_{I,1} = ∑_{d ≤ x} μ_{≤D}(d)f(d)·T^{log}_{d,∘}(α)`, PROVED.** -/
theorem sI1_split (x α D : ℝ) :
    sI1 x α D = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ((aU D d * fOdd d : ℝ) : ℂ) * tlo x α d := by
  unfold sI1
  rw [sP_mul_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [tw_apply]
  congr 1

/-- **`|S_{I,1}| ≤ |∑_{P} μ f T^{log}| + ∑_{d ≤ D, ¬P} |T^{log}_{d,∘}|`, PROVED.** -/
theorem sI1_le (x α D : ℝ) (P : ℕ → Prop) [DecidablePred P] (hDx : D ≤ x) :
    ‖sI1 x α D‖ ≤
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter P, ((aU D d * fOdd d : ℝ) : ℂ) * tlo x α d‖ +
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d), ‖tlo x α d‖ := by
  rw [sI1_split]
  exact split_le x D (tlo x α) P hDx

/-! ## (2) The three links -/

/-- **Link [TrompaisLogEta2] — the per-`m` estimate of `lem:bostb1`** (book `typeI.tex`
1279-1295): for `x > 0`, `1 ≤ d ≤ x/4`, `|T^{log}_{d,∘}(γ)| ≤ log(x/d)·min(x/2d + |η₂'|₁/2,
(|η₂'|₁/2)/|sin 2πdγ|, (d/x)(c₀/2)/sin²2πdγ)`, the last two written multiplicatively. Sources:
`eq:ra`, `lem:areval`, and `eq:puella` for `η₂` at `ρ = x/d ≥ 4` (third part: own proof owed,
see the module doc). OPEN. -/
def TrompaisLogEta2 : Prop :=
  ∀ x γ : ℝ, 0 < x → ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ x / 4 →
    ‖tlo x γ d‖ ≤ Real.log (x / d) * (x / (2 * d) + eta1 / 2) ∧
      ‖tlo x γ d‖ * |Real.sin (2 * Real.pi * d * γ)| ≤ Real.log (x / d) * (eta1 / 2) ∧
      ‖tlo x γ d‖ * Real.sin (2 * Real.pi * d * γ) ^ 2 ≤ Real.log (x / d) * (d / x * (c0 / 2))

/-- **Link [MainLogEta2] — the main term of `lem:bostb1`, CORRECTED** (book `typeI.tex`
1231-1277 with `x/2q`, `−δ/2`, `(m, 2q) = 1`): under `lem:bostb1`'s hypotheses, the terms
`m` odd, `q ∣ m`, `m ≤ M = mR` sum to at most `mainI1 x δ q M + errI1 x q D`. (Poisson for
`η_{(x/m)}` per `m = qm'`; zero frequency `(x/2m)(\widehat{log·η₂}(−δ/2) + log(x/m)η̂₂(−δ/2))`;
the nonzero frequencies `(m/x)log(x/m)(c₀/2π²)(π² − 4)`, valid as `|δm/x| ≤ 1/2q`; `t log(x/t)`
increasing on `t ≤ x/e`.) OPEN. -/
def MainLogEta2 : Prop :=
  ∀ x α δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.sqrt 3 ≤ D → D ≤ x / 4 →
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q D),
          ((aU D d * fOdd d : ℝ) : ℂ) * tlo x α d‖ ≤
        mainI1 x δ q (mR x δ q D) + errI1 x q D

/-- **`T` obeys the per-`m` estimate of `lem:bostb1` at `γ`** (with `T ≥ 0`), for `d ≤ x/4`. -/
def TromLB (x γ : ℝ) (T : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ x / 4 → 0 ≤ T d ∧
    (T d ≤ Real.log (x / d) * (x / (2 * d) + eta1 / 2) ∧
      T d * |Real.sin (2 * Real.pi * d * γ)| ≤ Real.log (x / d) * (eta1 / 2) ∧
      T d * Real.sin (2 * Real.pi * d * γ) ^ 2 ≤ Real.log (x / d) * (d / x * (c0 / 2)))

/-- **Link [EsthelLogEta2] — `eq:esthel2` of `lem:bostb1`, the `eq:kuche2` branch** (book
`typeI.tex` 1399-1466): under `lem:bostb1`'s hypotheses with `|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`, for
EVERY `T` obeying the per-`m` estimate at `α`, the sum of `T(d)` over the `d ≤ D` that are NOT
(`q ∣ d` and `d ≤ M`) is at most `eq:kuche2`. Sources: `eq:bobo` (`lem:thina`), `eq:bocio`
(`lem:couscous`), the `eq:caron` analogue and `eq:binbed` (`lem:gotog`), all PROVED trigonometric
sums in `Common.TrigSums`. OPEN. -/
def EsthelLogEta2 : Prop :=
  ∀ x α δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.sqrt 3 ≤ D → D ≤ x / 4 → (|δ| ≤ 1 / (2 * c2) ∨ D ≤ Q0 / 2) →
    ∀ T : ℕ → ℝ, TromLB x α T →
      ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q D)), T d ≤
        kuche2 x q D

/-! ## (3) The composition, PROVED -/

/-- **`MPG.Bostb1Eta2` from its three links, PROVED** (application, with `M = mR`). -/
theorem bostb1Eta2_of (h1 : TrompaisLogEta2) (h2 : MainLogEta2) (h3 : EsthelLogEta2) :
    Bostb1Eta2 := by
  intro x α δ Q0 D a q hq hg h2α hδ hqQ hQ hsq hD3 hDx hbr
  have hD0 : 0 < D := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) hD3
  have hx : 0 < x := by linarith
  have hT : TromLB x α (fun d => ‖tlo x α d‖) :=
    fun d hd hdx => ⟨norm_nonneg _, h1 x α hx d hd hdx⟩
  have hmain := h2 x α δ Q0 D a q hq hg h2α hδ hqQ hQ hsq hD3 hDx
  have hrest := h3 x α δ Q0 D a q hq hg h2α hδ hqQ hQ hsq hD3 hDx hbr _ hT
  have hle := sI1_le x α D (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q D) (by linarith)
  refine ⟨mR x δ q D, mR_ge x δ q D Q0 hx hq (by linarith) hδ, mR_le x δ q D, ?_⟩
  calc ‖sI1 x α D‖ ≤ _ := hle
    _ ≤ mainI1 x δ q (mR x δ q D) + errI1 x q D + kuche2 x q D := add_le_add hmain hrest

end Principia.Common.TernaryGoldbach.MPB1
