/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPieces

set_option autoImplicit false

/-!
# `MPc.Bosta2Eta2` spined to the three pieces of the proof of `lem:bosta2`

`lem:bosta2` (book `typeI.tex` 1002-1145; minarcs 1724-1866) bounds
`gorio2 = ∑_{m ≤ D odd} μ(m) T_{m,∘}(β)`, `T_{m,∘}(β) = ∑_{n odd} e(βmn)η₂(mn/x)` (`eq:baxter`).
Its proof has exactly three ingredients, and each is a NAMED link here:

```
 Bosta2Eta2 ← TrompaisEta2  eq:trompais: the three per-m bounds of |T_{m,∘}| (Poisson / eq:ra /
                            lem:areval with |η₂|₁ = 1, |η₂'|₁ = 8 log 2, |η̂₂''|_∞ ≤ c₀ = 31.521)
            ← MainOddEta2   eq:kormo + eq:karma: the m odd, q | m, m ≤ M terms ≤ eq:asparto
            ← EsthelEta2    eq:esthel: every other m ≤ D, for ANY T obeying eq:trompais,
                            ≤ eq:keks (|δ| ≤ 1/2c₂ or D ≤ Q₀/2) / eq:kallervo2 (|δ| ≥ 1/2c₂);
                            the trigonometric-sum core (lem:gotog, lem:couscous, lem:thina)
            gorio2_split, gorio2_le : PROVED (the decomposition and the triangle inequality)
            bosta2Eta2_of           : PROVED (application)
```

`EsthelEta2` quantifies over an abstract `T : ℕ → ℝ`, so it is pure trigonometric-sum
combinatorics: no Fourier analysis, no `η₂`; its inputs are exactly the PROVED
`Common.TrigSums` lemmas `gotog`, `couscous`, `thina`. The Fourier analysis is confined to
`TrompaisEta2` and `MainOddEta2`.

## The split point `M`

The book takes `M = min(Q/2, D)` with `Q = ⌊x/|δq|⌋` and states `M ∈ [min(Q₀/2, D), D]`. When
`Q₀ ∉ ℤ`, `⌊x/|δq|⌋/2` can fall below `Q₀/2` (e.g. `x/|δq| = Q₀ = 16.5`), so that choice does
not give the stated range. The spine uses the REAL split `M = min(x/(2|δ|q), D)` (`mR`), which
does (`mR_ge`): the main-term step only needs `m ≤ x/(2|δq|)` (`|x/m| ≥ 2|δq|`, `eq:karma`), and
the remaining set `{q ∤ m, m ≤ M} ∪ {m > M}` is a SUBSET of the book's remaining set at the
integer `Q` (at most one multiple of `q` lies in `(⌊Q⌋/2, Q/2]`, and it moves to the main term),
so the book's `eq:esthel` bounds apply verbatim to it because every `|T_m| ≥ 0`.
-/

namespace Principia.Common.TernaryGoldbach.MPB2

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc

/-! ## (1) The objects -/

/-- **`T_{d,∘}(β) = ∑_{m odd} e(βdm)η₂(dm/x)`** (`eq:baxter`), truncated at `dm ≤ x` (where
`η₂(dm/x) = 0` beyond). -/
noncomputable def tmo (x β : ℝ) (d : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / d), ((fOdd m : ℝ) : ℂ) * wt x β (d * m)

/-- **The split point** `M = min(x/(2|δ|q), D)` (`M = D` when `δ = 0`). -/
noncomputable def mR (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  if δ = 0 then D else min (x / (2 * |δ| * q)) D

/-- `M ≤ D`. -/
theorem mR_le (x δ : ℝ) (q : ℕ) (D : ℝ) : mR x δ q D ≤ D := by
  unfold mR
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

/-- `M ≥ min(Q₀/2, D)` from `|δ/x| ≤ 1/(qQ₀)`. -/
theorem mR_ge (x δ : ℝ) (q : ℕ) (D Q0 : ℝ) (hx : 0 < x) (hq : 1 ≤ q) (hQ0 : 0 < Q0)
    (hδ : |δ / x| ≤ 1 / (q * Q0)) : min (Q0 / 2) D ≤ mR x δ q D := by
  unfold mR
  split_ifs with h0
  · exact min_le_right _ _
  · refine min_le_min ?_ le_rfl
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hd : 0 < |δ| := abs_pos.mpr h0
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδ
    rw [le_div_iff₀ (by positivity)]
    linarith

/-! ## (2) The decomposition, PROVED -/

/-- **`gorio2 = ∑_{d ≤ x} μ_{≤D}(d)f(d)·T_{d,∘}(β)`, PROVED.** -/
theorem gorio2_split (x β D : ℝ) :
    gorio2 x β D = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ((aU D d * fOdd d : ℝ) : ℂ) * tmo x β d := by
  unfold gorio2
  rw [sP_mul_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [tw_apply]
  congr 1
  unfold tmo
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : m ≠ 0 := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  rw [tw_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hm1,
    Nat.cast_one, one_mul]

/-- `|μ_{≤D}(d)f(d)| ≤ 1`. -/
theorem coef_abs (D : ℝ) (d : ℕ) : |aU D d * fOdd d| ≤ 1 := by
  unfold aU
  rw [MinSum.truncate_apply]
  split_ifs
  · rw [abs_mul, ArithmeticFunction.intCoe_apply]
    have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have h2 : |fOdd d| ≤ 1 := by
      rw [abs_of_nonneg (fOdd_nonneg d)]
      exact fOdd_le_one d
    calc |((μ d : ℤ) : ℝ)| * |fOdd d| ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · simp

/-- `μ_{≤D}(d) = 0` for `d > D`. -/
theorem coef_zero (D : ℝ) (d : ℕ) (hd : ⌊D⌋₊ < d) : aU D d * fOdd d = 0 := by
  unfold aU
  rw [MinSum.truncate_apply, if_neg (by omega), zero_mul]

/-- **The triangle inequality along any split `P`, for any inner sums `T`, PROVED**:
`|∑_{d ≤ x} μ_{≤D}(d)f(d)T(d)| ≤ |∑_{P} μ f T| + ∑_{d ≤ D, ¬P} |T(d)|`. -/
theorem split_le (x D : ℝ) (T : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] (hDx : D ≤ x) :
    ‖∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ((aU D d * fOdd d : ℝ) : ℂ) * T d‖ ≤
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter P, ((aU D d * fOdd d : ℝ) : ℂ) * T d‖ +
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d), ‖T d‖ := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) P
    (fun d => ((aU D d * fOdd d : ℝ) : ℂ) * T d)]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  have hsub : (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d) ⊆
      (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => ¬ P d) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
    exact ⟨⟨hd.1.1, hd.1.2.trans (Nat.floor_mono hDx)⟩, hd.2⟩
  calc _ ≤ ∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => ¬ P d),
          ‖((aU D d * fOdd d : ℝ) : ℂ) * T d‖ := norm_sum_le _ _
    _ = ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d),
          ‖((aU D d * fOdd d : ℝ) : ℂ) * T d‖ := by
        refine (Finset.sum_subset hsub ?_).symm
        intro d hd hnd
        have hlt : ⌊D⌋₊ < d := by
          rw [Finset.mem_filter, Finset.mem_Ioc] at hd hnd
          by_contra h
          exact hnd ⟨⟨hd.1.1, not_lt.mp h⟩, hd.2⟩
        rw [coef_zero D d hlt]
        simp
    _ ≤ _ := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |aU D d * fOdd d| * ‖T d‖ ≤ 1 * ‖T d‖ :=
              mul_le_mul_of_nonneg_right (coef_abs D d) (norm_nonneg _)
          _ = ‖T d‖ := one_mul _

/-- **`|gorio2| ≤ |∑_{P} μ f T_{d,∘}| + ∑_{d ≤ D, ¬P} |T_{d,∘}|`, PROVED.** -/
theorem gorio2_le (x β D : ℝ) (P : ℕ → Prop) [DecidablePred P] (hDx : D ≤ x) :
    ‖gorio2 x β D‖ ≤
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter P, ((aU D d * fOdd d : ℝ) : ℂ) * tmo x β d‖ +
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d), ‖tmo x β d‖ := by
  rw [gorio2_split]
  exact split_le x D (tmo x β) P hDx

/-! ## (3) The three links -/

/-- **Link [TrompaisEta2] — `eq:trompais` for `η₂`** (book `typeI.tex` 1105-1118): for
`x > 0`, `d ≥ 1`, `|T_{d,∘}(γ)| ≤ min(x/2d + |η₂'|₁/2, (|η₂'|₁/2)/|sin 2πdγ|,
(d/x)(c₀/2)/sin²2πdγ)`, the last two written multiplicatively (so `sin = 0` is no exception).
Sources: `eq:ra` (Tao 2012 Lem 3.1), `lem:areval` (Poisson), `|η₂|₁ = 1`,
`|η₂'|₁ = 8 log 2` (`eq:muggle`), `|η̂₂''|_∞ ≤ c₀ = 31.521` (`lem:camelo`; `HC.CameloGridCited`).
OPEN. -/
def TrompaisEta2 : Prop :=
  ∀ x γ : ℝ, 0 < x → ∀ d : ℕ, 1 ≤ d →
    ‖tmo x γ d‖ ≤ x / (2 * d) + eta1 / 2 ∧
      ‖tmo x γ d‖ * |Real.sin (2 * Real.pi * d * γ)| ≤ eta1 / 2 ∧
      ‖tmo x γ d‖ * Real.sin (2 * Real.pi * d * γ) ^ 2 ≤ d / x * (c0 / 2)

/-- **Link [MainOddEta2] — the main term of `lem:bosta2`** (book `typeI.tex` 1058-1103,
`eq:kormo`, `eq:karma`): under `lem:bosta2`'s hypotheses, the terms `m` odd, `q ∣ m`,
`m ≤ M = mR` sum to at most `eq:asparto` with the μ-sum `∑_{m ≤ M/q, (m,2q)=1} μ(m)/m`. (Poisson
per `m = qm'`, the zero frequency `(x/2m)η̂(−δ/2)`, `|η̂(−δ/2)| ≤ min(1, c₀/(πδ)²)`, and the
nonzero frequencies `(m/x)(c₀/2π²)(π² − 4)` since `|δm/x| ≤ 1/2q`; `∑_{m' ≤ N odd} m' ≤
(N + 1)²/4`.) OPEN. -/
def MainOddEta2 : Prop :=
  ∀ x β δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * β = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ D → D ≤ x →
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q D),
          ((aU D d * fOdd d : ℝ) : ℂ) * tmo x β d‖ ≤
        asparto x δ q D (muS (2 * q) (mR x δ q D / q))

/-- **`T` obeys `eq:trompais` at `γ`** (with `T ≥ 0`). -/
def TromB (x γ : ℝ) (T : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → 0 ≤ T d ∧
    (T d ≤ x / (2 * d) + eta1 / 2 ∧
      T d * |Real.sin (2 * Real.pi * d * γ)| ≤ eta1 / 2 ∧
      T d * Real.sin (2 * Real.pi * d * γ) ^ 2 ≤ d / x * (c0 / 2))

/-- **Link [EsthelEta2] — `eq:esthel` of `lem:bosta2`, the trigonometric-sum core** (book
`typeI.tex` 720-993 with the modifications 1119-1141): under `lem:bosta2`'s hypotheses, for EVERY
`T` obeying `eq:trompais` at `β`, the sum of `T(d)` over the `d ≤ D` that are NOT (`q ∣ d` and
`d ≤ M`) is at most `eq:keks` when `|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`, and at most `eq:kallervo2(ε)` for
every `ε ∈ (0, 1]` when `|δ| ≥ 1/2c₂`. Sources: `lem:couscous`, `lem:gotog`, `lem:thina`
(PROVED in `Common.TrigSums`), the second approximation `a'/q'` at `Q' = ⌈(1 + ε)Q⌉`
(Dirichlet), `eq:tenda`, `eq:beatri`, `eq:kosto`, `eq:kostas`, `eq:sosot`. OPEN. -/
def EsthelEta2 : Prop :=
  ∀ x β δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * β = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ D → D ≤ x →
    ∀ T : ℕ → ℝ, TromB x β T →
      ((|δ| ≤ 1 / (2 * c2) ∨ D ≤ Q0 / 2) →
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q D)), T d ≤
          keks x q D) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q D)), T d ≤
          kallervo2 x δ q D Q0 ε)

/-! ## (4) The composition, PROVED -/

/-- **`MPc.Bosta2Eta2` from its three links, PROVED** (application, with `M = mR`). -/
theorem bosta2Eta2_of (h1 : TrompaisEta2) (h2 : MainOddEta2) (h3 : EsthelEta2) :
    Bosta2Eta2 := by
  intro x β δ Q0 D a q hq hg h2β hδ hqQ hQ hD1 hDx
  have hx : 0 < x := by linarith
  have hT : TromB x β (fun d => ‖tmo x β d‖) := fun d hd => ⟨norm_nonneg _, h1 x β hx d hd⟩
  have hmain := h2 x β δ Q0 D a q hq hg h2β hδ hqQ hQ hD1 hDx
  obtain ⟨hb, ha⟩ := h3 x β δ Q0 D a q hq hg h2β hδ hqQ hQ hD1 hDx _ hT
  have hle := gorio2_le x β D (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q D) hDx
  refine ⟨mR x δ q D, mR_ge x δ q D Q0 hx hq (by linarith) hδ, mR_le x δ q D,
    fun hc => hle.trans (add_le_add hmain (hb hc)),
    fun hc ε hε hε1 => hle.trans (add_le_add hmain (ha hc ε hε hε1))⟩

end Principia.Common.TernaryGoldbach.MPB2
