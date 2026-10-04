/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisAB

set_option autoImplicit false

/-!
# `MPG.BogusEta2` spined to the three pieces of the proof of `lem:bogus`

`lem:bogus` (book `typeI.tex` 1496-1700) bounds
`S_{I,2} = ∑_{v ≤ V odd} Λ(v) ∑_{u ≤ U odd} μ(u) ∑_{n odd} e(αvun)η₂(vun/x)`. Its proof groups
`m = uv`, with coefficient `c(m) = ∑_{uv = m, u ≤ U, v ≤ V} μ(u)Λ(v)` (`|c(m)| ≤ log m`, and
`c(m) = 0` for `m > UV`), and has exactly three ingredients, each a NAMED link here:

```
 BogusEta2 ← TrompaisEta2     eq:trompais (← MPT.TrompaisC alone: parts 1-2 are PROVED)
           ← MainBogusEta2    eq:hoho: the m odd, q | m, m ≤ M terms ≤ eq:cupcake3
                              (eq:kormo, eq:karma, eq:grara, eq:rala, eq:trado2, eq:chronop)
           ← EsthelBogusEta2  eq:esthel3: ∑ (log m)T(m) over every other m ≤ UV, for ANY T
                              obeying eq:trompais, ≤ eq:piececake / eq:tvorog(ε)
           sI2_split, coef_abs_le, coef_zero, wsplit_le : PROVED
           bogusEta2_of, bogusEta2_of_C                 : PROVED (application)
```

The split point is `M = MPB2.mR x δ q (UV)`, as in `Bosta2Spine` (the book's `min(UV, Q/2)`
with `Q = ⌊x/|δq|⌋` replaced by the real `x/(2|δ|q)`: `eq:karma` needs only `m ≤ x/(2|δq|)`,
and the remaining set is a subset of the book's, every `log m · |T_m| ≥ 0`).

`EsthelBogusEta2`'s second branch is `eq:tvorog` VERBATIM, as `MPG.BogusEta2` states it; a fork
reader flagged a "missing factor 2" slip in `eq:tvorog` (`minmain_spine.md`, T7). Whoever proves
this link is the first to check that branch as stated.
-/

namespace Principia.Common.TernaryGoldbach.MPBG

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPT

/-! ## (1) The coefficient `c = μ_{≤U} ∗ Λ_{≤V}` -/

/-- **`c(m) = ∑_{uv = m, u ≤ U, v ≤ V} μ(u)Λ(v)`.** -/
noncomputable def cUV (U V : ℝ) : ArithmeticFunction ℝ := aU U * bV V

/-- **`|c(m)| ≤ log m`, PROVED** (`|μ_{≤U}| ≤ 1`, `0 ≤ Λ_{≤V} ≤ Λ`, `∑_{v ∣ m} Λ(v) = log m`). -/
theorem coef_abs_le (U V : ℝ) (m : ℕ) : |cUV U V m| ≤ Real.log m := by
  unfold cUV
  rw [ArithmeticFunction.mul_apply, ← ArithmeticFunction.vonMangoldt_sum,
    ← Nat.sum_divisorsAntidiagonal' (f := fun _ b => Λ b)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  have h1 : |aU U p.1| ≤ 1 := by
    unfold aU
    rw [MinSum.truncate_apply]
    split_ifs
    · rw [ArithmeticFunction.intCoe_apply]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
    · simp
  have h2 : |bV V p.2| ≤ Λ p.2 := by
    unfold bV
    rw [MinSum.truncate_apply]
    split_ifs
    · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    · rw [abs_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
  calc |aU U p.1| * |bV V p.2| ≤ 1 * Λ p.2 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = Λ p.2 := one_mul _

/-- **`c(m) = 0` for `m > ⌊UV⌋`, PROVED** (`u ≤ ⌊U⌋`, `v ≤ ⌊V⌋` force `uv ≤ ⌊U⌋⌊V⌋ ≤ ⌊UV⌋`). -/
theorem coef_zero (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (m : ℕ) (hm : ⌊U * V⌋₊ < m) :
    cUV U V m = 0 := by
  unfold cUV
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpm := (Nat.mem_divisorsAntidiagonal.mp hp).1
  unfold aU bV
  rw [MinSum.truncate_apply, MinSum.truncate_apply]
  split_ifs with ha hb
  · exfalso
    have hfl : ⌊U⌋₊ * ⌊V⌋₊ ≤ ⌊U * V⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact mul_le_mul (Nat.floor_le hU) (Nat.floor_le hV) (Nat.cast_nonneg _) hU
    have : p.1 * p.2 ≤ ⌊U⌋₊ * ⌊V⌋₊ := Nat.mul_le_mul ha hb
    omega
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

/-! ## (2) The decomposition, PROVED -/

/-- **`S_{I,2} = ∑_{d ≤ x} c(d)f(d)·T_{d,∘}(α)`, PROVED.** -/
theorem sI2_split (x α U V : ℝ) :
    sI2 x α U V = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ((cUV U V d * fOdd d : ℝ) : ℂ) * tmo x α d := by
  unfold sI2 cUV
  rw [← tw_mul, sP_mul_eq]
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

/-- **The weighted triangle inequality along any split `P`, PROVED**: for `|c(d)| ≤ log d`,
`c(d) = 0` beyond `⌊D⌋`, `D ≤ x`:
`|∑_{d ≤ x} c f T| ≤ |∑_{P} c f T| + ∑_{d ≤ D, ¬P} (log d)|T(d)|`. -/
theorem wsplit_le (x D : ℝ) (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ Real.log d)
    (hz : ∀ d, ⌊D⌋₊ < d → c d = 0) (T : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    (hDx : D ≤ x) :
    ‖∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ((c d * fOdd d : ℝ) : ℂ) * T d‖ ≤
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter P, ((c d * fOdd d : ℝ) : ℂ) * T d‖ +
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d), Real.log d * ‖T d‖ := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) P
    (fun d => ((c d * fOdd d : ℝ) : ℂ) * T d)]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  have hsub : (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d) ⊆
      (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => ¬ P d) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
    exact ⟨⟨hd.1.1, hd.1.2.trans (Nat.floor_mono hDx)⟩, hd.2⟩
  calc _ ≤ ∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => ¬ P d),
          ‖((c d * fOdd d : ℝ) : ℂ) * T d‖ := norm_sum_le _ _
    _ = ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ P d),
          ‖((c d * fOdd d : ℝ) : ℂ) * T d‖ := by
        refine (Finset.sum_subset hsub ?_).symm
        intro d hd hnd
        have hlt : ⌊D⌋₊ < d := by
          rw [Finset.mem_filter, Finset.mem_Ioc] at hd hnd
          by_contra h
          exact hnd ⟨⟨hd.1.1, not_lt.mp h⟩, hd.2⟩
        rw [hz d hlt]
        simp
    _ ≤ _ := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have hf : |fOdd d| ≤ 1 := by
          rw [abs_of_nonneg (fOdd_nonneg d)]
          exact fOdd_le_one d
        calc |c d| * |fOdd d| * ‖T d‖ ≤ Real.log d * 1 * ‖T d‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul (hc d) hf (abs_nonneg _) ((abs_nonneg _).trans (hc d))
          _ = Real.log d * ‖T d‖ := by ring

/-- **`|S_{I,2}| ≤ |∑_{P} c f T_{d,∘}| + ∑_{d ≤ UV, ¬P} (log d)|T_{d,∘}|`, PROVED.** -/
theorem sI2_le (x α U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (P : ℕ → Prop) [DecidablePred P]
    (hDx : U * V ≤ x) :
    ‖sI2 x α U V‖ ≤
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter P, ((cUV U V d * fOdd d : ℝ) : ℂ) * tmo x α d‖ +
        ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter (fun d => ¬ P d), Real.log d * ‖tmo x α d‖ := by
  rw [sI2_split]
  exact wsplit_le x (U * V) (cUV U V) (coef_abs_le U V) (coef_zero U V hU hV) (tmo x α) P hDx

/-! ## (3) The two `lem:bogus`-specific links -/

/-- **Link [MainBogusEta2] — the main term of `lem:bogus`** (book `typeI.tex` 1576-1660,
`eq:hoho`, `eq:billy`, `eq:etoile`): under `lem:bogus`'s hypotheses, the terms `m` odd, `q ∣ m`,
`m ≤ M = mR` sum to at most `eq:cupcake3`. (Poisson per `m`, `eq:kormo`, `eq:karma`; the
`v`-`u` regrouping with `eq:grara`, `eq:rala`; `∑_{u ≤ R odd, q ∣ u} u ≤ R²/4q + 3R/4`,
`eq:trado2`, `eq:chronop`, `c₄ = 1.03884`.) OPEN. -/
def MainBogusEta2 : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 2 * Real.exp 1 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V)),
          ((cUV U V d * fOdd d : ℝ) : ℂ) * tmo x α d‖ ≤ cupcake3 x δ q U V

/-- **Link [EsthelBogusEta2] — `eq:esthel3` of `lem:bogus`, the trigonometric-sum core** (book
`typeI.tex` 1662-1780): under `lem:bogus`'s hypotheses, for EVERY `T` obeying `eq:trompais` at
`α`, the sum of `(log d)T(d)` over the `d ≤ UV` that are NOT (`q ∣ d` and `d ≤ M`) is at most
`eq:piececake` when `|δ| ≤ 1/2c₂` or `UV ≤ Q₀/2`, and at most `eq:tvorog(ε)` for every
`ε ∈ (0, 1]` when `|δ| ≥ 1/2c₂`. Sources: `lem:gotog`, `lem:couscous`, `lem:thina` (PROVED in
`Common.TrigSums`), `eq:cocolo`. OPEN. -/
def EsthelBogusEta2 : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 2 * Real.exp 1 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
    ∀ T : ℕ → ℝ, TromB x α T →
      ((|δ| ≤ 1 / (2 * c2) ∨ U * V ≤ Q0 / 2) →
        ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter
            (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V))), Real.log d * T d ≤
          piececake x q U V) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter
            (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V))), Real.log d * T d ≤
          tvorog x δ q U V ε)

/-! ## (4) The composition, PROVED -/

/-- **`MPG.BogusEta2` from its three links, PROVED** (application, `M = mR`). -/
theorem bogusEta2_of (h1 : TrompaisEta2) (h2 : MainBogusEta2) (h3 : EsthelBogusEta2) :
    BogusEta2 := by
  intro x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV
  have hx0 : 0 < x := by
    have := c2_pos
    have : 0 < Real.exp 1 ^ 2 * c2 / 2 := by positivity
    linarith
  have hT : TromB x α (fun d => ‖tmo x α d‖) := fun d hd => ⟨norm_nonneg _, h1 x α hx0 d hd⟩
  have hmain := h2 x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV
  obtain ⟨hb, ht⟩ := h3 x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV _ hT
  have hQ0 : 0 ≤ Q0 := by linarith [Real.exp_pos 1]
  have h56 : x / 5.6 ≤ x := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hDx : U * V ≤ x := by linarith
  have hle := sI2_le x α U V (by linarith) (by linarith)
    (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V)) hDx
  exact ⟨fun hc => hle.trans (add_le_add hmain (hb hc)),
    fun hc ε hε hε1 => hle.trans (add_le_add hmain (ht hc ε hε hε1))⟩

/-- **`MPG.BogusEta2` on `TrompaisC`, `MainBogusEta2`, `EsthelBogusEta2`, PROVED.** -/
theorem bogusEta2_of_C (h1 : TrompaisC) (h2 : MainBogusEta2) (h3 : EsthelBogusEta2) :
    BogusEta2 :=
  bogusEta2_of (trompaisEta2_of h1) h2 h3

end Principia.Common.TernaryGoldbach.MPBG
