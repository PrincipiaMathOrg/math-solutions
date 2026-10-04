/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EsthelBase

set_option autoImplicit false

/-!
# `MPB2.EsthelEta2`, the `eq:keks` branch PROVED

`MPB2.EsthelEta2` (`Bosta2Spine`) is the trigonometric-sum core of `lem:bosta2`: for every `T`
obeying `eq:trompais`, the `d ≤ D` other than (`q ∣ d` and `d ≤ M`) sum to at most `eq:keks`
(when `|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`) and to at most `eq:kallervo2(ε)` (when `|δ| ≥ 1/2c₂`).

```
 EsthelEta2 ← EsthelEta2K   the eq:keks branch      PROVED  (esthelEta2K_holds)
            ← EsthelEta2E   the eq:kallervo2 branch OPEN    (second approximation a'/q')
 esthelEta2_of_KE, esthelEta2_of_E : PROVED (application)
```

`esthel_keks` is the branch for an abstract approximation `α = a/q + β'/(qQ)`: the sum is
covered by `piece1` (`m ≤ q/2`), `piece2` (`q/2 < m ≤ D'`, `q ∤ m`; the `q ∣ m` there have
`m ≤ D' ≤ M` and are excluded) and `piece3` (`R < m ≤ D`), `D' = min(c₂x/q, D)`,
`R = max(c₂x/q, q/2)`; then `(2√c₀/π)D' + (2√(c₀c₁)/π)max(D - R, 0) ≤ (2√(c₀c₁)/π)D` because
`D' ≤ R` and `D' ≤ D` -- the book's "absorbed by the `-R` term". `approx_keks` supplies
`Q = x/|δ|q` (`Q = 2D + Q₀` if `δ = 0`), for which `2D' ≤ Q` and `D' ≤ mR` follow from either
branch hypothesis.

No falsification: the statement was checked term by term against the book's proof before
proving (the `eq:keks` constants `2|η₂'|₁/π · max(1, ·)`, `3c₁/2c₂`, `55c₀c₂/6π²` are exactly
what `lem:thina`, `eq:kosto` and `eq:martinu` deliver after the `lem:bosta2` doublings).
-/

namespace Principia.Common.TernaryGoldbach.MPE2

open Real Finset Principia.Common.TrigSumN
open Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPB2

/-- `∑_{A ∪ B} f ≤ ∑_A f + ∑_B f` for `f ≥ 0`. -/
theorem sum_union_le_nn (A B : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) :
    ∑ d ∈ A ∪ B, f d ≤ ∑ d ∈ A, f d + ∑ d ∈ B, f d := by
  rw [← Finset.sum_union_inter]
  have : 0 ≤ ∑ d ∈ A ∩ B, f d := Finset.sum_nonneg fun d _ => hf d
  linarith

/-- **`eq:esthel` in the `eq:keks` case, for any `T` obeying `eq:trompais`** (book `typeI.tex`
903-993, as modified at 1119-1141): if `2D' ≤ Q` and `D' ≤ M` for `D' = min(c₂x/q, D)`, then the
`m ≤ D` other than (`q ∣ m` and `m ≤ M`) contribute at most `eq:keks`. -/
theorem esthel_keks (x α β Q D M : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hD : 1 ≤ D) (hDQ : 2 * min (c2 * x / q) D ≤ Q) (hM : min (c2 * x / q) D ≤ M)
    (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), t d ≤ keks x q D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  set D' := min (c2 * x / q) D with hD'_def
  set R := max (c2 * x / q) ((q : ℝ) / 2) with hR_def
  have hD'0 : 0 ≤ D' := le_min (by positivity) (by linarith)
  have hD'c : D' ≤ c2 * x / q := min_le_left _ _
  have hD'D : D' ≤ D := min_le_right _ _
  have hR1 : c2 * x / q ≤ R := le_max_left _ _
  have hR2 : (q : ℝ) / 2 ≤ R := le_max_right _ _
  have ht0 : ∀ d, 0 ≤ (if 1 ≤ d then t d else 0) := by
    intro d
    split_ifs with h
    · exact (ht d h).1
    · exact le_rfl
  -- the cover
  have hcov : (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)) ⊆
      (Ioc 0 (q / 2) ∪ (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d)) ∪ Ioc ⌊R⌋₊ ⌊D⌋₊ := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, hdN⟩, hnot⟩ := hd
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc,
      Finset.mem_Ioc]
    by_cases h1 : d ≤ q / 2
    · exact Or.inl (Or.inl ⟨hd0, h1⟩)
    by_cases h2 : d ≤ ⌊D'⌋₊
    · refine Or.inl (Or.inr ⟨⟨by omega, h2⟩, fun hqd => hnot ⟨hqd, ?_⟩⟩)
      have : (d : ℝ) ≤ ⌊D'⌋₊ := by exact_mod_cast h2
      linarith [Nat.floor_le hD'0]
    · refine Or.inr ⟨?_, hdN⟩
      rw [Nat.floor_lt (by positivity)]
      have hDd : D' < d := (Nat.floor_lt hD'0).mp (by omega)
      have hdD : (d : ℝ) ≤ D := le_trans (by exact_mod_cast hdN) (Nat.floor_le (by linarith))
      have hcd : c2 * x / q < d := by
        rcases min_lt_iff.mp hDd with h | h
        · exact h
        · linarith
      have hqd : (q : ℝ) / 2 < d := by
        have : q < 2 * d := by omega
        have : (q : ℝ) < 2 * d := by exact_mod_cast this
        linarith
      exact max_lt hcd hqd
  -- the three pieces
  have hS : ∑ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), t d ≤
      ∑ d ∈ Ioc 0 (q / 2), t d + ∑ d ∈ (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d), t d +
        ∑ d ∈ Ioc ⌊R⌋₊ ⌊D⌋₊, t d := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcov (f := fun d => if 1 ≤ d then t d else 0)
      (fun d _ _ => ht0 d)
    have e0 : ∀ (S : Finset ℕ), (∀ d ∈ S, 1 ≤ d) →
        ∑ d ∈ S, (if 1 ≤ d then t d else 0) = ∑ d ∈ S, t d := by
      intro S hS
      exact Finset.sum_congr rfl fun d hd => if_pos (hS d hd)
    have hpos1 : ∀ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), 1 ≤ d := by
      intro d hd
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
      omega
    rw [e0 _ hpos1] at hsub
    refine hsub.trans ?_
    refine (sum_union_le_nn _ _ _ ht0).trans ?_
    refine add_le_add ((sum_union_le_nn _ _ _ ht0).trans (add_le_add ?_ ?_)) ?_
    · refine le_of_eq (e0 _ fun d hd => ?_)
      have := (Finset.mem_Ioc.mp hd).1
      omega
    · refine le_of_eq (e0 _ fun d hd => ?_)
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
      omega
    · refine le_of_eq (e0 _ fun d hd => ?_)
      have := (Finset.mem_Ioc.mp hd).1
      omega
  have h1 := piece1 x α β Q a q hq hcop hα hβ hqQ hx t ht
  have h2 := piece2 x α β Q D' a q hq hcop hα hβ hx hD'0 hDQ hD'c t ht
  have h3 := piece3 x α β Q D R a q hq hcop hα hβ hqQ hx hD hR1 hR2 t ht
  refine hS.trans ?_
  -- the arithmetic
  set s := √(c0 * c1 x D) with hs_def
  have hs1 : √c0 ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 ≤ √c0 := Real.sqrt_nonneg _
  have h3c : √(3 * c0 * c1 x D) = √3 * s := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num)]
  have hDterm : 2 * √c0 / π * D' + 2 * s / π * max (D - R) 0 ≤ 2 * s / π * D := by
    have hk : 0 ≤ 2 / π := by positivity
    have e1 : 2 * √c0 / π * D' + 2 * s / π * max (D - R) 0 = 2 / π * (√c0 * D' + s * max (D - R) 0)
      := by ring
    have e2 : 2 * s / π * D = 2 / π * (s * D) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ hk
    have hc : √c0 * D' ≤ s * D' := mul_le_mul_of_nonneg_right hs1 hD'0
    rcases le_total R D with hRD | hRD
    · rw [max_eq_left (by linarith)]
      have : s * D' ≤ s * R := mul_le_mul_of_nonneg_left (hD'c.trans hR1) (by positivity)
      nlinarith
    · rw [max_eq_right (by linarith)]
      have : s * D' ≤ s * D := mul_le_mul_of_nonneg_left hD'D (by positivity)
      linarith
  unfold keks
  rw [h3c]
  have e : 2 * s / π * (√3 * q + max (D - R) 0 + q / 2 * logp (D / (q / 2))) =
      2 * s / π * max (D - R) 0 + s / π * q * logp (D / (q / 2)) + 2 * (√3 * s) / π * q := by
    ring
  rw [e] at h3
  have e2 : (2 * (√3 * s) / π + 3 * c1 x D / (2 * c2) + 55 * c0 * c2 / (6 * π ^ 2)) * q =
      2 * (√3 * s) / π * q + 3 * c1 x D / (2 * c2) * q + 55 * c0 * c2 / (6 * π ^ 2) * q := by
    ring
  rw [e2]
  linarith

/-! ## `EsthelEta2` split into its two branches; the `eq:keks` branch PROVED -/

/-- **Link [EsthelEta2K] — `eq:esthel` of `lem:bosta2`, the `eq:keks` branch**: the first
conjunct of `MPB2.EsthelEta2`, verbatim. PROVED below (`esthelEta2K_holds`). -/
def EsthelEta2K : Prop :=
  ∀ x β δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * β = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ D → D ≤ x →
    ∀ T : ℕ → ℝ, TromB x β T →
      (|δ| ≤ 1 / (2 * c2) ∨ D ≤ Q0 / 2) →
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q D)), T d ≤
          keks x q D

/-- **Link [EsthelEta2E] — `eq:esthel` of `lem:bosta2`, the `eq:kallervo2` branch**: the second
conjunct of `MPB2.EsthelEta2`, verbatim (`|δ| ≥ 1/2c₂`, the second approximation `a'/q'`,
`eq:jenuf`, `eq:tenda`, `eq:beatri`, `eq:sauna`). OPEN. -/
def EsthelEta2E : Prop :=
  ∀ x β δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * β = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ D → D ≤ x →
    ∀ T : ℕ → ℝ, TromB x β T →
      1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∑ d ∈ (Finset.Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q D)), T d ≤
          kallervo2 x δ q D Q0 ε

/-- **`MPB2.EsthelEta2` from its two branches, PROVED.** -/
theorem esthelEta2_of_KE (hk : EsthelEta2K) (he : EsthelEta2E) : EsthelEta2 := by
  intro x β δ Q0 D a q hq hg h2 hδ hqQ hQ hD1 hDx T hT
  exact ⟨hk x β δ Q0 D a q hq hg h2 hδ hqQ hQ hD1 hDx T hT,
    he x β δ Q0 D a q hq hg h2 hδ hqQ hQ hD1 hDx T hT⟩

/-- **The approximation `2β = a/q + β'/(qQ)` with `|β'| ≤ 1`, `Q ≥ Q₀`, `2D' ≤ Q`, `D' ≤ mR`**
in the `eq:keks` case (`Q = x/|δ|q`; `Q = 2D + Q₀` when `δ = 0`). -/
theorem approx_keks (x β δ Q0 D : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (h2 : 2 * β = a / q + δ / x)
    (hδ : |δ / x| ≤ 1 / (q * Q0)) (hqQ : (q : ℝ) ≤ Q0) (hQ : 16 ≤ Q0) (hD1 : 1 ≤ D)
    (hDx : D ≤ x) (hbr : |δ| ≤ 1 / (2 * c2) ∨ D ≤ Q0 / 2) :
    ∃ Q β' : ℝ, 2 * β = a / q + β' / (q * Q) ∧ |β'| ≤ 1 ∧ (q : ℝ) ≤ Q ∧
      2 * min (c2 * x / q) D ≤ Q ∧ min (c2 * x / q) D ≤ mR x δ q D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : 0 < x := by linarith
  have hc2 := c2_pos
  by_cases h0 : δ = 0
  · refine ⟨2 * D + Q0, 0, ?_, by norm_num, by linarith, ?_, ?_⟩
    · rw [h2, h0]
      simp
    · have := min_le_right (c2 * x / q) D
      linarith
    · unfold mR
      rw [if_pos h0]
      exact min_le_right _ _
  · have hd : 0 < |δ| := abs_pos.mpr h0
    have hQ0 : Q0 ≤ x / (|δ| * q) := by
      rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδ
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hmR : mR x δ q D = min (x / (2 * |δ| * q)) D := by
      unfold mR
      rw [if_neg h0]
    have hhalf : x / (2 * |δ| * q) = x / (|δ| * q) / 2 := by
      field_simp
    refine ⟨x / (|δ| * q), δ / |δ|, ?_, ?_, by linarith, ?_, ?_⟩
    · rw [h2]
      congr 1
      field_simp
    · rw [abs_div, abs_abs, div_self hd.ne']
    · rcases hbr with hb | hb
      · have h1 : c2 * x / q ≤ x / (|δ| * q) / 2 := by
          rw [le_div_iff₀ (by norm_num), div_mul_eq_mul_div, div_le_div_iff₀ hq0 (by positivity)]
          rw [le_div_iff₀ (by positivity)] at hb
          have : 0 ≤ x * q := by positivity
          nlinarith
        have := min_le_left (c2 * x / q) D
        linarith
      · have := min_le_right (c2 * x / q) D
        linarith
    · rw [hmR, hhalf]
      rcases hbr with hb | hb
      · refine min_le_min ?_ le_rfl
        rw [le_div_iff₀ (by norm_num), div_mul_eq_mul_div, div_le_div_iff₀ hq0 (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hb
        have : 0 ≤ x * q := by positivity
        nlinarith
      · have hDQ : D ≤ x / (|δ| * q) / 2 := by linarith
        rw [min_eq_right hDQ]
        exact min_le_right _ _

/-- **`EsthelEta2K`, PROVED** (`esthel_keks` at `α = 2β`, with `approx_keks`). -/
theorem esthelEta2K_holds : EsthelEta2K := by
  intro x β δ Q0 D a q hq hg h2 hδ hqQ hQ hD1 hDx T hT hbr
  have hx : 0 < x := by linarith
  obtain ⟨Q, β', hα, hβ', hqQ', hDQ, hM⟩ := approx_keks x β δ Q0 D a q hq h2 hδ hqQ hQ hD1 hDx hbr
  exact esthel_keks x (2 * β) β' Q D (mR x δ q D) a q hq hg hα hβ' hqQ' hx hD1 hDQ hM T
    (tb_of_tromB x β T hT)

/-- **`MPB2.EsthelEta2` from its `eq:kallervo2` branch alone, PROVED.** -/
theorem esthelEta2_of_E (he : EsthelEta2E) : EsthelEta2 :=
  esthelEta2_of_KE esthelEta2K_holds he

end Principia.Common.TernaryGoldbach.MPE2
