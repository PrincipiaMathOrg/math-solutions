/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PSieveBasic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

/-!
# The `G`-swap of `prop:ramar` / `prop:bellen`: nested arcs, a ratio bound, and Fubini

`ternvin.tex` 2398-2431 (and 2523-2574): for a fixed character the arcs of the moduli
`m = q*r` are nested intervals `|β| ≤ u₀/ρ(m)`, so
`∑_m c_m ∫_{|β| ≤ u₀/ρ(m)} f = ∫ f(β)·(∑_{ρ(m) ≤ K₀, ρ(m)|β| ≤ u₀} c_m) dβ`, and the inner sum
is `∑_{ρ(m) ≤ K₀/s} c_m` with `s = max(1, K₀|β|/u₀) ∈ [1, K₀]`. A ratio bound
`∑_{ρ ≤ K₀/s} c ≤ B·∑_{ρ ≤ K/s} c` at every `s ∈ [1, K₀]` then compares the two families of
arcs pointwise in `β`, provided `K/K₀ = u/u₀` (the scale `Q/Q₀`). `swap_bound` is that step,
for an arbitrary finite index set, nonnegative weights and radii `ρ ≥ 1`.
-/

namespace Principia.Common.PSieve

open MeasureTheory

/-- `∫_{−w}^{w} f = ∫ 1_{[−w,w]}f` (`w ≥ 0`). -/
theorem ival_eq_ind (f : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w) :
    ∫ β in (-w)..w, f β = ∫ β, (Set.Icc (-w) w).indicator f β := by
  rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]

/-- `1_{[−w,w]}f(β) = [|β| ≤ w]·f(β)`. -/
theorem ind_apply (f : ℝ → ℝ) (w β : ℝ) :
    (Set.Icc (-w) w).indicator f β = if |β| ≤ w then f β else 0 := by
  rw [Set.indicator_apply]
  congr 1
  exact propext (by rw [Set.mem_Icc, abs_le])

/-- `|β| ≤ u/ρ ↔ ρ|β| ≤ u` for `ρ > 0`. -/
theorem abs_le_div_iff (β u ρ : ℝ) (hρ : 0 < ρ) : |β| ≤ u / ρ ↔ ρ * |β| ≤ u := by
  rw [le_div_iff₀ hρ, mul_comm]

/-- **The inner sum**: `∑_{m ∈ T} c_m·1[ρ_m|β| ≤ u]·f(β) = f(β)·∑_{m ∈ T, ρ_m|β| ≤ u} c_m`. -/
theorem sum_ind (f : ℝ → ℝ) (T : Finset ℕ) (c ρ : ℕ → ℝ) (hρ : ∀ m ∈ T, 0 < ρ m) (u β : ℝ) :
    ∑ m ∈ T, c m * (Set.Icc (-(u / ρ m)) (u / ρ m)).indicator f β =
      f β * ∑ m ∈ T.filter (fun m => ρ m * |β| ≤ u), c m := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ind_apply]
  simp only [abs_le_div_iff β u (ρ m) (hρ m hm)]
  split_ifs <;> ring

/-- **The swap**: `∑_{m ∈ T} c_m ∫_{−u/ρ_m}^{u/ρ_m} f = ∫ f(β)·∑_{m ∈ T, ρ_m|β| ≤ u} c_m`. -/
theorem sum_int_eq (f : ℝ → ℝ) (hf : Continuous f) (T : Finset ℕ) (c ρ : ℕ → ℝ)
    (hρ : ∀ m ∈ T, 0 < ρ m) (u : ℝ) (hu : 0 ≤ u) :
    ∑ m ∈ T, c m * ∫ β in (-(u / ρ m))..(u / ρ m), f β =
      ∫ β, f β * ∑ m ∈ T.filter (fun m => ρ m * |β| ≤ u), c m := by
  have hint : ∀ m ∈ T, Integrable fun β => c m * (Set.Icc (-(u / ρ m)) (u / ρ m)).indicator f β :=
    fun m _ => (hf.integrableOn_Icc.integrable_indicator measurableSet_Icc).const_mul (c m)
  have e1 : ∀ m ∈ T, c m * ∫ β in (-(u / ρ m))..(u / ρ m), f β =
      ∫ β, c m * (Set.Icc (-(u / ρ m)) (u / ρ m)).indicator f β := by
    intro m hm
    rw [ival_eq_ind f _ (div_nonneg hu (hρ m hm).le), integral_const_mul]
  rw [Finset.sum_congr rfl e1, ← integral_finsetSum T hint]
  congr 1
  funext β
  exact sum_ind f T c ρ hρ u β

/-- **Integrability of the swapped integrand.** -/
theorem int_swap (f : ℝ → ℝ) (hf : Continuous f) (T : Finset ℕ) (c ρ : ℕ → ℝ)
    (hρ : ∀ m ∈ T, 0 < ρ m) (u : ℝ) :
    Integrable fun β => f β * ∑ m ∈ T.filter (fun m => ρ m * |β| ≤ u), c m := by
  have h := integrable_finsetSum T fun m _ =>
    (hf.integrableOn_Icc (μ := volume) (a := -(u / ρ m)) (b := u / ρ m)).integrable_indicator
      measurableSet_Icc |>.const_mul (c m)
  refine h.congr (Filter.Eventually.of_forall fun β => ?_)
  exact sum_ind f T c ρ hρ u β

/-- The two filters coincide at `s = max(1, K₀|β|/u₀)`: `ρ ≤ K₀ ∧ ρ|β| ≤ u₀ ↔ ρ ≤ K₀/s`. -/
theorem filt_iff (ρ K₀ u₀ β : ℝ) (hu₀ : 0 < u₀) (hK₀ : 0 < K₀) :
    (ρ ≤ K₀ ∧ ρ * |β| ≤ u₀) ↔ ρ ≤ K₀ / max 1 (K₀ * |β| / u₀) := by
  have hb := abs_nonneg β
  rcases le_total (K₀ * |β| / u₀) 1 with h | h
  · rw [max_eq_left h, div_one]
    have h' : K₀ * |β| ≤ u₀ := by rwa [div_le_one hu₀] at h
    constructor
    · exact fun h2 => h2.1
    · intro h2
      exact ⟨h2, le_trans (mul_le_mul_of_nonneg_right h2 hb) h'⟩
  · rw [max_eq_right h]
    have h' : u₀ ≤ K₀ * |β| := by rwa [one_le_div hu₀] at h
    have hb0 : 0 < |β| := by
      by_contra hc
      have : |β| = 0 := le_antisymm (not_lt.mp hc) hb
      rw [this, mul_zero] at h'
      linarith
    have e : K₀ / (K₀ * |β| / u₀) = u₀ / |β| := by
      field_simp
    rw [e, le_div_iff₀ hb0]
    constructor
    · exact fun h2 => h2.2
    · intro h2
      refine ⟨?_, h2⟩
      have : ρ * |β| ≤ K₀ * |β| := le_trans h2 h'
      exact le_of_mul_le_mul_right this hb0

/-- **THE `G`-SWAP**: for weights `c ≥ 0`, radii `ρ ≥ 1` on a finite `S`, `K u₀ = K₀ u`, `u₀ ≤ u`,
`B ≥ 0` and the ratio bound `∑_{ρ ≤ K₀/s} c ≤ B∑_{ρ ≤ K/s} c` for every `s ∈ [1, K₀]`:
`∑_{ρ ≤ K₀} c ∫_{|β| ≤ u₀/ρ} f ≤ B ∑_{ρ ≤ K} c ∫_{|β| ≤ u/ρ} f` for continuous `f ≥ 0`. -/
theorem swap_bound (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ β, 0 ≤ f β) (S : Finset ℕ)
    (c ρ : ℕ → ℝ) (hc : ∀ m ∈ S, 0 ≤ c m) (hρ : ∀ m ∈ S, 1 ≤ ρ m) (K₀ K u₀ u B : ℝ)
    (hu₀ : 0 < u₀) (huu : u₀ ≤ u) (hK₀ : 1 ≤ K₀) (hB : 0 ≤ B) (hKK : K * u₀ = K₀ * u)
    (hrat : ∀ s : ℝ, 1 ≤ s → s ≤ K₀ →
      ∑ m ∈ S.filter (fun m => ρ m ≤ K₀ / s), c m ≤
        B * ∑ m ∈ S.filter (fun m => ρ m ≤ K / s), c m) :
    ∑ m ∈ S.filter (fun m => ρ m ≤ K₀), c m * ∫ β in (-(u₀ / ρ m))..(u₀ / ρ m), f β ≤
      B * ∑ m ∈ S.filter (fun m => ρ m ≤ K), c m * ∫ β in (-(u / ρ m))..(u / ρ m), f β := by
  classical
  have hu : 0 < u := lt_of_lt_of_le hu₀ huu
  have hK0 : 0 < K₀ := lt_of_lt_of_le one_pos hK₀
  have hρ0 : ∀ m ∈ S.filter (fun m => ρ m ≤ K₀), 0 < ρ m := fun m hm =>
    lt_of_lt_of_le one_pos (hρ m (Finset.mem_filter.mp hm).1)
  have hρ1 : ∀ m ∈ S.filter (fun m => ρ m ≤ K), 0 < ρ m := fun m hm =>
    lt_of_lt_of_le one_pos (hρ m (Finset.mem_filter.mp hm).1)
  rw [sum_int_eq f hf _ c ρ hρ0 u₀ hu₀.le, sum_int_eq f hf _ c ρ hρ1 u hu.le,
    ← integral_const_mul]
  refine integral_mono (int_swap f hf _ c ρ hρ0 u₀)
    ((int_swap f hf _ c ρ hρ1 u).const_mul B) fun β => ?_
  simp only [Finset.filter_filter]
  have hb := abs_nonneg β
  set s := max 1 (K₀ * |β| / u₀) with hs
  by_cases hβ : |β| ≤ u₀
  · -- the two filters are `ρ ≤ K₀/s` and `ρ ≤ K/s`
    have hs1 : 1 ≤ s := le_max_left _ _
    have hsK : s ≤ K₀ := by
      rw [hs]
      refine max_le hK₀ ?_
      rw [div_le_iff₀ hu₀]
      exact mul_le_mul_of_nonneg_left hβ hK0.le
    have hK : 0 < K := by
      have : 0 < K * u₀ := by rw [hKK]; positivity
      exact pos_of_mul_pos_left this hu₀.le
    have hu' : u = K * u₀ / K₀ := by
      rw [hKK]
      field_simp
    have hf1 : (S.filter fun m => ρ m ≤ K₀ ∧ ρ m * |β| ≤ u₀) =
        S.filter fun m => ρ m ≤ K₀ / s := by
      refine Finset.filter_congr fun m hm => ?_
      exact filt_iff (ρ m) K₀ u₀ β hu₀ hK0
    have hf2 : (S.filter fun m => ρ m ≤ K ∧ ρ m * |β| ≤ u) =
        S.filter fun m => ρ m ≤ K / s := by
      refine Finset.filter_congr fun m hm => ?_
      have h1 := filt_iff (ρ m) K u β hu hK
      have hmx : max 1 (K * |β| / u) = s := by
        rw [hs]
        congr 1
        rw [hu']
        field_simp
      rw [hmx] at h1
      exact h1
    rw [hf1, hf2]
    have h := hrat s hs1 hsK
    calc f β * ∑ m ∈ S.filter (fun m => ρ m ≤ K₀ / s), c m
        ≤ f β * (B * ∑ m ∈ S.filter (fun m => ρ m ≤ K / s), c m) :=
          mul_le_mul_of_nonneg_left h (hf0 β)
      _ = B * (f β * ∑ m ∈ S.filter (fun m => ρ m ≤ K / s), c m) := by ring
  · -- no arc of the first family reaches `β`
    push Not at hβ
    have hf1 : (S.filter fun m => ρ m ≤ K₀ ∧ ρ m * |β| ≤ u₀) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun m hm hc2 => ?_
      have h1 := hρ m hm
      have : |β| ≤ ρ m * |β| := le_mul_of_one_le_left hb h1
      linarith [hc2.2]
    rw [hf1, Finset.sum_empty, mul_zero]
    exact mul_nonneg hB (mul_nonneg (hf0 β)
      (Finset.sum_nonneg fun m hm => hc m (Finset.mem_filter.mp hm).1))

end Principia.Common.PSieve
