/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.ZeroFreeA

set_option autoImplicit false

/-!
# `EF.Horizontal` (EF5), part 1: good heights from Landau's lemma

`EF.Horizontal` (`ExplicitSpine.lean`) asks, for `Φ` decaying faster than every power of `|Im s|`
on `−1/2 ≤ Re s ≤ 3/2`, for admissible heights `T ≥ T₀` with small horizontal integrals of
`Ψ = −(L'/L)·Φ·x^s`. Since `Φ` decays super-polynomially it is enough to find, in every window
`[T₀, T₀ + 1]`, a height `T` (no zero ordinate) with `|L'/L(σ ± iT)| ≤ C(T₀ + 2)^n` on the whole
segment `σ ∈ [−1/2, 3/2]` (`GoodHeight`). This module proves that for ANY entire `F` with
`|F| ≤ e^{C(|t|+2)}` on a vertical strip and `|F(σ₀ + it)| ≥ e^{−C(|t|+2)}` (`landauHeights_holds`):

* **Landau's lemma** at `σ₀ ± i(T₀ + 1/2)` with radii `17 < 35/2` (`landau_ball`, from the SW
  bricks `landau_log_deriv` and the Jensen count `sum_m_le_jensen`, `ZeroFreeA.lean`): on the
  quarter ball (radius `17/4 > 4`, which contains both segments) `F'/F = ∑ m_ρ/(z − ρ) + O(T₀)`,
  and `∑ m_ρ ≤ C(2T₀ + 40)/log 2`.
* **Pigeonhole** (`exists_far`): among `n` ordinates some `T ∈ [T₀, T₀ + 1]` is at distance
  `≥ 1/(2(n + 1))` from all of them, so the partial fractions are `O(T₀²)` on the segment.

`LFactor χ` packages what an `L`-function must supply (an entire `F` with growth and anchor, and
`L'/L = F'/F − E` with `|E| ≤ C(|t| + 2)`); `goodHeight_of_factor` turns it into `GoodHeight χ`.
The functions `F` (the completed `L`-function, resp. `ξ` for `q = 1`) are built in
`AgamonHorizLambda.lean`; the composition to `EF.Horizontal` is `AgamonHoriz.lean`.
-/

namespace Principia.Common.TernaryGoldbach.AH

open Complex Metric

/-! ## The named sub-links -/

/-- **`GoodHeight χ`**: every window `[T₀, T₀ + 1]` beyond `T₁` contains a height `T` that is no
ordinate of a zero in the critical strip and at which `|L'/L| ≤ C(T₀ + 2)^n` on both horizontal
segments `σ ± iT`, `σ ∈ [−1/2, 3/2]`. -/
def GoodHeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∃ C : ℝ, ∃ n : ℕ, ∃ T₁ : ℝ, ∀ T₀ : ℝ, T₁ ≤ T₀ → ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧
    (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T) ∧
    ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) (σ + T * I)‖ ≤ C * (T₀ + 2) ^ n ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) (σ - T * I)‖ ≤ C * (T₀ + 2) ^ n

/-- **`LandauHeights` (PROVED: `landauHeights_holds`)**: an entire `F` with
`|F(s)| ≤ e^{C(|Im s|+2)}` on `−40 ≤ Re s ≤ 40`, `|Im s| ≥ T₁`, and
`|F(σ₀ + it)| ≥ e^{−C(|t|+2)}` (`1 ≤ σ₀ ≤ 3`) has, in every window `[T₀, T₀ + 1]` with
`T₀ ≥ T₁ + 40`, a height `T` that is no ordinate of a zero with `0 ≤ Re ρ ≤ 1`, with
`F ≠ 0` and `|F'/F| ≤ C'(T₀ + 2)²` on both segments `σ ± iT`, `σ ∈ [−1/2, 3/2]`. -/
def LandauHeights : Prop :=
  ∀ F : ℂ → ℂ, Differentiable ℂ F → ∀ σ₀ C T₁ : ℝ, 1 ≤ σ₀ → σ₀ ≤ 3 → 0 ≤ C → 0 ≤ T₁ →
    (∀ s : ℂ, -40 ≤ s.re → s.re ≤ 40 → T₁ ≤ |s.im| → ‖F s‖ ≤ Real.exp (C * (|s.im| + 2))) →
    (∀ t : ℝ, T₁ ≤ |t| → Real.exp (-(C * (|t| + 2))) ≤ ‖F (σ₀ + t * I)‖) →
    ∃ C' : ℝ, ∀ T₀ : ℝ, T₁ + 40 ≤ T₀ → ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧
      (∀ ρ : ℂ, F ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≠ T) ∧
      ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 / 2 →
        (F (σ + T * I) ≠ 0 ∧ ‖logDeriv F (σ + T * I)‖ ≤ C' * (T₀ + 2) ^ 2) ∧
        (F (σ - T * I) ≠ 0 ∧ ‖logDeriv F (σ - T * I)‖ ≤ C' * (T₀ + 2) ^ 2)

/-- **`LFactor χ`**: an entire `F` with the growth and anchor of `LandauHeights`, such that on the
strip `−1/2 ≤ Re s ≤ 3/2`, `|Im s| ≥ T₁`, wherever `F ≠ 0`, `L'/L = F'/F − E` with
`|E(s)| ≤ C(|Im s| + 2)`, and every zero of `L` in the critical strip with `|Im ρ| ≥ T₁` is a zero
of `F`. (For `q ≠ 1`: `F = Λ(·, χ)`, `E = Γ'_ℝ/Γ_ℝ(· + a)`; for `q = 1`: `F = s(s − 1)Λ(s)`.) -/
def LFactor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∃ (F E : ℂ → ℂ) (σ₀ C T₁ : ℝ), Differentiable ℂ F ∧ 1 ≤ σ₀ ∧ σ₀ ≤ 3 ∧ 0 ≤ C ∧ 0 ≤ T₁ ∧
    (∀ s : ℂ, -40 ≤ s.re → s.re ≤ 40 → T₁ ≤ |s.im| → ‖F s‖ ≤ Real.exp (C * (|s.im| + 2))) ∧
    (∀ t : ℝ, T₁ ≤ |t| → Real.exp (-(C * (|t| + 2))) ≤ ‖F (σ₀ + t * I)‖) ∧
    (∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → T₁ ≤ |s.im| → F s ≠ 0 →
      logDeriv (DirichletCharacter.LFunction χ) s = logDeriv F s - E s ∧
        ‖E s‖ ≤ C * (|s.im| + 2)) ∧
    (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → T₁ ≤ |ρ.im| →
      F ρ = 0)

/-- **`AllFactor`**: every primitive Dirichlet character (`q = 1` included) has an `LFactor`. -/
def AllFactor : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → LFactor χ

/-! ## Pigeonhole -/

/-- **Pigeonhole**: for a finite `Y ⊆ ℝ` with `n` elements, some `T ∈ [a, a + 1]` is at distance
`≥ 1/(2(n + 1))` from every point of `Y` (the `n + 2` points `a + k/(n + 1)` are `1/(n + 1)`
apart, and each `y` is within `1/(2(n + 1))` of at most one of them). -/
theorem exists_far (Y : Finset ℝ) (a : ℝ) :
    ∃ T : ℝ, a ≤ T ∧ T ≤ a + 1 ∧ ∀ y ∈ Y, 1 / (2 * ((Y.card : ℝ) + 1)) ≤ |T - y| := by
  classical
  have hn1 : (0 : ℝ) < (Y.card : ℝ) + 1 := by positivity
  by_contra hcon
  push Not at hcon
  set P : ℕ → ℝ := fun k => a + (k : ℝ) / ((Y.card : ℝ) + 1) with hP
  have hPmem : ∀ k ∈ Finset.range (Y.card + 2), a ≤ P k ∧ P k ≤ a + 1 := by
    intro k hk
    have hk' : (k : ℝ) ≤ (Y.card : ℝ) + 1 := by
      have := Finset.mem_range.mp hk
      exact_mod_cast Nat.lt_succ_iff.mp this
    have h0 : 0 ≤ (k : ℝ) / ((Y.card : ℝ) + 1) := by positivity
    have h1 : (k : ℝ) / ((Y.card : ℝ) + 1) ≤ 1 := (div_le_one hn1).mpr hk'
    exact ⟨by simp only [hP]; linarith, by simp only [hP]; linarith⟩
  have hch : ∀ k ∈ Finset.range (Y.card + 2), ∃ y ∈ Y,
      |P k - y| < 1 / (2 * ((Y.card : ℝ) + 1)) :=
    fun k hk => hcon (P k) (hPmem k hk).1 (hPmem k hk).2
  choose! f hfY hfδ using hch
  have hinj : Set.InjOn f (Finset.range (Y.card + 2) : Set ℕ) := by
    intro k hk j hj hkj
    by_contra hne
    have h1 := hfδ k hk
    have h2 := hfδ j hj
    rw [hkj] at h1
    have hd : |P k - P j| < 2 * (1 / (2 * ((Y.card : ℝ) + 1))) := by
      calc |P k - P j| = |(P k - f j) - (P j - f j)| := by ring_nf
        _ ≤ |P k - f j| + |P j - f j| := abs_sub _ _
        _ < 1 / (2 * ((Y.card : ℝ) + 1)) + 1 / (2 * ((Y.card : ℝ) + 1)) := add_lt_add h1 h2
        _ = 2 * (1 / (2 * ((Y.card : ℝ) + 1))) := by ring
    have hkj' : (1 : ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
      have hz : (k : ℤ) ≠ (j : ℤ) := by exact_mod_cast hne
      have h3 : (1 : ℤ) ≤ |(k : ℤ) - (j : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hz)
      exact_mod_cast h3
    have hPkj : |P k - P j| = |(k : ℝ) - (j : ℝ)| / ((Y.card : ℝ) + 1) := by
      simp only [hP]
      rw [show a + (k : ℝ) / ((Y.card : ℝ) + 1) - (a + (j : ℝ) / ((Y.card : ℝ) + 1)) =
        ((k : ℝ) - (j : ℝ)) / ((Y.card : ℝ) + 1) by ring, abs_div, abs_of_pos hn1]
    have h2d : 2 * (1 / (2 * ((Y.card : ℝ) + 1))) = 1 / ((Y.card : ℝ) + 1) := by
      field_simp
    rw [hPkj, h2d, div_lt_div_iff_of_pos_right hn1] at hd
    linarith
  have hcard := Finset.card_le_card_of_injOn f (by intro k hk; exact hfY k hk) hinj
  rw [Finset.card_range] at hcard
  omega

/-! ## Geometry -/

/-- `‖z − w‖ ≤ |Re(z − w)| + |Im(z − w)|`. -/
theorem norm_sub_le_re_im (z w : ℂ) : ‖z - w‖ ≤ |z.re - w.re| + |z.im - w.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im (z - w)
  simpa using h

/-- The partial fractions over zeros at vertical distance `≥ δ`: `‖∑ m_ρ/(z − ρ)‖ ≤ ∑ m_ρ / δ`. -/
theorem norm_sum_le_div (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hfar : ∀ ρ ∈ S, δ ≤ |z.im - ρ.im|) :
    ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) / δ := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have hd : δ ≤ ‖z - ρ‖ := by
    have := Complex.abs_im_le_norm (z - ρ)
    rw [Complex.sub_im] at this
    linarith [hfar ρ hρ]
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hd

/-! ## One Landau ball -/

open Principia.Common.SW in
/-- **One Landau ball** (from the SW bricks `landau_log_deriv` and `sum_m_le_jensen`): for an
entire `F` with `|F| ≤ Mb` on `B(c, 35)` and `|F(c)| ≥ ml > 0`, the zeros in `B̄(c, 17)` form a
finite set `S` with multiplicities `m ≥ 1`, `∑ m ≤ log(Mb/ml)/log 2`, and on `B(c, 17/4)` off `S`,
`|F'/F − ∑ m_ρ/(z − ρ)| ≤ 8(log(Mb/ml) + 1)/17`. -/
theorem landau_ball (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (Mb ml : ℝ)
    (hml : 0 < ml) (hmlc : ml ≤ ‖F c‖) (hMb : 1 ≤ Mb) (hfb : ∀ z ∈ ball c 35, ‖F z‖ ≤ Mb) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ), (∀ ρ ∈ S, F ρ = 0) ∧
      (∀ ρ ∈ closedBall c 17, F ρ = 0 → ρ ∈ S) ∧ (∀ ρ ∈ S, 1 ≤ m ρ) ∧
      (∑ ρ ∈ S, (m ρ : ℝ)) ≤ Real.log (Mb / ml) / Real.log 2 ∧
      ∀ z ∈ ball c (17 / 4), (∀ ρ ∈ S, z ≠ ρ) →
        ‖logDeriv F z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ 8 * (Real.log (Mb / ml) + 1) / 17 := by
  have hfc0 : F c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmlc
    linarith
  obtain ⟨S, m, hSz, hm, hcomp, hbound⟩ := landau_log_deriv F c 35 17 Mb ml (by norm_num)
    (by norm_num) hF.differentiableOn hfb hml hmlc
  have hJ := sum_m_le_jensen F c 17 34 Mb (by norm_num) (by norm_num) hMb
    (fun z _ => hF.analyticAt z) hfc0
    (fun z hz => hfb z (closedBall_subset_ball (by norm_num) (sphere_subset_closedBall hz)))
    S m hSz hm
  have h34 : (34 : ℝ) / 17 = 2 := by norm_num
  rw [h34] at hJ
  have hfcpos : 0 < ‖F c‖ := lt_of_lt_of_le hml hmlc
  have hMbpos : 0 < Mb := by linarith
  have hlt : Real.log (Mb / ‖F c‖) ≤ Real.log (Mb / ml) :=
    Real.log_le_log (div_pos hMbpos hfcpos) (div_le_div_of_nonneg_left hMbpos.le hml hmlc)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ' : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ Real.log (Mb / ml) / Real.log 2 :=
    hJ.trans (div_le_div_of_nonneg_right hlt hl2.le)
  have hmpos : ∀ ρ ∈ S, 1 ≤ m ρ := by
    intro ρ hρ
    have hFρ : F ρ = 0 := (hSz ρ hρ).2
    have hordtop : analyticOrderAt F ρ ≠ ⊤ := by
      intro htop
      have hev := analyticOrderAt_eq_top.mp htop
      have hanalU : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
      have hzero := hanalU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ ρ) hev
      exact hfc0 (hzero (Set.mem_univ c))
    have hordzero : analyticOrderAt F ρ ≠ 0 := by
      intro h0
      rcases analyticOrderAt_eq_zero.mp h0 with h | h
      · exact h (hF.analyticAt ρ)
      · exact h hFρ
    rw [hm ρ hρ, analyticOrderNatAt]
    apply Nat.one_le_iff_ne_zero.mpr
    intro h0
    rcases ENat.toNat_eq_zero.mp h0 with h | h
    · exact hordzero h
    · exact hordtop h
  exact ⟨S, m, fun ρ hρ => (hSz ρ hρ).2, hcomp, hmpos, hJ', hbound⟩

/-- **The Landau ball at `σ₀ + it`** under the growth/anchor hypotheses of `LandauHeights`:
`Mb = e^{C(|t|+37)}` on `B(σ₀ + it, 35)` (which lies in `−40 ≤ Re ≤ 40`, `|Im| ≥ |t| − 35`),
`ml = e^{−C(|t|+2)}`, so `log(Mb/ml) = C(2|t| + 39)`. -/
theorem ball_data (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ₀ C T₁ : ℝ) (h1 : 1 ≤ σ₀)
    (h3 : σ₀ ≤ 3) (hC : 0 ≤ C)
    (hgr : ∀ s : ℂ, -40 ≤ s.re → s.re ≤ 40 → T₁ ≤ |s.im| →
      ‖F s‖ ≤ Real.exp (C * (|s.im| + 2)))
    (han : ∀ t : ℝ, T₁ ≤ |t| → Real.exp (-(C * (|t| + 2))) ≤ ‖F (σ₀ + t * I)‖)
    (t : ℝ) (ht : T₁ + 40 ≤ |t|) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ), (∀ ρ ∈ S, F ρ = 0) ∧
      (∀ ρ ∈ closedBall ((σ₀ : ℂ) + t * I) 17, F ρ = 0 → ρ ∈ S) ∧ (∀ ρ ∈ S, 1 ≤ m ρ) ∧
      (∑ ρ ∈ S, (m ρ : ℝ)) ≤ C * (2 * |t| + 39) / Real.log 2 ∧
      ∀ z ∈ ball ((σ₀ : ℂ) + t * I) (17 / 4), (∀ ρ ∈ S, z ≠ ρ) →
        ‖logDeriv F z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ 8 * (C * (2 * |t| + 39) + 1) / 17 := by
  have hcre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
  have hcim : ((σ₀ : ℂ) + t * I).im = t := by simp
  have hlog : Real.log (Real.exp (C * (|t| + 37)) / Real.exp (-(C * (|t| + 2)))) =
      C * (2 * |t| + 39) := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  have hfb : ∀ z ∈ ball ((σ₀ : ℂ) + t * I) 35, ‖F z‖ ≤ Real.exp (C * (|t| + 37)) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre : |z.re - σ₀| < 35 := by
      have := Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + t * I))
      rw [Complex.sub_re, hcre] at this
      linarith
    have him : |z.im - t| < 35 := by
      have := Complex.abs_im_le_norm (z - ((σ₀ : ℂ) + t * I))
      rw [Complex.sub_im, hcim] at this
      linarith
    obtain ⟨hre1, hre2⟩ := abs_lt.mp hre
    have hz1 : |t| - 35 ≤ |z.im| := by
      have := abs_sub_abs_le_abs_sub t z.im
      rw [abs_sub_comm] at this
      linarith
    have hz2 : |z.im| ≤ |t| + 35 := by
      have := abs_sub_abs_le_abs_sub z.im t
      linarith
    refine (hgr z (by linarith) (by linarith) (by linarith)).trans ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hC)
  have hml : 0 < Real.exp (-(C * (|t| + 2))) := Real.exp_pos _
  have hmlc := han t (by linarith)
  have hMb : 1 ≤ Real.exp (C * (|t| + 37)) :=
    Real.one_le_exp (mul_nonneg hC (by positivity))
  obtain ⟨S, m, h1', h2', h3', h4', h5'⟩ := landau_ball F hF _ _ _ hml hmlc hMb hfb
  rw [hlog] at h4' h5'
  exact ⟨S, m, h1', h2', h3', h4', h5'⟩

/-! ## Good heights -/

/-- A point of a segment `σ + iT` (`σ ∈ [−1/2, 3/2]`, `|T − h| ≤ 1/2`) lies in `B(σ₀ + ih, 17/4)`
(`|σ − σ₀| ≤ 7/2` since `1 ≤ σ₀ ≤ 3`). -/
theorem mem_ball_seg {σ σ₀ T h : ℝ} (hσ1 : -1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) (h1 : 1 ≤ σ₀)
    (h3 : σ₀ ≤ 3) (hT : |T - h| ≤ 1 / 2) :
    (σ : ℂ) + T * I ∈ ball ((σ₀ : ℂ) + h * I) (17 / 4) := by
  rw [mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (norm_sub_le_re_im _ _) ?_
  have hre : ((σ : ℂ) + T * I).re = σ := by simp
  have him : ((σ : ℂ) + T * I).im = T := by simp
  have hre' : ((σ₀ : ℂ) + h * I).re = σ₀ := by simp
  have him' : ((σ₀ : ℂ) + h * I).im = h := by simp
  rw [hre, him, hre', him']
  have e1 : |σ - σ₀| ≤ 7 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- A zero `ρ` with `0 ≤ Re ρ ≤ 1` and `|Im ρ − h| ≤ 1/2` lies in `B̄(σ₀ + ih, 17)`. -/
theorem mem_closedBall_zero {ρ : ℂ} {σ₀ h : ℝ} (h1 : 1 ≤ σ₀) (h3 : σ₀ ≤ 3) (h0 : 0 ≤ ρ.re)
    (h1' : ρ.re ≤ 1) (hT : |ρ.im - h| ≤ 1 / 2) : ρ ∈ closedBall ((σ₀ : ℂ) + h * I) 17 := by
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_sub_le_re_im _ _).trans ?_
  have hre' : ((σ₀ : ℂ) + h * I).re = σ₀ := by simp
  have him' : ((σ₀ : ℂ) + h * I).im = h := by simp
  rw [hre', him']
  have e1 : |ρ.re - σ₀| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **The bound on one segment point**: off the zeros (vertical distance `≥ δ` from all of `S`),
`F(z) ≠ 0` and `|F'/F(z)| ≤ B + K/δ`, given the Landau decomposition with remainder `B` on
`B(c, 17/4)` and `∑ m ≤ K`. -/
theorem segment_bound (F : ℂ → ℂ) (S : Finset ℂ) (m : ℂ → ℕ) (c z : ℂ) (K δ B : ℝ)
    (hδ : 0 < δ) (hz : z ∈ ball c (17 / 4))
    (hcomp : ∀ ρ ∈ closedBall c 17, F ρ = 0 → ρ ∈ S) (hsum : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ K)
    (hb : ∀ w ∈ ball c (17 / 4), (∀ ρ ∈ S, w ≠ ρ) →
      ‖logDeriv F w - ∑ ρ ∈ S, (m ρ : ℂ) / (w - ρ)‖ ≤ B)
    (hfar : ∀ ρ ∈ S, δ ≤ |z.im - ρ.im|) :
    F z ≠ 0 ∧ ‖logDeriv F z‖ ≤ B + K / δ := by
  have hzS : ∀ ρ ∈ S, z ≠ ρ := by
    intro ρ hρ hzρ
    have := hfar ρ hρ
    rw [← hzρ, sub_self, abs_zero] at this
    linarith
  refine ⟨fun h0 => hzS z (hcomp z (ball_subset_closedBall
    (ball_subset_ball (by norm_num) hz)) h0) rfl, ?_⟩
  have hb1 := hb z hz hzS
  have hb2 := norm_sum_le_div S m z δ hδ hfar
  have hb3 : (∑ ρ ∈ S, (m ρ : ℝ)) / δ ≤ K / δ := div_le_div_of_nonneg_right hsum hδ.le
  calc ‖logDeriv F z‖ = ‖(logDeriv F z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)) +
        ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv F z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ +
        ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ := norm_add_le _ _
    _ ≤ B + K / δ := by linarith

/-- The numerical bookkeeping of `landauHeights_holds`: with `K = C(2(T₀ + 1/2) + 39)/log 2`,
`log 2 > 0.69` and `T₀ ≥ 40`, `K ≤ 40C(T₀ + 2)` and the remainder plus `K·2(n + 1)`, `n ≤ 2K`, is
at most `(6400C² + 100C + 1)(T₀ + 2)²`. -/
theorem final_bound {C T₀ y : ℝ} (hC : 0 ≤ C) (hT₀ : 40 ≤ T₀) (hy0 : 0 ≤ y)
    (hy : y ≤ 2 * (C * (2 * (T₀ + 1 / 2) + 39) / Real.log 2)) :
    8 * (C * (2 * (T₀ + 1 / 2) + 39) + 1) / 17 +
      C * (2 * (T₀ + 1 / 2) + 39) / Real.log 2 / (1 / (2 * (y + 1))) ≤
      (6400 * C ^ 2 + 100 * C + 1) * (T₀ + 2) ^ 2 := by
  set K : ℝ := C * (2 * (T₀ + 1 / 2) + 39) / Real.log 2 with hK
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg hC (by linarith)) hl2p.le
  have hKle : K ≤ 40 * C * (T₀ + 2) := by
    rw [hK, div_le_iff₀ hl2p]
    have hCu : 0 ≤ C * (T₀ + 2) := mul_nonneg hC (by linarith)
    have hm := mul_le_mul_of_nonneg_left hl2.le hCu
    have hm2 : 0 ≤ C * (T₀ + 2 - 42) := mul_nonneg hC (by linarith)
    nlinarith
  have hKd : K / (1 / (2 * (y + 1))) = K * (2 * (y + 1)) := by
    field_simp
  rw [hKd]
  have hA : K * (2 * (y + 1)) ≤ K * (2 * (2 * K + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have hCT : 0 ≤ 40 * C * (T₀ + 2) := mul_nonneg (by linarith) (by linarith)
  have hB : K * (2 * (2 * K + 1)) ≤
      (40 * C * (T₀ + 2)) * (2 * (2 * (40 * C * (T₀ + 2)) + 1)) :=
    mul_le_mul hKle (by linarith) (by linarith) hCT
  have hC1 : C * (2 * (T₀ + 1 / 2) + 39) ≤ 20 * C * (T₀ + 2) := by nlinarith
  have hC2 : C * (T₀ + 2) ≤ C * (T₀ + 2) ^ 2 := by
    have : 0 ≤ C * (T₀ + 2) * (T₀ + 2 - 1) :=
      mul_nonneg (mul_nonneg hC (by linarith)) (by linarith)
    nlinarith
  have hC3 : (1 : ℝ) ≤ (T₀ + 2) ^ 2 := by nlinarith
  nlinarith

/-- **`LandauHeights` PROVED**: Landau balls at `σ₀ ± i(T₀ + 1/2)`, pigeonhole on the
`≤ 2C(2T₀ + 40)/log 2` ordinates of their zeros. -/
theorem landauHeights_holds : LandauHeights := by
  intro F hF σ₀ C T₁ h1 h3 hC hT₁ hgr han
  refine ⟨6400 * C ^ 2 + 100 * C + 1, fun T₀ hT₀ => ?_⟩
  have hhpos : 0 < T₀ + 1 / 2 := by linarith
  have habs1 : |T₀ + 1 / 2| = T₀ + 1 / 2 := abs_of_pos hhpos
  have habs2 : |-(T₀ + 1 / 2)| = T₀ + 1 / 2 := by rw [abs_neg, habs1]
  obtain ⟨St, mt, -, hStc, hmt1, hmts, hStb⟩ :=
    ball_data F hF σ₀ C T₁ h1 h3 hC hgr han (T₀ + 1 / 2) (by rw [habs1]; linarith)
  obtain ⟨Sb, mb, -, hSbc, hmb1, hmbs, hSbb⟩ :=
    ball_data F hF σ₀ C T₁ h1 h3 hC hgr han (-(T₀ + 1 / 2)) (by rw [habs2]; linarith)
  rw [habs1] at hmts hStb
  rw [habs2] at hmbs hSbb
  have hcard : ∀ (S : Finset ℂ) (m : ℂ → ℕ), (∀ ρ ∈ S, 1 ≤ m ρ) →
      (S.card : ℝ) ≤ ∑ ρ ∈ S, (m ρ : ℝ) := by
    intro S m hm
    have := Finset.card_nsmul_le_sum S m 1 hm
    simp only [smul_eq_mul, mul_one] at this
    exact_mod_cast this
  have hYcard : (((St ∪ Sb).image (fun ρ => |ρ.im|)).card : ℝ) ≤
      2 * (C * (2 * (T₀ + 1 / 2) + 39) / Real.log 2) := by
    have h1' : ((St ∪ Sb).image (fun ρ => |ρ.im|)).card ≤ St.card + Sb.card :=
      (Finset.card_image_le).trans (Finset.card_union_le _ _)
    have h2' : (((St ∪ Sb).image (fun ρ => |ρ.im|)).card : ℝ) ≤ St.card + Sb.card := by
      exact_mod_cast h1'
    have h3' := (hcard St mt hmt1).trans hmts
    have h4' := (hcard Sb mb hmb1).trans hmbs
    linarith
  obtain ⟨T, hT0, hT1, hfar⟩ := exists_far ((St ∪ Sb).image (fun ρ => |ρ.im|)) T₀
  set n : ℝ := (((St ∪ Sb).image (fun ρ => |ρ.im|)).card : ℝ) with hn
  have hδpos : 0 < 1 / (2 * (n + 1)) := by positivity
  have hTpos : 0 ≤ T := by linarith
  have hfarSt : ∀ ρ ∈ St, 1 / (2 * (n + 1)) ≤ |T - ρ.im| := by
    intro ρ hρ
    have h1' := hfar _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hρ))
    have h2' := abs_abs_sub_abs_le_abs_sub T ρ.im
    rw [abs_of_nonneg hTpos] at h2'
    linarith
  have hfarSb : ∀ ρ ∈ Sb, 1 / (2 * (n + 1)) ≤ |-T - ρ.im| := by
    intro ρ hρ
    have h1' := hfar _ (Finset.mem_image_of_mem _ (Finset.mem_union_right _ hρ))
    have h2' := abs_abs_sub_abs_le_abs_sub T (-ρ.im)
    rw [abs_of_nonneg hTpos, abs_neg] at h2'
    have h3' : |-T - ρ.im| = |T - -ρ.im| := by
      rw [show -T - ρ.im = -(T - -ρ.im) by ring, abs_neg]
    rw [h3']
    linarith
  have hfin := final_bound hC (by linarith) (by positivity) hYcard
  refine ⟨T, hT0, hT1, ?_, fun σ hσ1 hσ2 => ?_⟩
  · -- no zero ordinate
    intro ρ hρ h0 h1' hT
    rcases le_or_gt 0 ρ.im with him | him
    · have hρim : ρ.im = T := by rw [← hT, abs_of_nonneg him]
      have hmem := mem_closedBall_zero (h := T₀ + 1 / 2) h1 h3 h0 h1'
        (by rw [hρim]; exact abs_le.mpr ⟨by linarith, by linarith⟩)
      have h2' := hfarSt ρ (hStc ρ hmem hρ)
      rw [hρim, sub_self, abs_zero] at h2'
      linarith
    · have hρim : ρ.im = -T := by rw [← hT, abs_of_neg him, neg_neg]
      have hmem := mem_closedBall_zero (h := -(T₀ + 1 / 2)) h1 h3 h0 h1'
        (by rw [hρim]; exact abs_le.mpr ⟨by linarith, by linarith⟩)
      have h2' := hfarSb ρ (hSbc ρ hmem hρ)
      rw [hρim, sub_neg_eq_add, neg_add_cancel, abs_zero] at h2'
      linarith
  · constructor
    · have hz := mem_ball_seg (T := T) (h := T₀ + 1 / 2) hσ1 hσ2 h1 h3
        (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hzim : ((σ : ℂ) + T * I).im = T := by simp
      obtain ⟨hne, hb⟩ := segment_bound F St mt _ _ _ _ _ hδpos hz hStc hmts hStb
        (fun ρ hρ => by rw [hzim]; exact hfarSt ρ hρ)
      exact ⟨hne, hb.trans hfin⟩
    · have hz := mem_ball_seg (T := -T) (h := -(T₀ + 1 / 2)) hσ1 hσ2 h1 h3
        (abs_le.mpr ⟨by linarith, by linarith⟩)
      have heq : (σ : ℂ) + ((-T : ℝ) : ℂ) * I = (σ : ℂ) - T * I := by push_cast; ring
      rw [heq] at hz
      have hzim : ((σ : ℂ) - T * I).im = -T := by simp
      obtain ⟨hne, hb⟩ := segment_bound F Sb mb _ _ _ _ _ hδpos hz hSbc hmbs hSbb
        (fun ρ hρ => by rw [hzim]; exact hfarSb ρ hρ)
      exact ⟨hne, hb.trans hfin⟩

/-- **`GoodHeight` from a factorization** (composition): `LandauHeights` applied to `F`, then
`|L'/L| ≤ |F'/F| + |E| ≤ C'(T₀ + 2)² + C(T₀ + 3)`. -/
theorem goodHeight_of_factor (hL : LandauHeights) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (h : LFactor χ) : GoodHeight χ := by
  obtain ⟨F, E, σ₀, C, T₁, hF, h1, h3, hC, hT₁, hgr, han, hsplit, hzero⟩ := h
  obtain ⟨C', hC'⟩ := hL F hF σ₀ C T₁ h1 h3 hC hT₁ hgr han
  refine ⟨C' + 2 * C, 2, T₁ + 40, fun T₀ hT₀ => ?_⟩
  obtain ⟨T, hT0, hT1, hz, hb⟩ := hC' T₀ hT₀
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hTm : |-T| = T := by rw [abs_neg, hTabs]
  refine ⟨T, hT0, hT1, fun ρ hρ h0 h1' hT => ?_, fun σ hσ1 hσ2 => ?_⟩
  · have hρim : T₁ ≤ |ρ.im| := by rw [hT]; linarith
    exact hz ρ (hzero ρ hρ h0 h1' hρim) h0.le h1'.le hT
  · obtain ⟨⟨hne1, hb1⟩, ⟨hne2, hb2⟩⟩ := hb σ hσ1 hσ2
    have hpos : 0 ≤ (T₀ + 2) ^ 2 - (T₀ + 3) := by nlinarith
    have hre1 : ((σ : ℂ) + T * I).re = σ := by simp
    have him1 : ((σ : ℂ) + T * I).im = T := by simp
    have hre2 : ((σ : ℂ) - T * I).re = σ := by simp
    have him2 : ((σ : ℂ) - T * I).im = -T := by simp
    obtain ⟨heq1, hE1⟩ := hsplit _ (by rw [hre1]; exact hσ1) (by rw [hre1]; exact hσ2)
      (by rw [him1, hTabs]; linarith) hne1
    obtain ⟨heq2, hE2⟩ := hsplit _ (by rw [hre2]; exact hσ1) (by rw [hre2]; exact hσ2)
      (by rw [him2, hTm]; linarith) hne2
    rw [him1, hTabs] at hE1
    rw [him2, hTm] at hE2
    have hCT : C * (T + 2) ≤ 2 * C * (T₀ + 2) ^ 2 := by nlinarith
    constructor
    · rw [heq1]
      calc _ ≤ ‖logDeriv F ((σ : ℂ) + T * I)‖ + ‖E ((σ : ℂ) + T * I)‖ := norm_sub_le _ _
        _ ≤ (C' + 2 * C) * (T₀ + 2) ^ 2 := by linarith
    · rw [heq2]
      calc _ ≤ ‖logDeriv F ((σ : ℂ) - T * I)‖ + ‖E ((σ : ℂ) - T * I)‖ := norm_sub_le _ _
        _ ≤ (C' + 2 * C) * (T₀ + 2) ^ 2 := by linarith

/-- **Good heights for every primitive character, from `AllFactor`** (composition). -/
theorem goodHeights_of_all (h : AllFactor) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) : GoodHeight χ :=
  goodHeight_of_factor landauHeights_holds (h q χ hχ)

end Principia.Common.TernaryGoldbach.AH
