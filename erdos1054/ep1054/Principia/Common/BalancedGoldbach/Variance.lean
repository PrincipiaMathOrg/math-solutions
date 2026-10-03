/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.Reduction

/-!
# Balanced Goldbach, `Variance`: the circle-method variance on the upper half `N < n < 2N`

The ported circle method (`Principia.Common.Goldbach`) controls the Λ-weighted pair count

  `R_N(n) = ∑_{a, b < N, a + b = n} Λ(a) Λ(b)`

against the model `coeffModel N P Q n` **for every `n < 2N`** (`core_variance`), but its reduction
only ever reads the lower half `n ≤ N`, where `R_N(n)` counts *all* Goldbach pairs of `n`. On the
upper half the same count is **range-restricted for free**: `a, b < N` and `a + b = n` force
`a, b ∈ (n − N, N)`. For `4N ≤ 3n` both summands lie in `(n/4, 3n/4)` — a *balanced* pair. So the
balanced problem needs no new exponential sum, no new minor arc and no new major-arc model; it
needs only the major-arc comparison `harc` re-run on `N < n < 2N`, where its main term is
`𝔖(n) · r_N(n)`, and `r_N(n) ≥ 2N − 1 − n` on the upper half (`Balanced.kernel_ge`).

Both legs of `harc` are already stated in the generality this needs:

* the arc-tail leg rests on `arcTailError_bessel N P Q M` — a Bessel inequality valid for **every**
  `M` — so it holds on `range (2N)` with the same right-hand side (`arcTail_upper`);
* the truncation leg `trunc_sub_error` is stated for an arbitrary weight `rN X n` on the dyadic
  block `(X/2, X]`; at `X = 2N` with `rN X n = r_{X/2}(n)` that block is `(N, 2N]`
  (`trunc_upper`).

With `core_variance` (the minor and major arcs, through Siegel–Walfisz) this gives
`variance_upper`: `∑_{N<n<2N} (R_N(n) − 𝔖(n) r_N(n))² ≤ ε N³` for all large `N`.

Nothing in `Principia.Common.Goldbach` is edited.
-/

set_option autoImplicit false

open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory
open Principia.Common.SW (MediumPNTBound)

namespace Principia.Common.BalancedGoldbach

open Principia.Common.Goldbach
open Principia.Common.Goldbach.MinSum
open Principia.Common.Goldbach.MinorArc
open Principia.Common.Goldbach.MajorArcMainTerm
open scoped ArithmeticFunction

/-- `R_N(n)`: the Λ-weighted count of ordered pairs `(a, b) ∈ [0, N)²` with `a + b = n`. -/
noncomputable def pairWeight (N n : ℕ) : ℝ :=
  ∑ pr ∈ (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n),
    Λ pr.1 * Λ pr.2

/-- `r_N(n)`: the number of ordered pairs `(a, b) ∈ [0, N)²` with `a + b = n`. -/
noncomputable def kernel (N n : ℕ) : ℝ :=
  (((Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n)).card : ℝ)

/-- The Hardy–Littlewood main term `𝔖(n) · r_N(n)` at window length `N`. -/
noncomputable def mainTermN (N n : ℕ) : ℝ := (∑' q, Tarithv n q) * kernel N n

/-- **Minor and major arcs** (`core_variance`, in real form): the weighted pair count is close in
`ℓ²` to the real part of the circle-method model on the whole range `n < 2N`. -/
theorem core_upper (hPNT : MediumPNTBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.range (2 * N),
        (pairWeight N n - (coeffModel N (Nat.floor ((Real.log N) ^ 9))
          (N / Nat.floor ((Real.log N) ^ 9)) n).re) ^ 2 ≤ ε * (N : ℝ) ^ 3 := by
  obtain ⟨N₀, hN₀⟩ := core_variance hPNT ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  refine le_trans ?_ (hN₀ N hN)
  refine Finset.sum_le_sum fun n _ => ?_
  have hcast : (∑ pr ∈ (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n),
      ((Λ pr.1 : ℝ) : ℂ) * ((Λ pr.2 : ℝ) : ℂ)) = ((pairWeight N n : ℝ) : ℂ) := by
    rw [pairWeight, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun pr _ => ?_
    push_cast
    ring
  rw [hcast]
  set z := coeffModel N (Nat.floor ((Real.log N) ^ 9)) (N / Nat.floor ((Real.log N) ^ 9)) n
  have h1 : |((pairWeight N n : ℂ) - z).re| ≤ ‖(pairWeight N n : ℂ) - z‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.ofReal_re] at h1
  calc (pairWeight N n - z.re) ^ 2 = |pairWeight N n - z.re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖(pairWeight N n : ℂ) - z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- **The arc-tail leg on the whole range `n < 2N`.** `h1_arcTail`'s argument with the Bessel
inequality `arcTailError_bessel N P Q (2N)` in place of `arcTailError_bessel N P Q N`: the
right-hand side `∫_{(0,1]} ‖Φ − Ψ_ideal‖²` does not depend on how many coefficients are taken. -/
theorem arcTail_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.range (2 * N),
        ((coeffModel N (Nat.floor ((Real.log N) ^ 9)) (N / Nat.floor ((Real.log N) ^ 9)) n).re
          - kernel N n * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log N) ^ 9)), Tarithv n q) ^ 2
        ≤ ε * (N : ℝ) ^ 3 := by
  obtain ⟨N₀, hN₀⟩ := arc_tail_rhs_small ε hε
  obtain ⟨N₂₇, hN₂₇⟩ := polylog_le_self 27 2 (by norm_num)
  refine ⟨max 4 (max N₀ N₂₇), fun N hN => ?_⟩
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂₇ : N₂₇ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  set L : ℝ := Real.log N with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ (N : ℝ) := by
          have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
          linarith
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    exact Nat.le_floor (by exact_mod_cast one_le_pow₀ hL1)
  have hPleL9 : (P : ℝ) ≤ L ^ 9 := Nat.floor_le (by positivity)
  have h2L27 : 2 * L ^ 27 ≤ (N : ℝ) := hN₂₇ N hNN₂₇
  have h2P3 : 2 * P ^ 3 ≤ N := by
    have hreal : 2 * (P : ℝ) ^ 3 ≤ (N : ℝ) := by
      have hL927 : (L ^ 9) ^ 3 = L ^ 27 := by ring
      have h1 : (P : ℝ) ^ 3 ≤ (L ^ 9) ^ 3 := pow_le_pow_left₀ (by positivity) hPleL9 3
      rw [hL927] at h1
      linarith
    exact_mod_cast hreal
  set Q : ℕ := N / P with hQdef
  have hQ2 : 2 ≤ Q := by
    rw [hQdef, Nat.le_div_iff_mul_le (by omega : 0 < P)]
    have hPP3 : P ≤ P ^ 3 := Nat.le_self_pow (by norm_num) P
    calc 2 * P ≤ 2 * P ^ 3 := Nat.mul_le_mul (le_refl 2) hPP3
      _ ≤ N := h2P3
  have hPQ : 2 * P ^ 2 < Q + 1 := by
    have h1 : 2 * P ^ 2 ≤ Q := by
      rw [hQdef, Nat.le_div_iff_mul_le (by omega : 0 < P)]
      nlinarith [h2P3]
    omega
  have hpt : ∀ n : ℕ,
      ((coeffModel N P Q n).re - kernel N n * ∑ q ∈ Finset.Icc 1 P, Tarithv n q) ^ 2
      ≤ ‖coeffModel N P Q n
          - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
            * singSeriesC P n‖ ^ 2 := by
    intro n
    set z : ℂ := coeffModel N P Q n
      - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
        * singSeriesC P n with hzdef
    have hS : (singSeriesC P n).re = ∑ q ∈ Finset.Icc 1 P, Tarithv n q := by
      rw [singSeriesC_re]
      exact Finset.sum_congr rfl fun q _ => (Tarithv_apply n q).symm
    have hre : (coeffModel N P Q n).re - kernel N n * ∑ q ∈ Finset.Icc 1 P, Tarithv n q
        = z.re := by
      rw [hzdef, Complex.sub_re, ← hS, kernel]
      congr 1
      rw [show (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
          = ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ) : ℂ)
        from by push_cast; rfl]
      rw [Complex.re_ofReal_mul]
    rw [hre]
    calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  calc ∑ n ∈ Finset.range (2 * N),
        ((coeffModel N P Q n).re - kernel N n * ∑ q ∈ Finset.Icc 1 P, Tarithv n q) ^ 2
      ≤ ∑ n ∈ Finset.range (2 * N),
          ‖coeffModel N P Q n
            - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
              * singSeriesC P n‖ ^ 2 := Finset.sum_le_sum fun n _ => hpt n
    _ ≤ ∫ α in Set.Ioc (0 : ℝ) 1, ‖PhiArc N P Q α - PsiIdeal N P α‖ ^ 2 :=
        arcTailError_bessel N P Q (2 * N)
    _ = ∫ α in Set.Ioc (0 : ℝ) 1, ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro α _
        dsimp only
        rw [norm_sub_rev]
    _ ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2))
        + 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 :=
        psi_sub_phi_L2_total N P Q hP1 hQ2 hPQ
    _ ≤ ε * (N : ℝ) ^ 3 := hN₀ N hNN₀

/-- `X ↦ ⌊(log (X/2))⁹⌋₊` tends to infinity (the truncation level at window length `X/2`). -/
theorem Phalf_tendsto :
    Tendsto (fun X : ℕ => Nat.floor ((Real.log ((X / 2 : ℕ) : ℝ)) ^ 9)) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (Filter.tendsto_pow_atTop (by norm_num : 9 ≠ 0)).comp
  apply Real.tendsto_log_atTop.comp
  exact tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop (by norm_num))

/-- **The truncation leg on the upper half `(N, 2N]`.** `trunc_sub_error` at `X = 2N`, with the
weight `r_{X/2}(n)` and the cutoff `⌊(log (X/2))⁹⌋₊`: the singular-series tail beyond
`P = ⌊(log N)⁹⌋₊` costs `≤ ε N³` in `ℓ²`. -/
theorem trunc_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Ioc N (2 * N),
        (kernel N n * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log N) ^ 9)), Tarithv n q
          - mainTermN N n) ^ 2 ≤ ε * (N : ℝ) ^ 3 := by
  have hrN : ∀ X : ℕ, ∀ n ∈ Finset.Ioc (X / 2) X,
      (kernel (X / 2) n) ^ 2 ≤ ((X : ℝ) + 1) ^ 2 := by
    intro X n _
    have h1 : kernel (X / 2) n ≤ ((X / 2 : ℕ) : ℝ) := kernel_card_le (X / 2) n
    have h0 : 0 ≤ kernel (X / 2) n := Nat.cast_nonneg _
    have h2 : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) + 1 := by
      have h3 : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.div_le_self X 2
      linarith
    exact pow_le_pow_left₀ h0 (h1.trans h2) 2
  obtain ⟨X₀, hX₀⟩ := trunc_sub_error (fun X n => kernel (X / 2) n)
    (fun X : ℕ => Nat.floor ((Real.log ((X / 2 : ℕ) : ℝ)) ^ 9)) hrN Phalf_tendsto
    (ε / 8) (by positivity)
  refine ⟨X₀, fun N hN => ?_⟩
  have hX := hX₀ (2 * N) (by omega)
  have hdiv : 2 * N / 2 = N := by omega
  simp only [hdiv] at hX
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [hcast] at hX
  calc ∑ n ∈ Finset.Ioc N (2 * N),
        (kernel N n * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log N) ^ 9)), Tarithv n q
          - mainTermN N n) ^ 2
      = ∑ n ∈ Finset.Ioc N (2 * N),
          ((∑' q, (if Nat.floor ((Real.log N) ^ 9) < q then Tarithv n q else 0))
            * kernel N n) ^ 2 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        rw [mainTermN, singSeries_tail' _ n hn1]
        ring
    _ ≤ ε / 8 * (2 * (N : ℝ)) ^ 3 := hX
    _ = ε * (N : ℝ) ^ 3 := by ring

/-- Three-term `ℓ²` triangle inequality: `(a − d)² ≤ 3((a − b)² + (b − c)² + (c − d)²)`,
summed. -/
theorem sum_sq_triangle3 (s : Finset ℕ) (A B C D : ℕ → ℝ) (e₁ e₂ e₃ : ℝ)
    (h₁ : ∑ n ∈ s, (A n - B n) ^ 2 ≤ e₁) (h₂ : ∑ n ∈ s, (B n - C n) ^ 2 ≤ e₂)
    (h₃ : ∑ n ∈ s, (C n - D n) ^ 2 ≤ e₃) :
    ∑ n ∈ s, (A n - D n) ^ 2 ≤ 3 * e₁ + 3 * e₂ + 3 * e₃ := by
  have hpt : ∀ n ∈ s, (A n - D n) ^ 2
      ≤ 3 * (A n - B n) ^ 2 + 3 * (B n - C n) ^ 2 + 3 * (C n - D n) ^ 2 := by
    intro n _
    nlinarith [sq_nonneg (A n - B n - (B n - C n)), sq_nonneg (B n - C n - (C n - D n)),
      sq_nonneg (A n - B n - (C n - D n))]
  calc ∑ n ∈ s, (A n - D n) ^ 2
      ≤ ∑ n ∈ s, (3 * (A n - B n) ^ 2 + 3 * (B n - C n) ^ 2 + 3 * (C n - D n) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 3 * ∑ n ∈ s, (A n - B n) ^ 2 + 3 * ∑ n ∈ s, (B n - C n) ^ 2
          + 3 * ∑ n ∈ s, (C n - D n) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
    _ ≤ 3 * e₁ + 3 * e₂ + 3 * e₃ := by linarith

/-- **The balanced-window variance.** For every `ε > 0` and all large `N`,
`∑_{N<n<2N} (R_N(n) − 𝔖(n) r_N(n))² ≤ ε N³`: `core_upper` (minor and major arcs),
`arcTail_upper` and `trunc_upper` (the two legs of the major-arc comparison), and
`sum_sq_triangle3`. -/
theorem variance_upper (hPNT : MediumPNTBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Ioo N (2 * N), (pairWeight N n - mainTermN N n) ^ 2 ≤ ε * (N : ℝ) ^ 3 := by
  obtain ⟨N₁, h1⟩ := core_upper hPNT (ε / 9) (by positivity)
  obtain ⟨N₂, h2⟩ := arcTail_upper (ε / 9) (by positivity)
  obtain ⟨N₃, h3⟩ := trunc_upper (ε / 9) (by positivity)
  refine ⟨max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hsub1 : Finset.Ioo N (2 * N) ⊆ Finset.range (2 * N) := by
    intro n hn
    rw [Finset.mem_Ioo] at hn
    rw [Finset.mem_range]
    omega
  have hsub2 : Finset.Ioo N (2 * N) ⊆ Finset.Ioc N (2 * N) := Finset.Ioo_subset_Ioc_self
  have key := sum_sq_triangle3 (Finset.Ioo N (2 * N)) (fun n => pairWeight N n)
    (fun n => (coeffModel N (Nat.floor ((Real.log N) ^ 9))
      (N / Nat.floor ((Real.log N) ^ 9)) n).re)
    (fun n => kernel N n * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log N) ^ 9)), Tarithv n q)
    (fun n => mainTermN N n) (ε / 9 * (N : ℝ) ^ 3) (ε / 9 * (N : ℝ) ^ 3) (ε / 9 * (N : ℝ) ^ 3)
    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun n _ _ => sq_nonneg _) (h1 N hN1))
    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun n _ _ => sq_nonneg _) (h2 N hN2))
    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun n _ _ => sq_nonneg _) (h3 N hN3))
  calc ∑ n ∈ Finset.Ioo N (2 * N), (pairWeight N n - mainTermN N n) ^ 2
      ≤ 3 * (ε / 9 * (N : ℝ) ^ 3) + 3 * (ε / 9 * (N : ℝ) ^ 3) + 3 * (ε / 9 * (N : ℝ) ^ 3) := key
    _ = ε * (N : ℝ) ^ 3 := by ring

end Principia.Common.BalancedGoldbach
