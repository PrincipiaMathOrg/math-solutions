/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonCont

set_option autoImplicit false

/-!
# `EF.MollLimit` PROVED: `∑Λ(n)χ(n)f_ε(n/x) → ∑Λ(n)χ(n)f(n/x)` as `ε → 0⁺`

**`mollLimit_holds : EF.MollLimit`**, with no hypothesis. `f = η e(δ·)`, `f_ε = f ∗_M ν_ε`
(`EF.Fe`), `ν_ε(u) = ν(u^{1/ε})/ε` supported in `[2^{−ε}, 2^ε]` with `∫ν_ε(u)du/u = 1`
(PNT+ `DeltaSpikeSupport`, `DeltaSpikeMass`).

Route (the link's docstring: an approximate identity plus a sum-versus-integral bound):
* `f_ε(t) = ∫ν_ε(u) f(t/u) du/u` (PNT+ `MellinConvolutionSymmetric`), so
  `|f_ε(t) − f(t)| ≤ sup_{u ∈ [2^{−ε}, 2^ε]} |f(t/u) − f(t)|` (`norm_fe_sub_le`) and `f_ε(t) → f(t)`
  for each `t > 0` (`tendsto_fe`), and `|f_ε(t)| ≤ ∫ν_ε(u)|η(t/u)|du/u` (`norm_fe_le`);
* **the uniform tail** (`tail_bound`): for every `θ > 0` there is `N` with
  `∑_{n ∈ s} log n·|η(n/y)| ≤ θ` for EVERY finite `s ⊂ (N, ∞)` and EVERY scale `y ∈ [x/2, 2x]`. From
  `|G(b)| ≤ (1/(b − a))∫_a^b|G| + ∫_a^b|G'|` (`abs_le_avg_add`, the fundamental theorem of calculus
  averaged over `[a, b]`) on `[n/y, (n + 1)/y]`, summed (`weighted_sum`), with
  `log(2yv)(y|η| + |η'|) ≤ C_x √v(|η| + |η'|)` (`Hy_le`) and `√v(|η| + |η'|) ∈ L¹` (`AgamonReg` at
  `σ = 3/2`), whose tails vanish (Mathlib `tendsto_integral_Ioi_zero`);
* the same tail for `f_ε`, uniformly in `ε ≤ 1` (`tail_fe`): `f_ε(n/x)` averages `f(n/(xu))` over
  scales `xu ∈ [x/2, 2x]`;
* split `∑'` into `n ≤ N` (finitely many pointwise limits) and `n > N` (`≤ θ/4` each for `f_ε` and
  `f`); `|Λ(n)χ(n)| ≤ log n`.

**Why not dominated convergence for the series:** `sup_ε |f_ε(n/x)|` is a multiplicative maximal
function of `η` on `[n/2x, 2n/x]`; bounding it by `|η| + ∫|η'|` over that interval costs a
factor `n` (the overlap), which needs `∫ t log t|η'| < ∞`, i.e. `AgamonReg` with `b > 2`.
Only `b > 3/2` is given, so the tail must be bounded per scale and averaged. No falsification:
the link is TRUE as stated (the target `twSum` is a genuinely convergent sum, so the `tsum`
junk value never fires).
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF
open scoped ArithmeticFunction

/-! ## (1) Regularity of `η` on `(0, ∞)` -/

theorem continuousOn_eta {η : ℝ → ℝ} (hreg : HM.AgamonReg η) : ContinuousOn η (Ioi 0) :=
  hreg.1.continuousOn.mono Ioi_subset_Ici_self

theorem continuousOn_deriv_eta {η : ℝ → ℝ} (hreg : HM.AgamonReg η) :
    ContinuousOn (deriv η) (Ioi 0) :=
  (hreg.1.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

/-! ## (2) The sum-versus-integral bound -/

/-- **`|G(b)| ≤ (1/(b − a))∫_a^b |G| + ∫_a^b |G'|`**: `G(b) = G(t) + ∫_t^b G'`, averaged over
`t ∈ [a, b]`. -/
theorem abs_le_avg_add {G G' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt G (G' t) t) (hc : ContinuousOn G' (Icc a b)) :
    |G b| ≤ (∫ t in a..b, |G t|) / (b - a) + ∫ t in a..b, |G' t| := by
  have hGc : ContinuousOn G (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have huI : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hGI : IntervalIntegrable (fun t => |G t|) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huI]
    exact continuous_abs.comp_continuousOn hGc
  have hG'I : IntervalIntegrable (fun t => |G' t|) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huI]
    exact continuous_abs.comp_continuousOn hc
  set K := ∫ t in a..b, |G' t| with hK
  have hpt : ∀ t ∈ Icc a b, |G b| ≤ |G t| + K := by
    intro t ht
    have hsub : uIcc t b ⊆ Icc a b := by
      rw [uIcc_of_le ht.2]
      exact Icc_subset_Icc ht.1 le_rfl
    have hftc : ∫ s in t..b, G' s = G b - G t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hd s (hsub hs))
        (ContinuousOn.intervalIntegrable (hc.mono hsub))
    have h1 : ‖∫ s in t..b, G' s‖ ≤ ∫ s in t..b, ‖G' s‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.2
    have h2 : ∫ s in t..b, |G' s| ≤ K :=
      intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
        (ae_of_all _ fun s => abs_nonneg _) hG'I
    simp only [Real.norm_eq_abs] at h1
    rw [hftc] at h1
    have h3 := abs_sub_abs_le_abs_sub (G b) (G t)
    linarith
  have hmono := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    (hGI.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hGI intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at hmono
  have hba : 0 < b - a := sub_pos.mpr hab
  have hle : |G b| ≤ ((∫ t in a..b, |G t|) + (b - a) * K) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith
  rw [add_div, mul_div_cancel_left₀ _ hba.ne'] at hle
  exact hle

/-- The weighted integrand `H_y(v) = log(2yv)(y|η(v)| + |η'(v)|)`. -/
noncomputable def Hy (η : ℝ → ℝ) (y v : ℝ) : ℝ :=
  Real.log (2 * y * v) * (y * |η v| + |deriv η v|)

/-- The integrable majorant `h(v) = √v(|η(v)| + |η'(v)|)`. -/
noncomputable def hfun (η : ℝ → ℝ) (v : ℝ) : ℝ :=
  |η v| * Real.sqrt v + |deriv η v| * Real.sqrt v

theorem continuousOn_Hy {η : ℝ → ℝ} (hreg : HM.AgamonReg η) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (Hy η y) (Ioi 0) := by
  unfold Hy
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.log (by fun_prop) fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    positivity
  · exact (continuousOn_const.mul (continuous_abs.comp_continuousOn (continuousOn_eta hreg))).add
      (continuous_abs.comp_continuousOn (continuousOn_deriv_eta hreg))

theorem continuousOn_hfun {η : ℝ → ℝ} (hreg : HM.AgamonReg η) :
    ContinuousOn (hfun η) (Ioi 0) := by
  unfold hfun
  have hs : Continuous Real.sqrt := Real.continuous_sqrt
  exact ((continuous_abs.comp_continuousOn (continuousOn_eta hreg)).mul hs.continuousOn).add
    ((continuous_abs.comp_continuousOn (continuousOn_deriv_eta hreg)).mul hs.continuousOn)

theorem integrableOn_hfun {η : ℝ → ℝ} (hreg : HM.AgamonReg η) :
    IntegrableOn (hfun η) (Ioi 0) := by
  obtain ⟨-, i2, -, i4⟩ := agamon_int hreg
  exact i2.add i4

theorem hfun_nonneg (η : ℝ → ℝ) (v : ℝ) : 0 ≤ hfun η v := by
  unfold hfun
  positivity

/-- **One step**: `log(n + 1)|η((n + 1)/y)| ≤ ∫_{n/y}^{(n+1)/y} H_y`. -/
theorem weighted_point {η : ℝ → ℝ} (hreg : HM.AgamonReg η) {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) * |η (((n : ℝ) + 1) / y)| ≤
      ∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y, Hy η y v := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) / y := by positivity
  have hab : (n : ℝ) / y < ((n : ℝ) + 1) / y := div_lt_div_of_pos_right (by linarith) hy
  have hsub : Icc ((n : ℝ) / y) (((n : ℝ) + 1) / y) ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le ha hv.1
  have huI : uIcc ((n : ℝ) / y) (((n : ℝ) + 1) / y) = Icc ((n : ℝ) / y) (((n : ℝ) + 1) / y) :=
    uIcc_of_le hab.le
  have hb := abs_le_avg_add hab (G := η) (G' := deriv η)
    (fun t ht => (agamon_diff hreg (hsub ht)).hasDerivAt)
    ((continuousOn_deriv_eta hreg).mono hsub)
  have hlen : ((n : ℝ) + 1) / y - (n : ℝ) / y = 1 / y := by
    field_simp
    ring
  rw [hlen, div_div_eq_mul_div, div_one] at hb
  have hηI : IntervalIntegrable (fun v => |η v|) volume ((n : ℝ) / y) (((n : ℝ) + 1) / y) := by
    apply ContinuousOn.intervalIntegrable
    rw [huI]
    exact continuous_abs.comp_continuousOn ((continuousOn_eta hreg).mono hsub)
  have hdI : IntervalIntegrable (fun v => |deriv η v|) volume ((n : ℝ) / y)
      (((n : ℝ) + 1) / y) := by
    apply ContinuousOn.intervalIntegrable
    rw [huI]
    exact continuous_abs.comp_continuousOn ((continuousOn_deriv_eta hreg).mono hsub)
  have hcomb : (∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y, |η v|) * y +
      ∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y, |deriv η v| =
      ∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y, (y * |η v| + |deriv η v|) := by
    rw [intervalIntegral.integral_add (hηI.const_mul y) hdI, intervalIntegral.integral_const_mul,
      mul_comm]
  rw [hcomb] at hb
  have hL : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hHI : IntervalIntegrable (Hy η y) volume ((n : ℝ) / y) (((n : ℝ) + 1) / y) := by
    apply ContinuousOn.intervalIntegrable
    rw [huI]
    exact (continuousOn_Hy hreg hy).mono hsub
  calc Real.log ((n : ℝ) + 1) * |η (((n : ℝ) + 1) / y)|
      ≤ Real.log ((n : ℝ) + 1) *
          ∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y, (y * |η v| + |deriv η v|) :=
        mul_le_mul_of_nonneg_left hb hL
    _ = ∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y,
          Real.log ((n : ℝ) + 1) * (y * |η v| + |deriv η v|) :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ v in (n : ℝ) / y..((n : ℝ) + 1) / y, Hy η y v := by
        refine intervalIntegral.integral_mono_on hab.le (((hηI.const_mul y).add hdI).const_mul _)
          hHI fun v hv => ?_
        have hv1 : (n : ℝ) ≤ y * v := by
          have := hv.1
          rw [div_le_iff₀ hy] at this
          linarith
        have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * y * v) :=
          Real.log_le_log (by linarith) (by linarith)
        unfold Hy
        exact mul_le_mul_of_nonneg_right hlog (by positivity)

/-- **Summed**: `∑_{k<m} log(N + k + 1)|η((N + k + 1)/y)| ≤ ∫_{N/y}^{(N+m)/y} H_y`. -/
theorem weighted_sum {η : ℝ → ℝ} (hreg : HM.AgamonReg η) {y : ℝ} (hy : 0 < y) {N : ℕ}
    (hN : 1 ≤ N) (m : ℕ) :
    ∑ k ∈ Finset.range m, Real.log (((N + k : ℕ) : ℝ) + 1) * |η ((((N + k : ℕ) : ℝ) + 1) / y)| ≤
      ∫ v in (N : ℝ) / y..((N + m : ℕ) : ℝ) / y, Hy η y v := by
  have hint : ∀ k < m, IntervalIntegrable (Hy η y) volume
      ((fun j : ℕ => ((N + j : ℕ) : ℝ) / y) k) ((fun j : ℕ => ((N + j : ℕ) : ℝ) / y) (k + 1)) := by
    intro k _
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_Hy hreg hy).mono fun v hv => ?_
    have hpos : 0 < ((N + k : ℕ) : ℝ) / y := by
      have : (1 : ℝ) ≤ ((N + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N + k by omega)
      positivity
    have hle : ((N + k : ℕ) : ℝ) / y ≤ ((N + (k + 1) : ℕ) : ℝ) / y := by
      apply div_le_div_of_nonneg_right _ hy.le
      exact_mod_cast (show N + k ≤ N + (k + 1) by omega)
    rw [uIcc_of_le hle] at hv
    exact lt_of_lt_of_le hpos hv.1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((N + j : ℕ) : ℝ) / y) hint
  calc ∑ k ∈ Finset.range m, Real.log (((N + k : ℕ) : ℝ) + 1) *
        |η ((((N + k : ℕ) : ℝ) + 1) / y)|
      ≤ ∑ k ∈ Finset.range m, ∫ v in ((N + k : ℕ) : ℝ) / y..((N + (k + 1) : ℕ) : ℝ) / y,
          Hy η y v := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h := weighted_point hreg hy (n := N + k) (by omega)
        have e : ((N + (k + 1) : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [e]
        exact h
    _ = ∫ v in ((N + 0 : ℕ) : ℝ) / y..((N + m : ℕ) : ℝ) / y, Hy η y v := hsum
    _ = ∫ v in (N : ℝ) / y..((N + m : ℕ) : ℝ) / y, Hy η y v := by rw [Nat.add_zero]

/-- **`H_y(v) ≤ C_x h(v)`** for `v ≥ 1`, `0 < y ≤ 2x`. -/
theorem Hy_le {η : ℝ → ℝ} {x y v : ℝ} (hx : 0 < x) (hy0 : 0 < y) (hy : y ≤ 2 * x)
    (hv : 1 ≤ v) :
    Hy η y v ≤ (|Real.log (4 * x)| + 2) * (2 * x + 1) * hfun η v := by
  have hv0 : 0 < v := by linarith
  have hsv : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv
  have hA : 0 ≤ y * |η v| + |deriv η v| := by positivity
  have hB : y * |η v| + |deriv η v| ≤ (2 * x + 1) * (|η v| + |deriv η v|) := by
    have h1 := abs_nonneg (η v)
    have h2 := abs_nonneg (deriv η v)
    nlinarith
  have hC : 0 ≤ (|Real.log (4 * x)| + 2) * (2 * x + 1) * hfun η v := by
    have := hfun_nonneg η v
    positivity
  rcases le_or_gt (Real.log (2 * y * v)) 0 with hl | hl
  · have : Hy η y v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl hA
    linarith
  · have h1 : Real.log (2 * y * v) ≤ Real.log (4 * x * v) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log (4 * x * v) = Real.log (4 * x) + Real.log v :=
      Real.log_mul (by positivity) (by positivity)
    have h3 : Real.log v ≤ 2 * Real.sqrt v := by
      have h := Real.log_le_rpow_div hv0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    have h4 : Real.log (4 * x) ≤ |Real.log (4 * x)| * Real.sqrt v := by
      have h5 := le_abs_self (Real.log (4 * x))
      have h6 := abs_nonneg (Real.log (4 * x))
      nlinarith
    have hL : Real.log (2 * y * v) ≤ (|Real.log (4 * x)| + 2) * Real.sqrt v := by nlinarith
    unfold Hy hfun
    calc Real.log (2 * y * v) * (y * |η v| + |deriv η v|)
        ≤ ((|Real.log (4 * x)| + 2) * Real.sqrt v) * ((2 * x + 1) * (|η v| + |deriv η v|)) :=
          mul_le_mul hL hB hA (by positivity)
      _ = (|Real.log (4 * x)| + 2) * (2 * x + 1) *
            (|η v| * Real.sqrt v + |deriv η v| * Real.sqrt v) := by ring

/-- **The uniform tail**: for every `θ > 0` there is `N` such that `∑_{n ∈ s} log n·|η(n/y)| ≤ θ`
for every finite `s ⊂ (N, ∞)` and every `y ∈ [x/2, 2x]`. -/
theorem tail_bound {η : ℝ → ℝ} (hreg : HM.AgamonReg η) {x : ℝ} (hx : 0 < x) {θ : ℝ}
    (hθ : 0 < θ) : ∃ N : ℕ, ∀ y ∈ Icc (x / 2) (2 * x), ∀ s : Finset ℕ, (∀ n ∈ s, N < n) →
      ∑ n ∈ s, Real.log n * |η (n / y)| ≤ θ := by
  set C : ℝ := (|Real.log (4 * x)| + 2) * (2 * x + 1) with hCdef
  have hC : 0 < C := by positivity
  have htail : Tendsto (fun n : ℕ => ∫ v in Ioi ((n : ℝ) / (2 * x)), hfun η v) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero ((tendsto_natCast_atTop_atTop).atTop_div_const (by positivity))
  have hev1 : ∀ᶠ n : ℕ in atTop, C * ∫ v in Ioi ((n : ℝ) / (2 * x)), hfun η v < θ := by
    have h := htail.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds hθ)
  have hev2 : ∀ᶠ n : ℕ in atTop, 2 * x ≤ (n : ℝ) ∧ 1 ≤ n := by
    obtain ⟨m, hm⟩ := exists_nat_ge (2 * x)
    filter_upwards [eventually_ge_atTop (max m 1)] with n hn
    refine ⟨hm.trans (by exact_mod_cast (le_max_left _ _).trans hn), (le_max_right _ _).trans hn⟩
  obtain ⟨N, hN1, hN2, hN3⟩ := (hev1.and hev2).exists
  refine ⟨N, fun y hy s hs => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact hθ.le
  set M := s.sup id with hM
  have hsM : ∀ n ∈ s, n ≤ M := fun n hn => Finset.le_sup (f := id) hn
  have hNM : N ≤ M := by
    obtain ⟨n, hn⟩ := hne
    exact (le_of_lt (hs n hn)).trans (hsM n hn)
  -- `s` sits inside `{N + 1 + k : k < M − N}`
  set T := (Finset.range (M - N)).map (addLeftEmbedding (N + 1)) with hT
  have hsT : s ⊆ T := by
    intro n hn
    rw [hT, Finset.mem_map]
    refine ⟨n - (N + 1), Finset.mem_range.mpr ?_, ?_⟩
    · have := hs n hn
      have := hsM n hn
      omega
    · have := hs n hn
      simp only [addLeftEmbedding_apply]
      omega
  have hnn : ∀ n ∈ T, 0 ≤ Real.log n * |η (n / y)| := fun n _ =>
    mul_nonneg (Real.log_natCast_nonneg n) (abs_nonneg _)
  have h1 : ∑ n ∈ s, Real.log n * |η (n / y)| ≤ ∑ n ∈ T, Real.log n * |η (n / y)| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsT fun n hn _ => hnn n hn
  have h2 : ∑ n ∈ T, Real.log n * |η (n / y)| =
      ∑ k ∈ Finset.range (M - N), Real.log (((N + k : ℕ) : ℝ) + 1) *
        |η ((((N + k : ℕ) : ℝ) + 1) / y)| := by
    rw [hT, Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (((addLeftEmbedding (N + 1)) k : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by
      simp only [addLeftEmbedding_apply]
      push_cast
      ring
    rw [e]
  have h3 := weighted_sum hreg hy0 hN3 (M - N)
  have hNMc : ((N + (M - N) : ℕ) : ℝ) = M := by
    rw [Nat.add_sub_cancel' hNM]
  rw [hNMc] at h3
  -- the integral against the majorant
  have hNy : (1 : ℝ) ≤ (N : ℝ) / y := by
    rw [le_div_iff₀ hy0]
    linarith [hy.2]
  have hNy' : (N : ℝ) / (2 * x) ≤ (N : ℝ) / y :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hy0 hy.2
  have hMy : (N : ℝ) / y ≤ (M : ℝ) / y :=
    div_le_div_of_nonneg_right (by exact_mod_cast hNM) hy0.le
  have hsubI : Icc ((N : ℝ) / y) ((M : ℝ) / y) ⊆ Ioi 0 := fun v hv =>
    lt_of_lt_of_le (by linarith) hv.1
  have huI : uIcc ((N : ℝ) / y) ((M : ℝ) / y) = Icc ((N : ℝ) / y) ((M : ℝ) / y) :=
    uIcc_of_le hMy
  have h4 : ∫ v in (N : ℝ) / y..(M : ℝ) / y, Hy η y v ≤
      ∫ v in (N : ℝ) / y..(M : ℝ) / y, C * hfun η v := by
    refine intervalIntegral.integral_mono_on hMy ?_ ?_ fun v hv => ?_
    · apply ContinuousOn.intervalIntegrable
      rw [huI]
      exact (continuousOn_Hy hreg hy0).mono hsubI
    · apply ContinuousOn.intervalIntegrable
      rw [huI]
      exact (continuousOn_const.mul (continuousOn_hfun hreg)).mono hsubI
    · exact Hy_le hx hy0 hy.2 (hNy.trans hv.1)
  have h5 : ∫ v in (N : ℝ) / y..(M : ℝ) / y, C * hfun η v ≤
      C * ∫ v in Ioi ((N : ℝ) / (2 * x)), hfun η v := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hMy]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have hN0 : (0 : ℝ) < (N : ℝ) / (2 * x) :=
      div_pos (Nat.cast_pos.mpr (by omega)) (by positivity)
    refine setIntegral_mono_set ((integrableOn_hfun hreg).mono_set fun v (hv : _ < v) =>
      hN0.trans hv) (ae_of_all _ fun v => hfun_nonneg η v) ?_
    have hss : Ioc ((N : ℝ) / y) ((M : ℝ) / y) ⊆ Ioi ((N : ℝ) / (2 * x)) := fun v hv =>
      lt_of_le_of_lt hNy' hv.1
    exact hss.eventuallyLE
  rw [h2] at h1
  linarith

/-! ## (3) The mollified weight as an average -/

theorem spike_nonneg {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    0 ≤ DeltaSpike ν ε u :=
  div_nonneg (hν.2.1 _) hε.le

theorem spike_mass {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) :
    ∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u / u = 1 :=
  DeltaSpikeMass hν.2.2.2 hε

theorem spike_int {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u => DeltaSpike ν ε u / u) (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [spike_mass hν hε]; norm_num)

/-- `ν_ε · ψ ∈ L¹(0, ∞)` for `ψ` continuous on `(0, ∞)`. -/
theorem integrableOn_spike_mul {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) {ψ : ℝ → ℂ}
    (hψ : ContinuousOn ψ (Ioi 0)) :
    IntegrableOn (fun u => nuC (DeltaSpike ν ε) u * ψ u) (Ioi 0) := by
  have hgc : Continuous (nuC (DeltaSpike ν ε)) :=
    DeltaSpikeOfRealContinuous hε (hν.1.of_le (by simp))
  have hsub : Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε) ⊆ Ioi 0 := fun u hu =>
    lt_of_lt_of_le (by positivity) hu.1
  have h1 : IntegrableOn (fun u => nuC (DeltaSpike ν ε) u * ψ u) (Icc (2 ^ (-ε)) (2 ^ ε)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (hgc.continuousOn.mul (hψ.mono hsub))
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun u hu => ?_
  have h0 : DeltaSpike ν ε u = 0 := DeltaSpikeSupport hε (le_of_lt hu.1) hν.2.2.1 hu.2
  simp [nuC, h0]

/-- **`f_ε(t) = ∫ν_ε(u) f(t/u) du/u`** (PNT+ `MellinConvolutionSymmetric`). -/
theorem fe_sym (η : ℝ → ℝ) (δ : ℝ) (ν : ℝ → ℝ) (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    Fe η δ ν ε t = ∫ u in Ioi (0 : ℝ), nuC (DeltaSpike ν ε) u * fw η δ (t / u) / u := by
  unfold Fe
  rw [MellinConvolutionSymmetric _ _ ht]
  rfl

/-- `u ↦ f(t/u)/u` is continuous on `(0, ∞)`. -/
theorem continuousOn_fw_div {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun u : ℝ => fw η δ (t / u) / u) (Ioi 0) := by
  intro u hu
  have hu' : (0 : ℝ) < u := hu
  have h1 : ContinuousAt (fun u : ℝ => fw η δ (t / u)) u :=
    ((continuousOn_fw hreg δ).continuousAt (Ioi_mem_nhds (div_pos ht hu'))).comp
      (continuousAt_const.div continuousAt_id hu'.ne')
  exact (h1.div (Complex.continuous_ofReal.continuousAt)
    (Complex.ofReal_ne_zero.mpr hu'.ne')).continuousWithinAt

/-- `u ↦ ν_ε(u)|η(t/u)|/u ∈ L¹(0, ∞)`. -/
theorem integrable_spike_abs {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {ν : ℝ → ℝ}
    (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => DeltaSpike ν ε u * |η (t / u)| / u) (Ioi 0) := by
  have h := integrableOn_spike_mul hν hε (continuousOn_fw_div hreg δ ht)
  refine IntegrableOn.congr_fun h.norm (fun u hu => ?_) measurableSet_Ioi
  have hu' : (0 : ℝ) < u := hu
  rw [norm_mul, norm_div, nuC, Complex.norm_real, Real.norm_of_nonneg (spike_nonneg hν hε u),
    norm_fw, Complex.norm_real, Real.norm_of_nonneg hu'.le]
  ring

/-- **`|f_ε(t)| ≤ ∫ν_ε(u)|η(t/u)|du/u`.** -/
theorem norm_fe_le {η : ℝ → ℝ} (δ : ℝ) {ν : ℝ → ℝ} (hν : MollData ν) {ε : ℝ}
    (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    ‖Fe η δ ν ε t‖ ≤ ∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u * |η (t / u)| / u := by
  rw [fe_sym η δ ν ε ht]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  rw [norm_div, norm_mul, nuC, Complex.norm_real, Real.norm_of_nonneg (spike_nonneg hν hε u),
    norm_fw, Complex.norm_real, Real.norm_of_nonneg hu'.le]

/-- **`|f_ε(t) − f(t)| ≤ θ`** when `|f(t/u) − f(t)| ≤ θ` on the support `[2^{−ε}, 2^ε]`. -/
theorem norm_fe_sub_le {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {ν : ℝ → ℝ}
    (hν : MollData ν) {ε : ℝ} (hε : 0 < ε) {t θ : ℝ} (ht : 0 < t)
    (hsup : ∀ u ∈ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε), ‖fw η δ (t / u) - fw η δ t‖ ≤ θ) :
    ‖Fe η δ ν ε t - fw η δ t‖ ≤ θ := by
  have hi1 := integrableOn_spike_mul hν hε (continuousOn_fw_div hreg δ ht)
  have hc2 : ContinuousOn (fun u : ℝ => fw η δ t / u) (Ioi 0) := fun u hu =>
    (continuousAt_const.div Complex.continuous_ofReal.continuousAt
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))).continuousWithinAt
  have hi2 := integrableOn_spike_mul hν hε hc2
  have hmass : ∫ u in Ioi (0 : ℝ), nuC (DeltaSpike ν ε) u * (fw η δ t / u) = fw η δ t := by
    have e : ∀ u ∈ Ioi (0 : ℝ), nuC (DeltaSpike ν ε) u * (fw η δ t / u) =
        ((DeltaSpike ν ε u / u : ℝ) : ℂ) * fw η δ t := by
      intro u _
      rw [nuC]
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_mul_const, integral_complex_ofReal,
      spike_mass hν hε, Complex.ofReal_one, one_mul]
  have hFe : Fe η δ ν ε t = ∫ u in Ioi (0 : ℝ), nuC (DeltaSpike ν ε) u * (fw η δ (t / u) / u) := by
    rw [fe_sym η δ ν ε ht]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [hFe]
  conv_lhs => rw [← hmass]
  rw [← integral_sub hi1 hi2]
  refine norm_integral_le_of_norm_le ((spike_int hν hε).const_mul θ)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)) |>.trans ?_
  · have hu' : (0 : ℝ) < u := hu
    have e : nuC (DeltaSpike ν ε) u * (fw η δ (t / u) / u) -
        nuC (DeltaSpike ν ε) u * (fw η δ t / u) =
        ((DeltaSpike ν ε u / u : ℝ) : ℂ) * (fw η δ (t / u) - fw η δ t) := by
      rw [nuC]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (spike_nonneg hν hε u) hu'.le)]
    by_cases hmem : u ∈ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε)
    · rw [mul_comm θ]
      exact mul_le_mul_of_nonneg_left (hsup u hmem) (div_nonneg (spike_nonneg hν hε u) hu'.le)
    · rw [DeltaSpikeSupport hε hu'.le hν.2.2.1 hmem, zero_div, zero_mul, mul_zero]
  · rw [integral_const_mul, spike_mass hν hε, mul_one]

/-- **`f_ε(t) → f(t)` as `ε → 0⁺`**, for `t > 0` (continuity of `f` at `t`). -/
theorem tendsto_fe {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {ν : ℝ → ℝ} (hν : MollData ν)
    {t : ℝ} (ht : 0 < t) : Tendsto (fun ε => Fe η δ ν ε t) (𝓝[>] 0) (𝓝 (fw η δ t)) := by
  rw [Metric.tendsto_nhds]
  intro θ hθ
  have hc : ContinuousAt (fw η δ) t := (continuousOn_fw hreg δ).continuousAt (Ioi_mem_nhds ht)
  have hc1 : ContinuousAt (fun u : ℝ => fw η δ (t / u)) 1 := by
    have h1 : ContinuousAt (fun u : ℝ => t / u) 1 :=
      continuousAt_const.div continuousAt_id one_ne_zero
    have h2 : ContinuousAt (fw η δ) (t / 1) := by rw [div_one]; exact hc
    exact h2.comp h1
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.mp hc1 (θ / 2) (by linarith)
  have h2 : Tendsto (fun ε : ℝ => (2 : ℝ) ^ ε) (𝓝 0) (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow (b := 0) (show (2 : ℝ) ≠ 0 by norm_num)).tendsto
    rwa [Real.rpow_zero] at h
  have h2n : Tendsto (fun ε : ℝ => (2 : ℝ) ^ (-ε)) (𝓝 0) (𝓝 1) := by
    have h := h2.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun ε => (Real.rpow_neg (by norm_num) ε).symm
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (h2.eventually (Metric.ball_mem_nhds 1 hρ)),
    nhdsWithin_le_nhds (h2n.eventually (Metric.ball_mem_nhds 1 hρ))] with ε hε hb1 hb2
  have hε' : 0 < ε := hε
  rw [dist_eq_norm]
  have hle : ‖Fe η δ ν ε t - fw η δ t‖ ≤ θ / 2 := by
    refine norm_fe_sub_le hreg δ hν hε' ht fun u hu => ?_
    rw [Real.dist_eq] at hb1 hb2
    have hu1 : dist u 1 < ρ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [hu.1, (abs_lt.mp hb2).1]
      · linarith [hu.2, (abs_lt.mp hb1).2]
    have h := hball hu1
    rw [div_one, dist_eq_norm] at h
    exact h.le
  linarith

/-- **The tail of `f_ε`, uniformly in `ε ≤ 1`**: inherited from the scales `xu ∈ [x/2, 2x]`. -/
theorem tail_fe {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {ν : ℝ → ℝ} (hν : MollData ν)
    {x : ℝ} (hx : 0 < x) {θ : ℝ} {N : ℕ}
    (hN : ∀ y ∈ Icc (x / 2) (2 * x), ∀ s : Finset ℕ, (∀ n ∈ s, N < n) →
      ∑ n ∈ s, Real.log n * |η (n / y)| ≤ θ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (s : Finset ℕ) (hs : ∀ n ∈ s, N < n) :
    ∑ n ∈ s, Real.log n * ‖Fe η δ ν ε (n / x)‖ ≤ θ := by
  have hpos : ∀ n ∈ s, (0 : ℝ) < (n : ℝ) / x := fun n hn => by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hs n hn; omega)
    positivity
  have hint : ∀ n ∈ s, IntegrableOn (fun u => Real.log n *
      (DeltaSpike ν ε u * |η ((n : ℝ) / x / u)| / u)) (Ioi 0) := fun n hn =>
    (integrable_spike_abs hreg δ hν hε0 (hpos n hn)).const_mul _
  calc ∑ n ∈ s, Real.log n * ‖Fe η δ ν ε (n / x)‖
      ≤ ∑ n ∈ s, Real.log n * ∫ u in Ioi (0 : ℝ),
          DeltaSpike ν ε u * |η ((n : ℝ) / x / u)| / u := by
        refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_
          (Real.log_natCast_nonneg n)
        exact norm_fe_le δ hν hε0 (hpos n hn)
    _ = ∫ u in Ioi (0 : ℝ), ∑ n ∈ s, Real.log n *
          (DeltaSpike ν ε u * |η ((n : ℝ) / x / u)| / u) := by
        rw [integral_finsetSum s hint]
        exact Finset.sum_congr rfl fun n _ => (integral_const_mul _ _).symm
    _ ≤ ∫ u in Ioi (0 : ℝ), θ * (DeltaSpike ν ε u / u) := by
        refine setIntegral_mono_on (integrable_finsetSum s hint)
          ((spike_int hν hε0).const_mul θ) measurableSet_Ioi fun u hu => ?_
        have hu' : (0 : ℝ) < u := hu
        have e : ∑ n ∈ s, Real.log n * (DeltaSpike ν ε u * |η ((n : ℝ) / x / u)| / u) =
            DeltaSpike ν ε u / u * ∑ n ∈ s, Real.log n * |η ((n : ℝ) / (x * u))| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [div_div]
          ring
        rw [e, mul_comm θ]
        have hDS : 0 ≤ DeltaSpike ν ε u / u := div_nonneg (spike_nonneg hν hε0 u) hu'.le
        by_cases hmem : u ∈ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε)
        · have h1 : (1 / 2 : ℝ) ≤ u := by
            refine le_trans ?_ hmem.1
            rw [show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have h2 : u ≤ 2 := by
            refine hmem.2.trans ?_
            calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
              _ = 2 := Real.rpow_one 2
          have hy : x * u ∈ Icc (x / 2) (2 * x) := ⟨by nlinarith, by nlinarith⟩
          exact mul_le_mul_of_nonneg_left (hN (x * u) hy s hs) hDS
        · rw [DeltaSpikeSupport hε0 hu'.le hν.2.2.1 hmem, zero_div, zero_mul, zero_mul]
    _ = θ := by rw [integral_const_mul, spike_mass hν hε0, mul_one]

/-! ## (4) Series bookkeeping -/

/-- A nonnegative sequence with uniformly bounded tail sums is summable. -/
theorem summable_of_tail {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {N : ℕ} {c : ℝ}
    (h : ∀ s : Finset ℕ, (∀ n ∈ s, N < n) → ∑ n ∈ s, f n ≤ c) : Summable f := by
  refine summable_of_sum_le (c := ∑ n ∈ Finset.range (N + 1), f n + c) (fun n => hf n)
    fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun n => n ≤ N)]
  refine add_le_add ?_ (h _ fun n hn => ?_)
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => hf n)
    rw [Finset.mem_filter] at hn
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.mem_filter] at hn
    omega

/-- The shifted tail `∑'_n f(n + N + 1)` is bounded by the tail bound. -/
theorem tsum_tail_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {N : ℕ} {c : ℝ}
    (h : ∀ s : Finset ℕ, (∀ n ∈ s, N < n) → ∑ n ∈ s, f n ≤ c) :
    ∑' n, f (n + (N + 1)) ≤ c := by
  refine Real.tsum_le_of_sum_le (fun n => hf _) fun s => ?_
  have h1 := h (s.map (addRightEmbedding (N + 1))) fun n hn => ?_
  · rwa [Finset.sum_map] at h1
  · rw [Finset.mem_map] at hn
    obtain ⟨m, _, rfl⟩ := hn
    simp only [addRightEmbedding_apply]
    omega

/-! ## (5) `MollLimit` -/

/-- `|Λ(n)χ(n)| ≤ log n`. -/
theorem norm_lam_chi_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤ Real.log n := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
        mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _)
          ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ Real.log n := by rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log

/-- **`EF.MollLimit` HOLDS.** -/
theorem mollLimit_holds : MollLimit := by
  intro η hreg _ ν hν q _ χ δ x hx
  have htgt : MajSp.twSum η χ x (δ / x) = twF (fw η δ) χ x := by
    unfold MajSp.twSum twF fw
    refine tsum_congr fun n => ?_
    rw [show (n : ℝ) * (δ / x) = δ * ((n : ℝ) / x) by ring]
    ring
  rw [htgt, Metric.tendsto_nhds]
  intro θ hθ
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) with ha
  have hθ4 : 0 < θ / 4 := by linarith
  obtain ⟨N, hN⟩ := tail_bound hreg hx hθ4
  have hxI : x ∈ Icc (x / 2) (2 * x) := ⟨by linarith, by linarith⟩
  have hPt := hN x hxI
  have hPnn : ∀ n : ℕ, 0 ≤ Real.log n * |η (n / x)| := fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (abs_nonneg _)
  have hPs : Summable fun n : ℕ => Real.log n * |η (n / x)| := summable_of_tail hPnn hPt
  have hS1 : Summable fun n : ℕ => a n * fw η δ (n / x) := by
    refine Summable.of_norm_bounded hPs fun n => ?_
    rw [norm_mul, norm_fw]
    exact mul_le_mul_of_nonneg_right (norm_lam_chi_le χ n) (abs_nonneg _)
  -- the first `N + 1` terms converge
  have hfin : Tendsto (fun ε => ∑ n ∈ Finset.range (N + 1),
      ‖a n‖ * ‖Fe η δ ν ε (n / x) - fw η δ (n / x)‖) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range (N + 1)) (x := 𝓝[>] (0 : ℝ))
      (f := fun n ε => ‖a n‖ * ‖Fe η δ ν ε (n / x) - fw η δ (n / x)‖)
      (a := fun _ => (0 : ℝ)) fun n _ => ?_
    · simpa using h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [ha]
    · have hpos : (0 : ℝ) < (n : ℝ) / x := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      have h1 := ((tendsto_fe hreg δ hν hpos).sub_const (fw η δ (n / x))).norm
      rw [sub_self, norm_zero] at h1
      have h2 := h1.const_mul ‖a n‖
      rwa [mul_zero] at h2
  filter_upwards [hfin.eventually (gt_mem_nhds hθ4),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hfε hε
  have hε0 : 0 < ε := hε.1
  have hQt := tail_fe hreg δ hν hx hN hε0 hε.2.le
  have hQnn : ∀ n : ℕ, 0 ≤ Real.log n * ‖Fe η δ ν ε (n / x)‖ := fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (norm_nonneg _)
  have hQs : Summable fun n : ℕ => Real.log n * ‖Fe η δ ν ε (n / x)‖ :=
    summable_of_tail hQnn hQt
  have hS2 : Summable fun n : ℕ => a n * Fe η δ ν ε (n / x) := by
    refine Summable.of_norm_bounded hQs fun n => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_lam_chi_le χ n) (norm_nonneg _)
  set d : ℕ → ℝ := fun n => ‖a n * Fe η δ ν ε (n / x) - a n * fw η δ (n / x)‖ with hd
  have hdnn : ∀ n, 0 ≤ d n := fun n => norm_nonneg _
  have hdle : ∀ n, d n ≤ Real.log n * ‖Fe η δ ν ε (n / x)‖ + Real.log n * |η (n / x)| := by
    intro n
    rw [hd]
    simp only
    rw [← mul_sub, norm_mul]
    have h1 := norm_lam_chi_le χ n
    have h2 := norm_sub_le (Fe η δ ν ε (n / x)) (fw η δ (n / x))
    rw [norm_fw] at h2
    calc ‖a n‖ * ‖Fe η δ ν ε (n / x) - fw η δ (n / x)‖
        ≤ Real.log n * (‖Fe η δ ν ε (n / x)‖ + |η (n / x)|) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.log_natCast_nonneg n)
      _ = _ := by ring
  have hds : Summable d := Summable.of_nonneg_of_le hdnn hdle (hQs.add hPs)
  have htl : ∑' n, d (n + (N + 1)) ≤ θ / 4 + θ / 4 := by
    refine tsum_tail_le hdnn fun s hs => ?_
    calc ∑ n ∈ s, d n
        ≤ ∑ n ∈ s, (Real.log n * ‖Fe η δ ν ε (n / x)‖ + Real.log n * |η (n / x)|) :=
          Finset.sum_le_sum fun n _ => hdle n
      _ = ∑ n ∈ s, Real.log n * ‖Fe η δ ν ε (n / x)‖ +
            ∑ n ∈ s, Real.log n * |η (n / x)| := Finset.sum_add_distrib
      _ ≤ θ / 4 + θ / 4 := add_le_add (hQt s hs) (hPt s hs)
  have hhead : ∑ n ∈ Finset.range (N + 1), d n =
      ∑ n ∈ Finset.range (N + 1), ‖a n‖ * ‖Fe η δ ν ε (n / x) - fw η δ (n / x)‖ := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hd]
    simp only
    rw [← mul_sub, norm_mul]
  rw [dist_eq_norm]
  have e1 : twF (Fe η δ ν ε) χ x - twF (fw η δ) χ x =
      ∑' n, (a n * Fe η δ ν ε (n / x) - a n * fw η δ (n / x)) := by
    rw [hS2.tsum_sub hS1]
    rfl
  rw [e1]
  calc ‖∑' n, (a n * Fe η δ ν ε (n / x) - a n * fw η δ (n / x))‖
      ≤ ∑' n, d n := norm_tsum_le_tsum_norm hds
    _ = ∑ n ∈ Finset.range (N + 1), d n + ∑' n, d (n + (N + 1)) :=
        (hds.sum_add_tsum_nat_add (N + 1)).symm
    _ < θ / 4 + (θ / 4 + θ / 4) := by
        rw [hhead]
        exact add_lt_add_of_lt_of_le hfε htl
    _ < θ := by linarith

end Principia.Common.TernaryGoldbach.AG
