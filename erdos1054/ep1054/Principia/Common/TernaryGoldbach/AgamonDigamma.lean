/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonLeftLD
import Principia.Common.PNT.DigammaSeries

set_option autoImplicit false

/-!
# `AG.DigammaLine` PROVED: `|ψ(z) − log z| ≤ 1/2` on `Re z = 3/2`

**`digammaLine_holds : DigammaLine`** (true supremum `0.3699`, at `z = 3/2`). Route:
* `ψ(z) − log z = −∑_n d_n`, `d_n = 1/w − (log(w + 1) − log w)`, `w = n + z` (`psi_sub_log`): the
  digamma series `ψ(z) + γ = ∑(1/(n+1) − 1/(n+z))` (PNT+ `Complex.hasSum_digamma`, ported in
  `Common/PNT/DigammaSeries`), the Euler–Mascheroni series `γ = ∑(1/(n+1) − log((n+2)/(n+1)))`
  (Mathlib `Real.tendsto_eulerMascheroniSeq`), and the telescoping series of
  `A_n = log(n + z) − log(n + 1) = log((n + z)/(n + 1)) → 0`
  (PNT+ `Complex.hasSum_sub_succ_of_tendsto_zero`);
* `|d_n| ≤ 1/(2|w|²)` (`norm_d_le`): `log(w + 1) − log w = ∫₀¹ dt/(w + t)`, so
  `d_n = ∫₀¹ t/(w(w + t)) dt` with `|w + t| ≥ |w|` (`Re w > 0`);
* `|w| ≥ n + 3/2` and `1/(n + 3/2)² ≤ 1/(n+1) − 1/(n+2)`, so `∑|d_n| ≤ 1/2` (`tsum_g_le`).
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology Complex
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF

/-! ## (1) One term -/

/-- `d(w) = 1/w − (log(w + 1) − log w)`. -/
noncomputable def dTerm (w : ℂ) : ℂ := 1 / w - (Complex.log (w + 1) - Complex.log w)

/-- **`log(w + 1) − log w = ∫₀¹ dt/(w + t)`** for `Re w > 0`. -/
theorem log_succ_sub {w : ℂ} (hw : 0 < w.re) :
    Complex.log (w + 1) - Complex.log w = ∫ t in (0 : ℝ)..1, 1 / (w + t) := by
  have hne : ∀ t : ℝ, 0 ≤ t → w + t ≠ 0 := fun t ht h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Complex.log (w + t)) (1 / (w + t)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hmem : w + t ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
    have hlin : HasDerivAt (fun u : ℝ => w + (u : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_add w
    exact hlin.clog_real hmem
  have hc : ContinuousOn (fun t : ℝ => 1 / (w + t)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    exact (continuousAt_const.div (continuousAt_const.add Complex.continuous_ofReal.continuousAt)
      (hne t ht.1)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

/-- `|w| ≤ |w + t|` for `t ≥ 0`, `Re w ≥ 0`. -/
theorem norm_le_norm_add {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 ≤ t) : ‖w‖ ≤ ‖w + t‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

/-- **`|d(w)| ≤ 1/(2|w|²)`** for `Re w > 0`. -/
theorem norm_d_le {w : ℂ} (hw : 0 < w.re) : ‖dTerm w‖ ≤ 1 / (2 * ‖w‖ ^ 2) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hne : ∀ t : ℝ, 0 ≤ t → w + t ≠ 0 := fun t ht h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hc : ContinuousOn (fun t : ℝ => 1 / (w + t)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    exact (continuousAt_const.div (continuousAt_const.add Complex.continuous_ofReal.continuousAt)
      (hne t ht.1)).continuousWithinAt
  have hI : dTerm w = ∫ t in (0 : ℝ)..1, (1 / w - 1 / (w + t)) := by
    rw [dTerm, log_succ_sub hw, intervalIntegral.integral_sub intervalIntegrable_const
      hc.intervalIntegrable, intervalIntegral.integral_const]
    simp
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ‖1 / w - 1 / (w + t)‖ ≤ t / ‖w‖ ^ 2 := by
    intro t ht
    have h1 := hne t ht.1
    have e : 1 / w - 1 / (w + t) = (t : ℂ) / (w * (w + t)) := by
      field_simp
      ring
    rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    have h2 := norm_le_norm_add hw.le ht.1
    have h3 : 0 < ‖w + t‖ := lt_of_lt_of_le hwn h2
    rw [div_le_div_iff₀ (mul_pos hwn h3) (by positivity)]
    have := mul_le_mul_of_nonneg_left h2 hwn.le
    nlinarith [ht.1]
  rw [hI]
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / w - 1 / (w + t)) volume 0 1 :=
    IntervalIntegrable.sub intervalIntegrable_const hc.intervalIntegrable
  calc ‖∫ t in (0 : ℝ)..1, (1 / w - 1 / (w + t))‖
      ≤ ∫ t in (0 : ℝ)..1, ‖1 / w - 1 / (w + t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, t / ‖w‖ ^ 2 :=
        intervalIntegral.integral_mono_on zero_le_one hint1.norm
          (by apply Continuous.intervalIntegrable; fun_prop) hpt
    _ = 1 / (2 * ‖w‖ ^ 2) := by
        rw [intervalIntegral.integral_div, integral_id]
        field_simp
        ring

/-! ## (2) The majorant series -/

/-- `g(n) = 1/(2(n + 3/2)²)`. -/
noncomputable def gD (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 3 / 2) ^ 2)

theorem gD_le (n : ℕ) : gD n ≤ 1 / 2 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by
  unfold gD
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

theorem summable_gD : Summable gD := by
  refine Summable.of_nonneg_of_le (fun n => by unfold gD; positivity) (fun n => ?_)
    (Complex.summable_one_div_natCast_add_one_sq)
  unfold gD
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **`∑ g(n) ≤ 1/2`.** -/
theorem tsum_g_le : ∑' n, gD n ≤ 1 / 2 := by
  refine Real.tsum_le_of_sum_le (fun n => by unfold gD; positivity) fun s => ?_
  set N := s.sup id + 1 with hN
  have hsN : s ⊆ Finset.range N := fun n hn => by
    rw [Finset.mem_range, hN]
    have := Finset.le_sup (f := id) hn
    simp only [id] at this
    omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsN
    (fun n _ _ => (show 0 ≤ gD n by unfold gD; positivity))
  have h2 : ∑ n ∈ Finset.range N, gD n ≤
      ∑ n ∈ Finset.range N, 1 / 2 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) :=
    Finset.sum_le_sum fun n _ => gD_le n
  have h3 : ∑ n ∈ Finset.range N, 1 / 2 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) =
      1 / 2 * (1 - 1 / ((N : ℝ) + 1)) := by
    rw [← Finset.mul_sum]
    congr 1
    have := Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + 1)) N
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [show ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) =
      ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1)) from
      Finset.sum_congr rfl fun n _ => by ring_nf, this]
    simp
  have h4 : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-! ## (3) `ψ(z) − log z = −∑ d_n` -/

/-- **The Euler–Mascheroni series** `γ = ∑(1/(n+1) − (log(n+2) − log(n+1)))`. -/
theorem hasSum_gamma :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)))
      Real.eulerMascheroniConstant := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) -
      (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
    intro n
    have h1 : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) =
        Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 2) / ((n : ℝ) + 1) by positivity)
    have h3 : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  refine Real.tendsto_eulerMascheroniSeq.congr fun N => ?_
  rw [Real.eulerMascheroniSeq, Finset.sum_sub_distrib]
  have hH : (harmonic N : ℝ) = ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    simp [one_div]
  have hL : ∑ n ∈ Finset.range N, (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) =
      Real.log ((N : ℝ) + 1) := by
    have := Finset.sum_range_sub (fun n : ℕ => Real.log ((n : ℝ) + 1)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, Real.log_one,
      sub_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun n _ => by ring_nf
  rw [hH, hL]

/-- `A_n = log(n + z) − log(n + 1) → 0`. -/
theorem tendsto_A {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.log ((n : ℂ) + z) - (Real.log ((n : ℝ) + 1) : ℂ)) atTop
      (𝓝 0) := by
  have hrat : Tendsto (fun n : ℕ => ((n : ℂ) + z) / ((n : ℂ) + 1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (h0.const_mul (z - 1)).const_add 1
    rw [mul_zero, add_zero] at h1
    refine h1.congr fun n => ?_
    have hn : (n : ℂ) + 1 ≠ 0 := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
    ring
  have hlog := ((continuousAt_clog (Or.inl (by simp : (0 : ℝ) < (1 : ℂ).re))).tendsto).comp
    hrat
  rw [Complex.log_one] at hlog
  refine hlog.congr fun n => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnz : (n : ℂ) + z ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hq : ((n : ℂ) + z) / ((n : ℂ) + 1) ≠ 0 := div_ne_zero hnz (by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact Complex.ofReal_ne_zero.mpr hn1.ne')
  have e := Complex.log_ofReal_mul hn1 hq
  have e2 : (((n : ℝ) + 1 : ℝ) : ℂ) * (((n : ℂ) + z) / ((n : ℂ) + 1)) = (n : ℂ) + z := by
    push_cast
    field_simp
  rw [e2] at e
  simp only [Function.comp]
  rw [e]
  ring

/-- **`ψ(z) − log z = −∑ d(n + z)`** for `Re z > 0`, with the series summable. -/
theorem psi_sub_log {z : ℂ} (hz : 0 < z.re) (hs : Summable fun n : ℕ => dTerm ((n : ℂ) + z)) :
    Complex.digamma z - Complex.log z = -∑' n : ℕ, dTerm ((n : ℂ) + z) := by
  have hz' : ∀ n : ℕ, z ≠ -n := fun n h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hA := Complex.hasSum_digamma hz'
  have hB : HasSum (fun n : ℕ => ((1 / ((n : ℝ) + 1) -
      (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ))
      (Real.eulerMascheroniConstant : ℂ) := Complex.hasSum_ofReal.mpr hasSum_gamma
  have hC := hs.hasSum
  set A : ℕ → ℂ := fun n => Complex.log ((n : ℂ) + z) - (Real.log ((n : ℝ) + 1) : ℂ) with hAdef
  have hterm : ∀ n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)) -
      ((1 / ((n : ℝ) + 1) - (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ) +
        dTerm ((n : ℂ) + z) = A n - A (n + 1) := by
    intro n
    simp only [hAdef, dTerm]
    push_cast
    ring_nf
  have hsum := (hA.sub hB).add hC
  have hT : HasSum (fun n => A n - A (n + 1)) (A 0) := by
    refine Complex.hasSum_sub_succ_of_tendsto_zero (tendsto_A hz) ?_
    exact ((hA.sub hB).add hC).summable.congr hterm
  have huniq := hsum.unique (hT.congr_fun hterm)
  have hA0 : A 0 = Complex.log z := by
    simp [hAdef]
  rw [hA0] at huniq
  linear_combination huniq

/-! ## (4) `DigammaLine` -/

/-- **`DigammaLine` HOLDS.** -/
theorem digammaLine_holds : DigammaLine := by
  intro τ
  set z := sR τ with hzdef
  have hz : 0 < z.re := by rw [hzdef, sR_re]; norm_num
  have hre : ∀ n : ℕ, ((n : ℂ) + z).re = n + 3 / 2 := by
    intro n
    simp [hzdef, sR_re]
  have hbd : ∀ n : ℕ, ‖dTerm ((n : ℂ) + z)‖ ≤ gD n := by
    intro n
    have hpos : 0 < ((n : ℂ) + z).re := by rw [hre]; positivity
    refine (norm_d_le hpos).trans ?_
    unfold gD
    have h1 : (n : ℝ) + 3 / 2 ≤ ‖(n : ℂ) + z‖ := by
      rw [← hre]
      exact Complex.re_le_norm _
    apply one_div_le_one_div_of_le (by positivity)
    have h2 : ((n : ℝ) + 3 / 2) ^ 2 ≤ ‖(n : ℂ) + z‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    linarith
  have hs : Summable fun n : ℕ => dTerm ((n : ℂ) + z) :=
    Summable.of_norm_bounded summable_gD hbd
  rw [psi_sub_log hz hs, norm_neg]
  exact (tsum_of_norm_bounded summable_gD.hasSum hbd).trans tsum_g_le

end Principia.Common.TernaryGoldbach.AG
