/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonLeftLD

set_option autoImplicit false

/-!
# `AG.VM32` PROVED: `∑ Λ(n) n^{−3/2} ≤ 7/4`

**`vm32_holds : VM32`** (true value `1.50524`). Route:
* `∑Λ(n)n^{−3/2} = (∑ log n·n^{−3/2})/(∑ n^{−3/2})` (`vm_ratio`): Mathlib
  `ArithmeticFunction.LSeries_vonMangoldt_eq` (`L Λ = −(L 1)'/L 1`) and `LSeries_deriv`
  (`(L 1)' = −L(log)`), read off in `ℝ` (`LSeries_ofReal`);
* `∑ log n·n^{−3/2} ≤ log 2/2^{3/2} + 2(log 2 + 2)/√2 ≤ 4.06` (`sum_log_le`): with
  `F(t) = 2(log t + 2)t^{−1/2}`, `F' = −log t·t^{−3/2}` and `log t·t^{−3/2}` decreasing on `[2, ∞)`
  (`antitoneOn_f`), the mean value theorem gives `log n·n^{−3/2} ≤ F(n − 1) − F(n)` for `n ≥ 3`, and
  the sum telescopes;
* `∑ n^{−3/2} ≥ 1 + √2 − 2/100 ≥ 2.39` (`sum_one_ge`): `n^{−3/2} ≥ 2(n^{−1/2} − (n + 1)^{−1/2})`,
  telescoped to `n = 9999`.
So the ratio is `≤ 4.06/2.39 < 7/4`.
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology
open scoped ArithmeticFunction

/-! ## (1) The ratio identity -/

/-- **A real-coefficient `L`-series at a real point is the real series.** -/
theorem LSeries_ofReal (g : ℕ → ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    LSeries (fun n => (g n : ℂ)) (σ : ℂ) = ((∑' n : ℕ, g n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow hσ]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- **`∑Λ(n)n^{−3/2} = (∑ log n·n^{−3/2})/(∑ n^{−3/2})`.** -/
theorem vm_ratio : ∑' n : ℕ, Λ n / (n : ℝ) ^ (3 / 2 : ℝ) =
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)) / ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hs : 1 < (((3 / 2 : ℝ)) : ℂ).re := by simp; norm_num
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq hs
  have hab : LSeries.abscissaOfAbsConv 1 < (((3 / 2 : ℝ)) : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    simp only [Complex.ofReal_re]
    exact_mod_cast (show (1 : ℝ) < 3 / 2 by norm_num)
  rw [LSeries_deriv hab, neg_neg] at h1
  have e1 := LSeries_ofReal (fun n => Λ n) (show (3 / 2 : ℝ) ≠ 0 by norm_num)
  have e2 : LSeries (LSeries.logMul 1) (((3 / 2 : ℝ)) : ℂ) =
      ((∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← LSeries_ofReal (fun n => Real.log n) (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
    congr 1
    funext n
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  have e3 : LSeries 1 (((3 / 2 : ℝ)) : ℂ) =
      ((∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← LSeries_ofReal (fun _ => (1 : ℝ)) (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
    congr 1
  rw [e1, e2, e3, ← Complex.ofReal_div] at h1
  exact_mod_cast h1

/-! ## (2) `∑ log n·n^{−3/2} ≤ 4.06` -/

/-- `f(t) = log t·t^{−3/2}`. -/
noncomputable def fL (t : ℝ) : ℝ := Real.log t * t ^ (-(3 / 2) : ℝ)

/-- `F(t) = 2(log t + 2)t^{−1/2}`. -/
noncomputable def FL (t : ℝ) : ℝ := 2 * (Real.log t + 2) * t ^ (-(1 / 2) : ℝ)

theorem hasDerivAt_FL {t : ℝ} (ht : 0 < t) : HasDerivAt FL (-fL t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) ((-(1 / 2)) * t ^ (-(1 / 2) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt (fun x : ℝ => 2 * (Real.log x + 2)) (2 * (1 / t)) t := by
    have := ((Real.hasDerivAt_log ht.ne').add_const 2).const_mul 2
    simpa [one_div] using this
  have h3 : HasDerivAt FL (2 * (1 / t) * t ^ (-(1 / 2) : ℝ) +
      2 * (Real.log t + 2) * ((-(1 / 2)) * t ^ (-(1 / 2) - 1 : ℝ))) t := h2.mul h1
  refine h3.congr_deriv ?_
  have e1 : t ^ (-(1 / 2) - 1 : ℝ) = t ^ (-(3 / 2) : ℝ) := by norm_num
  have e2 : 1 / t * t ^ (-(1 / 2) : ℝ) = t ^ (-(3 / 2) : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  rw [e1, fL]
  have e3 : 2 * (1 / t) * t ^ (-(1 / 2) : ℝ) = 2 * t ^ (-(3 / 2) : ℝ) := by
    rw [mul_assoc, e2]
  rw [e3]
  ring

theorem hasDerivAt_fL {t : ℝ} (ht : 0 < t) :
    HasDerivAt fL ((1 - 3 / 2 * Real.log t) * t ^ (-(5 / 2) : ℝ)) t := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-(3 / 2) : ℝ)) ((-(3 / 2)) * t ^ (-(3 / 2) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h3 : HasDerivAt fL (t⁻¹ * t ^ (-(3 / 2) : ℝ) +
      Real.log t * ((-(3 / 2)) * t ^ (-(3 / 2) - 1 : ℝ))) t :=
    (Real.hasDerivAt_log ht.ne').mul h1
  refine h3.congr_deriv ?_
  have e1 : t ^ (-(3 / 2) - 1 : ℝ) = t ^ (-(5 / 2) : ℝ) := by norm_num
  have e2 : t⁻¹ * t ^ (-(3 / 2) : ℝ) = t ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  rw [e1]
  have e3 : t⁻¹ * t ^ (-(3 / 2) : ℝ) + Real.log t * (-(3 / 2) * t ^ (-(5 / 2) : ℝ)) =
      t ^ (-(5 / 2) : ℝ) - 3 / 2 * Real.log t * t ^ (-(5 / 2) : ℝ) := by
    rw [e2]
    ring
  rw [e3]
  ring

/-- **`f` is decreasing on `[2, ∞)`** (`f' = (1 − (3/2)log t)t^{−5/2} ≤ 0` since `log 2 > 2/3`). -/
theorem antitoneOn_f : AntitoneOn fL (Ici 2) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 2) ?_ ?_ ?_
  · intro t ht
    have ht' : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht
    exact (hasDerivAt_fL ht').continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : (0 : ℝ) < t := lt_trans (by norm_num) ht
    exact (hasDerivAt_fL ht').differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : (0 : ℝ) < t := lt_trans (by norm_num) ht
    rw [(hasDerivAt_fL ht').deriv]
    have hl : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (le_of_lt ht)
    have h2 := Real.log_two_gt_d9
    have hp : 0 < t ^ (-(5 / 2) : ℝ) := Real.rpow_pos_of_pos ht' _
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hp.le

/-- **`f(n) ≤ F(n − 1) − F(n)`** for real `n ≥ 3` (mean value theorem). -/
theorem fL_le_FL {n : ℝ} (hn : 3 ≤ n) : fL n ≤ FL (n - 1) - FL n := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope FL (fun t => -fL t)
    (show n - 1 < n by linarith)
    (fun t ht =>
      (hasDerivAt_FL (lt_of_lt_of_le (by linarith) ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_FL (lt_trans (by linarith) ht.1))
  rw [show n - (n - 1) = 1 by ring, div_one] at hcd
  have hc2 : (2 : ℝ) ≤ c := by linarith [hc.1]
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hm := antitoneOn_f (Set.mem_Ici.mpr hc2) (Set.mem_Ici.mpr hn2) hc.2.le
  linarith

theorem FL_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ FL t := by
  unfold FL
  have := Real.log_nonneg ht
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ t by linarith) (-(1 / 2) : ℝ)
  positivity

/-- The terms: `log n/n^{3/2} = f(n)`. -/
theorem log_div_eq_fL (n : ℕ) : Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) = fL n := by
  unfold fL
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- **Partial sums telescope**: `∑_{k<N} f(k) + F(N − 1) ≤ f(2) + F(2)` for `N ≥ 3`. -/
theorem partial_fL (N : ℕ) (hN : 3 ≤ N) :
    ∑ k ∈ Finset.range N, fL k + FL ((N : ℝ) - 1) ≤ fL 2 + FL 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    have h0 : fL 0 = 0 := by simp [fL]
    have h1 : fL 1 = 0 := by simp [fL]
    rw [h0, h1]
    norm_num
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have h := fL_le_FL hNr
    push_cast
    rw [show (N : ℝ) + 1 - 1 = N by ring]
    linarith

/-- **`∑ log n·n^{−3/2} ≤ f(2) + F(2)`.** -/
theorem sum_log_le : ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ fL 2 + FL 2 := by
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := fun n =>
    div_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine Real.tsum_le_of_sum_le (fun n => hnn n) fun s => ?_
  set N := max (s.sup id + 1) 3 with hN
  have hsN : s ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_range, hN]
    have := Finset.le_sup (f := id) hn
    simp only [id] at this
    omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsN (fun n _ _ => hnn n)
  have h2 := partial_fL N (le_max_right _ _)
  have h3 : 0 ≤ FL ((N : ℝ) - 1) := FL_nonneg (by
    have : (3 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _ : 3 ≤ N)
    linarith)
  simp_rw [log_div_eq_fL] at h1 ⊢
  linarith

/-! ## (3) `∑ n^{−3/2} ≥ 2.39` -/

/-- `n^{3/2} = n√n`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- **`2(n^{−1/2} − (n + 1)^{−1/2}) ≤ n^{−3/2}`** for `n ≥ 1`. -/
theorem tele_le {x : ℝ} (hx : 1 ≤ x) :
    2 * ((Real.sqrt x)⁻¹ - (Real.sqrt (x + 1))⁻¹) ≤ (x * Real.sqrt x)⁻¹ := by
  set a := Real.sqrt x with ha
  set b := Real.sqrt (x + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hab : a < b := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hb0 : 0 < b := lt_trans ha0 hab
  rw [← ha2]
  have key : 2 * (b - a) * (a ^ 2 * a) ≤ a * b := by
    nlinarith [mul_pos ha0 hb0, mul_pos ha0 ha0, hab, mul_pos (sub_pos.mpr hab) ha0]
  have e : 2 * (a⁻¹ - b⁻¹) = 2 * (b - a) / (a * b) := by
    field_simp
  rw [e, ← one_div, div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)]
  nlinarith [key]

/-- **The telescoped partial sums**: `∑_{k ≤ M} k^{−3/2} ≥ 1 + 2/√2 − 2/√(M + 1)`, `M ≥ 1`. -/
theorem partial_one (M : ℕ) (hM : 1 ≤ M) :
    1 + 2 * (Real.sqrt 2)⁻¹ - 2 * (Real.sqrt ((M : ℝ) + 1))⁻¹ ≤
      ∑ k ∈ Finset.range (M + 1), ((k : ℝ) * Real.sqrt k)⁻¹ := by
  induction M, hM using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ M hM ih =>
    rw [Finset.sum_range_succ]
    have hMr : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ M + 1 by omega)
    have h := tele_le hMr
    push_cast at h ⊢
    linarith

/-- **`∑ n^{−3/2} ≥ 1 + 2/√2 − 1/50`.** -/
theorem sum_one_ge : 1 + 2 * (Real.sqrt 2)⁻¹ - 1 / 50 ≤
    ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have h1 := hsum.sum_le_tsum (Finset.range (9999 + 1))
    (fun n _ => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have h2 := partial_one 9999 (by norm_num)
  have e : ∀ k : ℕ, ((k : ℝ) * Real.sqrt k)⁻¹ = 1 / (k : ℝ) ^ (3 / 2 : ℝ) := fun k => by
    rw [rpow_three_halves (Nat.cast_nonneg k), one_div]
  simp_rw [e] at h2
  have h3 : Real.sqrt (((9999 : ℕ) : ℝ) + 1) = 100 := by
    rw [show (((9999 : ℕ) : ℝ) + 1) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h3] at h2
  linarith

/-! ## (4) `VM32` -/

/-- **`VM32` HOLDS**: `∑Λ(n)n^{−3/2} ≤ 4.06/2.39 < 7/4`. -/
theorem vm32_holds : VM32 := by
  unfold VM32
  rw [vm_ratio]
  have hA := sum_log_le
  have hZ := sum_one_ge
  have hs2 : (1.414 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs2' : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hl := Real.log_two_lt_d9
  -- `f(2) + F(2) = (log 2/2 + 2(log 2 + 2))/√2`
  have hf2 : fL 2 + FL 2 = (Real.log 2 / 2 + 2 * (Real.log 2 + 2)) / Real.sqrt 2 := by
    unfold fL FL
    have e1 : (2 : ℝ) ^ (-(3 / 2) : ℝ) = 1 / (2 * Real.sqrt 2) := by
      rw [Real.rpow_neg (by norm_num), rpow_three_halves (by norm_num), one_div]
    have e2 : (2 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt 2 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]
    rw [e1, e2]
    field_simp
  have hpos : 0 < Real.sqrt 2 := by positivity
  have hZpos : (2.39 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    have h : 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
      rw [← div_eq_mul_inv, div_eq_iff hpos.ne', Real.mul_self_sqrt (by norm_num)]
    rw [h] at hZ
    linarith
  have hAle : ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 4.06 := by
    refine hA.trans ?_
    rw [hf2, div_le_iff₀ hpos]
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  linarith

end Principia.Common.TernaryGoldbach.AG
