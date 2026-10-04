/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIISpine

set_option autoImplicit false

/-!
# `T2S.SecInt` PROVED: `eq:bycaus` and Cauchy–Schwarz for `S_{II}`

`secInt_holds : T2S.SecInt` — for `0 < x`, `0 < U`, `3 ≤ V`, `VU ≤ x`,
`‖S_{II}‖ ≤ 4∫_V^{x/U} (√(S₁S₂) + √(S₁S₃)) dW/W` with `S₁, S₂, S₃` the concrete objects
`T2S.s1`, `T2S.s2` (at `U' = max(U, x/2W)`, `W' = max(V, W/2)`), `T2S.s3` (`typeII.tex` 59-146).

1. `eta2_eq_int` — `eq:conque` at `y = mn/x`: `η₂(y) = 4∫_{(a,b)} dW/W`, `a = max(x/2m, n)`,
   `b = min(x/m, 2n)` (four cases in `y`), and `int_ind`: the `W`-integral of the indicator
   `1[x/2W < m ≤ x/W, W/2 < n ≤ W]/W` over `[V, x/U]` is that integral when `m > U`, `n > V`.
2. `sII_int` — `S_{II} = 4∫_V^{x/U} ∑_m ∑_n a_m b_n·ind·e(αmn)/W dW` (`coefA`: the `m`-coefficient
   is `f(m)c_m`; `coefB`: the `n`-coefficient is `Λ(n)f(n)1_{n > V}`; terms with `m ≤ U` or `n ≤ V`
   vanish on both sides).
3. `sum_bT`, `zS_split`, `nonprime_le`, `F_le` — at fixed `W ≥ V ≥ 3` the integrand is
   `(1/W)∑_{m ∈ mSet} c_m (∑_{W' < p ≤ W} log p·e(αmp) + non-primes)`, the non-prime part is at most
   `ψ(W) − θ(W)` (Mathlib's `psi_sub_theta_eq_sum_not_prime`), and Cauchy–Schwarz gives
   `√(S₁S₂) + √(S₁S₃)`.
4. `secI_ii` — the right side is integrable (a step function over `W`, bounded on `[V, x/U]`).

No hypothesis, no cited input: this link is closed. With it, `vinland1At_of_rest`,
`eriksagaAt_of_rest`, `secIIAt_of_rest` state the three Type II links from the links still open
(`Menson2`, `Kraken`, `KastLarge`, the three `…Calc`) plus `HC.KastCited` and `EB.RS62Thm13`.
-/

namespace Principia.Common.TernaryGoldbach.T2S

open ArithmeticFunction Principia.Common.Goldbach MeasureTheory Set
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc

/-- **The indicator of `eq:bycaus`**: `x/2W < m ≤ x/W` and `W/2 < n ≤ W`. -/
noncomputable def ind (x : ℝ) (m n : ℕ) (W : ℝ) : ℝ :=
  if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 else 0

/-- **`eq:conque` at an integer point**: `η₂(mn/x) = 4∫_{(a,b)} dW/W`,
`a = max(x/2m, n)`, `b = min(x/m, 2n)`. -/
theorem eta2_eq_int (x : ℝ) (m n : ℕ) (hx : 0 < x) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    HW.eta2 ((m : ℝ) * n / x) =
      4 * ∫ W in Ioo (max (x / (2 * m)) n) (min (x / m) (2 * n)), 1 / W := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set y := (m : ℝ) * n / x with hy
  have hy0 : 0 < y := by positivity
  have exm : x / m = n / y := by rw [hy]; field_simp
  have ex2m : x / (2 * m) = n / (2 * y) := by rw [hy]; field_simp
  rw [exm, ex2m]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt y (1 / 4) with h1 | h1
  · rw [eta2_zero_of_le _ h1]
    have : Ioo (max (n / (2 * y)) (n : ℝ)) (min (n / y) (2 * n)) = ∅ := by
      refine Ioo_eq_empty (not_lt.mpr ?_)
      refine le_trans (min_le_right _ _) (le_trans ?_ (le_max_left _ _))
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [this, Measure.restrict_empty, integral_zero_measure, mul_zero]
  rcases le_or_gt 1 y with h2 | h2
  · rw [eta2_zero_of_one_le _ h2]
    have : Ioo (max (n / (2 * y)) (n : ℝ)) (min (n / y) (2 * n)) = ∅ := by
      refine Ioo_eq_empty (not_lt.mpr ?_)
      refine le_trans (min_le_left _ _) (le_trans ?_ (le_max_right _ _))
      rw [div_le_iff₀ hy0]
      nlinarith
    rw [this, Measure.restrict_empty, integral_zero_measure, mul_zero]
  have hint : ∀ a b : ℝ, 0 < a → a < b → ∫ W in Ioo a b, 1 / W = Real.log (b / a) := by
    intro a b ha hab
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact integral_one_div_of_pos ha (by linarith)
  unfold HW.eta2
  rw [if_pos hy0]
  rcases le_or_gt y (1 / 2) with h3 | h3
  · have ea : max (n / (2 * y)) (n : ℝ) = n / (2 * y) := by
      refine max_eq_left ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have eb : min (n / y) (2 * n : ℝ) = 2 * n := by
      refine min_eq_right ?_
      rw [le_div_iff₀ hy0]
      nlinarith
    rw [ea, eb, hint _ _ (by positivity) (by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith)]
    have e4 : 2 * (n : ℝ) / (n / (2 * y)) = 4 * y := by field_simp; ring
    have hle : Real.log (2 * y) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    rw [e4, abs_of_nonpos hle]
    have e : Real.log (4 * y) = Real.log 2 + Real.log (2 * y) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      ring_nf
    have hpos : 0 < Real.log (4 * y) := Real.log_pos (by linarith)
    rw [max_eq_left (by linarith)]
    linarith
  · have ea : max (n / (2 * y)) (n : ℝ) = n := by
      refine max_eq_right ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have eb : min (n / y) (2 * n : ℝ) = n / y := by
      refine min_eq_left ?_
      rw [div_le_iff₀ hy0]
      nlinarith
    rw [ea, eb, hint _ _ (by positivity) (by
      rw [lt_div_iff₀ hy0]
      nlinarith)]
    have e1 : (n : ℝ) / y / n = 1 / y := by field_simp
    have hge : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
    rw [e1, abs_of_nonneg hge]
    have e : Real.log (1 / y) = Real.log 2 - Real.log (2 * y) := by
      rw [Real.log_mul (by norm_num) hy0.ne', one_div, Real.log_inv]
      ring
    have hpos : 0 < Real.log (1 / y) := by
      rw [one_div]
      exact Real.log_pos (by rw [one_lt_inv₀ hy0]; exact h2)
    rw [max_eq_left (by linarith)]
    linarith

/-- `ind/W` agrees with `1_{(a,b)}·(1/W)` off `{n, x/m}`, for `W > 0`. -/
theorem ind_eq (x : ℝ) (m n : ℕ) (hm : 1 ≤ m) (W : ℝ) (hW : 0 < W)
    (h1 : W ≠ n) (h2 : W ≠ x / m) :
    ind x m n W / W = (Ioo (max (x / (2 * m)) n) (min (x / m) (2 * n))).indicator
      (fun W => 1 / W) W := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have c1 : x / (2 * W) < m ↔ x / (2 * m) < W := by
    rw [div_lt_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  have c2 : (m : ℝ) ≤ x / W ↔ W ≤ x / m := by
    rw [le_div_iff₀ hW, le_div_iff₀ hmR]
    constructor <;> intro h <;> linarith
  have c3 : W / 2 < n ↔ W < 2 * n := by
    constructor <;> intro h <;> linarith
  unfold ind
  by_cases hc : x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W
  · rw [if_pos hc, indicator_of_mem]
    obtain ⟨a1, a2, a3, a4⟩ := hc
    rw [c1] at a1
    rw [c2] at a2
    rw [c3] at a3
    refine ⟨max_lt a1 (lt_of_le_of_ne a4 (Ne.symm h1)), lt_min (lt_of_le_of_ne a2 h2) a3⟩
  · rw [if_neg hc, indicator_of_notMem, zero_div]
    rintro ⟨ha, hb⟩
    refine hc ⟨c1.mpr (lt_of_le_of_lt (le_max_left _ _) ha), c2.mpr (le_of_lt
      (lt_of_lt_of_le hb (min_le_left _ _))), c3.mpr (lt_of_lt_of_le hb (min_le_right _ _)),
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) ha)⟩

/-- `ind/W =ᵐ 1_{(a,b)}/W` on `(V, x/U]`, `V > 0`. -/
theorem ind_ae (x V U' : ℝ) (m n : ℕ) (hm : 1 ≤ m) (hV : 0 < V) :
    (fun W => ind x m n W / W) =ᵐ[volume.restrict (Ioc V U')]
      (Ioo (max (x / (2 * m)) n) (min (x / m) (2 * n))).indicator (fun W => 1 / W) := by
  have hfin : ({(n : ℝ), x / m} : Set ℝ).Countable := (Set.toFinite _).countable
  have hae : ∀ᵐ W ∂volume, W ∉ ({(n : ℝ), x / m} : Set ℝ) := hfin.ae_notMem _
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hae] with W hW hWI
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hW
  exact ind_eq x m n hm W (lt_trans hV hWI.1) hW.1 hW.2

/-- The `W`-integral of `ind/W` over `[V, x/U]` is the integral over `(a, b)` when
`V < n`, `U < m`. -/
theorem int_ind (x U V : ℝ) (m n : ℕ) (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hVU : V ≤ x / U) (hm : 1 ≤ m) (hn : V < n) (hUm : U < m) :
    ∫ W in V..(x / U), ind x m n W / W =
      ∫ W in Ioo (max (x / (2 * m)) n) (min (x / m) (2 * n)), 1 / W := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [intervalIntegral.integral_of_le hVU, setIntegral_congr_ae₀ measurableSet_Ioc.nullMeasurableSet
    (by
      have := ind_ae x V (x / U) m n hm hV
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at this
      exact this), setIntegral_indicator measurableSet_Ioo]
  have hsub : Ioo (max (x / (2 * m)) n) (min (x / m) (2 * n)) ⊆ Ioc V (x / U) := by
    intro W hW
    rw [mem_Ioo] at hW
    refine mem_Ioc.mpr ⟨lt_of_lt_of_le hn (le_trans (le_max_right _ _) hW.1.le),
      le_trans hW.2.le (le_trans (min_le_left _ _) ?_)⟩
    exact div_le_div_of_nonneg_left hx.le hU hUm.le
  rw [inter_eq_right.mpr hsub]

/-- `ind/W` is integrable on `[V, x/U]`. -/
theorem ind_ii (x U V : ℝ) (m n : ℕ) (hV : 0 < V) (hVU : V ≤ x / U)
    (hm : 1 ≤ m) : IntervalIntegrable (fun W => ind x m n W / W) volume V (x / U) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hVU]
  have hc : IntegrableOn (fun W : ℝ => 1 / W) (Ioc V (x / U)) volume := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.div continuousOn_id fun W hW => (lt_of_lt_of_le hV hW.1).ne'
  exact (hc.indicator measurableSet_Ioo).congr_fun_ae (ind_ae x V (x / U) m n hm hV).symm


/-! ## (2) The coefficients and the double sum -/

/-- `c_m = 0` for `m ≤ U` (every divisor is `≤ m`). -/
theorem cU_zero (U : ℝ) (m : ℕ) (hm : (m : ℝ) ≤ U) : cU U m = 0 := by
  unfold cU
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  exfalso
  have hdm : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hd.1.1
  have : (d : ℝ) ≤ m := by exact_mod_cast hdm
  linarith [hd.2]

/-- **The `m`-coefficient**: `((μ − μ_{≤U})f ∗ ζf)(m) = f(m)·c_m` (`0 ≤ U`). -/
theorem coefA (U : ℝ) (hU : 0 ≤ U) (m : ℕ) :
    (tw ((μ : ArithmeticFunction ℝ) - aU U) * tw (ζ : ArithmeticFunction ℝ)) m =
      fOdd m * cU U m := by
  rw [← tw_mul, tw_apply, ArithmeticFunction.coe_mul_zeta_apply, mul_comm]
  congr 1
  unfold cU
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  unfold aU
  rw [MinSum.truncate_apply, ArithmeticFunction.intCoe_apply]
  by_cases h : U < (d : ℝ)
  · have : ¬ d ≤ ⌊U⌋₊ := by
      rw [not_le]
      exact (Nat.floor_lt hU).mpr h
    rw [if_neg this, if_pos h, neg_zero, add_zero]
  · have : d ≤ ⌊U⌋₊ := Nat.le_floor (not_lt.mp h)
    rw [if_pos this, if_neg h, add_neg_cancel]

/-- **The `n`-coefficient**: `((Λ − Λ_{≤V})f)(n) = Λ(n)f(n)·1_{n > V}` (`0 ≤ V`). -/
theorem coefB (V : ℝ) (hV : 0 ≤ V) (n : ℕ) :
    tw (Λ - bV V) n = if V < (n : ℝ) then Λ n * fOdd n else 0 := by
  rw [tw_apply, sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  unfold bV
  rw [MinSum.truncate_apply]
  by_cases h : V < (n : ℝ)
  · have : ¬ n ≤ ⌊V⌋₊ := by
      rw [not_le]
      exact (Nat.floor_lt hV).mpr h
    rw [if_neg this, if_pos h, neg_zero, add_zero]
  · have : n ≤ ⌊V⌋₊ := Nat.le_floor (not_lt.mp h)
    rw [if_pos this, if_neg h, add_neg_cancel, zero_mul]

/-- `S_{II}` as the double sum `∑_m f(m)c_m ∑_n ((Λ − Λ_{≤V})f)(n) w(mn)`. -/
theorem sII_double (x α U V : ℝ) (hU : 0 ≤ U) :
    sII x α U V = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ((fOdd m * cU U m : ℝ) : ℂ) *
      ∑ n ∈ Finset.Ioc 0 (⌊x⌋₊ / m), ((tw (Λ - bV V) n : ℝ) : ℂ) * wt x α (m * n) := by
  have hc : tw ((μ : ArithmeticFunction ℝ) - aU U) * tw (Λ - bV V) *
      tw (ζ : ArithmeticFunction ℝ) =
      tw ((μ : ArithmeticFunction ℝ) - aU U) * tw (ζ : ArithmeticFunction ℝ) *
        tw (Λ - bV V) := by ring
  unfold sII
  rw [hc, sP_mul_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coefA U hU m]

/-- **The term of `eq:bycaus`**: `a_m b_n (ind/W) e(mnα)`. -/
noncomputable def bT (x α U V : ℝ) (m n : ℕ) (W : ℝ) : ℂ :=
  ((fOdd m * cU U m * tw (Λ - bV V) n * (ind x m n W / W) : ℝ) : ℂ) *
    e (((m * n : ℕ) : ℝ) * α)

theorem bT_ii (x α U V : ℝ) (m n : ℕ) (hV : 0 < V) (hVU : V ≤ x / U) (hm : 1 ≤ m) :
    IntervalIntegrable (bT x α U V m n) volume V (x / U) := by
  have h := ((ind_ii x U V m n hV hVU hm).const_mul (fOdd m * cU U m * tw (Λ - bV V) n))
  have h' : IntervalIntegrable (fun W => ((fOdd m * cU U m * tw (Λ - bV V) n *
      (ind x m n W / W) : ℝ) : ℂ)) volume V (x / U) := ⟨h.1.ofReal, h.2.ofReal⟩
  exact h'.mul_const _

/-- **One term of `S_{II}` is `4∫_V^{x/U}` of its `eq:bycaus` integrand.** -/
theorem term_eq (x α U V : ℝ) (m n : ℕ) (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hVU : V ≤ x / U) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((fOdd m * cU U m : ℝ) : ℂ) * (((tw (Λ - bV V) n : ℝ) : ℂ) * wt x α (m * n)) =
      4 * ∫ W in V..(x / U), bT x α U V m n W := by
  unfold bT
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul]
  by_cases hA : (m : ℝ) ≤ U
  · rw [cU_zero U m hA]
    simp
  by_cases hB : (n : ℝ) ≤ V
  · rw [coefB V hV.le n, if_neg (not_lt.mpr hB)]
    simp
  push Not at hA hB
  have hI : ∫ W in Ioo (max (x / (2 * m)) n) (min (x / m) (2 * n)), 1 / W =
      HW.eta2 ((m : ℝ) * n / x) / 4 := by
    rw [eta2_eq_int x m n hx hm hn]
    ring
  rw [int_ind x U V m n hx hU hV hVU hm hB hA, hI]
  unfold wt
  push_cast
  ring

/-- **`S_{II} = 4∫_V^{x/U} ∑_m ∑_n a_m b_n (ind/W) e(mnα) dW`** (`eq:bycaus`). -/
theorem sII_int (x α U V : ℝ) (hx : 0 < x) (hU : 0 < U) (hV : 0 < V) (hVU : V ≤ x / U) :
    sII x α U V = 4 * ∫ W in V..(x / U), ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      ∑ n ∈ Finset.Ioc 0 (⌊x⌋₊ / m), bT x α U V m n W := by
  rw [sII_double x α U V hU.le, intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hm).1
    rw [intervalIntegral.integral_finsetSum, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      exact term_eq x α U V m n hx hU hV hVU hm1 (Finset.mem_Ioc.mp hn).1
    · intro n _
      exact bT_ii x α U V m n hV hVU hm1
  · intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hm).1
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum _ fun n _ => bT_ii x α U V m n hV hVU hm1

/-! ## (3) The integrand at fixed `W`: unsmoothed sums and Cauchy–Schwarz -/

/-- **The `n`-range** `{n odd : max(V, W/2) < n ≤ W}`. -/
noncomputable def nSet (V W : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊W⌋₊).filter (fun n => n % 2 = 1 ∧ max V (W / 2) < (n : ℝ))

/-- **`∑_{max(V,W/2) < n ≤ W, n odd} Λ(n)e(αmn)`**. -/
noncomputable def zS (α V W : ℝ) (m : ℕ) : ℂ :=
  ∑ n ∈ nSet V W, ((Λ n : ℝ) : ℂ) * e (((m * n : ℕ) : ℝ) * α)

theorem fOdd_odd (m : ℕ) (h : m % 2 = 1) : fOdd m = 1 := by
  rw [fOdd_apply, if_pos h]

theorem fOdd_even (m : ℕ) (h : ¬ m % 2 = 1) : fOdd m = 0 := by
  rw [fOdd_apply, if_neg h]

/-- The term at an `m` of the range. -/
theorem bT_in (x α U V W : ℝ) (m n : ℕ) (hV : 0 ≤ V) (hW : 0 < W) (hm : m ∈ mSet x U W) :
    bT x α U V m n W = ((1 / W : ℝ) : ℂ) * (cU U m : ℂ) *
      (if n ∈ nSet V W then ((Λ n : ℝ) : ℂ) * e (((m * n : ℕ) : ℝ) * α) else 0) := by
  rw [mSet, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨-, hmW⟩, hodd, hmax⟩ := hm
  have hmx : (m : ℝ) ≤ x / W := by
    have := Nat.cast_le (α := ℝ) |>.mpr hmW
    by_cases h0 : 0 ≤ x / W
    · exact this.trans (Nat.floor_le h0)
    · rw [Nat.floor_of_nonpos (not_le.mp h0).le] at hmW
      have : m = 0 := by omega
      omega
  have h2 : x / (2 * W) < m := lt_of_le_of_lt (le_max_left _ _) hmax
  unfold bT ind
  rw [coefB V hV n, fOdd_odd m hodd]
  by_cases hn : n ∈ nSet V W
  · have hn' := hn
    rw [nSet, Finset.mem_filter, Finset.mem_Icc] at hn'
    obtain ⟨⟨-, hnW⟩, hnodd, hnmax⟩ := hn'
    have hnW' : (n : ℝ) ≤ W := (Nat.cast_le.mpr hnW).trans (Nat.floor_le hW.le)
    rw [if_pos (lt_of_le_of_lt (le_max_left _ _) hnmax), fOdd_odd n hnodd,
      if_pos ⟨h2, hmx, lt_of_le_of_lt (le_max_right _ _) hnmax, hnW'⟩, if_pos hn]
    push_cast
    ring
  · rw [if_neg hn, mul_zero]
    have hz : (if V < (n : ℝ) then Λ n * fOdd n else 0) *
        (if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 else 0) = 0 := by
      by_cases hVn : V < (n : ℝ)
      · by_cases hc : x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W
        · by_cases hno : n % 2 = 1
          · exfalso
            refine hn ?_
            rw [nSet, Finset.mem_filter, Finset.mem_Icc]
            have hn1 : 1 ≤ n := by omega
            exact ⟨⟨hn1, Nat.le_floor hc.2.2.2⟩, hno, max_lt hVn hc.2.2.1⟩
          · rw [if_pos hVn, fOdd_even n hno]
            simp
        · rw [if_neg hc, mul_zero]
      · rw [if_neg hVn, zero_mul]
    have : (1 : ℝ) * cU U m * (if V < (n : ℝ) then Λ n * fOdd n else 0) *
        ((if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 else 0) / W) =
        0 := by
      rw [mul_div_assoc', mul_assoc (1 * cU U m), hz]
      simp
    rw [this]
    simp

/-- The term at an `m ≥ 1` off the range vanishes. -/
theorem bT_out (x α U V W : ℝ) (m n : ℕ) (hm1 : 1 ≤ m)
    (hm : m ∉ mSet x U W) : bT x α U V m n W = 0 := by
  unfold bT ind
  have hz : fOdd m * cU U m *
      (if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 else 0) = 0 := by
    by_cases hc : x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W
    · by_cases hodd : m % 2 = 1
      · by_cases hUm : U < (m : ℝ)
        · exfalso
          refine hm ?_
          rw [mSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hm1, Nat.le_floor hc.2.1⟩, hodd, max_lt hc.1 hUm⟩
        · rw [cU_zero U m (not_lt.mp hUm)]
          simp
      · rw [fOdd_even m hodd]
        simp
    · rw [if_neg hc, mul_zero]
  have : fOdd m * cU U m * tw (Λ - bV V) n *
      ((if x / (2 * W) < m ∧ (m : ℝ) ≤ x / W ∧ W / 2 < n ∧ (n : ℝ) ≤ W then 1 else 0) / W) =
      0 := by
    rw [mul_div_assoc', mul_right_comm (fOdd m * cU U m), hz]
    simp
  rw [this]
  simp

/-- **The integrand of `eq:bycaus` at `W`** is `(1/W)∑_{m} c_m ∑_{n} Λ(n)e(αmn)`. -/
theorem sum_bT (x α U V W : ℝ) (hx : 0 < x) (hV : 0 ≤ V) (hW1 : 1 ≤ W) :
    ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ n ∈ Finset.Ioc 0 (⌊x⌋₊ / m), bT x α U V m n W =
      ((1 / W : ℝ) : ℂ) * ∑ m ∈ mSet x U W, (cU U m : ℂ) * zS α V W m := by
  have hW : 0 < W := by linarith
  have hsub : mSet x U W ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro m hm
    rw [mSet, Finset.mem_filter, Finset.mem_Icc] at hm
    refine Finset.mem_Ioc.mpr ⟨hm.1.1, hm.1.2.trans (Nat.floor_le_floor ?_)⟩
    exact div_le_self hx.le hW1
  rw [Finset.mul_sum, ← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := hm
    rw [mSet, Finset.mem_filter, Finset.mem_Icc] at hm'
    have hmx : (m : ℝ) ≤ x / W :=
      (Nat.cast_le.mpr hm'.1.2).trans (Nat.floor_le (div_pos hx hW).le)
    have hnsub : nSet V W ⊆ Finset.Ioc 0 (⌊x⌋₊ / m) := by
      intro n hn
      rw [nSet, Finset.mem_filter, Finset.mem_Icc] at hn
      refine Finset.mem_Ioc.mpr ⟨hn.1.1, ?_⟩
      have hm1 : 0 < m := hm'.1.1
      rw [Nat.le_div_iff_mul_le hm1]
      apply Nat.le_floor
      have hnW : (n : ℝ) ≤ W := (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le hW.le)
      rw [le_div_iff₀ hW] at hmx
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    rw [Finset.sum_congr rfl fun n _ => bT_in x α U V W m n hV hW hm, ← Finset.mul_sum,
      Finset.sum_ite_mem, Finset.inter_eq_right.mpr hnsub, zS]
    ring
  · intro m hm hnm
    refine Finset.sum_eq_zero fun n _ => bT_out x α U V W m n (Finset.mem_Ioc.mp hm).1 hnm

/-- `zS = pS + (non-prime part)` when `V ≥ 3`. -/
theorem zS_split (α V W : ℝ) (m : ℕ) (hV : 3 ≤ V) :
    zS α V W m = pS α (max V (W / 2)) W m +
      ∑ n ∈ (nSet V W).filter (fun n => ¬ n.Prime),
        ((Λ n : ℝ) : ℂ) * e (((m * n : ℕ) : ℝ) * α) := by
  unfold zS
  rw [← Finset.sum_filter_add_sum_filter_not (nSet V W) Nat.Prime]
  congr 1
  have hset : (nSet V W).filter Nat.Prime =
      (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ max V (W / 2) < (p : ℝ)) := by
    ext p
    simp only [nSet, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      refine ⟨⟨h1, ?_, h3⟩, h4⟩
      have hp3 : (3 : ℝ) < p := lt_of_le_of_lt (hV.trans (le_max_left _ _)) h3
      have hp2 : p ≠ 2 := by
        rintro rfl
        norm_num at hp3
      exact Nat.odd_iff.mp (h4.odd_of_ne_two hp2)
  rw [hset, pS]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2.1]

/-- The non-prime part is at most `ψ(W) − θ(W)`. -/
theorem nonprime_le (α V W : ℝ) (m : ℕ) :
    ‖∑ n ∈ (nSet V W).filter (fun n => ¬ n.Prime),
        ((Λ n : ℝ) : ℂ) * e (((m * n : ℕ) : ℝ) * α)‖ ≤
      Chebyshev.psi W - Chebyshev.theta W := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  refine (norm_sum_le _ _).trans ?_
  have hn : ∀ n ∈ (nSet V W).filter (fun n => ¬ n.Prime),
      ‖((Λ n : ℝ) : ℂ) * e (((m * n : ℕ) : ℝ) * α)‖ = Λ n := by
    intro n _
    rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
  rw [Finset.sum_congr rfl hn]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
  intro n hn
  simp only [nSet, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
  exact ⟨⟨by omega, hn.1.1.2⟩, hn.2⟩

/-- **Cauchy–Schwarz**: `‖∑_{m ∈ s} c_m z_m‖ ≤ √(∑c_m²)·√(∑‖z_m‖²)`. -/
theorem cs_le (s : Finset ℕ) (c : ℕ → ℝ) (z : ℕ → ℂ) :
    ‖∑ m ∈ s, (c m : ℂ) * z m‖ ≤
      Real.sqrt (∑ m ∈ s, c m ^ 2) * Real.sqrt (∑ m ∈ s, ‖z m‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun m => |c m|) (fun m => ‖z m‖)
  simp only [sq_abs] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **The pointwise bound of `eq:costo`**: at `3 ≤ V ≤ W`,
`‖∑_m c_m zS_m‖ ≤ √(S₁S₂) + √(S₁S₃)`. -/
theorem F_le (x α U V W : ℝ) (hx : 0 < x) (hV : 3 ≤ V) (hW : V ≤ W) :
    ‖∑ m ∈ mSet x U W, (cU U m : ℂ) * zS α V W m‖ ≤
      Real.sqrt (s1 x U W * s2 x α (max U (x / (2 * W))) (max V (W / 2)) W) +
        Real.sqrt (s1 x U W * s3 x W) := by
  have hW0 : 0 < W := by linarith
  set N := fun m : ℕ => ∑ n ∈ (nSet V W).filter (fun n => ¬ n.Prime),
    ((Λ n : ℝ) : ℂ) * e (((m * n : ℕ) : ℝ) * α) with hN
  have hsplit : ∑ m ∈ mSet x U W, (cU U m : ℂ) * zS α V W m =
      ∑ m ∈ mSet x U W, (cU U m : ℂ) * pS α (max V (W / 2)) W m +
        ∑ m ∈ mSet x U W, (cU U m : ℂ) * N m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [zS_split α V W m hV, mul_add]
  have hmset : mSet x (max U (x / (2 * W))) W = mSet x U W := by
    unfold mSet
    have : max (x / (2 * W)) (max U (x / (2 * W))) = max (x / (2 * W)) U := by
      rw [max_comm U, ← max_assoc, max_self]
    rw [this]
  have h1 := cs_le (mSet x U W) (cU U) (pS α (max V (W / 2)) W)
  have h2 := cs_le (mSet x U W) (cU U) N
  have hs2 : ∑ m ∈ mSet x U W, ‖pS α (max V (W / 2)) W m‖ ^ 2 =
      s2 x α (max U (x / (2 * W))) (max V (W / 2)) W := by
    rw [s2, hmset]
  have hs3 : ∑ m ∈ mSet x U W, ‖N m‖ ^ 2 ≤ s3 x W := by
    unfold s3
    have hsub : mSet x U W ⊆ mSet x 0 W := by
      intro m hm
      rw [mSet, Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, hm.2.1, lt_of_le_of_lt ?_ hm.2.2⟩
      rw [max_eq_left (by positivity)]
      exact le_max_left _ _
    refine le_trans (Finset.sum_le_sum fun m _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (nonprime_le α V W m) 2
  have e1 : Real.sqrt (s1 x U W * s2 x α (max U (x / (2 * W))) (max V (W / 2)) W) =
      Real.sqrt (∑ m ∈ mSet x U W, cU U m ^ 2) *
        Real.sqrt (∑ m ∈ mSet x U W, ‖pS α (max V (W / 2)) W m‖ ^ 2) := by
    rw [hs2, Real.sqrt_mul (s1_nonneg x U W)]
    rfl
  have e2 : Real.sqrt (∑ m ∈ mSet x U W, cU U m ^ 2) *
      Real.sqrt (∑ m ∈ mSet x U W, ‖N m‖ ^ 2) ≤ Real.sqrt (s1 x U W * s3 x W) := by
    rw [Real.sqrt_mul (s1_nonneg x U W)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs3) (Real.sqrt_nonneg _)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [e1]
  exact add_le_add h1 (h2.trans e2)

/-! ## (4) The integrand `secI` is integrable on `[V, x/U]` -/

/-- Re-indexing a floor range: for `0 ≤ t ≤ T`,
`{k ∈ [1, ⌊t⌋] : P k} = {k ∈ [1, ⌊T⌋] : P k, k ≤ t}`. -/
theorem filter_floor (P : ℕ → Prop) [DecidablePred P] (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    (Finset.Icc 1 ⌊t⌋₊).filter P =
      (Finset.Icc 1 ⌊T⌋₊).filter (fun k => P k ∧ (k : ℝ) ≤ t) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hk : (k : ℝ) ≤ t := (Nat.le_floor_iff ht).mp h2
    exact ⟨⟨h1, Nat.le_floor (hk.trans htT)⟩, h3, hk⟩
  · rintro ⟨⟨h1, -⟩, h3, h4⟩
    exact ⟨⟨h1, Nat.le_floor h4⟩, h3⟩

/-- The `m`-condition as a measurable set in `W`. -/
theorem ms_m (x A : ℝ) (m : ℕ) : MeasurableSet
    {W : ℝ | (m % 2 = 1 ∧ max (x / (2 * W)) A < (m : ℝ)) ∧ (m : ℝ) ≤ x / W} := by
  have h1 : Measurable fun W : ℝ => max (x / (2 * W)) A := by fun_prop
  have h2 : Measurable fun W : ℝ => x / W := by fun_prop
  rw [Set.setOf_and, Set.setOf_and]
  exact ((MeasurableSet.const _).inter (measurableSet_lt h1 measurable_const)).inter
    (measurableSet_le measurable_const h2)

/-- The `p`-condition as a measurable set in `W`. -/
theorem ms_p (V : ℝ) (p : ℕ) : MeasurableSet
    {W : ℝ | (p.Prime ∧ max V (W / 2) < (p : ℝ)) ∧ (p : ℝ) ≤ W} := by
  have h1 : Measurable fun W : ℝ => max V (W / 2) := by fun_prop
  rw [Set.setOf_and, Set.setOf_and]
  exact ((MeasurableSet.const _).inter (measurableSet_lt h1 measurable_const)).inter
    (measurableSet_le measurable_const measurable_id)

/-- `mSet` over a fixed range `[1, ⌊x/V⌋]` for `W ≥ V > 0`. -/
theorem mSet_eq (x A V W : ℝ) (hx : 0 < x) (hV : 0 < V) (hW : V ≤ W) :
    mSet x A W = (Finset.Icc 1 ⌊x / V⌋₊).filter
      (fun m : ℕ => (m % 2 = 1 ∧ max (x / (2 * W)) A < (m : ℝ)) ∧ (m : ℝ) ≤ x / W) := by
  unfold mSet
  exact filter_floor _ (x / W) (x / V) (div_pos hx (by linarith)).le
    (div_le_div_of_nonneg_left hx.le hV hW)

/-- `pS` over a fixed range `[1, ⌊T⌋]` for `0 ≤ W ≤ T`. -/
theorem pS_eq (α V W T : ℝ) (m : ℕ) (hW : 0 ≤ W) (hWT : W ≤ T) :
    pS α (max V (W / 2)) W m = ∑ p ∈ Finset.Icc 1 ⌊T⌋₊,
      if (p.Prime ∧ max V (W / 2) < (p : ℝ)) ∧ (p : ℝ) ≤ W then
        ((Real.log p : ℝ) : ℂ) * e (((m * p : ℕ) : ℝ) * α) else 0 := by
  unfold pS
  rw [filter_floor _ W T hW hWT, Finset.sum_filter]

/-- `‖pS‖ ≤ ∑_{p ≤ T} log p`. -/
theorem pS_norm_le (α V W T : ℝ) (m : ℕ) (hWT : W ≤ T) :
    ‖pS α (max V (W / 2)) W m‖ ≤ ∑ p ∈ Finset.Icc 1 ⌊T⌋₊, Real.log p := by
  unfold pS
  refine (norm_sum_le _ _).trans ?_
  have hn : ∀ p ∈ (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ max V (W / 2) < (p : ℝ)),
      ‖((Real.log p : ℝ) : ℂ) * e (((m * p : ℕ) : ℝ) * α)‖ = Real.log p := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hp1)]
  rw [Finset.sum_congr rfl hn]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
  · intro p hp
    have hp := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_Icc] at hp ⊢
    exact ⟨hp.1, hp.2.trans (Nat.floor_le_floor hWT)⟩
  · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp).1)

/-- **`secI` is integrable on `[V, x/U]`** (it is a step function divided by `W`). -/
theorem secI_ii (x α U V : ℝ) (hx : 0 < x) (hV : 3 ≤ V) (hVU : V ≤ x / U) :
    IntervalIntegrable
      (secI (fun W => s1 x U W) (fun W => s2 x α (max U (x / (2 * W))) (max V (W / 2)) W)
        (fun W => s3 x W)) volume V (x / U) := by
  have hV0 : 0 < V := by linarith
  set N := ⌊x / V⌋₊ with hN
  set T := x / U with hT
  -- the measurable stand-ins
  set pS' : ℝ → ℕ → ℂ := fun W m => ∑ p ∈ Finset.Icc 1 ⌊T⌋₊,
      if (p.Prime ∧ max V (W / 2) < (p : ℝ)) ∧ (p : ℝ) ≤ W then
        ((Real.log p : ℝ) : ℂ) * e (((m * p : ℕ) : ℝ) * α) else 0 with hpS'
  set g1 : ℝ → ℝ := fun W => ∑ m ∈ Finset.Icc 1 N,
      if (m % 2 = 1 ∧ max (x / (2 * W)) U < (m : ℝ)) ∧ (m : ℝ) ≤ x / W then cU U m ^ 2 else 0
    with hg1
  set g2 : ℝ → ℝ := fun W => ∑ m ∈ Finset.Icc 1 N,
      if (m % 2 = 1 ∧ max (x / (2 * W)) U < (m : ℝ)) ∧ (m : ℝ) ≤ x / W then ‖pS' W m‖ ^ 2
        else 0 with hg2
  set g3 : ℝ → ℝ := fun W => ∑ m ∈ Finset.Icc 1 N,
      if (m % 2 = 1 ∧ max (x / (2 * W)) 0 < (m : ℝ)) ∧ (m : ℝ) ≤ x / W then
        (Chebyshev.psi W - Chebyshev.theta W) ^ 2 else 0 with hg3
  set G : ℝ → ℝ := fun W => (Real.sqrt (g1 W * g2 W) + Real.sqrt (g1 W * g3 W)) / W with hG
  -- equality on the interval
  have hmset : ∀ W, mSet x (max U (x / (2 * W))) W = mSet x U W := by
    intro W
    unfold mSet
    have : max (x / (2 * W)) (max U (x / (2 * W))) = max (x / (2 * W)) U := by
      rw [max_comm U, ← max_assoc, max_self]
    rw [this]
  have hEq : ∀ W ∈ Ioc V T, secI (fun W => s1 x U W)
      (fun W => s2 x α (max U (x / (2 * W))) (max V (W / 2)) W) (fun W => s3 x W) W = G W := by
    intro W hW
    have hVW : V ≤ W := hW.1.le
    have hW0 : 0 ≤ W := by linarith
    have e1 : s1 x U W = g1 W := by
      rw [s1, mSet_eq x U V W hx hV0 hVW, Finset.sum_filter]
    have e2 : s2 x α (max U (x / (2 * W))) (max V (W / 2)) W = g2 W := by
      rw [s2, hmset, mSet_eq x U V W hx hV0 hVW, Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [pS_eq α V W T m hW0 hW.2]
    have e3 : s3 x W = g3 W := by
      rw [s3, mSet_eq x 0 V W hx hV0 hVW, Finset.sum_filter]
    simp only [secI, hG]
    rw [e1, e2, e3]
  -- measurability
  have hmp : ∀ m : ℕ, Measurable fun W => pS' W m := by
    intro m
    refine Finset.measurable_sum _ fun p _ => ?_
    exact Measurable.ite (ms_p V p) measurable_const measurable_const
  have hm1 : Measurable g1 :=
    Finset.measurable_sum _ fun m _ => Measurable.ite (ms_m x U m) measurable_const
      measurable_const
  have hm2 : Measurable g2 :=
    Finset.measurable_sum _ fun m _ => Measurable.ite (ms_m x U m)
      (((hmp m).norm).pow_const 2) measurable_const
  have hpsi : Measurable fun W => (Chebyshev.psi W - Chebyshev.theta W) ^ 2 :=
    (Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).pow_const 2
  have hm3 : Measurable g3 :=
    Finset.measurable_sum _ fun m _ => Measurable.ite (ms_m x 0 m) hpsi measurable_const
  have hmG : Measurable G :=
    (((hm1.mul hm2).sqrt).add ((hm1.mul hm3).sqrt)).div measurable_id
  -- the bound on the interval
  set C1 := ∑ m ∈ Finset.Icc 1 N, cU U m ^ 2 with hC1
  set C2 := ∑ _m ∈ Finset.Icc 1 N, (∑ p ∈ Finset.Icc 1 ⌊T⌋₊, Real.log p) ^ 2 with hC2
  set C3 := ∑ _m ∈ Finset.Icc 1 N, Chebyshev.psi T ^ 2 with hC3
  have hbd : ∀ W ∈ Ioc V T, ‖G W‖ ≤ (Real.sqrt (C1 * C2) + Real.sqrt (C1 * C3)) / V := by
    intro W hW
    have hVW : V ≤ W := hW.1.le
    have hW0 : 0 < W := by linarith
    have hsub : mSet x U W ⊆ Finset.Icc 1 N := by
      rw [mSet_eq x U V W hx hV0 hVW]
      exact Finset.filter_subset _ _
    have hsub0 : mSet x 0 W ⊆ Finset.Icc 1 N := by
      rw [mSet_eq x 0 V W hx hV0 hVW]
      exact Finset.filter_subset _ _
    have b1 : s1 x U W ≤ C1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    have b2 : s2 x α (max U (x / (2 * W))) (max V (W / 2)) W ≤ C2 := by
      rw [s2, hmset]
      refine (Finset.sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _)
        (pS_norm_le α V W T m hW.2) 2).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    have b3 : s3 x W ≤ C3 := by
      unfold s3
      have hpt : (Chebyshev.psi W - Chebyshev.theta W) ^ 2 ≤ Chebyshev.psi T ^ 2 := by
        have h0 : 0 ≤ Chebyshev.psi W - Chebyshev.theta W :=
          sub_nonneg.mpr (Chebyshev.theta_le_psi W)
        refine pow_le_pow_left₀ h0 ?_ 2
        have := Chebyshev.theta_nonneg W
        have := Chebyshev.psi_mono hW.2
        linarith
      refine (Finset.sum_le_sum fun _ _ => hpt).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub0 fun _ _ _ => sq_nonneg _
    rw [← hEq W hW]
    have h1 := s1_nonneg x U W
    have h2 := s2_nonneg x α (max U (x / (2 * W))) (max V (W / 2)) W
    have h3 := s3_nonneg x W
    have hnum : Real.sqrt (s1 x U W * s2 x α (max U (x / (2 * W))) (max V (W / 2)) W) +
        Real.sqrt (s1 x U W * s3 x W) ≤ Real.sqrt (C1 * C2) + Real.sqrt (C1 * C3) :=
      add_le_add (Real.sqrt_le_sqrt (mul_le_mul b1 b2 h2 (h1.trans b1)))
        (Real.sqrt_le_sqrt (mul_le_mul b1 b3 h3 (h1.trans b1)))
    have hpos : 0 ≤ Real.sqrt (s1 x U W * s2 x α (max U (x / (2 * W))) (max V (W / 2)) W) +
        Real.sqrt (s1 x U W * s3 x W) := by positivity
    unfold secI
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpos hW0.le)]
    calc _ ≤ (Real.sqrt (C1 * C2) + Real.sqrt (C1 * C3)) / W :=
          div_le_div_of_nonneg_right hnum hW0.le
      _ ≤ _ := div_le_div_of_nonneg_left (hpos.trans hnum) hV0 hVW
  have hint : IntegrableOn G (Ioc V T) volume :=
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmG.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc hbd)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hVU]
  exact hint.congr_fun (fun W hW => (hEq W hW).symm) measurableSet_Ioc

/-! ## (5) `SecInt`, PROVED -/

/-- **`T2S.SecInt`, PROVED** — `eq:bycaus` and Cauchy–Schwarz (`typeII.tex` 59-146). -/
theorem secInt_holds : SecInt := by
  intro x α U V hx hU hV hVU'
  have hV0 : 0 < V := by linarith
  have hVU : V ≤ x / U := by rw [le_div_iff₀ hU]; exact hVU'
  rw [sII_int x α U V hx hU hV0 hVU, norm_mul, Complex.norm_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hGi : IntervalIntegrable (fun W => ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      ∑ n ∈ Finset.Ioc 0 (⌊x⌋₊ / m), bT x α U V m n W) volume V (x / U) := by
    rw [← Finset.sum_fn]
    refine IntervalIntegrable.sum _ fun m hm => ?_
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum _ fun n _ =>
      bT_ii x α U V m n hV0 hVU (Finset.mem_Ioc.mp hm).1
  refine (intervalIntegral.norm_integral_le_integral_norm hVU).trans ?_
  refine intervalIntegral.integral_mono_on_of_le_Ioo hVU hGi.norm
    (secI_ii x α U V hx hV hVU) fun W hW => ?_
  have hW1 : 1 ≤ W := by linarith [hW.1]
  have hW0 : 0 < W := by linarith
  rw [sum_bT x α U V W hx hV0.le hW1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), secI, one_div, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (F_le x α U V W hx hV hW.1.le) (by positivity)

/-- **`MPc.Vinland1At` from the links still open** (`SecInt` discharged). -/
theorem vinland1At_of_rest (hm : Menson2) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) (hv : Vin1Calc) : Vinland1At :=
  vinland1At_of secInt_holds hm hk hc hl h13 hv

/-- **`MPc.EriksagaAt` from the links still open** (`SecInt` discharged). -/
theorem eriksagaAt_of_rest (hm : Menson2) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) (he : ErikCalc) : EriksagaAt :=
  eriksagaAt_of secInt_holds hm hk hc hl h13 he

/-- **`MPc.SecIIAt` from the links still open** (`SecInt` discharged). -/
theorem secIIAt_of_rest (hm : Menson2) (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge)
    (h13 : EB.RS62Thm13) (h2c : SecIICalc) : SecIIAt :=
  secIIAt_of secInt_holds hm hk hc hl h13 h2c

end Principia.Common.TernaryGoldbach.T2S
