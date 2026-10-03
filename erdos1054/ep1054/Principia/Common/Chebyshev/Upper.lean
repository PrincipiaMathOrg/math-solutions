/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Chebyshev.Lower

/-!
# Chebyshev's 1852 upper bound `θ(t) ≤ 1.11 t` for `t ≥ 3·10⁹`

The companion of `Lower.lean`, by the same five-factorial argument read in the other direction.
The shape follows `psi_diff_upper` / `psi_upper` in PrimeNumberTheoremAnd
(`IEANTN/Chebyshev.lean`, Kontorovich–Tao et al.), which is **not imported**: it depends on
LeanCert, and its clean form `psi_upper_clean` rests on a compiled (native-code) evaluation of
`ψ(N) ≤ 1.11 N` for `N ≤ 11723`, which our gate records as blocked. Here the small range is
handled instead by
Mathlib's crude `ψ(x) ≤ (log 4 + 4) x`, paid for by a larger threshold `T₀ = 3·10⁹`.

* **the floor function.** `f(q) = q − ⌊q/2⌋ − ⌊q/3⌋ − ⌊q/5⌋ + ⌊q/30⌋` is `≥ 0` for every `q`
  (`floorComb_nonneg`) and `= 1` on `1 ≤ q ≤ 5` (`floorComb_eq_one`); `omega` checks both.
* **Legendre at a general `n`** (`log_factorial_div_eq_sum`, `chebComb_eq_sum`): with
  `⌊⌊n/k⌋/d⌋ = ⌊⌊n/d⌋/k⌋`, the combination
  `chebComb n = log n! − log ⌊n/2⌋! − log ⌊n/3⌋! − log ⌊n/5⌋! + log ⌊n/30⌋!` equals
  `∑_{d ≤ n} Λ(d) f(⌊n/d⌋)`. Every term is `≥ 0` and the terms with `n/6 < d ≤ n` are exactly
  `Λ(d)`, so `ψ(n) − ψ(⌊n/6⌋) ≤ chebComb n` (`psi_sub_psi_div_six_le`).
* **Stirling with floors** (`chebComb_le`): for `n ≥ 90`, `chebComb n ≤ A n + 4 log n + 2`, with
  `A = chebyshevA`. Upper Stirling (`log_factorial_le`) on `n!` and `⌊n/30⌋!`, pushed up to
  `Y = n/30` by monotonicity of `y log y − y` (`log_factorial_le_of_le`); Mathlib's lower Stirling
  on `⌊n/k⌋!`, `k = 2, 3, 5`, pushed down to `y = n/k` by the tangent line of `log`
  (`log_factorial_ge_of_ge`: `m log m − m ≥ m log y − y ≥ y log y − y − log y`).
* **The constant** (`chebyshevA_le_log_two`): `A ≤ (4/3) log 2`, from `2¹⁴ 3⁹ 5⁵ ≤ 2⁴⁰`; so
  `(6/5) A ≤ (8/5) log 2 < 1.10904`.
* **The induction** (`psi_nat_le`): `ψ(n) ≤ 1.1096 n + 1150000` for every `n`, by strong induction.
  Below `2¹⁸` the crude bound gives it (`(5.3863 − 1.1096)·2¹⁸ = 1121099 < 1150000`); above, the
  step needs `4 log n + 2 ≤ (5·1.1096/6 − A) n`, i.e. `47.91 ≤ 0.000455 n` (margin `71.4` at `2¹⁸`,
  using `log n ≤ 18 log 2 + n/2¹⁸ − 1`).
* **The result** (`psi_le_cheb`, `theta_le_cheb`): `ψ(t), θ(t) ≤ 1.11 t` for `t ≥ 3·10⁹`, since
  `1150000 ≤ 0.0004 · 3·10⁹ = 1200000`.

Constants priced exactly (rationals) in the session scratchpad `kref/upper_price.py`.
Nothing here mentions a campaign: it is the classical theorem, with explicit constants.
-/

set_option autoImplicit false

open Real Finset Chebyshev
open ArithmeticFunction hiding log
open scoped Nat

namespace Principia.Common.Chebyshev

/-! ## 1. The floor function -/

/-- **Chebyshev's floor function is nonnegative**: `⌊q/2⌋ + ⌊q/3⌋ + ⌊q/5⌋ ≤ q + ⌊q/30⌋`
(the lower half of `0 ≤ f(q) ≤ 1`; `f` has period `30`, `omega` checks it). -/
theorem floorComb_nonneg (q : ℕ) : q / 2 + q / 3 + q / 5 ≤ q + q / 30 := by
  omega

/-- **`f(q) = 1` on `1 ≤ q ≤ 5`**: `q + ⌊q/30⌋ = ⌊q/2⌋ + ⌊q/3⌋ + ⌊q/5⌋ + 1`. -/
theorem floorComb_eq_one (q : ℕ) (h1 : 1 ≤ q) (h5 : q ≤ 5) :
    q + q / 30 = q / 2 + q / 3 + q / 5 + 1 := by
  omega

/-! ## 2. Legendre at a general `n` -/

/-- **Chebyshev's factorial combination at a general `n`** (floors):
`log n! − log ⌊n/2⌋! − log ⌊n/3⌋! − log ⌊n/5⌋! + log ⌊n/30⌋!`. -/
noncomputable def chebComb (n : ℕ) : ℝ :=
  Real.log (n ! : ℝ) - Real.log ((n / 2) ! : ℝ) - Real.log ((n / 3) ! : ℝ)
    - Real.log ((n / 5) ! : ℝ) + Real.log ((n / 30) ! : ℝ)

/-- The `d`-th term of `chebComb n` as a von Mangoldt sum: `Λ(d) f(⌊n/d⌋)`. -/
noncomputable def chebTerm (n d : ℕ) : ℝ :=
  Λ d * (((n / d : ℕ) : ℝ) - ((n / d / 2 : ℕ) : ℝ) - ((n / d / 3 : ℕ) : ℝ)
    - ((n / d / 5 : ℕ) : ℝ) + ((n / d / 30 : ℕ) : ℝ))

/-- **Legendre for `⌊n/k⌋!`**: `log ⌊n/k⌋! = ∑_{0<d≤n} Λ(d) ⌊⌊n/d⌋/k⌋`
(using `⌊⌊n/k⌋/d⌋ = ⌊n/(kd)⌋ = ⌊⌊n/d⌋/k⌋`). -/
theorem log_factorial_div_eq_sum (n k : ℕ) :
    Real.log ((n / k) ! : ℝ) = ∑ d ∈ Ioc 0 n, Λ d * ((n / d / k : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_of_le (n / k) n (Nat.div_le_self _ _)]
  refine sum_congr rfl fun d _ => ?_
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]

/-- **The combination as one sum**: `chebComb n = ∑_{0<d≤n} Λ(d) f(⌊n/d⌋)`. -/
theorem chebComb_eq_sum (n : ℕ) : chebComb n = ∑ d ∈ Ioc 0 n, chebTerm n d := by
  rw [chebComb, log_factorial_eq_sum n, log_factorial_div_eq_sum n 2,
    log_factorial_div_eq_sum n 3, log_factorial_div_eq_sum n 5, log_factorial_div_eq_sum n 30,
    ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  unfold chebTerm
  ring

/-- Every term is nonnegative (`f ≥ 0`, `Λ ≥ 0`). -/
theorem chebTerm_nonneg (n d : ℕ) : 0 ≤ chebTerm n d := by
  have key := floorComb_nonneg (n / d)
  have keyR : ((n / d / 2 : ℕ) : ℝ) + ((n / d / 3 : ℕ) : ℝ) + ((n / d / 5 : ℕ) : ℝ)
      ≤ ((n / d : ℕ) : ℝ) + ((n / d / 30 : ℕ) : ℝ) := by
    exact_mod_cast key
  unfold chebTerm
  exact mul_nonneg vonMangoldt_nonneg (by linarith)

/-- For `n/6 < d ≤ n` one has `1 ≤ ⌊n/d⌋ ≤ 5`, so the term is exactly `Λ(d)`. -/
theorem chebTerm_eq (n d : ℕ) (hd : n / 6 < d) (hdn : d ≤ n) : chebTerm n d = Λ d := by
  have hd0 : 0 < d := by omega
  have hq1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
  have hq5 : n / d ≤ 5 := by
    by_contra h
    have h6 : 6 ≤ n / d := by omega
    have := (Nat.le_div_iff_mul_le hd0).mp h6
    omega
  have key := floorComb_eq_one (n / d) hq1 hq5
  have keyR : ((n / d : ℕ) : ℝ) + ((n / d / 30 : ℕ) : ℝ) = ((n / d / 2 : ℕ) : ℝ)
      + ((n / d / 3 : ℕ) : ℝ) + ((n / d / 5 : ℕ) : ℝ) + 1 := by
    exact_mod_cast key
  have hs : ((n / d : ℕ) : ℝ) - ((n / d / 2 : ℕ) : ℝ) - ((n / d / 3 : ℕ) : ℝ)
      - ((n / d / 5 : ℕ) : ℝ) + ((n / d / 30 : ℕ) : ℝ) = 1 := by linarith
  unfold chebTerm
  rw [hs, mul_one]

/-- **Chebyshev's upper inequality at a general `n`**: `ψ(n) − ψ(⌊n/6⌋) ≤ chebComb n`. -/
theorem psi_sub_psi_div_six_le (n : ℕ) :
    ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) ≤ chebComb n := by
  have h6 : n / 6 ≤ n := Nat.div_le_self n 6
  have hpsi : ψ (n : ℝ) = ψ ((n / 6 : ℕ) : ℝ) + ∑ d ∈ Ioc (n / 6) n, Λ d := by
    rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast]
    exact (sum_Ioc_consecutive _ (Nat.zero_le _) h6).symm
  have hcomb : chebComb n = ∑ d ∈ Ioc 0 (n / 6), chebTerm n d
      + ∑ d ∈ Ioc (n / 6) n, chebTerm n d := by
    rw [chebComb_eq_sum]
    exact (sum_Ioc_consecutive _ (Nat.zero_le _) h6).symm
  have h0 : 0 ≤ ∑ d ∈ Ioc 0 (n / 6), chebTerm n d :=
    sum_nonneg fun d _ => chebTerm_nonneg n d
  have h1 : ∑ d ∈ Ioc (n / 6) n, Λ d ≤ ∑ d ∈ Ioc (n / 6) n, chebTerm n d :=
    sum_le_sum fun d hd => (chebTerm_eq n d (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2).ge
  linarith

/-! ## 3. Stirling with floors -/

/-- `⌊n/k⌋ ≥ n/k − 1`. -/
theorem natDiv_ge_sub_one (n k : ℕ) : (n : ℝ) / k - 1 ≤ ((n / k : ℕ) : ℝ) := by
  have h := Nat.lt_floor_add_one ((n : ℝ) / k)
  rw [Nat.floor_div_eq_div] at h
  linarith

/-- **Lower Stirling, pushed down to a real point**: for `m ≥ 1`, `y ≥ 1` and `y − 1 ≤ m`,
`y log y − y − log y ≤ log m!` (tangent line of `log` at `m`: `m log y − m log m ≤ y − m`). -/
theorem log_factorial_ge_of_ge (m : ℕ) (y : ℝ) (hm : m ≠ 0) (hy : 1 ≤ y) (hmy : y - 1 ≤ m) :
    y * Real.log y - y - Real.log y ≤ Real.log (m ! : ℝ) := by
  have hst := Stirling.le_log_factorial_stirling hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have h2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [pi_gt_three])
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hconv : Real.log (y / m) ≤ y / m - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hm0)
  rw [Real.log_div hy0.ne' hm0.ne'] at hconv
  have hc1 := mul_le_mul_of_nonneg_right hconv hm0.le
  have he : (y / m - 1) * (m : ℝ) = y - m := by
    rw [sub_mul, div_mul_cancel₀ y hm0.ne', one_mul]
  have hc3 : (y - 1) * Real.log y ≤ m * Real.log y := mul_le_mul_of_nonneg_right hmy hlogy
  linarith

/-- **Upper Stirling, pushed up to a real point**: for `1 ≤ m ≤ Y` and `Y ≥ 3`,
`log m! ≤ Y log Y − Y + (log Y)/2 + 1` (`y log y − y` increases once `log y ≥ 1`). -/
theorem log_factorial_le_of_le (m : ℕ) (Y : ℝ) (hm : m ≠ 0) (hmY : (m : ℝ) ≤ Y) (hY : 3 ≤ Y) :
    Real.log (m ! : ℝ) ≤ Y * Real.log Y - Y + Real.log Y / 2 + 1 := by
  have hup := log_factorial_le m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hlog : Real.log m ≤ Real.log Y := Real.log_le_log hm0 hmY
  have hlogY : 1 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Y by linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h
  have h1 : (m : ℝ) * Real.log m ≤ m * Real.log Y := mul_le_mul_of_nonneg_left hlog hm0.le
  have h2 : (m : ℝ) * (Real.log Y - 1) ≤ Y * (Real.log Y - 1) :=
    mul_le_mul_of_nonneg_right hmY (by linarith)
  linarith

/-- **The combination from above (Stirling)**: for `n ≥ 90`,
`chebComb n ≤ A n + 4 log n + 2`. -/
theorem chebComb_le (n : ℕ) (hn : 90 ≤ n) :
    chebComb n ≤ chebyshevA * n + 4 * Real.log n + 2 := by
  have hnR : (90 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlow : ∀ k : ℕ, 0 < k → k ≤ 5 →
      (n : ℝ) / k * Real.log ((n : ℝ) / k) - (n : ℝ) / k - Real.log ((n : ℝ) / k) ≤
        Real.log ((n / k) ! : ℝ) := by
    intro k hk hk5
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hk5R : (k : ℝ) ≤ 5 := by exact_mod_cast hk5
    refine log_factorial_ge_of_ge (n / k) ((n : ℝ) / k) (Nat.div_pos (by omega) hk).ne' ?_
      (natDiv_ge_sub_one n k)
    rw [le_div_iff₀ hkR]
    linarith
  have h2 := hlow 2 (by norm_num) (by norm_num)
  have h3 := hlow 3 (by norm_num) (by norm_num)
  have h5 := hlow 5 (by norm_num) (by norm_num)
  push_cast at h2 h3 h5
  have h30 := log_factorial_le_of_le (n / 30) ((n : ℝ) / 30)
    (Nat.div_pos (by omega) (by norm_num)).ne'
    (by rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 30)
    (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hN := log_factorial_le n (by omega)
  have l30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [Real.log_div hn0.ne' (by norm_num)] at h2 h3 h5 h30
  rw [l30] at h30
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  unfold chebComb
  rw [chebyshevA_eq]
  linarith

/-! ## 4. The constant -/

/-- **`A ≤ (4/3) log 2`**, from `2¹⁴ 3⁹ 5⁵ = 1007769600000 ≤ 2⁴⁰ = 1099511627776`. -/
theorem chebyshevA_le_log_two : chebyshevA ≤ 4 / 3 * Real.log 2 := by
  have h : Real.log ((2 : ℝ) ^ 14 * 3 ^ 9 * 5 ^ 5) ≤ Real.log ((2 : ℝ) ^ 40) :=
    Real.log_le_log (by positivity) (by norm_num)
  have hK : Real.log ((2 : ℝ) ^ 14 * 3 ^ 9 * 5 ^ 5) = 30 * chebyshevA := by
    rw [chebyshevA]; ring
  rw [hK, Real.log_pow] at h
  push_cast at h
  linarith

/-! ## 5. The induction and the result -/

/-- **Chebyshev's upper bound at integers, with an additive constant**:
`ψ(n) ≤ 1.1096 n + 1150000` for every `n`. Strong induction: below `2¹⁸ = 262144` Mathlib's
`ψ(x) ≤ (log 4 + 4) x` suffices; above, `ψ(n) ≤ ψ(⌊n/6⌋) + A n + 4 log n + 2`. -/
theorem psi_nat_le (n : ℕ) : ψ (n : ℝ) ≤ 1.1096 * n + 1150000 := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl2 := Real.log_two_lt_d9
  rcases lt_or_ge n 262144 with hn | hn
  · have hbase := psi_le_const_mul_self hn0
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hnR : (n : ℝ) ≤ 262144 := by exact_mod_cast hn.le
    have hc : (Real.log 4 + 4) * n ≤ 5.3863 * n :=
      mul_le_mul_of_nonneg_right (by linarith) hn0
    linarith
  · have hnR : (262144 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiff := psi_sub_psi_div_six_le n
    have hcomb := chebComb_le n (by omega)
    have hih := ih (n / 6) (Nat.div_lt_self (by omega) (by norm_num))
    have hcast : 6 * ((n / 6 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n 6
    have hA : chebyshevA * n ≤ 4 / 3 * 0.6931471808 * n :=
      mul_le_mul_of_nonneg_right (by linarith [chebyshevA_le_log_two]) hn0
    have hlog : Real.log n ≤ 18 * Real.log 2 + n / 262144 - 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos (by linarith) (by norm_num) :
        (0 : ℝ) < n / 262144)
      rw [Real.log_div (by linarith) (by norm_num),
        show (262144 : ℝ) = 2 ^ 18 by norm_num, Real.log_pow] at h
      push_cast at h
      linarith
    linarith

/-- **Chebyshev's upper bound (1852)**: `ψ(t) ≤ 1.11 t` for real `t ≥ 3·10⁹`. -/
theorem psi_le_cheb {t : ℝ} (ht : 3 * 10 ^ 9 ≤ t) : ψ t ≤ 1.11 * t := by
  have ht0 : 0 ≤ t := by linarith
  have h := psi_nat_le ⌊t⌋₊
  have hf := Nat.floor_le ht0
  rw [psi_eq_psi_coe_floor]
  linarith

/-- **Chebyshev's upper bound for `θ`**: `θ(t) ≤ 1.11 t` for every real `t ≥ 3·10⁹`. -/
theorem theta_le_cheb : ∀ t : ℝ, 3 * 10 ^ 9 ≤ t → θ t ≤ 1.11 * t := fun t ht =>
  (theta_le_psi t).trans (psi_le_cheb ht)

end Principia.Common.Chebyshev
