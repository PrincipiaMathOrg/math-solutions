/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

/-!
# EP1054 §4.2 "Where are the small ratios?": the `SmallRatio` package of the spine

Discharges the seven obligations of `Principia.Erdos1054.Spine` for EP1054.tex lines 1150–1195
(`Campaigns/Erdos-1054/collab-paper/EP1054.tex`).

Leaves (proved from the definitions and Mathlib alone):
* `leaf_SmallRatio_prefixLeSig` (line 1161) — a divisor-prefix sum of `m` is at most `σ(m)`.
* `leaf_SmallRatio_abundancySmall` (lines 1166–1171) — `σ(m)/m = ∑_{d∣m} 1/d ≤ H_m ≤ 1 + log 5040
  < 10` for `1 ≤ m ≤ 5040` (Mathlib `harmonic_le_one_add_log`; `log 5040 < 9` from
  `Real.exp_one_gt_d9`).
* `leaf_SmallRatio_axlerNumeric` (lines 1172–1178) — `(1 + 3.15367·10⁻⁷) e^γ log log 10^{119} ≤
  9.99745` (true value `9.9974403…`, margin `9.6·10⁻⁶`). Certified bounds used:
  - `γ ≤ 0.5772158` (`gamma_le`): Mathlib only has `γ < H_n − log n` (error `≈ 1/(2n)`), far too
    weak. We prove that `c_k = H_k − log k − 1/(2k) + 1/(12k²)` is non-increasing for `k ≥ 1`
    (`cSeq_succ_le`: the step reduces, via three terms of Mathlib's `Real.hasSum_log_one_add_inv`,
    to the positivity of `(64k⁴+128k³+94k²+30k+5)/(60k²(k+1)²(2k+1)⁵)`, `step_poly`) and tends to
    `γ`, so `γ ≤ c_20`; `H_20 = 55835135/15519504` exactly and `log 20` from below via `log 2 >
    0.6931471803` and the series of `log (5/4)`.
  - `e^γ ≤ 1.7810727` (`exp_gamma_le`, Taylor bound `Real.exp_bound'` with 12 terms).
  - `log log 10^{119} ≤ 5.6131563` (`loglog_le`, via `log 10 ≤ 2.302585095` and
    `119 · 2.302585095 ≤ 2^8/(1 − 0.0657195)`, the series of `−log(1 − x)` with its tail bound).
* `leaf_Rem_Lcm289Abundant` (lines 1183–1187) and `leaf_Rem_Lcm289Values` (lines 1187–1194) — exact
  arithmetic: `lcm(1..289) = ∏ p^a` over the 61 prime powers (`lcmUpTo_289`, kernel `decide`),
  `σ` of that product is `∏ (p^{a+1}−1)/(p−1)` (`sig_prodPow`, multiplicativity), both evaluated
  to explicit literals (`prodPow_pp289`, `sigList_pp289`); all printed digits then follow by
  `norm_num`. Every printed value was also re-checked: `σ(m)/m = 10.0047357412…`,
  `σ(m) = 3.0781522093…·10^{128}`, `m/σ(m) = 0.0999526650042…`.

Links (proved from exactly the dependencies the spine names):
* `link_Prop_SmallRatioThreshold` (lines 1156–1181) — from `SmallRatio_prefixLeSig`,
  `SmallRatio_abundancySmall`, `SmallRatio_axlerNumeric` and the cited input `Cite_Axler_Cor2`.
* `link_Rem_Lcm289Witness` (lines 1189–1195) — from `Rem_Lcm289Abundant` (`σ(m) = F_1(m)` gives
  `σ(m) ∈ 𝓡` and `f(σ(m)) ≤ m`).
-/

namespace Principia.Erdos1054.Proofs.SmallRatio

open Finset Filter
open scoped Topology

/-! ## Elementary facts about `σ` -/

/-- `σ(n) = F_1(n)`: every divisor of `1 · n` is `≤ n`. -/
theorem sig_eq_F_one (n : ℕ) : sig n = F 1 n := by
  show ArithmeticFunction.sigma 1 n = F 1 n
  rw [ArithmeticFunction.sigma_one_apply, F, one_mul, Finset.filter_true_of_mem]
  intro d hd
  exact Nat.divisor_le hd

/-- `σ(m)/m = ∑_{d ∣ m} 1/d` for `m ≥ 1`. -/
theorem abundancy_eq_sum (m : ℕ) (hm : 1 ≤ m) :
    abundancy m = ∑ d ∈ m.divisors, (1 : ℝ) / d := by
  have hsig : (sig m : ℝ) = ∑ d ∈ m.divisors, (m : ℝ) / d := by
    show ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) = _
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors m (fun d => d), Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact Nat.cast_div (Nat.dvd_of_mem_divisors hd)
      (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [abundancy, hsig, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  field_simp

/-- `log 5040 < 9`, from `e > 2.7182818283`. -/
theorem log_5040_lt : Real.log 5040 < 9 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h9]
  calc (5040 : ℝ) < 2.7182818283 ^ 9 := by norm_num
    _ < Real.exp 1 ^ 9 := by gcongr

/-! ## Certified numerics for `SmallRatio_axlerNumeric` -/

/-- Two-sided bound from the Taylor series of `-log(1 - x)`, `0 ≤ x < 1`. -/
theorem log_series_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ -Real.log (1 - x) ∧
      -Real.log (1 - x) ≤ (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg h0]
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have h' := abs_le.1 h
  constructor <;> linarith [h'.1, h'.2]

/-- The polynomial inequality behind the monotonicity of `H_k − log k − 1/(2k) + 1/(12k²)`:
the difference of the two sides is `(64y⁴+128y³+94y²+30y+5)/(60y²(y+1)²(2y+1)⁵) ≥ 0`. -/
theorem step_poly (y : ℝ) (hy : 0 < y) :
    1 / (2 * y) - 1 / (12 * y ^ 2) - (1 / (2 * (y + 1)) - 1 / (12 * (y + 1) ^ 2)) + (y + 1)⁻¹ ≤
      ∑ i ∈ Finset.range 3, (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * (1 / (2 * y + 1)) ^ (2 * i + 1) := by
  have hy0 : y ≠ 0 := hy.ne'
  have hy1 : y + 1 ≠ 0 := by positivity
  have hy2 : 2 * y + 1 ≠ 0 := by positivity
  have e : (∑ i ∈ Finset.range 3, (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * (1 / (2 * y + 1)) ^ (2 * i + 1))
      - (1 / (2 * y) - 1 / (12 * y ^ 2) - (1 / (2 * (y + 1)) - 1 / (12 * (y + 1) ^ 2)) + (y + 1)⁻¹)
      = (64 * y ^ 4 + 128 * y ^ 3 + 94 * y ^ 2 + 30 * y + 5) /
          (60 * y ^ 2 * (y + 1) ^ 2 * (2 * y + 1) ^ 5) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd]
    field_simp
    ring
  have hpos : 0 ≤ (64 * y ^ 4 + 128 * y ^ 3 + 94 * y ^ 2 + 30 * y + 5) /
      (60 * y ^ 2 * (y + 1) ^ 2 * (2 * y + 1) ^ 5) := by positivity
  linarith

/-- `c_k = H_k − log k − (1/(2k) − 1/(12k²))`. -/
noncomputable def cSeq (k : ℕ) : ℝ :=
  Real.eulerMascheroniSeq' k - (1 / (2 * (k : ℝ)) - 1 / (12 * (k : ℝ) ^ 2))

/-- `c_{k+1} ≤ c_k` for `k ≥ 1`. -/
theorem cSeq_succ_le (k : ℕ) (hk : 1 ≤ k) : cSeq (k + 1) ≤ cSeq k := by
  have hk0 : k ≠ 0 := by omega
  have hy : (0 : ℝ) < k := by exact_mod_cast hk
  unfold cSeq Real.eulerMascheroniSeq'
  rw [if_neg (show k + 1 ≠ 0 by omega), if_neg hk0, harmonic_succ]
  push_cast
  have hlog : Real.log ((k : ℝ) + 1) = Real.log k + Real.log (1 + (k : ℝ)⁻¹) := by
    rw [← Real.log_mul hy.ne' (by positivity)]
    congr 1
    field_simp
  have hS := sum_le_hasSum (Finset.range 3) (fun i _ => by positivity)
    (Real.hasSum_log_one_add_inv hy)
  have hP := step_poly (k : ℝ) hy
  rw [hlog]
  linarith

theorem tendsto_phi :
    Tendsto (fun x : ℝ => 1 / (2 * x) - 1 / (12 * x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (1 / 2) * x⁻¹ - (1 / 12) * (x⁻¹) ^ 2) atTop
      (𝓝 ((1 / 2) * 0 - (1 / 12) * 0 ^ 2)) :=
    (tendsto_inv_atTop_zero.const_mul _).sub ((tendsto_inv_atTop_zero.pow 2).const_mul _)
  have hfun : (fun x : ℝ => 1 / (2 * x) - 1 / (12 * x ^ 2)) =
      (fun x : ℝ => (1 / 2) * x⁻¹ - (1 / 12) * (x⁻¹) ^ 2) := by
    funext x
    ring
  rw [hfun]
  have h0 : (1 / 2 : ℝ) * 0 - (1 / 12) * 0 ^ 2 = 0 := by norm_num
  rw [h0] at h
  exact h

/-- `γ ≤ c_k` for every `k ≥ 1` (`c` is non-increasing from `k` on and tends to `γ`). -/
theorem gamma_le_cSeq (k : ℕ) (hk : 1 ≤ k) : eulerGamma ≤ cSeq k := by
  have hanti : Antitone (fun j : ℕ => cSeq (j + k)) := by
    refine antitone_nat_of_succ_le (fun j => ?_)
    have h := cSeq_succ_le (j + k) (by omega)
    rwa [show j + k + 1 = j + 1 + k by omega] at h
  have htend : Tendsto (fun j : ℕ => cSeq (j + k)) atTop (𝓝 eulerGamma) := by
    have h1 : Tendsto (fun j : ℕ => Real.eulerMascheroniSeq' (j + k)) atTop
        (𝓝 Real.eulerMascheroniConstant) :=
      Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat k)
    have h2 : Tendsto (fun j : ℕ => 1 / (2 * ((j + k : ℕ) : ℝ)) - 1 / (12 * ((j + k : ℕ) : ℝ) ^ 2))
        atTop (𝓝 0) :=
      tendsto_phi.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k))
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3
  have h := hanti.le_of_tendsto htend 0
  simpa using h

/-- `log 20 > 2.99573227` (from `log 2 > 0.6931471803` and the series for `log (5/4)`). -/
theorem log_twenty_gt : (2.99573227 : ℝ) < Real.log 20 := by
  have hb := (log_series_bounds (x := 1 / 5) (by norm_num) (by norm_num) 12).1
  have h20 : Real.log 20 = 4 * Real.log 2 - Real.log (1 - 1 / 5) := by
    rw [show (20 : ℝ) = 2 ^ 4 / (1 - 1 / 5) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h2 := Real.log_two_gt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h20]
  norm_num at h2 ⊢
  linarith

theorem harmonic_twenty : harmonic 20 = 55835135 / 15519504 := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `γ ≤ 0.5772158` (true value `0.5772156649…`). -/
theorem gamma_le : eulerGamma ≤ 0.5772158 := by
  have h := gamma_le_cSeq 20 (by norm_num)
  have hc : cSeq 20 = (55835135 / 15519504 : ℝ) - Real.log 20 - (1 / 40 - 1 / 4800) := by
    unfold cSeq Real.eulerMascheroniSeq'
    rw [if_neg (show (20 : ℕ) ≠ 0 by norm_num), harmonic_twenty]
    norm_num
  have hl := log_twenty_gt
  rw [hc] at h
  norm_num at h hl ⊢
  linarith

/-- `e^γ ≤ 1.7810727` (true value `1.7810724179…`). -/
theorem exp_gamma_le : Real.exp eulerGamma ≤ 1.7810727 := by
  have h1 : Real.exp eulerGamma ≤ Real.exp 0.5772158 := Real.exp_le_exp.2 gamma_le
  have h2 := Real.exp_bound' (x := 0.5772158) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero] at h2
  norm_num at h2
  linarith

/-- `log 10 ≤ 2.302585095`. -/
theorem log_ten_le : Real.log 10 ≤ 2.302585095 := by
  have hb := (log_series_bounds (x := 1 / 5) (by norm_num) (by norm_num) 12).2
  have h10 : Real.log 10 = 3 * Real.log 2 - Real.log (1 - 1 / 5) := by
    rw [show (10 : ℝ) = 2 ^ 3 / (1 - 1 / 5) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h2 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h10]
  norm_num at h2 ⊢
  linarith

theorem log_pow119_eq : Real.log ((10 : ℝ) ^ 119) = 119 * Real.log 10 := by
  rw [Real.log_pow]
  push_cast
  ring

theorem one_le_log_pow119 : 1 ≤ Real.log ((10 : ℝ) ^ 119) := by
  rw [log_pow119_eq]
  have h2 := Real.log_two_gt_d9
  have h : Real.log 2 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
  norm_num at h2
  linarith

/-- `log log 10^{119} ≤ 5.6131563` (true value `5.6131559383…`). -/
theorem loglog_le : Real.log (Real.log ((10 : ℝ) ^ 119)) ≤ 5.6131563 := by
  have hpos : 0 < Real.log ((10 : ℝ) ^ 119) := lt_of_lt_of_le one_pos one_le_log_pow119
  have hY : Real.log ((10 : ℝ) ^ 119) ≤ 2 ^ 8 / (1 - 0.0657195) := by
    rw [log_pow119_eq]
    have := log_ten_le
    norm_num at this ⊢
    linarith
  have h1 := Real.log_le_log hpos hY
  have hsplit : Real.log (2 ^ 8 / (1 - 0.0657195) : ℝ) =
      8 * Real.log 2 - Real.log (1 - 0.0657195) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hb := (log_series_bounds (x := 0.0657195) (by norm_num) (by norm_num) 8).2
  have h2 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [hsplit] at h1
  norm_num at h1 h2 ⊢
  linarith

theorem loglog_nonneg : 0 ≤ Real.log (Real.log ((10 : ℝ) ^ 119)) :=
  Real.log_nonneg one_le_log_pow119

/-! ## Exact arithmetic for `m = lcm(1, …, 289)` -/

/-- The exponent pairs `(p, a)`, `p^a ∥ lcm(1, …, 289)`, for the 61 primes `p ≤ 289`. -/
def pp289 : List (ℕ × ℕ) :=
  [(2, 8), (3, 5), (5, 3), (7, 2), (11, 2), (13, 2), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1),
   (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1),
   (79, 1), (83, 1), (89, 1), (97, 1), (101, 1), (103, 1), (107, 1), (109, 1), (113, 1), (127, 1),
   (131, 1), (137, 1), (139, 1), (149, 1), (151, 1), (157, 1), (163, 1), (167, 1), (173, 1),
   (179, 1), (181, 1), (191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (227, 1),
   (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1),
   (277, 1), (281, 1), (283, 1)]

/-- `∏ p^a` over a list of pairs, by explicit recursion (kernel-reducible). -/
def prodPow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, a) :: t => p ^ a * prodPow t

/-- `∏ (p^(a+1) − 1)/(p − 1)` over a list of pairs, by explicit recursion. -/
def sigList : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, a) :: t => (p ^ (a + 1) - 1) / (p - 1) * sigList t

/-- Each head prime is coprime to the product of the later prime powers. -/
def copCheck : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, _) :: t => Nat.gcd p (prodPow t) == 1 && copCheck t

/-- For a list of primes, each coprime to the later part of the product, `σ` of the product is the
product of the geometric sums. -/
theorem sig_prodPow : ∀ l : List (ℕ × ℕ), (∀ x ∈ l, x.1.Prime) → copCheck l = true →
    sig (prodPow l) = sigList l
  | [], _, _ => by
    show ArithmeticFunction.sigma 1 1 = 1
    exact ArithmeticFunction.isMultiplicative_sigma.map_one
  | (p, a) :: t, hpr, hc => by
    simp only [copCheck, Bool.and_eq_true, beq_iff_eq] at hc
    have hp : p.Prime := hpr (p, a) List.mem_cons_self
    have ht : ∀ x ∈ t, x.1.Prime := fun x hx => hpr x (List.mem_cons_of_mem _ hx)
    have hcop : Nat.Coprime (p ^ a) (prodPow t) := Nat.Coprime.pow_left a hc.1
    rw [prodPow, sigList, ← sig_prodPow t ht hc.2]
    show ArithmeticFunction.sigma 1 (p ^ a * prodPow t) =
      (p ^ (a + 1) - 1) / (p - 1) * ArithmeticFunction.sigma 1 (prodPow t)
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]

theorem pp289_prime : ∀ x ∈ pp289, x.1.Prime := by
  decide +kernel

theorem pp289_cop : copCheck pp289 = true := by
  decide +kernel

theorem lcmUpTo_289 : lcmUpTo 289 = prodPow pp289 := by
  unfold lcmUpTo
  rw [Nat.floor_ofNat]
  decide +kernel

theorem prodPow_pp289 : prodPow pp289 =
    30766951661432036257097520730189002884501808457271349280434541477083049998681312421410763147264896264746435967273501721768608000 := by
  decide +kernel

theorem sigList_pp289 : sigList pp289 =
    307815220936162118454973147712163805237498756339865693900251555426121382540469258995639128352186473043660399181824000000000000000 := by
  decide +kernel

/-- `lcm(1, …, 289)` as an explicit literal. -/
theorem lcm289_eq : lcmUpTo 289 =
    30766951661432036257097520730189002884501808457271349280434541477083049998681312421410763147264896264746435967273501721768608000 := by
  rw [lcmUpTo_289, prodPow_pp289]

/-- `σ(lcm(1, …, 289))` as an explicit literal. -/
theorem sig_lcm289 : sig (lcmUpTo 289) =
    307815220936162118454973147712163805237498756339865693900251555426121382540469258995639128352186473043660399181824000000000000000 := by
  rw [lcmUpTo_289, sig_prodPow _ pp289_prime pp289_cop, sigList_pp289]

end Principia.Erdos1054.Proofs.SmallRatio

namespace Principia.Erdos1054.Proofs

open Finset Principia.Erdos1054.Proofs.SmallRatio

/-- EP1054.tex line 1161: every divisor-prefix sum of `m` is at most `σ(m)`. -/
theorem leaf_SmallRatio_prefixLeSig : Principia.Erdos1054.SmallRatio_prefixLeSig := by
  intro N m hrep
  rw [isRep_iff_exists_divisor] at hrep
  obtain ⟨d, hd, hN⟩ := hrep
  rw [hN, F, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  show _ ≤ ArithmeticFunction.sigma 1 m
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- EP1054.tex lines 1166–1171: `σ(m)/m ≤ H_m ≤ 1 + log 5040 < 10` for `1 ≤ m ≤ 5040`. -/
theorem leaf_SmallRatio_abundancySmall : Principia.Erdos1054.SmallRatio_abundancySmall := by
  intro m hm1 hm2
  rw [abundancy_eq_sum m hm1]
  have hsub : m.divisors ⊆ Finset.Icc 1 m := by
    intro d hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  have h1 : ∑ d ∈ m.divisors, (1 : ℝ) / d ≤ ∑ d ∈ Finset.Icc 1 m, (1 : ℝ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h2 : ∑ d ∈ Finset.Icc 1 m, (1 : ℝ) / d = (harmonic m : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  have h3 := harmonic_le_one_add_log m
  have h4 : Real.log m ≤ Real.log 5040 :=
    Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hm2)
  have h5 := log_5040_lt
  linarith

/-- EP1054.tex lines 1172–1178, the numeric half:
`(1 + 3.15367·10⁻⁷) e^γ log log 10^{119} ≤ 9.99745`. -/
theorem leaf_SmallRatio_axlerNumeric : Principia.Erdos1054.SmallRatio_axlerNumeric := by
  show (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log ((10 : ℝ) ^ 119)) ≤ 9.99745
  have hE := exp_gamma_le
  have hL := loglog_le
  have hL0 := loglog_nonneg
  have hc : (0 : ℝ) ≤ 1 + 3.15367e-7 := by norm_num
  have h1 : (1 + 3.15367e-7) * Real.exp eulerGamma ≤ (1 + 3.15367e-7) * 1.7810727 :=
    mul_le_mul_of_nonneg_left hE hc
  have h2 : (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log ((10 : ℝ) ^ 119)) ≤
      (1 + 3.15367e-7) * 1.7810727 * 5.6131563 :=
    mul_le_mul h1 hL hL0 (by norm_num)
  have h3 : (1 + 3.15367e-7) * (1.7810727 : ℝ) * 5.6131563 ≤ 9.99745 := by norm_num
  linarith

/-- EP1054.tex lines 1156–1181: `n ∈ 𝓡`, `f(n) ≤ n/10` ⟹ `n > 10^{120}`. -/
theorem link_Prop_SmallRatioThreshold :
    Principia.Erdos1054.Spine.Link_Prop_SmallRatioThreshold := by
  intro hPre hSmall hNum hAx n hn hf
  have hmem : f n ∈ {m | 1 ≤ m ∧ IsRep n m} := Nat.sInf_mem hn
  have hm1 : 1 ≤ f n := hmem.1
  have hle : n ≤ sig (f n) := hPre n (f n) hmem.2
  have hmpos : (0 : ℝ) < f n := by exact_mod_cast hm1
  have h10 : (10 : ℝ) * f n ≤ n := by
    have := hf
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)] at this
    linarith
  have hab : 10 ≤ abundancy (f n) := by
    rw [abundancy, le_div_iff₀ hmpos]
    have : (n : ℝ) ≤ sig (f n) := by exact_mod_cast hle
    linarith
  by_contra hcon
  have hn120 : n ≤ 10 ^ 120 := Nat.le_of_not_lt hcon
  have h10n : 10 * f n ≤ n := by exact_mod_cast h10
  have hm119 : f n ≤ 10 ^ 119 := by
    have h : 10 * f n ≤ 10 * 10 ^ 119 := by
      calc 10 * f n ≤ n := h10n
        _ ≤ 10 ^ 120 := hn120
        _ = 10 * 10 ^ 119 := by norm_num
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  rcases Nat.lt_or_ge 5040 (f n) with hbig | hsmall
  · have hA := hAx (f n) hbig hm119
    have hm1r : (1 : ℝ) < f n := by exact_mod_cast (by omega : 1 < f n)
    have hlogpos : 0 < Real.log (f n) := Real.log_pos hm1r
    have hmle : (f n : ℝ) ≤ (10 : ℝ) ^ 119 := by exact_mod_cast hm119
    have hlog : Real.log (f n) ≤ Real.log ((10 : ℝ) ^ 119) :=
      Real.log_le_log (by positivity) hmle
    have hloglog : Real.log (Real.log (f n)) ≤ Real.log (Real.log ((10 : ℝ) ^ 119)) :=
      Real.log_le_log hlogpos hlog
    have hcpos : (0 : ℝ) ≤ (1 + 3.15367e-7) * Real.exp eulerGamma := by positivity
    have hlt : abundancy (f n) < 10 :=
      calc abundancy (f n)
          < (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log (f n)) := hA
        _ ≤ (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log ((10 : ℝ) ^ 119)) :=
          mul_le_mul_of_nonneg_left hloglog hcpos
        _ ≤ 9.99745 := hNum
        _ < 10 := by norm_num
    linarith
  · have := hSmall (f n) hm1 hsmall
    linarith

/-- EP1054.tex lines 1183–1187: `σ(m)/m > 10` for `m = lcm(1, …, 289)`. -/
theorem leaf_Rem_Lcm289Abundant : Principia.Erdos1054.Rem_Lcm289Abundant := by
  show 10 < abundancy (lcmUpTo 289)
  rw [abundancy, sig_lcm289, lcm289_eq]
  norm_num

/-- EP1054.tex lines 1187–1194: the printed digits of `σ(m)/m`, `σ(m)` and `m/σ(m)`. -/
theorem leaf_Rem_Lcm289Values : Principia.Erdos1054.Rem_Lcm289Values := by
  unfold Principia.Erdos1054.Rem_Lcm289Values
  rw [abundancy, sig_lcm289, lcm289_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- EP1054.tex lines 1189–1195: `n = σ(m)` is represented, `f(n)/n ≤ m/σ(m) < 1/10`. -/
theorem link_Rem_Lcm289Witness : Principia.Erdos1054.Spine.Link_Rem_Lcm289Witness := by
  intro hA
  have hA' : 10 < abundancy (lcmUpTo 289) := hA
  have hm0 : (0 : ℝ) < (lcmUpTo 289 : ℝ) := by
    rcases (Nat.cast_nonneg (lcmUpTo 289) : (0 : ℝ) ≤ (lcmUpTo 289 : ℝ)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [abundancy, ← h, div_zero] at hA'
      norm_num at hA'
  have hm1 : 1 ≤ lcmUpTo 289 := by
    have h0 : 0 < lcmUpTo 289 := by exact_mod_cast hm0
    omega
  have hsigF := sig_eq_F_one (lcmUpTo 289)
  refine ⟨(mem_R_iff_exists_F _).2 ⟨1, lcmUpTo 289, le_rfl, hm1, hsigF⟩, ?_, ?_⟩
  · have hf := f_le_of_F 1 (lcmUpTo 289) (sig (lcmUpTo 289)) le_rfl hm1 hsigF
    rw [one_mul] at hf
    exact div_le_div_of_nonneg_right (by exact_mod_cast hf) (Nat.cast_nonneg _)
  · rw [abundancy, lt_div_iff₀ hm0] at hA'
    have hs : (0 : ℝ) < (sig (lcmUpTo 289) : ℝ) := by linarith
    rw [div_lt_iff₀ hs]
    linarith

end Principia.Erdos1054.Proofs
