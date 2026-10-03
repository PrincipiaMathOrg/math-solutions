/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfgottCited

set_option autoImplicit false

/-!
# `cor:austeria` on its two windows, PROVED: `HC.AusteriaWindowCited` leaves the citations

`HC.AusteriaWindowCited` is Helfgott's claim (`ternvin.tex` 5548-5553) that
`S(x) = ∑ Λ(n)η₂(n/x) ≤ 1.04488x` on `(9.5, 10.5) ∪ (13.5, 14.5)`, where "the prime powers
involved do not change … and thus we can find the maximum of the sum just by taking derivatives".
The citation round filed it as a computation. It is calculus, and it is proved here.

On each window only `n ∈ (x/4, x)` contribute, and `η₂(n/x)` is `4 log(4n/x)` or `4 log(x/n)`
according as `x ≥ 2n` or not. So on each side of the kink (`x = 10`, `x = 14`),
`S(x) = A + B log x` with explicit `A`, `B` (`S_w1a` … `S_w2b`).

**The kink argument** (`kink_inc`, `kink_dec`). From `log x ≤ log x₀ + x/x₀ − 1`, and `B ≥ S(x₀)`
on the left piece or `0 ≤ B ≤ S(x₀)` on the right piece, `S(x) ≤ S(x₀)·x/x₀`. So the maximum over
each window is `S(x₀)/x₀`, which needs two facts:
* `S(10)/10 = 1.0424555 ≤ 1.04488`;
* `S(14)/14 = 1.04487679 ≤ 1.04488`, a margin of `3.2·10⁻⁶`.

The sign conditions have margins `≥ 4`.

**Logs** to `10⁻⁹` from `log(1−u) = −∑uᵏ/k` with Mathlib's `Real.abs_log_sub_add_sum_range_le` at
`u = 1/4, 1/5, 1/8, 1/12, 1/13` and `log 2 ∈ (0.6931471803, 0.6931471808)`. The kink values are
sums of products of positive logs, each bounded by interval endpoints
(`scratchpad/austw/bounds.py`: `S(14) ≤ 14.6282752 < 14.62832`).
-/

namespace Principia.Common.TernaryGoldbach.AW

open ArithmeticFunction
open scoped ArithmeticFunction

/-! ## (1) Logs of small primes to `10⁻⁹` -/

/-- `log(1 − u)` bracketed by its Taylor polynomial. -/
theorem log_near (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) (n : ℕ) :
    -(u ^ (n + 1) / (1 - u)) ≤ (∑ i ∈ Finset.range n, u ^ (i + 1) / (i + 1)) + Real.log (1 - u) ∧
      (∑ i ∈ Finset.range n, u ^ (i + 1) / (i + 1)) + Real.log (1 - u) ≤ u ^ (n + 1) / (1 - u) := by
  have hu : |u| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hu n
  rw [abs_of_nonneg h0] at h
  exact abs_le.mp h

theorem l2_bd : (0.6931471803 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

theorem l3_bd : (1.098612288 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.098612290 := by
  have h := log_near (1 / 4) (by norm_num) (by norm_num) 16
  have e : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  obtain ⟨a, b⟩ := l2_bd
  constructor <;> linarith [h.1, h.2]

theorem l5_bd : (1.609437911 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.609437913 := by
  have h := log_near (1 / 5) (by norm_num) (by norm_num) 14
  have e : Real.log (1 - 1 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  obtain ⟨a, b⟩ := l2_bd
  constructor <;> linarith [h.1, h.2]

theorem l7_bd : (1.945910148 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.945910150 := by
  have h := log_near (1 / 8) (by norm_num) (by norm_num) 11
  have e : Real.log (1 - 1 / 8) = Real.log 7 - 3 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  obtain ⟨a, b⟩ := l2_bd
  constructor <;> linarith [h.1, h.2]

theorem l11_bd : (2.397895271 : ℝ) < Real.log 11 ∧ Real.log 11 < 2.397895275 := by
  have h := log_near (1 / 12) (by norm_num) (by norm_num) 9
  have e : Real.log (1 - 1 / 12) = Real.log 11 - 2 * Real.log 2 - Real.log 3 := by
    rw [show (1 : ℝ) - 1 / 12 = 11 / 12 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    ring
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  obtain ⟨a, b⟩ := l2_bd
  obtain ⟨c, d⟩ := l3_bd
  constructor <;> linarith [h.1, h.2]

theorem l13_bd : (2.564949356 : ℝ) < Real.log 13 ∧ Real.log 13 < 2.564949360 := by
  have h := log_near (1 / 13) (by norm_num) (by norm_num) 9
  have e : Real.log (1 - 1 / 13) = 2 * Real.log 2 + Real.log 3 - Real.log 13 := by
    rw [show (1 : ℝ) - 1 / 13 = 12 / 13 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e] at h
  norm_num [Finset.sum_range_succ] at h
  obtain ⟨a, b⟩ := l2_bd
  obtain ⟨c, d⟩ := l3_bd
  constructor <;> linarith [h.1, h.2]

theorem log4 : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem log8 : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num

theorem log9 : Real.log 9 = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem log10 : Real.log 10 = Real.log 2 + Real.log 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log14 : Real.log 14 = Real.log 2 + Real.log 7 := by
  rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

/-! ## (2) The von Mangoldt values -/

theorem vm0 : Λ 0 = 0 := by simp
theorem vm1 : Λ 1 = 0 := vonMangoldt_apply_one
theorem vm2 : Λ 2 = Real.log 2 := by rw [vonMangoldt_apply_prime Nat.prime_two]; norm_num
theorem vm3 : Λ 3 = Real.log 3 := by rw [vonMangoldt_apply_prime Nat.prime_three]; norm_num
theorem vm4 : Λ 4 = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, vonMangoldt_apply_pow (by norm_num), vm2]
theorem vm5 : Λ 5 = Real.log 5 := by rw [vonMangoldt_apply_prime (by norm_num)]; norm_num
theorem vm6 : Λ 6 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
theorem vm7 : Λ 7 = Real.log 7 := by rw [vonMangoldt_apply_prime (by norm_num)]; norm_num
theorem vm8 : Λ 8 = Real.log 2 := by
  rw [show (8 : ℕ) = 2 ^ 3 from rfl, vonMangoldt_apply_pow (by norm_num), vm2]
theorem vm9 : Λ 9 = Real.log 3 := by
  rw [show (9 : ℕ) = 3 ^ 2 from rfl, vonMangoldt_apply_pow (by norm_num), vm3]
theorem vm10 : Λ 10 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
theorem vm11 : Λ 11 = Real.log 11 := by rw [vonMangoldt_apply_prime (by norm_num)]; norm_num
theorem vm12 : Λ 12 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
theorem vm13 : Λ 13 = Real.log 13 := by rw [vonMangoldt_apply_prime (by norm_num)]; norm_num
theorem vm14 : Λ 14 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)

/-! ## (3) `S(x)` as a finite sum, and on each piece -/

/-- Terms with `n ≥ N ≥ x` vanish (`n/x ≥ 1`). -/
theorem sEta2_eq_sum (x : ℝ) (hx : 0 < x) (N : ℕ) (hN : x ≤ N) :
    GS.sEta2 x = ∑ n ∈ Finset.range N, Λ n * HW.eta2 ((n : ℝ) / x) := by
  unfold GS.sEta2
  refine tsum_eq_sum (s := Finset.range N) (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [HW.eta2_of_one_le ((one_le_div hx).mpr (by linarith)), mul_zero]

/-- **Window 2, left of the kink** (`13.5 ≤ x ≤ 14`). -/
theorem S_w2a (x : ℝ) (h1 : 13.5 ≤ x) (h2 : x ≤ 14) :
    GS.sEta2 x = Real.log 2 * (4 * (2 * Real.log 2 + Real.log 4 - Real.log x)) +
      Real.log 5 * (4 * (2 * Real.log 2 + Real.log 5 - Real.log x)) +
      Real.log 7 * (4 * (Real.log x - Real.log 7)) + Real.log 2 * (4 * (Real.log x - Real.log 8)) +
      Real.log 3 * (4 * (Real.log x - Real.log 9)) +
      Real.log 11 * (4 * (Real.log x - Real.log 11)) +
      Real.log 13 * (4 * (Real.log x - Real.log 13)) := by
  have hx : 0 < x := by linarith
  rw [sEta2_eq_sum x hx 15 (by norm_num; linarith)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one]
  have e2 : HW.eta2 (2 / x) = 0 := HW.eta2_div_zero (by norm_num) hx (Or.inr (by linarith))
  have e3 : HW.eta2 (3 / x) = 0 := HW.eta2_div_zero (by norm_num) hx (Or.inr (by linarith))
  have e4 := HW.eta2_hi (s := 4) (y := x) (by norm_num) (by linarith) (by linarith)
  have e5 := HW.eta2_hi (s := 5) (y := x) (by norm_num) (by linarith) (by linarith)
  have e7 := HW.eta2_lo (s := 7) (y := x) (by norm_num) (by linarith) (by linarith)
  have e8 := HW.eta2_lo (s := 8) (y := x) (by norm_num) (by linarith) (by linarith)
  have e9 := HW.eta2_lo (s := 9) (y := x) (by norm_num) (by linarith) (by linarith)
  have e11 := HW.eta2_lo (s := 11) (y := x) (by norm_num) (by linarith) (by linarith)
  have e13 := HW.eta2_lo (s := 13) (y := x) (by norm_num) (by linarith) (by linarith)
  rw [vm0, vm1, vm2, vm3, vm4, vm5, vm6, vm7, vm8, vm9, vm10, vm11, vm12, vm13, vm14, e2, e3, e4,
    e5, e7, e8, e9, e11, e13]
  ring

/-- **Window 2, right of the kink** (`14 ≤ x ≤ 14.5`): the `n = 7` term changes branch. -/
theorem S_w2b (x : ℝ) (h1 : 14 ≤ x) (h2 : x ≤ 14.5) :
    GS.sEta2 x = Real.log 2 * (4 * (2 * Real.log 2 + Real.log 4 - Real.log x)) +
      Real.log 5 * (4 * (2 * Real.log 2 + Real.log 5 - Real.log x)) +
      Real.log 7 * (4 * (2 * Real.log 2 + Real.log 7 - Real.log x)) +
      Real.log 2 * (4 * (Real.log x - Real.log 8)) +
      Real.log 3 * (4 * (Real.log x - Real.log 9)) +
      Real.log 11 * (4 * (Real.log x - Real.log 11)) +
      Real.log 13 * (4 * (Real.log x - Real.log 13)) := by
  have hx : 0 < x := by linarith
  rw [sEta2_eq_sum x hx 15 (by norm_num; linarith)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one]
  have e2 : HW.eta2 (2 / x) = 0 := HW.eta2_div_zero (by norm_num) hx (Or.inr (by linarith))
  have e3 : HW.eta2 (3 / x) = 0 := HW.eta2_div_zero (by norm_num) hx (Or.inr (by linarith))
  have e4 := HW.eta2_hi (s := 4) (y := x) (by norm_num) (by linarith) (by linarith)
  have e5 := HW.eta2_hi (s := 5) (y := x) (by norm_num) (by linarith) (by linarith)
  have e7 := HW.eta2_hi (s := 7) (y := x) (by norm_num) (by linarith) (by linarith)
  have e8 := HW.eta2_lo (s := 8) (y := x) (by norm_num) (by linarith) (by linarith)
  have e9 := HW.eta2_lo (s := 9) (y := x) (by norm_num) (by linarith) (by linarith)
  have e11 := HW.eta2_lo (s := 11) (y := x) (by norm_num) (by linarith) (by linarith)
  have e13 := HW.eta2_lo (s := 13) (y := x) (by norm_num) (by linarith) (by linarith)
  rw [vm0, vm1, vm2, vm3, vm4, vm5, vm6, vm7, vm8, vm9, vm10, vm11, vm12, vm13, vm14, e2, e3, e4,
    e5, e7, e8, e9, e11, e13]
  ring

/-- **Window 1, left of the kink** (`9.5 ≤ x ≤ 10`). -/
theorem S_w1a (x : ℝ) (h1 : 9.5 ≤ x) (h2 : x ≤ 10) :
    GS.sEta2 x = Real.log 3 * (4 * (2 * Real.log 2 + Real.log 3 - Real.log x)) +
      Real.log 2 * (4 * (2 * Real.log 2 + Real.log 4 - Real.log x)) +
      Real.log 5 * (4 * (Real.log x - Real.log 5)) + Real.log 7 * (4 * (Real.log x - Real.log 7)) +
      Real.log 2 * (4 * (Real.log x - Real.log 8)) +
      Real.log 3 * (4 * (Real.log x - Real.log 9)) := by
  have hx : 0 < x := by linarith
  rw [sEta2_eq_sum x hx 11 (by norm_num; linarith)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one]
  have e2 : HW.eta2 (2 / x) = 0 := HW.eta2_div_zero (by norm_num) hx (Or.inr (by linarith))
  have e3 := HW.eta2_hi (s := 3) (y := x) (by norm_num) (by linarith) (by linarith)
  have e4 := HW.eta2_hi (s := 4) (y := x) (by norm_num) (by linarith) (by linarith)
  have e5 := HW.eta2_lo (s := 5) (y := x) (by norm_num) (by linarith) (by linarith)
  have e7 := HW.eta2_lo (s := 7) (y := x) (by norm_num) (by linarith) (by linarith)
  have e8 := HW.eta2_lo (s := 8) (y := x) (by norm_num) (by linarith) (by linarith)
  have e9 := HW.eta2_lo (s := 9) (y := x) (by norm_num) (by linarith) (by linarith)
  rw [vm0, vm1, vm2, vm3, vm4, vm5, vm6, vm7, vm8, vm9, vm10, e2, e3, e4, e5, e7, e8, e9]
  ring

/-- **Window 1, right of the kink** (`10 ≤ x ≤ 10.5`): the `n = 5` term changes branch. -/
theorem S_w1b (x : ℝ) (h1 : 10 ≤ x) (h2 : x ≤ 10.5) :
    GS.sEta2 x = Real.log 3 * (4 * (2 * Real.log 2 + Real.log 3 - Real.log x)) +
      Real.log 2 * (4 * (2 * Real.log 2 + Real.log 4 - Real.log x)) +
      Real.log 5 * (4 * (2 * Real.log 2 + Real.log 5 - Real.log x)) +
      Real.log 7 * (4 * (Real.log x - Real.log 7)) +
      Real.log 2 * (4 * (Real.log x - Real.log 8)) +
      Real.log 3 * (4 * (Real.log x - Real.log 9)) := by
  have hx : 0 < x := by linarith
  rw [sEta2_eq_sum x hx 11 (by norm_num; linarith)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one]
  have e2 : HW.eta2 (2 / x) = 0 := HW.eta2_div_zero (by norm_num) hx (Or.inr (by linarith))
  have e3 := HW.eta2_hi (s := 3) (y := x) (by norm_num) (by linarith) (by linarith)
  have e4 := HW.eta2_hi (s := 4) (y := x) (by norm_num) (by linarith) (by linarith)
  have e5 := HW.eta2_hi (s := 5) (y := x) (by norm_num) (by linarith) (by linarith)
  have e7 := HW.eta2_lo (s := 7) (y := x) (by norm_num) (by linarith) (by linarith)
  have e8 := HW.eta2_lo (s := 8) (y := x) (by norm_num) (by linarith) (by linarith)
  have e9 := HW.eta2_lo (s := 9) (y := x) (by norm_num) (by linarith) (by linarith)
  rw [vm0, vm1, vm2, vm3, vm4, vm5, vm6, vm7, vm8, vm9, vm10, e2, e3, e4, e5, e7, e8, e9]
  ring

/-! ## (4) The kink argument -/

/-- `log x · x₀ ≤ log x₀ · x₀ + x − x₀` (tangent line of `log` at `x₀`). -/
theorem tan_log (x x0 : ℝ) (hx : 0 < x) (hx0 : 0 < x0) :
    Real.log x * x0 ≤ Real.log x0 * x0 + x - x0 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hx0)
  rw [Real.log_div hx.ne' hx0.ne'] at h
  have h2 := mul_le_mul_of_nonneg_right h hx0.le
  have e : (x / x0 - 1) * x0 = x - x0 := by
    rw [sub_mul, div_mul_cancel₀ x hx0.ne', one_mul]
  nlinarith [h2, e]

/-- **Left of the kink**: `A + B log x ≤ c x` for `x ≤ x₀` when `B ≥ S₀ := A + B log x₀` and
`S₀ ≤ c x₀`. -/
theorem kink_inc (A B L L0 x x0 c : ℝ) (hx0 : 0 < x0) (hx : x ≤ x0) (hxpos : 0 ≤ x) (hB : 0 ≤ B)
    (htan : L * x0 ≤ L0 * x0 + x - x0) (hBS : A + B * L0 ≤ B) (hc : A + B * L0 ≤ c * x0) :
    A + B * L ≤ c * x := by
  have p1 := mul_le_mul_of_nonneg_left htan hB
  have p2 : 0 ≤ (B - (A + B * L0)) * (x0 - x) := mul_nonneg (by linarith) (by linarith)
  have p3 := mul_le_mul_of_nonneg_right hc hxpos
  have key : (A + B * L) * x0 ≤ (c * x) * x0 := by nlinarith [p1, p2, p3]
  exact le_of_mul_le_mul_right key hx0

/-- **Right of the kink**: `A + B log x ≤ c x` for `x ≥ x₀` when `0 ≤ B ≤ S₀` and `S₀ ≤ c x₀`. -/
theorem kink_dec (A B L L0 x x0 c : ℝ) (hx0 : 0 < x0) (hx : x0 ≤ x) (hB : 0 ≤ B)
    (htan : L * x0 ≤ L0 * x0 + x - x0) (hBS : B ≤ A + B * L0) (hc : A + B * L0 ≤ c * x0) :
    A + B * L ≤ c * x := by
  have hxpos : 0 ≤ x := by linarith
  have p1 := mul_le_mul_of_nonneg_left htan hB
  have p2 : 0 ≤ (A + B * L0 - B) * (x - x0) := mul_nonneg (by linarith) (by linarith)
  have p3 := mul_le_mul_of_nonneg_right hc hxpos
  have key : (A + B * L) * x0 ≤ (c * x) * x0 := by nlinarith [p1, p2, p3]
  exact le_of_mul_le_mul_right key hx0

/-! ## (5) The kink values -/

/-- `a · c ≤ b · d` from `a ≤ b`, `0 ≤ c ≤ d`, `0 ≤ b`. -/
theorem pm (a b c d : ℝ) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) (hb : 0 ≤ b) : a * c ≤ b * d :=
  mul_le_mul hab hcd hc hb

/-- **`S(14) ≤ 14.62832`**, i.e. `S(14)/14 ≤ 1.04488` (truth `1.04487679`). -/
theorem s14_le :
    4 * (Real.log 2 * (3 * Real.log 2 - Real.log 7) +
      Real.log 5 * (Real.log 2 + Real.log 5 - Real.log 7) + Real.log 7 * Real.log 2 +
      Real.log 2 * (Real.log 7 - 2 * Real.log 2) +
      Real.log 3 * (Real.log 2 + Real.log 7 - 2 * Real.log 3) +
      Real.log 11 * (Real.log 2 + Real.log 7 - Real.log 11) +
      Real.log 13 * (Real.log 2 + Real.log 7 - Real.log 13)) ≤ 14.62832 := by
  obtain ⟨a2, b2⟩ := l2_bd
  obtain ⟨a3, b3⟩ := l3_bd
  obtain ⟨a5, b5⟩ := l5_bd
  obtain ⟨a7, b7⟩ := l7_bd
  obtain ⟨a11, b11⟩ := l11_bd
  obtain ⟨a13, b13⟩ := l13_bd
  have p1 := pm (Real.log 2) 0.6931471808 (3 * Real.log 2 - Real.log 7)
    (3 * 0.6931471808 - 1.945910148) b2.le (by linarith) (by linarith) (by norm_num)
  have p2 := pm (Real.log 5) 1.609437913 (Real.log 2 + Real.log 5 - Real.log 7)
    (0.6931471808 + 1.609437913 - 1.945910148) b5.le (by linarith) (by linarith) (by norm_num)
  have p3 := pm (Real.log 7) 1.945910150 (Real.log 2) 0.6931471808 b7.le (by linarith)
    b2.le (by norm_num)
  have p4 := pm (Real.log 2) 0.6931471808 (Real.log 7 - 2 * Real.log 2)
    (1.945910150 - 2 * 0.6931471803) b2.le (by linarith) (by linarith) (by norm_num)
  have p5 := pm (Real.log 3) 1.098612290 (Real.log 2 + Real.log 7 - 2 * Real.log 3)
    (0.6931471808 + 1.945910150 - 2 * 1.098612288) b3.le (by linarith) (by linarith)
    (by norm_num)
  have p6 := pm (Real.log 11) 2.397895275 (Real.log 2 + Real.log 7 - Real.log 11)
    (0.6931471808 + 1.945910150 - 2.397895271) b11.le (by linarith) (by linarith) (by norm_num)
  have p7 := pm (Real.log 13) 2.564949360 (Real.log 2 + Real.log 7 - Real.log 13)
    (0.6931471808 + 1.945910150 - 2.564949356) b13.le (by linarith) (by linarith) (by norm_num)
  norm_num at p1 p2 p3 p4 p5 p6 p7
  linarith

/-- **`S(14) ≥ 14`** (a crude lower bound, for the right-of-kink sign condition). -/
theorem s14_ge :
    14 ≤ 4 * (Real.log 2 * (3 * Real.log 2 - Real.log 7) +
      Real.log 5 * (Real.log 2 + Real.log 5 - Real.log 7) + Real.log 7 * Real.log 2 +
      Real.log 2 * (Real.log 7 - 2 * Real.log 2) +
      Real.log 3 * (Real.log 2 + Real.log 7 - 2 * Real.log 3) +
      Real.log 11 * (Real.log 2 + Real.log 7 - Real.log 11) +
      Real.log 13 * (Real.log 2 + Real.log 7 - Real.log 13)) := by
  obtain ⟨a2, b2⟩ := l2_bd
  obtain ⟨a3, b3⟩ := l3_bd
  obtain ⟨a5, b5⟩ := l5_bd
  obtain ⟨a7, b7⟩ := l7_bd
  obtain ⟨a11, b11⟩ := l11_bd
  obtain ⟨a13, b13⟩ := l13_bd
  have p1 := pm 0.6931471803 (Real.log 2) (3 * 0.6931471803 - 1.945910150)
    (3 * Real.log 2 - Real.log 7) a2.le (by norm_num) (by linarith) (by linarith)
  have p2 := pm 1.609437911 (Real.log 5) (0.6931471803 + 1.609437911 - 1.945910150)
    (Real.log 2 + Real.log 5 - Real.log 7) a5.le (by norm_num) (by linarith) (by linarith)
  have p3 := pm 1.945910148 (Real.log 7) 0.6931471803 (Real.log 2) a7.le (by norm_num) a2.le
    (by linarith)
  have p4 := pm 0.6931471803 (Real.log 2) (1.945910148 - 2 * 0.6931471808)
    (Real.log 7 - 2 * Real.log 2) a2.le (by norm_num) (by linarith) (by linarith)
  have p5 := pm 1.098612288 (Real.log 3) (0.6931471803 + 1.945910148 - 2 * 1.098612290)
    (Real.log 2 + Real.log 7 - 2 * Real.log 3) a3.le (by norm_num) (by linarith) (by linarith)
  have p6 := pm 2.397895271 (Real.log 11) (0.6931471803 + 1.945910148 - 2.397895275)
    (Real.log 2 + Real.log 7 - Real.log 11) a11.le (by norm_num) (by linarith) (by linarith)
  have p7 := pm 2.564949356 (Real.log 13) (0.6931471803 + 1.945910148 - 2.564949360)
    (Real.log 2 + Real.log 7 - Real.log 13) a13.le (by norm_num) (by linarith) (by linarith)
  norm_num at p1 p2 p3 p4 p5 p6 p7
  linarith

/-- **`10 ≤ S(10) ≤ 10.4488`**, i.e. `S(10)/10 ≤ 1.04488` (truth `1.0424555`). -/
theorem s10_bd :
    10 ≤ 4 * (Real.log 3 * (Real.log 2 + Real.log 3 - Real.log 5) +
      Real.log 2 * (3 * Real.log 2 - Real.log 5) + Real.log 5 * Real.log 2 +
      Real.log 7 * (Real.log 2 + Real.log 5 - Real.log 7) +
      Real.log 2 * (Real.log 5 - 2 * Real.log 2) +
      Real.log 3 * (Real.log 2 + Real.log 5 - 2 * Real.log 3)) ∧
    4 * (Real.log 3 * (Real.log 2 + Real.log 3 - Real.log 5) +
      Real.log 2 * (3 * Real.log 2 - Real.log 5) + Real.log 5 * Real.log 2 +
      Real.log 7 * (Real.log 2 + Real.log 5 - Real.log 7) +
      Real.log 2 * (Real.log 5 - 2 * Real.log 2) +
      Real.log 3 * (Real.log 2 + Real.log 5 - 2 * Real.log 3)) ≤ 10.4488 := by
  obtain ⟨a2, b2⟩ := l2_bd
  obtain ⟨a3, b3⟩ := l3_bd
  obtain ⟨a5, b5⟩ := l5_bd
  obtain ⟨a7, b7⟩ := l7_bd
  constructor
  · have p1 := pm 1.098612288 (Real.log 3) (0.6931471803 + 1.098612288 - 1.609437913)
      (Real.log 2 + Real.log 3 - Real.log 5) a3.le (by norm_num) (by linarith) (by linarith)
    have p2 := pm 0.6931471803 (Real.log 2) (3 * 0.6931471803 - 1.609437913)
      (3 * Real.log 2 - Real.log 5) a2.le (by norm_num) (by linarith) (by linarith)
    have p3 := pm 1.609437911 (Real.log 5) 0.6931471803 (Real.log 2) a5.le (by norm_num) a2.le
      (by linarith)
    have p4 := pm 1.945910148 (Real.log 7) (0.6931471803 + 1.609437911 - 1.945910150)
      (Real.log 2 + Real.log 5 - Real.log 7) a7.le (by norm_num) (by linarith) (by linarith)
    have p5 := pm 0.6931471803 (Real.log 2) (1.609437911 - 2 * 0.6931471808)
      (Real.log 5 - 2 * Real.log 2) a2.le (by norm_num) (by linarith) (by linarith)
    have p6 := pm 1.098612288 (Real.log 3) (0.6931471803 + 1.609437911 - 2 * 1.098612290)
      (Real.log 2 + Real.log 5 - 2 * Real.log 3) a3.le (by norm_num) (by linarith) (by linarith)
    norm_num at p1 p2 p3 p4 p5 p6
    linarith
  · have p1 := pm (Real.log 3) 1.098612290 (Real.log 2 + Real.log 3 - Real.log 5)
      (0.6931471808 + 1.098612290 - 1.609437911) b3.le (by linarith) (by linarith) (by norm_num)
    have p2 := pm (Real.log 2) 0.6931471808 (3 * Real.log 2 - Real.log 5)
      (3 * 0.6931471808 - 1.609437911) b2.le (by linarith) (by linarith) (by norm_num)
    have p3 := pm (Real.log 5) 1.609437913 (Real.log 2) 0.6931471808 b5.le (by linarith) b2.le
      (by norm_num)
    have p4 := pm (Real.log 7) 1.945910150 (Real.log 2 + Real.log 5 - Real.log 7)
      (0.6931471808 + 1.609437913 - 1.945910148) b7.le (by linarith) (by linarith) (by norm_num)
    have p5 := pm (Real.log 2) 0.6931471808 (Real.log 5 - 2 * Real.log 2)
      (1.609437913 - 2 * 0.6931471803) b2.le (by linarith) (by linarith) (by norm_num)
    have p6 := pm (Real.log 3) 1.098612290 (Real.log 2 + Real.log 5 - 2 * Real.log 3)
      (0.6931471808 + 1.609437913 - 2 * 1.098612288) b3.le (by linarith) (by linarith)
      (by norm_num)
    norm_num at p1 p2 p3 p4 p5 p6
    linarith

/-! ## (6) The windows -/

/-- **Window 2**: `S(x) ≤ 1.04488x` on `[13.5, 14.5]`. -/
theorem window2 (x : ℝ) (h1 : 13.5 ≤ x) (h2 : x ≤ 14.5) : GS.sEta2 x ≤ 1.04488 * x := by
  have hx : 0 < x := by linarith
  have ht := tan_log x 14 hx (by norm_num)
  rw [log14] at ht
  have hu := s14_le
  have hd := s14_ge
  obtain ⟨a2, b2⟩ := l2_bd
  obtain ⟨a3, b3⟩ := l3_bd
  obtain ⟨a5, b5⟩ := l5_bd
  obtain ⟨a7, b7⟩ := l7_bd
  obtain ⟨a11, b11⟩ := l11_bd
  obtain ⟨a13, b13⟩ := l13_bd
  rcases le_total x 14 with hle | hge
  · rw [S_w2a x h1 hle, log4, log8, log9]
    have k := kink_inc
      (4 * (Real.log 2 * (4 * Real.log 2) + Real.log 5 * (2 * Real.log 2 + Real.log 5) -
        Real.log 7 * Real.log 7 - Real.log 2 * (3 * Real.log 2) - Real.log 3 * (2 * Real.log 3) -
        Real.log 11 * Real.log 11 - Real.log 13 * Real.log 13))
      (4 * (Real.log 7 + Real.log 3 + Real.log 11 + Real.log 13 - Real.log 5))
      (Real.log x) (Real.log 2 + Real.log 7) x 14 1.04488 (by norm_num) hle hx.le
      (by linarith) ht (by nlinarith) (by nlinarith)
    linarith
  · rw [S_w2b x hge h2, log4, log8, log9]
    have k := kink_dec
      (4 * (Real.log 2 * (4 * Real.log 2) + Real.log 5 * (2 * Real.log 2 + Real.log 5) +
        Real.log 7 * (2 * Real.log 2 + Real.log 7) - Real.log 2 * (3 * Real.log 2) -
        Real.log 3 * (2 * Real.log 3) - Real.log 11 * Real.log 11 - Real.log 13 * Real.log 13))
      (4 * (Real.log 3 + Real.log 11 + Real.log 13 - Real.log 5 - Real.log 7))
      (Real.log x) (Real.log 2 + Real.log 7) x 14 1.04488 (by norm_num) hge (by linarith) ht
      (by nlinarith) (by nlinarith)
    linarith

/-- **Window 1**: `S(x) ≤ 1.04488x` on `[9.5, 10.5]`. -/
theorem window1 (x : ℝ) (h1 : 9.5 ≤ x) (h2 : x ≤ 10.5) : GS.sEta2 x ≤ 1.04488 * x := by
  have hx : 0 < x := by linarith
  have ht := tan_log x 10 hx (by norm_num)
  rw [log10] at ht
  obtain ⟨hd, hu⟩ := s10_bd
  obtain ⟨a2, b2⟩ := l2_bd
  obtain ⟨a3, b3⟩ := l3_bd
  obtain ⟨a5, b5⟩ := l5_bd
  obtain ⟨a7, b7⟩ := l7_bd
  rcases le_total x 10 with hle | hge
  · rw [S_w1a x h1 hle, log4, log8, log9]
    have k := kink_inc
      (4 * (Real.log 3 * (2 * Real.log 2 + Real.log 3) + Real.log 2 * (4 * Real.log 2) -
        Real.log 5 * Real.log 5 - Real.log 7 * Real.log 7 - Real.log 2 * (3 * Real.log 2) -
        Real.log 3 * (2 * Real.log 3)))
      (4 * (Real.log 5 + Real.log 7))
      (Real.log x) (Real.log 2 + Real.log 5) x 10 1.04488 (by norm_num) hle hx.le
      (by linarith) ht (by nlinarith) (by nlinarith)
    linarith
  · rw [S_w1b x hge h2, log4, log8, log9]
    have k := kink_dec
      (4 * (Real.log 3 * (2 * Real.log 2 + Real.log 3) + Real.log 2 * (4 * Real.log 2) +
        Real.log 5 * (2 * Real.log 2 + Real.log 5) - Real.log 7 * Real.log 7 -
        Real.log 2 * (3 * Real.log 2) - Real.log 3 * (2 * Real.log 3)))
      (4 * (Real.log 7 - Real.log 5))
      (Real.log x) (Real.log 2 + Real.log 5) x 10 1.04488 (by norm_num) hge (by linarith) ht
      (by nlinarith) (by nlinarith)
    linarith

/-- **`HC.AusteriaWindowCited` PROVED** -- the citation leaves: `cor:austeria` on its two
windows is calculus, not a computation. -/
theorem austeriaWindow : HC.AusteriaWindowCited := by
  intro x hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact window1 x h1.le h2.le
  · exact window2 x h1.le h2.le

end Principia.Common.TernaryGoldbach.AW
