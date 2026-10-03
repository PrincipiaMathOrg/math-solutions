/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.DrujalSpine

set_option autoImplicit false

/-!
# `DS.KSmall η₊` PROVED, by crude explicit bounds

`DS.KSmall η` asks, at every `x ≥ 4.9·10²⁶`, for the summability of `n ↦ Λ(n)|η(n/x)|` and for
`kAgg η x ≤ 10⁻⁶`, where (`DrujalSpine.lean`)

```
 kAgg η x = (∑_{q ≤ r odd} (δ₀r/q)·kArc q + ∑_{q ≤ 2r even} (2δ₀r/q)·kArc q) / x²
 kArc q   = φ(q)·bQ q·(2·sAbs + bQ q),   sAbs = ∑_n Λ(n)|η(n/x)|
 bQ q     = 2 ∑_{p | q} log p ∑_{k ≥ 0} |η(p^{k+1}/x)|.
```

The truth for `η₊` is `≈ 5·10⁻¹⁴`; this file proves `≤ 9.63·10⁻¹⁰`, a factor `1038` inside the
budget. Every step is elementary; nothing about primes is used beyond `Λ(n) ≤ log n` and
`∑_{d | q} Λ(d) = log q`.

## The bound chain (`scratchpad/ksmall/price.py`, `price2.py`)

1. **Shape** (`etaPlus_le`): `|η₊(t)| ≤ 3·t e^{−t}` for `t ≥ 0`. From `η₊ = h₂₀₀(t)·t·e^{−t²/2}`,
   `|h₂₀₀| ≤ |h| + 2.7·10⁻⁴` (`BS.band_sharp`), `h ≤ e^{1/2}` (`hFun_le`: `t²(2−t)³ ≤ 2−t ≤
   e^{1−t}`), and `e^{−t²/2} ≤ e^{1/2}e^{−t}`. Constant `(e^{1/2} + 2.7·10⁻⁴)e^{1/2} = 2.7187`.
2. **`sAbs`** (`sAbs_le`): `Λ(n) ≤ log n ≤ log x + n/x`, so each term is at most
   `3(log x + t)·t e^{−t} ≤ 3(2 log x + 16)·e^{−t/2}` (`t e^{−t} ≤ 2e^{−t/2}`,
   `t² e^{−t} ≤ 16e^{−t/2}`), `t = n/x`. The geometric series in `r = e^{−1/2x}` sums to
   `(1−r)⁻¹ ≤ 2x + 1`: `sAbs ≤ 3(2 log x + 16)(2x + 1)` (`≈ 834x` at the threshold). The same
   majorant gives the summability (`summable_helf`), so summability is not the hard part.
3. **`bQ`** (`bQ_le`): along `t_k = p^{k+1}/x` (ratio `p ≥ 2`), `t e^{−t} ≤ 4(F(pt) − F(t))` with
   `F(s) = s/(1+s)` (`tele`: `(1+2s)(1+s) ≤ 4(1 + s + s²/2) ≤ 4e^s`), so the `k`-sum telescopes to
   `≤ 3·4 = 12` UNIFORMLY in `x` (`sum_pow_le`). Then `∑_{p | q} log p ≤ ∑_{d | q} Λ(d) = log q ≤
   13` (`q ≤ 3·10⁵ ≤ 2.7¹³`): `bQ ≤ 2·12·13 = 312`.
4. **`kAgg`** (`kAgg_le`): `φ(q) ≤ q` cancels the arc length `δ₀r/q`; `#odd ≤ 1.5·10⁵`,
   `#even ≤ 3·10⁵` give `kAgg ≤ 9·10¹¹·312·(2·sAbs + 312)/x²`.
5. **Close** (`ksmall_helf`): `log x ≤ x/X₀ + 61` (`log X₀ ≤ 62`, `X₀ = 4.9·10²⁶ ≤ 2.7⁶²`), so
   `2·sAbs + 312 ≤ 24x²/X₀ + 12x/X₀ + 1656x + 1140`, and at `x ≥ X₀`
   `kAgg ≤ 2.808·10¹⁴·(24/X₀ + (1656 + 12/X₀)/X₀ + 1140/X₀²) = 9.63·10⁻¹⁰ ≤ 10⁻⁶`.
-/

namespace Principia.Common.TernaryGoldbach.KS

open ArithmeticFunction Finset
open scoped ArithmeticFunction

/-! ## Step 1: the shape of `η₊` -/

/-- **`h(t) ≤ e^{1/2}`** for every real `t` (the maximum, at `t = 1`): on `[0,2]`,
`t²(2−t)³ = (t(2−t))²(2−t) ≤ 2 − t ≤ e^{1−t}`. -/
theorem hFun_le (t : ℝ) : HW.hFun t ≤ Real.exp (1 / 2) := by
  unfold HW.hFun
  split_ifs with h
  · obtain ⟨h0, h2⟩ := h
    have hw0 : 0 ≤ t * (2 - t) := mul_nonneg h0 (by linarith)
    have hw1 : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have hsq : (t * (2 - t)) ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
    have hp : t ^ 2 * (2 - t) ^ 3 ≤ 2 - t := by
      rw [show t ^ 2 * (2 - t) ^ 3 = (t * (2 - t)) ^ 2 * (2 - t) by ring]
      exact mul_le_of_le_one_left (by linarith) hsq
    have he : 2 - t ≤ Real.exp (1 - t) := by linarith [Real.add_one_le_exp (1 - t)]
    have hprod : Real.exp (1 - t) * Real.exp (t - 1 / 2) = Real.exp (1 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2)
        ≤ Real.exp (1 - t) * Real.exp (t - 1 / 2) :=
          mul_le_mul_of_nonneg_right (hp.trans he) (Real.exp_pos _).le
      _ = Real.exp (1 / 2) := hprod
  · exact (Real.exp_pos _).le

/-- **`|h₂₀₀(t)| ≤ 1.64907`** for every real `t`: `e^{1/2} + 2.7·10⁻⁴ ≤ 1.6488 + 0.00027`. -/
theorem abs_hH_le (t : ℝ) : |HW.hH 200 t| ≤ 1.64907 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [HW.hH_of_nonpos 200 ht, abs_zero]
    norm_num
  · have hb := BS.band_sharp t ht
    have hf := hFun_le t
    have hf0 := BL.hFun_nonneg t
    have he := BL.exp_half_le
    have h1 := abs_sub_abs_le_abs_sub (HW.hH 200 t) (HW.hFun t)
    rw [abs_of_nonneg hf0] at h1
    linarith

/-- **The shape of `η₊`: `|η₊(t)| ≤ 3·t e^{−t}` for `t ≥ 0`** (constant `2.7187`), from
`|h₂₀₀| ≤ 1.64907` and `e^{−t²/2} ≤ e^{1/2}e^{−t}` (`(t − 1)² ≥ 0`). -/
theorem etaPlus_le (t : ℝ) (ht : 0 ≤ t) : |HW.etaPlus t| ≤ 3 * (t * Real.exp (-t)) := by
  have hh := abs_hH_le t
  have he := BL.exp_half_le
  have hg : Real.exp (-t ^ 2 / 2) ≤ Real.exp (1 / 2) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (t - 1)])
  have hte : 0 ≤ t * Real.exp (-t) := mul_nonneg ht (Real.exp_pos _).le
  have habs : |HW.etaPlus t| = |HW.hH 200 t| * (t * Real.exp (-t ^ 2 / 2)) := by
    rw [HW.etaPlus, abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
    ring
  rw [habs]
  calc |HW.hH 200 t| * (t * Real.exp (-t ^ 2 / 2))
      ≤ 1.64907 * (t * (Real.exp (1 / 2) * Real.exp (-t))) :=
        mul_le_mul hh (mul_le_mul_of_nonneg_left hg ht)
          (mul_nonneg ht (Real.exp_pos _).le) (by norm_num)
    _ = 1.64907 * Real.exp (1 / 2) * (t * Real.exp (-t)) := by ring
    _ ≤ 3 * (t * Real.exp (-t)) := by
        refine mul_le_mul_of_nonneg_right ?_ hte
        linarith

/-! ## Step 2: `sAbs` and summability -/

/-- `e^{−t} = e^{−t/2}·e^{−t/2}`. -/
theorem exp_neg_split (t : ℝ) : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- `e^{t/2}·e^{−t/2} = 1`. -/
theorem exp_half_mul (t : ℝ) : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
  rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]

/-- `t e^{−t} ≤ 2e^{−t/2}` (`t ≤ 2(1 + t/2) ≤ 2e^{t/2}`). -/
theorem t_exp_le (t : ℝ) : t * Real.exp (-t) ≤ 2 * Real.exp (-t / 2) := by
  have h1 : t ≤ 2 * Real.exp (t / 2) := by
    linarith [Real.add_one_le_exp (t / 2), Real.exp_pos (t / 2)]
  have hE : 0 < Real.exp (-t / 2) := Real.exp_pos _
  calc t * Real.exp (-t) = t * Real.exp (-t / 2) * Real.exp (-t / 2) := by
        rw [exp_neg_split]; ring
    _ ≤ 2 * Real.exp (t / 2) * Real.exp (-t / 2) * Real.exp (-t / 2) := by
        have h2 := mul_le_mul_of_nonneg_right h1 hE.le
        exact mul_le_mul_of_nonneg_right h2 hE.le
    _ = 2 * (Real.exp (t / 2) * Real.exp (-t / 2)) * Real.exp (-t / 2) := by ring
    _ = 2 * Real.exp (-t / 2) := by rw [exp_half_mul]; ring

/-- `t² e^{−t} ≤ 16e^{−t/2}` for `t ≥ 0` (`t ≤ 4e^{t/4}`). -/
theorem t2_exp_le (t : ℝ) (ht : 0 ≤ t) : t ^ 2 * Real.exp (-t) ≤ 16 * Real.exp (-t / 2) := by
  have h1 : t ≤ 4 * Real.exp (t / 4) := by
    linarith [Real.add_one_le_exp (t / 4), Real.exp_pos (t / 4)]
  have e0 : Real.exp (t / 4) * Real.exp (t / 4) = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : t ^ 2 ≤ 16 * Real.exp (t / 2) :=
    calc t ^ 2 ≤ (4 * Real.exp (t / 4)) ^ 2 := pow_le_pow_left₀ ht h1 2
      _ = 16 * (Real.exp (t / 4) * Real.exp (t / 4)) := by ring
      _ = 16 * Real.exp (t / 2) := by rw [e0]
  have hE : 0 < Real.exp (-t / 2) := Real.exp_pos _
  calc t ^ 2 * Real.exp (-t) = t ^ 2 * Real.exp (-t / 2) * Real.exp (-t / 2) := by
        rw [exp_neg_split]; ring
    _ ≤ 16 * Real.exp (t / 2) * Real.exp (-t / 2) * Real.exp (-t / 2) := by
        have h3 := mul_le_mul_of_nonneg_right h2 hE.le
        exact mul_le_mul_of_nonneg_right h3 hE.le
    _ = 16 * (Real.exp (t / 2) * Real.exp (-t / 2)) * Real.exp (-t / 2) := by ring
    _ = 16 * Real.exp (-t / 2) := by rw [exp_half_mul]; ring

/-- **The majorant of one term of `sAbs`**: `Λ(n)|η₊(n/x)| ≤ 3(2 log x + 16)·r^n`,
`r = e^{−1/2x}`, for `x ≥ 1`. -/
theorem term_le (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    Λ n * |HW.etaPlus ((n : ℝ) / x)| ≤
      3 * (2 * Real.log x + 16) * Real.exp (-1 / (2 * x)) ^ n := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hr : Real.exp (-1 / (2 * x)) ^ n = Real.exp (-((n : ℝ) / x) / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hr]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [ArithmeticFunction.map_zero, zero_mul]
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · have ht0 : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hn) hx0
    have hη := etaPlus_le _ ht0.le
    have hΛ : Λ n ≤ Real.log n := vonMangoldt_le_log
    have hlogn : Real.log n ≤ Real.log x + (n : ℝ) / x := by
      have e : (n : ℝ) = x * ((n : ℝ) / x) := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hx0.ne']
      have hl := Real.log_le_sub_one_of_pos ht0
      calc Real.log n = Real.log (x * ((n : ℝ) / x)) := by rw [← e]
        _ = Real.log x + Real.log ((n : ℝ) / x) := Real.log_mul hx0.ne' ht0.ne'
        _ ≤ Real.log x + (n : ℝ) / x := by linarith
    have h1 := t_exp_le ((n : ℝ) / x)
    have h2 := t2_exp_le _ ht0.le
    have h3 : Real.log x * ((n : ℝ) / x * Real.exp (-((n : ℝ) / x))) ≤
        Real.log x * (2 * Real.exp (-((n : ℝ) / x) / 2)) :=
      mul_le_mul_of_nonneg_left h1 hL
    calc Λ n * |HW.etaPlus ((n : ℝ) / x)|
        ≤ (Real.log x + (n : ℝ) / x) * (3 * ((n : ℝ) / x * Real.exp (-((n : ℝ) / x)))) :=
          mul_le_mul (hΛ.trans hlogn) hη (abs_nonneg _) (by linarith)
      _ = 3 * (Real.log x * ((n : ℝ) / x * Real.exp (-((n : ℝ) / x))) +
            ((n : ℝ) / x) ^ 2 * Real.exp (-((n : ℝ) / x))) := by ring
      _ ≤ 3 * (2 * Real.log x + 16) * Real.exp (-((n : ℝ) / x) / 2) := by linarith

/-- `r = e^{−1/2x} < 1`. -/
theorem r_lt_one (x : ℝ) (hx : 0 < x) : Real.exp (-1 / (2 * x)) < 1 :=
  (Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) (by linarith))).trans_eq
    Real.exp_zero

/-- **Summability**: `n ↦ Λ(n)|η₊(n/x)|` is summable for `x ≥ 1` (geometric majorant). -/
theorem summable_helf (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun n : ℕ => Λ n * |HW.etaPlus ((n : ℝ) / x)|) :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)) (term_le x hx)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le (r_lt_one x (by linarith))).mul_left _)

/-- `(1 − e^{−1/2x})⁻¹ ≤ 2x + 1`: `e^{−u}(1 + u) ≤ 1` at `u = 1/2x`. -/
theorem geom_le (x : ℝ) (hx : 0 < x) : (1 - Real.exp (-1 / (2 * x)))⁻¹ ≤ 2 * x + 1 := by
  have hr1 := r_lt_one x hx
  have hr0 : 0 < Real.exp (-1 / (2 * x)) := Real.exp_pos _
  have hru : Real.exp (-1 / (2 * x)) * Real.exp (1 / (2 * x)) = 1 := by
    rw [← Real.exp_add, show -1 / (2 * x) + 1 / (2 * x) = 0 by ring, Real.exp_zero]
  have hle : Real.exp (-1 / (2 * x)) * (1 / (2 * x) + 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hr0.le).trans hru.le
  have hxu : 2 * x * (1 / (2 * x)) = 1 := by field_simp
  generalize Real.exp (-1 / (2 * x)) = r at hr1 hr0 hle ⊢
  generalize 1 / (2 * x) = u at hle hxu
  have hk : r * (2 * x + 1) ≤ 2 * x := by
    have h2 := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 2 * x)
    have e : 2 * x * (r * (u + 1)) = r * (2 * x + 1) := by linear_combination r * hxu
    linarith
  have h1r : 0 < 1 - r := by linarith
  rw [← one_div, div_le_iff₀ h1r]
  linarith

/-- `sAbs η₊ ≥ 0`. -/
theorem sAbs_nonneg (x : ℝ) : 0 ≤ DS.sAbs HW.etaPlus x :=
  tsum_nonneg fun _ => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)

/-- **`sAbs η₊ ≤ 3(2 log x + 16)(2x + 1)`** for `x ≥ 1`. -/
theorem sAbs_le (x : ℝ) (hx : 1 ≤ x) :
    DS.sAbs HW.etaPlus x ≤ 3 * (2 * Real.log x + 16) * (2 * x + 1) := by
  have hx0 : 0 < x := by linarith
  have hC : 0 ≤ 3 * (2 * Real.log x + 16) := by linarith [Real.log_nonneg hx]
  have hr1 := r_lt_one x hx0
  have hr0 : 0 ≤ Real.exp (-1 / (2 * x)) := (Real.exp_pos _).le
  have hle : DS.sAbs HW.etaPlus x ≤
      ∑' n : ℕ, 3 * (2 * Real.log x + 16) * Real.exp (-1 / (2 * x)) ^ n :=
    (summable_helf x hx).tsum_le_tsum (term_le x hx)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left _)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (geom_le x hx0) hC)

/-! ## Step 3: `bQ`, uniformly in `x` -/

/-- **The telescoping step**: for `s ≥ 0`, `P ≥ 2`, `s e^{−s} ≤ 4(F(sP) − F(s))`,
`F(s) = s/(1+s)`. Via `F(sP) − F(s) ≥ s/((1+2s)(1+s))` and `(1+2s)(1+s) ≤ 4e^s`. -/
theorem tele (s P : ℝ) (hs : 0 ≤ s) (hP : 2 ≤ P) :
    s * Real.exp (-s) ≤ 4 * (s * P / (1 + s * P) - s / (1 + s)) := by
  have hE0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hq := Real.quadratic_le_exp_of_nonneg hs
  have hEE : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add, show -s + s = 0 by ring, Real.exp_zero]
  have hE : Real.exp (-s) * (1 + s + s ^ 2 / 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hq hE0.le).trans hEE.le
  have h1 : 0 < 1 + s := by linarith
  have h2 : 0 < 1 + s * P := by
    have := mul_nonneg hs (by linarith : (0 : ℝ) ≤ P)
    linarith
  have h3 : 0 < 1 + 2 * s := by linarith
  have ediff : s * P / (1 + s * P) - s / (1 + s) = s * (P - 1) / ((1 + s * P) * (1 + s)) := by
    rw [div_sub_div _ _ h2.ne' h1.ne']
    congr 1
    ring
  rw [ediff]
  have hED : Real.exp (-s) * ((1 + 2 * s) * (1 + s)) ≤ 4 := by
    nlinarith [mul_nonneg hE0.le (by linarith : (0 : ℝ) ≤ 3 + s)]
  have hA : s * Real.exp (-s) ≤ 4 * s / ((1 + 2 * s) * (1 + s)) := by
    rw [le_div_iff₀ (mul_pos h3 h1)]
    nlinarith [mul_le_mul_of_nonneg_left hED hs]
  have hB : 4 * s / ((1 + 2 * s) * (1 + s)) ≤ 4 * (s * (P - 1) / ((1 + s * P) * (1 + s))) := by
    rw [mul_div_assoc', div_le_div_iff₀ (mul_pos h3 h1) (mul_pos h2 h1)]
    nlinarith [mul_nonneg (mul_nonneg hs (sq_nonneg (1 + s))) (by linarith : (0 : ℝ) ≤ P - 2)]
  exact hA.trans hB

/-- **The prime-power sum, uniformly in `x`**: `∑_{k ≥ 0} |η₊(p^{k+1}/x)| ≤ 12` for `p ≥ 2`,
`x > 0` (`3·4`; telescoping of `tele` along `t_{k+1} = p·t_k`). -/
theorem sum_pow_le (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx : 0 < x) :
    ∑' k : ℕ, |HW.etaPlus ((p : ℝ) ^ (k + 1) / x)| ≤ 12 := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have ht0 : ∀ k : ℕ, 0 ≤ (p : ℝ) ^ (k + 1) / x := fun k =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg p) _) hx.le
  have hterm : ∀ k : ℕ, |HW.etaPlus ((p : ℝ) ^ (k + 1) / x)| ≤
      12 * ((p : ℝ) ^ (k + 1 + 1) / x / (1 + (p : ℝ) ^ (k + 1 + 1) / x) -
        (p : ℝ) ^ (k + 1) / x / (1 + (p : ℝ) ^ (k + 1) / x)) := by
    intro k
    have e : (p : ℝ) ^ (k + 1 + 1) / x = (p : ℝ) ^ (k + 1) / x * p := by ring
    rw [e]
    have h1 := etaPlus_le _ (ht0 k)
    have h2 := tele _ _ (ht0 k) hP
    linarith
  refine Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) fun N => ?_
  have hN := ht0 N
  have hF1 : (p : ℝ) ^ (N + 1) / x / (1 + (p : ℝ) ^ (N + 1) / x) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hF0 : 0 ≤ (p : ℝ) ^ (0 + 1) / x / (1 + (p : ℝ) ^ (0 + 1) / x) :=
    div_nonneg (ht0 0) (by linarith [ht0 0])
  calc ∑ k ∈ range N, |HW.etaPlus ((p : ℝ) ^ (k + 1) / x)|
      ≤ ∑ k ∈ range N, 12 * ((p : ℝ) ^ (k + 1 + 1) / x / (1 + (p : ℝ) ^ (k + 1 + 1) / x) -
          (p : ℝ) ^ (k + 1) / x / (1 + (p : ℝ) ^ (k + 1) / x)) := sum_le_sum fun k _ => hterm k
    _ = 12 * ((p : ℝ) ^ (N + 1) / x / (1 + (p : ℝ) ^ (N + 1) / x) -
          (p : ℝ) ^ (0 + 1) / x / (1 + (p : ℝ) ^ (0 + 1) / x)) := by
        rw [← mul_sum]
        congr 1
        exact sum_range_sub (fun k => (p : ℝ) ^ (k + 1) / x / (1 + (p : ℝ) ^ (k + 1) / x)) N
    _ ≤ 12 := by linarith

/-- `log q ≤ 13` for `1 ≤ q ≤ 3·10⁵` (`3·10⁵ ≤ 2.7¹³ ≤ e¹³`). -/
theorem log_q_le (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 300000) : Real.log q ≤ 13 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [Real.log_le_iff_le_exp hq0]
  have h1 : (2.7 : ℝ) ^ 13 ≤ Real.exp 1 ^ 13 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 13
  rw [← Real.exp_nat_mul, show ((13 : ℕ) : ℝ) * 1 = 13 by norm_num] at h1
  have h2 : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have h3 : (300000 : ℝ) ≤ 2.7 ^ 13 := by norm_num
  linarith

/-- `bQ η₊ ≥ 0`. -/
theorem bQ_nonneg (x : ℝ) (q : ℕ) : 0 ≤ DS.bQ HW.etaPlus x q :=
  mul_nonneg (by norm_num) (sum_nonneg fun p _ =>
    mul_nonneg (Real.log_natCast_nonneg p) (tsum_nonneg fun _ => abs_nonneg _))

/-- **`bQ η₊ ≤ 312`** for `1 ≤ q ≤ 3·10⁵`, uniformly in `x > 0`:
`2·∑_{p | q} log p·12 ≤ 24·∑_{d | q} Λ(d) = 24 log q ≤ 24·13`. -/
theorem bQ_le (x : ℝ) (hx : 0 < x) (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    DS.bQ HW.etaPlus x q ≤ 312 := by
  unfold DS.bQ
  have hs : ∀ p ∈ q.primeFactors,
      Real.log p * ∑' k : ℕ, |HW.etaPlus ((p : ℝ) ^ (k + 1) / x)| ≤ 12 * Λ p := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    rw [vonMangoldt_apply_prime hpp, mul_comm 12]
    exact mul_le_mul_of_nonneg_left (sum_pow_le p hpp.two_le x hx) (Real.log_natCast_nonneg p)
  have hsub : ∑ p ∈ q.primeFactors, Λ p ≤ ∑ d ∈ q.divisors, Λ d :=
    sum_le_sum_of_subset_of_nonneg
      (fun p hp => Nat.mem_divisors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).2.1, (Nat.mem_primeFactors.mp hp).2.2⟩)
      (fun _ _ _ => vonMangoldt_nonneg)
  rw [vonMangoldt_sum] at hsub
  have hlog := log_q_le q hq1 hq
  have hsum := sum_le_sum hs
  rw [← mul_sum] at hsum
  linarith

/-! ## Step 4: `kArc` and `kAgg` -/

/-- **`kArc η₊ q ≤ q·312·(2S + 312)`** whenever `sAbs η₊ x ≤ S`, `1 ≤ q ≤ 3·10⁵` (`φ(q) ≤ q`). -/
theorem kArc_le (x S : ℝ) (hx : 0 < x) (hS : DS.sAbs HW.etaPlus x ≤ S) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : q ≤ 300000) : DS.kArc HW.etaPlus x q ≤ q * (312 * (2 * S + 312)) := by
  unfold DS.kArc
  have hb := bQ_le x hx q hq1 hq
  have hb0 := bQ_nonneg x q
  have hs0 := sAbs_nonneg x
  have hφ : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  calc (Nat.totient q : ℝ) * DS.bQ HW.etaPlus x q *
        (2 * DS.sAbs HW.etaPlus x + DS.bQ HW.etaPlus x q)
      ≤ q * 312 * (2 * S + 312) :=
        mul_le_mul (mul_le_mul hφ hb hb0 (Nat.cast_nonneg _)) (by linarith) (by linarith)
          (by positivity)
    _ = q * (312 * (2 * S + 312)) := by ring

/-- `#odd moduli ≤ 1.5·10⁵`. -/
theorem card_odd : (DS.oddQ.card : ℝ) ≤ 150000 := by
  have h : DS.oddQ.card ≤ 150000 := by
    unfold DS.oddQ
    exact (card_filter_le _ _).trans (le_of_eq (by simp))
  exact_mod_cast h

/-- `#even moduli ≤ 3·10⁵`. -/
theorem card_even : (DS.evenQ.card : ℝ) ≤ 300000 := by
  have h : DS.evenQ.card ≤ 300000 := by
    unfold DS.evenQ
    exact (card_filter_le _ _).trans (le_of_eq (by simp))
  exact_mod_cast h

/-- **`kAgg η₊ ≤ 9·10¹¹·312·(2S + 312)/x²`** whenever `0 ≤ S`, `sAbs η₊ x ≤ S`: the arc length
`δ₀r/q` cancels against `φ(q) ≤ q`, leaving `1.2·10⁶·1.5·10⁵ + 2.4·10⁶·3·10⁵ = 9·10¹¹`. -/
theorem kAgg_le (x S : ℝ) (hx : 0 < x) (hS0 : 0 ≤ S) (hS : DS.sAbs HW.etaPlus x ≤ S) :
    DS.kAgg HW.etaPlus x ≤ 900000000000 * (312 * (2 * S + 312)) / x ^ 2 := by
  unfold DS.kAgg
  have hB0 : 0 ≤ 312 * (2 * S + 312) := by linarith
  have ho : ∑ q ∈ DS.oddQ, 1200000 / (q : ℝ) * DS.kArc HW.etaPlus x q ≤
      150000 * (1200000 * (312 * (2 * S + 312))) := by
    have h1 : ∀ q ∈ DS.oddQ, 1200000 / (q : ℝ) * DS.kArc HW.etaPlus x q ≤
        1200000 * (312 * (2 * S + 312)) := by
      intro q hq
      simp only [DS.oddQ, mem_filter, mem_Icc] at hq
      have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
      have hk := kArc_le x S hx hS q hq.1.1 (by omega)
      calc 1200000 / (q : ℝ) * DS.kArc HW.etaPlus x q
          ≤ 1200000 / (q : ℝ) * (q * (312 * (2 * S + 312))) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 1200000 * (312 * (2 * S + 312)) := by
            rw [div_mul_eq_mul_div, div_eq_iff hq0.ne']
            ring
    calc ∑ q ∈ DS.oddQ, 1200000 / (q : ℝ) * DS.kArc HW.etaPlus x q
        ≤ ∑ q ∈ DS.oddQ, 1200000 * (312 * (2 * S + 312)) := sum_le_sum h1
      _ = (DS.oddQ.card : ℝ) * (1200000 * (312 * (2 * S + 312))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 150000 * (1200000 * (312 * (2 * S + 312))) :=
          mul_le_mul_of_nonneg_right card_odd (by linarith)
  have he : ∑ q ∈ DS.evenQ, 2400000 / (q : ℝ) * DS.kArc HW.etaPlus x q ≤
      300000 * (2400000 * (312 * (2 * S + 312))) := by
    have h1 : ∀ q ∈ DS.evenQ, 2400000 / (q : ℝ) * DS.kArc HW.etaPlus x q ≤
        2400000 * (312 * (2 * S + 312)) := by
      intro q hq
      simp only [DS.evenQ, mem_filter, mem_Icc] at hq
      have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
      have hk := kArc_le x S hx hS q hq.1.1 hq.1.2
      calc 2400000 / (q : ℝ) * DS.kArc HW.etaPlus x q
          ≤ 2400000 / (q : ℝ) * (q * (312 * (2 * S + 312))) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 2400000 * (312 * (2 * S + 312)) := by
            rw [div_mul_eq_mul_div, div_eq_iff hq0.ne']
            ring
    calc ∑ q ∈ DS.evenQ, 2400000 / (q : ℝ) * DS.kArc HW.etaPlus x q
        ≤ ∑ q ∈ DS.evenQ, 2400000 * (312 * (2 * S + 312)) := sum_le_sum h1
      _ = (DS.evenQ.card : ℝ) * (2400000 * (312 * (2 * S + 312))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 300000 * (2400000 * (312 * (2 * S + 312))) :=
          mul_le_mul_of_nonneg_right card_even (by linarith)
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg x)
  linarith

/-! ## Step 5: the close -/

/-- `log(4.9·10²⁶) ≤ 62` (`4.9·10²⁶ ≤ 2.7⁶² ≤ e⁶²`; truth `61.456`). -/
theorem log_X0_le : Real.log (49 * 10 ^ 25) ≤ 62 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : (2.7 : ℝ) ^ 62 ≤ Real.exp 1 ^ 62 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 62
  rw [← Real.exp_nat_mul, show ((62 : ℕ) : ℝ) * 1 = 62 by norm_num] at h1
  have h2 : (49 * 10 ^ 25 : ℝ) ≤ 2.7 ^ 62 := by norm_num
  linarith

/-- `log x ≤ x/X₀ + 61` for `x > 0` (`log(x/X₀) ≤ x/X₀ − 1`, `log X₀ ≤ 62`). -/
theorem log_le_lin (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / (49 * 10 ^ 25) + 61 := by
  have hX : (0 : ℝ) < 49 * 10 ^ 25 := by norm_num
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx hX)
  rw [Real.log_div hx.ne' hX.ne'] at h1
  have h2 := log_X0_le
  -- `linarith` fails on the literal inside `log` unless it is first generalized to a variable
  generalize Real.log (49 * 10 ^ 25 : ℝ) = L at h1 h2
  linarith

/-- **`DS.KSmall η₊` HOLDS**: at every `x ≥ 4.9·10²⁶`, `∑ Λ(n)|η₊(n/x)|` converges and
`kAgg η₊ x ≤ 9.63·10⁻¹⁰ ≤ 10⁻⁶`. -/
theorem ksmall_helf : DS.KSmall HW.etaPlus := by
  intro x hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := by linarith
  refine ⟨summable_helf x hx1, ?_⟩
  have hL := log_le_lin x hx0
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hS0 : 0 ≤ 3 * (2 * Real.log x + 16) * (2 * x + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hk := kAgg_le x _ hx0 hS0 (sAbs_le x hx1)
  have hS : 3 * (2 * Real.log x + 16) * (2 * x + 1) ≤
      3 * (2 * (x / (49 * 10 ^ 25) + 61) + 16) * (2 * x + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hxx : 49 * 10 ^ 25 * x ≤ x ^ 2 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hx hx0.le
  have hxx2 : (49 * 10 ^ 25 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  refine hk.trans ?_
  rw [div_le_iff₀ (pow_pos hx0 2)]
  linarith

end Principia.Common.TernaryGoldbach.KS
