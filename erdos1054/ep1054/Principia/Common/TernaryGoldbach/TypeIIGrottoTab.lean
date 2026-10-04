/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIMenson2C

set_option autoImplicit false

/-!
# `M2H.GrottoTab` PROVED — `eq:grotto` (`v = 2`) equals `G₂(S) = K₁(⌊S⌋) + K₂(⌊S⌋)/S` on `[1, 16)`

`M2H.GrottoTab` asks that `HC.cortoLHS 2 S = ∑_{s ≤ S odd} (1/s)∫_{1/2}^{1} g₂(uS/s) du` be at
most `M2H.G2tab S` for `1 ≤ S < 16` (`typeII.tex` 680-707, 783-790: "`K_{v,1}(n)`, `K_{v,2}(n)`
can be computed explicitly"). It is proved here as an EQUALITY, from the definitions alone:

```
 stepInt / int_step_ab  ∫_a^b c(⌊t⌋) dt = Φ_c(b) − Φ_c(a),  Φ_c(y) = ∑_{k<⌊y⌋} c k + c⌊y⌋(y − ⌊y⌋)
 gQ_eq / gY_tab         g₂(k) for k ≤ 15, the double sum of HC.gYutto 2 evaluated in the kernel
 term_eq                (1/s)∫_{1/2}^{1} g₂(uS/s) du = Q(n, s) + P(n, s)/S on [n, n+1)
                        (u ↦ (S/s)u, then Φ at S/s and S/2s, ⌊S/s⌋ = n/s)
 tab_q                  ∑_{s ≤ n odd} Q = K₁(n), ∑ P = K₂(n), n = 1..15   (decide +kernel)
 grottoTab_holds        M2H.GrottoTab                                               PROVED
```

**No computation is cited and none of ours stands in for a proof step**: the only arithmetic is
the kernel's evaluation of finite rational sums (`decide +kernel`) — `g₂(k)` from its defining
double sum over `μ` and `σ`, and the fifteen `K` values from the exact pieces. The `K₁`, `K₂`
tables of `M2H` (computed in rationals from `eq:greco`, `scratchpad/t2s/ktab.py`) are confirmed
exactly; nothing in them changed.
-/

namespace Principia.Common.TernaryGoldbach.M2G

open MeasureTheory Set
open Principia.Common.TernaryGoldbach.M2H

/-! ## (1) Integrals of step functions `t ↦ c ⌊t⌋₊` -/

/-- `Φ_c(y) = ∑_{k < ⌊y⌋} c(k) + c(⌊y⌋)(y − ⌊y⌋)`, the primitive of `t ↦ c ⌊t⌋₊` from `0`. -/
noncomputable def stepInt (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  (∑ k ∈ Finset.range ⌊y⌋₊, c k) + c ⌊y⌋₊ * (y - ⌊y⌋₊)

theorem meas_step (c : ℕ → ℝ) : Measurable fun t : ℝ => c ⌊t⌋₊ :=
  (measurable_from_nat (f := c)).comp Nat.measurable_floor

theorem ii_step (c : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => c ⌊t⌋₊) volume a b := by
  refine ii_of_bdd _ (meas_step c) (∑ k ∈ Finset.range (⌊b⌋₊ + 1), |c k|) a b hab ?_
  intro t ht
  have hfl : ⌊t⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono ht.2
  exact Finset.single_le_sum (f := fun k => |c k|) (fun k _ => abs_nonneg (c k))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hfl))

theorem int_unit (c : ℕ → ℝ) (m : ℕ) (y : ℝ) (h1 : (m : ℝ) ≤ y) (h2 : y ≤ m + 1) :
    ∫ t in (m : ℝ)..y, c ⌊t⌋₊ = c m * (y - m) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le h1 (g := fun _ => c m)]
  · simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  · intro t ht
    simp only
    rw [floor_eq m t ht.1.le (by linarith [ht.2])]

theorem int_from0 (c : ℕ → ℝ) (m : ℕ) : ∀ y : ℝ, (m : ℝ) ≤ y → y ≤ m + 1 →
    ∫ t in (0 : ℝ)..y, c ⌊t⌋₊ = (∑ k ∈ Finset.range m, c k) + c m * (y - m) := by
  induction m with
  | zero =>
    intro y h1 h2
    have h := int_unit c 0 y h1 h2
    simp only [Nat.cast_zero] at h
    simp [h]
  | succ m ih =>
    intro y h1 h2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hc] at h1 h2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ) + 1)
      (ii_step c 0 _ (by linarith)) (ii_step c _ y h1)]
    have hu := int_unit c (m + 1) y (by rw [hc]; exact h1) (by rw [hc]; exact h2)
    rw [hc] at hu
    rw [ih ((m : ℝ) + 1) (by linarith) le_rfl, hu, Finset.sum_range_succ, hc]
    ring

theorem int_step (c : ℕ → ℝ) (y : ℝ) (hy : 0 ≤ y) :
    ∫ t in (0 : ℝ)..y, c ⌊t⌋₊ = stepInt c y :=
  int_from0 c ⌊y⌋₊ y (Nat.floor_le hy) (Nat.lt_floor_add_one y).le

theorem int_step_ab (c : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, c ⌊t⌋₊ = stepInt c b - stepInt c a := by
  rw [← intervalIntegral.integral_interval_sub_left (ii_step c 0 b (by linarith))
    (ii_step c 0 a ha), int_step c b (by linarith), int_step c a ha]

/-! ## (2) `g₂` at the integers `0, …, 15` -/

/-- `g₂(k)` for `k ≤ 15` (`lem:yutto`'s `g_v`, `v = 2`), exact. -/
def gq : ℕ → ℚ
  | 1 => 1 | 2 => 1 | 3 => 1 / 2 | 4 => 1 / 2 | 5 => 1 / 4 | 6 => 1 / 4 | 7 => 5 / 48
  | 8 => 5 / 48 | 9 => 5 / 48 | 10 => 5 / 48 | 11 => 1 / 36 | 12 => 1 / 36
  | 13 => -13 / 504 | 14 => -13 / 504 | 15 => 23 / 672 | _ => 0

/-- `g₂` at an integer, in `ℚ` (the same double sum as `HC.gYutto 2`). -/
def gQ (n : ℕ) : ℚ :=
  ∑ r1 ∈ Finset.Icc 1 n, ∑ r2 ∈ Finset.Icc 1 n,
    if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
      ((ArithmeticFunction.moebius r1 : ℤ) : ℚ) * ((ArithmeticFunction.moebius r2 : ℤ) : ℚ) /
        ((ArithmeticFunction.sigma 1 r1 : ℚ) * (ArithmeticFunction.sigma 1 r2 : ℚ))
    else 0

theorem gQ_eq : ∀ k, k < 16 → gQ k = gq k := by decide +kernel

theorem gY_cast (k : ℕ) : HC.gYutto 2 (k : ℝ) = ((gQ k : ℚ) : ℝ) := by
  simp only [HC.gYutto, gQ, Nat.floor_natCast, Rat.cast_sum]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
  split_ifs <;> push_cast <;> rfl

theorem gY_tab (k : ℕ) (hk : k ≤ 15) : HC.gYutto 2 (k : ℝ) = ((gq k : ℚ) : ℝ) := by
  rw [gY_cast, gQ_eq k (by omega)]

theorem gY_floor (x : ℝ) : HC.gYutto 2 x = HC.gYutto 2 (⌊x⌋₊ : ℝ) := by
  simp only [HC.gYutto, Nat.floor_natCast]

/-! ## (3) One summand of `eq:grotto` on `[n, n+1)` -/

/-- The odd `s ≤ n`. -/
def oddS (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun s => Nat.Coprime s 2)

/-- The constant part of `Φ(S/s) − Φ(S/2s)` on `[n, n+1)`. -/
def Pq (n s : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n / s), gq k) - gq (n / s) * ((n / s : ℕ) : ℚ) -
    ((∑ k ∈ Finset.range (n / (2 * s)), gq k) - gq (n / (2 * s)) * ((n / (2 * s) : ℕ) : ℚ))

/-- The coefficient of `S` in `Φ(S/s) − Φ(S/2s)` on `[n, n+1)`. -/
def Qq (n s : ℕ) : ℚ := gq (n / s) / (s : ℚ) - gq (n / (2 * s)) / ((2 * s : ℕ) : ℚ)

/-- `K_{2,1}`, in `ℚ`. -/
def K1q : ℕ → ℚ
  | 1 => 1 | 2 => 1 / 2 | 3 => 1 / 3 | 4 => 1 / 3 | 5 => 17 / 60 | 6 => 11 / 30
  | 7 => 611 / 1680 | 8 => 611 / 1680 | 9 => 1553 / 5040 | 10 => 1679 / 5040
  | 11 => 9637 / 27720 | 12 => 9637 / 27720 | 13 => 16712 / 45045 | 14 => 536929 / 1441440
  | 15 => 113819 / 360360 | _ => 0

/-- `K_{2,2}`, in `ℚ`. -/
def K2q : ℕ → ℚ
  | 1 => -1 | 2 => 0 | 3 => 1 / 2 | 4 => 1 / 2 | 5 => 3 / 4 | 6 => 1 / 4 | 7 => 13 / 48
  | 8 => 13 / 48 | 9 => 37 / 48 | 10 => 25 / 48 | 11 => 13 / 36 | 12 => 13 / 36
  | 13 => 29 / 504 | 14 => 37 / 1008 | 15 => 1787 / 2016 | _ => 0

/-- **The table**: summing the pieces over odd `s ≤ n` gives `K₁(n)`, `K₂(n)`. Kernel-checked. -/
theorem tab_q : ∀ n, n < 16 → 1 ≤ n →
    ∑ s ∈ oddS n, Qq n s = K1q n ∧ ∑ s ∈ oddS n, Pq n s = K2q n := by decide +kernel

theorem k_cast (n : ℕ) (h1 : 1 ≤ n) (h15 : n ≤ 15) :
    ((K1q n : ℚ) : ℝ) = K1t n ∧ ((K2q n : ℚ) : ℝ) = K2t n := by
  interval_cases n <;> norm_num [K1q, K2q, K1t, K2t]

theorem sum_cast (f : ℕ) (hf : f ≤ 15) :
    ∑ k ∈ Finset.range f, HC.gYutto 2 (k : ℝ) = ((∑ k ∈ Finset.range f, gq k : ℚ) : ℝ) := by
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun k hk => gY_tab k (by have := Finset.mem_range.mp hk; omega)

/-- **One summand**, `1 ≤ s ≤ n ≤ 15`, `S ∈ [n, n+1)`. -/
theorem term_eq (n s : ℕ) (hn : n ≤ 15) (hs1 : 1 ≤ s) (S : ℝ) (hS1 : (n : ℝ) ≤ S)
    (hS2 : S < n + 1) (hS0 : 0 < S) :
    1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) =
      ((Qq n s : ℚ) : ℝ) + ((Pq n s : ℚ) : ℝ) / S := by
  set gc : ℕ → ℝ := fun k => HC.gYutto 2 (k : ℝ) with hgc
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hne : S / s ≠ 0 := (div_pos hS0 hs0).ne'
  have hfun : ∀ u : ℝ, HC.gYutto 2 (u * S / s) = gc ⌊S / s * u⌋₊ := fun u => by
    simp only [hgc]
    rw [gY_floor]
    ring_nf
  simp_rw [hfun]
  have key := intervalIntegral.integral_comp_mul_left (f := fun t => gc ⌊t⌋₊) (a := 1 / 2)
    (b := 1) hne
  rw [key, smul_eq_mul, int_step_ab gc _ _ (by positivity)
    (by apply mul_le_mul_of_nonneg_left (by norm_num) (by positivity))]
  have hfl : ⌊S⌋₊ = n := floor_eq n S hS1 hS2
  rw [show S / s * 1 = S / ((s : ℕ) : ℝ) by ring,
    show S / s * (1 / 2) = S / ((2 * s : ℕ) : ℝ) by push_cast; ring]
  simp only [stepInt, Nat.floor_div_natCast, hfl]
  have hd1 : n / s ≤ 15 := le_trans (Nat.div_le_self n s) hn
  have hd2 : n / (2 * s) ≤ 15 := le_trans (Nat.div_le_self n _) hn
  simp only [hgc]
  rw [sum_cast _ hd1, sum_cast _ hd2, gY_tab _ hd1, gY_tab _ hd2]
  simp only [Pq, Qq]
  push_cast
  field_simp
  ring

/-! ## (4) `M2H.GrottoTab`, PROVED -/

/-- **`M2H.GrottoTab`, PROVED** — `eq:grotto` (`v = 2`) is at most `G₂(S) = K₁(⌊S⌋) + K₂(⌊S⌋)/S`
on `[1, 16)`; in fact equal. -/
theorem grottoTab_holds : GrottoTab := by
  intro S h1 h16
  obtain ⟨hn1, hn15, hl, hu⟩ := piece_of S h1 h16
  have hS0 : 0 < S := by linarith
  unfold HC.cortoLHS G2tab
  set n := ⌊S⌋₊ with hn
  have hsum : ∑ s ∈ (Finset.Icc 1 n).filter (fun s => Nat.Coprime s 2),
      1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) =
      ∑ s ∈ oddS n, (((Qq n s : ℚ) : ℝ) + ((Pq n s : ℚ) : ℝ) / S) :=
    Finset.sum_congr rfl fun s hs => term_eq n s hn15
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1 S hl hu hS0
  rw [hsum, Finset.sum_add_distrib, ← Finset.sum_div, ← Rat.cast_sum, ← Rat.cast_sum]
  obtain ⟨hQ, hP⟩ := tab_q n (by omega) hn1
  obtain ⟨hK1, hK2⟩ := k_cast n hn1 hn15
  rw [hQ, hP, hK1, hK2]

end Principia.Common.TernaryGoldbach.M2G
