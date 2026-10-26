/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #333222 — one Bernstein sign variation, hence a unique threshold

MathDB open problem #333222, on the one-stage-look-ahead stopping region of the Kurushima–Ano
best-choice problem.  With `H_m` the harmonic numbers and `n` stages to go, the expected advantage
of stopping is

  `G_n(x) = ∑_{j=0}^{n-1} (3 − 2 H_{n−1−j} + 2 H_j) x^j − 2n x^{n−1}`.

The record asserts **monotonicity of the stopping region**: `G_n(x) ≥ 0` implies `G_n(y) ≥ 0`
whenever `0 ≤ x ≤ y ≤ 1`.  That is `monotone_stopping`, the headline theorem here.  For `n ≥ 4` it
upgrades to a genuine threshold: `G_n(0) < 0 < G_n(1)`, so a root exists in `(0,1)`
(`exists_threshold`), and it is unique (`threshold_unique`).

## Why the Bernstein basis

In the power basis the coefficient sequence is `−…− +…+ −` — two sign changes — so Descartes gives
only "at most two roots" and the claim does not follow.  The source's move is to pass to the
Bernstein basis of degree `d = n−1`, where the coefficients become

  `β_k = n(3 − 2H_r)/(r+1)` for `k < d` (with `r = d−k`),   `β_d = n`,

which is `−…− 0 + +`: exactly one sign variation.

## What replaces Descartes' rule

Mathlib has no Descartes, and it is not needed.  Writing `u = (1−x)/x`, the Bernstein form gives
`G_n(x) = x^d · Φ_d(u)` with

  `Φ_d(u) = (d+1) + C(d+1,2) u + ∑_{r≥3} C(d+1,r+1)(3 − 2H_r) u^r`,

whose coefficients are `+ + 0 − … −`.  Dividing by `u²` makes **every** term decreasing in `u`, so
`Φ_d(u)/u²` is strictly decreasing — which is the whole content of the sign rule in this case, and
is proved here termwise, with no division: `Phi_key` shows

  `Φ_d(u) · v² ≤ Φ_d(v) · u²`  for `0 < v ≤ u`,

by checking three groups of terms separately.  Since `u = (1−x)/x` is decreasing in `x`, that is
exactly the monotonicity assertion.

## The identity the write-up delegates to two summation lemmas

The source obtains the Bernstein coefficients from the power coefficients via a hockey-stick
identity and a harmonic convolution.  Neither is needed.  After cancelling the `−2n x^d` term on
both sides, the Bernstein claim is equivalent to

  `∑_{r=0}^{d} C(d+1,r+1)(3 − 2H_r) x^{d−r}(1−x)^r = ∑_{j=0}^{d} (3 − 2H_{d−j} + 2H_j) x^j`,

whose `3`-part is the binomial theorem (`A_eq`) and whose harmonic part (`L_eq_Rp`) follows by
induction on `d`: both sides satisfy the **same recursion**, increasing by `P_{d+1}(x)` where

  `P_m(x) = ∑_{r=1}^{m} C(m,r) x^{m−r}(1−x)^r / r = ∑_{i=1}^{m} (x^{m−i} − x^m)/i`  (`P_eq`),

itself proved by induction from `P_{m+1} = x·P_m + (1 − x^{m+1})/(m+1)`.  Everything is elementary.

## Source corrections carried

The write-up reconciles two indexing typos in Kurushima–Ano (and the 2016 survey): the simplified
`U_n` prints `−n x^{n−1}` where the probability sum gives `−(n−2) x^{n−1}`, and the threshold
equation prints `H_{n−k−1}` where the defining integral gives `H_{n−k}`.  `G` above is the
corrected form; those corrections are inputs to the *modelling*, not to any proof here, and this
file proves the assertion about the corrected polynomial.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

namespace Principia.MathDB.P333222

open Finset

/-! ### Harmonic numbers -/

/-- `H m = 1 + 1/2 + ⋯ + 1/m`, with `H 0 = 0`. -/
noncomputable def H (m : ℕ) : ℝ := ∑ i ∈ range m, (1 : ℝ) / (i + 1)

theorem H_zero : H 0 = 0 := by simp [H]

theorem H_succ (m : ℕ) : H (m + 1) = H m + 1 / (m + 1) := by
  simp [H, Finset.sum_range_succ]

theorem H_one : H 1 = 1 := by norm_num [H, Finset.sum_range_succ]

theorem H_two : H 2 = 3 / 2 := by norm_num [H, Finset.sum_range_succ]

theorem H_three : H 3 = 11 / 6 := by norm_num [H, Finset.sum_range_succ]

theorem H_mono : Monotone H := by
  refine monotone_nat_of_le_succ fun m => ?_
  rw [H_succ]
  have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

/-- `H_r > 3/2` from `r = 3` on — the sign flip that creates the single Bernstein variation. -/
theorem H_gt {r : ℕ} (hr : 3 ≤ r) : (3 : ℝ) / 2 < H r := by
  have h := H_mono hr
  rw [H_three] at h
  linarith

/-! ### The three auxiliary sums -/

/-- `A m x = ∑_{q≤m} C(m+1,q+1) x^{m−q}(1−x)^q`. -/
noncomputable def A (m : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range (m + 1), ((m + 1).choose (q + 1) : ℝ) * x ^ (m - q) * (1 - x) ^ q

/-- `P m x = ∑_{r=1}^{m} C(m,r) x^{m−r}(1−x)^r / r`. -/
noncomputable def P (m : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range m, (m.choose (r + 1) : ℝ) * x ^ (m - (r + 1)) * (1 - x) ^ (r + 1) / (r + 1)

/-- `L d x = ∑_{r≤d} C(d+1,r+1) H_r x^{d−r}(1−x)^r`, the harmonic half of the Bernstein sum. -/
noncomputable def L (d : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range (d + 1), ((d + 1).choose (r + 1) : ℝ) * H r * x ^ (d - r) * (1 - x) ^ r

/-- `Rp d x = ∑_{j≤d} (H_{d−j} − H_j) x^j`, the harmonic half of the power sum. -/
noncomputable def Rp (d : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (d + 1), (H (d - j) - H j) * x ^ j

/-! ### `A` is the geometric sum -/

theorem A_mul (m : ℕ) (x : ℝ) : (1 - x) * A m x = 1 - x ^ (m + 1) := by
  have hbin : ((1 - x) + x) ^ (m + 1)
      = ∑ k ∈ range (m + 1 + 1), (1 - x) ^ k * x ^ (m + 1 - k) * ((m + 1).choose k : ℝ) :=
    add_pow (1 - x) x (m + 1)
  rw [sub_add_cancel, one_pow, Finset.sum_range_succ'] at hbin
  have hlast : ((1 : ℝ) - x) ^ 0 * x ^ (m + 1 - 0) * ((m + 1).choose 0 : ℝ) = x ^ (m + 1) := by
    simp
  have hmain : (∑ q ∈ range (m + 1),
      (1 - x) ^ (q + 1) * x ^ (m + 1 - (q + 1)) * ((m + 1).choose (q + 1) : ℝ))
      = (1 - x) * A m x := by
    rw [A, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hidx : m + 1 - (q + 1) = m - q := by omega
    rw [hidx]
    ring
  rw [hmain, hlast] at hbin
  linarith

theorem A_eq (m : ℕ) (x : ℝ) : A m x = ∑ j ∈ range (m + 1), x ^ j := by
  rcases eq_or_ne x 1 with rfl | hx
  · have hA : A m 1 = ((m : ℝ) + 1) := by
      rw [A]
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos m))
        (fun b _ hb => by simp [zero_pow hb])]
      simp
    rw [hA]
    simp
  · have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hgeom : (1 - x) * ∑ j ∈ range (m + 1), x ^ j = 1 - x ^ (m + 1) := by
      have h := geom_sum_mul x (m + 1)
      have hrw : (1 - x) * ∑ j ∈ range (m + 1), x ^ j
          = -((∑ j ∈ range (m + 1), x ^ j) * (x - 1)) := by ring
      rw [hrw, h]
      ring
    exact mul_left_cancel₀ h1 ((A_mul m x).trans hgeom.symm)

/-! ### The `P` identity -/

theorem P_zero (x : ℝ) : P 0 x = 0 := by simp [P]

/-- `P_{m+1} = x · P_m + (1 − x^{m+1})/(m+1)`.  Pascal splits the sum; the second half collapses
through `A_mul`. -/
theorem P_rec (m : ℕ) (x : ℝ) : P (m + 1) x = x * P m x + (1 - x ^ (m + 1)) / ((m : ℝ) + 1) := by
  have hpascal : ∀ r : ℕ, ((m + 1).choose (r + 1) : ℝ)
      = (m.choose (r + 1) : ℝ) + (m.choose r : ℝ) := by
    intro r
    rw [Nat.choose_succ_succ m r]
    push_cast
    ring
  have hsplit : P (m + 1) x
      = (∑ r ∈ range (m + 1), (m.choose (r + 1) : ℝ) * x ^ (m - r) * (1 - x) ^ (r + 1) / (r + 1))
        + ∑ r ∈ range (m + 1), (m.choose r : ℝ) * x ^ (m - r) * (1 - x) ^ (r + 1) / (r + 1) := by
    rw [P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hidx : m + 1 - (r + 1) = m - r := by omega
    rw [hidx, hpascal r]
    ring
  have hfirst : (∑ r ∈ range (m + 1),
      (m.choose (r + 1) : ℝ) * x ^ (m - r) * (1 - x) ^ (r + 1) / (r + 1)) = x * P m x := by
    rw [P, Finset.mul_sum, Finset.sum_range_succ]
    have hzero : (m.choose (m + 1) : ℝ) * x ^ (m - m) * (1 - x) ^ (m + 1) / ((m : ℝ) + 1) = 0 := by
      rw [Nat.choose_succ_self]
      simp
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r < m := Finset.mem_range.mp hr
    have hidx : m - r = (m - (r + 1)) + 1 := by omega
    rw [hidx]
    ring
  have hsecond : (∑ r ∈ range (m + 1),
      (m.choose r : ℝ) * x ^ (m - r) * (1 - x) ^ (r + 1) / (r + 1))
      = (1 - x ^ (m + 1)) / ((m : ℝ) + 1) := by
    have hcoef : ∀ r : ℕ, (m.choose r : ℝ) / ((r : ℝ) + 1)
        = ((m + 1).choose (r + 1) : ℝ) / ((m : ℝ) + 1) := by
      intro r
      have hnat := Nat.succ_mul_choose_eq m r
      have hcast : ((m : ℝ) + 1) * (m.choose r : ℝ)
          = ((m + 1).choose (r + 1) : ℝ) * ((r : ℝ) + 1) := by
        exact_mod_cast hnat
      have h1 : ((r : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      linarith [hcast]
    have hcast : ∀ r : ℕ, ((m : ℝ) + 1) * (m.choose r : ℝ)
        = ((m + 1).choose (r + 1) : ℝ) * ((r : ℝ) + 1) := by
      intro r
      exact_mod_cast Nat.succ_mul_choose_eq m r
    have hstep : (∑ r ∈ range (m + 1),
        (m.choose r : ℝ) * x ^ (m - r) * (1 - x) ^ (r + 1) / (r + 1))
        = (1 - x) * A m x / ((m : ℝ) + 1) := by
      have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
      rw [eq_div_iff h2, A, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      have h1 : ((r : ℝ) + 1) ≠ 0 := by positivity
      have hC := hcast r
      rw [div_mul_eq_mul_div, div_eq_iff h1]
      linear_combination (x ^ (m - r) * (1 - x) ^ (r + 1)) * hC
    rw [hstep, A_mul]
  rw [hsplit, hfirst, hsecond]

theorem P_eq (m : ℕ) (x : ℝ) :
    P m x = ∑ i ∈ range m, (x ^ (m - (i + 1)) - x ^ m) / ((i : ℝ) + 1) := by
  induction m with
  | zero => simp [P_zero]
  | succ m ih =>
    rw [P_rec, ih]
    rw [Finset.sum_range_succ]
    have hshift : (∑ i ∈ range m, (x ^ (m + 1 - (i + 1)) - x ^ (m + 1)) / ((i : ℝ) + 1))
        = x * ∑ i ∈ range m, (x ^ (m - (i + 1)) - x ^ m) / ((i : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < m := Finset.mem_range.mp hi
      have hidx : m + 1 - (i + 1) = (m - (i + 1)) + 1 := by omega
      rw [hidx]
      have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hlastterm : (x ^ (m + 1 - (m + 1)) - x ^ (m + 1)) / ((m : ℝ) + 1)
        = (1 - x ^ (m + 1)) / ((m : ℝ) + 1) := by
      simp
    rw [hshift, hlastterm]

/-! ### `L = Rp` -/

theorem L_zero (x : ℝ) : L 0 x = 0 := by
  simp [L, H_zero]

theorem Rp_zero (x : ℝ) : Rp 0 x = 0 := by
  simp [Rp]

/-- Both halves grow by the same `P`. -/
theorem L_rec (d : ℕ) (x : ℝ) : L (d + 1) x = L d x + P (d + 1) x := by
  have hpascal : ∀ r : ℕ, ((d + 2).choose (r + 1) : ℝ)
      = ((d + 1).choose (r + 1) : ℝ) + ((d + 1).choose r : ℝ) := by
    intro r
    rw [show d + 2 = (d + 1) + 1 from rfl, Nat.choose_succ_succ (d + 1) r]
    push_cast
    ring
  have hsplit : L (d + 1) x
      = (∑ r ∈ range (d + 2), ((d + 1).choose (r + 1) : ℝ) * H r * x ^ (d + 1 - r) * (1 - x) ^ r)
        + ∑ r ∈ range (d + 2), ((d + 1).choose r : ℝ) * H r * x ^ (d + 1 - r) * (1 - x) ^ r := by
    rw [L, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show d + 1 + 1 = d + 2 from rfl, hpascal r]
    ring
  have hfirst : (∑ r ∈ range (d + 2),
      ((d + 1).choose (r + 1) : ℝ) * H r * x ^ (d + 1 - r) * (1 - x) ^ r) = x * L d x := by
    rw [L, Finset.mul_sum, show d + 2 = (d + 1) + 1 from rfl, Finset.sum_range_succ]
    have hzero : ((d + 1).choose (d + 1 + 1) : ℝ) * H (d + 1)
        * x ^ (d + 1 - (d + 1)) * (1 - x) ^ (d + 1) = 0 := by
      rw [Nat.choose_succ_self]
      simp
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hidx : d + 1 - r = (d - r) + 1 := by omega
    rw [hidx]
    ring
  have hsecond : (∑ r ∈ range (d + 2),
      ((d + 1).choose r : ℝ) * H r * x ^ (d + 1 - r) * (1 - x) ^ r)
      = (1 - x) * L d x + P (d + 1) x := by
    rw [Finset.sum_range_succ']
    have hzeroterm : ((d + 1).choose 0 : ℝ) * H 0 * x ^ (d + 1 - 0) * (1 - x) ^ 0 = 0 := by
      rw [H_zero]
      ring
    rw [hzeroterm, add_zero]
    have hterm : ∀ q ∈ range (d + 1),
        ((d + 1).choose (q + 1) : ℝ) * H (q + 1) * x ^ (d + 1 - (q + 1)) * (1 - x) ^ (q + 1)
        = (1 - x) * (((d + 1).choose (q + 1) : ℝ) * H q * x ^ (d - q) * (1 - x) ^ q)
          + ((d + 1).choose (q + 1) : ℝ) * x ^ ((d + 1) - (q + 1)) * (1 - x) ^ (q + 1)
            / ((q : ℝ) + 1) := by
      intro q hq
      have hq' : q ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      have hidx : d + 1 - (q + 1) = d - q := by omega
      rw [hidx, H_succ q]
      have h1 : ((q : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← L, ← P]
  rw [hsplit, hfirst, hsecond]
  ring

theorem Rp_rec (d : ℕ) (x : ℝ) : Rp (d + 1) x = Rp d x + P (d + 1) x := by
  have hP : P (d + 1) x
      = (∑ i ∈ range (d + 1), x ^ (d - i) / ((i : ℝ) + 1)) - H (d + 1) * x ^ (d + 1) := by
    rw [P_eq]
    have hsplitdiv : ∀ i ∈ range (d + 1),
        (x ^ (d + 1 - (i + 1)) - x ^ (d + 1)) / ((i : ℝ) + 1)
        = x ^ (d - i) / ((i : ℝ) + 1) - (1 / ((i : ℝ) + 1)) * x ^ (d + 1) := by
      intro i hi
      have hi2 : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hidx : d + 1 - (i + 1) = d - i := by omega
      rw [hidx]
      ring
    rw [Finset.sum_congr rfl hsplitdiv, Finset.sum_sub_distrib, H, Finset.sum_mul]
  have hRdiff : Rp (d + 1) x - Rp d x
      = (∑ j ∈ range (d + 1), x ^ j / ((d : ℝ) + 1 - j)) - H (d + 1) * x ^ (d + 1) := by
    rw [Rp, Rp, Finset.sum_range_succ]
    have hlast : (H (d + 1 - (d + 1)) - H (d + 1)) * x ^ (d + 1) = -(H (d + 1) * x ^ (d + 1)) := by
      simp [H_zero]
    rw [hlast]
    have hterm : ∀ j ∈ range (d + 1),
        (H (d + 1 - j) - H j) * x ^ j = (H (d - j) - H j) * x ^ j + x ^ j / ((d : ℝ) + 1 - j) := by
      intro j hj
      have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hidx : d + 1 - j = (d - j) + 1 := by omega
      rw [hidx, H_succ]
      have hcast : ((d - j : ℕ) : ℝ) + 1 = (d : ℝ) + 1 - j := by
        have : ((d - j : ℕ) : ℝ) = (d : ℝ) - j := by
          rw [Nat.cast_sub hj']
        rw [this]
        ring
      rw [hcast]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Rp]
    ring
  have hreflect : (∑ j ∈ range (d + 1), x ^ j / ((d : ℝ) + 1 - j))
      = ∑ i ∈ range (d + 1), x ^ (d - i) / ((i : ℝ) + 1) := by
    have := Finset.sum_range_reflect (fun j => x ^ (d - j) / ((j : ℝ) + 1)) (d + 1)
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hidx : d - (d + 1 - 1 - j) = j := by omega
    have hcast : ((d + 1 - 1 - j : ℕ) : ℝ) + 1 = (d : ℝ) + 1 - j := by
      have h1 : d + 1 - 1 - j = d - j := by omega
      rw [h1, Nat.cast_sub hj']
      ring
    rw [hidx, hcast]
  rw [hP, ← hreflect]
  linarith [hRdiff]

theorem L_eq_Rp (d : ℕ) (x : ℝ) : L d x = Rp d x := by
  induction d with
  | zero => rw [L_zero, Rp_zero]
  | succ d ih => rw [L_rec, Rp_rec, ih]

/-! ### The polynomial `G` and its Bernstein form -/

/-- The source's `G_n`. -/
noncomputable def G (n : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ range n, (3 - 2 * H (n - 1 - j) + 2 * H j) * x ^ j) - 2 * (n : ℝ) * x ^ (n - 1)

/-- `G` at `n = d + 1`, the form every proof below uses. -/
noncomputable def Gd (d : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ range (d + 1), (3 - 2 * H (d - j) + 2 * H j) * x ^ j) - 2 * ((d : ℝ) + 1) * x ^ d

theorem G_succ (d : ℕ) (x : ℝ) : G (d + 1) x = Gd d x := by
  unfold G Gd
  push_cast
  simp

/-- **The Bernstein form.**  The `3`-part is `A_eq`, the harmonic part is `L_eq_Rp`. -/
theorem Gd_bernstein (d : ℕ) (x : ℝ) :
    Gd d x = (∑ r ∈ range (d + 1), ((d + 1).choose (r + 1) : ℝ) * (3 - 2 * H r)
        * x ^ (d - r) * (1 - x) ^ r) - 2 * ((d : ℝ) + 1) * x ^ d := by
  have hsplit : (∑ r ∈ range (d + 1), ((d + 1).choose (r + 1) : ℝ) * (3 - 2 * H r)
      * x ^ (d - r) * (1 - x) ^ r) = 3 * A d x - 2 * L d x := by
    rw [A, L, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hsplit, A_eq, L_eq_Rp, Rp, Gd]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The `u`-polynomial and the sign rule -/

/-- `Φ_d(u)`, with `G_n(x) = x^d · Φ_d((1−x)/x)` for `x ∈ (0,1)`. -/
noncomputable def Phi (d : ℕ) (u : ℝ) : ℝ :=
  (∑ r ∈ range (d + 1), ((d + 1).choose (r + 1) : ℝ) * (3 - 2 * H r) * u ^ r)
    - 2 * ((d : ℝ) + 1)

theorem Gd_eq_Phi (d : ℕ) {x : ℝ} (hx : 0 < x) :
    Gd d x = x ^ d * Phi d ((1 - x) / x) := by
  rw [Gd_bernstein, Phi]
  have hxne : x ≠ 0 := ne_of_gt hx
  have hterm : ∀ r ∈ range (d + 1),
      ((d + 1).choose (r + 1) : ℝ) * (3 - 2 * H r) * x ^ (d - r) * (1 - x) ^ r
      = x ^ d * (((d + 1).choose (r + 1) : ℝ) * (3 - 2 * H r) * ((1 - x) / x) ^ r) := by
    intro r hr
    have hr' : r ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hpow : x ^ (d - r) * x ^ r = x ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have hxr : (x : ℝ) ^ r ≠ 0 := pow_ne_zero r hxne
    rw [div_pow, ← hpow]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- The three-block form of `Φ`: constant `d+1`, linear `C(d+1,2)`, a vanishing `u²` term, and
nonpositive coefficients from `u³` on. -/
theorem Phi_split (m : ℕ) (u : ℝ) :
    Phi (m + 3) u = ((m : ℝ) + 3 + 1) + ((m + 4).choose 2 : ℝ) * u
      + ∑ r ∈ range (m + 1), ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * u ^ (r + 3) := by
  rw [Phi]
  rw [show (range (m + 3 + 1)) = range (3 + (m + 1)) from by
    congr 1
    omega]
  rw [Finset.sum_range_add]
  have hhead : (∑ r ∈ range 3, ((m + 3 + 1).choose (r + 1) : ℝ) * (3 - 2 * H r) * u ^ r)
      = 3 * ((m : ℝ) + 3 + 1) + ((m + 4).choose 2 : ℝ) * u := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, H_zero, H_one, H_two]
    have h1 : ((m + 3 + 1).choose 1 : ℝ) = (m : ℝ) + 3 + 1 := by
      rw [Nat.choose_one_right]
      push_cast
      ring
    have h4 : m + 3 + 1 = m + 4 := by omega
    rw [h1, h4]
    ring
  have htail : (∑ r ∈ range (m + 1), ((m + 3 + 1).choose (3 + r + 1) : ℝ)
      * (3 - 2 * H (3 + r)) * u ^ (3 + r))
      = ∑ r ∈ range (m + 1), ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * u ^ (r + 3) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 : m + 3 + 1 = m + 4 := by omega
    have h2 : 3 + r + 1 = r + 4 := by omega
    have h3 : 3 + r = r + 3 := by omega
    rw [h1, h2, h3]
  rw [hhead, htail]
  push_cast
  ring

/-- **The sign rule, in the only form needed.**  For `0 < v ≤ u`, `Φ_d(u) v² ≤ Φ_d(v) u²`.  Every
term is checked separately: the constant and linear parts push one way, and the nonpositive tail
coefficients push the same way because `v^{r} u² − u^{r} v² ≤ 0`. -/
theorem Phi_key (m : ℕ) {u v : ℝ} (hv : 0 < v) (huv : v ≤ u) :
    Phi (m + 3) u * v ^ 2 ≤ Phi (m + 3) v * u ^ 2 := by
  have hu : 0 < u := lt_of_lt_of_le hv huv
  have hexpand : ∀ w z : ℝ,
      Phi (m + 3) w * z ^ 2
      = ((m : ℝ) + 3 + 1) * z ^ 2 + ((m + 4).choose 2 : ℝ) * (w * z ^ 2)
        + ∑ r ∈ range (m + 1),
            ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * (w ^ (r + 3) * z ^ 2) := by
    intro w z
    rw [Phi_split, add_mul, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun r _ => by ring
  rw [hexpand, hexpand]
  have hsq : v ^ 2 ≤ u ^ 2 := by nlinarith
  have hconst : ((m : ℝ) + 3 + 1) * v ^ 2 ≤ ((m : ℝ) + 3 + 1) * u ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hbase : u * v ^ 2 ≤ v * u ^ 2 := by
    nlinarith [mul_nonneg (mul_pos hu hv).le (sub_nonneg.mpr huv)]
  have hlin : ((m + 4).choose 2 : ℝ) * (u * v ^ 2) ≤ ((m + 4).choose 2 : ℝ) * (v * u ^ 2) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  have htail : (∑ r ∈ range (m + 1),
      ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * (u ^ (r + 3) * v ^ 2))
      ≤ ∑ r ∈ range (m + 1),
      ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * (v ^ (r + 3) * u ^ 2) := by
    refine Finset.sum_le_sum fun r _ => ?_
    have hH : (3 : ℝ) / 2 < H (r + 3) := H_gt (by omega)
    have hc : (0 : ℝ) ≤ ((m + 4).choose (r + 4) : ℝ) := by positivity
    have hcoef : ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) ≤ 0 := by nlinarith
    have hpow : v ^ (r + 1) ≤ u ^ (r + 1) := pow_le_pow_left₀ hv.le huv _
    have hv3 : v ^ (r + 3) = v ^ (r + 1) * v ^ 2 := by rw [← pow_add]
    have hu3 : u ^ (r + 3) = u ^ (r + 1) * u ^ 2 := by rw [← pow_add]
    have hfac : v ^ (r + 3) * u ^ 2 - u ^ (r + 3) * v ^ 2 ≤ 0 := by
      rw [hv3, hu3]
      have hvv : (0 : ℝ) < v ^ 2 := by positivity
      have huu : (0 : ℝ) < u ^ 2 := by positivity
      nlinarith [mul_nonneg (mul_pos hvv huu).le (sub_nonneg.mpr hpow)]
    nlinarith [mul_nonneg (neg_nonneg.mpr hcoef) (neg_nonneg.mpr hfac)]
  linarith

/-- The strict form, which is what makes the threshold unique. -/
theorem Phi_key_strict (m : ℕ) {u v : ℝ} (hv : 0 < v) (huv : v < u) :
    Phi (m + 3) u * v ^ 2 < Phi (m + 3) v * u ^ 2 := by
  have hu : 0 < u := lt_trans hv huv
  have hexpand : ∀ w z : ℝ,
      Phi (m + 3) w * z ^ 2
      = ((m : ℝ) + 3 + 1) * z ^ 2 + ((m + 4).choose 2 : ℝ) * (w * z ^ 2)
        + ∑ r ∈ range (m + 1),
            ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * (w ^ (r + 3) * z ^ 2) := by
    intro w z
    rw [Phi_split, add_mul, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun r _ => by ring
  rw [hexpand, hexpand]
  have hsq : v ^ 2 < u ^ 2 := by nlinarith
  have hconst : ((m : ℝ) + 3 + 1) * v ^ 2 < ((m : ℝ) + 3 + 1) * u ^ 2 :=
    mul_lt_mul_of_pos_left hsq (by positivity)
  have hbase : u * v ^ 2 ≤ v * u ^ 2 := by
    nlinarith [mul_nonneg (mul_pos hu hv).le (sub_nonneg.mpr huv.le)]
  have hlin : ((m + 4).choose 2 : ℝ) * (u * v ^ 2) ≤ ((m + 4).choose 2 : ℝ) * (v * u ^ 2) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  have htail : (∑ r ∈ range (m + 1),
      ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * (u ^ (r + 3) * v ^ 2))
      ≤ ∑ r ∈ range (m + 1),
      ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) * (v ^ (r + 3) * u ^ 2) := by
    refine Finset.sum_le_sum fun r _ => ?_
    have hH : (3 : ℝ) / 2 < H (r + 3) := H_gt (by omega)
    have hc : (0 : ℝ) ≤ ((m + 4).choose (r + 4) : ℝ) := by positivity
    have hcoef : ((m + 4).choose (r + 4) : ℝ) * (3 - 2 * H (r + 3)) ≤ 0 := by nlinarith
    have hpow : v ^ (r + 1) ≤ u ^ (r + 1) := pow_le_pow_left₀ hv.le huv.le _
    have hv3 : v ^ (r + 3) = v ^ (r + 1) * v ^ 2 := by rw [← pow_add]
    have hu3 : u ^ (r + 3) = u ^ (r + 1) * u ^ 2 := by rw [← pow_add]
    have hfac : v ^ (r + 3) * u ^ 2 - u ^ (r + 3) * v ^ 2 ≤ 0 := by
      rw [hv3, hu3]
      have hvv : (0 : ℝ) < v ^ 2 := by positivity
      have huu : (0 : ℝ) < u ^ 2 := by positivity
      nlinarith [mul_nonneg (mul_pos hvv huu).le (sub_nonneg.mpr hpow)]
    nlinarith [mul_nonneg (neg_nonneg.mpr hcoef) (neg_nonneg.mpr hfac)]
  linarith

/-! ### The MathDB assertion -/

theorem Gd_at_one (d : ℕ) : Gd d 1 = (d : ℝ) + 1 := by
  have hrefl : (∑ j ∈ range (d + 1), H (d - j)) = ∑ j ∈ range (d + 1), H j := by
    have hr := Finset.sum_range_reflect (fun j => H j) (d + 1)
    rw [← hr]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj2 : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hidx : d + 1 - 1 - j = d - j := by omega
    rw [hidx]
  have hsum : (∑ j ∈ range (d + 1), (3 - 2 * H (d - j) + 2 * H j) * (1 : ℝ) ^ j)
      = (∑ j ∈ range (d + 1), (3 : ℝ))
        - 2 * (∑ j ∈ range (d + 1), H (d - j)) + 2 * ∑ j ∈ range (d + 1), H j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Gd, hsum, hrefl]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_pow, mul_one]
  push_cast
  ring

theorem Gd_at_zero (d : ℕ) (hd : 1 ≤ d) : Gd d 0 = 3 - 2 * H d := by
  have hd0 : (0 : ℝ) ^ d = 0 := zero_pow (by omega)
  have hsum : (∑ j ∈ range (d + 1), (3 - 2 * H (d - j) + 2 * H j) * (0 : ℝ) ^ j)
      = 3 - 2 * H d := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos d))
      (fun b _ hb => by simp [zero_pow hb])]
    simp [H_zero]
  rw [Gd, hsum, hd0]
  ring

theorem Gd_small_zero (x : ℝ) : Gd 0 x = 1 := by
  rw [Gd]
  norm_num [Finset.sum_range_succ, H_zero]

theorem Gd_small_one (x : ℝ) : Gd 1 x = 1 + x := by
  rw [Gd]
  norm_num [Finset.sum_range_succ, H_zero, H_one]
  try ring

theorem Gd_small_two (x : ℝ) : Gd 2 x = 3 * x := by
  rw [Gd]
  norm_num [Finset.sum_range_succ, H_zero, H_one, H_two]
  try ring

/-- The comparison `u = (1-x)/x` reverses order on `(0,1)`. -/
theorem u_antitone {x y : ℝ} (hx : 0 < x) (hy : y < 1) (hxy : x ≤ y) :
    (1 - y) / y ≤ (1 - x) / x := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy0
  have h1 : (1 - y) / y = 1 / y - 1 := by field_simp
  have h2 : (1 - x) / x = 1 / x - 1 := by field_simp
  have h3 : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx hxy
  rw [h1, h2]
  linarith

theorem u_antitone_strict {x y : ℝ} (hx : 0 < x) (hy : y < 1) (hxy : x < y) :
    (1 - y) / y < (1 - x) / x := by
  have hy0 : 0 < y := lt_trans hx hxy
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy0
  have h1 : (1 - y) / y = 1 / y - 1 := by field_simp
  have h2 : (1 - x) / x = 1 / x - 1 := by field_simp
  have h3 : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
  rw [h1, h2]
  linarith

/-- **MathDB #333222.**  The stopping region is monotone: on `[0,1]`, once `G_n` is nonnegative it
stays nonnegative.  This is the assertion the record makes. -/
theorem monotone_stopping (n : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) (h : 0 ≤ G n x) : 0 ≤ G n y := by
  rcases n with _ | d
  · simp [G]
  · rw [G_succ] at h ⊢
    have hy0b : 0 ≤ y := le_trans hx hxy
    rcases Nat.lt_or_ge d 3 with hd | hd
    · interval_cases d
      · rw [Gd_small_zero]; norm_num
      · rw [Gd_small_one]; linarith
      · rw [Gd_small_two]; linarith
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
      rcases eq_or_lt_of_le hy0b with hy0 | hy0
      · have hxeq : x = y := by linarith
        rw [← hxeq]
        exact h
      · rcases eq_or_lt_of_le hy with hy1 | hy1
        · rw [hy1, Gd_at_one]
          positivity
        · rcases eq_or_lt_of_le hx with hx0 | hx0
          · exfalso
            rw [← hx0, Gd_at_zero _ (by omega)] at h
            have hH := H_gt (show 3 ≤ m + 3 by omega)
            linarith
          · have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
            have hux : 0 < (1 - x) / x := div_pos (by linarith) hx0
            have huy : 0 < (1 - y) / y := div_pos (by linarith) hy0
            have hle := u_antitone hx0 hy1 hxy
            have hxd : (0 : ℝ) < x ^ (m + 3) := by positivity
            have hPhix : 0 ≤ Phi (m + 3) ((1 - x) / x) := by
              rw [Gd_eq_Phi _ hx0] at h
              nlinarith
            have hkey := Phi_key m huy hle
            have hx2 : (0 : ℝ) < ((1 - x) / x) ^ 2 := by positivity
            have hPhiy : 0 ≤ Phi (m + 3) ((1 - y) / y) := by nlinarith
            rw [Gd_eq_Phi _ hy0]
            positivity

/-- For `n ≥ 4` a threshold exists in `(0,1)`: `G_n(0) < 0 < G_n(1)` and `G_n` is continuous. -/
theorem exists_threshold (m : ℕ) : ∃ s ∈ Set.Ioo (0 : ℝ) 1, Gd (m + 3) s = 0 := by
  have hcont : Continuous fun x : ℝ => Gd (m + 3) x := by
    unfold Gd
    exact (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_pow j)).sub
      (continuous_const.mul (continuous_pow _))
  have h0 : Gd (m + 3) 0 < 0 := by
    rw [Gd_at_zero _ (by omega)]
    have hH := H_gt (show 3 ≤ m + 3 by omega)
    linarith
  have h1 : 0 < Gd (m + 3) 1 := by
    rw [Gd_at_one]
    positivity
  have hmem : (0 : ℝ) ∈ Set.Ioo (Gd (m + 3) 0) (Gd (m + 3) 1) := Set.mem_Ioo.mpr ⟨h0, h1⟩
  obtain ⟨s, hs, hs0⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hmem
  exact ⟨s, hs, hs0⟩

/-- Past a root the polynomial is strictly positive. -/
theorem pos_of_gt_root (m : ℕ) {s t : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hlt : s < t) (hs0 : Gd (m + 3) s = 0) :
    0 < Gd (m + 3) t := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  have hus : 0 < (1 - s) / s := div_pos (by linarith) hs1
  have hut : 0 < (1 - t) / t := div_pos (by linarith) ht1
  have hltu := u_antitone_strict hs1 ht2 hlt
  have hsd : (0 : ℝ) < s ^ (m + 3) := by positivity
  have hPhis : Phi (m + 3) ((1 - s) / s) = 0 := by
    rw [Gd_eq_Phi _ hs1] at hs0
    rcases mul_eq_zero.mp hs0 with hcon | hgood
    · exact absurd hcon (ne_of_gt hsd)
    · exact hgood
  have hkey := Phi_key_strict m hut hltu
  rw [hPhis] at hkey
  have hs2b : (0 : ℝ) < ((1 - s) / s) ^ 2 := by positivity
  have hPhit : 0 < Phi (m + 3) ((1 - t) / t) := by nlinarith
  rw [Gd_eq_Phi _ ht1]
  positivity

/-- **The threshold is unique.** -/
theorem threshold_unique (m : ℕ) {s t : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs0 : Gd (m + 3) s = 0) (ht0 : Gd (m + 3) t = 0) : s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hpos := pos_of_gt_root m hs ht hlt hs0
    rw [ht0] at hpos
    exact lt_irrefl 0 hpos
  · have hpos := pos_of_gt_root m ht hs hlt ht0
    rw [hs0] at hpos
    exact lt_irrefl 0 hpos

/-- **The threshold form, stated in the source's `n`.**  For `n ≥ 4` there is exactly one
`s ∈ (0,1)` with `G_n(s) = 0`.  `exists_threshold` and `threshold_unique` carry the `n ≥ 4`
restriction in their *types* (as `d = m + 3`, i.e. `n = m + 4`); this corollary makes it an
explicit hypothesis so the statement can be read without decoding the index. -/
theorem exists_unique_threshold (n : ℕ) (hn : 4 ≤ n) :
    ∃! s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 ∧ G n s = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hG : ∀ t : ℝ, G (m + 4) t = Gd (m + 3) t := by
    intro t
    have hidx : m + 4 = (m + 3) + 1 := by omega
    rw [hidx, G_succ]
  obtain ⟨s, hs, hs0⟩ := exists_threshold m
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [hG]
    exact hs0
  · rintro t ⟨ht, ht0⟩
    rw [hG] at ht0
    exact threshold_unique m ht hs ht0 hs0

end Principia.MathDB.P333222
