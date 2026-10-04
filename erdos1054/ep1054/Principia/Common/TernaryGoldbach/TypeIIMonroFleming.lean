/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIICortoLarge

set_option autoImplicit false

/-!
# `M2H.MonroFleming` spined: `eq:crusto` → `eq:fleming` from two links

`M2H.MonroFleming` asks `S₁(U, W) ≤ (x/W)(4/π²)·eq:grotto(x/WU) + 22.6418(x/W)^{3/2}/U`
(`minarcs.tex` 2626-2848). Everything after the two genuinely arithmetic steps is PROVED:

```
 CrustoCudo   S₁(U, W) = ∑_{s ≤ S odd} srto(S/s, x/Ws)       (eq:crusto, eq:cudo)    LINK, exact
 Monro2       |srto(y, z) − (4/π²)z·mutedSum(y)| ≤ 1.27ζ(3/2)²y√z(1 + 1/√2)(1 − 2^{−3/2})²
                                                               (lem:monro, eq:mudo)    LINK
 muted_eq     mutedSum(y) = ∫_{1/2}^{1} g₂(uy) du              (eq:fleming)            PROVED
 zeta32_le    ζ(3/2) ≤ 3;  odd32_le  ∑_{s odd} s^{−3/2} ≤ 2  (eq:flatow's sum)       PROVED
 kappa_le     2·1.27ζ(3/2)²(1 + 1/√2)(1 − 2^{−3/2})² ≤ 22.6418  (it is ≤ 16.31)      PROVED
 monroFleming_of_links : M2H.MonroFleming                                              PROVED
```

Both links were checked numerically before stating (scratch `corto/monro.py`): `CrustoCudo`
exactly on 60 random `(x, U, W)`, `Monro2` with worst ratio `0.015` on 300 random `(y, z)`.

**Finding (minor).** `lem:monro` (`minarcs.tex` 2672-2674, book likewise) bounds `l` below by
`min((z/y)/min(r₁, r₂), z/2r₁r₂)`; `eq:cudo` (the sum it is applied to) has `max`, and so does
the main term, whose factor `1 − max(1/2, r₁/y, r₂/y)` is the length of the `max` range. `srto`
uses `max`. The odd `s` and the crude `ζ(3/2) ≤ 3` leave a factor `1.39` of room in `22.6418`.
-/

namespace Principia.Common.TernaryGoldbach.M2F

open MeasureTheory Set

/-! ## (0) Objects and links -/

/-- `μ(r₁)μ(r₂)/(σ(r₁)σ(r₂))`. -/
noncomputable def tm (r1 r2 : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius r1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius r2 : ℤ) : ℝ) /
    ((ArithmeticFunction.sigma 1 r1 : ℝ) * (ArithmeticFunction.sigma 1 r2 : ℝ))

/-- The `l`-count of `eq:srto`/`eq:cudo`: square-free `l` coprime to `2r₁r₂` with
`max((z/y)/min(r₁, r₂), z/2r₁r₂) < l ≤ z/r₁r₂`. -/
noncomputable def lcnt (y z : ℝ) (r1 r2 : ℕ) : ℝ :=
  (((Finset.Icc 1 ⌊z / ((r1 : ℝ) * r2)⌋₊).filter (fun l : ℕ =>
    max (z / y / ((min r1 r2 : ℕ) : ℝ)) (z / (2 * r1 * r2)) < (l : ℝ) ∧
      Nat.Coprime l (2 * r1 * r2) ∧ Squarefree l)).card : ℝ)

/-- **`eq:srto`, `v = 2`**: `∑_{r₁, r₂ < y, cnd} μ(r₁)μ(r₂)·lcnt`. -/
noncomputable def srto (y z : ℝ) : ℝ :=
  ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, ∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊,
    if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
      ((ArithmeticFunction.moebius r1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius r2 : ℤ) : ℝ) *
        lcnt y z r1 r2
    else 0

/-- `∑_{r₁, r₂ < y, cnd} μ(r₁)μ(r₂)/(σ(r₁)σ(r₂))·(1 − max(1/2, r₁/y, r₂/y))`. -/
noncomputable def mutedSum (y : ℝ) : ℝ :=
  ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, ∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊,
    if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
      tm r1 r2 * (1 - max (1 / 2) (max ((r1 : ℝ) / y) ((r2 : ℝ) / y)))
    else 0

/-- `ζ(3/2) = ∑_{n ≥ 1} n^{−3/2}`. -/
noncomputable def zeta32 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ ((3 : ℝ) / 2)

/-! ## (1) `eq:fleming`: the main term of `lem:monro` is an integral of `g₂` -/

theorem gY_eq (y u : ℝ) (hy : 0 < y) (hu0 : 0 ≤ u) (hu : u < 1) :
    HC.gYutto 2 (u * y) = ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, ∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊,
      if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then tm r1 r2 *
        (if (max r1 r2 : ℕ) ≤ u * y then (1 : ℝ) else 0) else 0 := by
  have huy : u * y < y := by nlinarith
  have hsub : Finset.Icc 1 ⌊u * y⌋₊ ⊆ Finset.Ico 1 ⌈y⌉₊ := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [Finset.mem_Ico]
    refine ⟨hr.1, ?_⟩
    have h1 : (r : ℝ) ≤ u * y :=
      le_trans (by exact_mod_cast hr.2) (Nat.floor_le (by positivity))
    exact Nat.lt_ceil.mpr (by linarith)
  have hmem : ∀ r : ℕ, r ∈ Finset.Ico 1 ⌈y⌉₊ → (r ∈ Finset.Icc 1 ⌊u * y⌋₊ ↔ (r : ℝ) ≤ u * y) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    rw [Finset.mem_Icc]
    constructor
    · intro h
      exact le_trans (by exact_mod_cast h.2) (Nat.floor_le (by positivity))
    · intro h
      exact ⟨hr.1, Nat.le_floor h⟩
  unfold HC.gYutto
  rw [← Finset.sum_subset hsub (fun r1 hr1 hn => by
    refine Finset.sum_eq_zero fun r2 _ => ?_
    have : ¬ (r1 : ℝ) ≤ u * y := fun h => hn ((hmem r1 hr1).mpr h)
    have hnot : ¬ ((max r1 r2 : ℕ) : ℝ) ≤ u * y := fun h =>
      this (le_trans (Nat.cast_le.mpr (le_max_left r1 r2)) h)
    rw [if_neg hnot, mul_zero, ite_self])]
  refine Finset.sum_congr rfl fun r1 hr1 => ?_
  have h1 : (r1 : ℝ) ≤ u * y := (hmem r1 (hsub hr1)).mp hr1
  rw [← Finset.sum_subset hsub (fun r2 hr2 hn => by
    have : ¬ (r2 : ℝ) ≤ u * y := fun h => hn ((hmem r2 hr2).mpr h)
    have hnot : ¬ ((max r1 r2 : ℕ) : ℝ) ≤ u * y := fun h =>
      this (le_trans (Nat.cast_le.mpr (le_max_right r1 r2)) h)
    rw [if_neg hnot, mul_zero, ite_self])]
  refine Finset.sum_congr rfl fun r2 hr2 => ?_
  have h2 : (r2 : ℝ) ≤ u * y := (hmem r2 (hsub hr2)).mp hr2
  have hm : ((max r1 r2 : ℕ) : ℝ) ≤ u * y := by
    rw [Nat.cast_max]
    exact max_le h1 h2
  rw [if_pos hm, mul_one]
  rfl

theorem meas_ind (m y : ℝ) : Measurable fun u : ℝ => if m ≤ u * y then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_le measurable_const (measurable_id.mul_const y))
    measurable_const measurable_const

theorem ii_ind (m y a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => if m ≤ u * y then (1 : ℝ) else 0) volume a b := by
  refine M2H.ii_of_bdd _ (meas_ind m y) 1 a b hab fun u _ => ?_
  split_ifs <;> simp

/-- `∫_{1/2}^{1} 𝟙[m ≤ uy] du = 1 − max(1/2, m/y)` for `0 < m < y`. -/
theorem int_ind (m y : ℝ) (hm : 0 < m) (hmy : m < y) :
    ∫ u in (1 / 2 : ℝ)..1, (if m ≤ u * y then (1 : ℝ) else 0) = 1 - max (1 / 2) (m / y) := by
  have hy : 0 < y := by linarith
  have hc1 : m / y < 1 := by rw [div_lt_one hy]; exact hmy
  have hiff : ∀ u : ℝ, m ≤ u * y ↔ m / y ≤ u := fun u => by rw [div_le_iff₀ hy]
  rcases le_or_gt (m / y) (1 / 2) with hc | hc
  · rw [max_eq_left hc, intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      (g := fun _ => (1 : ℝ)) fun u hu => by
        simp only
        rw [if_pos ((hiff u).mpr (by linarith [hu.1]))]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  · rw [max_eq_right hc.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := m / y)
      (ii_ind m y _ _ hc.le) (ii_ind m y _ _ hc1.le)]
    rw [intervalIntegral.integral_congr_Ioo_of_le hc.le (g := fun _ => (0 : ℝ)) fun u hu => by
        simp only
        rw [if_neg (fun h => by linarith [(hiff u).mp h, hu.2])]]
    rw [intervalIntegral.integral_congr_Ioo_of_le hc1.le (g := fun _ => (1 : ℝ)) fun u hu => by
        simp only
        rw [if_pos ((hiff u).mpr hu.1.le)]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring

theorem meas_gy (y : ℝ) : Measurable fun u : ℝ => HC.gYutto 2 (u * y) := by
  have h : (fun u : ℝ => HC.gYutto 2 (u * y)) =
      (fun t : ℝ => (fun k : ℕ => HC.gYutto 2 (k : ℝ)) ⌊t⌋₊) ∘ (fun u : ℝ => u * y) :=
    funext fun u => M2G.gY_floor _
  rw [h]
  exact (M2G.meas_step (fun k : ℕ => HC.gYutto 2 (k : ℝ))).comp (measurable_id.mul_const y)

/-- **`eq:fleming`**: `mutedSum y = ∫_{1/2}^{1} g₂(uy) du`. -/
theorem muted_eq (y : ℝ) (hy : 0 < y) :
    mutedSum y = ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * y) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    (g := fun u => ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, ∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊,
      (if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then tm r1 r2 else 0) *
        (if ((max r1 r2 : ℕ) : ℝ) ≤ u * y then (1 : ℝ) else 0))
    fun u hu => by
      simp only
      rw [gY_eq y u hy (by linarith [hu.1]) hu.2]
      refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
      rw [ite_zero_mul]]
  rw [intervalIntegral.integral_finsetSum fun r1 _ => by
    have h := IntervalIntegrable.sum (Finset.Ico 1 ⌈y⌉₊) (fun r2 _ =>
      (ii_ind ((max r1 r2 : ℕ) : ℝ) y _ _ (by norm_num : (1 / 2 : ℝ) ≤ 1)).const_mul
        (if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then tm r1 r2 else 0))
    rw [Finset.sum_fn] at h
    exact h]
  unfold mutedSum
  refine Finset.sum_congr rfl fun r1 hr1 => ?_
  rw [intervalIntegral.integral_finsetSum fun r2 _ => (ii_ind _ y _ _ (by norm_num)).const_mul _]
  refine Finset.sum_congr rfl fun r2 hr2 => ?_
  rw [intervalIntegral.integral_const_mul]
  have h1 := Finset.mem_Ico.mp hr1
  have h2 := Finset.mem_Ico.mp hr2
  have hm1 : (1 : ℝ) ≤ ((max r1 r2 : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1.1 (le_max_left r1 r2)
  have hmy : ((max r1 r2 : ℕ) : ℝ) < y := by
    rw [Nat.cast_max]
    exact max_lt (Nat.lt_ceil.mp h1.2) (Nat.lt_ceil.mp h2.2)
  rw [int_ind _ y (by linarith) hmy, Nat.cast_max, max_div_div_right hy.le]
  split_ifs <;> simp

/-! ## (2) The links -/

/-- **Link [CrustoCudo] — `eq:crusto` + `eq:cudo`, `v = 2`** (`minarcs.tex` 2640-2665): with
`S = x/WU`, `S₁(U, W) = ∑_{s ≤ S odd} srto(S/s, x/Ws)` (write `d₁ = r₁l`, `d₂ = r₂l`,
`l = (d₁, d₂)`, `m = r₁r₂ls`). An exact identity of finite sums; OPEN. -/
def CrustoCudo : Prop :=
  ∀ x U W : ℝ, 1 ≤ U → 1 ≤ W → U * W ≤ x →
    T2S.s1 x U W = ∑ s ∈ (Finset.Icc 1 ⌊x / (W * U)⌋₊).filter (fun s => Nat.Coprime s 2),
      srto (x / (W * U) / s) (x / W / s)

/-- **Link [Monro2] — `lem:monro`, `v = 2` (`eq:muted` with the error `eq:mudo`)**
(`minarcs.tex` 2667-2690): `|srto(y, z) − (6z/π²)(v/σ(v))·mutedSum(y)| ≤
1.27ζ(3/2)²y√z(1 + 1/√2)(1 − 2^{−3/2})²`, `6v/π²σ(v) = 4/π²`. The `l`-range uses `eq:cudo`'s
`max`; `lem:monro` prints `min`, a typo (the main term's `1 − max(1/2, r₁/y, r₂/y)` is the
length of the `max` range). OPEN. -/
def Monro2 : Prop :=
  ∀ y z : ℝ, 0 < y → 0 < z →
    |srto y z - 4 / Real.pi ^ 2 * z * mutedSum y| ≤
      1.27 * zeta32 ^ 2 * y * Real.sqrt z * (1 + 1 / Real.sqrt 2) *
        (1 - 1 / 2 ^ ((3 : ℝ) / 2)) ^ 2

/-! ## (3) `ζ(3/2) ≤ 3` and `∑_{s odd} s^{−3/2} ≤ 2` -/

theorem rp32 (x : ℝ) (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `1/b³ ≤ (1/a − 1/b)·(2/(b² − a²))` in the form used twice below. -/
theorem cube_step (a b d : ℝ) (ha : 0 < a) (hab : a ≤ b) (hd : 0 < d) (h : b ^ 2 = a ^ 2 + d) :
    1 / (b ^ 2 * b) ≤ 2 / d * (1 / a - 1 / b) := by
  have hb : 0 < b := by linarith
  have e : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e2 : b - a = d / (a + b) := by
    field_simp
    nlinarith
  rw [e, e2, div_div, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : a * b * (a + b) ≤ b ^ 2 * (2 * b) := by nlinarith [mul_le_mul_of_nonneg_left hab hb.le]
  nlinarith [mul_le_mul_of_nonneg_left h1 hd.le]

theorem zeta_psum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤
      3 - 2 / Real.sqrt ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set a := Real.sqrt ((n : ℝ) + 1) with ha
    set b := Real.sqrt ((n : ℝ) + 1 + 1) with hb
    have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
    have ha2 : a ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = (n : ℝ) + 1 + 1 := Real.sq_sqrt (by linarith)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have hstep := cube_step a b 1 ha0 hab one_pos (by rw [ha2, hb2])
    have hr : ((n : ℝ) + 1 + 1) ^ ((3 : ℝ) / 2) = b ^ 2 * b := by
      rw [rp32 _ (by positivity), hb2]
    rw [hr]
    have key : 1 / (b ^ 2 * b) ≤ 2 / a - 2 / b := by
      rw [show (2 : ℝ) / a - 2 / b = 2 / 1 * (1 / a - 1 / b) by ring]
      exact hstep
    calc _ ≤ (3 - 2 / a) + (2 / a - 2 / b) := add_le_add ih key
      _ = 3 - 2 / b := by ring

theorem zeta32_le : zeta32 ≤ 3 := by
  unfold zeta32
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun n => ?_
  rcases n with _ | n
  · simp
  · refine (zeta_psum n).trans ?_
    have : 0 ≤ 2 / Real.sqrt ((n : ℝ) + 1) := by positivity
    linarith

theorem zeta32_nonneg : 0 ≤ zeta32 :=
  tsum_nonneg fun n => by positivity

theorem odd32_psum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 1 / ((2 * (k : ℝ) + 1) * Real.sqrt (2 * (k : ℝ) + 1)) ≤
      2 - 1 / Real.sqrt (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set a := Real.sqrt (2 * (n : ℝ) + 1) with ha
    set b := Real.sqrt (2 * ((n : ℝ) + 1) + 1) with hb
    have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
    have ha2 : a ^ 2 = 2 * (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = 2 * ((n : ℝ) + 1) + 1 := Real.sq_sqrt (by linarith)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have hstep := cube_step a b 2 ha0 hab two_pos (by rw [ha2, hb2]; ring)
    rw [← hb2]
    have key : 1 / (b ^ 2 * b) ≤ 1 / a - 1 / b := by
      rw [show (1 : ℝ) / a - 1 / b = 2 / 2 * (1 / a - 1 / b) by ring]
      exact hstep
    calc _ ≤ (2 - 1 / a) + (1 / a - 1 / b) := add_le_add ih key
      _ = 2 - 1 / b := by ring

/-- `∑_{s ≤ N odd} 1/(s√s) ≤ 2`. -/
theorem odd32_le (N : ℕ) :
    ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s 2),
      1 / ((s : ℝ) * Real.sqrt s) ≤ 2 := by
  have h := M2L.odd_sum_le N (N : ℝ)
    (fun s => if (s : ℝ) ≤ N then 1 / ((s : ℝ) * Real.sqrt s) else 0)
    (fun s hs => by rw [if_neg (not_le.mpr hs)])
    (fun k _ => by split_ifs <;> positivity)
  have e : ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s 2),
      1 / ((s : ℝ) * Real.sqrt s) =
      ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s 2),
        (if (s : ℝ) ≤ N then 1 / ((s : ℝ) * Real.sqrt s) else 0) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    rw [if_pos (by exact_mod_cast this)]
  rw [e]
  refine h.trans ?_
  set K := ⌊((N : ℝ) + 1) / 2⌋₊
  have hle : ∀ k ∈ Finset.range K,
      (if (((2 * k + 1 : ℕ) : ℝ)) ≤ N then 1 / (((2 * k + 1 : ℕ) : ℝ) *
        Real.sqrt ((2 * k + 1 : ℕ) : ℝ)) else 0) ≤
      1 / ((2 * (k : ℝ) + 1) * Real.sqrt (2 * (k : ℝ) + 1)) := by
    intro k _
    split_ifs
    · push_cast
      exact le_rfl
    · positivity
  refine (Finset.sum_le_sum hle).trans ?_
  rcases K with _ | n
  · simp
  · have := odd32_psum n
    have : 0 ≤ 1 / Real.sqrt (2 * (n : ℝ) + 1) := by positivity
    linarith

/-! ## (4) `eq:flatow`, `eq:fleming`: `M2H.MonroFleming` from its links -/

/-- `2·1.27ζ(3/2)²(1 + 1/√2)(1 − 2^{−3/2})² ≤ 22.6418` (it is `≤ 16.31`). -/
theorem kappa_le :
    2 * (1.27 * zeta32 ^ 2 * (1 + 1 / Real.sqrt 2) * (1 - 1 / 2 ^ ((3 : ℝ) / 2)) ^ 2) ≤
      22.6418 := by
  set q := Real.sqrt 2 with hq
  have hq2 : q ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg 2
  have hql : 1.41421 ≤ q := by nlinarith
  have hqu : q ≤ 1.414214 := by nlinarith
  have h32 : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * q := by rw [rp32 2 (by norm_num)]
  rw [h32]
  have hz : zeta32 ^ 2 ≤ 9 := by nlinarith [zeta32_le, zeta32_nonneg]
  have hB : 1 + 1 / q ≤ 1.70711 := by
    have : 1 / q ≤ 0.70711 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hC0 : 0 ≤ 1 - 1 / (2 * q) := by
    have : 1 / (2 * q) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hC1 : 1 - 1 / (2 * q) ≤ 0.64646 := by
    have : 0.35354 ≤ 1 / (2 * q) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  have hC : (1 - 1 / (2 * q)) ^ 2 ≤ 0.64646 ^ 2 := pow_le_pow_left₀ hC0 hC1 2
  have hB0 : 0 ≤ 1 + 1 / q := by positivity
  have hABC : zeta32 ^ 2 * (1 + 1 / q) * (1 - 1 / (2 * q)) ^ 2 ≤ 9 * 1.70711 * 0.64646 ^ 2 :=
    mul_le_mul (mul_le_mul hz hB hB0 (by norm_num)) hC (sq_nonneg _) (by positivity)
  nlinarith

/-- **`M2H.MonroFleming` from `CrustoCudo` and `Monro2`, PROVED** (`eq:flatow` summed with
`∑_{s odd} s^{−3/2} ≤ 2`, `ζ(3/2) ≤ 3`; `eq:fleming` is `muted_eq`). -/
theorem monroFleming_of_links (cc : CrustoCudo) (mo : Monro2) : M2H.MonroFleming := by
  intro x U W hU hW hUW
  have hW0 : 0 < W := by linarith
  have hU0 : 0 < U := by linarith
  have hx : 0 < x := by nlinarith
  have hxW : 0 < x / W := by positivity
  rw [cc x U W hU hW hUW]
  set S := x / (W * U) with hSdef
  have hS0 : 0 < S := by positivity
  set κ := 1.27 * zeta32 ^ 2 * (1 + 1 / Real.sqrt 2) * (1 - 1 / 2 ^ ((3 : ℝ) / 2)) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hterm : ∀ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
      srto (S / s) (x / W / s) ≤
        x / W * (4 / Real.pi ^ 2 * (1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s)))
          + κ * S * Real.sqrt (x / W) * (1 / ((s : ℝ) * Real.sqrt s)) := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    have hs0 : (0 : ℝ) < s := by linarith
    have hy : 0 < S / s := by positivity
    have hz : 0 < x / W / s := by positivity
    have h1 := (abs_le.mp (mo (S / s) (x / W / s) hy hz)).2
    rw [muted_eq (S / s) hy] at h1
    have e1 : ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * (S / s)) =
        ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) := by
      congr 1
      funext u
      rw [mul_div_assoc]
    rw [e1] at h1
    have hsq : Real.sqrt (x / W / s) = Real.sqrt (x / W) / Real.sqrt s :=
      Real.sqrt_div' _ hs0.le
    have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    have e2 : 1.27 * zeta32 ^ 2 * (S / s) * Real.sqrt (x / W / s) * (1 + 1 / Real.sqrt 2) *
        (1 - 1 / 2 ^ ((3 : ℝ) / 2)) ^ 2 =
        κ * S * Real.sqrt (x / W) * (1 / ((s : ℝ) * Real.sqrt s)) := by
      rw [hsq, hκ]
      field_simp
    have e3 : 4 / Real.pi ^ 2 * (x / W / s) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) =
        x / W * (4 / Real.pi ^ 2 * (1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1,
          HC.gYutto 2 (u * S / s))) := by ring
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hodd := odd32_le ⌊S⌋₊
  have hP0 : 0 ≤ x / W * Real.sqrt (x / W) / U := by positivity
  have h2 : κ * S * Real.sqrt (x / W) *
      ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
        1 / ((s : ℝ) * Real.sqrt s) ≤ κ * S * Real.sqrt (x / W) * 2 :=
    mul_le_mul_of_nonneg_left hodd (by positivity)
  have hSP : κ * S * Real.sqrt (x / W) * 2 = 2 * κ * (x / W * Real.sqrt (x / W) / U) := by
    rw [hSdef]
    field_simp
  have h3 : 2 * κ * (x / W * Real.sqrt (x / W) / U) ≤
      22.6418 * (x / W * Real.sqrt (x / W) / U) := by
    refine mul_le_mul_of_nonneg_right ?_ hP0
    have := kappa_le
    rw [hκ]
    linarith
  have hr : 22.6418 * (x / W) ^ ((3 : ℝ) / 2) / U = 22.6418 * (x / W * Real.sqrt (x / W) / U) := by
    rw [rp32 _ hxW]
    ring
  have hc : HC.cortoLHS 2 S = ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
      1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) := rfl
  rw [hr, ← hc]
  linarith

end Principia.Common.TernaryGoldbach.M2F
