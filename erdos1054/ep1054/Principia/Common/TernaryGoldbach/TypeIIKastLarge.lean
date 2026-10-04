/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIISpine

set_option autoImplicit false

/-!
# `T2S.KastLarge` PROVED from Rosser–Schoenfeld 1975, Corollary 2 (5.7)

`eq:kast` above the computed range (`minarcs.tex` 745-751): for `y ≥ 2·758699`,
`∑_{y/2 < p ≤ y} (log p)² ≤ ½ y log y`, "by [RS75, Cor. 2] applied to `x = y`, `y/2`, `2y/3`".

**The literature input** (`RS75Cor2`, NAMED, stated verbatim and no stronger): RS75 (Math. Comp.
29, 243-269), Corollary 2, (5.7): `|θ(x) − x| < x/(40 log x)` for `678407 ≤ x`. We state it for
`678407 < x` only (weaker). The constant is DECAYING (`x/(40 log x)`): a fixed-ratio bound
`|θ(x) − x| ≤ εx` cannot give `eq:kast`, whose slack is `(1 − log 2)/2 · y ≈ 0.153y` against a
loss of order `εy log y`.

**The argument (pointwise, then one sum).** For every prime `p ≤ y`,
`1_{p > y/2}(log p)² ≤ (log p)(L·1_{p ≤ y} − c·1_{p ≤ 2y/3} − b·1_{p ≤ y/2})` with
`L = log y`, `b = log(2y/3)`, `c = log(3/2)`, `L = b + c` (equality below `y/2`; `log p ≤ b`
on `(y/2, 2y/3]`; `log p ≤ L` above). Summing: `S ≤ Lθ(y) − cθ(2y/3) − bθ(y/2)`. Then (5.7) at the
three points, `b, log(y/2) ≥ 10`, `b ≤ 2 log(y/2)`, `c ≥ 1/3` give
`S ≤ ½yL + y/20 − 0.165·c·y ≤ ½yL − 0.005y`. Each `θ` appears ONCE (the book's three-point
form); bounding the two pieces `(y/2, 2y/3]`, `(2y/3, y]` separately would charge `θ(2y/3)` twice
and fails with RS75's constants (`≈ 0.0708y` of error against `≈ 0.0676y` of slack).
-/

namespace Principia.Common.TernaryGoldbach.KLR

open Finset

/-- **NAMED (literature) — Rosser–Schoenfeld 1975, Corollary 2, (5.7)** (Math. Comp. 29 (1975),
243-269, p. 266): `|θ(x) − x| < x/(40 log x)` if `678407 ≤ x`; stated here for `678407 < x`. -/
def RS75Cor2 : Prop :=
  ∀ x : ℝ, 678407 < x → |Chebyshev.theta x - x| < x / (40 * Real.log x)

/-- The prime indicator weight `1_{p prime, p ≤ t} log p`. -/
noncomputable def wt (t : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ (p : ℝ) ≤ t then Real.log p else 0

/-- `θ(t) = ∑_{1 ≤ p ≤ ⌊y⌋} 1_{p prime, p ≤ t} log p` for `0 ≤ t ≤ y`. -/
theorem theta_eq_sum_wt (t y : ℝ) (ht : 0 ≤ t) (hty : t ≤ y) :
    Chebyshev.theta t = ∑ p ∈ Icc 1 ⌊y⌋₊, wt t p := by
  unfold wt
  rw [← Finset.sum_filter, Chebyshev.theta]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  have hfl : ⌊t⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hty
  constructor
  · rintro ⟨⟨h0, hp⟩, hpr⟩
    exact ⟨⟨h0, hp.trans hfl⟩, hpr, (Nat.le_floor_iff ht).mp hp⟩
  · rintro ⟨⟨h0, -⟩, hpr, hp⟩
    exact ⟨⟨h0, (Nat.le_floor_iff ht).mpr hp⟩, hpr⟩

/-- **The pointwise inequality**, for `1 ≤ p ≤ y`. -/
theorem kast_pt (y : ℝ) (hy : 4 ≤ y) (p : ℕ) (hp1 : 1 ≤ p) (hpy : (p : ℝ) ≤ y) :
    (if p.Prime ∧ y / 2 < (p : ℝ) then Real.log p ^ 2 else 0) ≤
      Real.log y * wt y p - Real.log (3 / 2) * wt (2 * y / 3) p -
        Real.log (2 * y / 3) * wt (y / 2) p := by
  have hL : Real.log y = Real.log (2 * y / 3) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hp0
  unfold wt
  by_cases hpr : p.Prime
  · by_cases h2 : (p : ℝ) ≤ y / 2
    · have h3 : (p : ℝ) ≤ 2 * y / 3 := by linarith
      have hn : ¬ y / 2 < (p : ℝ) := not_lt.mpr h2
      simp only [hpr, hn, h2, h3, hpy, and_self, and_false, if_true, if_false]
      rw [hL]
      linarith
    · have hlt : y / 2 < (p : ℝ) := lt_of_not_ge h2
      simp only [hpr, hlt, h2, hpy, and_self, and_false, if_true, if_false, true_and]
      by_cases h3 : (p : ℝ) ≤ 2 * y / 3
      · simp only [h3, if_true]
        have hle : Real.log p ≤ Real.log (2 * y / 3) := Real.log_le_log (by linarith) h3
        rw [hL]
        nlinarith
      · simp only [h3, if_false]
        have hle : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
        nlinarith
  · simp only [hpr, false_and, if_false]
    simp

/-- `S ≤ log y · θ(y) − log(3/2) · θ(2y/3) − log(2y/3) · θ(y/2)`. -/
theorem kast_sum_le (y : ℝ) (hy : 4 ≤ y) :
    ∑ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ y / 2 < (p : ℝ)),
        Real.log p ^ 2 ≤
      Real.log y * Chebyshev.theta y - Real.log (3 / 2) * Chebyshev.theta (2 * y / 3) -
        Real.log (2 * y / 3) * Chebyshev.theta (y / 2) := by
  rw [Finset.sum_filter, theta_eq_sum_wt y y (by linarith) le_rfl,
    theta_eq_sum_wt (2 * y / 3) y (by linarith) (by linarith),
    theta_eq_sum_wt (y / 2) y (by linarith) (by linarith), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mem_Icc] at hp
  exact kast_pt y hy p hp.1
    ((Nat.cast_le.mpr hp.2).trans (Nat.floor_le (by linarith)))

/-- `log z ≥ 10` for `z ≥ 30000`. -/
theorem log_ge_ten (z : ℝ) (hz : 30000 ≤ z) : 10 ≤ Real.log z := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h10 : Real.exp 10 = Real.exp 1 ^ 10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hp : Real.exp 1 ^ 10 ≤ (2.7182818286 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 10
  rw [h10]
  linarith [show (2.7182818286 : ℝ) ^ 10 ≤ 30000 by norm_num]

/-- **`T2S.KastLarge`, PROVED from RS75 Corollary 2 (5.7).** -/
theorem kastLarge_of_rs75 (rs : RS75Cor2) : T2S.KastLarge := by
  intro y hy
  have hy4 : 4 ≤ y := by linarith
  refine (kast_sum_le y hy4).trans ?_
  set L := Real.log y with hLdef
  set b := Real.log (2 * y / 3) with hbdef
  set a := Real.log (y / 2) with hadef
  set c := Real.log (3 / 2) with hcdef
  have hL : L = b + c := by
    rw [hLdef, hbdef, hcdef, ← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hb : b = a + Real.log (4 / 3) := by
    rw [hbdef, hadef, ← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have h43 : Real.log (4 / 3) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    linarith
  have hc : 1 / 3 ≤ c := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    rw [hcdef]
    norm_num at this ⊢
    linarith
  have ha10 : 10 ≤ a := log_ge_ten _ (by linarith)
  have hb10 : 10 ≤ b := log_ge_ten _ (by linarith)
  have hL0 : 0 < L := by linarith
  have hy0 : 0 < y := by linarith
  -- (5.7) at y, 2y/3, y/2
  have r1 := (abs_lt.mp (rs y (by linarith))).2
  have r2 := (abs_lt.mp (rs (2 * y / 3) (by linarith))).1
  have r3 := (abs_lt.mp (rs (y / 2) (by linarith))).1
  rw [← hLdef] at r1
  rw [← hbdef] at r2
  rw [← hadef] at r3
  set T1 := Chebyshev.theta y
  set T2 := Chebyshev.theta (2 * y / 3)
  set T3 := Chebyshev.theta (y / 2)
  have e1 : L * (y / (40 * L)) = y / 40 := by
    field_simp
  have k1 : L * T1 ≤ L * y + y / 40 := by
    have := mul_le_mul_of_nonneg_left (show T1 ≤ y + y / (40 * L) by linarith) hL0.le
    nlinarith
  have k2 : 2 * y / 3 * (399 / 400) ≤ T2 := by
    have : 2 * y / 3 / (40 * b) ≤ 2 * y / 3 / 400 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith
  have k3 : b * (y / 2) - y / 40 ≤ b * T3 := by
    have hb0 : 0 ≤ b := by linarith
    have h := mul_le_mul_of_nonneg_left (show y / 2 - y / 2 / (40 * a) ≤ T3 by linarith) hb0
    have hq : b * (y / 2 / (40 * a)) ≤ y / 40 := by
      rw [show b * (y / 2 / (40 * a)) = (b / a) * (y / 80) by field_simp; ring]
      have hba : b / a ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      nlinarith
    nlinarith
  have kc : c * (2 * y / 3 * (399 / 400)) ≤ c * T2 :=
    mul_le_mul_of_nonneg_left k2 (by linarith)
  have hcy : y / 3 ≤ c * y := by nlinarith
  rw [hL] at k1 ⊢
  nlinarith

end Principia.Common.TernaryGoldbach.KLR
