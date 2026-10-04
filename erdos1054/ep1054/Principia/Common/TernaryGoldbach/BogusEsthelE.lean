/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SecI2ArithD
import Principia.Common.TernaryGoldbach.EsthelEta2E
import Principia.Common.TernaryGoldbach.TrompaisCamelo

set_option autoImplicit false

/-!
# `MPBD.EsthelBogusED` PROVED -- `eq:esthel3`, the `|δ| ≥ 1/2c₂` branch, corrected

The weighted sum `∑ (log m)T(m)` over the `m ≤ D = UV` other than (`q ∣ m` and `m ≤ M`), for any
`T` obeying `eq:trompais`, re-derived from the `lem:bosta2` pieces of `EsthelEta2E.lean`
(`Q = x/|δ|q` real, `M = mR = min(Q/2, D)`, `Y = Q/2`):

* `m ≤ M`, `q ∤ m`: `log m ≤ log M` times `MPE2.piece2E`;
* `Y < m ≤ D` (when `D > Y`): `piece3W`, the windows of `MPE2.piece3E` (length `q'`, the second
  approximation of `MPE2.second_approx`) each weighted by `log` of its TOP end
  `min(D, Y + (j + 1)q')` -- the book's `eq:gator1`/`eq:gator2` weight by the bottom end, which is
  not an upper bound for the increasing `log m`. The main terms telescope (`tel_W`) against
  `G(t) = t log t - t` (`gB`): window `j + 1` is compared with `[Y + jq', Y + (j + 1)q']`, so the
  endpoint mismatch costs `q'(f(j + 2) - f(j))`, `f(i) = log min(D, Y + iq')`, which telescopes to
  `≤ 2q' log(D/Y)` -- no `log D` factor.

Then `(2√c₀/π)·Y log Y - (2√(c₀c₁)/π)G(Y) ≤ (2√(c₀c₁)/π)Y`, `x/2Y = |δ|q`, `D/Y = 2D/K` and
`q' ≤ (1 + ε)K` give `MPBD.tvorogD` exactly. Consequently

```
 secI2At_of_mainD : MPc.SecI2At from HC.CameloGridCited, HC.WollustCited, MPBD.MainBogusEta2C
```
-/

namespace Principia.Common.TernaryGoldbach.MPBE

open Real Finset Principia.Common.TrigSumN
open Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPE2 Principia.Common.TernaryGoldbach.MPBD

/-! ## (1) The antiderivative `G(t) = t log t - t` -/

/-- `G(t) = t log t - t` (`= t log(t/e)`, `G' = log`). -/
noncomputable def gB (t : ℝ) : ℝ := t * Real.log t - t

/-- **`G` dominates the left-endpoint rule for `log`**: `(b - a)log a ≤ G(b) - G(a)`. -/
theorem gB_step (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : (b - a) * Real.log a ≤ gB b - gB a := by
  unfold gB
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h
  have h2 : b * (1 - a / b) ≤ b * (Real.log b - Real.log a) := mul_le_mul_of_nonneg_left h hb.le
  have e : b * (1 - a / b) = b - a := by field_simp
  nlinarith

/-- `G` is increasing on `[1, ∞)`. -/
theorem gB_mono (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : gB a ≤ gB b := by
  have h := gB_step a b (by linarith) hab
  have := mul_nonneg (sub_nonneg.mpr hab) (Real.log_nonneg ha)
  linarith

/-- `G(D) = D log(D/e)`. -/
theorem gB_eq (D : ℝ) (hD : 0 < D) : gB D = D * Real.log (D / Real.exp 1) := by
  unfold gB
  rw [Real.log_div hD.ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-- **The top-end weights telescope**: for `Kq + Y ≤ D`, `Y ≥ 1`,
`∑_{j<K} q·log min(D, (j + 2)q + Y) ≤ G(D) - G(Y) + 2q(log D - log Y)`. -/
theorem tel_W (q Y D : ℝ) (K : ℕ) (hq : 0 < q) (hY1 : 1 ≤ Y) (hKD : (K : ℝ) * q + Y ≤ D) :
    ∑ j ∈ range K, q * Real.log (min D (((j : ℝ) + 2) * q + Y)) ≤
      gB D - gB Y + 2 * q * (Real.log D - Real.log Y) := by
  set f : ℕ → ℝ := fun i => Real.log (min D ((i : ℝ) * q + Y)) with hf_def
  have hY0 : 0 < Y := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hYD : Y ≤ D := by have := mul_nonneg hK0 hq.le; linarith
  have hfle : ∀ i, f i ≤ Real.log D := by
    intro i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h1 : 0 < min D ((i : ℝ) * q + Y) := lt_min (by linarith) (by positivity)
    exact Real.log_le_log h1 (min_le_left _ _)
  have hf0 : f 0 = Real.log Y := by
    simp only [hf_def, Nat.cast_zero, zero_mul, zero_add]
    rw [min_eq_right hYD]
  have hf1 : Real.log Y ≤ f 1 := by
    simp only [hf_def, Nat.cast_one, one_mul]
    exact Real.log_le_log hY0 (le_min hYD (by linarith))
  have hstep : ∀ j ∈ range K, q * Real.log (min D (((j : ℝ) + 2) * q + Y)) ≤
      (gB (((j + 1 : ℕ) : ℝ) * q + Y) - gB ((j : ℝ) * q + Y)) + q * (f (j + 2) - f j) := by
    intro j hj
    have hjK : j + 1 ≤ K := Finset.mem_range.mp hj
    have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjK' : (j : ℝ) + 1 ≤ K := by exact_mod_cast hjK
    have ha : 0 < (j : ℝ) * q + Y := by positivity
    have hjD : (j : ℝ) * q + Y ≤ D := by nlinarith
    have hg := gB_step ((j : ℝ) * q + Y) (((j : ℝ) + 1) * q + Y) ha (by nlinarith)
    have e1 : ((j : ℝ) + 1) * q + Y - ((j : ℝ) * q + Y) = q := by ring
    rw [e1] at hg
    have hfj : f j = Real.log ((j : ℝ) * q + Y) := by
      simp only [hf_def]
      rw [min_eq_right hjD]
    have hfj2 : f (j + 2) = Real.log (min D (((j : ℝ) + 2) * q + Y)) := by
      simp only [hf_def]
      push_cast
      ring_nf
    have ec : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [ec, hfj2, hfj]
    linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_sub (fun j => gB ((j : ℝ) * q + Y))]
  have etel : ∑ j ∈ range K, (f (j + 2) - f j) = (f (K + 1) - f 1) + (f K - f 0) := by
    have h1 : ∑ j ∈ range K, (f (j + 2) - f j) =
        ∑ j ∈ range K, (f (j + 1 + 1) - f (j + 1)) + ∑ j ∈ range K, (f (j + 1) - f j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, Finset.sum_range_sub (fun j => f (j + 1)), Finset.sum_range_sub f]
  rw [etel]
  have hKD' : 1 ≤ (K : ℝ) * q + Y := by have := mul_nonneg hK0 hq.le; linarith
  have hG := gB_mono ((K : ℝ) * q + Y) D hKD' hKD
  have e0 : ((0 : ℕ) : ℝ) * q + Y = Y := by push_cast; ring
  simp only [e0]
  have h1 := hfle (K + 1)
  have h2 := hfle K
  have h3 : q * ((f (K + 1) - f 1) + (f K - f 0)) ≤ q * (2 * (Real.log D - Real.log Y)) :=
    mul_le_mul_of_nonneg_left (by rw [hf0]; linarith) hq.le
  linarith

/-! ## (2) The weighted windows -/

/-- **A window under a bounded weight**: if every `d` of the window with `d ≤ N` has
`log d ≤ w`, the `log`-weighted window sum is at most `w` times the plain one (`t ≥ 0`). -/
theorem win_le (x α : ℝ) (t : ℕ → ℝ) (ht : TB x α t) (lo hi N : ℕ) (w : ℝ)
    (hw : ∀ d, lo < d → d ≤ hi → d ≤ N → Real.log d ≤ w) :
    ∑ d ∈ Ioc lo hi, (if d ≤ N ∧ True then Real.log d * t d else 0) ≤
      w * ∑ d ∈ Ioc lo hi, (if d ≤ N ∧ True then t d else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd' := Finset.mem_Ioc.mp hd
  split_ifs with h
  · exact mul_le_mul_of_nonneg_right (hw d hd'.1 hd'.2 h.1) (ht d (by omega)).1
  · rw [mul_zero]

set_option maxHeartbeats 1000000 in
-- the window bookkeeping of `MPE2.piece3E` plus the weights and the telescoped sum
/-- **Piece 3W -- `eq:gator1` + `eq:gator2`, corrected**: for windows of length `q'` from
`1 ≤ Y ≤ D` (`q'` as in `MPE2.piece3E`), `∑_{Y < m ≤ D} (log m)T(m) ≤
log D·(3c₁/2)(x/2Y)(2 + ((1 + ε)/ε)log⁺(D/Y)) + (2√(c₀c₁)/π)((1 + ε)(2Y)√(3 + 2ε)·
log min(D, (3 + 2ε)Y) + G(D) - G(Y) + 2(1 + ε)(2Y)log⁺(D/Y) + ((1 + ε)(2Y)/2)log⁺(D/Y)log D)`. -/
theorem piece3W (x α β Q D Y ε : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hY1 : 1 ≤ Y) (hYD : Y ≤ D) (hε : 0 < ε) (hqlo : ε * (2 * Y) ≤ (1 + ε) * q)
    (hqhi : (q : ℝ) ≤ 2 * (1 + ε) * Y) (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ Ioc ⌊Y⌋₊ ⌊D⌋₊, Real.log d * t d ≤
      Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y))) +
        2 * √(c0 * c1 x D) / π *
          ((1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y)) +
            (gB D - gB Y) + 2 * ((1 + ε) * (2 * Y)) * logp (D / Y) +
            (1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hY0 : 0 < Y := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hc1' : 0 ≤ c1 x D := by linarith
  have hlp : 0 ≤ logp (D / Y) := le_max_right _ _
  have h3e : 0 ≤ √(3 + 2 * ε) := Real.sqrt_nonneg _
  have hLD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hGD : 0 ≤ gB D - gB Y := by have := gB_mono Y D hY1 hYD; linarith
  have hmin1 : 1 ≤ min D ((3 + 2 * ε) * Y) := le_min hD1 (by nlinarith)
  have hLm0 : 0 ≤ Real.log (min D ((3 + 2 * ε) * Y)) := Real.log_nonneg hmin1
  set s := √(c0 * c1 x D) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hRHS : 0 ≤ Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y))) +
      2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y)) +
        (gB D - gB Y) + 2 * ((1 + ε) * (2 * Y)) * logp (D / Y) +
        (1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D) := by
    have h1 : 0 ≤ 3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y)) := by
      positivity
    have h2 : 0 ≤ (1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y)) +
        (gB D - gB Y) + 2 * ((1 + ε) * (2 * Y)) * logp (D / Y) +
        (1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D := by
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + ε) * (2 * Y)) h3e) hLm0
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((1 + ε) * (2 * Y))) hlp
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + ε) * (2 * Y) / 2) hlp) hLD
      linarith
    exact add_nonneg (mul_nonneg hLD h1) (mul_nonneg (by positivity) h2)
  set r := ⌊Y⌋₊ with hr_def
  set N := ⌊D⌋₊ with hN_def
  set J := (N - r + q - 1) / q with hJ_def
  obtain ⟨hJ1, hJ2⟩ := cdiv_spec (N - r) q hq
  rw [← hJ_def] at hJ1 hJ2
  have hNJ : N ≤ r + J * q := by
    generalize J * q = P at hJ1 hJ2 ⊢
    omega
  have hfil : (Ioc r N).filter (fun _ => True) = Ioc r N :=
    Finset.filter_true_of_mem (fun _ _ => trivial)
  rw [← hfil, sum_filter_windows (fun d => Real.log d * t d) (fun _ => True) r q J N hNJ]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · rw [hJ0]
    simpa using hRHS
  obtain ⟨K, hK⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hNr : r + 1 ≤ N := by
    by_contra hcon
    have : N - r = 0 := by omega
    rw [this] at hJ_def
    have : J = 0 := by
      rw [hJ_def, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    omega
  have hrY : (r : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hND : (N : ℝ) ≤ D := Nat.floor_le (by linarith)
  have hKr : (K : ℝ) * q + Y ≤ D := by
    rw [hK] at hJ2
    have h1 : K * q + r + 1 ≤ N := by
      have e : (K + 1) * q = K * q + q := by ring
      rw [e] at hJ2
      generalize K * q = P at hJ2 ⊢
      omega
    have h2 : (K : ℝ) * q + r + 1 ≤ N := by exact_mod_cast h1
    have h3 : Y < r + 1 := Nat.lt_floor_add_one Y
    linarith
  have hKr0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [hK, Finset.sum_range_succ']
  -- the weight of window `i` is at most `log min(D, Y + (i + 1)q')`
  have hwt : ∀ i : ℕ, ∀ d, r + i * q < d → d ≤ r + i * q + q → d ≤ N →
      Real.log d ≤ Real.log (min D (((i : ℝ) + 1) * q + Y)) := by
    intro i d h1 h2 h3
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    refine Real.log_le_log (by linarith) (le_min ?_ ?_)
    · have : (d : ℝ) ≤ N := by exact_mod_cast h3
      linarith
    · have : (d : ℝ) ≤ r + i * q + q := by exact_mod_cast h2
      have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      nlinarith
  have hwt0 : ∀ i : ℕ, 0 ≤ Real.log (min D (((i : ℝ) + 1) * q + Y)) := by
    intro i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact Real.log_nonneg (le_min hD1 (by nlinarith))
  have hwD : ∀ i : ℕ, Real.log (min D (((i : ℝ) + 1) * q + Y)) ≤ Real.log D := by
    intro i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact Real.log_le_log (lt_min (by linarith) (by positivity)) (min_le_left _ _)
  -- windows `j + 1`, `j < K`
  have hwin : ∀ j ∈ range K,
      ∑ d ∈ Ioc (r + (j + 1) * q) (r + (j + 1) * q + q),
          (if d ≤ N ∧ True then Real.log d * t d else 0) ≤
        Real.log D * ((3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) *
            (1 / (((j : ℝ) + 1) * q + Y))) +
          2 * s / π * (q * Real.log (min D (((j : ℝ) + 2) * q + Y))) := by
    intro j hj
    have hjK : j + 1 ≤ K := Finset.mem_range.mp hj
    have hjK' : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hjK
    have hjD : ((j + 1 : ℕ) : ℝ) * q + Y ≤ D := by
      have := mul_le_mul_of_nonneg_right hjK' hq0.le
      linarith
    have hg := gwin x α β Q D Y a q hq hcop hα hβ hqQ hx hY0 t ht (j + 1) hjD
    have hsq := sqrt_ws x (c1 x D) Y q j hx hc1' hq0 hY0
    have hjR : 0 < ((j : ℝ) + 1) * q + Y := by positivity
    have hg' : ∑ d ∈ Ioc (r + (j + 1) * q) (r + (j + 1) * q + q),
        (if d ≤ N ∧ True then t d else 0) ≤
        (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + Y)) +
          2 * q / π * s := by
      refine hg.trans ?_
      have h4 : 4 * q / π * √(c1 x D * x / (2 * (((j + 1 : ℕ) : ℝ) * q + Y)) *
          (c0 * ((((j + 1 : ℕ) : ℝ) + 1) * q + Y) / (2 * x))) ≤
          4 * q / π * (s / 2 * (1 + q / (2 * ((j + 1) * q + Y)))) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have e : 3 * (c1 x D * x / (2 * (((j + 1 : ℕ) : ℝ) * q + Y))) +
          4 * q / π * (s / 2 * (1 + q / (2 * ((j + 1) * q + Y)))) =
          (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + Y)) +
            2 * q / π * s := by
        push_cast
        field_simp
        ring
      linarith
    have hw := win_le x α t ht (r + (j + 1) * q) (r + (j + 1) * q + q) N
      (Real.log (min D ((((j + 1 : ℕ) : ℝ) + 1) * q + Y)))
      (fun d h1 h2 h3 => hwt (j + 1) d h1 h2 h3)
    have ec : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
    rw [ec] at hw
    have hw0 : 0 ≤ Real.log (min D (((j : ℝ) + 2) * q + Y)) := by
      have := hwt0 (j + 1); rw [ec] at this; exact this
    have hwD' : Real.log (min D (((j : ℝ) + 2) * q + Y)) ≤ Real.log D := by
      have := hwD (j + 1); rw [ec] at this; exact this
    refine hw.trans ((mul_le_mul_of_nonneg_left hg' hw0).trans ?_)
    have hc' : 0 ≤ (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) *
        (1 / (((j : ℝ) + 1) * q + Y)) := by positivity
    have h5 := mul_le_mul_of_nonneg_right hwD' hc'
    have e3 : Real.log (min D (((j : ℝ) + 2) * q + Y)) *
        ((3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + Y)) +
          2 * q / π * s) =
        Real.log (min D (((j : ℝ) + 2) * q + Y)) *
            ((3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + Y))) +
          2 * s / π * (q * Real.log (min D (((j : ℝ) + 2) * q + Y))) := by ring
    linarith [e3]
  -- window `0`
  have hw0 := gwin x α β Q D Y a q hq hcop hα hβ hqQ hx hY0 t ht 0
    (by have := mul_nonneg hKr0 hq0.le; push_cast; linarith)
  have hsq0 := sqrt_w0e x (c1 x D) Y ε q hx hc1' hε.le hqhi hY0
  rw [← hs_def] at hsq0
  have hW0 := win_le x α t ht (r + 0 * q) (r + 0 * q + q) N
    (Real.log (min D ((((0 : ℕ) : ℝ) + 1) * q + Y))) (fun d h1 h2 h3 => hwt 0 d h1 h2 h3)
  have e00 : (((0 : ℕ) : ℝ) + 1) * q + Y = q + Y := by push_cast; ring
  rw [e00] at hW0
  have hL0 : 0 ≤ Real.log (min D (q + Y)) := by have := hwt0 0; rw [e00] at this; exact this
  have hL0D : Real.log (min D (q + Y)) ≤ Real.log D := by
    have := hwD 0; rw [e00] at this; exact this
  have hL0m : Real.log (min D (q + Y)) ≤ Real.log (min D ((3 + 2 * ε) * Y)) :=
    Real.log_le_log (lt_min (by linarith) (by positivity))
      (min_le_min le_rfl (by linarith))
  have hA0 : 3 * (c1 x D * x / (2 * (((0 : ℕ) : ℝ) * q + Y))) =
      3 / 2 * c1 x D * (x / (2 * Y)) * 2 := by
    push_cast
    rw [zero_mul, zero_add]
    field_simp
  rw [hA0] at hw0
  have h40 := mul_le_mul_of_nonneg_left hsq0 (by positivity : (0 : ℝ) ≤ 4 * q / π)
  have hB0 : ∑ d ∈ Ioc (r + 0 * q) (r + 0 * q + q), (if d ≤ N ∧ True then t d else 0) ≤
      3 / 2 * c1 x D * (x / (2 * Y)) * 2 + 2 * s / π * (q * √(3 + 2 * ε)) := by
    have e : 4 * q / π * (s / 2 * √(3 + 2 * ε)) = 2 * s / π * (q * √(3 + 2 * ε)) := by ring
    linarith
  have hB00 : 0 ≤ 3 / 2 * c1 x D * (x / (2 * Y)) * 2 := by positivity
  have hwin0 : ∑ d ∈ Ioc (r + 0 * q) (r + 0 * q + q),
      (if d ≤ N ∧ True then Real.log d * t d else 0) ≤
      Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * 2) +
        2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y))) := by
    refine hW0.trans ((mul_le_mul_of_nonneg_left hB0 hL0).trans ?_)
    have h1 := mul_le_mul_of_nonneg_right hL0D hB00
    have h2 : Real.log (min D (q + Y)) * (2 * s / π * (q * √(3 + 2 * ε))) ≤
        2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y))) := by
      have e : Real.log (min D (q + Y)) * (2 * s / π * (q * √(3 + 2 * ε))) =
          2 * s / π * ((q * √(3 + 2 * ε)) * Real.log (min D (q + Y))) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_right
        (by linarith) h3e) hL0m hL0 (by positivity)) (by positivity)
    nlinarith
  -- the sum over the windows `j + 1`
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hH := harm_le q Y hq0 hY0 K
  set H := ∑ j ∈ range K, 1 / (((j : ℝ) + 1) * q + Y) with hH_def
  have htel := tel_W q Y D K hq0 hY1 hKr
  set Lg := Real.log ((K * q + Y) / Y) with hLg_def
  have hLg0 : 0 ≤ Lg := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hY0]
    have := mul_nonneg hKr0 hq0.le
    linarith
  have hLg1 : Lg ≤ logp (D / Y) := by
    refine log_le_logp _ _ (by positivity) ?_
    exact div_le_div_of_nonneg_right hKr hY0.le
  have hcoef : 0 ≤ 3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2) := by positivity
  have hH2 := mul_le_mul_of_nonneg_left hH hcoef
  have hinvq : 1 / (q : ℝ) ≤ (1 + ε) / ε * (1 / (2 * Y)) := by
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hq0 (by positivity), one_mul]
    linarith
  have hlogDY : Real.log D - Real.log Y ≤ logp (D / Y) := by
    rw [← Real.log_div (by linarith) hY0.ne']
    exact le_max_left _ _
  -- the arithmetic
  have hA : Real.log D * ((3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * H) ≤
      Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y))) +
        2 * s / π * ((1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D) := by
    have h1 : (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * H ≤
        (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / q * Lg) := hH2
    have e : (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / q * Lg) =
        3 / 2 * c1 x D * x * (1 / q) * Lg + 2 * s / π * (q / 2 * Lg) := by
      field_simp
    have h2 : 3 / 2 * c1 x D * x * (1 / q) * Lg ≤
        3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y)) := by
      have h3 : 3 / 2 * c1 x D * x * (1 / q) * Lg ≤
          3 / 2 * c1 x D * x * ((1 + ε) / ε * (1 / (2 * Y))) * logp (D / Y) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hinvq (by positivity)) hLg1 hLg0 (by positivity)
      have e1 : 3 / 2 * c1 x D * x * ((1 + ε) / ε * (1 / (2 * Y))) * logp (D / Y) =
          3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y)) := by
        field_simp
      linarith
    have h4 : q / 2 * Lg ≤ (1 + ε) * (2 * Y) / 2 * logp (D / Y) :=
      mul_le_mul (by linarith) hLg1 hLg0 (by positivity)
    have h5 : 2 * s / π * (q / 2 * Lg) ≤ 2 * s / π * ((1 + ε) * (2 * Y) / 2 * logp (D / Y)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 := mul_le_mul_of_nonneg_left (h1.trans (le_of_eq e)) hLD
    have h7 := mul_le_mul_of_nonneg_left (add_le_add h2 h5) hLD
    have e2 : Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y)) +
        2 * s / π * ((1 + ε) * (2 * Y) / 2 * logp (D / Y))) =
        Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y))) +
          2 * s / π * ((1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D) := by ring
    linarith
  have hT : 2 * s / π * ∑ j ∈ range K, q * Real.log (min D (((j : ℝ) + 2) * q + Y)) ≤
      2 * s / π * ((gB D - gB Y) + 2 * ((1 + ε) * (2 * Y)) * logp (D / Y)) := by
    refine mul_le_mul_of_nonneg_left (htel.trans ?_) (by positivity)
    have h1 : 2 * q * (Real.log D - Real.log Y) ≤ 2 * ((1 + ε) * (2 * Y)) * logp (D / Y) := by
      have hLL : 0 ≤ Real.log D - Real.log Y := by
        have := Real.log_le_log hY0 hYD; linarith
      exact mul_le_mul (by linarith) hlogDY hLL (by positivity)
    linarith
  have e4 : Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y))) +
      2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y)) +
        (gB D - gB Y) + 2 * ((1 + ε) * (2 * Y)) * logp (D / Y) +
        (1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D) =
      (Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * 2) +
        2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Y)))) +
      ((Real.log D * (3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y))) +
        2 * s / π * ((1 + ε) * (2 * Y) / 2 * logp (D / Y) * Real.log D)) +
        2 * s / π * ((gB D - gB Y) + 2 * ((1 + ε) * (2 * Y)) * logp (D / Y))) := by ring
  rw [e4]
  have hfin := add_le_add hA hT
  linarith

/-! ## (3) The assembly -/

set_option maxHeartbeats 1000000 in
-- the assembly of `MPE2.esthelEta2E_holds` plus the weighted arithmetic
/-- **`MPBD.EsthelBogusED`, PROVED**: `Q = x/|δ|q` (real), `Y = Q/2`, `M = mR = min(Y, D)`;
`log m ≤ log M` times `MPE2.piece2E` on `m ≤ M`, `q ∤ m`; when `D > Y`, `piece3W` on
`Y < m ≤ D` with the second approximation of `MPE2.second_approx`. -/
theorem esthelBogusED_holds : EsthelBogusED := by
  intro x β δ Q0 U V a q hq hg h2 hδ hqQ hQ hU hV hDx T hT hbig ε hε hε1
  set D := U * V with hD_def
  have hD1 : 1 ≤ D := by rw [hD_def]; nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : 0 < x := by linarith
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hd : 0 < |δ| := lt_of_lt_of_le (by positivity) hbig
  have h0 : δ ≠ 0 := abs_pos.mp hd
  obtain ⟨Qr, hQr_def⟩ : ∃ Qr : ℝ, Qr = x / (|δ| * q) := ⟨_, rfl⟩
  have hQr0 : 0 < Qr := by rw [hQr_def]; positivity
  have hδ' : |δ| * q * Q0 ≤ x := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδ
    linarith
  have hQ0r : Q0 ≤ Qr := by
    rw [hQr_def, le_div_iff₀ (by positivity)]
    linarith
  have hqr : (q : ℝ) ≤ Qr := hqQ.trans hQ0r
  have hdc : 1 ≤ 2 * c2 * |δ| := by
    rw [div_le_iff₀ (by positivity)] at hbig
    linarith
  have hqq : (q : ℝ) ^ 2 ≤ 2 * c2 * x := by
    have h1 : (q : ℝ) * Q0 ≤ 2 * c2 * x := by
      have : (q : ℝ) * Q0 * 1 ≤ q * Q0 * (2 * c2 * |δ|) :=
        mul_le_mul_of_nonneg_left hdc (by positivity)
      nlinarith
    have h2 : (q : ℝ) ^ 2 ≤ q * Q0 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hqQ hq0.le
    linarith
  have hα1 : 2 * β = a / q + (δ / |δ|) / (q * Qr) := by
    rw [h2, hQr_def]
    congr 1
    field_simp
  have hθ : |(δ / |δ|)| ≤ 1 := by rw [abs_div, abs_abs, div_self hd.ne']
  have hαq : |2 * β - a / q| = 1 / (q * Qr) := by
    rw [h2, add_sub_cancel_left, hQr_def, abs_div, abs_of_pos hx]
    field_simp
  obtain ⟨Y, hY_def⟩ : ∃ Y : ℝ, Y = Qr / 2 := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hY_def]; exact half_pos hQr0
  have hY1 : 1 ≤ Y := by rw [hY_def]; linarith
  have hmR : mR x δ q D = min Y D := by
    unfold mR
    rw [if_neg h0, hY_def, hQr_def]
    congr 1
    field_simp
  rw [hmR]
  set M := min Y D with hM_def
  have hM0 : 0 ≤ M := le_min hY0.le (by linarith)
  have hMY : M ≤ Y := min_le_left _ _
  have hMc : (q : ℝ) * M ≤ c2 * x := by
    have h1 : (q : ℝ) * M ≤ q * Y := mul_le_mul_of_nonneg_left hMY hq0.le
    have h2 : (q : ℝ) * Y = x / (2 * |δ|) := by
      rw [hY_def, hQr_def]
      field_simp
    have h3 : x / (2 * |δ|) ≤ c2 * x := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have htb := tb_of_tromB x β T hT
  have hp2 := piece2E x (2 * β) (δ / |δ|) Qr M a q hq hg hα1 hθ hx hM0 (by linarith) hMc hqq T
    htb
  -- the weighted function
  set f : ℕ → ℝ := fun d => if 1 ≤ d then Real.log d * T d else 0 with hf_def
  have hf0 : ∀ d, 0 ≤ f d := by
    intro d
    simp only [hf_def]
    split_ifs with h
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast h)) (htb d h).1
    · exact le_rfl
  have ef : ∀ (S : Finset ℕ), (∀ d ∈ S, 1 ≤ d) → ∑ d ∈ S, f d = ∑ d ∈ S, Real.log d * T d := by
    intro S hS
    exact Finset.sum_congr rfl fun d hd => if_pos (hS d hd)
  have hpos1 : ∀ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), 1 ≤ d := by
    intro d hd
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
    omega
  -- `log m ≤ log M` on `m ≤ M`
  have hA : ∑ d ∈ (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d), Real.log d * T d ≤
      Real.log M * (2 * √c0 / π * M + 35 * c0 * c2 / (3 * π ^ 2) * q) := by
    have hmem : ∀ d ∈ (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d), 1 ≤ d ∧ (d : ℝ) ≤ M := by
      intro d hd
      have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      refine ⟨by omega, ?_⟩
      have : (d : ℝ) ≤ ⌊M⌋₊ := by exact_mod_cast h.2
      linarith [Nat.floor_le hM0]
    have hw := wsum_le _ T M hmem (fun d hd => (htb d (hmem d hd).1).1)
    have hMone : 1 ≤ M := le_min hY1 hD1
    exact hw.trans (mul_le_mul_of_nonneg_left hp2 (Real.log_nonneg hMone))
  -- the common pieces of `tvorogD`
  set s := √(c0 * c1 x D) with hs_def
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hs1 : √c0 ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 ≤ √c0 := Real.sqrt_nonneg _
  have hs0' : 0 ≤ s := hs0.trans hs1
  have hLD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hP0 : 0 ≤ logp (2 * D / Qr) := le_max_right _ _
  have hLmin : 0 ≤ Real.log (min D ((3 + 2 * ε) * Qr / 2)) :=
    Real.log_nonneg (le_min hD1 (by nlinarith))
  have hD0 : 0 < D := by linarith
  have etv : tvorogD x δ q U V ε =
      2 * s / π * (gB D + Y) +
        2 * s / π * ((1 + ε) * Qr * (√(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Qr / 2)) +
          2 * logp (2 * D / Qr) + Real.log D / 2 * logp (2 * D / Qr))) +
        3 * c1 x D * (|δ| * q) * Real.log D * (1 + (1 + ε) / (2 * ε) * logp (2 * D / Qr)) +
        35 * c0 * c2 / (3 * π ^ 2) * q * Real.log D := by
    unfold tvorogD
    rw [← hD_def, ← hQr_def, ← hs_def, gB_eq D hD0, hY_def]
    ring
  rw [etv]
  have h3e : 0 ≤ √(3 + 2 * ε) := Real.sqrt_nonneg _
  have hrest : 0 ≤ 2 * s / π * ((1 + ε) * Qr * (√(3 + 2 * ε) *
      Real.log (min D ((3 + 2 * ε) * Qr / 2)) + 2 * logp (2 * D / Qr) +
        Real.log D / 2 * logp (2 * D / Qr))) := by
    have h1 := mul_nonneg h3e hLmin
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log D / 2) hP0
    have h3 : 0 ≤ (1 + ε) * Qr * (√(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Qr / 2)) +
        2 * logp (2 * D / Qr) + Real.log D / 2 * logp (2 * D / Qr)) :=
      mul_nonneg (by positivity) (by linarith)
    exact mul_nonneg (by positivity) h3
  have hrest2 : 0 ≤ 3 * c1 x D * (|δ| * q) * Real.log D *
      (1 + (1 + ε) / (2 * ε) * logp (2 * D / Qr)) := by
    have : 0 ≤ 1 + (1 + ε) / (2 * ε) * logp (2 * D / Qr) := by positivity
    have : 0 ≤ 3 * c1 x D * (|δ| * q) := by positivity
    positivity
  have hcq0 : 0 ≤ 35 * c0 * c2 / (3 * π ^ 2) * q := by positivity
  have hk' : 2 * √c0 / π ≤ 2 * s / π := div_le_div_of_nonneg_right (by linarith) hpi.le
  have hgB : gB D = D * Real.log D - D := by unfold gB; ring
  rcases le_or_gt D Y with hDY | hDY
  · -- `D ≤ Q/2`: every term is `m ≤ M = D`, `q ∤ m`
    have hMeq : M = D := min_eq_right hDY
    have hsub : (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)) ⊆
        (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
      refine ⟨⟨hd.1.1, by rw [hMeq]; exact hd.1.2⟩, fun hqd => hd.2 ⟨hqd, ?_⟩⟩
      have : (d : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hd.1.2
      rw [hMeq]
      linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ D)]
    have hS := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := f) (fun d _ _ => hf0 d)
    rw [ef _ hpos1, ef _ (fun d hd => by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
      omega)] at hS
    refine hS.trans (hA.trans ?_)
    rw [hMeq]
    have h1 : Real.log D * (2 * √c0 / π * D) ≤ 2 * s / π * (gB D + Y) := by
      rw [hgB]
      have h := mul_le_mul_of_nonneg_left hk' (mul_nonneg hLD hD0.le)
      have h2 : 2 * s / π * (D * Real.log D) ≤ 2 * s / π * (D * Real.log D - D + Y) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc Real.log D * (2 * √c0 / π * D) = Real.log D * D * (2 * √c0 / π) := by ring
        _ ≤ Real.log D * D * (2 * s / π) := h
        _ = 2 * s / π * (D * Real.log D) := by ring
        _ ≤ 2 * s / π * (D * Real.log D - D + Y) := h2
    have h2 : Real.log D * (35 * c0 * c2 / (3 * π ^ 2) * q) =
        35 * c0 * c2 / (3 * π ^ 2) * q * Real.log D := by ring
    linarith
  · -- `D > Q/2`: `M = Q/2`, and the terms `Q/2 < m ≤ D` use `a'/q'`
    have hMeq : M = Y := min_eq_left hDY.le
    obtain ⟨a', q', β'', Q'', hq'1, hg', hα', hβ'', hq'Q, hlo, hhi⟩ :=
      second_approx (2 * β) Qr ε a q hq hg hαq hqr hε
    have hlo' : ε * (2 * Y) ≤ (1 + ε) * q' := by rw [hY_def]; linarith
    have hhi' : (q' : ℝ) ≤ 2 * (1 + ε) * Y := by rw [hY_def]; linarith
    have hp3 := piece3W x (2 * β) β'' Q'' D Y ε a' q' hq'1 hg' hα' hβ'' hq'Q hx hY1 hDY.le hε
      hlo' hhi' T htb
    rw [← hs_def] at hp3
    have hcov : (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)) ⊆
        (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d) ∪ Ioc ⌊Y⌋₊ ⌊D⌋₊ := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
      by_cases h1 : d ≤ ⌊M⌋₊
      · refine Or.inl ⟨⟨hd.1.1, h1⟩, fun hqd => hd.2 ⟨hqd, ?_⟩⟩
        have : (d : ℝ) ≤ ⌊M⌋₊ := by exact_mod_cast h1
        linarith [Nat.floor_le hM0]
      · refine Or.inr ⟨?_, hd.1.2⟩
        rw [← hMeq]
        omega
    have hS := Finset.sum_le_sum_of_subset_of_nonneg hcov (f := f) (fun d _ _ => hf0 d)
    rw [ef _ hpos1] at hS
    refine hS.trans ((sum_union_le_nn _ _ _ hf0).trans ?_)
    rw [ef _ (fun d hd => by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
      omega), ef _ (fun d hd => by
      have := (Finset.mem_Ioc.mp hd).1
      omega)]
    refine (add_le_add hA hp3).trans ?_
    rw [hMeq]
    -- the arithmetic
    have hxY : x / (2 * Y) = |δ| * q := by
      rw [hY_def, hQr_def]; field_simp
    have hDY' : D / Y = 2 * D / Qr := by rw [hY_def]; field_simp
    have h2Y : 2 * Y = Qr := by rw [hY_def]; ring
    have h3Y : (3 + 2 * ε) * Y = (3 + 2 * ε) * Qr / 2 := by rw [hY_def]; ring
    rw [hxY, hDY', h2Y, h3Y]
    have hlY : Real.log Y ≤ Real.log D := Real.log_le_log hY0 hDY.le
    have hlY0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hgY : gB Y = Y * Real.log Y - Y := by unfold gB; ring
    have h1 : Real.log Y * (2 * √c0 / π * Y) ≤ 2 * s / π * (Y * Real.log Y) := by
      have h := mul_le_mul_of_nonneg_left hk' (mul_nonneg hlY0 hY0.le)
      calc Real.log Y * (2 * √c0 / π * Y) = Real.log Y * Y * (2 * √c0 / π) := by ring
        _ ≤ Real.log Y * Y * (2 * s / π) := h
        _ = 2 * s / π * (Y * Real.log Y) := by ring
    have h2 : Real.log Y * (35 * c0 * c2 / (3 * π ^ 2) * q) ≤
        35 * c0 * c2 / (3 * π ^ 2) * q * Real.log D := by
      have h := mul_le_mul_of_nonneg_left hlY hcq0
      calc Real.log Y * (35 * c0 * c2 / (3 * π ^ 2) * q) =
            35 * c0 * c2 / (3 * π ^ 2) * q * Real.log Y := by ring
        _ ≤ 35 * c0 * c2 / (3 * π ^ 2) * q * Real.log D := h
    have e1 : Real.log D * (3 / 2 * c1 x D * (|δ| * q) * (2 + (1 + ε) / ε * logp (2 * D / Qr))) =
        3 * c1 x D * (|δ| * q) * Real.log D * (1 + (1 + ε) / (2 * ε) * logp (2 * D / Qr)) := by
      field_simp
    have e2 : 2 * s / π * ((1 + ε) * Qr * √(3 + 2 * ε) *
          Real.log (min D ((3 + 2 * ε) * Qr / 2)) + (gB D - gB Y) +
          2 * ((1 + ε) * Qr) * logp (2 * D / Qr) +
          (1 + ε) * Qr / 2 * logp (2 * D / Qr) * Real.log D) =
        2 * s / π * (gB D - gB Y) +
          2 * s / π * ((1 + ε) * Qr * (√(3 + 2 * ε) * Real.log (min D ((3 + 2 * ε) * Qr / 2)) +
            2 * logp (2 * D / Qr) + Real.log D / 2 * logp (2 * D / Qr))) := by ring
    rw [e1, e2, hgY]
    have e3 : Real.log Y * (2 * √c0 / π * Y + 35 * c0 * c2 / (3 * π ^ 2) * q) =
        Real.log Y * (2 * √c0 / π * Y) + Real.log Y * (35 * c0 * c2 / (3 * π ^ 2) * q) := by
      ring
    rw [e3]
    have e4 : 2 * s / π * (gB D - (Y * Real.log Y - Y)) =
        2 * s / π * (gB D + Y) - 2 * s / π * (Y * Real.log Y) := by ring
    rw [e4]
    linarith

/-! ## (4) `SecI2At` -/

/-- **`MPc.SecI2At` from the two cited computer checks and `MainBogusEta2C` alone, PROVED**
(`MPSD.secI2At_of_linksD` with `esthelBogusED_holds` and `MPTS.trompaisEta2_of_cited`). -/
theorem secI2At_of_mainD (hG : HC.CameloGridCited) (hW : HC.WollustCited)
    (hm : MainBogusEta2C) : SecI2At :=
  MPSD.secI2At_of_linksD (MPTS.trompaisEta2_of_cited hG hW) hm esthelBogusED_holds

end Principia.Common.TernaryGoldbach.MPBE
