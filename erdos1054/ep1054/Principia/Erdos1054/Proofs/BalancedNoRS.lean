/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.OddRepr

set_option autoImplicit false

/-!
# The balanced ternary Goldbach reduction without Rosser–Schoenfeld

`link_Lem_FraitureBalancedGoldbach` (in `Proofs/OddRepr.lean`) proves
`Cite_Helfgott_weighted → Cite_RosserSchoenfeld_psi → Lem_FraitureBalancedGoldbach`, following
the paper (EP1054.tex, proof lines 856–898), which bounds the weight of the triples with a
coordinate `≤ z = H / (30000 log H)` by `3 W ψ(z) ψ(H) log H` with `ψ(t) ≤ 1.03883 t`
(Rosser–Schoenfeld).

The proof only ever uses `θ`, never `ψ`, and it does not need a constant anywhere near `1.03883`.
`balanced_of_theta_le` isolates the one numerical requirement: any `c` with
`θ(t) ≤ c t` for `t > 0` (which forces `c ≥ 0`) and

  `W (3 c² / 30000 + 3 · 250047 / (5 · 10²⁶)) < 0.000422`,    `W = 1.079955² · 1.414 ≈ 1.649`

suffices (the second summand is the repeated-coordinate class, via `log_cube_le`). The largest
admissible `c` is `≈ 1.5997`. Mathlib's Chebyshev bound `θ(x) ≤ log 4 · x`
(`Chebyshev.theta_le_log4_mul_x`, valid for every `x ≥ 0`) has `log 4 < 1.3863`, which gives
`W (3 · 1.3863² / 30000 + …) ≈ 0.000317 < 0.000422`. Hence

  `balancedGoldbach_of_helfgott_noRS : Cite_Helfgott_weighted → Lem_FraitureBalancedGoldbach`,

with `Cite_RosserSchoenfeld_psi` removed from the hypotheses. The margin is `≈ 1.05·10⁻⁴ H²`
(against the paper's `0.000422 − 0.000178 ≈ 2.44·10⁻⁴ H²`).
-/

namespace Principia.Erdos1054.Proofs.BalancedNoRS

open Finset
open Principia.Erdos1054 Principia.Erdos1054.Proofs.OddRepr

/-- `log 4 < 1.3863`, from Mathlib's `log 2 < 0.6931471808`. -/
theorem log_four_lt : Real.log 4 < 1.3863 := by
  have h := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  linarith

/-- The unconditional Chebyshev bound in the form used below: `θ(t) ≤ 1.3863 t` for `t ≥ 0`. -/
theorem theta_le_mathlib {t : ℝ} (ht : 0 ≤ t) : Chebyshev.theta t ≤ 1.3863 * t :=
  (Chebyshev.theta_le_log4_mul_x ht).trans (mul_le_mul_of_nonneg_right log_four_lt.le ht)

/-- **The reduction, parametrised by the Chebyshev constant.** Any `c` with `θ(t) ≤ c t`
(`t > 0`) and `W (3c²/30000 + 3·250047/(5·10²⁶)) < 0.000422` turns Helfgott's weighted lower
bound into a balanced ternary representation. The inequality chain is the paper's
(lines 856–898), with `ψ ≤ 1.03883 t` replaced by the hypothesis `hθ`. -/
theorem balanced_of_theta_le (c : ℝ)
    (hθ : ∀ t : ℝ, 0 < t → Chebyshev.theta t ≤ c * t)
    (hnum : Wc * (3 * c ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < 0.000422) :
    Cite_Helfgott_weighted → Lem_FraitureBalancedGoldbach := by
  have hc0 : 0 ≤ c := by
    have h2 := hθ 2 (by norm_num)
    have h0 := Chebyshev.theta_nonneg 2
    linarith
  intro hHelf H hHodd hH
  obtain ⟨ηp, ηs, hηp, hηs, hsum⟩ := hHelf H hHodd hH
  by_contra hno
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHR
  set L := Real.log (H : ℝ) with hL
  have hL3 := log_cube_le (H : ℝ) hHR
  have hLpos : 0 < L := Real.log_pos (lt_of_lt_of_le (by norm_num) hHR)
  set z := (H : ℝ) / (30000 * L) with hz
  have hzpos : 0 < z := div_pos hHpos (by positivity)
  have hLne : L ≠ 0 := hLpos.ne'
  have hzL : z * L = H / 30000 := by rw [hz]; field_simp
  -- every weighted triple is exceptional
  have hbad : ∀ p q : ℕ, p + q < H → p.Prime → q.Prime → (H - p - q).Prime →
      Odd p → Odd q → Odd (H - p - q) →
      (p : ℝ) ≤ z ∨ (q : ℝ) ≤ z ∨ ((H - p - q : ℕ) : ℝ) ≤ z ∨ q = p ∨ H - p - q = p ∨
        q = H - p - q := by
    intro p q hpq hp hq hr op oq or
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcon
    exact hno ⟨p, q, H - p - q, hp, hq, hr, op, oq, or, fun h => h4 h.symm,
      fun h => h5 h.symm, h6, by omega, h1, h2, h3⟩
  have hW := Wc_nonneg
  have hWL : 0 ≤ Wc * L := mul_nonneg hW hLpos.le
  have hθz := Chebyshev.theta_nonneg z
  have hθH := Chebyshev.theta_nonneg (H : ℝ)
  have hθz' : Chebyshev.theta z ≤ c * z := hθ z hzpos
  have hθH' : Chebyshev.theta (H : ℝ) ≤ c * H := hθ _ hHpos
  have hS1 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lpLe z p * lp q) ≤
      Wc * L * (Chebyshev.theta z * Chebyshev.theta H) := by
    rw [double_sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sum_lpLe_le H z) (sum_lp_range_le H) (sum_lp_nonneg H) hθz) hWL
  have hS2 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpLe z q) ≤
      Wc * L * (Chebyshev.theta H * Chebyshev.theta z) := by
    rw [double_sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sum_lp_range_le H) (sum_lpLe_le H z) (sum_lpLe_nonneg H z) hθH) hWL
  have hS3 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpTail H p z q) ≤
      Wc * L * (Chebyshev.theta H * Chebyshev.theta z) := by
    calc ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpTail H p z q)
        = ∑ p ∈ range H, Wc * L * lp p * ∑ q ∈ range H, lpTail H p z q := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
      _ ≤ ∑ p ∈ range H, Wc * L * lp p * Chebyshev.theta z :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (sum_lpTail_le H p z) (mul_nonneg hWL (lp_nonneg p))
      _ = Wc * L * ((∑ p ∈ range H, lp p) * Chebyshev.theta z) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ Wc * L * (Chebyshev.theta H * Chebyshev.theta z) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sum_lp_range_le H) hθz) hWL
  have hS4 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q ≤
      (H : ℝ) * (Wc * L ^ 3 * 3) := by
    calc ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q
        = ∑ p ∈ range H, Wc * L ^ 3 * ∑ q ∈ range H, rep H p q :=
          Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ p ∈ range H, Wc * L ^ 3 * 3 :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (sum_rep_le H p) (mul_nonneg hW (pow_nonneg hLpos.le 3))
      _ = (H : ℝ) * (Wc * L ^ 3 * 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the numerics
  have hP1 : Chebyshev.theta z * Chebyshev.theta H ≤ (c * z) * (c * H) :=
    mul_le_mul hθz' hθH' hθH (mul_nonneg hc0 hzpos.le)
  have hP2 : Wc * L * (Chebyshev.theta z * Chebyshev.theta H) ≤
      Wc * c ^ 2 * (H / 30000) * H := by
    calc Wc * L * (Chebyshev.theta z * Chebyshev.theta H)
        ≤ Wc * L * ((c * z) * (c * H)) := mul_le_mul_of_nonneg_left hP1 hWL
      _ = Wc * c ^ 2 * (z * L) * H := by ring
      _ = Wc * c ^ 2 * (H / 30000) * H := by rw [hzL]
  have hP3 : (H : ℝ) * (Wc * L ^ 3 * 3) ≤ (H : ℝ) * (Wc * (250047 * H / (5 * 10 ^ 26)) * 3) := by
    have : L ^ 3 ≤ 250047 * H / (5 * 10 ^ 26) := by
      rw [le_div_iff₀ (by norm_num)]; exact hL3
    have h' : Wc * L ^ 3 * 3 ≤ Wc * (250047 * H / (5 * 10 ^ 26)) * 3 := by
      have := mul_le_mul_of_nonneg_left this hW
      linarith
    exact mul_le_mul_of_nonneg_left h' hHpos.le
  have hHH : 0 < (H : ℝ) * H := mul_pos hHpos hHpos
  have hfin : Wc * (3 * c ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) * ((H : ℝ) * H) <
      0.000422 * ((H : ℝ) * H) := mul_lt_mul_of_pos_right hnum hHH
  have hTH : Chebyshev.theta H * Chebyshev.theta z = Chebyshev.theta z * Chebyshev.theta H :=
    mul_comm _ _
  apply absurd hsum
  rw [not_le]
  calc _ ≤ ∑ p ∈ range H, ∑ q ∈ range H,
        (Wc * L * (lpLe z p * lp q) + Wc * L * (lp p * lpLe z q) +
          Wc * L * (lp p * lpTail H p z q) + Wc * L ^ 3 * rep H p q) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        split_ifs with hc
        · obtain ⟨hpq, hp, hq, hr, op, oq, or⟩ := hc
          exact pointwise H p q z _ hpq hp hq hr
            (weight_le _ _ _ _ _ _
              (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
              (Real.log_nonneg (by exact_mod_cast hq.one_lt.le))
              (Real.log_nonneg (by exact_mod_cast hr.one_lt.le))
              (hηp _) (hηp _) (hηs _))
            (hbad p q hpq hp hq hr op oq or)
        · have t1 : 0 ≤ Wc * L * (lpLe z p * lp q) :=
            mul_nonneg hWL (mul_nonneg (lpLe_nonneg z p) (lp_nonneg q))
          have t2 : 0 ≤ Wc * L * (lp p * lpLe z q) :=
            mul_nonneg hWL (mul_nonneg (lp_nonneg p) (lpLe_nonneg z q))
          have t3 : 0 ≤ Wc * L * (lp p * lpTail H p z q) :=
            mul_nonneg hWL (mul_nonneg (lp_nonneg p) (lpTail_nonneg H p z q))
          have t4 : 0 ≤ Wc * L ^ 3 * rep H p q :=
            mul_nonneg (mul_nonneg hW (pow_nonneg hLpos.le 3)) (rep_nonneg H p q)
          linarith
    _ = ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lpLe z p * lp q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpLe z q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpTail H p z q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q := by
        simp only [Finset.sum_add_distrib]
    _ ≤ Wc * L * (Chebyshev.theta z * Chebyshev.theta H) +
          Wc * L * (Chebyshev.theta H * Chebyshev.theta z) +
          Wc * L * (Chebyshev.theta H * Chebyshev.theta z) +
          (H : ℝ) * (Wc * L ^ 3 * 3) :=
        add_le_add (add_le_add (add_le_add hS1 hS2) hS3) hS4
    _ = 3 * (Wc * L * (Chebyshev.theta z * Chebyshev.theta H)) +
          (H : ℝ) * (Wc * L ^ 3 * 3) := by
        rw [hTH]; ring
    _ ≤ 3 * (Wc * c ^ 2 * (H / 30000) * H) +
          (H : ℝ) * (Wc * (250047 * H / (5 * 10 ^ 26)) * 3) := by
        linarith
    _ = Wc * (3 * c ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) * ((H : ℝ) * H) := by
        ring
    _ < 0.000422 * ((H : ℝ) * H) := hfin
    _ = 0.000422 * (H : ℝ) ^ 2 := by ring

/-- The numerical condition of `balanced_of_theta_le` at Mathlib's constant `c = 1.3863 > log 4`:
`W (3 · 1.3863² / 30000 + 3·250047/(5·10²⁶)) ≈ 0.000317 < 0.000422`. -/
theorem numerics_mathlib :
    Wc * (3 * (1.3863 : ℝ) ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < 0.000422 := by
  unfold Wc; norm_num

end Principia.Erdos1054.Proofs.BalancedNoRS

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054 Principia.Erdos1054.Proofs.BalancedNoRS

/-- **`lem:fraiture-balanced-goldbach` without Rosser–Schoenfeld.** Helfgott's weighted lower
bound alone implies the balanced ternary Goldbach statement: Mathlib's `θ(x) ≤ log 4 · x`
replaces `ψ(t) ≤ 1.03883 t` in the paper's proof (lines 856–898). -/
theorem balancedGoldbach_of_helfgott_noRS :
    Cite_Helfgott_weighted → Lem_FraitureBalancedGoldbach :=
  balanced_of_theta_le 1.3863 (fun _ ht => theta_le_mathlib ht.le)
    numerics_mathlib

end Principia.Erdos1054.Proofs
