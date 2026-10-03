/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.BalancedNoRS

set_option autoImplicit false

/-!
# The balanced ternary Goldbach reduction at a weaker Helfgott constant

`Cite_Helfgott_weighted` carries Helfgott's constant `0.000422 H²`. Its only consumer on the EP1054
route is `balanced_of_theta_le` at `c = 1.3863`, whose one numeric requirement is
`K > W(3c²/30000 + 3·250047/(5·10²⁶)) = 0.000316939…` (`W = 1.079955²·1.414`). So the constant is
chosen, not forced. This file states the input at any constant, `HelfgottAt K`
(`HelfgottAt 0.000422` IS `Cite_Helfgott_weighted`, `helfgottAt_cite`), repeats the reduction at
`K` (a verbatim copy of
`balanced_of_theta_le` with `0.000422` replaced by `K`), and instantiates it at `K = 0.00032`.

Why it matters: at `K = 0.00032` Helfgott's major-arc link needs the singular series only at
`C₀ ≥ 1.2948`, which `SingularSeries.sing3_ge_sharp` (`1.31`) already proves; at `0.000422` it
needs `1.3203219`, a 78 498-prime certification. See `Campaigns/Erdos-1054/LEAN-PROGRESS.md`.
-/

namespace Principia.Erdos1054.Proofs.BalancedK

open Finset
open Principia.Erdos1054 Principia.Erdos1054.Proofs.OddRepr Principia.Erdos1054.Proofs.BalancedNoRS

open Classical in
/-- **Helfgott's weighted lower bound at constant `K`** — `Cite_Helfgott_weighted` with `0.000422`
replaced by `K`, text otherwise identical (`helfgottAt_cite`). -/
def HelfgottAt (K : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∃ ηp ηs : ℝ → ℝ, (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414) ∧
      K * (H : ℝ) ^ 2 ≤
        ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
          if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
            ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
              ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)
          else 0

/-- `HelfgottAt 0.000422` is `Cite_Helfgott_weighted`, definitionally. -/
theorem helfgottAt_cite : HelfgottAt 0.000422 = Cite_Helfgott_weighted := rfl

/-- A lower bound at a larger constant gives one at any smaller constant. -/
theorem helfgottAt_mono {K K' : ℝ} (hK : K' ≤ K) : HelfgottAt K → HelfgottAt K' := by
  intro h H hHodd hH
  obtain ⟨ηp, ηs, hp, hs, hsum⟩ := h H hHodd hH
  exact ⟨ηp, ηs, hp, hs, le_trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) hsum⟩

/-- **The reduction at constant `K`**: `balanced_of_theta_le` verbatim, with `0.000422` replaced
by `K`. -/
theorem balanced_of_theta_le_K (K c : ℝ)
    (hθ : ∀ t : ℝ, 0 < t → Chebyshev.theta t ≤ c * t)
    (hnum : Wc * (3 * c ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < K) :
    HelfgottAt K → Lem_FraitureBalancedGoldbach := by
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
      K * ((H : ℝ) * H) := mul_lt_mul_of_pos_right hnum hHH
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
    _ < K * ((H : ℝ) * H) := hfin
    _ = K * (H : ℝ) ^ 2 := by ring

/-- The numeric condition at `K = 0.00032`: `W(3·1.3863²/30000 + …) = 0.000316939… < 0.00032`. -/
theorem numerics_K :
    Wc * (3 * (1.3863 : ℝ) ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < 0.00032 := by
  unfold Wc; norm_num

/-- **`lem:fraiture-balanced-goldbach` from Helfgott's bound at `K = 0.00032`.** -/
theorem balanced_of_helfgottAt : HelfgottAt 0.00032 → Lem_FraitureBalancedGoldbach :=
  balanced_of_theta_le_K 0.00032 1.3863 (fun _ ht => theta_le_mathlib ht.le) numerics_K

/-- Consistency: the original route factors through this one. -/
theorem balanced_of_cite : Cite_Helfgott_weighted → Lem_FraitureBalancedGoldbach := fun h =>
  balanced_of_helfgottAt (helfgottAt_mono (by norm_num) (helfgottAt_cite ▸ h))

end Principia.Erdos1054.Proofs.BalancedK
