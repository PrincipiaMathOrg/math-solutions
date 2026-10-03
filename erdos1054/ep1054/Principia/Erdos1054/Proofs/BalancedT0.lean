/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.BalancedK
import Principia.Common.Chebyshev.Upper

set_option autoImplicit false

/-!
# The balanced ternary Goldbach reduction from a Chebyshev bound on `[T₀, ∞)`

`BalancedK.balanced_of_theta_le_K` asks for `θ(t) ≤ c t` at every `t > 0`, and uses it only at
`t = 2` (for `0 ≤ c`), at `t = z = H/(30000 log H)` and at `t = H`, with `H ≥ 10²⁷` odd. Since `z`
increases for `H > e`, `z ≥ z(10²⁷) = 5.3616603·10²⁰`; this file proves the weaker `z ≥ 5·10²⁰`
(`cutoff_ge`, from `10²⁷ log H ≤ 62·10²⁷ + H`, `log_le_62_add`), so a Chebyshev bound valid on
`[T₀, ∞)` with `T₀ ≤ 5·10²⁰` is enough (`balanced_of_theta_T0`, a copy of
`balanced_of_theta_le_K` with `0 ≤ c` taken as a hypothesis and the two uses of `hθ` redirected).

Instantiated at Chebyshev's `θ(t) ≤ 1.11 t` for `t ≥ 3·10⁹`
(`Principia.Common.Chebyshev.theta_le_cheb`), the numeric condition is
`W(3·1.11²/30000 + 3·250047/(5·10²⁶)) = 2.0319204·10⁻⁴ < 0.000205` (`numerics_cheb`), so
`HelfgottAt 0.000205` suffices (`balanced_of_cheb`); `BalancedK` needed `0.00032` with
`c = log 4 < 1.3863`.
-/

namespace Principia.Erdos1054.Proofs.BalancedT0

open Finset
open Principia.Erdos1054 Principia.Erdos1054.Proofs.OddRepr Principia.Erdos1054.Proofs.BalancedNoRS
  Principia.Erdos1054.Proofs.BalancedK

/-- `log H ≤ 62 + H/10²⁷` for `H ≥ 10²⁷` (from `10²⁷ ≤ e⁶³` and `log x ≤ x − 1`), stated
multiplied out, `10²⁷ log H ≤ 62·10²⁷ + H`, so that `linarith` never meets the quotient. -/
theorem log_le_62_add (H : ℝ) (hH : 10 ^ 27 ≤ H) :
    Real.log H * 10 ^ 27 ≤ 62 * 10 ^ 27 + H := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hpos : (0 : ℝ) < 10 ^ 27 := by norm_num
  have he : (10 : ℝ) ^ 27 ≤ Real.exp 63 := by
    have e1 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
    rw [show (63 : ℝ) = 62 + 1 by norm_num, Real.exp_add]
    calc (10 : ℝ) ^ 27 ≤ 5 * 10 ^ 26 * 2.7 := by norm_num
      _ ≤ Real.exp 62 * Real.exp 1 :=
          mul_le_mul exp62_lower e1 (by norm_num) (Real.exp_pos 62).le
  have h63 : Real.log ((10 : ℝ) ^ 27) ≤ 63 := by
    have h := Real.log_le_log (by norm_num) he
    rwa [Real.log_exp] at h
  have h := Real.log_le_sub_one_of_pos (div_pos hHpos hpos)
  rw [Real.log_div hHpos.ne' hpos.ne'] at h
  have h2 := mul_le_mul_of_nonneg_right h hpos.le
  rw [sub_mul, sub_mul, div_mul_cancel₀ H hpos.ne', one_mul] at h2
  have h3 := mul_le_mul_of_nonneg_right h63 hpos.le
  linarith

/-- **The small cutoff clears `5·10²⁰`**: `z = H/(30000 log H) ≥ 5·10²⁰` for `H ≥ 10²⁷`
(the true minimum, at `H = 10²⁷`, is `5.3616603·10²⁰`). -/
theorem cutoff_ge (H : ℝ) (hH : 10 ^ 27 ≤ H) : 5 * 10 ^ 20 ≤ H / (30000 * Real.log H) := by
  have hL := log_le_62_add H hH
  have hLpos : 0 < Real.log H := Real.log_pos (lt_of_lt_of_le (by norm_num) hH)
  rw [le_div_iff₀ (mul_pos (by norm_num) hLpos)]
  linarith

/-- **The reduction from a Chebyshev bound on `[T₀, ∞)`**: `balanced_of_theta_le_K` verbatim,
except that `0 ≤ c` is a hypothesis and `θ(t) ≤ c t` is required only for `t ≥ T₀`,
`T₀ ≤ 5·10²⁰` (it is used at `t = z ≥ 5·10²⁰` and at `t = H ≥ 10²⁷`). -/
theorem balanced_of_theta_T0 (K c T0 : ℝ) (hc : 0 ≤ c) (hT0 : T0 ≤ 5 * 10 ^ 20)
    (hθ : ∀ t : ℝ, T0 ≤ t → Chebyshev.theta t ≤ c * t)
    (hnum : Wc * (3 * c ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < K) :
    HelfgottAt K → Lem_FraitureBalancedGoldbach := by
  intro hHelf H hHodd hH
  obtain ⟨ηp, ηs, hηp, hηs, hsum⟩ := hHelf H hHodd hH
  by_contra hno
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHR
  have hzT0 : T0 ≤ (H : ℝ) / (30000 * Real.log (H : ℝ)) := hT0.trans (cutoff_ge _ hHR)
  have hHT0 : T0 ≤ (H : ℝ) := by linarith
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
  have hθz' : Chebyshev.theta z ≤ c * z := hθ z hzT0
  have hθH' : Chebyshev.theta (H : ℝ) ≤ c * H := hθ _ hHT0
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
    mul_le_mul hθz' hθH' hθH (mul_nonneg hc hzpos.le)
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

/-- The numeric condition at `c = 1.11`, `K = 0.000205`:
`W(3·1.11²/30000 + 3·250047/(5·10²⁶)) = 2.0319204·10⁻⁴ < 0.000205`. -/
theorem numerics_cheb :
    Wc * (3 * (1.11 : ℝ) ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < 0.000205 := by
  unfold Wc; norm_num

/-- **`lem:fraiture-balanced-goldbach` from Helfgott's bound at `K = 0.000205`**, through
Chebyshev's `θ(t) ≤ 1.11 t` for `t ≥ 3·10⁹` (`Principia.Common.Chebyshev.theta_le_cheb`). -/
theorem balanced_of_cheb : HelfgottAt 0.000205 → Lem_FraitureBalancedGoldbach :=
  balanced_of_theta_T0 0.000205 1.11 (3 * 10 ^ 9) (by norm_num) (by norm_num)
    Principia.Common.Chebyshev.theta_le_cheb numerics_cheb

end Principia.Erdos1054.Proofs.BalancedT0
