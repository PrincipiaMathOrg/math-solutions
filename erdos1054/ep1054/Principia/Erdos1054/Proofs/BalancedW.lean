/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.BalancedT0

set_option autoImplicit false

/-!
# The balanced reduction with weights that vanish at `0`

`BalancedT0.balanced_of_theta_T0` bounds every exceptional triple (a coordinate `≤ z`, with
`z = H/(30000 log H)`) by the sup norms of the weights alone, so each of the three small-coordinate
classes costs `W L θ(z) θ(H)` with `W = 1.079955²·1.414`. That is what forces
`K > W(3c²/30000 + …) ≈ 2.03·10⁻⁴`.

But a coordinate `n ≤ z` enters its weight at `n/x ≤ z/x`, and `z/x ≤ 1.1·10⁻⁶` for `H ≥ 10²⁷`
(`x = helfgottX H ≥ H/2.023`, `log H > 62`). Helfgott's weights vanish at `0`: `|η₊(t)| ≤ 3t`
(`KSmall.etaPlus_le`), and `η_*(t) = O(t²)`. So a weight bound `|η(u)| ≤ A u` on
`0 ≤ u ≤ 1.1·10⁻⁶` shrinks each small-coordinate class by a factor of order `10⁻⁶`.

* `HelfgottAtW K A B` is `HelfgottAt K` plus those two small-argument bounds (`helfgottAt_of_W`
  forgets them).
* `balanced_of_weights` is `balanced_of_theta_T0` with the three small-coordinate classes charged
  `W₁ = W₂ = A·1.1·10⁻⁶·1.079955·1.414` and `W₃ = 1.079955²·B·1.1·10⁻⁶` in place of `W`. The
  repeated-coordinate class keeps `W`.
* At `c = 1.11` (`θ(t) ≤ 1.11 t` for `t ≥ 3·10⁹`), `A = 3`, `B = 250`, the numeric condition is
  `1.3587·10⁻⁸ < 2·10⁻⁸` (`numerics_w`), so `HelfgottAtW 2·10⁻⁸ 3 250` suffices (`balanced_of_w`),
  against `HelfgottAt 0.000205` before.
-/

namespace Principia.Erdos1054.Proofs.BalancedW

open Finset
open Principia.Erdos1054 Principia.Erdos1054.Proofs.OddRepr Principia.Erdos1054.Proofs.BalancedNoRS
  Principia.Erdos1054.Proofs.BalancedK Principia.Erdos1054.Proofs.BalancedT0

open Classical in
/-- **Helfgott's weighted lower bound at constant `K`, with weights vanishing linearly at `0`**:
`HelfgottAt K` with, in addition, `|η₊(u)| ≤ A u` and `|η_*(u)| ≤ B u` for
`0 ≤ u ≤ 1.1·10⁻⁶`. -/
def HelfgottAtW (K A B : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∃ ηp ηs : ℝ → ℝ, (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1.1e-6 → |ηp u| ≤ A * u) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1.1e-6 → |ηs u| ≤ B * u) ∧
      K * (H : ℝ) ^ 2 ≤
        ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
          if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
            ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
              ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)
          else 0

/-- Forgetting the small-argument bounds. -/
theorem helfgottAt_of_W {K A B : ℝ} (h : HelfgottAtW K A B) : HelfgottAt K := by
  intro H hHodd hH
  obtain ⟨ηp, ηs, hp, hs, -, -, hsum⟩ := h H hHodd hH
  exact ⟨ηp, ηs, hp, hs, hsum⟩

/-- `weight_le` with three separate bounds. -/
theorem weight_le3 (a b c u v w U V W : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : |u| ≤ U) (hv : |v| ≤ V) (hw : |w| ≤ W) :
    a * b * c * u * v * w ≤ U * V * W * (a * b * c) := by
  have habc : 0 ≤ a * b * c := by positivity
  have hU : 0 ≤ U := (abs_nonneg u).trans hu
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  have huvw : |u * v * w| ≤ U * V * W := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hu hv (abs_nonneg _) hU) hw (abs_nonneg _) (mul_nonneg hU hV)
  calc a * b * c * u * v * w = (a * b * c) * (u * v * w) := by ring
    _ ≤ (a * b * c) * |u * v * w| := mul_le_mul_of_nonneg_left (le_abs_self _) habc
    _ ≤ (a * b * c) * (U * V * W) := mul_le_mul_of_nonneg_left huvw habc
    _ = U * V * W * (a * b * c) := by ring

/-- `OddRepr.pointwise` with a separate weight constant for each small-coordinate class. -/
theorem pointwiseW (H p q : ℕ) (z T W1 W2 W3 : ℝ) (hW1 : 0 ≤ W1) (hW2 : 0 ≤ W2) (hW3 : 0 ≤ W3)
    (hpq : p + q < H) (hp : p.Prime) (hq : q.Prime) (hr : (H - p - q).Prime)
    (hT1 : (p : ℝ) ≤ z →
      T ≤ W1 * (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)))
    (hT2 : (q : ℝ) ≤ z →
      T ≤ W2 * (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)))
    (hT3 : ((H - p - q : ℕ) : ℝ) ≤ z →
      T ≤ W3 * (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)))
    (hT : T ≤ Wc * (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)))
    (hbad : (p : ℝ) ≤ z ∨ (q : ℝ) ≤ z ∨ ((H - p - q : ℕ) : ℝ) ≤ z ∨ q = p ∨ H - p - q = p ∨
      q = H - p - q) :
    T ≤ W1 * Real.log H * (lpLe z p * lp q) + W2 * Real.log H * (lp p * lpLe z q) +
      W3 * Real.log H * (lp p * lpTail H p z q) + Wc * Real.log H ^ 3 * rep H p q := by
  set L := Real.log (H : ℝ) with hL
  have hlog_le : ∀ n : ℕ, 0 < n → n ≤ H → Real.log n ≤ L := fun n hn hnH =>
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnH)
  have hlog_nn : ∀ n : ℕ, n.Prime → 0 ≤ Real.log n := fun n hn =>
    Real.log_nonneg (by exact_mod_cast hn.one_lt.le)
  set a := Real.log (p : ℝ) with ha
  set b := Real.log (q : ℝ) with hb
  set c := Real.log ((H - p - q : ℕ) : ℝ) with hc
  have ha0 : 0 ≤ a := hlog_nn p hp
  have hb0 : 0 ≤ b := hlog_nn q hq
  have hc0 : 0 ≤ c := hlog_nn _ hr
  have haL : a ≤ L := hlog_le p hp.pos (by omega)
  have hbL : b ≤ L := hlog_le q hq.pos (by omega)
  have hcL : c ≤ L := hlog_le _ hr.pos (by omega)
  have hL0 : 0 ≤ L := le_trans ha0 haL
  have hW := Wc_nonneg
  have hlpp : lp p = a := lp_of_prime hp
  have hlpq : lp q = b := lp_of_prime hq
  have hlpr : lp (H - p - q) = c := lp_of_prime hr
  have t1 : 0 ≤ W1 * L * (lpLe z p * lp q) :=
    mul_nonneg (mul_nonneg hW1 hL0) (mul_nonneg (lpLe_nonneg z p) (lp_nonneg q))
  have t2 : 0 ≤ W2 * L * (lp p * lpLe z q) :=
    mul_nonneg (mul_nonneg hW2 hL0) (mul_nonneg (lp_nonneg p) (lpLe_nonneg z q))
  have t3 : 0 ≤ W3 * L * (lp p * lpTail H p z q) :=
    mul_nonneg (mul_nonneg hW3 hL0) (mul_nonneg (lp_nonneg p) (lpTail_nonneg H p z q))
  have t4 : 0 ≤ Wc * L ^ 3 * rep H p q :=
    mul_nonneg (mul_nonneg hW (pow_nonneg hL0 3)) (rep_nonneg H p q)
  rcases hbad with h | h | h | h | h | h
  · have hle : lpLe z p = a := by unfold lpLe; rw [if_pos h, hlpp]
    have key : W1 * (a * b * c) ≤ W1 * L * (lpLe z p * lp q) := by
      rw [hle, hlpq]
      have : a * b * c ≤ a * b * L := mul_le_mul_of_nonneg_left hcL (mul_nonneg ha0 hb0)
      calc W1 * (a * b * c) ≤ W1 * (a * b * L) := mul_le_mul_of_nonneg_left this hW1
        _ = W1 * L * (a * b) := by ring
    have := hT1 h
    linarith
  · have hle : lpLe z q = b := by unfold lpLe; rw [if_pos h, hlpq]
    have key : W2 * (a * b * c) ≤ W2 * L * (lp p * lpLe z q) := by
      rw [hle, hlpp]
      have : a * b * c ≤ a * b * L := mul_le_mul_of_nonneg_left hcL (mul_nonneg ha0 hb0)
      calc W2 * (a * b * c) ≤ W2 * (a * b * L) := mul_le_mul_of_nonneg_left this hW2
        _ = W2 * L * (a * b) := by ring
    have := hT2 h
    linarith
  · have hle : lpTail H p z q = c := by unfold lpTail; rw [if_pos ⟨hpq, h⟩, hlpr]
    have key : W3 * (a * b * c) ≤ W3 * L * (lp p * lpTail H p z q) := by
      rw [hle, hlpp]
      have : a * b * c ≤ a * L * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbL ha0) hc0
      calc W3 * (a * b * c) ≤ W3 * (a * L * c) := mul_le_mul_of_nonneg_left this hW3
        _ = W3 * L * (a * c) := by ring
    have := hT3 h
    linarith
  all_goals
    have hrep : rep H p q = 1 := by
      unfold rep; rw [if_pos ⟨hpq, by tauto⟩]
    have habc : a * b * c ≤ L ^ 3 := by
      have hab : a * b ≤ L * L := mul_le_mul haL hbL hb0 hL0
      calc a * b * c ≤ L * L * L := mul_le_mul hab hcL hc0 (mul_nonneg hL0 hL0)
        _ = L ^ 3 := by ring
    have key : Wc * (a * b * c) ≤ Wc * L ^ 3 * rep H p q := by
      rw [hrep, mul_one]
      exact mul_le_mul_of_nonneg_left habc hW
    linarith

/-- `helfgottX H ≥ H/2.023`: the denominator `2 + 9/(196 √(2π))` is at most `2 + 9/392`. -/
theorem helfgottX_ge (H : ℕ) : (H : ℝ) / 2.023 ≤ helfgottX H := by
  unfold helfgottX
  have hs : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    (Real.le_sqrt' (by norm_num)).mpr (by nlinarith [Real.pi_gt_three])
  have hd : 9 / (196 * Real.sqrt (2 * Real.pi)) ≤ 9 / 392 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hD0 : 0 < 2 + 9 / (196 * Real.sqrt (2 * Real.pi)) := by positivity
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) hD0 (by linarith)

/-- **The small-coordinate range**: for `H ≥ 10²⁷`, `z = H/(30000 log H) ≤ 1.1·10⁻⁶ · x`. -/
theorem cutoff_le_x (H : ℕ) (hH : (10 : ℝ) ^ 27 ≤ H) :
    (H : ℝ) / (30000 * Real.log H) ≤ 1.1e-6 * helfgottX H := by
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hH
  have hL62 : 62 < Real.log H := by
    rw [Real.lt_log_iff_exp_lt hHpos]
    linarith [exp62_upper]
  have h1 : (H : ℝ) / (30000 * Real.log H) ≤ H / (30000 * 62) :=
    div_le_div_of_nonneg_left hHpos.le (by norm_num) (by linarith)
  have h2 := helfgottX_ge H
  calc (H : ℝ) / (30000 * Real.log H) ≤ H / (30000 * 62) := h1
    _ = (1 / (30000 * 62)) * H := by ring
    _ ≤ (1.1e-6 / 2.023) * H := mul_le_mul_of_nonneg_right (by norm_num) hHpos.le
    _ = 1.1e-6 * ((H : ℝ) / 2.023) := by ring
    _ ≤ 1.1e-6 * helfgottX H := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- **The reduction with weights vanishing at `0`**: `balanced_of_theta_T0`, with the three
small-coordinate classes charged `A·1.1·10⁻⁶·1.079955·1.414` (twice) and
`1.079955²·B·1.1·10⁻⁶` in place of `Wc`. -/
theorem balanced_of_weights (K c T0 A B : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT0 : T0 ≤ 5 * 10 ^ 20)
    (hθ : ∀ t : ℝ, T0 ≤ t → Chebyshev.theta t ≤ c * t)
    (hnum : (A * 1.1e-6 * 1.079955 * 1.414 + 1.079955 * (A * 1.1e-6) * 1.414 +
        1.079955 * 1.079955 * (B * 1.1e-6)) * (c ^ 2 / 30000) +
        Wc * (3 * 250047 / (5 * 10 ^ 26)) < K) :
    HelfgottAtW K A B → Lem_FraitureBalancedGoldbach := by
  intro hHelf H hHodd hH
  obtain ⟨ηp, ηs, hηp, hηs, hηp0, hηs0, hsum⟩ := hHelf H hHodd hH
  by_contra hno
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHR
  have hzT0 : T0 ≤ (H : ℝ) / (30000 * Real.log (H : ℝ)) := hT0.trans (cutoff_ge _ hHR)
  have hHT0 : T0 ≤ (H : ℝ) := by linarith
  have hzx := cutoff_le_x H hHR
  set x := helfgottX H with hx
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos hHpos (by norm_num)) (helfgottX_ge H)
  set L := Real.log (H : ℝ) with hL
  have hL3 := log_cube_le (H : ℝ) hHR
  have hLpos : 0 < L := Real.log_pos (lt_of_lt_of_le (by norm_num) hHR)
  set z := (H : ℝ) / (30000 * L) with hz
  have hzpos : 0 < z := div_pos hHpos (by positivity)
  have hLne : L ≠ 0 := hLpos.ne'
  have hzL : z * L = H / 30000 := by rw [hz]; field_simp
  have hsmall : ∀ n : ℕ, (n : ℝ) ≤ z → 0 ≤ (n : ℝ) / x ∧ (n : ℝ) / x ≤ 1.1e-6 :=
    fun n hn => ⟨div_nonneg (Nat.cast_nonneg n) hxpos.le,
      (div_le_iff₀ hxpos).mpr (hn.trans hzx)⟩
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
  set W1 := A * 1.1e-6 * 1.079955 * 1.414 with hW1d
  set W2 := 1.079955 * (A * 1.1e-6) * 1.414 with hW2d
  set W3 := 1.079955 * 1.079955 * (B * 1.1e-6) with hW3d
  have hW1 : 0 ≤ W1 := by positivity
  have hW2 : 0 ≤ W2 := by positivity
  have hW3 : 0 ≤ W3 := by positivity
  have hAu : A * 1.1e-6 = A * 1.1e-6 := rfl
  have hW := Wc_nonneg
  have hW1L : 0 ≤ W1 * L := mul_nonneg hW1 hLpos.le
  have hW2L : 0 ≤ W2 * L := mul_nonneg hW2 hLpos.le
  have hW3L : 0 ≤ W3 * L := mul_nonneg hW3 hLpos.le
  have hθz := Chebyshev.theta_nonneg z
  have hθH := Chebyshev.theta_nonneg (H : ℝ)
  have hθz' : Chebyshev.theta z ≤ c * z := hθ z hzT0
  have hθH' : Chebyshev.theta (H : ℝ) ≤ c * H := hθ _ hHT0
  have hS1 : ∑ p ∈ range H, ∑ q ∈ range H, W1 * L * (lpLe z p * lp q) ≤
      W1 * L * (Chebyshev.theta z * Chebyshev.theta H) := by
    rw [double_sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sum_lpLe_le H z) (sum_lp_range_le H) (sum_lp_nonneg H) hθz) hW1L
  have hS2 : ∑ p ∈ range H, ∑ q ∈ range H, W2 * L * (lp p * lpLe z q) ≤
      W2 * L * (Chebyshev.theta H * Chebyshev.theta z) := by
    rw [double_sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sum_lp_range_le H) (sum_lpLe_le H z) (sum_lpLe_nonneg H z) hθH) hW2L
  have hS3 : ∑ p ∈ range H, ∑ q ∈ range H, W3 * L * (lp p * lpTail H p z q) ≤
      W3 * L * (Chebyshev.theta H * Chebyshev.theta z) := by
    calc ∑ p ∈ range H, ∑ q ∈ range H, W3 * L * (lp p * lpTail H p z q)
        = ∑ p ∈ range H, W3 * L * lp p * ∑ q ∈ range H, lpTail H p z q := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
      _ ≤ ∑ p ∈ range H, W3 * L * lp p * Chebyshev.theta z :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (sum_lpTail_le H p z) (mul_nonneg hW3L (lp_nonneg p))
      _ = W3 * L * ((∑ p ∈ range H, lp p) * Chebyshev.theta z) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ W3 * L * (Chebyshev.theta H * Chebyshev.theta z) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sum_lp_range_le H) hθz) hW3L
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
  have hP2 : L * (Chebyshev.theta z * Chebyshev.theta H) ≤ c ^ 2 * (H / 30000) * H := by
    calc L * (Chebyshev.theta z * Chebyshev.theta H)
        ≤ L * ((c * z) * (c * H)) := mul_le_mul_of_nonneg_left hP1 hLpos.le
      _ = c ^ 2 * (z * L) * H := by ring
      _ = c ^ 2 * (H / 30000) * H := by rw [hzL]
  have hP3 : (H : ℝ) * (Wc * L ^ 3 * 3) ≤ (H : ℝ) * (Wc * (250047 * H / (5 * 10 ^ 26)) * 3) := by
    have : L ^ 3 ≤ 250047 * H / (5 * 10 ^ 26) := by
      rw [le_div_iff₀ (by norm_num)]; exact hL3
    have h' : Wc * L ^ 3 * 3 ≤ Wc * (250047 * H / (5 * 10 ^ 26)) * 3 := by
      have := mul_le_mul_of_nonneg_left this hW
      linarith
    exact mul_le_mul_of_nonneg_left h' hHpos.le
  have hW123 : 0 ≤ W1 + W2 + W3 := by linarith
  have hP4 : (W1 + W2 + W3) * (L * (Chebyshev.theta z * Chebyshev.theta H)) ≤
      (W1 + W2 + W3) * (c ^ 2 * (H / 30000) * H) := mul_le_mul_of_nonneg_left hP2 hW123
  have hHH : 0 < (H : ℝ) * H := mul_pos hHpos hHpos
  have hfin : ((W1 + W2 + W3) * (c ^ 2 / 30000) + Wc * (3 * 250047 / (5 * 10 ^ 26))) *
      ((H : ℝ) * H) < K * ((H : ℝ) * H) := mul_lt_mul_of_pos_right hnum hHH
  have hTH : Chebyshev.theta H * Chebyshev.theta z = Chebyshev.theta z * Chebyshev.theta H :=
    mul_comm _ _
  apply absurd hsum
  rw [not_le]
  calc _ ≤ ∑ p ∈ range H, ∑ q ∈ range H,
        (W1 * L * (lpLe z p * lp q) + W2 * L * (lp p * lpLe z q) +
          W3 * L * (lp p * lpTail H p z q) + Wc * L ^ 3 * rep H p q) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        split_ifs with hcnd
        · obtain ⟨hpq, hp, hq, hr, op, oq, or⟩ := hcnd
          have la : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
          have lb : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
          have lc : 0 ≤ Real.log ((H - p - q : ℕ) : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hr.one_lt.le)
          refine pointwiseW H p q z _ W1 W2 W3 hW1 hW2 hW3 hpq hp hq hr ?_ ?_ ?_
            (weight_le _ _ _ _ _ _ la lb lc (hηp _) (hηp _) (hηs _))
            (hbad p q hpq hp hq hr op oq or)
          · intro h
            obtain ⟨h0, h1⟩ := hsmall p h
            exact weight_le3 _ _ _ _ _ _ _ _ _ la lb lc
              ((hηp0 _ h0 h1).trans (mul_le_mul_of_nonneg_left h1 hA)) (hηp _) (hηs _)
          · intro h
            obtain ⟨h0, h1⟩ := hsmall q h
            exact weight_le3 _ _ _ _ _ _ _ _ _ la lb lc
              (hηp _) ((hηp0 _ h0 h1).trans (mul_le_mul_of_nonneg_left h1 hA)) (hηs _)
          · intro h
            obtain ⟨h0, h1⟩ := hsmall _ h
            exact weight_le3 _ _ _ _ _ _ _ _ _ la lb lc
              (hηp _) (hηp _) ((hηs0 _ h0 h1).trans (mul_le_mul_of_nonneg_left h1 hB))
        · have t1 : 0 ≤ W1 * L * (lpLe z p * lp q) :=
            mul_nonneg hW1L (mul_nonneg (lpLe_nonneg z p) (lp_nonneg q))
          have t2 : 0 ≤ W2 * L * (lp p * lpLe z q) :=
            mul_nonneg hW2L (mul_nonneg (lp_nonneg p) (lpLe_nonneg z q))
          have t3 : 0 ≤ W3 * L * (lp p * lpTail H p z q) :=
            mul_nonneg hW3L (mul_nonneg (lp_nonneg p) (lpTail_nonneg H p z q))
          have t4 : 0 ≤ Wc * L ^ 3 * rep H p q :=
            mul_nonneg (mul_nonneg hW (pow_nonneg hLpos.le 3)) (rep_nonneg H p q)
          linarith
    _ = ∑ p ∈ range H, ∑ q ∈ range H, W1 * L * (lpLe z p * lp q) +
          ∑ p ∈ range H, ∑ q ∈ range H, W2 * L * (lp p * lpLe z q) +
          ∑ p ∈ range H, ∑ q ∈ range H, W3 * L * (lp p * lpTail H p z q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q := by
        simp only [Finset.sum_add_distrib]
    _ ≤ W1 * L * (Chebyshev.theta z * Chebyshev.theta H) +
          W2 * L * (Chebyshev.theta H * Chebyshev.theta z) +
          W3 * L * (Chebyshev.theta H * Chebyshev.theta z) +
          (H : ℝ) * (Wc * L ^ 3 * 3) :=
        add_le_add (add_le_add (add_le_add hS1 hS2) hS3) hS4
    _ = (W1 + W2 + W3) * (L * (Chebyshev.theta z * Chebyshev.theta H)) +
          (H : ℝ) * (Wc * L ^ 3 * 3) := by
        rw [hTH]; ring
    _ ≤ (W1 + W2 + W3) * (c ^ 2 * (H / 30000) * H) +
          (H : ℝ) * (Wc * (250047 * H / (5 * 10 ^ 26)) * 3) := by
        linarith
    _ = ((W1 + W2 + W3) * (c ^ 2 / 30000) + Wc * (3 * 250047 / (5 * 10 ^ 26))) *
          ((H : ℝ) * H) := by
        ring
    _ < K * ((H : ℝ) * H) := hfin
    _ = K * (H : ℝ) ^ 2 := by ring

/-- The numeric condition at `c = 1.11`, `A = 3`, `B = 250`, `K = 2·10⁻⁸`:
`(2·3·1.1·10⁻⁶·1.079955·1.414 + 1.079955²·2.75·10⁻⁴)(1.11²/30000) + W·1.5·10⁻²¹
= 1.3587·10⁻⁸ < 2·10⁻⁸`. (`B = 250` admits the linear bound `η_*(t) ≤ 247.2 t`.) -/
theorem numerics_w :
    ((3 : ℝ) * 1.1e-6 * 1.079955 * 1.414 + 1.079955 * (3 * 1.1e-6) * 1.414 +
        1.079955 * 1.079955 * (250 * 1.1e-6)) * ((1.11 : ℝ) ^ 2 / 30000) +
        Wc * (3 * 250047 / (5 * 10 ^ 26)) < 2e-8 := by
  unfold Wc; norm_num

/-- **`lem:fraiture-balanced-goldbach` from `HelfgottAtW 2·10⁻⁸ 3 250`**, through Chebyshev's
`θ(t) ≤ 1.11 t` for `t ≥ 3·10⁹` (`Principia.Common.Chebyshev.theta_le_cheb`). -/
theorem balanced_of_w : HelfgottAtW 2e-8 3 250 → Lem_FraitureBalancedGoldbach :=
  balanced_of_weights 2e-8 1.11 (3 * 10 ^ 9) 3 250 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) Principia.Common.Chebyshev.theta_le_cheb numerics_w

end Principia.Erdos1054.Proofs.BalancedW
