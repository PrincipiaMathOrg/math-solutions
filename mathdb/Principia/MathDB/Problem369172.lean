import Mathlib

/-!
# MathDB #369172, part 1 — the Taylor coefficients of `√(1 + z + ⋯ + z⁴³)` by recurrence

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/369172/solution.tex`, refuting Kovalev's Conjecture 1.3 (positivity
of `∑_{k ≤ n} b_k^{(d)} cos(kt)`) at `d = 43`, `n = 1800`, `t = arccos(99/100)`.

**Status of this file: part 1 of the build.**  The write-up computes the coefficients from the
recurrence `2k b_k = (2k−1) b_{k−1} + (2k−132) b_{k−44} + (133−2k) b_{k−45}`, obtained by
logarithmic differentiation of `f = √P`, `P = 1 + z + ⋯ + z⁴³`.  Here `b` is DEFINED by that
recurrence and the converse is proved: `F = ∑ b_k zᵏ` satisfies `F² = P` (`F_sq`), so `b` really is
the coefficient sequence of the principal square root.  Route: `2 S F′ = Q F` coefficientwise from
the recurrence (`F_ode`), with `S = (1 − z)(1 − z⁴⁴)`, `Q = 1 − 44z⁴³ + 43z⁴⁴`; `P` satisfies `S P′
= Q P` (`P_ode`, from `(1 − z)P = 1 − z⁴⁴`); so `G = F² − P` satisfies `S G′ = Q G` with `G(0) =
0`, and the leading coefficient `1` of `S` forces `G = 0` (`ode_unique`).
-/

namespace Principia.MathDB.P369172

open PowerSeries

/-- The coefficients `b_k`, by the write-up's recurrence (with `b_{−j} = 0`). -/
def b (k : ℕ) : ℚ :=
  if h : k = 0 then 1 else
    ((2 * (k : ℚ) - 1) * b (k - 1)
      + (if 44 ≤ k then (2 * (k : ℚ) - 132) * b (k - 44) else 0)
      + (if 45 ≤ k then (133 - 2 * (k : ℚ)) * b (k - 45) else 0)) / (2 * (k : ℚ))
termination_by k
decreasing_by all_goals omega

theorem b_zero : b 0 = 1 := by
  rw [b]
  simp

/-- The recurrence, shifted:
`2(k+1) b_{k+1} = (2k+1) b_k + (2k−130) b_{k−43} + (131−2k) b_{k−44}`. -/
theorem b_rec (k : ℕ) :
    2 * ((k : ℚ) + 1) * b (k + 1) = (2 * (k : ℚ) + 1) * b k
      + (if 43 ≤ k then (2 * (k : ℚ) - 130) * b (k - 43) else 0)
      + (if 44 ≤ k then (131 - 2 * (k : ℚ)) * b (k - 44) else 0) := by
  have hk : (2 * ((k : ℚ) + 1)) ≠ 0 := by positivity
  conv_lhs => rw [b]
  rw [dif_neg (show k + 1 ≠ 0 by omega), Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    mul_div_assoc', mul_div_cancel_left₀ _ hk]
  by_cases h43 : 43 ≤ k
  · rw [if_pos (show 44 ≤ k + 1 by omega), if_pos h43, show k + 1 - 44 = k - 43 by omega]
    by_cases h44 : 44 ≤ k
    · rw [if_pos (show 45 ≤ k + 1 by omega), if_pos h44, show k + 1 - 45 = k - 44 by omega]
      ring
    · rw [if_neg (show ¬ 45 ≤ k + 1 by omega), if_neg h44]
      ring
  · rw [if_neg (show ¬ 44 ≤ k + 1 by omega), if_neg h43, if_neg (show ¬ 45 ≤ k + 1 by omega),
      if_neg (show ¬ 44 ≤ k by omega)]
    ring

/-- `F = ∑ b_k zᵏ`. -/
noncomputable def F : PowerSeries ℚ := PowerSeries.mk b

/-- `P = 1 + z + ⋯ + z⁴³`. -/
noncomputable def P : PowerSeries ℚ := ∑ i ∈ Finset.range 44, X ^ i

/-- `S = (1 − z)(1 − z⁴⁴)`. -/
noncomputable def S : PowerSeries ℚ := 1 - X ^ 1 - X ^ 44 + X ^ 45

/-- `Q = 1 − 44z⁴³ + 43z⁴⁴`. -/
noncomputable def Q : PowerSeries ℚ := 1 - C 44 * X ^ 43 + C 43 * X ^ 44

theorem coeff_S_mul (G : PowerSeries ℚ) (k : ℕ) :
    coeff k (S * G) = coeff k G - (if 1 ≤ k then coeff (k - 1) G else 0)
      - (if 44 ≤ k then coeff (k - 44) G else 0) + (if 45 ≤ k then coeff (k - 45) G else 0) := by
  simp only [S, sub_mul, add_mul, one_mul, map_sub, map_add, coeff_X_pow_mul']

theorem coeff_Q_mul (G : PowerSeries ℚ) (k : ℕ) :
    coeff k (Q * G) = coeff k G - 44 * (if 43 ≤ k then coeff (k - 43) G else 0)
      + 43 * (if 44 ≤ k then coeff (k - 44) G else 0) := by
  simp only [Q, sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul,
    coeff_X_pow_mul']

/-- `2 S F′ = Q F`, coefficientwise from the recurrence. -/
theorem F_ode : C 2 * (S * derivative ℚ F) = Q * F := by
  ext k
  rw [coeff_C_mul, coeff_S_mul, coeff_Q_mul]
  simp only [coeff_derivative, F, coeff_mk]
  have hr := b_rec k
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [Nat.le_zero, one_ne_zero, if_false, OfNat.ofNat_ne_zero, Nat.cast_zero] at hr ⊢
    linear_combination hr
  · simp only [if_pos (show 1 ≤ k by omega)]
    rw [show k - 1 + 1 = k by omega, Nat.cast_sub (show 1 ≤ k by omega)]
    by_cases h43 : 43 ≤ k
    · simp only [if_pos h43] at hr ⊢
      by_cases h44 : 44 ≤ k
      · simp only [if_pos h44] at hr ⊢
        rw [show k - 44 + 1 = k - 43 by omega, Nat.cast_sub h44]
        by_cases h45 : 45 ≤ k
        · simp only [if_pos h45]
          rw [show k - 45 + 1 = k - 44 by omega, Nat.cast_sub h45]
          push_cast
          linear_combination hr
        · have hk44 : k = 44 := by omega
          subst hk44
          simp only [if_neg h45]
          norm_num at hr ⊢
          linear_combination hr
      · simp only [if_neg h44] at hr ⊢
        have hk43 : k = 43 := by omega
        subst hk43
        simp only [if_neg (show ¬ 45 ≤ 43 by omega)]
        norm_num at hr ⊢
        linear_combination hr
    · simp only [if_neg h43, if_neg (show ¬ 44 ≤ k by omega), if_neg (show ¬ 45 ≤ k by omega)]
        at hr ⊢
      push_cast
      linear_combination hr

/-- `(1 − z) P = 1 − z⁴⁴`. -/
theorem P_geom : (1 - X) * P = 1 - X ^ 44 := mul_neg_geom_sum X 44

/-- `S P′ = Q P`. -/
theorem P_ode : S * derivative ℚ P = Q * P := by
  have h1 := P_geom
  have h2 := congrArg (derivative ℚ) h1
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at h2
  have e44 : (C 44 : PowerSeries ℚ) = 44 := map_ofNat C 44
  have e43 : (C 43 : PowerSeries ℚ) = 43 := map_ofNat C 43
  simp only [S, Q, e44, e43, pow_one]
  push_cast at h2
  linear_combination (1 - X ^ 44) * h2 + 44 * X ^ 43 * h1

/-- A power series `G` with `S G′ = Q G` and `G(0) = 0` vanishes. -/
theorem ode_unique (G : PowerSeries ℚ) (hG : S * derivative ℚ G = Q * G) (h0 : coeff 0 G = 0) :
    ∀ k, coeff k G = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · exact h0
    · have h := congrArg (coeff k) hG
      rw [coeff_S_mul, coeff_Q_mul] at h
      simp only [coeff_derivative] at h
      have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
      have e : ∀ m, m ≤ k → coeff m G = 0 := fun m hm => ih m (by omega)
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simpa [h0] using h
      · rw [e k le_rfl, e (k - 1 + 1) (by omega), e (k - 44 + 1) (by omega),
          e (k - 45 + 1) (by omega), e (k - 43) (by omega), e (k - 44) (by omega)] at h
        simp only [zero_mul, mul_zero, ite_self, sub_zero, add_zero] at h
        exact (mul_eq_zero.1 h).resolve_right (by exact_mod_cast hk)

/-- **`F² = P`**: the recurrence defines the Taylor coefficients of `√(1 + z + ⋯ + z⁴³)`. -/
theorem F_sq : F ^ 2 = P := by
  have hA := F_ode
  have hP := P_ode
  have hG : S * derivative ℚ (F ^ 2 - P) = Q * (F ^ 2 - P) := by
    have hd : derivative ℚ (F ^ 2) = C 2 * (F * derivative ℚ F) := by
      rw [sq, Derivation.leibniz, show (C 2 : PowerSeries ℚ) = 2 from map_ofNat C 2]
      try simp only [smul_eq_mul]
      ring
    rw [map_sub, hd]
    linear_combination F * hA - hP
  have h0 : coeff 0 (F ^ 2 - P) = 0 := by
    have hF0 : coeff 0 F = 1 := by simp [F, b_zero]
    have hP0 : coeff 0 P = 1 := by simp [P, map_sum, coeff_X_pow]
    rw [map_sub, coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
      hF0, hP0]
    norm_num
  have := ode_unique _ hG h0
  exact sub_eq_zero.1 (PowerSeries.ext fun k => by simpa using this k)

end Principia.MathDB.P369172
