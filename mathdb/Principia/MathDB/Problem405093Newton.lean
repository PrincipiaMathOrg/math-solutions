import Mathlib

/-!
# MathDB #405093 — Newton's inequality for real-rooted polynomials with nonpositive roots

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex` (unimodality and log-concavity of a lattice-path
sequence).  Its Lemma (Newton's inequalities) needs, for `R = F^{(ℓ−1)}` of degree `m` with only
nonpositive zeros, `R(0) R''(0) ≤ ((m−1)/m) R'(0)²`, i.e. in coefficients
`m · 2c₂c₀ ≤ (m−1) · c₁²`.  Mathlib has no Newton inequalities.

The write-up proves this through the logarithmic derivative and Cauchy–Schwarz.  Here it is proved
by induction over the linear factors, with no roots in sight: for `P = ∏ (X + sᵢ)`, `sᵢ ≥ 0`, one
factor `X + a` sends `(c₀, c₁, c₂)` to `(a c₀, c₀ + a c₁, c₁ + a c₂)` and the step is the exact
identity `m · goal = (m c₀ − a c₁)² + a²(m+1) · IH` (checked in SymPy).  `newton_splits` transfers
it to any real polynomial whose roots are all real (`card roots = natDegree`) and nonpositive.  The
lattice-path theorem is the consumer.
-/

namespace Principia.MathDB.P405093

open Polynomial

/-- The coefficients of `∏ (X + a)` over a multiset of nonnegative reals are nonnegative. -/
theorem prod_coeff_nonneg (s : Multiset ℝ) (hs : ∀ a ∈ s, 0 ≤ a) :
    ∀ n, 0 ≤ ((s.map fun a => X + C a).prod).coeff n := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n
    rcases n with _ | n <;> simp [coeff_one]
  | cons a s ih =>
    intro n
    have ha := hs a (Multiset.mem_cons_self a s)
    have ih' := ih fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons]
    rcases n with _ | n
    · simp only [mul_coeff_zero, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      exact mul_nonneg ha (ih' 0)
    · simp only [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
      exact add_nonneg (ih' n) (mul_nonneg ha (ih' (n + 1)))

/-- **Newton's inequality for `∏ (X + a)`**: `m · 2c₂c₀ ≤ (m−1) · c₁²` with `m = card s`. -/
theorem newton_prod (s : Multiset ℝ) (hs : ∀ a ∈ s, 0 ≤ a) :
    (Multiset.card s : ℝ) * (2 * ((s.map fun a => X + C a).prod).coeff 2
        * ((s.map fun a => X + C a).prod).coeff 0)
      ≤ ((Multiset.card s : ℝ) - 1) * ((s.map fun a => X + C a).prod).coeff 1 ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [coeff_one]
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, 0 ≤ b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have IH := ih hs'
    have h0 := prod_coeff_nonneg s hs' 0
    have h1 := prod_coeff_nonneg s hs' 1
    have h2 := prod_coeff_nonneg s hs' 2
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp [coeff_one, coeff_X]
    have hmpos : (0 : ℝ) < Multiset.card s := by exact_mod_cast Multiset.card_pos.2 hs0
    set P := (s.map fun a => X + C a).prod
    have e0 : ((X + C a) * P).coeff 0 = a * P.coeff 0 := by
      simp only [mul_coeff_zero, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
    have e1 : ((X + C a) * P).coeff 1 = P.coeff 0 + a * P.coeff 1 := by
      simp only [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
    have e2 : ((X + C a) * P).coeff 2 = P.coeff 1 + a * P.coeff 2 := by
      simp only [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
    rw [e0, e1, e2]
    push_cast
    set m : ℝ := (Multiset.card s : ℝ)
    have key : m * (m * (P.coeff 0 + a * P.coeff 1) ^ 2
        - (m + 1) * (2 * (P.coeff 1 + a * P.coeff 2) * (a * P.coeff 0)))
        = (m * P.coeff 0 - a * P.coeff 1) ^ 2
          + a ^ 2 * (m + 1) * ((m - 1) * P.coeff 1 ^ 2 - m * (2 * P.coeff 2 * P.coeff 0)) := by
      ring
    have hIH : 0 ≤ (m - 1) * P.coeff 1 ^ 2 - m * (2 * P.coeff 2 * P.coeff 0) := by linarith
    have hrhs : 0 ≤ (m * P.coeff 0 - a * P.coeff 1) ^ 2
        + a ^ 2 * (m + 1) * ((m - 1) * P.coeff 1 ^ 2 - m * (2 * P.coeff 2 * P.coeff 0)) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg a) (by linarith)) hIH)
    rw [← key] at hrhs
    have hdiff : 0 ≤ m * (P.coeff 0 + a * P.coeff 1) ^ 2
        - (m + 1) * (2 * (P.coeff 1 + a * P.coeff 2) * (a * P.coeff 0)) :=
      nonneg_of_mul_nonneg_right (by linarith) hmpos
    nlinarith [hdiff]

/-- **Newton's inequality** for a real polynomial whose roots are all real and nonpositive:
`deg · 2c₂c₀ ≤ (deg − 1) · c₁²`. -/
theorem newton_splits (R : ℝ[X]) (hR : Multiset.card R.roots = R.natDegree)
    (hneg : ∀ r ∈ R.roots, r ≤ 0) :
    (R.natDegree : ℝ) * (2 * R.coeff 2 * R.coeff 0) ≤ ((R.natDegree : ℝ) - 1) * R.coeff 1 ^ 2 := by
  set s := R.roots.map (fun r => -r) with hs_def
  have hs : ∀ a ∈ s, 0 ≤ a := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 ha
    linarith [hneg r hr]
  have hcard : Multiset.card s = R.natDegree := by
    rw [Multiset.card_map, hR]
  have hprod : (R.roots.map fun a => X - C a) = s.map fun a => X + C a := by
    rw [hs_def, Multiset.map_map]
    refine Multiset.map_congr rfl fun r _ => ?_
    simp [sub_eq_add_neg]
  have hRe : R = C R.leadingCoeff * (s.map fun a => X + C a).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hR]
    rw [hprod]
  have hN := newton_prod s hs
  rw [hcard] at hN
  have hc : ∀ n, R.coeff n = R.leadingCoeff * ((s.map fun a => X + C a).prod).coeff n := by
    intro n
    conv_lhs => rw [hRe]
    rw [coeff_C_mul]
  rw [hc 0, hc 1, hc 2]
  nlinarith [mul_le_mul_of_nonneg_left hN (sq_nonneg R.leadingCoeff)]

end Principia.MathDB.P405093
