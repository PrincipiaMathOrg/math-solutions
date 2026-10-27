import Mathlib

set_option autoImplicit false

namespace Principia.MathDB.P325507

/-- Positive part of a real scalar (a `1 × 1` Hermitian matrix). -/
def pp (x : ℝ) : ℝ := max x 0

/-- Negative part, so `x = pp x - np x` and `|x| = pp x + np x`. -/
def np (x : ℝ) : ℝ := max (-x) 0

theorem sub_parts (x : ℝ) : pp x - np x = x := by
  unfold pp np
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem add_parts (x : ℝ) : pp x + np x = |x| := by
  unfold pp np
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring

/-- **The polynomial clause of the signed mean-value trace conjecture, for real scalars** —
Paulin–Mackey–Tropp, Conjecture 7.3 (2013) p. 17 and Conjecture 13.4 (2016) pp. 3465–3466.
Neither source restricts `A` or `B` to be positive semidefinite, and the final article separately
asserts validity for scalars, which is exactly what this states. -/
def PolyClauseScalar : Prop :=
  ∀ (A B C : ℝ) (q : ℕ), 1 ≤ q → ∀ s : ℝ, 0 < s →
    C * (A ^ q - B ^ q) ≤
      (q / 2) * ((s * (pp (A - B)) ^ 2 + s⁻¹ * (pp C) ^ 2) * |A| ^ (q - 1)
        + (s * (np (A - B)) ^ 2 + s⁻¹ * (np C) ^ 2) * |B| ^ (q - 1))

/-- **THE CLAUSE IS FALSE.**  At `A = −2`, `B = −1`, `C = −1`, `q = 3`, `s = 1` the left side is
`7` and the right side is `3`. -/
theorem polyClauseScalar_false : ¬ PolyClauseScalar := by
  intro h
  have := h (-2) (-1) (-1) 3 (by norm_num) 1 (by norm_num)
  norm_num [pp, np] at this

/-! ### The failure is not isolated: the same point fails at every odd degree -/

/-- At `A = −2`, `B = −1`, `C = −1`, `s = 1` the left side is `2^q − 1` for odd `q`. -/
theorem lhs_odd (q : ℕ) (hq : Odd q) :
    (-1 : ℝ) * ((-2) ^ q - (-1) ^ q) = 2 ^ q - 1 := by
  rw [hq.neg_pow, hq.neg_pow]
  ring

/-- ...and the right side is exactly `q`.  No lower bound on `q` is needed: the `D₊`/`C₊` terms
vanish, and at `q = 0` both sides are `0`. -/
theorem rhs_eq (q : ℕ) :
    ((q : ℝ) / 2) * ((1 * (pp ((-2) - (-1))) ^ 2 + (1 : ℝ)⁻¹ * (pp (-1)) ^ 2) * |(-2 : ℝ)| ^ (q - 1)
      + (1 * (np ((-2) - (-1))) ^ 2 + (1 : ℝ)⁻¹ * (np (-1)) ^ 2) * |(-1 : ℝ)| ^ (q - 1)) = q := by
  norm_num [pp, np]

/-- `q + 1 < 2 ^ q` for `q ≥ 2`, the elementary gap that makes every odd degree fail. -/
theorem succ_lt_two_pow (q : ℕ) (hq : 2 ≤ q) : q + 1 < 2 ^ q := by
  induction q with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp_all
    · have := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-- **Every odd degree `q ≥ 3` fails at the same point**: `2^q − 1 > q`. -/
theorem odd_degree_fails (q : ℕ) (hq : 3 ≤ q) : (q : ℝ) < 2 ^ q - 1 := by
  have h := succ_lt_two_pow q (by omega)
  have : ((q : ℝ) + 1) < 2 ^ q := by exact_mod_cast h
  linarith

end Principia.MathDB.P325507
