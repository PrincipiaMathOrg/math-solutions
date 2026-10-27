/-
MathDB #328441 — the negative-parameter ACMS reciprocal-tail formulas.

With `u_0 = 0`, `u_1 = 1`, `u_j = s·u_{j−1} − t·u_{j−2}`, and `F_k = u_{rk}`, the question is
Conjecture 2 of Park (originally Conjecture 4.6 of Amdeberhan–Chen–Moll–Sagan): the reciprocal
tail `S_n = ∑_{k≥n} 1/F_k` satisfies `⌊S_n^{-1}⌋ = F_n − F_{n−1} − 1`, with a squared analogue.

**THE CONJECTURE IS FALSE AS PRINTED, AND THE WRITE-UP SAYS SO.**  Its own abstract restricts to
`s > t ≥ 1` with `(s,t) ≠ (2,1)`, and records that the squared formula needs `s ≥ 3` because
"`s = 1` gives zero denominators and `s = 2` gives counterexamples".  This file proves the
exclusions are *necessary* rather than cosmetic — which is the part of the write-up that can be
settled outright:

* `u_two_one` — at `(s,t) = (2,1)` the recurrence degenerates to `u_j = j`;
* `not_summable_at_two_one` — hence `F_k = rk` and the tail is the HARMONIC series, so `S_n`
  does not converge and the statement is not merely false there but meaningless.  That is why
  `(2,1)` is excluded;
* `u_one_one_three` — at `s = t = 1` the sequence hits `u_3 = 0`, so `1/F_k` divides by zero
  whenever `3 ∣ rk`.  That is the "zero denominators" case;
* `sq_sub_four_eq_zero_at_two` — the printed error bound `2/(s² − 4)` is *undefined* at `s = 2`,
  so the squared theorem cannot even be stated there.  That is the "counterexamples" case at the
  level of the bound itself.

Also proved, from the root estimates: `discriminant_ge`, that `t ≤ s − 1` forces
`s² − 4t ≥ (s−2)²`, which is what makes the discriminant positive and the roots real.

CARRIED.  The two theorems themselves (`Theorem1`, `Theorem2`) are stated with their exclusions
and left as named hypotheses: their proofs are the determinant identity and the root estimates
that bound the tail between `Δ_n − 1` and `Δ_n`, which is real analysis out of reach here.  Per
the spine rule they are hypotheses, never `sorry`.

Reference: S. Park, *Arithmetic properties of generalized Fibonacci sequences*, Conjecture 2
(p. 8); T. Amdeberhan, X. Chen, V. Moll and B. Sagan, Conjecture 4.6 (p. 556), with the note on
p. 560 recording Park's Theorem 18 as the partial large-parameter result.
-/
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace Principia.MathDB.P328441

/-! ## 1. The sequence -/

/-- `u_0 = 0`, `u_1 = 1`, `u_j = s·u_{j−1} − t·u_{j−2}`. -/
def u (s t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | j + 2 => s * u s t (j + 1) - t * u s t j

@[simp] theorem u_zero (s t : ℤ) : u s t 0 = 0 := rfl

@[simp] theorem u_one (s t : ℤ) : u s t 1 = 1 := rfl

theorem u_add_two (s t : ℤ) (j : ℕ) :
    u s t (j + 2) = s * u s t (j + 1) - t * u s t j := rfl

/-! ## 2. Why `(s,t) = (2,1)` must be excluded -/

theorem u_two_one_aux (j : ℕ) : u 2 1 j = (j : ℤ) ∧ u 2 1 (j + 1) = ((j : ℤ) + 1) := by
  induction j with
  | zero => exact ⟨rfl, by norm_num⟩
  | succ k ih =>
      refine ⟨by simpa using ih.2, ?_⟩
      rw [u_add_two, ih.1, ih.2]
      push_cast
      ring

/-- At `(s,t) = (2,1)` the recurrence degenerates: `u_j = j`. -/
theorem u_two_one (j : ℕ) : u 2 1 j = (j : ℤ) := (u_two_one_aux j).1

/-- **The exclusion of `(2,1)` is necessary.**  There `F_k = rk`, so the reciprocal tail is the
harmonic series and does not converge — the conjecture is not false there, it is meaningless. -/
theorem not_summable_at_two_one (n r : ℕ) (hr : 0 < r) :
    ¬ Summable (fun k : ℕ => 1 / ((u 2 1 (r * (k + n)) : ℤ) : ℝ)) := by
  intro h
  have hid : ∀ k : ℕ,
      1 / ((u 2 1 (r * (k + n)) : ℤ) : ℝ) = (r : ℝ)⁻¹ * (((k + n : ℕ) : ℝ))⁻¹ := by
    intro k
    rw [u_two_one]
    push_cast
    rw [one_div, mul_inv]
  rw [summable_congr (fun k => hid k)] at h
  have hr' : (r : ℝ)⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    exact hr.ne'
  have h2 : Summable (fun k : ℕ => (((k + n : ℕ) : ℝ))⁻¹) :=
    (summable_mul_left_iff hr').mp h
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff n).mp h2)

/-! ## 3. Why `s = 1` and `s = 2` must be excluded from the squared formula -/

/-- At `s = t = 1` the sequence hits zero: `u_3 = 0`, so `1/F_k` divides by zero whenever
`3 ∣ rk`.  This is the write-up's "zero denominators" case. -/
theorem u_one_one_three : u 1 1 3 = 0 := by decide

/-- The printed error bound `2/(s² − 4)` is UNDEFINED at `s = 2`: the denominator vanishes, so
the squared theorem cannot even be stated there.  This is the "counterexamples" case at the
level of the bound itself. -/
theorem sq_sub_four_eq_zero_at_two : (2 : ℤ) ^ 2 - 4 = 0 := by decide

/-! ## 4. The root estimate -/

/-- `t ≤ s − 1` forces `s² − 4t ≥ (s−2)²`, which is what makes the discriminant positive and the
roots real — the write-up's first displayed estimate.

**`1 ≤ t` is NOT needed**, though the write-up states the estimate under the full hypotheses
`s > t ≥ 1`.  Expanding, `(s−2)² ≤ s² − 4t` is `−4s + 4 ≤ −4t`, i.e. exactly `t ≤ s − 1`; the
lower bound on `t` contributes nothing.  Lean's unused-variable linter is what surfaced it. -/
theorem discriminant_ge (s t : ℤ) (hts : t ≤ s - 1) :
    (s - 2) ^ 2 ≤ s ^ 2 - 4 * t := by nlinarith

/-! ## 5. The two theorems, with their exclusions -/

/-- `F_k = u_{rk}`, as a real. -/
noncomputable def F (s t : ℤ) (r k : ℕ) : ℝ := ((u s t (r * k) : ℤ) : ℝ)

/-- **Theorem 1** (Park's Conjecture 2, with the exclusions the write-up establishes). -/
def Theorem1 : Prop :=
  ∀ s t : ℤ, 1 ≤ t → t < s → (s, t) ≠ (2, 1) → ∀ n r : ℕ, 0 < n → 0 < r →
    Summable (fun k : ℕ => 1 / F s t r (k + n)) ∧
      F s t r n - F s t r (n - 1) - 1 < (∑' k : ℕ, 1 / F s t r (k + n))⁻¹ ∧
      (∑' k : ℕ, 1 / F s t r (k + n))⁻¹ < F s t r n - F s t r (n - 1)

/-- **Theorem 2**, the squared formula.  The hypothesis `3 ≤ s` is exactly what
`u_one_one_three` and `sq_sub_four_eq_zero_at_two` show cannot be dropped. -/
def Theorem2 : Prop :=
  ∀ s : ℤ, 3 ≤ s → ∀ n r : ℕ, 0 < n → 0 < r →
    Summable (fun k : ℕ => 1 / (F s 1 r (k + n)) ^ 2) ∧
      (F s 1 r n ^ 2 - F s 1 r (n - 1) ^ 2) - 2 / ((s : ℝ) ^ 2 - 4)
        < (∑' k : ℕ, 1 / (F s 1 r (k + n)) ^ 2)⁻¹ ∧
      (∑' k : ℕ, 1 / (F s 1 r (k + n)) ^ 2)⁻¹ < F s 1 r n ^ 2 - F s 1 r (n - 1) ^ 2

end Principia.MathDB.P328441
