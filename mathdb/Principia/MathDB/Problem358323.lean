import Mathlib

/-!
# MathDB #358323 — Chung's zero-set limit for `1/((at² + bt + c)(1 − tz))` does not exist

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/358323/solution.tex`, refuting Conjecture 47 of Chung (p. 119):
for real nonzero `a, b, c` with `b² − 4ac ≤ 0`, the polynomials `P_m` defined by
`∑ P_m(z) tᵐ = 1/((at² + bt + c)(1 − tz))` satisfy `lim Z(P_m) = {|z| = 1/|t₁|}`, with `t₁` a
smallest-modulus zero of `at² + bt + c`.  The limit is the source's set limit (Definitions 38–41):
`w ∈ limsup` iff every ball around `w` meets `Z(P_m)` for arbitrarily large `m`; `w ∈ liminf` iff
it does for all large `m`; the limit is defined when the two agree.

**Encoding.**  With `1/(at² + bt + c) = ∑ cₖ tᵏ` (`cf`, by the recurrence
`c·c₀ = 1`, `c·c₁ + b·c₀ = 0`, `c·c_{k+2} + b·c_{k+1} + a·c_k = 0`), multiplication by
`1/(1 − tz)` gives `P_m(z) = ∑_{k ≤ m} cₖ z^{m−k}` (`P`).  Checked in SymPy against the series of
`1/((1 + t + t²)(1 − tz))` for `m < 12`.

**What is refuted.**  `not_limitExists` refutes the weakest reading — that the limit merely EXISTS
(`liminf = limsup`), with no claim about the circle — at `a = b = c = 1`.  `not_conj47` refutes
the full statement, whose hypotheses (a smallest-modulus zero `t₁`) the witness satisfies.

**Route (the write-up's).**  At `a = b = c = 1`, `cₖ = 1, −1, 0` by `k mod 3`; so
`P_{3r+2}(0) = c_{3r+2} = 0` puts `0` in the upper limit, while
`P_{3r+1}(z)·(z² + z + 1) = z^{3r+3} − 1` (checked in SymPy for `r < 6`, proved here for all `r`)
puts every zero of `P_{3r+1}` on `|z| = 1`, so the ball of radius `1/2` about `0` misses them and
`0` is not in the lower limit.
-/

namespace Principia.MathDB.P358323

open Polynomial

/-- The coefficients of `1/(at² + bt + c)`. -/
noncomputable def cf (a b c : ℝ) : ℕ → ℝ
  | 0 => 1 / c
  | 1 => -(b * cf a b c 0) / c
  | (k + 2) => -(b * cf a b c (k + 1) + a * cf a b c k) / c

/-- `P_m(z) = ∑_{k ≤ m} cₖ z^{m−k}`, the coefficient of `tᵐ` in `1/((at² + bt + c)(1 − tz))`. -/
noncomputable def P (a b c : ℝ) (m : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (m + 1), C (cf a b c k : ℂ) * X ^ (m - k)

/-- The zero set `Z(p)`. -/
def Z (p : ℂ[X]) : Set ℂ := {z | p.eval z = 0}

/-- The upper set limit (Definition 39 of the source). -/
def limsupZ (F : ℕ → Set ℂ) : Set ℂ :=
  {w | ∀ r : ℝ, 0 < r → ∀ N : ℕ, ∃ m ≥ N, ∃ z ∈ F m, ‖z - w‖ < r}

/-- The lower set limit (Definition 40 of the source). -/
def liminfZ (F : ℕ → Set ℂ) : Set ℂ :=
  {w | ∀ r : ℝ, 0 < r → ∃ N : ℕ, ∀ m ≥ N, ∃ z ∈ F m, ‖z - w‖ < r}

/-- The weakest reading: the zero-set limit exists. -/
def LimitExists : Prop :=
  ∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → b ^ 2 - 4 * a * c ≤ 0 →
    liminfZ (fun m => Z (P a b c m)) = limsupZ (fun m => Z (P a b c m))

/-- **Conjecture 47**: the limit exists and is the circle `|z| = 1/|t₁|`. -/
def Conj47 : Prop :=
  ∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → b ^ 2 - 4 * a * c ≤ 0 →
    ∀ t₁ : ℂ, (a : ℂ) * t₁ ^ 2 + (b : ℂ) * t₁ + (c : ℂ) = 0 →
      (∀ t : ℂ, (a : ℂ) * t ^ 2 + (b : ℂ) * t + (c : ℂ) = 0 → ‖t₁‖ ≤ ‖t‖) →
      liminfZ (fun m => Z (P a b c m)) = limsupZ (fun m => Z (P a b c m)) ∧
        limsupZ (fun m => Z (P a b c m)) = {z | ‖z‖ = 1 / ‖t₁‖}

theorem cf_rec (k : ℕ) : cf 1 1 1 (k + 2) = -(cf 1 1 1 (k + 1) + cf 1 1 1 k) := by
  rw [cf]
  ring

/-- `cₖ = 1, −1, 0` according to `k mod 3`. -/
theorem cf_one (j : ℕ) :
    cf 1 1 1 (3 * j) = 1 ∧ cf 1 1 1 (3 * j + 1) = -1 ∧ cf 1 1 1 (3 * j + 2) = 0 := by
  induction j with
  | zero => norm_num [cf]
  | succ j ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e0 : cf 1 1 1 (3 * (j + 1)) = 1 := by
      have := cf_rec (3 * j + 1)
      rw [show 3 * j + 1 + 2 = 3 * (j + 1) by ring, show 3 * j + 1 + 1 = 3 * j + 2 by ring,
        h2, h1] at this
      linarith
    have e1 : cf 1 1 1 (3 * (j + 1) + 1) = -1 := by
      have := cf_rec (3 * j + 2)
      rw [show 3 * j + 2 + 2 = 3 * (j + 1) + 1 by ring, show 3 * j + 2 + 1 = 3 * (j + 1) by ring,
        e0, h2] at this
      linarith
    have e2 : cf 1 1 1 (3 * (j + 1) + 2) = 0 := by
      have := cf_rec (3 * (j + 1))
      rw [e1, e0] at this
      linarith
    exact ⟨e0, e1, e2⟩

/-- `P_{m+1}(z) = z·P_m(z) + c_{m+1}`. -/
theorem eval_P_succ (a b c : ℝ) (m : ℕ) (z : ℂ) :
    (P a b c (m + 1)).eval z = z * (P a b c m).eval z + (cf a b c (m + 1) : ℂ) := by
  simp only [P, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
    ring
  · simp

theorem eval_zero_P (a b c : ℝ) (m : ℕ) : (P a b c m).eval 0 = (cf a b c m : ℂ) := by
  rcases m with _ | m
  · simp [P]
  · rw [eval_P_succ]
    simp

/-- `P_{3r+1}(z)·(z² + z + 1) = z^{3r+3} − 1`. -/
theorem key (r : ℕ) (z : ℂ) :
    (P 1 1 1 (3 * r + 1)).eval z * (z ^ 2 + z + 1) = z ^ (3 * r + 3) - 1 := by
  induction r with
  | zero =>
    have e := eval_P_succ 1 1 1 0 z
    have e0 : (P 1 1 1 0).eval z = 1 := by simp [P, cf]
    have c1 : cf 1 1 1 (0 + 1) = -1 := by norm_num [cf]
    rw [e0, c1] at e
    rw [show 3 * 0 + 1 = 0 + 1 from rfl, e]
    push_cast
    ring
  | succ r ih =>
    obtain ⟨-, -, h2⟩ := cf_one r
    obtain ⟨h3, h4, -⟩ := cf_one (r + 1)
    have e1 := eval_P_succ 1 1 1 (3 * r + 1) z
    have e2 := eval_P_succ 1 1 1 (3 * r + 2) z
    have e3 := eval_P_succ 1 1 1 (3 * (r + 1)) z
    rw [show 3 * r + 1 + 1 = 3 * r + 2 from rfl, h2] at e1
    rw [show 3 * r + 2 + 1 = 3 * (r + 1) by ring, h3] at e2
    rw [h4] at e3
    rw [e3, e2, e1]
    push_cast
    linear_combination z ^ 3 * ih

/-- Every zero of `P_{3r+1}` lies on the unit circle. -/
theorem norm_of_zero (r : ℕ) (z : ℂ) (hz : (P 1 1 1 (3 * r + 1)).eval z = 0) : ‖z‖ = 1 := by
  have h := key r z
  rw [hz, zero_mul] at h
  have h1 : z ^ (3 * r + 3) = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).1 h2

/-- `0` is in the upper limit: `P_{3r+2}(0) = 0` for every `r`. -/
theorem zero_mem_limsup : (0 : ℂ) ∈ limsupZ (fun m => Z (P 1 1 1 m)) := by
  intro r hr N
  refine ⟨3 * N + 2, by omega, 0, ?_, by simpa using hr⟩
  show (P 1 1 1 (3 * N + 2)).eval 0 = 0
  rw [eval_zero_P, (cf_one N).2.2]
  simp

/-- `0` is not in the lower limit: the zeros of `P_{3r+1}` stay on `|z| = 1`. -/
theorem zero_not_mem_liminf : (0 : ℂ) ∉ liminfZ (fun m => Z (P 1 1 1 m)) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  obtain ⟨z, hz, hlt⟩ := hN (3 * N + 1) (by omega)
  have hn := norm_of_zero N z hz
  rw [sub_zero, hn] at hlt
  norm_num at hlt

/-- **The limit does not exist** at `a = b = c = 1`. -/
theorem not_limitExists : ¬ LimitExists := by
  intro h
  have hlim := h 1 1 1 one_ne_zero one_ne_zero one_ne_zero (by norm_num)
  exact zero_not_mem_liminf (by rw [hlim]; exact zero_mem_limsup)

/-- The zeros of `t² + t + 1` have modulus one. -/
theorem root_norm (t : ℂ) (h : t ^ 2 + t + 1 = 0) : ‖t‖ = 1 := by
  have h3 : t ^ 3 = 1 := by linear_combination (t - 1) * h
  have h4 := congrArg norm h3
  rw [norm_pow, norm_one] at h4
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg t) (by norm_num)).1 h4

/-- **MathDB #358323: Chung's Conjecture 47 is false.** -/
theorem not_conj47 : ¬ Conj47 := by
  intro h
  have hdeg : (X ^ 2 + X + 1 : ℂ[X]).degree = 2 := by compute_degree!
  obtain ⟨t₁, ht⟩ := Complex.exists_root (f := (X ^ 2 + X + 1 : ℂ[X])) (by rw [hdeg]; norm_num)
  have ht₁ : t₁ ^ 2 + t₁ + 1 = 0 := by simpa using ht
  have hroot : ∀ t : ℂ, ((1 : ℝ) : ℂ) * t ^ 2 + ((1 : ℝ) : ℂ) * t + ((1 : ℝ) : ℂ) = 0 →
      ‖t‖ = 1 := fun t ht' => root_norm t (by simpa using ht')
  have ht₁' : ((1 : ℝ) : ℂ) * t₁ ^ 2 + ((1 : ℝ) : ℂ) * t₁ + ((1 : ℝ) : ℂ) = 0 := by
    simpa using ht₁
  obtain ⟨hlim, -⟩ := h 1 1 1 one_ne_zero one_ne_zero one_ne_zero (by norm_num) t₁ ht₁'
    (fun t ht' => by rw [hroot t₁ ht₁', hroot t ht'])
  exact zero_not_mem_liminf (by rw [hlim]; exact zero_mem_limsup)

end Principia.MathDB.P358323
