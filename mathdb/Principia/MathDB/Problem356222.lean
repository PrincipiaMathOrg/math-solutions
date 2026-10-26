import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MathDB #356222 — the Euler-transform candidate is not an optimal OGF

Write-up: `mathdb-open-problems/problems/356222/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: M. D. Schmidt, *Factorization theorems and canonical representations for generating
functions of special sums*, Georgia Tech dissertation, Chapter 5, **Conjecture 5.93**
(p. 87), which proposes the Euler-transform series `C_D(q)` as an **optimal** selection for
the correlation score of Notation 5.85 / Question 5.86,

`Corr(C,D) = ∑_{n≥1} (1/n) · (∑_{k=1}^n |c_k D⁻¹(n,k)|) / ((∑ c_k²)^{1/2} (∑ D⁻¹(n,k)²)^{1/2})`.

## The refutation formalized here

Take the **identity kernel** `D(n,k) = δ_{nk}` — lower triangular, invertible, integral,
unit diagonal, hence admissible under the source's own conditions.  Then `D⁻¹ = D` and the
score collapses to the write-up's equation (5),

`F(C) = ∑_{n≥1} |c_n| / (n · (∑_{k=1}^n c_k²)^{1/2})`,

which is what `score` is below.  The competitors are the write-up's normalized integer
polynomials `P_N(q) = 1 + ∑_{k=1}^N 2^{k-1} q^k` (`cf`).

**`not_conj` is the refutation: no real number bounds the competitors' scores.**  So
whatever finite score the proposed candidate has — and the source's optimization *requires*
a finite score — it is not an upper bound for the admissible competitors, and therefore not
optimal.  `score_unbounded` is the same fact stated directly.

The chain is `Sq_eq` (`∑_{k≤n} c_k² = (4ⁿ−1)/3`) → `term_lb` (each summand exceeds
`(√3/2)/n`, because `√3·√((4ⁿ−1)/3) = √(4ⁿ−1) ≤ 2ⁿ`) → `score_lb`
(`F(P_N) ≥ (√3/2)·H_N`) → the divergence of the harmonic series.

## What this deliberately does NOT formalize

The write-up also proves `Corr(E,D) < 2` for the candidate `E(q) = exp(−q/(1−q))`, via a
Parseval bound `∑ eₙ² ≤ e − 1` obtained from a contour integral.  That half is **not needed**
for the refutation above — unboundedness alone defeats optimality for any finite score — and
it is not formalized here.  `Campaigns/MathDB-Formalization/verify_356222.py` checks it
numerically (partial `F(E) ≈ 1.48`, `∑ eₙ² ≈ 1.61`) only to confirm the write-up is
self-consistent.

**Not Lean-checked:** that the identity kernel is admissible for the source's optimization,
and that the score specializes to (5) there.  Both are read off the source's own conditions,
as `#360860` reads off its barycentre formula.  Admissibility of the *competitors* is not
assumed — `cf` is manifestly integer-valued with `P_N(0) = 1` and `c₁ = 1 ≠ 0`, and
`score_eq_sum` shows each score is a finite sum, hence finite.

Values checked in `Campaigns/MathDB-Formalization/verify_356222.py`.
-/

namespace Principia.MathDB.P356222

open Filter

/-- Coefficient `c_k` of the competitor `P_N(q) = 1 + ∑_{k=1}^N 2^{k-1} qᵏ`, for `k ≥ 1`.
The constant term `c₀ = 1` never enters the score, whose sums start at `k = 1`. -/
def cf (N k : ℕ) : ℝ := if k = 0 ∨ N < k then 0 else 2 ^ (k - 1)

theorem cf_zero (N : ℕ) : cf N 0 = 0 := by
  rw [cf, if_pos (Or.inl rfl)]

theorem cf_of_gt {N k : ℕ} (h : N < k) : cf N k = 0 := by
  rw [cf, if_pos (Or.inr h)]

theorem cf_succ {N m : ℕ} (h : m + 1 ≤ N) : cf N (m + 1) = 2 ^ m := by
  rw [cf, if_neg (by omega)]
  norm_num

/-- `S_n = ∑_{k=1}^n c_k²`, written over `range n` with the shift `k = i+1`. -/
def Sq (N n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (cf N (i + 1)) ^ 2

/-- The `n`-th summand of the identity-kernel score (5). -/
noncomputable def term (N n : ℕ) : ℝ := |cf N n| / (n * Real.sqrt (Sq N n))

/-- The score `F(P_N)`, as a genuine infinite sum over all `n`. -/
noncomputable def score (N : ℕ) : ℝ := ∑' n : ℕ, term N n

/-- The harmonic sum, indexed to match Mathlib's divergence lemma. -/
noncomputable def Hsum (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, (1 / (i + 1) : ℝ)

/-! ### The coefficient sums -/

theorem Sq_eq {N : ℕ} : ∀ n : ℕ, n ≤ N → Sq N n = ((4:ℝ) ^ n - 1) / 3 := by
  intro n
  induction n with
  | zero => intro _; rw [Sq]; norm_num
  | succ m ih =>
    intro h
    rw [Sq, Finset.sum_range_succ, ← Sq, ih (by omega), cf_succ h]
    have h4 : ((2:ℝ) ^ m) ^ 2 = (4:ℝ) ^ m := by
      rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
    rw [h4, pow_succ]
    ring

theorem Sq_pos {N n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) : 0 < Sq N n := by
  rw [Sq_eq n h2]
  have : (4:ℝ) ^ 1 ≤ (4:ℝ) ^ n := by
    apply pow_le_pow_right₀ (by norm_num) h1
  norm_num at this ⊢
  linarith

/-! ### Each summand exceeds `(√3/2)/n` -/

theorem sqrt_three_mul {N n : ℕ} (h2 : n ≤ N) :
    Real.sqrt 3 * Real.sqrt (Sq N n) = Real.sqrt ((4:ℝ) ^ n - 1) := by
  rw [Sq_eq n h2, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring

theorem sqrt_le_pow (n : ℕ) : Real.sqrt ((4:ℝ) ^ n - 1) ≤ 2 ^ n := by
  have hp : ((2:ℝ) ^ n) ^ 2 = (4:ℝ) ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  have h0 : (0:ℝ) ≤ 2 ^ n := by positivity
  rw [show ((2:ℝ) ^ n) = Real.sqrt (((2:ℝ) ^ n) ^ 2) from (Real.sqrt_sq h0).symm, hp]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Each summand of `F(P_N)` exceeds `(√3/2)/n`.** -/
theorem term_lb {N n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) :
    Real.sqrt 3 / 2 / (n : ℝ) ≤ term N n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hSq : 0 < Sq N (m + 1) := Sq_pos h1 h2
  have hs : 0 < Real.sqrt (Sq N (m + 1)) := Real.sqrt_pos.2 hSq
  have hn : (0:ℝ) < ((m : ℝ) + 1) := by positivity
  have hc : |cf N (m + 1)| = 2 ^ m := by
    rw [cf_succ h2, abs_of_nonneg (by positivity)]
  have key : Real.sqrt 3 * Real.sqrt (Sq N (m + 1)) ≤ 2 ^ (m + 1) := by
    rw [sqrt_three_mul h2]; exact sqrt_le_pow _
  rw [term, hc]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hexp : (2:ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
  nlinarith [key, hn, hs.le, hexp]

/-! ### The score of `P_N` is a finite sum, bounded below by `(√3/2)·H_N` -/

theorem term_eq_zero_of_gt {N n : ℕ} (h : N < n) : term N n = 0 := by
  rw [term, cf_of_gt h, abs_zero, zero_div]

theorem term_zero (N : ℕ) : term N 0 = 0 := by
  rw [term, cf_zero, abs_zero, zero_div]

/-- Every omitted summand vanishes, so the infinite score IS the finite sum. -/
theorem score_eq_sum (N : ℕ) : score N = ∑ i ∈ Finset.range N, term N (i + 1) := by
  rw [score, tsum_eq_sum (s := Finset.range (N + 1)) (fun b hb => ?_)]
  · rw [Finset.sum_range_succ', term_zero, add_zero]
  · exact term_eq_zero_of_gt (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hb)

/-- **`F(P_N) ≥ (√3/2)·H_N`** — the write-up's equation (3). -/
theorem score_lb (N : ℕ) : Real.sqrt 3 / 2 * Hsum N ≤ score N := by
  rw [score_eq_sum, Hsum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
  have := term_lb (N := N) (n := i + 1) (by omega) hi'
  calc Real.sqrt 3 / 2 * (1 / ((i : ℝ) + 1))
      = Real.sqrt 3 / 2 / (((i + 1 : ℕ) : ℝ)) := by push_cast; ring
    _ ≤ term N (i + 1) := this

/-! ### Unboundedness, and the refutation -/

theorem harm_unbounded (B : ℝ) : ∃ N : ℕ, B < Hsum N := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨N, hN⟩ := ((tendsto_atTop.1 h) (B + 1)).exists
  exact ⟨N, by have : B + 1 ≤ Hsum N := hN; linarith⟩

/-- **The identity-kernel score is unbounded above on admissible competitors.** -/
theorem score_unbounded (s : ℝ) : ∃ N : ℕ, s < score N := by
  have h3 : (0:ℝ) < Real.sqrt 3 / 2 := by
    have : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  obtain ⟨N, hN⟩ := harm_unbounded (s / (Real.sqrt 3 / 2))
  refine ⟨N, lt_of_lt_of_le ?_ (score_lb N)⟩
  rw [div_lt_iff₀ h3] at hN
  linarith [hN]

/-- Conjecture 5.93 asserts the Euler-transform candidate is **optimal**: its score is an
upper bound for every admissible competitor's score. -/
def IsOptimal (sE : ℝ) : Prop := ∀ N : ℕ, score N ≤ sE

/-- **Conjecture 5.93 is FALSE.**  No real number — in particular no *finite* score, which
is what the source's optimization requires of its candidate — bounds the scores of the
admissible normalized integer polynomials `P_N`.  So the Euler-transform candidate is not
optimal, whatever its score. -/
theorem not_conj (sE : ℝ) : ¬ IsOptimal sE := by
  intro h
  obtain ⟨N, hN⟩ := score_unbounded sE
  exact absurd (h N) (not_le.2 hN)

end Principia.MathDB.P356222
