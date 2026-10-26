import Mathlib

set_option autoImplicit false

/-!
# MathDB #356321 — positive Bernstein coefficients of Bernoulli densities

Write-up `mathdb-open-problems/problems/356321/solution.tex`,
*Positive Bernstein coefficients of Bernoulli densities*, 21 September 2026.

With `b_n(x) = B_n(x)/n!` (Bernoulli polynomials, `B_1 = -1/2`) and the Bernstein basis
`B_{r,n}(x) = C(n,r) x^r (1-x)^(n-r)`, write the unique expansion

    1 - 2^n b_n(x) = ∑_{r=0}^n c_{n,r} B_{r,n}(x).                             (1)

El Maazouz–Pitman Conjecture 3.7 proposes that the `c_{n,r}` are positive.  The write-up
proves it for every `n ≥ 2`, with `(c_{1,0}, c_{1,1}) = (2,0)` as the boundary case, via the
uniform bound `|c_{n,r} - 1| ≤ 4 e^(2π) π^(-n)`.

## Why this row is here at all

It was previously skipped because the write-up disclaims its own campaign credit.  That is a
statement about novelty adjudication, not about mathematics, and this campaign verifies
rather than adjudicates — see the retraction recorded in the campaign README.  Re-triaged on
mathematics, the row has **no Mathlib gap**: `Polynomial.bernoulli`, `bernsteinPolynomial`
and — the one real input — `hasSum_zeta_nat` all exist.

## Status: VERIFIED — nothing is assumed

`bernstein_positive` proves Conjecture 3.7 outright: `1 - 2ⁿ bₙ` has the Bernstein expansion
with coefficients `cCoef n r`, and every one of them is strictly positive for `n ≥ 2`.  The
`n = 1` boundary case is recorded separately in `cCoef_one` — `(c₁₀, c₁₁) = (2, 0)`, so the
literal "strictly positive for every positive `n`" reading fails there while the
nonnegativity reading holds everywhere.  That is exactly the write-up's theorem.

Four pieces, in the order they were built:

* `bernoulli_abs_bound` — the ONLY analysis in the argument: `|B_m| (2π)^m / m! ≤ 4`.  For
  even `m = 2j` the quantity IS `2 ζ(2j)`, by Mathlib's `hasSum_zeta_nat`, and
  `ζ(2j) ≤ ζ(2) = π²/6` termwise gives `≤ π²/3 < 4`.
* `large_pos` — positivity for `n ≥ 9`.  `term_bound` turns the Bernoulli bound into
  `|a_(n,j)| ≤ 4(2π)ʲ/(πⁿ j!)`, `cCoef_sub_one_bound` sums it against
  `Real.sum_le_exp_of_nonneg`, and `4e^(2π) < 4·3⁷ < 3⁹ ≤ πⁿ`.  **No interchange of limits
  anywhere**: the sums are finite and the majorant is the exponential series.
* `expansion` — equation (1) itself, so `cCoef` are demonstrably THE Bernstein
  coefficients rather than a formula asserted to be them.  Its engine is
  `bernstein_moment`, the write-up's equation (4) in cleared form
  `∑_r C(r,j) B_(r,n) = C(n,j) Xʲ`, proved from `Nat.choose_mul` and the binomial theorem.
* `small_pos` — the finite table `n = 2..8`.  Mathlib stops at `bernoulli'_four`, and
  `simp [bernoulli, bernoulli'_def]` loops, so `B₆ = 1/42` and `B₈ = -1/30` are built one
  index at a time; the 42 coefficients are then exact rationals.

## Why this row was nearly missed

It had been skipped because the write-up disclaims its own campaign credit — a statement
about novelty adjudication, not about mathematics.  That heuristic was retracted (see the
campaign README) after it emerged that #375794, already verified, carries the same
disclaimer and the same `full-proof-eligibility-pending` upstream state.  Re-triaged on
mathematics, this row had no Mathlib gap at all.

## Checked in SymPy before formalizing

`Campaigns/MathDB-Formalization/verify_356321.py`: formula (5) agrees with the actual
Bernstein expansion for `n = 1..14`; the expansion reproduces `1 - 2^n b_n(x)` for
`n = 1..10`; the write-up's entire `n = 1..8` table (`D_n` and every numerator) is exact;
positivity holds for `2 ≤ n ≤ 59`; `(c_{1,0}, c_{1,1}) = (2,0)`; and the uniform bound holds
for `n = 1..39`, first dropping below `1` at `n = 7`.
-/

namespace Principia.MathDB.P356321

open Polynomial Finset

/-! ### The analytic input

`|B_m| (2π)^m / m! ≤ 4`.  For even `m = 2j` this quantity is exactly `2 ζ(2j)`, by the
classical Bernoulli–zeta relation that Mathlib carries as `hasSum_zeta_nat`; bounding
`ζ(2j) ≤ ζ(2) = π²/6` termwise gives `≤ π²/3 < 4`.  Odd `m > 1` contribute `0`, and `m = 0`,
`m = 1` are `1` and `π`. -/

/-- `ζ(2j) ≤ ζ(2)`, by termwise comparison. -/
theorem zeta_even_le (j : ℕ) (hj : j ≠ 0) :
    ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (2 * j) ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
  refine Summable.tsum_le_tsum (fun n => ?_) (hasSum_zeta_nat hj).summable
    hasSum_zeta_two.summable
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (2 * j) ≠ 0 := by omega
    simp [zero_pow h1]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 (by omega))

/-- The even case: the quantity is exactly `2 ζ(2j)`. -/
theorem bernoulli_even_bound (j : ℕ) (hj : j ≠ 0) :
    |((_root_.bernoulli (2 * j) : ℚ) : ℝ)| * (2 * Real.pi) ^ (2 * j)
      / (((2 * j).factorial : ℕ) : ℝ) ≤ 4 := by
  have hz := hasSum_zeta_nat hj
  have hle := zeta_even_le j hj
  rw [hz.tsum_eq, hasSum_zeta_two.tsum_eq] at hle
  have hfac : (0 : ℝ) < (((2 * j).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * j)
  have hVnn : (0 : ℝ) ≤ (-1) ^ (j + 1) * 2 ^ (2 * j - 1) * Real.pi ^ (2 * j)
      * ((_root_.bernoulli (2 * j) : ℚ) : ℝ) / (((2 * j).factorial : ℕ) : ℝ) := by
    rw [← hz.tsum_eq]
    exact tsum_nonneg (fun n => by positivity)
  set W : ℝ := (-1) ^ (j + 1) * ((_root_.bernoulli (2 * j) : ℚ) : ℝ) with hW
  have hrw : (-1 : ℝ) ^ (j + 1) * 2 ^ (2 * j - 1) * Real.pi ^ (2 * j)
      * ((_root_.bernoulli (2 * j) : ℚ) : ℝ) / (((2 * j).factorial : ℕ) : ℝ)
      = 2 ^ (2 * j - 1) * Real.pi ^ (2 * j) * W / (((2 * j).factorial : ℕ) : ℝ) := by
    rw [hW]; ring
  rw [hrw] at hVnn hle
  have hWnn : 0 ≤ W := by
    by_contra hneg
    push_neg at hneg
    have hp : (0 : ℝ) < 2 ^ (2 * j - 1) * Real.pi ^ (2 * j) := by positivity
    have : 2 ^ (2 * j - 1) * Real.pi ^ (2 * j) * W / (((2 * j).factorial : ℕ) : ℝ) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) hfac
    linarith
  have habs : |((_root_.bernoulli (2 * j) : ℚ) : ℝ)| = W := by
    have h1 : |W| = |((_root_.bernoulli (2 * j) : ℚ) : ℝ)| := by
      rw [hW, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← h1, abs_of_nonneg hWnn]
  rw [habs]
  have hpow : (2 : ℝ) * 2 ^ (2 * j - 1) = 2 ^ (2 * j) := by
    rw [← pow_succ']; congr 1; omega
  have hsplit : W * (2 * Real.pi) ^ (2 * j) / (((2 * j).factorial : ℕ) : ℝ)
      = 2 * (2 ^ (2 * j - 1) * Real.pi ^ (2 * j) * W / (((2 * j).factorial : ℕ) : ℝ)) := by
    rw [mul_pow, ← hpow]; ring
  rw [hsplit]
  nlinarith [hle, Real.pi_lt_d2, Real.pi_gt_three]

/-- **The analytic input, for every `m`.** -/
theorem bernoulli_abs_bound (m : ℕ) :
    |((_root_.bernoulli m : ℚ) : ℝ)| * (2 * Real.pi) ^ m / ((m.factorial : ℕ) : ℝ) ≤ 4 := by
  match m with
  | 0 => norm_num
  | 1 =>
    rw [_root_.bernoulli_one]
    norm_num
    nlinarith [Real.pi_lt_four, Real.pi_gt_three]
  | (k + 2) =>
    rcases Nat.even_or_odd (k + 2) with ⟨j, hj⟩ | ho
    · have h2 : k + 2 = 2 * j := by omega
      rw [h2]
      exact bernoulli_even_bound j (by omega)
    · rw [_root_.bernoulli_eq_zero_of_odd ho (by omega)]
      norm_num

/-! ### The objects of Conjecture 3.7 -/

/-- The write-up's formula (5): `c_{n,r} = 1 - (2^n/n!) ∑_{j≤r} C(r,j) B_{n-j}`. -/
noncomputable def cCoef (n r : ℕ) : ℚ :=
  1 - (2 ^ n / (n.factorial : ℚ))
        * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℚ) * _root_.bernoulli (n - j)

/-- Equation (1): the `cCoef` really are the Bernstein coefficients of `1 - 2^n b_n`. -/
def IsExpansion (n : ℕ) : Prop :=
  (1 : ℚ[X]) - C ((2 : ℚ) ^ n / (n.factorial : ℚ)) * Polynomial.bernoulli n
    = ∑ r ∈ Finset.range (n + 1), C (cCoef n r) * bernsteinPolynomial ℚ n r

/-! ### From the bound to positivity in large degree

Formula (5) already expresses `c_{n,r} - 1` through Bernoulli numbers, so no expansion
identity is needed here: `(2^n/n!) C(r,j) = a_{n,j} · C(r,j)/C(n,j)` and `C(r,j) ≤ C(n,j)`
for `r ≤ n`, which is the whole content of "the conversion ratios lie in `[0,1]`". -/

/-- `|a_{n,j}| ≤ 4 (2π)^j / (π^n j!)`, written with `n = j + m` so no ℕ-subtraction appears. -/
theorem term_bound (j m : ℕ) :
    (2 : ℝ) ^ (j + m) / (((j + m).factorial : ℕ) : ℝ) * (((j + m).choose j : ℕ) : ℝ)
        * |((_root_.bernoulli m : ℚ) : ℝ)|
      ≤ 4 * (2 * Real.pi) ^ j / (Real.pi ^ (j + m) * ((j.factorial : ℕ) : ℝ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfj : (0 : ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfm : (0 : ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfjm : (0 : ℝ) < (((j + m).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + m)
  have hC : (0 : ℝ) ≤ (((j + m).choose j : ℕ) : ℝ) := by positivity
  have hb : |((_root_.bernoulli m : ℚ) : ℝ)| * (2 * Real.pi) ^ m
      ≤ 4 * ((m.factorial : ℕ) : ℝ) := by
    have h := bernoulli_abs_bound m
    rw [div_le_iff₀ hfm] at h
    linarith
  have hch : (((j + m).choose j : ℕ) : ℝ) * ((j.factorial : ℕ) : ℝ)
      * ((m.factorial : ℕ) : ℝ) = (((j + m).factorial : ℕ) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j m)
    simp only [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have key : (2 : ℝ) ^ (j + m) * |((_root_.bernoulli m : ℚ) : ℝ)| * Real.pi ^ (j + m)
      ≤ 4 * 2 ^ j * Real.pi ^ j * ((m.factorial : ℕ) : ℝ) := by
    calc (2 : ℝ) ^ (j + m) * |((_root_.bernoulli m : ℚ) : ℝ)| * Real.pi ^ (j + m)
        = (2 ^ j * Real.pi ^ j) * (|((_root_.bernoulli m : ℚ) : ℝ)| * (2 * Real.pi) ^ m) := by
          rw [pow_add, pow_add, mul_pow]; ring
      _ ≤ (2 ^ j * Real.pi ^ j) * (4 * ((m.factorial : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 4 * 2 ^ j * Real.pi ^ j * ((m.factorial : ℕ) : ℝ) := by ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hfjm (by positivity)]
  have hmul := mul_le_mul_of_nonneg_left key
    (mul_nonneg hC hfj.le : (0 : ℝ) ≤ (((j + m).choose j : ℕ) : ℝ) * ((j.factorial : ℕ) : ℝ))
  calc (2 : ℝ) ^ (j + m) * (((j + m).choose j : ℕ) : ℝ)
          * |((_root_.bernoulli m : ℚ) : ℝ)| * (Real.pi ^ (j + m) * ((j.factorial : ℕ) : ℝ))
      = (((j + m).choose j : ℕ) : ℝ) * ((j.factorial : ℕ) : ℝ)
          * ((2 : ℝ) ^ (j + m) * |((_root_.bernoulli m : ℚ) : ℝ)| * Real.pi ^ (j + m)) := by
        ring
    _ ≤ (((j + m).choose j : ℕ) : ℝ) * ((j.factorial : ℕ) : ℝ)
          * (4 * 2 ^ j * Real.pi ^ j * ((m.factorial : ℕ) : ℝ)) := hmul
    _ = 4 * (2 * Real.pi) ^ j * ((((j + m).choose j : ℕ) : ℝ) * ((j.factorial : ℕ) : ℝ)
          * ((m.factorial : ℕ) : ℝ)) := by rw [mul_pow]; ring
    _ = 4 * (2 * Real.pi) ^ j * (((j + m).factorial : ℕ) : ℝ) := by rw [hch]

/-- `|c_{n,r} - 1| ≤ 4 e^(2π) / π^n` — the write-up's bound (2). -/
theorem cCoef_sub_one_bound (n r : ℕ) (hr : r ≤ n) :
    |((cCoef n r : ℚ) : ℝ) - 1| ≤ 4 * Real.exp (2 * Real.pi) / Real.pi ^ n := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfn : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hscal : (0 : ℝ) ≤ (2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ) := by positivity
  have hcast : ((cCoef n r : ℚ) : ℝ) - 1
      = -((2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ)
          * ∑ j ∈ Finset.range (r + 1),
              ((r.choose j : ℕ) : ℝ) * ((_root_.bernoulli (n - j) : ℚ) : ℝ)) := by
    simp only [cCoef]
    push_cast
    ring
  rw [hcast, abs_neg, abs_mul, abs_of_nonneg hscal]
  have h1 : |∑ j ∈ Finset.range (r + 1),
              ((r.choose j : ℕ) : ℝ) * ((_root_.bernoulli (n - j) : ℚ) : ℝ)|
      ≤ ∑ j ∈ Finset.range (r + 1),
          ((r.choose j : ℕ) : ℝ) * |((_root_.bernoulli (n - j) : ℚ) : ℝ)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl (fun j _ => ?_))
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((r.choose j : ℕ) : ℝ))]
  calc (2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ)
        * |∑ j ∈ Finset.range (r + 1),
            ((r.choose j : ℕ) : ℝ) * ((_root_.bernoulli (n - j) : ℚ) : ℝ)|
      ≤ (2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ)
          * ∑ j ∈ Finset.range (r + 1),
              ((r.choose j : ℕ) : ℝ) * |((_root_.bernoulli (n - j) : ℚ) : ℝ)| :=
        mul_le_mul_of_nonneg_left h1 hscal
    _ = ∑ j ∈ Finset.range (r + 1), ((2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ)
          * ((r.choose j : ℕ) : ℝ) * |((_root_.bernoulli (n - j) : ℚ) : ℝ)|) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j ∈ Finset.range (r + 1),
          4 * (2 * Real.pi) ^ j / (Real.pi ^ n * ((j.factorial : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hjr : j ≤ r := by
          have := Finset.mem_range.mp hj; omega
        have hcc : ((r.choose j : ℕ) : ℝ) ≤ ((n.choose j : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_le_choose j hr
        have hstep : (2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ) * ((r.choose j : ℕ) : ℝ)
              * |((_root_.bernoulli (n - j) : ℚ) : ℝ)|
            ≤ (2 : ℝ) ^ n / ((n.factorial : ℕ) : ℝ) * ((n.choose j : ℕ) : ℝ)
              * |((_root_.bernoulli (n - j) : ℚ) : ℝ)| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcc hscal) (abs_nonneg _)
        refine hstep.trans ?_
        have ht := term_bound j (n - j)
        rw [show j + (n - j) = n from by omega] at ht
        exact ht
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          4 * (2 * Real.pi) ^ j / (Real.pi ^ n * ((j.factorial : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (by
            have := Finset.mem_range.mp hx; omega))
          (fun j _ _ => by positivity)
    _ = 4 / Real.pi ^ n * ∑ j ∈ Finset.range (n + 1),
          (2 * Real.pi) ^ j / ((j.factorial : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 4 / Real.pi ^ n * Real.exp (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left
          (Real.sum_le_exp_of_nonneg (by positivity) (n + 1)) (by positivity)
    _ = 4 * Real.exp (2 * Real.pi) / Real.pi ^ n := by ring

/-- **Positivity in large degree**, from the analytic input. -/
theorem large_pos (n r : ℕ) (hn : 9 ≤ n) (hr : r ≤ n) : 0 < cCoef n r := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hb := cCoef_sub_one_bound n r hr
  have hexp : Real.exp (2 * Real.pi) < 2187 := by
    have h1 : Real.exp (2 * Real.pi) ≤ Real.exp 7 :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_lt_d2])
    have h2 : Real.exp 7 = (Real.exp 1) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    have h3 : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
    have h4 : (Real.exp 1) ^ 7 < 3 ^ 7 :=
      pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (by norm_num)
    rw [h2] at h1
    norm_num at h4
    linarith
  have hpn : (19683 : ℝ) < Real.pi ^ n := by
    have h9 : (3 : ℝ) ^ 9 < Real.pi ^ 9 :=
      pow_lt_pow_left₀ Real.pi_gt_three (by norm_num) (by norm_num)
    have hmono : Real.pi ^ 9 ≤ Real.pi ^ n :=
      pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hn
    norm_num at h9
    linarith
  have hlt : 4 * Real.exp (2 * Real.pi) / Real.pi ^ n < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have habs : |((cCoef n r : ℚ) : ℝ) - 1| < 1 := lt_of_le_of_lt hb hlt
  have h2 : (0 : ℝ) < ((cCoef n r : ℚ) : ℝ) := by
    rcases abs_lt.mp habs with ⟨hl, _⟩
    linarith
  exact_mod_cast h2

/-! ### The monomial-to-Bernstein conversion, and the expansion identity

The write-up's equation (4), `x^j = ∑_r [C(r,j)/C(n,j)] B_{r,n}(x)`, in the cleared form
`∑_r C(r,j) B_{r,n} = C(n,j) X^j`.  The proof is the subset-of-a-subset identity
`C(n,r) C(r,j) = C(n,j) C(n-j, r-j)` (`Nat.choose_mul`) followed by the binomial theorem on
`(X + (1-X))^(n-j) = 1`. -/

theorem bernstein_moment (n j : ℕ) (hj : j ≤ n) :
    ∑ r ∈ Finset.range (n + 1), (((r.choose j : ℕ) : ℚ[X])) * bernsteinPolynomial ℚ n r
      = ((n.choose j : ℕ) : ℚ[X]) * X ^ j := by
  have hsub : Finset.Ico j (n + 1) ⊆ Finset.range (n + 1) :=
    fun x hx => Finset.mem_range.mpr (by
      have := Finset.mem_Ico.mp hx; omega)
  have hzero : ∀ r ∈ Finset.range (n + 1), r ∉ Finset.Ico j (n + 1) →
      (((r.choose j : ℕ) : ℚ[X])) * bernsteinPolynomial ℚ n r = 0 := by
    intro r hr hnot
    have hrn : r < n + 1 := Finset.mem_range.mp hr
    have hlt : r < j := by
      by_contra hge
      exact hnot (Finset.mem_Ico.mpr ⟨by omega, hrn⟩)
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range,
    show n + 1 - j = (n - j) + 1 from by omega]
  have hterm : ∀ k ∈ Finset.range ((n - j) + 1),
      (((j + k).choose j : ℕ) : ℚ[X]) * bernsteinPolynomial ℚ n (j + k)
        = ((n.choose j : ℕ) : ℚ[X]) * X ^ j
            * ((((n - j).choose k : ℕ) : ℚ[X]) * X ^ k * (1 - X) ^ ((n - j) - k)) := by
    intro k hk
    have hk' : k ≤ n - j := by
      have := Finset.mem_range.mp hk; omega
    have hmul : n.choose (j + k) * (j + k).choose j
        = n.choose j * (n - j).choose k := by
      have h := Nat.choose_mul (n := n) (k := j + k) (s := j) (Nat.le_add_right j k)
      simpa using h
    have hcast : ((n.choose (j + k) : ℕ) : ℚ[X]) * (((j + k).choose j : ℕ) : ℚ[X])
        = ((n.choose j : ℕ) : ℚ[X]) * (((n - j).choose k : ℕ) : ℚ[X]) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hmul]
    simp only [bernsteinPolynomial, show n - (j + k) = (n - j) - k from by omega]
    rw [pow_add]
    linear_combination (X ^ j * X ^ k * (1 - X) ^ ((n - j) - k)) * hcast
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbin : ∑ k ∈ Finset.range ((n - j) + 1),
      (((n - j).choose k : ℕ) : ℚ[X]) * X ^ k * (1 - X) ^ ((n - j) - k) = 1 := by
    have h := add_pow (X : ℚ[X]) (1 - X) (n - j)
    rw [show (X : ℚ[X]) + (1 - X) = 1 from by ring, one_pow] at h
    calc ∑ k ∈ Finset.range ((n - j) + 1),
        (((n - j).choose k : ℕ) : ℚ[X]) * X ^ k * (1 - X) ^ ((n - j) - k)
        = ∑ k ∈ Finset.range ((n - j) + 1),
            X ^ k * (1 - X) ^ ((n - j) - k) * (((n - j).choose k : ℕ) : ℚ[X]) :=
          Finset.sum_congr rfl (fun k _ => by ring)
      _ = 1 := h.symm
  rw [hbin, mul_one]

/-- **Equation (1) itself**: the `cCoef` really are the Bernstein coefficients of
`1 - 2ⁿ bₙ`.  This is what licenses calling formula (5) "the" coefficients. -/
theorem expansion (n : ℕ) : IsExpansion n := by
  rw [IsExpansion]
  have hext : ∀ r ∈ Finset.range (n + 1),
      C (cCoef n r) * bernsteinPolynomial ℚ n r
        = bernsteinPolynomial ℚ n r
          - C ((2 : ℚ) ^ n / (n.factorial : ℚ))
            * ∑ j ∈ Finset.range (n + 1),
                ((r.choose j : ℕ) : ℚ[X]) * C (_root_.bernoulli (n - j))
                  * bernsteinPolynomial ℚ n r := by
    intro r hr
    have hrn : r < n + 1 := Finset.mem_range.mp hr
    have hs : ∑ j ∈ Finset.range (r + 1),
          ((r.choose j : ℕ) : ℚ[X]) * C (_root_.bernoulli (n - j))
        = ∑ j ∈ Finset.range (n + 1),
          ((r.choose j : ℕ) : ℚ[X]) * C (_root_.bernoulli (n - j)) := by
      refine Finset.sum_subset ?_ (fun j _ hj => ?_)
      · exact fun x hx => Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hx; omega)
      · have hrj : r < j := by
          simp only [Finset.mem_range, not_lt] at hj
          omega
        rw [Nat.choose_eq_zero_of_lt hrj]
        simp
    have hc : C (cCoef n r) = 1 - C ((2 : ℚ) ^ n / (n.factorial : ℚ))
        * ∑ j ∈ Finset.range (n + 1),
            ((r.choose j : ℕ) : ℚ[X]) * C (_root_.bernoulli (n - j)) := by
      rw [cCoef, map_sub, map_one, map_mul, map_sum, ← hs]
      refine congrArg (fun z => 1 - C ((2 : ℚ) ^ n / (n.factorial : ℚ)) * z) ?_
      exact Finset.sum_congr rfl (fun j _ => by rw [map_mul]; simp)
    rw [hc, sub_mul, one_mul, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl hext, Finset.sum_sub_distrib, bernsteinPolynomial.sum]
  refine congrArg (fun z => (1 : ℚ[X]) - z) ?_
  rw [← Finset.mul_sum]
  refine congrArg (fun z => C ((2 : ℚ) ^ n / (n.factorial : ℚ)) * z) ?_
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range (n + 1),
      ∑ r ∈ Finset.range (n + 1),
          ((r.choose j : ℕ) : ℚ[X]) * C (_root_.bernoulli (n - j))
            * bernsteinPolynomial ℚ n r
        = C (_root_.bernoulli (n - j)) * (((n.choose j : ℕ) : ℚ[X]) * X ^ j) := by
    intro j hj
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj; omega
    calc ∑ r ∈ Finset.range (n + 1),
          ((r.choose j : ℕ) : ℚ[X]) * C (_root_.bernoulli (n - j))
            * bernsteinPolynomial ℚ n r
        = C (_root_.bernoulli (n - j)) * ∑ r ∈ Finset.range (n + 1),
            ((r.choose j : ℕ) : ℚ[X]) * bernsteinPolynomial ℚ n r := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = C (_root_.bernoulli (n - j)) * (((n.choose j : ℕ) : ℚ[X]) * X ^ j) := by
          rw [bernstein_moment n j hjn]
  rw [Finset.sum_congr rfl hinner, Polynomial.bernoulli_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  simp
  ring

/-! ### The finite table `n = 2..8`

Mathlib stops at `bernoulli'_four`, and `simp [bernoulli, bernoulli'_def]` loops (the
defining equation rewrites `bernoulli' n` into earlier `bernoulli' k`), so `B₆` and `B₈` are
built one index at a time from `bernoulli'_def`.  With `B₀…B₈` in hand each of the 42
coefficients is an exact rational and `norm_num` decides its sign. -/

theorem b'5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem b'6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, b'5, Nat.choose]

theorem b'7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem b'8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, b'5, b'6, b'7, Nat.choose]

theorem B0 : _root_.bernoulli 0 = 1 := _root_.bernoulli_zero
theorem B1 : _root_.bernoulli 1 = -1 / 2 := _root_.bernoulli_one
theorem B2 : _root_.bernoulli 2 = 1 / 6 := by rw [_root_.bernoulli_two]; norm_num
theorem B3 : _root_.bernoulli 3 = 0 :=
  _root_.bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem B4 : _root_.bernoulli 4 = -1 / 30 := by
  rw [_root_.bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
theorem B5 : _root_.bernoulli 5 = 0 :=
  _root_.bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem B6 : _root_.bernoulli 6 = 1 / 42 := by
  rw [_root_.bernoulli_eq_bernoulli'_of_ne_one (by norm_num), b'6]
theorem B7 : _root_.bernoulli 7 = 0 :=
  _root_.bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem B8 : _root_.bernoulli 8 = -1 / 30 := by
  rw [_root_.bernoulli_eq_bernoulli'_of_ne_one (by norm_num), b'8]

/-- **The write-up's finite table**: every coefficient is positive for `2 ≤ n ≤ 8`. -/
theorem small_pos (n r : ℕ) (h2 : 2 ≤ n) (h8 : n ≤ 8) (hr : r ≤ n) : 0 < cCoef n r := by
  interval_cases n <;> interval_cases r <;>
    norm_num [cCoef, Finset.sum_range_succ, B0, B1, B2, B3, B4, B5, B6, B7, B8,
      Nat.factorial, Nat.choose]

/-! ### El Maazouz–Pitman Conjecture 3.7

Nothing is assumed: the expansion identity, the large-degree bound and the finite table are
all theorems above. -/

/-- **MathDB #356321 — Conjecture 3.7 is TRUE.**  `1 - 2ⁿ bₙ` has the Bernstein expansion
with coefficients `cCoef n r`, and every one of them is strictly positive for `n ≥ 2`.

The `n = 1` boundary case is genuine and is recorded separately in `cCoef_one`:
`(c₁₀, c₁₁) = (2, 0)`, so the literal "strictly positive for every positive `n`" reading of
the conjecture fails at `n = 1` while the nonnegativity reading holds everywhere. -/
theorem bernstein_positive :
    (∀ n : ℕ, (1 : ℚ[X]) - C ((2 : ℚ) ^ n / (n.factorial : ℚ)) * Polynomial.bernoulli n
        = ∑ r ∈ Finset.range (n + 1), C (cCoef n r) * bernsteinPolynomial ℚ n r) ∧
      (∀ n r : ℕ, 2 ≤ n → r ≤ n → 0 < cCoef n r) := by
  refine ⟨expansion, fun n r hn hr => ?_⟩
  rcases Nat.lt_or_ge n 9 with h | h
  · exact small_pos n r hn (by omega) hr
  · exact large_pos n r h hr

/-- The `n = 1` boundary case the write-up flags: `c₁₁ = 0`, so strict positivity fails. -/
theorem cCoef_one : cCoef 1 0 = 2 ∧ cCoef 1 1 = 0 := by
  constructor <;> norm_num [cCoef, Finset.sum_range_succ, B0, B1, Nat.factorial, Nat.choose]

end Principia.MathDB.P356321
