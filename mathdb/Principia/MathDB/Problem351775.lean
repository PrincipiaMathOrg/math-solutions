import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
# MathDB #351775 — Barry's almost-Riordan row-sum formula (Conjecture 27) is TRUE

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/351775/solution.tex`, proving Conjecture 27 of Barry.

**The objects, exactly as in the source.**  The almost-Riordan array
`A = ((1 + 2z)/(1 − z²); −1/((1 − z)(1 + z)²), z/(1 + z))` has first column with generating
function `(1 + 2z)/(1 − z²)`, and column `k ≥ 1` with generating function
`z · g · f^{k−1}`, `g = −1/((1 − z)(1 + z)²)`, `f = z/(1 + z)`.  `colGF` below is that, as formal
power series over `ℚ`, and `A m k` is the coefficient of `z^m` — the array is DEFINED from the
source's generating functions, not from any closed form derived from them.  `P` is `A` with its
first row deleted, `u₀ = (1, 0, …)`, `u_{n+1} = u_n P`, and `Pₙ(x) = ∑ₖ (uₙ)ₖ xᵏ`.

**The theorem.**  `Pₙ(x) = 1 + (1 − x) ∑_{i<n} (1 − x)^{(i)}`, with `y^{(i)}` the RISING factorial
— `(ascPochhammer ℚ i).comp (1 − X)`.  (The write-up notes the MathDB transcription's falling
factorial contradicts the source's own `P₃`; the rising factorial is the source's formula.)  The
statement is an identity in `ℚ[X]`, the strongest form, not a pointwise one.

**The proof, following the write-up without its closed forms.**
1. The generating functions give four power-series identities (`col0_eq`, `col1_eq`, `colSucc_eq`
   and the order bound `colGF_order`), and taking coefficients gives short recurrences.
2. Those give the row recurrence `R_{m+2} = (X − 1) R_{m+1} + (3 − 2X)` and hence
   `R_{j+1} = 1 + (1 − X) ∑_{i ≤ j} (X − 1)^i` (`R_closed`), with no binomial sums.
3. Right multiplication by `P` therefore satisfies
   `(2 − X) · T F = (3 − 2X) F(1) + (1 − X)² F(X − 1)` — the source's operator identity with its
   denominator cleared, so no division ever appears.
4. The same identity holds for the claimed formula (`Q_succ`, via `ascPochhammer_succ_left`), and
   cancelling the nonzero factor `2 − X` closes the induction.
Every step was checked in exact arithmetic (SymPy) before this file was written.
-/

namespace Principia.MathDB.P351775

open Finset

/-- The column generating functions of Barry's almost-Riordan array. -/
noncomputable def colGF : ℕ → PowerSeries ℚ
  | 0 => (1 + 2 * PowerSeries.X) * (1 - PowerSeries.X ^ 2)⁻¹
  | k + 1 => PowerSeries.X * (-((1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2)⁻¹) *
      (PowerSeries.X * (1 + PowerSeries.X)⁻¹) ^ k

/-- The entry in row `m`, column `k`: the coefficient of `z^m` in column `k`. -/
noncomputable def A (m k : ℕ) : ℚ := PowerSeries.coeff m (colGF k)

theorem cc_d0 : PowerSeries.constantCoeff (1 - PowerSeries.X ^ 2 : PowerSeries ℚ) ≠ 0 := by
  simp

theorem cc_d1 :
    PowerSeries.constantCoeff ((1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ)
      ≠ 0 := by
  simp

theorem cc_d2 : PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
  simp

/-- Column 0: `(1 − z²) · col₀ = 1 + 2z`, written as a fixed-point equation. -/
theorem col0_eq :
    colGF 0 = 1 + PowerSeries.X + PowerSeries.X + PowerSeries.X ^ 2 * colGF 0 := by
  have h := PowerSeries.mul_inv_cancel _ cc_d0
  simp only [colGF]
  linear_combination (1 + 2 * PowerSeries.X) * h

/-- Column 1: with `H = (1 + z) · col₁`, `(1 − z²) H = −z`. -/
theorem col1_eq :
    (1 + PowerSeries.X) * colGF 1 =
      -PowerSeries.X + PowerSeries.X ^ 2 * ((1 + PowerSeries.X) * colGF 1) := by
  have h := PowerSeries.mul_inv_cancel _ cc_d1
  simp only [colGF, pow_zero, mul_one]
  linear_combination (-PowerSeries.X) * h

/-- Columns `k + 2`: `(1 + z) · col_{k+2} = z · col_{k+1}`. -/
theorem colSucc_eq (k : ℕ) :
    (1 + PowerSeries.X) * colGF (k + 2) = PowerSeries.X * colGF (k + 1) := by
  have h := PowerSeries.mul_inv_cancel _ cc_d2
  simp only [colGF]
  linear_combination
    (PowerSeries.X * (PowerSeries.X * (-((1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2)⁻¹) *
      (PowerSeries.X * (1 + PowerSeries.X)⁻¹) ^ k)) * h

/-- Column `k + 1` is divisible by `z^{k+1}`. -/
theorem colGF_order (k : ℕ) :
    colGF (k + 1) = PowerSeries.X ^ (k + 1) *
      ((-((1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2)⁻¹) * ((1 + PowerSeries.X)⁻¹) ^ k) := by
  simp only [colGF]
  ring

/-- The array is lower triangular. -/
theorem A_zero_of_lt {m k : ℕ} (h : m < k) : A m k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold A
  rw [colGF_order, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_one_add_X_mul (φ : PowerSeries ℚ) (m : ℕ) :
    PowerSeries.coeff (m + 1) ((1 + PowerSeries.X) * φ) =
      PowerSeries.coeff (m + 1) φ + PowerSeries.coeff m φ := by
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul]

theorem A00 : A 0 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0) col0_eq
  simpa [A, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] using h

theorem A10 : A 1 0 = 2 := by
  have h := congrArg (PowerSeries.coeff 1) col0_eq
  simp [PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] at h
  unfold A
  linarith

theorem A_col0_step (m : ℕ) : A (m + 2) 0 = A m 0 := by
  have h := congrArg (PowerSeries.coeff (m + 2)) col0_eq
  simpa [A, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] using h

/-- `A_{m+1,0} + A_{m,0} = 3`: column 0 alternates `1, 2, 1, 2, …`. -/
theorem A_col0_pair : ∀ m, A (m + 1) 0 + A m 0 = 3 := by
  intro m
  induction m with
  | zero => show A 1 0 + A 0 0 = 3; rw [A10, A00]; norm_num
  | succ m ih =>
    rw [show A (m + 1 + 1) 0 = A m 0 from A_col0_step m]
    linarith

/-- `H_m = A_{m,1} + A_{m−1,1}`, the coefficients of `(1 + z) · col₁`. -/
noncomputable def hc (m : ℕ) : ℚ := PowerSeries.coeff m ((1 + PowerSeries.X) * colGF 1)

theorem hc0 : hc 0 = 0 := by
  have h := congrArg (PowerSeries.coeff 0) col1_eq
  simpa [hc, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] using h

theorem hc1 : hc 1 = -1 := by
  have h := congrArg (PowerSeries.coeff 1) col1_eq
  simpa [hc, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] using h

theorem hc_step (m : ℕ) : hc (m + 2) = hc m := by
  have h := congrArg (PowerSeries.coeff (m + 2)) col1_eq
  simpa [hc, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] using h

theorem hc_succ (m : ℕ) : hc (m + 1) = A (m + 1) 1 + A m 1 := by
  unfold hc A
  exact coeff_one_add_X_mul _ m

/-- `A_{m+1,1} + A_{m,1} = A_{m,0} − 2`. -/
theorem A_col1_pair : ∀ m, A (m + 1) 1 + A m 1 = A m 0 - 2 := by
  have key : ∀ m, (hc (m + 1) = A m 0 - 2) ∧ (hc (m + 2) = A (m + 1) 0 - 2) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · show hc 1 = A 0 0 - 2
        rw [hc1, A00]; norm_num
      · show hc 2 = A 1 0 - 2
        rw [show hc 2 = hc 0 from hc_step 0, hc0, A10]; norm_num
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [hc_step, ih.1, show A (m + 1 + 1) 0 = A m 0 from A_col0_step m]
  intro m
  rw [← hc_succ]
  exact (key m).1

/-- `A_{m+1,k+2} + A_{m,k+2} = A_{m,k+1}`. -/
theorem A_colSucc (m k : ℕ) : A (m + 1) (k + 2) + A m (k + 2) = A m (k + 1) := by
  have h := congrArg (PowerSeries.coeff (m + 1)) (colSucc_eq k)
  rw [coeff_one_add_X_mul, PowerSeries.coeff_succ_X_mul] at h
  exact h

/-! ### Row polynomials of `A` -/

/-- Row `m` of `A` as a polynomial.  `A` is lower triangular, so the sum is the whole row. -/
noncomputable def R (m : ℕ) : Polynomial ℚ :=
  ∑ k ∈ range (m + 1), Polynomial.C (A m k) * Polynomial.X ^ k

/-- Summing further along the row adds only zeros. -/
theorem R_ext (m : ℕ) : ∀ N, m + 1 ≤ N →
    R m = ∑ k ∈ range N, Polynomial.C (A m k) * Polynomial.X ^ k := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ← ih, A_zero_of_lt (by omega)]
    simp

/-- **The row recurrence** `R_{m+2} = (X − 1) R_{m+1} + (3 − 2X)`. -/
theorem R_rec (m : ℕ) :
    R (m + 2) = (Polynomial.X - 1) * R (m + 1) + (3 - 2 * Polynomial.X) := by
  have e2 : R (m + 2) = ∑ j ∈ range (m + 1),
      Polynomial.C (A (m + 2) (j + 2)) * Polynomial.X ^ (j + 2) +
      Polynomial.C (A (m + 2) 1) * Polynomial.X + Polynomial.C (A (m + 2) 0) := by
    rw [R, Finset.sum_range_succ', Finset.sum_range_succ'] <;>
      simp only [pow_zero, mul_one, pow_one, zero_add, add_assoc]
  have e1 : R (m + 1) = ∑ j ∈ range (m + 1),
      Polynomial.C (A (m + 1) (j + 1)) * Polynomial.X ^ (j + 1) + Polynomial.C (A (m + 1) 0) := by
    rw [R, Finset.sum_range_succ'] <;> simp only [pow_zero, mul_one]
  have e1' : R (m + 1) = ∑ j ∈ range (m + 1),
      Polynomial.C (A (m + 1) (j + 2)) * Polynomial.X ^ (j + 2) +
      Polynomial.C (A (m + 1) 1) * Polynomial.X + Polynomial.C (A (m + 1) 0) := by
    rw [R_ext (m + 1) (m + 3) (by omega), Finset.sum_range_succ', Finset.sum_range_succ'] <;>
      simp only [pow_zero, mul_one, pow_one, zero_add, add_assoc]
  have hs : ∑ j ∈ range (m + 1), Polynomial.C (A (m + 2) (j + 2)) * Polynomial.X ^ (j + 2) =
      Polynomial.X * ∑ j ∈ range (m + 1),
        Polynomial.C (A (m + 1) (j + 1)) * Polynomial.X ^ (j + 1) -
      ∑ j ∈ range (m + 1), Polynomial.C (A (m + 1) (j + 2)) * Polynomial.X ^ (j + 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hr : A (m + 2) (j + 2) + A (m + 1) (j + 2) = A (m + 1) (j + 1) := A_colSucc (m + 1) j
    have : A (m + 2) (j + 2) = A (m + 1) (j + 1) - A (m + 1) (j + 2) := by linarith
    rw [this, map_sub]
    ring
  have h0 : Polynomial.C (A (m + 2) 0) + Polynomial.C (A (m + 1) 0) = (3 : Polynomial ℚ) := by
    have hp : A (m + 2) 0 + A (m + 1) 0 = 3 := A_col0_pair (m + 1)
    rw [← map_add, hp]
    exact Polynomial.C_ofNat 3
  have h1 : Polynomial.C (A (m + 2) 1) + Polynomial.C (A (m + 1) 1) - Polynomial.C (A (m + 1) 0)
      = (-2 : Polynomial ℚ) := by
    have hq : A (m + 2) 1 + A (m + 1) 1 = A (m + 1) 0 - 2 := A_col1_pair (m + 1)
    rw [← map_add, ← map_sub, hq, show A (m + 1) 0 - 2 - A (m + 1) 0 = -2 by ring, map_neg,
      Polynomial.C_ofNat]
  rw [e2, hs]
  linear_combination (-Polynomial.X) * e1 + e1' + h0 + Polynomial.X * h1

/-- **Rows in closed form**: `R_{m+1} = 1 + (1 − X) ∑_{i ≤ m} (X − 1)^i`. -/
theorem R_closed : ∀ m, R (m + 1) =
    1 + (1 - Polynomial.X) * ∑ i ∈ range (m + 1), (Polynomial.X - 1 : Polynomial ℚ) ^ i := by
  intro m
  induction m with
  | zero =>
    have hA11 : A 1 1 = -1 := by
      have h := hc_succ 0
      rw [hc1, A_zero_of_lt (by norm_num : (0 : ℕ) < 1), add_zero] at h
      linarith
    show R 1 = 1 + (1 - Polynomial.X) * ∑ i ∈ range 1, (Polynomial.X - 1 : Polynomial ℚ) ^ i
    rw [R, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, A10, hA11]
    simp [Polynomial.C_ofNat] <;> ring
  | succ m ih =>
    have hgeo : (Polynomial.X - 1) * ∑ i ∈ range (m + 1), (Polynomial.X - 1 : Polynomial ℚ) ^ i =
        ∑ i ∈ range (m + 1), (Polynomial.X - 1 : Polynomial ℚ) ^ i +
          (Polynomial.X - 1) ^ (m + 1) - 1 := by
      have hg := geom_sum_mul (Polynomial.X - 1 : Polynomial ℚ) (m + 1)
      linear_combination hg
    have hsplit : ∑ i ∈ range (m + 1 + 1), (Polynomial.X - 1 : Polynomial ℚ) ^ i =
        ∑ i ∈ range (m + 1), (Polynomial.X - 1 : Polynomial ℚ) ^ i +
          (Polynomial.X - 1) ^ (m + 1) := Finset.sum_range_succ _ _
    rw [show R (m + 1 + 1) = R (m + 2) from rfl, R_rec, ih]
    linear_combination (-(Polynomial.X - 1)) * hgeo - (1 - Polynomial.X) * hsplit

/-- `(2 − X) R_{j+1} = (3 − 2X) + (1 − X)² (X − 1)^j`: the source's operator on a basis vector,
with its denominator cleared. -/
theorem two_sub_mul_R (j : ℕ) :
    (2 - Polynomial.X) * R (j + 1) =
      (3 - 2 * Polynomial.X) + (1 - Polynomial.X) ^ 2 * (Polynomial.X - 1 : Polynomial ℚ) ^ j := by
  have hg := geom_sum_mul (Polynomial.X - 1 : Polynomial ℚ) (j + 1)
  rw [R_closed]
  linear_combination (-(1 - Polynomial.X)) * hg

/-! ### The produced rows -/

/-- `u₀ = (1, 0, …)` and `u_{n+1} = u_n P`, where row `j` of `P` is row `j + 1` of `A`. -/
noncomputable def u : ℕ → ℕ → ℚ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => ∑ j ∈ range (n + 1), u n j * A (j + 1) k

theorem u_zero_of_lt : ∀ n k, n < k → u n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; simp [u]; omega
  | succ n ih =>
    intro k hk
    simp only [u]
    apply Finset.sum_eq_zero
    intro j hj
    rw [A_zero_of_lt (by simp at hj; omega), mul_zero]

/-- The truncated sum in `u` is the full product `u_n P`: every omitted term has `(u_n)_j = 0`. -/
theorem u_succ_full (n k : ℕ) : ∀ N, n + 1 ≤ N →
    u (n + 1) k = ∑ j ∈ range N, u n j * A (j + 1) k := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ← ih, u_zero_of_lt n N (by omega), zero_mul, add_zero]

/-- `Pₙ(x) = ∑ₖ (uₙ)ₖ xᵏ`. -/
noncomputable def Pn (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ range (n + 1), Polynomial.C (u n k) * Polynomial.X ^ k

theorem Pn_succ (n : ℕ) :
    Pn (n + 1) = ∑ j ∈ range (n + 1), Polynomial.C (u n j) * R (j + 1) := by
  simp only [Pn, u, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [R_ext (j + 1) (n + 1 + 1) (by simp at hj; omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem Pn_eval_one (n : ℕ) : (Pn n).eval 1 = ∑ j ∈ range (n + 1), u n j := by
  rw [← Polynomial.coe_evalRingHom, Pn, map_sum]
  simp

theorem Pn_comp (n : ℕ) :
    (Pn n).comp (Polynomial.X - 1) =
      ∑ j ∈ range (n + 1), Polynomial.C (u n j) * (Polynomial.X - 1 : Polynomial ℚ) ^ j := by
  rw [Polynomial.comp_eq_aeval, Pn, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- **The operator identity** for the produced rows. -/
theorem Pn_step (n : ℕ) :
    (2 - Polynomial.X) * Pn (n + 1) =
      (3 - 2 * Polynomial.X) * Polynomial.C ((Pn n).eval 1) +
        (1 - Polynomial.X) ^ 2 * (Pn n).comp (Polynomial.X - 1) := by
  rw [Pn_succ, Pn_eval_one, Pn_comp, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj := two_sub_mul_R j
  linear_combination Polynomial.C (u n j) * hj

/-! ### The claimed formula satisfies the same identity -/

/-- The right side of Barry's formula: `1 + (1 − x) ∑_{i<n} (1 − x)^{(i)}`, rising factorial. -/
noncomputable def Q (n : ℕ) : Polynomial ℚ :=
  1 + (1 - Polynomial.X) *
    ∑ i ∈ range n, (ascPochhammer ℚ i).comp (1 - Polynomial.X)

theorem asc_shift (i : ℕ) :
    (ascPochhammer ℚ (i + 1)).comp (1 - Polynomial.X) =
      (1 - Polynomial.X) * (ascPochhammer ℚ i).comp (2 - Polynomial.X) := by
  rw [ascPochhammer_succ_left, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.comp_assoc]
  congr 2
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp]
  ring

theorem Q_eval_one (n : ℕ) : (Q n).eval 1 = 1 := by
  simp [Q]

theorem Q_comp (n : ℕ) :
    (Q n).comp (Polynomial.X - 1) =
      1 + (2 - Polynomial.X) * ∑ i ∈ range n, (ascPochhammer ℚ i).comp (2 - Polynomial.X) := by
  have hs : (∑ i ∈ range n, (ascPochhammer ℚ i).comp (1 - Polynomial.X)).comp
      (Polynomial.X - 1) = ∑ i ∈ range n, (ascPochhammer ℚ i).comp (2 - Polynomial.X) := by
    rw [Polynomial.comp_eq_aeval, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Polynomial.comp_eq_aeval, Polynomial.comp_assoc]
    congr 1
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
    ring
  rw [Q, Polynomial.add_comp, Polynomial.mul_comp, hs]
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
  ring

theorem Q_step (n : ℕ) :
    (2 - Polynomial.X) * Q (n + 1) =
      (3 - 2 * Polynomial.X) * Polynomial.C ((Q n).eval 1) +
        (1 - Polynomial.X) ^ 2 * (Q n).comp (Polynomial.X - 1) := by
  rw [Q_eval_one, Q_comp, Q, Finset.sum_range_succ']
  simp only [asc_shift, ascPochhammer_zero, Polynomial.one_comp, map_one, mul_one]
  rw [← Finset.mul_sum]
  ring

/-- **MathDB #351775: Barry's Conjecture 27.**  For every `n`,
`Pₙ(x) = 1 + (1 − x) ∑_{i<n} (1 − x)^{(i)}`, as polynomials over `ℚ`. -/
theorem barry_row_sum : ∀ n, Pn n = Q n := by
  intro n
  induction n with
  | zero => simp [Pn, Q, u]
  | succ n ih =>
    have h2 : (2 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
      intro h
      have := congrArg (Polynomial.eval 0) h
      norm_num at this
    apply mul_left_cancel₀ h2
    rw [Pn_step, Q_step, ih]

end Principia.MathDB.P351775
