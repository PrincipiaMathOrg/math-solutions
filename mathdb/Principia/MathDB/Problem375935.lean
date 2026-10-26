import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 375935 — an obstruction to the binary Hankel product formula

Write-up: `mathdb-open-problems/problems/375935/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It **disproves Conjecture 4.6** of
Sobolewski–Ulas.  With `s(a)` the binary digit sum, `H(n) = det[s(i+j)]_{0≤i,j<n}`,
`B_m = ∏_{j=1}^m (2ʲ-1)^{2^{m-j}}` and `T_m = ∑_{j=1}^m 2^{j-1}/(2ʲ-1)`, the conjecture
asserts that for each fixed `k` there are `r ≥ 0`, a sign `ε`, a polynomial `P` and a
constant `c` with, eventually,

  `H(2^m + k) = ε P(2^m) (c + T_{m-r}) B_{m-r}`.   (1)

The write-up's own new result is the **exact evaluation at offset 2**:

  `H(2^m+2) = B_m(2 + T_{m-1})/((2^{m-1}-1)(2^m-1)) = (B_m/A(X))(T_m + d(X))`,  (2)

with `X = 2^m`, `A(X) = (X/2-1)(X-1)` and `d(X) = 3/2 - 1/(2(X-1))`.

## Indexing

`T` and `B` are defined by **recursion**, which removes every `ℕ`-subtraction:
`T 0 = 0`, `T (m+1) = T m + 2^m/(2^{m+1}-1)`, and `B 0 = 1`,
`B (m+1) = (B m)²(2^{m+1}-1)`.  The source's `U_m`, `V_m` start at `m = 2`, so they are
carried shifted: `Y k = U_{k+2}`, `W k = V_{k+2}`.

## What is proved

* `T_succ_sub`, `T_eq_half_add` — `T_{m+1} - T_m = 2^m/(2^{m+1}-1)`, and the `d` in (2)
  is exactly `2 + T_{m-1} - T_m` rearranged.
* **`ratio_eq`** — the write-up's identity (4), by induction on the carried recurrence:
  `Y k x = W k x · (1 + ∑_{j≤k} 1/(2 - x/2ʲ))`.  Dividing the two branches of the
  recurrence makes the `C_m` prefactor cancel, so the induction is one line of algebra
  plus `Finset.sum_range_succ'` to absorb the new term at `j = 0`.
* `inv_two_sub_eq` — at `x = 1` the summand is `2ʲ/(2^{j+1}-1)`, so the sum is `T (k+1)`;
  hence `Y k 1 = W k 1 · (1 + T (k+1))` (`ratio_at_one`).
* `Setup.evaluation` — combining with the carried (5) and the source's final branch,
  `H(2^m+2) = B_m(2 + T_{m-1})/((2^{m-1}-1)(2^m-1))`.
* **`Setup.no_constant`** — the obstruction's elementary branch: `d(2^m)` is strictly
  increasing, so `c = d(2^m)` cannot hold for two different `m`, let alone eventually.

## What is carried

The source's determinant recurrence (its Theorem 4.2 / Proposition 4.3) in the shifted
form `hW`, `hY`, together with `W k x ≠ 0`; the evaluation `V_m(1)` of (5); the final
branch `H(2^m+2) = U_m(1) + V_m(1)`; and the asymptotic half of the obstruction
(`log B_m/2^m → λ` forcing `r = 0`, and the rational-function dichotomy that kills
`R ≢ 1`).

`Campaigns/MathDB-Formalization/verify_375935.py` checks every identity in exact
rationals and **cross-checks the whole carried chain against a convention-free
quantity**: `U_m(1) + V_m(1)` equals `H(2^m+2)` computed directly from the matrix
`[s(i+j)]` for `m ≤ 5`, reproducing the write-up's `3, 11, 2403, 1127461923`.
-/

namespace Principia.MathDB.P375935

open Finset

/-! ## The two sequences, defined by recursion -/

/-- `T m = ∑_{j=1}^m 2^{j-1}/(2ʲ-1)`, written without `ℕ`-subtraction. -/
noncomputable def T : ℕ → ℝ
  | 0 => 0
  | (m + 1) => T m + (2 : ℝ) ^ m / (2 ^ (m + 1) - 1)

/-- `B m = ∏_{j=1}^m (2ʲ-1)^{2^{m-j}}`, as a recursion. -/
noncomputable def Bp : ℕ → ℝ
  | 0 => 1
  | (m + 1) => (Bp m) ^ 2 * (2 ^ (m + 1) - 1)

theorem T_succ (m : ℕ) : T (m + 1) = T m + (2 : ℝ) ^ m / (2 ^ (m + 1) - 1) := rfl

theorem two_pow_sub_one_pos (j : ℕ) : (0 : ℝ) < 2 ^ (j + 1) - 1 := by
  have h : (1 : ℝ) < 2 ^ (j + 1) := by
    have : (1 : ℝ) = 2 ^ 0 := by norm_num
    rw [this]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith

/-- `d(X) = 3/2 - 1/(2(X-1))` at `X = 2^{m+1}`. -/
noncomputable def dfun (m : ℕ) : ℝ := 3 / 2 - 1 / (2 * ((2 : ℝ) ^ (m + 1) - 1))

/-! ## The carried recurrence, and identity (4) -/

/-- The source's determinant data, shifted so the base case is at `0`:
`Y k = U_{k+2}` and `W k = V_{k+2}`. -/
structure Setup where
  /-- `U_{k+2}(x)` -/
  Y : ℕ → ℝ → ℝ
  /-- `V_{k+2}(x)` -/
  W : ℕ → ℝ → ℝ
  /-- the prefactor `C_{k+3}(x)` -/
  Cc : ℕ → ℝ → ℝ
  hY0 : ∀ x, Y 0 x = 3 - x
  hW0 : ∀ x, W 0 x = 2 - x
  /-- **CARRIED** (Sobolewski–Ulas, Theorem 4.2 / Proposition 4.3, second branch). -/
  hW : ∀ (k : ℕ) (x : ℝ), W (k + 1) x = Cc k x * W k (x / 2)
  hY : ∀ (k : ℕ) (x : ℝ), x ≠ 2 →
    Y (k + 1) x = Cc k x * (Y k (x / 2) + W k (x / 2) / (2 - x))
  /-- **CARRIED** (the write-up's (5)): `V_m(1) = B_m/((2^{m-1}-1)(2^m-1))`. -/
  hW1 : ∀ k : ℕ, W k 1 = Bp (k + 2) / (((2 : ℝ) ^ (k + 1) - 1) * ((2 : ℝ) ^ (k + 2) - 1))
  /-- the Hankel determinant at offset `2` -/
  Hk : ℕ → ℝ
  /-- **CARRIED** (the source recurrence's first branch): `H(2^m+2) = U_m(1)+V_m(1)`. -/
  hHk : ∀ k : ℕ, Hk (k + 2) = Y k 1 + W k 1

namespace Setup

variable (S : Setup)

/-- **IDENTITY (4).**  Dividing the two branches cancels the prefactor `C`, so the
iteration is one algebraic step; `Finset.sum_range_succ'` absorbs the new `j = 0` term. -/
theorem ratio_eq (k : ℕ) (x : ℝ) (hx : ∀ j : ℕ, x / 2 ^ j ≠ 2) :
    S.Y k x = S.W k x * (1 + ∑ j ∈ range (k + 1), 1 / (2 - x / 2 ^ j)) := by
  induction k generalizing x with
  | zero =>
    have h0 : x ≠ 2 := by simpa using hx 0
    have hne : (2 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h0)
    rw [S.hY0, S.hW0, Finset.sum_range_one]
    simp only [pow_zero, div_one]
    field_simp
    ring
  | succ n ih =>
    have h0 : x ≠ 2 := by simpa using hx 0
    have hne : (2 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h0)
    have hx2 : ∀ j : ℕ, x / 2 / 2 ^ j ≠ 2 := by
      intro j hc
      have hre : x / 2 / 2 ^ j = x / 2 ^ (j + 1) := by
        rw [pow_succ]; ring
      rw [hre] at hc
      exact hx (j + 1) hc
    rw [S.hY n x h0, ih (x / 2) hx2, S.hW n x]
    have hsum : (1 : ℝ) + ∑ j ∈ range (n + 2), 1 / (2 - x / 2 ^ j)
        = (1 + ∑ j ∈ range (n + 1), 1 / (2 - x / 2 / 2 ^ j)) + 1 / (2 - x) := by
      rw [Finset.sum_range_succ' (fun j => 1 / (2 - x / 2 ^ j)) (n + 1)]
      simp only [pow_zero, div_one]
      have hre : ∀ j : ℕ, x / 2 ^ (j + 1) = x / 2 / 2 ^ j := by
        intro j; rw [pow_succ]; ring
      simp_rw [hre]
      ring
    rw [hsum]
    ring

/-- At `x = 1` the summand is `2ʲ/(2^{j+1}-1)`. -/
theorem inv_two_sub_eq (j : ℕ) :
    (1 : ℝ) / (2 - 1 / 2 ^ j) = 2 ^ j / (2 ^ (j + 1) - 1) := by
  have h2 : ((2 : ℝ) ^ j) ≠ 0 := by positivity
  have hden : (2 : ℝ) - 1 / 2 ^ j ≠ 0 := by
    have h1 : (1 : ℝ) / 2 ^ j ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    intro hc
    linarith
  field_simp
  ring

/-- so the sum is `T (k+1)`, and `Y k 1 = W k 1 · (1 + T (k+1))`. -/
theorem sum_at_one (k : ℕ) :
    ∑ j ∈ range (k + 1), (1 : ℝ) / (2 - 1 / 2 ^ j) = T (k + 1) := by
  induction k with
  | zero => rw [Finset.sum_range_one, inv_two_sub_eq, T_succ]; simp [T]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, inv_two_sub_eq, T_succ (n + 1)]

theorem ratio_at_one (k : ℕ) : S.Y k 1 = S.W k 1 * (1 + T (k + 1)) := by
  have hx : ∀ j : ℕ, (1 : ℝ) / 2 ^ j ≠ 2 := by
    intro j hc
    have h1 : (1 : ℝ) / 2 ^ j ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    rw [hc] at h1
    linarith
  rw [S.ratio_eq k 1 hx, sum_at_one]

/-- **THE EVALUATION (2).** -/
theorem evaluation (k : ℕ) :
    S.Hk (k + 2)
      = Bp (k + 2) * (2 + T (k + 1))
        / (((2 : ℝ) ^ (k + 1) - 1) * ((2 : ℝ) ^ (k + 2) - 1)) := by
  rw [S.hHk, S.ratio_at_one, S.hW1]
  have h1 := (two_pow_sub_one_pos k).ne'
  have h2 := (two_pow_sub_one_pos (k + 1)).ne'
  field_simp
  ring

/-- `2 + T_{m-1} = T_m + d(X)` — the write-up's "the second follows from
`T_m - T_{m-1} = X/(2(X-1))`". -/
theorem two_add_T_eq (k : ℕ) : 2 + T (k + 1) = T (k + 2) + dfun (k + 1) := by
  have h2 := (two_pow_sub_one_pos (k + 1)).ne'
  have hT : T (k + 2) = T (k + 1) + (2 : ℝ) ^ (k + 1) / (2 ^ (k + 2) - 1) :=
    T_succ (k + 1)
  rw [hT]
  unfold dfun
  field_simp
  ring

/-- and the write-up's second form, `H(2^m+2) = (B_m/A(X))(T_m + d(X))` with `X = 2^m`. -/
theorem evaluation_d (k : ℕ) :
    S.Hk (k + 2)
      = Bp (k + 2) / (((2 : ℝ) ^ (k + 1) - 1) * ((2 : ℝ) ^ (k + 2) - 1))
        * (T (k + 2) + dfun (k + 1)) := by
  rw [S.evaluation, ← two_add_T_eq k]
  ring

/-! ## The obstruction's elementary branch -/

/-- `d(2^m)` is **strictly increasing**. -/
theorem dfun_strictMono (m : ℕ) : dfun m < dfun (m + 1) := by
  have h1 := two_pow_sub_one_pos m
  have h2 := two_pow_sub_one_pos (m + 1)
  have hlt : (2 : ℝ) ^ (m + 1) - 1 < 2 ^ (m + 2) - 1 := by
    have : (2 : ℝ) ^ (m + 1) < 2 ^ (m + 2) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  unfold dfun
  have e : (1 : ℝ) / (2 * ((2 : ℝ) ^ (m + 2) - 1)) < 1 / (2 * ((2 : ℝ) ^ (m + 1) - 1)) := by
    apply one_div_lt_one_div_of_lt
    · linarith
    · linarith
  linarith

/-- **No constant can equal `d(2^m)` eventually** — the `R ≡ 1` branch of the
obstruction.  Two distinct indices already suffice. -/
theorem no_constant (c : ℝ) (m : ℕ) (h1 : c = dfun m) : c ≠ dfun (m + 1) := by
  rw [h1]
  exact (dfun_strictMono m).ne

end Setup

end Principia.MathDB.P375935
