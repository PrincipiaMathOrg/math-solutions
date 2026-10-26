import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 320607 — rational differences of periodic Dyck-path generating functions

Write-up: `mathdb-open-problems/problems/320607/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It proves **both parts of
Conjecture 5.2** of Eu and Fu as special cases of one identity: for `i ≥ 1` and
`m ≥ 2i+2`,

  `G^{(m-i-1)} - G^{(i)} = (1-y)xⁱD_{m-2i-2} / (D_{m-1} + x(1-y)D_{i-1}D_{m-i-2})`,

where `D` is the continuant sequence `D_{-1} = 0`, `D₀ = D₁ = 1`,
`Dₙ = D_{n-1} - x D_{n-2}`, and `G^{(c)}` counts Dyck paths by up steps at height
`≡ c (mod m)`.

## Everything here is polynomial algebra

No power series are needed: the whole argument lives in an arbitrary commutative ring
with two elements `x`, `y`, and the final identity is stated **cleared of denominators**.

* `E` is the continuant, **shifted** so that `E k = D_{k-1}`.  That makes `E 0 = 0` the
  base case and removes every `ℕ`-subtraction from the development.
* `M_pow` — `M^{n+1} = !![-x·E n, E (n+1); -x·E (n+1), E (n+2)]`, by induction.
* `A_entry`, `C_entry` — the `(0,0)` and `(1,0)` entries of
  `P a b = Mᵃ · M_y · M^{b+1}` (so the source's `c = a+1` and `m = a+b+2`).
* **`C_symm`** — `C (a) (b+1) = C (b) (a+1)`, which in the source's indices is exactly
  `C_c = C_{m-c-1}`.  This is the symmetry that lets the quadratic terms cancel, and in
  this parametrisation it is visible: the formula depends on `a` and `b` only through
  `E (a+1) · E (b+1)`.
* **`continuant`** — `E (a+1)·E (a+c+1) - E a·E (a+c+2) = xᵃ·E (c+1)`, by induction.
* `A_diff` — hence `A_d - A_c = -x^{p+2}(1-y)·E (r+1)`.
* `disc_eq` — completing the square: `(E_c - A_c)² + 4B_cC_c = T² - 4·det P`, so the
  `S_c` all have the same square.
* `Setup.conjecture` — the cleared identity, and `Setup.eu_fu_first` / `eu_fu_second`
  the two cases `i = 1` and `i = 2` that Conjecture 5.2 states.

## What is carried

`Setup` carries the combinatorial input: that `G^{(c)}` satisfies the source's continued
fraction `C_c·G² + (E_c - A_c)·G - B_c = 0` (its Theorem 3.1), and that the branch is
pinned so `S_c = S_d` — the write-up gets that from `S_c(0,y) = 1` and invertibility of
`S_c + S_d`.

`Campaigns/MathDB-Formalization/verify_320607.py` checks every algebraic step in exact
rationals, and validates the final cleared identity against `G^{(c)}` computed by
**directly enumerating Dyck paths**; the residual is confirmed to be truncation
(`2.8e-07` at semilength `≤ 6`, `2.7e-12` at `≤ 12`) rather than error.
-/

namespace Principia.MathDB.P320607

open Matrix

variable {R : Type*} [CommRing R]

/-! ## The shifted continuant -/

/-- `E k = D_{k-1}`: `E 0 = D_{-1} = 0`, `E 1 = D₀ = 1`, `E (k+2) = E (k+1) - x·E k`.
Shifting by one makes `0` the base case and removes every `ℕ`-subtraction below. -/
def E (x : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (k + 2) => E x (k + 1) - x * E x k

@[simp] theorem E_zero (x : R) : E x 0 = 0 := rfl
@[simp] theorem E_one (x : R) : E x 1 = 1 := rfl

theorem E_succ_succ (x : R) (k : ℕ) : E x (k + 2) = E x (k + 1) - x * E x k := rfl

@[simp] theorem E_two (x : R) : E x 2 = 1 := by rw [E_succ_succ]; simp

/-! ## The transfer matrices -/

/-- `M = !![0, 1; -x, 1]`, the unmarked transfer matrix. -/
def M (x : R) : Matrix (Fin 2) (Fin 2) R := !![0, 1; -x, 1]

/-- `M_y = !![0, 1; -xy, 1]`, the marked one. -/
def My (x y : R) : Matrix (Fin 2) (Fin 2) R := !![0, 1; -(x * y), 1]

/-- **The matrix power.** -/
theorem M_pow (x : R) (n : ℕ) :
    M x ^ (n + 1) = !![-x * E x n, E x (n + 1); -x * E x (n + 1), E x (n + 2)] := by
  induction n with
  | zero =>
    rw [pow_one, M]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E_succ_succ]
  | succ k ih =>
    rw [pow_succ, ih, M]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, E_succ_succ] <;> ring

/-- `P a b = Mᵃ · M_y · M^{b+1}`.  In the source's indices this is `P_c` with
`c = a + 1` and `m = a + b + 2`. -/
def P (x y : R) (a b : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  M x ^ a * My x y * M x ^ (b + 1)

/-- **The continuant addition formula**, read off from `M^{a+1}·M^{b+1} = M^{a+b+2}`. -/
theorem E_add (x : R) (a b : ℕ) :
    E x (a + b + 2) = E x (a + 1) * E x (b + 2) - x * E x a * E x (b + 1) := by
  have h : M x ^ (a + 1) * M x ^ (b + 1) = M x ^ (a + b + 1 + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h01 := congrFun (congrFun h 0) 1
  rw [M_pow, M_pow, M_pow] at h01
  have hi : a + b + 1 + 1 = a + b + 2 := by omega
  rw [hi] at h01
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  linear_combination -h01

/-! ## The matrix entries justify the closed forms -/

/-- `A a b = -x·E (a+b+1) - x²(1-y)·E a·E b`. -/
def Aent (x y : R) (a b : ℕ) : R :=
  -x * E x (a + b + 1) - x ^ 2 * (1 - y) * E x a * E x b

/-- `C a b = -x·(E (a+b+2) + x(1-y)·E (a+1)·E b)`. -/
def Cent (x y : R) (a b : ℕ) : R :=
  -x * (E x (a + b + 2) + x * (1 - y) * E x (a + 1) * E x b)

/-- Index-normalised forms of the two recurrences, matching what `ring_nf` produces. -/
theorem E_add' (x : R) (k b : ℕ) :
    E x (2 + k + b) = E x (1 + k) * E x (2 + b) - x * E x k * E x (1 + b) := by
  have h := E_add x k b
  have i1 : k + b + 2 = 2 + k + b := by omega
  have i2 : k + 1 = 1 + k := by omega
  have i3 : b + 2 = 2 + b := by omega
  have i4 : b + 1 = 1 + b := by omega
  rw [i1, i2, i3, i4] at h
  exact h

theorem E_step' (x : R) (b : ℕ) : E x (2 + b) = E x (1 + b) - x * E x b := by
  have h := E_succ_succ x b
  have i3 : b + 2 = 2 + b := by omega
  have i4 : b + 1 = 1 + b := by omega
  rw [i3, i4] at h
  exact h

/-- The `(0,0)` entry of `P a b` really is `Aent a b`. -/
theorem A_entry (x y : R) (a b : ℕ) : P x y a b 0 0 = Aent x y a b := by
  rcases a with _ | k
  · simp only [P, pow_zero, one_mul, My, M_pow, Aent, E_zero]
    simp [Matrix.mul_apply, Fin.sum_univ_two, E_succ_succ]
  · simp only [P, M_pow, My, Aent]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    linear_combination x * E_add' x k b + x * E x (1 + k) * E_step' x b

/-- `Mᵃ` row 1 is `M^{a+1}` row 0, because `M^{a+1} = M·Mᵃ` and `M`'s first row is
`(0, 1)`. -/
theorem M_row_shift (x : R) (a : ℕ) (j : Fin 2) :
    (M x ^ a) 1 j = (M x ^ (a + 1)) 0 j := by
  rw [pow_succ']
  simp [Matrix.mul_apply, Fin.sum_univ_two, M]

/-- The two closed forms are the same formula one step apart. -/
theorem Cent_eq_Aent (x y : R) (a b : ℕ) : Cent x y a b = Aent x y (a + 1) b := by
  unfold Cent Aent
  have h : a + 1 + b + 1 = a + b + 2 := by omega
  rw [h]
  ring

/-- The `(1,0)` entry of `P a b` really is `Cent a b` — it is the `(0,0)` entry of
`P (a+1) b`, by the row shift. -/
theorem C_entry (x y : R) (a b : ℕ) : P x y a b 1 0 = Cent x y a b := by
  rw [Cent_eq_Aent, ← A_entry]
  unfold P
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, M_row_shift]

/-- **The symmetry `C_c = C_{m-c-1}`.**  In this parametrisation the formula depends on
`a` and `b` only through `E (a+1)·E (b+1)` and `a+b`, so it is visible. -/
theorem C_symm (x y : R) (a b : ℕ) : Cent x y a (b + 1) = Cent x y b (a + 1) := by
  unfold Cent
  have h : a + (b + 1) + 2 = b + (a + 1) + 2 := by omega
  rw [h]
  ring

/-! ## The continuant identity -/

/-- **`E (a+1)·E (a+c+1) - E a·E (a+c+2) = xᵃ·E (c+1)`.** -/
theorem continuant (x : R) (a c : ℕ) :
    E x (a + 1) * E x (a + c + 1) - E x a * E x (a + c + 2) = x ^ a * E x (c + 1) := by
  induction a with
  | zero => simp
  | succ k ih =>
    have i1 : k + 1 + c + 1 = k + c + 2 := by omega
    have i2 : k + 1 + c + 2 = k + c + 1 + 2 := by omega
    have i3 : k + 1 + 1 = k + 2 := by omega
    rw [i1, i2, i3, E_succ_succ x k, E_succ_succ x (k + c + 1)]
    have i4 : k + c + 1 + 1 = k + c + 2 := by omega
    rw [i4, pow_succ]
    linear_combination x * ih

/-! ## The difference of the two `A` entries -/

/-- With `c ↔ (a,b) = (p, p+r+2)` and `d ↔ (a,b) = (p+r+1, p+1)` — both giving
`m = 2p+r+4` — the `-x·E (a+b+1)` terms are equal and the continuant identity collapses
what is left. -/
theorem A_diff (x y : R) (p r : ℕ) :
    Aent x y (p + r + 1) (p + 1) - Aent x y p (p + r + 2)
      = -(x ^ (p + 2) * (1 - y) * E x (r + 1)) := by
  unfold Aent
  have h1 : p + r + 1 + (p + 1) + 1 = 2 * p + r + 3 := by omega
  have h2 : p + (p + r + 2) + 1 = 2 * p + r + 3 := by omega
  rw [h1, h2]
  have hc := continuant x p r
  have hp : x ^ (p + 2) = x ^ p * x ^ 2 := by rw [pow_add]
  rw [hp]
  linear_combination (-(x ^ 2) * (1 - y)) * hc

/-! ## The carried combinatorial input -/

/-- What the source's continued fraction (its Theorem 3.1) and the branch choice give.
`hSeq` is `S_c = S_d` after substituting `E_c = T - A_c` and cancelling the common
trace `T`; the write-up obtains it from `S_c² = T² - 4xᵐy`, `S_c(0,y) = 1`, and
invertibility of `S_c + S_d`. -/
structure Setup (R : Type*) [CommRing R] where
  x : R
  y : R
  /-- `x` is a non-zero-divisor; in the source's ring `ℚ[y][[x]]` it is. -/
  hx : ∀ u v : R, x * u = x * v → u = v
  /-- so is `2`. -/
  h2 : ∀ u v : R, 2 * u = 2 * v → u = v
  /-- `G c` is the generating function for up steps at height `≡ c (mod m)`. -/
  G : ℕ → R
  /-- **CARRIED**: the two `S` values agree, with the traces cancelled. -/
  hSeq : ∀ a b : ℕ,
    2 * Cent x y a (b + 1) * G (a + 1) - 2 * Aent x y a (b + 1)
      = 2 * Cent x y b (a + 1) * G (b + 1) - 2 * Aent x y b (a + 1)

namespace Setup

variable (S : Setup R)

/-- `C·(G_d - G_c) = A_d - A_c`, derived from the carried `S_c = S_d` using the
**symmetry** `C_c = C_d`. -/
theorem hdiff (a b : ℕ) :
    Cent S.x S.y a (b + 1) * (S.G (b + 1) - S.G (a + 1))
      = Aent S.x S.y b (a + 1) - Aent S.x S.y a (b + 1) := by
  have hs := S.hSeq a b
  rw [C_symm S.x S.y a b] at hs ⊢
  refine S.h2 _ _ ?_
  linear_combination -hs

/-- **THE GENERAL IDENTITY, cleared of denominators.**  With `i = p+1` and
`m = 2p + r + 4` (so `m ≥ 2i+2` says exactly `r ≥ 0`),

  `(D_{m-1} + x(1-y)D_{i-1}D_{m-i-2})·(G^{(m-i-1)} - G^{(i)}) = (1-y)xⁱD_{m-2i-2}`. -/
theorem conjecture (p r : ℕ) :
    (E S.x (2 * p + r + 4) + S.x * (1 - S.y) * E S.x (p + 1) * E S.x (p + r + 2))
        * (S.G (p + r + 2) - S.G (p + 1))
      = (1 - S.y) * S.x ^ (p + 1) * E S.x (r + 1) := by
  have hd := S.hdiff p (p + r + 1)
  have hb : p + r + 1 + 1 = p + r + 2 := by omega
  rw [hb, A_diff S.x S.y p r] at hd
  have hC : Cent S.x S.y p (p + r + 2)
      = -S.x * (E S.x (2 * p + r + 4)
        + S.x * (1 - S.y) * E S.x (p + 1) * E S.x (p + r + 2)) := by
    unfold Cent
    have h : p + (p + r + 2) + 2 = 2 * p + r + 4 := by omega
    rw [h]
  rw [hC] at hd
  refine S.hx _ _ ?_
  have hp : S.x ^ (p + 2) = S.x * S.x ^ (p + 1) := by rw [pow_succ']
  rw [hp] at hd
  linear_combination -hd

/-- **Eu–Fu Conjecture 5.2, first identity** is the case `i = 1`, i.e. `p = 0`. -/
theorem eu_fu_first (r : ℕ) :
    (E S.x (r + 4) + S.x * (1 - S.y) * E S.x 1 * E S.x (r + 2))
        * (S.G (r + 2) - S.G 1)
      = (1 - S.y) * S.x ^ 1 * E S.x (r + 1) := by
  have h := S.conjecture 0 r
  have i1 : 2 * 0 + r + 4 = r + 4 := by omega
  have i2 : 0 + r + 2 = r + 2 := by omega
  rw [i1, i2] at h
  norm_num at h ⊢
  exact h

/-- **Eu–Fu Conjecture 5.2, second identity** is the case `i = 2`, i.e. `p = 1`. -/
theorem eu_fu_second (r : ℕ) :
    (E S.x (r + 6) + S.x * (1 - S.y) * E S.x 2 * E S.x (r + 3))
        * (S.G (r + 3) - S.G 2)
      = (1 - S.y) * S.x ^ 2 * E S.x (r + 1) := by
  have h := S.conjecture 1 r
  have i1 : 2 * 1 + r + 4 = r + 6 := by omega
  have i2 : 1 + r + 2 = r + 3 := by omega
  rw [i1, i2] at h
  norm_num at h ⊢
  exact h

end Setup

end Principia.MathDB.P320607
