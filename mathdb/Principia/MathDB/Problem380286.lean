import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# MathDB #380286 — Fisk's totally stable matrix conjecture is FALSE

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/380286/solution.tex`, refuting Fisk's Conjecture 21.84
(*Polynomials, roots, and interlacing*, printed p. 648; also Question 10 of arXiv:0808.1850).

**The conjecture.**  If `f(x, y) = ∑ⱼ fⱼ(x) yʲ` is a real polynomial with positive coefficients
that does not vanish when both variables lie in the open upper half-plane, then every minor of
`T_f(x)` — the matrix with `fⱼ₋ᵢ(x)` at `(i, j)` for `i ≤ j` and `0` below the diagonal — is
stable, i.e. has no zero in the open right half-plane.

**How it is stated.**  `FiskConj` quantifies over every coefficient array `c` supported in
`[0, N]²`.  "Positive coefficients" is read as `0 ≤ c i j`: the source's own witness omits the
monomial `x²y`, so the phrase cannot mean every monomial up to the degree, and for real numbers
"every nonzero coefficient is positive" is exactly nonnegativity — the hypothesis is not
weakened.  Minors range over strictly increasing row and column index maps of any size `k`.  The
conclusion is weakened in one harmless way: a minor that vanishes identically is exempt, which
only makes the conjecture easier to satisfy.

**The witness.**  `f = (10x + y + 1)(x + y + 10)`, nonvanishing on the product of upper
half-planes because each factor has positive imaginary part there.  Rows `0, 1, 2, 3` and columns
`1, 2, 3, 4` of `T_f` give a tridiagonal minor with determinant
`D(x) = 11111x⁴ + 16661x³ + 17661x² + 16661x + 11111`.

**The root, constructively.**  `D(x) = x² G(x + x⁻¹)` with `G(t) = 11111t² + 16661t − 4561`.
`G(1/5) < 0 < G(1/4)` gives a real `t₀ ∈ (1/5, 1/4)` with `G(t₀) = 0` by the intermediate value
theorem.  `z₀ = (t₀ + i√(4 − t₀²))/2` lies on the unit circle, so `z₀⁻¹ = conj z₀` and
`z₀ + z₀⁻¹ = t₀`; hence `D(z₀) = 0` with `Re z₀ = t₀/2 > 0`.  No Rouché argument is needed — the
reciprocal identity turns the complex root into a real one.  Every value was checked in Python
(SymPy) before this file was written.
-/

namespace Principia.MathDB.P380286

open Finset

/-- `f(x, y) = ∑_{i, j ≤ N} c i j xⁱ yʲ`. -/
def fval (c : ℕ → ℕ → ℝ) (N : ℕ) (x y : ℂ) : ℂ :=
  ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), (c i j : ℂ) * x ^ i * y ^ j

/-- `fⱼ(x) = ∑_{i ≤ N} c i j xⁱ`, the coefficient of `yʲ`. -/
def fj (c : ℕ → ℕ → ℝ) (N j : ℕ) (x : ℂ) : ℂ :=
  ∑ i ∈ range (N + 1), (c i j : ℂ) * x ^ i

/-- The `(r, s)` entry of `T_f(x)`. -/
def T (c : ℕ → ℕ → ℝ) (N : ℕ) (x : ℂ) (r s : ℕ) : ℂ :=
  if r ≤ s then fj c N (s - r) x else 0

/-- The minor of `T_f(x)` on the given rows and columns. -/
def minorDet (c : ℕ → ℕ → ℝ) (N k : ℕ) (rows cols : Fin k → ℕ) (x : ℂ) : ℂ :=
  (Matrix.of fun i j => T c N x (rows i) (cols j)).det

/-- Fisk's Conjecture 21.84. -/
def FiskConj : Prop :=
  ∀ (c : ℕ → ℕ → ℝ) (N : ℕ), (∀ i j, 0 ≤ c i j) → (∀ i j, N < i ∨ N < j → c i j = 0) →
    (∀ x y : ℂ, 0 < x.im → 0 < y.im → fval c N x y ≠ 0) →
    ∀ (k : ℕ) (rows cols : Fin k → ℕ), StrictMono rows → StrictMono cols →
      (∃ z, minorDet c N k rows cols z ≠ 0) →
      ∀ z : ℂ, 0 < z.re → minorDet c N k rows cols z ≠ 0

/-- The coefficients of `(10x + y + 1)(x + y + 10) = 10x² + 11xy + y² + 101x + 11y + 10`. -/
def cw (i j : ℕ) : ℝ :=
  if i = 2 ∧ j = 0 then 10 else if i = 1 ∧ j = 1 then 11 else if i = 0 ∧ j = 2 then 1
  else if i = 1 ∧ j = 0 then 101 else if i = 0 ∧ j = 1 then 11
  else if i = 0 ∧ j = 0 then 10 else 0

theorem cw_nonneg : ∀ i j, 0 ≤ cw i j := by
  intro i j
  unfold cw
  split_ifs <;> norm_num

theorem cw_support : ∀ i j, 2 < i ∨ 2 < j → cw i j = 0 := by
  intro i j h
  unfold cw
  split_ifs <;> first | rfl | (exfalso; omega)

theorem fval_cw (x y : ℂ) : fval cw 2 x y = (10 * x + y + 1) * (x + y + 10) := by
  simp [fval, cw, Finset.sum_range_succ]
  ring

theorem cw_nonvanishing : ∀ x y : ℂ, 0 < x.im → 0 < y.im → fval cw 2 x y ≠ 0 := by
  intro x y hx hy
  rw [fval_cw]
  apply mul_ne_zero
  · intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  · intro h
    have him := congrArg Complex.im h
    simp at him
    linarith

/-- Rows `0, 1, 2, 3`. -/
def rowsW : Fin 4 → ℕ := fun i => (i : ℕ)

/-- Columns `1, 2, 3, 4`. -/
def colsW : Fin 4 → ℕ := fun i => (i : ℕ) + 1

theorem rowsW_mono : StrictMono rowsW := Fin.val_strictMono

theorem colsW_mono : StrictMono colsW := fun _ _ h => Nat.succ_lt_succ h

/-- The minor's determinant, in closed form. -/
def D (x : ℂ) : ℂ := 11111 * x ^ 4 + 16661 * x ^ 3 + 17661 * x ^ 2 + 16661 * x + 11111

/-- Every `Fin.succ`, `Fin.succAbove` and `Fin.val` on the literals a `4 × 4` Laplace expansion
produces, as definitional facts — so the expansion never depends on a simp normal form. -/
theorem minor_det (x : ℂ) : minorDet cw 2 4 rowsW colsW x = D x := by
  rw [minorDet, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply,
    (show Fin.succAbove (0 : Fin 4) (0 : Fin 3) = 1 from rfl),
    (show Fin.succAbove (0 : Fin 4) (1 : Fin 3) = 2 from rfl),
    (show Fin.succAbove (0 : Fin 4) (2 : Fin 3) = 3 from rfl),
    (show Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 from rfl),
    (show Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 from rfl),
    (show Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 from rfl),
    (show Fin.succAbove (2 : Fin 4) (0 : Fin 3) = 0 from rfl),
    (show Fin.succAbove (2 : Fin 4) (1 : Fin 3) = 1 from rfl),
    (show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl),
    (show Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 from rfl),
    (show Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 from rfl),
    (show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl),
    (show Fin.succ (0 : Fin 3) = 1 from rfl),
    (show Fin.succ (1 : Fin 3) = 2 from rfl),
    (show Fin.succ (2 : Fin 3) = 3 from rfl),
    (show ((0 : Fin 4) : ℕ) = 0 from rfl),
    (show ((1 : Fin 4) : ℕ) = 1 from rfl),
    (show ((2 : Fin 4) : ℕ) = 2 from rfl),
    (show ((3 : Fin 4) : ℕ) = 3 from rfl),
    rowsW, colsW]
  simp [T, fj, cw, Finset.sum_range_succ, D]
  ring

/-- `G(t) = 11111t² + 16661t − 4561`, over `ℂ`. -/
def G (t : ℂ) : ℂ := 11111 * t ^ 2 + 16661 * t - 4561

/-- … and over `ℝ`. -/
def Gr (t : ℝ) : ℝ := 11111 * t ^ 2 + 16661 * t - 4561

/-- The reciprocal identity `D(x) = x² G(x + x⁻¹)`. -/
theorem D_eq (x : ℂ) (hx : x ≠ 0) : D x = x ^ 2 * G (x + x⁻¹) := by
  unfold D G
  field_simp
  ring

/-- A real zero of `G` strictly between `1/5` and `1/4`. -/
theorem exists_t0 : ∃ t : ℝ, t ∈ Set.Ioo (1 / 5 : ℝ) (1 / 4) ∧ Gr t = 0 := by
  have hc : ContinuousOn Gr (Set.Icc (1 / 5 : ℝ) (1 / 4)) := by
    unfold Gr
    fun_prop
  have h0 : (0 : ℝ) ∈ Set.Ioo (Gr (1 / 5)) (Gr (1 / 4)) := by
    constructor <;> norm_num [Gr]
  obtain ⟨t, ht, hGt⟩ := intermediate_value_Ioo (by norm_num) hc h0
  exact ⟨t, ht, hGt⟩

/-- `z₀ = (t + i√(4 − t²))/2`. -/
noncomputable def z0 (t : ℝ) : ℂ := ⟨t / 2, Real.sqrt (4 - t ^ 2) / 2⟩

theorem z0_normSq (t : ℝ) (ht : t ^ 2 ≤ 4) : Complex.normSq (z0 t) = 1 := by
  have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 4 - t ^ 2 by linarith)
  rw [Complex.normSq_apply]
  show t / 2 * (t / 2) + Real.sqrt (4 - t ^ 2) / 2 * (Real.sqrt (4 - t ^ 2) / 2) = 1
  linear_combination (1 / 4 : ℝ) * hs

theorem z0_add_inv (t : ℝ) (ht : t ^ 2 ≤ 4) : z0 t + (z0 t)⁻¹ = (t : ℂ) := by
  have hinv : (z0 t)⁻¹ = (starRingEnd ℂ) (z0 t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [Complex.mul_conj, z0_normSq t ht]
    simp
  rw [hinv, Complex.add_conj]
  congr 1
  show 2 * (t / 2) = t
  ring

theorem D_z0 (t : ℝ) (ht : t ^ 2 ≤ 4) (hG : Gr t = 0) : D (z0 t) = 0 := by
  have hne : z0 t ≠ 0 := by
    intro h
    have := z0_normSq t ht
    rw [h] at this
    simp at this
  rw [D_eq _ hne, z0_add_inv t ht]
  have : G (t : ℂ) = ((Gr t : ℝ) : ℂ) := by
    unfold G Gr
    push_cast
    try ring
  rw [this, hG]
  simp

/-- **MathDB #380286: Fisk's Conjecture 21.84 is false.** -/
theorem not_fiskConj : ¬ FiskConj := by
  intro h
  obtain ⟨t, ⟨ht1, ht2⟩, hGt⟩ := exists_t0
  have ht4 : t ^ 2 ≤ 4 := by nlinarith
  have hnz : ∃ z, minorDet cw 2 4 rowsW colsW z ≠ 0 := ⟨0, by rw [minor_det]; norm_num [D]⟩
  have hre : 0 < (z0 t).re := by
    show 0 < t / 2
    linarith
  exact h cw 2 cw_nonneg cw_support cw_nonvanishing 4 rowsW colsW rowsW_mono colsW_mono hnz
    (z0 t) hre (by rw [minor_det]; exact D_z0 t ht4 hGt)

end Principia.MathDB.P380286
