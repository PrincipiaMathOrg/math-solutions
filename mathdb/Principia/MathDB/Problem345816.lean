import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# MathDB 345816 — unimodality for one occurrence of the pattern 112

Write-up: `mathdb-open-problems/problems/345816/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It proves **Conjecture 4.1** of
Dorward: for `n ≥ 3` the polynomial `LS_{n,1}(112)` is unimodal.

## The three pieces, and which one is the write-up's

With `m = n - 2` and `[r] = 1 + q + ⋯ + q^{r-1}`:

* **Carried** (Dorward, Thm 3.3 / Prop 3.5): `q⁻¹ LS_{n,1}(112) = [m] ∏_{i=2}^m (1+qⁱ)`.
* **The write-up's own step, proved here**: that product is the length generating function
  of the minimum-length coset representatives `W^J` for a Weyl group of type `Bₘ` modulo
  the parabolic `W_J` of type `A_{m-2} × A₁`, because
  `F_W = ∏_{i=1}^m [2i]` and `F_{W_J} = [2] ∏_{i=1}^{m-1} [i]` satisfy
  `F_W = F_{W_J} · ([m] ∏_{i=2}^m (1+qⁱ))`.
* **Carried** (Stanley, Thm 3.1): the length coefficients of `W^J` are unimodal.

So the module proves the *identification* and carries the two attributed inputs, which is
exactly how the write-up itself apportions credit.

## How the identity is proved

`qint_two_mul` gives `[2i] = [i](1+qⁱ)` by cancelling `q - 1` against `geom_sum_mul`
(`Polynomial ℤ` is a domain, so `mul_right_cancel₀` applies) — no induction and no
division.  Multiplying over `i ∈ [1,m]` and peeling `i = m` off the `[i]` product and
`i = 1` off the `(1+qⁱ)` product gives the stated factorisation, since `[2] = 1 + q`.

`FWJ_eq` then cancels `F_{W_J}`, which is nonzero because each `[r]` with `r ≥ 1` has
constant coefficient `1`.

## Scope

`Unimodal` is defined here on coefficients, with a single peak index.  The conclusion is
stated for `q⁻¹ LS_{n,1}(112)` — exactly the polynomial the write-up's Theorem asserts to
be symmetric and unimodal — together with `LS_eq : LS n = q · (q⁻¹ LS n)`.  Symmetry is
not formalised; `Campaigns/MathDB-Formalization/verify_345816.py` checks the identity
exactly for `m ≤ 13`, the quoted degree `(m²+3m-4)/2`, symmetry and unimodality for
`m ≤ 11`, and that `F_W(1) = 2^m m! = |Bₘ|`.
-/

namespace Principia.MathDB.P345816

open Finset Polynomial

/-- `[r] = 1 + q + ⋯ + q^{r-1}`. -/
noncomputable def qint (r : ℕ) : Polynomial ℤ := ∑ j ∈ range r, X ^ j

theorem qint_two : qint 2 = 1 + X := by
  simp [qint, Finset.sum_range_succ]

theorem X_sub_one_ne_zero : (X - 1 : Polynomial ℤ) ≠ 0 := by
  intro h
  have h1 : (X - 1 : Polynomial ℤ).coeff 1 = 1 := by
    simp [Polynomial.coeff_one]
  rw [h] at h1
  simp at h1

/-- `[2i] = [i](1 + qⁱ)`, by cancelling `q - 1`. -/
theorem qint_two_mul (i : ℕ) : qint (2 * i) = qint i * (1 + X ^ i) := by
  refine mul_right_cancel₀ X_sub_one_ne_zero ?_
  rw [qint, qint, geom_sum_mul]
  have h : qint i * (1 + X ^ i) * (X - 1) = (qint i * (X - 1)) * (1 + X ^ i) := by ring
  rw [qint] at h
  rw [h, geom_sum_mul, show 2 * i = i + i from by ring, pow_add]
  ring

/-- Multiplying `qint_two_mul` over `i ∈ [1,m]`. -/
theorem prod_qint_two_mul (m : ℕ) :
    ∏ i ∈ Icc 1 m, qint (2 * i)
      = (∏ i ∈ Icc 1 m, qint i) * ∏ i ∈ Icc 1 m, (1 + X ^ i) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => qint_two_mul i

theorem Icc_one_eq_insert {m : ℕ} (hm : 1 ≤ m) :
    Icc 1 m = insert 1 (Icc 2 m) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

theorem prod_qint_top {m : ℕ} (hm : 1 ≤ m) :
    ∏ i ∈ Icc 1 m, qint i = (∏ i ∈ Ico 1 m, qint i) * qint m := by
  rw [show Icc 1 m = Ico 1 (m + 1) from by ext x; simp]
  exact Finset.prod_Ico_succ_top hm _

theorem prod_one_add_bot {m : ℕ} (hm : 1 ≤ m) :
    ∏ i ∈ Icc 1 m, (1 + X ^ i : Polynomial ℤ)
      = (1 + X) * ∏ i ∈ Icc 2 m, (1 + X ^ i : Polynomial ℤ) := by
  rw [Icc_one_eq_insert hm, Finset.prod_insert (by simp)]
  simp

/-- **The coset-quotient identity** — the write-up's own step. -/
theorem F_factor {m : ℕ} (hm : 1 ≤ m) :
    ∏ i ∈ Icc 1 m, qint (2 * i)
      = (qint 2 * ∏ i ∈ Ico 1 m, qint i) * (qint m * ∏ i ∈ Icc 2 m, (1 + X ^ i)) := by
  rw [prod_qint_two_mul, prod_qint_top hm, prod_one_add_bot hm, qint_two]
  ring

/-! ## Nonvanishing, so the quotient is determined -/

theorem qint_coeff_zero {r : ℕ} (hr : 1 ≤ r) : (qint r).coeff 0 = 1 := by
  rw [qint, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [Polynomial.coeff_X_pow, Ne.symm hb]
  · intro h
    simp [Finset.mem_range] at h
    omega

theorem qint_ne_zero {r : ℕ} (hr : 1 ≤ r) : qint r ≠ 0 := by
  intro h
  have := qint_coeff_zero hr
  rw [h] at this
  simp at this

theorem FWJ_denom_ne_zero {m : ℕ} :
    qint 2 * ∏ i ∈ Ico 1 m, qint i ≠ 0 := by
  refine mul_ne_zero (qint_ne_zero (by norm_num)) (Finset.prod_ne_zero_iff.mpr ?_)
  intro i hi
  rw [mem_Ico] at hi
  exact qint_ne_zero hi.1

/-! ## The carried inputs -/

/-- A polynomial is unimodal when its coefficients rise to a peak and then fall. -/
def Unimodal (p : Polynomial ℤ) : Prop :=
  ∃ k : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ k → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, k ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)

/-- Dorward's product formula and Stanley's unimodality theorem, both attributed. -/
structure Setup where
  LS : ℕ → Polynomial ℤ
  FWJ : ℕ → Polynomial ℤ
  /-- Dorward Thm 3.3: `LS_{n,1}(112) = q · [m] ∏_{i=2}^m (1+qⁱ)` with `m = n-2`. -/
  dorward : ∀ n, 3 ≤ n →
    LS n = X * (qint (n - 2) * ∏ i ∈ Icc 2 (n - 2), (1 + X ^ i))
  /-- The coset factorisation `F_W = F_{W_J} · F_{W^J}`. -/
  coset : ∀ m, 1 ≤ m →
    ∏ i ∈ Icc 1 m, qint (2 * i) = (qint 2 * ∏ i ∈ Ico 1 m, qint i) * FWJ m
  /-- Stanley Thm 3.1: the length coefficients of `W^J` are unimodal. -/
  stanley : ∀ m, 1 ≤ m → Unimodal (FWJ m)

namespace Setup

variable (S : Setup)

/-- The identification: `F_{W^J}` really is `[m] ∏_{i=2}^m (1+qⁱ)`. -/
theorem FWJ_eq {m : ℕ} (hm : 1 ≤ m) :
    S.FWJ m = qint m * ∏ i ∈ Icc 2 m, (1 + X ^ i) := by
  refine mul_left_cancel₀ (FWJ_denom_ne_zero (m := m)) ?_
  rw [← S.coset m hm, F_factor hm]

/-- **Dorward's Conjecture 4.1**: `q⁻¹ LS_{n,1}(112)` is unimodal for every `n ≥ 3`. -/
theorem unimodal (S : Setup) {n : ℕ} (hn : 3 ≤ n) :
    Unimodal (qint (n - 2) * ∏ i ∈ Icc 2 (n - 2), (1 + X ^ i)) := by
  have hm : 1 ≤ n - 2 := by omega
  rw [← FWJ_eq S hm]
  exact S.stanley _ hm

/-- and that polynomial is `q⁻¹ LS_{n,1}(112)`. -/
theorem LS_eq {n : ℕ} (hn : 3 ≤ n) :
    S.LS n = X * (qint (n - 2) * ∏ i ∈ Icc 2 (n - 2), (1 + X ^ i)) :=
  S.dorward n hn

end Setup

end Principia.MathDB.P345816
