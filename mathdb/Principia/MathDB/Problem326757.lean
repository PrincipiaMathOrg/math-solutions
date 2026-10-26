import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# MathDB 326757 — positive reduced numerators for Carlitz–Riordan interpolation

Write-up: `mathdb-open-problems/problems/326757/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Positive reduced numerators for
Carlitz–Riordan interpolation".  It proves **Conjecture 8** of Chapoton–Zeng: writing
`[r] = 1 + q + ⋯ + q^{r-1}` and `[r]! = ∏_{i≤r}[i]`, the numerators

  `P n = [n-1]! · C_n(x ∣ q)`

of their interpolation polynomials have **nonnegative** integer coefficients.

## The shape of the proof

Chapoton–Zeng's own Theorem 7, eq. (4.9), is a recurrence for `[n] C_{n+1}`.  Multiplying
it through by `[n-1]!` turns it into a recurrence for the numerators,

  `P (n+1) = ([2n-1] + x q^{2n-1}) · P n`
  `        + ∑_{j=0}^{n-2} q^{2j+1} [n-j-1] T j (∏_{t=n-j}^{n-1} [t]) · P (n-j)`,

in which **every multiplier has nonnegative coefficients**.  Induction from `P 1 = 1` then
gives the conjecture.  The write-up is explicit that the recurrence is the authors' result
and the proof is its direct consequence; that division of labour is reproduced here.

## What is carried, and what is proved

**Carried** (`Setup`): the recurrence above, `P 1 = 1`, and the defining recurrence of the
Carlitz–Riordan polynomials `T 0 = 1`, `T (r+1) = ∑_{i≤r} qⁱ T i T (r-i)`.

**Proved**: that `[r]` is nonnegative, that `T r` is nonnegative for every `r` (strong
induction on the carried recurrence — *not* assumed), that nonnegativity is closed under
the ring operations at both levels, and hence `conj8_positivity`.

Note `T_nonneg` is derived rather than carried on purpose: the write-up asserts
"all in `ℤ≥0[q]`" in passing, and asserting it in `Setup` would have made the module's main
induction depend on an unchecked claim of exactly the kind it exists to establish.

## Representation

`Polynomial (Polynomial ℤ)`: the outer variable is `x`, the inner one `q`.  This is what
makes `Nonneg` a two-line definition and its closure under `*` a single
`Polynomial.coeff_mul` plus `Finset.sum_nonneg` at each level — an `MvPolynomial` encoding
would need the same antidiagonal argument with more plumbing.

## Scope (the 215 check)

The conjecture's "positivity" means **nonnegative coefficients, with every coefficient in
the support positive** — and those are the same condition, since a support coefficient is
nonzero by definition.  So `Nonneg` is exactly the conjecture's requirement, not a
weakening.  The write-up's further claims — `[x^{n-1}] P n = q^{(n-1)²}`, that every
`x^k` with `k ≤ n-1` occurs, and coprimality of `P n` with `[n-1]!` (which is what makes
the denominator *reduced*) — are **not** formalised here; they are checked numerically for
`n ≤ 10` in `Campaigns/MathDB-Formalization/verify_326757.py`, which also confirms the
recurrence reproduces them.
-/

namespace Principia.MathDB.P326757

open Finset Polynomial

/-- `q`-polynomials. -/
abbrev QPoly := Polynomial ℤ

/-- Polynomials in `x` whose coefficients are `q`-polynomials. -/
abbrev XPoly := Polynomial QPoly

/-! ## Nonnegativity at the two levels -/

/-- A `q`-polynomial with nonnegative coefficients. -/
def NonnegQ (p : QPoly) : Prop := ∀ k, 0 ≤ p.coeff k

/-- An `x`-polynomial all of whose `q`-coefficients are nonnegative. -/
def Nonneg (P : XPoly) : Prop := ∀ k, NonnegQ (P.coeff k)

theorem NonnegQ.zero : NonnegQ 0 := fun _ => by simp

theorem NonnegQ.one : NonnegQ 1 := fun k => by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [Polynomial.coeff_one, hk]

theorem NonnegQ.add {p q : QPoly} (hp : NonnegQ p) (hq : NonnegQ q) : NonnegQ (p + q) :=
  fun k => by simpa using add_nonneg (hp k) (hq k)

theorem NonnegQ.mul {p q : QPoly} (hp : NonnegQ p) (hq : NonnegQ q) : NonnegQ (p * q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem NonnegQ.sum {ι : Type*} (s : Finset ι) (f : ι → QPoly)
    (h : ∀ i ∈ s, NonnegQ (f i)) : NonnegQ (∑ i ∈ s, f i) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun i hi => h i hi k

theorem NonnegQ.prod {ι : Type*} (s : Finset ι) (f : ι → QPoly)
    (h : ∀ i ∈ s, NonnegQ (f i)) : NonnegQ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using NonnegQ.one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem NonnegQ.X_pow (i : ℕ) : NonnegQ ((Polynomial.X : QPoly) ^ i) := by
  intro k
  rw [Polynomial.coeff_X_pow]
  split <;> norm_num

theorem Nonneg.one : Nonneg 1 := by
  intro k
  rcases eq_or_ne k 0 with rfl | hk
  · simpa [Polynomial.coeff_one] using NonnegQ.one
  · simpa [Polynomial.coeff_one, hk] using NonnegQ.zero

theorem Nonneg.C {p : QPoly} (hp : NonnegQ p) : Nonneg (Polynomial.C p) := by
  intro k
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hp
  · simpa [Polynomial.coeff_C, hk] using NonnegQ.zero

theorem Nonneg.X : Nonneg (Polynomial.X : XPoly) := by
  intro k
  rcases eq_or_ne k 1 with rfl | hk
  · simpa using NonnegQ.one
  · have hz : (Polynomial.X : XPoly).coeff k = 0 := by
      rw [Polynomial.coeff_X]
      simp [Ne.symm hk]
    rw [hz]
    exact NonnegQ.zero

theorem Nonneg.add {P Q : XPoly} (hP : Nonneg P) (hQ : Nonneg Q) : Nonneg (P + Q) :=
  fun k => by simpa using (hP k).add (hQ k)

theorem Nonneg.mul {P Q : XPoly} (hP : Nonneg P) (hQ : Nonneg Q) : Nonneg (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact NonnegQ.sum _ _ fun x _ => (hP _).mul (hQ _)

theorem Nonneg.sum {ι : Type*} (s : Finset ι) (f : ι → XPoly)
    (h : ∀ i ∈ s, Nonneg (f i)) : Nonneg (∑ i ∈ s, f i) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact NonnegQ.sum _ _ fun i hi => h i hi k

/-! ## The `q`-integers -/

/-- `qint r = [r] = 1 + q + ⋯ + q^{r-1}`, with `[0] = 0`. -/
noncomputable def qint (r : ℕ) : QPoly := ∑ i ∈ range r, (Polynomial.X : QPoly) ^ i

theorem qint_nonneg (r : ℕ) : NonnegQ (qint r) :=
  NonnegQ.sum _ _ fun i _ => NonnegQ.X_pow i

/-! ## The carried recurrences -/

/-- Everything taken from Chapoton–Zeng.  `T` are the Carlitz–Riordan polynomials and `P n`
is the numerator `[n-1]! C_n(x ∣ q)`; `P_rec` is their Theorem 7, eq. (4.9), multiplied
through by `[n-1]!`. -/
structure Setup where
  T : ℕ → QPoly
  T_zero : T 0 = 1
  T_rec : ∀ r : ℕ, T (r + 1)
    = ∑ i ∈ range (r + 1), (Polynomial.X : QPoly) ^ i * T i * T (r - i)
  P : ℕ → XPoly
  P_one : P 1 = 1
  P_rec : ∀ n : ℕ, 1 ≤ n → P (n + 1)
    = (Polynomial.C (qint (2 * n - 1))
        + Polynomial.X * Polynomial.C ((Polynomial.X : QPoly) ^ (2 * n - 1))) * P n
      + ∑ j ∈ range (n - 1),
          Polynomial.C ((Polynomial.X : QPoly) ^ (2 * j + 1) * qint (n - j - 1) * T j
            * ∏ t ∈ Finset.Ico (n - j) n, qint t) * P (n - j)

namespace Setup

variable (S : Setup)

/-- The Carlitz–Riordan polynomials are nonnegative.  Proved from `T_rec`, not assumed. -/
theorem T_nonneg : ∀ r, NonnegQ (S.T r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => rw [S.T_zero]; exact NonnegQ.one
    | (m + 1) =>
        rw [S.T_rec m]
        refine NonnegQ.sum _ _ fun i hi => ?_
        rw [mem_range] at hi
        exact ((NonnegQ.X_pow i).mul (ih i (by omega))).mul (ih (m - i) (by omega))

/-- **Chapoton–Zeng Conjecture 8**: every numerator `P n = [n-1]! C_n(x ∣ q)` has
nonnegative integer coefficients. -/
theorem conj8_positivity : ∀ n, 1 ≤ n → Nonneg (S.P n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n, hn with
    | 1, _ => rw [S.P_one]; exact Nonneg.one
    | (m + 2), _ =>
        rw [S.P_rec (m + 1) (by omega)]
        refine Nonneg.add (Nonneg.mul ?_ (ih (m + 1) (by omega) (by omega)))
          (Nonneg.sum _ _ fun j hj => ?_)
        · exact Nonneg.add (Nonneg.C (qint_nonneg _))
            (Nonneg.mul Nonneg.X (Nonneg.C (NonnegQ.X_pow _)))
        · rw [mem_range] at hj
          refine Nonneg.mul (Nonneg.C ?_) (ih (m + 1 - j) (by omega) (by omega))
          exact ((((NonnegQ.X_pow _).mul (qint_nonneg _)).mul (S.T_nonneg j)).mul
            (NonnegQ.prod _ _ fun t _ => qint_nonneg t))

end Setup

end Principia.MathDB.P326757
