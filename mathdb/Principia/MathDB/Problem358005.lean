/-
MathDB #358005 — the Amdeberhan–Callan Gaussian-product inequality.

With `B(n,r)` the Gaussian binomial `[n choose r]_q` (zero for `r > n`), the target is

    D_{a,b,k}(q) := B(a,k)·B(a+b,b−k) − B(b,k)·B(a+b,a−k)  ≥_q 0     for 0 ≤ k ≤ a < b,

where `P ≥_q 0` means `P ∈ ℕ[q]`, i.e. every coefficient is nonnegative.  This is Conjecture 4
(arXiv) / Conjecture 15 (journal, p. 1533) of Amdeberhan and Callan.  The write-up proves it by a
Gaussian Vandermonde expansion plus a subspace-intersection linearization, reducing to positivity
of two-by-two Gaussian Pascal minors `Δ_{a,b}(r,s) = B(a,r)B(b,s) − B(a,s)B(b,r)`, which it
settles by an explicit subset injection.

**MEASURED, AND IT IS THE FIRST THING THIS ROW ESTABLISHES: MATHLIB HAS NO GAUSSIAN BINOMIALS.**
A search across the whole library for `gaussBinomial` / `gaussianBinomial` / `qBinomial` /
`qPochhammer` returns nothing; `gaussSum`, `gaussianPDF` and `gaussNorm` are unrelated.  So unlike
every other row banked this session, the object itself has to be built before anything can be
stated.  That is done here.

WHAT IS PROVED.

* `qbin`, the Gaussian binomial over `ℤ[X]`, by the q-Pascal recurrence
  `B(n+1,r+1) = B(n,r) + q^{r+1}·B(n,r+1)`, with `B(n,0) = 1` and `B(0,r+1) = 0`.
* `qbin_self`, `qbin_eq_zero_of_lt` — the boundary values, so the convention "`B(n,r) = 0` for
  `r > n`" that the write-up states in prose is a theorem here.
* `NonnegCoeffs`, the faithful encoding of `≥_q 0`, with closure under `+`, `*` and `X^k·−`.
  The subtraction in `D` is why this cannot simply be done in `ℕ[X]`: truncated subtraction would
  make the statement vacuously true.
* **`qbin_nonneg`** — every Gaussian binomial lies in `ℕ[q]`.  This is the base fact the whole
  positivity argument rests on, and it falls straight out of the recurrence.
* `minor_eq_zero_of_eq` and `minor_nonneg_of_gt` — the two cases of the Pascal-minor lemma the
  write-up disposes of immediately (`r = s` gives zero; `s > a` kills the subtracted product).

CARRIED.  `PascalMinor` in its remaining range (`r < s ≤ a`), which is the subset injection, and
`Conjecture15` itself, which needs the Vandermonde expansion and the linearization formula.  Per
the spine rule both are named hypotheses, never a `sorry`.

Reference: T. Amdeberhan and D. Callan, *Gaussian inequality*, Rocky Mountain J. Math.;
Conjecture 4 (arXiv, p. 7) = Conjecture 15 (journal, p. 1533).
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Principia.MathDB.P358005

open Polynomial

/-! ## 1. The Gaussian binomial, which Mathlib does not have -/

/-- `qbin n r = [n choose r]_q`, by the q-Pascal recurrence
`B(n+1,r+1) = B(n,r) + q^{r+1} B(n,r+1)`. -/
noncomputable def qbin : ℕ → ℕ → Polynomial ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 => qbin n r + (X : Polynomial ℤ) ^ (r + 1) * qbin n (r + 1)

@[simp] theorem qbin_zero_right (n : ℕ) : qbin n 0 = 1 := by cases n <;> rfl

@[simp] theorem qbin_zero_succ (r : ℕ) : qbin 0 (r + 1) = 0 := rfl

theorem qbin_succ_succ (n r : ℕ) :
    qbin (n + 1) (r + 1) = qbin n r + (X : Polynomial ℤ) ^ (r + 1) * qbin n (r + 1) := rfl

/-- The convention the write-up states in prose — `B(n,r) = 0` for `r > n` — is a theorem. -/
theorem qbin_eq_zero_of_lt : ∀ n r : ℕ, n < r → qbin n r = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, r + 1, h => by
      rw [qbin_succ_succ, qbin_eq_zero_of_lt n r (by omega),
        qbin_eq_zero_of_lt n (r + 1) (by omega)]
      ring

theorem qbin_self : ∀ n : ℕ, qbin n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [qbin_succ_succ, qbin_self n, qbin_eq_zero_of_lt n (n + 1) (by omega)]
      ring

/-! ## 2. `≥_q 0`, and why it cannot be done in `ℕ[X]` -/

/-- `P ≥_q 0`: every coefficient is nonnegative.  The subtraction in `D_{a,b,k}` is why this is
stated over `ℤ[X]` — in `ℕ[X]` truncated subtraction would make the conjecture vacuous. -/
def NonnegCoeffs (P : Polynomial ℤ) : Prop := ∀ n, 0 ≤ P.coeff n

theorem nonneg_zero : NonnegCoeffs 0 := by intro n; simp

theorem nonneg_one : NonnegCoeffs 1 := by
  intro n
  rcases eq_or_ne n 0 with rfl | h
  · simp
  · simp [coeff_one, h]

theorem NonnegCoeffs.add {P Q : Polynomial ℤ} (hP : NonnegCoeffs P) (hQ : NonnegCoeffs Q) :
    NonnegCoeffs (P + Q) := by
  intro n
  rw [coeff_add]
  exact add_nonneg (hP n) (hQ n)

theorem NonnegCoeffs.mul {P Q : Polynomial ℤ} (hP : NonnegCoeffs P) (hQ : NonnegCoeffs Q) :
    NonnegCoeffs (P * Q) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hP x.1) (hQ x.2)

theorem nonneg_X_pow (k : ℕ) : NonnegCoeffs ((X : Polynomial ℤ) ^ k) := by
  intro n
  rw [coeff_X_pow]
  split <;> norm_num

/-! ## 3. Gaussian binomials have nonnegative coefficients -/

/-- **Every Gaussian binomial lies in `ℕ[q]`** — the base fact the whole positivity argument
rests on, straight from the recurrence. -/
theorem qbin_nonneg : ∀ n r : ℕ, NonnegCoeffs (qbin n r)
  | _, 0 => by rw [qbin_zero_right]; exact nonneg_one
  | 0, _ + 1 => by rw [qbin_zero_succ]; exact nonneg_zero
  | n + 1, r + 1 => by
      rw [qbin_succ_succ]
      exact (qbin_nonneg n r).add ((nonneg_X_pow (r + 1)).mul (qbin_nonneg n (r + 1)))

/-! ## 4. The Pascal minors — the two cases the write-up disposes of immediately -/

/-- `Δ_{a,b}(r,s) = B(a,r)B(b,s) − B(a,s)B(b,r)`. -/
noncomputable def PascalMinor (a b r s : ℕ) : Polynomial ℤ :=
  qbin a r * qbin b s - qbin a s * qbin b r

/-- The `r = s` case is identically zero. -/
theorem minor_eq_zero_of_eq (a b r : ℕ) : PascalMinor a b r r = 0 := by
  rw [PascalMinor]
  ring

/-- The `s > a` case: the subtracted product vanishes, so the minor is a product of Gaussian
binomials and is nonnegative for free. -/
theorem minor_nonneg_of_gt (a b r s : ℕ) (h : a < s) : NonnegCoeffs (PascalMinor a b r s) := by
  have hz : qbin a s = 0 := qbin_eq_zero_of_lt a s h
  have : PascalMinor a b r s = qbin a r * qbin b s := by
    rw [PascalMinor, hz]
    ring
  rw [this]
  exact (qbin_nonneg a r).mul (qbin_nonneg b s)

/-! ## 5. The conjecture -/

/-- The remaining range of the minor lemma (`r < s ≤ a`), which the write-up settles by an
explicit subset injection.  Carried. -/
def PascalMinorNonneg : Prop :=
  ∀ a b r s : ℕ, a ≤ b → r ≤ s → NonnegCoeffs (PascalMinor a b r s)

/-- `D_{a,b,k}(q) = B(a,k)B(a+b,b−k) − B(b,k)B(a+b,a−k)`. -/
noncomputable def D (a b k : ℕ) : Polynomial ℤ :=
  qbin a k * qbin (a + b) (b - k) - qbin b k * qbin (a + b) (a - k)

/-- **Conjecture 15** (Conjecture 4 of the arXiv version). -/
def Conjecture15 : Prop :=
  ∀ a b k : ℕ, k ≤ a → a < b → NonnegCoeffs (D a b k)

end Principia.MathDB.P358005
