/-
MathDB #322495 — vanishing in Nuttall's normalized determinant expansion.

Write-up `mathdb-open-problems/problems/322495/solution.tex` on the `mathdb-results` branch.
Source: J. Nuttall, *Determinantal approach to a proof of the Riemann hypothesis*,
arXiv:1111.1128v1 (2011), §§6.5 and 7, **Conjecture 3** and equations (7.15)–(7.24).

With `R = r(r-1)`, Nuttall asks that the coefficients `C(i;m,j)` of the normalized
determinant vanish in a stated range.  The write-up proves the stronger statement
`C(i;m,j) = 0` whenever `m + 2i < R`, and — this is the part worth formalising — **the proof
is purely algebraic**: no analytic property of Nuttall's `Φ` is used, and the moments `b_h`
play no role at all.

THE ARGUMENT IN ONE LINE, AND IT IS THE LINE THIS MODULE PROVES.  Writing `t = 1 + x`:

* the coefficient of `y^i` is `Q_i(E_1, …, E_r) B_r(t)`, a differential operator of order at
  most `2i` applied to a fixed polynomial;
* `B_r(1 + x) = ((-1)^{R/2}/r!) ∏_{a<b} (x_b - x_a)^2 (2 + x_a + x_b)^2`, every monomial of
  which has `x`-degree at least `R`;
* **a differential operator of order at most `d` cannot lower the order by more than `d`**,
  so everything below degree `R - 2i` vanishes.

WHAT IS PROVED HERE
* **`vanishing_of_order`** — the theorem, in the form the source consumes: if `B` has order
  at least `R` and `D` is a differential operator of order at most `2 * i`, then every
  coefficient of `D B` in total degree `m < R - 2 * i` is zero.  Equivalently `m + 2i < R`
  forces the coefficient to vanish, which is exactly the write-up's conclusion.
* **`vandermondeSq_minDeg`** — the input: the squared-difference product
  `∏_{p ∈ s} (X p.2 - X p.1)^2` has order at least `2 * s.card`, so over the `C(r,2)` pairs it
  has order `R = r(r-1)`.  **The `(2 + x_a + x_b)^2` factors are handled by
  `MinDeg_mul_left` and contribute nothing**, which is the write-up's *"multiplication by a
  polynomial cannot lower it"*.
* `eulerOp_isOrderLE` — the write-up's `E_a = ½ t_a ∂/∂t_a - (r-1)` is, in the `x` variables,
  a polynomial multiple of one `pderiv` plus a scalar, hence of order at most `1`; so a
  polynomial of degree `2i` in the `E_a` has order at most `2i`.

The general filtration machinery is **campaign-agnostic and lives in
`Principia/Common/PolynomialOrderFiltration.lean`** — it mentions no determinant and no zeta
function.  This module is the part specific to #322495.

CARRIED, and it is the combinatorial bookkeeping rather than the mathematics: the explicit
`Z_σ`, `M_σ` and `P_r`; Lemma 1's claim that `[y^k] F_v(y)` is a polynomial in `v` of degree
at most `2k` (a finite-difference argument via the Bernoulli-style `S_ℓ`); the identity
`B_r(t) = ((-1)^{R/2}/r!) ∏_{a<b}(t_b^2 - t_a^2)^2`; and the fact that the symmetrized
monomials `μ(m,j)` form a basis, which is what turns "the homogeneous component vanishes"
into "each `C(i;m,j)` vanishes".  **None of those is where the proof's content lies** — the
write-up itself calls them normalisation — and all feed the one theorem proved here.

ABSENT FROM MATHLIB, measured: **no `coeff_pderiv`, no `support_pderiv`, no
`totalDegree_pderiv`** (zero hits each).  Mathlib has the *upward* degree filtration
`MvPolynomial.degreesLE` but no downward order filtration, which is why `Common/` now carries
one.
-/
import Principia.Common.PolynomialOrderFiltration

set_option autoImplicit false

namespace Principia.MathDB.P322495

open MvPolynomial Principia.Common.PolynomialOrderFiltration

variable {σ : Type*} {R : Type*} [CommRing R]

/-! ## 1. The input: the squared Vandermonde has order `R` -/

/-- Each squared difference `(X b - X a)^2` has order at least `2`. -/
theorem sq_diff_minDeg (a b : σ) :
    MinDeg ((X b - X a : MvPolynomial σ R) ^ 2) 2 := by
  -- NB `MvPolynomial.support_sub` does not exist at this pin; the bare name resolves to
  -- `Function.support_sub`, which reports as an argument-name error about `R`.  Building the
  -- difference out of `MinDeg_X` and `MinDeg_sub` avoids the support calculus entirely.
  have h1 : MinDeg (X b - X a : MvPolynomial σ R) 1 := MinDeg_sub (MinDeg_X b) (MinDeg_X a)
  have := MinDeg_mul h1 h1
  simpa [sq] using this

/-- **The squared-difference product over any finite set of pairs has order twice its size.**
Over the `C(r,2)` pairs `a < b` this is exactly the write-up's order `R = r(r-1)`. -/
theorem vandermondeSq_minDeg (s : Finset (σ × σ)) :
    MinDeg (∏ p ∈ s, ((X p.2 - X p.1 : MvPolynomial σ R) ^ 2)) (2 * s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MinDeg_of_le_zero (1 : MvPolynomial σ R)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have := MinDeg_mul (sq_diff_minDeg (R := R) a.1 a.2) ih
      refine MinDeg_mono ?_ this
      omega

/-- The write-up's extra factors `(2 + x_a + x_b)^2` cannot lower the order — this is
*"multiplication by a polynomial cannot lower it"*, and it is why they never appear again. -/
theorem minDeg_mul_extra (q : MvPolynomial σ R) {p : MvPolynomial σ R} {N : ℕ}
    (hp : MinDeg p N) : MinDeg (q * p) N :=
  MinDeg_mul_left q hp

/-! ## 2. The Euler operators have order at most one -/

/-- `E_a` in the `x` variables is `c • (q * ∂/∂x_a) + (scalar multiple of the identity)`, and
every such operator has order at most `1`.  Stated for an arbitrary polynomial coefficient `q`
and an arbitrary added multiple of a polynomial, which is the general shape. -/
theorem eulerOp_isOrderLE (q c : MvPolynomial σ R) (i : σ) :
    IsOrderLE (fun p : MvPolynomial σ R => q * pderiv i p + c * p) 1 := by
  refine IsOrderLE.add ?_ ?_
  · have := IsOrderLE.comp (IsOrderLE.mulLeft q) (IsOrderLE.deriv (R := R) i)
    simpa using this
  · exact IsOrderLE.mono (Nat.zero_le 1) (IsOrderLE.mulLeft c)

/-! ## 3. The theorem -/

/-- **The write-up's Theorem, in the form Nuttall's coefficients consume.**

If `B` has order at least `Rr` and `D` is a differential operator of order at most `2 * i`
with polynomial coefficients, then every coefficient of `D B` in total degree `m` with
`m + 2 * i < Rr` vanishes.  Applied with `B = B_r(1+x)` (order `R`, by
`vandermondeSq_minDeg`) and `D = Q_i(E_1,…,E_r)` (order `≤ 2i`, by `eulerOp_isOrderLE` and
composition) this is `C(i;m,j) = 0` for `m + 2i < R`. -/
theorem vanishing_of_order {B : MvPolynomial σ R} {Rr i : ℕ} (hB : MinDeg B Rr)
    {D : MvPolynomial σ R → MvPolynomial σ R} (hD : IsOrderLE D (2 * i))
    {m : σ →₀ ℕ} (hm : m.degree + 2 * i < Rr) :
    (D B).coeff m = 0 := by
  have hDB : MinDeg (D B) (Rr - 2 * i) := MinDeg_of_isOrderLE hD hB
  exact coeff_eq_zero_of_degree_lt hDB (by omega)

/-- **Nuttall's requested range is contained in the range proved**, which is what makes the
write-up's *"a slightly larger range than requested"* precise.

Only two of the source's four side conditions are needed: `m ≤ R - 2i - 2` together with
`2i + 2 ≤ R`.  The bounds `i ≤ R/2 - 1` and `2 ≤ R` are **implied and were dropped** — an
earlier draft carried all four and `omega` never touched two of them, which is the
used-but-unnecessary-hypothesis trap that no linter reports. -/
theorem conjecture3_range {Rr i m : ℕ} (hm : m ≤ Rr - 2 * i - 2) (hi2 : 2 * i + 2 ≤ Rr) :
    m + 2 * i < Rr := by
  omega

end Principia.MathDB.P322495
