import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# MathDB #316888 — order-independent Hermite means

Write-up: `mathdb-open-problems/problems/316888/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Horwitz, **Conjecture 23** (published p. 95): independence of both interpolation
orders characterises `f(x) = C/x`.

For `0 < a < b` and integers `0 ≤ m₂ < m₁`, put `n = m₁+m₂+1` and `m = m₁−m₂`.  `P` is the
degree-`≤ n` Hermite interpolant to `f` matching derivatives through order `m₁` at `a` and
`m₂` at `b`; `Q` swaps the orders.  With `E_P = f−P`, `E_Q = f−Q`, the source defines the
mean as the interior solution of `E_P(x) = (−1)^m E_Q(x)` — which covers both of its cases
(`P = Q` for even `m`, `2f = P+Q` for odd `m`).

**`not_conj` refutes Conjecture 23**: `f(x) = 1/(x+1)` has a mean independent of both
orders, yet is not `C/x`.

## Why this needs no Hermite-interpolation theory

The row was deferred on 2026-09-16 as "needs general Hermite interpolation, which Mathlib
lacks".  **That was wrong.**  The source's own proof never interpolates: for
`f(x) = C/(x+c)` it observes that `C − (x+c)P(x)` is a polynomial of degree `≤ n+1`
vanishing at the nodes to the required multiplicities, hence a constant multiple of the
monic `W_P = (X−a)^{m₁+1}(X−b)^{m₂+1}`; evaluating at `−c` pins the constant.  That is
pure polynomial algebra, and it is what `Interp` and `interp_eq` encode here — the
interpolation conditions are stated in exactly the divisibility form the source uses.

## What is proved

* `interp_eq` — from `Interp`, `C − (X+c)·P = (C / W_P(−c)) • W_P`.  Degree counting plus
  `Polynomial.eq_C_of_degree_le_zero`; this is the write-up's key step.
* `err_eq` — hence the error has the closed form `E_P(x) = C·W_P(x)/((x+c)·W_P(−c))`.
* `ratio_eq` — `E_P(x)/E_Q(x) = (−1)^m ((x−a)(b+c)/((b−x)(a+c)))^m` for `a < x < b`.
* `mean_unique` — **the defining equation has the unique interior solution
  `Mc a b c = (2ab + c(a+b))/(a+b+2c)`, independent of `m₁` and `m₂`.**  That independence
  is the whole content of "order-independent".
* `not_conj` — `f(x) = 1/(x+1)` is order-independent but not of the form `C/x`.

## What is NOT here

The classification half of the write-up (that `C/(x+c) + p`, `deg p ≤ 2`, is the *complete*
list of order-independent generators) is absent: it needs a converse argument over all
smooth `f`.  Refuting Conjecture 23 needs only the witness, not the classification.

Also not formalized: that the polynomial divisibility form of the interpolation conditions
is equivalent to the derivative-matching form.  That equivalence is standard, and the
source argues in the divisibility form throughout, so the statement here is the source's.
`Campaigns/MathDB-Formalization/verify_316888.py` closes the gap empirically — it computes
the genuine Hermite interpolant from its defining derivative conditions for seven order
pairs and confirms the closed form each time.

Values checked in `Campaigns/MathDB-Formalization/verify_316888.py`.
-/

namespace Principia.MathDB.P316888

open Polynomial

/-- `W_P = (X−a)^{m₁+1} (X−b)^{m₂+1}`, the node polynomial. -/
noncomputable def W (a b : ℝ) (m1 m2 : ℕ) : Polynomial ℝ :=
  (X - Polynomial.C a) ^ (m1 + 1) * (X - Polynomial.C b) ^ (m2 + 1)

theorem W_ne_zero (a b : ℝ) (m1 m2 : ℕ) : W a b m1 m2 ≠ 0 := by
  rw [W]
  exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a)) (pow_ne_zero _ (X_sub_C_ne_zero b))

theorem W_natDegree (a b : ℝ) (m1 m2 : ℕ) :
    (W a b m1 m2).natDegree = m1 + m2 + 2 := by
  rw [W, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) (pow_ne_zero _ (X_sub_C_ne_zero b)),
    natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C]
  ring

theorem W_eval (a b : ℝ) (m1 m2 : ℕ) (x : ℝ) :
    (W a b m1 m2).eval x = (x - a) ^ (m1 + 1) * (x - b) ^ (m2 + 1) := by
  simp [W]

/-- `W_P(−c) ≠ 0` when `a, b > 0` and `c ≥ 0`. -/
theorem W_eval_neg_c_ne (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (m1 m2 : ℕ) :
    (W a b m1 m2).eval (-c) ≠ 0 := by
  rw [W_eval]
  have h1 : (-c - a) ≠ 0 := by intro h; nlinarith
  have h2 : (-c - b) ≠ 0 := by intro h; nlinarith
  exact mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)

/-- **The interpolation conditions, in the divisibility form the source's proof uses.**
`P` has degree `≤ n = m₁+m₂+1` and `C − (X+c)·P` vanishes at the nodes to the required
multiplicities. -/
def Interp (Cc c a b : ℝ) (m1 m2 : ℕ) (P : Polynomial ℝ) : Prop :=
  P.degree ≤ (m1 + m2 + 1 : ℕ) ∧
    W a b m1 m2 ∣ (Polynomial.C Cc - (X + Polynomial.C c) * P)

/-- **The write-up's key step.**  Degree counting forces the quotient to be a constant, and
evaluating at `−c` identifies it. -/
theorem interp_eq {Cc c a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    {m1 m2 : ℕ} {P : Polynomial ℝ} (hP : Interp Cc c a b m1 m2 P) :
    Polynomial.C Cc - (X + Polynomial.C c) * P
      = Polynomial.C (Cc / (W a b m1 m2).eval (-c)) * W a b m1 m2 := by
  obtain ⟨hdeg, q, hq⟩ := hP
  have hWne := W_ne_zero a b m1 m2
  have hWc := W_eval_neg_c_ne a b c ha hb hc m1 m2
  -- evaluating at `-c` kills the `(X+c)P` term
  have hev : Cc = (W a b m1 m2).eval (-c) * q.eval (-c) := by
    have h := congrArg (Polynomial.eval (-c)) hq
    simp only [eval_sub, eval_C, eval_mul, eval_add, eval_X] at h
    have hz : (-c + c) = 0 := by ring
    rw [hz, zero_mul, sub_zero] at h
    exact h
  rcases eq_or_ne q 0 with hq0 | hq0
  · subst hq0
    rw [mul_zero] at hq
    rw [eval_zero, mul_zero] at hev
    rw [hq, hev]
    simp
  · -- `deg (C Cc - (X+c)P) ≤ n+1 = deg W`, so the quotient has degree 0
    have hub : (Polynomial.C Cc - (X + Polynomial.C c) * P).natDegree ≤ m1 + m2 + 2 := by
      refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
      refine le_trans (natDegree_mul_le) ?_
      have h1 : (X + Polynomial.C c : Polynomial ℝ).natDegree ≤ 1 := by
        rw [show (X + Polynomial.C c : Polynomial ℝ) = X - Polynomial.C (-c) by
          rw [map_neg, sub_neg_eq_add], natDegree_X_sub_C]
      have h2 : P.natDegree ≤ m1 + m2 + 1 := natDegree_le_iff_degree_le.2 hdeg
      omega
    have hd : (Polynomial.C Cc - (X + Polynomial.C c) * P).natDegree
        = (m1 + m2 + 2) + q.natDegree := by
      rw [hq, natDegree_mul hWne hq0, W_natDegree]
    have hq00 : q.natDegree = 0 := by omega
    obtain ⟨lam, hlam⟩ := natDegree_eq_zero.1 hq00
    subst hlam
    rw [eval_C] at hev
    rw [hq, mul_comm]
    congr 1
    rw [hev]
    field_simp


/-! ### The order-independent mean -/

/-- The order-independent mean `M_c(a,b) = (2ab + c(a+b))/(a+b+2c)`. -/
noncomputable def Mc (a b c : ℝ) : ℝ := (2 * a * b + c * (a + b)) / (a + b + 2 * c)

theorem Mc_mem {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 ≤ c) :
    a < Mc a b c ∧ Mc a b c < b := by
  have hd : 0 < a + b + 2 * c := by linarith
  constructor
  · rw [Mc, lt_div_iff₀ hd]; nlinarith
  · rw [Mc, div_lt_iff₀ hd]; nlinarith

/-- **The reduced equation pins the mean, for every `m ≥ 1`.**  The solution does not
depend on `m`, which is exactly the order-independence. -/
theorem mean_char {a b c x : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hx1 : a < x) (hx2 : x < b) {m : ℕ} (hm : 1 ≤ m) :
    ((x - a) * (c + b)) ^ m = ((b - x) * (c + a)) ^ m ↔ x = Mc a b c := by
  have hxa : 0 < x - a := by linarith
  have hbx : 0 < b - x := by linarith
  have hca : 0 < c + a := by linarith
  have hcb : 0 < c + b := by linarith
  rw [pow_left_inj₀ (by positivity) (by positivity) (by omega : m ≠ 0)]
  constructor
  · intro h
    rw [Mc]
    have hd : 0 < a + b + 2 * c := by linarith
    field_simp
    nlinarith [h]
  · intro h
    subst h
    rw [Mc]
    have hd : 0 < a + b + 2 * c := by linarith
    field_simp
    ring


/-! ### The sign bookkeeping, and the refutation -/

/-- **Both sides of the defining equation carry the same sign.**  Pairing `A` with `−V` and
`−B` with `−U` makes that visible: each side is `(−1)^(k+m)` times a product of positive
powers, so the equation collapses to one about positive quantities. -/
theorem sign_reduce {A B U V : ℝ} (hA : 0 < A) (hB : 0 < B) (hU : 0 < U) (hV : 0 < V)
    (k m : ℕ) :
    (A ^ (k + m) * (-B) ^ k) * ((-U) ^ k * (-V) ^ (k + m))
        = (-1 : ℝ) ^ m * ((A ^ k * (-B) ^ (k + m)) * ((-U) ^ (k + m) * (-V) ^ k))
      ↔ (A * V) ^ m = (B * U) ^ m := by
  have hs : ∀ (y : ℝ) (j : ℕ), (-y) ^ j = (-1 : ℝ) ^ j * y ^ j := by
    intro y j; rw [neg_eq_neg_one_mul, mul_pow]
  have e1 : (A ^ (k + m) * (-B) ^ k) * ((-U) ^ k * (-V) ^ (k + m))
      = (-1 : ℝ) ^ (k + m) * ((A * V) ^ (k + m) * (B * U) ^ k) := by
    rw [hs B, hs U, hs V, mul_pow, mul_pow, pow_add ((-1 : ℝ)) k m]
    rcases Nat.even_or_odd k with hk | hk <;> rcases Nat.even_or_odd m with hm | hm <;>
      rw [hk.neg_one_pow, hm.neg_one_pow] <;> ring
  have e2 : (-1 : ℝ) ^ m * ((A ^ k * (-B) ^ (k + m)) * ((-U) ^ (k + m) * (-V) ^ k))
      = (-1 : ℝ) ^ (k + m) * ((A * V) ^ k * (B * U) ^ (k + m)) := by
    rw [hs B, hs U, hs V, mul_pow, mul_pow, pow_add ((-1 : ℝ)) k m]
    rcases Nat.even_or_odd k with hk | hk <;> rcases Nat.even_or_odd m with hm | hm <;>
      rw [hk.neg_one_pow, hm.neg_one_pow] <;> ring
  have hne : ((-1 : ℝ) ^ (k + m)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hAV : (0:ℝ) < (A * V) ^ k := by positivity
  have hBU : (0:ℝ) < (B * U) ^ k := by positivity
  rw [e1, e2]
  constructor
  · intro h
    have h1 := mul_left_cancel₀ hne h
    rw [pow_add, pow_add] at h1
    have h2 : ((A * V) ^ k * (B * U) ^ k) * (A * V) ^ m
        = ((A * V) ^ k * (B * U) ^ k) * (B * U) ^ m := by linear_combination h1
    exact mul_left_cancel₀ (ne_of_gt (mul_pos hAV hBU)) h2
  · intro h
    rw [pow_add, pow_add]
    linear_combination ((-1 : ℝ) ^ (k + m) * (A * V) ^ k * (B * U) ^ k) * h

/-- Clearing the two nonzero denominators.  Proved over ABSTRACT arguments, where
`field_simp` sees the denominators literally; instantiating afterwards avoids the
normalisation that otherwise defeats `linear_combination`. -/
theorem div_reduce {Cc WPx WQx WPc WQc s : ℝ} (hC : Cc ≠ 0) (hP : WPc ≠ 0) (hQ : WQc ≠ 0) :
    (Cc / WPc * WPx = s * (Cc / WQc * WQx)) ↔ (WPx * WQc = s * (WQx * WPc)) := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff hP hQ]
  constructor
  · intro h
    exact mul_left_cancel₀ hC (by linear_combination h)
  · intro h
    linear_combination Cc * h

/-- **The defining equation has the unique interior solution `M_c`, for EVERY admissible
order pair.**  That independence is the order-independence Conjecture 23 claims
characterises `C/x`. -/
theorem mean_unique {Cc c a b : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 ≤ c)
    (hCc : Cc ≠ 0) {m1 m2 : ℕ} (hm : m2 < m1)
    {P Q : Polynomial ℝ} (hP : Interp Cc c a b m1 m2 P) (hQ : Interp Cc c a b m2 m1 Q)
    {x : ℝ} (hx1 : a < x) (hx2 : x < b) :
    (Cc / (x + c) - P.eval x) = (-1 : ℝ) ^ (m1 - m2) * (Cc / (x + c) - Q.eval x)
      ↔ x = Mc a b c := by
  have hb : 0 < b := lt_trans ha hab
  have hxc : (0:ℝ) < x + c := by linarith
  have hA : (0:ℝ) < x - a := by linarith
  have hB : (0:ℝ) < b - x := by linarith
  have hU : (0:ℝ) < c + a := by linarith
  have hV : (0:ℝ) < c + b := by linarith
  have hWP := W_eval_neg_c_ne a b c ha hb hc m1 m2
  have hWQ := W_eval_neg_c_ne a b c ha hb hc m2 m1
  have hm1 : 1 ≤ m1 - m2 := by omega
  have hk1 : m1 + 1 = (m2 + 1) + (m1 - m2) := by omega
  -- the two interpolation identities, evaluated at `x`
  have hPi := congrArg (Polynomial.eval x) (interp_eq ha hb hc hP)
  have hQi := congrArg (Polynomial.eval x) (interp_eq ha hb hc hQ)
  simp only [eval_sub, eval_C, eval_mul, eval_add, eval_X, W_eval] at hPi hQi
  simp only [W_eval] at hWP hWQ
  -- clearing the denominator `x + c`
  have hEP : (x + c) * (Cc / (x + c) - P.eval x) = Cc - (x + c) * P.eval x := by
    field_simp
  have hEQ : (x + c) * (Cc / (x + c) - Q.eval x) = Cc - (x + c) * Q.eval x := by
    field_simp
  have hiff : ((Cc / (x + c) - P.eval x)
        = (-1 : ℝ) ^ (m1 - m2) * (Cc / (x + c) - Q.eval x))
      ↔ (Cc - (x + c) * P.eval x
        = (-1 : ℝ) ^ (m1 - m2) * (Cc - (x + c) * Q.eval x)) := by
    constructor
    · intro h
      rw [← hEP, ← hEQ, h]; ring
    · intro h
      rw [← hEP, ← hEQ] at h
      exact mul_left_cancel₀ (ne_of_gt hxc) (by linear_combination h)
  have hxb : x - b = -(b - x) := by ring
  have hca : (-c) - a = -(c + a) := by ring
  have hcb : (-c) - b = -(c + b) := by ring
  rw [hca, hcb, hk1] at hWP hWQ
  rw [hiff, hPi, hQi, hxb, hca, hcb, hk1]
  rw [div_reduce hCc hWP hWQ, sign_reduce hA hB hU hV (m2 + 1) (m1 - m2)]
  exact mean_char ha hc hx1 hx2 hm1

/-- **Conjecture 23 is FALSE.**  `f(x) = 1/(x+1)` — the case `C = 1`, `c = 1` — has a mean
independent of both interpolation orders, namely `(2ab + a + b)/(a + b + 2)`, yet is not of
the form `C/x`: the latter would force `C = 1/2` from `f(1)` and `C = 2/3` from `f(2)`. -/
theorem not_conj :
    (∀ (a b : ℝ), 0 < a → a < b → ∀ (m1 m2 : ℕ), m2 < m1 →
        ∀ (P Q : Polynomial ℝ), Interp 1 1 a b m1 m2 P → Interp 1 1 a b m2 m1 Q →
          ∀ x : ℝ, a < x → x < b →
            ((1 / (x + 1) - P.eval x) = (-1 : ℝ) ^ (m1 - m2) * (1 / (x + 1) - Q.eval x)
              ↔ x = Mc a b 1))
    ∧ ¬ ∃ Cc : ℝ, (1 : ℝ) / (1 + 1) = Cc / 1 ∧ (1 : ℝ) / (2 + 1) = Cc / 2 := by
  constructor
  · intro a b ha hab m1 m2 hm P Q hP hQ x hx1 hx2
    exact mean_unique ha hab (by norm_num) (by norm_num : (1:ℝ) ≠ 0) hm hP hQ hx1 hx2
  · rintro ⟨Cc, h1, h2⟩
    rw [div_one] at h1
    norm_num at h1 h2
    rw [← h1] at h2
    norm_num at h2

section Existence

/-! ### The interpolant EXISTS — so `not_conj`'s first conjunct says something

`not_conj` is a conjunction: the mean of `f(x) = 1/(x+1)` is independent of the interpolation
orders (a statement universally quantified over `P`, `Q` satisfying `Interp`), and `f` is not of
the form `C/x` (a concrete arithmetic refutation).  **The second conjunct is unconditional, but
the first is vacuous unless interpolants exist**, and nothing produced one: `Interp` appeared
only as a hypothesis.  A counterexample whose defining property holds vacuously exhibits nothing.

The interpolant is explicit rather than abstract.  `interp_eq` already shows that any `P`
satisfying `Interp` obeys `C·Cc − (X+c)·P = (Cc / W(−c))·W`; reading that backwards names the
candidate, and the only thing to check is that the division is exact — which it is, because the
numerator vanishes at `−c` exactly when `W(−c) ≠ 0`, and that is `W_eval_neg_c_ne`.  So the
existence proof needs no coprimality or Bezout machinery, only `dvd_iff_isRoot`.
-/

/-- **`Interp` is satisfiable**: for every admissible parameter set there IS an interpolant.
Without this, `not_conj`'s first conjunct would be vacuously true. -/
theorem exists_interp (Cc c a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (m1 m2 : ℕ) :
    ∃ P : Polynomial ℝ, Interp Cc c a b m1 m2 P := by
  have hWc : (W a b m1 m2).eval (-c) ≠ 0 := W_eval_neg_c_ne a b c ha hb hc m1 m2
  have hroot : (Polynomial.C Cc
      - Polynomial.C (Cc / (W a b m1 m2).eval (-c)) * W a b m1 m2).IsRoot (-c) := by
    simp only [Polynomial.IsRoot.def, eval_sub, eval_mul, eval_C]
    field_simp
    ring
  obtain ⟨P, hP⟩ := dvd_iff_isRoot.mpr hroot
  have hXc : (X - Polynomial.C (-c) : Polynomial ℝ) = X + Polynomial.C c := by
    rw [map_neg]
    ring
  rw [hXc] at hP
  refine ⟨P, ?_, ?_⟩
  · by_cases hP0 : P = 0
    · rw [hP0]
      simp
    · have hx0 : (X + Polynomial.C c : Polynomial ℝ) ≠ 0 := by
        rw [← hXc]
        exact X_sub_C_ne_zero _
      have hnd : (Polynomial.C Cc
          - Polynomial.C (Cc / (W a b m1 m2).eval (-c)) * W a b m1 m2).natDegree
          = 1 + P.natDegree := by
        rw [hP, natDegree_mul hx0 hP0, ← hXc, natDegree_X_sub_C]
      have hNle : (Polynomial.C Cc
          - Polynomial.C (Cc / (W a b m1 m2).eval (-c)) * W a b m1 m2).natDegree
          ≤ m1 + m2 + 2 := by
        refine le_trans (natDegree_sub_le _ _) ?_
        refine max_le ?_ ?_
        · simp
        · refine le_trans (natDegree_C_mul_le _ _) ?_
          rw [W_natDegree]
      have hPle : P.natDegree ≤ m1 + m2 + 1 := by omega
      exact natDegree_le_iff_degree_le.mp hPle
  · refine ⟨Polynomial.C (Cc / (W a b m1 m2).eval (-c)), ?_⟩
    have hkey : Polynomial.C Cc - (X + Polynomial.C c) * P
        = Polynomial.C (Cc / (W a b m1 m2).eval (-c)) * W a b m1 m2 := by
      rw [← hP]
      ring
    rw [hkey]
    ring

end Existence

end Principia.MathDB.P316888
