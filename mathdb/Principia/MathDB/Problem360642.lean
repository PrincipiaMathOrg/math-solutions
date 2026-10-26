import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Principia.Common.NegBinomTrunc

/-!
# MathDB #360642 -- Hilbert coefficients of the square of the maximal ideal

Write-up `mathdb-open-problems/problems/360642/solution.tex`,
*Hilbert coefficients of the square of the maximal ideal*, 22 September 2026.
Source: R. Froberg, *Hilbert coefficients of quadratic algebras*, arXiv:2311.02860v1,
Conjecture 3, p. 5; published as *J. Exp. Math.* 1(2) (2025) 315--321, Conjecture 3.1, p. 319.

With `S_n = k[x_1,...,x_n]` and `I = (x_1,...,x_n)^2`, the source's defining convention is

  `l(S_n/I^s) = sum_{j=0}^{n} (-1)^j e_j(I) * C(s+n-j-1, n-j)`   for `s >> 0`,   (1)

and the conjecture is `e_j(I) = 2^(n-2j) C(n-j, j)` for `2j <= n`, and `0` beyond.   (2)

**What is proved here.**  `conj_holds` : the coefficients `e n j` of (2) satisfy (1) for every
`n` and every `s >= 1` -- this is the write-up's identity (3),

  `C(2s+n-1, n) = sum_j (-1)^j 2^(n-2j) C(n-j, j) C(s+n-j-1, n-j)`.

`e_unique` : (1) has at most one solution, so (2) is not merely *a* family of coefficients
satisfying (1) but *the* Hilbert coefficients.  Its hypothesis is (1) `for all s >= s0` with
`s0` arbitrary, which is the source's own `s >> 0` reading, not the stronger `s >= 1`.
`e_pos` and `e_eq_zero` are the source's "strictly positive, then zero" clause.
`conj_half_range` restates (1)+(2) as the source's own display, summed to `floor(n/2)`.
`uncorrected_fails` certifies the source's index correction: with the published upper entry
`s+n-j` the identity already fails at `n = 1, s = 5` (it reads `2s = 2s+2`).

**The proof** is the write-up's generating-function argument made finite.  `1 - u = (1 - X)^2`
for `u = X(2 - X)`, so the truncated negative-binomial series in `u` at exponent `s` and the
one in `X` at exponent `2s` are truncated inverses of the SAME polynomial `(1-X)^{2s}`.  The
truncation identity `P334350.trunc` gives each of them an exact remainder, and multiplying the
two relations crosswise shows the two truncations differ by a multiple of `X^{n+1}` (`key`) --
no power series, no units, no division.  Comparing the `X^n` coefficients then IS (3).

**The one modelling step.**  `len n s` is *defined* as `C(2s+n-1, n)`.  That is the source's
own stars-and-bars count -- the monomials of total degree `< 2s` form a basis of `S_n/I^s` --
and it is taken here as the model rather than re-derived from commutative algebra, which would
need a monomial basis for `S_n/I^s` and a count of `Finsupp`s of bounded degree.  Everything
downstream of (1) is proved.

**Imported.**  `U` and `trunc` now live in `Principia.Common.NegBinomTrunc`, promoted there on 2026-09-22; the
truncated negative-binomial series was built.  Both are campaign-agnostic (they mention
nothing of either problem) and belong in `Principia/Common/`; the promotion is deliberately
NOT bundled with this module, since it would touch a 95-declaration verified artifact and two
gates.  Recorded as a follow-up in the campaign README.

Values checked first in `Campaigns/MathDB-Formalization/verify_360642.py`.
-/

namespace Principia.MathDB.P360642

open Polynomial Finset
open Principia.Common (U trunc)

noncomputable section

/-- `u = X(2 - X)`, the substitution behind `1 - u = (1 - X)^2`. -/
def u : Polynomial ℤ := X * (2 - X)

theorem one_sub_u : 1 - u = (1 - X) ^ 2 := by
  rw [u]; ring

theorem coeff_two_sub_X_pow (p k : ℕ) :
    (((2 : Polynomial ℤ) - X) ^ p).coeff k = (-1) ^ k * 2 ^ (p - k) * (p.choose k : ℤ) := by
  have hC : (C (-2 : ℤ)) = -2 := by simp
  have h2 : ((2 : Polynomial ℤ) - X) = -(X + C (-2 : ℤ)) := by rw [hC]; ring
  have hneg : ((-1 : Polynomial ℤ)) ^ p = C ((-1 : ℤ) ^ p) := by
    rw [map_pow, map_neg, map_one]
  rw [h2, neg_pow, hneg, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rcases le_or_gt k p with hk | hk
  · obtain ⟨t, rfl⟩ : ∃ t, p = k + t := ⟨p - k, by omega⟩
    rw [show k + t - k = t from by omega]
    have hs : ((-2 : ℤ)) ^ t = (-1) ^ t * 2 ^ t := by
      rw [← neg_pow]
    have hp : ((-1 : ℤ)) ^ (k + t) = (-1) ^ k * (-1) ^ t := by rw [pow_add]
    have hsq : ((-1 : ℤ)) ^ t * (-1) ^ t = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hs, hp]
    linear_combination ((-1 : ℤ) ^ k * 2 ^ t * (((k + t).choose k : ℕ) : ℤ)) * hsq
  · rw [Nat.choose_eq_zero_of_lt hk]
    push_cast
    ring

/-- The `X^n` coefficient of the truncation in `X` itself: one surviving term. -/
theorem coeff_U_X (d n : ℕ) :
    (U (X : Polynomial ℤ) d (n + 1)).coeff n = ((d + n).choose n : ℤ) := by
  have h : ∀ p ∈ Finset.range (n + 1),
      (((d + p).choose p : Polynomial ℤ) * X ^ p).coeff n
        = if p = n then ((d + p).choose p : ℤ) else 0 := by
    intro p _
    rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hp : p = n
    · subst hp; simp
    · rw [if_neg (fun h => hp h.symm), if_neg hp, mul_zero]
  rw [U, Polynomial.finsetSum_coeff, Finset.sum_congr rfl h, Finset.sum_ite_eq' _ n _]
  simp

/-- The `X^n` coefficient of the truncation in `u`, term by term. -/
theorem coeff_U_u (m n : ℕ) :
    (U u m (n + 1)).coeff n
      = ∑ p ∈ Finset.range (n + 1),
          ((m + p).choose p : ℤ)
            * ((-1) ^ (n - p) * 2 ^ (p - (n - p)) * (p.choose (n - p) : ℤ)) := by
  rw [U, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpn : p ≤ n := by have := Finset.mem_range.mp hp; omega
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul, u, mul_pow,
    Polynomial.coeff_X_pow_mul', if_pos hpn, coeff_two_sub_X_pow]

/-- The same coefficient, reindexed by `j = n - p`: the write-up's summation. -/
theorem coeff_U_u' (m n : ℕ) :
    (U u m (n + 1)).coeff n
      = ∑ j ∈ Finset.range (n + 1),
          (-1) ^ j * 2 ^ (n - 2 * j) * ((n - j).choose j : ℤ)
            * ((m + (n - j)).choose (n - j) : ℤ) := by
  rw [coeff_U_u, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show n + 1 - 1 - j = n - j from by omega, show n - (n - j) = j from by omega,
    show n - j - j = n - 2 * j from by omega]
  ring

/-- The two truncations differ by a multiple of `X^{n+1}`.  This is the whole cancellation:
`(1-u)^s = (1-X)^{2s}`, so both are truncated inverses of the SAME polynomial. -/
theorem key (m n : ℕ) :
    U u m (n + 1) - U (X : Polynomial ℤ) (2 * m + 1) (n + 1)
      = (U (1 - X) n (2 * m + 1 + 1) * U u m (n + 1)
          - ((2 - X) ^ (n + 1) * U (1 - u) n (m + 1))
              * U (X : Polynomial ℤ) (2 * m + 1) (n + 1))
        * X ^ (n + 1) := by
  have h1 := trunc u n m
  have h2 := trunc (X : Polynomial ℤ) n (2 * m + 1)
  have hu : (1 - u) ^ (m + 1) = (1 - X) ^ (2 * m + 1 + 1) := by
    rw [one_sub_u, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 from by omega]
  have hup : u ^ (n + 1) = X ^ (n + 1) * (2 - X) ^ (n + 1) := by
    rw [u, mul_pow]
  rw [hu, hup] at h1
  linear_combination (U (X : Polynomial ℤ) (2 * m + 1) (n + 1)) * h1 - (U u m (n + 1)) * h2

theorem coeff_eq (m n : ℕ) :
    (U u m (n + 1)).coeff n = (U (X : Polynomial ℤ) (2 * m + 1) (n + 1)).coeff n := by
  have h := congrArg (fun q : Polynomial ℤ => q.coeff n) (key m n)
  have hlt : ¬ (n + 1 ≤ n) := by omega
  simp only [Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', if_neg hlt] at h
  linarith [h]

/-- **The write-up's identity (3)**, for every `n` and every `s = m+1 ≥ 1`. -/
theorem main_ident (m n : ℕ) :
    ((2 * m + 1 + n).choose n : ℤ)
      = ∑ j ∈ Finset.range (n + 1),
          (-1) ^ j * 2 ^ (n - 2 * j) * ((n - j).choose j : ℤ)
            * ((m + (n - j)).choose (n - j) : ℤ) := by
  rw [← coeff_U_u', coeff_eq, coeff_U_X]

end

/-- `ℓ(S_n/I^s)` in the source's convention: the monomials of total degree `< 2s` in `n`
variables form a basis, so stars and bars gives this count.  That classical length step is
the source's own, and is taken here as the model. -/
def len (n s : ℕ) : ℕ := (2 * s + n - 1).choose n

/-- The claimed Hilbert coefficients (2). -/
def e (n j : ℕ) : ℤ := if 2 * j ≤ n then 2 ^ (n - 2 * j) * ((n - j).choose j : ℤ) else 0

/-- Froberg's Conjecture 3 (published 3.1), in the source's CORRECTED convention (1). -/
def Conj (n : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s →
    (len n s : ℤ)
      = ∑ j ∈ Finset.range (n + 1), (-1) ^ j * e n j * ((s + (n - j) - 1).choose (n - j) : ℤ)

/-- **The conjecture, for every dimension `n`.** -/
theorem conj_holds (n : ℕ) : Conj n := by
  intro s hs
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hlen : len n (m + 1) = (2 * m + 1 + n).choose n := by
    rw [len]; congr 1; omega
  rw [hlen, main_ident m n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show m + 1 + (n - j) - 1 = m + (n - j) from by omega, e]
  by_cases h2 : 2 * j ≤ n
  · rw [if_pos h2]; ring
  · rw [if_neg h2, Nat.choose_eq_zero_of_lt (by omega : n - j < j)]
    push_cast
    ring

/-- The nonzero coefficients are strictly positive. -/
theorem e_pos (n j : ℕ) (h : 2 * j ≤ n) : 0 < e n j := by
  rw [e, if_pos h]
  have hc : 0 < (n - j).choose j := Nat.choose_pos (by omega)
  have : (0 : ℤ) < ((n - j).choose j : ℤ) := by exact_mod_cast hc
  positivity

/-- Beyond `⌊n/2⌋` the coefficients vanish. -/
theorem e_eq_zero (n j : ℕ) (h : n < 2 * j) : e n j = 0 := by
  rw [e, if_neg (by omega)]

/-- The source's own display (3): the sum truncated at `⌊n/2⌋`. -/
theorem conj_half_range (n s : ℕ) (hs : 1 ≤ s) :
    (len n s : ℤ)
      = ∑ j ∈ Finset.range (n / 2 + 1),
          (-1) ^ j * (2 ^ (n - 2 * j) * ((n - j).choose j : ℤ))
            * ((s + (n - j) - 1).choose (n - j) : ℤ) := by
  have hsub : Finset.range (n / 2 + 1) ⊆ Finset.range (n + 1) := by
    intro j hj
    have := Finset.mem_range.mp hj
    exact Finset.mem_range.mpr (by omega)
  have h1 : ∑ j ∈ Finset.range (n / 2 + 1),
      (-1 : ℤ) ^ j * e n j * ((s + (n - j) - 1).choose (n - j) : ℤ)
      = ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * e n j * ((s + (n - j) - 1).choose (n - j) : ℤ) := by
    refine Finset.sum_subset hsub fun j hj hj' => ?_
    have ha := Finset.mem_range.mp hj
    have hb : ¬ (j < n / 2 + 1) := fun h => hj' (Finset.mem_range.mpr h)
    rw [e_eq_zero n j (by omega), mul_zero, zero_mul]
  rw [conj_holds n s hs, ← h1]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [e, if_pos (by omega)]

/-! ### The representation (1) determines the coefficients

The source's convention (1) DEFINES `e_j(I)`, so (2) says something only if (1) has at most
one solution.  The write-up gets that from distinct degrees; here it is the forward difference
`C(m+d+1,d) - C(m+d,d) = C(m+d,d-1)`, which walks the basis down one degree at a time.
-/

/-- `bas d m = C(m+d, d)`: the source's degree-`d` basis polynomial `C(s+d-1,d)` at `s = m+1`. -/
def bas (d m : ℕ) : ℤ := ((m + d).choose d : ℤ)

theorem bas_zero (m : ℕ) : bas 0 m = 1 := by simp [bas]

/-- The forward difference drops the degree by one. -/
theorem bas_diff (d m : ℕ) : bas (d + 1) (m + 1) - bas (d + 1) m = bas d (m + 1) := by
  simp only [bas]
  rw [show m + 1 + (d + 1) = (m + d + 1) + 1 from by omega,
    show m + (d + 1) = m + d + 1 from by omega,
    show m + 1 + d = m + d + 1 from by omega,
    Nat.choose_succ_succ (m + d + 1) d]
  push_cast
  ring

/-- **Uniqueness**: a vanishing combination of the basis has vanishing coefficients. -/
theorem coeff_unique : ∀ (n : ℕ) (c : ℕ → ℤ) (t : ℕ),
    (∀ m, t ≤ m → (∑ d ∈ Finset.range (n + 1), c d * bas d m) = 0) →
    ∀ d, d ≤ n → c d = 0 := by
  intro n
  induction n with
  | zero =>
      intro c t h d hd
      have h0 := h t le_rfl
      rw [Finset.sum_range_one, bas_zero, mul_one] at h0
      have : d = 0 := by omega
      subst this
      exact h0
  | succ n ih =>
      intro c t h d hd
      have hstep : ∀ m, t + 1 ≤ m →
          (∑ i ∈ Finset.range (n + 1), c (i + 1) * bas i m) = 0 := by
        intro m hm
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have ha := h (m' + 1) (by omega)
        have hb := h m' (by omega)
        have hd2 : (∑ i ∈ Finset.range (n + 1 + 1), c i * bas i (m' + 1))
            - (∑ i ∈ Finset.range (n + 1 + 1), c i * bas i m') = 0 := by
          rw [ha, hb]; ring
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ'] at hd2
        rw [bas_zero, bas_zero] at hd2
        have hcong : (∑ i ∈ Finset.range (n + 1),
            (c (i + 1) * bas (i + 1) (m' + 1) - c (i + 1) * bas (i + 1) m'))
            = ∑ i ∈ Finset.range (n + 1), c (i + 1) * bas i (m' + 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_sub, bas_diff]
        rw [hcong] at hd2
        linarith [hd2]
      have hrec := ih (fun d => c (d + 1)) (t + 1) hstep
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · have h0 := h t le_rfl
        rw [Finset.sum_range_succ', bas_zero, mul_one] at h0
        have hz : (∑ i ∈ Finset.range (n + 1), c (i + 1) * bas (i + 1) t) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have := Finset.mem_range.mp hi
          rw [hrec i (by omega), zero_mul]
        rw [hz] at h0
        linarith [h0]
      · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        exact hrec d' (by omega)

/-- **The Hilbert coefficients are exactly (2)** -- any family satisfying the source's
defining convention (1) agrees with `e` in every index `j ≤ n`. -/
theorem e_unique (n s0 : ℕ) (a : ℕ → ℤ)
    (ha : ∀ s : ℕ, s0 ≤ s → 1 ≤ s → (len n s : ℤ)
      = ∑ j ∈ Finset.range (n + 1), (-1) ^ j * a j * ((s + (n - j) - 1).choose (n - j) : ℤ)) :
    ∀ j, j ≤ n → a j = e n j := by
  have hzero : ∀ m : ℕ, s0 ≤ m → (∑ d ∈ Finset.range (n + 1),
      ((-1) ^ (n - d) * (a (n - d) - e n (n - d))) * bas d m) = 0 := by
    intro m hm
    have h1 := ha (m + 1) (by omega) (by omega)
    have h2 := conj_holds n (m + 1) (by omega)
    have hre := Finset.sum_range_reflect
      (fun j => (-1 : ℤ) ^ j * (a j - e n j) * bas (n - j) m) (n + 1)
    have hL : (∑ d ∈ Finset.range (n + 1),
        ((-1 : ℤ)) ^ (n - d) * (a (n - d) - e n (n - d)) * bas d m)
        = ∑ d ∈ Finset.range (n + 1),
          ((-1 : ℤ)) ^ (n + 1 - 1 - d) * (a (n + 1 - 1 - d) - e n (n + 1 - 1 - d))
            * bas (n - (n + 1 - 1 - d)) m := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have := Finset.mem_range.mp hd
      rw [show n + 1 - 1 - d = n - d from by omega, show n - (n - d) = d from by omega]
    rw [hL, hre]
    have hR : (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℤ)) ^ j * (a j - e n j) * bas (n - j) m)
        = (∑ j ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ j * a j * ((m + 1 + (n - j) - 1).choose (n - j) : ℤ))
          - ∑ j ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ j * e n j * ((m + 1 + (n - j) - 1).choose (n - j) : ℤ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.mp hj
      rw [show m + 1 + (n - j) - 1 = m + (n - j) from by omega, bas]
      ring
    rw [hR, ← h1, ← h2]
    ring
  intro j hj
  have hc := coeff_unique n _ s0 (fun m hm => hzero m hm) (n - j) (by omega)
  rw [show n - (n - j) = j from by omega] at hc
  rcases mul_eq_zero.mp hc with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · linarith [h]

/-- The index correction is real: with the published upper entry `s+n-j` the identity
already fails at `n = 1, s = 5`, where it reads `2s = 2s+2`. -/
theorem uncorrected_fails :
    (len 1 5 : ℤ)
      ≠ ∑ j ∈ Finset.range 2, (-1) ^ j * e 1 j * ((5 + (1 - j)).choose (1 - j) : ℤ) := by
  norm_num [len, e, Finset.sum_range_succ]

end Principia.MathDB.P360642
