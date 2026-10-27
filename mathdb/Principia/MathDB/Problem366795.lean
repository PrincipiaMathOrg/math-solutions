import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# MathDB #366795 — Rowland–Sistos Barrón Conjecture 5.3 (particular ranks) is FALSE

Write-up: `mathdb-open-problems/problems/366795/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-29 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: E. Rowland and J. Sistos Barrón, *Complexity of powers of a constant-recursive sequence*,
arXiv:2501.14643v1, **Conjecture 5.3** (p. 15), whose *particular*-rank half predicts that
`M ↦ rank ((s n ^ M)_n)` is eventually **quasipolynomial**.

The counterexample is the write-up's own: the rank-eight integer sequence

`s n = 1 + 2^n + 3^n - 6^n + n·27^n + n·54^n`

whose power ranks satisfy, for every `M ≥ 5`,

`R M = (M+1)(3M² + 3M + 2)/2 - 3(M-1)·[2 ∣ M] - 6(M-2)·[M is a square]`,

and the correction term supported **exactly on the perfect squares** is what kills
quasipolynomiality.

## What this module proves, and where the line falls

**Proved here, unconditionally and with no hypotheses at all:** the formula's own function
`Rformula` is not eventually quasipolynomial (`not_evQuasipoly_Rformula`), hence so is any
power-rank sequence agreeing with it from `M = 5` on (`conjecture_5_3_particular_false`). Also
proved: `s` really does satisfy the order-eight integer recurrence with characteristic polynomial
`(z-1)(z-2)(z-3)(z-6)(z-27)²(z-54)²` (`s_recurrence`), that polynomial has degree `8`
(`charPoly_natDegree`) and nonzero constant term `76527504` (`charPoly_coeff_zero`) — i.e. **`s`
meets the source's hypotheses**, which is not a side remark but the reason the counterexample is
admissible.

**Not proved here, and named rather than hidden:** the rank formula itself, i.e. that `R M` *is*
the right-hand side. That computation runs through the rank of an exponential polynomial and a
vanishing analysis of Krawtchouk coefficients, and **Mathlib has no notion of the rank (minimal
eventual recurrence order) of a constant-recursive sequence at all** — `LinearRecurrence` carries
no minimality theory. So the rank formula enters `conjecture_5_3_particular_false` as a named
hypothesis `hR`, per the project's spine rule; the residue is written out at the foot of this file
as a work-list, with the constants that stage will need.

The point of the split is that **the refutation mechanism is the part that is fully formal**: given
the formula, no quasipolynomial can agree with it, and that is proved here with no `sorry` and no
carried assumption.

## The mechanism, in one paragraph

`EvQuasipoly` is closed under subtraction (`EvQuasipoly.sub`, via the product period and
`Nat.mod_mod_of_dvd`), the polynomial part is quasipolynomial with period `1` and the parity part
with period `2`. So a quasipolynomial `R` would make the square-indicator term quasipolynomial, and
that is impossible for a reason needing no analysis: on the residue class `0 mod p`, the constituent
polynomial vanishes at every `(pt)² + p`, since `p ∣ (pt)² + p` and `(pt)² < (pt)² + p < (pt+1)²`
makes it a **nonsquare**; those points are infinitely many, so the polynomial is zero
(`Polynomial.eq_zero_of_infinite_isRoot`); yet on the same class it must take the nonzero value
`6((pt)² - 2)` at the squares `(pt)²`.

`EvQuasipoly` and its four closure lemmas mention nothing about this problem and are promotion
candidates for `Principia/Common/`.
-/

namespace Principia.MathDB.P366795

open Polynomial

/-! ## Eventual quasipolynomiality -/

/-- `f` is **eventually quasipolynomial**: for some period `p > 0` there are polynomials
`P 0, …, P (p-1)` with `f M = (P (M % p)).eval M` for every large `M`.

This is the write-up's reading of the source's "pseudo-polynomial", made explicit: the source
motivates the term with periodic-cancellation examples and never defines it separately. -/
def EvQuasipoly (f : ℕ → ℚ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∃ P : ℕ → ℚ[X], ∃ N : ℕ,
    ∀ M : ℕ, N ≤ M → f M = (P (M % p)).eval (M : ℚ)

/-- Eventual quasipolynomiality only sees large arguments, so it transfers along an eventual
equality. -/
theorem EvQuasipoly.congr {f g : ℕ → ℚ} (hf : EvQuasipoly f) (N₀ : ℕ)
    (h : ∀ M : ℕ, N₀ ≤ M → f M = g M) : EvQuasipoly g := by
  obtain ⟨p, hp, P, N, hPN⟩ := hf
  refine ⟨p, hp, P, max N N₀, fun M hM => ?_⟩
  rw [← h M (le_trans (le_max_right N N₀) hM)]
  exact hPN M (le_trans (le_max_left N N₀) hM)

/-- **Closure under subtraction**, on the product period. This is the step that lets the polynomial
and parity parts of the rank formula be peeled off. -/
theorem EvQuasipoly.sub {f g : ℕ → ℚ} (hf : EvQuasipoly f) (hg : EvQuasipoly g) :
    EvQuasipoly (fun M => f M - g M) := by
  obtain ⟨p, hp, P, N, hP⟩ := hf
  obtain ⟨q, hq, Q, N', hQ⟩ := hg
  refine ⟨p * q, Nat.mul_pos hp hq, fun a => P (a % p) - Q (a % q), max N N', fun M hM => ?_⟩
  have h1 : M % (p * q) % p = M % p := Nat.mod_mod_of_dvd M ⟨q, rfl⟩
  have h2 : M % (p * q) % q = M % q := Nat.mod_mod_of_dvd M ⟨p, mul_comm p q⟩
  simp only [h1, h2, Polynomial.eval_sub]
  rw [hP M (le_trans (le_max_left N N') hM), hQ M (le_trans (le_max_right N N') hM)]

/-- A polynomial function is quasipolynomial, with period `1`. -/
theorem evQuasipoly_of_poly (P : ℚ[X]) : EvQuasipoly (fun M => P.eval (M : ℚ)) :=
  ⟨1, one_pos, fun _ => P, 0, fun _ _ => rfl⟩

/-- The rank formula's parity term is quasipolynomial, with period `2`. -/
theorem evQuasipoly_parity :
    EvQuasipoly (fun M : ℕ => 3 * ((M : ℚ) - 1) * (if 2 ∣ M then 1 else 0)) := by
  refine ⟨2, two_pos, fun a => if a = 0 then 3 * (X - 1) else 0, 0, fun M _ => ?_⟩
  by_cases h : 2 ∣ M
  · have hm : M % 2 = 0 := by omega
    simp [h, hm]
  · have hm : M % 2 = 1 := by omega
    simp [h, hm]

/-! ## The indicator of the perfect squares -/

/-- `1` at the perfect squares and `0` elsewhere, via `Nat.sqrt` so that it is decidable. -/
def sqInd (M : ℕ) : ℚ := if Nat.sqrt M * Nat.sqrt M = M then 1 else 0

theorem sqrt_mul_self_iff (M : ℕ) : Nat.sqrt M * Nat.sqrt M = M ↔ IsSquare M := by
  rw [← Nat.exists_mul_self]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

theorem sqInd_eq_zero {M : ℕ} (h : ¬ IsSquare M) : sqInd M = 0 := by
  rw [sqInd, if_neg]
  exact fun hc => h ((sqrt_mul_self_iff M).mp hc)

theorem sqInd_eq_one {M : ℕ} (h : IsSquare M) : sqInd M = 1 := by
  rw [sqInd, if_pos ((sqrt_mul_self_iff M).mpr h)]

/-- The rank formula's square-supported correction term, named rather than written as a lambda so
that `EvQuasipoly` applications reduce without a beta step. -/
def Dsq (M : ℕ) : ℚ := 6 * ((M : ℚ) - 2) * sqInd M

/-- `(pt)² + p` is **not** a perfect square once `t ≥ 1`: it is squeezed strictly between the
consecutive squares `(pt)²` and `(pt+1)²`, because `p ≤ pt < 2pt + 1`. -/
theorem not_isSquare_sq_add (p t : ℕ) (hp : 0 < p) (ht : 1 ≤ t) :
    ¬ IsSquare ((p * t) ^ 2 + p) := by
  rintro ⟨k, hk⟩
  have hm : p ≤ p * t := Nat.le_mul_of_pos_right p ht
  have h1 : p * t < k := by
    by_contra hc
    rw [not_lt] at hc
    have hle : k * k ≤ p * t * (p * t) := Nat.mul_le_mul hc hc
    nlinarith
  have h2 : k < p * t + 1 := by
    by_contra hc
    rw [not_lt] at hc
    have hle : (p * t + 1) * (p * t + 1) ≤ k * k := Nat.mul_le_mul hc hc
    nlinarith
  omega

/-- **The mechanism.** A correction term supported exactly on the perfect squares is not eventually
quasipolynomial. -/
theorem not_evQuasipoly_Dsq : ¬ EvQuasipoly Dsq := by
  rintro ⟨p, hp, P, N, hP⟩
  have hmod : ∀ t : ℕ, ((p * t) ^ 2 + p) % p = 0 := by
    intro t
    have he : (p * t) ^ 2 + p = p * (p * t ^ 2 + 1) := by ring
    rw [he, Nat.mul_mod_right]
  -- every `(pt)² + p` beyond `N` is a root of the class-`0` polynomial
  have hzero : ∀ t : ℕ, 1 ≤ t → N ≤ (p * t) ^ 2 + p →
      (P 0).eval (((p * t) ^ 2 + p : ℕ) : ℚ) = 0 := by
    intro t ht hN
    have h := hP ((p * t) ^ 2 + p) hN
    rw [hmod t] at h
    rw [← h]
    simp only [Dsq, sqInd_eq_zero (not_isSquare_sq_add p t hp ht), mul_zero]
  -- there are infinitely many of them, so that polynomial is zero
  have hQ : P 0 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hsm : StrictMono (fun t : ℕ => (p * (t + N + 1)) ^ 2 + p) := by
      intro a b hab
      have h1 : p * (a + N + 1) < p * (b + N + 1) :=
        mul_lt_mul_of_pos_left (by omega) hp
      exact Nat.add_lt_add_right (Nat.pow_lt_pow_left h1 two_ne_zero) p
    refine Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => (((p * (t + N + 1)) ^ 2 + p : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      exact hsm.injective (Nat.cast_injective hab)
    · intro t
      have hle : t + N + 1 ≤ p * (t + N + 1) := Nat.le_mul_of_pos_left _ hp
      exact hzero (t + N + 1) (by omega) (by nlinarith)
  -- but on the same residue class it must be nonzero at a square
  set M : ℕ := (p * (N + 3)) ^ 2 with hMdef
  have hle : N + 3 ≤ p * (N + 3) := Nat.le_mul_of_pos_left _ hp
  have hMN : N ≤ M := by rw [hMdef]; nlinarith
  have hM9 : 9 ≤ M := by rw [hMdef]; nlinarith
  have hMmod : M % p = 0 := by
    have he : M = p * (p * (N + 3) ^ 2) := by rw [hMdef]; ring
    rw [he, Nat.mul_mod_right]
  have hsq : IsSquare M := ⟨p * (N + 3), by rw [hMdef]; ring⟩
  have h := hP M hMN
  rw [hMmod, hQ, Polynomial.eval_zero] at h
  rw [Dsq, sqInd_eq_one hsq, mul_one] at h
  have h9 : (9 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM9
  linarith

/-! ## The rank formula and the refutation -/

/-- The write-up's rank formula (its equation (4)) for the power ranks of `s`, as a function of the
exponent `M`. Valid, per the write-up, for every `M ≥ 5`. -/
def Rformula (M : ℕ) : ℚ :=
  ((M : ℚ) + 1) * (3 * (M : ℚ) ^ 2 + 3 * (M : ℚ) + 2) / 2
    - 3 * ((M : ℚ) - 1) * (if 2 ∣ M then 1 else 0)
    - 6 * ((M : ℚ) - 2) * sqInd M

theorem not_evQuasipoly_Rformula : ¬ EvQuasipoly Rformula := by
  intro hR
  apply not_evQuasipoly_Dsq
  have hpoly : EvQuasipoly (fun M : ℕ => ((M : ℚ) + 1) * (3 * (M : ℚ) ^ 2 + 3 * (M : ℚ) + 2) / 2) :=
    by
      have := evQuasipoly_of_poly ((X + 1) * (3 * X ^ 2 + 3 * X + 2) * C (1 / 2 : ℚ))
      refine this.congr 0 (fun M _ => ?_)
      simp
      ring
  refine ((hpoly.sub evQuasipoly_parity).sub hR).congr 0 (fun M _ => ?_)
  simp only [Rformula, Dsq]
  ring

/-- **Rowland–Sistos Barrón Conjecture 5.3 fails for particular ranks.** Any function agreeing with
the write-up's rank formula from `M = 5` on is not eventually quasipolynomial.

`R` is intended as `M ↦ rank ((s n ^ M)_n)`; the hypothesis `hR` is exactly the rank computation,
which is the part Mathlib cannot currently express (see the residue at the foot of this file). -/
theorem conjecture_5_3_particular_false (R : ℕ → ℚ)
    (hR : ∀ M : ℕ, 5 ≤ M → R M = Rformula M) : ¬ EvQuasipoly R := by
  intro h
  exact not_evQuasipoly_Rformula (h.congr 5 hR)

/-! ## The counterexample sequence meets the source's hypotheses -/

/-- The write-up's rank-eight integer sequence. -/
def s (n : ℕ) : ℤ := 1 + 2 ^ n + 3 ^ n - 6 ^ n + (n : ℤ) * 27 ^ n + (n : ℤ) * 54 ^ n

/-- The minimal characteristic polynomial of `s`. -/
noncomputable def charPoly : ℤ[X] :=
  (X - 1) * (X - 2) * (X - 3) * (X - 6) * (X - 27) ^ 2 * (X - 54) ^ 2

theorem charPoly_expand :
    charPoly = X ^ 8 - 174 * X ^ 7 + 11468 * X ^ 6 - 357606 * X ^ 5 + 5417235 * X ^ 4
      - 37298556 * X ^ 3 + 117258192 * X ^ 2 - 161558064 * X + 76527504 := by
  rw [charPoly]; ring

theorem charPoly_natDegree : charPoly.natDegree = 8 := by
  rw [charPoly_expand]; compute_degree!

/-- The constant term is nonzero, one of the two conditions the source imposes on an admissible
characteristic polynomial (the other, integrality, is the ambient ring). -/
theorem charPoly_coeff_zero : charPoly.coeff 0 = 76527504 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, charPoly]
  simp

theorem charPoly_coeff_zero_ne : charPoly.coeff 0 ≠ 0 := by
  rw [charPoly_coeff_zero]; norm_num

/-- **`s` is constant-recursive of order eight**, with the coefficients of `charPoly`. Each
exponential atom is annihilated because the corresponding number is a root, and the two double
roots kill the `n·27^n`, `n·54^n` terms as well — so the identity is a polynomial identity in the
atoms `n, 2^n, 3^n, 6^n, 27^n, 54^n` and `ring` sees it. -/
theorem s_recurrence (n : ℕ) :
    76527504 * s n - 161558064 * s (n + 1) + 117258192 * s (n + 2) - 37298556 * s (n + 3)
      + 5417235 * s (n + 4) - 357606 * s (n + 5) + 11468 * s (n + 6) - 174 * s (n + 7)
      + s (n + 8) = 0 := by
  simp only [s]
  push_cast
  ring

/-! ## The ambient count, before the losses -/

/-- The triangular sum, stated multiplied out so no division occurs. -/
theorem two_mul_tri (m : ℕ) :
    2 * ∑ h ∈ Finset.range (m + 1), (h + 1) = (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- **The rank before any cancellation.** Summing `deg + 1` over the feasible pairs
`r ∈ {0,1,2}`, `0 ≤ h ≤ M - r`, for each of the `M + 1` values of `i`, gives
`(M+1)(3M² + 3M + 2)/2` — the leading term of the formula, here in division-free form. -/
theorem count_total (M : ℕ) (hM : 2 ≤ M) :
    2 * ((M + 1) * ∑ r ∈ Finset.range 3, ∑ h ∈ Finset.range (M - r + 1), (h + 1))
      = (M + 1) * (3 * M ^ 2 + 3 * M + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have e0 : k + 2 - 0 = k + 2 := rfl
  have e1 : k + 2 - 1 = k + 1 := rfl
  have e2 : k + 2 - 2 = k := rfl
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, e0, e1, e2, Nat.zero_add]
  have h0 := two_mul_tri (k + 2)
  have h1 := two_mul_tri (k + 1)
  have h2 := two_mul_tri k
  nlinarith [h0, h1, h2]

/-! ## Residue — the rank computation, as a work-list

`conjecture_5_3_particular_false` carries exactly one hypothesis, `hR`, and closing it is the whole
remaining obligation. It splits into pieces that are all statable in Lean; what is **absent from
Mathlib** is only the first.

1. **Rank of an exponential polynomial.** `rank (∑_j A_j(n) λ_j^n) = ∑_j (deg A_j + 1)` for distinct
   nonzero `λ_j` and nonzero `A_j`, with `rank` the minimal *eventual* constant-coefficient
   recurrence order. Mathlib's `LinearRecurrence` has no minimality theory and no `rank`, so this
   needs the whole definition plus the shift-operator argument (`E - λ` lowers the degree of
   `A(n)λ^n` by one and preserves that of `A(n)μ^n` for `μ ≠ λ`). This is the friction boundary and
   should be its own stage.
2. **The expansion.** With `F t x y = (1+x) + y(1-x) + t y³ (1+x)` one has `s n = F n 2^n 3^n`, and
   `F^M = ∑_{h+k ≤ M} M!/(h!k!(M-h-k)!) · t^h y^{3h+k} (1+x)^{M-k} (1-x)^k`. Distinctness of the
   `2^i 3^j` is unique factorisation.
3. **Feasibility.** Writing `j = 3h + r` with `r ∈ {0,1,2}`, the pair is feasible iff `h + r ≤ M`;
   `count_total` above already prices the resulting index set.
4. **Krawtchouk coefficients and the duality.** `A_r(i) := [x^i](1+x)^{M-r}(1-x)^r`,
   `K_k(i) := [z^k](1-z)^i(1+z)^{M-i}`, `a := M - 2i`, and `C(M,r) A_r(i) = C(M,i) K_r(i)`. Then
   `K₀ = 1`, `K₁ = a`, `K₂ = (a² - M)/2`, with the recurrence
   `(k+1)K_{k+1} = a K_k - (M-k+1)K_{k-1}`.
5. **The vanishing loci.** `K₁` vanishes only at `i = M/2` (so only for even `M`); `K₂` only at
   `i = (M ± √M)/2`, which are two distinct integers in `[0,M]` exactly when `M` is a square — note
   `M` and `√M` have the same parity, so `(M ± √M)/2` are integers.
6. **The exact losses.** At a vanished leading coefficient the next term is a nonzero multiple of
   `K_{r+3}`, and the recurrence gives `K₄ = M(M-2)/8` when `a = 0` and
   `K₅ = a(M-1)(M-4)/20` when `a² = M`; both nonzero for `M ≥ 5`. Aggregating over feasible `h`,
   including the two boundary values where the whole polynomial dies, the loss per vanishing index
   is `3(M - r)`: one index for `r = 1` at even `M`, two for `r = 2` at square `M`, in disjoint
   `y`-exponent classes so the losses add.

Constants that stage will need, recorded here so they are not re-derived: `charPoly`'s coefficients
are `76527504, -161558064, 117258192, -37298556, 5417235, -357606, 11468, -174, 1`
(`charPoly_expand`), and the uncancelled count is `(M+1)(3M²+3M+2)/2` (`count_total`).
-/

end Principia.MathDB.P366795
