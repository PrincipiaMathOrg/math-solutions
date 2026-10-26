/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #320644 — the Sondow–MacMillan supercongruence (infrastructure)

MathDB open problem #320644, Conjecture 2 of Sondow–MacMillan (arXiv:1011.2154v1,
*Integers* 11 (2011), A34).  With `S n m = 1^n + 2^n + ... + m^n`, the conjecture says that if

  (1)  `S n k ≡ (k+1)^n (mod k^2)`

then for every prime `p | k`,

  (2)  `S n k ≡ (k/p) * S n p (mod p^3)`.

This module builds the ingredients the proof runs on.  The final theorem is assembled in later
work; **nothing here claims (2)**.

## The block expansion

Splitting `1, ..., ap` into the `a` blocks `tp+1, ..., tp+p` and expanding `(tp + r)^n` in powers
of `tp` through the quadratic term gives, exactly,

  `S n (ap) - a * S n p ≡ n p A₁ S (n-1) p + C(n,2) p² A₂ S (n-2) p  (mod p³)`

with `A₁ = ∑_{t<a} t` and `A₂ = ∑_{t<a} t²`.  Both are *sums*, so they are integers with no
division to justify — which is what keeps the identity honest at `p = 2` and `p = 3`, exactly
where the source's later cases live.

`binom_trunc` is the underlying truncation: `x³` divides the error in the degree-2 Taylor
expansion of `(x + y)^n` in `x`.  It is proved by induction, the step being that multiplying the
truncation by `x + y` reproduces the next truncation up to `C(n,2) x³ yⁿ⁻²`, which uses only
`C(m+3,2) = (m+2) + C(m+2,2)`.

## The power-sum identity and Gate G0

`S m p mod p` is `-1` when `p-1 ∣ m` and `0` otherwise.  This is the standard finite-field fact,
and Mathlib has it for a sum over the *units* of a finite field; `sum_pow_zmod` extends it to a
sum over all of `ZMod p` (the extra term `0^m` vanishes since `m ≥ 1`), and `S_cast_zmod` is the
bridge from the integer sum `S m p` to that sum over `ZMod p`.

`gate_G0` is the first consequence of the premise: reducing (1) modulo `p` and collapsing the
blocks gives `a * S n p ≡ 1 (mod p)`, which by the power-sum identity forces **both** `p - 1 ∣ n`
and `a ≡ -1 (mod p)`.  The second of these says `p ∤ a`, so `k` is squarefree — a fact the later
small-exponent cases need in order to enumerate `k` at all.

## Gate G2: the primes at least five

Here `p - 1 ∣ n` and `p - 1 ≥ 4` force `n` even and `n ≥ 4`, so write `n = 2u + 4`.  Both
correction terms in the block expansion then vanish: `p ∣ S (n-2) p` because `p - 1` divides `n`
but cannot divide `n - 2` (it would have to divide `2`), and `p² ∣ S (n-1) p` by pairing.

The pairing is done over the **whole** range `1, ..., p-1` rather than over half of it as the
source does.  Summing `r^M + (p-r)^M` for odd `M` gives `2 S_M ≡ M p S_{M-1}`, and the factor `2`
is then removed by coprimality with `p` — which costs one lemma and avoids constructing the
involution `r ↦ p - r` on a half-range, along with the `(p-1)/2` that only exists because `p` is
odd.  Reflection over the full range is `Finset.sum_range_reflect`, already in Mathlib.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Off, deliberately.  The lakefile sets `relaxedAutoImplicit = false`, which still auto-binds
-- SINGLE-CHARACTER identifiers -- and a mistyped or out-of-scope one-letter name then becomes a
-- universally quantified variable instead of an error, turning a theorem about the intended
-- object into a vacuous statement about an arbitrary one.  This file is full of one-letter
-- names (S, Q, a, p, u, v), so the weaker guard is the one that does not cover it.
set_option autoImplicit false

namespace Principia.MathDB.P320644

open Finset

/-! ### The power sums and the block coefficients -/

/-- `S n m = 1^n + 2^n + ... + m^n`. -/
def S (n m : ℕ) : ℤ := ∑ j ∈ Finset.range m, ((j : ℤ) + 1) ^ n

/-- `A1 a = 0 + 1 + ... + (a-1)`, the first block coefficient.  Kept as a sum, not as
`a(a-1)/2`, so that it is visibly an integer. -/
def A1 (a : ℕ) : ℤ := ∑ t ∈ Finset.range a, (t : ℤ)

/-- `A2 a = 0² + 1² + ... + (a-1)²`, the second block coefficient. -/
def A2 (a : ℕ) : ℤ := ∑ t ∈ Finset.range a, (t : ℤ) ^ 2

/-- `c2 m = C(m+2, 2)`, the quadratic binomial coefficient, as an integer. -/
def c2 (m : ℕ) : ℤ := ((m + 2).choose 2 : ℕ)

theorem S_def (n m : ℕ) : S n m = ∑ j ∈ Finset.range m, ((j : ℤ) + 1) ^ n := rfl

theorem A1_def (a : ℕ) : A1 a = ∑ t ∈ Finset.range a, (t : ℤ) := rfl

theorem A2_def (a : ℕ) : A2 a = ∑ t ∈ Finset.range a, (t : ℤ) ^ 2 := rfl

theorem c2_zero : c2 0 = 1 := by simp [c2]

theorem c2_succ (m : ℕ) : c2 (m + 1) = ((m : ℤ) + 2) + c2 m := by
  have h : (m + 1 + 2).choose 2 = (m + 2) + (m + 2).choose 2 := by
    rw [show m + 1 + 2 = (m + 2) + 1 from rfl, Nat.choose_succ_succ (m + 2) 1,
      Nat.choose_one_right]
  simp only [c2, h]
  push_cast
  ring

/-! ### The binomial truncation -/

/-- **`x³` divides the error in the degree-2 expansion of `(x + y)^(m+2)` in `x`.** -/
theorem binom_trunc (x y : ℤ) (m : ℕ) :
    x ^ 3 ∣ (x + y) ^ (m + 2)
      - (y ^ (m + 2) + ((m : ℤ) + 2) * x * y ^ (m + 1) + c2 m * x ^ 2 * y ^ m) := by
  induction m with
  | zero =>
    refine ⟨0, ?_⟩
    rw [c2_zero]
    push_cast
    ring
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(x + y) * c + c2 m * y ^ m, ?_⟩
    rw [c2_succ]
    push_cast
    linear_combination (x + y) * hc

/-! ### Splitting the sum into blocks -/

/-- `1, ..., ap` split into the `a` blocks `tp+1, ..., tp+p`. -/
theorem S_block (n p a : ℕ) :
    S n (a * p)
      = ∑ t ∈ Finset.range a, ∑ r ∈ Finset.range p, ((t : ℤ) * p + ((r : ℤ) + 1)) ^ n := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
    have hidx : (a + 1) * p = a * p + p := by ring
    have hstep : S n (a * p + p)
        = S n (a * p) + ∑ r ∈ Finset.range p, (((a * p + r : ℕ) : ℤ) + 1) ^ n :=
      Finset.sum_range_add (fun j : ℕ => ((j : ℤ) + 1) ^ n) (a * p) p
    rw [hidx, hstep, ih, Finset.sum_range_succ]
    congr 1

/-! ### Gate G1: the exact block expansion modulo `p³` -/

/-- **The block expansion.**  Exact modulo `p³`, with integer coefficients `A1` and `A2`. -/
theorem block_congr (N p a : ℕ) :
    (p : ℤ) ^ 3 ∣ S (N + 2) (a * p)
      - ((a : ℤ) * S (N + 2) p + ((N : ℤ) + 2) * p * A1 a * S (N + 1) p
          + c2 N * (p : ℤ) ^ 2 * A2 a * S N p) := by
  have hY : ∀ t ∈ Finset.range a, (∑ r ∈ Finset.range p,
        (((r : ℤ) + 1) ^ (N + 2) + ((N : ℤ) + 2) * ((t : ℤ) * p) * ((r : ℤ) + 1) ^ (N + 1)
          + c2 N * ((t : ℤ) * p) ^ 2 * ((r : ℤ) + 1) ^ N))
      = S (N + 2) p + ((N : ℤ) + 2) * ((t : ℤ) * p) * S (N + 1) p
          + c2 N * ((t : ℤ) * p) ^ 2 * S N p := by
    intro t _
    rw [S_def (N + 2) p, S_def (N + 1) p, S_def N p, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hYY : (∑ t ∈ Finset.range a, (S (N + 2) p + ((N : ℤ) + 2) * ((t : ℤ) * p) * S (N + 1) p
          + c2 N * ((t : ℤ) * p) ^ 2 * S N p))
      = (a : ℤ) * S (N + 2) p + ((N : ℤ) + 2) * p * A1 a * S (N + 1) p
          + c2 N * (p : ℤ) ^ 2 * A2 a * S N p := by
    have e1 : ∀ t ∈ Finset.range a, ((N : ℤ) + 2) * ((t : ℤ) * p) * S (N + 1) p
        = (((N : ℤ) + 2) * p * S (N + 1) p) * (t : ℤ) := fun t _ => by ring
    have e2 : ∀ t ∈ Finset.range a, c2 N * ((t : ℤ) * p) ^ 2 * S N p
        = (c2 N * (p : ℤ) ^ 2 * S N p) * (t : ℤ) ^ 2 := fun t _ => by ring
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_congr rfl e1,
      Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, A1_def, A2_def]
    ring
  have inner : ∀ t ∈ Finset.range a,
      (∑ r ∈ Finset.range p,
        (((t : ℤ) * p + ((r : ℤ) + 1)) ^ (N + 2)
          - (((r : ℤ) + 1) ^ (N + 2) + ((N : ℤ) + 2) * ((t : ℤ) * p) * ((r : ℤ) + 1) ^ (N + 1)
              + c2 N * ((t : ℤ) * p) ^ 2 * ((r : ℤ) + 1) ^ N)))
      = (∑ r ∈ Finset.range p, ((t : ℤ) * p + ((r : ℤ) + 1)) ^ (N + 2))
        - (∑ r ∈ Finset.range p,
            (((r : ℤ) + 1) ^ (N + 2) + ((N : ℤ) + 2) * ((t : ℤ) * p) * ((r : ℤ) + 1) ^ (N + 1)
              + c2 N * ((t : ℤ) * p) ^ 2 * ((r : ℤ) + 1) ^ N)) :=
    fun _ _ => Finset.sum_sub_distrib _ _
  have key : (∑ t ∈ Finset.range a, ∑ r ∈ Finset.range p,
        (((t : ℤ) * p + ((r : ℤ) + 1)) ^ (N + 2)
          - (((r : ℤ) + 1) ^ (N + 2) + ((N : ℤ) + 2) * ((t : ℤ) * p) * ((r : ℤ) + 1) ^ (N + 1)
              + c2 N * ((t : ℤ) * p) ^ 2 * ((r : ℤ) + 1) ^ N)))
      = S (N + 2) (a * p)
        - ((a : ℤ) * S (N + 2) p + ((N : ℤ) + 2) * p * A1 a * S (N + 1) p
            + c2 N * (p : ℤ) ^ 2 * A2 a * S N p) := by
    rw [Finset.sum_congr rfl inner, Finset.sum_sub_distrib, ← S_block,
      Finset.sum_congr rfl hY, hYY]
  rw [← key]
  refine Finset.dvd_sum fun t _ => Finset.dvd_sum fun r _ => ?_
  have hdvd : (p : ℤ) ^ 3 ∣ ((t : ℤ) * p) ^ 3 := ⟨(t : ℤ) ^ 3, by ring⟩
  exact hdvd.trans (binom_trunc ((t : ℤ) * p) ((r : ℤ) + 1) N)

/-! ### The same expansion modulo `p`, valid for every exponent -/

/-- Modulo `p` the blocks collapse: `S n (ap) ≡ a * S n p`.  Unlike `block_congr` this needs no
lower bound on `n`, because it uses only `x ∣ (x+y)^n - y^n`. -/
theorem S_block_mod_p (n p a : ℕ) : (p : ℤ) ∣ S n (a * p) - (a : ℤ) * S n p := by
  have inner : ∀ t ∈ Finset.range a,
      (∑ r ∈ Finset.range p, (((t : ℤ) * p + ((r : ℤ) + 1)) ^ n - ((r : ℤ) + 1) ^ n))
      = (∑ r ∈ Finset.range p, ((t : ℤ) * p + ((r : ℤ) + 1)) ^ n)
        - (∑ r ∈ Finset.range p, ((r : ℤ) + 1) ^ n) := fun _ _ => Finset.sum_sub_distrib _ _
  have key : (∑ t ∈ Finset.range a, ∑ r ∈ Finset.range p,
        (((t : ℤ) * p + ((r : ℤ) + 1)) ^ n - ((r : ℤ) + 1) ^ n))
      = S n (a * p) - (a : ℤ) * S n p := by
    rw [S_def n p, Finset.sum_congr rfl inner, Finset.sum_sub_distrib, ← S_block,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← key]
  refine Finset.dvd_sum fun t _ => Finset.dvd_sum fun r _ => ?_
  have h : ((t : ℤ) * p + ((r : ℤ) + 1)) - ((r : ℤ) + 1)
      ∣ ((t : ℤ) * p + ((r : ℤ) + 1)) ^ n - ((r : ℤ) + 1) ^ n :=
    (Commute.all _ _).sub_dvd_pow_sub_pow n
  have he : ((t : ℤ) * p + ((r : ℤ) + 1)) - ((r : ℤ) + 1) = (t : ℤ) * p := by ring
  rw [he] at h
  have hpt : (p : ℤ) ∣ (t : ℤ) * p := ⟨(t : ℤ), by ring⟩
  exact hpt.trans h

/-! ### Gate G0, first half: the finite-field power-sum identity -/

/-- Reindexing: a sum over `Finset.range p` of a function of `j mod p` is a sum over `ZMod p`. -/
theorem sum_range_zmod {R : Type*} [AddCommMonoid R] (p : ℕ) [NeZero p] (h : ZMod p → R) :
    ∑ j ∈ Finset.range p, h (j : ZMod p) = ∑ x : ZMod p, h x := by
  rw [Finset.sum_range (fun j : ℕ => h (j : ZMod p))]
  refine Fintype.sum_bijective (fun i : Fin p => ((i : ℕ) : ZMod p)) ?_ _ _ (fun i => rfl)
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j hij => ?_, ?_⟩
  · have hij' : ((i : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := hij
    have hi : ((i : ℕ) : ZMod p).val = (i : ℕ) := ZMod.val_cast_of_lt i.isLt
    have hj : ((j : ℕ) : ZMod p).val = (j : ℕ) := ZMod.val_cast_of_lt j.isLt
    exact Fin.ext (by rw [← hi, ← hj, hij'])
  · simp [ZMod.card]

/-- `S n p` reduced mod `p` is the sum of `n`-th powers over all of `ZMod p`. -/
theorem S_cast_zmod (n p : ℕ) [NeZero p] : ((S n p : ℤ) : ZMod p) = ∑ x : ZMod p, x ^ n := by
  have h1 : ((S n p : ℤ) : ZMod p) = ∑ j ∈ Finset.range p, (((j : ZMod p) + 1) ^ n) := by
    push_cast [S_def]
    rfl
  rw [h1, sum_range_zmod p (fun x => (x + 1) ^ n)]
  exact Fintype.sum_bijective (fun x : ZMod p => x + 1) (Equiv.addRight (1 : ZMod p)).bijective
    _ _ (fun x => rfl)

/-- The sum of `m`-th powers over all of `ZMod p`, for `m ≥ 1`. -/
theorem sum_pow_zmod (p : ℕ) [Fact p.Prime] [NeZero p] (m : ℕ) (hm : 0 < m) :
    (∑ x : ZMod p, x ^ m) = if (p - 1) ∣ m then -1 else 0 := by
  have hmap : Finset.univ \ {(0 : ZMod p)}
      = Finset.univ.map ⟨fun x : (ZMod p)ˣ => (x : ZMod p), Units.val_injective⟩ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    exact isUnit_iff_ne_zero.symm
  have hsplit : ∑ x : ZMod p, x ^ m = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ m) := by
    have h1 : ∑ x : ZMod p, x ^ m = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ m := by
      rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))), Finset.sum_singleton,
        zero_pow hm.ne', add_zero]
    rw [h1, hmap, Finset.sum_map]
    rfl
  rw [hsplit, FiniteField.sum_pow_units (ZMod p) m, ZMod.card]

/-- **The power-sum identity.**  `S m p ≡ -1 (mod p)` when `p - 1 ∣ m`, and `≡ 0` otherwise. -/
theorem S_mod_p (p : ℕ) (hp : p.Prime) (m : ℕ) (hm : 0 < m) :
    ((S m p : ℤ) : ZMod p) = if (p - 1) ∣ m then -1 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [S_cast_zmod, sum_pow_zmod p m hm]

/-! ### Gate G0: what the premise forces -/

/-- **Gate G0.**  If `k = ap` satisfies the premise `(1)`, then `p - 1 ∣ n` and `a ≡ -1 (mod p)`.

Both halves come from one congruence: modulo `p` the premise reads `a * S n p ≡ 1`, and the
power-sum identity leaves `S n p` only two possible values.  The value `0` is impossible because
`1 ≠ 0` in `ZMod p`, which is what forces `p - 1 ∣ n`; the value `-1` then pins `a`. -/
theorem gate_G0 {n k p a : ℕ} (hn : 0 < n) (hp : p.Prime) (hka : k = a * p)
    (hpre : (k : ℤ) ^ 2 ∣ ((k : ℤ) + 1) ^ n - S n k) :
    (p - 1) ∣ n ∧ (a : ZMod p) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hpk : (p : ℤ) ∣ (k : ℤ) := by
    rw [hka]
    push_cast
    exact ⟨(a : ℤ), by ring⟩
  have h1 : (p : ℤ) ∣ ((k : ℤ) + 1) ^ n - S n k :=
    (hpk.trans (dvd_pow_self (k : ℤ) (by norm_num : 2 ≠ 0))).trans hpre
  have h2 : (p : ℤ) ∣ ((k : ℤ) + 1) ^ n - 1 := by
    have h : ((k : ℤ) + 1) - 1 ∣ ((k : ℤ) + 1) ^ n - 1 := sub_one_dvd_pow_sub_one _ n
    rw [add_sub_cancel_right] at h
    exact hpk.trans h
  have h3 : (p : ℤ) ∣ S n k - (a : ℤ) * S n p := by
    rw [hka]
    exact S_block_mod_p n p a
  have h4 : (p : ℤ) ∣ 1 - (a : ℤ) * S n p := by
    have e : (1 : ℤ) - (a : ℤ) * S n p
        = -(((k : ℤ) + 1) ^ n - 1) + (((k : ℤ) + 1) ^ n - S n k) + (S n k - (a : ℤ) * S n p) := by
      ring
    rw [e]
    exact dvd_add (dvd_add (dvd_neg.mpr h2) h1) h3
  have h5 : (((1 : ℤ) - (a : ℤ) * S n p : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h4
  push_cast at h5
  rw [S_mod_p p hp n hn] at h5
  by_cases hd : (p - 1) ∣ n
  · rw [if_pos hd] at h5
    exact ⟨hd, by linear_combination h5⟩
  · rw [if_neg hd, mul_zero, sub_zero] at h5
    exact absurd h5 one_ne_zero

/-! ### Gate G2: the primes at least five -/

/-- The two-term truncation: `x²` divides the error in the linear expansion of `(x+y)^(m+1)`. -/
theorem binom_trunc2 (x y : ℤ) (m : ℕ) :
    x ^ 2 ∣ (x + y) ^ (m + 1) - (y ^ (m + 1) + ((m : ℤ) + 1) * x * y ^ m) := by
  induction m with
  | zero => exact ⟨0, by push_cast; ring⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(x + y) * c + ((m : ℤ) + 1) * y ^ m, ?_⟩
    push_cast
    linear_combination (x + y) * hc

/-- Peeling the last term off a power sum. -/
theorem S_succ (m q : ℕ) : S m (q + 1) = S m q + ((q : ℤ) + 1) ^ m := by
  simp only [S_def, Finset.sum_range_succ]

/-- **Reflection.**  Replacing `r` by `p - r` on `1, ..., q` (with `p = q + 1`) permutes the
summands, so the power sum is unchanged. -/
theorem S_reflect (m q : ℕ) :
    (∑ j ∈ Finset.range q, ((q : ℤ) - (j : ℤ)) ^ m) = S m q := by
  rw [S_def, ← Finset.sum_range_reflect (fun j : ℕ => ((j : ℤ) + 1) ^ m) q]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjq : j < q := Finset.mem_range.mp hj
  have hcast : ((q : ℤ) - (j : ℤ)) = ((q - 1 - j : ℕ) : ℤ) + 1 := by omega
  rw [hcast]

/-- **The pairing identity.**  For an odd exponent `M = 2u+3` and `p = q+1`,
`2 S_M(q) ≡ M p S_{M-1}(q) (mod p²)`.  This is the whole content of the `p ≥ 5` case. -/
theorem pair_congr (q u : ℕ) :
    ((q : ℤ) + 1) ^ 2 ∣ 2 * S (2 * u + 3) q
      - (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * S (2 * u + 2) q := by
  have key : (∑ j ∈ Finset.range q,
        (((q : ℤ) - (j : ℤ)) ^ (2 * u + 3) + ((j : ℤ) + 1) ^ (2 * u + 3)
          - (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * ((j : ℤ) + 1) ^ (2 * u + 2)))
      = 2 * S (2 * u + 3) q - (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * S (2 * u + 2) q := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, S_reflect, ← Finset.mul_sum,
      ← S_def, ← S_def]
    ring
  rw [← key]
  refine Finset.dvd_sum fun j _ => ?_
  have hodd : Odd (2 * u + 3) := ⟨u + 1, by ring⟩
  have heven : Even (2 * u + 2) := ⟨u + 1, by ring⟩
  have h := binom_trunc2 ((q : ℤ) + 1) (-((j : ℤ) + 1)) (2 * u + 2)
  have e : (((q : ℤ) + 1) + -((j : ℤ) + 1)) ^ (2 * u + 2 + 1)
        - ((-((j : ℤ) + 1)) ^ (2 * u + 2 + 1)
            + (((2 * u + 2 : ℕ) : ℤ) + 1) * ((q : ℤ) + 1) * (-((j : ℤ) + 1)) ^ (2 * u + 2))
      = ((q : ℤ) - (j : ℤ)) ^ (2 * u + 3) + ((j : ℤ) + 1) ^ (2 * u + 3)
        - (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * ((j : ℤ) + 1) ^ (2 * u + 2) := by
    rw [show 2 * u + 2 + 1 = 2 * u + 3 from rfl, hodd.neg_pow, heven.neg_pow,
      show ((q : ℤ) + 1) + -((j : ℤ) + 1) = (q : ℤ) - (j : ℤ) from by ring]
    push_cast
    ring
  rw [← e]
  exact h

/-- **Gate G2.**  For a prime `p = q + 1 ≥ 5` whose `p - 1 = q` divides `n = 2u + 4`, both
correction terms of the block expansion vanish modulo `p³`: `p ∣ S (n-2) p` and
`p² ∣ S (n-1) p`. -/
theorem gate_G2 (q u : ℕ) (hp : (q + 1).Prime) (hq : 4 ≤ q) (hdvd : q ∣ (2 * u + 4)) :
    ((q : ℤ) + 1) ∣ S (2 * u + 2) (q + 1)
      ∧ ((q : ℤ) + 1) ^ 2 ∣ S (2 * u + 3) (q + 1) := by
  haveI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  have hnd : ¬ q ∣ (2 * u + 2) := by
    intro h
    have hs := Nat.dvd_sub hdvd h
    have he : 2 * u + 4 - (2 * u + 2) = 2 := by omega
    rw [he] at hs
    have hle := Nat.le_of_dvd (by norm_num) hs
    omega
  have ha : ((q : ℤ) + 1) ∣ S (2 * u + 2) (q + 1) := by
    have h := S_mod_p (q + 1) hp (2 * u + 2) (by omega)
    rw [Nat.add_sub_cancel, if_neg hnd] at h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (S (2 * u + 2) (q + 1)) (q + 1)).mp h
    push_cast at hd
    exact hd
  refine ⟨ha, ?_⟩
  have hq2 : ((q : ℤ) + 1) ∣ S (2 * u + 2) q := by
    have h1 : ((q : ℤ) + 1) ∣ ((q : ℤ) + 1) ^ (2 * u + 2) := dvd_pow_self _ (by omega)
    have h2 : ((q : ℤ) + 1) ∣ S (2 * u + 2) q + ((q : ℤ) + 1) ^ (2 * u + 2) := by
      rw [← S_succ]
      exact ha
    have h3 := dvd_sub h2 h1
    have he : S (2 * u + 2) q + ((q : ℤ) + 1) ^ (2 * u + 2) - ((q : ℤ) + 1) ^ (2 * u + 2)
        = S (2 * u + 2) q := by ring
    rwa [he] at h3
  have h3 : ((q : ℤ) + 1) ^ 2 ∣ (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * S (2 * u + 2) q := by
    obtain ⟨c, hc⟩ := hq2
    exact ⟨(2 * (u : ℤ) + 3) * c, by rw [hc]; ring⟩
  have hb : ((q : ℤ) + 1) ^ 2 ∣ 2 * S (2 * u + 3) q := by
    have hsum := dvd_add (pair_congr q u) h3
    have he : (2 * S (2 * u + 3) q - (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * S (2 * u + 2) q)
        + (2 * (u : ℤ) + 3) * ((q : ℤ) + 1) * S (2 * u + 2) q = 2 * S (2 * u + 3) q := by ring
    rwa [he] at hsum
  have hb2 : ((q : ℤ) + 1) ^ 2 ∣ 2 * S (2 * u + 3) (q + 1) := by
    have h4 : ((q : ℤ) + 1) ^ 2 ∣ 2 * ((q : ℤ) + 1) ^ (2 * u + 3) :=
      Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) 2
    have he : 2 * S (2 * u + 3) (q + 1)
        = 2 * S (2 * u + 3) q + 2 * ((q : ℤ) + 1) ^ (2 * u + 3) := by
      rw [S_succ]
      ring
    rw [he]
    exact dvd_add hb h4
  have hcopN : Nat.Coprime (q + 1) 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hcopZ : IsCoprime ((q : ℤ) + 1) (2 : ℤ) := by
    have hc := Nat.isCoprime_iff_coprime.mpr hcopN
    push_cast at hc
    exact hc
  exact (hcopZ.pow_left (m := 2)).dvd_of_dvd_mul_left hb2

/-! ### Small power sums, in closed form

At `p = 2` and `p = 3` the power sum is short enough to write out, which replaces the whole
finite-field machinery by arithmetic on `2 ^ m` and `3 ^ m`. -/

theorem S_two (m : ℕ) : S m 2 = 1 + 2 ^ m := by
  rw [S_def, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem S_three (m : ℕ) : S m 3 = 1 + 2 ^ m + 3 ^ m := by
  rw [S_def, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

/-! ### The block coefficients modulo three

`A1` and `A2` are periodic modulo `3` with period `9` in `a`, because nine consecutive integers
contribute `9a + 36` and nine consecutive squares contribute `9a² + 72a + 204`, both divisible by
three.  This is what lets the `p = 3` case read `A1` and `A2` off `a mod 9` alone. -/

theorem A1_add_nine (a : ℕ) : A1 (a + 9) = A1 a + (9 * (a : ℤ) + 36) := by
  simp only [A1_def, Finset.sum_range_succ]
  push_cast
  ring

theorem A2_add_nine (a : ℕ) :
    A2 (a + 9) = A2 a + (9 * (a : ℤ) ^ 2 + 72 * (a : ℤ) + 204) := by
  simp only [A2_def, Finset.sum_range_succ]
  push_cast
  ring

theorem A1_mod_three (b c : ℕ) : (3 : ℤ) ∣ A1 (9 * b + c) - A1 c := by
  induction b with
  | zero => simp
  | succ b ih =>
    have he : 9 * (b + 1) + c = (9 * b + c) + 9 := by ring
    rw [he, A1_add_nine]
    have h2 : A1 (9 * b + c) + (9 * ((9 * b + c : ℕ) : ℤ) + 36) - A1 c
        = (A1 (9 * b + c) - A1 c) + (9 * ((9 * b + c : ℕ) : ℤ) + 36) := by ring
    rw [h2]
    exact dvd_add ih ⟨3 * ((9 * b + c : ℕ) : ℤ) + 12, by ring⟩

theorem A2_mod_three (b c : ℕ) : (3 : ℤ) ∣ A2 (9 * b + c) - A2 c := by
  induction b with
  | zero => simp
  | succ b ih =>
    have he : 9 * (b + 1) + c = (9 * b + c) + 9 := by ring
    rw [he, A2_add_nine]
    have h2 : A2 (9 * b + c)
          + (9 * ((9 * b + c : ℕ) : ℤ) ^ 2 + 72 * ((9 * b + c : ℕ) : ℤ) + 204) - A2 c
        = (A2 (9 * b + c) - A2 c)
          + (9 * ((9 * b + c : ℕ) : ℤ) ^ 2 + 72 * ((9 * b + c : ℕ) : ℤ) + 204) := by ring
    rw [h2]
    exact dvd_add ih
      ⟨3 * ((9 * b + c : ℕ) : ℤ) ^ 2 + 24 * ((9 * b + c : ℕ) : ℤ) + 68, by ring⟩

/-! ### Gate G4: the prime two

No block expansion is needed here.  For even `n ≥ 4`, every odd `j` has `j^n ≡ 1 (mod 8)` and
every even `j` has `j^n ≡ 0 (mod 8)`, and exactly `a` of `1, ..., 2a` are odd. -/

theorem odd_sq_mod_eight (t : ℤ) : (8 : ℤ) ∣ (2 * t + 1) ^ 2 - 1 := by
  obtain ⟨c, hc⟩ := Int.even_mul_succ_self t
  refine ⟨c, ?_⟩
  have he : (2 * t + 1) ^ 2 - 1 = 4 * (t * (t + 1)) := by ring
  rw [he, hc]
  ring

/-- If `d` divides `x - 1` it divides every `x ^ m - 1`.  Stated for a general modulus: it is
used at `d = 8` for the prime two and at `d = 9` and `d = 3` for the prime three. -/
theorem dvd_pow_sub_one {d x : ℤ} (h : d ∣ x - 1) (m : ℕ) : d ∣ x ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : x ^ (m + 1) - 1 = x * (x ^ m - 1) + (x - 1) := by ring
    rw [he]
    exact dvd_add (Dvd.dvd.mul_left ih x) h

theorem odd_pow_mod_eight (t : ℤ) (v : ℕ) : (8 : ℤ) ∣ (2 * t + 1) ^ (2 * v) - 1 := by
  rw [pow_mul]
  exact dvd_pow_sub_one (odd_sq_mod_eight t) v

/-- **Gate G4.**  `S n (2a) ≡ a (mod 8)` for `n = 2u + 4`.  Since `S n 2 ≡ 1 (mod 8)` for such
`n`, this is exactly the supercongruence at `p = 2`. -/
theorem gate_G4 (a u : ℕ) : (8 : ℤ) ∣ S (2 * u + 4) (a * 2) - (a : ℤ) := by
  have hblock : S (2 * u + 4) (a * 2)
      = ∑ t ∈ Finset.range a,
          ((2 * (t : ℤ) + 1) ^ (2 * u + 4) + (2 * ((t : ℤ) + 1)) ^ (2 * u + 4)) := by
    rw [S_block]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  have key : (∑ t ∈ Finset.range a,
        ((2 * (t : ℤ) + 1) ^ (2 * u + 4) + (2 * ((t : ℤ) + 1)) ^ (2 * u + 4) - 1))
      = S (2 * u + 4) (a * 2) - (a : ℤ) := by
    rw [Finset.sum_sub_distrib, hblock, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
  rw [← key]
  refine Finset.dvd_sum fun t _ => ?_
  have h1 : (8 : ℤ) ∣ (2 * (t : ℤ) + 1) ^ (2 * u + 4) - 1 := by
    rw [show 2 * u + 4 = 2 * (u + 2) from by ring]
    exact odd_pow_mod_eight (t : ℤ) (u + 2)
  have h8 : (8 : ℤ) ∣ 2 ^ (2 * u + 4) :=
    dvd_trans (by norm_num : (8 : ℤ) ∣ 2 ^ 3) (pow_dvd_pow 2 (by omega))
  have h2 : (8 : ℤ) ∣ (2 * ((t : ℤ) + 1)) ^ (2 * u + 4) := by
    rw [mul_pow]
    exact Dvd.dvd.mul_right h8 _
  have he : (2 * (t : ℤ) + 1) ^ (2 * u + 4) + (2 * ((t : ℤ) + 1)) ^ (2 * u + 4) - 1
      = ((2 * (t : ℤ) + 1) ^ (2 * u + 4) - 1) + (2 * ((t : ℤ) + 1)) ^ (2 * u + 4) := by ring
  rw [he]
  exact dvd_add h1 h2

/-! ### Arithmetic helpers for the prime three

Everything the `p = 3` case needs about `A1`, `A2`, `c2` and `2 ^ m`, in the form of explicit
divisibilities.  Two design choices keep this elementary.  The Gauss sum and the binomial
coefficient are recorded *doubled* — `2 A1 a = a(a-1)` and `2 c2 m = (m+2)(m+1)` — so that no
division ever appears; the stray factor of two is removed at the end by
`three_dvd_of_dvd_two_mul`, which is three lines and needs no coprimality API. -/

/-- If `3 ∣ 2Y` then `3 ∣ Y`, from `Y = 2(2Y) - 3Y`. -/
theorem three_dvd_of_dvd_two_mul {Y : ℤ} (h : (3 : ℤ) ∣ 2 * Y) : (3 : ℤ) ∣ Y := by
  have he : Y = 2 * (2 * Y) - 3 * Y := by ring
  rw [he]
  exact dvd_sub (Dvd.dvd.mul_left h 2) ⟨Y, rfl⟩

theorem A1_succ (a : ℕ) : A1 (a + 1) = A1 a + (a : ℤ) := by
  simp only [A1_def, Finset.sum_range_succ]

/-- The Gauss sum, doubled so that it is an identity of integers. -/
theorem two_mul_A1 (a : ℕ) : 2 * A1 a = (a : ℤ) * ((a : ℤ) - 1) := by
  induction a with
  | zero => simp [A1_def]
  | succ a ih =>
    rw [A1_succ]
    push_cast
    linear_combination ih

/-- `2 C(m+2,2) = (m+2)(m+1)`, again with no division. -/
theorem two_mul_c2 (m : ℕ) : 2 * c2 m = ((m : ℤ) + 2) * ((m : ℤ) + 1) := by
  induction m with
  | zero =>
    rw [c2_zero]
    norm_num
  | succ m ih =>
    rw [c2_succ]
    push_cast
    linear_combination ih

/-- `2` has order six modulo nine, so `2 ^ m mod 9` depends only on `m mod 6`. -/
theorem two_pow_mod_nine (w r : ℕ) : (9 : ℤ) ∣ 2 ^ (6 * w + r) - 2 ^ r := by
  have h2 : (9 : ℤ) ∣ ((2 : ℤ) ^ 6) ^ w - 1 :=
    dvd_pow_sub_one (by norm_num : (9 : ℤ) ∣ (2 : ℤ) ^ 6 - 1) w
  have he : (2 : ℤ) ^ (6 * w + r) - 2 ^ r = 2 ^ r * (((2 : ℤ) ^ 6) ^ w - 1) := by
    rw [pow_add, pow_mul]
    ring
  rw [he]
  exact Dvd.dvd.mul_left h2 _

/-- `2` has order two modulo three. -/
theorem two_pow_mod_three (w r : ℕ) : (3 : ℤ) ∣ 2 ^ (2 * w + r) - 2 ^ r := by
  have h2 : (3 : ℤ) ∣ ((2 : ℤ) ^ 2) ^ w - 1 :=
    dvd_pow_sub_one (by norm_num : (3 : ℤ) ∣ (2 : ℤ) ^ 2 - 1) w
  have he : (2 : ℤ) ^ (2 * w + r) - 2 ^ r = 2 ^ r * (((2 : ℤ) ^ 2) ^ w - 1) := by
    rw [pow_add, pow_mul]
    ring
  rw [he]
  exact Dvd.dvd.mul_left h2 _

/-- **`A1 a ≡ 1 (mod 3)` whenever `a ≡ 2 (mod 3)`**, which is what Gate G0 supplies at `p = 3`.
Note this holds for every such `a`, with no dependence on `a mod 9`. -/
theorem A1_mod_three_of {a : ℕ} (h : (3 : ℤ) ∣ (a : ℤ) - 2) : (3 : ℤ) ∣ A1 a - 1 := by
  refine three_dvd_of_dvd_two_mul ?_
  obtain ⟨s, hs⟩ := h
  have ha : (a : ℤ) = 3 * s + 2 := by linarith
  have he : 2 * (A1 a - 1) = (a : ℤ) * ((a : ℤ) - 1) - 2 := by
    have h2 := two_mul_A1 a
    linarith
  rw [he, ha]
  exact ⟨3 * s ^ 2 + 3 * s, by ring⟩

theorem A2_eight : A2 8 = 140 := by
  simp only [A2_def, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **`A2 a ≡ 2 (mod 3)` whenever `a ≡ 8 (mod 9)`.**  Unlike `A1`, this genuinely needs `a`
modulo nine, which is why the `p = 3` case has to go back to the premise modulo nine. -/
theorem A2_mod_three_of {a : ℕ} (h : (9 : ℤ) ∣ (a : ℤ) + 1) : (3 : ℤ) ∣ A2 a - 2 := by
  obtain ⟨b, hb⟩ : ∃ b, a = 9 * b + 8 := by
    obtain ⟨c, hc⟩ := h
    refine ⟨a / 9, ?_⟩
    omega
  subst hb
  have h1 := A2_mod_three b 8
  rw [A2_eight] at h1
  have he : A2 (9 * b + 8) - 2 = (A2 (9 * b + 8) - 140) + 138 := by ring
  rw [he]
  exact dvd_add h1 ⟨46, by norm_num⟩

/-! ### Gate G3: the exceptional prime three

At `p = 3` the two correction terms do **not** vanish separately — they cancel — so the case has
to be run on the sum.  Writing `n = 2u + 4` and `S (n-1) 3 = 3Q`, what must be shown is

  `3 ∣ (2u+4) * A1 a * Q + c2 (2u+2) * A2 a * S (n-2) 3`,

and every factor is determined modulo three by `u mod 3`, except `A1 a` (which needs only
`a mod 3`, from Gate G0) and `A2 a` (which needs `a mod 9`, from the premise).

Two of the three residues of `u` are easy: the coefficients themselves are divisible by three and
each term dies on its own.  Only `u ≡ 2` needs the cancellation, and there the six residues are
`2, 1, 1, 1, 2, 2`, giving `2·1·1 + 1·2·2 = 6 ≡ 0`.  That last computation is done with
`Int.ModEq` rather than by exhibiting a witness, so the arithmetic is checked by the combinators
rather than by me. -/

/-- `u ≡ 0 (mod 3)`.  Here `2^(6v+3) ≡ 8 (mod 9)` makes the odd power sum divisible by nine, so
`Q ≡ 0`, and `2 c2 (6v+2) = (6v+4)(6v+3)` is divisible by three.  Both terms die separately. -/
theorem gate_G3_zero (u v a : ℕ) (hu : u = 3 * v) (Q : ℤ) (hQ : S (2 * u + 3) 3 = 3 * Q) :
    (3 : ℤ) ∣ (2 * (u : ℤ) + 4) * A1 a * Q + c2 (2 * u + 2) * A2 a * S (2 * u + 2) 3 := by
  subst hu
  have i1 : 2 * (3 * v) + 3 = 6 * v + 3 := by ring
  have i2 : 2 * (3 * v) + 2 = 6 * v + 2 := by ring
  rw [i1] at hQ
  rw [i2]
  have hQ3 : (3 : ℤ) ∣ Q := by
    have hnine : (9 : ℤ) ∣ S (6 * v + 3) 3 := by
      rw [S_three]
      have h1 : (9 : ℤ) ∣ 2 ^ (6 * v + 3) - 2 ^ 3 := two_pow_mod_nine v 3
      have h2 : (9 : ℤ) ∣ (3 : ℤ) ^ (6 * v + 3) :=
        dvd_trans (by norm_num : (9 : ℤ) ∣ (3 : ℤ) ^ 2) (pow_dvd_pow 3 (by omega))
      have he : (1 : ℤ) + 2 ^ (6 * v + 3) + 3 ^ (6 * v + 3)
          = (2 ^ (6 * v + 3) - 2 ^ 3) + (2 ^ 3 + 1) + 3 ^ (6 * v + 3) := by ring
      rw [he]
      exact dvd_add (dvd_add h1 ⟨1, by norm_num⟩) h2
    rw [hQ] at hnine
    obtain ⟨c, hc⟩ := hnine
    exact ⟨c, by linarith⟩
  have hc2 : (3 : ℤ) ∣ c2 (6 * v + 2) := by
    refine three_dvd_of_dvd_two_mul ?_
    rw [two_mul_c2]
    push_cast
    exact ⟨(6 * (v : ℤ) + 4) * (2 * (v : ℤ) + 1), by ring⟩
  exact dvd_add (Dvd.dvd.mul_left hQ3 _)
    (Dvd.dvd.mul_right (Dvd.dvd.mul_right hc2 _) _)

/-- `u ≡ 1 (mod 3)`.  Here `2u + 4 = 6v + 6` and `2 c2 (6v+4) = (6v+6)(6v+5)` are both divisible
by three, so again both terms die separately and nothing about `a` is needed. -/
theorem gate_G3_one (u v a : ℕ) (hu : u = 3 * v + 1) (Q : ℤ) :
    (3 : ℤ) ∣ (2 * (u : ℤ) + 4) * A1 a * Q + c2 (2 * u + 2) * A2 a * S (2 * u + 2) 3 := by
  subst hu
  have i2 : 2 * (3 * v + 1) + 2 = 6 * v + 4 := by ring
  have i3 : (2 * ((3 * v + 1 : ℕ) : ℤ) + 4) = 6 * (v : ℤ) + 6 := by push_cast; ring
  rw [i2, i3]
  have h1 : (3 : ℤ) ∣ 6 * (v : ℤ) + 6 := ⟨2 * (v : ℤ) + 2, by ring⟩
  have hc2 : (3 : ℤ) ∣ c2 (6 * v + 4) := by
    refine three_dvd_of_dvd_two_mul ?_
    rw [two_mul_c2]
    push_cast
    exact ⟨(2 * (v : ℤ) + 2) * (6 * (v : ℤ) + 5), by ring⟩
  exact dvd_add (Dvd.dvd.mul_right (Dvd.dvd.mul_right h1 _) _)
    (Dvd.dvd.mul_right (Dvd.dvd.mul_right hc2 _) _)

/-- `u ≡ 2 (mod 3)`, the only case where the two terms must cancel.  The six factors are
congruent to `2, 1, 1` and `1, 2, 2` modulo three, so the sum is `2 + 4 = 6 ≡ 0`.  This is the
one place `a mod 9` is used, and hence the one place the original premise is needed rather than
Gate G0's conclusion. -/
theorem gate_G3_two (u v a : ℕ) (hu : u = 3 * v + 2) (Q : ℤ) (hQ : S (2 * u + 3) 3 = 3 * Q)
    (h3 : (3 : ℤ) ∣ (a : ℤ) - 2) (h9 : (9 : ℤ) ∣ (a : ℤ) + 1) :
    (3 : ℤ) ∣ (2 * (u : ℤ) + 4) * A1 a * Q + c2 (2 * u + 2) * A2 a * S (2 * u + 2) 3 := by
  subst hu
  have i1 : 2 * (3 * v + 2) + 3 = 6 * v + 7 := by ring
  have i2 : 2 * (3 * v + 2) + 2 = 6 * v + 6 := by ring
  have i3 : (2 * ((3 * v + 2 : ℕ) : ℤ) + 4) = 6 * (v : ℤ) + 8 := by push_cast; ring
  rw [i1] at hQ
  rw [i2, i3]
  have e1 : (2 : ℤ) ≡ 6 * (v : ℤ) + 8 [ZMOD 3] :=
    Int.modEq_iff_dvd.mpr ⟨2 * (v : ℤ) + 2, by ring⟩
  have e2 : (1 : ℤ) ≡ A1 a [ZMOD 3] := Int.modEq_iff_dvd.mpr (A1_mod_three_of h3)
  have e3 : (1 : ℤ) ≡ Q [ZMOD 3] := by
    refine Int.modEq_iff_dvd.mpr ?_
    have hnine : (9 : ℤ) ∣ S (6 * v + 7) 3 - 3 := by
      rw [S_three]
      have h1 : (9 : ℤ) ∣ 2 ^ (6 * v + 7) - 2 ^ 7 := two_pow_mod_nine v 7
      have h2 : (9 : ℤ) ∣ (3 : ℤ) ^ (6 * v + 7) :=
        dvd_trans (by norm_num : (9 : ℤ) ∣ (3 : ℤ) ^ 2) (pow_dvd_pow 3 (by omega))
      have he : (1 : ℤ) + 2 ^ (6 * v + 7) + 3 ^ (6 * v + 7) - 3
          = (2 ^ (6 * v + 7) - 2 ^ 7) + (2 ^ 7 - 2) + 3 ^ (6 * v + 7) := by ring
      rw [he]
      exact dvd_add (dvd_add h1 ⟨14, by norm_num⟩) h2
    rw [hQ] at hnine
    obtain ⟨c, hc⟩ := hnine
    exact ⟨c, by linarith⟩
  have e4 : (1 : ℤ) ≡ c2 (6 * v + 6) [ZMOD 3] := by
    refine Int.modEq_iff_dvd.mpr (three_dvd_of_dvd_two_mul ?_)
    have he : 2 * (c2 (6 * v + 6) - 1) = 2 * c2 (6 * v + 6) - 2 := by ring
    rw [he, two_mul_c2]
    push_cast
    exact ⟨12 * (v : ℤ) ^ 2 + 30 * (v : ℤ) + 18, by ring⟩
  have e5 : (2 : ℤ) ≡ A2 a [ZMOD 3] := Int.modEq_iff_dvd.mpr (A2_mod_three_of h9)
  have e6 : (2 : ℤ) ≡ S (6 * v + 6) 3 [ZMOD 3] := by
    refine Int.modEq_iff_dvd.mpr ?_
    rw [S_three]
    have h1 : (3 : ℤ) ∣ 2 ^ (2 * (3 * v + 3) + 0) - 2 ^ 0 := two_pow_mod_three (3 * v + 3) 0
    have hidx : 2 * (3 * v + 3) + 0 = 6 * v + 6 := by ring
    rw [hidx] at h1
    have h2 : (3 : ℤ) ∣ (3 : ℤ) ^ (6 * v + 6) := dvd_pow_self 3 (by omega)
    have he : (1 : ℤ) + 2 ^ (6 * v + 6) + 3 ^ (6 * v + 6) - 2
        = (2 ^ (6 * v + 6) - 2 ^ 0) + (2 ^ 0 - 1) + 3 ^ (6 * v + 6) := by ring
    rw [he]
    exact dvd_add (dvd_add h1 ⟨0, by norm_num⟩) h2
  have hcomb := Int.ModEq.add ((e1.mul e2).mul e3) ((e4.mul e5).mul e6)
  have h6 : (2 : ℤ) * 1 * 1 + 1 * 2 * 2 = 6 := by norm_num
  rw [h6] at hcomb
  have h60 : (6 : ℤ) ≡ 0 [ZMOD 3] := by decide
  exact Int.modEq_zero_iff_dvd.mp (hcomb.symm.trans h60)

/-- **Gate G3.**  The whole `p = 3` correction is divisible by `27`.  The hypothesis `h9` is
demanded only in the residue class where it is actually used. -/
theorem gate_G3 (u a : ℕ) (h3 : (3 : ℤ) ∣ (a : ℤ) - 2)
    (h9 : u % 3 = 2 → (9 : ℤ) ∣ (a : ℤ) + 1) :
    (27 : ℤ) ∣ 3 * ((2 * (u : ℤ) + 4) * A1 a * S (2 * u + 3) 3)
      + 9 * (c2 (2 * u + 2) * A2 a * S (2 * u + 2) 3) := by
  have hS3 : (3 : ℤ) ∣ S (2 * u + 3) 3 := by
    rw [S_three]
    have h1 : (3 : ℤ) ∣ 2 ^ (2 * u + 3) - 2 ^ 3 := two_pow_mod_three u 3
    have h2 : (3 : ℤ) ∣ (3 : ℤ) ^ (2 * u + 3) := dvd_pow_self 3 (by omega)
    have he : (1 : ℤ) + 2 ^ (2 * u + 3) + 3 ^ (2 * u + 3)
        = (2 ^ (2 * u + 3) - 2 ^ 3) + (2 ^ 3 + 1) + 3 ^ (2 * u + 3) := by ring
    rw [he]
    exact dvd_add (dvd_add h1 ⟨3, by norm_num⟩) h2
  obtain ⟨Q, hQ⟩ := hS3
  suffices hX : (3 : ℤ) ∣ (2 * (u : ℤ) + 4) * A1 a * Q
      + c2 (2 * u + 2) * A2 a * S (2 * u + 2) 3 by
    obtain ⟨Y, hY⟩ := hX
    refine ⟨Y, ?_⟩
    rw [hQ]
    linear_combination 9 * hY
  obtain ⟨v, w, hw, hu⟩ : ∃ v w, w < 3 ∧ u = 3 * v + w :=
    ⟨u / 3, u % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have hw3 : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases hw3 with rfl | rfl | rfl
  · exact gate_G3_zero u v a (by omega) Q hQ
  · exact gate_G3_one u v a (by omega) Q
  · exact gate_G3_two u v a (by omega) Q hQ h3 (h9 (by omega))

/-! ### Gate G5: the exponent two

The source disposes of `n = 2` by observing that `p - 1 ∣ 2` restricts every prime divisor of `k`
to `2` or `3`, then enumerating the squarefree `k` built from those.  There is a shorter route.
Multiplying the premise by six and using `6 S₂(k) = 2k³ + 3k² + k` gives `k² ∣ 11k + 6` outright,
which bounds `k ≤ 11` with no reference to primes, squarefreeness, or the structure of `k` at all.
Eleven cases then remain and each is a numeric check. -/

theorem six_mul_S_two (m : ℕ) : 6 * S 2 m = 2 * (m : ℤ) ^ 3 + 3 * (m : ℤ) ^ 2 + (m : ℤ) := by
  induction m with
  | zero => simp [S_def]
  | succ m ih =>
    rw [S_succ]
    push_cast
    linear_combination ih

/-- **At `n = 2` the premise bounds `k`.**  Six times the premise is `k² ∣ 11k + 6` modulo a
multiple of `k²`, and `11k + 6` is positive, so `k² ≤ 11k + 6`. -/
theorem two_case_bound {k : ℕ} (hk : 0 < k)
    (hpre : (k : ℤ) ^ 2 ∣ ((k : ℤ) + 1) ^ 2 - S 2 k) : k ≤ 11 := by
  have h2 : (k : ℤ) ^ 2 ∣ 6 * (((k : ℤ) + 1) ^ 2 - S 2 k) := Dvd.dvd.mul_left hpre 6
  have he : 6 * (((k : ℤ) + 1) ^ 2 - S 2 k)
      = (11 * (k : ℤ) + 6) + (k : ℤ) ^ 2 * (3 - 2 * (k : ℤ)) := by
    linear_combination (-1 : ℤ) * six_mul_S_two k
  rw [he] at h2
  have hsq : (k : ℤ) ^ 2 ∣ (k : ℤ) ^ 2 * (3 - 2 * (k : ℤ)) := ⟨3 - 2 * (k : ℤ), rfl⟩
  have h5 := dvd_sub h2 hsq
  have h6 : ((11 * (k : ℤ) + 6) + (k : ℤ) ^ 2 * (3 - 2 * (k : ℤ)))
      - (k : ℤ) ^ 2 * (3 - 2 * (k : ℤ)) = 11 * (k : ℤ) + 6 := by ring
  rw [h6] at h5
  by_contra hcon
  push_neg at hcon
  have hk12 : (12 : ℤ) ≤ (k : ℤ) := by omega
  have hpos : (0 : ℤ) < 11 * (k : ℤ) + 6 := by linarith
  have hle := Int.le_of_dvd hpos h5
  nlinarith [hle, hk12]

/-! ### The premise modulo nine

The `u ≡ 2` branch of Gate G3 is the only place `a mod 9` is needed, and it is the only place the
ORIGINAL premise is used rather than Gate G0's conclusion.  Three reductions modulo nine —
the binomial expansion of `(3a+1)^n`, the block expansion, and the closed form of `S n 3` —
combine to give `a ≡ -1 (mod 9)`. -/

theorem three_dvd_S_odd (m : ℕ) : (3 : ℤ) ∣ S (2 * m + 3) 3 := by
  rw [S_three]
  have h1 : (3 : ℤ) ∣ 2 ^ (2 * m + 3) - 2 ^ 3 := two_pow_mod_three m 3
  have h2 : (3 : ℤ) ∣ (3 : ℤ) ^ (2 * m + 3) := dvd_pow_self 3 (by omega)
  have he : (1 : ℤ) + 2 ^ (2 * m + 3) + 3 ^ (2 * m + 3)
      = (2 ^ (2 * m + 3) - 2 ^ 3) + (2 ^ 3 + 1) + 3 ^ (2 * m + 3) := by ring
  rw [he]
  exact dvd_add (dvd_add h1 ⟨3, by norm_num⟩) h2

theorem three_dvd_S_shift (v : ℕ) : (3 : ℤ) ∣ S (6 * v + 6 + 1) 3 := by
  have h := three_dvd_S_odd (3 * v + 2)
  have hi : 2 * (3 * v + 2) + 3 = 6 * v + 6 + 1 := by ring
  rwa [hi] at h

/-- The block expansion at `p = 3`, reduced modulo nine: both corrections carry a factor `9`
once `3 ∣ S (N+1) 3`. -/
theorem block_three_mod_nine (N a : ℕ) (h3 : (3 : ℤ) ∣ S (N + 1) 3) :
    (9 : ℤ) ∣ S (N + 2) (a * 3) - (a : ℤ) * S (N + 2) 3 := by
  obtain ⟨c, hc⟩ := block_congr N 3 a
  obtain ⟨d, hd⟩ := h3
  rw [hd] at hc
  refine ⟨3 * c + ((N : ℤ) + 2) * A1 a * d + c2 N * A2 a * S N 3, ?_⟩
  push_cast at hc
  linear_combination hc

theorem pow_three_a_mod_nine (a m : ℕ) :
    (9 : ℤ) ∣ (3 * (a : ℤ) + 1) ^ (m + 1) - (1 + ((m : ℤ) + 1) * (3 * (a : ℤ))) := by
  have hb := binom_trunc2 (3 * (a : ℤ)) 1 m
  have hx : (9 : ℤ) ∣ (3 * (a : ℤ)) ^ 2 := ⟨(a : ℤ) ^ 2, by ring⟩
  have h := hx.trans hb
  have he : (3 * (a : ℤ) + 1) ^ (m + 1)
        - ((1 : ℤ) ^ (m + 1) + ((m : ℤ) + 1) * (3 * (a : ℤ)) * 1 ^ m)
      = (3 * (a : ℤ) + 1) ^ (m + 1) - (1 + ((m : ℤ) + 1) * (3 * (a : ℤ))) := by
    simp
  rwa [he] at h

/-- **The premise modulo nine pins `a`.**  With `n = 6v + 8` (that is, `n ≡ 2 mod 6`), the premise
forces `a ≡ -1 (mod 9)`. -/
theorem premise_mod_nine (v a : ℕ)
    (hpre : ((a * 3 : ℕ) : ℤ) ^ 2 ∣ (((a * 3 : ℕ) : ℤ) + 1) ^ (6 * v + 8)
        - S (6 * v + 8) (a * 3)) :
    (9 : ℤ) ∣ (a : ℤ) + 1 := by
  have hk9 : (9 : ℤ) ∣ ((a * 3 : ℕ) : ℤ) ^ 2 := by
    push_cast
    exact ⟨(a : ℤ) ^ 2, by ring⟩
  have hP := hk9.trans hpre
  have hE : (9 : ℤ) ∣ (((a * 3 : ℕ) : ℤ) + 1) ^ (6 * v + 8)
      - (1 + ((6 * v + 8 : ℕ) : ℤ) * (3 * (a : ℤ))) := by
    have h := pow_three_a_mod_nine a (6 * v + 7)
    have he : (3 * (a : ℤ) + 1) ^ (6 * v + 7 + 1)
          - (1 + (((6 * v + 7 : ℕ) : ℤ) + 1) * (3 * (a : ℤ)))
        = (((a * 3 : ℕ) : ℤ) + 1) ^ (6 * v + 8)
          - (1 + ((6 * v + 8 : ℕ) : ℤ) * (3 * (a : ℤ))) := by
      push_cast
      ring
    rwa [he] at h
  have hB : (9 : ℤ) ∣ S (6 * v + 8) (a * 3) - (a : ℤ) * S (6 * v + 8) 3 := by
    have h := block_three_mod_nine (6 * v + 6) a (three_dvd_S_shift v)
    have hi : 6 * v + 6 + 2 = 6 * v + 8 := by ring
    rwa [hi] at h
  have D1 : (9 : ℤ) ∣ (1 + ((6 * v + 8 : ℕ) : ℤ) * (3 * (a : ℤ)))
      - (a : ℤ) * S (6 * v + 8) 3 := by
    have he : (1 + ((6 * v + 8 : ℕ) : ℤ) * (3 * (a : ℤ))) - (a : ℤ) * S (6 * v + 8) 3
        = -((((a * 3 : ℕ) : ℤ) + 1) ^ (6 * v + 8)
              - (1 + ((6 * v + 8 : ℕ) : ℤ) * (3 * (a : ℤ))))
          + ((((a * 3 : ℕ) : ℤ) + 1) ^ (6 * v + 8) - S (6 * v + 8) (a * 3))
          + (S (6 * v + 8) (a * 3) - (a : ℤ) * S (6 * v + 8) 3) := by ring
    rw [he]
    exact dvd_add (dvd_add (dvd_neg.mpr hE) hP) hB
  have h2n : (9 : ℤ) ∣ 2 ^ (6 * v + 8) - 4 := by
    have h := two_pow_mod_nine v 8
    have he : (2 : ℤ) ^ (6 * v + 8) - 4
        = (2 ^ (6 * v + 8) - 2 ^ 8) + (2 ^ 8 - 4) := by ring
    rw [he]
    exact dvd_add h ⟨28, by norm_num⟩
  have h3n : (9 : ℤ) ∣ (3 : ℤ) ^ (6 * v + 8) :=
    dvd_trans (by norm_num : (9 : ℤ) ∣ (3 : ℤ) ^ 2) (pow_dvd_pow 3 (by omega))
  have hn3 : (9 : ℤ) ∣ ((6 * v + 8 : ℕ) : ℤ) * 3 - 6 := by
    push_cast
    exact ⟨2 * (v : ℤ) + 2, by ring⟩
  have final : (a : ℤ) + 1
      = ((1 + ((6 * v + 8 : ℕ) : ℤ) * (3 * (a : ℤ))) - (a : ℤ) * S (6 * v + 8) 3)
        - (a : ℤ) * (((6 * v + 8 : ℕ) : ℤ) * 3 - 6)
        + (a : ℤ) * (2 ^ (6 * v + 8) - 4)
        + (a : ℤ) * 3 ^ (6 * v + 8) := by
    rw [S_three]
    ring
  rw [final]
  exact dvd_add (dvd_add (dvd_sub D1 (Dvd.dvd.mul_left hn3 _)) (Dvd.dvd.mul_left h2n _))
    (Dvd.dvd.mul_left h3n _)

/-! ### The assembly -/

/-- **MathDB #320644: Conjecture 2 of Sondow–MacMillan.**  If `S n k ≡ (k+1)^n (mod k²)` then
for every prime `p` dividing `k`, `S n k ≡ (k/p) · S n p (mod p³)`.

The case structure follows the source.  `a = k/p = 1` is trivial and is taken first, which is
what makes the small-exponent cases finite rather than a squarefreeness argument: for odd `n` and
for `n = 2` the premise forces `a = 1`, so nothing else is left to prove.  For even `n ≥ 4` the
block expansion reduces everything to the three gates. -/
theorem sondow_macmillan (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hpk : p ∣ k)
    (hpre : (k : ℤ) ^ 2 ∣ ((k : ℤ) + 1) ^ n - S n k) :
    (p : ℤ) ^ 3 ∣ S n k - ((k / p : ℕ) : ℤ) * S n p := by
  obtain ⟨a, hka⟩ := hpk
  have hk : k = a * p := by rw [hka]; ring
  have hdiv : k / p = a := by rw [hk]; exact Nat.mul_div_cancel _ hp.pos
  rw [hdiv]
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [hk]
    simp
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      rw [S_def] at hpre
      simp at hpre
    · exact h
  obtain ⟨hpn, hamod⟩ := gate_G0 hn hp hk hpre
  rcases Nat.even_or_odd n with hev | hod
  · -- `n` even
    obtain ⟨mm, hmm⟩ := hev
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · -- `n = 2`: the premise bounds `k`, and every surviving value forces `a = 1`
      exfalso
      have hn2 : n = 2 := by omega
      subst hn2
      have hb := two_case_bound hk0 hpre
      interval_cases k
      · have h1 : p ∣ 1 := ⟨a, hka⟩
        have h2 := Nat.le_of_dvd one_pos h1
        have h3 := hp.two_le
        omega
      · have h2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨a, hka⟩
        have h3 := hp.two_le
        have hpe : p = 2 := by omega
        subst hpe
        omega
      all_goals (norm_num [S_def, Finset.sum_range_succ] at hpre)
    · -- `n ≥ 4` even
      obtain ⟨u, hu⟩ : ∃ u, n = 2 * u + 4 := ⟨(n - 4) / 2, by omega⟩
      subst hu
      rcases Nat.lt_or_ge p 5 with hplt | hpge
      · have hp2 := hp.two_le
        interval_cases p
        · -- `p = 2`
          rw [hk, S_two]
          have h8 : (8 : ℤ) ∣ 2 ^ (2 * u + 4) :=
            dvd_trans (by norm_num : (8 : ℤ) ∣ (2 : ℤ) ^ 3) (pow_dvd_pow 2 (by omega))
          obtain ⟨c, hc⟩ := gate_G4 a u
          obtain ⟨d, hd⟩ := h8
          refine ⟨c - (a : ℤ) * d, ?_⟩
          have h23 : ((2 : ℕ) : ℤ) ^ 3 = 8 := by norm_num
          rw [h23, hd]
          linear_combination hc
        · -- `p = 3`
          have h3 : (3 : ℤ) ∣ (a : ℤ) - 2 := by
            refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) - 2) 3).mp ?_
            push_cast
            rw [hamod]
            decide
          have h9 : u % 3 = 2 → (9 : ℤ) ∣ (a : ℤ) + 1 := by
            intro hu3
            obtain ⟨v, hv⟩ : ∃ v, u = 3 * v + 2 := ⟨u / 3, by omega⟩
            refine premise_mod_nine v a ?_
            have hi : 6 * v + 8 = 2 * u + 4 := by omega
            rw [hi, ← hk]
            exact hpre
          rw [hk]
          obtain ⟨c, hc⟩ := block_congr (2 * u + 2) 3 a
          obtain ⟨e, he⟩ := gate_G3 u a h3 h9
          have i1 : 2 * u + 2 + 2 = 2 * u + 4 := by ring
          have i2 : 2 * u + 2 + 1 = 2 * u + 3 := by ring
          rw [i1, i2] at hc
          have h33 : ((3 : ℕ) : ℤ) ^ 3 = 27 := by norm_num
          rw [h33]
          refine ⟨c + e, ?_⟩
          push_cast at hc
          linear_combination hc + he
        · exact absurd hp (by decide)
      · -- `p ≥ 5`
        obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        subst hq
        have hq4 : 4 ≤ q := by omega
        have hdvdq : q ∣ 2 * u + 4 := by simpa using hpn
        obtain ⟨hg1, hg2⟩ := gate_G2 q u hp hq4 hdvdq
        rw [hk]
        obtain ⟨c, hc⟩ := block_congr (2 * u + 2) (q + 1) a
        obtain ⟨d1, hd1⟩ := hg1
        obtain ⟨d2, hd2⟩ := hg2
        have i1 : 2 * u + 2 + 2 = 2 * u + 4 := by ring
        have i2 : 2 * u + 2 + 1 = 2 * u + 3 := by ring
        rw [i1, i2, hd1, hd2] at hc
        refine ⟨c + ((2 * (u : ℤ) + 4) * A1 a * d2 + c2 (2 * u + 2) * A2 a * d1), ?_⟩
        push_cast at hc ⊢
        linear_combination hc
  · -- `n` odd: the premise forces `a = 1`, contradicting the branch hypothesis
    exfalso
    have key : ∀ l : ℕ, l.Prime → l ∣ k → l = 2 := by
      intro l hl hlk
      rcases hl.eq_two_or_odd' with h2 | hodd
      · exact h2
      · exfalso
        obtain ⟨b, hb⟩ := hlk
        have hkb : k = b * l := by rw [hb]; ring
        obtain ⟨hln, -⟩ := gate_G0 hn hl hkb hpre
        obtain ⟨cc, hcc⟩ := hodd
        have h2l : 2 ∣ l - 1 := ⟨cc, by omega⟩
        have h2n : 2 ∣ n := h2l.trans hln
        obtain ⟨dd, hdd⟩ := hod
        omega
    have hp2 : p = 2 := key p hp ⟨a, hka⟩
    obtain ⟨l, hl, hla⟩ := Nat.exists_prime_and_dvd ha1
    have hl2 : l = 2 := key l hl (hla.trans ⟨p, hk⟩)
    subst hp2
    have h2a : (2 : ℕ) ∣ a := hl2 ▸ hla
    have hz : (a : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff a 2).mpr h2a
    rw [hz] at hamod
    exact absurd hamod (by decide)

end Principia.MathDB.P320644
