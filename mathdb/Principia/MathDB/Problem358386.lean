import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# MathDB #358386 — Billey–Swanson Conjecture 48 is FALSE, unconditionally

Write-up: `mathdb-open-problems/problems/358386/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-28 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: S. C. Billey and J. P. Swanson, *Cyclotomic Generating Functions*, **Conjecture 48**
(arXiv:2305.07620v3): *every nonconstant unimodal basic cyclotomic generating function has a
factor `Φ_p` for some prime `p`.*

A *basic cyclotomic generating function* is a monic polynomial with constant term `1`, nonnegative
integer coefficients, and all roots roots of unity; `Φᵘⁿᶦ` is the monoid of the unimodal ones.

**The counterexample is the write-up's own:**

`F = Φ₄ ^ 7 * Φ₉ ^ 4 * Φ₂₅ * Φ₃₀`,   of degree `66`.

`conjecture_48_false` carries **no hypotheses**: the 67-coefficient table is computed inside Lean,
not assumed.

## The two halves, and why the computational half turned out to be cheap

The **structural** half needs no computation at all. `ℤ[X]` is a UFD and every `Φₙ` is irreducible,
so a prime-index factor of `F` would have to be *associated* to one of `Φ₄`, `Φ₉`, `Φ₂₅`, `Φ₃₀`;
monic associates are equal, and `cyclotomic_injective` then forces `p ∈ {4, 9, 25, 30}`, none of
which is prime (`no_prime_cyclotomic_factor`).

The **computational** half is the write-up's table

`1, 1, 7, 10, 24, 42, 63, 105, 147, 198, 283, …, 1810, …, 7, 1, 1`   (palindromic, peak at `33`),

and the honest expectation was that it could not be done in Lean: `Polynomial` is a quotient of
`Finsupp`, so it does not kernel-reduce and neither `decide` nor `native_decide` can evaluate
`F.coeff 33`. **That expectation was wrong, and it was worth measuring before believing.** The
route that works takes the coefficients out of the kernel entirely:

1. Each factor gets an **explicit** form (`cyclotomic_four`, `_nine`, `_twentyfive`, `_fifteen`,
   `_thirty`). The prime powers come straight from `cyclotomic_prime_pow_eq_geom_sum`; `Φ₁₅` and
   `Φ₃₀` come from `cyclotomic_expand_eq_cyclotomic_mul` by cancelling a nonzero factor — a two-rung
   ladder `Φ₅ → Φ₁₅ → Φ₃₀` rather than the eight-way divisor product, because `expand` turns
   `X ↦ X ^ p` and `15 = 5 · 3`, `30 = 15 · 2`.
2. `F_eq_sum` equates that product with `∑ i ∈ range 67, C (cf i) * X ^ i` — **one `ring` call**,
   which expands a degree-66 product in about 45 s. `ring` normalises in the commutative ring
   `ℤ[X]` with `X` as an atom, so it never needs `Polynomial` to reduce.
3. `coeff_sum_range` reads a single coefficient off that sum, so `F_coeff : F.coeff k = cf k` holds
   for **every** `k` — above the degree both sides are `0`.
4. `cf` is a `List.getD`, which *does* kernel-reduce, so the 33 rising and 32 falling steps are
   `decide`.

So nothing here is an axiom, a `sorry`, or a carried hypothesis, and no new Mathlib theory was
needed — only the observation that `ring` and `decide` operate on different representations and the
work should be handed to whichever one can see it.

## Two places where the encoding matters

**`Unimodal` is stated as the property, not as the route.** `∃ m`, nondecreasing up to `m` and
nonincreasing after — quantified over all of `ℕ`, so the tail beyond the degree is included rather
than tacitly ignored. `unimodal_of_step` supplies it from consecutive steps alone, and
`nonneg_of_unimodal` shows **coefficient nonnegativity is not a separate obligation**: below the
peak every coefficient dominates `coeff 0`, above it every coefficient dominates one beyond the
degree, which is `0`. Both lemmas are campaign-agnostic and belong in `Common/` if anything else
needs them.

**"All roots are roots of unity" is stated as "is a product of cyclotomic polynomials"**
(`IsCyclotomicProduct`), which for a monic integer polynomial is equivalent — the minimal
polynomial of a primitive `d`-th root of unity **is** `Φ_d` — and is also what makes `Φᵘⁿᶦ` a
monoid, which is how the source uses it. *Divisibility of `X ^ N - 1` would be the wrong encoding*:
`X ^ N - 1` is squarefree, so it is not divisible by `Φ₄ ^ 7`, yet every root of `Φ₄ ^ 7` is
certainly a root of unity.

## What the verifier found that the write-up does not say

`Campaigns/MathDB-Formalization/verify_358386.py` checks the table in exact integer arithmetic by
two independent expansions (direct, and the write-up's own `b`-recurrence), and its 34 tabulated
values agree with the write-up exactly. Its negative controls also establish something the write-up
leaves implicit: **`Φ₄ ^ 7 * Φ₉ ^ 4 * Φ₂₅` — the product without `Φ₃₀` — is not unimodal**, so the
`Φ₃₀` factor is load-bearing for the counterexample rather than incidental. The `ring` expansion
here was likewise given a negative control: perturbing coefficient 33 by one makes the call fail.
-/

namespace Principia.MathDB.P358386

open Polynomial

/-- A polynomial's coefficient sequence is **unimodal**: nondecreasing up to some index and
nonincreasing after it. -/
def Unimodal (p : ℤ[X]) : Prop :=
  ∃ m : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ m → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, m ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)

/-- `p` is a product of cyclotomic polynomials — the encoding of *"all roots are roots of unity"*
for a monic integer polynomial; see the module header. -/
def IsCyclotomicProduct (p : ℤ[X]) : Prop :=
  ∃ s : Multiset ℕ, (∀ d ∈ s, 0 < d) ∧ p = (s.map fun d => cyclotomic d ℤ).prod

/-- A **basic cyclotomic generating function** (Billey–Swanson): monic, constant term `1`,
nonnegative coefficients, every root a root of unity. -/
structure BasicCGF (p : ℤ[X]) : Prop where
  monic : p.Monic
  coeff_zero : p.coeff 0 = 1
  coeff_nonneg : ∀ i, 0 ≤ p.coeff i
  cyclotomicProduct : IsCyclotomicProduct p

/-- Membership in the monoid `Φᵘⁿᶦ` of the write-up: a unimodal basic cyclotomic generating
function. -/
def MemPhiUni (p : ℤ[X]) : Prop := BasicCGF p ∧ Unimodal p

/-! ### Campaign-agnostic lemmas about `Unimodal` -/

/-- Unimodality follows from **consecutive** steps alone: rising below `m`, falling from `m` on. -/
theorem unimodal_of_step {p : ℤ[X]} {m : ℕ}
    (hup : ∀ i, i < m → p.coeff i ≤ p.coeff (i + 1))
    (hdown : ∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i) : Unimodal p := by
  refine ⟨m, ?_, ?_⟩
  · intro i j hij hjm
    induction j with
    | zero =>
        have : i = 0 := Nat.le_zero.mp hij
        subst this; exact le_refl _
    | succ n ih =>
        rcases Nat.lt_or_ge i (n + 1) with h | h
        · have hin : i ≤ n := Nat.lt_succ_iff.mp h
          exact le_trans (ih hin (le_trans (Nat.le_succ n) hjm))
            (hup n (lt_of_lt_of_le (Nat.lt_succ_self n) hjm))
        · have : i = n + 1 := le_antisymm hij h
          subst this; exact le_refl _
  · intro i j hmi hij
    induction j with
    | zero =>
        have : i = 0 := Nat.le_zero.mp hij
        subst this; exact le_refl _
    | succ n ih =>
        rcases Nat.lt_or_ge i (n + 1) with h | h
        · have hin : i ≤ n := Nat.lt_succ_iff.mp h
          exact le_trans (hdown n (le_trans hmi hin)) (ih hin)
        · have : i = n + 1 := le_antisymm hij h
          subst this; exact le_refl _

/-- **Nonnegativity is a consequence of unimodality**, given a nonnegative constant term: below the
peak every coefficient dominates `coeff 0`, and above it every coefficient dominates one beyond the
degree, which vanishes. -/
theorem nonneg_of_unimodal {p : ℤ[X]} (h : Unimodal p) (h0 : 0 ≤ p.coeff 0) :
    ∀ i, 0 ≤ p.coeff i := by
  obtain ⟨m, hup, hdown⟩ := h
  intro i
  rcases le_or_gt i m with hi | hi
  · exact le_trans h0 (hup 0 i (Nat.zero_le i) hi)
  · have hj : p.coeff (max (p.natDegree + 1) i) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
    have := hdown i (max (p.natDegree + 1) i) (le_of_lt hi) (le_max_right _ _)
    rw [hj] at this
    exact this

/-- A coefficient of an explicitly indexed sum, read off directly. -/
theorem coeff_sum_range (f : ℕ → ℤ) (n k : ℕ) (hk : k < n) :
    (∑ i ∈ Finset.range n, C (f i) * X ^ i).coeff k = f k := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_range.mpr hk) h

/-! ### The explicit form of each factor

The prime powers come straight from the geometric-sum formula; `Φ₁₅` and `Φ₃₀` come from `expand`
(which sends `X ↦ X ^ p`) by cancelling a nonzero factor. -/

theorem cyclotomic_four : cyclotomic 4 ℤ = X ^ 2 + 1 := by
  have h : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ]
  ring

theorem cyclotomic_nine : cyclotomic 9 ℤ = X ^ 6 + X ^ 3 + 1 := by
  have h : (9 : ℕ) = 3 ^ (1 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_three]
  simp [Finset.sum_range_succ]
  ring

theorem cyclotomic_twentyfive :
    cyclotomic 25 ℤ = X ^ 20 + X ^ 15 + X ^ 10 + X ^ 5 + 1 := by
  have h : (25 : ℕ) = 5 ^ (1 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum (by norm_num)]
  simp [Finset.sum_range_succ]
  ring

theorem cyclotomic_fifteen :
    cyclotomic 15 ℤ = X ^ 8 - X ^ 7 + X ^ 5 - X ^ 4 + X ^ 3 - X + 1 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 5 ℤ)
  rw [show (15 : ℕ) = 5 * 3 by rfl,
    ← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_three (by norm_num1) ℤ]
  have h5 : cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  rw [h5]
  simp [map_add, map_pow, expand_X, map_one]
  ring

theorem cyclotomic_thirty :
    cyclotomic 30 ℤ = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 15 ℤ)
  rw [show (30 : ℕ) = 15 * 2 by rfl,
    ← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two (by norm_num1) ℤ, cyclotomic_fifteen]
  simp [map_add, map_sub, map_pow, expand_X, map_one]
  ring

/-! ## The witness -/

/-- The write-up's counterexample. -/
noncomputable def F : ℤ[X] :=
  (cyclotomic 4 ℤ) ^ 7 * (cyclotomic 9 ℤ) ^ 4 * cyclotomic 25 ℤ * cyclotomic 30 ℤ

theorem F_monic : F.Monic := by
  unfold F
  exact (((((cyclotomic.monic 4 ℤ).pow 7).mul ((cyclotomic.monic 9 ℤ).pow 4)).mul
    (cyclotomic.monic 25 ℤ)).mul (cyclotomic.monic 30 ℤ))

/-- The constant term is `1`: each factor has constant term `1`, and `coeff 0 = eval 0` is
multiplicative. -/
theorem F_coeff_zero : F.coeff 0 = 1 := by
  have e : ∀ n : ℕ, 1 < n → (cyclotomic n ℤ).eval 0 = 1 := fun n hn => by
    rw [← coeff_zero_eq_eval_zero]; exact cyclotomic_coeff_zero ℤ hn
  have h4 := e 4 (by norm_num)
  have h9 := e 9 (by norm_num)
  have h25 := e 25 (by norm_num)
  have h30 := e 30 (by norm_num)
  rw [coeff_zero_eq_eval_zero]
  unfold F
  simp [eval_mul, eval_pow, h4, h9, h25, h30]

/-- Every root of `F` is a root of unity, in the product encoding. -/
theorem F_isCyclotomicProduct : IsCyclotomicProduct F := by
  refine ⟨Multiset.replicate 7 4 + Multiset.replicate 4 9 + {25} + {30}, ?_, ?_⟩
  · intro d hd
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton] at hd
    rcases hd with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl) | rfl <;> norm_num
  · rw [Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.prod_add,
      Multiset.prod_add, Multiset.prod_add, Multiset.map_replicate, Multiset.map_replicate,
      Multiset.prod_replicate, Multiset.prod_replicate, Multiset.map_singleton,
      Multiset.map_singleton, Multiset.prod_singleton, Multiset.prod_singleton]
    unfold F
    ring

/-- `deg F = 7·φ(4) + 4·φ(9) + φ(25) + φ(30) = 14 + 24 + 20 + 8 = 66`. -/
theorem F_natDegree : F.natDegree = 66 := by
  have m4 : ((cyclotomic 4 ℤ) ^ 7).Monic := (cyclotomic.monic 4 ℤ).pow 7
  have m9 : ((cyclotomic 9 ℤ) ^ 4).Monic := (cyclotomic.monic 9 ℤ).pow 4
  have m49 : ((cyclotomic 4 ℤ) ^ 7 * (cyclotomic 9 ℤ) ^ 4).Monic := m4.mul m9
  have m4925 : ((cyclotomic 4 ℤ) ^ 7 * (cyclotomic 9 ℤ) ^ 4 * cyclotomic 25 ℤ).Monic :=
    m49.mul (cyclotomic.monic 25 ℤ)
  unfold F
  rw [m4925.natDegree_mul (cyclotomic.monic 30 ℤ), m49.natDegree_mul (cyclotomic.monic 25 ℤ),
    m4.natDegree_mul m9, natDegree_pow, natDegree_pow, natDegree_cyclotomic,
    natDegree_cyclotomic, natDegree_cyclotomic, natDegree_cyclotomic]
  have t4 : Nat.totient 4 = 2 := by decide
  have t9 : Nat.totient 9 = 6 := by decide
  have t25 : Nat.totient 25 = 20 := by decide
  have t30 : Nat.totient 30 = 8 := by decide
  rw [t4, t9, t25, t30]

theorem F_nonconstant : F.natDegree ≠ 0 := by rw [F_natDegree]; norm_num

/-! ## The coefficient table, computed rather than assumed -/

/-- The 67 coefficients of `F`, lowest degree first. Independently reproduced in exact integer
arithmetic by `verify_358386.py`; the first 34 are the write-up's own table. -/
def tbl : List ℤ :=
  [1, 1, 7, 10, 24, 42, 63, 105, 147, 198, 283, 337, 437, 524, 592, 701, 763, 829, 920, 940,
   1025, 1058, 1109, 1184, 1220, 1319, 1381, 1450, 1570, 1588, 1704, 1737, 1746, 1810, 1746,
   1737, 1704, 1588, 1570, 1450, 1381, 1319, 1220, 1184, 1109, 1058, 1025, 940, 920, 829,
   763, 701, 592, 524, 437, 337, 283, 198, 147, 105, 63, 42, 24, 10, 7, 1, 1]

/-- The table as a total function: `0` beyond the degree, which is what `F.coeff` does too. -/
def cf (i : ℕ) : ℤ := tbl.getD i 0

theorem tbl_length : tbl.length = 67 := by decide

theorem cf_eq_zero {k : ℕ} (hk : 67 ≤ k) : cf k = 0 :=
  List.getD_eq_default _ _ (by rw [tbl_length]; exact hk)

set_option maxHeartbeats 4000000 in
-- The single `ring` call below expands a degree-66 product of four explicit factors into
-- 67 terms, which is well past the default budget.
/-- `F` in explicitly indexed form. The single `ring` call expands the degree-66 product; `ring`
works in the commutative ring `ℤ[X]` with `X` as an atom, so `Polynomial` is never asked to
reduce. -/
theorem F_eq_sum : F = ∑ i ∈ Finset.range 67, C (cf i) * X ^ i := by
  unfold F
  rw [cyclotomic_four, cyclotomic_nine, cyclotomic_twentyfive, cyclotomic_thirty]
  simp [Finset.sum_range_succ, cf, tbl, List.getD]
  ring

/-- Every coefficient of `F`, for every index. -/
theorem F_coeff (k : ℕ) : F.coeff k = cf k := by
  rcases lt_or_ge k 67 with hk | hk
  · rw [F_eq_sum]; exact coeff_sum_range cf 67 k hk
  · rw [cf_eq_zero hk]
    exact coeff_eq_zero_of_natDegree_lt (by rw [F_natDegree]; omega)

/-! The table itself, checked by kernel reduction: `cf` is a `List.getD`, which *does* reduce. -/

theorem cf_rising : ∀ i, i < 33 → cf i ≤ cf (i + 1) := by decide

theorem cf_falling : ∀ i, 33 ≤ i → i < 66 → cf (i + 1) ≤ cf i := by decide

theorem cf_nonneg : ∀ i, i < 67 → 0 ≤ cf i := by decide

/-- **`F` is unimodal**, with peak at index `33`. -/
theorem F_unimodal : Unimodal F := by
  refine unimodal_of_step (m := 33) ?_ ?_
  · intro i hi
    rw [F_coeff, F_coeff]
    exact cf_rising i hi
  · intro i hi
    rw [F_coeff, F_coeff]
    rcases lt_or_ge i 66 with h | h
    · exact cf_falling i hi h
    · rw [cf_eq_zero (by omega)]
      rcases lt_or_ge i 67 with h' | h'
      · exact cf_nonneg i h'
      · rw [cf_eq_zero h']

/-! ## The clause that refutes the conjecture, and it needs no computation -/

/-- If `Φ_p ∣ Φ_d` with `0 < p` and `0 < d`, then `p = d`: both are irreducible, so divisibility
forces associates, and monic associates are equal. -/
theorem cyclotomic_dvd_cyclotomic_iff_eq {p d : ℕ} (hp : 0 < p) (hd : 0 < d)
    (h : cyclotomic p ℤ ∣ cyclotomic d ℤ) : p = d := by
  have hassoc : Associated (cyclotomic p ℤ) (cyclotomic d ℤ) :=
    (cyclotomic.irreducible hp).associated_of_dvd (cyclotomic.irreducible hd) h
  have : cyclotomic p ℤ = cyclotomic d ℤ :=
    eq_of_monic_of_associated (cyclotomic.monic p ℤ) (cyclotomic.monic d ℤ) hassoc
  exact cyclotomic_injective this

/-- **THE REFUTING CLAUSE.**  `F` has no prime-index cyclotomic factor. -/
theorem no_prime_cyclotomic_factor {p : ℕ} (hp : p.Prime) : ¬ (cyclotomic p ℤ ∣ F) := by
  intro hdvd
  have hpirr : Irreducible (cyclotomic p ℤ) := cyclotomic.irreducible hp.pos
  have hprime : Prime (cyclotomic p ℤ) := hpirr.prime
  -- Split the product with primality, then strip the powers.
  have hfac : cyclotomic p ℤ ∣ cyclotomic 4 ℤ ∨ cyclotomic p ℤ ∣ cyclotomic 9 ℤ ∨
      cyclotomic p ℤ ∣ cyclotomic 25 ℤ ∨ cyclotomic p ℤ ∣ cyclotomic 30 ℤ := by
    unfold F at hdvd
    rcases (hprime.dvd_mul.mp hdvd) with h | h
    · rcases (hprime.dvd_mul.mp h) with h' | h'
      · rcases (hprime.dvd_mul.mp h') with h'' | h''
        · exact Or.inl (hprime.dvd_of_dvd_pow h'')
        · exact Or.inr (Or.inl (hprime.dvd_of_dvd_pow h''))
      · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h))
  -- Each case names `p`, and none of 4, 9, 25, 30 is prime.
  rcases hfac with h | h | h | h
  · have := cyclotomic_dvd_cyclotomic_iff_eq hp.pos (by norm_num) h
    subst this; norm_num at hp
  · have := cyclotomic_dvd_cyclotomic_iff_eq hp.pos (by norm_num) h
    subst this; norm_num at hp
  · have := cyclotomic_dvd_cyclotomic_iff_eq hp.pos (by norm_num) h
    subst this; norm_num at hp
  · have := cyclotomic_dvd_cyclotomic_iff_eq hp.pos (by norm_num) h
    subst this; norm_num at hp

/-! ## The refutation -/

/-- `F` is a basic cyclotomic generating function. Nonnegativity is *derived* from unimodality
rather than checked again. -/
theorem F_basicCGF : BasicCGF F where
  monic := F_monic
  coeff_zero := F_coeff_zero
  coeff_nonneg := nonneg_of_unimodal F_unimodal (by rw [F_coeff_zero]; norm_num)
  cyclotomicProduct := F_isCyclotomicProduct

theorem F_memPhiUni : MemPhiUni F := ⟨F_basicCGF, F_unimodal⟩

/-- **BILLEY–SWANSON CONJECTURE 48 IS FALSE.**  There is a nonconstant unimodal basic cyclotomic
generating function with no factor `Φ_p` for any prime `p`. No hypotheses. -/
theorem conjecture_48_false :
    ∃ p : ℤ[X], MemPhiUni p ∧ p.natDegree ≠ 0 ∧ ∀ q : ℕ, q.Prime → ¬ (cyclotomic q ℤ ∣ p) :=
  ⟨F, F_memPhiUni, F_nonconstant, fun _ hq => no_prime_cyclotomic_factor hq⟩

end Principia.MathDB.P358386
