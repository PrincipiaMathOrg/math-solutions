import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

set_option autoImplicit false

/-!
# MathDB #340544 — Soykan Conjecture 4.2, with the constant-coefficient hypothesis REMOVED

Write-up: `mathdb-open-problems/problems/340544/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-29 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: Y. Soykan, **Conjecture 4.2**: a polynomial identity in terms `H_{aᵢn+bᵢ}` of a
constant-coefficient recurrence sequence, valid for all sufficiently large integers `n`, is valid
for **every** integer `n`.

## What this module proves

The write-up's engine is the propagation step: a sequence on `ℤ` satisfying a monic
constant-coefficient recurrence **with nonzero constant coefficient** cannot vanish on a terminal
ray without vanishing everywhere, because the constant coefficient is what lets the recurrence be
run backwards. That engine is proved here in full — and with the hypothesis the write-up carries
throughout **removed**:

**`zero_of_eventually_zero` needs no assumption on the coefficients at all.** For a *bilateral*
sequence, monicity alone suffices. The reason is the write-up's own first observation, made into a
lemma (`BilatRec.shift`): if the lowest `t` coefficients vanish, substituting `n - t` for `n`
produces a monic recurrence of order `D - t` whose constant coefficient is `q t ≠ 0`. Iterating is
unnecessary — one shift lands on the least nonvanishing index — and if *every* coefficient vanishes
the relation reads `u (n + D) = 0` for all `n`, which already gives `u = 0`. So the normalisation
step the write-up performs on the annihilator (`P = x^t Q`, pass to `Q`) is not a preliminary to be
assumed away: **it is why the hypothesis is free.**

`zero_of_consecutive_zeros` is the write-up's corollary: `D` consecutive zeros anywhere force
`u = 0`, proved by running the recurrence forward off the block and then the above backwards.

`bilaterality_essential` is the matching fence: on `ℕ`-indexed sequences the statement is false, and
the witness is as small as it can be (`u 0 = 1`, `u n = 0` for `n ≥ 1`, satisfying `u (n+1) = 0` for
every `n : ℕ`). So the bilateral convention is not a convenience of the write-up's setup — it is
load-bearing, and this is the one-line proof that it is.

## THE LIFT IS PROVED, so the state form carries nothing

`liftGoal_holds` closes what this file previously named as its residue, and `stateSeq_eq_zero` is
therefore Soykan's statement in **state form** with no hypothesis beyond the eventual vanishing it
is given. Three steps got it there, and Mathlib had every ingredient:

* `tdeg_aeval_le` — **substituting linear forms cannot raise total degree.** This was the one
  ingredient the residue named as absent, and it is what makes `restrictTotalDegree` invariant
  under `P ↦ P ∘ A`. Proved by writing `P` over its support and bounding each monomial's image with
  `totalDegree_finsetProd` and `totalDegree_pow`.
* `bilatRec_orbitSeq` — **the orbit core, and it mentions nothing about this problem.** For a
  finite-dimensional `V`, an invertible `T : V ≃ₗ[K] V`, a vector `v` and any functional `φ`, the
  sequence `n ↦ φ (Tⁿ v)` satisfies a monic bilateral recurrence: `LinearMap.aeval_self_charpoly`
  supplies it, `LinearMap.charpoly_monic` makes it monic, and invertibility of `T` is what makes
  `Tⁿ` meaningful at negative `n`. **No condition on the constant coefficient is needed** — which
  is `zero_of_eventually_zero`'s strengthening paying for itself, because a monic recurrence with
  no coefficient condition is exactly what Cayley–Hamilton hands you. Had the write-up's hypothesis
  been carried into Lean, this step would have owed a determinant computation it does not owe.
* `linSubstE` and `linSubstE_zpow` — the automorphism of the bounded-degree space and the fact that
  its integer powers are `linSubst` of the matrix powers. `linSubst_comp` is an
  **anti**-homomorphism (`linSubst B ∘ linSubst B' = linSubst (B' * B)`), which is why the matrix
  powers emerge in the order they do; getting that backwards was two of the errors this stage cost.

## THE SOURCE CONJECTURE IS PROVED -- `conjecture_4_2`

Stage 3 closed the gap the section above described. `conjecture_4_2` is Soykan's Conjecture 4.2
verbatim: for a bilateral `H` satisfying a monic order-`kk+1` recurrence whose constant coefficient
is nonzero (the source's own hypothesis), arbitrary integer slopes `a` and shifts `b`, and any
polynomial `f`, if `f(H_{a1 n+b1}, ..., H_{ar n+br})` vanishes for all large `n` then it vanishes at
**every** integer. It carries nothing else.

The bridge is the companion matrix:

* `companion` and `companionInv` -- the matrix and its inverse, the latter read straight off the
  BACKWARD recurrence. That is the only place the nonzero constant coefficient is used and the only
  place anything is divided by. One entrywise identity (`companion_mul_inv`) plus
  `Matrix.isUnit_det_of_right_inverse` yields `companionGL`; **no determinant is ever expanded.**
* `companion_mulVec_stateVec` -- the state equation, which needs **only monicity**.
  `companionGL_inv_mulVec` runs it backwards with no separate computation, being the state equation
  composed with `A` inverse times `A = 1`, and `companionGL_zpow_mulVec` translates the state vector
  by an arbitrary **integer**.
* `blockGL` and `blockGL_coe_zpow` -- `r` arithmetic subsequences at once, as a block-diagonal stack
  of the powers `A ^ (a i)`, invertible blockwise; `blockDiagonal_mulVec_apply` reads one block off.
* `bilatRec_polySubseq` assembles these with `liftGoal_holds`, taking `F` to be `f` renamed along
  `i` mapsto `(0, i)` so that `MvPolynomial.eval_rename` converts the state-form statement into the
  literal one.

## THE WRITE-UP'S OWN THEOREM IS PROVED TOO -- `conjecture_4_2_multi`

Stage 4 closed the last open statement. `conjecture_4_2_multi` is the write-up's Theorem rather
than the source's conjecture: **several** bilateral sequences `H 1, ..., H r` of possibly
**different** orders, arbitrary integer slopes and shifts, any polynomial, any field. It is a
direct mirror of stage 3 over `Matrix.blockDiagonal'` with the dependent index type
`Sigma i, Fin (k i + 1)`, and it **compiled on the first attempt** -- which is the whole argument
for having built the uniform-size case first, since every primed lemma lines up one-for-one with
its unprimed counterpart.

`conjecture_4_2_of_lift` is therefore **subsumed** and is kept only as the typed interface that
stage 2 was written against; it is documentation of how the file was built, not an open obligation.
Nothing in this file is now hypothetical beyond the source's own conditions: a monic bilateral
recurrence per sequence whose constant coefficient is nonzero.

Nothing in this file mentions Tribonacci numbers, or indeed any particular sequence: `BilatRec` and
its four lemmas are campaign-agnostic and belong in `Principia/Common/`.
-/

namespace Principia.MathDB.P340544

variable {K : Type*} [Field K]

/-- `u : ℤ → K` satisfies the **monic** order-`D` constant-coefficient linear recurrence with lower
coefficients `q`, on all of `ℤ`.

This is the write-up's bilateral convention: the recurrence holds at every integer index, negative
indices being supplied by running it backwards. `zero_of_eventually_zero` is false without it —
see `bilaterality_essential`. -/
def BilatRec (D : ℕ) (q : ℕ → K) (u : ℤ → K) : Prop :=
  ∀ n : ℤ, u (n + (D : ℤ)) + ∑ k ∈ Finset.range D, q k * u (n + (k : ℤ)) = 0

/-- Running the recurrence **forwards**: monicity alone determines each term from the `D` before it,
so a block of `D` zeros propagates upward. -/
theorem BilatRec.forward {D : ℕ} {q : ℕ → K} {u : ℤ → K} (h : BilatRec D q u) (n : ℤ)
    (hz : ∀ k : ℕ, k < D → u (n + (k : ℤ)) = 0) : u (n + (D : ℤ)) = 0 := by
  have key := h n
  rw [Finset.sum_eq_zero fun k hk => by
    rw [hz k (Finset.mem_range.mp hk), mul_zero], add_zero] at key
  exact key

/-- **The normalisation, as a lemma.** If the lowest `t` coefficients vanish then the relation,
read at `n - t`, is a monic recurrence of order `D - t` whose lowest coefficient is `q t`.

This is the step the write-up performs on the annihilator before assuming a nonzero constant term;
making it a lemma is what lets `zero_of_eventually_zero` assume nothing. -/
theorem BilatRec.shift {D : ℕ} {q : ℕ → K} {u : ℤ → K} (h : BilatRec D q u) (t : ℕ) (ht : t ≤ D)
    (hlow : ∀ k : ℕ, k < t → q k = 0) : BilatRec (D - t) (fun j => q (t + j)) u := by
  intro n
  have hD : D = t + (D - t) := by omega
  have key := h (n - (t : ℤ))
  rw [hD, Finset.sum_range_add] at key
  rw [Finset.sum_eq_zero fun k hk => by
    rw [hlow k (Finset.mem_range.mp hk), zero_mul]] at key
  rw [zero_add] at key
  have e1 : n - (t : ℤ) + ((t + (D - t) : ℕ) : ℤ) = n + ((D - t : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e1] at key
  refine Eq.trans ?_ key
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

/-- Running the recurrence **backwards**, which needs the lowest coefficient to be invertible. -/
theorem BilatRec.backward {E : ℕ} {Q : ℕ → K} {u : ℤ → K} (h : BilatRec (E + 1) Q u)
    (hQ : Q 0 ≠ 0) (n : ℤ) (hz : ∀ j : ℕ, 1 ≤ j → j ≤ E + 1 → u (n + (j : ℤ)) = 0) : u n = 0 := by
  have key := h n
  rw [Finset.sum_range_succ'] at key
  have h1 : u (n + ((E + 1 : ℕ) : ℤ)) = 0 := hz (E + 1) (by omega) le_rfl
  have h2 : (∑ j ∈ Finset.range E, Q (j + 1) * u (n + ((j + 1 : ℕ) : ℤ))) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [hz (j + 1) (by omega) (by
        have := Finset.mem_range.mp hj
        omega)]
      exact mul_zero _
  rw [h1, h2, zero_add, zero_add] at key
  have : Q 0 * u n = 0 := by
    have e : n + ((0 : ℕ) : ℤ) = n := by push_cast; ring
    rw [e] at key
    exact key
  exact (mul_eq_zero.mp this).resolve_left hQ

/-- **The engine of the write-up's theorem, with its coefficient hypothesis removed.** A bilateral
monic recurrence forces a sequence vanishing on a terminal ray to vanish identically — for *any*
coefficients, because `BilatRec.shift` manufactures the nonzero constant coefficient when one
exists and its absence already forces `u = 0`. -/
theorem zero_of_eventually_zero {D : ℕ} {q : ℕ → K} {u : ℤ → K} (h : BilatRec D q u) (L : ℤ)
    (hL : ∀ n : ℤ, L ≤ n → u n = 0) : ∀ n : ℤ, u n = 0 := by
  classical
  by_cases hex : ∃ k : ℕ, k < D ∧ q k ≠ 0
  · -- pass to the least nonvanishing coefficient; the shifted recurrence runs backwards
    set t : ℕ := Nat.find hex with hts
    have htD : t < D := (Nat.find_spec hex).1
    have htq : q t ≠ 0 := (Nat.find_spec hex).2
    have hlow : ∀ k : ℕ, k < t → q k = 0 := by
      intro k hk
      by_contra hc
      have hle : t ≤ k := Nat.find_le ⟨lt_trans hk htD, hc⟩
      omega
    have h' : BilatRec (D - t) (fun j => q (t + j)) u := h.shift t (le_of_lt htD) hlow
    obtain ⟨E, hE⟩ : ∃ E : ℕ, D - t = E + 1 := ⟨D - t - 1, by omega⟩
    rw [hE] at h'
    have hQ0 : (fun j => q (t + j)) 0 ≠ 0 := by simpa using htq
    -- downward induction: everything at or above `L - m` vanishes, for every `m`
    have step : ∀ m : ℕ, ∀ n : ℤ, L - (m : ℤ) ≤ n → u n = 0 := by
      intro m
      induction m with
      | zero => intro n hn; exact hL n (by simpa using hn)
      | succ p ih =>
        intro n hn
        by_cases hge : L - (p : ℤ) ≤ n
        · exact ih n hge
        · have hn' : n = L - (p : ℤ) - 1 := by push_cast at hn ⊢; omega
          refine h'.backward hQ0 n fun j hj1 _ => ih (n + (j : ℤ)) ?_
          have : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj1
          omega
    intro n
    exact step (L - n).toNat n (by omega)
  · -- no coefficient survives: the relation itself says `u (n + D) = 0` for every `n`
    have hall : ∀ k : ℕ, k < D → q k = 0 := by
      intro k hk
      by_contra hc
      exact hex ⟨k, hk, hc⟩
    intro n
    have key := h (n - (D : ℤ))
    rw [Finset.sum_eq_zero fun k hk => by
      rw [hall k (Finset.mem_range.mp hk), zero_mul], add_zero,
      show n - (D : ℤ) + (D : ℤ) = n by ring] at key
    exact key

/-- **The write-up's corollary.** `D` consecutive zeros anywhere already force `u = 0`: run the
recurrence forwards off the block to reach a terminal ray, then backwards. -/
theorem zero_of_consecutive_zeros {D : ℕ} {q : ℕ → K} {u : ℤ → K} (h : BilatRec D q u) (n₀ : ℤ)
    (hz : ∀ j : ℕ, j < D → u (n₀ + (j : ℤ)) = 0) : ∀ n : ℤ, u n = 0 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    intro n
    have := h (n - (0 : ℤ))
    simpa using this
  · -- the block slides upward by one at each step
    have block : ∀ m : ℕ, ∀ j : ℕ, j < D → u (n₀ + (m : ℤ) + (j : ℤ)) = 0 := by
      intro m
      induction m with
      | zero => intro j hj; simpa using hz j hj
      | succ p ih =>
        intro j hj
        by_cases hlt : j + 1 < D
        · have hih := ih (j + 1) hlt
          rw [show n₀ + ((p + 1 : ℕ) : ℤ) + (j : ℤ) = n₀ + (p : ℤ) + ((j + 1 : ℕ) : ℤ) by
            push_cast; ring]
          exact hih
        · have hjD : j + 1 = D := by omega
          have hfw := h.forward (n₀ + (p : ℤ)) fun k hk => ih k hk
          rw [show n₀ + ((p + 1 : ℕ) : ℤ) + (j : ℤ) = n₀ + (p : ℤ) + (D : ℤ) by
            have hcast : (D : ℤ) = (j : ℤ) + 1 := by exact_mod_cast hjD.symm
            rw [hcast]; push_cast; ring]
          exact hfw
    refine zero_of_eventually_zero h n₀ fun n hn => ?_
    have := block (n - n₀).toNat 0 hD
    rw [show n₀ + (((n - n₀).toNat : ℤ)) + ((0 : ℕ) : ℤ) = n by
      push_cast
      omega] at this
    exact this

/-- **The bilateral convention is load-bearing, not cosmetic.** On one-sided sequences the same
statement fails, and the counterexample is minimal. -/
theorem bilaterality_essential :
    ∃ u : ℕ → K, (∀ n : ℕ, u (n + 1) = 0) ∧ u 0 ≠ 0 :=
  ⟨fun n => if n = 0 then 1 else 0, fun n => by simp, by simp⟩

/-- **Soykan Conjecture 4.2**, in its own shape: a polynomial `f` in terms of arbitrary arithmetic
subsequences `H i (a i * n + b i)` — the slopes `a i` may be negative or zero — vanishing for all
large `n`, vanishes for every integer `n`.

The single hypothesis `hlift` is the write-up's lift lemma (Cayley–Hamilton on `P ↦ P ∘ A`, stage 2
of the residue); everything else is discharged. Note no distinct-root hypothesis appears, and `K` is
an arbitrary field, so the argument covers finite fields. -/
theorem conjecture_4_2_of_lift {r : ℕ} (H : Fin r → ℤ → K) (a b : Fin r → ℤ)
    (f : MvPolynomial (Fin r) K) (u : ℤ → K)
    (hu : ∀ n : ℤ, u n = MvPolynomial.eval (fun i => H i (a i * n + b i)) f)
    {D : ℕ} {q : ℕ → K} (hlift : BilatRec D q u)
    (L : ℤ) (hL : ∀ n : ℤ, L ≤ n → MvPolynomial.eval (fun i => H i (a i * n + b i)) f = 0) :
    ∀ n : ℤ, MvPolynomial.eval (fun i => H i (a i * n + b i)) f = 0 := by
  intro n
  rw [← hu n]
  exact zero_of_eventually_zero hlift L (fun m hm => by rw [hu m]; exact hL m hm) n

/-! ## The lift: first typed as an interface, then proved

Per the project's skeleton-first direction the interface was typed before the proof existed, and
that is what let the two halves -- the polynomial-degree plumbing and the Cayley-Hamilton core -- be
written and checked independently. Both are below. -/

/-- The state sequence of the write-up's representation: `n ↦ F(Aⁿ w)`, with `A` invertible so that
`Aⁿ` makes sense for **negative** `n` — which is the whole reason the argument is bilateral.

Named rather than written as a lambda, so that applications reduce without a beta step. -/
noncomputable def stateSeq {E : Type} [Fintype E] [DecidableEq E]
    (A : Matrix.GeneralLinearGroup E K) (w : E → K)
    (F : MvPolynomial E K) (n : ℤ) : K :=
  MvPolynomial.eval
    ((((A ^ n : Matrix.GeneralLinearGroup E K) : Matrix E E K)).mulVec w) F

section Lift

variable (K)

/-- **The lift.** For every invertible `A` and every polynomial `F`, the sequence `n ↦ F(Aⁿ w)`
satisfies *some* monic bilateral recurrence.

This is the write-up's Lemma, and it is what `conjecture_4_2_of_lift` assumes. **It is proved below,
as `liftGoal_holds`** — by Cayley–Hamilton for the operator `P ↦ P ∘ A` on the space of polynomials
of total degree at most `deg F`, whose invariance under that operator is `tdeg_aeval_le`. It is kept
as a named `Prop` rather than inlined because it is the interface the conjecture consumes, and
naming it is what let the two halves be built and checked separately.

Note what the statement does **not** ask for: a nonzero constant coefficient. `BilatRec` needs only
monicity (see `zero_of_eventually_zero`), which is precisely what Cayley–Hamilton supplies, so no
determinant is ever computed. -/
def LiftGoal : Prop :=
  ∀ (E : Type) [Fintype E] [DecidableEq E] (A : Matrix.GeneralLinearGroup E K) (w : E → K)
    (F : MvPolynomial E K), ∃ (D : ℕ) (q : ℕ → K), BilatRec D q (stateSeq A w F)

end Lift

/-- **The conjecture in state form, granted the lift** — and note what it does *not* assume: no
bound on `deg F`, no distinct-root hypothesis, no condition on `A` beyond invertibility, and nothing
about the characteristic of `K`. Every one of those is a hypothesis the source or the write-up
carries somewhere, and none of them is needed once the propagation step is done properly. -/
theorem stateSeq_eq_zero_of_liftGoal (hlift : LiftGoal K) {E : Type} [Fintype E]
    [DecidableEq E]
    (A : Matrix.GeneralLinearGroup E K) (w : E → K) (F : MvPolynomial E K)
    (L : ℤ) (hL : ∀ n : ℤ, L ≤ n → stateSeq A w F n = 0) :
    ∀ n : ℤ, stateSeq A w F n = 0 := by
  obtain ⟨D, q, hrec⟩ := hlift E A w F
  exact zero_of_eventually_zero hrec L hL

section Stage2

open MvPolynomial

variable {E : Type} [Fintype E] [DecidableEq E]

/-! ### Stage 2, step 1: the orbit core

Campaign-agnostic: an orbit of an invertible operator on a finite-dimensional space,
read by any linear functional, satisfies a monic bilateral recurrence.  Cayley-Hamilton
supplies the recurrence and invertibility is what makes negative indices meaningful. -/

noncomputable def orbitSeq {V : Type*} [AddCommGroup V] [Module K V] (T : V ≃ₗ[K] V) (v : V)
    (phi : V →ₗ[K] K) (n : ℤ) : K := phi ((T ^ n) v)

theorem bilatRec_orbitSeq {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (T : V ≃ₗ[K] V) (v : V) (phi : V →ₗ[K] K) :
    ∃ (D : ℕ) (q : ℕ → K), BilatRec D q (orbitSeq T v phi) := by
  classical
  set f : V →ₗ[K] V := (T : V →ₗ[K] V) with hf
  set p : Polynomial K := f.charpoly with hp
  refine ⟨p.natDegree, p.coeff, ?_⟩
  intro n
  have hmonic : p.Monic := LinearMap.charpoly_monic f
  have hCH : (Polynomial.aeval f) p = 0 := LinearMap.aeval_self_charpoly f
  have hsum : (Polynomial.aeval f) p
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • f ^ i :=
    Polynomial.aeval_eq_sum_range (p := p) f
  rw [Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hsum
  have hzero : (∑ i ∈ Finset.range p.natDegree, p.coeff i • f ^ i) + f ^ p.natDegree = 0 := by
    rw [← hsum]; exact hCH
  have hfp : ∀ (k : ℕ) (x : V), (f ^ k) x = (T ^ (k : ℤ)) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      have hidx : ((j + 1 : ℕ) : ℤ) = 1 + (j : ℤ) := by push_cast; ring
      rw [pow_succ', Module.End.mul_apply, ih, hidx, zpow_add, zpow_one]
      rfl
  have hshift : ∀ k : ℕ, (f ^ k) ((T ^ n) v) = (T ^ (n + (k : ℤ))) v := by
    intro k
    have hsplit : (T ^ ((k : ℤ) + n)) v = (T ^ (k : ℤ)) ((T ^ n) v) := by
      rw [zpow_add]; rfl
    rw [hfp k, ← hsplit, add_comm]
  have happ := congrArg (fun g : V →ₗ[K] V => phi (g ((T ^ n) v))) hzero
  simp only [LinearMap.add_apply, LinearMap.zero_apply, map_add, map_zero,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_smul, map_sum,
    hshift, smul_eq_mul] at happ
  simp only [orbitSeq]
  rw [add_comm]
  exact happ

/-! ### Stage 2, step 2: linear substitution preserves bounded degree

This is the one ingredient the residue named as absent from Mathlib, and it is what makes
`restrictTotalDegree` invariant under `P` mapsto `P` composed with `A`. -/

omit [Fintype E] [DecidableEq E] in
theorem tdeg_aeval_le (g : E → MvPolynomial E K)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial E K) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  have key : aeval g P = ∑ v ∈ P.support, aeval g (monomial v (coeff v P)) := by
    rw [← map_sum, ← P.as_sum]
  rw [key]
  refine MvPolynomial.totalDegree_finsetSum_le fun a ha => ?_
  rw [MvPolynomial.aeval_monomial]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have hC : (algebraMap K (MvPolynomial E K) (coeff a P)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact MvPolynomial.totalDegree_C _
  rw [hC, zero_add, Finsupp.prod]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (MvPolynomial.le_totalDegree ha)
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  calc a i * (g i).totalDegree ≤ a i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = a i := by ring

noncomputable def linSubst (B : Matrix E E K) :
    MvPolynomial E K →ₐ[K] MvPolynomial E K :=
  aeval fun i => ∑ j, C (B i j) * X j

omit [DecidableEq E] in
@[simp] theorem linSubst_X (B : Matrix E E K) (i : E) :
    linSubst B (X i) = ∑ j, C (B i j) * (X j : MvPolynomial E K) := by
  rw [linSubst, MvPolynomial.aeval_X]

omit [DecidableEq E] in
@[simp] theorem linSubst_C (B : Matrix E E K) (c : K) :
    linSubst B (C c) = (C c : MvPolynomial E K) := by
  rw [linSubst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

omit [DecidableEq E] in
theorem tdeg_substGen (B : Matrix E E K) (i : E) :
    (∑ j, C (B i j) * (X j : MvPolynomial E K)).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X]

omit [DecidableEq E] in
theorem tdeg_subst_le (B : Matrix E E K) (P : MvPolynomial E K) :
    (linSubst B P).totalDegree ≤ P.totalDegree :=
  tdeg_aeval_le _ (tdeg_substGen B) P

omit [DecidableEq E] in
theorem aeval_subst (B : Matrix E E K) (v : E → K) (P : MvPolynomial E K) :
    aeval v (linSubst B P) = aeval (B.mulVec v) P := by
  have h : (aeval v : MvPolynomial E K →ₐ[K] K).comp (linSubst B)
      = (aeval (B.mulVec v) : MvPolynomial E K →ₐ[K] K) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linSubst_X, map_sum, MvPolynomial.aeval_X]
    simp [Matrix.mulVec, dotProduct]
  exact congrArg (fun φ : MvPolynomial E K →ₐ[K] K => φ P) h

omit [DecidableEq E] in
theorem linSubst_comp (B B' : Matrix E E K) (P : MvPolynomial E K) :
    linSubst B (linSubst B' P) = linSubst (B' * B) P := by
  have h : (linSubst B).comp (linSubst B') = linSubst (B' * B) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linSubst_X, map_sum, linSubst_X]
    have hstep : ∀ j : E, (linSubst B) (C (B' i j) * (X j : MvPolynomial E K))
        = ∑ l, C (B' i j * B j l) * (X l : MvPolynomial E K) := by
      intro j
      rw [map_mul, linSubst_C, linSubst_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, ← MvPolynomial.C_mul]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hstep j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply]
  exact congrArg (fun φ : MvPolynomial E K →ₐ[K] MvPolynomial E K => φ P) h

theorem linSubst_one (P : MvPolynomial E K) :
    linSubst (1 : Matrix E E K) P = P := by
  have h : linSubst (1 : Matrix E E K) = AlgHom.id K (MvPolynomial E K) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [linSubst_X, AlgHom.id_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Matrix.one_apply_ne (Ne.symm hj), map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h, AlgHom.id_apply]

/-! ### Stage 2, step 3: the assembly -/

/-- `linSubst B` restricted to the polynomials of total degree at most `d`, which it preserves. -/
noncomputable def linSubstR (d : ℕ) (B : Matrix E E K) :
    (MvPolynomial.restrictTotalDegree E K d) →ₗ[K]
      (MvPolynomial.restrictTotalDegree E K d) :=
  LinearMap.restrict (linSubst B).toLinearMap (fun P hP => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hP ⊢
    exact le_trans (tdeg_subst_le B P) hP)

omit [DecidableEq E] in
theorem linSubstR_coe (d : ℕ) (B : Matrix E E K)
    (P : MvPolynomial.restrictTotalDegree E K d) :
    ((linSubstR d B P : MvPolynomial.restrictTotalDegree E K d) : MvPolynomial E K)
      = linSubst B (P : MvPolynomial E K) := rfl

/-- `linSubst` of an invertible matrix is a linear automorphism of the bounded-degree space. -/
noncomputable def linSubstE (d : ℕ) (A : Matrix.GeneralLinearGroup E K) :
    (MvPolynomial.restrictTotalDegree E K d) ≃ₗ[K]
      (MvPolynomial.restrictTotalDegree E K d) :=
  LinearEquiv.ofLinear (linSubstR d ↑A) (linSubstR d ↑A⁻¹)
    (by
      refine LinearMap.ext fun P => Subtype.ext ?_
      rw [LinearMap.comp_apply, linSubstR_coe, linSubstR_coe, linSubst_comp]
      have : ((A⁻¹ : Matrix.GeneralLinearGroup E K) : Matrix E E K)
          * ((A : Matrix.GeneralLinearGroup E K) : Matrix E E K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [this, linSubst_one]
      rfl)
    (by
      refine LinearMap.ext fun P => Subtype.ext ?_
      rw [LinearMap.comp_apply, linSubstR_coe, linSubstR_coe, linSubst_comp]
      have : ((A : Matrix.GeneralLinearGroup E K) : Matrix E E K)
          * ((A⁻¹ : Matrix.GeneralLinearGroup E K) : Matrix E E K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [this, linSubst_one]
      rfl)

theorem linSubstE_coe (d : ℕ) (A : Matrix.GeneralLinearGroup E K)
    (P : MvPolynomial.restrictTotalDegree E K d) :
    ((linSubstE d A P : MvPolynomial.restrictTotalDegree E K d) : MvPolynomial E K)
      = linSubst ↑A (P : MvPolynomial E K) := rfl

theorem linSubstE_inv_coe (d : ℕ) (A : Matrix.GeneralLinearGroup E K)
    (P : MvPolynomial.restrictTotalDegree E K d) :
    (((linSubstE d A)⁻¹ P : MvPolynomial.restrictTotalDegree E K d) :
      MvPolynomial E K) = linSubst ↑A⁻¹ (P : MvPolynomial E K) := rfl

/-- Integer powers of `linSubstE` are `linSubst` of the corresponding power of the matrix. -/
theorem linSubstE_zpow (d : ℕ) (A : Matrix.GeneralLinearGroup E K) (n : ℤ) :
    ∀ P : MvPolynomial.restrictTotalDegree E K d,
      (((linSubstE d A ^ n) P : MvPolynomial.restrictTotalDegree E K d) :
        MvPolynomial E K)
        = linSubst ((A ^ n : Matrix.GeneralLinearGroup E K) : Matrix E E K)
            (P : MvPolynomial E K) := by
  induction n using Int.induction_on with
  | zero => intro P; rw [zpow_zero, zpow_zero]; simp [linSubst_one]
  | succ j ih =>
    intro P
    have hstep : (linSubstE d A ^ ((j : ℤ) + 1)) P
        = (linSubstE d A ^ (j : ℤ)) (linSubstE d A P) := by
      rw [zpow_add, zpow_one]; rfl
    have hA : (A : Matrix.GeneralLinearGroup E K) * A ^ (j : ℤ)
        = A ^ ((j : ℤ) + 1) := by
      rw [add_comm, zpow_add, zpow_one]
    rw [hstep, ih, linSubstE_coe, linSubst_comp, ← Units.val_mul, hA]
  | pred j ih =>
    intro P
    have hstep : (linSubstE d A ^ (-(j : ℤ) - 1)) P
        = (linSubstE d A)⁻¹ ((linSubstE d A ^ (-(j : ℤ))) P) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_one]; rfl
    have hA : (A ^ (-(j : ℤ))) * (A⁻¹ : Matrix.GeneralLinearGroup E K)
        = A ^ (-(j : ℤ) - 1) := by
      rw [sub_eq_add_neg, zpow_add]
      simp
    rw [hstep, linSubstE_inv_coe, ih, linSubst_comp, ← Units.val_mul, hA]

/-- Evaluation at `w`, as a linear functional on the bounded-degree space. -/
noncomputable def evalOn (d : ℕ) (w : E → K) :
    (MvPolynomial.restrictTotalDegree E K d) →ₗ[K] K :=
  (aeval w : MvPolynomial E K →ₐ[K] K).toLinearMap.comp (Submodule.subtype _)

/-- **The lift, proved.** -/
theorem liftGoal_holds : LiftGoal K := by
  intro E _ _ A w F
  classical
  set d : ℕ := F.totalDegree with hd
  have hFmem : F ∈ MvPolynomial.restrictTotalDegree E K d := by
    rw [MvPolynomial.mem_restrictTotalDegree]
  obtain ⟨D, q, hrec⟩ :=
    bilatRec_orbitSeq (linSubstE d A) (⟨F, hFmem⟩ : MvPolynomial.restrictTotalDegree E K d)
      (evalOn d w)
  refine ⟨D, q, ?_⟩
  have hEq : orbitSeq (linSubstE d A) ⟨F, hFmem⟩ (evalOn d w) = stateSeq A w F := by
    funext n
    rw [orbitSeq, evalOn, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, linSubstE_zpow, aeval_subst, stateSeq]
    rfl
  rw [← hEq]
  exact hrec

/-- **Soykan Conjecture 4.2 in state form, now UNCONDITIONAL.**  The lift is no longer
assumed: `liftGoal_holds` proves it, so this theorem carries nothing beyond the eventual
vanishing it is given. -/
theorem stateSeq_eq_zero {E : Type} [Fintype E] [DecidableEq E]
    (A : Matrix.GeneralLinearGroup E K) (w : E → K)
    (F : MvPolynomial E K) (L : ℤ)
    (hL : ∀ n : ℤ, L ≤ n → stateSeq A w F n = 0) :
    ∀ n : ℤ, stateSeq A w F n = 0 :=
  stateSeq_eq_zero_of_liftGoal liftGoal_holds A w F L hL

end Stage2

section Stage3

/-! ## Stage 3: from a recurrence sequence to `stateSeq`, and the literal conjecture

The companion matrix turns a bilateral recurrence sequence into an orbit; a block-diagonal
stack of its powers handles several arithmetic subsequences at once.  Nothing here needs
absent Mathlib theory -- it is `Fin`-index arithmetic and `Matrix.blockDiagonal`. -/

/-- The companion matrix of a monic order-`kk+1` recurrence: superdiagonal ones, and the
coefficients negated along the last row. -/
def companion (kk : ℕ) (c : ℕ → K) : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K :=
  Matrix.of fun i j =>
    if (i : ℕ) < kk then (if (j : ℕ) = (i : ℕ) + 1 then 1 else 0) else -c (j : ℕ)

/-- Its inverse, read straight off the BACKWARD recurrence. This is the only place the nonzero
constant coefficient is used, and it is used to divide by. -/
noncomputable def companionInv (kk : ℕ) (c : ℕ → K) : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 then (if (j : ℕ) < kk then -(c ((j : ℕ) + 1)) / c 0 else -1 / c 0)
    else (if (j : ℕ) + 1 = (i : ℕ) then 1 else 0)

theorem companion_mul_inv (kk : ℕ) (c : ℕ → K) (hc : c 0 ≠ 0) :
    companion kk c * companionInv kk c = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hi : (i : ℕ) < kk
  · -- a superdiagonal row selects row `i+1` of the inverse
    have hsucc : ((i : ℕ) + 1) < kk + 1 := by omega
    rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hsucc⟩ : Fin (kk + 1))
      (fun l _ hl => by
        have hlne : (l : ℕ) ≠ (i : ℕ) + 1 := fun h => hl (Fin.ext h)
        simp [companion, hi, hlne])
      (fun h => absurd (Finset.mem_univ _) h)]
    have e1 : companion kk c i (⟨(i : ℕ) + 1, hsucc⟩ : Fin (kk + 1)) = 1 := by
      simp [companion, hi]
    rw [e1, one_mul]
    simp only [companionInv, Matrix.of_apply]
    rw [if_neg (Nat.succ_ne_zero _)]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hij, if_neg (fun h : (j : ℕ) + 1 = (i : ℕ) + 1 => hij (Fin.ext (by omega)))]
  · -- the coefficient row, where the division cancels
    have hik : (i : ℕ) = kk := by omega
    rw [Fin.sum_univ_succ]
    have hzero : ∀ l : Fin kk, companion kk c i l.succ * companionInv kk c l.succ j
        = (-c ((l : ℕ) + 1)) * (if (j : ℕ) = (l : ℕ) then 1 else 0) := by
      intro l
      have e1 : companion kk c i l.succ = -c ((l : ℕ) + 1) := by
        simp only [companion, Matrix.of_apply, if_neg hi, Fin.val_succ]
      have e2 : companionInv kk c l.succ j = (if (j : ℕ) = (l : ℕ) then 1 else 0) := by
        simp only [companionInv, Matrix.of_apply, Fin.val_succ,
          if_neg (Nat.succ_ne_zero (l : ℕ))]
        by_cases h : (j : ℕ) = (l : ℕ)
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [e1, e2]
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hzero l]
    have e0 : companion kk c i (0 : Fin (kk + 1)) = -c 0 := by
      simp only [companion, Matrix.of_apply, if_neg hi, Fin.val_zero]
    have e0' : companionInv kk c (0 : Fin (kk + 1)) j
        = (if (j : ℕ) < kk then -(c ((j : ℕ) + 1)) / c 0 else -1 / c 0) := by
      simp only [companionInv, Matrix.of_apply, Fin.val_zero, if_true]
    rw [e0, e0']
    by_cases hjk : (j : ℕ) < kk
    · rw [if_pos hjk]
      have hsum : (∑ l : Fin kk, (-c ((l : ℕ) + 1)) * (if (j : ℕ) = (l : ℕ) then 1 else 0))
          = -c ((j : ℕ) + 1) := by
        rw [Finset.sum_eq_single (⟨(j : ℕ), hjk⟩ : Fin kk)
          (fun l _ hl => by
            rw [if_neg (fun h : (j : ℕ) = (l : ℕ) => hl (Fin.ext h.symm)), mul_zero])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [if_pos rfl, mul_one]
      rw [hsum, if_neg (fun h : i = j => by rw [h] at hik; omega)]
      field_simp
      ring
    · rw [if_neg hjk]
      have hsum : (∑ l : Fin kk, (-c ((l : ℕ) + 1)) * (if (j : ℕ) = (l : ℕ) then 1 else 0))
          = 0 :=
        Finset.sum_eq_zero fun l _ => by
          rw [if_neg (by omega : ¬ (j : ℕ) = (l : ℕ)), mul_zero]
      rw [hsum, add_zero, if_pos (Fin.ext (by omega) : i = j)]
      field_simp

theorem companion_isUnit_det (kk : ℕ) (c : ℕ → K) (hc : c 0 ≠ 0) :
    IsUnit (companion kk c).det :=
  Matrix.isUnit_det_of_right_inverse (companion_mul_inv kk c hc)

/-- The companion matrix as an element of the general linear group. -/
noncomputable def companionGL (kk : ℕ) (c : ℕ → K) (hc : c 0 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin (kk + 1)) K :=
  Units.mk (companion kk c) (companion kk c)⁻¹
    (Matrix.mul_nonsing_inv _ (companion_isUnit_det kk c hc))
    (Matrix.nonsing_inv_mul _ (companion_isUnit_det kk c hc))

/-- The state vector of a bilateral sequence: `kk+1` consecutive values from index `n`. -/
def stateVec (kk : ℕ) (H : ℤ → K) (n : ℤ) : Fin (kk + 1) → K := fun j => H (n + (j : ℕ))

/-- **The state equation.** The companion matrix advances the state vector by one step. This needs
only monicity — the coefficient condition is nowhere in it. -/
theorem companion_mulVec_stateVec (kk : ℕ) (c : ℕ → K) (H : ℤ → K)
    (hH : BilatRec (kk + 1) c H) (n : ℤ) :
    (companion kk c).mulVec (stateVec kk H n) = stateVec kk H (n + 1) := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : (i : ℕ) < kk
  · have hsucc : ((i : ℕ) + 1) < kk + 1 := by omega
    rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hsucc⟩ : Fin (kk + 1))
      (fun l _ hl => by
        have hlne : (l : ℕ) ≠ (i : ℕ) + 1 := fun h => hl (Fin.ext h)
        simp [companion, hi, hlne])
      (fun h => absurd (Finset.mem_univ _) h)]
    have e1 : companion kk c i (⟨(i : ℕ) + 1, hsucc⟩ : Fin (kk + 1)) = 1 := by
      simp [companion, hi]
    rw [e1, one_mul]
    simp only [stateVec]
    congr 1
    push_cast
    ring
  · have hik : (i : ℕ) = kk := by omega
    have hrec := hH n
    have e : (∑ l : Fin (kk + 1), companion kk c i l * stateVec kk H n l)
        + (∑ j ∈ Finset.range (kk + 1), c j * H (n + (j : ℕ))) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => c j * H (n + (j : ℤ))) (kk + 1),
        ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      simp only [companion, Matrix.of_apply, if_neg hi, stateVec]
      ring
    have key : (∑ l : Fin (kk + 1), companion kk c i l * stateVec kk H n l)
        = H (n + ((kk + 1 : ℕ) : ℤ)) := by linear_combination e - hrec
    rw [key]
    simp only [stateVec]
    congr 1
    push_cast
    omega

@[simp] theorem companionGL_coe (kk : ℕ) (c : ℕ → K) (hc : c 0 ≠ 0) :
    ((companionGL kk c hc : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
      Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) = companion kk c := rfl

/-- The inverse runs the recurrence BACKWARDS, and needs no separate computation: it is the state
equation plus `A⁻¹ * A = 1`. -/
theorem companionGL_inv_mulVec (kk : ℕ) (c : ℕ → K) (hc : c 0 ≠ 0) (H : ℤ → K)
    (hH : BilatRec (kk + 1) c H) (m : ℤ) :
    (((companionGL kk c hc)⁻¹ : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
      Matrix (Fin (kk + 1)) (Fin (kk + 1)) K).mulVec (stateVec kk H m)
      = stateVec kk H (m - 1) := by
  have hstep : (companion kk c).mulVec (stateVec kk H (m - 1)) = stateVec kk H m := by
    rw [companion_mulVec_stateVec kk c H hH (m - 1)]
    congr 1
    ring
  rw [← hstep, Matrix.mulVec_mulVec, ← companionGL_coe kk c hc, Units.inv_mul,
    Matrix.one_mulVec]

/-- **Integer powers of the companion matrix translate the state vector.** This is the bridge from
a bilateral recurrence sequence to `stateSeq`, and the only place both directions are needed. -/
theorem companionGL_zpow_mulVec (kk : ℕ) (c : ℕ → K) (hc : c 0 ≠ 0) (H : ℤ → K)
    (hH : BilatRec (kk + 1) c H) (b : ℤ) (n : ℤ) :
    ((companionGL kk c hc ^ n : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
      Matrix (Fin (kk + 1)) (Fin (kk + 1)) K).mulVec (stateVec kk H b)
      = stateVec kk H (b + n) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ j ih =>
    have hsplit : (companionGL kk c hc ^ ((j : ℤ) + 1)
        : Matrix.GeneralLinearGroup (Fin (kk + 1)) K)
        = companionGL kk c hc * companionGL kk c hc ^ (j : ℤ) := by
      rw [add_comm (j : ℤ) 1, zpow_add, zpow_one]
    rw [hsplit, Units.val_mul, ← Matrix.mulVec_mulVec, ih, companionGL_coe,
      companion_mulVec_stateVec kk c H hH]
    congr 1
    ring
  | pred j ih =>
    have hsplit : (companionGL kk c hc ^ (-(j : ℤ) - 1)
        : Matrix.GeneralLinearGroup (Fin (kk + 1)) K)
        = (companionGL kk c hc)⁻¹ * companionGL kk c hc ^ (-(j : ℤ)) := by
      rw [sub_eq_add_neg, add_comm (-(j : ℤ)) (-1), zpow_add]
      simp
    rw [hsplit, Units.val_mul, ← Matrix.mulVec_mulVec, ih,
      companionGL_inv_mulVec kk c hc H hH]
    congr 1
    ring

/-! ### Stage 3, step 2: stacking the subsequences -/

/-- A block-diagonal family of invertible matrices is invertible, with the blockwise inverse. -/
noncomputable def blockGL {kk r : ℕ}
    (G : Fin r → Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
    Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K :=
  Units.mk
    (Matrix.blockDiagonal fun i => ((G i : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K)))
    (Matrix.blockDiagonal fun i =>
      (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
        Matrix (Fin (kk + 1)) (Fin (kk + 1)) K))
    (by
      rw [← Matrix.blockDiagonal_mul]
      have h : (fun i => ((G i : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K)) *
          (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
            Matrix (Fin (kk + 1)) (Fin (kk + 1)) K))
          = fun _ => (1 : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) := by
        funext i; exact Units.mul_inv (G i)
      rw [h]
      exact Matrix.blockDiagonal_one)
    (by
      rw [← Matrix.blockDiagonal_mul]
      have h : (fun i => (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
            Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) *
          ((G i : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K)))
          = fun _ => (1 : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) := by
        funext i; exact Units.inv_mul (G i)
      rw [h]
      exact Matrix.blockDiagonal_one)

theorem blockGL_coe {kk r : ℕ} (G : Fin r → Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
    ((blockGL G : Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K) :
      Matrix (Fin (kk + 1) × Fin r) (Fin (kk + 1) × Fin r) K)
      = Matrix.blockDiagonal fun i => ((G i : Matrix (Fin (kk + 1)) (Fin (kk + 1)) K)) := rfl

theorem blockGL_inv_coe {kk r : ℕ} (G : Fin r → Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
    (((blockGL G)⁻¹ : Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K) :
      Matrix (Fin (kk + 1) × Fin r) (Fin (kk + 1) × Fin r) K)
      = Matrix.blockDiagonal fun i =>
          (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
            Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) := rfl

theorem blockGL_coe_zpow {kk r : ℕ}
    (G : Fin r → Matrix.GeneralLinearGroup (Fin (kk + 1)) K) (n : ℤ) :
    ((blockGL G ^ n : Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K) :
      Matrix (Fin (kk + 1) × Fin r) (Fin (kk + 1) × Fin r) K)
      = Matrix.blockDiagonal fun i =>
          ((G i ^ n : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
            Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) := by
  induction n using Int.induction_on with
  | zero =>
    simp only [zpow_zero, Units.val_one]
    exact Matrix.blockDiagonal_one.symm
  | succ j ih =>
    rw [add_comm (j : ℤ) 1, zpow_add, zpow_one, Units.val_mul, ih, blockGL_coe,
      ← Matrix.blockDiagonal_mul]
    refine congrArg Matrix.blockDiagonal (funext fun i => ?_)
    rw [← Units.val_mul]
    congr 1
    rw [zpow_add, zpow_one]
  | pred j ih =>
    have hinv : (blockGL G ^ (-1 : ℤ) :
        Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K) = (blockGL G)⁻¹ :=
      zpow_neg_one _
    rw [sub_eq_add_neg, add_comm (-(j : ℤ)) (-1), zpow_add, Units.val_mul, ih, hinv,
      blockGL_inv_coe, ← Matrix.blockDiagonal_mul]
    refine congrArg Matrix.blockDiagonal (funext fun i => ?_)
    rw [← Units.val_mul]
    congr 1
    rw [zpow_add, zpow_neg_one]

theorem blockDiagonal_mulVec_apply {kk r : ℕ}
    (M : Fin r → Matrix (Fin (kk + 1)) (Fin (kk + 1)) K) (v : Fin (kk + 1) × Fin r → K)
    (p : Fin (kk + 1) × Fin r) :
    (Matrix.blockDiagonal M).mulVec v p = (M p.2).mulVec (fun j => v (j, p.2)) p.1 := by
  obtain ⟨p1, p2⟩ := p
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single p2
    (fun y _ hy => by rw [Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hy), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [Matrix.blockDiagonal_apply_eq]

/-- The write-up's object: a polynomial in arithmetic subsequences of one bilateral sequence.
Named, not a lambda, so downstream applications reduce. -/
noncomputable def polySubseq {r : ℕ} (H : ℤ → K) (a b : Fin r → ℤ)
    (f : MvPolynomial (Fin r) K) (n : ℤ) : K :=
  MvPolynomial.eval (fun i => H (a i * n + b i)) f

/-! ### Stage 3, step 3: the literal conjecture -/

theorem bilatRec_polySubseq {kk r : ℕ} (c : ℕ → K) (hc : c 0 ≠ 0) (H : ℤ → K)
    (hH : BilatRec (kk + 1) c H) (a b : Fin r → ℤ) (f : MvPolynomial (Fin r) K) :
    ∃ (D : ℕ) (q : ℕ → K), BilatRec D q (polySubseq H a b f) := by
  classical
  set G : Fin r → Matrix.GeneralLinearGroup (Fin (kk + 1)) K :=
    fun i => companionGL kk c hc ^ (a i) with hG
  set A : Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K := blockGL G with hA
  set w : Fin (kk + 1) × Fin r → K := fun p => stateVec kk H (b p.2) p.1 with hw
  set F : MvPolynomial (Fin (kk + 1) × Fin r) K :=
    MvPolynomial.rename (fun i : Fin r => ((0 : Fin (kk + 1)), i)) f with hF
  obtain ⟨D, q, hrec⟩ := liftGoal_holds (Fin (kk + 1) × Fin r) A w F
  refine ⟨D, q, ?_⟩
  have hpt : ∀ n : ℤ, (((A ^ n : Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K) :
      Matrix (Fin (kk + 1) × Fin r) (Fin (kk + 1) × Fin r) K).mulVec w
      ∘ fun i : Fin r => ((0 : Fin (kk + 1)), i))
      = fun i => H (a i * n + b i) := by
    intro n
    funext i
    have hblk : (((A ^ n : Matrix.GeneralLinearGroup (Fin (kk + 1) × Fin r) K) :
        Matrix (Fin (kk + 1) × Fin r) (Fin (kk + 1) × Fin r) K).mulVec w)
        ((0 : Fin (kk + 1)), i)
        = ((G i ^ n : Matrix.GeneralLinearGroup (Fin (kk + 1)) K) :
            Matrix (Fin (kk + 1)) (Fin (kk + 1)) K).mulVec
            (fun j => w (j, i)) (0 : Fin (kk + 1)) := by
      rw [hA, blockGL_coe_zpow, blockDiagonal_mulVec_apply]
    have hwi : (fun j => w (j, i)) = stateVec kk H (b i) := by funext j; rw [hw]
    rw [Function.comp_apply, hblk, hwi, hG, ← zpow_mul,
      companionGL_zpow_mulVec kk c hc H hH (b i) (a i * n)]
    simp only [stateVec, Fin.val_zero, Nat.cast_zero, add_zero]
    congr 1
    ring
  have hEq : stateSeq A w F = polySubseq H a b f := by
    funext n
    simp only [stateSeq, polySubseq, hF, MvPolynomial.eval_rename, hpt n]
  rw [← hEq]
  exact hrec

/-- **Soykan Conjecture 4.2, in full and unconditionally.** A polynomial in arbitrary arithmetic
subsequences of a bilateral constant-recursive sequence, vanishing for all large `n`, vanishes at
EVERY integer. -/
theorem conjecture_4_2 {kk r : ℕ} (c : ℕ → K) (hc : c 0 ≠ 0) (H : ℤ → K)
    (hH : BilatRec (kk + 1) c H) (a b : Fin r → ℤ) (f : MvPolynomial (Fin r) K)
    (L : ℤ) (hL : ∀ n : ℤ, L ≤ n → polySubseq H a b f n = 0) :
    ∀ n : ℤ, polySubseq H a b f n = 0 := by
  obtain ⟨D, q, hrec⟩ := bilatRec_polySubseq c hc H hH a b f
  exact zero_of_eventually_zero hrec L hL

/-! ### Stage 4: the write-up's own generalisation -- several sequences, different orders

A direct mirror of stage 3 with `Matrix.blockDiagonal'` over the dependent index type
`Sigma i, Fin (k i + 1)`.  It compiled on the FIRST attempt, which is the whole argument for
having built the uniform-size case first: the primed lemmas line up one-for-one with the
unprimed ones. -/

/-- A block-diagonal family of invertible matrices of DIFFERING sizes is invertible. -/
noncomputable def blockGL' {r : ℕ} {k : Fin r → ℕ}
    (G : ∀ i, Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
    Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K :=
  Units.mk
    (Matrix.blockDiagonal' fun i => ((G i : Matrix (Fin (k i + 1)) (Fin (k i + 1)) K)))
    (Matrix.blockDiagonal' fun i =>
      (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
        Matrix (Fin (k i + 1)) (Fin (k i + 1)) K))
    (by
      rw [← Matrix.blockDiagonal'_mul]
      have h : (fun i => ((G i : Matrix (Fin (k i + 1)) (Fin (k i + 1)) K)) *
          (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
            Matrix (Fin (k i + 1)) (Fin (k i + 1)) K))
          = fun i => (1 : Matrix (Fin (k i + 1)) (Fin (k i + 1)) K) := by
        funext i; exact Units.mul_inv (G i)
      rw [h]
      exact Matrix.blockDiagonal'_one)
    (by
      rw [← Matrix.blockDiagonal'_mul]
      have h : (fun i => (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
            Matrix (Fin (k i + 1)) (Fin (k i + 1)) K) *
          ((G i : Matrix (Fin (k i + 1)) (Fin (k i + 1)) K)))
          = fun i => (1 : Matrix (Fin (k i + 1)) (Fin (k i + 1)) K) := by
        funext i; exact Units.inv_mul (G i)
      rw [h]
      exact Matrix.blockDiagonal'_one)

theorem blockGL'_coe {r : ℕ} {k : Fin r → ℕ}
    (G : ∀ i, Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
    ((blockGL' G : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K) :
      Matrix (Σ i : Fin r, Fin (k i + 1)) (Σ i : Fin r, Fin (k i + 1)) K)
      = Matrix.blockDiagonal' fun i =>
          ((G i : Matrix (Fin (k i + 1)) (Fin (k i + 1)) K)) := rfl

theorem blockGL'_inv_coe {r : ℕ} {k : Fin r → ℕ}
    (G : ∀ i, Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
    (((blockGL' G)⁻¹ : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K) :
      Matrix (Σ i : Fin r, Fin (k i + 1)) (Σ i : Fin r, Fin (k i + 1)) K)
      = Matrix.blockDiagonal' fun i =>
          (((G i)⁻¹ : Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
            Matrix (Fin (k i + 1)) (Fin (k i + 1)) K) := rfl

theorem blockGL'_coe_zpow {r : ℕ} {k : Fin r → ℕ}
    (G : ∀ i, Matrix.GeneralLinearGroup (Fin (k i + 1)) K) (n : ℤ) :
    ((blockGL' G ^ n : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K) :
      Matrix (Σ i : Fin r, Fin (k i + 1)) (Σ i : Fin r, Fin (k i + 1)) K)
      = Matrix.blockDiagonal' fun i =>
          ((G i ^ n : Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
            Matrix (Fin (k i + 1)) (Fin (k i + 1)) K) := by
  induction n using Int.induction_on with
  | zero =>
    simp only [zpow_zero, Units.val_one]
    exact Matrix.blockDiagonal'_one.symm
  | succ j ih =>
    rw [add_comm (j : ℤ) 1, zpow_add, zpow_one, Units.val_mul, ih, blockGL'_coe,
      ← Matrix.blockDiagonal'_mul]
    refine congrArg Matrix.blockDiagonal' (funext fun i => ?_)
    rw [← Units.val_mul]
    congr 1
    rw [zpow_add, zpow_one]
  | pred j ih =>
    have hinv : (blockGL' G ^ (-1 : ℤ) :
        Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K) = (blockGL' G)⁻¹ :=
      zpow_neg_one _
    rw [sub_eq_add_neg, add_comm (-(j : ℤ)) (-1), zpow_add, Units.val_mul, ih, hinv,
      blockGL'_inv_coe, ← Matrix.blockDiagonal'_mul]
    refine congrArg Matrix.blockDiagonal' (funext fun i => ?_)
    rw [← Units.val_mul]
    congr 1
    rw [zpow_add, zpow_neg_one]

theorem blockDiagonal'_mulVec_apply {r : ℕ} {k : Fin r → ℕ}
    (M : ∀ i, Matrix (Fin (k i + 1)) (Fin (k i + 1)) K)
    (v : (Σ i : Fin r, Fin (k i + 1)) → K) (p : Σ i : Fin r, Fin (k i + 1)) :
    (Matrix.blockDiagonal' M).mulVec v p = (M p.1).mulVec (fun j => v ⟨p.1, j⟩) p.2 := by
  obtain ⟨p1, p2⟩ := p
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    Fintype.sum_eq_single p1 (fun i hi => Finset.sum_eq_zero fun j _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hi), zero_mul]),
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.blockDiagonal'_apply_eq]

/-- The write-up's own object: a polynomial in arithmetic subsequences of SEVERAL bilateral
sequences, of possibly different orders. -/
noncomputable def polySubseqMulti {r : ℕ} (H : Fin r → ℤ → K) (a b : Fin r → ℤ)
    (f : MvPolynomial (Fin r) K) (n : ℤ) : K :=
  MvPolynomial.eval (fun i => H i (a i * n + b i)) f

theorem bilatRec_polySubseqMulti {r : ℕ} {k : Fin r → ℕ} (c : Fin r → ℕ → K)
    (hc : ∀ i, c i 0 ≠ 0) (H : Fin r → ℤ → K)
    (hH : ∀ i, BilatRec (k i + 1) (c i) (H i)) (a b : Fin r → ℤ)
    (f : MvPolynomial (Fin r) K) :
    ∃ (D : ℕ) (q : ℕ → K), BilatRec D q (polySubseqMulti H a b f) := by
  classical
  set G : ∀ i : Fin r, Matrix.GeneralLinearGroup (Fin (k i + 1)) K :=
    fun i => companionGL (k i) (c i) (hc i) ^ (a i) with hG
  set A : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K := blockGL' G with hA
  set w : (Σ i : Fin r, Fin (k i + 1)) → K :=
    fun p => stateVec (k p.1) (H p.1) (b p.1) p.2 with hw
  set F : MvPolynomial (Σ i : Fin r, Fin (k i + 1)) K :=
    MvPolynomial.rename
      (fun i : Fin r => (⟨i, (0 : Fin (k i + 1))⟩ : Σ i : Fin r, Fin (k i + 1))) f with hF
  obtain ⟨D, q, hrec⟩ := liftGoal_holds (Σ i : Fin r, Fin (k i + 1)) A w F
  refine ⟨D, q, ?_⟩
  have hpt : ∀ n : ℤ,
      (((A ^ n : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K) :
        Matrix (Σ i : Fin r, Fin (k i + 1)) (Σ i : Fin r, Fin (k i + 1)) K).mulVec w
        ∘ fun i : Fin r => (⟨i, (0 : Fin (k i + 1))⟩ : Σ i : Fin r, Fin (k i + 1)))
      = fun i => H i (a i * n + b i) := by
    intro n
    funext i
    have hblk : (((A ^ n : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin (k i + 1)) K) :
        Matrix (Σ i : Fin r, Fin (k i + 1)) (Σ i : Fin r, Fin (k i + 1)) K).mulVec w)
        (⟨i, (0 : Fin (k i + 1))⟩ : Σ i : Fin r, Fin (k i + 1))
        = ((G i ^ n : Matrix.GeneralLinearGroup (Fin (k i + 1)) K) :
            Matrix (Fin (k i + 1)) (Fin (k i + 1)) K).mulVec
            (fun j => w ⟨i, j⟩) (0 : Fin (k i + 1)) := by
      rw [hA, blockGL'_coe_zpow, blockDiagonal'_mulVec_apply]
    have hwi : (fun j => w (⟨i, j⟩ : Σ i : Fin r, Fin (k i + 1)))
        = stateVec (k i) (H i) (b i) := by funext j; rw [hw]
    rw [Function.comp_apply, hblk, hwi, hG, ← zpow_mul,
      companionGL_zpow_mulVec (k i) (c i) (hc i) (H i) (hH i) (b i) (a i * n)]
    simp only [stateVec, Fin.val_zero, Nat.cast_zero, add_zero]
    congr 1
    ring
  have hEq : stateSeq A w F = polySubseqMulti H a b f := by
    funext n
    simp only [stateSeq, polySubseqMulti, hF, MvPolynomial.eval_rename, hpt n]
  rw [← hEq]
  exact hrec

/-- **The write-up's Theorem, in full.** Several bilateral constant-recursive sequences, of
possibly different orders, arbitrary integer slopes and shifts, any polynomial, any field. -/
theorem conjecture_4_2_multi {r : ℕ} {k : Fin r → ℕ} (c : Fin r → ℕ → K)
    (hc : ∀ i, c i 0 ≠ 0) (H : Fin r → ℤ → K)
    (hH : ∀ i, BilatRec (k i + 1) (c i) (H i)) (a b : Fin r → ℤ)
    (f : MvPolynomial (Fin r) K) (L : ℤ)
    (hL : ∀ n : ℤ, L ≤ n → polySubseqMulti H a b f n = 0) :
    ∀ n : ℤ, polySubseqMulti H a b f n = 0 := by
  obtain ⟨D, q, hrec⟩ := bilatRec_polySubseqMulti c hc H hH a b f
  exact zero_of_eventually_zero hrec L hL
end Stage3

end Principia.MathDB.P340544
