import Principia.Common.ConvexIntegral

set_option autoImplicit false

/-!
# MathDB #347913 — convexity of hypergraph polynomials

Write-up `mathdb-open-problems/problems/347913/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.

For a family `E` of distinct nonempty subsets of a finite set `V`, and `d ≥ 2`,

    f_d(x) = ∑_{(e_1,…,e_d) ∈ E^d} ∏_{k=1}^d x_{e_k} / |e_1 ∪ … ∪ e_k|.

Brosch–Laurent–Steenkamp Conjecture 1 asks whether `f_d` is convex on the simplex when
`E = C([n], L)`.  The write-up proves more: `f_d` is strictly convex on the whole
nonnegative orthant, for ANY family of distinct nonempty hyperedges.

## The whole conjecture funnels through one identity

With `(T_v)` independent rate-one exponentials and `Y_e = min_{v ∈ e} T_v`, the write-up's
boxed theorem is

    f_d(x) = (1/d!) · E[ (∑_e x_e Y_e)^d ].                                   (moment)

Convexity is then immediate, because the integrand is a `d`-th power of a NONNEGATIVE
linear form in `x`, and `t ↦ t^d` is convex on `[0,∞)`.  Unwinding, the only probabilistic
content is a product formula for the joint moments.

## THE WRITE-UP'S PRODUCT FORMULA IS WRONG AS STATED, AND THE FIX IS A SUM

The write-up gives the probabilistic content as

    E[ ∏_{k=1}^d Y_{e_k} ] = d! / ∏_{k=1}^d |e_1 ∪ … ∪ e_k|.          (AS WRITTEN)

**The left-hand side is symmetric in the `e_k` and the right-hand side is not** — `|U_1|` is
`|e_1|`, which depends on which edge is listed first — so no per-tuple identity of this shape
can hold.  The smallest counterexample is closed-form: take `e_1 = {a}` and `e_2 = {b,c}`
disjoint.  Then `Y_1` and `Y_2` are INDEPENDENT, so `E[Y_1 Y_2] = (1/1)(1/2) = 1/2` exactly,
while (AS WRITTEN) gives `2!/(1·3) = 2/3` in one order and `2!/(2·3) = 1/3` in the other.
Neither is `1/2`.

**The correct statement is a SUM OVER ORDERINGS:**

    E[ ∏_{k=1}^d Y_{e_k} ] = ∑_{σ ∈ S_d} ∏_{k=1}^d 1/|e_{σ(1)} ∪ … ∪ e_{σ(k)}|.     (moments)

This is exact, not a repair by hand.  For nonnegative `Y`,
`E[∏ Y_k] = ∫_{[0,∞)^d} P(∀k, Y_k > t_k) dt`, and
`P(∀k, Y_k > t_k) = exp(-∑_v max{t_k : v ∈ e_k})`.  Splitting the orthant by the ordering of
`t` makes the exponent linear; the substitution `s_j = u_0 + … + u_j` turns each region into
a positive orthant and its integral into `∏_i 1/|e_{σ(i)} ∪ … ∪ e_{σ(d)}|`, a SUFFIX union.
Reversing `σ` turns suffixes into prefixes, giving (moments).

**The aggregate identity is unaffected.**  `f_d` sums over ALL tuples, which symmetrises the
right-hand side, so (moment) — and therefore `HasPowerRep` and everything the spine proves
from it — is correct.  It is the per-tuple formula, quoted as *the thing to prove*, that is
false; anyone formalising from it would have been proving a false lemma.  `hasPowerRep_of_moments`
below derives (moment) from (moments) by multilinear expansion and a reindexing.

Checked in `Campaigns/MathDB-Formalization/verify_347913_moment.py`, which computes the
moments exactly, cross-checks against Monte Carlo, and asserts the set of configurations
where (AS WRITTEN) fails is EXACTLY the expected one.  The three configurations where it
happens to agree all have EQUAL EDGE SIZES, which forces every ordering to give the same
product — that is why the error survived.

## What this module contains

A **SPINE**, now down to a single mathematical hypothesis.  `convex_of_power_rep` composes
the chain; PROVED here are both steps of the convexity half:

* `pow_linear_convexOn` — for nonnegative weights `Y`, the map `x ↦ (∑ i, x i * Y i)^d` is
  convex on the nonnegative orthant.  This is the step the write-up compresses into the
  word "Consequently".
* `integral_convexOn` — convexity passes from an integrand to its integral.  It is stated
  with explicit INTEGRABILITY side conditions, which are not pedantry: `∫` of a
  non-integrable function is `0` in Mathlib, and without them the inequality is false.
  The lemma is campaign-agnostic and belongs in `Common/` if a second row needs it.

What remains assumed is the MOMENT FORMULA (moments) — a finite list of numbers, one per
tuple `p : Fin d → ι` — plus the integrability it supplies.  `hasPowerRep_of_moments` covers
everything between that and the power representation, so the functional identity
`HasPowerRep` is no longer what is carried.

## Why this row is being opened now

Its triage said "skip"; that judgement was made WITHOUT reading the write-up, which is true
of 102 of the table's rows.  Read, it turns out the conjecture reduces to a single
expectation identity and an elementary convexity step — no Ehrhart theory, no missing
special function.  The same re-reading produced #376316, #358171 and #356321.
-/

namespace Principia.MathDB.P347913

open Finset MeasureTheory
open Principia.Common.ConvexIntegral

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `prefixUnion edge p k = e_{p 0} ∪ … ∪ e_{p k}`. -/
def prefixUnion (edge : ι → Finset V) {d : ℕ} (p : Fin d → ι) (k : Fin d) : Finset V :=
  (Finset.Iic k).biUnion (fun k' => edge (p k'))

/-- The write-up's `f_d`. -/
noncomputable def fpoly (edge : ι → Finset V) (d : ℕ) (x : ι → ℝ) : ℝ :=
  ∑ p : Fin d → ι, ∏ k : Fin d, x (p k) / ((prefixUnion edge p k).card : ℝ)

/-- The write-up's boxed identity (moment), stated as the property the convexity argument
consumes: `f_d` is `1/d!` times an average of `d`-th powers of nonnegative linear forms. -/
def HasPowerRep (edge : ι → Finset V) (d : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (Y : Ω → ι → ℝ) : Prop :=
  (∀ ω i, 0 ≤ Y ω i) ∧
    ∀ x : ι → ℝ, fpoly edge d x
      = (1 / (d.factorial : ℝ)) * ∫ ω, (∑ i, x i * Y ω i) ^ d ∂μ

/-! ### The spine

Both the pointwise convexity and its passage through the integral are now PROVED, so the
spine carries ONE mathematical hypothesis — and as of 2026-09-24 it is the MOMENT FORMULA
`HasMomentFormula` (a finite list of moment values, summed over orderings) rather than the
functional identity `HasPowerRep`, with `hasPowerRep_of_moments` bridging them.

**A vacuity warning that is not addressed here.**  `convex_of_power_rep` and
`hasPowerRep_of_moments` both QUANTIFY over `(Ω, μ, Y)`; no witness is exhibited anywhere in
this module, so each is an implication that has not been shown non-vacuous for `d ≥ 2`.  A
Dirac measure witnesses `d ≤ 1` and provably cannot witness `d ≥ 2` (its moments factor).
Building the real witness — `Ω = V → ℝ` with a product of rate-one exponentials, and
`Y_e = min_{v ∈ e} T_v` — needs product measures and the exponential distribution, and is
the whole remaining job. -/

theorem convex_of_power_rep (edge : ι → Finset V) (d : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (Y : Ω → ι → ℝ)
    (rep : HasPowerRep edge d Ω μ Y)
    (hint : ∀ x ∈ orthant ι,
      Integrable (fun ω => (∑ i, x i * Y ω i) ^ d) μ) :
    ConvexOn ℝ (orthant ι) (fpoly edge d) := by
  obtain ⟨hY, hrep⟩ := rep
  have hpt : ∀ ω, ConvexOn ℝ (orthant ι) (fun x : ι → ℝ => (∑ i, x i * Y ω i) ^ d) :=
    fun ω => pow_linear_convexOn (Y ω) (hY ω) d
  have hcv := integral_convexOn μ (fun x ω => (∑ i, x i * Y ω i) ^ d) hpt hint
  have hfac : (0 : ℝ) ≤ 1 / (d.factorial : ℝ) := by positivity
  have hfun : fpoly edge d = fun x : ι → ℝ =>
      (1 / (d.factorial : ℝ)) * ∫ ω, (∑ i, x i * Y ω i) ^ d ∂μ := funext hrep
  rw [hfun]
  simpa [smul_eq_mul] using hcv.smul hfac

/-! ### The moment formula, and the narrowing of the carried hypothesis

`HasPowerRep` is an identity between FUNCTIONS of a real vector `x`.  What the probability
actually supplies is a finite list of numbers — one joint moment per tuple `p : Fin d → ι`.
Everything between the two is multilinear expansion and a reindexing, and that is proved
here, so the carried hypothesis shrinks to `HasMomentFormula`.

The expansion is `Finset.prod_univ_sum` (a `d`-fold product of one sum is a sum over
`Fin d → ι`); the integral passes through the finite sum by `integral_finsetSum`; and the
`d!` is recovered by reindexing `p ↦ p ∘ σ` for each `σ : Equiv.Perm (Fin d)`, under which the
monomial `∏_k x_{p k}` is invariant (`Equiv.prod_comp`) while the coefficient is not.  That
reindexing is exactly why the per-tuple formula needed the sum over orderings. -/

/-- The coefficient `f_d` attaches to the tuple `p`: `∏_k 1/|e_{p_1} ∪ … ∪ e_{p_k}|`. -/
noncomputable def coeff (edge : ι → Finset V) {d : ℕ} (p : Fin d → ι) : ℝ :=
  ∏ k, (1 / ((prefixUnion edge p k).card : ℝ))

omit [DecidableEq ι] in
/-- `f_d` with its coefficients separated from the monomials. -/
theorem fpoly_eq_sum (edge : ι → Finset V) (d : ℕ) (x : ι → ℝ) :
    fpoly edge d x = ∑ p : Fin d → ι, (∏ k, x (p k)) * coeff edge p := by
  rw [fpoly]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [coeff, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun k _ => by ring)

/-- **The product formula, CORRECTED.**  The moment is a SUM OVER ORDERINGS of the
prefix-union coefficient, not `d!` times a single ordering's.  The left-hand side is
symmetric in the `e_k` and a single ordering's coefficient is not, so no per-tuple form
without the sum can be right. -/
-- SPEC-CARRY-CHECKED: HasMomentFormula -- 2026-09-26.  This spec IS a campaign FINDING, not an
-- unexamined assumption: the write-up's per-tuple product formula is FALSE as stated, and this
-- is the corrected form (a sum over orderings of the prefix-union coefficient, since the left
-- side is symmetric in the `e_k` and a single ordering's coefficient is not).  Carried as the
-- measure-theoretic input on an uncounted row.
def HasMomentFormula (edge : ι → Finset V) (d : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (Y : Ω → ι → ℝ) : Prop :=
  (∀ ω i, 0 ≤ Y ω i) ∧
    ∀ p : Fin d → ι, ∫ ω, ∏ k, Y ω (p k) ∂μ
      = ∑ σ : Equiv.Perm (Fin d), coeff edge (p ∘ σ)

omit [DecidableEq ι] in
/-- **The narrowing.**  `HasPowerRep` is an identity between functions of a real vector `x`;
`HasMomentFormula` is a finite list of moment values.  Everything between them is
multilinear expansion and a reindexing, and that is proved here. -/
theorem hasPowerRep_of_moments (edge : ι → Finset V) (d : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (Y : Ω → ι → ℝ)
    (hm : HasMomentFormula edge d Ω μ Y)
    (hint : ∀ p : Fin d → ι, Integrable (fun ω => ∏ k, Y ω (p k)) μ) :
    HasPowerRep edge d Ω μ Y := by
  obtain ⟨hY, hmom⟩ := hm
  refine ⟨hY, fun x => ?_⟩
  -- multilinear expansion of the d-th power
  have hexp : ∀ ω, (∑ i, x i * Y ω i) ^ d
      = ∑ p : Fin d → ι, (∏ k, x (p k)) * ∏ k, Y ω (p k) := by
    intro ω
    have h1 : (∑ i, x i * Y ω i) ^ d = ∏ _k : Fin d, (∑ i, x i * Y ω i) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun p _ => Finset.prod_mul_distrib)
  have hintegral : ∫ ω, (∑ i, x i * Y ω i) ^ d ∂μ
      = ∑ p : Fin d → ι, (∏ k, x (p k)) * ∫ ω, ∏ k, Y ω (p k) ∂μ := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun p _ => (hint p).const_mul _)]
    exact Finset.sum_congr rfl (fun p _ => integral_const_mul _ _)
  rw [hintegral]
  simp_rw [hmom]
  rw [fpoly_eq_sum]
  -- swap the two sums, then reindex p by the permutation
  have hswap : ∑ p : Fin d → ι,
        (∏ k, x (p k)) * ∑ σ : Equiv.Perm (Fin d), coeff edge (p ∘ σ)
      = ∑ σ : Equiv.Perm (Fin d),
          ∑ p : Fin d → ι, (∏ k, x (p k)) * coeff edge (p ∘ σ) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hre : ∀ σ : Equiv.Perm (Fin d),
      ∑ p : Fin d → ι, (∏ k, x (p k)) * coeff edge (p ∘ σ)
        = ∑ q : Fin d → ι, (∏ k, x (q k)) * coeff edge q := by
    intro σ
    refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl ι)) _ _ (fun p => ?_)
    have : ∏ k, x (p k) = ∏ k, x (p (σ k)) := (Equiv.prod_comp σ (fun k => x (p k))).symm
    rw [this]
    rfl
  rw [hswap, Finset.sum_congr rfl (fun σ _ => hre σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hd : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  field_simp

/-! ### The vacuity warning above, settled at `d = 1` and at `d = 2`

The header records that `convex_of_power_rep` and `hasPowerRep_of_moments` quantify over
`(Ω, μ, Y)` with no witness anywhere, and asserts in prose that *"a Dirac measure witnesses
`d ≤ 1` and provably cannot witness `d ≥ 2` (its moments factor)"*.  Both halves are now proved,
which is what turns a warning into a statement:

* `dirac_hasMomentFormula_one` exhibits the Dirac witness at `d = 1`, so the `d = 1` instance is
  known non-vacuous.  **It is a witness for the degenerate stratum only** — the conjecture starts
  at `d = 2` — and it is recorded in exactly those terms rather than as "the spec is satisfied".
* `dirac_not_hasMomentFormula_two` proves no Dirac can work at `d = 2` as soon as two edges
  differ.  The mechanism is sharper than "its moments factor": the constant tuples pin
  `(Y i)² = 2/|eᵢ|²`, the mixed tuple pins `Y i · Y j = (|eᵢ|+|eⱼ|)/(|eᵢ||eⱼ||eᵢ∪eⱼ|)`, and
  squaring the second against the first forces `2|eᵢ∪eⱼ| = |eᵢ| + |eⱼ|` — which, against
  `|eᵢ∪eⱼ| ≥ |eᵢ|, |eⱼ|`, collapses to `eᵢ = eⱼ`.

So the remaining job is exactly what the header says it is: the product-measure witness.  What has
changed is that its necessity is now proved rather than asserted.

`fin_zero_le` and `Iic_zero_eq` mention nothing of this campaign and are `Common/` promotion
candidates. -/

theorem fin_zero_le {d : ℕ} [NeZero d] (k : Fin d) : (0 : Fin d) ≤ k := by
  rw [Fin.le_def]
  simp

theorem Iic_zero_eq {d : ℕ} [NeZero d] : (Finset.Iic (0 : Fin d)) = {0} := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_singleton]
  exact ⟨fun h => le_antisymm h (fin_zero_le k), fun h => h ▸ le_refl _⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The first prefix union is just the first edge. -/
theorem prefixUnion_zero (edge : ι → Finset V) {d : ℕ} [NeZero d] (p : Fin d → ι) :
    prefixUnion edge p 0 = edge (p 0) := by
  rw [prefixUnion, Iic_zero_eq, Finset.singleton_biUnion]

omit [Fintype ι] [DecidableEq ι] in
/-- For a CONSTANT tuple every prefix union is the same edge. -/
theorem prefixUnion_const (edge : ι → Finset V) {d : ℕ} [NeZero d] (i : ι) (k : Fin d) :
    prefixUnion edge (fun _ => i) k = edge i := by
  simp only [prefixUnion]
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_Iic]
  exact ⟨fun ⟨_, _, hv⟩ => hv, fun hv => ⟨0, fin_zero_le k, hv⟩⟩

/-- `coeff` at a constant tuple is the reciprocal edge size to the `d`-th power. -/
theorem coeff_const (edge : ι → Finset V) (d : ℕ) [NeZero d] (i : ι) :
    coeff edge (fun _ : Fin d => i) = (1 / ((edge i).card : ℝ)) ^ d := by
  simp only [coeff, prefixUnion_const]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **A Dirac measure witnesses the moment formula at `d = 1`** — the degenerate stratum only. -/
theorem dirac_hasMomentFormula_one (edge : ι → Finset V) :
    HasMomentFormula edge 1 Unit (Measure.dirac ())
      (fun _ i => 1 / ((edge i).card : ℝ)) := by
  refine ⟨fun _ i => by positivity, fun p => ?_⟩
  rw [integral_dirac]
  have hone : ∀ σ : Equiv.Perm (Fin 1), coeff edge (p ∘ σ) = coeff edge p := by
    intro σ
    congr 1
    funext k
    simp [Subsingleton.elim (σ k) k]
  rw [Finset.sum_congr rfl (fun σ _ => hone σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  simp only [Nat.factorial_one, one_smul, coeff]
  rw [Fin.prod_univ_one, Fin.prod_univ_one, prefixUnion_zero]

/-- **NO Dirac measure witnesses the moment formula at `d = 2` once two edges differ**, so the
product-measure witness is genuinely required rather than merely preferred. -/
theorem dirac_not_hasMomentFormula_two (edge : ι → Finset V) (i j : ι)
    (hij : edge i ≠ edge j) (hi : (edge i).Nonempty) (hj : (edge j).Nonempty)
    (Y : Unit → ι → ℝ)
    (h : HasMomentFormula edge 2 Unit (Measure.dirac ()) Y) : False := by
  obtain ⟨-, hmom⟩ := h
  have hm0 : (0 : ℝ) < ((edge i).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hi
  have hn0 : (0 : ℝ) < ((edge j).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hj
  have hu0 : (0 : ℝ) < ((edge i ∪ edge j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hi.mono Finset.subset_union_left)
  have hconst : ∀ k : ι, (Y () k) ^ 2 = 2 * (1 / ((edge k).card : ℝ)) ^ 2 := by
    intro k
    have hk := hmom (fun _ => k)
    rw [integral_dirac] at hk
    have hL : ∏ t : Fin 2, Y () ((fun _ => k) t) = (Y () k) ^ 2 := by
      rw [Fin.prod_univ_two]; ring
    have hR : ∑ σ : Equiv.Perm (Fin 2), coeff edge ((fun _ => k) ∘ σ)
        = 2 * (1 / ((edge k).card : ℝ)) ^ 2 := by
      have hc : ∀ σ : Equiv.Perm (Fin 2),
          coeff edge ((fun _ => k) ∘ σ) = (1 / ((edge k).card : ℝ)) ^ 2 :=
        fun σ => coeff_const edge 2 k
      rw [Finset.sum_congr rfl (fun σ _ => hc σ), Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      rw [nsmul_eq_mul]
      norm_num
    rw [hL, hR] at hk
    exact hk
  have hmix := hmom (fun k => if k = 0 then i else j)
  rw [integral_dirac] at hmix
  have hL : ∏ t : Fin 2, Y () ((fun k => if k = 0 then i else j) t) = Y () i * Y () j := by
    rw [Fin.prod_univ_two]; norm_num
  have hIic1 : (Finset.Iic (1 : Fin 2)) = {0, 1} := by decide
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hR : ∑ σ : Equiv.Perm (Fin 2), coeff edge ((fun k => if k = 0 then i else j) ∘ σ)
      = 1 / (((edge i).card : ℝ) * ((edge i ∪ edge j).card : ℝ))
        + 1 / (((edge j).card : ℝ) * ((edge i ∪ edge j).card : ℝ)) := by
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton, coeff, coeff,
      Fin.prod_univ_two, Fin.prod_univ_two]
    have q0 : prefixUnion edge ((fun k => if k = 0 then i else j) ∘ (1 : Equiv.Perm (Fin 2))) 0
        = edge i := by rw [prefixUnion, Iic_zero_eq (d := 2), Finset.singleton_biUnion]; norm_num
    have q1 : prefixUnion edge ((fun k => if k = 0 then i else j) ∘ (1 : Equiv.Perm (Fin 2))) 1
        = edge i ∪ edge j := by
      rw [prefixUnion, hIic1]
      rw [Finset.biUnion_insert, Finset.singleton_biUnion]
      norm_num
    have r0 : prefixUnion edge ((fun k => if k = 0 then i else j) ∘ (Equiv.swap (0 : Fin 2) 1)) 0
        = edge j := by
      rw [prefixUnion, Iic_zero_eq (d := 2), Finset.singleton_biUnion]
      simp [Function.comp]
    have r1 : prefixUnion edge ((fun k => if k = 0 then i else j) ∘ (Equiv.swap (0 : Fin 2) 1)) 1
        = edge i ∪ edge j := by
      rw [prefixUnion, hIic1, Finset.biUnion_insert, Finset.singleton_biUnion]
      simp only [Function.comp]
      rw [show (Equiv.swap (0 : Fin 2) 1) 0 = 1 from by decide,
        show (Equiv.swap (0 : Fin 2) 1) 1 = 0 from by decide]
      norm_num [Finset.union_comm]
    rw [q0, q1, r0, r1]
    ring
  rw [hL, hR] at hmix
  have hsq : (Y () i * Y () j) ^ 2
      = 4 * (1 / ((edge i).card : ℝ)) ^ 2 * (1 / ((edge j).card : ℝ)) ^ 2 := by
    have hexp : (Y () i * Y () j) ^ 2 = (Y () i) ^ 2 * (Y () j) ^ 2 := by ring
    rw [hexp, hconst i, hconst j]; ring
  rw [hmix] at hsq
  have hkey : ((edge i).card : ℝ) + ((edge j).card : ℝ) = 2 * ((edge i ∪ edge j).card : ℝ) := by
    have h1 : (((edge i).card : ℝ) + ((edge j).card : ℝ)) ^ 2
        = 4 * ((edge i ∪ edge j).card : ℝ) ^ 2 := by
      field_simp at hsq
      nlinarith [hsq, hm0, hn0, hu0]
    nlinarith [h1, hm0, hn0, hu0]
  have hmu : ((edge i).card : ℝ) ≤ ((edge i ∪ edge j).card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.subset_union_left
  have hnu : ((edge j).card : ℝ) ≤ ((edge i ∪ edge j).card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.subset_union_right
  have hi' : edge i = edge i ∪ edge j := by
    refine Finset.eq_of_subset_of_card_le Finset.subset_union_left ?_
    have : ((edge i ∪ edge j).card : ℝ) ≤ ((edge i).card : ℝ) := by linarith
    exact_mod_cast this
  have hj' : edge j = edge i ∪ edge j := by
    refine Finset.eq_of_subset_of_card_le Finset.subset_union_right ?_
    have : ((edge i ∪ edge j).card : ℝ) ≤ ((edge j).card : ℝ) := by linarith
    exact_mod_cast this
  exact hij (hi'.trans hj'.symm)

end Principia.MathDB.P347913
