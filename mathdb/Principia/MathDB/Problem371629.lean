/-
Copyright (c) 2026 Principia. All rights reserved.
Released under Apache 2.0.
-/
-- `ℝ` is what the first draft forgot: without it the structure's `toFun : Set G → ℝ` field fails
-- to elaborate, the whole `structure` is rejected, and every later error in the file is a cascade
-- from that one.  The reported first error was a stuck `HAdd` instance three lines further down.
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
-- `limsup_add_le` is NOT in `Order.LiminfLimsup`; it needs the topological-order file, and
-- it is declared at root level under `open Filter`, so it is not `Filter.`-qualified either.
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Data.ZMod.Basic
-- Schur's theorem for l1, built separately because Mathlib has none.
import Principia.MathDB.SchurL1
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# #371629 — mensural densities and Reiter sequences: the finitely additive layer

**The row.**  For probability masses `μ n ∈ ℓ¹(G)` on an infinite commutative discrete group,
`d̄(A) = limsup_n μ_n(A)` is an upper density in the sense of Révész–Ruzsa **iff**
`∑_x |μ_n(x) − μ_n(x+t)| → 0` for every `t` (the Reiter condition).  Sufficiency is noted in the
source; the substance is necessity, and its five steps are: dominated ultralimits → cyclic block
selectors → a swap argument → weak nullity → the **Schur property of ℓ¹**.

**What this module is.**  Steps one and three consume a *finitely additive probability defined on
every subset* of `G`, and the swap argument is where the proof's weight sits.  Both are stated here
and fully proved.  Nothing here mentions the group, the measures, or the density, so nothing here is
waiting on the parts that are hard.

**Why a bespoke structure rather than `MeasureTheory.AddContent`.**  `AddContent` is indexed by a
`SetSemiring` and its additivity is stated over `Finset`-indexed families drawn from that semiring.
Here the domain is *all* of `Set G` — the selector argument forms complements, differences and
arbitrary unions of selectors freely — so the semiring bookkeeping would be pure overhead on a
lattice where every operation is already available.  Four fields, and the semiring's own additivity
is recovered as `sum_biUnion` below.

**The one fact the whole selector argument runs on** is `eq_of_partition_pair`: two sets that
complete the *same* third set to the *same* total have equal measure.  In the source this is the
step from "both selectors have measure `1/L`" to `q(E+it) = q(E+jt)`, and it is where the
translation invariance actually comes from.  Stated with the group stripped out, it is four lines —
which is the point of stripping the group out.

**Known trap, avoided here.**  `union_diff_cancel` is deprecated in this Mathlib (the live name is
`union_sdiff_cancel`), so `mono` builds `A ∪ (B \ A) = B` by hand rather than quoting either.
-/

namespace Principia.MathDB.P371629

/-- A finitely additive probability measure defined on **every** subset of `G`. -/
structure FinAddProb (G : Type*) where
  /-- The measure of a set. -/
  toFun : Set G → ℝ
  /-- Measures are nonnegative. -/
  nonneg : ∀ A, 0 ≤ toFun A
  /-- The total mass is one. -/
  univ_eq : toFun Set.univ = 1
  /-- Finite additivity on disjoint pairs. -/
  additive : ∀ A B : Set G, Disjoint A B → toFun (A ∪ B) = toFun A + toFun B

namespace FinAddProb

variable {G : Type*} (q : FinAddProb G)

theorem empty : q.toFun ∅ = 0 := by
  have hd : Disjoint (Set.univ : Set G) (∅ : Set G) := by simp
  have h := q.additive Set.univ ∅ hd
  rw [Set.union_empty, q.univ_eq] at h
  linarith

/-- `B` splits as `A` and `B \ A`. -/
theorem eq_add_diff {A B : Set G} (h : A ⊆ B) :
    q.toFun B = q.toFun A + q.toFun (B \ A) := by
  have hset : A ∪ (B \ A) = B := by
    ext x
    constructor
    · rintro (hx | ⟨hx, -⟩)
      · exact h hx
      · exact hx
    · intro hx
      by_cases hA : x ∈ A
      · exact Or.inl hA
      · exact Or.inr ⟨hx, hA⟩
  have hd : Disjoint A (B \ A) := Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx
  have := q.additive A (B \ A) hd
  rw [hset] at this
  exact this

theorem mono {A B : Set G} (h : A ⊆ B) : q.toFun A ≤ q.toFun B := by
  have := q.eq_add_diff h
  linarith [q.nonneg (B \ A)]

theorem le_one (A : Set G) : q.toFun A ≤ 1 := by
  have := q.mono (Set.subset_univ A)
  rw [q.univ_eq] at this
  exact this

/-- Finite additivity over a `Finset`-indexed pairwise disjoint family — the additivity an
`AddContent` on a semiring would give, recovered on the full power set. -/
theorem sum_biUnion {ι : Type*} [DecidableEq ι] (C : ι → Set G)
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) (s : Finset ι) :
    q.toFun (⋃ i ∈ s, C i) = ∑ i ∈ s, q.toFun (C i) := by
  refine Finset.induction_on s ?_ ?_
  · simp [q.empty]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, q.additive, ih]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by rintro rfl; exact ha hi)

end FinAddProb

/-! ### The swap argument, with the group stripped out -/

variable {G : Type*}

/-- **Two sets that complete the same third set to the same total have equal measure.**

This is the whole engine of the selector argument.  In the source, `X = E + it`, `Z = E + jt` and
`Y = (C₀ \ E) + jt`: the selector `S = X ∪ Y` has measure `1/L`, and so does `C_j = Z ∪ Y`, whence
`q(E+it) = q(E+jt)` — which is translation invariance in the making. -/
theorem eq_of_partition_pair (q : FinAddProb G) {X Y Z : Set G} {c : ℝ}
    (hXY : Disjoint X Y) (hXYq : q.toFun (X ∪ Y) = c)
    (hZY : Disjoint Z Y) (hZYq : q.toFun (Z ∪ Y) = c) :
    q.toFun X = q.toFun Z := by
  have h1 := q.additive X Y hXY
  have h2 := q.additive Z Y hZY
  rw [hXYq] at h1
  rw [hZYq] at h2
  linarith

/-- **Two disjoint sets, each capped by `c`, whose union has measure `2c`, both attain `c`.**

The source states this as "consequently both inequalities are equalities".  It is the step that
converts the *upper* bound `q(S) ≤ d̄(S) = 1/L` on selectors into the *exact* value needed. -/
theorem eq_of_le_of_union (q : FinAddProb G) {S S' : Set G} {c : ℝ}
    (hS : q.toFun S ≤ c) (hS' : q.toFun S' ≤ c) (hdisj : Disjoint S S')
    (hunion : q.toFun (S ∪ S') = 2 * c) :
    q.toFun S = c ∧ q.toFun S' = c := by
  have h := q.additive S S' hdisj
  rw [hunion] at h
  exact ⟨by linarith, by linarith⟩

/-- **A partition into `L` pieces each capped by `c`, with total `L · c`, has every piece at `c`.**

Applied with `c = 1/L` and the `L` translates `C_0, …, C_{L−1}`: domination gives `q(C_i) ≤ 1/L`,
the total is `q(G) = 1`, and the conclusion `q(C_i) = 1/L` is equation (7) of the source. -/
theorem eq_of_le_of_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hle : ∀ i ∈ s, f i ≤ c) (hsum : ∑ i ∈ s, f i = (s.card : ℝ) * c) :
    ∀ i ∈ s, f i = c := by
  refine (Finset.sum_eq_sum_iff_of_le hle).1 ?_
  rw [hsum, Finset.sum_const, nsmul_eq_mul]

/-- The partition form, stated directly against `sum_biUnion`: an `L`-piece partition of `G` whose
pieces are each capped by `c = 1/L` has every piece exactly `1/L`. -/
theorem eq_of_le_of_biUnion_univ (q : FinAddProb G) {ι : Type*} [DecidableEq ι]
    (C : ι → Set G) (hd : Pairwise fun i j => Disjoint (C i) (C j)) (s : Finset ι)
    (hcov : (⋃ i ∈ s, C i) = Set.univ) (hs : s.Nonempty)
    (hle : ∀ i ∈ s, q.toFun (C i) ≤ (s.card : ℝ)⁻¹) :
    ∀ i ∈ s, q.toFun (C i) = (s.card : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    have : 0 < s.card := Finset.card_pos.mpr hs
    exact_mod_cast this
  refine eq_of_le_of_sum_eq s (fun i => q.toFun (C i)) _ hle ?_
  rw [← q.sum_biUnion C hd s, hcov, q.univ_eq]
  field_simp


/-! ### Step 1: dominated ultralimits

The source's first step.  Every `μ n` takes values in `[0,1]`, which is compact, so the pushforward
ultrafilter converges; `choose` picks a limit for **every** subset at once, and the three
`FinAddProb` fields are three applications of uniqueness of limits.

Nothing here needs the ultrafilter to be free.  Freeness is wanted only for the *domination*
`q(A) ≤ limsup_n μ_n(A)`, which is what ties the ultralimit back to the density and is the next
brick. -/

/-- **An ultrafilter limit of finitely additive probabilities is one.** -/
theorem exists_finAddProb_ultralimit (U : Ultrafilter ℕ) (μ : ℕ → FinAddProb G) :
    ∃ q : FinAddProb G, ∀ A, Filter.Tendsto (fun n => (μ n).toFun A) U (nhds (q.toFun A)) := by
  have hex : ∀ A : Set G, ∃ x ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n => (μ n).toFun A) U (nhds x) := by
    intro A
    have hmap : ((Ultrafilter.map (fun n => (μ n).toFun A) U) : Filter ℝ)
        ≤ Filter.principal (Set.Icc 0 1) := by
      rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
      filter_upwards with n
      simp only [Set.mem_preimage, Set.mem_Icc]
      exact ⟨(μ n).nonneg A, (μ n).le_one A⟩
    obtain ⟨x, hx, hle⟩ :=
      isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map (fun n => (μ n).toFun A) U) hmap
    refine ⟨x, hx, ?_⟩
    rwa [Filter.Tendsto, ← Ultrafilter.coe_map]
  choose f hf hlim using hex
  refine ⟨⟨f, fun A => (hf A).1, ?_, ?_⟩, hlim⟩
  · have he : (fun n => (μ n).toFun Set.univ) = fun _ => (1 : ℝ) :=
      funext fun n => (μ n).univ_eq
    have h1 := hlim Set.univ
    rw [he] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · intro A B hd
    have he : (fun n => (μ n).toFun (A ∪ B)) = fun n => (μ n).toFun A + (μ n).toFun B :=
      funext fun n => (μ n).additive A B hd
    have h1 := hlim (A ∪ B)
    rw [he] at h1
    exact tendsto_nhds_unique h1 ((hlim A).add (hlim B))


/-! ### The domination, and where freeness is actually used

`q(A) ≤ limsup_n μ_n(A)` is the clause that ties the ultralimit back to the density, and it is the
**only** place the ultrafilter has to be free.  The mechanism is one line of filter algebra: a set
in a free ultrafilter cannot have its complement in `atTop`, or both would lie in the ultrafilter
and it would be `⊥`.  So every `U`-eventual statement is `atTop`-frequent, and frequent-below is
what `Filter.le_limsup_of_frequently_le` consumes.

Stated for a bare sequence rather than for `FinAddProb`, because that is all it is about; the
`FinAddProb` version is one line on top. -/

/-- **A limit along a free ultrafilter is at most the `limsup`.** -/
theorem le_limsup_of_tendsto_ultrafilter (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ Filter.atTop) (f : ℕ → ℝ) (L : ℝ)
    (hL : Filter.Tendsto f U (nhds L)) (hb : ∀ n, f n ≤ 1) :
    L ≤ Filter.limsup f Filter.atTop := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f :=
    Filter.isBoundedUnder_of ⟨1, hb⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfreq : ∃ᶠ n in Filter.atTop, L - ε ≤ f n := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    -- `hfree` turns an `atTop`-eventual statement into a `U`-eventual one; the ultralimit gives
    -- the opposite one; an ultrafilter cannot hold both.
    have h1 : ∀ᶠ n in (U : Filter ℕ), ¬ (L - ε ≤ f n) := hfree hcon
    have h2 : ∀ᶠ n in (U : Filter ℕ), L - ε < f n :=
      hL.eventually (eventually_gt_nhds (by linarith))
    have h3 : ∀ᶠ _n in (U : Filter ℕ), False := by
      filter_upwards [h1, h2] with n hn1 hn2
      exact hn1 (le_of_lt hn2)
    obtain ⟨_, hfalse⟩ := h3.exists
    exact hfalse
  have hle := Filter.le_limsup_of_frequently_le hfreq hbdd
  linarith

/-- **Step 1 in the form the selector lemma consumes**: a free ultrafilter turns a sequence of
finitely additive probabilities into a single one dominated by the upper density. -/
theorem exists_finAddProb_le_limsup (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ Filter.atTop) (μ : ℕ → FinAddProb G) :
    ∃ q : FinAddProb G,
      ∀ A, q.toFun A ≤ Filter.limsup (fun n => (μ n).toFun A) Filter.atTop := by
  obtain ⟨q, hq⟩ := exists_finAddProb_ultralimit U μ
  exact ⟨q, fun A =>
    le_limsup_of_tendsto_ultrafilter U hfree _ _ (hq A) fun n => (μ n).le_one A⟩


/-! ### Step 4: weak nullity

The source argues by contradiction — "if (12) failed, then after passing to a subsequence and
choosing one sign there would be an `ε > 0` …, and a free ultrafilter concentrated on that
subsequence would give a non-translation-invariant `q_𝒰`".

None of that is needed.  `Filter.tendsto_iff_ultrafilter` says convergence along `atTop` **is**
convergence along every ultrafilter refining `atTop`, so the subsequence extraction, the sign
choice and the `ε` are all internal to a lemma Mathlib already has.  What remains is to observe
that along any such ultrafilter the two sequences converge to `q A` and `q B`, which agree.

This is the step where the earlier separation pays off: `exists_finAddProb_ultralimit` was proved
for an *arbitrary* ultrafilter, so it applies verbatim to the one `tendsto_iff_ultrafilter` hands
over, and freeness is carried only as a hypothesis to be passed along. -/

/-- **Weak nullity.**  If every free-ultrafilter limit of the measures gives `A` and `B` the same
mass, then `μ_n(A) − μ_n(B) → 0`. -/
theorem tendsto_sub_of_ultralimit_eq (μ : ℕ → FinAddProb G) (A B : Set G)
    (h : ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.atTop →
      ∀ q : FinAddProb G,
        (∀ C, Filter.Tendsto (fun n => (μ n).toFun C) U (nhds (q.toFun C))) →
        q.toFun A = q.toFun B) :
    Filter.Tendsto (fun n => (μ n).toFun A - (μ n).toFun B) Filter.atTop (nhds 0) := by
  refine (Filter.tendsto_iff_ultrafilter _ _ _).2 fun U hU => ?_
  obtain ⟨q, hq⟩ := exists_finAddProb_ultralimit U μ
  have hAB := h U hU q hq
  have hsub := (hq A).sub (hq B)
  rwa [hAB, sub_self] at hsub

/-- The same statement with the invariance supplied as a property of the *sets* rather than of each
limit: if `A` and `B` are interchangeable under every dominated finitely additive probability, the
difference of the measures is null. -/
theorem tendsto_sub_of_forall_dominated (μ : ℕ → FinAddProb G) (d : Set G → ℝ) (A B : Set G)
    (hdom : ∀ (q : FinAddProb G), (∀ C, q.toFun C ≤ d C) → q.toFun A = q.toFun B)
    (hle : ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.atTop →
      ∀ q : FinAddProb G,
        (∀ C, Filter.Tendsto (fun n => (μ n).toFun C) U (nhds (q.toFun C))) →
        ∀ C, q.toFun C ≤ d C) :
    Filter.Tendsto (fun n => (μ n).toFun A - (μ n).toFun B) Filter.atTop (nhds 0) :=
  tendsto_sub_of_ultralimit_eq μ A B fun U hU q hq => hdom q (hle U hU q hq)


section Height

variable [AddCommGroup G]

/-! ### Step 2: the cyclic blocks, as residue classes of a height

The source builds the blocks from a transversal `R` for the cosets of `⟨t⟩`, cuts each `t`-orbit
into consecutive `L`-blocks, and sets `C_i` to be the `i`-th points of all blocks.  Every element of
that construction — the transversal, the orbit, the block index — collapses into **one** object: an
integer coordinate along the orbit,

  `k : G → ℤ`  with  `k (x + t) = k x + 1`,

and the classes are then the fibres of `k` modulo `L`.  A transversal is exactly what is needed to
*produce* such a `k`, so nothing is being assumed away; what changes is that the construction is
isolated in one existence statement and every consequence below is choice-free.

**Indexing by `ZMod L`, not by `Finset.range L`.**  This is the whole reason the section is short.
With `ℕ` indices the translation step reads `C_i + t = C_{(i+1) mod L}` and every proof carries a
wrap-around case split at `i = L − 1`.  Over `ZMod L` the same step is `C_i + t = C_{i+1}` with no
case at all, because the wrap is the ring's own arithmetic.  The partition and covering statements
likewise become "the fibres of a map into a fintype", which is what they actually are. -/

/-- **A `t`-height**: an integer coordinate advancing by one along the `t`-orbit. -/
def IsHeight (t : G) (k : G → ℤ) : Prop := ∀ x, k (x + t) = k x + 1

/-- The `i`-th residue class of a height, modulo `L` — the source's `C_i`. -/
def heightClass (k : G → ℤ) (L : ℕ) (i : ZMod L) : Set G := {x | ((k x : ℤ) : ZMod L) = i}

theorem mem_heightClass_self (k : G → ℤ) (L : ℕ) (x : G) :
    x ∈ heightClass k L ((k x : ZMod L)) := rfl

/-- Distinct classes are disjoint: they are fibres of one map. -/
theorem heightClass_disjoint (k : G → ℤ) (L : ℕ) {i j : ZMod L} (h : i ≠ j) :
    Disjoint (heightClass k L i) (heightClass k L j) :=
  Set.disjoint_left.mpr fun _ hx hx' => h (hx.symm.trans hx')

/-- The classes cover `G`. -/
theorem heightClass_cover (k : G → ℤ) (L : ℕ) [NeZero L] :
    (⋃ i ∈ (Finset.univ : Finset (ZMod L)), heightClass k L i) = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨(k x : ZMod L), Finset.mem_univ _, mem_heightClass_self k L x⟩

/-- **`C_i + t = C_{i+1}`** — no wrap-around case, because `ZMod L` does the wrapping. -/
theorem heightClass_translate {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (i : ZMod L) :
    (fun x => x + t) '' heightClass k L i = heightClass k L (i + 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ((k (x + t) : ℤ) : ZMod L) = i + 1
    rw [hk x]
    push_cast
    rw [show ((k x : ℤ) : ZMod L) = i from hx]
  · intro hy
    have hxt : y - t + t = y := by abel
    refine ⟨y - t, ?_, hxt⟩
    have h := hk (y - t)
    rw [hxt] at h
    have hy' : ((k y : ℤ) : ZMod L) = i + 1 := hy
    rw [h] at hy'
    push_cast at hy'
    exact add_right_cancel hy'

/-- **Each of the `L` height classes carries exactly `1/L`** for any finitely additive probability
capped by `1/L` on each of them.

This is equation (7) of the source, and the cap is where the upper density enters: domination gives
`q(C_i) ≤ d̄(C_i) = 1/L`, and the total forces equality.  The forcing itself is
`eq_of_le_of_biUnion_univ`, which knows nothing about heights. -/
theorem q_heightClass_eq (q : FinAddProb G) (k : G → ℤ) (L : ℕ) [NeZero L]
    (hle : ∀ i : ZMod L, q.toFun (heightClass k L i) ≤ (L : ℝ)⁻¹) (i : ZMod L) :
    q.toFun (heightClass k L i) = (L : ℝ)⁻¹ := by
  have hcard : (Finset.univ : Finset (ZMod L)).card = L := by
    rw [Finset.card_univ, ZMod.card]
  have hne : (Finset.univ : Finset (ZMod L)).Nonempty := ⟨(0 : ZMod L), Finset.mem_univ _⟩
  have hle' : ∀ j ∈ (Finset.univ : Finset (ZMod L)),
      q.toFun (heightClass k L j) ≤ (((Finset.univ : Finset (ZMod L)).card : ℝ))⁻¹ := by
    intro j _
    rw [hcard]
    exact hle j
  have h := eq_of_le_of_biUnion_univ q (heightClass k L)
    (fun _ _ hab => heightClass_disjoint k L hab) Finset.univ
    (heightClass_cover k L) hne hle' i (Finset.mem_univ i)
  rwa [hcard] at h


/-! ### The one choice-dependent step, isolated

Everything above takes the height `k` as given.  A height exists exactly when `t` has infinite
order, and producing one is where the source's transversal lives: choose a representative of each
`t`-orbit, and let `k x` be `x`'s displacement from its own orbit's representative.

Isolating it here is the point.  `Quotient.out` supplies the transversal in one step, and the
infinite-order hypothesis is used for exactly one thing — that `m • t` determines `m`, so the
displacement is well defined.  Nothing downstream mentions choice again. -/

/-- The `t`-orbit equivalence: `y` sits on `x`'s orbit. -/
def orbitSetoid (t : G) : Setoid G where
  r x y := ∃ m : ℤ, y = x + m • t
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := fun {x y} h => by
        obtain ⟨m, hm⟩ := h
        exact ⟨-m, by rw [hm, neg_zsmul]; abel⟩
      trans := fun {x y z} h h' => by
        obtain ⟨m, hm⟩ := h
        obtain ⟨n, hn⟩ := h'
        exact ⟨m + n, by rw [hn, hm, add_zsmul]; abel⟩ }

/-- **A height exists whenever `t` has infinite order.**

`hinf` states infinite order in the form the proof actually consumes: only `m • t = 0 → m = 0` is
used, and only to know that the orbit displacement is unique. -/
theorem exists_isHeight (t : G) (hinf : ∀ m : ℤ, m • t = 0 → m = 0) :
    ∃ k : G → ℤ, IsHeight t k := by
  classical
  have hcancel : ∀ m n : ℤ, m • t = n • t → m = n := by
    intro m n h
    -- `sub_zsmul` produces `m • t + -(n • t)`, not `m • t - n • t`, so `sub_self` finds nothing.
    have hz : (m - n) • t = 0 := by rw [sub_zsmul, h]; abel
    have := hinf _ hz
    omega
  refine ⟨fun x => Classical.choose (Quotient.mk_out (s := orbitSetoid t) x), fun x => ?_⟩
  have hspec : ∀ y : G, y = (Quotient.mk (orbitSetoid t) y).out
      + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) y)) • t :=
    fun y => Classical.choose_spec (Quotient.mk_out (s := orbitSetoid t) y)
  have hrel : (orbitSetoid t).r (x + t) x := ⟨-1, by rw [neg_one_zsmul]; abel⟩
  have hq : Quotient.mk (orbitSetoid t) (x + t) = Quotient.mk (orbitSetoid t) x :=
    Quotient.sound hrel
  -- `rw [hq] at h1` is NOT available: `h1` mentions `Classical.choose (Quotient.mk_out (x+t))`,
  -- whose TYPE contains the class being rewritten, so the motive is ill-typed.  Rewriting the
  -- plain equation `.out = .out` in a GOAL touches no dependent position.
  have hout : (Quotient.mk (orbitSetoid t) (x + t)).out
      = (Quotient.mk (orbitSetoid t) x).out := congrArg Quotient.out hq
  have h1 : x + t = (Quotient.mk (orbitSetoid t) x).out
      + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [← hout]
    exact hspec (x + t)
  have h2 : (Quotient.mk (orbitSetoid t) x).out
        + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) x)) • t + t
      = (Quotient.mk (orbitSetoid t) x).out
        + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [← hspec x]
    exact h1
  rw [add_assoc] at h2
  have h3 := add_left_cancel h2
  have h4 : (Classical.choose (Quotient.mk_out (s := orbitSetoid t) x) + 1) • t
      = (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [add_zsmul, one_zsmul]
    exact h3
  exact (hcancel _ _ h4).symm


/-! ### Step 3: the swap, and translation by an arbitrary integer

`heightClass_translate` moves by one `t`.  The swap needs to move by an arbitrary `m : ℤ`, and the
class it lands in is indexed by `(m : ZMod L)` — which is the second place the `ZMod` indexing pays
for itself, since `i • t` is not even *defined* for a residue `i`, while `m • t` for an integer `m`
lands in the class `i + (m : ZMod L)` with no side condition.

The swap itself splits in two.  `q_eq_of_swap` is pure `FinAddProb`: four sets, two of which
partition one class and two the other, with the two *crossed* unions capped by `c`.  It mentions no
group, no height, no shift — and it is the entire content of the source's "consequently both
inequalities are equalities … comparing gives `q(E+it) = q(E+jt)`".  The geometric statement is then
the instantiation, whose only work is checking that the shifted sets sit where they should. -/

/-- The height advances by `m` along `m • t`. -/
theorem isHeight_zsmul {t : G} {k : G → ℤ} (hk : IsHeight t k) (x : G) (m : ℤ) :
    k (x + m • t) = k x + m := by
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro n ih
    have h : x + ((n : ℤ) + 1) • t = (x + (n : ℤ) • t) + t := by
      rw [add_zsmul, one_zsmul]; abel
    rw [h, hk, ih]
    ring
  · intro n ih
    have h : x + (-(n : ℤ) - 1) • t + t = x + (-(n : ℤ)) • t := by
      rw [sub_zsmul, one_zsmul]; abel
    have h2 := hk (x + (-(n : ℤ) - 1) • t)
    rw [h, ih] at h2
    omega

/-- **Translation by `m • t` sends `C_i` to `C_{i+m}`.** -/
theorem heightClass_shift {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (i : ZMod L) (m : ℤ) :
    (fun x => x + m • t) '' heightClass k L i = heightClass k L (i + (m : ZMod L)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ((k (x + m • t) : ℤ) : ZMod L) = i + (m : ZMod L)
    rw [isHeight_zsmul hk]
    push_cast
    rw [show ((k x : ℤ) : ZMod L) = i from hx]
  · intro hy
    refine ⟨y + (-m) • t, ?_, ?_⟩
    · show ((k (y + (-m) • t) : ℤ) : ZMod L) = i
      rw [isHeight_zsmul hk]
      push_cast
      rw [show ((k y : ℤ) : ZMod L) = i + (m : ZMod L) from hy]
      ring
    -- the goal is a beta-redex `(fun x => x + m • t) (y + -m • t) = y`, in which `rw` cannot see
    -- the `+` structure at all; `show` exposes it first.
    · show y + (-m) • t + m • t = y
      have hz : (-m) • t + m • t = 0 := by rw [← add_zsmul]; simp
      rw [add_assoc, hz, add_zero]

/-- **The swap, with the group stripped out.**

`X, W` partition one class and `Z, Y` the other; the two crossed unions `X ∪ Y` and `W ∪ Z` are the
selectors, each capped by `c`.  Their union is the two classes, whose total is `2c`, so both caps
are attained — and then `X ∪ Y` and `Z ∪ Y` both totalling `c` forces `q X = q Z`. -/
theorem q_eq_of_swap (q : FinAddProb G) {X Y Z W : Set G} {c : ℝ}
    (hXW : Disjoint X W) (hZY : Disjoint Z Y)
    (hcross : Disjoint (X ∪ W) (Z ∪ Y))
    (hCm : q.toFun (X ∪ W) = c) (hCn : q.toFun (Z ∪ Y) = c)
    (hS : q.toFun (X ∪ Y) ≤ c) (hS' : q.toFun (W ∪ Z) ≤ c) :
    q.toFun X = q.toFun Z := by
  have hXZ : Disjoint X Z :=
    Set.disjoint_of_subset Set.subset_union_left Set.subset_union_left hcross
  have hXY : Disjoint X Y :=
    Set.disjoint_of_subset Set.subset_union_left Set.subset_union_right hcross
  have hWZ : Disjoint W Z :=
    Set.disjoint_of_subset Set.subset_union_right Set.subset_union_left hcross
  have hWY : Disjoint W Y :=
    Set.disjoint_of_subset Set.subset_union_right Set.subset_union_right hcross
  have hdisj : Disjoint (X ∪ Y) (W ∪ Z) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hXW, hXZ⟩, ⟨hWY.symm, hZY.symm⟩⟩
  have hset : (X ∪ Y) ∪ (W ∪ Z) = (X ∪ W) ∪ (Z ∪ Y) := by
    ext y
    simp only [Set.mem_union]
    tauto
  have h2c : q.toFun ((X ∪ Y) ∪ (W ∪ Z)) = 2 * c := by
    rw [hset, q.additive _ _ hcross, hCm, hCn]
    ring
  obtain ⟨hSc, -⟩ := eq_of_le_of_union q hS hS' hdisj h2c
  exact eq_of_partition_pair q hXY hSc hZY hCn

/-- **Equation (8)**: `E` and its translates.  For `E` inside the zero class, its `m`-shift and its
`n`-shift carry the same mass, given that the two crossed selectors are capped by `c` and the two
classes attain `c`. -/
theorem q_shift_eq_of_selector_le (q : FinAddProb G) {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) (E : Set G) (hE : E ⊆ heightClass k L 0) (m n : ℤ)
    (hmn : ((m : ZMod L)) ≠ ((n : ZMod L))) {c : ℝ}
    (hCm : q.toFun (heightClass k L (m : ZMod L)) = c)
    (hCn : q.toFun (heightClass k L (n : ZMod L)) = c)
    (hS : q.toFun ((fun x => x + m • t) '' E
        ∪ (fun x => x + n • t) '' (heightClass k L 0 \ E)) ≤ c)
    (hS' : q.toFun ((fun x => x + m • t) '' (heightClass k L 0 \ E)
        ∪ (fun x => x + n • t) '' E) ≤ c) :
    q.toFun ((fun x => x + m • t) '' E) = q.toFun ((fun x => x + n • t) '' E) := by
  have hdiff : Disjoint E (heightClass k L 0 \ E) :=
    Set.disjoint_left.mpr fun _ hx hx' => hx'.2 hx
  have hEC : E ∪ (heightClass k L 0 \ E) = heightClass k L 0 := by
    ext y
    constructor
    · rintro (hy | ⟨hy, -⟩)
      · exact hE hy
      · exact hy
    · intro hy
      by_cases hE' : y ∈ E
      · exact Or.inl hE'
      · exact Or.inr ⟨hy, hE'⟩
  have hm0 : (fun x : G => x + m • t) '' heightClass k L 0 = heightClass k L (m : ZMod L) := by
    have := heightClass_shift hk L 0 m
    rwa [zero_add] at this
  have hn0 : (fun x : G => x + n • t) '' heightClass k L 0 = heightClass k L (n : ZMod L) := by
    have := heightClass_shift hk L 0 n
    rwa [zero_add] at this
  have hUm : (fun x : G => x + m • t) '' E ∪ (fun x : G => x + m • t) '' (heightClass k L 0 \ E)
      = heightClass k L (m : ZMod L) := by
    rw [← Set.image_union, hEC, hm0]
  have hUn : (fun x : G => x + n • t) '' E ∪ (fun x : G => x + n • t) '' (heightClass k L 0 \ E)
      = heightClass k L (n : ZMod L) := by
    rw [← Set.image_union, hEC, hn0]
  refine q_eq_of_swap q (X := (fun x : G => x + m • t) '' E)
    (W := (fun x : G => x + m • t) '' (heightClass k L 0 \ E))
    (Z := (fun x : G => x + n • t) '' E)
    (Y := (fun x : G => x + n • t) '' (heightClass k L 0 \ E))
    (Set.disjoint_image_of_injective (add_left_injective _) hdiff)
    (Set.disjoint_image_of_injective (add_left_injective _) hdiff)
    ?_ ?_ ?_ hS hS'
  · rw [hUm, hUn]
    exact heightClass_disjoint k L hmn
  · rw [hUm]; exact hCm
  · rw [hUn]; exact hCn


/-! ### The upper-density axiom enters, and `d̄(C_i) = 1/L`

This is the source's equation (5), and the first place anything about *densities* is used rather
than about finitely additive measures.  Mathlib has no notion of a Révész–Ruzsa upper density, so
the axiom enters as a hypothesis on an abstract `d` — which is the honest encoding, and also the
useful one: the theorem below says exactly what property of `d̄` the block argument consumes.

Only **restricted additivity** is needed here.  Perturbation invariance, the other axiom, is what
the *selector* half needs, and is separate.

The source states restricted additivity for arbitrary translations `A + t_1, …, A + t_m`; the block
argument only ever uses multiples of a single `t`, so that is the form declared. -/

/-- **Restricted additivity along `t`**: disjoint translates of one set add. -/
def RestrictedAdditiveAlong (d : Set G → ℝ) (t : G) : Prop :=
  ∀ (s : Finset ℤ) (A : Set G),
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint ((fun x => x + i • t) '' A) ((fun x => x + j • t) '' A)) →
    d (⋃ i ∈ s, (fun x => x + i • t) '' A) = s.card * d A

/-- Distinct integers in `[0, L)` stay distinct in `ZMod L`. -/
theorem intCast_ne_intCast_of_mem_Ico {L : ℕ} {i j : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (L : ℤ)) (hj : j ∈ Finset.Ico (0 : ℤ) (L : ℤ)) (hij : i ≠ j) :
    ((i : ZMod L)) ≠ ((j : ZMod L)) := by
  simp only [Finset.mem_Ico] at hi hj
  intro h
  have hdvd : ((L : ℤ)) ∣ (i - j) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    ring
  have habs : |i - j| < (L : ℤ) := by
    rw [abs_lt]
    omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  exact hij (by omega)

/-- The `L` translates of `C_0` by `0, t, …, (L−1)t` cover `G`. -/
theorem heightClass_zero_translate_cover {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ)
    (hL : 0 < L) :
    (⋃ i ∈ Finset.Ico (0 : ℤ) (L : ℤ), (fun x => x + i • t) '' heightClass k L 0) = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have hr0 : 0 ≤ k x % (L : ℤ) := Int.emod_nonneg _ (ne_of_gt hLz)
  have hrL : k x % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos _ hLz
  have hdm := Int.ediv_add_emod (k x) ((L : ℤ))
  refine Set.mem_iUnion₂.mpr ⟨k x % (L : ℤ), Finset.mem_Ico.mpr ⟨hr0, hrL⟩,
    ⟨x + (-(k x % (L : ℤ))) • t, ?_, ?_⟩⟩
  · show ((k (x + (-(k x % (L : ℤ))) • t) : ℤ) : ZMod L) = 0
    rw [isHeight_zsmul hk, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨k x / (L : ℤ), by linarith⟩
  · show x + (-(k x % (L : ℤ))) • t + (k x % (L : ℤ)) • t = x
    have hz : (-(k x % (L : ℤ))) • t + (k x % (L : ℤ)) • t = 0 := by rw [← add_zsmul]; simp
    rw [add_assoc, hz, add_zero]

/-- **Equation (5): every height class has upper density exactly `1/L`.**

Restricted additivity applied to the `L` translates of `C_0`, whose union is `G`, gives
`1 = L · d̄(C_0)`; the same axiom with a single translation gives `d̄(C_i) = d̄(C_0)`. -/
theorem d_heightClass_eq {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L)
    (d : Set G → ℝ) (hadd : RestrictedAdditiveAlong d t) (hone : d Set.univ = 1) (i : ZMod L) :
    d (heightClass k L i) = (L : ℝ)⁻¹ := by
  haveI : NeZero L := ⟨by omega⟩
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hshift : ∀ m : ℤ, (fun x : G => x + m • t) '' heightClass k L 0
      = heightClass k L (m : ZMod L) := by
    intro m
    have := heightClass_shift hk L 0 m
    rwa [zero_add] at this
  -- the `L` translates are pairwise disjoint
  have hdisj : ∀ a ∈ Finset.Ico (0 : ℤ) (L : ℤ), ∀ b ∈ Finset.Ico (0 : ℤ) (L : ℤ), a ≠ b →
      Disjoint ((fun x : G => x + a • t) '' heightClass k L 0)
        ((fun x : G => x + b • t) '' heightClass k L 0) := by
    intro a ha b hb hab
    rw [hshift a, hshift b]
    exact heightClass_disjoint k L (intCast_ne_intCast_of_mem_Ico ha hb hab)
  have hcard : (Finset.Ico (0 : ℤ) (L : ℤ)).card = L := by
    rw [Int.card_Ico]
    simp
  -- `1 = L · d̄(C₀)`
  have hsum := hadd (Finset.Ico (0 : ℤ) (L : ℤ)) (heightClass k L 0) hdisj
  rw [heightClass_zero_translate_cover hk L hL, hone, hcard] at hsum
  -- `d̄(C_i) = d̄(C₀)`, by the same axiom with one translation
  have hone' : d (heightClass k L i) = d (heightClass k L 0) := by
    have h1 := hadd {(i.val : ℤ)} (heightClass k L 0) (by
      intro a ha b hb hab
      simp only [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab)
    have hval : (((i.val : ℤ)) : ZMod L) = i := by
      push_cast
      exact ZMod.natCast_rightInverse i
    -- `Set.biUnion_singleton` does NOT fire here: the index is a FINSET singleton, and the
    -- matching lemma is `Finset.set_biUnion_singleton`.
    simp only [Finset.set_biUnion_singleton, Finset.card_singleton] at h1
    rw [hshift, hval] at h1
    rw [h1]
    push_cast
    ring
  rw [hone']
  field_simp at hsum ⊢
  linarith


/-! ### The selector half: `d̄(S) = 1/L`

The source says every selector is a perturbation of `C₀` — "move its selected point in a block to
that block's zeroth point" — with displacements among `0, −t, …, −(L−1)t`.  Written out, the map is

  `φ x = x + (−(k x mod L)) • t`,

and the three obligations of `Set.BijOn` split cleanly along the definition of a selector:

* **MapsTo** uses nothing about `S` at all — `k(φ x) = L·(k x / L)` is divisible by `L` for *every*
  `x`, so `φ` lands in `C₀` unconditionally.
* **InjOn** is the *uniqueness* half of "exactly one point per block".
* **SurjOn** is the *existence* half.

So the `∃!` in `IsSelector` is not one hypothesis used twice; its two halves discharge two different
obligations, and neither is needed for the third.  `blockZero_eq` is the one computation both share:
a point `c` of `C₀` is its own block's zero point, so anything `m` steps above it, `0 ≤ m < L`, maps
back to `c`. -/

/-- The zero point of `x`'s block: step back by `k x mod L`. -/
def blockZero (t : G) (k : G → ℤ) (L : ℕ) (x : G) : G := x + (-(k x % (L : ℤ))) • t

/-- Stepping back and forward again returns `x`. -/
theorem blockZero_add (t : G) (k : G → ℤ) (L : ℕ) (x : G) :
    blockZero t k L x + (k x % (L : ℤ)) • t = x := by
  unfold blockZero
  have hz : (-(k x % (L : ℤ))) • t + (k x % (L : ℤ)) • t = 0 := by rw [← add_zsmul]; simp
  rw [add_assoc, hz, add_zero]

/-- `φ` lands in `C₀` for every `x`, selector or not. -/
theorem blockZero_mem {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L) (x : G) :
    blockZero t k L x ∈ heightClass k L 0 := by
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have hdm := Int.ediv_add_emod (k x) ((L : ℤ))
  show ((k (blockZero t k L x) : ℤ) : ZMod L) = 0
  unfold blockZero
  rw [isHeight_zsmul hk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨k x / (L : ℤ), by linarith⟩

/-- **A point of `C₀` is its own block's zero point**, so anything `m` steps above it with
`0 ≤ m < L` maps back to it.  Both `InjOn` and `SurjOn` run on this. -/
theorem blockZero_eq {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ)
    {c x : G} (hc : c ∈ heightClass k L 0) {m : ℤ}
    (hm0 : 0 ≤ m) (hmL : m < (L : ℤ)) (hx : x = c + m • t) :
    blockZero t k L x = c := by
  obtain ⟨q, hq⟩ : ((L : ℤ)) ∣ k c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hc
  have hkx : k x = (L : ℤ) * q + m := by
    rw [hx, isHeight_zsmul hk, hq]
  have hmod : k x % (L : ℤ) = m := by
    rw [hkx, add_comm ((L : ℤ) * q) m, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hm0 hmL
  unfold blockZero
  rw [hmod, hx, add_assoc]
  have hz : m • t + (-m) • t = 0 := by rw [← add_zsmul]; simp
  rw [hz, add_zero]

/-- **A selector**: exactly one point from each `L`-block. -/
def IsSelector (t : G) (k : G → ℤ) (L : ℕ) (S : Set G) : Prop :=
  ∀ c ∈ heightClass k L 0, ∃! x : G, x ∈ S ∧ ∃ m : ℤ, 0 ≤ m ∧ m < (L : ℤ) ∧ x = c + m • t

/-- **Perturbation invariance** — the Révész–Ruzsa axiom (3): a bijection with displacements in one
finite set preserves the upper density. -/
def PerturbationInvariant (d : Set G → ℝ) : Prop :=
  ∀ (A B : Set G) (T : Finset G) (f : G → G),
    Set.BijOn f A B → (∀ x ∈ A, f x - x ∈ T) → d B = d A

/-- **`φ` is a bijection from any selector onto `C₀`.** -/
theorem bijOn_blockZero {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L)
    {S : Set G} (hS : IsSelector t k L S) :
    Set.BijOn (blockZero t k L) S (heightClass k L 0) := by
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  refine ⟨fun x _ => blockZero_mem hk L hL x, ?_, ?_⟩
  · intro x hx y hy hxy
    -- `∃! x, p x` is `∃ x, p x ∧ ∀ y, p y → y = x`: THREE components, not two.  Binding two puts
    -- the conjunction in the second and loses the uniqueness clause entirely.
    obtain ⟨z, -, huniq⟩ := hS _ (blockZero_mem hk L hL x)
    have hxw : x ∈ S ∧ ∃ m : ℤ, 0 ≤ m ∧ m < (L : ℤ) ∧ x = blockZero t k L x + m • t :=
      ⟨hx, k x % (L : ℤ), Int.emod_nonneg _ (ne_of_gt hLz), Int.emod_lt_of_pos _ hLz,
        (blockZero_add t k L x).symm⟩
    have hyw : y ∈ S ∧ ∃ m : ℤ, 0 ≤ m ∧ m < (L : ℤ) ∧ y = blockZero t k L x + m • t :=
      ⟨hy, k y % (L : ℤ), Int.emod_nonneg _ (ne_of_gt hLz), Int.emod_lt_of_pos _ hLz, by
        rw [hxy]; exact (blockZero_add t k L y).symm⟩
    rw [huniq x hxw, huniq y hyw]
  · intro c hc
    obtain ⟨x, ⟨hxS, m, hm0, hmL, hxm⟩, -⟩ := hS c hc
    exact ⟨x, hxS, blockZero_eq hk L hc hm0 hmL hxm⟩

/-- **Equation (6): every selector has upper density `1/L`.** -/
theorem d_selector_eq {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L)
    (d : Set G → ℝ) (hpert : PerturbationInvariant d) (hadd : RestrictedAdditiveAlong d t)
    (hone : d Set.univ = 1) {S : Set G} (hS : IsSelector t k L S) :
    d S = (L : ℝ)⁻¹ := by
  -- `Finset.image` needs `DecidableEq G`, which a bare `AddCommGroup` does not supply.
  classical
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  -- the displacements lie in one finite set, which is the axiom's hypothesis
  have hdisp : ∀ x ∈ S, blockZero t k L x - x
      ∈ (Finset.Ico (0 : ℤ) (L : ℤ)).image (fun m : ℤ => (-m) • t) := by
    intro x _
    refine Finset.mem_image.mpr ⟨k x % (L : ℤ), Finset.mem_Ico.mpr
      ⟨Int.emod_nonneg _ (ne_of_gt hLz), Int.emod_lt_of_pos _ hLz⟩, ?_⟩
    unfold blockZero
    abel
  have h := hpert S (heightClass k L 0)
    ((Finset.Ico (0 : ℤ) (L : ℤ)).image (fun m : ℤ => (-m) • t)) (blockZero t k L)
    (bijOn_blockZero hk L hL hS) hdisp
  rw [d_heightClass_eq hk L hL d hadd hone 0] at h
  exact h.symm


/-! ### Equation (9): the telescoping, and where the boundary term comes from

`q(B+t) − q(B)` splits over the `L` classes.  Translation permutes the classes cyclically
(`C_j + t = C_{j+1}`), so after reindexing by `j ↦ j − 1` the two sums run over the same index set
and the difference is a single sum of differences.  The swap kills every term whose class is not the
boundary one, and what survives is one term.

**The boundary is real, and the `ZMod` indexing does not hide it.**  `C_{L−1} + t = C₀` holds as
sets — the classes really are permuted cyclically — but the *swap* is only available when both
shifts stay inside one block, `0 ≤ m, n < L`.  For the class whose points sit at offset `L−1`, the
shift by `t` leaves the block, and `q_shift_eq_of_selector_le` has no selector to offer.  That one
class is `j₀` below; the conclusion is stated as an exact identity for it, and the bound `1/L`
follows because both surviving terms lie in `[0, 1/L]`. -/

/-- `q B` splits over the `L` height classes. -/
theorem q_eq_sum_inter_heightClass (q : FinAddProb G) (k : G → ℤ) (L : ℕ) [NeZero L] (B : Set G) :
    q.toFun B = ∑ j : ZMod L, q.toFun (B ∩ heightClass k L j) := by
  classical
  have hd : Pairwise fun i j : ZMod L =>
      Disjoint (B ∩ heightClass k L i) (B ∩ heightClass k L j) := fun i j hij =>
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right (heightClass_disjoint k L hij)
  have hcov : (⋃ j ∈ (Finset.univ : Finset (ZMod L)), B ∩ heightClass k L j) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hx
      exact hj.1
    · intro hx
      exact Set.mem_iUnion₂.mpr
        ⟨(k x : ZMod L), Finset.mem_univ _, hx, mem_heightClass_self k L x⟩
  have h := q.sum_biUnion (fun j => B ∩ heightClass k L j) hd Finset.univ
  rwa [hcov] at h

/-- Translation permutes the classes: the part of `B + t` in `C_j` is the shift of the part of `B`
in `C_{j−1}`. -/
theorem shift_inter_heightClass {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (B : Set G)
    (j : ZMod L) :
    ((fun x => x + t) '' B) ∩ heightClass k L j
      = (fun x => x + t) '' (B ∩ heightClass k L (j - 1)) := by
  ext y
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hcls⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    show ((k b : ℤ) : ZMod L) = j - 1
    have hj : ((k (b + t) : ℤ) : ZMod L) = j := hcls
    rw [hk b] at hj
    push_cast at hj
    -- `linear_combination` is NOT in this module's import closure (it is in Problem333521's only
    -- because that file pulls half of Analysis); the explicit lemma needs no tactic at all.
    exact eq_sub_of_add_eq hj
  · rintro ⟨b, ⟨hb, hcls⟩, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    show ((k (b + t) : ℤ) : ZMod L) = j
    rw [hk b]
    push_cast
    rw [show ((k b : ℤ) : ZMod L) = j - 1 from hcls]
    ring

/-- **Equation (9), as an exact identity**: all but the boundary class cancel. -/
theorem q_shift_sub_eq_boundary (q : FinAddProb G) {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) [NeZero L] (B : Set G) (j₀ : ZMod L)
    (hinv : ∀ j : ZMod L, j ≠ j₀ →
      q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j)) = q.toFun (B ∩ heightClass k L j)) :
    q.toFun ((fun x => x + t) '' B) - q.toFun B
      = q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j₀))
        - q.toFun (B ∩ heightClass k L j₀) := by
  classical
  have h1 : q.toFun ((fun x => x + t) '' B)
      = ∑ j : ZMod L, q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j)) := by
    rw [q_eq_sum_inter_heightClass q k L ((fun x => x + t) '' B)]
    have hstep : ∀ j : ZMod L,
        q.toFun (((fun x => x + t) '' B) ∩ heightClass k L j)
          = q.toFun ((fun x => x + t) '' (B ∩ heightClass k L (j - 1))) := by
      intro j
      rw [shift_inter_heightClass hk L B j]
    rw [Finset.sum_congr rfl fun j _ => hstep j]
    exact Fintype.sum_equiv (Equiv.subRight (1 : ZMod L)) _ _ fun _ => rfl
  rw [h1, q_eq_sum_inter_heightClass q k L B, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_single j₀ (fun j _ hj => by rw [hinv j hj, sub_self])
    (fun h => absurd (Finset.mem_univ j₀) h)

/-- **The `1/L` bound.**  Both surviving terms lie in `[0, 1/L]`, so their difference is at most
`1/L` in absolute value — and `L` is arbitrary, which is what makes `q` translation invariant. -/
theorem abs_q_shift_sub_le (q : FinAddProb G) {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) [NeZero L] (B : Set G) (j₀ : ZMod L)
    (hcap : ∀ i : ZMod L, q.toFun (heightClass k L i) ≤ (L : ℝ)⁻¹)
    (hinv : ∀ j : ZMod L, j ≠ j₀ →
      q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j)) = q.toFun (B ∩ heightClass k L j)) :
    |q.toFun ((fun x => x + t) '' B) - q.toFun B| ≤ (L : ℝ)⁻¹ := by
  rw [q_shift_sub_eq_boundary q hk L B j₀ hinv]
  have h1 : q.toFun (B ∩ heightClass k L j₀) ≤ (L : ℝ)⁻¹ :=
    le_trans (q.mono Set.inter_subset_right) (hcap j₀)
  have h2 : q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j₀)) ≤ (L : ℝ)⁻¹ := by
    refine le_trans (q.mono ?_) (hcap (j₀ + 1))
    rintro y ⟨b, ⟨-, hb⟩, rfl⟩
    show ((k (b + t) : ℤ) : ZMod L) = j₀ + 1
    rw [hk b]
    push_cast
    rw [show ((k b : ℤ) : ZMod L) = j₀ from hb]
  rw [abs_le]
  exact ⟨by linarith [q.nonneg ((fun x => x + t) '' (B ∩ heightClass k L j₀))],
    by linarith [q.nonneg (B ∩ heightClass k L j₀)]⟩


/-! ### The crossed set is a selector

This is the joint the necessity direction was missing, and it is the only thing standing between the
proved pieces and equation (12).

`q_shift_eq_of_selector_le` (equation (8)) asks for two *crossed selectors* to be capped by `c`.
`d_selector_eq` (equation (6)) says every selector has upper density exactly `1/L`.  Between them
sits an unproved sentence of the source — that the crossed sets *are* selectors.  It is true and it
is not free: existence splits on whether the block's zero point lies in `E`, while uniqueness is a
height computation.  `k` is `0` mod `L` on `C₀`, so a point `c + a·t` of the shifted set forces
`a ≡ m` (or `a ≡ n`) mod `L`, and since both lie in `[0, L)` they are equal — after which the group
cancels and the two branches of the union cannot collide, because one is inside `E` and the other
is outside it. -/

/-- Two points of `C₀` shifted by amounts in `[0, L)` coincide only if both the shifts and the
points do.  This is the height computation the selector property runs on. -/
theorem eq_of_shift_eq_of_mem_zero {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ)
    {e c : G} (he : e ∈ heightClass k L 0) (hc : c ∈ heightClass k L 0) {a b : ℤ}
    (ha0 : 0 ≤ a) (haL : a < (L : ℤ)) (hb0 : 0 ≤ b) (hbL : b < (L : ℤ))
    (hab : e + a • t = c + b • t) : a = b ∧ e = c := by
  have h1 : k e + a = k c + b := by
    rw [← isHeight_zsmul hk e a, ← isHeight_zsmul hk c b, hab]
  have he0 : ((k e : ℤ) : ZMod L) = 0 := he
  have hc0 : ((k c : ℤ) : ZMod L) = 0 := hc
  have hcast : ((k e : ℤ) : ZMod L) + ((a : ℤ) : ZMod L)
      = ((k c : ℤ) : ZMod L) + ((b : ℤ) : ZMod L) := by
    have hz := congrArg (fun z : ℤ => ((z : ZMod L))) h1
    push_cast at hz
    push_cast
    exact hz
  rw [he0, hc0, zero_add, zero_add] at hcast
  have hEq : a = b := by
    by_contra hne
    exact intCast_ne_intCast_of_mem_Ico (Finset.mem_Ico.2 ⟨ha0, haL⟩)
      (Finset.mem_Ico.2 ⟨hb0, hbL⟩) hne hcast
  refine ⟨hEq, ?_⟩
  rw [hEq] at hab
  exact add_right_cancel hab

/-- **The crossed set is a selector.**  Shift `E ⊆ C₀` by `m·t` and its complement in `C₀` by `n·t`,
with `0 ≤ m, n < L`.  Every block then meets the union in exactly one point.

This is what `q_shift_eq_of_selector_le` needs in order to be applied, and what `d_selector_eq`
converts into the cap `1/L`.  Note that `m ≠ n` is **not** required here: the two branches cannot
collide because one lies in `E` and the other in its complement, which is a sharper reason than
distinctness of the shifts. -/
theorem isSelector_union_image {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ)
    (E : Set G) (hE : E ⊆ heightClass k L 0) {m n : ℤ}
    (hm0 : 0 ≤ m) (hmL : m < (L : ℤ)) (hn0 : 0 ≤ n) (hnL : n < (L : ℤ)) :
    IsSelector t k L ((fun x => x + m • t) '' E
      ∪ (fun x => x + n • t) '' (heightClass k L 0 \ E)) := by
  intro c hc
  by_cases hcE : c ∈ E
  · refine ⟨c + m • t, ⟨Or.inl ⟨c, hcE, rfl⟩, m, hm0, hmL, rfl⟩, ?_⟩
    rintro y ⟨hyS, a, ha0, haL, rfl⟩
    rcases hyS with ⟨e, heE, hey⟩ | ⟨f, hf, hfy⟩
    · obtain ⟨hma, -⟩ := eq_of_shift_eq_of_mem_zero hk L (hE heE) hc hm0 hmL ha0 haL hey
      rw [hma]
    · obtain ⟨-, hfc⟩ := eq_of_shift_eq_of_mem_zero hk L hf.1 hc hn0 hnL ha0 haL hfy
      exact absurd (by rw [hfc]; exact hcE) hf.2
  · refine ⟨c + n • t, ⟨Or.inr ⟨c, ⟨hc, hcE⟩, rfl⟩, n, hn0, hnL, rfl⟩, ?_⟩
    rintro y ⟨hyS, a, ha0, haL, rfl⟩
    rcases hyS with ⟨e, heE, hey⟩ | ⟨f, hf, hfy⟩
    · obtain ⟨-, hec⟩ := eq_of_shift_eq_of_mem_zero hk L (hE heE) hc hm0 hmL ha0 haL hey
      exact absurd (by rw [← hec]; exact heE) hcE
    · obtain ⟨hna, -⟩ := eq_of_shift_eq_of_mem_zero hk L hf.1 hc hn0 hnL ha0 haL hfy
      rw [hna]

/-! ### The invariance composition

Everything the necessity direction needs is proved; what follows is assembly, in the source's own
shape.  Fix `L`; cap each class by domination; promote the cap to equality; move each non-boundary
class one step with equation (8); let the `1/L` of `abs_q_shift_sub_le` go to zero.

Only the first step below has content, and it is the one that consumes `isSelector_union_image`:
turning "the crossed sets are selectors" into "translation preserves `q` on a class". -/

/-- Two successive shifts compose.  Stated separately because it is used four times and each use
would otherwise repeat the same `add_assoc`/`add_zsmul` rewrite. -/
theorem image_shift_shift (a b : ℤ) (t : G) (A : Set G) :
    (fun x => x + b • t) '' ((fun x => x + a • t) '' A) = (fun x => x + (a + b) • t) '' A := by
  rw [Set.image_image]
  exact congrArg (fun f => Set.image f A) (funext fun x => by rw [add_assoc, ← add_zsmul])

/-- **One class, one step.**  If `A` lies inside the class of `m`, and `m + 1` is still inside the
block, then translation by `t` preserves `q`.

This is where the proved facts meet.  `isSelector_union_image` says the two crossed sets are
selectors; `d_selector_eq` gives each of them density exactly `1/L`; domination converts that into
the cap equation (8) asks for; and `q_heightClass_eq` supplies the two class masses.  Nothing here
is new mathematics — but nothing here was available before the crossed sets were known to be
selectors, which is why this is the joint. -/
theorem q_image_add_eq_of_subset_heightClass {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) (hL : 1 < L) (q : FinAddProb G) (d : Set G → ℝ)
    (hdom : ∀ C, q.toFun C ≤ d C) (hadd : RestrictedAdditiveAlong d t)
    (hpert : PerturbationInvariant d) (hone : d Set.univ = 1)
    {m : ℤ} (hm0 : 0 ≤ m) (hm1 : m + 1 < (L : ℤ))
    {A : Set G} (hA : A ⊆ heightClass k L ((m : ℤ) : ZMod L)) :
    q.toFun ((fun x => x + t) '' A) = q.toFun A := by
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : 0 < L := by omega
  have hmL : m < (L : ℤ) := by linarith
  have hm10 : (0 : ℤ) ≤ m + 1 := by linarith
  -- domination caps every class, and the total forces the cap to be attained
  have hcap : ∀ i : ZMod L, q.toFun (heightClass k L i) ≤ (L : ℝ)⁻¹ := fun i =>
    le_of_le_of_eq (hdom _) (d_heightClass_eq hk L hLpos d hadd hone i)
  have hCeq : ∀ i : ZMod L, q.toFun (heightClass k L i) = (L : ℝ)⁻¹ :=
    fun i => q_heightClass_eq q k L hcap i
  -- pull `A` back to the zero class; the two shifts of it are `A` and `A + t`
  obtain ⟨E, hEsub, hEm, hEm1⟩ : ∃ E : Set G, E ⊆ heightClass k L 0 ∧
      (fun x => x + m • t) '' E = A ∧
      (fun x => x + (m + 1) • t) '' E = (fun x => x + t) '' A := by
    refine ⟨(fun x => x + (-m) • t) '' A, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      show ((k (a + (-m) • t) : ℤ) : ZMod L) = 0
      have hka : ((k a : ℤ) : ZMod L) = ((m : ℤ) : ZMod L) := hA ha
      rw [isHeight_zsmul hk]
      push_cast
      push_cast at hka
      rw [hka]
      ring
    · rw [image_shift_shift]
      simpa using congrArg (fun f => Set.image f A) (funext fun x : G => by simp)
    · rw [image_shift_shift]
      exact congrArg (fun f => Set.image f A) (funext fun x : G => by
        rw [show -m + (m + 1) = (1 : ℤ) by ring, one_zsmul])
  -- the two classes are distinct, since both shifts sit inside one block
  have hmn : (((m : ℤ) : ZMod L)) ≠ (((m + 1 : ℤ) : ZMod L)) := fun hcon =>
    intCast_ne_intCast_of_mem_Ico (Finset.mem_Ico.2 ⟨hm0, hmL⟩)
      (Finset.mem_Ico.2 ⟨hm10, hm1⟩) (by omega) hcon
  -- both crossed sets are selectors, hence capped
  have hcapS : ∀ F : Set G, F ⊆ heightClass k L 0 →
      q.toFun ((fun x => x + m • t) '' F
        ∪ (fun x => x + (m + 1) • t) '' (heightClass k L 0 \ F)) ≤ (L : ℝ)⁻¹ := fun F hF =>
    le_of_le_of_eq (hdom _)
      (d_selector_eq hk L hLpos d hpert hadd hone
        (isSelector_union_image hk L F hF hm0 hmL hm10 hm1))
  have hS' : q.toFun ((fun x => x + m • t) '' (heightClass k L 0 \ E)
      ∪ (fun x => x + (m + 1) • t) '' E) ≤ (L : ℝ)⁻¹ := by
    have hcompl : heightClass k L 0 \ (heightClass k L 0 \ E) = E := by
      ext y
      constructor
      · rintro ⟨hy0, hy⟩
        by_contra hyE
        exact hy ⟨hy0, hyE⟩
      · intro hyE
        exact ⟨hEsub hyE, fun hc => hc.2 hyE⟩
    have hx := hcapS (heightClass k L 0 \ E) Set.diff_subset
    rwa [hcompl] at hx
  have h8 := q_shift_eq_of_selector_le q hk L E hEsub m (m + 1) hmn
    (hCeq _) (hCeq _) (hcapS E hEsub) hS'
  rw [hEm, hEm1] at h8
  exact h8.symm

/-! ### The boundary, and the limit

The per-class step moves a class only when `m + 1` is still inside the block, so it moves every
class but the last.  That is not a defect to be repaired: `abs_q_shift_sub_le` already absorbs the
one unmoved class into an error of `1/L`, and `L` is arbitrary.  **Letting `L → ∞` is what converts
"invariant off one class" into invariance** — the boundary never disappears at any fixed `L`, it is
only ever made small.

This is also where the source's `L` finally does its job.  Up to here `L` has been an arbitrary
block size carried through every lemma; here it becomes the free parameter whose limit is the
theorem. -/

/-- Every class but the boundary one is moved by translation, so the whole difference is at most
`1/L`. -/
theorem abs_q_image_add_sub_le_inv {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) (hL : 1 < L) (q : FinAddProb G) (d : Set G → ℝ)
    (hdom : ∀ C, q.toFun C ≤ d C) (hadd : RestrictedAdditiveAlong d t)
    (hpert : PerturbationInvariant d) (hone : d Set.univ = 1) (B : Set G) :
    |q.toFun ((fun x => x + t) '' B) - q.toFun B| ≤ (L : ℝ)⁻¹ := by
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : 0 < L := by omega
  have hcap : ∀ i : ZMod L, q.toFun (heightClass k L i) ≤ (L : ℝ)⁻¹ := fun i =>
    le_of_le_of_eq (hdom _) (d_heightClass_eq hk L hLpos d hadd hone i)
  refine abs_q_shift_sub_le q hk L B ((((L - 1 : ℕ)) : ZMod L)) hcap ?_
  intro j hj
  have hval : ((j.val : ℤ) : ZMod L) = j := by
    push_cast
    exact ZMod.natCast_rightInverse j
  have hlt : j.val < L := ZMod.val_lt j
  -- `j` is not the boundary class, so its own representative has room for one more step
  have hne : j.val ≠ L - 1 := by
    intro hcon
    refine hj ?_
    have hr := ZMod.natCast_rightInverse j
    rw [hcon] at hr
    exact hr.symm
  have hm1 : ((j.val : ℤ)) + 1 < (L : ℤ) := by omega
  have hA : B ∩ heightClass k L j ⊆ heightClass k L (((j.val : ℤ)) : ZMod L) := by
    rw [hval]
    exact Set.inter_subset_right
  exact q_image_add_eq_of_subset_heightClass hk L hL q d hdom hadd hpert hone
    (by omega) hm1 hA

/-- **Every dominated finitely additive probability is translation invariant.**

`L` was an arbitrary block size in every lemma up to here; this is where it becomes the parameter
whose limit is the theorem.  The bound above holds for all `L`, and a real number smaller in
absolute value than `1/L` for every `L` is zero. -/
theorem q_image_add_eq_of_dominated {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (q : FinAddProb G) (d : Set G → ℝ)
    (hdom : ∀ C, q.toFun C ≤ d C) (hadd : RestrictedAdditiveAlong d t)
    (hpert : PerturbationInvariant d) (hone : d Set.univ = 1) (B : Set G) :
    q.toFun ((fun x => x + t) '' B) = q.toFun B := by
  by_contra hne
  set x := q.toFun ((fun x => x + t) '' B) - q.toFun B with hxdef
  have hpos : 0 < |x| := abs_pos.2 (sub_ne_zero_of_ne hne)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- `1 < (n+1)·|x|`
  have h1 : (1 : ℝ) < ((n : ℝ) + 1) * |x| := by
    have hc : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
      field_simp
    have h := mul_lt_mul_of_pos_left hn hn1
    rwa [hc] at h
  -- but `(n+2)·|x| ≤ 1`, and `n + 2 ≥ n + 1`
  have hL : 1 < n + 2 := by omega
  have hb := abs_q_image_add_sub_le_inv hk (n + 2) hL q d hdom hadd hpert hone B
  have hLR : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have h2 : ((n + 2 : ℕ) : ℝ) * |x| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hb (le_of_lt hLR)
    rwa [mul_inv_cancel₀ (ne_of_gt hLR)] at h
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at h2
  nlinarith [abs_nonneg x]

/-! ### The finite-order case: a `ZMod m` grading in place of a height

The source proves its theorem for **every** `t`, in two cases; the height construction above covers
only the infinite-order one, because `k (x + t) = k x + 1` in `ℤ` *forces* infinite order.  The
finite-order case needs the other construction, and this is its first piece.

**The right replacement for a height is a grading**: `κ : G → ZMod m` with `κ (x + t) = κ x + 1`.
It is the same orbit-transversal construction — `Quotient.out` again — but the displacement is read
modulo the order rather than as an integer, which is exactly what makes it well defined when
`m • t = 0`.

**Why this is the honest shape.**  Reading the displacement mod `m` is not a workaround; it is what
the source's `C_i = C₀ + it, 0 ≤ i < m` *is*, and it is why its finite-order case has **no boundary
error**: translation by `t` sends grade `i` to grade `i + 1` in `ZMod m` with no exception at
`i = m − 1`, because `m • t = 0` makes the wrap real rather than an approximation.  The
infinite-order argument had to pay for that wrap with an error of `1/L` and a limit. -/

/-- **A `ZMod m` grading exists whenever `m` annihilates `t` faithfully.**

`hord` says that `m` is a *period* of `t` in the form the proof consumes: only "`j • t = 0` implies
`m ∣ j`" is used, and only to know the orbit displacement is well defined modulo `m`. -/
theorem exists_grading (t : G) (m : ℕ) [NeZero m]
    (hord : ∀ j : ℤ, j • t = 0 → ((m : ℤ) ∣ j)) :
    ∃ κ : G → ZMod m, ∀ x, κ (x + t) = κ x + 1 := by
  classical
  have hcancel : ∀ a b : ℤ, a • t = b • t → ((a : ZMod m)) = ((b : ZMod m)) := by
    intro a b h
    have hz : (a - b) • t = 0 := by rw [sub_zsmul, h]; abel
    have hzero : ((a - b : ℤ) : ZMod m) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hord _ hz)
    push_cast at hzero
    exact eq_of_sub_eq_zero hzero
  refine ⟨fun x => ((Classical.choose (Quotient.mk_out (s := orbitSetoid t) x) : ℤ) : ZMod m),
    fun x => ?_⟩
  have hspec : ∀ y : G, y = (Quotient.mk (orbitSetoid t) y).out
      + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) y)) • t :=
    fun y => Classical.choose_spec (Quotient.mk_out (s := orbitSetoid t) y)
  have hq : Quotient.mk (orbitSetoid t) (x + t) = Quotient.mk (orbitSetoid t) x :=
    Quotient.sound ⟨-1, by rw [neg_one_zsmul]; abel⟩
  -- same dependent-motive dodge as `exists_isHeight`: rewrite the plain `.out = .out` in a GOAL
  have hout : (Quotient.mk (orbitSetoid t) (x + t)).out
      = (Quotient.mk (orbitSetoid t) x).out := congrArg Quotient.out hq
  have h1 : x + t = (Quotient.mk (orbitSetoid t) x).out
      + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [← hout]
    exact hspec (x + t)
  have h2 : (Quotient.mk (orbitSetoid t) x).out
        + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) x)) • t + t
      = (Quotient.mk (orbitSetoid t) x).out
        + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [← hspec x]
    exact h1
  rw [add_assoc] at h2
  have h3 := add_left_cancel h2
  have h4 : (Classical.choose (Quotient.mk_out (s := orbitSetoid t) x) + 1) • t
      = (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [add_zsmul, one_zsmul]
    exact h3
  have h5 := hcancel _ _ h4
  push_cast at h5
  exact h5.symm

/-- The grade classes: the fibres of a grading.  Deliberately the **same shape** as `heightClass`
so that the swap machinery, which only ever asks "are these two classes disjoint / does translation
move this one to that one", applies verbatim. -/
def gradeClass {m : ℕ} (κ : G → ZMod m) (i : ZMod m) : Set G := {x | κ x = i}

theorem mem_gradeClass_self {m : ℕ} (κ : G → ZMod m) (x : G) : x ∈ gradeClass κ (κ x) := rfl

theorem gradeClass_disjoint {m : ℕ} (κ : G → ZMod m) {i j : ZMod m} (h : i ≠ j) :
    Disjoint (gradeClass κ i) (gradeClass κ j) :=
  Set.disjoint_left.mpr fun x hx hx' => h (hx ▸ hx' ▸ rfl)

theorem gradeClass_cover {m : ℕ} [NeZero m] (κ : G → ZMod m) :
    (⋃ i ∈ (Finset.univ : Finset (ZMod m)), gradeClass κ i) = Set.univ := by
  ext x
  exact ⟨fun _ => Set.mem_univ _,
    fun _ => Set.mem_iUnion₂.mpr ⟨κ x, Finset.mem_univ _, mem_gradeClass_self κ x⟩⟩

/-- **Translation moves each grade to the next — with no exception.**  This is the whole point of
the finite-order case: there is no boundary class, because the wrap is an equality rather than an
approximation. -/
theorem gradeClass_translate {m : ℕ} {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (i : ZMod m) :
    (fun x => x + t) '' gradeClass κ i = gradeClass κ (i + 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show κ (x + t) = i + 1
    rw [hκ x]
    exact congrArg (· + 1) hx
  · intro hy
    refine ⟨y + (-1 : ℤ) • t, ?_, by rw [neg_one_zsmul]; abel⟩
    show κ (y + (-1 : ℤ) • t) = i
    have h := hκ (y + (-1 : ℤ) • t)
    rw [show y + (-1 : ℤ) • t + t = y by rw [neg_one_zsmul]; abel] at h
    have hyi : κ y = i + 1 := hy
    rw [hyi] at h
    exact (add_right_cancel h).symm

/-- **The grading reads an arbitrary integer shift**, the `ZMod` analogue of `isHeight_zsmul`.

The induction is the same, but the closing step is not: the height version finishes with `omega`,
which is unavailable here because `ZMod m` is a ring without a linear order.  `linear_combination`
does the same job algebraically — and that is the general shape of porting a height argument to a
grading: the *structure* transfers, the *arithmetic tactic* does not. -/
theorem isGrading_zsmul {m : ℕ} {t : G} {κ : G → ZMod m} (hκ : ∀ x, κ (x + t) = κ x + 1)
    (x : G) (j : ℤ) : κ (x + j • t) = κ x + (j : ZMod m) := by
  refine Int.induction_on j ?_ ?_ ?_
  · simp
  · intro n ih
    have h : x + ((n : ℤ) + 1) • t = (x + (n : ℤ) • t) + t := by
      rw [add_zsmul, one_zsmul]; abel
    rw [h, hκ, ih]
    push_cast
    ring
  · intro n ih
    have h : x + (-(n : ℤ) - 1) • t + t = x + (-(n : ℤ)) • t := by
      rw [sub_zsmul, one_zsmul]; abel
    have h2 := hκ (x + (-(n : ℤ) - 1) • t)
    rw [h, ih] at h2
    push_cast at h2 ⊢
    -- `linear_combination h2` leaves `2 * (…)`: the goal is MINUS h2, not plus.
    linear_combination -h2

/-- **Translation by any integer multiple moves grade `i` to grade `i + j`** — and, unlike the
height version, with no side condition on `j` at all.  `heightClass_shift` needed the shift to be
read modulo `L`; here the modulus *is* the group's own arithmetic. -/
theorem gradeClass_shift {m : ℕ} {t : G} {κ : G → ZMod m} (hκ : ∀ x, κ (x + t) = κ x + 1)
    (i : ZMod m) (j : ℤ) :
    (fun x => x + j • t) '' gradeClass κ i = gradeClass κ (i + (j : ZMod m)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show κ (x + j • t) = i + (j : ZMod m)
    rw [isGrading_zsmul hκ]
    exact congrArg (· + (j : ZMod m)) hx
  · intro hy
    -- a typed `have` sidesteps the un-beta-reduced witness goal `(fun x => x + j • t) … = y`
    have hw : y + (-j) • t + j • t = y := by
      rw [add_assoc, ← add_zsmul]; simp
    refine ⟨y + (-j) • t, ?_, hw⟩
    show κ (y + (-j) • t) = i
    rw [isGrading_zsmul hκ]
    have hyi : κ y = i + (j : ZMod m) := hy
    rw [hyi]
    push_cast
    ring

/-- The zero point of `x`'s block, in grading form: step back by `x`'s own grade. -/
def blockZeroGrade {m : ℕ} (t : G) (κ : G → ZMod m) (x : G) : G :=
  x + (-((κ x).val : ℤ)) • t

theorem blockZeroGrade_add {m : ℕ} (t : G) (κ : G → ZMod m) (x : G) :
    blockZeroGrade t κ x + ((κ x).val : ℤ) • t = x := by
  unfold blockZeroGrade
  rw [add_assoc, ← add_zsmul]
  simp

/-- Stepping back by one's own grade always lands in grade `0` — for every `x`, selector or not. -/
theorem blockZeroGrade_mem {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (x : G) :
    blockZeroGrade t κ x ∈ gradeClass κ 0 := by
  show κ (x + (-((κ x).val : ℤ)) • t) = 0
  rw [isGrading_zsmul hκ]
  push_cast
  -- `ZMod.natCast_val` and `ZMod.cast_id` are both `@[simp]`, so `((κ x).val : ZMod m) = κ x`
  simp [ZMod.natCast_val, ZMod.cast_id]

/-! ### Selectors in grading form

One new ingredient is needed here that the infinite-order case never wanted: the **converse** order
fact, `m ∣ j → j • t = 0`.  `exists_grading` only used the forward direction (`j • t = 0 → m ∣ j`,
to make the displacement well defined); the selector argument needs the other way round, because it
must *cancel* a shift once it knows the shift is a multiple of the order.  Carrying both as separate
hypotheses rather than one `↔` keeps each theorem's statement honest about which half it uses. -/

/-- A multiple of the period annihilates. -/
theorem zsmul_eq_zero_of_dvd {t : G} {m : ℕ} (hmt : ((m : ℤ)) • t = 0) {j : ℤ}
    (hdvd : ((m : ℤ)) ∣ j) : j • t = 0 := by
  obtain ⟨q, rfl⟩ := hdvd
  rw [mul_comm, mul_zsmul, hmt, zsmul_zero]

/-- **A point of grade `0` is its own block's zero point**, so anything `a` steps above it maps back
to it.  Unlike the height version this needs **no** `0 ≤ a < m` side condition: the grading reads `a`
modulo `m` already, so a shift outside the block simply wraps.  The height version had to bound `a`
precisely because `ℤ` does not wrap. -/
theorem blockZeroGrade_eq {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (hmt : ((m : ℤ)) • t = 0)
    {c x : G} (hc : c ∈ gradeClass κ 0) {a : ℤ} (hx : x = c + a • t) :
    blockZeroGrade t κ x = c := by
  have hc0 : κ c = 0 := hc
  have hkx : κ x = (a : ZMod m) := by
    rw [hx, isGrading_zsmul hκ, hc0, zero_add]
  have hdvd : ((m : ℤ)) ∣ (a - ((κ x).val : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id, hkx]
  have hz : (a - ((κ x).val : ℤ)) • t = 0 := zsmul_eq_zero_of_dvd hmt hdvd
  have hsplit : a + (-((κ x).val : ℤ)) = a - ((κ x).val : ℤ) := by ring
  have hstep : x + (-((κ x).val : ℤ)) • t = c + (a + (-((κ x).val : ℤ))) • t := by
    rw [hx, add_assoc, ← add_zsmul]
  show x + (-((κ x).val : ℤ)) • t = c
  rw [hstep, hsplit, hz, add_zero]

/-- **A selector in grading form**: exactly one point from each block, where a block is now a full
`⟨t⟩`-orbit.  The shape matches `IsSelector` so the swap machinery reads the same. -/
def IsSelectorGrade {m : ℕ} (t : G) (κ : G → ZMod m) (S : Set G) : Prop :=
  ∀ c ∈ gradeClass κ 0, ∃! x : G, x ∈ S ∧ ∃ a : ℤ, 0 ≤ a ∧ a < (m : ℤ) ∧ x = c + a • t

/-- **`blockZeroGrade` is a bijection from any selector onto grade `0`.**

Same three-way split as the height version, and for the same reason: `MapsTo` uses nothing about
`S`, `InjOn` is the uniqueness half of "exactly one point per block", `SurjOn` the existence half. -/
theorem bijOn_blockZeroGrade {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (hmt : ((m : ℤ)) • t = 0)
    {S : Set G} (hS : IsSelectorGrade t κ S) :
    Set.BijOn (blockZeroGrade t κ) S (gradeClass κ 0) := by
  refine ⟨fun x _ => blockZeroGrade_mem hκ x, ?_, ?_⟩
  · intro x hx y hy hxy
    -- THREE components, exactly as `bijOn_blockZero` above already warns: `∃! x, p x` is
    -- `∃ x, p x ∧ ∀ y, p y → y = x`.  I copied that proof's structure and reintroduced the
    -- very bug its comment documents.
    obtain ⟨z, -, huniq⟩ := hS _ (blockZeroGrade_mem hκ x)
    have hxw : x ∈ S ∧ ∃ a : ℤ, 0 ≤ a ∧ a < (m : ℤ) ∧ x = blockZeroGrade t κ x + a • t :=
      ⟨hx, ((κ x).val : ℤ), (by exact_mod_cast Nat.zero_le _),
        (by exact_mod_cast ZMod.val_lt (κ x)), (blockZeroGrade_add t κ x).symm⟩
    have hyw : y ∈ S ∧ ∃ a : ℤ, 0 ≤ a ∧ a < (m : ℤ) ∧ y = blockZeroGrade t κ x + a • t :=
      ⟨hy, ((κ y).val : ℤ), (by exact_mod_cast Nat.zero_le _),
        (by exact_mod_cast ZMod.val_lt (κ y)),
        (by rw [hxy]; exact (blockZeroGrade_add t κ y).symm)⟩
    rw [huniq x hxw, huniq y hyw]
  · intro c hc
    obtain ⟨x, ⟨hxS, a, -, -, hxa⟩, -⟩ := hS c hc
    exact ⟨x, hxS, blockZeroGrade_eq hκ hmt hc hxa⟩

/-! ### Per-grade density, and the cap forced to equality

The height versions of these are `heightClass_zero_translate_cover`, `d_heightClass_eq` and
`q_heightClass_eq`; these are their grading counterparts.  The cover is markedly shorter than its
height twin, which had to do integer division by hand (`Int.ediv_add_emod`) to find which translate
a point lies in — here `blockZeroGrade_mem` and `blockZeroGrade_add` say exactly that, and the two
were already proved. -/

/-- The `m` translates of grade `0` cover the group. -/
theorem gradeClass_zero_translate_cover {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) :
    (⋃ i ∈ Finset.Ico (0 : ℤ) (m : ℤ), (fun x => x + i • t) '' gradeClass κ 0) = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  -- typed `have`, so the witness goal never arrives as an applied lambda
  have hw : blockZeroGrade t κ x + ((κ x).val : ℤ) • t = x := blockZeroGrade_add t κ x
  have hlt : ((κ x).val : ℤ) < (m : ℤ) := by exact_mod_cast ZMod.val_lt (κ x)
  exact Set.mem_iUnion₂.mpr ⟨((κ x).val : ℤ),
    Finset.mem_Ico.mpr ⟨by exact_mod_cast Nat.zero_le _, hlt⟩,
    ⟨blockZeroGrade t κ x, blockZeroGrade_mem hκ x, hw⟩⟩

/-- **Every grade class has upper density exactly `1/m`.** -/
theorem d_gradeClass_eq {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (d : Set G → ℝ)
    (hadd : RestrictedAdditiveAlong d t) (hone : d Set.univ = 1) (i : ZMod m) :
    d (gradeClass κ i) = (m : ℝ)⁻¹ := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hshift : ∀ j : ℤ, (fun x : G => x + j • t) '' gradeClass κ 0
      = gradeClass κ (j : ZMod m) := by
    intro j
    have := gradeClass_shift hκ 0 j
    rwa [zero_add] at this
  have hdisj : ∀ a ∈ Finset.Ico (0 : ℤ) (m : ℤ), ∀ b ∈ Finset.Ico (0 : ℤ) (m : ℤ), a ≠ b →
      Disjoint ((fun x : G => x + a • t) '' gradeClass κ 0)
        ((fun x : G => x + b • t) '' gradeClass κ 0) := by
    intro a ha b hb hab
    rw [hshift a, hshift b]
    exact gradeClass_disjoint κ (intCast_ne_intCast_of_mem_Ico ha hb hab)
  have hcard : (Finset.Ico (0 : ℤ) (m : ℤ)).card = m := by
    rw [Int.card_Ico]
    simp
  have hsum := hadd (Finset.Ico (0 : ℤ) (m : ℤ)) (gradeClass κ 0) hdisj
  rw [gradeClass_zero_translate_cover hκ, hone, hcard] at hsum
  have hone' : d (gradeClass κ i) = d (gradeClass κ 0) := by
    have h1 := hadd {(i.val : ℤ)} (gradeClass κ 0) (by
      intro a ha b hb hab
      simp only [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab)
    have hval : (((i.val : ℤ)) : ZMod m) = i := by
      push_cast
      exact ZMod.natCast_rightInverse i
    simp only [Finset.set_biUnion_singleton, Finset.card_singleton] at h1
    rw [hshift, hval] at h1
    rw [h1]
    push_cast
    ring
  rw [hone']
  field_simp at hsum ⊢
  linarith

/-- **Each grade carries exactly `1/m`** for any finitely additive probability capped by `1/m` on
each of them — the grading counterpart of equation (7). -/
theorem q_gradeClass_eq {m : ℕ} [NeZero m] (q : FinAddProb G) (κ : G → ZMod m)
    (hle : ∀ i : ZMod m, q.toFun (gradeClass κ i) ≤ (m : ℝ)⁻¹) (i : ZMod m) :
    q.toFun (gradeClass κ i) = (m : ℝ)⁻¹ := by
  have hcard : (Finset.univ : Finset (ZMod m)).card = m := by
    rw [Finset.card_univ, ZMod.card]
  have hne : (Finset.univ : Finset (ZMod m)).Nonempty := ⟨(0 : ZMod m), Finset.mem_univ _⟩
  have hle' : ∀ j ∈ (Finset.univ : Finset (ZMod m)),
      q.toFun (gradeClass κ j) ≤ (((Finset.univ : Finset (ZMod m)).card : ℝ))⁻¹ := by
    intro j _
    rw [hcard]
    exact hle j
  have h := eq_of_le_of_biUnion_univ q (gradeClass κ)
    (fun _ _ hab => gradeClass_disjoint κ hab) Finset.univ
    (gradeClass_cover κ) hne hle' i (Finset.mem_univ i)
  rwa [hcard] at h

/-! ### The crossed sets are selectors, in grading form

The same three lemmas as the height case: a shift-cancellation fact, the crossed-selector property,
and the density of any selector.  The proofs mirror their twins, with `isGrading_zsmul` in place of
`isHeight_zsmul`.

**The `m ≠ n` observation carries over unchanged and is worth re-stating**, because it is what makes
the lemma usable at `n = m + 1`: the two branches of the union are kept apart not by the shifts
being distinct but by one branch lying in `E` and the other in its complement. -/

/-- Two points of grade `0` shifted by amounts in `[0, m)` coincide only if both the shifts and the
points do. -/
theorem eq_of_shift_eq_of_grade_zero {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) {e c : G}
    (he : e ∈ gradeClass κ 0) (hc : c ∈ gradeClass κ 0) {a b : ℤ}
    (ha0 : 0 ≤ a) (ham : a < (m : ℤ)) (hb0 : 0 ≤ b) (hbm : b < (m : ℤ))
    (hab : e + a • t = c + b • t) : a = b ∧ e = c := by
  have he0 : κ e = 0 := he
  have hc0 : κ c = 0 := hc
  have hcast : ((a : ℤ) : ZMod m) = ((b : ℤ) : ZMod m) := by
    have h1 : κ (e + a • t) = κ (c + b • t) := congrArg κ hab
    rw [isGrading_zsmul hκ, isGrading_zsmul hκ, he0, hc0, zero_add, zero_add] at h1
    exact h1
  have hEq : a = b := by
    by_contra hne
    exact intCast_ne_intCast_of_mem_Ico (Finset.mem_Ico.2 ⟨ha0, ham⟩)
      (Finset.mem_Ico.2 ⟨hb0, hbm⟩) hne hcast
  refine ⟨hEq, ?_⟩
  rw [hEq] at hab
  exact add_right_cancel hab

/-- **The crossed set is a selector.**  `m ≠ n` is *not* required: the two branches cannot collide
because one lies in `E` and the other in its complement — sharper than distinctness of the shifts,
and what makes the lemma usable at `n = m + 1`. -/
theorem isSelectorGrade_union_image {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (E : Set G) (hE : E ⊆ gradeClass κ 0) {a b : ℤ}
    (ha0 : 0 ≤ a) (ham : a < (m : ℤ)) (hb0 : 0 ≤ b) (hbm : b < (m : ℤ)) :
    IsSelectorGrade t κ ((fun x => x + a • t) '' E
      ∪ (fun x => x + b • t) '' (gradeClass κ 0 \ E)) := by
  intro c hc
  by_cases hcE : c ∈ E
  · refine ⟨c + a • t, ⟨Or.inl ⟨c, hcE, rfl⟩, a, ha0, ham, rfl⟩, ?_⟩
    rintro y ⟨hyS, s, hs0, hsm, rfl⟩
    rcases hyS with ⟨e, heE, hey⟩ | ⟨f, hf, hfy⟩
    · obtain ⟨has, -⟩ := eq_of_shift_eq_of_grade_zero hκ (hE heE) hc ha0 ham hs0 hsm hey
      rw [has]
    · obtain ⟨-, hfc⟩ := eq_of_shift_eq_of_grade_zero hκ hf.1 hc hb0 hbm hs0 hsm hfy
      exact absurd (by rw [hfc]; exact hcE) hf.2
  · refine ⟨c + b • t, ⟨Or.inr ⟨c, ⟨hc, hcE⟩, rfl⟩, b, hb0, hbm, rfl⟩, ?_⟩
    rintro y ⟨hyS, s, hs0, hsm, rfl⟩
    rcases hyS with ⟨e, heE, hey⟩ | ⟨f, hf, hfy⟩
    · obtain ⟨-, hec⟩ := eq_of_shift_eq_of_grade_zero hκ (hE heE) hc ha0 ham hs0 hsm hey
      exact absurd (by rw [← hec]; exact heE) hcE
    · obtain ⟨hbs, -⟩ := eq_of_shift_eq_of_grade_zero hκ hf.1 hc hb0 hbm hs0 hsm hfy
      rw [hbs]

/-- **Every selector has upper density exactly `1/m`.** -/
theorem d_selectorGrade_eq {m : ℕ} [NeZero m] {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (hmt : ((m : ℤ)) • t = 0)
    (d : Set G → ℝ) (hpert : PerturbationInvariant d) (hadd : RestrictedAdditiveAlong d t)
    (hone : d Set.univ = 1) {S : Set G} (hS : IsSelectorGrade t κ S) :
    d S = (m : ℝ)⁻¹ := by
  -- `Finset.image` needs `DecidableEq G`, which a bare `AddCommGroup` does not supply.  The height
  -- twin `d_selector_eq` says exactly this, and I mirrored the proof without its `classical`.
  classical
  have hdisp : ∀ x ∈ S, blockZeroGrade t κ x - x
      ∈ (Finset.Ico (0 : ℤ) (m : ℤ)).image (fun j : ℤ => (-j) • t) := by
    intro x _
    have hlt : ((κ x).val : ℤ) < (m : ℤ) := by exact_mod_cast ZMod.val_lt (κ x)
    have hge : (0 : ℤ) ≤ ((κ x).val : ℤ) := by positivity
    refine Finset.mem_image.mpr ⟨((κ x).val : ℤ), Finset.mem_Ico.mpr ⟨hge, hlt⟩, ?_⟩
    show (-((κ x).val : ℤ)) • t = blockZeroGrade t κ x - x
    unfold blockZeroGrade
    abel
  have h := hpert S (gradeClass κ 0)
    ((Finset.Ico (0 : ℤ) (m : ℤ)).image (fun j : ℤ => (-j) • t)) (blockZeroGrade t κ)
    (bijOn_blockZeroGrade hκ hmt hS) hdisp
  rw [d_gradeClass_eq hκ d hadd hone 0] at h
  exact h.symm

/-! ### Equation (8) and per-class invariance, in grading form

`q_eq_of_swap` is pure `FinAddProb` — no group, no height, no grading — so it is reused verbatim;
only the wrapper that feeds it the two classes changes.

**Here is where the finite-order case finally collects.**  The height version
`q_image_add_eq_of_subset_heightClass` requires `m + 1 < L`, so it moves every class *but the last*,
and the leftover is absorbed as an error of `1/L` and killed by a limit.  The grading version has no
such hypothesis: the two shifts are `i.val` and `(i+1).val`, **both automatically in `[0, m)`**, and
`(i+1).val − i.val ≡ 1` modulo `m` is exactly what makes the second shift equal to translation by
`t`.  Every class moves, including the last.  That is the whole difference between the two cases.

The one genuine side condition is `1 < m`: at `m = 1` the grading is trivial (`i = i + 1`), which is
correct rather than a defect — `m = 1` says `t = 0`, and translation by `0` is invariant for nothing
to prove.  The caller handles it. -/

/-- **Equation (8) in grading form.** -/
theorem q_shift_eq_of_selectorGrade_le {m : ℕ} [NeZero m] (q : FinAddProb G) {t : G}
    {κ : G → ZMod m} (hκ : ∀ x, κ (x + t) = κ x + 1)
    (E : Set G) (hE : E ⊆ gradeClass κ 0) (a b : ℤ)
    (hab : ((a : ℤ) : ZMod m) ≠ ((b : ℤ) : ZMod m)) {c : ℝ}
    (hCa : q.toFun (gradeClass κ ((a : ℤ) : ZMod m)) = c)
    (hCb : q.toFun (gradeClass κ ((b : ℤ) : ZMod m)) = c)
    (hS : q.toFun ((fun x => x + a • t) '' E
        ∪ (fun x => x + b • t) '' (gradeClass κ 0 \ E)) ≤ c)
    (hS' : q.toFun ((fun x => x + a • t) '' (gradeClass κ 0 \ E)
        ∪ (fun x => x + b • t) '' E) ≤ c) :
    q.toFun ((fun x => x + a • t) '' E) = q.toFun ((fun x => x + b • t) '' E) := by
  have hdiff : Disjoint E (gradeClass κ 0 \ E) :=
    Set.disjoint_left.mpr fun _ hx hx' => hx'.2 hx
  have hEC : E ∪ (gradeClass κ 0 \ E) = gradeClass κ 0 := by
    ext y
    constructor
    · rintro (hy | ⟨hy, -⟩)
      · exact hE hy
      · exact hy
    · intro hy
      by_cases hE' : y ∈ E
      · exact Or.inl hE'
      · exact Or.inr ⟨hy, hE'⟩
  have ha0 : (fun x : G => x + a • t) '' gradeClass κ 0 = gradeClass κ ((a : ℤ) : ZMod m) := by
    have := gradeClass_shift hκ 0 a
    rwa [zero_add] at this
  have hb0 : (fun x : G => x + b • t) '' gradeClass κ 0 = gradeClass κ ((b : ℤ) : ZMod m) := by
    have := gradeClass_shift hκ 0 b
    rwa [zero_add] at this
  have hUa : (fun x : G => x + a • t) '' E ∪ (fun x : G => x + a • t) '' (gradeClass κ 0 \ E)
      = gradeClass κ ((a : ℤ) : ZMod m) := by
    rw [← Set.image_union, hEC, ha0]
  have hUb : (fun x : G => x + b • t) '' E ∪ (fun x : G => x + b • t) '' (gradeClass κ 0 \ E)
      = gradeClass κ ((b : ℤ) : ZMod m) := by
    rw [← Set.image_union, hEC, hb0]
  refine q_eq_of_swap q (X := (fun x : G => x + a • t) '' E)
    (W := (fun x : G => x + a • t) '' (gradeClass κ 0 \ E))
    (Z := (fun x : G => x + b • t) '' E)
    (Y := (fun x : G => x + b • t) '' (gradeClass κ 0 \ E))
    (Set.disjoint_image_of_injective (add_left_injective _) hdiff)
    (Set.disjoint_image_of_injective (add_left_injective _) hdiff)
    ?_ ?_ ?_ hS hS'
  · rw [hUa, hUb]
    exact gradeClass_disjoint κ hab
  · rw [hUa]; exact hCa
  · rw [hUb]; exact hCb

/-- **Every class moves — including the last.**  If `A` sits inside the class of `i`, translation by
`t` preserves `q`.

**This is where the finite-order case collects.**  `q_image_add_eq_of_subset_heightClass` requires
`m + 1 < L`, so it moves every class *but the last*, and the leftover is absorbed as an error of
`1/L` and killed by a limit.  There is no such hypothesis here: the two shifts are chosen with
`(a : ZMod m) = i` and `(b : ZMod m) = i + 1`, **both automatically in `[0, m)`**, and
`(-a) + b ≡ 1` modulo `m` is exactly what makes the second shift equal translation by `t`.  Every
class moves, the last included.

The shifts arrive from an `obtain` rather than a `set`, so `a` and `b` are **opaque** and carry their
three facts with them; nothing downstream has to unfold `ZMod.val` again.

`1 < m` is the one genuine side condition, and it is not a defect: `m = 1` says `t = 0`, where
translation is the identity and there is nothing to prove.  The caller handles that case. -/
theorem q_image_add_eq_of_subset_gradeClass {m : ℕ} [NeZero m] (hm1 : 1 < m) {t : G}
    {κ : G → ZMod m} (hκ : ∀ x, κ (x + t) = κ x + 1) (hmt : ((m : ℤ)) • t = 0)
    (q : FinAddProb G) (d : Set G → ℝ)
    (hdom : ∀ C, q.toFun C ≤ d C) (hadd : RestrictedAdditiveAlong d t)
    (hpert : PerturbationInvariant d) (hone : d Set.univ = 1)
    {i : ZMod m} {A : Set G} (hA : A ⊆ gradeClass κ i) :
    q.toFun ((fun x => x + t) '' A) = q.toFun A := by
  classical
  obtain ⟨a, hacast, ha0, halt⟩ : ∃ a : ℤ, ((a : ℤ) : ZMod m) = i ∧ 0 ≤ a ∧ a < (m : ℤ) :=
    ⟨((i.val : ℕ) : ℤ), by push_cast; exact ZMod.natCast_rightInverse i, by positivity,
      by exact_mod_cast ZMod.val_lt i⟩
  obtain ⟨b, hbcast, hb0, hblt⟩ : ∃ b : ℤ, ((b : ℤ) : ZMod m) = i + 1 ∧ 0 ≤ b ∧ b < (m : ℤ) :=
    ⟨(((i + 1).val : ℕ) : ℤ), by push_cast; exact ZMod.natCast_rightInverse (i + 1),
      by positivity, by exact_mod_cast ZMod.val_lt (i + 1)⟩
  haveI : Fact (1 < m) := ⟨hm1⟩
  have hne : ((a : ℤ) : ZMod m) ≠ ((b : ℤ) : ZMod m) := by
    rw [hacast, hbcast]
    intro hcon
    have h10 : (1 : ZMod m) = 0 := by linear_combination -hcon
    have hv := ZMod.val_one m
    rw [h10] at hv
    simp at hv
  -- pull `A` back to grade `0`
  have hEsub : (fun x : G => x + (-a) • t) '' A ⊆ gradeClass κ 0 := by
    rintro _ ⟨y, hy, rfl⟩
    show κ (y + (-a) • t) = 0
    rw [isGrading_zsmul hκ]
    have hyi : κ y = i := hA hy
    rw [hyi]
    push_cast
    rw [hacast]
    ring
  have hEa : (fun x : G => x + a • t) '' ((fun x : G => x + (-a) • t) '' A) = A := by
    rw [image_shift_shift]
    have hz : ∀ y : G, y + ((-a) + a) • t = y := by
      intro y
      have hzero : (-a) + a = (0 : ℤ) := by ring
      rw [hzero, zero_zsmul, add_zero]
    calc (fun x : G => x + ((-a) + a) • t) '' A = (fun x : G => x) '' A :=
          congrArg (fun f => Set.image f A) (funext hz)
      _ = A := by simp
  have hEb : (fun x : G => x + b • t) '' ((fun x : G => x + (-a) • t) '' A)
      = (fun x : G => x + t) '' A := by
    rw [image_shift_shift]
    have hdvd : ((m : ℤ)) ∣ ((-a) + b - 1) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hacast, hbcast]
      ring
    have hz0 : ((-a) + b - 1) • t = 0 := zsmul_eq_zero_of_dvd hmt hdvd
    have hstep : ∀ y : G, y + ((-a) + b) • t = y + t := by
      intro y
      have h1 : ((-a) + b) • t = ((-a) + b - 1) • t + (1 : ℤ) • t := by
        rw [← add_zsmul]
        congr 1
        ring
      rw [h1, hz0, one_zsmul, zero_add]
    exact congrArg (fun f => Set.image f A) (funext hstep)
  -- domination caps the classes and the crossed selectors, and the caps are attained
  have hcap : ∀ j : ZMod m, q.toFun (gradeClass κ j) ≤ (m : ℝ)⁻¹ := fun j =>
    le_of_le_of_eq (hdom _) (d_gradeClass_eq hκ d hadd hone j)
  have hCeq : ∀ j : ZMod m, q.toFun (gradeClass κ j) = (m : ℝ)⁻¹ :=
    fun j => q_gradeClass_eq q κ hcap j
  have hcapS : ∀ F : Set G, F ⊆ gradeClass κ 0 →
      q.toFun ((fun x => x + a • t) '' F
        ∪ (fun x => x + b • t) '' (gradeClass κ 0 \ F)) ≤ (m : ℝ)⁻¹ := fun F hF =>
    le_of_le_of_eq (hdom _)
      (d_selectorGrade_eq hκ hmt d hpert hadd hone
        (isSelectorGrade_union_image hκ F hF ha0 halt hb0 hblt))
  have hS' : q.toFun ((fun x => x + a • t) '' (gradeClass κ 0 \ ((fun x : G => x + (-a) • t) '' A))
      ∪ (fun x => x + b • t) '' ((fun x : G => x + (-a) • t) '' A)) ≤ (m : ℝ)⁻¹ := by
    have hcompl : gradeClass κ 0 \ (gradeClass κ 0 \ ((fun x : G => x + (-a) • t) '' A))
        = (fun x : G => x + (-a) • t) '' A := by
      ext y
      constructor
      · rintro ⟨hy0, hy⟩
        by_contra hyE
        exact hy ⟨hy0, hyE⟩
      · intro hyE
        exact ⟨hEsub hyE, fun hc => hc.2 hyE⟩
    have hx := hcapS (gradeClass κ 0 \ ((fun x : G => x + (-a) • t) '' A)) Set.diff_subset
    rwa [hcompl] at hx
  have h8 := q_shift_eq_of_selectorGrade_le q hκ ((fun x : G => x + (-a) • t) '' A) hEsub a b hne
    (by rw [hacast]; exact hCeq i) (by rw [hbcast]; exact hCeq (i + 1))
    (hcapS ((fun x : G => x + (-a) • t) '' A) hEsub) hS'
  rw [hEa, hEb] at h8
  exact h8.symm

/-! ### The telescoping, with nothing left over

The height case needed three pieces here — a split over classes, a shift lemma, and
`q_shift_sub_eq_boundary` isolating the one class that could not be moved — and then an `abs` bound
of `1/L` and a limit to dispose of it.

**None of that is needed now.**  Every class moves, so the sum of the moved pieces is the sum of the
original pieces after one reindex, and the equality is *exact*.  `abs_q_shift_sub_le` has no
counterpart in this case, and that absence is the whole content of the source's remark that its
finite-order case has "no boundary error". -/

/-- `q B` splits over the `m` grade classes. -/
theorem q_eq_sum_inter_gradeClass {m : ℕ} [NeZero m] (q : FinAddProb G) (κ : G → ZMod m)
    (B : Set G) :
    q.toFun B = ∑ j : ZMod m, q.toFun (B ∩ gradeClass κ j) := by
  classical
  have hd : Pairwise fun i j : ZMod m =>
      Disjoint (B ∩ gradeClass κ i) (B ∩ gradeClass κ j) := fun i j hij =>
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right (gradeClass_disjoint κ hij)
  have hcov : (⋃ j ∈ (Finset.univ : Finset (ZMod m)), B ∩ gradeClass κ j) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hx
      exact hj.1
    · intro hx
      exact Set.mem_iUnion₂.mpr ⟨κ x, Finset.mem_univ _, hx, mem_gradeClass_self κ x⟩
  have h := q.sum_biUnion (fun j => B ∩ gradeClass κ j) hd Finset.univ
  rwa [hcov] at h

/-- Translation permutes the grades: the part of `B + t` in grade `j` is the shift of the part of
`B` in grade `j − 1`.  No wrap-around case: `ZMod m`'s own arithmetic is the wrap. -/
theorem shift_inter_gradeClass {m : ℕ} {t : G} {κ : G → ZMod m}
    (hκ : ∀ x, κ (x + t) = κ x + 1) (B : Set G) (j : ZMod m) :
    ((fun x => x + t) '' B) ∩ gradeClass κ j
      = (fun x => x + t) '' (B ∩ gradeClass κ (j - 1)) := by
  ext y
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hcls⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    show κ b = j - 1
    have hj : κ (b + t) = j := hcls
    rw [hκ b] at hj
    linear_combination hj
  · rintro ⟨b, ⟨hb, hcls⟩, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    show κ (b + t) = j
    rw [hκ b]
    have hbj : κ b = j - 1 := hcls
    rw [hbj]
    ring

/-- **Every dominated finitely additive probability is translation invariant — exactly.**

Contrast the infinite-order route: there the corresponding statement is reached only by bounding the
discrepancy by `1/L` for every `L` and letting `L → ∞`.  Here the telescoping closes with no
remainder, because `q_image_add_eq_of_subset_gradeClass` moves *every* class. -/
theorem q_image_add_eq_of_dominated_grade {m : ℕ} [NeZero m] (hm1 : 1 < m) {t : G}
    {κ : G → ZMod m} (hκ : ∀ x, κ (x + t) = κ x + 1) (hmt : ((m : ℤ)) • t = 0)
    (q : FinAddProb G) (d : Set G → ℝ)
    (hdom : ∀ C, q.toFun C ≤ d C) (hadd : RestrictedAdditiveAlong d t)
    (hpert : PerturbationInvariant d) (hone : d Set.univ = 1) (B : Set G) :
    q.toFun ((fun x => x + t) '' B) = q.toFun B := by
  classical
  have h2 : ∀ j : ZMod m, q.toFun (((fun x => x + t) '' B) ∩ gradeClass κ j)
      = q.toFun (B ∩ gradeClass κ (j - 1)) := by
    intro j
    rw [shift_inter_gradeClass hκ B j]
    exact q_image_add_eq_of_subset_gradeClass hm1 hκ hmt q d hdom hadd hpert hone
      Set.inter_subset_right
  rw [q_eq_sum_inter_gradeClass q κ ((fun x => x + t) '' B),
    Finset.sum_congr rfl (fun j _ => h2 j), q_eq_sum_inter_gradeClass q κ B]
  exact Fintype.sum_equiv (Equiv.subRight (1 : ZMod m)) _ _ fun _ => rfl

/-! ### The period, when `t` does not have infinite order

The two cases are now both proved, but they take different data: the infinite-order route wants
`∀ j, j • t = 0 → j = 0`, the finite-order route wants a modulus `m` with `m • t = 0` *and* the
converse divisibility.  This produces the second from the negation of the first, so a single case
split on that one proposition covers every `t`.

Built directly with `Nat.find` rather than through `addOrderOf`: Mathlib's order machinery is stated
for `ℕ`-smul and every hypothesis here is `ℤ`-smul, so the bridge would cost more than the search.
The minimality of `Nat.find` is exactly what gives the divisibility — a smaller positive remainder
would be a smaller period. -/
theorem exists_period {t : G} (hinf : ¬ (∀ j : ℤ, j • t = 0 → j = 0)) :
    ∃ m : ℕ, 0 < m ∧ ((m : ℤ)) • t = 0 ∧ ∀ j : ℤ, j • t = 0 → ((m : ℤ)) ∣ j := by
  classical
  push_neg at hinf
  obtain ⟨j₀, hj₀, hne⟩ := hinf
  have hex : ∃ n : ℕ, 0 < n ∧ ((n : ℤ)) • t = 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨(-j₀).toNat, by omega, ?_⟩
      have hc : (((-j₀).toNat : ℕ) : ℤ) = -j₀ := by omega
      rw [hc, neg_zsmul, hj₀, neg_zero]
    · refine ⟨j₀.toNat, by omega, ?_⟩
      have hc : ((j₀.toNat : ℕ) : ℤ) = j₀ := by omega
      rw [hc, hj₀]
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj
  have hm0 : 0 < Nat.find hex := (Nat.find_spec hex).1
  have hmz : (0 : ℤ) < ((Nat.find hex : ℕ) : ℤ) := by exact_mod_cast hm0
  -- the remainder is itself a period, so minimality forces it to vanish
  have hrt : (j % ((Nat.find hex : ℕ) : ℤ)) • t = 0 := by
    have hdm := Int.ediv_add_emod j ((Nat.find hex : ℕ) : ℤ)
    have h1 : (((Nat.find hex : ℕ) : ℤ) * (j / ((Nat.find hex : ℕ) : ℤ))) • t = 0 := by
      rw [mul_comm, mul_zsmul, (Nat.find_spec hex).2, zsmul_zero]
    have h2 : j • t = (((Nat.find hex : ℕ) : ℤ) * (j / ((Nat.find hex : ℕ) : ℤ))) • t
        + (j % ((Nat.find hex : ℕ) : ℤ)) • t := by
      rw [← add_zsmul, hdm]
    rw [h1, zero_add, hj] at h2
    exact h2.symm
  by_contra hnd
  have hrne : j % ((Nat.find hex : ℕ) : ℤ) ≠ 0 := fun h0 => hnd (Int.dvd_of_emod_eq_zero h0)
  have hr0 : 0 ≤ j % ((Nat.find hex : ℕ) : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hmz)
  have hrm : j % ((Nat.find hex : ℕ) : ℤ) < ((Nat.find hex : ℕ) : ℤ) :=
    Int.emod_lt_of_pos _ hmz
  have hlt : (j % ((Nat.find hex : ℕ) : ℤ)).toNat < Nat.find hex := by omega
  refine Nat.find_min hex hlt ⟨by omega, ?_⟩
  have hc : (((j % ((Nat.find hex : ℕ) : ℤ)).toNat : ℕ) : ℤ) = j % ((Nat.find hex : ℕ) : ℤ) := by
    omega
  rw [hc]
  exact hrt

/-! ### Both cases, joined

The source's necessity proof splits on whether `t` has infinite order, and so does this.  With both
branches proved and `exists_period` manufacturing the finite branch's data from the negation of the
infinite branch's hypothesis, the split is exhaustive and the result is **unconditional in `t`**.

Three cases, not two, because `q_image_add_eq_of_subset_gradeClass` needs `1 < m`.  The missing one
is `m = 1`, which says `t = 0` — translation by `0` is the identity map, so there is nothing to
prove.  That is a degenerate case rather than a gap: the source disposes of it in four words ("The
case `t = 0` is immediate"). -/

/-- **Every dominated finitely additive probability is translation invariant, for every `t`.** -/
theorem q_image_add_eq_of_dominated_all (q : FinAddProb G) (d : Set G → ℝ)
    (hdom : ∀ C, q.toFun C ≤ d C) (t : G)
    (hadd : RestrictedAdditiveAlong d t) (hpert : PerturbationInvariant d)
    (hone : d Set.univ = 1) (B : Set G) :
    q.toFun ((fun x => x + t) '' B) = q.toFun B := by
  by_cases hinf : ∀ j : ℤ, j • t = 0 → j = 0
  · obtain ⟨k, hk⟩ := exists_isHeight t hinf
    exact q_image_add_eq_of_dominated hk q d hdom hadd hpert hone B
  · obtain ⟨m, hm0, hmt, hord⟩ := exists_period hinf
    by_cases hm1 : 1 < m
    · haveI : NeZero m := ⟨by omega⟩
      obtain ⟨κ, hκ⟩ := exists_grading t m hord
      exact q_image_add_eq_of_dominated_grade hm1 hκ hmt q d hdom hadd hpert hone B
    · -- `m = 1` says `t = 0`, and translation by `0` moves nothing
      have hm : m = 1 := by omega
      subst hm
      have ht : t = 0 := by simpa using hmt
      subst ht
      have himg : (fun x : G => x + (0 : G)) '' B = B := by
        ext y
        simp
      rw [himg]

/-- **Equation (12), unconditional in `t`.** -/
theorem tendsto_sub_image_add_all (μ : ℕ → FinAddProb G) (d : Set G → ℝ) (t : G)
    (hadd : RestrictedAdditiveAlong d t) (hpert : PerturbationInvariant d)
    (hone : d Set.univ = 1)
    (hsub : ∀ A, Filter.limsup (fun n => (μ n).toFun A) Filter.atTop ≤ d A) (A : Set G) :
    Filter.Tendsto (fun n => (μ n).toFun A - (μ n).toFun ((fun x => x + t) '' A))
      Filter.atTop (nhds 0) := by
  refine tendsto_sub_of_forall_dominated μ d A ((fun x => x + t) '' A) ?_ ?_
  · intro q hdomq
    exact (q_image_add_eq_of_dominated_all q d hdomq t hadd hpert hone A).symm
  · intro U hU q hq C
    exact le_trans
      (le_limsup_of_tendsto_ultrafilter U hU _ _ (hq C) (fun n => (μ n).le_one C)) (hsub C)

end Height

/-! ### The `ℓ¹` side, and the join to Schur

Everything above works with `FinAddProb` — a finitely additive probability on the whole power set,
which is what an ultrafilter limit produces and what the block argument consumes.  The row's actual
hypothesis is different: the `μₙ` are honest `ℓ¹` measures.  Two facts join the halves.

The first is that an `ℓ¹` probability **induces** a `FinAddProb`; additivity is `tsum` over a
disjoint union and nothing more.  The second is the **translation bridge**: the quantity steps 1–4
drive to zero, `q A − q (A + t)`, is *literally* the indicator test applied to the difference
sequence `νₙ x = μₙ x − μₙ (x + t)` that Schur is stated about.  Once that identification is a
theorem rather than a remark, `SchurL1.tendsto_l1norm_of_weaklyNullOn_type` closes step 5 with no
further analysis — and on an arbitrary `G`, since it carries no countability hypothesis.
-/

/-- An `ℓ¹` probability measure on `G` — the row's actual hypothesis, as opposed to the finitely
additive probabilities the limit arguments produce. -/
structure L1Prob (G : Type*) where
  /-- The mass at a point. -/
  toFun : G → ℝ
  /-- Masses are nonnegative. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The masses are summable. -/
  summable : Summable toFun
  /-- The total mass is one. -/
  tsum_eq_one : ∑' x, toFun x = 1

namespace L1Prob

variable {G : Type*}

/-- The induced finitely additive probability, `A ↦ ∑' x, 1_A(x)·μ(x)`. -/
noncomputable def toFinAddProb (μ : L1Prob G) : FinAddProb G where
  toFun A := ∑' x, Set.indicator A μ.toFun x
  nonneg A := tsum_nonneg fun x => Set.indicator_nonneg (fun y _ => μ.nonneg y) x
  univ_eq := by
    simp only [Set.indicator_univ]
    exact μ.tsum_eq_one
  additive A B hAB := by
    rw [Set.indicator_union_of_disjoint hAB]
    exact (μ.summable.indicator A).tsum_add (μ.summable.indicator B)

theorem toFinAddProb_apply (μ : L1Prob G) (A : Set G) :
    μ.toFinAddProb.toFun A = ∑' x, Set.indicator A μ.toFun x := rfl

end L1Prob

section Translate

variable {G : Type*} [AddCommGroup G]

/-- The difference sequence `ν x = μ x − μ (x + t)`, the object Schur is applied to. -/
def subTranslate (μ : L1Prob G) (t : G) : G → ℝ := fun x => μ.toFun x - μ.toFun (x + t)

theorem summable_translate (μ : L1Prob G) (t : G) : Summable fun x => μ.toFun (x + t) := by
  have h := ((Equiv.addRight t).summable_iff (f := μ.toFun)).2 μ.summable
  simpa [Function.comp_def] using h

theorem summable_subTranslate (μ : L1Prob G) (t : G) : Summable (subTranslate μ t) :=
  μ.summable.sub (summable_translate μ t)

/-- Reindexing along `x ↦ x + t`: testing `μ` against the translate of `A` is testing the translate
of `μ` against `A`. -/
theorem tsum_indicator_image_add (μ : L1Prob G) (t : G) (A : Set G) :
    (∑' x, Set.indicator ((fun y => y + t) '' A) μ.toFun x)
      = ∑' x, Set.indicator A (fun y => μ.toFun (y + t)) x := by
  have hmem : ∀ x : G, (x + t ∈ (fun y => y + t) '' A) ↔ x ∈ A := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      -- `add_left_inj` takes the cancelled summand EXPLICITLY here, so `add_left_inj.1`
      -- is a projection on a function rather than on an `Iff`.
      rwa [(add_left_inj t).1 hxy] at hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hfun : (fun x => Set.indicator ((fun y => y + t) '' A) μ.toFun (x + t))
      = fun x => Set.indicator A (fun y => μ.toFun (y + t)) x := by
    funext x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem ((hmem x).2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem fun hc => hx ((hmem x).1 hc), Set.indicator_of_notMem hx]
  calc (∑' x, Set.indicator ((fun y => y + t) '' A) μ.toFun x)
      = ∑' x, Set.indicator ((fun y => y + t) '' A) μ.toFun (x + t) := by
        simpa using
          ((Equiv.addRight t).tsum_eq (Set.indicator ((fun y => y + t) '' A) μ.toFun)).symm
    _ = ∑' x, Set.indicator A (fun y => μ.toFun (y + t)) x := by rw [hfun]

/-- **The bridge.**  `q A − q (A + t)` *is* the indicator test applied to the difference sequence.
This identification is what lets step 4's output be handed to Schur unchanged — nothing is
approximated, and no functional is extended. -/
theorem toFinAddProb_sub_image_add (μ : L1Prob G) (t : G) (A : Set G) :
    μ.toFinAddProb.toFun A - μ.toFinAddProb.toFun ((fun y => y + t) '' A)
      = ∑' x, Set.indicator A (subTranslate μ t) x := by
  rw [L1Prob.toFinAddProb_apply, L1Prob.toFinAddProb_apply, tsum_indicator_image_add,
    ← (μ.summable.indicator A).tsum_sub ((summable_translate μ t).indicator A)]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      sub_zero]

/-- **Step 5, joined.**  If the induced finitely additive probabilities kill every translation
difference — which is exactly what steps 1–4 deliver — then the `ℓ¹` differences are norm null,
which is the row's equation (1).  No countability hypothesis on `G`. -/
theorem tendsto_l1norm_subTranslate (μ : ℕ → L1Prob G) (t : G)
    (h : ∀ A : Set G, Filter.Tendsto
      (fun n => (μ n).toFinAddProb.toFun A - (μ n).toFinAddProb.toFun ((fun y => y + t) '' A))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) t x|) Filter.atTop (nhds 0) :=
  SchurL1.tendsto_l1norm_of_weaklyNullOn_type
    (fun n => (summable_subTranslate (μ n) t).abs)
    fun A => by simpa only [toFinAddProb_sub_image_add] using h A

/-! ### Equation (12), and the necessity direction closed

Every ingredient exists; what follows is the composition, and it is worth saying exactly what each
hypothesis is doing because the theorem has five of them and none is decorative.

`hk` names a height for `t` — `exists_isHeight` produces one whenever `t` has infinite order, and it
is carried rather than derived so that the finite-order case fails loudly at the call site instead of
silently here.  `hadd`, `hpert`, `hone` are the Révész–Ruzsa axioms on the abstract upper density
`d`; Mathlib has no such notion, so they enter as hypotheses, which is both the honest encoding and
the informative one — together they are *exactly* what this direction consumes.  `hsub` is the link
between the sequence and the density: the `μₙ` realize `d` in the sense that their `limsup` never
exceeds it.

The domination that `q_image_add_eq_of_dominated` demanded is discharged by
`le_limsup_of_tendsto_ultrafilter` composed with `hsub`: an ultrafilter limit is at most the
`limsup`, and the `limsup` is at most `d`. -/

/-- **Equation (12).**  For a sequence of finitely additive probabilities whose `limsup` is
dominated by an upper density satisfying the Révész–Ruzsa axioms, translation differences vanish. -/
theorem tendsto_sub_image_add (μ : ℕ → FinAddProb G) (d : Set G → ℝ)
    {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (hadd : RestrictedAdditiveAlong d t) (hpert : PerturbationInvariant d)
    (hone : d Set.univ = 1)
    (hsub : ∀ A, Filter.limsup (fun n => (μ n).toFun A) Filter.atTop ≤ d A) (A : Set G) :
    Filter.Tendsto (fun n => (μ n).toFun A - (μ n).toFun ((fun x => x + t) '' A))
      Filter.atTop (nhds 0) := by
  refine tendsto_sub_of_forall_dominated μ d A ((fun x => x + t) '' A) ?_ ?_
  · intro q hdom
    exact (q_image_add_eq_of_dominated hk q d hdom hadd hpert hone A).symm
  · intro U hU q hq C
    exact le_trans
      (le_limsup_of_tendsto_ultrafilter U hU _ _ (hq C) (fun n => (μ n).le_one C)) (hsub C)

/-- **The necessity direction, end to end.**  If the `μₙ` are `ℓ¹` probabilities whose induced
finitely additive measures are dominated by a Révész–Ruzsa upper density, then the `ℓ¹` translation
differences are norm null — the row's equation (1).

This is the whole chain in one statement: the block/selector machinery makes every dominated `q`
translation invariant, ultrafilter limits supply such `q`, that gives equation (12), the bridge says
(12) *is* the indicator test on `νₙ`, and Schur — built from nothing, since Mathlib has no
`SchurProperty` — turns the indicator test into norm nullity.  No countability hypothesis on `G`
anywhere: Schur's own transport removed it. -/
theorem tendsto_l1norm_subTranslate_of_dominated (μ : ℕ → L1Prob G) (d : Set G → ℝ)
    {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (hadd : RestrictedAdditiveAlong d t) (hpert : PerturbationInvariant d)
    (hone : d Set.univ = 1)
    (hsub : ∀ A, Filter.limsup (fun n => (μ n).toFinAddProb.toFun A) Filter.atTop ≤ d A) :
    Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) t x|) Filter.atTop (nhds 0) :=
  tendsto_l1norm_subTranslate μ t
    (fun A => tendsto_sub_image_add (fun n => (μ n).toFinAddProb) d hk hadd hpert hone hsub A)

/-! ### Sufficiency: the mean is translation invariant

The converse direction defines `M̄(f) = limsup_n ∑ₓ f(x)·μₙ(x)` and checks it is a Révész–Ruzsa
upper mean.  The source disposes of most of that in one line — "monotonicity, nonnegative
homogeneity, and subadditivity are immediate" — and it is right: those are `limsup` facts about a
sum that is already linear in `f`.  **The one clause with content is translation invariance**, and
it is where assumption (1) is consumed:

`∑ₓ (f(x) − f(x+t))·μₙ(x) = ∑ₓ f(x)·(μₙ(x) − μₙ(x−t))`, bounded by `‖f‖_∞ · ‖νₙ‖₁ → 0`.

The rearrangement is a reindex along `x ↦ x + t` and nothing more, but it is the whole point: it
moves the translation off `f`, which is merely bounded, and onto `μ`, which is summable — and it is
the summable side that assumption (1) controls.  Note the *sign*: the estimate needs
`μₙ(x) − μₙ(x−t)`, which is `subTranslate μₙ (−t)`, so sufficiency consumes (1) at `−t`.  Nothing
here is new machinery; the hard analytic input was Schur, and this direction does not use it. -/

/-- Summability survives a shift of the argument. -/
theorem summable_shift {g : G → ℝ} (hg : Summable g) (s : G) : Summable fun x => g (x + s) := by
  have h := ((Equiv.addRight s).summable_iff (f := g)).2 hg
  simpa [Function.comp_def] using h

/-- A bounded function times a summable one is summable. -/
theorem summable_mul_of_bounded {g : G → ℝ} (hg : Summable fun x => |g x|)
    {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) : Summable fun x => f x * g x := by
  have habs : Summable fun x => |f x * g x| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun x => ?_) (hg.mul_left C)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
  exact habs.of_abs

/-- **The rearrangement.**  Reindexing along `x ↦ x + t` moves the translation off `f` — which is
only bounded — and onto `g`, which is summable.  That is what makes assumption (1) applicable.

Stated with **no hypotheses at all**: it is an equivalence of index sets, so neither summability nor
boundedness enters.  Carrying either would have misdescribed what the step needs. -/
theorem tsum_mul_shift_eq (f g : G → ℝ) (t : G) :
    (∑' x, f (x + t) * g x) = ∑' x, f x * g (x + -t) := by
  have h := (Equiv.addRight t).tsum_eq (fun y => f y * g (y + -t))
  simpa using h

/-- The difference of the two tested sums is the test against `subTranslate μ (−t)`. -/
theorem tsum_mul_sub_eq {g : G → ℝ} (hg : Summable fun x => |g x|)
    {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) (t : G) :
    (∑' x, f x * g x) - (∑' x, f (x + t) * g x)
      = ∑' x, f x * (g x - g (x + -t)) := by
  have hs1 : Summable fun x => f x * g x := summable_mul_of_bounded hg hf
  have hgs : Summable fun x => |g (x + -t)| := summable_shift hg (-t)
  have hs2 : Summable fun x => f x * g (x + -t) := summable_mul_of_bounded hgs hf
  rw [tsum_mul_shift_eq f g t, ← hs1.tsum_sub hs2]
  exact tsum_congr fun x => by ring

/-- **The estimate.**  `|∑ f·(μ − τμ)| ≤ ‖f‖_∞ · ‖ν‖₁`. -/
theorem abs_tsum_mul_sub_le {g : G → ℝ} (hg : Summable fun x => |g x|)
    {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) (t : G) :
    |∑' x, f x * (g x - g (x + -t))| ≤ C * ∑' x, |g x - g (x + -t)| := by
  have hgs : Summable fun x => |g (x + -t)| := summable_shift hg (-t)
  have hd : Summable fun x => |g x - g (x + -t)| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun x => ?_) (hg.add hgs)
    -- `abs_sub` under this Mathlib is NOT `|a - b| ≤ |a| + |b|`; spell the step out.
    calc |g x - g (x + -t)| = |g x + -(g (x + -t))| := by rw [sub_eq_add_neg]
      _ ≤ |g x| + |-(g (x + -t))| := abs_add_le _ _
      _ = |g x| + |g (x + -t)| := by rw [abs_neg]
  have hfd : Summable fun x => |f x * (g x - g (x + -t))| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun x => ?_) (hd.mul_left C)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
  refine le_trans (SchurL1.abs_tsum_le hfd) ?_
  rw [← hd.tsum_mul_left C]
  refine hfd.tsum_le_tsum (fun x => ?_) (hd.mul_left C)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)

/-- **Translation invariance of the mean.**  Assumption (1) — at `−t`, which is the sign the
rearrangement produces — makes the two tested sums agree in the limit.  This is the only clause of
"`M̄` is an upper mean" that is not a formal property of `limsup`. -/
theorem tendsto_tsum_mul_sub (μ : ℕ → L1Prob G) {f : G → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (t : G)
    (h1 : Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) (-t) x|) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => (∑' x, f x * (μ n).toFun x) - ∑' x, f (x + t) * (μ n).toFun x)
      Filter.atTop (nhds 0) := by
  have habs : ∀ n, Summable fun x => |(μ n).toFun x| := fun n => (μ n).summable.abs
  have hbound : ∀ n,
      |(∑' x, f x * (μ n).toFun x) - ∑' x, f (x + t) * (μ n).toFun x|
        ≤ C * ∑' x, |subTranslate (μ n) (-t) x| := by
    intro n
    rw [tsum_mul_sub_eq (habs n) hf t]
    exact abs_tsum_mul_sub_le (habs n) hf t
  have hup : Filter.Tendsto (fun n => C * ∑' x, |subTranslate (μ n) (-t) x|)
      Filter.atTop (nhds 0) := by
    simpa using h1.const_mul C
  have hlow : Filter.Tendsto (fun n => -C * ∑' x, |subTranslate (μ n) (-t) x|)
      Filter.atTop (nhds 0) := by
    simpa using h1.const_mul (-C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) (fun n => ?_)
  · have h := (abs_le.1 (hbound n)).1
    have hneg : -(C * ∑' x, |subTranslate (μ n) (-t) x|)
        = -C * ∑' x, |subTranslate (μ n) (-t) x| := by ring
    rwa [hneg] at h
  · exact (abs_le.1 (hbound n)).2

/-! ### The upper mean `M̄`

`M̄(f) = limsup_n ∑ₓ f(x)·μₙ(x)`.  Everything below is the "immediate" half of the source's
sufficiency argument — the substantive clause, translation invariance, is `tendsto_tsum_mul_sub`
above.  And it *is* immediate, but only once the sequence is known to be *bounded*, which is what `abs_tsum_mul_le` supplies: `|∑ f·μₙ| ≤ ‖f‖_∞` because `μₙ` is a
probability.  Without that, none of the `limsup` lemmas apply at all: `limsup_le_limsup` wants
coboundedness, `limsup_add_le` wants four boundedness side conditions, and `limsup` of an unbounded
sequence is junk rather than an error.  So the one line the source spends on this half rests on a
fact it does not mention.

**Nonnegative homogeneity is NOT here**, and the reason is worth recording: Mathlib has
`limsup_const_mul` for `ℝ≥0∞` and `EReal` but **not for `ℝ`**, so `M̄(c·f) = c·M̄(f)` is not a
one-liner and has to be built by hand (two `limsup_le_limsup` passes plus the `c = 0` case).  It is
the one clause of "immediate" that is not. -/

/-- **The upper mean.**  Its restriction to indicators is the upper density. -/
noncomputable def mean (μ : ℕ → L1Prob G) (f : G → ℝ) : ℝ :=
  Filter.limsup (fun n => ∑' x, f x * (μ n).toFun x) Filter.atTop

/-- **The bound that makes every `limsup` step legal**: a probability cannot amplify. -/
theorem abs_tsum_mul_le (μ : L1Prob G) {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    |∑' x, f x * μ.toFun x| ≤ C := by
  have hs : Summable fun x => |f x * μ.toFun x| :=
    (summable_mul_of_bounded μ.summable.abs hf).abs
  have hCs : Summable fun x => C * μ.toFun x := μ.summable.mul_left C
  refine le_trans (SchurL1.abs_tsum_le hs) ?_
  have h1 : (∑' x, |f x * μ.toFun x|) ≤ ∑' x, C * μ.toFun x := by
    refine hs.tsum_le_tsum (fun x => ?_) hCs
    rw [abs_mul, abs_of_nonneg (μ.nonneg x)]
    exact mul_le_mul_of_nonneg_right (hf x) (μ.nonneg x)
  rwa [μ.summable.tsum_mul_left C, μ.tsum_eq_one, mul_one] at h1

theorem isBoundedUnder_le_tsum_mul (μ : ℕ → L1Prob G) {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => ∑' x, f x * (μ n).toFun x) :=
  Filter.isBoundedUnder_of ⟨C, fun n => (abs_le.1 (abs_tsum_mul_le (μ n) hf)).2⟩

theorem isBoundedUnder_ge_tsum_mul (μ : ℕ → L1Prob G) {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => ∑' x, f x * (μ n).toFun x) :=
  Filter.isBoundedUnder_of ⟨-C, fun n => (abs_le.1 (abs_tsum_mul_le (μ n) hf)).1⟩

/-- **Norming on constants** — this is exactly where `∑ μₙ = 1` is used. -/
theorem mean_const (μ : ℕ → L1Prob G) (c : ℝ) : mean μ (fun _ => c) = c := by
  have h : ∀ n, (∑' x, c * (μ n).toFun x) = c := fun n => by
    rw [(μ n).summable.tsum_mul_left c, (μ n).tsum_eq_one, mul_one]
  show Filter.limsup (fun n => ∑' x, c * (μ n).toFun x) Filter.atTop = c
  simp only [h]
  exact Filter.limsup_const c

/-- **Monotonicity.** -/
theorem mean_mono (μ : ℕ → L1Prob G) {f g : G → ℝ} {C D : ℝ}
    (hf : ∀ x, |f x| ≤ C) (hg : ∀ x, |g x| ≤ D) (hfg : ∀ x, f x ≤ g x) :
    mean μ f ≤ mean μ g := by
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
    (isBoundedUnder_ge_tsum_mul μ hf).isCoboundedUnder_le (isBoundedUnder_le_tsum_mul μ hg)
  exact (summable_mul_of_bounded (μ n).summable.abs hf).tsum_le_tsum
    (fun x => mul_le_mul_of_nonneg_right (hfg x) ((μ n).nonneg x))
    (summable_mul_of_bounded (μ n).summable.abs hg)

/-- **Subadditivity.** -/
theorem mean_add_le (μ : ℕ → L1Prob G) {f g : G → ℝ} {C D : ℝ}
    (hf : ∀ x, |f x| ≤ C) (hg : ∀ x, |g x| ≤ D) :
    mean μ (fun x => f x + g x) ≤ mean μ f + mean μ g := by
  have hsplit : (fun n => ∑' x, (f x + g x) * (μ n).toFun x)
      = (fun n => ∑' x, f x * (μ n).toFun x) + fun n => ∑' x, g x * (μ n).toFun x := by
    funext n
    rw [Pi.add_apply, ← Summable.tsum_add (summable_mul_of_bounded (μ n).summable.abs hf)
      (summable_mul_of_bounded (μ n).summable.abs hg)]
    exact tsum_congr fun x => by ring
  show Filter.limsup (fun n => ∑' x, (f x + g x) * (μ n).toFun x) Filter.atTop ≤ _
  rw [hsplit]
  exact limsup_add_le (isBoundedUnder_ge_tsum_mul μ hf) (isBoundedUnder_le_tsum_mul μ hf)
    (isBoundedUnder_ge_tsum_mul μ hg).isCoboundedUnder_le (isBoundedUnder_le_tsum_mul μ hg)

/-! ### `M̄` is translation invariant, and the density it induces

`tendsto_tsum_mul_sub` says the two tested sequences differ by a null sequence; this turns that into
equality of their `limsup`s.  There is no Mathlib lemma "`u − v → 0` implies `limsup u = limsup v`",
so it is done by `limsup_add_le` in both directions: `B = A + (B − A)` gives `limsup B ≤ limsup A`
because `limsup (B − A) = 0`, and symmetrically.  The boundedness side conditions are what the whole
`abs_tsum_mul_le` layer exists to supply — `B − A` is bounded by `2C` simply because each of `A`
and `B` is bounded by `C`.

This lemma is the workhorse for **both** remaining axioms: restricted additivity needs the translates
of a set to carry the same mass, and perturbation invariance needs displacement by a finite set not
to matter — and both reduce to "shifting the test function does not move `M̄`". -/

/-- **Translation invariance of the mean.** -/
theorem mean_shift_eq (μ : ℕ → L1Prob G) {f : G → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) (t : G)
    (h1 : Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) (-t) x|) Filter.atTop (nhds 0)) :
    mean μ (fun x => f (x + t)) = mean μ f := by
  have hft : ∀ x, |f (x + t)| ≤ C := fun x => hf (x + t)
  -- the two sequences differ by a null sequence, in both signs
  have hAB := tendsto_tsum_mul_sub μ hf t h1
  have hBA : Filter.Tendsto
      (fun n => (∑' x, f (x + t) * (μ n).toFun x) - ∑' x, f x * (μ n).toFun x)
      Filter.atTop (nhds 0) := by
    have h := hAB.const_mul (-1)
    have heq : (fun n => (-1 : ℝ) *
        ((∑' x, f x * (μ n).toFun x) - ∑' x, f (x + t) * (μ n).toFun x))
        = fun n => (∑' x, f (x + t) * (μ n).toFun x) - ∑' x, f x * (μ n).toFun x := by
      funext n; ring
    rw [heq] at h
    simpa using h
  -- a difference of two `C`-bounded sequences is `2C`-bounded; this is all `limsup_add_le` needs
  have hbd : ∀ (g h : G → ℝ), (∀ x, |g x| ≤ C) → (∀ x, |h x| ≤ C) →
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n => (∑' x, g x * (μ n).toFun x) - ∑' x, h x * (μ n).toFun x) ∧
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n => (∑' x, g x * (μ n).toFun x) - ∑' x, h x * (μ n).toFun x) := by
    intro g h hg hh
    constructor
    · refine Filter.isBoundedUnder_of ⟨C + C, fun n => ?_⟩
      have h1' := (abs_le.1 (abs_tsum_mul_le (μ n) hg)).2
      have h2' := (abs_le.1 (abs_tsum_mul_le (μ n) hh)).1
      linarith
    · refine Filter.isBoundedUnder_of ⟨-(C + C), fun n => ?_⟩
      have h1' := (abs_le.1 (abs_tsum_mul_le (μ n) hg)).1
      have h2' := (abs_le.1 (abs_tsum_mul_le (μ n) hh)).2
      linarith
  refine le_antisymm ?_ ?_
  · -- `limsup B ≤ limsup A + limsup (B − A) = limsup A`
    have hsplit : (fun n => ∑' x, f (x + t) * (μ n).toFun x)
        = (fun n => ∑' x, f x * (μ n).toFun x)
          + fun n => (∑' x, f (x + t) * (μ n).toFun x) - ∑' x, f x * (μ n).toFun x := by
      funext n
      rw [Pi.add_apply]
      ring
    obtain ⟨hle, hge⟩ := hbd (fun x => f (x + t)) f hft hf
    show Filter.limsup (fun n => ∑' x, f (x + t) * (μ n).toFun x) Filter.atTop ≤ _
    rw [hsplit]
    refine le_trans (limsup_add_le (isBoundedUnder_ge_tsum_mul μ hf)
      (isBoundedUnder_le_tsum_mul μ hf) hge.isCoboundedUnder_le hle) ?_
    rw [hBA.limsup_eq, add_zero]
    exact le_rfl
  · -- and symmetrically
    have hsplit : (fun n => ∑' x, f x * (μ n).toFun x)
        = (fun n => ∑' x, f (x + t) * (μ n).toFun x)
          + fun n => (∑' x, f x * (μ n).toFun x) - ∑' x, f (x + t) * (μ n).toFun x := by
      funext n
      rw [Pi.add_apply]
      ring
    obtain ⟨hle, hge⟩ := hbd f (fun x => f (x + t)) hf hft
    show Filter.limsup (fun n => ∑' x, f x * (μ n).toFun x) Filter.atTop ≤ _
    rw [hsplit]
    refine le_trans (limsup_add_le (isBoundedUnder_ge_tsum_mul μ hft)
      (isBoundedUnder_le_tsum_mul μ hft) hge.isCoboundedUnder_le hle) ?_
    rw [hAB.limsup_eq, add_zero]
    exact le_rfl

/-- **The upper density the sequence induces**: `M̄` restricted to indicators.  This is the object
the necessity direction takes as its abstract `d`, so proving *this* satisfies the Révész–Ruzsa
axioms is what closes the equivalence. -/
noncomputable def density (μ : ℕ → L1Prob G) (A : Set G) : ℝ :=
  mean μ (Set.indicator A (fun _ => 1))

/-- Indicators are bounded by one — the hypothesis every `mean` lemma above wants. -/
theorem abs_indicator_one_le (A : Set G) (x : G) :
    |Set.indicator A (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- **Normalization**: the whole group has density one.  This is `∑ μₙ = 1` again, one layer up. -/
theorem density_univ (μ : ℕ → L1Prob G) : density μ Set.univ = 1 := by
  have h : Set.indicator (Set.univ : Set G) (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ) := by
    funext x
    simp
  show mean μ (Set.indicator (Set.univ : Set G) (fun _ => (1 : ℝ))) = 1
  rw [h]
  exact mean_const μ 1

/-- **Nonnegative homogeneity of the mean.**

Mathlib has `limsup_const_mul` for `ℝ≥0∞` and `EReal` but **not for `ℝ`**, so this is built here.
The route is `OrderIso.limsup_apply`: for `c > 0` multiplication by `c` is an order *isomorphism*
of `ℝ`, and `limsup` commutes with order isomorphisms.  The `c = 0` case is genuinely separate —
`x ↦ 0 * x` is not an isomorphism — and is `mean_const`.

I had recorded this clause as "wanted for the upper-mean statement but not for the two density
axioms".  **That was wrong**: restricted additivity needs `limsup (m·A) = m·limsup A`, where `m` is
the number of translates, so homogeneity is on the critical path rather than beside it. -/
theorem mean_smul (μ : ℕ → L1Prob G) {f : G → ℝ} {C c : ℝ} (hf : ∀ x, |f x| ≤ C) (hc : 0 ≤ c) :
    mean μ (fun x => c * f x) = c * mean μ f := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · -- `c = 0`: not an isomorphism, and not needed to be
    subst hc0
    simp only [zero_mul]
    exact mean_const μ 0
  · have hA : ∀ n, (∑' x, c * f x * (μ n).toFun x) = c * ∑' x, f x * (μ n).toFun x := by
      intro n
      rw [← tsum_mul_left]
      exact tsum_congr fun x => by ring
    have hbdd_le : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n => c * ∑' x, f x * (μ n).toFun x) :=
      Filter.isBoundedUnder_of ⟨c * C, fun n =>
        mul_le_mul_of_nonneg_left (abs_le.1 (abs_tsum_mul_le (μ n) hf)).2 hc⟩
    have hbdd_ge : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n => c * ∑' x, f x * (μ n).toFun x) :=
      Filter.isBoundedUnder_of ⟨c * -C, fun n =>
        mul_le_mul_of_nonneg_left (abs_le.1 (abs_tsum_mul_le (μ n) hf)).1 hc⟩
    have hiso := (OrderIso.mulLeft₀ c hcpos).limsup_apply
      (f := Filter.atTop) (u := fun n => ∑' x, f x * (μ n).toFun x)
      (isBoundedUnder_le_tsum_mul μ hf)
      (isBoundedUnder_ge_tsum_mul μ hf).isCoboundedUnder_le
      (by simpa using hbdd_le) (by simpa using hbdd_ge.isCoboundedUnder_le)
    show Filter.limsup (fun n => ∑' x, c * f x * (μ n).toFun x) Filter.atTop
        = c * Filter.limsup (fun n => ∑' x, f x * (μ n).toFun x) Filter.atTop
    simp only [hA]
    simpa using hiso.symm

/-! ### Null perturbation, extracted

`mean_shift_eq` proved "two bounded sequences differing by a null sequence have the same `limsup`"
*inline*, for the particular pair coming from a shift.  Restricted additivity needs the same fact for
a different pair — the sum over `m` translates against `m` copies of the base sequence — so it is
extracted here as a statement about sequences, with no `μ` and no group in sight.

Keeping `mean_shift_eq` as it stands rather than re-deriving it: it is green, and rewriting a proved
theorem to save a dozen lines is exactly the kind of churn the house rules warn against. -/

/-- **Bounded sequences differing by a null sequence have the same `limsup`.** -/
theorem limsup_eq_of_tendsto_sub {u v : ℕ → ℝ} {M : ℝ}
    (hu : ∀ n, |u n| ≤ M) (hv : ∀ n, |v n| ≤ M)
    (h : Filter.Tendsto (fun n => u n - v n) Filter.atTop (nhds 0)) :
    Filter.limsup u Filter.atTop = Filter.limsup v Filter.atTop := by
  have hvu : Filter.Tendsto (fun n => v n - u n) Filter.atTop (nhds 0) := by
    have h' := h.const_mul (-1)
    have heq : (fun n => (-1 : ℝ) * (u n - v n)) = fun n => v n - u n := by funext n; ring
    rw [heq] at h'
    simpa using h'
  have hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of ⟨M, fun n => (abs_le.1 (hu n)).2⟩
  have hgu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of ⟨-M, fun n => (abs_le.1 (hu n)).1⟩
  have hbv : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop v :=
    Filter.isBoundedUnder_of ⟨M, fun n => (abs_le.1 (hv n)).2⟩
  have hgv : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop v :=
    Filter.isBoundedUnder_of ⟨-M, fun n => (abs_le.1 (hv n)).1⟩
  have hbd : ∀ (a b : ℕ → ℝ), (∀ n, |a n| ≤ M) → (∀ n, |b n| ≤ M) →
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => a n - b n) ∧
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => a n - b n) := by
    intro a b ha hb
    refine ⟨Filter.isBoundedUnder_of ⟨M + M, fun n => ?_⟩,
      Filter.isBoundedUnder_of ⟨-(M + M), fun n => ?_⟩⟩
    · have h1 := (abs_le.1 (ha n)).2
      have h2 := (abs_le.1 (hb n)).1
      linarith
    · have h1 := (abs_le.1 (ha n)).1
      have h2 := (abs_le.1 (hb n)).2
      linarith
  refine le_antisymm ?_ ?_
  · have hsplit : u = v + fun n => u n - v n := by funext n; rw [Pi.add_apply]; ring
    obtain ⟨hle, hge⟩ := hbd u v hu hv
    rw [hsplit]
    refine le_trans (limsup_add_le hgv hbv hge.isCoboundedUnder_le hle) ?_
    rw [h.limsup_eq, add_zero]
  · have hsplit : v = u + fun n => v n - u n := by funext n; rw [Pi.add_apply]; ring
    obtain ⟨hle, hge⟩ := hbd v u hv hu
    rw [hsplit]
    refine le_trans (limsup_add_le hgu hbu hge.isCoboundedUnder_le hle) ?_
    rw [hvu.limsup_eq, add_zero]

/-- A finite sum of null sequences is null.  Stated over a `Finset` because the translates in
restricted additivity are indexed by one. -/
theorem tendsto_finset_sum_zero {ι : Type*} (s : Finset ι) (w : ι → ℕ → ℝ)
    (h : ∀ i ∈ s, Filter.Tendsto (w i) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∑ i ∈ s, w i n) Filter.atTop (nhds 0) := by
  simpa using tendsto_finsetSum s h

/-! ### Restricted additivity of the induced density

This is the axiom the necessity direction consumed, now proved for the density sufficiency
produces — which is what makes the two halves meet on the same object rather than on two that
merely look alike.

**`limsup` is not additive**, so the route is not the obvious one.  It goes: split the indicator of
the disjoint union pointwise into a `Finset` sum (`Finset.indicator_biUnion_apply`); interchange the
sum with the `tsum`; observe each translate's sequence differs from the base sequence by a *null*
sequence (assumption (1), through `tendsto_tsum_mul_sub`); conclude the whole sum is `m ·` the base
sequence up to a null perturbation (`tendsto_finset_sum_zero` + `limsup_eq_of_tendsto_sub`); and pull
the `m` out with `mean_smul`.  Every one of those four supports had to be built first. -/

/-- The indicator of a translate is the translate of the indicator. -/
theorem indicator_image_add (A : Set G) (u x : G) :
    Set.indicator ((fun y => y + u) '' A) (fun _ => (1 : ℝ)) x
      = Set.indicator A (fun _ => (1 : ℝ)) (x + -u) := by
  by_cases hx : x + -u ∈ A
  · -- the anonymous constructor has no expected type inside `rw`'s argument, so name it
    have hmem : x ∈ (fun y => y + u) '' A := ⟨x + -u, hx, by abel⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    rintro ⟨a, ha, rfl⟩
    exact hx (by simpa using ha)

/-- **Restricted additivity of the induced density.**  `h1` is assumption (1) in its natural global
form — the sequence is asymptotically invariant under *every* translation, which is what the source
assumes and what the translates here require, one shift per translate. -/
theorem restrictedAdditive_density (μ : ℕ → L1Prob G) (t : G)
    (h1 : ∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0)) :
    RestrictedAdditiveAlong (density μ) t := by
  classical
  intro s A hdisj
  have hfb : ∀ x, |Set.indicator A (fun _ => (1 : ℝ)) x| ≤ 1 := abs_indicator_one_le A
  have hpair : (s : Set ℤ).PairwiseDisjoint fun i => (fun x => x + i • t) '' A := by
    intro i hi j hj hij
    exact hdisj i (Finset.mem_coe.1 hi) j (Finset.mem_coe.1 hj) hij
  -- (i) the union's sequence is the finite sum of the translates' sequences
  have hsplit : ∀ n,
      (∑' x, Set.indicator (⋃ i ∈ s, (fun y => y + i • t) '' A) (fun _ => (1 : ℝ)) x
          * (μ n).toFun x)
        = ∑ i ∈ s, ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x := by
    intro n
    have hpt : ∀ x,
        Set.indicator (⋃ i ∈ s, (fun y => y + i • t) '' A) (fun _ => (1 : ℝ)) x
          * (μ n).toFun x
          = ∑ i ∈ s, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x := by
      intro x
      rw [Finset.indicator_biUnion_apply s _ hpair x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [indicator_image_add A (i • t) x]
    rw [tsum_congr hpt]
    exact Summable.tsum_finsetSum fun i _ =>
      summable_mul_of_bounded (μ n).summable.abs (fun x => hfb (x + -(i • t)))
  -- (ii) each translate's sequence differs from the base sequence by a null sequence
  have hnull : ∀ i ∈ s, Filter.Tendsto
      (fun n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
        - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x) Filter.atTop (nhds 0) := by
    intro i _
    have h := tendsto_tsum_mul_sub μ hfb (-(i • t)) (h1 (-(-(i • t))))
    have hneg : Filter.Tendsto
        (fun n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
          - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x) Filter.atTop (nhds 0) := by
      have h' := h.const_mul (-1)
      have heq : (fun n => (-1 : ℝ) *
          ((∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
            - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x))
          = fun n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
            - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
        funext n; ring
      rw [heq] at h'
      simpa using h'
    exact hneg
  -- (iii) so the sum is `card • base` up to a null perturbation
  have hsum_null : Filter.Tendsto
      (fun n => (∑ i ∈ s, ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
        - ∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
      Filter.atTop (nhds 0) := by
    have hcard : ∀ n, (∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
        = ∑ i ∈ s, ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      intro n
      rw [Finset.sum_const, nsmul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun x => by ring
    have := tendsto_finset_sum_zero s
      (fun i n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
        - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x) hnull
    have heq : (fun n => ∑ i ∈ s,
        ((∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
          - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x))
        = fun n => (∑ i ∈ s,
            ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x)
          - ∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      funext n
      rw [Finset.sum_sub_distrib, hcard n]
    rwa [heq] at this
  -- (iv) assemble
  have hb1 : ∀ n, |∑ i ∈ s, ∑' x,
      Set.indicator A (fun _ => (1 : ℝ)) (x + -(i • t)) * (μ n).toFun x| ≤ (s.card : ℝ) := by
    intro n
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ =>
      abs_tsum_mul_le (μ n) (fun x => hfb (x + -(i • t)))) ?_
    simp
  have hb2 : ∀ n, |∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x|
      ≤ (s.card : ℝ) := by
    intro n
    refine abs_tsum_mul_le (μ n) fun x => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (s.card : ℝ))]
    calc (s.card : ℝ) * |Set.indicator A (fun _ => (1 : ℝ)) x|
        ≤ (s.card : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left (hfb x) (by positivity)
      _ = (s.card : ℝ) := by ring
  show Filter.limsup (fun n => ∑' x,
      Set.indicator (⋃ i ∈ s, (fun y => y + i • t) '' A) (fun _ => (1 : ℝ)) x
        * (μ n).toFun x) Filter.atTop = _
  rw [Filter.limsup_congr (Filter.Eventually.of_forall hsplit),
    limsup_eq_of_tendsto_sub hb1 hb2 hsum_null]
  exact mean_smul μ hfb (by positivity)

/-! ### Perturbation invariance — the last axiom

A bijection `A → B` whose displacements lie in a finite set `T` cannot change the density.  The
argument slices `A` by displacement: `P u = {x ∈ A | f x − x = u}`, so `B` is the union of the
*translates* `P u + u`, and each translate has the same mean as its slice by assumption (1).

**No disjoint-union machinery is needed**, which is worth noting because restricted additivity did
need it.  The two pointwise identities below — `1_A = ∑_{u∈T} 1_{P u}` and
`1_B = ∑_{u∈T} 1_{P u + u}` — already *encode* the disjointness: each is proved by
`Finset.sum_eq_single`, whose side goal is exactly "no other `u` contributes", and that side goal is
where injectivity of `f` is spent.  Carrying `Set.PairwiseDisjoint` as well would be proving the
same fact twice in two shapes. -/

/-- The slice of `A` on which `f` displaces by exactly `u`. -/
def fibre (A : Set G) (f : G → G) (u : G) : Set G := {x | x ∈ A ∧ f x - x = u}

/-- **`A` decomposes over displacements.**  `Finset.sum_eq_single`'s side goal is the disjointness. -/
theorem indicator_eq_sum_fibre (A : Set G) (T : Finset G) (f : G → G)
    (hdisp : ∀ x ∈ A, f x - x ∈ T) (x : G) :
    Set.indicator A (fun _ => (1 : ℝ)) x
      = ∑ u ∈ T, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Finset.sum_eq_single (f x - x)]
    · rw [Set.indicator_of_mem (show x ∈ fibre A f (f x - x) from ⟨hx, rfl⟩)]
    · intro u _ hu
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨-, h⟩
      exact hu h.symm
    · intro h
      exact absurd (hdisp x hx) h
  · rw [Set.indicator_of_notMem hx]
    refine (Finset.sum_eq_zero fun u _ => ?_).symm
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨h, -⟩
    exact hx h

/-- **`B` decomposes over the translated slices.**  This is where `Set.BijOn`'s injectivity and
surjectivity are used — surjectivity to find the preimage, injectivity to make it the only one. -/
theorem indicator_eq_sum_fibre_image (A B : Set G) (T : Finset G) (f : G → G)
    (hbij : Set.BijOn f A B) (hdisp : ∀ x ∈ A, f x - x ∈ T) (y : G) :
    Set.indicator B (fun _ => (1 : ℝ)) y
      = ∑ u ∈ T, Set.indicator ((fun z => z + u) '' fibre A f u) (fun _ => (1 : ℝ)) y := by
  classical
  by_cases hy : y ∈ B
  · obtain ⟨x, hxA, hfx⟩ := hbij.surjOn hy
    have hmem : y ∈ (fun z => z + (f x - x)) '' fibre A f (f x - x) :=
      ⟨x, ⟨hxA, rfl⟩, by rw [← hfx]; abel⟩
    rw [Set.indicator_of_mem hy, Finset.sum_eq_single (f x - x)]
    · rw [Set.indicator_of_mem hmem]
    · intro u _ hu
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨z, ⟨hzA, hzu⟩, rfl⟩
      -- `f z = z + u = y = f x`, so injectivity forces `z = x` and hence `u = f x - x`
      have hfz : f z = z + u := by rw [← hzu]; abel
      have : f z = f x := by rw [hfz, hfx]
      have hzx : z = x := hbij.injOn hzA hxA this
      exact hu (by rw [← hzu, hzx])
    · intro h
      exact absurd (hdisp x hxA) h
  · rw [Set.indicator_of_notMem hy]
    refine (Finset.sum_eq_zero fun u _ => ?_).symm
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨z, ⟨hzA, hzu⟩, rfl⟩
    refine hy ?_
    have hfz : f z = z + u := by rw [← hzu]; abel
    -- `rintro ... rfl` leaves the goal as `(fun z => z + u) z ∈ B`, un-beta-reduced
    show z + u ∈ B
    rw [← hfz]
    exact hbij.mapsTo hzA

/-- **Perturbation invariance of the induced density** — the second Révész–Ruzsa axiom, and the
last piece of the sufficiency direction. -/
theorem perturbationInvariant_density (μ : ℕ → L1Prob G)
    (h1 : ∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0)) :
    PerturbationInvariant (density μ) := by
  classical
  intro A B T f hbij hdisp
  have hfb : ∀ (u : G) (x : G), |Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x| ≤ 1 :=
    fun u => abs_indicator_one_le _
  -- both sequences split over the displacement slices
  have hBsum : ∀ n, (∑' y, Set.indicator B (fun _ => (1 : ℝ)) y * (μ n).toFun y)
      = ∑ u ∈ T, ∑' y,
          Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y := by
    intro n
    have hpt : ∀ y, Set.indicator B (fun _ => (1 : ℝ)) y * (μ n).toFun y
        = ∑ u ∈ T,
            Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y := by
      intro y
      rw [indicator_eq_sum_fibre_image A B T f hbij hdisp y, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by rw [indicator_image_add (fibre A f u) u y]
    rw [tsum_congr hpt]
    exact Summable.tsum_finsetSum fun u _ =>
      summable_mul_of_bounded (μ n).summable.abs (fun y => hfb u (y + -u))
  have hAsum : ∀ n, (∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
      = ∑ u ∈ T, ∑' x, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
    intro n
    have hpt : ∀ x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x
        = ∑ u ∈ T, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      intro x
      rw [indicator_eq_sum_fibre A T f hdisp x, Finset.sum_mul]
    rw [tsum_congr hpt]
    exact Summable.tsum_finsetSum fun u _ =>
      summable_mul_of_bounded (μ n).summable.abs (hfb u)
  -- each slice's translate carries the same mass in the limit
  have hnull : ∀ u ∈ T, Filter.Tendsto
      (fun n => (∑' y, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y)
        - ∑' x, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x)
      Filter.atTop (nhds 0) := by
    intro u _
    have h := tendsto_tsum_mul_sub μ (hfb u) (-u) (h1 (- -u))
    have h' := h.const_mul (-1)
    have heq : (fun n => (-1 : ℝ) *
        ((∑' x, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x)
          - ∑' y, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y))
        = fun n => (∑' y, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y)
          - ∑' x, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      funext n; ring
    rw [heq] at h'
    simpa using h'
  have hdiff : Filter.Tendsto
      (fun n => (∑' y, Set.indicator B (fun _ => (1 : ℝ)) y * (μ n).toFun y)
        - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x) Filter.atTop (nhds 0) := by
    have h := tendsto_finset_sum_zero T
      (fun u n => (∑' y, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y)
        - ∑' x, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x) hnull
    have heq : (fun n => ∑ u ∈ T,
        ((∑' y, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) (y + -u) * (μ n).toFun y)
          - ∑' x, Set.indicator (fibre A f u) (fun _ => (1 : ℝ)) x * (μ n).toFun x))
        = fun n => (∑' y, Set.indicator B (fun _ => (1 : ℝ)) y * (μ n).toFun y)
          - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      funext n
      rw [Finset.sum_sub_distrib, ← hBsum n, ← hAsum n]
    rwa [heq] at h
  exact limsup_eq_of_tendsto_sub (fun n => abs_tsum_mul_le (μ n) (abs_indicator_one_le B))
    (fun n => abs_tsum_mul_le (μ n) (abs_indicator_one_le A)) hdiff

/-! ### The equivalence

Both directions are proved; this states them as one theorem.

**Why the torsion-freeness hypothesis is real and not an artefact.**  The backward direction routes
through the block/selector machinery, which needs a *height* for the shift — and `exists_isHeight`
produces one only when the shift has infinite order.  A torsion element genuinely breaks the
construction rather than merely inconveniencing this proof: the `L` blocks the argument slices into
are the fibres of that height, and a shift of finite order has no such slicing.  So the hypothesis
is stated rather than hidden, and `u = 0` is handled separately because it is free (translation by
`0` moves nothing, so its `ℓ¹` discrepancy is identically zero, not merely small).

The forward direction needs nothing extra. -/

/-- The finitely additive measure of `A` is the indicator sum — the bridge that makes `density` and
`toFinAddProb` the same object rather than two similar ones. -/
theorem toFinAddProb_eq_indicator_mul (μ : L1Prob G) (A : Set G) :
    μ.toFinAddProb.toFun A = ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * μ.toFun x := by
  show (∑' x, Set.indicator A μ.toFun x) = _
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- `density` *is* the `limsup` of the induced finitely additive measures. -/
theorem limsup_toFinAddProb_eq_density (μ : ℕ → L1Prob G) (A : Set G) :
    Filter.limsup (fun n => (μ n).toFinAddProb.toFun A) Filter.atTop = density μ A :=
  Filter.limsup_congr
    (Filter.Eventually.of_forall fun n => toFinAddProb_eq_indicator_mul (μ n) A)

/-- Translation by `0` moves nothing. -/
theorem subTranslate_zero (μ : L1Prob G) : subTranslate μ 0 = fun _ => (0 : ℝ) := by
  funext x
  show μ.toFun x - μ.toFun (x + 0) = 0
  rw [add_zero, sub_self]

/-- **#371629, both directions.**  For a torsion-free group, a sequence of `ℓ¹` probabilities is
asymptotically translation invariant **iff** the upper density it induces satisfies the
Révész–Ruzsa axioms. -/
theorem tendsto_subTranslate_iff_density_axioms (μ : ℕ → L1Prob G)
    (htf : ∀ t : G, t ≠ 0 → ∀ m : ℤ, m • t = 0 → m = 0) :
    (∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0))
      ↔ (density μ Set.univ = 1 ∧ PerturbationInvariant (density μ) ∧
          ∀ t : G, RestrictedAdditiveAlong (density μ) t) := by
  constructor
  · intro h1
    exact ⟨density_univ μ, perturbationInvariant_density μ h1,
      fun t => restrictedAdditive_density μ t h1⟩
  · rintro ⟨hone, hpert, hadd⟩ u
    by_cases hu : u = 0
    · subst hu
      have hzero : (fun n => ∑' x, |subTranslate (μ n) (0 : G) x|) = fun _ => (0 : ℝ) := by
        funext n
        rw [subTranslate_zero]
        simp
      rw [hzero]
      exact tendsto_const_nhds
    · obtain ⟨k, hk⟩ := exists_isHeight u (htf u hu)
      exact tendsto_l1norm_subTranslate_of_dominated μ (density μ) hk (hadd u) hpert hone
        fun A => le_of_eq (limsup_toFinAddProb_eq_density μ A)

/-! ### The equivalence, unconditional

`tendsto_subTranslate_iff_density_axioms` carried a torsion-freeness hypothesis because its backward
direction routed through the height construction, which needs the shift to have infinite order.  With
both cases proved and joined, that hypothesis is gone and the statement matches the source's.

The `u = 0` case also disappears from the capstone: it used to be handled here, because translation
by `0` has no height; it is now absorbed by `q_image_add_eq_of_dominated_all`, which is where it
belongs — the degenerate case is a fact about invariance, not about this theorem. -/

/-- **The necessity direction, end to end, for every `t`.** -/
theorem tendsto_l1norm_subTranslate_of_dominated_all (μ : ℕ → L1Prob G) (d : Set G → ℝ) (t : G)
    (hadd : RestrictedAdditiveAlong d t) (hpert : PerturbationInvariant d)
    (hone : d Set.univ = 1)
    (hsub : ∀ A, Filter.limsup (fun n => (μ n).toFinAddProb.toFun A) Filter.atTop ≤ d A) :
    Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) t x|) Filter.atTop (nhds 0) :=
  tendsto_l1norm_subTranslate μ t
    (fun A => tendsto_sub_image_add_all (fun n => (μ n).toFinAddProb) d t hadd hpert hone hsub A)

/-- **#371629, both directions, no hypothesis on `G`.**

A sequence of `ℓ¹` probability measures is asymptotically translation invariant **iff** the upper
density it induces satisfies the Révész–Ruzsa axioms.  This is the source's statement, for an
arbitrary commutative group and every `t`. -/
theorem tendsto_subTranslate_iff_density_axioms_all (μ : ℕ → L1Prob G) :
    (∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0))
      ↔ (density μ Set.univ = 1 ∧ PerturbationInvariant (density μ) ∧
          ∀ t : G, RestrictedAdditiveAlong (density μ) t) := by
  constructor
  · intro h1
    exact ⟨density_univ μ, perturbationInvariant_density μ h1,
      fun t => restrictedAdditive_density μ t h1⟩
  · rintro ⟨hone, hpert, hadd⟩ u
    exact tendsto_l1norm_subTranslate_of_dominated_all μ (density μ) u (hadd u) hpert hone
      fun A => le_of_eq (limsup_toFinAddProb_eq_density μ A)

/-! ### Restricted additivity for an arbitrary family of shifts

`RestrictedAdditiveAlong d t` quantifies over multiples `i • t` of a *single* shift.  That is what
the block argument consumes, and consuming the weaker form is what makes the necessity direction
strong — but the sufficiency direction **produces** it, and there the narrowing is a genuine
weakening relative to the source, whose property (2) is for an arbitrary finite tuple
`t₁, …, t_m`.

So the general predicate is declared here and sufficiency is proved for *it*.  The proof is the same
as `restrictedAdditive_density`'s, because assumption (1) holds at **every** shift: nothing in that
argument ever used the shifts being multiples of one `t`.  That is the tell that the narrowing was
never doing any work on this side. -/

/-- **Restricted additivity, source form**: disjoint translates of one set by an arbitrary finite
family of shifts add. -/
def RestrictedAdditive (d : Set G → ℝ) : Prop :=
  ∀ (s : Finset G) (A : Set G),
    (∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      Disjoint ((fun x => x + u) '' A) ((fun x => x + v) '' A)) →
    d (⋃ u ∈ s, (fun x => x + u) '' A) = s.card * d A

/-- **Sufficiency, for the source's form of restricted additivity.** -/
theorem restrictedAdditive_density_general (μ : ℕ → L1Prob G)
    (h1 : ∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0)) :
    RestrictedAdditive (density μ) := by
  classical
  intro s A hdisj
  have hfb : ∀ x, |Set.indicator A (fun _ => (1 : ℝ)) x| ≤ 1 := abs_indicator_one_le A
  have hpair : (s : Set G).PairwiseDisjoint fun u => (fun x => x + u) '' A := by
    intro u hu v hv huv
    exact hdisj u (Finset.mem_coe.1 hu) v (Finset.mem_coe.1 hv) huv
  -- (i) the union's sequence is the finite sum of the translates' sequences
  have hsplit : ∀ n,
      (∑' x, Set.indicator (⋃ u ∈ s, (fun y => y + u) '' A) (fun _ => (1 : ℝ)) x
          * (μ n).toFun x)
        = ∑ u ∈ s, ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x := by
    intro n
    have hpt : ∀ x,
        Set.indicator (⋃ u ∈ s, (fun y => y + u) '' A) (fun _ => (1 : ℝ)) x * (μ n).toFun x
          = ∑ u ∈ s, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x := by
      intro x
      rw [Finset.indicator_biUnion_apply s _ hpair x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by rw [indicator_image_add A u x]
    rw [tsum_congr hpt]
    exact Summable.tsum_finsetSum fun u _ =>
      summable_mul_of_bounded (μ n).summable.abs (fun x => hfb (x + -u))
  -- (ii) each translate's sequence differs from the base sequence by a null sequence
  have hnull : ∀ u ∈ s, Filter.Tendsto
      (fun n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x)
        - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x) Filter.atTop (nhds 0) := by
    intro u _
    have h := tendsto_tsum_mul_sub μ hfb (-u) (h1 (- -u))
    have h' := h.const_mul (-1)
    have heq : (fun n => (-1 : ℝ) *
        ((∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
          - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x))
        = fun n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x)
          - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      funext n; ring
    rw [heq] at h'
    simpa using h'
  -- (iii) the sum is `card • base` up to a null perturbation
  have hsum_null : Filter.Tendsto
      (fun n => (∑ u ∈ s, ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x)
        - ∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
      Filter.atTop (nhds 0) := by
    have hcard : ∀ n, (∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x)
        = ∑ u ∈ s, ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      intro n
      rw [Finset.sum_const, nsmul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun x => by ring
    have h := tendsto_finset_sum_zero s
      (fun u n => (∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x)
        - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x) hnull
    have heq : (fun n => ∑ u ∈ s,
        ((∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x)
          - ∑' x, Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x))
        = fun n => (∑ u ∈ s,
            ∑' x, Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x)
          - ∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x := by
      funext n
      rw [Finset.sum_sub_distrib, hcard n]
    rwa [heq] at h
  -- (iv) assemble
  have hb1 : ∀ n, |∑ u ∈ s, ∑' x,
      Set.indicator A (fun _ => (1 : ℝ)) (x + -u) * (μ n).toFun x| ≤ (s.card : ℝ) := by
    intro n
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun u _ =>
      abs_tsum_mul_le (μ n) (fun x => hfb (x + -u))) ?_
    simp
  have hb2 : ∀ n, |∑' x, (s.card : ℝ) * Set.indicator A (fun _ => (1 : ℝ)) x * (μ n).toFun x|
      ≤ (s.card : ℝ) := by
    intro n
    refine abs_tsum_mul_le (μ n) fun x => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (s.card : ℝ))]
    calc (s.card : ℝ) * |Set.indicator A (fun _ => (1 : ℝ)) x|
        ≤ (s.card : ℝ) * 1 := mul_le_mul_of_nonneg_left (hfb x) (by positivity)
      _ = (s.card : ℝ) := by ring
  show Filter.limsup (fun n => ∑' x,
      Set.indicator (⋃ u ∈ s, (fun y => y + u) '' A) (fun _ => (1 : ℝ)) x
        * (μ n).toFun x) Filter.atTop = _
  rw [Filter.limsup_congr (Filter.Eventually.of_forall hsplit),
    limsup_eq_of_tendsto_sub hb1 hb2 hsum_null]
  exact mean_smul μ hfb (by positivity)

/-- The empty set has density zero — **and the axiom proves it of itself**, applied with an *empty*
family of shifts: the union is empty and the count is `0`.

I had expected this to need two distinct shifts and hence a nontriviality hypothesis on `G`.  It does
not; the degenerate instance `s = ∅` is already in the axiom's scope. -/
theorem d_empty_of_restrictedAdditive {d : Set G → ℝ} (h : RestrictedAdditive d) :
    d (∅ : Set G) = 0 := by
  have hx := h ∅ ∅ (by simp)
  simpa using hx

/-- **The source's form implies the form the block argument consumes.**

Necessity is stated against `RestrictedAdditiveAlong` — multiples of a single `t` — because that is
all its blocks use, and consuming less makes that direction stronger.  Sufficiency now produces the
source's general form.  This is the bridge, so the capstone can put the strong statement on the right
of the `iff` while the machinery underneath keeps the weak one.

Two cases, and the empty one is not a technicality: with `A = ∅` every translate is empty and the
shift map need not be injective, so the count could collapse.  `d ∅ = 0` is what makes both sides
vanish regardless. -/
theorem restrictedAdditiveAlong_of_restrictedAdditive {d : Set G → ℝ}
    (h : RestrictedAdditive d) (t : G) : RestrictedAdditiveAlong d t := by
  classical
  intro s A hdisj
  by_cases hA : A = ∅
  · subst hA
    have hU : (⋃ i ∈ s, (fun x : G => x + i • t) '' (∅ : Set G)) = (∅ : Set G) := by simp
    rw [hU, d_empty_of_restrictedAdditive h]
    ring
  · obtain ⟨a, ha⟩ : ∃ a, a ∈ A := Set.nonempty_iff_ne_empty.2 hA
    -- disjointness forces the shift map to be injective on `s`
    have hinj : Set.InjOn (fun i : ℤ => i • t) s := by
      intro i hi j hj hij
      by_contra hne
      have hd := hdisj i (Finset.mem_coe.1 hi) j (Finset.mem_coe.1 hj) hne
      have hij' : i • t = j • t := hij
      have h1 : a + i • t ∈ (fun x : G => x + i • t) '' A := ⟨a, ha, rfl⟩
      have h2 : a + i • t ∈ (fun x : G => x + j • t) '' A := by
        refine ⟨a, ha, ?_⟩
        show a + j • t = a + i • t
        rw [hij']
      exact Set.disjoint_left.1 hd h1 h2
    have hdisjS : ∀ u ∈ s.image (fun i : ℤ => i • t), ∀ v ∈ s.image (fun i : ℤ => i • t), u ≠ v →
        Disjoint ((fun x : G => x + u) '' A) ((fun x : G => x + v) '' A) := by
      intro u hu v hv huv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
      exact hdisj i hi j hj fun hij => huv (congrArg (fun i : ℤ => i • t) hij)
    have hS := h (s.image (fun i : ℤ => i • t)) A hdisjS
    rw [Finset.card_image_of_injOn hinj] at hS
    have hU : (⋃ u ∈ s.image (fun i : ℤ => i • t), (fun x : G => x + u) '' A)
        = ⋃ i ∈ s, (fun x : G => x + i • t) '' A := by
      ext y
      constructor
      · intro hy
        obtain ⟨u, hu, hyu⟩ := Set.mem_iUnion₂.1 hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
        exact Set.mem_iUnion₂.2 ⟨i, hi, hyu⟩
      · intro hy
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 hy
        exact Set.mem_iUnion₂.2 ⟨i • t, Finset.mem_image.2 ⟨i, hi, rfl⟩, hyi⟩
    rw [hU] at hS
    exact hS

/-- **#371629 — the source's statement.**

A sequence of `ℓ¹` probability measures is asymptotically translation invariant **iff** the upper
density it induces satisfies the Révész–Ruzsa axioms: norming on constants, perturbation invariance,
and restricted additivity **for an arbitrary finite family of shifts**.  No hypothesis on `G`, no
hypothesis on `t`.

**The two directions use different forms of restricted additivity on purpose.**  Sufficiency
*produces* the general form (`restrictedAdditive_density_general`), because a weaker conclusion would
be a weaker theorem.  Necessity *consumes* the single-shift form, because that is all the block
argument needs and consuming less makes that direction stronger;
`restrictedAdditiveAlong_of_restrictedAdditive` bridges the two.

That asymmetry is the whole lesson of this row's two comparator failures.  A predicate appearing on
both sides of an `iff` cannot be judged once — a narrowing is harmless where it is consumed and
load-bearing where it is produced, and I mistook the first for the second twice. -/
theorem tendsto_subTranslate_iff_isUpperDensity (μ : ℕ → L1Prob G) :
    (∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0))
      ↔ (density μ Set.univ = 1 ∧ PerturbationInvariant (density μ) ∧
          RestrictedAdditive (density μ)) := by
  constructor
  · intro h1
    exact ⟨density_univ μ, perturbationInvariant_density μ h1,
      restrictedAdditive_density_general μ h1⟩
  · rintro ⟨hone, hpert, hadd⟩ u
    exact tendsto_l1norm_subTranslate_of_dominated_all μ (density μ) u
      (restrictedAdditiveAlong_of_restrictedAdditive hadd u) hpert hone
      fun A => le_of_eq (limsup_toFinAddProb_eq_density μ A)

/-! ### `d̄` is an upper density — all of the axioms, not just the two that are hard

The previous capstone asserted three conjuncts: norming, perturbation invariance, restricted
additivity.  Those are the two *substantive* axioms plus normalization — but a Révész–Ruzsa upper
density is also **monotone** and **subadditive**, and the statement said nothing about them.  They
hold unconditionally for `density μ`, which is exactly why they were easy to forget: no proof ever
failed for want of them.

Nonnegative homogeneity is a property of the upper *mean* `M̄` on functions, not of `d̄` on sets —
indicators are not scaled — and it is `mean_smul`. -/

/-- Monotonicity of the induced density.  Unconditional: no assumption on `μ` beyond its being a
sequence of probabilities. -/
theorem density_mono (μ : ℕ → L1Prob G) {A B : Set G} (hAB : A ⊆ B) :
    density μ A ≤ density μ B := by
  refine mean_mono μ (abs_indicator_one_le A) (abs_indicator_one_le B) fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hAB hx)]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) x

/-- Subadditivity of the induced density.  Also unconditional. -/
theorem density_subadditive (μ : ℕ → L1Prob G) (A B : Set G) :
    density μ (A ∪ B) ≤ density μ A + density μ B := by
  have hsum : ∀ x, |Set.indicator A (fun _ => (1 : ℝ)) x
      + Set.indicator B (fun _ => (1 : ℝ)) x| ≤ 2 := by
    intro x
    have h1 := abs_indicator_one_le A x
    have h2 := abs_indicator_one_le B x
    calc |Set.indicator A (fun _ => (1 : ℝ)) x + Set.indicator B (fun _ => (1 : ℝ)) x|
        ≤ |Set.indicator A (fun _ => (1 : ℝ)) x| + |Set.indicator B (fun _ => (1 : ℝ)) x| :=
          abs_add_le _ _
      _ ≤ 2 := by linarith
  have hstep : mean μ (Set.indicator (A ∪ B) (fun _ => (1 : ℝ)))
      ≤ mean μ (fun x => Set.indicator A (fun _ => (1 : ℝ)) x
          + Set.indicator B (fun _ => (1 : ℝ)) x) := by
    refine mean_mono μ (abs_indicator_one_le (A ∪ B)) hsum fun x => ?_
    by_cases hx : x ∈ A ∪ B
    · rw [Set.indicator_of_mem hx]
      rcases hx with hxA | hxB
      · rw [Set.indicator_of_mem hxA]
        have hB : (0 : ℝ) ≤ Set.indicator B (fun _ => (1 : ℝ)) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        linarith
      · rw [Set.indicator_of_mem hxB]
        have hA : (0 : ℝ) ≤ Set.indicator A (fun _ => (1 : ℝ)) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        linarith
    · rw [Set.indicator_of_notMem hx]
      have h1 : (0 : ℝ) ≤ Set.indicator A (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have h2 : (0 : ℝ) ≤ Set.indicator B (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      linarith
  exact le_trans hstep
    (mean_add_le μ (abs_indicator_one_le A) (abs_indicator_one_le B))

/-- **An upper density in the sense of Révész–Ruzsa**, bundled.

Norming on constants, monotonicity and subadditivity are the general axioms; restricted additivity
and perturbation invariance are the two the source singles out as the ones its argument uses. -/
def IsUpperDensity (d : Set G → ℝ) : Prop :=
  d Set.univ = 1 ∧ (∀ A B : Set G, A ⊆ B → d A ≤ d B)
    ∧ (∀ A B : Set G, d (A ∪ B) ≤ d A + d B)
    ∧ RestrictedAdditive d ∧ PerturbationInvariant d

/-- **#371629.**  A sequence of `ℓ¹` probability measures is asymptotically translation invariant
**iff** the upper density it induces is an upper density in the sense of Révész–Ruzsa.  No hypothesis
on `G`, none on `t`, and every axiom of the definition is present. -/
theorem tendsto_subTranslate_iff_isUpperDensity_full (μ : ℕ → L1Prob G) :
    (∀ u : G, Filter.Tendsto (fun n => ∑' x, |subTranslate (μ n) u x|) Filter.atTop (nhds 0))
      ↔ IsUpperDensity (density μ) := by
  constructor
  · intro h1
    exact ⟨density_univ μ, fun _ _ h => density_mono μ h, density_subadditive μ,
      restrictedAdditive_density_general μ h1, perturbationInvariant_density μ h1⟩
  · rintro ⟨hone, -, -, hadd, hpert⟩ u
    exact tendsto_l1norm_subTranslate_of_dominated_all μ (density μ) u
      (restrictedAdditiveAlong_of_restrictedAdditive hadd u) hpert hone
      fun A => le_of_eq (limsup_toFinAddProb_eq_density μ A)

end Translate

end Principia.MathDB.P371629
