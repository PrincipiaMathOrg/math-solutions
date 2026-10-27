import Mathlib

/-!
# MathDB #374957 — transpose duality for preorder multichain matrices (SPINE)

Write-up `mathdb-open-problems/problems/374957/solution.tex`,
*Transpose duality for preorder multichain matrices*, 18 September 2026.
Source: C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to preorders*,
arXiv:2605.26916v1 (2026), Conjecture 4.2.

For a preorder `τ` on a finite set `E`, the preorder polytope is
`Q_τ = {x ≥ 0 : ∑_{e ∈ I} x_e ≤ |I| for every order ideal I}`, and `∇_τ(k,ℓ)` counts the
`k`-multichains `a⁽¹⁾ ≤ ⋯ ≤ a⁽ᵏ⁾` inside `ℓQ_τ ∩ ℤ^E`.  The conjecture is

    ∇_τ(k,ℓ) = ∇_{τ*}(ℓ,k)     for every finite preorder and all k, ℓ ≥ 0,

with `τ*` the reversed preorder.  Note it is a **pure counting identity between two finite
cardinalities** — nothing asserts either side is a polynomial, so the Ehrhart polynomiality that
Mathlib lacks is never needed.  (This row's original triage said otherwise; see the campaign
README.)

## How the work is split, and why that split is the honest one

The write-up's proof has two ingredients, and it is explicit about which is its own:

* the **increments identification** — reindexing a multichain by its successive differences
  turns `∇_τ(k,ℓ)` into a count of nonnegative integer matrices on `E × [k]` constrained by
  `∑_{f ∈ I} ∑_t z_{f,t} ≤ ℓ|I|`.  The write-up calls this, with the repeated-vertex graph,
  *"the reduction resolving the target"*;
* **Postnikov's lattice-point duality** for Minkowski sums of coordinate simplices, which it
  states is *"an established input, not a new claim of this solution"*.

So this module proves the reduction's content and carries the cited classical input as a named
hypothesis, never a `sorry`.

### Proved here, unconditionally

* `InPoly.mono_le` — the dilated polytope's integer points are **downward closed** under
  coordinatewise decrease.  This is the write-up's *"every earlier vector does too"* step, and it
  is what makes the whole increments construction work: only the TERMINAL vector of a multichain
  has to be checked against the ideal inequalities.
* `partialSum`, `partialSum_mono`, `partialSum_le_total` — the increments-to-chain map and its
  two structural facts.
* `toMultichain` — the forward half of the identification, **built and proved to land in the
  polytope**: given increments satisfying the ideal bound, its partial sums really are a
  multichain in `ℓQ_τ ∩ ℤ^E`.
* `isIdeal_univ`, `isIdeal_empty` — the two ideals every preorder has.
* `nabla_zero_left` — the `k = 0` degenerate parameter, where the
  write-up's "these cases give the same identity" is discharged outright rather than assumed.

### The increments identification is PROVED, not assumed

`nabla_eq_W` is unconditional.  Injectivity (`toMultichain_injective`) and surjectivity
(`incrementsSurjective`) are both established, so the write-up's own stated contribution is
carried in Lean rather than hypothesised.  Neither direction needed `ℕ`-subtraction: the splitting
`Finset.Iic j = insert j (Finset.Iio j)` lets `Nat.add_right_cancel` recover an increment for
injectivity, and for surjectivity `diffs` uses an explicit predecessor whose truncated subtraction
is *exact* because the chain is monotone.  `IncrementsBijection` survives only as the weaker
statement that `incrementsBijection_of_surjective` discharges, kept so the earlier `main_of_hyps`
still typechecks.

### Carried as a hypothesis — one, not two

* `PostnikovDuality` — `W_τ(k,ℓ) = W_{τ*}(ℓ,k)`.  This is where Postnikov's lattice-point duality
  lives.  The write-up derives it from **Hall's marriage theorem, which Mathlib HAS**
  (`Combinatorics/Hall/Basic.lean`), together with Athanasiadis–Chapoton's counting theorem;
  Mathlib has neither Postnikov's theorem nor any Minkowski-sum lattice-point theory, so this is
  the row's whole remaining residue.  Reversal is an involution on it, which `reverse_reverse`
  records.

`main_of_duality` takes that single hypothesis and delivers Conjecture 4.2.
-/

namespace Principia.MathDB.P374957

-- Only the two declarations that mention `Finset.univ` need `[Fintype E]`; it is requested there
-- rather than in this `variable` line, so the rest of the module carries no unused instances.
variable {E : Type*}

/-! ### Order ideals -/

/-- `I` is an **order ideal** of the preorder `r`: downward closed, i.e. `r e f` and `f ∈ I`
force `e ∈ I`.  No antisymmetry is assumed anywhere — the write-up notes that equivalent
distinct elements of a preorder are deliberately included. -/
def IsIdeal (r : E → E → Prop) (I : Finset E) : Prop :=
  ∀ e f : E, r e f → f ∈ I → e ∈ I

/-- The reversed preorder `τ*`. -/
def reverse (r : E → E → Prop) : E → E → Prop := fun a b => r b a

@[simp] theorem reverse_reverse (r : E → E → Prop) : reverse (reverse r) = r := rfl

theorem isIdeal_univ [Fintype E] (r : E → E → Prop) :
    IsIdeal r (Finset.univ : Finset E) :=
  fun _ _ _ _ => Finset.mem_univ _

theorem isIdeal_empty (r : E → E → Prop) : IsIdeal r (∅ : Finset E) :=
  fun _ _ _ hf => absurd hf (Finset.notMem_empty _)

/-! ### Integer points of the dilate `ℓ · Q_τ` -/

/-- `x` is an integer point of `ℓ · Q_τ`: a nonnegative integer vector (automatic over `ℕ`)
with `∑_{e ∈ I} x e ≤ ℓ * |I|` for every order ideal `I`. -/
def InPoly (r : E → E → Prop) (l : ℕ) (x : E → ℕ) : Prop :=
  ∀ I : Finset E, IsIdeal r I → ∑ e ∈ I, x e ≤ l * I.card

/-- **The dilate is downward closed under coordinatewise decrease.**

This is the write-up's *"every earlier vector does too, since the polytope is closed under
decreasing nonnegative coordinates"*, and it is the reason the increments construction only has
to check its terminal vector against the ideal inequalities. -/
theorem InPoly.mono_le {r : E → E → Prop} {l : ℕ} {x y : E → ℕ}
    (hy : InPoly r l y) (hxy : ∀ e, x e ≤ y e) : InPoly r l x := fun I hI =>
  le_trans (Finset.sum_le_sum fun e _ => hxy e) (hy I hI)

/-- Over `ℓ = 0` the only integer point is the origin: `univ` is an ideal, so the whole sum
is bounded by `0`. -/
theorem InPoly.eq_zero_of_l_zero [Finite E] {r : E → E → Prop} {x : E → ℕ}
    (hx : InPoly r 0 x) (e : E) : x e = 0 := by
  -- `[Finite E]` rather than `[Fintype E]`: the STATEMENT never mentions a `Fintype`, only the
  -- proof needs one to form `Finset.univ`, which is exactly what the `unusedFintypeInType`
  -- linter asks for.  A `letI` suffices because the sum lives in the proof, not the statement.
  letI := Fintype.ofFinite E
  have h := hx Finset.univ (isIdeal_univ r)
  rw [Nat.zero_mul] at h
  exact Nat.eq_zero_of_le_zero
    (le_trans (Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)) h)

/-! ### Multichains and increment matrices -/

/-- A `k`-multichain in `ℓ · Q_τ ∩ ℤ^E`: a coordinatewise-nondecreasing sequence of integer
points of the dilate. -/
structure Multichain (r : E → E → Prop) (k l : ℕ) where
  a : Fin k → E → ℕ
  mono : ∀ i j : Fin k, i ≤ j → ∀ e, a i e ≤ a j e
  mem : ∀ j, InPoly r l (a j)

/-- The increment matrices of the write-up's equation (increments): nonnegative integer
`z : E × [k] → ℕ` with `∑_{f ∈ I} ∑_t z_{f,t} ≤ ℓ|I|` for every order ideal `I`. -/
structure Increments (r : E → E → Prop) (k l : ℕ) where
  z : Fin k → E → ℕ
  bound : ∀ I : Finset E, IsIdeal r I → ∑ e ∈ I, (∑ t : Fin k, z t e) ≤ l * I.card

/-- `∇_τ(k,ℓ)`. -/
noncomputable def nabla (r : E → E → Prop) (k l : ℕ) : ℕ := Nat.card (Multichain r k l)

/-- `W_τ(k,ℓ)`, the increment-matrix count. -/
noncomputable def W (r : E → E → Prop) (k l : ℕ) : ℕ := Nat.card (Increments r k l)

/-! ### The forward half of the increments identification, proved -/

/-- Partial sums of an increment matrix: the write-up's `a⁽ʲ⁾_f = ∑_{t ≤ j} z_{f,t}`. -/
def partialSum {k : ℕ} (z : Fin k → E → ℕ) (j : Fin k) (e : E) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin k => t ≤ j), z t e

theorem partialSum_mono {k : ℕ} (z : Fin k → E → ℕ) (i j : Fin k) (hij : i ≤ j) (e : E) :
    partialSum z i e ≤ partialSum z j e := by
  apply Finset.sum_le_sum_of_subset
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact le_trans ht hij

theorem partialSum_le_total {k : ℕ} (z : Fin k → E → ℕ) (j : Fin k) (e : E) :
    partialSum z j e ≤ ∑ t : Fin k, z t e :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **The forward map of the identification, with its polytope membership proved.**

Given increments obeying the ideal bound, the partial sums form a genuine `k`-multichain in
`ℓ · Q_τ ∩ ℤ^E`.  Membership of every entry follows from membership of the terminal vector by
`InPoly.mono_le` — which is exactly the write-up's argument. -/
def toMultichain {r : E → E → Prop} {k l : ℕ} (w : Increments r k l) : Multichain r k l where
  a := partialSum w.z
  mono := fun i j hij e => partialSum_mono w.z i j hij e
  mem := fun j => InPoly.mono_le (y := fun e => ∑ t : Fin k, w.z t e) w.bound
    (fun e => partialSum_le_total w.z j e)

/-! ### `toMultichain` is injective — proved, with no subtraction anywhere

The obvious route to inverting the increments map is `z_{f,t} = a⁽ᵗ⁾_f − a⁽ᵗ⁻¹⁾_f`, which drags in
`ℕ`-subtraction.  Injectivity needs none of it: `Iic j = insert j (Iio j)` splits a partial sum as
`z j e + ∑_{t < j} z t e`, so `Nat.add_right_cancel` recovers `z j e` once the strictly earlier
values are known, and plain induction on a bound for `j.val` supplies those. -/

theorem partialSum_eq_Iic {k : ℕ} (z : Fin k → E → ℕ) (j : Fin k) (e : E) :
    partialSum z j e = ∑ t ∈ Finset.Iic j, z t e := by
  unfold partialSum
  congr 1
  ext t
  simp

/-- Peel the top index off a partial sum.  This one split carries both directions of the
identification: injectivity cancels it, surjectivity telescopes it. -/
theorem partialSum_split {k : ℕ} (z : Fin k → E → ℕ) (j : Fin k) (e : E) :
    partialSum z j e = z j e + ∑ t ∈ Finset.Iio j, z t e := by
  rw [partialSum_eq_Iic, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]

/-- One step of the recovery: the value at `j` is determined by the partial sum at `j` together
with the strictly earlier values. -/
theorem partialSum_step {k : ℕ} (z z' : Fin k → E → ℕ) (j : Fin k) (e : E)
    (hj : partialSum z j e = partialSum z' j e)
    (hlt : ∀ t ∈ Finset.Iio j, z t e = z' t e) : z j e = z' j e := by
  rw [partialSum_split z j e, partialSum_split z' j e, Finset.sum_congr rfl hlt] at hj
  exact Nat.add_right_cancel hj

/-- **The increments are recoverable from their partial sums.** -/
theorem partialSum_injective {k : ℕ} {z z' : Fin k → E → ℕ}
    (h : partialSum z = partialSum z') : z = z' := by
  have hpt : ∀ j e, partialSum z j e = partialSum z' j e := fun j e => by rw [h]
  -- induction on a BOUND for `j.val`, so ordinary `Nat.rec` suffices; no strong recursion needed
  have key : ∀ n : ℕ, ∀ j : Fin k, (j : ℕ) ≤ n → ∀ e, z j e = z' j e := by
    intro n
    induction n with
    | zero =>
      intro j hj e
      refine partialSum_step z z' j e (hpt j e) ?_
      intro t ht
      rw [Finset.mem_Iio, Fin.lt_def] at ht
      exact absurd ht (by omega)
    | succ m ih =>
      intro j hj e
      refine partialSum_step z z' j e (hpt j e) ?_
      intro t ht
      rw [Finset.mem_Iio, Fin.lt_def] at ht
      exact ih t (by omega) e
  funext j e
  exact key (j : ℕ) j le_rfl e

/-- **The forward half of the identification is injective.**  So the bijection hypothesis reduces
to *surjectivity* alone. -/
theorem toMultichain_injective {r : E → E → Prop} {k l : ℕ} :
    Function.Injective (toMultichain (r := r) (k := k) (l := l)) := by
  intro w w' hw
  obtain ⟨z1, b1⟩ := w
  obtain ⟨z2, b2⟩ := w'
  have hz : partialSum z1 = partialSum z2 := congrArg Multichain.a hw
  have h1 : z1 = z2 := partialSum_injective hz
  subst h1
  rfl

/-! ### The degenerate parameters, discharged -/

instance instSubsingletonMultichainZero (r : E → E → Prop) (l : ℕ) :
    Subsingleton (Multichain r 0 l) := by
  constructor
  intro x y
  obtain ⟨a, _, _⟩ := x
  obtain ⟨b, _, _⟩ := y
  have : a = b := by
    funext j
    exact absurd j.2 (Nat.not_lt_zero _)
  subst this
  rfl

instance instNonemptyMultichainZero (r : E → E → Prop) (l : ℕ) :
    Nonempty (Multichain r 0 l) :=
  ⟨{ a := fun j _ => absurd j.2 (Nat.not_lt_zero _)
     mono := fun j _ _ _ => absurd j.2 (Nat.not_lt_zero _)
     mem := fun j => absurd j.2 (Nat.not_lt_zero _) }⟩

/-- `k = 0`: exactly the empty multichain. -/
theorem nabla_zero_left (r : E → E → Prop) (l : ℕ) : nabla r 0 l = 1 := by
  rw [nabla, Nat.card_eq_one_iff_unique]
  exact ⟨instSubsingletonMultichainZero r l, instNonemptyMultichainZero r l⟩

/-! ### The two carried hypotheses, and the composition -/

/-- **The increments identification is a bijection** — the write-up's equations (chain) and (id).
`toMultichain` above is the forward map, constructed and proved; what this hypothesis still owes
is injectivity and surjectivity, i.e. recovering `z_{f,t} = a⁽ᵗ⁾_f − a⁽ᵗ⁻¹⁾_f`. -/
def IncrementsBijection (r : E → E → Prop) (k l : ℕ) : Prop := nabla r k l = W r k l

/-- **Postnikov's lattice-point duality**, transported along `G_τ(k,ℓ)* = G_{τ*}(ℓ,k)`.

The write-up derives `#(P_G ∩ ℤ^B) = #(P_{G*} ∩ ℤ^A)` from Hall's marriage theorem (which
Mathlib has) plus Athanasiadis–Chapoton's counting theorem, and states the duality is *"an
established input, not a new claim of this solution"*.  Mathlib has no Postnikov theorem and no
Minkowski-sum lattice-point theory, so this is the row's residue. -/
-- SPEC-CARRY-CHECKED: PostnikovDuality -- 2026-09-26.  What stays carried is exactly what the
-- write-up itself calls "an established input, not a new claim of this solution"; `nabla_eq_W` is
-- unconditional, so this Prop is the row's whole residue.  A cited literature input on an
-- uncounted row, not a vacuity.
def PostnikovDuality (r : E → E → Prop) (k l : ℕ) : Prop := W r k l = W (reverse r) l k

/-- **Conjecture 4.2, conditional on the two named inputs.**  The composition is a typing
fact: no gap can hide in the reassembly. -/
theorem main_of_hyps (r : E → E → Prop) (k l : ℕ)
    (hb : IncrementsBijection r k l) (hd : PostnikovDuality r k l)
    (hb' : IncrementsBijection (reverse r) l k) :
    nabla r k l = nabla (reverse r) l k := by
  rw [IncrementsBijection] at hb hb'
  rw [PostnikovDuality] at hd
  rw [hb, hd, hb']

/-! ### Surjectivity: every multichain IS the partial sums of its own differences

This discharges the remaining half of the identification.  Two things make it cheap.  The
truncated subtraction `a j e - a (j-1) e` is **exact**, because the chain is monotone, so no
side conditions leak out.  And the bound on the constructed increments does not have to be
re-derived: summing all of them gives back the chain's TERMINAL vector (`sum_diffs_eq_top`,
via `univ = Iic last`), whose membership is part of the multichain's data. -/

/-- In `Fin k`, `Iio j` is `Iic` of the predecessor. -/
theorem Iio_eq_Iic_pred {k : ℕ} (j : Fin k) (h : (j : ℕ) ≠ 0) :
    Finset.Iio j = Finset.Iic ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ := by
  ext t
  simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
  omega

theorem Iio_eq_empty_of_val_zero {k : ℕ} (j : Fin k) (h : (j : ℕ) = 0) :
    Finset.Iio j = ∅ := by
  ext t
  simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, Fin.lt_def]
  omega

/-- The successive differences of a chain.  No predecessor is needed at `j = 0`. -/
def diffs {k : ℕ} (a : Fin k → E → ℕ) (j : Fin k) (e : E) : ℕ :=
  if (j : ℕ) = 0 then a j e
  else a j e - a ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ e

/-- **The differences telescope back to the chain.** -/
theorem partialSum_diffs {k : ℕ} {a : Fin k → E → ℕ}
    (hmono : ∀ i j : Fin k, i ≤ j → ∀ e, a i e ≤ a j e) (j : Fin k) (e : E) :
    partialSum (diffs a) j e = a j e := by
  have key : ∀ n : ℕ, ∀ j : Fin k, (j : ℕ) ≤ n → ∀ e, partialSum (diffs a) j e = a j e := by
    intro n
    induction n with
    | zero =>
      intro j hj e
      have hz : (j : ℕ) = 0 := by omega
      rw [partialSum_split, Iio_eq_empty_of_val_zero j hz, Finset.sum_empty, Nat.add_zero, diffs,
        if_pos hz]
    | succ m ih =>
      intro j hj e
      rcases eq_or_ne (j : ℕ) 0 with hz | hz
      · rw [partialSum_split, Iio_eq_empty_of_val_zero j hz, Finset.sum_empty, Nat.add_zero, diffs,
          if_pos hz]
      · -- The predecessor is written out EXPLICITLY, with the same proof term that
        -- `Iio_eq_Iic_pred` and `diffs` use, so the rewrites line up syntactically.  A `set`
        -- here is what broke the first attempt: it hides `(⟨↑j - 1, _⟩ : Fin k).val` behind a
        -- local constant, and `omega` then treats that value as an opaque atom unrelated to
        -- `↑j`, exactly the "two atoms" trap.
        have hlt : (j : ℕ) - 1 < k := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
        have hple : (⟨(j : ℕ) - 1, hlt⟩ : Fin k) ≤ j := by
          rw [Fin.le_def]
          exact Nat.sub_le _ _
        have hIH : partialSum (diffs a) ⟨(j : ℕ) - 1, hlt⟩ e = a ⟨(j : ℕ) - 1, hlt⟩ e :=
          -- `change`, not `show`: this unfolds `Fin.val (mk ..)`, i.e. it alters the goal rather
          -- than restating it, which is what the `linter.style.show` linter asks for.
          ih ⟨(j : ℕ) - 1, hlt⟩ (by change (j : ℕ) - 1 ≤ m; omega) e
        rw [partialSum_split, Iio_eq_Iic_pred j hz, ← partialSum_eq_Iic, hIH, diffs, if_neg hz]
        exact Nat.sub_add_cancel (hmono _ j hple e)
  exact key (j : ℕ) j le_rfl e

/-- Summing every difference returns the chain's terminal vector. -/
theorem sum_diffs_eq_top {k : ℕ} (hk : 0 < k) {a : Fin k → E → ℕ}
    (hmono : ∀ i j : Fin k, i ≤ j → ∀ e, a i e ≤ a j e) (e : E) :
    ∑ t : Fin k, diffs a t e = a ⟨k - 1, by omega⟩ e := by
  have huniv : (Finset.univ : Finset (Fin k)) = Finset.Iic ⟨k - 1, by omega⟩ := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_Iic, Fin.le_def, true_iff]
    omega
  rw [huniv, ← partialSum_eq_Iic]
  exact partialSum_diffs hmono _ e

/-! ### The weaker form of the first hypothesis

`toMultichain_injective` is proved, so the identification needs only **surjectivity** — every
multichain arises as the partial sums of some increment matrix.  `IncrementsSurjective` is
therefore strictly weaker than `IncrementsBijection`, and `main_of_surj` is the capstone a future
tick should discharge. -/

/-- Surjectivity of the increments map: the only half of the identification still owed. -/
def IncrementsSurjective (r : E → E → Prop) (k l : ℕ) : Prop :=
  Function.Surjective (toMultichain (r := r) (k := k) (l := l))

/-- Surjectivity suffices, because injectivity is proved. -/
theorem nabla_eq_W_of_surjective {r : E → E → Prop} {k l : ℕ}
    (h : IncrementsSurjective r k l) : nabla r k l = W r k l :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨toMultichain_injective, h⟩)).symm

/-- So the bijection hypothesis is implied by the surjectivity one. -/
theorem incrementsBijection_of_surjective {r : E → E → Prop} {k l : ℕ}
    (h : IncrementsSurjective r k l) : IncrementsBijection r k l :=
  nabla_eq_W_of_surjective h

/-- **Conjecture 4.2 from the weaker pair of hypotheses.** -/
theorem main_of_surj (r : E → E → Prop) (k l : ℕ)
    (hs : IncrementsSurjective r k l) (hd : PostnikovDuality r k l)
    (hs' : IncrementsSurjective (reverse r) l k) :
    nabla r k l = nabla (reverse r) l k :=
  main_of_hyps r k l (incrementsBijection_of_surjective hs) hd
    (incrementsBijection_of_surjective hs')

/-! ### Surjectivity is now PROVED, so the identification is no longer a hypothesis

`diffs` supplies the preimage and `partialSum_diffs` shows it is one.  The constructed increments
satisfy the ideal bound for free: summing all of them returns the chain's terminal vector, whose
membership is part of the multichain's data.  So `IncrementsBijection` is discharged and the row
rests on `PostnikovDuality` ALONE. -/

/-- Surjectivity for a nonempty chain length. -/
theorem incrementsSurjective_of_pos {r : E → E → Prop} {k l : ℕ} (hk : 0 < k) :
    IncrementsSurjective r k l := by
  intro m
  obtain ⟨a, hmono, hmem⟩ := m
  refine ⟨⟨diffs a, ?_⟩, ?_⟩
  · -- the bound comes from the TERMINAL vector, not re-derived
    intro I hI
    have hb := hmem ⟨k - 1, by omega⟩ I hI
    calc ∑ e ∈ I, (∑ t : Fin k, diffs a t e)
        = ∑ e ∈ I, a ⟨k - 1, by omega⟩ e :=
          Finset.sum_congr rfl fun e _ => sum_diffs_eq_top hk hmono e
      _ ≤ l * I.card := hb
  · simp only [toMultichain]
    congr 1
    funext j e
    exact partialSum_diffs hmono j e

/-- Surjectivity at `k = 0`, where both sides are singletons. -/
theorem incrementsSurjective_zero {r : E → E → Prop} {l : ℕ} : IncrementsSurjective r 0 l := by
  intro m
  refine ⟨⟨fun j _ => absurd j.2 (Nat.not_lt_zero _), ?_⟩, ?_⟩
  · intro I _
    simp
  · exact Subsingleton.elim _ _

/-- **The increments identification is a bijection — unconditionally.** -/
theorem incrementsSurjective (r : E → E → Prop) (k l : ℕ) : IncrementsSurjective r k l := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; exact incrementsSurjective_zero
  · exact incrementsSurjective_of_pos hk

/-- `∇_τ(k,ℓ) = W_τ(k,ℓ)`, with no hypotheses: the write-up's equations (chain) and (id). -/
theorem nabla_eq_W (r : E → E → Prop) (k l : ℕ) : nabla r k l = W r k l :=
  nabla_eq_W_of_surjective (incrementsSurjective r k l)

/-- **Conjecture 4.2 now rests on Postnikov's duality ALONE.**  The increments identification,
which was the write-up's own stated contribution, is discharged. -/
theorem main_of_duality (r : E → E → Prop) (k l : ℕ) (hd : PostnikovDuality r k l) :
    nabla r k l = nabla (reverse r) l k := by
  rw [PostnikovDuality] at hd
  rw [nabla_eq_W, hd, ← nabla_eq_W]

/-! ### The degenerate strata, which need no Postnikov

`PostnikovDuality` is the row's whole residue, and it is a cited literature input.  At `k = 0`
and at `l = 0` both sides of it are `1` for elementary reasons, so the duality — and Conjecture 4.2
with it — is unconditional there.  **This covers two UNCOVERED CASES; it does not
discharge the hypothesis**, and the strata are the cases with no content: the row's
mathematics lives at `k, l ≥ 1`.

* `k = 0` — the increment matrix is the empty function and the ideal bound reads `0 ≤ ℓ·#I`.
* `l = 0` — the bound at `I = univ` (`isIdeal_univ`) forces every entry to vanish. -/

/-- `k = 0`: the only increment matrix is the empty one. -/
instance instSubsingletonIncrementsZeroLeft (r : E → E → Prop) (l : ℕ) :
    Subsingleton (Increments r 0 l) := by
  constructor
  intro x y
  obtain ⟨z, _⟩ := x
  obtain ⟨z', _⟩ := y
  have : z = z' := by
    funext t
    exact absurd t.2 (Nat.not_lt_zero _)
  subst this
  rfl

instance instNonemptyIncrementsZeroLeft (r : E → E → Prop) (l : ℕ) :
    Nonempty (Increments r 0 l) :=
  ⟨{ z := fun t _ => absurd t.2 (Nat.not_lt_zero _)
     bound := by
       intro I _
       have hz : ∑ e ∈ I, (∑ t : Fin 0,
           (fun t _ => absurd t.2 (Nat.not_lt_zero _) : Fin 0 → E → ℕ) t e) = 0 := by simp
       rw [hz]
       exact Nat.zero_le _ }⟩

/-- `W_τ(0, ℓ) = 1`. -/
theorem W_zero_left (r : E → E → Prop) (l : ℕ) : W r 0 l = 1 := by
  rw [W, Nat.card_eq_one_iff_unique]
  exact ⟨instSubsingletonIncrementsZeroLeft r l, instNonemptyIncrementsZeroLeft r l⟩

/-- `l = 0`: every entry vanishes.  The column-sum vector is an integer point of the `0`-dilate --
`Increments.bound` at `l = 0` IS `InPoly r 0` by definition -- so the module's own
`InPoly.eq_zero_of_l_zero` kills the column sum, and a single entry is bounded by it. -/
theorem increments_eq_zero_of_dilate_zero [Finite E] {r : E → E → Prop} {k : ℕ}
    (w : Increments r k 0) (t : Fin k) (e : E) : w.z t e = 0 := by
  letI := Fintype.ofFinite E
  have hcol : ∑ t : Fin k, w.z t e = 0 :=
    InPoly.eq_zero_of_l_zero (x := fun e => ∑ t : Fin k, w.z t e) w.bound e
  exact Nat.eq_zero_of_le_zero
    (le_trans (Finset.single_le_sum (f := fun t => w.z t e)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)) (le_of_eq hcol))

instance instSubsingletonIncrementsZeroRight [Finite E] (r : E → E → Prop) (k : ℕ) :
    Subsingleton (Increments r k 0) := by
  constructor
  intro x y
  have hx := increments_eq_zero_of_dilate_zero x
  have hy := increments_eq_zero_of_dilate_zero y
  obtain ⟨z, _⟩ := x
  obtain ⟨z', _⟩ := y
  have : z = z' := by
    funext t e
    have h1 : z t e = 0 := hx t e
    have h2 : z' t e = 0 := hy t e
    rw [h1, h2]
  subst this
  rfl

instance instNonemptyIncrementsZeroRight (r : E → E → Prop) (k : ℕ) :
    Nonempty (Increments r k 0) :=
  ⟨{ z := fun _ _ => 0
     bound := by intro I _; simp }⟩

/-- `W_τ(k, 0) = 1`. -/
theorem W_zero_right [Finite E] (r : E → E → Prop) (k : ℕ) : W r k 0 = 1 := by
  rw [W, Nat.card_eq_one_iff_unique]
  exact ⟨instSubsingletonIncrementsZeroRight r k, instNonemptyIncrementsZeroRight r k⟩

/-- **POSTNIKOV'S DUALITY AT `k = 0`, WITHOUT POSTNIKOV.** -/
theorem postnikovDuality_zero_left [Finite E] (r : E → E → Prop) (l : ℕ) :
    PostnikovDuality r 0 l := by
  rw [PostnikovDuality, W_zero_left, W_zero_right]

/-- **POSTNIKOV'S DUALITY AT `l = 0`, WITHOUT POSTNIKOV.** -/
theorem postnikovDuality_zero_right [Finite E] (r : E → E → Prop) (k : ℕ) :
    PostnikovDuality r k 0 := by
  rw [PostnikovDuality, W_zero_right, W_zero_left]

/-- **CONJECTURE 4.2 IS UNCONDITIONAL AT `k = 0`.** -/
theorem main_zero_left [Finite E] (r : E → E → Prop) (l : ℕ) :
    nabla r 0 l = nabla (reverse r) l 0 :=
  main_of_duality r 0 l (postnikovDuality_zero_left r l)

/-- **CONJECTURE 4.2 IS UNCONDITIONAL AT `l = 0`.** -/
theorem main_zero_right [Finite E] (r : E → E → Prop) (k : ℕ) :
    nabla r k 0 = nabla (reverse r) 0 k :=
  main_of_duality r k 0 (postnikovDuality_zero_right r k)

/-! ### `k = 1`: `W` IS the lattice-point count of the dilated order polytope

This is the bridge that names what Postnikov's duality is *about*.  An increment matrix with one row
carries no more information than its column-sum vector, so `W_τ(1, ℓ)` is literally
`#(ℓ·Q_τ ∩ ℤ^E)`.  With it, the surviving hypothesis at one row reads as a lattice-point equation
rather than as a fact about matrices — which is the form any future attempt on the residue has to
start from, since Postnikov's theorem is a statement about lattice points of Minkowski sums. -/

/-- Two increment matrices with the same entries are equal; the `bound` field is a `Prop`. -/
theorem increments_ext {r : E → E → Prop} {k l : ℕ} {w w' : Increments r k l}
    (h : w.z = w'.z) : w = w' := by
  obtain ⟨z, hb⟩ := w
  obtain ⟨z', hb'⟩ := w'
  have h' : z = z' := h
  subst h'
  rfl

/-- One-row increment matrices are exactly the lattice points of the dilate. -/
def incrementsOneEquiv (r : E → E → Prop) (l : ℕ) :
    Increments r 1 l ≃ {s : E → ℕ // InPoly r l s} where
  toFun w := ⟨w.z 0, by
    intro I hI
    have h := w.bound I hI
    simpa [Fin.sum_univ_one] using h⟩
  invFun s :=
    { z := fun _ => s.1
      bound := by
        intro I hI
        have h := s.2 I hI
        simpa [Fin.sum_univ_one] using h }
  left_inv w := increments_ext (by
    funext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst ht
    rfl)
  right_inv s := rfl

/-- **`W_τ(1, ℓ) = #(ℓ·Q_τ ∩ ℤ^E)`** — the increment count at one row is the polytope's
lattice-point count. -/
theorem W_one_left (r : E → E → Prop) (l : ℕ) :
    W r 1 l = Nat.card {s : E → ℕ // InPoly r l s} :=
  Nat.card_congr (incrementsOneEquiv r l)

/-- **THE RESIDUE AT `k = 1`, RESTATED AS A LATTICE-POINT EQUATION.**  This is what makes
`W_one_left` load-bearing rather than decorative: it turns the surviving hypothesis at one row
from a statement about increment matrices into one about `#(ℓ·Q_τ ∩ ℤ^E)`. -/
theorem postnikovDuality_one_iff (r : E → E → Prop) (l : ℕ) :
    PostnikovDuality r 1 l ↔ Nat.card {s : E → ℕ // InPoly r l s} = W (reverse r) l 1 := by
  rw [PostnikovDuality, W_one_left]

/-! ### `nabla` and `W` count FINITE types, so the row's equations are not `0 = 0`

Both are `Nat.card`, and **`Nat.card` of an infinite type is `0`**.  Nothing above established that
`Multichain` or `Increments` is finite, so a priori every equation between them — including
Conjecture 4.2 itself — could hold vacuously with both sides `0`.  This section closes that reading.

Under `[Finite E]` the ideal bound at `I = univ` caps every entry by `l · #E`, so each type injects
into a finite function space; and each is nonempty (the zero matrix, the constant-zero chain).  So
both counts are strictly POSITIVE.  **Without `[Finite E]` the degenerate reading is genuinely
available** — for an infinite preorder a principal ideal need not be a `Finset`, so the bound
constrains nothing and the types can be infinite.  That is not a defect in anything proved
above, but it is the difference between an identity and an identity about numbers.

The two nonemptiness facts are plain theorems rather than instances, so they do not overlap the
specialised `instNonemptyIncrementsZeroLeft/Right` and `instNonemptyMultichainZero` above. -/

/-- The ideal bound at `I = univ` caps every entry of an increment matrix. -/
theorem increments_entry_le [Finite E] {r : E → E → Prop} {k l : ℕ}
    (w : Increments r k l) (t : Fin k) (e : E) : w.z t e ≤ l * Nat.card E := by
  letI := Fintype.ofFinite E
  have h := w.bound Finset.univ (isIdeal_univ r)
  have hcard : (Finset.univ : Finset E).card = Nat.card E := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hcard] at h
  have hcol : ∑ t : Fin k, w.z t e ≤ l * Nat.card E :=
    le_trans (Finset.single_le_sum
      (f := fun e => ∑ t : Fin k, w.z t e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)) h
  exact le_trans (Finset.single_le_sum (f := fun t => w.z t e)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)) hcol

/-- Increment matrices form a finite type, so `W` is a genuine cardinality. -/
instance instFiniteIncrements [Finite E] (r : E → E → Prop) (k l : ℕ) :
    Finite (Increments r k l) := by
  have hinj : Function.Injective
      (fun w : Increments r k l => fun t e => (⟨w.z t e, Nat.lt_succ_of_le
        (increments_entry_le w t e)⟩ : Fin (l * Nat.card E + 1))) := by
    intro w w' h
    refine increments_ext ?_
    funext t e
    have := congrFun (congrFun h t) e
    simpa using this
  exact Finite.of_injective _ hinj

/-- The zero matrix is always an increment matrix. -/
theorem nonempty_increments (r : E → E → Prop) (k l : ℕ) : Nonempty (Increments r k l) :=
  ⟨{ z := fun _ _ => 0
     bound := by intro I _; simp }⟩

/-- **`W` IS A POSITIVE COUNT** — not `0` by infinitude. -/
theorem W_pos [Finite E] (r : E → E → Prop) (k l : ℕ) : 0 < W r k l := by
  haveI := nonempty_increments r k l
  rw [W]
  exact Nat.card_pos

/-- Two multichains with the same entries are equal; the other two fields are `Prop`s. -/
theorem multichain_ext {r : E → E → Prop} {k l : ℕ} {c c' : Multichain r k l}
    (h : c.a = c'.a) : c = c' := by
  obtain ⟨a, hm, hp⟩ := c
  obtain ⟨a', hm', hp'⟩ := c'
  have h' : a = a' := h
  subst h'
  rfl

/-- The same entry bound for a multichain. -/
theorem multichain_entry_le [Finite E] {r : E → E → Prop} {k l : ℕ}
    (c : Multichain r k l) (j : Fin k) (e : E) : c.a j e ≤ l * Nat.card E := by
  letI := Fintype.ofFinite E
  have h := c.mem j Finset.univ (isIdeal_univ r)
  have hcard : (Finset.univ : Finset E).card = Nat.card E := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hcard] at h
  exact le_trans (Finset.single_le_sum
    (f := fun e => c.a j e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)) h

/-- Multichains form a finite type, so `nabla` is a genuine cardinality. -/
instance instFiniteMultichain [Finite E] (r : E → E → Prop) (k l : ℕ) :
    Finite (Multichain r k l) := by
  have hinj : Function.Injective
      (fun c : Multichain r k l => fun j e => (⟨c.a j e, Nat.lt_succ_of_le
        (multichain_entry_le c j e)⟩ : Fin (l * Nat.card E + 1))) := by
    intro c c' h
    refine multichain_ext ?_
    funext j e
    have := congrFun (congrFun h j) e
    simpa using this
  exact Finite.of_injective _ hinj

/-- The constant-zero chain is always a multichain. -/
theorem nonempty_multichain (r : E → E → Prop) (k l : ℕ) : Nonempty (Multichain r k l) :=
  ⟨{ a := fun _ _ => 0
     mono := fun _ _ _ _ => le_refl _
     mem := by intro j I _; simp }⟩

/-- **`nabla` IS A POSITIVE COUNT**, so Conjecture 4.2 is an equation between genuine cardinalities
rather than a vacuous `0 = 0`. -/
theorem nabla_pos [Finite E] (r : E → E → Prop) (k l : ℕ) : 0 < nabla r k l := by
  haveI := nonempty_multichain r k l
  rw [nabla]
  exact Nat.card_pos

/-! ### `InPoly` IS INHABITED, AND AT ITS TIGHT POINT

`check_unsatisfied_specs.py` reported `InPoly` as consumed by three declarations with no producer
and **UNEXAMINED** — the one class of spec where a vacuity would go unnoticed, because an empty
hypothesis is axiom-free, gates clean, and passes `check_unused_hypotheses` (the hypothesis really
is used). The constant vector `l` settles it, and settles it at the *extreme* point: it meets every
ideal inequality with **equality**, so the spec is not merely satisfiable but achieved. -/

/-- **`InPoly` at its TIGHT point.**  The constant vector `l` gives `∑_{e ∈ I} l = l · |I|`, so the
ideal inequality holds with equality for every ideal. -/
theorem inPoly_const (r : E → E → Prop) (l : ℕ) : InPoly r l (fun _ => l) := by
  intro I _
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The zero vector, for contrast — the slack witness. -/
theorem inPoly_zero (r : E → E → Prop) (l : ℕ) : InPoly r l (fun _ => 0) := by
  intro I _
  simp

/-- **Non-degenerate inhabitation**: for `l > 0` the dilate contains a NONZERO lattice point, so the
three consumers of `InPoly` are not vacuous. -/
theorem exists_inPoly_ne_zero (r : E → E → Prop) (l : ℕ) (hl : 0 < l) [Nonempty E] :
    ∃ x : E → ℕ, x ≠ 0 ∧ InPoly r l x := by
  refine ⟨fun _ => l, ?_, inPoly_const r l⟩
  intro h
  have := congrFun h (Classical.arbitrary E)
  simp at this
  omega

end Principia.MathDB.P374957
