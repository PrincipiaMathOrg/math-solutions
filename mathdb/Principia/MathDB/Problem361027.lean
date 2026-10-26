/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #361027 — signed edge colouring of two cliques joined by an edge (definitions)

MathDB open problem #361027, Conjecture 26 of Janczewski–Turowski–Wróblewski.  Let `G_n` be the
graph obtained from two vertex-disjoint copies of `K_n` by adding one edge between them.  The
conjecture asserts that for **every** signature `σ : E(G_n) → {±1}`,

  `χ'(G_n, σ) = Δ(G_n) = n`.

Mathlib has no signed graphs and no edge colouring of any kind, so this module builds the
definitions before any of the mathematics.  It contains the colour set, the graph, its maximum
degree, and the lower bound `χ' ≥ Δ`.  **It does not claim the conjecture**; the construction
(Walecki decompositions, then the colouring) is built in later work.

## The conventions, which are the source's

A signed `k`-edge-colouring assigns a colour to every **incidence** `(u : uv)`, not to every edge,
from the set

  `M k = {0, ±1, …, ±ℓ}` if `k = 2ℓ+1`,   `M k = {±1, …, ±ℓ}` if `k = 2ℓ`,

which has exactly `k` elements either way.  The two incidences of an edge are tied by

  `f(u : uv) = -σ(uv) · f(v : uv)`,

and the colours at incidences sharing a vertex must be distinct.  Note the balance condition means
a colour and its negative are *not* interchangeable: which of `±j` sits at which end is forced by
the sign, and this is exactly what makes the problem depend on `σ` at all.

## Two encoding choices

The vertex set is `Fin (m+1) ⊕ Fin (m+1)` with `n = m + 1`, rather than `Fin n` carrying `0 < n`
alongside, so the joining vertices are literally `Sum.inl 0` and `Sum.inr 0` and no proof term
travels inside a vertex.  The case `n = 0` is not a case of the conjecture.

The graph is built with `SimpleGraph.fromRel`, which supplies symmetry and irreflexivity, rather
than by giving the structure fields directly — their types are `Std.Symm` and `Std.Irrefl`, which
are classes rather than the plain propositions they resemble, and `intro` will not unfold them.
`G_adj` recovers the intended adjacency, and everything downstream uses that rather than the
definition.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Int.Interval
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace Principia.MathDB.P361027

open Finset

/-! ### The colour set -/

/-- The source's colour set `M k`, of cardinality `k`: the symmetric interval `[-⌊k/2⌋, ⌊k/2⌋]`,
with `0` removed when `k` is even. -/
def M (k : ℕ) : Finset ℤ :=
  if k % 2 = 1 then Finset.Icc (-((k / 2 : ℕ) : ℤ)) ((k / 2 : ℕ) : ℤ)
  else (Finset.Icc (-((k / 2 : ℕ) : ℤ)) ((k / 2 : ℕ) : ℤ)).erase 0

/-- **`M k` has exactly `k` colours.**  This is the only property of `M` the lower bound uses. -/
theorem M_card (k : ℕ) : (M k).card = k := by
  by_cases hk : k % 2 = 1
  · rw [M, if_pos hk, Int.card_Icc]
    omega
  · have h0 : (0 : ℤ) ∈ Finset.Icc (-((k / 2 : ℕ) : ℤ)) ((k / 2 : ℕ) : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [M, if_neg hk, Finset.card_erase_of_mem h0, Int.card_Icc]
    omega

/-! ### The graph -/

/-- Adjacency of `G_n` for `n = m + 1`: each copy of `Fin (m+1)` is a clique, and the two vertices
`0` are joined. -/
def Gadj (m : ℕ) : (Fin (m + 1) ⊕ Fin (m + 1)) → (Fin (m + 1) ⊕ Fin (m + 1)) → Prop
  | Sum.inl a, Sum.inl b => a ≠ b
  | Sum.inr a, Sum.inr b => a ≠ b
  | Sum.inl a, Sum.inr b => a = 0 ∧ b = 0
  | Sum.inr a, Sum.inl b => a = 0 ∧ b = 0

instance (m : ℕ) : DecidableRel (Gadj m) := by
  intro a b
  cases a <;> cases b <;> · unfold Gadj; infer_instance

theorem Gadj_symm (m : ℕ) : ∀ a b : Fin (m + 1) ⊕ Fin (m + 1), Gadj m a b → Gadj m b a := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact Ne.symm h
    | inr b => exact ⟨h.2, h.1⟩
  | inr a => cases b with
    | inl b => exact ⟨h.2, h.1⟩
    | inr b => exact Ne.symm h

theorem Gadj_ne (m : ℕ) : ∀ a b : Fin (m + 1) ⊕ Fin (m + 1), Gadj m a b → a ≠ b := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact fun hab => h (Sum.inl_injective hab)
    | inr b => exact fun hab => by simp at hab
  | inr a => cases b with
    | inl b => exact fun hab => by simp at hab
    | inr b => exact fun hab => h (Sum.inr_injective hab)

/-- `G_n` for `n = m + 1`: two disjoint copies of `K_{m+1}` joined by one edge. -/
def G (m : ℕ) : SimpleGraph (Fin (m + 1) ⊕ Fin (m + 1)) := SimpleGraph.fromRel (Gadj m)

/-- The adjacency of `G m` is `Gadj m`.  `fromRel` symmetrises and removes loops, and `Gadj` is
already symmetric and loop-free, so nothing is lost. -/
theorem G_adj (m : ℕ) (a b : Fin (m + 1) ⊕ Fin (m + 1)) : (G m).Adj a b ↔ Gadj m a b := by
  rw [G, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact Gadj_symm m b a h
  · intro h
    exact ⟨Gadj_ne m a b h, Or.inl h⟩

instance (m : ℕ) : DecidableRel (G m).Adj :=
  fun a b => decidable_of_iff _ (G_adj m a b).symm

/-! ### Degrees

Computed from the neighbour Finsets rather than from `∑ w, if Adj v w then 1 else 0`.  The sum
form drags the adjacency's `Decidable` instance through every rewrite, and the mismatches surface
as "typeclass instance problem is stuck" and "motive is not type correct" — errors that name the
rewrite rather than the instance.  An explicit Finset has one decidability obligation, on
`DecidableEq (Fin (m+1))`, which is canonical. -/

theorem neighborFinset_inl (m : ℕ) (a : Fin (m + 1)) :
    (G m).neighborFinset (Sum.inl a)
      = ((Finset.univ.erase a).image Sum.inl)
        ∪ (if a = 0 then {Sum.inr (0 : Fin (m + 1))} else ∅) := by
  ext w
  rcases w with b | b <;> by_cases ha : a = 0 <;>
    simp [SimpleGraph.mem_neighborFinset, G_adj, Gadj, ha, eq_comm]

theorem neighborFinset_inr (m : ℕ) (a : Fin (m + 1)) :
    (G m).neighborFinset (Sum.inr a)
      = ((Finset.univ.erase a).image Sum.inr)
        ∪ (if a = 0 then {Sum.inl (0 : Fin (m + 1))} else ∅) := by
  ext w
  rcases w with b | b <;> by_cases ha : a = 0 <;>
    simp [SimpleGraph.mem_neighborFinset, G_adj, Gadj, ha, eq_comm]

theorem degree_inl (m : ℕ) (a : Fin (m + 1)) :
    (G m).degree (Sum.inl a) = m + (if a = 0 then 1 else 0) := by
  have hd : (G m).degree (Sum.inl a) = ((G m).neighborFinset (Sum.inl a)).card := rfl
  have hdisj : Disjoint ((Finset.univ.erase a).image Sum.inl)
      (if a = 0 then ({Sum.inr (0 : Fin (m + 1))} : Finset (Fin (m + 1) ⊕ Fin (m + 1)))
        else ∅) := by
    by_cases ha : a = 0 <;> simp [ha, Finset.disjoint_left]
  rw [hd, neighborFinset_inl, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  by_cases ha : a = 0 <;> simp [ha]

theorem degree_inr (m : ℕ) (a : Fin (m + 1)) :
    (G m).degree (Sum.inr a) = m + (if a = 0 then 1 else 0) := by
  have hd : (G m).degree (Sum.inr a) = ((G m).neighborFinset (Sum.inr a)).card := rfl
  have hdisj : Disjoint ((Finset.univ.erase a).image Sum.inr)
      (if a = 0 then ({Sum.inl (0 : Fin (m + 1))} : Finset (Fin (m + 1) ⊕ Fin (m + 1)))
        else ∅) := by
    by_cases ha : a = 0 <;> simp [ha, Finset.disjoint_left]
  rw [hd, neighborFinset_inr, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inr_injective,
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  by_cases ha : a = 0 <;> simp [ha]

/-- **The joining vertex has degree `n = m + 1`.** -/
theorem degree_inl_zero (m : ℕ) : (G m).degree (Sum.inl 0) = m + 1 := by
  rw [degree_inl]
  simp

/-- Every vertex has degree at most `n = m + 1`. -/
theorem degree_le (m : ℕ) (v : Fin (m + 1) ⊕ Fin (m + 1)) : (G m).degree v ≤ m + 1 := by
  rcases v with a | a
  · rw [degree_inl]
    by_cases ha : a = 0 <;> simp [ha]
  · rw [degree_inr]
    by_cases ha : a = 0 <;> simp [ha]

/-- **`Δ(G_n) = n`.** -/
theorem maxDegree_eq (m : ℕ) : (G m).maxDegree = m + 1 := by
  refine le_antisymm (SimpleGraph.maxDegree_le_of_forall_degree_le _ _ (degree_le m)) ?_
  -- Rewriting `m + 1` BACKWARDS here builds a bad motive: `m + 1` also occurs in the type
  -- `Fin (m + 1)`, so abstracting it breaks `G m`.  Rewrite forwards, in the hypothesis.
  have h := SimpleGraph.degree_le_maxDegree (G m) (Sum.inl 0)
  rwa [degree_inl_zero] at h

/-! ### Signed colourings -/

/-- A signature assigns `±1` to every edge, symmetrically. -/
structure IsSignature {W : Type*} (Gr : SimpleGraph W) (s : W → W → ℤ) : Prop where
  symm : ∀ u v, s u v = s v u
  sign : ∀ u v, Gr.Adj u v → s u v = 1 ∨ s u v = -1

/-- A signed `k`-edge-colouring: a colour on every **incidence**, drawn from `M k`, with the two
incidences of an edge tied by the signature, and distinct colours at incidences sharing a vertex. -/
structure SignedColouring {W : Type*} (Gr : SimpleGraph W) (s : W → W → ℤ) (k : ℕ) where
  col : W → W → ℤ
  mem : ∀ u v, Gr.Adj u v → col u v ∈ M k
  bal : ∀ u v, Gr.Adj u v → col u v = -(s u v) * col v u
  proper : ∀ u v w, Gr.Adj u v → Gr.Adj u w → v ≠ w → col u v ≠ col u w

/-- The signed chromatic index. -/
noncomputable def chi {W : Type*} (Gr : SimpleGraph W) (s : W → W → ℤ) : ℕ :=
  sInf {k : ℕ | Nonempty (SignedColouring Gr s k)}

/-! ### The lower bound -/

/-- **A vertex of degree `d` forces `d ≤ k`.**  Its `d` incidences carry distinct colours from
`M k`, and `M k` has `k` elements. -/
theorem degree_le_of_colouring {W : Type*} [Fintype W] {Gr : SimpleGraph W}
    [DecidableRel Gr.Adj] {s : W → W → ℤ} {k : ℕ} (c : SignedColouring Gr s k) (v : W) :
    Gr.degree v ≤ k := by
  have hd : Gr.degree v = (Gr.neighborFinset v).card := rfl
  rw [hd, ← M_card k]
  refine Finset.card_le_card_of_injOn (fun w => c.col v w) ?_ ?_
  · intro w hw
    exact c.mem v w ((Gr.mem_neighborFinset v w).mp hw)
  · intro w1 h1 w2 h2 he
    by_contra hne
    exact c.proper v w1 w2 ((Gr.mem_neighborFinset v w1).mp h1)
      ((Gr.mem_neighborFinset v w2).mp h2) hne he

/-- **`χ'(G_n, σ) ≥ n` for every signature**, because the joining vertex has degree `n`.  This is
the half of the conjecture that needs no construction. -/
theorem n_le_of_colouring (m : ℕ)
    {s : (Fin (m + 1) ⊕ Fin (m + 1)) → (Fin (m + 1) ⊕ Fin (m + 1)) → ℤ} {k : ℕ}
    (c : SignedColouring (G m) s k) : m + 1 ≤ k := by
  have h := degree_le_of_colouring c (Sum.inl 0)
  rwa [degree_inl_zero] at h

/-! ### The Walecki vertex sequence

The source's Hamilton cycle `C_i = (∞, i, i-1, i+1, i-2, i+2, …, i-(m-1), i+(m-1), i-m, ∞)` on
`{∞} ∪ ZMod (2m)`, with `∞` deleted, is the vertex sequence

  `w i 0 = i`,  `w i 1 = i-1`,  `w i 2 = i+1`,  `w i 3 = i-2`,  …,  `w i (2m-1) = i-m`,

that is `w i (2j) = i + j` and `w i (2j+1) = i - (j+1)`.

Two facts drive everything.  The sequence is injective on `t < 2m`, so each `P_i` really is a
path; and consecutive vertices have **endpoint sum** `2i - 1` when the first index is even and
`2i` when it is odd.  The endpoint sum is what separates the two families of edges and, in the
next stage, lets an edge be traced back to the unique path carrying it.

Note that Hamiltonicity is never needed downstream.  Each vertex has degree `2m-1`, sits on each
of the `m` paths with local degree `0`, `1` or `2`, and the only way `m` terms from `{0,1,2}` sum
to `2m-1` is one `1` and `m-1` twos — so "endpoint of exactly one path, internal on the rest"
falls out of the edge partition and degree counting alone. -/

namespace Walecki

/-- Casting is injective below the modulus.  Used to turn an equation between vertices back into
an equation between the natural-number indices that produced them. -/
theorem cast_inj (m : ℕ) {a b : ℕ} (ha : a < 2 * m) (hb : b < 2 * m)
    (h : (a : ZMod (2 * m)) = (b : ZMod (2 * m))) : a = b := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  rw [← ZMod.val_cast_of_lt ha, ← ZMod.val_cast_of_lt hb, h]

/-- A nonzero natural below the modulus does not cast to zero. -/
theorem cast_ne_zero (m : ℕ) {a : ℕ} (h1 : 0 < a) (h2 : a < 2 * m) :
    ((a : ℕ) : ZMod (2 * m)) ≠ 0 := by
  intro h
  have hdvd := (ZMod.natCast_eq_zero_iff a (2 * m)).mp h
  have := Nat.le_of_dvd h1 hdvd
  omega

/-- The `t`-th vertex of the `i`-th Walecki path. -/
def w (m : ℕ) (i : ZMod (2 * m)) (t : ℕ) : ZMod (2 * m) :=
  if t % 2 = 0 then i + ((t / 2 : ℕ) : ZMod (2 * m))
  else i - (((t / 2 : ℕ) + 1 : ℕ) : ZMod (2 * m))

theorem w_even (m : ℕ) (i : ZMod (2 * m)) (j : ℕ) :
    w m i (2 * j) = i + ((j : ℕ) : ZMod (2 * m)) := by
  have h1 : 2 * j % 2 = 0 := by omega
  have h2 : 2 * j / 2 = j := by omega
  rw [w, if_pos h1, h2]

theorem w_odd (m : ℕ) (i : ZMod (2 * m)) (j : ℕ) :
    w m i (2 * j + 1) = i - ((j + 1 : ℕ) : ZMod (2 * m)) := by
  have h1 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  rw [w, if_neg h1, h2]

/-- **Each Walecki path is a path**: the vertex sequence is injective on `t < 2m`.

The four cases are the four parities.  Like parities cancel `i` and reduce to injectivity of the
cast; unlike parities give `j + j' + 1 ≡ 0 (mod 2m)` with `1 ≤ j + j' + 1 ≤ 2m - 1`, which is
impossible.  That is the whole content: the "up" half of the zig-zag and the "down" half occupy
disjoint residues. -/
theorem w_inj (m : ℕ) (i : ZMod (2 * m)) {t t' : ℕ} (ht : t < 2 * m) (ht' : t' < 2 * m)
    (h : w m i t = w m i t') : t = t' := by
  rcases Nat.even_or_odd t with he | ho
  · obtain ⟨j, hj⟩ := he
    have hjt : t = 2 * j := by omega
    subst hjt
    rcases Nat.even_or_odd t' with he' | ho'
    · obtain ⟨j', hj'⟩ := he'
      have hjt' : t' = 2 * j' := by omega
      subst hjt'
      rw [w_even, w_even] at h
      have hc : ((j : ℕ) : ZMod (2 * m)) = ((j' : ℕ) : ZMod (2 * m)) := by
        linear_combination h
      have := cast_inj m (by omega : j < 2 * m) (by omega : j' < 2 * m) hc
      omega
    · obtain ⟨j', hj'⟩ := ho'
      have hjt' : t' = 2 * j' + 1 := by omega
      subst hjt'
      exfalso
      rw [w_even, w_odd] at h
      refine cast_ne_zero m (a := j + j' + 1) (by omega) (by omega) ?_
      push_cast
      push_cast at h
      linear_combination h
  · obtain ⟨j, hj⟩ := ho
    have hjt : t = 2 * j + 1 := by omega
    subst hjt
    rcases Nat.even_or_odd t' with he' | ho'
    · obtain ⟨j', hj'⟩ := he'
      have hjt' : t' = 2 * j' := by omega
      subst hjt'
      exfalso
      rw [w_odd, w_even] at h
      refine cast_ne_zero m (a := j + j' + 1) (by omega) (by omega) ?_
      push_cast
      push_cast at h
      linear_combination -h
    · obtain ⟨j', hj'⟩ := ho'
      have hjt' : t' = 2 * j' + 1 := by omega
      subst hjt'
      rw [w_odd, w_odd] at h
      have hc : ((j + 1 : ℕ) : ZMod (2 * m)) = ((j' + 1 : ℕ) : ZMod (2 * m)) := by
        linear_combination -h
      have := cast_inj m (by omega : j + 1 < 2 * m) (by omega : j' + 1 < 2 * m) hc
      omega

/-- **Endpoint sum, even position.**  The edge `{w i (2j), w i (2j+1)}` has endpoint sum `2i - 1`,
which is odd. -/
theorem sum_even (m : ℕ) (i : ZMod (2 * m)) (j : ℕ) :
    w m i (2 * j) + w m i (2 * j + 1) = 2 * i - 1 := by
  rw [w_even, w_odd]
  push_cast
  ring

/-- **Endpoint sum, odd position.**  The edge `{w i (2j+1), w i (2j+2)}` has endpoint sum `2i`,
which is even. -/
theorem sum_odd (m : ℕ) (i : ZMod (2 * m)) (j : ℕ) :
    w m i (2 * j + 1) + w m i (2 * j + 2) = 2 * i := by
  have h : 2 * j + 2 = 2 * (j + 1) := by ring
  rw [h, w_odd, w_even]
  push_cast
  ring

end Walecki

/-! ### The Walecki edges, and why no two coincide

The `p`-th path contributes the edges `{w p t, w p (t+1)}` for `t + 1 < 2m`, so `m` paths
contribute `m(2m-1)` edges in all — exactly `|E(K_{2m})|`.  Injectivity of `(p, t) ↦ edge` is
therefore the whole decomposition: surjectivity is then pure counting.

The proof separates the two indices.  The **endpoint sum** is `2p - 1` from an even position and
`2p` from an odd one, and it is invariant under swapping the ends of the edge, so it survives the
passage to `Sym2`.  Matching sums forces `p = p'` — and in the mixed-parity case forces
`2(p - p') = 1`, which multiplied by `m` gives `m = 0` in `ZMod (2m)`, impossible for `m ≥ 1`.
That last step needs no parity homomorphism: `2m = 0` is all the arithmetic involved.

With `p` pinned, `t` follows from injectivity of the vertex sequence alone.  Either the two edges
agree end-for-end, giving `t = t'`, or they agree crosswise, giving `t = t' + 1` and `t + 1 = t'`
at once. -/

namespace Walecki

/-- The `t`-th edge of the `p`-th Walecki path, as an unordered pair. -/
def edge (m p t : ℕ) : Sym2 (ZMod (2 * m)) :=
  s(w m (p : ZMod (2 * m)) t, w m (p : ZMod (2 * m)) (t + 1))

/-- The endpoint sum survives the passage to an unordered pair. -/
theorem sum_of_eq {A : Type*} [AddCommMonoid A] {a b c d : A} (h : s(a, b) = s(c, d)) :
    a + b = c + d := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact add_comm _ _

/-- `2m = 0` in `ZMod (2m)`, in the form the cancellation below needs. -/
theorem two_mul_cast (m : ℕ) : (2 : ZMod (2 * m)) * ((m : ℕ) : ZMod (2 * m)) = 0 := by
  have h : (2 : ZMod (2 * m)) * ((m : ℕ) : ZMod (2 * m)) = ((2 * m : ℕ) : ZMod (2 * m)) := by
    push_cast
    ring
  rw [h, ZMod.natCast_self]

/-- **The path index is determined by the endpoint sum.**  Both edges even-positioned, or both
odd-positioned. -/
theorem index_eq (m : ℕ) {p p' : ℕ} (hp : p < m) (hp' : p' < m)
    (h : (2 : ZMod (2 * m)) * ((p : ℕ) : ZMod (2 * m))
      = (2 : ZMod (2 * m)) * ((p' : ℕ) : ZMod (2 * m))) : p = p' := by
  have hc : ((2 * p : ℕ) : ZMod (2 * m)) = ((2 * p' : ℕ) : ZMod (2 * m)) := by
    push_cast
    linear_combination h
  have := cast_inj m (by omega : 2 * p < 2 * m) (by omega : 2 * p' < 2 * m) hc
  omega

/-- **Mixed parities are impossible.**  `2p - 1 = 2p'` would give `m = 0` in `ZMod (2m)`. -/
theorem mixed_absurd (m : ℕ) (hm : 0 < m) {p p' : ℕ}
    (h : (2 : ZMod (2 * m)) * ((p : ℕ) : ZMod (2 * m)) - 1
      = (2 : ZMod (2 * m)) * ((p' : ℕ) : ZMod (2 * m))) : False := by
  have hz := two_mul_cast m
  have hm0 : ((m : ℕ) : ZMod (2 * m)) = 0 := by
    linear_combination (-((m : ℕ) : ZMod (2 * m))) * h
      + (((p : ℕ) : ZMod (2 * m)) - ((p' : ℕ) : ZMod (2 * m))) * hz
  have hdvd := (ZMod.natCast_eq_zero_iff m (2 * m)).mp hm0
  have := Nat.le_of_dvd hm hdvd
  omega

/-- **Distinct `(p, t)` give distinct edges.**  With `m` paths of `2m-1` edges each and
`m(2m-1) = |E(K_{2m})|`, this is the Walecki decomposition. -/
theorem edge_inj (m : ℕ) (hm : 0 < m) {p t p' t' : ℕ} (hp : p < m) (hp' : p' < m)
    (ht : t + 1 < 2 * m) (ht' : t' + 1 < 2 * m) (h : edge m p t = edge m p' t') :
    p = p' ∧ t = t' := by
  have hs := sum_of_eq h
  have hpp : p = p' := by
    rcases Nat.even_or_odd t with he | ho
    · obtain ⟨j, hj⟩ := he
      have hjt : t = 2 * j := by omega
      subst hjt
      rw [sum_even] at hs
      rcases Nat.even_or_odd t' with he' | ho'
      · obtain ⟨j', hj'⟩ := he'
        have hjt' : t' = 2 * j' := by omega
        subst hjt'
        rw [sum_even] at hs
        refine index_eq m hp hp' ?_
        linear_combination hs
      · obtain ⟨j', hj'⟩ := ho'
        have hjt' : t' = 2 * j' + 1 := by omega
        subst hjt'
        have hstep : 2 * j' + 1 + 1 = 2 * j' + 2 := by ring
        rw [hstep, sum_odd] at hs
        exact absurd (by linear_combination hs :
          (2 : ZMod (2 * m)) * ((p : ℕ) : ZMod (2 * m)) - 1
            = (2 : ZMod (2 * m)) * ((p' : ℕ) : ZMod (2 * m))) (fun hx => mixed_absurd m hm hx)
    · obtain ⟨j, hj⟩ := ho
      have hjt : t = 2 * j + 1 := by omega
      subst hjt
      have hstep : 2 * j + 1 + 1 = 2 * j + 2 := by ring
      rw [hstep, sum_odd] at hs
      rcases Nat.even_or_odd t' with he' | ho'
      · obtain ⟨j', hj'⟩ := he'
        have hjt' : t' = 2 * j' := by omega
        subst hjt'
        rw [sum_even] at hs
        exact absurd (by linear_combination -hs :
          (2 : ZMod (2 * m)) * ((p' : ℕ) : ZMod (2 * m)) - 1
            = (2 : ZMod (2 * m)) * ((p : ℕ) : ZMod (2 * m))) (fun hx => mixed_absurd m hm hx)
      · obtain ⟨j', hj'⟩ := ho'
        have hjt' : t' = 2 * j' + 1 := by omega
        subst hjt'
        have hstep' : 2 * j' + 1 + 1 = 2 * j' + 2 := by ring
        rw [hstep', sum_odd] at hs
        refine index_eq m hp hp' ?_
        linear_combination hs
  subst hpp
  refine ⟨rfl, ?_⟩
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact w_inj m _ (by omega) (by omega) h1
  · have e1 := w_inj m _ (by omega : t < 2 * m) (by omega : t' + 1 < 2 * m) h1
    have e2 := w_inj m _ (by omega : t + 1 < 2 * m) (by omega : t' < 2 * m) h2
    omega

end Walecki

/-! ### Hamiltonicity is free, and each vertex ends exactly one path

`w p ·` is injective on `t < 2m` into a type of exactly `2m` elements, so it is a **bijection** —
each path visits every vertex exactly once, with no separate argument.

The endpoints of `P_p` are `w p 0 = p` and `w p (2m-1) = p - m`.  So `v` ends `P_p` exactly when
`p = v` or `p = v + m` as elements of `ZMod (2m)`, and of the two natural representatives `v.val`
and `v.val ± m` precisely one lies below `m`.  Hence **every vertex is an endpoint of exactly one
path** — the fact the colouring argument runs on, obtained directly rather than by counting local
degrees. -/

namespace Walecki

theorem w_zero (m : ℕ) (i : ZMod (2 * m)) : w m i 0 = i := by
  have h : (0 : ℕ) = 2 * 0 := by ring
  rw [h, w_even]
  simp

theorem w_last (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m)) :
    w m i (2 * m - 1) = i - ((m : ℕ) : ZMod (2 * m)) := by
  have h : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have h2 : m - 1 + 1 = m := by omega
  rw [h, w_odd, h2]

/-- **Each Walecki path is Hamiltonian**, for free: an injection between finite types of equal
cardinality is a bijection. -/
theorem w_bij (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m)) :
    Function.Bijective (fun t : Fin (2 * m) => w m i (t : ℕ)) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro t t' h
    exact Fin.ext (w_inj m i t.isLt t'.isLt h)
  · simp [ZMod.card]

/-- Every vertex occurs on every path. -/
theorem w_surj (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m)) (v : ZMod (2 * m)) :
    ∃ t : ℕ, t < 2 * m ∧ w m i t = v := by
  obtain ⟨t, ht⟩ := (w_bij m hm i).2 v
  exact ⟨(t : ℕ), t.isLt, ht⟩

theorem val_cast (m : ℕ) (hm : 0 < m) (v : ZMod (2 * m)) :
    ((v.val : ℕ) : ZMod (2 * m)) = v := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  exact ZMod.natCast_rightInverse v

/-- The index of the unique path that `v` ends. -/
def pathOf (m : ℕ) (v : ZMod (2 * m)) : ℕ := if v.val < m then v.val else v.val - m

theorem pathOf_lt (m : ℕ) (hm : 0 < m) (v : ZMod (2 * m)) : pathOf m v < m := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hv := ZMod.val_lt v
  rw [pathOf]
  split <;> omega

/-- **`v` really does end the path `pathOf m v`.** -/
theorem endpoint_pathOf (m : ℕ) (hm : 0 < m) (v : ZMod (2 * m)) :
    w m ((pathOf m v : ℕ) : ZMod (2 * m)) 0 = v
      ∨ w m ((pathOf m v : ℕ) : ZMod (2 * m)) (2 * m - 1) = v := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hv := ZMod.val_lt v
  rw [w_zero, w_last m hm, pathOf]
  by_cases hlt : v.val < m
  · left
    rw [if_pos hlt, val_cast m hm]
  · right
    rw [if_neg hlt]
    have hsub : ((v.val - m : ℕ) : ZMod (2 * m))
        = ((v.val : ℕ) : ZMod (2 * m)) - ((m : ℕ) : ZMod (2 * m)) := by
      have : m ≤ v.val := by omega
      rw [Nat.cast_sub this]
    rw [hsub, val_cast m hm]
    have hz := two_mul_cast m
    linear_combination -hz

/-- **No other path is ended by `v`.** -/
theorem endpoint_unique (m : ℕ) (hm : 0 < m) (v : ZMod (2 * m)) {p : ℕ} (hp : p < m)
    (h : w m ((p : ℕ) : ZMod (2 * m)) 0 = v
      ∨ w m ((p : ℕ) : ZMod (2 * m)) (2 * m - 1) = v) : p = pathOf m v := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  rw [w_zero, w_last m hm] at h
  rcases h with h1 | h2
  · have hval : v.val = p := by
      rw [← h1, ZMod.val_cast_of_lt (by omega : p < 2 * m)]
    rw [pathOf, if_pos (by omega : v.val < m), hval]
  · have hcast : ((p + m : ℕ) : ZMod (2 * m)) = v := by
      have hz := two_mul_cast m
      push_cast
      linear_combination h2 + hz
    have hval : v.val = p + m := by
      rw [← hcast, ZMod.val_cast_of_lt (by omega : p + m < 2 * m)]
    rw [pathOf, if_neg (by omega : ¬ v.val < m), hval]
    omega

end Walecki

/-! ### The decomposition

`m` paths of `2m-1` edges is `m(2m-1)` edges, and `K_{2m}` has `(2m choose 2) = m(2m-1)` of them.
Injectivity of `(p, t) ↦ edge` therefore forces **surjectivity**, by cardinality alone: every
unordered pair of distinct vertices is a Walecki edge, at exactly one path and one position.

This is the point of doing injectivity first.  The source verifies surjectivity directly, by
checking that for each endpoint sum the listed pairs exhaust the pairs with that sum; counting
gets the same conclusion from work already done.

The statement is phrased on a pair `u ≠ v` rather than on `edgeFinset`.  `edgeFinset` carries a
`Fintype ↑⊤.edgeSet` obligation that must be discharged when the STATEMENT is elaborated, and the
instances it needs (`NeZero (2m)`, and decidability of `⊤`'s adjacency) are exactly what a `haveI`
inside the proof arrives too late to supply.  Keeping the complete graph internal costs nothing
and keeps the interface free of instance arguments. -/

namespace Walecki

/-- **Every pair of distinct vertices is a Walecki edge.**  Injectivity plus equal cardinality. -/
theorem edge_surj (m : ℕ) (hm : 0 < m) {u v : ZMod (2 * m)} (huv : u ≠ v) :
    ∃ p t : ℕ, p < m ∧ t + 1 < 2 * m ∧ edge m p t = s(u, v) := by
  -- No `classical`, and no hand-rolled `DecidableRel` for the complete graph: Mathlib's
  -- `SimpleGraph.Top.adjDecidable` is the instance its own cardinality lemma was elaborated
  -- with, and supplying a competing one makes the two `edgeFinset`s different TERMS -- so the
  -- rewrite fails to find a pattern that is visibly the whole goal.
  haveI : NeZero (2 * m) := ⟨by omega⟩
  -- the target: the edge set of the complete graph, of size `m(2m-1)`
  have hcard_edges : ((⊤ : SimpleGraph (ZMod (2 * m))).edgeFinset).card = m * (2 * m - 1) := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, ZMod.card, Nat.choose_two_right]
    have h : 2 * m * (2 * m - 1) = 2 * (m * (2 * m - 1)) := by ring
    rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  -- every Walecki edge lands there: its two ends are distinct
  have hedge_mem : ∀ p t : ℕ, t + 1 < 2 * m →
      edge m p t ∈ (⊤ : SimpleGraph (ZMod (2 * m))).edgeFinset := by
    intro p t ht
    rw [edge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    intro hcon
    have := w_inj m ((p : ℕ) : ZMod (2 * m)) (by omega : t < 2 * m)
      (by omega : t + 1 < 2 * m) hcon
    omega
  set S : Finset (ℕ × ℕ) := (Finset.range m) ×ˢ (Finset.range (2 * m - 1)) with hS
  have hmem : ∀ a : ℕ × ℕ, a ∈ S → a.1 < m ∧ a.2 < 2 * m - 1 := by
    intro a ha
    rw [hS, Finset.mem_product, Finset.mem_range, Finset.mem_range] at ha
    exact ha
  have hScard : S.card = m * (2 * m - 1) := by
    rw [hS, Finset.card_product, Finset.card_range, Finset.card_range]
  have hmaps : ∀ (a : ℕ × ℕ) (_ : a ∈ S),
      edge m a.1 a.2 ∈ (⊤ : SimpleGraph (ZMod (2 * m))).edgeFinset := by
    intro a ha
    exact hedge_mem a.1 a.2 (by have := hmem a ha; omega)
  have hinj : ∀ (a₁ a₂ : ℕ × ℕ) (_ : a₁ ∈ S) (_ : a₂ ∈ S),
      edge m a₁.1 a₁.2 = edge m a₂.1 a₂.2 → a₁ = a₂ := by
    intro a₁ a₂ h₁ h₂ heq
    have k₁ := hmem a₁ h₁
    have k₂ := hmem a₂ h₂
    obtain ⟨hp, ht⟩ := edge_inj m hm k₁.1 k₂.1 (by omega) (by omega) heq
    exact Prod.ext hp ht
  have hcard : ((⊤ : SimpleGraph (ZMod (2 * m))).edgeFinset).card ≤ S.card := by
    rw [hScard, hcard_edges]
  have htarget : s(u, v) ∈ (⊤ : SimpleGraph (ZMod (2 * m))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    exact huv
  obtain ⟨a, ha, hae⟩ :=
    Finset.surj_on_of_inj_on_of_card_le (fun (a : ℕ × ℕ) (_ : a ∈ S) => edge m a.1 a.2)
      hmaps hinj hcard s(u, v) htarget
  have k := hmem a ha
  exact ⟨a.1, a.2, k.1, by omega, hae.symm⟩

end Walecki

/-! ### Colouring one path

A path can be coloured with a single pair `{±c}` **whatever the signs on its edges** — this is the
observation the source opens with, and it is why the construction goes through paths rather than
matchings.  Fix the colour at the first incidence and propagate: the balance condition determines
the colour at the far end of each edge, and the properness condition at an internal vertex then
determines the colour at the near end of the next.

Concretely, carry a sign `sgn p t ∈ {±1}` with `sgn p 0 = 1` and `sgn p (t+1) = sgn p t · σ(e_t)`.
The incidence at `w p t` pointing along `e_t` gets `sgn p t · c`, and the incidence at
`w p (t+1)` pointing back gets `-sgn p (t+1) · c`.

Two facts fall out, and they are the only two the assembly needs.  Balance holds by construction,
using nothing about `σ` beyond `σ² = 1`.  And at an **internal** vertex the two incidences are
`sgn p (t+1) · c` and `-sgn p (t+1) · c` — negatives, hence distinct, hence proper — with no
reference to the signs at all.  The signature is absorbed entirely into `sgn`. -/

namespace Walecki

/-- The sign carried along path `p` up to position `t`. -/
def sgn (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (p : ℕ) : ℕ → ℤ
  | 0 => 1
  | (t + 1) => sgn m sg p t * sg (w m ((p : ℕ) : ZMod (2 * m)) t)
      (w m ((p : ℕ) : ZMod (2 * m)) (t + 1))

theorem sgn_zero (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (p : ℕ) : sgn m sg p 0 = 1 := rfl

theorem sgn_succ (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (p t : ℕ) :
    sgn m sg p (t + 1) = sgn m sg p t * sg (w m ((p : ℕ) : ZMod (2 * m)) t)
      (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)) := rfl

/-- The carried sign is itself a sign. -/
theorem sgn_eq_one_or (m : ℕ) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) (p t : ℕ) :
    sgn m sg p t = 1 ∨ sgn m sg p t = -1 := by
  induction t with
  | zero => left; rfl
  | succ t ih =>
    rw [sgn_succ]
    rcases ih with h1 | h1 <;>
      rcases hsg (w m ((p : ℕ) : ZMod (2 * m)) t) (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)) with
        h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- Colour of the incidence at `w p t` pointing along the edge to `w p (t+1)`. -/
def colFwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (p t : ℕ) : ℤ :=
  sgn m sg p t * ((p : ℤ) + 1)

/-- Colour of the incidence at `w p (t+1)` pointing back along the same edge. -/
def colBwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (p t : ℕ) : ℤ :=
  -(sgn m sg p (t + 1)) * ((p : ℤ) + 1)

/-- **The balance condition holds by construction.**  Only `σ² = 1` is used. -/
theorem colFwd_eq (m : ℕ) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) (p t : ℕ) :
    colFwd m sg p t
      = -(sg (w m ((p : ℕ) : ZMod (2 * m)) t) (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)))
        * colBwd m sg p t := by
  rw [colFwd, colBwd, sgn_succ]
  rcases hsg (w m ((p : ℕ) : ZMod (2 * m)) t) (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)) with h | h <;>
    rw [h] <;> ring

/-- **At an internal vertex the two incidences are negatives**, hence distinct.  The signature
does not appear: it has been absorbed into `sgn`. -/
theorem colBwd_eq_neg_colFwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (p t : ℕ) :
    colBwd m sg p t = -(colFwd m sg p (t + 1)) := by
  rw [colBwd, colFwd]
  ring

/-- Membership in the colour set, for an even number of colours. -/
theorem mem_M_two_mul (m : ℕ) (x : ℤ) :
    x ∈ M (2 * m) ↔ -(m : ℤ) ≤ x ∧ x ≤ (m : ℤ) ∧ x ≠ 0 := by
  have h1 : ¬ (2 * m) % 2 = 1 := by omega
  have h2 : 2 * m / 2 = m := by omega
  rw [M, if_neg h1, h2, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hne, hlo, hhi⟩
    exact ⟨hlo, hhi, hne⟩
  · rintro ⟨hlo, hhi, hne⟩
    exact ⟨hne, hlo, hhi⟩

/-- Both incidence colours of a path edge lie in `M (2m)`, with absolute value `p + 1`. -/
theorem colFwd_mem (m : ℕ) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) {p : ℕ} (hp : p < m) (t : ℕ) :
    colFwd m sg p t ∈ M (2 * m) := by
  rw [mem_M_two_mul, colFwd]
  have hple : ((p : ℤ) + 1) ≤ (m : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hp
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rcases sgn_eq_one_or m hsg p t with h | h
  · rw [h]
    exact ⟨by linarith, by linarith, by intro hc; linarith⟩
  · rw [h]
    exact ⟨by linarith, by linarith, by intro hc; linarith⟩

theorem colBwd_mem (m : ℕ) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) {p : ℕ} (hp : p < m) (t : ℕ) :
    colBwd m sg p t ∈ M (2 * m) := by
  rw [mem_M_two_mul, colBwd]
  have hple : ((p : ℤ) + 1) ≤ (m : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hp
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rcases sgn_eq_one_or m hsg p (t + 1) with h | h
  · rw [h]
    exact ⟨by linarith, by linarith, by intro hc; linarith⟩
  · rw [h]
    exact ⟨by linarith, by linarith, by intro hc; linarith⟩

end Walecki

/-! ### From the decomposition to a colouring of the clique

Every pair `u ≠ v` lies on exactly one path at exactly one position, so `locate` can name that
`(path, position)` and `col` can read off the incidence colour.  `locate` is total — junk on the
diagonal — rather than carrying `u ≠ v` as an argument, because a proof-carrying definition would
force every later statement to thread the same proof through.

The one thing that has to be checked rather than assumed is that `locate` does not depend on the
ORDER of `u` and `v`.  `s(u,v)` and `s(v,u)` are propositionally equal but not the same term, so
the two `Classical.choose` calls could in principle land on different witnesses; `locate_symm`
rules that out via uniqueness, and every later argument uses it. -/

namespace Walecki

theorem edge_surj' (m : ℕ) (hm : 0 < m) {u v : ZMod (2 * m)} (huv : u ≠ v) :
    ∃ a : ℕ × ℕ, a.1 < m ∧ a.2 + 1 < 2 * m ∧ edge m a.1 a.2 = s(u, v) := by
  obtain ⟨p, t, hp, ht, he⟩ := edge_surj m hm huv
  exact ⟨(p, t), hp, ht, he⟩

open scoped Classical in
/-- The path index and position carrying the edge `{u, v}`; junk when `u = v`. -/
noncomputable def locate (m : ℕ) (u v : ZMod (2 * m)) : ℕ × ℕ :=
  if h : ∃ a : ℕ × ℕ, a.1 < m ∧ a.2 + 1 < 2 * m ∧ edge m a.1 a.2 = s(u, v) then h.choose
  else (0, 0)

theorem locate_spec (m : ℕ) (hm : 0 < m) {u v : ZMod (2 * m)} (huv : u ≠ v) :
    (locate m u v).1 < m ∧ (locate m u v).2 + 1 < 2 * m
      ∧ edge m (locate m u v).1 (locate m u v).2 = s(u, v) := by
  classical
  have h := edge_surj' m hm huv
  rw [locate, dif_pos h]
  exact h.choose_spec

theorem locate_unique (m : ℕ) (hm : 0 < m) {u v : ZMod (2 * m)} (huv : u ≠ v) {p t : ℕ}
    (hp : p < m) (ht : t + 1 < 2 * m) (he : edge m p t = s(u, v)) : locate m u v = (p, t) := by
  obtain ⟨hp', ht', he'⟩ := locate_spec m hm huv
  have hpair := edge_inj m hm hp' hp ht' ht (by rw [he', he])
  exact Prod.ext hpair.1 hpair.2

/-- **`locate` sees only the unordered pair.** -/
theorem locate_symm (m : ℕ) (hm : 0 < m) {u v : ZMod (2 * m)} (huv : u ≠ v) :
    locate m u v = locate m v u := by
  obtain ⟨hp, ht, he⟩ := locate_spec m hm (Ne.symm huv)
  -- `locate_unique` returns the pair in eta-EXPANDED form, `(x.1, x.2)`, so `.symm` alone leaves
  -- a goal that is only definitionally the one wanted.  `Prod.mk.eta` closes the gap.
  have h := locate_unique m hm huv hp ht (by rw [he, Sym2.eq_swap])
  exact h.trans Prod.mk.eta

open scoped Classical in
/-- The colour of the incidence at `u` along the edge `{u, v}`. -/
noncomputable def col (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) (u v : ZMod (2 * m)) : ℤ :=
  if w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u
  then colFwd m sg (locate m u v).1 (locate m u v).2
  else colBwd m sg (locate m u v).1 (locate m u v).2

theorem col_eq_colFwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) {u v : ZMod (2 * m)}
    (h : w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u) :
    col m sg u v = colFwd m sg (locate m u v).1 (locate m u v).2 := by
  classical
  rw [col, if_pos h]

theorem col_eq_colBwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) {u v : ZMod (2 * m)}
    (h : ¬ w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u) :
    col m sg u v = colBwd m sg (locate m u v).1 (locate m u v).2 := by
  classical
  rw [col, if_neg h]

/-- **Every incidence colour lies in the colour set.** -/
theorem col_mem (m : ℕ) (hm : 0 < m) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) {u v : ZMod (2 * m)} (huv : u ≠ v) :
    col m sg u v ∈ M (2 * m) := by
  classical
  obtain ⟨hp, -, -⟩ := locate_spec m hm huv
  by_cases h : w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u
  · rw [col_eq_colFwd m sg h]
    exact colFwd_mem m hsg hp _
  · rw [col_eq_colBwd m sg h]
    exact colBwd_mem m hsg hp _

/-- The absolute value of an incidence colour is `p + 1`, where `p` is its path index.  This is
what separates colours coming from different paths. -/
theorem col_abs (m : ℕ) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (u v : ZMod (2 * m)) :
    col m sg u v = ((locate m u v).1 : ℤ) + 1 ∨ col m sg u v = -(((locate m u v).1 : ℤ) + 1) := by
  classical
  by_cases h : w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u
  · rw [col_eq_colFwd m sg h, colFwd]
    rcases sgn_eq_one_or m hsg (locate m u v).1 (locate m u v).2 with hs | hs
    · left; rw [hs]; ring
    · right; rw [hs]; ring
  · rw [col_eq_colBwd m sg h, colBwd]
    rcases sgn_eq_one_or m hsg (locate m u v).1 ((locate m u v).2 + 1) with hs | hs
    · right; rw [hs]; ring
    · left; rw [hs]; ring

end Walecki

/-! ### The clique is properly coloured

Two conditions remain for a single copy of `K_{2m}`.

**Balance** is `colFwd_eq` plus bookkeeping: `locate_symm` guarantees `col u v` and `col v u` read
the *same* edge, and `locate_ends` says which end each of them sits at.  When `u` is the far end
the identity comes back multiplied by `-σ`, and `σ² = 1` together with the symmetry of the
signature returns it.

**Properness** splits on whether the two incidences come from the same path.  Different paths give
different absolute values, `p+1` against `p'+1`, so nothing more is needed.  The same path forces
`u` to sit at one position on it, and the two edges must then be the two edges at that position —
one entered, one left — whose colours are negatives of each other.  The degenerate possibility,
that the two edges coincide, is excluded because that would make `v = v'`. -/

namespace Walecki

theorem colFwd_ne_zero (m : ℕ) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (p t : ℕ) : colFwd m sg p t ≠ 0 := by
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rw [colFwd]
  rcases sgn_eq_one_or m hsg p t with h | h
  · rw [h]; intro hc; linarith
  · rw [h]; intro hc; linarith

/-- `col` at a located edge, near end. -/
theorem col_of_loc_fwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) {u v : ZMod (2 * m)}
    {a : ℕ × ℕ} (hloc : locate m u v = a)
    (h : w m ((a.1 : ℕ) : ZMod (2 * m)) a.2 = u) : col m sg u v = colFwd m sg a.1 a.2 := by
  classical
  rw [col, hloc, if_pos h]

/-- `col` at a located edge, far end. -/
theorem col_of_loc_bwd (m : ℕ) (sg : ZMod (2 * m) → ZMod (2 * m) → ℤ) {u v : ZMod (2 * m)}
    {a : ℕ × ℕ} (hloc : locate m u v = a)
    (h : ¬ w m ((a.1 : ℕ) : ZMod (2 * m)) a.2 = u) : col m sg u v = colBwd m sg a.1 a.2 := by
  classical
  rw [col, hloc, if_neg h]

/-- Which end of its edge `u` sits at. -/
theorem locate_ends (m : ℕ) (hm : 0 < m) {u v : ZMod (2 * m)} (huv : u ≠ v) :
    (w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u
        ∧ w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) ((locate m u v).2 + 1) = v)
      ∨ (w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = v
        ∧ w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) ((locate m u v).2 + 1) = u) := by
  obtain ⟨-, -, he⟩ := locate_spec m hm huv
  rw [edge] at he
  exact Sym2.eq_iff.mp he

/-- **The balance condition, on a clique.** -/
theorem col_balance (m : ℕ) (hm : 0 < m) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x)
    {u v : ZMod (2 * m)} (huv : u ≠ v) :
    col m sg u v = -(sg u v) * col m sg v u := by
  have hloc : locate m v u = locate m u v := (locate_symm m hm huv).symm
  rcases locate_ends m hm huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hne : ¬ w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = v := by
      rw [h1]; exact huv
    rw [col_of_loc_fwd m sg rfl h1, col_of_loc_bwd m sg hloc hne]
    have hfe := colFwd_eq m hsg (locate m u v).1 (locate m u v).2
    rw [h1, h2] at hfe
    exact hfe
  · have hne : ¬ w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u := by
      rw [h1]; exact fun hc => huv hc.symm
    rw [col_of_loc_bwd m sg rfl hne, col_of_loc_fwd m sg hloc h1]
    have hfe := colFwd_eq m hsg (locate m u v).1 (locate m u v).2
    rw [h1, h2, hsymm v u] at hfe
    rcases hsg u v with hs | hs
    · rw [hs] at hfe ⊢; linarith
    · rw [hs] at hfe ⊢; linarith

/-- **Properness, on a clique.** -/
theorem col_proper (m : ℕ) (hm : 0 < m) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) {u v v' : ZMod (2 * m)}
    (huv : u ≠ v) (huv' : u ≠ v') (hvv : v ≠ v') : col m sg u v ≠ col m sg u v' := by
  obtain ⟨hpa, hta, hea⟩ := locate_spec m hm huv
  obtain ⟨hpb, htb, heb⟩ := locate_spec m hm huv'
  -- the two edges cannot coincide, or `v = v'`
  have hsame : (locate m u v).1 = (locate m u v').1 → (locate m u v).2 = (locate m u v').2
      → False := by
    intro e1 e2
    have hee : edge m (locate m u v).1 (locate m u v).2
        = edge m (locate m u v').1 (locate m u v').2 := by rw [e1, e2]
    rw [hea, heb] at hee
    rcases Sym2.eq_iff.mp hee with ⟨-, hv2⟩ | ⟨hu2, -⟩
    · exact hvv hv2
    · exact huv' hu2
  by_cases hpp : (locate m u v).1 = (locate m u v').1
  · rcases locate_ends m hm huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases locate_ends m hm huv' with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · -- both near ends: the edges coincide
      exact absurd (w_inj m _ (by omega) (by omega) (by rw [h1, hpp, k1]))
        (fun e => hsame hpp e)
    · -- `u` near on the first, far on the second
      have hidx : (locate m u v).2 = (locate m u v').2 + 1 :=
        w_inj m _ (by omega) (by omega) (by rw [h1, hpp, k2])
      have hne : ¬ w m (((locate m u v').1 : ℕ) : ZMod (2 * m)) (locate m u v').2 = u := by
        rw [k1]; exact fun hc => huv' hc.symm
      rw [col_of_loc_fwd m sg rfl h1, col_of_loc_bwd m sg rfl hne, hpp, hidx,
        colBwd_eq_neg_colFwd]
      have hz := colFwd_ne_zero m hsg (locate m u v').1 ((locate m u v').2 + 1)
      intro hc
      exact hz (by linarith)
    · -- `u` far on the first, near on the second
      have hidx : (locate m u v).2 + 1 = (locate m u v').2 :=
        w_inj m _ (by omega) (by omega) (by rw [h2, hpp, k1])
      have hne : ¬ w m (((locate m u v).1 : ℕ) : ZMod (2 * m)) (locate m u v).2 = u := by
        rw [h1]; exact fun hc => huv hc.symm
      rw [col_of_loc_bwd m sg rfl hne, col_of_loc_fwd m sg rfl k1, ← hpp, ← hidx,
        colBwd_eq_neg_colFwd]
      have hz := colFwd_ne_zero m hsg (locate m u v).1 ((locate m u v).2 + 1)
      intro hc
      exact hz (by linarith)
    · -- both far ends: the edges coincide
      have hidx : (locate m u v).2 + 1 = (locate m u v').2 + 1 :=
        w_inj m _ (by omega) (by omega) (by rw [h2, hpp, k2])
      exact absurd (by omega : (locate m u v).2 = (locate m u v').2) (fun e => hsame hpp e)
  · intro hcon
    rcases col_abs m hsg u v with ha | ha <;> rcases col_abs m hsg u v' with hb | hb <;>
      rw [ha, hb] at hcon <;> omega

end Walecki

end Principia.MathDB.P361027

namespace Principia.MathDB

/-! ### Two tools for the join

Neither is about Walecki, so both are stated for an arbitrary vertex type.

**Flipping a colour class.**  Negating every incidence whose colour has a given absolute value
preserves all three conditions.  This is the source's "reversing all incidence colours on one
path", in the only form the assembly needs — and stated on absolute values rather than on paths it
needs no path structure at all.  It is what supplies the freedom to choose which of `±c` is the
colour missing at a vertex, and hence to satisfy the joining edge's balance condition.

**A colour is always missing.**  A vertex of a clique on `k` vertices has `k-1` neighbours, its
incidence colours are distinct and lie in `M k`, and `|M k| = k`.  So one colour is unused.  Pure
counting; no structure enters. -/

namespace Colouring

/-- The colour set is symmetric. -/
theorem neg_mem_M (k : ℕ) (x : ℤ) (h : x ∈ P361027.M k) : -x ∈ P361027.M k := by
  by_cases hk : k % 2 = 1
  · rw [P361027.M, if_pos hk, Finset.mem_Icc] at h ⊢
    omega
  · rw [P361027.M, if_neg hk, Finset.mem_erase, Finset.mem_Icc] at h ⊢
    omega

/-- Negate every incidence whose colour has absolute value `c`. -/
def flip {V : Type*} (c : ℤ) (f : V → V → ℤ) : V → V → ℤ :=
  fun u v => if |f u v| = c then -(f u v) else f u v

theorem flip_mem {V : Type*} {k : ℕ} {f : V → V → ℤ} (c : ℤ) {u v : V}
    (h : f u v ∈ P361027.M k) : flip c f u v ∈ P361027.M k := by
  rw [flip]
  split
  · exact neg_mem_M k _ h
  · exact h

/-- Flipping preserves the balance condition.  Both ends of an edge have the same absolute value,
because the signature is `±1`, so they flip together or not at all. -/
theorem flip_balance {V : Type*} {f : V → V → ℤ} {sg : V → V → ℤ} (c : ℤ) {u v : V}
    (hsg : sg u v = 1 ∨ sg u v = -1) (h : f u v = -(sg u v) * f v u) :
    flip c f u v = -(sg u v) * flip c f v u := by
  have habs : |f u v| = |f v u| := by
    rcases hsg with hs | hs <;> rw [h, hs] <;> simp
  rw [flip, flip, habs]
  split
  · rw [h]; ring
  · exact h

/-- Flipping preserves properness. -/
theorem flip_proper {V : Type*} {f : V → V → ℤ} (c : ℤ) {u v v' : V}
    (h : f u v ≠ f u v') : flip c f u v ≠ flip c f u v' := by
  rw [flip, flip]
  by_cases h1 : |f u v| = c <;> by_cases h2 : |f u v'| = c
  · rw [if_pos h1, if_pos h2]
    intro hc
    exact h (by linarith)
  · rw [if_pos h1, if_neg h2]
    intro hc
    apply h2
    rw [← hc, abs_neg]
    exact h1
  · rw [if_neg h1, if_pos h2]
    intro hc
    apply h1
    rw [hc, abs_neg]
    exact h2
  · rw [if_neg h1, if_neg h2]
    exact h

/-- **A vertex of a clique on `k` vertices always misses a colour.** -/
theorem exists_missing_colour {V : Type*} [Fintype V] (f : V → V → ℤ) (k : ℕ) (u : V)
    (hcard : Fintype.card V = k)
    (hmem : ∀ v, v ≠ u → f u v ∈ P361027.M k)
    (hproper : ∀ v v', v ≠ u → v' ≠ u → v ≠ v' → f u v ≠ f u v') :
    ∃ c ∈ P361027.M k, ∀ v, v ≠ u → f u v ≠ c := by
  classical
  set T : Finset V := Finset.univ.erase u with hT
  have hTcard : T.card = k - 1 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, hcard]
  have hsub : T.image (fun v => f u v) ⊆ P361027.M k := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact hmem v (Finset.ne_of_mem_erase hv)
  have himg : (T.image (fun v => f u v)).card = k - 1 := by
    rw [Finset.card_image_of_injOn, hTcard]
    intro a ha b hb hab
    by_contra hne
    exact hproper a b (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb) hne hab
  have hk1 : 1 ≤ k := by
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr ⟨u⟩
  have hlt : (T.image (fun v => f u v)).card < (P361027.M k).card := by
    rw [himg, P361027.M_card]
    omega
  obtain ⟨c, hcM, hcni⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, hcM, ?_⟩
  intro v hv hcon
  exact hcni (Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩, hcon⟩)

end Colouring

/-! ### The clique colouring as a bundle, and how to move it

`CliqueColouring V k sg` packages the three conditions on a complete graph.  Bundling them buys
three things the assembly needs and that are awkward as loose lemmas: the even-order construction
becomes a single named object, flipping a colour class becomes an operation on that object, and
**transport along an equivalence** becomes one definition rather than a rewrite at every use.

Transport is what reconciles the two indexings.  The graph's cliques are `Fin (n)` with `n = m+1`,
while the Walecki construction lives on `ZMod (2μ)`.  `ZMod (m+1)` reduces to `Fin (m+1)` — `ZMod`
is defined by cases and `m+1` is a syntactic successor — so the only gap is between `ZMod (m+1)`
and `ZMod (2μ)` when `m + 1 = 2μ`.  That is a propositional equality of naturals, hence a
propositional equality of types via `congrArg ZMod`, hence an `Equiv.cast`.  No `Fin n ≃ ZMod n`
is needed and nothing has to be rebuilt.

Note the signature travels backwards: to colour `V` one transports a colouring of `W` built for
the signature pulled back along `e.symm`. -/

namespace Colouring

/-- A signed `k`-edge-colouring of a complete graph on `V`. -/
structure CliqueColouring (V : Type*) (k : ℕ) (sg : V → V → ℤ) where
  col : V → V → ℤ
  mem : ∀ u v, u ≠ v → col u v ∈ P361027.M k
  bal : ∀ u v, u ≠ v → col u v = -(sg u v) * col v u
  proper : ∀ u v v', u ≠ v → u ≠ v' → v ≠ v' → col u v ≠ col u v'

/-- **Transport along an equivalence of vertex types.** -/
def CliqueColouring.transport {V W : Type*} (e : V ≃ W) {k : ℕ} {sg : V → V → ℤ}
    (c : CliqueColouring W k (fun x y => sg (e.symm x) (e.symm y))) : CliqueColouring V k sg where
  col u v := c.col (e u) (e v)
  mem u v huv := c.mem (e u) (e v) (fun h => huv (e.injective h))
  bal u v huv := by
    have h := c.bal (e u) (e v) (fun h => huv (e.injective h))
    simpa using h
  proper u v v' h1 h2 h3 :=
    c.proper (e u) (e v) (e v') (fun h => h1 (e.injective h)) (fun h => h2 (e.injective h))
      (fun h => h3 (e.injective h))

/-- **Negating a whole colour class.**  The source's "reverse the colours on one path", as an
operation on a bundled colouring. -/
def CliqueColouring.flipAt {V : Type*} {k : ℕ} {sg : V → V → ℤ} (c : CliqueColouring V k sg)
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (d : ℤ) : CliqueColouring V k sg where
  col := flip d c.col
  mem u v huv := flip_mem d (c.mem u v huv)
  bal u v huv := flip_balance d (hsg u v) (c.bal u v huv)
  proper u v v' h1 h2 h3 := flip_proper d (c.proper u v v' h1 h2 h3)

/-- **Every vertex misses a colour.** -/
theorem CliqueColouring.exists_missing {V : Type*} [Fintype V] {k : ℕ}
    {sg : V → V → ℤ} (c : CliqueColouring V k sg) (hcard : Fintype.card V = k) (u : V) :
    ∃ x ∈ P361027.M k, ∀ v, v ≠ u → c.col u v ≠ x :=
  exists_missing_colour c.col k u hcard (fun v hv => c.mem u v (Ne.symm hv))
    (fun v v' hv hv' hvv => c.proper u v v' (Ne.symm hv) (Ne.symm hv') hvv)

end Colouring

namespace P361027

/-- **A clique of even order is signed-colourable with `2m` colours, for every signature.**
This is the even half of the construction, packaged. -/
noncomputable def evenClique (m : ℕ) (hm : 0 < m) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x) :
    Colouring.CliqueColouring (ZMod (2 * m)) (2 * m) sg where
  col := Walecki.col m sg
  mem _ _ huv := Walecki.col_mem m hm hsg huv
  bal _ _ huv := Walecki.col_balance m hm hsg hsymm huv
  proper _ _ _ huv huv' hvv := Walecki.col_proper m hm hsg huv huv' hvv

end P361027

/-! ### Basepoint-preserving transport

`CliqueColouring.transport` moves a colouring along any equivalence, and that is not enough for
the join.  The two joining vertices need missing colours `x` and `y` with `x = -σ(e)·y`, and
`flipAt` can change a sign but never an absolute value — so `|x| = |y|` has to come from the
construction.  It does: `pathOf 0 = 0`, so the clique's vertex `0` ends path `0` and misses a
colour of absolute value `1`.  But that is a fact about the vertex `0` **of `ZMod (2m)`**, and an
arbitrary equivalence need not send the graph's joining vertex there.

`atBasepoint` repairs any equivalence into one that does, by composing with the transposition that
swaps the image of the chosen point with the chosen target.  Nothing else about the equivalence
changes, so the transported colouring is still a colouring. -/

end Principia.MathDB

/-! ### A basepoint-preserving repair for an arbitrary equivalence

Declared in the root `Equiv` namespace rather than with a `_root_.` prefix inside
`Principia.MathDB`.  The two spell the same declaration, but `check_gate_coverage.py` records the
name **as written**, so the prefixed form reads to it as one ungated declaration plus one phantom
gate entry. -/

namespace Equiv

/-- Adjust an equivalence so that it sends `u₀` to `w₀`. -/
def atBasepoint {V W : Type*} [DecidableEq W] (e : V ≃ W) (u₀ : V) (w₀ : W) :
    V ≃ W := e.trans (Equiv.swap (e u₀) w₀)

@[simp] theorem atBasepoint_apply_self {V W : Type*} [DecidableEq W] (e : V ≃ W)
    (u₀ : V) (w₀ : W) : e.atBasepoint u₀ w₀ u₀ = w₀ := by
  simp [Equiv.atBasepoint]

end Equiv

namespace Principia.MathDB.P361027

/-! ### The odd decomposition

`K_{2m+1}` is handled on `Option (ZMod (2m)) = {∞} ∪ ℤ_{2m}`, **not** on `ZMod (2m+1)`: `∞` is
internal to every path and is the vertex the matching misses, which is exactly why it misses only
the colour `0`.

The decomposition is Walecki's second consequence.  Each cycle `C_p` runs
`∞, w p 0, …, w p (2m-1), ∞`; deleting its *central* edge — the one joining positions `m-1` and `m`
of the finite stretch — leaves a Hamilton path on all `2m+1` vertices, and the `m` deleted edges are
precisely the diameter perfect matching of `ℤ_{2m}`.

**This reuses the even case rather than repeating it.**  The finite edges of the `p`-th path are
exactly the Walecki edges `s(w p t, w p (t+1))` for every `t ≠ m-1`, so `edge_inj` and `edge_surj`
carry over verbatim on that restriction.  What is genuinely new is only what is proved below: that
the central edges join antipodes and cover `ℤ_{2m}`, and that the `2m` edges at `∞` hit every
residue once. -/

namespace Odd

open Walecki

/-- **Every Walecki path is a translate of the path through `0`.**  The zig-zag `i, i-1, i+1, …`
adds a quantity depending only on the position, so the starting point factors out.  This is what
makes the `m` central edges a transversal: they start at `m` consecutive residues. -/
theorem w_shift (m : ℕ) (i : ZMod (2 * m)) (t : ℕ) : w m i t = i + w m 0 t := by
  simp only [w]
  split_ifs with h <;> ring

/-- Where the central edge of the path through `0` begins. -/
def base (m : ℕ) : ZMod (2 * m) := w m 0 (m - 1)

theorem central_start (m p : ℕ) :
    w m ((p : ℕ) : ZMod (2 * m)) (m - 1) = ((p : ℕ) : ZMod (2 * m)) + base m :=
  w_shift m _ _

/-- **The central edge joins antipodes.**  Its endpoints differ by `m`, for either parity of `m`:
with `m = 2j` they are `i+j` and `i-j`, with `m = 2j+1` they are `i+j` and `i-(j+1)`, and
`4j+2 = 2m` closes the second case.

Note the rewrites go through `congrArg`.  Rewriting `m` itself would also rewrite the `m` in the
ambient type `ZMod (2 * m)`; `congrArg (w m i)` reaches the index and nothing else. -/
theorem central_diff (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m)) :
    w m i m = w m i (m - 1) + ((m : ℕ) : ZMod (2 * m)) := by
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨j, hj⟩ := he
    have h1 : m = 2 * j := by omega
    have h2 : m - 1 = 2 * (j - 1) + 1 := by omega
    have h3 : j - 1 + 1 = j := by omega
    have e1 : w m i m = w m i (2 * j) := congrArg (w m i) h1
    have e2 : w m i (m - 1) = w m i (2 * (j - 1) + 1) := congrArg (w m i) h2
    have hmc : ((m : ℕ) : ZMod (2 * m)) = ((2 * j : ℕ) : ZMod (2 * m)) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod (2 * m))) h1
    rw [e1, e2, w_even, w_odd, h3, hmc]
    push_cast
    ring
  · obtain ⟨j, hj⟩ := ho
    have h2 : m - 1 = 2 * j := by omega
    have e1 : w m i m = w m i (2 * j + 1) := congrArg (w m i) hj
    have e2 : w m i (m - 1) = w m i (2 * j) := congrArg (w m i) h2
    have hmc : ((m : ℕ) : ZMod (2 * m)) = ((2 * j + 1 : ℕ) : ZMod (2 * m)) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod (2 * m))) hj
    have h4 : ((4 * j + 2 : ℕ) : ZMod (2 * m)) = 0 := by
      have e : (4 * j + 2 : ℕ) = 2 * m := by omega
      rw [e]
      exact ZMod.natCast_self _
    rw [e1, e2, w_odd, w_even, hmc]
    push_cast at h4 ⊢
    linear_combination -h4

/-- The central edge is a genuine edge: `m ≠ 0` in `ℤ_{2m}`. -/
theorem central_ne (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m)) :
    w m i m ≠ w m i (m - 1) := by
  rw [central_diff m hm]
  intro h
  have hz : ((m : ℕ) : ZMod (2 * m)) = 0 := by linear_combination h
  exact cast_ne_zero m hm (by omega) hz

/-- **The `m` central edges cover `ℤ_{2m}`.**  Every vertex is an endpoint of one of them, so the
matching is perfect.  Since `w p (m-1) = p + base`, the `m` starting points are `m` consecutive
residues, hence a transversal of the `m` antipodal pairs. -/
theorem matching_cover (m : ℕ) (hm : 0 < m) (v : ZMod (2 * m)) :
    ∃ p, p < m ∧ (v = w m ((p : ℕ) : ZMod (2 * m)) (m - 1) ∨
      v = w m ((p : ℕ) : ZMod (2 * m)) (m - 1) + ((m : ℕ) : ZMod (2 * m))) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hdlt : (v - base m).val < 2 * m := ZMod.val_lt _
  have hdv : (((v - base m).val : ℕ) : ZMod (2 * m)) = v - base m := val_cast m hm _
  by_cases hc : (v - base m).val < m
  · refine ⟨(v - base m).val, hc, Or.inl ?_⟩
    rw [central_start]
    linear_combination -hdv
  · refine ⟨(v - base m).val - m, by omega, Or.inr ?_⟩
    rw [central_start]
    have hsum : (((v - base m).val - m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m))
        = (((v - base m).val : ℕ) : ZMod (2 * m)) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    linear_combination -hsum - hdv

/-- The `s`-th vertex of the `p`-th path: the cycle through `∞` with its central edge deleted,
read from one end.  Positions `0 … m-1` walk the first half backwards to `w p 0`, position `m` is
`∞`, and positions `m+1 … 2m` walk the second half back down to `w p m`. -/
def ov (m p s : ℕ) : Option (ZMod (2 * m)) :=
  if s < m then some (w m ((p : ℕ) : ZMod (2 * m)) (m - 1 - s))
  else if s = m then none
  else some (w m ((p : ℕ) : ZMod (2 * m)) (3 * m - s))

theorem ov_before (m p : ℕ) (hm : 0 < m) :
    ov m p (m - 1) = some ((p : ℕ) : ZMod (2 * m)) := by
  rw [ov, if_pos (by omega), show m - 1 - (m - 1) = 0 from by omega, w_zero]

/-- `∞` sits at the middle position of every path — it is internal, never an endpoint. -/
theorem ov_infty (m p : ℕ) (hm : 0 < m) : ov m p m = none := by
  rw [ov, if_neg (by omega), if_pos rfl]

theorem ov_after (m p : ℕ) (hm : 0 < m) :
    ov m p (m + 1) = some (((p : ℕ) : ZMod (2 * m)) - ((m : ℕ) : ZMod (2 * m))) := by
  rw [ov, if_neg (by omega), if_neg (by omega),
    show 3 * m - (m + 1) = 2 * m - 1 from by omega, w_last m hm]

/-- **The two neighbours of `∞` on the `p`-th path are `p` and `p - m`**, so over `p < m` they run
through every residue: `{p : p < m}` and `{p - m : p < m}` partition `ℤ_{2m}`. -/
theorem infty_cover (m : ℕ) (hm : 0 < m) (v : ZMod (2 * m)) :
    ∃ p, p < m ∧ (some v = ov m p (m - 1) ∨ some v = ov m p (m + 1)) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hvlt : v.val < 2 * m := ZMod.val_lt _
  have hvv : ((v.val : ℕ) : ZMod (2 * m)) = v := val_cast m hm _
  by_cases hc : v.val < m
  · exact ⟨v.val, hc, Or.inl (by rw [ov_before m _ hm, hvv])⟩
  · refine ⟨v.val - m, by omega, Or.inr ?_⟩
    rw [ov_after m _ hm]
    have e1 : ((v.val - m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = v := by
      rw [← Nat.cast_add, show v.val - m + m = v.val from by omega, hvv]
    have e2 : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
      rw [← Nat.cast_add, show m + m = 2 * m from by ring]
      exact ZMod.natCast_self _
    simp only [Option.some.injEq]
    linear_combination -e1 + e2

/-- The two families are disjoint: an "up" neighbour of `∞` is never a "down" one, so the `2m`
edges at `∞` are distinct. -/
theorem infty_disjoint (m : ℕ) (hm : 0 < m) {p p' : ℕ} (hp : p < m) (hp' : p' < m)
    (h : ((p : ℕ) : ZMod (2 * m)) = ((p' : ℕ) : ZMod (2 * m)) - ((m : ℕ) : ZMod (2 * m))) :
    False := by
  have h2 : ((p + m : ℕ) : ZMod (2 * m)) = ((p' : ℕ) : ZMod (2 * m)) := by
    push_cast
    linear_combination h
  have h3 : p + m = p' := cast_inj m (by omega) (by omega) h2
  omega

end Odd

/-! ### Odd colours, and the bridge back to the even decomposition

Two things are set up here.

**The colours.**  `colFwd` assigns magnitude `p + 1` — the *path index*, never the position — and
absorbs the whole signature into the carried sign.  So the `m` odd paths take magnitudes `1 … m`
and the matching takes `0`, which is exactly `M (2m+1) = [-m, m]`.  The sign has to be
re-accumulated along the odd path's own traversal order, because that order visits `σ` at `∞` as
well; but once `osgn` is defined the balance and internal-negation proofs are the even ones word
for word, since neither mentions the path.

**The bridge.**  The `p`-th odd path's edge at position `s` is, for every `s` other than the two
straddling `∞`, a Walecki edge — and `widx` says which one.  Positions `0 … m-2` walk `t` down from
`m-2` to `0`, positions `m+1 … 2m-1` walk `t` down from `2m-2` to `m`, and the index `m-1` that
would be the central edge is exactly the one never hit.  This is what lets `edge_inj` and
`edge_surj` be reused instead of reproved. -/

namespace Odd

open Walecki

/-- Membership in the colour set, for an odd number of colours.  Unlike `M (2m)` there is no
puncture: `0` is a colour, and it is the one the matching uses. -/
theorem mem_M_odd (m : ℕ) (x : ℤ) : x ∈ M (2 * m + 1) ↔ -(m : ℤ) ≤ x ∧ x ≤ (m : ℤ) := by
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [M, if_pos h1, h2, Finset.mem_Icc]

theorem zero_mem_M_odd (m : ℕ) : (0 : ℤ) ∈ M (2 * m + 1) := by
  rw [mem_M_odd]
  constructor <;> omega

/-- The sign carried along the `p`-th odd path up to position `s`. -/
def osgn (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ) (p : ℕ) : ℕ → ℤ
  | 0 => 1
  | (s + 1) => osgn m sg p s * sg (ov m p s) (ov m p (s + 1))

theorem osgn_succ (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ) (p s : ℕ) :
    osgn m sg p (s + 1) = osgn m sg p s * sg (ov m p s) (ov m p (s + 1)) := rfl

theorem osgn_eq_one_or (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) (p s : ℕ) :
    osgn m sg p s = 1 ∨ osgn m sg p s = -1 := by
  induction s with
  | zero => left; rfl
  | succ s ih =>
    rw [osgn_succ]
    rcases ih with h1 | h1 <;> rcases hsg (ov m p s) (ov m p (s + 1)) with h2 | h2 <;>
      rw [h1, h2] <;> norm_num

/-- Colour of the incidence at `ov p s` pointing along the edge to `ov p (s+1)`. -/
def ocolFwd (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ) (p s : ℕ) : ℤ :=
  osgn m sg p s * ((p : ℤ) + 1)

/-- Colour of the incidence at `ov p (s+1)` pointing back along the same edge. -/
def ocolBwd (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ) (p s : ℕ) : ℤ :=
  -(osgn m sg p (s + 1)) * ((p : ℤ) + 1)

/-- **Balance holds by construction**, using only `σ² = 1`. -/
theorem ocolFwd_eq (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) (p s : ℕ) :
    ocolFwd m sg p s = -(sg (ov m p s) (ov m p (s + 1))) * ocolBwd m sg p s := by
  rw [ocolFwd, ocolBwd, osgn_succ]
  rcases hsg (ov m p s) (ov m p (s + 1)) with h | h <;> rw [h] <;> ring

/-- **At an internal vertex the two incidences are negatives.**  In particular this holds at `∞`,
which is internal on every path — so `∞` sees both signs of every magnitude `1 … m`. -/
theorem ocolBwd_eq_neg_ocolFwd (m : ℕ)
    (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ) (p s : ℕ) :
    ocolBwd m sg p s = -(ocolFwd m sg p (s + 1)) := by
  rw [ocolBwd, ocolFwd]
  ring

theorem ocolFwd_mem (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) {p : ℕ} (hp : p < m) (s : ℕ) :
    ocolFwd m sg p s ∈ M (2 * m + 1) := by
  rw [mem_M_odd, ocolFwd]
  have hple : ((p : ℤ) + 1) ≤ (m : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hp
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rcases osgn_eq_one_or m hsg p s with h | h <;> rw [h] <;> constructor <;> linarith

theorem ocolBwd_mem (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ u v, sg u v = 1 ∨ sg u v = -1) {p : ℕ} (hp : p < m) (s : ℕ) :
    ocolBwd m sg p s ∈ M (2 * m + 1) := by
  rw [mem_M_odd, ocolBwd]
  have hple : ((p : ℤ) + 1) ≤ (m : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hp
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rcases osgn_eq_one_or m hsg p (s + 1) with h | h <;> rw [h] <;> constructor <;> linarith

/-- The Walecki index of the finite edge sitting at position `s` of an odd path.  Positions
`0 … m-2` give `t = m-2-s`, counting down; positions `m+1 … 2m-1` give `t = 3m-1-s`, again counting
down.  The two ranges are `[0, m-2]` and `[m, 2m-2]`, so the central index `m-1` is precisely the
one never produced — which is the sense in which the deleted edge is deleted. -/
def widx (m s : ℕ) : ℕ := if s + 1 < m then m - 2 - s else 3 * m - 1 - s

theorem ov_lo (m p s : ℕ) (hs : s + 1 < m) :
    ov m p s = some (w m ((p : ℕ) : ZMod (2 * m)) (widx m s + 1)) := by
  rw [ov, if_pos (show s < m by omega), widx, if_pos hs,
    show m - 1 - s = m - 2 - s + 1 from by omega]

theorem ov_lo_succ (m p s : ℕ) (hs : s + 1 < m) :
    ov m p (s + 1) = some (w m ((p : ℕ) : ZMod (2 * m)) (widx m s)) := by
  rw [ov, if_pos (show s + 1 < m by omega), widx, if_pos hs,
    show m - 1 - (s + 1) = m - 2 - s from by omega]

theorem ov_hi (m p s : ℕ) (hm : 0 < m) (h1 : m + 1 ≤ s) (h2 : s ≤ 2 * m - 1) :
    ov m p s = some (w m ((p : ℕ) : ZMod (2 * m)) (widx m s + 1)) := by
  rw [ov, if_neg (show ¬ s < m by omega), if_neg (show ¬ s = m by omega), widx,
    if_neg (show ¬ s + 1 < m by omega), show 3 * m - 1 - s + 1 = 3 * m - s from by omega]

theorem ov_hi_succ (m p s : ℕ) (hm : 0 < m) (h1 : m + 1 ≤ s) (h2 : s ≤ 2 * m - 1) :
    ov m p (s + 1) = some (w m ((p : ℕ) : ZMod (2 * m)) (widx m s)) := by
  rw [ov, if_neg (show ¬ s + 1 < m by omega), if_neg (show ¬ s + 1 = m by omega), widx,
    if_neg (show ¬ s + 1 < m by omega), show 3 * m - (s + 1) = 3 * m - 1 - s from by omega]

/-- **The deleted edge is never produced, and every produced index is a legitimate Walecki
position.**  This is the whole content of the reuse: on these positions the odd path's edges are
even-case edges, so `edge_inj` and `edge_surj` apply unchanged. -/
theorem widx_ne_central (m s : ℕ) (hm : 0 < m)
    (h : s + 1 < m ∨ (m + 1 ≤ s ∧ s ≤ 2 * m - 1)) :
    widx m s ≠ m - 1 ∧ widx m s + 1 ≤ 2 * m - 1 := by
  rcases h with h | h
  · rw [widx, if_pos h]
    omega
  · rw [widx, if_neg (show ¬ s + 1 < m by omega)]
    omega

end Odd

/-! ### Every pair is a matching edge or a path edge

The three cases separate without an argument.  An antipodal pair *is* a central edge — there are
`m` of each, the central ones are antipodal by `central_diff`, and `edge_surj` says every pair
occurs exactly once, so counting forces the identification.  Only one direction is needed below,
and `central_diff` gives it alone.

The consequence is that the `t` returned by `edge_surj` for a non-antipodal pair automatically
avoids `m-1`, which is exactly the index `widx` never produces.  `spos` inverts `widx` on what
remains. -/

namespace Odd

open Walecki

/-- The `s`-th edge of the `p`-th odd path. -/
def oedge (m p s : ℕ) : Sym2 (Option (ZMod (2 * m))) := s(ov m p s, ov m p (s + 1))

/-- `-m = m` in `ℤ_{2m}`, so an antipodal pair is named by either sign. -/
theorem neg_m (m : ℕ) : -((m : ℕ) : ZMod (2 * m)) = ((m : ℕ) : ZMod (2 * m)) := by
  have h : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add, show m + m = 2 * m from by ring]
    exact ZMod.natCast_self _
  linear_combination -h

/-- **A non-antipodal pair never sits on the central edge.**  This is the half of "the antipodal
pairs are exactly the central edges" that the decomposition needs, and `central_diff` supplies it
without any counting. -/
theorem central_of_antipodal (m : ℕ) (hm : 0 < m) {p t : ℕ} {u v : ZMod (2 * m)}
    (he : edge m p t = s(u, v)) (hanti : v ≠ u + ((m : ℕ) : ZMod (2 * m))) : t ≠ m - 1 := by
  intro h
  have hmm : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add, show m + m = 2 * m from by ring]
    exact ZMod.natCast_self _
  rw [edge, h, show m - 1 + 1 = m from by omega, central_diff m hm] at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hanti (by rw [← h2, ← h1])
  · refine hanti ?_
    rw [← h1, ← h2]
    linear_combination -hmm

/-- The inverse of `widx` on the indices a path edge can carry. -/
def spos (m t : ℕ) : ℕ := if t < m - 1 then m - 2 - t else 3 * m - 1 - t

theorem spos_range (m t : ℕ) (hm : 0 < m) (h : t ≠ m - 1) (ht : t + 1 < 2 * m) :
    (spos m t + 1 < m ∨ (m + 1 ≤ spos m t ∧ spos m t ≤ 2 * m - 1)) ∧ spos m t < 2 * m := by
  rw [spos]
  split_ifs with hc <;> omega

theorem widx_spos (m t : ℕ) (hm : 0 < m) (h : t ≠ m - 1) (ht : t + 1 < 2 * m) :
    widx m (spos m t) = t := by
  rw [spos]
  split_ifs with hc
  · rw [widx, if_pos (by omega)]
    omega
  · rw [widx, if_neg (by omega)]
    omega

/-- **The odd path's edge at `spos t` is the Walecki edge at `t`**, with the endpoints in the
reversed order — the odd traversal walks each half backwards. -/
theorem oedge_eq_edge (m : ℕ) (hm : 0 < m) (p t : ℕ) (h : t ≠ m - 1) (ht : t + 1 < 2 * m) :
    oedge m p (spos m t)
      = s(some (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)), some (w m ((p : ℕ) : ZMod (2 * m)) t)) := by
  obtain ⟨hr, -⟩ := spos_range m t hm h ht
  rw [oedge]
  rcases hr with hlo | ⟨h1, h2⟩
  · rw [ov_lo m p _ hlo, ov_lo_succ m p _ hlo, widx_spos m t hm h ht]
  · rw [ov_hi m p _ hm h1 h2, ov_hi_succ m p _ hm h1 h2, widx_spos m t hm h ht]

/-- **Every pair of distinct vertices is a matching edge or a path edge.** -/
theorem oedge_surj (m : ℕ) (hm : 0 < m) {u v : Option (ZMod (2 * m))} (huv : u ≠ v) :
    (∃ a : ZMod (2 * m), u = some a ∧ v = some (a + ((m : ℕ) : ZMod (2 * m)))) ∨
    (∃ q : ℕ × ℕ, q.1 < m ∧ q.2 < 2 * m ∧ oedge m q.1 q.2 = s(u, v)) := by
  cases u with
  | none =>
    cases v with
    | none => exact absurd rfl huv
    | some b =>
      right
      obtain ⟨p, hp, hcase⟩ := infty_cover m hm b
      rcases hcase with hc | hc
      · refine ⟨(p, m - 1), hp, by omega, ?_⟩
        rw [oedge, show m - 1 + 1 = m from by omega, ov_infty m p hm, ← hc]
        exact Sym2.eq_swap
      · refine ⟨(p, m), hp, by omega, ?_⟩
        rw [oedge, ov_infty m p hm, ← hc]
  | some a =>
    cases v with
    | none =>
      right
      obtain ⟨p, hp, hcase⟩ := infty_cover m hm a
      rcases hcase with hc | hc
      · refine ⟨(p, m - 1), hp, by omega, ?_⟩
        rw [oedge, show m - 1 + 1 = m from by omega, ov_infty m p hm, ← hc]
      · refine ⟨(p, m), hp, by omega, ?_⟩
        rw [oedge, ov_infty m p hm, ← hc]
        exact Sym2.eq_swap
    | some b =>
      by_cases hab : b = a + ((m : ℕ) : ZMod (2 * m))
      · exact Or.inl ⟨a, rfl, by rw [hab]⟩
      · right
        have hne : a ≠ b := by
          intro hcon
          exact huv (by rw [hcon])
        obtain ⟨q, hq1, hq2, hq3⟩ := edge_surj' m hm hne
        have hcent : q.2 ≠ m - 1 := central_of_antipodal m hm hq3 hab
        refine ⟨(q.1, spos m q.2), hq1, (spos_range m q.2 hm hcent hq2).2, ?_⟩
        rw [oedge_eq_edge m hm q.1 q.2 hcent hq2]
        rw [edge] at hq3
        rcases Sym2.eq_iff.mp hq3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
          exact Sym2.eq_swap
        · rw [h1, h2]

end Odd

/-! ### Uniqueness

`∞` does the case split for free.  Whether a path edge contains `∞` is a property of the *edge*,
so it transfers across an equality of edges without touching either side — and it is equivalent to
the position being `m-1` or `m`.  So the two edges are either both incident to `∞` or both finite,
and the remaining work splits into a four-case check on `∞`'s edges and one appeal to `edge_inj`
for the finite ones.

`w_step` completes the antipodal/central identification in the direction stage 12b did not need:
consecutive path vertices differ by `±(t+1)`, so an antipodal pair forces `t+1 = m`. Together with
`central_of_antipodal` this says the central edges are *exactly* the antipodal pairs, which is what
makes the matching's colour `0` well defined. -/

namespace Odd

open Walecki

/-- **Consecutive vertices of a Walecki path differ by `±(t+1)`.**  The zig-zag alternates a step
up and a step down, and the step length grows by one each time. -/
theorem w_step (m : ℕ) (i : ZMod (2 * m)) (t : ℕ) :
    w m i (t + 1) - w m i t = ((t + 1 : ℕ) : ZMod (2 * m)) ∨
    w m i (t + 1) - w m i t = -(((t + 1 : ℕ)) : ZMod (2 * m)) := by
  rcases Nat.even_or_odd t with he | ho
  · obtain ⟨j, hj⟩ := he
    have e1 : w m i t = w m i (2 * j) := congrArg (w m i) (by omega)
    have e2 : w m i (t + 1) = w m i (2 * j + 1) := congrArg (w m i) (by omega)
    have hc : ((t + 1 : ℕ) : ZMod (2 * m)) = ((2 * j + 1 : ℕ) : ZMod (2 * m)) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod (2 * m))) (by omega)
    right
    rw [e1, e2, w_even, w_odd, hc]
    push_cast
    ring
  · obtain ⟨j, hj⟩ := ho
    have e1 : w m i t = w m i (2 * j + 1) := congrArg (w m i) hj
    have e2 : w m i (t + 1) = w m i (2 * (j + 1)) := congrArg (w m i) (by omega)
    have hc : ((t + 1 : ℕ) : ZMod (2 * m)) = ((2 * j + 2 : ℕ) : ZMod (2 * m)) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod (2 * m))) (by omega)
    left
    rw [e1, e2, w_even, w_odd, hc]
    push_cast
    ring

/-- **An antipodal pair sits on the central edge** — the converse of `central_of_antipodal`, and
the half that makes "the central edges are exactly the antipodal pairs" an identification rather
than an inclusion. -/
theorem central_of_antipodal_conv (m : ℕ) (hm : 0 < m) {p t : ℕ} (ht : t + 1 < 2 * m)
    {u v : ZMod (2 * m)} (he : edge m p t = s(u, v))
    (hanti : v = u + ((m : ℕ) : ZMod (2 * m))) : t = m - 1 := by
  have hstep : w m ((p : ℕ) : ZMod (2 * m)) (t + 1) - w m ((p : ℕ) : ZMod (2 * m)) t
      = ((m : ℕ) : ZMod (2 * m)) := by
    rw [edge] at he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hanti]
      ring
    · rw [h1, h2, hanti]
      have h0 := neg_m m
      linear_combination h0
  have hmt : ((m : ℕ) : ZMod (2 * m)) = ((t + 1 : ℕ) : ZMod (2 * m)) := by
    rcases w_step m ((p : ℕ) : ZMod (2 * m)) t with hc | hc
    · rw [← hstep]
      exact hc
    · have h0 := neg_m m
      rw [hstep] at hc
      linear_combination -hc - h0
  have := cast_inj m (by omega) ht hmt
  omega

/-- `∞` occupies position `m` of every path and no other. -/
theorem ov_eq_none_iff (m p s : ℕ) (hm : 0 < m) : ov m p s = none ↔ s = m := by
  rw [ov]
  split_ifs with h1 h2
  · constructor
    · intro hc
      simp at hc
    · intro hc
      omega
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · constructor
    · intro hc
      simp at hc
    · intro hc
      exact absurd hc h2

/-- **`∞` lies on the `p`-th path's edge at `s` exactly when `s` is `m-1` or `m`.**  Being a
property of the edge, this transfers across an equality of edges. -/
theorem none_mem_oedge (m p s : ℕ) (hm : 0 < m) :
    (none : Option (ZMod (2 * m))) ∈ oedge m p s ↔ (s = m - 1 ∨ s = m) := by
  rw [oedge, Sym2.mem_iff]
  constructor
  · rintro (hc | hc)
    · exact Or.inr ((ov_eq_none_iff m p s hm).mp hc.symm)
    · have := (ov_eq_none_iff m p (s + 1) hm).mp hc.symm
      exact Or.inl (by omega)
  · rintro (hc | hc)
    · exact Or.inr ((ov_eq_none_iff m p (s + 1) hm).mpr (by omega)).symm
    · exact Or.inl ((ov_eq_none_iff m p s hm).mpr hc).symm

/-- `widx` is injective on the positions that carry a finite edge: it is strictly decreasing on
each of the two runs, and the runs land in the disjoint ranges `[0, m-2]` and `[m, 2m-2]`. -/
theorem widx_inj (m s s' : ℕ) (hm : 0 < m)
    (h : s + 1 < m ∨ (m + 1 ≤ s ∧ s ≤ 2 * m - 1))
    (h' : s' + 1 < m ∨ (m + 1 ≤ s' ∧ s' ≤ 2 * m - 1))
    (he : widx m s = widx m s') : s = s' := by
  rw [widx, widx] at he
  rcases h with h | h
  · rw [if_pos h] at he
    rcases h' with h' | h'
    · rw [if_pos h'] at he; omega
    · rw [if_neg (show ¬ s' + 1 < m by omega)] at he; omega
  · rw [if_neg (show ¬ s + 1 < m by omega)] at he
    rcases h' with h' | h'
    · rw [if_pos h'] at he; omega
    · rw [if_neg (show ¬ s' + 1 < m by omega)] at he; omega

/-- **A path edge determines its path and its position.** -/
theorem oedge_inj (m : ℕ) (hm : 0 < m) {p s p' s' : ℕ} (hp : p < m) (hp' : p' < m)
    (hs : s < 2 * m) (hs' : s' < 2 * m) (h : oedge m p s = oedge m p' s') :
    p = p' ∧ s = s' := by
  have e1 : ∀ q : ℕ, oedge m q (m - 1) = s(some ((q : ℕ) : ZMod (2 * m)), none) := by
    intro q
    rw [oedge, show m - 1 + 1 = m from by omega, ov_infty m q hm, ov_before m q hm]
  have e2 : ∀ q : ℕ, oedge m q m
      = s(none, some (((q : ℕ) : ZMod (2 * m)) - ((m : ℕ) : ZMod (2 * m)))) := by
    intro q
    rw [oedge, ov_infty m q hm, ov_after m q hm]
  have ef : ∀ q x : ℕ, x < 2 * m → ¬ (x = m - 1 ∨ x = m) →
      oedge m q x = s(some (w m ((q : ℕ) : ZMod (2 * m)) (widx m x + 1)),
                      some (w m ((q : ℕ) : ZMod (2 * m)) (widx m x))) := by
    intro q x hx hnx
    rw [oedge]
    rcases (show x + 1 < m ∨ (m + 1 ≤ x ∧ x ≤ 2 * m - 1) by omega) with hl | ⟨ha, hb⟩
    · rw [ov_lo m q x hl, ov_lo_succ m q x hl]
    · rw [ov_hi m q x hm ha hb, ov_hi_succ m q x hm ha hb]
  have hmem : (s = m - 1 ∨ s = m) ↔ (s' = m - 1 ∨ s' = m) := by
    rw [← none_mem_oedge m p s hm, ← none_mem_oedge m p' s' hm, h]
  by_cases hc : s = m - 1 ∨ s = m
  · have hc' : s' = m - 1 ∨ s' = m := hmem.mp hc
    -- NO `subst` here.  `subst hy` on `hy : s' = m` eliminates **`m`**, not `s'` — both sides are
    -- variables, so the tactic is free to choose, and every later mention of `m` then fails with
    -- "unknown identifier".  Rewriting `h` leaves the context intact.
    rcases hc with hx | hx
    · rcases hc' with hy | hy
      · rw [hx, hy, e1 p, e1 p'] at h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact ⟨cast_inj m (by omega) (by omega) (Option.some_injective _ h1),
            hx.trans hy.symm⟩
        · simp at h1
      · rw [hx, hy, e1 p, e2 p'] at h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · simp at h1
        · exact (infty_disjoint m hm hp hp' (Option.some_injective _ h1)).elim
    · rcases hc' with hy | hy
      · rw [hx, hy, e2 p, e1 p'] at h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
        · simp at h1
        · exact (infty_disjoint m hm hp' hp (Option.some_injective _ h2).symm).elim
      · rw [hx, hy, e2 p, e2 p'] at h
        rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
        · refine ⟨cast_inj m (by omega) (by omega) ?_, hx.trans hy.symm⟩
          have h3 := Option.some_injective _ h2
          linear_combination h3
        · simp at h1
  · have hc' : ¬ (s' = m - 1 ∨ s' = m) := fun x => hc (hmem.mpr x)
    have hr : s + 1 < m ∨ (m + 1 ≤ s ∧ s ≤ 2 * m - 1) := by omega
    have hr' : s' + 1 < m ∨ (m + 1 ≤ s' ∧ s' ≤ 2 * m - 1) := by omega
    obtain ⟨hne, hle⟩ := widx_ne_central m s hm hr
    obtain ⟨hne', hle'⟩ := widx_ne_central m s' hm hr'
    rw [ef p s hs hc, ef p' s' hs' hc'] at h
    have hedge : edge m p (widx m s) = edge m p' (widx m s') := by
      rw [edge, edge]
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Option.some_injective _ h1, Option.some_injective _ h2]
      · rw [Option.some_injective _ h1, Option.some_injective _ h2]
        exact Sym2.eq_swap
    obtain ⟨hpp, hww⟩ := edge_inj m hm hp hp' (by omega) (by omega) hedge
    exact ⟨hpp, widx_inj m s s' hm hr hr' hww⟩

end Odd

/-! ### The odd colouring 

`ocol` reads the incidence colour off `olocate`, exactly as the even `col` reads it off `locate`.
The one structural difference is the `else` branch: a matching edge is **not** a path edge, so it
falls through — and it falls through to `0`, which is precisely the colour it should carry.  That
the two branches are exclusive is `central_of_antipodal_conv` together with the fact that `widx`
never produces `m-1`.

`ocol_proper` then splits three ways at a vertex `u`, and only the first is real work:
  * both incidences on path edges — the even argument, via `ocolBwd_eq_neg_ocolFwd`;
  * one path, one matching — the matching gives `0` and a path gives `±(p+1) ≠ 0`;
  * both matching — impossible, since `v = u + m` determines `v`.
-/

namespace Odd

open Walecki

/-- `{u, v}` is an edge of one of the `m` paths. -/
def IsPathEdge (m : ℕ) (u v : Option (ZMod (2 * m))) : Prop :=
  ∃ q : ℕ × ℕ, q.1 < m ∧ q.2 < 2 * m ∧ oedge m q.1 q.2 = s(u, v)

open scoped Classical in
/-- The path index and position carrying `{u, v}`; junk when it is not a path edge. -/
noncomputable def olocate (m : ℕ) (u v : Option (ZMod (2 * m))) : ℕ × ℕ :=
  if h : IsPathEdge m u v then h.choose else (0, 0)

theorem olocate_spec (m : ℕ) {u v : Option (ZMod (2 * m))} (h : IsPathEdge m u v) :
    (olocate m u v).1 < m ∧ (olocate m u v).2 < 2 * m
      ∧ oedge m (olocate m u v).1 (olocate m u v).2 = s(u, v) := by
  classical
  rw [olocate, dif_pos h]
  exact h.choose_spec

theorem olocate_unique (m : ℕ) (hm : 0 < m) {u v : Option (ZMod (2 * m))} (h : IsPathEdge m u v)
    {p s : ℕ} (hp : p < m) (hs : s < 2 * m) (he : oedge m p s = s(u, v)) :
    olocate m u v = (p, s) := by
  obtain ⟨hp', hs', he'⟩ := olocate_spec m h
  have hpair := oedge_inj m hm hp' hp hs' hs (by rw [he', he])
  exact Prod.ext hpair.1 hpair.2

/-- **`olocate` sees only the unordered pair.** -/
theorem olocate_symm (m : ℕ) (hm : 0 < m) {u v : Option (ZMod (2 * m))} (h : IsPathEdge m u v)
    (h' : IsPathEdge m v u) : olocate m u v = olocate m v u := by
  obtain ⟨hp, hs, he⟩ := olocate_spec m h'
  have hx := olocate_unique m hm h hp hs (by rw [he, Sym2.eq_swap])
  exact hx.trans Prod.mk.eta

open scoped Classical in
/-- The colour of the incidence at `u` along `{u, v}`.  A matching edge falls through to `0`. -/
noncomputable def ocol (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ)
    (u v : Option (ZMod (2 * m))) : ℤ :=
  if IsPathEdge m u v then
    (if ov m (olocate m u v).1 (olocate m u v).2 = u
      then ocolFwd m sg (olocate m u v).1 (olocate m u v).2
      else ocolBwd m sg (olocate m u v).1 (olocate m u v).2)
  else 0

/-- **A matching edge is not a path edge.**  Its Walecki index would have to be `m-1`, and that is
exactly the index `widx` never produces. -/
theorem not_isPathEdge_of_antipodal (m : ℕ) (hm : 0 < m) {a : ZMod (2 * m)} :
    ¬ IsPathEdge m (some a) (some (a + ((m : ℕ) : ZMod (2 * m)))) := by
  rintro ⟨q, hq1, hq2, hq3⟩
  -- the edge has no `none`, so the position is finite and `widx` applies
  have hnone : ¬ (q.2 = m - 1 ∨ q.2 = m) := by
    rw [← none_mem_oedge m q.1 q.2 hm, hq3, Sym2.mem_iff]
    rintro (hc | hc) <;> simp at hc
  have hr : q.2 + 1 < m ∨ (m + 1 ≤ q.2 ∧ q.2 ≤ 2 * m - 1) := by omega
  obtain ⟨hne, hle⟩ := widx_ne_central m q.2 hm hr
  -- so it is the Walecki edge at `widx q.2`, which by the converse must be central
  have hedge : edge m q.1 (widx m q.2) = s(a, a + ((m : ℕ) : ZMod (2 * m))) := by
    rw [edge]
    rcases hr with hl | ⟨ha, hb⟩
    · rw [oedge, ov_lo m q.1 q.2 hl, ov_lo_succ m q.1 q.2 hl] at hq3
      rcases Sym2.eq_iff.mp hq3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Option.some_injective _ h1, Option.some_injective _ h2]
        exact Sym2.eq_swap
      · rw [Option.some_injective _ h1, Option.some_injective _ h2]
    · rw [oedge, ov_hi m q.1 q.2 hm ha hb, ov_hi_succ m q.1 q.2 hm ha hb] at hq3
      rcases Sym2.eq_iff.mp hq3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Option.some_injective _ h1, Option.some_injective _ h2]
        exact Sym2.eq_swap
      · rw [Option.some_injective _ h1, Option.some_injective _ h2]
  exact hne (central_of_antipodal_conv m hm (by omega) hedge rfl)

end Odd

/-! ### The odd path is Hamiltonian, and the colour's magnitude

`vidx` is to *vertices* what `widx` is to *edges*: it maps a position on the odd path to the
Walecki position carrying it.  Positions `0 … m-1` walk `t` down from `m-1` to `0`, positions
`m+1 … 2m` walk `t` down from `2m-1` to `m`, and `∞` sits at `m`.  The two runs cover `[0, m-1]`
and `[m, 2m-1]` — every Walecki position exactly once — so the `2m+1` positions carry `2m+1`
distinct vertices and the odd path is Hamiltonian.  As with `widx`, the injectivity is a range
argument, not a computation. -/

namespace Odd

open Walecki

/-- The Walecki position of the vertex at position `s`; meaningless at `s = m`, which is `∞`. -/
def vidx (m s : ℕ) : ℕ := if s < m then m - 1 - s else 3 * m - s

theorem ov_eq_some (m p s : ℕ) (hm : 0 < m) (hne : s ≠ m) :
    ov m p s = some (w m ((p : ℕ) : ZMod (2 * m)) (vidx m s)) := by
  -- Explicit `by_cases` rather than `split_ifs`.  `ov` and `vidx` each carry an `if s < m`, and
  -- `ov` a further `if s = m`; `split_ifs` merges and discharges them in a pattern that does not
  -- match the three cases one expects, so the branch names it introduces are not the ones written
  -- here.  Expanding `vidx` only after the `ov` conditions are settled keeps each `if_neg`
  -- unambiguous.
  by_cases h1 : s < m
  · rw [ov, if_pos h1, vidx, if_pos h1]
  · rw [ov, if_neg h1, if_neg hne, vidx, if_neg h1]

theorem vidx_lt (m s : ℕ) (hm : 0 < m) (hs : s ≤ 2 * m) (hne : s ≠ m) : vidx m s < 2 * m := by
  rw [vidx]
  split_ifs with h1 <;> omega

theorem vidx_inj (m s s' : ℕ) (hm : 0 < m) (hs : s ≤ 2 * m) (hs' : s' ≤ 2 * m)
    (hne : s ≠ m) (hne' : s' ≠ m) (he : vidx m s = vidx m s') : s = s' := by
  rw [vidx, vidx] at he
  split_ifs at he with h1 h2 <;> omega

/-- **The odd path is Hamiltonian.**  `∞` is the only position that is not a Walecki position, and
the remaining `2m` positions hit each Walecki position once. -/
theorem ov_inj (m p : ℕ) (hm : 0 < m) {s s' : ℕ} (hs : s ≤ 2 * m) (hs' : s' ≤ 2 * m)
    (he : ov m p s = ov m p s') : s = s' := by
  by_cases h1 : s = m
  · by_cases h2 : s' = m
    · omega
    · rw [h1, ov_infty m p hm, ov_eq_some m p s' hm h2] at he
      simp at he
  · by_cases h2 : s' = m
    · rw [h2, ov_infty m p hm, ov_eq_some m p s hm h1] at he
      simp at he
    · rw [ov_eq_some m p s hm h1, ov_eq_some m p s' hm h2] at he
      have hw := w_inj m ((p : ℕ) : ZMod (2 * m)) (vidx_lt m s hm hs h1)
        (vidx_lt m s' hm hs' h2) (Option.some_injective _ he)
      exact vidx_inj m s s' hm hs hs' h1 h2 hw

/-- Consecutive positions carry distinct vertices, so every path edge is a genuine edge. -/
theorem ov_ne_succ (m p s : ℕ) (hm : 0 < m) (hs : s < 2 * m) :
    ov m p s ≠ ov m p (s + 1) := by
  intro hc
  have := ov_inj m p hm (by omega) (by omega) hc
  omega

/-- Being a path edge does not depend on the order of the endpoints. -/
theorem isPathEdge_symm (m : ℕ) {u v : Option (ZMod (2 * m))} (h : IsPathEdge m u v) :
    IsPathEdge m v u := by
  obtain ⟨q, h1, h2, h3⟩ := h
  exact ⟨q, h1, h2, by rw [h3, Sym2.eq_swap]⟩

/-- **Every colour is `0` or `±(p+1)` for the path `p` carrying it.**  The magnitude names the
path, which is what makes properness a comparison of path indices. -/
theorem ocol_abs (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (u v : Option (ZMod (2 * m))) :
    ocol m sg u v = 0 ∨ ocol m sg u v = (((olocate m u v).1 : ℤ) + 1)
      ∨ ocol m sg u v = -(((olocate m u v).1 : ℤ) + 1) := by
  classical
  rw [ocol]
  split_ifs with h1 h2
  · rcases osgn_eq_one_or m hsg (olocate m u v).1 (olocate m u v).2 with hc | hc
    · exact Or.inr (Or.inl (by rw [ocolFwd, hc]; ring))
    · exact Or.inr (Or.inr (by rw [ocolFwd, hc]; ring))
  · rcases osgn_eq_one_or m hsg (olocate m u v).1 ((olocate m u v).2 + 1) with hc | hc
    · exact Or.inr (Or.inr (by rw [ocolBwd, hc]; ring))
    · exact Or.inr (Or.inl (by rw [ocolBwd, hc]; ring))
  · exact Or.inl rfl

/-- **Every colour lies in the colour set.**  Unlike the even case this needs no `u ≠ v`: the
matching branch supplies `0`, which is a legitimate colour when the order is odd. -/
theorem ocol_mem (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (u v : Option (ZMod (2 * m))) :
    ocol m sg u v ∈ M (2 * m + 1) := by
  classical
  rw [ocol]
  split_ifs with h1 h2
  · exact ocolFwd_mem m hsg (olocate_spec m h1).1 _
  · exact ocolBwd_mem m hsg (olocate_spec m h1).1 _
  · exact zero_mem_M_odd m

end Odd

/-! ### Balance and properness for the odd clique

Balance runs as in the even case, with one extra branch: a matching edge gives `0` at both ends and
`0 = -σ·0` for either sign, so the condition holds without any appeal to the signature.

Properness splits three ways at a vertex `u`, and only the first is the even argument:
  * both incidences on path edges — same-path means `u` is internal, so the two colours are
    negatives of a nonzero number; different paths means different magnitudes;
  * one path, one matching — the matching gives `0` and a path colour is never `0`;
  * both matching — impossible, because `v = u + m` determines `v`.
-/

namespace Odd

open Walecki

theorem ocol_eq_fwd (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ)
    {u v : Option (ZMod (2 * m))} (hp : IsPathEdge m u v)
    (h : ov m (olocate m u v).1 (olocate m u v).2 = u) :
    ocol m sg u v = ocolFwd m sg (olocate m u v).1 (olocate m u v).2 := by
  classical
  rw [ocol, if_pos hp, if_pos h]

theorem ocol_eq_bwd (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ)
    {u v : Option (ZMod (2 * m))} (hp : IsPathEdge m u v)
    (h : ¬ ov m (olocate m u v).1 (olocate m u v).2 = u) :
    ocol m sg u v = ocolBwd m sg (olocate m u v).1 (olocate m u v).2 := by
  classical
  rw [ocol, if_pos hp, if_neg h]

theorem ocol_eq_zero (m : ℕ) (sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ)
    {u v : Option (ZMod (2 * m))} (hp : ¬ IsPathEdge m u v) : ocol m sg u v = 0 := by
  classical
  rw [ocol, if_neg hp]

/-- The two ends of the located edge, in whichever order they occur. -/
theorem olocate_ends (m : ℕ) {u v : Option (ZMod (2 * m))} (h : IsPathEdge m u v) :
    (ov m (olocate m u v).1 (olocate m u v).2 = u
        ∧ ov m (olocate m u v).1 ((olocate m u v).2 + 1) = v)
      ∨ (ov m (olocate m u v).1 (olocate m u v).2 = v
        ∧ ov m (olocate m u v).1 ((olocate m u v).2 + 1) = u) := by
  obtain ⟨-, -, he⟩ := olocate_spec m h
  rw [oedge] at he
  exact Sym2.eq_iff.mp he

theorem ocolFwd_ne_zero (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (p s : ℕ) : ocolFwd m sg p s ≠ 0 := by
  rw [ocolFwd]
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rcases osgn_eq_one_or m hsg p s with hc | hc <;> rw [hc] <;> intro hcon <;> linarith

/-- A path colour is never `0`; `0` belongs to the matching alone. -/
theorem ocol_ne_zero (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) {u v : Option (ZMod (2 * m))}
    (hp : IsPathEdge m u v) : ocol m sg u v ≠ 0 := by
  classical
  rw [ocol, if_pos hp]
  have hp0 : (0 : ℤ) ≤ (((olocate m u v).1 : ℕ) : ℤ) := by positivity
  split_ifs with h
  · exact ocolFwd_ne_zero m hsg _ _
  · rw [ocolBwd]
    rcases osgn_eq_one_or m hsg (olocate m u v).1 ((olocate m u v).2 + 1) with hc | hc <;>
      rw [hc] <;> intro hcon <;> linarith

/-- On a path edge the colour is exactly `±(p+1)`: the `0` disjunct of `ocol_abs` cannot occur,
which is what lets properness across different paths be a comparison of path indices. -/
theorem ocol_abs_of_path (m : ℕ) {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) {u v : Option (ZMod (2 * m))}
    (hp : IsPathEdge m u v) :
    ocol m sg u v = (((olocate m u v).1 : ℤ) + 1)
      ∨ ocol m sg u v = -(((olocate m u v).1 : ℤ) + 1) := by
  classical
  rw [ocol, if_pos hp]
  split_ifs with h
  · rcases osgn_eq_one_or m hsg (olocate m u v).1 (olocate m u v).2 with hc | hc
    · exact Or.inl (by rw [ocolFwd, hc]; ring)
    · exact Or.inr (by rw [ocolFwd, hc]; ring)
  · rcases osgn_eq_one_or m hsg (olocate m u v).1 ((olocate m u v).2 + 1) with hc | hc
    · exact Or.inr (by rw [ocolBwd, hc]; ring)
    · exact Or.inl (by rw [ocolBwd, hc]; ring)

/-- **The balance condition on the odd clique.** -/
theorem ocol_balance (m : ℕ) (hm : 0 < m)
    {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x)
    {u v : Option (ZMod (2 * m))} (huv : u ≠ v) :
    ocol m sg u v = -(sg u v) * ocol m sg v u := by
  by_cases hp : IsPathEdge m u v
  · have hp' : IsPathEdge m v u := isPathEdge_symm m hp
    have hloc : olocate m v u = olocate m u v := (olocate_symm m hm hp hp').symm
    rcases olocate_ends m hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hne : ¬ ov m (olocate m v u).1 (olocate m v u).2 = v := by
        rw [hloc, h1]; exact huv
      rw [ocol_eq_fwd m sg hp h1, ocol_eq_bwd m sg hp' hne, hloc]
      have hfe := ocolFwd_eq m hsg (olocate m u v).1 (olocate m u v).2
      rw [h1, h2] at hfe
      exact hfe
    · have hne : ¬ ov m (olocate m u v).1 (olocate m u v).2 = u := by
        rw [h1]; exact fun hc => huv hc.symm
      have hyes : ov m (olocate m v u).1 (olocate m v u).2 = v := by rw [hloc, h1]
      rw [ocol_eq_bwd m sg hp hne, ocol_eq_fwd m sg hp' hyes, hloc]
      have hfe := ocolFwd_eq m hsg (olocate m u v).1 (olocate m u v).2
      rw [h1, h2, hsymm v u] at hfe
      rcases hsg u v with hs | hs
      · rw [hs] at hfe ⊢; linarith
      · rw [hs] at hfe ⊢; linarith
  · have hp' : ¬ IsPathEdge m v u := fun x => hp (isPathEdge_symm m x)
    rw [ocol_eq_zero m sg hp, ocol_eq_zero m sg hp']
    ring

/-- A pair that is not a path edge is a matching pair. -/
theorem antipodal_of_not_isPathEdge (m : ℕ) (hm : 0 < m) {u v : Option (ZMod (2 * m))}
    (huv : u ≠ v) (hp : ¬ IsPathEdge m u v) :
    ∃ a : ZMod (2 * m), u = some a ∧ v = some (a + ((m : ℕ) : ZMod (2 * m))) := by
  rcases oedge_surj m hm huv with h | h
  · exact h
  · exact absurd h hp

/-- **Properness on the odd clique.** -/
theorem ocol_proper (m : ℕ) (hm : 0 < m)
    {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) {u v v' : Option (ZMod (2 * m))}
    (huv : u ≠ v) (huv' : u ≠ v') (hvv : v ≠ v') : ocol m sg u v ≠ ocol m sg u v' := by
  by_cases hpa : IsPathEdge m u v
  · by_cases hpb : IsPathEdge m u v'
    · obtain ⟨-, hsa, hea⟩ := olocate_spec m hpa
      obtain ⟨-, hsb, heb⟩ := olocate_spec m hpb
      have hsame : (olocate m u v).1 = (olocate m u v').1 →
          (olocate m u v).2 = (olocate m u v').2 → False := by
        intro e1 e2
        have hee : oedge m (olocate m u v).1 (olocate m u v).2
            = oedge m (olocate m u v').1 (olocate m u v').2 := by rw [e1, e2]
        rw [hea, heb] at hee
        rcases Sym2.eq_iff.mp hee with ⟨-, hv2⟩ | ⟨hu2, -⟩
        · exact hvv hv2
        · exact huv' hu2
      by_cases hpp : (olocate m u v).1 = (olocate m u v').1
      · rcases olocate_ends m hpa with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases olocate_ends m hpb with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact absurd (ov_inj m _ hm (by omega) (by omega) (by rw [h1, hpp, k1]))
            (fun e => hsame hpp e)
        · have hidx : (olocate m u v).2 = (olocate m u v').2 + 1 :=
            ov_inj m _ hm (by omega) (by omega) (by rw [h1, hpp, k2])
          have hne : ¬ ov m (olocate m u v').1 (olocate m u v').2 = u := by
            rw [k1]; exact fun hc => huv' hc.symm
          rw [ocol_eq_fwd m sg hpa h1, ocol_eq_bwd m sg hpb hne, hpp, hidx,
            ocolBwd_eq_neg_ocolFwd]
          have hz := ocolFwd_ne_zero m hsg (olocate m u v').1 ((olocate m u v').2 + 1)
          intro hc
          exact hz (by linarith)
        · have hidx : (olocate m u v).2 + 1 = (olocate m u v').2 :=
            ov_inj m _ hm (by omega) (by omega) (by rw [h2, hpp, k1])
          have hne : ¬ ov m (olocate m u v).1 (olocate m u v).2 = u := by
            rw [h1]; exact fun hc => huv hc.symm
          rw [ocol_eq_bwd m sg hpa hne, ocol_eq_fwd m sg hpb k1, ← hpp, ← hidx,
            ocolBwd_eq_neg_ocolFwd]
          have hz := ocolFwd_ne_zero m hsg (olocate m u v).1 ((olocate m u v).2 + 1)
          intro hc
          exact hz (by linarith)
        · have hidx : (olocate m u v).2 + 1 = (olocate m u v').2 + 1 :=
            ov_inj m _ hm (by omega) (by omega) (by rw [h2, hpp, k2])
          exact absurd (by omega : (olocate m u v).2 = (olocate m u v').2)
            (fun e => hsame hpp e)
      · intro hcon
        rcases ocol_abs_of_path m hsg hpa with ha | ha <;>
          rcases ocol_abs_of_path m hsg hpb with hb | hb <;>
          rw [ha, hb] at hcon <;> omega
    · rw [ocol_eq_zero m sg hpb]
      exact ocol_ne_zero m hsg hpa
  · by_cases hpb : IsPathEdge m u v'
    · rw [ocol_eq_zero m sg hpa]
      exact fun hc => ocol_ne_zero m hsg hpb hc.symm
    · obtain ⟨a, ha1, ha2⟩ := antipodal_of_not_isPathEdge m hm huv hpa
      obtain ⟨b, hb1, hb2⟩ := antipodal_of_not_isPathEdge m hm huv' hpb
      have hab : a = b := Option.some_injective _ (ha1.symm.trans hb1)
      exact absurd (by rw [ha2, hb2, hab] : v = v') hvv

end Odd

namespace Odd

/-- **A clique of ODD order is signed-colourable with `2m+1` colours, for every signature.**  The
odd half of the construction, packaged like `evenClique`.  Note `mem` discards its `u ≠ v`
hypothesis: on the odd order `0` is a colour, so even the diagonal's junk value is legitimate. -/
noncomputable def oddClique (m : ℕ) (hm : 0 < m)
    {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x) :
    Colouring.CliqueColouring (Option (ZMod (2 * m))) (2 * m + 1) sg where
  col := ocol m sg
  mem u v _ := ocol_mem m hsg u v
  bal u v huv := ocol_balance m hm hsg hsymm huv
  proper u v v' huv huv' hvv := ocol_proper m hm hsg huv huv' hvv

end Odd

/-! ### Which colour is missing, and why the join can match the two cliques

The join needs the two joining vertices to miss colours `x` and `y` with `x = -σ(e)·y`.  `flipAt`
can change a sign but never a magnitude, so `|x| = |y|` has to come from the construction.

It does, and more cheaply than the earlier design note assumed.  The missing colour's magnitude is
`pathOf v + 1` — determined by *which path `v` ends*, and in particular **independent of the
signature**.  So the two cliques, carrying different signatures, still miss colours of the same
magnitude at the same basepoint, and the basepoint may be any vertex rather than `0` specifically.

The mechanism: `v` is internal on every path it does not end, and the two incidences at an internal
vertex are negatives of one another (`colBwd_eq_neg_colFwd`).  So for every path `p` other than
`pathOf v`, *both* signs of `p+1` already occur at `v` — leaving only `±(pathOf v + 1)` available
to be missing. -/

namespace Walecki

/-- `0` ends path `0`. -/
theorem pathOf_zero (m : ℕ) (hm : 0 < m) : pathOf m 0 = 0 := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have h0 : (0 : ZMod (2 * m)).val = 0 := by simp
  rw [pathOf, h0, if_pos hm]

/-- **Every colour of magnitude `p+1`, for a path `p` that `v` does not end, already occurs at
`v`.**  Both signs, because the two incidences at an internal vertex are negatives. -/
theorem exists_both_signs (m : ℕ) (hm : 0 < m) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (v : ZMod (2 * m)) {p : ℕ} (hp : p < m)
    (hne : p ≠ pathOf m v) {c : ℤ} (hc : c = ((p : ℤ) + 1) ∨ c = -((p : ℤ) + 1)) :
    ∃ v', v' ≠ v ∧ col m sg v v' = c := by
  obtain ⟨t, ht, hvt⟩ := w_surj m hm ((p : ℕ) : ZMod (2 * m)) v
  -- `v` does not end path `p`, so its position is interior
  have ht0 : t ≠ 0 := by
    intro h
    exact hne (endpoint_unique m hm v hp (Or.inl (by rw [← hvt, h])))
  have htl : t ≠ 2 * m - 1 := by
    intro h
    exact hne (endpoint_unique m hm v hp (Or.inr (by rw [← hvt, h])))
  -- Bind the equation as a TYPED `have`.  Passing `w_inj m _ …` with the vertex left as `_` makes
  -- the `by` block prove a goal that still contains the metavariable, and it degenerates to
  -- `w m ?i t = w m ?i t` — the rewrite then cannot find its pattern and `omega` sees nothing.
  have hA : w m ((p : ℕ) : ZMod (2 * m)) (t + 1) ≠ v := by
    intro h
    have heq : w m ((p : ℕ) : ZMod (2 * m)) (t + 1) = w m ((p : ℕ) : ZMod (2 * m)) t := by
      rw [h, hvt]
    have hidx := w_inj m ((p : ℕ) : ZMod (2 * m)) (show t + 1 < 2 * m by omega) ht heq
    omega
  have hB : w m ((p : ℕ) : ZMod (2 * m)) (t - 1) ≠ v := by
    intro h
    have heq : w m ((p : ℕ) : ZMod (2 * m)) (t - 1) = w m ((p : ℕ) : ZMod (2 * m)) t := by
      rw [h, hvt]
    have hidx := w_inj m ((p : ℕ) : ZMod (2 * m)) (show t - 1 < 2 * m by omega) ht heq
    omega
  -- the forward incidence
  have hlocA : locate m v (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)) = (p, t) :=
    locate_unique m hm (Ne.symm hA) hp (by omega) (by rw [edge, hvt])
  have hcA : col m sg v (w m ((p : ℕ) : ZMod (2 * m)) (t + 1)) = colFwd m sg p t :=
    col_of_loc_fwd m sg hlocA (by simpa using hvt)
  -- the backward incidence
  have hts : t - 1 + 1 = t := by omega
  have hlocB : locate m v (w m ((p : ℕ) : ZMod (2 * m)) (t - 1)) = (p, t - 1) :=
    locate_unique m hm (Ne.symm hB) hp (by omega)
      (by rw [edge, hts, hvt]; exact Sym2.eq_swap)
  have hcB : col m sg v (w m ((p : ℕ) : ZMod (2 * m)) (t - 1)) = -(colFwd m sg p t) := by
    rw [col_of_loc_bwd m sg hlocB (by simpa using hB), colBwd_eq_neg_colFwd, hts]
  have hfw : colFwd m sg p t = ((p : ℤ) + 1) ∨ colFwd m sg p t = -((p : ℤ) + 1) := by
    rw [colFwd]
    rcases sgn_eq_one_or m hsg p t with h | h
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (by rw [h]; ring)
  rcases hc with rfl | rfl
  · rcases hfw with h | h
    · exact ⟨_, hA, by rw [hcA, h]⟩
    · exact ⟨_, hB, by rw [hcB, h]; ring⟩
  · rcases hfw with h | h
    · exact ⟨_, hB, by rw [hcB, h]⟩
    · exact ⟨_, hA, by rw [hcA, h]⟩

/-- **The colour missing at `v` is `±(pathOf v + 1)`.**  Its magnitude does not depend on the
signature, which is exactly what lets the two cliques be joined. -/
theorem missing_eq (m : ℕ) (hm : 0 < m) {sg : ZMod (2 * m) → ZMod (2 * m) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (v : ZMod (2 * m)) {x : ℤ}
    (hx : x ∈ M (2 * m)) (hmiss : ∀ v', v' ≠ v → col m sg v v' ≠ x) :
    x = (((pathOf m v : ℕ) : ℤ) + 1) ∨ x = -((((pathOf m v : ℕ) : ℤ)) + 1) := by
  rw [mem_M_two_mul] at hx
  obtain ⟨hlo, hhi, hnz⟩ := hx
  have hpv : pathOf m v < m := pathOf_lt m hm v
  by_contra hcon
  obtain ⟨hc1, hc2⟩ := not_or.mp hcon
  have hx1 : x = (x.natAbs : ℤ) ∨ x = -((x.natAbs : ℤ)) := by
    rcases Int.natAbs_eq x with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hn1 : 1 ≤ x.natAbs := by omega
  have hnm : x.natAbs ≤ m := by omega
  have hp : x.natAbs - 1 < m := by omega
  have hne : x.natAbs - 1 ≠ pathOf m v := by
    intro h
    rcases hx1 with hh | hh
    · exact hc1 (by omega)
    · exact hc2 (by omega)
  obtain ⟨v', hv', hcol⟩ := exists_both_signs m hm hsg v hp hne (c := x)
    (by rcases hx1 with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
  exact hmiss v' hv' hcol

end Walecki

namespace Odd

open Walecki

/-- **`∞` misses exactly the colour `0`.**  Every edge at `∞` is a path edge — the matching does
not cover `∞` — and a path colour is never `0`. -/
theorem ocol_infty_ne_zero (m : ℕ) (hm : 0 < m)
    {sg : Option (ZMod (2 * m)) → Option (ZMod (2 * m)) → ℤ}
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) {v : Option (ZMod (2 * m))} (hv : v ≠ none) :
    ocol m sg none v ≠ 0 := by
  refine ocol_ne_zero m hsg ?_
  by_contra hp
  obtain ⟨a, ha1, -⟩ := antipodal_of_not_isPathEdge m hm (Ne.symm hv) hp
  simp at ha1

end Odd
end Principia.MathDB.P361027

namespace Principia.MathDB

/-! ### Moving the missing colour, and the shape of the join

`SignedColouring` conditions everything on **adjacency**, not on `u ≠ v`, which is what makes the
assembly cheap: away from the two joining vertices each half is exactly its clique colouring, and
the only new obligation is at `inl 0` and `inr 0`.

What the joining edge needs is `x = -σ·y` where `x` is missing at `inl 0` and `y` at `inr 0`.
Stage 16 gives `|x| = |y|` for free — the missing magnitude is `pathOf(basepoint) + 1`, which does
not depend on the signature — so the two differ at most in sign, and `flip_missing` supplies the
sign. -/

namespace Colouring

/-- **Flipping a colour class moves the missing colour to its negative.**  Everything of magnitude
`c` is negated, so a colour of that magnitude that was absent is absent in negated form; a colour
of any other magnitude is untouched and cannot become one of magnitude `c`. -/
theorem flip_missing {V : Type*} {c : ℤ} {f : V → V → ℤ} {u : V} {y : ℤ} (hy : |y| = c)
    (hmiss : ∀ v, v ≠ u → f u v ≠ y) : ∀ v, v ≠ u → flip c f u v ≠ -y := by
  intro v hv hcon
  rw [flip] at hcon
  split_ifs at hcon with h
  · exact hmiss v hv (by linarith)
  · exact h (by rw [hcon, abs_neg, hy])

/-- The same, for a bundled clique colouring. -/
theorem CliqueColouring.flipAt_missing {V : Type*} {k : ℕ} {sg : V → V → ℤ}
    (c : CliqueColouring V k sg) (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (d : ℤ)
    {u : V} {y : ℤ} (hy : |y| = d) (hmiss : ∀ v, v ≠ u → c.col u v ≠ y) :
    ∀ v, v ≠ u → (c.flipAt hsg d).col u v ≠ -y :=
  flip_missing hy hmiss

end Colouring

end Principia.MathDB

/-! ### Both constructions, moved onto `Fin n`

The graph's cliques are `Fin (m+1)`; the constructions live on `ZMod (2μ)` and on
`Option (ZMod (2μ))`.  `Fintype.equivOfCardEq` supplies *an* equivalence and `Equiv.atBasepoint`
repairs it into one that sends the chosen basepoint where the join needs it — to `0` in the even
case, to `∞` in the odd one.

Two things about the shape of these statements, each of which cost a build.

**The basepoint is a parameter, not the numeral `0`.**  Writing `0 : Fin n` fails: `Fin n` has an
`OfNat` instance only when `n` is a syntactic successor, and `hn : n = 2 * μ` is a hypothesis, not
a reduction — so the numeral cannot elaborate in the *statement*, where no `subst` has happened
yet.  Taking `u₀ : Fin n` avoids the question, and the caller supplies `0 : Fin (m+1)`, which is
fine because `m+1` *is* a successor.

**The equivalence is obtained, not `let`-bound.**  A `let e := …` leaves occurrences that are
sometimes the body and sometimes the name, and `rw [he0]` then reports it cannot find `e 0` in a
goal displaying exactly `none = e 0`.  `obtain ⟨e, he0⟩ : ∃ e, …` makes `e` genuinely opaque.

Each `subst` below is on `n = 2 * μ` or `n = 2 * μ + 1`, where only the left side is a variable, so
the direction is forced — the case the earlier `subst` trap does not cover. -/

namespace Principia.MathDB.P361027

open Colouring

/-- **Even order.**  The missing colour has magnitude `1` — `missing_eq` with `pathOf_zero` — and
crucially that magnitude does not depend on `sg`. -/
theorem exists_clique_even (n μ : ℕ) (hμ : 0 < μ) (hn : n = 2 * μ) (u₀ : Fin n)
    (sg : Fin n → Fin n → ℤ)
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x) :
    ∃ (c : CliqueColouring (Fin n) n sg) (x : ℤ),
      x ∈ M n ∧ |x| = 1 ∧ ∀ v, v ≠ u₀ → c.col u₀ v ≠ x := by
  subst hn
  haveI : NeZero (2 * μ) := ⟨by omega⟩
  obtain ⟨e, he0⟩ : ∃ e : Fin (2 * μ) ≃ ZMod (2 * μ), e u₀ = 0 := by
    have hcard : Fintype.card (Fin (2 * μ)) = Fintype.card (ZMod (2 * μ)) := by
      simp [ZMod.card]
    exact ⟨(Fintype.equivOfCardEq hcard).atBasepoint u₀ 0,
      Equiv.atBasepoint_apply_self _ _ _⟩
  have hsg' : ∀ x y : ZMod (2 * μ),
      sg (e.symm x) (e.symm y) = 1 ∨ sg (e.symm x) (e.symm y) = -1 := fun x y => hsg _ _
  have hsymm' : ∀ x y : ZMod (2 * μ),
      sg (e.symm x) (e.symm y) = sg (e.symm y) (e.symm x) := fun x y => hsymm _ _
  refine ⟨CliqueColouring.transport e (evenClique μ hμ hsg' hsymm'), ?_⟩
  obtain ⟨x, hxM, hxmiss⟩ :=
    (CliqueColouring.transport e (evenClique μ hμ hsg' hsymm')).exists_missing
      (Fintype.card_fin _) u₀
  refine ⟨x, hxM, ?_, hxmiss⟩
  have hmiss' : ∀ w : ZMod (2 * μ), w ≠ 0 →
      Walecki.col μ (fun a b => sg (e.symm a) (e.symm b)) 0 w ≠ x := by
    intro w hw
    have hv : e.symm w ≠ u₀ := by
      intro hc
      apply hw
      rw [← he0, ← hc, Equiv.apply_symm_apply]
    have h2 : Walecki.col μ (fun a b => sg (e.symm a) (e.symm b)) (e u₀) (e (e.symm w)) ≠ x :=
      hxmiss (e.symm w) hv
    rwa [he0, Equiv.apply_symm_apply] at h2
  rcases Walecki.missing_eq μ hμ hsg' 0 hxM hmiss' with h | h <;>
    rw [Walecki.pathOf_zero μ hμ] at h <;> rw [h] <;> norm_num

/-- **Odd order, at least three.**  The basepoint goes to `∞`, which misses exactly `0` — so on
this side the join needs no sign adjustment at all. -/
theorem exists_clique_odd (n μ : ℕ) (hμ : 0 < μ) (hn : n = 2 * μ + 1) (u₀ : Fin n)
    (sg : Fin n → Fin n → ℤ)
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x) :
    ∃ c : CliqueColouring (Fin n) n sg, ∀ v, v ≠ u₀ → c.col u₀ v ≠ 0 := by
  subst hn
  haveI : NeZero (2 * μ) := ⟨by omega⟩
  obtain ⟨e, he0⟩ : ∃ e : Fin (2 * μ + 1) ≃ Option (ZMod (2 * μ)), e u₀ = none := by
    have hcard : Fintype.card (Fin (2 * μ + 1)) = Fintype.card (Option (ZMod (2 * μ))) := by
      simp [ZMod.card]
    exact ⟨(Fintype.equivOfCardEq hcard).atBasepoint u₀ none,
      Equiv.atBasepoint_apply_self _ _ _⟩
  have hsg' : ∀ x y : Option (ZMod (2 * μ)),
      sg (e.symm x) (e.symm y) = 1 ∨ sg (e.symm x) (e.symm y) = -1 := fun x y => hsg _ _
  have hsymm' : ∀ x y : Option (ZMod (2 * μ)),
      sg (e.symm x) (e.symm y) = sg (e.symm y) (e.symm x) := fun x y => hsymm _ _
  refine ⟨CliqueColouring.transport e (Odd.oddClique μ hμ hsg' hsymm'), ?_⟩
  intro v hv
  have hne : e v ≠ none := by
    intro hc
    exact hv (e.injective (hc.trans he0.symm))
  have h2 : Odd.ocol μ (fun a b => sg (e.symm a) (e.symm b)) (e u₀) (e v) ≠ 0 := by
    rw [he0]
    exact Odd.ocol_infty_ne_zero μ hμ hsg' hne
  exact h2

/-- **Order one.**  No clique edges at all, and `0` is missing at the only vertex vacuously.  This
is the `m = 0` graph — two vertices and one edge — and it is genuinely separate, because
`oddClique` needs `0 < μ`. -/
theorem exists_clique_one (u₀ : Fin 1) (sg : Fin 1 → Fin 1 → ℤ) :
    ∃ c : CliqueColouring (Fin 1) 1 sg, ∀ v, v ≠ u₀ → c.col u₀ v ≠ 0 := by
  refine ⟨⟨fun _ _ => 0, ?_, ?_, ?_⟩, ?_⟩
  · intro u v _
    rw [M]
    norm_num
  · intro u v _
    ring
  · intro u v v' _ _ hvv
    exact absurd (Subsingleton.elim v v') hvv
  · intro v hv
    exact absurd (Subsingleton.elim v u₀) hv

/-- **Every order, uniformly.**  The magnitude of the missing colour depends only on `n`, which is
what lets the two cliques be joined: they carry different signatures but miss colours of equal
magnitude. -/
theorem exists_clique_of_card (n : ℕ) (hn : 0 < n) (u₀ : Fin n) (sg : Fin n → Fin n → ℤ)
    (hsg : ∀ x y, sg x y = 1 ∨ sg x y = -1) (hsymm : ∀ x y, sg x y = sg y x) :
    ∃ (c : CliqueColouring (Fin n) n sg) (x : ℤ),
      x ∈ M n ∧ |x| = (if n % 2 = 0 then 1 else 0) ∧ ∀ v, v ≠ u₀ → c.col u₀ v ≠ x := by
  by_cases hpar : n % 2 = 0
  · obtain ⟨c, x, hxM, hxa, hxm⟩ :=
      exists_clique_even n (n / 2) (by omega) (by omega) u₀ sg hsg hsymm
    exact ⟨c, x, hxM, by rw [if_pos hpar]; exact hxa, hxm⟩
  · have hzero : (0 : ℤ) ∈ M n := by
      rw [M, if_pos (by omega : n % 2 = 1), Finset.mem_Icc]
      constructor <;> omega
    by_cases h1 : n = 1
    · subst h1
      obtain ⟨c, hxm⟩ := exists_clique_one u₀ sg
      exact ⟨c, 0, hzero, by norm_num, hxm⟩
    · obtain ⟨c, hxm⟩ :=
        exists_clique_odd n (n / 2) (by omega) (by omega) u₀ sg hsg hsymm
      exact ⟨c, 0, hzero, by rw [if_neg hpar]; norm_num, hxm⟩
end Principia.MathDB.P361027

/-! ### The assembly

`SignedColouring` conditions `mem`, `bal` and `proper` on **adjacency**, not on `u ≠ v`.  Away from
the two joining vertices each half is therefore verbatim its clique colouring, and the only new
obligations sit at `inl 0` and `inr 0`.

`IsSignature` constrains `s` only on adjacent pairs, while a `CliqueColouring` wants `±1`
everywhere, so each clique is given a diagonal-normalised signature `if a = b then 1 else s …`,
which agrees with `s` on every edge and is `1` on the diagonal that no condition inspects.

The joining edge carries `x` at the `inl` end and `-σ·x` at the `inr` end, where `x` is the colour
missing at `inl 0`.  Balance is then `σ² = 1`, and properness at each joining vertex is exactly the
missing-colour property.  What makes this possible is stage 16: both cliques miss colours of the
*same magnitude*, since that magnitude depends only on the order.  `flipAt` then matches the sign. -/

namespace Principia.MathDB.P361027

open Colouring

/-- **The construction**: a signed `(m+1)`-edge-colouring of `G m`, for every signature. -/
theorem exists_signedColouring (m : ℕ)
    (s : (Fin (m + 1) ⊕ Fin (m + 1)) → (Fin (m + 1) ⊕ Fin (m + 1)) → ℤ)
    (hs : IsSignature (G m) s) :
    Nonempty (SignedColouring (G m) s (m + 1)) := by
  classical
  have hadjL : ∀ a b : Fin (m + 1), a ≠ b → (G m).Adj (Sum.inl a) (Sum.inl b) := by
    intro a b h; rw [G_adj]; exact h
  have hadjR : ∀ a b : Fin (m + 1), a ≠ b → (G m).Adj (Sum.inr a) (Sum.inr b) := by
    intro a b h; rw [G_adj]; exact h
  have hadjJ : (G m).Adj (Sum.inl (0 : Fin (m + 1))) (Sum.inr (0 : Fin (m + 1))) := by
    rw [G_adj]; exact ⟨rfl, rfl⟩
  -- the normalised per-clique signatures, NAMED: `flipAt` needs the same proof term again, and a
  -- `_` there cannot be inferred from the goal.
  have hsgA : ∀ a b : Fin (m + 1),
      (if a = b then (1 : ℤ) else s (Sum.inl a) (Sum.inl b)) = 1 ∨
      (if a = b then (1 : ℤ) else s (Sum.inl a) (Sum.inl b)) = -1 := by
    intro a b
    by_cases h : a = b
    · left; simp [h]
    · rw [if_neg h]; exact hs.sign _ _ (hadjL a b h)
  have hsymmA : ∀ a b : Fin (m + 1),
      (if a = b then (1 : ℤ) else s (Sum.inl a) (Sum.inl b))
        = (if b = a then (1 : ℤ) else s (Sum.inl b) (Sum.inl a)) := by
    intro a b
    by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]; exact hs.symm _ _
  have hsgB : ∀ a b : Fin (m + 1),
      (if a = b then (1 : ℤ) else s (Sum.inr a) (Sum.inr b)) = 1 ∨
      (if a = b then (1 : ℤ) else s (Sum.inr a) (Sum.inr b)) = -1 := by
    intro a b
    by_cases h : a = b
    · left; simp [h]
    · rw [if_neg h]; exact hs.sign _ _ (hadjR a b h)
  have hsymmB : ∀ a b : Fin (m + 1),
      (if a = b then (1 : ℤ) else s (Sum.inr a) (Sum.inr b))
        = (if b = a then (1 : ℤ) else s (Sum.inr b) (Sum.inr a)) := by
    intro a b
    by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]; exact hs.symm _ _
  obtain ⟨cA, x, hxM, hxa, hxm⟩ := exists_clique_of_card (m + 1) (by omega) 0
      (fun a b => if a = b then 1 else s (Sum.inl a) (Sum.inl b)) hsgA hsymmA
  obtain ⟨cB, z, hzM, hza, hzm⟩ := exists_clique_of_card (m + 1) (by omega) 0
      (fun a b => if a = b then 1 else s (Sum.inr a) (Sum.inr b)) hsgB hsymmB
  set σ : ℤ := s (Sum.inl (0 : Fin (m + 1))) (Sum.inr (0 : Fin (m + 1))) with hσdef
  have hσ : σ = 1 ∨ σ = -1 := hs.sign _ _ hadjJ
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> ring
  -- the colour the `inr` clique must miss
  have hyabs : |(-σ * x)| = |x| := by
    rcases hσ with h | h <;> rw [h] <;> simp
  -- match `cB` to it, flipping the class if the signs disagree
  obtain ⟨cB', hzm'⟩ : ∃ c : CliqueColouring (Fin (m + 1)) (m + 1)
      (fun a b => if a = b then 1 else s (Sum.inr a) (Sum.inr b)),
      ∀ v, v ≠ 0 → c.col 0 v ≠ -σ * x := by
    by_cases hcase : z = -σ * x
    · exact ⟨cB, by rw [← hcase]; exact hzm⟩
    · have hzz : z = -(-σ * x) := by
        have h1 : |z| = |(-σ * x)| := by rw [hyabs, hza, hxa]
        rcases abs_eq_abs.mp h1 with h | h
        · exact absurd h hcase
        · exact h
      refine ⟨cB.flipAt hsgB |z|, ?_⟩
      have := CliqueColouring.flipAt_missing cB hsgB |z| rfl hzm
      intro v hv hcon
      exact this v hv (by rw [hcon, hzz]; ring)
  -- the colouring
  refine ⟨⟨fun u v => match u, v with
      | Sum.inl a, Sum.inl b => cA.col a b
      | Sum.inr a, Sum.inr b => cB'.col a b
      | Sum.inl _, Sum.inr _ => x
      | Sum.inr _, Sum.inl _ => -σ * x, ?_, ?_, ?_⟩⟩
  · intro u v hadj
    rw [G_adj] at hadj
    match u, v with
    | Sum.inl a, Sum.inl b => exact cA.mem a b hadj
    | Sum.inr a, Sum.inr b => exact cB'.mem a b hadj
    | Sum.inl a, Sum.inr b => exact hxM
    | Sum.inr a, Sum.inl b =>
        -- `σ = 1` gives `-x`, which needs `neg_mem_M`; `σ = -1` gives `x` back, which does not.
        rcases hσ with h | h
        · rw [h]; simpa using neg_mem_M (m + 1) x hxM
        · rw [h]; simpa using hxM
  · intro u v hadj
    rw [G_adj] at hadj
    match u, v with
    | Sum.inl a, Sum.inl b =>
        have h := cA.bal a b hadj
        rwa [if_neg hadj] at h
    | Sum.inr a, Sum.inr b =>
        have h := cB'.bal a b hadj
        rwa [if_neg hadj] at h
    | Sum.inl a, Sum.inr b =>
        obtain ⟨rfl, rfl⟩ := hadj
        show x = -σ * (-σ * x)
        linear_combination (-x) * hσσ
    | Sum.inr a, Sum.inl b =>
        obtain ⟨rfl, rfl⟩ := hadj
        show -σ * x = -(s (Sum.inr (0 : Fin (m + 1))) (Sum.inl (0 : Fin (m + 1)))) * x
        rw [hs.symm]
  · intro u v w hadj1 hadj2 hvw
    rw [G_adj] at hadj1 hadj2
    match u, v, w with
    | Sum.inl a, Sum.inl b, Sum.inl c => exact cA.proper a b c hadj1 hadj2 (by simpa using hvw)
    | Sum.inr a, Sum.inr b, Sum.inr c => exact cB'.proper a b c hadj1 hadj2 (by simpa using hvw)
    | Sum.inl a, Sum.inl b, Sum.inr c =>
        obtain ⟨rfl, rfl⟩ := hadj2
        exact hxm b (Ne.symm hadj1)
    | Sum.inl a, Sum.inr b, Sum.inl c =>
        obtain ⟨rfl, rfl⟩ := hadj1
        exact fun hc => hxm c (Ne.symm hadj2) hc.symm
    | Sum.inl a, Sum.inr b, Sum.inr c =>
        obtain ⟨rfl, rfl⟩ := hadj1
        obtain ⟨-, rfl⟩ := hadj2
        exact absurd rfl hvw
    | Sum.inr a, Sum.inr b, Sum.inl c =>
        obtain ⟨rfl, rfl⟩ := hadj2
        exact hzm' b (Ne.symm hadj1)
    | Sum.inr a, Sum.inl b, Sum.inr c =>
        obtain ⟨rfl, rfl⟩ := hadj1
        exact fun hc => hzm' c (Ne.symm hadj2) hc.symm
    | Sum.inr a, Sum.inl b, Sum.inl c =>
        obtain ⟨rfl, rfl⟩ := hadj1
        obtain ⟨-, rfl⟩ := hadj2
        exact absurd rfl hvw

/-- **`χ'(G_m, σ) = Δ(G_m) = m+1` for every signature.**  The lower bound is the joining vertex's
degree; the upper bound is the construction. -/
theorem chi_eq (m : ℕ)
    (s : (Fin (m + 1) ⊕ Fin (m + 1)) → (Fin (m + 1) ⊕ Fin (m + 1)) → ℤ)
    (hs : IsSignature (G m) s) : chi (G m) s = m + 1 := by
  have hmem : (m + 1) ∈ {k : ℕ | Nonempty (SignedColouring (G m) s k)} :=
    exists_signedColouring m s hs
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨m + 1, hmem⟩ ?_
  rintro k ⟨c⟩
  exact n_le_of_colouring m c

/-- **The conjecture, in the form the source states it.** -/
theorem chi_eq_maxDegree (m : ℕ)
    (s : (Fin (m + 1) ⊕ Fin (m + 1)) → (Fin (m + 1) ⊕ Fin (m + 1)) → ℤ)
    (hs : IsSignature (G m) s) : chi (G m) s = (G m).maxDegree := by
  rw [chi_eq m s hs, maxDegree_eq m]

/-- **Conjecture 26 in full.**  The source states a TWO-PART equality, `χ'(S) = Δ(S) = n`, and
`chi_eq_maxDegree` alone renders only the first part — it never says what `Δ` is.  This states both
at once, which is what the conjecture actually claims. -/
theorem chi_eq_maxDegree_eq_n (m : ℕ)
    (s : (Fin (m + 1) ⊕ Fin (m + 1)) → (Fin (m + 1) ⊕ Fin (m + 1)) → ℤ)
    (hs : IsSignature (G m) s) :
    chi (G m) s = (G m).maxDegree ∧ (G m).maxDegree = m + 1 :=
  ⟨chi_eq_maxDegree m s hs, maxDegree_eq m⟩

section Existence

/-! ### Signatures exist

The signed-chromatic results are stated for every `s` with `IsSignature (G m) s`, and nothing
produced one.  The all-`+1` signature is one: symmetric by definition, and `+1` is an allowed
sign on every edge.  It is the unsigned case, which is a legitimate instance rather than a
degenerate one — the theorems hold for every signature, so this makes them say something about
at least the ordinary colouring problem.
-/

/-- **The all-`+1` signature is a signature.** -/
theorem isSignature_one {W : Type*} (Gr : SimpleGraph W) :
    IsSignature Gr (fun _ _ => (1 : ℤ)) where
  symm := fun _ _ => rfl
  sign := fun _ _ _ => Or.inl rfl

/-- **`IsSignature` is inhabited** for every graph. -/
theorem exists_isSignature {W : Type*} (Gr : SimpleGraph W) :
    ∃ s : W → W → ℤ, IsSignature Gr s :=
  ⟨fun _ _ => 1, isSignature_one Gr⟩

end Existence

end Principia.MathDB.P361027
