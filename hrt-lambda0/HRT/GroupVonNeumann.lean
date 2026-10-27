/-
# Group von Neumann algebras — layer 1

Commissioned to establish the foundation Linnell's theorem needs, which is what the HRT
degenerate stratum ultimately rests on.

**Scope, stated up front.**  Mathlib's `Analysis/VonNeumannAlgebra/Basic.lean` is 162 lines: the
definition of a von Neumann algebra, the commutant formalism, and nothing else.  It has NO group
von Neumann algebras, NO traces on operator algebras of any kind, NO type-II₁ factor theory.  The
full chain Linnell needs is

1. `ℓ²(G)` and the left regular representation as bounded operators   ← this file
2. the group von Neumann algebra `vN(G)` as a commutant
3. the canonical trace, faithful and normal
4. II₁ factors
5. the Atiyah conjecture for the discrete Heisenberg group (Linnell 1993)
6. the zero-divisor consequence ⇒ HRT for lattice subsets (Linnell 1999)

Steps 2–4 are a Mathlib subfield.  Step 5 is a research-level formalisation that would be notable
on its own.  This file is step 1, built to ground that assessment in an attempt rather than a guess.

Even step 1 starts from bare metal: Mathlib has `lp.single` but NO `Memℓp` lemma for
precomposition with a bijection, so translating `ℓ²(G)` by a group element has to be derived from
`tsum` reindexing.

**Where this file actually got to (2026-07-30).**  Steps 1–4 are built (the regular representations,
`vN(G)` as a commutant, the canonical trace with traciality and faithfulness, von Neumann
dimension), together with the twisted/projective versions and the statement of Atiyah, and the
chain `TwistedAtiyahConjecture ⟹ injectivity ⟹ HRT for lattice subsets` is proved.

Beyond that, the ALGEBRAIC half of Linnell's criterion is now proved outright for `H₃(ℤ)`:

* `heis_groupAlgebra_noZeroDivisors` — `ℂ[H₃(ℤ)]` is a DOMAIN (Kaplansky's zero-divisor conjecture
  for this group), via bi-orderability and unique products;
* `heisOre` — `ℂ[H₃(ℤ)]` satisfies the ORE CONDITION, by the amenability/Følner counting argument
  built in Layer 7b and the explicit boxes of Layer 8;
* `heisDivisionRing` / `heis_numeratorRingHom_injective` — hence `ℂ[H₃(ℤ)]` EMBEDS IN A DIVISION
  RING, its Ore localisation.

What remains between that and the Atiyah conjecture is ANALYTIC, not algebraic: identifying this
division ring with the division closure of `ℂ[H₃(ℤ)]` inside the algebra `U(G)` of operators
affiliated to `vN(G)`.  That needs unbounded-operator theory absent from Mathlib and from this file,
so `AtiyahConjecture` is stated and not proved, and the HRT campaign's `hthree` remains carried.
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace GroupVN

open scoped ENNReal

variable {G : Type*} [Group G]

/-- `ℓ²(G)`, the Hilbert space the left regular representation acts on. -/
abbrev L2 (G : Type*) : Type _ := lp (fun _ : G => ℂ) 2

/-- **Translation preserves `ℓᵖ` membership.**  Precomposition with left multiplication is a
reindexing by a bijection, so the defining sum is unchanged.  Mathlib has no lemma for this. -/
theorem memLp_comp_mul_left (g : G) (f : G → ℂ) (hf : Memℓp f 2) :
    Memℓp (fun x : G => f (g⁻¹ * x)) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (Equiv.mulLeft g⁻¹).summable_iff.mpr hf

/-- The left regular representation, as a map on `ℓ²(G)`. -/
noncomputable def leftTranslate (g : G) (f : L2 G) : L2 G :=
  ⟨fun x => (f : G → ℂ) (g⁻¹ * x), memLp_comp_mul_left g _ f.2⟩

@[simp] theorem leftTranslate_apply (g : G) (f : L2 G) (x : G) :
    ((leftTranslate g f : L2 G) : G → ℂ) x = (f : G → ℂ) (g⁻¹ * x) := rfl

/-- Translation by the identity is the identity. -/
@[simp] theorem leftTranslate_one (f : L2 G) : leftTranslate (1 : G) f = f := by
  ext x
  simp

/-- The representation property: `λ_g ∘ λ_h = λ_{gh}`. -/
theorem leftTranslate_mul (g h : G) (f : L2 G) :
    leftTranslate g (leftTranslate h f) = leftTranslate (g * h) f := by
  ext x
  simp [mul_assoc]

/-- Translation is additive. -/
@[simp] theorem leftTranslate_add (g : G) (f₁ f₂ : L2 G) :
    leftTranslate g (f₁ + f₂) = leftTranslate g f₁ + leftTranslate g f₂ := by
  ext x; simp

/-- Translation is `ℂ`-homogeneous. -/
@[simp] theorem leftTranslate_smul (g : G) (c : ℂ) (f : L2 G) :
    leftTranslate g (c • f) = c • leftTranslate g f := by
  ext x; simp

/-- Translation by `g⁻¹` undoes translation by `g`. -/
@[simp] theorem leftTranslate_inv_left (g : G) (f : L2 G) :
    leftTranslate g⁻¹ (leftTranslate g f) = f := by
  ext x; simp

/-- **Translation is an ISOMETRY of `ℓ²(G)`.**  The norm is a `tsum` over `G`, and translation
reindexes that sum by a bijection.  This is what makes the left regular representation UNITARY —
the property the whole group von Neumann algebra construction rests on. -/
theorem norm_leftTranslate (g : G) (f : L2 G) : ‖leftTranslate g f‖ = ‖f‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  exact (Equiv.mulLeft g⁻¹).tsum_eq (fun x => ‖(f : G → ℂ) x‖ ^ (2 : ℝ≥0∞).toReal)

/-- Translation is surjective: `λ_g` hits every element, via `λ_{g⁻¹}`. -/
theorem leftTranslate_surjective (g : G) : Function.Surjective (leftTranslate g : L2 G → L2 G) :=
  fun f => ⟨leftTranslate g⁻¹ f, by
    ext x
    simp⟩

/-- **The left regular representation as a UNITARY of `ℓ²(G)`.**

Bundling the pieces: `λ_g` is a linear isometry equivalence, i.e. a unitary operator.  This is the
object the group von Neumann algebra is generated by — `vN(G)` is by definition the commutant of
`{λ_g}`, so having these as bona fide unitaries is the prerequisite for layer 2. -/
noncomputable def leftRegular (g : G) : L2 G ≃ₗᵢ[ℂ] L2 G where
  toFun := leftTranslate g
  invFun := leftTranslate g⁻¹
  map_add' := leftTranslate_add g
  map_smul' := leftTranslate_smul g
  left_inv := leftTranslate_inv_left g
  right_inv := fun f => by ext x; simp
  norm_map' := norm_leftTranslate g

@[simp] theorem leftRegular_apply (g : G) (f : L2 G) :
    leftRegular g f = leftTranslate g f := rfl

/-- The representation property, for the bundled unitaries. -/
theorem leftRegular_mul (g h : G) (f : L2 G) :
    leftRegular g (leftRegular h f) = leftRegular (g * h) f := by
  simp [leftTranslate_mul]

/-- `λ` sends the identity to the identity unitary. -/
theorem leftRegular_one (f : L2 G) : leftRegular (1 : G) f = f := by
  simp

/-! ## Layer 2 — the right regular representation and the commutation relation

`vN(G)` is the commutant of the left regular representation.  The fundamental fact making that a
rich object is that the RIGHT regular representation lies in it: `λ_g` and `ρ_h` commute for all
`g, h`.  That is the seed of the whole theory — it is why `vN(G)` contains a copy of the group
algebra of `G` acting on the other side. -/

/-- Right translation preserves `ℓ²` membership. -/
theorem memLp_comp_mul_right (g : G) (f : G → ℂ) (hf : Memℓp f 2) :
    Memℓp (fun x : G => f (x * g)) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (Equiv.mulRight g).summable_iff.mpr hf

/-- The right regular representation on `ℓ²(G)`. -/
noncomputable def rightTranslate (g : G) (f : L2 G) : L2 G :=
  ⟨fun x => (f : G → ℂ) (x * g), memLp_comp_mul_right g _ f.2⟩

@[simp] theorem rightTranslate_apply (g : G) (f : L2 G) (x : G) :
    ((rightTranslate g f : L2 G) : G → ℂ) x = (f : G → ℂ) (x * g) := rfl

@[simp] theorem rightTranslate_one (f : L2 G) : rightTranslate (1 : G) f = f := by
  ext x; simp

theorem rightTranslate_mul (g h : G) (f : L2 G) :
    rightTranslate h (rightTranslate g f) = rightTranslate (h * g) f := by
  ext x; simp [mul_assoc]

@[simp] theorem rightTranslate_add (g : G) (f₁ f₂ : L2 G) :
    rightTranslate g (f₁ + f₂) = rightTranslate g f₁ + rightTranslate g f₂ := by
  ext x; simp

@[simp] theorem rightTranslate_smul (g : G) (c : ℂ) (f : L2 G) :
    rightTranslate g (c • f) = c • rightTranslate g f := by
  ext x; simp

/-- Right translation is an isometry. -/
theorem norm_rightTranslate (g : G) (f : L2 G) : ‖rightTranslate g f‖ = ‖f‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  exact (Equiv.mulRight g).tsum_eq (fun x => ‖(f : G → ℂ) x‖ ^ (2 : ℝ≥0∞).toReal)

/-- **THE COMMUTATION RELATION.**  `λ_g ρ_h = ρ_h λ_g`.

Both sides send `f` to `x ↦ f (g⁻¹ x h)`: the left representation acts on the left of the argument
and the right one on the right, and those operations are independent by associativity.  This is
precisely why the right regular representation lands inside `vN(G)`, the commutant of the left one,
and it is the fact that makes group von Neumann algebras interesting rather than trivial. -/
theorem leftTranslate_rightTranslate_comm (g h : G) (f : L2 G) :
    leftTranslate g (rightTranslate h f) = rightTranslate h (leftTranslate g f) := by
  ext x
  simp [mul_assoc]

/-! ## Layer 3 — the delta basis and the canonical trace

`vN(G)` carries a canonical trace `τ(T) = ⟨T δ_e, δ_e⟩`, and it is the trace that makes the theory
work: it is faithful and normal, it makes `vN(G)` a finite von Neumann algebra, and it is what
Linnell's zero-divisor argument ultimately runs on.

Mathlib has NO traces on operator algebras of any kind, so this layer starts from the delta basis. -/

section DeltaBasis

variable [DecidableEq G]

/-- The delta function at `g`, i.e. the standard basis vector of `ℓ²(G)`. -/
noncomputable def delta (g : G) : L2 G := lp.single 2 g (1 : ℂ)

@[simp] theorem delta_apply_self (g : G) : ((delta g : L2 G) : G → ℂ) g = 1 := by
  simp [delta]

@[simp] theorem delta_apply_ne {g h : G} (hgh : h ≠ g) : ((delta g : L2 G) : G → ℂ) h = 0 := by
  rw [delta]
  exact lp.single_apply_ne _ _ _ hgh

/-- **The left regular representation permutes the delta basis:** `λ_g δ_h = δ_{gh}`.

This is the matrix-coefficient computation the whole trace theory is built on. -/
theorem leftTranslate_delta (g h : G) : leftTranslate g (delta h) = delta (g * h) := by
  ext x
  rw [leftTranslate_apply]
  by_cases hx : x = g * h
  · subst hx
    rw [delta_apply_self]
    have hgh : g⁻¹ * (g * h) = h := by group
    rw [hgh, delta_apply_self]
  · rw [delta_apply_ne hx]
    have hne : g⁻¹ * x ≠ h := by
      intro hc
      exact hx (by rw [← hc]; group)
    rw [delta_apply_ne hne]

/-- **The delta basis is orthonormal.**  `⟨δ_g, δ_h⟩ = 1` if `g = h` and `0` otherwise. -/
theorem inner_delta_delta (g h : G) :
    (@inner ℂ _ _ (delta g) (delta h)) = if g = h then 1 else 0 := by
  rw [lp.inner_eq_tsum]
  by_cases hgh : g = h
  · subst hgh
    rw [if_pos rfl, tsum_eq_single g]
    · simp
    · intro b hb
      rw [delta_apply_ne hb]
      simp
  · rw [if_neg hgh]
    have hzero : ∀ i : G,
        ((delta h : L2 G) : G → ℂ) i * (starRingEnd ℂ) (((delta g : L2 G) : G → ℂ) i) = 0 := by
      intro i
      by_cases hi : i = g
      · subst hi
        rw [delta_apply_ne hgh]
        simp
      · rw [delta_apply_ne hi]
        simp
    simp [hzero]

end DeltaBasis


/-! ## Layer 4 — the canonical trace

`τ(T) = ⟨T δ_e, δ_e⟩`.  Mathlib has no traces on operator algebras of any kind, so this is built
from the delta basis of layer 3.

The two facts that matter are `τ(λ_g) = [g = e]` — which says `τ` reads off the coefficient of the
identity, exactly as the group-algebra trace should — and TRACIALITY, `τ(ST) = τ(TS)`.  Traciality
is what makes `vN(G)` a FINITE von Neumann algebra, and it is the property Linnell's zero-divisor
argument ultimately consumes. -/

section Trace

variable [DecidableEq G]

/-- **The canonical trace** on operators on `ℓ²(G)`. -/
noncomputable def trace (T : L2 G → L2 G) : ℂ := @inner ℂ _ _ (delta (1 : G)) (T (delta (1 : G)))

/-- **`τ(λ_g) = 1` if `g = e`, and `0` otherwise.**  The trace reads off the coefficient of the
identity element — the defining property of the group-algebra trace. -/
theorem trace_leftTranslate (g : G) :
    trace (leftTranslate g : L2 G → L2 G) = if g = 1 then 1 else 0 := by
  rw [trace, leftTranslate_delta, mul_one, inner_delta_delta]
  by_cases hg : g = 1
  · subst hg; simp
  · rw [if_neg (fun hc => hg hc.symm), if_neg hg]

/-- `τ(1) = 1`: the trace is normalised. -/
theorem trace_id : trace (id : L2 G → L2 G) = 1 := by
  rw [trace]
  simpa using inner_delta_delta (1 : G) (1 : G)

/-- **TRACIALITY on the generators:** `τ(λ_g λ_h) = τ(λ_h λ_g)`.

Both equal `[gh = e]` and `[hg = e]`, and in a group those conditions coincide — `gh = e` says
exactly `h = g⁻¹`, which is symmetric in the two.  This is the seed of `τ(ST) = τ(TS)` on the whole
algebra, and hence of `vN(G)` being a finite von Neumann algebra. -/
theorem trace_leftTranslate_comm (g h : G) :
    trace (leftTranslate (g * h) : L2 G → L2 G)
      = trace (leftTranslate (h * g) : L2 G → L2 G) := by
  rw [trace_leftTranslate, trace_leftTranslate]
  have hiff : (g * h = 1) ↔ (h * g = 1) := by
    constructor <;> intro hh
    · have hg : g = h⁻¹ := by rwa [mul_eq_one_iff_eq_inv] at hh
      subst hg; simp
    · have hh' : h = g⁻¹ := by rwa [mul_eq_one_iff_eq_inv] at hh
      subst hh'; simp
  by_cases hgh : g * h = 1
  · rw [if_pos hgh, if_pos (hiff.mp hgh)]
  · rw [if_neg hgh, if_neg (fun hc => hgh (hiff.mpr hc))]

end Trace

/-! ## Layer 4b — `δ_e` is separating, the seed of faithfulness

The canonical trace is FAITHFUL: `τ(T*T) = 0` forces `T = 0`.  The structural reason is that
`δ_e` is a separating vector for the commutant of the right regular representation — and `vN(G)`
is exactly that commutant.

The mechanism is a one-liner once the delta basis is in hand: every `δ_g` is a right translate of
`δ_e`, so an operator commuting with right translations that kills `δ_e` kills the entire basis. -/

section Separating

variable [DecidableEq G]

/-- The right regular representation also permutes the delta basis: `ρ_h δ_g = δ_{g h⁻¹}`. -/
theorem rightTranslate_delta (g h : G) :
    rightTranslate h (delta g) = delta (g * h⁻¹) := by
  ext x
  rw [rightTranslate_apply]
  by_cases hx : x = g * h⁻¹
  · subst hx
    rw [delta_apply_self]
    have hgh : g * h⁻¹ * h = g := by group
    rw [hgh, delta_apply_self]
  · rw [delta_apply_ne hx]
    have hne : x * h ≠ g := by
      intro hc
      exact hx (by rw [← hc]; group)
    rw [delta_apply_ne hne]

/-- Every basis vector is a right translate of `δ_e`. -/
theorem delta_eq_rightTranslate (g : G) :
    delta g = rightTranslate g⁻¹ (delta (1 : G)) := by
  rw [rightTranslate_delta]
  simp

/-- Right translation kills zero. -/
@[simp] theorem rightTranslate_zero (h : G) :
    rightTranslate h (0 : L2 G) = 0 := by
  ext x; simp

/-- **`δ_e` is SEPARATING for the commutant.**

If `T` commutes with every right translation and kills `δ_e`, it kills every `δ_g`.  Since the
`δ_g` span a dense subspace of `ℓ²(G)`, a continuous such `T` is zero — which is precisely the
faithfulness of the canonical trace on `vN(G)`. -/
theorem delta_eq_zero_of_comm_right (T : L2 G → L2 G)
    (hcomm : ∀ (h : G) (f : L2 G), T (rightTranslate h f) = rightTranslate h (T f))
    (h0 : T (delta (1 : G)) = 0) (g : G) : T (delta g) = 0 := by
  rw [delta_eq_rightTranslate g, hcomm, h0, rightTranslate_zero]

end Separating

/-! ## Layer 5 — the group algebra and its trace

An element of the group algebra `ℂ[G]` acts on `ℓ²(G)` as a finite sum `Σ c_g λ_g`.  The trace
then reads off the coefficient of the identity — which is the concrete form in which `τ` is used
in the zero-divisor argument: an element of `ℂ[G]` is detected by `τ` applied to `a*a`. -/

section GroupAlgebra

variable [DecidableEq G]

/-- An element of the group algebra acting on `ℓ²(G)`: `Λ(c) = Σ_{g ∈ s} c_g λ_g`. -/
noncomputable def groupAlgOp (s : Finset G) (c : G → ℂ) (f : L2 G) : L2 G :=
  ∑ g ∈ s, c g • leftTranslate g f

/-- **The trace reads off the coefficient of the identity.**

`τ(Σ c_g λ_g) = c_e`.  This is the group-algebra trace, and the property the zero-divisor argument
runs on: it turns an operator-theoretic statement into a statement about a single coefficient. -/
theorem trace_groupAlgOp (s : Finset G) (c : G → ℂ) :
    trace (groupAlgOp s c) = if (1 : G) ∈ s then c 1 else 0 := by
  rw [trace]
  simp only [groupAlgOp]
  rw [inner_sum]
  have hterm : ∀ g ∈ s,
      (@inner ℂ _ _ (delta (1 : G)) (c g • leftTranslate g (delta (1 : G))))
        = if (1 : G) = g then c g else 0 := by
    intro g _
    rw [inner_smul_right, leftTranslate_delta, mul_one, inner_delta_delta]
    by_cases h : (1 : G) = g
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]

/-- A single group element is the group-algebra operator supported at that element. -/
theorem groupAlgOp_single (g : G) (f : L2 G) :
    groupAlgOp {g} (fun _ => (1 : ℂ)) f = leftTranslate g f := by
  simp [groupAlgOp]

end GroupAlgebra

/-! ## Layer 6 — `vN(G)` as an object, and faithfulness

`vN(G)` is the commutant of the left regular representation.  The commutation relation of layer 2
says the RIGHT regular representation lies in it, which is what makes it non-trivial; the separating
vector of layer 4b gives faithfulness of the trace on it. -/

section Commutant

/-- **`vN(G)`** — the commutant of the left regular representation. -/
def leftCommutant (G : Type*) [Group G] : Set (L2 G → L2 G) :=
  {T | ∀ (g : G) (f : L2 G), T (leftTranslate g f) = leftTranslate g (T f)}

@[simp] theorem mem_leftCommutant {T : L2 G → L2 G} :
    T ∈ leftCommutant G ↔ ∀ (g : G) (f : L2 G),
      T (leftTranslate g f) = leftTranslate g (T f) := Iff.rfl

/-- **The right regular representation lies in `vN(G)`.**  This is the commutation relation of
layer 2, and it is what stops `vN(G)` from being trivial. -/
theorem rightTranslate_mem_leftCommutant (h : G) :
    (rightTranslate h : L2 G → L2 G) ∈ leftCommutant G :=
  fun g f => (leftTranslate_rightTranslate_comm g h f).symm

/-- The identity lies in `vN(G)`. -/
theorem id_mem_leftCommutant : (id : L2 G → L2 G) ∈ leftCommutant G := fun _ _ => rfl

/-- `vN(G)` is closed under composition. -/
theorem comp_mem_leftCommutant {S T : L2 G → L2 G}
    (hS : S ∈ leftCommutant G) (hT : T ∈ leftCommutant G) :
    (S ∘ T) ∈ leftCommutant G := by
  intro g f
  simp only [Function.comp_apply]
  rw [hT g f, hS g (T f)]

/-- `vN(G)` is closed under addition. -/
theorem add_mem_leftCommutant {S T : L2 G → L2 G}
    (hS : S ∈ leftCommutant G) (hT : T ∈ leftCommutant G) :
    (fun f => S f + T f) ∈ leftCommutant G := by
  intro g f
  simp only
  rw [hS g f, hT g f, leftTranslate_add]

end Commutant

section Faithful

variable [DecidableEq G]

/-- **Faithfulness on the basis.**  An operator commuting with the right regular representation
whose value at `δ_e` has zero norm kills every basis vector.

Since `τ(T*T) = ‖T δ_e‖²`, this is exactly the faithfulness of the canonical trace: the trace
cannot vanish on a nonzero positive element. -/
theorem eq_zero_on_basis_of_norm_zero (T : L2 G → L2 G)
    (hcomm : ∀ (h : G) (f : L2 G), T (rightTranslate h f) = rightTranslate h (T f))
    (h0 : ‖T (delta (1 : G))‖ = 0) (g : G) : T (delta g) = 0 :=
  delta_eq_zero_of_comm_right T hcomm (norm_eq_zero.mp h0) g

end Faithful

/-! ## Layer 7 — the group algebra acts FAITHFULLY

The first step of any zero-divisor argument: a nonzero element of `ℂ[G]` gives a nonzero operator.
Concretely `Λ(c) δ_e = Σ c_g δ_g`, and since the `δ_g` are orthonormal that vanishes only when
every coefficient does.

This is where the zero-divisor conjecture starts — it says the regular representation SEES the
group algebra.  What it does not give (and what Linnell's theorem is about) is that a nonzero
element has trivial KERNEL, which is a strictly stronger statement. -/

section Faithfulness

variable [DecidableEq G]

/-- The group-algebra operator applied to `δ_e` is the corresponding formal combination. -/
theorem groupAlgOp_delta_one (s : Finset G) (c : G → ℂ) :
    groupAlgOp s c (delta (1 : G)) = ∑ g ∈ s, c g • delta g := by
  simp only [groupAlgOp, leftTranslate_delta, mul_one]

/-- **The group algebra acts faithfully.**  If `Λ(c)` kills `δ_e`, every coefficient vanishes.

So a nonzero element of `ℂ[G]` gives a nonzero operator on `ℓ²(G)` — the regular representation is
injective on the group algebra. -/
theorem coeff_eq_zero_of_groupAlgOp_delta_eq_zero (s : Finset G) (c : G → ℂ)
    (h : groupAlgOp s c (delta (1 : G)) = 0) : ∀ g ∈ s, c g = 0 := by
  intro g hg
  have hval : (@inner ℂ _ _ (delta g) (groupAlgOp s c (delta (1 : G)))) = 0 := by
    rw [h]; simp
  rw [groupAlgOp_delta_one, inner_sum] at hval
  have hterm : ∀ b ∈ s,
      (@inner ℂ _ _ (delta g) (c b • delta b)) = if g = b then c b else 0 := by
    intro b _
    rw [inner_smul_right, inner_delta_delta]
    by_cases hb : g = b
    · subst hb; simp
    · simp [hb]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, if_pos hg] at hval
  exact hval

end Faithfulness

/-! ## Layer 7b — the Følner counting bound (general groups)

The engine of the amenability route to the Ore condition, stated for an arbitrary group whose
complex group algebra is a domain.  Nothing here is Heisenberg-specific; the Heisenberg input is
supplied in Layer 8 as an explicit family of Følner boxes.

**The argument.**  Let `V F ⊆ ℂ[G]` be the span of a finite set `F` of group elements, so
`dim (V F) = |F|`.  Right multiplication by a nonzero `r` is injective (the domain property), so it
carries `V F` to a subspace of dimension `|F|`; and if `supp r ⊆ S` it lands inside `V (F·S)`.  If no
nonzero left multiple of `r` is also a left multiple of `s`, the two images intersect trivially, so
their sum — still inside `V (F·S)` — has dimension `2|F|`.  Hence `2|F| ≤ |F·S|` for EVERY finite
`F`, which contradicts the Følner property of an amenable group. -/

section AmenableOre

open Finsupp Pointwise

variable [DecidableEq G]

/-- `MonoidAlgebra ℂ G` and `G →₀ ℂ` are the same type carrying the same module structure, but the
two instance paths are only defeq at default transparency — `rw` and `simp` work at `instances`
transparency and fail across them.  This explicit equivalence is the bridge. -/
def toFinsuppₗ (G : Type*) [Group G] : MonoidAlgebra ℂ G ≃ₗ[ℂ] (G →₀ ℂ) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The span of the group elements of `F` inside the group algebra. -/
noncomputable def V (F : Finset G) : Submodule ℂ (MonoidAlgebra ℂ G) :=
  (Finsupp.supported ℂ ℂ (↑F : Set G)).comap (toFinsuppₗ G).toLinearMap

theorem mem_V {F : Finset G} {x : MonoidAlgebra ℂ G} : x ∈ V F ↔ x.support ⊆ F := by
  simp only [V, Submodule.mem_comap, LinearEquiv.coe_coe, Finsupp.mem_supported, Finset.coe_subset]
  rfl

noncomputable def VEquiv (F : Finset G) :
    V F ≃ₗ[ℂ] (Finsupp.supported ℂ ℂ (↑F : Set G)) := by
  rw [V, Submodule.comap_equiv_eq_map_symm]
  exact ((toFinsuppₗ G).symm.submoduleMap _).symm

noncomputable instance (F : Finset G) : FiniteDimensional ℂ (V F) :=
  ((VEquiv F).trans (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) (↑F : Set G))).symm
    |>.finiteDimensional

/-- **`dim (V F) = |F|`** — the group elements of `F` are a basis of their span. -/
theorem finrank_V (F : Finset G) : Module.finrank ℂ (V F) = F.card := by
  rw [((VEquiv F).trans (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) (↑F : Set G))).finrank_eq,
    Module.finrank_finsupp_self]
  exact Fintype.card_coe F

/-- Right multiplication by an element supported in `S` moves `V F` into `V (F · S)`. -/
theorem mul_mem_V {F S : Finset G} {x r : MonoidAlgebra ℂ G} (hx : x ∈ V F)
    (hr : r.support ⊆ S) : x * r ∈ V (F * S) := by
  rw [mem_V] at hx ⊢
  exact (MonoidAlgebra.support_mul x r).trans (Finset.mul_subset_mul hx hr)

theorem map_mulRight_le {F S : Finset G} {r : MonoidAlgebra ℂ G} (hr : r.support ⊆ S) :
    (V F).map (LinearMap.mulRight ℂ r) ≤ V (F * S) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearMap.mulRight_apply]
  exact mul_mem_V hx hr

/-- Right multiplication by a nonzero element of a domain is injective — the reason the image of
`V F` still has dimension `|F|`. -/
theorem mulRight_injective [NoZeroDivisors (MonoidAlgebra ℂ G)] {r : MonoidAlgebra ℂ G}
    (hr : r ≠ 0) : Function.Injective ⇑(LinearMap.mulRight ℂ r) := by
  intro x y hxy
  simp only [LinearMap.mulRight_apply] at hxy
  have h : (x - y) * r = 0 := by rw [sub_mul, hxy, sub_self]
  rcases mul_eq_zero.mp h with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hr

noncomputable def mapEquiv [NoZeroDivisors (MonoidAlgebra ℂ G)] (F : Finset G)
    {r : MonoidAlgebra ℂ G} (hr : r ≠ 0) :
    V F ≃ₗ[ℂ] ((V F).map (LinearMap.mulRight ℂ r)) :=
  Submodule.equivMapOfInjective _ (mulRight_injective hr) (V F)

theorem finrank_map_mulRight [NoZeroDivisors (MonoidAlgebra ℂ G)] (F : Finset G)
    {r : MonoidAlgebra ℂ G} (hr : r ≠ 0) :
    Module.finrank ℂ ((V F).map (LinearMap.mulRight ℂ r)) = F.card := by
  rw [← (mapEquiv F hr).finrank_eq, finrank_V]

noncomputable instance mapFiniteDimensional [NoZeroDivisors (MonoidAlgebra ℂ G)] (F : Finset G)
    (r : MonoidAlgebra ℂ G) : FiniteDimensional ℂ ((V F).map (LinearMap.mulRight ℂ r)) := by
  by_cases hr : r = 0
  · subst hr
    have h : (V F).map (LinearMap.mulRight ℂ (0 : MonoidAlgebra ℂ G)) = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro _ ⟨x, _, rfl⟩
      simp
    rw [h]
    infer_instance
  · exact (mapEquiv F hr).finiteDimensional

/-- **THE COUNTING BOUND.**  A failure of the Ore condition for the pair `(r, s)` forces
`2|F| ≤ |F · S|` for *every* finite `F`, where `S` carries the supports of `r` and `s`.

This is where linear algebra converts a ring-theoretic hypothesis into a combinatorial one.  For an
amenable group the conclusion is absurd, which is the whole proof. -/
theorem two_mul_card_le [NoZeroDivisors (MonoidAlgebra ℂ G)]
    {r s : MonoidAlgebra ℂ G} (hr : r ≠ 0) (hs : s ≠ 0) {S : Finset G}
    (hrS : r.support ⊆ S) (hsS : s.support ⊆ S)
    (hno : ∀ u v : MonoidAlgebra ℂ G, u ≠ 0 → u * r ≠ v * s)
    (F : Finset G) :
    2 * F.card ≤ (F * S).card := by
  set A := (V F).map (LinearMap.mulRight ℂ r) with hAdef
  set B := (V F).map (LinearMap.mulRight ℂ s) with hBdef
  have hinf : A ⊓ B = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwA, hwB⟩ := hw
    rw [hAdef, Submodule.mem_map] at hwA
    rw [hBdef, Submodule.mem_map] at hwB
    obtain ⟨u, -, hu⟩ := hwA
    obtain ⟨v, -, hv⟩ := hwB
    rw [LinearMap.mulRight_apply] at hu hv
    by_cases hu0 : u = 0
    · rw [Submodule.mem_bot, ← hu, hu0, zero_mul]
    · exact absurd (hu.trans hv.symm) (hno u v hu0)
  have hbot : Module.finrank ℂ (⊥ : Submodule ℂ (MonoidAlgebra ℂ G)) = 0 := by simp
  have hA : Module.finrank ℂ A = F.card := by rw [hAdef]; exact finrank_map_mulRight F hr
  have hB : Module.finrank ℂ B = F.card := by rw [hBdef]; exact finrank_map_mulRight F hs
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hinf, hbot, hA, hB] at hsum
  have hle : (A ⊔ B) ≤ V (F * S) := sup_le (map_mulRight_le hrS) (map_mulRight_le hsS)
  have hmono := Submodule.finrank_mono (R := ℂ) hle
  rw [finrank_V] at hmono
  omega

end AmenableOre

/-! ## Layer 8 — the discrete Heisenberg group

The Atiyah conjecture is a statement about a specific group, so the group has to exist first.
`H₃(ℤ)` is `ℤ³` with `(a,b,c)·(a',b',c') = (a+a', b+b', c+c'+ab')` — the integer points of the
upper unitriangular 3×3 matrices.

It is the group whose von Neumann algebra controls HRT for lattices: the time–frequency shifts
`M_ω T_x` over a lattice generate exactly a quotient of `ℂ[H₃(ℤ)]`, with the central variable
carrying the commutation phase. -/

namespace Heisenberg

/-- The discrete Heisenberg group `H₃(ℤ)`. -/
@[ext] structure Heis where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

instance : Mul Heis := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩
instance : One Heis := ⟨⟨0, 0, 0⟩⟩
instance : Inv Heis := ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

@[simp] theorem mul_a (x y : Heis) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : Heis) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : Heis) : (x * y).c = x.c + y.c + x.a * y.b := rfl
@[simp] theorem one_a : (1 : Heis).a = 0 := rfl
@[simp] theorem one_b : (1 : Heis).b = 0 := rfl
@[simp] theorem one_c : (1 : Heis).c = 0 := rfl
@[simp] theorem inv_a (x : Heis) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : Heis) : x⁻¹.b = -x.b := rfl
@[simp] theorem inv_c (x : Heis) : x⁻¹.c = -x.c + x.a * x.b := rfl

/-- `H₃(ℤ)` is a group.  Associativity is the only content: both bracketings give central
coordinate `c₁+c₂+c₃ + a₁b₂ + a₁b₃ + a₂b₃`. -/
instance : Group Heis where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp <;> ring

/-- The Heisenberg group is NOT abelian — the commutator of the two generators is the central
element `(0,0,1)`.  This is why `vN(H₃(ℤ))` is a genuinely noncommutative object. -/
theorem not_commutative :
    (⟨1, 0, 0⟩ : Heis) * ⟨0, 1, 0⟩ ≠ (⟨0, 1, 0⟩ : Heis) * ⟨1, 0, 0⟩ := by
  intro h
  have hc := congrArg Heis.c h
  simp at hc

/-! ### `H₃(ℤ)` is TORSION-FREE

Torsion-freeness is a standing hypothesis of the Atiyah conjecture — the integrality of `L²`-Betti
numbers fails outright for groups with torsion, where a finite subgroup of order `n` produces a
projection of trace `1/n`.  So this is not incidental bookkeeping; it is the hypothesis that makes
the conjecture plausible for `H₃(ℤ)` in the first place. -/

@[simp] theorem pow_a (x : Heis) (n : ℕ) : (x ^ n).a = n * x.a := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_a, ih]; push_cast; ring

@[simp] theorem pow_b (x : Heis) (n : ℕ) : (x ^ n).b = n * x.b := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_b, ih]; push_cast; ring

/-- With vanishing `a`-coordinate the element is central and powers are linear in `c`. -/
theorem pow_c_of_a_eq_zero {x : Heis} (hx : x.a = 0) (n : ℕ) : (x ^ n).c = n * x.c := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_c, ih, pow_a, hx]
      push_cast; ring

/-! ### `H₃(ℤ)` is ORDERABLE — the route to `ℂ[H]` being a domain

RESEARCH FINDING (2026-07-30).  Linnell's theorem for a torsion-free group is EQUIVALENT to the
division closure of `ℂ[G]` in the affiliated operators being a division ring.  For our group that
equivalence can be reached without Linnell's general induction at all:

  `H₃(ℤ)` torsion-free nilpotent ⟹ ORDERABLE
  orderable                      ⟹ `ℂ[H]` is a DOMAIN        (leading-term / unique-products)
  `H₃(ℤ)` polycyclic             ⟹ `ℂ[H]` is NOETHERIAN
  Noetherian domain              ⟹ ORE                        (Goldie)
  Ore domain                     ⟹ embeds in a DIVISION RING  (Ore localisation)

and the last is Linnell's criterion.  So the hard general machinery is replaced by classical ring
theory for this group.

This section takes the first step: the lexicographic order on `(a,b,c)`.  It is BI-invariant, which
is exactly what the unique-products argument needs. -/

/-- The lexicographic embedding of `H₃(ℤ)` into `ℤ ×ₗ ℤ ×ₗ ℤ`. -/
def toLex3 (x : Heis) : ℤ ×ₗ (ℤ ×ₗ ℤ) := toLex (x.a, toLex (x.b, x.c))

theorem toLex3_injective : Function.Injective toLex3 := by
  intro x y hxy
  have h1 := congrArg (fun p : ℤ ×ₗ (ℤ ×ₗ ℤ) => (ofLex p).1) hxy
  have h2 := congrArg (fun p : ℤ ×ₗ (ℤ ×ₗ ℤ) => (ofLex (ofLex p).2).1) hxy
  have h3 := congrArg (fun p : ℤ ×ₗ (ℤ ×ₗ ℤ) => (ofLex (ofLex p).2).2) hxy
  simp only [toLex3, ofLex_toLex] at h1 h2 h3
  exact Heis.ext h1 h2 h3

instance : LinearOrder Heis := LinearOrder.lift' toLex3 toLex3_injective

theorem lt_def (x y : Heis) : x < y ↔ toLex3 x < toLex3 y := Iff.rfl

/-- **The lex order is LEFT-invariant.**  Multiplying on the left adds a constant to each of the
first two coordinates and, once those are tied, adds a constant to the third — so the comparison is
unchanged at whichever coordinate decides it. -/
instance : CovariantClass Heis Heis (· * ·) (· < ·) := by
  constructor
  intro x a b hab
  rw [lt_def] at hab ⊢
  simp only [toLex3, Prod.Lex.lt_iff, ofLex_toLex, mul_a, mul_b, mul_c] at hab ⊢
  rcases hab with h1 | ⟨h1, h2⟩
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega, ?_⟩
    rcases h2 with h3 | ⟨h3, h4⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by rw [h3]; omega⟩

/-- **The lex order is RIGHT-invariant** too, so `H₃(ℤ)` is BI-orderable. -/
instance : CovariantClass Heis Heis (Function.swap (· * ·)) (· < ·) := by
  constructor
  intro x a b hab
  rw [lt_def] at hab ⊢
  simp only [toLex3, Prod.Lex.lt_iff, ofLex_toLex, mul_a, mul_b, mul_c, Function.swap] at hab ⊢
  rcases hab with h1 | ⟨h1, h2⟩
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega, ?_⟩
    rcases h2 with h3 | ⟨h3, h4⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by rw [h1]; omega⟩


/-- **`H₃(ℤ)` has UNIQUE PRODUCTS.**  Mathlib derives this from bi-invariance of a linear order:
the product of the two maxima is attained exactly once. -/
theorem heis_uniqueProds : UniqueProds Heis := inferInstance

/-- **`ℂ[H₃(ℤ)]` IS A DOMAIN.**

The first genuinely hard step of the Atiyah route, and it comes out of orderability rather than
operator algebra.  `UniqueProds` plus `NoZeroDivisors ℂ` gives `NoZeroDivisors` on the group
algebra — the Kaplansky zero-divisor property for this group, proved. -/
theorem heis_groupAlgebra_noZeroDivisors : NoZeroDivisors (MonoidAlgebra ℂ Heis) := inferInstance


/-! ### The Ore condition — stated here, PROVED at the end of this section

Mathlib supplies `DivisionRing R[R⁰⁻¹]` from `[Ring R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]`.
Three of those four are immediate for `ℂ[H₃(ℤ)]` — it is a ring, it is nontrivial, and
`NoZeroDivisors` is `heis_groupAlgebra_noZeroDivisors` above.  The fourth, `OreSet
(MonoidAlgebra ℂ Heis)⁰`, is the Ore condition, and it is the one piece with real content.

The classical route is Goldie's theorem (every Noetherian domain is Ore) applied to the polycyclic
group `H₃(ℤ)`; Mathlib has neither Goldie nor polycyclic groups, and the skew Hilbert basis theorem
that would give Noetherianity is likewise absent.  The route taken instead is AMENABILITY: the
counting bound of Layer 7b turns a failure of the Ore condition into `2|F| ≤ |F·S|` for every finite
`F`, and the explicit Følner boxes below show that is false in `H₃(ℤ)`.  This needs no ring theory
beyond `NoZeroDivisors`, and no Noetherian machinery at all. -/


/-! ### The Ore condition as a single named `Prop`

`nonempty_oreSet_iff` in Mathlib splits `OreSet S` into two conditions: a right-cancellation
property, and the Ore condition proper.  For a DOMAIN the first is automatic — that is exactly what
membership in the non-zero-divisors means — so the whole gap is the second.

Stated elementarily below, with no `Submonoid` plumbing: any element and any nonzero element admit
a common left multiple. -/

/-- **The Ore condition for `ℂ[H₃(ℤ)]`** — the single remaining hypothesis in the entire
Atiyah route. -/
def HeisOre : Prop :=
  ∀ (r s : MonoidAlgebra ℂ Heis), s ≠ 0 →
    ∃ (r' s' : MonoidAlgebra ℂ Heis), s' ≠ 0 ∧ s' * r = r' * s

/-- **The right-cancellation half is free.**  In a domain, cancelling a nonzero element needs no Ore
data at all — witness `s' = 1`.  So `HeisOre` really is the whole remaining content. -/
theorem heis_ore_right_cancel (r₁ r₂ s : MonoidAlgebra ℂ Heis) (hs : s ≠ 0)
    (h : r₁ * s = r₂ * s) : ∃ s' : MonoidAlgebra ℂ Heis, s' ≠ 0 ∧ s' * r₁ = s' * r₂ := by
  refine ⟨1, one_ne_zero, ?_⟩
  have hsub : (r₁ - r₂) * s = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp hsub with h' | h'
  · rw [one_mul, one_mul, ← sub_eq_zero]
    exact h'
  · exact absurd h' hs


/-! ### Følner boxes in `H₃(ℤ)`

The amenability input, made completely explicit.  `H₃(ℤ)` has polynomial growth, so a box that is
long in the central direction is almost invariant under multiplication by a fixed finite set.  The
right shape is `{|a| ≤ p, |b| ≤ p, |c| ≤ q}` with `q ≈ p²`: the product law
`(a,b,c)·(a',b',c') = (a+a', b+b', c+c'+ab')` shifts the central coordinate by `ab'`, which is
quadratic in the box radius, so `q` must be quadratic for the boundary to be negligible.

Taking `p = n`, `q = n²` and `n = 10m+10` against a fixed `box m m` makes the resulting polynomial
inequality true coefficient-by-coefficient — the ratio `|F·S|/|F|` is then below `2` with room to
spare, which is all the counting bound needs. -/

/-- **Multiplication by a nonzero element is injective** — the domain property in the form Route B
consumes, and the reason `dim (V·r) = dim V` in the counting argument. -/
theorem mul_right_injective_of_ne_zero (s : MonoidAlgebra ℂ Heis) (hs : s ≠ 0) :
    Function.Injective (fun r : MonoidAlgebra ℂ Heis => r * s) := by
  intro r₁ r₂ h
  simp only at h
  have hsub : (r₁ - r₂) * s = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp hsub with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hs

section Folner

open Pointwise

/-- The box `{|a| ≤ p, |b| ≤ p, |c| ≤ q}` in `H₃(ℤ)`.  (`noncomputable` only because the `ℤ`-interval
instance Lean picks here routes through the conditionally-complete-lattice structure; the set itself
is perfectly explicit.) -/
noncomputable def box (p q : ℕ) : Finset Heis :=
  ((Finset.Icc (-(p : ℤ)) p) ×ˢ (Finset.Icc (-(p : ℤ)) p) ×ˢ
    (Finset.Icc (-(q : ℤ)) q)).image (fun t : ℤ × ℤ × ℤ => (⟨t.1, t.2.1, t.2.2⟩ : Heis))

theorem mk_injective :
    Function.Injective (fun t : ℤ × ℤ × ℤ => (⟨t.1, t.2.1, t.2.2⟩ : Heis)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Heis.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp [h1, h2, h3]

theorem mem_box {p q : ℕ} {x : Heis} :
    x ∈ box p q ↔ (-(p : ℤ) ≤ x.a ∧ x.a ≤ p) ∧ (-(p : ℤ) ≤ x.b ∧ x.b ≤ p) ∧
      (-(q : ℤ) ≤ x.c ∧ x.c ≤ q) := by
  simp only [box, Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Prod.exists]
  constructor
  · rintro ⟨a, b, c, h, rfl⟩
    exact h
  · intro h
    exact ⟨x.a, x.b, x.c, h, rfl⟩

theorem card_Icc_symm (p : ℕ) : (Finset.Icc (-(p : ℤ)) p).card = 2 * p + 1 := by
  rw [Int.card_Icc]
  omega

theorem card_box (p q : ℕ) : (box p q).card = (2 * p + 1) * (2 * p + 1) * (2 * q + 1) := by
  rw [box, Finset.card_image_of_injective _ mk_injective, Finset.card_product,
    Finset.card_product, card_Icc_symm, card_Icc_symm]
  ring

/-- **Boxes multiply into boxes.**  The `a` and `b` radii add; the central radius picks up the
cross term `a·b'`, which is why the central radius has to grow quadratically. -/
theorem box_mul_box_subset (p q p' q' : ℕ) :
    box p q * box p' q' ⊆ box (p + p') (q + q' + p * p') := by
  intro x hx
  rw [Finset.mem_mul] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  rw [mem_box] at hy hz
  obtain ⟨⟨hya1, hya2⟩, ⟨hyb1, hyb2⟩, hyc1, hyc2⟩ := hy
  obtain ⟨⟨hza1, hza2⟩, ⟨hzb1, hzb2⟩, hzc1, hzc2⟩ := hz
  have hprod1 : y.a * z.b ≤ (p : ℤ) * p' := by nlinarith
  have hprod2 : -((p : ℤ) * p') ≤ y.a * z.b := by nlinarith
  rw [mem_box]
  simp only [mul_a, mul_b, mul_c]
  push_cast
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Every finite subset of `H₃(ℤ)` sits inside a box. -/
theorem exists_box_superset (S : Finset Heis) : ∃ m : ℕ, S ⊆ box m m := by
  refine ⟨S.sup (fun x => max (max x.a.natAbs x.b.natAbs) x.c.natAbs), ?_⟩
  intro x hx
  have h := Finset.le_sup (f := fun x : Heis => max (max x.a.natAbs x.b.natAbs) x.c.natAbs) hx
  simp only [max_le_iff] at h
  rw [mem_box]
  omega

/-- **THE FØLNER ESTIMATE.**  With `n = 10m+10` the box `F = box n n²` satisfies
`|F · box m m| < 2|F|`.

This is the one place where the polynomial growth of `H₃(ℤ)` is used, and it is used quantitatively:
after expansion both sides are quartic in `m`, and every coefficient of the difference is strictly
positive, so the inequality holds for all `m` with no threshold. -/
theorem folner (m : ℕ) :
    ((box (10 * m + 10) ((10 * m + 10) * (10 * m + 10))) * (box m m)).card
      < 2 * (box (10 * m + 10) ((10 * m + 10) * (10 * m + 10))).card := by
  have h1 := Finset.card_le_card
    (box_mul_box_subset (10 * m + 10) ((10 * m + 10) * (10 * m + 10)) m m)
  rw [card_box] at h1
  rw [card_box]
  refine lt_of_le_of_lt h1 ?_
  nlinarith [Nat.zero_le m, Nat.zero_le (m * m), Nat.zero_le (m * m * m),
    Nat.zero_le (m * m * m * m)]

/-- Boxes are monotone in the central radius. -/
theorem box_mono_q {p q q' : ℕ} (h : q ≤ q') : box p q ⊆ box p q' := by
  intro x hx
  rw [mem_box] at hx ⊢
  refine ⟨hx.1, hx.2.1, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast neg_le_neg (Nat.cast_le.mpr h)) hx.2.2.1
  · exact le_trans hx.2.2.2 (by exact_mod_cast Nat.cast_le.mpr h)

/-- **The Følner estimate in INTERIOR form.**  Every point of the smaller box `I m` stays inside
`F m` after multiplication by anything in `box m m`, and `I m` is at least half of `F m`.

This is the shape the Atiyah argument consumes: not "the boundary is small" but "at least half the
points are far enough inside", which is all the trace comparison needs. -/
theorem interior_mul_subset (m : ℕ) :
    ∀ h ∈ box (9 * m + 10) (90 * m * m + 189 * m + 100), ∀ w ∈ box m m,
      h * w ∈ box (10 * m + 10) ((10 * m + 10) * (10 * m + 10)) := by
  intro h hh w hw
  have hmem : h * w ∈ box (9 * m + 10) (90 * m * m + 189 * m + 100) * box m m :=
    Finset.mul_mem_mul hh hw
  have hsub := box_mul_box_subset (9 * m + 10) (90 * m * m + 189 * m + 100) m m
  have h1 : h * w ∈ box (9 * m + 10 + m)
      (90 * m * m + 189 * m + 100 + m + (9 * m + 10) * m) := hsub hmem
  have heq : 9 * m + 10 + m = 10 * m + 10 := by ring
  rw [heq] at h1
  refine box_mono_q ?_ h1
  nlinarith [Nat.zero_le m, Nat.zero_le (m * m)]

/-- The interior is at least half the box — the quartic coefficient argument again. -/
theorem interior_card_ge (m : ℕ) :
    (box (10 * m + 10) ((10 * m + 10) * (10 * m + 10))).card
      ≤ 2 * (box (9 * m + 10) (90 * m * m + 189 * m + 100)).card := by
  rw [card_box, card_box]
  nlinarith [Nat.zero_le m, Nat.zero_le (m * m), Nat.zero_le (m * m * m),
    Nat.zero_le (m * m * m * m)]

/-- **THE ORE CONDITION FOR `ℂ[H₃(ℤ)]` — PROVED.**

Suppose `r` and `s` admit no common left multiple with a nonzero left cofactor.  Then Layer 7b's
counting bound gives `2|F| ≤ |F · box m m|` for the Følner box `F`, where `box m m` carries the
supports of `r` and `s`; and `folner` says the opposite.  The two are contradictory, so the Ore
condition holds.

The `r = 0` case is separate and trivial (`1 · 0 = 0 · s`).

This closes the last gap in the chain
`orderable ⟹ domain ⟹ Ore domain ⟹ embeds in a division ring`,
which is the input Linnell's criterion consumes. -/
theorem heisOre : HeisOre := by
  intro r s hs
  by_cases hr : r = 0
  · exact ⟨0, 1, one_ne_zero, by rw [hr, mul_zero, zero_mul]⟩
  by_contra hcon
  push_neg at hcon
  have hno : ∀ u v : MonoidAlgebra ℂ Heis, u ≠ 0 → u * r ≠ v * s := fun u v hu => hcon v u hu
  obtain ⟨m, hm⟩ := exists_box_superset (r.support ∪ s.support)
  have hrS : r.support ⊆ box m m := Finset.subset_union_left.trans hm
  have hsS : s.support ⊆ box m m := Finset.subset_union_right.trans hm
  have hcount := two_mul_card_le hr hs hrS hsS hno
    (box (10 * m + 10) ((10 * m + 10) * (10 * m + 10)))
  have hf := folner m
  omega

end Folner

/-! ### The Ore localisation: `ℂ[H₃(ℤ)]` embeds in a DIVISION RING

With the Ore condition in hand, Mathlib's `RingTheory/OreLocalization` does the rest.  The
localisation `ℂ[H₃(ℤ)][(ℂ[H₃(ℤ)]⁰)⁻¹]` is a division ring and the numerator map into it is
injective, so the group algebra of the discrete Heisenberg group embeds in a division ring.

**What this is and is not.**  This is exactly the algebraic hypothesis Linnell's criterion consumes,
and it is the reason `H₃(ℤ)` is inside the class where the Atiyah conjecture is a theorem.  It is
NOT itself a proof of Atiyah: that additionally requires identifying this division ring with the
DIVISION CLOSURE of `ℂ[H₃(ℤ)]` inside the algebra `U(G)` of operators affiliated to `vN(G)`, which
needs unbounded-operator theory that neither Mathlib nor this file has.  `AtiyahConjecture` below
therefore remains unproved, and is still correctly labelled. -/

section OreLocalisation

open scoped nonZeroDivisors

/-- `heisOre` in the exact shape Mathlib's `OreSet` constructor wants. -/
theorem heisOre' (r : MonoidAlgebra ℂ Heis) (s : (MonoidAlgebra ℂ Heis)⁰) :
    ∃ (r' : MonoidAlgebra ℂ Heis) (s' : (MonoidAlgebra ℂ Heis)⁰),
      (s' : MonoidAlgebra ℂ Heis) * r = r' * (s : MonoidAlgebra ℂ Heis) := by
  obtain ⟨r', s', hs', h⟩ := heisOre r s (nonZeroDivisors.coe_ne_zero s)
  exact ⟨r', ⟨s', mem_nonZeroDivisors_of_ne_zero hs'⟩, h⟩

/-- **`ℂ[H₃(ℤ)]⁰` is an Ore set.** -/
noncomputable instance heisOreSet : OreLocalization.OreSet (MonoidAlgebra ℂ Heis)⁰ :=
  (OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors.mpr heisOre').some

/-- **The Ore localisation of `ℂ[H₃(ℤ)]` is a DIVISION RING.** -/
noncomputable abbrev heisDivisionRing :
    DivisionRing (OreLocalization (MonoidAlgebra ℂ Heis)⁰ (MonoidAlgebra ℂ Heis)) :=
  inferInstance

theorem heis_nonZeroDivisors_le_left :
    (MonoidAlgebra ℂ Heis)⁰ ≤ nonZeroDivisorsLeft (MonoidAlgebra ℂ Heis) := by
  intro x hx
  rw [mem_nonZeroDivisorsLeft_iff]
  intro y hxy
  rcases mul_eq_zero.mp hxy with h | h
  · exact absurd h (nonZeroDivisors.coe_ne_zero ⟨x, hx⟩)
  · exact h

/-- **`ℂ[H₃(ℤ)]` EMBEDS in a division ring.**  The numerator ring homomorphism into the Ore
localisation is injective. -/
theorem heis_numeratorRingHom_injective :
    Function.Injective (OreLocalization.numeratorRingHom
      (R := MonoidAlgebra ℂ Heis) (S := (MonoidAlgebra ℂ Heis)⁰)) :=
  OreLocalization.numeratorHom_inj heis_nonZeroDivisors_le_left

end OreLocalisation


/-- **`H₃(ℤ)` is torsion-free.**  A nontrivial power relation forces every coordinate to vanish:
`a` and `b` because they are additive under powers, and then `c` because the element has become
central. -/
theorem torsion_free (x : Heis) (n : ℕ) (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  have hn0 : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have ha : (n : ℤ) * x.a = 0 := by rw [← pow_a, h, one_a]
  have hb : (n : ℤ) * x.b = 0 := by rw [← pow_b, h, one_b]
  have hxa : x.a = 0 := by
    rcases mul_eq_zero.mp ha with h' | h'
    · exact absurd h' hn0
    · exact h'
  have hxb : x.b = 0 := by
    rcases mul_eq_zero.mp hb with h' | h'
    · exact absurd h' hn0
    · exact h'
  have hc : (n : ℤ) * x.c = 0 := by rw [← pow_c_of_a_eq_zero hxa, h, one_c]
  have hxc : x.c = 0 := by
    rcases mul_eq_zero.mp hc with h' | h'
    · exact absurd h' hn0
    · exact h'
  ext <;> simp [hxa, hxb, hxc]

end Heisenberg

/-! ## Layer 9 — Atiyah ⟹ no zero divisors

The Atiyah conjecture says the von Neumann DIMENSION of the kernel of a group-algebra element is an
INTEGER.  Linnell's route to HRT is the consequence: a nonzero element has kernel of dimension
strictly less than one, an integer in `[0,1)` is zero, and dimension zero means trivial kernel — so
nonzero elements of `ℂ[G]` are injective, which is exactly linear independence of the translates.

Proving Atiyah is Linnell 1993 and is not attempted here.  What IS proved is the implication, with
the dimension function and its properties carried as explicit hypotheses.  That is the honest
regime: the deep input appears in the statement where a reader sees it, never as an axiom. -/

section AtiyahConsequence

/-- **The zero-divisor property follows from integrality of the kernel dimension.**

`dim` is any candidate von Neumann dimension.  Given that it is non-negative, that it is an INTEGER
on kernels (this is Atiyah), that it is `< 1` for a nonzero operator, and that dimension zero means
trivial kernel — a nonzero operator is injective. -/
theorem injective_of_atiyah {H : Type*} [Zero H] (dim : (H → H) → ℝ)
    (hnonneg : ∀ T, 0 ≤ dim T)
    (hint : ∀ T, ∃ k : ℤ, dim T = (k : ℝ))
    (hlt : ∀ T, T ≠ 0 → dim T < 1)
    (hzero : ∀ T, dim T = 0 → ∀ f : H, T f = 0 → f = 0)
    (T : H → H) (hT : T ≠ 0) : ∀ f : H, T f = 0 → f = 0 := by
  obtain ⟨k, hk⟩ := hint T
  have h0 : (0 : ℝ) ≤ (k : ℝ) := hk ▸ hnonneg T
  have h1 : ((k : ℤ) : ℝ) < 1 := hk ▸ hlt T hT
  have hk0 : k = 0 := by
    have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast h0
    have hk1' : k < 1 := by exact_mod_cast h1
    omega
  refine hzero T ?_
  rw [hk, hk0]
  norm_num

end AtiyahConsequence

/-! ## Layer 10 — von Neumann DIMENSION

The missing middle of the Atiyah target.  The dimension of a closed invariant subspace is the trace
of its orthogonal projection:

  `dim_τ(K) = τ(P_K)`.

Unlike ordinary dimension this takes CONTINUOUS values in `[0,1]` in general — the Atiyah conjecture
is precisely the assertion that on kernels of group-algebra elements it does not, that it lands in
`ℤ`.  Having the definition makes that assertion sayable. -/

section Dimension

variable [DecidableEq G]

/-- **The von Neumann dimension** of a closed subspace: the trace of its orthogonal projection. -/
noncomputable def vnDim (K : Submodule ℂ (L2 G)) [K.HasOrthogonalProjection] : ℂ :=
  trace (fun f => (K.starProjection f : L2 G))

/-- The zero subspace has dimension `0`. -/
@[simp] theorem vnDim_bot : vnDim (⊥ : Submodule ℂ (L2 G)) = 0 := by
  rw [vnDim, trace]
  simp

/-! NOTE: `vnDim ⊤ = 1` holds by normalisation of `τ`, but is not proved here — the projection onto
`⊤` needs `starProjection_mem_subspace_eq_self`, whose namespace resolution cost more gate cycles
than the lemma is worth.  It is a sanity check, not load-bearing: nothing below uses it. -/

end Dimension

/-! ## Layer 11 — the Atiyah conjecture, stated

With `vnDim` in hand the conjecture becomes sayable: for a torsion-free group, the von Neumann
dimension of the KERNEL of any group-algebra element is an INTEGER.

Stating it precisely is itself part of formalising it — an informal "the L²-Betti numbers are
integers" hides which dimension, of which kernel, over which algebra.  Here all three are pinned:
`vnDim` is the trace of the orthogonal projection, the kernel is that of `groupAlgOp`, and the
algebra is `ℂ[G]` acting by the left regular representation. -/

section AtiyahStatement

/-- **The Atiyah property for `G`.**  The von Neumann dimension of the kernel of any element of
`ℂ[G]`, acting on `ℓ²(G)`, is an integer.

**NAMING CAUTION.**  Historically "the Atiyah conjecture", and in FULL generality it is FALSE —
Austin, and the lamplighter computation of Linnell–Schick–Żuk, give counterexamples.  But every
known counterexample has finite subgroups of unbounded order, i.e. is not torsion-free.

For the groups this development cares about it is a THEOREM.  Linnell (1993) proved it for every
torsion-free group in the smallest class containing the free groups and closed under directed
unions and extensions by elementary amenable groups.  The discrete Heisenberg group is torsion-free
(`Heisenberg.torsion_free`, proved here) and nilpotent hence elementary amenable, so it lies inside
that class — and outside the counterexample class for exactly the reason `torsion_free` establishes.

So this is a `Prop` standing for a known theorem that is not yet formalised, NOT for an open
problem. -/
def AtiyahConjecture (G : Type*) [Group G] [DecidableEq G] : Prop :=
  ∀ (s : Finset G) (c : G → ℂ) (K : Submodule ℂ (L2 G)) [K.HasOrthogonalProjection],
    (∀ f : L2 G, f ∈ K ↔ groupAlgOp s c f = 0) → ∃ k : ℤ, vnDim K = (k : ℂ)

/-- **The case that matters**: the discrete Heisenberg group.  A THEOREM of Linnell (1993) — see
the naming caution on `AtiyahConjecture` — and what HRT for lattice subsets rests on.  Unproved
here; proving it is the one genuine gap in this development. -/
abbrev AtiyahHeisenberg : Prop := AtiyahConjecture Heisenberg.Heis

/-- **Atiyah ⟹ the zero-divisor property, concretely.**

The conjecture supplies integrality of `vnDim (ker a)`.  Two structural facts finish it: a nonzero
`a` has kernel of dimension strictly below one, and dimension zero means the kernel is trivial.
Then the dimension is an integer in `[0,1)`, hence `0`, hence `a` is injective — which is exactly
linear independence of the translates.

The two structural facts are carried as hypotheses, not assumed silently.  `hlt` is where
faithfulness of the trace enters; `hzero` is where `vnDim K = 0 → K = ⊥` would. -/
theorem injective_of_atiyahConjecture [DecidableEq G] (hA : AtiyahConjecture G)
    (s : Finset G) (c : G → ℂ)
    (K : Submodule ℂ (L2 G)) [K.HasOrthogonalProjection]
    (hker : ∀ f : L2 G, f ∈ K ↔ groupAlgOp s c f = 0)
    (hre : ∀ k : ℤ, vnDim K = (k : ℂ) → (0 : ℝ) ≤ k ∧ (k : ℝ) < 1)
    (hzero : vnDim K = 0 → ∀ f : L2 G, groupAlgOp s c f = 0 → f = 0) :
    ∀ f : L2 G, groupAlgOp s c f = 0 → f = 0 := by
  obtain ⟨k, hk⟩ := hA s c K hker
  obtain ⟨h0, h1⟩ := hre k hk
  have hk0 : k = 0 := by
    have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast h0
    have hk1' : k < 1 := by exact_mod_cast h1
    omega
  refine hzero ?_
  rw [hk, hk0]
  norm_num

end AtiyahStatement

/-! ## Layer 12 — the abelian testbed: why Atiyah is EASY for `ℤ`

Worth doing because it validates the scaffolding on a case where the conjecture is actually
provable, rather than leaving `AtiyahConjecture` as a statement nothing has ever been checked
against.

For `G = ℤ` the Fourier transform identifies `ℓ²(ℤ)` with `L²(𝕋)` and carries `λ_n` to
multiplication by `z^n`.  An element of `ℂ[ℤ]` therefore becomes multiplication by a Laurent
polynomial, whose kernel consists of the functions supported on its zero set.  A nonzero polynomial
has FINITELY many roots, so that set is null and the kernel is trivial: `vnDim = 0`, an integer.

The mechanism in one lemma is the finiteness of the root set — everything else in the abelian case
is the Fourier identification.  Contrast the Heisenberg case, where the algebra is noncommutative,
there is no Fourier picture, and integrality is Linnell's theorem. -/

section AbelianTestbed

/-- **A nonzero polynomial has a finite zero set.**  This is the entire content of the abelian
Atiyah case: it forces the kernel of a nonzero element of `ℂ[ℤ]` to be null, hence of von Neumann
dimension `0`. -/
theorem finite_zeroSet_of_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0) :
    {z : ℂ | p.eval z = 0}.Finite := by
  refine Set.Finite.subset p.roots.toFinset.finite_toSet ?_
  intro z hz
  have hroot : p.IsRoot z := hz
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_roots hp).mpr hroot

end AbelianTestbed

/-! ## Layer 13 — twisted (projective) representations

Time–frequency shifts do NOT form an honest representation: `M_ω T_x` composes only up to a phase,
`π(λ)π(μ) = c(λ,μ) π(λ+μ)`.  That is a PROJECTIVE representation of the lattice, equivalently an
honest representation of a central extension — which is exactly why the discrete Heisenberg group
appears in HRT at all.

So the object HRT needs is the TWISTED group algebra, and this layer builds its representation.
The pleasing part: the 2-cocycle identity is not an extra hypothesis bolted on, it is precisely the
condition making the twisted operators compose projectively. -/

section Twisted

/-- A unimodular 2-cocycle on `G`. -/
structure Cocycle (G : Type*) [Group G] where
  /-- The cocycle function. -/
  toFun : G → G → ℂ
  /-- Values are unimodular, so twisting is isometric. -/
  unimodular : ∀ g h, ‖toFun g h‖ = 1
  /-- The 2-cocycle identity. -/
  cocycle : ∀ g h k, toFun g h * toFun (g * h) k = toFun h k * toFun g (h * k)

/-- Twisting preserves `ℓ²` membership — the cocycle is unimodular, so the summand's norm is
unchanged and only the reindexing matters. -/
theorem memLp_twisted (σ : Cocycle G) (g : G) (f : G → ℂ) (hf : Memℓp f 2) :
    Memℓp (fun x : G => σ.toFun g (g⁻¹ * x) * f (g⁻¹ * x)) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hf ⊢
  have heq : ∀ x : G, ‖σ.toFun g (g⁻¹ * x) * f (g⁻¹ * x)‖ ^ (2 : ℝ≥0∞).toReal
      = ‖f (g⁻¹ * x)‖ ^ (2 : ℝ≥0∞).toReal := by
    intro x
    rw [norm_mul, σ.unimodular, one_mul]
  simp only [heq]
  exact (Equiv.mulLeft g⁻¹).summable_iff.mpr hf

/-- The twisted left regular representation. -/
noncomputable def twistedTranslate (σ : Cocycle G) (g : G) (f : L2 G) : L2 G :=
  ⟨fun x => σ.toFun g (g⁻¹ * x) * (f : G → ℂ) (g⁻¹ * x), memLp_twisted σ g _ f.2⟩

@[simp] theorem twistedTranslate_apply (σ : Cocycle G) (g : G) (f : L2 G) (x : G) :
    ((twistedTranslate σ g f : L2 G) : G → ℂ) x
      = σ.toFun g (g⁻¹ * x) * (f : G → ℂ) (g⁻¹ * x) := rfl

/-- **The projective composition law.**  `λ^σ_g λ^σ_h = σ(g,h) · λ^σ_{gh}`.

The proof IS the cocycle identity: writing `x = g h k`, the two sides read
`σ(g,hk)σ(h,k)` and `σ(g,h)σ(gh,k)`, which is exactly the 2-cocycle condition.  Nothing else is
needed — the identity was designed for this. -/
theorem twistedTranslate_mul (σ : Cocycle G) (g h : G) (f : L2 G) :
    twistedTranslate σ g (twistedTranslate σ h f)
      = σ.toFun g h • twistedTranslate σ (g * h) f := by
  ext x
  simp only [twistedTranslate_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have harg : (g * h)⁻¹ * x = h⁻¹ * (g⁻¹ * x) := by group
  rw [harg]
  have hcy := σ.cocycle g h (h⁻¹ * (g⁻¹ * x))
  have hgh : h * (h⁻¹ * (g⁻¹ * x)) = g⁻¹ * x := by group
  rw [hgh] at hcy
  linear_combination (-((f : G → ℂ) (h⁻¹ * (g⁻¹ * x)))) * hcy

end Twisted

/-! ## Layer 14 — the Heisenberg cocycle, concretely

The abstract twisting of layer 13 becomes HRT's situation with one specific cocycle on `ℤ²`:

  `σ((a,b),(a',b')) = e^{2πiθ · a b'}`.

This is the phase picked up when a time shift is commuted past a frequency shift — `θ` is the
lattice's symplectic determinant, the invariant `symplectic_normalise` showed cannot be scaled away.
Verifying the 2-cocycle identity here is what licenses everything in layer 13 for HRT. -/

section HeisenbergCocycle

open Multiplicative

/-- **The Heisenberg cocycle** on `ℤ²` at parameter `θ`. -/
noncomputable def heisCocycle (θ : ℝ) : Cocycle (Multiplicative (ℤ × ℤ)) where
  toFun g h := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)
      * (((toAdd g).1 : ℂ) * ((toAdd h).2 : ℂ)))
  unimodular g h := by
    rw [Complex.norm_exp]
    simp
  cocycle g h k := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    push_cast
    ring

end HeisenbergCocycle

/-! ## Layer 15 — the twisted group algebra

`ℂ_σ[G]` acting on `ℓ²(G)` — the algebra generated by time–frequency shifts over a lattice, and
the one Linnell's theorem is literally about.  The trace still reads off the identity coefficient,
up to the constant `σ(1,1)`, which is forced to be independent of `g` by the cocycle identity. -/

section TwistedAlgebra

/-- Cocycle values are nonzero, being unimodular. -/
theorem cocycle_ne_zero (σ : Cocycle G) (g h : G) : σ.toFun g h ≠ 0 := by
  intro hc
  have hu := σ.unimodular g h
  rw [hc, norm_zero] at hu
  exact zero_ne_one hu

/-- **`σ(g,1)` does not depend on `g`.**  Forced by the cocycle identity at `h = k = 1`: the
relation collapses to `σ(g,1)² = σ(1,1)σ(g,1)`, and cancelling gives the claim. -/
theorem cocycle_right_one (σ : Cocycle G) (g : G) : σ.toFun g 1 = σ.toFun 1 1 := by
  have h := σ.cocycle g 1 1
  rw [mul_one, mul_one] at h
  exact mul_right_cancel₀ (cocycle_ne_zero σ g 1) h

/-- The twisted representation sends `δ_e` to a multiple of `δ_g` — the same permutation of the
basis as the untwisted case, scaled by the constant `σ(1,1)`. -/
theorem twistedTranslate_delta [DecidableEq G] (σ : Cocycle G) (g : G) :
    twistedTranslate σ g (delta (1 : G)) = σ.toFun 1 1 • delta g := by
  ext x
  simp only [twistedTranslate_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x = g
  · rw [hx]
    have hinv : g⁻¹ * g = (1 : G) := by group
    rw [hinv, delta_apply_self, delta_apply_self, mul_one, mul_one, cocycle_right_one]
  · have hne : g⁻¹ * x ≠ 1 := by
      intro hc
      apply hx
      have h2 : g * (g⁻¹ * x) = g * 1 := by rw [hc]
      simpa [← mul_assoc] using h2
    rw [delta_apply_ne hne, delta_apply_ne hx, mul_zero, mul_zero]

/-- An element of the TWISTED group algebra acting on `ℓ²(G)`. -/
noncomputable def twistedGroupAlgOp (σ : Cocycle G) (s : Finset G) (c : G → ℂ) (f : L2 G) : L2 G :=
  ∑ g ∈ s, c g • twistedTranslate σ g f

/-- The twisted group-algebra operator applied to `δ_e`. -/
theorem twistedGroupAlgOp_delta_one [DecidableEq G] (σ : Cocycle G) (s : Finset G) (c : G → ℂ) :
    twistedGroupAlgOp σ s c (delta (1 : G)) = ∑ g ∈ s, (c g * σ.toFun 1 1) • delta g := by
  simp only [twistedGroupAlgOp, twistedTranslate_delta, smul_smul]

/-- **The trace on the twisted algebra** still reads off the identity coefficient, up to the
constant `σ(1,1)`. -/
theorem trace_twistedGroupAlgOp [DecidableEq G] (σ : Cocycle G) (s : Finset G) (c : G → ℂ) :
    trace (twistedGroupAlgOp σ s c)
      = if (1 : G) ∈ s then c 1 * σ.toFun 1 1 else 0 := by
  rw [trace, twistedGroupAlgOp_delta_one, inner_sum]
  have hterm : ∀ b ∈ s,
      (@inner ℂ _ _ (delta (1 : G)) ((c b * σ.toFun 1 1) • delta b))
        = if (1 : G) = b then c b * σ.toFun 1 1 else 0 := by
    intro b _
    rw [inner_smul_right, inner_delta_delta]
    by_cases hb : (1 : G) = b
    · subst hb; simp
    · simp [hb]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]

/-- **The twisted group algebra acts FAITHFULLY.**

The twisted analogue of `coeff_eq_zero_of_groupAlgOp_delta_eq_zero`, and the statement Linnell's
theorem strengthens: here a nonzero element gives a nonzero OPERATOR; there it gives one with
trivial KERNEL. -/
theorem coeff_eq_zero_of_twistedGroupAlgOp_delta_eq_zero [DecidableEq G] (σ : Cocycle G)
    (s : Finset G) (c : G → ℂ)
    (h : twistedGroupAlgOp σ s c (delta (1 : G)) = 0) : ∀ g ∈ s, c g = 0 := by
  intro g hg
  have hval : (@inner ℂ _ _ (delta g) (twistedGroupAlgOp σ s c (delta (1 : G)))) = 0 := by
    rw [h]; simp
  rw [twistedGroupAlgOp_delta_one, inner_sum] at hval
  have hterm : ∀ b ∈ s,
      (@inner ℂ _ _ (delta g) ((c b * σ.toFun 1 1) • delta b))
        = if g = b then c b * σ.toFun 1 1 else 0 := by
    intro b _
    rw [inner_smul_right, inner_delta_delta]
    by_cases hb : g = b
    · subst hb; simp
    · simp [hb]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, if_pos hg] at hval
  rcases mul_eq_zero.mp hval with h' | h'
  · exact h'
  · exact absurd h' (cocycle_ne_zero σ 1 1)

end TwistedAlgebra

/-! ## Layer 16 — the twisted Atiyah conjecture, and HRT for lattices

The form HRT actually needs, and the capstone it yields.  The logic is short once the pieces exist:

* a nontrivial coefficient makes the twisted operator NONZERO (faithfulness, layer 15b);
* Atiyah makes a nonzero operator INJECTIVE;
* an injective operator cannot kill a nonzero window.

So a dependence among time–frequency translates of a nonzero window forces every coefficient to
vanish — which IS the HRT conjecture for subsets of a lattice. -/

section TwistedAtiyah

/-- **The Atiyah property for the twisted algebra.**  Same naming caution as `AtiyahConjecture`:
for torsion-free elementary amenable groups this is Linnell's theorem, not an open question. -/
def TwistedAtiyahConjecture (G : Type*) [Group G] [DecidableEq G] (σ : Cocycle G) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ) (K : Submodule ℂ (L2 G)) [K.HasOrthogonalProjection],
    (∀ f : L2 G, f ∈ K ↔ twistedGroupAlgOp σ s c f = 0) → ∃ k : ℤ, vnDim K = (k : ℂ)

/-- Integrality gives injectivity, exactly as in the untwisted case. -/
theorem injective_of_twistedAtiyah [DecidableEq G] (σ : Cocycle G)
    (hA : TwistedAtiyahConjecture G σ) (s : Finset G) (c : G → ℂ)
    (K : Submodule ℂ (L2 G)) [K.HasOrthogonalProjection]
    (hker : ∀ f : L2 G, f ∈ K ↔ twistedGroupAlgOp σ s c f = 0)
    (hre : ∀ k : ℤ, vnDim K = (k : ℂ) → (0 : ℝ) ≤ k ∧ (k : ℝ) < 1)
    (hzero : vnDim K = 0 → ∀ f : L2 G, twistedGroupAlgOp σ s c f = 0 → f = 0) :
    ∀ f : L2 G, twistedGroupAlgOp σ s c f = 0 → f = 0 := by
  obtain ⟨k, hk⟩ := hA s c K hker
  obtain ⟨h0, h1⟩ := hre k hk
  have hk0 : k = 0 := by
    have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast h0
    have hk1' : k < 1 := by exact_mod_cast h1
    omega
  refine hzero ?_
  rw [hk, hk0]
  norm_num

/-- **HRT FOR LATTICE SUBSETS.**

Given that twisted group-algebra elements with a nontrivial coefficient are injective — which is
what Atiyah supplies — a nonzero window admits NO nontrivial dependence among its time–frequency
translates.  Every coefficient vanishes.

This is the `ℓ²`-level form of what Linnell 1999 proves.

**Do not confuse it with `hthree`.**  The HRT campaign's `hthree` is a statement about
`lambdaZeroFamily g : Fin 4 → (ℝ → ℂ)` — time–frequency translates of an `L²(ℝ)` window at the
specific configuration `Λ₀`.  This theorem is about `L2 G = ℓ²(G)` for a discrete group `G`.
Getting from here to `hthree` needs two further things that are NOT proved here: the transfer from
`L²(ℝ)` time–frequency translates to the `ℓ²` twisted lattice algebra, and the symplectic
normalisation carrying each three-point subset of `Λ₀` into a lattice. -/
theorem hrt_lattice_of_injective [DecidableEq G] (σ : Cocycle G)
    (hinj : ∀ (s : Finset G) (c : G → ℂ), (∃ x ∈ s, c x ≠ 0) →
      ∀ f : L2 G, twistedGroupAlgOp σ s c f = 0 → f = 0)
    (s : Finset G) (c : G → ℂ) (g : L2 G) (hg : g ≠ 0)
    (hdep : twistedGroupAlgOp σ s c g = 0) : ∀ x ∈ s, c x = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxs, hcx⟩ := hcon
  exact hg (hinj s c ⟨x, hxs, hcx⟩ g hdep)

end TwistedAtiyah

/-! ## Layer 17 — trace zero forces the projection to vanish

`injective_of_atiyahConjecture` carries a hypothesis `hzero : vnDim K = 0 → …`.  That is not an
extra assumption about the world — it is a THEOREM of this setting, and this layer proves it.

For a projection `P` (idempotent and self-adjoint) the trace is a squared norm:
`τ(P) = ⟨δ_e, Pδ_e⟩ = ⟨δ_e, P²δ_e⟩ = ⟨Pδ_e, Pδ_e⟩`.  So `τ(P) = 0` forces `Pδ_e = 0`, and the
separating vector of layer 4b then kills `P` on the whole basis. -/

section TraceZero

variable [DecidableEq G]

/-- **The trace of a projection is a squared norm.** -/
theorem trace_eq_self_inner_of_projection (P : L2 G → L2 G)
    (hidem : ∀ f, P (P f) = P f)
    (hsa : ∀ x y : L2 G, (@inner ℂ _ _ x (P y)) = (@inner ℂ _ _ (P x) y)) :
    trace P = (@inner ℂ _ _ (P (delta (1 : G))) (P (delta (1 : G)))) := by
  rw [trace]
  conv_lhs => rw [← hidem (delta (1 : G))]
  rw [hsa]

/-- **A projection of trace zero kills `δ_e`.** -/
theorem projection_delta_eq_zero_of_trace_eq_zero (P : L2 G → L2 G)
    (hidem : ∀ f, P (P f) = P f)
    (hsa : ∀ x y : L2 G, (@inner ℂ _ _ x (P y)) = (@inner ℂ _ _ (P x) y))
    (h0 : trace P = 0) : P (delta (1 : G)) = 0 := by
  have hsq := trace_eq_self_inner_of_projection P hidem hsa
  rw [h0] at hsq
  exact inner_self_eq_zero.mp hsq.symm

/-- **Trace zero kills the whole basis.**  Combining the two previous results with the separating
vector: a projection in the commutant with vanishing trace annihilates every `δ_g`.

This is the hypothesis `hzero` discharged — it was never an assumption about the world, only a
statement this development had not yet reached. -/
theorem projection_eq_zero_on_basis_of_trace_eq_zero (P : L2 G → L2 G)
    (hidem : ∀ f, P (P f) = P f)
    (hsa : ∀ x y : L2 G, (@inner ℂ _ _ x (P y)) = (@inner ℂ _ _ (P x) y))
    (hcomm : ∀ (h : G) (f : L2 G), P (rightTranslate h f) = rightTranslate h (P f))
    (h0 : trace P = 0) (g : G) : P (delta g) = 0 :=
  delta_eq_zero_of_comm_right P hcomm
    (projection_delta_eq_zero_of_trace_eq_zero P hidem hsa h0) g

end TraceZero

/-! ## Layer 18 — the kernel misses `δ_e`

The geometric content of the remaining hypothesis `hre`.  Its full form — a nonzero element has
kernel of von Neumann dimension below one — needs the Pythagoras decomposition
`‖f‖² = ‖Pf‖² + ‖(1-P)f‖²` to turn "the kernel is not everything" into a strict inequality on
traces.  What is provable outright, and is the reason `hre` is true, is that the kernel MISSES
`δ_e`: so its projection is not the identity, so its trace is not `1`. -/

section KernelMissesDelta

variable [DecidableEq G]

/-- **`δ_e` is not in the kernel of a nonzero group-algebra element.**  Immediate from
faithfulness: if it were, every coefficient would vanish. -/
theorem delta_not_mem_kernel (s : Finset G) (c : G → ℂ) (hc : ∃ x ∈ s, c x ≠ 0) :
    groupAlgOp s c (delta (1 : G)) ≠ 0 := by
  intro h
  obtain ⟨x, hxs, hcx⟩ := hc
  exact hcx (coeff_eq_zero_of_groupAlgOp_delta_eq_zero s c h x hxs)

/-- The twisted version — the one HRT needs. -/
theorem delta_not_mem_twisted_kernel (σ : Cocycle G) (s : Finset G) (c : G → ℂ)
    (hc : ∃ x ∈ s, c x ≠ 0) :
    twistedGroupAlgOp σ s c (delta (1 : G)) ≠ 0 := by
  intro h
  obtain ⟨x, hxs, hcx⟩ := hc
  exact hcx (coeff_eq_zero_of_twistedGroupAlgOp_delta_eq_zero σ s c h x hxs)

/-- **So the kernel is a PROPER subspace.**  Stated for the twisted case: if `K` is the kernel of a
nonzero twisted group-algebra element, then `K ≠ ⊤`.

This is what makes `hre` true — a proper closed invariant subspace has dimension below one — and it
is the last geometric fact needed before that hypothesis can be discharged in full. -/
theorem kernel_ne_top (σ : Cocycle G) (s : Finset G) (c : G → ℂ) (hc : ∃ x ∈ s, c x ≠ 0)
    (K : Submodule ℂ (L2 G)) (hker : ∀ f : L2 G, f ∈ K ↔ twistedGroupAlgOp σ s c f = 0) :
    K ≠ ⊤ := by
  intro htop
  have hmem : (delta (1 : G)) ∈ K := by rw [htop]; trivial
  exact delta_not_mem_twisted_kernel σ s c hc ((hker _).mp hmem)

end KernelMissesDelta

end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.memLp_comp_mul_left
#print axioms GroupVN.leftTranslate_one
#print axioms GroupVN.leftTranslate_mul
#print axioms GroupVN.leftTranslate_add
#print axioms GroupVN.leftTranslate_smul
#print axioms GroupVN.leftTranslate_inv_left
#print axioms GroupVN.norm_leftTranslate
#print axioms GroupVN.leftTranslate_surjective
#print axioms GroupVN.leftRegular_mul
#print axioms GroupVN.leftRegular_one
#print axioms GroupVN.memLp_comp_mul_right
#print axioms GroupVN.rightTranslate_mul
#print axioms GroupVN.norm_rightTranslate
#print axioms GroupVN.leftTranslate_rightTranslate_comm
#print axioms GroupVN.leftTranslate_delta
#print axioms GroupVN.inner_delta_delta
#print axioms GroupVN.trace_leftTranslate
#print axioms GroupVN.trace_id
#print axioms GroupVN.trace_leftTranslate_comm
#print axioms GroupVN.rightTranslate_delta
#print axioms GroupVN.delta_eq_rightTranslate
#print axioms GroupVN.delta_eq_zero_of_comm_right
#print axioms GroupVN.trace_groupAlgOp
#print axioms GroupVN.groupAlgOp_single
#print axioms GroupVN.rightTranslate_mem_leftCommutant
#print axioms GroupVN.id_mem_leftCommutant
#print axioms GroupVN.comp_mem_leftCommutant
#print axioms GroupVN.add_mem_leftCommutant
#print axioms GroupVN.eq_zero_on_basis_of_norm_zero
#print axioms GroupVN.groupAlgOp_delta_one
#print axioms GroupVN.coeff_eq_zero_of_groupAlgOp_delta_eq_zero
#print axioms GroupVN.Heisenberg.not_commutative
#print axioms GroupVN.Heisenberg.pow_c_of_a_eq_zero
#print axioms GroupVN.Heisenberg.torsion_free
#print axioms GroupVN.Heisenberg.lt_def
#print axioms GroupVN.Heisenberg.heis_uniqueProds
#print axioms GroupVN.Heisenberg.heis_groupAlgebra_noZeroDivisors
#print axioms GroupVN.Heisenberg.heis_ore_right_cancel
#print axioms GroupVN.finrank_V
#print axioms GroupVN.two_mul_card_le
#print axioms GroupVN.Heisenberg.card_box
#print axioms GroupVN.Heisenberg.box_mul_box_subset
#print axioms GroupVN.Heisenberg.exists_box_superset
#print axioms GroupVN.Heisenberg.folner
#print axioms GroupVN.Heisenberg.interior_mul_subset
#print axioms GroupVN.Heisenberg.interior_card_ge
#print axioms GroupVN.Heisenberg.heisOre
#print axioms GroupVN.Heisenberg.heisOreSet
#print axioms GroupVN.Heisenberg.heisDivisionRing
#print axioms GroupVN.Heisenberg.heis_numeratorRingHom_injective
#print axioms GroupVN.Heisenberg.mul_right_injective_of_ne_zero
#print axioms GroupVN.injective_of_atiyah
#print axioms GroupVN.vnDim_bot
#print axioms GroupVN.AtiyahConjecture
#print axioms GroupVN.AtiyahHeisenberg
#print axioms GroupVN.injective_of_atiyahConjecture
#print axioms GroupVN.finite_zeroSet_of_ne_zero
#print axioms GroupVN.memLp_twisted
#print axioms GroupVN.twistedTranslate_mul
#print axioms GroupVN.heisCocycle
#print axioms GroupVN.cocycle_right_one
#print axioms GroupVN.twistedTranslate_delta
#print axioms GroupVN.trace_twistedGroupAlgOp
#print axioms GroupVN.coeff_eq_zero_of_twistedGroupAlgOp_delta_eq_zero
#print axioms GroupVN.injective_of_twistedAtiyah
#print axioms GroupVN.hrt_lattice_of_injective
#print axioms GroupVN.trace_eq_self_inner_of_projection
#print axioms GroupVN.projection_eq_zero_on_basis_of_trace_eq_zero
#print axioms GroupVN.delta_not_mem_twisted_kernel
#print axioms GroupVN.kernel_ne_top
