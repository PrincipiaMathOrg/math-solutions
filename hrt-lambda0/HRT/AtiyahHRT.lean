/-
# Feeding the twisted theorem into the HRT consumer

`GroupVN.hrt_lattice_of_injective` takes injectivity of `twistedGroupAlgOp` as a HYPOTHESIS and
concludes HRT for lattice subsets.  This file works toward discharging that hypothesis from
`GroupVN.Tw.eq_zero_of_tconv_eq_zero`.

The two operators differ: the file's is a LEFT twisted convolution, mine is a RIGHT one.  For an
ABELIAN group they coincide after transposing the cocycle — and the transpose of a 2-cocycle on an
abelian group is again a 2-cocycle, because substituting `(g,h,k) ↦ (k,h,g)` in the identity and
commuting the products gives exactly the transposed identity.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import AtiyahTwistedMaster

set_option maxHeartbeats 1000000

namespace GroupVN
namespace HRT

open Multiplicative
open scoped Pointwise

/-- The transpose of a normalised unimodular cocycle on a COMMUTATIVE group is again one. -/
noncomputable def transposeCocycle {G : Type*} [CommGroup G] (σ : Cocycle G)
    (h1 : ∀ g, σ.toFun 1 g = 1) (h2 : ∀ g, σ.toFun g 1 = 1) : Tw.UCocycle G where
  toFun g h := σ.toFun h g
  norm_eq g h := σ.unimodular h g
  cocycle g h k := by
    have hσ := σ.cocycle k h g
    -- σ k h * σ (k*h) g = σ h g * σ k (h*g)
    rw [mul_comm k h, mul_comm h g] at hσ
    -- σ k h * σ (h*k) g = σ h g * σ k (g*h)
    exact hσ.symm
  one_left g := h2 g
  one_right g := h1 g

/-- `heisCocycle` is normalised on the left. -/
theorem heisCocycle_one_left (θ : ℝ) (g : Multiplicative (ℤ × ℤ)) :
    (heisCocycle θ).toFun 1 g = 1 := by
  show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)
      * (((toAdd (1 : Multiplicative (ℤ × ℤ))).1 : ℂ) * ((toAdd g).2 : ℂ))) = 1
  norm_num

/-- `heisCocycle` is normalised on the right. -/
theorem heisCocycle_one_right (θ : ℝ) (g : Multiplicative (ℤ × ℤ)) :
    (heisCocycle θ).toFun g 1 = 1 := by
  show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)
      * (((toAdd g).1 : ℂ) * ((toAdd (1 : Multiplicative (ℤ × ℤ))).2 : ℂ))) = 1
  norm_num

/-! ### The operator bridge -/

theorem twistedGroupAlgOp_apply {G : Type*} [CommGroup G] [DecidableEq G] (σ : Cocycle G)
    (s : Finset G) (c : G → ℂ) (f : L2 G) (x : G) :
    ((twistedGroupAlgOp σ s c f : L2 G) : G → ℂ) x
      = ∑ g ∈ s, c g * (σ.toFun g (g⁻¹ * x) * (f : G → ℂ) (g⁻¹ * x)) := by
  rw [twistedGroupAlgOp, lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, twistedTranslate_apply]

/-- **The file's LEFT twisted operator is my RIGHT twisted convolution with the transposed
cocycle** — valid because the group is abelian. -/
theorem twistedGroupAlgOp_eq_tconv {G : Type*} [CommGroup G] [DecidableEq G] (σ : Cocycle G)
    (h1 : ∀ g, σ.toFun 1 g = 1) (h2 : ∀ g, σ.toFun g 1 = 1)
    (s : Finset G) (c : G → ℂ) (f : L2 G)
    (r : MonoidAlgebra ℂ G) (hrs : r.support ⊆ s) (hrc : ∀ g ∈ s, r g = c g) :
    Tw.tconv (transposeCocycle σ h1 h2) (f : G → ℂ) r
      = ((twistedGroupAlgOp σ s c f : L2 G) : G → ℂ) := by
  funext x
  rw [Tw.tconv_eq_sum _ _ r hrs x, twistedGroupAlgOp_apply]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  have hcomm : x * g⁻¹ = g⁻¹ * x := mul_comm _ _
  have hσ : (transposeCocycle σ h1 h2) (x * g⁻¹) g = σ.toFun g (g⁻¹ * x) := by
    show σ.toFun g (x * g⁻¹) = _
    rw [hcomm]
  rw [hσ, hcomm, hrc g hg]
  ring

/-- **HRT'S HYPOTHESIS, DISCHARGED** for an abelian bi-orderable Følner group. -/
theorem twistedGroupAlgOp_injective {G : Type*} [CommGroup G] [DecidableEq G] [LinearOrder G]
    [CovariantClass G G (· * ·) (· < ·)] [CovariantClass G G (Function.swap (· * ·)) (· < ·)]
    (σ : Cocycle G) (h1 : ∀ g, σ.toFun 1 g = 1) (h2 : ∀ g, σ.toFun g 1 = 1)
    (hF : Master.HasFolner G)
    (s : Finset G) (c : G → ℂ) (hc : ∃ x ∈ s, c x ≠ 0) (f : L2 G)
    (hf0 : twistedGroupAlgOp σ s c f = 0) : f = 0 := by
  classical
  obtain ⟨x₀, hx₀s, hx₀⟩ := hc
  set c' : G → ℂ := fun x => if x ∈ s then c x else 0 with hc'
  have hmem : ∀ a : G, c' a ≠ 0 → a ∈ s := by
    intro a ha
    by_contra hcon
    exact ha (by simp [hc', hcon])
  set r : MonoidAlgebra ℂ G := Finsupp.onFinset s c' hmem with hr
  have hrapp : ∀ x, r x = c' x := fun x => rfl
  have hrne : r ≠ 0 := by
    intro hzero
    have hz : r x₀ = 0 := by rw [hzero]; rfl
    rw [hrapp, hc'] at hz
    simp [hx₀s] at hz
    exact hx₀ hz
  have hsupp : r.support ⊆ s := Finsupp.support_onFinset_subset
  have hrc : ∀ g ∈ s, r g = c g := by
    intro g hg
    rw [hrapp, hc']
    simp [hg]
  have hzero : Tw.tconv (transposeCocycle σ h1 h2) (f : G → ℂ) r = 0 := by
    rw [twistedGroupAlgOp_eq_tconv σ h1 h2 s c f r hsupp hrc, hf0]
    rfl
  have hsum : Summable fun x => ‖(f : G → ℂ) x‖ ^ 2 := by
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hmem := (memℓp_gen_iff hp).mp f.2
    simpa [Real.rpow_natCast] using hmem
  have hfun : (f : G → ℂ) = 0 :=
    Tw.eq_zero_of_tconv_eq_zero (transposeCocycle σ h1 h2) r hrne hF _ hsum hzero
  exact Subtype.ext (by rw [hfun]; rfl)

/-! ### The lattice `ℤ²`, on a type synonym

`Multiplicative (ℤ × ℤ)` already carries the PRODUCT order's `LT`, and a direct `LT` instance beats
one derived from a `LinearOrder` no matter the priority — so a lex order cannot be installed on it.
A type synonym has no ambient order, which is the standard fix. -/

section Lattice

/-- The lattice `ℤ²` as a multiplicative group, on a synonym so the lex order is unobstructed. -/
def Lat : Type := Multiplicative (ℤ × ℤ)

instance : CommGroup Lat := inferInstanceAs (CommGroup (Multiplicative (ℤ × ℤ)))
instance : DecidableEq Lat := inferInstanceAs (DecidableEq (Multiplicative (ℤ × ℤ)))

/-- The underlying additive pair. -/
def latPair (g : Lat) : ℤ × ℤ := Multiplicative.toAdd (show Multiplicative (ℤ × ℤ) from g)

@[simp] theorem latPair_mul (g h : Lat) : latPair (g * h) = latPair g + latPair h := rfl

@[simp] theorem latPair_one : latPair 1 = 0 := rfl

theorem latPair_injective : Function.Injective latPair := fun _ _ h => h

/-- The lex embedding. -/
def latLex (g : Lat) : ℤ ×ₗ ℤ := toLex (latPair g)

theorem latLex_injective : Function.Injective latLex := by
  intro x y hxy
  have h1 := congrArg (fun p : ℤ ×ₗ ℤ => (ofLex p).1) hxy
  have h2 := congrArg (fun p : ℤ ×ₗ ℤ => (ofLex p).2) hxy
  simp only [latLex, ofLex_toLex] at h1 h2
  exact latPair_injective (Prod.ext h1 h2)

instance latLinearOrder : LinearOrder Lat := LinearOrder.lift' latLex latLex_injective

theorem lat_lt_def (x y : Lat) : x < y ↔ latLex x < latLex y := Iff.rfl

instance latCov : CovariantClass Lat Lat (· * ·) (· < ·) := by
  constructor
  intro x a b hab
  rw [lat_lt_def] at hab ⊢
  simp only [latLex, latPair_mul, Prod.Lex.lt_iff, ofLex_toLex, Prod.fst_add, Prod.snd_add] at hab ⊢
  rcases hab with h1 | ⟨h1, h2⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩

instance latCovSwap : CovariantClass Lat Lat (Function.swap (· * ·)) (· < ·) := by
  constructor
  intro x a b hab
  rw [lat_lt_def] at hab ⊢
  simp only [latLex, Function.swap, latPair_mul, Prod.Lex.lt_iff, ofLex_toLex, Prod.fst_add,
    Prod.snd_add] at hab ⊢
  rcases hab with h1 | ⟨h1, h2⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩

/-- The square box. -/
noncomputable def zbox (p : ℕ) : Finset Lat :=
  ((Finset.Icc (-(p : ℤ)) p) ×ˢ (Finset.Icc (-(p : ℤ)) p)).map
    ⟨fun t : ℤ × ℤ => (Multiplicative.ofAdd t : Lat), fun a b hab => hab⟩

theorem mem_zbox {p : ℕ} {g : Lat} :
    g ∈ zbox p ↔ (-(p : ℤ) ≤ (latPair g).1 ∧ (latPair g).1 ≤ p) ∧
      (-(p : ℤ) ≤ (latPair g).2 ∧ (latPair g).2 ≤ p) := by
  simp only [zbox, Finset.mem_map, Finset.mem_product, Finset.mem_Icc, Function.Embedding.coeFn_mk,
    Prod.exists]
  constructor
  · rintro ⟨a, b, h, rfl⟩
    exact h
  · intro h
    exact ⟨(latPair g).1, (latPair g).2, h, rfl⟩

theorem card_zbox (p : ℕ) : (zbox p).card = (2 * p + 1) * (2 * p + 1) := by
  rw [zbox, Finset.card_map, Finset.card_product, Heisenberg.card_Icc_symm]

theorem zbox_mul_subset (p q : ℕ) : zbox p * zbox q ⊆ zbox (p + q) := by
  intro x hx
  rw [Finset.mem_mul] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  rw [mem_zbox] at hy hz ⊢
  simp only [latPair_mul, Prod.fst_add, Prod.snd_add]
  push_cast
  exact ⟨⟨by linarith [hy.1.1, hz.1.1], by linarith [hy.1.2, hz.1.2]⟩,
    by linarith [hy.2.1, hz.2.1], by linarith [hy.2.2, hz.2.2]⟩

theorem exists_zbox_superset (S : Finset Lat) : ∃ m : ℕ, S ⊆ zbox m := by
  refine ⟨S.sup (fun g => max (latPair g).1.natAbs (latPair g).2.natAbs), ?_⟩
  intro g hg
  have h := Finset.le_sup (f := fun g : Lat => max (latPair g).1.natAbs (latPair g).2.natAbs) hg
  simp only [max_le_iff] at h
  rw [mem_zbox]
  omega

theorem zbox_nonempty (p : ℕ) : (zbox p).Nonempty := by
  refine ⟨1, ?_⟩
  rw [mem_zbox]
  simp

/-- **The lattice has the combinatorial Følner property.** -/
theorem lat_hasFolner : Master.HasFolner Lat := by
  intro W
  obtain ⟨m, hm⟩ := exists_zbox_superset W
  refine ⟨zbox (10 * m + 10), zbox (9 * m + 10), ?_, ?_, ?_, zbox_nonempty _⟩
  · intro x hx
    rw [mem_zbox] at hx ⊢
    have h1 : ((9 * m + 10 : ℕ) : ℤ) ≤ ((10 * m + 10 : ℕ) : ℤ) := by push_cast; omega
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩,
      by linarith [hx.2.1], by linarith [hx.2.2]⟩
  · intro h hh w hw
    have hmem : h * w ∈ zbox (9 * m + 10) * zbox m := Finset.mul_mem_mul hh (hm hw)
    have hin := zbox_mul_subset (9 * m + 10) m hmem
    have heq : 9 * m + 10 + m = 10 * m + 10 := by ring
    rwa [heq] at hin
  · rw [card_zbox, card_zbox]
    push_cast
    nlinarith [Nat.zero_le m]

/-- The Heisenberg cocycle, transported to the synonym. -/
noncomputable def heisCocycleLat (θ : ℝ) : Cocycle Lat := heisCocycle θ

theorem heisCocycleLat_one_left (θ : ℝ) (g : Lat) : (heisCocycleLat θ).toFun 1 g = 1 :=
  heisCocycle_one_left θ g

theorem heisCocycleLat_one_right (θ : ℝ) (g : Lat) : (heisCocycleLat θ).toFun g 1 = 1 :=
  heisCocycle_one_right θ g

/-- **HRT FOR LATTICE SUBSETS, from twisted Atiyah.**  A nonzero window admits no nontrivial
dependence among its projective (time–frequency) translates over the lattice: every coefficient
vanishes.  Unconditional. -/
theorem hrt_lattice (θ : ℝ) (s : Finset Lat) (c : Lat → ℂ) (g : L2 Lat) (hg : g ≠ 0)
    (hdep : twistedGroupAlgOp (heisCocycleLat θ) s c g = 0) : ∀ x ∈ s, c x = 0 :=
  hrt_lattice_of_injective (heisCocycleLat θ)
    (fun s' c' hc' f hf => twistedGroupAlgOp_injective (heisCocycleLat θ)
      (heisCocycleLat_one_left θ) (heisCocycleLat_one_right θ) lat_hasFolner s' c' hc' f hf)
    s c g hg hdep

/-! ### The trivial cocycle, and the covolume-1 endgame

Route C reduces HRT over a covolume-1 lattice to a convolution identity on `ℤ²` with NO twist.
That is this development at the trivial cocycle. -/

/-- The trivial cocycle. -/
def trivCocycle (G : Type*) [Group G] : Cocycle G where
  toFun _ _ := 1
  unimodular _ _ := by simp
  cocycle _ _ _ := by simp

@[simp] theorem trivCocycle_toFun {G : Type*} [Group G] (g h : G) :
    (trivCocycle G).toFun g h = 1 := rfl

/-- **Ordinary convolution on `ℓ²(ℤ²)` is injective** — the endgame Route C lands on.

`twistedGroupAlgOp` at the trivial cocycle is the ordinary group-algebra operator, so this says:
a finitely supported nonzero `c` cannot annihilate a nonzero `ℓ²(ℤ²)` function by convolution. -/
theorem lat_groupAlgOp_injective (s : Finset Lat) (c : Lat → ℂ) (hc : ∃ x ∈ s, c x ≠ 0)
    (f : L2 Lat) (hf0 : twistedGroupAlgOp (trivCocycle Lat) s c f = 0) : f = 0 :=
  twistedGroupAlgOp_injective (trivCocycle Lat) (fun _ => rfl) (fun _ => rfl)
    lat_hasFolner s c hc f hf0

end Lattice

end HRT
end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.HRT.transposeCocycle
#print axioms GroupVN.HRT.twistedGroupAlgOp_eq_tconv
#print axioms GroupVN.HRT.twistedGroupAlgOp_injective
#print axioms GroupVN.HRT.lat_hasFolner
#print axioms GroupVN.HRT.hrt_lattice
#print axioms GroupVN.HRT.lat_groupAlgOp_injective
