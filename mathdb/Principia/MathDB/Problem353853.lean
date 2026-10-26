import Mathlib

/-!
# MathDB #353853 — strong avoidance does not force principal localizations

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/353853/solution.tex`, refuting Conjecture 4.10 of Chen and Tarizadeh:
a commutative ring `S` has *strong avoidance* (Definition 4.2: for every ring map `φ : R → S` and
ideals `I, I₁, …, Iₙ` of `R` with `I ⊆ I₁ ∪ ⋯ ∪ Iₙ`, some `IS ⊆ IⱼS`) if and only if `S_𝔭` is a
principal ideal domain for every prime `𝔭` of `S`.

**What is refuted.**  `CTConj` is the forward implication alone, for rings `S : Type` with `1 ≠ 0`
(both restrictions weaken the statement); the source rings `R` range over an arbitrary universe `u`,
and "PID" is `IsDomain ∧ IsPrincipalIdealRing`.

**The witness (the write-up's).**  `S = ℤ/4ℤ`.  Its ideals are linearly ordered (`comparable`), so
it has strong avoidance (`sa_of_comparable`, the write-up's Lemma: the largest `IⱼS` contains
`φ(I)`).  At any prime `𝔭` the element `2` lies in `𝔭` (`2² = 0`), its image in `S_𝔭` is nonzero
(no element outside `𝔭` kills it) and squares to zero, so `S_𝔭` is not a domain.

**Absent:** the write-up's valuation-domain counterexample (a domain with non-principal maximal
ideal).
-/

namespace Principia.MathDB.P353853

universe u

/-- Definition 4.2 of Chen–Tarizadeh: strong avoidance. -/
def StrongAvoidance (S : Type) [CommRing S] : Prop :=
  ∀ (R : Type u) [CommRing R] (φ : R →+* S) (n : ℕ) (I : Ideal R) (J : Fin (n + 1) → Ideal R),
    (I : Set R) ⊆ ⋃ k, (J k : Set R) → ∃ k, I.map φ ≤ (J k).map φ

/-- The forward implication of Conjecture 4.10. -/
def CTConj : Prop :=
  ∀ (S : Type) [CommRing S] [Nontrivial S], StrongAvoidance.{u} S →
    ∀ (p : Ideal S) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsPrincipalIdealRing (Localization.AtPrime p)

/-- In a ring whose ideals form a chain, every finite nonempty family has a largest member. -/
theorem exists_max_ideal {S : Type} [CommRing S] (hc : ∀ A B : Ideal S, A ≤ B ∨ B ≤ A) :
    ∀ (n : ℕ) (K : Fin (n + 1) → Ideal S), ∃ j, ∀ k, K k ≤ K j := by
  intro n
  induction n with
  | zero => exact fun K => ⟨0, fun k => le_of_eq (congrArg K (Subsingleton.elim (α := Fin 1) k 0))⟩
  | succ n ih =>
    intro K
    obtain ⟨j, hj⟩ := ih fun k => K k.succ
    rcases hc (K 0) (K j.succ) with h | h
    · exact ⟨j.succ, fun k => Fin.cases (motive := fun k => K k ≤ K j.succ) h (fun k => hj k) k⟩
    · exact ⟨0, fun k => Fin.cases (motive := fun k => K k ≤ K 0) le_rfl
        (fun k => (hj k).trans h) k⟩

/-- The write-up's Lemma: linearly ordered ideals give strong avoidance. -/
theorem sa_of_comparable (S : Type) [CommRing S] (hc : ∀ A B : Ideal S, A ≤ B ∨ B ≤ A) :
    StrongAvoidance.{u} S := by
  intro R _ φ n I J hIJ
  obtain ⟨j, hj⟩ := exists_max_ideal hc n fun k => (J k).map φ
  refine ⟨j, Ideal.map_le_iff_le_comap.2 fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hIJ hx)
  exact hj k (Ideal.mem_map_of_mem φ hk)

theorem eq_top_of_mem (X : Ideal (ZMod 4)) (x : ZMod 4) (hx : x ∈ X) (h0 : x ≠ 0) (h2 : x ≠ 2) :
    X = ⊤ := by
  fin_cases x
  · exact absurd rfl h0
  · exact Ideal.eq_top_of_isUnit_mem X hx isUnit_one
  · exact absurd rfl h2
  · exact Ideal.eq_top_of_isUnit_mem X hx (IsUnit.of_mul_eq_one 3 (by decide))

/-- The ideals of `ℤ/4ℤ` form a chain. -/
theorem comparable (A B : Ideal (ZMod 4)) : A ≤ B ∨ B ≤ A := by
  by_contra h
  rw [not_or, SetLike.not_le_iff_exists, SetLike.not_le_iff_exists] at h
  obtain ⟨⟨a, ha, haB⟩, ⟨b, hb, hbA⟩⟩ := h
  have ha0 : a ≠ 0 := fun h => haB (h ▸ B.zero_mem)
  have hb0 : b ≠ 0 := fun h => hbA (h ▸ A.zero_mem)
  have ha2 : a = 2 := by
    by_contra h
    exact hbA (by rw [eq_top_of_mem A a ha ha0 h]; exact Submodule.mem_top)
  have hb2 : b = 2 := by
    by_contra h
    exact haB (by rw [eq_top_of_mem B b hb hb0 h]; exact Submodule.mem_top)
  exact haB (by rw [ha2, ← hb2]; exact hb)

/-- **MathDB #353853: Conjecture 4.10 of Chen–Tarizadeh is false** (`S = ℤ/4ℤ`). -/
theorem not_ctConj : ¬ CTConj.{u} := by
  intro h
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ZMod 4)
  haveI := hm.isPrime
  obtain ⟨hd, -⟩ := h (ZMod 4) (sa_of_comparable (ZMod 4) comparable) m
  have h2 : (2 : ZMod 4) ∈ m :=
    hm.isPrime.mem_of_pow_mem 2 (by rw [show (2 : ZMod 4) ^ 2 = 0 by decide]; exact m.zero_mem)
  have hx : algebraMap (ZMod 4) (Localization.AtPrime m) 2 ≠ 0 := by
    rw [Ne, IsLocalization.map_eq_zero_iff m.primeCompl]
    rintro ⟨⟨c, hc⟩, hc2⟩
    have hc' : c ∉ m := hc
    apply hc'
    change c * 2 = 0 at hc2
    fin_cases c
    · exact m.zero_mem
    · exact absurd hc2 (by decide)
    · exact h2
    · exact absurd hc2 (by decide)
  have hsq : algebraMap (ZMod 4) (Localization.AtPrime m) 2
      * algebraMap (ZMod 4) (Localization.AtPrime m) 2 = 0 := by
    rw [← map_mul, show (2 : ZMod 4) * 2 = 0 by decide, map_zero]
  haveI := hd
  exact hx (mul_self_eq_zero.1 hsq)

end Principia.MathDB.P353853
