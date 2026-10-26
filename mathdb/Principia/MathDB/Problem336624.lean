import Mathlib.Data.Rat.Denumerable
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# MathDB #336624 — Kiss–Somlai Conjecture 5.3 is FALSE

Write-up: `mathdb-open-problems/problems/336624/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-28 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: G. Kiss and G. Somlai, **Conjecture 5.3**: an associative, idempotent, strictly
coordinatewise monotone operation on a totally ordered abelian group that is *nonreducible* must
have odd arity and be conjugate, by a monotone bijection, to the alternating sum formed with the
group's own addition.

**The counterexample is the write-up's own**, at arity `3` on `ℚ`: transport the addition of the
*different* ordered group `H = ℤ + √2·ℤ` along an order isomorphism `h : ℚ ≃o H`, and set

`F x y z = h⁻¹(h x − h y + h z)`.

`H` has the same order type as `ℚ` but different divisibility, and that is the whole mechanism.

## What carried the formalisation: Cantor's isomorphism theorem

The write-up builds `h` by an explicit back-and-forth. Mathlib already has the theorem —
`Order.iso_of_countable_dense`, for countable dense linear orders without endpoints — so the work
is supplying the four instances for `H`, all of which come from `H` being a *dense* subgroup:
`AddSubgroup.dense_or_cyclic` gives dense-or-cyclic, and `H` is not cyclic because it contains both
`1` and `√2` (a common generator would make `√2` rational). Density then yields `DenselyOrdered`
via `Dense.exists_between`, and `1 ∈ H` yields `NoMinOrder`/`NoMaxOrder` by `x ± 1`.

## Two simplifications over the write-up

**The normalisation `h 0 = 0`, `h 1 = 1` is not needed.** Cantor's theorem supplies *some* order
isomorphism and nothing pins two of its values, so the write-up's use of `1/2 ∉ H` is re-routed:
take `a = h⁻¹ 0` and `b = h⁻¹ 1`, and then `F x a x = b` is exactly `2·h x = 0 + 1`, unsolvable
because `1/2 ∉ H`. The obstruction is *`H` is not 2-divisible*, and the normalisation was only a
way of pointing at it.

**Nonreducibility needs no torsion argument.** The write-up derives `2(x − e) = 0` for every
`x ∈ H` and contradicts it with `x = e + 1`. In `H ⊆ ℝ` the same equation gives `h x = h e` for
*every* `x`, so `h` would be constant — contradicting injectivity, which is cheaper and does not
mention the group structure at all. The identity-element step is the write-up's and is kept: from
`e = star 0 0`, associativity gives `star e z = F 0 0 z = z` and `star z e = F z 0 0 = z`, so
`F e x e = star (star e x) e = star x e = x`.

## 215 check

* The source's printed sum starts with a minus sign; as the write-up notes, that reading cannot be
  idempotent on `ℚ` at all (on the diagonal it needs `−g x = g x`). The refutation here is of the
  **substantive** plus-first reading, matching the source's own Example 4.10, so it does not rest on
  the typographical issue.
* Reducibility is taken as *iteration of an associative binary operation*, with **no monotonicity
  assumed of that binary operation** — exactly the source's sense, and the weaker hypothesis makes
  the refutation stronger.
* The refutation excludes **every** bijection `g`, not merely the monotone ones the conjecture
  offers, so it is insensitive to how "conjugate" is read.
-/

namespace Principia.MathDB.P336624

open Real

/-! ### The group `H = ℤ + √2·ℤ` -/

/-- `H = ℤ + √2·ℤ`, an additive subgroup of `ℝ` with the same order type as `ℚ` but which is not
`2`-divisible. -/
def Hs : AddSubgroup ℝ where
  carrier := {x : ℝ | ∃ a b : ℤ, x = (a : ℝ) + (b : ℝ) * Real.sqrt 2}
  zero_mem' := ⟨0, 0, by norm_num⟩
  add_mem' := by
    rintro x y ⟨a1, b1, rfl⟩ ⟨a2, b2, rfl⟩
    exact ⟨a1 + a2, b1 + b2, by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩

theorem one_mem_Hs : (1 : ℝ) ∈ Hs := ⟨1, 0, by norm_num⟩

theorem sqrt2_mem_Hs : Real.sqrt 2 ∈ Hs := ⟨0, 1, by norm_num⟩

/-- **`H` is not `2`-divisible**, and this single fact is what refutes the conjecture. -/
theorem half_not_mem_Hs : (1 / 2 : ℝ) ∉ Hs := by
  rintro ⟨a, b, hab⟩
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb] at hab
    norm_num at hab
    have hc : ((2 * a : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h2 : (2 * a : ℤ) = 1 := by exact_mod_cast hc
    omega
  · have hthis : Real.sqrt 2 = (1 / 2 - (a : ℝ)) / (b : ℝ) := by
      field_simp at hab ⊢
      linarith
    have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
    rw [hthis] at hirr
    exact hirr ⟨(1 / 2 - (a : ℚ)) / (b : ℚ), by push_cast; ring⟩

theorem countable_Hs : (Hs : Set ℝ).Countable := by
  have hr : (Hs : Set ℝ) = Set.range (fun p : ℤ × ℤ => (p.1 : ℝ) + (p.2 : ℝ) * Real.sqrt 2) := by
    ext x
    constructor
    · rintro ⟨a, b, rfl⟩; exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨a, b, rfl⟩
  rw [hr]
  exact Set.countable_range _

/-- `H` is dense: it is not cyclic, because a common generator of `1` and `√2` would make `√2`
rational. -/
theorem dense_Hs : Dense (Hs : Set ℝ) := by
  rcases AddSubgroup.dense_or_cyclic Hs with hd | ⟨a, ha⟩
  · exact hd
  · exfalso
    have h1 : (1 : ℝ) ∈ AddSubgroup.closure {a} := ha ▸ one_mem_Hs
    have h2 : Real.sqrt 2 ∈ AddSubgroup.closure {a} := ha ▸ sqrt2_mem_Hs
    rw [AddSubgroup.mem_closure_singleton] at h1 h2
    obtain ⟨m, hm⟩ := h1
    obtain ⟨n, hn⟩ := h2
    have hm0 : m ≠ 0 := by
      intro h; rw [h] at hm; simp at hm
    have hm' : (m : ℝ) * a = 1 := by rw [← zsmul_eq_mul]; exact hm
    have hn' : (n : ℝ) * a = Real.sqrt 2 := by rw [← zsmul_eq_mul]; exact hn
    have hmne : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    have hthis : Real.sqrt 2 = (n : ℝ) / (m : ℝ) := by
      rw [← hn', eq_div_iff hmne]
      calc (n : ℝ) * a * (m : ℝ) = (n : ℝ) * ((m : ℝ) * a) := by ring
        _ = (n : ℝ) := by rw [hm']; ring
    have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
    rw [hthis] at hirr
    exact hirr ⟨(n : ℚ) / (m : ℚ), by push_cast; ring⟩

instance : Countable (Hs : Set ℝ) := countable_Hs.to_subtype

instance : DenselyOrdered (Hs : Set ℝ) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨c, hcH, hc⟩ := dense_Hs.exists_between (by exact_mod_cast hxy)
  exact ⟨⟨c, hcH⟩, by exact_mod_cast hc.1, by exact_mod_cast hc.2⟩

instance : NoMaxOrder (Hs : Set ℝ) := by
  constructor
  rintro ⟨x, hx⟩
  exact ⟨⟨x + 1, Hs.add_mem hx one_mem_Hs⟩, by simp⟩

instance : NoMinOrder (Hs : Set ℝ) := by
  constructor
  rintro ⟨x, hx⟩
  exact ⟨⟨x - 1, Hs.sub_mem hx one_mem_Hs⟩, by simp⟩

instance : Nonempty (Hs : Set ℝ) := ⟨⟨0, Hs.zero_mem⟩⟩

/-- **Cantor's isomorphism theorem** supplies the order isomorphism the write-up builds by hand. -/
theorem exists_orderIso : Nonempty (ℚ ≃o (Hs : Set ℝ)) := Order.iso_of_countable_dense _ _

/-! ### The operation -/

/-- `Reducible F` : `F` is the iteration of an associative binary operation. No monotonicity is
asked of that operation — the source's sense, and the weaker hypothesis makes the refutation
stronger. -/
def Reducible (F : ℚ → ℚ → ℚ → ℚ) : Prop :=
  ∃ star : ℚ → ℚ → ℚ, (∀ a b c, star (star a b) c = star a (star b c)) ∧
    ∀ x y z, F x y z = star (star x y) z

/-- `F` is conjugate to the alternating sum by a bijection of `ℚ`. -/
def AltSumConjugate (F : ℚ → ℚ → ℚ → ℚ) : Prop :=
  ∃ g : ℚ ≃ ℚ, ∀ x y z, F x y z = g.symm (g x - g y + g z)

section Witness

variable (h : ℚ ≃o (Hs : Set ℝ))

/-- The witness: the alternating sum of `H`, pulled back along `h`. -/
def Fw (x y z : ℚ) : ℚ := h.symm (h x - h y + h z)

theorem Fw_coe (x y z : ℚ) : ((h (Fw h x y z) : ℝ)) = (h x : ℝ) - (h y : ℝ) + (h z : ℝ) := by
  rw [Fw, OrderIso.apply_symm_apply]
  push_cast
  ring

theorem Fw_idem (x : ℚ) : Fw h x x x = x := by
  have : (h x : (Hs : Set ℝ)) - h x + h x = h x := by abel
  rw [Fw, this, OrderIso.symm_apply_apply]

/-- Strictly increasing in the first variable. -/
theorem Fw_strictMono_fst (y z : ℚ) : StrictMono (fun x => Fw h x y z) := by
  intro x1 x2 hx
  have h1 : ((h x1 : (Hs : Set ℝ)) : ℝ) < ((h x2 : (Hs : Set ℝ)) : ℝ) := by
    exact_mod_cast h.lt_iff_lt.mpr hx
  have h2 : (h x1 - h y + h z : (Hs : Set ℝ)) < h x2 - h y + h z := by
    have : ((h x1 - h y + h z : (Hs : Set ℝ)) : ℝ)
        < ((h x2 - h y + h z : (Hs : Set ℝ)) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact h.symm.lt_iff_lt.mpr h2

/-- Strictly decreasing in the second variable. -/
theorem Fw_strictAnti_snd (x z : ℚ) : StrictAnti (fun y => Fw h x y z) := by
  intro y1 y2 hy
  have h1 : ((h y1 : (Hs : Set ℝ)) : ℝ) < ((h y2 : (Hs : Set ℝ)) : ℝ) := by
    exact_mod_cast h.lt_iff_lt.mpr hy
  have h2 : (h x - h y2 + h z : (Hs : Set ℝ)) < h x - h y1 + h z := by
    have : ((h x - h y2 + h z : (Hs : Set ℝ)) : ℝ)
        < ((h x - h y1 + h z : (Hs : Set ℝ)) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact h.symm.lt_iff_lt.mpr h2

/-- Strictly increasing in the third variable. -/
theorem Fw_strictMono_thd (x y : ℚ) : StrictMono (fun z => Fw h x y z) := by
  intro z1 z2 hz
  have h1 : ((h z1 : (Hs : Set ℝ)) : ℝ) < ((h z2 : (Hs : Set ℝ)) : ℝ) := by
    exact_mod_cast h.lt_iff_lt.mpr hz
  have h2 : (h x - h y + h z1 : (Hs : Set ℝ)) < h x - h y + h z2 := by
    have : ((h x - h y + h z1 : (Hs : Set ℝ)) : ℝ)
        < ((h x - h y + h z2 : (Hs : Set ℝ)) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact h.symm.lt_iff_lt.mpr h2

/-- **Associativity in the source's sense**: all three ways of nesting agree, because in `H` each
is the alternating sum `u₁ − u₂ + u₃ − u₄ + u₅`. -/
theorem Fw_assoc (u1 u2 u3 u4 u5 : ℚ) :
    Fw h (Fw h u1 u2 u3) u4 u5 = Fw h u1 (Fw h u2 u3 u4) u5 ∧
      Fw h u1 (Fw h u2 u3 u4) u5 = Fw h u1 u2 (Fw h u3 u4 u5) := by
  constructor
  · rw [Fw, Fw, Fw, Fw, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
    congr 1
    abel
  · rw [Fw, Fw, Fw, Fw, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
    congr 1
    abel

/-- **NONREDUCIBLE.** An associative binary reduction makes `e = star 0 0` a two-sided identity,
so `F e x e = (star (star e x)) e = x`; but `F e x e = h⁻¹(2·h e − h x)`, which forces
`h x = h e` for *every* `x`, and `h` is injective. -/
theorem Fw_not_reducible : ¬ Reducible (Fw h) := by
  rintro ⟨star, hassoc, hred⟩
  have hFw00 : ∀ z : ℚ, Fw h 0 0 z = z := by
    intro z
    rw [Fw, show (h 0 : (Hs : Set ℝ)) - h 0 + h z = h z by abel, OrderIso.symm_apply_apply]
  have hFwz00 : ∀ z : ℚ, Fw h z 0 0 = z := by
    intro z
    rw [Fw, show (h z : (Hs : Set ℝ)) - h 0 + h 0 = h z by abel, OrderIso.symm_apply_apply]
  -- `star 0 0` is a two-sided identity
  have hleft : ∀ z : ℚ, star (star 0 0) z = z := by
    intro z; rw [← hred 0 0 z, hFw00 z]
  have hright : ∀ z : ℚ, star z (star 0 0) = z := by
    intro z; rw [← hassoc z 0 0, ← hred z 0 0, hFwz00 z]
  -- hence `F e x e = x`
  have hFex : ∀ x : ℚ, Fw h (star 0 0) x (star 0 0) = x := by
    intro x
    rw [hred (star 0 0) x (star 0 0), hleft x, hright x]
  -- but that says `h e - h x + h e = h x`, so `h` is constant
  have hconst : ∀ x : ℚ, (h x : ℝ) = (h (star 0 0) : ℝ) := by
    intro x
    have h3 := hFex x
    have h4 : (h (star 0 0) : (Hs : Set ℝ)) - h x + h (star 0 0) = h x := by
      have h5 := congrArg h h3
      rwa [Fw, OrderIso.apply_symm_apply] at h5
    have h6 := Subtype.ext_iff.mp h4
    push_cast at h6
    linarith
  have h01 : (h 0 : ℝ) = (h 1 : ℝ) := by rw [hconst 0, hconst 1]
  have : h 0 = h 1 := Subtype.ext h01
  exact absurd (h.injective this) (by norm_num)

/-- **NOT CONJUGATE TO THE ALTERNATING SUM, BY ANY BIJECTION.** With `a = h⁻¹ 0` and `b = h⁻¹ 1`,
the equation `F x a x = b` says `2·h x = 1`, unsolvable because `1/2 ∉ H`. A conjugating `g` would
solve it at `x = g⁻¹((g a + g b)/2)`. -/
theorem Fw_not_altSumConjugate : ¬ AltSumConjugate (Fw h) := by
  rintro ⟨g, hg⟩
  set a : ℚ := h.symm ⟨0, Hs.zero_mem⟩ with ha
  set b : ℚ := h.symm ⟨1, one_mem_Hs⟩ with hb
  have hha : (h a : ℝ) = 0 := by rw [ha, OrderIso.apply_symm_apply]
  have hhb : (h b : ℝ) = 1 := by rw [hb, OrderIso.apply_symm_apply]
  -- no `x` solves it, because `H` is not 2-divisible
  have hno : ∀ x : ℚ, Fw h x a x ≠ b := by
    intro x hx
    have h4 : (h x : (Hs : Set ℝ)) - h a + h x = h b := by
      have h5 := congrArg h hx
      rwa [Fw, OrderIso.apply_symm_apply] at h5
    have h6 := Subtype.ext_iff.mp h4
    push_cast at h6
    rw [hha, hhb] at h6
    have hhalf : ((h x : ℝ)) = 1 / 2 := by linarith
    exact half_not_mem_Hs (hhalf ▸ (h x).2)
  -- but `g` provides one
  refine hno (g.symm ((g a + g b) / 2)) ?_
  rw [hg]
  have hgx : g (g.symm ((g a + g b) / 2)) = (g a + g b) / 2 := g.apply_symm_apply _
  rw [hgx]
  have : (g a + g b) / 2 - g a + (g a + g b) / 2 = g b := by ring
  rw [this, Equiv.symm_apply_apply]

end Witness

/-! ## The refutation, assembled -/

/-- **KISS–SOMLAI CONJECTURE 5.3 IS FALSE.** There is an associative, idempotent ternary operation
on `ℚ`, strictly increasing in its outer variables and strictly decreasing in its middle one, which
is nonreducible and yet is conjugate to the alternating sum by **no** bijection of `ℚ` — monotone or
otherwise. -/
theorem conjecture_5_3_false :
    ∃ F : ℚ → ℚ → ℚ → ℚ,
      (∀ u1 u2 u3 u4 u5, F (F u1 u2 u3) u4 u5 = F u1 (F u2 u3 u4) u5 ∧
        F u1 (F u2 u3 u4) u5 = F u1 u2 (F u3 u4 u5)) ∧
      (∀ x, F x x x = x) ∧
      (∀ y z, StrictMono fun x => F x y z) ∧
      (∀ x z, StrictAnti fun y => F x y z) ∧
      (∀ x y, StrictMono fun z => F x y z) ∧
      ¬ Reducible F ∧ ¬ AltSumConjugate F := by
  obtain ⟨h⟩ := exists_orderIso
  exact ⟨Fw h, Fw_assoc h, Fw_idem h, Fw_strictMono_fst h, Fw_strictAnti_snd h,
    Fw_strictMono_thd h, Fw_not_reducible h, Fw_not_altSumConjugate h⟩

end Principia.MathDB.P336624
