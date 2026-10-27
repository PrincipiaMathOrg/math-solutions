/-
# The Følner interior lemma — where amenability enters, and it enters combinatorially

**What this file proves.**  Let `u ∈ ℂ[G]` and let `trunc u F` be the truncation of
right-convolution by `u` to a finite set `F` — the `F × F` matrix `(g, h) ↦ u(h⁻¹g)`.  If
`h · (the k-ball of supp u) ⊆ F`, then

  `(trunc u F ^ k) g h = (u ^ k) (h⁻¹ g)`     (`GroupVN.Folner.trunc_pow_apply`)

exactly, for every `g ∈ F`.

**Why it matters.**  The whole Atiyah argument for an amenable group runs by comparing an infinite
object (the convolution operator on `ℓ²(G)`) with finite truncations whose spectra can be controlled
by the determinant bound.  That comparison is usually presented analytically — as an approximation
theorem with an error term bounded by the measure of a boundary.  It is not analytic at all: for any
point `h` far enough inside `F`, every length-`k` path out of `h` stays in `F`, so the truncated
matrix power agrees with the group-algebra power ON THE NOSE.  The Følner condition is only ever
used to say that most points of `F` are far enough inside.

The proof is an induction on `k` in which the only content is that a term of the group-algebra
product which falls outside `F` must have `u^j` vanishing on it — because otherwise it would lie in
`h · ball u j ⊆ F`.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace GroupVN

namespace Folner

open scoped Pointwise

variable {G : Type*} [Group G] [DecidableEq G]

/-- The truncation of right-convolution by `u` to a finite set `F`. -/
noncomputable def trunc (u : MonoidAlgebra ℂ G) (F : Finset G) : Matrix F F ℂ :=
  fun g h => u ((h : G)⁻¹ * (g : G))

/-- The `k`-ball of the support of `u`, containing the support of every power up to `u^k`. -/
noncomputable def ball (u : MonoidAlgebra ℂ G) : ℕ → Finset G
  | 0 => {1}
  | (k + 1) => (u.support ∪ {1}) * ball u k

theorem one_mem_ball (u : MonoidAlgebra ℂ G) (k : ℕ) : (1 : G) ∈ ball u k := by
  induction k with
  | zero => simp [ball]
  | succ j ih =>
      rw [ball, Finset.mem_mul]
      exact ⟨1, by simp, 1, ih, one_mul 1⟩

theorem ball_subset_succ (u : MonoidAlgebra ℂ G) (k : ℕ) : ball u k ⊆ ball u (k + 1) := by
  intro x hx
  rw [ball, Finset.mem_mul]
  exact ⟨1, by simp, x, hx, one_mul x⟩

theorem support_pow_subset_ball (u : MonoidAlgebra ℂ G) (k : ℕ) :
    (u ^ k).support ⊆ ball u k := by
  induction k with
  | zero =>
      intro x hx
      simp only [pow_zero] at hx
      have : x = 1 := by
        have := Finsupp.support_single_subset (a := (1 : G)) (b := (1 : ℂ)) hx
        simpa using this
      simp [ball, this]
  | succ j ih =>
      intro x hx
      rw [pow_succ'] at hx
      have hx' := MonoidAlgebra.support_mul u (u ^ j) hx
      rw [Finset.mem_mul] at hx'
      obtain ⟨y, hy, z, hz, rfl⟩ := hx'
      rw [ball, Finset.mem_mul]
      exact ⟨y, Finset.mem_union_left _ hy, z, ih hz, rfl⟩

/-- **The interior lemma.**  If `h · (the `k`-ball) ⊆ F`, then every path of length `k` starting at
`h` stays inside `F`, so the truncated matrix power agrees exactly with the group-algebra power.

This is the only place the Følner condition enters, and it enters as a purely combinatorial
statement about supports — no analysis. -/
theorem trunc_pow_apply (u : MonoidAlgebra ℂ G) (F : Finset G) :
    ∀ (k : ℕ) (h : F), (∀ w ∈ ball u k, (h : G) * w ∈ F) →
      ∀ g : F, (trunc u F ^ k) g h = (u ^ k) ((h : G)⁻¹ * (g : G)) := by
  intro k
  induction k with
  | zero =>
      intro h _ g
      simp only [pow_zero, Matrix.one_apply, MonoidAlgebra.one_def]
      by_cases hgh : g = h
      · subst hgh; simp
      · rw [if_neg hgh, Finsupp.single_apply, if_neg]
        intro hc
        exact hgh (Subtype.ext (by
          have : (h : G)⁻¹ * (g : G) = 1 := hc.symm
          simpa [eq_comm, inv_mul_eq_one] using this))
  | succ j ih =>
      intro h hint g
      have hintj : ∀ w ∈ ball u j, (h : G) * w ∈ F :=
        fun w hw => hint w (ball_subset_succ u j hw)
      rw [pow_succ', Matrix.mul_apply]
      have hstep : ∀ z : F, trunc u F g z * (trunc u F ^ j) z h
          = u ((z : G)⁻¹ * (g : G)) * (u ^ j) ((h : G)⁻¹ * (z : G)) := by
        intro z
        rw [ih h hintj z]
        rfl
      rw [Finset.sum_congr rfl (fun z _ => hstep z), pow_succ]
      rw [Finset.sum_coe_sort F
        (fun z => u (z⁻¹ * (g : G)) * (u ^ j) ((h : G)⁻¹ * z))]
      have hsub : (u ^ j).support.image (fun a => (h : G) * a) ⊆ F := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact hintj a (support_pow_subset_ball u j ha)
      rw [← Finset.sum_subset hsub ?_]
      · rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
        rw [MonoidAlgebra.mul_apply_left, Finsupp.sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_comm]
      · intro z _ hz
        have : (u ^ j) ((h : G)⁻¹ * z) = 0 := by
          by_contra hne
          exact hz (Finset.mem_image.mpr ⟨(h : G)⁻¹ * z, Finsupp.mem_support_iff.mpr hne,
            by rw [mul_inv_cancel_left]⟩)
        rw [this, mul_zero]

end Folner
end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.Folner.support_pow_subset_ball
#print axioms GroupVN.Folner.trunc_pow_apply
