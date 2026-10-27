/-
# The convolution layer — how a vanishing sequence in `ℂ[G]` forces injectivity on `ℓ²(G)`

**What this file proves.**  Let `f : G → ℂ` be square-summable and `r ∈ ℂ[G]` annihilate it on the
right (`f ⋆ r = 0`).  If the group algebra elements `(1 - c·r)^k` have `ℓ²` norms tending to zero,
then `f = 0` (`GroupVN.Conv.eq_zero_of_alg2norm_small`).

**Why this shape.**  The textbook route to "a nonzero `r ∈ ℂ[G]` acts injectively on `ℓ²(G)`" goes
through the orthogonal projection `P` onto the kernel, the canonical trace `τ`, the inequality
`P ≤ (1 - B/C)^{2k}` from the Borel functional calculus, and normality of `τ`.  None of that is
needed.  The observation here is that `f ⋆ (1 - c·r)^k = f` *exactly*, for every `k`, because every
term of the binomial expansion past the first is killed by `f ⋆ r = 0`.  So Cauchy–Schwarz gives

  `|f(x)| = |(f ⋆ q_k)(x)| ≤ ‖q_k‖₂ · ‖f‖₂`

pointwise, and `f` vanishes as soon as `‖q_k‖₂` can be made small.  No projection, no trace, no
functional calculus, no spectral measure — the entire operator-theoretic layer collapses into one
finite sum and one Cauchy–Schwarz.

What remains, and is where the real content lives, is the estimate `‖q_k‖₂ → 0`; that is supplied by
the Følner argument together with the determinant bound of `AtiyahDeterminant.lean`.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace GroupVN

namespace Conv

open scoped Pointwise

variable {G : Type*} [Group G] [DecidableEq G]

/-- Right convolution of an arbitrary function by a finitely supported one:
`(f ⋆ r)(x) = ∑_b r(b) · f(x b⁻¹)`.  A finite sum, so no summability hypothesis is needed. -/
noncomputable def rconv (f : G → ℂ) (r : MonoidAlgebra ℂ G) : G → ℂ :=
  fun x => r.sum fun b c => c * f (x * b⁻¹)

theorem rconv_eq_sum (f : G → ℂ) (r : MonoidAlgebra ℂ G) {D : Finset G}
    (hD : r.support ⊆ D) (x : G) :
    rconv f r x = ∑ d ∈ D, r d * f (x * d⁻¹) :=
  Finsupp.sum_of_support_subset r hD _ (by intro i _; simp)

@[simp] theorem rconv_one (f : G → ℂ) : rconv f 1 = f := by
  ext x
  simp [rconv, MonoidAlgebra.one_def, MonoidAlgebra.single, Finsupp.sum_single_index]

theorem rconv_add (f : G → ℂ) (r s : MonoidAlgebra ℂ G) :
    rconv f (r + s) = rconv f r + rconv f s := by
  ext x
  simp only [rconv, Pi.add_apply]
  exact Finsupp.sum_add_index' (by simp) (by intros; ring)

theorem rconv_single (f : G → ℂ) (b : G) (c : ℂ) (x : G) :
    rconv f (MonoidAlgebra.single b c) x = c * f (x * b⁻¹) := by
  simp [rconv, MonoidAlgebra.single, Finsupp.sum_single_index]

theorem rconv_mul_single (f : G → ℂ) (r : MonoidAlgebra ℂ G) (b : G) (c : ℂ) :
    rconv f (r * MonoidAlgebra.single b c) = rconv (rconv f r) (MonoidAlgebra.single b c) := by
  ext x
  rw [rconv_single]
  have hsub : (r * MonoidAlgebra.single b c).support ⊆ r.support.image (· * b) := by
    intro d hd
    have hd' := MonoidAlgebra.support_mul r (MonoidAlgebra.single b c) hd
    rw [Finset.mem_mul] at hd'
    obtain ⟨y, hy, z, hz, rfl⟩ := hd'
    have hzb : z = b := by simpa using Finsupp.support_single_subset hz
    subst hzb
    exact Finset.mem_image_of_mem _ hy
  rw [rconv_eq_sum f _ hsub x,
    Finset.sum_image (fun a _ a' _ h => by simpa using h)]
  rw [rconv, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have hval : (r * MonoidAlgebra.single b c) (a * b) = r a * c := by
    refine MonoidAlgebra.mul_single_apply_aux ?_
    intro z _
    constructor
    · intro h; exact mul_right_cancel h
    · intro h; rw [h]
  rw [hval, mul_inv_rev, ← mul_assoc]
  ring

theorem rconv_smul (f : G → ℂ) (c : ℂ) (r : MonoidAlgebra ℂ G) :
    rconv f (c • r) = c • rconv f r := by
  ext x
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsub : (c • r).support ⊆ r.support := Finsupp.support_smul
  rw [rconv_eq_sum f (c • r) hsub x, rconv_eq_sum f r Finset.Subset.rfl x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hval : (c • r) a = c * r a := rfl
  rw [hval]; ring

/-- **Right convolution is an anti-action of the group algebra.** -/
theorem rconv_mul (f : G → ℂ) (r s : MonoidAlgebra ℂ G) :
    rconv f (r * s) = rconv (rconv f r) s := by
  induction s using MonoidAlgebra.induction_on with
  | hM g => exact rconv_mul_single f r g 1
  | hadd s₁ s₂ h₁ h₂ => rw [mul_add, rconv_add, rconv_add, h₁, h₂]
  | hsmul c s h => rw [mul_smul_comm, rconv_smul, rconv_smul, h]

theorem rconv_sub (f : G → ℂ) (r s : MonoidAlgebra ℂ G) :
    rconv f (r - s) = rconv f r - rconv f s := by
  have h : r - s + s = r := by abel
  have := rconv_add f (r - s) s
  rw [h] at this
  rw [this]
  abel

/-! ### The vanishing sequence -/

/-- If `r` annihilates `f` on the right, so does every power of `1 - c • r`'s complement:
`f ⋆ (1 - c • r)^k = f` for every `k`. -/
theorem rconv_pow_eq (f : G → ℂ) (r : MonoidAlgebra ℂ G) (c : ℂ)
    (hfr : rconv f r = 0) (k : ℕ) :
    rconv f ((1 - c • r) ^ k) = f := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, rconv_mul, ih, rconv_sub, rconv_one, rconv_smul, hfr]
      simp

/-! ### Cauchy–Schwarz -/

/-- The `ℓ²` norm of a function on the group. -/
noncomputable def l2norm (f : G → ℂ) : ℝ := Real.sqrt (∑' g, ‖f g‖ ^ 2)

/-- The `ℓ²` norm of a finitely supported element. -/
noncomputable def alg2norm (q : MonoidAlgebra ℂ G) : ℝ :=
  Real.sqrt (∑ d ∈ q.support, ‖q d‖ ^ 2)

theorem alg2norm_nonneg (q : MonoidAlgebra ℂ G) : 0 ≤ alg2norm q := Real.sqrt_nonneg _

/-- **Cauchy–Schwarz for right convolution.**  Every value of `f ⋆ q` is bounded by the product
of the two `ℓ²` norms — this is what turns "`‖q‖₂` is small" into "`f` is small". -/
theorem norm_rconv_le (f : G → ℂ) (hf : Summable fun g => ‖f g‖ ^ 2)
    (q : MonoidAlgebra ℂ G) (x : G) :
    ‖rconv f q x‖ ≤ alg2norm q * l2norm f := by
  classical
  rw [rconv_eq_sum f q Finset.Subset.rfl x]
  have h1 : ‖∑ d ∈ q.support, q d * f (x * d⁻¹)‖
      ≤ ∑ d ∈ q.support, ‖q d‖ * ‖f (x * d⁻¹)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun d _ => norm_mul _ _)
  have hcs : (∑ d ∈ q.support, ‖q d‖ * ‖f (x * d⁻¹)‖) ^ 2
      ≤ (∑ d ∈ q.support, ‖q d‖ ^ 2) * ∑ d ∈ q.support, ‖f (x * d⁻¹)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnn : 0 ≤ ∑ d ∈ q.support, ‖q d‖ * ‖f (x * d⁻¹)‖ := by positivity
  have hfin : ∑ d ∈ q.support, ‖f (x * d⁻¹)‖ ^ 2 ≤ ∑' g, ‖f g‖ ^ 2 := by
    have hinj : ∀ a ∈ q.support, ∀ b ∈ q.support, x * a⁻¹ = x * b⁻¹ → a = b := by
      intro a _ b _ h
      simpa using h
    rw [← Finset.sum_image (f := fun g => ‖f g‖ ^ 2) (g := fun d => x * d⁻¹) hinj]
    exact hf.sum_le_tsum _ (fun g _ => by positivity)
  have hstep : (∑ d ∈ q.support, ‖q d‖ * ‖f (x * d⁻¹)‖)
      ≤ alg2norm q * Real.sqrt (∑ d ∈ q.support, ‖f (x * d⁻¹)‖ ^ 2) := by
    rw [alg2norm, ← Real.sqrt_mul (by positivity)]
    exact (Real.le_sqrt hnn (by positivity)).mpr hcs
  refine h1.trans (hstep.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (alg2norm_nonneg q)
  exact Real.sqrt_le_sqrt hfin

@[simp] theorem rconv_zero_fun (r : MonoidAlgebra ℂ G) : rconv (0 : G → ℂ) r = 0 := by
  ext x
  rw [rconv_eq_sum _ r Finset.Subset.rfl x]
  simp

/-- **THE BRIDGE.**  If `r` annihilates `f` on the right and the powers of `1 - c • r` have
`ℓ²` norms tending to zero, then `f` is zero.

This replaces the whole projection/spectral-measure layer of the textbook argument: no kernel
projection, no trace, no functional calculus — just Cauchy–Schwarz against a sequence of group
algebra elements that `f` cannot distinguish from the identity. -/
theorem eq_zero_of_alg2norm_small (f : G → ℂ) (hf : Summable fun g => ‖f g‖ ^ 2)
    (r : MonoidAlgebra ℂ G) (c : ℂ) (hfr : rconv f r = 0)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, alg2norm ((1 - c • r) ^ k) < ε) :
    f = 0 := by
  funext x
  by_contra hne
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hne
  have hL : 0 ≤ l2norm f := Real.sqrt_nonneg _
  obtain ⟨k, hk⟩ := hq (‖f x‖ / (l2norm f + 1)) (by positivity)
  rw [lt_div_iff₀ (by positivity)] at hk
  have hbound := norm_rconv_le f hf ((1 - c • r) ^ k) x
  rw [show rconv f ((1 - c • r) ^ k) = f from rconv_pow_eq f r c hfr k] at hbound
  nlinarith [alg2norm_nonneg ((1 - c • r) ^ k), hpos, hL]

end Conv
end GroupVN


/-! ## Acceptance gate -/

#print axioms GroupVN.Conv.rconv_mul
#print axioms GroupVN.Conv.rconv_pow_eq
#print axioms GroupVN.Conv.norm_rconv_le
#print axioms GroupVN.Conv.eq_zero_of_alg2norm_small
