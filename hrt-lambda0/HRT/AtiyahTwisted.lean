/-
# The twisted (projective) layer

The HRT chain does not need the Atiyah statement for `ℂ[G]`; it needs it for the TWISTED group
algebra `ℂ_σ[G]`, because time–frequency translates over a lattice generate a projective, not an
ordinary, representation.

This file builds the twisted convolution calculus.  Everything else in the Atiyah development
survives a **unimodular** cocycle unchanged:

* the determinant bound, because the triangular minor's diagonal becomes `r(m)·σ(gᵢ, m)` — entries
  that differ from one another but all have modulus `|r(m)|`, which is exactly the hypothesis of
  `DetLB.gramOf_det_lower_bound`;
* Cauchy–Schwarz, because `|σ| = 1`;
* the Følner interior lemma, because supports are unaffected by the twist.

What genuinely changes is the algebra: twisted convolution is an anti-action of the twisted product,
and *that* is where the cocycle identity is consumed.  This file proves it.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib
import AtiyahConvolution
import AtiyahDeterminant

set_option maxHeartbeats 1000000

namespace GroupVN
namespace Tw

open scoped Pointwise ComplexOrder

variable {G : Type*} [Group G] [DecidableEq G]

/-- A normalised unimodular 2-cocycle on `G`. -/
structure UCocycle (G : Type*) [Group G] where
  /-- The cocycle itself. -/
  toFun : G → G → ℂ
  /-- Unimodularity: every value is a phase. -/
  norm_eq : ∀ g h, ‖toFun g h‖ = 1
  /-- The 2-cocycle identity. -/
  cocycle : ∀ g h k, toFun g h * toFun (g * h) k = toFun h k * toFun g (h * k)
  /-- Normalisation on the left. -/
  one_left : ∀ g, toFun 1 g = 1
  /-- Normalisation on the right. -/
  one_right : ∀ g, toFun g 1 = 1

instance : CoeFun (UCocycle G) (fun _ => G → G → ℂ) := ⟨UCocycle.toFun⟩

theorem UCocycle.ne_zero (σ : UCocycle G) (g h : G) : σ g h ≠ 0 := by
  intro hc
  have := σ.norm_eq g h
  rw [hc, norm_zero] at this
  exact zero_ne_one this

/-! ### Twisted convolution and the twisted product -/

/-- Twisted right convolution: `(f ⋆_σ r)(x) = ∑_b r(b) · f(x b⁻¹) · σ(x b⁻¹, b)`. -/
noncomputable def tconv (σ : UCocycle G) (f : G → ℂ) (r : MonoidAlgebra ℂ G) : G → ℂ :=
  fun x => r.sum fun b c => c * f (x * b⁻¹) * σ (x * b⁻¹) b

/-- The twisted product on the group algebra, given by its coefficients:
`(a ∗_σ b)(x) = ∑_{y ∈ supp a} a(y) · b(y⁻¹x) · σ(y, y⁻¹x)`. -/
noncomputable def tmul (σ : UCocycle G) (a b : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  Finsupp.onFinset (a.support * b.support)
    (fun x => ∑ y ∈ a.support, a y * b (y⁻¹ * x) * σ y (y⁻¹ * x))
    (by
      intro x hx
      by_contra hmem
      refine hx (Finset.sum_eq_zero (fun y hy => ?_))
      have hb : b (y⁻¹ * x) = 0 := by
        by_contra hne
        exact hmem (Finset.mem_mul.mpr ⟨y, hy, y⁻¹ * x,
          Finsupp.mem_support_iff.mpr hne, by group⟩)
      rw [hb, mul_zero, zero_mul])

theorem tmul_apply (σ : UCocycle G) (a b : MonoidAlgebra ℂ G) (x : G) :
    tmul σ a b x = ∑ y ∈ a.support, a y * b (y⁻¹ * x) * σ y (y⁻¹ * x) := rfl

theorem tconv_eq_sum (σ : UCocycle G) (f : G → ℂ) (r : MonoidAlgebra ℂ G) {D : Finset G}
    (hD : r.support ⊆ D) (x : G) :
    tconv σ f r x = ∑ d ∈ D, r d * f (x * d⁻¹) * σ (x * d⁻¹) d :=
  Finsupp.sum_of_support_subset r hD _ (by intro i _; simp)

@[simp] theorem tconv_one (σ : UCocycle G) (f : G → ℂ) :
    tconv σ f (1 : MonoidAlgebra ℂ G) = f := by
  ext x
  rw [MonoidAlgebra.one_def, tconv, Finsupp.sum_single_index (by simp)]
  simp [σ.one_right]

theorem tconv_add (σ : UCocycle G) (f : G → ℂ) (r s : MonoidAlgebra ℂ G) :
    tconv σ f (r + s) = tconv σ f r + tconv σ f s := by
  ext x
  simp only [tconv, Pi.add_apply]
  exact Finsupp.sum_add_index' (by simp) (by intros; ring)

theorem tconv_smul (σ : UCocycle G) (f : G → ℂ) (c : ℂ) (r : MonoidAlgebra ℂ G) :
    tconv σ f (c • r) = c • tconv σ f r := by
  ext x
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsub : (c • r).support ⊆ r.support := Finsupp.support_smul
  rw [tconv_eq_sum σ f (c • r) hsub x, tconv_eq_sum σ f r Finset.Subset.rfl x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hval : (c • r) a = c * r a := rfl
  rw [hval]; ring

theorem tconv_single (σ : UCocycle G) (f : G → ℂ) (b : G) (c : ℂ) (x : G) :
    tconv σ f (MonoidAlgebra.single b c) x = c * f (x * b⁻¹) * σ (x * b⁻¹) b := by
  rw [tconv, MonoidAlgebra.single, Finsupp.sum_single_index (by simp)]

theorem tmul_single (σ : UCocycle G) (a : MonoidAlgebra ℂ G) (b : G) (c : ℂ) (d : G) :
    tmul σ a (MonoidAlgebra.single b c) d = a (d * b⁻¹) * c * σ (d * b⁻¹) b := by
  classical
  rw [tmul_apply]
  by_cases hmem : d * b⁻¹ ∈ a.support
  · rw [Finset.sum_eq_single (d * b⁻¹)]
    · congr 1
      · congr 1
        rw [MonoidAlgebra.single, Finsupp.single_apply, if_pos (by group)]
      · congr 1
        group
    · intro y _ hy
      have hz : (MonoidAlgebra.single b c : MonoidAlgebra ℂ G) (y⁻¹ * d) = 0 := by
        rw [MonoidAlgebra.single, Finsupp.single_apply, if_neg]
        intro hc
        refine hy ?_
        have h2 : y * b = d := by rw [hc]; group
        rw [← h2]; group
      rw [hz, mul_zero, zero_mul]
    · intro hc; exact absurd hmem hc
  · have hz : a (d * b⁻¹) = 0 := by
      by_contra hne; exact hmem (Finsupp.mem_support_iff.mpr hne)
    rw [hz, zero_mul, zero_mul]
    refine Finset.sum_eq_zero (fun y hy => ?_)
    have hz2 : (MonoidAlgebra.single b c : MonoidAlgebra ℂ G) (y⁻¹ * d) = 0 := by
      rw [MonoidAlgebra.single, Finsupp.single_apply, if_neg]
      intro hc
      have h2 : y * b = d := by rw [hc]; group
      have h3 : y = d * b⁻¹ := by rw [← h2]; group
      exact hmem (by rwa [← h3])
    rw [hz2, mul_zero, zero_mul]

/-! ### The anti-action — where the cocycle identity is consumed -/

theorem tconv_tmul_single (σ : UCocycle G) (f : G → ℂ) (a : MonoidAlgebra ℂ G) (b : G) (c : ℂ) :
    tconv σ f (tmul σ a (MonoidAlgebra.single b c))
      = tconv σ (tconv σ f a) (MonoidAlgebra.single b c) := by
  classical
  ext x
  rw [tconv_single]
  have hsub : (tmul σ a (MonoidAlgebra.single b c)).support ⊆ a.support.image (· * b) := by
    refine Finsupp.support_onFinset_subset.trans ?_
    intro z hz
    rw [Finset.mem_mul] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    have hwb : w = b := by simpa using Finsupp.support_single_subset hw
    subst hwb
    exact Finset.mem_image_of_mem _ hy
  rw [tconv_eq_sum σ f _ hsub x,
    Finset.sum_image (fun p _ q _ h => by simpa using h)]
  rw [tconv, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [tmul_single]
  -- name the two group elements the cocycle identity relates
  have hg1 : y * b * b⁻¹ = y := by group
  have hg2 : x * (y * b)⁻¹ = x * b⁻¹ * y⁻¹ := by group
  have hg3 : x * b⁻¹ * y⁻¹ * y = x * b⁻¹ := by group
  rw [hg1, hg2]
  have hcoc := σ.cocycle (x * b⁻¹ * y⁻¹) y b
  rw [hg3] at hcoc
  -- hcoc : σ (x b⁻¹ y⁻¹) y * σ (x b⁻¹) b = σ y b * σ (x b⁻¹ y⁻¹) (y * b)
  calc a y * c * σ y b * f (x * b⁻¹ * y⁻¹) * σ (x * b⁻¹ * y⁻¹) (y * b)
      = a y * f (x * b⁻¹ * y⁻¹) * c * (σ y b * σ (x * b⁻¹ * y⁻¹) (y * b)) := by ring
    _ = a y * f (x * b⁻¹ * y⁻¹) * c
          * (σ (x * b⁻¹ * y⁻¹) y * σ (x * b⁻¹) b) := by rw [hcoc]
    _ = c * (a y * f (x * b⁻¹ * y⁻¹) * σ (x * b⁻¹ * y⁻¹) y) * σ (x * b⁻¹) b := by ring

/-- **Twisted convolution is an anti-action of the twisted product.** -/
theorem tconv_tmul (σ : UCocycle G) (f : G → ℂ) (a b : MonoidAlgebra ℂ G) :
    tconv σ f (tmul σ a b) = tconv σ (tconv σ f a) b := by
  induction b using MonoidAlgebra.induction_on with
  | hM g => exact tconv_tmul_single σ f a g 1
  | hadd b₁ b₂ h₁ h₂ =>
      have hdist : tmul σ a (b₁ + b₂) = tmul σ a b₁ + tmul σ a b₂ := by
        ext x
        have hadd : ∀ z : G, (b₁ + b₂ : MonoidAlgebra ℂ G) z = b₁ z + b₂ z := fun _ => rfl
        have hsum : ∀ z : G, (tmul σ a b₁ + tmul σ a b₂ : MonoidAlgebra ℂ G) z
            = tmul σ a b₁ z + tmul σ a b₂ z := fun _ => rfl
        rw [tmul_apply, hsum, tmul_apply, tmul_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun y _ => by rw [hadd]; ring)
      rw [hdist, tconv_add, tconv_add, h₁, h₂]
  | hsmul c b h =>
      have hdist : tmul σ a (c • b) = c • tmul σ a b := by
        ext x
        have hsm : ∀ z : G, (c • b : MonoidAlgebra ℂ G) z = c * b z := fun _ => rfl
        have hsm2 : ∀ z : G, (c • tmul σ a b : MonoidAlgebra ℂ G) z
            = c * tmul σ a b z := fun _ => rfl
        rw [tmul_apply, hsm2, tmul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by rw [hsm]; ring)
      rw [hdist, tconv_smul, tconv_smul, h]

/-! ### Twisted powers, and the Cauchy–Schwarz bridge -/

theorem tconv_sub (σ : UCocycle G) (f : G → ℂ) (r s : MonoidAlgebra ℂ G) :
    tconv σ f (r - s) = tconv σ f r - tconv σ f s := by
  have h : r - s + s = r := by abel
  have h2 := tconv_add σ f (r - s) s
  rw [h] at h2
  rw [h2]; abel

/-- Powers in the twisted product. -/
noncomputable def tpow (σ : UCocycle G) (u : MonoidAlgebra ℂ G) : ℕ → MonoidAlgebra ℂ G
  | 0 => 1
  | (k + 1) => tmul σ (tpow σ u k) u

/-- **`f ⋆ (1 − c·r)^k = f` exactly, in the twisted calculus too.** -/
theorem tconv_tpow_eq (σ : UCocycle G) (f : G → ℂ) (r : MonoidAlgebra ℂ G) (c : ℂ)
    (hfr : tconv σ f r = 0) (k : ℕ) :
    tconv σ f (tpow σ (1 - c • r) k) = f := by
  induction k with
  | zero => simp [tpow]
  | succ j ih =>
      rw [tpow, tconv_tmul, ih, tconv_sub, tconv_one, tconv_smul, hfr]
      simp

@[simp] theorem tconv_zero_fun (σ : UCocycle G) (r : MonoidAlgebra ℂ G) :
    tconv σ (0 : G → ℂ) r = 0 := by
  ext x
  rw [tconv_eq_sum σ _ r Finset.Subset.rfl x]
  simp

/-- **Cauchy–Schwarz, twisted.**  Unimodularity of the cocycle means the bound is the same as in
the untwisted case: the phases drop out of every modulus. -/
theorem norm_tconv_le (σ : UCocycle G) (f : G → ℂ) (hf : Summable fun g => ‖f g‖ ^ 2)
    (q : MonoidAlgebra ℂ G) (x : G) :
    ‖tconv σ f q x‖ ≤ Conv.alg2norm q * Conv.l2norm f := by
  classical
  rw [tconv_eq_sum σ f q Finset.Subset.rfl x]
  have h1 : ‖∑ d ∈ q.support, q d * f (x * d⁻¹) * σ (x * d⁻¹) d‖
      ≤ ∑ d ∈ q.support, ‖q d‖ * ‖f (x * d⁻¹)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [norm_mul, norm_mul, σ.norm_eq, mul_one]
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
      ≤ Conv.alg2norm q * Real.sqrt (∑ d ∈ q.support, ‖f (x * d⁻¹)‖ ^ 2) := by
    rw [Conv.alg2norm, ← Real.sqrt_mul (by positivity)]
    exact (Real.le_sqrt hnn (by positivity)).mpr hcs
  refine h1.trans (hstep.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (Conv.alg2norm_nonneg q)
  exact Real.sqrt_le_sqrt hfin

/-- **THE TWISTED BRIDGE.** -/
theorem eq_zero_of_alg2norm_small (σ : UCocycle G) (f : G → ℂ)
    (hf : Summable fun g => ‖f g‖ ^ 2) (r : MonoidAlgebra ℂ G) (c : ℂ)
    (hfr : tconv σ f r = 0)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, Conv.alg2norm (tpow σ (1 - c • r) k) < ε) :
    f = 0 := by
  funext x
  by_contra hne
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hne
  have hL : 0 ≤ Conv.l2norm f := Real.sqrt_nonneg _
  obtain ⟨k, hk⟩ := hq (‖f x‖ / (Conv.l2norm f + 1)) (by positivity)
  rw [lt_div_iff₀ (by positivity)] at hk
  have hbound := norm_tconv_le σ f hf (tpow σ (1 - c • r) k) x
  rw [show tconv σ f (tpow σ (1 - c • r) k) = f from tconv_tpow_eq σ f r c hfr k] at hbound
  nlinarith [Conv.alg2norm_nonneg (tpow σ (1 - c • r) k), hpos, hL]


/-! ### The determinant bound, transferred to the twisted case

The twisted translate `δ_g ⋆_σ r` has value `r(g⁻¹p)·σ(g, g⁻¹p)` at position `p`.  Below the
diagonal that vanishes for the same reason as in the untwisted case (the group element overshoots
the largest support element), and ON the diagonal it is `r(m)·σ(i,m)` — entries that DIFFER from
one another but all have modulus `|r(m)|`.  That is exactly the hypothesis
`DetLB.gramOf_det_lower_bound` was generalised to accept, so the bound transfers with no new
analysis. -/

section Order

variable [LinearOrder G] [CovariantClass G G (· * ·) (· < ·)]
  [CovariantClass G G (Function.swap (· * ·)) (· < ·)]

/-- The coefficient of the twisted translate `δ_g ⋆_σ r` at position `p`. -/
noncomputable def tcoeff (σ : UCocycle G) (r : MonoidAlgebra ℂ G) : G → G → ℂ :=
  fun p g => r (g⁻¹ * p) * σ g (g⁻¹ * p)

theorem tcoeff_triangular (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (F : Finset G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) :
    ∀ i j : F, j < i → tcoeff σ r ((i : G) * m) (j : G) = 0 := by
  intro i j hji
  have h0 : r ((j : G)⁻¹ * ((i : G) * m)) = 0 :=
    DetLB.leadMat_upperTriangular r F hm i j hji
  show r ((j : G)⁻¹ * ((i : G) * m)) * σ (j : G) ((j : G)⁻¹ * ((i : G) * m)) = 0
  rw [h0, zero_mul]

theorem tcoeff_diag_normSq (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (F : Finset G) (m : G)
    (i : F) :
    Complex.normSq (tcoeff σ r ((i : G) * m) (i : G)) = Complex.normSq (r m) := by
  have hgrp : (i : G)⁻¹ * ((i : G) * m) = m := by group
  have hone : Complex.normSq (σ (i : G) m) = 1 := by
    rw [Complex.normSq_eq_norm_sq, σ.norm_eq]
    norm_num
  show Complex.normSq (r ((i : G)⁻¹ * ((i : G) * m))
      * σ (i : G) ((i : G)⁻¹ * ((i : G) * m))) = Complex.normSq (r m)
  rw [hgrp, map_mul, hone, mul_one]

/-- **THE DETERMINANT BOUND, TWISTED.**  Same conclusion, same constant, no new analysis. -/
theorem tgram_det_lower_bound (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (F T : Finset G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0) (hsub : F.image (· * m) ⊆ T) :
    Complex.normSq (r m) ^ F.card
      ≤ ∏ i, (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i :=
  DetLB.gramOf_det_lower_bound (tcoeff σ r) F T m (r m) hmr
    (tcoeff_triangular σ r F hm) (tcoeff_diag_normSq σ r F m) hsub

/-! ### The twisted interior lemma

Supports do not see the twist, so the combinatorics is unchanged — but twisted powers put the new
factor on the RIGHT (`tpow σ u (k+1) = tmul σ (tpow σ u k) u`, which is what pairs with
`M^{k+1} = M * M^k` in the matrix induction), and in a nonabelian group that forces a right-handed
ball.  The one analytic-looking step is again a single application of the cocycle identity. -/

/-- The right-handed `k`-ball, containing the support of every twisted power up to `tpow σ u k`. -/
noncomputable def rball (u : MonoidAlgebra ℂ G) : ℕ → Finset G
  | 0 => {1}
  | (k + 1) => rball u k * (u.support ∪ {1})

theorem rball_subset_succ (u : MonoidAlgebra ℂ G) (k : ℕ) : rball u k ⊆ rball u (k + 1) := by
  intro x hx
  rw [rball, Finset.mem_mul]
  exact ⟨x, hx, 1, by simp, mul_one x⟩

theorem tmul_support_subset (σ : UCocycle G) (a b : MonoidAlgebra ℂ G) :
    (tmul σ a b).support ⊆ a.support * b.support := Finsupp.support_onFinset_subset

theorem tpow_support_subset_rball (σ : UCocycle G) (u : MonoidAlgebra ℂ G) (k : ℕ) :
    (tpow σ u k).support ⊆ rball u k := by
  induction k with
  | zero =>
      intro x hx
      have hx1 : x = 1 := by
        have := Finsupp.support_single_subset (a := (1 : G)) (b := (1 : ℂ)) hx
        simpa using this
      simp [rball, hx1]
  | succ j ih =>
      intro x hx
      have hx' := tmul_support_subset σ (tpow σ u j) u hx
      rw [Finset.mem_mul] at hx'
      obtain ⟨y, hy, z, hz, rfl⟩ := hx'
      rw [rball, Finset.mem_mul]
      exact ⟨y, ih hy, z, Finset.mem_union_left _ hz, rfl⟩

/-- The truncation of twisted convolution to `F`. -/
noncomputable def ttrunc (σ : UCocycle G) (u : MonoidAlgebra ℂ G) (F : Finset G) : Matrix F F ℂ :=
  fun g h => tcoeff σ u (g : G) (h : G)

/-- **THE TWISTED INTERIOR LEMMA.** -/
theorem ttrunc_pow_apply (σ : UCocycle G) (u : MonoidAlgebra ℂ G) (F : Finset G) :
    ∀ (k : ℕ) (h : F), (∀ w ∈ rball u k, (h : G) * w ∈ F) →
      ∀ g : F, (ttrunc σ u F ^ k) g h = tcoeff σ (tpow σ u k) (g : G) (h : G) := by
  intro k
  induction k with
  | zero =>
      intro h _ g
      have hval : tcoeff σ (tpow σ u 0) (g : G) (h : G)
          = (1 : MonoidAlgebra ℂ G) ((h : G)⁻¹ * (g : G))
            * σ (h : G) ((h : G)⁻¹ * (g : G)) := rfl
      rw [pow_zero, Matrix.one_apply, hval, MonoidAlgebra.one_def, Finsupp.single_apply]
      by_cases hgh : g = h
      · subst hgh
        rw [if_pos rfl, if_pos (by group), inv_mul_cancel, σ.one_right]
        ring
      · rw [if_neg hgh, if_neg, zero_mul]
        intro hc
        exact hgh (Subtype.ext (by
          have h1 : (h : G)⁻¹ * (g : G) = 1 := hc.symm
          simpa [eq_comm, inv_mul_eq_one] using h1))
  | succ j ih =>
      intro h hint g
      have hintj : ∀ w ∈ rball u j, (h : G) * w ∈ F :=
        fun w hw => hint w (rball_subset_succ u j hw)
      rw [pow_succ', Matrix.mul_apply]
      have hstep : ∀ z : F, ttrunc σ u F g z * (ttrunc σ u F ^ j) z h
          = tcoeff σ u (g : G) (z : G) * tcoeff σ (tpow σ u j) (z : G) (h : G) := by
        intro z
        rw [ih h hintj z]
        rfl
      rw [Finset.sum_congr rfl (fun z _ => hstep z)]
      -- now the group-algebra side
      have hsub : (tpow σ u j).support.image (fun a => (h : G) * a) ⊆ F := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact hintj a (tpow_support_subset_rball σ u j ha)
      rw [Finset.sum_coe_sort F
        (fun z => tcoeff σ u (g : G) z * tcoeff σ (tpow σ u j) z (h : G))]
      rw [← Finset.sum_subset hsub ?_]
      · rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
        show _ = (tmul σ (tpow σ u j) u) ((h : G)⁻¹ * (g : G)) * σ (h : G) ((h : G)⁻¹ * (g : G))
        rw [tmul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have hg1 : ((h : G) * y)⁻¹ * (g : G) = y⁻¹ * ((h : G)⁻¹ * (g : G)) := by group
        have hg2 : (h : G)⁻¹ * ((h : G) * y) = y := by group
        have hcoc := σ.cocycle (h : G) y (y⁻¹ * ((h : G)⁻¹ * (g : G)))
        have hg4 : y * (y⁻¹ * ((h : G)⁻¹ * (g : G))) = (h : G)⁻¹ * (g : G) := by group
        rw [hg4] at hcoc
        show tcoeff σ u (g : G) ((h : G) * y) * tcoeff σ (tpow σ u j) ((h : G) * y) (h : G)
          = _
        show u (((h : G) * y)⁻¹ * (g : G)) * σ ((h : G) * y) (((h : G) * y)⁻¹ * (g : G))
            * ((tpow σ u j) ((h : G)⁻¹ * ((h : G) * y)) * σ (h : G) ((h : G)⁻¹ * ((h : G) * y)))
          = _
        rw [hg1, hg2]
        calc u (y⁻¹ * ((h : G)⁻¹ * (g : G))) * σ ((h : G) * y) (y⁻¹ * ((h : G)⁻¹ * (g : G)))
              * ((tpow σ u j) y * σ (h : G) y)
            = (tpow σ u j) y * u (y⁻¹ * ((h : G)⁻¹ * (g : G)))
              * (σ (h : G) y * σ ((h : G) * y) (y⁻¹ * ((h : G)⁻¹ * (g : G)))) := by ring
          _ = (tpow σ u j) y * u (y⁻¹ * ((h : G)⁻¹ * (g : G)))
              * (σ y (y⁻¹ * ((h : G)⁻¹ * (g : G))) * σ (h : G) ((h : G)⁻¹ * (g : G))) := by
                rw [hcoc]
          _ = (tpow σ u j) y * u (y⁻¹ * ((h : G)⁻¹ * (g : G)))
                * σ y (y⁻¹ * ((h : G)⁻¹ * (g : G))) * σ (h : G) ((h : G)⁻¹ * (g : G)) := by ring
      · intro z _ hz
        have hzero : (tpow σ u j) ((h : G)⁻¹ * z) = 0 := by
          by_contra hne
          exact hz (Finset.mem_image.mpr ⟨(h : G)⁻¹ * z, Finsupp.mem_support_iff.mpr hne,
            by rw [mul_inv_cancel_left]⟩)
        show tcoeff σ u (g : G) z * tcoeff σ (tpow σ u j) z (h : G) = 0
        show _ * ((tpow σ u j) ((h : G)⁻¹ * z) * σ (h : G) ((h : G)⁻¹ * z)) = 0
        rw [hzero, zero_mul, mul_zero]

/-! ### The Gram matrix IS a twisted truncation

In the untwisted case the Gram matrix of the translates was the truncation of convolution by
`r · r*`.  The twisted analogue holds with the SAME shape, for an element defined directly by its
coefficients — no twisted involution is needed.  The proof is one cocycle application plus
`conj z · z = 1` for a phase. -/

/-- The self-adjoint element whose twisted truncations are the Gram matrices of the twisted
translates of `r`. -/
noncomputable def tbElt (σ : UCocycle G) (r : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  Finsupp.onFinset (r.support * r.support⁻¹)
    (fun x => ∑ q ∈ r.support, (starRingEnd ℂ) (r (x⁻¹ * q) * σ x (x⁻¹ * q)) * r q)
    (by
      intro x hx
      by_contra hmem
      refine hx (Finset.sum_eq_zero (fun q hq => ?_))
      have hz : r (x⁻¹ * q) = 0 := by
        by_contra hne
        refine hmem (Finset.mem_mul.mpr ⟨q, hq, (x⁻¹ * q)⁻¹, ?_, by group⟩)
        exact Finset.inv_mem_inv (Finsupp.mem_support_iff.mpr hne)
      rw [hz, zero_mul, map_zero, zero_mul])

theorem tbElt_apply (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (x : G) :
    tbElt σ r x = ∑ q ∈ r.support, (starRingEnd ℂ) (r (x⁻¹ * q) * σ x (x⁻¹ * q)) * r q := rfl

theorem UCocycle.conj_mul_self (σ : UCocycle G) (g h : G) :
    (starRingEnd ℂ) (σ g h) * σ g h = 1 := by
  have h1 : Complex.normSq (σ g h) = 1 := by
    rw [Complex.normSq_eq_norm_sq, σ.norm_eq]; norm_num
  have h2 := Complex.normSq_eq_conj_mul_self (z := σ g h)
  rw [h1] at h2
  simpa using h2.symm

/-- **The twisted Gram matrix is the twisted truncation of `tbElt σ r`.** -/
theorem gramOf_tcoeff_eq (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (g h : F) :
    DetLB.gramOf (tcoeff σ r) F T g h = tcoeff σ (tbElt σ r) (g : G) (h : G) := by
  classical
  have hsub : r.support.image (fun q => (h : G) * q) ⊆ T := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact hT (h : G) h.2 q hq
  rw [DetLB.gramOf]
  simp only [Matrix.sum_apply, DetLB.rank1_apply]
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
    show _ = tbElt σ r ((h : G)⁻¹ * (g : G)) * σ (h : G) ((h : G)⁻¹ * (g : G))
    rw [tbElt_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    set x : G := (h : G)⁻¹ * (g : G) with hx
    have hgx : (h : G) * x = (g : G) := by rw [hx]; group
    have hxq : x * (x⁻¹ * q) = q := by group
    have hcoc := σ.cocycle (h : G) x (x⁻¹ * q)
    rw [hgx, hxq] at hcoc
    have hgq : (g : G)⁻¹ * ((h : G) * q) = x⁻¹ * q := by rw [← hgx]; group
    have hhq : (h : G)⁻¹ * ((h : G) * q) = q := by group
    show (starRingEnd ℂ) (r ((g : G)⁻¹ * ((h : G) * q)) * σ (g : G) ((g : G)⁻¹ * ((h : G) * q)))
        * (r ((h : G)⁻¹ * ((h : G) * q)) * σ (h : G) ((h : G)⁻¹ * ((h : G) * q)))
      = (starRingEnd ℂ) (r (x⁻¹ * q) * σ x (x⁻¹ * q)) * r q * σ (h : G) x
    rw [hgq, hhq]
    have hc1 : (starRingEnd ℂ) (σ (h : G) x) * (starRingEnd ℂ) (σ (g : G) (x⁻¹ * q))
        = (starRingEnd ℂ) (σ x (x⁻¹ * q)) * (starRingEnd ℂ) (σ (h : G) q) := by
      rw [← map_mul, ← map_mul, hcoc]
    have e1 := σ.conj_mul_self (h : G) x
    have e2 := σ.conj_mul_self (h : G) q
    have hkey : (starRingEnd ℂ) (σ (g : G) (x⁻¹ * q)) * σ (h : G) q
        = (starRingEnd ℂ) (σ x (x⁻¹ * q)) * σ (h : G) x := by
      linear_combination (σ (h : G) x * σ (h : G) q) * hc1
        - ((starRingEnd ℂ) (σ (g : G) (x⁻¹ * q)) * σ (h : G) q) * e1
        + ((starRingEnd ℂ) (σ x (x⁻¹ * q)) * σ (h : G) x) * e2
    calc (starRingEnd ℂ) (r (x⁻¹ * q) * σ (g : G) (x⁻¹ * q)) * (r q * σ (h : G) q)
        = (starRingEnd ℂ) (r (x⁻¹ * q)) * r q
            * ((starRingEnd ℂ) (σ (g : G) (x⁻¹ * q)) * σ (h : G) q) := by
          rw [map_mul (starRingEnd ℂ)]; ring
      _ = (starRingEnd ℂ) (r (x⁻¹ * q)) * r q
            * ((starRingEnd ℂ) (σ x (x⁻¹ * q)) * σ (h : G) x) := by rw [hkey]
      _ = (starRingEnd ℂ) (r (x⁻¹ * q) * σ x (x⁻¹ * q)) * r q * σ (h : G) x := by
          rw [map_mul (starRingEnd ℂ)]; ring
  · intro p _ hp
    have hzero : r ((h : G)⁻¹ * p) = 0 := by
      by_contra hne
      exact hp (Finset.mem_image.mpr ⟨(h : G)⁻¹ * p, Finsupp.mem_support_iff.mpr hne,
        by rw [mul_inv_cancel_left]⟩)
    show (starRingEnd ℂ) (tcoeff σ r p (g : G)) * tcoeff σ r p (h : G) = 0
    show _ * (r ((h : G)⁻¹ * p) * σ (h : G) ((h : G)⁻¹ * p)) = 0
    rw [hzero, zero_mul, mul_zero]

end Order

end Tw
end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.Tw.tmul_single
#print axioms GroupVN.Tw.tconv_tmul
#print axioms GroupVN.Tw.tconv_tpow_eq
#print axioms GroupVN.Tw.norm_tconv_le
#print axioms GroupVN.Tw.eq_zero_of_alg2norm_small
#print axioms GroupVN.Tw.tcoeff_triangular
#print axioms GroupVN.Tw.tcoeff_diag_normSq
#print axioms GroupVN.Tw.tgram_det_lower_bound
#print axioms GroupVN.Tw.tpow_support_subset_rball
#print axioms GroupVN.Tw.ttrunc_pow_apply
#print axioms GroupVN.Tw.gramOf_tcoeff_eq
