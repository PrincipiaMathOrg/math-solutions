/-
# The twisted assembly

Mirrors `AtiyahMaster` with `tcoeff`/`ttrunc`/`rball` in place of the untwisted family, reusing
every matrix-level lemma (`DetLB.trace_one_sub_smul_pow`, `DetLB.card_small_eigenvalues_le`,
`DetLB.eigenvalues_le_of_rowSum_le`, `Master.sum_one_sub_pow_le`, `Master.diag_even_pow`) unchanged
— those are statements about Hermitian matrices and never saw the group.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import AtiyahTwisted
import AtiyahMaster

set_option maxHeartbeats 1000000

namespace GroupVN
namespace Tw

open Matrix
open scoped Pointwise ComplexOrder

variable {G : Type*} [Group G] [DecidableEq G] [LinearOrder G]
  [CovariantClass G G (· * ·) (· < ·)] [CovariantClass G G (Function.swap (· * ·)) (· < ·)]

/-- The twisted contraction. -/
noncomputable def tuElt (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (C : ℝ) : MonoidAlgebra ℂ G :=
  1 - ((C⁻¹ : ℝ) : ℂ) • tbElt σ r

/-- `tcoeff` of the identity is the identity matrix. -/
theorem tcoeff_one (σ : UCocycle G) (F : Finset G) (g h : F) :
    tcoeff σ (1 : MonoidAlgebra ℂ G) (g : G) (h : G) = (1 : Matrix F F ℂ) g h := by
  have hval : tcoeff σ (1 : MonoidAlgebra ℂ G) (g : G) (h : G)
      = (1 : MonoidAlgebra ℂ G) ((h : G)⁻¹ * (g : G))
        * σ (h : G) ((h : G)⁻¹ * (g : G)) := rfl
  rw [hval, Matrix.one_apply, MonoidAlgebra.one_def, Finsupp.single_apply]
  by_cases hgh : g = h
  · subst hgh
    rw [if_pos rfl, if_pos (by group), inv_mul_cancel, σ.one_right]
    ring
  · rw [if_neg hgh, if_neg, zero_mul]
    intro hc
    exact hgh (Subtype.ext (by
      have h1 : (h : G)⁻¹ * (g : G) = 1 := hc.symm
      simpa [eq_comm, inv_mul_eq_one] using h1))

/-- **The truncation of the twisted contraction is `1 − gram/C`.** -/
theorem ttrunc_tuElt (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) :
    ttrunc σ (tuElt σ r C) F = 1 - ((C⁻¹ : ℝ) : ℂ) • DetLB.gramOf (tcoeff σ r) F T := by
  ext g h
  have hg : DetLB.gramOf (tcoeff σ r) F T g h = tcoeff σ (tbElt σ r) (g : G) (h : G) :=
    gramOf_tcoeff_eq σ r F T hT g h
  have hL : ttrunc σ (tuElt σ r C) F g h
      = ((1 : MonoidAlgebra ℂ G) ((h : G)⁻¹ * (g : G))
          - ((C⁻¹ : ℝ) : ℂ) * tbElt σ r ((h : G)⁻¹ * (g : G)))
        * σ (h : G) ((h : G)⁻¹ * (g : G)) := rfl
  have h1 : tcoeff σ (1 : MonoidAlgebra ℂ G) (g : G) (h : G) = (1 : Matrix F F ℂ) g h :=
    tcoeff_one σ F g h
  have h1' : (1 : MonoidAlgebra ℂ G) ((h : G)⁻¹ * (g : G))
      * σ (h : G) ((h : G)⁻¹ * (g : G)) = (1 : Matrix F F ℂ) g h := h1
  have hb : tbElt σ r ((h : G)⁻¹ * (g : G)) * σ (h : G) ((h : G)⁻¹ * (g : G))
      = DetLB.gramOf (tcoeff σ r) F T g h := hg.symm
  rw [hL, sub_mul, h1', mul_assoc, hb]
  simp [Matrix.sub_apply, Matrix.smul_apply, mul_assoc]

theorem ttrunc_tuElt_isHermitian (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (C : ℝ)
    (F T : Finset G) (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) :
    (ttrunc σ (tuElt σ r C) F).IsHermitian := by
  rw [ttrunc_tuElt σ r C F T hT]
  refine Matrix.IsHermitian.sub Matrix.isHermitian_one ?_
  have hH := (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian
  ext i j
  have hij : star (DetLB.gramOf (tcoeff σ r) F T j i) = DetLB.gramOf (tcoeff σ r) F T i j := by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.star_def, hij]

/-! ### The twisted key estimate -/

/-- The squared column norm of the `k`-th power of the twisted truncation. -/
noncomputable def tcolNorm (σ : UCocycle G) (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ)
    (h : F) : ℝ :=
  ∑ g : F, ‖((ttrunc σ u F) ^ k) g h‖ ^ 2

theorem tcolNorm_nonneg (σ : UCocycle G) (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ)
    (h : F) : 0 ≤ tcolNorm σ u F k h := by
  unfold tcolNorm; positivity

/-- At an interior point the column norm is exactly `‖tpow σ u k‖₂²`.  The phases drop out. -/
theorem tcolNorm_interior (σ : UCocycle G) (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ)
    (h : F) (hint : ∀ w ∈ rball u k, (h : G) * w ∈ F) :
    tcolNorm σ u F k h = Conv.alg2norm (tpow σ u k) ^ 2 := by
  classical
  rw [tcolNorm]
  have hstep : ∀ g : F, ‖((ttrunc σ u F) ^ k) g h‖ ^ 2
      = ‖(tpow σ u k) ((h : G)⁻¹ * (g : G))‖ ^ 2 := by
    intro g
    rw [ttrunc_pow_apply σ u F k h hint g]
    show ‖(tpow σ u k) ((h : G)⁻¹ * (g : G)) * σ (h : G) ((h : G)⁻¹ * (g : G))‖ ^ 2 = _
    rw [norm_mul, σ.norm_eq, mul_one]
  rw [Finset.sum_congr rfl (fun g _ => hstep g),
    Finset.sum_coe_sort F (fun g => ‖(tpow σ u k) ((h : G)⁻¹ * g)‖ ^ 2)]
  have hsub : (tpow σ u k).support.image (fun d => (h : G) * d) ⊆ F := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact hint d (tpow_support_subset_rball σ u k hd)
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab),
      Conv.alg2norm, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl (fun d _ => by rw [inv_mul_cancel_left])
  · intro x _ hx
    have hz : (tpow σ u k) ((h : G)⁻¹ * x) = 0 := by
      by_contra hne
      exact hx (Finset.mem_image.mpr ⟨(h : G)⁻¹ * x, Finsupp.mem_support_iff.mpr hne,
        by rw [mul_inv_cancel_left]⟩)
    rw [hz]; simp

/-- The trace identity, twisted. -/
theorem tsum_colNorm_eq (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (k : ℕ) :
    ∑ h : F, tcolNorm σ (tuElt σ r C) F k h
      = ∑ i, (1 - C⁻¹ *
          (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i) ^ (2 * k) := by
  have hherm := ttrunc_tuElt_isHermitian σ r C F T hT
  have htr : ((ttrunc σ (tuElt σ r C) F) ^ (2 * k)).trace
      = ((∑ h : F, tcolNorm σ (tuElt σ r C) F k h : ℝ) : ℂ) := by
    rw [Matrix.trace, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun h _ => by
      rw [Matrix.diag_apply, Master.diag_even_pow hherm k h]; rfl)
  have htr2 : ((ttrunc σ (tuElt σ r C) F) ^ (2 * k)).trace
      = ((∑ i, (1 - C⁻¹ *
          (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i) ^ (2 * k)
          : ℝ) : ℂ) := by
    rw [ttrunc_tuElt σ r C F T hT]
    exact DetLB.trace_one_sub_smul_pow_real
      (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian C⁻¹ (2 * k)
  have := htr.symm.trans htr2
  exact_mod_cast this

/-- **THE TWISTED KEY ESTIMATE.** -/
theorem talg2norm_mul_card_le (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (k : ℕ)
    (I : Finset F) (hI : ∀ h ∈ I, ∀ w ∈ rball (tuElt σ r C) k, (h : G) * w ∈ F) :
    Conv.alg2norm (tpow σ (tuElt σ r C) k) ^ 2 * (I.card : ℝ)
      ≤ ∑ i, (1 - C⁻¹ *
          (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i) ^ (2 * k) := by
  rw [← tsum_colNorm_eq σ r C F T hT k]
  have hsub : ∑ h ∈ I, tcolNorm σ (tuElt σ r C) F k h
      ≤ ∑ h : F, tcolNorm σ (tuElt σ r C) F k h :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun h _ _ => tcolNorm_nonneg _ _ _ _ _)
  refine le_trans (le_of_eq ?_) hsub
  rw [Finset.sum_congr rfl (fun h hh => tcolNorm_interior σ (tuElt σ r C) F k h (hI h hh)),
    Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### The uniform eigenvalue ceiling, twisted -/

noncomputable def tbNorm (σ : UCocycle G) (r : MonoidAlgebra ℂ G) : ℝ :=
  ∑ x ∈ (tbElt σ r).support, ‖tbElt σ r x‖

theorem tgram_rowSum_le (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (g : F) :
    ∑ h : F, ‖DetLB.gramOf (tcoeff σ r) F T g h‖ ≤ tbNorm σ r := by
  classical
  have hg : ∀ h : F, ‖DetLB.gramOf (tcoeff σ r) F T g h‖
      = ‖tbElt σ r ((h : G)⁻¹ * (g : G))‖ := by
    intro h
    rw [gramOf_tcoeff_eq σ r F T hT g h]
    show ‖tbElt σ r ((h : G)⁻¹ * (g : G)) * σ (h : G) ((h : G)⁻¹ * (g : G))‖ = _
    rw [norm_mul, σ.norm_eq, mul_one]
  rw [Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => hg h),
    Finset.sum_coe_sort F (fun h => ‖tbElt σ r (h⁻¹ * (g : G))‖)]
  have hinj : ∀ a ∈ F, ∀ b ∈ F, a⁻¹ * (g : G) = b⁻¹ * (g : G) → a = b := by
    intro a _ b _ hab
    simpa using mul_right_cancel hab
  rw [← Finset.sum_image (f := fun x => ‖tbElt σ r x‖) (g := fun h => h⁻¹ * (g : G)) hinj]
  have hsplit : ∑ x ∈ F.image (fun h => h⁻¹ * (g : G)), ‖tbElt σ r x‖
      = ∑ x ∈ (F.image (fun h => h⁻¹ * (g : G))) ∩ (tbElt σ r).support, ‖tbElt σ r x‖ := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro x hx hnot
    have hz : tbElt σ r x = 0 := by
      by_contra hne
      exact hnot (Finset.mem_inter.mpr ⟨hx, Finsupp.mem_support_iff.mpr hne⟩)
    rw [hz, norm_zero]
  rw [hsplit, tbNorm]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun _ _ _ => norm_nonneg _)

theorem tgram_eigenvalues_le (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (i : F) :
    (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i ≤ tbNorm σ r :=
  DetLB.eigenvalues_le_of_rowSum_le _ (tgram_rowSum_le σ r F T hT) i

theorem tbElt_one_eq (σ : UCocycle G) (r : MonoidAlgebra ℂ G) :
    tbElt σ r 1 = ((∑ q ∈ r.support, Complex.normSq (r q) : ℝ) : ℂ) := by
  rw [tbElt_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inv_one, one_mul, σ.one_left, mul_one, Complex.normSq_eq_conj_mul_self]

theorem normSq_le_tbNorm (σ : UCocycle G) (r : MonoidAlgebra ℂ G) {m : G} (hmr : r m ≠ 0) :
    Complex.normSq (r m) ≤ tbNorm σ r := by
  classical
  have hmem : m ∈ r.support := Finsupp.mem_support_iff.mpr hmr
  have h1 : Complex.normSq (r m) ≤ ∑ q ∈ r.support, Complex.normSq (r q) :=
    Finset.single_le_sum (f := fun q => Complex.normSq (r q))
      (fun q _ => Complex.normSq_nonneg _) hmem
  have hb1 : ‖tbElt σ r 1‖ = ∑ q ∈ r.support, Complex.normSq (r q) := by
    rw [tbElt_one_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hpos : (0 : ℝ) < ∑ q ∈ r.support, Complex.normSq (r q) :=
    lt_of_lt_of_le (Complex.normSq_pos.mpr hmr) h1
  have hmem1 : (1 : G) ∈ (tbElt σ r).support := by
    refine Finsupp.mem_support_iff.mpr ?_
    intro hc
    rw [hc] at hb1
    simp at hb1
    linarith [hpos, hb1]
  have h2 : ‖tbElt σ r 1‖ ≤ tbNorm σ r :=
    Finset.single_le_sum (f := fun x => ‖tbElt σ r x‖) (fun _ _ => norm_nonneg _) hmem1
  rw [hb1] at h2
  linarith

theorem tbNorm_pos (σ : UCocycle G) (r : MonoidAlgebra ℂ G) {m : G} (hmr : r m ≠ 0) :
    0 < tbNorm σ r :=
  lt_of_lt_of_le (Complex.normSq_pos.mpr hmr) (normSq_le_tbNorm σ r hmr)

/-! ### `tbElt` really is `r ∗_σ r*`

`tbElt` was DEFINED by its coefficients, because that is what made the Gram identity come out.  To
inherit annihilation (`f ⋆ r = 0 ⟹ f ⋆ tbElt = 0`) it must also be an honest twisted product.  It
is: with the twisted involution `r*(z) = conj(r(z⁻¹)·σ(z,z⁻¹))`, one cocycle application shows
`tbElt σ r = r ∗_σ r*`.  Note the phase in `tstar` is forced — the naive `conj(r(z⁻¹))` does not
work, and the correction factor `σ(z,z⁻¹)` is exactly what the cocycle demands. -/

/-- The twisted involution. -/
noncomputable def tstar (σ : UCocycle G) (r : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  Finsupp.onFinset r.support⁻¹
    (fun z => (starRingEnd ℂ) (r z⁻¹ * σ z z⁻¹))
    (by
      intro z hz
      have hrz : r z⁻¹ ≠ 0 := by
        intro hc
        exact hz (by rw [hc, zero_mul, map_zero])
      have hmem := Finset.inv_mem_inv (Finsupp.mem_support_iff.mpr hrz)
      rwa [inv_inv] at hmem)

theorem tstar_apply (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (z : G) :
    tstar σ r z = (starRingEnd ℂ) (r z⁻¹ * σ z z⁻¹) := rfl

theorem tbElt_eq_tmul_tstar (σ : UCocycle G) (r : MonoidAlgebra ℂ G) :
    tbElt σ r = tmul σ r (tstar σ r) := by
  ext x
  rw [tbElt_apply, tmul_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hinv : (q⁻¹ * x)⁻¹ = x⁻¹ * q := by group
  have hcoc := σ.cocycle q (q⁻¹ * x) (x⁻¹ * q)
  have hg1 : q * (q⁻¹ * x) = x := by group
  have hg2 : q⁻¹ * x * (x⁻¹ * q) = 1 := by group
  rw [hg1, hg2, σ.one_right, mul_one] at hcoc
  -- hcoc : σ q (q⁻¹ x) * σ x (x⁻¹ q) = σ (q⁻¹ x) (x⁻¹ q)
  have e1 := σ.conj_mul_self q (q⁻¹ * x)
  rw [tstar_apply, hinv]
  have hkey : (starRingEnd ℂ) (σ (q⁻¹ * x) (x⁻¹ * q)) * σ q (q⁻¹ * x)
      = (starRingEnd ℂ) (σ x (x⁻¹ * q)) := by
    have hc1 : (starRingEnd ℂ) (σ q (q⁻¹ * x)) * (starRingEnd ℂ) (σ x (x⁻¹ * q))
        = (starRingEnd ℂ) (σ (q⁻¹ * x) (x⁻¹ * q)) := by
      rw [← map_mul, hcoc]
    linear_combination (σ q (q⁻¹ * x)) * hc1.symm
      + ((starRingEnd ℂ) (σ x (x⁻¹ * q))) * e1
  calc (starRingEnd ℂ) (r (x⁻¹ * q) * σ x (x⁻¹ * q)) * r q
      = r q * ((starRingEnd ℂ) (r (x⁻¹ * q)) * (starRingEnd ℂ) (σ x (x⁻¹ * q))) := by
        rw [map_mul (starRingEnd ℂ)]; ring
    _ = r q * ((starRingEnd ℂ) (r (x⁻¹ * q))
          * ((starRingEnd ℂ) (σ (q⁻¹ * x) (x⁻¹ * q)) * σ q (q⁻¹ * x))) := by rw [hkey]
    _ = r q * (starRingEnd ℂ) (r (x⁻¹ * q) * σ (q⁻¹ * x) (x⁻¹ * q)) * σ q (q⁻¹ * x) := by
        rw [map_mul (starRingEnd ℂ)]; ring

/-- Annihilation is inherited. -/
theorem tconv_tbElt_eq_zero (σ : UCocycle G) (f : G → ℂ) (r : MonoidAlgebra ℂ G)
    (hfr : tconv σ f r = 0) : tconv σ f (tbElt σ r) = 0 := by
  rw [tbElt_eq_tmul_tstar, tconv_tmul, hfr, tconv_zero_fun]

/-! ### The final twisted chain -/

theorem tgram_eigenvalues_pos (σ : UCocycle G) (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0) (F T : Finset G)
    (hsubT : F.image (· * m) ⊆ T) (i : F) :
    0 < (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i := by
  have hnn := (DetLB.gramOf_posSemidef (tcoeff σ r) F T).eigenvalues_nonneg i
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hdet := tgram_det_lower_bound σ r F T hm hmr hsubT
    have hzero : ∏ j, (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h.symm
    rw [hzero] at hdet
    have hpos : 0 < Complex.normSq (r m) ^ F.card :=
      pow_pos (Complex.normSq_pos.mpr hmr) _
    linarith

theorem talg2norm_sq_le_of_interior (σ : UCocycle G) (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0)
    {C : ℝ} (hC : 0 < C) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T)
    (hsubT : F.image (· * m) ⊆ T)
    (hub : ∀ i, (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i ≤ C)
    (hCm : Complex.normSq (r m) ≤ C)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hεC : ε < C)
    (I : Finset F) (hI : ∀ h ∈ I, ∀ w ∈ rball (tuElt σ r C) k, (h : G) * w ∈ F)
    (hIcard : (F.card : ℝ) ≤ 2 * (I.card : ℝ)) (hIpos : 0 < (I.card : ℝ)) :
    Conv.alg2norm (tpow σ (tuElt σ r C) k) ^ 2
      ≤ 2 * ((Real.log C - Real.log (Complex.normSq (r m))) / (Real.log C - Real.log ε))
        + 2 * (1 - C⁻¹ * ε) ^ (2 * k) := by
  classical
  set hH := (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian with hHdef
  set ev := hH.eigenvalues with hev
  have hpos : ∀ i, 0 < ev i := tgram_eigenvalues_pos σ r hm hmr F T hsubT
  have hnn : ∀ i, 0 ≤ ev i := fun i => (hpos i).le
  have hcardF : Fintype.card F = F.card := Fintype.card_coe F
  have hkey := talg2norm_mul_card_le σ r C F T hT k I hI
  have hsplit := Master.sum_one_sub_pow_le hH hC hεC.le hnn hub k
  have hdet := tgram_det_lower_bound σ r F T hm hmr hsubT
  have hdpos : 0 < Complex.normSq (r m) ^ F.card := pow_pos (Complex.normSq_pos.mpr hmr) _
  have hcount := DetLB.card_small_eigenvalues_le hH hC hdpos hε hpos hub hdet
  have hlogd : Real.log (Complex.normSq (r m) ^ F.card)
      = (F.card : ℝ) * Real.log (Complex.normSq (r m)) := Real.log_pow _ _
  have hlogpos : 0 < Real.log C - Real.log ε := by
    have := Real.log_lt_log hε hεC
    linarith
  have hsmall : ((Finset.univ.filter (fun i => ev i ≤ ε)).card : ℝ)
      ≤ (F.card : ℝ) * ((Real.log C - Real.log (Complex.normSq (r m)))
          / (Real.log C - Real.log ε)) := by
    rw [hlogd, hcardF] at hcount
    rw [← mul_div_assoc]
    refine (le_div_iff₀ hlogpos).mpr ?_
    linarith [hcount]
  have hXnn : (0 : ℝ) ≤ (Real.log C - Real.log (Complex.normSq (r m)))
      / (Real.log C - Real.log ε) := by
    refine div_nonneg ?_ hlogpos.le
    have := Real.log_le_log (Complex.normSq_pos.mpr hmr) hCm
    linarith
  have hpowpos : (0 : ℝ) ≤ (1 - C⁻¹ * ε) ^ (2 * k) := by
    have h1 : (0 : ℝ) ≤ 1 - C⁻¹ * ε := by
      have h := mul_le_mul_of_nonneg_left hεC.le (inv_pos.mpr hC).le
      rw [inv_mul_cancel₀ hC.ne'] at h
      linarith
    positivity
  have hchain : Conv.alg2norm (tpow σ (tuElt σ r C) k) ^ 2 * (I.card : ℝ)
      ≤ (F.card : ℝ) * ((Real.log C - Real.log (Complex.normSq (r m)))
          / (Real.log C - Real.log ε))
        + (F.card : ℝ) * (1 - C⁻¹ * ε) ^ (2 * k) := by
    rw [hcardF] at hsplit
    linarith [hkey, hsplit, hsmall]
  have hfinal : Conv.alg2norm (tpow σ (tuElt σ r C) k) ^ 2 * (I.card : ℝ)
      ≤ (2 * ((Real.log C - Real.log (Complex.normSq (r m))) / (Real.log C - Real.log ε))
          + 2 * (1 - C⁻¹ * ε) ^ (2 * k)) * (I.card : ℝ) := by
    nlinarith [hchain, hIcard, hXnn, hpowpos, hIpos]
  exact le_of_mul_le_mul_right hfinal hIpos

/-- The twisted Følner data. -/
def TFolnerData (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (m : G) (C : ℝ) : Prop :=
  ∀ k : ℕ, ∃ (F T : Finset G) (I : Finset F),
    (∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) ∧
    F.image (· * m) ⊆ T ∧
    (∀ i, (DetLB.gramOf_posSemidef (tcoeff σ r) F T).isHermitian.eigenvalues i ≤ C) ∧
    (∀ h ∈ I, ∀ w ∈ rball (tuElt σ r C) k, (h : G) * w ∈ F) ∧
    (F.card : ℝ) ≤ 2 * (I.card : ℝ) ∧ 0 < (I.card : ℝ)

theorem tfolnerData_of_hasFolner (σ : UCocycle G) (r : MonoidAlgebra ℂ G) {m : G}
    (hmr : r m ≠ 0) (hF : Master.HasFolner G) : TFolnerData σ r m (tbNorm σ r) := by
  classical
  intro k
  obtain ⟨F, I, hIF, hint, hcard, hne⟩ := hF (rball (tuElt σ r (tbNorm σ r)) k)
  have hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ F * r.support :=
    fun x hx y hy => Finset.mul_mem_mul hx hy
  have hfilter : I.filter (fun x => x ∈ F) = I := Finset.filter_true_of_mem (fun x hx => hIF hx)
  refine ⟨F, F * r.support, I.subtype (· ∈ F), hT, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mul_mem_mul hx (Finsupp.mem_support_iff.mpr hmr)
  · exact fun i => tgram_eigenvalues_le σ r F _ hT i
  · intro h hh w hw
    rw [Finset.mem_subtype] at hh
    exact hint _ hh w hw
  · rw [Finset.card_subtype, hfilter]; exact hcard
  · rw [Finset.card_subtype, hfilter]
    exact_mod_cast Finset.card_pos.mpr hne

theorem texists_alg2norm_lt (σ : UCocycle G) (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0)
    {C : ℝ} (hC : 0 < C) (hCm : Complex.normSq (r m) ≤ C)
    (hFD : TFolnerData σ r m C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, Conv.alg2norm (tpow σ (tuElt σ r C) k) < δ := by
  classical
  set K := Real.log C - Real.log (Complex.normSq (r m)) with hK
  have hKnn : 0 ≤ K := by
    have := Real.log_le_log (Complex.normSq_pos.mpr hmr) hCm
    simp only [hK]; linarith
  set t : ℝ := 4 * K / δ ^ 2 + 1 with ht
  have htpos : 0 < t := by positivity
  set ε : ℝ := C * Real.exp (-t) with hε
  have hεpos : 0 < ε := by positivity
  have hεC : ε < C := by
    have h1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    calc ε = C * Real.exp (-t) := hε
      _ < C * 1 := by exact mul_lt_mul_of_pos_left h1 hC
      _ = C := mul_one C
  have hlogε : Real.log ε = Real.log C - t := by
    rw [hε, Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]; ring
  have hL : Real.log C - Real.log ε = t := by rw [hlogε]; ring
  have hterm1 : 2 * (K / (Real.log C - Real.log ε)) < δ ^ 2 / 2 := by
    rw [hL]
    have hd2 : (δ : ℝ) ^ 2 ≠ 0 := by positivity
    have hexp : t * δ ^ 2 = 4 * K + δ ^ 2 := by rw [ht]; field_simp
    have h1 : K / t < δ ^ 2 / 4 := by
      rw [div_lt_div_iff₀ htpos (by norm_num : (0:ℝ) < 4)]
      nlinarith [hexp, hδ, sq_nonneg δ]
    linarith
  have hxnn : (0 : ℝ) ≤ 1 - C⁻¹ * ε := by
    have h := mul_le_mul_of_nonneg_left hεC.le (inv_pos.mpr hC).le
    rw [inv_mul_cancel₀ hC.ne'] at h
    linarith
  have hxlt : 1 - C⁻¹ * ε < 1 := by
    have : 0 < C⁻¹ * ε := by positivity
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ ^ 2 / 4 by positivity) hxlt
  obtain ⟨F, T, I, hT, hsubT, hub, hI, hIcard, hIpos⟩ := hFD N
  refine ⟨N, ?_⟩
  have hbound := talg2norm_sq_le_of_interior σ r hm hmr hC F T hT hsubT hub hCm N hεpos hεC I hI
    hIcard hIpos
  have hterm2 : (1 - C⁻¹ * ε) ^ (2 * N) ≤ (1 - C⁻¹ * ε) ^ N :=
    pow_le_pow_of_le_one hxnn hxlt.le (by omega)
  have hsq : Conv.alg2norm (tpow σ (tuElt σ r C) N) ^ 2 < δ ^ 2 := by
    have h1 : 2 * (K / (Real.log C - Real.log ε)) + 2 * (1 - C⁻¹ * ε) ^ (2 * N) < δ ^ 2 := by
      nlinarith [hterm1, hterm2, hN]
    calc Conv.alg2norm (tpow σ (tuElt σ r C) N) ^ 2
        ≤ 2 * (K / (Real.log C - Real.log ε)) + 2 * (1 - C⁻¹ * ε) ^ (2 * N) := hbound
      _ < δ ^ 2 := h1
  nlinarith [hsq, Conv.alg2norm_nonneg (tpow σ (tuElt σ r C) N), hδ]

/-- **TWISTED ATIYAH.**  A nonzero element of the twisted group algebra of a bi-orderable
Følner group acts injectively by twisted convolution on `ℓ²(G)`. -/
theorem eq_zero_of_tconv_eq_zero (σ : UCocycle G) (r : MonoidAlgebra ℂ G) (hr : r ≠ 0)
    (hF : Master.HasFolner G) (f : G → ℂ) (hf : Summable fun g => ‖f g‖ ^ 2)
    (hfr : tconv σ f r = 0) : f = 0 := by
  classical
  have hne : r.support.Nonempty := Finsupp.support_nonempty_iff.mpr hr
  set m := r.support.max' hne with hm
  have hmem : m ∈ r.support := r.support.max'_mem hne
  have hmr : r m ≠ 0 := Finsupp.mem_support_iff.mp hmem
  have hle : ∀ x ∈ r.support, x ≤ m := fun x hx => r.support.le_max' x hx
  refine eq_zero_of_alg2norm_small σ f hf (tbElt σ r) (((tbNorm σ r)⁻¹ : ℝ) : ℂ)
    (tconv_tbElt_eq_zero σ f r hfr) (fun δ hδ => ?_)
  exact texists_alg2norm_lt σ r hle hmr (tbNorm_pos σ r hmr) (normSq_le_tbNorm σ r hmr)
    (tfolnerData_of_hasFolner σ r hmr hF) hδ

end Tw
end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.Tw.ttrunc_tuElt
#print axioms GroupVN.Tw.tcolNorm_interior
#print axioms GroupVN.Tw.tsum_colNorm_eq
#print axioms GroupVN.Tw.talg2norm_mul_card_le
#print axioms GroupVN.Tw.tgram_eigenvalues_le
#print axioms GroupVN.Tw.normSq_le_tbNorm
#print axioms GroupVN.Tw.tbElt_eq_tmul_tstar
#print axioms GroupVN.Tw.tconv_tbElt_eq_zero
#print axioms GroupVN.Tw.talg2norm_sq_le_of_interior
#print axioms GroupVN.Tw.texists_alg2norm_lt
#print axioms GroupVN.Tw.eq_zero_of_tconv_eq_zero
