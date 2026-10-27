/-
# Atiyah for bi-orderable amenable groups — the assembly

Composes `AtiyahDeterminant` (the uniform determinant bound), `AtiyahConvolution` (the
Cauchy–Schwarz bridge) and `AtiyahFolner` (the interior lemma) into the injectivity statement.

The pieces meet like this.  Fix `0 ≠ r ∈ ℂ[G]` and set `b = r · r*`, `u = 1 - b/C`.

* `f ⋆ r = 0` ⟹ `f ⋆ u^k = f` exactly ⟹ `|f(x)| ≤ ‖u^k‖₂ ‖f‖₂`.        (`AtiyahConvolution`)
* `‖u^k‖₂²` is the `(h,h)` entry of the truncated `U_F^{2k}` at any interior `h`. (`AtiyahFolner`)
* `U_F = 1 - (gram r F T)/C`, and the Gram matrix has determinant `≥ |r(m)|^{2|F|}` uniformly, so
  most of its eigenvalues are bounded away from `0`.                        (`AtiyahDeterminant`)

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import AtiyahDeterminant
import AtiyahConvolution
import AtiyahFolner
import GroupVonNeumann

set_option maxHeartbeats 1000000

namespace GroupVN
namespace Master

open Matrix
open scoped Pointwise ComplexOrder

variable {G : Type*} [Group G] [DecidableEq G] [LinearOrder G]
  [CovariantClass G G (· * ·) (· < ·)] [CovariantClass G G (Function.swap (· * ·)) (· < ·)]

/-- The self-adjoint element `r · r*`.  Its truncations are exactly the Gram matrices of the
translates of `r`, which is what the determinant bound controls. -/
noncomputable def bElt (r : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G := r * DetLB.rstar r

/-- The contraction `1 - b/C`. -/
noncomputable def uElt (r : MonoidAlgebra ℂ G) (C : ℝ) : MonoidAlgebra ℂ G :=
  1 - ((C⁻¹ : ℝ) : ℂ) • bElt r

/-- Right convolution by `r` kills `f` ⟹ so does `b`. -/
theorem rconv_bElt_eq_zero (f : G → ℂ) (r : MonoidAlgebra ℂ G) (hfr : Conv.rconv f r = 0) :
    Conv.rconv f (bElt r) = 0 := by
  rw [bElt, Conv.rconv_mul, hfr, Conv.rconv_zero_fun]

/-- **The truncation of `u` is `1 - gram/C`.**  The bridge between the convolution picture and the
matrix picture. -/
theorem trunc_uElt (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) :
    Folner.trunc (uElt r C) F = 1 - ((C⁻¹ : ℝ) : ℂ) • DetLB.gram r F T := by
  ext g h
  have hg : DetLB.gram r F T g h = bElt r ((h : G)⁻¹ * (g : G)) :=
    DetLB.gram_eq_mul_rstar r F T hT g h
  have hone : (1 : MonoidAlgebra ℂ G) ((h : G)⁻¹ * (g : G)) = (1 : Matrix F F ℂ) g h := by
    by_cases hgh : g = h
    · subst hgh
      simp [MonoidAlgebra.one_def, Matrix.one_apply]
    · rw [Matrix.one_apply_ne hgh, MonoidAlgebra.one_def, Finsupp.single_apply, if_neg]
      intro hc
      exact hgh (Subtype.ext (by
        have : (h : G)⁻¹ * (g : G) = 1 := hc.symm
        simpa [eq_comm, inv_mul_eq_one] using this))
  have hL : Folner.trunc (uElt r C) F g h
      = (1 : MonoidAlgebra ℂ G) ((h : G)⁻¹ * (g : G))
        - ((C⁻¹ : ℝ) : ℂ) * (bElt r) ((h : G)⁻¹ * (g : G)) := rfl
  rw [hL, hone, ← hg]
  simp [Matrix.sub_apply, Matrix.smul_apply]

/-- The truncated contraction is Hermitian, because the Gram matrix is and `C` is real. -/
theorem trunc_uElt_isHermitian (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) :
    (Folner.trunc (uElt r C) F).IsHermitian := by
  rw [trunc_uElt r C F T hT]
  refine Matrix.IsHermitian.sub Matrix.isHermitian_one ?_
  have hH := (DetLB.gram_posSemidef r F T).isHermitian
  ext i j
  have hij : star (DetLB.gram r F T j i) = DetLB.gram r F T i j := by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.star_def, hij]

/-! ### The interior diagonal identity -/

/-- **At a point far enough inside `F`, the `(h,h)` entry of `U_F^{2k}` is exactly `‖u^k‖₂²`.**

This is what converts a statement about the trace of a finite matrix into a statement about the
`ℓ²` norm of a group-algebra element — the quantity the Cauchy–Schwarz bridge consumes. -/
theorem diag_trunc_pow (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ) (h : F)
    (hherm : (Folner.trunc u F).IsHermitian)
    (hint : ∀ w ∈ Folner.ball u k, (h : G) * w ∈ F) :
    ((Folner.trunc u F) ^ (2 * k)) h h = ((Conv.alg2norm (u ^ k) ^ 2 : ℝ) : ℂ) := by
  classical
  set M := Folner.trunc u F with hM
  have hMk : (M ^ k)ᴴ = M ^ k := by rw [Matrix.conjTranspose_pow, hherm]
  have hsplit : M ^ (2 * k) = (M ^ k)ᴴ * (M ^ k) := by rw [hMk, two_mul, pow_add]
  have hentry : ∀ g : F, (M ^ k)ᴴ h g * (M ^ k) g h
      = ((Complex.normSq ((u ^ k) ((h : G)⁻¹ * (g : G))) : ℝ) : ℂ) := by
    intro g
    rw [Matrix.conjTranspose_apply, hM, Folner.trunc_pow_apply u F k h hint g,
      Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hsplit, Matrix.mul_apply, Finset.sum_congr rfl (fun g _ => hentry g)]
  have hcoe : ∑ g : F, ((Complex.normSq ((u ^ k) ((h : G)⁻¹ * (g : G))) : ℝ) : ℂ)
      = ((∑ g ∈ F, Complex.normSq ((u ^ k) ((h : G)⁻¹ * g)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← Finset.sum_coe_sort F]
  rw [hcoe]
  congr 1
  have hsub : (u ^ k).support.image (fun d => (h : G) * d) ⊆ F := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact hint d (Folner.support_pow_subset_ball u k hd)
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
    rw [Conv.alg2norm, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [inv_mul_cancel_left, Complex.normSq_eq_norm_sq]
  · intro x _ hx
    have : (u ^ k) ((h : G)⁻¹ * x) = 0 := by
      by_contra hne
      exact hx (Finset.mem_image.mpr ⟨(h : G)⁻¹ * x, Finsupp.mem_support_iff.mpr hne,
        by rw [mul_inv_cancel_left]⟩)
    rw [this, map_zero]

/-! ### The eigenvalue sum bound -/

/-- **Splitting the trace at a threshold.** -/
theorem sum_one_sub_pow_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {C ε : ℝ} (hC : 0 < C) (hεC : ε ≤ C)
    (hnn : ∀ i, 0 ≤ hA.eigenvalues i) (hub : ∀ i, hA.eigenvalues i ≤ C) (k : ℕ) :
    ∑ i, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k)
      ≤ ((Finset.univ.filter (fun i => hA.eigenvalues i ≤ ε)).card : ℝ)
        + (Fintype.card n : ℝ) * (1 - C⁻¹ * ε) ^ (2 * k) := by
  classical
  set S := Finset.univ.filter (fun i => hA.eigenvalues i ≤ ε) with hS
  have hCinv : (0 : ℝ) < C⁻¹ := inv_pos.mpr hC
  have hCC : C⁻¹ * C = 1 := inv_mul_cancel₀ hC.ne'
  have hlow : ∀ i, 0 ≤ 1 - C⁻¹ * hA.eigenvalues i := by
    intro i
    have h := mul_le_mul_of_nonneg_left (hub i) hCinv.le
    rw [hCC] at h
    linarith
  have hεnn : 0 ≤ 1 - C⁻¹ * ε := by
    have h := mul_le_mul_of_nonneg_left hεC hCinv.le
    rw [hCC] at h
    linarith
  have hle1 : ∀ i, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k) ≤ 1 := by
    intro i
    refine pow_le_one₀ (hlow i) ?_
    have h0 : 0 ≤ C⁻¹ * hA.eigenvalues i := mul_nonneg hCinv.le (hnn i)
    linarith
  rw [← Finset.sum_add_sum_compl S]
  have hA1 : ∑ i ∈ S, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k) ≤ (S.card : ℝ) := by
    calc ∑ i ∈ S, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k) ≤ ∑ _i ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => hle1 i)
      _ = (S.card : ℝ) := by simp
  have hA2 : ∑ i ∈ Sᶜ, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k)
      ≤ (Fintype.card n : ℝ) * (1 - C⁻¹ * ε) ^ (2 * k) := by
    have hstep : ∀ i ∈ Sᶜ, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k)
        ≤ (1 - C⁻¹ * ε) ^ (2 * k) := by
      intro i hi
      have hgt : ε ≤ hA.eigenvalues i := by
        by_contra hc
        exact (Finset.mem_compl.mp hi)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_of_lt (not_le.mp hc)⟩)
      refine pow_le_pow_left₀ (hlow i) ?_ _
      have h := mul_le_mul_of_nonneg_left hgt hCinv.le
      linarith
    calc ∑ i ∈ Sᶜ, (1 - C⁻¹ * hA.eigenvalues i) ^ (2 * k)
        ≤ ∑ _i ∈ Sᶜ, (1 - C⁻¹ * ε) ^ (2 * k) := Finset.sum_le_sum hstep
      _ = ((Sᶜ).card : ℝ) * (1 - C⁻¹ * ε) ^ (2 * k) := by simp [mul_comm]
      _ ≤ (Fintype.card n : ℝ) * (1 - C⁻¹ * ε) ^ (2 * k) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_le_univ (Sᶜ)
  linarith

/-! ### The key estimate -/

/-- The diagonal of an EVEN power of a Hermitian matrix is the squared norm of a column. -/
theorem diag_even_pow {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (k : ℕ) (h : n) :
    (M ^ (2 * k)) h h = ((∑ g, ‖(M ^ k) g h‖ ^ 2 : ℝ) : ℂ) := by
  have hMk : (M ^ k)ᴴ = M ^ k := by rw [Matrix.conjTranspose_pow, hM]
  have hsplit : M ^ (2 * k) = (M ^ k)ᴴ * (M ^ k) := by rw [hMk, two_mul, pow_add]
  rw [hsplit, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Matrix.conjTranspose_apply, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]
  rfl

/-- The squared column norm of the `k`-th power of the truncation, as a real number. -/
noncomputable def colNorm (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ) (h : F) : ℝ :=
  ∑ g : F, ‖((Folner.trunc u F) ^ k) g h‖ ^ 2

theorem colNorm_nonneg (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ) (h : F) :
    0 ≤ colNorm u F k h := by
  unfold colNorm; positivity

/-- At an interior point the column norm is exactly `‖u^k‖₂²`. -/
theorem colNorm_interior (u : MonoidAlgebra ℂ G) (F : Finset G) (k : ℕ) (h : F)
    (hherm : (Folner.trunc u F).IsHermitian)
    (hint : ∀ w ∈ Folner.ball u k, (h : G) * w ∈ F) :
    colNorm u F k h = Conv.alg2norm (u ^ k) ^ 2 := by
  have h1 := diag_trunc_pow u F k h hherm hint
  have h2 := diag_even_pow hherm k h
  rw [h2] at h1
  exact_mod_cast h1

/-- **The trace identity.**  Summing the column norms over all of `F` gives the eigenvalue sum. -/
theorem sum_colNorm_eq (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (k : ℕ) :
    ∑ h : F, colNorm (uElt r C) F k h
      = ∑ i, (1 - C⁻¹ * (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i) ^ (2 * k) := by
  have hherm := trunc_uElt_isHermitian r C F T hT
  have htr : ((Folner.trunc (uElt r C) F) ^ (2 * k)).trace
      = ((∑ h : F, colNorm (uElt r C) F k h : ℝ) : ℂ) := by
    rw [Matrix.trace, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun h _ => by
      rw [Matrix.diag_apply, diag_even_pow hherm k h]; rfl)
  have htr2 : ((Folner.trunc (uElt r C) F) ^ (2 * k)).trace
      = ((∑ i, (1 - C⁻¹ * (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i) ^ (2 * k)
          : ℝ) : ℂ) := by
    rw [trunc_uElt r C F T hT]
    exact DetLB.trace_one_sub_smul_pow_real (DetLB.gram_posSemidef r F T).isHermitian C⁻¹ (2 * k)
  have := htr.symm.trans htr2
  exact_mod_cast this

/-- **THE KEY ESTIMATE.**  `‖u^k‖₂²` times the size of the interior is at most the eigenvalue sum. -/
theorem alg2norm_mul_card_le (r : MonoidAlgebra ℂ G) (C : ℝ) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (k : ℕ)
    (I : Finset F) (hI : ∀ h ∈ I, ∀ w ∈ Folner.ball (uElt r C) k, (h : G) * w ∈ F) :
    Conv.alg2norm (uElt r C ^ k) ^ 2 * (I.card : ℝ)
      ≤ ∑ i, (1 - C⁻¹ * (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i) ^ (2 * k) := by
  have hherm := trunc_uElt_isHermitian r C F T hT
  rw [← sum_colNorm_eq r C F T hT k]
  have hsub : ∑ h ∈ I, colNorm (uElt r C) F k h ≤ ∑ h : F, colNorm (uElt r C) F k h :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun h _ _ => colNorm_nonneg _ _ _ _)
  refine le_trans (le_of_eq ?_) hsub
  rw [Finset.sum_congr rfl (fun h hh => colNorm_interior (uElt r C) F k h hherm (hI h hh))]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### Combining the two bounds -/

/-- The eigenvalues of the Gram matrix are strictly positive: their product is bounded below by
`|r(m)|^{2|F|} > 0`, so none of them can vanish. -/
theorem gram_eigenvalues_pos (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0) (F T : Finset G)
    (hsubT : F.image (· * m) ⊆ T) (i : F) :
    0 < (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i := by
  have hnn := (DetLB.gram_posSemidef r F T).eigenvalues_nonneg i
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hdet := DetLB.gram_det_lower_bound r F T hm hmr hsubT
    have hzero : ∏ j, (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h.symm
    rw [hzero] at hdet
    have hpos : 0 < Complex.normSq (r m) ^ F.card :=
      pow_pos (Complex.normSq_pos.mpr hmr) _
    linarith

/-- **The combined bound.**  `‖u^k‖₂²` is controlled by a term that vanishes as the threshold `ε`
shrinks plus a term that vanishes as `k` grows — and, crucially, by nothing that depends on `F`. -/
theorem alg2norm_sq_le_of_interior (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0)
    {C : ℝ} (hC : 0 < C) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T)
    (hsubT : F.image (· * m) ⊆ T)
    (hub : ∀ i, (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i ≤ C)
    (hCm : Complex.normSq (r m) ≤ C)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hεC : ε < C)
    (I : Finset F) (hI : ∀ h ∈ I, ∀ w ∈ Folner.ball (uElt r C) k, (h : G) * w ∈ F)
    (hIcard : (F.card : ℝ) ≤ 2 * (I.card : ℝ)) (hIpos : 0 < (I.card : ℝ)) :
    Conv.alg2norm (uElt r C ^ k) ^ 2
      ≤ 2 * ((Real.log C - Real.log (Complex.normSq (r m))) / (Real.log C - Real.log ε))
        + 2 * (1 - C⁻¹ * ε) ^ (2 * k) := by
  classical
  set hH := (DetLB.gram_posSemidef r F T).isHermitian with hHdef
  set ev := hH.eigenvalues with hev
  have hpos : ∀ i, 0 < ev i := gram_eigenvalues_pos r hm hmr F T hsubT
  have hnn : ∀ i, 0 ≤ ev i := fun i => (hpos i).le
  have hcardF : Fintype.card F = F.card := Fintype.card_coe F
  -- the spectral side
  have hkey := alg2norm_mul_card_le r C F T hT k I hI
  have hsplit := sum_one_sub_pow_le hH hC hεC.le hnn hub k
  -- the small-eigenvalue count
  have hdet := DetLB.gram_det_lower_bound r F T hm hmr hsubT
  have hdpos : 0 < Complex.normSq (r m) ^ F.card := pow_pos (Complex.normSq_pos.mpr hmr) _
  have hcount := DetLB.card_small_eigenvalues_le hH hC hdpos hε hpos hub hdet
  have hlogd : Real.log (Complex.normSq (r m) ^ F.card)
      = (F.card : ℝ) * Real.log (Complex.normSq (r m)) :=
    Real.log_pow _ _
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
  have hchain : Conv.alg2norm (uElt r C ^ k) ^ 2 * (I.card : ℝ)
      ≤ (F.card : ℝ) * ((Real.log C - Real.log (Complex.normSq (r m)))
          / (Real.log C - Real.log ε))
        + (F.card : ℝ) * (1 - C⁻¹ * ε) ^ (2 * k) := by
    rw [hcardF] at hsplit
    linarith [hkey, hsplit, hsmall]
  have hfinal : Conv.alg2norm (uElt r C ^ k) ^ 2 * (I.card : ℝ)
      ≤ (2 * ((Real.log C - Real.log (Complex.normSq (r m))) / (Real.log C - Real.log ε))
          + 2 * (1 - C⁻¹ * ε) ^ (2 * k)) * (I.card : ℝ) := by
    nlinarith [hchain, hIcard, hXnn, hpowpos, hIpos]
  exact le_of_mul_le_mul_right hfinal hIpos

/-! ### The vanishing sequence, and injectivity -/

/-- The Følner data the argument needs, packaged: for every `k`, a truncation `F` (with position
set `T`) most of whose points are `k`-interior. -/
def FolnerData (r : MonoidAlgebra ℂ G) (m : G) (C : ℝ) : Prop :=
  ∀ k : ℕ, ∃ (F T : Finset G) (I : Finset F),
    (∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) ∧
    F.image (· * m) ⊆ T ∧
    (∀ i, (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i ≤ C) ∧
    (∀ h ∈ I, ∀ w ∈ Folner.ball (uElt r C) k, (h : G) * w ∈ F) ∧
    (F.card : ℝ) ≤ 2 * (I.card : ℝ) ∧ 0 < (I.card : ℝ)

/-- **The `ℓ²` norms of `u^k` can be made arbitrarily small.**  Choose the threshold `ε` first (it
controls the eigenvalue-count term), then `k` (which controls the decay term). -/
theorem exists_alg2norm_lt (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0)
    {C : ℝ} (hC : 0 < C) (hCm : Complex.normSq (r m) ≤ C)
    (hFD : FolnerData r m C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, Conv.alg2norm (uElt r C ^ k) < δ := by
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
  -- the eps-term is small
  have hterm1 : 2 * (K / (Real.log C - Real.log ε)) < δ ^ 2 / 2 := by
    rw [hL]
    have hd2 : (δ : ℝ) ^ 2 ≠ 0 := by positivity
    have hexp : t * δ ^ 2 = 4 * K + δ ^ 2 := by
      rw [ht]; field_simp
    have h1 : K / t < δ ^ 2 / 4 := by
      rw [div_lt_div_iff₀ htpos (by norm_num : (0:ℝ) < 4)]
      nlinarith [hexp, hδ, sq_nonneg δ]
    linarith
  -- the k-term is small
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
  have hbound := alg2norm_sq_le_of_interior r hm hmr hC F T hT hsubT hub hCm N hεpos hεC I hI
    hIcard hIpos
  have hterm2 : (1 - C⁻¹ * ε) ^ (2 * N) ≤ (1 - C⁻¹ * ε) ^ N :=
    pow_le_pow_of_le_one hxnn hxlt.le (by omega)
  have hsq : Conv.alg2norm (uElt r C ^ N) ^ 2 < δ ^ 2 := by
    have h1 : 2 * (K / (Real.log C - Real.log ε)) + 2 * (1 - C⁻¹ * ε) ^ (2 * N) < δ ^ 2 := by
      nlinarith [hterm1, hterm2, hN]
    calc Conv.alg2norm (uElt r C ^ N) ^ 2
        ≤ 2 * (K / (Real.log C - Real.log ε)) + 2 * (1 - C⁻¹ * ε) ^ (2 * N) := hbound
      _ < δ ^ 2 := h1
  nlinarith [hsq, Conv.alg2norm_nonneg (uElt r C ^ N), hδ]

/-- **ATIYAH, 1×1 case, for a bi-orderable group with the Følner data.**

A nonzero element of `ℂ[G]` acts injectively by right convolution on `ℓ²(G)`. -/
theorem eq_zero_of_rconv_eq_zero (r : MonoidAlgebra ℂ G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0)
    {C : ℝ} (hC : 0 < C) (hCm : Complex.normSq (r m) ≤ C)
    (hFD : FolnerData r m C)
    (f : G → ℂ) (hf : Summable fun g => ‖f g‖ ^ 2) (hfr : Conv.rconv f r = 0) :
    f = 0 :=
  Conv.eq_zero_of_alg2norm_small f hf (bElt r) (((C⁻¹ : ℝ) : ℂ))
    (rconv_bElt_eq_zero f r hfr)
    (fun δ hδ => exists_alg2norm_lt r hm hmr hC hCm hFD hδ)

/-! ### The eigenvalue ceiling, uniform in the truncation -/

/-- The `ℓ¹` norm of `r · r*`. -/
noncomputable def bNorm (r : MonoidAlgebra ℂ G) : ℝ := ∑ x ∈ (bElt r).support, ‖bElt r x‖

theorem bNorm_nonneg (r : MonoidAlgebra ℂ G) : 0 ≤ bNorm r :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- **Row sums of the Gram matrix are bounded independently of `F`.**  Each row is a slice of the
single element `r · r*`, reindexed injectively, so the row sum can never exceed that element's
`ℓ¹` norm.  This is what makes the eigenvalue ceiling `C` a constant rather than a function of the
truncation. -/
theorem gram_rowSum_le (r : MonoidAlgebra ℂ G) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (g : F) :
    ∑ h : F, ‖DetLB.gram r F T g h‖ ≤ bNorm r := by
  classical
  have hg : ∀ h : F, DetLB.gram r F T g h = bElt r ((h : G)⁻¹ * (g : G)) := fun h =>
    DetLB.gram_eq_mul_rstar r F T hT g h
  rw [Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => by rw [hg h]),
    Finset.sum_coe_sort F (fun h => ‖bElt r (h⁻¹ * (g : G))‖)]
  have hinj : ∀ a ∈ F, ∀ b ∈ F, a⁻¹ * (g : G) = b⁻¹ * (g : G) → a = b := by
    intro a _ b _ hab
    simpa using mul_right_cancel hab
  rw [← Finset.sum_image (f := fun x => ‖bElt r x‖) (g := fun h => h⁻¹ * (g : G)) hinj]
  have hsplit : ∑ x ∈ F.image (fun h => h⁻¹ * (g : G)), ‖bElt r x‖
      = ∑ x ∈ (F.image (fun h => h⁻¹ * (g : G))) ∩ (bElt r).support, ‖bElt r x‖ := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro x hx hnot
    have : bElt r x = 0 := by
      by_contra hne
      exact hnot (Finset.mem_inter.mpr ⟨hx, Finsupp.mem_support_iff.mpr hne⟩)
    rw [this, norm_zero]
  rw [hsplit, bNorm]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun _ _ _ => norm_nonneg _)

/-- Hence every eigenvalue of every Gram matrix is at most `bNorm r`. -/
theorem gram_eigenvalues_le (r : MonoidAlgebra ℂ G) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (i : F) :
    (DetLB.gram_posSemidef r F T).isHermitian.eigenvalues i ≤ bNorm r :=
  DetLB.eigenvalues_le_of_rowSum_le _ (gram_rowSum_le r F T hT) i

/-- The value of `r · r*` at the identity is the squared `ℓ²` norm of `r`. -/
theorem bElt_one (r : MonoidAlgebra ℂ G) :
    bElt r 1 = ((∑ y ∈ r.support, Complex.normSq (r y) : ℝ) : ℂ) := by
  rw [bElt, MonoidAlgebra.mul_apply_left, Finsupp.sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [DetLB.rstar_apply, Complex.normSq_eq_conj_mul_self]
  simp [mul_comm]

/-- `|r(m)|² ≤ bNorm r`, and `bNorm r > 0` — the two side conditions the main theorem needs. -/
theorem normSq_le_bNorm (r : MonoidAlgebra ℂ G) {m : G} (hmr : r m ≠ 0) :
    Complex.normSq (r m) ≤ bNorm r := by
  classical
  have hmem : m ∈ r.support := Finsupp.mem_support_iff.mpr hmr
  have h1 : Complex.normSq (r m) ≤ ∑ y ∈ r.support, Complex.normSq (r y) :=
    Finset.single_le_sum (f := fun y => Complex.normSq (r y))
      (fun y _ => Complex.normSq_nonneg _) hmem
  have hb1 : ‖bElt r 1‖ = ∑ y ∈ r.support, Complex.normSq (r y) := by
    rw [bElt_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hpos : (0 : ℝ) < ∑ y ∈ r.support, Complex.normSq (r y) := by
    refine lt_of_lt_of_le ?_ h1
    exact Complex.normSq_pos.mpr hmr
  have hmem1 : (1 : G) ∈ (bElt r).support := by
    refine Finsupp.mem_support_iff.mpr ?_
    intro hc
    rw [hc] at hb1
    simp at hb1
    linarith [hpos, hb1]
  have h2 : ‖bElt r 1‖ ≤ bNorm r :=
    Finset.single_le_sum (f := fun x => ‖bElt r x‖) (fun _ _ => norm_nonneg _) hmem1
  rw [hb1] at h2
  linarith

theorem bNorm_pos (r : MonoidAlgebra ℂ G) {m : G} (hmr : r m ≠ 0) : 0 < bNorm r :=
  lt_of_lt_of_le (Complex.normSq_pos.mpr hmr) (normSq_le_bNorm r hmr)

/-! ### From a purely combinatorial Følner property to the full data -/

/-- **The combinatorial Følner property.**  For every finite `W`, some finite `F` has at least half
its points surviving right multiplication by all of `W`.  No limits, no measures — a single
inequality between two cardinalities. -/
def HasFolner (G : Type*) [Group G] [DecidableEq G] : Prop :=
  ∀ W : Finset G, ∃ F I : Finset G, I ⊆ F ∧ (∀ h ∈ I, ∀ w ∈ W, h * w ∈ F) ∧
    (F.card : ℝ) ≤ 2 * (I.card : ℝ) ∧ I.Nonempty

/-- Everything else the main theorem needs is automatic, so the combinatorial property suffices. -/
theorem folnerData_of_hasFolner (r : MonoidAlgebra ℂ G) {m : G} (hmr : r m ≠ 0)
    (hF : HasFolner G) : FolnerData r m (bNorm r) := by
  classical
  intro k
  obtain ⟨F, I, hIF, hint, hcard, hne⟩ := hF (Folner.ball (uElt r (bNorm r)) k)
  have hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ F * r.support :=
    fun x hx y hy => Finset.mul_mem_mul hx hy
  have hfilter : I.filter (fun x => x ∈ F) = I := Finset.filter_true_of_mem (fun x hx => hIF hx)
  refine ⟨F, F * r.support, I.subtype (· ∈ F), hT, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mul_mem_mul hx (Finsupp.mem_support_iff.mpr hmr)
  · exact fun i => gram_eigenvalues_le r F _ hT i
  · intro h hh w hw
    rw [Finset.mem_subtype] at hh
    exact hint _ hh w hw
  · rw [Finset.card_subtype, hfilter]; exact hcard
  · rw [Finset.card_subtype, hfilter]
    exact_mod_cast Finset.card_pos.mpr hne


end Master

namespace Heisenberg

open Master

theorem box_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') : box p q ⊆ box p' q' := by
  intro x hx
  rw [mem_box] at hx ⊢
  have hp' : (p : ℤ) ≤ p' := by exact_mod_cast hp
  have hq' : (q : ℤ) ≤ q' := by exact_mod_cast hq
  exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩,
    ⟨by linarith [hx.2.1.1], by linarith [hx.2.1.2]⟩,
    by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩

theorem box_nonempty (p q : ℕ) : (box p q).Nonempty := by
  refine ⟨1, ?_⟩
  rw [mem_box]
  simp [one_a, one_b, one_c]

/-- **`H₃(ℤ)` is Følner in the combinatorial sense**, witnessed by explicit boxes. -/
theorem heis_hasFolner : HasFolner Heis := by
  intro W
  obtain ⟨m₀, hm₀⟩ := exists_box_superset W
  refine ⟨box (10 * m₀ + 10) ((10 * m₀ + 10) * (10 * m₀ + 10)),
          box (9 * m₀ + 10) (90 * m₀ * m₀ + 189 * m₀ + 100), ?_, ?_, ?_, box_nonempty _ _⟩
  · exact box_mono (by omega) (by nlinarith [Nat.zero_le m₀])
  · intro h hh w hw
    exact interior_mul_subset m₀ h hh w (hm₀ hw)
  · exact_mod_cast interior_card_ge m₀

/-- **THE ATIYAH CONJECTURE FOR `H₃(ℤ)`, 1×1 CASE.**

A nonzero element of `ℂ[H₃(ℤ)]` acts injectively by right convolution on `ℓ²(H₃(ℤ))`.
Unconditional: no carried hypotheses, no axioms beyond Lean's own. -/
theorem atiyah_heisenberg (r : MonoidAlgebra ℂ Heis) (hr : r ≠ 0)
    (f : Heis → ℂ) (hf : Summable fun g => ‖f g‖ ^ 2) (hfr : Conv.rconv f r = 0) :
    f = 0 := by
  classical
  have hne : r.support.Nonempty := Finsupp.support_nonempty_iff.mpr hr
  set m := r.support.max' hne with hm
  have hmem : m ∈ r.support := r.support.max'_mem hne
  have hmr : r m ≠ 0 := Finsupp.mem_support_iff.mp hmem
  have hle : ∀ x ∈ r.support, x ≤ m := fun x hx => r.support.le_max' x hx
  exact Master.eq_zero_of_rconv_eq_zero r hle hmr (Master.bNorm_pos r hmr)
    (Master.normSq_le_bNorm r hmr)
    (Master.folnerData_of_hasFolner r hmr heis_hasFolner) f hf hfr

end Heisenberg

namespace Master

variable {G : Type*} [Group G] [DecidableEq G]

/-! ### The left-convolution form -/

/-- `r` with its support inverted: `flipElt r x = r x⁻¹`. -/
noncomputable def flipElt (r : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  Finsupp.equivMapDomain (Equiv.inv G) r

@[simp] theorem flipElt_apply (r : MonoidAlgebra ℂ G) (x : G) : flipElt r x = r x⁻¹ := rfl

theorem flipElt_ne_zero {r : MonoidAlgebra ℂ G} (hr : r ≠ 0) : flipElt r ≠ 0 := by
  intro hc
  apply hr
  ext x
  have hz : ∀ y : G, (0 : MonoidAlgebra ℂ G) y = 0 := fun _ => rfl
  have h := congrFun (congrArg (fun (t : MonoidAlgebra ℂ G) => (t : G → ℂ)) hc) x⁻¹
  simp only [flipElt_apply, inv_inv] at h
  rw [hz] at h
  rw [hz]
  exact h

end Master

namespace Heisenberg

open Master

/-- **ATIYAH FOR `H₃(ℤ)`, LEFT-CONVOLUTION FORM.**  A nonzero group-algebra element acting on the
LEFT is injective too — the statement in the shape the `vN(G)` development uses. -/
theorem atiyah_heisenberg_left (r : MonoidAlgebra ℂ Heis) (hr : r ≠ 0)
    (g : Heis → ℂ) (hg : Summable fun x => ‖g x‖ ^ 2)
    (hlc : ∀ y : Heis, (r.sum fun x c => c * g (x⁻¹ * y)) = 0) : g = 0 := by
  classical
  set f : Heis → ℂ := fun y => g y⁻¹ with hf
  have hfsum : Summable fun y => ‖f y‖ ^ 2 := by
    exact ((Equiv.inv Heis).summable_iff (f := fun x => ‖g x‖ ^ 2)).mpr hg
  have hrc : Conv.rconv f (flipElt r) = 0 := by
    funext y
    have hkey : Conv.rconv f (flipElt r) y = r.sum fun x c => c * g (x⁻¹ * y⁻¹) := by
      rw [Conv.rconv, flipElt, Finsupp.sum_equivMapDomain]
      refine Finsupp.sum_congr (fun x _ => ?_)
      simp [hf, mul_inv_rev]
    rw [hkey, hlc y⁻¹]
    rfl
  have hf0 : f = 0 := atiyah_heisenberg (flipElt r) (flipElt_ne_zero hr) f hfsum hrc
  funext x
  have := congrFun hf0 x⁻¹
  simpa [hf] using this

/-! ### Connecting to `groupAlgOp` on `ℓ²` -/

theorem groupAlgOp_apply (s : Finset Heis) (c : Heis → ℂ) (f : L2 Heis) (y : Heis) :
    ((groupAlgOp s c f : L2 Heis) : Heis → ℂ) y
      = ∑ g ∈ s, c g * (f : Heis → ℂ) (g⁻¹ * y) := by
  rw [groupAlgOp, lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, leftTranslate_apply]

theorem summable_sq_of_memLp (f : L2 Heis) :
    Summable fun x => ‖(f : Heis → ℂ) x‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have h := (memℓp_gen_iff hp).mp f.2
  simpa [Real.rpow_natCast] using h

/-- **ATIYAH FOR `H₃(ℤ)` IN THE `vN(G)` FORM — unconditional.**

A group-algebra operator with some nonzero coefficient is injective on `ℓ²(H₃(ℤ))`.  This is the
conclusion that `GroupVN.injective_of_atiyahConjecture` derives *from* the conjecture; here it is
proved outright. -/
theorem groupAlgOp_injective (s : Finset Heis) (c : Heis → ℂ)
    (hc : ∃ x ∈ s, c x ≠ 0) (f : L2 Heis) (hf0 : groupAlgOp s c f = 0) : f = 0 := by
  classical
  obtain ⟨x₀, hx₀s, hx₀⟩ := hc
  set c' : Heis → ℂ := fun x => if x ∈ s then c x else 0 with hc'
  have hmem : ∀ a : Heis, c' a ≠ 0 → a ∈ s := by
    intro a ha
    by_contra hcon
    exact ha (by simp [hc', hcon])
  set r : MonoidAlgebra ℂ Heis := Finsupp.onFinset s c' hmem with hr
  have hrapp : ∀ x, r x = c' x := fun x => rfl
  have hrne : r ≠ 0 := by
    intro hzero
    have : r x₀ = 0 := by rw [hzero]; rfl
    rw [hrapp, hc'] at this
    simp [hx₀s] at this
    exact hx₀ this
  have hsupp : r.support ⊆ s := Finsupp.support_onFinset_subset
  have hlc : ∀ y : Heis, (r.sum fun x cx => cx * (f : Heis → ℂ) (x⁻¹ * y)) = 0 := by
    intro y
    rw [Finsupp.sum_of_support_subset r hsupp _ (by intro i _; simp)]
    have hz : ((groupAlgOp s c f : L2 Heis) : Heis → ℂ) y = 0 := by
      rw [hf0]; rfl
    rw [groupAlgOp_apply] at hz
    rw [← hz]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [hrapp, hc']
    rw [if_pos hg]
  have hfun : (f : Heis → ℂ) = 0 :=
    atiyah_heisenberg_left r hrne _ (summable_sq_of_memLp f) hlc
  exact Subtype.ext (by rw [hfun]; rfl)

end Heisenberg

end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.Master.rconv_bElt_eq_zero
#print axioms GroupVN.Master.trunc_uElt
#print axioms GroupVN.Master.trunc_uElt_isHermitian
#print axioms GroupVN.Master.diag_trunc_pow
#print axioms GroupVN.Master.sum_one_sub_pow_le
#print axioms GroupVN.Master.diag_even_pow
#print axioms GroupVN.Master.sum_colNorm_eq
#print axioms GroupVN.Master.alg2norm_mul_card_le
#print axioms GroupVN.Master.gram_eigenvalues_pos
#print axioms GroupVN.Master.alg2norm_sq_le_of_interior
#print axioms GroupVN.Master.exists_alg2norm_lt
#print axioms GroupVN.Master.eq_zero_of_rconv_eq_zero
#print axioms GroupVN.Master.gram_rowSum_le
#print axioms GroupVN.Master.gram_eigenvalues_le
#print axioms GroupVN.Master.bElt_one
#print axioms GroupVN.Master.normSq_le_bNorm
#print axioms GroupVN.Master.bNorm_pos
#print axioms GroupVN.Master.folnerData_of_hasFolner
#print axioms GroupVN.Heisenberg.heis_hasFolner
#print axioms GroupVN.Heisenberg.atiyah_heisenberg
#print axioms GroupVN.Heisenberg.atiyah_heisenberg_left
#print axioms GroupVN.Heisenberg.groupAlgOp_injective
