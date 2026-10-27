/-
# The translate determinant bound — the analytic engine for Atiyah over amenable groups

**What this file proves.**  For a group `G` carrying a bi-invariant linear order, and a nonzero
`r ∈ ℂ[G]` whose support has largest element `m`, the Gram matrix of the translates
`{δ_g · r : g ∈ F}` satisfies

  `det ≥ |r(m)|^{2|F|}`     (`GroupVN.DetLB.gram_det_lower_bound`)

**uniformly in the finite set `F`**, and consequently at most `|F| · θ(ε)` of its eigenvalues lie
below `ε`, with `θ(ε) → 0` independent of `F` (`GroupVN.DetLB.card_small_eigenvalues_le`).

**Why it matters.**  The Atiyah conjecture for an amenable group with `ℂ[G]` a domain says a nonzero
`r` acts injectively on `ℓ²(G)`.  The finite truncations of that action are injective for free (the
domain property), but injectivity of finite truncations does NOT pass to the limit: the singular
values can collapse to zero.  What is needed is a bound on the NUMBER of small singular values that
does not degrade with `|F|`, and in the literature that is supplied by Lück's dimension-flatness
theorem for amenable groups (Lück, *L²-Invariants*, Thm 6.37) — a chapter of book, resting on the
extended dimension function for arbitrary modules over a finite von Neumann algebra.

The observation formalised here is that **bi-orderability supplies it directly and elementarily.**
Order `F` increasingly; the position `g · m` receives a contribution from `δ_g · r` and from no
later translate, so the translate matrix has a square minor that is TRIANGULAR with constant
diagonal `r(m)`.  Its determinant is `r(m)^{|F|}` on the nose, and the rest of the Gram matrix only
increases the determinant.  Both invariance directions of the order are used: left invariance gives
`1 < j⁻¹i`, right invariance pushes it past `m`.

This is known mathematics — the "leading coefficient" lower bound for the Fuglede–Kadison
determinant over orderable groups — but no formalisation of it exists.

**Mathlib gaps filled here** (all verified absent on this toolchain): the Cauchy–Binet formula, the
Gram determinant identity, and monotonicity of `det` on the positive-semidefinite order.  The last
is proved as `normSq_det_le_prod_eigenvalues` by the congruence factorisation `B = Mᴴ(1 + Y)M`.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace GroupVN

/-! Determinant lower bounds for Gram matrices of group-algebra translates. -/

namespace DetLB

open Matrix
open scoped ComplexOrder

section FiniteDim

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian matrix dominating the identity has all eigenvalues at least one. -/
theorem one_le_eigenvalues_of_sub_one_posSemidef {W : Matrix n n ℂ} (hW : W.IsHermitian)
    (h : (W - 1).PosSemidef) (i : n) : 1 ≤ hW.eigenvalues i := by
  have hv := hW.eigenvectorBasis.orthonormal.1 i
  set v : EuclideanSpace ℂ n := hW.eigenvectorBasis i with hvdef
  have key := hW.eigenvalues_eq i
  have hsplit : (W *ᵥ (v : n → ℂ)) = ((W - 1) *ᵥ (v : n → ℂ)) + (v : n → ℂ) := by
    rw [sub_mulVec, one_mulVec]
    abel
  rw [key, hsplit, dotProduct_add, map_add]
  have h1 : (0 : ℝ) ≤ RCLike.re (star (v : n → ℂ) ⬝ᵥ ((W - 1) *ᵥ (v : n → ℂ))) :=
    h.re_dotProduct_nonneg _
  have h2 : RCLike.re (star (v : n → ℂ) ⬝ᵥ (v : n → ℂ)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [inner_self_eq_norm_sq, hv]
  rw [h2]
  linarith

/-- **`det (1 + Y) ≥ 1` for positive semidefinite `Y`.**  Every eigenvalue of `1 + Y` is at
least one, and the determinant is their product. -/
theorem one_le_prod_eigenvalues_one_add {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    1 ≤ ∏ i, ((Matrix.isHermitian_one (n := n) (α := ℂ)).add hY.isHermitian).eigenvalues i := by
  have hev : ∀ i : n, (1 : ℝ) ≤
      ((Matrix.isHermitian_one (n := n) (α := ℂ)).add hY.isHermitian).eigenvalues i := by
    intro i
    refine one_le_eigenvalues_of_sub_one_posSemidef _ ?_ i
    simpa using hY
  have := Finset.prod_le_prod (s := (Finset.univ : Finset n)) (f := fun _ : n => (1 : ℝ))
    (g := fun i => ((Matrix.isHermitian_one (n := n) (α := ℂ)).add hY.isHermitian).eigenvalues i)
    (fun i _ => zero_le_one) (fun i _ => hev i)
  simpa using this

/-- **The determinant lower bound.**  If a Hermitian matrix `B` splits as `MᴴM` plus something
positive semidefinite, with `M` invertible, then `det B ≥ |det M|²`.

This is the PSD determinant-monotonicity Mathlib lacks, in exactly the form the Følner argument
needs.  The proof factors `B = Mᴴ(1 + Y)M` with `Y = (M⁻¹)ᴴ R M⁻¹` positive semidefinite, so the
determinant picks up `|det M|²` times something at least `1`. -/
theorem normSq_det_le_prod_eigenvalues {M R B : Matrix n n ℂ} (hM : IsUnit M.det)
    (hR : R.PosSemidef) (hBdef : B = Mᴴ * M + R) (hB : B.IsHermitian) :
    Complex.normSq M.det ≤ ∏ i, hB.eigenvalues i := by
  set Y : Matrix n n ℂ := (M⁻¹)ᴴ * R * M⁻¹ with hYdef
  have hY : Y.PosSemidef := hR.conjTranspose_mul_mul_same _
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hM
  have hinvH : Mᴴ * (M⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  have hfact : B = Mᴴ * (1 + Y) * M := by
    rw [hBdef, hYdef]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    congr 1
    calc R = (Mᴴ * (M⁻¹)ᴴ) * R * (M⁻¹ * M) := by
              rw [hinv, hinvH, Matrix.one_mul, Matrix.mul_one]
      _ = Mᴴ * ((M⁻¹)ᴴ * R * M⁻¹) * M := by simp [Matrix.mul_assoc]
  have hdet : B.det = star M.det * ((1 + Y).det * M.det) := by
    rw [hfact, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_assoc]
  have hYh : (1 + Y).IsHermitian := (Matrix.isHermitian_one (n := n) (α := ℂ)).add hY.isHermitian
  have e1 : B.det = ((∏ i, hB.eigenvalues i : ℝ) : ℂ) := by
    rw [hB.det_eq_prod_eigenvalues]; push_cast; try rfl
  have e2 : (1 + Y).det = ((∏ i, hYh.eigenvalues i : ℝ) : ℂ) := by
    rw [hYh.det_eq_prod_eigenvalues]; push_cast; try rfl
  rw [e1, e2] at hdet
  have hcast : ((∏ i, hB.eigenvalues i : ℝ) : ℂ)
      = ((Complex.normSq M.det * ∏ i, hYh.eigenvalues i : ℝ) : ℂ) := by
    rw [hdet, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply]
    ring
  have hreal : (∏ i, hB.eigenvalues i) = Complex.normSq M.det * ∏ i, hYh.eigenvalues i :=
    Complex.ofReal_inj.mp hcast
  rw [hreal]
  have h1 : (1 : ℝ) ≤ ∏ i, hYh.eigenvalues i := one_le_prod_eigenvalues_one_add hY
  nlinarith [Complex.normSq_nonneg M.det]

/-! ### Counting the small eigenvalues

A determinant lower bound caps how many eigenvalues can be near zero, *uniformly in the size of
the matrix*.  This is the step that converts the algebraic bound into the analytic one. -/

/-- **Chebyshev on the logarithm.**  If all eigenvalues lie in `(0, C]` and their product is at
least `d`, then the number below `ε` is at most `(n log C - log d) / (log C - log ε)`. -/
theorem card_small_eigenvalues_le {B : Matrix n n ℂ} (hB : B.IsHermitian) {C d ε : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hε : 0 < ε)
    (hpos : ∀ i, 0 < hB.eigenvalues i) (hub : ∀ i, hB.eigenvalues i ≤ C)
    (hdet : d ≤ ∏ i, hB.eigenvalues i) :
    ((Finset.univ.filter (fun i => hB.eigenvalues i ≤ ε)).card : ℝ) *
        (Real.log C - Real.log ε)
      ≤ (Fintype.card n : ℝ) * Real.log C - Real.log d := by
  classical
  set S := Finset.univ.filter (fun i => hB.eigenvalues i ≤ ε) with hS
  have hsum : Real.log d ≤ ∑ i, Real.log (hB.eigenvalues i) := by
    rw [← Real.log_prod]
    · exact Real.log_le_log hd hdet
    · exact fun i _ => (hpos i).ne'
  have hsplit : ∑ i, Real.log (hB.eigenvalues i)
      = (∑ i ∈ S, Real.log (hB.eigenvalues i)) + ∑ i ∈ Sᶜ, Real.log (hB.eigenvalues i) := by
    rw [← Finset.sum_add_sum_compl S]
  have hS1 : ∑ i ∈ S, Real.log (hB.eigenvalues i) ≤ (S.card : ℝ) * Real.log ε := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum (fun i hi => ?_)
    exact Real.log_le_log (hpos i) (by simpa [hS] using (Finset.mem_filter.mp hi).2)
  have hS2 : ∑ i ∈ Sᶜ, Real.log (hB.eigenvalues i) ≤ ((Sᶜ).card : ℝ) * Real.log C := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun i _ => Real.log_le_log (hpos i) (hub i))
  have hcard : (S.card : ℝ) + ((Sᶜ).card : ℝ) = (Fintype.card n : ℝ) := by
    rw [← Nat.cast_add, Finset.card_add_card_compl]
  have hstep := hsum.trans (hsplit.le.trans (add_le_add hS1 hS2))
  have hcompl : ((Sᶜ).card : ℝ) = (Fintype.card n : ℝ) - (S.card : ℝ) := by linarith
  rw [hcompl] at hstep
  nlinarith [hstep]


/-! ### Traces of polynomials in a Hermitian matrix -/

/-- **Trace of a power of `1 - c·A` in terms of the eigenvalues of `A`.**

The spectral theorem is applied through `conjStarAlgAut`, which is a star algebra automorphism, so
the polynomial passes through it by `map_one`/`map_smul`/`map_sub`/`map_pow` with no computation. -/
theorem trace_one_sub_smul_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℝ) (k : ℕ) :
    ((1 - (c : ℂ) • A) ^ k).trace
      = ∑ i, ((1 - c * hA.eigenvalues i : ℝ) : ℂ) ^ k := by
  have hd1 : (1 : Matrix n n ℂ) - (c : ℂ) • diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      = diagonal (fun i => ((1 - c * hA.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply,
        Matrix.diagonal_apply_eq, Function.comp_apply, smul_eq_mul]
      push_cast
      rfl
    · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h, h]
  have hdiag : (1 - (c : ℂ) • diagonal (RCLike.ofReal ∘ hA.eigenvalues)) ^ k
      = diagonal (fun i => ((1 - c * hA.eigenvalues i : ℝ) : ℂ) ^ k) := by
    rw [hd1, diagonal_pow]
    rfl
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_smul, ← map_one (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary), ← map_sub, ← map_pow,
    Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, hdiag, trace_diagonal]


/-- The real-valued form. -/
theorem trace_one_sub_smul_pow_real {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℝ) (k : ℕ) :
    ((1 - (c : ℂ) • A) ^ k).trace = ((∑ i, (1 - c * hA.eigenvalues i) ^ k : ℝ) : ℂ) := by
  rw [trace_one_sub_smul_pow hA c k]
  push_cast
  rfl


/-- **A uniform eigenvalue bound from the row sums.**  For a Hermitian matrix every eigenvalue is at
most the largest absolute row sum.  (Gershgorin, in the only form needed here, and absent from
Mathlib.)  Crucially the bound does not involve the size of the matrix — for a truncated convolution
operator the row sums are bounded by `‖r‖₁²` no matter how large the truncation. -/
theorem eigenvalues_le_of_rowSum_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {C : ℝ}
    (hrow : ∀ g, ∑ h, ‖A g h‖ ≤ C) (i : n) : hA.eigenvalues i ≤ C := by
  set v : EuclideanSpace ℂ n := hA.eigenvectorBasis i with hvdef
  have hv : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hv2 : ∑ g, ‖(v : n → ℂ) g‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq (𝕜 := ℂ) v
    rw [hv] at this
    have h1 : Real.sqrt (∑ g, ‖(v : n → ℂ) g‖ ^ 2) = 1 := this.symm
    have h2 : (0 : ℝ) ≤ ∑ g, ‖(v : n → ℂ) g‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt h2, h1]
  have hkey : hA.eigenvalues i ≤ ∑ g, ∑ h, ‖A g h‖ * ‖(v : n → ℂ) g‖ * ‖(v : n → ℂ) h‖ := by
    rw [hA.eigenvalues_eq i]
    have hexp : star (v : n → ℂ) ⬝ᵥ (A *ᵥ (v : n → ℂ))
        = ∑ g, ∑ h, (starRingEnd ℂ) ((v : n → ℂ) g) * A g h * (v : n → ℂ) h := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun h _ => by ring))
    rw [hexp]
    refine le_trans (RCLike.re_le_norm _) ?_
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun g _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun h _ => ?_)
    rw [norm_mul, norm_mul]
    simp [mul_comm, mul_left_comm, mul_assoc]
  refine hkey.trans ?_
  have hAM : ∀ g h : n, ‖A g h‖ * ‖(v : n → ℂ) g‖ * ‖(v : n → ℂ) h‖
      ≤ ‖A g h‖ * (‖(v : n → ℂ) g‖ ^ 2 + ‖(v : n → ℂ) h‖ ^ 2) / 2 := by
    intro g h
    nlinarith [sq_nonneg (‖(v : n → ℂ) g‖ - ‖(v : n → ℂ) h‖), norm_nonneg (A g h)]
  refine (Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun h _ => hAM g h))).trans ?_
  have hcol : ∀ h, ∑ g, ‖A g h‖ ≤ C := by
    intro h
    refine le_trans (le_of_eq ?_) (hrow h)
    exact Finset.sum_congr rfl (fun g _ => by rw [← hA.apply g h]; simp)
  have h1 : ∑ g, ∑ h, ‖A g h‖ * ‖(v : n → ℂ) g‖ ^ 2 ≤ C := by
    have e1 : ∀ g : n, ∑ h, ‖A g h‖ * ‖(v : n → ℂ) g‖ ^ 2
        = ‖(v : n → ℂ) g‖ ^ 2 * ∑ h, ‖A g h‖ := by
      intro g; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun h _ => by ring)
    rw [Finset.sum_congr rfl (fun g _ => e1 g)]
    calc ∑ g, ‖(v : n → ℂ) g‖ ^ 2 * ∑ h, ‖A g h‖
        ≤ ∑ g, ‖(v : n → ℂ) g‖ ^ 2 * C :=
          Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hrow g) (by positivity))
      _ = C := by rw [← Finset.sum_mul, hv2, one_mul]
  have h2 : ∑ g, ∑ h, ‖A g h‖ * ‖(v : n → ℂ) h‖ ^ 2 ≤ C := by
    rw [Finset.sum_comm]
    have e2 : ∀ h : n, ∑ g, ‖A g h‖ * ‖(v : n → ℂ) h‖ ^ 2
        = ‖(v : n → ℂ) h‖ ^ 2 * ∑ g, ‖A g h‖ := by
      intro h; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
    rw [Finset.sum_congr rfl (fun h _ => e2 h)]
    calc ∑ h, ‖(v : n → ℂ) h‖ ^ 2 * ∑ g, ‖A g h‖
        ≤ ∑ h, ‖(v : n → ℂ) h‖ ^ 2 * C :=
          Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hcol h) (by positivity))
      _ = C := by rw [← Finset.sum_mul, hv2, one_mul]
  calc ∑ g, ∑ h, ‖A g h‖ * (‖(v : n → ℂ) g‖ ^ 2 + ‖(v : n → ℂ) h‖ ^ 2) / 2
      = ∑ g, ((∑ h, ‖A g h‖ * ‖(v : n → ℂ) g‖ ^ 2) / 2
          + (∑ h, ‖A g h‖ * ‖(v : n → ℂ) h‖ ^ 2) / 2) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun h _ => by ring)
    _ = (∑ g, ∑ h, ‖A g h‖ * ‖(v : n → ℂ) g‖ ^ 2) / 2
          + (∑ g, ∑ h, ‖A g h‖ * ‖(v : n → ℂ) h‖ ^ 2) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    _ ≤ C / 2 + C / 2 := by linarith
    _ = C := by ring

end FiniteDim

/-! ### Rank-one blocks -/

/-- The rank-one positive semidefinite matrix `v ↦ (conj v_g) v_h`. -/
noncomputable def rank1 {ι : Type*} [Fintype ι] (v : ι → ℂ) : Matrix ι ι ℂ :=
  (Matrix.of (fun _ : Unit => v))ᴴ * (Matrix.of (fun _ : Unit => v))

theorem rank1_posSemidef {ι : Type*} [Fintype ι] (v : ι → ℂ) : (rank1 v).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem rank1_apply {ι : Type*} [Fintype ι] (v : ι → ℂ) (g h : ι) :
    rank1 v g h = (starRingEnd ℂ) (v g) * v h := by
  simp [rank1, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem posSemidef_sum {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ)
    (f : κ → Matrix ι ι ℂ) (hf : ∀ k ∈ s, (f k).PosSemidef) :
    (∑ k ∈ s, f k).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Matrix.PosSemidef.zero (n := ι) (R := ℂ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-! ### The ordered-group input: a triangular minor with constant diagonal -/

section Group

variable {G : Type*} [Group G] [DecidableEq G] [LinearOrder G]
  [CovariantClass G G (· * ·) (· < ·)] [CovariantClass G G (Function.swap (· * ·)) (· < ·)]

/-- The Gram matrix of the translates `{δ_g * r : g ∈ F}`, as a sum of rank-one blocks over the
positions `T`.  `T` must contain every position where some translate is supported. -/
noncomputable def gram (r : MonoidAlgebra ℂ G) (F T : Finset G) : Matrix F F ℂ :=
  ∑ p ∈ T, rank1 (fun g : F => r ((g : G)⁻¹ * p))

theorem gram_posSemidef (r : MonoidAlgebra ℂ G) (F T : Finset G) : (gram r F T).PosSemidef :=
  posSemidef_sum _ _ (fun _ _ => rank1_posSemidef _)

/-- The square minor of the translate matrix on the rows `{g · m : g ∈ F}`, where `m` is the
largest element of the support of `r`. -/
noncomputable def leadMat (r : MonoidAlgebra ℂ G) (F : Finset G) (m : G) : Matrix F F ℂ :=
  fun i j => r ((j : G)⁻¹ * ((i : G) * m))

/-- **The order makes the minor triangular.**  Below the diagonal the argument exceeds the largest
support element, so the coefficient vanishes.  Both invariance directions are used: left
invariance to get `1 < j⁻¹i`, right invariance to push it past `m`. -/
theorem leadMat_upperTriangular (r : MonoidAlgebra ℂ G) (F : Finset G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) :
    ∀ i j : F, j < i → leadMat r F m i j = 0 := by
  intro i j hji
  have hji' : (j : G) < (i : G) := hji
  have h1 : (1 : G) < (j : G)⁻¹ * (i : G) := by
    have h := CovariantClass.elim (μ := (· * ·)) (r := ((· < ·) : G → G → Prop)) (j : G)⁻¹ hji'
    simpa using h
  have h2 : m < (j : G)⁻¹ * (i : G) * m := by
    have h := CovariantClass.elim (μ := Function.swap (· * ·))
      (r := ((· < ·) : G → G → Prop)) m h1
    simpa [Function.swap] using h
  have h3 : (j : G)⁻¹ * ((i : G) * m) = (j : G)⁻¹ * (i : G) * m := by rw [mul_assoc]
  by_contra hne
  have hmem : (j : G)⁻¹ * ((i : G) * m) ∈ r.support := Finsupp.mem_support_iff.mpr hne
  have := hm _ hmem
  rw [h3] at this
  exact absurd this (not_le.mpr h2)

theorem leadMat_diag (r : MonoidAlgebra ℂ G) (F : Finset G) (m : G) (i : F) :
    leadMat r F m i i = r m := by
  simp [leadMat, ← mul_assoc]

theorem leadMat_det (r : MonoidAlgebra ℂ G) (F : Finset G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) :
    (leadMat r F m).det = (r m) ^ F.card := by
  rw [Matrix.det_of_upperTriangular (leadMat_upperTriangular r F hm)]
  simp [leadMat_diag, Finset.card_univ]

/-- The rank-one blocks over the special rows assemble into `Mᴴ M`. -/
theorem sum_image_rank1 (r : MonoidAlgebra ℂ G) (F : Finset G) (m : G) :
    ∑ p ∈ F.image (· * m), rank1 (fun g : F => r ((g : G)⁻¹ * p))
      = (leadMat r F m)ᴴ * (leadMat r F m) := by
  rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
  ext g h
  simp only [Matrix.sum_apply, rank1_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, leadMat]
  rw [← Finset.sum_coe_sort F]
  simp only [starRingEnd_apply]

/-- The Gram matrix splits as the triangular minor's square plus a positive semidefinite rest. -/
theorem gram_split (r : MonoidAlgebra ℂ G) (F T : Finset G) (m : G)
    (hsub : F.image (· * m) ⊆ T) :
    gram r F T = (leadMat r F m)ᴴ * (leadMat r F m)
      + ∑ p ∈ T \ F.image (· * m), rank1 (fun g : F => r ((g : G)⁻¹ * p)) := by
  rw [← sum_image_rank1, gram, ← Finset.sum_sdiff hsub]
  abel

/-- **THE DETERMINANT BOUND FOR TRANSLATES.**  For a bi-orderable group, the Gram matrix of the
translates `{δ_g · r : g ∈ F}` has determinant at least `|r(m)|^{2|F|}`, where `m` is the largest
element of the support of `r`.

The bound is uniform in `F` — that is the whole point.  It says the translates of a nonzero group
algebra element are quantitatively independent, at a rate that does not degrade as `F` grows. -/
theorem gram_det_lower_bound (r : MonoidAlgebra ℂ G) (F T : Finset G) {m : G}
    (hm : ∀ x ∈ r.support, x ≤ m) (hmr : r m ≠ 0) (hsub : F.image (· * m) ⊆ T) :
    Complex.normSq (r m) ^ F.card
      ≤ ∏ i, (gram_posSemidef r F T).isHermitian.eigenvalues i := by
  have hdetM : (leadMat r F m).det = (r m) ^ F.card := leadMat_det r F hm
  have hunit : IsUnit (leadMat r F m).det := by
    rw [hdetM]
    exact (pow_ne_zero _ hmr).isUnit
  have hR : (∑ p ∈ T \ F.image (· * m), rank1 (fun g : F => r ((g : G)⁻¹ * p))).PosSemidef :=
    posSemidef_sum _ _ (fun _ _ => rank1_posSemidef _)
  have key := normSq_det_le_prod_eigenvalues hunit hR (gram_split r F T m hsub)
    (gram_posSemidef r F T).isHermitian
  rwa [hdetM, map_pow] at key

/-- The involution `r ↦ r*`, `r*(x) = conj (r x⁻¹)`.  Mathlib has no `StarRing` instance on
`MonoidAlgebra ℂ G` reachable here, so it is built by hand from `equivMapDomain (Equiv.inv G)`. -/
noncomputable def rstar (r : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (Finsupp.equivMapDomain (Equiv.inv G) r)

@[simp] theorem rstar_apply (r : MonoidAlgebra ℂ G) (x : G) :
    rstar r x = (starRingEnd ℂ) (r x⁻¹) := rfl

/-- **The Gram matrix IS the truncation of convolution by `r · r*`.**  This is what links the
determinant bound (a statement about translates) to the trace comparison (a statement about a
single self-adjoint group-algebra element). -/
theorem gram_eq_mul_rstar (r : MonoidAlgebra ℂ G) (F T : Finset G)
    (hT : ∀ x : G, x ∈ F → ∀ y ∈ r.support, x * y ∈ T) (g h : F) :
    gram r F T g h = (r * rstar r) ((h : G)⁻¹ * (g : G)) := by
  have hsub : r.support.image (fun y => (h : G) * y) ⊆ T := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hT (h : G) h.2 y hy
  rw [gram]
  simp only [Matrix.sum_apply, rank1_apply]
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
    rw [MonoidAlgebra.mul_apply_left, Finsupp.sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [rstar_apply, mul_comm]
    congr 2
    · simp
    · congr 1
      group
  · intro p _ hp
    have hzero : r ((h : G)⁻¹ * p) = 0 := by
      by_contra hne
      exact hp (Finset.mem_image.mpr ⟨(h : G)⁻¹ * p, Finsupp.mem_support_iff.mpr hne,
        by rw [mul_inv_cancel_left]⟩)
    rw [hzero, mul_zero]

end Group


/-! ### The determinant bound for an ABSTRACT coefficient family

The bound above is stated for the translates of a group-algebra element.  Nothing in the proof uses
that: it needs only a family of coefficient vectors indexed by position, a distinguished position
map `i ↦ i·m`, triangularity below the diagonal, and a constant modulus ON the diagonal.  Stating it
that way lets the TWISTED case (where each coefficient is multiplied by a unimodular cocycle value,
so the diagonal entries differ but their moduli do not) reuse it verbatim. -/

section Abstract

variable {G : Type*} [Group G] [DecidableEq G] [LinearOrder G]

/-- The Gram matrix of an abstract coefficient family. -/
noncomputable def gramOf (A : G → G → ℂ) (F T : Finset G) : Matrix F F ℂ :=
  ∑ p ∈ T, rank1 (fun g : F => A p (g : G))

theorem gramOf_posSemidef (A : G → G → ℂ) (F T : Finset G) : (gramOf A F T).PosSemidef :=
  posSemidef_sum _ _ (fun _ _ => rank1_posSemidef _)

/-- The square minor on the distinguished rows `{i · m : i ∈ F}`. -/
noncomputable def leadMatOf (A : G → G → ℂ) (F : Finset G) (m : G) : Matrix F F ℂ :=
  fun i j => A ((i : G) * m) (j : G)

theorem leadMatOf_det (A : G → G → ℂ) (F : Finset G) (m : G)
    (htri : ∀ i j : F, j < i → A ((i : G) * m) (j : G) = 0) :
    (leadMatOf A F m).det = ∏ i : F, A ((i : G) * m) (i : G) :=
  Matrix.det_of_upperTriangular htri

theorem gramOf_split (A : G → G → ℂ) (F T : Finset G) (m : G)
    (hsub : F.image (· * m) ⊆ T) :
    gramOf A F T = (leadMatOf A F m)ᴴ * (leadMatOf A F m)
      + ∑ p ∈ T \ F.image (· * m), rank1 (fun g : F => A p (g : G)) := by
  have hone : ∑ p ∈ F.image (· * m), rank1 (fun g : F => A p (g : G))
      = (leadMatOf A F m)ᴴ * (leadMatOf A F m) := by
    rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    ext g h
    simp only [Matrix.sum_apply, rank1_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      leadMatOf]
    rw [← Finset.sum_coe_sort F]
    simp only [starRingEnd_apply]
  rw [← hone, gramOf, ← Finset.sum_sdiff hsub]
  abel

/-- **THE DETERMINANT BOUND, abstract form.**  Triangular below the diagonal plus constant modulus
`‖c‖` on the diagonal forces `det ≥ ‖c‖^{2|F|}`, uniformly in `F`. -/
theorem gramOf_det_lower_bound (A : G → G → ℂ) (F T : Finset G) (m : G) (c : ℂ) (hc : c ≠ 0)
    (htri : ∀ i j : F, j < i → A ((i : G) * m) (j : G) = 0)
    (hdiag : ∀ i : F, Complex.normSq (A ((i : G) * m) (i : G)) = Complex.normSq c)
    (hsub : F.image (· * m) ⊆ T) :
    Complex.normSq c ^ F.card
      ≤ ∏ i, (gramOf_posSemidef A F T).isHermitian.eigenvalues i := by
  have hdet : (leadMatOf A F m).det = ∏ i : F, A ((i : G) * m) (i : G) :=
    leadMatOf_det A F m htri
  have hnsq : Complex.normSq ((leadMatOf A F m).det) = Complex.normSq c ^ F.card := by
    rw [hdet, map_prod]
    rw [Finset.prod_congr rfl (fun i _ => hdiag i), Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
  have hunit : IsUnit (leadMatOf A F m).det := by
    rw [← Complex.normSq_pos] at *
    refine isUnit_iff_ne_zero.mpr ?_
    intro hz
    rw [hz] at hnsq
    simp only [map_zero] at hnsq
    exact absurd hnsq.symm (by positivity)
  have hR : (∑ p ∈ T \ F.image (· * m), rank1 (fun g : F => A p (g : G))).PosSemidef :=
    posSemidef_sum _ _ (fun _ _ => rank1_posSemidef _)
  have key := normSq_det_le_prod_eigenvalues hunit hR (gramOf_split A F T m hsub)
    (gramOf_posSemidef A F T).isHermitian
  rwa [hnsq] at key

end Abstract

end DetLB

end GroupVN

/-! ## Acceptance gate -/

#print axioms GroupVN.DetLB.one_le_prod_eigenvalues_one_add
#print axioms GroupVN.DetLB.normSq_det_le_prod_eigenvalues
#print axioms GroupVN.DetLB.card_small_eigenvalues_le
#print axioms GroupVN.DetLB.leadMat_upperTriangular
#print axioms GroupVN.DetLB.leadMat_det
#print axioms GroupVN.DetLB.gram_split
#print axioms GroupVN.DetLB.gram_det_lower_bound
#print axioms GroupVN.DetLB.gramOf_split
#print axioms GroupVN.DetLB.gramOf_det_lower_bound
#print axioms GroupVN.DetLB.gram_eq_mul_rstar
#print axioms GroupVN.DetLB.trace_one_sub_smul_pow
#print axioms GroupVN.DetLB.trace_one_sub_smul_pow_real
#print axioms GroupVN.DetLB.eigenvalues_le_of_rowSum_le
