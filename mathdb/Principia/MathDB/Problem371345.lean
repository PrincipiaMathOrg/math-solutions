import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity


set_option maxHeartbeats 1000000

/-!
# MathDB #371345 — the Vendi–LCR comparison at nonpositive order (PARTIAL)

Write-up `mathdb-open-problems/problems/371345/solution.tex`,
*The Vendi–LCR inequality at every order*, 18 September 2026.
Source: Nathan, as recorded by MathDB 371345.

For `Z` real symmetric positive semidefinite with `z_ii = 1` and `0 ≤ z_ij ≤ 1`, with
`r_i = ∑_j z_ij`, `s_i = ∑_j z_ij²`, and `λ_1,…,λ_r > 0` the POSITIVE eigenvalues, the
source's Theorem asserts `VS_q(Z) ≥ D_q(Z)` for every `q ∈ [−∞,+∞]`, and more precisely
that for finite `q ≤ 0`

`∑_ℓ λ_ℓ^q ≥ ∑_i h_i^{1−q} ≥ ∑_i s_i^{q−1} ≥ ∑_i r_i^{q−1}`.

## What is proved here, and what is not

The write-up is explicit that the source ALREADY proves every nonnegative order, and negative
orders for invertible `Z`; its own contribution is **the singular case at negative order**.
That contribution is proved here in full:

* `main_chain` — all three links of the displayed chain, for every finite `q ≤ 0`;
* `vendi_ge_lcr` — `D_q(Z) ≤ VS_q(Z)` for every finite `q ≤ 0`, singular `Z` included.

**NOT proved, and the reason the row is not counted:** the positive orders and the invertible
negative orders (the source's own prior work — its proof runs through operator monotonicity of
`A ↦ A^α` via the integral representation `x^α = (sin πα/π)∫ t^{α−1}x/(x+t)dt`, i.e. Loewner
theory, absent from Mathlib), the limiting cases `q = 1` and `q = ±∞`, and the equality
characterisation. So the module proves a PROPER PART of the source's theorem — unconditionally,
with no hypotheses carried — in the sense of `#347788`.

## The route, and why it needs no projection

The write-up obtains `h_i s_i ≥ 1` from `1 = ⟨P e_i, Z e_i⟩ ≤ ‖P e_i‖·‖Z e_i‖`, where `P` is
the orthogonal projection onto `ran Z` and `h_i = P_ii`.  That needs `P` and `ran Z` as
objects.  Working directly with the eigenbasis weights `w_{iℓ} = (U_{iℓ})²` avoids both:

* `entry_eq` — `Z_{ij} = ∑_ℓ λ_ℓ U_{iℓ} U_{jℓ}`, unfolded out of Mathlib's
  `conjStarAlgAut`-packaged `spectral_theorem`;
* `diag_one` — `∑_ℓ λ_ℓ w_{iℓ} = Z_{ii} = 1`, and `sq_diag` — `∑_ℓ λ_ℓ² w_{iℓ} = s_i`, the
  latter by column orthonormality (`sum_col`);
* `one_le_hh_mul_ss` — Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) on `√w` and `λ√w`
  gives `1 = (∑ λ w)² ≤ (∑ w)(∑ λ² w) = h_i s_i`.

`hh` is therefore a DEFINITION — the weight the positive spectrum carries at `i` — rather than
a matrix entry to be identified.  **215 note:** the source defines `h_i` as `P_ii`; the two
agree by the standard description of a spectral projection, but that identification is NOT
formalised here.  It does not affect the headline results, since neither `vendi_ge` nor
`vendi_ge_lcr` mentions `hh` — it appears only in the chain's middle terms.

## A lemma Mathlib does not have

`convexOn_rpow_nonpos` — `ConvexOn ℝ (Ioi 0) (x ↦ x^q)` for real `q ≤ 0`.  Mathlib's
`convexOn_rpow` covers only `1 ≤ p`.  Proved from `convexOn_of_deriv2_nonneg'` and
`Real.hasDerivAt_rpow_const`, the second derivative `q(q−1)x^{q−2}` being nonnegative because
both factors are nonpositive.  It mentions nothing of this problem and is a `Common/`
promotion candidate.  Taking `q : ℤ` instead would have made `convexOn_zpow` free, but the
source says "every finite `q ≤ 0`" with `q` REAL, so that would have been a silent
restriction.

## 215 check

* `Adm` carries exactly the source's hypotheses: symmetric (`IsHermitian` over `ℝ`), positive
  semidefinite, `z_ii = 1`, `0 ≤ z_ij`, `z_ij ≤ 1`.  None is dropped or weakened.
* `pos` omits the zero eigenvalues, matching the source's stated convention ("zero eigenvalues
  are omitted, including at nonpositive orders").
* `q` is REAL and the hypothesis is exactly `q ≤ 0`, as stated.
* `VS` and `Dq` are the source's displayed definitions, including the `n^{-q}` factor and the
  `1/(1-q)` exponent.
-/

namespace Principia.MathDB.P371345

open Finset Matrix

variable {n : ℕ}

/-! ### The source's setting

`Z` is real symmetric positive semidefinite with unit diagonal and entries in `[0,1]`.
`r_i = ∑_j z_ij`, `s_i = ∑_j z_ij²`.  The write-up's new case is `q ≤ 0` with `Z` singular. -/

/-- The admissible matrices of the source. -/
structure Adm (Z : Matrix (Fin n) (Fin n) ℝ) : Prop where
  herm : Z.IsHermitian
  psd : Z.PosSemidef
  diag : ∀ i, Z i i = 1
  nonneg : ∀ i j, 0 ≤ Z i j
  le_one : ∀ i j, Z i j ≤ 1

noncomputable def rr (Z : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, Z i j

noncomputable def ss (Z : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, (Z i j) ^ 2

/-- The eigenvector matrix, as a plain matrix. -/
noncomputable def U {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) :
    Matrix (Fin n) (Fin n) ℝ := hZ.eigenvectorUnitary

/-- `w i ℓ` is the squared `(i,ℓ)` entry of the eigenvector matrix: the Jensen weight. -/
noncomputable def w {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (i l : Fin n) : ℝ :=
  (U hZ i l) ^ 2

theorem w_nonneg {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (i l : Fin n) :
    0 ≤ w hZ i l := sq_nonneg _

/-- The eigenvector matrix is orthogonal. -/
theorem U_mul_star {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) :
    (U hZ) * (star (U hZ)) = 1 :=
  Unitary.coe_mul_star_self hZ.eigenvectorUnitary

/-- **Each row of the eigenvector matrix is a unit vector**: the weights sum to one. -/
theorem sum_w_row {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (i : Fin n) :
    ∑ l, w hZ i l = 1 := by
  have h := congrFun (congrFun (U_mul_star hZ) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [w, Matrix.star_apply, sq]

/-- **The entrywise spectral decomposition** of a real symmetric matrix. -/
theorem entry_eq {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (i j : Fin n) :
    Z i j = ∑ l, hZ.eigenvalues l * (U hZ i l * U hZ j l) := by
  conv_lhs => rw [hZ.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.star_apply,
    Matrix.diagonal_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_to_real,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, U,
    RCLike.ofReal_real_eq_id, id_eq]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Column orthonormality of the eigenvector matrix. -/
theorem star_U_mul {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) :
    (star (U hZ)) * (U hZ) = 1 :=
  Unitary.coe_star_mul_self hZ.eigenvectorUnitary

theorem sum_col {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (l m : Fin n) :
    ∑ j, U hZ j l * U hZ j m = if l = m then (1 : ℝ) else 0 := by
  have h := congrFun (congrFun (star_U_mul hZ) l) m
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.star_apply, U]

/-- **The unit diagonal, spectrally**: the weights average the eigenvalues to one. -/
theorem diag_one {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (i : Fin n) : ∑ l, hZ.eigenvalues l * w hZ i l = 1 := by
  have h := entry_eq hZ i i
  rw [hA.diag i] at h
  have e : ∑ l, hZ.eigenvalues l * w hZ i l
      = ∑ l, hZ.eigenvalues l * (U hZ i l * U hZ i l) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [w, sq]
  rw [e, ← h]

/-- **The squared row sum, spectrally.** -/
theorem sq_diag {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian)
    (i : Fin n) : ∑ l, (hZ.eigenvalues l) ^ 2 * w hZ i l = ss Z i := by
  have hsym : ∀ a b : Fin n, Z b a = Z a b := fun a b => by
    have h1 := hZ.apply a b
    simpa using h1
  have hZZ : ∑ j, Z i j * Z j i = ∑ l, (hZ.eigenvalues l) ^ 2 * w hZ i l := by
    have hexp : ∀ j, Z i j * Z j i
        = ∑ l, ∑ m, (hZ.eigenvalues l * hZ.eigenvalues m)
            * ((U hZ i l * U hZ i m) * (U hZ j l * U hZ j m)) := by
      intro j
      rw [entry_eq hZ i j, entry_eq hZ j i, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    have key : ∀ m, ∑ j, (hZ.eigenvalues l * hZ.eigenvalues m)
        * ((U hZ i l * U hZ i m) * (U hZ j l * U hZ j m))
        = (hZ.eigenvalues l * hZ.eigenvalues m) * (U hZ i l * U hZ i m)
            * (if l = m then (1 : ℝ) else 0) := by
      intro m
      rw [← sum_col hZ l m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun m _ => key m)]
    rw [Finset.sum_eq_single l]
    · simp [w, sq]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hcon
      exact absurd (Finset.mem_univ l) hcon
  rw [← hZZ, ss]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j, sq]


/-! ### Restricting to the positive spectrum, and Cauchy-Schwarz -/

/-- The indices of the strictly positive eigenvalues: the source omits the zero ones. -/
noncomputable def pos {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) :
    Finset (Fin n) := univ.filter (fun l => 0 < hZ.eigenvalues l)

/-- `h i` is the source's `P_ii`, the `i`-th diagonal entry of the projection onto `ran Z`,
here defined directly as the weight the positive spectrum carries. -/
noncomputable def hh {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (i : Fin n) : ℝ :=
  ∑ l ∈ pos hZ, w hZ i l

/-- Dropping the zero eigenvalues changes nothing that vanishes there. -/
theorem sum_pos_drop {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian)
    (hP : Z.PosSemidef) (g : Fin n → ℝ) (hg : ∀ l, hZ.eigenvalues l = 0 → g l = 0) :
    ∑ l ∈ pos hZ, g l = ∑ l, g l := by
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro l _ hl
  have hnn : 0 ≤ hZ.eigenvalues l := by
    have := hP.eigenvalues_nonneg l
    simpa using this
  have hz : hZ.eigenvalues l = 0 := by
    by_contra hne
    exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, lt_of_le_of_ne hnn (Ne.symm hne)⟩)
  exact hg l hz

/-- **Cauchy-Schwarz on the weights**: `h_i * s_i ≥ 1`, with no projection in sight. -/
theorem one_le_hh_mul_ss {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) (i : Fin n) : 1 ≤ hh hZ i * ss Z i := by
  have hw : ∀ l, 0 ≤ w hZ i l := fun l => w_nonneg hZ i l
  have hone : ∑ l ∈ pos hZ, hZ.eigenvalues l * w hZ i l = 1 := by
    rw [sum_pos_drop hZ hP _ (fun l hl => by rw [hl, zero_mul])]
    exact diag_one hZ hA i
  have hsq : ∑ l ∈ pos hZ, (hZ.eigenvalues l) ^ 2 * w hZ i l = ss Z i := by
    rw [sum_pos_drop hZ hP _ (fun l hl => by rw [hl]; ring)]
    exact sq_diag hZ i
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (pos hZ)
    (fun l => Real.sqrt (w hZ i l))
    (fun l => hZ.eigenvalues l * Real.sqrt (w hZ i l))
  have e1 : ∑ l ∈ pos hZ, Real.sqrt (w hZ i l) * (hZ.eigenvalues l * Real.sqrt (w hZ i l))
      = ∑ l ∈ pos hZ, hZ.eigenvalues l * w hZ i l := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show Real.sqrt (w hZ i l) * (hZ.eigenvalues l * Real.sqrt (w hZ i l))
        = hZ.eigenvalues l * (Real.sqrt (w hZ i l) * Real.sqrt (w hZ i l)) from by ring,
      Real.mul_self_sqrt (hw l)]
  have e2 : ∑ l ∈ pos hZ, (Real.sqrt (w hZ i l)) ^ 2 = hh hZ i := by
    rw [hh]
    refine Finset.sum_congr rfl fun l _ => Real.sq_sqrt (hw l)
  have e3 : ∑ l ∈ pos hZ, (hZ.eigenvalues l * Real.sqrt (w hZ i l)) ^ 2 = ss Z i := by
    rw [← hsq]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw l)]
  rw [e1, e2, e3, hone] at hcs
  simpa using hcs


/-! ### Convexity of `x ↦ x^q` for `q ≤ 0`, which Mathlib does not have

Mathlib has `convexOn_rpow` only for `1 ≤ p`.  For the source's range `q ≤ 0` the second
derivative `q(q-1)x^{q-2}` is nonnegative on `(0,∞)` because both factors are nonpositive. -/

theorem convexOn_rpow_nonpos {q : ℝ} (hq : q ≤ 0) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => x ^ q) := by
  have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y ^ q) (q * x ^ (q - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have hd2 : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => q * y ^ (q - 1)) (q * ((q - 1) * x ^ (q - 1 - 1))) x :=
    fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).const_mul q
  have hEq : Set.EqOn (deriv (fun x : ℝ => x ^ q)) (fun x => q * x ^ (q - 1))
      (Set.Ioi 0) := fun x hx => (hd x hx).deriv
  have hone : DifferentiableOn ℝ (fun x : ℝ => x ^ q) (Set.Ioi 0) :=
    fun x hx => ((hd x hx).differentiableAt).differentiableWithinAt
  have htwo : DifferentiableOn ℝ (deriv (fun x : ℝ => x ^ q)) (Set.Ioi 0) := by
    have hbase : DifferentiableOn ℝ (fun x : ℝ => q * x ^ (q - 1)) (Set.Ioi 0) :=
      fun x hx => ((hd2 x hx).differentiableAt).differentiableWithinAt
    exact hbase.congr (fun x hx => hEq hx)
  refine convexOn_of_deriv2_nonneg' (convex_Ioi 0) hone htwo ?_
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hfe : deriv (fun x : ℝ => x ^ q) =ᶠ[nhds x] (fun y : ℝ => q * y ^ (q - 1)) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx) hEq
  have : (deriv^[2] (fun x : ℝ => x ^ q)) x = q * ((q - 1) * x ^ (q - 1 - 1)) := by
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
    rw [hfe.deriv_eq]
    exact (hd2 x hx).deriv
  rw [this]
  have h1 : 0 ≤ q * (q - 1) := by nlinarith
  have h2 : (0 : ℝ) < x ^ (q - 1 - 1) := Real.rpow_pos_of_pos hx0 _
  calc (0 : ℝ) ≤ (q * (q - 1)) * x ^ (q - 1 - 1) := mul_nonneg h1 (le_of_lt h2)
    _ = q * ((q - 1) * x ^ (q - 1 - 1)) := by ring


/-! ### The Jensen step -/

theorem ss_nonneg {Z : Matrix (Fin n) (Fin n) ℝ} (i : Fin n) : 0 ≤ ss Z i :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

theorem hh_pos {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) (i : Fin n) : 0 < hh hZ i := by
  have h1 := one_le_hh_mul_ss hZ hA hP i
  by_contra hcon
  push_neg at hcon
  have : hh hZ i * ss Z i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (ss_nonneg i)
  linarith

/-- **Jensen against `x ↦ x^q`**, the write-up's first inequality in the chain. -/
theorem jensen_step {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) (i : Fin n) {q : ℝ} (hq : q ≤ 0) :
    (hh hZ i) ^ (1 - q) ≤ ∑ l ∈ pos hZ, w hZ i l * (hZ.eigenvalues l) ^ q := by
  have hpos := hh_pos hZ hA hP i
  have hw : ∀ l ∈ pos hZ, 0 ≤ w hZ i l / hh hZ i :=
    fun l _ => div_nonneg (w_nonneg hZ i l) (le_of_lt hpos)
  have hsum1 : ∑ l ∈ pos hZ, w hZ i l / hh hZ i = 1 := by
    rw [← Finset.sum_div, hh]
    exact div_self (ne_of_gt hpos)
  have hmem : ∀ l ∈ pos hZ, hZ.eigenvalues l ∈ Set.Ioi (0 : ℝ) :=
    fun l hl => (Finset.mem_filter.mp hl).2
  have hJ := (convexOn_rpow_nonpos hq).map_sum_le hw hsum1 hmem
  -- the barycentre is 1 / h_i
  have hone : ∑ l ∈ pos hZ, hZ.eigenvalues l * w hZ i l = 1 := by
    rw [sum_pos_drop hZ hP _ (fun l hl => by rw [hl, zero_mul])]
    exact diag_one hZ hA i
  have hbar : ∑ l ∈ pos hZ, (w hZ i l / hh hZ i) • hZ.eigenvalues l = (hh hZ i)⁻¹ := by
    have : ∀ l ∈ pos hZ, (w hZ i l / hh hZ i) • hZ.eigenvalues l
        = (hh hZ i)⁻¹ * (hZ.eigenvalues l * w hZ i l) := by
      intro l _
      simp only [smul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hone, mul_one]
  rw [hbar] at hJ
  -- rewrite the right-hand side and clear the 1/h_i
  have hrhs : ∑ l ∈ pos hZ, (w hZ i l / hh hZ i) • (hZ.eigenvalues l) ^ q
      = (hh hZ i)⁻¹ * ∑ l ∈ pos hZ, w hZ i l * (hZ.eigenvalues l) ^ q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [smul_eq_mul]
    field_simp
  rw [hrhs] at hJ
  have hinv : ((hh hZ i)⁻¹) ^ q = ((hh hZ i) ^ q)⁻¹ :=
    Real.inv_rpow (le_of_lt hpos) q
  rw [hinv] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt hpos)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hmul
  have hsplit : (hh hZ i) ^ (1 - q) = hh hZ i * ((hh hZ i) ^ q)⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt hpos) q, sub_eq_add_neg, Real.rpow_add hpos,
      Real.rpow_one]
  rw [hsplit]
  exact hmul


/-! ### The remaining two links, and the chain -/

/-- `s_i ≤ r_i`, because `0 ≤ z_ij ≤ 1` forces `z² ≤ z`. -/
theorem ss_le_rr {Z : Matrix (Fin n) (Fin n) ℝ} (hA : Adm Z) (i : Fin n) :
    ss Z i ≤ rr Z i := by
  rw [ss, rr]
  refine Finset.sum_le_sum fun j _ => ?_
  have h0 := hA.nonneg i j
  have h1 := hA.le_one i j
  nlinarith

/-- `1 ≤ s_i`, from the unit diagonal. -/
theorem one_le_ss {Z : Matrix (Fin n) (Fin n) ℝ} (hA : Adm Z) (i : Fin n) :
    1 ≤ ss Z i := by
  have hle : (Z i i) ^ 2 ≤ ∑ j, (Z i j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (Z i j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  rw [hA.diag i] at hle
  simpa [ss] using hle

/-- **Chain link 1**: summing Jensen over `i`, using column orthonormality. -/
theorem chain_one {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) {q : ℝ} (hq : q ≤ 0) :
    ∑ i, (hh hZ i) ^ (1 - q) ≤ ∑ l ∈ pos hZ, (hZ.eigenvalues l) ^ q := by
  calc ∑ i, (hh hZ i) ^ (1 - q)
      ≤ ∑ i, ∑ l ∈ pos hZ, w hZ i l * (hZ.eigenvalues l) ^ q :=
        Finset.sum_le_sum fun i _ => jensen_step hZ hA hP i hq
    _ = ∑ l ∈ pos hZ, ∑ i, w hZ i l * (hZ.eigenvalues l) ^ q := Finset.sum_comm
    _ = ∑ l ∈ pos hZ, (hZ.eigenvalues l) ^ q := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_mul]
        have hcol : ∑ i, w hZ i l = 1 := by
          have h := sum_col hZ l l
          simpa [w, sq] using h
        rw [hcol, one_mul]

/-- **Chain link 2**: `h_i ≥ 1/s_i` raised to the positive power `1 - q`. -/
theorem chain_two {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) {q : ℝ} (hq : q ≤ 0) (i : Fin n) :
    (ss Z i) ^ (q - 1) ≤ (hh hZ i) ^ (1 - q) := by
  have hs1 := one_le_ss hA i
  have hs0 : (0 : ℝ) < ss Z i := by linarith
  have hcs := one_le_hh_mul_ss hZ hA hP i
  have hinv : (ss Z i)⁻¹ ≤ hh hZ i := by
    rw [inv_le_iff_one_le_mul₀ hs0]
    linarith [hcs]
  have hmono : ((ss Z i)⁻¹) ^ (1 - q) ≤ (hh hZ i) ^ (1 - q) :=
    Real.rpow_le_rpow (le_of_lt (inv_pos.mpr hs0)) hinv (by linarith)
  have heq : ((ss Z i)⁻¹) ^ (1 - q) = (ss Z i) ^ (q - 1) := by
    rw [Real.inv_rpow (le_of_lt hs0), ← Real.rpow_neg (le_of_lt hs0)]
    ring_nf
  rwa [heq] at hmono

/-- **Chain link 3**: `s_i ≤ r_i` raised to the negative power `q - 1`. -/
theorem chain_three {Z : Matrix (Fin n) (Fin n) ℝ} (hA : Adm Z) {q : ℝ} (hq : q ≤ 0)
    (i : Fin n) : (rr Z i) ^ (q - 1) ≤ (ss Z i) ^ (q - 1) := by
  have hs1 := one_le_ss hA i
  have hs0 : (0 : ℝ) < ss Z i := by linarith
  exact Real.rpow_le_rpow_of_nonpos hs0 (ss_le_rr hA i) (by linarith)

/-- **The source's chain, for every finite `q ≤ 0`.**  This is the write-up's new case:
a singular `Z` at a nonpositive order. -/
theorem main_chain {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) {q : ℝ} (hq : q ≤ 0) :
    ∑ i, (rr Z i) ^ (q - 1) ≤ ∑ i, (ss Z i) ^ (q - 1) ∧
    ∑ i, (ss Z i) ^ (q - 1) ≤ ∑ i, (hh hZ i) ^ (1 - q) ∧
    ∑ i, (hh hZ i) ^ (1 - q) ≤ ∑ l ∈ pos hZ, (hZ.eigenvalues l) ^ q := by
  refine ⟨Finset.sum_le_sum fun i _ => chain_three hA hq i,
    Finset.sum_le_sum fun i _ => chain_two hZ hA hP hq i,
    chain_one hZ hA hP hq⟩

/-- and the comparison the source states: the positive spectrum dominates the row sums. -/
theorem vendi_ge {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) {q : ℝ} (hq : q ≤ 0) :
    ∑ i, (rr Z i) ^ (q - 1) ≤ ∑ l ∈ pos hZ, (hZ.eigenvalues l) ^ q := by
  obtain ⟨h1, h2, h3⟩ := main_chain hZ hA hP hq
  linarith


/-! ### The source's scores -/

theorem one_le_rr {Z : Matrix (Fin n) (Fin n) ℝ} (hA : Adm Z) (i : Fin n) :
    1 ≤ rr Z i := le_trans (one_le_ss hA i) (ss_le_rr hA i)

/-- The Vendi score at order `q`, in the source's convention: zero eigenvalues omitted. -/
noncomputable def VS {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (q : ℝ) : ℝ :=
  ((n : ℝ) ^ (-q) * ∑ l ∈ pos hZ, (hZ.eigenvalues l) ^ q) ^ (1 / (1 - q))

/-- The LCR diversity `D_q`. -/
noncomputable def Dq (Z : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) : ℝ :=
  ((n : ℝ) ^ (-q) * ∑ i, (rr Z i) ^ (q - 1)) ^ (1 / (1 - q))

/-- **`VS_q(Z) ≥ D_q(Z)` for every finite `q ≤ 0`**, singular `Z` included — the write-up's
new case, and the one the source had left open. -/
theorem vendi_ge_lcr {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsHermitian) (hA : Adm Z)
    (hP : Z.PosSemidef) {q : ℝ} (hq : q ≤ 0) : Dq Z q ≤ VS hZ q := by
  have hchain := vendi_ge hZ hA hP hq
  have hnq : (0 : ℝ) ≤ (n : ℝ) ^ (-q) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hrr : (0 : ℝ) ≤ ∑ i, (rr Z i) ^ (q - 1) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by linarith [one_le_rr hA i]) _
  have hexp : (0 : ℝ) ≤ 1 / (1 - q) := by
    apply div_nonneg zero_le_one
    linarith
  refine Real.rpow_le_rpow (mul_nonneg hnq hrr) ?_ hexp
  exact mul_le_mul_of_nonneg_left hchain hnq

section Existence

variable {n : ℕ}

/-! ### `Adm` is inhabited

Every theorem in this file is an implication from `Adm Z`, and nothing exhibited an admissible
matrix, so the whole development was at risk of being vacuous.  The identity is admissible: it
is symmetric, positive semidefinite, has unit diagonal, and its entries are `0` and `1`.

**Honest about what this does and does not settle.**  It settles inhabitation, which is what the
vacuity risk needs.  It is NOT the source's interesting case: the write-up's new material is
`q ≤ 0` with `Z` SINGULAR, and the identity is nonsingular.  A singular admissible witness (the
all-ones matrix, for `n ≥ 2`) is not built here.
-/

/-- **The identity matrix is admissible.** -/
theorem adm_one : Adm (1 : Matrix (Fin n) (Fin n) ℝ) where
  herm := Matrix.isHermitian_one
  psd := Matrix.PosSemidef.one
  diag := fun i => Matrix.one_apply_eq i
  nonneg := fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [Matrix.one_apply_ne hij]
  le_one := fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [Matrix.one_apply_ne hij]

/-- **`Adm` is inhabited**, so the file's theorems are not vacuous. -/
theorem exists_adm : ∃ Z : Matrix (Fin n) (Fin n) ℝ, Adm Z := ⟨1, adm_one⟩

/-! ### A SINGULAR admissible witness — the stratum the write-up's new material lives on

`adm_one` settles inhabitation, but the identity is nonsingular, so it does not witness the case
this row's contribution is about: `q ≤ 0` with `Z` **singular**.  Until something singular is
exhibited, `vendi_ge_lcr` could still be vacuous *on the stratum that matters* — a gap no gate
detects, since the theorems are honest implications either way.  The docstring above recorded the
all-ones matrix as the intended witness and said it "is not built here"; it is built here now.

The three ingredients are all structural rather than computational: `vecMulVec 1 1` is positive
semidefinite because it is a Gram matrix (`posSemidef_vecMulVec_self_star`), its entries are
literally `1 * 1`, and it is singular for `n ≥ 2` because `e₀ - e₁` is a nonzero kernel vector —
every row sums to the same thing, so any vector of coordinate-sum zero is killed. -/

/-- The all-ones matrix, presented as a Gram matrix so positive semidefiniteness is structural. -/
noncomputable def allOnes : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec 1 1

@[simp] theorem allOnes_apply (i j : Fin n) : (allOnes : Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
  simp [allOnes, Matrix.vecMulVec_apply]

theorem allOnes_posSemidef : (allOnes : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (1 : Fin n → ℝ)
  simpa [allOnes, star_one] using h

/-- **The all-ones matrix is admissible.** -/
theorem adm_allOnes : Adm (allOnes : Matrix (Fin n) (Fin n) ℝ) where
  herm := allOnes_posSemidef.1
  psd := allOnes_posSemidef
  diag := fun i => by simp
  nonneg := fun i j => by simp
  le_one := fun i j => by simp

/-- **And it is SINGULAR once `n ≥ 2`**: every row is the constant `1`, so rows `0` and `1` are
equal and `det_zero_of_row_eq` applies.  (A kernel vector `e₀ - e₁` also works — every vector is
sent to its coordinate sum — but repeated rows need no vector arithmetic at all.) -/
theorem allOnes_det_eq_zero (h : 2 ≤ n) :
    (allOnes : Matrix (Fin n) (Fin n) ℝ).det = 0 := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  refine Matrix.det_zero_of_row_eq (i := (⟨0, h0⟩ : Fin n)) (j := (⟨1, h1⟩ : Fin n)) ?_ ?_
  · intro hEq
    have := congrArg Fin.val hEq
    simp at this
  · funext j
    simp

/-- **A singular admissible witness exists**, so the `q ≤ 0` singular stratum — the write-up's own
new material — is inhabited in Lean and `vendi_ge_lcr` is not vacuous there. -/
theorem exists_adm_singular (h : 2 ≤ n) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Adm Z ∧ Z.det = 0 :=
  ⟨allOnes, adm_allOnes, allOnes_det_eq_zero h⟩

end Existence

end Principia.MathDB.P371345
