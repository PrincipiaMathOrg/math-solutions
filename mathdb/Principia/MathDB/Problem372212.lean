/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #372212 — the sharp constant is `C_d = d/2`

MathDB open problem #372212.  For positive-definite covariances `A, B` on `ℝ^d`, let `π_ε` be the
Gaussian entropic optimal-transport coupling and `π₀` the unregularized one.  The record asks for
the optimal universal constant in

  `limsup_{ε ↓ 0} W₂²(π_ε, π₀) / ε ≤ C_d`.

The answer is `C_d = d/2`, and the limsup is in fact a limit.

## The split between what is assumed and what is proved

The source's Theorem 3.10 supplies the exact finite-`ε` distance formula, and differentiating it
through the Sylvester equation `SZ + ZS = H` gives

  `lim_{ε ↓ 0} W₂²(π_ε, π₀) / ε = tr(S⁻¹C)`,   `S = G*G + M*M`,  `C = G*M = M*G`,

for properly aligned Green operators `G, M` with `GG* = A`, `MM* = B`.  Formalizing Gaussian
entropic OT and the Fréchet derivative of the matrix square root is a separate project, so **that
identification enters as a hypothesis** (`hL` below) — never as an `axiom`.

Everything downstream is finite-dimensional matrix algebra and is proved here: the bound
`tr(S⁻¹C) ≤ d/2`, its sharpness, and the equality case.  That is the part carrying the constant,
which is what the record actually asks for.

## Why no matrix square root is needed

The textbook argument conjugates by `S^{-1/2}` to get `0 ≺ S^{-1/2} C S^{-1/2} ⪯ I/2`.  Mathlib has
no square root of a positive-semidefinite matrix, but none is needed, because proper alignment
hands over an explicit factorization:

  `S − 2C = G*G + M*M − G*M − M*G = (G − M)*(G − M)`.

So with `N = G − M` the whole inequality is `tr(S⁻¹ N*N) ≥ 0`, and cyclicity turns that into
`tr(N S⁻¹ N*)`, a conjugate of the positive-definite `S⁻¹` — positive semidefinite by
`Matrix.PosSemidef.conjTranspose_mul_mul_same`, hence of nonnegative trace.  The equality case
falls out of the same expression: the trace is a sum of quadratic forms `vᵢ ⬝ S⁻¹ vᵢ` over the rows
`vᵢ` of `N`, each `> 0` unless the row vanishes.

## Scope

`sharp_bound` gives `L ≤ d/2` with equality exactly when `G = M`, and `G = M` forces `A = B`.  The
converse — that `A = B` permits the aligned choice `G = M` — is a statement about the alignment
construction, which this file does not formalize; `cov_eq_of_roots_eq` records the direction that
is proved.  Nothing here claims a lower bound on any other constant.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecificLimits.Basic

namespace Principia.MathDB.P372212

open Matrix

variable {d : ℕ}

/-! ### The two matrix facts

Stated with `ᴴ` rather than `ᵀ`: over `ℝ` the two agree, and Mathlib's positive-definiteness API
is phrased with `ᴴ`, so this avoids a conversion at every step. -/

/-- The `i`-th diagonal entry of `N R Nᴴ` is the quadratic form of `R` at the `i`-th row of `N`. -/
theorem conj_diag (N R : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (N * R * Nᴴ) i i = star (fun j => N i j) ⬝ᵥ (R *ᵥ fun j => N i j) := by
  have hl : (N * R * Nᴴ) i i = ∑ l, (∑ k, N i k * R k l) * N i l := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hr : star (fun j => N i j) ⬝ᵥ (R *ᵥ fun j => N i j)
      = ∑ k, N i k * ∑ l, R k l * N i l := by
    simp [dotProduct, Matrix.mulVec]
  rw [hl, hr]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Conjugating a positive-semidefinite matrix keeps the trace nonnegative. -/
theorem trace_conj_nonneg {N R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosSemidef) :
    0 ≤ (N * R * Nᴴ).trace := by
  have h := hR.conjTranspose_mul_mul_same Nᴴ
  rw [Matrix.conjTranspose_conjTranspose] at h
  exact h.trace_nonneg

/-- …and it vanishes only for `N = 0`, when `R` is positive definite. -/
theorem eq_zero_of_trace_conj_eq_zero {N R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosDef)
    (h : (N * R * Nᴴ).trace = 0) : N = 0 := by
  have hnn : ∀ j : Fin d, 0 ≤ (N * R * Nᴴ) j j := by
    intro j
    rw [conj_diag]
    exact hR.posSemidef.dotProduct_mulVec_nonneg _
  have hsum : ∑ j, (N * R * Nᴴ) j j = 0 := h
  have hzero : ∀ j : Fin d, (N * R * Nᴴ) j j = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnn k).mp hsum j (Finset.mem_univ j)
  ext i j
  have hrow : (fun k => N i k) = 0 := by
    by_contra hne
    have hpos : 0 < star (fun k => N i k) ⬝ᵥ (R *ᵥ fun k => N i k) :=
      hR.dotProduct_mulVec_pos hne
    rw [← conj_diag] at hpos
    exact absurd (hzero i) (ne_of_gt hpos)
  have := congrFun hrow j
  simpa using this

/-! ### The sharp bound -/

/-- **The inequality.**  If `S` is positive definite and `S − 2C` factors as `NᴴN`, then
`tr(S⁻¹C) ≤ d/2`. -/
theorem trace_le_half {S C N : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (hfac : S - (2 : ℝ) • C = Nᴴ * N) : (S⁻¹ * C).trace ≤ (d : ℝ) / 2 := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hone : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hdet
  have hkey : (S⁻¹ * (Nᴴ * N)).trace = (d : ℝ) - 2 * (S⁻¹ * C).trace := by
    rw [← hfac, Matrix.mul_sub, Matrix.trace_sub, hone, Matrix.trace_one, Matrix.mul_smul,
      Matrix.trace_smul]
    simp
  have hcyc : (S⁻¹ * (Nᴴ * N)).trace = (N * S⁻¹ * Nᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hnn : 0 ≤ (N * S⁻¹ * Nᴴ).trace := trace_conj_nonneg hS.inv.posSemidef
  rw [hcyc] at hkey
  linarith

/-- **The equality case.**  Equality holds exactly when the factor vanishes. -/
theorem trace_eq_half_iff {S C N : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (hfac : S - (2 : ℝ) • C = Nᴴ * N) : (S⁻¹ * C).trace = (d : ℝ) / 2 ↔ N = 0 := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hone : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hdet
  have hkey : (S⁻¹ * (Nᴴ * N)).trace = (d : ℝ) - 2 * (S⁻¹ * C).trace := by
    rw [← hfac, Matrix.mul_sub, Matrix.trace_sub, hone, Matrix.trace_one, Matrix.mul_smul,
      Matrix.trace_smul]
    simp
  have hcyc : (S⁻¹ * (Nᴴ * N)).trace = (N * S⁻¹ * Nᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [hcyc] at hkey
  constructor
  · intro heq
    refine eq_zero_of_trace_conj_eq_zero hS.inv ?_
    rw [hkey, heq]
    ring
  · intro hN
    have hz : (N * S⁻¹ * Nᴴ).trace = 0 := by
      rw [hN]
      simp
    rw [hz] at hkey
    linarith

/-! ### Proper alignment -/

/-- Proper alignment `G*M = M*G` makes `S − 2C` an explicit square. -/
theorem align_factor {G M : Matrix (Fin d) (Fin d) ℝ} (halign : Gᴴ * M = Mᴴ * G) :
    (Gᴴ * G + Mᴴ * M) - (2 : ℝ) • (Gᴴ * M) = (G - M)ᴴ * (G - M) := by
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, two_smul, ← halign]
  abel

/-- `G = M` forces the two covariances to agree. -/
theorem cov_eq_of_roots_eq {G M : Matrix (Fin d) (Fin d) ℝ} (h : G = M) :
    G * Gᴴ = M * Mᴴ := by rw [h]

/-! ### The answer -/

/-- **MathDB #372212: the sharp constant is `d/2`.**  Given the source's identification of the
limit with `tr(S⁻¹C)` — the one hypothesis, since it is Theorem 3.10 plus the derivative of the
matrix square root — the limit is at most `d/2`, with equality exactly when the aligned roots
coincide, and then the two covariances agree. -/
theorem sharp_bound {G M : Matrix (Fin d) (Fin d) ℝ} (halign : Gᴴ * M = Mᴴ * G)
    (hS : (Gᴴ * G + Mᴴ * M).PosDef) {L : ℝ}
    (hL : L = ((Gᴴ * G + Mᴴ * M)⁻¹ * (Gᴴ * M)).trace) :
    L ≤ (d : ℝ) / 2 ∧ (L = (d : ℝ) / 2 ↔ G = M) := by
  have hfac := align_factor halign
  refine ⟨?_, ?_⟩
  · rw [hL]
    exact trace_le_half hS hfac
  · rw [hL, trace_eq_half_iff hS hfac, sub_eq_zero]

/-- **The constant is attained, so nothing smaller works.**  Taking `G = M` — the case `A = B` —
makes the factor `G - M` vanish, and the bound is met with equality.  Together with `sharp_bound`
this is what makes `d/2` the *optimal* universal constant rather than merely an upper bound: any
`C' < d/2` is violated by this instance. -/
theorem attained {G : Matrix (Fin d) (Fin d) ℝ} (hS : (Gᴴ * G + Gᴴ * G).PosDef) :
    ((Gᴴ * G + Gᴴ * G)⁻¹ * (Gᴴ * G)).trace = (d : ℝ) / 2 :=
  (trace_eq_half_iff hS (align_factor rfl)).mpr (sub_self G)

end Principia.MathDB.P372212
