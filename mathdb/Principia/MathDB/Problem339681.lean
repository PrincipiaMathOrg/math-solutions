import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 339681 — the finite-sum coupling construction is impossible

Write-up: `mathdb-open-problems/problems/339681/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It **disproves Conjecture 19** of
Nüsken and Pavliotis (pp. 337–338): that for generators of ergodic Feller semigroups one
can always choose decompositions `L_i = -∑_k (A^i_k)^* A^i_k + B^i` so that *every*
coupling operator is a **finite** sum

  `Γ = ∑_{i ≠ j, k ≤ K_i, l ≤ K_j} α_{ijkl} A^i_k A^j_l`.

## The witness

Each marginal on the circle resets at rate one to an independent uniform point; the
coupling resets **both** coordinates simultaneously to the **same** uniform point.  With
`P` the averaging projection and `Q` the diagonal averaging operator,
`L = P - I`, `L̄ = Q - I`, and `Γ = L̄ - (L_x + L_y) = Q - P_x - P_y + I`, so on simple
tensors

  `Γ(f ⊗ g)(x,y) = ⟨f,g⟩ - g(y)π(f) - f(x)π(g) + f(x)g(y)`.   (1)

## The obstruction is a rank bound, and that is what this module proves

If the finite-sum construction held, then operators in different coordinates commute on
simple tensors and the `(1,2)`/`(2,1)` terms combine to give

  `Γ(f ⊗ g)(x,y) = ∑_{k,l} β_{kl}(x,y) (A^1_k f)(x) (A^2_l g)(y)`,

so for any test functions `f₁,…,f_m` the matrix `M(x,y)_{ij} = Γ(f_i ⊗ f_j)(x,y)`
**factors** as `U(x) β(x,y) V(y)ᵀ` and therefore has rank at most `min(K₁,K₂)`
(`rank_le_of_factor`).  But `m` orthonormal bumps supported away from an open arc `O`
make `M(x,y) = I_m` on `O × O` (`M_eq_one`), and `rank I_m = m`.  Choosing
`m > max(K₁,K₂)` is the contradiction (`no_finite_factorization`).

**The obstruction holds for every choice of the finite families**, because `U`, `β` and
`V` are arbitrary in `rank_le_of_factor`: nothing about the `A^i_k` is used beyond the
shape of the sum.

The conjecture does not fail for want of a decomposition: `decomposition_exists` shows
that for any self-adjoint projection `P`, taking `A = I - P` and `B = 0` gives
`-AᵀA + B = P - I = L` exactly (`witness_admits_decomposition`).

## What is carried

`Setup` carries the probabilistic content: that the reset process is a rich ergodic
Feller coupling, formula (1) for `Γ` on simple tensors, and the existence of the
orthonormal bump family vanishing on `O`.  It also carries — as the *hypothesis* of
`no_finite_factorization` — that the conjecture's construction would produce the
factorization; that step is the source's "operators in different coordinates commute on
simple tensors".

`Campaigns/MathDB-Formalization/verify_339681.py` checks all of it in a finite reset
model (the circle replaced by `ℤ/N`): that `P` and `Q` are constant-preserving
projections, that `-AᵀA = L`, that `L̄` reproduces the prescribed **marginal**, that `Γ`
vanishes on functions of one coordinate alone and satisfies (1) exactly, that the bumps
give `M = I_m` on `O × O`, and that `rank(UβVᵀ) ≤ min(K₁,K₂)` on 300 random instances.
-/

namespace Principia.MathDB.P339681

open Matrix

/-! ## The rank obstruction -/

/-- A matrix factoring through `Fin K₁` and `Fin K₂` has rank at most each of them.
`U`, `B`, `V` are **arbitrary**, which is why the obstruction covers every choice of the
conjecture's finite families. -/
theorem rank_le_of_factor {m K1 K2 : ℕ} (U : Matrix (Fin m) (Fin K1) ℝ)
    (B : Matrix (Fin K1) (Fin K2) ℝ) (V : Matrix (Fin m) (Fin K2) ℝ) :
    (U * B * Vᵀ).rank ≤ K1 ∧ (U * B * Vᵀ).rank ≤ K2 := by
  have hstep : (U * B * Vᵀ).rank ≤ (U * B).rank := Matrix.rank_mul_le_left (U * B) Vᵀ
  constructor
  · exact hstep.trans ((Matrix.rank_mul_le_left U B).trans (Matrix.rank_le_width U))
  · exact hstep.trans ((Matrix.rank_mul_le_right U B).trans (Matrix.rank_le_width B))

theorem rank_one_eq (m : ℕ) : (1 : Matrix (Fin m) (Fin m) ℝ).rank = m := by
  rw [Matrix.rank_one]
  simp

/-- **The identity matrix admits no such factorization once `m` exceeds both widths.** -/
theorem no_factorization_one {m K1 K2 : ℕ} (h1 : K1 < m)
    (U : Matrix (Fin m) (Fin K1) ℝ) (B : Matrix (Fin K1) (Fin K2) ℝ)
    (V : Matrix (Fin m) (Fin K2) ℝ) :
    (1 : Matrix (Fin m) (Fin m) ℝ) ≠ U * B * Vᵀ := by
  intro h
  have hr := (rank_le_of_factor U B V).1
  rw [← h, rank_one_eq] at hr
  omega

/-! ## The decomposition the conjecture asks for does exist -/

/-- For a self-adjoint projection `P`, `A = I - P` gives `-AᵀA = P - I`. -/
theorem decomposition_exists {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hsymm : Pᵀ = P) :
    -((1 - P)ᵀ * (1 - P)) = P - 1 := by
  have ht : (1 - P)ᵀ = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  rw [ht]
  have hmul : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hP]
    abel
  rw [hmul]
  abel

/-- So the marginal generator really does admit a decomposition of the required shape;
the disproof is not an artefact of there being none. -/
theorem witness_admits_decomposition {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hsymm : Pᵀ = P) :
    ∃ (A B : Matrix (Fin n) (Fin n) ℝ), -(Aᵀ * A) + B = P - 1 :=
  ⟨1 - P, 0, by rw [decomposition_exists P hP hsymm]; abel⟩

/-! ## The carried probabilistic content -/

/-- The reset coupling, reduced to what the obstruction uses. -/
structure Setup where
  /-- the state space of one marginal (the circle) -/
  T : Type
  /-- the mean against the invariant measure `π` -/
  mean : (T → ℝ) → ℝ
  /-- the `L²(π)` inner product -/
  ip : (T → ℝ) → (T → ℝ) → ℝ
  /-- the coupling operator evaluated on a simple tensor -/
  Gam : (T → ℝ) → (T → ℝ) → T → T → ℝ
  /-- **CARRIED** — formula (1), from `Γ = Q - P_x - P_y + I`. -/
  hGam : ∀ f g x y,
    Gam f g x y = ip f g - g y * mean f - f x * mean g + f x * g y
  /-- the number of test functions -/
  m : ℕ
  /-- the test functions -/
  fs : Fin m → (T → ℝ)
  /-- the open arc they avoid -/
  O : Set T
  /-- **CARRIED** (the bump construction): they are orthonormal in `L²(π)`. -/
  horth : ∀ i j, ip (fs i) (fs j) = if i = j then 1 else 0
  /-- **CARRIED**: each is supported in the complementary arc, so vanishes on `O`. -/
  hvanish : ∀ (i : Fin m) (x : T), x ∈ O → fs i x = 0

namespace Setup

/-- The matrix of coupling values at a point. -/
noncomputable def Mat (S : Setup) (x y : S.T) : Matrix (Fin S.m) (Fin S.m) ℝ :=
  Matrix.of fun i j => S.Gam (S.fs i) (S.fs j) x y

/-- **On `O × O` the matrix is the identity.**  Every term of (1) except the inner
product carries a factor `f_i(x)` or `f_j(y)`, and both vanish there. -/
theorem M_eq_one (S : Setup) {x y : S.T} (hx : x ∈ S.O) (hy : y ∈ S.O) :
    S.Mat x y = 1 := by
  ext i j
  rw [Mat, Matrix.of_apply, S.hGam, S.hvanish i x hx, S.hvanish j y hy, S.horth]
  by_cases h : i = j
  · simp [h, Matrix.one_apply]
  · simp [h, Matrix.one_apply_ne h]

/-- **THE DISPROOF.**  With more test functions than either finite range, the coupling
matrix at a point of `O × O` cannot factor — so `Γ` is not a finite sum of the
conjectured shape, for any decompositions of the marginal generators. -/
theorem no_finite_factorization (S : Setup) {K1 K2 : ℕ} (h1 : K1 < S.m)
    {x y : S.T} (hx : x ∈ S.O) (hy : y ∈ S.O)
    (U : Matrix (Fin S.m) (Fin K1) ℝ) (B : Matrix (Fin K1) (Fin K2) ℝ)
    (V : Matrix (Fin S.m) (Fin K2) ℝ) :
    S.Mat x y ≠ U * B * Vᵀ := by
  rw [S.M_eq_one hx hy]
  exact no_factorization_one h1 U B V

/-- The same conclusion stated against the rank directly: the coupling matrix has full
rank on `O × O`, while any admissible factorization would cap it at `min(K₁,K₂)`. -/
theorem rank_Mat (S : Setup) {x y : S.T} (hx : x ∈ S.O) (hy : y ∈ S.O) :
    (S.Mat x y).rank = S.m := by
  rw [S.M_eq_one hx hy, rank_one_eq]

end Setup

end Principia.MathDB.P339681
