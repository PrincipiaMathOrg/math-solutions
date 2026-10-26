import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 327618 — the osculating mean of the polynomial–logarithmic curve

Write-up: `mathdb-open-problems/problems/327618/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It proves **Horwitz's final
conjecture**: for the curve `α(t) = (t, t², …, t^{n-1}, log t)` on `t > 0`, the osculating
hyperplanes at `n` distinct positive nodes meet in a unique point whose last coordinate is

  `i_n = ∑ᵢ wᵢ log aᵢ - H_N`,  `wᵢ = aᵢ^N / ∏_{k≠i}(aᵢ - a_k)`,  `N = n - 1`,

so `M_n = exp(i_n)` is the multivariate **identric** mean.  (The MathDB title says
"logarithmic"; the write-up says explicitly that the formula identified is identric.)

## Where the content sits

The geometry reduces the problem to **polynomial interpolation at the reciprocal nodes**
`rᵢ = 1/aᵢ`: membership in all the hyperplanes says exactly `R(rᵢ) = log aᵢ - H_N` for a
polynomial `R` of degree `< n`, and the last coordinate is `R(0)`.  This module proves
everything from that point on.

* `factor_at_zero` — the single-factor identity `(0 - 1/y)/(1/x - 1/y) = x/(x - y)`.
* `eval_basis_zero` — hence the Lagrange basis at the reciprocal nodes, **evaluated at
  zero**, is exactly `wᵢ = ∏_{k≠i} aᵢ/(aᵢ - a_k)`.
* `w_eq_pow_div` — and that equals the write-up's `aᵢ^N / ∏_{k≠i}(aᵢ - a_k)`, because the
  product has exactly `N` factors.
* `sum_w` — **`∑ᵢ wᵢ = 1`**, by evaluating `Lagrange.sum_basis` at zero.
* `eval_interpolate_zero` and `z_formula` — so `R(0) = ∑ᵢ (log aᵢ - H_N) wᵢ`, which by
  `∑ wᵢ = 1` is `∑ᵢ wᵢ log aᵢ - H_N`.  That is the theorem.
* `term_eq`, `taylor_coeff` — the identity behind the hyperplane equation of Lemma 1:
  `∑_{k=j}^N (1/k)C(k,j) = (1/j)C(N,j)`, from `(1/k)C(k,j) = (1/j)C(k-1,j-1)` and the
  hockey-stick identity.  Stated with `j = p+1`, `N = q+1` so no `ℕ`-subtraction occurs.

## What is carried

`Setup.hz` — that the osculating hyperplanes do meet in a unique point and that its last
coordinate is the value at `0` of the interpolant through `(1/aᵢ, log aᵢ - H_N)`.  That
is Lemma 1 (the Taylor computation, whose combinatorial core `taylor_coeff` is proved
here) together with the identification of the hyperplane system as an interpolation
problem.  The identification of `exp(i_n)` with the multivariate identric mean `I_Z` is
carried as `Setup.identric`.

`Campaigns/MathDB-Formalization/verify_327618.py` checks every step in exact rationals,
and **audits the carried geometry** by building the `n` hyperplane equations numerically
and solving the linear system: the last coordinate agrees with `∑ wᵢ log aᵢ - H_N`.  It
also confirms internality and degree-one homogeneity.
-/

namespace Principia.MathDB.P327618

open Finset Polynomial

/-! ## The harmonic number and the weights -/

/-- `H N = ∑_{k=1}^N 1/k`. -/
noncomputable def H (N : ℕ) : ℝ := ∑ k ∈ Icc 1 N, (1 : ℝ) / k

/-- `w i = ∏_{k ≠ i} a i / (a i - a k)`. -/
noncomputable def w {N : ℕ} (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  ∏ k ∈ univ.erase i, a i / (a i - a k)

theorem card_erase {N : ℕ} (i : Fin (N + 1)) :
    ((univ : Finset (Fin (N + 1))).erase i).card = N := by
  rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

/-- The write-up's other form of the weight: the product has exactly `N` factors. -/
theorem w_eq_pow_div {N : ℕ} (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    w a i = (a i) ^ N / ∏ k ∈ univ.erase i, (a i - a k) := by
  rw [w, Finset.prod_div_distrib, Finset.prod_const, card_erase]

/-! ## The Lagrange basis at zero -/

/-- **The single-factor identity.**  This is what turns reciprocal nodes back into the
original ones. -/
theorem factor_at_zero {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    ((1 : ℝ) / x - 1 / y)⁻¹ * (0 - 1 / y) = x / (x - y) := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hden : (1 : ℝ) / x - 1 / y ≠ 0 := by
    rw [div_sub_div _ _ hx hy]
    simp only [one_mul, mul_one]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hxy)) (mul_ne_zero hx hy)
  field_simp
  ring

/-- **The Lagrange basis at the reciprocal nodes, evaluated at zero, is `w i`.** -/
theorem eval_basis_zero {N : ℕ} (a : Fin (N + 1) → ℝ) (i : Fin (N + 1))
    (hne : ∀ k, a k ≠ 0) (hinj : ∀ j k, j ≠ k → a j ≠ a k) :
    eval 0 (Lagrange.basis univ (fun k => 1 / a k) i) = w a i := by
  rw [Lagrange.basis, eval_prod, w]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hik : i ≠ k := (Finset.ne_of_mem_erase hk).symm
  rw [Lagrange.basisDivisor]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  exact factor_at_zero (hne i) (hne k) (hinj i k hik)

/-- `inv` is injective on ℝ, so distinct nodes have distinct reciprocals. -/
theorem injOn_inv {N : ℕ} (a : Fin (N + 1) → ℝ)
    (hinj : ∀ j k, j ≠ k → a j ≠ a k) :
    Set.InjOn (fun k => 1 / a k) (univ : Finset (Fin (N + 1))) := by
  intro j _ k _ h
  simp only [one_div] at h
  have hajk : a j = a k := inv_injective h
  by_contra hjk
  exact hinj j k hjk hajk

/-- **`∑ᵢ wᵢ = 1`** — the Lagrange basis polynomials sum to one, evaluated at zero. -/
theorem sum_w {N : ℕ} (a : Fin (N + 1) → ℝ) (hne : ∀ k, a k ≠ 0)
    (hinj : ∀ j k, j ≠ k → a j ≠ a k) :
    ∑ i : Fin (N + 1), w a i = 1 := by
  have hs : (univ : Finset (Fin (N + 1))).Nonempty := univ_nonempty
  have hb := Lagrange.sum_basis (injOn_inv a hinj) hs
  have h0 := congrArg (eval 0) hb
  rw [eval_finsetSum, eval_one] at h0
  rw [← h0]
  exact Finset.sum_congr rfl fun i _ => (eval_basis_zero a i hne hinj).symm

/-! ## The last coordinate -/

/-- The value at zero of the interpolant through `(1/aᵢ, rᵢ)`. -/
theorem eval_interpolate_zero {N : ℕ} (a : Fin (N + 1) → ℝ) (r : Fin (N + 1) → ℝ)
    (hne : ∀ k, a k ≠ 0) (hinj : ∀ j k, j ≠ k → a j ≠ a k) :
    eval 0 (Lagrange.interpolate univ (fun k => 1 / a k) r)
      = ∑ i : Fin (N + 1), r i * w a i := by
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_basis_zero a i hne hinj]

/-- **The theorem's last coordinate.** -/
theorem z_formula {N : ℕ} (a : Fin (N + 1) → ℝ) (hne : ∀ k, a k ≠ 0)
    (hinj : ∀ j k, j ≠ k → a j ≠ a k) :
    eval 0 (Lagrange.interpolate univ (fun k => 1 / a k)
        (fun k => Real.log (a k) - H N))
      = (∑ i : Fin (N + 1), w a i * Real.log (a i)) - H N := by
  rw [eval_interpolate_zero a _ hne hinj]
  have hsplit : ∀ i : Fin (N + 1),
      (Real.log (a i) - H N) * w a i = w a i * Real.log (a i) - H N * w a i :=
    fun i => by ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_w a hne hinj, mul_one]

/-! ## The combinatorial core of Lemma 1 -/

/-- `(1/(k+1)) C(k+1, p+1) = (1/(p+1)) C(k, p)`. -/
theorem term_eq (k p : ℕ) :
    (1 : ℝ) / (k + 1) * ((k + 1).choose (p + 1))
      = (1 : ℝ) / (p + 1) * (k.choose p) := by
  have h := Nat.add_one_mul_choose_eq k p
  have hR : ((k : ℝ) + 1) * (k.choose p) = ((k + 1).choose (p + 1)) * ((p : ℝ) + 1) := by
    exact_mod_cast h
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hp : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hR]

/-- **The Taylor coefficient identity** behind the hyperplane equation of Lemma 1:
`∑_{k=j}^N (1/k)C(k,j) = (1/j)C(N,j)`.  Written with `j = p+1` and `N = q+1`, so that no
`ℕ`-subtraction appears. -/
theorem taylor_coeff (p q : ℕ) :
    ∑ k ∈ Icc p q, (1 : ℝ) / (k + 1) * ((k + 1).choose (p + 1))
      = (1 : ℝ) / (p + 1) * ((q + 1).choose (p + 1)) := by
  simp_rw [term_eq]
  rw [← Finset.mul_sum]
  congr 1
  have h := Nat.sum_Icc_choose q p
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h

/-! ## The carried geometry, and the conjecture -/

/-- What the osculating-hyperplane analysis supplies. -/
structure Setup (N : ℕ) where
  /-- the nodes -/
  a : Fin (N + 1) → ℝ
  hpos : ∀ k, 0 < a k
  hdist : ∀ j k, j ≠ k → a j ≠ a k
  /-- the last coordinate of the common point of the osculating hyperplanes -/
  z : ℝ
  /-- **CARRIED** (Lemma 1 and the reduction to interpolation): the hyperplanes meet in a
  unique point, and its last coordinate is the value at `0` of the unique polynomial of
  degree `< n` through the data `(1/aᵢ, log aᵢ - H N)`. -/
  hz : z = eval 0 (Lagrange.interpolate univ (fun k => 1 / a k)
    (fun k => Real.log (a k) - H N))
  /-- the multivariate identric mean of the nodes -/
  IZ : ℝ
  /-- **CARRIED**: the identification of the value with the identric mean. -/
  identric : IZ = Real.exp ((∑ i : Fin (N + 1), w a i * Real.log (a i)) - H N)

namespace Setup

variable {N : ℕ} (S : Setup N)

theorem a_ne_zero (k : Fin (N + 1)) : S.a k ≠ 0 := (S.hpos k).ne'

/-- **HORWITZ'S CONJECTURE.**  The last coordinate is `∑ wᵢ log aᵢ - H_N`, and the mean
`exp z` is the multivariate identric mean. -/
theorem horwitz :
    S.z = (∑ i : Fin (N + 1), w S.a i * Real.log (S.a i)) - H N ∧
      Real.exp S.z = S.IZ := by
  have hzf := z_formula S.a S.a_ne_zero S.hdist
  refine ⟨by rw [S.hz, hzf], ?_⟩
  rw [S.hz, hzf, S.identric]

/-- and in the write-up's displayed form, with `wᵢ = aᵢ^N / ∏_{k≠i}(aᵢ - a_k)`. -/
theorem horwitz_pow_form :
    S.z = (∑ i : Fin (N + 1),
      (S.a i) ^ N / (∏ k ∈ univ.erase i, (S.a i - S.a k)) * Real.log (S.a i)) - H N := by
  rw [S.horwitz.1]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [w_eq_pow_div]

end Setup

end Principia.MathDB.P327618
