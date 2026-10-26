/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #381167 — the pointwise Barbashin criterion is FALSE in general Banach spaces

MathDB open problem #381167, from Popa–Ceaușu–Megan, *On exponential stability for linear
discrete-time systems in Banach spaces* (Comput. Math. Appl., doi 10.1016/j.camwa.2012.01.027;
arXiv:1305.2036, §7).

For a sequence `A(n)` of bounded operators write `A_m^k = A(m) ⋯ A(k+1)` for `k < m` and
`A_m^m = I`.  The source asks whether the existence of `B ≥ 1` with

  (1)  `∑_{k=0}^{m} ‖A_m^k x‖ ≤ B ‖x‖`   for every `m` and every `x`

forces uniform exponential stability.  **It does not.**

## The counterexample

On `X = ℓ¹(ℕ)`, put `A(0) = 0` and `A(n) x = x_{n-1} e_n` for `n ≥ 1`: bounded rank-one operators
of norm one.  Then `A_m^k x = x_k e_m` for `k < m` (`shift_apply`), so

  `∑_{k=0}^{m} ‖A_m^k x‖ = ‖x‖ + ∑_{k<m} |x_k| ≤ 2‖x‖`,

which is (1) with `B = 2` (`summability_bound`).  Yet `A_m^k e_k = e_m` has norm one for every
`k < m`, so no estimate `‖A_m^k x‖ ≤ N e^{-α(m−k)} ‖x‖` can hold (`not_exponentially_stable`).

## Where the argument actually lives

The obstruction is an exchange of a supremum and a sum.  Condition (1) bounds
`sup_{‖x‖=1} ∑_k ‖A_m^k x‖`, whereas the operator-norm criterion controls
`∑_k sup_{‖x‖=1} ‖A_m^k x‖`.  On `ℓ¹` different products read **disjoint coordinates of the same
vector**, so the first stays bounded while every individual operator norm is one.  That is exactly
what `shift_apply` makes visible: `A_m^k` depends on `x` only through the single coordinate `x_k`.

## Statement shapes

Products are indexed by their *length*: `Q k j = A(k+j) ⋯ A(k+1)`, so the source's `A_m^k` is
`Q k (m−k)` and `A_m^m` is `Q k 0 = id`.  This avoids truncated subtraction inside the recursion.

Stability is stated **pointwise** (`‖A_m^k x‖ ≤ N e^{-α(m−k)} ‖x‖`) rather than through operator
norms.  The two are equivalent, and the pointwise form is what the refutation refutes: a single
witness vector `e_k` defeats it.  The operators themselves are genuine `ContinuousLinearMap`s, so
"sequence of bounded operators" is literal and not weakened.

This refutes the conjecture for **general** Banach spaces, which is what the source asks; it says
nothing about Hilbert spaces or about any additional hypothesis the authors might add.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Principia.MathDB.P381167

open scoped ENNReal

/-- The coordinate spaces: `ℓ¹` of reals. -/
abbrev E : ℕ → Type := fun _ => ℝ

local instance factOneLeOne : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩

/-- The Banach space `X = ℓ¹(ℕ)`. -/
abbrev L : Type := lp E 1

/-! ### The unit vectors -/

/-- The `n`-th unit vector of `ℓ¹`. -/
noncomputable def e (n : ℕ) : L := lp.single 1 n (1 : ℝ)

theorem e_self (n : ℕ) : e n n = 1 := by
  rw [e]
  exact lp.single_apply_self (E := E) 1 n (1 : ℝ)

theorem e_ne {n j : ℕ} (h : j ≠ n) : e n j = 0 := by
  rw [e]
  exact lp.single_apply_ne (E := E) 1 n (1 : ℝ) h

theorem norm_e (n : ℕ) : ‖e n‖ = 1 := by
  rw [e, lp.norm_single (by norm_num)]
  simp

/-! ### The operators -/

/-- `A 0 = 0` and `A (n+1) x = xₙ • e_{n+1}`: bounded rank-one operators of norm one. -/
noncomputable def A : ℕ → (L →L[ℝ] L)
  | 0 => 0
  | n + 1 => (ContinuousLinearMap.toSpanSingleton ℝ (e (n + 1))).comp (lp.evalCLM ℝ E 1 n)

theorem A_apply (n : ℕ) (x : L) : A (n + 1) x = x n • e (n + 1) := by
  show (ContinuousLinearMap.toSpanSingleton ℝ (e (n + 1))) (lp.evalCLM ℝ E 1 n x) = _
  have hev : (lp.evalCLM ℝ E 1 n) x = x n := rfl
  rw [ContinuousLinearMap.toSpanSingleton_apply, hev]

/-- `Q k j = A(k+j) ⋯ A(k+1)`, the source's `A_m^k` with `m = k + j`.  Indexing by the length `j`
keeps truncated subtraction out of the recursion. -/
noncomputable def Q (k : ℕ) : ℕ → (L →L[ℝ] L)
  | 0 => ContinuousLinearMap.id ℝ L
  | j + 1 => (A (k + j + 1)).comp (Q k j)

theorem Q_zero (k : ℕ) (x : L) : Q k 0 x = x := rfl

theorem Q_succ (k j : ℕ) (x : L) : Q k (j + 1) x = A (k + j + 1) (Q k j x) := rfl

/-! ### The product formula -/

/-- **`A_m^k x = x_k e_m` for `k < m`.**  Every product reads a single coordinate. -/
theorem shift_apply (k : ℕ) : ∀ (j : ℕ) (x : L), Q k (j + 1) x = x k • e (k + j + 1) := by
  intro j
  induction j with
  | zero =>
    intro x
    rw [Q_succ, Q_zero, A_apply]
  | succ j ih =>
    intro x
    have hidx : k + (j + 1) = k + j + 1 := by omega
    rw [Q_succ, ih x, A_apply, hidx]
    have hcoord : (x k • e (k + j + 1)) (k + j + 1) = x k := by
      rw [lp.coeFn_smul, Pi.smul_apply, e_self]
      simp
    rw [hcoord]

theorem norm_shift (k j : ℕ) (x : L) : ‖Q k (j + 1) x‖ = |x k| := by
  rw [shift_apply, norm_smul, norm_e]
  simp [Real.norm_eq_abs]

/-! ### Condition (1) holds with `B = 2` -/

/-- Partial sums of coordinates are bounded by the `ℓ¹` norm. -/
theorem sum_abs_le (x : L) (m : ℕ) : (∑ k ∈ Finset.range m, |x k|) ≤ ‖x‖ := by
  have h := lp.sum_rpow_le_norm_rpow (p := 1) (E := E) (by norm_num) x (Finset.range m)
  simpa [Real.norm_eq_abs] using h

/-- **Condition (1) with `B = 2`.**  The sum over all `k ≤ m` of `‖A_m^k x‖` is at most `2‖x‖`. -/
theorem summability_bound (m : ℕ) (x : L) :
    (∑ k ∈ Finset.range (m + 1), ‖Q k (m - k) x‖) ≤ 2 * ‖x‖ := by
  rw [Finset.sum_range_succ]
  have hlast : ‖Q m (m - m) x‖ = ‖x‖ := by
    rw [Nat.sub_self, Q_zero]
  have hterms : ∀ k ∈ Finset.range m, ‖Q k (m - k) x‖ = |x k| := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - k - 1, by omega⟩
    rw [hj, norm_shift]
  rw [Finset.sum_congr rfl hterms, hlast]
  have := sum_abs_le x m
  linarith

/-! ### Uniform exponential stability fails -/

/-- Each product carries a unit vector to a unit vector. -/
theorem norm_shift_unit (k j : ℕ) : ‖Q k (j + 1) (e k)‖ = 1 := by
  rw [norm_shift, e_self]
  norm_num

/-- **MathDB #381167: the criterion is false.**  Condition (1) holds with `B = 2`, yet no uniform
exponential estimate does. -/
theorem not_exponentially_stable :
    ¬ ∃ N α : ℝ, 0 < α ∧
      ∀ (k j : ℕ) (x : L), ‖Q k (j + 1) x‖ ≤ N * Real.exp (-α * (j + 1)) * ‖x‖ := by
  rintro ⟨N, α, hα, hbound⟩
  set r : ℝ := Real.exp (-α) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hone : ∀ j : ℕ, (1 : ℝ) ≤ N * r ^ (j + 1) := by
    intro j
    have h := hbound 0 j (e 0)
    rw [norm_shift_unit, norm_e, mul_one] at h
    have hexp : Real.exp (-α * ((j : ℝ) + 1)) = r ^ (j + 1) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring] at h
    rw [show (-α * ((j + 1 : ℕ) : ℝ)) = -α * ((j : ℝ) + 1) by push_cast; ring] at h
    rw [hexp] at h
    exact h
  have hlim : Filter.Tendsto (fun j : ℕ => N * r ^ (j + 1)) Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun j : ℕ => r ^ (j + 1)) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
      exact this.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using hpow.const_mul N
  have hev : ∀ᶠ j : ℕ in Filter.atTop, N * r ^ (j + 1) < 1 :=
    hlim.eventually_lt_const (by norm_num)
  obtain ⟨j, hj⟩ := hev.exists
  exact absurd (hone j) (not_le.mpr hj)

end Principia.MathDB.P381167
