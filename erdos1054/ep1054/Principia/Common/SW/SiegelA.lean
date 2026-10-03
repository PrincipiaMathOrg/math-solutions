/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.ZeroFreeB

/-!
# Siegel–Walfisz, `SiegelA`: Siegel's theorem (Goldfeld's route), part A: Euler-factor positivity, hyperbola method

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 4641–6667; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
built in the PrimeNumberTheoremAnd workspace on Mathlib `db127794`, one day from ours). The master
imported `Mathlib`, `PrimeNumberTheoremAnd.MediumPNT` and `PrimeNumberTheoremAnd.PerronFormula`; here
the Mathlib imports are narrowed, the two Perron-kernel shims are re-proved from Mathlib's Mellin
inversion (`Principia.Common.SW.PerronKernel`), and the `medium_PNT` shim is not ported (see
`MediumPNTBound` in `Principia.Common.SW.Rate`). Declarations live in `Principia.Common.SW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex

namespace Principia.Common.SW

/-! ### ================= SiegelTheorem.lean (verbatim, deduplicated) ================= -/

set_option maxHeartbeats 2000000

/-!
# Siegel's theorem for Dirichlet L-functions — brick-by-brick (Goldfeld's route)

Target: `siegel_zero_free`: ∀ ε > 0, ∃ c(ε) > 0, every real zero β of every L(·,χ)
(χ real nontrivial mod q) satisfies β ≤ 1 − c(ε)/q^ε. Ineffective (the dichotomy
case-split is classical); the last missing zero-free input for Siegel–Walfisz and
hence for almost-all binary Goldbach (see the approved roadmap plan).

Phase A of the roadmap; every lemma verified 0-error + `#print axioms`-clean
([propext, Classical.choice, Quot.sound]) before banking.
-/

open PowerSeries ArithmeticFunction Finset Filter

/-- The geometric power series `Σ xⁿ tⁿ` — the local Euler factor `(1 − xt)⁻¹`
    of a completely multiplicative function with `g(p) = x`. -/
noncomputable def geomPS (x : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun n => x ^ n)

lemma coeff_geomPS (x : ℝ) (n : ℕ) : (PowerSeries.coeff (R := ℝ) n) (geomPS x) = x ^ n := by
  rw [geomPS, PowerSeries.coeff_mk]

/-- Products preserve coefficientwise nonnegativity. -/
lemma coeff_mul_nonneg (f g : PowerSeries ℝ)
    (hf : ∀ n, 0 ≤ (PowerSeries.coeff (R := ℝ) n) f) (hg : ∀ n, 0 ≤ (PowerSeries.coeff (R := ℝ) n) g)
    (n : ℕ) : 0 ≤ (PowerSeries.coeff (R := ℝ) n) (f * g) := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hf p.1) (hg p.2)

/-- `(1−t)⁻¹(1−xt)⁻¹` has nonnegative coefficients for `x ∈ {−1,0,1}`
    (the character-value alphabet): `Σ_{j≤n} xʲ ≥ 0`. -/
lemma coeff_one_mul_geomPS_nonneg (x : ℝ) (hx : x = -1 ∨ x = 0 ∨ x = 1) (n : ℕ) :
    0 ≤ (PowerSeries.coeff (R := ℝ) n) (geomPS 1 * geomPS x) := by
  rw [PowerSeries.coeff_mul]
  have hsum : ∑ p ∈ Finset.antidiagonal n,
      (PowerSeries.coeff (R := ℝ) p.1) (geomPS 1) * (PowerSeries.coeff (R := ℝ) p.2) (geomPS x)
      = ∑ p ∈ Finset.antidiagonal n, x ^ p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [coeff_geomPS, coeff_geomPS, one_pow, one_mul]
  rw [hsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only
  rcases hx with rfl | rfl | rfl
  · -- x = −1: the alternating partial sum is 0 or 1
    have h : ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ (n - i)
        = ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ i := by
      have hr := Finset.sum_range_reflect (fun i => ((-1:ℝ)) ^ i) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      exact hr
    rw [h, neg_one_geom_sum]
    split <;> norm_num
  · -- x = 0: only the i = n term (0^0 = 1) survives
    apply Finset.sum_nonneg
    intro i _
    rcases Nat.eq_zero_or_pos (n - i) with h0 | h0
    · rw [h0]; norm_num
    · rw [zero_pow h0.ne']
  · -- x = 1: n+1 ones
    simp
    positivity

/-- `(1−xt)⁻¹(1+xt)⁻¹ = (1−x²t²)⁻¹` has nonnegative coefficients for EVERY real `x`:
    the coefficient is `xⁿ` times the alternating sum, nonzero only for even `n`. -/
lemma coeff_geomPS_mul_neg_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ (PowerSeries.coeff (R := ℝ) n) (geomPS x * geomPS (-x)) := by
  rw [PowerSeries.coeff_mul]
  have hsum : ∑ p ∈ Finset.antidiagonal n,
      (PowerSeries.coeff (R := ℝ) p.1) (geomPS x) * (PowerSeries.coeff (R := ℝ) p.2) (geomPS (-x))
      = x ^ n * ∑ p ∈ Finset.antidiagonal n, (-1:ℝ) ^ p.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [coeff_geomPS, coeff_geomPS, neg_pow]
    have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    rw [show x ^ p.1 * ((-1:ℝ) ^ p.2 * x ^ p.2) = (-1:ℝ) ^ p.2 * (x ^ p.1 * x ^ p.2) by ring,
      ← pow_add, hpn]
    ring
  rw [hsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only
  rcases Nat.even_or_odd n with he | ho
  · apply mul_nonneg (he.pow_nonneg x)
    have h : ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ (n - i)
        = ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ i := by
      have hr := Finset.sum_range_reflect (fun i => ((-1:ℝ)) ^ i) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      exact hr
    rw [h, neg_one_geom_sum]
    split <;> norm_num
  · -- odd n: the alternating sum over n+1 (even count) terms vanishes
    have h : ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ (n - i)
        = ∑ i ∈ Finset.range (n + 1), ((-1:ℝ)) ^ i := by
      have hr := Finset.sum_range_reflect (fun i => ((-1:ℝ)) ^ i) (n + 1)
      simp only [Nat.add_sub_cancel] at hr
      exact hr
    rw [h, neg_one_geom_sum, if_pos ho.add_one, mul_zero]

/-- **The Goldfeld positivity core** (Siegel brick A1a): for character values
    `x, y ∈ {−1,0,1}`, the local factor product
    `(1−t)⁻¹(1−xt)⁻¹(1−yt)⁻¹(1−xyt)⁻¹` of `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` has
    nonnegative power-series coefficients — by pairing the four geometric series
    so each pair is nonneg: `y = 1`: `(1·x)(1·x)`; `y = 0`: the `y`-factors are `1`;
    `y = −1`: `(1·(−1)) ⋆ (x·(−x))`. -/
lemma coeff_euler_quad_nonneg (x y : ℝ) (hx : x = -1 ∨ x = 0 ∨ x = 1)
    (hy : y = -1 ∨ y = 0 ∨ y = 1) (n : ℕ) :
    0 ≤ (PowerSeries.coeff (R := ℝ) n) (geomPS 1 * geomPS x * geomPS y * geomPS (x * y)) := by
  rcases hy with rfl | rfl | rfl
  · -- y = −1: regroup as (1 ⋆ (−1)) * (x ⋆ (−x))
    have hre : geomPS 1 * geomPS x * geomPS (-1) * geomPS (x * -1)
        = (geomPS 1 * geomPS (-1)) * (geomPS x * geomPS (-x)) := by
      rw [show x * (-1:ℝ) = -x by ring]
      ring
    rw [hre]
    apply coeff_mul_nonneg
    · exact coeff_one_mul_geomPS_nonneg (-1) (Or.inl rfl)
    · exact coeff_geomPS_mul_neg_nonneg x
  · -- y = 0: geomPS 0 has coefficients δ₀; the product bound reduces via nonneg factors
    rw [show x * (0:ℝ) = 0 by ring]
    apply coeff_mul_nonneg
    · apply coeff_mul_nonneg
      · exact coeff_one_mul_geomPS_nonneg x hx
      · intro m
        rw [coeff_geomPS]
        rcases Nat.eq_zero_or_pos m with rfl | h0
        · norm_num
        · rw [zero_pow h0.ne']
    · intro m
      rw [coeff_geomPS]
      rcases Nat.eq_zero_or_pos m with rfl | h0
      · norm_num
      · rw [zero_pow h0.ne']
  · -- y = 1: regroup as (1 ⋆ x) * (1 ⋆ x)
    have hre : geomPS 1 * geomPS x * geomPS 1 * geomPS (x * 1)
        = (geomPS 1 * geomPS x) * (geomPS 1 * geomPS x) := by
      rw [mul_one]
      ring
    rw [hre]
    exact coeff_mul_nonneg _ _
      (coeff_one_mul_geomPS_nonneg x hx) (coeff_one_mul_geomPS_nonneg x hx) n

/-- **Dirichlet convolution at prime powers** (Siegel brick A1b-i):
    `(f ⋆ g)(pᵐ) = Σ_{i≤m} f(pⁱ)·g(p^{m−i})` — the divisor pairs of `pᵐ` are exactly
    `(pⁱ, p^{m−i})`. -/
lemma mul_apply_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (f * g) (p ^ m) = ∑ i ∈ Finset.range (m + 1), f (p ^ i) * g (p ^ (m - i)) := by
  rw [ArithmeticFunction.mul_apply]
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 < p := hp.one_lt
  apply Finset.sum_nbij' (fun pr => pr.1.factorization p)
    (fun i => ((p ^ i : ℕ), (p ^ (m - i) : ℕ)))
  · -- membership: divisor pair → range
    intro pr hpr
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hmul, _⟩ := hpr
    have hdvd : pr.1 ∣ p ^ m := ⟨pr.2, hmul.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [Finset.mem_range, hk', Nat.factorization_pow_self hp]
    omega
  · -- membership: range → divisor pair
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mem_divisorsAntidiagonal]
    constructor
    · rw [← pow_add]
      congr 1
      omega
    · positivity
  · -- left inverse
    intro pr hpr
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hmul, _⟩ := hpr
    have hdvd : pr.1 ∣ p ^ m := ⟨pr.2, hmul.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hfact : pr.1.factorization p = k := by
      rw [hk', Nat.factorization_pow_self hp]
    rw [hfact]
    have hb : pr.2 = p ^ (m - k) := by
      have h1 : p ^ k * pr.2 = p ^ k * p ^ (m - k) := by
        rw [← pow_add, show k + (m - k) = m by omega, ← hk', hmul]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [← hk', ← hb]
  · -- right inverse
    intro i hi
    rw [Nat.factorization_pow_self hp]
  · -- summand match
    intro pr hpr
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hmul, _⟩ := hpr
    have hdvd : pr.1 ∣ p ^ m := ⟨pr.2, hmul.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hfact : pr.1.factorization p = k := by
      rw [hk', Nat.factorization_pow_self hp]
    have hb : pr.2 = p ^ (m - k) := by
      have h1 : p ^ k * pr.2 = p ^ k * p ^ (m - k) := by
        rw [← pow_add, show k + (m - k) = m by omega, ← hk', hmul]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [hfact, ← hk', hb]

/-- The prime-power fiber of an arithmetic function, as a power series in the exponent. -/
noncomputable def primeFiber (f : ArithmeticFunction ℝ) (p : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun m => f (p ^ m))

lemma coeff_primeFiber (f : ArithmeticFunction ℝ) (p m : ℕ) :
    (PowerSeries.coeff (R := ℝ) m) (primeFiber f p) = f (p ^ m) := by
  rw [primeFiber, PowerSeries.coeff_mk]

/-- **The prime fiber is multiplicative** (Siegel brick A1b-ii): Dirichlet convolution
    restricted to powers of one prime IS power-series multiplication. -/
lemma primeFiber_mul (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    primeFiber (f * g) p = primeFiber f p * primeFiber g p := by
  ext m
  rw [coeff_primeFiber, PowerSeries.coeff_mul, mul_apply_prime_pow f g hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_primeFiber, coeff_primeFiber]

/-- A bare function packaged as an arithmetic function (forcing the value 0 at 0). -/
noncomputable def toArith (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else g n, by simp⟩

lemma toArith_apply (g : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) : toArith g n = g n := by
  simp [toArith, hn]

/-- Completely multiplicative bare functions give multiplicative arithmetic functions. -/
lemma toArith_isMultiplicative (g : ℕ → ℝ) (hg : ∀ m n, g (m * n) = g m * g n)
    (hg1 : g 1 = 1) : (toArith g).IsMultiplicative := by
  constructor
  · rw [toArith_apply g 1 one_ne_zero, hg1]
  · intro m n _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [toArith]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [toArith]
    rw [toArith_apply g _ (by positivity), toArith_apply g _ hm.ne',
      toArith_apply g _ hn.ne', hg]

/-- Completely multiplicative functions turn powers into powers. -/
lemma comp_mult_pow (g : ℕ → ℝ) (hg : ∀ m n, g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (a : ℕ) : ∀ m : ℕ, g (a ^ m) = g a ^ m := by
  intro m
  induction m with
  | zero => simpa using hg1
  | succ k ih =>
    rw [pow_succ, hg, ih, pow_succ]

/-- The prime fiber of a packaged completely multiplicative function is the geometric
    series at its prime value. -/
lemma primeFiber_toArith (g : ℕ → ℝ) (hg : ∀ m n, g (m * n) = g m * g n) (hg1 : g 1 = 1)
    {p : ℕ} (hp : p.Prime) : primeFiber (toArith g) p = geomPS (g p) := by
  ext m
  rw [coeff_primeFiber, coeff_geomPS, toArith_apply g _ (pow_ne_zero m hp.ne_zero),
    comp_mult_pow g hg hg1 p m]

/-- **Nonnegativity of the Goldfeld convolution** (Siegel brick A1c): for completely
    multiplicative `g₁, g₂` with values in `{−1,0,1}` (the real-character shape), every
    value of the Dirichlet convolution `1 ⋆ g₁ ⋆ g₂ ⋆ g₁g₂` — the coefficient sequence
    of `ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)` — is nonnegative, and the value at 1 is 1. -/
theorem quad_conv_nonneg (g₁ g₂ : ℕ → ℝ)
    (h₁ : ∀ m n, g₁ (m * n) = g₁ m * g₁ n) (h₂ : ∀ m n, g₂ (m * n) = g₂ m * g₂ n)
    (h₁1 : g₁ 1 = 1) (h₂1 : g₂ 1 = 1)
    (h₁v : ∀ n, g₁ n = -1 ∨ g₁ n = 0 ∨ g₁ n = 1)
    (h₂v : ∀ n, g₂ n = -1 ∨ g₂ n = 0 ∨ g₂ n = 1) :
    (∀ n, 0 ≤ (toArith (fun _ => 1) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) n)
    ∧ (toArith (fun _ => 1) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) 1 = 1 := by
  set A : ArithmeticFunction ℝ := toArith (fun _ => 1) * toArith g₁ * toArith g₂
    * toArith (fun k => g₁ k * g₂ k) with hA
  have hm0 : (toArith (fun _ => (1:ℝ))).IsMultiplicative :=
    toArith_isMultiplicative _ (fun _ _ => (one_mul 1).symm) rfl
  have hm1 : (toArith g₁).IsMultiplicative := toArith_isMultiplicative g₁ h₁ h₁1
  have hm2 : (toArith g₂).IsMultiplicative := toArith_isMultiplicative g₂ h₂ h₂1
  have h12 : ∀ m n, (fun k => g₁ k * g₂ k) (m * n)
      = (fun k => g₁ k * g₂ k) m * (fun k => g₁ k * g₂ k) n := by
    intro m n
    simp only
    rw [h₁, h₂]
    ring
  have h121 : (fun k => g₁ k * g₂ k) 1 = 1 := by
    simp only
    rw [h₁1, h₂1, one_mul]
  have hm3 : (toArith (fun k => g₁ k * g₂ k)).IsMultiplicative :=
    toArith_isMultiplicative _ h12 h121
  have hmA : A.IsMultiplicative := ((hm0.mul hm1).mul hm2).mul hm3
  -- prime-power nonnegativity via the fiber bridge + the A1a positivity core
  have hpp : ∀ p : ℕ, p.Prime → ∀ m : ℕ, 0 ≤ A (p ^ m) := by
    intro p hp m
    have hfib : primeFiber A p
        = geomPS 1 * geomPS (g₁ p) * geomPS (g₂ p) * geomPS (g₁ p * g₂ p) := by
      rw [hA, primeFiber_mul _ _ hp, primeFiber_mul _ _ hp, primeFiber_mul _ _ hp,
        primeFiber_toArith _ (fun _ _ => (one_mul 1).symm) rfl hp,
        primeFiber_toArith g₁ h₁ h₁1 hp, primeFiber_toArith g₂ h₂ h₂1 hp,
        primeFiber_toArith _ h12 h121 hp]
    have := coeff_euler_quad_nonneg (g₁ p) (g₂ p) (h₁v p) (h₂v p) m
    rw [← hfib, coeff_primeFiber] at this
    exact this
  refine ⟨?_, hmA.map_one⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ArithmeticFunction.map_zero]
  have hfac := hmA.multiplicative_factorization A hn.ne'
  rw [hfac, Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hpmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors
    (by rwa [Nat.support_factorization] at hpmem)
  exact hpp p hp _

/-- The lattice-point index set of the hyperbola method: pairs `(d,e)` with
    `1 ≤ d, e` and `d·e ≤ N`. -/
def hypSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N)

/-- **Convolution partial sums are lattice-point sums** (Siegel brick A2a-i). -/
lemma sum_conv_eq_sum_hypSet (f g : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (f * g) n = ∑ p ∈ hypSet N, f p.1 * g p.2 := by
  have hL : ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ n ∈ Icc 1 N, ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          f p.1 * g p.2 := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    rw [ArithmeticFunction.mul_apply,
      Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by omega) hnN]
  rw [hL, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  rw [hypSet]
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hp.1.1 hp.2.1).ne'

/-- Row fibers of the hyperbola set: for `1 ≤ d`, the `e` with `d·e ≤ N` form `Icc 1 (N/d)`. -/
lemma row_fiber (N d : ℕ) (hd : 0 < d) :
    (Ioc 0 N).filter (fun e => d * e ≤ N) = Icc 1 (N / d) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · intro ⟨⟨he0, _⟩, hde⟩
    refine ⟨he0, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
    rw [Nat.mul_comm]
    exact hde
  · intro ⟨he1, heNd⟩
    have hde : d * e ≤ N := by
      have h := (Nat.le_div_iff_mul_le hd).mp heNd
      rw [Nat.mul_comm e d] at h
      exact h
    have heN : e ≤ N := by
      calc e ≤ d * e := Nat.le_mul_of_pos_left e hd
        _ ≤ N := hde
    exact ⟨⟨by omega, heN⟩, hde⟩

/-- Column fibers above the split: for `1 ≤ e`, the `d > y` with `d·e ≤ N` form
    `Icc (y+1) (N/e)`. -/
lemma col_fiber (N y e : ℕ) (he : 0 < e) :
    (Ioc 0 N).filter (fun d => ¬ d ≤ y ∧ d * e ≤ N) = Icc (y + 1) (N / e) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, not_le]
  constructor
  · intro ⟨⟨_, _⟩, hyd, hde⟩
    exact ⟨hyd, (Nat.le_div_iff_mul_le he).mpr hde⟩
  · intro ⟨hyd, hdNe⟩
    have hde : d * e ≤ N := (Nat.le_div_iff_mul_le he).mp hdNe
    have hdN : d ≤ N := by
      calc d ≤ d * e := Nat.le_mul_of_pos_right d he
        _ ≤ N := hde
    exact ⟨⟨by omega, hdN⟩, hyd, hde⟩

/-- **The Dirichlet hyperbola identity** (Siegel brick A2a): for any split `y ≤ N`,
    `Σ_{n≤N}(f⋆g)(n) = Σ_{d≤y} f(d)·G(N/d) + Σ_{e≤N/(y+1)} g(e)·(F(N/e) − F(y))` —
    the exact identity behind the coefficient asymptotic `A(x) = λx + O(Q^c x^{4/5})`. -/
theorem hyperbola_identity (f g : ArithmeticFunction ℝ) (N y : ℕ) (hy : y ≤ N) :
    ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ d ∈ Icc 1 y, f d * (∑ e ∈ Icc 1 (N / d), g e)
        + ∑ e ∈ Icc 1 (N / (y + 1)),
            g e * ((∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d) := by
  rw [sum_conv_eq_sum_hypSet, hypSet,
    ← Finset.sum_filter_add_sum_filter_not _ (fun p => p.1 ≤ y)]
  congr 1
  · -- head: rows d ≤ y
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
    simp only
    rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 N) (fun d => d ≤ y)]
    have hz : ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d ≤ y),
        ∑ e ∈ Ioc 0 N, (if d * e ≤ N ∧ d ≤ y then f d * g e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro e _
      rw [Finset.mem_filter] at hd
      rw [if_neg]
      intro hcon
      exact hd.2 hcon.2
    rw [hz, add_zero]
    have hIoc : (Ioc 0 N).filter (fun d => d ≤ y) = Icc 1 y := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hIoc]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [Finset.mul_sum, ← row_fiber N d (by omega), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hde : d * e ≤ N
    · rw [if_pos ⟨hde, hdy⟩, if_pos hde]
    · rw [if_neg (fun h => hde h.1), if_neg hde]
  · -- tail: columns, d > y
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product_right]
    simp only
    have hsub : Icc 1 (N / (y + 1)) ⊆ Ioc 0 N := by
      intro e he
      obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
      rw [Finset.mem_Ioc]
      have : N / (y + 1) ≤ N := Nat.div_le_self N (y + 1)
      omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro e he
      obtain ⟨he1, heNy⟩ := Finset.mem_Icc.mp he
      have hy1e : y + 1 ≤ N / e + 1 := by
        have h1 : e * (y + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp heNy
        have h2 : y + 1 ≤ N / e := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr
          rw [Nat.mul_comm]
          exact h1
        omega
      have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
        intro a b
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      have hdiff : (∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d
          = ∑ d ∈ Icc (y + 1) (N / e), f d := by
        rw [← hIcoIcc 1 (N / e),
          ← Finset.sum_Ico_consecutive (fun d => f d) (by omega : 1 ≤ y + 1) hy1e,
          hIcoIcc 1 y, hIcoIcc (y + 1) (N / e), add_sub_cancel_left]
      rw [hdiff, Finset.mul_sum, ← col_fiber N y e (by omega), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hcase : d * e ≤ N ∧ ¬ d ≤ y
      · rw [if_pos hcase, if_pos ⟨hcase.2, hcase.1⟩, mul_comm]
      · rw [if_neg hcase, if_neg (fun hcon => hcase ⟨hcon.2, hcon.1⟩)]
    · intro e heIoc heNot
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      intro ⟨hde, hdy⟩
      apply heNot
      rw [Finset.mem_Icc]
      obtain ⟨he0, _⟩ := Finset.mem_Ioc.mp heIoc
      refine ⟨by omega, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0 < y + 1)]
      push_neg at hdy
      calc e * (y + 1) ≤ e * d := by
            apply Nat.mul_le_mul_left
            omega
        _ = d * e := Nat.mul_comm e d
        _ ≤ N := hde

/-- **Harmonic partial sums** (Siegel brick A2b-i): `Σ_{c≤z} 1/c ≤ 1 + log z`. -/
lemma sum_one_div_le_log (z : ℕ) (hz : 1 ≤ z) :
    ∑ c ∈ Icc 1 z, (1 : ℝ) / c ≤ 1 + Real.log z := by
  have hh := harmonic_le_one_add_log z
  have hcast : ((harmonic z : ℚ) : ℝ) = ∑ c ∈ Icc 1 z, (1 : ℝ) / c := by
    rw [harmonic,
      show Icc 1 z = Ico 1 (z + 1) from by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega,
      Finset.sum_Ico_eq_sum_range]
    push_cast
    apply Finset.sum_congr (by norm_num)
    intro i _
    push_cast
    ring
  rw [← hcast]
  exact_mod_cast hh

/-- **Square-root reciprocal partial sums** (Siegel brick A2b-ii): `Σ_{e≤z} 1/√e ≤ 2√z` —
    by the telescoping `1/√e ≤ 2(√e − √(e−1))`. -/
lemma sum_one_div_sqrt_le (z : ℕ) :
    ∑ e ∈ Icc 1 z, (1 : ℝ) / Real.sqrt e ≤ 2 * Real.sqrt z := by
  induction z with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hstep : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hstep, Finset.sum_insert (by simp)]
    have hkey : (1 : ℝ) / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
      have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hprod : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)
          * (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n) = 1 := by
        have h1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
          Real.sq_sqrt (by positivity)
        have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        nlinarith [h1, h2]
      have hsumle : Real.sqrt ((n : ℝ) + 1) + Real.sqrt n
          ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
        have := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
        linarith
      rw [div_le_iff₀ hs1]
      have hdiffpos : 0 < Real.sqrt ((n : ℝ) + 1) - Real.sqrt n := by
        rcases lt_or_ge (Real.sqrt n) (Real.sqrt ((n:ℝ) + 1)) with h | h
        · linarith
        · exfalso
          nlinarith [hprod]
      nlinarith [hprod, hsumle, hdiffpos, hs1]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at *
    linarith [ih, hkey]

/-- **Row decomposition of hyperbola-set sums** (Siegel brick A2b-iii):
    `Σ_{p ∈ hypSet N} F(p) = Σ_{d≤N} Σ_{e≤N/d} F(d,e)`. -/
lemma sum_hypSet_eq_rows (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N), F p
      = ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F (d, e) := by
  rw [Finset.sum_filter, Finset.sum_product]
  have hIoc : (Ioc 0 N : Finset ℕ) = Icc 1 N := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  have hrow : Icc 1 (N / d) = (Icc 1 N).filter (fun e => d * e ≤ N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro ⟨he1, heNd⟩
      have hde : d * e ≤ N := by
        have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp heNd
        rw [Nat.mul_comm e d] at h
        exact h
      have heN : e ≤ N := le_trans (Nat.le_mul_of_pos_left e (by omega)) hde
      exact ⟨⟨he1, heN⟩, hde⟩
    · intro ⟨⟨he1, _⟩, hde⟩
      refine ⟨he1, (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr ?_⟩
      rw [Nat.mul_comm]
      exact hde
  rw [hrow, Finset.sum_filter]

/-- **The divisor-weighted root sum** (Siegel brick A2b-iv):
    `Σ_{p ∈ hypSet z} 1/√(p₁p₂) ≤ 2√z(1 + log z)` — the error-term workhorse:
    every `Σ_{e≤z} d(e)/√e` style bound routes through this lattice form. -/
lemma sum_hypSet_inv_sqrt_le (z : ℕ) (hz : 1 ≤ z) :
    ∑ p ∈ (Ioc 0 z ×ˢ Ioc 0 z).filter (fun p => p.1 * p.2 ≤ z),
        (1 : ℝ) / Real.sqrt (p.1 * p.2)
      ≤ 2 * Real.sqrt z * (1 + Real.log z) := by
  rw [sum_hypSet_eq_rows]
  have hrow : ∀ d ∈ Icc 1 z, ∑ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
      ≤ (1 / (d : ℝ)) * (2 * Real.sqrt z) := by
    intro d hd
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    have hsplit : ∀ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
        = (1 / Real.sqrt d) * (1 / Real.sqrt e) := by
      intro e he
      obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
      simp only
      rw [Real.sqrt_mul (Nat.cast_nonneg d)]
      ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    have hsum := sum_one_div_sqrt_le (z / d)
    have hdivle : Real.sqrt ((z / d : ℕ) : ℝ) ≤ Real.sqrt z / Real.sqrt d := by
      calc Real.sqrt ((z / d : ℕ) : ℝ) ≤ Real.sqrt ((z : ℝ) / d) :=
            Real.sqrt_le_sqrt Nat.cast_div_le
        _ = Real.sqrt z / Real.sqrt d := Real.sqrt_div (Nat.cast_nonneg z) d
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
    calc (1 / Real.sqrt d) * ∑ e ∈ Icc 1 (z / d), (1:ℝ) / Real.sqrt e
        ≤ (1 / Real.sqrt d) * (2 * Real.sqrt ((z / d : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (1 / Real.sqrt d) * (2 * (Real.sqrt z / Real.sqrt d)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hdivle]
      _ = 2 * Real.sqrt z / (Real.sqrt d * Real.sqrt d) := by ring
      _ = (1 / (d : ℝ)) * (2 * Real.sqrt z) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg d)]
          ring
  calc ∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
      ≤ ∑ d ∈ Icc 1 z, (1 / (d : ℝ)) * (2 * Real.sqrt z) := Finset.sum_le_sum hrow
    _ = (∑ d ∈ Icc 1 z, (1 : ℝ) / d) * (2 * Real.sqrt z) := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + Real.log z) * (2 * Real.sqrt z) := by
        apply mul_le_mul_of_nonneg_right (sum_one_div_le_log z hz) (by positivity)
    _ = 2 * Real.sqrt z * (1 + Real.log z) := by ring

/-- **Abel rearrangement over a tail window** (Siegel brick A2c-i-a): with
    `G t = Σ_{n≤t} g n`, for `y ≤ z`:
    `Σ_{y<d≤z} g(d)/d = Σ_{y<d≤z} G(d)(1/d − 1/(d+1)) + G(z)/(z+1) − G(y)/(y+1)`. -/
lemma abel_window (g : ℕ → ℝ) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, g d / d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1) := by
  intro z
  induction z with
  | zero =>
    intro hy0
    interval_cases y
    simp
  | succ m ih =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · -- y = m + 1: both windows empty
      have hy : y = m + 1 := by omega
      subst hy
      simp
    · -- extend from m to m+1
      have hstepL : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hstepG : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstepL, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        hstepG, Finset.sum_insert (by simp), ih hge]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- The telescoping kernel sum: `Σ_{y<d≤z} (1/d − 1/(d+1)) = 1/(y+1) − 1/(z+1)`. -/
lemma telescope_kernel (y : ℕ) : ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, ((1 : ℝ) / d - 1 / (d + 1)) = 1 / (y + 1) - 1 / (z + 1) := by
  intro z
  induction z with
  | zero =>
    intro hy0
    interval_cases y
    simp
  | succ m ihm =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · have hy : y = m + 1 := by omega
      subst hy
      simp
    · have hstep : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstep, Finset.sum_insert (by simp), ihm hge]
      push_cast
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      field_simp
      ring

/-- **The bounded-sum Abel tail bound** (Siegel brick A2c-i): if all partial sums of `g`
    are bounded by `q`, the tail `Σ_{y<d≤z} g(d)/d` is at most `2q/(y+1)` — uniformly
    in `z`. The engine of both `Σ_{d≤y} g(d)/d`'s convergence and its tail rate. -/
lemma abel_tail_bound (g : ℕ → ℝ) (q : ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q) (y z : ℕ) (hyz : y ≤ z) :
    |∑ d ∈ Icc (y + 1) z, g d / d| ≤ 2 * q / (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  rw [abel_window g y z hyz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ q * ((1 : ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    rw [abs_mul, abs_of_nonneg hker]
    exact mul_le_mul_of_nonneg_right (hG d) hker
  have htele := telescope_kernel y z hyz
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) / (z + 1)| + |(∑ n ∈ Icc 1 y, g n) / (y + 1)| := by
        set A := ∑ d ∈ Icc (y + 1) z,
          (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1)) with hA
        set B := (∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1) with hB
        set C := (∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1) with hC
        have h1 : |A + B| ≤ |A| + |B| := abs_add_le A B
        have h2 : |A + B - C| ≤ |A + B| + |C| := by
          rw [sub_eq_add_neg]
          have := abs_add_le (A + B) (-C)
          rwa [abs_neg] at this
        linarith [h1, h2]
    _ ≤ (q * ((1:ℝ) / (y + 1) - 1 / (z + 1))) + q / (z + 1) + q / (y + 1) := by
        have hs : |∑ d ∈ Icc (y + 1) z,
            (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
            ≤ q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * ((1 : ℝ) / d - 1 / (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
                rw [← Finset.mul_sum, htele]
        have hz1 : |(∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1)| ≤ q / (z + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG z) (by positivity)
        have hy1 : |(∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1)| ≤ q / (y + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG y) (by positivity)
        linarith [hs, hz1, hy1]
    _ ≤ 2 * q / (y + 1) := by
        have hzq : (0:ℝ) ≤ q / (z + 1) := by positivity
        have h1 : q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) + q / (z + 1) = q / (y + 1) := by
          field_simp
          ring
        have h2 : q / ((y:ℝ) + 1) + q / (y + 1) = 2 * q / (y + 1) := by ring
        linarith [h1, h2]

/-- Prefix-sum difference over `Icc 1`: `Σ_{≤z} − Σ_{≤y} = Σ_{y<·≤z}`. -/
lemma sum_Icc_split (F : ℕ → ℝ) (y z : ℕ) (hyz : y ≤ z) :
    ∑ d ∈ Icc 1 z, F d - ∑ d ∈ Icc 1 y, F d = ∑ d ∈ Icc (y + 1) z, F d := by
  have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
    intro a b
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [← hIcoIcc 1 z,
    ← Finset.sum_Ico_consecutive F (by omega : 1 ≤ y + 1) (by omega : y + 1 ≤ z + 1),
    hIcoIcc 1 y, hIcoIcc (y + 1) z, add_sub_cancel_left]

/-- **The logarithmic mean exists with a tail rate** (Siegel brick A2c-ii): if every
    partial sum of `g` is bounded by `q`, then `S_y = Σ_{d≤y} g(d)/d` converges to some
    `L` with `|L − S_y| ≤ 2q/(y+1)` for every `y` — the abstract `L(1,χ)` of the
    hyperbola main term. -/
theorem log_mean_exists (g : ℕ → ℝ) (q : ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q) :
    ∃ L : ℝ, ∀ y : ℕ, |L - ∑ d ∈ Icc 1 y, g d / d| ≤ 2 * q / (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  set S : ℕ → ℝ := fun y => ∑ d ∈ Icc 1 y, g d / d with hS
  have hdiff : ∀ y z : ℕ, y ≤ z → |S z - S y| ≤ 2 * q / (y + 1) := by
    intro y z hyz
    rw [hS]
    simp only
    rw [sum_Icc_split (fun d => g d / d) y z hyz]
    exact abel_tail_bound g q hG y z hyz
  have hb0 : Filter.Tendsto (fun N : ℕ => 2 * q / ((N : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    have h2 := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := 2 * q)) h1
    simpa using h2
  have hcauchy : CauchySeq S := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 2 * q / ((N : ℝ) + 1)) _ hb0
    intro n m N hn hm
    rw [Real.dist_eq]
    rcases le_total n m with h | h
    · rw [abs_sub_comm]
      calc |S m - S n| ≤ 2 * q / ((n : ℝ) + 1) := hdiff n m h
        _ ≤ 2 * q / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            exact_mod_cast Nat.add_le_add_right hn 1
    · calc |S n - S m| ≤ 2 * q / ((m : ℝ) + 1) := hdiff m n h
        _ ≤ 2 * q / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            exact_mod_cast Nat.add_le_add_right hm 1
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ?_⟩
  intro y
  have htend : Filter.Tendsto (fun z : ℕ => |S z - S y|) Filter.atTop
      (nhds (|L - S y|)) := by
    apply Filter.Tendsto.abs
    exact Filter.Tendsto.sub_const hL (S y)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop y] with z hz
  exact hdiff y z hz

/-- Partial sums of the packaged constant-one function count the interval. -/
lemma sum_toArith_one (M : ℕ) :
    ∑ e ∈ Icc 1 M, toArith (fun _ => (1:ℝ)) e = (M : ℝ) := by
  have hterm : ∀ e ∈ Icc 1 M, toArith (fun _ => (1:ℝ)) e = 1 := by
    intro e he
    obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
    rw [toArith_apply _ _ (by omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc]
  simp

/-- **The divisor-character asymptotic** (Siegel brick A2c-iii): for `g` with values
    bounded by 1, partial sums bounded by `q`, and logarithmic mean `L`,
    `|Σ_{n≤N}(g⋆1)(n) − L·N| ≤ (1+4q)·(√N + 1)` — the `H₁(t) = L(1,χ)t + O(q√t)`
    input of the hyperbola method, with the split at `y = ⌊√N⌋`. -/
theorem divisor_char_asymptotic (g : ℕ → ℝ) (q L : ℝ)
    (hgb : ∀ n, |g n| ≤ 1)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q)
    (hL : ∀ y : ℕ, |L - ∑ d ∈ Icc 1 y, g d / d| ≤ 2 * q / (y + 1))
    (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, (toArith g * toArith (fun _ => (1:ℝ))) n - L * N|
      ≤ (1 + 4 * q) * (Real.sqrt N + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  set y : ℕ := Nat.sqrt N with hy
  have hyN : y ≤ N := Nat.sqrt_le_self N
  rw [hyperbola_identity _ _ N y hyN]
  -- head with the floor split
  have hhead : ∀ d ∈ Icc 1 y, toArith g d * (∑ e ∈ Icc 1 (N / d), toArith (fun _ => (1:ℝ)) e)
      = g d * ((N / d : ℕ) : ℝ) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    rw [sum_toArith_one, toArith_apply _ _ (by omega)]
  rw [Finset.sum_congr rfl hhead]
  -- decompose ⌊N/d⌋ = N/d − frac(d)
  have hfloor : ∀ d ∈ Icc 1 y, g d * ((N / d : ℕ) : ℝ)
      = (N : ℝ) * (g d / d) - g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : ((d:ℝ)) ≠ 0 := by
      have : (0:ℝ) < d := by exact_mod_cast hd1
      linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hfloor, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- name the pieces
  set S : ℝ := ∑ d ∈ Icc 1 y, g d / d with hS
  set FR : ℝ := ∑ d ∈ Icc 1 y, g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hFR
  set T : ℝ := ∑ e ∈ Icc 1 (N / (y + 1)), toArith (fun _ => (1:ℝ)) e
      * ((∑ d ∈ Icc 1 (N / e), toArith g d) - ∑ d ∈ Icc 1 y, toArith g d) with hT
  -- bound the fractional-part sum: |FR| ≤ y
  have hFRb : |FR| ≤ y := by
    rw [hFR]
    calc |∑ d ∈ Icc 1 y, g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |g d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, 1 := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
          rw [abs_mul]
          have hfr0 : (0:ℝ) ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) := by
            rw [sub_nonneg]
            exact Nat.cast_div_le
          have hfr1 : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
            have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hd0]
              have hnat : N < (N / d + 1) * d := by
                have hexp : (N / d + 1) * d = d * (N / d) + d := by ring
                rw [hexp]
                have h1 := Nat.div_add_mod N d
                have h2 := Nat.mod_lt N (show 0 < d by omega)
                omega
              exact_mod_cast hnat
            linarith
          rw [abs_of_nonneg hfr0]
          nlinarith [hgb d, hfr0, hfr1, abs_nonneg (g d)]
      _ ≤ (y : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  -- bound the tail: |T| ≤ 2q · N/(y+1)
  have hTb : |T| ≤ 2 * q * ((N / (y + 1) : ℕ) : ℝ) := by
    rw [hT]
    calc |∑ e ∈ Icc 1 (N / (y + 1)), toArith (fun _ => (1:ℝ)) e
          * ((∑ d ∈ Icc 1 (N / e), toArith g d) - ∑ d ∈ Icc 1 y, toArith g d)|
        ≤ ∑ e ∈ Icc 1 (N / (y + 1)), |toArith (fun _ => (1:ℝ)) e
          * ((∑ d ∈ Icc 1 (N / e), toArith g d) - ∑ d ∈ Icc 1 y, toArith g d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 (N / (y + 1)), 2 * q := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
          have hone : toArith (fun _ => (1:ℝ)) e = 1 := toArith_apply _ _ (by omega)
          rw [hone, one_mul]
          have hsg : ∀ t : ℕ, ∑ d ∈ Icc 1 t, toArith g d = ∑ d ∈ Icc 1 t, g d := by
            intro t
            apply Finset.sum_congr rfl
            intro d hd
            obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
            exact toArith_apply _ _ (by omega)
          rw [hsg, hsg]
          calc |∑ d ∈ Icc 1 (N / e), g d - ∑ d ∈ Icc 1 y, g d|
              ≤ |∑ d ∈ Icc 1 (N / e), g d| + |∑ d ∈ Icc 1 y, g d| := by
                have := abs_add_le (∑ d ∈ Icc 1 (N / e), g d) (-(∑ d ∈ Icc 1 y, g d))
                rwa [abs_neg, ← sub_eq_add_neg] at this
            _ ≤ q + q := add_le_add (hG _) (hG _)
            _ = 2 * q := by ring
      _ = 2 * q * ((N / (y + 1) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          ring
  -- bound the mean deviation: |N·S − N·L| ≤ 2qN/(y+1)
  have hSL : |(N : ℝ) * S - L * N| ≤ (N : ℝ) * (2 * q / (y + 1)) := by
    have h := hL y
    calc |(N : ℝ) * S - L * N| = (N : ℝ) * |L - S| := by
          rw [show (N : ℝ) * S - L * N = -((N:ℝ) * (L - S)) by ring, abs_neg, abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ))]
      _ ≤ (N : ℝ) * (2 * q / (y + 1)) := by
          apply mul_le_mul_of_nonneg_left h (by positivity)
  -- the √N conversions
  have hyle : (y : ℝ) ≤ Real.sqrt N := by
    rw [hy]
    have h1 : ((Nat.sqrt N : ℝ)) ^ 2 ≤ (N : ℝ) := by
      exact_mod_cast Nat.sqrt_le' N
    exact Real.le_sqrt_of_sq_le h1
  have hNdiv : ((N / (y + 1) : ℕ) : ℝ) ≤ Real.sqrt N := by
    have h1 : ((N / (y + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((y : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := y + 1)
      push_cast at this
      exact this
    have h2 : (N : ℝ) / ((y : ℝ) + 1) ≤ Real.sqrt N := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg N)
      have hy1 : Real.sqrt N ≤ (y : ℝ) + 1 := by
        rw [hy]
        have := Nat.lt_succ_sqrt' N
        have hcast : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
          push_cast
          exact_mod_cast this
        nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N),
          Real.sqrt_nonneg (N:ℝ), hcast]
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    linarith
  have hNy1 : (N : ℝ) * (2 * q / (y + 1)) ≤ 2 * q * Real.sqrt N := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (y:ℝ) + 1)]
    have hy1 : Real.sqrt N ≤ (y : ℝ) + 1 := by
      rw [hy]
      have := Nat.lt_succ_sqrt' N
      have hcast : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
        push_cast
        exact_mod_cast this
      nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N), hcast]
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg N)
    have hkey : Real.sqrt N * Real.sqrt N ≤ Real.sqrt N * ((y:ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hy1 (Real.sqrt_nonneg _)
    nlinarith [Real.sqrt_nonneg (N : ℝ), hq, hkey, hsq]
  -- assemble
  have hgoal : |(N : ℝ) * S - FR + T - L * N| ≤ (1 + 4*q) * (Real.sqrt N + 1) := by
    have h1 : |(N : ℝ) * S - FR + T - L * N|
        ≤ |(N : ℝ) * S - L * N| + |FR| + |T| := by
      have ha := abs_add_le ((N : ℝ) * S - L * N) (-FR)
      have hb := abs_add_le ((N : ℝ) * S - L * N + -FR) T
      rw [abs_neg] at ha
      have hrw : (N : ℝ) * S - FR + T - L * N = ((N : ℝ) * S - L * N + -FR) + T := by
        ring
      rw [hrw]
      calc |((N : ℝ) * S - L * N + -FR) + T|
          ≤ |(N : ℝ) * S - L * N + -FR| + |T| := abs_add_le _ _
        _ ≤ |(N : ℝ) * S - L * N| + |FR| + |T| := by linarith [ha]
    calc |(N : ℝ) * S - FR + T - L * N|
        ≤ |(N : ℝ) * S - L * N| + |FR| + |T| := h1
      _ ≤ (N : ℝ) * (2 * q / (y + 1)) + (y : ℝ) + 2 * q * ((N / (y + 1) : ℕ) : ℝ) := by
          linarith [hSL, hFRb, hTb]
      _ ≤ 2 * q * Real.sqrt N + Real.sqrt N + 2 * q * Real.sqrt N := by
          have h3 : 2 * q * ((N / (y + 1) : ℕ) : ℝ) ≤ 2 * q * Real.sqrt N :=
            mul_le_mul_of_nonneg_left hNdiv (by linarith)
          linarith [hNy1, hyle, h3]
      _ ≤ (1 + 4*q) * (Real.sqrt N + 1) := by
          have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
          nlinarith [hq, hs0]
  exact hgoal

/-- **The doubly-bounded convolution has √-size partial sums** (Siegel brick A2d):
    if `k₁, k₂` have values bounded by 1 and partial sums bounded by `q₁, q₂`, then
    `|Σ_{n≤t}(k₁⋆k₂)(n)| ≤ (2q₁+q₂)(√t+1)` — the `K(t) ≪ Q²√t` bound for
    `k = χ₂ ⋆ (χ₁χ₂)`, whose L-series has no pole. -/
theorem bounded_conv_sqrt_bound (k₁ k₂ : ℕ → ℝ) (q₁ q₂ : ℝ)
    (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (hK1 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k₁ n| ≤ q₁)
    (hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k₂ n| ≤ q₂)
    (t : ℕ) :
    |∑ n ∈ Icc 1 t, (toArith k₁ * toArith k₂) n| ≤ (2 * q₁ + q₂) * (Real.sqrt t + 1) := by
  have hq1 : 0 ≤ q₁ := le_trans (abs_nonneg _) (hK1 0)
  have hq2 : 0 ≤ q₂ := le_trans (abs_nonneg _) (hK2 0)
  set y : ℕ := Nat.sqrt t with hy
  have hyt : y ≤ t := Nat.sqrt_le_self t
  rw [hyperbola_identity _ _ t y hyt]
  have hsg : ∀ (k : ℕ → ℝ) (M : ℕ), ∑ d ∈ Icc 1 M, toArith k d = ∑ d ∈ Icc 1 M, k d := by
    intro k M
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    exact toArith_apply _ _ (by omega)
  -- the √ conversions (as in A2c-iii)
  have hyle : (y : ℝ) ≤ Real.sqrt t := by
    rw [hy]
    have h1 : ((Nat.sqrt t : ℝ)) ^ 2 ≤ (t : ℝ) := by exact_mod_cast Nat.sqrt_le' t
    exact Real.le_sqrt_of_sq_le h1
  have hy1 : Real.sqrt t ≤ (y : ℝ) + 1 := by
    rw [hy]
    have hlt := Nat.lt_succ_sqrt' t
    have hcast : (t : ℝ) < ((Nat.sqrt t : ℝ) + 1) ^ 2 := by
      push_cast
      exact_mod_cast hlt
    nlinarith [Real.sqrt_nonneg (t : ℝ), Real.sq_sqrt (Nat.cast_nonneg t), hcast]
  have hNdiv : ((t / (y + 1) : ℕ) : ℝ) ≤ Real.sqrt t := by
    have h1 : ((t / (y + 1) : ℕ) : ℝ) ≤ (t : ℝ) / ((y : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := t) (n := y + 1)
      push_cast at this
      exact this
    have h2 : (t : ℝ) / ((y : ℝ) + 1) ≤ Real.sqrt t := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : Real.sqrt t * Real.sqrt t = (t : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg t)
      nlinarith [Real.sqrt_nonneg (t : ℝ), hy1, hsq]
    linarith
  -- head bound
  have hhead : |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)|
      ≤ (y : ℝ) * q₂ := by
    calc |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)|
        ≤ ∑ d ∈ Icc 1 y, |toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, q₂ := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          rw [abs_mul, toArith_apply _ _ (by omega), hsg]
          calc |k₁ d| * |∑ e ∈ Icc 1 (t / d), k₂ e| ≤ 1 * q₂ :=
              mul_le_mul (h1b d) (hK2 _) (abs_nonneg _) zero_le_one
            _ = q₂ := one_mul q₂
      _ = (y : ℝ) * q₂ := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- tail bound
  have htail : |∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
      * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)|
      ≤ ((t / (y + 1) : ℕ) : ℝ) * (2 * q₁) := by
    calc |∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
        * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)|
        ≤ ∑ e ∈ Icc 1 (t / (y + 1)), |toArith k₂ e
          * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 (t / (y + 1)), 2 * q₁ := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
          rw [abs_mul, toArith_apply _ _ (by omega), hsg, hsg]
          have hdiff : |∑ d ∈ Icc 1 (t / e), k₁ d - ∑ d ∈ Icc 1 y, k₁ d| ≤ 2 * q₁ := by
            have h := abs_add_le (∑ d ∈ Icc 1 (t / e), k₁ d) (-(∑ d ∈ Icc 1 y, k₁ d))
            rw [abs_neg, ← sub_eq_add_neg] at h
            calc |∑ d ∈ Icc 1 (t / e), k₁ d - ∑ d ∈ Icc 1 y, k₁ d|
                ≤ |∑ d ∈ Icc 1 (t / e), k₁ d| + |∑ d ∈ Icc 1 y, k₁ d| := h
              _ ≤ q₁ + q₁ := add_le_add (hK1 _) (hK1 _)
              _ = 2 * q₁ := by ring
          calc |k₂ e| * |∑ d ∈ Icc 1 (t / e), k₁ d - ∑ d ∈ Icc 1 y, k₁ d|
              ≤ 1 * (2 * q₁) := mul_le_mul (h2b e) hdiff (abs_nonneg _) zero_le_one
            _ = 2 * q₁ := one_mul _
      _ = ((t / (y + 1) : ℕ) : ℝ) * (2 * q₁) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- assemble
  calc |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)
        + ∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
          * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)|
      ≤ |∑ d ∈ Icc 1 y, toArith k₁ d * (∑ e ∈ Icc 1 (t / d), toArith k₂ e)|
        + |∑ e ∈ Icc 1 (t / (y + 1)), toArith k₂ e
          * ((∑ d ∈ Icc 1 (t / e), toArith k₁ d) - ∑ d ∈ Icc 1 y, toArith k₁ d)| :=
        abs_add_le _ _
    _ ≤ (y : ℝ) * q₂ + ((t / (y + 1) : ℕ) : ℝ) * (2 * q₁) := add_le_add hhead htail
    _ ≤ Real.sqrt t * q₂ + Real.sqrt t * (2 * q₁) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hyle hq2
        · apply mul_le_mul_of_nonneg_right hNdiv (by linarith)
    _ ≤ (2 * q₁ + q₂) * (Real.sqrt t + 1) := by
        have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
        nlinarith [hq1, hq2, hs0]

/-- Sharp 3/2-power telescoping (Siegel brick A2e-i-a):
    `Σ_{y<d≤z} 1/(d√d) ≤ 2/√y − 2/√z` for `1 ≤ y ≤ z` — from the previous-interval
    comparison `1/(d√d) ≤ 2(1/√(d−1) − 1/√d)`. -/
lemma sum_three_half_tail_sharp (y : ℕ) (hy1 : 1 ≤ y) : ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d)
      ≤ 2 / Real.sqrt y - 2 / Real.sqrt z := by
  intro z
  induction z with
  | zero =>
    intro hy0
    omega
  | succ m ihm =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · -- y = m + 1: empty window, RHS = 0
      have hy : y = m + 1 := by omega
      subst hy
      simp
    · -- extend from m to m+1; m ≥ y ≥ 1
      have hm1 : 1 ≤ m := le_trans hy1 hge
      have hstep : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstep, Finset.sum_insert (by simp)]
      have hm0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hm10 : (0:ℝ) < (m : ℝ) + 1 := by linarith
      set a : ℝ := Real.sqrt m with ha
      set b : ℝ := Real.sqrt ((m : ℝ) + 1) with hb
      have hs1 : (0:ℝ) < a := Real.sqrt_pos.mpr hm0
      have hs2 : (0:ℝ) < b := Real.sqrt_pos.mpr hm10
      have hsq1 : a * a = (m : ℝ) := Real.mul_self_sqrt hm0.le
      have hsq2 : b * b = (m : ℝ) + 1 := Real.mul_self_sqrt hm10.le
      have hmono : a ≤ b := Real.sqrt_le_sqrt (by linarith)
      have hba : b * b - a * a = 1 := by linarith [hsq1, hsq2]
      have hkey : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))
          ≤ 2 / a - 2 / b := by
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast, ← hb]
        rw [div_sub_div _ _ (ne_of_gt hs1) (ne_of_gt hs2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        -- goal: 1·(a·b) ≤ (2b − 2a)·((m+1)·b); with m+1 = b², reduces to ab ≤ m+2
        have hab : a * b ≤ b * b := mul_le_mul_of_nonneg_right hmono hs2.le
        nlinarith [hab, hba, hsq1, hsq2, hs1, hs2, hmono,
          mul_pos hs1 hs2, mul_nonneg (mul_nonneg (sub_nonneg.mpr hmono) hs2.le) hs2.le,
          mul_le_mul_of_nonneg_right hab hs2.le]
      have hih := ihm hge
      have hccast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hsm : Real.sqrt ((m : ℕ) : ℝ) = a := rfl
      calc (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))
            + ∑ d ∈ Icc (y + 1) m, (1 : ℝ) / (d * Real.sqrt d)
          ≤ (2 / a - 2 / b) + (2 / Real.sqrt y - 2 / a) :=
            add_le_add hkey hih
        _ = 2 / Real.sqrt y - 2 / b := by ring
        _ = 2 / Real.sqrt y - 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
            rw [show Real.sqrt ((m + 1 : ℕ) : ℝ) = b from by rw [hccast]]

/-- Boundary helper: `(√t+1)/(t+1) ≤ 2/√t` for `t ≥ 1`. -/
lemma sqrt_boundary_le (t : ℕ) (ht : 1 ≤ t) :
    (Real.sqrt t + 1) / ((t : ℝ) + 1) ≤ 2 / Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt ht0.le
  have hs1 : (1:ℝ) ≤ Real.sqrt t :=
    Real.one_le_sqrt.mpr (by exact_mod_cast ht)
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith [hsq, hs1, hs]

/-- **The √-growth Abel tail** (Siegel brick A2e-ii-a): if the partial sums of `k`
    satisfy `|K(t)| ≤ B(√t+1)`, then `|Σ_{y<d≤z} k(d)/d| ≤ 7B/√y` for `1 ≤ y ≤ z` —
    the tail engine for the pole-free convolution side of the Goldfeld product. -/
theorem abel_tail_sqrt (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    (y z : ℕ) (hy1 : 1 ≤ y) (hyz : y ≤ z) :
    |∑ d ∈ Icc (y + 1) z, k d / d| ≤ 7 * B / Real.sqrt y := by
  have hB : 0 ≤ B := by
    have h0 := hK 0
    simp at h0
    linarith [abs_nonneg (∑ n ∈ Icc 1 0, k n), h0]
  have hy0 : (0:ℝ) < y := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsyz : Real.sqrt y ≤ Real.sqrt z := Real.sqrt_le_sqrt (by exact_mod_cast hyz)
  have hsz : (0:ℝ) < Real.sqrt z := lt_of_lt_of_le hsy hsyz
  rw [abel_window k y z hyz]
  -- termwise: |K(d)|·κ_d ≤ B/(d√d) + B·κ_d
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ B * ((1:ℝ) / (d * Real.sqrt d)) + B * ((1:ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast this
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
    have hsqd : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt hd0.le
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    have hkerid : (1 : ℝ) / d - 1 / (d + 1) = 1 / ((d : ℝ) * (d + 1)) := by
      field_simp
      ring
    have hsdker : Real.sqrt d * ((1:ℝ) / d - 1 / (d + 1)) ≤ 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [hkerid,
        show Real.sqrt d * ((1:ℝ) / ((d:ℝ) * (d + 1)))
          = Real.sqrt d / ((d:ℝ) * (d + 1)) from by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsqd, hd0, hsd]
    rw [abs_mul, abs_of_nonneg hker]
    calc |∑ n ∈ Icc 1 d, k n| * ((1:ℝ) / d - 1 / (d + 1))
        ≤ (B * (Real.sqrt d + 1)) * ((1:ℝ) / d - 1 / (d + 1)) :=
          mul_le_mul_of_nonneg_right (hK d) hker
      _ = B * (Real.sqrt d * ((1:ℝ) / d - 1 / (d + 1)))
          + B * ((1:ℝ) / d - 1 / (d + 1)) := by ring
      _ ≤ B * ((1:ℝ) / (d * Real.sqrt d)) + B * ((1:ℝ) / d - 1 / (d + 1)) := by
          have := mul_le_mul_of_nonneg_left hsdker hB
          linarith
  -- the summed middle piece
  have hmid : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
      ≤ B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)) := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, (B * ((1:ℝ) / (d * Real.sqrt d))
          + B * ((1:ℝ) / d - 1 / (d + 1))) := Finset.sum_le_sum hterm
      _ = B * (∑ d ∈ Icc (y + 1) z, (1:ℝ) / (d * Real.sqrt d))
          + B * (∑ d ∈ Icc (y + 1) z, ((1:ℝ) / d - 1 / (d + 1))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ B * (2 / Real.sqrt y - 2 / Real.sqrt z)
          + B * (1 / ((y:ℝ) + 1) - 1 / ((z:ℝ) + 1)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (sum_three_half_tail_sharp y hy1 z hyz) hB
          · rw [telescope_kernel y z hyz]
      _ ≤ B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)) := by
          have h1 : (0:ℝ) ≤ 2 / Real.sqrt z := by positivity
          have h2 : (0:ℝ) ≤ 1 / ((z:ℝ) + 1) := by positivity
          nlinarith [hB, h1, h2]
  -- boundaries
  have hbz : |(∑ n ∈ Icc 1 z, k n) / ((z:ℝ) + 1)| ≤ 2 * B / Real.sqrt y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
    have h1 : |∑ n ∈ Icc 1 z, k n| / ((z:ℝ) + 1) ≤ B * ((Real.sqrt z + 1) / ((z:ℝ) + 1)) := by
      rw [mul_div_assoc'] at *
      apply div_le_div_of_nonneg_right (hK z) (by positivity)
    have h2 : (Real.sqrt z + 1) / ((z:ℝ) + 1) ≤ 2 / Real.sqrt z :=
      sqrt_boundary_le z (by omega)
    have h3 : (2:ℝ) / Real.sqrt z ≤ 2 / Real.sqrt y := by
      apply div_le_div_of_nonneg_left (by norm_num) hsy hsyz
    calc |∑ n ∈ Icc 1 z, k n| / ((z:ℝ) + 1)
        ≤ B * ((Real.sqrt z + 1) / ((z:ℝ) + 1)) := h1
      _ ≤ B * (2 / Real.sqrt y) := by
          apply mul_le_mul_of_nonneg_left _ hB
          linarith
      _ = 2 * B / Real.sqrt y := by ring
  have hby : |(∑ n ∈ Icc 1 y, k n) / ((y:ℝ) + 1)| ≤ 2 * B / Real.sqrt y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
    have h1 : |∑ n ∈ Icc 1 y, k n| / ((y:ℝ) + 1) ≤ B * ((Real.sqrt y + 1) / ((y:ℝ) + 1)) := by
      rw [mul_div_assoc'] at *
      apply div_le_div_of_nonneg_right (hK y) (by positivity)
    have h2 : (Real.sqrt y + 1) / ((y:ℝ) + 1) ≤ 2 / Real.sqrt y :=
      sqrt_boundary_le y hy1
    calc |∑ n ∈ Icc 1 y, k n| / ((y:ℝ) + 1)
        ≤ B * ((Real.sqrt y + 1) / ((y:ℝ) + 1)) := h1
      _ ≤ B * (2 / Real.sqrt y) := mul_le_mul_of_nonneg_left h2 hB
      _ = 2 * B / Real.sqrt y := by ring
  -- assemble: mid + boundaries, with 1/(y+1) ≤ 1/√y
  have hy1r : (1:ℝ) / ((y:ℝ) + 1) ≤ 1 / Real.sqrt y := by
    apply div_le_div_of_nonneg_left one_pos.le hsy
    nlinarith [Real.mul_self_sqrt hy0.le,
      Real.one_le_sqrt.mpr (by exact_mod_cast hy1 : (1:ℝ) ≤ (y:ℝ)), hsy]
  set M := ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1)) with hM
  set Bz := (∑ n ∈ Icc 1 z, k n) / ((z:ℝ) + 1) with hBz
  set By := (∑ n ∈ Icc 1 y, k n) / ((y:ℝ) + 1) with hBy
  have htri : |M + Bz - By| ≤ |M| + |Bz| + |By| := by
    have h1 := abs_add_le M Bz
    have h2 := abs_add_le (M + Bz) (-By)
    rw [abs_neg, ← sub_eq_add_neg] at h2
    linarith
  calc |M + Bz - By| ≤ |M| + |Bz| + |By| := htri
    _ ≤ (B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)))
        + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [hmid, hbz, hby]
    _ ≤ 7 * B / Real.sqrt y := by
        have hstep : B * (1 / ((y:ℝ) + 1)) ≤ B * (1 / Real.sqrt y) :=
          mul_le_mul_of_nonneg_left hy1r hB
        have hexp : B * (2 / Real.sqrt y) = 2 * B / Real.sqrt y := by ring
        have hexp2 : B * (1 / Real.sqrt y) = B / Real.sqrt y := by ring
        have hexp3 : 7 * B / Real.sqrt y = 7 * (B / Real.sqrt y) := by ring
        have hexp4 : 2 * B / Real.sqrt y = 2 * (B / Real.sqrt y) := by ring
        linarith [hstep, hexp, hexp2, hexp3, hexp4]

/-- **The k-side mean exists with √-rate** (Siegel brick A2e-ii): with `|K(t)| ≤ B(√t+1)`,
    `S_y = Σ_{d≤y} k(d)/d` converges to some `Lk` with `|Lk − S_y| ≤ 7B/√y` for `y ≥ 1` —
    the abstract `L(1,χ₂)L(1,χ₁χ₂)` of the hyperbola main term. -/
theorem sqrt_mean_exists (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1)) :
    ∃ Lk : ℝ, ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, k d / d| ≤ 7 * B / Real.sqrt y := by
  have hB : 0 ≤ B := by
    have h0 := hK 0
    simp at h0
    linarith [abs_nonneg (∑ n ∈ Icc 1 0, k n), h0]
  set S : ℕ → ℝ := fun y => ∑ d ∈ Icc 1 y, k d / d with hS
  have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
    intro a b
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hdiff : ∀ y z : ℕ, 1 ≤ y → y ≤ z → |S z - S y| ≤ 7 * B / Real.sqrt y := by
    intro y z hy1 hyz
    have hsplit : S z - S y = ∑ d ∈ Icc (y + 1) z, k d / d := by
      rw [hS]
      simp only
      rw [← hIcoIcc 1 z,
        ← Finset.sum_Ico_consecutive (fun d => k d / d)
          (by omega : 1 ≤ y + 1) (by omega : y + 1 ≤ z + 1),
        hIcoIcc 1 y, hIcoIcc (y + 1) z, add_sub_cancel_left]
    rw [hsplit]
    exact abel_tail_sqrt k B hK y z hy1 hyz
  -- work with the shifted sequence T n = S (n+1): indices always ≥ 1
  set T : ℕ → ℝ := fun n => S (n + 1) with hT
  have hb0 : Filter.Tendsto (fun N : ℕ => 7 * B / Real.sqrt ((N:ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => Real.sqrt ((N:ℝ) + 1))
        Filter.atTop Filter.atTop := by
      apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    have h2 := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := 7 * B)) h1
    simpa using h2
  have hcauchy : CauchySeq T := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 7 * B / Real.sqrt ((N:ℝ) + 1)) _ hb0
    intro n m N hn hm
    rw [Real.dist_eq]
    have hkey : ∀ u v : ℕ, u ≤ v → N ≤ u →
        |T v - T u| ≤ 7 * B / Real.sqrt ((N:ℝ) + 1) := by
      intro u v huv hNu
      calc |T v - T u| = |S (v + 1) - S (u + 1)| := by rw [hT]
        _ ≤ 7 * B / Real.sqrt ((u:ℝ) + 1) := by
            have h := hdiff (u + 1) (v + 1) (by omega) (by omega)
            have hc : ((u + 1 : ℕ) : ℝ) = (u : ℝ) + 1 := by push_cast; ring
            rwa [hc] at h
        _ ≤ 7 * B / Real.sqrt ((N:ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            apply Real.sqrt_le_sqrt
            have : (N:ℝ) ≤ (u:ℝ) := by exact_mod_cast hNu
            linarith
    rcases le_total n m with h | h
    · rw [abs_sub_comm]
      exact hkey n m h hn
    · exact hkey m n h hm
  obtain ⟨Lk, hLk⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨Lk, ?_⟩
  intro y hy1
  have htend : Filter.Tendsto (fun z : ℕ => |T z - S y|) Filter.atTop
      (nhds (|Lk - S y|)) := by
    apply Filter.Tendsto.abs
    exact Filter.Tendsto.sub_const hLk (S y)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop y] with z hz
  calc |T z - S y| = |S (z + 1) - S y| := by rw [hT]
    _ ≤ 7 * B / Real.sqrt y := hdiff y (z + 1) hy1 (by omega)

/-- Convolution values are divisor-counted (Siegel brick A2e-iii-a1): for 1-bounded
    inputs, `|(k₁⋆k₂)(n)| ≤ τ(n)` where `τ(n) = #divisorsAntidiagonal(n)`. -/
lemma conv_value_le_tau (k₁ k₂ : ℕ → ℝ) (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (n : ℕ) :
    |(toArith k₁ * toArith k₂) n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
  rw [ArithmeticFunction.mul_apply]
  calc |∑ p ∈ n.divisorsAntidiagonal, toArith k₁ p.1 * toArith k₂ p.2|
      ≤ ∑ p ∈ n.divisorsAntidiagonal, |toArith k₁ p.1 * toArith k₂ p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        have h1 : |toArith k₁ p.1| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.1 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₁ p.1 = k₁ p.1 from by simp [toArith, h0.ne']]
            exact h1b p.1
        have h2 : |toArith k₂ p.2| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.2 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₂ p.2 = k₂ p.2 from by simp [toArith, h0.ne']]
            exact h2b p.2
        calc |toArith k₁ p.1| * |toArith k₂ p.2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = ((n.divisorsAntidiagonal).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Fiberwise unfolding: divisor-pair sums over `d ≤ y` are hyperbola-set sums
    (Siegel brick A2e-iii-a2). -/
lemma sum_divA_eq_hypSet (y : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ d ∈ Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p
      = ∑ p ∈ (Ioc 0 y ×ˢ Ioc 0 y).filter (fun p => p.1 * p.2 ≤ y), F p := by
  have hL : ∑ d ∈ Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p
      = ∑ d ∈ Icc 1 y, ∑ p ∈ (Ioc 0 y ×ˢ Ioc 0 y).filter (fun x => x.1 * x.2 = d), F p := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by omega) hdy]
  rw [hL, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hp.1.1 hp.2.1).ne', h⟩

/-- **τ partial sums** (Siegel brick A2e-iii-a3): `Σ_{d≤y} τ(d) ≤ y(1 + log y)`. -/
lemma sum_tau_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) ≤ (y : ℝ) * (1 + Real.log y) := by
  have hcard : ∀ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ)
      = ∑ p ∈ d.divisorsAntidiagonal, (1 : ℝ) := by
    intro d _
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hcard, sum_divA_eq_hypSet, sum_hypSet_eq_rows]
  have hrow : ∀ d ∈ Icc 1 y, ∑ e ∈ Icc 1 (y / d), (1:ℝ) ≤ (y : ℝ) * (1 / d) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
    have h1 : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / d := Nat.cast_div_le
    rw [mul_one_div]
    exact h1
  calc ∑ d ∈ Icc 1 y, ∑ e ∈ Icc 1 (y / d), (1:ℝ)
      ≤ ∑ d ∈ Icc 1 y, (y : ℝ) * (1 / d) := Finset.sum_le_sum hrow
    _ = (y : ℝ) * ∑ d ∈ Icc 1 y, (1 : ℝ) / d := by rw [← Finset.mul_sum]
    _ ≤ (y : ℝ) * (1 + Real.log y) := by
        apply mul_le_mul_of_nonneg_left (sum_one_div_le_log y hy) (by positivity)

/-- **τ/√ partial sums** (Siegel brick A2e-iii-a4):
    `Σ_{d≤y} τ(d)/√d ≤ 2√y(1 + log y)` — on each antidiagonal `p₁p₂ = d`. -/
lemma sum_tau_div_sqrt_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      ≤ 2 * Real.sqrt y * (1 + Real.log y) := by
  have hstep : ∀ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      = ∑ p ∈ d.divisorsAntidiagonal, (1 : ℝ) / Real.sqrt (p.1 * p.2) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hterm : ∀ p ∈ d.divisorsAntidiagonal, (1 : ℝ) / Real.sqrt (p.1 * p.2)
        = (1 : ℝ) / Real.sqrt d := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [show ((p.1 : ℝ) * (p.2 : ℝ)) = ((d : ℕ) : ℝ) from by exact_mod_cast hp.1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [Finset.sum_congr rfl hstep, sum_divA_eq_hypSet]
  exact sum_hypSet_inv_sqrt_le y hy

/-- **The Goldfeld coefficient asymptotic** (Siegel brick A2e-iii, the analytic capstone
    of A2): with `h := 1⋆g₁` carrying the mean `L₁` and `k := g₂⋆(g₁g₂)` carrying the
    mean `Lk` (√-bounded partial sums `≤ B(√t+1)`),
    `|Σ_{n≤N} a(n) − L₁·Lk·N| ≤ 30(1+q₁)(1+B)·√N·√√N·(1+log N)` for `N ≥ 4` —
    the `A(x) = λx + O(Q^c x^{3/4+ε})` input of Goldfeld's lemma, with
    `λ = L₁·Lk` and the split at `y = ⌊√N⌋`. -/
theorem quad_coeff_asymptotic (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y)
    (N : ℕ) (hN : 4 ≤ N) :
    |∑ n ∈ Icc 1 N, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n - L₁ * Lk * N|
      ≤ 30 * (1 + q₁) * (1 + B)
        * (Real.sqrt N * Real.sqrt (Real.sqrt N) * (1 + Real.log N)) := by
  have hB : 0 ≤ B := by
    have h0 := hKb 0
    rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, abs_zero, Nat.cast_zero, Real.sqrt_zero] at h0
    linarith
  have hN1 : 1 ≤ N := by omega
  have hNr : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- names
  set h : ArithmeticFunction ℝ := toArith (fun _ => (1:ℝ)) * toArith g₁ with hh
  set k : ArithmeticFunction ℝ := toArith g₂ * toArith (fun m => g₁ m * g₂ m) with hk
  have hregroup : toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m) = k * h := by
    rw [hh, hk, mul_assoc]
    exact mul_comm _ _
  rw [hregroup]
  set y : ℕ := Nat.sqrt N with hy
  have hy2 : 2 ≤ y := by
    rw [hy]
    exact Nat.le_sqrt.mpr (by omega)
  have hy1 : 1 ≤ y := by omega
  have hyN : y ≤ N := Nat.sqrt_le_self N
  rw [hyperbola_identity k h N y hyN]
  -- ===== √-conversions =====
  have hsN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsqN : Real.sqrt N * Real.sqrt N = (N:ℝ) := Real.mul_self_sqrt (by linarith)
  have hssN : (0:ℝ) < Real.sqrt (Real.sqrt N) := Real.sqrt_pos.mpr hsN
  have hsqsN : Real.sqrt (Real.sqrt N) * Real.sqrt (Real.sqrt N) = Real.sqrt N :=
    Real.mul_self_sqrt hsN.le
  have hyle : (y : ℝ) ≤ Real.sqrt N := by
    rw [hy]
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
  have hsyle : Real.sqrt y ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt hyle
  have hy1r : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  -- √N ≤ 2y (from ⌊√N⌋ ≥ √N − 1 ≥ √N/2 for N ≥ 4)
  have h2y : Real.sqrt N ≤ 2 * (y : ℝ) := by
    have hlt := Nat.lt_succ_sqrt' N
    have hcast : (N : ℝ) < ((y : ℝ) + 1) ^ 2 := by
      rw [hy]
      push_cast
      exact_mod_cast hlt
    have hsylt : Real.sqrt N < (y:ℝ) + 1 := by
      nlinarith [hcast, hsqN, hsN]
    linarith [hy1r]
  -- N/√y ≤ √2·√N·√√N — via √y ≥ √√N/√2, i.e. 2y ≥ √N → √(2y) ≥ √√N
  have hNdivsy : (N:ℝ) / Real.sqrt y ≤ 2 * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by
    rw [div_le_iff₀ hsy]
    -- √√N ≤ √(2y) = √2·√y, then N = (√N√√N)·√√N ≤ (√N√√N)·√2√y ≤ 2(√N√√N)√y
    have h1 : Real.sqrt (Real.sqrt N) ≤ Real.sqrt 2 * Real.sqrt y := by
      calc Real.sqrt (Real.sqrt N) ≤ Real.sqrt (2 * y) := Real.sqrt_le_sqrt (by
            push_cast
            linarith [h2y])
        _ = Real.sqrt 2 * Real.sqrt y := Real.sqrt_mul (by norm_num) _
    have hs2le : Real.sqrt 2 ≤ 2 := by
      have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have hss1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt N) := by
      apply Real.one_le_sqrt.mpr
      have h2s : (2:ℝ) ≤ Real.sqrt N := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      linarith
    have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg hsN.le hssN.le)
    nlinarith [hmul, hsqN, hsqsN, hs2le,
      mul_nonneg (mul_nonneg hsN.le hssN.le) hsy.le]
  -- ===== value bounds =====
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hkτ : ∀ n, |k n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
    intro n
    rw [hk]
    exact conv_value_le_tau g₂ (fun m => g₁ m * g₂ m) h2b hg12b n
  have hhτ : ∀ n, |h n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
    intro n
    rw [hh]
    exact conv_value_le_tau (fun _ => (1:ℝ)) g₁ honeb h1b n
  have hL1b : |L₁| ≤ 1 + q₁ := by
    have h1 := hL₁ 1
    have hS1 : ∑ d ∈ Icc 1 1, g₁ d / d = g₁ 1 := by
      rw [show (Icc 1 1 : Finset ℕ) = {1} from rfl, Finset.sum_singleton]
      norm_num
    rw [hS1] at h1
    have habs := abs_add_le (L₁ - g₁ 1) (g₁ 1)
    simp only [sub_add_cancel] at habs
    have hc : ((1:ℕ):ℝ) + 1 = 2 := by norm_num
    rw [hc] at h1
    have hq2 : 2 * q₁ / 2 = q₁ := by ring
    linarith [habs, h1, h1b 1, hq2.le, hq2.ge]
  -- ===== M' facts =====
  set M' : ℕ := N / (y + 1) with hM'
  have hyy : y * y ≤ N := by
    have h := Nat.sqrt_le' N
    rw [pow_two] at h
    rw [hy]
    exact h
  have hyN2 : y + 1 ≤ N := by nlinarith [hy2, hyy]
  have hM'1 : 1 ≤ M' := by
    rw [hM', Nat.le_div_iff_mul_le (by omega : 0 < y + 1)]
    omega
  have hM'le : (M' : ℝ) ≤ Real.sqrt N := by
    have h1 : ((M' : ℕ) : ℝ) ≤ (N : ℝ) / ((y:ℝ) + 1) := by
      rw [hM']
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := y + 1)
      push_cast at this
      exact this
    have hylt : Real.sqrt N < (y:ℝ) + 1 := by
      have hlt := Nat.lt_succ_sqrt' N
      have hcast : (N : ℝ) < ((y : ℝ) + 1) ^ 2 := by
        rw [hy]
        push_cast
        exact_mod_cast hlt
      nlinarith [hsqN, hsN]
    have h2 : (N : ℝ) / ((y:ℝ) + 1) ≤ Real.sqrt N := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hsqN, hylt, hsN]
    linarith
  have hsM'le : Real.sqrt M' ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt hM'le
  have hlogy : Real.log y ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hy1 : (0:ℝ) < (y:ℝ))
    exact_mod_cast hyN
  have hlogM' : Real.log M' ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hM'1 : (0:ℝ) < (M':ℝ))
    have : M' ≤ N := Nat.div_le_self N (y + 1)
    exact_mod_cast this
  have hlogN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogy1 : 1 + Real.log y ≤ 1 + Real.log N := by linarith
  have hlogy0 : (0:ℝ) ≤ 1 + Real.log y := by
    have := Real.log_nonneg (by exact_mod_cast hy1 : (1:ℝ) ≤ (y:ℝ))
    linarith
  have hlogM'0 : (0:ℝ) ≤ 1 + Real.log M' := by
    have := Real.log_nonneg (by exact_mod_cast hM'1 : (1:ℝ) ≤ (M':ℝ))
    linarith
  have hlogM'1 : 1 + Real.log M' ≤ 1 + Real.log N := by linarith
  have hsqrtdiv : ∀ d : ℕ, 1 ≤ d → Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt d := by
    intro d hd1
    calc Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / d) :=
          Real.sqrt_le_sqrt Nat.cast_div_le
      _ = Real.sqrt N / Real.sqrt d := Real.sqrt_div (Nat.cast_nonneg N) d
  -- ===== HEAD =====
  set Sk : ℝ := ∑ d ∈ Icc 1 y, k d / d with hSk
  have hSkLk : |Lk - Sk| ≤ 7 * B / Real.sqrt y := by
    rw [hSk, hk]
    exact hLk y hy1
  have hhead_eq : ∑ d ∈ Icc 1 y, k d * (∑ e ∈ Icc 1 (N / d), h e)
      = L₁ * (∑ d ∈ Icc 1 y, k d * ((N / d : ℕ) : ℝ))
        + ∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hfloor_eq : ∑ d ∈ Icc 1 y, k d * ((N / d : ℕ) : ℝ)
      = (N : ℝ) * Sk - ∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    rw [hSk, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : ((d:ℝ)) ≠ 0 := by
      have : (0:ℝ) < d := by exact_mod_cast hd1
      linarith
    field_simp
    ring
  have hfrac_le : |∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
      ≤ (y:ℝ) * (1 + Real.log y) := by
    calc |∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
          rw [abs_mul]
          have hfr0 : (0:ℝ) ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) := by
            rw [sub_nonneg]
            exact Nat.cast_div_le
          have hfr1 : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
            have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hd0]
              have hnat : N < (N / d + 1) * d := by
                have hexp : (N / d + 1) * d = d * (N / d) + d := by ring
                rw [hexp]
                have h1 := Nat.div_add_mod N d
                have h2 := Nat.mod_lt N (show 0 < d by omega)
                omega
              exact_mod_cast hnat
            linarith
          rw [abs_of_nonneg hfr0]
          have hτ1 : (1:ℝ) ≤ ((d.divisorsAntidiagonal).card : ℝ) := by
            have hmem : ((1:ℕ), d) ∈ d.divisorsAntidiagonal := by
              rw [Nat.mem_divisorsAntidiagonal]
              exact ⟨one_mul d, by omega⟩
            have hpos : 0 < (d.divisorsAntidiagonal).card := Finset.card_pos.mpr ⟨_, hmem⟩
            exact_mod_cast hpos
          nlinarith [hkτ d, hfr0, hfr1, abs_nonneg (k d), hτ1]
      _ ≤ (y:ℝ) * (1 + Real.log y) := sum_tau_le y hy1
  have hε_le : |∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
      ≤ (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
          + 2 * (y:ℝ) * (1 + Real.log y)) := by
    have hterm : ∀ d ∈ Icc 1 y, |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
        ≤ (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt d)
            + ((d.divisorsAntidiagonal).card : ℝ)) := by
      intro d hd
      obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
      have hNd1 : 1 ≤ N / d := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
        have : d ≤ N := le_trans hdy hyN
        omega
      have hεd := hH (N / d) hNd1
      have hq4 : (0:ℝ) ≤ 1 + 4 * q₁ := by linarith
      rw [show |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
          = |k d| * |(∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)| from abs_mul _ _]
      calc |k d| * |(∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)|
          ≤ ((d.divisorsAntidiagonal).card : ℝ)
            * ((1 + 4 * q₁) * (Real.sqrt ((N / d : ℕ) : ℝ) + 1)) :=
            mul_le_mul (hkτ d) hεd (abs_nonneg _) (Nat.cast_nonneg _)
        _ ≤ ((d.divisorsAntidiagonal).card : ℝ)
            * ((1 + 4 * q₁) * (Real.sqrt N / Real.sqrt d + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hq4
            linarith [hsqrtdiv d hd1]
        _ = (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt d)
            + ((d.divisorsAntidiagonal).card : ℝ)) := by ring
    calc |∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ)
            * (Real.sqrt N / Real.sqrt d) + ((d.divisorsAntidiagonal).card : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ (1 + 4 * q₁) * (Real.sqrt N * (2 * Real.sqrt y * (1 + Real.log y))
            + (y:ℝ) * (1 + Real.log y)) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hsplit : ∑ d ∈ Icc 1 y, (((d.divisorsAntidiagonal).card : ℝ)
              * (Real.sqrt N / Real.sqrt d) + ((d.divisorsAntidiagonal).card : ℝ))
              = Real.sqrt N * (∑ d ∈ Icc 1 y,
                  ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d)
                + ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro d _
            ring
          rw [hsplit]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_tau_div_sqrt_le y hy1) hsN.le)
            (sum_tau_le y hy1)
      _ ≤ (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hy0' : (0:ℝ) ≤ (y:ℝ) := by positivity
          nlinarith [hlogy0, hy0']
  -- ===== TAIL =====
  have htail_le : |∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
      ≤ 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
          + 2 * (M':ℝ) * (1 + Real.log M')) := by
    have hterm : ∀ e ∈ Icc 1 M', |h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
        ≤ 2 * B * (((e.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt e)
            + ((e.divisorsAntidiagonal).card : ℝ)) := by
      intro e he
      obtain ⟨he1, heM⟩ := Finset.mem_Icc.mp he
      have hyNe : y ≤ N / e := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < e)]
        have h1 : e * (y + 1) ≤ N := by
          rw [hM'] at heM
          have := (Nat.le_div_iff_mul_le (by omega : 0 < y + 1)).mp heM
          omega
        nlinarith [h1]
      have hKdiff : |(∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d|
          ≤ 2 * B * (Real.sqrt ((N / e : ℕ) : ℝ) + 1) := by
        have h1 := hKb (N / e)
        have h2 := hKb y
        have hsymono : Real.sqrt ((y:ℕ) : ℝ) ≤ Real.sqrt ((N / e : ℕ) : ℝ) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hyNe
        have htri := abs_add_le (∑ d ∈ Icc 1 (N / e), k d) (-(∑ d ∈ Icc 1 y, k d))
        rw [abs_neg, ← sub_eq_add_neg] at htri
        have hprod := mul_le_mul_of_nonneg_left hsymono hB
        linarith [htri, h1, h2, hprod]
      rw [abs_mul]
      have hB2 : (0:ℝ) ≤ 2 * B := by linarith
      calc |h e| * |(∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d|
          ≤ ((e.divisorsAntidiagonal).card : ℝ)
            * (2 * B * (Real.sqrt ((N / e : ℕ) : ℝ) + 1)) :=
            mul_le_mul (hhτ e) hKdiff (abs_nonneg _) (Nat.cast_nonneg _)
        _ ≤ ((e.divisorsAntidiagonal).card : ℝ)
            * (2 * B * (Real.sqrt N / Real.sqrt e + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hB2
            linarith [hsqrtdiv e he1]
        _ = 2 * B * (((e.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt e)
            + ((e.divisorsAntidiagonal).card : ℝ)) := by ring
    calc |∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
        ≤ ∑ e ∈ Icc 1 M', |h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 M', 2 * B * (((e.divisorsAntidiagonal).card : ℝ)
            * (Real.sqrt N / Real.sqrt e) + ((e.divisorsAntidiagonal).card : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ 2 * B * (Real.sqrt N * (2 * Real.sqrt M' * (1 + Real.log M'))
            + (M':ℝ) * (1 + Real.log M')) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hsplit : ∑ e ∈ Icc 1 M', (((e.divisorsAntidiagonal).card : ℝ)
              * (Real.sqrt N / Real.sqrt e) + ((e.divisorsAntidiagonal).card : ℝ))
              = Real.sqrt N * (∑ e ∈ Icc 1 M',
                  ((e.divisorsAntidiagonal).card : ℝ) / Real.sqrt e)
                + ∑ e ∈ Icc 1 M', ((e.divisorsAntidiagonal).card : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro e _
            ring
          rw [hsplit]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_tau_div_sqrt_le M' hM'1) hsN.le)
            (sum_tau_le M' hM'1)
      _ ≤ 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hM'0 : (0:ℝ) ≤ (M':ℝ) := by positivity
          nlinarith [hlogM'0, hM'0]
  -- ===== ASSEMBLE =====
  rw [hhead_eq, hfloor_eq]
  set FR := ∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hFRd
  set T2 := ∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)) with hT2d
  set TL := ∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d) with hTLd
  have hrw : L₁ * ((N : ℝ) * Sk - FR) + T2 + TL - L₁ * Lk * N
      = -(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL := by ring
  rw [hrw]
  have hb1 : |L₁ * ((N:ℝ) * (Lk - Sk))|
      ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N))) := by
    rw [abs_mul, abs_mul]
    have hNpos : (0:ℝ) ≤ (N:ℝ) := by positivity
    have h1 : |(N:ℝ)| * |Lk - Sk| ≤ (N:ℝ) * (7 * B / Real.sqrt y) := by
      rw [abs_of_nonneg hNpos]
      exact mul_le_mul_of_nonneg_left hSkLk hNpos
    have h3 : (N:ℝ) * (7 * B / Real.sqrt y)
        ≤ 14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by
      have h2 : (N:ℝ) * (7 * B / Real.sqrt y) = 7 * B * ((N:ℝ) / Real.sqrt y) := by ring
      rw [h2]
      calc 7 * B * ((N:ℝ) / Real.sqrt y)
          ≤ 7 * B * (2 * (Real.sqrt N * Real.sqrt (Real.sqrt N))) :=
            mul_le_mul_of_nonneg_left hNdivsy (by linarith)
        _ = 14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by ring
    calc |L₁| * (|(N:ℝ)| * |Lk - Sk|) ≤ (1 + q₁) * (|(N:ℝ)| * |Lk - Sk|) :=
        mul_le_mul_of_nonneg_right hL1b (by positivity)
      _ ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith [h1, h3]
  have hb2 : |L₁ * FR| ≤ (1 + q₁) * ((y:ℝ) * (1 + Real.log y)) := by
    rw [abs_mul]
    apply mul_le_mul hL1b hfrac_le (abs_nonneg _) (by linarith)
  have htri4 : |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
      ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := by
    have t1 := abs_add_le (-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) T2
    have t2 := abs_add_le ((-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) + T2) TL
    have t3 := abs_add_le (-(L₁ * ((N:ℝ) * (Lk - Sk)))) (-(L₁ * FR))
    rw [abs_neg, abs_neg, ← sub_eq_add_neg] at t3
    calc |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
        ≤ |(-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) + T2| + |TL| := t2
      _ ≤ |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR| + |T2| + |TL| := by linarith [t1]
      _ ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := by linarith [t3]
  set U := Real.sqrt N * Real.sqrt (Real.sqrt N) * (1 + Real.log N) with hUd
  have hlogNfac : (1:ℝ) ≤ 1 + Real.log N := by linarith
  have hU0 : (0:ℝ) < U := by
    rw [hUd]
    have : (0:ℝ) < 1 + Real.log N := by linarith
    positivity
  have hss1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt N) := by
    apply Real.one_le_sqrt.mpr
    apply Real.one_le_sqrt.mpr
    linarith
  have hu1 : Real.sqrt N * Real.sqrt (Real.sqrt N) ≤ U := by
    rw [hUd]
    nlinarith [mul_nonneg hsN.le hssN.le, hlogNfac]
  have hu2 : (y:ℝ) * (1 + Real.log y) ≤ U := by
    rw [hUd]
    have h1 : (y:ℝ) * (1 + Real.log y) ≤ Real.sqrt N * (1 + Real.log N) :=
      mul_le_mul hyle hlogy1 hlogy0 hsN.le
    nlinarith [hss1, hsN.le, hlogNfac, h1]
  have hu3 : 2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
      + 2 * (y:ℝ) * (1 + Real.log y) ≤ 4 * U := by
    have h1 : Real.sqrt N * Real.sqrt y * (1 + Real.log y) ≤ U := by
      rw [hUd]
      have h2 : Real.sqrt N * Real.sqrt y ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsyle hsN.le
      apply mul_le_mul h2 hlogy1 hlogy0 (by positivity)
    linarith [hu2]
  have hu4 : 2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
      + 2 * (M':ℝ) * (1 + Real.log M') ≤ 4 * U := by
    have h1 : Real.sqrt N * Real.sqrt M' * (1 + Real.log M') ≤ U := by
      rw [hUd]
      have h2 : Real.sqrt N * Real.sqrt M' ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsM'le hsN.le
      apply mul_le_mul h2 hlogM'1 hlogM'0 (by positivity)
    have h2 : (M':ℝ) * (1 + Real.log M') ≤ U := by
      rw [hUd]
      have hM'N : (M':ℝ) * (1 + Real.log M') ≤ Real.sqrt N * (1 + Real.log N) :=
        mul_le_mul hM'le hlogM'1 hlogM'0 hsN.le
      nlinarith [hss1, hsN.le, hlogNfac, hM'N]
    linarith
  calc |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
      ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := htri4
    _ ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)))
        + (1 + q₁) * ((y:ℝ) * (1 + Real.log y))
        + (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y))
        + 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) := by
        linarith [hb1, hb2, hε_le, htail_le]
    _ ≤ (1 + q₁) * (14 * B * U) + (1 + q₁) * U + (1 + 4 * q₁) * (4 * U)
        + 2 * B * (4 * U) := by
        have c1 : (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)))
            ≤ (1 + q₁) * (14 * B * U) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hu1 (by linarith)
        have c2 : (1 + q₁) * ((y:ℝ) * (1 + Real.log y)) ≤ (1 + q₁) * U :=
          mul_le_mul_of_nonneg_left hu2 (by linarith)
        have c3 : (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y)) ≤ (1 + 4 * q₁) * (4 * U) :=
          mul_le_mul_of_nonneg_left hu3 (by linarith)
        have c4 : 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) ≤ 2 * B * (4 * U) :=
          mul_le_mul_of_nonneg_left hu4 (by linarith)
        linarith [c1, c2, c3, c4]
    _ ≤ 30 * (1 + q₁) * (1 + B) * U := by
        nlinarith [hU0.le, hq₁, hB, mul_nonneg hq₁ hB,
          mul_nonneg (mul_nonneg hq₁ hB) hU0.le,
          mul_nonneg hq₁ hU0.le, mul_nonneg hB hU0.le]

/-- The ℂ-cast of a packaged real function. -/
noncomputable def castFn (g : ℕ → ℝ) : ℕ → ℂ := fun n => ((toArith g n : ℝ) : ℂ)

lemma castFn_zero (g : ℕ → ℝ) : castFn g 0 = 0 := by
  simp [castFn, toArith]

lemma castFn_bound (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (n : ℕ) : ‖castFn g n‖ ≤ 1 := by
  rw [castFn, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · simp [toArith]
  · rw [show toArith g n = g n from by simp [toArith, h0.ne']]
    exact hg n

open scoped LSeries.notation in
/-- **Casting commutes with Dirichlet convolution** (Siegel brick A2f-i):
    the ℂ-cast of the `ArithmeticFunction` product is the `⍟`-convolution of the casts. -/
lemma castFn_conv (u v : ℕ → ℝ) (n : ℕ) :
    (((toArith u * toArith v) n : ℝ) : ℂ) = (castFn u ⍟ castFn v) n := by
  rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have h1 : p.1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hp
    exact hp.2 hp.1.symm
  have h2 : p.2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hp
    exact hp.2 hp.1.symm
  rw [castFn, castFn]

/-- **Summability of bounded packaged series** (Siegel brick A2f-ii): `Re s > 1`. -/
lemma castFn_summable (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (castFn g) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => castFn_bound g hg n) hs

open scoped LSeries.notation in
/-- **The Goldfeld product identity** (Siegel brick A2f-iii): on `Re s > 1`, the
    L-series of the quadruple coefficient sequence factors as the product of the four
    L-series — the series side of `F(s) = ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)`. -/
theorem quad_LSeries_eq (g₁ g₂ : ℕ → ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)) s
      = LSeries (castFn (fun _ => (1:ℝ))) s * LSeries (castFn g₁) s
        * LSeries (castFn g₂) s * LSeries (castFn (fun m => g₁ m * g₂ m)) s := by
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hS0 := castFn_summable (fun _ => (1:ℝ)) honeb hs
  have hS1 := castFn_summable g₁ h1b hs
  have hS2 := castFn_summable g₂ h2b hs
  have hS12 := castFn_summable (fun m => g₁ m * g₂ m) hg12b hs
  -- rewrite the coefficient function through the cast bridge, twice-nested
  have hbridge : (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ))
      = ((castFn (fun _ => (1:ℝ)) ⍟ castFn g₁) ⍟ castFn g₂)
        ⍟ castFn (fun m => g₁ m * g₂ m) := by
    funext n
    -- peel the outermost product
    have step1 : (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)
        = ((fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
          ⍟ castFn (fun m => g₁ m * g₂ m)) n := by
      rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h2 : p.2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hp
        exact hp.2 hp.1.symm
      rw [castFn]
    rw [step1]
    -- peel the middle product inside the left slot
    have step2 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
        = (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ)) ⍟ castFn g₂ := by
      funext m
      rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h2 : p.2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hp
        exact hp.2 hp.1.symm
      rw [castFn]
    rw [step2]
    -- peel the innermost product
    have step3 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ))
        = castFn (fun _ => (1:ℝ)) ⍟ castFn g₁ := by
      funext m
      exact castFn_conv (fun _ => (1:ℝ)) g₁ m
    rw [step3]
  rw [hbridge]
  -- three applications of the convolution identity
  rw [LSeries_convolution' ((hS0.convolution hS1).convolution hS2) hS12,
    LSeries_convolution' (hS0.convolution hS1) hS2,
    LSeries_convolution' hS0 hS1]

/-- **ℂ-weighted Abel summation over an initial window** (Siegel brick A2g-i):
    `Σ_{n≤x} a(n)w(n) = A(x)w(x) + Σ_{n<x} A(n)(w(n) − w(n+1))` with
    `A(t) = Σ_{n≤t} a(n)` — the discrete engine of the integral representation,
    for arbitrary complex weights `w`. -/
lemma abel_initial (a : ℕ → ℂ) (w : ℕ → ℂ) :
    ∀ x : ℕ, 1 ≤ x →
    ∑ n ∈ Icc 1 x, a n * w n
      = (∑ n ∈ Icc 1 x, a n) * w x
        + ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
  intro x
  induction x with
  | zero =>
    intro h0
    omega
  | succ p ih =>
    intro _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · -- x = 1
      simp
    · -- step p → p+1
      have hstepL : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hp1 : p + 1 - 1 = p := by omega
      rw [hstepL, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih hp, hp1]
      have hstepW : Icc 1 p = insert p (Icc 1 (p - 1)) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [show ∑ n ∈ Icc 1 p, (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
          = (∑ m ∈ Icc 1 p, a m) * (w p - w (p + 1))
            + ∑ n ∈ Icc 1 (p - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) from by
        rw [hstepW, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), ← hstepW]]
      ring

end Principia.Common.SW
