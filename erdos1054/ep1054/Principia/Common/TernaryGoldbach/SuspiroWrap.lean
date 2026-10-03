/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnWrap

set_option autoImplicit false

/-!
# `HX.SuspiroBig` PROVED from Rosser–Schoenfeld: only RS75 (5.1) stays named

`lem:suspiro` beyond its computed range (`ternvin.tex` 2738-2757) is an argument, not a
computation. Here it is proved from two literature statements, both CITED THEOREMS rather than
arguments:

* **RS62 (3.42)** = `GS.RS62Thm15` (`n/φ(n) < e^γ log log n + 2.50637/log log n`, `n ≥ 3`),
  which the EP1054 headline ALREADY carries as a binder;
* **RS75 (5.1)** = `RS75Theta` (`θ(n) ≤ 1.001102n`), named here, the one new input.

## The proof (`suspiroBig_of`)

With `𝒫 = ∏_{p ∣ q ∨ p ≤ m} p`, `X = m + log q > 8.53`:

* `log 𝒫 ≤ log q + θ(m) ≤ 1.001102X` (`log_prodP_le`), so `u = log log 𝒫 ≤ log X + 0.001102`;
* **`𝒫 ≥ 27`**: RS62 at `n = 𝒫`, and `t ↦ e^γt + b/t` is non-decreasing from `u` to
  `U = log X + 0.001102` because `uU ≥ u² ≥ 1.1864² ≥ b/e^γ` (`u ≥ 1.1864` from `log 27 ≥ 3.28 ≥
  e^{1.1864}`); then `b/U ≤ b/log X ≤ 0.656608e^γ` since `log X ≥ log 8.53 ≥ 2.14358` and
  `e^γ ≥ 1.7808`: `0.656608·1.7808·2.14358 = 2.50646 ≥ 2.50637`;
* **`𝒫 < 27`** — a case the printed argument does not treat (it needs `x ≥ n ≥ 27` for (3.42)):
  `n ≤ 3φ(n)` for every `1 ≤ n < 27` (`decide`), and the right side is `≥ 1.7808·2.80129 > 3`.

## `γ ≥ 0.5771`, new here

The margin above needs `e^γ ≥ 1.78075`, sharper than anything in the library (`CELower.gamma_ge`
gives `0.55209`). `d_k = H_k − log k − 1/(2k)` is non-decreasing — `log(1 + 1/k) ≤ 1/(2k) +
1/(2(k+1))`, by comparing `Real.hasSum_log_one_add_inv` termwise with the geometric series — and
tends to `γ`, so `γ ≥ d_30 ≥ 0.57712` (`gamma_ge`), the lower companion of
`SmallRatio.gamma_le` (`γ ≤ 0.5772158`).
-/

namespace Principia.Common.TernaryGoldbach.HX

open Filter Topology

/-- **NAMED (literature) — Rosser–Schoenfeld 1975, (5.1)** (Math. Comp. 29, 243-269; quoted in
`ternvin.tex` 2741-2744 as `∑_{p ≤ m} log p ≤ (1 + ε₀)m`, `ε₀ = 0.001102`): `θ(n) ≤ 1.001102n`,
at the integers where it is consumed (RS75 states `θ(x) < 1.001102x` for all `x > 0`, which implies
this). A cited theorem, not a computation of Helfgott's: an owner question, like `GS.RS62Thm15`. -/
def RS75Theta : Prop := ∀ n : ℕ, Chebyshev.theta n ≤ 1.001102 * n

/-! ## (1) `γ ≥ 0.5771` -/

/-- **`log(1 + 1/a) ≤ 1/(2a) + 1/(2(a+1))`** for `a > 0`: the series
`∑ 2/(2k+1)·z^{2k+1}`, `z = 1/(2a+1)`, is termwise below `∑ 2z^{2k+1} = 2z/(1 − z²)`. -/
theorem log_one_add_inv_le (a : ℝ) (ha : 0 < a) :
    Real.log (1 + a⁻¹) ≤ 1 / (2 * a) + 1 / (2 * (a + 1)) := by
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / (2 * a + 1) := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := by
    rw [hz]
    positivity
  have hz1 : z < 1 := by
    rw [hz, div_lt_one (by positivity)]
    linarith
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ => 2 * z * (z ^ 2) ^ k) (2 * z * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left (2 * z)
  have hf := Real.hasSum_log_one_add_inv ha
  have hle : ∀ k : ℕ, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
      2 * z * (z ^ 2) ^ k := by
    intro k
    rw [← hz]
    have hk : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hp : 0 ≤ z ^ (2 * k + 1) := pow_nonneg hz0 _
    have e : 2 * z * (z ^ 2) ^ k = 2 * z ^ (2 * k + 1) := by
      rw [← pow_mul, pow_succ]
      ring
    rw [e]
    nlinarith
  have h := hasSum_le hle hf hg
  have ha0 : a ≠ 0 := ha.ne'
  have ha1 : a + 1 ≠ 0 := by positivity
  have ha2 : 2 * a + 1 ≠ 0 := by positivity
  have h1z : 1 - z ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
    rw [hz]
    field_simp
    ring
  have e2 : 2 * z * (1 - z ^ 2)⁻¹ = 1 / (2 * a) + 1 / (2 * (a + 1)) := by
    rw [h1z, hz]
    field_simp
    ring
  linarith

/-- `d_k = H_k − log k − 1/(2k)`. -/
noncomputable def dSeq (k : ℕ) : ℝ := Real.eulerMascheroniSeq' k - 1 / (2 * (k : ℝ))

/-- `d_k ≤ d_{k+1}` for `k ≥ 1`. -/
theorem dSeq_le_succ (k : ℕ) (hk : 1 ≤ k) : dSeq k ≤ dSeq (k + 1) := by
  have hk0 : k ≠ 0 := by omega
  have hy : (0 : ℝ) < k := by exact_mod_cast hk
  unfold dSeq Real.eulerMascheroniSeq'
  rw [if_neg (show k + 1 ≠ 0 by omega), if_neg hk0, harmonic_succ]
  push_cast
  have hlog : Real.log ((k : ℝ) + 1) = Real.log k + Real.log (1 + (k : ℝ)⁻¹) := by
    rw [← Real.log_mul hy.ne' (by positivity)]
    congr 1
    field_simp
  have hS := log_one_add_inv_le (k : ℝ) hy
  have e : ((k : ℝ) + 1)⁻¹ = 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) := by
    field_simp
    ring
  rw [hlog, e]
  linarith

/-- `1/(2x) → 0`. -/
theorem tendsto_half_inv : Tendsto (fun x : ℝ => 1 / (2 * x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (1 / 2) * x⁻¹) atTop (𝓝 ((1 / 2) * 0)) :=
    tendsto_inv_atTop_zero.const_mul _
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  ring

/-- **`d_k ≤ γ`** for `k ≥ 1`: `d` is non-decreasing from `k` on and tends to `γ`. -/
theorem dSeq_le_gamma (k : ℕ) (hk : 1 ≤ k) : dSeq k ≤ Real.eulerMascheroniConstant := by
  have hmono : Monotone (fun j : ℕ => dSeq (j + k)) := by
    refine monotone_nat_of_le_succ (fun j => ?_)
    have h := dSeq_le_succ (j + k) (by omega)
    rwa [show j + k + 1 = j + 1 + k by omega] at h
  have htend : Tendsto (fun j : ℕ => dSeq (j + k)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h1 : Tendsto (fun j : ℕ => Real.eulerMascheroniSeq' (j + k)) atTop
        (𝓝 Real.eulerMascheroniConstant) :=
      Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat k)
    have h2 : Tendsto (fun j : ℕ => 1 / (2 * ((j + k : ℕ) : ℝ))) atTop (𝓝 0) :=
      tendsto_half_inv.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k))
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3
  have h := hmono.ge_of_tendsto htend 0
  simpa using h

/-- `H₃₀`. -/
theorem harmonic_thirty : harmonic 30 = 9304682830147 / 2329089562800 := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `log 30 ≤ 3.4012` (`log 30 = 5 log 2 + log(1 − 1/16)`). -/
theorem log_thirty_le : Real.log 30 ≤ 3.4012 := by
  have hb := (Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 1 / 16)
    (by norm_num) (by norm_num) 4).1
  have h30 : Real.log 30 = 5 * Real.log 2 + Real.log (1 - 1 / 16) := by
    rw [show (30 : ℝ) = 2 ^ 5 * (1 - 1 / 16) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h30]
  norm_num at h2 ⊢
  linarith

/-- **`γ ≥ 0.5771`** (true value `0.5772156649…`), from `d₃₀ = H₃₀ − log 30 − 1/60`. -/
theorem gamma_ge : (0.5771 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := dSeq_le_gamma 30 (by norm_num)
  have hc : dSeq 30 = (9304682830147 / 2329089562800 : ℝ) - Real.log 30 - 1 / 60 := by
    unfold dSeq Real.eulerMascheroniSeq'
    rw [if_neg (show (30 : ℕ) ≠ 0 by norm_num), harmonic_thirty]
    norm_num
  have hl := log_thirty_le
  rw [hc] at h
  norm_num at h hl ⊢
  linarith

/-- **`e^γ ≥ 1.7808`** (true value `1.7810724…`). -/
theorem expG_ge : (1.7808 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  have h1 : Real.exp 0.5771 ≤ Real.exp Real.eulerMascheroniConstant := Real.exp_le_exp.2 gamma_ge
  have h2 := Real.sum_le_exp_of_nonneg (x := 0.5771) (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero] at h2
  norm_num at h2
  linarith

/-! ## (2) Logarithms -/

/-- `log 8.53 ≥ 2.14358` (`log 8.53 = 3 log 2 − log(1 − 53/853)`). -/
theorem log_853_ge : (2.14358 : ℝ) ≤ Real.log 8.53 := by
  have hb := (Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 53 / 853)
    (by norm_num) (by norm_num) 5).1
  have h853 : Real.log 8.53 = 3 * Real.log 2 - Real.log (1 - 53 / 853) := by
    rw [show (8.53 : ℝ) = 2 ^ 3 / (1 - 53 / 853) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h853]
  norm_num at h2 ⊢
  linarith

/-- `log 27 ≥ 3.28` (`log 3 = 2 log 2 + log(1 − 1/4)`). -/
theorem log_27_ge : (3.28 : ℝ) ≤ Real.log 27 := by
  have hb := (Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 1 / 4)
    (by norm_num) (by norm_num) 8).2
  have h27 : Real.log 27 = 3 * (2 * Real.log 2 + Real.log (1 - 1 / 4)) := by
    rw [show (27 : ℝ) = (2 ^ 2 * (1 - 1 / 4)) ^ 3 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h27]
  norm_num at h2 ⊢
  linarith

/-- `e^{1.1864} ≤ 3.28`. -/
theorem exp_11864_le : Real.exp 1.1864 ≤ 3.28 := by
  have hs : Real.exp 1.1864 = Real.exp 1 * Real.exp 0.1864 := by
    rw [← Real.exp_add]
    norm_num
  have he := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 0.1864) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero] at h2
  norm_num at h2
  rw [hs]
  have h0 : 0 < Real.exp 0.1864 := Real.exp_pos _
  nlinarith

/-! ## (3) `lem:suspiro` beyond `8.53` -/

/-- `n ≤ 3φ(n)` for `1 ≤ n < 27` (the maximum `3` is at `n = 6, 12, 18, 24`). -/
theorem le_three_totient : ∀ n : ℕ, n < 27 → 1 ≤ n → n ≤ 3 * Nat.totient n := by
  decide

/-- **`log 𝒫 ≤ log q + θ(m)`** for `𝒫 = ∏_{p ∈ S} p`, `S` a set of primes each dividing `q` or
at most `m`. -/
theorem log_prodP_le (m q : ℕ) (hq : 1 ≤ q) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p ∣ q ∨ p ≤ m)) :
    Real.log (∏ p ∈ S, (p : ℝ)) ≤ Real.log q + Chebyshev.theta m := by
  have hpos : ∀ p ∈ S, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (hS p hp).1.ne_zero
  rw [Real.log_prod hpos]
  set A := q.primeFactors
  set T := (Finset.Ioc 0 m).filter Nat.Prime
  have hsub : S ⊆ A ∪ T := by
    intro p hp
    obtain ⟨hpr, hd⟩ := hS p hp
    rcases hd with hd | hd
    · exact Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hpr, hd, by omega⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpr.pos, hd⟩, hpr⟩)
  have hnn : ∀ p ∈ A ∪ T, 0 ≤ Real.log (p : ℝ) := fun p _ => Real.log_natCast_nonneg p
  have h1 : ∑ p ∈ S, Real.log (p : ℝ) ≤ ∑ p ∈ A ∪ T, Real.log (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp
  have h2 := Finset.sum_union_inter (s₁ := A) (s₂ := T) (f := fun p => Real.log (p : ℝ))
  have h3 : 0 ≤ ∑ p ∈ A ∩ T, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  have hA : ∑ p ∈ A, Real.log (p : ℝ) ≤ Real.log q := by
    have e : Real.log (∏ p ∈ A, (p : ℝ)) = ∑ p ∈ A, Real.log (p : ℝ) :=
      Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hle : (∏ p ∈ A, (p : ℝ)) ≤ q := by
      have h := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
      have h' : ((∏ p ∈ A, p : ℕ) : ℝ) ≤ q := by exact_mod_cast h
      rwa [Nat.cast_prod] at h'
    have h0 : 0 < ∏ p ∈ A, (p : ℝ) := Finset.prod_pos fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    rw [← e]
    exact Real.log_le_log h0 hle
  have hT : ∑ p ∈ T, Real.log (p : ℝ) = Chebyshev.theta m := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast]
  linarith

/-- **`HX.SuspiroBig`, PROVED from RS75 (5.1) and RS62 (3.42)** (`ternvin.tex` 2738-2757; module
docstring). -/
theorem suspiroBig_of (rs : RS75Theta) (h15 : GS.RS62Thm15) : SuspiroBig := by
  intro m q hm hq hX
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ,
      S = (Finset.range (m + q + 1)).filter (fun p => p.Prime ∧ (p ∣ q ∨ p ≤ m)) := ⟨_, rfl⟩
  have hSm : ∀ p ∈ S, p.Prime ∧ (p ∣ q ∨ p ≤ m) := fun p hp => by
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hSm p hp).1
  have hsus : HC.suspProd m q = PSieve.wq (∏ p ∈ S, p) := by
    rw [wq_prod S hSp]
    unfold HC.suspProd
    rw [hSdef]
  have hP1 : 1 ≤ ∏ p ∈ S, p :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => (hSp p hp).ne_zero)
  rw [hsus, PSieve.wq_eq]
  have hEg := expG_ge
  have hlX : 2.14358 ≤ Real.log ((m : ℝ) + Real.log q) :=
    le_trans log_853_ge (Real.log_le_log (by norm_num) hX.le)
  have hφ : (0 : ℝ) < Nat.totient (∏ p ∈ S, p) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  by_cases hP : 27 ≤ ∏ p ∈ S, p
  · -- `𝒫 ≥ 27`: RS62 (3.42) and monotonicity of `e^γ t + b/t`
    have hrs := h15 (∏ p ∈ S, p) (by omega)
    unfold MinSp.bigF at hrs
    have hP27 : (27 : ℝ) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hP
    have hlogP : 3.28 ≤ Real.log ((∏ p ∈ S, p : ℕ) : ℝ) :=
      le_trans log_27_ge (Real.log_le_log (by norm_num) hP27)
    have hlogP0 : 0 < Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by linarith
    -- `u = log log 𝒫 ≥ 1.1864`
    have hu : 1.1864 ≤ Real.log (Real.log ((∏ p ∈ S, p : ℕ) : ℝ)) := by
      have h := Real.log_le_log (Real.exp_pos 1.1864) (le_trans exp_11864_le hlogP)
      rwa [Real.log_exp] at h
    -- `log 𝒫 ≤ 1.001102 X`
    have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have hlP : Real.log ((∏ p ∈ S, p : ℕ) : ℝ) ≤ 1.001102 * ((m : ℝ) + Real.log q) := by
      have h1 := log_prodP_le m q hq S hSm
      rw [← Nat.cast_prod] at h1
      have h2 := rs m
      linarith
    have hX0 : 0 < (m : ℝ) + Real.log q := by linarith
    -- `u ≤ U = log X + 0.001102`
    have hU : Real.log (Real.log ((∏ p ∈ S, p : ℕ) : ℝ)) ≤
        Real.log ((m : ℝ) + Real.log q) + 0.001102 := by
      have h1 := Real.log_le_log hlogP0 hlP
      rw [Real.log_mul (by norm_num) hX0.ne'] at h1
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.001102 by norm_num)
      linarith
    set u := Real.log (Real.log ((∏ p ∈ S, p : ℕ) : ℝ)) with hudef
    set L := Real.log ((m : ℝ) + Real.log q) with hLdef
    set E := Real.exp Real.eulerMascheroniConstant with hEdef
    have hu0 : 0 < u := by linarith
    have hU0 : 0 < L + 0.001102 := by linarith
    -- `b/u ≤ b/U + E(U − u)`, since `b ≤ E·u·U`
    have hb : 2.50637 ≤ E * (u * (L + 0.001102)) := by
      have h1 : 1.1864 * 1.1864 ≤ u * (L + 0.001102) :=
        mul_le_mul hu (by linarith) (by norm_num) hu0.le
      nlinarith
    have hmono : 2.50637 / u ≤ 2.50637 / (L + 0.001102) + E * (L + 0.001102 - u) := by
      have e : 2.50637 / u - 2.50637 / (L + 0.001102) =
          2.50637 * (L + 0.001102 - u) / (u * (L + 0.001102)) := by
        field_simp
      have h2 : 2.50637 * (L + 0.001102 - u) / (u * (L + 0.001102)) ≤
          E * (L + 0.001102 - u) := by
        rw [div_le_iff₀ (by positivity)]
        have hd : 0 ≤ L + 0.001102 - u := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hb hd]
      linarith
    -- `b/U ≤ b/L ≤ 0.656608·E`
    have hL0 : 0 < L := by linarith
    have hbU : 2.50637 / (L + 0.001102) ≤ 2.50637 / L :=
      div_le_div_of_nonneg_left (by norm_num) hL0 (by linarith)
    have hbL : 2.50637 / L ≤ 0.656608 * E := by
      rw [div_le_iff₀ hL0]
      have := mul_le_mul hEg hlX (by norm_num) (by linarith)
      nlinarith
    have hfin : E * u + 2.50637 / u ≤ E * (L + 0.65771) := by
      have hEu : E * u ≤ E * (L + 0.001102) := mul_le_mul_of_nonneg_left hU (by linarith)
      nlinarith
    linarith
  · -- `𝒫 < 27`: `𝒫 ≤ 3φ(𝒫)`
    have h3 := le_three_totient _ (by omega) hP1
    have h3' : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ 3 * (Nat.totient (∏ p ∈ S, p) : ℝ) := by
      exact_mod_cast h3
    have hle3 : ((∏ p ∈ S, p : ℕ) : ℝ) / (Nat.totient (∏ p ∈ S, p) : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hφ]
      linarith
    have hr : 3 ≤ Real.exp Real.eulerMascheroniConstant *
        (Real.log ((m : ℝ) + Real.log q) + 0.65771) := by
      nlinarith
    linarith

/-- **`HC.EspagnRed` with `lem:suspiro` discharged**: RS75 (5.1), RS62 (3.42) and the two named
links that remain. -/
theorem espagnRed_of_rs (rs : RS75Theta) (h15 : GS.RS62Thm15) (ed : EspagnEdge)
    (lq : EspagnLargeQ) : HC.EspagnRed :=
  espagnRed_of_links (suspiroBig_of rs h15) ed lq

end Principia.Common.TernaryGoldbach.HX
