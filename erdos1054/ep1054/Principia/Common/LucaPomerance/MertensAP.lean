/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.Unconditional
import Principia.Common.Mertens.Mertens

set_option autoImplicit false

/-!
# Mertens' second theorem in arithmetic progressions, uniformly in the modulus

`mertens_AP`: for every `B ≥ 1` there are `K > 0` and `T₀` such that for every modulus `m ≥ 1`,
every unit class `a mod m` and all `T₀ ≤ T ≤ x` with `m ≤ (log T)^B`,

  `|∑_{T < n ≤ x, n ≡ a (m)} Λ(n)/(n log n) − (log log x − log log T)/φ(m)| ≤ K/φ(m)`.

`mertens_AP_primes` is the prime form (`∑ 1/q` over primes `q ≡ a`), with an extra absolute
constant on the lower side for the prime powers.

**Route (no integrals).** Siegel–Walfisz (`Principia.Common.SW.siegel_walfisz_unconditional`) gives
`|ψ(k; m, a) − k/φ(m)| ≤ C k e^{−c(log k)^{1/10}}`, which is `≤ (k/φ(m))·C K₁/log k` once
`φ(m) ≤ m ≤ (log k)^B`. Discrete summation by parts against `f(k) = 1/(k log k)`
(`sum_Ioc_mul_eq_by_parts`) and the identity
`k(f(k) − f(k+1)) = [1/log k − 1/log(k+1)] + 1/((k+1) log(k+1))` reduce the main term to a
telescoping sum and to `∑ 1/(j log j)`, which `log log` brackets on both sides
(`one_div_mul_log_le_loglog_sub`, `loglog_sub_le_one_div_mul_log`). The error is controlled by
`(k/log k)(f(k) − f(k+1)) ≤ 2(1/log k − 1/log(k+1))`, which telescopes.

This is the input that Luca–Pomerance, Lemma 2.1 (1) needs **with the exact constant `1/φ(m)`**:
see `Campaigns/Erdos-1054/LP21-PLAN.md`.
-/

namespace Principia.Common.LucaPomerance.LP21

open Finset Real ArithmeticFunction

/-! ## Summation by parts and telescoping -/

/-- Discrete summation by parts with partial sums `A k = ∑_{n ≤ k} c n`. -/
theorem sum_Ioc_mul_eq_by_parts (c f : ℕ → ℝ) (T x : ℕ) (hTx : T ≤ x) :
    ∑ n ∈ Finset.Ioc T x, c n * f n =
      (∑ n ∈ Finset.range (x + 1), c n) * f x - (∑ n ∈ Finset.range (T + 1), c n) * f T +
      ∑ k ∈ Finset.Ico T x, (∑ n ∈ Finset.range (k + 1), c n) * (f k - f (k + 1)) := by
  induction x, hTx using Nat.le_induction with
  | base => simp
  | succ x hx ih =>
    rw [Finset.sum_Ioc_succ_top hx, ih, Finset.sum_Ico_succ_top hx,
      Finset.sum_range_succ (n := x + 1)]
    ring

/-- Telescoping over `Ico`. -/
theorem sum_Ico_telescope (g : ℕ → ℝ) (T x : ℕ) (h : T ≤ x) :
    ∑ k ∈ Finset.Ico T x, (g k - g (k + 1)) = g T - g x := by
  induction x, h using Nat.le_induction with
  | base => simp
  | succ x hx ih => rw [Finset.sum_Ico_succ_top hx, ih]; ring

/-! ## Elementary inequalities for `log` and `log log` -/

theorem one_le_log_of_three_le {k : ℕ} (hk : 3 ≤ k) : 1 ≤ Real.log k := by
  have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith)

/-- `log(k+1) − log k ≤ 1/k`. -/
theorem log_succ_sub_log_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) - Real.log k ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / k by positivity)
  have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
  linarith

/-- `1/(k+1) ≤ log(k+1) − log k`. -/
theorem le_log_succ_sub_log {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / k by positivity)
  have e : 1 - (((k : ℝ) + 1) / k)⁻¹ = 1 / ((k : ℝ) + 1) := by field_simp; ring
  linarith

/-- `log log (k+1) − log log k ≤ 1/(k log k)` for `k ≥ 3`. -/
theorem loglog_sub_le_one_div_mul_log {k : ℕ} (hk : 3 ≤ k) :
    Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) ≤ 1 / (k * Real.log k) := by
  have hL : 1 ≤ Real.log k := one_le_log_of_three_le hk
  have hk0 : (0 : ℝ) < k := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL1 : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log hk0 (by linarith)
  have hL1pos : 0 < Real.log ((k : ℝ) + 1) := by linarith
  rw [← Real.log_div hL1pos.ne' (by linarith)]
  have h1 := Real.log_le_sub_one_of_pos (div_pos hL1pos (by linarith : (0 : ℝ) < Real.log k))
  have h2 := log_succ_sub_log_le (k := k) (by omega)
  have e : Real.log ((k : ℝ) + 1) / Real.log k - 1 =
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log k := by
    field_simp
  have h3 : (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log k ≤ (1 / k) / Real.log k :=
    div_le_div_of_nonneg_right h2 (by linarith)
  have e2 : (1 / (k : ℝ)) / Real.log k = 1 / (k * Real.log k) := by
    rw [div_div]
  linarith

/-- `1/((k+1) log(k+1)) ≤ log log (k+1) − log log k` for `k ≥ 3`. -/
theorem one_div_mul_log_le_loglog_sub {k : ℕ} (hk : 3 ≤ k) :
    1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) ≤
      Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) := by
  have hL : 1 ≤ Real.log k := one_le_log_of_three_le hk
  have hk0 : (0 : ℝ) < k := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL1 : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log hk0 (by linarith)
  have hL1pos : 0 < Real.log ((k : ℝ) + 1) := by linarith
  rw [← Real.log_div hL1pos.ne' (by linarith)]
  have h1 := Real.one_sub_inv_le_log_of_pos
    (div_pos hL1pos (by linarith : (0 : ℝ) < Real.log k))
  have h2 := le_log_succ_sub_log (k := k) (by omega)
  have e : 1 - (Real.log ((k : ℝ) + 1) / Real.log k)⁻¹ =
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) := by
    field_simp
  have h3 : (1 / ((k : ℝ) + 1)) / Real.log ((k : ℝ) + 1) ≤
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) :=
    div_le_div_of_nonneg_right h2 hL1pos.le
  have e2 : (1 / ((k : ℝ) + 1)) / Real.log ((k : ℝ) + 1) =
      1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) := by
    rw [div_div]
  linarith

/-! ## The weight `f k = 1/(k log k)` -/

/-- The partial-summation weight `f(k) = 1/(k log k)`. -/
noncomputable def wt (k : ℕ) : ℝ := 1 / ((k : ℝ) * Real.log k)

theorem wt_nonneg (k : ℕ) : 0 ≤ wt k := by
  unfold wt
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · have : 0 ≤ Real.log k := Real.log_natCast_nonneg k
    positivity

/-- `k (f(k) − f(k+1)) = [1/log k − 1/log(k+1)] + 1/((k+1) log(k+1))`. -/
theorem mul_wt_sub {k : ℕ} (hk : 3 ≤ k) :
    (k : ℝ) * (wt k - wt (k + 1)) =
      (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) +
        1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) := by
  have hL : 1 ≤ Real.log k := one_le_log_of_three_le hk
  have hk0 : (0 : ℝ) < k := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL1 : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log hk0 (by linarith)
  have hL1pos : 0 < Real.log ((k : ℝ) + 1) := by linarith
  unfold wt
  push_cast
  field_simp
  ring

theorem wt_sub_nonneg {k : ℕ} (hk : 3 ≤ k) : 0 ≤ wt k - wt (k + 1) := by
  have hL : 1 ≤ Real.log k := one_le_log_of_three_le hk
  have hk0 : (0 : ℝ) < k := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL1 : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log hk0 (by linarith)
  unfold wt
  push_cast
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul (by linarith) hL1 (by linarith) (by linarith)

/-- `(k/log k)(f(k) − f(k+1)) ≤ 2 (1/log k − 1/log(k+1))`. -/
theorem div_log_mul_wt_sub_le {k : ℕ} (hk : 3 ≤ k) :
    (k : ℝ) / Real.log k * (wt k - wt (k + 1)) ≤
      2 * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := by
  have hL : 1 ≤ Real.log k := one_le_log_of_three_le hk
  have hk0 : (0 : ℝ) < k := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL1 : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log hk0 (by linarith)
  have hL1pos : 0 < Real.log ((k : ℝ) + 1) := by linarith
  have hid := mul_wt_sub hk
  have e : (k : ℝ) / Real.log k * (wt k - wt (k + 1)) =
      (1 / Real.log k) * ((k : ℝ) * (wt k - wt (k + 1))) := by ring
  rw [e, hid]
  have hd : 0 ≤ 1 / Real.log k - 1 / Real.log ((k : ℝ) + 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) hL1
  -- first piece: (1/log k) · d ≤ d
  have h1 : (1 / Real.log k) * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) ≤
      1 / Real.log k - 1 / Real.log ((k : ℝ) + 1) := by
    have : 1 / Real.log k ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
    nlinarith
  -- second piece: (1/log k) / ((k+1) log(k+1)) ≤ d
  have h2 : (1 / Real.log k) * (1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1))) ≤
      1 / Real.log k - 1 / Real.log ((k : ℝ) + 1) := by
    have hg := le_log_succ_sub_log (k := k) (by omega)
    have e3 : 1 / Real.log k - 1 / Real.log ((k : ℝ) + 1) =
        (Real.log ((k : ℝ) + 1) - Real.log k) / (Real.log k * Real.log ((k : ℝ) + 1)) := by
      field_simp
    have e4 : (1 / Real.log k) * (1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1))) =
        (1 / ((k : ℝ) + 1)) / (Real.log k * Real.log ((k : ℝ) + 1)) := by
      field_simp
    rw [e3, e4]
    exact div_le_div_of_nonneg_right hg (by positivity)
  linarith

/-! ## `u^N e^{−c u^{1/10}}` is bounded -/

theorem pow_mul_exp_neg_rpow_le (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u →
      u ^ N * Real.exp (-(c * u ^ ((1 : ℝ) / 10))) ≤ K := by
  refine ⟨((10 * N).factorial : ℝ) / c ^ (10 * N) + 1, by positivity, fun u hu => ?_⟩
  set v := u ^ ((1 : ℝ) / 10) with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg hu _
  have hvu : v ^ 10 = u := by
    rw [hv, show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hu (by norm_num)
  have hpow : u ^ N = v ^ (10 * N) := by rw [← hvu, ← pow_mul]
  have hexp := Real.pow_div_factorial_le_exp (c * v) (mul_nonneg hc.le hv0) (10 * N)
  have hfact : (0 : ℝ) < ((10 * N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcpow : (0 : ℝ) < c ^ (10 * N) := by positivity
  -- v^{10N} ≤ (10N)!/c^{10N} · e^{c v}
  have h1 : v ^ (10 * N) ≤ ((10 * N).factorial : ℝ) / c ^ (10 * N) * Real.exp (c * v) := by
    rw [mul_pow, div_le_iff₀ hfact] at hexp
    rw [div_mul_eq_mul_div, le_div_iff₀ hcpow]
    nlinarith [Real.exp_pos (c * v)]
  rw [hpow]
  have he : Real.exp (-(c * v)) * Real.exp (c * v) = 1 := by
    rw [← Real.exp_add]; simp
  have hepos : 0 < Real.exp (-(c * v)) := Real.exp_pos _
  calc v ^ (10 * N) * Real.exp (-(c * v))
      ≤ ((10 * N).factorial : ℝ) / c ^ (10 * N) * Real.exp (c * v) * Real.exp (-(c * v)) :=
        mul_le_mul_of_nonneg_right h1 hepos.le
    _ = ((10 * N).factorial : ℝ) / c ^ (10 * N) := by
        rw [mul_assoc, mul_comm (Real.exp (c * v)), he, mul_one]
    _ ≤ _ := by linarith

/-! ## Siegel–Walfisz with a relative error -/

/-- `ψ(k; m, a) = ∑_{n ≤ k, n ≡ a (m)} Λ(n)`, in the form of `siegel_walfisz_unconditional`. -/
noncomputable def psiAP (m : ℕ) (a : ZMod m) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), if a = ((n : ZMod m)) then vonMangoldt n else 0

theorem psiAP_nonneg (m : ℕ) (a : ZMod m) (k : ℕ) : 0 ≤ psiAP m a k := by
  unfold psiAP
  refine Finset.sum_nonneg fun n _ => ?_
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

/-- **Siegel–Walfisz, relative form.** For `m ≤ (log k)^B` the error is at most
`(k/φ(m))·K₁/log k`. -/
theorem sw_relative (B : ℕ) (hB : 1 ≤ B) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ T₀ : ℕ, 3 ≤ T₀ ∧ ∀ (m : ℕ) [NeZero m] (a : ZMod m), IsUnit a →
      ∀ k : ℕ, T₀ ≤ k → (m : ℝ) ≤ Real.log k ^ B →
        |psiAP m a k - (k : ℝ) / m.totient| ≤ (k : ℝ) / m.totient * (K₁ / Real.log k) := by
  obtain ⟨c, C, hc, hC, X₀, hsw⟩ :=
    Principia.Common.SW.siegel_walfisz_unconditional (B : ℝ) (by exact_mod_cast hB)
  obtain ⟨K, hK, hKb⟩ := pow_mul_exp_neg_rpow_le c hc (B + 1)
  refine ⟨C * K, by positivity, max 3 ⌈X₀⌉₊, le_max_left _ _, ?_⟩
  intro m _ a ha k hk hmk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ (k : ℝ) := Nat.ceil_le.mp (le_trans (le_max_right _ _) hk)
  have hL : 1 ≤ Real.log k := one_le_log_of_three_le hk3
  have hk0 : (0 : ℝ) < k := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    linarith
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hφm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hmk' : (m : ℝ) ≤ Real.log k ^ (B : ℝ) := by rw [Real.rpow_natCast]; exact hmk
  have h := hsw (k : ℝ) hkX m hmk' a ha
  rw [Nat.floor_natCast] at h
  set E := Real.exp (-(c * Real.log k ^ ((1 : ℝ) / 10))) with hE
  have hE' : Real.exp (-c * Real.log k ^ ((1 : ℝ) / 10)) = E := by rw [hE, neg_mul]
  rw [hE'] at h
  have hEpos : 0 < E := Real.exp_pos _
  -- φ · E ≤ K / log k
  have hφE : (m.totient : ℝ) * E ≤ K / Real.log k := by
    have h1 := hKb (Real.log k) (by linarith)
    rw [pow_succ] at h1
    rw [le_div_iff₀ (by linarith)]
    calc (m.totient : ℝ) * E * Real.log k ≤ Real.log k ^ B * E * Real.log k := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_right (hφm.trans hmk) hEpos.le
      _ = Real.log k ^ B * Real.log k * E := by ring
      _ ≤ K := h1
  have hmain : C * (k : ℝ) * E ≤ (k : ℝ) / m.totient * (C * K / Real.log k) := by
    have e1 : C * (k : ℝ) * E = C * k / m.totient * (m.totient * E) := by
      field_simp
    have e2 : (k : ℝ) / m.totient * (C * K / Real.log k) =
        C * k / m.totient * (K / Real.log k) := by
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hφE (by positivity)
  unfold psiAP
  linarith

/-! ## Mertens' second theorem in progressions -/

/-- **Mertens' second theorem in arithmetic progressions, uniform in the modulus** (von Mangoldt
form, weight `wt n = 1/(n log n)`). -/
theorem mertens_AP (B : ℕ) (hB : 1 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, 3 ≤ T₀ ∧ ∀ (m : ℕ) [NeZero m] (a : ZMod m), IsUnit a →
      ∀ T x : ℕ, T₀ ≤ T → T ≤ x → (m : ℝ) ≤ Real.log T ^ B →
        |∑ n ∈ Finset.Ioc T x, (if a = ((n : ZMod m)) then vonMangoldt n * wt n else 0)
          - (Real.log (Real.log x) - Real.log (Real.log T)) / m.totient| ≤ K / m.totient := by
  obtain ⟨K₁, hK₁, T₀, hT₀3, hrel⟩ := sw_relative B hB
  refine ⟨2 + 3 * K₁, by positivity, T₀, hT₀3, ?_⟩
  intro m _ a ha T x hT hTx hmT
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set φ : ℝ := (m.totient : ℝ) with hφdef
  have hφ : 0 < φ := by rw [hφdef]; exact_mod_cast Nat.totient_pos.mpr hm0
  have hT3 : 3 ≤ T := le_trans hT₀3 hT
  have hx3 : 3 ≤ x := le_trans hT3 hTx
  have hLT : 1 ≤ Real.log T := one_le_log_of_three_le hT3
  have hT0 : (0 : ℝ) < T := by
    have : (3 : ℝ) ≤ T := by exact_mod_cast hT3
    linarith
  have hlogTx : Real.log T ≤ Real.log x :=
    Real.log_le_log hT0 (by exact_mod_cast hTx)
  -- facts at every `k ≥ T`
  have hA : ∀ k : ℕ, T ≤ k →
      |psiAP m a k - (k : ℝ) / φ| ≤ (k : ℝ) / φ * (K₁ / Real.log k) := by
    intro k hk
    have hk0 : (0 : ℝ) < T := hT0
    have hlogk : Real.log T ≤ Real.log k := Real.log_le_log hk0 (by exact_mod_cast hk)
    have hmk : (m : ℝ) ≤ Real.log k ^ B :=
      hmT.trans (pow_le_pow_left₀ (by linarith) hlogk B)
    exact hrel m a ha k (le_trans hT hk) hmk
  -- the sum in partial-summation form
  set c : ℕ → ℝ := fun n => if a = ((n : ZMod m)) then vonMangoldt n else 0 with hcdef
  have hsum : ∑ n ∈ Finset.Ioc T x, (if a = ((n : ZMod m)) then vonMangoldt n * wt n else 0) =
      ∑ n ∈ Finset.Ioc T x, c n * wt n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    change _ = (if a = ((n : ZMod m)) then vonMangoldt n else 0) * wt n
    by_cases h : a = ((n : ZMod m))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  have hpsi : ∀ k : ℕ, ∑ n ∈ Finset.range (k + 1), c n = psiAP m a k := fun k => rfl
  have hbp := sum_Ioc_mul_eq_by_parts c wt T x hTx
  simp only [hpsi] at hbp
  rw [hsum, hbp]
  set D := Real.log (Real.log x) - Real.log (Real.log T) with hDdef
  -- boundary terms
  have hbd : ∀ k : ℕ, T ≤ k → 0 ≤ psiAP m a k * wt k ∧ psiAP m a k * wt k ≤ (1 + K₁) / φ := by
    intro k hk
    have hk3 : 3 ≤ k := le_trans hT3 hk
    have hLk : 1 ≤ Real.log k := one_le_log_of_three_le hk3
    have hk0 : (0 : ℝ) < k := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      linarith
    refine ⟨mul_nonneg (psiAP_nonneg m a k) (wt_nonneg k), ?_⟩
    have h1 := (abs_le.mp (hA k hk)).2
    have hAup : psiAP m a k ≤ (k : ℝ) / φ * (1 + K₁ / Real.log k) := by nlinarith
    have hK1k : K₁ / Real.log k ≤ K₁ := div_le_self hK₁.le hLk
    have hwt : wt k = 1 / ((k : ℝ) * Real.log k) := rfl
    calc psiAP m a k * wt k ≤ (k : ℝ) / φ * (1 + K₁ / Real.log k) * wt k :=
          mul_le_mul_of_nonneg_right hAup (wt_nonneg k)
      _ = (1 + K₁ / Real.log k) / (φ * Real.log k) := by
          rw [hwt]; field_simp
      _ ≤ (1 + K₁) / (φ * 1) := by
          apply div_le_div₀ (by positivity) (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_left hLk hφ.le
      _ = (1 + K₁) / φ := by rw [mul_one]
  obtain ⟨hbx0, hbx1⟩ := hbd x hTx
  obtain ⟨hbT0, hbT1⟩ := hbd T le_rfl
  -- the main sum: split `A k = k/φ + (A k − k/φ)`
  have hsplit : ∑ k ∈ Finset.Ico T x, psiAP m a k * (wt k - wt (k + 1)) =
      (1 / φ) * ∑ k ∈ Finset.Ico T x, (k : ℝ) * (wt k - wt (k + 1)) +
        ∑ k ∈ Finset.Ico T x, (psiAP m a k - (k : ℝ) / φ) * (wt k - wt (k + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
    ring
  -- the telescoping part of `k (f k − f (k+1))`
  have htel : ∑ k ∈ Finset.Ico T x, (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) =
      1 / Real.log T - 1 / Real.log x := by
    have := sum_Ico_telescope (fun k : ℕ => 1 / Real.log k) T x hTx
    simpa [Nat.cast_add, Nat.cast_one] using this
  have htel_nonneg : 0 ≤ 1 / Real.log T - 1 / Real.log x := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) hlogTx
  have htel_le : 1 / Real.log T - 1 / Real.log x ≤ 1 := by
    have h1 : 1 / Real.log T ≤ 1 := by rw [div_le_one (by linarith)]; exact hLT
    have h2 : 0 ≤ 1 / Real.log x := by
      have : 0 < Real.log x := by linarith
      positivity
    linarith
  have hkd : ∑ k ∈ Finset.Ico T x, (k : ℝ) * (wt k - wt (k + 1)) =
      (1 / Real.log T - 1 / Real.log x) +
        ∑ k ∈ Finset.Ico T x, 1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) := by
    rw [← htel, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    exact mul_wt_sub (le_trans hT3 hk.1)
  -- `H = ∑ 1/((k+1) log (k+1))` between `D − 1` and `D`
  have hH_le : ∑ k ∈ Finset.Ico T x, 1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) ≤ D := by
    have h1 : ∑ k ∈ Finset.Ico T x, 1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) ≤
        ∑ k ∈ Finset.Ico T x,
          (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      exact one_div_mul_log_le_loglog_sub (le_trans hT3 hk.1)
    have h2 := sum_Ico_telescope (fun k : ℕ => -Real.log (Real.log k)) T x hTx
    have h3 : ∑ k ∈ Finset.Ico T x,
        (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) = D := by
      rw [hDdef, ← neg_sub_neg, ← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    linarith
  have hH_ge : D - 1 ≤ ∑ k ∈ Finset.Ico T x, 1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) := by
    have h1 : ∑ k ∈ Finset.Ico T x,
          (Real.log (Real.log ((k : ℝ) + 1 + 1)) - Real.log (Real.log ((k : ℝ) + 1))) ≤
        ∑ k ∈ Finset.Ico T x, 1 / (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      have := loglog_sub_le_one_div_mul_log (k := k + 1) (by omega)
      push_cast at this
      exact this
    have h2 := sum_Ico_telescope (fun k : ℕ => -Real.log (Real.log ((k : ℝ) + 1))) T x hTx
    have h3 : ∑ k ∈ Finset.Ico T x,
        (Real.log (Real.log ((k : ℝ) + 1 + 1)) - Real.log (Real.log ((k : ℝ) + 1))) =
          Real.log (Real.log ((x : ℝ) + 1)) - Real.log (Real.log ((T : ℝ) + 1)) := by
      rw [← neg_sub_neg, ← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    -- `log log (x+1) ≥ log log x` and `log log (T+1) − log log T ≤ 1`
    have hx0 : (0 : ℝ) < x := by
      have : (3 : ℝ) ≤ x := by exact_mod_cast hx3
      linarith
    have hLx : 0 < Real.log x := by linarith
    have hmono : Real.log (Real.log x) ≤ Real.log (Real.log ((x : ℝ) + 1)) :=
      Real.log_le_log hLx (Real.log_le_log hx0 (by linarith))
    have hTstep := loglog_sub_le_one_div_mul_log hT3
    have hTle : 1 / ((T : ℝ) * Real.log T) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (3 : ℝ) ≤ T := by exact_mod_cast hT3
      nlinarith
    rw [hDdef]
    linarith
  -- the error sum
  have herr : |∑ k ∈ Finset.Ico T x, (psiAP m a k - (k : ℝ) / φ) * (wt k - wt (k + 1))| ≤
      2 * K₁ / φ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ k ∈ Finset.Ico T x,
        |(psiAP m a k - (k : ℝ) / φ) * (wt k - wt (k + 1))| ≤
          (2 * K₁ / φ) * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk3 : 3 ≤ k := le_trans hT3 hk.1
      have hd := wt_sub_nonneg hk3
      rw [abs_mul, abs_of_nonneg hd]
      have h2 := div_log_mul_wt_sub_le hk3
      calc |psiAP m a k - (k : ℝ) / φ| * (wt k - wt (k + 1))
          ≤ (k : ℝ) / φ * (K₁ / Real.log k) * (wt k - wt (k + 1)) :=
            mul_le_mul_of_nonneg_right (hA k hk.1) hd
        _ = (K₁ / φ) * ((k : ℝ) / Real.log k * (wt k - wt (k + 1))) := by ring
        _ ≤ (K₁ / φ) * (2 * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (2 * K₁ / φ) * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, htel]
    have : 0 ≤ 2 * K₁ / φ := by positivity
    nlinarith
  -- assemble
  have hKd : 0 < 2 + 3 * K₁ := by positivity
  rw [abs_le]
  have herr' := abs_le.mp herr
  constructor
  · -- lower bound
    have e : (D / φ) = (1 / φ) * D := by ring
    have hl : (1 / φ) * (D - 1) ≤
        (1 / φ) * ∑ k ∈ Finset.Ico T x, (k : ℝ) * (wt k - wt (k + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hkd]; linarith
    rw [hsplit]
    have e2 : -((2 + 3 * K₁) / φ) = (1 / φ) * (D - 1) - (1 + K₁) / φ - 2 * K₁ / φ - D / φ := by
      field_simp; ring
    linarith
  · -- upper bound
    have hu : (1 / φ) * ∑ k ∈ Finset.Ico T x, (k : ℝ) * (wt k - wt (k + 1)) ≤
        (1 / φ) * (1 + D) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hkd]; linarith
    rw [hsplit]
    have e2 : (2 + 3 * K₁) / φ = (1 + K₁) / φ + (1 / φ) * (1 + D) + 2 * K₁ / φ - D / φ := by
      field_simp; ring
    linarith

/-! ## Prime form -/

/-- For a prime `q`, `Λ(q) · wt q = 1/q`. -/
theorem vonMangoldt_mul_wt_prime {q : ℕ} (hq : q.Prime) : vonMangoldt q * wt q = 1 / q := by
  rw [vonMangoldt_apply_prime hq]
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlog : 0 < Real.log q := Real.log_pos hq1
  unfold wt
  field_simp

/-- A non-prime `n` with `Λ(n) ≠ 0` is at least `4`. -/
theorem four_le_of_vonMangoldt_ne_zero {n : ℕ} (hn : ¬ n.Prime) (hΛ : vonMangoldt n ≠ 0) :
    4 ≤ n := by
  rw [vonMangoldt_apply] at hΛ
  split_ifs at hΛ with hpp
  · obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp2 : 2 ≤ p := (Nat.prime_iff.mpr hp).two_le
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      exact absurd (by simpa using Nat.prime_iff.mpr hp) hn
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
  · exact absurd rfl hΛ

/-- The non-prime part of `∑ Λ(n)/(n log n)` over any subset of `(0, x]` and any class is at most
`E₁ = ∑_p log p/(p(p−1))` (Mertens port, `E₁Λ.le_E₁p_add_E₁`). -/
theorem sum_nonprime_le_E₁ (P : ℕ → Prop) [DecidablePred P] (s : Finset ℕ) (x : ℕ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    ∑ n ∈ s.filter (fun n => ¬ n.Prime), (if P n then vonMangoldt n * wt n else 0) ≤
      Mertens.E₁ := by
  classical
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    have : s = ∅ := Finset.subset_empty.mp (by simpa using hs)
    subst this
    simp only [Finset.filter_empty, Finset.sum_empty]
    exact tsum_nonneg Mertens.E₁.summand_nonneg
  -- termwise: `[P n] Λ(n) wt(n) ≤ Λ(n)/n` for non-prime `n ≥ 1`
  have hterm : ∀ n ∈ s.filter (fun n => ¬ n.Prime),
      (if P n then vonMangoldt n * wt n else 0) ≤ vonMangoldt n / n := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp (hs hn.1)).1
    have hΛ0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    split_ifs
    · by_cases hΛ : vonMangoldt n = 0
      · rw [hΛ]; simp
      · have h4 := four_le_of_vonMangoldt_ne_zero hn.2 hΛ
        have hL : 1 ≤ Real.log n := one_le_log_of_three_le (by omega)
        unfold wt
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hn0]
        have : vonMangoldt n * n ≤ vonMangoldt n * (n * Real.log n) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0
          nlinarith
        linarith
    · positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  -- enlarge to all non-primes in `(0, x]`
  have hsub : ∑ n ∈ s.filter (fun n => ¬ n.Prime), vonMangoldt n / (n : ℝ) ≤
      ∑ n ∈ (Finset.Ioc 0 x).filter (fun n => ¬ n.Prime), vonMangoldt n / (n : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ hs
    · intro n _ _
      have : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
      positivity
  refine hsub.trans ?_
  have hM := Mertens.E₁Λ.le_E₁p_add_E₁ (x := (x : ℝ)) (by exact_mod_cast hx0)
  unfold Mertens.E₁Λ Mertens.E₁p at hM
  rw [Nat.floor_natCast] at hM
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 x) (fun n => n.Prime)
    (fun n => vonMangoldt n / (n : ℝ))
  have hprime : ∑ n ∈ (Finset.Ioc 0 x).filter (fun n => n.Prime), vonMangoldt n / (n : ℝ) =
      ∑ p ∈ (Finset.Ioc 0 x).filter (fun n => n.Prime), Real.log p / p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  linarith

/-- **Mertens' second theorem in progressions, prime form.** Upper bound `(D + K)/φ(m)` and lower
bound `(D − K)/φ(m) − K`, with `D = log log x − log log T`. -/
theorem mertens_AP_primes (B : ℕ) (hB : 1 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, 3 ≤ T₀ ∧ ∀ (m : ℕ) [NeZero m] (a : ZMod m), IsUnit a →
      ∀ T x : ℕ, T₀ ≤ T → T ≤ x → (m : ℝ) ≤ Real.log T ^ B →
        (∑ q ∈ (Finset.Ioc T x).filter (fun q : ℕ => q.Prime ∧ a = ((q : ZMod m))), (1 : ℝ) / q) ≤
            (Real.log (Real.log x) - Real.log (Real.log T) + K) / m.totient ∧
        (Real.log (Real.log x) - Real.log (Real.log T) - K) / m.totient - K ≤
            ∑ q ∈ (Finset.Ioc T x).filter (fun q : ℕ => q.Prime ∧ a = ((q : ZMod m))),
              (1 : ℝ) / q := by
  classical
  obtain ⟨K, hK, T₀, hT₀3, hmap⟩ := mertens_AP B hB
  have hE₁ : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
  refine ⟨K + Mertens.E₁, by positivity, T₀, hT₀3, ?_⟩
  intro m _ a ha T x hT hTx hmT
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have h := abs_le.mp (hmap m a ha T x hT hTx hmT)
  set S := ∑ n ∈ Finset.Ioc T x, (if a = ((n : ZMod m)) then vonMangoldt n * wt n else 0)
    with hSdef
  set D := Real.log (Real.log x) - Real.log (Real.log T)
  set Pr := ∑ q ∈ (Finset.Ioc T x).filter (fun q : ℕ => q.Prime ∧ a = ((q : ZMod m))), (1 : ℝ) / q
  set Np := ∑ n ∈ (Finset.Ioc T x).filter (fun n => ¬ n.Prime),
    (if a = ((n : ZMod m)) then vonMangoldt n * wt n else 0)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc T x) (fun n => n.Prime)
    (fun n : ℕ => if a = ((n : ZMod m)) then vonMangoldt n * wt n else 0)
  have hPr : ∑ n ∈ (Finset.Ioc T x).filter (fun n => n.Prime),
      (if a = ((n : ZMod m)) then vonMangoldt n * wt n else 0) = Pr := by
    rw [← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr rfl fun q hq => ?_
    exact vonMangoldt_mul_wt_prime (Finset.mem_filter.mp hq).2.1
  have hNp0 : 0 ≤ Np := by
    refine Finset.sum_nonneg fun n _ => ?_
    split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (wt_nonneg n)
    · exact le_rfl
  have hNp1 : Np ≤ Mertens.E₁ :=
    sum_nonprime_le_E₁ (fun n : ℕ => a = ((n : ZMod m))) (Finset.Ioc T x) x
      (Finset.Ioc_subset_Ioc_left (Nat.zero_le T))
  have hSeq : S = Pr + Np := by rw [hSdef, ← hsplit, hPr]
  constructor
  · have e : (D + (K + Mertens.E₁)) / m.totient = D / m.totient + K / m.totient +
        Mertens.E₁ / m.totient := by ring
    have : 0 ≤ Mertens.E₁ / m.totient := by positivity
    rw [e]; linarith
  · have e : (D - (K + Mertens.E₁)) / m.totient = D / m.totient - K / m.totient -
        Mertens.E₁ / m.totient := by ring
    have : 0 ≤ Mertens.E₁ / m.totient := by positivity
    rw [e]; linarith

end Principia.Common.LucaPomerance.LP21
