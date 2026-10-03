/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.OmegaP
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

/-!
# Luca–Pomerance Lemma 2.1 (i): `v_p(n) < v_p(σ(n))` for every prime `p ≤ y(n)`, almost always

`y(n) = log log n / log log log n` (`lpY`). `FailI n` says (i) fails at `n`.
`failI_count_le`: for every `ε > 0`, eventually `#{n ≤ N : FailI n} ≤ ε N`.

Proof (see `Campaigns/Erdos-1054/LP21-PLAN.md` §2). If (i) fails at `p` then `ω_p(n) ≤ v_p(n)`
(`omegaP_le_factorization_of_fail`). For `n ∈ (√N, N]`, `y(n) ≤ Y := L/log(L − log 2)`,
`L = log log N` (`lpY_le_of_sq`). With `P₀ ≥ 8/ε` and `4·2^{−J} ≤ ε/8`:
* `p ≤ P₀`: `p^J ∣ n` or `ω_p(n) ≤ J − 1`; the latter costs `≤ 2^J C N e^{K/2} e^{−L/(2P₀)}`
  (Pollack with `z = 1/2` and `S_p ≥ L/(p−1) − K`);
* `P₀ < p ≤ Y`: `p² ∣ n` or `ω_p(n) ≤ 1`; the latter costs `≤ e^{1+K} C N λ/(L − log 2)`,
  `λ = log(L − log 2)` (Pollack with `z = 1/s₀`, `s₀ = L/(p−1) − K ≥ λ − K`, and `t e^{−t}`
  decreasing), and there are `π(Y) ≪ Y/log Y` such primes (`Chebyshev.pi_le_log4_mul_div`);
  the product tends to 0 (`tendsto_GF`).
-/

namespace Principia.Common.LucaPomerance.LP21

open Finset Real ArithmeticFunction Filter
open scoped Topology

/-- The Luca–Pomerance level `y(n) = log log n / log log log n`. -/
noncomputable def lpY (n : ℕ) : ℝ := Real.log (Real.log n) / Real.log (Real.log (Real.log n))

/-- (i) fails at the prime `p`: `v_p(σ(n)) ≤ v_p(n)`. -/
def FailP (p n : ℕ) : Prop := (sigma 1 n).factorization p ≤ n.factorization p

/-- (i) fails at `n`: some prime `p ≤ y(n)` has `v_p(σ(n)) ≤ v_p(n)`. -/
def FailI (n : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ lpY n ∧ FailP p n

/-! ## Counting multiples; inverse-power sums -/

theorem card_filter_dvd_Icc (d N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have h : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

theorem card_filter_dvd_Icc_le (d N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) ≤ (N : ℝ) / d := by
  rw [card_filter_dvd_Icc]
  exact Nat.cast_div_le

theorem sum_Ioc_inv_sq_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / a - 1 / b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb]
    have hb0 : (0 : ℝ) < b := by
      have : (1 : ℝ) ≤ b := by exact_mod_cast le_trans ha hb
      linarith
    have hstep : (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hb0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `∑_{k ∈ s} 1/k² ≤ 1/a` when every `k ∈ s` exceeds `a ≥ 1`. -/
theorem sum_inv_sq_le_of_gt (s : Finset ℕ) (a : ℕ) (ha : 1 ≤ a) (hs : ∀ k ∈ s, a < k) :
    ∑ k ∈ s, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / a := by
  set b := max a (s.sup id)
  have hsub : s ⊆ Finset.Ioc a b := by
    intro k hk
    rw [Finset.mem_Ioc]
    exact ⟨hs k hk, le_trans (Finset.le_sup (f := id) hk) (le_max_right _ _)⟩
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => by positivity : ∀ k ∈ Finset.Ioc a b, k ∉ s → (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2)
  have h2 := sum_Ioc_inv_sq_le a b ha (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  linarith

/-- `∑_{k ∈ s} 1/k^J ≤ 4/2^J` for `J ≥ 2` and every `k ∈ s` at least `2`. -/
theorem sum_inv_pow_le (s : Finset ℕ) (J : ℕ) (hJ : 2 ≤ J) (hs : ∀ k ∈ s, 2 ≤ k) :
    ∑ k ∈ s, (1 : ℝ) / (k : ℝ) ^ J ≤ 4 / 2 ^ J := by
  have hterm : ∀ k ∈ s, (1 : ℝ) / (k : ℝ) ^ J ≤ (4 / 2 ^ J) * ((1 : ℝ) / (k : ℝ) ^ 2) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hs k hk
    have hk0 : (0 : ℝ) < k := by linarith
    obtain ⟨j, rfl⟩ : ∃ j, J = j + 2 := ⟨J - 2, by omega⟩
    have hpow : (2 : ℝ) ^ j ≤ (k : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) hk2 j
    rw [pow_add, pow_add]
    rw [div_le_iff₀ (by positivity)]
    have e : 4 / (2 ^ j * 2 ^ 2) * (1 / (k : ℝ) ^ 2) * ((k : ℝ) ^ j * (k : ℝ) ^ 2) =
        (k : ℝ) ^ j / 2 ^ j := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity), one_mul]
    exact hpow
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h1 := sum_inv_sq_le_of_gt s 1 le_rfl (fun k hk => by have := hs k hk; omega)
  have h4 : (0 : ℝ) ≤ 4 / 2 ^ J := by positivity
  calc 4 / 2 ^ J * ∑ k ∈ s, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 4 / 2 ^ J * (1 / ((1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = 4 / 2 ^ J := by norm_num

/-- `t e^{−t}` is decreasing on `[1, ∞)`. -/
theorem mul_exp_neg_le {t s : ℝ} (ht : 1 ≤ t) (hts : t ≤ s) :
    s * Real.exp (-s) ≤ t * Real.exp (-t) := by
  have h1 := Real.add_one_le_exp (s - t)
  have he : Real.exp (-t) = Real.exp (s - t) * Real.exp (-s) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  have hes : 0 < Real.exp (-s) := Real.exp_pos _
  have hkey : s ≤ t * Real.exp (s - t) := by nlinarith
  nlinarith

/-! ## `y(n)` on `(√N, N]` -/

/-- For `n ≤ N < n²`, `y(n) ≤ L/log(L − log 2)` with `L = log log N`. -/
theorem lpY_le_of_sq (N n : ℕ) (hnN : n ≤ N) (hsq : N < n * n)
    (hL : 1 + Real.log 2 < Real.log (Real.log N)) :
    lpY n ≤ Real.log (Real.log N) / Real.log (Real.log (Real.log N) - Real.log 2) := by
  set LN := Real.log (Real.log N) with hLN
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `N ≥ 2`, so `log N > 0`
  have hN2 : 2 ≤ N := by
    by_contra h
    push Not at h
    interval_cases N <;> simp [hLN] at hL <;> linarith
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith)
  have hn2 : 2 ≤ n := by nlinarith
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith)
  have hlognN : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hsq' : Real.log N < 2 * Real.log n := by
    have h1 : (N : ℝ) < (n : ℝ) * n := by exact_mod_cast hsq
    have h2 := Real.log_lt_log hN0 h1
    rw [Real.log_mul hn0.ne' hn0.ne'] at h2
    linarith
  have hLn_le : Real.log (Real.log n) ≤ LN := Real.log_le_log hlogn hlognN
  have hLn_ge : LN - Real.log 2 < Real.log (Real.log n) := by
    have h1 : Real.log (Real.log N / 2) < Real.log (Real.log n) :=
      Real.log_lt_log (by positivity) (by linarith)
    rw [Real.log_div hlogN.ne' (by norm_num)] at h1
    exact h1
  have hpos : 0 < LN - Real.log 2 := by linarith
  have hden : Real.log (LN - Real.log 2) ≤ Real.log (Real.log (Real.log n)) :=
    Real.log_le_log hpos hLn_ge.le
  have hden0 : 0 < Real.log (LN - Real.log 2) := Real.log_pos (by linarith)
  unfold lpY
  exact div_le_div₀ (by linarith) hLn_le hden0 hden

/-! ## The large-prime cost tends to zero -/

/-- `λ(L) = log(L − log 2)`. -/
noncomputable def lamF (L : ℝ) : ℝ := Real.log (L - Real.log 2)

/-- The large-prime cost, per unit of `e^{1+K} C N`: Chebyshev's bound for `π(Y)`,
`Y = L/λ`, times `λ/(L − log 2)`. -/
noncomputable def GF (L : ℝ) : ℝ :=
  (Real.log 4 * (L / lamF L) / Real.log (Real.sqrt (L / lamF L)) + Real.sqrt (L / lamF L)) *
    (lamF L / (L - Real.log 2))

theorem tendsto_sub_log_two : Tendsto (fun L : ℝ => L - Real.log 2) atTop atTop :=
  (tendsto_atTop_add_const_right atTop (-Real.log 2) tendsto_id).congr
    (fun L => by simp [sub_eq_add_neg])

theorem tendsto_lamF : Tendsto lamF atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_sub_log_two

theorem tendsto_lamF_div : Tendsto (fun L : ℝ => lamF L / L) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h2 : Real.log 2 ≠ 1 := by
      intro h
      have := Real.exp_one_gt_d9
      have e := Real.exp_log (show (0 : ℝ) < 2 by norm_num)
      rw [h] at e
      linarith
    exact lt_of_le_of_ne (by linarith) h2
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlogdiv ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    unfold lamF
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    unfold lamF
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by linarith)

theorem tendsto_ratio_sub_log_two : Tendsto (fun L : ℝ => L / (L - Real.log 2)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := Real.log 2)).div_atTop tendsto_sub_log_two)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.log 2)] with L hL
  have : L - Real.log 2 ≠ 0 := by linarith
  field_simp
  ring

theorem tendsto_GF : Tendsto GF atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlamL := tendsto_lamF_div
  -- `λ/L → 0⁺`, so `Y = L/λ → ∞`
  have hpos : ∀ᶠ L : ℝ in atTop, 0 < lamF L / L := by
    filter_upwards [(tendsto_lamF.eventually_gt_atTop 0), eventually_gt_atTop (0 : ℝ)]
      with L h1 h2
    positivity
  have hY : Tendsto (fun L : ℝ => L / lamF L) atTop atTop := by
    have h := (tendsto_nhdsWithin_iff.mpr ⟨hlamL, hpos⟩).inv_tendsto_nhdsGT_zero
    refine h.congr (fun L => ?_)
    simp [inv_div]
  have hinvlog : Tendsto (fun L : ℝ => (Real.log (L / lamF L))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hY)
  have hsqrt : Tendsto (fun L : ℝ => Real.sqrt (lamF L / L)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlamL
    rw [Real.sqrt_zero] at h
    exact h
  have hratio := tendsto_ratio_sub_log_two
  have hlim := ((tendsto_const_nhds (x := 2 * Real.log 4)).mul hratio |>.mul hinvlog).add
    (hsqrt.mul hratio)
  simp only [mul_one, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_lamF.eventually_gt_atTop 0, eventually_gt_atTop (Real.log 2 + 1),
    hY.eventually_gt_atTop 1] with L hlam hL hY1
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < L / lamF L := by positivity
  have hlogY : 0 < Real.log (L / lamF L) := Real.log_pos hY1
  have hsub : 0 < L - Real.log 2 := by linarith
  have hsL := Real.mul_self_sqrt hL0.le
  have hsl := Real.mul_self_sqrt hlam.le
  have hsL0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsl0 : 0 < Real.sqrt (lamF L) := Real.sqrt_pos.mpr hlam
  have hlamne : lamF L ≠ 0 := hlam.ne'
  have hlogYne : Real.log (L / lamF L) ≠ 0 := hlogY.ne'
  have hsubne : L - Real.log 2 ≠ 0 := hsub.ne'
  unfold GF
  rw [Real.log_sqrt hY0.le, Real.sqrt_div hL0.le, Real.sqrt_div hlam.le, add_mul]
  congr 1
  · field_simp
  · rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (L * (L - Real.log 2)) * hsl - (lamF L * (L - Real.log 2)) * hsL

/-! ## Failure at one prime -/

open Classical in
/-- If (i) fails at `p` then `p^J ∣ n` or `ω_p(n) ≤ J − 1`. -/
theorem card_failP_le (p N J : ℕ) (hp : p.Prime) :
    (((Finset.Icc 1 N).filter (FailP p)).card : ℝ) ≤
      (N : ℝ) / (p : ℝ) ^ J +
        (((Finset.Icc 1 N).filter (fun n => omegaP p n ≤ J - 1)).card : ℝ) := by
  have hsub : (Finset.Icc 1 N).filter (FailP p) ⊆
      (Finset.Icc 1 N).filter (fun n => p ^ J ∣ n) ∪
        (Finset.Icc 1 N).filter (fun n => omegaP p n ≤ J - 1) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hω := omegaP_le_factorization_of_fail hp hn0 hn.2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
    by_cases hJv : J ≤ n.factorization p
    · exact Or.inl ⟨hn.1, (hp.pow_dvd_iff_le_factorization hn0).mpr hJv⟩
    · exact Or.inr ⟨hn.1, by omega⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.Icc 1 N).filter (fun n => p ^ J ∣ n))
    ((Finset.Icc 1 N).filter (fun n => omegaP p n ≤ J - 1))
  have h3 := card_filter_dvd_Icc_le (p ^ J) N
  push_cast at h3
  have h4 : (((Finset.Icc 1 N).filter (FailP p)).card : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n => p ^ J ∣ n)).card : ℝ) +
        (((Finset.Icc 1 N).filter (fun n => omegaP p n ≤ J - 1)).card : ℝ) := by
    exact_mod_cast h1.trans h2
  linarith

/-! ## The density bound for (i) -/

theorem tendsto_loglog_nat : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_sqrt_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N ≤ δ * N := by
  filter_upwards [eventually_ge_atTop ⌈(1 / δ) ^ 2⌉₊] with N hN
  have hN' : (1 / δ) ^ 2 ≤ (N : ℝ) := Nat.ceil_le.mp hN
  have hs : 1 / δ ≤ Real.sqrt N := by
    rw [show 1 / δ = Real.sqrt ((1 / δ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hN'
  have hsN := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have h1 : 1 ≤ δ * Real.sqrt N := by
    rw [div_le_iff₀ hδ] at hs
    linarith
  nlinarith

open Classical in
/-- **Luca–Pomerance Lemma 2.1 (i), counting form.** For every `ε > 0`, eventually
`#{n ≤ N : (i) fails at n} ≤ ε N`. -/
theorem failI_count_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (((Finset.Icc 1 N).filter FailI).card : ℝ) ≤ ε * N := by
  obtain ⟨C, hC, hcount⟩ := card_omegaP_le_exp
  obtain ⟨K, hK, N₁, hSp⟩ := Sp_lower
  -- parameters
  set P₀ : ℕ := ⌈8 / ε⌉₊ + 2 with hP₀def
  have hP₀2 : 2 ≤ P₀ := by omega
  have hP₀ε : 1 / (P₀ : ℝ) ≤ ε / 8 := by
    have h1 : 8 / ε ≤ (P₀ : ℝ) := by
      rw [hP₀def]; push_cast
      have := Nat.le_ceil (8 / ε)
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at h1
    linarith
  obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 32 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set J : ℕ := J₀ + 2 with hJdef
  have hJ2 : 2 ≤ J := by omega
  have h4J : (4 : ℝ) / 2 ^ J ≤ ε / 8 := by
    have e : (4 : ℝ) / 2 ^ J = (1 / 2) ^ J₀ := by
      rw [hJdef, pow_add, one_div_pow]; field_simp; norm_num
    rw [e]; linarith
  -- eventual conditions, as functions of `L = log log N`
  have hsmallL : Tendsto (fun L : ℝ => (P₀ : ℝ) * 2 ^ J * C * Real.exp (K / 2) *
      Real.exp (-(L / (2 * P₀)))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 * P₀ by positivity))
    have h2 := h.const_mul ((P₀ : ℝ) * 2 ^ J * C * Real.exp (K / 2))
    rw [mul_zero] at h2
    exact h2
  have hlargeL : Tendsto (fun L : ℝ => Real.exp (1 + K) * C * GF L) atTop (𝓝 0) := by
    have h2 := tendsto_GF.const_mul (Real.exp (1 + K) * C)
    rw [mul_zero] at h2
    exact h2
  have hEvL : ∀ᶠ L : ℝ in atTop, 1 + Real.log 2 < L ∧ 1 + K ≤ lamF L ∧
      (P₀ : ℝ) * 2 ^ J * C * Real.exp (K / 2) * Real.exp (-(L / (2 * P₀))) ≤ ε / 8 ∧
      Real.exp (1 + K) * C * GF L ≤ ε / 8 := by
    filter_upwards [eventually_gt_atTop (1 + Real.log 2), tendsto_lamF.eventually_ge_atTop (1 + K),
      (hsmallL.eventually_lt_const (show (0 : ℝ) < ε / 8 by positivity)),
      (hlargeL.eventually_lt_const (show (0 : ℝ) < ε / 8 by positivity))] with L h1 h2 h3 h4
    exact ⟨h1, h2, h3.le, h4.le⟩
  have hEvN : ∀ᶠ N : ℕ in atTop,
      (1 + Real.log 2 < Real.log (Real.log N) ∧ 1 + K ≤ lamF (Real.log (Real.log N)) ∧
        (P₀ : ℝ) * 2 ^ J * C * Real.exp (K / 2) *
          Real.exp (-(Real.log (Real.log N) / (2 * P₀))) ≤ ε / 8 ∧
        Real.exp (1 + K) * C * GF (Real.log (Real.log N)) ≤ ε / 8) ∧
      N₁ ≤ N ∧ 3 ≤ N ∧ Real.sqrt N ≤ ε / 8 * N := by
    filter_upwards [tendsto_loglog_nat.eventually hEvL, eventually_ge_atTop N₁,
      eventually_ge_atTop 3, eventually_sqrt_le (ε / 8) (by positivity)] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hEvN
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hL1, hLK, hsmall, hlarge⟩, hN₁, hN3, hsqrtN⟩ := hN₀ N hN
  set L := Real.log (Real.log N) with hLdef
  set lam := lamF L with hlamdef
  set Y := L / lam with hYdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 < L := by linarith
  have hsub0 : 1 < L - Real.log 2 := by linarith
  have hlam1 : 1 ≤ lam := by linarith
  have hlam0 : 0 < lam := by linarith
  have hlamL : lam < L := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L - Real.log 2 by linarith)
    rw [hlamdef]; unfold lamF; linarith
  have hY1 : 1 < Y := by rw [hYdef, one_lt_div hlam0]; exact hlamL
  have hYL : Y ≤ L := by rw [hYdef]; exact div_le_self hL0.le hlam1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- Step 1: the union bound
  set P := Nat.primesLE ⌊Y⌋₊ with hPdef
  have hunion : (Finset.Icc 1 N).filter FailI ⊆
      (Finset.Icc 1 N).filter (fun n => n * n ≤ N) ∪
        P.biUnion (fun p => (Finset.Icc 1 N).filter (FailP p)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨p, hp, hpy, hfail⟩ := hn.2
    rw [Finset.mem_union]
    by_cases hsq : n * n ≤ N
    · exact Or.inl (Finset.mem_filter.mpr ⟨hn.1, hsq⟩)
    · right
      push Not at hsq
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn.1).2
      have hly := lpY_le_of_sq N n hnN hsq hL1
      rw [Finset.mem_biUnion]
      refine ⟨p, ?_, Finset.mem_filter.mpr ⟨hn.1, hfail⟩⟩
      rw [hPdef, Nat.mem_primesLE]
      refine ⟨Nat.le_floor ?_, hp⟩
      calc (p : ℝ) ≤ lpY n := hpy
        _ ≤ L / Real.log (L - Real.log 2) := hly
        _ = Y := rfl
  have hcard1 : (((Finset.Icc 1 N).filter FailI).card : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n => n * n ≤ N)).card : ℝ) +
        ∑ p ∈ P, (((Finset.Icc 1 N).filter (FailP p)).card : ℝ) := by
    have h1 := Finset.card_le_card hunion
    have h2 := Finset.card_union_le ((Finset.Icc 1 N).filter (fun n => n * n ≤ N))
      (P.biUnion (fun p => (Finset.Icc 1 N).filter (FailP p)))
    have h3 := Finset.card_biUnion_le (s := P) (t := fun p => (Finset.Icc 1 N).filter (FailP p))
    have h4 : ((Finset.Icc 1 N).filter FailI).card ≤
        ((Finset.Icc 1 N).filter (fun n => n * n ≤ N)).card +
          ∑ p ∈ P, ((Finset.Icc 1 N).filter (FailP p)).card := by omega
    exact_mod_cast h4
  have hsqcard : (((Finset.Icc 1 N).filter (fun n => n * n ≤ N)).card : ℝ) ≤ Real.sqrt N := by
    have hsub : (Finset.Icc 1 N).filter (fun n => n * n ≤ N) ⊆ Finset.Icc 1 (Nat.sqrt N) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      exact ⟨hn.1.1, Nat.le_sqrt.mpr hn.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    calc (((Finset.Icc 1 N).filter (fun n => n * n ≤ N)).card : ℝ) ≤ (Nat.sqrt N : ℝ) := by
          exact_mod_cast h1
      _ ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  -- Step 2: per-prime bounds
  have hPprops : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [hPdef, Nat.mem_primesLE] at hp
    exact ⟨hp.2, (Nat.le_floor_iff (by linarith)).mp hp.1⟩
  set A := (2 : ℝ) ^ J * C * N * Real.exp (K / 2) * Real.exp (-(L / (2 * P₀))) with hAdef
  set Bc := Real.exp (1 + K) * C * N * (lam / (L - Real.log 2)) with hBdef
  have hsmallp : ∀ p ∈ P, p ≤ P₀ →
      (((Finset.Icc 1 N).filter (FailP p)).card : ℝ) ≤ (N : ℝ) * (1 / (p : ℝ) ^ J) + A := by
    intro p hpP hpP₀
    obtain ⟨hp, hpY⟩ := hPprops p hpP
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hSpp := hSp N hN₁ p hp (hpY.trans hYL)
    have h1 := card_failP_le p N J hp
    have h2 := hcount p (1 / 2) (by norm_num) (by norm_num) (J - 1) N (by omega)
    have hexp : Real.exp (-(1 - 1 / 2) * Sp p N) ≤
        Real.exp (K / 2) * Real.exp (-(L / (2 * P₀))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hpP₀' : (p : ℝ) - 1 ≤ P₀ := by
        have : (p : ℝ) ≤ P₀ := by exact_mod_cast hpP₀
        linarith
      have hLp : L / P₀ ≤ L / ((p : ℝ) - 1) := div_le_div_of_nonneg_left hL0.le hp1 hpP₀'
      have e : L / (2 * P₀) = (L / P₀) / 2 := by ring
      rw [e]
      linarith
    have hpow : (1 : ℝ) / (1 / 2) ^ (J - 1) ≤ 2 ^ J := by
      rw [one_div_pow, one_div_one_div]
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    have h3 : C * N * Real.exp (-(1 - 1 / 2) * Sp p N) / (1 / 2) ^ (J - 1) ≤ A := by
      rw [hAdef]
      rw [div_eq_mul_one_div]
      have hCN : 0 ≤ C * N := by positivity
      calc C * N * Real.exp (-(1 - 1 / 2) * Sp p N) * (1 / (1 / 2) ^ (J - 1))
          ≤ C * N * (Real.exp (K / 2) * Real.exp (-(L / (2 * P₀)))) * 2 ^ J := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hCN) hpow (by positivity)
            positivity
        _ = _ := by ring
    have e : (N : ℝ) / (p : ℝ) ^ J = (N : ℝ) * (1 / (p : ℝ) ^ J) := by ring
    linarith
  have hlargep : ∀ p ∈ P, ¬ p ≤ P₀ →
      (((Finset.Icc 1 N).filter (FailP p)).card : ℝ) ≤ (N : ℝ) * (1 / (p : ℝ) ^ 2) + Bc := by
    intro p hpP _
    obtain ⟨hp, hpY⟩ := hPprops p hpP
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hSpp := hSp N hN₁ p hp (hpY.trans hYL)
    have h1 := card_failP_le p N 2 hp
    set s₀ := L / ((p : ℝ) - 1) - K with hs₀
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hs₀lam : lam - K ≤ s₀ := by
      have h1 : L / (p : ℝ) ≤ L / ((p : ℝ) - 1) :=
        div_le_div_of_nonneg_left hL0.le hp1 (by linarith)
      have h2 : L / Y ≤ L / (p : ℝ) := div_le_div_of_nonneg_left hL0.le (by linarith) hpY
      have h3 : L / Y = lam := by rw [hYdef]; field_simp
      rw [hs₀]; linarith
    have hs₀1 : 1 ≤ s₀ := by linarith
    have hs₀0 : 0 < s₀ := by linarith
    have hz0 : 0 < 1 / s₀ := by positivity
    have hz1 : 1 / s₀ ≤ 1 := by rw [div_le_one hs₀0]; exact hs₀1
    have h2 := hcount p (1 / s₀) hz0 hz1 (2 - 1) N (by omega)
    have hexp1 : -(1 - 1 / s₀) * Sp p N ≤ 1 - s₀ := by
      have hc : 0 ≤ 1 - 1 / s₀ := by linarith
      have := mul_le_mul_of_nonneg_left hSpp hc
      have e : (1 - 1 / s₀) * s₀ = s₀ - 1 := by field_simp
      nlinarith
    have hmono := mul_exp_neg_le (t := lam - K) (s := s₀) (by linarith) hs₀lam
    have hexplam : Real.exp (-lam) = 1 / (L - Real.log 2) := by
      rw [hlamdef, Real.exp_neg]; unfold lamF
      rw [Real.exp_log (by linarith), one_div]
    have h3 : C * N * Real.exp (-(1 - 1 / s₀) * Sp p N) / (1 / s₀) ^ (2 - 1) ≤ Bc := by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, div_div_eq_mul_div, div_one]
      have hCN : 0 ≤ C * N := by positivity
      calc C * N * Real.exp (-(1 - 1 / s₀) * Sp p N) * s₀
          ≤ C * N * Real.exp (1 - s₀) * s₀ := by
            apply mul_le_mul_of_nonneg_right _ hs₀0.le
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp1) hCN
        _ = C * N * Real.exp 1 * (s₀ * Real.exp (-s₀)) := by
            rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ C * N * Real.exp 1 * ((lam - K) * Real.exp (-(lam - K))) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = C * N * Real.exp (1 + K) * ((lam - K) * Real.exp (-lam)) := by
            rw [neg_sub, sub_eq_add_neg K lam, Real.exp_add K, Real.exp_add 1]; ring
        _ ≤ C * N * Real.exp (1 + K) * (lam * Real.exp (-lam)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = Bc := by rw [hexplam, hBdef]; ring
    have e : (N : ℝ) / (p : ℝ) ^ 2 = (N : ℝ) * (1 / (p : ℝ) ^ 2) := by ring
    linarith
  -- Step 3: sum the per-prime bounds
  have hsum : ∑ p ∈ P, (((Finset.Icc 1 N).filter (FailP p)).card : ℝ) ≤
      ∑ p ∈ P.filter (fun p => p ≤ P₀), ((N : ℝ) * (1 / (p : ℝ) ^ J) + A) +
        ∑ p ∈ P.filter (fun p => ¬ p ≤ P₀), ((N : ℝ) * (1 / (p : ℝ) ^ 2) + Bc) := by
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ P₀)]
    apply add_le_add
    · exact Finset.sum_le_sum fun p hp =>
        hsmallp p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
    · exact Finset.sum_le_sum fun p hp =>
        hlargep p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hS1 : ∑ p ∈ P.filter (fun p => p ≤ P₀), ((N : ℝ) * (1 / (p : ℝ) ^ J) + A) ≤
      (N : ℝ) * (4 / 2 ^ J) + (P₀ : ℝ) * A := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ hN0
      apply sum_inv_pow_le _ J hJ2
      intro p hp
      exact (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).two_le
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : P.filter (fun p => p ≤ P₀) ⊆ Finset.Icc 1 P₀ := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_Icc]
        exact ⟨(Nat.prime_of_mem_primesLE hp.1).one_le, hp.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact_mod_cast this
  have hpi : ((P.card : ℕ) : ℝ) ≤ Real.log 4 * Y / Real.log (Real.sqrt Y) + Real.sqrt Y := by
    rw [hPdef, Nat.primesLE_card_eq_primeCounting]
    exact Chebyshev.pi_le_log4_mul_div hY1
  have hS2 : ∑ p ∈ P.filter (fun p => ¬ p ≤ P₀), ((N : ℝ) * (1 / (p : ℝ) ^ 2) + Bc) ≤
      (N : ℝ) * (1 / (P₀ : ℝ)) + Real.exp (1 + K) * C * GF L * N := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ hN0
      apply sum_inv_sq_le_of_gt _ P₀ (by omega)
      intro p hp
      exact not_le.mp (Finset.mem_filter.mp hp).2
    · have hcard : (((P.filter (fun p => ¬ p ≤ P₀)).card : ℕ) : ℝ) ≤ (P.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hBc0 : 0 ≤ Bc := by rw [hBdef]; positivity
      have hGF : GF L = (Real.log 4 * Y / Real.log (Real.sqrt Y) + Real.sqrt Y) *
          (lam / (L - Real.log 2)) := rfl
      calc (((P.filter (fun p => ¬ p ≤ P₀)).card : ℕ) : ℝ) * Bc ≤ (P.card : ℝ) * Bc :=
            mul_le_mul_of_nonneg_right hcard hBc0
        _ ≤ (Real.log 4 * Y / Real.log (Real.sqrt Y) + Real.sqrt Y) * Bc :=
            mul_le_mul_of_nonneg_right hpi hBc0
        _ = Real.exp (1 + K) * C * GF L * N := by rw [hGF, hBdef]; ring
  -- assemble
  have hA' : (P₀ : ℝ) * A ≤ ε / 8 * N := by
    have e : (P₀ : ℝ) * A = ((P₀ : ℝ) * 2 ^ J * C * Real.exp (K / 2) *
        Real.exp (-(L / (2 * P₀)))) * N := by rw [hAdef]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hsmall hN0
  have hB' : Real.exp (1 + K) * C * GF L * N ≤ ε / 8 * N :=
    mul_le_mul_of_nonneg_right hlarge hN0
  have hJ' : (N : ℝ) * (4 / 2 ^ J) ≤ ε / 8 * N := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right h4J hN0
  have hP' : (N : ℝ) * (1 / (P₀ : ℝ)) ≤ ε / 8 * N := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hP₀ε hN0
  have hεN : 0 ≤ ε / 8 * N := by positivity
  linarith

end Principia.Common.LucaPomerance.LP21
