/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Lemma21Part1

set_option autoImplicit false

/-!
# Luca–Pomerance Lemma 2.1 (ii): `gcd(n, σ(n))` is `y(n)`-smooth, almost always

`FailII n`: some prime `r > y(n)` divides both `n` and `σ(n)`.
`failII_count_le`: for every `ε > 0`, eventually `#{n ≤ N : FailII n} ≤ ε N`.

Proof (see `Campaigns/Erdos-1054/LP21-PLAN.md` §3). For `n ∈ (√N, N]`, `y(n) ≥ Y₁ =
(L − log 2)/log L` (`le_lpY_of_sq`). A prime `r > Y₁` dividing `n` and `σ(n)` divides
`σ(q^k)` for some `q^k ∥ n` (`failII_cases`):
* (a) `k = 1`: `r ∣ q + 1` and `rq ∣ n`. For `r ≤ M = L log L` the trivial count `N/r` summed
  with Mertens' second theorem with explicit error (`sum_prime_inv_Ioc_le`) is
  `≤ N (log(M/Y₁) + 2C)/log Y₁ → 0`. For `r > M` the count is `(N/r) S_r(N)`, and
  `S_r(N) ≤ (2/r)(c₁ + √r) + (L + K)/(r − 1)` for `r ≤ (log N)²` (`Sp_upper`, Mertens in
  progressions at `B = 2`), `S_r(N) ≤ (2/r)(1 + log(N+1))` always (`Sp_le_trivial`).
* (b) `k ≥ 2`, `q > T`: `q² ∣ n`, total `≤ N/T`.
* (c) `q ≤ T`: `q^k > Y₁/T`, total `≤ T² N/Y₁`.
-/

namespace Principia.Common.LucaPomerance.LP21

open Finset Real ArithmeticFunction Filter
open scoped Topology

/-- (ii) fails at `n`: a prime `r > y(n)` divides `n` and `σ(n)`. -/
def FailII (n : ℕ) : Prop := ∃ r : ℕ, r.Prime ∧ lpY n < r ∧ r ∣ n ∧ r ∣ sigma 1 n

/-! ## `y(n)` from below on `(√N, N]` -/

theorem le_lpY_of_sq (N n : ℕ) (hnN : n ≤ N) (hsq : N < n * n)
    (hL : 1 + Real.log 2 < Real.log (Real.log N)) :
    (Real.log (Real.log N) - Real.log 2) / Real.log (Real.log (Real.log N)) ≤ lpY n := by
  set LN := Real.log (Real.log N) with hLN
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
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
  have hLLn : 1 < Real.log (Real.log n) := by linarith
  have hden0 : 0 < Real.log (Real.log (Real.log n)) := Real.log_pos hLLn
  have hden : Real.log (Real.log (Real.log n)) ≤ Real.log LN :=
    Real.log_le_log (by linarith) hLn_le
  unfold lpY
  exact div_le_div₀ (by linarith) hLn_ge.le hden0 hden

/-! ## Mertens' second theorem on a window -/

theorem sum_prime_inv_Ioc_le (Y M : ℝ) (hY : 2 ≤ Y) (hYM : Y ≤ M) :
    ∑ r ∈ (Finset.Ioc ⌊Y⌋₊ ⌊M⌋₊).filter Nat.Prime, (1 : ℝ) / r ≤
      (Real.log M - Real.log Y) / Real.log Y +
        2 * ((Real.log 4 + 6 + Mertens.E₁) / Real.log Y) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogYM : Real.log Y ≤ Real.log M := Real.log_le_log hY0 hYM
  have hfl : ⌊Y⌋₊ ≤ ⌊M⌋₊ := Nat.floor_le_floor hYM
  have hsplit : ∑ r ∈ (Finset.Ioc 0 ⌊M⌋₊).filter Nat.Prime, (1 : ℝ) / r =
      ∑ r ∈ (Finset.Ioc 0 ⌊Y⌋₊).filter Nat.Prime, (1 : ℝ) / r +
        ∑ r ∈ (Finset.Ioc ⌊Y⌋₊ ⌊M⌋₊).filter Nat.Prime, (1 : ℝ) / r := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hM := Mertens.sum_prime_div_eq M
  have hYs := Mertens.sum_prime_div_eq Y
  have hEM := Mertens.E₂p.abs_le (show 2 ≤ M by linarith)
  have hEY := Mertens.E₂p.abs_le hY
  have hE₁ : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
  have hC : 0 ≤ Real.log 4 + 6 + Mertens.E₁ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hEM' : Mertens.E₂p M ≤ (Real.log 4 + 6 + Mertens.E₁) / Real.log Y := by
    have h1 := (abs_le.mp hEM).2
    have h2 : (Real.log 4 + 6 + Mertens.E₁) / Real.log M ≤
        (Real.log 4 + 6 + Mertens.E₁) / Real.log Y :=
      div_le_div_of_nonneg_left hC hlogY hlogYM
    linarith
  have hEY' : -Mertens.E₂p Y ≤ (Real.log 4 + 6 + Mertens.E₁) / Real.log Y := by
    have h1 := (abs_le.mp hEY).1
    linarith
  have hloglog : Real.log (Real.log M) - Real.log (Real.log Y) ≤
      (Real.log M - Real.log Y) / Real.log Y := by
    rw [← Real.log_div (by linarith) hlogY.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log M / Real.log Y by
      apply div_pos (by linarith) hlogY)
    have e : Real.log M / Real.log Y - 1 = (Real.log M - Real.log Y) / Real.log Y := by
      field_simp
    linarith
  linarith

/-! ## `S_r(T)`: the trivial bound -/

theorem sum_Icc_inv_le (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [← e]
  exact h

/-- `S_r(T) ≤ (2/r)(1 + log(T+1))`. -/
theorem Sp_le_trivial (r T : ℕ) (hr : 1 ≤ r) :
    Sp r T ≤ (2 / r) * (1 + Real.log ((T : ℝ) + 1)) := by
  classical
  unfold Sp
  set S := (Nat.primesLE T).filter (fun q => r ∣ q + 1) with hSdef
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set j : ℕ → ℕ := fun q => (q + 1) / r with hjdef
  have hjmul : ∀ q ∈ S, ((q : ℝ) + 1) = r * (j q : ℝ) := by
    intro q hq
    have hd := (Finset.mem_filter.mp hq).2
    have := Nat.div_mul_cancel hd
    rw [hjdef]
    have h2 : ((q + 1 : ℕ) : ℝ) = (((q + 1) / r : ℕ) : ℝ) * r := by exact_mod_cast this.symm
    push_cast at h2
    linarith
  have hterm : ∀ q ∈ S, (1 : ℝ) / q ≤ (2 / r) * (1 / (j q : ℝ)) := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by
      exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1).one_le
    have hj := hjmul q hq
    have hj0 : (0 : ℝ) < (j q : ℝ) := by
      have : (0 : ℝ) < (q : ℝ) + 1 := by linarith
      rw [hj] at this
      exact pos_of_mul_pos_right this hr0.le
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by linarith) (by positivity), one_mul]
    have e : (j q : ℝ) * r = (q : ℝ) + 1 := by rw [hj]; ring
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hinj : Set.InjOn j S := by
    intro a ha b hb hab
    have h1 := hjmul a ha
    have h2 := hjmul b hb
    have : (a : ℝ) = b := by
      have : ((a : ℝ) + 1) = (b : ℝ) + 1 := by rw [h1, h2, hab]
      linarith
    exact_mod_cast this
  rw [← Finset.sum_image (f := fun i : ℕ => (1 : ℝ) / (i : ℝ)) hinj]
  have hsub : S.image j ⊆ Finset.Icc 1 (T + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨q, hq, rfl⟩ := hi
    have hqT : q ≤ T := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hq).1
    have hd := (Finset.mem_filter.mp hq).2
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) hr
    · exact le_trans (Nat.div_le_self _ _) (by omega)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)).trans ?_
  have := sum_Icc_inv_le (T + 1)
  push_cast at this
  exact this

/-! ## `∑ k^{−3/2}` -/

theorem sum_Ioc_inv_mul_sqrt_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, (1 : ℝ) / ((k : ℝ) * Real.sqrt k) ≤
      2 / Real.sqrt a - 2 / Real.sqrt b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb]
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast le_trans ha hb
    set s := Real.sqrt b with hs
    set t := Real.sqrt ((b : ℝ) + 1) with ht
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
    have hss : s * s = b := Real.mul_self_sqrt (by linarith)
    have htt : t * t = (b : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
    have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
    have hcast : Real.sqrt (((b + 1 : ℕ) : ℝ)) = t := by rw [ht, Nat.cast_add, Nat.cast_one]
    have hcast2 : (((b + 1 : ℕ) : ℝ)) = t * t := by rw [htt, Nat.cast_add, Nat.cast_one]
    have hdiff : (t - s) * (t + s) = 1 := by nlinarith
    have h1 : 0 < t + s := by positivity
    have h2 : (2 * (t - s) * (t * t * t) - s * t) * (t + s) = t * (t - s) * (2 * t + s) := by
      linear_combination (2 * t ^ 3) * hdiff
    have h3 : 0 ≤ t * (t - s) * (2 * t + s) :=
      mul_nonneg (mul_nonneg ht0.le (sub_nonneg.mpr hst)) (by linarith)
    have hkey : s * t ≤ 2 * (t - s) * (t * t * t) := by nlinarith
    have hstep : (1 : ℝ) / (((b + 1 : ℕ) : ℝ) * t) ≤ 2 / s - 2 / t := by
      rw [hcast2, div_sub_div _ _ hs0.ne' ht0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hcast]
    linarith

theorem sum_inv_mul_sqrt_le_of_gt (s : Finset ℕ) (a : ℕ) (ha : 1 ≤ a) (hs : ∀ k ∈ s, a < k) :
    ∑ k ∈ s, (1 : ℝ) / ((k : ℝ) * Real.sqrt k) ≤ 2 / Real.sqrt a := by
  set b := max a (s.sup id)
  have hsub : s ⊆ Finset.Ioc a b := by
    intro k hk
    rw [Finset.mem_Ioc]
    exact ⟨hs k hk, le_trans (Finset.le_sup (f := id) hk) (le_max_right _ _)⟩
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => by positivity :
      ∀ k ∈ Finset.Ioc a b, k ∉ s → (0 : ℝ) ≤ 1 / ((k : ℝ) * Real.sqrt k))
  have h2 := sum_Ioc_inv_mul_sqrt_le a b ha (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ 2 / Real.sqrt b := by positivity
  linarith

/-! ## `S_r(N)` from above, for `r ≤ (log N)²` -/

theorem Sp_upper :
    ∃ K c₁ : ℝ, 0 < K ∧ 0 < c₁ ∧ ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → ∀ r : ℕ, r.Prime →
      (r : ℝ) ≤ Real.log N ^ 2 →
        Sp r N ≤ (2 / r) * (c₁ + Real.sqrt r) + (Real.log (Real.log N) + K) / ((r : ℝ) - 1) := by
  classical
  obtain ⟨K, hK, T₀, hT₀3, hmap⟩ := mertens_AP_primes 2 (by norm_num)
  have hT₀2 : (0 : ℝ) ≤ Real.log ((T₀ : ℝ) + 2) := Real.log_nonneg (by linarith)
  refine ⟨K, 1 + Real.log ((T₀ : ℝ) + 2), hK, by positivity, T₀, ?_⟩
  intro N hN r hr hrN
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hN3 : 3 ≤ N := le_trans hT₀3 hN
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le hN3
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.one_le
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  set T := max T₀ ⌈Real.exp (Real.sqrt r)⌉₊ with hTdef
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hT3 : 3 ≤ T := le_trans hT₀3 hT₀T
  have hsqrtr : Real.sqrt r ≤ Real.log N := by
    rw [show Real.log N = Real.sqrt (Real.log N ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hrN
  have hTN : T ≤ N := by
    refine max_le hN (Nat.ceil_le.mpr ?_)
    calc Real.exp (Real.sqrt r) ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hsqrtr
      _ = N := Real.exp_log hN0
  have hTge : Real.exp (Real.sqrt r) ≤ (T : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right T₀ ⌈Real.exp (Real.sqrt r)⌉₊)
  have hlogT : Real.sqrt r ≤ Real.log T := by
    calc Real.sqrt r = Real.log (Real.exp (Real.sqrt r)) := (Real.log_exp _).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hTge
  have hrT : (r : ℝ) ≤ Real.log T ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hlogT 2
    rwa [Real.sq_sqrt (by linarith)] at h
  have hunit : IsUnit (-1 : ZMod r) := isUnit_one.neg
  have hAP := (hmap r (-1 : ZMod r) hunit T N hT₀T hTN hrT).1
  have hφ : ((r.totient : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.totient_prime hr, Nat.cast_sub hr.one_le, Nat.cast_one]
  rw [hφ] at hAP
  -- split `S_r(N)` at `T`
  have hsplit : Sp r N ≤ Sp r T +
      ∑ q ∈ (Finset.Ioc T N).filter (fun q : ℕ => q.Prime ∧ (-1 : ZMod r) = ((q : ZMod r))),
        (1 : ℝ) / q := by
    unfold Sp
    have hdisj : Disjoint ((Nat.primesLE T).filter (fun q => r ∣ q + 1))
        ((Finset.Ioc T N).filter (fun q : ℕ => q.Prime ∧ (-1 : ZMod r) = ((q : ZMod r)))) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      have h1 := Nat.le_of_mem_primesLE (Finset.mem_filter.mp hq1).1
      have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq2).1).1
      omega
    rw [← Finset.sum_union hdisj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [Finset.mem_filter, Nat.mem_primesLE] at hq
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Nat.mem_primesLE,
        Finset.mem_Ioc]
      by_cases hqT : q ≤ T
      · exact Or.inl ⟨⟨hqT, hq.1.2⟩, hq.2⟩
      · exact Or.inr ⟨⟨by omega, hq.1.1⟩, hq.1.2, (neg_one_eq_cast_iff r q).mpr hq.2⟩
    · intro q _ _
      positivity
  -- the two pieces
  have hloglogT : 0 ≤ Real.log (Real.log T) :=
    Real.log_nonneg (one_le_log_of_three_le hT3)
  have hpiece2 : ∑ q ∈ (Finset.Ioc T N).filter
      (fun q : ℕ => q.Prime ∧ (-1 : ZMod r) = ((q : ZMod r))), (1 : ℝ) / q ≤
      (Real.log (Real.log N) + K) / ((r : ℝ) - 1) := by
    refine hAP.trans (div_le_div_of_nonneg_right ?_ (by linarith))
    linarith
  have hT1 : (T : ℝ) + 1 ≤ ((T₀ : ℝ) + 2) * Real.exp (Real.sqrt r) := by
    have he1 : (1 : ℝ) ≤ Real.exp (Real.sqrt r) := Real.one_le_exp (Real.sqrt_nonneg _)
    rcases le_total T₀ ⌈Real.exp (Real.sqrt r)⌉₊ with hle | hle
    · have hT : T = ⌈Real.exp (Real.sqrt r)⌉₊ := max_eq_right hle
      rw [hT]
      have h1 := (Nat.ceil_lt_add_one (Real.exp_pos (Real.sqrt r)).le).le
      have hT₀0 : (3 : ℝ) ≤ T₀ := by exact_mod_cast hT₀3
      nlinarith
    · have hT : T = T₀ := max_eq_left hle
      rw [hT]
      have hT₀0 : (3 : ℝ) ≤ T₀ := by exact_mod_cast hT₀3
      nlinarith
  have hlogT1 : Real.log ((T : ℝ) + 1) ≤ Real.log ((T₀ : ℝ) + 2) + Real.sqrt r := by
    calc Real.log ((T : ℝ) + 1) ≤ Real.log (((T₀ : ℝ) + 2) * Real.exp (Real.sqrt r)) :=
          Real.log_le_log (by positivity) hT1
      _ = Real.log ((T₀ : ℝ) + 2) + Real.sqrt r := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hpiece1 : Sp r T ≤ (2 / r) * (1 + Real.log ((T₀ : ℝ) + 2) + Real.sqrt r) := by
    refine (Sp_le_trivial r T hr.one_le).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

/-! ## The case split for (ii) -/

/-- A prime `r > Y` dividing `n` and `σ(n)` gives one of three configurations. -/
theorem failII_cases (n : ℕ) (hn : n ≠ 0) (Y : ℝ) (T : ℕ) (hT : 1 ≤ T) (r : ℕ)
    (hr : r.Prime) (hrY : Y < r) (hrn : r ∣ n) (hrσ : r ∣ sigma 1 n) :
    (∃ q : ℕ, q.Prime ∧ r ∣ q + 1 ∧ r * q ∣ n) ∨
    (∃ q : ℕ, q.Prime ∧ T < q ∧ q ^ 2 ∣ n) ∨
    (∃ q k : ℕ, q.Prime ∧ q ≤ T ∧ 1 ≤ k ∧ q ^ k ∣ n ∧ Y / T < (q : ℝ) ^ k) := by
  obtain ⟨q, hq, hrq⟩ := exists_prime_pow_of_dvd_sigma hn hr hrσ
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  set k := n.factorization q with hk
  have hk1 : 1 ≤ k := (hqp.dvd_iff_one_le_factorization hn).mp hqn
  have hqkn : q ^ k ∣ n := Nat.ordProj_dvd n q
  by_cases hk2 : k = 1
  · left
    rw [hk2, pow_one, sigma_one_prime hqp] at hrq
    have hne : r ≠ q := by
      rintro rfl
      have : r ∣ 1 := (Nat.dvd_add_right (dvd_refl r)).mp hrq
      exact hr.one_lt.ne' (Nat.dvd_one.mp this)
    have hcop : Nat.Coprime r q := (Nat.coprime_primes hr hqp).mpr hne
    exact ⟨q, hqp, hrq, hcop.mul_dvd_of_dvd_of_dvd hrn hqn⟩
  · right
    by_cases hqT : T < q
    · left
      have h2 : q ^ 2 ∣ q ^ k := pow_dvd_pow q (by omega)
      exact ⟨q, hqp, hqT, h2.trans hqkn⟩
    · right
      push Not at hqT
      refine ⟨q, k, hqp, hqT, hk1, hqkn, ?_⟩
      have hσpos : 0 < sigma 1 (q ^ k) := by
        rw [sigma_pos_iff]; exact pow_pos hqp.pos k
      have hrle : r ≤ sigma 1 (q ^ k) := Nat.le_of_dvd hσpos hrq
      have hlt := sigma_prime_pow_lt hqp k
      have h1 : (r : ℝ) < (q : ℝ) ^ (k + 1) := by exact_mod_cast lt_of_le_of_lt hrle hlt
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      have hqT' : (q : ℝ) ≤ T := by exact_mod_cast hqT
      rw [div_lt_iff₀ hT0]
      have hqk0 : (0 : ℝ) ≤ (q : ℝ) ^ k := by positivity
      calc Y < r := hrY
        _ < (q : ℝ) ^ (k + 1) := h1
        _ = (q : ℝ) ^ k * q := pow_succ _ _
        _ ≤ (q : ℝ) ^ k * T := mul_le_mul_of_nonneg_left hqT' hqk0

/-! ## Asymptotics in `L = log log N` -/

/-- `Y₁(L) = (L − log 2)/log L`, the lower bound for `y(n)` on `(√N, N]`. -/
noncomputable def Y1F (L : ℝ) : ℝ := (L - Real.log 2) / Real.log L

/-- `M(L) = L log L`, where the trivial bound hands over to the progression bound. -/
noncomputable def MMF (L : ℝ) : ℝ := L * Real.log L

theorem tendsto_log_div_self : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa using this

theorem tendsto_loglog_div_log :
    Tendsto (fun L : ℝ => Real.log (Real.log L) / Real.log L) atTop (𝓝 0) :=
  tendsto_log_div_self.comp Real.tendsto_log_atTop

theorem tendsto_Y1F : Tendsto Y1F atTop atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2 : Tendsto (fun L : ℝ => Real.log L / (L - Real.log 2)) atTop (𝓝 0) := by
    have h := tendsto_log_div_self.mul tendsto_ratio_sub_log_two
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (Real.log 2 + 1)] with L hL
    have hL0 : L ≠ 0 := by linarith
    have hL1 : L - Real.log 2 ≠ 0 := by linarith
    field_simp
  have hpos : ∀ᶠ L : ℝ in atTop, 0 < Real.log L / (L - Real.log 2) := by
    filter_upwards [eventually_gt_atTop (Real.log 2 + 2)] with L hL
    have h1 : 0 < Real.log L := Real.log_pos (by linarith)
    have h2 : 0 < L - Real.log 2 := by linarith
    positivity
  have h := (tendsto_nhdsWithin_iff.mpr ⟨h2, hpos⟩).inv_tendsto_nhdsGT_zero
  refine h.congr (fun L => ?_)
  simp [Y1F, inv_div]

/-- Eventually `log Y₁(L) ≥ (log L)/2`. -/
theorem eventually_log_Y1F :
    ∀ᶠ L : ℝ in atTop, (1 / 2) * Real.log L ≤ Real.log (Y1F L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlim : Tendsto (fun L : ℝ => (Real.log 2 + Real.log (Real.log L)) / Real.log L) atTop
      (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop
    have h2 := h.add tendsto_loglog_div_log
    rw [add_zero] at h2
    refine h2.congr (fun L => ?_)
    ring
  filter_upwards [hlim.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_gt_atTop (Real.exp 1 + 2 * Real.log 2)] with L h1 hL
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hL0 : 0 < L := by linarith
  have hlogL : 1 < Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log he (by linarith)
  have hsub : L / 2 ≤ L - Real.log 2 := by linarith
  have h2 : Real.log L - Real.log 2 ≤ Real.log (L - Real.log 2) := by
    rw [← Real.log_div hL0.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) hsub
  have h3 : Real.log (Y1F L) = Real.log (L - Real.log 2) - Real.log (Real.log L) := by
    unfold Y1F
    rw [Real.log_div (by linarith) (by linarith)]
  rw [div_le_iff₀ (by linarith)] at h1
  rw [h3]
  linarith

/-- The window `(Y₁, M]` of Mertens' second theorem costs `o(1)`. -/
theorem eventually_a1 (C : ℝ) (hC : 0 ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ Y1F L ∧ Y1F L ≤ MMF L ∧
      (Real.log (MMF L) - Real.log (Y1F L)) / Real.log (Y1F L) + 2 * (C / Real.log (Y1F L)) ≤
        δ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlim : Tendsto (fun L : ℝ =>
      (2 * Real.log (Real.log L) + Real.log 2 + 2 * C) / ((1 / 2) * Real.log L)) atTop (𝓝 0) := by
    have h1 := tendsto_loglog_div_log.const_mul 4
    have h2 := (tendsto_const_nhds (x := 2 * Real.log 2 + 4 * C)).div_atTop Real.tendsto_log_atTop
    have h3 := h1.add h2
    rw [mul_zero, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    have : Real.log L ≠ 0 := (Real.log_pos hL).ne'
    field_simp
    ring
  filter_upwards [tendsto_Y1F.eventually_ge_atTop 2, eventually_log_Y1F,
    hlim.eventually_le_const hδ, eventually_gt_atTop (Real.exp 1 + 2 * Real.log 2)]
    with L hY2 hlogY hbound hL
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hL0 : 0 < L := by linarith
  have hlogL : 1 < Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log he (by linarith)
  have hY1le : Y1F L ≤ L - Real.log 2 := by
    unfold Y1F
    exact div_le_self (by linarith) hlogL.le
  have hYM : Y1F L ≤ MMF L := by
    unfold MMF
    have : L ≤ L * Real.log L := le_mul_of_one_le_right hL0.le hlogL.le
    linarith
  refine ⟨hY2, hYM, ?_⟩
  have hY0 : 0 < Y1F L := by linarith
  have hlogY0 : 0 < Real.log (Y1F L) := by linarith
  have hsub : L ≤ 2 * (L - Real.log 2) := by linarith
  have hlogsub : Real.log L ≤ Real.log 2 + Real.log (L - Real.log 2) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hL0 hsub
  have hdiff : Real.log (MMF L) - Real.log (Y1F L) ≤ 2 * Real.log (Real.log L) + Real.log 2 := by
    unfold MMF Y1F
    rw [Real.log_mul hL0.ne' (by linarith), Real.log_div (by linarith) (by linarith)]
    linarith
  have hnum0 : 0 ≤ Real.log (MMF L) - Real.log (Y1F L) :=
    sub_nonneg.mpr (Real.log_le_log hY0 hYM)
  have e : (Real.log (MMF L) - Real.log (Y1F L)) / Real.log (Y1F L) + 2 * (C / Real.log (Y1F L)) =
      (Real.log (MMF L) - Real.log (Y1F L) + 2 * C) / Real.log (Y1F L) := by
    field_simp
  rw [e]
  refine le_trans ?_ hbound
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) hlogY

/-- The progression part `r > M` costs `o(1)`. -/
theorem eventually_a2 (c K δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ MMF L ∧
      (2 * c + 2 * (L + K)) / (MMF L - 1) + 4 / Real.sqrt (MMF L - 1) ≤ δ := by
  have hMM : Tendsto (fun L : ℝ => MMF L - 1) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      ((tendsto_atTop_add_const_right atTop (-1) tendsto_id))
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
    have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
    have hlogL : 1 ≤ Real.log L := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hL
    have : L ≤ L * Real.log L := le_mul_of_one_le_right hL0.le hlogL
    unfold MMF
    simp only [id]
    linarith
  have h1 : Tendsto (fun L : ℝ => (2 * c + 2 * (L + K)) / (MMF L - 1)) atTop (𝓝 0) := by
    have hnum : Tendsto (fun L : ℝ => 2 * c / L + 2 + 2 * K / L) atTop (𝓝 2) := by
      have ha := (tendsto_const_nhds (x := 2 * c)).div_atTop tendsto_id
      have hb := (tendsto_const_nhds (x := 2 * K)).div_atTop tendsto_id
      have := (ha.add (tendsto_const_nhds (x := (2 : ℝ)))).add hb
      simpa using this
    have hden : Tendsto (fun L : ℝ => Real.log L - 1 / L) atTop atTop := by
      have h := Real.tendsto_log_atTop.atTop_add (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg
      refine h.congr (fun L => ?_)
      rw [one_div, sub_eq_add_neg]
    refine (hnum.div_atTop hden).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    unfold MMF
    have hne : L * Real.log L - 1 = L * (Real.log L - 1 / L) := by field_simp
    rw [hne]
    field_simp
    ring
  have h2 : Tendsto (fun L : ℝ => 4 / Real.sqrt (MMF L - 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (4 : ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp hMM)
  have h3 := h1.add h2
  rw [add_zero] at h3
  filter_upwards [h3.eventually_le_const hδ, hMM.eventually_ge_atTop 1] with L h4 h5
  exact ⟨by linarith, h4⟩

/-- The very large primes `r > (log N)²` cost `o(1)`. -/
theorem eventually_a3 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ ⌊Real.log N ^ 2⌋₊ ∧
      2 * (1 + Real.log ((N : ℝ) + 1)) / (⌊Real.log N ^ 2⌋₊ : ℝ) ≤ δ := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => 8 / Real.log N) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (8 : ℝ))).div_atTop hlogN
  filter_upwards [hlim.eventually_le_const hδ, hlogN.eventually_ge_atTop 2,
    eventually_ge_atTop 1] with N h1 h2 hN1
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h2' : Real.log 2 ≠ 1 := by
      intro h
      have := Real.exp_one_gt_d9
      have e := Real.exp_log (show (0 : ℝ) < 2 by norm_num)
      rw [h] at e
      linarith
    exact lt_of_le_of_ne (by linarith) h2'
  set v := Real.log N with hv
  have hv2 : (4 : ℝ) ≤ v ^ 2 := by nlinarith
  have hW : v ^ 2 - 1 < (⌊v ^ 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (v ^ 2)
    linarith
  have hW1 : 1 ≤ ⌊v ^ 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  refine ⟨hW1, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + v := by
    rw [hv, ← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_le_log (by positivity) (by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      linarith)
  have hWpos : (0 : ℝ) < (⌊v ^ 2⌋₊ : ℝ) := by exact_mod_cast hW1
  rw [div_le_iff₀ hWpos]
  rw [div_le_iff₀ (by linarith)] at h1
  have hWge : v ^ 2 / 2 ≤ (⌊v ^ 2⌋₊ : ℝ) := by linarith
  have hkey : 2 * (1 + Real.log ((N : ℝ) + 1)) ≤ 8 / v * (v ^ 2 / 2) := by
    rw [div_mul_div_comm, show (8 : ℝ) * v ^ 2 / (v * 2) = 4 * v by field_simp; ring]
    linarith
  have h8 : 0 ≤ 8 / v := by positivity
  nlinarith

/-! ## The density bound for (ii) -/

/-- `#{n ≤ N : n² ≤ N} ≤ √N`. -/
theorem card_filter_sq_le (N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => n * n ≤ N)).card : ℝ) ≤ Real.sqrt N := by
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

/-- `(1/r)((2/r)(c + √r) + A/(r−1)) ≤ 2c/r² + 2/(r√r) + 2A/r²` for `r ≥ 2`, `A, c ≥ 0`. -/
theorem per_r_bound (r c A : ℝ) (hr : 2 ≤ r) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    (1 / r) * ((2 / r) * (c + Real.sqrt r) + A / (r - 1)) ≤
      2 * c * (1 / r ^ 2) + 2 * (1 / (r * Real.sqrt r)) + 2 * A * (1 / r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  have hinv : (1 : ℝ) / (r * Real.sqrt r) = Real.sqrt r / r ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-r) * hss
  have e1 : (1 / r) * ((2 / r) * (c + Real.sqrt r)) =
      2 * c * (1 / r ^ 2) + 2 * (1 / (r * Real.sqrt r)) := by
    rw [hinv]
    field_simp
  have e2 : (1 / r) * (A / (r - 1)) ≤ 2 * A * (1 / r ^ 2) := by
    rw [div_mul_div_comm, one_mul, mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hA hr0.le) (sub_nonneg.mpr hr)]
  rw [mul_add, e1]
  linarith

open Classical in
/-- **Luca–Pomerance Lemma 2.1 (ii), counting form.** For every `ε > 0`, eventually
`#{n ≤ N : some prime r > y(n) divides n and σ(n)} ≤ ε N`. -/
theorem failII_count_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (((Finset.Icc 1 N).filter FailII).card : ℝ) ≤ ε * N := by
  obtain ⟨K₂, c₁, hK₂, hc₁, N₂, hSpU⟩ := Sp_upper
  set CE := Real.log 4 + 6 + Mertens.E₁ with hCE
  have hCE0 : 0 ≤ CE := by
    have h1 : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
    have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hCE]; linarith
  set T : ℕ := ⌈8 / ε⌉₊ + 1 with hTdef
  have hT1 : 1 ≤ T := by omega
  have hTε : 1 / (T : ℝ) ≤ ε / 8 := by
    have h1 : 8 / ε ≤ (T : ℝ) := by
      rw [hTdef]; push_cast
      have := Nat.le_ceil (8 / ε)
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at h1
    linarith
  have hclim : Tendsto (fun L : ℝ => (T : ℝ) ^ 2 / Y1F L) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (T : ℝ) ^ 2)).div_atTop tendsto_Y1F
  have hEvL : ∀ᶠ L : ℝ in atTop, 1 + Real.log 2 < L ∧
      (2 ≤ Y1F L ∧ Y1F L ≤ MMF L ∧
        (Real.log (MMF L) - Real.log (Y1F L)) / Real.log (Y1F L) + 2 * (CE / Real.log (Y1F L))
          ≤ ε / 8) ∧
      (2 ≤ MMF L ∧ (2 * c₁ + 2 * (L + K₂)) / (MMF L - 1) + 4 / Real.sqrt (MMF L - 1) ≤ ε / 16) ∧
      (T : ℝ) ^ 2 / Y1F L ≤ ε / 8 := by
    filter_upwards [eventually_gt_atTop (1 + Real.log 2),
      eventually_a1 CE hCE0 (ε / 8) (by positivity),
      eventually_a2 c₁ K₂ (ε / 16) (by positivity),
      hclim.eventually_le_const (show (0 : ℝ) < ε / 8 by positivity)] with L h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hEvN : ∀ᶠ N : ℕ in atTop,
      (1 + Real.log 2 < Real.log (Real.log N) ∧
        (2 ≤ Y1F (Real.log (Real.log N)) ∧
          Y1F (Real.log (Real.log N)) ≤ MMF (Real.log (Real.log N)) ∧
          (Real.log (MMF (Real.log (Real.log N))) - Real.log (Y1F (Real.log (Real.log N)))) /
              Real.log (Y1F (Real.log (Real.log N))) +
            2 * (CE / Real.log (Y1F (Real.log (Real.log N)))) ≤ ε / 8) ∧
        (2 ≤ MMF (Real.log (Real.log N)) ∧
          (2 * c₁ + 2 * (Real.log (Real.log N) + K₂)) / (MMF (Real.log (Real.log N)) - 1) +
            4 / Real.sqrt (MMF (Real.log (Real.log N)) - 1) ≤ ε / 16) ∧
        (T : ℝ) ^ 2 / Y1F (Real.log (Real.log N)) ≤ ε / 8) ∧
      N₂ ≤ N ∧ 3 ≤ N ∧ Real.sqrt N ≤ ε / 8 * N ∧
      (1 ≤ ⌊Real.log N ^ 2⌋₊ ∧
        2 * (1 + Real.log ((N : ℝ) + 1)) / (⌊Real.log N ^ 2⌋₊ : ℝ) ≤ ε / 16) := by
    filter_upwards [tendsto_loglog_nat.eventually hEvL, eventually_ge_atTop N₂,
      eventually_ge_atTop 3, eventually_sqrt_le (ε / 8) (by positivity),
      eventually_a3 (ε / 16) (by positivity)] with N h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hEvN
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hL1, ⟨hY2, hYM, ha1⟩, ⟨hMM2, ha2⟩, hc⟩, hN₂, hN3, hsqrtN, ⟨hW1, ha3⟩⟩ := hN₀ N hN
  set L := Real.log (Real.log N) with hLdef
  set Y₁ := Y1F L with hY₁def
  set m : ℕ := ⌊MMF L⌋₊ with hmdef
  set W : ℕ := ⌊Real.log N ^ 2⌋₊ with hWdef
  set Z : ℝ := Y₁ / T with hZdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hY₁0 : 0 < Y₁ := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hZ0 : 0 < Z := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm1 : 1 ≤ m := Nat.le_floor (by push_cast; linarith)
  have hmlow : MMF L - 1 < (m : ℝ) := by
    have := Nat.lt_floor_add_one (MMF L)
    rw [← hmdef] at this
    linarith
  -- the five families
  set E0 := (Finset.Icc 1 N).filter (fun n => n * n ≤ N) with hE0
  set R1 := (Finset.Ioc ⌊Y₁⌋₊ m).filter Nat.Prime with hR1
  set R2 := (Nat.primesLE N).filter (fun r => m < r) with hR2
  set Qr : ℕ → Finset ℕ := fun r => (Nat.primesLE N).filter (fun q => r ∣ q + 1) with hQr
  set Qb := (Nat.primesLE N).filter (fun q => T < q) with hQb
  set kq : ℕ → ℕ := fun q => Nat.log q ⌊Z⌋₊ + 1 with hkq
  set F1 := R1.biUnion (fun r => (Finset.Icc 1 N).filter (fun n => r ∣ n)) with hF1
  set F2 := R2.biUnion (fun r => (Qr r).biUnion
    (fun q => (Finset.Icc 1 N).filter (fun n => r * q ∣ n))) with hF2
  set F3 := Qb.biUnion (fun q => (Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)) with hF3
  set F4 := (Nat.primesLE T).biUnion
    (fun q => (Finset.Icc 1 N).filter (fun n => q ^ kq q ∣ n)) with hF4
  have hunion : (Finset.Icc 1 N).filter FailII ⊆ E0 ∪ F1 ∪ F2 ∪ F3 ∪ F4 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hnI := hn.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hnI).2
    have hn0 : n ≠ 0 := by omega
    simp only [Finset.mem_union]
    by_cases hsq : n * n ≤ N
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hnI, hsq⟩))))
    push Not at hsq
    obtain ⟨r, hr, hry, hrn, hrσ⟩ := hn.2
    have hly := le_lpY_of_sq N n hnN hsq hL1
    have hrY : Y₁ < r := lt_of_le_of_lt hly hry
    have hrN : r ≤ N := le_trans (Nat.le_of_dvd (by omega) hrn) hnN
    rcases failII_cases n hn0 Y₁ T hT1 r hr hrY hrn hrσ with
      ⟨q, hq, hrq, hrqn⟩ | ⟨q, hq, hTq, hq2⟩ | ⟨q, k, hq, hqT, hk1, hqk, hZk⟩
    · by_cases hrm : r ≤ m
      · left; left; left; right
        rw [hF1, Finset.mem_biUnion]
        refine ⟨r, ?_, Finset.mem_filter.mpr ⟨hnI, hrn⟩⟩
        rw [hR1, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨(Nat.floor_lt hY₁0.le).mpr hrY, hrm⟩, hr⟩
      · left; left; right
        push Not at hrm
        have hqn : q ∣ n := Dvd.dvd.trans (Dvd.intro_left r rfl) hrqn
        have hqN : q ≤ N := le_trans (Nat.le_of_dvd (by omega) hqn) hnN
        rw [hF2, Finset.mem_biUnion]
        refine ⟨r, ?_, ?_⟩
        · rw [hR2, Finset.mem_filter, Nat.mem_primesLE]
          exact ⟨⟨hrN, hr⟩, hrm⟩
        · rw [Finset.mem_biUnion]
          refine ⟨q, ?_, Finset.mem_filter.mpr ⟨hnI, hrqn⟩⟩
          rw [hQr]
          simp only [Finset.mem_filter, Nat.mem_primesLE]
          exact ⟨⟨hqN, hq⟩, hrq⟩
    · left; right
      have hqn : q ∣ n := (dvd_pow_self q two_ne_zero).trans hq2
      have hqN : q ≤ N := le_trans (Nat.le_of_dvd (by omega) hqn) hnN
      rw [hF3, Finset.mem_biUnion]
      refine ⟨q, ?_, Finset.mem_filter.mpr ⟨hnI, hq2⟩⟩
      rw [hQb, Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨hqN, hq⟩, hTq⟩
    · right
      rw [hF4, Finset.mem_biUnion]
      refine ⟨q, Nat.mem_primesLE.mpr ⟨hqT, hq⟩, Finset.mem_filter.mpr ⟨hnI, ?_⟩⟩
      have hfl : ⌊Z⌋₊ < q ^ k := by
        rw [Nat.floor_lt hZ0.le]; push_cast; exact hZk
      have hlt : Nat.log q ⌊Z⌋₊ < k := Nat.log_lt_of_lt_pow' (by omega) hfl
      have hkk : kq q ≤ k := by
        change Nat.log q ⌊Z⌋₊ + 1 ≤ k
        omega
      exact (pow_dvd_pow q hkk).trans hqk
  -- cardinalities
  have hcardN : ((Finset.Icc 1 N).filter FailII).card ≤
      E0.card + ∑ r ∈ R1, ((Finset.Icc 1 N).filter (fun n => r ∣ n)).card +
        ∑ r ∈ R2, ∑ q ∈ Qr r, ((Finset.Icc 1 N).filter (fun n => r * q ∣ n)).card +
        ∑ q ∈ Qb, ((Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)).card +
        ∑ q ∈ Nat.primesLE T, ((Finset.Icc 1 N).filter (fun n => q ^ kq q ∣ n)).card := by
    have h0 := Finset.card_le_card hunion
    have h1 := Finset.card_union_le (E0 ∪ F1 ∪ F2 ∪ F3) F4
    have h2 := Finset.card_union_le (E0 ∪ F1 ∪ F2) F3
    have h3 := Finset.card_union_le (E0 ∪ F1) F2
    have h4 := Finset.card_union_le E0 F1
    have hb1 : F1.card ≤ ∑ r ∈ R1, ((Finset.Icc 1 N).filter (fun n => r ∣ n)).card :=
      Finset.card_biUnion_le
    have hb2 : F2.card ≤
        ∑ r ∈ R2, ∑ q ∈ Qr r, ((Finset.Icc 1 N).filter (fun n => r * q ∣ n)).card := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun r _ => ?_)
      exact Finset.card_biUnion_le
    have hb3 : F3.card ≤ ∑ q ∈ Qb, ((Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)).card :=
      Finset.card_biUnion_le
    have hb4 : F4.card ≤
        ∑ q ∈ Nat.primesLE T, ((Finset.Icc 1 N).filter (fun n => q ^ kq q ∣ n)).card :=
      Finset.card_biUnion_le
    omega
  have hcard : (((Finset.Icc 1 N).filter FailII).card : ℝ) ≤
      (E0.card : ℝ) + ∑ r ∈ R1, (((Finset.Icc 1 N).filter (fun n => r ∣ n)).card : ℝ) +
        ∑ r ∈ R2, ∑ q ∈ Qr r, (((Finset.Icc 1 N).filter (fun n => r * q ∣ n)).card : ℝ) +
        ∑ q ∈ Qb, (((Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)).card : ℝ) +
        ∑ q ∈ Nat.primesLE T, (((Finset.Icc 1 N).filter (fun n => q ^ kq q ∣ n)).card : ℝ) := by
    exact_mod_cast hcardN
  -- (E0)
  have hB0 : (E0.card : ℝ) ≤ ε / 8 * N := (card_filter_sq_le N).trans hsqrtN
  -- (a1)
  have hB1 : ∑ r ∈ R1, (((Finset.Icc 1 N).filter (fun n => r ∣ n)).card : ℝ) ≤ ε / 8 * N := by
    have h1 : ∑ r ∈ R1, (((Finset.Icc 1 N).filter (fun n => r ∣ n)).card : ℝ) ≤
        (N : ℝ) * ∑ r ∈ R1, (1 : ℝ) / r := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [mul_one_div]
      exact card_filter_dvd_Icc_le r N
    have h2 := sum_prime_inv_Ioc_le Y₁ (MMF L) hY2 hYM
    rw [← hmdef, ← hR1] at h2
    have h3 : (N : ℝ) * ∑ r ∈ R1, (1 : ℝ) / r ≤ (N : ℝ) * (ε / 8) :=
      mul_le_mul_of_nonneg_left (h2.trans ha1) hN0
    linarith
  -- (a2)
  have hR2prop : ∀ r ∈ R2, r.Prime ∧ m < r := by
    intro r hr
    rw [hR2, Finset.mem_filter, Nat.mem_primesLE] at hr
    exact ⟨hr.1.2, hr.2⟩
  have hinner : ∀ r ∈ R2, ∑ q ∈ Qr r, (((Finset.Icc 1 N).filter (fun n => r * q ∣ n)).card : ℝ) ≤
      (N : ℝ) * ((1 / (r : ℝ)) * Sp r N) := by
    intro r _
    unfold Sp
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have := card_filter_dvd_Icc_le (r * q) N
    push_cast at this
    calc (((Finset.Icc 1 N).filter (fun n => r * q ∣ n)).card : ℝ) ≤ (N : ℝ) / ((r : ℝ) * q) :=
          this
      _ = (N : ℝ) * ((1 / (r : ℝ)) * (1 / (q : ℝ))) := by
          rw [div_mul_div_comm, one_mul, mul_one_div]
  have hB2 : ∑ r ∈ R2, ∑ q ∈ Qr r, (((Finset.Icc 1 N).filter (fun n => r * q ∣ n)).card : ℝ) ≤
      ε / 16 * N + ε / 16 * N := by
    refine (Finset.sum_le_sum hinner).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not R2 (fun r => r ≤ W)]
    -- the pieces `r ≤ W` and `r > W`
    have hsmall : ∑ r ∈ R2.filter (fun r => r ≤ W), (1 / (r : ℝ)) * Sp r N ≤
        (2 * c₁ + 2 * (L + K₂)) * (1 / (m : ℝ)) + 2 * (2 / Real.sqrt m) := by
      have hterm : ∀ r ∈ R2.filter (fun r => r ≤ W), (1 / (r : ℝ)) * Sp r N ≤
          (2 * c₁ + 2 * (L + K₂)) * (1 / (r : ℝ) ^ 2) + 2 * (1 / ((r : ℝ) * Real.sqrt r)) := by
        intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨hrp, _⟩ := hR2prop r hr.1
        have hrW : (r : ℝ) ≤ Real.log N ^ 2 := by
          have : (r : ℝ) ≤ (W : ℝ) := by exact_mod_cast hr.2
          exact this.trans (Nat.floor_le (sq_nonneg _))
        have hSp := hSpU N hN₂ r hrp hrW
        have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hrp.two_le
        have hLK : 0 ≤ L + K₂ := by linarith
        have h1 : (1 / (r : ℝ)) * Sp r N ≤
            (1 / (r : ℝ)) * ((2 / r) * (c₁ + Real.sqrt r) + (L + K₂) / ((r : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hSp (by positivity)
        have h2 := per_r_bound r c₁ (L + K₂) hr2 hc₁.le hLK
        linarith
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hgt : ∀ r ∈ R2.filter (fun r => r ≤ W), m < r := fun r hr =>
        (hR2prop r (Finset.mem_filter.mp hr).1).2
      have hs1 := sum_inv_sq_le_of_gt (R2.filter (fun r => r ≤ W)) m hm1 hgt
      have hs2 := sum_inv_mul_sqrt_le_of_gt (R2.filter (fun r => r ≤ W)) m hm1 hgt
      have hcoef : 0 ≤ 2 * c₁ + 2 * (L + K₂) := by linarith
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hs1 hcoef
      · exact mul_le_mul_of_nonneg_left hs2 (by norm_num)
    have hlarge : ∑ r ∈ R2.filter (fun r => ¬ r ≤ W), (1 / (r : ℝ)) * Sp r N ≤
        2 * (1 + Real.log ((N : ℝ) + 1)) * (1 / (W : ℝ)) := by
      have hterm : ∀ r ∈ R2.filter (fun r => ¬ r ≤ W), (1 / (r : ℝ)) * Sp r N ≤
          2 * (1 + Real.log ((N : ℝ) + 1)) * (1 / (r : ℝ) ^ 2) := by
        intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨hrp, _⟩ := hR2prop r hr.1
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hrp.pos
        have hSp := Sp_le_trivial r N hrp.one_le
        calc (1 / (r : ℝ)) * Sp r N ≤ (1 / (r : ℝ)) * ((2 / r) * (1 + Real.log ((N : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hSp (by positivity)
          _ = 2 * (1 + Real.log ((N : ℝ) + 1)) * (1 / (r : ℝ) ^ 2) := by
              field_simp
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      have hlogN1 : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith)
        linarith
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_inv_sq_le_of_gt _ W hW1
      intro r hr
      exact not_le.mp (Finset.mem_filter.mp hr).2
    -- compare with `M − 1`
    have hMM1 : 0 < MMF L - 1 := by linarith
    have hinvm : 1 / (m : ℝ) ≤ 1 / (MMF L - 1) := one_div_le_one_div_of_le hMM1 hmlow.le
    have hsqrtm : 2 / Real.sqrt m ≤ 2 / Real.sqrt (MMF L - 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hMM1)
      exact Real.sqrt_le_sqrt hmlow.le
    have hcoef : 0 ≤ 2 * c₁ + 2 * (L + K₂) := by linarith
    have hsmall' : ∑ r ∈ R2.filter (fun r => r ≤ W), (1 / (r : ℝ)) * Sp r N ≤ ε / 16 := by
      refine hsmall.trans (le_trans ?_ ha2)
      have e1 : (2 * c₁ + 2 * (L + K₂)) * (1 / (MMF L - 1)) =
          (2 * c₁ + 2 * (L + K₂)) / (MMF L - 1) := by ring
      have e2 : 2 * (2 / Real.sqrt (MMF L - 1)) = 4 / Real.sqrt (MMF L - 1) := by ring
      rw [← e1, ← e2]
      exact add_le_add (mul_le_mul_of_nonneg_left hinvm hcoef)
        (mul_le_mul_of_nonneg_left hsqrtm (by norm_num))
    have hlarge' : ∑ r ∈ R2.filter (fun r => ¬ r ≤ W), (1 / (r : ℝ)) * Sp r N ≤ ε / 16 := by
      refine hlarge.trans (le_of_eq_of_le ?_ ha3)
      ring
    rw [mul_add]
    have := mul_le_mul_of_nonneg_left hsmall' hN0
    have := mul_le_mul_of_nonneg_left hlarge' hN0
    linarith
  -- (b)
  have hB3 : ∑ q ∈ Qb, (((Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)).card : ℝ) ≤ ε / 8 * N := by
    have h1 : ∑ q ∈ Qb, (((Finset.Icc 1 N).filter (fun n => q ^ 2 ∣ n)).card : ℝ) ≤
        (N : ℝ) * ∑ q ∈ Qb, (1 : ℝ) / (q : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      have := card_filter_dvd_Icc_le (q ^ 2) N
      push_cast at this
      rw [mul_one_div]
      exact this
    have h2 := sum_inv_sq_le_of_gt Qb T hT1 (fun q hq => (Finset.mem_filter.mp hq).2)
    have h3 : (N : ℝ) * ∑ q ∈ Qb, (1 : ℝ) / (q : ℝ) ^ 2 ≤ (N : ℝ) * (ε / 8) :=
      mul_le_mul_of_nonneg_left (h2.trans hTε) hN0
    linarith
  -- (c)
  have hB4 : ∑ q ∈ Nat.primesLE T, (((Finset.Icc 1 N).filter (fun n => q ^ kq q ∣ n)).card : ℝ) ≤
      ε / 8 * N := by
    have hterm : ∀ q ∈ Nat.primesLE T,
        (((Finset.Icc 1 N).filter (fun n => q ^ kq q ∣ n)).card : ℝ) ≤ (N : ℝ) / Z := by
      intro q hq
      have hqp := Nat.prime_of_mem_primesLE hq
      have h1 := card_filter_dvd_Icc_le (q ^ kq q) N
      have hpow : Z < ((q ^ kq q : ℕ) : ℝ) := by
        have h2 := Nat.lt_pow_succ_log_self hqp.one_lt ⌊Z⌋₊
        have h3 : ⌊Z⌋₊ < q ^ kq q := h2
        exact (Nat.floor_lt hZ0.le).mp h3
      refine h1.trans ?_
      exact div_le_div_of_nonneg_left hN0 hZ0 hpow.le
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcardT : ((Nat.primesLE T).card : ℝ) ≤ T := by
      have hsub : Nat.primesLE T ⊆ Finset.Icc 1 T := by
        intro q hq
        rw [Nat.mem_primesLE] at hq
        exact Finset.mem_Icc.mpr ⟨hq.2.one_le, hq.1⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact_mod_cast this
    have e : (T : ℝ) * ((N : ℝ) / Z) = (T : ℝ) ^ 2 / Y₁ * N := by
      rw [hZdef]; field_simp
    calc ((Nat.primesLE T).card : ℝ) * ((N : ℝ) / Z) ≤ (T : ℝ) * ((N : ℝ) / Z) :=
          mul_le_mul_of_nonneg_right hcardT (by positivity)
      _ = (T : ℝ) ^ 2 / Y₁ * N := e
      _ ≤ ε / 8 * N := mul_le_mul_of_nonneg_right hc hN0
  have hεN : 0 ≤ ε * N := by positivity
  linarith

end Principia.Common.LucaPomerance.LP21
