/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Chebyshev.Upper
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false

/-!
# Sums over prime powers with explicit constants

Campaign-agnostic tools for bounding `∑_{v ≤ N} Λ(v) g(v)` with explicit constants, built for the
Totals algebra of Helfgott's `S_{I,2}` (`MPc.I2Arith`) but mentioning nothing of it.

* **Abel summation against a linear majorant** (`abel_linear`): if the partial sums of `w` over
  `(a, n]` are at most `A n + B` for every `n > a`, and `g` is antitone and `≥ 0` on `(a, b]`,
  then `∑_{a < n ≤ b} w(n) g(n) ≤ (A(a+1) + B) g(a+1) + A ∑_{a+1 < n ≤ b} g(n)`. One
  induction on `b`, with the invariant `∑ w g + (A b + B − W(b)) g(b) ≤ RHS(b)`.
* **Telescoping** (`sum_inv_le_log`, `sum_inv_sqrt_le`): `∑_{a<n≤b} 1/n ≤ log b − log a`
  (`a ≥ 1`), `∑_{a<n≤b} 1/√n ≤ 2(√b − √a)`.
* **Chebyshev partial sums** (`sum_vM_le`): `∑_{0<m≤n} w(m) ≤ 1.1096 n + 1150000` for every
  `0 ≤ w ≤ Λ` (`Chebyshev.psi_nat_le`).
* **Prime powers not coprime to `q`** (`sum_nc_le`): `∑_{v ≤ N, (v,q) > 1} Λ(v) F(v) ≤
  ∑_{p ∣ q} ∑_{1 ≤ k ≤ N} log p · F(p^k)` for `F ≥ 0` — the map `(p, k) ↦ p^k` covers them.
  Two consequences, each restricted to odd `v`:
  - **count** (`sum_nc_count`): `∑_{v ≤ N odd, (v,q)>1} Λ(v) ≤ (log q / log 3) log N`;
  - **gcd** (`sum_nc_gcd`): `∑_{v ≤ N odd, (v,q)>1} Λ(v) (v,q)/v ≤ (3/2) log q`, from
    `∑_{k ≥ 1} p^{min(k,j)}/p^k = j + 1/(p − 1) ≤ (3/2) j` for odd `p`, `j = v_p(q) ≥ 1`.
-/

namespace Principia.Common.PPSum

open ArithmeticFunction hiding log
open Finset Real Chebyshev

/-! ## 1. Abel summation against a linear majorant -/

/-- **The Abel invariant.** -/
theorem abel_inv (w g : ℕ → ℝ) (A B : ℝ) (a : ℕ)
    (hW : ∀ n, a < n → ∑ m ∈ Ioc a n, w m ≤ A * n + B)
    (hg : ∀ n, a < n → g (n + 1) ≤ g n) :
    ∀ b, a + 1 ≤ b → ∑ n ∈ Ioc a b, w n * g n + (A * b + B - ∑ m ∈ Ioc a b, w m) * g b ≤
      (A * (a + 1) + B) * g (a + 1) + A * ∑ n ∈ Ioc (a + 1) b, g n := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
    rw [Nat.Ioc_succ_singleton, Finset.Ioc_self, sum_singleton, sum_singleton, sum_empty]
    push_cast
    ring_nf
    exact le_refl _
  | succ b hb ih =>
    rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
    have hD : 0 ≤ A * b + B - ∑ m ∈ Ioc a b, w m := by linarith [hW b (by omega)]
    have hgb := hg b (by omega)
    have h1 := mul_le_mul_of_nonneg_left hgb hD
    push_cast
    have e : ∑ n ∈ Ioc a b, w n * g n + w (b + 1) * g (b + 1) +
        (A * (b + 1) + B - (∑ m ∈ Ioc a b, w m + w (b + 1))) * g (b + 1) =
        ∑ n ∈ Ioc a b, w n * g n + (A * b + B - ∑ m ∈ Ioc a b, w m) * g (b + 1) +
          A * g (b + 1) := by ring
    rw [e]
    linarith

/-- **Abel summation against a linear majorant of the partial sums.** -/
theorem abel_linear (w g : ℕ → ℝ) (A B : ℝ) (a b : ℕ) (hab : a + 1 ≤ b)
    (hW : ∀ n, a < n → ∑ m ∈ Ioc a n, w m ≤ A * n + B)
    (hg : ∀ n, a < n → g (n + 1) ≤ g n) (hgb : 0 ≤ g b) :
    ∑ n ∈ Ioc a b, w n * g n ≤
      (A * (a + 1) + B) * g (a + 1) + A * ∑ n ∈ Ioc (a + 1) b, g n := by
  have h := abel_inv w g A B a hW hg b hab
  have hD : 0 ≤ A * b + B - ∑ m ∈ Ioc a b, w m := by linarith [hW b (by omega)]
  nlinarith [mul_nonneg hD hgb]

/-! ## 2. Telescoping sums -/

/-- `1/(n+1) ≤ log(n+1) − log n` for `n ≥ 1`. -/
theorem inv_succ_le_log (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
  rw [Real.log_div hn0.ne' hn1.ne'] at h
  have e : (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = -(1 / ((n + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  linarith

/-- **`∑_{a < n ≤ b} 1/n ≤ log b − log a`** for `1 ≤ a ≤ b`. -/
theorem sum_inv_le_log (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / n ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ioc_succ_top hb]
    have := inv_succ_le_log b (by omega)
    push_cast at this ⊢
    linarith

/-- `1/√(n+1) ≤ 2(√(n+1) − √n)`. -/
theorem inv_sqrt_succ_le (n : ℕ) :
    1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity)
  have hs0 := Real.sq_sqrt hn0
  have hsn := Real.sqrt_nonneg (n : ℝ)
  rw [div_le_iff₀ h1]
  push_cast at hs1 ⊢
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)]

/-- **`∑_{a < n ≤ b} 1/√n ≤ 2(√b − √a)`.** -/
theorem sum_inv_sqrt_le (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, 1 / Real.sqrt n ≤ 2 * (Real.sqrt b - Real.sqrt a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ioc_succ_top hb]
    have := inv_sqrt_succ_le b
    push_cast at this ⊢
    linarith

/-! ## 3. Chebyshev partial sums -/

/-- **`∑_{0 < m ≤ n} w(m) ≤ 1.1096 n + 1150000`** for `0 ≤ w ≤ Λ` (`psi_nat_le`). -/
theorem sum_vM_le (w : ℕ → ℝ) (hw : ∀ m, w m ≤ Λ m) (n : ℕ) :
    ∑ m ∈ Ioc 0 n, w m ≤ 1.1096 * n + 1150000 := by
  have h := Principia.Common.Chebyshev.psi_nat_le n
  have e : _root_.Chebyshev.psi (n : ℝ) = ∑ m ∈ Ioc 0 n, Λ m := by
    rw [_root_.Chebyshev.psi, Nat.floor_natCast]
  rw [e] at h
  exact (sum_le_sum fun m _ => hw m).trans h

/-! ## 4. Prime powers not coprime to `q` -/

/-- **The prime powers `v ≤ N` with `(v, q) > 1` are covered by `(p, k) ↦ p^k`**,
`p ∣ q`, `1 ≤ k ≤ N`. -/
theorem sum_nc_le (N q : ℕ) (hq : q ≠ 0) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q), Λ v * F v ≤
      ∑ p ∈ q.primeFactors, ∑ k ∈ Icc 1 N, Real.log p * F (p ^ k) := by
  classical
  set S := (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q) with hS
  set T := q.primeFactors ×ˢ Icc 1 N with hT
  have hsub : S.filter (fun v => Λ v ≠ 0) ⊆ T.image (fun pk => pk.1 ^ pk.2) := by
    intro v hv
    simp only [hS, mem_filter, mem_Ioc] at hv
    obtain ⟨⟨⟨hv0, hvN⟩, hcop⟩, hΛ⟩ := hv
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hpq : p ∣ q := by
      by_contra hpq
      exact hcop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq))
    have hkN : k ≤ N := by
      have h1 : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      omega
    rw [mem_image]
    refine ⟨(p, k), ?_, rfl⟩
    rw [hT, mem_product, Nat.mem_primeFactors, mem_Icc]
    exact ⟨⟨hp, hpq, hq⟩, by omega, hkN⟩
  have hinj : Set.InjOn (fun pk : ℕ × ℕ => pk.1 ^ pk.2) (T : Set (ℕ × ℕ)) := by
    rintro ⟨p, k⟩ hpk ⟨p', k'⟩ hpk' he
    simp only [hT, coe_product, Set.mem_prod, mem_coe, Nat.mem_primeFactors, mem_Icc] at hpk hpk'
    have he' : p ^ k = p' ^ k' := he
    obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hpk.1.1 hpk'.1.1 (by omega) (by omega) he'
    rfl
  calc ∑ v ∈ S, Λ v * F v = ∑ v ∈ S.filter (fun v => Λ v ≠ 0), Λ v * F v :=
        (sum_filter_of_ne fun v _ h => left_ne_zero_of_mul h).symm
    _ ≤ ∑ v ∈ T.image (fun pk => pk.1 ^ pk.2), Λ v * F v :=
        sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
          mul_nonneg vonMangoldt_nonneg (hF v)
    _ = ∑ pk ∈ T, Λ (pk.1 ^ pk.2) * F (pk.1 ^ pk.2) := sum_image hinj
    _ = ∑ pk ∈ T, Real.log pk.1 * F (pk.1 ^ pk.2) := by
        refine sum_congr rfl fun pk hpk => ?_
        simp only [hT, mem_product, Nat.mem_primeFactors, mem_Icc] at hpk
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hpk.1.1]
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ Icc 1 N, Real.log p * F (p ^ k) := by
        rw [hT, sum_product]

/-- `∑_{p ∣ q} log p ≤ log q`. -/
theorem sum_primeFactors_log_le (q : ℕ) (hq : q ≠ 0) :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hpos : ∀ p ∈ q.primeFactors, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
  apply Real.log_le_log (prod_pos hpos)
  have h := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h' : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast h
  rwa [Nat.cast_prod] at h'

/-- **The count**: `∑_{v ≤ N odd, (v,q)>1} Λ(v) ≤ (log q / log 3)·log N`. -/
theorem sum_nc_count (N q : ℕ) (hN : 1 ≤ N) (hq : q ≠ 0) :
    ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q),
      Λ v * (if v % 2 = 1 then 1 else 0) ≤ Real.log q / Real.log 3 * Real.log N := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  refine (sum_nc_le N q hq (fun v => if v ≤ N ∧ v % 2 = 1 then 1 else 0)
    (fun v => by split_ifs <;> norm_num) |>.trans' ?_).trans ?_
  · refine sum_le_sum fun v hv => ?_
    have hvN : v ≤ N := (mem_Ioc.mp (mem_filter.mp hv).1).2
    by_cases h : v % 2 = 1
    · simp [h, hvN]
    · simp [h]
  · -- each prime contributes `≤ [p odd]·log N`
    have hper : ∀ p ∈ q.primeFactors, ∑ k ∈ Icc 1 N,
        Real.log p * (if p ^ k ≤ N ∧ p ^ k % 2 = 1 then (1 : ℝ) else 0) ≤
          Real.log p / Real.log 3 * Real.log N := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
      by_cases h2 : p = 2
      · have hz : ∀ k ∈ Icc 1 N,
            Real.log p * (if p ^ k ≤ N ∧ p ^ k % 2 = 1 then (1 : ℝ) else 0) = 0 := by
          intro k hk
          have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
          have : p ^ k % 2 = 0 := by
            rw [h2]
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            rw [pow_succ]; simp
          simp [this]
        rw [sum_congr rfl hz, sum_const_zero]
        positivity
      · have hp3 : (3 : ℝ) ≤ p := by
          have := hpp.two_le
          have : p ≠ 2 := h2
          have : 3 ≤ p := by omega
          exact_mod_cast this
        have hlp3 : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp3
        -- the number of `k ≥ 1` with `p^k ≤ N` is at most `log_p N`
        have hcard : ∑ k ∈ Icc 1 N, (if p ^ k ≤ N ∧ p ^ k % 2 = 1 then (1 : ℝ) else 0) ≤
            (Nat.log p N : ℝ) := by
          calc ∑ k ∈ Icc 1 N, (if p ^ k ≤ N ∧ p ^ k % 2 = 1 then (1 : ℝ) else 0)
              ≤ ∑ k ∈ Icc 1 N, (if k ≤ Nat.log p N then (1 : ℝ) else 0) := by
                refine sum_le_sum fun k _ => ?_
                split_ifs with h1 h2 <;> try norm_num
                exact h2 (Nat.le_log_of_pow_le hpp.one_lt h1.1)
            _ ≤ ∑ k ∈ Icc 1 (Nat.log p N), (1 : ℝ) := by
                rw [← sum_filter]
                refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by norm_num)
                simp only [mem_filter, mem_Icc] at hk ⊢
                omega
            _ = (Nat.log p N : ℝ) := by simp
        have hlog : (Nat.log p N : ℝ) * Real.log p ≤ Real.log N := by
          have h := Nat.pow_log_le_self p (show N ≠ 0 by omega)
          have h' : ((p : ℝ)) ^ (Nat.log p N) ≤ N := by exact_mod_cast h
          have := Real.log_le_log (by positivity) h'
          rwa [Real.log_pow] at this
        rw [← mul_sum]
        calc Real.log p * ∑ k ∈ Icc 1 N,
              (if p ^ k ≤ N ∧ p ^ k % 2 = 1 then (1 : ℝ) else 0)
            ≤ Real.log p * (Nat.log p N : ℝ) := mul_le_mul_of_nonneg_left hcard hlp.le
          _ ≤ Real.log N := by linarith
          _ ≤ Real.log p / Real.log 3 * Real.log N := by
              have : 1 ≤ Real.log p / Real.log 3 := by rw [le_div_iff₀ hl3]; linarith
              nlinarith
    refine (sum_le_sum hper).trans ?_
    rw [← sum_mul, ← sum_div]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (sum_primeFactors_log_le q hq) hl3.le) hlN

/-- `(p^k, q) ≤ p^{min(k, v_p(q))}`. -/
theorem gcd_pow_le (p k q : ℕ) (hp : p.Prime) (hq : q ≠ 0) :
    Nat.gcd (p ^ k) q ≤ p ^ (min k (q.factorization p)) := by
  obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ k) q)
  have hiq : p ^ i ∣ q := hi ▸ Nat.gcd_dvd_right (p ^ k) q
  have hij : i ≤ q.factorization p := (hp.pow_dvd_iff_le_factorization hq).mp hiq
  rw [hi]
  exact Nat.pow_le_pow_right hp.pos (le_min hik hij)

/-- **One prime**: `∑_{1 ≤ k ≤ N} (p^k, q)/p^k ≤ j + 1/2` for `p ≥ 3`, `j = v_p(q)`. -/
theorem sum_gcd_pow_le (p N q : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hq : q ≠ 0) :
    ∑ k ∈ Icc 1 N, ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / (p : ℝ) ^ k ≤
      (q.factorization p : ℝ) + 1 / 2 := by
  set j := q.factorization p with hj
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hterm : ∀ k, ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / (p : ℝ) ^ k ≤
      if k ≤ j then 1 else (1 / (p : ℝ)) ^ (k - j) := by
    intro k
    have hg := gcd_pow_le p k q hp hq
    have hgR : ((Nat.gcd (p ^ k) q : ℕ) : ℝ) ≤ (p : ℝ) ^ (min k j) := by exact_mod_cast hg
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    split_ifs with h
    · rw [min_eq_left h] at hgR
      rw [div_le_one hpk]; exact hgR
    · rw [min_eq_right (by omega)] at hgR
      have e : (p : ℝ) ^ k = (p : ℝ) ^ (k - j) * (p : ℝ) ^ j := by
        rw [← pow_add]; congr 1; omega
      calc ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / (p : ℝ) ^ k ≤ (p : ℝ) ^ j / (p : ℝ) ^ k :=
            div_le_div_of_nonneg_right hgR hpk.le
        _ = (1 / (p : ℝ)) ^ (k - j) := by
            rw [e, div_mul_cancel_right₀ (by positivity), one_div_pow, one_div]
  calc ∑ k ∈ Icc 1 N, ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / (p : ℝ) ^ k
      ≤ ∑ k ∈ Icc 1 N, (if k ≤ j then (1 : ℝ) else (1 / (p : ℝ)) ^ (k - j)) :=
        sum_le_sum fun k _ => hterm k
    _ ≤ ∑ k ∈ Icc 1 j, (1 : ℝ) + ∑ m ∈ Ico 1 (N + 1), (1 / (p : ℝ)) ^ m := by
        rw [sum_ite]
        refine add_le_add ?_ ?_
        · refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by norm_num)
          simp only [mem_filter, mem_Icc] at hk ⊢
          omega
        · -- reindex `k ↦ k − j` into `[1, N]`
          have hsub : ((Icc 1 N).filter (fun k => ¬ k ≤ j)).image (fun k => k - j) ⊆
              Ico 1 (N + 1) := by
            intro m hm
            simp only [mem_image, mem_filter, mem_Icc] at hm
            obtain ⟨k, ⟨⟨hk1, hkN⟩, hkj⟩, rfl⟩ := hm
            simp only [mem_Ico]
            omega
          have hinj : Set.InjOn (fun k => k - j)
              (((Icc 1 N).filter (fun k => ¬ k ≤ j)) : Set ℕ) := by
            intro a ha b hb hab
            simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
            simp only at hab
            omega
          calc ∑ k ∈ (Icc 1 N).filter (fun k => ¬ k ≤ j), (1 / (p : ℝ)) ^ (k - j)
              = ∑ m ∈ ((Icc 1 N).filter (fun k => ¬ k ≤ j)).image (fun k => k - j),
                  (1 / (p : ℝ)) ^ m := (sum_image hinj).symm
            _ ≤ ∑ m ∈ Ico 1 (N + 1), (1 / (p : ℝ)) ^ m :=
                sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ (j : ℝ) + 1 / 2 := by
        have h1 : ∑ k ∈ Icc 1 j, (1 : ℝ) = j := by simp
        have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        have hr1 : 1 / (p : ℝ) ≤ 1 / 3 := by
          rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
        have h2 := geom_sum_Ico_le_of_lt_one (m := 1) (n := N + 1) hr0 (by linarith)
        have h3 : (1 / (p : ℝ)) ^ 1 / (1 - 1 / (p : ℝ)) ≤ 1 / 2 := by
          rw [pow_one, div_le_iff₀ (by linarith)]; linarith
        linarith

/-- **The gcd sum**: `∑_{v ≤ N odd, (v,q)>1} Λ(v)·(v,q)/v ≤ (3/2) log q`. -/
theorem sum_nc_gcd (N q : ℕ) (hq : q ≠ 0) :
    ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q),
      Λ v * (if v % 2 = 1 then ((Nat.gcd v q : ℕ) : ℝ) / v else 0) ≤ 3 / 2 * Real.log q := by
  refine (sum_nc_le N q hq (fun v => if v % 2 = 1 then ((Nat.gcd v q : ℕ) : ℝ) / v else 0)
    (fun v => by split_ifs <;> positivity)).trans ?_
  have hper : ∀ p ∈ q.primeFactors, ∑ k ∈ Icc 1 N, Real.log p *
      (if p ^ k % 2 = 1 then ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) else 0) ≤
        3 / 2 * ((q.factorization p : ℝ) * Real.log p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hj : 1 ≤ q.factorization p :=
      hpp.factorization_pos_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)
    have hjR : (1 : ℝ) ≤ q.factorization p := by exact_mod_cast hj
    by_cases h2 : p = 2
    · have hz : ∀ k ∈ Icc 1 N, Real.log p * (if p ^ k % 2 = 1 then
          ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) else 0) = 0 := by
        intro k hk
        have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
        have : p ^ k % 2 = 0 := by
          rw [h2]
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [pow_succ]; simp
        simp [this]
      rw [sum_congr rfl hz, sum_const_zero]
      positivity
    · have hp3 : 3 ≤ p := by have := hpp.two_le; omega
      rw [← mul_sum]
      have hs : ∑ k ∈ Icc 1 N, (if p ^ k % 2 = 1 then
          ((Nat.gcd (p ^ k) q : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) else 0) ≤
            (q.factorization p : ℝ) + 1 / 2 := by
        refine (sum_le_sum fun k _ => ?_).trans (sum_gcd_pow_le p N q hpp hp3 hq)
        split_ifs
        · push_cast; exact le_refl _
        · positivity
      nlinarith
  refine (sum_le_sum hper).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
  rw [Real.log_nat_eq_sum_factorization q, Finsupp.sum, Nat.support_factorization]

end Principia.Common.PPSum
