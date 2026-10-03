/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.DrujalSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

/-!
# `S(r) ≥ 6.76`: the sharp floor for `S(r) = ∑_{q ≤ r odd} μ²(q)/φ(q)`, `r = 150000`

`DS.sR_ge` gives `S ≥ 6.5942` through `S ≥ ∑_{n ≤ r odd} 1/n` (the fibres of the squarefree
kernel), which loses `0.2044 = ∑_{n odd > r, rad n ≤ r} 1/n` (truth `S = 6.7987792`). This file
proves **`sR_ge_sharp : 6.76 ≤ DS.sR`** by keeping the part of that loss carried by the four
smallest odd primes.

## The route (NOT the `n = ab²` route it was briefed with, which prices at `6.73507` for `b ≤ 25`)

Split each odd `q` by `R = gcd(q, P)`, `P = 3·5·7·11`. A squarefree `q` with `gcd(q, P) = R` is
`q = R q'` with `q'` coprime to `P`, and `μ²/φ` is multiplicative, so

    S = ∑_{R | P} (1/φ(R)) · T_P(r/R),     T_P(y) = ∑_{q' ≤ y odd, (q', P) = 1} μ²(q')/φ(q')

(`tS_step`: one prime at a time, as an inequality, which is all that is needed). The fibres of
`rad` over the `q'` coprime to `P` give `T_P(y) ≥ H_P(y) = ∑_{m ≤ y odd, (m, P) = 1} 1/m`
(`hS_le_tS`, the argument of `DS.hOdd_le_sR` restricted to a coprimality class), and the sieve
identity `H_{kp}(y) = H_k(y) − H_k(y/p)/p` (`hS_step`) reduces every `H_P` to the odd harmonic sums
`H_1(N) = ∑_{n ≤ N odd} 1/n`. Collecting,

    S ≥ ∑_N c_N · H_1(N),  N = ⌊r/D⌋,  c_D = ∏_p c_{D_p},  c_1 = 1, c_p = 1/(p(p−1)), c_{p²} = −c_p

(`sR_ge_comb`; the `p`-local factor `1 + (H(y/p) − H(y/p²))/(p(p−1))` is where the gain
`½ log p/(p(p−1))` per prime comes from). Each `H_1(N)` is bounded in the direction its `c_N`
needs: below by the trapezoid rule from `2·24+1 = 49` (`hodd_lo`, `DS.trap`), above by the midpoint
rule `1/(2k+1) ≤ ½ log((k+1)/k)` from `48` (`hodd_hi`, from Mathlib's series for `log(1 + 1/a)`),
with `log N` reduced to `log 2, 3, 5, 7, 11` (`hS1_lo`, `hS1_hi`) and those bounded by the
`log(1 − x)` series (`log3_bd` … `log11_bd`) and Mathlib's `log 2` to nine places. The `N ≤ 48`
are summed exactly.

| quantity | value |
|---|---|
| exact `∑_R H_P(r/R)/φ(R)` (the route's ceiling at `P = 1155`) | `6.7602204` |
| certified by this file (`∑ c_N q_N`) | `6.7601212` |
| claimed | `6.76` (margin `1.2·10⁻⁴`) |
| `P = 105` / `3·5` would give | `6.7493` / `6.7262` |

Generated part: `scratchpad/sfloor/gen_sfloor.py` (exact rationals throughout; the per-`N` bounds
`bN_*` are rounded outward to `10⁻¹⁰`, the log bounds to `10⁻⁸`).
-/

namespace Principia.Common.TernaryGoldbach.SF

open Finset

/-! ## The sums over a coprimality class -/

/-- **The odd `q ≤ y` coprime to `k`**. -/
def oddCop (k y : ℕ) : Finset ℕ := (Icc 1 y).filter (fun q => Odd q ∧ Nat.Coprime q k)

/-- Membership in `oddCop`. -/
theorem mem_oddCop {k y q : ℕ} : q ∈ oddCop k y ↔ (1 ≤ q ∧ q ≤ y) ∧ Odd q ∧ Nat.Coprime q k := by
  unfold oddCop
  rw [mem_filter, mem_Icc]

/-- **`T_k(y) = ∑ μ²(q)/φ(q)`** over the odd `q ≤ y` coprime to `k`. -/
noncomputable def tS (k y : ℕ) : ℝ := ∑ q ∈ oddCop k y, DS.cQ q

/-- **`H_k(y) = ∑ 1/n`** over the odd `n ≤ y` coprime to `k`. -/
noncomputable def hS (k y : ℕ) : ℝ := ∑ n ∈ oddCop k y, (1 : ℝ) / n

/-- `S(r) = T_1(r)`. -/
theorem sR_eq : DS.sR = tS 1 150000 := by
  unfold DS.sR tS
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp [mem_oddCop, DS.oddQ, mem_filter, mem_Icc]

/-- **`μ²/φ` is multiplicative**. -/
theorem cQ_mul {m n : ℕ} (h : Nat.Coprime m n) : DS.cQ (m * n) = DS.cQ m * DS.cQ n := by
  unfold DS.cQ
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h,
    Int.cast_mul, Nat.cast_mul, mul_pow, div_mul_div_comm]

/-- `μ²(p)/φ(p) = 1/(p − 1)`. -/
theorem cQ_prime {p : ℕ} (hp : p.Prime) : DS.cQ p = 1 / ((p : ℝ) - 1) := by
  rw [DS.cQ_sqfree hp.prime.squarefree, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]

/-- The members not divisible by the prime `p` are the class of `kp`. -/
theorem filter_not_dvd (k p y : ℕ) (hp : p.Prime) :
    (oddCop k y).filter (fun q => ¬ p ∣ q) = oddCop (k * p) y := by
  ext q
  rw [mem_filter, mem_oddCop, mem_oddCop, Nat.coprime_mul_iff_right,
    Nat.coprime_comm (n := q) (m := p), hp.coprime_iff_not_dvd]
  tauto

/-- The members divisible by the odd prime `p ∤ k` are `p` times the class of `k` below `y/p`. -/
theorem filter_dvd_eq (k p y : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : Nat.Coprime p k) :
    (oddCop k y).filter (fun q => p ∣ q) = (oddCop k (y / p)).image (fun q => p * q) := by
  have hp0 := hp.pos
  ext q
  rw [mem_filter, mem_image, mem_oddCop]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ho, hc⟩, t, rfl⟩
    refine ⟨t, ?_, rfl⟩
    rw [mem_oddCop]
    refine ⟨⟨?_, ?_⟩, Odd.of_dvd_nat ho (dvd_mul_left t p),
      Nat.Coprime.coprime_dvd_left (dvd_mul_left t p) hc⟩
    · refine Nat.pos_of_ne_zero fun ht => ?_
      rw [ht, mul_zero] at h1
      omega
    · rw [Nat.le_div_iff_mul_le hp0, mul_comm]
      exact h2
  · rintro ⟨t, ht, rfl⟩
    rw [mem_oddCop] at ht
    obtain ⟨⟨h1, h2⟩, ho, hc⟩ := ht
    refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero
      (Nat.one_le_iff_ne_zero.mp h1)), ?_⟩, (hp.odd_of_ne_two hp2).mul ho,
      Nat.coprime_mul_iff_left.mpr ⟨hpk, hc⟩⟩, dvd_mul_right p t⟩
    rw [Nat.le_div_iff_mul_le hp0] at h2
    rw [mul_comm]
    exact h2

/-- **One prime of the `gcd` split**: `T_k(y) ≥ T_{kp}(y) + T_{kp}(y/p)/(p − 1)` (the `q`
divisible by `p` include `p q'`, `q'` coprime to `kp`, and `μ²/φ(pq') = μ²/φ(p)·μ²/φ(q')`). -/
theorem tS_step (k p m y : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : Nat.Coprime p k)
    (hm : k * p = m) : tS m y + DS.cQ p * tS m (y / p) ≤ tS k y := by
  subst hm
  unfold tS
  rw [← sum_filter_add_sum_filter_not (oddCop k y) (fun q => p ∣ q), filter_not_dvd k p y hp,
    filter_dvd_eq k p y hp hp2 hpk,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h]
  have hsub : oddCop (k * p) (y / p) ⊆ oddCop k (y / p) := fun q hq => by
    rw [mem_oddCop] at hq ⊢
    exact ⟨hq.1, hq.2.1, (Nat.coprime_mul_iff_right.mp hq.2.2).1⟩
  have h1 : DS.cQ p * ∑ q ∈ oddCop (k * p) (y / p), DS.cQ q =
      ∑ q ∈ oddCop (k * p) (y / p), DS.cQ (p * q) := by
    rw [mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [mem_oddCop] at hq
    rw [cQ_mul (Nat.coprime_comm.mp (Nat.coprime_mul_iff_right.mp hq.2.2).2)]
  have h2 : ∑ q ∈ oddCop (k * p) (y / p), DS.cQ (p * q) ≤
      ∑ q ∈ oddCop k (y / p), DS.cQ (p * q) :=
    sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => DS.cQ_nonneg _
  linarith

/-- **The sieve identity**: `H_{kp}(y) = H_k(y) − H_k(y/p)/p` for an odd prime `p ∤ k`. -/
theorem hS_step (k p m y : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : Nat.Coprime p k)
    (hm : k * p = m) : hS m y = hS k y - hS k (y / p) / p := by
  subst hm
  unfold hS
  rw [← sum_filter_add_sum_filter_not (oddCop k y) (fun q => p ∣ q), filter_not_dvd k p y hp,
    filter_dvd_eq k p y hp hp2 hpk,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h]
  have h : ∑ q ∈ oddCop k (y / p), (1 : ℝ) / ((p * q : ℕ) : ℝ) =
      (∑ q ∈ oddCop k (y / p), (1 : ℝ) / q) / p := by
    rw [sum_div]
    refine sum_congr rfl fun q _ => ?_
    push_cast
    ring
  rw [h]
  ring

/-- `rad` maps a coprimality class into itself. -/
theorem rad_mem_oddCop {k y n : ℕ} (hn : n ∈ oddCop k y) : DS.rad n ∈ oddCop k y := by
  rw [mem_oddCop] at hn ⊢
  obtain ⟨⟨h1, h2⟩, ho, hc⟩ := hn
  exact ⟨⟨DS.rad_pos n, le_trans (Nat.le_of_dvd (by omega) (DS.rad_dvd n)) h2⟩,
    Odd.of_dvd_nat ho (DS.rad_dvd n), Nat.Coprime.coprime_dvd_left (DS.rad_dvd n) hc⟩

/-- **`H_k(y) ≤ T_k(y)`**: the argument of `DS.hOdd_le_sR` inside one coprimality class (the fibre
of `rad` over a squarefree `q` costs at most `1/φ(q)`, `DS.fiber_le`). -/
theorem hS_le_tS (k y : ℕ) : hS k y ≤ tS k y := by
  unfold hS tS
  rw [← sum_fiberwise_of_maps_to (fun n hn => rad_mem_oddCop hn) (fun n => (1 : ℝ) / n)]
  refine sum_le_sum fun q _ => ?_
  by_cases hsq : Squarefree q
  · rw [DS.cQ_sqfree hsq]
    refine DS.fiber_le hsq _ fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := mem_filter.mp hn
    refine ⟨?_, hn2⟩
    rw [mem_oddCop] at hn1
    omega
  · have he : (oddCop k y).filter (fun n => DS.rad n = q) = ∅ :=
      filter_eq_empty_iff.mpr fun n _ h => hsq (h ▸ DS.rad_sqfree n)
    rw [he, sum_empty]
    exact DS.cQ_nonneg q

/-! ## The odd harmonic sums `H_1(N)` -/

/-- The odd `n ≤ N` are `2k + 1`, `k < (N + 1)/2`. -/
theorem oddCop_one (N : ℕ) : oddCop 1 N = (range ((N + 1) / 2)).image (fun k => 2 * k + 1) := by
  ext n
  rw [mem_oddCop, mem_image]
  simp only [mem_range, Nat.coprime_one_right_eq_true, and_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩
    exact ⟨k, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, by omega⟩⟩

/-- `H_1(N) = ∑_{k < (N+1)/2} 1/(2k + 1)`. -/
theorem hS_one (N K : ℕ) (hK : K = (N + 1) / 2) : hS 1 N = ∑ k ∈ range K, DS.fo k := by
  subst hK
  unfold hS DS.fo
  rw [oddCop_one, sum_image fun a _ b _ h => by
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega]
  exact sum_congr rfl fun k _ => by push_cast; ring

/-- **The anchor** `∑_{k < 24} 1/(2k + 1)` (the odd `n ≤ 47`). -/
noncomputable def h24 : ℝ := ∑ k ∈ range 24, DS.fo k

/-- `log(1 + 1/a) ≥ 2/(2a + 1)`: the first term of Mathlib's series in `1/(2a + 1)`. -/
theorem log_succ_ge (a : ℝ) (ha : 0 < a) : 2 / (2 * a + 1) ≤ Real.log (1 + a⁻¹) := by
  have h0 := le_hasSum (Real.hasSum_log_one_add_inv ha) 0 (fun j _ => by positivity)
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, mul_one] at h0
  calc 2 / (2 * a + 1) = 2 * (1 / (2 * a + 1)) := by ring
    _ ≤ _ := h0

/-- **The midpoint step** `1/(2k + 1) ≤ ½(log 2(k + 1) − log 2k)`, `k ≥ 1`. -/
theorem fo_le_log (k : ℕ) (hk : 1 ≤ k) :
    DS.fo k ≤ (Real.log (2 * ((k : ℝ) + 1)) - Real.log (2 * (k : ℝ))) / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have h := log_succ_ge k hk0
  have e0 : 2 * ((k : ℝ) + 1) = 2 * (k : ℝ) * (1 + (k : ℝ)⁻¹) := by
    have := mul_inv_cancel₀ hkne
    linear_combination (-2 : ℝ) * this
  have e : Real.log (2 * ((k : ℝ) + 1)) - Real.log (2 * (k : ℝ)) = Real.log (1 + (k : ℝ)⁻¹) := by
    rw [e0, Real.log_mul (by positivity) (by positivity)]
    ring
  rw [e]
  unfold DS.fo
  have e2 : 1 / (2 * (k : ℝ) + 1) = (2 / (2 * (k : ℝ) + 1)) / 2 := by ring
  rw [e2]
  linarith

/-- **`H_1` from above** (midpoint rule from `48`): `∑_{k < K} 1/(2k+1) ≤ h24 + ½(log 2K − log 48)`,
`K ≥ 24`. -/
theorem hodd_hi : ∀ K : ℕ, 24 ≤ K →
    ∑ k ∈ range K, DS.fo k ≤ h24 + (Real.log (2 * (K : ℝ)) - Real.log 48) / 2 := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have e : Real.log (2 * ((24 : ℕ) : ℝ)) = Real.log 48 := by norm_num
    rw [e, sub_self, zero_div, add_zero]
    exact le_of_eq rfl
  | succ K hK ih =>
    rw [sum_range_succ]
    have h := fo_le_log K (by omega)
    push_cast
    linarith

/-- **`H_1` from below** (trapezoid rule from `49`, `DS.trap`):
`∑_{k < K} 1/(2k+1) ≥ h24 + 1/98 + 1/(2x) + ½(log x − log 49)`, `x = 2K − 1`, `K ≥ 25`. -/
theorem hodd_lo (K : ℕ) (hK : 25 ≤ K) (x : ℝ) (hx : x = 2 * (K : ℝ) - 1) :
    h24 + 1 / 98 + 1 / (2 * x) + (Real.log x - Real.log 49) / 2 ≤ ∑ k ∈ range K, DS.fo k := by
  obtain ⟨J, rfl⟩ : ∃ J, K = 24 + J + 1 := ⟨K - 25, by omega⟩
  have h := DS.trap 24 J
  have e1 : DS.fo 24 = 1 / 49 := by
    unfold DS.fo
    norm_num
  have e3 : 2 * (((24 + J : ℕ)) : ℝ) + 1 = x := by
    rw [hx]
    push_cast
    ring
  have e2 : DS.fo (24 + J) = 1 / x := by
    unfold DS.fo
    rw [e3]
  have e4 : 2 * ((24 : ℕ) : ℝ) + 1 = 49 := by norm_num
  rw [e1, e2, e3, e4] at h
  have e5 : (1 / 49 + 1 / x) / 2 = 1 / 98 + 1 / (2 * x) := by ring
  have e6 : h24 = ∑ k ∈ range 24, DS.fo k := rfl
  linarith

/-- **`H_1(N)` from below, `log N` split off `log r`**: with `x = 2K − 1` the largest odd `≤ N`
and any `D > 0`, `log x ≥ log r − log D + 1 − (r/D)/x`. -/
theorem hS1_lo (N K : ℕ) (hK : K = (N + 1) / 2) (h25 : 25 ≤ K) (x D c : ℝ)
    (hx : x = 2 * (K : ℝ) - 1) (hD : 0 < D)
    (hc : c ≤ 1 / 98 + 1 / (2 * x) + (1 - 150000 / D / x) / 2) :
    h24 + c + (Real.log 150000 - Real.log D - Real.log 49) / 2 ≤ hS 1 N := by
  rw [hS_one N K hK]
  have h := hodd_lo K h25 x hx
  have hK25 : (25 : ℝ) ≤ K := by exact_mod_cast h25
  have hx0 : 0 < x := by rw [hx]; linarith
  have hl := Real.one_sub_inv_le_log_of_pos (x := x / (150000 / D)) (by positivity)
  rw [Real.log_div hx0.ne' (by positivity), Real.log_div (by norm_num) hD.ne', inv_div] at hl
  linarith

/-- **`H_1(N)` from above, `log N` split off `log r`**: with `y = 2K`,
`log y ≤ log r − log D + yD/r − 1`. -/
theorem hS1_hi (N K : ℕ) (hK : K = (N + 1) / 2) (h24K : 24 ≤ K) (y D c : ℝ)
    (hy : y = 2 * (K : ℝ)) (hD : 0 < D) (hc : (y * D / 150000 - 1) / 2 ≤ c) :
    hS 1 N ≤ h24 + c + (Real.log 150000 - Real.log D - Real.log 48) / 2 := by
  rw [hS_one N K hK]
  have h := hodd_hi K h24K
  rw [← hy] at h
  have hK24 : (24 : ℝ) ≤ K := by exact_mod_cast h24K
  have hy0 : 0 < y := by rw [hy]; linarith
  have hl := Real.log_le_sub_one_of_pos (x := y / (150000 / D)) (by positivity)
  rw [Real.log_div hy0.ne' (by positivity), Real.log_div (by norm_num) hD.ne',
    div_div_eq_mul_div] at hl
  linarith

/-! ## Logarithms of `2, 3, 5, 7, 11` -/

/-- `log(3^a 5^b 7^c 11^e)` in terms of the prime logarithms. -/
theorem logD_eq (D : ℝ) (a b c e : ℕ) (h : D = 3 ^ a * 5 ^ b * 7 ^ c * 11 ^ e) (A B C E : ℝ)
    (hA : (a : ℝ) = A) (hB : (b : ℝ) = B) (hC : (c : ℝ) = C) (hE : (e : ℝ) = E) :
    Real.log D = A * Real.log 3 + B * Real.log 5 + C * Real.log 7 + E * Real.log 11 := by
  rw [← hA, ← hB, ← hC, ← hE, h, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]

/-- `log(1 − x)` to `n` terms, with Mathlib's remainder bound `x^{n+1}/(1 − x)`. -/
theorem log_one_sub_bd (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    Real.log (1 - x) ≤ -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) ∧
      -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have h2 := abs_le.mp h
  constructor <;> linarith [h2.1, h2.2]

/-- `log 150000 = 4 log 2 + log 3 + 5 log 5`. -/
theorem log150000_eq : Real.log 150000 = 4 * Real.log 2 + Real.log 3 + 5 * Real.log 5 := by
  rw [show (150000 : ℝ) = 2 ^ 4 * 3 * 5 ^ 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num

/-- `log 49 = 2 log 7`. -/
theorem log49_eq : Real.log 49 = 2 * Real.log 7 := by
  rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- `log 48 = 4 log 2 + log 3`. -/
theorem log48_eq : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
  rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  norm_num

/-! ## `μ²(p)/φ(p)` at the four primes -/

/-- `μ²(3)/φ(3) = 1/2`. -/
theorem cQ3 : DS.cQ 3 = 1 / 2 := by
  rw [cQ_prime Nat.prime_three]
  norm_num

/-- `μ²(5)/φ(5) = 1/4`. -/
theorem cQ5 : DS.cQ 5 = 1 / 4 := by
  rw [cQ_prime Nat.prime_five]
  norm_num

/-- `μ²(7)/φ(7) = 1/6`. -/
theorem cQ7 : DS.cQ 7 = 1 / 6 := by
  rw [cQ_prime Nat.prime_seven]
  norm_num

/-- `μ²(11)/φ(11) = 1/10`. -/
theorem cQ11 : DS.cQ 11 = 1 / 10 := by
  rw [cQ_prime Nat.prime_eleven]
  norm_num

/-- `log 3 ∈ [1.09861228, 1.09861229]` (truth `1.0986122887`), from the series of
`log(1 − 1/4) = log 3 - 2 * log 2` to 16 terms. -/
theorem log3_bd : (1.09861228 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.09861229 := by
  obtain ⟨hu, hl⟩ := log_one_sub_bd (1 / 4) (by norm_num) (by norm_num) 16
  have e : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e] at hu hl
  norm_num [sum_range_succ] at hu hl
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith

/-- `log 5 ∈ [1.60943791, 1.60943792]` (truth `1.6094379124`), from the series of
`log(1 − 1/5) = 2 * log 2 - log 5` to 14 terms. -/
theorem log5_bd : (1.60943791 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ 1.60943792 := by
  obtain ⟨hu, hl⟩ := log_one_sub_bd (1 / 5) (by norm_num) (by norm_num) 14
  have e : Real.log (1 - 1 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 : ℝ) - 1 / 5 = 2 ^ 2 / 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e] at hu hl
  norm_num [sum_range_succ] at hu hl
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith

/-- `log 7 ∈ [1.94591014, 1.94591015]` (truth `1.9459101491`), from the series of
`log(1 − 1/8) = log 7 - 3 * log 2` to 12 terms. -/
theorem log7_bd : (1.94591014 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ 1.94591015 := by
  obtain ⟨hu, hl⟩ := log_one_sub_bd (1 / 8) (by norm_num) (by norm_num) 12
  have e : Real.log (1 - 1 / 8) = Real.log 7 - 3 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 8 = 7 / 2 ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e] at hu hl
  norm_num [sum_range_succ] at hu hl
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith

/-- `log 11 ∈ [2.39789526, 2.39789528]` (truth `2.3978952728`), from the series of
`log(1 − 1/12) = log 11 - (2 * log 2 + log 3)` to 10 terms. -/
theorem log11_bd : (2.39789526 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ 2.39789528 := by
  obtain ⟨hu, hl⟩ := log_one_sub_bd (1 / 12) (by norm_num) (by norm_num) 10
  have e : Real.log (1 - 1 / 12) = Real.log 11 - (2 * Real.log 2 + Real.log 3) := by
    rw [show (1 : ℝ) - 1 / 12 = 11 / (2 ^ 2 * 3) by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [e] at hu hl
  norm_num [sum_range_succ] at hu hl
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  have h4 := log3_bd.1
  have h5 := log3_bd.2
  constructor <;> linarith

/-- The anchor, exactly: `∑_{k < 24} 1/(2k + 1) = 2.570818086187…`. -/
theorem h24_eq : h24 = 35567319917031991744 / 13835020108241056725 := by
  unfold h24
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-! ## The `gcd(q, 1155)` split and the sieve, for every `y` -/

/-- **The `gcd` split, all four primes**: `T_1(y) ≥ ∑_{R | 1155} T_{1155}(y/R)/φ(R)` (`tS_step`
fifteen times, each prime in turn). -/
theorem tS_chain (y : ℕ) : tS 1155 y + tS 1155 (y / 11) / 10 + tS 1155 (y / 7) / 6
    + tS 1155 (y / 7 / 11) / 60 + tS 1155 (y / 5) / 4 + tS 1155 (y / 5 / 11) / 40
    + tS 1155 (y / 5 / 7) / 24 + tS 1155 (y / 5 / 7 / 11) / 240 + tS 1155 (y / 3) / 2
    + tS 1155 (y / 3 / 11) / 20 + tS 1155 (y / 3 / 7) / 12 + tS 1155 (y / 3 / 7 / 11) / 120
    + tS 1155 (y / 3 / 5) / 8 + tS 1155 (y / 3 / 5 / 11) / 80 + tS 1155 (y / 3 / 5 / 7) / 48
    + tS 1155 (y / 3 / 5 / 7 / 11) / 480 ≤ tS 1 y := by
  have s0 := tS_step 1 3 3 y Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  rw [cQ3] at s0
  have s1 := tS_step 3 5 15 y Nat.prime_five
    (by norm_num) (by decide) (by norm_num)
  rw [cQ5] at s1
  have s2 := tS_step 3 5 15 (y / 3) Nat.prime_five
    (by norm_num) (by decide) (by norm_num)
  rw [cQ5] at s2
  have s3 := tS_step 15 7 105 y Nat.prime_seven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ7] at s3
  have s4 := tS_step 15 7 105 (y / 5) Nat.prime_seven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ7] at s4
  have s5 := tS_step 15 7 105 (y / 3) Nat.prime_seven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ7] at s5
  have s6 := tS_step 15 7 105 (y / 3 / 5) Nat.prime_seven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ7] at s6
  have s7 := tS_step 105 11 1155 y Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s7
  have s8 := tS_step 105 11 1155 (y / 7) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s8
  have s9 := tS_step 105 11 1155 (y / 5) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s9
  have s10 := tS_step 105 11 1155 (y / 5 / 7) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s10
  have s11 := tS_step 105 11 1155 (y / 3) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s11
  have s12 := tS_step 105 11 1155 (y / 3 / 7) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s12
  have s13 := tS_step 105 11 1155 (y / 3 / 5) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s13
  have s14 := tS_step 105 11 1155 (y / 3 / 5 / 7) Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  rw [cQ11] at s14
  linarith

/-- **The sieve, all four primes**: `H_{1155}(y) = ∑_{d | 1155} μ(d)/d · H_1(y/d)` (`hS_step`
fifteen times). -/
theorem hS_expand (y : ℕ) : hS 1155 y = hS 1 y - hS 1 (y / 3) / 3 - hS 1 (y / 5) / 5
    + hS 1 (y / 5 / 3) / 15 - hS 1 (y / 7) / 7 + hS 1 (y / 7 / 3) / 21 + hS 1 (y / 7 / 5) / 35
    - hS 1 (y / 7 / 5 / 3) / 105 - hS 1 (y / 11) / 11 + hS 1 (y / 11 / 3) / 33
    + hS 1 (y / 11 / 5) / 55 - hS 1 (y / 11 / 5 / 3) / 165 + hS 1 (y / 11 / 7) / 77
    - hS 1 (y / 11 / 7 / 3) / 231 - hS 1 (y / 11 / 7 / 5) / 385
    + hS 1 (y / 11 / 7 / 5 / 3) / 1155 := by
  have e0 := hS_step 105 11 1155 y Nat.prime_eleven
    (by norm_num) (by decide) (by norm_num)
  have e1 := hS_step 15 7 105 y Nat.prime_seven
    (by norm_num) (by decide) (by norm_num)
  have e2 := hS_step 15 7 105 (y / 11) Nat.prime_seven
    (by norm_num) (by decide) (by norm_num)
  have e3 := hS_step 3 5 15 y Nat.prime_five
    (by norm_num) (by decide) (by norm_num)
  have e4 := hS_step 3 5 15 (y / 7) Nat.prime_five
    (by norm_num) (by decide) (by norm_num)
  have e5 := hS_step 3 5 15 (y / 11) Nat.prime_five
    (by norm_num) (by decide) (by norm_num)
  have e6 := hS_step 3 5 15 (y / 11 / 7) Nat.prime_five
    (by norm_num) (by decide) (by norm_num)
  have e7 := hS_step 1 3 3 y Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e8 := hS_step 1 3 3 (y / 5) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e9 := hS_step 1 3 3 (y / 7) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e10 := hS_step 1 3 3 (y / 7 / 5) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e11 := hS_step 1 3 3 (y / 11) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e12 := hS_step 1 3 3 (y / 11 / 5) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e13 := hS_step 1 3 3 (y / 11 / 7) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  have e14 := hS_step 1 3 3 (y / 11 / 7 / 5) Nat.prime_three
    (by norm_num) (by decide) (by norm_num)
  linarith

/-! ## `H_1(N)` at the 70 arguments, each in the direction its coefficient needs

Generated: `N = ⌊150000/D⌋` for `D = Rd`, `R, d | 1155`; `D` below is the smallest such.
Lower bounds where `c_N > 0` (`hS1_lo`), upper where `c_N < 0` (`hS1_hi`); `N ≤ 48` exactly.
-/

/-- `H_1(150000) ≥ 6.5943072934` (`D = 1`; coefficient `1`). -/
theorem bN_150000 : (6.5943072934 : ℝ) ≤ hS 1 150000 := by
  have h := hS1_lo 150000 75000 (by norm_num) (by norm_num) 149999 1 (0.010204081632) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1 0 0 0 0 (by norm_num) 0 0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(50000) ≥ 6.0450011534` (`D = 3`; coefficient `1/6`). -/
theorem bN_50000 : (6.0450011534 : ℝ) ≤ hS 1 50000 := by
  have h := hS1_lo 50000 25000 (by norm_num) (by norm_num) 49999 3 (0.010204081632) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 3 1 0 0 0 (by norm_num) 1 0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(30000) ≥ 5.7895883384` (`D = 5`; coefficient `1/20`). -/
theorem bN_30000 : (5.7895883384 : ℝ) ≤ hS 1 30000 := by
  have h := hS1_lo 30000 15000 (by norm_num) (by norm_num) 29999 5 (0.010204081632) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 5 0 1 0 0 (by norm_num) 0 1 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(21428) ≥ 5.6213388841` (`D = 7`; coefficient `1/42`). -/
theorem bN_21428 : (5.6213388841 : ℝ) ≤ hS 1 21428 := by
  have h := hS1_lo 21428 10714 (by norm_num) (by norm_num) 21427 7 (0.010190747321) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 7 0 0 1 0 (by norm_num) 0 0 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(16666) ≤ 5.4957806062` (`D = 9`; coefficient `-1/6`). -/
theorem bN_16666 : hS 1 16666 ≤ 5.4957806062 := by
  have h := hS1_hi 16666 8333 (by norm_num) (by norm_num) 16666 9 (-0.00002) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 9 2 0 0 0 (by norm_num) 2 0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(13636) ≥ 5.3953463187` (`D = 11`; coefficient `1/110`). -/
theorem bN_13636 : (5.3953463187 : ℝ) ≤ hS 1 13636 := by
  have h := hS1_lo 13636 6818 (by norm_num) (by norm_num) 13635 11 (0.010190746965) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 11 0 0 0 1 (by norm_num) 0 0 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(10000) ≥ 5.2402821984` (`D = 15`; coefficient `1/120`). -/
theorem bN_10000 : (5.2402821984 : ℝ) ≤ hS 1 10000 := by
  have h := hS1_lo 10000 5000 (by norm_num) (by norm_num) 9999 15 (0.010204081632) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 15 1 1 0 0 (by norm_num) 1 1 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(7142) ≥ 5.0719860628` (`D = 21`; coefficient `1/252`). -/
theorem bN_7142 : (5.0719860628 : ℝ) ≤ hS 1 7142 := by
  have h := hS1_lo 7142 3571 (by norm_num) (by norm_num) 7141 21 (0.010144066028) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 21 1 0 1 0 (by norm_num) 1 0 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(6000) ≤ 4.9849749662` (`D = 25`; coefficient `-1/20`). -/
theorem bN_6000 : hS 1 6000 ≤ 4.9849749662 := by
  have h := hS1_hi 6000 3000 (by norm_num) (by norm_num) 6000 25 (0) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 25 0 2 0 0 (by norm_num) 0 2 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(4545) ≥ 4.8461135194` (`D = 33`; coefficient `1/660`). -/
theorem bN_4545 : (4.8461135194 : ℝ) ≤ hS 1 4545 := by
  have h := hS1_lo 4545 2273 (by norm_num) (by norm_num) 4545 33 (0.010264087633) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 33 1 0 0 1 (by norm_num) 1 0 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(4285) ≥ 4.8166666023` (`D = 35`; coefficient `1/840`). -/
theorem bN_4285 : (4.8166666023 : ℝ) ≤ hS 1 4285 := by
  have h := hS1_lo 4285 2143 (by norm_num) (by norm_num) 4285 35 (0.010237420522) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 35 0 1 1 0 (by norm_num) 0 1 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(3333) ≤ 4.6911816462` (`D = 45`; coefficient `-1/120`). -/
theorem bN_3333 : hS 1 3333 ≤ 4.6911816462 := by
  have h := hS1_hi 3333 1667 (by norm_num) (by norm_num) 3334 45 (0.0001) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 45 2 1 0 0 (by norm_num) 2 1 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(3061) ≤ 4.6486294129` (`D = 49`; coefficient `-1/42`). -/
theorem bN_3061 : hS 1 3061 ≤ 4.6486294129 := by
  have h := hS1_hi 3061 1531 (by norm_num) (by norm_num) 3062 49 (0.000126666667) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 49 0 0 2 0 (by norm_num) 0 0 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(2727) ≥ 4.590774045` (`D = 55`; coefficient `1/2200`). -/
theorem bN_2727 : (4.590774045 : ℝ) ≤ hS 1 2727 := by
  have h := hS1_lo 2727 1364 (by norm_num) (by norm_num) 2727 55 (0.0103374283) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 55 0 1 0 1 (by norm_num) 0 1 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(2380) ≤ 4.5226455362` (`D = 63`; coefficient `-1/252`). -/
theorem bN_2380 : hS 1 2380 ≤ 4.5226455362 := by
  have h := hS1_hi 2380 1190 (by norm_num) (by norm_num) 2380 63 (-0.0002) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 63 2 0 1 0 (by norm_num) 2 0 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(2000) ≤ 4.4356688262` (`D = 75`; coefficient `-1/120`). -/
theorem bN_2000 : hS 1 2000 ≤ 4.4356688262 := by
  have h := hS1_hi 2000 1000 (by norm_num) (by norm_num) 2000 75 (0) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 75 1 2 0 0 (by norm_num) 1 2 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(1948) ≥ 4.4223912378` (`D = 77`; coefficient `1/4620`). -/
theorem bN_1948 : (4.4223912378 : ℝ) ≤ hS 1 1948 := by
  have h := hS1_lo 1948 974 (by norm_num) (by norm_num) 1947 77 (0.010190741095) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 77 0 0 1 1 (by norm_num) 0 0 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(1515) ≤ 4.2971329762` (`D = 99`; coefficient `-1/660`). -/
theorem bN_1515 : hS 1 1515 ≤ 4.2971329762 := by
  have h := hS1_hi 1515 758 (by norm_num) (by norm_num) 1516 99 (0.00028) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 99 2 0 0 1 (by norm_num) 2 0 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(1428) ≥ 4.2671269031` (`D = 105`; coefficient `1/5040`). -/
theorem bN_1428 : (4.2671269031 : ℝ) ≤ hS 1 1428 := by
  have h := hS1_lo 1428 714 (by norm_num) (by norm_num) 1427 105 (0.01000386139) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 105 1 1 1 0 (by norm_num) 1 1 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(1239) ≤ 4.1966509596` (`D = 121`; coefficient `-1/110`). -/
theorem bN_1239 : hS 1 1239 ≤ 4.1966509596 := by
  have h := hS1_hi 1239 620 (by norm_num) (by norm_num) 1240 121 (0.000133333334) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 121 0 0 0 2 (by norm_num) 0 0 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(1020) ≤ 4.0989966062` (`D = 147`; coefficient `-1/252`). -/
theorem bN_1020 : hS 1 1020 ≤ 4.0989966062 := by
  have h := hS1_hi 1020 510 (by norm_num) (by norm_num) 1020 147 (-0.0002) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 147 1 0 2 0 (by norm_num) 1 0 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(909) ≥ 4.0418346084` (`D = 165`; coefficient `1/13200`). -/
theorem bN_909 : (4.0418346084 : ℝ) ≤ hS 1 909 := by
  have h := hS1_lo 909 455 (by norm_num) (by norm_num) 909 165 (0.010704131637) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 165 1 1 0 1 (by norm_num) 1 1 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(857) ≤ 4.0125198962` (`D = 175`; coefficient `-1/840`). -/
theorem bN_857 : hS 1 857 ≤ 4.0125198962 := by
  have h := hS1_hi 857 429 (by norm_num) (by norm_num) 858 175 (0.0005) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 175 0 2 1 0 (by norm_num) 0 2 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(666) ≥ 3.8857558452` (`D = 225`; coefficient `1/120`). -/
theorem bN_666 : (3.8857558452 : ℝ) ≤ hS 1 666 := by
  have h := hS1_lo 666 333 (by norm_num) (by norm_num) 665 225 (0.009702828499) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 225 2 2 0 0 (by norm_num) 2 2 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(649) ≥ 3.8735987085` (`D = 231`; coefficient `1/27720`). -/
theorem bN_649 : (3.8735987085 : ℝ) ≤ hS 1 649 := by
  have h := hS1_lo 649 325 (by norm_num) (by norm_num) 649 231 (0.010704351778) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 231 1 0 1 1 (by norm_num) 1 0 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(612) ≤ 3.8435837862` (`D = 245`; coefficient `-1/840`). -/
theorem bN_612 : hS 1 612 ≤ 3.8435837862 := by
  have h := hS1_hi 612 306 (by norm_num) (by norm_num) 612 245 (-0.0002) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 245 0 1 2 0 (by norm_num) 0 1 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(545) ≤ 3.7865273362` (`D = 275`; coefficient `-1/2200`). -/
theorem bN_545 : hS 1 545 ≤ 3.7865273362 := by
  have h := hS1_hi 545 273 (by norm_num) (by norm_num) 546 275 (0.0005) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 275 0 2 0 1 (by norm_num) 0 2 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(476) ≤ 3.7179265762` (`D = 315`; coefficient `-1/5040`). -/
theorem bN_476 : hS 1 476 ≤ 3.7179265762 := by
  have h := hS1_hi 476 238 (by norm_num) (by norm_num) 476 315 (-0.0002) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 315 2 1 1 0 (by norm_num) 2 1 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(413) ≤ 3.6481514862` (`D = 363`; coefficient `-1/660`). -/
theorem bN_413 : hS 1 413 ≤ 3.6481514862 := by
  have h := hS1_hi 413 207 (by norm_num) (by norm_num) 414 363 (0.00094) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 363 1 0 0 2 (by norm_num) 1 0 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(389) ≥ 3.6181864079` (`D = 385`; coefficient `1/92400`). -/
theorem bN_389 : (3.6181864079 : ℝ) ≤ hS 1 389 := by
  have h := hS1_lo 389 195 (by norm_num) (by norm_num) 389 385 (0.010704866195) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 385 0 1 1 1 (by norm_num) 0 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(340) ≥ 3.5495841881` (`D = 441`; coefficient `1/252`). -/
theorem bN_340 : (3.5495841881 : ℝ) ≤ hS 1 340 := by
  have h := hS1_lo 340 170 (by norm_num) (by norm_num) 339 441 (0.010003411394) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 441 2 0 2 0 (by norm_num) 2 0 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(303) ≤ 3.4937340162` (`D = 495`; coefficient `-1/13200`). -/
theorem bN_303 : hS 1 303 ≤ 3.4937340162 := by
  have h := hS1_hi 303 152 (by norm_num) (by norm_num) 304 495 (0.0016) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 495 2 1 0 1 (by norm_num) 2 1 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(285) ≤ 3.4632137562` (`D = 525`; coefficient `-1/5040`). -/
theorem bN_285 : hS 1 285 ≤ 3.4632137562 := by
  have h := hS1_hi 285 143 (by norm_num) (by norm_num) 286 525 (0.0005) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 525 1 2 1 0 (by norm_num) 1 2 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(278) ≤ 3.4490284496` (`D = 539`; coefficient `-1/4620`). -/
theorem bN_278 : hS 1 278 ≤ 3.4490284496 := by
  have h := hS1_hi 278 139 (by norm_num) (by norm_num) 278 539 (-0.000526666666) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 539 0 0 2 1 (by norm_num) 0 0 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(247) ≤ 3.3919319996` (`D = 605`; coefficient `-1/2200`). -/
theorem bN_247 : hS 1 247 ≤ 3.3919319996 := by
  have h := hS1_hi 247 124 (by norm_num) (by norm_num) 248 605 (0.000133333334) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 605 0 1 0 2 (by norm_num) 0 1 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(216) ≤ 3.3228579062` (`D = 693`; coefficient `-1/27720`). -/
theorem bN_216 : hS 1 216 ≤ 3.3228579062 := by
  have h := hS1_hi 216 108 (by norm_num) (by norm_num) 216 693 (-0.00104) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 693 2 0 1 1 (by norm_num) 2 0 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(204) ≤ 3.2942776462` (`D = 735`; coefficient `-1/5040`). -/
theorem bN_204 : hS 1 204 ≤ 3.2942776462 := by
  have h := hS1_hi 204 102 (by norm_num) (by norm_num) 204 735 (-0.0002) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 735 1 1 2 0 (by norm_num) 1 1 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(181) ≤ 3.2372211962` (`D = 825`; coefficient `-1/13200`). -/
theorem bN_181 : hS 1 181 ≤ 3.2372211962 := by
  have h := hS1_hi 181 91 (by norm_num) (by norm_num) 182 825 (0.0005) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 825 1 2 0 1 (by norm_num) 1 2 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(177) ≤ 3.2261158896` (`D = 847`; coefficient `-1/4620`). -/
theorem bN_177 : hS 1 177 ≤ 3.2261158896 := by
  have h := hS1_hi 177 89 (by norm_num) (by norm_num) 178 847 (0.002553333334) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 847 0 0 1 2 (by norm_num) 0 0 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(137) ≥ 3.0987448129` (`D = 1089`; coefficient `1/660`). -/
theorem bN_137 : (3.0987448129 : ℝ) ≤ hS 1 137 := by
  have h := hS1_lo 137 69 (by norm_num) (by norm_num) 137 1089 (0.011149166187) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1089 2 0 0 2 (by norm_num) 2 0 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(129) ≥ 3.068882856` (`D = 1155`; coefficient `1/554400`). -/
theorem bN_129 : (3.068882856 : ℝ) ≤ hS 1 129 := by
  have h := hS1_lo 129 65 (by norm_num) (by norm_num) 129 1155 (0.010707454229) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1155 1 1 1 1 (by norm_num) 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(122) ≥ 3.0371039458` (`D = 1225`; coefficient `1/840`). -/
theorem bN_122 : (3.0371039458 : ℝ) ≤ hS 1 122 := by
  have h := hS1_lo 122 61 (by norm_num) (by norm_num) 121 1225 (0.008348794063) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1225 0 2 2 0 (by norm_num) 0 2 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(95) ≥ 2.9173120484` (`D = 1575`; coefficient `1/5040`). -/
theorem bN_95 : (2.9173120484 : ℝ) ≤ hS 1 95 := by
  have h := hS1_lo 95 48 (by norm_num) (by norm_num) 95 1575 (0.014214106695) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1575 2 2 1 0 (by norm_num) 2 2 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(92) ≤ 2.8961289762` (`D = 1617`; coefficient `-1/27720`). -/
theorem bN_92 : hS 1 92 ≤ 2.8961289762 := by
  have h := hS1_hi 92 46 (by norm_num) (by norm_num) 92 1617 (-0.00412) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1617 1 0 2 1 (by norm_num) 1 0 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(82) ≤ 2.8385925262` (`D = 1815`; coefficient `-1/13200`). -/
theorem bN_82 : hS 1 82 ≤ 2.8385925262 := by
  have h := hS1_hi 82 41 (by norm_num) (by norm_num) 82 1815 (-0.0039) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1815 1 1 0 2 (by norm_num) 1 1 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(77) ≤ 2.8135722662` (`D = 1925`; coefficient `-1/92400`). -/
theorem bN_77 : hS 1 77 ≤ 2.8135722662 := by
  have h := hS1_hi 77 39 (by norm_num) (by norm_num) 78 1925 (0.0005) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 1925 0 2 1 1 (by norm_num) 0 2 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(68) ≥ 2.7448628371` (`D = 2205`; coefficient `1/5040`). -/
theorem bN_68 : (2.7448628371 : ℝ) ≤ hS 1 68 := by
  have h := hS1_lo 68 34 (by norm_num) (by norm_num) 67 2205 (0.010001015331) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 2205 2 1 2 0 (by norm_num) 2 1 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(60) ≥ 2.6821733515` (`D = 2475`; coefficient `1/13200`). -/
theorem bN_60 : (2.6821733515 : ℝ) ≤ hS 1 60 := by
  have h := hS1_lo 60 30 (by norm_num) (by norm_num) 59 2475 (0.005067974801) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 2475 2 2 0 1 (by norm_num) 2 2 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(59) ≤ 2.6824564162` (`D = 2541`; coefficient `-1/27720`). -/
theorem bN_59 : hS 1 59 ≤ 2.6824564162 := by
  have h := hS1_hi 59 30 (by norm_num) (by norm_num) 60 2541 (0.0082) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 2541 1 0 1 2 (by norm_num) 1 0 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(55) ≤ 2.6479028229` (`D = 2695`; coefficient `-1/92400`). -/
theorem bN_55 : hS 1 55 ≤ 2.6479028229 := by
  have h := hS1_hi 55 28 (by norm_num) (by norm_num) 56 2695 (0.003066666667) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 2695 0 1 2 1 (by norm_num) 0 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log48_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(49) ≥ 2.591190666` (`D = 3025`; coefficient `1/2200`). -/
theorem bN_49 : (2.591190666 : ℝ) ≤ hS 1 49 := by
  have h := hS1_lo 49 25 (by norm_num) (by norm_num) 49 3025 (0.01442064429) (by norm_num)
    (by norm_num) (by norm_num)
  have hD := logD_eq 3025 0 2 0 2 (by norm_num) 0 2 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith [log150000_eq, log49_eq, h24_eq,
    log3_bd.1, log3_bd.2, log5_bd.1, log5_bd.2, log7_bd.1, log7_bd.2,
    log11_bd.1, log11_bd.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `H_1(43)`, summed exactly (coefficient `-1/554400`). -/
theorem bN_43 : hS 1 43 ≤ 2.5273192683 := by
  rw [hS_one 43 22 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(40)`, summed exactly (coefficient `1/5040`). -/
theorem bN_40 : (2.4796732103 : ℝ) ≤ hS 1 40 := by
  rw [hS_one 40 20 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(35)`, summed exactly (coefficient `-1/92400`). -/
theorem bN_35 : hS 1 35 ≤ 2.4270051577 := by
  rw [hS_one 35 18 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(30)`, summed exactly (coefficient `1/27720`). -/
theorem bN_30 : (2.3358726343 : ℝ) ≤ hS 1 30 := by
  rw [hS_one 30 15 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(27)`, summed exactly (coefficient `1/13200`). -/
theorem bN_27 : (2.3013898756 : ℝ) ≤ hS 1 27 := by
  rw [hS_one 27 14 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(25)`, summed exactly (coefficient `17/79200`). -/
theorem bN_25 : (2.2643528386 : ℝ) ≤ hS 1 25 := by
  rw [hS_one 25 13 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(19)`, summed exactly (coefficient `1/27720`). -/
theorem bN_19 : (2.1332555301 : ℝ) ≤ hS 1 19 := by
  rw [hS_one 19 10 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(18)`, summed exactly (coefficient `-1/554400`). -/
theorem bN_18 : hS 1 18 ≤ 2.0806239513 := by
  rw [hS_one 18 9 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(16)`, summed exactly (coefficient `1/13200`). -/
theorem bN_16 : (2.0218004218 : ℝ) ≤ hS 1 16 := by
  rw [hS_one 16 8 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(13)`, summed exactly (coefficient `-1/5040`). -/
theorem bN_13 : hS 1 13 ≤ 1.9551337552 := by
  rw [hS_one 13 7 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(11)`, summed exactly (coefficient `1/110880`). -/
theorem bN_11 : (1.8782106782 : ℝ) ≤ hS 1 11 := by
  rw [hS_one 11 6 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(8)`, summed exactly (coefficient `1/26400`). -/
theorem bN_8 : (1.6761904761 : ℝ) ≤ hS 1 8 := by
  rw [hS_one 8 4 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(7)`, summed exactly (coefficient `1/92400`). -/
theorem bN_7 : (1.6761904761 : ℝ) ≤ hS 1 7 := by
  rw [hS_one 7 4 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(6)`, summed exactly (coefficient `1/554400`). -/
theorem bN_6 : (1.5333333333 : ℝ) ≤ hS 1 6 := by
  rw [hS_one 6 3 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(5)`, summed exactly (coefficient `-1/15400`). -/
theorem bN_5 : hS 1 5 ≤ 1.5333333334 := by
  rw [hS_one 5 3 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(3)`, summed exactly (coefficient `1/277200`). -/
theorem bN_3 : (1.3333333333 : ℝ) ≤ hS 1 3 := by
  rw [hS_one 3 2 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(2)`, summed exactly (coefficient `-19/554400`). -/
theorem bN_2 : hS 1 2 ≤ 1 := by
  rw [hS_one 2 1 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(1)`, summed exactly (coefficient `-1/92400`). -/
theorem bN_1 : hS 1 1 ≤ 1 := by
  rw [hS_one 1 1 (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, DS.fo]
  norm_num

/-- `H_1(0)`, summed exactly (coefficient `-1/277200`). -/
theorem bN_0 : hS 1 0 = 0 := by
  rw [hS_one 0 0 (by norm_num), sum_range_zero]

/-! ## The assembly at `r = 150000` -/

/-- **`S(r) ≥ ∑_N c_N H_1(N)`**: `tS_chain` at `r`, `hS_le_tS` and `hS_expand` at the 16
arguments `r/R`, collected (exact coefficients). -/
theorem sR_ge_comb : hS 1 150000 + hS 1 50000 / 6 + hS 1 30000 / 20 + hS 1 21428 / 42
    - hS 1 16666 / 6 + hS 1 13636 / 110 + hS 1 10000 / 120 + hS 1 7142 / 252 - hS 1 6000 / 20
    + hS 1 4545 / 660 + hS 1 4285 / 840 - hS 1 3333 / 120 - hS 1 3061 / 42 + hS 1 2727 / 2200
    - hS 1 2380 / 252 - hS 1 2000 / 120 + hS 1 1948 / 4620 - hS 1 1515 / 660 + hS 1 1428 / 5040
    - hS 1 1239 / 110 - hS 1 1020 / 252 + hS 1 909 / 13200 - hS 1 857 / 840 + hS 1 666 / 120
    + hS 1 649 / 27720 - hS 1 612 / 840 - hS 1 545 / 2200 - hS 1 476 / 5040 - hS 1 413 / 660
    + hS 1 389 / 92400 + hS 1 340 / 252 - hS 1 303 / 13200 - hS 1 285 / 5040 - hS 1 278 / 4620
    - hS 1 247 / 2200 - hS 1 216 / 27720 - hS 1 204 / 5040 - hS 1 181 / 13200 - hS 1 177 / 4620
    + hS 1 137 / 660 + hS 1 129 / 554400 + hS 1 122 / 840 + hS 1 95 / 5040 - hS 1 92 / 27720
    - hS 1 82 / 13200 - hS 1 77 / 92400 + hS 1 68 / 5040 + hS 1 60 / 13200 - hS 1 59 / 27720
    - hS 1 55 / 92400 + hS 1 49 / 2200 - hS 1 43 / 554400 + hS 1 40 / 5040 - hS 1 35 / 92400
    + hS 1 30 / 27720 + hS 1 27 / 13200 + 17 * hS 1 25 / 79200 + hS 1 19 / 27720 - hS 1 18 / 554400
    + hS 1 16 / 13200 - hS 1 13 / 5040 + hS 1 11 / 110880 + hS 1 8 / 26400 + hS 1 7 / 92400
    + hS 1 6 / 554400 - hS 1 5 / 15400 + hS 1 3 / 277200 - 19 * hS 1 2 / 554400 - hS 1 1 / 92400
    - hS 1 0 / 277200 ≤ DS.sR := by
  have hA := tS_chain 150000
  simp only [Nat.reduceDiv] at hA
  have hB0 := hS_le_tS 1155 150000
  have hC0 := hS_expand 150000
  simp only [Nat.reduceDiv] at hC0
  have hB1 := hS_le_tS 1155 13636
  have hC1 := hS_expand 13636
  simp only [Nat.reduceDiv] at hC1
  have hB2 := hS_le_tS 1155 21428
  have hC2 := hS_expand 21428
  simp only [Nat.reduceDiv] at hC2
  have hB3 := hS_le_tS 1155 1948
  have hC3 := hS_expand 1948
  simp only [Nat.reduceDiv] at hC3
  have hB4 := hS_le_tS 1155 30000
  have hC4 := hS_expand 30000
  simp only [Nat.reduceDiv] at hC4
  have hB5 := hS_le_tS 1155 2727
  have hC5 := hS_expand 2727
  simp only [Nat.reduceDiv] at hC5
  have hB6 := hS_le_tS 1155 4285
  have hC6 := hS_expand 4285
  simp only [Nat.reduceDiv] at hC6
  have hB7 := hS_le_tS 1155 389
  have hC7 := hS_expand 389
  simp only [Nat.reduceDiv] at hC7
  have hB8 := hS_le_tS 1155 50000
  have hC8 := hS_expand 50000
  simp only [Nat.reduceDiv] at hC8
  have hB9 := hS_le_tS 1155 4545
  have hC9 := hS_expand 4545
  simp only [Nat.reduceDiv] at hC9
  have hB10 := hS_le_tS 1155 7142
  have hC10 := hS_expand 7142
  simp only [Nat.reduceDiv] at hC10
  have hB11 := hS_le_tS 1155 649
  have hC11 := hS_expand 649
  simp only [Nat.reduceDiv] at hC11
  have hB12 := hS_le_tS 1155 10000
  have hC12 := hS_expand 10000
  simp only [Nat.reduceDiv] at hC12
  have hB13 := hS_le_tS 1155 909
  have hC13 := hS_expand 909
  simp only [Nat.reduceDiv] at hC13
  have hB14 := hS_le_tS 1155 1428
  have hC14 := hS_expand 1428
  simp only [Nat.reduceDiv] at hC14
  have hB15 := hS_le_tS 1155 129
  have hC15 := hS_expand 129
  simp only [Nat.reduceDiv] at hC15
  rw [sR_eq]
  linarith

/-- **`S(r) ≥ 6.76`** (truth `6.7987792`; certified `6.7601212`; `DS.sR_ge` had `6.5942`). -/
theorem sR_ge_sharp : (6.76 : ℝ) ≤ DS.sR := by
  linarith [sR_ge_comb, bN_150000, bN_50000, bN_30000, bN_21428, bN_16666, bN_13636, bN_10000,
    bN_7142, bN_6000, bN_4545, bN_4285, bN_3333, bN_3061, bN_2727, bN_2380, bN_2000, bN_1948,
    bN_1515, bN_1428, bN_1239, bN_1020, bN_909, bN_857, bN_666, bN_649, bN_612, bN_545, bN_476,
    bN_413, bN_389, bN_340, bN_303, bN_285, bN_278, bN_247, bN_216, bN_204, bN_181, bN_177, bN_137,
    bN_129, bN_122, bN_95, bN_92, bN_82, bN_77, bN_68, bN_60, bN_59, bN_55, bN_49, bN_43, bN_40,
    bN_35, bN_30, bN_27, bN_25, bN_19, bN_18, bN_16, bN_13, bN_11, bN_8, bN_7, bN_6, bN_5, bN_3,
    bN_2, bN_1, bN_0]

end Principia.Common.TernaryGoldbach.SF
