/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIYuttoConv
import Principia.Common.TernaryGoldbach.TypeIIYuttoEuler
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

/-!
# `M2Y.KSumH` and `M2Y.KSumQ` PROVED — the `a`-sums as finite Euler products

For a completely multiplicative weight `w ≥ 0` with `w(p) < p`, `F(a) = aK(2d, a)·w(a)` is
multiplicative and its local sum at `p` is at most `1 + c_p^{-1}·r/(1 − r)`, `r = w(p)/p`,
`c_p = 1` if `p | 2d` and `p + 1` otherwise (`M2YC.A_pp`, geometric series). That is
`β_p = 1/(1 − r)` at `p | 2d` and `α_p = 1 + r/((p+1)(1 − r))` otherwise, and `β_p = α_p·ρ_p`
with `ρ_p = (p+1)/((p+1)(1 − r) + r)` — `M2Y.rhoH` for `w = √`, `M2Y.rhoQ` for `w = ⁴√`. So

`∑_{a ≤ N} aK(2d, a)w(a) ≤ β_2 · ∏_{3 ≤ p ≤ N} α_p · ∏_{p | d} ρ_p`.

The odd product is bounded by `M2YE.prod_primes_le`: the 24 odd primes below `101` explicitly
(with `⌊1000√p⌋/1000 ≤ √p`, `⌊1000·p^{1/4}⌋/1000 ≤ p^{1/4}`, evaluated by `norm_num`) and the tail
`α_p − 1 ≤ C/(p√p)` for `p ≥ 101`. Kernel-checked arithmetic only; no computation is cited.

```
 local_le, ksum_gen, ksum_split     the Euler product and its split
 kSumH : M2Y.KSumH    (2 + √2)·1.9154/(1 − 0.1117) ≤ 7.37 ≤ 8                   PROVED
 kSumQ : M2Y.KSumQ    2.4669·1.4172/(1 − 0.0354) ≤ 3.63 ≤ 4                     PROVED
```
-/

namespace Principia.Common.TernaryGoldbach.M2YK

open Finset

/-! ## (1) The generic Euler bound -/

theorem pow_w (w : ℕ → ℝ) (hw1 : w 1 = 1) (hwm : ∀ m n, w (m * n) = w m * w n) (p j : ℕ) :
    w (p ^ j) = w p ^ j := by
  induction j with
  | zero => simp [hw1]
  | succ j ih => rw [pow_succ, hwm, ih, pow_succ]

/-- `c_p`. -/
noncomputable def cc (k p : ℕ) : ℝ := if p ∣ k then 1 else (p : ℝ) + 1

theorem cc_ge (k p : ℕ) : 1 ≤ cc k p := by
  unfold cc
  have := Nat.cast_nonneg (α := ℝ) p
  split_ifs <;> linarith

/-- **The local sum**: `∑_{j ≤ N} aK(k, p^j)w(p)^j ≤ 1 + c_p^{-1}·r/(1 − r)`. -/
theorem local_le (k p N : ℕ) (hp : p.Prime) (w : ℕ → ℝ) (hw1 : w 1 = 1)
    (hwm : ∀ m n, w (m * n) = w m * w n) (hwp0 : 0 ≤ w p) (hwp : w p < p) :
    ∑ j ∈ range (N + 1), M2Y.aK k (p ^ j) * w (p ^ j) ≤
      1 + 1 / cc k p * ((w p / p) / (1 - w p / p)) := by
  have hc1 := cc_ge k p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set r := w p / p with hr
  have hr0 : 0 ≤ r := div_nonneg hwp0 hp0.le
  have hr1 : r < 1 := by rw [hr, div_lt_one hp0]; exact hwp
  rw [Finset.sum_range_succ']
  have hterm : ∀ j ∈ range N, M2Y.aK k (p ^ (j + 1)) * w (p ^ (j + 1)) =
      1 / cc k p * r ^ (j + 1) := by
    intro j _
    have h := M2YC.A_pp k p (j + 1) hp
    rw [M2YC.fA_apply] at h
    rw [h, if_neg (Nat.succ_ne_zero j), pow_w w hw1 hwm, hr, div_pow]
    unfold cc
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h0 : M2Y.aK k (p ^ 0) * w (p ^ 0) = 1 := by simp [M2Y.aK, hw1]
  rw [h0]
  have hgeom : ∑ j ∈ range N, r ^ (j + 1) ≤ r / (1 - r) := by
    have e : ∑ j ∈ range N, r ^ (j + 1) = r * ∑ j ∈ range N, r ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hg := geom_sum_mul r N
    have hrN : 0 ≤ r ^ N := pow_nonneg hr0 N
    have hs0 : 0 ≤ ∑ j ∈ range N, r ^ j := Finset.sum_nonneg fun j _ => pow_nonneg hr0 j
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have := mul_le_mul_of_nonneg_left hgeom (by positivity : (0 : ℝ) ≤ 1 / cc k p)
  linarith

/-- **The Euler bound for `aK(k, ·)·w`.** -/
theorem ksum_gen (k N : ℕ) (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hw1 : w 1 = 1)
    (hwm : ∀ m n, w (m * n) = w m * w n) (hwp : ∀ p : ℕ, p.Prime → w p < p) :
    ∑ a ∈ Icc 1 N, M2Y.aK k a * w a ≤
      ∏ p ∈ (range (N + 1)).filter Nat.Prime,
        (1 + 1 / cc k p * ((w p / p) / (1 - w p / p))) := by
  refine (M2YE.euler_le (fun a => M2Y.aK k a * w a)
    (fun n => mul_nonneg (M2Y.aK_nonneg k n) (hw0 n)) (by simp [M2Y.aK, hw1])
    (fun m n _ _ h => ?_) N).trans ?_
  · have hA := (M2YC.isMult_A k).map_mul_of_coprime h
    simp only [M2YC.fA_apply] at hA
    rw [hA, hwm]
    ring
  · refine Finset.prod_le_prod (fun p _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (M2Y.aK_nonneg k _) (hw0 _)) fun p hp => ?_
    have hp' := (Finset.mem_filter.mp hp).2
    exact local_le k p N hp' w hw1 hwm (hw0 p) (hwp p hp')

/-! ## (2) Splitting off `p = 2` and `p | d` -/

/-- `α_p = 1 + r/((p+1)(1 − r))`. -/
noncomputable def alp (p : ℕ) (r : ℝ) : ℝ := 1 + r / (((p : ℝ) + 1) * (1 - r))

/-- `ρ_p = (p+1)/((p+1)(1 − r) + r)`. -/
noncomputable def rho (p : ℕ) (r : ℝ) : ℝ := ((p : ℝ) + 1) / (((p : ℝ) + 1) * (1 - r) + r)

theorem rho_ge_one (p : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : 1 ≤ rho p r := by
  unfold rho
  have hp := Nat.cast_nonneg (α := ℝ) p
  have hd : 0 < ((p : ℝ) + 1) * (1 - r) + r := by nlinarith
  rw [le_div_iff₀ hd]
  nlinarith

/-- `α_p·ρ_p = 1/(1 − r)`. -/
theorem alp_mul_rho (p : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    alp p r * rho p r = 1 + r / (1 - r) := by
  unfold alp rho
  have hp := Nat.cast_nonneg (α := ℝ) p
  have hd : 0 < ((p : ℝ) + 1) * (1 - r) + r := by nlinarith
  have h1 : (0 : ℝ) < 1 - r := by linarith
  field_simp
  ring

/-- **The split**: `∏_{p ≤ N} L_p ≤ (1 + r₂/(1 − r₂))·∏_{3 ≤ p ≤ N} α_p·∏_{p | d} ρ_p`. -/
theorem ksum_split (d N : ℕ) (hd : Nat.Coprime d 2) (rr : ℕ → ℝ) (hr0 : ∀ p, 0 ≤ rr p)
    (hr1 : ∀ p, rr p < 1) :
    ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 + 1 / cc (d * 2) p * (rr p / (1 - rr p))) ≤
      (1 + rr 2 / (1 - rr 2)) *
        (∏ p ∈ ((range (N + 1)).filter Nat.Prime).filter (· ≠ 2), alp p (rr p)) *
          ∏ p ∈ d.primeFactors, rho p (rr p) := by
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  have hb : ∀ p, 1 ≤ 1 + rr p / (1 - rr p) := fun p => by
    have := hr1 p
    have : 0 ≤ rr p / (1 - rr p) := div_nonneg (hr0 p) (by linarith)
    linarith
  have ha : ∀ p, 1 ≤ alp p (rr p) := fun p => by
    unfold alp
    have := hr1 p
    have : 0 ≤ rr p / (((p : ℝ) + 1) * (1 - rr p)) :=
      div_nonneg (hr0 p) (mul_nonneg (by positivity) (by linarith))
    linarith
  have hpt : ∀ p ∈ P, 1 + 1 / cc (d * 2) p * (rr p / (1 - rr p)) ≤
      (if p = 2 then 1 + rr 2 / (1 - rr 2) else alp p (rr p)) *
        (if p ∈ d.primeFactors then rho p (rr p) else 1) := by
    intro p hp
    have hpr := (Finset.mem_filter.mp hp).2
    have h1r : (0 : ℝ) < 1 - rr p := by linarith [hr1 p]
    by_cases h2 : p = 2
    · subst h2
      have hnd : (2 : ℕ) ∉ d.primeFactors := fun h =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hd.symm (Nat.dvd_of_mem_primeFactors h)
      rw [if_pos rfl, if_neg hnd, mul_one]
      unfold cc
      rw [if_pos (dvd_mul_left 2 d)]
      simp
    · rw [if_neg h2]
      by_cases hpd : p ∣ d
      · rw [if_pos (Nat.mem_primeFactors.mpr ⟨hpr, hpd, hd0⟩), alp_mul_rho p _ (hr0 p) (hr1 p)]
        unfold cc
        rw [if_pos (dvd_mul_of_dvd_left hpd 2)]
        simp
      · have hnd : p ∉ d.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
        have hn2 : ¬ p ∣ d * 2 := by
          intro h
          rcases (Nat.Prime.dvd_mul hpr).mp h with h' | h'
          · exact hpd h'
          · exact h2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp h')
        rw [if_neg hnd, mul_one]
        unfold cc alp
        rw [if_neg hn2]
        have hp0 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
        rw [div_mul_div_comm, one_mul]
  have hnn : ∀ p ∈ P, 0 ≤ 1 + 1 / cc (d * 2) p * (rr p / (1 - rr p)) := fun p _ => by
    have := cc_ge (d * 2) p
    have : 0 ≤ rr p / (1 - rr p) := div_nonneg (hr0 p) (by linarith [hr1 p])
    have : 0 ≤ 1 / cc (d * 2) p := by positivity
    nlinarith
  refine (Finset.prod_le_prod hnn hpt).trans ?_
  rw [Finset.prod_mul_distrib]
  have hI : ∏ p ∈ P, (if p ∈ d.primeFactors then rho p (rr p) else 1) ≤
      ∏ p ∈ d.primeFactors, rho p (rr p) := by
    rw [← Finset.prod_filter]
    refine Finset.prod_le_prod_of_subset_of_one_le (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p _ => le_trans zero_le_one (rho_ge_one p _ (hr0 p) (hr1 p)))
      fun p _ _ => rho_ge_one p _ (hr0 p) (hr1 p)
  have hB : ∏ p ∈ P, (if p = 2 then 1 + rr 2 / (1 - rr 2) else alp p (rr p)) ≤
      (1 + rr 2 / (1 - rr 2)) * ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) := by
    rw [← Finset.prod_filter_mul_prod_filter_not P (· = 2)]
    have e2 : ∏ p ∈ P.filter (· = 2), (if p = 2 then 1 + rr 2 / (1 - rr 2) else alp p (rr p)) =
        ∏ p ∈ P.filter (· = 2), (1 + rr 2 / (1 - rr 2)) :=
      Finset.prod_congr rfl fun p hp => by rw [if_pos (Finset.mem_filter.mp hp).2]
    have eo : ∏ p ∈ P.filter (fun p => ¬ p = 2),
        (if p = 2 then 1 + rr 2 / (1 - rr 2) else alp p (rr p)) =
        ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) :=
      Finset.prod_congr rfl fun p hp => by rw [if_neg (Finset.mem_filter.mp hp).2]
    rw [e2, eo]
    have hsub : P.filter (· = 2) ⊆ {2} := fun p hp => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hp).2
    have h2 : ∏ p ∈ P.filter (· = 2), (1 + rr 2 / (1 - rr 2)) ≤ 1 + rr 2 / (1 - rr 2) := by
      calc ∏ p ∈ P.filter (· = 2), (1 + rr 2 / (1 - rr 2))
          ≤ ∏ p ∈ ({2} : Finset ℕ), (1 + rr 2 / (1 - rr 2)) :=
            Finset.prod_le_prod_of_subset_of_one_le hsub
              (fun p _ => le_trans zero_le_one (hb 2)) fun p _ _ => hb 2
        _ = 1 + rr 2 / (1 - rr 2) := Finset.prod_singleton _ _
    exact mul_le_mul_of_nonneg_right h2 (Finset.prod_nonneg fun p _ =>
      le_trans zero_le_one (ha p))
  have hI0 : 0 ≤ ∏ p ∈ P, (if p ∈ d.primeFactors then rho p (rr p) else 1) :=
    Finset.prod_nonneg fun p _ => by
      split_ifs
      · exact le_trans zero_le_one (rho_ge_one p _ (hr0 p) (hr1 p))
      · exact zero_le_one
  have hB0 : 0 ≤ (1 + rr 2 / (1 - rr 2)) * ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) :=
    mul_nonneg (le_trans zero_le_one (hb 2)) (Finset.prod_nonneg fun p _ =>
      le_trans zero_le_one (ha p))
  calc (∏ p ∈ P, (if p = 2 then 1 + rr 2 / (1 - rr 2) else alp p (rr p))) *
        ∏ p ∈ P, (if p ∈ d.primeFactors then rho p (rr p) else 1)
      ≤ ((1 + rr 2 / (1 - rr 2)) * ∏ p ∈ P.filter (· ≠ 2), alp p (rr p)) *
          ∏ p ∈ d.primeFactors, rho p (rr p) := mul_le_mul hB hI hI0 hB0

/-! ## (3) Numerics -/

/-- The 24 odd primes below `101`. -/
def smallP : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

theorem mem_smallP (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h : p < 101) : p ∈ smallP := by
  interval_cases p <;> first | exact absurd rfl h2 | decide | (exfalso; norm_num at hp)

/-- `⌊1000√p⌋/1000`. -/
noncomputable def sL (p : ℕ) : ℝ := (Nat.sqrt (p * 1000000) : ℝ) / 1000

/-- `⌊1000·p^{1/4}⌋/1000`. -/
noncomputable def tL (p : ℕ) : ℝ := (Nat.sqrt (Nat.sqrt (p * 1000000000000)) : ℝ) / 1000

theorem sL_le (p : ℕ) : sL p ≤ Real.sqrt p := by
  unfold sL
  rw [div_le_iff₀ (by norm_num), show (1000 : ℝ) = Real.sqrt 1000000 by
    rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    ← Real.sqrt_mul (Nat.cast_nonneg p)]
  apply Real.le_sqrt_of_sq_le
  have h := Nat.sqrt_le' (p * 1000000)
  have h' : ((Nat.sqrt (p * 1000000) : ℕ) : ℝ) ^ 2 ≤ ((p * 1000000 : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  exact h'

theorem tL_le (p : ℕ) : tL p ≤ Real.sqrt (Real.sqrt p) := by
  unfold tL
  set m := Nat.sqrt (Nat.sqrt (p * 1000000000000))
  have h1 : m ^ 2 ≤ Nat.sqrt (p * 1000000000000) := Nat.sqrt_le' _
  have h2 : (Nat.sqrt (p * 1000000000000)) ^ 2 ≤ p * 1000000000000 := Nat.sqrt_le' _
  have hm4 : ((m : ℝ) / 1000) ^ 4 ≤ p := by
    have h3 : (m : ℝ) ^ 4 ≤ (p : ℝ) * 1000000000000 := by
      have : m ^ 4 ≤ p * 1000000000000 := by
        calc m ^ 4 = (m ^ 2) ^ 2 := by ring
          _ ≤ (Nat.sqrt (p * 1000000000000)) ^ 2 := Nat.pow_le_pow_left h1 2
          _ ≤ p * 1000000000000 := h2
      exact_mod_cast this
    rw [div_pow]
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) / 1000 := by positivity
  apply Real.le_sqrt_of_sq_le
  apply Real.le_sqrt_of_sq_le
  have e : (((m : ℝ) / 1000) ^ 2) ^ 2 = ((m : ℝ) / 1000) ^ 4 := by ring
  rw [e]
  exact hm4

/-- `x ↦ x/((p+1)(1 − x))` is monotone on `[0, 1)`. -/
theorem frac_mono (p : ℕ) (x y : ℝ) (hxy : x ≤ y) (hy : y < 1) :
    x / (((p : ℝ) + 1) * (1 - x)) ≤ y / (((p : ℝ) + 1) * (1 - y)) := by
  have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left hxy hp.le]

theorem sqrt_two_le : Real.sqrt 2 ≤ 1.41422 := by
  rw [show (1.41422 : ℝ) = Real.sqrt (1.41422 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem sqrt_99_ge : 9.949 ≤ Real.sqrt 99 :=
  Real.le_sqrt_of_sq_le (by norm_num)

/-! ## (4) `KSumH` -/

theorem sqrt_w_mul (m n : ℕ) :
    Real.sqrt ((m * n : ℕ) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) := by
  push_cast
  exact Real.sqrt_mul (Nat.cast_nonneg m) _

theorem sqrt_lt_self (p : ℕ) (hp : p.Prime) : Real.sqrt (p : ℝ) < p := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact Real.sqrt_lt' (by linarith) |>.mpr (by nlinarith)

theorem rH_eq (p : ℕ) (hp : 1 ≤ p) : Real.sqrt (p : ℝ) / p = 1 / Real.sqrt p := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_eq_div_iff h0.ne' (Real.sqrt_pos.2 h0).ne', one_mul, Real.mul_self_sqrt h0.le]

theorem rH_lt (p : ℕ) (hp : 2 ≤ p) : 1 / Real.sqrt (p : ℝ) < 1 := by
  have h : (1 : ℝ) < Real.sqrt p := by
    rw [Real.lt_sqrt (by norm_num)]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  rw [div_lt_one (by linarith)]
  exact h

/-- **`M2Y.KSumH`, PROVED.** -/
theorem kSumH : M2Y.KSumH := by
  intro d N hd
  set w : ℕ → ℝ := fun n => Real.sqrt (n : ℝ) with hw
  set rr : ℕ → ℝ := fun p => if 2 ≤ p then 1 / Real.sqrt (p : ℝ) else 0 with hrr
  have hr0 : ∀ p, 0 ≤ rr p := fun p => by simp only [hrr]; split_ifs <;> positivity
  have hr1 : ∀ p, rr p < 1 := fun p => by
    simp only [hrr]
    split_ifs with h
    · exact rH_lt p h
    · norm_num
  have h1 := ksum_gen (d * 2) N w (fun n => Real.sqrt_nonneg _) (by simp [hw])
    (fun m n => sqrt_w_mul m n) (fun p hp => sqrt_lt_self p hp)
  have hrw : ∀ p ∈ (range (N + 1)).filter Nat.Prime, w p / p = rr p := fun p hp => by
    have hpr := (Finset.mem_filter.mp hp).2
    simp only [hw, hrr, if_pos hpr.two_le]
    exact rH_eq p hpr.one_lt.le
  rw [Finset.prod_congr rfl fun p hp => by rw [hrw p hp]] at h1
  have h2 := ksum_split d N hd rr hr0 hr1
  have hrho : ∏ p ∈ d.primeFactors, rho p (rr p) = ∏ p ∈ d.primeFactors, M2Y.rhoH p :=
    Finset.prod_congr rfl fun p hp => by
      simp only [hrr, if_pos (Nat.prime_of_mem_primeFactors hp).two_le, rho, M2Y.rhoH]
  rw [hrho] at h2
  -- the odd product
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hodd : ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) ≤ 2.157 := by
    have hT : (10 / 9 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) ≤ 0.1117 := by
      have := sqrt_99_ge
      norm_num
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hpp := M2YE.prod_primes_le P (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p => rr p / (((p : ℝ) + 1) * (1 - rr p)))
      (fun p => (1 / sL p) / (((p : ℝ) + 1) * (1 - 1 / sL p))) smallP 101 (by norm_num)
      (by norm_num) (10 / 9)
      (fun p _ => div_nonneg (hr0 p) (mul_nonneg (by positivity) (by linarith [hr1 p])))
      (fun p hp h2 h => mem_smallP p (Finset.mem_filter.mp hp).2 h2 h)
      (fun p hp => by
        simp only [smallP, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · simp only [sL]
          norm_num)
      (fun p hp h2 h => by
        have hpr := (Finset.mem_filter.mp hp).2
        have hs := sL_le p
        have hs1 : 1 < sL p := by
          have hm := mem_smallP p hpr h2 h
          simp only [smallP, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · simp only [sL]
            norm_num
        simp only [hrr, if_pos hpr.two_le]
        refine frac_mono p _ _ ?_ ?_
        · exact one_div_le_one_div_of_le (by linarith) hs
        · rw [div_lt_one (by linarith)]
          exact hs1)
      (fun p hp hM => by
        have hpr := (Finset.mem_filter.mp hp).2
        have hp0 : (101 : ℝ) ≤ p := by exact_mod_cast hM
        have hsq : 10 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
        simp only [hrr, if_pos hpr.two_le]
        have hs0 : 0 < Real.sqrt (p : ℝ) := by linarith
        rw [div_div, div_le_div_iff₀ (by
          have : 1 / Real.sqrt (p : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hsq
          have : 0 < 1 - 1 / Real.sqrt (p : ℝ) := by linarith
          positivity) (by positivity)]
        field_simp
        nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) p)])
      (by norm_num) (by linarith)
    have hsmall : ∏ p ∈ smallP, (1 + (1 / sL p) / (((p : ℝ) + 1) * (1 - 1 / sL p))) ≤
        1.9154 := by
      simp only [smallP, sL]
      norm_num [Finset.prod_insert, Finset.prod_singleton]
    have hfil : ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) =
        ∏ p ∈ P.filter (· ≠ 2), (1 + rr p / (((p : ℝ) + 1) * (1 - rr p))) := rfl
    rw [hfil]
    refine hpp.trans ?_
    have hT0 : 0 ≤ (10 / 9 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) := by positivity
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb2 : 1 + rr 2 / (1 - rr 2) ≤ 3.41422 := by
    simp only [hrr, if_pos (le_refl 2)]
    have hs := sqrt_two_le
    have hs1 : (1.4142 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have e : 1 + 1 / Real.sqrt ((2 : ℕ) : ℝ) / (1 - 1 / Real.sqrt ((2 : ℕ) : ℝ)) =
        2 + Real.sqrt 2 := by
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      push_cast
      have : Real.sqrt 2 - 1 ≠ 0 := by linarith
      field_simp
      nlinarith
    rw [e]
    linarith
  have hrho0 : 0 ≤ ∏ p ∈ d.primeFactors, M2Y.rhoH p := Finset.prod_nonneg fun p hp => by
    have := rho_ge_one p (rr p) (hr0 p) (hr1 p)
    simp only [hrr, if_pos (Nat.prime_of_mem_primeFactors hp).two_le, rho] at this
    unfold M2Y.rhoH
    linarith
  have hodd0 : 0 ≤ ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) := Finset.prod_nonneg fun p _ => by
    unfold alp
    have := hr1 p
    have : 0 ≤ rr p / (((p : ℝ) + 1) * (1 - rr p)) :=
      div_nonneg (hr0 p) (mul_nonneg (by positivity) (by linarith))
    linarith
  calc ∑ a ∈ Icc 1 N, M2Y.aK (d * 2) a * Real.sqrt a
      ≤ (1 + rr 2 / (1 - rr 2)) * (∏ p ∈ P.filter (· ≠ 2), alp p (rr p)) *
          ∏ p ∈ d.primeFactors, M2Y.rhoH p := h1.trans h2
    _ ≤ (3.41422 * 2.157) * ∏ p ∈ d.primeFactors, M2Y.rhoH p := by
        apply mul_le_mul_of_nonneg_right _ hrho0
        exact mul_le_mul hb2 hodd hodd0 (by norm_num)
    _ ≤ 8 * ∏ p ∈ d.primeFactors, M2Y.rhoH p :=
        mul_le_mul_of_nonneg_right (by norm_num) hrho0

/-! ## (5) `KSumQ` -/

theorem root_w_mul (m n : ℕ) :
    Real.sqrt (Real.sqrt ((m * n : ℕ) : ℝ)) =
      Real.sqrt (Real.sqrt (m : ℝ)) * Real.sqrt (Real.sqrt (n : ℝ)) := by
  rw [sqrt_w_mul, Real.sqrt_mul (Real.sqrt_nonneg _)]

theorem root_lt_self (p : ℕ) (hp : p.Prime) : Real.sqrt (Real.sqrt (p : ℝ)) < p := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2 := sqrt_lt_self p hp
  have h3 : Real.sqrt (Real.sqrt (p : ℝ)) ≤ Real.sqrt (p : ℝ) := by
    rw [Real.sqrt_le_left (Real.sqrt_nonneg _)]
    have h4 : (1 : ℝ) ≤ Real.sqrt p := Real.one_le_sqrt.mpr h1.le
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)]
  linarith

theorem rQ_eq (p : ℕ) (hp : 1 ≤ p) : Real.sqrt (Real.sqrt (p : ℝ)) / p = M2Y.qq p := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs := Real.sqrt_pos.2 h0
  have ht := Real.sqrt_pos.2 hs
  unfold M2Y.qq
  have e1 : Real.sqrt (Real.sqrt (p : ℝ)) * Real.sqrt (Real.sqrt (p : ℝ)) = Real.sqrt p :=
    Real.mul_self_sqrt hs.le
  have e2 : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p := Real.mul_self_sqrt h0.le
  rw [div_eq_div_iff h0.ne' (by positivity), one_mul]
  nlinarith

theorem qq_lt (p : ℕ) (hp : 2 ≤ p) : M2Y.qq p < 1 := by
  unfold M2Y.qq
  have h1 : (1 : ℝ) < Real.sqrt p := by
    rw [Real.lt_sqrt (by norm_num)]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h2 : (1 : ℝ) < Real.sqrt (Real.sqrt p) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **`M2Y.KSumQ`, PROVED.** -/
theorem kSumQ : M2Y.KSumQ := by
  intro d N hd
  set w : ℕ → ℝ := fun n => Real.sqrt (Real.sqrt (n : ℝ)) with hw
  set rr : ℕ → ℝ := fun p => if 2 ≤ p then M2Y.qq p else 0 with hrr
  have hr0 : ∀ p, 0 ≤ rr p := fun p => by
    simp only [hrr]
    split_ifs
    · unfold M2Y.qq
      positivity
    · exact le_rfl
  have hr1 : ∀ p, rr p < 1 := fun p => by
    simp only [hrr]
    split_ifs with h
    · exact qq_lt p h
    · norm_num
  have h1 := ksum_gen (d * 2) N w (fun n => Real.sqrt_nonneg _) (by simp [hw])
    (fun m n => root_w_mul m n) (fun p hp => root_lt_self p hp)
  have hrw : ∀ p ∈ (range (N + 1)).filter Nat.Prime, w p / p = rr p := fun p hp => by
    have hpr := (Finset.mem_filter.mp hp).2
    simp only [hw, hrr, if_pos hpr.two_le]
    exact rQ_eq p hpr.one_lt.le
  rw [Finset.prod_congr rfl fun p hp => by rw [hrw p hp]] at h1
  have h2 := ksum_split d N hd rr hr0 hr1
  have hrho : ∏ p ∈ d.primeFactors, rho p (rr p) = ∏ p ∈ d.primeFactors, M2Y.rhoQ p :=
    Finset.prod_congr rfl fun p hp => by
      simp only [hrr, if_pos (Nat.prime_of_mem_primeFactors hp).two_le, rho, M2Y.rhoQ]
  rw [hrho] at h2
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hqb : ∀ p, 0 < sL p * tL p → M2Y.qq p ≤ 1 / (sL p * tL p) := fun p h => by
    unfold M2Y.qq
    have ht0 : 0 ≤ tL p := by unfold tL; positivity
    exact one_div_le_one_div_of_le h (mul_le_mul (sL_le p) (tL_le p) ht0 (Real.sqrt_nonneg _))
  have hodd : ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) ≤ 1.469 := by
    have hT : (0.35 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) ≤ 0.03518 := by
      have := sqrt_99_ge
      norm_num
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hpp := M2YE.prod_primes_le P (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p => rr p / (((p : ℝ) + 1) * (1 - rr p)))
      (fun p => (1 / (sL p * tL p)) / (((p : ℝ) + 1) * (1 - 1 / (sL p * tL p)))) smallP 101
      (by norm_num) (by norm_num) 0.35
      (fun p _ => div_nonneg (hr0 p) (mul_nonneg (by positivity) (by linarith [hr1 p])))
      (fun p hp h2 h => mem_smallP p (Finset.mem_filter.mp hp).2 h2 h)
      (fun p hp => by
        simp only [smallP, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · simp only [sL, tL]
          norm_num)
      (fun p hp h2 h => by
        have hpr := (Finset.mem_filter.mp hp).2
        have hs1 : 1 < sL p * tL p := by
          have hm := mem_smallP p hpr h2 h
          simp only [smallP, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · simp only [sL, tL]
            norm_num
        simp only [hrr, if_pos hpr.two_le]
        refine frac_mono p _ _ (hqb p (by linarith)) ?_
        rw [div_lt_one (by linarith)]
        exact hs1)
      (fun p hp hM => by
        have hpr := (Finset.mem_filter.mp hp).2
        have hp0 : (101 : ℝ) ≤ p := by exact_mod_cast hM
        have hsq : 10 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
        have hrt : 3 ≤ Real.sqrt (Real.sqrt (p : ℝ)) := Real.le_sqrt_of_sq_le (by linarith)
        simp only [hrr, if_pos hpr.two_le]
        unfold M2Y.qq
        set a := Real.sqrt (p : ℝ) with ha
        set b := Real.sqrt (Real.sqrt (p : ℝ)) with hb
        have hq : 1 / (a * b) ≤ 1 / 30 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
        have hq0 : 0 < 1 / (a * b) := by positivity
        have haa : a * a = p := Real.mul_self_sqrt (Nat.cast_nonneg _)
        rw [div_div, div_le_div_iff₀ (by
          have : 0 < 1 - 1 / (a * b) := by linarith
          positivity) (by positivity)]
        have e : a * b * (((p : ℝ) + 1) * (1 - 1 / (a * b))) = ((p : ℝ) + 1) * (a * b - 1) := by
          have : a * b ≠ 0 := by positivity
          field_simp
        rw [e]
        have h3 : 2.9 * a ≤ a * b - 1 := by nlinarith
        have h4 : (p : ℝ) * (2.9 * a) ≤ ((p : ℝ) + 1) * (a * b - 1) :=
          mul_le_mul (by linarith) h3 (by positivity) (by positivity)
        nlinarith)
      (by norm_num) (by linarith)
    have hsmall : ∏ p ∈ smallP,
        (1 + (1 / (sL p * tL p)) / (((p : ℝ) + 1) * (1 - 1 / (sL p * tL p)))) ≤ 1.4172 := by
      simp only [smallP, sL, tL]
      norm_num [Finset.prod_insert, Finset.prod_singleton]
    have hfil : ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) =
        ∏ p ∈ P.filter (· ≠ 2), (1 + rr p / (((p : ℝ) + 1) * (1 - rr p))) := rfl
    rw [hfil]
    refine hpp.trans ?_
    have hT0 : 0 ≤ (0.35 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) := by positivity
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb2 : 1 + rr 2 / (1 - rr 2) ≤ 2.4669 := by
    simp only [hrr, if_pos (le_refl 2)]
    have hs1 : (1.4142 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have ht1 : (1.1892 : ℝ) ≤ Real.sqrt (Real.sqrt 2) := Real.le_sqrt_of_sq_le (by linarith)
    have hq : M2Y.qq 2 ≤ 0.59462 := by
      unfold M2Y.qq
      push_cast
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hq0 : 0 ≤ M2Y.qq 2 := by unfold M2Y.qq; positivity
    have h1q : 0 < 1 - M2Y.qq 2 := by linarith
    have : M2Y.qq 2 / (1 - M2Y.qq 2) ≤ 1.4669 := by
      rw [div_le_iff₀ h1q]
      nlinarith
    linarith
  have hrho0 : 0 ≤ ∏ p ∈ d.primeFactors, M2Y.rhoQ p := Finset.prod_nonneg fun p hp =>
    (M2Y.rhoQ_pos p (Nat.prime_of_mem_primeFactors hp).one_lt.le).le
  have hodd0 : 0 ≤ ∏ p ∈ P.filter (· ≠ 2), alp p (rr p) := Finset.prod_nonneg fun p _ => by
    unfold alp
    have := hr1 p
    have : 0 ≤ rr p / (((p : ℝ) + 1) * (1 - rr p)) :=
      div_nonneg (hr0 p) (mul_nonneg (by positivity) (by linarith))
    linarith
  calc ∑ a ∈ Icc 1 N, M2Y.aK (d * 2) a * Real.sqrt (Real.sqrt a)
      ≤ (1 + rr 2 / (1 - rr 2)) * (∏ p ∈ P.filter (· ≠ 2), alp p (rr p)) *
          ∏ p ∈ d.primeFactors, M2Y.rhoQ p := h1.trans h2
    _ ≤ (2.4669 * 1.469) * ∏ p ∈ d.primeFactors, M2Y.rhoQ p := by
        apply mul_le_mul_of_nonneg_right _ hrho0
        exact mul_le_mul hb2 hodd hodd0 (by norm_num)
    _ ≤ 4 * ∏ p ∈ d.primeFactors, M2Y.rhoQ p :=
        mul_le_mul_of_nonneg_right (by norm_num) hrho0

end Principia.Common.TernaryGoldbach.M2YK
