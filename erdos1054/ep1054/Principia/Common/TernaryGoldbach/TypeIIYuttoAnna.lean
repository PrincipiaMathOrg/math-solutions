/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIYuttoSpine

set_option autoImplicit false

/-!
# `M2Y.Anna2` PROVED — Helfgott's `eq:anna` for `v = 2`

`g₂(x) = ∑_{d ≤ x odd} μ(d)/σ(d)²·(∑_{u ≤ x/d, (u, 2d) = 1} μ(u)/σ(u))²` (`minarcs.tex`
2895-2920): write `1_{(r₁,r₂)=1} = ∑_{d | (r₁,r₂)} μ(d)`, swap, put `rᵢ = d·uᵢ`; for squarefree
`d` the term `μ(d)·T(du₁, du₂)` is `μ(d)/σ(d)²·g(u₁)g(u₂)` when `(uᵢ, 2d) = 1` and `d` odd, and
`0` otherwise (`du` is not squarefree when `(u, d) > 1`; `d²u₁u₂` is even when `2 | du₁u₂`).

```
 coprime_ind   1_{(a,b)=1} = ∑_{d | (a,b)} μ(d)
 sum_mult      ∑_{r ≤ N, d | r} h(r) = ∑_{u ≤ N/d} h(du)
 term_eq       μ(d)·T'(du₁, du₂) = 1_{d odd}·μ(d)/σ(d)²·g(u₁)g(u₂)
 anna2 : M2Y.Anna2                                                               PROVED
```
-/

namespace Principia.Common.TernaryGoldbach.M2YA

open Finset ArithmeticFunction

/-- `T'(r₁, r₂) = 1_{(r₁r₂, 2) = 1}·μ(r₁)μ(r₂)/(σ(r₁)σ(r₂))`. -/
noncomputable def tT (r1 r2 : ℕ) : ℝ :=
  if Nat.Coprime (r1 * r2) 2 then
    M2Y.mu r1 * M2Y.mu r2 / (M2Y.sg r1 * M2Y.sg r2) else 0

/-- `g_d(u) = 1_{(u, 2d) = 1}·μ(u)/σ(u)`. -/
noncomputable def gg (d u : ℕ) : ℝ :=
  if Nat.Coprime u (d * 2) then M2Y.mu u / M2Y.sg u else 0

theorem coprime_ind (a b : ℕ) :
    (if Nat.Coprime a b then (1 : ℝ) else 0) = ∑ d ∈ (Nat.gcd a b).divisors, M2Y.mu d := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f (Nat.gcd a b)) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  unfold M2Y.mu
  rw [← Int.cast_sum, h]
  unfold Nat.Coprime
  split_ifs <;> simp

theorem divisors_gcd_eq (a b N : ℕ) (ha : a ∈ Icc 1 N) (F : ℕ → ℝ) :
    ∑ d ∈ (Nat.gcd a b).divisors, F d =
      ∑ d ∈ Icc 1 N, if d ∣ a ∧ d ∣ b then F d else 0 := by
  rw [← Finset.sum_filter]
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have hg : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_left b (by omega)).ne'
  congr 1
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    have := Nat.le_of_dvd (by omega) h1
    have := Nat.pos_of_dvd_of_pos h1 (by omega)
    exact ⟨⟨by omega, by omega⟩, h1, h2⟩
  · rintro ⟨_, h1, h2⟩
    exact ⟨⟨h1, h2⟩, hg⟩

theorem sum_mult (d N : ℕ) (hd : 0 < d) (h : ℕ → ℝ) :
    ∑ r ∈ Icc 1 N, (if d ∣ r then h r else 0) = ∑ u ∈ Icc 1 (N / d), h (d * u) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun u => d * u) (fun r => r / d) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d u⟩
    calc d * u ≤ d * (N / d) := Nat.mul_le_mul_left d hu.2
      _ ≤ N := Nat.mul_div_le N d
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    simp only [Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hr
    refine ⟨?_, Nat.div_le_div_right h2⟩
    obtain ⟨c, rfl⟩ := h3
    rw [Nat.mul_div_cancel_left c hd]
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp at h1
    · exact hc
  · intro u _
    exact Nat.mul_div_cancel_left u hd
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact Nat.mul_div_cancel' hr.2
  · intro u _
    rfl

theorem mu_sq_of_sqfree (d : ℕ) (h : Squarefree d) : M2Y.mu d ^ 2 = 1 := by
  unfold M2Y.mu
  rcases moebius_ne_zero_iff_eq_or.mp (moebius_ne_zero_iff_squarefree.mpr h) with h1 | h1 <;>
    · rw [h1]
      norm_num

theorem mu_mul' (m n : ℕ) (h : Nat.Coprime m n) : M2Y.mu (m * n) = M2Y.mu m * M2Y.mu n := by
  unfold M2Y.mu
  rw [isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast
  ring

theorem sg_mul' (m n : ℕ) (h : Nat.Coprime m n) : M2Y.sg (m * n) = M2Y.sg m * M2Y.sg n := by
  unfold M2Y.sg
  rw [isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  ring

/-- If `(u, 2d) > 1` then `T'(du, ·) = 0` (for squarefree `d`). -/
theorem tT_zero_left (d u v : ℕ) (hu : ¬ Nat.Coprime u (d * 2)) : tT (d * u) (d * v) = 0 := by
  unfold tT
  rcases not_and_or.mp (fun h => hu (Nat.Coprime.mul_right h.1 h.2)) with h | h
  · have hns : ¬ Squarefree (d * u) := by
      rw [Nat.squarefree_mul_iff]
      exact fun h' => h h'.1.symm
    unfold M2Y.mu
    rw [moebius_eq_zero_of_not_squarefree hns]
    simp
  · rw [if_neg]
    intro h'
    apply h
    exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left d rfl)
      (Nat.Coprime.coprime_dvd_left (Dvd.intro (d * v) rfl) h')

theorem tT_comm (a b : ℕ) : tT a b = tT b a := by
  unfold tT
  rw [mul_comm a b, mul_comm (M2Y.mu a), mul_comm (M2Y.sg a)]

theorem sg_pos' (n : ℕ) (hn : 1 ≤ n) : 0 < M2Y.sg n := M2Y.sg_pos n hn

/-- **The pointwise identity.** -/
theorem term_eq (d u1 u2 : ℕ) (hd : 1 ≤ d) (hu1 : 1 ≤ u1) (hu2 : 1 ≤ u2) :
    M2Y.mu d * tT (d * u1) (d * u2) =
      if Nat.Coprime d 2 then M2Y.mu d / M2Y.sg d ^ 2 * (gg d u1 * gg d u2) else 0 := by
  by_cases hs : Squarefree d
  swap
  · have h0 : M2Y.mu d = 0 := by
      unfold M2Y.mu
      rw [moebius_eq_zero_of_not_squarefree hs]
      simp
    rw [h0]
    simp
  by_cases hA : Nat.Coprime u1 (d * 2)
  swap
  · rw [tT_zero_left d u1 u2 hA]
    unfold gg
    rw [if_neg hA]
    simp
  by_cases hB : Nat.Coprime u2 (d * 2)
  swap
  · rw [tT_comm, tT_zero_left d u2 u1 hB]
    unfold gg
    rw [if_neg hB]
    simp
  have hA1 : Nat.Coprime u1 d := Nat.Coprime.coprime_mul_right_right hA
  have hB1 : Nat.Coprime u2 d := Nat.Coprime.coprime_mul_right_right hB
  have hA2 : Nat.Coprime u1 2 := Nat.Coprime.coprime_mul_left_right hA
  have hB2 : Nat.Coprime u2 2 := Nat.Coprime.coprime_mul_left_right hB
  unfold gg tT
  rw [if_pos hA, if_pos hB]
  by_cases hd2 : Nat.Coprime d 2
  · have hc : Nat.Coprime (d * u1 * (d * u2)) 2 :=
      Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨hd2, hA2⟩,
        Nat.coprime_mul_iff_left.mpr ⟨hd2, hB2⟩⟩
    rw [if_pos hc, if_pos hd2, mu_mul' d u1 hA1.symm, mu_mul' d u2 hB1.symm,
      sg_mul' d u1 hA1.symm, sg_mul' d u2 hB1.symm]
    have hm := mu_sq_of_sqfree d hs
    have h1 := sg_pos' d hd
    have h2 := sg_pos' u1 hu1
    have h3 := sg_pos' u2 hu2
    field_simp
    have e : M2Y.mu d ^ 3 = M2Y.mu d := by rw [pow_succ, hm, one_mul]
    rw [e]
  · have hc : ¬ Nat.Coprime (d * u1 * (d * u2)) 2 := fun h =>
      hd2 (Nat.Coprime.coprime_dvd_left (Dvd.intro (u1 * (d * u2)) (by ring)) h)
    rw [if_neg hc, if_neg hd2, mul_zero]

/-- **`M2Y.Anna2`, PROVED.** -/
theorem anna2 : M2Y.Anna2 := by
  intro x hx
  set N := ⌊x⌋₊ with hN
  have hL : HC.gYutto 2 x = ∑ r1 ∈ Icc 1 N, ∑ r2 ∈ Icc 1 N,
      ∑ d ∈ Icc 1 N, (if d ∣ r1 then (if d ∣ r2 then M2Y.mu d * tT r1 r2 else 0) else 0) := by
    unfold HC.gYutto
    refine Finset.sum_congr rfl fun r1 hr1 => Finset.sum_congr rfl fun r2 hr2 => ?_
    have e : (if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
        ((ArithmeticFunction.moebius r1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius r2 : ℤ) : ℝ) /
          ((ArithmeticFunction.sigma 1 r1 : ℝ) * (ArithmeticFunction.sigma 1 r2 : ℝ)) else 0) =
        (if Nat.Coprime r1 r2 then (1 : ℝ) else 0) * tT r1 r2 := by
      unfold tT M2Y.mu M2Y.sg
      by_cases h1 : Nat.Coprime r1 r2 <;> by_cases h2 : Nat.Coprime (r1 * r2) 2
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, one_mul]
      · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2, one_mul]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
    rw [e, coprime_ind, divisors_gcd_eq r1 r2 N hr1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h1 : d ∣ r1 <;> by_cases h2 : d ∣ r2 <;> simp [h1, h2]
  rw [hL, Finset.sum_congr rfl fun r1 _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have step : ∑ r1 ∈ Icc 1 N, ∑ r2 ∈ Icc 1 N,
      (if d ∣ r1 then (if d ∣ r2 then M2Y.mu d * tT r1 r2 else 0) else 0) =
      ∑ u1 ∈ Icc 1 (N / d), ∑ u2 ∈ Icc 1 (N / d), M2Y.mu d * tT (d * u1) (d * u2) := by
    calc ∑ r1 ∈ Icc 1 N, ∑ r2 ∈ Icc 1 N,
          (if d ∣ r1 then (if d ∣ r2 then M2Y.mu d * tT r1 r2 else 0) else 0)
        = ∑ r1 ∈ Icc 1 N, (if d ∣ r1 then
            ∑ r2 ∈ Icc 1 N, (if d ∣ r2 then M2Y.mu d * tT r1 r2 else 0) else 0) :=
          Finset.sum_congr rfl fun r1 _ => by split_ifs <;> simp
      _ = ∑ u1 ∈ Icc 1 (N / d), ∑ r2 ∈ Icc 1 N,
            (if d ∣ r2 then M2Y.mu d * tT (d * u1) r2 else 0) :=
          sum_mult d N hd1 (fun r1 =>
            ∑ r2 ∈ Icc 1 N, (if d ∣ r2 then M2Y.mu d * tT r1 r2 else 0))
      _ = ∑ u1 ∈ Icc 1 (N / d), ∑ u2 ∈ Icc 1 (N / d), M2Y.mu d * tT (d * u1) (d * u2) :=
          Finset.sum_congr rfl fun u1 _ =>
            sum_mult d N hd1 (fun r2 => M2Y.mu d * tT (d * u1) r2)
  rw [step, Finset.sum_congr rfl fun u1 hu1 => Finset.sum_congr rfl fun u2 hu2 =>
    term_eq d u1 u2 hd1 (Finset.mem_Icc.mp hu1).1 (Finset.mem_Icc.mp hu2).1]
  unfold M2Y.hY
  rw [Nat.floor_div_natCast, ← hN]
  split_ifs with h
  · change _ = M2Y.mu d / M2Y.sg d ^ 2 * (∑ r ∈ Icc 1 (N / d), gg d r) ^ 2
    have e2 : (∑ r ∈ Icc 1 (N / d), gg d r) ^ 2 =
        ∑ u1 ∈ Icc 1 (N / d), ∑ u2 ∈ Icc 1 (N / d), gg d u1 * gg d u2 := by
      rw [sq, Finset.sum_mul_sum]
    rw [e2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u1 _ => by rw [Finset.mul_sum]
  · simp

end Principia.Common.TernaryGoldbach.M2YA
