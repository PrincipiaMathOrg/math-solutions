/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PNT.Wiener
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# The prime number theorem, in arithmetic progressions and in `ψ`-form

Principia's bridge from the PNT+ port (`Principia.Common.PNT.Wiener`) to the forms consumers use.
Not part of PNT+; everything here is proved in this file from `WeakPNT_AP` / `WeakPNT` and pinned
Mathlib (`Chebyshev.psi_sub_theta_le`, `Chebyshev.psi_sub_theta_eq_sum_not_prime`).

Headlines:
* `tendsto_primeCountingAP_mul_log_div` — for `q ≥ 1` and `a` coprime to `q`,
  `#{p ≤ x : p prime, p ≡ a (mod q)} · log x / x → 1/φ(q)` as `x → ∞` (real `x`, primes counted in
  `Finset.Iic ⌊x⌋₊`, the class written `p % q = a % q`).
* `tendsto_psi_div_self` — `ψ(x)/x → 1` (Mathlib's `Chebyshev.psi`).

The transfer lemma `tendsto_card_filter_prime_mul_log_div` is Mathlib-only and general: for any
`P : ℕ → Prop`, `(∑_{n<N, P n} Λ n)/N → L > 0` implies `π_P(x) log x / x → L`. Proof: the lower
bound is `π_P(x) log x ≥ ψ_P(x) − (ψ(x) − θ(x))` and `ψ − θ ≤ 2√x log x`; the upper bound splits
the primes at `x^{1−ε}`, giving `π_P(x) log x ≤ (x^{1−ε} + 1) log x + ψ_P(x)/(1 − ε)`, and `ε` is
chosen from the target gap.
-/

namespace Principia.Common.PNT

open Filter Topology Finset
open ArithmeticFunction hiding log

/-- A range sum that vanishes at `0` is the same sum over `Ioc 0 n`. -/
lemma sum_range_succ_eq_sum_Ioc (g : ℕ → ℝ) (hg0 : g 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), g i = ∑ i ∈ Finset.Ioc 0 n, g i := by
  symm
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_Ioc] at hi
    rw [Finset.mem_range]
    omega
  · intro i hi hi'
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0]
      exact hg0
    · exact absurd (Finset.mem_Ioc.2 ⟨hpos, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)⟩) hi'

/-- The primes `≤ n` satisfying `P`, as `Iic` vs `Ioc 0`. -/
lemma filter_prime_and_Iic_eq_Ioc (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    (Finset.Iic n).filter (fun p => p.Prime ∧ P p) =
      (Finset.Ioc 0 n).filter (fun p => p.Prime ∧ P p) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h2.pos, h1⟩, h2, h3⟩
  · rintro ⟨⟨_, h1⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩

/-- Lower comparison: `ψ_P(x) ≤ π_P(x) log x + (ψ(x) − θ(x))` for `x ≥ 1`. -/
lemma sum_vonMangoldt_filter_le (P : ℕ → Prop) [DecidablePred P] {x : ℝ} (hx : 1 ≤ x) :
    ∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0) ≤
      (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) * Real.log x +
        (Chebyshev.psi x - Chebyshev.theta x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have key : ∀ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0) ≤
      (if i.Prime ∧ P i then Real.log x else 0) + (if ¬ i.Prime then Λ i else 0) := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
    have hix : (i : ℝ) ≤ x := (Nat.cast_le.2 hi.2).trans (Nat.floor_le hx0.le)
    by_cases hp : i.Prime
    · by_cases hP : P i
      · rw [if_pos hP, if_pos ⟨hp, hP⟩, if_neg (not_not.2 hp), add_zero,
          vonMangoldt_apply_prime hp]
        exact Real.log_le_log hi0 hix
      · rw [if_neg hP, if_neg (show ¬ (i.Prime ∧ P i) from fun h => hP h.2),
          if_neg (not_not.2 hp), add_zero]
    · rw [if_neg (show ¬ (i.Prime ∧ P i) from fun h => hp h.1), if_pos hp, zero_add]
      split_ifs
      · exact le_rfl
      · exact vonMangoldt_nonneg
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, filter_prime_and_Iic_eq_Ioc, Chebyshev.psi_sub_theta_eq_sum_not_prime]

/-- Upper comparison: for `0 < ε < 1` and `x > 1`,
`π_P(x) log x ≤ (x^{1-ε} + 1) log x + ψ_P(x)/(1 − ε)`. -/
lemma card_mul_log_le (P : ℕ → Prop) [DecidablePred P] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {x : ℝ} (hx : 1 < x) :
    (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) * Real.log x ≤
      (x ^ (1 - ε) + 1) * Real.log x +
        (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / (1 - ε) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have h1ε : 0 < 1 - ε := by linarith
  set A := (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ P p) with hA
  set y : ℝ := x ^ (1 - ε) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hlogy : Real.log y = (1 - ε) * Real.log x := Real.log_rpow hx0 _
  -- split `A` at `y`
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun p : ℕ => (p : ℝ) ≤ y)
  -- the small primes
  have hsmall : ((A.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ y + 1 := by
    have hsub : A.filter (fun p : ℕ => (p : ℝ) ≤ y) ⊆ Finset.Iic ⌊y⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_Iic]
      exact Nat.le_floor hp.2
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Iic] at hc
    have hc' : ((A.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ (⌊y⌋₊ : ℝ) + 1 := by
      exact_mod_cast hc
    linarith [Nat.floor_le hy0.le]
  -- the large primes
  have hlarge : ((A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * ((1 - ε) * Real.log x) ≤
      ∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0) := by
    have h1 : ((A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * ((1 - ε) * Real.log x) ≤
        ∑ p ∈ A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), Real.log p := by
      rw [← nsmul_eq_mul]
      apply Finset.card_nsmul_le_sum
      intro p hp
      rw [Finset.mem_filter, not_le] at hp
      rw [← hlogy]
      exact (Real.log_lt_log hy0 hp.2).le
    have h2 : ∑ p ∈ A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), Real.log p ≤ ∑ p ∈ A, Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      rw [hA, Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)
    have h3 : ∑ p ∈ A, Real.log p ≤ ∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0) := by
      rw [hA, filter_prime_and_Iic_eq_Ioc, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i _
      by_cases hp : i.Prime
      · by_cases hP : P i
        · rw [if_pos ⟨hp, hP⟩, if_pos hP, vonMangoldt_apply_prime hp]
        · rw [if_neg (show ¬ (i.Prime ∧ P i) from fun h => hP h.2), if_neg hP]
      · rw [if_neg (show ¬ (i.Prime ∧ P i) from fun h => hp h.1)]
        split_ifs
        · exact vonMangoldt_nonneg
        · exact le_rfl
    linarith
  have hlarge' : ((A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * Real.log x ≤
      (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / (1 - ε) := by
    rw [le_div_iff₀ h1ε]
    calc ((A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * Real.log x * (1 - ε)
        = ((A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * ((1 - ε) * Real.log x) := by ring
      _ ≤ _ := hlarge
  have hcard : (A.card : ℝ) = ((A.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) +
      ((A.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) := by
    exact_mod_cast hsplit.symm
  rw [hcard, add_mul]
  have hs' : ((A.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) * Real.log x ≤
      (y + 1) * Real.log x := mul_le_mul_of_nonneg_right hsmall hlog.le
  linarith

/-- A sum over `range N` that vanishes at `0` and is asymptotic to `L N` along the naturals is
asymptotic to `L x` along the reals, when summed over `Ioc 0 ⌊x⌋₊`. -/
lemma tendsto_sum_Ioc_floor_div (g : ℕ → ℝ) (hg0 : g 0 = 0) {L : ℝ}
    (hW : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, g i) / (N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, g i) / x) atTop (𝓝 L) := by
  have h1 : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  have h2 := hW.comp h1
  have h3 : Tendsto (fun x : ℝ => (((⌊x⌋₊ + 1 : ℕ) : ℝ)) / x) atTop (𝓝 1) := by
    have h := (tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    push_cast
    field_simp
  have h4 := h2.mul h3
  rw [mul_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hne : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  rw [sum_range_succ_eq_sum_Ioc g hg0 ⌊x⌋₊]
  field_simp

/-- `ψ(x)/x → 1` along the reals from `(∑_{n<N} Λ n)/N → 1` along the naturals. -/
lemma tendsto_psi_div_self_of
    (hW : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, Λ i) / (N : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  tendsto_sum_Ioc_floor_div (fun i => Λ i) (by simp) hW

/-- **From `ψ_P(x) ∼ L x` to `π_P(x) ∼ L x / log x`.** For any set `P` of naturals, if the
von Mangoldt mass of `P` below `N` is asymptotic to `L N` (`L > 0`), then the number of primes in
`P` up to `x` is asymptotic to `L x / log x`. -/
theorem tendsto_card_filter_prime_mul_log_div (P : ℕ → Prop) [DecidablePred P] {L : ℝ}
    (hL : 0 < L)
    (hW : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, (if P i then Λ i else 0)) / (N : ℝ))
      atTop (𝓝 L)) :
    Tendsto (fun x : ℝ =>
      (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) * Real.log x / x)
      atTop (𝓝 L) := by
  -- Step A: `ψ_P(x)/x → L` along the reals.
  have hS : Tendsto (fun x : ℝ => (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / x)
      atTop (𝓝 L) :=
    tendsto_sum_Ioc_floor_div (fun i => if P i then Λ i else 0) (by simp) hW
  -- Step B: `(ψ(x) − θ(x))/x → 0`.
  have hE : Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    have hlr : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hup : Tendsto (fun x : ℝ => 2 * (Real.log x / x ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
      simpa using hlr.const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_nonneg (sub_nonneg.2 (Chebyshev.theta_le_psi x)) hx.le
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
      have hsqpos : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
      have hxx : x = x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hx0]
        norm_num
      have hxs : x / x ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
        rw [div_eq_iff hsqpos.ne']
        exact hxx
      rw [div_le_iff₀ hx0]
      calc Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
            Chebyshev.psi_sub_theta_le hx
        _ = 2 * Real.log x * (x / x ^ (1 / 2 : ℝ)) := by
            rw [hxs, hsq]
            ring
        _ = 2 * (Real.log x / x ^ (1 / 2 : ℝ)) * x := by ring
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro a ha
    have hlow : Tendsto (fun x : ℝ =>
        (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / x -
          (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 L) := by
      simpa using hS.sub hE
    filter_upwards [(tendsto_order.1 hlow).1 a ha, eventually_ge_atTop 1] with x h1 h2
    have hx0 : (0 : ℝ) < x := by linarith
    have hb := sum_vonMangoldt_filter_le P h2
    refine lt_of_lt_of_le h1 ?_
    rw [← sub_div, div_le_div_iff_of_pos_right hx0]
    linarith
  · -- upper bound
    intro b hb
    have hb0 : 0 < b := hL.trans hb
    set ε : ℝ := (b - L) / (2 * b) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have hε1 : ε < 1 := by
      rw [hε, div_lt_one (by linarith)]
      linarith
    have h1ε : 0 < 1 - ε := by linarith
    have hlt : L / (1 - ε) < b := by
      rw [div_lt_iff₀ h1ε]
      have : b * (1 - ε) = (b + L) / 2 := by
        rw [hε]
        field_simp
        ring
      rw [this]
      linarith
    have hU : Tendsto (fun x : ℝ =>
        2 * (Real.log x / x ^ ε) +
          (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / x / (1 - ε))
        atTop (𝓝 (2 * 0 + L / (1 - ε))) :=
      (((isLittleO_log_rpow_atTop hε0).tendsto_div_nhds_zero).const_mul 2).add
        (hS.div_const (1 - ε))
    rw [mul_zero, zero_add] at hU
    filter_upwards [(tendsto_order.1 hU).2 b hlt, eventually_gt_atTop 1] with x h1 h2
    have hx0 : (0 : ℝ) < x := by linarith
    refine lt_of_le_of_lt ?_ h1
    have hc := card_mul_log_le P hε0 hε1 h2
    have hy1 : 1 ≤ x ^ (1 - ε) := Real.one_le_rpow h2.le h1ε.le
    have hlog : 0 < Real.log x := Real.log_pos h2
    have hxe : x ^ (1 - ε) = x / x ^ ε := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    have hxepos : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
    -- (x^{1-ε} + 1) log x ≤ 2 x^{1-ε} log x = 2 (log x / x^ε) x
    have hmain : (x ^ (1 - ε) + 1) * Real.log x ≤ 2 * (Real.log x / x ^ ε) * x := by
      calc (x ^ (1 - ε) + 1) * Real.log x ≤ (2 * x ^ (1 - ε)) * Real.log x :=
            mul_le_mul_of_nonneg_right (by linarith) hlog.le
        _ = 2 * (Real.log x / x ^ ε) * x := by
            rw [hxe]
            field_simp
    change (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) * Real.log x / x ≤ _
    rw [div_le_iff₀ hx0]
    have hsplit : (2 * (Real.log x / x ^ ε) +
        (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / x / (1 - ε)) * x =
        2 * (Real.log x / x ^ ε) * x +
          (∑ i ∈ Finset.Ioc 0 ⌊x⌋₊, (if P i then Λ i else 0)) / (1 - ε) := by
      field_simp
    rw [hsplit]
    linarith

/-! ## The prime number theorem, from the PNT+ port -/

/-- **Prime number theorem in arithmetic progressions, `π`-form.** For `q ≥ 1` and `a` coprime
to `q`, `#{p ≤ x : p prime, p ≡ a (mod q)} · log x / x → 1/φ(q)`. From PNT+'s `WeakPNT_AP`
(von Mangoldt form, applied to the reduced residue `a % q`) by
`tendsto_card_filter_prime_mul_log_div`. -/
theorem tendsto_primeCountingAP_mul_log_div {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    Tendsto (fun x : ℝ =>
      (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) *
        Real.log x / x)
      atTop (𝓝 (1 / (q.totient : ℝ))) := by
  have hr : a % q < q := Nat.mod_lt a (by omega)
  have hrc : (a % q).Coprime q := by
    have h1 : Nat.gcd (a % q) q = Nat.gcd q a := (Nat.gcd_rec q a).symm
    change Nat.gcd (a % q) q = 1
    rw [h1, Nat.gcd_comm]
    exact ha
  have hL : (0 : ℝ) < 1 / (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  exact tendsto_card_filter_prime_mul_log_div (fun p => p % q = a % q) hL (WeakPNT_AP hq hrc hr)

/-- **Prime number theorem**, `ψ(x)/x → 1`, from PNT+'s `WeakPNT`. -/
theorem tendsto_psi_div_self : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  tendsto_psi_div_self_of WeakPNT

end Principia.Common.PNT
