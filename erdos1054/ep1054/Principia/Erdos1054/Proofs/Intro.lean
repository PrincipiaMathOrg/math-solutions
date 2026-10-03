/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

/-!
# EP1054 §1–§2 small facts: the `Intro` package of the spine

Discharges eleven obligations of `Principia.Erdos1054.Spine` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, §1 Introduction/Notation and the §2 preamble).

Leaves (proved from the definitions and Mathlib alone):
* `leaf_Intro_f_sigma_le` — `σ(n) ∈ 𝓡` and `f(σ(n)) ≤ n` (line 105): `σ(n) = F_1(n)`.
* `leaf_Notation_Delta_density` — `Δ(y) = φ(y#)/y#` and it is the density of integers coprime to
  `y#` (lines 323–330): Euler's product for `φ` and complete residue periods mod `y#`.
* `leaf_Notation_sigmaPrefix_zero` — `σ₀ = σ` (line 346).
* `leaf_EmpiricalMeasures_isProbability` — `ν_X` is a probability measure for `X ≥ 1` (line 221):
  `1 ∈ 𝓡`, so `R(X) ≥ 1`.
* `leaf_Eq_Reflection` — `eq:reflection` (lines 372–377): `Principia.Erdos1054.reflection`.
* `leaf_Disp_FinalDivisor` — `F_e(d) ≥ d`, `F_e(d) ≤ X ⟹ ed ≤ eX` (lines 358–361).

Links (proved from exactly the dependencies the spine names):
* `link_Intro_LiminfZero` (lines 105–107) — from `Intro_f_sigma_le`; the unboundedness of
  `σ(n)/n` is proved here at `n = k!` via the harmonic series (`sig_factorial_ge`).
* `link_Intro_RcntFormula` (line 230) — from `Eq_ExactRepresentability`.
* `link_Intro_ErdosLittleO_fails` (line 108) — from `Thm_AlmostLogTail_limsup`.
* `link_Intro_ErdosAlmostAllLittleO_fails` (lines 108–109) — from
  `Thm_AlmostLogTail_posLowerDens` at `T = 1`.
* `link_Intro_LittleO_onlyOnDensityZero` (lines 79, 152–155) — from `Thm_SmallUpper_upperDens`,
  letting `δ → 0⁺`.
-/

namespace Principia.Erdos1054.Proofs.Intro

open Finset Filter
open scoped Topology ENNReal

/-- `σ(n) = F_1(n)`: every divisor of `1 · n` is `≤ n`. -/
theorem sig_eq_F_one (n : ℕ) : sig n = F 1 n := by
  show ArithmeticFunction.sigma 1 n = F 1 n
  rw [ArithmeticFunction.sigma_one_apply, F, one_mul, Finset.filter_true_of_mem]
  intro d hd
  exact Nat.divisor_le hd

/-- `1 ∈ 𝓡` (`1 = F_1(1)`). -/
theorem one_mem_R : (1 : ℕ) ∈ R := (mem_R_iff_exists_F 1).2 ⟨1, 1, le_rfl, le_rfl, by decide⟩

/-- `σ(k!) ≥ k! · ∑_{i < k} 1/(i+1)`: the divisors `k!/j`, `1 ≤ j ≤ k`, already give the harmonic
sum. -/
theorem sig_factorial_ge (k : ℕ) :
    (k.factorial : ℝ) * ∑ i ∈ Finset.range k, (1 / ((i : ℝ) + 1)) ≤ (sig k.factorial : ℝ) := by
  set m := k.factorial with hm
  have hmpos : 0 < m := Nat.factorial_pos k
  have hsig : (sig m : ℝ) = ∑ d ∈ m.divisors, (m : ℝ) / d := by
    show ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) = _
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors m (fun d => d), Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact Nat.cast_div (Nat.dvd_of_mem_divisors hd)
      (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')
  have himg : (Finset.range k).image (fun i : ℕ => i + 1) ⊆ m.divisors := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    rw [Finset.mem_range] at hi
    rw [Nat.mem_divisors]
    exact ⟨Nat.dvd_factorial (Nat.succ_pos i) hi, hmpos.ne'⟩
  have hsum : ∑ d ∈ (Finset.range k).image (fun i : ℕ => i + 1), (m : ℝ) / (d : ℝ)
      = (m : ℝ) * ∑ i ∈ Finset.range k, (1 / ((i : ℝ) + 1)) := by
    rw [Finset.sum_image (by intro a _ b _ h; exact Nat.add_right_cancel h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hsig, ← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun d _ _ => by positivity)

open Classical in
/-- Membership in a classical filter by a generic set (see the decidability note in `Density`):
stated for a generic `S`, so its instance is the one `hasDens_of_mem_iff_mod_mem` uses. -/
theorem mem_filter_classical {S : Set ℕ} {s : Finset ℕ} {n : ℕ} :
    n ∈ s.filter (· ∈ S) ↔ n ∈ s ∧ n ∈ S := Finset.mem_filter

/-- `R(X) ≥ 1` for `X ≥ 1`. -/
theorem one_le_Rcnt {X : ℝ} (hX : 1 ≤ X) : 1 ≤ Rcnt X := by
  have h1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  show 1 ≤ cnt R X
  unfold cnt
  exact Finset.card_pos.2 ⟨1, mem_cntFinset.2 ⟨⟨le_rfl, h1⟩, one_mem_R⟩⟩

end Principia.Erdos1054.Proofs.Intro

namespace Principia.Erdos1054.Proofs

open Finset Filter Intro
open scoped Topology ENNReal

/-- `eq:reflection` (EP1054.tex lines 372–377). -/
theorem leaf_Eq_Reflection : Principia.Erdos1054.Eq_Reflection :=
  fun e d he hd => reflection e d he hd

/-- The final-divisor display (EP1054.tex lines 358–361). -/
theorem leaf_Disp_FinalDivisor : Principia.Erdos1054.Disp_FinalDivisor := by
  intro e d he hd
  refine ⟨F_ge e d he hd, fun X hX => ?_⟩
  have h1 : (d : ℝ) ≤ F e d := by exact_mod_cast F_ge e d he hd
  exact mul_le_mul_of_nonneg_left (h1.trans hX) (Nat.cast_nonneg e)

/-- `σ(n) ∈ 𝓡` and `f(σ(n)) ≤ n` (EP1054.tex line 105). -/
theorem leaf_Intro_f_sigma_le : Principia.Erdos1054.Intro_f_sigma_le := by
  intro n hn
  have hF := sig_eq_F_one n
  refine ⟨(mem_R_iff_exists_F _).2 ⟨1, n, le_rfl, hn, hF⟩, ?_⟩
  have h := f_le_of_F 1 n (sig n) le_rfl hn hF
  rwa [one_mul] at h

/-- `σ₀ = σ` (EP1054.tex line 346). -/
theorem leaf_Notation_sigmaPrefix_zero : Principia.Erdos1054.Notation_sigmaPrefix_zero := by
  intro n hn
  have hcard : 0 < n.divisors.card := Finset.card_pos.2 (Nat.nonempty_divisors.2 (by omega))
  rw [sigmaPrefix, if_pos hcard, Nat.sub_zero, prefixSumDivisors,
    List.take_of_length_le (by rw [Finset.length_sort]),
    list_sum_eq_toFinset_sum (n.divisors.sort_nodup (· ≤ ·)), Finset.sort_toFinset]
  show _ = ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]

/-- `ν_X` is a probability measure for `X ≥ 1` (EP1054.tex lines 221–225). -/
theorem leaf_EmpiricalMeasures_isProbability :
    Principia.Erdos1054.EmpiricalMeasures_isProbability := by
  intro X hX
  constructor
  rw [nuX, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finsetSum_apply]
  simp only [MeasureTheory.measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  change (Rcnt X : ℝ≥0∞)⁻¹ * (Rcnt X : ℝ≥0∞) = 1
  have h1 := one_le_Rcnt hX
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : Rcnt X ≠ 0))
    (ENNReal.natCast_ne_top _)

/-- `Δ(y) = φ(y#)/y#` is the natural density of the integers coprime to `y#`
(EP1054.tex lines 323–330). -/
theorem leaf_Notation_Delta_density : Principia.Erdos1054.Notation_Delta_density := by
  intro y _hy
  set q := primorialR y with hq
  have hqpos : 0 < q := primorial_pos _
  have hPF : q.primeFactors = (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime :=
    Nat.primeFactors_prod (s := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime)
      (fun p hp => (Finset.mem_filter.1 hp).2)
  have hphi : ((q.totient : ℕ) : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at h
    exact h
  have hDelta : Delta y = (q.totient : ℝ) / q := by
    rw [hphi, hPF, mul_div_cancel_left₀ _ (by exact_mod_cast hqpos.ne')]
    unfold Delta
    simp only [one_div]
  refine ⟨hDelta, ?_⟩
  have hS : ∀ N, N ∈ {n : ℕ | Nat.Coprime n q} ↔ N % q ∈ {n : ℕ | Nat.Coprime n q} := by
    intro N
    show Nat.gcd N q = 1 ↔ Nat.gcd (N % q) q = 1
    rw [← Nat.gcd_rec q N, Nat.gcd_comm q N]
  have h := hasDens_of_mem_iff_mod_mem hqpos hS
  rw [hDelta]
  convert h using 3
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  rw [mem_filter_classical, Finset.mem_filter, Set.mem_setOf_eq, Nat.coprime_comm]

/-- `liminf_{N ∈ 𝓡} f(N)/N = 0` (EP1054.tex lines 105–107), from `f(σ(n)) ≤ n` and the
unboundedness of `σ(n)/n` (here at `n = k!`, where `σ(k!)/k! ≥ H_k`). -/
theorem link_Intro_LiminfZero : Principia.Erdos1054.Spine.Link_Intro_LiminfZero := by
  intro hfs ε hε N₀
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.1
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (1 / ε))
  set k := max k₁ N₀ with hk
  have hH : 1 / ε < ∑ i ∈ Finset.range k, (1 / ((i : ℝ) + 1)) := hk₁ k (le_max_left _ _)
  have hm1 : 1 ≤ k.factorial := Nat.factorial_pos k
  obtain ⟨hNR, hfN⟩ := hfs k.factorial hm1
  have h3 : k.factorial ≤ sig k.factorial := by
    rw [sig_eq_F_one]
    exact F_ge 1 _ le_rfl hm1
  refine ⟨sig k.factorial, ?_, hNR, ?_⟩
  · have h1 : N₀ ≤ k := le_max_right _ _
    have h2 : k ≤ k.factorial := Nat.self_le_factorial k
    omega
  · have hmR : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hNpos : (0 : ℝ) < sig k.factorial := by
      have : ((k.factorial : ℕ) : ℝ) ≤ (sig k.factorial : ℝ) := by exact_mod_cast h3
      linarith
    have hsig := sig_factorial_ge k
    have hεH : 1 < (∑ i ∈ Finset.range k, (1 / ((i : ℝ) + 1))) * ε := by
      rwa [div_lt_iff₀ hε] at hH
    rw [div_lt_iff₀ hNpos]
    calc (f (sig k.factorial) : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast hfN
      _ < (k.factorial : ℝ) * ((∑ i ∈ Finset.range k, (1 / ((i : ℝ) + 1))) * ε) :=
          lt_mul_of_one_lt_right hmR hεH
      _ = ((k.factorial : ℝ) * ∑ i ∈ Finset.range k, (1 / ((i : ℝ) + 1))) * ε := by ring
      _ ≤ (sig k.factorial : ℝ) * ε := mul_le_mul_of_nonneg_right hsig hε.le
      _ = ε * (sig k.factorial : ℝ) := by ring

/-- `R(X) = ⌊X⌋ − 2` for `X ≥ 5` (EP1054.tex line 230), from `𝓡 = ℕ ∖ {2, 5}`. -/
theorem link_Intro_RcntFormula : Principia.Erdos1054.Spine.Link_Intro_RcntFormula := by
  intro hR X hX
  have h5 : 5 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hm2 : 2 ∈ Finset.Icc 1 ⌊X⌋₊ := by
    rw [Finset.mem_Icc]
    omega
  have hm5 : 5 ∈ (Finset.Icc 1 ⌊X⌋₊).erase 2 := by
    rw [Finset.mem_erase, Finset.mem_Icc]
    omega
  show cnt R X = _
  rw [hR]
  calc cnt {N : ℕ | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5} X
      = (((Finset.Icc 1 ⌊X⌋₊).erase 2).erase 5).card := by
        unfold cnt
        congr 1
        ext N
        rw [mem_cntFinset, Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc, Set.mem_setOf_eq]
        omega
    _ = ⌊X⌋₊ - 2 := by
        rw [Finset.card_erase_of_mem hm5, Finset.card_erase_of_mem hm2, Nat.card_Icc]
        omega

/-- `f(N) = o(N)` fails (EP1054.tex line 108), from `limsup_{N ∈ 𝓡} f(N)/N = ∞`. -/
theorem link_Intro_ErdosLittleO_fails :
    Principia.Erdos1054.Spine.Link_Intro_ErdosLittleO_fails := by
  intro hlim hsmall
  obtain ⟨N₀, hN₀⟩ := hsmall 1 one_pos
  obtain ⟨N, hN, hNR, hB⟩ := hlim 1 N₀
  have hle := hN₀ N hN hNR
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      rw [Nat.cast_zero, div_zero] at hB
      linarith
    · exact_mod_cast h
  rw [lt_div_iff₀ hNpos] at hB
  linarith

/-- `f(N) = o(N)` fails along every set of density one (EP1054.tex lines 108–109, 155, 192), from
the positive lower density of `{N ∈ 𝓡 : f(N) > N}`. -/
theorem link_Intro_ErdosAlmostAllLittleO_fails :
    Principia.Erdos1054.Spine.Link_Intro_ErdosAlmostAllLittleO_fails := by
  rintro hpos ⟨S, hS1, hS⟩
  obtain ⟨N₀, hN₀⟩ := hS 1 one_pos
  have hsub : largeRatioSet 1 ⊆ Sᶜ ∪ {N : ℕ | N < N₀} := by
    intro N hN
    obtain ⟨hNR, hlt⟩ := hN
    by_contra hc
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not,
      not_lt] at hc
    have := hN₀ N hc.2 hc.1 hNR
    linarith
  have hz : DensZero (Sᶜ ∪ {N : ℕ | N < N₀}) := by
    refine densZero_union ?_ (densZero_of_finite (Set.finite_lt_nat N₀))
    have h := hS1.compl
    rw [sub_self] at h
    exact h
  have h0 : lowerDens (largeRatioSet 1) = 0 := HasDens.lowerDens_eq (densZero_subset hz hsub)
  have := hpos 1 one_pos
  linarith

/-- Along any set carrying `f(N) = o(N)`, the represented members have density zero
(EP1054.tex lines 79, 152–155), from the upper-density form of Theorem 1.1 with `δ → 0⁺`. -/
theorem link_Intro_LittleO_onlyOnDensityZero :
    Principia.Erdos1054.Spine.Link_Intro_LittleO_onlyOnDensityZero := by
  rintro ⟨c, hc, C, δ₀, hδ₀, hU⟩ S hS
  rw [densZero_iff_upperDens_eq_zero]
  refine le_antisymm ?_ (upperDens_nonneg _)
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      upperDens {N : ℕ | N ∈ S ∧ N ∈ R} ≤ C * Real.exp (-Real.exp ((1 / δ) ^ c)) := by
    intro δ hδ hδle
    obtain ⟨N₀, hN₀⟩ := hS δ hδ
    have hsub : {N : ℕ | N ∈ S ∧ N ∈ R} ⊆ smallRatioSet δ ∪ {N : ℕ | N < N₀} := by
      intro N hN
      by_cases h : N < N₀
      · exact Or.inr h
      · exact Or.inl ⟨hN.2, hN₀ N (not_lt.1 h) hN.1 hN.2⟩
    calc upperDens {N : ℕ | N ∈ S ∧ N ∈ R}
        ≤ upperDens (smallRatioSet δ ∪ {N : ℕ | N < N₀}) := upperDens_mono hsub
      _ = upperDens (smallRatioSet δ) :=
          upperDens_union_of_densZero _ (densZero_of_finite (Set.finite_lt_nat N₀))
      _ ≤ C * Real.exp (-Real.exp ((1 / δ) ^ c)) := hU δ hδ hδle
  have hlim : Tendsto (fun δ : ℝ => C * Real.exp (-Real.exp ((1 / δ) ^ c))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => 1 / δ) (𝓝[>] 0) atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    have h4 := tendsto_neg_atTop_atBot.comp
      (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop hc).comp h1))
    have h5 := Real.tendsto_exp_atBot.comp h4
    have h6 := h5.const_mul C
    rw [mul_zero] at h6
    exact h6
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  exact key δ hδ.1 hδ.2.le

end Principia.Erdos1054.Proofs
