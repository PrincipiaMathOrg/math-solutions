/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Principia.Erdos1054.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — the proof of Theorem 1.4 (`thm:subexp-growth`), lines 2109–2244

Discharges the `Thm14` package of `Campaigns/Erdos-1054/LEAN-WORKLIST.md`. Parameters:
`P = ⌊ρ log₂X / log₃X⌋`, `J = log P`, `W = √(J log J / 2)`, `F = ⌊e^W⌋`, `t = e^{(1-ε)W}`
(`UpperTails.subP … subT`).

Leaves (definitions and Mathlib only):
* `leaf_UpperTails_Claim_SubexpFltP` (line 2122) — `P ≥ 2` eventually (`P → ∞`), and then
  `W < J` (`log J ≤ J - 1`), so `F ≤ e^W < e^J = P`;
* `leaf_UpperTails_Claim_SubexpLogT` (lines 2224–2229) — `log₃X − log₄X + log(ρ/2) ≤ J ≤
  log₃X − log₄X + log ρ` gives `J / log₃X → 1`, hence `log J − log₄X = log(J/log₃X) → 0`, so
  `W / √(log₃X log₄X / 2) → 1`;
* `leaf_UpperTails_Claim_SubexpCofactorOne` (lines 2155–2156) — `F_1(d) = σ(d)`, and `2 ∣ σ(d)`
  contradicts `2`-roughness of `N = σ(d) ≥ 1`.

Links (from exactly the dependencies the spine names; unused ones are marked `_`):
* `link_UpperTails_Claim_SubexpWitnessStructure` (2157–2181) — `eq:fm-reflection` gives
  `σ(n) = N + (n/L) C`; every `p ≤ P` divides `σ(n)` but not `N`, so `(n/L) C` is `P`-rough;
  `e` is coprime to `n/L` (its prime factors are `≤ F < P`), so `e ∣ L`; then `gcd(e, L) = e` and
  `Fact_KmodGeTwo` gives `C ≥ L ≥ e ≥ 2`, so `C` has a prime factor, necessarily `> P`;
  `C ≤ σ(L)` since `j ↦ L/j` is injective on divisors;
* `link_Eq_MovingKernelLowerBound` (2176–2185), `C₀ = 2e^γ` — `σ(L) Δ(F) ≤ L` (multiplicativity,
  `σ(p^a)(1 - 1/p) ≤ p^a`, primes of `L ∣ Λ(F)` are `≤ F`), Mertens 3 at `F → ∞`, `log F ≤ W`;
* `link_UpperTails_Claim_SubexpCoprimeCount` (2187–2197) — `P# · L ≤ 4^P P^P = (4P)^P ≤ √X`
  (`Λ(F) ≤ F^F`, `F ≤ P`); `|#{u ≤ Y : (u, P#) = 1} − Δ(P) Y| ≤ Δ(P) P#` by complete periods, the
  period count being `Δ(P) P#` by `Notation_Delta_density` and uniqueness of densities;
* `link_UpperTails_Claim_SubexpLowCofactorSum` (2198–2204) — fibre count over `L = Mlcm e d`:
  `(e, d) ↦ (e, ed/L) ∈ divisors(L) × {u ≤ tX/L coprime to P#}` is injective;
* `link_UpperTails_Claim_SubexpLowCofactor` (2202–2207) — `eq:moving-kernel-tail` at `C = C₀`,
  `η/2`, and `W ≥ 2 log 2 / η`;
* `link_UpperTails_Claim_SubexpLargeCofactor` (2209–2218) — `t^{k+1}F^{1-k} ≤ 2^{k-1}e^{-δW}`,
  `δ = (k+1)ε − 2`, against `Δ(P) J ≥ e^{-γ}/2` (Mertens 3) and `e^{δW} ≥ δ⁴J²/24` (`W ≥ √J`);
* `link_Eq_SharpRoughTargetCount` (2122–2129), `C = 2`, `c₁ = e^{-γ}/16`, `c₂ = 4e^{-γ}+1` —
  complete periods on `(X/2, X]`, Mertens 3 along `P`, `J / log₃X → 1`, `P# ≪ √X`;
* `link_Eq_SharpBadSourceCount` (2135–2144), `ρ₀ = c₀` — union bound over the primes `p ≤ P`
  (`B_2 ≪ √Y`, and the odd `p` in range since `u ↦ u / log u` increases for `u ≥ e`);
* `link_UpperTails_Claim_SubexpBadPairs` (2145–2153), `ρ₀ = min(ρ₀', c₁/5)` — `F, t, π(P) ≤ P`,
  `e^{-c₁ log₂Y/P} ≤ (log₂X)^{-5}`, and the elementary `Δ(P) ≥ 1/P`. The dependency
  `Eq_SharpRoughTargetCount` is **not consumed** (`Δ(P) ≥ 1/P` suffices once `c₁/ρ ≥ 5`);
* `link_UpperTails_Claim_SubexpCore` (2219–2224) — every `P`-rough target in `(X/2, X]` not in
  the target set lies in one of five exceptional sets (non-squarefree, odd unrepresented,
  bad-source pairs, low-cofactor witnesses, `lem:moment` large cofactors), each of size
  `≤ (c₁/10) X / log₃X`;
* `link_UpperTails_Claim_SubexpThreshold` (2230–2233), `ε₀ = min(η/2, 1/2)`;
* `link_Eq_SubexpGrowth` (196–208) and `link_Eq_PositiveMomentGrowth` (209–216).
-/

namespace Principia.Erdos1054.Proofs.Thm14

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.UpperTails
open scoped Topology

lemma mem_Dset {e d j : ℕ} : j ∈ Dset e d ↔ 1 ≤ j ∧ j < e ∧ j ∣ e * d := by
  unfold Dset
  rw [Finset.mem_filter, Finset.mem_Ico, and_assoc]

lemma Mlcm_pos (e d : ℕ) : 0 < Mlcm e d := by
  unfold Mlcm
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  have h1 := (mem_Dset.1 hx).1
  simp only [id] at hx0
  omega

lemma dvd_Mlcm {e d j : ℕ} (h : j ∈ Dset e d) : j ∣ Mlcm e d :=
  Finset.dvd_lcm (f := id) h

lemma sig_def (n : ℕ) : sig n = ArithmeticFunction.sigma 1 n := rfl

lemma F_one (d : ℕ) : F 1 d = sig d := by
  unfold F
  rw [one_mul, Finset.filter_true_of_mem (fun q hq => Nat.divisor_le hq)]
  exact (ArithmeticFunction.sigma_one_apply d).symm

lemma not_dvd_of_isRough {y : ℝ} {N p : ℕ} (hN : IsRough y N) (hN0 : N ≠ 0) (hp : p.Prime)
    (hpy : (p : ℝ) ≤ y) : ¬ p ∣ N := by
  intro h
  have := hN p (Nat.mem_primeFactors.2 ⟨hp, h, hN0⟩)
  linarith

lemma coprime_primorial_of {x P : ℕ} (hx : ∀ p : ℕ, p.Prime → p ≤ P → ¬ p ∣ x) :
    Nat.Coprime x (primorial P) := by
  apply Nat.coprime_of_dvd
  intro k hk hkx hkP
  exact hx k hk (hk.dvd_primorial_iff.1 hkP) hkx

lemma Csum_le_sig (e d : ℕ) : Csum e d ≤ sig (Mlcm e d) := by
  have hM := Mlcm_pos e d
  have hs := Nat.sum_div_divisors (Mlcm e d) (fun x => x)
  unfold Csum
  rw [sig_def, ArithmeticFunction.sigma_one_apply, ← hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [Nat.mem_divisors]
    exact ⟨dvd_Mlcm hj, hM.ne'⟩
  · intros
    exact Nat.zero_le _

theorem cofactorOne : UpperTails.Claim_SubexpCofactorOne := by
  intro P N d hP hd hN hR hgood
  have h2 := hgood 2 Nat.prime_two hP
  rw [← F_one, ← hN] at h2
  have hdN : d ≤ N := hN ▸ F_ge 1 d le_rfl hd
  have hN0 : N ≠ 0 := by omega
  exact not_dvd_of_isRough hR hN0 Nat.prime_two (by exact_mod_cast hP) h2

theorem witnessStructure (hFM : Lem_FmModulus) (hKG : Fact_KmodGeTwo) :
    UpperTails.Claim_SubexpWitnessStructure := by
  intro P Fb N e d hFP he2 heF hd hN hR hgood
  obtain ⟨⟨hMdvd, hrefl⟩, _, _, _⟩ := hFM e d he2 hd
  obtain ⟨_, hMpos, _, _, hcase⟩ := hKG e d he2 hd
  have hn : e * d = Mlcm e d * (e * d / Mlcm e d) := (Nat.mul_div_cancel' hMdvd).symm
  have hdN : d ≤ N := hN ▸ F_ge e d (by omega) hd
  have hN0 : N ≠ 0 := by omega
  have hsig : sig (e * d) = N + e * d / Mlcm e d * Csum e d := by
    rw [hN]
    exact hrefl.symm
  have hRC : ∀ p : ℕ, p.Prime → p ≤ P → ¬ p ∣ e * d / Mlcm e d * Csum e d := by
    intro p hp hpP hdiv
    have h1 : p ∣ sig (e * d) := hgood p hp hpP
    rw [hsig] at h1
    have h2 : p ∣ N := (Nat.dvd_add_iff_left hdiv).2 h1
    exact not_dvd_of_isRough hR hN0 hp (by exact_mod_cast hpP) h2
  have hu_cop : Nat.Coprime (e * d / Mlcm e d) (primorial P) :=
    coprime_primorial_of fun p hp hpP h => hRC p hp hpP (h.mul_right _)
  have hC_cop : Nat.Coprime (Csum e d) (primorial P) :=
    coprime_primorial_of fun p hp hpP h => hRC p hp hpP (h.mul_left _)
  have he_cop : Nat.Coprime e (e * d / Mlcm e d) := by
    apply Nat.coprime_of_dvd
    intro k hk hke hku
    have hkP : k ≤ P := by
      have := Nat.le_of_dvd (by omega) hke
      omega
    exact hRC k hk hkP (hku.mul_right _)
  have heM : e ∣ Mlcm e d := by
    have : e ∣ Mlcm e d * (e * d / Mlcm e d) := hn ▸ dvd_mul_right e d
    exact he_cop.dvd_of_dvd_mul_right this
  have hMΛ : Mlcm e d ∣ lcmUpTo (Fb : ℝ) := by
    unfold lcmUpTo Mlcm
    rw [Nat.floor_natCast]
    apply Finset.lcm_mono
    intro j hj
    rw [mem_Dset] at hj
    rw [Finset.mem_Icc]
    omega
  have hg : Nat.gcd e (Mlcm e d) = e := Nat.gcd_eq_left heM
  have hcase' := hcase (by rw [hg, Nat.div_self (by omega)])
  have hPC : P < Csum e d := by
    by_contra hle
    rw [not_lt] at hle
    have hC1 : Csum e d ≠ 1 := by omega
    have hp := Nat.minFac_prime hC1
    have hle' := Nat.minFac_le (show 0 < Csum e d by omega)
    exact hRC (Nat.minFac (Csum e d)) hp (by omega) ((Nat.minFac_dvd _).mul_left _)
  exact ⟨hMdvd, hsig, hu_cop, hC_cop, heM, hMΛ, hPC, Csum_le_sig e d⟩

/-- `σ(p^k) (1 - 1/p) ≤ p^k`. -/
lemma sig_prime_pow_mul_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sig (p ^ k) : ℝ) * (1 - 1 / (p : ℝ)) ≤ (p : ℝ) ^ k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (sig (p ^ k) : ℝ) = ∑ i ∈ Finset.range (k + 1), (p : ℝ) ^ i := by
    rw [sig_def, ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    rfl
  have hg := geom_sum_mul (p : ℝ) (k + 1)
  rw [hs]
  have e1 : (1 - 1 / (p : ℝ)) = ((p : ℝ) - 1) / p := by
    field_simp
  rw [e1, ← mul_div_assoc, hg, div_le_iff₀ hp0, pow_succ]
  linarith

lemma sig_mul_prod_le {M : ℕ} (hM : M ≠ 0) :
    (sig M : ℝ) * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) ≤ M := by
  have h1 : sig M = ∏ p ∈ M.primeFactors, sig (p ^ M.factorization p) := by
    rw [sig_def, ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hM, Finsupp.prod, Nat.support_factorization]
  have h2 : (M : ℝ) = ∏ p ∈ M.primeFactors, (p : ℝ) ^ M.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hM]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [h1, h2]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
    have h0 : (0 : ℝ) ≤ 1 - 1 / p := by linarith
    positivity
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := sig_prime_pow_mul_le hpp (M.factorization p)
    exact this

/-! ## Iterated logarithms -/

lemma logIt_one (x : ℝ) : logIt 1 x = Real.log x := rfl
lemma logIt_two (x : ℝ) : logIt 2 x = Real.log (logIt 1 x) := rfl
lemma logIt_three (x : ℝ) : logIt 3 x = Real.log (logIt 2 x) := rfl
lemma logIt_four (x : ℝ) : logIt 4 x = Real.log (logIt 3 x) := rfl

lemma tendsto_logIt_one : Tendsto (fun x : ℝ => logIt 1 x) atTop atTop := Real.tendsto_log_atTop
lemma tendsto_logIt_two : Tendsto (fun x : ℝ => logIt 2 x) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_logIt_one
lemma tendsto_logIt_three : Tendsto (fun x : ℝ => logIt 3 x) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_logIt_two
lemma tendsto_logIt_four : Tendsto (fun x : ℝ => logIt 4 x) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_logIt_three

lemma tendsto_log_div_self : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa using h

lemma half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.2 hx
  linarith

/-! ## The parameters `P, J, W, F, t` -/

lemma tendsto_ratio {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun X : ℝ => ρ * logIt 2 X / logIt 3 X) atTop atTop := by
  have h1 : Tendsto (fun X : ℝ => logIt 3 X / logIt 2 X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_log_div_self.comp tendsto_logIt_two, ?_⟩
    filter_upwards [tendsto_logIt_three.eventually_gt_atTop 0,
      tendsto_logIt_two.eventually_gt_atTop 0] with X h3 h2
    exact div_pos h3 h2
  have h2 := (h1.inv_tendsto_nhdsGT_zero).const_mul_atTop hρ
  refine h2.congr' (Eventually.of_forall fun X => ?_)
  simp only [Pi.inv_apply, inv_div]
  ring

lemma tendsto_subP {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (fun X : ℝ => (subP ρ X : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (tendsto_ratio hρ))

lemma tendsto_subJ {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (fun X : ℝ => subJ ρ X) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_subP hρ)

lemma sqrt_le_Wmov {J : ℝ} (hJ : Real.exp 2 ≤ J) : Real.sqrt J ≤ Wmov J := by
  unfold Wmov
  apply Real.sqrt_le_sqrt
  have hJ0 : 0 < J := lt_of_lt_of_le (Real.exp_pos 2) hJ
  have hl : 2 ≤ Real.log J := by
    have := Real.log_le_log (Real.exp_pos 2) hJ
    rwa [Real.log_exp] at this
  nlinarith

lemma tendsto_Wmov : Tendsto Wmov atTop atTop :=
  tendsto_atTop_mono' atTop ((eventually_ge_atTop (Real.exp 2)).mono fun _ hJ => sqrt_le_Wmov hJ)
    Real.tendsto_sqrt_atTop

lemma tendsto_subW {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (fun X : ℝ => subW ρ X) atTop atTop :=
  tendsto_Wmov.comp (tendsto_subJ hρ)

lemma Wmov_nonneg (J : ℝ) : 0 ≤ Wmov J := Real.sqrt_nonneg _

lemma subW_nonneg (ρ X : ℝ) : 0 ≤ subW ρ X := Wmov_nonneg _

lemma Wmov_le {J : ℝ} (hJ : 0 ≤ J) : Wmov J ≤ J := by
  unfold Wmov
  rw [Real.sqrt_le_left hJ]
  have := Real.log_le_self hJ
  nlinarith

lemma Wmov_lt {J : ℝ} (hJ : 0 < J) : Wmov J < J := by
  unfold Wmov
  rw [Real.sqrt_lt' hJ]
  have := Real.log_le_sub_one_of_pos hJ
  nlinarith

lemma subF_le (ρ X : ℝ) : (subF ρ X : ℝ) ≤ Real.exp (subW ρ X) :=
  Nat.floor_le (Real.exp_pos _).le

lemma half_le_subF (ρ X : ℝ) : Real.exp (subW ρ X) / 2 ≤ (subF ρ X : ℝ) :=
  half_le_floor (Real.one_le_exp (subW_nonneg ρ X))

lemma one_le_subF (ρ X : ℝ) : 1 ≤ subF ρ X := by
  unfold subF Fmov
  exact Nat.one_le_floor_iff _ |>.2 (Real.one_le_exp (Wmov_nonneg _))

lemma subJ_eq (ρ X : ℝ) : subJ ρ X = Real.log (subP ρ X) := rfl

/-- `e^W ≤ P` once `P ≥ 1`. -/
lemma expW_le_subP {ρ X : ℝ} (hP : 1 ≤ subP ρ X) : Real.exp (subW ρ X) ≤ subP ρ X := by
  have hP1 : (1 : ℝ) ≤ subP ρ X := by exact_mod_cast hP
  have hJ : 0 ≤ subJ ρ X := Real.log_nonneg hP1
  have h := Wmov_le hJ
  calc Real.exp (subW ρ X) ≤ Real.exp (subJ ρ X) := Real.exp_le_exp.2 h
    _ = subP ρ X := Real.exp_log (by linarith)

lemma subF_lt_subP {ρ X : ℝ} (hP : 2 ≤ subP ρ X) : subF ρ X < subP ρ X := by
  have hP1 : (2 : ℝ) ≤ subP ρ X := by exact_mod_cast hP
  have hJ : 0 < subJ ρ X := Real.log_pos (by linarith)
  have h := Wmov_lt hJ
  have h2 : Real.exp (subW ρ X) < subP ρ X := by
    calc Real.exp (subW ρ X) < Real.exp (subJ ρ X) := Real.exp_lt_exp.2 h
      _ = subP ρ X := Real.exp_log (by linarith)
  have h3 := subF_le ρ X
  exact_mod_cast lt_of_le_of_lt h3 h2

lemma eventually_subP_ge {ρ : ℝ} (hρ : 0 < ρ) (K : ℕ) : ∀ᶠ X : ℝ in atTop, K ≤ subP ρ X := by
  filter_upwards [(tendsto_subP hρ).eventually_ge_atTop (K : ℝ)] with X hX
  exact_mod_cast hX

theorem fltP : UpperTails.Claim_SubexpFltP := by
  intro ρ hρ
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_subP_ge hρ 2)
  exact ⟨X₀, fun X hX => subF_lt_subP (hX₀ X hX)⟩

/-! ## `J / log₃ X → 1` and `log J / log₄ X → 1` -/

lemma subJ_bounds {ρ X : ℝ} (hρ : 0 < ρ) (h2 : 0 < logIt 2 X) (h3 : 0 < logIt 3 X)
    (hr : 1 ≤ ρ * logIt 2 X / logIt 3 X) :
    logIt 3 X - logIt 4 X + Real.log (ρ / 2) ≤ subJ ρ X ∧
      subJ ρ X ≤ logIt 3 X - logIt 4 X + Real.log ρ := by
  have hlr : Real.log (ρ * logIt 2 X / logIt 3 X) = logIt 3 X - logIt 4 X + Real.log ρ := by
    rw [Real.log_div (by positivity) h3.ne', Real.log_mul hρ.ne' h2.ne', ← logIt_three,
      ← logIt_four]
    ring
  have hlo := half_le_floor hr
  have hhi : (subP ρ X : ℝ) ≤ ρ * logIt 2 X / logIt 3 X := Nat.floor_le (by positivity)
  have hr0 : 0 < ρ * logIt 2 X / logIt 3 X := by positivity
  constructor
  · have h := Real.log_le_log (by positivity) hlo
    rw [Real.log_div hr0.ne' (by norm_num), hlr] at h
    rw [Real.log_div hρ.ne' (by norm_num), subJ_eq]
    unfold subP at *
    linarith
  · have h := Real.log_le_log (lt_of_lt_of_le (by positivity) hlo) hhi
    rw [hlr] at h
    rw [subJ_eq]
    exact h

lemma tendsto_const_div_logIt_three (c : ℝ) :
    Tendsto (fun X : ℝ => c / logIt 3 X) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_logIt_three

lemma tendsto_four_div_three : Tendsto (fun X : ℝ => logIt 4 X / logIt 3 X) atTop (𝓝 0) :=
  tendsto_log_div_self.comp tendsto_logIt_three

lemma tendsto_subJ_div {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun X : ℝ => subJ ρ X / logIt 3 X) atTop (𝓝 1) := by
  have hlo : Tendsto (fun X : ℝ => 1 - logIt 4 X / logIt 3 X + Real.log (ρ / 2) / logIt 3 X)
      atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)).sub tendsto_four_div_three).add
      (tendsto_const_div_logIt_three (Real.log (ρ / 2)))
    simpa using this
  have hhi : Tendsto (fun X : ℝ => 1 - logIt 4 X / logIt 3 X + Real.log ρ / logIt 3 X)
      atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)).sub tendsto_four_div_three).add
      (tendsto_const_div_logIt_three (Real.log ρ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [tendsto_logIt_two.eventually_gt_atTop 0,
      tendsto_logIt_three.eventually_gt_atTop 0,
      (tendsto_ratio hρ).eventually_ge_atTop 1] with X h2 h3 hr
    have hb := (subJ_bounds hρ h2 h3 hr).1
    have e : 1 - logIt 4 X / logIt 3 X + Real.log (ρ / 2) / logIt 3 X =
        (logIt 3 X - logIt 4 X + Real.log (ρ / 2)) / logIt 3 X := by
      rw [add_div, sub_div, div_self h3.ne']
    rw [e]
    exact div_le_div_of_nonneg_right hb h3.le
  · filter_upwards [tendsto_logIt_two.eventually_gt_atTop 0,
      tendsto_logIt_three.eventually_gt_atTop 0,
      (tendsto_ratio hρ).eventually_ge_atTop 1] with X h2 h3 hr
    have hb := (subJ_bounds hρ h2 h3 hr).2
    have e : 1 - logIt 4 X / logIt 3 X + Real.log ρ / logIt 3 X =
        (logIt 3 X - logIt 4 X + Real.log ρ) / logIt 3 X := by
      rw [add_div, sub_div, div_self h3.ne']
    rw [e]
    exact div_le_div_of_nonneg_right hb h3.le

lemma tendsto_logJ_div {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun X : ℝ => Real.log (subJ ρ X) / logIt 4 X) atTop (𝓝 1) := by
  have h1 : Tendsto (fun X : ℝ => Real.log (subJ ρ X / logIt 3 X)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp (tendsto_subJ_div hρ)
    rw [Real.log_one] at this
    exact this
  have h2 : Tendsto (fun X : ℝ => 1 + Real.log (subJ ρ X / logIt 3 X) / logIt 4 X) atTop
      (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)) |>.add (h1.div_atTop tendsto_logIt_four)
    simpa using this
  refine h2.congr' ?_
  filter_upwards [(tendsto_subJ hρ).eventually_gt_atTop 0,
    tendsto_logIt_three.eventually_gt_atTop 0,
    tendsto_logIt_four.eventually_gt_atTop 0] with X hJ h3 h4
  rw [Real.log_div hJ.ne' h3.ne', ← logIt_four, sub_div, div_self h4.ne']
  ring

/-- `W / √(log₃X · log₄X / 2) → 1`. -/
lemma tendsto_subW_div {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun X : ℝ => subW ρ X / Real.sqrt (logIt 3 X * logIt 4 X / 2)) atTop (𝓝 1) := by
  have h := ((tendsto_subJ_div hρ).mul (tendsto_logJ_div hρ))
  rw [mul_one] at h
  have hs := ((Real.continuous_sqrt.tendsto 1).comp h)
  rw [Real.sqrt_one] at hs
  refine hs.congr' ?_
  filter_upwards [tendsto_logIt_three.eventually_gt_atTop 0,
    tendsto_logIt_four.eventually_gt_atTop 0] with X h3 h4
  have hd : (0 : ℝ) ≤ logIt 3 X * logIt 4 X / 2 := by positivity
  simp only [Function.comp_apply]
  rw [subW, Wmov, ← Real.sqrt_div' _ hd]
  congr 1
  field_simp

theorem logT : UpperTails.Claim_SubexpLogT := by
  intro ρ hρ ε hε hε1 η hη
  have h := Metric.tendsto_nhds.1 (tendsto_subW_div hρ) η hη
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (h.and ((tendsto_logIt_three.eventually_gt_atTop 0).and
    (tendsto_logIt_four.eventually_gt_atTop 0)))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hd, h3, h4⟩ := hX₀ X hX
  rw [Real.dist_eq] at hd
  set S := Real.sqrt (logIt 3 X * logIt 4 X) with hS
  set V := Real.sqrt (logIt 3 X * logIt 4 X / 2) with hV
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hV0 : 0 < V := Real.sqrt_pos.2 (by positivity)
  have hVS : V = S / Real.sqrt 2 := Real.sqrt_div (by positivity) 2
  have hs2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs20 : 0 < Real.sqrt 2 := by linarith
  have hVle : V ≤ S := by
    rw [hVS, div_le_iff₀ hs20]
    nlinarith
  have hlogt : Real.log (subT ε ρ X) = (1 - ε) * subW ρ X := by
    unfold subT
    rw [Real.log_exp]
  have e1 : (1 - ε) / Real.sqrt 2 * S = (1 - ε) * V := by
    rw [hVS]
    ring
  have e2 : (1 - ε) * subW ρ X - (1 - ε) * V = (1 - ε) * V * (subW ρ X / V - 1) := by
    field_simp
  rw [hlogt, e1, e2, abs_mul, abs_of_pos (by nlinarith : 0 < (1 - ε) * V)]
  have hle : (1 - ε) * V ≤ S := by nlinarith
  calc (1 - ε) * V * |subW ρ X / V - 1| ≤ S * η :=
        mul_le_mul hle hd.le (abs_nonneg _) hS0.le
    _ = η * S := by ring

/-! ## Monotonicity of the iterated logarithms -/

lemma logIt_mono_regime {N X : ℝ} (hN : Real.exp (Real.exp (Real.exp 1)) ≤ N) (hNX : N ≤ X) :
    1 ≤ logIt 3 N ∧ logIt 3 N ≤ logIt 3 X ∧ 0 ≤ logIt 4 N ∧ logIt 4 N ≤ logIt 4 X := by
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos _) hN
  have h1 : Real.exp (Real.exp 1) ≤ logIt 1 N := by
    have := Real.log_le_log (Real.exp_pos _) hN
    rwa [Real.log_exp] at this
  have h1' : logIt 1 N ≤ logIt 1 X := Real.log_le_log hN0 hNX
  have hl1 : 0 < logIt 1 N := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp 1 ≤ logIt 2 N := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have h2' : logIt 2 N ≤ logIt 2 X := Real.log_le_log hl1 h1'
  have hl2 : 0 < logIt 2 N := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : 1 ≤ logIt 3 N := by
    have := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this
  have h3' : logIt 3 N ≤ logIt 3 X := Real.log_le_log hl2 h2'
  have h4 : 0 ≤ logIt 4 N := Real.log_nonneg h3
  have h4' : logIt 4 N ≤ logIt 4 X :=
    Real.log_le_log (x := logIt 3 N) (y := logIt 3 X) (by linarith) h3'
  exact ⟨h3, h3', h4, h4'⟩

lemma one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem threshold (hLT : UpperTails.Claim_SubexpLogT) : UpperTails.Claim_SubexpThreshold := by
  intro η hη
  refine ⟨min (η / 2) (1 / 2), by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro ε hε hεle ρ hρ
  have hε1 : ε < 1 := lt_of_le_of_lt (hεle.trans (min_le_right _ _)) (by norm_num)
  have hεη : ε ≤ η / 2 := hεle.trans (min_le_left _ _)
  obtain ⟨X₁, hX₁⟩ := hLT ρ hρ ε hε hε1 (η / 2) (by positivity)
  refine ⟨max X₁ (2 * Real.exp (Real.exp (Real.exp 1))), fun X hX N hN1 hN2 => ?_⟩
  have hXX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : 2 * Real.exp (Real.exp (Real.exp 1)) ≤ X := le_trans (le_max_right _ _) hX
  have hNe : Real.exp (Real.exp (Real.exp 1)) ≤ (N : ℝ) := by linarith
  obtain ⟨m1, m2, m3, m4⟩ := logIt_mono_regime hNe hN2
  have hS : Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ)) ≤
      Real.sqrt (logIt 3 X * logIt 4 X) :=
    Real.sqrt_le_sqrt (mul_le_mul m2 m4 m3 (by linarith))
  have hS0 : 0 ≤ Real.sqrt (logIt 3 X * logIt 4 X) := Real.sqrt_nonneg _
  have hlt := hX₁ X hXX1
  rw [abs_le] at hlt
  have hlogt : Real.log (subT ε ρ X) = (1 - ε) * subW ρ X := by
    unfold subT
    rw [Real.log_exp]
  rw [hlogt] at hlt
  unfold subT
  rw [Real.exp_le_exp]
  by_cases hc : 1 / Real.sqrt 2 - η ≤ 0
  · have h1 : (1 / Real.sqrt 2 - η) * Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
    have h2 : 0 ≤ (1 - ε) * subW ρ X := mul_nonneg (by linarith) (subW_nonneg _ _)
    linarith
  · rw [not_le] at hc
    have h1 : (1 / Real.sqrt 2 - η) * Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ)) ≤
        (1 / Real.sqrt 2 - η) * Real.sqrt (logIt 3 X * logIt 4 X) :=
      mul_le_mul_of_nonneg_left hS hc.le
    have hk : ε / Real.sqrt 2 ≤ η / 2 := (div_le_self hε.le one_le_sqrt_two).trans hεη
    have e : (1 - ε) / Real.sqrt 2 = 1 / Real.sqrt 2 - ε / Real.sqrt 2 := sub_div _ _ _
    have h2 : (1 / Real.sqrt 2 - η) * Real.sqrt (logIt 3 X * logIt 4 X) ≤
        ((1 - ε) / Real.sqrt 2 - η / 2) * Real.sqrt (logIt 3 X * logIt 4 X) := by
      apply mul_le_mul_of_nonneg_right _ hS0
      rw [e]
      linarith
    have h3 : ((1 - ε) / Real.sqrt 2 - η / 2) * Real.sqrt (logIt 3 X * logIt 4 X) =
        (1 - ε) / Real.sqrt 2 * Real.sqrt (logIt 3 X * logIt 4 X) -
          η / 2 * Real.sqrt (logIt 3 X * logIt 4 X) := by ring
    linarith

open Classical in
lemma cntHalf_le_card (S : Set ℕ) (X : ℝ) (T : Finset ℕ)
    (h : ∀ N : ℕ, ⌊X / 2⌋₊ < N → N ≤ ⌊X⌋₊ → N ∈ S → N ∈ T) : cntHalf S X ≤ T.card := by
  unfold cntHalf
  apply Finset.card_le_card
  intro N hN
  rw [Finset.mem_filter, Finset.mem_Ioc] at hN
  exact h N hN.1.1 hN.1.2 hN.2

open Classical in
theorem subexpGrowth (hC : UpperTails.Claim_SubexpCore) (hT : UpperTails.Claim_SubexpThreshold) :
    Eq_SubexpGrowth := by
  intro η hη
  obtain ⟨ε₀, hε₀, hε₀1, hT'⟩ := hT η hη
  obtain ⟨ρ₀, hρ₀, hC'⟩ := hC
  obtain ⟨c, hc, X₁, hX₁⟩ := hC' ρ₀ hρ₀ le_rfl ε₀ hε₀ hε₀1
  obtain ⟨X₂, hX₂⟩ := hT' ε₀ hε₀ le_rfl ρ₀ hρ₀
  refine ⟨c, hc, max (max X₁ X₂) 0, fun X hX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
  refine (hX₁ X hX1).trans (Nat.cast_le.2 (cntHalf_le_card _ X _ ?_))
  · intro N hN1 hN2 hNS
    obtain ⟨hR, hsq, ht⟩ := hNS
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hN1, hN2⟩, ?_⟩
    have hNl : X / 2 < (N : ℝ) := (Nat.floor_lt (by linarith)).1 hN1
    have hNu : (N : ℝ) ≤ X := (Nat.le_floor_iff hX0).1 hN2
    have hN0 : (0 : ℝ) < N := by linarith
    refine ⟨hR, hsq, ?_⟩
    have hth := hX₂ X hX2 N hNl hNu
    have ht' : subT ε₀ ρ₀ X < (f N : ℝ) / N := by
      rw [lt_div_iff₀ hN0]
      exact ht
    exact lt_of_le_of_lt hth ht'

/-! ## `eq:positive-moment-growth` -/

lemma log_half_le {x y : ℝ} (hx : 4 ≤ x) (hy : x / 2 ≤ y) :
    Real.log x / 2 ≤ Real.log y ∧ Real.log x - Real.log 2 ≤ Real.log y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < x / 2 := by linarith
  have h1 : Real.log (x / 2) ≤ Real.log y := Real.log_le_log hy0 hy
  rw [Real.log_div hx0.ne' (by norm_num)] at h1
  have h4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  constructor <;> linarith

/-- For `X/2 ≤ N` with `X` large: `log₃ N ≥ log₃ X − log 2 ≥ 0` and `log₄ N ≥ log₄ X − log 2`. -/
lemma logIt_half {X N : ℝ} (hX : 4 ≤ X) (h1 : 4 ≤ logIt 1 X) (h2 : 4 ≤ logIt 2 X)
    (h3 : 4 ≤ logIt 3 X) (hN : X / 2 ≤ N) :
    logIt 3 X - Real.log 2 ≤ logIt 3 N ∧ logIt 4 X - Real.log 2 ≤ logIt 4 N := by
  obtain ⟨a1, _⟩ := log_half_le hX hN
  obtain ⟨b1, _⟩ := log_half_le h1 a1
  obtain ⟨c1, c2⟩ := log_half_le h2 b1
  obtain ⟨_, d2⟩ := log_half_le h3 c1
  exact ⟨c2, d2⟩

lemma exp_ge_pow_four {y : ℝ} (hy : 0 ≤ y) : y ^ 4 / 24 ≤ Real.exp y := by
  calc y ^ 4 / 24 = y ^ 4 / ((Nat.factorial 4 : ℕ) : ℝ) := by norm_num [Nat.factorial]
    _ ≤ Real.exp y := Real.pow_div_factorial_le_exp y hy 4

open Classical in
/-- The moment bound for an abstract finite set `G` of large-ratio targets. -/
lemma moment_aux {s η δ c X : ℝ} (hs : 0 < s) (hη : 0 < η) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hδs : s * δ ≤ η / 4) (hc : 0 < c) (hX4 : 4 ≤ X) (h1 : 4 ≤ logIt 1 X) (h2 : 4 ≤ logIt 2 X)
    (h3 : 4 ≤ logIt 3 X) (h4 : 1 ≤ logIt 4 X) (h3δ : Real.log 2 ≤ δ * logIt 3 X)
    (h4δ : Real.log 2 ≤ δ * logIt 4 X) (h3big : 24 / (c * (η / 2) ^ 4) ≤ logIt 3 X)
    (G : Finset ℕ) (hcard : c * X / logIt 3 X ≤ (G.card : ℝ))
    (hG : ∀ N ∈ G, 1 ≤ N ∧ N ≤ ⌊X⌋₊ ∧ N ∈ R ∧ X / 2 < (N : ℝ) ∧
      Real.exp ((1 / Real.sqrt 2 - δ) * Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ))) <
        (f N : ℝ) / N) :
    Real.exp ((s / Real.sqrt 2 - η) * Real.sqrt (logIt 3 X * logIt 4 X)) ≤
      (1 / X) * ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), ((f N : ℝ) / N) ^ s := by
  have hX0 : 0 < X := by linarith
  have ha0 : 0 < logIt 3 X := by linarith
  have hb0 : 0 < logIt 4 X := by linarith
  have hs2 : 1 ≤ Real.sqrt 2 := one_le_sqrt_two
  have hs2' : 1 / Real.sqrt 2 ≤ 1 := by rw [div_le_one (by linarith)]; exact hs2
  have hs2'' : 1 / 2 < 1 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    have : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  obtain ⟨S, hS⟩ : ∃ S, Real.sqrt (logIt 3 X * logIt 4 X) = S := ⟨_, rfl⟩
  rw [hS]
  have hS0 : 0 ≤ S := hS ▸ Real.sqrt_nonneg _
  obtain ⟨E, hE⟩ : ∃ E, Real.exp (s * ((1 / Real.sqrt 2 - δ) * ((1 - δ) * S))) = E := ⟨_, rfl⟩
  have hmem : ∀ N ∈ G, E ≤ ((f N : ℝ) / N) ^ s := by
    intro N hN
    obtain ⟨_, _, _, hNl, hfN⟩ := hG N hN
    obtain ⟨l3, l4⟩ := logIt_half hX4 h1 h2 h3 hNl.le
    have hδa : 0 ≤ (1 - δ) * logIt 3 X := mul_nonneg (by linarith) ha0.le
    have hδb : 0 ≤ (1 - δ) * logIt 4 X := mul_nonneg (by linarith) hb0.le
    have l3' : (1 - δ) * logIt 3 X ≤ logIt 3 (N : ℝ) := by nlinarith
    have l4' : (1 - δ) * logIt 4 X ≤ logIt 4 (N : ℝ) := by nlinarith
    have hprod : ((1 - δ) * S) ^ 2 ≤ logIt 3 (N : ℝ) * logIt 4 (N : ℝ) := by
      rw [mul_pow, ← hS, Real.sq_sqrt (by positivity)]
      have e : (1 - δ) ^ 2 * (logIt 3 X * logIt 4 X) =
          ((1 - δ) * logIt 3 X) * ((1 - δ) * logIt 4 X) := by ring
      rw [e]
      exact mul_le_mul l3' l4' hδb (le_trans hδa l3')
    have hsq : (1 - δ) * S ≤ Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ)) :=
      Real.le_sqrt_of_sq_le hprod
    have hco : 0 ≤ 1 / Real.sqrt 2 - δ := by linarith
    have hA : (1 / Real.sqrt 2 - δ) * ((1 - δ) * S) ≤
        (1 / Real.sqrt 2 - δ) * Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq hco
    calc E = Real.exp (s * ((1 / Real.sqrt 2 - δ) * ((1 - δ) * S))) := hE.symm
      _ ≤ Real.exp (((1 / Real.sqrt 2 - δ) *
            Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ))) * s) := by
          rw [Real.exp_le_exp, mul_comm s]
          exact mul_le_mul_of_nonneg_right hA hs.le
      _ = Real.exp ((1 / Real.sqrt 2 - δ) *
            Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ))) ^ s := Real.exp_mul _ _
      _ ≤ ((f N : ℝ) / N) ^ s := Real.rpow_le_rpow (Real.exp_pos _).le hfN.le hs.le
  have hsub : G ⊆ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R) := by
    intro N hN
    obtain ⟨hN1, hN2, hR, _, _⟩ := hG N hN
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hN1, hN2⟩, hR⟩
  have hnn : ∀ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), N ∉ G →
      (0 : ℝ) ≤ ((f N : ℝ) / N) ^ s :=
    fun N _ _ => Real.rpow_nonneg (by positivity) s
  have hsum1 : ∑ N ∈ G, ((f N : ℝ) / N) ^ s ≤
      ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), ((f N : ℝ) / N) ^ s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hsum2 : (G.card : ℝ) * E ≤ ∑ N ∈ G, ((f N : ℝ) / N) ^ s := by
    have := Finset.card_nsmul_le_sum G (fun N => ((f N : ℝ) / N) ^ s) E hmem
    rw [nsmul_eq_mul] at this
    exact this
  have hexp1 : (s / Real.sqrt 2 - η / 2) * S ≤ s * ((1 / Real.sqrt 2 - δ) * ((1 - δ) * S)) := by
    have e : s * ((1 / Real.sqrt 2 - δ) * ((1 - δ) * S)) =
        (s / Real.sqrt 2 - s * δ - s * δ * (1 / Real.sqrt 2) + s * δ * δ) * S := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hS0
    have h1' : s * δ * (1 / Real.sqrt 2) ≤ s * δ := by
      have := mul_le_mul_of_nonneg_left hs2' (by positivity : (0 : ℝ) ≤ s * δ)
      linarith
    have h2' : 0 ≤ s * δ * δ := by positivity
    linarith
  have hSa : Real.sqrt (logIt 3 X) ≤ S := by
    rw [← hS]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hbig : logIt 3 X ≤ c * Real.exp (η / 2 * S) := by
    have hy : 0 ≤ η / 2 * Real.sqrt (logIt 3 X) := by positivity
    have he := exp_ge_pow_four hy
    have hmono : Real.exp (η / 2 * Real.sqrt (logIt 3 X)) ≤ Real.exp (η / 2 * S) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hSa (by positivity))
    have hsq : Real.sqrt (logIt 3 X) ^ 2 = logIt 3 X := Real.sq_sqrt ha0.le
    have hpow : (η / 2 * Real.sqrt (logIt 3 X)) ^ 4 = (η / 2) ^ 4 * logIt 3 X ^ 2 := by
      calc (η / 2 * Real.sqrt (logIt 3 X)) ^ 4
          = (η / 2) ^ 4 * (Real.sqrt (logIt 3 X) ^ 2) ^ 2 := by ring
        _ = (η / 2) ^ 4 * logIt 3 X ^ 2 := by rw [hsq]
    rw [hpow] at he
    have hc4 : 0 < c * (η / 2) ^ 4 := by positivity
    have h3big' : 24 ≤ logIt 3 X * (c * (η / 2) ^ 4) := by
      rw [div_le_iff₀ hc4] at h3big
      exact h3big
    have key : logIt 3 X ≤ c * ((η / 2) ^ 4 * logIt 3 X ^ 2 / 24) := by
      rw [show c * ((η / 2) ^ 4 * logIt 3 X ^ 2 / 24) =
          logIt 3 X * (logIt 3 X * (c * (η / 2) ^ 4)) / 24 by ring, le_div_iff₀ (by norm_num)]
      exact mul_le_mul_of_nonneg_left h3big' ha0.le
    exact key.trans (mul_le_mul_of_nonneg_left (he.trans hmono) hc.le)
  have hE0 : 0 < E := hE ▸ Real.exp_pos _
  have hfinal : Real.exp ((s / Real.sqrt 2 - η) * S) ≤ c / logIt 3 X * E := by
    have e1 : Real.exp ((s / Real.sqrt 2 - η) * S) =
        Real.exp ((s / Real.sqrt 2 - η / 2) * S) / Real.exp (η / 2 * S) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [e1, div_le_iff₀ (Real.exp_pos _)]
    have hEge : Real.exp ((s / Real.sqrt 2 - η / 2) * S) ≤ E := hE ▸ Real.exp_le_exp.2 hexp1
    have e2 : c / logIt 3 X * E * Real.exp (η / 2 * S) =
        E * (c * Real.exp (η / 2 * S)) / logIt 3 X := by ring
    rw [e2, le_div_iff₀ ha0]
    calc Real.exp ((s / Real.sqrt 2 - η / 2) * S) * logIt 3 X ≤ E * logIt 3 X :=
          mul_le_mul_of_nonneg_right hEge ha0.le
      _ ≤ E * (c * Real.exp (η / 2 * S)) := mul_le_mul_of_nonneg_left hbig hE0.le
  have hXne : X ≠ 0 := hX0.ne'
  have hane : logIt 3 X ≠ 0 := ha0.ne'
  have e3 : c / logIt 3 X * E = 1 / X * (c * X / logIt 3 X * E) := by
    field_simp
  calc Real.exp ((s / Real.sqrt 2 - η) * S) ≤ c / logIt 3 X * E := hfinal
    _ = 1 / X * (c * X / logIt 3 X * E) := e3
    _ ≤ 1 / X * ((G.card : ℝ) * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hE0.le) (by positivity)
    _ ≤ 1 / X * ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), ((f N : ℝ) / N) ^ s :=
        mul_le_mul_of_nonneg_left (hsum2.trans hsum1) (by positivity)

open Classical in
theorem positiveMomentGrowth (hG : Eq_SubexpGrowth) : Eq_PositiveMomentGrowth := by
  intro s hs η hη
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (η / (4 * s)) (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 2 := hδ ▸ min_le_right _ _
  have hδs : s * δ ≤ η / 4 := by
    have : δ ≤ η / (4 * s) := hδ ▸ min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨c, hc, X₁, hX₁⟩ := hG δ hδ0
  have ev : ∀ᶠ X : ℝ in atTop, X₁ ≤ X ∧ 4 ≤ X ∧ 4 ≤ logIt 1 X ∧ 4 ≤ logIt 2 X ∧
      4 ≤ logIt 3 X ∧ 1 ≤ logIt 4 X ∧ Real.log 2 ≤ δ * logIt 3 X ∧
      Real.log 2 ≤ δ * logIt 4 X ∧ 24 / (c * (η / 2) ^ 4) ≤ logIt 3 X := by
    filter_upwards [eventually_ge_atTop X₁, eventually_ge_atTop 4,
      tendsto_logIt_one.eventually_ge_atTop 4, tendsto_logIt_two.eventually_ge_atTop 4,
      tendsto_logIt_three.eventually_ge_atTop 4, tendsto_logIt_four.eventually_ge_atTop 1,
      (tendsto_logIt_three.const_mul_atTop hδ0).eventually_ge_atTop (Real.log 2),
      (tendsto_logIt_four.const_mul_atTop hδ0).eventually_ge_atTop (Real.log 2),
      tendsto_logIt_three.eventually_ge_atTop (24 / (c * (η / 2) ^ 4))]
      with X a1 a2 a3 a4 a5 a6 a7 a8 a9
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ev
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hXX1, hX4, h1, h2, h3, h4, h3δ, h4δ, h3big⟩ := hX₀ X hX
  refine moment_aux hs hη hδ0 hδ1 hδs hc hX4 h1 h2 h3 h4 h3δ h4δ h3big _ (hX₁ X hXX1) ?_
  intro N hN
  rw [Finset.mem_filter, Finset.mem_Ioc] at hN
  obtain ⟨⟨hN1, hN2⟩, hR, _, hfN⟩ := hN
  exact ⟨by omega, hN2, hR, (Nat.floor_lt (by linarith)).1 hN1, hfN⟩


/-! ## `Δ`, primorials and `Λ(F)` -/

lemma Delta_nonneg (y : ℝ) : 0 ≤ Delta y := by
  unfold Delta
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 := (Finset.mem_filter.1 hp).2.two_le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have : (1 : ℝ) / p ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hpR
  linarith

lemma Delta_pos (y : ℝ) : 0 < Delta y := by
  unfold Delta
  refine Finset.prod_pos fun p hp => ?_
  have hp2 := (Finset.mem_filter.1 hp).2.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have : (1 : ℝ) / p < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

lemma Delta_le_one (y : ℝ) : Delta y ≤ 1 := by
  unfold Delta
  apply Finset.prod_le_one
  · intro p hp
    have hp2 := (Finset.mem_filter.1 hp).2.two_le
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hpR
    linarith
  · intro p _
    have : (0 : ℝ) ≤ 1 / p := by positivity
    linarith

/-- `σ(M) Δ(n) ≤ M` when every prime factor of `M` is at most `n`. -/
lemma sig_mul_Delta_le {M n : ℕ} (hM : M ≠ 0) (h : ∀ p ∈ M.primeFactors, p ≤ n) :
    (sig M : ℝ) * Delta n ≤ M := by
  have hsub : M.primeFactors ⊆ (Finset.range (⌊(n : ℝ)⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.floor_natCast, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := h p hp; omega, Nat.prime_of_mem_primeFactors hp⟩
  have hsplit := Finset.prod_sdiff (f := fun p : ℕ => (1 - 1 / (p : ℝ))) hsub
  have hle1 : ∏ p ∈ (Finset.range (⌊(n : ℝ)⌋₊ + 1)).filter Nat.Prime \ M.primeFactors,
      (1 - 1 / (p : ℝ)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      have hp2 := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hp).1).2.two_le
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
      have : (1 : ℝ) / p ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hpR
      linarith
    · intro p _
      have : (0 : ℝ) ≤ 1 / p := by positivity
      linarith
  have hpf0 : 0 ≤ ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hp1
    linarith
  have hDle : Delta n ≤ ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) := by
    unfold Delta
    rw [← hsplit]
    calc (∏ p ∈ (Finset.range (⌊(n : ℝ)⌋₊ + 1)).filter Nat.Prime \ M.primeFactors,
          (1 - 1 / (p : ℝ))) * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ))
        ≤ 1 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hle1 hpf0
      _ = ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) := one_mul _
  calc (sig M : ℝ) * Delta n ≤ (sig M : ℝ) * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hDle (Nat.cast_nonneg _)
    _ ≤ M := sig_mul_prod_le hM

lemma lcmUpTo_pos (A : ℝ) : 0 < lcmUpTo A := by
  unfold lcmUpTo
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  rw [Finset.mem_Icc] at hx
  simp only [id] at hx0
  omega

lemma lcmUpTo_dvd_prod (n : ℕ) : lcmUpTo (n : ℝ) ∣ ∏ i ∈ Finset.Icc 1 n, i := by
  unfold lcmUpTo
  rw [Nat.floor_natCast]
  exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem (fun i => i) hi

lemma lcmUpTo_le_pow (n : ℕ) : lcmUpTo (n : ℝ) ≤ n ^ n := by
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 n, i :=
    Finset.prod_pos fun i hi => (Finset.mem_Icc.1 hi).1
  refine (Nat.le_of_dvd hpos (lcmUpTo_dvd_prod n)).trans ?_
  have := Finset.prod_le_pow_card (Finset.Icc 1 n) (fun i => i) n
    (fun i hi => (Finset.mem_Icc.1 hi).2)
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at this

lemma prime_le_of_dvd_lcmUpTo {n p : ℕ} (hp : p.Prime) (h : p ∣ lcmUpTo (n : ℝ)) : p ≤ n := by
  have h2 := h.trans (lcmUpTo_dvd_prod n)
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h2
  have := Finset.mem_Icc.1 hi
  exact (Nat.le_of_dvd (by omega) hpi).trans this.2

lemma primorialR_natCast (P : ℕ) : primorialR (P : ℝ) = primorial P := by
  unfold primorialR
  rw [Nat.floor_natCast]

/-! ## Integers coprime to `P#` (complete periods) -/

lemma coprime_period (Q : ℕ) :
    ∀ N, N + Q ∈ {n : ℕ | Nat.Coprime n Q} ↔ N ∈ {n : ℕ | Nat.Coprime n Q} := by
  intro N
  simp only [Set.mem_setOf_eq]
  exact Nat.coprime_add_self_left

lemma cnt_coprime_period (hD : Notation_Delta_density) {P : ℕ} (hP : 1 ≤ P) :
    (cnt {n : ℕ | Nat.Coprime n (primorial P)} (primorial P : ℝ) : ℝ) =
      Delta P * primorial P := by
  have hQ : 0 < primorial P := primorial_pos P
  have h1 := hasDens_of_periodic hQ (coprime_period (primorial P))
  have h2 := (hD (P : ℝ) (by exact_mod_cast hP)).2
  rw [primorialR_natCast] at h2
  have h3 := h1.unique h2
  have hQR : (0 : ℝ) < primorial P := by exact_mod_cast hQ
  rw [div_eq_iff hQR.ne'] at h3
  exact h3

lemma abs_cnt_coprime_sub_le (hD : Notation_Delta_density) {P : ℕ} (hP : 1 ≤ P) {Y : ℝ}
    (hY : 0 ≤ Y) :
    |(cnt {n : ℕ | Nat.Coprime n (primorial P)} Y : ℝ) - Delta P * Y| ≤
      Delta P * primorial P := by
  have hQ : 0 < primorial P := primorial_pos P
  have h := abs_cnt_sub_le_of_periodic hQ (coprime_period (primorial P)) hY
  rw [cnt_coprime_period hD hP] at h
  have hQR : (primorial P : ℝ) ≠ 0 := by positivity
  have e : Delta P * (primorial P : ℝ) * Y / primorial P = Delta P * Y := by
    field_simp
  rw [e] at h
  exact h

open Classical in
lemma cntHalf_add (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) : cntHalf S X + cnt S (X / 2) = cnt S X := by
  unfold cntHalf cnt
  have hle : ⌊X / 2⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor (by linarith)
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext N
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨by omega, h2⟩, h3⟩
      · exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : N ≤ ⌊X / 2⌋₊
      · exact Or.inr ⟨⟨h1, h⟩, h3⟩
      · exact Or.inl ⟨⟨by omega, h2⟩, h3⟩
  · rw [Finset.disjoint_left]
    intro N h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at h1 h2
    omega

lemma abs_cntHalf_coprime (hD : Notation_Delta_density) {P : ℕ} (hP : 1 ≤ P) {X : ℝ}
    (hX : 0 ≤ X) :
    |(cntHalf {N : ℕ | Nat.Coprime N (primorial P)} X : ℝ) - X / 2 * Delta P| ≤
      2 * (primorial P : ℝ) := by
  have h1 := abs_cnt_coprime_sub_le hD hP hX
  have h2 := abs_cnt_coprime_sub_le hD hP (show 0 ≤ X / 2 by linarith)
  have hadd := congrArg (Nat.cast : ℕ → ℝ) (cntHalf_add {N : ℕ | Nat.Coprime N (primorial P)} hX)
  push_cast at hadd
  have hΔ := Delta_le_one (P : ℝ)
  have hΔ0 := Delta_nonneg (P : ℝ)
  have hQ : (0 : ℝ) ≤ primorial P := by positivity
  have hDQ : Delta P * (primorial P : ℝ) ≤ primorial P := by nlinarith
  rw [abs_le] at h1 h2 ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  constructor <;> linarith

/-! ## `P#` and `Λ(F)` are `X^{o(1)}` -/

lemma poly_le_exp (A B : ℝ) : ∀ᶠ u : ℝ in atTop, A + B * u ^ 2 + u ≤ Real.exp u / 2 := by
  filter_upwards [eventually_ge_atTop (12 * (|A| + |B| + 1) + 1)] with u hu
  have hA0 := abs_nonneg A
  have hB0 := abs_nonneg B
  have hu1 : 1 ≤ u := by linarith
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have h3 : u ^ 3 / 6 ≤ Real.exp u := by
    calc u ^ 3 / 6 = u ^ 3 / ((Nat.factorial 3 : ℕ) : ℝ) := by norm_num [Nat.factorial]
      _ ≤ Real.exp u := Real.pow_div_factorial_le_exp u (by linarith) 3
  have hA : A ≤ |A| * u ^ 2 :=
    le_trans (le_abs_self A) (le_mul_of_one_le_right hA0 (by nlinarith))
  have hB : B * u ^ 2 ≤ |B| * u ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg u)
  have hk : |A| + |B| + 1 ≤ u / 12 := by linarith
  have hbig : (|A| + |B| + 1) * u ^ 2 ≤ u / 12 * u ^ 2 :=
    mul_le_mul_of_nonneg_right hk (sq_nonneg u)
  have e : u / 12 * u ^ 2 = u ^ 3 / 12 := by ring
  linarith

/-- `K (4P)^P log₃ X ≤ √X` for all large `X`. -/
lemma eventually_small {ρ : ℝ} (hρ : 0 < ρ) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop, K * (4 * (subP ρ X : ℝ)) ^ (subP ρ X) * logIt 3 X ≤ Real.sqrt X := by
  filter_upwards [tendsto_logIt_two.eventually (poly_le_exp (Real.log (K + 1)) (4 * ρ ^ 2)),
    eventually_subP_ge hρ 1, tendsto_logIt_three.eventually_ge_atTop 1,
    tendsto_logIt_two.eventually_gt_atTop 0, tendsto_logIt_one.eventually_gt_atTop 0,
    eventually_gt_atTop 0] with X hpoly hP1 h3 h2 h1 hX0
  have hPR : (1 : ℝ) ≤ subP ρ X := by exact_mod_cast hP1
  have hPu : (subP ρ X : ℝ) ≤ ρ * logIt 2 X := by
    have hfl : (subP ρ X : ℝ) ≤ ρ * logIt 2 X / logIt 3 X := Nat.floor_le (by positivity)
    exact hfl.trans (div_le_self (by positivity) h3)
  have h4P : 0 < 4 * (subP ρ X : ℝ) := by linarith
  have hlog4P : Real.log (4 * (subP ρ X : ℝ)) ≤ 4 * ρ * logIt 2 X :=
    (Real.log_le_self h4P.le).trans (by linarith)
  have hlog4P0 : 0 ≤ Real.log (4 * (subP ρ X : ℝ)) := Real.log_nonneg (by linarith)
  have hpow : (4 * (subP ρ X : ℝ)) ^ (subP ρ X) =
      Real.exp ((subP ρ X : ℝ) * Real.log (4 * (subP ρ X : ℝ))) := by
    rw [Real.exp_nat_mul, Real.exp_log h4P]
  have hPlog : (subP ρ X : ℝ) * Real.log (4 * (subP ρ X : ℝ)) ≤
      4 * ρ ^ 2 * logIt 2 X ^ 2 := by
    calc (subP ρ X : ℝ) * Real.log (4 * (subP ρ X : ℝ))
        ≤ (ρ * logIt 2 X) * (4 * ρ * logIt 2 X) := mul_le_mul hPu hlog4P hlog4P0 (by positivity)
      _ = 4 * ρ ^ 2 * logIt 2 X ^ 2 := by ring
  have h3u : logIt 3 X ≤ Real.exp (logIt 2 X) := by
    have := Real.add_one_le_exp (logIt 2 X)
    have h' : logIt 3 X ≤ logIt 2 X := Real.log_le_self h2.le
    linarith
  have hK1 : 0 < K + 1 := by linarith
  have hsqrt : Real.sqrt X = Real.exp (Real.exp (logIt 2 X) / 2) := by
    rw [logIt_two, Real.exp_log h1, logIt_one, ← Real.log_sqrt hX0.le,
      Real.exp_log (Real.sqrt_pos.2 hX0)]
  calc K * (4 * (subP ρ X : ℝ)) ^ (subP ρ X) * logIt 3 X
      ≤ (K + 1) * Real.exp ((subP ρ X : ℝ) * Real.log (4 * (subP ρ X : ℝ))) *
          Real.exp (logIt 2 X) := by
        rw [hpow]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) h3u
          (by linarith) (by positivity)
    _ ≤ Real.exp (Real.log (K + 1)) * Real.exp (4 * ρ ^ 2 * logIt 2 X ^ 2) *
          Real.exp (logIt 2 X) := by
        rw [Real.exp_log hK1]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hPlog) hK1.le
    _ = Real.exp (Real.log (K + 1) + 4 * ρ ^ 2 * logIt 2 X ^ 2 + logIt 2 X) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (Real.exp (logIt 2 X) / 2) := Real.exp_le_exp.2 hpoly
    _ = Real.sqrt X := hsqrt.symm

lemma primorial_le_four_mul_pow (P : ℕ) (hP : 1 ≤ P) :
    (primorial P : ℝ) ≤ (4 * (P : ℝ)) ^ P := by
  have h1 : (primorial P : ℝ) ≤ (4 : ℝ) ^ P := by exact_mod_cast primorial_le_four_pow P
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  exact h1.trans (pow_le_pow_left₀ (by norm_num) (by linarith) P)

lemma primorial_mul_lcm_le (P F L : ℕ) (hP : 1 ≤ P) (hFP : F ≤ P) (hL : L ∣ lcmUpTo (F : ℝ)) :
    (primorial P : ℝ) * L ≤ (4 * (P : ℝ)) ^ P := by
  have hL1 : L ≤ F ^ F := (Nat.le_of_dvd (lcmUpTo_pos _) hL).trans (lcmUpTo_le_pow F)
  have hL2 : F ^ F ≤ P ^ P :=
    (Nat.pow_le_pow_left hFP F).trans (Nat.pow_le_pow_right hP hFP)
  have hQ : primorial P ≤ 4 ^ P := primorial_le_four_pow P
  have hprod : primorial P * L ≤ 4 ^ P * P ^ P := Nat.mul_le_mul hQ (hL1.trans hL2)
  rw [← mul_pow] at hprod
  exact_mod_cast hprod

/-! ## `eq:sharp-rough-target-count` -/

theorem sharpRoughTargetCount (hD : Notation_Delta_density) (hM3 : Std_Mertens3) :
    Eq_SharpRoughTargetCount := by
  have hg0 : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  refine ⟨2, Real.exp (-eulerGamma) / 16, 4 * Real.exp (-eulerGamma) + 1, by positivity,
    by positivity, ?_⟩
  intro ρ hρ
  have hM : Tendsto (fun X : ℝ => Delta (subP ρ X) * Real.log (subP ρ X)) atTop
      (𝓝 (Real.exp (-eulerGamma))) := hM3.comp (tendsto_subP hρ)
  have ev : ∀ᶠ X : ℝ in atTop,
      Delta (subP ρ X) * Real.log (subP ρ X) ∈
        Set.Ioo (Real.exp (-eulerGamma) / 2) (2 * Real.exp (-eulerGamma)) ∧
      subJ ρ X / logIt 3 X ∈ Set.Ioo (1 / 2 : ℝ) 2 ∧
      (32 / Real.exp (-eulerGamma) + 2) * (4 * (subP ρ X : ℝ)) ^ (subP ρ X) * logIt 3 X ≤
        Real.sqrt X ∧
      1 ≤ subP ρ X ∧ 0 < logIt 3 X ∧ 1 ≤ X ∧ 0 < subJ ρ X := by
    filter_upwards [hM.eventually (Ioo_mem_nhds (a := Real.exp (-eulerGamma) / 2)
        (b := 2 * Real.exp (-eulerGamma)) (by linarith) (by linarith)),
      (tendsto_subJ_div hρ).eventually (Ioo_mem_nhds (a := (1 / 2 : ℝ)) (b := 2)
        (by norm_num) (by norm_num)),
      eventually_small hρ (32 / Real.exp (-eulerGamma) + 2) (by positivity),
      eventually_subP_ge hρ 1, tendsto_logIt_three.eventually_gt_atTop 0,
      eventually_ge_atTop 1, (tendsto_subJ hρ).eventually_gt_atTop 0]
      with X a1 a2 a3 a4 a5 a6 a7
    exact ⟨a1, a2, a3, a4, a5, a6, a7⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ev
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨⟨hDJ1, hDJ2⟩, ⟨hJa1, hJa2⟩, hsmall, hP1, ha0, hX1, hJ0⟩ := hX₀ X hX
  have hX0 : 0 ≤ X := by linarith
  have habs := abs_cntHalf_coprime hD hP1 hX0
  refine ⟨habs, ?_, ?_⟩
  all_goals
    set g := Real.exp (-eulerGamma) with hg
    set D := Delta (subP ρ X) with hDdef
    set J := subJ ρ X with hJdef
    set a := logIt 3 X with hadef
    set Q := (primorial (subP ρ X) : ℝ) with hQdef
    set cH := (cntHalf {N : ℕ | Nat.Coprime N (primorial (subP ρ X))} X : ℝ) with hcH
    have hD0 : 0 ≤ D := Delta_nonneg _
    have hQ0 : 0 ≤ Q := by positivity
    have hlogJ : Real.log (subP ρ X) = J := rfl
    rw [hlogJ] at hDJ1 hDJ2
    have hJa1' : a / 2 < J := by
      rw [lt_div_iff₀ ha0] at hJa1
      linarith
    have hJa2' : J < 2 * a := by
      rw [div_lt_iff₀ ha0] at hJa2
      linarith
    have hDa1 : g / 4 < D * a := by
      have : D * J ≤ D * (2 * a) := mul_le_mul_of_nonneg_left hJa2'.le hD0
      linarith
    have hDa2 : D * a < 4 * g := by
      have : D * (a / 2) ≤ D * J := mul_le_mul_of_nonneg_left hJa1'.le hD0
      linarith
    have hQP : Q ≤ (4 * (subP ρ X : ℝ)) ^ (subP ρ X) := primorial_le_four_mul_pow _ hP1
    have hsq : Real.sqrt X ≤ X := by
      rw [Real.sqrt_le_left hX0]
      nlinarith
    have hKQa : (32 / g + 2) * Q * a ≤ X := by
      have hK : 0 ≤ 32 / g + 2 := by positivity
      calc (32 / g + 2) * Q * a ≤ (32 / g + 2) * (4 * (subP ρ X : ℝ)) ^ (subP ρ X) * a :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQP hK) ha0.le
        _ ≤ Real.sqrt X := hsmall
        _ ≤ X := hsq
    have hQa0 : 0 ≤ Q * a := mul_nonneg hQ0 ha0.le
    have h32 : 32 * (Q * a) ≤ g * X := by
      have h1 : 32 / g * (Q * a) ≤ X := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left h1 hg0.le
      have e : g * (32 / g * (Q * a)) = 32 * (Q * a) := by
        field_simp
      linarith
    have h2Qa : 2 * (Q * a) ≤ X := by
      have : 0 ≤ 32 / g * (Q * a) := by positivity
      linarith
    have hgX : 0 ≤ g * X := by positivity
    rw [abs_le] at habs
    obtain ⟨hab1, hab2⟩ := habs
  · -- lower bound
    rw [div_le_iff₀ ha0]
    have hmul : (X / 2 * D - 2 * Q) * a ≤ cH * a := mul_le_mul_of_nonneg_right (by linarith) ha0.le
    have hXDa : X / 2 * (g / 4) ≤ X / 2 * (D * a) :=
      mul_le_mul_of_nonneg_left hDa1.le (by linarith)
    linarith
  · -- upper bound
    rw [le_div_iff₀ ha0]
    have hmul : cH * a ≤ (X / 2 * D + 2 * Q) * a := mul_le_mul_of_nonneg_right (by linarith) ha0.le
    have hXDa : X / 2 * (D * a) ≤ X / 2 * (4 * g) :=
      mul_le_mul_of_nonneg_left hDa2.le (by linarith)
    linarith

/-! ## `Claim_SubexpCoprimeCount` -/

theorem coprimeCount (hD : Notation_Delta_density) : UpperTails.Claim_SubexpCoprimeCount := by
  intro ρ hρ ε hε hε1
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ((eventually_small hρ 1 (by norm_num)).and
    ((eventually_subP_ge hρ 2).and ((tendsto_logIt_three.eventually_ge_atTop 1).and
      (eventually_ge_atTop 1))))
  refine ⟨X₀, fun X hX L hL => ?_⟩
  obtain ⟨hs, hP2, h3, hX1⟩ := hX₀ X hX
  have hX0 : 0 ≤ X := by linarith
  have hFP : subF ρ X < subP ρ X := subF_lt_subP hP2
  have hLpos : 0 < L := Nat.pos_of_dvd_of_pos hL (lcmUpTo_pos _)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hQL := primorial_mul_lcm_le (subP ρ X) (subF ρ X) L (by omega) hFP.le hL
  have hsq : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_left hX0]
    nlinarith
  have hPow : (4 * (subP ρ X : ℝ)) ^ (subP ρ X) ≤ Real.sqrt X := by
    have hpow0 : 0 ≤ (4 * (subP ρ X : ℝ)) ^ (subP ρ X) := by positivity
    nlinarith
  have ht1 : 1 ≤ subT ε ρ X := Real.one_le_exp (mul_nonneg (by linarith) (subW_nonneg _ _))
  have hXt : X ≤ subT ε ρ X * X := by nlinarith
  have hP1 : 1 ≤ subP ρ X := by omega
  have hY : (primorial (subP ρ X) : ℝ) ≤ subT ε ρ X * X / L := by
    rw [le_div_iff₀ hLR]
    linarith
  refine ⟨hY, ?_⟩
  have hY0 : 0 ≤ subT ε ρ X * X / L := by positivity
  have habs := abs_cnt_coprime_sub_le hD hP1 hY0
  rw [abs_le] at habs
  have hmul := mul_le_mul_of_nonneg_left hY (Delta_nonneg (subP ρ X))
  have e : 2 * subT ε ρ X * X * Delta (subP ρ X) / L =
      2 * (Delta (subP ρ X) * (subT ε ρ X * X / L)) := by ring
  rw [e]
  linarith

/-! ## `eq:moving-kernel-lower-bound` -/

lemma tendsto_subF {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (fun X : ℝ => (subF ρ X : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop (Eventually.of_forall (half_le_subF ρ))
    ((Real.tendsto_exp_atTop.comp (tendsto_subW hρ)).atTop_div_const two_pos)

theorem movingKernelLowerBound (hWS : UpperTails.Claim_SubexpWitnessStructure)
    (hF : UpperTails.Claim_SubexpFltP) (hM3 : Std_Mertens3) : Eq_MovingKernelLowerBound := by
  have hg0 : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1
    (hM3.eventually (lt_mem_nhds
      (by linarith : Real.exp (-eulerGamma) / 2 < Real.exp (-eulerGamma))))
  refine ⟨2 / Real.exp (-eulerGamma), by positivity, fun ρ hρ => ?_⟩
  obtain ⟨X₁, hX₁⟩ := hF ρ hρ
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (((tendsto_subF hρ).eventually_ge_atTop (max y₀ 2)).and
    (eventually_ge_atTop X₁))
  refine ⟨X₀, fun X hX N e d he2 heF hd hN hR hgood => ?_⟩
  obtain ⟨hFy, hXX1⟩ := hX₀ X hX
  obtain ⟨_, _, _, _, _, hMΛ, hPC, hCσ⟩ :=
    hWS (subP ρ X) (subF ρ X) N e d (hX₁ X hXX1) he2 heF hd hN hR hgood
  have hM0 : Mlcm e d ≠ 0 := (Mlcm_pos e d).ne'
  have hpf : ∀ p ∈ (Mlcm e d).primeFactors, p ≤ subF ρ X := fun p hp =>
    prime_le_of_dvd_lcmUpTo (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hMΛ)
  have hsd := sig_mul_Delta_le hM0 hpf
  have hFy0 : y₀ ≤ (subF ρ X : ℝ) := le_trans (le_max_left _ _) hFy
  have hF2 : (2 : ℝ) ≤ (subF ρ X : ℝ) := le_trans (le_max_right _ _) hFy
  have hmert := hy₀ (subF ρ X : ℝ) hFy0
  have hlogF : Real.log (subF ρ X : ℝ) ≤ subW ρ X := by
    have := Real.log_le_log (by linarith) (subF_le ρ X)
    rwa [Real.log_exp] at this
  have hlogF0 : 0 < Real.log (subF ρ X : ℝ) := Real.log_pos (by linarith)
  have hW0 : 0 < subW ρ X := lt_of_lt_of_le hlogF0 hlogF
  have hΔ0 := Delta_pos (subF ρ X : ℝ)
  have hkey : 1 ≤ Delta (subF ρ X) * (2 / Real.exp (-eulerGamma) * subW ρ X) := by
    have h1 : Delta (subF ρ X) * Real.log (subF ρ X) ≤ Delta (subF ρ X) * subW ρ X :=
      mul_le_mul_of_nonneg_left hlogF hΔ0.le
    have e : Delta (subF ρ X) * (2 / Real.exp (-eulerGamma) * subW ρ X) =
        2 / Real.exp (-eulerGamma) * (Delta (subF ρ X) * subW ρ X) := by ring
    rw [e, div_mul_eq_mul_div, le_div_iff₀ hg0]
    linarith
  have hPC' : (subP ρ X : ℝ) < sig (Mlcm e d) := by
    exact_mod_cast lt_of_lt_of_le hPC hCσ
  have hsig0 : (0 : ℝ) ≤ sig (Mlcm e d) := Nat.cast_nonneg _
  have hchain : (subP ρ X : ℝ) < Mlcm e d * (2 / Real.exp (-eulerGamma) * subW ρ X) := by
    calc (subP ρ X : ℝ) < sig (Mlcm e d) := hPC'
      _ ≤ sig (Mlcm e d) * (Delta (subF ρ X) * (2 / Real.exp (-eulerGamma) * subW ρ X)) :=
          le_mul_of_one_le_right hsig0 hkey
      _ = ((sig (Mlcm e d) : ℝ) * Delta (subF ρ X)) * (2 / Real.exp (-eulerGamma) * subW ρ X) := by
          ring
      _ ≤ Mlcm e d * (2 / Real.exp (-eulerGamma) * subW ρ X) :=
          mul_le_mul_of_nonneg_right hsd (by positivity)
  rw [div_lt_iff₀ (by positivity)]
  linarith


/-! ## The low-cofactor witnesses (`Claim_SubexpLowCofactorSum`, `Claim_SubexpLowCofactor`) -/

open Classical in
/-- Counting by fibres of `f`: if every point of `A` maps into `Λs`, each fibre over `L` has at
most `τ(L) c(L)` points and `c(L) ≤ B/L`, then `#A ≤ B ∑_{L ∈ Λs} τ(L)/L`. -/
lemma card_le_sum_fiber {A : Finset (ℕ × ℕ)} {Λs : Finset ℕ} {B : ℝ}
    (f : ℕ × ℕ → ℕ) (c : ℕ → ℕ) (hmaps : ∀ q ∈ A, f q ∈ Λs)
    (hfib : ∀ L ∈ Λs, (A.filter (fun q => f q = L)).card ≤ L.divisors.card * c L)
    (hU : ∀ L ∈ Λs, (c L : ℝ) ≤ B / L) :
    (A.card : ℝ) ≤ B * ∑ L ∈ Λs, (L.divisors.card : ℝ) / L := by
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro L hL
  calc ((A.filter (fun q => f q = L)).card : ℝ) ≤ (L.divisors.card : ℝ) * (c L : ℝ) := by
        exact_mod_cast hfib L hL
    _ ≤ (L.divisors.card : ℝ) * (B / L) :=
        mul_le_mul_of_nonneg_left (hU L hL) (Nat.cast_nonneg _)
    _ = B * ((L.divisors.card : ℝ) / L) := by ring

open Classical in
/-- An injection of a finset of pairs into `divisors(L) × {1 ≤ u ≤ Y, u ∈ S}`. -/
lemma fiber_card_le (S : Set ℕ) (Y : ℝ) (L : ℕ) (B : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℕ × ℕ)
    (hmaps : ∀ q ∈ B, (g q).1 ∈ L.divisors ∧ 1 ≤ (g q).2 ∧ (g q).2 ≤ ⌊Y⌋₊ ∧ (g q).2 ∈ S)
    (hinj : ∀ q ∈ B, ∀ q' ∈ B, g q = g q' → q = q') :
    B.card ≤ L.divisors.card * cnt S Y := by
  unfold cnt
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn g
  · intro q hq
    have h := hmaps q hq
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩
  · intro q hq q' hq' h
    exact hinj q hq q' hq' h

open Classical in
theorem lowCofactorSum (hWS : UpperTails.Claim_SubexpWitnessStructure)
    (hMK : Eq_MovingKernelLowerBound) (hCC : UpperTails.Claim_SubexpCoprimeCount)
    (hF : UpperTails.Claim_SubexpFltP) : UpperTails.Claim_SubexpLowCofactorSum := by
  obtain ⟨C₀, hC₀, hMK'⟩ := hMK
  refine ⟨C₀, hC₀, fun ρ hρ ε hε hε1 => ?_⟩
  obtain ⟨X₁, hX₁⟩ := hMK' ρ hρ
  obtain ⟨X₂, hX₂⟩ := hCC ρ hρ ε hε hε1
  obtain ⟨X₃, hX₃⟩ := hF ρ hρ
  refine ⟨max (max X₁ X₂) (max X₃ 0), fun X hX => ?_⟩
  have hXX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXX3 : X₃ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX0 : 0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hΔ0 := Delta_nonneg (subP ρ X : ℝ)
  have hFP := hX₃ X hXX3
  unfold lowWitness Skernel
  refine card_le_sum_fiber (fun q => Mlcm q.1 q.2)
    (fun L => cnt {u : ℕ | Nat.Coprime u (primorial (subP ρ X))} (subT ε ρ X * X / L)) ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨he2, heF⟩, ⟨hd1, _⟩⟩, _, hR, hgood⟩ := hq
    obtain ⟨_, _, _, _, _, hMΛ, _, _⟩ :=
      hWS (subP ρ X) (subF ρ X) (F q.1 q.2) q.1 q.2 hFP he2 heF hd1 rfl hR hgood
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hMΛ, (lcmUpTo_pos _).ne'⟩, hX₁ X hXX1 (F q.1 q.2) q.1 q.2 he2 heF hd1 rfl hR hgood⟩
  · intro L hL
    have hL0 : L ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pos_of_mem_divisors (Finset.mem_filter.1 hL).1)
    have hLR : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
    apply fiber_card_le _ _ L _ (fun q => (q.1, q.1 * q.2 / L))
    · intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqA, hqL⟩ := hq
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hqA
      obtain ⟨⟨⟨he2, heF⟩, ⟨hd1, _⟩⟩, hed, hR, hgood⟩ := hqA
      obtain ⟨hMdvd, _, hucop, _, heM, _, _, _⟩ :=
        hWS (subP ρ X) (subF ρ X) (F q.1 q.2) q.1 q.2 hFP he2 heF hd1 rfl hR hgood
      rw [hqL] at hMdvd hucop heM
      have hed0 : 0 < q.1 * q.2 := Nat.mul_pos (by omega) hd1
      refine ⟨Nat.mem_divisors.2 ⟨heM, hL0⟩, Nat.div_pos (Nat.le_of_dvd hed0 hMdvd)
        (Nat.pos_of_ne_zero hL0), ?_, hucop⟩
      apply Nat.le_floor
      rw [Nat.cast_div hMdvd hLR.ne']
      exact div_le_div_of_nonneg_right hed hLR.le
    · intro q hq q' hq' h
      rw [Finset.mem_filter] at hq hq'
      obtain ⟨hqA, hqL⟩ := hq
      obtain ⟨hqA', hqL'⟩ := hq'
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hqA hqA'
      have hd1 : L ∣ q.1 * q.2 := hqL ▸ Finset.lcm_dvd fun _ hj => (mem_Dset.1 hj).2.2
      have hd2 : L ∣ q'.1 * q'.2 := hqL' ▸ Finset.lcm_dvd fun _ hj => (mem_Dset.1 hj).2.2
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h3 : q.1 * q.2 = q'.1 * q'.2 := (Nat.div_left_inj hd1 hd2).1 h2
      rw [h1] at h3
      have h4 : q.2 = q'.2 := Nat.eq_of_mul_eq_mul_left (by omega) h3
      exact Prod.ext h1 h4
  · intro L hL
    have hLd : L ∣ lcmUpTo (subF ρ X : ℝ) := Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hL).1
    exact (hX₂ X hXX2 L hLd).2

theorem lowCofactor (hLS : UpperTails.Claim_SubexpLowCofactorSum) (hMT : Eq_MovingKernelTail) :
    UpperTails.Claim_SubexpLowCofactor := by
  intro ρ hρ ε hε hε1 η hη
  obtain ⟨C₀, hC₀, hLS'⟩ := hLS
  obtain ⟨X₁, hX₁⟩ := hLS' ρ hρ ε hε hε1
  obtain ⟨J₀, hJ₀⟩ := hMT C₀ hC₀ (η / 2) (by positivity)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (((tendsto_subJ hρ).eventually_ge_atTop J₀).and
    (((tendsto_subW hρ).eventually_ge_atTop (2 * Real.log 2 / η)).and
      ((eventually_subP_ge hρ 1).and ((eventually_ge_atTop X₁).and (eventually_ge_atTop 0)))))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hJ, hW, hP1, hXX1, hX0⟩ := hX₀ X hX
  have hPR : (0 : ℝ) < subP ρ X := by
    have : (1 : ℝ) ≤ subP ρ X := by exact_mod_cast hP1
    linarith
  have hk := hJ₀ (subJ ρ X) hJ
  have hexpJ : Real.exp (subJ ρ X) = subP ρ X := Real.exp_log hPR
  rw [hexpJ] at hk
  have hk' : Skernel (subF ρ X) ((subP ρ X : ℝ) / (C₀ * subW ρ X)) ≤
      Real.exp (-(subW ρ X) + η / 2 * subW ρ X) := hk
  have hls := hX₁ X hXX1
  have hΔ0 := Delta_nonneg (subP ρ X : ℝ)
  have hXΔ : 0 ≤ X * Delta (subP ρ X) := mul_nonneg hX0 hΔ0
  have e1 : subT ε ρ X * Real.exp (-(subW ρ X) + η / 2 * subW ρ X) =
      Real.exp (-(ε * subW ρ X) + η / 2 * subW ρ X) := by
    unfold subT
    rw [← Real.exp_add]
    congr 1
    ring
  have hlog2 : Real.log 2 ≤ η / 2 * subW ρ X := by
    rw [div_le_iff₀ hη] at hW
    linarith
  have h2' : (2 : ℝ) ≤ Real.exp (η / 2 * subW ρ X) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp (η / 2 * subW ρ X) := Real.exp_le_exp.2 hlog2
  have h2 : 2 * Real.exp (-(ε * subW ρ X) + η / 2 * subW ρ X) ≤
      Real.exp (-(ε * subW ρ X) + η * subW ρ X) := by
    have e2 : Real.exp (-(ε * subW ρ X) + η * subW ρ X) =
        Real.exp (-(ε * subW ρ X) + η / 2 * subW ρ X) * Real.exp (η / 2 * subW ρ X) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e2, mul_comm]
    exact mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
  calc (lowWitness ε ρ X : ℝ)
      ≤ 2 * subT ε ρ X * X * Delta (subP ρ X) *
          Skernel (subF ρ X) ((subP ρ X : ℝ) / (C₀ * subW ρ X)) := hls
    _ ≤ 2 * subT ε ρ X * X * Delta (subP ρ X) *
          Real.exp (-(subW ρ X) + η / 2 * subW ρ X) :=
        mul_le_mul_of_nonneg_left hk'
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hX0) hΔ0)
    _ = X * Delta (subP ρ X) *
          (2 * (subT ε ρ X * Real.exp (-(subW ρ X) + η / 2 * subW ρ X))) := by ring
    _ = X * Delta (subP ρ X) * (2 * Real.exp (-(ε * subW ρ X) + η / 2 * subW ρ X)) := by
        rw [e1]
    _ ≤ X * Delta (subP ρ X) * Real.exp (-(ε * subW ρ X) + η * subW ρ X) :=
        mul_le_mul_of_nonneg_left h2 hXΔ

/-! ## `Claim_SubexpLargeCofactor` -/

theorem largeCofactor (hM3 : Std_Mertens3) : UpperTails.Claim_SubexpLargeCofactor := by
  intro ρ hρ ε hε hε1 k hk hkε η hη
  have hg0 : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  set δ : ℝ := ((k : ℝ) + 1) * ε - 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set c : ℝ := ((k : ℝ) - 1) * Real.log 2 with hc
  have hM : Tendsto (fun X : ℝ => Delta (subP ρ X) * Real.log (subP ρ X)) atTop
      (𝓝 (Real.exp (-eulerGamma))) := hM3.comp (tendsto_subP hρ)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    ((hM.eventually (lt_mem_nhds (by linarith : Real.exp (-eulerGamma) / 2 <
        Real.exp (-eulerGamma)))).and
      (((tendsto_subJ hρ).eventually_ge_atTop (Real.exp 2)).and
        ((tendsto_subJ hρ).eventually_ge_atTop
          (48 * Real.exp c / (η * Real.exp (-eulerGamma) * δ ^ 4)))))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hmert, hJe, hJbig⟩ := hX₀ X hX
  have hlogJ : Real.log (subP ρ X) = subJ ρ X := rfl
  rw [hlogJ] at hmert
  have hJ0 : 0 < subJ ρ X := lt_of_lt_of_le (Real.exp_pos 2) hJe
  have hΔ0 := Delta_nonneg (subP ρ X : ℝ)
  have hW : Real.sqrt (subJ ρ X) ≤ subW ρ X := sqrt_le_Wmov hJe
  have hW0 := subW_nonneg ρ X
  -- `t^{k+1} F^{1-k} ≤ exp(-δ W + c)`
  have hexpW : 1 ≤ Real.exp (subW ρ X) := Real.one_le_exp hW0
  have hFlo : 0 < Real.exp (subW ρ X) / 2 := by positivity
  have hF1 : (subF ρ X : ℝ) ^ (1 - (k : ℝ)) ≤ (Real.exp (subW ρ X) / 2) ^ (1 - (k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hFlo (half_le_subF ρ X)
      (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith)
  have hF2 : (Real.exp (subW ρ X) / 2) ^ (1 - (k : ℝ)) =
      Real.exp ((subW ρ X - Real.log 2) * (1 - (k : ℝ))) := by
    rw [Real.rpow_def_of_pos hFlo, Real.log_div (Real.exp_pos _).ne' two_ne_zero, Real.log_exp]
  have ht : subT ε ρ X ^ (k + 1) = Real.exp (((k : ℝ) + 1) * ((1 - ε) * subW ρ X)) := by
    unfold subT
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hprod : subT ε ρ X ^ (k + 1) * (subF ρ X : ℝ) ^ (1 - (k : ℝ)) ≤
      Real.exp (-(δ * subW ρ X) + c) := by
    calc subT ε ρ X ^ (k + 1) * (subF ρ X : ℝ) ^ (1 - (k : ℝ))
        ≤ subT ε ρ X ^ (k + 1) * (Real.exp (subW ρ X) / 2) ^ (1 - (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hF1
            (pow_nonneg (le_of_lt (Real.exp_pos ((1 - ε) * subW ρ X))) _)
      _ = Real.exp (((k : ℝ) + 1) * ((1 - ε) * subW ρ X) +
            (subW ρ X - Real.log 2) * (1 - (k : ℝ))) := by
          rw [ht, hF2, ← Real.exp_add]
      _ = Real.exp (-(δ * subW ρ X) + c) := by
          congr 1
          rw [hδ, hc]
          ring
  -- `exp(δ W) · η Δ ≥ exp c`
  have hsqJ : Real.sqrt (subJ ρ X) ^ 2 = subJ ρ X := Real.sq_sqrt hJ0.le
  have hexpδ : δ ^ 4 * subJ ρ X ^ 2 / 24 ≤ Real.exp (δ * subW ρ X) := by
    have h1 := exp_ge_pow_four (show 0 ≤ δ * Real.sqrt (subJ ρ X) by positivity)
    have h2 : Real.exp (δ * Real.sqrt (subJ ρ X)) ≤ Real.exp (δ * subW ρ X) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hW hδ0.le)
    have e : (δ * Real.sqrt (subJ ρ X)) ^ 4 = δ ^ 4 * subJ ρ X ^ 2 := by
      calc (δ * Real.sqrt (subJ ρ X)) ^ 4 = δ ^ 4 * (Real.sqrt (subJ ρ X) ^ 2) ^ 2 := by ring
        _ = δ ^ 4 * subJ ρ X ^ 2 := by rw [hsqJ]
    rw [e] at h1
    linarith
  have hηΔJ : η * Real.exp (-eulerGamma) / 2 ≤ η * Delta (subP ρ X) * subJ ρ X := by
    have := mul_le_mul_of_nonneg_left hmert.le hη.le
    linarith
  have hJbig' : 48 * Real.exp c ≤ subJ ρ X * (η * Real.exp (-eulerGamma) * δ ^ 4) := by
    rwa [div_le_iff₀ (by positivity)] at hJbig
  have hkey : Real.exp c ≤ Real.exp (δ * subW ρ X) * (η * Delta (subP ρ X)) := by
    have hηΔ : 0 ≤ η * Delta (subP ρ X) := mul_nonneg hη.le hΔ0
    calc Real.exp c ≤ (δ ^ 4 * subJ ρ X / 24) * (η * Real.exp (-eulerGamma) / 2) := by
          nlinarith
      _ ≤ (δ ^ 4 * subJ ρ X / 24) * (η * Delta (subP ρ X) * subJ ρ X) :=
          mul_le_mul_of_nonneg_left hηΔJ (by positivity)
      _ = (δ ^ 4 * subJ ρ X ^ 2 / 24) * (η * Delta (subP ρ X)) := by ring
      _ ≤ Real.exp (δ * subW ρ X) * (η * Delta (subP ρ X)) :=
          mul_le_mul_of_nonneg_right hexpδ hηΔ
  have hfin : Real.exp (-(δ * subW ρ X) + c) ≤ η * Delta (subP ρ X) := by
    have e : Real.exp (-(δ * subW ρ X) + c) = Real.exp c / Real.exp (δ * subW ρ X) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [e, div_le_iff₀ (Real.exp_pos _)]
    linarith
  exact hprod.trans hfin


/-! ## `Δ(P) ≥ 1/P` (elementary) -/

lemma Delta_natCast (n : ℕ) :
    Delta (n : ℝ) = ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  unfold Delta
  rw [Nat.floor_natCast]

lemma Delta_mul_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ Delta (n : ℝ) * n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h : (Finset.range (1 + 1)).filter Nat.Prime = ∅ :=
      Finset.filter_eq_empty_iff.2 fun x hx hp => by
        have := hp.two_le
        rw [Finset.mem_range] at hx
        omega
    rw [Delta_natCast, h, Finset.prod_empty]
    norm_num
  | succ n hn ih =>
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hD0 : 0 ≤ Delta (n : ℝ) := Delta_nonneg _
    rw [Delta_natCast] at ih hD0
    rw [Delta_natCast, Finset.range_add_one, Finset.filter_insert]
    split_ifs with hp
    · rw [Finset.prod_insert (by simp)]
      push_cast
      have e : (1 - 1 / ((n : ℝ) + 1)) *
          (∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) * ((n : ℝ) + 1) =
          (∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) * n := by
        field_simp
        ring
      rw [e]
      exact ih
    · push_cast
      nlinarith

lemma inv_le_Delta (n : ℕ) (hn : 1 ≤ n) : 1 / (n : ℝ) ≤ Delta (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  exact Delta_mul_ge_one n hn

/-! ## `eq:sharp-bad-source-count` -/

open Classical in
lemma cnt_le_sum {ι : Type*} (s : Finset ι) (S : Set ℕ) (A : ι → Set ℕ)
    (h : ∀ n, n ∈ S → ∃ i ∈ s, n ∈ A i) (X : ℝ) :
    cnt S X ≤ ∑ i ∈ s, cnt (A i) X := by
  unfold cnt
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨i, hi, hni⟩ := h n hn.2
  rw [Finset.mem_biUnion]
  exact ⟨i, hi, Finset.mem_filter.2 ⟨hn.1, hni⟩⟩

lemma div_log_mono {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hs := Real.log_le_sub_one_of_pos (div_pos (show 0 < b by linarith) ha0)
  rw [Real.log_div (by linarith) ha0.ne'] at hs
  have hmul : a * (Real.log b - Real.log a) ≤ a * (b / a - 1) :=
    mul_le_mul_of_nonneg_left hs ha0.le
  have e : a * (b / a - 1) = b - a := by
    field_simp
  have hprod : (b - a) * 1 ≤ (b - a) * Real.log a :=
    mul_le_mul_of_nonneg_left hla (by linarith)
  linarith

lemma primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc (Nat.primesLE n).card ≤ (Finset.Icc 1 n).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨hpn, hpp⟩ := Nat.mem_primesLE.1 hp
        rw [Finset.mem_Icc]
        exact ⟨hpp.one_lt.le, hpn⟩
    _ = n := by rw [Nat.card_Icc, Nat.add_sub_cancel]

theorem badSourceCount (hSR : Lem_SigmaRate) : Eq_SharpBadSourceCount := by
  obtain ⟨⟨c₀, hc₀, c₁, hc₁, C, y₀, hodd⟩, ⟨C₂, hB2⟩⟩ := hSR
  refine ⟨c₁, hc₁, max C₂ 0 + max C 0, c₀, hc₀, fun ρ hρ hρ₀ ε hε hε1 => ?_⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (max y₀ 1)).and
    ((tendsto_logIt_two.eventually_ge_atTop (Real.exp 1)).and ((eventually_subP_ge hρ 2).and
      (tendsto_logIt_one.eventually_gt_atTop 0))))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hXy, hX2, hP2, hlX⟩ := hX₀ X hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hXy
  have ht1 : 1 ≤ subT ε ρ X := Real.one_le_exp (mul_nonneg (by linarith) (subW_nonneg _ _))
  have hXY : X ≤ subT ε ρ X * X := by nlinarith
  have hY1 : 1 ≤ subT ε ρ X * X := le_trans hX1 hXY
  have hY0 : 0 ≤ subT ε ρ X * X := by linarith
  have hYy : y₀ ≤ subT ε ρ X * X := le_trans (le_trans (le_max_left _ _) hXy) hXY
  have hl1 : logIt 1 X ≤ logIt 1 (subT ε ρ X * X) := Real.log_le_log (by linarith) hXY
  have hl2 : logIt 2 X ≤ logIt 2 (subT ε ρ X * X) := Real.log_le_log hlX hl1
  have hmono : logIt 2 X / logIt 3 X ≤
      logIt 2 (subT ε ρ X * X) / logIt 3 (subT ε ρ X * X) := div_log_mono hX2 hl2
  have h3X : 1 ≤ logIt 3 X := by
    have := Real.log_le_log (Real.exp_pos 1) hX2
    rwa [Real.log_exp] at this
  have hl2Y : 0 ≤ logIt 2 (subT ε ρ X * X) := by
    have := Real.exp_pos 1
    linarith
  have hPle : (subP ρ X : ℝ) ≤
      c₀ * logIt 2 (subT ε ρ X * X) / logIt 3 (subT ε ρ X * X) := by
    have hfl : (subP ρ X : ℝ) ≤ ρ * logIt 2 X / logIt 3 X := Nat.floor_le (by
      have := Real.exp_pos 1
      have : 0 ≤ logIt 2 X := by linarith
      positivity)
    have hq0 : 0 ≤ logIt 2 X / logIt 3 X := div_nonneg (by linarith [Real.exp_pos 1])
      (by linarith)
    calc (subP ρ X : ℝ) ≤ ρ * logIt 2 X / logIt 3 X := hfl
      _ = ρ * (logIt 2 X / logIt 3 X) := by ring
      _ ≤ c₀ * (logIt 2 (subT ε ρ X * X) / logIt 3 (subT ε ρ X * X)) :=
          mul_le_mul hρ₀ hmono hq0 hc₀.le
      _ = c₀ * logIt 2 (subT ε ρ X * X) / logIt 3 (subT ε ρ X * X) := by ring
  have hPpos : (0 : ℝ) < subP ρ X := by
    have : (2 : ℝ) ≤ subP ρ X := by exact_mod_cast hP2
    linarith
  -- the union bound
  have hsum : cnt (badSrc (subP ρ X)) (subT ε ρ X * X) ≤
      ∑ p ∈ Nat.primesLE (subP ρ X), cnt {m : ℕ | ¬ p ∣ sig m} (subT ε ρ X * X) := by
    refine cnt_le_sum (Nat.primesLE (subP ρ X)) (badSrc (subP ρ X))
      (fun p => {m : ℕ | ¬ p ∣ sig m}) ?_ (subT ε ρ X * X)
    rintro n ⟨p, hp, hpP, hnd⟩
    exact ⟨p, Nat.mem_primesLE.2 ⟨hpP, hp⟩, hnd⟩
  have h2mem : 2 ∈ Nat.primesLE (subP ρ X) := Nat.mem_primesLE.2 ⟨hP2, Nat.prime_two⟩
  rw [← Finset.add_sum_erase _ _ h2mem] at hsum
  have hsumR : (cnt (badSrc (subP ρ X)) (subT ε ρ X * X) : ℝ) ≤
      (cnt {m : ℕ | ¬ 2 ∣ sig m} (subT ε ρ X * X) : ℝ) +
        ∑ p ∈ (Nat.primesLE (subP ρ X)).erase 2,
          (cnt {m : ℕ | ¬ p ∣ sig m} (subT ε ρ X * X) : ℝ) := by
    exact_mod_cast hsum
  have hodd' : ∀ p ∈ (Nat.primesLE (subP ρ X)).erase 2,
      (cnt {m : ℕ | ¬ p ∣ sig m} (subT ε ρ X * X) : ℝ) ≤
        max C 0 * (subT ε ρ X * X) *
          Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))) := by
    intro p hp
    obtain ⟨hp2, hpmem⟩ := Finset.mem_erase.1 hp
    obtain ⟨hpP, hpp⟩ := Nat.mem_primesLE.1 hpmem
    have hp3 : 3 ≤ p := by
      have := hpp.two_le
      omega
    have hpR : (p : ℝ) ≤ subP ρ X := by exact_mod_cast hpP
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hB : (Bq p (subT ε ρ X * X) : ℝ) ≤
        C * (subT ε ρ X * X) * Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / p)) :=
      hodd (subT ε ρ X * X) hYy p hpp hp3 (le_trans hpR hPle)
    have hexp : Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / p)) ≤
        Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (mul_nonneg hc₁.le hl2Y) hp0 hpR
    calc (cnt {m : ℕ | ¬ p ∣ sig m} (subT ε ρ X * X) : ℝ) = (Bq p (subT ε ρ X * X) : ℝ) := rfl
      _ ≤ C * (subT ε ρ X * X) * Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / p)) := hB
      _ ≤ max C 0 * (subT ε ρ X * X) *
            Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0) hexp
            (Real.exp_pos _).le (mul_nonneg (le_max_right _ _) hY0)
  have hcard : (((Nat.primesLE (subP ρ X)).erase 2).card : ℝ) ≤ Nat.primeCounting (subP ρ X) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast Finset.card_erase_le
  have hsumodd : ∑ p ∈ (Nat.primesLE (subP ρ X)).erase 2,
      (cnt {m : ℕ | ¬ p ∣ sig m} (subT ε ρ X * X) : ℝ) ≤
        (Nat.primeCounting (subP ρ X) : ℝ) * (max C 0 * (subT ε ρ X * X) *
          Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ)))) := by
    refine (Finset.sum_le_sum hodd').trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg (le_max_right _ _) hY0)
      (Real.exp_pos _).le)
  have h2 : (cnt {m : ℕ | ¬ 2 ∣ sig m} (subT ε ρ X * X) : ℝ) ≤
      max C₂ 0 * Real.sqrt (subT ε ρ X * X) :=
    (hB2 (subT ε ρ X * X) hY1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hA0 : 0 ≤ max C₂ 0 := le_max_right _ _
  have hB0 : 0 ≤ max C 0 := le_max_right _ _
  have hs0 : 0 ≤ Real.sqrt (subT ε ρ X * X) := Real.sqrt_nonneg _
  have hw0 : 0 ≤ subT ε ρ X * X * (Nat.primeCounting (subP ρ X) : ℝ) *
      Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))) :=
    mul_nonneg (mul_nonneg hY0 (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hAw := mul_nonneg hA0 hw0
  have hBs := mul_nonneg hB0 hs0
  have e : (Nat.primeCounting (subP ρ X) : ℝ) * (max C 0 * (subT ε ρ X * X) *
      Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ)))) =
      max C 0 * (subT ε ρ X * X * (Nat.primeCounting (subP ρ X) : ℝ) *
        Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ)))) := by ring
  have e2 : (max C₂ 0 + max C 0) * (Real.sqrt (subT ε ρ X * X) +
      subT ε ρ X * X * (Nat.primeCounting (subP ρ X) : ℝ) *
        Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ)))) =
      max C₂ 0 * Real.sqrt (subT ε ρ X * X) + max C 0 * (subT ε ρ X * X *
        (Nat.primeCounting (subP ρ X) : ℝ) *
          Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ)))) +
      (max C₂ 0 * (subT ε ρ X * X * (Nat.primeCounting (subP ρ X) : ℝ) *
          Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ)))) +
        max C 0 * Real.sqrt (subT ε ρ X * X)) := by ring
  rw [e2]
  linarith

/-! ## `Claim_SubexpBadPairs` -/

theorem badPairs (hBS : Eq_SharpBadSourceCount) : UpperTails.Claim_SubexpBadPairs := by
  obtain ⟨c₁, hc₁, C, ρ₀, hρ₀, hBS'⟩ := hBS
  refine ⟨min ρ₀ (c₁ / 5), by positivity, fun ρ hρ hρle ε hε hε1 η hη => ?_⟩
  have hρ₀' : ρ ≤ ρ₀ := hρle.trans (min_le_left _ _)
  have hρc : ρ ≤ c₁ / 5 := hρle.trans (min_le_right _ _)
  obtain ⟨X₁, hX₁⟩ := hBS' ρ hρ hρ₀' ε hε hε1
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (max X₁ 1)).and
    ((eventually_subP_ge hρ 3).and ((tendsto_logIt_three.eventually_ge_atTop 1).and
      ((tendsto_logIt_two.eventually_ge_atTop (2 * max C 0 * ρ ^ 4 / η + 1)).and
        ((eventually_small hρ (2 * max C 0 / η) (by positivity)).and
          (tendsto_logIt_one.eventually_gt_atTop 0))))))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hXX, hP3, h3, h2big, hsmall, hlX⟩ := hX₀ X hX
  have hXX1 : X₁ ≤ X := le_trans (le_max_left _ _) hXX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hXX
  have hX0 : 0 ≤ X := by linarith
  have hPR : (3 : ℝ) ≤ subP ρ X := by exact_mod_cast hP3
  have hP0 : (0 : ℝ) < subP ρ X := by linarith
  have hL2pos : 0 < logIt 2 X := by
    have : (0 : ℝ) ≤ 2 * max C 0 * ρ ^ 4 / η := by positivity
    linarith
  -- sizes: F ≤ P, t ≤ P, π(P) ≤ P, P ≤ ρ log₂ X
  have hFP : (subF ρ X : ℝ) ≤ subP ρ X := by
    exact_mod_cast (subF_lt_subP (by omega : 2 ≤ subP ρ X)).le
  have htP : subT ε ρ X ≤ subP ρ X := by
    refine le_trans ?_ (expW_le_subP (by omega : 1 ≤ subP ρ X))
    unfold subT
    rw [Real.exp_le_exp]
    have := subW_nonneg ρ X
    nlinarith
  have ht0 : 0 ≤ subT ε ρ X := (Real.exp_pos _).le
  have hπP : (Nat.primeCounting (subP ρ X) : ℝ) ≤ subP ρ X := by
    exact_mod_cast primeCounting_le_self _
  have hPL : (subP ρ X : ℝ) * logIt 3 X ≤ ρ * logIt 2 X := by
    have hfl : (subP ρ X : ℝ) ≤ ρ * logIt 2 X / logIt 3 X := Nat.floor_le (by positivity)
    rw [le_div_iff₀ (by linarith)] at hfl
    exact hfl
  have hPρ : (subP ρ X : ℝ) ≤ ρ * logIt 2 X := by
    have := mul_le_mul_of_nonneg_left h3 hP0.le
    linarith
  -- the exponential factor
  have ht1 : 1 ≤ subT ε ρ X := Real.one_le_exp (mul_nonneg (by linarith) (subW_nonneg _ _))
  have hXY : X ≤ subT ε ρ X * X := by nlinarith
  have hl1 : logIt 1 X ≤ logIt 1 (subT ε ρ X * X) := Real.log_le_log (by linarith) hXY
  have hl2 : logIt 2 X ≤ logIt 2 (subT ε ρ X * X) := Real.log_le_log hlX hl1
  have h5 : 5 * logIt 3 X ≤ c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ) := by
    rw [le_div_iff₀ hP0]
    have h5a : 5 * ρ * logIt 2 X ≤ c₁ * logIt 2 X := by
      have := mul_le_mul_of_nonneg_right hρc hL2pos.le
      linarith
    have h5b : c₁ * logIt 2 X ≤ c₁ * logIt 2 (subT ε ρ X * X) :=
      mul_le_mul_of_nonneg_left hl2 hc₁.le
    linarith
  have hexp5 : Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))) ≤
      (logIt 2 X ^ 5)⁻¹ := by
    have e : Real.exp (-(5 * logIt 3 X)) = (logIt 2 X ^ 5)⁻¹ := by
      rw [Real.exp_neg, show 5 * logIt 3 X = ((5 : ℕ) : ℝ) * logIt 3 X by norm_num,
        Real.exp_nat_mul, logIt_three, Real.exp_log hL2pos]
    rw [← e, Real.exp_le_exp]
    linarith
  -- the bound from `eq:sharp-bad-source-count`
  have hcnt := hX₁ X hXX1
  set e := Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))) with he
  set cB := (cnt (badSrc (subP ρ X)) (subT ε ρ X * X) : ℝ) with hcB
  set P := (subP ρ X : ℝ) with hPdef
  set Fr := (subF ρ X : ℝ) with hFdef
  set t := subT ε ρ X with htdef
  set L2 := logIt 2 X with hL2def
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hπ0 : (0 : ℝ) ≤ Nat.primeCounting (subP ρ X) := Nat.cast_nonneg _
  have hbr0 : 0 ≤ Real.sqrt (t * X) + t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg ht0 hX0) hπ0) he0)
  have hcnt' : cB ≤
      max C 0 * (Real.sqrt (t * X) + t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e) :=
    hcnt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbr0)
  -- part 1: `√(tX) ≤ P √X`
  have hsqrtY : Real.sqrt (t * X) ≤ P * Real.sqrt X := by
    have h1 : Real.sqrt (t * X) ≤ Real.sqrt (P * X) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right htP hX0)
    rw [Real.sqrt_mul hP0.le] at h1
    have h2 : Real.sqrt P ≤ P := by
      rw [Real.sqrt_le_left hP0.le]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))
  have hP3le : P ^ 3 ≤ (4 * P) ^ subP ρ X := by
    calc P ^ 3 ≤ (4 * P) ^ 3 := pow_le_pow_left₀ hP0.le (by linarith) 3
      _ ≤ (4 * P) ^ subP ρ X := pow_le_pow_right₀ (by linarith) hP3
  have hK : 2 * max C 0 / η * P ^ 3 ≤ Real.sqrt X := by
    have hk0 : 0 ≤ 2 * max C 0 / η := by positivity
    calc 2 * max C 0 / η * P ^ 3 ≤ 2 * max C 0 / η * (4 * P) ^ subP ρ X * 1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hP3le hk0
      _ ≤ 2 * max C 0 / η * (4 * P) ^ subP ρ X * logIt 3 X :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ Real.sqrt X := hsmall
  have hpart1 : max C 0 * (Fr * Real.sqrt (t * X)) * P ≤ η / 2 * X := by
    have hsX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
    have hK' : max C 0 * P ^ 3 ≤ η / 2 * Real.sqrt X := by
      have e3 : 2 * max C 0 / η * P ^ 3 = (2 / η) * (max C 0 * P ^ 3) := by ring
      rw [e3] at hK
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ η)
      have e4 : η * (2 / η * (max C 0 * P ^ 3)) = 2 * (max C 0 * P ^ 3) := by
        field_simp
      linarith
    calc max C 0 * (Fr * Real.sqrt (t * X)) * P ≤ max C 0 * (P * (P * Real.sqrt X)) * P := by
          apply mul_le_mul_of_nonneg_right _ hP0.le
          apply mul_le_mul_of_nonneg_left _ hC'0
          exact mul_le_mul hFP hsqrtY (Real.sqrt_nonneg _) hP0.le
      _ = (max C 0 * P ^ 3) * Real.sqrt X := by ring
      _ ≤ (η / 2 * Real.sqrt X) * Real.sqrt X :=
          mul_le_mul_of_nonneg_right hK' (Real.sqrt_nonneg _)
      _ = η / 2 * X := by rw [mul_assoc, hsX]
  -- part 2
  have hpart2 : max C 0 * (Fr * (t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e)) * P ≤
      η / 2 * X := by
    have hL5 : 0 < L2 ^ 5 := by positivity
    have hP4 : P ^ 4 ≤ (ρ * L2) ^ 4 := pow_le_pow_left₀ hP0.le hPρ 4
    have hbig : max C 0 * ρ ^ 4 ≤ η / 2 * L2 := by
      have h' : 2 * max C 0 * ρ ^ 4 / η ≤ L2 := by linarith
      rw [div_le_iff₀ hη] at h'
      linarith
    have hkey : max C 0 * P ^ 4 * (L2 ^ 5)⁻¹ ≤ η / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hL5]
      calc max C 0 * P ^ 4 ≤ max C 0 * (ρ * L2) ^ 4 := mul_le_mul_of_nonneg_left hP4 hC'0
        _ = (max C 0 * ρ ^ 4) * L2 ^ 4 := by ring
        _ ≤ (η / 2 * L2) * L2 ^ 4 := mul_le_mul_of_nonneg_right hbig (by positivity)
        _ = η / 2 * L2 ^ 5 := by ring
    have hinner : Fr * (t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e) ≤
        P * (P * X * P * (L2 ^ 5)⁻¹) := by
      apply mul_le_mul hFP _ (by positivity) hP0.le
      apply mul_le_mul _ hexp5 he0 (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right htP hX0) hπP hπ0 (by positivity)
    calc max C 0 * (Fr * (t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e)) * P
        ≤ max C 0 * (P * (P * X * P * (L2 ^ 5)⁻¹)) * P :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hC'0) hP0.le
      _ = (max C 0 * P ^ 4 * (L2 ^ 5)⁻¹) * X := by ring
      _ ≤ η / 2 * X := mul_le_mul_of_nonneg_right hkey hX0
  -- assemble: `F · cB · P ≤ η X ≤ η X Δ P`
  have hΔ : 1 ≤ Delta (subP ρ X) * P := Delta_mul_ge_one _ (by omega)
  have hF0 : 0 ≤ Fr := Nat.cast_nonneg _
  have hmain : Fr * cB * P ≤ η * X := by
    have h1 : Fr * cB * P ≤ Fr * (max C 0 * (Real.sqrt (t * X) +
        t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e)) * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcnt' hF0) hP0.le
    have e1 : Fr * (max C 0 * (Real.sqrt (t * X) +
        t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e)) * P =
        max C 0 * (Fr * Real.sqrt (t * X)) * P +
          max C 0 * (Fr * (t * X * (Nat.primeCounting (subP ρ X) : ℝ) * e)) * P := by ring
    linarith
  have hfin : Fr * cB * P ≤ η * X * Delta (subP ρ X) * P := by
    have : η * X * 1 ≤ η * X * (Delta (subP ρ X) * P) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    have e2 : η * X * (Delta (subP ρ X) * P) = η * X * Delta (subP ρ X) * P := by ring
    linarith
  exact le_of_mul_le_mul_right hfin hP0


/-! ## `Claim_SubexpCore`: the surviving targets -/

/-- For `n ≥ 1`, `y`-roughness is coprimality with `y#`. -/
lemma isRough_iff_coprime {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : n ≠ 0) :
    IsRough y n ↔ Nat.Coprime n (primorialR y) := by
  unfold IsRough primorialR
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpn hpP
    have h1 := h p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩)
    have h3 : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).1 (hp.dvd_primorial_iff.1 hpP)
    linarith
  · intro h p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    by_contra hle
    have h2 : p ∣ primorial ⌊y⌋₊ := hpp.dvd_primorial_iff.2 (Nat.le_floor (not_lt.1 hle))
    exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hpn h2)

/-- `P ≥ M log₃ X` eventually (`P ≍ log₂X / log₃X`). -/
lemma eventually_subP_ge_mul {ρ : ℝ} (hρ : 0 < ρ) (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ X : ℝ in atTop, M * logIt 3 X ≤ subP ρ X := by
  have hlim : Tendsto (fun X : ℝ => logIt 3 X ^ 2 / logIt 2 X) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simp only [one_mul, add_zero] at h
    exact h.comp tendsto_logIt_two
  have hpos : (0 : ℝ) < ρ / (2 * M + 1) := by positivity
  filter_upwards [hlim.eventually (Iio_mem_nhds hpos), tendsto_logIt_three.eventually_gt_atTop 0,
    tendsto_logIt_two.eventually_gt_atTop 0, (tendsto_ratio hρ).eventually_ge_atTop 1]
    with X h1 h3 h2 hr
  have h1' : logIt 3 X ^ 2 / logIt 2 X < ρ / (2 * M + 1) := h1
  rw [div_lt_div_iff₀ h2 (by positivity)] at h1'
  have hP := half_le_floor hr
  have hPdef : (⌊ρ * logIt 2 X / logIt 3 X⌋₊ : ℝ) = subP ρ X := rfl
  rw [hPdef] at hP
  have hkey : M * logIt 3 X ≤ ρ * logIt 2 X / logIt 3 X / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have : 2 * M * logIt 3 X ^ 2 ≤ logIt 3 X ^ 2 * (2 * M + 1) := by nlinarith
    nlinarith
  linarith

open Classical in
lemma exists_bad_image (S : Set ℕ) (Fb : ℕ) (Y : ℝ) :
    ∃ Sc : Finset ℕ, Sc.card ≤ Fb * cnt S Y ∧
      ∀ e n : ℕ, 1 ≤ e → e ≤ Fb → 1 ≤ n → (n : ℝ) ≤ Y → n ∈ S → F e (n / e) ∈ Sc := by
  refine ⟨((Finset.Icc 1 Fb) ×ˢ ((Finset.Icc 1 ⌊Y⌋₊).filter (· ∈ S))).image
    (fun q => F q.1 (q.2 / q.1)), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
    exact le_rfl
  · intro e n he heF hn hnY hnS
    rw [Finset.mem_image]
    refine ⟨(e, n), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨he, heF⟩, ⟨hn, Nat.le_floor hnY⟩, hnS⟩

open Classical in
lemma exists_low_image (ε ρ X : ℝ) :
    ∃ Sd : Finset ℕ, Sd.card ≤ lowWitness ε ρ X ∧
      ∀ e d : ℕ, 2 ≤ e → e ≤ subF ρ X → 1 ≤ d → ((e * d : ℕ) : ℝ) ≤ subT ε ρ X * X →
        IsRough (subP ρ X) (F e d) → (∀ p : ℕ, p.Prime → p ≤ subP ρ X → p ∣ sig (e * d)) →
          F e d ∈ Sd := by
  unfold lowWitness
  refine ⟨_, Finset.card_image_le (f := fun q : ℕ × ℕ => F q.1 q.2), ?_⟩
  intro e d he heF hd hed hR hgood
  rw [Finset.mem_image]
  refine ⟨(e, d), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨⟨he, heF⟩, ⟨hd, ?_⟩⟩, hed, hR, hgood⟩
  apply Nat.le_floor
  have : (d : ℝ) ≤ ((e * d : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left d (by omega)
  linarith

open Classical in
lemma cntHalf_le_cover (A T Sa Sb Se : Set ℕ) (Sc Sd : Finset ℕ) (X : ℝ)
    (h : ∀ N : ℕ, ⌊X / 2⌋₊ < N → N ≤ ⌊X⌋₊ → N ∈ A →
      N ∈ T ∨ N ∈ Sa ∨ N ∈ Sb ∨ N ∈ Sc ∨ N ∈ Sd ∨ N ∈ Se) :
    (cntHalf A X : ℝ) ≤
      cntHalf T X + cnt Sa X + cnt Sb X + Sc.card + Sd.card + cnt Se X := by
  have key : cntHalf A X ≤
      cntHalf T X + cnt Sa X + cnt Sb X + Sc.card + Sd.card + cnt Se X := by
    unfold cntHalf cnt
    set Tf := (Finset.Ioc ⌊X / 2⌋₊ ⌊X⌋₊).filter (· ∈ T) with hTf
    set Saf := (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ Sa) with hSaf
    set Sbf := (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ Sb) with hSbf
    set Sef := (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ Se) with hSef
    have hsub : (Finset.Ioc ⌊X / 2⌋₊ ⌊X⌋₊).filter (· ∈ A) ⊆
        ((((Tf ∪ Saf) ∪ Sbf) ∪ Sc) ∪ Sd) ∪ Sef := by
      intro N hN
      rw [Finset.mem_filter, Finset.mem_Ioc] at hN
      obtain ⟨⟨h1, h2⟩, hA⟩ := hN
      have hI : N ∈ Finset.Icc 1 ⌊X⌋₊ := Finset.mem_Icc.2 ⟨by omega, h2⟩
      rcases h N h1 h2 hA with hT | hSa | hSb | hSc | hSd | hSe
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1, h2⟩, hT⟩)))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hI, hSa⟩)))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hI, hSb⟩))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hSc))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hSd)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hI, hSe⟩)
    have c0 := Finset.card_le_card hsub
    have c1 := Finset.card_union_le Tf Saf
    have c2 := Finset.card_union_le (Tf ∪ Saf) Sbf
    have c3 := Finset.card_union_le ((Tf ∪ Saf) ∪ Sbf) Sc
    have c4 := Finset.card_union_le (((Tf ∪ Saf) ∪ Sbf) ∪ Sc) Sd
    have c5 := Finset.card_union_le ((((Tf ∪ Saf) ∪ Sbf) ∪ Sc) ∪ Sd) Sef
    omega
  exact_mod_cast key

open Classical in
theorem subexpCore (hSR : Eq_SharpRoughTargetCount) (hRN : UpperTails.Claim_RoughNonsquarefree)
    (hBP : UpperTails.Claim_SubexpBadPairs) (hC1 : UpperTails.Claim_SubexpCofactorOne)
    (hLC : UpperTails.Claim_SubexpLowCofactor) (hLG : UpperTails.Claim_SubexpLargeCofactor)
    (hMom : Lem_Moment) (hOdd : Lem_AnalyticOddRepresentability) :
    UpperTails.Claim_SubexpCore := by
  obtain ⟨ρ₀, hρ₀, hBP'⟩ := hBP
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρle ε hε hε1 => ?_⟩
  obtain ⟨Cs, c₁, c₂, hc₁, hc₂, hSR'⟩ := hSR
  obtain ⟨Cr, hRN'⟩ := hRN
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ, η₀ = c₁ / 10 := ⟨_, rfl⟩
  have hη₀0 : 0 < η₀ := by rw [hη₀]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * (c₂ + 1) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  -- the moment exponent `k` with `(k+1) ε > 2`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈2 / ε⌉₊ + 2 := ⟨_, rfl⟩
  have hk2 : 2 ≤ k := by omega
  have hkε : 2 < ((k : ℝ) + 1) * ε := by
    have h1 : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((k : ℝ) + 1) = (⌈2 / ε⌉₊ : ℝ) + 3 := by
      rw [hk]
      push_cast
      ring
    rw [h2]
    have h3 : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε.ne'
    have h4 := mul_le_mul_of_nonneg_right h1 hε.le
    nlinarith
  obtain ⟨Ck, ⟨hCk0, _⟩, _, hLCk⟩ := hMom k hk2
  -- the component bounds
  obtain ⟨X₁, hX₁⟩ := hSR' ρ hρ
  obtain ⟨X₂, hX₂⟩ := hOdd.2 η₀ hη₀0
  obtain ⟨X₃, hX₃⟩ := hBP' ρ hρ hρle ε hε hε1 (η₀ / K) (by positivity)
  obtain ⟨X₄, hX₄⟩ := hLC ρ hρ ε hε hε1 (ε / 2) (by positivity)
  obtain ⟨X₅, hX₅⟩ := hLG ρ hρ ε hε hε1 k hk2 hkε (η₀ / (K * Ck)) (by positivity)
  have ev : ∀ᶠ X : ℝ in atTop, X₁ ≤ X ∧ X₂ ≤ X ∧ X₃ ≤ X ∧ X₄ ≤ X ∧ X₅ ≤ X ∧ 1 ≤ X ∧
      2 ≤ subP ρ X ∧ 0 < logIt 3 X ∧
      (|Cs| + 1) * (4 * (subP ρ X : ℝ)) ^ (subP ρ X) * logIt 3 X ≤ Real.sqrt X ∧
      2 / ε * Real.log (K / η₀) ≤ subW ρ X ∧
      |Cr| / η₀ * logIt 3 X ≤ subP ρ X := by
    filter_upwards [eventually_ge_atTop X₁, eventually_ge_atTop X₂, eventually_ge_atTop X₃,
      eventually_ge_atTop X₄, eventually_ge_atTop X₅, eventually_ge_atTop 1,
      eventually_subP_ge hρ 2, tendsto_logIt_three.eventually_gt_atTop 0,
      eventually_small hρ (|Cs| + 1) (by positivity),
      (tendsto_subW hρ).eventually_ge_atTop (2 / ε * Real.log (K / η₀)),
      eventually_subP_ge_mul hρ (|Cr| / η₀) (by positivity)]
      with X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ev
  refine ⟨c₁ / 2, by positivity, X₀, fun X hX => ?_⟩
  obtain ⟨hX1', hX2', hX3', hX4', hX5', hX1, hP2, ha0, hsmall, hWbig, hPbig⟩ := hX₀ X hX
  obtain ⟨habs, hlow, hup⟩ := hX₁ X hX1'
  have hX0 : 0 ≤ X := by linarith
  have hPR : (2 : ℝ) ≤ subP ρ X := by exact_mod_cast hP2
  have hP0 : (0 : ℝ) < subP ρ X := by linarith
  have hΔ0 := Delta_nonneg (subP ρ X : ℝ)
  have ht1 : 1 ≤ subT ε ρ X := Real.one_le_exp (mul_nonneg (by linarith) (subW_nonneg _ _))
  have hZ0 : 0 ≤ X / logIt 3 X := div_nonneg hX0 ha0.le
  have hKne : K ≠ 0 := hK0.ne'
  have hη₀ne : η₀ ≠ 0 := hη₀0.ne'
  have hCkne : Ck ≠ 0 := hCk0.ne'
  have hane : logIt 3 X ≠ 0 := ha0.ne'
  have hεne : ε ≠ 0 := hε.ne'
  -- `|Cs| P# ≤ X / log₃ X` and `X Δ ≤ K X / log₃ X`
  have hsqX : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_left hX0]
    nlinarith
  have hQle := primorial_le_four_mul_pow (subP ρ X) (by omega)
  have hQ0 : (0 : ℝ) ≤ primorial (subP ρ X) := Nat.cast_nonneg _
  have hQa : |Cs| * (primorial (subP ρ X) : ℝ) ≤ X / logIt 3 X := by
    rw [le_div_iff₀ ha0]
    have h1 : |Cs| * (primorial (subP ρ X) : ℝ) * logIt 3 X ≤
        (|Cs| + 1) * (4 * (subP ρ X : ℝ)) ^ (subP ρ X) * logIt 3 X := by
      apply mul_le_mul_of_nonneg_right _ ha0.le
      exact mul_le_mul (by linarith) hQle hQ0 (by positivity)
    linarith
  have hXΔ : X * Delta (subP ρ X) ≤ K * (X / logIt 3 X) := by
    rw [abs_le] at habs
    have hCsQ : Cs * (primorial (subP ρ X) : ℝ) ≤ |Cs| * (primorial (subP ρ X) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self Cs) hQ0
    have hup' : c₂ * X / logIt 3 X = c₂ * (X / logIt 3 X) := mul_div_assoc _ _ _
    rw [hK]
    linarith
  -- the five exceptional pieces, each at most `η₀ X / log₃ X`
  obtain ⟨Sc, hSc_card, hSc_mem⟩ := exists_bad_image (badSrc (subP ρ X)) (subF ρ X)
    (subT ε ρ X * X)
  obtain ⟨Sd, hSd_card, hSd_mem⟩ := exists_low_image ε ρ X
  have hcov := cntHalf_le_cover {N : ℕ | Nat.Coprime N (primorial (subP ρ X))}
    {N : ℕ | N ∈ R ∧ Squarefree N ∧ subT ε ρ X * (N : ℝ) < (f N : ℝ)}
    {N : ℕ | IsRough (subP ρ X : ℝ) N ∧ ¬ Squarefree N} oddUnrep
    (largeCofactorSet (subT ε ρ X) (subF ρ X)) Sc Sd X ?_
  swap
  · intro N hN1 hN2 hNA
    have hNA' : Nat.Coprime N (primorial (subP ρ X)) := hNA
    have hN0 : N ≠ 0 := by omega
    have hrough : IsRough (subP ρ X : ℝ) N := by
      rw [isRough_iff_coprime (Nat.cast_nonneg _) hN0, primorialR_natCast]
      exact hNA'
    have h2P : 2 ∣ primorial (subP ρ X) := Nat.prime_two.dvd_primorial_iff.2 hP2
    have hodd : Odd N := by
      have hnd : ¬ 2 ∣ N := fun h =>
        (by norm_num : (2 : ℕ) ≠ 1) (Nat.eq_one_of_dvd_coprimes hNA' h h2P)
      rcases Nat.mod_two_eq_zero_or_one N with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hnd
      · exact Nat.odd_iff.2 h
    by_cases hsq : Squarefree N
    swap
    · exact Or.inr (Or.inl (⟨hrough, hsq⟩ : IsRough (subP ρ X : ℝ) N ∧ ¬ Squarefree N))
    by_cases hR : N ∈ R
    swap
    · exact Or.inr (Or.inr (Or.inl (⟨hodd, hR⟩ : Odd N ∧ N ∉ R)))
    by_cases ht : subT ε ρ X * (N : ℝ) < (f N : ℝ)
    · exact Or.inl (⟨hR, hsq, ht⟩ : N ∈ R ∧ Squarefree N ∧ subT ε ρ X * (N : ℝ) < (f N : ℝ))
    rw [not_lt] at ht
    obtain ⟨e, d, he, hd, hfN, hNF⟩ := f_mem_Fform N hR
    have hNX : (N : ℝ) ≤ X := (Nat.le_floor_iff hX0).1 hN2
    have hedN : ((e * d : ℕ) : ℝ) ≤ subT ε ρ X * N := by
      rw [← hfN]
      exact ht
    have hedX : ((e * d : ℕ) : ℝ) ≤ subT ε ρ X * X :=
      hedN.trans (mul_le_mul_of_nonneg_left hNX (by linarith))
    by_cases heF : (subF ρ X : ℝ) < e
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      have hedN' : (e : ℝ) * d ≤ subT ε ρ X * N := by
        push_cast at hedN
        exact hedN
      exact (⟨e, d, he, hd, hNF, heF, hedN'⟩ : ∃ e d : ℕ, 1 ≤ e ∧ 1 ≤ d ∧ N = F e d ∧
        (subF ρ X : ℝ) < (e : ℝ) ∧ (e * d : ℝ) ≤ subT ε ρ X * N)
    rw [not_lt] at heF
    have heF' : e ≤ subF ρ X := by exact_mod_cast heF
    by_cases hbad : e * d ∈ badSrc (subP ρ X)
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have hmem := hSc_mem e (e * d) he heF' (Nat.mul_pos (by omega) (by omega)) hedX hbad
      rwa [Nat.mul_div_cancel_left d (by omega : 0 < e), ← hNF] at hmem
    have hbad' : ¬ ∃ p : ℕ, p.Prime ∧ p ≤ subP ρ X ∧ ¬ p ∣ sig (e * d) := hbad
    have hgood : ∀ p : ℕ, p.Prime → p ≤ subP ρ X → p ∣ sig (e * d) := by
      intro p hp hpP
      by_contra h
      exact hbad' ⟨p, hp, hpP, h⟩
    by_cases he1 : e = 1
    · exfalso
      subst he1
      have hgood1 : ∀ p : ℕ, p.Prime → p ≤ subP ρ X → p ∣ sig d := by
        intro p hp hpP
        have := hgood p hp hpP
        rwa [one_mul] at this
      exact hC1 (subP ρ X) N d hP2 hd hNF hrough hgood1
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      have hmem := hSd_mem e d (by omega) heF' hd hedX (hNF ▸ hrough) hgood
      rwa [← hNF] at hmem
  -- bound each piece
  have ha : (cnt {N : ℕ | IsRough (subP ρ X : ℝ) N ∧ ¬ Squarefree N} X : ℝ) ≤
      η₀ * (X / logIt 3 X) := by
    refine (hRN' (subP ρ X : ℝ) hPR X hX1).trans ?_
    have h1 : Cr * X / (subP ρ X : ℝ) ≤ |Cr| * X / (subP ρ X : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cr) hX0) hP0.le
    refine h1.trans ?_
    have h2 : |Cr| * logIt 3 X ≤ η₀ * subP ρ X := by
      have := mul_le_mul_of_nonneg_left hPbig hη₀0.le
      have e : η₀ * (|Cr| / η₀ * logIt 3 X) = |Cr| * logIt 3 X := by
        field_simp
      linarith
    rw [← mul_div_assoc, div_le_div_iff₀ hP0 ha0]
    have := mul_le_mul_of_nonneg_right h2 hX0
    linarith
  have hb : (cnt oddUnrep X : ℝ) ≤ η₀ * (X / logIt 3 X) := hX₂ X hX2'
  have hc : (Sc.card : ℝ) ≤ η₀ * (X / logIt 3 X) := by
    have h1 : (Sc.card : ℝ) ≤ (subF ρ X : ℝ) * (cnt (badSrc (subP ρ X)) (subT ε ρ X * X) : ℝ) := by
      exact_mod_cast hSc_card
    have h2 := hX₃ X hX3'
    have h3 : η₀ / K * X * Delta (subP ρ X) ≤ η₀ / K * (K * (X / logIt 3 X)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hXΔ (by positivity)
    have e : η₀ / K * (K * (X / logIt 3 X)) = η₀ * (X / logIt 3 X) := by
      field_simp
    linarith
  have hd : (Sd.card : ℝ) ≤ η₀ * (X / logIt 3 X) := by
    have h1 : (Sd.card : ℝ) ≤ lowWitness ε ρ X := by exact_mod_cast hSd_card
    have h2 := hX₄ X hX4'
    have hexp : Real.exp (-(ε * subW ρ X) + ε / 2 * subW ρ X) ≤ η₀ / K := by
      have hlog : -(ε * subW ρ X) + ε / 2 * subW ρ X ≤ Real.log (η₀ / K) := by
        rw [Real.log_div hη₀0.ne' hK0.ne', ← neg_sub, ← Real.log_div hK0.ne' hη₀0.ne']
        have := mul_le_mul_of_nonneg_left hWbig (by positivity : (0 : ℝ) ≤ ε / 2)
        have e : ε / 2 * (2 / ε * Real.log (K / η₀)) = Real.log (K / η₀) := by
          field_simp
        linarith
      calc Real.exp (-(ε * subW ρ X) + ε / 2 * subW ρ X) ≤ Real.exp (Real.log (η₀ / K)) :=
            Real.exp_le_exp.2 hlog
        _ = η₀ / K := Real.exp_log (by positivity)
    have h3 : X * Delta (subP ρ X) * Real.exp (-(ε * subW ρ X) + ε / 2 * subW ρ X) ≤
        K * (X / logIt 3 X) * (η₀ / K) :=
      mul_le_mul hXΔ hexp (Real.exp_pos _).le (by positivity)
    have e : K * (X / logIt 3 X) * (η₀ / K) = η₀ * (X / logIt 3 X) := by
      field_simp
    linarith
  have he : (cnt (largeCofactorSet (subT ε ρ X) (subF ρ X)) X : ℝ) ≤
      η₀ * (X / logIt 3 X) := by
    have hF1 : (1 : ℝ) ≤ subF ρ X := by exact_mod_cast one_le_subF ρ X
    have h1 := hLCk (subT ε ρ X) X (subF ρ X) ht1 hX1 hF1
    have h2 := hX₅ X hX5'
    have h3 : Ck * subT ε ρ X ^ (k + 1) * (subF ρ X : ℝ) ^ (1 - (k : ℝ)) * X ≤
        Ck * (η₀ / (K * Ck) * Delta (subP ρ X)) * X := by
      rw [mul_assoc Ck]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCk0.le) hX0
    have e : Ck * (η₀ / (K * Ck) * Delta (subP ρ X)) * X = η₀ / K * (X * Delta (subP ρ X)) := by
      field_simp
    have h4 : η₀ / K * (X * Delta (subP ρ X)) ≤ η₀ / K * (K * (X / logIt 3 X)) :=
      mul_le_mul_of_nonneg_left hXΔ (by positivity)
    have e2 : η₀ / K * (K * (X / logIt 3 X)) = η₀ * (X / logIt 3 X) := by
      field_simp
    linarith
  -- assemble
  have hlow' : c₁ * X / logIt 3 X = c₁ * (X / logIt 3 X) := mul_div_assoc _ _ _
  have hgoal : c₁ / 2 * X / logIt 3 X = c₁ / 2 * (X / logIt 3 X) := mul_div_assoc _ _ _
  rw [hgoal]
  rw [hlow'] at hlow
  have hη : η₀ * (X / logIt 3 X) = c₁ / 10 * (X / logIt 3 X) := by rw [hη₀]
  linarith

end Principia.Erdos1054.Proofs.Thm14

/-! ## The package `Thm14`: leaves and links, stated by name -/

namespace Principia.Erdos1054.Proofs

theorem leaf_UpperTails_Claim_SubexpFltP : Principia.Erdos1054.UpperTails.Claim_SubexpFltP :=
  Thm14.fltP

theorem leaf_UpperTails_Claim_SubexpLogT : Principia.Erdos1054.UpperTails.Claim_SubexpLogT :=
  Thm14.logT

theorem leaf_UpperTails_Claim_SubexpCofactorOne :
    Principia.Erdos1054.UpperTails.Claim_SubexpCofactorOne :=
  Thm14.cofactorOne

theorem link_UpperTails_Claim_SubexpWitnessStructure :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpWitnessStructure :=
  fun hFM hKG => Thm14.witnessStructure hFM hKG

theorem link_Eq_MovingKernelLowerBound :
    Principia.Erdos1054.Spine.Link_Eq_MovingKernelLowerBound :=
  fun hWS hF hM3 => Thm14.movingKernelLowerBound hWS hF hM3

theorem link_UpperTails_Claim_SubexpCoprimeCount :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpCoprimeCount :=
  fun hD => Thm14.coprimeCount hD

theorem link_UpperTails_Claim_SubexpLowCofactorSum :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpLowCofactorSum :=
  fun hWS hMK hCC hF => Thm14.lowCofactorSum hWS hMK hCC hF

theorem link_UpperTails_Claim_SubexpLowCofactor :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpLowCofactor :=
  fun hLS hMT => Thm14.lowCofactor hLS hMT

theorem link_UpperTails_Claim_SubexpLargeCofactor :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpLargeCofactor :=
  fun hM3 => Thm14.largeCofactor hM3

theorem link_Eq_SharpRoughTargetCount :
    Principia.Erdos1054.Spine.Link_Eq_SharpRoughTargetCount :=
  fun hD hM3 => Thm14.sharpRoughTargetCount hD hM3

theorem link_Eq_SharpBadSourceCount :
    Principia.Erdos1054.Spine.Link_Eq_SharpBadSourceCount :=
  fun hSR => Thm14.badSourceCount hSR

theorem link_UpperTails_Claim_SubexpBadPairs :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpBadPairs :=
  fun hBS _ => Thm14.badPairs hBS

theorem link_UpperTails_Claim_SubexpCore :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpCore :=
  fun hSR hRN hBP hC1 hLC hLG hMom hOdd =>
    Thm14.subexpCore hSR hRN hBP hC1 hLC hLG hMom hOdd

theorem link_UpperTails_Claim_SubexpThreshold :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_SubexpThreshold :=
  fun hLT => Thm14.threshold hLT

theorem link_Eq_SubexpGrowth : Principia.Erdos1054.Spine.Link_Eq_SubexpGrowth :=
  fun hC hT => Thm14.subexpGrowth hC hT

theorem link_Eq_PositiveMomentGrowth : Principia.Erdos1054.Spine.Link_Eq_PositiveMomentGrowth :=
  fun hG => Thm14.positiveMomentGrowth hG

end Principia.Erdos1054.Proofs
