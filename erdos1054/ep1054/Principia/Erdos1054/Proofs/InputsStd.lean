/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Common.Mertens.Mertens
import Principia.Common.HalberstamRichertPollack
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false

/-!
# EP1054: the standard inputs — the `InputsStd` package of the spine

Discharges, for `Principia.Erdos1054.Spine` (paper `Campaigns/Erdos-1054/collab-paper/EP1054.tex`),
the standard analytic inputs of `Principia.Erdos1054.Statements.Inputs` that are provable from
pinned Mathlib and the ported, axiom-clean Mertens / Halberstam–Richert modules. Nothing here is
new mathematics; everything is a bridge from an existing verified statement to the exact
`Inputs.lean` encoding (sum ranges `Iic ⌊x⌋₊` / `range (⌊y⌋₊ + 1)` vs `Ioc 0 ⌊x⌋₊` vs
`Nat.primesLE`), or a textbook argument.

Inputs discharged (trusted base, sections (1)–(2) of `Inputs.lean`):
* `input_Std_Mertens2` — Mertens' second theorem, from `Mertens.E₂p.abs_le`
  (`M = Mertens.M`, `C = log 4 + 6 + E₁`).
* `input_Std_Mertens3` — `Δ(y) log y → e^{-γ}`, from `Mertens.prod_one_minus_div_prime_eq` and
  `Mertens.E₃.bound'`.
* `input_Cite_Pollack_Lemma24` — Pollack's Lemma 2.4 at `λ₁ = λ₂ = 1`, from
  `Principia.Common.HalberstamRichert.pollack_mean_value_arithmeticFunction`.
* `input_Std_divisorBound` — `τ(n) ≤ C_ε n^ε`, proved here: `τ(n) = ∏_{p^a ‖ n} (a + 1)`
  (`Nat.card_divisors`) and `a + 1 ≤ w_p (p^a)^ε` with `w_p = 1` once `p^ε ≥ 2`
  (`prime_pow_bound`, Bernoulli's inequality).

Leaves:
* `leaf_Std_Mertens1` — `∑_{p ≤ y} log p/(p − 1) ≪ log y`, from `log p/(p − 1) ≤ 2 log p/p` and
  `Mertens.sum_log_prime_div_eq_log`.
* `leaf_Std_recipPrimesAP_diverges` — proved outright (`recipPrimesAP_diverges`) by the project's
  own axiom-free proof of Dirichlet's theorem in reciprocal form,
  `LeanSandbox/DirichletReciprocalAP.lean` (`A1proof.main`, 2026-07-09, commit `75867642`), ported
  below as section `A1`: Mathlib's pole bound `LSeries_residueClass_lower_bound`, a per-prime FTC,
  Tonelli, and `∫ c/(t − 1) = ∞`. The paper derives it from `Std_PNT_AP` (lines 476–478); that
  edge was dropped from the spine on 2026-09-26 (LEAN-PROGRESS F7), and this was a link before.

Links (derived inputs of section (4)):
* `link_Std_PNT` — `ψ(x)/x → 1` from `Std_PNT_AP` at `Q = 1` (`π(x) log x/x → 1`), Mathlib's
  `Chebyshev.primeCounting_sub_theta_div_log_isBigO` (`π − θ/log = O(x/log² x)`) and
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`.
* `link_Std_primes_dyadic_lower` — `π(2t) − π(t) ≥ c t/log t` (`t ≥ 2`) from `Std_PNT_AP` at
  `Q = 1` for `t ≥ T`, and Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) on `[2, T)`.

Port changes to `A1proof` (otherwise verbatim): namespace `A1proof` →
`Principia.Erdos1054.Proofs.InputsStd.A1`; `import Mathlib` → the specific imports above; the unused
hypothesis `ha : IsUnit a` removed from `VW`, `Wint`, `Vmono`, `hunb` (call sites in `main` updated);
`variable [NeZero q]` moved below `bridge` (unused by `Vmono`, `bridge`); an unused `simp` argument
dropped.

Footprints: every declaration is `[propext, Classical.choice, Quot.sound]` (probe
`probe_InputsStd.lean`).
-/

namespace Principia.Erdos1054.Proofs.InputsStd

open Filter Topology

/-! ## Sum-range bridges -/

/-- The primes `≤ n`, as `Iic` vs `Ioc 0`. -/
lemma filter_prime_Iic_eq_Ioc (n : ℕ) :
    (Finset.Iic n).filter Nat.Prime = (Finset.Ioc 0 n).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.pos, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- The primes `≤ n`, as `range (n + 1)` vs `Ioc 0`. -/
lemma filter_prime_range_eq_Ioc (n : ℕ) :
    (Finset.range (n + 1)).filter Nat.Prime = (Finset.Ioc 0 n).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.pos, by omega⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨by omega, h2⟩

/-- The primes `≤ n`, as `Iic` vs Mathlib's `primesLE`. -/
lemma filter_prime_Iic_eq_primesLE (n : ℕ) :
    (Finset.Iic n).filter Nat.Prime = Nat.primesLE n := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mem_primesLE]

/-! ## The divisor bound -/

/-- Per-prime-power bound behind the divisor bound: for `ε > 0` there are `B ≥ 1` and `M` such
that `k + 1 ≤ w_p · (p^k)^ε` for every prime `p` and `k : ℕ`, where `w_p = B` if `p < M` and
`w_p = 1` otherwise. -/
lemma prime_pow_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ M : ℕ, ∀ p k : ℕ, p.Prime →
      ((k : ℝ) + 1) ≤ (if p < M then B else 1) * (((p : ℝ) ^ k) ^ ε) := by
  have hr1 : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  refine ⟨max 1 (1 / ((2 : ℝ) ^ ε - 1)), le_max_left _ _, ⌈(2 : ℝ) ^ (1 / ε)⌉₊,
    fun p k hp => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← Real.rpow_pow_comm hp0 ε k]
  have hqr : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
  have hbern : 1 + (k : ℝ) * ((p : ℝ) ^ ε - 1) ≤ ((p : ℝ) ^ ε) ^ k := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) ^ ε - 1 by linarith) k
    have h' : 1 + ((p : ℝ) ^ ε - 1) = (p : ℝ) ^ ε := by ring
    rw [h'] at h
    exact h
  split_ifs with hpM
  · set B : ℝ := max 1 (1 / ((2 : ℝ) ^ ε - 1)) with hBdef
    have hB1 : 1 ≤ B := le_max_left _ _
    have hB0 : 0 ≤ B := by linarith
    have hBr : 1 ≤ B * ((2 : ℝ) ^ ε - 1) := by
      have h2 : 1 / ((2 : ℝ) ^ ε - 1) ≤ B := le_max_right _ _
      rwa [div_le_iff₀ (by linarith)] at h2
    have hprod := mul_nonneg hk (sub_nonneg.mpr hBr)
    calc (k : ℝ) + 1 ≤ B * (1 + k * ((2 : ℝ) ^ ε - 1)) := by nlinarith [hprod]
      _ ≤ B * (1 + k * ((p : ℝ) ^ ε - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right hqr 1) hk]
      _ ≤ B * ((p : ℝ) ^ ε) ^ k := mul_le_mul_of_nonneg_left hbern hB0
  · have hMp : (2 : ℝ) ^ (1 / ε) ≤ p := by
      have hle : ⌈(2 : ℝ) ^ (1 / ε)⌉₊ ≤ p := Nat.le_of_not_lt hpM
      calc (2 : ℝ) ^ (1 / ε) ≤ (⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ p := by exact_mod_cast hle
    have hq2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hMp hε.le
    rw [one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (p : ℝ) ^ ε - 1 by linarith) hk]

/-! ## The prime number theorem from `Std_PNT_AP` -/

/-- `π(x; 1, 0) = π(⌊x⌋)`: the `Q = 1` count of `piAP` is the prime-counting function. -/
lemma piAP_one (x : ℝ) : Principia.Erdos1054.piAP x 1 (1 - 1) = Nat.primeCounting ⌊x⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  unfold Principia.Erdos1054.piAP
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mem_primesLE, Nat.mod_one]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, trivial⟩

/-- The `Q = 1` case of `Std_PNT_AP`: `π(x) log x / x → 1`. -/
lemma primeCounting_tendsto (hAP : Principia.Erdos1054.Std_PNT_AP) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) := by
  have h := hAP 1 le_rfl
  simp only [piAP_one, Nat.totient_one, Nat.cast_one, div_one] at h
  exact h

/-- `θ(x)/x → 1`, from `π(x) log x/x → 1` and Mathlib's
`π(x) − θ(x)/log x = O(x/log² x)`. -/
lemma theta_div_tendsto
    (hπ : Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hE := Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have h1 : (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) *
      (Real.log x / x)) =O[atTop] (fun x : ℝ => x / Real.log x ^ 2 * (Real.log x / x)) :=
    hE.mul (Asymptotics.isBigO_refl _ _)
  have h2 : Tendsto (fun x : ℝ => x / Real.log x ^ 2 * (Real.log x / x)) atTop (𝓝 0) := by
    refine Real.tendsto_log_atTop.inv_tendsto_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := by linarith
    show (Real.log x)⁻¹ = x / Real.log x ^ 2 * (Real.log x / x)
    field_simp
  have h4 := hπ.sub (h1.trans_tendsto h2)
  rw [sub_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  field_simp
  ring

/-- `(ψ(x) − θ(x))/x → 0`, from Mathlib's `|ψ − θ| ≤ 2 √x log x`. -/
lemma psi_sub_theta_div_tendsto :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
  have hlo := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hlo2 := hlo.const_mul 2
  rw [mul_zero] at hlo2
  refine squeeze_zero_norm' ?_ hlo2
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx.le
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0, ← Real.sqrt_eq_rpow]
  calc |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x := hb
    _ = 2 * (Real.log x / Real.sqrt x) * (Real.sqrt x * Real.sqrt x) := by field_simp
    _ = 2 * (Real.log x / Real.sqrt x) * x := by rw [hs]

end Principia.Erdos1054.Proofs.InputsStd

/-! ## Dirichlet's theorem, reciprocal form (port of `LeanSandbox/DirichletReciprocalAP.lean`) -/

section A1

open scoped BigOperators LSeries.notation
open ArithmeticFunction ArithmeticFunction.vonMangoldt MeasureTheory intervalIntegral

namespace Principia.Erdos1054.Proofs.InputsStd.A1
variable {q : ℕ} {a : ZMod q}

noncomputable def prc (a : ZMod q) (n : ℕ) : ℝ := if (n.Prime ∧ (n:ZMod q) = a) then 1 else 0
noncomputable def Vf (a : ZMod q) (x : ℝ) : ℝ := ∑' n : ℕ, prc a n * (n:ℝ)^(-x)
noncomputable def Wf (a : ZMod q) (x : ℝ) : ℝ := ∑' n : ℕ, prc a n * Real.log n * (n:ℝ)^(-x)

theorem prc_nonneg (a : ZMod q) (n : ℕ) : 0 ≤ prc a n := by unfold prc; split_ifs <;> norm_num
theorem prc_le_one (a : ZMod q) (n : ℕ) : prc a n ≤ 1 := by unfold prc; split_ifs <;> norm_num
theorem coef_nonneg (a : ZMod q) (n : ℕ) : 0 ≤ prc a n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [prc, Nat.not_prime_zero]
  · exact mul_nonneg (prc_nonneg a n) (Real.log_nonneg (by exact_mod_cast hn))

theorem ftc_rpow (p : ℝ) (hp : 0 < p) (x : ℝ) :
    (∫ t in x..2, Real.log p * p^(-t)) = p^(-x) - p^(-(2:ℝ)) := by
  have hcont : Continuous (fun t : ℝ => Real.log p * p^(-t)) :=
    continuous_const.mul ((Real.continuous_const_rpow (ne_of_gt hp)).comp continuous_neg)
  have hd : ∀ t ∈ Set.uIcc x (2:ℝ),
      HasDerivAt (fun t => -(p^(-t))) (Real.log p * p^(-t)) t := by
    intro t _
    have hf : HasDerivAt (fun t : ℝ => -t) (-1) t := (hasDerivAt_id t).neg
    have h1 := (hf.const_rpow hp).neg
    have heq : -(Real.log p * (-1) * p^(-t)) = Real.log p * p^(-t) := by ring
    rw [heq] at h1; exact h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]; ring

theorem gcont (a : ZMod q) (n : ℕ) : Continuous (fun t : ℝ => prc a n * Real.log n * (n:ℝ)^(-t)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [prc, Nat.not_prime_zero, false_and, if_false, Nat.cast_zero, Real.log_zero,
      mul_zero, zero_mul]; exact continuous_const
  · exact continuous_const.mul ((Real.continuous_const_rpow (by exact_mod_cast hn.ne')).comp continuous_neg)

noncomputable def gcm (a : ZMod q) (n : ℕ) : C(ℝ, ℝ) := ⟨fun t => prc a n * Real.log n * (n:ℝ)^(-t), gcont a n⟩

theorem gnorm_le (x : ℝ) (hx1 : 1 < x) (hx2 : x ≤ 2) (n : ℕ) :
    ‖(gcm a n).restrict (⟨Set.uIcc x 2, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ prc a n * Real.log n * (n:ℝ)^(-x) := by
  have hval : 0 ≤ prc a n * Real.log n * (n:ℝ)^(-x) :=
    mul_nonneg (coef_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [ContinuousMap.norm_le _ hval]
  rintro ⟨t, ht⟩
  have ht' : x ≤ t ∧ t ≤ 2 := by simpa [Set.uIcc_of_le hx2] using ht
  simp only [ContinuousMap.restrict_apply, gcm, ContinuousMap.coe_mk]
  rw [Real.norm_of_nonneg (mul_nonneg (coef_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
  have hrp : (n:ℝ)^(-t) ≤ (n:ℝ)^(-x) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith [ht'.1] : -t ≠ 0), Real.zero_rpow (by linarith : -x ≠ 0)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith [ht'.1])
  exact mul_le_mul_of_nonneg_left hrp (coef_nonneg a n)

theorem Rsum (x : ℝ) (hx : 1 < x) : Summable (fun n : ℕ => residueClass a n / (n:ℝ)^x) := by
  have h : LSeriesSummable (↗(residueClass a)) (x:ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx)
  refine (h.norm).congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [hn, if_false, Complex.ofReal_re]
    rw [Complex.norm_real, Real.norm_of_nonneg (residueClass_nonneg a n)]

theorem Wf_summand (x : ℝ) (n : ℕ) :
    prc a n * Real.log n * (n:ℝ)^(-x) = (if n.Prime then residueClass a n else 0) / (n:ℝ)^x := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  unfold prc residueClass
  by_cases hp : n.Prime
  · simp only [hp, if_true, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hc : (n:ZMod q) = a
    · simp only [hc, and_self, if_true, vonMangoldt_apply_prime hp]; ring
    · simp only [hc, and_false, if_false]; ring
  · simp only [hp, if_false, false_and, if_false]; ring

theorem Wsummable (x : ℝ) (hx : 1 < x) : Summable (fun n : ℕ => prc a n * Real.log n * (n:ℝ)^(-x)) := by
  apply (Rsum (a := a) x hx).of_nonneg_of_le
    (fun n => by rw [Wf_summand]; positivity [residueClass_nonneg a n])
    (fun n => ?_)
  rw [Wf_summand]
  by_cases hp : n.Prime <;> simp [hp] <;> exact div_nonneg (residueClass_nonneg a n) (by positivity)

theorem Vfsummable (x : ℝ) (hx : 1 < x) : Summable (fun n : ℕ => prc a n * (n:ℝ)^(-x)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (prc_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => ?_) (Real.summable_nat_rpow_inv.mpr hx)
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  calc prc a n * ((n:ℝ)^x)⁻¹ ≤ 1 * ((n:ℝ)^x)⁻¹ :=
        mul_le_mul_of_nonneg_right (prc_le_one a n) (by positivity)
    _ = ((n:ℝ)^x)⁻¹ := one_mul _

theorem intterm (x : ℝ) (n : ℕ) :
    (∫ t in x..2, gcm a n t) = prc a n * ((n:ℝ)^(-x) - (n:ℝ)^(-(2:ℝ))) := by
  simp only [gcm, ContinuousMap.coe_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [prc, Nat.not_prime_zero]
  · have hfac : (∫ t in x..2, prc a n * Real.log n * (n:ℝ)^(-t))
        = prc a n * ∫ t in x..2, Real.log (n:ℝ) * (n:ℝ)^(-t) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hfac, ftc_rpow (n:ℝ) (by exact_mod_cast hn) x]

theorem VW {x : ℝ} (hx : x ∈ Set.Ioc 1 2) :
    Vf a x = Vf a 2 + ∫ t in x..2, Wf a t := by
  have hx1 : 1 < x := hx.1
  have hx2 : x ≤ 2 := hx.2
  set K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc x 2, isCompact_uIcc⟩ with hK
  have hnormsum : Summable (fun n : ℕ => ‖(gcm a n).restrict K‖) :=
    (Wsummable (a := a) x hx1).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => gnorm_le x hx1 hx2 n)
  have hton := tsum_intervalIntegral_eq_of_summable_norm (a := x) (b := 2) hnormsum
  have hL : (∑' n : ℕ, ∫ t in x..2, gcm a n t) = Vf a x - Vf a 2 := by
    have hcong : (fun n : ℕ => ∫ t in x..2, gcm a n t)
        = (fun n : ℕ => prc a n * (n:ℝ)^(-x) - prc a n * (n:ℝ)^(-(2:ℝ))) := by
      funext n; rw [intterm]; ring
    rw [hcong, Summable.tsum_sub (Vfsummable (a := a) x hx1) (Vfsummable (a := a) 2 (by norm_num))]
    rfl
  have hR : (∫ t in x..2, ∑' n : ℕ, gcm a n t) = ∫ t in x..2, Wf a t := by
    simp only [Wf, gcm, ContinuousMap.coe_mk]
  rw [hL] at hton; rw [hR] at hton
  linarith [hton]

theorem Wint {x : ℝ} (hx : x ∈ Set.Ioc 1 2) :
    IntervalIntegrable (Wf a) MeasureTheory.volume x 2 := by
  have hx1 : 1 < x := hx.1
  have hx2 : x ≤ 2 := hx.2
  set K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc x 2, isCompact_uIcc⟩ with hK
  have hnormsum : Summable (fun n : ℕ => ‖(gcm a n).restrict K‖) :=
    (Wsummable (a := a) x hx1).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => gnorm_le x hx1 hx2 n)
  have hFsum : Summable (fun n : ℕ => (gcm a n).restrict K) := hnormsum.of_norm
  set S : C(K, ℝ) := ∑' n, (gcm a n).restrict K with hS
  have hSapp : ∀ p : K, S p = Wf a p.1 := by
    intro p
    have hmap := ContinuousLinearMap.map_tsum (ContinuousMap.evalCLM ℝ p) hFsum
    simp only [ContinuousMap.evalCLM_apply, hS] at hmap ⊢
    rw [hmap, Wf]
    exact tsum_congr (fun n => rfl)
  have hcont : ContinuousOn (Wf a) (Set.uIcc x 2) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.uIcc x 2).restrict (Wf a) = fun p : K => S p := by
      funext p; rw [hSapp]; rfl
    rw [heq]; exact S.continuous.comp continuous_id
  exact hcont.intervalIntegrable

theorem int_pole (c C : ℝ) (x : ℝ) (hx : 1 < x) (hx2 : x ≤ 2) :
    (∫ t in x..2, (c / (t - 1) - C)) = c * (- Real.log (x - 1)) - C * (2 - x) := by
  have hxpos : (0:ℝ) < x - 1 := by linarith
  have h1 : (∫ t in x..2, c / (t - 1)) = c * (- Real.log (x - 1)) := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_comp_sub_right (fun u => u⁻¹) 1,
        integral_inv_of_pos hxpos (by norm_num : (0:ℝ) < 2 - 1),
        show (2:ℝ) - 1 = 1 by norm_num, Real.log_div one_ne_zero (ne_of_gt hxpos), Real.log_one]
    ring
  have hint : IntervalIntegrable (fun t => c / (t - 1)) MeasureTheory.volume x 2 := by
    apply (continuousOn_const.div (by fun_prop) ?_).intervalIntegrable
    intro t ht; simp only [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
    exact ne_of_gt (by linarith [ht.1])
  rw [intervalIntegral.integral_sub hint (intervalIntegral.intervalIntegrable_const),
      h1, intervalIntegral.integral_const, smul_eq_mul]; ring

theorem int_pole_intble (c C : ℝ) (x : ℝ) (hx : 1 < x) (hx2 : x ≤ 2) :
    IntervalIntegrable (fun t => c / (t - 1) - C) MeasureTheory.volume x 2 := by
  apply IntervalIntegrable.sub _ (intervalIntegral.intervalIntegrable_const)
  apply (continuousOn_const.div (by fun_prop) ?_).intervalIntegrable
  intro t ht; simp only [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
  exact ne_of_gt (by linarith [ht.1])

theorem Vmono {x : ℝ} (hx : 1 ≤ x)
    (hsum : Summable (fun n : ℕ => prc a n / n)) : Vf a x ≤ Vf a 1 := by
  have hV1 : (fun n : ℕ => prc a n / n) = (fun n : ℕ => prc a n * (n:ℝ)^(-(1:ℝ))) := by
    funext n; rw [Real.rpow_neg_one]; ring
  have hle : ∀ n : ℕ, prc a n * (n:ℝ)^(-x) ≤ prc a n * (n:ℝ)^(-(1:ℝ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [prc, Nat.not_prime_zero]
    · refine mul_le_mul_of_nonneg_left ?_ (prc_nonneg a n)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have hsum' : Summable (fun n : ℕ => prc a n * (n:ℝ)^(-(1:ℝ))) := hV1 ▸ hsum
  have hnn : ∀ n : ℕ, 0 ≤ prc a n * (n:ℝ)^(-x) :=
    fun n => mul_nonneg (prc_nonneg a n) (Real.rpow_nonneg (by positivity) _)
  unfold Vf
  exact Summable.tsum_le_tsum hle (hsum'.of_nonneg_of_le hnn hle) hsum'

theorem bridge (hq : 1 < q) (ha : a = ((q - 1 : ℕ) : ZMod q))
    (H : Summable (fun p : {p : Nat // p.Prime ∧ p % q = q - 1} => (1 / (p.1 : ℝ)))) :
    Summable (fun n : ℕ => prc a n / n) := by
  have H2 : Summable ({p : ℕ | p.Prime ∧ p % q = q - 1}.indicator (fun p : ℕ => 1 / (p:ℝ))) :=
    (summable_subtype_iff_indicator (s := {p : ℕ | p.Prime ∧ p % q = q - 1})
      (f := fun n : ℕ => 1 / (n:ℝ))).mp H
  refine H2.congr (fun n => ?_)
  have hiff : ((n:ZMod q) = a) ↔ (n % q = q - 1) := by
    rw [ha, ZMod.natCast_eq_natCast_iff]; unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt (show q - 1 < q by omega)]
  unfold prc
  rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]
  by_cases hp : n.Prime ∧ n % q = q - 1
  · rw [if_pos hp, if_pos ⟨hp.1, hiff.mpr hp.2⟩]
  · rw [if_neg hp, if_neg (fun h => hp ⟨h.1, hiff.mp h.2⟩)]; simp

variable [NeZero q]

theorem Wpole (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ}, x ∈ Set.Ioc 1 2 → (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ Wf a x := by
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  have hBsum : Summable (fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n) :=
    summable_residueClass_non_primes_div a
  set B : ℝ := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / (n:ℝ) with hBdef
  refine ⟨C + B, fun {x} hx => ?_⟩
  have hx1 : 1 < x := hx.1
  have hRs := Rsum (a := a) x hx1
  have hnp : ∀ n : ℕ, 1 ≤ n → (n:ℝ) ≤ (n:ℝ)^x := by
    intro n hn
    have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    calc (n:ℝ) = (n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ (n:ℝ)^x := Real.rpow_le_rpow_of_exponent_le h1n hx1.le
  have hsplit : ∀ n : ℕ, residueClass a n / (n:ℝ)^x
      = (if n.Prime then residueClass a n else 0) / (n:ℝ)^x
        + (if n.Prime then 0 else residueClass a n) / (n:ℝ)^x := by
    intro n; by_cases hp : n.Prime <;> simp [hp]
  have hWs : Summable (fun n : ℕ => (if n.Prime then residueClass a n else 0) / (n:ℝ)^x) := by
    apply hRs.of_nonneg_of_le
      (fun n => div_nonneg (by split_ifs; exacts [residueClass_nonneg a n, le_refl 0]) (Real.rpow_nonneg (Nat.cast_nonneg n) x))
      (fun n => ?_)
    gcongr
    split_ifs
    · exact le_refl _
    · exact residueClass_nonneg a n
  have htle : ∀ n : ℕ, (if n.Prime then 0 else residueClass a n) / (n:ℝ)^x
      ≤ (if n.Prime then 0 else residueClass a n) / (n:ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · gcongr
      · split_ifs; exacts [le_refl 0, residueClass_nonneg a n]
      · exact hnp n hn
  have htails : Summable (fun n : ℕ => (if n.Prime then 0 else residueClass a n) / (n:ℝ)^x) := by
    apply hBsum.of_nonneg_of_le
      (fun n => div_nonneg (by split_ifs; exacts [le_refl 0, residueClass_nonneg a n]) (Real.rpow_nonneg (Nat.cast_nonneg n) x)) htle
  have hWval : Wf a x = ∑' n : ℕ, (if n.Prime then residueClass a n else 0) / (n:ℝ)^x := by
    unfold Wf; exact tsum_congr (fun n => Wf_summand x n)
  have hRsplit : (∑' n : ℕ, residueClass a n / (n:ℝ)^x)
      = Wf a x + ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / (n:ℝ)^x := by
    rw [hWval, ← Summable.tsum_add hWs htails]; exact tsum_congr hsplit
  have hpole := hC hx
  have htaille : (∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / (n:ℝ)^x) ≤ B :=
    Summable.tsum_le_tsum htle htails hBsum
  linarith [hpole, htaille, hRsplit]

theorem hunb
    (hVW : ∀ {x:ℝ}, x ∈ Set.Ioc 1 2 → Vf a x = Vf a 2 + ∫ t in x..2, Wf a t)
    (hWint : ∀ {x:ℝ}, x ∈ Set.Ioc 1 2 → IntervalIntegrable (Wf a) MeasureTheory.volume x 2)
    (C : ℝ) (hC : ∀ {x:ℝ}, x ∈ Set.Ioc 1 2 → (q.totient:ℝ)⁻¹/(x-1) - C ≤ Wf a x) :
    ∀ M : ℝ, ∃ x : ℝ, x ∈ Set.Ioc 1 2 ∧ M < Vf a x := by
  intro M
  have hcpos : (0:ℝ) < (q.totient:ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)); positivity
  set c : ℝ := (q.totient:ℝ)⁻¹ with hc
  set K : ℝ := (Vf a 2 - |C| - M) / c with hKd
  set ε : ℝ := min 1 (Real.exp (K - 1)) with hε
  have hεpos : 0 < ε := lt_min one_pos (Real.exp_pos _)
  have hεle : ε ≤ 1 := min_le_left _ _
  set x : ℝ := 1 + ε with hxd
  have hxmem : x ∈ Set.Ioc 1 2 := ⟨by linarith, by linarith⟩
  have hxm1 : x - 1 = ε := by rw [hxd]; ring
  refine ⟨x, hxmem, ?_⟩
  have hmono : (∫ t in x..2, (c/(t-1) - C)) ≤ ∫ t in x..2, Wf a t := by
    apply intervalIntegral.integral_mono_on hxmem.2 (int_pole_intble c C x hxmem.1 hxmem.2) (hWint hxmem)
    intro t ht
    exact hC ⟨by simp only [Set.mem_Icc] at ht; linarith [ht.1, hxmem.1], by
      simp only [Set.mem_Icc] at ht; linarith [ht.2]⟩
  have heval := int_pole c C x hxmem.1 hxmem.2
  rw [hxm1] at heval
  have hlog : Real.log ε ≤ K - 1 := by
    calc Real.log ε ≤ Real.log (Real.exp (K-1)) := Real.log_le_log hεpos (min_le_right _ _)
    _ = K - 1 := Real.log_exp _
  have hcK : c * K = Vf a 2 - |C| - M := by rw [hKd]; field_simp
  have hCbound : -C * (2 - x) ≥ -|C| := by
    have h2x : (0:ℝ) ≤ 2 - x := by linarith [hxmem.2]
    have h2x1 : 2 - x ≤ 1 := by linarith [hxmem.1]
    nlinarith [abs_nonneg C, neg_abs_le C, le_abs_self C]
  rw [hVW hxmem]
  have h3 : Vf a 2 + (c * (-Real.log ε) - C * (2 - x)) ≤ Vf a 2 + ∫ t in x..2, Wf a t := by
    rw [← heval]; linarith [hmono]
  have h4 : M + c ≤ Vf a 2 + (c * (-Real.log ε) - C * (2 - x)) := by
    have hc2 : c * (-Real.log ε) ≥ -(c * (K-1)) := by nlinarith [hlog, hcpos]
    nlinarith [hc2, hCbound, hcK]
  linarith [h3, h4, hcpos]

theorem main (hq : 1 < q) :
    ¬ Summable (fun p : {p : Nat // p.Prime ∧ p % q = q - 1} => (1 / (p.1 : ℝ))) := by
  set a : ZMod q := ((q - 1 : ℕ) : ZMod q) with ha_def
  have ha : IsUnit a := by
    have h : a = -1 := by
      rw [ha_def]; push_cast [Nat.cast_sub (by omega : 1 ≤ q)]; simp
    rw [h]; exact isUnit_one.neg
  intro H
  have hsum : Summable (fun n : ℕ => prc a n / n) := bridge hq ha_def H
  obtain ⟨C, hC⟩ := Wpole ha
  have hunbd := hunb (a := a) (fun {x} hx => VW hx) (fun {x} hx => Wint hx) C hC
  obtain ⟨x, hx, hM⟩ := hunbd (Vf a 1)
  exact absurd (Vmono (a := a) hx.1.le hsum) (not_le.mpr hM)

end Principia.Erdos1054.Proofs.InputsStd.A1

end A1

namespace Principia.Erdos1054.Proofs.InputsStd

/-- **`Std_recipPrimesAP_diverges`, unconditionally**: for every prime power `q`, the reciprocals
of the primes `≡ −1 (mod q)` diverge. From the ported `A1.main` (every `q > 1`). -/
theorem recipPrimesAP_diverges : Principia.Erdos1054.Std_recipPrimesAP_diverges := by
  intro q hq H
  have hq1 : 1 < q := hq.one_lt
  haveI : NeZero q := ⟨by omega⟩
  apply A1.main hq1
  have H2 : Summable ({p : ℕ | p.Prime ∧ p % q = q - 1}.indicator (fun p : ℕ => 1 / (p : ℝ))) := by
    refine H.congr (fun n => ?_)
    by_cases h : n.Prime ∧ n % q = q - 1
    · rw [if_pos h, Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p % q = q - 1} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime ∧ p % q = q - 1} from h)]
  exact (summable_subtype_iff_indicator (s := {p : ℕ | p.Prime ∧ p % q = q - 1})
    (f := fun n : ℕ => 1 / (n : ℝ))).mpr H2

end Principia.Erdos1054.Proofs.InputsStd

namespace Principia.Erdos1054.Proofs

open Filter Topology
open Principia.Erdos1054.Proofs.InputsStd

/-! ## The obligations -/

/-- **Mertens' second theorem** (input `Std_Mertens2`), from the ported `Mertens.E₂p.abs_le`. -/
theorem input_Std_Mertens2 : Principia.Erdos1054.Std_Mertens2 := by
  refine ⟨Mertens.M, Real.log 4 + 6 + Mertens.E₁, fun x hx => ?_⟩
  rw [filter_prime_Iic_eq_Ioc]
  exact Mertens.E₂p.abs_le hx

/-- **Mertens' product theorem** (input `Std_Mertens3`), from the ported
`Mertens.prod_one_minus_div_prime_eq` and `Mertens.E₃.bound'`. -/
theorem input_Std_Mertens3 : Principia.Erdos1054.Std_Mertens3 := by
  have hE : Filter.Tendsto Mertens.E₃ Filter.atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hexp : Filter.Tendsto (fun y => Real.exp (Mertens.E₃ y)) Filter.atTop
      (nhds (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp hE
  rw [Real.exp_zero] at hexp
  have hlim : Filter.Tendsto
      (fun y => Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ y))
      Filter.atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    have h := hexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
    rw [mul_one] at h
    exact h
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with y hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  simp only [Principia.Erdos1054.Delta]
  rw [filter_prime_range_eq_Ioc, Mertens.prod_one_minus_div_prime_eq hy,
    div_mul_cancel₀ _ hlog.ne']

/-- **Pollack's Lemma 2.4 at `λ₁ = λ₂ = 1`** (input `Cite_Pollack_Lemma24`), from the ported
Halberstam–Richert mean-value bound `pollack_mean_value_arithmeticFunction`. -/
theorem input_Cite_Pollack_Lemma24 : Principia.Erdos1054.Cite_Pollack_Lemma24 := by
  obtain ⟨C, -, hmain⟩ :=
    Principia.Common.HalberstamRichert.pollack_mean_value_arithmeticFunction
  refine ⟨C, fun f hf hnn hle x hx => ?_⟩
  rw [filter_prime_Iic_eq_primesLE]
  exact hmain f hf (fun p k hp hk => ⟨hnn _, hle p k hp hk⟩) x hx

/-- **The divisor bound** (input `Std_divisorBound`): `τ(n) ≤ C_ε n^ε`, from
`τ(n) = ∏_{p^a ‖ n} (a + 1)` and `prime_pow_bound` factor by factor. -/
theorem input_Std_divisorBound : Principia.Erdos1054.Std_divisorBound := by
  intro ε hε
  obtain ⟨B, hB1, M, hbound⟩ := prime_pow_bound ε hε
  refine ⟨B ^ M, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hfac := Nat.prod_factorization_pow_eq_self hn0
  simp only [Finsupp.prod, Nat.support_factorization] at hfac
  have hn_eq : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    calc (n : ℝ) = ((∏ p ∈ n.primeFactors, p ^ (n.factorization p) : ℕ) : ℝ) := by
          rw [hfac]
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
          rw [Nat.cast_prod]
          exact Finset.prod_congr rfl (fun p _ => Nat.cast_pow p _)
  rw [Nat.card_divisors hn0, hn_eq,
    ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  push_cast
  have hcard : (n.primeFactors.filter (· < M)).card ≤ M := by
    calc (n.primeFactors.filter (· < M)).card ≤ (Finset.range M).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr hp.2
      _ = M := Finset.card_range M
  have hw : ∏ p ∈ n.primeFactors, (if p < M then B else 1) ≤ B ^ M := by
    rw [← Finset.prod_filter, Finset.prod_const]
    exact pow_le_pow_right₀ hB1 hcard
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if p < M then B else 1) * ((p : ℝ) ^ (n.factorization p)) ^ ε) :=
        Finset.prod_le_prod (fun p _ => by positivity)
          (fun p hp => hbound p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, (if p < M then B else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ ε :=
        Finset.prod_mul_distrib
    _ ≤ B ^ M * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ ε :=
        mul_le_mul_of_nonneg_right hw (Finset.prod_nonneg fun p _ => by positivity)

/-- **Mertens' first theorem in the form used** (leaf `Std_Mertens1`):
`∑_{p ≤ y} log p/(p − 1) ≪ log y`, from `log p/(p − 1) ≤ 2 log p/p` and the ported
`Mertens.sum_log_prime_div_eq_log`. -/
theorem leaf_Std_Mertens1 : Principia.Erdos1054.Std_Mertens1 := by
  refine ⟨2 + 2 * ((Real.log 4 + 4) / Real.log 2), fun y hy => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl4 : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hM := Mertens.sum_log_prime_div_eq_log (show (1 : ℝ) ≤ y by linarith)
  have hMu := (abs_le.mp hM).2
  rw [filter_prime_Iic_eq_Ioc]
  have hterm : ∀ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime,
      Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((p : ℝ) / 2) :=
          div_le_div_of_nonneg_left hlogp (by linarith) (by linarith)
      _ = 2 * (Real.log p / p) := by ring
  have hkey : Real.log 4 + 4 ≤ ((Real.log 4 + 4) / Real.log 2) * Real.log y := by
    calc Real.log 4 + 4 = ((Real.log 4 + 4) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ ((Real.log 4 + 4) / Real.log 2) * Real.log y :=
          mul_le_mul_of_nonneg_left hly (div_nonneg hl4 hl2.le)
  calc ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, 2 * (Real.log p / p) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, Real.log p / p := by
        rw [Finset.mul_sum]
    _ ≤ (2 + 2 * ((Real.log 4 + 4) / Real.log 2)) * Real.log y := by
        nlinarith [hMu, hkey]

/-- **The prime number theorem `ψ(x) ∼ x`** (link `Std_PNT`), from the `Q = 1` case of
`Std_PNT_AP`, Mathlib's `π − θ/log = O(x/log² x)` and `|ψ − θ| ≤ 2 √x log x`. -/
theorem link_Std_PNT : Principia.Erdos1054.Spine.Link_Std_PNT := by
  intro hAP
  have hθ := theta_div_tendsto (primeCounting_tendsto hAP)
  have h := hθ.add psi_sub_theta_div_tendsto
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
  ring

/-- **Primes in dyadic intervals** (link `Std_primes_dyadic_lower`): `π(2t) − π(t) ≫ t/log t`
for `t ≥ 2`, from the `Q = 1` case of `Std_PNT_AP` for large `t` and Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`) on the bounded range. -/
theorem link_Std_primes_dyadic_lower : Principia.Erdos1054.Spine.Link_Std_primes_dyadic_lower := by
  intro hAP
  have hπ := primeCounting_tendsto hAP
  have hg2 : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop two_pos
  have hπ2 : Tendsto (fun t : ℝ => (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) * Real.log (2 * t) / (2 * t))
      atTop (𝓝 1) := hπ.comp hg2
  have hL : Tendsto (fun t : ℝ => 2 / (1 + Real.log 2 / Real.log t)) atTop (𝓝 2) := by
    have h0 : Tendsto (fun t : ℝ => Real.log 2 / Real.log t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).add h0
    rw [add_zero] at h1
    have h2 := (tendsto_const_nhds (x := (2 : ℝ))).div h1 one_ne_zero
    rw [div_one] at h2
    exact h2
  have hmain := (hπ2.mul hL).sub hπ
  rw [one_mul, show (2 : ℝ) - 1 = 1 by norm_num] at hmain
  have hev : ∀ᶠ t : ℝ in atTop, (1 : ℝ) / 2 <
      ((Nat.primeCounting ⌊2 * t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ)) * Real.log t / t := by
    have hlt := (tendsto_order.1 hmain).1 (1 / 2) (by norm_num)
    filter_upwards [hlt, eventually_gt_atTop (1 : ℝ)] with t ht ht1
    have hl : 0 < Real.log t := Real.log_pos ht1
    have ht0 : 0 < t := by linarith
    have hl2t : Real.log (2 * t) = Real.log 2 + Real.log t :=
      Real.log_mul (by norm_num) ht0.ne'
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have heq : (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) * Real.log (2 * t) / (2 * t) *
          (2 / (1 + Real.log 2 / Real.log t)) - (Nat.primeCounting ⌊t⌋₊ : ℝ) * Real.log t / t =
        ((Nat.primeCounting ⌊2 * t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ)) * Real.log t / t := by
      rw [hl2t]
      field_simp
      ring
    rw [← heq]
    exact ht
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hev
  set T : ℝ := max t₀ 2 with hTdef
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 2) (Real.log 2 / T), lt_min (by norm_num) (div_pos hl2 (by linarith)),
    fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hq : 0 ≤ t / Real.log t := div_nonneg ht0.le hlt.le
  by_cases htT : T ≤ t
  · have hgt := ht₀ t (le_trans (le_max_left _ _) htT)
    rw [lt_div_iff₀ ht0] at hgt
    rw [mul_div_assoc]
    calc min (1 / 2) (Real.log 2 / T) * (t / Real.log t) ≤ 1 / 2 * (t / Real.log t) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hq
      _ ≤ (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
          rw [← mul_div_assoc, div_le_iff₀ hlt]
          linarith
  · rw [not_le] at htT
    -- Bertrand: a prime in `(⌊t⌋, 2⌊t⌋] ⊆ (⌊t⌋, ⌊2t⌋]`.
    have hn0 : ⌊t⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by norm_num; linarith)
      omega
    obtain ⟨p, hp, hlt1, hle1⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊t⌋₊ hn0
    have hfl : 2 * ⌊t⌋₊ ≤ ⌊2 * t⌋₊ := by
      apply Nat.le_floor
      push_cast
      have := Nat.floor_le ht0.le
      linarith
    have hsub : Nat.primesLE ⌊t⌋₊ ⊂ Nat.primesLE ⌊2 * t⌋₊ := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨p, Nat.mem_primesLE.mpr ⟨le_trans hle1 hfl, hp⟩, ?_⟩
        intro hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
      · intro r hr
        have hr' := Nat.mem_primesLE.mp hr
        exact Nat.mem_primesLE.mpr ⟨le_trans hr'.1 (le_trans (by omega) hfl), hr'.2⟩
    have hcard := Finset.card_lt_card hsub
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard
    have hdiff : (1 : ℝ) ≤ (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
      have : (Nat.primeCounting ⌊t⌋₊ : ℝ) + 1 ≤ (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) := by
        exact_mod_cast hcard
      linarith
    have hbound : t / Real.log t ≤ T / Real.log 2 := by
      have hl2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      calc t / Real.log t ≤ T / Real.log t := div_le_div_of_nonneg_right htT.le hlt.le
        _ ≤ T / Real.log 2 := div_le_div_of_nonneg_left (by linarith) hl2 hl2t
    rw [mul_div_assoc]
    calc min (1 / 2) (Real.log 2 / T) * (t / Real.log t)
        ≤ Real.log 2 / T * (T / Real.log 2) :=
          mul_le_mul (min_le_right _ _) hbound hq (div_nonneg hl2.le (by linarith))
      _ = 1 := by field_simp
      _ ≤ _ := hdiff


/-- **The primes `≡ −1 (mod q)` have divergent reciprocal sum** (leaf
`Std_recipPrimesAP_diverges`). It holds unconditionally (`recipPrimesAP_diverges`, the ported
axiom-free `A1proof.main`), so the spine takes it as a leaf; the paper's route through
`Std_PNT_AP` (lines 476–478) is not needed (LEAN-PROGRESS F7). -/
theorem leaf_Std_recipPrimesAP_diverges : Principia.Erdos1054.Std_recipPrimesAP_diverges :=
  InputsStd.recipPrimesAP_diverges

end Principia.Erdos1054.Proofs
