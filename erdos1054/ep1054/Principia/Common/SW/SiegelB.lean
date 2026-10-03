/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.SiegelA

/-!
# Siegel–Walfisz, `SiegelB`: Siegel's theorem, part B: Abel summation, zeta truncation, the Goldfeld master inequality

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 6668–9336; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
built in the PrimeNumberTheoremAnd workspace on Mathlib `db127794`, one day from ours). The master
imported `Mathlib`, `PrimeNumberTheoremAnd.MediumPNT` and `PrimeNumberTheoremAnd.PerronFormula`; here
the Mathlib imports are narrowed, the two Perron-kernel shims are re-proved from Mathlib's Mellin
inversion (`Principia.Common.SW.PerronKernel`), and the `medium_PNT` shim is not ported (see
`MediumPNTBound` in `Principia.Common.SW.Rate`). Declarations live in `Principia.Common.SW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter

namespace Principia.Common.SW

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/

/-- The weighted telescope: `Σ_{n≤x} n(wₙ − wₙ₊₁) = Σ_{n≤x} wₙ − x·w_{x+1}` (real). -/
lemma weighted_telescope (w : ℕ → ℝ) : ∀ x : ℕ,
    ∑ n ∈ Icc 1 x, (n : ℝ) * (w n - w (n + 1))
      = ∑ n ∈ Icc 1 x, w n - (x : ℝ) * w (x + 1) := by
  intro x
  induction x with
  | zero => simp
  | succ p ih =>
    have hstep : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hstep, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih]
    push_cast
    ring

/-- **The partial-sum series representation** (Siegel brick A2g-ii): for linearly
    bounded partial sums `‖A(x)‖ ≤ Cx` and `Re s > 1`,
    `Σ' n, a(n)n^{−s} = Σ' n, A(n)(n^{−s} − (n+1)^{−s})` — the boundary term
    `A(x)x^{−s}` dies and the Abel-rearranged series converges to the L-series. -/
theorem lseries_eq_tsum_abel (a : ℕ → ℂ) (C : ℝ)
    (hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ C * x)
    {s : ℂ} (hs : 1 < s.re) (hsum : LSeriesSummable a s) :
    LSeries a s
      = ∑' n : ℕ, (∑ m ∈ Icc 1 n, a m) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
  -- the partial sums of the L-series along Icc 1 x
  have hterm_eq : ∀ n : ℕ, 1 ≤ n → LSeries.term a s n = a n * ((n:ℂ)) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  have hpartial : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
      atTop (nhds (LSeries a s)) := by
    have h1 : Tendsto (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n)
        atTop (nhds (LSeries a s)) := by
      have := hsum.hasSum.tendsto_sum_nat
      exact this.comp (tendsto_add_atTop_nat 1)
    have h2 : ∀ x : ℕ, ∑ n ∈ range (x + 1), LSeries.term a s n
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s) := by
      intro x
      rw [show range (x + 1) = insert 0 (Icc 1 x) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [LSeries.term_zero, zero_add]
      exact Finset.sum_congr rfl (fun n hn => hterm_eq n (Finset.mem_Icc.mp hn).1)
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
        = (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n) from
      funext (fun x => (h2 x).symm)]
    exact h1
  -- boundary decay: A(x)·x^{−s} → 0
  have hboundary : Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s))
      atTop (nhds 0) := by
    have hC0 : 0 ≤ C := by
      have h0 := hC 1
      have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
      have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
      linarith [h0, h1, h2.le, h2.ge]
    have hbnd : ∀ x : ℕ, ‖(∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s)‖
        ≤ C * ((x:ℝ)) ^ (1 - s.re) := by
      intro x
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
          Finset.sum_empty, zero_mul, norm_zero, Nat.cast_zero,
          Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0), mul_zero]
      · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hx0, Complex.neg_re]
        have hxr : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx0
        calc ‖∑ n ∈ Icc 1 x, a n‖ * ((x:ℝ)) ^ (-s.re)
            ≤ (C * x) * ((x:ℝ)) ^ (-s.re) := by
              apply mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg hxr.le _)
          _ = C * ((x:ℝ)) ^ (1 - s.re) := by
              rw [show (1:ℝ) - s.re = 1 + (-s.re) by ring, Real.rpow_add hxr,
                Real.rpow_one]
              ring
    have hg0 : Tendsto (fun x : ℕ => C * ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℕ => ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := this.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      simpa using h1.const_mul C
    exact squeeze_zero_norm hbnd hg0
  -- Abel + limits
  have hAbel : ∀ x : ℕ, 1 ≤ x →
      ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
        - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
    intro x hx
    have := abel_initial a (fun n => ((n:ℂ)) ^ (-s)) x hx
    push_cast at this ⊢
    linear_combination -this
  have hlim : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop (nhds (LSeries a s)) := by
    have heq : ∀ᶠ x : ℕ in atTop, ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
          - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      exact hAbel x hx
    rw [Filter.tendsto_congr' heq]
    have := hpartial.sub hboundary
    simpa using this
  -- absolute convergence via the real difference kernel
  have hC0' : 0 ≤ C := by
    have h0 := hC 1
    have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  have hsummable : Summable (fun n : ℕ => (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
    have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
      intro n hn
      rw [hw]
      simp only
      apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
      linarith
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
    · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
      · intro n
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp
        · apply mul_nonneg (by positivity)
          apply mul_nonneg (Nat.cast_nonneg n)
          linarith [hwanti n hn0]
      · intro x
        have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
            = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
          rw [Finset.mul_sum]
          rcases Nat.eq_zero_or_pos x with rfl | hx0
          · simp
          · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
              ext m
              simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
              omega]
            rw [Finset.sum_insert (by simp)]
            simp
        rw [hIcc, weighted_telescope w (x - 1)]
        have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
          apply mul_nonneg (Nat.cast_nonneg _)
          rw [hw]
          simp only
          positivity
        have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
          have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
            intro n hn
            obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
            rw [hw]
            simp only
            rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
          rw [Finset.sum_congr rfl hterm]
          calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
              ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
                Summable.sum_le_tsum _ (fun n _ => by positivity)
                  (Real.summable_one_div_nat_rpow.mpr hs)
            _ ≤ s.re / (s.re - 1) := tsum_one_div_nat_rpow_le s.re hs
        have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
        apply mul_le_mul_of_nonneg_left _ hfac
        linarith [hsums, htail]
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · rw [norm_mul]
        have h1 := hC n
        have h2 := cpow_diff_kernel_bound n hn0 s hσ0
        calc ‖∑ m ∈ Icc 1 n, a m‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
            ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
              apply mul_le_mul h1 h2 (norm_nonneg _)
              positivity
          _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
              rw [hw]
              simp only
              push_cast
              ring
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hIccrange : ∀ x : ℕ, ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.sum_empty, zero_mul, zero_add]
  have hrange' : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop
      (nhds (∑' n : ℕ, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))) := by
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
        = (fun x : ℕ => ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) from
      funext (fun x => (hIccrange x).symm)]
    exact hrange
  exact (tendsto_nhds_unique hrange' hlim).symm

/-- **The Abel identity sums to ζ** (Siegel brick A2g-iii-b):
    `Σ' n·(n^{−s} − (n+1)^{−s}) = ζ(s)` on `Re s > 1` — the λ-part of the
    continuation `G` is Mathlib's `riemannZeta`, pole included. -/
theorem tsum_abel_id_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, ((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) = riemannZeta s := by
  set a : ℕ → ℂ := fun n => if n = 0 then 0 else 1 with ha
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp only [Complex.zero_re] at hs
    linarith
  have hA : ∀ x : ℕ, ∑ n ∈ Icc 1 x, a n = (x : ℂ) := by
    intro x
    have hterm : ∀ n ∈ Icc 1 x, a n = 1 := by
      intro n hn
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
      rw [ha]
      simp only [if_neg (by omega : ¬ n = 0)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
  have hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ 1 * x := by
    intro x
    rw [hA x, one_mul, Complex.norm_natCast]
  have hsummable : LSeriesSummable a s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n _
    rw [ha]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [if_neg hn]
  have hLS : LSeries a s = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs, LSeries]
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      rw [Nat.cast_zero, Complex.zero_cpow hs0, div_zero]
    · rw [LSeries.term_of_ne_zero hn, ha]
      simp only [if_neg hn]
  have habel := lseries_eq_tsum_abel a 1 hC hs hsummable
  rw [hLS] at habel
  rw [habel]
  apply tsum_congr
  intro n
  rw [hA n]

/-- Bernoulli for negative real exponents (Siegel brick A2g-a1-i):
    `(1+u)^{−σ} ≥ 1 − σu` for `u, σ ≥ 0` — from `(1−x)eˣ ≤ 1` and `log(1+u) ≤ u`. -/
lemma rpow_neg_ge_one_sub (u σ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ) :
    1 - σ * u ≤ (1 + u) ^ (-σ) := by
  by_cases hbig : 1 ≤ σ * u
  · -- trivial: LHS ≤ 0 ≤ RHS
    have h1 : (0:ℝ) < 1 + u := by linarith
    have h2 : (0:ℝ) ≤ (1 + u) ^ (-σ) := Real.rpow_nonneg h1.le _
    linarith
  · -- (1+u)^σ ≤ e^{σu} ≤ 1/(1−σu)
    push_neg at hbig
    have hsmall : σ * u < 1 := hbig
    have h1 : (0:ℝ) < 1 + u := by linarith
    have hlog : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos h1
      linarith
    have hpow : (1 + u) ^ σ ≤ Real.exp (σ * u) := by
      rw [Real.rpow_def_of_pos h1]
      apply Real.exp_le_exp.mpr
      calc Real.log (1 + u) * σ ≤ u * σ := mul_le_mul_of_nonneg_right hlog hσ
        _ = σ * u := mul_comm _ _
    have hexp : Real.exp (σ * u) * (1 - σ * u) ≤ 1 := by
      have h2 := Real.add_one_le_exp (-(σ * u))
      have h3 : (0:ℝ) < Real.exp (σ * u) := Real.exp_pos _
      have h4 : Real.exp (-(σ * u)) = 1 / Real.exp (σ * u) := by
        rw [Real.exp_neg, one_div]
      rw [h4, le_div_iff₀ h3] at h2
      nlinarith [h2]
    have hposσu : (0:ℝ) < 1 - σ * u := by linarith
    have hpow0 : (0:ℝ) < (1 + u) ^ σ := Real.rpow_pos_of_pos h1 _
    rw [Real.rpow_neg h1.le, le_inv_comm₀ hposσu hpow0]
    calc (1 + u) ^ σ ≤ Real.exp (σ * u) := hpow
      _ ≤ 1 / (1 - σ * u) := by
          rw [le_div_iff₀ hposσu]
          exact hexp
      _ = (1 - σ * u)⁻¹ := one_div _

/-- **The kernel decay bound** (Siegel brick A2g-a1): for `σ ≥ 0` and `n ≥ 1`,
    `n^{−σ} − (n+1)^{−σ} ≤ σ·n^{−σ−1}` — the uniform-in-window majorant. -/
lemma rpow_diff_le (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 ≤ σ) :
    (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ σ * (n : ℝ) ^ (-σ - 1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hu : (0:ℝ) ≤ 1 / n := by positivity
  have hb := rpow_neg_ge_one_sub (1 / n) σ hu hσ
  have hsplit : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * (1 + 1 / n) := by
    push_cast
    field_simp
  have hmul : ((n + 1 : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ) := by
    rw [hsplit, Real.mul_rpow hn0.le (by positivity)]
  rw [hmul]
  have hnσ : (0:ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
  have hkey : (n : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ)
      ≤ (n : ℝ) ^ (-σ) * (σ * (1 / n)) := by
    have h1 : (n : ℝ) ^ (-σ) * (1 - σ * (1 / n)) ≤ (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ) :=
      mul_le_mul_of_nonneg_left hb hnσ.le
    nlinarith [h1]
  calc (n : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ)
      ≤ (n : ℝ) ^ (-σ) * (σ * (1 / n)) := hkey
    _ = σ * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-(1:ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
    _ = σ * (n : ℝ) ^ (-σ - 1) := by
        rw [← Real.rpow_add hn0]
        ring_nf

/-- **The E-series is differentiable on `Re s > 9/10`** (Siegel brick A2g-a2): with
    `|E(n)| ≤ C·n^{3/4}(1+log n)` and `E(0) = 0`, the series
    `s ↦ Σ' E(n)(n^{−s} − (n+1)^{−s})` is differentiable at every point of the
    half-plane — the analytic error part of the continuation `G`, via Mathlib's
    Weierstrass M-test `differentiableOn_tsum_of_summable_norm` on windows. -/
theorem eseries_differentiableAt (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) :
    DifferentiableAt ℂ (fun s => ∑' n : ℕ,
      ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) s₀ := by
  set σ₀ : ℝ := (9/10 + s₀.re) / 2 with hσ₀
  have hσ₀1 : 9/10 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀2 : σ₀ < s₀.re := by rw [hσ₀]; linarith
  set R : ℝ := ‖s₀‖ + 1 with hR
  have hR0 : 0 < R := by
    rw [hR]
    have := norm_nonneg s₀
    linarith
  set U : Set ℂ := {s : ℂ | σ₀ < s.re} ∩ Metric.ball 0 R with hU
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := by
    rw [hU]
    constructor
    · exact hσ₀2
    · rw [Metric.mem_ball, dist_zero_right, hR]
      linarith
  -- the majorant
  set u : ℕ → ℝ := fun n => if n = 0 then 0 else
    C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) with hu
  have hmajsum : Summable (fun n : ℕ => (9 * C * R) * (1 / ((n:ℝ)) ^ (σ₀ + 1/8))) :=
    Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
  have husum : Summable u := by
    apply Summable.of_nonneg_of_le _ _ hmajsum
    · intro n
      rw [hu]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp only [if_neg hn]
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          exact_mod_cast this
        have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1
          linarith
        positivity
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [hu]
        simp only [if_pos rfl]
        positivity
      · rw [hu]
        simp only [if_neg hn]
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          exact_mod_cast this
        have hn0 : (0:ℝ) < (n:ℝ) := by linarith
        -- (1 + log n) ≤ 9 n^{1/8}
        have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
          have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
            Real.log_le_rpow_div hn0.le (by norm_num)
          have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
          have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
            Real.one_le_rpow hn1 (by norm_num)
          linarith [h1, h2.le, h2.ge, h3]
        -- collect exponents: 3/4 + 1/8 − σ₀ − 1 = −(σ₀ + 1/8)
        have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-σ₀ - 1)
            = ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
          ring_nf
        have hfinal : C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
            ≤ (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by
          calc C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
              ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ hC0
                apply mul_le_mul_of_nonneg_left hlogbound (by positivity)
            _ = (9 * C * R) * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-σ₀ - 1)) := by
                ring
            _ = (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by rw [hcollect]
        calc C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
            ≤ (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := hfinal
          _ = (9 * C * R) * (1 / ((n:ℝ)) ^ (σ₀ + 1/8)) := by
              rw [Real.rpow_neg hn0.le]
              ring
  -- pointwise bounds on U
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w))‖ ≤ u n := by
    intro n w hw
    obtain ⟨hwre, hwball⟩ := hw
    have hwre' : σ₀ < w.re := hwre
    have hwσ : (0:ℝ) < w.re := by linarith
    have hwnorm : ‖w‖ ≤ R := by
      rw [Metric.mem_ball, dist_zero_right] at hwball
      linarith
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero, hu, if_pos rfl]
      exact le_refl 0
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      rw [hu]
      simp only [if_neg hn]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hE n hn1
      have h2 := cpow_diff_kernel_bound n hn1 w hwσ
      have h3 := rpow_diff_le n hn1 w.re hwσ.le
      have hker : ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖ ≤ R * ((n:ℝ)) ^ (-σ₀ - 1) := by
        have hstep : (‖w‖ / w.re) * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re))
            ≤ (‖w‖ / w.re) * (w.re * (n : ℝ) ^ (-w.re - 1)) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
        have hsimp : (‖w‖ / w.re) * (w.re * (n : ℝ) ^ (-w.re - 1))
            = ‖w‖ * (n : ℝ) ^ (-w.re - 1) := by
          field_simp
        have hmono : ((n:ℝ)) ^ (-w.re - 1) ≤ ((n:ℝ)) ^ (-σ₀ - 1) := by
          apply Real.rpow_le_rpow_of_exponent_le hn1r
          linarith
        calc ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖
            ≤ (‖w‖ / w.re) * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re)) := h2
          _ ≤ ‖w‖ * ((n:ℝ)) ^ (-w.re - 1) := by
              rw [← hsimp]
              exact hstep
          _ ≤ R * ((n:ℝ)) ^ (-σ₀ - 1) := by
              apply mul_le_mul hwnorm hmono (by positivity) hR0.le
      have hEnn : (0:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
        have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1r
          linarith
        positivity
      calc |E n| * ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖
          ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) :=
            mul_le_mul h1 hker (norm_nonneg _) hEnn
        _ = C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) := by
            ring
  -- termwise differentiability on U
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s => ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) U := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul]
      exact differentiableOn_const 0
    · have hn0 : ((n:ℂ)) ≠ 0 := by exact_mod_cast hn
      have hn10 : (((n + 1 : ℕ):ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply DifferentiableOn.const_mul
      apply DifferentiableOn.sub
      · exact ((Differentiable.neg differentiable_id).const_cpow
          (Or.inl hn0)).differentiableOn
      · exact ((Differentiable.neg differentiable_id).const_cpow
          (Or.inl hn10)).differentiableOn
  -- assemble
  have hDon := Complex.differentiableOn_tsum_of_summable_norm husum hdiff hUopen hbound
  exact (hDon.differentiableAt (hUopen.mem_nhds hs₀U))

/-- Linear-growth sequences give absolutely convergent Abel series (A2g-c-i):
    the summability half of `lseries_eq_tsum_abel`, exposed standalone. -/
lemma abel_tsum_summable (b : ℕ → ℂ) (C : ℝ)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ C * n)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => b n * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
  have hC0 : 0 ≤ C := by
    have h0 := hb 1
    have h1 : (0:ℝ) ≤ ‖b 1‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
  have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    rw [hw]
    simp only
    apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
    linarith
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
  · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · apply mul_nonneg (by positivity)
        apply mul_nonneg (Nat.cast_nonneg n)
        linarith [hwanti n hn0]
    · intro x
      have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
          = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
        rw [Finset.mul_sum]
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · simp
        · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
            ext m
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega]
          rw [Finset.sum_insert (by simp)]
          simp
      rw [hIcc, weighted_telescope w (x - 1)]
      have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [hw]
        simp only
        positivity
      have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
        have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
          intro n hn
          obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
          rw [hw]
          simp only
          rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
        rw [Finset.sum_congr rfl hterm]
        calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
            ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
              Summable.sum_le_tsum _ (fun n _ => by positivity)
                (Real.summable_one_div_nat_rpow.mpr hs)
          _ ≤ s.re / (s.re - 1) := tsum_one_div_nat_rpow_le s.re hs
      have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
      apply mul_le_mul_of_nonneg_left _ hfac
      linarith [hsums, htail]
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hb0 : ‖b 0‖ = 0 := by
        have h := hb 0
        have h2 : C * ((0:ℕ):ℝ) = 0 := by norm_num
        have := norm_nonneg (b 0)
        linarith [h, h2.le, h2.ge]
      rw [norm_mul, hb0, zero_mul]
      have hrhs : (C * (‖s‖ / s.re)) * (((0:ℕ):ℝ) * (w 0 - w (0 + 1))) = 0 := by
        norm_num
      rw [hrhs]
    · rw [norm_mul]
      have h1 := hb n
      have h2 := cpow_diff_kernel_bound n hn0 s hσ0
      calc ‖b n‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
          ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            apply mul_le_mul h1 h2 (norm_nonneg _)
            positivity
        _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
            rw [hw]
            simp only
            push_cast
            ring

/-- **The continuation identity on `Re s > 1`** (Siegel brick A2g-c): with
    `A(n) = λn + E(n)` (linear main term + controlled error), the L-series equals
    `λ·ζ(s) + Σ' E(n)Δₙ(s)` — the function `G` that continues it to `Re > 9/10`. -/
theorem lseries_eq_G (a : ℕ → ℂ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = (lam * n : ℝ) + E n)
    (hEb : ∀ n : ℕ, |E n| ≤ C * n)
    {s : ℂ} (hs : 1 < s.re) (hsum : LSeriesSummable a s) :
    LSeries a s = (lam : ℂ) * riemannZeta s
      + ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
  have hC0 : 0 ≤ C := by
    have h0 := hEb 1
    have h1 : (0:ℝ) ≤ |E 1| := abs_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  -- the A-partial sums are linearly bounded
  have hA : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ (|lam| + C) * x := by
    intro x
    rw [hAE x]
    calc ‖((lam * x : ℝ) : ℂ) + ((E x : ℝ) : ℂ)‖
        ≤ ‖((lam * x : ℝ) : ℂ)‖ + ‖((E x : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |lam * x| + |E x| := by
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |lam| * x + C * x := by
          apply add_le_add
          · rw [abs_mul, Nat.abs_cast]
          · exact hEb x
      _ = (|lam| + C) * x := by ring
  rw [lseries_eq_tsum_abel a (|lam| + C) hA hs hsum]
  -- split the tsum
  have hsplit : ∀ n : ℕ, (∑ m ∈ Icc 1 n, a m) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = (lam : ℂ) * (((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
        + ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
    intro n
    rw [hAE n]
    push_cast
    ring
  rw [tsum_congr hsplit]
  -- summabilities for tsum_add
  have hid : Summable (fun n : ℕ =>
      ((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    apply abel_tsum_summable (fun n : ℕ => ((n:ℂ))) 1 _ hs
    intro n
    rw [Complex.norm_natCast, one_mul]
  have hsum1 : Summable (fun n : ℕ => (lam : ℂ)
      * (((n:ℂ)) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))) :=
    hid.mul_left ((lam : ℝ) : ℂ)
  have hsum2 : Summable (fun n : ℕ =>
      ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    apply abel_tsum_summable (fun n : ℕ => ((E n : ℝ) : ℂ)) C _ hs
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hEb n
  rw [hsum1.tsum_add hsum2, tsum_mul_left, tsum_abel_id_eq_zeta hs]

/-- Identity-theorem step on a convex open piece: agreement near one interior point
    propagates to the whole piece. -/
lemma eqOn_of_convex_piece (f g : ℂ → ℂ) (V : Set ℂ) (hVo : IsOpen V)
    (hVc : Convex ℝ V)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (z₀ : ℂ) (hz₀ : z₀ ∈ V) (hseed : f =ᶠ[nhds z₀] g) :
    Set.EqOn f g V := by
  have hfa : AnalyticOnNhd ℂ f V := hf.analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := hg.analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc.isPreconnected hz₀ hseed

/-- **The identity theorem on the slit half-plane** (Siegel brick A2h-iii): two
    functions differentiable on `{Re > 9/10} ∖ {1}` that agree on `{Re > 1}` agree
    everywhere on the slit half-plane — by chaining through overlapping convex pieces
    (no slit-plane connectivity needed). -/
theorem eqOn_slit_halfplane (f g : ℂ → ℂ)
    (hf : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ f s)
    (hg : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ g s)
    (heq : ∀ s : ℂ, 1 < s.re → f s = g s)
    (s₀ : ℂ) (h₀re : 9/10 < s₀.re) (h₀ne : s₀ ≠ 1) : f s₀ = g s₀ := by
  -- the convex pieces
  set V₁ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ 0 < s.im} with hV₁
  set V₂ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ s.im < 0} with hV₂
  set V₃ : Set ℂ := {s : ℂ | 1 < s.re} with hV₃
  set V₄ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ s.re < 1} with hV₄
  -- openness
  have hV₁o : IsOpen V₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hV₂o : IsOpen V₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hV₃o : IsOpen V₃ := isOpen_lt continuous_const Complex.continuous_re
  have hV₄o : IsOpen V₄ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  -- convexity: intersections of re/im half-spaces
  have hV₁c : Convex ℝ V₁ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_im_gt 0)
  have hV₂c : Convex ℝ V₂ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_im_lt 0)
  have hV₃c : Convex ℝ V₃ := convex_halfSpace_re_gt 1
  have hV₄c : Convex ℝ V₄ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_re_lt 1)
  -- every piece avoids 1 and sits in the domain
  have hne1 : ∀ {V : Set ℂ}, (∀ s ∈ V, 9/10 < s.re ∧ s ≠ 1) →
      DifferentiableOn ℂ f V ∧ DifferentiableOn ℂ g V := by
    intro V hV
    constructor
    · intro s hs
      exact ((hf s (hV s hs).1 (hV s hs).2).differentiableWithinAt)
    · intro s hs
      exact ((hg s (hV s hs).1 (hV s hs).2).differentiableWithinAt)
  have hdom₁ : ∀ s ∈ V₁, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  have hdom₂ : ∀ s ∈ V₂, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  have hdom₃ : ∀ s ∈ V₃, 9/10 < s.re ∧ s ≠ 1 := by
    intro s hs
    have h1 : 1 < s.re := hs
    refine ⟨by linarith, ?_⟩
    intro hc
    rw [hc] at h1
    simp at h1
  have hdom₄ : ∀ s ∈ V₄, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  obtain ⟨hf₁, hg₁⟩ := hne1 hdom₁
  obtain ⟨hf₂, hg₂⟩ := hne1 hdom₂
  obtain ⟨hf₄, hg₄⟩ := hne1 hdom₄
  -- seed on V₃ overlaps: 2 + i ∈ V₁ ∩ V₃, 2 − i ∈ V₂ ∩ V₃
  have hseed₁ : f =ᶠ[nhds (2 + Complex.I)] g := by
    have hmem : (2 + Complex.I) ∈ V₃ := by
      show (1:ℝ) < (2 + Complex.I).re
      simp
    filter_upwards [hV₃o.mem_nhds hmem] with w hw
    exact heq w hw
  have hseed₂ : f =ᶠ[nhds (2 - Complex.I)] g := by
    have hmem : (2 - Complex.I) ∈ V₃ := by
      show (1:ℝ) < (2 - Complex.I).re
      simp
    filter_upwards [hV₃o.mem_nhds hmem] with w hw
    exact heq w hw
  -- V₁, V₂ agreement
  have hEq₁ : Set.EqOn f g V₁ := by
    apply eqOn_of_convex_piece f g V₁ hV₁o hV₁c hf₁ hg₁ (2 + Complex.I) _ hseed₁
    constructor
    · show (9:ℝ)/10 < (2 + Complex.I).re
      simp
      norm_num
    · show (0:ℝ) < (2 + Complex.I).im
      simp
  have hEq₂ : Set.EqOn f g V₂ := by
    apply eqOn_of_convex_piece f g V₂ hV₂o hV₂c hf₂ hg₂ (2 - Complex.I) _ hseed₂
    constructor
    · show (9:ℝ)/10 < (2 - Complex.I).re
      simp
      norm_num
    · show (2 - Complex.I).im < 0
      simp
  -- V₄ agreement, seeded from V₁ at 19/20 + i/2
  have hmid : ((19:ℝ)/20 + Complex.I * (1/2)) ∈ V₁ ∩ V₄ := by
    constructor
    · constructor
      · show (9:ℝ)/10 < ((19:ℝ)/20 + Complex.I * (1/2)).re
        simp
        norm_num
      · show (0:ℝ) < ((19:ℝ)/20 + Complex.I * (1/2)).im
        simp
    · constructor
      · show (9:ℝ)/10 < ((19:ℝ)/20 + Complex.I * (1/2)).re
        simp
        norm_num
      · show ((19:ℝ)/20 + Complex.I * (1/2)).re < 1
        simp
        norm_num
  have hseed₄ : f =ᶠ[nhds ((19:ℝ)/20 + Complex.I * (1/2))] g := by
    filter_upwards [hV₁o.mem_nhds hmid.1] with w hw
    exact hEq₁ hw
  have hEq₄ : Set.EqOn f g V₄ := by
    apply eqOn_of_convex_piece f g V₄ hV₄o hV₄c hf₄ hg₄ _ hmid.2 hseed₄
  -- conclude by cases on s₀
  rcases lt_trichotomy s₀.re 1 with hlt | heq1 | hgt
  · exact hEq₄ ⟨h₀re, hlt⟩
  · -- re = 1: im ≠ 0
    have him : s₀.im ≠ 0 := by
      intro hc
      apply h₀ne
      apply Complex.ext
      · rw [heq1]
        simp
      · rw [hc]
        simp
    rcases lt_or_gt_of_ne him with hneg | hpos
    · exact hEq₂ ⟨h₀re, hneg⟩
    · exact hEq₁ ⟨h₀re, hpos⟩
  · exact heq s₀ hgt

/-- Complex log-Taylor remainder (A2h-i-a): for real `0 ≤ z ≤ 1/2`,
    `|log(1+z) − z| ≤ z²`. -/
lemma log_taylor_remainder (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2) :
    |Real.log (1 + z) - z| ≤ z ^ 2 := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- upper: log(1+z) ≤ z
  have hup : Real.log (1 + z) ≤ z := by
    have := Real.log_le_sub_one_of_pos h1z
    linarith
  -- lower: log(1+z) ≥ z − z² via log(1+z) = −log(1/(1+z)) and log(1/(1+z)) ≤ 1/(1+z) − 1
  have hlow : z - z ^ 2 ≤ Real.log (1 + z) := by
    have hinv : Real.log (1 / (1 + z)) ≤ 1 / (1 + z) - 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + z) by positivity)
      linarith
    have hneg : Real.log (1 / (1 + z)) = -Real.log (1 + z) := by
      rw [one_div, Real.log_inv]
    rw [hneg] at hinv
    have halg : 1 / (1 + z) - 1 = -z / (1 + z) := by
      field_simp
      ring
    rw [halg] at hinv
    -- −log(1+z) ≤ −z/(1+z) ⟹ log(1+z) ≥ z/(1+z) ≥ z − z²
    have hfrac : z - z ^ 2 ≤ z / (1 + z) := by
      rw [le_div_iff₀ h1z]
      nlinarith [h0, h1]
    have : z / (1 + z) ≤ Real.log (1 + z) := by
      have := neg_le_neg hinv
      simp only [neg_neg] at this
      calc z / (1 + z) = -(-z / (1 + z)) := by ring
        _ ≤ Real.log (1 + z) := by linarith [hinv]
    linarith
  rw [abs_le]
  constructor
  · linarith
  · nlinarith [hup, h0]

/-- **Second-order cpow Taylor bound** (Siegel brick A2h-i): for `w : ℂ` and real
    `0 ≤ z ≤ 1/2` with `‖w‖ ≤ W` and `W*z ≤ 1`,
    `‖(1+z)^w − 1 − wz‖ ≤ 4(W+1)²z²` — the engine of the ζ-truncation defect. -/
lemma cpow_taylor_two (w : ℂ) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2)
    (W : ℝ) (hW : ‖w‖ ≤ W) (hWz : W * z ≤ 1) :
    ‖((1 + z : ℝ) : ℂ) ^ w - 1 - w * z‖ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg w) hW
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- (1+z)^w = exp(w log(1+z))
  have hcpow : ((1 + z : ℝ) : ℂ) ^ w = Complex.exp (w * Real.log (1 + z)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt h1z)]
    congr 1
    rw [Complex.ofReal_log h1z.le]
    ring
  rw [hcpow]
  -- split: exp(wL) − 1 − wz = [exp(wL) − 1 − wL] + w(L − z)
  set L : ℝ := Real.log (1 + z) with hL
  have hLz : |L - z| ≤ z ^ 2 := log_taylor_remainder z h0 h1
  have hLb : |L| ≤ z := by
    have h2 : 0 ≤ L := Real.log_nonneg (by linarith)
    have h3 : L ≤ z := by
      have := Real.log_le_sub_one_of_pos h1z
      rw [hL]
      linarith
    rw [abs_of_nonneg h2]
    exact h3
  have hwL : ‖w * (L : ℂ)‖ ≤ W * z := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hW hLb (abs_nonneg _) hW0
  -- ‖exp(u) − 1 − u‖ ≤ ‖u‖² for ‖u‖ ≤ 1
  have hexp2 : ‖Complex.exp (w * L) - 1 - w * L‖ ≤ ‖w * (L : ℂ)‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := w * (L : ℂ)) (by
      calc ‖w * (L : ℂ)‖ ≤ W * z := hwL
        _ ≤ 1 := hWz)
    exact this
  have hsplit : Complex.exp (w * L) - 1 - w * z
      = (Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z) := by
    ring
  rw [hsplit]
  have hterm2 : ‖w * ((L : ℂ) - z)‖ ≤ W * z ^ 2 := by
    rw [norm_mul, show ((L : ℂ) - (z : ℝ)) = (((L - z : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hW hLz (abs_nonneg _) hW0
  have hsq : ‖w * (L : ℂ)‖ ^ 2 ≤ (W * z) ^ 2 := by
    have h := norm_nonneg (w * (L : ℂ))
    nlinarith [hwL, h]
  calc ‖(Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z)‖
      ≤ ‖Complex.exp (w * L) - 1 - w * L‖ + ‖w * ((L : ℂ) - z)‖ := norm_add_le _ _
    _ ≤ ‖w * (L : ℂ)‖ ^ 2 + W * z ^ 2 := add_le_add hexp2 hterm2
    _ ≤ (W * z) ^ 2 + W * z ^ 2 := by linarith [hsq]
    _ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
        nlinarith [hW0, sq_nonneg z, sq_nonneg W, mul_nonneg hW0 (sq_nonneg z)]

/-- **The second-order Euler–Maclaurin kernel bound** (Siegel brick A2h-ii-α), in the
    `(s−1)`-cleared form: for `n ≥ 2`, `‖1−s‖ ≤ W`, `W/n ≤ 1`:
    `‖(s−1)n^{−s} − (n^{1−s} − (n+1)^{1−s})‖ ≤ 4(W+1)²·n^{−2}·n^{1−Re s}`. -/
lemma euler_maclaurin_kernel (s : ℂ) (n : ℕ) (hn2 : 2 ≤ n)
    (W : ℝ) (hW : ‖1 - s‖ ≤ W) (hWn : W * (1 / n) ≤ 1) :
    ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hnc0 : ((n:ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hz1 : (1:ℝ) / n ≤ 1/2 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    push_cast
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn2]
  have hz0 : (0:ℝ) ≤ 1 / n := by positivity
  -- (n+1)^{1−s} = n^{1−s}·(1+1/n)^{1−s}
  have hsplit : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)
      = ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) := by
    have hy0 : (0:ℝ) ≤ 1 + 1/(n:ℝ) := by positivity
    have hb : (((n + 1 : ℕ):ℂ)) = (((n:ℝ) : ℂ)) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) := by
      push_cast
      field_simp
    rw [hb, Complex.mul_cpow_ofReal_nonneg hn0.le hy0]
    norm_cast
  rw [hsplit]
  -- factor: LHS = n^{1−s}·[(1+1/n)^{1−s} − 1 − (1−s)(1/n)]
  have hpow : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) * ((n:ℂ)) ^ (-s) := by
    rw [show (1:ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hnc0, Complex.cpow_one]
  have hnz : ((n:ℂ)) * ((1/(n:ℝ) : ℝ) : ℂ) = 1 := by
    have hc : ((1/(n:ℝ) : ℝ) : ℂ) = 1 / ((n:ℂ)) := by push_cast; ring
    rw [hc, mul_one_div, div_self hnc0]
  have hfactor : (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s))
      = ((n:ℂ)) ^ ((1:ℂ) - s)
        * ((((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)) := by
    rw [hpow]
    linear_combination (((1:ℂ) - s) * ((n:ℂ)) ^ (-s)) * hnz
  rw [hfactor, norm_mul]
  have hnorm1 : ‖((n:ℂ)) ^ ((1:ℂ) - s)‖ = ((n:ℝ)) ^ (1 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [Complex.sub_re]
  rw [hnorm1]
  have hbr := cpow_taylor_two ((1:ℂ) - s) (1/(n:ℝ)) hz0 hz1 W hW hWn
  calc ((n:ℝ)) ^ (1 - s.re)
        * ‖(((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)‖
      ≤ ((n:ℝ)) ^ (1 - s.re) * (4 * (W + 1) ^ 2 * (1/(n:ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
        have hcast : ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)
            = ((1:ℂ) - s) * (1/(n:ℝ) : ℝ) := by norm_num
        rw [hcast]
        exact hbr
    _ = 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by ring

/-- Reverse Bernoulli (A2h-ii-β1): `(1+θu)(1−u)^θ ≤ 1` for `θ ≥ 0`, `0 ≤ u < 1` —
    hence `(n−1)^{1−p} − n^{1−p} ≥ (p−1)n^{−p}`. -/
lemma one_add_mul_rpow_one_sub_le (θ u : ℝ) (hθ : 0 ≤ θ) (h0 : 0 ≤ u) (h1 : u < 1) :
    (1 + θ * u) * (1 - u) ^ θ ≤ 1 := by
  have h1u : (0:ℝ) < 1 - u := by linarith
  -- (1−u)^θ ≤ e^{−θu}
  have hlog : Real.log (1 - u) ≤ -u := by
    have := Real.log_le_sub_one_of_pos h1u
    linarith
  have hpow : (1 - u) ^ θ ≤ Real.exp (-(θ * u)) := by
    rw [Real.rpow_def_of_pos h1u]
    apply Real.exp_le_exp.mpr
    calc Real.log (1 - u) * θ ≤ (-u) * θ := mul_le_mul_of_nonneg_right hlog hθ
      _ = -(θ * u) := by ring
  -- (1+w)e^{−w} ≤ 1 for w := θu ≥ 0
  have hw0 : 0 ≤ θ * u := mul_nonneg hθ h0
  have hexp : (1 + θ * u) * Real.exp (-(θ * u)) ≤ 1 := by
    have h2 := Real.add_one_le_exp (θ * u)
    have h3 : (0:ℝ) < Real.exp (θ * u) := Real.exp_pos _
    have h4 : Real.exp (-(θ * u)) = 1 / Real.exp (θ * u) := by
      rw [Real.exp_neg, one_div]
    rw [h4, mul_one_div, div_le_one h3]
    linarith
  calc (1 + θ * u) * (1 - u) ^ θ ≤ (1 + θ * u) * Real.exp (-(θ * u)) := by
        apply mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ 1 := hexp

/-- The decreasing-power telescoping comparison (A2h-ii-β2): for `p > 1`, `n ≥ 2`:
    `(p−1)·n^{−p} ≤ (n−1)^{1−p} − n^{1−p}` — each tail term is dominated by the
    telescoping antiderivative decrement. -/
lemma rpow_tail_term_le (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) :
    (p - 1) * ((n:ℝ)) ^ (-p) ≤ (((n - 1 : ℕ)):ℝ) ^ (1 - p) - ((n:ℝ)) ^ (1 - p) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have : (1:ℕ) ≤ n := by omega
    exact_mod_cast this
  set u : ℝ := 1 / n with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hn0]
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn]
  have hcast : (((n - 1 : ℕ)):ℝ) = (n:ℝ) * (1 - u) := by
    rw [hu]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp
  have hber := one_add_mul_rpow_one_sub_le (p - 1) u (by linarith) hu0 hu1
  -- (n−1)^{1−p} = n^{1−p}·(1−u)^{1−p}; want n^{1−p}[(1−u)^{1−p} − 1] ≥ (p−1)n^{−p}
  have hsplit : (((n - 1 : ℕ)):ℝ) ^ (1 - p) = ((n:ℝ)) ^ (1 - p) * (1 - u) ^ (1 - p) := by
    rw [hcast, Real.mul_rpow hn0.le (by linarith)]
  rw [hsplit]
  have hnp : ((n:ℝ)) ^ (1 - p) = (n:ℝ) * ((n:ℝ)) ^ (-p) := by
    rw [show (1:ℝ) - p = 1 + (-p) by ring, Real.rpow_add hn0, Real.rpow_one]
  have hkey : 1 + (p - 1) * u ≤ (1 - u) ^ (1 - p) := by
    have hpow0 : (0:ℝ) < (1 - u) ^ (p - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hinv : (1 - u) ^ (1 - p) = ((1 - u) ^ (p - 1))⁻¹ := by
      rw [← Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - u)]
      congr 1
      ring
    rw [hinv, le_inv_comm₀ (by positivity) hpow0]
    calc (1 - u) ^ (p - 1) ≤ 1 / (1 + (p - 1) * u) := by
          rw [le_div_iff₀ (by nlinarith [mul_nonneg (show (0:ℝ) ≤ p - 1 by linarith) hu0])]
          calc (1 - u) ^ (p - 1) * (1 + (p - 1) * u)
              = (1 + (p - 1) * u) * (1 - u) ^ (p - 1) := by ring
            _ ≤ 1 := hber
      _ = (1 + (p - 1) * u)⁻¹ := one_div _
  -- assemble: n^{1−p}(1−u)^{1−p} − n^{1−p} ≥ n^{1−p}·(p−1)u = (p−1)n^{−p}
  have hnu : (n:ℝ) * u = 1 := by
    rw [hu]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hkey
    (Real.rpow_nonneg hn0.le (1 - p))
  have hfin : ((n:ℝ)) ^ (1 - p) * ((p - 1) * u) = (p - 1) * ((n:ℝ)) ^ (-p) := by
    rw [hnp]
    calc (n:ℝ) * ((n:ℝ)) ^ (-p) * ((p - 1) * u)
        = (p - 1) * ((n:ℝ)) ^ (-p) * ((n:ℝ) * u) := by ring
      _ = (p - 1) * ((n:ℝ)) ^ (-p) := by rw [hnu, mul_one]
  nlinarith [hmul, hfin.le, hfin.ge]

/-- **The p-tail bound** (Siegel brick A2h-ii-β): for `p > 1`, `1 ≤ x`:
    `Σ_{x<n≤z} n^{−p} ≤ x^{1−p}/(p−1)` — sharp telescoping, uniform in `z`. -/
lemma rpow_tail_sum_le (p : ℝ) (hp : 1 < p) (x : ℕ) (hx : 1 ≤ x) : ∀ z : ℕ, x ≤ z →
    ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p) ≤ ((x:ℝ)) ^ (1 - p) / (p - 1) := by
  have hp0 : (0:ℝ) < p - 1 := by linarith
  -- sharp form by induction: Σ ≤ (x^{1−p} − z^{1−p})/(p−1)
  have hsharp : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p)
        ≤ (((x:ℝ)) ^ (1 - p) - ((z:ℝ)) ^ (1 - p)) / (p - 1) := by
    intro z
    induction z with
    | zero =>
      intro hx0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        simp
      · have hstep : Icc (x + 1) (m + 1) = insert (m + 1) (Icc (x + 1) m) := by
          ext k
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hstep, Finset.sum_insert (by simp)]
        have hterm := rpow_tail_term_le p hp (m + 1) (by omega)
        have hm1 : (m + 1 : ℕ) - 1 = m := by omega
        rw [hm1] at hterm
        have hih := ihm hge
        have hd : ((m + 1 : ℕ):ℝ) ^ (-p)
            ≤ (((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1) := by
          rw [le_div_iff₀ hp0]
          calc ((m + 1 : ℕ):ℝ) ^ (-p) * (p - 1) = (p - 1) * ((m + 1 : ℕ):ℝ) ^ (-p) := by ring
            _ ≤ ((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p) := hterm
        calc ((m + 1 : ℕ):ℝ) ^ (-p) + ∑ n ∈ Icc (x + 1) m, ((n:ℝ)) ^ (-p)
            ≤ (((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1)
              + (((x:ℝ)) ^ (1 - p) - ((m:ℝ)) ^ (1 - p)) / (p - 1) := add_le_add hd hih
          _ = (((x:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1) := by ring
  intro z hz
  have hzp : (0:ℝ) ≤ ((z:ℝ)) ^ (1 - p) := Real.rpow_nonneg (Nat.cast_nonneg z) _
  calc ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p)
      ≤ (((x:ℝ)) ^ (1 - p) - ((z:ℝ)) ^ (1 - p)) / (p - 1) := hsharp z hz
    _ ≤ ((x:ℝ)) ^ (1 - p) / (p - 1) := by
        apply div_le_div_of_nonneg_right _ hp0.le
        linarith

/-- **The Euler–Maclaurin tail series is differentiable on `Re s > 9/10`**
    (Siegel brick A2h-ii-γ): `Wtail_x(s) := Σ'_n [n≥x]·((s−1)n^{−s} − (n^{1−s}−(n+1)^{1−s}))`
    is differentiable at every point of the half-plane — the continuation vehicle of the
    ζ-truncation. M-test on windows, head split off as a finite entire sum. -/
theorem wtail_differentiableAt (x : ℕ) (hx : 1 ≤ x) (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) :
    DifferentiableAt ℂ (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) s₀ := by
  set σ₀ : ℝ := (9/10 + s₀.re) / 2 with hσ₀
  have hσ₀1 : 9/10 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀2 : σ₀ < s₀.re := by rw [hσ₀]; linarith
  set R : ℝ := ‖s₀‖ + 1 with hR
  have hR0 : 0 < R := by
    rw [hR]
    have := norm_nonneg s₀
    linarith
  set U : Set ℂ := {s : ℂ | σ₀ < s.re} ∩ Metric.ball 0 R with hU
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := by
    rw [hU]
    constructor
    · exact hσ₀2
    · rw [Metric.mem_ball, dist_zero_right, hR]
      linarith
  set W : ℝ := R + 2 with hW
  set N₀ : ℕ := max x (Nat.ceil R + 4) with hN₀
  have hN₀x : x ≤ N₀ := le_max_left _ _
  have hN₀2 : 2 ≤ N₀ := le_trans (by omega) (le_max_right x (Nat.ceil R + 4))
  have hN₀W : ∀ n : ℕ, N₀ ≤ n → W ≤ (n:ℝ) := by
    intro n hn
    have h1 : Nat.ceil R + 4 ≤ n := le_trans (le_max_right x _) hn
    have h2 : ((Nat.ceil R + 4 : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have h3 : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    push_cast at h2
    rw [hW]
    linarith
  -- the pointwise kernel bound on U, for n ≥ N₀
  have hVbound : ∀ n : ℕ, N₀ ≤ n → ∀ w : ℂ, w ∈ U →
      ‖(w - 1) * ((n:ℂ)) ^ (-w)
        - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) := by
    intro n hn w hwU
    obtain ⟨hwre, hwball⟩ := hwU
    have hwre' : σ₀ < w.re := hwre
    have hwnorm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hwball
      exact hwball
    have hn2 : 2 ≤ n := le_trans hN₀2 hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hWb : ‖1 - w‖ ≤ W := by
      calc ‖1 - w‖ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ = 1 + ‖w‖ := by rw [norm_one]
        _ ≤ W := by rw [hW]; linarith
    have hWn : W * (1 / (n:ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hn0]
      exact hN₀W n hn
    have hker := euler_maclaurin_kernel w n hn2 W hWb hWn
    have hexp : ((n:ℝ)) ^ (1 - w.re) ≤ ((n:ℝ)) ^ (1 - σ₀) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1r
      linarith
    calc ‖(w - 1) * ((n:ℂ)) ^ (-w)
          - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w))‖
        ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - w.re) := hker
      _ ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
  -- the majorant is summable
  have husum : Summable (fun n : ℕ => if n < N₀ then (0:ℝ) else
      4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) := by
    have hmajsum : Summable (fun n : ℕ => (4 * (W + 1) ^ 2) * (1 / ((n:ℝ)) ^ (σ₀ + 1))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le _ _ hmajsum
    · intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h]
      · rw [if_neg (not_lt.mpr h)]
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have h1 : (1:ℕ) ≤ n := le_trans (le_trans hx hN₀x) h
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
          linarith
        positivity
    · intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h]
        positivity
      · rw [if_neg (not_lt.mpr h)]
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have h1 : (1:ℕ) ≤ n := le_trans (le_trans hx hN₀x) h
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
          linarith
        have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
          rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
            ← Real.rpow_neg hn0.le]
        have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) = 1 / ((n:ℝ)) ^ (σ₀ + 1) := by
          rw [hpow2, ← Real.rpow_add hn0,
            show -((2:ℕ):ℝ) + (1 - σ₀) = -(σ₀ + 1) by push_cast; ring,
            Real.rpow_neg hn0.le, one_div]
        apply le_of_eq
        rw [← hcollect]
        ring
  -- entire terms
  have hterm : ∀ n : ℕ, 1 ≤ n → Differentiable ℂ (fun s : ℂ =>
      (s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) := by
    intro n hn
    have hn0 : ((n:ℂ)) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hn10 : (((n + 1 : ℕ):ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    apply Differentiable.sub
    · apply Differentiable.mul
      · exact differentiable_id.sub (differentiable_const 1)
      · exact (Differentiable.neg differentiable_id).const_cpow (Or.inl hn0)
    · apply Differentiable.sub
      · exact ((differentiable_const 1).sub differentiable_id).const_cpow (Or.inl hn0)
      · exact ((differentiable_const 1).sub differentiable_id).const_cpow (Or.inl hn10)
  -- the tail: M-test on U
  have hgdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s : ℂ => if n < N₀ then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) U := by
    intro n
    rcases Nat.lt_or_ge n N₀ with h | h
    · simp only [if_pos h]
      exact differentiableOn_const 0
    · simp only [if_neg (not_lt.mpr h)]
      exact (hterm n (le_trans (le_trans hx hN₀x) h)).differentiableOn
  have hgbound : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖if n < N₀ then 0 else
        ((w - 1) * ((n:ℂ)) ^ (-w)
          - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w)))‖
      ≤ (if n < N₀ then (0:ℝ) else
          4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) := by
    intro n w hwU
    rcases Nat.lt_or_ge n N₀ with h | h
    · rw [if_pos h, if_pos h, norm_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h)]
      exact hVbound n h w hwU
  have hTail : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, (if n < N₀ then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U :=
    Complex.differentiableOn_tsum_of_summable_norm husum hgdiff hUopen hgbound
  -- the head: a finite sum of entire functions
  have hHead : DifferentiableOn ℂ (fun s : ℂ => ∑ n ∈ range N₀, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U := by
    have hsum : DifferentiableOn ℂ (∑ n ∈ range N₀, fun s : ℂ => (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U := by
      apply DifferentiableOn.sum
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · simp only [if_pos h]
        exact differentiableOn_const 0
      · simp only [if_neg (not_lt.mpr h)]
        exact (hterm n (le_trans hx h)).differentiableOn
    have hfn : (fun s : ℂ => ∑ n ∈ range N₀, (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        = (∑ n ∈ range N₀, fun s : ℂ => (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
      funext s
      rw [Finset.sum_apply]
    rw [hfn]
    exact hsum
  -- on U the full series splits as head + tail
  have hEqOn : ∀ s ∈ U, (∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
      = (∑ n ∈ range N₀, (if n < x then 0 else
          ((s - 1) * ((n:ℂ)) ^ (-s)
            - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        + (∑' n : ℕ, (if n < N₀ then 0 else
          ((s - 1) * ((n:ℂ)) ^ (-s)
            - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
    intro s hsU
    set V : ℕ → ℂ := fun n => (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)) with hV
    have hgsum : Summable (fun n : ℕ => if n < N₀ then 0 else V n) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => if n < N₀ then (0:ℝ) else
        4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) husum
      intro n
      exact hgbound n s hsU
    have hhsum : Summable (fun n : ℕ => if n < N₀ then (if n < x then 0 else V n) else 0) :=
      summable_of_ne_finset_zero (s := range N₀) (by
        intro n hn
        rw [Finset.mem_range] at hn
        rw [if_neg hn])
    have hsplit : ∀ n : ℕ, (if n < x then 0 else V n)
        = (if n < N₀ then (if n < x then 0 else V n) else 0)
          + (if n < N₀ then 0 else V n) := by
      intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h, if_pos h, add_zero]
      · have hnx : ¬ n < x := not_lt.mpr (le_trans hN₀x h)
        have hnN : ¬ n < N₀ := not_lt.mpr h
        rw [if_neg hnx, if_neg hnN, if_neg hnN, zero_add]
    calc ∑' n : ℕ, (if n < x then 0 else V n)
        = ∑' n : ℕ, ((if n < N₀ then (if n < x then 0 else V n) else 0)
            + (if n < N₀ then 0 else V n)) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < N₀ then (if n < x then 0 else V n) else 0))
            + (∑' n : ℕ, (if n < N₀ then 0 else V n)) := hhsum.tsum_add hgsum
      _ = (∑ n ∈ range N₀, (if n < x then 0 else V n))
            + (∑' n : ℕ, (if n < N₀ then 0 else V n)) := by
          congr 1
          rw [tsum_eq_sum (s := range N₀) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  -- assemble
  have hSum : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U :=
    DifferentiableOn.congr (hHead.add hTail) hEqOn
  exact hSum.differentiableAt (hUopen.mem_nhds hs₀U)

/-- **The Euler–Maclaurin tail on `Re s > 1`** (Siegel brick A2h-ii-δ):
    `Wtail_x(s) = (s−1)·(ζ(s) − Σ_{n<x} n^{−s}) − x^{1−s}` — the closed form the
    identity theorem transports to the strip. -/
theorem wtail_eq_on_gt_one (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if n < x then 0 else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
    = (s - 1) * (riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        - ((x:ℂ)) ^ ((1:ℂ) - s) := by
  -- summability of the pieces
  have hzsum : Summable (fun n : ℕ => ((n:ℂ)) ^ (-s)) := by
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    apply h.congr
    intro n
    rw [Complex.cpow_neg, one_div]
  have hzsum_ite : Summable (fun n : ℕ => if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖((n:ℂ)) ^ (-s)‖) hzsum.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have hhead : Summable (fun n : ℕ => if n < x then ((n:ℂ)) ^ (-s) else 0) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htel_sum := tsum_cpow_telescope_summable x hx hs
  have hmul : Summable (fun n : ℕ => (s - 1) * (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))) :=
    hzsum_ite.mul_left (s - 1)
  -- ζ splits as head + tail
  have hzeta_split : riemannZeta s = (∑ n ∈ range x, ((n:ℂ)) ^ (-s))
      + ∑' n : ℕ, (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    have hconv : ∀ n : ℕ, 1 / ((n:ℂ)) ^ s = ((n:ℂ)) ^ (-s) := by
      intro n
      rw [Complex.cpow_neg, one_div]
    rw [tsum_congr hconv]
    have hsplit : ∀ n : ℕ, ((n:ℂ)) ^ (-s)
        = (if n < x then ((n:ℂ)) ^ (-s) else 0) + (if n < x then 0 else ((n:ℂ)) ^ (-s)) := by
      intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_pos h, add_zero]
      · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
    rw [tsum_congr hsplit, hhead.tsum_add hzsum_ite]
    congr 1
    rw [tsum_eq_sum (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos hn]
  have hz2 : ∑' n : ℕ, (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))
      = riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s) := by
    rw [hzeta_split]
    ring
  -- pointwise split of the V-term
  have hVsplit : ∀ n : ℕ, (if n < x then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      = (s - 1) * (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))
        - (if n < x then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, if_pos h, mul_zero, sub_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), if_neg (not_lt.mpr h)]
  -- assemble
  rw [tsum_congr hVsplit, Summable.tsum_sub hmul htel_sum, tsum_mul_left,
    tsum_cpow_telescope x hx hs, hz2]

/-- **The ζ-truncation identity at real `β′ ∈ (9/10, 1)`** (Siegel brick A2h-ii-ε1):
    the closed form of `Wtail_x` continues through the pole-free slit — the identity
    theorem transports `wtail_eq_on_gt_one` from `Re > 1` to the strip. -/
theorem zeta_truncation_identity (x : ℕ) (hx : 1 ≤ x) {β : ℝ}
    (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    ∑' n : ℕ, (if n < x then 0 else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))
    = (((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) := by
  have hx0 : ((x:ℂ)) ≠ 0 := by
    have : x ≠ 0 := by omega
    exact_mod_cast this
  -- differentiability of each n^{−s} term (n = 0 is locally the zero function)
  have hterm0 : ∀ n : ℕ, ∀ s : ℂ, 9/10 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => ((n:ℂ)) ^ (-s)) s := by
    intro n s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · apply (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq
      have hopen : IsOpen {w : ℂ | 9/10 < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hs] with w hw
      rw [Nat.cast_zero, Complex.zero_cpow]
      intro hc
      have hw0 : w = 0 := by
        have := neg_eq_zero.mp hc
        exact this
      rw [hw0] at hw
      simp only [Set.mem_setOf_eq, Complex.zero_re] at hw
      linarith
    · have hn0 : ((n:ℂ)) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      exact ((Differentiable.neg differentiable_id).const_cpow
        (Or.inl hn0)).differentiableAt
  -- differentiability of the finite sum
  have hgsum : ∀ s : ℂ, 9/10 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => ∑ n ∈ range x, ((n:ℂ)) ^ (-s)) s := by
    intro s hs
    have h : DifferentiableAt ℂ (∑ n ∈ range x, fun s : ℂ => ((n:ℂ)) ^ (-s)) s := by
      apply DifferentiableAt.sum
      intro n _
      exact hterm0 n s hs
    have hfn : (fun s : ℂ => ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        = ∑ n ∈ range x, fun s : ℂ => ((n:ℂ)) ^ (-s) := by
      funext w
      rw [Finset.sum_apply]
    rw [hfn]
    exact h
  -- apply the identity theorem
  have h₀re : 9/10 < ((β:ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hβ1
  have h₀ne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  exact eqOn_slit_halfplane
    (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
    (fun s : ℂ => (s - 1) * (riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        - ((x:ℂ)) ^ ((1:ℂ) - s))
    (fun s hs _ => wtail_differentiableAt x hx s hs)
    (by
      intro s hs hs1
      apply DifferentiableAt.sub
      · apply DifferentiableAt.mul
        · exact (differentiable_id.sub (differentiable_const 1)).differentiableAt
        · apply DifferentiableAt.sub
          · exact differentiableAt_riemannZeta hs1
          · exact hgsum s hs
      · exact (((differentiable_const 1).sub differentiable_id).const_cpow
          (Or.inl hx0)).differentiableAt)
    (fun s hs => wtail_eq_on_gt_one x hx hs)
    ((β:ℂ)) h₀re h₀ne

/-- **THE ζ-TRUNCATION BOUND** (Siegel brick A2h-ii-ε): at real `β′ ∈ (9/10, 1)`,
    `‖(β′−1)(ζ(β′) − Σ_{n<x}n^{−β′}) − x^{1−β′}‖ ≤ 11·x^{−β′}` for `x ≥ 2` — the
    quantitative form the Goldfeld master inequality consumes. -/
theorem zeta_truncation (x : ℕ) (hx : 2 ≤ x) {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    ‖(((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))‖ ≤ 11 * ((x:ℝ)) ^ (-β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  rw [← zeta_truncation_identity x hx1 hβ1 hβ2]
  -- the pointwise kernel bound at s = β′
  have hpoint : ∀ n : ℕ, x ≤ n →
      ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
      ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans hx hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hW : ‖1 - ((β:ℂ))‖ ≤ 1/10 := by
      rw [show (1:ℂ) - ((β:ℂ)) = (((1 - β : ℝ)):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hWn : (1/10 : ℝ) * (1 / (n:ℝ)) ≤ 1 := by
      have h1 : (1:ℝ)/(n:ℝ) ≤ 1 := by
        rw [div_le_one hn0]
        linarith
      linarith
    have hker := euler_maclaurin_kernel ((β:ℂ)) n hn2 (1/10) hW hWn
    rw [Complex.ofReal_re] at hker
    have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) = ((n:ℝ)) ^ (-(1 + β)) := by
      have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
        rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
          ← Real.rpow_neg hn0.le]
      rw [hpow2, ← Real.rpow_add hn0]
      congr 1
      push_cast
      ring
    calc ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
        ≤ 4 * (1/10 + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) := hker
      _ = 4 * (1/10 + 1) ^ 2 * (((n:ℝ)) ^ (-(1 + β))) := by
          rw [← hcollect]
          ring
      _ ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
          have ht : (0:ℝ) ≤ ((n:ℝ)) ^ (-(1 + β)) := Real.rpow_nonneg hn0.le _
          nlinarith [ht]
  -- partial sums of the norms are uniformly ≤ 11 x^{−β}
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (-β) := Real.rpow_nonneg hx0.le _
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z,
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
      ≤ 11 * ((x:ℝ)) ^ (-β) := by
    intro z
    have hite : ∀ n ∈ range z,
        ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
        = (if x ≤ n then ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 := hpoint x (le_refl x)
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1),
          ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
            - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β))
          = 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β)) := by
        rw [Finset.mul_sum]
      have h4 := rpow_tail_sum_le (1 + β) (by linarith) x hx1 (z - 1) hm
      rw [show (1:ℝ) - (1 + β) = -β by ring, show (1:ℝ) + β - 1 = β by ring] at h4
      -- x-term: 5x^{−(1+β)} ≤ (5/2)x^{−β}
      have hxsplit : ((x:ℝ)) ^ (-(1 + β)) = ((x:ℝ)) ^ (-β) * ((x:ℝ)) ^ (-(1:ℝ)) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hxinv : ((x:ℝ)) ^ (-(1:ℝ)) ≤ 1/2 := by
        rw [Real.rpow_neg_one, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hx
      have h5 : 5 * ((x:ℝ)) ^ (-(1 + β)) ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) := by
        rw [hxsplit]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hxinv hxβ
      -- tail: 5·x^{−β}/β ≤ 5·x^{−β}·(10/9)
      have hβinv : (1:ℝ)/β ≤ 10/9 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have h6 : ((x:ℝ)) ^ (-β) / β ≤ ((x:ℝ)) ^ (-β) * (10/9) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hβinv hxβ
      calc ‖(((β:ℂ)) - 1) * ((x:ℂ)) ^ (-(β:ℂ))
            - (((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1),
              ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
                - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ 5 * ((x:ℝ)) ^ (-(1 + β))
            + 5 * (((x:ℝ)) ^ (-β) / β) := by
            have := le_trans h2 (le_of_eq h3)
            have h7 : 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β))
                ≤ 5 * (((x:ℝ)) ^ (-β) / β) := by
              apply mul_le_mul_of_nonneg_left h4 (by norm_num)
            linarith
        _ ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) + 5 * (((x:ℝ)) ^ (-β) * (10/9)) := by
            have h8 : 5 * (((x:ℝ)) ^ (-β) / β) ≤ 5 * (((x:ℝ)) ^ (-β) * (10/9)) :=
              mul_le_mul_of_nonneg_left h6 (by norm_num)
            linarith
        _ ≤ 11 * ((x:ℝ)) ^ (-β) := by linarith
  -- summability of the norms
  have hnorm_sum : Summable (fun n : ℕ =>
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖) := by
    have hmaj : Summable (fun n : ℕ => (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hmaj
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg (not_lt.mpr h)]
      have hn0 : (0:ℝ) < (n:ℝ) := by
        have : (0:ℕ) < n := by omega
        exact_mod_cast this
      have heq : (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β)) = 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n h
  -- assemble
  calc ‖∑' n : ℕ, (if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))‖
      ≤ ∑' n : ℕ, ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ 11 * ((x:ℝ)) ^ (-β) :=
        hnorm_sum.tsum_le_of_sum_range_le hpartial

/-- Real Abel initial-value summation (A2h-iv-a1): the ℝ twin of `abel_initial`. -/
lemma abel_initial_r (a w : ℕ → ℝ) : ∀ x : ℕ, 1 ≤ x →
    ∑ n ∈ Icc 1 x, a n * w n
      = (∑ n ∈ Icc 1 x, a n) * w x
        + ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
  intro x
  induction x with
  | zero =>
    intro h0
    omega
  | succ p ih =>
    intro _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have hp1 : (p + 1 : ℕ) - 1 = p := by omega
      have hnotmem : (p + 1) ∉ Icc 1 p := by
        simp only [Finset.mem_Icc]
        omega
      have hnotmem2 : p ∉ Icc 1 (p - 1) := by
        simp only [Finset.mem_Icc]
        omega
      have hins : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hins2 : Icc 1 p = insert p (Icc 1 (p - 1)) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hLHS : ∑ n ∈ Icc 1 (p + 1), a n * w n
          = a (p + 1) * w (p + 1) + ∑ n ∈ Icc 1 p, a n * w n := by
        rw [hins, Finset.sum_insert hnotmem]
      have hRHS2 : ∑ n ∈ Icc 1 ((p + 1) - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
          = (∑ m ∈ Icc 1 p, a m) * (w p - w (p + 1))
            + ∑ n ∈ Icc 1 (p - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
        rw [hp1]
        conv_lhs => rw [hins2]
        rw [Finset.sum_insert hnotmem2]
      have hA : ∑ m ∈ Icc 1 (p + 1), a m = a (p + 1) + ∑ m ∈ Icc 1 p, a m := by
        rw [hins, Finset.sum_insert hnotmem]
      rw [hLHS, ih hp, hRHS2, hA]
      ring

/-- **The finite Abel master identity** (Siegel brick A2h-iv-a): for partial sums
    `A(y) = λy + E(y)`, against ANY weight `w`:
    `Σ_{n≤x} a(n)w(n) = λ·Σ_{n≤x}w(n) + E(x)w(x) + Σ_{n<x}E(n)(w(n)−w(n+1))` —
    the λ-part telescopes exactly; no continuation enters. -/
theorem abel_master_identity (a : ℕ → ℝ) (lam : ℝ) (E : ℕ → ℝ)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = lam * n + E n)
    (w : ℕ → ℝ) (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 x, a n * w n
    = lam * (∑ n ∈ Icc 1 x, w n) + E x * w x
      + ∑ n ∈ Icc 1 (x - 1), E n * (w n - w (n + 1)) := by
  rw [abel_initial_r a w x hx, hAE x]
  have hterm : ∀ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
      = (n : ℝ) * (w n - w (n + 1)) * lam + E n * (w n - w (n + 1)) := by
    intro n _
    rw [hAE n]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
    weighted_telescope w (x - 1)]
  have hxx : (x - 1 : ℕ) + 1 = x := by omega
  rw [hxx]
  have hsplit : ∑ n ∈ Icc 1 x, w n = w x + ∑ n ∈ Icc 1 (x - 1), w n := by
    rw [show Icc 1 x = insert x (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
  rw [hsplit]
  have hcast : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
    push_cast [Nat.cast_sub hx]
    ring
  rw [hcast]
  ring

/-- Real-cast bridge for cpow at real exponents (A2h-iv-b0). -/
lemma cpow_real_cast (n : ℕ) (β : ℝ) :
    ((n:ℂ)) ^ (-(β:ℂ)) = ((((n:ℝ)) ^ (-β) : ℝ) : ℂ) := by
  rw [show -(β:ℂ) = (((-β : ℝ)):ℂ) from by push_cast; ring,
    show ((n:ℂ)) = (((n:ℝ)):ℂ) from by push_cast; ring]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-β)).symm

/-- The E-Abel term is real at real exponents (A2h-iv-b0'). -/
lemma eabel_term_real (E : ℕ → ℝ) (n : ℕ) (β : ℝ) :
    ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
    = (((E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) : ℝ)) : ℂ) := by
  rw [cpow_real_cast n β, cpow_real_cast (n + 1) β]
  push_cast
  ring

/-- **The E-Abel tail bound** (Siegel brick A2h-iv-b): with `|E(n)| ≤ C·n^{3/4}(1+log n)`,
    at real `β ∈ (9/10, 1)` the series tail beyond `x` is `≤ 400C·x^{7/8−β}` — the error
    that the choice `9/10 > 7/8` makes vanish. -/
theorem eabel_tail_bound (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x) :
    ‖(∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      - ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
    ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hβ0 : (0:ℝ) < β := by linarith
  have hp1 : (1:ℝ) < β + 1/8 := by linarith
  -- the pointwise majorant: ‖E(n)Δn‖ ≤ 9C·n^{−(β+1/8)} for n ≥ 1
  have hpoint : ∀ n : ℕ, 1 ≤ n →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
    intro n hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    rw [eabel_term_real, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hΔ0 : (0:ℝ) ≤ ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := by
      have hmono : (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β) := by
        apply Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith)
        linarith
      linarith
    have hΔle : ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β - 1) := by
      calc ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)
          ≤ β * ((n:ℝ)) ^ (-β - 1) := rpow_diff_le n hn β hβ0.le
        _ ≤ 1 * ((n:ℝ)) ^ (-β - 1) := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            exact Real.rpow_nonneg hn0.le _
        _ = ((n:ℝ)) ^ (-β - 1) := one_mul _
    have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
      have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
        Real.log_le_rpow_div hn0.le (by norm_num)
      have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
      have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
        Real.one_le_rpow hn1r (by norm_num)
      linarith [h1, h2.le, h2.ge, h3]
    have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    have hEn := hE n hn
    have habs : |((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)|
        = ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := abs_of_nonneg hΔ0
    rw [habs]
    have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)
        = ((n:ℝ)) ^ (-(β + 1/8)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring
    calc |E n| * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))
        ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (((n:ℝ)) ^ (-β - 1)) := by
          exact mul_le_mul hEn hΔle hΔ0 (by positivity)
      _ ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8)))) * (((n:ℝ)) ^ (-β - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
          apply mul_le_mul_of_nonneg_left _ hC0
          apply mul_le_mul_of_nonneg_left hlogbound (Real.rpow_nonneg hn0.le _)
      _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)) := by
          ring
      _ = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by rw [hcollect]
  -- summability of the terms
  have hsummable : Summable (fun n : ℕ => ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    have hmaj : Summable (fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr hp1)
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have heq : (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))
          = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n hn
  -- the finite sum is the range-x head (the n = 0 term vanishes)
  have hhead : ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = ∑ n ∈ range x, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) := by
    rw [show range x = insert 0 (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    rw [hE0]
    simp
  rw [hhead]
  -- head/tail split of the tsum
  have hsplit : ∀ n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = (if n < x then ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
        + (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, add_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
  have hheadsum : Summable (fun n : ℕ => (if n < x then ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htailsum : Summable (fun n : ℕ => (if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ =>
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖)
      hsummable.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have htsum_split : (∑' n : ℕ, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
        + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    calc ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
        = ∑' n : ℕ, ((if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
            + (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) :=
          hheadsum.tsum_add htailsum
      _ = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
          congr 1
          rw [tsum_eq_sum (s := range x) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  rw [htsum_split]
  rw [show ∀ (u v : ℂ), u + v - u = v from fun u v => by ring]
  -- bound the tail tsum by its norms
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (7/8 - β) := Real.rpow_nonneg hx0.le _
  have hnormsum : Summable (fun n : ℕ => ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖) := htailsum.norm
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
    intro z
    have hite : ∀ n ∈ range z, ‖if n < x then (0:ℂ) else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
        = (if x ≤ n then ‖((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 : ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) := hpoint x hx1
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8))
          = 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [Finset.mul_sum]
      have h4 := rpow_tail_sum_le (β + 1/8) hp1 x hx1 (z - 1) hm
      rw [show (1:ℝ) - (β + 1/8) = 7/8 - β by ring,
        show β + 1/8 - 1 = β - 7/8 by ring] at h4
      have hdenom : ((x:ℝ)) ^ (7/8 - β) / (β - 7/8) ≤ 40 * ((x:ℝ)) ^ (7/8 - β) := by
        rw [div_le_iff₀ (by linarith)]
        have h5 : (1:ℝ) ≤ 40 * (β - 7/8) := by linarith
        nlinarith [hxβ]
      have hxterm : ((x:ℝ)) ^ (-(β + 1/8)) ≤ ((x:ℝ)) ^ (7/8 - β) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1)
        linarith
      calc ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8))
            + 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
            have h6 : 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8))
                ≤ 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
              apply mul_le_mul_of_nonneg_left h4 (by positivity)
            linarith [le_trans h2 (le_of_eq h3), h1, h6,
              le_trans (le_trans h2 (le_of_eq h3)) h6]
        _ ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) + 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) := by
            have h7 : 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) :=
              mul_le_mul_of_nonneg_left hxterm (by positivity)
            have h8 : 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8))
                ≤ 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) :=
              mul_le_mul_of_nonneg_left hdenom (by positivity)
            linarith
        _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by nlinarith [hxβ, hC0]
  calc ‖∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))‖
      ≤ ∑' n : ℕ, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) :=
        hnormsum.tsum_le_of_sum_range_le hpartial

/-- **THE GOLDFELD MASTER INEQUALITY** (Siegel brick A2h-iv): for a nonnegative
    Dirichlet-coefficient system with `a(1) = 1` and partial sums `λy + E(y)`,
    `|E(n)| ≤ C·n^{3/4}(1+log n)`: at every real `β ∈ (9/10, 1)` and every `x ≥ 2`,
    `1 ≤ G(β).re + λ·x^{1−β}/(1−β) + 12λ·x^{−β}/(1−β) + 410C·x^{7/8−β}`
    where `G = λζ + Σ'E(n)Δn` is the analytic continuation of `Σa(n)n^{−s}`.
    At a zero of the L-product `G(β) = 0` and `x → ∞` forces `λ` large — Siegel. -/
theorem goldfeld_master_inequality (a : ℕ → ℝ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1) (hlam : 0 ≤ lam)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = lam * n + E n)
    (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x) :
    1 ≤ ((lam : ℂ) * riemannZeta ((β:ℂ))
          + ∑' n : ℕ, ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))).re
        + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β))
        + 410 * C * ((x:ℝ)) ^ (7/8 - β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hx1r : (1:ℝ) ≤ (x:ℝ) := by
    have : (1:ℕ) ≤ x := hx1
    exact_mod_cast this
  have h1β : (0:ℝ) < 1 - β := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (-β) := Real.rpow_nonneg hx0.le _
  have hx78 : (0:ℝ) ≤ ((x:ℝ)) ^ (7/8 - β) := Real.rpow_nonneg hx0.le _
  have hx1β : (0:ℝ) ≤ ((x:ℝ)) ^ (1 - β) := Real.rpow_nonneg hx0.le _
  -- abbreviations
  set Z : ℂ := riemannZeta ((β:ℂ)) with hZ
  set ES : ℂ := ∑' n : ℕ, ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) with hES
  set SC : ℂ := ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)) with hSC
  set SF : ℂ := ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) with hSF
  -- Step 1: the unit lower bound
  have hone : (1:ℝ) ≤ ∑ n ∈ Icc 1 x, a n * ((n:ℝ)) ^ (-β) := by
    have h1mem : (1:ℕ) ∈ Icc 1 x := by
      simp only [Finset.mem_Icc]
      omega
    have hterm1 : a 1 * (((1:ℕ)):ℝ) ^ (-β) = 1 := by
      rw [ha1, Nat.cast_one, Real.one_rpow, one_mul]
    calc (1:ℝ) = a 1 * (((1:ℕ)):ℝ) ^ (-β) := hterm1.symm
      _ ≤ ∑ n ∈ Icc 1 x, a n * ((n:ℝ)) ^ (-β) := by
          apply Finset.single_le_sum (f := fun n : ℕ => a n * ((n:ℝ)) ^ (-β)) _ h1mem
          intro n _
          exact mul_nonneg (ha0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- Step 2: the finite Abel identity at w(n) = n^{−β}
  have hiden : ∑ n ∈ Icc 1 x, a n * ((n:ℝ)) ^ (-β)
      = lam * (∑ n ∈ Icc 1 x, ((n:ℝ)) ^ (-β)) + E x * ((x:ℝ)) ^ (-β)
        + ∑ n ∈ Icc 1 (x - 1), E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) :=
    abel_master_identity a lam E hAE (fun n => ((n:ℝ)) ^ (-β)) x hx1
  -- Step 3: the E-part vs the full E-series
  have hbridgeE : SF = ((( ∑ n ∈ Icc 1 (x - 1),
      E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) : ℝ)) : ℂ) := by
    rw [hSF, Finset.sum_congr rfl (fun n _ => eabel_term_real E n β),
      ← Complex.ofReal_sum]
  have hSFre : (∑ n ∈ Icc 1 (x - 1),
      E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))) = SF.re := by
    rw [hbridgeE, Complex.ofReal_re]
  have hEtail := eabel_tail_bound E C hC0 hE0 hE hβ1 hβ2 x hx
  have hSEle : ∑ n ∈ Icc 1 (x - 1), E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))
      ≤ ES.re + 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
    have h1 : (SF - ES).re ≤ ‖SF - ES‖ := Complex.re_le_norm _
    have h2 : ‖SF - ES‖ = ‖ES - SF‖ := norm_sub_rev _ _
    have h3 : (SF - ES).re = SF.re - ES.re := Complex.sub_re _ _
    rw [hSFre]
    have h4 : ‖ES - SF‖ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := hEtail
    linarith [h1, h2.le, h2.ge, h3.le, h3.ge, h4]
  -- Step 4: the ζ-part
  have hztr := zeta_truncation x hx hβ1 hβ2
  have hxc : ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) = ((((x:ℝ)) ^ (1 - β) : ℝ) : ℂ) := by
    rw [show (1:ℂ) - (β:ℂ) = (((1 - β : ℝ)):ℂ) from by push_cast; ring,
      show ((x:ℂ)) = (((x:ℝ)):ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cpow hx0.le (1 - β)).symm
  have hre_expr : ((((β:ℂ)) - 1) * (Z - SC) - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))).re
      = (β - 1) * (Z.re - SC.re) - ((x:ℝ)) ^ (1 - β) := by
    rw [hxc, show (((β:ℂ)) - 1) = (((β - 1 : ℝ)):ℂ) from by push_cast; ring,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]
  have habs : |(β - 1) * (Z.re - SC.re) - ((x:ℝ)) ^ (1 - β)| ≤ 11 * ((x:ℝ)) ^ (-β) := by
    rw [← hre_expr]
    calc |((((β:ℂ)) - 1) * (Z - SC) - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))).re|
        ≤ ‖(((β:ℂ)) - 1) * (Z - SC) - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ 11 * ((x:ℝ)) ^ (-β) := hztr
  -- SC is the real partial sum
  have hSCre : SC = ((( ∑ n ∈ Icc 1 (x - 1), ((n:ℝ)) ^ (-β) : ℝ)) : ℂ) := by
    rw [hSC, show range x = insert 0 (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    have h0 : (((0:ℕ)):ℂ) ^ (-(β:ℂ)) = 0 := by
      rw [Nat.cast_zero, Complex.zero_cpow]
      simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
      linarith
    rw [h0, zero_add, Finset.sum_congr rfl (fun n _ => cpow_real_cast n β),
      ← Complex.ofReal_sum]
  have hSx : ∑ n ∈ Icc 1 x, ((n:ℝ)) ^ (-β) = SC.re + ((x:ℝ)) ^ (-β) := by
    rw [hSCre, Complex.ofReal_re, show Icc 1 x = insert x (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    ring
  -- S.re ≤ Z.re + (x^{1−β} + 11x^{−β})/(1−β)
  have hSCbound : SC.re ≤ Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    rw [show Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β)
        = Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) * (1 - β)⁻¹ from by ring]
    have hkey : (SC.re - Z.re) * (1 - β) ≤ ((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β) := by
      nlinarith [hlo, hx1β]
    have h2 : SC.re - Z.re ≤ (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) * (1 - β)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1β]
      exact hkey
    linarith
  -- x^{−β} ≤ x^{−β}/(1−β)
  have hxββ : ((x:ℝ)) ^ (-β) ≤ ((x:ℝ)) ^ (-β) / (1 - β) := by
    rw [le_div_iff₀ h1β]
    nlinarith [hxβ, hβ0]
  -- Step 5: the boundary term
  have hlogx : 1 + Real.log x ≤ 9 * ((x:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : Real.log x ≤ ((x:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
      Real.log_le_rpow_div hx0.le (by norm_num)
    have h2 : ((x:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((x:ℝ)) ^ ((1:ℝ)/8) := by ring
    have h3 : (1:ℝ) ≤ ((x:ℝ)) ^ ((1:ℝ)/8) := Real.one_le_rpow hx1r (by norm_num)
    linarith [h1, h2.le, h2.ge, h3]
  have hEx : E x * ((x:ℝ)) ^ (-β) ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) := by
    have h1 : E x ≤ |E x| := le_abs_self _
    have h2 := hE x hx1
    have hcollect78 : ((x:ℝ)) ^ ((3:ℝ)/4) * ((x:ℝ)) ^ ((1:ℝ)/8) = ((x:ℝ)) ^ ((7:ℝ)/8) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have h3 : E x ≤ 9 * C * ((x:ℝ)) ^ ((7:ℝ)/8) := by
      calc E x ≤ C * (((x:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log x)) := le_trans h1 h2
        _ ≤ C * (((x:ℝ)) ^ ((3:ℝ)/4) * (9 * ((x:ℝ)) ^ ((1:ℝ)/8))) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            apply mul_le_mul_of_nonneg_left hlogx (Real.rpow_nonneg hx0.le _)
        _ = 9 * C * (((x:ℝ)) ^ ((3:ℝ)/4) * ((x:ℝ)) ^ ((1:ℝ)/8)) := by ring
        _ = 9 * C * ((x:ℝ)) ^ ((7:ℝ)/8) := by rw [hcollect78]
    have hcollect : ((x:ℝ)) ^ ((7:ℝ)/8) * ((x:ℝ)) ^ (-β) = ((x:ℝ)) ^ (7/8 - β) := by
      rw [← Real.rpow_add hx0]
      congr 1
    calc E x * ((x:ℝ)) ^ (-β) ≤ (9 * C * ((x:ℝ)) ^ ((7:ℝ)/8)) * ((x:ℝ)) ^ (-β) :=
          mul_le_mul_of_nonneg_right h3 hxβ
      _ = 9 * C * (((x:ℝ)) ^ ((7:ℝ)/8) * ((x:ℝ)) ^ (-β)) := by ring
      _ = 9 * C * ((x:ℝ)) ^ (7/8 - β) := by rw [hcollect]
  -- Step 6: assemble
  have hGre : ((lam : ℂ) * Z + ES).re = lam * Z.re + ES.re := by
    rw [Complex.add_re, Complex.re_ofReal_mul]
  rw [hGre]
  -- lam·Σ_{n≤x} n^{−β} bounded
  have hlamS : lam * (∑ n ∈ Icc 1 x, ((n:ℝ)) ^ (-β))
      ≤ lam * Z.re + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β)) := by
    rw [hSx]
    have h1 : SC.re + ((x:ℝ)) ^ (-β)
        ≤ Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β)
          + ((x:ℝ)) ^ (-β) / (1 - β) := by
      linarith [hSCbound, hxββ]
    have h2 : Z.re + (((x:ℝ)) ^ (1 - β) + 11 * ((x:ℝ)) ^ (-β)) / (1 - β)
          + ((x:ℝ)) ^ (-β) / (1 - β)
        = Z.re + ((x:ℝ)) ^ (1 - β) / (1 - β) + 12 * (((x:ℝ)) ^ (-β) / (1 - β)) := by
      ring
    calc lam * (SC.re + ((x:ℝ)) ^ (-β))
        ≤ lam * (Z.re + ((x:ℝ)) ^ (1 - β) / (1 - β)
            + 12 * (((x:ℝ)) ^ (-β) / (1 - β))) := by
          apply mul_le_mul_of_nonneg_left _ hlam
          rw [← h2]
          exact h1
      _ = lam * Z.re + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
            + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β)) := by ring
  have hCx : (0:ℝ) ≤ C * ((x:ℝ)) ^ (7/8 - β) := mul_nonneg hC0 hx78
  linarith [hone, hiden.le, hiden.ge, hlamS, hEx, hSEle, hCx]

/-- **The λ-extraction at a vanishing continuation** (Siegel brick A3-a): when the
    master inequality's `G(β).re` term is `≤ 0` (a zero of the L-product) and
    `x ≥ (820(C+1))^{40}` kills the error term, the main term must carry the unit:
    `1−β ≤ 26·λ·x^{1−β}`. Pure arithmetic — the quantitative heart of the dichotomy. -/
theorem siegel_lambda_extraction (lam C : ℝ) (hlam : 0 ≤ lam) (hC0 : 0 ≤ C)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x)
    (hxC : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ))
    (Gre : ℝ) (hG : Gre ≤ 0)
    (hmaster : 1 ≤ Gre + lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β))
        + 410 * C * ((x:ℝ)) ^ (7/8 - β)) :
    1 - β ≤ 26 * lam * ((x:ℝ)) ^ (1 - β) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hx1r : (1:ℝ) ≤ (x:ℝ) := by
    have : (1:ℕ) ≤ x := by omega
    exact_mod_cast this
  have h1β : (0:ℝ) < 1 - β := by linarith
  have hy0 : (0:ℝ) < 820 * (C + 1) := by linarith
  -- error term ≤ 1/2
  have herr : 410 * C * ((x:ℝ)) ^ (7/8 - β) ≤ 1/2 := by
    have h1 : ((x:ℝ)) ^ (7/8 - β) ≤ ((x:ℝ)) ^ (-(1/40 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1r
      linarith
    have h2 : (820 * (C + 1)) ≤ ((x:ℝ)) ^ ((1/40 : ℝ)) := by
      have h3 : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ^ ((1/40 : ℝ)) ≤ ((x:ℝ)) ^ ((1/40 : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) hxC (by norm_num)
      have h4 : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ^ ((1/40 : ℝ)) = 820 * (C + 1) := by
        rw [← Real.rpow_natCast (820 * (C + 1)) 40, ← Real.rpow_mul hy0.le]
        norm_num
      rw [h4] at h3
      exact h3
    have h5 : ((x:ℝ)) ^ (-(1/40 : ℝ)) ≤ 1 / (820 * (C + 1)) := by
      rw [Real.rpow_neg hx0.le, ← one_div]
      apply one_div_le_one_div_of_le hy0 h2
    have h6 : 410 * C * ((x:ℝ)) ^ (7/8 - β) ≤ 410 * C * (1 / (820 * (C + 1))) := by
      apply mul_le_mul_of_nonneg_left (le_trans h1 h5) (by positivity)
    have h7 : 410 * C * (1 / (820 * (C + 1))) ≤ 1/2 := by
      rw [mul_one_div, div_le_div_iff₀ hy0 (by norm_num)]
      linarith
    linarith
  -- x^{−β} ≤ x^{1−β}
  have hmono : ((x:ℝ)) ^ (-β) ≤ ((x:ℝ)) ^ (1 - β) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1r
    linarith
  have hx1β : (0:ℝ) ≤ ((x:ℝ)) ^ (1 - β) := Real.rpow_nonneg hx0.le _
  -- main-term consolidation: 1/2 ≤ 13·λ·x^{1−β}/(1−β)
  have hmain : (1:ℝ)/2 ≤ 13 * lam * ((x:ℝ)) ^ (1 - β) / (1 - β) := by
    have h8 : 12 * lam * (((x:ℝ)) ^ (-β) / (1 - β))
        ≤ 12 * lam * (((x:ℝ)) ^ (1 - β) / (1 - β)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_div_of_nonneg_right hmono h1β.le
    have h9 : lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        + 12 * lam * (((x:ℝ)) ^ (1 - β) / (1 - β))
        = 13 * lam * ((x:ℝ)) ^ (1 - β) / (1 - β) := by
      ring
    linarith [hmaster, hG, herr, h8]
  -- clear the denominator
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h1β] at hmain
  linarith

/-- **G is the L-product on the slit** (Siegel brick A3-b): the continuation
    `G = λζ + Σ'E(n)Δn` of the Dirichlet series agrees at every real
    `β ∈ (9/10, 1)` with ANY function `P` that is analytic on the slit half-plane
    and equals the L-series on `Re > 1` — in application, `P = ζ·L₁·L₂·L₁₂`,
    which VANISHES at a real zero `β₁` of `L(·,χ₁)`. -/
theorem G_eq_P_at_real (a : ℕ → ℂ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = (lam * n : ℝ) + E n)
    (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (P : ℂ → ℂ)
    (hP : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ P s)
    (hPeq : ∀ s : ℂ, 1 < s.re → LSeries a s = P s)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    (lam : ℂ) * riemannZeta ((β:ℂ))
      + (∑' n : ℕ, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
    = P ((β:ℂ)) := by
  -- the linear E-bound demanded by lseries_eq_G
  have hEb : ∀ n : ℕ, |E n| ≤ (9 * C) * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hE0]
      simp
    · have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
        have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
          Real.log_le_rpow_div hn0.le (by norm_num)
        have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
        have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) := Real.one_le_rpow hn1r (by norm_num)
        linarith [h1, h2.le, h2.ge, h3]
      have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) = ((n:ℝ)) ^ ((7:ℝ)/8) := by
        rw [← Real.rpow_add hn0]
        norm_num
      have h78 : ((n:ℝ)) ^ ((7:ℝ)/8) ≤ (n:ℝ) := by
        calc ((n:ℝ)) ^ ((7:ℝ)/8) ≤ ((n:ℝ)) ^ ((1:ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hn1r (by norm_num)
          _ = (n:ℝ) := Real.rpow_one _
      calc |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := hE n hn
        _ ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            apply mul_le_mul_of_nonneg_left hlogbound (Real.rpow_nonneg hn0.le _)
        _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8)) := by ring
        _ = 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := by rw [hcollect]
        _ ≤ (9 * C) * (n:ℝ) := by
            apply mul_le_mul_of_nonneg_left h78 (by positivity)
  -- the identity theorem
  have h₀re : 9/10 < ((β:ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hβ1
  have h₀ne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  exact eqOn_slit_halfplane
    (fun s : ℂ => (lam : ℂ) * riemannZeta s
      + ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
    P
    (by
      intro s hs hs1
      apply DifferentiableAt.add
      · exact (differentiableAt_riemannZeta hs1).const_mul _
      · exact eseries_differentiableAt E C hC0 hE0 hE s hs)
    hP
    (by
      intro s hs
      rw [← lseries_eq_G a lam E (9 * C) hAE hEb hs (hsum s hs)]
      exact hPeq s hs)
    ((β:ℂ)) h₀re h₀ne

/-- **The λ lower bound at an L-product zero** (Siegel brick A3-c): a nonnegative
    coefficient system with `a(1) = 1`, `A = λ·id + E`, whose continued L-product `P`
    VANISHES at a real `β ∈ (9/10, 1)`, forces `1−β ≤ 26·λ·x^{1−β}` for every
    admissible truncation `x ≥ (820(C+1))^{40}` — Goldfeld's engine, fully wired. -/
theorem siegel_lambda_lower (a : ℕ → ℝ) (lam : ℝ) (E : ℕ → ℝ) (C : ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1) (hlam : 0 ≤ lam)
    (hAE : ∀ n : ℕ, ∑ m ∈ Icc 1 n, a m = lam * n + E n)
    (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => ((a n : ℝ) : ℂ)) s)
    (P : ℂ → ℂ)
    (hP : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ P s)
    (hPeq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => ((a n : ℝ) : ℂ)) s = P s)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (hPzero : P ((β:ℂ)) = 0)
    (x : ℕ) (hx : 2 ≤ x) (hxC : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ)) :
    1 - β ≤ 26 * lam * ((x:ℝ)) ^ (1 - β) := by
  -- the complex partial-sum hypothesis
  have hAEc : ∀ n : ℕ, ∑ m ∈ Icc 1 n, ((a m : ℝ) : ℂ) = ((lam * n : ℝ) : ℂ) + ((E n : ℝ) : ℂ) := by
    intro n
    rw [← Complex.ofReal_sum, hAE n]
    push_cast
    ring
  -- G(β) = P(β) = 0
  have hGP := G_eq_P_at_real (fun n => ((a n : ℝ) : ℂ)) lam E C hAEc hC0 hE0 hE hsum
    P hP hPeq hβ1 hβ2
  have hGzero : ((lam : ℂ) * riemannZeta ((β:ℂ))
      + ∑' n : ℕ, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))).re = 0 := by
    rw [hGP, hPzero]
    exact Complex.zero_re
  -- the master inequality
  have hmaster := goldfeld_master_inequality a lam E C ha0 ha1 hlam hAE hC0 hE0 hE
    hβ1 hβ2 x hx
  -- extract λ
  exact siegel_lambda_extraction lam C hlam hC0 hβ1 hβ2 x hx hxC
    (((lam : ℂ) * riemannZeta ((β:ℂ))
      + ∑' n : ℕ, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))).re)
    (le_of_eq hGzero) hmaster

/-- Values of a quadratic Dirichlet character lie in `{−1, 0, 1}` (A3-d1). -/
lemma real_char_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : χ a = -1 ∨ χ a = 0 ∨ χ a = 1 := by
  by_cases hu : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = 1 := by
        rw [hχ2]
        exact MulChar.one_apply hu
      rw [pow_two, MulChar.mul_apply] at h1
      exact h1
    have hfactor : (χ a - 1) * (χ a + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfactor with h | h
    · right; right
      exact sub_eq_zero.mp h
    · left
      have := eq_neg_of_add_eq_zero_left h
      exact this
  · right; left
    exact MulChar.map_nonunit χ hu

/-- The bare real-valued function of a quadratic Dirichlet character (A3-d0). -/
noncomputable def charFn (q : ℕ) (χ : DirichletCharacter ℂ q) : ℕ → ℝ :=
  fun n => (χ ((n : ZMod q))).re

/-- `charFn` represents `χ` (A3-d2): the character IS the cast of its real values. -/
lemma charFn_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    ((charFn q χ n : ℝ) : ℂ) = χ ((n : ZMod q)) := by
  rcases real_char_repr χ hχ2 ((n : ZMod q)) with h | h | h <;>
    rw [charFn, h] <;> norm_num

/-- `charFn` takes values in `{−1, 0, 1}` (A3-d3). -/
lemma charFn_values {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    charFn q χ n = -1 ∨ charFn q χ n = 0 ∨ charFn q χ n = 1 := by
  rcases real_char_repr χ hχ2 ((n : ZMod q)) with h | h | h <;>
    rw [charFn, h] <;> norm_num

/-- `charFn` is bounded by 1 (A3-d3'). -/
lemma charFn_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    |charFn q χ n| ≤ 1 := by
  rcases charFn_values χ hχ2 n with h | h | h <;> rw [h] <;> norm_num

/-- `charFn` is completely multiplicative (A3-d4). -/
lemma charFn_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (m n : ℕ) :
    charFn q χ (m * n) = charFn q χ m * charFn q χ n := by
  have hc : ((charFn q χ (m * n) : ℝ) : ℂ)
      = ((charFn q χ m * charFn q χ n : ℝ) : ℂ) := by
    rw [charFn_repr χ hχ2 (m * n), Nat.cast_mul, map_mul,
      ← charFn_repr χ hχ2 m, ← charFn_repr χ hχ2 n]
    push_cast
    ring
  exact_mod_cast hc

/-- `charFn 1 = 1` (A3-d5). -/
lemma charFn_one {q : ℕ} (χ : DirichletCharacter ℂ q) : charFn q χ 1 = 1 := by
  rw [charFn, Nat.cast_one, map_one, Complex.one_re]

/-- **Character partial sums are bounded by the modulus** (Siegel brick A3-e):
    for a nontrivial quadratic `χ mod q`, `|Σ_{n≤t} χ(n)| ≤ q` — every block of `q`
    consecutive integers hits each residue once and cancels. The `hG` input of the
    whole divisor-asymptotic ladder. -/
theorem charFn_partial_sum_bound {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    ∀ t : ℕ, |∑ n ∈ Icc 1 t, charFn q χ n| ≤ q := by
  haveI : NeZero q := ⟨by omega⟩
  -- one full block cancels
  have hblock : ∀ m : ℕ, ∑ n ∈ Icc (m + 1) (m + q), charFn q χ n = 0 := by
    intro m
    have hinj : ∀ n₁ ∈ Icc (m + 1) (m + q), ∀ n₂ ∈ Icc (m + 1) (m + q),
        ((n₁ : ZMod q)) = ((n₂ : ZMod q)) → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ heq
      rw [Finset.mem_Icc] at h₁ h₂
      rcases Nat.le_total n₁ n₂ with hle | hle
      · have hmod : n₁ ≡ n₂ [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
        have hdvd : q ∣ n₂ - n₁ := (Nat.modEq_iff_dvd' hle).mp hmod
        have hz : n₂ - n₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
      · have hmod : n₂ ≡ n₁ [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq.symm
        have hdvd : q ∣ n₁ - n₂ := (Nat.modEq_iff_dvd' hle).mp hmod
        have hz : n₁ - n₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
    have himg : (Icc (m + 1) (m + q)).image (fun n : ℕ => ((n : ZMod q)))
        = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn (fun n₁ h₁ n₂ h₂ heq =>
        hinj n₁ (Finset.mem_coe.mp h₁) n₂ (Finset.mem_coe.mp h₂) heq),
        Nat.card_Icc, ZMod.card]
      omega
    have hcsum : ∑ n ∈ Icc (m + 1) (m + q), χ ((n : ZMod q)) = 0 := by
      have h1 : ∑ a ∈ (Icc (m + 1) (m + q)).image (fun n : ℕ => ((n : ZMod q))), χ a
          = ∑ n ∈ Icc (m + 1) (m + q), χ ((n : ZMod q)) := Finset.sum_image hinj
      rw [← h1, himg]
      exact MulChar.sum_eq_zero_of_ne_one hχ1
    have hreal : ((∑ n ∈ Icc (m + 1) (m + q), charFn q χ n : ℝ) : ℂ)
        = ∑ n ∈ Icc (m + 1) (m + q), χ ((n : ZMod q)) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun n _ => charFn_repr χ hχ2 n)
    exact_mod_cast hreal.trans hcsum
  -- strong induction in blocks of q
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.lt_or_ge t q with h | h
    · calc |∑ n ∈ Icc 1 t, charFn q χ n|
          ≤ ∑ n ∈ Icc 1 t, |charFn q χ n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Icc 1 t, (1:ℝ) := Finset.sum_le_sum (fun n _ => charFn_bound χ hχ2 n)
        _ = t := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            norm_num
        _ ≤ q := by
            have : t ≤ q := h.le
            exact_mod_cast this
    · have hsplit : Icc 1 t = Icc 1 (t - q) ∪ Icc (t - q + 1) t := by
        ext n
        simp only [Finset.mem_union, Finset.mem_Icc]
        omega
      have hdisj : Disjoint (Icc 1 (t - q)) (Icc (t - q + 1) t) := by
        rw [Finset.disjoint_left]
        intro n hn hn2
        rw [Finset.mem_Icc] at hn hn2
        omega
      rw [hsplit, Finset.sum_union hdisj]
      have hb := hblock (t - q)
      rw [show t - q + q = t from by omega] at hb
      rw [hb, add_zero]
      exact ih (t - q) (by omega)

/-- **The product-character bridge** (Siegel brick A3-f): the bare real function of
    the level-`q₁q₂` product character is the pointwise product of the bare
    functions — non-units die on both sides, units factor through `changeLevel`. -/
theorem charFn_mul_char {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (n : ℕ) :
    charFn (q₁ * q₂)
      ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n
    = charFn q₁ χ₁ n * charFn q₂ χ₂ n := by
  simp only [charFn, MulChar.mul_apply]
  by_cases hu : IsUnit ((n : ZMod (q₁ * q₂)))
  · have huc : ((hu.unit : (ZMod (q₁ * q₂))ˣ) : ZMod (q₁ * q₂)) = ((n : ZMod (q₁ * q₂))) :=
      IsUnit.unit_spec hu
    have h₁ : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁) ((n : ZMod (q₁ * q₂)))
        = χ₁ ((n : ZMod q₁)) := by
      rw [← huc,
        DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right q₁ q₂) hu.unit,
        huc, ZMod.cast_natCast (dvd_mul_right q₁ q₂)]
    have h₂ : (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ((n : ZMod (q₁ * q₂)))
        = χ₂ ((n : ZMod q₂)) := by
      rw [← huc,
        DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ (dvd_mul_left q₂ q₁) hu.unit,
        huc, ZMod.cast_natCast (dvd_mul_left q₂ q₁)]
    rw [h₁, h₂]
    rcases real_char_repr χ₁ hχ₁2 ((n : ZMod q₁)) with h1 | h1 | h1 <;>
      rcases real_char_repr χ₂ hχ₂2 ((n : ZMod q₂)) with h2 | h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  · rw [MulChar.map_nonunit _ hu, zero_mul, Complex.zero_re]
    have hcop : ¬ Nat.Coprime n (q₁ * q₂) := fun hc =>
      hu ((ZMod.isUnit_iff_coprime n (q₁ * q₂)).mpr hc)
    have hsplit : ¬ Nat.Coprime n q₁ ∨ ¬ Nat.Coprime n q₂ := by
      by_contra hcon
      push_neg at hcon
      exact hcop (Nat.Coprime.mul_right hcon.1 hcon.2)
    rcases hsplit with h | h
    · have hnu : ¬ IsUnit ((n : ZMod q₁)) := fun hun =>
        h ((ZMod.isUnit_iff_coprime _ _).mp hun)
      rw [MulChar.map_nonunit _ hnu, Complex.zero_re, zero_mul]
    · have hnu : ¬ IsUnit ((n : ZMod q₂)) := fun hun =>
        h ((ZMod.isUnit_iff_coprime _ _).mp hun)
      rw [MulChar.map_nonunit _ hnu, Complex.zero_re, mul_zero]

/-- Convolving a power-bounded arithmetic function with a 1-bounded bare function
    raises the power by one (A3-g1a helper). -/
lemma conv_abs_le_pow (F : ArithmeticFunction ℝ) (k : ℕ → ℝ) (t : ℕ)
    (hF : ∀ j : ℕ, |F j| ≤ ((j:ℝ)) ^ t) (hkb : ∀ j, |k j| ≤ 1) (m : ℕ) :
    |(F * toArith k) m| ≤ ((m:ℝ)) ^ (t + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ArithmeticFunction.map_zero, abs_zero, Nat.cast_zero, zero_pow (by omega)]
  · have hkb' : ∀ j : ℕ, |toArith k j| ≤ 1 := by
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [toArith]
      · rw [toArith_apply k j (by omega)]
        exact hkb j
    rw [ArithmeticFunction.mul_apply]
    calc |∑ p ∈ m.divisorsAntidiagonal, F p.1 * toArith k p.2|
        ≤ ∑ p ∈ m.divisorsAntidiagonal, |F p.1 * toArith k p.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ m.divisorsAntidiagonal, ((m:ℝ)) ^ t := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨he, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
          have hp1m : p.1 ≤ m := Nat.le_of_dvd hm (Dvd.intro p.2 he)
          have hcast : ((p.1:ℝ)) ^ t ≤ ((m:ℝ)) ^ t :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hp1m) t
          rw [abs_mul]
          calc |F p.1| * |toArith k p.2| ≤ ((p.1:ℝ)) ^ t * 1 :=
                mul_le_mul (hF p.1) (hkb' p.2) (abs_nonneg _)
                  (le_trans (abs_nonneg _) (hF p.1))
            _ = ((p.1:ℝ)) ^ t := mul_one _
            _ ≤ ((m:ℝ)) ^ t := hcast
      _ = (m.divisorsAntidiagonal.card : ℝ) * ((m:ℝ)) ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((m:ℝ)) * ((m:ℝ)) ^ t := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : m.divisorsAntidiagonal.card ≤ m := by
            have hmap : ∀ p ∈ m.divisorsAntidiagonal, p.1 ∈ Icc 1 m := by
              intro p hp
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              rw [Finset.mem_Icc]
              constructor
              · by_contra h0
                push_neg at h0
                have h1 : p.1 = 0 := by omega
                rw [h1, zero_mul] at he
                omega
              · exact Nat.le_of_dvd hm (Dvd.intro p.2 he)
            have hinj : ∀ p ∈ m.divisorsAntidiagonal, ∀ p' ∈ m.divisorsAntidiagonal,
                p.1 = p'.1 → p = p' := by
              intro p hp p' hp' hfst
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              obtain ⟨he', _⟩ := Nat.mem_divisorsAntidiagonal.mp hp'
              have h1 : p.1 ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at he
                omega
              have h2 : p.2 = p'.2 := by
                apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1)
                rw [he, hfst, he']
              exact Prod.ext hfst h2
            calc m.divisorsAntidiagonal.card ≤ (Icc 1 m).card :=
                  Finset.card_le_card_of_injOn (fun p => p.1)
                    (fun p hp => hmap p hp)
                    (fun p hp p' hp' h => hinj p hp p' hp' h)
              _ = m := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcard
      _ = ((m:ℝ)) ^ (t + 1) := by ring

/-- The quadruple convolution is crudely cubed-bounded (A3-g1a): `|a(m)| ≤ m³`. -/
lemma quad_value_le_cube (g₁ g₂ : ℕ → ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1) (m : ℕ) :
    |(toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m| ≤ ((m:ℝ)) ^ (3:ℕ) := by
  have h12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 :=
        mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h1 : ∀ j : ℕ, |(toArith (fun _ => (1:ℝ))) j| ≤ ((j:ℝ)) ^ (0:ℕ) := by
    intro j
    rw [pow_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [toArith]
    · rw [toArith_apply _ j (by omega)]
      norm_num
  have h2 := fun j => conv_abs_le_pow (toArith (fun _ => (1:ℝ))) g₁ 0 h1 h1b j
  have h3 := fun j => conv_abs_le_pow (toArith (fun _ => (1:ℝ)) * toArith g₁) g₂ 1 h2 h2b j
  exact conv_abs_le_pow (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂)
    (fun k => g₁ k * g₂ k) 2 h3 h12b m

/-- **The E-package** (Siegel brick A3-g1): the hyperbola asymptotic upgraded to the
    Goldfeld-shape error bound at EVERY `n ≥ 1` — `|A(n) − L₁Lk·n| ≤ C·n^{3/4}(1+log n)`
    with `C = 30(1+q₁)(1+B) + 36 + 3|L₁Lk|` (small `n` patched by the cube bound). -/
theorem quad_E_package (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have hB0 : 0 ≤ B := by
    have h0 := hKb 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  refine ⟨30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|, by positivity, ?_⟩
  intro n hn
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := hn
    exact_mod_cast this
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have htge1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by
    have h1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) := Real.one_le_rpow hn1r (by norm_num)
    have h2 : (1:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    nlinarith [h1, h2]
  have ht0 : (0:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by linarith
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · -- n ∈ {1, 2, 3}: cube bound
    have hA : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m| ≤ 36 := by
      calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m|
          ≤ ∑ m ∈ Icc 1 n, |(toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Icc 1 n, ((m:ℝ)) ^ (3:ℕ) :=
            Finset.sum_le_sum (fun m _ => quad_value_le_cube g₁ g₂ h1b h2b m)
        _ ≤ ∑ m ∈ Icc (1:ℕ) 3, ((m:ℝ)) ^ (3:ℕ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_Icc] at hm ⊢
              omega
            · intro m _ _
              positivity
        _ = 36 := by
            rw [show (Icc (1:ℕ) 3 : Finset ℕ) = {1, 2, 3} by decide]
            norm_num [Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
    have h3n : (n:ℝ) ≤ 3 := by
      have : n ≤ 3 := by omega
      exact_mod_cast this
    have hlam : |L₁ * Lk| * (n:ℝ) ≤ 3 * |L₁ * Lk| := by
      nlinarith [abs_nonneg (L₁ * Lk), h3n]
    have htri : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| + |L₁ * Lk * (n:ℝ)| := by
      have h := abs_add_le (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁
          * toArith g₂ * toArith (fun k => g₁ k * g₂ k)) m) (-(L₁ * Lk * (n:ℝ)))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    have habsmul : |L₁ * Lk * (n:ℝ)| = |L₁ * Lk| * (n:ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 36 + 3 * |L₁ * Lk| := by
          rw [habsmul] at htri
          linarith [htri, hA, hlam]
      _ = (36 + 3 * |L₁ * Lk|) * 1 := (mul_one _).symm
      _ ≤ (36 + 3 * |L₁ * Lk|) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left htge1 (by positivity)
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [hq₁, hB0]
  · -- n ≥ 4: the hyperbola asymptotic
    have hmain := quad_coeff_asymptotic g₁ g₂ q₁ B L₁ Lk h1b h2b hL₁ hq₁ hH hKb hLk n h4
    have hconv : Real.sqrt n * Real.sqrt (Real.sqrt n) = ((n:ℝ)) ^ ((3:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
      norm_num
    rw [hconv] at hmain
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 30 * (1 + q₁) * (1 + B) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := hmain
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [abs_nonneg (L₁ * Lk)]

/-- **The character quad system** (Siegel brick A3-g2): for nontrivial quadratic
    `χ₁ mod q₁`, `χ₂ mod q₂` with nontrivial product, the Goldfeld coefficient system
    exists — `L₁, Lk` with their approach rates and the full error package. -/
theorem quad_system_for_chars {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1) :
    ∃ L₁ Lk C : ℝ,
      (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ 0 ≤ C
      ∧ ∀ n : ℕ, 1 ≤ n →
        |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
            * toArith (charFn q₂ χ₂)
            * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m - L₁ * Lk * n|
          ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  have hG₁ := charFn_partial_sum_bound hq₁ χ₁ hχ₁2 hχ₁1
  have hG₂ := charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1
  obtain ⟨L₁, hL₁⟩ := log_mean_exists (charFn q₁ χ₁) ((q₁:ℝ)) hG₁
  -- hH: commute the divisor asymptotic
  have hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)) n - L₁ * M|
        ≤ (1 + 4 * (q₁:ℝ)) * (Real.sqrt M + 1) := by
    intro M hM
    have hcomm : toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        = toArith (charFn q₁ χ₁) * toArith (fun _ => (1:ℝ)) := mul_comm _ _
    rw [hcomm]
    exact divisor_char_asymptotic (charFn q₁ χ₁) ((q₁:ℝ)) L₁ h1b hG₁ hL₁ M hM
  -- the product character is quadratic
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hG₃ := charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1
  -- the product bare function is 1-bounded with q₁q₂-bounded partial sums
  have h12b : ∀ n, |charFn q₁ χ₁ n * charFn q₂ χ₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |charFn q₁ χ₁ n| * |charFn q₂ χ₂ n| ≤ 1 * 1 :=
        mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)|
      ≤ (q₁:ℝ) * (q₂:ℝ) := by
    intro t
    have heq : ∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)
        = ∑ n ∈ Icc 1 t, charFn (q₁ * q₂)
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n :=
      Finset.sum_congr rfl (fun n _ => (charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n).symm)
    rw [heq]
    have h := hG₃ t
    push_cast at h
    exact h
  have hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n|
      ≤ (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) * (Real.sqrt t + 1) :=
    fun t => bounded_conv_sqrt_bound (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) ((q₂:ℝ)) ((q₁:ℝ) * (q₂:ℝ))
      h2b h12b hG₂ hK2 t
  obtain ⟨Lk, hLk⟩ := sqrt_mean_exists
    (fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d)
    (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) hKb
  obtain ⟨C, hC0, hE⟩ := quad_E_package (charFn q₁ χ₁) (charFn q₂ χ₂)
    ((q₁:ℝ)) (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) L₁ Lk h1b h2b hL₁
    (by positivity) hH hKb hLk
  exact ⟨L₁, Lk, C, hL₁, hLk, hC0, hE⟩

end Principia.Common.SW
