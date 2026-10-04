/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LogHat

set_option autoImplicit false

/-!
# `MPB1.MainLogEta2` from `MPTC.EtaHatLBound` and `MPTC.EtaHatBound`, PROVED

The main term of `lem:bostb1` (book `typeI.tex` 1231-1277, CORRECTED as in `MPB1`). For `d = qm'`
odd, `d ≤ M`: `MPTH.tlo_main` leaves the `j₀ = m'a` term `(x/2d)(−1)^{m'a}ĝ_{x/d}(−δ/2)` with
`ĝ_ρ = log ρ·η̂₂ + ĥ` (`MPTE.gl_hat_lin`), and an error `c₀(1/2 − 2/π²)(d/x)log(x/d)`.

* main: `(x/2q)|μ(q)f(q)|·(|η̂₂(−δ/2)||∑ μ(m)/m·log(x/qm)| + |ĥ(−δ/2)||∑ μ(m)/m|)
  ≤ mainI1` (`MPBM.etaHat_capM`, `MPTH.hHat_capM`, the weighted μ-sum `mu_sum_w`);
* error: `∑_{m' odd, qm' ≤ D} F(qm')/x ≤ D²/(4qx)·log(√e x/D) + 1/e` for `F(t) = t log(x/t)`,
  increasing on `[0, x/e] ⊃ [0, D]` (`D ≤ x/4`), `F ≤ x/e` (`err_sum`): each term but the last is
  at most the mean of `F` over the next cell of length `2q`.
-/

namespace Principia.Common.TernaryGoldbach.MPBL

open Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTP
  Principia.Common.TernaryGoldbach.MPB2 Principia.Common.TernaryGoldbach.MPB1
  Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPTL
  Principia.Common.TernaryGoldbach.MPTE Principia.Common.TernaryGoldbach.MPTH
  Principia.Common.TernaryGoldbach.MPBM

/-! ## (1) The error sum -/

/-- `F(t) = t log x − t log t` (`= t log(x/t)` for `t > 0`). -/
noncomputable def fF (x t : ℝ) : ℝ := t * Real.log x - t * Real.log t

/-- `F ≤ x/e` on `(0, ∞)`. -/
theorem fF_le (x t : ℝ) (hx : 0 < x) (ht : 0 < t) : fF x t ≤ x / Real.exp 1 := by
  unfold fF
  have h := Real.log_le_sub_one_of_pos (show 0 < x / (Real.exp 1 * t) by positivity)
  rw [Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) ht.ne', Real.log_exp] at h
  have he := Real.exp_pos 1
  rw [div_sub_one (by positivity), le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ he]
  nlinarith

/-- `F ≥ 0` on `(0, x]`. -/
theorem fF_nonneg (x t : ℝ) (ht : 0 < t) (htx : t ≤ x) : 0 ≤ fF x t := by
  unfold fF
  have := Real.log_le_log ht htx
  nlinarith

/-- `F' = log x − log t − 1` on `(0, ∞)`. -/
theorem hasDerivAt_fF (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fF x) (Real.log x - Real.log t - 1) t := by
  have := ((hasDerivAt_id' t).mul_const (Real.log x)).sub
    ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht.ne'))
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `F` increases on `[a, b] ⊂ (0, x/e]`: `(b − a)F(a) ≤ ∫_a^b F`. -/
theorem cell_le (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ x / Real.exp 1) : (b - a) * fF x a ≤ ∫ t in a..b, fF x t := by
  have hmono : MonotoneOn (fF x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t ht => (hasDerivAt_fF x t (by linarith [ht.1])).continuousAt.continuousWithinAt)
      (fun t ht => ?_) fun t ht => ?_
    · rw [interior_Icc] at ht
      exact (hasDerivAt_fF x t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [(hasDerivAt_fF x t ht0).deriv]
      have h1 : t ≤ x / Real.exp 1 := by linarith [ht.2]
      have h2 : Real.log t ≤ Real.log (x / Real.exp 1) := Real.log_le_log ht0 h1
      rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h2
      linarith
  have hc : ContinuousOn (fF x) (Icc a b) :=
    fun t ht => (hasDerivAt_fF x t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (hc.intervalIntegrable_of_Icc (μ := volume) hab) fun t ht =>
      hmono (left_mem_Icc.mpr hab) ht ht.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  exact this

/-- `∫_q^D F ≤ (D²/2)log(√e·x/D)` for `0 < q ≤ D ≤ x`. -/
theorem int_fF_le (x q D : ℝ) (hx : 0 < x) (hq : 0 < q) (hqD : q ≤ D) (hDx : D ≤ x) :
    ∫ t in q..D, fF x t ≤ D ^ 2 / 2 * Real.log (Real.sqrt (Real.exp 1) * x / D) := by
  have hD : 0 < D := by linarith
  set G : ℝ → ℝ := fun t => t ^ 2 / 2 * (Real.log x - Real.log t) + t ^ 2 / 4
  have hG : ∀ t, 0 < t → HasDerivAt G (fF x t) t := by
    intro t ht
    have := ((((hasDerivAt_id' t).pow 2).div_const 2).mul
      ((hasDerivAt_const t (Real.log x)).sub (Real.hasDerivAt_log ht.ne'))).add
      (((hasDerivAt_id' t).pow 2).div_const 4)
    refine this.congr_deriv ?_
    unfold fF
    simp only [Pi.pow_apply, Pi.sub_apply]
    field_simp
    ring
  rw [MPTH.ftc G (fF x) q D hq hqD hG
    (fun t ht => (hasDerivAt_fF x t (by linarith [ht.1])).continuousAt.continuousWithinAt)]
  have hGq : 0 ≤ G q := by
    have := Real.log_le_log hq (hqD.trans hDx)
    simp only [G]
    nlinarith [sq_nonneg q]
  have hlog : Real.log (Real.sqrt (Real.exp 1) * x / D) = 1 / 2 + Real.log x - Real.log D := by
    rw [Real.log_div (by positivity) hD.ne', Real.log_mul (by positivity) hx.ne',
      Real.log_sqrt (Real.exp_pos 1).le, Real.log_exp]
  rw [hlog]
  simp only [G] at hGq ⊢
  linarith

/-- Real odd reindexing: `∑_{0<m≤L} f(m)g(m) = ∑_{k<⌈L/2⌉} g(2k+1)`. -/
theorem sum_odd_real (g : ℕ → ℝ) (L : ℕ) :
    ∑ m ∈ Finset.Ioc 0 L, MT.fOdd m * g m = ∑ k ∈ Finset.range ((L + 1) / 2), g (2 * k + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, MT.fOdd_apply]
    rcases Nat.even_or_odd L with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h1 : (L + 1) / 2 = j := by omega
      have h2 : (L + 1 + 1) / 2 = j + 1 := by omega
      have h3 : L + 1 = 2 * j + 1 := by omega
      rw [h1, h2, if_pos (by omega), Finset.sum_range_succ, h3, one_mul]
    · have h1 : (L + 1) / 2 = j + 1 := by omega
      have h2 : (L + 1 + 1) / 2 = j + 1 := by omega
      rw [h1, h2, if_neg (by omega), zero_mul, add_zero]

/-- **The error sum**: `∑_{m ≤ M/q odd} F(qm)/x ≤ D²/(4qx)·log(√e x/D) + 1/e` for
`0 < M ≤ D ≤ x/4`. -/
theorem err_sum (x M D : ℝ) (q : ℕ) (hq : 1 ≤ q) (hx : 0 < x) (hM : 0 < M) (hMD : M ≤ D)
    (hDx : D ≤ x / 4) :
    ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, MT.fOdd m * (fF x (q * m) / x) ≤
      D ^ 2 / (4 * q * x) * Real.log (Real.sqrt (Real.exp 1) * x / D) + 1 / Real.exp 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  have hDe : D ≤ x / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]; nlinarith
  set N := ⌊M / q⌋₊ with hN
  have hNq : (N : ℝ) * q ≤ M := by
    have := Nat.floor_le (show 0 ≤ M / q by positivity)
    rw [le_div_iff₀ hqR] at this; exact this
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := rfl
  rw [hI, sum_odd_real (fun m => fF x (q * m) / x) N]
  set K := (N + 1) / 2 with hK
  have hlogpos : 0 ≤ Real.log (Real.sqrt (Real.exp 1) * x / D) := by
    rcases (show (0 : ℝ) ≤ D by linarith).lt_or_eq with hD | hD
    · apply Real.log_nonneg
      rw [le_div_iff₀ hD, one_mul]
      have : 1 ≤ Real.sqrt (Real.exp 1) := by
        rw [Real.one_le_sqrt]; exact Real.one_le_exp (by norm_num)
      nlinarith
    · rw [← hD, div_zero, Real.log_zero]
  rcases Nat.eq_zero_or_pos K with hK0 | hK0
  · rw [hK0, Finset.sum_range_zero]
    have : 0 ≤ D ^ 2 / (4 * q * x) := by positivity
    have := Real.exp_pos 1
    positivity
  -- all terms but the last, then the last
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [hK', Finset.sum_range_succ]
  have h2K : 2 * K' + 1 ≤ N := by omega
  have hlast : fF x (q * ((2 * K' + 1 : ℕ) : ℝ)) / x ≤ 1 / Real.exp 1 := by
    rw [div_le_div_iff₀ hx (Real.exp_pos 1), one_mul]
    have := fF_le x (q * ((2 * K' + 1 : ℕ) : ℝ)) hx (by positivity)
    rw [le_div_iff₀ (Real.exp_pos 1)] at this
    linarith
  have hcells : ∀ k ∈ Finset.range K', fF x (q * ((2 * k + 1 : ℕ) : ℝ)) / x ≤
      (∫ t in q * ((2 * k + 1 : ℕ) : ℝ)..q * ((2 * (k + 1) + 1 : ℕ) : ℝ), fF x t) /
        (2 * q * x) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk3 : ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * (k + 1) + 1 ≤ N)
    have hb : q * ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤ x / Real.exp 1 := by
      have : q * ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤ q * N := mul_le_mul_of_nonneg_left hk3 hqR.le
      nlinarith
    have hc := cell_le x (q * ((2 * k + 1 : ℕ) : ℝ)) (q * ((2 * (k + 1) + 1 : ℕ) : ℝ)) hx
      (by positivity) (by push_cast; nlinarith) hb
    have hw : q * ((2 * (k + 1) + 1 : ℕ) : ℝ) - q * ((2 * k + 1 : ℕ) : ℝ) = 2 * q := by
      push_cast; ring
    rw [hw] at hc
    rw [div_le_div_iff₀ hx (by positivity)]
    nlinarith
  have hsum := Finset.sum_le_sum hcells
  have hS : ∑ k ∈ Finset.range K',
      (∫ t in q * ((2 * k + 1 : ℕ) : ℝ)..q * ((2 * (k + 1) + 1 : ℕ) : ℝ), fF x t) / (2 * q * x) =
      (∫ t in q * ((2 * 0 + 1 : ℕ) : ℝ)..q * ((2 * K' + 1 : ℕ) : ℝ), fF x t) / (2 * q * x) := by
    rw [← Finset.sum_div, intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ =>
      q * ((2 * k + 1 : ℕ) : ℝ)) fun k _ => ?_]
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have h0 : 0 < min (q * ((2 * k + 1 : ℕ) : ℝ)) (q * ((2 * (k + 1) + 1 : ℕ) : ℝ)) := by
      apply lt_min <;> positivity
    exact (hasDerivAt_fF x t (lt_of_lt_of_le h0 ht.1)).continuousAt.continuousWithinAt
  rw [hS] at hsum
  · have hend : q * ((2 * K' + 1 : ℕ) : ℝ) ≤ D := by
      have : ((2 * K' + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h2K
      nlinarith
    have hstart : q * ((2 * 0 + 1 : ℕ) : ℝ) = q := by push_cast; ring
    rw [hstart] at hsum
    have hq1 : (q : ℝ) ≤ q * ((2 * K' + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((2 * K' + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K' + 1)
      nlinarith
    have hmono : ∫ t in (q : ℝ)..q * ((2 * K' + 1 : ℕ) : ℝ), fF x t ≤
        ∫ t in (q : ℝ)..D, fF x t := by
      refine intervalIntegral.integral_mono_interval le_rfl hq1 hend ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact fF_nonneg x t (by linarith [ht.1]) (by linarith [ht.2])
      · refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) fun t ht =>
          (hasDerivAt_fF x t (by linarith [ht.1])).continuousAt.continuousWithinAt
    have hint := int_fF_le x q D hx hqR (hq1.trans hend) (by linarith)
    have h4 : (∫ t in (q : ℝ)..D, fF x t) / (2 * q * x) ≤
        D ^ 2 / (4 * q * x) * Real.log (Real.sqrt (Real.exp 1) * x / D) := by
      rw [div_le_iff₀ (by positivity)]
      calc ∫ t in (q : ℝ)..D, fF x t ≤ D ^ 2 / 2 * Real.log (Real.sqrt (Real.exp 1) * x / D) := hint
        _ = D ^ 2 / (4 * q * x) * Real.log (Real.sqrt (Real.exp 1) * x / D) * (2 * q * x) := by
            field_simp
            ring
    have h5 := div_le_div_of_nonneg_right hmono (show (0 : ℝ) ≤ 2 * q * x by positivity)
    linarith

/-! ## (2) The weighted μ-sum and the assembly -/

/-- **The weighted μ-sum**: `∑_{m ≤ L} μ(qm)f(qm)/m·w(m) = μ(q)f(q)·∑_{m ≤ L, (m, 2q) = 1}
μ(m)/m·w(m)`. -/
theorem mu_sum_w (q L : ℕ) (w : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 L,
        ((ArithmeticFunction.moebius (q * m) : ℤ) : ℝ) * MT.fOdd (q * m) / m * w m =
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
        ∑ m ∈ (Finset.Icc 1 L).filter (fun m => Nat.Coprime m (2 * q)),
          ((ArithmeticFunction.moebius m : ℤ) : ℝ) / m * w m := by
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fOdd_mul]
  split_ifs with hc
  · have h2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 q) hc
    have hq : Nat.Coprime q m := (Nat.Coprime.coprime_dvd_right (dvd_mul_left q 2) hc).symm
    have hodd : MT.fOdd m = 1 := by
      rw [MT.fOdd_apply, if_pos]
      exact Nat.odd_iff.mp ((Nat.coprime_two_right).mp h2)
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hq, hodd]
    push_cast
    ring
  · rcases Nat.even_or_odd m with he | ho
    · have : MT.fOdd m = 0 := by
        rw [MT.fOdd_apply, if_neg]
        rw [Nat.even_iff] at he
        omega
      rw [this]
      ring
    · have hnc : ¬ Nat.Coprime q m := by
        intro hqm
        apply hc
        exact Nat.Coprime.mul_right ((Nat.coprime_two_right).mpr ho) hqm.symm
      have hμ : ArithmeticFunction.moebius (q * m) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h =>
          hnc (Nat.squarefree_mul_iff.mp h).1
      rw [hμ]
      push_cast
      ring

/-- **`MPB1.MainLogEta2` from `EtaHatBound` and `EtaHatLBound`, PROVED.** -/
theorem mainLogEta2_of (hB : EtaHatBound) (hL : EtaHatLBound) : MainLogEta2 := by
  intro x α δ Q0 D a q hq _ h2α hδ hqQ hQ _ hD3 hDx
  have hD0 : 0 < D := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) hD3
  have hx : 0 < x := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpi := Real.pi_pos
  have hc0 : (0 : ℝ) ≤ c0 := by unfold c0; norm_num
  set M := mR x δ q D with hMdef
  have hMge := mR_ge x δ q D Q0 hx hq (by linarith) hδ
  have hM0 : 0 < M := lt_of_lt_of_le (lt_min (by linarith) hD0) hMge
  have hMD : M ≤ D := mR_le x δ q D
  have hMx : M ≤ x := by linarith
  have hy : ∀ d : ℕ, (d : ℝ) ≤ M → |(d : ℝ) * δ / x| ≤ 1 / 2 := by
    intro d hd
    by_cases h0 : δ = 0
    · rw [h0]; simp
    · have hdM : (d : ℝ) ≤ x / (2 * |δ| * q) := by
        have : M = min (x / (2 * |δ| * q)) D := by rw [hMdef]; unfold mR; rw [if_neg h0]
        rw [this] at hd
        exact hd.trans (min_le_left _ _)
      have hδ0 : 0 < |δ| := abs_pos.mpr h0
      rw [abs_div, abs_mul, Nat.abs_cast, abs_of_pos hx, div_le_iff₀ hx]
      rw [le_div_iff₀ (by positivity)] at hdM
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
  set K : ℝ := c0 * (1 / 2 - 2 / Real.pi ^ 2) with hK
  have hK0 : 0 ≤ K := by
    have : 2 / Real.pi ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
    rw [hK]; nlinarith
  set Mn : ℕ → ℂ := fun d => ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ (((d / q : ℕ) : ℤ) * a) *
    etaHatL (x / d) (-δ / 2) with hMn
  have hper : ∀ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M),
      ‖tlo x α d - Mn d‖ ≤ K * (fF x d / x) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, _⟩, ⟨k, rfl⟩, hdM⟩ := hd
    have hdR : (0 : ℝ) < ((q * k : ℕ) : ℝ) := by exact_mod_cast hd0
    have hkq : q * k / q = k := Nat.mul_div_cancel_left k (by omega)
    have hj0 : ((((q * k / q : ℕ) : ℤ) * a : ℤ) : ℝ) / 2 - ((q * k : ℕ) : ℝ) * α =
        -(((q * k : ℕ) : ℝ) * δ / x) / 2 := by
      have e2 : α = (a / q + δ / x) / 2 := by linarith
      rw [hkq, e2]
      push_cast
      field_simp
      ring
    have := tlo_main hL x α hx (q * k) (by omega) (by linarith) _ _ (hy (q * k) hdM) hj0
    have harg : x / ((q * k : ℕ) : ℝ) * (-(((q * k : ℕ) : ℝ) * δ / x) / 2) = -δ / 2 := by
      field_simp
    rw [harg] at this
    have hfF : fF x ((q * k : ℕ) : ℝ) = ((q * k : ℕ) : ℝ) * Real.log (x / ((q * k : ℕ) : ℝ)) := by
      unfold fF
      rw [Real.log_div hx.ne' hdR.ne']
      ring
    calc ‖tlo x α (q * k) - Mn (q * k)‖
        ≤ c0 * Real.log (x / ((q * k : ℕ) : ℝ)) * ((q * k : ℕ) : ℝ) / (2 * Real.pi ^ 2 * x) *
          (Real.pi ^ 2 - 4) := this
      _ = K * (fF x ((q * k : ℕ) : ℝ) / x) := by
          rw [hK, hfF]
          field_simp
          ring
  set S := (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M) with hS
  set cf : ℕ → ℝ := fun d => MT.aU D d * MT.fOdd d with hcf
  have hsplit : ∑ d ∈ S, ((cf d : ℝ) : ℂ) * tlo x α d =
      ∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d + ∑ d ∈ S, ((cf d : ℝ) : ℂ) * (tlo x α d - Mn d) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  -- the error part
  have herr : ‖∑ d ∈ S, ((cf d : ℝ) : ℂ) * (tlo x α d - Mn d)‖ ≤ errI1 x q D := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ d ∈ S, ‖((cf d : ℝ) : ℂ) * (tlo x α d - Mn d)‖ ≤
        K * (MT.fOdd d * (fF x d / x)) := by
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc : |cf d| ≤ MT.fOdd d := by
        rw [hcf]
        simp only
        rw [abs_mul, abs_of_nonneg (MT.fOdd_nonneg d)]
        have ha : |MT.aU D d| ≤ 1 := by
          unfold MT.aU
          rw [MinSum.truncate_apply]
          split_ifs
          · rw [ArithmeticFunction.intCoe_apply]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
          · simp
        exact mul_le_of_le_one_left (MT.fOdd_nonneg d) ha
      calc |cf d| * ‖tlo x α d - Mn d‖ ≤ MT.fOdd d * (K * (fF x d / x)) :=
            mul_le_mul hc (hper d hd) (norm_nonneg _) (MT.fOdd_nonneg d)
        _ = K * (MT.fOdd d * (fF x d / x)) := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, hS, reindex (fun d => MT.fOdd d * (fF x d / x)) x M q hq hM0.le hMx]
    have h2 : ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, MT.fOdd (q * m) * (fF x ((q * m : ℕ) : ℝ) / x) ≤
        ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, MT.fOdd m * (fF x (q * m) / x) := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      have hm1 : (m : ℝ) ≤ M / q := (Nat.le_floor_iff (by positivity)).mp hm.2
      rw [le_div_iff₀ hqR] at hm1
      have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hnn : 0 ≤ fF x (q * m) / x :=
        div_nonneg (fF_nonneg x _ (by positivity) (by nlinarith)) hx.le
      rw [fOdd_mul]
      push_cast
      calc MT.fOdd q * MT.fOdd m * (fF x (q * m) / x) =
            MT.fOdd q * (MT.fOdd m * (fF x (q * m) / x)) := by ring
        _ ≤ MT.fOdd m * (fF x (q * m) / x) :=
            mul_le_of_le_one_left (mul_nonneg (MT.fOdd_nonneg m) hnn) (MT.fOdd_le_one q)
    have h3 := err_sum x M D q hq hx hM0 hMD hDx
    unfold errI1
    rw [← hK]
    exact mul_le_mul_of_nonneg_left (h2.trans h3) hK0
  -- the main part
  have hmain : ∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d = ((x / (2 * q) : ℝ) : ℂ) * (-1 : ℂ) ^ a *
      (etaHat (-δ / 2) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
        muL (2 * q) (M / q) (x / q) : ℝ) +
       gHat (gl 1) (-δ / 2) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
        muS (2 * q) (M / q) : ℝ)) := by
    rw [hS, reindex (fun d => ((cf d : ℝ) : ℂ) * Mn d) x M q hq hM0.le hMx]
    unfold muL muS
    rw [← mu_sum_w q ⌊M / q⌋₊ (fun n => Real.log (x / q / n)), ← mu_sum q ⌊M / q⌋₊,
      Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hqm : q * m ≤ ⌊D⌋₊ := by
      have h1 : (m : ℝ) ≤ M / q := (Nat.le_floor_iff (by positivity)).mp hm.2
      rw [le_div_iff₀ hqR] at h1
      exact Nat.le_floor (by push_cast; linarith)
    simp only [hcf, hMn]
    rw [show MT.aU D (q * m) = ((ArithmeticFunction.moebius (q * m) : ℤ) : ℝ) by
      unfold MT.aU; rw [MinSum.truncate_apply, if_pos hqm]; rfl]
    rw [Nat.mul_div_cancel_left m (by omega)]
    have hqm0 : (0 : ℝ) < ((q * m : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    have hρ : (0 : ℝ) < x / ((q * m : ℕ) : ℝ) := div_pos hx hqm0
    change _ * (_ * _ * gHat (gl (x / ((q * m : ℕ) : ℝ))) (-δ / 2)) = _
    rw [gl_hat_lin _ hρ]
    have hlog : Real.log (x / ((q * m : ℕ) : ℝ)) = Real.log (x / q / m) := by
      congr 1; push_cast; field_simp
    rw [hlog]
    rcases Nat.even_or_odd m with he | ho
    · have h0 : MT.fOdd (q * m) = 0 := by
        rw [fOdd_mul, MT.fOdd_apply m, if_neg (by rw [Nat.even_iff] at he; omega), mul_zero]
      rw [h0]
      push_cast
      ring
    · have hs : (-1 : ℂ) ^ ((m : ℤ) * a) = (-1 : ℂ) ^ a := by
        rw [zpow_mul, Odd.neg_one_zpow (by exact_mod_cast ho)]
      rw [hs]
      push_cast
      field_simp
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ herr)
  unfold mainI1
  rw [hmain, norm_mul, norm_mul, Complex.norm_real, norm_neg_one_zpow, mul_one, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q| ≤ 1 := by
    rw [abs_mul]
    have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have h2 : |MT.fOdd q| ≤ 1 := by
      rw [abs_of_nonneg (MT.fOdd_nonneg q)]; exact MT.fOdd_le_one q
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hA := etaHat_capM hB δ
  have hBh := hHat_capM δ
  have hcap1 : 0 ≤ MT.capM (c0 / Real.pi ^ 2) δ := (norm_nonneg _).trans hA
  have hcap2 : 0 ≤
      (2 - Real.log 4) * MT.capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ :=
    (norm_nonneg _).trans hBh
  have t1 : ‖etaHat (-δ / 2) * ((((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
      muL (2 * q) (M / q) (x / q) : ℝ) : ℂ)‖ ≤
      MT.capM (c0 / Real.pi ^ 2) δ * |muL (2 * q) (M / q) (x / q)| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc ‖etaHat (-δ / 2)‖ * (|((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q| *
          |muL (2 * q) (M / q) (x / q)|)
        ≤ MT.capM (c0 / Real.pi ^ 2) δ * (1 * |muL (2 * q) (M / q) (x / q)|) := by gcongr
      _ = _ := by ring
  have t2 : ‖gHat (gl 1) (-δ / 2) * ((((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
      muS (2 * q) (M / q) : ℝ) : ℂ)‖ ≤
      (2 - Real.log 4) * MT.capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ *
        |muS (2 * q) (M / q)| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc ‖gHat (gl 1) (-δ / 2)‖ * (|((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q| *
          |muS (2 * q) (M / q)|)
        ≤ (2 - Real.log 4) * MT.capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ *
          (1 * |muS (2 * q) (M / q)|) := by gcongr
      _ = _ := by ring
  have := add_le_add t1 t2
  have hx2 : 0 ≤ x / (2 * q) := by positivity
  calc x / (2 * q) * ‖_ + _‖ ≤ x / (2 * q) * (MT.capM (c0 / Real.pi ^ 2) δ *
        |muL (2 * q) (M / q) (x / q)| +
        (2 - Real.log 4) * MT.capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ *
          |muS (2 * q) (M / q)|) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans this) hx2
    _ = _ := by ring

/-- **`MPB1.MainLogEta2` from the two cited computer checks alone, PROVED.** -/
theorem mainLogEta2_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) : MainLogEta2 :=
  have hB := etaHatBound_of MPTI.etaHatIBP_holds (MPTS.cameloSup_of hG hW)
  mainLogEta2_of hB (etaHatLBound_of hB)

/-- **`MPG.Bostb1Eta2` from the cited checks and `EsthelLogEta2` alone, PROVED.** -/
theorem bostb1Eta2_of_esthel (hG : HC.CameloGridCited) (hW : HC.WollustCited)
    (h3 : EsthelLogEta2) : MPG.Bostb1Eta2 :=
  bostb1Eta2_of (trompaisLogEta2_cited hG hW) (mainLogEta2_of_cited hG hW) h3

end Principia.Common.TernaryGoldbach.MPBL
