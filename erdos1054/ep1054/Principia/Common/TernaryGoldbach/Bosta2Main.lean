/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisCamelo

set_option autoImplicit false

/-!
# `MPB2.MainOddEta2` from `MPTC.EtaHatBound`, PROVED

The main term of `lem:bosta2` (book `typeI.tex` 1058-1103). For `d = qm'` odd and `d ≤ M`, Poisson
(`MPTC.PoissonOdd`, PROVED) writes `T_{d,∘}(β) = ∑_j (ρ/2)(−1)^j η̂₂(ρ(j/2 − dβ))`, `ρ = x/d`; since
`2β = a/q + δ/x`, the index `j₀ = m'a` has `j₀/2 − dβ = −y/2`, `y = dδ/x`, `|y| ≤ 1/2q ≤ 1/2`:

* the `j₀` term is `(x/2d)(−1)^{m'a}η̂₂(−δ/2)`, and `|η̂₂(−δ/2)| ≤ min(1, c₀/(πδ)²) = capM`;
* the other terms total at most `(c₀/2π²)(d/x)∑_{k ≠ 0} (k − y)⁻² ≤ (c₀/2π²)(d/x)(π² − 4)`
  (`off_sum`: pairing `k, −k`, each pair `2(k² + y²)/(k² − y²)²` grows with `y²`, and at
  `y = 1/2` the pairs sum to `π² − 4` by `CscSq.hasSum_inv_sq`).

Summing over `d = qm' ≤ M`: the main terms give `(x/2q)|η̂₂(−δ/2)||μ(q)||∑_{m' ≤ M/q, (m', 2q) = 1}
μ(m')/m'|`, and the error terms `c₀(q/x)(1/8 − 1/2π²)(D/q + 1)²` (`∑_{m' ≤ N odd} m' ≤ (N + 1)²/4`).
-/

namespace Principia.Common.TernaryGoldbach.MPBM

open Principia.Common.Goldbach Set
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTP
  Principia.Common.TernaryGoldbach.MPB2 Principia.Common.TernaryGoldbach.MPc

/-! ## (1) The off-zero frequency sum -/

/-- **`∑_{k ≥ 0} ((k + 1/2)⁻² + (k + 3/2)⁻²) = π² − 4`**, from `CscSq` at `y = 1/2`. -/
theorem half_pairs :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2 + 1 / ((k : ℝ) + 3 / 2) ^ 2)
      (Real.pi ^ 2 - 4) := by
  have hy : ∀ n : ℤ, (1 / 2 : ℝ) + n ≠ 0 := by
    intro n h
    have h2 : (2 * n + 1 : ℝ) = 0 := by linarith
    have : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  have h := CscSq.hasSum_inv_sq (1 / 2) hy
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two, one_pow, div_one] at h
  have sA : Summable fun n : ℕ => 1 / ((1 / 2 : ℝ) + ((n : ℤ) + 1 : ℤ)) ^ 2 := by
    have := (Real.summable_one_div_nat_add_rpow (3 / 2) 2).mpr (by norm_num)
    refine this.congr fun n => ?_
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have sB : Summable fun n : ℕ => 1 / ((1 / 2 : ℝ) + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2 := by
    have := (Real.summable_one_div_nat_add_rpow (1 / 2) 2).mpr (by norm_num)
    refine this.congr fun n => ?_
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hall := HasSum.of_add_one_of_neg_add_one (f := fun n : ℤ => 1 / ((1 / 2 : ℝ) + n) ^ 2)
    sA.hasSum sB.hasSum
  have hv := hall.unique h
  have h4 : (1 : ℝ) / ((1 / 2 : ℝ) + ((0 : ℤ) : ℝ)) ^ 2 = 4 := by norm_num
  rw [h4] at hv
  have hs := sA.hasSum.add sB.hasSum
  rw [show Real.pi ^ 2 - 4 = (∑' n : ℕ, 1 / ((1 / 2 : ℝ) + ((n : ℤ) + 1 : ℤ)) ^ 2) +
    ∑' n : ℕ, 1 / ((1 / 2 : ℝ) + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2 by linarith]
  refine hs.congr_fun fun k => ?_
  push_cast
  ring_nf

/-- **Each pair grows with `y²`**: `(n − y)⁻² + (n + y)⁻² ≤ (n − 1/2)⁻² + (n + 1/2)⁻²` for
`n ≥ 1`, `|y| ≤ 1/2`. -/
theorem pair_le (n y : ℝ) (hn : 1 ≤ n) (hy : |y| ≤ 1 / 2) :
    1 / (n - y) ^ 2 + 1 / (n + y) ^ 2 ≤ 1 / (n - 1 / 2) ^ 2 + 1 / (n + 1 / 2) ^ 2 := by
  have hy1 : -(1 / 2) ≤ y := by linarith [neg_abs_le y]
  have hy2 : y ≤ 1 / 2 := by linarith [le_abs_self y]
  have a1 : 0 < n - y := by linarith
  have a2 : 0 < n + y := by linarith
  have a3 : 0 < n - 1 / 2 := by linarith
  have a4 : 0 < n + 1 / 2 := by linarith
  have hs : y ^ 2 ≤ 1 / 4 := by nlinarith
  have p1 : 0 < n ^ 2 - y ^ 2 := by nlinarith
  have p2 : 0 < n ^ 2 - 1 / 4 := by nlinarith
  have e1 : 1 / (n - y) ^ 2 + 1 / (n + y) ^ 2 = 2 * (n ^ 2 + y ^ 2) / (n ^ 2 - y ^ 2) ^ 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have e2 : 1 / (n - 1 / 2) ^ 2 + 1 / (n + 1 / 2) ^ 2 =
      2 * (n ^ 2 + 1 / 4) / (n ^ 2 - 1 / 4) ^ 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (n ^ 2 + 1 / 4) * (n ^ 2 - y ^ 2) ^ 2 - (n ^ 2 + y ^ 2) * (n ^ 2 - 1 / 4) ^ 2 =
      (1 / 4 - y ^ 2) * ((3 * (n ^ 2) ^ 2 - n ^ 2 / 4) - (n ^ 2 + 1 / 4) * y ^ 2) := by ring
  have hA : 1 ≤ n ^ 2 := by nlinarith
  have f2 : 0 ≤ (3 * (n ^ 2) ^ 2 - n ^ 2 / 4) - (n ^ 2 + 1 / 4) * y ^ 2 := by nlinarith
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - y ^ 2) f2
  nlinarith

/-- **The off-zero sum**: for `|y| ≤ 1/2`, `c ≥ 0` and any `j₀ ∈ ℤ`, the function
`j ↦ [j ≠ j₀]·c/((j − j₀) − y)²` has a sum `≤ c(π² − 4)`. -/
theorem off_sum (c y : ℝ) (hc : 0 ≤ c) (hy : |y| ≤ 1 / 2) (j0 : ℤ) :
    ∃ S : ℝ, HasSum (fun j : ℤ => if j = j0 then 0 else c * (1 / (((j - j0 : ℤ) : ℝ) - y) ^ 2))
      S ∧ S ≤ c * (Real.pi ^ 2 - 4) := by
  set F : ℤ → ℝ := fun k => if k = 0 then 0 else c * (1 / ((k : ℝ) - y) ^ 2) with hF
  have sA : Summable fun n : ℕ => F ((n : ℤ) + 1) := by
    have := ((Real.summable_one_div_nat_add_rpow (1 - y) 2).mpr (by norm_num)).mul_left c
    refine this.congr fun n => ?_
    simp only [hF, if_neg (by omega : ((n : ℤ) + 1) ≠ 0)]
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have sB : Summable fun n : ℕ => F (-((n : ℤ) + 1)) := by
    have := ((Real.summable_one_div_nat_add_rpow (1 + y) 2).mpr (by norm_num)).mul_left c
    refine this.congr fun n => ?_
    simp only [hF, if_neg (by omega : -((n : ℤ) + 1) ≠ 0)]
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hall := HasSum.of_add_one_of_neg_add_one (f := F) sA.hasSum sB.hasSum
  have hF0 : F 0 = 0 := by simp only [hF, if_pos rfl]
  rw [hF0, add_zero] at hall
  have hshift : HasSum (F ∘ (Equiv.subRight j0))
      ((∑' n : ℕ, F ((n : ℤ) + 1)) + ∑' n : ℕ, F (-((n : ℤ) + 1))) :=
    (Equiv.subRight j0).hasSum_iff.mpr hall
  refine ⟨(∑' n : ℕ, F ((n : ℤ) + 1)) + ∑' n : ℕ, F (-((n : ℤ) + 1)), ?_, ?_⟩
  · refine hshift.congr_fun fun j => ?_
    simp only [Function.comp, Equiv.subRight_apply, hF]
    by_cases h : j = j0
    · rw [if_pos h, if_pos (sub_eq_zero.mpr h)]
    · rw [if_neg h, if_neg (sub_ne_zero.mpr h)]
  · rw [← sA.tsum_add sB]
    have hle : ∀ n : ℕ, F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)) ≤
        c * (1 / ((n : ℝ) + 1 / 2) ^ 2 + 1 / ((n : ℝ) + 3 / 2) ^ 2) := by
      intro n
      simp only [hF, if_neg (by omega : ((n : ℤ) + 1) ≠ 0),
        if_neg (by omega : -((n : ℤ) + 1) ≠ 0)]
      have := pair_le ((n : ℝ) + 1) y (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) hy
      push_cast
      have e1 : ((n : ℝ) + 1 - 1 / 2) = (n : ℝ) + 1 / 2 := by ring
      have e2 : ((n : ℝ) + 1 + 1 / 2) = (n : ℝ) + 3 / 2 := by ring
      have e3 : (-((n : ℝ) + 1) - y) ^ 2 = ((n : ℝ) + 1 + y) ^ 2 := by ring
      rw [e1, e2] at this
      rw [e3, ← mul_add]
      exact mul_le_mul_of_nonneg_left this hc
    exact hasSum_le hle (sA.add sB).hasSum (half_pairs.mul_left c)

/-! ## (2) One `T_{d,∘}`: the `j₀` term and the rest -/

/-- **Per-`d` main term, PROVED** (given `EtaHatBound`): if `j₀/2 − dβ = −y/2` with `|y| ≤ 1/2`,
`|T_{d,∘}(β) − (x/2d)(−1)^{j₀}η̂₂((x/d)(−y/2))| ≤ (c₀d/2π²x)(π² − 4)`. -/
theorem tmo_main (hB : EtaHatBound) (x β : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) (j0 : ℤ)
    (y : ℝ) (hy : |y| ≤ 1 / 2) (hj0 : (j0 : ℝ) / 2 - d * β = -y / 2) :
    ‖tmo x β d - ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j0 * etaHat (x / d * (-y / 2))‖ ≤
      c0 * d / (2 * Real.pi ^ 2 * x) * (Real.pi ^ 2 - 4) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : 0 < x / d := by positivity
  have hpi := Real.pi_pos
  have hc0 : (0 : ℝ) ≤ c0 := by unfold c0; norm_num
  have P := poissonOdd_holds x β hx d hd
  have U := P.update j0 0
  obtain ⟨S, hS, hSle⟩ := off_sum (c0 * d / (2 * Real.pi ^ 2 * x)) y (by positivity) hy j0
  have hle := U.norm_le_of_bounded hS fun j => by
    by_cases h : j = j0
    · rw [h, Function.update_self, norm_zero, if_pos rfl]
    · rw [Function.update_of_ne h, if_neg h]
      set k : ℝ := ((j - j0 : ℤ) : ℝ) with hk
      have hk1 : 1 ≤ |k| := by
        rw [hk]
        have : (j - j0 : ℤ) ≠ 0 := sub_ne_zero.mpr h
        have h1 : (1 : ℤ) ≤ |j - j0| := Int.one_le_abs this
        exact_mod_cast h1
      have hky : k - y ≠ 0 := by
        intro h0
        have : |k| = |y| := by rw [sub_eq_zero.mp h0]
        linarith
      have harg : (j : ℝ) / 2 - d * β = (k - y) / 2 := by
        rw [hk]
        push_cast
        linarith
      rw [harg]
      set u := x / d * ((k - y) / 2) with hu
      have hu2 : (2 * Real.pi * u) ^ 2 = Real.pi ^ 2 * (x / d) ^ 2 * (k - y) ^ 2 := by
        rw [hu]; ring
      have hpos : 0 < (2 * Real.pi * u) ^ 2 := by
        rw [hu2]
        have : 0 < (k - y) ^ 2 := by positivity
        positivity
      have hH : ‖etaHat u‖ ≤ c0 / (2 * Real.pi * u) ^ 2 := by
        rw [le_div_iff₀ hpos]; exact hB u
      rw [norm_mul, norm_mul, norm_neg_one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      calc x / d / 2 * ‖etaHat u‖ ≤ x / d / 2 * (c0 / (2 * Real.pi * u) ^ 2) :=
            mul_le_mul_of_nonneg_left hH (by positivity)
        _ = c0 * d / (2 * Real.pi ^ 2 * x) * (1 / (k - y) ^ 2) := by
            rw [hu2]
            field_simp
  rw [hj0] at hle
  have e : (0 : ℂ) - ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j0 * etaHat (x / d * (-y / 2)) +
      tmo x β d =
        tmo x β d - ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j0 * etaHat (x / d * (-y / 2)) := by
    ring
  rw [e] at hle
  linarith

/-! ## (3) Arithmetic of the `d = qm'` terms -/

/-- **Reindexing `d = qm`**: the `d ≤ ⌊x⌋` with `q ∣ d`, `d ≤ M` are the `qm`, `1 ≤ m ≤ M/q`. -/
theorem reindex {β : Type*} [AddCommMonoid β] (F : ℕ → β) (x M : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (hM0 : 0 ≤ M) (hMx : M ≤ x) :
    ∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M), F d =
      ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, F (q * m) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine Finset.sum_nbij' (fun d => d / q) (fun m => q * m) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨h0, _⟩, ⟨k, rfl⟩, hM⟩ := hd
    rw [Finset.mem_Icc, Nat.mul_div_cancel_left k (by omega)]
    refine ⟨by rcases Nat.eq_zero_or_pos k with h | h <;> [simp [h] at h0; omega], ?_⟩
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hqR]
    push_cast at hM
    linarith
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, Finset.mem_Ioc]
    have hm2 : (m : ℝ) ≤ M / q := (Nat.le_floor_iff (by positivity)).mp hm.2
    rw [le_div_iff₀ hqR] at hm2
    have hqm : ((q * m : ℕ) : ℝ) ≤ M := by push_cast; linarith
    refine ⟨⟨Nat.mul_pos (by omega) (by omega), Nat.le_floor (by linarith)⟩,
      dvd_mul_right q m, hqm⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2.1
  · intro m _
    exact Nat.mul_div_cancel_left m (by omega)
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Nat.mul_div_cancel' hd.2.1]

/-- `f(qm) = f(q)f(m)` for the odd indicator. -/
theorem fOdd_mul (q m : ℕ) : MT.fOdd (q * m) = MT.fOdd q * MT.fOdd m := by
  rw [MT.fOdd_apply, MT.fOdd_apply, MT.fOdd_apply, Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one m with h' | h' <;> simp [h, h']

/-- **The μ-sum**: `∑_{m ≤ L} μ(qm)f(qm)/m = μ(q)f(q)·∑_{m ≤ L, (m, 2q) = 1} μ(m)/m`. -/
theorem mu_sum (q L : ℕ) :
    ∑ m ∈ Finset.Icc 1 L, ((ArithmeticFunction.moebius (q * m) : ℤ) : ℝ) * MT.fOdd (q * m) / m =
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
        ∑ m ∈ (Finset.Icc 1 L).filter (fun m => Nat.Coprime m (2 * q)),
          ((ArithmeticFunction.moebius m : ℤ) : ℝ) / m := by
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

/-- **`4∑_{m ≤ L} f(m)m` is `(L + 1)²` (`L` odd) or `L²` (`L` even).** -/
theorem odd_sum_eq (L : ℕ) :
    4 * ∑ m ∈ Finset.Ioc 0 L, MT.fOdd m * m =
      if L % 2 = 1 then ((L : ℝ) + 1) ^ 2 else (L : ℝ) ^ 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), mul_add, ih, MT.fOdd_apply]
    rcases Nat.mod_two_eq_zero_or_one L with h | h
    · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      push_cast
      ring
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]
      push_cast
      ring

/-- **`∑_{m ≤ N odd} m ≤ (N + 1)²/4`.** -/
theorem odd_sum_le (N : ℝ) (hN : 0 ≤ N) :
    ∑ m ∈ Finset.Icc 1 ⌊N⌋₊, MT.fOdd m * m ≤ (N + 1) ^ 2 / 4 := by
  have hI : Finset.Icc 1 ⌊N⌋₊ = Finset.Ioc 0 ⌊N⌋₊ := rfl
  rw [hI]
  have h := odd_sum_eq ⌊N⌋₊
  have hL : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le hN
  have hL0 : (0 : ℝ) ≤ ⌊N⌋₊ := Nat.cast_nonneg _
  have hsq : ((⌊N⌋₊ : ℝ) + 1) ^ 2 ≤ (N + 1) ^ 2 := by nlinarith
  split_ifs at h <;> nlinarith

/-- **`|η̂₂(u)| ≤ 1`** (`|η₂|₁ = 1`). -/
theorem norm_etaHat_le_one (u : ℝ) : ‖etaHat u‖ ≤ 1 := by
  unfold etaHat
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  have h1 : (fun t : ℝ => ‖((HW.eta2 t : ℝ) : ℂ) * e (-(t * u))‖) = HW.eta2 := by
    funext t
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (HW.eta2_nonneg t)]
  rw [h1, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
    fun t ht => HW.eta2_of_nonpos (not_lt.mp ht)]
  exact EN.int_eta2_Ioi

/-- **`|η̂₂(−δ/2)| ≤ min(1, c₀/(πδ)²) = capM`** (given `EtaHatBound`). -/
theorem etaHat_capM (hB : EtaHatBound) (δ : ℝ) :
    ‖etaHat (-δ / 2)‖ ≤ MT.capM (c0 / Real.pi ^ 2) δ := by
  have hpi := Real.pi_pos
  have hc : 0 < c0 / Real.pi ^ 2 := by unfold c0; positivity
  unfold MT.capM
  rcases le_total (δ ^ 2) (c0 / Real.pi ^ 2) with h | h
  · rw [max_eq_left h, div_self hc.ne']
    exact norm_etaHat_le_one _
  · rw [max_eq_right h]
    have hd : 0 < δ ^ 2 := lt_of_lt_of_le hc h
    have := hB (-δ / 2)
    rw [show (2 * Real.pi * (-δ / 2)) ^ 2 = Real.pi ^ 2 * δ ^ 2 by ring] at this
    rw [div_div, le_div_iff₀ (by positivity)]
    linarith

/-! ## (4) The assembly -/

/-- **`MPB2.MainOddEta2` from `EtaHatBound`, PROVED.** -/
theorem mainOddEta2_of (hB : EtaHatBound) : MainOddEta2 := by
  intro x β δ Q0 D a q hq _ h2β hδ hqQ hQ hD1 hDx
  have hx : 0 < x := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpi := Real.pi_pos
  have hc0 : (0 : ℝ) ≤ c0 := by unfold c0; norm_num
  set M := mR x δ q D with hMdef
  have hMge := mR_ge x δ q D Q0 hx hq (by linarith) hδ
  have hM0 : 0 < M := lt_of_lt_of_le (lt_min (by linarith) (by linarith)) hMge
  have hMD : M ≤ D := mR_le x δ q D
  have hMx : M ≤ x := hMD.trans hDx
  -- `|dδ/x| ≤ 1/2` for `d ≤ M`
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
  -- the per-`d` decomposition
  set K : ℝ := c0 / (2 * Real.pi ^ 2 * x) * (Real.pi ^ 2 - 4) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.pi ^ 2 - 4 := by nlinarith [Real.pi_gt_three]
    positivity
  set Mn : ℕ → ℂ := fun d => ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ (((d / q : ℕ) : ℤ) * a) *
    etaHat (-δ / 2) with hMn
  have hper : ∀ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M),
      ‖tmo x β d - Mn d‖ ≤ K * d := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, _⟩, ⟨k, rfl⟩, hdM⟩ := hd
    have hdR : (0 : ℝ) < ((q * k : ℕ) : ℝ) := by exact_mod_cast hd0
    have hkq : q * k / q = k := Nat.mul_div_cancel_left k (by omega)
    have hj0 : ((((q * k / q : ℕ) : ℤ) * a : ℤ) : ℝ) / 2 - ((q * k : ℕ) : ℝ) * β =
        -(((q * k : ℕ) : ℝ) * δ / x) / 2 := by
      have e2 : β = (a / q + δ / x) / 2 := by linarith
      rw [hkq, e2]
      push_cast
      field_simp
      ring
    have := tmo_main hB x β hx (q * k) (by omega) _ _ (hy (q * k) hdM) hj0
    have harg : x / ((q * k : ℕ) : ℝ) * (-(((q * k : ℕ) : ℝ) * δ / x) / 2) = -δ / 2 := by
      field_simp
    rw [harg] at this
    calc ‖tmo x β (q * k) - Mn (q * k)‖
        ≤ c0 * ((q * k : ℕ) : ℝ) / (2 * Real.pi ^ 2 * x) * (Real.pi ^ 2 - 4) := this
      _ = K * ((q * k : ℕ) : ℝ) := by rw [hK]; ring
  set S := (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M) with hS
  set cf : ℕ → ℝ := fun d => MT.aU D d * MT.fOdd d with hcf
  have hsplit : ∑ d ∈ S, ((cf d : ℝ) : ℂ) * tmo x β d =
      ∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d + ∑ d ∈ S, ((cf d : ℝ) : ℂ) * (tmo x β d - Mn d) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  -- the error part
  have herr : ‖∑ d ∈ S, ((cf d : ℝ) : ℂ) * (tmo x β d - Mn d)‖ ≤
      K * q * ((D / q + 1) ^ 2 / 4) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ d ∈ S, ‖((cf d : ℝ) : ℂ) * (tmo x β d - Mn d)‖ ≤ K * (MT.fOdd d * d) := by
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
      calc |cf d| * ‖tmo x β d - Mn d‖ ≤ MT.fOdd d * (K * d) :=
            mul_le_mul hc (hper d hd) (norm_nonneg _) (MT.fOdd_nonneg d)
        _ = K * (MT.fOdd d * d) := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, hS, reindex (fun d => MT.fOdd d * (d : ℝ)) x M q hq hM0.le hMx]
    have h2 : ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, MT.fOdd (q * m) * ((q * m : ℕ) : ℝ) ≤
        q * ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, MT.fOdd m * m := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m _ => ?_
      rw [fOdd_mul]
      push_cast
      have h0 : 0 ≤ (q : ℝ) * (MT.fOdd m * m) :=
        mul_nonneg hqR.le (mul_nonneg (MT.fOdd_nonneg m) (Nat.cast_nonneg m))
      calc MT.fOdd q * MT.fOdd m * ((q : ℝ) * m) = MT.fOdd q * ((q : ℝ) * (MT.fOdd m * m)) := by
            ring
        _ ≤ (q : ℝ) * (MT.fOdd m * m) := mul_le_of_le_one_left h0 (MT.fOdd_le_one q)
    have h3 := odd_sum_le (M / q) (by positivity)
    have h4 : (M / q + 1) ^ 2 ≤ (D / q + 1) ^ 2 := by
      have : M / q ≤ D / q := div_le_div_of_nonneg_right hMD hqR.le
      have : 0 ≤ M / q := by positivity
      nlinarith
    calc K * ∑ m ∈ Finset.Icc 1 ⌊M / q⌋₊, MT.fOdd (q * m) * ((q * m : ℕ) : ℝ)
        ≤ K * (q * ((M / q + 1) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hqR.le)) hK0
      _ ≤ K * q * ((D / q + 1) ^ 2 / 4) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the main part
  have hmain : ∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d = ((x / (2 * q) : ℝ) : ℂ) * (-1 : ℂ) ^ a *
      etaHat (-δ / 2) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * MT.fOdd q *
        muS (2 * q) (M / q) : ℝ) := by
    rw [hS, reindex (fun d => ((cf d : ℝ) : ℂ) * Mn d) x M q hq hM0.le hMx]
    unfold muS
    rw [← mu_sum, Complex.ofReal_sum, Finset.mul_sum]
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
    -- the sign `(−1)^{ma}` is `(−1)^a` whenever `f(qm) ≠ 0`
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
  refine (norm_add_le _ _).trans ?_
  unfold asparto
  have hmn : ‖∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d‖ ≤
      x / (2 * q) * MT.capM (c0 / Real.pi ^ 2) δ * |muS (2 * q) (M / q)| := by
    rw [hmain, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      norm_neg_one_zpow, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity), abs_mul, abs_mul]
    have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have h2 : |MT.fOdd q| ≤ 1 := by
      rw [abs_of_nonneg (MT.fOdd_nonneg q)]; exact MT.fOdd_le_one q
    have h3 := etaHat_capM hB δ
    have h4 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| * |MT.fOdd q| ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hcap : 0 ≤ MT.capM (c0 / Real.pi ^ 2) δ := (norm_nonneg _).trans h3
    calc x / (2 * q) * ‖etaHat (-δ / 2)‖ *
          (|((ArithmeticFunction.moebius q : ℤ) : ℝ)| * |MT.fOdd q| * |muS (2 * q) (M / q)|)
        ≤ x / (2 * q) * MT.capM (c0 / Real.pi ^ 2) δ * (1 * |muS (2 * q) (M / q)|) := by
          gcongr
      _ = _ := by ring
  have hKq : K * q * ((D / q + 1) ^ 2 / 4) =
      c0 * q / x * (1 / 8 - 1 / (2 * Real.pi ^ 2)) * (D / q + 1) ^ 2 := by
    rw [hK]
    field_simp
    ring
  linarith

/-- **`MPB2.MainOddEta2` from the two cited computer checks alone, PROVED.** -/
theorem mainOddEta2_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) : MainOddEta2 :=
  mainOddEta2_of (etaHatBound_of MPTI.etaHatIBP_holds (MPTS.cameloSup_of hG hW))

/-- **`MPc.Bosta2Eta2` from the cited checks and `EsthelEta2` alone, PROVED.** -/
theorem bosta2Eta2_of_esthel (hG : HC.CameloGridCited) (hW : HC.WollustCited)
    (h3 : EsthelEta2) : Bosta2Eta2 :=
  bosta2Eta2_of (MPTS.trompaisEta2_of_cited hG hW) (mainOddEta2_of_cited hG hW) h3

end Principia.Common.TernaryGoldbach.MPBM
