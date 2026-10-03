/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.I2PerV
import Principia.Common.PrimePowerSums

set_option autoImplicit false

/-!
# `MPc.I2Arith`, part 2: the sum over `v ≤ V`

`I2PerV.lean` bounds each `T(v) ≤ b2v` by an explicit majorant `Gv(v)`. Here the sum
`∑_{v ≤ V} Λ(v) f(v) Gv(v)` is bounded by an explicit total (`sum_le_tot`), using only:

* Chebyshev, `ψ(n) ≤ 1.1096 n + 1150000` (`PPSum.sum_vM_le`), and Mertens,
  `∑_{n ≤ N} Λ(n)/n ≤ log N + log 4 + 4` (`Mertens.E₁Λ.le`);
* for `v` NOT coprime to `q`: `∑ Λ(v)(v,q)/v ≤ (3/2) log q` and `∑ Λ(v) ≤ (log q/log 3) log N`
  (`PPSum.sum_nc_gcd`, `PPSum.sum_nc_count`) — these `v` carry `|s| ≤ 1` and the trivial
  `m ≤ 2U`;
* for `v` coprime to `q`: `q_v = q`, `eq:ronsard` gives `|s| ≤ min(1, 1.6(q/φ(q))/ℓ*)` with
  `ℓ* = log(x^{1/3}/(24q²))` (`s_le_mR`), and the `eq:kallervo2` factor is `Gc(v)`, antitone in
  `v`, summed by Abel against Chebyshev (`sumG_abel`).
-/

namespace Principia.Common.TernaryGoldbach.I2A

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA Principia.Common.TernaryGoldbach.MPI1
open Finset

/-! ## (0) Definitions -/

/-- `ℓ* = log(x^{1/3}/(24 q²))`. -/
noncomputable def lstar (Y : ℝ) (q : ℕ) : ℝ := Real.log (Y ^ ((1 : ℝ) / 3) / (24 * (q : ℝ) ^ 2))

/-- `q/φ(q)`. -/
noncomputable def Rq (q : ℕ) : ℝ := (q : ℝ) / Nat.totient q

/-- `min(1, 1.6(q/φ(q))/ℓ*)` (and `1` if `ℓ* ≤ 0`): the `eq:grara`/`eq:ronsard` cap. -/
noncomputable def mR (Y : ℝ) (q : ℕ) : ℝ :=
  if 0 < lstar Y q then min 1 (1.6 * Rq q / lstar Y q) else 1

/-- `K = x/(|δ|q)`. -/
noncomputable def KK (Y δ : ℝ) (q : ℕ) : ℝ := Y / (|δ| * q)

/-- **The coprime `eq:kallervo2` factor**, antitone in `n`. -/
noncomputable def Gc (Y δ : ℝ) (q : ℕ) (n : ℕ) : ℝ :=
  1.7721 * min (KK Y δ q / n) (2 * uA Y δ q) +
    0.36788 * Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q)) + 1.7721 + lz δ q / 2

/-- **The per-`v` majorant.** -/
noncomputable def Gv (Y δ : ℝ) (q : ℕ) (v : ℕ) : ℝ :=
  capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) *
      (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v) +
    2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) +
    3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q +
    if |δ| ≤ 1 / (2 * c2) then 0.8219 * cP δ q * uA Y δ q + kq δ q (uA Y δ q) * q
    else 3.8246 * Real.sqrt (cP δ q) *
          (if Nat.Coprime v q then Gc Y δ q v else 2 * uA Y δ q * (1.7721 + lz δ q / 2)) +
        2 * cP δ q * Y ^ ((1 : ℝ) / 3) * (2 + 15.2858 * lz δ q) + 25.03 * q

/-! ## (1) The `μ`-sum cap at coprime `v` -/

/-- `q_v = q` for `(v, q) = 1`. -/
theorem qv_cop (q v : ℕ) (h : Nat.Coprime v q) : qv q v = q := by
  unfold qv; rw [h.gcd_eq_one, Nat.div_one]

/-- `min((3/4)x^{2/3}/(2v), U) ≥ x^{1/3}/12` for `v ≤ V`. -/
theorem M_ge (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (v : ℝ) (hv : 0 < v) (hvV : v ≤ vA Y) :
    Y ^ ((1 : ℝ) / 3) / 12 ≤ min (3 / 4 * Y ^ ((2 : ℝ) / 3) / v / 2) (uA Y δ q) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hs1, hsu⟩ := sqrt_dq Y δ q hY hq hdq hy
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hU := uA_eq Y δ q hY0
  rw [e13, e23]
  rw [← hu_def] at hU
  unfold vA at hvV
  rw [e13] at hvV
  apply le_min
  · rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < u by linarith) 2]
  · rw [hU, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < u by linarith) 2,
      pow_pos (show (0 : ℝ) < u by linarith) 3]

/-- **At coprime `v`, `|s| ≤ mR`.** -/
theorem s_le_mR (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (v : ℕ) (hv1 : 1 ≤ v) (hvV : (v : ℝ) ≤ vA Y) (hcop : Nat.Coprime v q) (M s : ℝ)
    (hM : min (3 / 4 * Y ^ ((2 : ℝ) / 3) / v / 2) (uA Y δ q) ≤ M) (hs : |s| ≤ 1)
    (hron : ((2 * qv q v : ℕ) : ℝ) < M / (qv q v : ℕ) →
      |s| ≤ 4 / 5 * (((2 * qv q v : ℕ) : ℝ) / Nat.totient (2 * qv q v)) /
        Real.log (M / (qv q v : ℕ) / ((2 * qv q v : ℕ) : ℝ))) :
    |s| ≤ mR Y q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  rw [qv_cop q v hcop] at hron
  unfold mR
  split_ifs with hl
  · refine le_min hs ?_
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hM12 := (M_ge Y δ q hY hq hdq hy v hv0 hvV).trans hM
    have hc : 0 < Y ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY0 _
    -- `M/q/(2q) ≥ x^{1/3}/(24q²) = e^{ℓ*} > 1`
    have hge : Y ^ ((1 : ℝ) / 3) / (24 * (q : ℝ) ^ 2) ≤ M / q / ((2 * q : ℕ) : ℝ) := by
      push_cast
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hgt1 : 1 < Y ^ ((1 : ℝ) / 3) / (24 * (q : ℝ) ^ 2) := by
      unfold lstar at hl
      have := Real.exp_log (show 0 < Y ^ ((1 : ℝ) / 3) / (24 * (q : ℝ) ^ 2) by positivity)
      rw [← this]
      exact Real.one_lt_exp_iff.mpr hl
    have hlt : ((2 * q : ℕ) : ℝ) < M / q := by
      have h1 : 1 < M / q / ((2 * q : ℕ) : ℝ) := lt_of_lt_of_le hgt1 hge
      rwa [one_lt_div (by positivity)] at h1
    have hb := hron hlt
    have hlog : lstar Y q ≤ Real.log (M / q / ((2 * q : ℕ) : ℝ)) := by
      unfold lstar
      exact Real.log_le_log (by positivity) hge
    have hR2 := R2_le q hq
    have hRq : ((2 * q : ℕ) : ℝ) / Nat.totient (2 * q) ≤ 2 * Rq q := hR2
    have hRq0 : 0 ≤ ((2 * q : ℕ) : ℝ) / Nat.totient (2 * q) := by positivity
    calc |s| ≤ 4 / 5 * (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q)) /
          Real.log (M / q / ((2 * q : ℕ) : ℝ)) := hb
      _ ≤ 4 / 5 * (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q)) / lstar Y q :=
          div_le_div_of_nonneg_left (by positivity) hl hlog
      _ ≤ 1.6 * Rq q / lstar Y q := by
          apply div_le_div_of_nonneg_right _ hl.le
          linarith
  · exact hs

/-! ## (2) `T(v) ≤ Gv(v)` -/

/-- **The `μ`-sum term of `eq:asparto` at one `v`.** -/
theorem a1_le (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) (v : ℕ) (hv1 : 1 ≤ v) (s : ℝ)
    (hs : |s| ≤ 1) (hsm : Nat.Coprime v q → |s| ≤ mR Y q) :
    Y / v / (2 * ((qv q v : ℕ) : ℝ)) * capM (c0 / Real.pi ^ 2) δ * |s| ≤
      capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) *
        (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcap : 0 ≤ capM (c0 / Real.pi ^ 2) δ := capM_nonneg _ δ (by unfold c0; positivity)
  have hs0 := abs_nonneg s
  split_ifs with hcop
  · rw [qv_cop q v hcop]
    have h := hsm hcop
    have e : capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) * (mR Y q / v) =
        Y / v / (2 * q) * capM (c0 / Real.pi ^ 2) δ * mR Y q := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · have hg0 : 0 < Nat.gcd v q := Nat.gcd_pos_of_pos_left q hv1
    have hgq : Nat.gcd v q ∣ q := Nat.gcd_dvd_right v q
    have hgR : (0 : ℝ) < (Nat.gcd v q : ℕ) := by exact_mod_cast hg0
    have eq : ((qv q v : ℕ) : ℝ) = q / (Nat.gcd v q : ℕ) := by
      unfold qv; exact Nat.cast_div hgq hgR.ne'
    rw [eq]
    have e : Y / v / (2 * (q / (Nat.gcd v q : ℕ))) * capM (c0 / Real.pi ^ 2) δ =
        capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) * (((Nat.gcd v q : ℕ) : ℝ) / v) := by
      field_simp
    rw [e]
    have h0 : 0 ≤ capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) * (((Nat.gcd v q : ℕ) : ℝ) / v) := by
      positivity
    nlinarith

/-- `Gc` is antitone in `n`. -/
theorem Gc_anti (Y δ : ℝ) (q : ℕ) (hK : 0 ≤ KK Y δ q) (hU : 0 ≤ uA Y δ q) (n : ℕ)
    (hn : 0 < n) :
    Gc Y δ q (n + 1) ≤ Gc Y δ q n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : KK Y δ q / ((n + 1 : ℕ) : ℝ) ≤ KK Y δ q / n :=
    div_le_div_of_nonneg_left hK hn0 (by push_cast; linarith)
  have hm : min (KK Y δ q / ((n + 1 : ℕ) : ℝ)) (2 * uA Y δ q) ≤
      min (KK Y δ q / n) (2 * uA Y δ q) := min_le_min_right _ hd
  unfold Gc
  have hs : Real.sqrt (2 * uA Y δ q * min (KK Y δ q / ((n + 1 : ℕ) : ℝ)) (2 * uA Y δ q)) ≤
      Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hm (by linarith)
  linarith

/-- `0 ≤ Gc`. -/
theorem Gc_nonneg (Y δ : ℝ) (q : ℕ) (hK : 0 ≤ KK Y δ q) (hU : 0 ≤ uA Y δ q) (hz : 0 ≤ lz δ q)
    (n : ℕ) : 0 ≤ Gc Y δ q n := by
  unfold Gc
  have : 0 ≤ min (KK Y δ q / n) (2 * uA Y δ q) := le_min (by positivity) (by linarith)
  have := Real.sqrt_nonneg (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q))
  nlinarith

/-- **`T(v) ≤ Gv(v)`** at every `1 ≤ v ≤ V`. -/
theorem b2v_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (v : ℕ) (hv1 : 1 ≤ v) (hvV : (v : ℝ) ≤ vA Y) (s : ℝ) (hs : |s| ≤ 1)
    (hsm : Nat.Coprime v q → |s| ≤ mR Y q) :
    b2v Y δ q v s ≤ Gv Y δ q v := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  have hA := asp_v Y δ q hY0 hq v hv1 s
  have hA1 := a1_le Y δ q hY0 hq v hv1 s hs hsm
  unfold b2v Gv
  by_cases hd : |δ| ≤ 1 / (2 * c2)
  · rw [if_pos hd, if_pos hd]
    have hk := keks_v Y δ q hY hq hdq hy v hv1 hvV
    linarith
  rw [if_neg hd, if_neg hd]
  by_cases hcop : Nat.Coprime v q
  · -- kallervo, coprime
    rw [if_pos hcop] at hA1
    rw [if_pos hcop, if_pos hcop]
    have hδ : 0 < |δ| := lt_of_lt_of_le (by obtain ⟨hc2a, -⟩ := c2_bounds; positivity)
      (le_of_lt (not_le.mp hd))
    have hk := kall_v Y δ q hY hq hδ v hv1 hvV
    have hU := uA_pos Y δ q hY0 hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    obtain ⟨hn1, hnq⟩ := qv_bounds q v hq hv1
    rw [qv_cop q v hcop] at hk hA hA1 ⊢
    have hX : Y / v / (|δ| * (q : ℝ)) = KK Y δ q / v := by unfold KK; field_simp
    rw [hX] at hk
    have hLz : logp (2 * uA Y δ q / (KK Y δ q / v)) ≤ lz δ q := by
      rw [← hX]
      unfold lz logp
      apply max_le_max_right
      apply Real.log_le_log (by positivity)
      exact twoU_X_le Y δ q hY0 hq v q hv0 hvV hqR le_rfl hδ
    have hphi := phi_le (KK Y δ q / v) (uA Y δ q) (lz δ q) (by unfold KK; positivity) hU hLz
    have hsP : 0 ≤ Real.sqrt (cP δ q) := Real.sqrt_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hphi
      (by positivity : (0 : ℝ) ≤ 3.8246 * Real.sqrt (cP δ q))
    unfold Gc
    linarith
  · -- kallervo, not coprime
    rw [if_neg hcop] at hA1
    rw [if_neg hcop, if_neg hcop]
    have hδ : 0 < |δ| := lt_of_lt_of_le (by obtain ⟨hc2a, -⟩ := c2_bounds; positivity)
      (le_of_lt (not_le.mp hd))
    have hk := kall_v Y δ q hY hq hδ v hv1 hvV
    have hU := uA_pos Y δ q hY0 hq
    obtain ⟨hn1, hnq⟩ := qv_bounds q v hq hv1
    have hnR : (1 : ℝ) ≤ (qv q v : ℕ) := by exact_mod_cast hn1
    have hnqR : ((qv q v : ℕ) : ℝ) ≤ q := by exact_mod_cast hnq
    have hX : 0 < Y / v / (|δ| * ((qv q v : ℕ) : ℝ)) := by positivity
    have hLz : logp (2 * uA Y δ q / (Y / v / (|δ| * ((qv q v : ℕ) : ℝ)))) ≤ lz δ q := by
      unfold lz logp
      apply max_le_max_right
      apply Real.log_le_log (by positivity)
      exact twoU_X_le Y δ q hY0 hq v _ hv0 hvV (by linarith) hnqR hδ
    have hm : min ((⌊Y / v / (|δ| * ((qv q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * uA Y δ q) ≤
        2 * uA Y δ q := min_le_right _ _
    have hm0 : 0 ≤ min ((⌊Y / v / (|δ| * ((qv q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * uA Y δ q) :=
      le_min (by positivity) (by linarith)
    have hL0 : 0 ≤ logp (2 * uA Y δ q / (Y / v / (|δ| * ((qv q v : ℕ) : ℝ)))) := le_max_right _ _
    have hprod : min ((⌊Y / v / (|δ| * ((qv q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * uA Y δ q) *
        (1.7721 + logp (2 * uA Y δ q / (Y / v / (|δ| * ((qv q v : ℕ) : ℝ)))) / 2) ≤
        2 * uA Y δ q * (1.7721 + lz δ q / 2) :=
      mul_le_mul hm (by linarith) (by positivity) (by linarith)
    have hsP : 0 ≤ Real.sqrt (cP δ q) := Real.sqrt_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hprod
      (by positivity : (0 : ℝ) ≤ 3.8246 * Real.sqrt (cP δ q))
    linarith

/-! ## (3) The sum over `v` -/

/-- `N = ⌊V⌋`. -/
noncomputable def NN (Y : ℝ) : ℕ := ⌊vA Y⌋₊

/-- `Ψ = 1.1096 N + 1150000 ≥ ψ(N)`. -/
noncomputable def Psi (Y : ℝ) : ℝ := 1.1096 * (NN Y : ℝ) + 1150000

/-- `∑_{v ≤ N} Λ(v) Gc(v)`. -/
noncomputable def SG (Y δ : ℝ) (q : ℕ) : ℝ := ∑ v ∈ Ioc 0 (NN Y), Λ v * Gc Y δ q v

/-- **The total.** -/
noncomputable def TOT (Y δ : ℝ) (q : ℕ) : ℝ :=
  capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) *
      (mR Y q * (Real.log (NN Y) + 5.3863) + 3 / 2 * Real.log q) +
    2.3433 * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) / Y * ((NN Y : ℝ) * Psi Y) +
    3.5743 * uA Y δ q * (Psi Y + eta1 * uA Y δ q / (2 * Y) * ((NN Y : ℝ) * Psi Y)) +
    if |δ| ≤ 1 / (2 * c2) then (0.8219 * cP δ q * uA Y δ q + kq δ q (uA Y δ q) * q) * Psi Y
    else 3.8246 * Real.sqrt (cP δ q) * (SG Y δ q + 2 * uA Y δ q * (1.7721 + lz δ q / 2) *
          (Real.log q / Real.log 3 * Real.log (NN Y))) +
        (2 * cP δ q * Y ^ ((1 : ℝ) / 3) * (2 + 15.2858 * lz δ q) + 25.03 * q) * Psi Y

theorem lf_nonneg (v : ℕ) : 0 ≤ Λ v * fOdd v := mul_nonneg vonMangoldt_nonneg (fOdd_nonneg v)

/-- `∑ Λ(v) f(v) ≤ Ψ`. -/
theorem sum_lf_le (N : ℕ) : ∑ v ∈ Ioc 0 N, Λ v * fOdd v ≤ 1.1096 * (N : ℝ) + 1150000 :=
  PPSum.sum_vM_le (fun v => Λ v * fOdd v)
    (fun v => by have := fOdd_le_one v; have := vonMangoldt_nonneg (n := v); nlinarith) N

/-- `∑ Λ(v) f(v) v ≤ N Ψ`. -/
theorem sum_lfv_le (N : ℕ) :
    ∑ v ∈ Ioc 0 N, Λ v * fOdd v * v ≤ (N : ℝ) * (1.1096 * (N : ℝ) + 1150000) := by
  calc ∑ v ∈ Ioc 0 N, Λ v * fOdd v * v ≤ ∑ v ∈ Ioc 0 N, Λ v * fOdd v * N :=
        sum_le_sum fun v hv => mul_le_mul_of_nonneg_left
          (by exact_mod_cast (mem_Ioc.mp hv).2) (lf_nonneg v)
    _ = (N : ℝ) * ∑ v ∈ Ioc 0 N, Λ v * fOdd v := by rw [← sum_mul, mul_comm]
    _ ≤ (N : ℝ) * (1.1096 * (N : ℝ) + 1150000) :=
        mul_le_mul_of_nonneg_left (sum_lf_le N) (Nat.cast_nonneg N)

/-- **The `μ`-sum part.** -/
theorem sum_a1 (Y : ℝ) (q N : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) (hm0 : 0 ≤ mR Y q) :
    ∑ v ∈ Ioc 0 N, Λ v * fOdd v *
        (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v) ≤
      mR Y q * (Real.log N + 5.3863) + 3 / 2 * Real.log q := by
  simp_rw [mul_ite]
  rw [sum_ite]
  have hmert : ∑ v ∈ Ioc 0 N, Λ v / v ≤ Real.log N + 5.3863 := by
    have h := Mertens.E₁Λ.le (x := (N : ℝ)) (by exact_mod_cast hN)
    unfold Mertens.E₁Λ at h
    rw [Nat.floor_natCast] at h
    have := log4_le
    linarith
  have h1 : ∑ v ∈ (Ioc 0 N).filter (fun v => Nat.Coprime v q), Λ v * fOdd v * (mR Y q / v) ≤
      mR Y q * (Real.log N + 5.3863) := by
    calc ∑ v ∈ (Ioc 0 N).filter (fun v => Nat.Coprime v q), Λ v * fOdd v * (mR Y q / v)
        ≤ ∑ v ∈ (Ioc 0 N).filter (fun v => Nat.Coprime v q), mR Y q * (Λ v / v) := by
          refine sum_le_sum fun v _ => ?_
          have h1 := fOdd_le_one v
          have h2 : 0 ≤ Λ v / v := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg v)
          have e : Λ v * fOdd v * (mR Y q / v) = fOdd v * (mR Y q * (Λ v / v)) := by ring
          rw [e]
          exact mul_le_of_le_one_left (mul_nonneg hm0 h2) h1 |>.trans' (le_of_eq rfl)
      _ ≤ ∑ v ∈ Ioc 0 N, mR Y q * (Λ v / v) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v _ _ =>
            mul_nonneg hm0 (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg v))
      _ = mR Y q * ∑ v ∈ Ioc 0 N, Λ v / v := by rw [mul_sum]
      _ ≤ mR Y q * (Real.log N + 5.3863) := mul_le_mul_of_nonneg_left hmert hm0
  have h2 : ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q),
      Λ v * fOdd v * (((Nat.gcd v q : ℕ) : ℝ) / v) ≤ 3 / 2 * Real.log q := by
    refine le_trans (le_of_eq ?_) (PPSum.sum_nc_gcd N q (by omega))
    refine sum_congr rfl fun v _ => ?_
    rw [fOdd_apply]
    split_ifs <;> ring
  linarith

/-- **The `(1 + |η'|₁Uv/(2x))U` part.** -/
theorem sum_m (Y U : ℝ) (N : ℕ) (hU : 0 ≤ U) (hY : 0 < Y) :
    ∑ v ∈ Ioc 0 N, Λ v * fOdd v * (3.5743 * (1 + eta1 * (U * v / Y) / 2) * U) ≤
      3.5743 * U * ((1.1096 * (N : ℝ) + 1150000) +
        eta1 * U / (2 * Y) * ((N : ℝ) * (1.1096 * (N : ℝ) + 1150000))) := by
  have e : ∀ v : ℕ, Λ v * fOdd v * (3.5743 * (1 + eta1 * (U * v / Y) / 2) * U) =
      3.5743 * U * (Λ v * fOdd v) + 3.5743 * U * (eta1 * U / (2 * Y)) * (Λ v * fOdd v * v) := by
    intro v; field_simp
  simp_rw [e]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have he : 0 ≤ eta1 := by unfold eta1; have := Real.log_two_gt_d9; linarith
  have h1 := sum_lf_le N
  have h2 := sum_lfv_le N
  have hc : 0 ≤ 3.5743 * U * (eta1 * U / (2 * Y)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3.5743 * U),
    mul_le_mul_of_nonneg_left h2 hc]

/-- **A constant times `Λ f`.** -/
theorem sum_lf_const (N : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∑ v ∈ Ioc 0 N, Λ v * fOdd v * C ≤ C * (1.1096 * (N : ℝ) + 1150000) := by
  rw [← sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (sum_lf_le N) hC

/-- **The coprime / non-coprime `eq:kallervo2` part.** -/
theorem sum_kall (Y δ : ℝ) (q N : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) (hG : ∀ v, 0 ≤ Gc Y δ q v)
    (Gn c : ℝ) (hGn : 0 ≤ Gn) (hc : 0 ≤ c) :
    ∑ v ∈ Ioc 0 N, Λ v * fOdd v * (c * (if Nat.Coprime v q then Gc Y δ q v else Gn)) ≤
      c * (∑ v ∈ Ioc 0 N, Λ v * Gc Y δ q v + Gn * (Real.log q / Real.log 3 * Real.log N)) := by
  have e : ∀ v, Λ v * fOdd v * (c * (if Nat.Coprime v q then Gc Y δ q v else Gn)) =
      c * (Λ v * fOdd v * (if Nat.Coprime v q then Gc Y δ q v else Gn)) := fun v => by ring
  simp_rw [e]
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hc
  simp_rw [mul_ite]
  rw [sum_ite]
  have h1 : ∑ v ∈ (Ioc 0 N).filter (fun v => Nat.Coprime v q), Λ v * fOdd v * Gc Y δ q v ≤
      ∑ v ∈ Ioc 0 N, Λ v * Gc Y δ q v := by
    calc ∑ v ∈ (Ioc 0 N).filter (fun v => Nat.Coprime v q), Λ v * fOdd v * Gc Y δ q v
        ≤ ∑ v ∈ (Ioc 0 N).filter (fun v => Nat.Coprime v q), Λ v * Gc Y δ q v := by
          refine sum_le_sum fun v _ => ?_
          have := fOdd_le_one v
          have := vonMangoldt_nonneg (n := v)
          have := hG v
          nlinarith [mul_nonneg (vonMangoldt_nonneg (n := v)) (hG v), fOdd_nonneg v]
      _ ≤ ∑ v ∈ Ioc 0 N, Λ v * Gc Y δ q v :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v _ _ =>
            mul_nonneg vonMangoldt_nonneg (hG v)
  have h2 : ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q), Λ v * fOdd v * Gn ≤
      Gn * (Real.log q / Real.log 3 * Real.log N) := by
    have hc := PPSum.sum_nc_count N q hN (by omega)
    calc ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q), Λ v * fOdd v * Gn
        = Gn * ∑ v ∈ (Ioc 0 N).filter (fun v => ¬ Nat.Coprime v q),
            Λ v * (if v % 2 = 1 then 1 else 0) := by
          rw [mul_sum]
          refine sum_congr rfl fun v _ => ?_
          rw [fOdd_apply]; ring
      _ ≤ Gn * (Real.log q / Real.log 3 * Real.log N) := mul_le_mul_of_nonneg_left hc hGn
  linarith

/-- **`∑ Λ f Gv ≤ TOT`.** -/
theorem sum_le_tot (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hN : 1 ≤ NN Y) :
    ∑ v ∈ Ioc 0 (NN Y), Λ v * fOdd v * Gv Y δ q v ≤ TOT Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hU := uA_pos Y δ q hY0 hq
  have hU1 := uA_ge_one Y δ q hY hq hdq hy
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcap : 0 ≤ capM (c0 / Real.pi ^ 2) δ := capM_nonneg _ δ (by unfold c0; positivity)
  have hm0 : 0 ≤ mR Y q := by
    unfold mR; split_ifs with h
    · refine le_min (by norm_num) (div_nonneg ?_ h.le)
      unfold Rq; positivity
    · norm_num
  obtain ⟨-, -, hP1, -, -⟩ := s_facts Y δ q hY hq hdq hy
  have hsP := Real.sqrt_nonneg (cP δ q)
  have hlz : 0 ≤ lz δ q := le_max_right _ _
  have hA1 := sum_a1 Y q (NN Y) hq hN hm0
  have hS2 : ∑ v ∈ Ioc 0 (NN Y), Λ v * fOdd v *
      (2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q)) ≤
      2.3433 * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) / Y * ((NN Y : ℝ) * Psi Y) := by
    have e : ∀ v : ℕ, Λ v * fOdd v * (2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q)) =
        2.3433 * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) / Y * (Λ v * fOdd v * v) := by
      intro v; field_simp
    simp_rw [e]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_lfv_le _) (by positivity)
  have hSm := sum_m Y (uA Y δ q) (NN Y) hU.le hY0
  unfold Gv TOT
  split_ifs with hd
  · -- keks
    have hkq : 0 ≤ 0.8219 * cP δ q * uA Y δ q + kq δ q (uA Y δ q) * q := by
      have : 0 ≤ kq δ q (uA Y δ q) := by
        unfold kq
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * uA Y δ q by linarith)
        positivity
      positivity
    have hK := sum_lf_const (NN Y) _ hkq
    have e : ∀ v : ℕ, Λ v * fOdd v * (capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) *
        (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v) +
          2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) +
          3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q +
          (0.8219 * cP δ q * uA Y δ q + kq δ q (uA Y δ q) * q)) =
        capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) * (Λ v * fOdd v *
          (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v)) +
        Λ v * fOdd v * (2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q)) +
        Λ v * fOdd v * (3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q) +
        Λ v * fOdd v * (0.8219 * cP δ q * uA Y δ q + kq δ q (uA Y δ q) * q) := fun v => by ring
    simp_rw [e]
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum]
    unfold Psi
    have := mul_le_mul_of_nonneg_left hA1 (by positivity :
      (0 : ℝ) ≤ capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)))
    unfold Psi at hS2
    linarith
  · -- kallervo
    have hGc : ∀ v, 0 ≤ Gc Y δ q v := Gc_nonneg Y δ q (by unfold KK; positivity) hU.le hlz
    have hGn : 0 ≤ 2 * uA Y δ q * (1.7721 + lz δ q / 2) := by positivity
    have hL := sum_kall Y δ q (NN Y) hq hN hGc _ (3.8246 * Real.sqrt (cP δ q)) hGn (by positivity)
    have hcst : 0 ≤ 2 * cP δ q * Y ^ ((1 : ℝ) / 3) * (2 + 15.2858 * lz δ q) + 25.03 * q := by
      have := Real.rpow_pos_of_pos hY0 ((1 : ℝ) / 3)
      positivity
    have hK := sum_lf_const (NN Y) _ hcst
    have e : ∀ v : ℕ, Λ v * fOdd v * (capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) *
        (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v) +
          2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q) +
          3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q +
          (3.8246 * Real.sqrt (cP δ q) *
            (if Nat.Coprime v q then Gc Y δ q v else 2 * uA Y δ q * (1.7721 + lz δ q / 2)) +
            2 * cP δ q * Y ^ ((1 : ℝ) / 3) * (2 + 15.2858 * lz δ q) + 25.03 * q)) =
        capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)) * (Λ v * fOdd v *
          (if Nat.Coprime v q then mR Y q / v else ((Nat.gcd v q : ℕ) : ℝ) / v)) +
        Λ v * fOdd v * (2.3433 * (v / Y) * (uA Y δ q ^ 2 + 2 * uA Y δ q + q)) +
        Λ v * fOdd v * (3.5743 * (1 + eta1 * (uA Y δ q * v / Y) / 2) * uA Y δ q) +
        Λ v * fOdd v * (3.8246 * Real.sqrt (cP δ q) *
            (if Nat.Coprime v q then Gc Y δ q v else 2 * uA Y δ q * (1.7721 + lz δ q / 2))) +
        Λ v * fOdd v * (2 * cP δ q * Y ^ ((1 : ℝ) / 3) * (2 + 15.2858 * lz δ q) + 25.03 * q) :=
      fun v => by ring
    simp_rw [e]
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum]
    unfold Psi SG
    have := mul_le_mul_of_nonneg_left hA1 (by positivity :
      (0 : ℝ) ≤ capM (c0 / Real.pi ^ 2) δ * (Y / (2 * q)))
    unfold Psi at hS2
    linarith

/-! ## (4) Abel on `Gc` -/

/-- **`SG ≤ (A + B) Gc(1) + A ∑_{1 < n ≤ N} Gc(n)`**, `A = 1.1096`, `B = 1150000`. -/
theorem sg_abel (Y δ : ℝ) (q : ℕ) (hK : 0 ≤ KK Y δ q) (hU : 0 ≤ uA Y δ q) (hz : 0 ≤ lz δ q)
    (hN : 1 ≤ NN Y) :
    SG Y δ q ≤ (1.1096 + 1150000) * Gc Y δ q 1 + 1.1096 * ∑ n ∈ Ioc 1 (NN Y), Gc Y δ q n := by
  have h := PPSum.abel_linear (fun n => Λ n) (Gc Y δ q) 1.1096 1150000 0 (NN Y) (by omega)
    (fun n _ => PPSum.sum_vM_le (fun m => Λ m) (fun m => le_refl _) n)
    (fun n hn => Gc_anti Y δ q hK hU n hn) (Gc_nonneg Y δ q hK hU hz _)
  unfold SG
  simpa using h

/-! ## (5) The two `Gc` sums -/

/-- `∑_{1 < n ≤ N} min(K/n, 2U) ≤ 2UN`. -/
theorem smin_le1 (K U : ℝ) (hU : 0 ≤ U) (N : ℕ) :
    ∑ n ∈ Ioc 1 N, min (K / n) (2 * U) ≤ 2 * U * N := by
  calc ∑ n ∈ Ioc 1 N, min (K / n) (2 * U) ≤ ∑ n ∈ Ioc 1 N, 2 * U :=
        sum_le_sum fun n _ => min_le_right _ _
    _ = 2 * U * ((N - 1 : ℕ) : ℝ) := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]; ring
    _ ≤ 2 * U * N := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le N 1) (by linarith)

/-- `∑_{1 < n ≤ N} √(2U min(K/n, 2U)) ≤ 2UN`. -/
theorem ssq_le1 (K U : ℝ) (hU : 0 ≤ U) (N : ℕ) :
    ∑ n ∈ Ioc 1 N, Real.sqrt (2 * U * min (K / n) (2 * U)) ≤ 2 * U * N := by
  calc ∑ n ∈ Ioc 1 N, Real.sqrt (2 * U * min (K / n) (2 * U)) ≤ ∑ n ∈ Ioc 1 N, 2 * U := by
        refine sum_le_sum fun n _ => ?_
        rw [Real.sqrt_le_left (by linarith)]
        have := min_le_right (K / n) (2 * U)
        nlinarith
    _ = 2 * U * ((N - 1 : ℕ) : ℝ) := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]; ring
    _ ≤ 2 * U * N := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le N 1) (by linarith)

/-- `∑_{1 < n ≤ N} min(K/n, 2U) ≤ K + K(log N − log a)` for `1 ≤ a ≤ N`, `2Ua ≤ K`. -/
theorem smin_le2 (K U : ℝ) (hU : 0 ≤ U) (N a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N)
    (hKa : 2 * U * a ≤ K) :
    ∑ n ∈ Ioc 1 N, min (K / n) (2 * U) ≤ K + K * (Real.log N - Real.log a) := by
  have hK : 0 ≤ K := le_trans (by positivity) hKa
  rw [← sum_Ioc_consecutive _ ha haN]
  have h1 : ∑ n ∈ Ioc 1 a, min (K / n) (2 * U) ≤ K :=
    (smin_le1 K U hU a).trans hKa
  have h2 : ∑ n ∈ Ioc a N, min (K / n) (2 * U) ≤ K * (Real.log N - Real.log a) := by
    calc ∑ n ∈ Ioc a N, min (K / n) (2 * U) ≤ ∑ n ∈ Ioc a N, K * (1 / n) :=
          sum_le_sum fun n _ => (min_le_left _ _).trans (le_of_eq (by ring))
      _ = K * ∑ n ∈ Ioc a N, (1 : ℝ) / n := by rw [mul_sum]
      _ ≤ K * (Real.log N - Real.log a) :=
          mul_le_mul_of_nonneg_left (PPSum.sum_inv_le_log a N ha haN) hK
  linarith

/-- `∑_{1 < n ≤ N} √(2U min(K/n, 2U)) ≤ K + 2√(2UK)(√N − √a)` for `1 ≤ a ≤ N`, `2Ua ≤ K`. -/
theorem ssq_le2 (K U : ℝ) (hU : 0 ≤ U) (N a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N)
    (hKa : 2 * U * a ≤ K) :
    ∑ n ∈ Ioc 1 N, Real.sqrt (2 * U * min (K / n) (2 * U)) ≤
      K + 2 * Real.sqrt (2 * U * K) * (Real.sqrt N - Real.sqrt a) := by
  have hK : 0 ≤ K := le_trans (by positivity) hKa
  rw [← sum_Ioc_consecutive _ ha haN]
  have h1 : ∑ n ∈ Ioc 1 a, Real.sqrt (2 * U * min (K / n) (2 * U)) ≤ K :=
    (ssq_le1 K U hU a).trans hKa
  have h2 : ∑ n ∈ Ioc a N, Real.sqrt (2 * U * min (K / n) (2 * U)) ≤
      2 * Real.sqrt (2 * U * K) * (Real.sqrt N - Real.sqrt a) := by
    calc ∑ n ∈ Ioc a N, Real.sqrt (2 * U * min (K / n) (2 * U))
        ≤ ∑ n ∈ Ioc a N, Real.sqrt (2 * U * K) * (1 / Real.sqrt n) := by
          refine sum_le_sum fun n hn => ?_
          have hn0 : (0 : ℝ) < n := by
            have := (mem_Ioc.mp hn).1; exact_mod_cast (by omega : 0 < n)
          calc Real.sqrt (2 * U * min (K / n) (2 * U)) ≤ Real.sqrt (2 * U * (K / n)) :=
                Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith))
            _ = Real.sqrt (2 * U * K) * (1 / Real.sqrt n) := by
                rw [show 2 * U * (K / n) = 2 * U * K / n by ring,
                  Real.sqrt_div' _ hn0.le, mul_one_div]
      _ = Real.sqrt (2 * U * K) * ∑ n ∈ Ioc a N, 1 / Real.sqrt n := by rw [mul_sum]
      _ ≤ Real.sqrt (2 * U * K) * (2 * (Real.sqrt N - Real.sqrt a)) :=
          mul_le_mul_of_nonneg_left (PPSum.sum_inv_sqrt_le a N haN) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt (2 * U * K) * (Real.sqrt N - Real.sqrt a) := by ring
  linarith

end Principia.Common.TernaryGoldbach.I2A
