/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeResWin

set_option autoImplicit false

/-!
# Regime A of `EE.EspagnEdgeRes`: Cover A holds below `70000` once `ϖ(q) ≥ 3`

**The shape of `ϖ` below `70000`.** `ϖ₀(q) = 0` there: `c(1.36)q^τ = A(log q)` is a convex function
of `ℓ = log q` with `A(0) ≤ 1` and `A(11.1572) ≤ 12.1572`, so `A(ℓ) ≤ 1 + ℓ` on `[0, 11.1572]`
and the branch of `ϖ₀` is never taken (`varpi0_small`). The third term
`t₃ = 10⁵/(c_{ρ,2}q)^{1/(1−ω)}` is `≤ 1` from `q ≥ 100` (`t3_le_one`: `c_{ρ,2} ≥ 1`,
`1/(1 − ω) ≥ 2.5`, `100^{2.5} = 10⁵`), and `t₃q ≤ 35356` from `q ≥ 2` (`t3q_le`). So for
`100 ≤ q < 70000` and `ϖ ≥ 3`, `ϖ = K − log q` exactly.

**Cover A** (`EE.CoverA`) with `N = ⌊ϖ⌋ + 1`: the transfer term is bounded once and for all
(`coverA_of`): `(q/φ)f₁(q) ≤ Π_{p≤13} g(p) ≤ 5.1` (`W_le`, `LQ.hipo`), and the cube-root
difference by the mean value bound `x^{−1/3} − y^{−1/3} ≤ (y − x)/(3x·x^{1/3})`
(`rpow_neg_third_sub`), so it is at most `0.28618(N − ϖ)/(ϖ·ϖ^{1/3})`. Then four cases:

* `100 ≤ q`, `3 ≤ ϖ < 4` (`N = 4`): `log(4/ϖ) ≤ log(4/3) ≤ 0.28769`, transfer `≤ 0.06615`, against
  `(1 − ω)(log 10⁵ − log 4 − (K − 3)) ≥ 0.38036`;
* `100 ≤ q`, `ϖ ≥ 4`: `log(N/ϖ) ≤ 1/ϖ`, against `(1 − ω)(log 10⁵ − K + ϖ − log(ϖ + 1)) ≥ 0.6698`;
* `2 ≤ q < 100`: `ϖ ≥ K − log 100 ≥ 7.4948` and `Nq ≤ ϖq + q ≤ 35455 < 10⁵/e`;
* `q = 1`: `ϖ ≥ K ≥ 12.1` and `ϖ ≤ max(K, 10⁵/1.3)`, split at `ϖ = 1000`.
-/

namespace Principia.Common.TernaryGoldbach.ER

open Principia.Common.PSieve (gQ)
open Principia.Common.TernaryGoldbach.HC (omegaE cDeltaE kappaE tauE cSig cRho2 varpi0 varpiE
  errE sumLogP)

/-! ## (1) The shape of `ϖ` -/

/-- `ϖ(q)` spelled with `K`. -/
theorem varpiE_eq (q : ℕ) : varpiE q = max (varpi0 q)
    (max (Kc - Real.log q) (100000 / (cRho2 * q) ^ (1 / (1 - omegaE)))) := rfl

/-- `log 70000 ≤ 11.1572`. -/
theorem log70000_le : Real.log 70000 ≤ 11.1572 := by
  have h := exp_lo 11.1572 (27893 / 20000) 14 8 70000 (by norm_num) (by push_cast; norm_num)
    (by decide +kernel)
  have e : ((70000 : ℚ) : ℝ) = 70000 := by norm_num
  rw [e] at h
  exact log_le_of (by norm_num) h

/-- **`ϖ₀(q) = 0` for `1 ≤ q ≤ 70000`**: the branch `log q + 1 < c(1.36)q^τ` fails. -/
theorem varpi0_small (q : ℕ) (hq : 1 ≤ q) (h7 : q ≤ 70000) : varpi0 q = 0 := by
  unfold varpi0
  rw [if_neg]
  intro hbr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [cq_eq q hq0] at hbr
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlL : Real.log q ≤ 11.1572 := le_trans (Real.log_le_log hq0 (by exact_mod_cast h7))
    log70000_le
  have hAL : Af 11.1572 ≤ 12.1572 := by
    refine le_trans (Af_le 11.1572 11.1572 le_rfl (by norm_num)) ?_
    have h := exp_hi (0.5615454 * (2 / 5 * 11.1572 - 3371 / 20500)) (15086061 / 50000000) 12 8
      (121572 / 10000) (by norm_num) (by norm_num) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
    have e : ((121572 / 10000 : ℚ) : ℝ) = 12.1572 := by norm_num
    rw [e] at h
    exact h
  have hA0 : Af 0 ≤ 1 := by
    unfold Af
    rw [Real.exp_le_one_iff]
    nlinarith [gE_pos]
  set t := Real.log q / 11.1572 with ht
  have ht0 : 0 ≤ t := div_nonneg hl0 (by norm_num)
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by norm_num)]; exact hlL
  have hconv := convexOn_exp.2 (Set.mem_univ (gE * (2 / 5 * 0 - 3371 / 20500)))
    (Set.mem_univ (gE * (2 / 5 * 11.1572 - 3371 / 20500))) (by linarith : 0 ≤ 1 - t) ht0
    (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at hconv
  have e : (1 - t) * (gE * (2 / 5 * 0 - 3371 / 20500)) +
      t * (gE * (2 / 5 * 11.1572 - 3371 / 20500)) = gE * (2 / 5 * Real.log q - 3371 / 20500) := by
    rw [ht]
    field_simp
    ring
  rw [e] at hconv
  have hconv' : Af (Real.log q) ≤ (1 - t) * Af 0 + t * Af 11.1572 := hconv
  have h1 := mul_le_mul_of_nonneg_left hA0 (by linarith : 0 ≤ 1 - t)
  have h2 := mul_le_mul_of_nonneg_left hAL ht0
  have h3 : t * 11.1572 = Real.log q := by rw [ht]; field_simp
  linarith

/-- `100^{2.5} = 10⁵`, so `x^{2.5} ≥ 10⁵` for `x ≥ 100`. -/
theorem rpow_25_ge (x : ℝ) (hx : 100 ≤ x) : 100000 ≤ x ^ (2.5 : ℝ) := by
  have e : (100 : ℝ) ^ (2.5 : ℝ) = 100000 := by
    rw [show (100 : ℝ) = (10 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast_mul (by norm_num),
      show ((2 : ℕ) : ℝ) * 2.5 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [← e]
  exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)

/-- **`t₃(q) ≤ 1` for `q ≥ 100`.** -/
theorem t3_le_one (cer : CY.CERange) (q : ℕ) (hq : 100 ≤ q) :
    100000 / (cRho2 * q) ^ (1 / (1 - omegaE)) ≤ 1 := by
  have hc := cRho2_ge_one cer
  have he := expo_ge cer
  have hq' : (100 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : (100 : ℝ) ≤ cRho2 * q := by nlinarith
  have h1 : (cRho2 * q) ^ (2.5 : ℝ) ≤ (cRho2 * q) ^ (1 / (1 - omegaE)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) he
  have h2 := rpow_25_ge _ hb
  rw [div_le_one (by linarith)]
  linarith

/-- **`t₃(q)·q ≤ 35356` for `q ≥ 2`** (`q^{2.5} ≥ 2√2·q`). -/
theorem t3q_le (cer : CY.CERange) (q : ℕ) (hq : 2 ≤ q) :
    100000 / (cRho2 * q) ^ (1 / (1 - omegaE)) * q ≤ 35356 := by
  have hc := cRho2_ge_one cer
  have he := expo_ge cer
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hb : (q : ℝ) ≤ cRho2 * q := by nlinarith
  have h1 : (q : ℝ) ^ (2.5 : ℝ) ≤ (cRho2 * q) ^ (1 / (1 - omegaE)) :=
    le_trans (Real.rpow_le_rpow hq0.le hb (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le (by linarith) he)
  have hsq : (1.4142 : ℝ) ≤ (q : ℝ) ^ (0.5 : ℝ) := by
    rw [show (0.5 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have h25 : (q : ℝ) ^ (2.5 : ℝ) = (q : ℝ) ^ (2 : ℕ) * (q : ℝ) ^ (0.5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq0]
    norm_num
  have h2 : 2.8284 * (q : ℝ) ≤ (q : ℝ) ^ (2.5 : ℝ) := by
    rw [h25]
    have : (2 : ℝ) * q ≤ (q : ℝ) ^ (2 : ℕ) := by nlinarith
    nlinarith
  have hpos : 0 < (cRho2 * q) ^ (1 / (1 - omegaE)) := by
    have : 0 < cRho2 * q := by nlinarith
    exact Real.rpow_pos_of_pos this _
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith

/-- **`t₃(1) ≤ 10⁵/1.3`** (`c_{ρ,2}^{1/(1−ω)} ≥ e^{2.5·0.1109} ≥ 1.3`). -/
theorem t3_one (cer : CY.CERange) (q : ℕ) (hq : q = 1) :
    100000 / (cRho2 * q) ^ (1 / (1 - omegaE)) ≤ 100000 / 1.3 := by
  subst hq
  have hc := cRho2_ge cer
  have he := expo_ge cer
  have hc0 : 0 < cRho2 := lt_of_lt_of_le (Real.exp_pos _) hc
  have hlc : 0.1109 ≤ Real.log cRho2 := log_ge_of hc0 hc
  rw [Nat.cast_one, mul_one, Real.rpow_def_of_pos hc0]
  have h1 : (0.27725 : ℝ) ≤ Real.log cRho2 * (1 / (1 - omegaE)) := by nlinarith
  have h2 := exp_lo (Real.log cRho2 * (1 / (1 - omegaE))) (1109 / 32000) 14 8 (13 / 10)
    (by norm_num) (by push_cast; linarith) (by decide +kernel)
  have e : ((13 / 10 : ℚ) : ℝ) = 1.3 := by norm_num
  rw [e] at h2
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2

/-! ## (2) The transfer term of Cover A -/

/-- **Mean value bound for `x^{−1/3}`**: `x^{−1/3} − y^{−1/3} ≤ (y − x)/(3x·x^{1/3})`. -/
theorem rpow_neg_third_sub (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    x ^ (-(1 : ℝ) / 3) - y ^ (-(1 : ℝ) / 3) ≤ (y - x) / (3 * x * x ^ ((1 : ℝ) / 3)) := by
  have hy : 0 < y := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = x ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos hx _
  have hab : a ≤ b := by rw [ha, hb]; exact Real.rpow_le_rpow hx.le hxy (by norm_num)
  have ha3 : a ^ 3 = x := by rw [ha]; exact LQ.cube_cbrt hx.le
  have hb3 : b ^ 3 = y := by rw [hb]; exact LQ.cube_cbrt hy.le
  have hneg : ∀ z : ℝ, 0 < z → z ^ (-(1 : ℝ) / 3) = (z ^ ((1 : ℝ) / 3))⁻¹ := fun z hz => by
    rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg hz.le]
  rw [hneg x hx, hneg y hy, ← ha, ← hb, ← ha3, ← hb3]
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have e : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : 0 ≤ (b - a) * a * ((a ^ 2 + a * b + b ^ 2) * b - 3 * a ^ 3) := by
    have h1 : 0 ≤ b - a := by linarith
    have h3 : 3 * a ^ 2 ≤ a ^ 2 + a * b + b ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hab ha0.le, mul_le_mul hab hab ha0.le hb0.le]
    have h2 : 3 * a ^ 3 ≤ (a ^ 2 + a * b + b ^ 2) * b := by
      have h4 := mul_le_mul h3 hab ha0.le
        (add_nonneg (add_nonneg (sq_nonneg a) (mul_pos ha0 hb0).le) (sq_nonneg b))
      have e3 : 3 * a ^ 2 * a = 3 * a ^ 3 := by ring
      linarith
    have := mul_nonneg (mul_nonneg h1 ha0.le) (by linarith : 0 ≤ (a ^ 2 + a * b + b ^ 2) * b -
      3 * a ^ 3)
    exact this
  nlinarith [hk]

/-- `(q/φ)f₁(q) ≤ 5.1` for `q < 510510`: `LQ.hipo` at `n = 16` and `Π_{p≤13} g(p) ≤ 5.0843`. -/
theorem W_le (q : ℕ) (hq : 1 ≤ q) (hq5 : q < 510510) : (q : ℝ) / q.totient * CY.f1 q ≤ 5.1 := by
  have hpr : primorial (16 + 1) = 510510 := by decide
  have h := (LQ.hipo q 16 hq (by norm_num) (by rw [hpr]; exact hq5)).2
  rw [LQ.mert_f1_eq 16] at h
  have hf : (Finset.range (16 + 1)).filter Nat.Prime = {2, 3, 5, 7, 11, 13} := by decide
  rw [hf] at h
  have h2 : ∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), LQ.gP p ≤
      ∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), (gHi p : ℝ) := by
    refine Finset.prod_le_prod (fun p hp => le_trans zero_le_one (LQ.one_le_gP p ?_))
      (fun p hp => gP_le_gHi p hp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have h3 : (∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), gHi p : ℚ) ≤ 51 / 10 := by decide +kernel
  have h3' : ((∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), gHi p : ℚ) : ℝ) ≤ ((51 / 10 : ℚ) : ℝ) := by
    exact_mod_cast h3
  push_cast at h3'
  linarith

/-- **Cover A from one numeric inequality** (`q < 510510`, `ϖ ≥ 1`): the transfer term is at
most `0.28618(N − ϖ)/(ϖ·ϖ^{1/3})`. -/
theorem coverA_of (cer : CY.CERange) (q : ℕ) (hq : 1 ≤ q) (hq5 : q < 510510)
    (hv1 : 1 ≤ varpiE q)
    (h : Real.log ((EE.edgeN q : ℝ) / varpiE q) + 0.28618 * (((EE.edgeN q : ℝ) - varpiE q) /
        (varpiE q * varpiE q ^ ((1 : ℝ) / 3))) ≤
      (1 - omegaE) * Real.log (100000 / ((EE.edgeN q : ℝ) * q))) :
    EE.CoverA q := by
  unfold EE.CoverA
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = varpiE q := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (EE.edgeN q : ℝ) := ⟨_, rfl⟩
  rw [← hv, ← hN] at h ⊢
  have hv1' : 1 ≤ v := by rw [hv]; exact hv1
  have hNe : N = (⌊v⌋₊ : ℝ) + 1 := by rw [hN, hv]; unfold EE.edgeN; push_cast; rfl
  have hvN : v < N := by rw [hNe]; exact Nat.lt_floor_add_one v
  have hω := LQ.omegaE_le cer
  have hω0 := omega_lo cer
  have hW := W_le q hq hq5
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hW0 : 0 ≤ (q : ℝ) / q.totient * CY.f1 q :=
    mul_nonneg (div_nonneg hq0.le hφ.le) (HX.f1_nonneg q)
  -- the cube-root difference
  have hv0 : 0 < v := by linarith
  have hcube := rpow_neg_third_sub (20000 * v) (20000 * N) (by positivity) (by linarith)
  have h20 : (20000 * v) ^ ((1 : ℝ) / 3) = (20000 : ℝ) ^ ((1 : ℝ) / 3) * v ^ ((1 : ℝ) / 3) :=
    Real.mul_rpow (by norm_num) hv0.le
  have hc20 := LQ.cbrt20000_ge
  have hvc : 0 < v ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hv0 _
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (N - v) / (v * v ^ ((1 : ℝ) / 3)) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact div_nonneg (by linarith) (by positivity)
  have hcY : (20000 * N - 20000 * v) / (3 * (20000 * v) * (20000 * v) ^ ((1 : ℝ) / 3)) =
      Y / (3 * (20000 : ℝ) ^ ((1 : ℝ) / 3)) := by
    rw [h20, hY]
    field_simp
  have hY3 : Y / (3 * (20000 : ℝ) ^ ((1 : ℝ) / 3)) ≤ Y / (3 * 27.144) :=
    div_le_div_of_nonneg_left hY0 (by norm_num) (by linarith)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (20000 * v) ^ (-(1 : ℝ) / 3) - (20000 * N) ^ (-(1 : ℝ) / 3) :=
    ⟨_, rfl⟩
  have hcle : c ≤ Y / (3 * 27.144) := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by
    rw [hc, sub_nonneg]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [← hc]
  -- the transfer term
  have hT : (q : ℝ) / q.totient * (omegaE * (7.284 * CY.f1 q * c)) ≤ 0.28618 * Y := by
    have e : (q : ℝ) / q.totient * (omegaE * (7.284 * CY.f1 q * c)) =
        omegaE * 7.284 * ((q : ℝ) / q.totient * CY.f1 q) * c := by ring
    rw [e]
    have h1 : omegaE * 7.284 * ((q : ℝ) / q.totient * CY.f1 q) ≤ 0.62732 * 7.284 * 5.1 :=
      mul_le_mul (by nlinarith) hW hW0 (by norm_num)
    have h2 := mul_le_mul h1 hcle hc0 (by norm_num)
    have h3 : (0.62732 : ℝ) * 7.284 * 5.1 * (Y / (3 * 27.144)) ≤ 0.28618 * Y := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  have hmax : (1 - omegaE) * Real.log (100000 / (N * q)) ≤
      (1 - omegaE) * max 0 (Real.log (100000 / (N * q))) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  rw [hY] at hT
  linarith

/-! ## (3) Regime A -/

/-- **The left side of Cover A, crudely**: `ϖ ≥ v₀ ≥ c³ > 0`, `ϖ < N ≤ ϖ + 1` ⟹
`log(N/ϖ) + 0.28618(N − ϖ)/(ϖϖ^{1/3}) ≤ 1/v₀ + 0.28618/(v₀c)`. -/
theorem lhs_le (v N vm cm : ℝ) (hvm : vm ≤ v) (hvm0 : 0 < vm) (hcm0 : 0 < cm)
    (hc : cm ^ 3 ≤ vm) (hvN : v < N) (hNv : N ≤ v + 1) :
    Real.log (N / v) + 0.28618 * ((N - v) / (v * v ^ ((1 : ℝ) / 3))) ≤
      1 / vm + 0.28618 / (vm * cm) := by
  have hv0 : 0 < v := by linarith
  have hN0 : 0 < N := by linarith
  have hlog : Real.log (N / v) ≤ N / v - 1 := Real.log_le_sub_one_of_pos (div_pos hN0 hv0)
  have e : N / v - 1 = (N - v) / v := by field_simp
  have h1 : (N - v) / v ≤ 1 / vm := by
    rw [div_le_div_iff₀ hv0 hvm0]
    nlinarith
  have hvc : cm ≤ v ^ ((1 : ℝ) / 3) := LQ.le_cbrt hv0.le (by linarith)
  have hprod : vm * cm ≤ v * v ^ ((1 : ℝ) / 3) := mul_le_mul hvm hvc hcm0.le hv0.le
  have hpos : 0 < v * v ^ ((1 : ℝ) / 3) := mul_pos hv0 (Real.rpow_pos_of_pos hv0 _)
  have h2 : (N - v) / (v * v ^ ((1 : ℝ) / 3)) ≤ 1 / (vm * cm) := by
    rw [div_le_div_iff₀ hpos (mul_pos hvm0 hcm0)]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 0.28618)
  have e2 : (0.28618 : ℝ) * (1 / (vm * cm)) = 0.28618 / (vm * cm) := by ring
  linarith

/-- **The left side of Cover A at `N = 4`** (used for `3 ≤ ϖ < 4`; only `ϖ ≥ 3` is needed). -/
theorem lhs_le4 (v : ℝ) (hv3 : 3 ≤ v) :
    Real.log (4 / v) + 0.28618 * ((4 - v) / (v * v ^ ((1 : ℝ) / 3))) ≤
      0.28769 + 0.28618 / (3 * 1.4422) := by
  have hv0 : 0 < v := by linarith
  have hl43 : Real.log (4 / v) ≤ 0.28769 := by
    have h := exp_lo 0.28769 (28769 / 800000) 14 8 (4 / 3) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    have e : ((4 / 3 : ℚ) : ℝ) = 4 / 3 := by norm_num
    rw [e] at h
    refine le_trans (Real.log_le_log (by positivity) ?_) (log_le_of (by norm_num) h)
    rw [div_le_div_iff₀ hv0 (by norm_num)]
    linarith
  have hvc : (1.4422 : ℝ) ≤ v ^ ((1 : ℝ) / 3) := LQ.le_cbrt hv0.le (by norm_num; linarith)
  have hprod : (3 : ℝ) * 1.4422 ≤ v * v ^ ((1 : ℝ) / 3) := mul_le_mul hv3 hvc (by norm_num) hv0.le
  have hpos : 0 < v * v ^ ((1 : ℝ) / 3) := mul_pos hv0 (Real.rpow_pos_of_pos hv0 _)
  have h2 : (4 - v) / (v * v ^ ((1 : ℝ) / 3)) ≤ 1 / (3 * 1.4422) := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 0.28618)
  have e2 : (0.28618 : ℝ) * (1 / (3 * 1.4422)) = 0.28618 / (3 * 1.4422) := by ring
  linarith

/-- **`ϖ = K − log q` for `100 ≤ q < 70000` once `ϖ ≥ 3`.** -/
theorem varpi_t2 (cer : CY.CERange) (q : ℕ) (hq7 : q < 70000) (hq100 : 100 ≤ q)
    (hv3 : 3 ≤ varpiE q) : varpiE q = Kc - Real.log q := by
  have hvar := varpiE_eq q
  rw [varpi0_small q (by omega) hq7.le] at hvar
  have ht3 := t3_le_one cer q hq100
  have hm : max (Kc - Real.log q) (100000 / (cRho2 * q) ^ (1 / (1 - omegaE))) =
      Kc - Real.log q := by
    rcases le_total (Kc - Real.log q) (100000 / (cRho2 * q) ^ (1 / (1 - omegaE))) with h | h
    · exfalso
      rw [max_eq_right h] at hvar
      have : varpiE q ≤ 1 := by rw [hvar]; exact max_le (by norm_num) ht3
      linarith
    · exact max_eq_left h
  rw [hm] at hvar
  rw [hvar]
  apply max_eq_right
  by_contra hc
  push Not at hc
  rw [hvar, max_eq_left hc.le] at hv3
  linarith

/-- **Regime A, PROVED** (`q < 70000`, `ϖ(q) ≥ 3`). -/
theorem regA (cer : CY.CERange) : RegA := by
  intro q hq hq7 hv3
  have hq5 : q < 510510 := by omega
  have hv1 : 1 ≤ varpiE q := by linarith
  refine coverA_of cer q hq hq5 hv1 ?_
  have hω0 := omega_lo cer
  have hω := LQ.omegaE_le cer
  have hK1 := Kc_lo
  have hK2 := Kc_hi
  have hL5 := LQ.logQ0_ge
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hvt2 : Kc - Real.log q ≤ varpiE q := by
    rw [varpiE_eq]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = varpiE q := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (EE.edgeN q : ℝ) := ⟨_, rfl⟩
  have hNe : N = (⌊v⌋₊ : ℝ) + 1 := by rw [hN, hv]; unfold EE.edgeN; push_cast; rfl
  have hv3' : 3 ≤ v := by rw [hv]; exact hv3
  have hvN : v < N := by rw [hNe]; exact Nat.lt_floor_add_one v
  have hNv : N ≤ v + 1 := by rw [hNe]; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ v)]
  have hv0 : 0 < v := by linarith
  have hN0 : 0 < N := by linarith
  have ht2 : Kc - Real.log q ≤ v := by rw [hv]; exact hvt2
  rw [← hv, ← hN]
  have hNq : 0 < N * q := mul_pos hN0 hq0
  -- the right side, from any `M ≥ Nq` and any `c ≤ log(10⁵/M)`
  have hRHS : ∀ M c : ℝ, 0 < M → N * q ≤ M → c ≤ Real.log (100000 / M) → 0 ≤ c →
      0.37268 * c ≤ (1 - omegaE) * Real.log (100000 / (N * q)) := by
    intro M c hM hle hc hc0
    have hl : Real.log (100000 / M) ≤ Real.log (100000 / (N * q)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hNq hle)
    exact mul_le_mul (by linarith) (le_trans hc hl) hc0 (by linarith)
  rcases Nat.lt_or_ge q 100 with hq100 | hq100
  · -- `q < 100`
    have hl100 : Real.log q ≤ 4.6052 := by
      have h := exp_lo 4.6052 (11513 / 20000) 14 8 100 (by norm_num) (by push_cast; norm_num)
        (by decide +kernel)
      have e : ((100 : ℚ) : ℝ) = 100 := by norm_num
      rw [e] at h
      exact le_trans (Real.log_le_log hq0 (by exact_mod_cast hq100.le))
        (log_le_of (by norm_num) h)
    have hvar := varpiE_eq q
    rw [← hv, varpi0_small q hq hq7.le] at hvar
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · -- `q = 1`
      have hq1 : q = 1 := by omega
      have hlq1 : Real.log q = 0 := by rw [hq1]; simp
      have hqr : (q : ℝ) = 1 := by rw [hq1]; simp
      have hvK : Kc ≤ v := by rw [hlq1] at ht2; linarith
      have hvbig : v ≤ 76924 := by
        rw [hvar]
        refine max_le (by norm_num) (max_le ?_ ?_)
        · rw [hlq1]
          linarith
        · exact le_trans (t3_one cer q hq1) (by norm_num)
      rcases le_or_gt v 1000 with hv1000 | hv1000
      · have hl := lhs_le v N 12.1 2.2957 (by linarith) (by norm_num) (by norm_num) (by norm_num)
          hvN hNv
        have h46 : (4.6 : ℝ) ≤ Real.log (100000 / 1001) := by
          have h := exp_hi 4.6 (23 / 40) 12 8 (999 / 10) (by norm_num) (by norm_num)
            (by norm_num) (by push_cast; norm_num) (by decide +kernel)
          exact log_ge_of (by norm_num) (le_trans h (by norm_num))
        have hr := hRHS 1001 4.6 (by norm_num) (by rw [hqr]; linarith) h46 (by norm_num)
        have hn : (1 : ℝ) / 12.1 + 0.28618 / (12.1 * 2.2957) ≤ 0.37268 * 4.6 := by norm_num
        linarith
      · have hl := lhs_le v N 1000 10 (by linarith) (by norm_num) (by norm_num) (by norm_num)
          hvN hNv
        have h025 : (0.25 : ℝ) ≤ Real.log (100000 / 76925) := by
          have h := exp_hi 0.25 (1 / 32) 12 8 (12999 / 10000) (by norm_num) (by norm_num)
            (by norm_num) (by push_cast; norm_num) (by decide +kernel)
          exact log_ge_of (by norm_num) (le_trans h (by norm_num))
        have hr := hRHS 76925 0.25 (by norm_num) (by rw [hqr]; linarith) h025 (by norm_num)
        have hn : (1 : ℝ) / 1000 + 0.28618 / (1000 * 10) ≤ 0.37268 * 0.25 := by norm_num
        linarith
    · -- `2 ≤ q < 100`
      have hq99 : (q : ℝ) ≤ 99 := by exact_mod_cast (by omega : q ≤ 99)
      have ht3 := t3q_le cer q hq2
      have hvq : v * q ≤ 35356 := by
        rw [hvar, max_mul_of_nonneg _ _ hq0.le, max_mul_of_nonneg _ _ hq0.le]
        refine max_le (by norm_num) (max_le ?_ ht3)
        have := mul_le_mul (by linarith : Kc - Real.log q ≤ 12.106) hq99 hq0.le (by norm_num)
        linarith
      have hNq' : N * q ≤ 35455 := by
        have := mul_le_mul_of_nonneg_right hNv hq0.le
        nlinarith
      have h1 : (1 : ℝ) ≤ Real.log (100000 / 35455) := by
        refine log_ge_of (by norm_num) ?_
        have := Real.exp_one_lt_d9
        linarith
      have hr := hRHS 35455 1 (by norm_num) hNq' h1 (by norm_num)
      have hl := lhs_le v N 7.4948 1.9566 (by linarith) (by norm_num) (by norm_num) (by norm_num)
        hvN hNv
      have hn : (1 : ℝ) / 7.4948 + 0.28618 / (7.4948 * 1.9566) ≤ 0.37268 * 1 := by norm_num
      linarith
  · -- `100 ≤ q`: `ϖ = K − log q`
    have hveq : v = Kc - Real.log q := by rw [hv]; exact varpi_t2 cer q hq7 hq100 hv3
    rcases lt_or_ge v 4 with hv4 | hv4
    · -- `N = 4`
      have hfl : ⌊v⌋₊ = 3 := by
        rw [Nat.floor_eq_iff (by linarith)]
        constructor <;> push_cast <;> linarith
      have hN4 : N = 4 := by rw [hNe, hfl]; norm_num
      rw [hN4]
      have hl := lhs_le4 v hv3'
      have hlog4 : Real.log 4 ≤ 1.3863 := by
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast
          ring
        have := Real.log_two_lt_d9
        linarith
      have hR : Real.log (100000 / (4 * q)) = Real.log 100000 - Real.log 4 - Real.log q := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) hq0.ne']
        ring
      have hRv : (1.020625 : ℝ) ≤ Real.log (100000 / (4 * q)) := by
        rw [hR]
        linarith
      have hRR : (0.37268 : ℝ) * 1.020625 ≤ (1 - omegaE) * Real.log (100000 / (4 * q)) :=
        mul_le_mul (by linarith) hRv (by norm_num) (by linarith)
      have hn : (0.28769 : ℝ) + 0.28618 / (3 * 1.4422) ≤ 0.37268 * 1.020625 := by norm_num
      linarith
    · -- `ϖ ≥ 4`
      have hl := lhs_le v N 4 1.5874 hv4 (by norm_num) (by norm_num) (by norm_num) hvN hNv
      have hlog5 : Real.log 5 ≤ 1.60944 := by
        have h := exp_lo 1.60944 (10059 / 50000) 14 8 5 (by norm_num) (by push_cast; norm_num)
          (by decide +kernel)
        have e : ((5 : ℚ) : ℝ) = 5 := by norm_num
        rw [e] at h
        exact log_le_of (by norm_num) h
      have hlv1 : Real.log (v + 1) ≤ Real.log 5 + (v + 1) / 5 - 1 := by
        have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (v + 1) / 5)
        rw [Real.log_div (by positivity) (by norm_num)] at h
        linarith
      have hR : Real.log (100000 / ((v + 1) * q)) =
          Real.log 100000 - Real.log (v + 1) - Real.log q := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by positivity) hq0.ne']
        ring
      have hRv : (1.797485 : ℝ) ≤ Real.log (100000 / ((v + 1) * q)) := by
        rw [hR]
        linarith
      have hr := hRHS ((v + 1) * q) 1.797485 (by positivity)
        (mul_le_mul_of_nonneg_right hNv hq0.le) hRv (by norm_num)
      have hn : (1 : ℝ) / 4 + 0.28618 / (4 * 1.5874) ≤ 0.37268 * 1.797485 := by norm_num
      linarith

end Principia.Common.TernaryGoldbach.ER
