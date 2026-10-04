/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeCover
import Principia.Common.TernaryGoldbach.LargeQAnalytic

set_option autoImplicit false

/-!
# The numerics of `EE.EspagnEdgeRes`: certified exponentials and the constants of `ϖ(q)`

Everything numeric that the proof of `EE.EspagnEdgeRes` needs, from one mechanism.

* **Certified exponentials** (`exp_lo`, `exp_hi`). `tayQ y n = Σ_{i<n} yⁱ/i!` is computed in `ℚ`
  by recursion, so an inequality `B ≤ tayQ(y, n)^m` or `(tayQ(y, n) + rem(y, n))^m ≤ B` is a
  closed rational statement that `decide +kernel` settles exactly; `Real.sum_le_exp_of_nonneg`
  and `Real.exp_bound'` turn it into `B ≤ e^{my}` or `e^{my} ≤ B`. Every logarithm below is
  bounded the same way (`log y ≥ L ⟸ e^L ≤ y`). No floating point enters a proof.
* **The constants of `eq:armor`**: `g = e^{−γ} ∈ [0.5614593, 0.5615454]` (`gE_lo`, `gE_hi`, from
  `1.7808 ≤ e^γ ≤ 1.7810727`), `τ = (2/5)g` (`tauE_eq`), `c(1.36) = e^{−(3371/20500)g}`
  (`cSig_eq`), so that `c(1.36)·q^τ = A(log q)` with `A(ℓ) = exp(g((2/5)ℓ − 3371/20500))`
  (`cq_eq`): the whole first two terms of `ϖ(q)` are one exponential in `ℓ = log q`.
  `K = c(1.36)·10^{5τ} ∈ [12.1, 12.106]` (`Kc_lo`, `Kc_hi`), `ω ∈ [0.6273, 0.62732]`
  (`omega_lo`, `LQ.omegaE_le`), `c_{ρ,2} ≥ e^{0.1109}` (`cRho2_ge`).
* **`A(ℓ)` is monotone, and so are `D(ℓ) = A(ℓ) − ℓ` and `ℓ/D(ℓ)`** where `τA ≥ 1`, `τℓ ≥ 1`
  (`D_mono`, `ratio_mono`): the cell argument of the Cover B regime evaluates `A` only at the
  ends of each cell.
-/

namespace Principia.Common.TernaryGoldbach.ER

open Principia.Common.TernaryGoldbach.HC (omegaE cDeltaE kappaE betaE lambdaE tauE cSig cRho2
  varpi0 varpiE errE sumLogP)

/-! ## (1) Certified exponentials -/

/-- `Σ_{i<n} yⁱ/i!` in `ℚ`, by recursion (closed, kernel-evaluable). -/
def tayQ (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => tayQ y n + y ^ n / (n.factorial : ℚ)

/-- The remainder of `Real.exp_bound'`: `yⁿ(n + 1)/(n!·n)`. -/
def remQ (y : ℚ) (n : ℕ) : ℚ := y ^ n * ((n : ℚ) + 1) / ((n.factorial : ℚ) * n)

/-- `tayQ` is the Taylor sum. -/
theorem tayQ_cast (y : ℚ) (n : ℕ) :
    ((tayQ y n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (y : ℝ) ^ i / (i.factorial : ℝ) := by
  induction n with
  | zero => simp [tayQ]
  | succ n ih =>
    rw [tayQ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- **Certified lower bound**: `B ≤ tayQ(y, n)^m`, `my ≤ x` ⟹ `B ≤ eˣ`. -/
theorem exp_lo (x : ℝ) (y : ℚ) (n m : ℕ) (B : ℚ) (hy : 0 ≤ y) (hx : (m : ℝ) * (y : ℝ) ≤ x)
    (h : B ≤ tayQ y n ^ m) : (B : ℝ) ≤ Real.exp x := by
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hs := Real.sum_le_exp_of_nonneg hy' n
  rw [← tayQ_cast] at hs
  have h0 : (0 : ℝ) ≤ (tayQ y n : ℝ) := by
    rw [tayQ_cast]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hB : (B : ℝ) ≤ (tayQ y n : ℝ) ^ m := by exact_mod_cast h
  calc (B : ℝ) ≤ (tayQ y n : ℝ) ^ m := hB
    _ ≤ Real.exp y ^ m := pow_le_pow_left₀ h0 hs m
    _ = Real.exp (m * y) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp x := Real.exp_le_exp.mpr hx

/-- **Certified upper bound**: `(tayQ(y, n) + rem(y, n))^m ≤ B`, `0 ≤ y ≤ 1`, `x ≤ my` ⟹
`eˣ ≤ B`. -/
theorem exp_hi (x : ℝ) (y : ℚ) (n m : ℕ) (B : ℚ) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hn : 0 < n)
    (hx : x ≤ (m : ℝ) * (y : ℝ)) (h : (tayQ y n + remQ y n) ^ m ≤ B) :
    Real.exp x ≤ (B : ℝ) := by
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1' : (y : ℝ) ≤ 1 := by exact_mod_cast hy1
  have hb := Real.exp_bound' hy' hy1' hn
  have hr : ((remQ y n : ℚ) : ℝ) = (y : ℝ) ^ n * ((n : ℝ) + 1) / ((n.factorial : ℝ) * n) := by
    unfold remQ
    push_cast
    ring
  rw [← tayQ_cast, ← hr] at hb
  have hB : (((tayQ y n + remQ y n : ℚ) : ℝ)) ^ m ≤ (B : ℝ) := by exact_mod_cast h
  push_cast at hB
  calc Real.exp x ≤ Real.exp (m * y) := Real.exp_le_exp.mpr hx
    _ = Real.exp y ^ m := by rw [← Real.exp_nat_mul]
    _ ≤ ((tayQ y n : ℝ) + (remQ y n : ℝ)) ^ m := pow_le_pow_left₀ (Real.exp_pos _).le hb m
    _ ≤ B := hB

/-- `log y ≥ L` from a certified `e^L ≤ y`. -/
theorem log_ge_of {y L : ℝ} (hy : 0 < y) (h : Real.exp L ≤ y) : L ≤ Real.log y :=
  (Real.le_log_iff_exp_le hy).mpr h

/-- `log y ≤ U` from a certified `y ≤ e^U`. -/
theorem log_le_of {y U : ℝ} (hy : 0 < y) (h : y ≤ Real.exp U) : Real.log y ≤ U :=
  (Real.log_le_iff_le_exp hy).mpr h

/-! ## (2) `g = e^{−γ}`, `τ`, `c(1.36)` and `A(ℓ)` -/

/-- `g = e^{−γ}`. -/
noncomputable def gE : ℝ := Real.exp (-Real.eulerMascheroniConstant)

/-- `g ≥ 0.5614593` (`e^γ ≤ 1.7810727`). -/
theorem gE_lo : (0.5614593 : ℝ) ≤ gE := by
  have h := Principia.Erdos1054.Proofs.SmallRatio.exp_gamma_le
  have hpos : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  unfold gE
  rw [Real.exp_neg, ← one_div, le_div_iff₀ hpos]
  nlinarith

/-- `g ≤ 0.5615454` (`e^γ ≥ 1.7808`). -/
theorem gE_hi : gE ≤ 0.5615454 := by
  have h := HX.expG_ge
  have hpos : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  unfold gE
  rw [Real.exp_neg, ← one_div, div_le_iff₀ hpos]
  nlinarith

/-- `g > 0`. -/
theorem gE_pos : 0 < gE := Real.exp_pos _

/-- `τ = (2/5)g`. -/
theorem tauE_eq : tauE = 2 / 5 * gE := by
  unfold tauE gE
  norm_num

/-- `0.22458372 ≤ τ ≤ 0.22461816`. -/
theorem tau_bounds : (0.22458372 : ℝ) ≤ tauE ∧ tauE ≤ 0.22461816 := by
  rw [tauE_eq]
  constructor <;> linarith [gE_lo, gE_hi]

/-- `c(1.36) = e^{−(3371/20500)g}`. -/
theorem cSig_eq : cSig 1.36 = Real.exp (gE * -(3371 / 20500)) := by
  unfold cSig gE
  norm_num

/-- `A(ℓ) = exp(g((2/5)ℓ − 3371/20500))`, so that `c(1.36)q^τ = A(log q)`. -/
noncomputable def Af (l : ℝ) : ℝ := Real.exp (gE * (2 / 5 * l - 3371 / 20500))

/-- **`c(1.36)·q^τ = A(log q)`**. -/
theorem cq_eq (q : ℝ) (hq : 0 < q) : cSig 1.36 * q ^ tauE = Af (Real.log q) := by
  rw [cSig_eq, Real.rpow_def_of_pos hq, ← Real.exp_add, tauE_eq]
  unfold Af
  congr 1
  ring

/-- `A(ℓ) > 0`. -/
theorem Af_pos (l : ℝ) : 0 < Af l := Real.exp_pos _

/-- **Lower bound of `A` from a left end**: `ℓ ≥ L ≥ 0.4111` ⟹
`A(ℓ) ≥ exp(0.5614593((2/5)L − 3371/20500))`. -/
theorem Af_ge (l L : ℝ) (hL : L ≤ l) (h0 : 3371 / 20500 ≤ 2 / 5 * L) :
    Real.exp (0.5614593 * (2 / 5 * L - 3371 / 20500)) ≤ Af l := by
  unfold Af
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ 2 / 5 * L - 3371 / 20500 := by linarith
  have h2 : 2 / 5 * L - 3371 / 20500 ≤ 2 / 5 * l - 3371 / 20500 := by linarith
  exact mul_le_mul gE_lo h2 h1 gE_pos.le

/-- **Upper bound of `A` from a right end**: `ℓ ≤ L`, `ℓ ≥ 0.4111` ⟹
`A(ℓ) ≤ exp(0.5615454((2/5)L − 3371/20500))`. -/
theorem Af_le (l L : ℝ) (hL : l ≤ L) (h0 : 3371 / 20500 ≤ 2 / 5 * l) :
    Af l ≤ Real.exp (0.5615454 * (2 / 5 * L - 3371 / 20500)) := by
  unfold Af
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ 2 / 5 * l - 3371 / 20500 := by linarith
  have h2 : 2 / 5 * l - 3371 / 20500 ≤ 2 / 5 * L - 3371 / 20500 := by linarith
  exact mul_le_mul gE_hi h2 h1 (by norm_num)

/-- `A(ℓ') = A(ℓ)e^{τ(ℓ' − ℓ)}`. -/
theorem Af_shift (l l' : ℝ) : Af l' = Af l * Real.exp (tauE * (l' - l)) := by
  unfold Af
  rw [← Real.exp_add, tauE_eq]
  congr 1
  ring

/-- **`D(ℓ) = A(ℓ) − ℓ` is non-decreasing** where `τA(ℓ) ≥ 1`. -/
theorem D_mono (l l' : ℝ) (hll : l ≤ l') (hτA : 1 ≤ tauE * Af l) :
    Af l - l ≤ Af l' - l' := by
  have h := Real.add_one_le_exp (tauE * (l' - l))
  have hA := Af_pos l
  have e := Af_shift l l'
  have h2 : Af l * (tauE * (l' - l) + 1) ≤ Af l' := by
    rw [e]
    exact mul_le_mul_of_nonneg_left h hA.le
  nlinarith

/-- **`ℓ/D(ℓ)` is non-increasing** where `τℓ ≥ 1` and `D > 0`: `ℓ'D(ℓ) ≤ ℓD(ℓ')`. -/
theorem ratio_mono (l l' : ℝ) (hl : 0 < l) (hll : l ≤ l') (hτl : 1 ≤ tauE * l) :
    l' * (Af l - l) ≤ l * (Af l' - l') := by
  have h := Real.add_one_le_exp (tauE * (l' - l))
  have hA := Af_pos l
  have e := Af_shift l l'
  have h2 : Af l * (tauE * (l' - l) + 1) ≤ Af l' := by
    rw [e]
    exact mul_le_mul_of_nonneg_left h hA.le
  have h3 : l' ≤ l * (tauE * (l' - l) + 1) := by nlinarith
  have h4 : l' * Af l ≤ l * Af l' := by
    calc l' * Af l ≤ l * (tauE * (l' - l) + 1) * Af l := mul_le_mul_of_nonneg_right h3 hA.le
      _ = l * (Af l * (tauE * (l' - l) + 1)) := by ring
      _ ≤ l * Af l' := mul_le_mul_of_nonneg_left h2 hl.le
  nlinarith

/-! ## (3) `log 10⁵`, `K`, `ω`, `c_{ρ,2}` -/

/-- `log 10⁵ ≤ 11.5129255` (`log 10 ≤ 2.302585095`). -/
theorem logQ0_le : Real.log 100000 ≤ 11.5129255 := by
  rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]
  have := Principia.Erdos1054.Proofs.SmallRatio.log_ten_le
  push_cast
  linarith

/-- `K = c(1.36)·10^{5τ}`, the constant of the second term of `ϖ(q)`. -/
noncomputable def Kc : ℝ := cSig 1.36 * (100000 : ℝ) ^ tauE

/-- `K = A(log 10⁵)`. -/
theorem Kc_eq : Kc = Af (Real.log 100000) := cq_eq 100000 (by norm_num)

/-- **`K ≥ 12.1`**. -/
theorem Kc_lo : (12.1 : ℝ) ≤ Kc := by
  rw [Kc_eq]
  have hL := LQ.logQ0_ge
  refine le_trans ?_ (Af_ge _ 11.512925 hL (by norm_num))
  have h := exp_lo (0.5614593 * (2 / 5 * 11.512925 - 3371 / 20500)) (311661213 / 1000000000) 14 8
    (121 / 10) (by norm_num) (by push_cast; norm_num) (by decide +kernel)
  have e : ((121 / 10 : ℚ) : ℝ) = 12.1 := by norm_num
  rw [e] at h
  exact h

/-- **`K ≤ 12.106`**. -/
theorem Kc_hi : Kc ≤ 12.106 := by
  rw [Kc_eq]
  have hL := logQ0_le
  have hL0 := LQ.logQ0_ge
  refine le_trans (Af_le _ 11.5129255 hL (by linarith)) ?_
  have h := exp_hi (0.5615454 * (2 / 5 * 11.5129255 - 3371 / 20500)) (311709021 / 1000000000) 12 8
    (6053 / 500) (by norm_num) (by norm_num) (by norm_num) (by push_cast; norm_num)
    (by decide +kernel)
  have e : ((6053 / 500 : ℚ) : ℝ) = 12.106 := by norm_num
  rw [e] at h
  exact h

/-- **`ω ≥ 0.6273`** (`c_E ≤ 1.3325823`, `log 10⁵ ≤ 11.5129255`). -/
theorem omega_lo (cer : CY.CERange) : (0.6273 : ℝ) ≤ omegaE := by
  rw [HX.omegaE_eq]
  have hL := logQ0_le
  have hL0 := LQ.logQ0_ge
  have hc := cer.2
  rw [le_div_iff₀ (by linarith [cer.1])]
  linarith

/-- `1/(1 − ω) ≥ 2.5`. -/
theorem expo_ge (cer : CY.CERange) : (2.5 : ℝ) ≤ 1 / (1 - omegaE) := by
  have h1 := omega_lo cer
  have h2 := LQ.omegaE_le cer
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **`c_{ρ,2} ≥ e^{0.1109}`** (`c_E ≥ 1.312`, `ω > 0`). -/
theorem cRho2_ge (cer : CY.CERange) : Real.exp 0.1109 ≤ cRho2 := by
  unfold cRho2 cDeltaE
  apply Real.exp_le_exp.mpr
  have hw := HX.omegaE_pos cer
  have hc := cer.1
  have : 0 ≤ omegaE * (CY.cE - 1.312) := mul_nonneg hw.le (by linarith)
  linarith

/-- `c_{ρ,2} ≥ 1`. -/
theorem cRho2_ge_one (cer : CY.CERange) : 1 ≤ cRho2 :=
  le_trans (Real.one_le_exp (by norm_num)) (cRho2_ge cer)

end Principia.Common.TernaryGoldbach.ER
