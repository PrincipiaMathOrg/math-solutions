/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.StarCert
import Principia.Common.TernaryGoldbach.NefumoClose

set_option autoImplicit false

/-!
# `ZvsL η*` PROVED, so `prop:nefumo` is PROVED on Helfgott's weights

`NefumoClose` left exactly one link of `RW.NefumoW η₊ η* η∘` open, `NF.ZvsL η*`, and reduced it
(`NC.zvsL_star_of_mass`) to one inequality: `0.7903·x ≤ ∑_n Λ(n)²η*(n/x)²` for `x ≥ 4.9·10²⁶`.
This file proves it (`mass_ge`), with the certified lower bound `55·0.0153 = 0.8415`:

* **the step minorant** (`minorant`): on each of 146 cells `(a_c, a_{c+1}]` of `t`, `a_c = g_c/49`
  (32 per octave on `[0.0025, 0.0591]`), `m_c ≤ η*(t)²`. With `s = 49t ∈ (g_c, g_{c+1}]` the closed
  form `SC.etaStar_closed` gives `η*(t) = 4∫_s^{2s} f ≥ 4∫_{g_{c+1}}^{2g_c} f`, and `SC.cell_ge`
  bounds that below piecewise from the certified exponential table (`exp_tab = SC.exp_chain` on
  `SK.base_ok`, `SK.chain_ok`); `SK.cells_ok` checks `m_c ≤ (4S_c)²`;
* **the mass** (`NC.Z_ge`): only primes in `(a_0x, a_{146}x]`, `Λ(p) ≥ log(a_0x) ≥ 55`;
* **`θ` at the 147 cut points** (`theta_cut`: `NC.theta_ge_lin`, `NC.theta_le_lin`) and summation
  by parts (`SC.abel_ge`), certified `≥ 0.0153·x` (`SK.abel_ok`).

Captured: the step mass is `0.018838` of `|η*|₂² = 0.021706` (`86.8%`); after the `θ` constants
the Abel sum is `0.015374`; against `log(a_0x)` at `x = 4.9·10²⁶` (`55.46`) the bound is `0.853`,
against the proved `55`, `0.8456`, target `0.7903`. The lever (`|η*|₂² ≤ 1.2774/49`, target
`0.505`) was NOT needed.

**Results.** `zvsL_star : NF.ZvsL η*`; `jokoW_proved : NF.JokoW η₊ η*`; and
**`nefumoW_proved : RW.NefumoW η₊ η* η∘`, no hypotheses**.
-/

namespace Principia.Common.TernaryGoldbach.SM

open ArithmeticFunction Finset MeasureTheory
open scoped ArithmeticFunction

/-- **The certified exponential table**: `el_j ≤ e^{−g_j²/2} ≤ eh_j` at every `j ≤ 208`. -/
theorem exp_tab : ∀ j ≤ 208, (SK.elQ j : ℝ) ≤ Real.exp (-(SK.gQ j : ℝ) ^ 2 / 2) ∧
    Real.exp (-(SK.gQ j : ℝ) ^ 2 / 2) ≤ (SK.ehQ j : ℝ) :=
  SC.exp_chain SK.gQ SK.elQ SK.ehQ 208 SK.base_ok SK.chain_ok

/-- The grid is positive and increasing on `[0, 208]`. -/
theorem grid_ok : ∀ j < 208, 0 < SK.gQ j ∧ SK.gQ j < SK.gQ (j + 1) := fun j hj =>
  ⟨(SK.chain_ok j hj).1, (SK.chain_ok j hj).2.1⟩

/-- `a_c = g_c/49` over `ℝ`. -/
theorem aQ_cast (i : ℕ) : ((SK.aQ i : ℚ) : ℝ) = (SK.gQ i : ℝ) / 49 := by
  unfold SK.aQ
  push_cast
  ring

/-- **THE STEP MINORANT OF `η*²`**: for `c < 146` and `a_c < t ≤ a_{c+1}`, `m_c ≤ η*(t)²`. -/
theorem minorant (c : ℕ) (hc : c < 146) (t : ℝ) (h1 : (SK.aQ c : ℝ) < t)
    (h2 : t ≤ (SK.aQ (c + 1) : ℝ)) : (SK.mQ c : ℝ) ≤ HW.etaStar t ^ 2 := by
  rw [aQ_cast c] at h1
  rw [aQ_cast (c + 1)] at h2
  have hg0 : (0 : ℝ) < SK.gQ c := by exact_mod_cast (grid_ok c (by omega)).1
  have ht : 0 < t := by
    have : (0 : ℝ) < (SK.gQ c : ℝ) / 49 := by positivity
    linarith
  have hs1 : (SK.gQ c : ℝ) < 49 * t := by linarith
  have hs2 : 49 * t ≤ (SK.gQ (c + 1) : ℝ) := by linarith
  have hcell := SC.cell_ge SK.gQ SK.elQ SK.ehQ 32 208 c (by norm_num) (by omega) grid_ok SK.gQ_dbl
    exp_tab (49 * t) hs1 hs2
  obtain ⟨hS0, hm⟩ := SK.cells_ok c hc
  have hS0' : (0 : ℝ) ≤ (SC.cellS SK.gQ SK.elQ SK.ehQ 32 c : ℝ) := by exact_mod_cast hS0
  have hm' : (SK.mQ c : ℝ) ≤ (4 * (SC.cellS SK.gQ SK.elQ SK.ehQ 32 c : ℝ)) ^ 2 := by
    exact_mod_cast hm
  rw [SC.etaStar_closed ht]
  have h4 : 4 * (SC.cellS SK.gQ SK.elQ SK.ehQ 32 c : ℝ) ≤
      4 * ∫ w in (49 * t)..(2 * (49 * t)), SC.fS w := by linarith
  exact hm'.trans (pow_le_pow_left₀ (by linarith) h4 2)

/-- `a_i ≥ a_0 = 1/400` for every `i`. -/
theorem aQ_ge (i : ℕ) : (1 / 400 : ℝ) ≤ (SK.aQ i : ℝ) := by
  have h := (monotone_nat_of_le_succ SK.aQ_le) (Nat.zero_le i)
  rw [SK.aQ_zero] at h
  have h' : (((1 / 400 : ℚ)) : ℝ) ≤ (SK.aQ i : ℝ) := by exact_mod_cast h
  norm_num at h'
  linarith

/-- **`θ` at every cut point** `y = a_i x ≥ 1.225·10²⁴`: `0.92079y ≤ θ(y) ≤ 1.11y`. -/
theorem theta_cut (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (i : ℕ) :
    ((92079 / 100000 : ℚ) : ℝ) * ((SK.aQ i : ℝ) * x) ≤ Chebyshev.theta ((SK.aQ i : ℝ) * x) ∧
      Chebyshev.theta ((SK.aQ i : ℝ) * x) ≤ ((111 / 100 : ℚ) : ℝ) * ((SK.aQ i : ℝ) * x) := by
  have ha := aQ_ge i
  have hy : (10 : ℝ) ^ 24 ≤ (SK.aQ i : ℝ) * x := by
    have := mul_le_mul ha hx (by norm_num) (by linarith)
    linarith
  have hlo := NC.theta_ge_lin ((SK.aQ i : ℝ) * x) hy
  have hhi := NC.theta_le_lin ((SK.aQ i : ℝ) * x) (by linarith)
  constructor
  · norm_num
    linarith
  · norm_num
    linarith

/-- `log(a_0x) ≥ 55` for `x ≥ 4.9·10²⁶` (`e ≤ 2.7182818286`). -/
theorem log_a0x (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 55 ≤ Real.log ((SK.aQ 0 : ℝ) * x) := by
  have ha0 : ((SK.aQ 0 : ℚ) : ℝ) = 1 / 400 := by
    rw [SK.aQ_zero]
    norm_num
  rw [ha0, Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 55 = Real.exp 1 ^ 55 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 55 ≤ 2.7182818286 ^ 55 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 55
  have h4 : (2.7182818286 : ℝ) ^ 55 ≤ 1 / 400 * (49 * 10 ^ 25) := by norm_num
  linarith

/-- **THE MASS INEQUALITY**: `0.7903·x ≤ ∑_n Λ(n)²η*(n/x)²` for every `x ≥ 4.9·10²⁶`
(certified `0.8415·x`). -/
theorem mass_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0.7903 * x ≤ ∑' n : ℕ, (Λ n) ^ 2 * HW.etaStar ((n : ℝ) / x) ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have ha0 : (1 / 400 : ℝ) ≤ (SK.aQ 0 : ℝ) := aQ_ge 0
  have hZ := NC.Z_ge HW.etaStar x hx0 146 (fun i => (SK.aQ i : ℝ)) (fun i => (SK.mQ i : ℝ))
    (by linarith) (fun i => by exact_mod_cast SK.aQ_le i)
    (fun i _ => by exact_mod_cast SK.mQ_nonneg i)
    (fun i hi t ht1 ht2 => minorant i hi t ht1 ht2) (NC.summW_star x hx)
    (by nlinarith)
  have hA := SC.abel_ge Chebyshev.theta x hx0 (92079 / 100000) (111 / 100) SK.aQ SK.mQ 146
    (fun i _ => theta_cut x hx i)
  have hab : ((153 / 10000 : ℚ) : ℝ) ≤
      ((SC.abelQ (92079 / 100000) (111 / 100) SK.aQ SK.mQ 146 : ℚ) : ℝ) := by
    exact_mod_cast SK.abel_ok
  have hlog := log_a0x x hx
  set S := ∑ i ∈ Finset.range 146, (SK.mQ i : ℝ) *
    (Chebyshev.theta ((SK.aQ (i + 1) : ℝ) * x) - Chebyshev.theta ((SK.aQ i : ℝ) * x)) with hSdef
  have hS : x * ((153 / 10000 : ℚ) : ℝ) ≤ S :=
    le_trans (mul_le_mul_of_nonneg_left hab hx0.le) hA
  norm_num at hS
  have hS0 : 0 ≤ S := by nlinarith
  have k1 : 55 * S ≤ Real.log ((SK.aQ 0 : ℝ) * x) * S := mul_le_mul_of_nonneg_right hlog hS0
  have hZ' : Real.log ((SK.aQ 0 : ℝ) * x) * S ≤
      ∑' n : ℕ, (Λ n) ^ 2 * HW.etaStar ((n : ℝ) / x) ^ 2 := hZ
  nlinarith

/-- **[ZvsL] PROVED at Helfgott's `η*`** (`NC.zvsL_star_of_mass` + `mass_ge`). -/
theorem zvsL_star : NF.ZvsL HW.etaStar := NC.zvsL_star_of_mass mass_ge

/-- **[Joko] PROVED at Helfgott's weights**. -/
theorem jokoW_proved : NF.JokoW HW.etaPlus HW.etaStar := NC.jokoW_helf zvsL_star

/-- **`prop:nefumo` PROVED on Helfgott's weights**: `RW.NefumoW η₊ η* η∘`, no hypotheses. -/
theorem nefumoW_proved : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc :=
  NC.nefumoW_helf_closed zvsL_star

end Principia.Common.TernaryGoldbach.SM
