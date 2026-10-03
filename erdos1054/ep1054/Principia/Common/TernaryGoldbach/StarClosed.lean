/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfWeights
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-!
# `η*` in closed form, and the generic machinery of a certified step minorant of `η*²`

**The closed form** (`etaStar_closed`): for `t > 0`, `s = 49t`,
`η*(t) = 4∫_s^{2s} f(w) dw`, `f(w) = (e^{−w²/2} − e^{−2w²})/w` (`fS`). From `HW.mconv_eta2`,
`η*(t) = ∫_s^{4s} η₂(s/y)·y e^{−y²/2} dy`; on `[s, 2s]` the tent is `4(log y − log s)`, on
`[2s, 4s]` it is `4(2 log 2 + log s − log y)`; one integration by parts on each half against
`v = −e^{−y²/2}` (`ibp_lo`, `ibp_hi`) leaves the boundary terms `∓4 log 2·e^{−2s²}`, which cancel,
and `4∫_s^{2s} e^{−y²/2}/y − 4∫_{2s}^{4s} e^{−y²/2}/y`; `y = 2w` turns the second into
`4∫_s^{2s} e^{−2w²}/w` (`int_sub`). The integrand `f` is `≥ 0` and explicit.

**The generic minorant machinery** (all numbers are `ℚ` data, checked elsewhere by the kernel):

* `exp_chain`: bounds `el_j ≤ e^{−g_j²/2} ≤ eh_j` along an increasing grid `g`, from
  `e^{−g_{j+1}²/2} = e^{−g_j²/2}·e^{−d}`, `d = (g_{j+1}² − g_j²)/2`, and
  `P(d) ≤ e^d ≤ P(d) + d⁵/100` (`P` the quartic Taylor polynomial; `Real.sum_le_exp_of_nonneg`,
  `Real.exp_bound'`), one decidable condition `StepOK` per step.
* `piece_ge`: on `[u, v]`, `f ≥ max(0, lo − hi)/v` when `lo ≤ e^{−v²/2}`, `e^{−(2u)²/2} ≤ hi`.
* `cell_ge`: on a doubling grid (`g_{j+K} = 2g_j`) and `s ∈ (g_c, g_{c+1}]`,
  `[g_{c+1}, g_{c+K}] ⊆ [s, 2s]`, so `∫_s^{2s} f ≥ ∑_{j=c+1}^{c+K−1} q_j(g_{j+1} − g_j)`
  (`cellS`, `q_j = max(0, el_{j+1} − eh_{j+K})/g_{j+1}`).
* `abel_ge`: summation by parts with `lo·y ≤ θ(y) ≤ hi·y`: `∑ m_i(θ(a_{i+1}x) − θ(a_i x)) ≥
  x·abelQ`, where each Abel coefficient takes the worse of the two `θ` constants (`mnQ`).
-/

namespace Principia.Common.TernaryGoldbach.SC

open MeasureTheory Set Finset

/-! ## The closed form -/

/-- The integrand of the closed form: `f(w) = (e^{−w²/2} − e^{−2w²})/w`. -/
noncomputable def fS (w : ℝ) : ℝ := (Real.exp (-w ^ 2 / 2) - Real.exp (-2 * w ^ 2)) / w

/-- `f` is continuous on `(0, ∞)`. -/
theorem fS_contOn : ContinuousOn fS (Ioi 0) := by
  have hc : Continuous fun w : ℝ => Real.exp (-w ^ 2 / 2) - Real.exp (-2 * w ^ 2) := by fun_prop
  exact hc.continuousOn.div continuousOn_id fun w hw => (mem_Ioi.mp hw).ne'

/-- `f ≥ 0` on `[0, ∞)`. -/
theorem fS_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ fS w := by
  have h : Real.exp (-2 * w ^ 2) ≤ Real.exp (-w ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg w])
  exact div_nonneg (by linarith) hw

/-- `φ(y)/y = y·e^{−y²/2}`. -/
theorem phi_div {y : ℝ} (hy : y ≠ 0) : HW.phi y / y = y * Real.exp (-y ^ 2 / 2) := by
  rw [HW.phi, div_eq_iff hy]
  ring

/-- `(−e^{−y²/2})' = y·e^{−y²/2}`. -/
theorem hasDerivAt_ng (y : ℝ) :
    HasDerivAt (fun y => -Real.exp (-y ^ 2 / 2)) (y * Real.exp (-y ^ 2 / 2)) y := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-y) y := by
    have e : (fun y : ℝ => -y ^ 2 / 2) = fun x => -(x * x) / 2 := by
      funext x
      ring
    rw [e]
    exact (((hasDerivAt_id' y).mul (hasDerivAt_id' y)).neg.div_const 2).congr_deriv (by ring)
  exact h1.exp.neg.congr_deriv (by ring)

/-- `e^{−y²/2}/y` is continuous on `(0, ∞)`. -/
theorem g1_contOn : ContinuousOn (fun y : ℝ => Real.exp (-y ^ 2 / 2) / y) (Ioi 0) :=
  (by fun_prop : Continuous fun y : ℝ => Real.exp (-y ^ 2 / 2)).continuousOn.div continuousOn_id
    fun y hy => (mem_Ioi.mp hy).ne'

/-- `e^{−2y²}/y` is continuous on `(0, ∞)`. -/
theorem g2_contOn : ContinuousOn (fun y : ℝ => Real.exp (-2 * y ^ 2) / y) (Ioi 0) :=
  (by fun_prop : Continuous fun y : ℝ => Real.exp (-2 * y ^ 2)).continuousOn.div continuousOn_id
    fun y hy => (mem_Ioi.mp hy).ne'

/-- **By parts on `[s, 2s]`**: `∫ η₂(s/y)φ(y)/y = 4 log 2·(−e^{−(2s)²/2}) + 4∫ e^{−y²/2}/y`. -/
theorem ibp_lo {s : ℝ} (hs : 0 < s) :
    ∫ y in s..2 * s, HW.eta2 (s / y) * HW.phi y / y =
      4 * Real.log 2 * -Real.exp (-(2 * s) ^ 2 / 2) +
        4 * ∫ y in s..2 * s, Real.exp (-y ^ 2 / 2) / y := by
  have hsub : uIcc s (2 * s) ⊆ Ioi 0 := HW.uIcc_pos hs (by linarith)
  have hcongr : EqOn (fun y => HW.eta2 (s / y) * HW.phi y / y)
      (fun y => 4 * (Real.log y - Real.log s) * (y * Real.exp (-y ^ 2 / 2))) (uIcc s (2 * s)) := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    simp only
    rw [mul_div_assoc, HW.eta2_lo hs hy.1 hy.2, phi_div hy0.ne']
  rw [intervalIntegral.integral_congr hcongr]
  have hu : ∀ y ∈ uIcc s (2 * s), HasDerivAt (fun y => 4 * (Real.log y - Real.log s))
      (4 * y⁻¹) y := fun y hy =>
    ((Real.hasDerivAt_log (hsub hy).ne').sub_const (Real.log s)).const_mul 4
  have hv : ∀ y ∈ uIcc s (2 * s), HasDerivAt (fun y => -Real.exp (-y ^ 2 / 2))
      (y * Real.exp (-y ^ 2 / 2)) y := fun y _ => hasDerivAt_ng y
  have hu' : IntervalIntegrable (fun y => 4 * y⁻¹) volume s (2 * s) :=
    (continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => (hsub hy).ne')).intervalIntegrable
  have hv' : IntervalIntegrable (fun y => y * Real.exp (-y ^ 2 / 2)) volume s (2 * s) :=
    (by fun_prop : Continuous fun y : ℝ => y * Real.exp (-y ^ 2 / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hint : ∫ y in s..2 * s, 4 * y⁻¹ * -Real.exp (-y ^ 2 / 2) =
      -(4 * ∫ y in s..2 * s, Real.exp (-y ^ 2 / 2) / y) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  rw [hint, Real.log_mul two_ne_zero hs.ne']
  ring

/-- **By parts on `[2s, 4s]`**: `∫ η₂(s/y)φ(y)/y = −4 log 2·(−e^{−(2s)²/2}) − 4∫ e^{−y²/2}/y`. -/
theorem ibp_hi {s : ℝ} (hs : 0 < s) :
    ∫ y in 2 * s..4 * s, HW.eta2 (s / y) * HW.phi y / y =
      -(4 * Real.log 2 * -Real.exp (-(2 * s) ^ 2 / 2)) -
        4 * ∫ y in 2 * s..4 * s, Real.exp (-y ^ 2 / 2) / y := by
  have hsub : uIcc (2 * s) (4 * s) ⊆ Ioi 0 := HW.uIcc_pos (by linarith) (by linarith)
  have hcongr : EqOn (fun y => HW.eta2 (s / y) * HW.phi y / y)
      (fun y => 4 * (2 * Real.log 2 + Real.log s - Real.log y) * (y * Real.exp (-y ^ 2 / 2)))
      (uIcc (2 * s) (4 * s)) := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    simp only
    rw [mul_div_assoc, HW.eta2_hi hs hy.1 hy.2, phi_div hy0.ne']
  rw [intervalIntegral.integral_congr hcongr]
  have hu : ∀ y ∈ uIcc (2 * s) (4 * s), HasDerivAt
      (fun y => 4 * (2 * Real.log 2 + Real.log s - Real.log y)) (4 * -y⁻¹) y := fun y hy =>
    ((Real.hasDerivAt_log (hsub hy).ne').const_sub (2 * Real.log 2 + Real.log s)).const_mul 4
  have hv : ∀ y ∈ uIcc (2 * s) (4 * s), HasDerivAt (fun y => -Real.exp (-y ^ 2 / 2))
      (y * Real.exp (-y ^ 2 / 2)) y := fun y _ => hasDerivAt_ng y
  have hu' : IntervalIntegrable (fun y => 4 * -y⁻¹) volume (2 * s) (4 * s) :=
    (continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => (hsub hy).ne').neg).intervalIntegrable
  have hv' : IntervalIntegrable (fun y => y * Real.exp (-y ^ 2 / 2)) volume (2 * s) (4 * s) :=
    (by fun_prop : Continuous fun y : ℝ => y * Real.exp (-y ^ 2 / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hint : ∫ y in 2 * s..4 * s, 4 * -y⁻¹ * -Real.exp (-y ^ 2 / 2) =
      4 * ∫ y in 2 * s..4 * s, Real.exp (-y ^ 2 / 2) / y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  have h4 : Real.log (4 * s) = 2 * Real.log 2 + Real.log s := by
    rw [show (4 : ℝ) * s = 2 * (2 * s) by ring, Real.log_mul two_ne_zero (by positivity),
      Real.log_mul two_ne_zero hs.ne']
    ring
  rw [hint, h4, Real.log_mul two_ne_zero hs.ne']
  ring

/-- **`y = 2w`**: `∫_{2s}^{4s} e^{−y²/2}/y = ∫_s^{2s} e^{−2w²}/w`. -/
theorem int_sub (s : ℝ) :
    ∫ y in 2 * s..4 * s, Real.exp (-y ^ 2 / 2) / y =
      ∫ w in s..2 * s, Real.exp (-2 * w ^ 2) / w := by
  have h := intervalIntegral.integral_comp_mul_left (a := s) (b := 2 * s)
    (fun y : ℝ => Real.exp (-y ^ 2 / 2) / y) (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [smul_eq_mul, show (2 : ℝ) * (2 * s) = 4 * s by ring] at h
  have hc : ∫ w in s..2 * s, (fun y : ℝ => Real.exp (-y ^ 2 / 2) / y) (2 * w) =
      2⁻¹ * ∫ w in s..2 * s, Real.exp (-2 * w ^ 2) / w := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun w _ => ?_
    simp only
    rw [show -(2 * w) ^ 2 / 2 = -2 * w ^ 2 by ring]
    ring
  rw [hc] at h
  linarith

/-- **THE CLOSED FORM**: `η*(t) = 4∫_{49t}^{98t} (e^{−w²/2} − e^{−2w²})/w dw` for `t > 0`. -/
theorem etaStar_closed {t : ℝ} (ht : 0 < t) :
    HW.etaStar t = 4 * ∫ w in (49 * t)..(2 * (49 * t)), fS w := by
  set s := 49 * t with hs_def
  have hs : 0 < s := by positivity
  change HW.mconv HW.eta2 HW.phi s = 4 * ∫ w in s..2 * s, fS w
  have hc : ContinuousOn (fun y => HW.eta2 (s / y) * HW.phi y / y) (Ioi 0) :=
    ((HW.eta2_div_contOn hs).mul HW.continuous_phi.continuousOn).div continuousOn_id
      fun y hy => (mem_Ioi.mp hy).ne'
  have i1 : IntervalIntegrable (fun y => HW.eta2 (s / y) * HW.phi y / y) volume s (2 * s) :=
    (hc.mono (HW.uIcc_pos hs (by linarith))).intervalIntegrable
  have i2 : IntervalIntegrable (fun y => HW.eta2 (s / y) * HW.phi y / y) volume (2 * s) (4 * s) :=
    (hc.mono (HW.uIcc_pos (by linarith) (by linarith))).intervalIntegrable
  rw [HW.mconv_eta2 HW.phi hs, ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    ibp_lo hs, ibp_hi hs, int_sub s]
  have g1i : IntervalIntegrable (fun w => Real.exp (-w ^ 2 / 2) / w) volume s (2 * s) :=
    (g1_contOn.mono (HW.uIcc_pos hs (by linarith))).intervalIntegrable
  have g2i : IntervalIntegrable (fun w => Real.exp (-2 * w ^ 2) / w) volume s (2 * s) :=
    (g2_contOn.mono (HW.uIcc_pos hs (by linarith))).intervalIntegrable
  have hf : ∫ w in s..2 * s, fS w = (∫ w in s..2 * s, Real.exp (-w ^ 2 / 2) / w) -
      ∫ w in s..2 * s, Real.exp (-2 * w ^ 2) / w := by
    rw [← intervalIntegral.integral_sub g1i g2i]
    refine intervalIntegral.integral_congr fun w _ => ?_
    simp only [fS, sub_div]
  rw [hf]
  ring

/-! ## The exponential chain -/

/-- `P(d) = 1 + d + d²/2 + d³/6 + d⁴/24` over `ℚ` (the certificate's side). -/
def pq (d : ℚ) : ℚ := 1 + d + d ^ 2 / 2 + d ^ 3 / 6 + d ^ 4 / 24

/-- `P(d)` over `ℝ`. -/
noncomputable def pr (d : ℝ) : ℝ := 1 + d + d ^ 2 / 2 + d ^ 3 / 6 + d ^ 4 / 24

theorem pq_cast (d : ℚ) : ((pq d : ℚ) : ℝ) = pr (d : ℝ) := by
  unfold pq pr
  push_cast
  ring

/-- `P(d) ≤ e^d` for `d ≥ 0` (`Real.sum_le_exp_of_nonneg`). -/
theorem pr_le_exp {d : ℝ} (hd : 0 ≤ d) : pr d ≤ Real.exp d := by
  have h := Real.sum_le_exp_of_nonneg hd 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  unfold pr
  linarith

/-- `e^d ≤ P(d) + d⁵/100` for `0 ≤ d ≤ 1` (`Real.exp_bound'`, `6/(5!·5) = 1/100`). -/
theorem exp_le_pr {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) : Real.exp d ≤ pr d + d ^ 5 / 100 := by
  have h := Real.exp_bound' h0 h1 (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  unfold pr
  linarith

/-- **One step of the chain**: from `lo ≤ X ≤ hi` to `lo' ≤ X e^{−d} ≤ hi'`. -/
theorem exp_step {X lo hi lo' hi' d : ℝ} (hX0 : 0 < X) (hlo : lo ≤ X) (hhi : X ≤ hi)
    (hd : 0 ≤ d) (hup : hi ≤ hi' * pr d)
    (hlow : lo' ≤ 0 ∨ (d ≤ 1 ∧ lo' * (pr d + d ^ 5 / 100) ≤ lo)) :
    lo' ≤ X * Real.exp (-d) ∧ X * Real.exp (-d) ≤ hi' := by
  have he : 0 < Real.exp (-d) := Real.exp_pos _
  have hed : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hp := pr_le_exp hd
  have hp0 : 0 < pr d := by
    unfold pr
    positivity
  have hXe : 0 < X * Real.exp (-d) := mul_pos hX0 he
  constructor
  · rcases hlow with h | ⟨h1, h2⟩
    · exact le_trans h hXe.le
    · rcases le_or_gt lo' 0 with h0 | h0
      · exact le_trans h0 hXe.le
      · have hq := exp_le_pr hd h1
        have k1 : 1 ≤ (pr d + d ^ 5 / 100) * Real.exp (-d) := by
          have := mul_le_mul_of_nonneg_right hq he.le
          linarith
        have k2 : lo' * (pr d + d ^ 5 / 100) * Real.exp (-d) ≤ X * Real.exp (-d) :=
          mul_le_mul_of_nonneg_right (h2.trans hlo) he.le
        have k3 : lo' ≤ lo' * ((pr d + d ^ 5 / 100) * Real.exp (-d)) :=
          le_mul_of_one_le_right h0.le k1
        rw [← mul_assoc] at k3
        exact k3.trans k2
  · have k1 : pr d * Real.exp (-d) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hp he.le
      linarith
    have hi'0 : 0 < hi' := by
      rcases le_or_gt hi' 0 with hneg | hpos
      · have := mul_nonpos_of_nonpos_of_nonneg hneg hp0.le
        linarith
      · exact hpos
    have k2 : X * Real.exp (-d) ≤ hi' * pr d * Real.exp (-d) :=
      mul_le_mul_of_nonneg_right (hhi.trans hup) he.le
    have k3 : hi' * (pr d * Real.exp (-d)) ≤ hi' := mul_le_of_le_one_right hi'0.le k1
    rw [← mul_assoc] at k3
    exact k2.trans k3

/-- The chain's step condition at `j` (decided by the kernel on the certificate). -/
abbrev StepOK (g el eh : ℕ → ℚ) (j : ℕ) : Prop :=
  0 < g j ∧ g j < g (j + 1) ∧ eh j ≤ eh (j + 1) * pq ((g (j + 1) ^ 2 - g j ^ 2) / 2) ∧
    (el (j + 1) ≤ 0 ∨ ((g (j + 1) ^ 2 - g j ^ 2) / 2 ≤ 1 ∧
      el (j + 1) * (pq ((g (j + 1) ^ 2 - g j ^ 2) / 2) + ((g (j + 1) ^ 2 - g j ^ 2) / 2) ^ 5 / 100)
        ≤ el j))

/-- The chain's base condition (from `e⁰ = 1`). -/
abbrev BaseOK (g el eh : ℕ → ℚ) : Prop :=
  0 < g 0 ∧ 1 ≤ eh 0 * pq (g 0 ^ 2 / 2) ∧
    (el 0 ≤ 0 ∨ (g 0 ^ 2 / 2 ≤ 1 ∧ el 0 * (pq (g 0 ^ 2 / 2) + (g 0 ^ 2 / 2) ^ 5 / 100) ≤ 1))

/-- The `ℚ → ℝ` transfer of one lower-branch condition. -/
theorem low_cast (l L d : ℚ) (h : l ≤ 0 ∨ (d ≤ 1 ∧ l * (pq d + d ^ 5 / 100) ≤ L)) :
    (l : ℝ) ≤ 0 ∨ ((d : ℝ) ≤ 1 ∧ (l : ℝ) * (pr (d : ℝ) + (d : ℝ) ^ 5 / 100) ≤ (L : ℝ)) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (by exact_mod_cast h)
  · refine Or.inr ⟨by exact_mod_cast h1, ?_⟩
    have h3 := (Rat.cast_le (K := ℝ)).mpr h2
    rw [Rat.cast_mul, Rat.cast_add, pq_cast, Rat.cast_div, Rat.cast_pow] at h3
    norm_num at h3 ⊢
    exact h3

/-- **The certified exponential chain**: `el_j ≤ e^{−g_j²/2} ≤ eh_j` for `j ≤ n`. -/
theorem exp_chain (g el eh : ℕ → ℚ) (n : ℕ) (hb : BaseOK g el eh)
    (hs : ∀ j < n, StepOK g el eh j) :
    ∀ j ≤ n, (el j : ℝ) ≤ Real.exp (-(g j : ℝ) ^ 2 / 2) ∧
      Real.exp (-(g j : ℝ) ^ 2 / 2) ≤ (eh j : ℝ) := by
  intro j hj
  induction j with
  | zero =>
    obtain ⟨_, hup, hlow⟩ := hb
    have hd : (((g 0 ^ 2 / 2 : ℚ)) : ℝ) = (g 0 : ℝ) ^ 2 / 2 := by push_cast; ring
    have e : Real.exp (-(g 0 : ℝ) ^ 2 / 2) = 1 * Real.exp (-((g 0 : ℝ) ^ 2 / 2)) := by
      rw [one_mul]
      congr 1
      ring
    rw [e]
    have hup' : (1 : ℝ) ≤ (eh 0 : ℝ) * pr ((g 0 : ℝ) ^ 2 / 2) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hup
      rw [Rat.cast_one, Rat.cast_mul, pq_cast, hd] at h
      exact h
    have hlow' := low_cast (el 0) 1 (g 0 ^ 2 / 2) hlow
    rw [hd, Rat.cast_one] at hlow'
    exact exp_step one_pos le_rfl le_rfl (by positivity) hup' hlow'
  | succ j ih =>
    obtain ⟨hgp, hglt, hup, hlow⟩ := hs j (by omega)
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hd : ((((g (j + 1)) ^ 2 - (g j) ^ 2) / 2 : ℚ) : ℝ) =
        (((g (j + 1) : ℝ)) ^ 2 - ((g j : ℝ)) ^ 2) / 2 := by push_cast; ring
    have hgp' : (0 : ℝ) < g j := by exact_mod_cast hgp
    have hglt' : (g j : ℝ) < g (j + 1) := by exact_mod_cast hglt
    have hd0 : 0 ≤ (((g (j + 1) : ℝ)) ^ 2 - ((g j : ℝ)) ^ 2) / 2 := by nlinarith
    have e : Real.exp (-(g (j + 1) : ℝ) ^ 2 / 2) = Real.exp (-(g j : ℝ) ^ 2 / 2) *
        Real.exp (-((((g (j + 1) : ℝ)) ^ 2 - ((g j : ℝ)) ^ 2) / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    have hup' : (eh j : ℝ) ≤ (eh (j + 1) : ℝ) *
        pr ((((g (j + 1) : ℝ)) ^ 2 - ((g j : ℝ)) ^ 2) / 2) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hup
      rw [Rat.cast_mul, pq_cast, hd] at h
      exact h
    have hlow' := low_cast (el (j + 1)) (el j) (((g (j + 1)) ^ 2 - (g j) ^ 2) / 2) hlow
    rw [hd] at hlow'
    exact exp_step (Real.exp_pos _) ih1 ih2 hd0 hup' hlow'

/-! ## One piece, one cell -/

/-- **One piece**: on `[u, v] ⊆ (0, ∞)`, with `lo ≤ e^{−v²/2}` and `e^{−(2u)²/2} ≤ hi`,
`∫_u^v f ≥ max(0, lo − hi)/v·(v − u)`. -/
theorem piece_ge {u v lo hi : ℝ} (hu : 0 < u) (huv : u ≤ v) (hlo : lo ≤ Real.exp (-v ^ 2 / 2))
    (hhi : Real.exp (-(2 * u) ^ 2 / 2) ≤ hi) :
    max 0 (lo - hi) / v * (v - u) ≤ ∫ w in u..v, fS w := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hint : IntervalIntegrable fS volume u v :=
    (fS_contOn.mono (HW.uIcc_pos hu hv)).intervalIntegrable
  have hconst : ∫ _ in u..v, max 0 (lo - hi) / v = max 0 (lo - hi) / v * (v - u) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hconst]
  refine intervalIntegral.integral_mono_on huv intervalIntegrable_const hint fun w hw => ?_
  have hw0 : 0 < w := lt_of_lt_of_le hu hw.1
  rcases le_total (lo - hi) 0 with h | h
  · rw [max_eq_left h, zero_div]
    exact fS_nonneg hw0.le
  · rw [max_eq_right h]
    have e1 : Real.exp (-v ^ 2 / 2) ≤ Real.exp (-w ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hw.1, hw.2])
    have e2 : Real.exp (-2 * w ^ 2) ≤ Real.exp (-(2 * u) ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hw.1, hw.2])
    have hnum : lo - hi ≤ Real.exp (-w ^ 2 / 2) - Real.exp (-2 * w ^ 2) := by linarith
    unfold fS
    calc (lo - hi) / v ≤ (Real.exp (-w ^ 2 / 2) - Real.exp (-2 * w ^ 2)) / v :=
          div_le_div_of_nonneg_right hnum hv.le
      _ ≤ (Real.exp (-w ^ 2 / 2) - Real.exp (-2 * w ^ 2)) / w :=
          div_le_div_of_nonneg_left (by linarith) hw0 hw.2

/-- A sum over `ℚ` by structural recursion (so that the kernel can evaluate it). -/
def sumQ (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumQ f n + f n

theorem sumQ_cast (f : ℕ → ℚ) (n : ℕ) :
    ((sumQ f n : ℚ) : ℝ) = ∑ i ∈ range n, (f i : ℝ) := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih => rw [sumQ, Rat.cast_add, ih, Finset.sum_range_succ]

/-- The piece value `q_j = max(0, el_{j+1} − eh_{j+K})/g_{j+1}`. -/
def qf (g el eh : ℕ → ℚ) (K j : ℕ) : ℚ := max 0 (el (j + 1) - eh (j + K)) / g (j + 1)

/-- The cell value `∑_{i < K−1} q_{c+1+i}(g_{c+2+i} − g_{c+1+i})`. -/
def cellS (g el eh : ℕ → ℚ) (K c : ℕ) : ℚ :=
  sumQ (fun i => qf g el eh K (c + 1 + i) * (g (c + 1 + i + 1) - g (c + 1 + i))) (K - 1)

/-- An increasing chain is monotone on `[0, n]`. -/
theorem mono_le (g : ℕ → ℚ) (n : ℕ) (hs : ∀ j < n, g j < g (j + 1)) :
    ∀ i j, i ≤ j → j ≤ n → g i ≤ g j := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (hs j (by omega)).le

/-- **One cell**: for `s ∈ (g_c, g_{c+1}]` on a doubling grid, `∫_s^{2s} f ≥ cellS`. -/
theorem cell_ge (g el eh : ℕ → ℚ) (K N c : ℕ) (hK : 1 ≤ K) (hcN : c + 2 * K ≤ N + 1)
    (hs : ∀ j < N, 0 < g j ∧ g j < g (j + 1)) (hdbl : ∀ j, g (j + K) = 2 * g j)
    (hE : ∀ j ≤ N, (el j : ℝ) ≤ Real.exp (-(g j : ℝ) ^ 2 / 2) ∧
      Real.exp (-(g j : ℝ) ^ 2 / 2) ≤ (eh j : ℝ))
    (s : ℝ) (hs1 : (g c : ℝ) < s) (hs2 : s ≤ (g (c + 1) : ℝ)) :
    ((cellS g el eh K c : ℚ) : ℝ) ≤ ∫ w in s..2 * s, fS w := by
  have hlt : ∀ j < N, g j < g (j + 1) := fun j hj => (hs j hj).2
  have hmono := mono_le g N hlt
  have hg0 : 0 < g 0 := (hs 0 (by omega)).1
  have hpos : ∀ j ≤ N, (0 : ℝ) < g j := fun j hj => by
    have h := hmono 0 j (Nat.zero_le _) hj
    exact_mod_cast lt_of_lt_of_le hg0 h
  have hs0 : 0 < s := (hpos c (by omega)).trans hs1
  have hB : ((g (c + K) : ℚ) : ℝ) = 2 * (g c : ℝ) := by
    rw [hdbl c]
    push_cast
    ring
  have hAB : ((g (c + 1) : ℚ) : ℝ) ≤ ((g (c + K) : ℚ) : ℝ) := by
    exact_mod_cast hmono (c + 1) (c + K) (by omega) (by omega)
  have hint : IntervalIntegrable fS volume s (2 * s) :=
    (fS_contOn.mono (HW.uIcc_pos hs0 (by linarith))).intervalIntegrable
  have h1 : ∫ w in ((g (c + 1) : ℚ) : ℝ)..((g (c + K) : ℚ) : ℝ), fS w ≤
      ∫ w in s..2 * s, fS w :=
    intervalIntegral.integral_mono_interval hs2 hAB (by rw [hB]; linarith)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun w hw =>
        fS_nonneg (le_of_lt (hs0.trans hw.1))) hint
  have hpiece : ∀ j ∈ Set.Ico (c + 1) (c + K),
      IntervalIntegrable fS volume ((g j : ℚ) : ℝ) ((g (j + 1) : ℚ) : ℝ) := fun j hj => by
    obtain ⟨_, hj2⟩ := Set.mem_Ico.mp hj
    exact (fS_contOn.mono (HW.uIcc_pos (hpos j (by omega))
      (hpos (j + 1) (by omega)))).intervalIntegrable
  have h2 := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun j => ((g j : ℚ) : ℝ)) (f := fS) (μ := volume) (by omega : c + 1 ≤ c + K) hpiece
  rw [Finset.sum_Ico_eq_sum_range, show c + K - (c + 1) = K - 1 by omega] at h2
  rw [cellS, sumQ_cast]
  refine le_trans ?_ (h2.le.trans h1)
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hu : (0 : ℝ) < g (c + 1 + i) := hpos (c + 1 + i) (by omega)
  have huv : ((g (c + 1 + i) : ℚ) : ℝ) ≤ ((g (c + 1 + i + 1) : ℚ) : ℝ) := by
    exact_mod_cast (hlt (c + 1 + i) (by omega)).le
  have hlo := (hE (c + 1 + i + 1) (by omega)).1
  have hhi : Real.exp (-(2 * ((g (c + 1 + i) : ℚ) : ℝ)) ^ 2 / 2) ≤
      ((eh (c + 1 + i + K) : ℚ) : ℝ) := by
    have h := (hE (c + 1 + i + K) (by omega)).2
    rw [hdbl (c + 1 + i)] at h
    push_cast at h
    exact h
  have hp := piece_ge hu huv hlo hhi
  unfold qf
  push_cast
  exact hp

/-! ## Summation by parts against `θ` -/

/-- The shifted sequence `m_{i−1}` (`0` at `i = 0`). -/
def pmQ {α : Type} [Zero α] (m : ℕ → α) : ℕ → α
  | 0 => 0
  | i + 1 => m i

/-- The worse of the two `θ` constants on an Abel coefficient `c` at the cut point `a`. -/
def mnQ (lo hi c a : ℚ) : ℚ := min (lo * c * a) (hi * c * a)

/-- The certified Abel sum: `∑_{i ≤ k} min(lo·c_i·a_i, hi·c_i·a_i)`, `c_i = m_{i−1} − m_i`
(`m_k := 0`). -/
def abelQ (lo hi : ℚ) (a m : ℕ → ℚ) (k : ℕ) : ℚ :=
  mnQ lo hi (pmQ m k) (a k) + sumQ (fun i => mnQ lo hi (pmQ m i - m i) (a i)) k

theorem pmQ_cast (m : ℕ → ℚ) (i : ℕ) :
    ((pmQ m i : ℚ) : ℝ) = pmQ (fun j => (m j : ℝ)) i := by
  cases i with
  | zero => simp [pmQ]
  | succ i => simp [pmQ]

/-- **Summation by parts**:
`∑_{i<k} m_i(θ_{i+1} − θ_i) = m_{k−1}θ_k + ∑_{i<k}(m_{i−1} − m_i)θ_i`. -/
theorem by_parts (m θ : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range k, m i * (θ (i + 1) - θ i) =
      pmQ m k * θ k + ∑ i ∈ range k, (pmQ m i - m i) * θ i := by
  induction k with
  | zero => simp [pmQ]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [pmQ]
    ring

/-- One Abel term: `lo·y ≤ θ ≤ hi·y`, `x > 0` give `x·min(lo·c·a, hi·c·a) ≤ c·θ` (`y = a·x`). -/
theorem term_ge {c a x θ lo hi : ℝ} (hx : 0 < x) (h1 : lo * (a * x) ≤ θ)
    (h2 : θ ≤ hi * (a * x)) : x * min (lo * c * a) (hi * c * a) ≤ c * θ := by
  rcases le_total 0 c with hc | hc
  · calc x * min (lo * c * a) (hi * c * a) ≤ x * (lo * c * a) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hx.le
      _ = c * (lo * (a * x)) := by ring
      _ ≤ c * θ := mul_le_mul_of_nonneg_left h1 hc
  · calc x * min (lo * c * a) (hi * c * a) ≤ x * (hi * c * a) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hx.le
      _ = c * (hi * (a * x)) := by ring
      _ ≤ c * θ := mul_le_mul_of_nonpos_left h2 hc

/-- **The Abel lower bound**: with `lo·y ≤ θ(y) ≤ hi·y` at the cut points `y = a_i x`,
`x·abelQ ≤ ∑_{i<k} m_i(θ(a_{i+1}x) − θ(a_i x))`. -/
theorem abel_ge (θ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (lo hi : ℚ) (a m : ℕ → ℚ) (k : ℕ)
    (hθ : ∀ i ≤ k, (lo : ℝ) * ((a i : ℝ) * x) ≤ θ ((a i : ℝ) * x) ∧
      θ ((a i : ℝ) * x) ≤ (hi : ℝ) * ((a i : ℝ) * x)) :
    x * ((abelQ lo hi a m k : ℚ) : ℝ) ≤
      ∑ i ∈ range k, (m i : ℝ) * (θ ((a (i + 1) : ℝ) * x) - θ ((a i : ℝ) * x)) := by
  have hbp := by_parts (fun i => (m i : ℝ)) (fun i => θ ((a i : ℝ) * x)) k
  rw [hbp, abelQ, Rat.cast_add, sumQ_cast, mul_add, Finset.mul_sum]
  refine add_le_add ?_ (Finset.sum_le_sum fun i hi => ?_)
  · obtain ⟨h1, h2⟩ := hθ k le_rfl
    rw [mnQ, Rat.cast_min, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, pmQ_cast]
    exact term_ge hx h1 h2
  · obtain ⟨h1, h2⟩ := hθ i (Finset.mem_range.mp hi).le
    rw [mnQ, Rat.cast_min, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, Rat.cast_sub,
      pmQ_cast]
    exact term_ge hx h1 h2

end Principia.Common.TernaryGoldbach.SC
