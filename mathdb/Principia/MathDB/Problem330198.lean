import Principia.MathDB.Problem372858

set_option autoImplicit false

namespace Principia.MathDB.P330198

/-! ### The logarithm bound, IMPORTED from #372858 rather than re-proved

`Principia.MathDB.P372858.log_ge_two_mul_div` states `2t/(2+t) ≤ log(1+t)` for `t ≥ 0`, which is
exactly the write-up's *"elementary inequality `log x > 2(x−1)/(x+1)`"*.  It mentions nothing of
that row's problem, so this row consumes it by import — the campaign's cheapest reuse mode, as
row 286 did with row 284's `f`. -/

/-- `2(x−1)/(x+1) ≤ log x` for `x ≥ 1`. -/
theorem log_ge (x : ℝ) (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have h := Principia.MathDB.P372858.log_ge_two_mul_div (t := x - 1) (by linarith)
  have h1 : (1 : ℝ) + (x - 1) = x := by ring
  have h2 : (2 : ℝ) + (x - 1) = x + 1 := by ring
  rw [h1, h2] at h
  exact h

/-- **The write-up's `log(a/b) > 16/25`**, for any ratio at least `33/17`. -/
theorem log_ge_const (x : ℝ) (hx : 33 / 17 ≤ x) : 16 / 25 ≤ Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hpos : (0 : ℝ) < x + 1 := by linarith
  refine le_trans ?_ (log_ge x hx1)
  rw [le_div_iff₀ hpos]
  linarith

/-! ### The exact rational certificate -/

/-- `C = ∑_{j=1}^{5} 1/((2j−1)·2j)`, the odd-index contribution to the first ten terms. -/
noncomputable def C : ℝ := 1627 / 2520

/-- `D = ∑_{n=1}^{10} (n + ⌊(n+1)/2⌋)/(n(n+1))`, the `ε`-coefficient. -/
noncomputable def D : ℝ := 18587 / 5544

theorem C_eq : C = 1 / 2 + 1 / 12 + 1 / 30 + 1 / 56 + 1 / 90 := by
  unfold C; norm_num

theorem D_pos : 0 < D := by unfold D; norm_num

/-- **The write-up's final arithmetic**, exactly. -/
theorem certificate : (16 : ℝ) / 25 + C - D / 50 - 2 / 11 = 95797 / 92400 := by
  unfold C D; norm_num

theorem certificate_gt_one : (1 : ℝ) < 95797 / 92400 := by norm_num

/-- ...and the stated margin `95797/92400 = 1 + 3397/92400`. -/
theorem margin : (95797 : ℝ) / 92400 = 1 + 3397 / 92400 := by norm_num

/-! ### The spine

`E(a,b) = log(a/b) − S₁₀ − T`, and the write-up computes `S₁₀ = −C + εD` from ten exact floor
identities and bounds the tail by `T < a/11 < 2/11`.  Those two facts are the analytic content and
enter here as named hypotheses; everything else is arithmetic and is proved. -/

theorem E_gt_one (E logab T eps : ℝ)
    (hE : E = logab + C - eps * D - T)
    (hlog : 16 / 25 ≤ logab)
    (heps : 0 < eps) (heps' : eps < 1 / 50)
    (hT : T < 2 / 11) :
    1 < E := by
  have hD := D_pos
  have hepsD : eps * D < D / 50 := by nlinarith
  have hc := certificate
  linarith [certificate_gt_one]

/-- **The refutation, modulo the two analytic inputs.**  Polanco's Conjecture 2 asserts
`|E(a,b)| < 1` for all irrational `a, b > 1`; at `a = 2 − ε`, `b = 1 + ε` with `0 < ε < 1/50`
irrational, `E(a,b) > 95797/92400 > 1`, so the absolute value exceeds one. -/
theorem abs_E_gt_one (E logab T eps : ℝ)
    (hE : E = logab + C - eps * D - T)
    (hlog : 16 / 25 ≤ logab)
    (heps : 0 < eps) (heps' : eps < 1 / 50)
    (hT : T < 2 / 11) :
    1 < |E| := by
  have h := E_gt_one E logab T eps hE hlog heps heps' hT
  rw [abs_of_pos (by linarith)]
  exact h

end Principia.MathDB.P330198
