import Mathlib

/-!
# MathDB #335285 — the unrestricted extension of Kalmykov–Karp's Theorem 3 to all `α > 0` is FALSE

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/335285/solution.tex`, refuting Conjecture 1 of Kalmykov–Karp
(p. 344): for a nontrivial nonnegative log-concave sequence `(gₙ)` without internal zeros,
`g(μ; x) = ∑ gₙ xⁿ / Γ_q(μ + n)` and `Δ_g = g(μ+α; x) g(μ+β; x) − g(μ; x) g(μ+α+β; x)`, the
conclusions of Theorem 3 (positivity of `Δ_g`) extend to every `α > 0`, keeping `β > 0` and
`μ ≥ max(−β, −1)`.

**The objects.**  `(a; q)_∞ = ∏ⱼ (1 − a qʲ)` (`qp`, a `tprod`), and the reciprocal gamma
function `1/Γ_q(z) = (1 − q)^{z−1} (q^z; q)_∞ / (q; q)_∞` (`rG`), the source's product definition
inverted, so that poles cause no division by zero.  `[z]_q = (1 − q^z)/(1 − q)` (`qint`).

**What is refuted, and why it is stated weakly.**  `Conj1` asks only for `Δ_g(x) ≥ 0` (not `> 0`),
only for FINITELY supported sequences (so every series is a finite sum), at every `x > 0`.  The
witness breaks it at `x = 1`; for `g = δ₀`, `Δ_g` does not depend on `x`, so the constant
coefficient is negative too.

**The witness (the write-up's).**  `q = 256/625` (so `q^{1/4} = 4/5`), `μ = −3/4`, `α = 1/4`,
`β = 2`, `g₀ = 1`, `gₙ = 0` otherwise.  `Γ_q(z+1) = [z]_q Γ_q(z)` (`rG_rec`, from
`(a;q)_∞ = (1−a)(aq;q)_∞`) gives `Δ_g = A·B·(−95/576)` with `A = 1/Γ_q(1/4) > 0` and
`B = 1/Γ_q(1/2) > 0` (`qp_pos`, through `Real.rexp_tsum_eq_tprod`).  Checked exactly in Python, and
numerically against the product definition.
-/

namespace Principia.MathDB.P335285

/-- `(a; q)_∞ = ∏ⱼ (1 − a qʲ)`. -/
noncomputable def qp (q a : ℝ) : ℝ := ∏' j : ℕ, (1 - a * q ^ j)

/-- `1/Γ_q(z) = (1 − q)^{z−1} (q^z; q)_∞ / (q; q)_∞`. -/
noncomputable def rG (q z : ℝ) : ℝ := (1 - q) ^ (z - 1) * qp q (q ^ z) / qp q q

/-- `[z]_q = (1 − q^z)/(1 − q)`. -/
noncomputable def qint (q z : ℝ) : ℝ := (1 - q ^ z) / (1 - q)

/-- `g(μ; x) = ∑_{n < N} gₙ xⁿ / Γ_q(μ + n)` for a sequence supported below `N`. -/
noncomputable def gser (q : ℝ) (gs : ℕ → ℝ) (N : ℕ) (μ x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, gs n * x ^ n * rG q (μ + n)

/-- No internal zeros. -/
def NoInternalZeros (gs : ℕ → ℝ) : Prop :=
  ∀ i j k : ℕ, i < j → j < k → gs i ≠ 0 → gs k ≠ 0 → gs j ≠ 0

/-- **Conjecture 1**, weakest reading: `Δ_g ≥ 0` for finitely supported sequences. -/
def Conj1 : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ (gs : ℕ → ℝ) (N : ℕ), (∀ n, 0 ≤ gs n) → (∃ n, gs n ≠ 0) →
    (∀ n, N ≤ n → gs n = 0) → (∀ n, 1 ≤ n → gs (n - 1) * gs (n + 1) ≤ gs n ^ 2) →
    NoInternalZeros gs → ∀ μ α β : ℝ, 0 < α → 0 < β → max (-β) (-1) ≤ μ → ∀ x : ℝ, 0 < x →
      0 ≤ gser q gs N (μ + α) x * gser q gs N (μ + β) x
        - gser q gs N μ x * gser q gs N (μ + α + β) x

theorem multipliable_shift (q a : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Multipliable (fun j : ℕ => 1 - a * q ^ (j + 1)) := by
  have hs : Summable (fun j : ℕ => -(a * q) * q ^ j) :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  exact (Real.multipliable_one_add_of_summable hs).congr fun j => by
    beta_reduce
    ring

/-- `(a; q)_∞ = (1 − a)(aq; q)_∞`. -/
theorem qp_succ (q a : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : qp q a = (1 - a) * qp q (a * q) := by
  unfold qp
  rw [tprod_eq_zero_mul' (f := fun j : ℕ => 1 - a * q ^ j) (multipliable_shift q a hq0 hq1)]
  simp only [pow_zero, mul_one]
  congr 1
  exact tprod_congr fun j => by ring

/-- `(a; q)_∞ > 0` for `0 ≤ a < 1`. -/
theorem qp_pos (q a : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    0 < qp q a := by
  have hfn : ∀ j : ℕ, 0 < 1 - a * q ^ j := fun j => by
    have : a * q ^ j ≤ a := mul_le_of_le_one_right ha0 (pow_le_one₀ hq0.le hq1.le)
    linarith
  have hs : Summable (fun j : ℕ => -a * q ^ j) :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hlog : Summable (fun j : ℕ => Real.log (1 - a * q ^ j)) :=
    (Real.summable_log_one_add_of_summable hs).congr fun j => by
      beta_reduce
      congr 1
      ring
  unfold qp
  rw [← Real.rexp_tsum_eq_tprod hfn hlog]
  exact Real.exp_pos _

/-- `1/Γ_q(z) = [z]_q / Γ_q(z + 1)`, i.e. `Γ_q(z + 1) = [z]_q Γ_q(z)`. -/
theorem rG_rec (q z : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : rG q z = qint q z * rG q (z + 1) := by
  have h1q : (1 - q) ≠ 0 := by linarith
  unfold rG qint
  rw [qp_succ q (q ^ z) hq0 hq1, ← Real.rpow_add_one hq0.ne', show z + 1 - 1 = z by ring,
    Real.rpow_sub_one h1q]
  ring

/-- The witness modulus `q = 256/625`. -/
noncomputable def q0 : ℝ := 256 / 625

theorem q0_rpow (r : ℝ) : q0 ^ r = (4 / 5 : ℝ) ^ (4 * r) := by
  rw [q0, Real.rpow_mul (x := 4 / 5) (by norm_num) 4 r,
    show ((4 / 5 : ℝ) ^ (4 : ℝ)) = 256 / 625 by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num]

theorem hq0 : 0 < q0 := by
  rw [q0]
  norm_num

theorem hq1 : q0 < 1 := by
  rw [q0]
  norm_num

theorem pow_quarter : q0 ^ (1 / 4 : ℝ) = 4 / 5 := by
  rw [q0_rpow, show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]

theorem pow_half : q0 ^ (1 / 2 : ℝ) = 16 / 25 := by
  rw [q0_rpow, show (4 : ℝ) * (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem pow_neg_half : q0 ^ (-1 / 2 : ℝ) = 25 / 16 := by
  rw [q0_rpow, show (4 : ℝ) * (-1 / 2) = -((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (x := 4 / 5) (by norm_num), Real.rpow_natCast]
  norm_num

theorem pow_neg_three_quarters : q0 ^ (-3 / 4 : ℝ) = 125 / 64 := by
  rw [q0_rpow, show (4 : ℝ) * (-3 / 4) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (x := 4 / 5) (by norm_num), Real.rpow_natCast]
  norm_num

/-- **The key value**: `Δ_g = (1/Γ_q(1/4))·(1/Γ_q(1/2))·(−95/576)` for `g = δ₀`. -/
theorem delta_value :
    rG q0 (-1 / 2) * rG q0 (5 / 4) - rG q0 (-3 / 4) * rG q0 (3 / 2)
      = rG q0 (1 / 4) * rG q0 (1 / 2) * (-95 / 576) := by
  have r1 := rG_rec q0 (-1 / 2) hq0 hq1
  have r2 := rG_rec q0 (1 / 4) hq0 hq1
  have r3 := rG_rec q0 (-3 / 4) hq0 hq1
  have r4 := rG_rec q0 (1 / 2) hq0 hq1
  rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at r1
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num] at r2
  rw [show (-3 / 4 : ℝ) + 1 = 1 / 4 by norm_num] at r3
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at r4
  have i1 : qint q0 (-1 / 2) = (1 - 25 / 16) / (1 - 256 / 625) := by
    rw [qint, pow_neg_half, q0]
  have i2 : qint q0 (1 / 4) = (1 - 4 / 5) / (1 - 256 / 625) := by
    rw [qint, pow_quarter, q0]
  have i3 : qint q0 (-3 / 4) = (1 - 125 / 64) / (1 - 256 / 625) := by
    rw [qint, pow_neg_three_quarters, q0]
  have i4 : qint q0 (1 / 2) = (1 - 16 / 25) / (1 - 256 / 625) := by
    rw [qint, pow_half, q0]
  rw [i1] at r1
  rw [i2] at r2
  rw [i3] at r3
  rw [i4] at r4
  rw [r1, r3, r2, r4]
  ring

theorem gser_delta (ν : ℝ) : gser q0 (fun n => if n = 0 then 1 else 0) 1 ν 1 = rG q0 ν := by
  simp [gser]

/-- **MathDB #335285: Conjecture 1 of Kalmykov–Karp is false.** -/
theorem not_conj1 : ¬ Conj1 := by
  intro h
  have hA : 0 < rG q0 (1 / 4) := by
    unfold rG
    refine div_pos (mul_pos (Real.rpow_pos_of_pos (by rw [q0]; norm_num) _) ?_)
      (qp_pos q0 q0 hq0 hq1 hq0.le hq1)
    exact qp_pos q0 _ hq0 hq1 (Real.rpow_nonneg hq0.le _) (by rw [pow_quarter]; norm_num)
  have hB : 0 < rG q0 (1 / 2) := by
    unfold rG
    refine div_pos (mul_pos (Real.rpow_pos_of_pos (by rw [q0]; norm_num) _) ?_)
      (qp_pos q0 q0 hq0 hq1 hq0.le hq1)
    exact qp_pos q0 _ hq0 hq1 (Real.rpow_nonneg hq0.le _) (by rw [pow_half]; norm_num)
  have hc := h q0 hq0 hq1 (fun n => if n = 0 then 1 else 0) 1
    (fun n => show (0 : ℝ) ≤ if n = 0 then 1 else 0 by split_ifs <;> norm_num) ⟨0, by simp⟩
    (fun n hn => if_neg (by omega))
    (fun n _ => by
      simp only [Nat.add_one_ne_zero, if_false, mul_zero]
      exact sq_nonneg _)
    (fun i j k hij hjk hi hk => absurd (if_neg (by omega : k ≠ 0)) hk)
    (-3 / 4) (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num) 1 one_pos
  rw [gser_delta, gser_delta, gser_delta, gser_delta,
    show (-3 / 4 : ℝ) + 1 / 4 + 2 = 3 / 2 by norm_num,
    show (-3 / 4 : ℝ) + 1 / 4 = -1 / 2 by norm_num,
    show (-3 / 4 : ℝ) + 2 = 5 / 4 by norm_num, delta_value] at hc
  nlinarith [mul_pos hA hB]

end Principia.MathDB.P335285
