import Mathlib

/-!
# MathDB #364606 — Canfield–Helton–Hughes: `e^{−x/(r+1)} B_r(x)` has nonnegative coefficients

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/364606/solution.tex`, proving Conjecture 3.2 of Canfield, Helton
and Hughes: for every integer `r ≥ 1`, with `B_r(x) = eˣ − ∑_{j<r} xʲ/j!`, all Maclaurin
coefficients of `e^{−x/(r+1)} B_r(x)` are nonnegative.

**What is proved.**  `chh_conj`: exactly that, for the formal power series over `ℚ` (the Maclaurin
coefficients of these entire functions are these rational numbers).  **Not formalized:** the
write-up's refinements (which coefficients vanish, strict positivity, and the `iff` in `c`).

**Route (an algebraic replacement for the write-up's Beta moments).**  With `μ = 1/(r+1)`,
`R = e^{−μx}` and `G = R·B_r`: `B_r′ = B_r + x^{r−1}/(r−1)!` and `R′ = −μR` give
`K := G′ − (1 − μ)G = x^{r−1}R/(r−1)!` (`K_eq`), and then `x K′ = ((r−1) − μx) K` (`K_ode`).
On coefficients `g_N`, with `k_n = (n+1)g_{n+1} − (1−μ)g_n`, this is
`(n + 2 − r) k_{n+1} = −μ k_n`, which yields
`N(N−r) g_N = ((r−1)(N−r−1)/(r+1)) g_{N−1} + (r/(r+1)²) g_{N−2}` for `N ≥ r + 2`, with nonnegative
weights.  Together with `g_N = 0` for `N < r`, `g_r = 1/r!` and `g_{r+1} = 0`, induction gives
`g_N ≥ 0`.  The recurrence and values were checked exactly in Python for `r ≤ 6`, `N < 30`.
-/

namespace Principia.MathDB.P364606

open PowerSeries

/-- `μ = 1/(r+1)`. -/
noncomputable def mu (r : ℕ) : ℚ := 1 / ((r : ℚ) + 1)

/-- `B_r(x) = eˣ − ∑_{j<r} xʲ/j!`. -/
noncomputable def Br (r : ℕ) : PowerSeries ℚ :=
  exp ℚ - ∑ j ∈ Finset.range r, C (1 / (j.factorial : ℚ)) * X ^ j

/-- `R = e^{−μx}`. -/
noncomputable def R (r : ℕ) : PowerSeries ℚ := rescale (-mu r) (exp ℚ)

/-- `G = e^{−μx} B_r(x)`. -/
noncomputable def G (r : ℕ) : PowerSeries ℚ := R r * Br r

/-- **Conjecture 3.2 of Canfield–Helton–Hughes.** -/
def CHHConj : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ N : ℕ, 0 ≤ coeff N (rescale (-(1 / ((r : ℚ) + 1))) (exp ℚ)
    * (exp ℚ - ∑ j ∈ Finset.range r, C (1 / (j.factorial : ℚ)) * X ^ j))

theorem mu_pos (r : ℕ) : 0 < mu r := by
  unfold mu
  positivity

theorem coeff_Br (r n : ℕ) : coeff n (Br r) = if r ≤ n then 1 / (n.factorial : ℚ) else 0 := by
  simp only [Br, map_sub, map_sum, coeff_C_mul, coeff_X_pow, coeff_exp]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  simp only [eq_ratCast, Rat.cast_id]
  split_ifs with h1 h2 <;> first | omega | ring

theorem coeff_R (r n : ℕ) : coeff n (R r) = (-mu r) ^ n / (n.factorial : ℚ) := by
  simp only [R, coeff_rescale, coeff_exp, eq_ratCast, Rat.cast_id]
  ring

/-- `R′ = −μR`. -/
theorem dR (r : ℕ) : derivative ℚ (R r) = -(C (mu r)) * R r := by
  ext n
  rw [coeff_derivative, neg_mul, map_neg, coeff_C_mul, coeff_R, coeff_R, Nat.factorial_succ]
  push_cast
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- `B_r′ = B_r + x^{r−1}/(r−1)!` for `r ≥ 1`. -/
theorem dBr (r : ℕ) (hr : 1 ≤ r) :
    derivative ℚ (Br r) = Br r + C (1 / ((r - 1).factorial : ℚ)) * X ^ (r - 1) := by
  ext n
  rw [coeff_derivative, map_add, coeff_C_mul, coeff_X_pow, coeff_Br, coeff_Br, Nat.factorial_succ]
  push_cast
  have h2 : (n.factorial : ℚ) ≠ 0 := by positivity
  by_cases hn : r ≤ n
  · rw [if_pos (by omega), if_pos hn, if_neg (by omega)]
    field_simp
    ring
  · by_cases hn1 : n = r - 1
    · rw [if_pos (by omega), if_neg hn, if_pos hn1, hn1]
      have h3 : (((r - 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    · rw [if_neg (by omega), if_neg hn, if_neg hn1]
      ring

/-- `K = G′ − (1 − μ)G`. -/
noncomputable def K (r : ℕ) : PowerSeries ℚ := derivative ℚ (G r) - (1 - C (mu r)) * G r

/-- `K = x^{r−1} R/(r−1)!`. -/
theorem K_eq (r : ℕ) (hr : 1 ≤ r) :
    K r = C (1 / ((r - 1).factorial : ℚ)) * (R r * X ^ (r - 1)) := by
  unfold K G
  rw [Derivation.leibniz, dBr r hr, dR]
  simp only [smul_eq_mul]
  ring

/-- `x K′ = ((r−1) − μx) K`. -/
theorem K_ode (r : ℕ) (hr : 1 ≤ r) :
    X * derivative ℚ (K r) = (C ((r : ℚ) - 1) - C (mu r) * X) * K r := by
  rw [K_eq r hr]
  rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, Derivation.leibniz, dR,
    Derivation.leibniz_pow, derivative_X]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
  rcases Nat.lt_or_ge r 2 with h | h
  · have hr1 : r = 1 := by omega
    subst hr1
    simp
    ring
  · have hX : X * X ^ (r - 1 - 1) = (X : PowerSeries ℚ) ^ (r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hc : ((r - 1 : ℕ) : PowerSeries ℚ) = C ((r : ℚ) - 1) := by
      rw [← map_natCast C, Nat.cast_sub hr]
      simp
    rw [hc]
    linear_combination (C (1 / ((r - 1).factorial : ℚ)) * R r * C ((r : ℚ) - 1)) * hX

theorem coeff_G_zero (r : ℕ) (hr : 1 ≤ r) : coeff 0 (G r) = 0 := by
  rw [G, coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
    ← coeff_zero_eq_constantCoeff_apply, coeff_Br, if_neg (by omega), mul_zero]

/-- The coefficient form of `K`: `k_n = (n+1) g_{n+1} − (1 − μ) g_n`. -/
theorem coeff_K (r n : ℕ) :
    coeff n (K r) = coeff (n + 1) (G r) * ((n : ℚ) + 1) - (1 - mu r) * coeff n (G r) := by
  rw [K, map_sub, coeff_derivative, sub_mul, one_mul, map_sub, coeff_C_mul]
  push_cast
  ring

/-- `k_n` from `K_eq`: zero below `r − 1`, `1/(r−1)!` at `r − 1`. -/
theorem coeff_K_small (r n : ℕ) (hr : 1 ≤ r) :
    coeff n (K r) = if r - 1 ≤ n then (1 / ((r - 1).factorial : ℚ)) * coeff (n - (r - 1)) (R r)
      else 0 := by
  rw [K_eq r hr, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> ring

/-- `(n + 2 − r) k_{n+1} = −μ k_n`. -/
theorem k_rec (r n : ℕ) (hr : 1 ≤ r) :
    ((n : ℚ) + 2 - r) * coeff (n + 1) (K r) = -(mu r) * coeff n (K r) := by
  have h := congrArg (coeff (n + 1)) (K_ode r hr)
  rw [coeff_succ_X_mul, coeff_derivative, sub_mul, map_sub, coeff_C_mul, mul_assoc,
    coeff_C_mul, coeff_succ_X_mul] at h
  push_cast at h
  linear_combination h

/-- **MathDB #364606: the Canfield–Helton–Hughes conjecture holds.** -/
theorem chh_conj : CHHConj := by
  intro r hr N
  have hG : rescale (-(1 / ((r : ℚ) + 1))) (exp ℚ)
      * (exp ℚ - ∑ j ∈ Finset.range r, C (1 / (j.factorial : ℚ)) * X ^ j) = G r := rfl
  rw [hG]
  set g : ℕ → ℚ := fun n => coeff n (G r) with hg
  set k : ℕ → ℚ := fun n => coeff n (K r) with hk
  have hmu : mu r = 1 / ((r : ℚ) + 1) := rfl
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hr
  have hkg : ∀ n, k n = g (n + 1) * ((n : ℚ) + 1) - (1 - mu r) * g n := fun n => coeff_K r n
  -- `g_n = 0` for `n < r`
  have hsmall : ∀ n, n < r → g n = 0 := by
    intro n
    induction n with
    | zero => intro _; exact coeff_G_zero r hr
    | succ n ih =>
      intro hn
      have h1 := hkg n
      have h2 : k n = 0 := by
        show coeff n (K r) = 0
        rw [coeff_K_small r n hr, if_neg (by omega)]
      rw [h2, ih (by omega)] at h1
      have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
      have : g (n + 1) * ((n : ℚ) + 1) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hn1
  have hkr1 : k (r - 1) = 1 / ((r - 1).factorial : ℚ) := by
    show coeff (r - 1) (K r) = _
    rw [coeff_K_small r (r - 1) hr, if_pos le_rfl, Nat.sub_self, coeff_R]
    simp
  have hfac : ((r.factorial : ℕ) : ℚ) = (r : ℚ) * ((r - 1).factorial : ℚ) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [Nat.factorial_succ]
    push_cast
    rw [Nat.cast_sub hr]
    ring
  have hfpos : (0 : ℚ) < ((r - 1).factorial : ℚ) := by positivity
  have hgr : g r = 1 / (r * ((r - 1).factorial : ℚ)) := by
    have h1 := hkg (r - 1)
    rw [hkr1, show r - 1 + 1 = r by omega, hsmall (r - 1) (by omega), Nat.cast_sub hr] at h1
    field_simp at h1 ⊢
    push_cast at h1
    linarith
  have hkr : k r = -(mu r) * (1 / ((r - 1).factorial : ℚ)) := by
    have h := k_rec r (r - 1) hr
    rw [show r - 1 + 1 = r by omega, Nat.cast_sub hr] at h
    change ((↑r - 1 : ℚ) + 2 - ↑r) * k r = -mu r * k (r - 1) at h
    rw [hkr1] at h
    linarith
  have hgr1 : g (r + 1) = 0 := by
    have h1 := hkg r
    rw [hkr, hgr, hmu] at h1
    have hr1 : ((r : ℚ) + 1) ≠ 0 := by positivity
    field_simp at h1
    have : g (r + 1) * (((r : ℚ) + 1) * (((r : ℚ) + 1) * (r - 1).factorial * r)) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exfalso
      have : (0 : ℚ) < ((r : ℚ) + 1) * (((r : ℚ) + 1) * (r - 1).factorial * r) := by positivity
      linarith
  -- the second-order recurrence for `N ≥ r + 2`
  have hrec2 : ∀ N, r + 2 ≤ N →
      (N : ℚ) * (N - r) * g N = ((r : ℚ) - 1) * (N - r - 1) / (r + 1) * g (N - 1)
        + r * (1 / ((r : ℚ) + 1)) ^ 2 * g (N - 2) := by
    intro N hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
    have h := k_rec r m hr
    change ((m : ℚ) + 2 - r) * k (m + 1) = -mu r * k m at h
    rw [hkg (m + 1), hkg m, hmu, show m + 1 + 1 = m + 2 from rfl] at h
    rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    push_cast at h ⊢
    have hr1 : ((r : ℚ) + 1) ≠ 0 := by positivity
    have hI : 1 / ((r : ℚ) + 1) * ((r : ℚ) + 1) = 1 := div_mul_cancel₀ (1 : ℚ) hr1
    linear_combination h + (-(1 / ((r : ℚ) + 1)) * g m - g (m + 1) * (m : ℚ)
      + g (m + 1) * (r : ℚ) - 2 * g (m + 1)) * hI
  -- nonnegativity by strong induction
  have hpos : ∀ N, 0 ≤ g N := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases Nat.lt_or_ge N r with h | h
      · rw [hsmall N h]
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [← h', hgr]
          positivity
        · rcases Nat.eq_or_lt_of_le h' with h'' | h''
          · rw [← h'', hgr1]
          · have hN : r + 2 ≤ N := by omega
            have e := hrec2 N hN
            have a1 := ih (N - 1) (by omega)
            have a2 := ih (N - 2) (by omega)
            have hNr : (0 : ℚ) < (N : ℚ) * (N - r) := by
              have : (r : ℚ) + 2 ≤ N := by exact_mod_cast hN
              nlinarith
            have hc1 : 0 ≤ ((r : ℚ) - 1) * (N - r - 1) / (r + 1) := by
              have : (1 : ℚ) ≤ r := by exact_mod_cast hr
              have : (r : ℚ) + 2 ≤ N := by exact_mod_cast hN
              apply div_nonneg _ (by positivity)
              nlinarith
            have rhs : 0 ≤ ((r : ℚ) - 1) * (N - r - 1) / (r + 1) * g (N - 1)
                + r * (1 / ((r : ℚ) + 1)) ^ 2 * g (N - 2) :=
              add_nonneg (mul_nonneg hc1 a1) (mul_nonneg (by positivity) a2)
            rw [← e] at rhs
            by_contra hneg
            push_neg at hneg
            nlinarith
  exact hpos N

end Principia.MathDB.P364606
