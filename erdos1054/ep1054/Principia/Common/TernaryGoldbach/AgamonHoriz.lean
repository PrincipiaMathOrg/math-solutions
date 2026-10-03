/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.ExplicitSpine
import Principia.Common.TernaryGoldbach.AgamonHorizLambda

set_option autoImplicit false

/-!
# `EF.Horizontal` (EF5, "the real risk"): PROVED (`horizontal_holds`)

```
 landauHeights_holds (PROVED, AgamonHorizPick)   allFactor_holds (PROVED, AgamonHorizLambda)
        └──── goodHeight_of_factor : LFactor χ → GoodHeight χ ────┘
                              ▼
 horizontal_of_good (PROVED here): super-polynomial decay of Φ beats |L'/L| ≤ C(T₀+2)^n
                              ▼
                 EF.Horizontal  (horizontal_holds)
```

Route (Landau–Jensen–pigeonhole, all crude): for every primitive `χ` an entire `F` (the
completed `L`-function `Λ(·, χ)` for `q ≠ 1`, `ξ(s) = s(s − 1)Λ(s)` for `q = 1`) with
`|F| ≤ e^{C(|t|+2)}` on `−40 ≤ σ ≤ 40` and `|F(σ₀ + it)| ≥ e^{−C(|t|+2)}` (`AgamonHorizLambda`,
from the functional equation, the SW strip bound, PNT+'s `ζ₀` and crude `Γ` bounds in
`AgamonHorizGamma`); Landau's lemma + Jensen at `σ₀ ± i(T₀ + 1/2)` and pigeonhole give a height
`T ∈ [T₀, T₀ + 1]` with `|F'/F| ≤ C'(T₀ + 2)²` on both segments (`AgamonHorizPick`, reusing the
SW bricks `landau_log_deriv`, `sum_m_le_jensen`, `logDeriv_bound_of_ne_zero`); `L'/L = F'/F − E`
with `|E| = |Γ'_ℝ/Γ_ℝ| + O(1) ≤ C(|t| + 2)`.

`horizontal_of_good`: at a good height `T ∈ [T₀', T₀' + 1]`,
`|Ψ(σ ± iT)| = |L'/L|·|Φ|·x^σ ≤ C(T₀' + 2)^n · C_{n+1}/(1 + T)^{n+1} · (x^{−1/2} + x^{3/2})
≤ |C| 2^n C_{n+1} X/(1 + T₀')`, and each horizontal integral is at most twice the integrand bound;
`T₀'` is chosen beyond `T₀`, `T₁` and `4|C|C_{n+1}X 2^n/θ`.

No falsification of `EF.Horizontal` was found: it is true as stated (junk values only help: a
non-integrable integrand has `HIntegral = 0`, and `L'/L = 0` at a zero of `L`, which good heights
avoid anyway).
-/

namespace Principia.Common.TernaryGoldbach.AH

open Complex

/-- `x^σ ≤ x^{−1/2} + x^{3/2}` for `x > 0`, `−1/2 ≤ σ ≤ 3/2`. -/
theorem rpow_le_of_mem {x σ : ℝ} (hx : 0 < x) (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) :
    x ^ σ ≤ x ^ (-1 / 2 : ℝ) + x ^ (3 / 2 : ℝ) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · have h3 := Real.rpow_le_rpow_of_exponent_le hx1 h2
    have h4 : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    linarith
  · have h3 := Real.rpow_le_rpow_of_exponent_ge hx hx1.le h1
    have h4 : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    linarith

/-- **The integrand bound**: `|Ψ(s)| ≤ |L'/L(s)|·|Φ(s)|·(x^{−1/2} + x^{3/2})` on the strip. -/
theorem psi_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Φ : ℂ → ℂ) {x : ℝ}
    (hx : 0 < x) (s : ℂ) {P Q : ℝ} (hre1 : -1 / 2 ≤ s.re) (hre2 : s.re ≤ 3 / 2)
    (hLD : ‖EF.LD χ s‖ ≤ P) (hΦ : ‖Φ s‖ ≤ Q) :
    ‖EF.Psi χ Φ x s‖ ≤ P * Q * (x ^ (-1 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) := by
  unfold EF.Psi
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hP0 : 0 ≤ P := le_trans (norm_nonneg _) hLD
  have hQ0 : 0 ≤ Q := le_trans (norm_nonneg _) hΦ
  exact mul_le_mul (mul_le_mul hLD hΦ (norm_nonneg _) hP0) (rpow_le_of_mem hx hre1 hre2)
    (Real.rpow_nonneg hx.le _) (mul_nonneg hP0 hQ0)

/-- **A horizontal integral is at most twice its integrand bound** (length `3/2 − (−1/2) = 2`). -/
theorem hIntegral_le (f : ℂ → ℂ) (y B : ℝ)
    (hB : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 / 2 → ‖f (σ + y * I)‖ ≤ B) :
    ‖HIntegral f (-1 / 2) (3 / 2) y‖ ≤ B * 2 := by
  unfold HIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1 / 2) (b := 3 / 2) (C := B) (f := fun σ : ℝ => f (σ + y * I)) (fun σ hσ => by
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      exact hB σ hσ.1.le hσ.2)
  have h2 : |(3 / 2 : ℝ) - (-1 / 2)| = 2 := by norm_num
  rwa [h2] at h

/-- **`EF.Horizontal` from good heights** (PROVED): super-polynomial decay of `Φ` against the
polynomial bound on `L'/L` at good heights. -/
theorem horizontal_of_good (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → GoodHeight χ) : EF.Horizontal := by
  intro q _ χ hχ Φ hΦ x hx θ hθ T₀
  obtain ⟨C, n, T₁, hG⟩ := h q χ hχ
  obtain ⟨Ck, hCk⟩ := hΦ (n + 1)
  set X : ℝ := x ^ (-1 / 2 : ℝ) + x ^ (3 / 2 : ℝ) with hX
  have hX0 : 0 ≤ X := add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
  have hCk0 : 0 ≤ Ck := by
    have h0 := hCk 0 (by norm_num) (by norm_num)
    have h1 : (1 + |(0 : ℂ).im|) ^ (n + 1) = 1 := by simp
    rw [h1, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  set M : ℝ := 4 * |C| * Ck * X * 2 ^ n / θ with hM
  set T₀' : ℝ := max (max T₀ T₁) (max 1 M) with hT₀'
  have hT₀'1 : 1 ≤ T₀' := le_trans (le_max_left 1 M) (le_max_right _ _)
  have hT₀'M : M ≤ T₀' := le_trans (le_max_right 1 M) (le_max_right _ _)
  have hT₀'0 : T₀ ≤ T₀' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT₀'T : T₁ ≤ T₀' := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨T, hT0, hT1, hz, hb⟩ := hG T₀' hT₀'T
  have hTpos : 0 < T := by linarith
  set A : ℝ := 1 + T with hA
  have hApos : 0 < A := by linarith
  -- the integrand bound at height `±T`
  set B : ℝ := C * (T₀' + 2) ^ n * (Ck / A ^ (n + 1)) * X with hB
  have hpt : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → |s.im| = T →
      ‖EF.LD χ s‖ ≤ C * (T₀' + 2) ^ n → ‖EF.Psi χ Φ x s‖ ≤ B := by
    intro s h1 h2 him hLD
    have hΦs := hCk s h1 h2
    rw [him] at hΦs
    exact psi_bound χ Φ hx s h1 h2 hLD hΦs
  have hHT : ‖HIntegral (EF.Psi χ Φ x) (-1 / 2) (3 / 2) T‖ ≤ B * 2 := by
    refine hIntegral_le _ _ _ fun σ h1 h2 => hpt _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_pos hTpos]) (hb σ h1 h2).1
  have hHmT : ‖HIntegral (EF.Psi χ Φ x) (-1 / 2) (3 / 2) (-T)‖ ≤ B * 2 := by
    refine hIntegral_le _ _ _ fun σ h1 h2 => ?_
    have heq : (σ : ℂ) + ((-T : ℝ) : ℂ) * I = (σ : ℂ) - T * I := by push_cast; ring
    rw [heq]
    exact hpt _ (by simpa using h1) (by simpa using h2) (by simp [abs_of_pos hTpos])
      (hb σ h1 h2).2
  -- `B ≤ |C| 2^n C_{n+1} X / A`
  have hBle : B ≤ |C| * 2 ^ n * Ck * X / A := by
    have hT2 : T₀' + 2 ≤ 2 * A := by linarith
    have hpow : (T₀' + 2) ^ n ≤ 2 ^ n * A ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) hT2 n
    have hCabs : C * (T₀' + 2) ^ n ≤ |C| * (2 ^ n * A ^ n) :=
      (le_abs_self C |> fun h => mul_le_mul_of_nonneg_right h (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg C))
    have hAn : 0 < A ^ n := pow_pos hApos n
    have hfac : 0 ≤ Ck / A ^ (n + 1) * X := mul_nonneg (div_nonneg hCk0 (by positivity)) hX0
    calc B = C * (T₀' + 2) ^ n * (Ck / A ^ (n + 1) * X) := by rw [hB]; ring
      _ ≤ |C| * (2 ^ n * A ^ n) * (Ck / A ^ (n + 1) * X) := mul_le_mul_of_nonneg_right hCabs hfac
      _ = |C| * 2 ^ n * Ck * X / A := by
          rw [pow_succ]
          field_simp
  have hfin : |C| * 2 ^ n * Ck * X / A * 4 ≤ θ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hApos]
    have hMθ : M * θ = 4 * |C| * Ck * X * 2 ^ n := by
      rw [hM]
      field_simp
    have hMA : M ≤ A := by linarith
    have hθA : M * θ ≤ A * θ := mul_le_mul_of_nonneg_right hMA hθ.le
    nlinarith
  refine ⟨T, by linarith, hTpos, fun ρ hρ => hz ρ hρ.1 hρ.2.1 hρ.2.2, ?_⟩
  calc ‖HIntegral (EF.Psi χ Φ x) (-1 / 2) (3 / 2) (-T) -
        HIntegral (EF.Psi χ Φ x) (-1 / 2) (3 / 2) T‖
      ≤ ‖HIntegral (EF.Psi χ Φ x) (-1 / 2) (3 / 2) (-T)‖ +
        ‖HIntegral (EF.Psi χ Φ x) (-1 / 2) (3 / 2) T‖ := norm_sub_le _ _
    _ ≤ B * 2 + B * 2 := add_le_add hHmT hHT
    _ ≤ |C| * 2 ^ n * Ck * X / A * 4 := by linarith
    _ ≤ θ := hfin

/-- **The spine of `EF.Horizontal`** (composition by application): `AllFactor` (the completed
`L`-functions and `ξ` supply an entire `F` with growth, anchor and `L'/L = F'/F − E`) gives good
heights through the PROVED `landauHeights_holds`, and good heights give `EF.Horizontal`. -/
theorem horizontal_of_allFactor (hF : AllFactor) : EF.Horizontal :=
  horizontal_of_good (goodHeights_of_all hF)

/-- **`EF.Horizontal` (EF5) PROVED.** -/
theorem horizontal_holds : EF.Horizontal :=
  horizontal_of_allFactor allFactor_holds

end Principia.Common.TernaryGoldbach.AH
