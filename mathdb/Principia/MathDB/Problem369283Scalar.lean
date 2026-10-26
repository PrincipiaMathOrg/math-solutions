import Mathlib

/-!
# MathDB #369283 — scalar core: superadditivity of real powers on `2 × 2` triples

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/369283/solution.tex` (the generalized Cauchy–Schwarz inequality for
real powers, Conjecture 5.1 of Johnston–Plosker–Torrance–Varona).  The write-up's matrix lemma
`(A+B)^{∘p} ⪰ A^{∘p} + B^{∘p}` for entrywise-nonnegative `2 × 2` positive semidefinite matrices
comes down to the scalar inequality `F_sq`:

`F(√(a₁a₂), √(b₁b₂))² ≤ F(a₁, b₁) F(a₂, b₂)`, where `F(u, v) = (u+v)^p − u^p − v^p`, `p ≥ 2`.

The write-up proves the matrix lemma through a double integral of `(sA+tB)^{∘(p−2)} ∘ A ∘ B`.  Here
the same idea is split into two one-variable integrals: `F(u,v) = ∫₀¹ u p G(λu, v) dλ` with
`G(x,y) = (x+y)^{p−1} − x^{p−1} = ∫₀¹ y (p−1) (x+τy)^{p−2} dτ` (`F_int`, `G_int`), a pointwise
comparison `(√(x₁x₂) + τ√(y₁y₂))² ≤ (x₁+τy₁)(x₂+τy₂)`, and a square-root-free Cauchy–Schwarz
inequality for interval integrals (`cs_int`: `f² ≤ f₁f₂` pointwise gives
`(∫f)² ≤ ∫f₁ ∫f₂`).  `F_mono_left` records the monotonicity used when an off-diagonal entry is
below `√(αβ)`.  The reduction of the vector inequality to this core is the consumer.
-/

namespace Principia.MathDB.P369283

open intervalIntegral Set

/-- `G_q(x, y) = (x+y)^q − x^q`. -/
noncomputable def G (q x y : ℝ) : ℝ := (x + y) ^ q - x ^ q

/-- `F_p(u, v) = (u+v)^p − u^p − v^p`. -/
noncomputable def F (p u v : ℝ) : ℝ := (u + v) ^ p - u ^ p - v ^ p

/-- A square-root-free Cauchy–Schwarz inequality on `[0, 1]`. -/
theorem cs_int (f f1 f2 : ℝ → ℝ) (hc : Continuous f) (hc1 : Continuous f1) (hc2 : Continuous f2)
    (h0 : ∀ τ ∈ Icc (0 : ℝ) 1, 0 ≤ f τ) (h1 : ∀ τ ∈ Icc (0 : ℝ) 1, 0 ≤ f1 τ)
    (h2 : ∀ τ ∈ Icc (0 : ℝ) 1, 0 ≤ f2 τ)
    (hle : ∀ τ ∈ Icc (0 : ℝ) 1, f τ ^ 2 ≤ f1 τ * f2 τ) :
    (∫ τ in (0 : ℝ)..1, f τ) ^ 2 ≤ (∫ τ in (0 : ℝ)..1, f1 τ) * ∫ τ in (0 : ℝ)..1, f2 τ := by
  have hJ : 0 ≤ ∫ τ in (0 : ℝ)..1, f τ := integral_nonneg (by norm_num) h0
  have hI1 : 0 ≤ ∫ τ in (0 : ℝ)..1, f1 τ := integral_nonneg (by norm_num) h1
  have hI2 : 0 ≤ ∫ τ in (0 : ℝ)..1, f2 τ := integral_nonneg (by norm_num) h2
  have key : ∀ t : ℝ, 0 < t → 2 * ∫ τ in (0 : ℝ)..1, f τ
      ≤ t * (∫ τ in (0 : ℝ)..1, f1 τ) + (∫ τ in (0 : ℝ)..1, f2 τ) / t := by
    intro t ht
    have hpt : ∀ τ ∈ Icc (0 : ℝ) 1, 2 * f τ ≤ t * f1 τ + f2 τ / t := by
      intro τ hτ
      have ha : 0 ≤ t * f1 τ := mul_nonneg ht.le (h1 τ hτ)
      have hb : 0 ≤ f2 τ / t := div_nonneg (h2 τ hτ) ht.le
      have hab : f1 τ * f2 τ = (t * f1 τ) * (f2 τ / t) := by
        field_simp
      have hsq := hle τ hτ
      rw [hab] at hsq
      nlinarith [sq_nonneg (t * f1 τ - f2 τ / t), h0 τ hτ]
    have hm : ∫ τ in (0 : ℝ)..1, 2 * f τ ≤ ∫ τ in (0 : ℝ)..1, (t * f1 τ + f2 τ / t) :=
      integral_mono_on (by norm_num) ((hc.const_mul 2).intervalIntegrable 0 1)
        (((hc1.const_mul t).add (hc2.div_const t)).intervalIntegrable 0 1) hpt
    rw [integral_const_mul, integral_add ((hc1.const_mul t).intervalIntegrable 0 1)
      ((hc2.div_const t).intervalIntegrable 0 1), integral_const_mul, integral_div] at hm
    exact hm
  set J := ∫ τ in (0 : ℝ)..1, f τ
  set I1 := ∫ τ in (0 : ℝ)..1, f1 τ
  set I2 := ∫ τ in (0 : ℝ)..1, f2 τ
  rcases eq_or_lt_of_le hJ with hJ0 | hJpos
  · rw [← hJ0]
    nlinarith
  rcases eq_or_lt_of_le hI1 with hI10 | hI1pos
  · exfalso
    have ht : 0 < (I2 + 1) / J := div_pos (by linarith) hJpos
    have hk := key _ ht
    rw [← hI10, mul_zero, zero_add, div_div_eq_mul_div] at hk
    have : I2 * J / (I2 + 1) < J := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  · have hk := key (J / I1) (div_pos hJpos hI1pos)
    have e1 : J / I1 * I1 = J := div_mul_cancel₀ J hI1pos.ne'
    have e2 : I2 / (J / I1) = I2 * I1 / J := by
      field_simp
    rw [e1, e2] at hk
    have h3 : J ≤ I2 * I1 / J := by linarith
    rw [le_div_iff₀ hJpos] at h3
    nlinarith

/-- `G_q(x, y) = ∫₀¹ y q (x + τy)^{q−1} dτ` for `q ≥ 1`. -/
theorem G_int (q x y : ℝ) (hq : 1 ≤ q) :
    G q x y = ∫ τ in (0 : ℝ)..1, y * q * (x + τ * y) ^ (q - 1) := by
  have hd : ∀ τ : ℝ, HasDerivAt (fun τ => (x + τ * y) ^ q) (y * q * (x + τ * y) ^ (q - 1)) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => x + τ * y) y τ := by
      simpa using ((hasDerivAt_id τ).mul_const y).const_add x
    exact h1.rpow_const (Or.inr hq)
  have hcont : Continuous fun τ : ℝ => y * q * (x + τ * y) ^ (q - 1) :=
    continuous_const.mul ((continuous_const.add (continuous_id.mul continuous_const)).rpow_const
      fun _ => Or.inr (by linarith))
  rw [integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ) (hcont.intervalIntegrable 0 1)]
  simp [G]

/-- `F_p(u, v) = ∫₀¹ u p G_{p−1}(λu, v) dλ` for `p ≥ 2`. -/
theorem F_int (p u v : ℝ) (hp : 2 ≤ p) :
    F p u v = ∫ l in (0 : ℝ)..1, u * p * G (p - 1) (l * u) v := by
  have hd : ∀ l : ℝ, HasDerivAt (fun l => (l * u + v) ^ p - (l * u) ^ p)
      (u * p * G (p - 1) (l * u) v) l := by
    intro l
    have h1 : HasDerivAt (fun l : ℝ => l * u + v) u l := by
      simpa using ((hasDerivAt_id l).mul_const u).add_const v
    have h2 : HasDerivAt (fun l : ℝ => l * u) u l := by
      simpa using (hasDerivAt_id l).mul_const u
    refine ((h1.rpow_const (Or.inr (by linarith))).sub
      (h2.rpow_const (Or.inr (by linarith)))).congr_deriv ?_
    simp only [G]
    ring
  have hcont : Continuous fun l : ℝ => u * p * G (p - 1) (l * u) v := by
    unfold G
    exact continuous_const.mul
      ((((continuous_id.mul continuous_const).add continuous_const).rpow_const
        fun _ => Or.inr (by linarith)).sub
      ((continuous_id.mul continuous_const).rpow_const fun _ => Or.inr (by linarith)))
  rw [integral_eq_sub_of_hasDerivAt (fun l _ => hd l) (hcont.intervalIntegrable 0 1)]
  have hp0 : p ≠ 0 := by linarith
  simp [F, Real.zero_rpow hp0]

theorem G_nonneg (q x y : ℝ) (hq : 1 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ G q x y := by
  unfold G
  have := Real.rpow_le_rpow hx (by linarith : x ≤ x + y) (by linarith : (0 : ℝ) ≤ q)
  linarith

/-- The pointwise comparison `(√(x₁x₂) + τ√(y₁y₂))² ≤ (x₁+τy₁)(x₂+τy₂)`. -/
theorem sq_le_prod (x1 x2 y1 y2 τ : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1)
    (hy2 : 0 ≤ y2) (hτ : 0 ≤ τ) :
    (Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2)) ^ 2 ≤ (x1 + τ * y1) * (x2 + τ * y2) := by
  have hs1 := Real.sq_sqrt (mul_nonneg hx1 hx2)
  have hs2 := Real.sq_sqrt (mul_nonneg hy1 hy2)
  have hn1 := Real.sqrt_nonneg (x1 * x2)
  have hn2 := Real.sqrt_nonneg (y1 * y2)
  have hcross : 2 * (Real.sqrt (x1 * x2) * Real.sqrt (y1 * y2)) ≤ x1 * y2 + x2 * y1 := by
    have hprod : (Real.sqrt (x1 * x2) * Real.sqrt (y1 * y2)) ^ 2 = (x1 * y2) * (x2 * y1) := by
      rw [mul_pow, hs1, hs2]
      ring
    nlinarith [sq_nonneg (x1 * y2 - x2 * y1), mul_nonneg hn1 hn2, mul_nonneg hx1 hy2,
      mul_nonneg hx2 hy1]
  nlinarith [mul_nonneg hτ (mul_nonneg hn1 hn2), sq_nonneg τ]

/-- `G_q(√(x₁x₂), √(y₁y₂))² ≤ G_q(x₁, y₁) G_q(x₂, y₂)` for `q ≥ 1`. -/
theorem G_sq (q x1 x2 y1 y2 : ℝ) (hq : 1 ≤ q) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1)
    (hy2 : 0 ≤ y2) :
    G q (Real.sqrt (x1 * x2)) (Real.sqrt (y1 * y2)) ^ 2 ≤ G q x1 y1 * G q x2 y2 := by
  rw [G_int q _ _ hq, G_int q x1 y1 hq, G_int q x2 y2 hq]
  have hr : 0 ≤ q - 1 := by linarith
  have hcont : ∀ a b : ℝ, Continuous fun τ : ℝ => b * q * (a + τ * b) ^ (q - 1) := fun a b =>
    continuous_const.mul ((continuous_const.add (continuous_id.mul continuous_const)).rpow_const
      fun _ => Or.inr hr)
  apply cs_int _ _ _ (hcont _ _) (hcont _ _) (hcont _ _)
  · intro τ hτ
    have hb : 0 ≤ Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2) :=
      add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hτ.1 (Real.sqrt_nonneg _))
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (Real.rpow_nonneg hb _)
  · intro τ hτ
    exact mul_nonneg (mul_nonneg hy1 (by linarith))
      (Real.rpow_nonneg (add_nonneg hx1 (mul_nonneg hτ.1 hy1)) _)
  · intro τ hτ
    exact mul_nonneg (mul_nonneg hy2 (by linarith))
      (Real.rpow_nonneg (add_nonneg hx2 (mul_nonneg hτ.1 hy2)) _)
  · intro τ hτ
    have hB : 0 ≤ Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2) :=
      add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hτ.1 (Real.sqrt_nonneg _))
    have hC1 : 0 ≤ x1 + τ * y1 := add_nonneg hx1 (mul_nonneg hτ.1 hy1)
    have hC2 : 0 ≤ x2 + τ * y2 := add_nonneg hx2 (mul_nonneg hτ.1 hy2)
    have hpow : ((Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2)) ^ (q - 1)) ^ 2
        ≤ (x1 + τ * y1) ^ (q - 1) * (x2 + τ * y2) ^ (q - 1) := by
      rw [← Real.mul_rpow hC1 hC2, sq, ← Real.mul_rpow hB hB]
      exact Real.rpow_le_rpow (mul_nonneg hB hB)
        (by rw [← sq]; exact sq_le_prod x1 x2 y1 y2 τ hx1 hx2 hy1 hy2 hτ.1) hr
    have hy : Real.sqrt (y1 * y2) ^ 2 = y1 * y2 := Real.sq_sqrt (mul_nonneg hy1 hy2)
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    calc (Real.sqrt (y1 * y2) * q * (Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2)) ^ (q - 1)) ^ 2
        = (y1 * y2 * q ^ 2) * ((Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2)) ^ (q - 1)) ^ 2 := by
          linear_combination
            (q ^ 2 * ((Real.sqrt (x1 * x2) + τ * Real.sqrt (y1 * y2)) ^ (q - 1)) ^ 2) * hy
      _ ≤ (y1 * y2 * q ^ 2) * ((x1 + τ * y1) ^ (q - 1) * (x2 + τ * y2) ^ (q - 1)) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hy1 hy2) hq2)
      _ = y1 * q * (x1 + τ * y1) ^ (q - 1) * (y2 * q * (x2 + τ * y2) ^ (q - 1)) := by ring

/-- **The scalar core:** `F_p(√(a₁a₂), √(b₁b₂))² ≤ F_p(a₁, b₁) F_p(a₂, b₂)` for `p ≥ 2`. -/
theorem F_sq (p a1 a2 b1 b2 : ℝ) (hp : 2 ≤ p) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1)
    (hb2 : 0 ≤ b2) :
    F p (Real.sqrt (a1 * a2)) (Real.sqrt (b1 * b2)) ^ 2 ≤ F p a1 b1 * F p a2 b2 := by
  rw [F_int p _ _ hp, F_int p a1 b1 hp, F_int p a2 b2 hp]
  have hq : 1 ≤ p - 1 := by linarith
  have hcont : ∀ u v : ℝ, Continuous fun l : ℝ => u * p * G (p - 1) (l * u) v := by
    intro u v
    unfold G
    exact continuous_const.mul
      ((((continuous_id.mul continuous_const).add continuous_const).rpow_const
        fun _ => Or.inr (by linarith)).sub
      ((continuous_id.mul continuous_const).rpow_const fun _ => Or.inr (by linarith)))
  apply cs_int _ _ _ (hcont _ _) (hcont _ _) (hcont _ _)
  · intro l hl
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
      (G_nonneg _ _ _ hq (mul_nonneg hl.1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · intro l hl
    exact mul_nonneg (mul_nonneg ha1 (by linarith)) (G_nonneg _ _ _ hq (mul_nonneg hl.1 ha1) hb1)
  · intro l hl
    exact mul_nonneg (mul_nonneg ha2 (by linarith)) (G_nonneg _ _ _ hq (mul_nonneg hl.1 ha2) hb2)
  · intro l hl
    have hsq : Real.sqrt ((l * a1) * (l * a2)) = l * Real.sqrt (a1 * a2) := by
      rw [show (l * a1) * (l * a2) = l * l * (a1 * a2) by ring, Real.sqrt_mul (mul_self_nonneg l),
        Real.sqrt_mul_self hl.1]
    have hG := G_sq (p - 1) (l * a1) (l * a2) b1 b2 hq (mul_nonneg hl.1 ha1)
      (mul_nonneg hl.1 ha2) hb1 hb2
    rw [hsq] at hG
    have ha : Real.sqrt (a1 * a2) ^ 2 = a1 * a2 := Real.sq_sqrt (mul_nonneg ha1 ha2)
    calc (Real.sqrt (a1 * a2) * p * G (p - 1) (l * Real.sqrt (a1 * a2)) (Real.sqrt (b1 * b2))) ^ 2
        = (a1 * a2 * p ^ 2) * G (p - 1) (l * Real.sqrt (a1 * a2)) (Real.sqrt (b1 * b2)) ^ 2 := by
          linear_combination
            (p ^ 2 * G (p - 1) (l * Real.sqrt (a1 * a2)) (Real.sqrt (b1 * b2)) ^ 2) * ha
      _ ≤ (a1 * a2 * p ^ 2) * (G (p - 1) (l * a1) b1 * G (p - 1) (l * a2) b2) :=
          mul_le_mul_of_nonneg_left hG (mul_nonneg (mul_nonneg ha1 ha2) (sq_nonneg p))
      _ = a1 * p * G (p - 1) (l * a1) b1 * (a2 * p * G (p - 1) (l * a2) b2) := by ring

/-- `F_p` is nondecreasing in its first argument on `[0, ∞)`. -/
theorem F_mono_left (p u u' v : ℝ) (hp : 2 ≤ p) (hu : 0 ≤ u) (huu : u ≤ u') (hv : 0 ≤ v) :
    F p u v ≤ F p u' v := by
  rw [F_int p u v hp, F_int p u' v hp]
  have hq : 1 ≤ p - 1 := by linarith
  have hcont : ∀ w : ℝ, Continuous fun l : ℝ => w * p * G (p - 1) (l * w) v := by
    intro w
    unfold G
    exact continuous_const.mul
      ((((continuous_id.mul continuous_const).add continuous_const).rpow_const
        fun _ => Or.inr (by linarith)).sub
      ((continuous_id.mul continuous_const).rpow_const fun _ => Or.inr (by linarith)))
  refine integral_mono_on (by norm_num) ((hcont u).intervalIntegrable 0 1)
    ((hcont u').intervalIntegrable 0 1) fun l hl => ?_
  have hxl : l * u ≤ l * u' := mul_le_mul_of_nonneg_left huu hl.1
  have hGmono : G (p - 1) (l * u) v ≤ G (p - 1) (l * u') v := by
    rw [G_int (p - 1) (l * u) v hq, G_int (p - 1) (l * u') v hq]
    have hr : 0 ≤ p - 1 - 1 := by linarith
    refine integral_mono_on (by norm_num)
      ((continuous_const.mul ((continuous_const.add (continuous_id.mul continuous_const)).rpow_const
        fun _ => Or.inr hr)).intervalIntegrable 0 1)
      ((continuous_const.mul ((continuous_const.add (continuous_id.mul continuous_const)).rpow_const
        fun _ => Or.inr hr)).intervalIntegrable 0 1) fun τ hτ => ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (add_nonneg (mul_nonneg hl.1 hu) (mul_nonneg hτ.1 hv)) (by linarith) hr)
      (mul_nonneg hv (by linarith))
  have hG0 := G_nonneg (p - 1) (l * u) v hq (mul_nonneg hl.1 hu) hv
  have hp0 : 0 ≤ p := by linarith
  calc u * p * G (p - 1) (l * u) v ≤ u' * p * G (p - 1) (l * u) v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right huu hp0) hG0
    _ ≤ u' * p * G (p - 1) (l * u') v :=
        mul_le_mul_of_nonneg_left hGmono (mul_nonneg (hu.trans huu) hp0)

end Principia.MathDB.P369283
