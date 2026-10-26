import Mathlib

/-!
# MathDB #398865 — a symmetric cubic whose zero set in the bidisk is connected and off the diagonal

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/398865/solution.tex`, answering Khavinson's request (p. 381 of the
source): find a symmetric polynomial `P(z₁, z₂)` whose zero set in the bidisk `𝔻²` is nonempty and
connected but does not meet the diagonal `{(z, z)}`.

**What is proved.**  For `P(z₁, z₂) = (z₁ + z₂)(z₁ − z₂)² − 1/2`: `P` is symmetric,
`P(z, z) ≠ 0` for EVERY `z ∈ ℂ`, and `V = {P = 0} ∩ 𝔻²` is nonempty and PATH-connected (hence
connected) — `khavinson`.  **Not formalized:** the write-up's minimality proposition (no symmetric
polynomial of degree ≤ 2 works), which needs holomorphic square roots on the disk.

**Route (the write-up's).**  With `u = (z₁ + z₂)/2`, `w = (z₁ − z₂)/2`, `P = 0` reads `uw² = 1/16`,
so `V` is the image of `Ω = {w ≠ 0 : |1/(16w²) + w| < 1, |1/(16w²) − w| < 1}` under the continuous
map `Φ(w) = (1/(16w²) + w, 1/(16w²) − w)` (`V_eq`).  Along the ray `t ↦ tw` (`t > 0`),
`|1/(16(tw)²) ± tw|² = t²|w|² + 1/(256t⁴|w|⁴) ± k/(8t)` with `k = Re(w̄/w²)`, `|k| ≤ 1/|w|`
(`sq_norm_pm`), so `tw ∈ Ω` iff `H(t) = t²|w|² + 1/(256t⁴|w|⁴) + |k|/(8t) < 1`
(`mem_Om_iff`).  `H` is convex on `t > 0`, so the radial segment from `w` to the circle
`|w| = 1/2` stays in `Ω` (`segment_sub`), and that circle lies in `Ω` because there
`H ≤ 1/4 + 1/16 + 1/4`.  Joining two points through their radial segments and the circle gives
path-connectedness of `Ω`, hence of `V`.
-/

namespace Principia.MathDB.P398865

open Complex

/-- The polynomial `P(z₁, z₂) = (z₁ + z₂)(z₁ − z₂)² − 1/2`. -/
noncomputable def P (z₁ z₂ : ℂ) : ℂ := (z₁ + z₂) * (z₁ - z₂) ^ 2 - 1 / 2

/-- Its zero set in the open bidisk. -/
def V : Set (ℂ × ℂ) := {p | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1 ∧ P p.1 p.2 = 0}

theorem P_symm (z₁ z₂ : ℂ) : P z₁ z₂ = P z₂ z₁ := by
  unfold P
  ring

theorem P_diag (z : ℂ) : P z z ≠ 0 := by
  unfold P
  norm_num

/-- The parametrization `Φ(w) = (1/(16w²) + w, 1/(16w²) − w)`. -/
noncomputable def Phi (w : ℂ) : ℂ × ℂ := ((1 / 16) / w ^ 2 + w, (1 / 16) / w ^ 2 - w)

/-- The parameter set. -/
def Om : Set ℂ := {w | w ≠ 0 ∧ ‖(1 / 16) / w ^ 2 + w‖ < 1 ∧ ‖(1 / 16) / w ^ 2 - w‖ < 1}

theorem V_eq : V = Phi '' Om := by
  ext ⟨z₁, z₂⟩
  simp only [V, Om, Phi, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h0⟩
    have hw : (z₁ - z₂) / 2 ≠ 0 := by
      intro hw
      have hz : z₁ = z₂ := by linear_combination 2 * hw
      subst hz
      exact P_diag _ h0
    have key : (1 / 16) / ((z₁ - z₂) / 2) ^ 2 = (z₁ + z₂) / 2 := by
      rw [div_eq_iff (pow_ne_zero 2 hw)]
      unfold P at h0
      linear_combination (-1 / 8) * h0
    refine ⟨(z₁ - z₂) / 2, ⟨hw, ?_, ?_⟩, ?_, ?_⟩
    · rw [key, show (z₁ + z₂) / 2 + (z₁ - z₂) / 2 = z₁ by ring]
      exact h1
    · rw [key, show (z₁ + z₂) / 2 - (z₁ - z₂) / 2 = z₂ by ring]
      exact h2
    · rw [key]
      ring
    · rw [key]
      ring
  · rintro ⟨w, ⟨hw, h1, h2⟩, e1, e2⟩
    subst e1 e2
    refine ⟨h1, h2, ?_⟩
    have hc : (1 / 16) / w ^ 2 * w ^ 2 = (1 / 16 : ℂ) := div_mul_cancel₀ _ (pow_ne_zero 2 hw)
    unfold P
    linear_combination 8 * hc

/-- `k(w) = Re(w̄ / w²)`. -/
noncomputable def kk (w : ℂ) : ℝ := ((starRingEnd ℂ) w / w ^ 2).re

theorem abs_kk_le (w : ℂ) (hw : w ≠ 0) : |kk w| ≤ 1 / ‖w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hn' := hn.ne'
  calc |kk w| ≤ ‖(starRingEnd ℂ) w / w ^ 2‖ := abs_re_le_norm _
    _ = 1 / ‖w‖ := by
      rw [norm_div, norm_pow, Complex.norm_conj, div_eq_div_iff (pow_ne_zero 2 hn') hn']
      ring

/-- The squared norms along a ray. -/
theorem sq_norm_pm (w : ℂ) (hw : w ≠ 0) (t : ℝ) (ht : 0 < t) :
    ‖(1 / 16) / ((t : ℂ) * w) ^ 2 + (t : ℂ) * w‖ ^ 2
        = t ^ 2 * ‖w‖ ^ 2 + 1 / (256 * t ^ 4 * ‖w‖ ^ 4) + kk w / (8 * t) ∧
      ‖(1 / 16) / ((t : ℂ) * w) ^ 2 - (t : ℂ) * w‖ ^ 2
        = t ^ 2 * ‖w‖ ^ 2 + 1 / (256 * t ^ 4 * ‖w‖ ^ 4) - kk w / (8 * t) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hn' := hn.ne'
  have htr := ht.ne'
  have hxx : ‖(1 / 16 : ℂ) / ((t : ℂ) * w) ^ 2‖ ^ 2 = 1 / (256 * t ^ 4 * ‖w‖ ^ 4) := by
    rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le,
      show ‖(1 / 16 : ℂ)‖ = 1 / 16 by norm_num [norm_div]]
    ring
  have hyy : ‖(t : ℂ) * w‖ ^ 2 = t ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    ring
  have hxy : (1 / 16 : ℂ) / ((t : ℂ) * w) ^ 2 * (starRingEnd ℂ) ((t : ℂ) * w)
      = ((1 / (16 * t) : ℝ) : ℂ) * ((starRingEnd ℂ) w / w ^ 2) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    field_simp
    try ring
  have hre : ((1 / 16 : ℂ) / ((t : ℂ) * w) ^ 2 * (starRingEnd ℂ) ((t : ℂ) * w)).re
      = kk w / (16 * t) := by
    rw [hxy, Complex.re_ofReal_mul, kk]
    ring
  constructor
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hxx, hyy, hre]
    ring
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hxx, hyy, hre]
    ring

/-- The radial profile `H(t) = t²|w|² + 1/(256t⁴|w|⁴) + |k|/(8t)`. -/
noncomputable def H (w : ℂ) (t : ℝ) : ℝ :=
  t ^ 2 * ‖w‖ ^ 2 + 1 / (256 * t ^ 4 * ‖w‖ ^ 4) + |kk w| / (8 * t)

theorem mem_Om_iff (w : ℂ) (hw : w ≠ 0) (t : ℝ) (ht : 0 < t) : (t : ℂ) * w ∈ Om ↔ H w t < 1 := by
  obtain ⟨e1, e2⟩ := sq_norm_pm w hw t ht
  have hne : (t : ℂ) * w ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') hw
  have hpos : 0 < 8 * t := by linarith
  have c1 := pow_lt_one_iff_of_nonneg
    (norm_nonneg ((1 / 16 : ℂ) / ((t : ℂ) * w) ^ 2 + (t : ℂ) * w)) two_ne_zero
  have c2 := pow_lt_one_iff_of_nonneg
    (norm_nonneg ((1 / 16 : ℂ) / ((t : ℂ) * w) ^ 2 - (t : ℂ) * w)) two_ne_zero
  rw [e1] at c1
  rw [e2] at c2
  have habs : |kk w| / (8 * t) = |kk w / (8 * t)| := by
    rw [abs_div, abs_of_pos hpos]
  simp only [Om, Set.mem_setOf_eq, H, habs]
  constructor
  · rintro ⟨-, h1, h2⟩
    have h1' := c1.2 h1
    have h2' := c2.2 h2
    rcases abs_cases (kk w / (8 * t)) with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  · intro h
    refine ⟨hne, c1.1 ?_, c2.1 ?_⟩
    · linarith [le_abs_self (kk w / (8 * t))]
    · linarith [neg_abs_le (kk w / (8 * t))]

theorem H_convex (w : ℂ) : ConvexOn ℝ (Set.Ioi 0) (H w) := by
  have hc := (((convexOn_pow 2).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).smul
      (sq_nonneg ‖w‖)).add ((convexOn_zpow (-4)).smul
      (by positivity : (0 : ℝ) ≤ 1 / (256 * ‖w‖ ^ 4))) |>.add
      ((convexOn_zpow (-1)).smul (by positivity : (0 : ℝ) ≤ |kk w| / 8))
  have hH : H w = ((fun t : ℝ => ‖w‖ ^ 2 • t ^ 2) + fun t : ℝ =>
      (1 / (256 * ‖w‖ ^ 4)) • t ^ (-4 : ℤ)) + fun t : ℝ => (|kk w| / 8) • t ^ (-1 : ℤ) := by
    funext t
    simp only [Pi.add_apply, smul_eq_mul, H]
    rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_one]
    ring
  rw [hH]
  exact hc

/-- The radial segment from `w ∈ Ω` to the circle `|w| = 1/2` stays in `Ω`. -/
theorem segment_sub (w : ℂ) (hw : w ∈ Om) :
    segment ℝ w (((1 / (2 * ‖w‖) : ℝ) : ℂ) * w) ⊆ Om := by
  have hw0 : w ≠ 0 := hw.1
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hn' := hn.ne'
  set τ : ℝ := 1 / (2 * ‖w‖) with hτ
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have h1 : H w 1 < 1 := (mem_Om_iff w hw0 1 one_pos).1 (by simpa using hw)
  have h2 : H w τ < 1 := by
    have hτw : τ * ‖w‖ = 1 / 2 := by
      rw [hτ]
      field_simp
      try ring
    have hk := abs_kk_le w hw0
    have e1 : τ ^ 2 * ‖w‖ ^ 2 = 1 / 4 := by
      rw [← mul_pow, hτw]
      norm_num
    have e2 : 1 / (256 * τ ^ 4 * ‖w‖ ^ 4) = 1 / 16 := by
      rw [mul_assoc, ← mul_pow, hτw]
      norm_num
    have e3 : |kk w| / (8 * τ) ≤ 1 / 4 := by
      rw [div_le_iff₀ (show (0 : ℝ) < 8 * τ by linarith)]
      calc |kk w| ≤ 1 / ‖w‖ := hk
        _ = 1 / 4 * (8 * τ) := by
          rw [hτ]
          field_simp
          try ring
    unfold H
    linarith
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  have hpos : 0 < a * 1 + b * τ := by
    rcases ha.eq_or_lt with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1]
      linarith
    · nlinarith [mul_nonneg hb hτ0.le]
  have hz : a • w + b • ((τ : ℂ) * w) = ((a * 1 + b * τ : ℝ) : ℂ) * w := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hz, mem_Om_iff w hw0 _ hpos]
  calc H w (a * 1 + b * τ) = H w (a • (1 : ℝ) + b • τ) := by simp only [smul_eq_mul]
    _ ≤ max (H w 1) (H w τ) :=
      (H_convex w).le_on_segment' (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 hτ0) ha hb hab
    _ < 1 := max_lt h1 h2

/-- The circle `|w| = 1/2` lies in `Ω`. -/
theorem sphere_sub : Metric.sphere (0 : ℂ) (1 / 2) ⊆ Om := by
  intro z hz
  rw [Metric.mem_sphere, dist_zero_right] at hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  have hk := abs_kk_le z hz0
  have hmem : ((1 : ℝ) : ℂ) * z ∈ Om := by
    rw [mem_Om_iff z hz0 1 one_pos]
    unfold H
    rw [hz] at hk ⊢
    norm_num at hk ⊢
    linarith
  simpa using hmem

theorem Om_pathConnected : IsPathConnected Om := by
  have hS : IsPathConnected (Metric.sphere (0 : ℂ) (1 / 2)) :=
    isPathConnected_sphere (by rw [Complex.rank_real_complex]; exact_mod_cast (by norm_num : 1 < 2))
      0 (by norm_num)
  have hproj : ∀ w ∈ Om, JoinedIn Om w (((1 / (2 * ‖w‖) : ℝ) : ℂ) * w) ∧
      ((1 / (2 * ‖w‖) : ℝ) : ℂ) * w ∈ Metric.sphere (0 : ℂ) (1 / 2) := by
    intro w hw
    refine ⟨JoinedIn.of_segment_subset (segment_sub w hw), ?_⟩
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw.1
    have hn' := hn.ne'
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ 1 / (2 * ‖w‖) by positivity)]
    field_simp
    try ring
  have h0 : (1 / 2 : ℂ) ∈ Metric.sphere (0 : ℂ) (1 / 2) := by
    rw [Metric.mem_sphere, dist_zero_right]
    norm_num [norm_div]
  refine isPathConnected_iff.2 ⟨⟨1 / 2, sphere_sub h0⟩, fun x hx y hy => ?_⟩
  obtain ⟨jx, sx⟩ := hproj x hx
  obtain ⟨jy, sy⟩ := hproj y hy
  exact jx.trans (((hS.joinedIn _ sx _ sy).mono sphere_sub).trans jy.symm)

theorem V_pathConnected : IsPathConnected V := by
  rw [V_eq]
  refine Om_pathConnected.image' ?_
  have hc : ContinuousOn (fun w : ℂ => (1 / 16 : ℂ) / w ^ 2) Om :=
    continuousOn_const.div (continuous_pow 2).continuousOn fun w hw => pow_ne_zero 2 hw.1
  exact (hc.add continuousOn_id).prodMk (hc.sub continuousOn_id)

/-- **MathDB #398865 (Khavinson's request)**: `P` is symmetric, never vanishes on the diagonal of
`ℂ²`, and its zero set in the bidisk is nonempty and path-connected, hence connected. -/
theorem khavinson :
    (∀ z₁ z₂ : ℂ, P z₁ z₂ = P z₂ z₁) ∧ (∀ z : ℂ, P z z ≠ 0) ∧ V.Nonempty ∧
      IsPathConnected V ∧ IsConnected V :=
  ⟨P_symm, P_diag, V_pathConnected.nonempty, V_pathConnected, V_pathConnected.isConnected⟩

end Principia.MathDB.P398865
