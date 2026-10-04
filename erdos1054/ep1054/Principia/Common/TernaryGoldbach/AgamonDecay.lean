/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonCont

set_option autoImplicit false

/-!
# `EF.MollDecay` PROVED: `Φ_ε = G_cont·Mν(ε·)` decays faster than every power on the strip

**`mollDecay_holds : EF.MollDecay`**, with no hypothesis. Route (the link's docstring):
* `G_cont` is bounded on `−1/2 ≤ Re s ≤ 3/2` (`gcont_bounded`):
  `|M f(s)| ≤ ∫(t^{1/2} + t^{−1/2})|f|` for `Re s ≥ 1/2`; `G_cont(s) = −M f'(s + 1)/s`
  (`AG.gcont_eq_dslope`) with `|s| ≥ 1` for `Re s < 1/2`, `|Im s| ≥ 1`; and continuity
  (`AG.continuation_holds`) on the compact rectangle `[−1/2, 1/2] × [−1, 1]`;
* `Mν` decays like `|w|^{−k}` for every `k`, uniformly on `|Re w| ≤ R` (`mnu_decay`): with
  `θφ(t) = t φ'(t)`, `w·Mφ(w) = −M(θφ)(w)` for `w ≠ 0` (PNT+ `MellinOfPsi_aux`, one integration by
  parts), so `w^k Mν(w) = (−1)^k M(θ^k ν)(w)` (`mellin_thetaPow`), and
  `|Mψ(w)| ≤ 2^{|Re w|}∫|ψ(t)|dt/t` for `ψ` supported in `[1/2, 2]` (`norm_mellin_supp_le`);
* `1 + |Im s| ≤ (1 + 1/ε)(1 + |εs|)` and `(1 + r)^k ≤ 2^k(1 + r^k)`.

PNT+ `MellinOfPsi` is the case `k = 1` of `mnu_decay`. No falsification: the link is TRUE as stated
(any `ε > 0`; `C` depends on `η, δ, ν, ε, k`, as the existential allows).
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF
open scoped ContDiff

/-! ## (1) `G_cont` is bounded on the strip -/

/-- **`G_cont` is bounded on `−1/2 ≤ Re s ≤ 3/2`.** -/
theorem gcont_bounded {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (h0 : η 0 = 0) (δ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Gcont η δ s‖ ≤ B := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := agamon_strip hreg δ
  have hi1 := hab (1 / 2) ⟨by linarith, by linarith⟩
  have hi3 := hab (3 / 2) ⟨by linarith, by linarith⟩
  set B1 := ∫ t in Ioi (0 : ℝ), (t ^ ((3 / 2 : ℝ) - 1) * ‖fw η δ t‖ +
    t ^ ((1 / 2 : ℝ) - 1) * ‖fw η δ t‖) with hB1
  set B2 := ∫ t in Ioi (0 : ℝ), (t ^ ((3 / 2 : ℝ) - 1) * ‖deriv (fw η δ) t‖ +
    t ^ ((1 / 2 : ℝ) - 1) * ‖deriv (fw η δ) t‖) with hB2
  -- the compact rectangle
  obtain ⟨b', hb', hdiff⟩ := continuation_holds η hreg h0 δ
  set K : Set ℂ := Icc (-1 / 2 : ℝ) (1 / 2) ×ℂ Icc (-1 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : K ⊆ {s : ℂ | -1 < s.re ∧ s.re < b'} := by
    intro s hs
    rw [hK, Complex.mem_reProdIm] at hs
    exact ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  obtain ⟨B3, hB3⟩ := hKc.exists_bound_of_continuousOn (hdiff.continuousOn.mono hKsub)
  refine ⟨max 0 (max B1 (max B2 B3)), le_max_left _ _, fun s hs1 hs2 => ?_⟩
  by_cases hre : 1 / 2 ≤ s.re
  · have hpos : 0 < s.re := by linarith
    have e : Gcont η δ s = HM.Gm η δ s := by unfold Gcont; rw [if_pos hpos]
    rw [e, gm_eq]
    have h := norm_mellin_le_two (f := fw η δ) hre hs2 hi1.1 hi3.1
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [not_le] at hre
    by_cases him : 1 ≤ |s.im|
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, Complex.zero_im, abs_zero] at him
        linarith
      have hnorm : 1 ≤ ‖s‖ := him.trans (Complex.abs_im_le_norm s)
      rw [gcont_eq_dslope hreg h0 δ hre, dslope_of_ne _ hs0, slope_def_field,
        fd_zero hreg h0 δ, sub_zero, sub_zero, norm_neg, norm_div]
      have hre1 : (s + 1).re = s.re + 1 := by simp
      have hF : ‖Fd η δ s‖ ≤ B2 := norm_mellin_le_two (f := deriv (fw η δ))
        (show (1 / 2 : ℝ) ≤ (s + 1).re by rw [hre1]; linarith)
        (show (s + 1).re ≤ 3 / 2 by rw [hre1]; linarith) hi1.2 hi3.2
      have hB2 : 0 ≤ B2 := (norm_nonneg _).trans hF
      calc ‖Fd η δ s‖ / ‖s‖ ≤ ‖Fd η δ s‖ / 1 :=
            div_le_div_of_nonneg_left (norm_nonneg _) one_pos hnorm
        _ ≤ B2 := by rw [div_one]; exact hF
        _ ≤ _ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · rw [not_le] at him
      have hsK : s ∈ K := by
        rw [hK, Complex.mem_reProdIm]
        exact ⟨⟨hs1, hre.le⟩, ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩⟩
      exact (hB3 s hsK).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))

/-! ## (2) `Mν` decays faster than every power -/

/-- `θφ(t) = t φ'(t)`. -/
noncomputable def theta (φ : ℝ → ℝ) (t : ℝ) : ℝ := t * deriv φ t

/-- `θ^k φ`. -/
noncomputable def thetaPow (φ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => φ
  | k + 1 => theta (thetaPow φ k)

/-- `θ` preserves smoothness and support in `[1/2, 2]`. -/
theorem theta_props {φ : ℝ → ℝ} (h1 : ContDiff ℝ ∞ φ) (h2 : Function.support φ ⊆ Icc (1 / 2) 2) :
    ContDiff ℝ ∞ (theta φ) ∧ Function.support (theta φ) ⊆ Icc (1 / 2) 2 := by
  refine ⟨contDiff_id.mul (contDiff_infty_iff_deriv.mp h1).2, ?_⟩
  refine (Function.support_mul_subset_right _ _).trans ?_
  exact Function.support_deriv_subset_Icc h2

/-- `θ^k φ` is smooth with support in `[1/2, 2]`. -/
theorem thetaPow_props {φ : ℝ → ℝ} (h1 : ContDiff ℝ ∞ φ)
    (h2 : Function.support φ ⊆ Icc (1 / 2) 2) (k : ℕ) :
    ContDiff ℝ ∞ (thetaPow φ k) ∧ Function.support (thetaPow φ k) ⊆ Icc (1 / 2) 2 := by
  induction k with
  | zero => exact ⟨h1, h2⟩
  | succ k ih => exact theta_props ih.1 ih.2

/-- **`w·Mφ(w) = −M(θφ)(w)`** for `w ≠ 0` (PNT+ `MellinOfPsi_aux`). -/
theorem mellin_theta {φ : ℝ → ℝ} (h1 : ContDiff ℝ 1 φ) (h2 : Function.support φ ⊆ Icc (1 / 2) 2)
    {w : ℂ} (hw : w ≠ 0) : w * mellin (nuC φ) w = -mellin (nuC (theta φ)) w := by
  have h := MellinOfPsi_aux h1 h2 hw
  have eL : mellin (nuC φ) w = ∫ x in Ioi (0 : ℝ), (φ x : ℂ) * (x : ℂ) ^ (w - 1) := by
    unfold mellin nuC
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [smul_eq_mul, mul_comm]
  have eR : mellin (nuC (theta φ)) w =
      ∫ x in Ioi (0 : ℝ), ((deriv φ x : ℝ) : ℂ) * (x : ℂ) ^ w := by
    unfold mellin nuC theta
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    rw [smul_eq_mul, Complex.cpow_sub _ _ hx', Complex.cpow_one]
    push_cast
    field_simp
  rw [eL, eR, h]
  field_simp

/-- **`w^k Mν(w) = (−1)^k M(θ^k ν)(w)`** for `w ≠ 0`. -/
theorem mellin_thetaPow {φ : ℝ → ℝ} (h1 : ContDiff ℝ ∞ φ)
    (h2 : Function.support φ ⊆ Icc (1 / 2) 2) {w : ℂ} (hw : w ≠ 0) (k : ℕ) :
    w ^ k * mellin (nuC φ) w = (-1) ^ k * mellin (nuC (thetaPow φ k)) w := by
  induction k with
  | zero => simp [thetaPow]
  | succ k ih =>
    have hp := thetaPow_props h1 h2 k
    have ht := mellin_theta (hp.1.of_le (by simp)) hp.2 hw
    calc w ^ (k + 1) * mellin (nuC φ) w = w * (w ^ k * mellin (nuC φ) w) := by ring
      _ = w * ((-1) ^ k * mellin (nuC (thetaPow φ k)) w) := by rw [ih]
      _ = (-1) ^ k * (w * mellin (nuC (thetaPow φ k)) w) := by ring
      _ = (-1) ^ (k + 1) * mellin (nuC (thetaPow φ (k + 1))) w := by
          rw [ht, thetaPow]
          ring

/-- `|ψ|/t ∈ L¹(0, ∞)` for `ψ` continuous with support in `[1/2, 2]`. -/
theorem integrableOn_abs_div {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hs : Function.support ψ ⊆ Icc (1 / 2) 2) :
    IntegrableOn (fun t => |ψ t| / t) (Ioi 0) := by
  have h1 : IntegrableOn (fun t => |ψ t| / t) (Icc (1 / 2) 2) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    exact (hc.abs.continuousAt.div continuousAt_id (ne_of_gt ht')).continuousWithinAt
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht => ?_
  have h0 : ψ t = 0 := by
    by_contra hne
    exact ht.2 (hs hne)
  simp [h0]

/-- **`|Mψ(w)| ≤ 2^{|Re w|}∫|ψ(t)|dt/t`** for `ψ` continuous with support in `[1/2, 2]`. -/
theorem norm_mellin_supp_le {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hs : Function.support ψ ⊆ Icc (1 / 2) 2) (w : ℂ) :
    ‖mellin (nuC ψ) w‖ ≤ 2 ^ |w.re| * ∫ t in Ioi (0 : ℝ), |ψ t| / t := by
  have hint := integrableOn_abs_div hc hs
  have hb : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (w - 1) • nuC ψ t‖ ≤ 2 ^ |w.re| * (|ψ t| / t) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', nuC, Complex.norm_real,
      Real.norm_eq_abs, Complex.sub_re, Complex.one_re, Real.rpow_sub_one ht'.ne']
    by_cases h0 : ψ t = 0
    · rw [h0]
      simp
    · have hmem : t ∈ Icc (1 / 2 : ℝ) 2 := hs h0
      have h3 := rpow_le_two_rpow_abs (σ := w.re) hmem
      calc t ^ w.re / t * |ψ t| = t ^ w.re * (|ψ t| / t) := by ring
        _ ≤ 2 ^ |w.re| * (|ψ t| / t) :=
            mul_le_mul_of_nonneg_right h3 (div_nonneg (abs_nonneg _) ht'.le)
  unfold mellin
  calc ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • nuC ψ t‖
      ≤ ∫ t in Ioi (0 : ℝ), 2 ^ |w.re| * (|ψ t| / t) :=
        norm_integral_le_of_norm_le (hint.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hb))
    _ = 2 ^ |w.re| * ∫ t in Ioi (0 : ℝ), |ψ t| / t := by rw [integral_const_mul]

/-- `(1 + r)^k ≤ 2^k(1 + r^k)` for `r ≥ 0`. -/
theorem one_add_pow_le {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : (1 + r) ^ k ≤ 2 ^ k * (1 + r ^ k) := by
  rcases le_or_gt r 1 with h | h
  · have h1 : (1 + r) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have h2 : 0 ≤ r ^ k := pow_nonneg hr k
    have h3 : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith
  · have h1 : (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    rw [mul_pow] at h1
    have h3 : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith

/-- **`Mν(w) = O_k((1 + |w|)^{−k})` uniformly on `|Re w| ≤ R`.** -/
theorem mnu_decay {ν : ℝ → ℝ} (hν : MollData ν) (R : ℝ) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, |w.re| ≤ R → (1 + ‖w‖) ^ k * ‖Mnu ν w‖ ≤ A := by
  have hp0 := thetaPow_props hν.1 hν.2.2.1 0
  have hpk := thetaPow_props hν.1 hν.2.2.1 k
  set A0 := ∫ t in Ioi (0 : ℝ), |thetaPow ν 0 t| / t with hA0
  set Ak := ∫ t in Ioi (0 : ℝ), |thetaPow ν k t| / t with hAk
  have hA0n : 0 ≤ A0 := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    div_nonneg (abs_nonneg _) (le_of_lt ht)
  have hAkn : 0 ≤ Ak := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    div_nonneg (abs_nonneg _) (le_of_lt ht)
  have h2R : (0 : ℝ) ≤ 2 ^ R := by positivity
  refine ⟨2 ^ k * (2 ^ R * A0 + 2 ^ R * Ak), by positivity, fun w hw => ?_⟩
  have hpow : (2 : ℝ) ^ |w.re| ≤ 2 ^ R := Real.rpow_le_rpow_of_exponent_le (by norm_num) hw
  -- `|Mν(w)| ≤ 2^R A₀`
  have hM0 : ‖Mnu ν w‖ ≤ 2 ^ R * A0 := by
    have h := norm_mellin_supp_le hp0.1.continuous hp0.2 w
    rw [show thetaPow ν 0 = ν from rfl] at h
    exact h.trans (mul_le_mul_of_nonneg_right hpow hA0n)
  -- `|w|^k |Mν(w)| ≤ 2^R A_k`
  have hMk : ‖w‖ ^ k * ‖Mnu ν w‖ ≤ 2 ^ R * Ak := by
    by_cases hw0 : w = 0
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [pow_zero, one_mul]
        exact hM0
      · rw [hw0, norm_zero, zero_pow hk.ne', zero_mul]
        positivity
    · have hid := mellin_thetaPow hν.1 hν.2.2.1 hw0 k
      have h := norm_mellin_supp_le hpk.1.continuous hpk.2 w
      calc ‖w‖ ^ k * ‖Mnu ν w‖ = ‖w ^ k * mellin (nuC ν) w‖ := by
            rw [norm_mul, norm_pow, Mnu]
        _ = ‖mellin (nuC (thetaPow ν k)) w‖ := by
            rw [hid, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        _ ≤ 2 ^ |w.re| * Ak := h
        _ ≤ 2 ^ R * Ak := mul_le_mul_of_nonneg_right hpow hAkn
  have hk := one_add_pow_le (norm_nonneg w) k
  calc (1 + ‖w‖) ^ k * ‖Mnu ν w‖ ≤ 2 ^ k * (1 + ‖w‖ ^ k) * ‖Mnu ν w‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ = 2 ^ k * (‖Mnu ν w‖ + ‖w‖ ^ k * ‖Mnu ν w‖) := by ring
    _ ≤ 2 ^ k * (2 ^ R * A0 + 2 ^ R * Ak) := by gcongr

/-! ## (3) `MollDecay` -/

/-- **`EF.MollDecay` HOLDS.** -/
theorem mollDecay_holds : MollDecay := by
  intro η hreg h0 ν hν ε hε δ k
  obtain ⟨B, hB0, hB⟩ := gcont_bounded hreg h0 δ
  obtain ⟨A, hA0, hA⟩ := mnu_decay hν (3 / 2 * ε) k
  set c : ℝ := 1 + 1 / ε with hc
  have hc0 : 0 < c := by positivity
  refine ⟨B * A * c ^ k, fun s hs1 hs2 => ?_⟩
  have hw : |((ε : ℂ) * s).re| ≤ 3 / 2 * ε := by
    have hre : ((ε : ℂ) * s).re = ε * s.re := by simp
    rw [hre, abs_mul, abs_of_pos hε]
    have : |s.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, hs2⟩
    nlinarith
  have hMA := hA _ hw
  have hnw : ‖(ε : ℂ) * s‖ = ε * ‖s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  -- `1 + |Im s| ≤ c (1 + |εs|)`
  have hcmp : 1 + |s.im| ≤ c * (1 + ‖(ε : ℂ) * s‖) := by
    rw [hnw, hc]
    have h1 := Complex.abs_im_le_norm s
    have h2 : 0 ≤ ‖s‖ := norm_nonneg s
    have h3 : (1 / ε) * (ε * ‖s‖) = ‖s‖ := by field_simp
    nlinarith [one_div_pos.mpr hε]
  have hpos : 0 < (1 + |s.im|) ^ k := by positivity
  rw [le_div_iff₀ hpos]
  have hG := hB s hs1 hs2
  have hpk : (1 + |s.im|) ^ k ≤ c ^ k * (1 + ‖(ε : ℂ) * s‖) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hcmp k
  calc ‖Phi η δ ν ε s‖ * (1 + |s.im|) ^ k
      = ‖Gcont η δ s‖ * ‖Mnu ν (ε * s)‖ * (1 + |s.im|) ^ k := by rw [Phi, norm_mul]
    _ ≤ B * ‖Mnu ν (ε * s)‖ * (c ^ k * (1 + ‖(ε : ℂ) * s‖) ^ k) := by gcongr
    _ = B * c ^ k * ((1 + ‖(ε : ℂ) * s‖) ^ k * ‖Mnu ν (ε * s)‖) := by ring
    _ ≤ B * c ^ k * A := by gcongr
    _ = B * A * c ^ k := by ring

end Principia.Common.TernaryGoldbach.AG
