/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMalTail
import Principia.Common.TernaryGoldbach.EasyStar

set_option autoImplicit false

/-!
# `φ(t) = t²e^{−t²/2}`: `HM.PhiReg` PROVED, `HM.PhiNorms` replaced by a proved `PhiNormsL`

**`phiReg_holds : HM.PhiReg`** — `φ` satisfies the hypotheses of `lem:agamon` and `lem:hausierer`
(Gaussian moments `∫₀^∞ t^s e^{−bt²} < ∞`, `s > −1`; `|log t| ≤ t + 1/t`).

**`HM.PhiNorms` is NOT proved at its constants, and this is a FINDING, not a gap in effort.**
Four of its five conjuncts sit within `10⁻⁵` (relative) of their true values, and three of those
true values are not elementary:

| conjunct | stated | true value | closed form | proved here |
|---|---|---|---|---|
| `|φ|₂` | `0.81528` | `0.815273` | `√(3√π/8)` | **`0.81528`** (exact) |
| `|φ'|₂` | `0.88060` | `0.880596` | `√(7√π/16)` | **`0.88060`** (exact) |
| `|φ·log|₂` | `0.40453` | `0.404524` | `√((3√π/32)((8/3−γ−2log2)² + π²/2 − 40/9))` | `0.41312` |
| `|φ/√t|₁` | `1.07791` | `1.077900` | `2^{1/4}Γ(5/4)` | `1.1196` |
| `c₀` | `2.1376 + 10.99|δ|` | `2.13758 + 10.9896|δ|` | `Γ(1/4)`-type | `2.786 + 11.33|δ|` |

`|φ·log|₂² = Γ''(5/2)/8` needs the trigamma value `ψ'(5/2) = π²/2 − 40/9` (Mathlib has `digamma` at
`1/2` and `1` only, no trigamma); the stated `0.40453` has `1.5·10⁻⁵` relative room, below what the
elementary `log²t ≤ t + 1/t − 2` gives (`√(3/2 − 3√π/4) = 0.41311`). `|φ/√t|₁ = 2^{1/4}Γ(5/4)` has
`9·10⁻⁶` room and `Γ(5/4)` has no closed form; the Bohr–Mollerup sandwich would need `~3·10⁴` terms.
These are Helfgott's `eq:drachcat` digits (4000–4014), "obtained by symbolic integration" — a CAS
evaluation of closed forms in `γ`, `log 2`, `π²`, `Γ(1/4)`, `Γ(3/4)`, which this round's brief rules
out citing (bound them instead).

**The consumer does not need them.** `PhiNormsL` (proved: AM–GM against Gaussian moments of
integer order, all `√π`- or `√(2π)`-multiples) carries the loosened constants, and the Cor 1.3
chain is re-derived from it (`phi_errL` → `coprar_wL` → `coprarR_of_linksL`, copies of the spine's
`phi_err` → `coprar_w` → `coprarR_of_links` at the new constants). The retyped target
`MR.CoprarR` still closes: the low-zero term is `384 990/√q + 112.2` (was `379 300/√q + 108`), and
after the `η₂` transfer `528 447/√q + 155.1 ≤ 650 000/√q + 80` for `√q ≤ 548`
(`coprar_closeL`, margin `118 936/√q − 75.1 ≥ 142`).
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set

/-! ## (1) Gaussian moments of integer order -/

/-- `f` is integrable on `(0,∞)` with integral `A`. -/
def GI (f : ℝ → ℝ) (A : ℝ) : Prop := IntegrableOn f (Ioi 0) ∧ ∫ t in Ioi (0 : ℝ), f t = A

theorem gi_lin {f g : ℝ → ℝ} {A B : ℝ} (a b : ℝ) (hf : GI f A) (hg : GI g B) :
    GI (fun t => a * f t + b * g t) (a * A + b * B) := by
  refine ⟨(hf.1.const_mul a).add (hg.1.const_mul b), ?_⟩
  rw [integral_add (hf.1.const_mul a) (hg.1.const_mul b), integral_const_mul, integral_const_mul,
    hf.2, hg.2]

theorem gi_congr {f g : ℝ → ℝ} {A B : ℝ} (hf : GI f A) (hfg : ∀ t : ℝ, 0 < t → f t = g t)
    (hAB : A = B) : GI g B := by
  refine ⟨hf.1.congr_fun (fun t ht => hfg t ht) measurableSet_Ioi, ?_⟩
  rw [← hAB, ← hf.2]
  exact (setIntegral_congr_fun measurableSet_Ioi fun t ht => hfg t ht).symm

/-- `∫₀^∞ tᵏe^{−t²} = Γ((k+1)/2)/2`. -/
theorem gm1 (k : ℕ) : GI (fun t => t ^ k * Real.exp (-t ^ 2)) (Real.Gamma ((k + 1) / 2) / 2) := by
  have hk : (-1 : ℝ) < k := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos hk
  have hv := EN.gauss_moment (k : ℝ) 1 hk one_pos
  simp only [Real.rpow_natCast, neg_mul, one_mul, Real.one_rpow] at hi hv
  exact ⟨hi, by rw [hv]; ring⟩

/-- `∫₀^∞ tᵏe^{−t²/2} = (√2)^{k+1}Γ((k+1)/2)/2` (`t = √2·u`). -/
theorem gm2 (k : ℕ) : GI (fun t => t ^ k * Real.exp (-t ^ 2 / 2))
    (Real.sqrt 2 ^ (k + 1) * (Real.Gamma ((k + 1) / 2) / 2)) := by
  have hk : (-1 : ℝ) < k := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hi0 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) hk
  have hi : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t ^ 2 / 2)) (Ioi 0) :=
    hi0.congr_fun (fun t _ => by
      beta_reduce
      rw [Real.rpow_natCast, show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]) measurableSet_Ioi
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc := integral_comp_mul_left_Ioi (fun t : ℝ => t ^ k * Real.exp (-t ^ 2 / 2)) 0 h2
  rw [mul_zero, smul_eq_mul] at hc
  have he : ∀ x : ℝ, (Real.sqrt 2 * x) ^ k * Real.exp (-(Real.sqrt 2 * x) ^ 2 / 2) =
      Real.sqrt 2 ^ k * (x ^ k * Real.exp (-x ^ 2)) := fun x => by
    rw [mul_pow, mul_pow, hs2, show -(2 * x ^ 2) / 2 = -x ^ 2 by ring]
    ring
  simp only [he] at hc
  rw [integral_const_mul, (gm1 k).2] at hc
  refine ⟨hi, ?_⟩
  have hv : ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-t ^ 2 / 2) =
      Real.sqrt 2 * (Real.sqrt 2 ^ k * (Real.Gamma ((k + 1) / 2) / 2)) := by
    rw [hc, mul_inv_cancel_left₀ h2.ne']
  rw [hv]
  ring

theorem gam_3_2 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

theorem gam_5_2 : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), gam_3_2]
  ring

theorem gam_7_2 : Real.Gamma (7 / 2) = 15 / 8 * Real.sqrt Real.pi := by
  rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), gam_5_2]
  ring

theorem gam_3 : Real.Gamma 3 = 2 := by
  rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]
  norm_num

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `√π ∈ [1.77245, 1.77247]`. -/
theorem sqrt_pi_bounds : 1.77245 ≤ Real.sqrt Real.pi ∧ Real.sqrt Real.pi ≤ 1.77247 :=
  ⟨(Real.le_sqrt (by norm_num) Real.pi_pos.le).mpr (by nlinarith [Real.pi_gt_d6]),
    (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith [Real.pi_lt_d6])⟩

/-- `√2·√π = √(2π) ∈ [2.50662, 2.50663]`. -/
theorem sqrt_2pi_bounds : 2.50662 ≤ Real.sqrt 2 * Real.sqrt Real.pi ∧
    Real.sqrt 2 * Real.sqrt Real.pi ≤ 2.50663 := by
  rw [← Real.sqrt_mul (by norm_num)]
  exact ⟨(Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_d6]),
    (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith [Real.pi_lt_d6])⟩

theorem I2 : GI (fun t => t ^ 2 * Real.exp (-t ^ 2)) (Real.sqrt Real.pi / 4) := by
  have h := gm1 2
  rw [show (((2 : ℕ) : ℝ) + 1) / 2 = 3 / 2 by norm_num, gam_3_2] at h
  exact ⟨h.1, by rw [h.2]; ring⟩

theorem I3 : GI (fun t => t ^ 3 * Real.exp (-t ^ 2)) (1 / 2) := by
  have h := gm1 3
  rw [show (((3 : ℕ) : ℝ) + 1) / 2 = 2 by norm_num, Real.Gamma_two] at h
  exact h

theorem I4 : GI (fun t => t ^ 4 * Real.exp (-t ^ 2)) (3 / 8 * Real.sqrt Real.pi) := by
  have h := gm1 4
  rw [show (((4 : ℕ) : ℝ) + 1) / 2 = 5 / 2 by norm_num, gam_5_2] at h
  exact ⟨h.1, by rw [h.2]; ring⟩

theorem I5 : GI (fun t => t ^ 5 * Real.exp (-t ^ 2)) 1 := by
  have h := gm1 5
  rw [show (((5 : ℕ) : ℝ) + 1) / 2 = 3 by norm_num, gam_3] at h
  exact ⟨h.1, by rw [h.2]; norm_num⟩

theorem I6 : GI (fun t => t ^ 6 * Real.exp (-t ^ 2)) (15 / 16 * Real.sqrt Real.pi) := by
  have h := gm1 6
  rw [show (((6 : ℕ) : ℝ) + 1) / 2 = 7 / 2 by norm_num, gam_7_2] at h
  exact ⟨h.1, by rw [h.2]; ring⟩

theorem M0 : GI (fun t => t ^ 0 * Real.exp (-t ^ 2 / 2))
    (Real.sqrt 2 * Real.sqrt Real.pi / 2) := by
  have h := gm2 0
  rw [show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq] at h
  exact ⟨h.1, by rw [h.2]; ring⟩

theorem M1 : GI (fun t => t ^ 1 * Real.exp (-t ^ 2 / 2)) 1 := by
  have h := gm2 1
  rw [show (((1 : ℕ) : ℝ) + 1) / 2 = 1 by norm_num, Real.Gamma_one] at h
  exact ⟨h.1, by rw [h.2, sqrt2_sq]; norm_num⟩

theorem M2 : GI (fun t => t ^ 2 * Real.exp (-t ^ 2 / 2))
    (Real.sqrt 2 * Real.sqrt Real.pi / 2) := by
  have h := gm2 2
  rw [show (((2 : ℕ) : ℝ) + 1) / 2 = 3 / 2 by norm_num, gam_3_2] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, pow_succ, sqrt2_sq]
  ring

theorem M3 : GI (fun t => t ^ 3 * Real.exp (-t ^ 2 / 2)) 2 := by
  have h := gm2 3
  rw [show (((3 : ℕ) : ℝ) + 1) / 2 = 2 by norm_num, Real.Gamma_two] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, show (3 + 1 : ℕ) = 2 * 2 from rfl, pow_mul, sqrt2_sq]
  norm_num

theorem M4 : GI (fun t => t ^ 4 * Real.exp (-t ^ 2 / 2))
    (3 / 2 * (Real.sqrt 2 * Real.sqrt Real.pi)) := by
  have h := gm2 4
  rw [show (((4 : ℕ) : ℝ) + 1) / 2 = 5 / 2 by norm_num, gam_5_2] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, pow_succ, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrt2_sq]
  ring

theorem M5 : GI (fun t => t ^ 5 * Real.exp (-t ^ 2 / 2)) 8 := by
  have h := gm2 5
  rw [show (((5 : ℕ) : ℝ) + 1) / 2 = 3 by norm_num, gam_3] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, show (5 + 1 : ℕ) = 2 * 3 from rfl, pow_mul, sqrt2_sq]
  norm_num

/-! ## (2) `φ` and `φ'` -/

/-- `e^{−t²/2}² = e^{−t²}`. -/
theorem exp_half_sq (t : ℝ) : Real.exp (-t ^ 2 / 2) ^ 2 = Real.exp (-t ^ 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `φ' = (2t − t³)e^{−t²/2}`. -/
theorem hasDerivAt_phi (t : ℝ) :
    HasDerivAt HW.phi ((2 * t - t ^ 3) * Real.exp (-t ^ 2 / 2)) t := by
  have h1 := EN.hasDerivAt_sq' t
  have h2 := (h1.neg.div_const 2).exp
  refine (h1.mul h2).congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

theorem deriv_phi_eq (t : ℝ) : deriv HW.phi t = (2 * t - t ^ 3) * Real.exp (-t ^ 2 / 2) :=
  (hasDerivAt_phi t).deriv

/-- `|log t| ≤ t + 1/t` for `t > 0`. -/
theorem abs_log_le {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 1 / t := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.log_le_sub_one_of_pos (one_div_pos.mpr ht)
  rw [one_div, Real.log_inv] at h2
  have h3 : 0 < t⁻¹ := inv_pos.mpr ht
  rw [abs_le, one_div]
  constructor <;> linarith

/-- **`log²t ≤ t + 1/t − 2`** for `t > 0` (`y² ≤ 2(cosh y − 1) = 4 sinh²(y/2)`, `y = log t`). -/
theorem log_sq_le {t : ℝ} (ht : 0 < t) : Real.log t ^ 2 ≤ t + 1 / t - 2 := by
  set y := Real.log t with hy
  have hc : Real.cosh y = (t + 1 / t) / 2 := by
    rw [Real.cosh_eq, hy, Real.exp_log ht, Real.exp_neg, Real.exp_log ht, one_div]
  have h2 : Real.cosh y = 1 + 2 * Real.sinh (y / 2) ^ 2 := by
    have e := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring, Real.cosh_sq] at e
    linarith
  have h3 : (y / 2) ^ 2 ≤ Real.sinh (y / 2) ^ 2 := by
    rcases le_total 0 (y / 2) with h | h
    · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.mpr h) 2
    · have h4 := Real.sinh_le_self_iff.mpr h
      nlinarith
  nlinarith

/-! ## (3) `PhiReg` -/

/-- `t^s e^{−t²/2}` is integrable on `(0,∞)` for `s > −1` (rpow). -/
theorem rint2 {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-t ^ 2 / 2)) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) hs).congr_fun
    (fun t _ => by
      beta_reduce
      rw [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]) measurableSet_Ioi

/-- `φ(t)t^{σ−1} = t^{σ+1}e^{−t²/2}` on `t > 0`: integrable for `σ > −2`. -/
theorem phi_mellin_int {σ : ℝ} (hσ : -2 < σ) :
    IntegrableOn (fun t => HW.phi t * t ^ (σ - 1)) (Ioi 0) :=
  (rint2 (s := σ + 1) (by linarith)).congr_fun (fun t ht => by
    have ht0 : 0 < t := ht
    beta_reduce
    rw [show σ + 1 = 2 + (σ - 1) by ring, Real.rpow_add ht0, Real.rpow_two]
    unfold HW.phi
    ring) measurableSet_Ioi

/-- `φ'(t)t^{σ−1} = 2t^σe^{−t²/2} − t^{σ+2}e^{−t²/2}` on `t > 0`: integrable for `σ > −1`. -/
theorem dphi_mellin_int {σ : ℝ} (hσ : -1 < σ) :
    IntegrableOn (fun t => deriv HW.phi t * t ^ (σ - 1)) (Ioi 0) :=
  IntegrableOn.congr_fun
    (((rint2 (s := σ) hσ).const_mul 2).sub (rint2 (s := σ + 2) (by linarith)))
    (fun t ht => by
      have ht0 : 0 < t := ht
      have e1 : t ^ σ = t * t ^ (σ - 1) := by
        have h := Real.rpow_add ht0 1 (σ - 1)
        rw [Real.rpow_one, show (1 : ℝ) + (σ - 1) = σ by ring] at h
        exact h
      have e3 : t ^ (3 : ℝ) = t ^ 3 := by exact_mod_cast Real.rpow_natCast t 3
      have e2 : t ^ (σ + 2) = t ^ 3 * t ^ (σ - 1) := by
        rw [← e3, ← Real.rpow_add ht0]
        congr 1
        ring
      simp only [Pi.sub_apply]
      rw [deriv_phi_eq, e1, e2]
      ring) measurableSet_Ioi

/-- `∫ φ² = ∫ t⁴e^{−t²}`. -/
theorem gi_phi_sq : GI (fun t => HW.phi t ^ 2) (3 / 8 * Real.sqrt Real.pi) :=
  gi_congr I4 (fun t _ => by unfold HW.phi; rw [mul_pow, exp_half_sq]; ring) rfl

/-- `∫ φ'² = 4∫t²e^{−t²} − 4∫t⁴e^{−t²} + ∫t⁶e^{−t²} = (7/16)√π`. -/
theorem gi_dphi_sq : GI (fun t => deriv HW.phi t ^ 2) (7 / 16 * Real.sqrt Real.pi) :=
  gi_congr (gi_lin 1 1 (gi_lin 4 (-4) I2 I4) I6)
    (fun t _ => by rw [deriv_phi_eq, mul_pow, exp_half_sq]; ring) (by ring)

/-- The majorant of `(φ·log)²`: `(t⁵ + t³ − 2t⁴)e^{−t²}`, integral `3/2 − (3/4)√π`. -/
theorem gi_llog_maj : GI (fun t => 1 * (1 * (t ^ 5 * Real.exp (-t ^ 2)) +
    1 * (t ^ 3 * Real.exp (-t ^ 2))) + -2 * (t ^ 4 * Real.exp (-t ^ 2)))
    (1 * (1 * 1 + 1 * (1 / 2)) + -2 * (3 / 8 * Real.sqrt Real.pi)) :=
  gi_lin 1 (-2) (gi_lin 1 1 I5 I3) I4

theorem llog_sq_le {t : ℝ} (ht : 0 < t) : llog HW.phi t ^ 2 ≤ 1 * (1 * (t ^ 5 * Real.exp (-t ^ 2)) +
    1 * (t ^ 3 * Real.exp (-t ^ 2))) + -2 * (t ^ 4 * Real.exp (-t ^ 2)) := by
  unfold llog HW.phi
  have hl := log_sq_le ht
  have hE : 0 ≤ t ^ 4 * Real.exp (-t ^ 2) := by positivity
  have e1 : (Real.log t * (t ^ 2 * Real.exp (-t ^ 2 / 2))) ^ 2 =
      Real.log t ^ 2 * (t ^ 4 * Real.exp (-t ^ 2)) := by
    rw [mul_pow, mul_pow, exp_half_sq]
    ring
  have e2 : 1 * (1 * (t ^ 5 * Real.exp (-t ^ 2)) + 1 * (t ^ 3 * Real.exp (-t ^ 2))) +
      -2 * (t ^ 4 * Real.exp (-t ^ 2)) = (t + 1 / t - 2) * (t ^ 4 * Real.exp (-t ^ 2)) := by
    field_simp
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hl hE

theorem measurable_llog_phi : Measurable (llog HW.phi) :=
  Real.measurable_log.mul HW.continuous_phi.measurable

/-- `(φ·log)` is integrable: `|log t|φ(t) ≤ (t³ + t)e^{−t²/2}`. -/
theorem llog_phi_int : IntegrableOn (llog HW.phi) (Ioi 0) := by
  refine Integrable.mono' (gi_lin 1 1 M3 M1).1 measurable_llog_phi.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := ht
  unfold llog HW.phi
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 *
    Real.exp (-t ^ 2 / 2))]
  have h := mul_le_mul_of_nonneg_right (abs_log_le ht0)
    (by positivity : (0 : ℝ) ≤ t ^ 2 * Real.exp (-t ^ 2 / 2))
  have e : (t + 1 / t) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) =
      1 * (t ^ 3 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) := by
    field_simp
  linarith

/-- `(φ·log)²` is integrable. -/
theorem llog_phi_sq_int : IntegrableOn (fun t => llog HW.phi t ^ 2) (Ioi 0) :=
  Integrable.mono' gi_llog_maj.1 (measurable_llog_phi.pow_const 2).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact llog_sq_le ht))

/-- `|φ|/√t ≤ (λ/2)t e^{−t²/2} + t²e^{−t²/2}/(2λ)`, `λ = 1.1195` (`t(√t − λ)² ≥ 0`). -/
theorem n1h_phi_pt {t : ℝ} (ht : 0 < t) :
    |HW.phi t| / Real.sqrt t ≤ 1.1195 / 2 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) +
      1 / (2 * 1.1195) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have key : t * Real.sqrt t ≤ 1.1195 / 2 * t + 1 / (2 * 1.1195) * t ^ 2 := by
    have h1 := mul_nonneg ht.le (sq_nonneg (Real.sqrt t - 1.1195))
    have h2 : t * Real.sqrt t ^ 2 = t * t := by rw [hss]
    nlinarith
  have e : |HW.phi t| / Real.sqrt t = t * Real.sqrt t * Real.exp (-t ^ 2 / 2) := by
    rw [abs_of_nonneg (HW.phi_nonneg t), div_eq_iff hs0.ne']
    unfold HW.phi
    have : t * Real.sqrt t * Real.exp (-t ^ 2 / 2) * Real.sqrt t =
        t * Real.sqrt t ^ 2 * Real.exp (-t ^ 2 / 2) := by ring
    rw [this, hss]
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_right key hE.le
  have e2 : (1.1195 / 2 * t + 1 / (2 * 1.1195) * t ^ 2) * Real.exp (-t ^ 2 / 2) =
      1.1195 / 2 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) +
        1 / (2 * 1.1195) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by ring
  linarith

/-- The majorant of `|φ|/√t`, integral `λ/2 + √(2π)/(4λ)`. -/
theorem gi_n1h_maj : GI (fun t => 1.1195 / 2 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) +
    1 / (2 * 1.1195) * (t ^ 2 * Real.exp (-t ^ 2 / 2)))
    (1.1195 / 2 * 1 + 1 / (2 * 1.1195) * (Real.sqrt 2 * Real.sqrt Real.pi / 2)) :=
  gi_lin _ _ M1 M2

theorem phi_div_sqrt_int : IntegrableOn (fun t => HW.phi t / Real.sqrt t) (Ioi 0) :=
  Integrable.mono' gi_n1h_maj.1
    ((HW.continuous_phi.measurable.div Real.continuous_sqrt.measurable).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
      have ht0 : 0 < t := ht
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg t)]
      exact n1h_phi_pt ht0))

/-- **`PhiReg` PROVED.** -/
theorem phiReg_holds : PhiReg := by
  have hm : AEStronglyMeasurable HW.phi (volume.restrict (Ioi 0)) :=
    HW.continuous_phi.aestronglyMeasurable
  have hL2 : MemLp HW.phi 2 (volume.restrict (Ioi 0)) :=
    (memLp_two_iff_integrable_sq hm).mpr gi_phi_sq.1
  have hσ : ∀ σ ∈ Ioo (-1 / 2 : ℝ) 2, IntegrableOn (fun t => HW.phi t * t ^ (σ - 1)) (Ioi 0) ∧
      IntegrableOn (fun t => deriv HW.phi t * t ^ (σ - 1)) (Ioi 0) := fun σ hσ =>
    ⟨phi_mellin_int (by linarith [hσ.1]), dphi_mellin_int (by linarith [hσ.1])⟩
  refine ⟨⟨?_, hL2, ?_, -1 / 2, 2, by norm_num, by norm_num, hσ⟩,
    ⟨memLp_one_iff_integrable.mpr EN.integrable_phi, hL2,
      memLp_one_iff_integrable.mpr llog_phi_int,
      (memLp_two_iff_integrable_sq measurable_llog_phi.aestronglyMeasurable).mpr llog_phi_sq_int,
      phi_div_sqrt_int, 0, 1, by norm_num, by norm_num, fun σ hσ' =>
        phi_mellin_int (by linarith [hσ'.1])⟩⟩
  · have hc : ContDiff ℝ 1 (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2)) := by fun_prop
    exact hc.contDiffOn
  · refine (memLp_two_iff_integrable_sq (measurable_deriv HW.phi).aestronglyMeasurable).mpr ?_
    exact gi_dphi_sq.1

/-! ## (4) `PhiNormsL` -/

/-- **`eq:drachcat` at constants reachable without trigamma or `Γ(1/4)`** (the stated `PhiNorms`
is recorded as a finding in the module docstring). -/
def PhiNormsL : Prop :=
  MajSp.l2 HW.phi ≤ 0.81528 ∧ MajSp.l2 (llog HW.phi) ≤ 0.41312 ∧ n1h HW.phi ≤ 1.1196 ∧
    MajSp.l2 (deriv HW.phi) ≤ 0.88060 ∧ ∀ δ : ℝ, c0 HW.phi δ ≤ 2.786 + 11.33 * |δ|

/-- A Bochner bound from a pointwise majorant on `(0,∞)`. -/
theorem int_le_of_pt {f g : ℝ → ℝ} {A : ℝ} (hg : GI g A) (hf0 : ∀ t, 0 ≤ f t)
    (hfg : ∀ t : ℝ, 0 < t → f t ≤ g t) : ∫ t in Ioi (0 : ℝ), f t ≤ A := by
  rw [← hg.2]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall hf0) hg.1
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => hfg t ht))

theorem l2_phi_le : MajSp.l2 HW.phi ≤ 0.81528 := by
  unfold MajSp.l2
  rw [gi_phi_sq.2, Real.sqrt_le_left (by norm_num)]
  nlinarith [sqrt_pi_bounds.2]

theorem l2_dphi_le : MajSp.l2 (deriv HW.phi) ≤ 0.88060 := by
  unfold MajSp.l2
  rw [gi_dphi_sq.2, Real.sqrt_le_left (by norm_num)]
  nlinarith [sqrt_pi_bounds.2]

theorem l2_llog_le : MajSp.l2 (llog HW.phi) ≤ 0.41312 := by
  unfold MajSp.l2
  have h := int_le_of_pt gi_llog_maj (fun t => sq_nonneg _) fun t ht => llog_sq_le ht
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [sqrt_pi_bounds.1]

theorem n1h_phi_le : n1h HW.phi ≤ 1.1196 := by
  unfold n1h
  have h := int_le_of_pt gi_n1h_maj (fun t => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    fun t ht => n1h_phi_pt ht
  nlinarith [sqrt_2pi_bounds.2]

/-- `|φ'|/√t ≤ (λ/2)(2 − t²)²e^{−t²/2} + t e^{−t²/2}/(2λ)`, `λ = 0.5157`. -/
theorem n1h_dphi_pt {t : ℝ} (ht : 0 < t) :
    |deriv HW.phi t| / Real.sqrt t ≤ 1 * (1 * (0.5157 / 2 * 4 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) +
      -(0.5157 / 2 * 4) * (t ^ 2 * Real.exp (-t ^ 2 / 2))) +
        0.5157 / 2 * (t ^ 4 * Real.exp (-t ^ 2 / 2))) +
      1 / (2 * 0.5157) * (t ^ 1 * Real.exp (-t ^ 2 / 2)) := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have key : Real.sqrt t * |2 - t ^ 2| ≤ 0.5157 / 2 * (2 - t ^ 2) ^ 2 + 1 / (2 * 0.5157) * t := by
    have h1 := sq_nonneg (0.5157 * |2 - t ^ 2| - Real.sqrt t)
    have h2 := sq_abs (2 - t ^ 2)
    nlinarith
  have e : |deriv HW.phi t| / Real.sqrt t = Real.sqrt t * |2 - t ^ 2| * Real.exp (-t ^ 2 / 2) := by
    rw [deriv_phi_eq, abs_mul, abs_of_pos hE, div_eq_iff hs0.ne',
      show 2 * t - t ^ 3 = t * (2 - t ^ 2) by ring, abs_mul, abs_of_pos ht]
    have : Real.sqrt t * |2 - t ^ 2| * Real.exp (-t ^ 2 / 2) * Real.sqrt t =
        Real.sqrt t ^ 2 * |2 - t ^ 2| * Real.exp (-t ^ 2 / 2) := by ring
    rw [this, hss]
  rw [e]
  have := mul_le_mul_of_nonneg_right key hE.le
  have e2 : (0.5157 / 2 * (2 - t ^ 2) ^ 2 + 1 / (2 * 0.5157) * t) * Real.exp (-t ^ 2 / 2) =
      1 * (1 * (0.5157 / 2 * 4 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) +
        -(0.5157 / 2 * 4) * (t ^ 2 * Real.exp (-t ^ 2 / 2))) +
          0.5157 / 2 * (t ^ 4 * Real.exp (-t ^ 2 / 2))) +
        1 / (2 * 0.5157) * (t ^ 1 * Real.exp (-t ^ 2 / 2)) := by ring
  linarith

theorem n1h_dphi_le : n1h (deriv HW.phi) ≤ 1.9391 := by
  unfold n1h
  have h := int_le_of_pt (gi_lin 1 (1 / (2 * 0.5157)) (gi_lin 1 (0.5157 / 2)
      (gi_lin (0.5157 / 2 * 4) (-(0.5157 / 2 * 4)) M0 M2) M4) M1)
    (fun t => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) fun t ht => n1h_dphi_pt ht
  nlinarith [sqrt_2pi_bounds.2]

/-- `|φ'|√t ≤ (λ/2)t(2 − t²)²e^{−t²/2} + t²e^{−t²/2}/(2λ)`, `λ = 0.5598`. -/
theorem n1s_dphi_pt {t : ℝ} (ht : 0 < t) :
    |deriv HW.phi t| * Real.sqrt t ≤ 1 * (1 * (0.5598 / 2 * 4 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) +
      -(0.5598 / 2 * 4) * (t ^ 3 * Real.exp (-t ^ 2 / 2))) +
        0.5598 / 2 * (t ^ 5 * Real.exp (-t ^ 2 / 2))) +
      1 / (2 * 0.5598) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have key : Real.sqrt t * |2 - t ^ 2| * t ≤
      0.5598 / 2 * (t * (2 - t ^ 2) ^ 2) + 1 / (2 * 0.5598) * t ^ 2 := by
    have h1 := sq_nonneg (0.5598 * (Real.sqrt t * |2 - t ^ 2|) - t)
    have h2 := sq_abs (2 - t ^ 2)
    have h3 : (Real.sqrt t * |2 - t ^ 2|) ^ 2 = t * (2 - t ^ 2) ^ 2 := by
      rw [mul_pow, hss, h2]
    nlinarith
  have e : |deriv HW.phi t| * Real.sqrt t =
      Real.sqrt t * |2 - t ^ 2| * t * Real.exp (-t ^ 2 / 2) := by
    rw [deriv_phi_eq, abs_mul, abs_of_pos hE, show 2 * t - t ^ 3 = t * (2 - t ^ 2) by ring,
      abs_mul, abs_of_pos ht]
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_right key hE.le
  have e2 : (0.5598 / 2 * (t * (2 - t ^ 2) ^ 2) + 1 / (2 * 0.5598) * t ^ 2) *
      Real.exp (-t ^ 2 / 2) =
      1 * (1 * (0.5598 / 2 * 4 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) +
        -(0.5598 / 2 * 4) * (t ^ 3 * Real.exp (-t ^ 2 / 2))) +
          0.5598 / 2 * (t ^ 5 * Real.exp (-t ^ 2 / 2))) +
        1 / (2 * 0.5598) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by ring
  linarith

theorem n1s_dphi_le : n1s (deriv HW.phi) ≤ 2.2391 := by
  unfold n1s
  have h := int_le_of_pt (gi_lin 1 (1 / (2 * 0.5598)) (gi_lin 1 (0.5598 / 2)
      (gi_lin (0.5598 / 2 * 4) (-(0.5598 / 2 * 4)) M1 M3) M5) M2)
    (fun t => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) fun t ht => n1s_dphi_pt ht
  nlinarith [sqrt_2pi_bounds.2]

/-- `|φ|√t ≤ (λ/2)t²e^{−t²/2} + t³e^{−t²/2}/(2λ)`, `λ = 1.2632` (`t²(√t − λ)² ≥ 0`). -/
theorem n1s_phi_pt {t : ℝ} (ht : 0 < t) :
    |HW.phi t| * Real.sqrt t ≤ 1.2632 / 2 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) +
      1 / (2 * 1.2632) * (t ^ 3 * Real.exp (-t ^ 2 / 2)) := by
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have key : t ^ 2 * Real.sqrt t ≤ 1.2632 / 2 * t ^ 2 + 1 / (2 * 1.2632) * t ^ 3 := by
    have h1 := mul_nonneg (sq_nonneg t) (sq_nonneg (Real.sqrt t - 1.2632))
    have h2 : t ^ 2 * Real.sqrt t ^ 2 = t ^ 3 := by rw [hss]; ring
    nlinarith
  rw [abs_of_nonneg (HW.phi_nonneg t)]
  unfold HW.phi
  have := mul_le_mul_of_nonneg_right key hE.le
  have e : t ^ 2 * Real.exp (-t ^ 2 / 2) * Real.sqrt t =
      t ^ 2 * Real.sqrt t * Real.exp (-t ^ 2 / 2) := by ring
  have e2 : (1.2632 / 2 * t ^ 2 + 1 / (2 * 1.2632) * t ^ 3) * Real.exp (-t ^ 2 / 2) =
      1.2632 / 2 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) +
        1 / (2 * 1.2632) * (t ^ 3 * Real.exp (-t ^ 2 / 2)) := by ring
  linarith

theorem n1s_phi_le : n1s HW.phi ≤ 1.5833 := by
  unfold n1s
  have h := int_le_of_pt (gi_lin (1.2632 / 2) (1 / (2 * 1.2632)) M2 M3)
    (fun t => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) fun t ht => n1s_phi_pt ht
  nlinarith [sqrt_2pi_bounds.2]

theorem c0_phi_le (δ : ℝ) : c0 HW.phi δ ≤ 2.786 + 11.33 * |δ| := by
  unfold c0
  have h1 := n1h_dphi_le
  have h2 := n1s_dphi_le
  have h3 := n1h_phi_le
  have h4 := n1s_phi_le
  have hd : 0 ≤ 2 * Real.pi * |δ| := by positivity
  have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) hd
  have h6 : 2 * Real.pi * |δ| * (1.1196 + 1.5833) ≤ 2 * 3.141593 * |δ| * 2.7029 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (by norm_num : (0 : ℝ) ≤ 2))
      (abs_nonneg δ)) (by norm_num : (0 : ℝ) ≤ 2.7029)
    linarith
  nlinarith [abs_nonneg δ]

/-- **`PhiNormsL` PROVED.** -/
theorem phiNormsL_holds : PhiNormsL :=
  ⟨l2_phi_le, l2_llog_le, n1h_phi_le, l2_dphi_le, c0_phi_le⟩

/-! ## (5) Cor 1.3 from `PhiNormsL` (the spine's chain at the proved constants) -/

open HW

/-- The residue-and-`x^{−3/2}` numerator of `prop:magoma` at `PhiNormsL`. -/
noncomputable def RphiL (q δ x : ℝ) : ℝ :=
  2.786 + 11.33 * |δ| + (Real.log q + 8) * (0.88060 + 2 * Real.pi * |δ| * 0.81528) / Real.sqrt x

/-- **`prop:magoma`, corrected, at `PhiNormsL`** (the spine's `phi_err` with the proved norms). -/
theorem phi_errL (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer) (hG : GarmolaDecr)
    (fr : PhiReg) (fn : PhiNormsL) (fd : PhiDecay) (ft : PhiTailInt)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≤ 400000)
    {δ x T : ℝ} (hx : 1 ≤ x) (hT : 333 ≤ T) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ T)
    (hgrh : GRHTo χ T) :
    ‖MajSp.err phi χ δ x‖ ≤
      tailF q T δ + hbC q T 0.81528 0.41312 1.1196 / Real.sqrt x + RphiL q δ x / x := by
  obtain ⟨n2, nl, n1, nd, nc⟩ := fn
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqT : 37 ≤ (q : ℝ) * T := by nlinarith
  have hH := hHs hZC phi fr.2 q χ hχ δ T (by linarith) hqT hgrh
  have hTail := phi_high hZC hG fd ft hχ hq hT hTd
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1']
  have hR : c0 phi δ + (Real.log q + 8) *
      (MajSp.l2 (deriv phi) + 2 * Real.pi * |δ| * MajSp.l2 phi) / Real.sqrt x ≤
        RphiL q δ x := by
    unfold RphiL
    have hpd : 0 ≤ 2 * Real.pi * |δ| := by positivity
    have h1 : MajSp.l2 (deriv phi) + 2 * Real.pi * |δ| * MajSp.l2 phi ≤
        0.88060 + 2 * Real.pi * |δ| * 0.81528 :=
      add_le_add nd (mul_le_mul_of_nonneg_left n2 hpd)
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlq) hs0.le
    linarith [nc δ]
  have h0 : phi 0 = 0 := by simp [phi]
  exact err_le_of_zero_sums hEF fr.1 h0 hχ hx hgrh
    (hbC_nonneg hq1' hqT (by norm_num) (by norm_num) (by norm_num)) (tailF_nonneg hq1' hT)
    (le_trans hH.1 (ENNReal.ofReal_le_ofReal (hbC_mono hq1' hqT n2 nl n1))) hTail hR

/-- The low zeros of `φ` at `T = 10⁸/Q` at `PhiNormsL`: `hbC ≤ 385000/√Q + 113`
(`38.4990·10⁴` and `112.12`). -/
theorem hbC_phi_closeL {S L lq u : ℝ} (hS : S = 10000 * u) (hu : 0 ≤ u) (hL19 : L ≤ 19)
    (hL3 : 3 ≤ L) (hlq : lq ≤ 13) :
    0.7979 * 0.81528 * S * (L - 2.3378) + 2.5067 * 0.41312 * S * (0.5 * L + 17.21) +
      1.1196 * (0.819 * lq + 16.8 + 1.4143 * (0.5 * lq + 17.7) + 1.4143 * (0.5 * L + 17.7)) ≤
        385000 * u + 113 := by
  have hA : S * (L - 2.3378) ≤ 10000 * u * 16.6622 :=
    mul_le_mul (le_of_eq hS) (by linarith) (by linarith) (by positivity)
  have hB : S * (0.5 * L + 17.21) ≤ 10000 * u * 26.71 :=
    mul_le_mul (le_of_eq hS) (by linarith) (by linarith) (by positivity)
  linarith

theorem hbC_phi_leL {Q : ℝ} (hQ : 1 ≤ Q) (hQr : Q ≤ 300000) :
    hbC Q (1e8 / Q) 0.81528 0.41312 1.1196 ≤ 385000 * (1 / Real.sqrt Q) + 113 := by
  obtain ⟨-, -, hs, -, hL19, hL3, -⟩ := coprT_facts hQ hQr
  exact hbC_phi_closeL hs (by positivity) hL19 hL3 (logQ_le hQ hQr)

/-- **Cor 1.3, RETYPED — the closing arithmetic at `PhiNormsL`.** -/
theorem coprar_closeL {u v sx d : ℝ} (hv : v ≤ u) (hv0 : 0 ≤ v) (hu : 1 / 548 ≤ u)
    (hsx : 10000 ≤ sx) (hd : d ≤ 1.2e6 * v) :
    2.5e-13 * v + 1.37259 * ((385000 * u + 113) / sx) +
        1.92182 * ((2.786 + 11.33 * d) / (sx * sx)) +
        2.74517 * (21 * (0.88060 + 5.1226 * d) / (sx * sx * sx)) ≤
      3e-13 * v + (650000 * u + 80) / sx := by
  have hsx0 : 0 < sx := by linarith
  have h2 : (2.786 + 11.33 * d) / (sx * sx) ≤ (2.786 + 11.33 * (1.2e6 * v)) / 10000 / sx := by
    rw [div_div]
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) (by nlinarith)
  have h3 : 21 * (0.88060 + 5.1226 * d) / (sx * sx * sx) ≤
      21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000 / sx := by
    rw [div_div]
    exact div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by nlinarith)
  have h4 : 1.37259 * ((385000 * u + 113) / sx) +
      1.92182 * ((2.786 + 11.33 * (1.2e6 * v)) / 10000 / sx) +
      2.74517 * (21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000 / sx) =
        (1.37259 * (385000 * u + 113) + 1.92182 * ((2.786 + 11.33 * (1.2e6 * v)) / 10000) +
          2.74517 * (21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000)) / sx := by ring
  have h5 : (1.37259 * (385000 * u + 113) + 1.92182 * ((2.786 + 11.33 * (1.2e6 * v)) / 10000) +
      2.74517 * (21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000)) / sx ≤
        (650000 * u + 80) / sx :=
    div_le_div_of_nonneg_right (by linarith) hsx0.le
  linarith

/-- **`prop:magoma` at `(δw, wx)`, `w ∈ [1/4,1]`, at `PhiNormsL`**, in the transfer's shape. -/
theorem coprar_wL (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer) (hG : GarmolaDecr)
    (fr : PhiReg) (fn : PhiNormsL) (fd : PhiDecay) (ft : PhiTailInt) (pf : RT.PlattFull)
    {x : ℝ} (hx : 10 ^ 8 ≤ x) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≤ 300000) {δ : ℝ} (hδ : |δ| ≤ 4 * 300000 / q) (w : ℝ)
    (hw : w ∈ Icc (1 / 4 : ℝ) 1) :
    ‖MajSp.err phi χ (δ * w) (w * x)‖ ≤ 2.5e-13 * (1 / q) +
      (385000 * (1 / Real.sqrt q) + 113) / Real.sqrt x * (1 / Real.sqrt w) +
      (2.786 + 11.33 * |δ|) / x * (1 / w) +
      (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) *
        (1 / (w * Real.sqrt w)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have hw0 : 0 < w := by linarith [hw.1]
  have hw1 : w ≤ 1 := hw.2
  have hx0 : 0 < x := by linarith
  obtain ⟨hT, -, -, -, -, -, -⟩ := coprT_facts hq1 hqr
  have hδ1 : |δ| ≤ 1.2e6 / q := by
    rw [show (1.2e6 : ℝ) = 4 * 300000 by norm_num]
    exact hδ
  have hδw : |δ * w| ≤ |δ| := by
    rw [abs_mul, abs_of_pos hw0]
    exact mul_le_of_le_one_right (abs_nonneg δ) hw1
  have hδw1 : |δ * w| ≤ 1.2e6 / q := hδw.trans hδ1
  have hTd : 4 * Real.pi ^ 2 * |δ * w| ≤ 1e8 / q := by
    have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h1 := mul_le_mul_of_nonneg_left hδw1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
    have h2 : 4 * Real.pi ^ 2 * (1.2e6 / q) ≤ 1e8 / q := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith) hQ0.le
    linarith
  have hTh : (1e8 : ℝ) / q ≤ RT.plattHeight q := by
    rw [show (1e8 : ℝ) = 10 ^ 8 by norm_num]
    exact RT.height_ge q
  have hgrh := grh_of_platt pf (by omega) hχ hTh
  have hwx : 1 ≤ w * x := by nlinarith [hw.1]
  have hb := phi_errL hEF hZC hHs hG fr fn fd ft hχ (by omega) hwx (by linarith) hTd hgrh
  have h1 := tailF_le hq1 hqr hδw1
  have h2 := hbC_phi_leL hq1 hqr
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hswx : Real.sqrt (w * x) = Real.sqrt w * Real.sqrt x := Real.sqrt_mul hw0.le x
  have hH : hbC q (1e8 / q) 0.81528 0.41312 1.1196 / Real.sqrt (w * x) ≤
      (385000 * (1 / Real.sqrt q) + 113) / Real.sqrt x * (1 / Real.sqrt w) := by
    rw [hswx]
    have e : (385000 * (1 / Real.sqrt q) + 113) / Real.sqrt x * (1 / Real.sqrt w) =
        (385000 * (1 / Real.sqrt q) + 113) / (Real.sqrt w * Real.sqrt x) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1]
  have hRn : RphiL q (δ * w) (w * x) ≤ 2.786 + 11.33 * |δ| +
      (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (Real.sqrt w * Real.sqrt x) := by
    unfold RphiL
    rw [hswx]
    have ha : 2 * Real.pi * |δ * w| * 0.81528 ≤ 5.1226 * |δ| := by
      have := mul_le_mul twopi_phi hδw (abs_nonneg _) (by norm_num)
      linarith
    have hb2 : (Real.log q + 8) * (0.88060 + 2 * Real.pi * |δ * w| * 0.81528) ≤
        (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) :=
      mul_le_mul_of_nonneg_left (by linarith) hlq
    have hb3 := div_le_div_of_nonneg_right hb2 (by positivity : 0 ≤ Real.sqrt w * Real.sqrt x)
    have hb4 := mul_le_mul_of_nonneg_left hδw (by norm_num : (0 : ℝ) ≤ 11.33)
    linarith
  have hR : RphiL q (δ * w) (w * x) / (w * x) ≤ (2.786 + 11.33 * |δ|) / x * (1 / w) +
      (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) *
        (1 / (w * Real.sqrt w)) := by
    have e : (2.786 + 11.33 * |δ|) / x * (1 / w) +
        (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) *
          (1 / (w * Real.sqrt w)) = (2.786 + 11.33 * |δ| +
        (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (Real.sqrt w * Real.sqrt x)) / (w * x) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hRn (by positivity)
  linarith

/-- **`MR.CoprarR (η₂ ∗_M φ)` from the links, at `PhiNormsL`** (the spine's `coprarR_of_links`
with `coprar_wL`, `coprar_closeL`). -/
theorem coprarR_of_linksL (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (fr : PhiReg) (fn : PhiNormsL) (fd : PhiDecay) (ft : PhiTailInt)
    (ko : Kolona) (mo : Eta2Moments) (pf : RT.PlattFull) : MR.CoprarR (mconv eta2 phi) := by
  intro x hx q hq1 hq χ hχ δ hδ
  haveI : NeZero q := ⟨by omega⟩
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have hx0 : 0 < x := by linarith
  have hsx := Real.sqrt_pos.mpr hx0
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1']
  have hb := kolona_transfer ko mo χ (δ := δ) hx0 (by positivity) (by positivity) (by positivity)
    (by positivity) (coprar_wL hEF hZC hHs hG fr fn fd ft pf hx hχ hq hδ)
  have hsx4 : 10000 ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hs548 : Real.sqrt q ≤ 548 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  have hu : 1 / 548 ≤ 1 / Real.sqrt q :=
    one_div_le_one_div_of_le (by linarith [one_le_sqrt' hq1']) hs548
  have hvu : 1 / (q : ℝ) ≤ 1 / Real.sqrt q :=
    one_div_le_one_div_of_le (by linarith [one_le_sqrt' hq1']) (sqrt_le_self' hq1')
  have hd : |δ| ≤ 1.2e6 * (1 / q) := by
    have e : 1.2e6 * (1 / (q : ℝ)) = 4 * 300000 / q := by ring
    rw [e]
    exact hδ
  have key := coprar_closeL hvu (by positivity) hu hsx4 hd
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
  have hC2 : (2.786 + 11.33 * |δ|) / x = (2.786 + 11.33 * |δ|) / (Real.sqrt x * Real.sqrt x) := by
    rw [← hxx]
  have hC3 : (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) ≤
      21 * (0.88060 + 5.1226 * |δ|) / (Real.sqrt x * Real.sqrt x * Real.sqrt x) := by
    rw [← hxx]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (by positivity)
    linarith [logQ_le hq1' hqr]
  have e1 : 3e-13 * (1 / (q : ℝ)) + (650000 * (1 / Real.sqrt q) + 80) / Real.sqrt x =
      3e-13 / q + (650000 / Real.sqrt q + 80) / Real.sqrt x := by ring
  have hC3' := mul_le_mul_of_nonneg_left hC3 (by norm_num : (0 : ℝ) ≤ 2.74517)
  rw [← e1]
  linarith

end Principia.Common.TernaryGoldbach.HM
