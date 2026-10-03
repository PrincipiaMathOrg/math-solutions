/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinorSpine

set_option autoImplicit false

/-!
# `MinSp.Dubistdie` — DISCHARGED for every weight

`eq:malus` + `eq:dubistdie`: for EVERY `η` with `|η(t)| ≤ a = 1.079955` and `|η(t)·t| ≤ c =
1.19073` on `t ≥ 0`, and `b(t) = sup_{r≥t}|η(r)|`, `E ≤ 8.4031·10⁻¹²·x` at `x ≥ 4.9·10²⁶`.
Weight-free real analysis, proved here outright (`dubistdie_all`), so it leaves the chain.

**The route** (numbers `scratchpad/integ/integ_numbers.py`, exact rationals):
* `0 ≤ b(t) ≤ a` and `b(t)·t ≤ c` (`supFn_bounds`: `b(t)` is a LEAST upper bound).
* `C_{η,0} = 0.7131∫₀^∞ b²/√t` with the majorant `a²t^{−1/2}` on `(0, s]`, `c²t^{−5/2}` on
  `(s, ∞)`, split at `s = 1.1025 = 1.05²` (the optimal split is `c/a = 1.10257`; a perfect square
  keeps `√s` rational): `∫ ≤ 2.1a² + (2/3)c²/1.05³` (`int0_le`), so `C_{η,0} ≤ 2.3288113`.
  (Helfgott/`MinorSpine` quote `2.33742`; the true value of this majorant is `2.3288113`.)
* `C_{η,1} = 0.7131∫₁^∞ (log t/√t)b²`, crudely: `log t/√t ≤ s − 1` on `(1, s]` and
  `log t ≤ 2(√t − 1)` on `(s, ∞)`: `∫ ≤ a²(s−1)² + 2c²(1/s − (2/3)/1.05³)` (`int1_le`), so
  `C_{η,1} ≤ 0.6783384` (the exact majorant gives `0.449`; the slack costs `1.2·10⁻¹⁴` in `E/x`).
* `C_{η,2} = 0.51942·b(0)² ≤ 0.6058010`.
* `E/x = ((C₀ + C₂)log x + 2C₀ + C₁)/√x` decreases for `x ≥ x₀ = 4.9·10²⁶`: with `w = √(x/x₀)`,
  `log x ≤ 61.5 + 2(w − 1)` and `√x ≥ 22135943·10⁶·w`, and `(C₀ + C₂)·61.5 + 2C₀ + C₁ =
  185.8146 ≤ 8.4031·10⁻¹²·22135943·10⁶ = 186.0105`: `E/x ≤ 8.3943·10⁻¹²` at `x₀`, margin `0.1 %`.
-/

namespace Principia.Common.TernaryGoldbach.DB

open MeasureTheory Set

/-! ## The sup function -/

/-- **`0 ≤ b(t) ≤ 1.079955` and `b(t)·t ≤ 1.19073`**, `b(t) = sup_{r ≥ t}|η(r)|`. -/
theorem supFn_bounds (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ b t ∧ b t ≤ 1.079955 ∧ b t * t ≤ 1.19073 := by
  have hl := hb t ht
  refine ⟨(abs_nonneg (η t)).trans (hl.1 ⟨t, Set.self_mem_Ici, rfl⟩), hl.2 ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact h1 r (le_trans ht hr)
  · rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      norm_num
    · have hub : b t ≤ 1.19073 / t := hl.2 (by
        rintro _ ⟨r, hr, rfl⟩
        have hr' : t ≤ r := hr
        have hr0 : 0 < r := lt_of_lt_of_le hpos hr'
        have h := h2 r hr0.le
        rw [abs_mul, abs_of_pos hr0] at h
        rw [le_div_iff₀ hpos]
        calc |η r| * t ≤ |η r| * r := mul_le_mul_of_nonneg_left hr' (abs_nonneg _)
          _ ≤ 1.19073 := h)
      rwa [le_div_iff₀ hpos] at hub

/-! ## Rational powers of `s = 1.1025 = 1.05²` -/

/-- `s^p = 1.05^{2p}`. -/
theorem rpow_s (p : ℝ) : (1.1025 : ℝ) ^ p = 1.05 ^ (2 * p) := by
  rw [show (1.1025 : ℝ) = 1.05 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
    ← Real.rpow_mul (by norm_num)]

/-- `s^{1/2} = 1.05`. -/
theorem s_half : (1.1025 : ℝ) ^ (-(1 / 2) + 1 : ℝ) = 1.05 := by
  rw [rpow_s, show (2 * (-(1 / 2) + 1) : ℝ) = 1 by norm_num, Real.rpow_one]

/-- `s^{−3/2} = 1/1.05³`. -/
theorem s_three_half : (1.1025 : ℝ) ^ (-(5 / 2) + 1 : ℝ) = (1.05 ^ 3)⁻¹ := by
  rw [rpow_s, show (2 * (-(5 / 2) + 1) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- `s^{−1} = 1/1.1025`. -/
theorem s_one : (1.1025 : ℝ) ^ (-2 + 1 : ℝ) = (1.1025 : ℝ)⁻¹ := by
  rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]

/-- `t^{−5/2} = 1/(t²·√t)` for `t > 0`. -/
theorem rpow_five_half {t : ℝ} (ht : 0 < t) : t ^ (-(5 / 2) : ℝ) = (t ^ 2 * Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht.le, show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num,
    Real.rpow_add ht, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-- `t^{−2} = 1/t²` for `t > 0`. -/
theorem rpow_neg_two {t : ℝ} (ht : 0 < t) : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]

/-- `t^{−1/2} = 1/√t` for `t > 0`. -/
theorem rpow_neg_half {t : ℝ} (ht : 0 < t) : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]

/-! ## `C_{η,0}` -/

/-- The majorant of `b²/√t`. -/
noncomputable def m0 (t : ℝ) : ℝ :=
  if t ≤ 1.1025 then 1.079955 ^ 2 * t ^ (-(1 / 2) : ℝ) else 1.19073 ^ 2 * t ^ (-(5 / 2) : ℝ)

/-- **`∫₀^∞ m₀ = 2.1a² + (2/3)c²/1.05³`**, and `m₀` is integrable. -/
theorem m0_int : IntegrableOn m0 (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), m0 t = 1.079955 ^ 2 * 2.1 + 1.19073 ^ 2 * (2 / 3 / 1.05 ^ 3) := by
  have hA : IntegrableOn (fun t : ℝ => 1.079955 ^ 2 * t ^ (-(1 / 2) : ℝ)) (Ioc 0 1.1025) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _).1
  have hB : IntegrableOn (fun t : ℝ => 1.19073 ^ 2 * t ^ (-(5 / 2) : ℝ)) (Ioi 1.1025) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
  have hmA : IntegrableOn m0 (Ioc 0 1.1025) :=
    hA.congr_fun (fun t ht => by rw [m0, if_pos ht.2]) measurableSet_Ioc
  have hmB : IntegrableOn m0 (Ioi 1.1025) :=
    hB.congr_fun (fun t ht => by rw [m0, if_neg (not_le.mpr ht)]) measurableSet_Ioi
  have hU : Ioc (0 : ℝ) 1.1025 ∪ Ioi 1.1025 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  refine ⟨hU ▸ hmA.union hmB, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hmA hmB]
  have iA : ∫ t in Ioc (0 : ℝ) 1.1025, m0 t = 1.079955 ^ 2 * 2.1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [m0, if_pos ht.2]),
      integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inl (by norm_num)), s_half, Real.zero_rpow (by norm_num)]
    norm_num
  have iB : ∫ t in Ioi (1.1025 : ℝ), m0 t = 1.19073 ^ 2 * (2 / 3 / 1.05 ^ 3) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [m0, if_neg (not_le.mpr ht)]),
      integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num), s_three_half]
    norm_num
  rw [iA, iB]

/-- **`∫₀^∞ b²/√t ≤ 2.1a² + (2/3)c²/1.05³`**. -/
theorem int0_le (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) :
    ∫ t in Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t ≤
      1.079955 ^ 2 * 2.1 + 1.19073 ^ 2 * (2 / 3 / 1.05 ^ 3) := by
  obtain ⟨hm, hval⟩ := m0_int
  have hpt : ∀ t ∈ Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t ≤ m0 t := by
    intro t ht
    have ht0 : 0 < t := ht
    obtain ⟨hb0, hba, hbt⟩ := supFn_bounds η b h1 h2 hb ht0.le
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    unfold m0
    split_ifs with hts
    · rw [rpow_neg_half ht0, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hb0 hba 2) hs0.le
    · rw [rpow_five_half ht0, ← div_eq_mul_inv, div_le_div_iff₀ hs0 (by positivity)]
      have hsq : (b t * t) ^ 2 ≤ 1.19073 ^ 2 := pow_le_pow_left₀ (by positivity) hbt 2
      calc b t ^ 2 * (t ^ 2 * Real.sqrt t) = (b t * t) ^ 2 * Real.sqrt t := by ring
        _ ≤ 1.19073 ^ 2 * Real.sqrt t := mul_le_mul_of_nonneg_right hsq hs0.le
  have hI := integral_mono_of_nonneg
    (ae_of_all _ fun t => div_nonneg (sq_nonneg (b t)) (Real.sqrt_nonneg t)) hm
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [hval] at hI
  exact hI

/-! ## `C_{η,1}` -/

/-- The majorant of `(log t/√t)·b²` on `(1, ∞)`. -/
noncomputable def m1 (t : ℝ) : ℝ :=
  if t ≤ 1.1025 then 1.079955 ^ 2 * (1.1025 - 1)
  else 2 * 1.19073 ^ 2 * (t ^ (-2 : ℝ) - t ^ (-(5 / 2) : ℝ))

/-- **`∫₁^∞ m₁ = a²(s−1)² + 2c²(1/s − (2/3)/1.05³)`**, and `m₁` is integrable. -/
theorem m1_int : IntegrableOn m1 (Ioi 1) ∧
    ∫ t in Ioi (1 : ℝ), m1 t = 1.079955 ^ 2 * (1.1025 - 1) * (1.1025 - 1) +
      2 * 1.19073 ^ 2 * ((1.1025 : ℝ)⁻¹ - 2 / 3 / 1.05 ^ 3) := by
  have hA : IntegrableOn (fun _ : ℝ => (1.079955 : ℝ) ^ 2 * (1.1025 - 1)) (Ioc 1 1.1025) :=
    (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi 1.1025) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h5 : IntegrableOn (fun t : ℝ => t ^ (-(5 / 2) : ℝ)) (Ioi 1.1025) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hB : IntegrableOn (fun t : ℝ => 2 * 1.19073 ^ 2 * (t ^ (-2 : ℝ) - t ^ (-(5 / 2) : ℝ)))
      (Ioi 1.1025) := (Integrable.sub h2 h5).const_mul _
  have hmA : IntegrableOn m1 (Ioc 1 1.1025) :=
    hA.congr_fun (fun t ht => by rw [m1, if_pos ht.2]) measurableSet_Ioc
  have hmB : IntegrableOn m1 (Ioi 1.1025) :=
    hB.congr_fun (fun t ht => by rw [m1, if_neg (not_le.mpr ht)]) measurableSet_Ioi
  have hU : Ioc (1 : ℝ) 1.1025 ∪ Ioi 1.1025 = Ioi 1 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  refine ⟨hU ▸ hmA.union hmB, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hmA hmB]
  have iA : ∫ t in Ioc (1 : ℝ) 1.1025, m1 t = 1.079955 ^ 2 * (1.1025 - 1) * (1.1025 - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [m1, if_pos ht.2]),
      ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have iB : ∫ t in Ioi (1.1025 : ℝ), m1 t =
      2 * 1.19073 ^ 2 * ((1.1025 : ℝ)⁻¹ - 2 / 3 / 1.05 ^ 3) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [m1, if_neg (not_le.mpr ht)]),
      integral_const_mul, integral_sub h2 h5, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num),
      integral_Ioi_rpow_of_lt (by norm_num) (by norm_num), s_one, s_three_half]
    norm_num
  rw [iA, iB]

/-- **`∫₁^∞ (log t/√t)b² ≤ a²(s−1)² + 2c²(1/s − (2/3)/1.05³)`**. -/
theorem int1_le (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) :
    ∫ t in Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2 ≤
      1.079955 ^ 2 * (1.1025 - 1) * (1.1025 - 1) +
        2 * 1.19073 ^ 2 * ((1.1025 : ℝ)⁻¹ - 2 / 3 / 1.05 ^ 3) := by
  obtain ⟨hm, hval⟩ := m1_int
  have hpt : ∀ t ∈ Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2 ≤ m1 t := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    obtain ⟨hb0, hba, hbt⟩ := supFn_bounds η b h1 h2 hb ht0.le
    have hL0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hq1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1.le
    have hq0 : 0 < Real.sqrt t := by linarith
    unfold m1
    split_ifs with hts
    · have hlq : Real.log t / Real.sqrt t ≤ 1.1025 - 1 := by
        rw [div_le_iff₀ hq0]
        have hl := Real.log_le_sub_one_of_pos ht0
        nlinarith
      have hlq0 : 0 ≤ Real.log t / Real.sqrt t := div_nonneg hL0 hq0.le
      calc Real.log t / Real.sqrt t * b t ^ 2 ≤ (1.1025 - 1) * 1.079955 ^ 2 :=
            mul_le_mul hlq (pow_le_pow_left₀ hb0 hba 2) (sq_nonneg _) (by norm_num)
        _ = 1.079955 ^ 2 * (1.1025 - 1) := by ring
    · set q := Real.sqrt t with hq_def
      have htq : t = q ^ 2 := (Real.sq_sqrt ht0.le).symm
      have hlog : Real.log t ≤ 2 * (q - 1) := by
        have h := Real.log_le_sub_one_of_pos hq0
        rw [hq_def, Real.log_sqrt ht0.le] at h
        linarith
      have hqne : q ≠ 0 := hq0.ne'
      rw [rpow_neg_two ht0, rpow_five_half ht0, ← hq_def]
      have hbq : b t * q ^ 2 ≤ 1.19073 := by rw [← htq]; exact hbt
      have hbq0 : 0 ≤ b t * q ^ 2 := by positivity
      have hb2 : (b t * q ^ 2) ^ 2 ≤ 1.19073 ^ 2 := pow_le_pow_left₀ hbq0 hbq 2
      have e : 2 * 1.19073 ^ 2 * ((t ^ 2)⁻¹ - (t ^ 2 * q)⁻¹) =
          2 * (q - 1) * 1.19073 ^ 2 / q ^ 5 := by
        rw [htq]
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have hstep : Real.log t / q * b t ^ 2 * q ^ 5 = Real.log t * (b t * q ^ 2) ^ 2 := by
        field_simp
      rw [hstep]
      calc Real.log t * (b t * q ^ 2) ^ 2 ≤ 2 * (q - 1) * (b t * q ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_right hlog (sq_nonneg _)
        _ ≤ 2 * (q - 1) * 1.19073 ^ 2 :=
            mul_le_mul_of_nonneg_left hb2 (by linarith)
  have hnn : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ Real.log t / Real.sqrt t * b t ^ 2 := fun t ht =>
    mul_nonneg (div_nonneg (Real.log_nonneg (le_of_lt ht)) (Real.sqrt_nonneg t)) (sq_nonneg _)
  have hI := integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioi hnn) hm
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [hval] at hI
  exact hI

/-! ## `E ≤ 8.4031·10⁻¹²·x` -/

/-- `log(4.9·10²⁶) ≤ 61.5` (`e^{61.5} ≥ 2.7182818283⁶¹·1.64`). -/
theorem log_x0_le : Real.log (49 * 10 ^ 25) ≤ 61.5 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (61.5 : ℝ) = (61 : ℕ) + 1 / 2 by norm_num,
    Real.exp_add, ← Real.exp_one_pow]
  have he := Real.exp_one_gt_d9
  have hh := HW.exp_half_gt
  have hp : (2.7182818283 : ℝ) ^ 61 ≤ Real.exp 1 ^ 61 := pow_le_pow_left₀ (by norm_num) he.le 61
  have hn : (49 : ℝ) * 10 ^ 25 ≤ 2.7182818283 ^ 61 * 1.64 := by norm_num
  calc (49 : ℝ) * 10 ^ 25 ≤ 2.7182818283 ^ 61 * 1.64 := hn
    _ ≤ Real.exp 1 ^ 61 * Real.exp (1 / 2) :=
        mul_le_mul hp hh.le (by norm_num) (by positivity)

/-- **`MinSp.Dubistdie η` for EVERY `η`** — `E ≤ 8.4031·10⁻¹²·x` at `x ≥ 4.9·10²⁶`. DISCHARGED. -/
theorem dubistdie_all (η : ℝ → ℝ) : MinSp.Dubistdie η := by
  intro h1 h2 b hb x hx
  obtain ⟨hb00, hb0a, -⟩ := supFn_bounds η b h1 h2 hb le_rfl
  have hI0 := int0_le η b h1 h2 hb
  have hI1 := int1_le η b h1 h2 hb
  have hC0 : MinSp.cE0 b ≤ 0.7131 * (1.079955 ^ 2 * 2.1 + 1.19073 ^ 2 * (2 / 3 / 1.05 ^ 3)) := by
    unfold MinSp.cE0
    exact mul_le_mul_of_nonneg_left hI0 (by norm_num)
  have hC1 : MinSp.cE1 b ≤ 0.7131 * (1.079955 ^ 2 * (1.1025 - 1) * (1.1025 - 1) +
      2 * 1.19073 ^ 2 * ((1.1025 : ℝ)⁻¹ - 2 / 3 / 1.05 ^ 3)) := by
    unfold MinSp.cE1
    exact mul_le_mul_of_nonneg_left hI1 (by norm_num)
  have hb0sq : b 0 ^ 2 ≤ 1.079955 ^ 2 := pow_le_pow_left₀ hb00 hb0a 2
  -- the scale: `w = √(x/x₀)`
  have hx0 : (0 : ℝ) < 49 * 10 ^ 25 := by norm_num
  have hxp : 0 < x := lt_of_lt_of_le hx0 hx
  have hr : 1 ≤ x / (49 * 10 ^ 25) := by rw [le_div_iff₀ hx0]; linarith
  set w := Real.sqrt (x / (49 * 10 ^ 25)) with hw_def
  have hw1 : 1 ≤ w := Real.one_le_sqrt.mpr hr
  have hw0 : 0 < w := by linarith
  have hxx : x = 49 * 10 ^ 25 * (x / (49 * 10 ^ 25)) := by field_simp
  have hsx : Real.sqrt x = Real.sqrt (49 * 10 ^ 25) * w := by
    rw [hw_def, ← Real.sqrt_mul hx0.le, ← hxx]
  have hsx0 := MajSp.sqrt_x_ge (49 * 10 ^ 25) le_rfl
  have hlogx : Real.log x = Real.log (49 * 10 ^ 25) + 2 * Real.log w := by
    rw [hw_def, Real.log_sqrt (le_trans zero_le_one hr)]
    conv_lhs => rw [hxx]
    rw [Real.log_mul hx0.ne' (div_pos hxp hx0).ne']
    ring
  have hlw := Real.log_le_sub_one_of_pos hw0
  have hL0 := log_x0_le
  have hlog1 := MajSp.log_ge_one x hx
  -- the constants
  set A : ℝ := 0.7131 * (1.079955 ^ 2 * 2.1 + 1.19073 ^ 2 * (2 / 3 / 1.05 ^ 3)) +
    0.51942 * 1.079955 ^ 2 with hA_def
  set B : ℝ := 2 * (0.7131 * (1.079955 ^ 2 * 2.1 + 1.19073 ^ 2 * (2 / 3 / 1.05 ^ 3))) +
    0.7131 * (1.079955 ^ 2 * (1.1025 - 1) * (1.1025 - 1) +
      2 * 1.19073 ^ 2 * ((1.1025 : ℝ)⁻¹ - 2 / 3 / 1.05 ^ 3)) with hB_def
  have hA0 : 0 ≤ A := by rw [hA_def]; norm_num
  have hK1 : A * 61.5 + B ≤ 8.4031e-12 * (22135943 * 10 ^ 6) := by rw [hA_def, hB_def]; norm_num
  have hK2 : 2 * A ≤ 8.4031e-12 * (22135943 * 10 ^ 6) := by rw [hA_def]; norm_num
  have hin1 : (MinSp.cE0 b + 0.51942 * b 0 ^ 2) * Real.log x ≤ A * Real.log x :=
    mul_le_mul_of_nonneg_right (by rw [hA_def]; linarith) (by linarith)
  have hin2 : 2 * MinSp.cE0 b + MinSp.cE1 b ≤ B := by rw [hB_def]; linarith
  have hlx : Real.log x ≤ 61.5 + 2 * (w - 1) := by rw [hlogx]; linarith
  have hmain : A * Real.log x + B ≤ 8.4031e-12 * Real.sqrt x := by
    have h3 : A * Real.log x ≤ A * (61.5 + 2 * (w - 1)) := mul_le_mul_of_nonneg_left hlx hA0
    have h4 : 8.4031e-12 * (22135943 * 10 ^ 6) * w ≤ 8.4031e-12 * Real.sqrt x := by
      rw [hsx, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsx0 hw0.le) (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hK2) (sub_nonneg.mpr hw1)]
  unfold MinSp.eBig
  have hs0 := Real.sqrt_nonneg x
  calc ((MinSp.cE0 b + 0.51942 * b 0 ^ 2) * Real.log x + (2 * MinSp.cE0 b + MinSp.cE1 b)) *
        Real.sqrt x ≤ (A * Real.log x + B) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (by linarith) hs0
    _ ≤ 8.4031e-12 * Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hmain hs0
    _ = 8.4031e-12 * x := by rw [mul_assoc, Real.mul_self_sqrt hxp.le]

end Principia.Common.TernaryGoldbach.DB
