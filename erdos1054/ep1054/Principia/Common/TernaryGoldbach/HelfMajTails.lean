/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMalTail

set_option autoImplicit false

/-!
# The zero-tail integrals `HM.PhiTailInt` and `HM.PlusTailInt` — PROVED

`phiTailInt_holds : HM.PhiTailInt` (`lem:festavign`, majarcs 3860–3981) and
`plusTailInt_holds : HM.PlusTailInt` (`lem:schastya`, 4262–4336), both at the spine's statement:
twice Helfgott's printed one-sided closed form, `+10 %`, against the two-sided density
`gw(q,t) = max((1/π) log(qt/2π), 0) + 1/(2t)`.

## The method: one exponential per term, no closed-form incomplete gammas

Every factor of the integrand is dominated, for `t = T + u ≥ T`, by its value at `T` times an
exponential in `u`:

* `log(qt/2π) = L + log(t/T) ≤ L + u/T ≤ L·e^{u/(TL)}`, `L = log(qT/2π)` (`logw_le_shift`);
* `t ≤ T e^{u/T}` and `√t ≤ √v e^{(t − v)/(2v)}` (`1 + x ≤ eˣ`);
* the Gaussian factors, in `s = t/a` (`a = π|δ|`, `S = T/a ≥ 4π`):
  `s²e^{−ks²} ≤ S²e^{−kS²}e^{−(2kS² − 2)(s − S)/S}` and
  `se^{−ks²} ≤ Se^{−kS²}e^{−(2kS² − 1)(s − S)/S}` (`(s − S)² ≥ 0` and `s ≤ Se^{s/S − 1}`), where
  `(s − S)/S = u/T`.

So the integrand is at most `∑ Aᵢ e^{−λᵢ u}` and its integral at most `∑ Aᵢ/λᵢ`
(`lint_le_exp3`). The rates are `0.1557` (`φ`, exponential part: `c − 1/T − 1/(TL) ≥ 0.1557` at
`T ≥ 333`, `L ≥ 3`), `0.198 S²/T` and `0.2 S²/T` (`φ`, Gaussian part: `2kS² − 2 − 1/L ≥ 0.198 S²`
needs `S² ≥ 155.6`, and `S² ≥ 16π² ≥ 157.9`), `0.1572` (`η₊`), `0.205 S²/v` and `0.2 S²/v` (`η₊`,
`v = T − 200`).

## Margins (the bounds proved against the right sides, `1/π ≤ 0.31832`)

| link | part | proved coefficient | stated |
|---|---|---|---|
| `PhiTailInt` | `TL e^{−0.1598T}` | `3.262/(0.1557π) = 6.669` (+`10.48 e^{−0.1598T}`) | `7.7` |
| `PhiTailInt` | `TL e^{−0.1065S²}` | `3.262/(0.792π) = 1.311` (+`2.04 e^{−0.1065S²}`) | `1.408` |
| `PlusTailInt` | `√v e^{−0.1598v} L` | `9.062/(0.1572π) = 18.35` (+`0.064/L`) | `20.82` |
| `PlusTailInt` | `|δ| e^{−0.1065S²} L` | `9.062/0.41 = 22.10` (+`0.08/L`) | `24.83` |

(The spine's mpmath worst ratios of the exact integrals, `0.8981` and `0.8814`, sit below these.)
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set

/-! ## (1) Integrals of shifted exponentials -/

/-- `e^{−l(t − T)} = e^{lT}e^{−lt}`. -/
theorem exp_shift_eq (T l : ℝ) :
    (fun t => Real.exp (-l * (t - T))) = fun t => Real.exp (l * T) * Real.exp (-l * t) := by
  funext t
  rw [← Real.exp_add]
  ring_nf

/-- `∫_{t > T} e^{−l(t − T)} dt = 1/l`. -/
theorem integral_exp_shift (T : ℝ) {l : ℝ} (hl : 0 < l) :
    ∫ t in Ioi T, Real.exp (-l * (t - T)) = 1 / l := by
  have h1 : Real.exp (l * T) * Real.exp (-l * T) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [exp_shift_eq, integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hl) T,
    neg_div_neg_eq, mul_div_assoc', h1]

/-- `e^{−l(t − T)}` is integrable on `(T, ∞)`. -/
theorem integrableOn_exp_shift (T : ℝ) {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun t => Real.exp (-l * (t - T))) (Ioi T) := by
  rw [exp_shift_eq]
  exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hl) T).const_mul _

/-- **Three exponentials dominate**: `f ≤ ∑ Aᵢe^{−lᵢ(t − T)}` on `(T, ∞)` gives
`∫⁻_{t > T} f ≤ ∑ Aᵢ/lᵢ`. -/
theorem lint_le_exp3 {f : ℝ → ℝ} {T A1 A2 A3 l1 l2 l3 : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hA3 : 0 ≤ A3) (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3)
    (hf : ∀ t ∈ Ioi T, f t ≤ A1 * Real.exp (-l1 * (t - T)) + A2 * Real.exp (-l2 * (t - T)) +
      A3 * Real.exp (-l3 * (t - T))) :
    ∫⁻ t in Ioi T, ENNReal.ofReal (f t) ≤ ENNReal.ofReal (A1 / l1 + A2 / l2 + A3 / l3) := by
  have i1 := (integrableOn_exp_shift T hl1).const_mul A1
  have i2 := (integrableOn_exp_shift T hl2).const_mul A2
  have i3 := (integrableOn_exp_shift T hl3).const_mul A3
  have hg : IntegrableOn (fun t => A1 * Real.exp (-l1 * (t - T)) +
      A2 * Real.exp (-l2 * (t - T)) + A3 * Real.exp (-l3 * (t - T))) (Ioi T) :=
    (i1.add i2).add i3
  have hval : ∫ t in Ioi T, (A1 * Real.exp (-l1 * (t - T)) + A2 * Real.exp (-l2 * (t - T)) +
      A3 * Real.exp (-l3 * (t - T))) = A1 / l1 + A2 / l2 + A3 / l3 := by
    have i12 : Integrable (fun t => A1 * Real.exp (-l1 * (t - T)) +
        A2 * Real.exp (-l2 * (t - T))) (volume.restrict (Ioi T)) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_exp_shift T hl1, integral_exp_shift T hl2,
      integral_exp_shift T hl3]
    ring
  have hnn : ∀ t : ℝ, 0 ≤ A1 * Real.exp (-l1 * (t - T)) + A2 * Real.exp (-l2 * (t - T)) +
      A3 * Real.exp (-l3 * (t - T)) := fun t =>
    add_nonneg (add_nonneg (mul_nonneg hA1 (Real.exp_pos _).le)
      (mul_nonneg hA2 (Real.exp_pos _).le)) (mul_nonneg hA3 (Real.exp_pos _).le)
  calc ∫⁻ t in Ioi T, ENNReal.ofReal (f t)
      ≤ ∫⁻ t in Ioi T, ENNReal.ofReal (A1 * Real.exp (-l1 * (t - T)) +
          A2 * Real.exp (-l2 * (t - T)) + A3 * Real.exp (-l3 * (t - T))) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => ENNReal.ofReal_le_ofReal (hf t ht)
    _ = ENNReal.ofReal (∫ t in Ioi T, (A1 * Real.exp (-l1 * (t - T)) +
          A2 * Real.exp (-l2 * (t - T)) + A3 * Real.exp (-l3 * (t - T)))) :=
        (ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hnn)).symm
    _ = ENNReal.ofReal (A1 / l1 + A2 / l2 + A3 / l3) := by rw [hval]

/-! ## (2) Pointwise domination -/

/-- `t ≤ T e^{(t − T)/T}` for `T > 0`. -/
theorem lin_le_exp_shift {T : ℝ} (t : ℝ) (hT : 0 < T) : t ≤ T * Real.exp ((t - T) / T) := by
  have e : T * ((t - T) / T + 1) = t := by
    rw [mul_add, mul_div_cancel₀ _ hT.ne']
    ring
  calc t = T * ((t - T) / T + 1) := e.symm
    _ ≤ T * Real.exp ((t - T) / T) := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hT.le

/-- `√t ≤ √v e^{(t − v)/(2v)}` for `v > 0`. -/
theorem sqrt_le_exp_shift {v : ℝ} (t : ℝ) (hv : 0 < v) :
    Real.sqrt t ≤ Real.sqrt v * Real.exp ((t - v) / (2 * v)) := by
  have h1 : t ≤ v * Real.exp ((t - v) / (2 * v)) ^ 2 := by
    have e : Real.exp ((t - v) / (2 * v)) ^ 2 = Real.exp ((t - v) / v) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
      ring
    rw [e]
    exact lin_le_exp_shift t hv
  calc Real.sqrt t ≤ Real.sqrt (v * Real.exp ((t - v) / (2 * v)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt v * Real.exp ((t - v) / (2 * v)) := by
        rw [Real.sqrt_mul hv.le, Real.sqrt_sq (Real.exp_pos _).le]

/-- **The density, by its value at `T`**: `max((1/π) log(qt/2π), 0) ≤ (L/π) e^{(t − T)/(TL)}`,
`L = log(qT/2π) > 0`, for `t ≥ T > 0`, `q > 0`. -/
theorem logw_le_shift {q T t : ℝ} (hq : 0 < q) (hT : 0 < T) (hTt : T ≤ t)
    (hL0 : 0 < Real.log (q * T / (2 * Real.pi))) :
    max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0 ≤
      Real.log (q * T / (2 * Real.pi)) / Real.pi *
        Real.exp ((t - T) / (T * Real.log (q * T / (2 * Real.pi)))) := by
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  have ht0 : 0 < t := lt_of_lt_of_le hT hTt
  have hTne : T ≠ 0 := hT.ne'
  have hLne : L ≠ 0 := hL0.ne'
  have hA : 0 < q * T / (2 * Real.pi) := div_pos (mul_pos hq hT) (by positivity)
  have h1 : Real.log (q * t / (2 * Real.pi)) = L + Real.log (t / T) := by
    rw [hLdef, ← Real.log_mul hA.ne' (div_pos ht0 hT).ne']
    congr 1
    field_simp
  have h2 : Real.log (t / T) ≤ (t - T) / T := by
    have := Real.log_le_sub_one_of_pos (div_pos ht0 hT)
    have e : t / T - 1 = (t - T) / T := by
      field_simp
    linarith
  have h3 : L + (t - T) / T ≤ L * Real.exp ((t - T) / (T * L)) := by
    have e : L * ((t - T) / (T * L) + 1) = L + (t - T) / T := by
      field_simp
      ring
    rw [← e]
    exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hL0.le
  have h4 : Real.log (q * t / (2 * Real.pi)) ≤ L * Real.exp ((t - T) / (T * L)) := by
    linarith
  have e5 : L / Real.pi * Real.exp ((t - T) / (T * L)) =
      L * Real.exp ((t - T) / (T * L)) / Real.pi := by ring
  rw [e5]
  exact max_le (div_le_div_of_nonneg_right h4 Real.pi_pos.le)
    (div_nonneg (mul_nonneg hL0.le (Real.exp_pos _).le) Real.pi_pos.le)

/-- **The squared Gaussian by its value at `S`**: for `0 < S ≤ s`, `k ≥ 0`,
`s²e^{−ks²} ≤ S²e^{−kS²}e^{−(2kS² − 2)((s − S)/S)}`. -/
theorem sq_gauss_tail {k S s : ℝ} (hk : 0 ≤ k) (hS : 0 < S) (hs : S ≤ s) :
    s ^ 2 * Real.exp (-k * s ^ 2) ≤
      S ^ 2 * Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S ^ 2 - 2) * ((s - S) / S)) := by
  have hs0 : 0 ≤ s := by linarith
  have hSne : S ≠ 0 := hS.ne'
  have h1 := lin_le_exp_shift s hS
  have h2 : s ^ 2 ≤ S ^ 2 * Real.exp (2 * ((s - S) / S)) := by
    have := pow_le_pow_left₀ hs0 h1 2
    rw [mul_pow, ← Real.exp_nat_mul] at this
    exact_mod_cast this
  have h3 : Real.exp (-k * s ^ 2) ≤ Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S) * (s - S)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hk (sq_nonneg (s - S))])
  have e : 2 * ((s - S) / S) + -(2 * k * S) * (s - S) = -(2 * k * S ^ 2 - 2) * ((s - S) / S) := by
    field_simp
    ring
  calc s ^ 2 * Real.exp (-k * s ^ 2)
      ≤ S ^ 2 * Real.exp (2 * ((s - S) / S)) *
          (Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S) * (s - S))) :=
        mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
    _ = S ^ 2 * Real.exp (-k * S ^ 2) *
          Real.exp (2 * ((s - S) / S) + -(2 * k * S) * (s - S)) := by
        rw [Real.exp_add]
        ring
    _ = S ^ 2 * Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S ^ 2 - 2) * ((s - S) / S)) := by
        rw [e]

/-- **The linear Gaussian by its value at `S`**: for `0 < S`, `k ≥ 0`,
`se^{−ks²} ≤ Se^{−kS²}e^{−(2kS² − 1)((s − S)/S)}` (for every `s`). -/
theorem lin_gauss_tail {k S : ℝ} (s : ℝ) (hk : 0 ≤ k) (hS : 0 < S) :
    s * Real.exp (-k * s ^ 2) ≤
      S * Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S ^ 2 - 1) * ((s - S) / S)) := by
  have hSne : S ≠ 0 := hS.ne'
  have h1 := lin_le_exp_shift s hS
  have h3 : Real.exp (-k * s ^ 2) ≤ Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S) * (s - S)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hk (sq_nonneg (s - S))])
  have e : (s - S) / S + -(2 * k * S) * (s - S) = -(2 * k * S ^ 2 - 1) * ((s - S) / S) := by
    field_simp
    ring
  calc s * Real.exp (-k * s ^ 2)
      ≤ S * Real.exp ((s - S) / S) *
          (Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S) * (s - S))) :=
        mul_le_mul h1 h3 (Real.exp_pos _).le (mul_nonneg hS.le (Real.exp_pos _).le)
    _ = S * Real.exp (-k * S ^ 2) * Real.exp ((s - S) / S + -(2 * k * S) * (s - S)) := by
        rw [Real.exp_add]
        ring
    _ = S * Real.exp (-k * S ^ 2) * Real.exp (-(2 * k * S ^ 2 - 1) * ((s - S) / S)) := by
        rw [e]

/-- `(u/(πδ))² = (u/(π|δ|))²`. -/
theorem sq_div_pi_abs (u δ : ℝ) : (u / (Real.pi * δ)) ^ 2 = (u / (Real.pi * |δ|)) ^ 2 := by
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]

/-- `u/(2π|δ|) = (u/(π|δ|))/2`. -/
theorem div_two_pi_abs (u δ : ℝ) : u / (2 * Real.pi * |δ|) = u / (Real.pi * |δ|) / 2 := by
  rw [div_div, mul_comm (Real.pi * |δ|) 2, mul_assoc]

/-- `1/π ≤ 0.31832`. -/
theorem inv_pi_le : 1 / Real.pi ≤ 0.31832 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_d6]

/-- `(4π)² ≥ 157.9`. -/
theorem sixteen_pi_sq : (157.9 : ℝ) ≤ (4 * Real.pi) ^ 2 := by
  have h : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  have h2 : (4 * 3.141592 : ℝ) ^ 2 ≤ (4 * Real.pi) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h3 : (157.9 : ℝ) ≤ (4 * 3.141592) ^ 2 := by norm_num
  linarith

/-! ## (3) `PhiTailInt` -/

/-- The exponential part of `lem:festavign`'s integrand: for `t > T ≥ 333`, `L ≥ 3`,
`t e^{−0.1598t}·gw(q,t) ≤ e^{−0.1598T}(TL/π + 1/2)e^{−0.1557(t − T)}`. -/
theorem phi_exp_pt {q T t : ℝ} (hq : 1 ≤ q) (hT : 333 ≤ T) (hTt : T < t)
    (hL3 : 3 ≤ Real.log (q * T / (2 * Real.pi))) :
    t * Real.exp (-0.1598 * t) * gw q t ≤
      Real.exp (-0.1598 * T) * (T * Real.log (q * T / (2 * Real.pi)) / Real.pi + 1 / 2) *
        Real.exp (-0.1557 * (t - T)) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hm := logw_le_shift (q := q) (by linarith) hT0 hTt.le (by linarith)
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  have hlin := lin_le_exp_shift t hT0
  have hTL : 999 ≤ T * L := by nlinarith [mul_nonneg (sub_nonneg.2 hT) (sub_nonneg.2 hL3)]
  have hu : 0 ≤ t - T := by linarith
  have hd1 : (t - T) / T ≤ (t - T) / 333 := div_le_div_of_nonneg_left hu (by norm_num) hT
  have hd2 : (t - T) / (T * L) ≤ (t - T) / 999 :=
    div_le_div_of_nonneg_left hu (by norm_num) hTL
  have hE1 : Real.exp ((t - T) / T) * Real.exp (-0.1598 * t) *
      Real.exp ((t - T) / (T * L)) ≤ Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hE2 : Real.exp (-0.1598 * t) ≤ Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hLp : 0 ≤ L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have hA : t * Real.exp (-0.1598 * t) *
      max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0 ≤
        T * L / Real.pi * (Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T))) := by
    have p1 := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-0.1598 * t)).le
    have p2 := mul_le_mul p1 hm (le_max_right _ _)
      (mul_nonneg (mul_nonneg hT0.le (Real.exp_pos _).le) (Real.exp_pos _).le)
    have p3 := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hT0.le hLp)
    calc t * Real.exp (-0.1598 * t) * max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0
        ≤ T * Real.exp ((t - T) / T) * Real.exp (-0.1598 * t) *
            (L / Real.pi * Real.exp ((t - T) / (T * L))) := p2
      _ = T * (L / Real.pi) * (Real.exp ((t - T) / T) * Real.exp (-0.1598 * t) *
            Real.exp ((t - T) / (T * L))) := by ring
      _ ≤ T * (L / Real.pi) * (Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T))) := p3
      _ = T * L / Real.pi * (Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T))) := by ring
  have hB : t * Real.exp (-0.1598 * t) * (1 / (2 * t)) = Real.exp (-0.1598 * t) / 2 := by
    have htne : t ≠ 0 := ht0.ne'
    field_simp
  unfold gw
  rw [mul_add, hB]
  have := div_le_div_of_nonneg_right hE2 (by norm_num : (0 : ℝ) ≤ 2)
  have e : Real.exp (-0.1598 * T) * (T * L / Real.pi + 1 / 2) * Real.exp (-0.1557 * (t - T)) =
      T * L / Real.pi * (Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T))) +
        Real.exp (-0.1598 * T) * Real.exp (-0.1557 * (t - T)) / 2 := by ring
  rw [e]
  linarith

/-- The Gaussian part of `lem:festavign`'s integrand (`δ ≠ 0`, `S = T/(π|δ|) ≥ 4π`,
`e' = e^{−0.1065S²}`): `(t/2π|δ|)²e^{−0.1065(t/πδ)²}·gw(q,t) ≤
(S²/4)e'(L/π)e^{−(0.198S²/T)(t − T)} + (S²/4)e'/(2T)·e^{−(0.2S²/T)(t − T)}`. -/
theorem phi_gauss_pt {q T t δ : ℝ} (hδ : δ ≠ 0) (hq : 1 ≤ q) (hT : 333 ≤ T)
    (hTd : 4 * Real.pi ^ 2 * |δ| ≤ T) (hTt : T < t)
    (hL3 : 3 ≤ Real.log (q * T / (2 * Real.pi))) :
    (t / (2 * Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (t / (Real.pi * δ)) ^ 2) * gw q t ≤
      (T / (Real.pi * |δ|)) ^ 2 / 4 * Real.exp (-0.1065 * (T / (Real.pi * |δ|)) ^ 2) *
          (Real.log (q * T / (2 * Real.pi)) / Real.pi) *
          Real.exp (-(0.198 * (T / (Real.pi * |δ|)) ^ 2 / T) * (t - T)) +
        (T / (Real.pi * |δ|)) ^ 2 / 4 * Real.exp (-0.1065 * (T / (Real.pi * |δ|)) ^ 2) /
          (2 * T) * Real.exp (-(0.2 * (T / (Real.pi * |δ|)) ^ 2 / T) * (t - T)) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hm := logw_le_shift (q := q) (by linarith) hT0 hTt.le (by linarith)
  have hd : 0 < |δ| := abs_pos.mpr hδ
  have ha0 : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
  have hG : (t / (2 * Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (t / (Real.pi * δ)) ^ 2) =
      (t / (Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (t / (Real.pi * |δ|)) ^ 2) / 4 := by
    rw [sq_div_pi_abs, div_two_pi_abs]
    ring
  rw [hG]
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  set a := Real.pi * |δ| with ha
  have hane : a ≠ 0 := ha0.ne'
  have hTne : T ≠ 0 := hT0.ne'
  set S := T / a with hS
  set E := Real.exp (-0.1065 * S ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hS4 : 4 * Real.pi ≤ S := by
    rw [hS, le_div_iff₀ ha0]
    have e : 4 * Real.pi * a = 4 * Real.pi ^ 2 * |δ| := by rw [ha]; ring
    linarith
  have hS2 : 157.9 ≤ S ^ 2 := le_trans sixteen_pi_sq (pow_le_pow_left₀ (by positivity) hS4 2)
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS4
  have hsS : S ≤ t / a := div_le_div_of_nonneg_right hTt.le ha0.le
  have hratio : (t / a - S) / S = (t - T) / T := by
    rw [hS]
    field_simp
  have hg := sq_gauss_tail (k := 0.1065) (by norm_num) hS0 hsS
  rw [hratio] at hg
  set w := (t - T) / T with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hT0.le
  have hTL : 3 * T ≤ T * L := by nlinarith
  have hwL : (t - T) / (T * L) ≤ w / 3 := by
    have e : w / 3 = (t - T) / (3 * T) := by rw [hw]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) hTL
  have hr1 : -(2 * 0.1065 * S ^ 2 - 2) * w + (t - T) / (T * L) ≤
      -(0.198 * S ^ 2 / T) * (t - T) := by
    have e : -(0.198 * S ^ 2 / T) * (t - T) = -(0.198 * S ^ 2) * w := by rw [hw]; ring
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.015 * S ^ 2 - 7 / 3) hw0]
  have hr2 : -(2 * 0.1065 * S ^ 2 - 2) * w ≤ -(0.2 * S ^ 2 / T) * (t - T) := by
    have e : -(0.2 * S ^ 2 / T) * (t - T) = -(0.2 * S ^ 2) * w := by rw [hw]; ring
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.013 * S ^ 2 - 2) hw0]
  have hmain : (t / a) ^ 2 * Real.exp (-0.1065 * (t / a) ^ 2) / 4 ≤
      S ^ 2 * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) / 4 := by
    rw [hE]
    linarith
  have hh : 1 / (2 * t) ≤ 1 / (2 * T) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hL0 : 0 ≤ L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have hX0 : 0 ≤ S ^ 2 * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) / 4 := by positivity
  unfold gw
  rw [mul_add]
  have p1 : (t / a) ^ 2 * Real.exp (-0.1065 * (t / a) ^ 2) / 4 *
      max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0 ≤
        S ^ 2 / 4 * E * (L / Real.pi) * Real.exp (-(0.198 * S ^ 2 / T) * (t - T)) := by
    have q1 := mul_le_mul hmain hm (le_max_right _ _) hX0
    have q2 : Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) *
        Real.exp ((t - T) / (T * L)) ≤ Real.exp (-(0.198 * S ^ 2 / T) * (t - T)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hr1
    have q3 := mul_le_mul_of_nonneg_left q2
      (mul_nonneg (by positivity : (0 : ℝ) ≤ S ^ 2 / 4 * E) hL0)
    calc (t / a) ^ 2 * Real.exp (-0.1065 * (t / a) ^ 2) / 4 *
          max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0
        ≤ S ^ 2 * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) / 4 *
            (L / Real.pi * Real.exp ((t - T) / (T * L))) := q1
      _ = S ^ 2 / 4 * E * (L / Real.pi) * (Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) *
            Real.exp ((t - T) / (T * L))) := by ring
      _ ≤ S ^ 2 / 4 * E * (L / Real.pi) * Real.exp (-(0.198 * S ^ 2 / T) * (t - T)) := q3
  have p2 : (t / a) ^ 2 * Real.exp (-0.1065 * (t / a) ^ 2) / 4 * (1 / (2 * t)) ≤
      S ^ 2 / 4 * E / (2 * T) * Real.exp (-(0.2 * S ^ 2 / T) * (t - T)) := by
    have q1 := mul_le_mul hmain hh (by positivity) hX0
    have q2 : Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) ≤
        Real.exp (-(0.2 * S ^ 2 / T) * (t - T)) := Real.exp_le_exp.mpr hr2
    have q3 := mul_le_mul_of_nonneg_left q2 (by positivity : (0 : ℝ) ≤ S ^ 2 / 4 * E / (2 * T))
    calc (t / a) ^ 2 * Real.exp (-0.1065 * (t / a) ^ 2) / 4 * (1 / (2 * t))
        ≤ S ^ 2 * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) / 4 * (1 / (2 * T)) := q1
      _ = S ^ 2 / 4 * E / (2 * T) * Real.exp (-(2 * 0.1065 * S ^ 2 - 2) * w) := by ring
      _ ≤ S ^ 2 / 4 * E / (2 * T) * Real.exp (-(0.2 * S ^ 2 / T) * (t - T)) := q3
  linarith

/-- **`PhiTailInt` PROVED.** -/
theorem phiTailInt_holds : PhiTailInt := by
  intro q hq1 _ δ T hT hTd
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hT0 : 0 < T := by linarith
  have hL3 : 3 ≤ Real.log (q * T / (2 * Real.pi)) := by
    have h := nat_le_log 3 (y := q * T / (2 * Real.pi)) (by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2])
    push_cast at h
    exact h
  have hpi := inv_pi_le
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  set ε := Real.exp (-0.1598 * T) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hTL : 999 ≤ T * L := by nlinarith [mul_nonneg (sub_nonneg.2 hT) (sub_nonneg.2 hL3)]
  have hLp : 0 ≤ L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have hA1 : 0 ≤ 3.262 * (ε * (T * L / Real.pi + 1 / 2)) := by
    have : 0 ≤ T * L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
    positivity
  -- the exponential part, integrated: `ε(TL/π + 1/2)/0.1557 ≤ 7.7·TLε`
  have hexp : 3.262 * (ε * (T * L / Real.pi + 1 / 2)) / 0.1557 ≤ 2.2 * T * L * (3.5 * ε) := by
    have e : T * L / Real.pi = T * L * (1 / Real.pi) := by ring
    rw [e]
    have h1 : ε * (T * L) * (1 / Real.pi) ≤ ε * (T * L) * 0.31832 :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    have h2 : ε * 999 ≤ ε * (T * L) := mul_le_mul_of_nonneg_left hTL hε0.le
    rw [div_le_iff₀ (by norm_num)]
    linarith
  rcases eq_or_ne δ 0 with hδ | hδ
  · -- `δ = 0`: the Gaussian part vanishes
    subst hδ
    have hgq : gq T 0 = 0 := by simp [gq]
    rw [hgq]
    have hb := lint_le_exp3 (f := fun t => fphi 0 t * gw q t) (T := T)
      (A1 := 3.262 * (ε * (T * L / Real.pi + 1 / 2))) (A2 := 0) (A3 := 0)
      (l1 := 0.1557) (l2 := 1) (l3 := 1) hA1 le_rfl le_rfl (by norm_num)
      one_pos one_pos (fun t ht => by
        have ht' : T < t := ht
        have hp := phi_exp_pt hq1' hT ht' hL3
        rw [← hLdef, ← hε] at hp
        have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3.262)
        change fphi 0 t * gw q t ≤ _
        simp only [fphi, abs_zero, mul_zero, div_zero, zero_pow two_ne_zero, zero_mul, add_zero]
        linarith)
    refine le_trans hb (ENNReal.ofReal_le_ofReal ?_)
    simp only [zero_div, add_zero, mul_zero]
    exact hexp
  · -- `δ ≠ 0`
    have hd : 0 < |δ| := abs_pos.mpr hδ
    have ha0 : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
    set a := Real.pi * |δ| with ha
    set S := T / a with hS
    have hS4 : 4 * Real.pi ≤ S := by
      rw [hS, le_div_iff₀ ha0]
      have e : 4 * Real.pi * a = 4 * Real.pi ^ 2 * |δ| := by rw [ha]; ring
      linarith
    have hS2 : 157.9 ≤ S ^ 2 := le_trans sixteen_pi_sq (pow_le_pow_left₀ (by positivity) hS4 2)
    have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS4
    have hSne : S ≠ 0 := hS0.ne'
    have hTne : T ≠ 0 := hT0.ne'
    set E := Real.exp (-0.1065 * S ^ 2) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hgq : gq T δ = E := by
      unfold gq
      rw [if_neg hδ, sq_div_pi_abs, hE, hS, ha]
    rw [hgq]
    have hb := lint_le_exp3 (f := fun t => fphi δ t * gw q t) (T := T)
      (A1 := 3.262 * (ε * (T * L / Real.pi + 1 / 2)))
      (A2 := 3.262 * (S ^ 2 / 4 * E * (L / Real.pi)))
      (A3 := 3.262 * (S ^ 2 / 4 * E / (2 * T)))
      (l1 := 0.1557) (l2 := 0.198 * S ^ 2 / T) (l3 := 0.2 * S ^ 2 / T) hA1
      (mul_nonneg (by norm_num) (mul_nonneg (by positivity) hLp))
      (by positivity) (by norm_num) (by positivity) (by positivity) (fun t ht => by
        have ht' : T < t := ht
        have hp := phi_exp_pt hq1' hT ht' hL3
        rw [← hLdef, ← hε] at hp
        have hg := phi_gauss_pt hδ hq1' hT hTd ht' hL3
        rw [← ha, ← hS, ← hE, ← hLdef] at hg
        have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3.262)
        have hg' := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 3.262)
        change fphi δ t * gw q t ≤ _
        unfold fphi
        linarith)
    refine le_trans hb (ENNReal.ofReal_le_ofReal ?_)
    -- the Gaussian part, integrated
    have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
    have e2 : 3.262 * (S ^ 2 / 4 * E * (L / Real.pi)) / (0.198 * S ^ 2 / T) =
        3.262 / 0.792 * (E * (T * L) * (1 / Real.pi)) := by
      field_simp
      ring
    have e3 : 3.262 * (S ^ 2 / 4 * E / (2 * T)) / (0.2 * S ^ 2 / T) = 3.262 / 1.6 * E := by
      field_simp
      ring
    rw [e2, e3]
    have h1 : E * (T * L) * (1 / Real.pi) ≤ E * (T * L) * 0.31832 :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    have h2 : E * 999 ≤ E * (T * L) := mul_le_mul_of_nonneg_left hTL hE0.le
    have e4 : 2.2 * T * L * (3.5 * ε + 0.64 * E) =
        2.2 * T * L * (3.5 * ε) + 1.408 * (E * (T * L)) := by ring
    rw [e4]
    linarith

/-! ## (4) `PlusTailInt` -/

/-- The exponential part of `lem:schastya`'s integrand: for `t > T ≥ 450`, `L ≥ 4`,
`√(t − 200)e^{−0.1598(t − 200)}·gw(q,t) ≤ √v e^{−0.1598v}(L/π + 1/(2T))e^{−0.1572(t − T)}`,
`v = T − 200`. -/
theorem plus_exp_pt {q T t : ℝ} (hq : 1 ≤ q) (hT : 450 ≤ T) (hTt : T < t)
    (hL4 : 4 ≤ Real.log (q * T / (2 * Real.pi))) :
    Real.sqrt (t - 200) * Real.exp (-0.1598 * (t - 200)) * gw q t ≤
      Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) *
        (Real.log (q * T / (2 * Real.pi)) / Real.pi + 1 / (2 * T)) *
        Real.exp (-0.1572 * (t - T)) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hv0 : 0 < T - 200 := by linarith
  have hm := logw_le_shift (q := q) (by linarith) hT0 hTt.le (by linarith)
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  have hsq := sqrt_le_exp_shift (t - 200) hv0
  have e0 : t - 200 - (T - 200) = t - T := by ring
  rw [e0] at hsq
  have hu : 0 ≤ t - T := by linarith
  have hTL : 1800 ≤ T * L := by nlinarith [mul_nonneg (sub_nonneg.2 hT) (sub_nonneg.2 hL4)]
  have hd1 : (t - T) / (2 * (T - 200)) ≤ (t - T) / 500 :=
    div_le_div_of_nonneg_left hu (by norm_num) (by linarith)
  have hd2 : (t - T) / (T * L) ≤ (t - T) / 1800 := div_le_div_of_nonneg_left hu (by norm_num) hTL
  have hE1 : Real.exp ((t - T) / (2 * (T - 200))) * Real.exp (-0.1598 * (t - 200)) *
      Real.exp ((t - T) / (T * L)) ≤ Real.exp (-0.1598 * (T - 200)) *
        Real.exp (-0.1572 * (t - T)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hE2 : Real.exp ((t - T) / (2 * (T - 200))) * Real.exp (-0.1598 * (t - 200)) ≤
      Real.exp (-0.1598 * (T - 200)) * Real.exp (-0.1572 * (t - T)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs0 : 0 ≤ Real.sqrt (T - 200) := Real.sqrt_nonneg _
  have hLp : 0 ≤ L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have hA : Real.sqrt (t - 200) * Real.exp (-0.1598 * (t - 200)) *
      max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0 ≤
        Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (L / Real.pi) *
          Real.exp (-0.1572 * (t - T)) := by
    have p1 := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-0.1598 * (t - 200))).le
    have p2 := mul_le_mul p1 hm (le_max_right _ _) (by positivity)
    have p3 := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hs0 hLp)
    calc Real.sqrt (t - 200) * Real.exp (-0.1598 * (t - 200)) *
          max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0
        ≤ Real.sqrt (T - 200) * Real.exp ((t - T) / (2 * (T - 200))) *
            Real.exp (-0.1598 * (t - 200)) * (L / Real.pi * Real.exp ((t - T) / (T * L))) := p2
      _ = Real.sqrt (T - 200) * (L / Real.pi) * (Real.exp ((t - T) / (2 * (T - 200))) *
            Real.exp (-0.1598 * (t - 200)) * Real.exp ((t - T) / (T * L))) := by ring
      _ ≤ Real.sqrt (T - 200) * (L / Real.pi) * (Real.exp (-0.1598 * (T - 200)) *
            Real.exp (-0.1572 * (t - T))) := p3
      _ = Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (L / Real.pi) *
            Real.exp (-0.1572 * (t - T)) := by ring
  have hB : Real.sqrt (t - 200) * Real.exp (-0.1598 * (t - 200)) * (1 / (2 * t)) ≤
      Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (1 / (2 * T)) *
        Real.exp (-0.1572 * (t - T)) := by
    have hh : 1 / (2 * t) ≤ 1 / (2 * T) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have p1 := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-0.1598 * (t - 200))).le
    have p2 := mul_le_mul p1 hh (by positivity) (by positivity)
    have p3 := mul_le_mul_of_nonneg_left hE2
      (mul_nonneg hs0 (by positivity : (0 : ℝ) ≤ 1 / (2 * T)))
    calc Real.sqrt (t - 200) * Real.exp (-0.1598 * (t - 200)) * (1 / (2 * t))
        ≤ Real.sqrt (T - 200) * Real.exp ((t - T) / (2 * (T - 200))) *
            Real.exp (-0.1598 * (t - 200)) * (1 / (2 * T)) := p2
      _ = Real.sqrt (T - 200) * (1 / (2 * T)) * (Real.exp ((t - T) / (2 * (T - 200))) *
            Real.exp (-0.1598 * (t - 200))) := by ring
      _ ≤ Real.sqrt (T - 200) * (1 / (2 * T)) * (Real.exp (-0.1598 * (T - 200)) *
            Real.exp (-0.1572 * (t - T))) := p3
      _ = Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (1 / (2 * T)) *
            Real.exp (-0.1572 * (t - T)) := by ring
  unfold gw
  rw [mul_add]
  have e : Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (L / Real.pi + 1 / (2 * T)) *
      Real.exp (-0.1572 * (t - T)) =
        Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (L / Real.pi) *
          Real.exp (-0.1572 * (t - T)) +
        Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) * (1 / (2 * T)) *
          Real.exp (-0.1572 * (t - T)) := by ring
  rw [e]
  linarith

/-- The Gaussian part of `lem:schastya`'s integrand (`δ ≠ 0`, `v = T − 200`, `S = v/(π|δ|) ≥ 4π`,
`e' = e^{−0.1065S²}`): `((t − 200)/2π|δ|)e^{−0.1065((t−200)/πδ)²}·gw(q,t) ≤
(S/2)e'(L/π)e^{−(0.205S²/v)(t − T)} + (S/2)e'/(2T)·e^{−(0.2S²/v)(t − T)}`. -/
theorem plus_gauss_pt {q T t δ : ℝ} (hδ : δ ≠ 0) (hq : 1 ≤ q) (hT : 450 ≤ T)
    (hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ T) (hTt : T < t)
    (hL4 : 4 ≤ Real.log (q * T / (2 * Real.pi))) :
    (t - 200) / (2 * Real.pi * |δ|) * Real.exp (-0.1065 * ((t - 200) / (Real.pi * δ)) ^ 2) *
        gw q t ≤
      (T - 200) / (Real.pi * |δ|) / 2 *
          Real.exp (-0.1065 * ((T - 200) / (Real.pi * |δ|)) ^ 2) *
          (Real.log (q * T / (2 * Real.pi)) / Real.pi) *
          Real.exp (-(0.205 * ((T - 200) / (Real.pi * |δ|)) ^ 2 / (T - 200)) * (t - T)) +
        (T - 200) / (Real.pi * |δ|) / 2 *
          Real.exp (-0.1065 * ((T - 200) / (Real.pi * |δ|)) ^ 2) / (2 * T) *
          Real.exp (-(0.2 * ((T - 200) / (Real.pi * |δ|)) ^ 2 / (T - 200)) * (t - T)) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hv0 : 0 < T - 200 := by linarith
  have hm := logw_le_shift (q := q) (by linarith) hT0 hTt.le (by linarith)
  have hd : 0 < |δ| := abs_pos.mpr hδ
  have ha0 : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
  have hG : (t - 200) / (2 * Real.pi * |δ|) *
      Real.exp (-0.1065 * ((t - 200) / (Real.pi * δ)) ^ 2) =
      (t - 200) / (Real.pi * |δ|) * Real.exp (-0.1065 * ((t - 200) / (Real.pi * |δ|)) ^ 2) / 2 := by
    rw [sq_div_pi_abs, div_two_pi_abs]
    ring
  rw [hG]
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  set a := Real.pi * |δ| with ha
  have hane : a ≠ 0 := ha0.ne'
  have hvne : T - 200 ≠ 0 := hv0.ne'
  set S := (T - 200) / a with hS
  set E := Real.exp (-0.1065 * S ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hS4 : 4 * Real.pi ≤ S := by
    rw [hS, le_div_iff₀ ha0]
    have e : 4 * Real.pi * a = 4 * Real.pi ^ 2 * |δ| := by rw [ha]; ring
    linarith
  have hS2 : 157.9 ≤ S ^ 2 := le_trans sixteen_pi_sq (pow_le_pow_left₀ (by positivity) hS4 2)
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS4
  have hratio : ((t - 200) / a - S) / S = (t - T) / (T - 200) := by
    rw [hS]
    field_simp
    ring
  have hg := lin_gauss_tail (k := 0.1065) ((t - 200) / a) (by norm_num) hS0
  rw [hratio] at hg
  set w := (t - T) / (T - 200) with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hv0.le
  have hTL : 4 * (T - 200) ≤ T * L := by nlinarith
  have hwL : (t - T) / (T * L) ≤ w / 4 := by
    have e : w / 4 = (t - T) / (4 * (T - 200)) := by rw [hw]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) hTL
  have hr1 : -(2 * 0.1065 * S ^ 2 - 1) * w + (t - T) / (T * L) ≤
      -(0.205 * S ^ 2 / (T - 200)) * (t - T) := by
    have e : -(0.205 * S ^ 2 / (T - 200)) * (t - T) = -(0.205 * S ^ 2) * w := by rw [hw]; ring
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.008 * S ^ 2 - 1.25) hw0]
  have hr2 : -(2 * 0.1065 * S ^ 2 - 1) * w ≤ -(0.2 * S ^ 2 / (T - 200)) * (t - T) := by
    have e : -(0.2 * S ^ 2 / (T - 200)) * (t - T) = -(0.2 * S ^ 2) * w := by rw [hw]; ring
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.013 * S ^ 2 - 1) hw0]
  have hmain : (t - 200) / a * Real.exp (-0.1065 * ((t - 200) / a) ^ 2) / 2 ≤
      S * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) / 2 := by
    rw [hE]
    linarith
  have hh : 1 / (2 * t) ≤ 1 / (2 * T) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hL0 : 0 ≤ L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have hX0 : 0 ≤ S * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) / 2 := by positivity
  unfold gw
  rw [mul_add]
  have p1 : (t - 200) / a * Real.exp (-0.1065 * ((t - 200) / a) ^ 2) / 2 *
      max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0 ≤
        S / 2 * E * (L / Real.pi) * Real.exp (-(0.205 * S ^ 2 / (T - 200)) * (t - T)) := by
    have q1 := mul_le_mul hmain hm (le_max_right _ _) hX0
    have q2 : Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) *
        Real.exp ((t - T) / (T * L)) ≤ Real.exp (-(0.205 * S ^ 2 / (T - 200)) * (t - T)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hr1
    have q3 := mul_le_mul_of_nonneg_left q2
      (mul_nonneg (by positivity : (0 : ℝ) ≤ S / 2 * E) hL0)
    calc (t - 200) / a * Real.exp (-0.1065 * ((t - 200) / a) ^ 2) / 2 *
          max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0
        ≤ S * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) / 2 *
            (L / Real.pi * Real.exp ((t - T) / (T * L))) := q1
      _ = S / 2 * E * (L / Real.pi) *
            (Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) * Real.exp ((t - T) / (T * L))) := by ring
      _ ≤ S / 2 * E * (L / Real.pi) * Real.exp (-(0.205 * S ^ 2 / (T - 200)) * (t - T)) := q3
  have p2 : (t - 200) / a * Real.exp (-0.1065 * ((t - 200) / a) ^ 2) / 2 * (1 / (2 * t)) ≤
      S / 2 * E / (2 * T) * Real.exp (-(0.2 * S ^ 2 / (T - 200)) * (t - T)) := by
    have hY0 : 0 ≤ (t - 200) / a * Real.exp (-0.1065 * ((t - 200) / a) ^ 2) / 2 := by
      have : 0 ≤ (t - 200) / a := div_nonneg (by linarith) ha0.le
      positivity
    have q1 := mul_le_mul hmain hh (by positivity) hX0
    have q2 : Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) ≤
        Real.exp (-(0.2 * S ^ 2 / (T - 200)) * (t - T)) := Real.exp_le_exp.mpr hr2
    have q3 := mul_le_mul_of_nonneg_left q2 (by positivity : (0 : ℝ) ≤ S / 2 * E / (2 * T))
    calc (t - 200) / a * Real.exp (-0.1065 * ((t - 200) / a) ^ 2) / 2 * (1 / (2 * t))
        ≤ S * E * Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) / 2 * (1 / (2 * T)) := q1
      _ = S / 2 * E / (2 * T) * Real.exp (-(2 * 0.1065 * S ^ 2 - 1) * w) := by ring
      _ ≤ S / 2 * E / (2 * T) * Real.exp (-(0.2 * S ^ 2 / (T - 200)) * (t - T)) := q3
  linarith

/-- **`PlusTailInt` PROVED.** -/
theorem plusTailInt_holds : PlusTailInt := by
  intro q hq1 _ δ T hT hTd
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hT0 : 0 < T := by linarith
  have hv0 : 0 < T - 200 := by linarith
  have hL4 : 4 ≤ Real.log (q * T / (2 * Real.pi)) := by
    have h := nat_le_log 4 (y := q * T / (2 * Real.pi)) (by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2])
    push_cast at h
    exact h
  have hpi := inv_pi_le
  set L := Real.log (q * T / (2 * Real.pi)) with hLdef
  have hLp : 0 ≤ L / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have eK : 9.462 * Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) =
      9.462 * (Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200))) := by ring
  rw [eK]
  set K := Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hLK : 0 ≤ K * L := mul_nonneg hK0 (by linarith)
  have hA1 : 0 ≤ 9.062 * (K * (L / Real.pi + 1 / (2 * T))) := by positivity
  -- the exponential part, integrated: `9.062K(L/π + 1/2T)/0.1572 ≤ 2.2·9.462·KL`
  have hexp : 9.062 * (K * (L / Real.pi + 1 / (2 * T))) / 0.1572 ≤
      2.2 * (9.462 * K) * L := by
    have e : L / Real.pi = L * (1 / Real.pi) := by ring
    rw [e]
    have h1 : K * L * (1 / Real.pi) ≤ K * L * 0.31832 := mul_le_mul_of_nonneg_left hpi hLK
    have hT1 : 1 / (2 * T) ≤ 1 / 900 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : K * (1 / (2 * T)) ≤ K * (1 / 900) := mul_le_mul_of_nonneg_left hT1 hK0
    have h3 : K * 4 ≤ K * L := mul_le_mul_of_nonneg_left hL4 hK0
    rw [div_le_iff₀ (by norm_num)]
    linarith
  rcases eq_or_ne δ 0 with hδ | hδ
  · subst hδ
    have hb := lint_le_exp3 (f := fun t => fplus 0 t * gw q t) (T := T)
      (A1 := 9.062 * (K * (L / Real.pi + 1 / (2 * T)))) (A2 := 0) (A3 := 0)
      (l1 := 0.1572) (l2 := 1) (l3 := 1) hA1 le_rfl le_rfl (by norm_num) one_pos one_pos
      (fun t ht => by
        have ht' : T < t := ht
        have hp := plus_exp_pt hq1' hT ht' hL4
        rw [← hLdef, ← hK] at hp
        have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 9.062)
        change fplus 0 t * gw q t ≤ _
        simp only [fplus, abs_zero, mul_zero, div_zero, zero_mul, add_zero]
        linarith)
    refine le_trans hb (ENNReal.ofReal_le_ofReal ?_)
    simp only [zero_div, add_zero, abs_zero, zero_mul, mul_zero]
    exact hexp
  · have hd : 0 < |δ| := abs_pos.mpr hδ
    have hdne : |δ| ≠ 0 := hd.ne'
    have ha0 : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
    set a := Real.pi * |δ| with ha
    set S := (T - 200) / a with hS
    have hS4 : 4 * Real.pi ≤ S := by
      rw [hS, le_div_iff₀ ha0]
      have e : 4 * Real.pi * a = 4 * Real.pi ^ 2 * |δ| := by rw [ha]; ring
      linarith
    have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS4
    have hSne : S ≠ 0 := hS0.ne'
    have hTne : T ≠ 0 := hT0.ne'
    set E := Real.exp (-0.1065 * S ^ 2) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hgq : Real.exp (-0.1065 * ((T - 200) / (Real.pi * δ)) ^ 2) = E := by
      rw [sq_div_pi_abs, hE, hS, ha]
    rw [hgq]
    have hb := lint_le_exp3 (f := fun t => fplus δ t * gw q t) (T := T)
      (A1 := 9.062 * (K * (L / Real.pi + 1 / (2 * T))))
      (A2 := 9.062 * (S / 2 * E * (L / Real.pi)))
      (A3 := 9.062 * (S / 2 * E / (2 * T)))
      (l1 := 0.1572) (l2 := 0.205 * S ^ 2 / (T - 200)) (l3 := 0.2 * S ^ 2 / (T - 200)) hA1
      (mul_nonneg (by norm_num) (mul_nonneg (by positivity) hLp))
      (by positivity) (by norm_num) (by positivity) (by positivity) (fun t ht => by
        have ht' : T < t := ht
        have hp := plus_exp_pt hq1' hT ht' hL4
        rw [← hLdef, ← hK] at hp
        have hg := plus_gauss_pt hδ hq1' hT hTd ht' hL4
        rw [← ha, ← hS, ← hE, ← hLdef] at hg
        have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 9.062)
        have hg' := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 9.062)
        change fplus δ t * gw q t ≤ _
        unfold fplus
        linarith)
    refine le_trans hb (ENNReal.ofReal_le_ofReal ?_)
    have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
    have hSa : S * a = T - 200 := by
      rw [hS]
      exact div_mul_cancel₀ _ ha0.ne'
    have e2 : 9.062 * (S / 2 * E * (L / Real.pi)) / (0.205 * S ^ 2 / (T - 200)) =
        9.062 / 0.41 * (|δ| * E * L) := by
      rw [← hSa, ha]
      field_simp
      ring
    have e3 : 9.062 * (S / 2 * E / (2 * T)) / (0.2 * S ^ 2 / (T - 200)) =
        9.062 * (Real.pi * |δ| * E / (0.8 * T)) := by
      rw [← hSa, ha]
      field_simp
      ring
    rw [e2, e3]
    have hdE : 0 ≤ |δ| * E := by positivity
    have hT1 : Real.pi * |δ| * E / (0.8 * T) ≤ 3.1416 * (|δ| * E) / 360 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : Real.pi * (|δ| * E) ≤ 3.1416 * (|δ| * E) :=
        mul_le_mul_of_nonneg_right Real.pi_lt_d4.le hdE
      have h2 := mul_nonneg hdE (by linarith : (0 : ℝ) ≤ 0.8 * T - 360)
      nlinarith
    have h4 : |δ| * E * 4 ≤ |δ| * E * L := mul_le_mul_of_nonneg_left hL4 hdE
    have e4 : 2.2 * (9.462 * K + 11.287 * |δ| * E) * L =
        2.2 * (9.462 * K) * L + 24.8314 * (|δ| * E * L) := by ring
    rw [e4]
    linarith

end Principia.Common.TernaryGoldbach.HM
