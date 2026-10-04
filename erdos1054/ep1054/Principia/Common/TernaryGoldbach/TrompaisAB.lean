/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Bostb1Spine
import Principia.Common.TernaryGoldbach.EasyStar

set_option autoImplicit false

/-!
# The first two parts of `eq:trompais`, PROVED, for `T_{d,∘}` and `T^{log}_{d,∘}`

`MPB2.TrompaisEta2` and `MPB1.TrompaisLogEta2` each bundle three per-`d` bounds. The first two
are elementary and are PROVED here; only the third (the `sin²` bound, which needs Poisson
summation and `|η̂₂''|_∞ ≤ c₀`, resp. `eq:puella`'s third part) stays a named link:

```
 TrompaisEta2    ← TrompaisC     (third part, sin² bound)                       OWED
                   tmo_le, tmo_sin_le (first two parts)                        PROVED
 TrompaisLogEta2 ← TrompaisLogC  (third part, sin² bound, d ≤ x/4)              OWED
                   tlo_le, tlo_sin_le (first two parts)                        PROVED
```

## Route (no Fourier analysis)

Write `T_{d,∘}(γ) = e(dγ) ∑_{k<K} h_k z^k` with `z = e(2dγ)`, `h_k = η₂(d(2k+1)/x)`
(`tmo_eq`), `K = ⌈L/2⌉`, `L = ⌊x⌋/d`, and `h_K = 0`.

* **Abel** (`abel_id`, `abel_le`): `(z − 1)∑ h_k z^k = ∑ (h_k − h_{k+1})z^{k+1} − h_0 + h_K z^K`,
  so `‖z − 1‖·|∑| ≤ V := h_0 + ∑_{k<K} |h_k − h_{k+1}|`, and `‖z − 1‖ = 2|sin 2πdγ|`.
* **Unimodality** (`tv_le`): samples of a function increasing on `(−∞, c]` and decreasing on
  `[c, ∞)`, with values in `[0, M]`, have `V ≤ 2M`. `η₂` is such with `c = 1/2`,
  `M = 4 log 2 = |η₂'|₁/2`; so the second part.
* **The sum** (`sum_eq_min`, `min_le_integral`): `2∑h_k = 2∑ min(h_k, h_{k+1}) + V` (as
  `h_K = 0`), and `min(η₂(s), η₂(u))·(u − s) ≤ ∫_s^u η₂` (quasi-concavity), so
  `∑ h_k ≤ (x/2d)∫η₂ + V/2 ≤ x/2d + 4 log 2`: the first part, with `|η₂|₁ = 1`.
* **Log weights**: `log(2k+1)η₂(d(2k+1)/x) = g(t_k)` with `g(t) = log(ρt)η₂(t)`, `ρ = x/d ≥ 4`;
  `g` is again increasing on `(−∞, 1/2]` and decreasing on `[1/2, ∞)` (on `[1/2, 1]`,
  `g(s) − g(t) = 4(log t − log s)(log ρ + log s + log t) ≥ 0`), with `0 ≤ g ≤ 4 log 2·log ρ`,
  and `log(2k+1) ≤ log ρ` wherever `η₂(t_k) ≠ 0`.
-/

namespace Principia.Common.TernaryGoldbach.MPT

open ArithmeticFunction Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPB2 Principia.Common.TernaryGoldbach.MPB1
  Principia.Common.TernaryGoldbach.MPG

/-! ## (1) Abel summation and unimodal variation -/

/-- **Abel's identity**:
`(z − 1)∑_{k<K} h_k z^k = ∑_{k<K} (h_k − h_{k+1})z^{k+1} − h_0 + h_K z^K`. -/
theorem abel_id (w : ℕ → ℝ) (z : ℂ) (K : ℕ) :
    (z - 1) * ∑ k ∈ Finset.range K, (w k : ℂ) * z ^ k =
      ∑ k ∈ Finset.range K, ((w k - w (k + 1) : ℝ) : ℂ) * z ^ (k + 1) - (w 0 : ℂ) +
        (w K : ℂ) * z ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- `‖z − 1‖·|∑_{k<K} h_k z^k| ≤ |h_0| + ∑_{k<K} |h_k − h_{k+1}|` for `|z| = 1`, `h_K = 0`. -/
theorem abel_le (w : ℕ → ℝ) (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ) (hK : w K = 0) :
    ‖z - 1‖ * ‖∑ k ∈ Finset.range K, (w k : ℂ) * z ^ k‖ ≤
      |w 0| + ∑ k ∈ Finset.range K, |w k - w (k + 1)| := by
  rw [← norm_mul, abel_id, hK, Complex.ofReal_zero, zero_mul, add_zero]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, add_comm]
  refine add_le_add le_rfl ((norm_sum_le _ _).trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Variation of unimodal samples**: if `g` increases on `(−∞, c]`, decreases on `[c, ∞)`, and
`0 ≤ g(t_k) ≤ M` along a nondecreasing `t`, then `g(t_0) + ∑_{k<K} |g(t_k) − g(t_{k+1})|`
equals `g(t_K)` while `t_K ≤ c`, and is always at most `2M − g(t_K)`. -/
theorem tv_le (g : ℝ → ℝ) (c M : ℝ) (hm : MonotoneOn g (Iic c)) (ha : AntitoneOn g (Ici c))
    (t : ℕ → ℝ) (ht : ∀ k, t k ≤ t (k + 1)) (h0 : ∀ k, 0 ≤ g (t k)) (hM : ∀ k, g (t k) ≤ M)
    (K : ℕ) :
    (t K ≤ c → g (t 0) + ∑ k ∈ Finset.range K, |g (t k) - g (t (k + 1))| = g (t K)) ∧
      g (t 0) + ∑ k ∈ Finset.range K, |g (t k) - g (t (k + 1))| ≤ 2 * M - g (t K) := by
  induction K with
  | zero =>
    refine ⟨fun _ => by simp, ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    linarith [hM 0]
  | succ K ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_range_succ, ← add_assoc]
    have hM1 := hM (K + 1)
    have hMK := hM K
    have h01 := h0 (K + 1)
    by_cases h1 : t (K + 1) ≤ c
    · have hK : t K ≤ c := (ht K).trans h1
      have hle : g (t K) ≤ g (t (K + 1)) := hm (mem_Iic.mpr hK) (mem_Iic.mpr h1) (ht K)
      rw [ih1 hK, abs_of_nonpos (by linarith)]
      exact ⟨fun _ => by ring, by linarith⟩
    · rw [not_le] at h1
      refine ⟨fun h => absurd h (not_le.mpr h1), ?_⟩
      by_cases h2 : t K ≤ c
      · rw [ih1 h2]
        rcases abs_cases (g (t K) - g (t (K + 1))) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
      · rw [not_le] at h2
        have hle : g (t (K + 1)) ≤ g (t K) :=
          ha (mem_Ici.mpr h2.le) (mem_Ici.mpr h1.le) (ht K)
        rw [abs_of_nonneg (by linarith)]
        linarith

/-- `2 min(a, b) + |a − b| = a + b`. -/
theorem two_min_add_abs (a b : ℝ) : 2 * min a b + |a - b| = a + b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- `2∑_{k<K} h_k = 2∑_{k<K} min(h_k, h_{k+1}) + h_0 + ∑_{k<K} |h_k − h_{k+1}| − h_K`. -/
theorem sum_eq_min (w : ℕ → ℝ) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, w k =
      2 * ∑ k ∈ Finset.range K, min (w k) (w (k + 1)) + w 0 +
        ∑ k ∈ Finset.range K, |w k - w (k + 1)| - w K := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [Finset.sum_range_succ, mul_add]
    have := two_min_add_abs (w K) (w (K + 1))
    linarith

/-! ## (2) `η₂`: shape and mass -/

/-- `η₂ = 0` on `(−∞, 1/4]`. -/
theorem eta2_le_quarter {s : ℝ} (hs : s ≤ 1 / 4) : HW.eta2 s = 0 := by
  rcases le_or_gt s 0 with h | h
  · exact HW.eta2_of_nonpos h
  · exact HW.eta2_of_le_quarter h hs

/-- `η₂ ≤ 4 log 2`. -/
theorem eta2_le (t : ℝ) : HW.eta2 t ≤ 4 * Real.log 2 := GS.eta2_le t

/-- `η₂` is continuous. -/
theorem eta2_cont : Continuous HW.eta2 := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_or_ge 0 t with ht | ht
  · exact EN.eta2_contOn.continuousAt (Ioi_mem_nhds ht)
  · have hev : HW.eta2 =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 4 by linarith)] with s hs
      exact eta2_le_quarter (le_of_lt hs)
    exact continuousAt_const.congr hev.symm

/-- `η₂` increases on `(−∞, 1/2]`. -/
theorem eta2_mono : MonotoneOn HW.eta2 (Iic (1 / 2)) := by
  intro s hs t ht hst
  rw [mem_Iic] at hs ht
  rcases le_or_gt s (1 / 4) with h | h
  · rw [eta2_le_quarter h]
    exact HW.eta2_nonneg t
  · rw [EN.eta2_left h.le hs, EN.eta2_left (by linarith) ht]
    have := Real.log_le_log (by linarith) hst
    linarith

/-- `η₂` decreases on `[1/2, ∞)`. -/
theorem eta2_anti : AntitoneOn HW.eta2 (Ici (1 / 2)) := by
  intro s hs t ht hst
  rw [mem_Ici] at hs ht
  rcases le_or_gt 1 t with h | h
  · rw [HW.eta2_of_one_le h]
    exact HW.eta2_nonneg s
  · rw [EN.eta2_right hs (by linarith), EN.eta2_right ht h.le]
    have := Real.log_le_log (by linarith) hst
    linarith

/-- **Quasi-concavity**: `min(η₂(s), η₂(u))·(u − s) ≤ ∫_s^u η₂` for `s ≤ u`. -/
theorem min_le_integral (s u : ℝ) (hsu : s ≤ u) :
    min (HW.eta2 s) (HW.eta2 u) * (u - s) ≤ ∫ t in s..u, HW.eta2 t := by
  have hc : ∫ _ in s..u, min (HW.eta2 s) (HW.eta2 u) = min (HW.eta2 s) (HW.eta2 u) * (u - s) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [← hc]
  refine intervalIntegral.integral_mono_on hsu intervalIntegrable_const
    (eta2_cont.intervalIntegrable _ _) fun t ht => ?_
  rcases le_total t (1 / 2) with h | h
  · exact (min_le_left _ _).trans (eta2_mono (mem_Iic.mpr (ht.1.trans h)) (mem_Iic.mpr h) ht.1)
  · exact (min_le_right _ _).trans
      (eta2_anti (mem_Ici.mpr h) (mem_Ici.mpr (h.trans ht.2)) ht.2)

/-- **`∫_a^b η₂ ≤ |η₂|₁ = 1`** for `a ≤ b`. -/
theorem integral_eta2_le (a b : ℝ) (hab : a ≤ b) : ∫ t in a..b, HW.eta2 t ≤ 1 := by
  have hI : ∀ p q : ℝ, IntervalIntegrable HW.eta2 volume p q :=
    fun p q => eta2_cont.intervalIntegrable p q
  set m := min a (1 / 4)
  set M := max b 1
  have hm : m ≤ 1 / 4 := min_le_right _ _
  have hM : 1 ≤ M := le_max_right _ _
  have h1 : ∫ t in a..b, HW.eta2 t ≤ ∫ t in m..M, HW.eta2 t :=
    intervalIntegral.integral_mono_interval (min_le_left _ _) hab (le_max_left _ _)
      (Filter.Eventually.of_forall fun t => HW.eta2_nonneg t) (hI m M)
  have hz1 : ∫ t in m..(1 / 4), HW.eta2 t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [uIcc_of_le hm] at ht
      exact eta2_le_quarter ht.2
  have hz2 : ∫ t in (1 : ℝ)..M, HW.eta2 t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [uIcc_of_le hM] at ht
      exact HW.eta2_of_one_le ht.1
  have hsplit : ∫ t in m..M, HW.eta2 t = (∫ t in m..(1 / 4), HW.eta2 t) +
      (∫ t in (1 / 4 : ℝ)..(1 / 2), HW.eta2 t) + (∫ t in (1 / 2 : ℝ)..1, HW.eta2 t) +
      ∫ t in (1 : ℝ)..M, HW.eta2 t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _),
      intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _),
      intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _)]
  rw [hsplit, hz1, hz2, EN.int_eta2_left, EN.int_eta2_right] at h1
  linarith

/-! ## (3) `T_{d,∘}` as a power sum -/

/-- **Odd reindexing**: `∑_{0<m≤L} f(m)F(m) = ∑_{k<⌈L/2⌉} F(2k+1)`. -/
theorem sum_odd (F : ℕ → ℂ) (L : ℕ) :
    ∑ m ∈ Finset.Ioc 0 L, ((fOdd m : ℝ) : ℂ) * F m =
      ∑ k ∈ Finset.range ((L + 1) / 2), F (2 * k + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, fOdd_apply]
    rcases Nat.even_or_odd L with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h1 : (L + 1) / 2 = j := by omega
      have h2 : (L + 1 + 1) / 2 = j + 1 := by omega
      have h3 : L + 1 = 2 * j + 1 := by omega
      rw [h1, h2, if_pos (by omega), Finset.sum_range_succ, h3]
      push_cast
      rw [one_mul]
    · have h1 : (L + 1) / 2 = j + 1 := by omega
      have h2 : (L + 1 + 1) / 2 = j + 1 := by omega
      rw [h1, h2, if_neg (by omega)]
      push_cast
      rw [zero_mul, add_zero]

/-- `e(d(2k+1)γ) = e(dγ)·e(2dγ)^k`. -/
theorem e_odd (d : ℕ) (γ : ℝ) (k : ℕ) :
    e (((d * (2 * k + 1) : ℕ) : ℝ) * γ) = e (d * γ) * e (2 * d * γ) ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The samples `h_k = η₂(d(2k+1)/x)`. -/
noncomputable def hs (x : ℝ) (d k : ℕ) : ℝ := HW.eta2 ((d : ℝ) * (2 * k + 1) / x)

/-- The number of odd terms, `K = ⌈⌊x⌋₊/d / 2⌉`. -/
noncomputable def kK (x : ℝ) (d : ℕ) : ℕ := (⌊x⌋₊ / d + 1) / 2

/-- **`T_{d,∘}(γ) = e(dγ)∑_{k<K} h_k e(2dγ)^k`.** -/
theorem tmo_eq (x γ : ℝ) (d : ℕ) :
    tmo x γ d = e (d * γ) * ∑ k ∈ Finset.range (kK x d), (hs x d k : ℂ) * e (2 * d * γ) ^ k := by
  unfold tmo kK
  rw [sum_odd (fun m => wt x γ (d * m)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold wt hs
  rw [e_odd]
  push_cast
  ring

/-- **`h_K = 0`**: `d(2K+1) > ⌊x⌋₊`, so `d(2K+1)/x > 1`. -/
theorem hs_kK (x : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) : hs x d (kK x d) = 0 := by
  unfold hs kK
  apply HW.eta2_of_one_le
  have h1 : ⌊x⌋₊ < d * (⌊x⌋₊ / d + 1) := Nat.lt_mul_div_succ _ (by omega)
  have h2 : d * (⌊x⌋₊ / d + 1) ≤ d * (2 * ((⌊x⌋₊ / d + 1) / 2) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : ⌊x⌋₊ + 1 ≤ d * (2 * ((⌊x⌋₊ / d + 1) / 2) + 1) := by omega
  have h4 : x < ((d * (2 * ((⌊x⌋₊ / d + 1) / 2) + 1) : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one x
    have h5 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((d * (2 * ((⌊x⌋₊ / d + 1) / 2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h5 ⊢
    linarith
  rw [le_div_iff₀ hx, one_mul]
  push_cast at h4
  linarith

/-- The sample points increase. -/
theorem t_mono (x : ℝ) (hx : 0 < x) (d : ℕ) (k : ℕ) :
    (d : ℝ) * (2 * k + 1) / x ≤ (d : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) / x := by
  apply div_le_div_of_nonneg_right _ hx.le
  push_cast
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- **The variation of `h` is at most `2·4 log 2 = |η₂'|₁`.** -/
theorem hs_tv (x : ℝ) (hx : 0 < x) (d K : ℕ) :
    |hs x d 0| + ∑ k ∈ Finset.range K, |hs x d k - hs x d (k + 1)| ≤ 2 * (4 * Real.log 2) := by
  have := (tv_le HW.eta2 (1 / 2) (4 * Real.log 2) eta2_mono eta2_anti
    (fun k : ℕ => (d : ℝ) * (2 * k + 1) / x) (t_mono x hx d) (fun k => HW.eta2_nonneg _)
    (fun k => eta2_le _) K).2
  have h0 : 0 ≤ hs x d 0 := HW.eta2_nonneg _
  have hK : 0 ≤ hs x d K := HW.eta2_nonneg _
  rw [abs_of_nonneg h0]
  unfold hs at h0 hK ⊢
  push_cast at this ⊢
  linarith

/-! ## (4) The first two parts for `T_{d,∘}`, PROVED -/

/-- **`∑_{k<K} h_k ≤ x/2d + 4 log 2`.** -/
theorem sum_hs_le (x : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (kK x d), hs x d k ≤ x / (2 * d) + eta1 / 2 := by
  set K := kK x d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hid := sum_eq_min (hs x d) K
  have htv := hs_tv x hx d K
  rw [hs_kK x hx d hd, sub_zero] at hid
  have h0 : 0 ≤ hs x d 0 := HW.eta2_nonneg _
  rw [abs_of_nonneg h0] at htv
  -- each `min` is at most `(x/2d)∫` over its cell
  set t : ℕ → ℝ := fun k => (d : ℝ) * (2 * k + 1) / x with ht_def
  have hstep : ∀ k : ℕ, t (k + 1) - t k = 2 * d / x := by
    intro k; simp only [ht_def]; push_cast; field_simp; ring
  have hmin : ∀ k : ℕ, min (hs x d k) (hs x d (k + 1)) ≤
      x / (2 * d) * ∫ s in t k..t (k + 1), HW.eta2 s := by
    intro k
    have := min_le_integral (t k) (t (k + 1)) (t_mono x hx d k)
    rw [hstep] at this
    have e1 : hs x d k = HW.eta2 (t k) := rfl
    have e2 : hs x d (k + 1) = HW.eta2 (t (k + 1)) := by simp only [hs, ht_def]
    rw [e1, e2]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e3 : min (HW.eta2 (t k)) (HW.eta2 (t (k + 1))) * (2 * d) =
        min (HW.eta2 (t k)) (HW.eta2 (t (k + 1))) * (2 * d / x) * x := by
      field_simp
    rw [e3]
    nlinarith
  have hsum : ∑ k ∈ Finset.range K, min (hs x d k) (hs x d (k + 1)) ≤
      x / (2 * d) * ∫ s in t 0..t K, HW.eta2 s := by
    rw [← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => eta2_cont.intervalIntegrable _ _), Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hmin k
  have hint : ∫ s in t 0..t K, HW.eta2 s ≤ 1 := by
    refine integral_eta2_le _ _ ?_
    simp only [ht_def]
    apply div_le_div_of_nonneg_right _ hx.le
    push_cast
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hfac : x / (2 * d) * ∫ s in t 0..t K, HW.eta2 s ≤ x / (2 * d) :=
    mul_le_of_le_one_right (by positivity) hint
  unfold eta1
  linarith

/-- **First part of `eq:trompais`, PROVED**: `|T_{d,∘}(γ)| ≤ x/2d + |η₂'|₁/2`. -/
theorem tmo_le (x γ : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) :
    ‖tmo x γ d‖ ≤ x / (2 * d) + eta1 / 2 := by
  rw [tmo_eq, norm_mul, e_norm, one_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans (sum_hs_le x hx d hd))
  rw [norm_mul, norm_pow, e_norm, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact le_of_eq (abs_of_nonneg (HW.eta2_nonneg _))

/-- `‖e(2dγ) − 1‖ = 2|sin 2πdγ|`. -/
theorem norm_z_sub_one (d : ℕ) (γ : ℝ) :
    ‖e (2 * d * γ) - 1‖ = 2 * |Real.sin (2 * Real.pi * d * γ)| := by
  rw [e_sub_one_norm]
  congr 3
  ring

/-- **Second part of `eq:trompais`, PROVED**: `|T_{d,∘}(γ)|·|sin 2πdγ| ≤ |η₂'|₁/2`. -/
theorem tmo_sin_le (x γ : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) :
    ‖tmo x γ d‖ * |Real.sin (2 * Real.pi * d * γ)| ≤ eta1 / 2 := by
  have hab := abel_le (hs x d) (e (2 * d * γ)) (e_norm _) (kK x d) (hs_kK x hx d hd)
  have htv := hs_tv x hx d (kK x d)
  rw [norm_z_sub_one] at hab
  rw [tmo_eq, norm_mul, e_norm, one_mul]
  unfold eta1
  nlinarith

/-! ## (5) The first two parts for `T^{log}_{d,∘}`, PROVED -/

/-- The log-weighted samples `log(2k+1)·η₂(d(2k+1)/x)`. -/
noncomputable def hl (x : ℝ) (d k : ℕ) : ℝ := Real.log ((2 * k + 1 : ℕ) : ℝ) * hs x d k

/-- **`T^{log}_{d,∘}(γ) = e(dγ)∑_{k<K} log(2k+1)h_k e(2dγ)^k`.** -/
theorem tlo_eq (x γ : ℝ) (d : ℕ) :
    tlo x γ d = e (d * γ) * ∑ k ∈ Finset.range (kK x d), (hl x d k : ℂ) * e (2 * d * γ) ^ k := by
  unfold tlo kK
  have hre : ∀ m : ℕ, ((Real.log m * fOdd m : ℝ) : ℂ) * wt x γ (d * m) =
      ((fOdd m : ℝ) : ℂ) * (((Real.log m : ℝ) : ℂ) * wt x γ (d * m)) := by
    intro m; push_cast; ring
  rw [Finset.sum_congr rfl fun m _ => hre m, sum_odd (fun m => ((Real.log m : ℝ) : ℂ) *
    wt x γ (d * m)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold wt hl hs
  rw [e_odd]
  push_cast
  ring

/-- `g(t) = log(ρt)η₂(t)` increases on `(−∞, 1/2]` for `ρ ≥ 4`. -/
theorem gl_mono (ρ : ℝ) (hρ : 4 ≤ ρ) :
    MonotoneOn (fun t => Real.log (ρ * t) * HW.eta2 t) (Iic (1 / 2)) := by
  intro s hs t ht hst
  rw [mem_Iic] at hs ht
  simp only
  rcases le_or_gt s (1 / 4) with h | h
  · rw [eta2_le_quarter h, mul_zero]
    rcases le_or_gt t (1 / 4) with h' | h'
    · rw [eta2_le_quarter h', mul_zero]
    · exact mul_nonneg (Real.log_nonneg (by nlinarith)) (HW.eta2_nonneg t)
  · have hl1 : Real.log (ρ * s) ≤ Real.log (ρ * t) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hl0 : 0 ≤ Real.log (ρ * s) := Real.log_nonneg (by nlinarith)
    exact mul_le_mul hl1 (eta2_mono (mem_Iic.mpr hs) (mem_Iic.mpr ht) hst) (HW.eta2_nonneg s)
      (hl0.trans hl1)

/-- `g(t) = log(ρt)η₂(t)` decreases on `[1/2, ∞)` for `ρ ≥ 4`. -/
theorem gl_anti (ρ : ℝ) (hρ : 4 ≤ ρ) :
    AntitoneOn (fun t => Real.log (ρ * t) * HW.eta2 t) (Ici (1 / 2)) := by
  intro s hs t ht hst
  rw [mem_Ici] at hs ht
  simp only
  have hls : 0 ≤ Real.log (ρ * s) := Real.log_nonneg (by nlinarith)
  rcases le_or_gt 1 t with h | h
  · rw [HW.eta2_of_one_le h, mul_zero]
    exact mul_nonneg hls (HW.eta2_nonneg s)
  · have hs0 : 0 < s := by linarith
    have ht0 : 0 < t := by linarith
    rw [EN.eta2_right hs (by linarith), EN.eta2_right ht h.le,
      Real.log_mul (by linarith) hs0.ne', Real.log_mul (by linarith) ht0.ne']
    have hst' : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
    have hsl : -Real.log 2 ≤ Real.log s := by
      have := Real.log_le_log (by norm_num) hs
      rwa [EN.log_half] at this
    have htl : -Real.log 2 ≤ Real.log t := hsl.trans hst'
    have hρl : 2 * Real.log 2 ≤ Real.log ρ := by
      have := Real.log_le_log (by norm_num) hρ
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat] at this
    have key : 0 ≤ (Real.log t - Real.log s) * (Real.log ρ + Real.log s + Real.log t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- `0 ≤ log(2k+1)·h_k`. -/
theorem hl_nonneg (x : ℝ) (d k : ℕ) : 0 ≤ hl x d k := by
  unfold hl
  refine mul_nonneg (Real.log_nonneg ?_) (HW.eta2_nonneg _)
  exact_mod_cast (by omega : 1 ≤ 2 * k + 1)

/-- `log(2k+1)·h_k ≤ log(x/d)·h_k` (only `d(2k+1) < x` contributes). -/
theorem hl_le (x : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    hl x d k ≤ Real.log (x / d) * hs x d k := by
  unfold hl
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rcases le_or_gt 1 ((d : ℝ) * (2 * k + 1) / x) with h | h
  · have : hs x d k = 0 := HW.eta2_of_one_le h
    rw [this, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ?_ (HW.eta2_nonneg _)
    rw [div_lt_one hx] at h
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ hdR]
    push_cast
    linarith

/-- `log(x/d) ≥ log 4 > 0` for `d ≤ x/4`. -/
theorem log_xd_nonneg (x : ℝ) (d : ℕ) (hd : 1 ≤ d) (hdx : (d : ℝ) ≤ x / 4) :
    0 ≤ Real.log (x / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact Real.log_nonneg (by rw [le_div_iff₀ hdR]; linarith)

/-- **First part for `T^{log}`, PROVED**: `|T^{log}_{d,∘}(γ)| ≤ log(x/d)(x/2d + |η₂'|₁/2)`. -/
theorem tlo_le (x γ : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) (hdx : (d : ℝ) ≤ x / 4) :
    ‖tlo x γ d‖ ≤ Real.log (x / d) * (x / (2 * d) + eta1 / 2) := by
  have hL := log_xd_nonneg x d hd hdx
  rw [tlo_eq, norm_mul, e_norm, one_mul]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (kK x d),
      ‖(hl x d k : ℂ) * e (2 * d * γ) ^ k‖ ≤ Real.log (x / d) * hs x d k := by
    intro k _
    rw [norm_mul, norm_pow, e_norm, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hl_nonneg x d k)]
    exact hl_le x hx d hd k
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_hs_le x hx d hd) hL

/-- **Second part for `T^{log}`, PROVED**:
`|T^{log}_{d,∘}(γ)|·|sin 2πdγ| ≤ log(x/d)·|η₂'|₁/2`. -/
theorem tlo_sin_le (x γ : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d) (hdx : (d : ℝ) ≤ x / 4) :
    ‖tlo x γ d‖ * |Real.sin (2 * Real.pi * d * γ)| ≤ Real.log (x / d) * (eta1 / 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL := log_xd_nonneg x d hd hdx
  have hρ : 4 ≤ x / d := by rw [le_div_iff₀ hdR]; linarith
  set ρ := x / d with hρ_def
  have hsamp : ∀ k : ℕ, hl x d k = (fun t => Real.log (ρ * t) * HW.eta2 t)
      ((d : ℝ) * (2 * k + 1) / x) := by
    intro k
    simp only [hl, hs, hρ_def]
    congr 2
    push_cast
    field_simp
  have htv := (tv_le (fun t => Real.log (ρ * t) * HW.eta2 t) (1 / 2)
    (Real.log ρ * (4 * Real.log 2)) (gl_mono ρ hρ) (gl_anti ρ hρ)
    (fun k : ℕ => (d : ℝ) * (2 * k + 1) / x) (t_mono x hx d)
    (fun k => by
      have := hl_nonneg x d k
      rwa [hsamp] at this)
    (fun k => by
      have := (hl_le x hx d hd k).trans (mul_le_mul_of_nonneg_left (eta2_le _) hL)
      rwa [hsamp] at this)
    (kK x d)).2
  simp only [← hsamp] at htv
  have hK0 : hl x d (kK x d) = 0 := by rw [hl, hs_kK x hx d hd, mul_zero]
  have h00 : 0 ≤ hl x d 0 := hl_nonneg x d 0
  have hab := abel_le (hl x d) (e (2 * d * γ)) (e_norm _) (kK x d) hK0
  rw [norm_z_sub_one, abs_of_nonneg h00] at hab
  rw [hK0] at htv
  rw [tlo_eq, norm_mul, e_norm, one_mul]
  unfold eta1
  nlinarith

/-! ## (6) The third parts, named; the compositions, PROVED -/

/-- **Link [TrompaisC] — the third part of `eq:trompais` for `η₂`**: for `x > 0`, `d ≥ 1`,
`|T_{d,∘}(γ)|·sin²(2πdγ) ≤ (d/x)(c₀/2)`. Poisson summation (`lem:areval`) with
`|η̂₂''|_∞ ≤ c₀ = 31.521` (`lem:camelo`; `HC.CameloGridCited` plus interpolation and tail).
NOT reachable by summation by parts: two Abel steps give `24(d/x)` (`|η₂''|₁ = 48`), above
`c₀/2 = 15.76`. OPEN. -/
def TrompaisC : Prop :=
  ∀ x γ : ℝ, 0 < x → ∀ d : ℕ, 1 ≤ d →
    ‖tmo x γ d‖ * Real.sin (2 * Real.pi * d * γ) ^ 2 ≤ d / x * (c0 / 2)

/-- **Link [TrompaisLogC] — the third part of the per-`m` estimate of `lem:bostb1`**: for
`x > 0`, `1 ≤ d ≤ x/4`, `|T^{log}_{d,∘}(γ)|·sin²(2πdγ) ≤ log(x/d)(d/x)(c₀/2)`. Poisson with
`eq:puella`'s third part `|η̂_{(ρ)}''|_∞ ≤ c₀ log ρ` at `ρ = x/d ≥ 4` (own proof owed: the printed
`eq:cloclo` route is too weak at `c₀ = 31.521`). OPEN. -/
def TrompaisLogC : Prop :=
  ∀ x γ : ℝ, 0 < x → ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ x / 4 →
    ‖tlo x γ d‖ * Real.sin (2 * Real.pi * d * γ) ^ 2 ≤ Real.log (x / d) * (d / x * (c0 / 2))

/-- **`MPB2.TrompaisEta2` from its third part alone, PROVED.** -/
theorem trompaisEta2_of (hC : TrompaisC) : TrompaisEta2 :=
  fun x γ hx d hd => ⟨tmo_le x γ hx d hd, tmo_sin_le x γ hx d hd, hC x γ hx d hd⟩

/-- **`MPB1.TrompaisLogEta2` from its third part alone, PROVED.** -/
theorem trompaisLogEta2_of (hC : TrompaisLogC) : TrompaisLogEta2 :=
  fun x γ hx d hd hdx =>
    ⟨tlo_le x γ hx d hd hdx, tlo_sin_le x γ hx d hd hdx, hC x γ hx d hd hdx⟩

/-- **`MPc.Bosta2Eta2` on `TrompaisC`, `MainOddEta2`, `EsthelEta2`, PROVED** (application). -/
theorem bosta2Eta2_of_C (h1 : TrompaisC) (h2 : MainOddEta2) (h3 : EsthelEta2) : Bosta2Eta2 :=
  bosta2Eta2_of (trompaisEta2_of h1) h2 h3

/-- **`MPG.Bostb1Eta2` on `TrompaisLogC`, `MainLogEta2`, `EsthelLogEta2`, PROVED**. -/
theorem bostb1Eta2_of_C (h1 : TrompaisLogC) (h2 : MainLogEta2) (h3 : EsthelLogEta2) :
    Bostb1Eta2 :=
  bostb1Eta2_of (trompaisLogEta2_of h1) h2 h3

end Principia.Common.TernaryGoldbach.MPT
