/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopC
import Principia.Common.TernaryGoldbach.MNumProofs
import Principia.Erdos1054.Proofs.SmallRatio

set_option autoImplicit false

/-!
# `MNumC` toolkit: the generic analysis behind `MC.mnumC_proved`

Everything here is GENERIC in its numeric parameters; the certified numbers live in the generated
modules `MNumCMom` (Gaussian moments, `exp`, `log`) and `MNumCR0`–`MNumCRF` (the region envelopes).

* **Integral bounds without integrability of the integrand** (`IntBnd`, `IntBndI`): a
  non-integrable integrand has junk integral `0`, so a bound `B ≥ 0` holds either way; bounds over
  adjacent intervals add (`intBnd_add`, `intBndI_add`). This is how `gT`'s `w`-integrals and
  `intGT`'s `r`-integral are split into pieces and regions with no continuity argument about `g_Y`.
* **The factors of `g_Y`** (`eq:syryza`): `R_{z,t}` by the tangent of `log` at `1 + u*` and the
  chord of `1/(K_D − ξ)` (`rR_tan`, `chord_inv`, `rChordLo`, `rChordHi`); on the far region
  `R ≤ 0.72` (`rFarLo`, `rFarHi`); `F` by the tangent of `log log` (`bigF_le_tan`, with
  `e^γ ≤ 1.7810727` from `SmallRatio.exp_gamma_le`); `√F` by AM–GM; `L_t` (`lL_le_of`);
  `1/√w` by its quartic Taylor polynomial at the left end of a piece (`isq_le`, one-sided because
  the remainder is `(u−1)⁵(35u⁴+175u³+345u²+325u+128)/128 ≥ 0`); `log w` by a tangent (`w < 1`)
  or a chord (`w ≥ 1`).
* **Piece majorants** (`ptLoGen`, `ptHiGen`, `ptTailGen`, `ptFirstGen`): `g_Y φ` below a polynomial
  in `(w, log r)` times `e^{−w²/2}` (or `C·w` on the first piece `[w₁, 0.04]`, or `K w³e^{−w²/2}/q`
  on the tail); their integrals are linear in the Gaussian moments `J_k(a,b)` (`mJ`, `mJ_rec`,
  `mJ_one`, `mJ0_taylor`, `int_shapeG`, `mI_eq`, `rows_le`) and in `∫_q^∞ w³e^{−w²/2} =
  (q²+2)e^{−q²/2}` (`int_w3_tail`).
* **`gT` from its three parts** (`gT_le_of`, with the sliver `sliver_le`), and **the region
  envelope** `E(r) = P(log r)/√r + Q(log r)/r + z` with its exact antiderivative against `dr/r`
  (`envF`, `envG`, `envG_deriv`, `intBnd_region`, `envG_mono`).
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset Filter
open scoped Topology


/-- `e^γ ≤ 1.7810727` (`SmallRatio.exp_gamma_le`, the corrected Euler–Maclaurin sequence). -/
theorem expG_le : Real.exp Real.eulerMascheroniConstant ≤ 1.7810727 :=
  Principia.Erdos1054.Proofs.SmallRatio.exp_gamma_le

/-- **`1/√w ≤ (1/s)·T₄(w/s² − 1)`** for `w ≥ s² > 0`: the quartic Taylor polynomial of
`(1+x)^{−1/2}` at `0` is an upper bound for `x ≥ 0`; with `u = √w/s ≥ 1` the remainder is
`(u − 1)⁵(35u⁴ + 175u³ + 345u² + 325u + 128)/128 ≥ 0`. -/
theorem isq_le (s w : ℝ) (hs : 0 < s) (hw : s ^ 2 ≤ w) :
    1 / Real.sqrt w ≤ 1 / s * (1 - (w / s ^ 2 - 1) / 2 + 3 / 8 * (w / s ^ 2 - 1) ^ 2 -
      5 / 16 * (w / s ^ 2 - 1) ^ 3 + 35 / 128 * (w / s ^ 2 - 1) ^ 4) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hsw : s ≤ Real.sqrt w := by
    have h := Real.sqrt_le_sqrt hw
    rwa [Real.sqrt_sq hs.le] at h
  set u := Real.sqrt w / s with hu
  have hu1 : 1 ≤ u := by
    rw [hu, le_div_iff₀ hs]
    linarith
  have hu0 : 0 < u := by linarith
  have hsq : Real.sqrt w = s * u := by
    rw [hu]
    field_simp
  have hwu : w / s ^ 2 = u ^ 2 := by
    have h2 : w = Real.sqrt w ^ 2 := (Real.sq_sqrt hw0.le).symm
    rw [h2, hsq]
    field_simp
  rw [hsq, hwu]
  have hv : 0 ≤ u - 1 := by linarith
  have e : u * (1 - (u ^ 2 - 1) / 2 + 3 / 8 * (u ^ 2 - 1) ^ 2 - 5 / 16 * (u ^ 2 - 1) ^ 3 +
      35 / 128 * (u ^ 2 - 1) ^ 4) - 1 =
      (u - 1) ^ 5 * (35 * u ^ 4 + 175 * u ^ 3 + 345 * u ^ 2 + 325 * u + 128) / 128 := by ring
  have hr : 0 ≤ (u - 1) ^ 5 * (35 * u ^ 4 + 175 * u ^ 3 + 345 * u ^ 2 + 325 * u + 128) / 128 := by
    have := pow_nonneg hv 5
    positivity
  have h2 : 1 / u ≤ 1 - (u ^ 2 - 1) / 2 + 3 / 8 * (u ^ 2 - 1) ^ 2 - 5 / 16 * (u ^ 2 - 1) ^ 3 +
      35 / 128 * (u ^ 2 - 1) ^ 4 := by
    rw [div_le_iff₀ hu0]
    linarith
  calc 1 / (s * u) = 1 / s * (1 / u) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The tangent of `log` at `m`**: `log w ≤ log m − 1 + w/m`. -/
theorem log_le_tan (w m LM : ℝ) (hw : 0 < w) (hm : 0 < m) (hLM : Real.log m ≤ LM) :
    Real.log w ≤ LM - 1 + w / m := by
  have h := Real.log_le_sub_one_of_pos (div_pos hw hm)
  rw [Real.log_div hw.ne' hm.ne'] at h
  linarith

/-- **A chord of `log` lies below it**: if `α + βa ≤ log a` and `α + βb ≤ log b` then
`α + βw ≤ log w` on `[a, b]` (`log` is concave). -/
theorem log_ge_chord (a b w α β : ℝ) (ha : 0 < a) (haw : a ≤ w) (hwb : w ≤ b)
    (hA : α + β * a ≤ Real.log a) (hB : α + β * b ≤ Real.log b) : α + β * w ≤ Real.log w := by
  rcases eq_or_lt_of_le (haw.trans hwb) with hab | hab
  · have hw : w = a := le_antisymm (hab ▸ hwb) haw
    rw [hw]
    exact hA
  have hba : 0 < b - a := by linarith
  set θ := (b - w) / (b - a) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hba.le
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, one_sub_div hba.ne']
    exact div_nonneg (by linarith) hba.le
  have hwc : θ • a + (1 - θ) • b = w := by
    simp only [smul_eq_mul]
    rw [hθ]
    field_simp
    ring
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr ha)
    (Set.mem_Ioi.mpr (lt_of_lt_of_le ha (haw.trans hwb))) hθ0 hθ1 (by ring)
  rw [hwc] at hc
  simp only [smul_eq_mul] at hc
  have e : α + β * w = θ * (α + β * a) + (1 - θ) * (α + β * b) := by
    rw [← hwc]
    simp only [smul_eq_mul]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hA hθ0, mul_le_mul_of_nonneg_left hB hθ1]

/-- **`e^{−v}` by its Taylor polynomial** for `0 ≤ v ≤ 1` (`Real.exp_bound`). -/
theorem exp_neg_taylor (v : ℝ) (n : ℕ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hn : 0 < n) :
    |Real.exp (-v) - ∑ i ∈ range n, (-v) ^ i / (i.factorial : ℝ)| ≤
      v ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
  have h := Real.exp_bound (x := -v) (by rw [abs_neg, abs_of_nonneg hv0]; exact hv1) hn
  rwa [abs_neg, abs_of_nonneg hv0] at h

/-- **Two-sided Taylor bounds for `e^{−v}`**, `0 ≤ v ≤ 1`. -/
theorem exp_taylor_cert (v : ℝ) (n : ℕ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hn : 0 < n) :
    (∑ i ∈ range n, (-v) ^ i / (i.factorial : ℝ)) -
        v ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) ≤ Real.exp (-v) ∧
      Real.exp (-v) ≤ (∑ i ∈ range n, (-v) ^ i / (i.factorial : ℝ)) +
        v ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
  have h := abs_le.mp (exp_neg_taylor v n hv0 hv1 hn)
  constructor <;> linarith [h.1, h.2]

/-- **Chaining**: `e^{−b²/2} = e^{−a²/2}·e^{−(b² − a²)/2}`. -/
theorem exp_chain (a b lo1 hi1 lo2 hi2 : ℝ)
    (h1 : lo1 ≤ Real.exp (-a ^ 2 / 2) ∧ Real.exp (-a ^ 2 / 2) ≤ hi1)
    (h2 : lo2 ≤ Real.exp (-((b ^ 2 - a ^ 2) / 2)) ∧ Real.exp (-((b ^ 2 - a ^ 2) / 2)) ≤ hi2)
    (hlo1 : 0 ≤ lo1) (hlo2 : 0 ≤ lo2) :
    lo1 * lo2 ≤ Real.exp (-b ^ 2 / 2) ∧ Real.exp (-b ^ 2 / 2) ≤ hi1 * hi2 := by
  have e : Real.exp (-b ^ 2 / 2) = Real.exp (-a ^ 2 / 2) * Real.exp (-((b ^ 2 - a ^ 2) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  exact ⟨mul_le_mul h1.1 h2.1 hlo2 (hlo1.trans h1.1),
    mul_le_mul h1.2 h2.2 (Real.exp_pos _).le (hlo1.trans (h1.1.trans h1.2))⟩

/-- `log 8 ≤ 2.0794415424` (`log 2 < 0.6931471808`). -/
theorem log8_le : Real.log 8 ≤ 2.0794415424 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-- `e^{−x} = (e^{−x/m})^m`. -/
theorem exp_neg_pow (x : ℝ) (m : ℕ) (hm : 0 < m) :
    Real.exp (-x) = Real.exp (-(x / m)) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

/-- **A polynomial from its coefficient list**: `pevR [c₀, c₁, …] w = ∑ cᵢ wⁱ`. -/
noncomputable def pevR (cs : List ℝ) (w : ℝ) : ℝ := ∑ i ∈ range cs.length, cs.getD i 0 * w ^ i

/-- `∫_a^b ∑ cᵢwⁱ = ∑ cᵢ(b^{i+1} − a^{i+1})/(i+1)`. -/
theorem int_pevR (a b : ℝ) (cs : List ℝ) :
    ∫ w in a..b, pevR cs w =
      ∑ i ∈ range cs.length, cs.getD i 0 * ((b ^ (i + 1) - a ^ (i + 1)) / (i + 1)) := by
  unfold pevR
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
  · intro i _
    exact (continuous_const.mul (continuous_pow i)).intervalIntegrable _ _

/-- `pevR` is continuous. -/
@[fun_prop]
theorem continuous_pevR (cs : List ℝ) : Continuous (pevR cs) := by
  unfold pevR
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

/-- **The Gaussian moments** `J_k(a,b) = ∫_a^b w^k e^{−w²/2} dw`. -/
noncomputable def mJ (a b : ℝ) (k : ℕ) : ℝ := ∫ w in a..b, w ^ k * Real.exp (-w ^ 2 / 2)

/-- `w ↦ w^k e^{−w²/2}` is continuous. -/
theorem continuous_mom (k : ℕ) : Continuous fun w : ℝ => w ^ k * Real.exp (-w ^ 2 / 2) := by
  fun_prop

/-- `d/dw e^{−w²/2} = −w e^{−w²/2}`. -/
theorem hasDerivAt_gauss (w : ℝ) :
    HasDerivAt (fun w : ℝ => Real.exp (-w ^ 2 / 2)) (-(w * Real.exp (-w ^ 2 / 2))) w := by
  have h1 : HasDerivAt (fun w : ℝ => -w ^ 2 / 2) (-w) w := by
    have h := (hasDerivAt_pow 2 w).div_const (-2)
    have e : (fun w : ℝ => w ^ 2 / (-2)) = fun w : ℝ => -w ^ 2 / 2 := by
      funext w
      ring
    rw [e] at h
    refine h.congr_deriv ?_
    push_cast
    ring
  refine h1.exp.congr_deriv ?_
  ring

/-- **The recursion** `J_{k+2} = (k+1)J_k + a^{k+1}e^{−a²/2} − b^{k+1}e^{−b²/2}`
(`d/dw[−w^{k+1}e^{−w²/2}] = w^{k+2}e^{−w²/2} − (k+1)w^k e^{−w²/2}`). -/
theorem mJ_rec (a b : ℝ) (k : ℕ) :
    mJ a b (k + 2) = (k + 1) * mJ a b k + a ^ (k + 1) * Real.exp (-a ^ 2 / 2) -
      b ^ (k + 1) * Real.exp (-b ^ 2 / 2) := by
  have hd : ∀ w : ℝ, HasDerivAt (fun w : ℝ => -(w ^ (k + 1) * Real.exp (-w ^ 2 / 2)))
      (w ^ (k + 2) * Real.exp (-w ^ 2 / 2) - (k + 1) * (w ^ k * Real.exp (-w ^ 2 / 2))) w := by
    intro w
    have h1 := hasDerivAt_pow (k + 1) w
    refine ((h1.mul (hasDerivAt_gauss w)).neg).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  have hi1 := (continuous_mom (k + 2)).intervalIntegrable (μ := volume) a b
  have hi2 := ((continuous_mom k).const_mul ((k : ℝ) + 1)).intervalIntegrable (μ := volume) a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hd w) (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul] at h
  unfold mJ
  linarith

/-- `J_1 = e^{−a²/2} − e^{−b²/2}`. -/
theorem mJ_one (a b : ℝ) : mJ a b 1 = Real.exp (-a ^ 2 / 2) - Real.exp (-b ^ 2 / 2) := by
  have hd : ∀ w : ℝ, HasDerivAt (fun w : ℝ => -Real.exp (-w ^ 2 / 2))
      (w ^ 1 * Real.exp (-w ^ 2 / 2)) w := by
    intro w
    refine (hasDerivAt_gauss w).neg.congr_deriv ?_
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hd w)
    ((continuous_mom 1).intervalIntegrable (μ := volume) a b)
  unfold mJ
  rw [h]
  ring

/-- `J_k(a,b) + J_k(b,c) = J_k(a,c)`. -/
theorem mJ_add (a b c : ℝ) (k : ℕ) : mJ a b k + mJ b c k = mJ a c k :=
  intervalIntegral.integral_add_adjacent_intervals
    ((continuous_mom k).intervalIntegrable (μ := volume) a b)
    ((continuous_mom k).intervalIntegrable (μ := volume) b c)

/-- **`J₀` by the Taylor polynomial of `e^{−v}`, `v = (w² − a²)/2`**: for `0 ≤ a ≤ b` with
`(b² − a²)/2 ≤ 1` and a polynomial `cs` equal to `∑_{i<n} (−v)^i/i!` on `[a, b]`,
`|J₀ − e^{−a²/2}∫cs| ≤ e^{−a²/2}(b − a)V^n(n+1)/(n!·n)`, `V = (b² − a²)/2`. -/
theorem mJ0_taylor (a b : ℝ) (n : ℕ) (cs : List ℝ) (hn : 0 < n) (ha : 0 ≤ a) (hab : a ≤ b)
    (hV : (b ^ 2 - a ^ 2) / 2 ≤ 1)
    (hcs : ∀ w : ℝ, pevR cs w =
      ∑ i ∈ range n, (-((w ^ 2 - a ^ 2) / 2)) ^ i / (i.factorial : ℝ)) :
    |mJ a b 0 - Real.exp (-a ^ 2 / 2) * ∫ w in a..b, pevR cs w| ≤
      Real.exp (-a ^ 2 / 2) * (b - a) *
        (((b ^ 2 - a ^ 2) / 2) ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n))) := by
  set E := Real.exp (-a ^ 2 / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set C := ((b ^ 2 - a ^ 2) / 2) ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) with hC
  have hpt : ∀ w ∈ Set.uIoc a b,
      ‖w ^ 0 * Real.exp (-w ^ 2 / 2) - E * pevR cs w‖ ≤ E * C := by
    intro w hw
    rw [Set.uIoc_of_le hab] at hw
    have hw0 : 0 ≤ (w ^ 2 - a ^ 2) / 2 := by nlinarith [hw.1]
    have hw1 : (w ^ 2 - a ^ 2) / 2 ≤ (b ^ 2 - a ^ 2) / 2 := by nlinarith [hw.1, hw.2]
    have ht := exp_neg_taylor ((w ^ 2 - a ^ 2) / 2) n hw0 (hw1.trans hV) hn
    have hsplit : Real.exp (-w ^ 2 / 2) = E * Real.exp (-((w ^ 2 - a ^ 2) / 2)) := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    rw [pow_zero, one_mul, hsplit, hcs w, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos hE0]
    refine mul_le_mul_of_nonneg_left (ht.trans ?_) hE0.le
    rw [hC]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw1 n) (by positivity)
  have hint1 := (continuous_mom 0).intervalIntegrable (μ := volume) a b
  have hint2 := ((continuous_pevR cs).const_mul E).intervalIntegrable (μ := volume) a b
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
  unfold mJ
  calc |(∫ w in a..b, w ^ 0 * Real.exp (-w ^ 2 / 2)) - E * ∫ w in a..b, pevR cs w|
      ≤ E * C * (b - a) := h
    _ = E * (b - a) * C := by ring

/-! ## Integral bounds that need no integrability of the integrand -/

/-- **`∫_a^b f ≤ B` whenever `f` is integrable, with `a ≤ b` and `B ≥ 0`.** A non-integrable `f`
has junk integral `0 ≤ B`, so `IntBnd` always yields the bound (`le_of_intBnd`); and it composes
over adjacent intervals with no integrability hypothesis on `f` (`intBnd_add`). -/
def IntBnd (f : ℝ → ℝ) (a b B : ℝ) : Prop :=
  a ≤ b ∧ 0 ≤ B ∧ (IntervalIntegrable f volume a b → ∫ w in a..b, f w ≤ B)

/-- `IntBnd` from a pointwise majorant `g ≥ 0` with `∫ g ≤ B`. -/
theorem intBnd_of (f g : ℝ → ℝ) (a b B : ℝ) (hab : a ≤ b) (hfg : ∀ w ∈ Icc a b, f w ≤ g w)
    (hg0 : ∀ w ∈ Icc a b, 0 ≤ g w) (hgi : IntervalIntegrable g volume a b)
    (hB : ∫ w in a..b, g w ≤ B) : IntBnd f a b B :=
  ⟨hab, (intervalIntegral.integral_nonneg hab hg0).trans hB,
    fun hf => (intervalIntegral.integral_mono_on hab hf hgi hfg).trans hB⟩

/-- `IntBnd` over adjacent intervals adds. -/
theorem intBnd_add (f : ℝ → ℝ) (a m b B1 B2 : ℝ) (h1 : IntBnd f a m B1) (h2 : IntBnd f m b B2) :
    IntBnd f a b (B1 + B2) := by
  obtain ⟨ham, hB1, h1⟩ := h1
  obtain ⟨hmb, hB2, h2⟩ := h2
  refine ⟨ham.trans hmb, add_nonneg hB1 hB2, fun hf => ?_⟩
  have hf1 : IntervalIntegrable f volume a m := hf.mono_set (by
    rw [uIcc_of_le ham, uIcc_of_le (ham.trans hmb)]
    exact Icc_subset_Icc le_rfl hmb)
  have hf2 : IntervalIntegrable f volume m b := hf.mono_set (by
    rw [uIcc_of_le hmb, uIcc_of_le (ham.trans hmb)]
    exact Icc_subset_Icc ham le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hf1 hf2]
  linarith [h1 hf1, h2 hf2]

/-- `IntBnd` weakens as `B` grows. -/
theorem intBnd_mono (f : ℝ → ℝ) (a b B B' : ℝ) (h : IntBnd f a b B) (hB : B ≤ B') :
    IntBnd f a b B' :=
  ⟨h.1, h.2.1.trans hB, fun hf => (h.2.2 hf).trans hB⟩

/-- **`IntBnd` gives the bound**, integrable or not. -/
theorem le_of_intBnd (f : ℝ → ℝ) (a b B : ℝ) (h : IntBnd f a b B) : ∫ w in a..b, f w ≤ B := by
  by_cases hf : IntervalIntegrable f volume a b
  · exact h.2.2 hf
  · rw [intervalIntegral.integral_undef hf]
    exact h.2.1

/-- **The same on `(q, ∞)`.** -/
def IntBndI (f : ℝ → ℝ) (q B : ℝ) : Prop :=
  0 ≤ B ∧ (IntegrableOn f (Ioi q) → ∫ w in Ioi q, f w ≤ B)

/-- `[p, q]` then `(q, ∞)`. -/
theorem intBndI_add (f : ℝ → ℝ) (p q B1 B2 : ℝ) (h1 : IntBnd f p q B1) (h2 : IntBndI f q B2) :
    IntBndI f p (B1 + B2) := by
  obtain ⟨hpq, hB1, h1⟩ := h1
  obtain ⟨hB2, h2⟩ := h2
  refine ⟨add_nonneg hB1 hB2, fun hf => ?_⟩
  have hf1 : IntegrableOn f (Ioc p q) := hf.mono_set Ioc_subset_Ioi_self
  have hf2 : IntegrableOn f (Ioi q) := hf.mono_set (Ioi_subset_Ioi hpq)
  have hu : Ioc p q ∪ Ioi q = Ioi p := Ioc_union_Ioi_eq_Ioi hpq
  rw [← hu, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hf1 hf2,
    ← intervalIntegral.integral_of_le hpq]
  have hi : IntervalIntegrable f volume p q :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mpr hf1
  linarith [h1 hi, h2 hf2]

/-- `IntBndI` gives the bound, integrable or not. -/
theorem le_of_intBndI (f : ℝ → ℝ) (q B : ℝ) (h : IntBndI f q B) : ∫ w in Ioi q, f w ≤ B := by
  by_cases hf : IntegrableOn f (Ioi q)
  · exact h.2 hf
  · rw [integral_undef hf]
    exact h.1

/-- `(w² + 2)e^{−w²/2} → 0`. -/
theorem tendsto_gtail :
    Tendsto (fun w : ℝ => -((w ^ 2 + 2) * Real.exp (-w ^ 2 / 2))) atTop (𝓝 0) := by
  have hx : Tendsto (fun w : ℝ => w ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
  have h := ((h1.const_mul 2).add (h0.const_mul 2)).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  refine h.congr fun w => ?_
  simp only [Function.comp]
  have e : -w ^ 2 / 2 = -(w ^ 2 / 2) := by ring
  rw [e]
  ring

/-- **`∫_q^∞ w³e^{−w²/2} = (q² + 2)e^{−q²/2}`**, and `w³e^{−w²/2}` is integrable there. -/
theorem int_w3_tail (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun w : ℝ => w ^ 3 * Real.exp (-w ^ 2 / 2)) (Ioi q) ∧
      ∫ w in Ioi q, w ^ 3 * Real.exp (-w ^ 2 / 2) = (q ^ 2 + 2) * Real.exp (-q ^ 2 / 2) := by
  have hd : ∀ w ∈ Ici q, HasDerivAt (fun w : ℝ => -((w ^ 2 + 2) * Real.exp (-w ^ 2 / 2)))
      (w ^ 3 * Real.exp (-w ^ 2 / 2)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + 2) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).add_const 2
    have h2 : HasDerivAt (fun w : ℝ => -w ^ 2 / 2) (-w) w := by
      have h := (hasDerivAt_pow 2 w).div_const (-2)
      have e : (fun w : ℝ => w ^ 2 / (-2)) = fun w : ℝ => -w ^ 2 / 2 := by
        funext w
        ring
      rw [e] at h
      refine h.congr_deriv ?_
      push_cast
      ring
    refine ((h1.mul h2.exp).neg).congr_deriv ?_
    ring
  have hpos : ∀ w ∈ Ioi q, 0 ≤ w ^ 3 * Real.exp (-w ^ 2 / 2) := fun w hw => by
    have : 0 ≤ w := hq.trans (le_of_lt hw)
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos tendsto_gtail, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos tendsto_gtail]
  ring

/-- **The Gaussian tail piece**: `f(w) ≤ K w³ e^{−w²/2}/q` on `(q, ∞)` gives
`IntBndI f q (K(q² + 2)e^{−q²/2}/q)`. -/
theorem intBndI_tail (f : ℝ → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hf : ∀ w ∈ Ioi q, f w ≤ K / q * (w ^ 3 * Real.exp (-w ^ 2 / 2))) :
    IntBndI f q (K / q * ((q ^ 2 + 2) * Real.exp (-q ^ 2 / 2))) := by
  obtain ⟨hint, hval⟩ := int_w3_tail q hq.le
  refine ⟨by positivity, fun hfi => ?_⟩
  have h := setIntegral_mono_on hfi (hint.const_mul (K / q)) measurableSet_Ioi hf
  rw [integral_const_mul, hval] at h
  exact h

/-! ## The three factors of `g_Y`: `R`, `√F`, `L` -/

/-- **`R_{z,t}` by the tangent of `log` at `1 + u*`**: with `log 4t ≤ N̄`, `0 < D̲ ≤
log(9z^{1/3}/(2.004t))`, `ρ₁(1 + u*) = 0.27125` and `0.27125·lus − ρ₁u* + 0.41415 ≤ ρ₀`
(`lus ≥ log(1 + u*)`): `R_{z,t} ≤ ρ₀ + ρ₁N̄/(2D̲)`. -/
theorem rR_tan (z t Nb Db us lus ρ0 ρ1 : ℝ) (ht : 1 / 4 ≤ t) (hN : Real.log (4 * t) ≤ Nb)
    (hDb : 0 < Db) (hD : Db ≤ Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))) (hus : 0 ≤ us)
    (hlus : Real.log (1 + us) ≤ lus) (hρ1 : ρ1 * (1 + us) = 0.27125)
    (hρ0 : 0.27125 * lus - ρ1 * us + 0.41415 ≤ ρ0) :
    rR z t ≤ ρ0 + ρ1 * (Nb / (2 * Db)) := by
  have h4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  set D := Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t))
  have hq : Real.log (4 * t) / (2 * D) ≤ Nb / (2 * Db) :=
    div_le_div₀ (by linarith) hN (by linarith) (by linarith)
  have hq0 : 0 ≤ Real.log (4 * t) / (2 * D) := div_nonneg h4 (by linarith)
  set q := Real.log (4 * t) / (2 * D)
  have hus1 : 0 < 1 + us := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < 1 + q) hus1)
  rw [Real.log_div (by linarith) hus1.ne'] at hl
  have hρ1' : ρ1 = 0.27125 / (1 + us) := by
    rw [eq_div_iff hus1.ne']
    exact hρ1
  have e : (1 + q) / (1 + us) - 1 = (q - us) / (1 + us) := by field_simp; ring
  rw [e] at hl
  have hρ10 : 0 ≤ ρ1 := by rw [hρ1']; positivity
  have key : 0.27125 * ((q - us) / (1 + us)) = ρ1 * (q - us) := by rw [hρ1']; ring
  have hrR : rR z t = 0.27125 * Real.log (1 + q) + 0.41415 := rfl
  rw [hrR]
  have h1 : 0.27125 * Real.log (1 + q) ≤ 0.27125 * lus + ρ1 * (q - us) := by
    rw [← key]
    nlinarith
  have h2 : ρ1 * q ≤ ρ1 * (Nb / (2 * Db)) := mul_le_mul_of_nonneg_left hq hρ10
  linarith

/-- **A chord of `1/(K − ξ)` lies above it** on `[ξ₀, ξ₁]` (`K > ξ₁`): checked at the two ends,
`(K − ξ₀)A ≥ 1`, `(K − ξ₁)(A + B(ξ₁ − ξ₀)) ≥ 1`, `B ≥ 0` (the product is concave in `ξ`). -/
theorem chord_inv (K ξ ξ0 ξ1 A B : ℝ) (h0 : ξ0 ≤ ξ) (h1 : ξ ≤ ξ1) (hK : 0 < K - ξ1) (hB : 0 ≤ B)
    (hA : 1 ≤ (K - ξ0) * A) (hAB : 1 ≤ (K - ξ1) * (A + B * (ξ1 - ξ0))) :
    1 / (K - ξ) ≤ A + B * (ξ - ξ0) := by
  have hKx : 0 < K - ξ := by linarith
  rw [div_le_iff₀ hKx]
  rcases eq_or_lt_of_le (h0.trans h1) with he | hlt
  · have hx : ξ = ξ0 := le_antisymm (he ▸ h1) h0
    rw [hx, sub_self, mul_zero, add_zero, mul_comm]
    exact hA
  · have hd : 0 < ξ1 - ξ0 := by linarith
    have k1 : 0 ≤ ((K - ξ0) * A - 1) * (ξ1 - ξ) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ ((K - ξ1) * (A + B * (ξ1 - ξ0)) - 1) * (ξ - ξ0) :=
      mul_nonneg (by linarith) (by linarith)
    have k3 : 0 ≤ B * (ξ - ξ0) * (ξ1 - ξ) * (ξ1 - ξ0) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hB (sub_nonneg.2 h0)) (sub_nonneg.2 h1)) hd.le
      linarith
    have key : (ξ1 - ξ0) * ((A + B * (ξ - ξ0)) * (K - ξ) - 1) =
        ((K - ξ0) * A - 1) * (ξ1 - ξ) + ((K - ξ1) * (A + B * (ξ1 - ξ0)) - 1) * (ξ - ξ0) +
          B * (ξ - ξ0) * (ξ1 - ξ) * (ξ1 - ξ0) := by ring
    have h3 : 0 ≤ (ξ1 - ξ0) * ((A + B * (ξ - ξ0)) * (K - ξ) - 1) := by rw [key]; linarith
    have h4 := (mul_nonneg_iff_of_pos_left hd).mp h3
    linarith

/-- **`R_{wy, 2wr}` for `w < 1`, jointly linear-times-linear in `(log r, w)`**:
`log 8wr ≤ c₈ + log r + τ(w)` and `log(9(wy)^{1/3}/(4.008wr)) ≥ K_D − ξ`, `ξ = log r + (2/3)τ(w)`,
`τ(w) = τ₀ + τ₁w ≥ log w`, then `rR_tan` and `chord_inv`. -/
theorem rChordLo (y r w KD c8 τ0 τ1 ξ0 ξ1 A B us lus ρ0 ρ1 : ℝ) (hy : 0 < y) (hr : 0 < r)
    (hw : 0 < w) (hwr : 1 ≤ 8 * (w * r)) (hτ : Real.log w ≤ τ0 + τ1 * w)
    (hKD : KD ≤ Real.log 9 - Real.log 2.004 - Real.log 2 + Real.log y / 3)
    (hc8 : Real.log 8 ≤ c8) (hξ0 : ξ0 ≤ Real.log r + 2 / 3 * (τ0 + τ1 * w))
    (hξ1 : Real.log r + 2 / 3 * (τ0 + τ1 * w) ≤ ξ1) (hK : 0 < KD - ξ1) (hB : 0 ≤ B)
    (hA : 1 ≤ (KD - ξ0) * A) (hAB : 1 ≤ (KD - ξ1) * (A + B * (ξ1 - ξ0))) (hus : 0 ≤ us)
    (hlus : Real.log (1 + us) ≤ lus) (hρ1 : ρ1 * (1 + us) = 0.27125)
    (hρ0 : 0.27125 * lus - ρ1 * us + 0.41415 ≤ ρ0) :
    0 ≤ rR (w * y) (2 * (w * r)) ∧ rR (w * y) (2 * (w * r)) ≤
      ρ0 + ρ1 * ((c8 + Real.log r + (τ0 + τ1 * w)) *
      (A + B * (Real.log r + 2 / 3 * (τ0 + τ1 * w) - ξ0)) / 2) := by
  set ξ := Real.log r + 2 / 3 * (τ0 + τ1 * w) with hξ
  have hwr0 : 0 < w * r := mul_pos hw hr
  have hN : Real.log (4 * (2 * (w * r))) ≤ c8 + Real.log r + (τ0 + τ1 * w) := by
    rw [show (4 : ℝ) * (2 * (w * r)) = 8 * w * r by ring, Real.log_mul (by positivity) hr.ne',
      Real.log_mul (by norm_num) hw.ne']
    linarith
  have hN0 : 0 ≤ Real.log (4 * (2 * (w * r))) := Real.log_nonneg (by linarith)
  have hD : KD - ξ ≤ Real.log (9 * (w * y) ^ ((1 : ℝ) / 3) / (2.004 * (2 * (w * r)))) := by
    rw [MN.logD_eq _ _ (mul_pos hw hy) (by positivity), Real.log_mul hw.ne' hy.ne',
      show (2.004 : ℝ) * (2 * (w * r)) = 2.004 * 2 * w * r by ring,
      Real.log_mul (by positivity) hr.ne', Real.log_mul (by positivity) hw.ne',
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hKx : 0 < KD - ξ := by linarith
  have hR := rR_tan (w * y) (2 * (w * r)) (c8 + Real.log r + (τ0 + τ1 * w)) (KD - ξ) us lus ρ0 ρ1
    (by linarith) hN hKx hD hus hlus hρ1 hρ0
  have hch := chord_inv KD ξ ξ0 ξ1 A B hξ0 hξ1 hK hB hA hAB
  have hNb : 0 ≤ c8 + Real.log r + (τ0 + τ1 * w) := hN0.trans hN
  have hρ10 : 0 ≤ ρ1 := by
    have : (0 : ℝ) < 1 + us := by linarith
    nlinarith
  have hq : (c8 + Real.log r + (τ0 + τ1 * w)) / (2 * (KD - ξ)) ≤
      (c8 + Real.log r + (τ0 + τ1 * w)) * (A + B * (ξ - ξ0)) / 2 := by
    have e : (c8 + Real.log r + (τ0 + τ1 * w)) / (2 * (KD - ξ)) =
        (c8 + Real.log r + (τ0 + τ1 * w)) * (1 / (KD - ξ)) / 2 := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hch hNb
    linarith
  have := mul_le_mul_of_nonneg_left hq hρ10
  exact ⟨le_trans (by norm_num) (MN.rR_ge _ _ (by linarith) (by linarith)), by linarith⟩

/-- **`R_{wy, 2r}` for `w ≥ 1`**: `log(9(wy)^{1/3}/(4.008r)) ≥ K_D − ξ`, `ξ = log r − τ(w)/3`,
`τ(w) = τ₀ + τ₁w ≤ log w`. -/
theorem rChordHi (y r w KD c8 τ0 τ1 ξ0 ξ1 A B us lus ρ0 ρ1 : ℝ) (hy : 0 < y) (hr : 0 < r)
    (hw : 0 < w) (hr8 : 1 ≤ 8 * r) (hτ : τ0 + τ1 * w ≤ Real.log w)
    (hKD : KD ≤ Real.log 9 - Real.log 2.004 - Real.log 2 + Real.log y / 3)
    (hc8 : Real.log 8 ≤ c8) (hξ0 : ξ0 ≤ Real.log r - (τ0 + τ1 * w) / 3)
    (hξ1 : Real.log r - (τ0 + τ1 * w) / 3 ≤ ξ1) (hK : 0 < KD - ξ1) (hB : 0 ≤ B)
    (hA : 1 ≤ (KD - ξ0) * A) (hAB : 1 ≤ (KD - ξ1) * (A + B * (ξ1 - ξ0))) (hus : 0 ≤ us)
    (hlus : Real.log (1 + us) ≤ lus) (hρ1 : ρ1 * (1 + us) = 0.27125)
    (hρ0 : 0.27125 * lus - ρ1 * us + 0.41415 ≤ ρ0) :
    0 ≤ rR (w * y) (2 * r) ∧ rR (w * y) (2 * r) ≤ ρ0 + ρ1 * ((c8 + Real.log r) *
      (A + B * (Real.log r - (τ0 + τ1 * w) / 3 - ξ0)) / 2) := by
  set ξ := Real.log r - (τ0 + τ1 * w) / 3 with hξ
  have hN : Real.log (4 * (2 * r)) ≤ c8 + Real.log r := by
    rw [show (4 : ℝ) * (2 * r) = 8 * r by ring, Real.log_mul (by norm_num) hr.ne']
    linarith
  have hN0 : 0 ≤ Real.log (4 * (2 * r)) := Real.log_nonneg (by linarith)
  have hD : KD - ξ ≤ Real.log (9 * (w * y) ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))) := by
    rw [MN.logD_eq _ _ (mul_pos hw hy) (by positivity), Real.log_mul hw.ne' hy.ne',
      show (2.004 : ℝ) * (2 * r) = 2.004 * 2 * r by ring, Real.log_mul (by norm_num) hr.ne',
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hKx : 0 < KD - ξ := by linarith
  have hR := rR_tan (w * y) (2 * r) (c8 + Real.log r) (KD - ξ) us lus ρ0 ρ1
    (by linarith) hN hKx hD hus hlus hρ1 hρ0
  have hch := chord_inv KD ξ ξ0 ξ1 A B hξ0 hξ1 hK hB hA hAB
  have hNb : 0 ≤ c8 + Real.log r := hN0.trans hN
  have hρ10 : 0 ≤ ρ1 := by
    have : (0 : ℝ) < 1 + us := by linarith
    nlinarith
  have hq : (c8 + Real.log r) / (2 * (KD - ξ)) ≤ (c8 + Real.log r) * (A + B * (ξ - ξ0)) / 2 := by
    have e : (c8 + Real.log r) / (2 * (KD - ξ)) = (c8 + Real.log r) * (1 / (KD - ξ)) / 2 := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hch hNb
    linarith
  have := mul_le_mul_of_nonneg_left hq hρ10
  exact ⟨le_trans (by norm_num) (MN.rR_ge _ _ (by linarith) (by linarith)), by linarith⟩

/-- **`F(t) = e^γ log log t + 2.50637/log log t`** by the tangent of `log` at `L_s` and
`log log t ≥ λ_lo > 0`: `F(t) ≤ 1.7810727(λ_s − 1 + ℓ_t/L_s) + 2.50637/λ_lo` for `log t ≤ ℓ_t`. -/
theorem bigF_le_tan (t Llo lamlo Ls lams lt : ℝ) (hLlo0 : 0 < Llo)
    (hLlo : Llo ≤ Real.log t) (hlamlo : lamlo ≤ Real.log Llo) (hlamlo0 : 0 < lamlo) (hLs : 0 < Ls)
    (hlams : Real.log Ls ≤ lams) (hlt : Real.log t ≤ lt) :
    0 ≤ bigF t ∧ bigF t ≤ 1.7810727 * (lams - 1 + lt / Ls) + 2.50637 / lamlo := by
  have hl0 : 0 < Real.log t := lt_of_lt_of_le hLlo0 hLlo
  have hu : lamlo ≤ Real.log (Real.log t) := hlamlo.trans (Real.log_le_log hLlo0 hLlo)
  have hu0 : 0 < Real.log (Real.log t) := lt_of_lt_of_le hlamlo0 hu
  have htan := log_le_tan_aux (Real.log t) Ls lams hl0 hLs hlams
  have hdiv : lt / Ls ≥ Real.log t / Ls := div_le_div_of_nonneg_right hlt hLs.le
  have hE := expG_le
  have hE0 := Real.exp_pos Real.eulerMascheroniConstant
  have h1 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log t) ≤
      1.7810727 * (lams - 1 + lt / Ls) := by
    have := mul_le_mul hE (by linarith : Real.log (Real.log t) ≤ lams - 1 + lt / Ls) hu0.le
      (by norm_num)
    linarith
  have h2 : 2.50637 / Real.log (Real.log t) ≤ 2.50637 / lamlo :=
    div_le_div_of_nonneg_left (by norm_num) hlamlo0 hu
  unfold bigF
  constructor
  · have := mul_pos hE0 hu0
    have : 0 ≤ 2.50637 / Real.log (Real.log t) := div_nonneg (by norm_num) hu0.le
    linarith
  · linarith
where
  log_le_tan_aux (w m LM : ℝ) (hw : 0 < w) (hm : 0 < m) (hLM : Real.log m ≤ LM) :
      Real.log w ≤ LM - 1 + w / m := by
    have h := Real.log_le_sub_one_of_pos (div_pos hw hm)
    rw [Real.log_div hw.ne' hm.ne'] at h
    linarith

/-- **`√F ≤ (F + c²)/(2c)`** (AM–GM). -/
theorem sqrt_le_amgm (F c : ℝ) (hc : 0 < c) (hF : 0 ≤ F) : Real.sqrt F ≤ (F + c ^ 2) / (2 * c) := by
  rw [le_div_iff₀ (by positivity)]
  have h := Real.sq_sqrt hF
  nlinarith [sq_nonneg (Real.sqrt F - c)]

/-- **`L_t` (`eq:veror`)** from `F(t) ≤ F̄`, `0 ≤ log t ≤ ℓ_t`, `log 2 ≤ c₂`. -/
theorem lL_le_of (t lt Fb c2 : ℝ) (ht : 0 < t) (hl0 : 0 ≤ Real.log t) (hlt : Real.log t ≤ lt)
    (hF0 : 0 ≤ bigF t) (hF : bigF t ≤ Fb) (hc2 : Real.log 2 ≤ c2) :
    lL t ≤ Fb * (7 / 4 * c2 + 13 / 4 * lt + 80 / 9) + 16 / 9 * c2 + 80 / 9 * lt + 111 / 5 := by
  have h2 := Real.log_two_gt_d9
  have e1 : Real.log (2 ^ ((7 : ℝ) / 4) * t ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log 2 + 13 / 4 * Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow ht]
  have e2 : Real.log (2 ^ ((16 : ℝ) / 9) * t ^ ((80 : ℝ) / 9)) =
      16 / 9 * Real.log 2 + 80 / 9 * Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow ht]
  unfold lL
  rw [e1, e2]
  have hm : 0 ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9 := by linarith
  have k1 := mul_le_mul_of_nonneg_right hF hm
  have k2 : Fb * (7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9) ≤
      Fb * (7 / 4 * c2 + 13 / 4 * lt + 80 / 9) :=
    mul_le_mul_of_nonneg_left (by linarith) (hF0.trans hF)
  linarith

/-- `Y^{−1/6} ≤ Ȳ` from `1 ≤ Ȳ⁶Y`. -/
theorem rpow_neg6_le (Y Yb : ℝ) (hY : 0 < Y) (hYb : 0 < Yb) (h : 1 ≤ Yb ^ 6 * Y) :
    Y ^ (-(1 : ℝ) / 6) ≤ Yb := by
  have h1 : (1 / Yb) ^ 6 ≤ Y ^ 1 := by
    rw [div_pow, one_pow, pow_one, div_le_iff₀ (by positivity)]
    linarith
  have h2 := MN.le_rpow_of_pow Y (1 / Yb) 1 6 (by norm_num) hY.le (by positivity) h1
  rw [show ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 6 by norm_num] at h2
  rw [show -(1 : ℝ) / 6 = -(1 / 6) by ring, Real.rpow_neg hY.le]
  rw [div_le_iff₀ hYb] at h2
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

/-- `(wy)^{−1/6} ≤ (aY₀)^{−1/6}` for `w ≥ a > 0`, `y ≥ Y₀ > 0`. -/
theorem wy_rpow_le (w y a Y0 : ℝ) (ha : 0 < a) (hw : a ≤ w) (hY0 : 0 < Y0) (hy : Y0 ≤ y) :
    (w * y) ^ (-(1 : ℝ) / 6) ≤ (a * Y0) ^ (-(1 : ℝ) / 6) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (mul_le_mul hw hy hY0.le (ha.le.trans hw))
    (by norm_num)



/-! ## The pointwise envelopes of `g_Y φ` -/

/-- `1/√2 ≤ 0.70711`. -/
theorem inv_sqrt_two_le : 1 / Real.sqrt 2 ≤ 0.70711 := by
  rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  have := MN.sqrt_two_ge
  linarith

/-- **The numerator of `g_Y`** `(R·log 2t + ½)√F + 5/2 ≤ (R̄Λ + ½)S̄ + 5/2`. -/
theorem num_le (R Rb L Lam sF Sb : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ Rb) (hL0 : 0 ≤ L) (hL : L ≤ Lam)
    (hs0 : 0 ≤ sF) (hS : sF ≤ Sb) :
    (R * L + 0.5) * sF + 2.5 ≤ (Rb * Lam + 0.5) * Sb + 2.5 := by
  have h1 : R * L ≤ Rb * Lam := mul_le_mul hR hL hL0 (hR0.trans hR)
  have h2 : 0 ≤ R * L + 0.5 := by nlinarith
  have := mul_le_mul (by linarith : R * L + 0.5 ≤ Rb * Lam + 0.5) hS hs0 (by linarith)
  linarith

/-- **`g_{wy}(wr)φ(w)` for `w` in a piece of `(0, 1]`** (the Main-Theorem part of `gT`):
with `1/√w ≤ I_q`, `0 ≤ R_{wy,2wr} ≤ R̄`, `0 ≤ log 2wr ≤ Λ`, `√F(wr) ≤ S̄`, `L_{wr} ≤ L̄`,
`(wy)^{−1/6} ≤ Ȳ`:
`g φ ≤ (0.70711 I_q((R̄Λ + ½)S̄ + 5/2)w²/√r + L̄w/r + 3.2Ȳw²)e^{−w²/2}`. -/
theorem ptLo (y r w Iq Rb Lam Sb Lb Yb : ℝ) (hr : 0 < r) (hw : 0 < w)
    (hq : 1 / Real.sqrt w ≤ Iq) (hR0 : 0 ≤ rR (w * y) (2 * (w * r)))
    (hR : rR (w * y) (2 * (w * r)) ≤ Rb) (hL0 : 0 ≤ Real.log (2 * (w * r)))
    (hL : Real.log (2 * (w * r)) ≤ Lam) (hS : Real.sqrt (bigF (w * r)) ≤ Sb)
    (hLL : lL (w * r) ≤ Lb) (hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ Yb) :
    OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * Iq * ((Rb * Lam + 0.5) * Sb + 2.5) * w ^ 2 * (1 / Real.sqrt r) +
        Lb * w * (1 / r) + 3.2 * Yb * w ^ 2) * Real.exp (-w ^ 2 / 2) := by
  have hwr : 0 < w * r := mul_pos hw hr
  have hE := Real.exp_pos (-w ^ 2 / 2)
  have hsF := Real.sqrt_nonneg (bigF (w * r))
  have hN := num_le _ Rb _ Lam _ Sb hR0 hR hL0 hL hsF hS
  have hN0 : 0 ≤ (rR (w * y) (2 * (w * r)) * Real.log (2 * (w * r)) + 0.5) *
      Real.sqrt (bigF (w * r)) + 2.5 := by
    have := mul_nonneg hR0 hL0
    positivity
  set N := (rR (w * y) (2 * (w * r)) * Real.log (2 * (w * r)) + 0.5) * Real.sqrt (bigF (w * r)) +
    2.5
  set Nb := (Rb * Lam + 0.5) * Sb + 2.5
  have hsw := Real.sqrt_pos.mpr hw
  have hsr := Real.sqrt_pos.mpr hr
  have hs2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hsplit : Real.sqrt (2 * (w * r)) = Real.sqrt 2 * Real.sqrt w * Real.sqrt r := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hw.le, mul_assoc]
  have hIq0 : 0 ≤ Iq := le_trans (by positivity) hq
  have h1 : N / Real.sqrt (2 * (w * r)) ≤ 0.70711 * Iq * Nb * (1 / Real.sqrt r) := by
    rw [hsplit]
    have e : N / (Real.sqrt 2 * Real.sqrt w * Real.sqrt r) =
        N * (1 / Real.sqrt 2) * (1 / Real.sqrt w) * (1 / Real.sqrt r) := by
      field_simp
    rw [e]
    have k1 : N * (1 / Real.sqrt 2) ≤ Nb * 0.70711 :=
      mul_le_mul hN inv_sqrt_two_le (by positivity) (hN0.trans hN)
    have k2 : N * (1 / Real.sqrt 2) * (1 / Real.sqrt w) ≤ Nb * 0.70711 * Iq :=
      mul_le_mul k1 hq (by positivity) (by nlinarith)
    have k3 := mul_le_mul_of_nonneg_right k2 (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt r)
    linarith
  have h2 : lL (w * r) / (w * r) * w ^ 2 = lL (w * r) * w * (1 / r) := by
    field_simp
  have h3 : lL (w * r) * w * (1 / r) ≤ Lb * w * (1 / r) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLL hw.le) (by positivity)
  unfold OC.gY HW.phi
  have t1 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ w ^ 2 * Real.exp (-w ^ 2 / 2))
  have t2 := mul_le_mul_of_nonneg_right h3 hE.le
  have t3 : 3.2 * (w * y) ^ (-(1 : ℝ) / 6) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) ≤
      3.2 * Yb * (w ^ 2 * Real.exp (-w ^ 2 / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e2 : lL (w * r) / (w * r) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) =
      lL (w * r) * w * (1 / r) * Real.exp (-w ^ 2 / 2) := by
    rw [← mul_assoc, h2]
  calc (N / Real.sqrt (2 * (w * r)) + lL (w * r) / (w * r) + 3.2 * (w * y) ^ (-(1 : ℝ) / 6)) *
        (w ^ 2 * Real.exp (-w ^ 2 / 2))
      = N / Real.sqrt (2 * (w * r)) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) +
          lL (w * r) * w * (1 / r) * Real.exp (-w ^ 2 / 2) +
          3.2 * (w * y) ^ (-(1 : ℝ) / 6) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) := by
        rw [← e2]
        ring
    _ ≤ 0.70711 * Iq * Nb * (1 / Real.sqrt r) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) +
          Lb * w * (1 / r) * Real.exp (-w ^ 2 / 2) +
          3.2 * Yb * (w ^ 2 * Real.exp (-w ^ 2 / 2)) := by
        linarith
    _ = _ := by ring

/-- **`g_{wy}(r)φ(w)` for `w ≥ 1`** (the part of `gT` where the argument stays `r`). -/
theorem ptHi (y r w Rb Lam Sb Lb Yb : ℝ) (hr : 0 < r) (hw : 0 < w)
    (hR0 : 0 ≤ rR (w * y) (2 * r)) (hR : rR (w * y) (2 * r) ≤ Rb) (hL0 : 0 ≤ Real.log (2 * r))
    (hL : Real.log (2 * r) ≤ Lam) (hS : Real.sqrt (bigF r) ≤ Sb) (hLL : lL r ≤ Lb)
    (hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ Yb) :
    OC.gY (w * y) r * HW.phi w ≤
      (0.70711 * ((Rb * Lam + 0.5) * Sb + 2.5) * w ^ 2 * (1 / Real.sqrt r) +
        Lb * w ^ 2 * (1 / r) + 3.2 * Yb * w ^ 2) * Real.exp (-w ^ 2 / 2) := by
  have hE := Real.exp_pos (-w ^ 2 / 2)
  have hsF := Real.sqrt_nonneg (bigF r)
  have hN := num_le _ Rb _ Lam _ Sb hR0 hR hL0 hL hsF hS
  have hN0 : 0 ≤ (rR (w * y) (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (bigF r) + 2.5 := by
    have := mul_nonneg hR0 hL0
    positivity
  set N := (rR (w * y) (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (bigF r) + 2.5
  set Nb := (Rb * Lam + 0.5) * Sb + 2.5
  have hsr := Real.sqrt_pos.mpr hr
  have hsplit : Real.sqrt (2 * r) = Real.sqrt 2 * Real.sqrt r := Real.sqrt_mul (by norm_num) r
  have h1 : N / Real.sqrt (2 * r) ≤ 0.70711 * Nb * (1 / Real.sqrt r) := by
    rw [hsplit]
    have e : N / (Real.sqrt 2 * Real.sqrt r) = N * (1 / Real.sqrt 2) * (1 / Real.sqrt r) := by
      field_simp
    rw [e]
    have k1 : N * (1 / Real.sqrt 2) ≤ Nb * 0.70711 :=
      mul_le_mul hN inv_sqrt_two_le (by positivity) (hN0.trans hN)
    have k3 := mul_le_mul_of_nonneg_right k1 (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt r)
    linarith
  have h3 : lL r / r ≤ Lb * (1 / r) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hLL (by positivity)
  unfold OC.gY HW.phi
  have hw2 : 0 ≤ w ^ 2 * Real.exp (-w ^ 2 / 2) := by positivity
  have t1 := mul_le_mul_of_nonneg_right h1 hw2
  have t2 := mul_le_mul_of_nonneg_right h3 hw2
  have t3 : 3.2 * (w * y) ^ (-(1 : ℝ) / 6) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) ≤
      3.2 * Yb * (w ^ 2 * Real.exp (-w ^ 2 / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hw2
  calc (N / Real.sqrt (2 * r) + lL r / r + 3.2 * (w * y) ^ (-(1 : ℝ) / 6)) *
        (w ^ 2 * Real.exp (-w ^ 2 / 2))
      = N / Real.sqrt (2 * r) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) +
          lL r / r * (w ^ 2 * Real.exp (-w ^ 2 / 2)) +
          3.2 * (w * y) ^ (-(1 : ℝ) / 6) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) := by ring
    _ ≤ 0.70711 * Nb * (1 / Real.sqrt r) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) +
          Lb * (1 / r) * (w ^ 2 * Real.exp (-w ^ 2 / 2)) +
          3.2 * Yb * (w ^ 2 * Real.exp (-w ^ 2 / 2)) := by linarith
    _ = _ := by ring

/-- **The first piece `w ∈ (0, p₁]`, crudely**: `w²/√w ≤ √p₁·w` and `e^{−w²/2} ≤ 1`:
`g φ ≤ (0.70711√p₁((R̄Λ + ½)S̄ + 5/2)/√r + L̄/r + 3.2Ȳ₁)w`, with `(wy)^{−1/6}w ≤ Ȳ₁`. -/
theorem ptFirst (y r w sp Rb Lam Sb Lb Yb : ℝ) (hy : 0 < y) (hr : 0 < r) (hw : 0 < w)
    (hsp : Real.sqrt w ≤ sp) (hR0 : 0 ≤ rR (w * y) (2 * (w * r)))
    (hR : rR (w * y) (2 * (w * r)) ≤ Rb) (hL0 : 0 ≤ Real.log (2 * (w * r)))
    (hL : Real.log (2 * (w * r)) ≤ Lam) (hS : Real.sqrt (bigF (w * r)) ≤ Sb)
    (hLL0 : 0 ≤ lL (w * r)) (hLL : lL (w * r) ≤ Lb) (hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ Yb) :
    OC.gY (w * y) (w * r) * HW.phi w ≤
      (0.70711 * sp * ((Rb * Lam + 0.5) * Sb + 2.5) * (1 / Real.sqrt r) + Lb * (1 / r) +
        3.2 * Yb) * w := by
  have h := ptLo y r w (1 / Real.sqrt w) Rb Lam Sb Lb ((w * y) ^ (-(1 : ℝ) / 6)) hr hw le_rfl hR0
    hR hL0 hL hS hLL le_rfl
  have hsw := Real.sqrt_pos.mpr hw
  have hsr := Real.sqrt_pos.mpr hr
  have hE1 : Real.exp (-w ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg w]
  have hE0 := Real.exp_pos (-w ^ 2 / 2)
  have hsF := Real.sqrt_nonneg (bigF (w * r))
  have hRb0 : 0 ≤ Rb := hR0.trans hR
  have hLam0 : 0 ≤ Lam := hL0.trans hL
  have hSb0 : 0 ≤ Sb := hsF.trans hS
  have hLb0 : 0 ≤ Lb := hLL0.trans hLL
  have hNb0 : 0 ≤ (Rb * Lam + 0.5) * Sb + 2.5 := by
    have := mul_nonneg hRb0 hLam0
    positivity
  set Nb := (Rb * Lam + 0.5) * Sb + 2.5
  have hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (mul_pos hw hy).le _
  have hw2 : 1 / Real.sqrt w * w ^ 2 = Real.sqrt w * w := by
    rw [show 1 / Real.sqrt w * w ^ 2 = w / Real.sqrt w * w by ring, Real.div_sqrt]
  have hT0 : 0 ≤ 0.70711 * (1 / Real.sqrt w) * Nb * w ^ 2 * (1 / Real.sqrt r) +
      Lb * w * (1 / r) + 3.2 * (w * y) ^ (-(1 : ℝ) / 6) * w ^ 2 := by positivity
  have hTe := mul_le_mul_of_nonneg_left hE1 hT0
  have e1 : 0.70711 * (1 / Real.sqrt w) * Nb * w ^ 2 * (1 / Real.sqrt r) =
      0.70711 * Nb * (1 / Real.sqrt r) * (Real.sqrt w * w) := by
    rw [← hw2]
    ring
  have k1 : 0.70711 * Nb * (1 / Real.sqrt r) * (Real.sqrt w * w) ≤
      0.70711 * Nb * (1 / Real.sqrt r) * (sp * w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsp hw.le) (by positivity)
  have k3 : 3.2 * (w * y) ^ (-(1 : ℝ) / 6) * w ^ 2 ≤ 3.2 * Yb * w := by
    have := mul_le_mul_of_nonneg_right hY hw.le
    nlinarith
  calc OC.gY (w * y) (w * r) * HW.phi w
      ≤ (0.70711 * (1 / Real.sqrt w) * Nb * w ^ 2 * (1 / Real.sqrt r) + Lb * w * (1 / r) +
          3.2 * (w * y) ^ (-(1 : ℝ) / 6) * w ^ 2) * Real.exp (-w ^ 2 / 2) := h
    _ ≤ 0.70711 * (1 / Real.sqrt w) * Nb * w ^ 2 * (1 / Real.sqrt r) + Lb * w * (1 / r) +
          3.2 * (w * y) ^ (-(1 : ℝ) / 6) * w ^ 2 := by linarith
    _ ≤ 0.70711 * Nb * (1 / Real.sqrt r) * (sp * w) + Lb * w * (1 / r) + 3.2 * Yb * w := by
        rw [e1]
        linarith
    _ = (0.70711 * sp * Nb * (1 / Real.sqrt r) + Lb * (1 / r) + 3.2 * Yb) * w := by ring

/-- **The first piece as an `IntBnd`**: `f ≤ Cw` on `[w₁, p₁]`, `0 ≤ w₁ ≤ p₁`, `C ≥ 0` give
`IntBnd f w₁ p₁ (Cp₁²/2)`. -/
theorem intBnd_lin (f : ℝ → ℝ) (w1 p1 C : ℝ) (hw1 : 0 ≤ w1) (hp : w1 ≤ p1) (hC : 0 ≤ C)
    (hf : ∀ w ∈ Icc w1 p1, f w ≤ C * w) : IntBnd f w1 p1 (C * (p1 ^ 2 / 2)) := by
  refine intBnd_of f (fun w => C * w) w1 p1 _ hp hf (fun w hw => mul_nonneg hC (hw1.trans hw.1))
    ((continuous_const.mul continuous_id).intervalIntegrable _ _) ?_
  rw [intervalIntegral.integral_const_mul, integral_id]
  have : 0 ≤ w1 ^ 2 := sq_nonneg w1
  have := mul_le_mul_of_nonneg_left (by linarith : (p1 ^ 2 - w1 ^ 2) / 2 ≤ p1 ^ 2 / 2) hC
  linarith

/-- **The sliver** `∫_{1/K}^{max(1/K, c)} |φ| ≤ c³/3` (`φ(w) ≤ w²`). -/
theorem sliver_le (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ∫ w in a..max a c, |HW.phi w| ≤ c ^ 3 / 3 := by
  rcases le_total c a with h | h
  · rw [max_eq_left h, intervalIntegral.integral_same]
    positivity
  · rw [max_eq_right h]
    have hmono : ∫ w in a..c, |HW.phi w| ≤ ∫ w in a..c, w ^ 2 := by
      refine intervalIntegral.integral_mono_on h
        ((HW.continuous_phi.abs).intervalIntegrable _ _) ((continuous_pow 2).intervalIntegrable _ _)
        fun w _ => ?_
      rw [abs_of_nonneg (HW.phi_nonneg w)]
      exact MN.phi_le_sq w
    rw [integral_pow] at hmono
    have : 0 ≤ a ^ 3 := pow_nonneg ha 3
    push_cast at hmono
    linarith

/-- **`gT` from its three parts**: the `w ≤ 1` integral, the `w > 1` integral and the sliver, over
`|φ|₁ = √(π/2) ≥ 1.2533139`. -/
theorem gT_le_of (y r Blo Bhi Bs : ℝ) (hy : 1 < y) (hr : 0 < r)
    (hlo : IntBnd (fun w => OC.gY (w * y) (w * r) * HW.phi w) (max (1 / kK y) (1000 / r)) 1 Blo)
    (hhi : IntBndI (fun w => OC.gY (w * y) r * HW.phi w) 1 Bhi) (hs : (1000 / r) ^ 3 / 3 ≤ Bs) :
    OC.gT HW.phi y r ≤ (Blo + Bhi + 1.04488 * Bs) / 1.2533139 := by
  have hK : 0 < kK y := by
    unfold kK
    have := Real.log_pos hy
    positivity
  have h1 := le_of_intBnd _ _ _ _ hlo
  have h2 := le_of_intBndI _ _ _ hhi
  have h3 := sliver_le (1 / kK y) (1000 / r) (by positivity) (by positivity)
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  have hs0 := MajSp.sqrt_pi_half.1
  have hB0 : 0 ≤ Blo + Bhi + 1.04488 * Bs := by
    have := hlo.2.1
    have := hhi.1
    have : 0 ≤ (1000 / r) ^ 3 / 3 := by positivity
    nlinarith
  unfold OC.gT
  rw [hl1]
  have hnum : (∫ w in (max (1 / kK y) (1000 / r))..1, OC.gY (w * y) (w * r) * HW.phi w) +
      (∫ w in Ioi (1 : ℝ), OC.gY (w * y) r * HW.phi w) +
      1.04488 * ∫ w in (1 / kK y)..(max (1 / kK y) (1000 / r)), |HW.phi w| ≤
      Blo + Bhi + 1.04488 * Bs := by
    linarith
  calc _ ≤ (Blo + Bhi + 1.04488 * Bs) / Real.sqrt (Real.pi / 2) :=
        div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (Blo + Bhi + 1.04488 * Bs) / 1.2533139 :=
        div_le_div_of_nonneg_left hB0 (by norm_num) hs0

/-! ## The region envelope and its antiderivative in `r` -/

/-- **The region envelope** `E(r) = P(ℓ)/√r + Q(ℓ)/r + z`, `ℓ = log r`, `P` quartic, `Q`
quadratic. -/
noncomputable def envF (p0 p1 p2 p3 p4 q0 q1 q2 z r : ℝ) : ℝ :=
  (p0 + p1 * Real.log r + p2 * Real.log r ^ 2 + p3 * Real.log r ^ 3 + p4 * Real.log r ^ 4) /
      Real.sqrt r +
    (q0 + q1 * Real.log r + q2 * Real.log r ^ 2) / r + z

/-- **Its antiderivative against `dr/r`**: `−2S(ℓ)/√r − T(ℓ)/r + zℓ` with `S = P + 2P′ + 4P″ +
8P‴ + 16P⁗`, `T = Q + Q′ + Q″` (`envG_deriv`). -/
noncomputable def envG (p0 p1 p2 p3 p4 q0 q1 q2 z r : ℝ) : ℝ :=
  -2 * ((p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) +
      (p1 + 4 * p2 + 24 * p3 + 192 * p4) * Real.log r + (p2 + 6 * p3 + 48 * p4) * Real.log r ^ 2 +
      (p3 + 8 * p4) * Real.log r ^ 3 + p4 * Real.log r ^ 4) / Real.sqrt r -
    ((q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log r + q2 * Real.log r ^ 2) / r +
    z * Real.log r

/-- A quartic times an exponential. -/
theorem hasDerivAt_quart_exp (a0 a1 a2 a3 a4 k l : ℝ) :
    HasDerivAt (fun l => (a0 + a1 * l + a2 * l ^ 2 + a3 * l ^ 3 + a4 * l ^ 4) * Real.exp (k * l))
      ((a1 + 2 * a2 * l + 3 * a3 * l ^ 2 + 4 * a4 * l ^ 3 +
        k * (a0 + a1 * l + a2 * l ^ 2 + a3 * l ^ 3 + a4 * l ^ 4)) * Real.exp (k * l)) l := by
  have h1 : HasDerivAt (fun l => a0 + a1 * l + a2 * l ^ 2 + a3 * l ^ 3 + a4 * l ^ 4)
      (a1 + 2 * a2 * l + 3 * a3 * l ^ 2 + 4 * a4 * l ^ 3) l := by
    have := ((((hasDerivAt_id' (x := l)).const_mul a1).const_add a0).add
      ((hasDerivAt_pow 2 l).const_mul a2)).add ((hasDerivAt_pow 3 l).const_mul a3) |>.add
      ((hasDerivAt_pow 4 l).const_mul a4)
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun l => Real.exp (k * l)) (Real.exp (k * l) * k) l :=
    (((hasDerivAt_id' (x := l)).const_mul k).exp).congr_deriv (by ring)
  exact (h1.mul h2).congr_deriv (by ring)

/-- `envG` as a function of `ℓ = log r`. -/
theorem envG_eq (p0 p1 p2 p3 p4 q0 q1 q2 z r : ℝ) (hr : 0 < r) :
    envG p0 p1 p2 p3 p4 q0 q1 q2 z r =
      -2 * (((p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) +
        (p1 + 4 * p2 + 24 * p3 + 192 * p4) * Real.log r +
        (p2 + 6 * p3 + 48 * p4) * Real.log r ^ 2 + (p3 + 8 * p4) * Real.log r ^ 3 +
        p4 * Real.log r ^ 4) * Real.exp (-(1 / 2) * Real.log r)) -
      ((q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log r + q2 * Real.log r ^ 2 +
        0 * Real.log r ^ 3 + 0 * Real.log r ^ 4) * Real.exp (-1 * Real.log r) +
      z * Real.log r := by
  unfold envG
  rw [div_eq_mul_inv, div_eq_mul_inv, MN.inv_sqrt_eq r hr, MN.inv_eq_exp r hr]
  ring

/-- **`d/dr envG = envF/r`** for `r > 0`. -/
theorem envG_deriv (p0 p1 p2 p3 p4 q0 q1 q2 z r : ℝ) (hr : 0 < r) :
    HasDerivAt (envG p0 p1 p2 p3 p4 q0 q1 q2 z) (envF p0 p1 p2 p3 p4 q0 q1 q2 z r / r) r := by
  have hG := (((hasDerivAt_quart_exp (p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4)
      (p1 + 4 * p2 + 24 * p3 + 192 * p4) (p2 + 6 * p3 + 48 * p4) (p3 + 8 * p4) p4 (-(1 / 2))
      (Real.log r)).const_mul (-2)).sub
    (hasDerivAt_quart_exp (q0 + q1 + 2 * q2) (q1 + 2 * q2) q2 0 0 (-1) (Real.log r))).add
    ((hasDerivAt_id' (x := Real.log r)).const_mul z)
  have hc := hG.comp r (Real.hasDerivAt_log hr.ne')
  have heq : envG p0 p1 p2 p3 p4 q0 q1 q2 z =ᶠ[𝓝 r] (fun l => -2 *
      (((p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) + (p1 + 4 * p2 + 24 * p3 + 192 * p4) * l +
        (p2 + 6 * p3 + 48 * p4) * l ^ 2 + (p3 + 8 * p4) * l ^ 3 + p4 * l ^ 4) *
        Real.exp (-(1 / 2) * l)) -
      ((q0 + q1 + 2 * q2) + (q1 + 2 * q2) * l + q2 * l ^ 2 + 0 * l ^ 3 + 0 * l ^ 4) *
        Real.exp (-1 * l) + z * l) ∘ Real.log := by
    filter_upwards [lt_mem_nhds hr] with u hu
    exact envG_eq p0 p1 p2 p3 p4 q0 q1 q2 z u hu
  have hF : envF p0 p1 p2 p3 p4 q0 q1 q2 z r / r =
      ((p0 + p1 * Real.log r + p2 * Real.log r ^ 2 + p3 * Real.log r ^ 3 + p4 * Real.log r ^ 4) *
        Real.exp (-(1 / 2) * Real.log r) +
        (q0 + q1 * Real.log r + q2 * Real.log r ^ 2) * Real.exp (-1 * Real.log r) + z) * r⁻¹ := by
    unfold envF
    rw [← MN.inv_sqrt_eq r hr, ← MN.inv_eq_exp r hr]
    ring
  refine (hc.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [hF]
  ring


/-- **A region of the `r`-integral**: `f ≤ E` and `E ≥ 0` on `[a, b] ⊂ (0, ∞)` give
`IntBnd (f/r) a b (G(b) − G(a))`, `G = envG` (`integral_le_sub_of_hasDeriv_right_of_le`; the
non-integrable case uses `G(b) ≥ G(a)`, `G` increasing). -/
theorem intBnd_region (f : ℝ → ℝ) (a b p0 p1 p2 p3 p4 q0 q1 q2 z : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hf : ∀ r ∈ Icc a b, f r ≤ envF p0 p1 p2 p3 p4 q0 q1 q2 z r)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ envF p0 p1 p2 p3 p4 q0 q1 q2 z r) :
    IntBnd (fun r => f r / r) a b
      (envG p0 p1 p2 p3 p4 q0 q1 q2 z b - envG p0 p1 p2 p3 p4 q0 q1 q2 z a) := by
  set G := envG p0 p1 p2 p3 p4 q0 q1 q2 z
  have hd : ∀ r ∈ Icc a b, HasDerivAt G (envF p0 p1 p2 p3 p4 q0 q1 q2 z r / r) r :=
    fun r hr => envG_deriv p0 p1 p2 p3 p4 q0 q1 q2 z r (lt_of_lt_of_le ha hr.1)
  have hcont : ContinuousOn G (Icc a b) := fun r hr => (hd r hr).continuousAt.continuousWithinAt
  have hmono : MonotoneOn G (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
    · intro r hr
      rw [interior_Icc] at hr
      exact (hd r (Ioo_subset_Icc_self hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hd r (Ioo_subset_Icc_self hr)).deriv]
      have hr0 : 0 < r := lt_of_lt_of_le ha (le_of_lt hr.1)
      exact div_nonneg (hpos r (Ioo_subset_Icc_self hr)) hr0.le
  have hB : 0 ≤ G b - G a := by
    have := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
    linarith
  refine ⟨hab, hB, fun hfi => ?_⟩
  have hint : IntegrableOn (fun r => f r / r) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hfi
  exact intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hcont
    (fun r hr => (hd r (Ioo_subset_Icc_self hr)).hasDerivWithinAt) hint
    (fun r hr => by
      have hr0 : 0 < r := lt_of_lt_of_le ha (le_of_lt hr.1)
      exact div_le_div_of_nonneg_right (hf r (Ioo_subset_Icc_self hr)) hr0.le)

/-- **`envG` is increasing** where `envF ≥ 0`. -/
theorem envG_mono (a b p0 p1 p2 p3 p4 q0 q1 q2 z : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ envF p0 p1 p2 p3 p4 q0 q1 q2 z r) :
    envG p0 p1 p2 p3 p4 q0 q1 q2 z a ≤ envG p0 p1 p2 p3 p4 q0 q1 q2 z b :=
  by
    have h := (intBnd_region (fun _ => 0) a b p0 p1 p2 p3 p4 q0 q1 q2 z ha hab
      (fun r hr => hpos r hr) hpos).2.1
    linarith


/-! ## The piece majorants, from short-coefficient factor bounds -/

/-- The quartic Taylor majorant of `1/√w` at `s²` (`isq_le`). -/
noncomputable def isqP (s w : ℝ) : ℝ :=
  1 / s * (1 - (w / s ^ 2 - 1) / 2 + 3 / 8 * (w / s ^ 2 - 1) ^ 2 -
    5 / 16 * (w / s ^ 2 - 1) ^ 3 + 35 / 128 * (w / s ^ 2 - 1) ^ 4)

/-- **`F(t)` by the tangent of `log` at `1/ι`** (`ι = invLs`): `log log t ≤ λ_s − 1 + ι log t` with
`λ_s ≥ −log ι`, `e^γ ≤ 1.7810727 ≤ e_g`, `log log t ≥ λ_lo > 0`, `2.50637/λ_lo ≤ K`. -/
theorem bigF_le_tan2 (t Llo lamlo invLs lams lt eg K : ℝ) (hLlo0 : 0 < Llo)
    (hLlo : Llo ≤ Real.log t) (hlamlo : lamlo ≤ Real.log Llo) (hlamlo0 : 0 < lamlo)
    (hK : 2.50637 / lamlo ≤ K) (hinv : 0 < invLs) (hlams : -lams ≤ Real.log invLs)
    (hlt : Real.log t ≤ lt) (heg : 1.7810727 ≤ eg) :
    0 ≤ bigF t ∧ bigF t ≤ eg * (lams - 1 + lt * invLs) + K := by
  have hl0 : 0 < Real.log t := lt_of_lt_of_le hLlo0 hLlo
  have hu : lamlo ≤ Real.log (Real.log t) := hlamlo.trans (Real.log_le_log hLlo0 hLlo)
  have hu0 : 0 < Real.log (Real.log t) := lt_of_lt_of_le hlamlo0 hu
  have htan : Real.log (Real.log t) ≤ lams - 1 + Real.log t * invLs := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hl0 hinv)
    rw [Real.log_mul hl0.ne' hinv.ne'] at h
    linarith
  have hmul : Real.log t * invLs ≤ lt * invLs := mul_le_mul_of_nonneg_right hlt hinv.le
  have hE := expG_le
  have hE0 := Real.exp_pos Real.eulerMascheroniConstant
  have h1 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log t) ≤
      eg * (lams - 1 + lt * invLs) := by
    have := mul_le_mul (hE.trans heg) (by linarith : Real.log (Real.log t) ≤ lams - 1 + lt * invLs)
      hu0.le (by linarith)
    linarith
  have h2 : 2.50637 / Real.log (Real.log t) ≤ 2.50637 / lamlo :=
    div_le_div_of_nonneg_left (by norm_num) hlamlo0 hu
  unfold bigF
  constructor
  · have := mul_pos hE0 hu0
    have : 0 ≤ 2.50637 / Real.log (Real.log t) := div_nonneg (by norm_num) hu0.le
    linarith
  · linarith

/-- **`√F ≤ αF + β`** whenever `4αβ ≥ 1` (`α > 0`). -/
theorem sqrt_le_lin (F α β : ℝ) (hα : 0 < α) (h : 1 ≤ 4 * α * β) (hF : 0 ≤ F) :
    Real.sqrt F ≤ α * F + β := by
  have hs := Real.sq_sqrt hF
  have key : 0 ≤ 4 * α * (α * F + β - Real.sqrt F) := by
    have e : 4 * α * (α * F + β - Real.sqrt F) =
        (2 * α * Real.sqrt F - 1) ^ 2 + (4 * α * β - 1) := by
      linear_combination (-(4 * α ^ 2)) * hs
    rw [e]
    have := sq_nonneg (2 * α * Real.sqrt F - 1)
    linarith
  have := (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < 4 * α)).mp key
  linarith

/-- `L_t ≥ 0` when `log t ≥ 0` and `F(t) ≥ 0`. -/
theorem lL_nonneg (t : ℝ) (ht : 0 < t) (hl0 : 0 ≤ Real.log t) (hF0 : 0 ≤ bigF t) : 0 ≤ lL t := by
  have h2 := Real.log_two_gt_d9
  have e1 : Real.log (2 ^ ((7 : ℝ) / 4) * t ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log 2 + 13 / 4 * Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow ht]
  have e2 : Real.log (2 ^ ((16 : ℝ) / 9) * t ^ ((80 : ℝ) / 9)) =
      16 / 9 * Real.log 2 + 80 / 9 * Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow ht]
  unfold lL
  rw [e1, e2]
  have : 0 ≤ bigF t * (7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9) :=
    mul_nonneg hF0 (by linarith)
  linarith

/-- **The three factor bounds at `t`**: `F ≥ 0`, `√F ≤ α F̄ + β`, `L_t ≤ F̄(7/4c₂ + 13/4ℓ_t + 80/9)
+ 16/9c₂ + 80/9ℓ_t + 111/5`, `L_t ≥ 0`, with `F̄ = e_g(λ_s − 1 + ℓ_t ι) + K`. -/
theorem factorsS (t Llo lamlo invLs lams lt eg K α β c2 : ℝ) (ht : 0 < t) (hLlo0 : 0 < Llo)
    (hLlo : Llo ≤ Real.log t) (hlamlo : lamlo ≤ Real.log Llo) (hlamlo0 : 0 < lamlo)
    (hK : 2.50637 / lamlo ≤ K) (hinv : 0 < invLs) (hlams : -lams ≤ Real.log invLs)
    (hlt : Real.log t ≤ lt) (heg : 1.7810727 ≤ eg) (hα : 0 < α) (hαβ : 1 ≤ 4 * α * β)
    (hc2 : Real.log 2 ≤ c2) :
    0 ≤ bigF t ∧ Real.sqrt (bigF t) ≤ α * (eg * (lams - 1 + lt * invLs) + K) + β ∧
      lL t ≤ (eg * (lams - 1 + lt * invLs) + K) * (7 / 4 * c2 + 13 / 4 * lt + 80 / 9) +
        16 / 9 * c2 + 80 / 9 * lt + 111 / 5 ∧ 0 ≤ lL t := by
  obtain ⟨hF0, hF⟩ := bigF_le_tan2 t Llo lamlo invLs lams lt eg K hLlo0 hLlo hlamlo hlamlo0 hK
    hinv hlams hlt heg
  have hl0 : 0 ≤ Real.log t := le_trans hLlo0.le hLlo
  have hαF := mul_le_mul_of_nonneg_left hF hα.le
  refine ⟨hF0, (sqrt_le_lin _ α β hα hαβ hF0).trans (by linarith), ?_, lL_nonneg t ht hl0 hF0⟩
  exact lL_le_of t lt _ c2 ht hl0 hlt hF0 hF hc2

/-- **The lo-piece majorant, with its nonnegativity**: `ptLo` plus `0 ≤` of the majorant, from
the nonnegativity of each factor. -/
theorem ptLoS (y r w Iq Rb Lam Sb Lb Yb : ℝ) (hr : 0 < r) (hw : 0 < w)
    (hq : 1 / Real.sqrt w ≤ Iq) (hR0 : 0 ≤ rR (w * y) (2 * (w * r)))
    (hR : rR (w * y) (2 * (w * r)) ≤ Rb) (hL0 : 0 ≤ Real.log (2 * (w * r)))
    (hL : Real.log (2 * (w * r)) ≤ Lam) (hS : Real.sqrt (bigF (w * r)) ≤ Sb)
    (hLL0 : 0 ≤ lL (w * r)) (hLL : lL (w * r) ≤ Lb) (hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6))
    (hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ Yb) :
    OC.gY (w * y) (w * r) * HW.phi w ≤
        (0.70711 * Iq * ((Rb * Lam + 0.5) * Sb + 2.5) * w ^ 2 * (1 / Real.sqrt r) +
          Lb * w * (1 / r) + 3.2 * Yb * w ^ 2) * Real.exp (-w ^ 2 / 2) ∧
      0 ≤ (0.70711 * Iq * ((Rb * Lam + 0.5) * Sb + 2.5) * w ^ 2 * (1 / Real.sqrt r) +
          Lb * w * (1 / r) + 3.2 * Yb * w ^ 2) * Real.exp (-w ^ 2 / 2) := by
  refine ⟨ptLo y r w Iq Rb Lam Sb Lb Yb hr hw hq hR0 hR hL0 hL hS hLL hY, ?_⟩
  have hIq : 0 ≤ Iq := le_trans (by positivity) hq
  have hRb : 0 ≤ Rb := hR0.trans hR
  have hLam : 0 ≤ Lam := hL0.trans hL
  have hSb : 0 ≤ Sb := (Real.sqrt_nonneg _).trans hS
  have hLb : 0 ≤ Lb := hLL0.trans hLL
  have hYb : 0 ≤ Yb := hY0.trans hY
  have hN : 0 ≤ (Rb * Lam + 0.5) * Sb + 2.5 := by
    have := mul_nonneg hRb hLam
    positivity
  have hsr := Real.sqrt_nonneg r
  have : 0 ≤ 1 / r := by positivity
  positivity

/-- **The hi-piece majorant (`w ≥ 1`), with its nonnegativity.** -/
theorem ptHiS (y r w Rb Lam Sb Lb Yb : ℝ) (hr : 0 < r) (hw : 0 < w)
    (hR0 : 0 ≤ rR (w * y) (2 * r)) (hR : rR (w * y) (2 * r) ≤ Rb) (hL0 : 0 ≤ Real.log (2 * r))
    (hL : Real.log (2 * r) ≤ Lam) (hS : Real.sqrt (bigF r) ≤ Sb) (hLL0 : 0 ≤ lL r)
    (hLL : lL r ≤ Lb) (hY0 : 0 ≤ (w * y) ^ (-(1 : ℝ) / 6)) (hY : (w * y) ^ (-(1 : ℝ) / 6) ≤ Yb) :
    OC.gY (w * y) r * HW.phi w ≤
        (0.70711 * ((Rb * Lam + 0.5) * Sb + 2.5) * w ^ 2 * (1 / Real.sqrt r) +
          Lb * w ^ 2 * (1 / r) + 3.2 * Yb * w ^ 2) * Real.exp (-w ^ 2 / 2) ∧
      0 ≤ (0.70711 * ((Rb * Lam + 0.5) * Sb + 2.5) * w ^ 2 * (1 / Real.sqrt r) +
          Lb * w ^ 2 * (1 / r) + 3.2 * Yb * w ^ 2) * Real.exp (-w ^ 2 / 2) := by
  refine ⟨ptHi y r w Rb Lam Sb Lb Yb hr hw hR0 hR hL0 hL hS hLL hY, ?_⟩
  have hRb : 0 ≤ Rb := hR0.trans hR
  have hLam : 0 ≤ Lam := hL0.trans hL
  have hSb : 0 ≤ Sb := (Real.sqrt_nonneg _).trans hS
  have hLb : 0 ≤ Lb := hLL0.trans hLL
  have hYb : 0 ≤ Yb := hY0.trans hY
  have hN : 0 ≤ (Rb * Lam + 0.5) * Sb + 2.5 := by
    have := mul_nonneg hRb hLam
    positivity
  have hsr := Real.sqrt_nonneg r
  have : 0 ≤ 1 / r := by positivity
  positivity

/-- **The Gaussian tail `w > q`**: a hi-piece majorant `C·w²e^{−w²/2}` with `C ≥ 0` independent
of `w`, and `w² ≤ w³/q`. -/
theorem tail_of (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C)
    (hf : ∀ w ∈ Ioi q, f w ≤ C * (w ^ 2 * Real.exp (-w ^ 2 / 2))) :
    ∀ w ∈ Ioi q, f w ≤ C / q * (w ^ 3 * Real.exp (-w ^ 2 / 2)) := by
  intro w hw
  have hw' : q < w := hw
  have hE := Real.exp_pos (-w ^ 2 / 2)
  have hw2 : w ^ 2 ≤ w ^ 3 / q := by
    rw [le_div_iff₀ hq]
    have : w ^ 3 = w ^ 2 * w := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hw'.le (sq_nonneg w)
  calc f w ≤ C * (w ^ 2 * Real.exp (-w ^ 2 / 2)) := hf w hw
    _ ≤ C * (w ^ 3 / q * Real.exp (-w ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw2 hE.le) hC
    _ = C / q * (w ^ 3 * Real.exp (-w ^ 2 / 2)) := by ring

/-- **The first-piece majorant, with its nonnegativity**: `ptFirst` plus `C ≥ 0`. -/
theorem ptFirstS (y r w sp Rb Lam Sb Lb Yb : ℝ) (hy : 0 < y) (hr : 0 < r) (hw : 0 < w)
    (hsp : Real.sqrt w ≤ sp) (hR0 : 0 ≤ rR (w * y) (2 * (w * r)))
    (hR : rR (w * y) (2 * (w * r)) ≤ Rb) (hL0 : 0 ≤ Real.log (2 * (w * r)))
    (hL : Real.log (2 * (w * r)) ≤ Lam) (hS : Real.sqrt (bigF (w * r)) ≤ Sb)
    (hLL0 : 0 ≤ lL (w * r)) (hLL : lL (w * r) ≤ Lb) (hY : (w * y) ^ (-(1 : ℝ) / 6) * w ≤ Yb) :
    OC.gY (w * y) (w * r) * HW.phi w ≤
        (0.70711 * sp * ((Rb * Lam + 0.5) * Sb + 2.5) * (1 / Real.sqrt r) + Lb * (1 / r) +
          3.2 * Yb) * w ∧
      0 ≤ 0.70711 * sp * ((Rb * Lam + 0.5) * Sb + 2.5) * (1 / Real.sqrt r) + Lb * (1 / r) +
          3.2 * Yb := by
  refine ⟨ptFirst y r w sp Rb Lam Sb Lb Yb hy hr hw hsp hR0 hR hL0 hL hS hLL0 hLL hY, ?_⟩
  have hsp0 : 0 ≤ sp := (Real.sqrt_nonneg w).trans hsp
  have hRb : 0 ≤ Rb := hR0.trans hR
  have hLam : 0 ≤ Lam := hL0.trans hL
  have hSb : 0 ≤ Sb := (Real.sqrt_nonneg _).trans hS
  have hLb : 0 ≤ Lb := hLL0.trans hLL
  have hYb : 0 ≤ Yb := le_trans (mul_nonneg (Real.rpow_nonneg (mul_pos hw hy).le _) hw.le) hY
  have hN : 0 ≤ (Rb * Lam + 0.5) * Sb + 2.5 := by
    have := mul_nonneg hRb hLam
    positivity
  have hsr := Real.sqrt_nonneg r
  have : 0 ≤ 1 / r := by positivity
  positivity

/-- **The δ-trick**: `A ≤ B` from `B − A = D` and `D ≥ 0`. -/
theorem le_of_sub_eq (A B D : ℝ) (h : B - A = D) (hD : 0 ≤ D) : A ≤ B := by linarith

/-- `(wy)^{−1/6}w ≤ Y₀^{−1/6}` for `0 < w ≤ 1`, `y ≥ Y₀ > 0`. -/
theorem wy_rpow_w_le (w y Y0 : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) (hY0 : 0 < Y0) (hy : Y0 ≤ y) :
    (w * y) ^ (-(1 : ℝ) / 6) * w ≤ Y0 ^ (-(1 : ℝ) / 6) := by
  have hy0 : 0 < y := hY0.trans_le hy
  rw [Real.mul_rpow hw.le hy0.le]
  have h1 : w ^ (-(1 : ℝ) / 6) * w = w ^ ((5 : ℝ) / 6) := by
    have h := Real.rpow_add hw (-(1 : ℝ) / 6) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  have h2 : w ^ ((5 : ℝ) / 6) ≤ 1 := Real.rpow_le_one hw.le hw1 (by norm_num)
  have h3 : y ^ (-(1 : ℝ) / 6) ≤ Y0 ^ (-(1 : ℝ) / 6) :=
    Real.rpow_le_rpow_of_nonpos hY0 hy (by norm_num)
  have h4 : 0 ≤ y ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hy0.le _
  calc w ^ (-(1 : ℝ) / 6) * y ^ (-(1 : ℝ) / 6) * w =
        w ^ (-(1 : ℝ) / 6) * w * y ^ (-(1 : ℝ) / 6) := by ring
    _ = w ^ ((5 : ℝ) / 6) * y ^ (-(1 : ℝ) / 6) := by rw [h1]
    _ ≤ 1 * y ^ (-(1 : ℝ) / 6) := mul_le_mul_of_nonneg_right h2 h4
    _ ≤ Y0 ^ (-(1 : ℝ) / 6) := by linarith

/-! ## Integrating a piece majorant against the Gaussian moments -/

/-- `∫_a^b (∑ cᵢwⁱ) e^{−w²/2}`. -/
noncomputable def mI (a b : ℝ) (cs : List ℝ) : ℝ :=
  ∫ w in a..b, pevR cs w * Real.exp (-w ^ 2 / 2)

/-- `mI = ∑ cᵢ J_i(a,b)`. -/
theorem mI_eq (a b : ℝ) (cs : List ℝ) :
    mI a b cs = ∑ i ∈ range cs.length, cs.getD i 0 * mJ a b i := by
  unfold mI pevR mJ
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext w
    ring
  · intro i _
    exact ((continuous_const.mul (continuous_pow i)).mul
      (by fun_prop : Continuous fun w : ℝ => Real.exp (-w ^ 2 / 2))).intervalIntegrable _ _

/-- **The shape of a piece majorant**: `(X·∑_{i≤4} ℓⁱPᵢ(w) + Z·∑_{i≤2} ℓⁱQᵢ(w) + Y(w))e^{−w²/2}`,
`X = 1/√r`, `Z = 1/r`, `ℓ = log r`. -/
noncomputable def shapeG (X Z l : ℝ) (P0 P1 P2 P3 P4 Q0 Q1 Q2 Yr : List ℝ) (w : ℝ) : ℝ :=
  (X * (pevR P0 w + l * pevR P1 w + l ^ 2 * pevR P2 w + l ^ 3 * pevR P3 w + l ^ 4 * pevR P4 w) +
    Z * (pevR Q0 w + l * pevR Q1 w + l ^ 2 * pevR Q2 w) + pevR Yr w) * Real.exp (-w ^ 2 / 2)

/-- `shapeG` is continuous. -/
theorem continuous_shapeG (X Z l : ℝ) (P0 P1 P2 P3 P4 Q0 Q1 Q2 Yr : List ℝ) :
    Continuous (shapeG X Z l P0 P1 P2 P3 P4 Q0 Q1 Q2 Yr) := by
  unfold shapeG
  fun_prop

/-- `∫ shapeG` by linearity. -/
theorem int_shapeG (a b X Z l : ℝ) (P0 P1 P2 P3 P4 Q0 Q1 Q2 Yr : List ℝ) :
    ∫ w in a..b, shapeG X Z l P0 P1 P2 P3 P4 Q0 Q1 Q2 Yr w =
      X * (mI a b P0 + l * mI a b P1 + l ^ 2 * mI a b P2 + l ^ 3 * mI a b P3 +
        l ^ 4 * mI a b P4) + Z * (mI a b Q0 + l * mI a b Q1 + l ^ 2 * mI a b Q2) + mI a b Yr := by
  have e : (fun w => shapeG X Z l P0 P1 P2 P3 P4 Q0 Q1 Q2 Yr w) = fun w =>
      X * (pevR P0 w * Real.exp (-w ^ 2 / 2)) + (X * l) * (pevR P1 w * Real.exp (-w ^ 2 / 2)) +
      (X * l ^ 2) * (pevR P2 w * Real.exp (-w ^ 2 / 2)) +
      (X * l ^ 3) * (pevR P3 w * Real.exp (-w ^ 2 / 2)) +
      (X * l ^ 4) * (pevR P4 w * Real.exp (-w ^ 2 / 2)) +
      Z * (pevR Q0 w * Real.exp (-w ^ 2 / 2)) + (Z * l) * (pevR Q1 w * Real.exp (-w ^ 2 / 2)) +
      (Z * l ^ 2) * (pevR Q2 w * Real.exp (-w ^ 2 / 2)) + pevR Yr w * Real.exp (-w ^ 2 / 2) := by
    funext w
    unfold shapeG
    ring
  rw [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul]
    unfold mI
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- **Rows to envelope**: `Iᵢ ≤ Uᵢ`, `Jᵢ ≤ Vᵢ`, `K ≤ W`, `X, Z, ℓ ≥ 0`. -/
theorem rows_le (X Z l I0 I1 I2 I3 I4 U0 U1 U2 U3 U4 J0 J1 J2 V0 V1 V2 K W : ℝ) (hX : 0 ≤ X)
    (hZ : 0 ≤ Z) (hl : 0 ≤ l) (h0 : I0 ≤ U0) (h1 : I1 ≤ U1) (h2 : I2 ≤ U2) (h3 : I3 ≤ U3)
    (h4 : I4 ≤ U4) (g0 : J0 ≤ V0) (g1 : J1 ≤ V1) (g2 : J2 ≤ V2) (hK : K ≤ W) :
    X * (I0 + l * I1 + l ^ 2 * I2 + l ^ 3 * I3 + l ^ 4 * I4) + Z * (J0 + l * J1 + l ^ 2 * J2) +
        K ≤
      X * (U0 + l * U1 + l ^ 2 * U2 + l ^ 3 * U3 + l ^ 4 * U4) + Z * (V0 + l * V1 + l ^ 2 * V2) +
        W := by
  gcongr


/-! ## The remaining generic facts: `K_D`, the far `R`, the far `Y`, log ranges -/

/-- **`K_D`**: `log 9 − log 2.004 − log 2 + (log y)/3 ≥ 0.8089301384 + L_Y/3` for `y ≥ Y₀`,
`log Y₀ ≥ L_Y` (`log 9 ≥ 2.1972245`, `log 2.004 ≤ log 2 + 0.002`). -/
theorem kD_ge (y Y0 LY : ℝ) (hY0 : 0 < Y0) (hy : Y0 ≤ y) (hLY : LY ≤ Real.log Y0) :
    0.8089301384 + LY / 3 ≤ Real.log 9 - Real.log 2.004 - Real.log 2 + Real.log y / 3 := by
  have h9 := MN.log9_ge
  have h2 := Real.log_two_lt_d9
  have h2004 : Real.log 2.004 ≤ Real.log 2 + 0.002 := by
    rw [show (2.004 : ℝ) = 2 * 1.002 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.002)
    linarith
  have hly : Real.log Y0 ≤ Real.log y := Real.log_le_log hY0 hy
  linarith

/-- `L_a ≤ log r ≤ L_b` on `[r_a, r_b]`. -/
theorem lr_of (r ra rb La Lb : ℝ) (hra : 0 < ra) (h1 : ra ≤ r) (h2 : r ≤ rb)
    (hLa : La ≤ Real.log ra) (hLb : Real.log rb ≤ Lb) : La ≤ Real.log r ∧ Real.log r ≤ Lb :=
  ⟨hLa.trans (Real.log_le_log hra h1), (Real.log_le_log (hra.trans_le h1) h2).trans hLb⟩

/-- **`R_{wy,2wr} ≤ 0.72` on the far region** (`w ≤ 1`, `r ≤ r₁(y)`): `8wr ≤ 3y^{4/15}`,
`log(9(wy)^{1/3}/(4.008wr)) ≥ log 9 − log 1.503 + (log y)/15 − (2/3)log w`, the ratio inside `R` is
`≤ 2.08`, `0.27125 log 3.08 + 0.41415 ≤ 0.72` (`MN.rR_le`). -/
theorem rFarLo (y r w : ℝ) (hy1 : 1 ≤ y) (hr : 0 < r) (hw : 0 < w) (hw1 : w ≤ 1)
    (hwr : 1 ≤ 8 * (w * r)) (hr1 : r ≤ r1y y) :
    0 ≤ rR (w * y) (2 * (w * r)) ∧ rR (w * y) (2 * (w * r)) ≤ 0.72 := by
  have hy : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hry : 0 < y ^ ((4 : ℝ) / 15) := by positivity
  have hlw : Real.log w ≤ 0 := Real.log_nonpos hw.le hw1
  have hl3 := MN.log3_le
  have hl9 := MN.log9_ge
  have hl15 := MN.log1503_le
  unfold r1y at hr1
  have hA : Real.log (4 * (2 * (w * r))) ≤ Real.log 3 + 4 / 15 * Real.log y := by
    have h1 : 4 * (2 * (w * r)) ≤ 3 * y ^ ((4 : ℝ) / 15) := by nlinarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by norm_num) hry.ne', Real.log_rpow hy] at this
  have hE : Real.log (2.004 * (2 * (w * r))) ≤
      Real.log 1.503 + 4 / 15 * Real.log y + Real.log w := by
    have h1 : 2.004 * (2 * (w * r)) ≤ 1.503 * y ^ ((4 : ℝ) / 15) * w := by nlinarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) hw.ne', Real.log_mul (by norm_num) hry.ne',
      Real.log_rpow hy] at this
  set A1 := Real.log 3 + 4 / 15 * Real.log y with hA1
  set D1 := Real.log 9 - Real.log 1.503 + Real.log y / 15 with hD1d
  have hl30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hD1 : 0 < D1 := by rw [hD1d]; linarith
  have hD : D1 ≤ Real.log (9 * (w * y) ^ ((1 : ℝ) / 3) / (2.004 * (2 * (w * r)))) := by
    rw [MN.logD_eq _ _ (mul_pos hw hy) (by positivity), Real.log_mul hw.ne' hy.ne', hD1d]
    linarith
  have hq : A1 / (2 * D1) ≤ 2.08 := by
    rw [div_le_iff₀ (by linarith), hA1, hD1d]
    linarith
  have hq0 : 0 ≤ A1 / (2 * D1) := div_nonneg (by rw [hA1]; linarith) (by linarith)
  have hU : Real.log (1 + A1 / (2 * D1)) ≤ 1.12494 :=
    (Real.log_le_log (by linarith) (by linarith : 1 + A1 / (2 * D1) ≤ 3.08)).trans MN.log308_le
  have h := MN.rR_le (w * y) (2 * (w * r)) A1 D1 1.12494 (by linarith) hA hD1 hD hU
  exact ⟨le_trans (by norm_num) (MN.rR_ge _ _ (by linarith) (by linarith)), by linarith⟩

/-- **`R_{wy,2r} ≤ 0.72` on the far region** (`w ≥ 1`, `r₀ ≤ r ≤ r₁(y)`): `MN.rR_tail` with
`log(wy) ≥ log y`. -/
theorem rFarHi (y r w : ℝ) (hy1 : 1 ≤ y) (hr0 : 150000 ≤ r) (hw1 : 1 ≤ w) (hr1 : r ≤ r1y y) :
    0 ≤ rR (w * y) (2 * r) ∧ rR (w * y) (2 * r) ≤ 0.72 := by
  have hy : 0 < y := by linarith
  have hw : 0 < w := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hLz : Real.log y ≤ Real.log (w * y) := by
    rw [Real.log_mul hw.ne' hy.ne']
    linarith [Real.log_nonneg hw1]
  have hl3 := MN.log3_le
  have hl9 := MN.log9_ge
  have hl15 := MN.log1503_le
  have h := MN.rR_tail (w * y) y r (Real.log y) hy1 (mul_pos hw hy) hr0 hr1 hLz (by linarith)
    (by linarith)
  have hry : 0 < y ^ ((4 : ℝ) / 15) := by positivity
  have hr1' := hr1
  unfold r1y at hr1'
  have hE : Real.log (2.004 * (2 * r)) ≤ Real.log 1.503 + 4 / 15 * Real.log y := by
    have h1 : 2.004 * (2 * r) ≤ 1.503 * y ^ ((4 : ℝ) / 15) := by linarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by norm_num) hry.ne', Real.log_rpow hy] at this
  have hD : 0 < Real.log (9 * (w * y) ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))) := by
    rw [MN.logD_eq _ _ (mul_pos hw hy) (by positivity)]
    linarith
  exact ⟨le_trans (by norm_num) (MN.rR_ge _ _ (by linarith) hD), h⟩

/-- **The far `Y`**: with `Y₀ = y`, `Ȳ = c_Y y^{−1/6}` satisfies `1 ≤ Ȳ⁶(ay)` once `1 ≤ c_Y⁶a`. -/
theorem yb_far (y a cY : ℝ) (hy : 0 < y) (h : 1 ≤ cY ^ 6 * a) :
    1 ≤ (cY * y ^ (-(1 : ℝ) / 6)) ^ 6 * (a * y) := by
  have e : (y ^ (-(1 : ℝ) / 6)) ^ 6 = y⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
    exact Real.rpow_neg_one y
  rw [mul_pow, e]
  have : cY ^ 6 * y⁻¹ * (a * y) = cY ^ 6 * a := by field_simp
  rw [this]
  exact h

/-! ## Assembly and evaluation helpers -/

/-- Rewrite the majorant of a `P ≤ G ∧ 0 ≤ G` pair along `G = G'`. -/
theorem and_eq_of (P G G' : ℝ) (h : P ≤ G ∧ 0 ≤ G) (e : G = G') : P ≤ G' ∧ 0 ≤ G' :=
  ⟨h.1.trans_eq e, h.2.trans_eq e⟩

/-- `c·lⁱ ≤ c·L₁ⁱ` for `c ≥ 0`, `0 ≤ l ≤ L₁`. -/
theorem tm_le_pos (c L1 l : ℝ) (i : ℕ) (hc : 0 ≤ c) (hl : 0 ≤ l) (h : l ≤ L1) :
    c * l ^ i ≤ c * L1 ^ i :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl h i) hc

/-- `c·lⁱ ≤ c·L₀ⁱ` for `c ≤ 0`, `0 ≤ L₀ ≤ l`. -/
theorem tm_le_neg (c L0 l : ℝ) (i : ℕ) (hc : c ≤ 0) (h0 : 0 ≤ L0) (h : L0 ≤ l) :
    c * l ^ i ≤ c * L0 ^ i :=
  mul_le_mul_of_nonpos_left (pow_le_pow_left₀ h0 h i) hc

/-- `c·L₀ⁱ ≤ c·lⁱ` for `c ≥ 0`, `0 ≤ L₀ ≤ l`. -/
theorem tm_ge_pos (c L0 l : ℝ) (i : ℕ) (hc : 0 ≤ c) (h0 : 0 ≤ L0) (h : L0 ≤ l) :
    c * L0 ^ i ≤ c * l ^ i :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h i) hc

/-- `c·L₁ⁱ ≤ c·lⁱ` for `c ≤ 0`, `0 ≤ l ≤ L₁`. -/
theorem tm_ge_neg (c L1 l : ℝ) (i : ℕ) (hc : c ≤ 0) (hl : 0 ≤ l) (h : l ≤ L1) :
    c * L1 ^ i ≤ c * l ^ i :=
  mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hl h i) hc

/-- `envF` in product form (what `linarith` expands). -/
theorem envF_eq (p0 p1 p2 p3 p4 q0 q1 q2 z r : ℝ) :
    envF p0 p1 p2 p3 p4 q0 q1 q2 z r =
      1 / Real.sqrt r * (p0 + Real.log r * p1 + Real.log r ^ 2 * p2 + Real.log r ^ 3 * p3 +
        Real.log r ^ 4 * p4) + 1 / r * (q0 + Real.log r * q1 + Real.log r ^ 2 * q2) + z := by
  unfold envF
  ring

/-- **`envF` on a box**: `P(ℓ) ≤ P̄`, `Q(ℓ) ≤ Q̄` (both `≥ 0`) and `s² ≤ r` give
`envF ≤ P̄/s + Q̄/s² + z`. -/
theorem envF_le_box (p0 p1 p2 p3 p4 q0 q1 q2 z r s Pb Qb : ℝ) (hs : 0 < s) (hsr : s ^ 2 ≤ r)
    (hP : p0 + p1 * Real.log r + p2 * Real.log r ^ 2 + p3 * Real.log r ^ 3 +
      p4 * Real.log r ^ 4 ≤ Pb)
    (hQ : q0 + q1 * Real.log r + q2 * Real.log r ^ 2 ≤ Qb) (hPb : 0 ≤ Pb) (hQb : 0 ≤ Qb) :
    envF p0 p1 p2 p3 p4 q0 q1 q2 z r ≤ Pb / s + Qb / s ^ 2 + z := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hsr
  have hsq : s ≤ Real.sqrt r := MN.sqrt_ge_of r s hs.le hsr
  have hsr0 : 0 < Real.sqrt r := lt_of_lt_of_le hs hsq
  unfold envF
  have h1 := (div_le_div_of_nonneg_right hP hsr0.le).trans
    (div_le_div_of_nonneg_left hPb hs hsq)
  have h2 := (div_le_div_of_nonneg_right hQ hr.le).trans
    (div_le_div_of_nonneg_left hQb (by positivity) hsr)
  linarith

/-- **`envF ≥ 0`** from `P(ℓ), Q(ℓ), z ≥ 0`. -/
theorem envF_nonneg (p0 p1 p2 p3 p4 q0 q1 q2 z r : ℝ) (hr : 0 < r)
    (hP : 0 ≤ p0 + p1 * Real.log r + p2 * Real.log r ^ 2 + p3 * Real.log r ^ 3 +
      p4 * Real.log r ^ 4)
    (hQ : 0 ≤ q0 + q1 * Real.log r + q2 * Real.log r ^ 2) (hz : 0 ≤ z) :
    0 ≤ envF p0 p1 p2 p3 p4 q0 q1 q2 z r := by
  unfold envF
  have := div_nonneg hP (Real.sqrt_nonneg r)
  have := div_nonneg hQ hr.le
  linarith

/-- **`envG` from above**: `S(ℓ) ≥ S̲ ≥ 0`, `T(ℓ) ≥ T̲ ≥ 0`, `√r ≤ s̄`, `ℓ ≤ L₁`, `z ≥ 0`. -/
theorem envG_ub (p0 p1 p2 p3 p4 q0 q1 q2 z r sh Sl Tl L1 : ℝ) (hr : 0 < r)
    (hsh : Real.sqrt r ≤ sh)
    (hS : Sl ≤ (p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) +
      (p1 + 4 * p2 + 24 * p3 + 192 * p4) * Real.log r + (p2 + 6 * p3 + 48 * p4) * Real.log r ^ 2 +
      (p3 + 8 * p4) * Real.log r ^ 3 + p4 * Real.log r ^ 4) (hSl : 0 ≤ Sl)
    (hT : Tl ≤ (q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log r + q2 * Real.log r ^ 2)
    (hz : 0 ≤ z) (hl : Real.log r ≤ L1) :
    envG p0 p1 p2 p3 p4 q0 q1 q2 z r ≤ -2 * (Sl / sh) - Tl / r + z * L1 := by
  have hsr0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  unfold envG
  set S := (p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) +
      (p1 + 4 * p2 + 24 * p3 + 192 * p4) * Real.log r + (p2 + 6 * p3 + 48 * p4) * Real.log r ^ 2 +
      (p3 + 8 * p4) * Real.log r ^ 3 + p4 * Real.log r ^ 4 with hSd
  set T := (q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log r + q2 * Real.log r ^ 2 with hTd
  have h1 : Sl / sh ≤ S / Real.sqrt r :=
    (div_le_div_of_nonneg_left hSl hsr0 hsh).trans (div_le_div_of_nonneg_right hS hsr0.le)
  have h2 : Tl / r ≤ T / r := div_le_div_of_nonneg_right hT hr.le
  have h3 : z * Real.log r ≤ z * L1 := mul_le_mul_of_nonneg_left hl hz
  have e : -2 * S / Real.sqrt r = -2 * (S / Real.sqrt r) := by ring
  rw [e]
  linarith

/-- **`envG` from below**: `S(ℓ) ≤ S̄` (`S̄ ≥ 0`), `T(ℓ) ≤ T̄`, `s̲ ≤ √r`, `L₀ ≤ ℓ`, `z ≥ 0`. -/
theorem envG_lb (p0 p1 p2 p3 p4 q0 q1 q2 z r sl Sh Th L0 : ℝ) (hr : 0 < r) (hsl0 : 0 < sl)
    (hsl : sl ≤ Real.sqrt r)
    (hS : (p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) +
      (p1 + 4 * p2 + 24 * p3 + 192 * p4) * Real.log r + (p2 + 6 * p3 + 48 * p4) * Real.log r ^ 2 +
      (p3 + 8 * p4) * Real.log r ^ 3 + p4 * Real.log r ^ 4 ≤ Sh) (hSh : 0 ≤ Sh)
    (hT : (q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log r + q2 * Real.log r ^ 2 ≤ Th)
    (hz : 0 ≤ z) (hl : L0 ≤ Real.log r) :
    -2 * (Sh / sl) - Th / r + z * L0 ≤ envG p0 p1 p2 p3 p4 q0 q1 q2 z r := by
  have hsr0 : 0 < Real.sqrt r := lt_of_lt_of_le hsl0 hsl
  unfold envG
  set S := (p0 + 2 * p1 + 8 * p2 + 48 * p3 + 384 * p4) +
      (p1 + 4 * p2 + 24 * p3 + 192 * p4) * Real.log r + (p2 + 6 * p3 + 48 * p4) * Real.log r ^ 2 +
      (p3 + 8 * p4) * Real.log r ^ 3 + p4 * Real.log r ^ 4 with hSd
  set T := (q0 + q1 + 2 * q2) + (q1 + 2 * q2) * Real.log r + q2 * Real.log r ^ 2 with hTd
  have h1 : S / Real.sqrt r ≤ Sh / sl :=
    (div_le_div_of_nonneg_right hS hsr0.le).trans (div_le_div_of_nonneg_left hSh hsl0 hsl)
  have h2 : T / r ≤ Th / r := div_le_div_of_nonneg_right hT hr.le
  have h3 : z * L0 ≤ z * Real.log r := mul_le_mul_of_nonneg_left hl hz
  have e : -2 * S / Real.sqrt r = -2 * (S / Real.sqrt r) := by ring
  rw [e]
  linarith

/-- **The sliver on a region `r ≥ r_a`**: `(1000/r)³/3 ≤ c/r` for `c ≥ 10⁹/(3r_a²)`. -/
theorem sliver_bnd (r ra c : ℝ) (hra : 0 < ra) (hr : ra ≤ r) (hc : 10 ^ 9 / (3 * ra ^ 2) ≤ c) :
    (1000 / r) ^ 3 / 3 ≤ c * (1 / r) := by
  have hr0 : 0 < r := lt_of_lt_of_le hra hr
  have e : (1000 / r) ^ 3 / 3 = 10 ^ 9 / (3 * r ^ 2) * (1 / r) := by
    field_simp
    ring
  have h : 10 ^ 9 / (3 * r ^ 2) ≤ 10 ^ 9 / (3 * ra ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith)
  rw [e]
  exact mul_le_mul_of_nonneg_right (h.trans hc) (by positivity)

/-- **The first-piece window**: for `y ≥ 10²⁵`, `r ≥ 25000`, `w₁ = max(1/K, 1000/r) ∈ [0, 0.04]`. -/
theorem w1_facts (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 25000 ≤ r) :
    1 < y ∧ 0 ≤ max (1 / kK y) (1000 / r) ∧ max (1 / kK y) (1000 / r) ≤ 0.04 := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hly : 57.564626 ≤ Real.log y := MN.lya_ge_1.trans (Real.log_le_log (by norm_num) hy)
  have hK : 25 ≤ kK y := by
    unfold kK
    linarith
  refine ⟨lt_of_lt_of_le (by norm_num) hy, le_max_of_le_right (by positivity), max_le ?_ ?_⟩
  · rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [div_le_iff₀ (by linarith)]
    linarith

/-- `w ≥ 1000/r ⇒ wr ≥ 1000`. -/
theorem wr_ge (y r w : ℝ) (hr : 0 < r) (hw : max (1 / kK y) (1000 / r) ≤ w) : 1000 ≤ w * r := by
  have h := (le_max_right _ _).trans hw
  rwa [div_le_iff₀ hr] at h

/-! ## `g̃ ≥ 0` at `r₀` -/

/-- **`g_Y(t) ≥ 0`** once `t ≥ 1000` and `log(9Y^{1/3}/(4.008t)) > 0`. -/
theorem gY_nonneg (Y t : ℝ) (hY : 0 < Y) (ht : 1000 ≤ t)
    (hD : 0 < Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * t)))) : 0 ≤ OC.gY Y t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hR : 0 ≤ rR Y (2 * t) := le_trans (by norm_num) (MN.rR_ge _ _ (by linarith) hD)
  have hL : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have hl1 : 1 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt ht0]
    linarith [Real.exp_one_lt_d9]
  have hll : 0 < Real.log (Real.log t) := Real.log_pos hl1
  have hF : 0 ≤ bigF t := by
    unfold bigF
    positivity
  have hLL := lL_nonneg t ht0 (by linarith) hF
  unfold OC.gY
  positivity

/-- **`g̃(y, r₀) ≥ 0`** for `y ≥ 10²⁵` (every integrand of `gT` is `≥ 0`). -/
theorem gT_nonneg_r0 (y : ℝ) (hy : 10 ^ 25 ≤ y) : 0 ≤ OC.gT HW.phi y 150000 := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hly : 57.564626 ≤ Real.log y := MN.lya_ge_1.trans (Real.log_le_log (by norm_num) hy)
  have h9 := MN.log9_ge
  have h20 : Real.log 601200 ≤ 20 * 0.6931471808 := by
    have := Real.log_le_log (by norm_num) (show (601200 : ℝ) ≤ 2 ^ 20 by norm_num)
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_lt_d9]
  obtain ⟨hy1, hm0, hm1⟩ := w1_facts y 150000 hy (by norm_num)
  have hK : 0 < kK y := by
    unfold kK
    linarith
  have hlo : ∀ w ∈ Icc (max (1 / kK y) (1000 / 150000)) 1,
      0 ≤ OC.gY (w * y) (w * 150000) * HW.phi w := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hw.1
    have hwr := wr_ge y 150000 w (by norm_num) hw.1
    have hlw : Real.log w ≤ 0 := Real.log_nonpos hw0.le hw.2
    refine mul_nonneg (gY_nonneg _ _ (mul_pos hw0 hy0) hwr ?_) (HW.phi_nonneg w)
    rw [MN.logD_eq _ _ (mul_pos hw0 hy0) (by positivity), Real.log_mul hw0.ne' hy0.ne',
      show (2.004 : ℝ) * (2 * (w * 150000)) = w * 601200 by ring,
      Real.log_mul hw0.ne' (by norm_num)]
    linarith
  have hhi : ∀ w ∈ Ioi (1 : ℝ), 0 ≤ OC.gY (w * y) 150000 * HW.phi w := by
    intro w hw
    have hw1 : (1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hlw : 0 ≤ Real.log w := Real.log_nonneg hw1.le
    refine mul_nonneg (gY_nonneg _ _ (mul_pos hw0 hy0) (by norm_num) ?_) (HW.phi_nonneg w)
    rw [MN.logD_eq _ _ (mul_pos hw0 hy0) (by positivity), Real.log_mul hw0.ne' hy0.ne',
      show (2.004 : ℝ) * (2 * (150000 : ℝ)) = 601200 by norm_num]
    linarith
  have h1 : 0 ≤ ∫ w in (max (1 / kK y) (1000 / 150000))..1,
      OC.gY (w * y) (w * 150000) * HW.phi w :=
    intervalIntegral.integral_nonneg (hm1.trans (by norm_num)) hlo
  have h2 : 0 ≤ ∫ w in Ioi (1 : ℝ), OC.gY (w * y) 150000 * HW.phi w :=
    setIntegral_nonneg measurableSet_Ioi hhi
  have h3 : 0 ≤ ∫ w in (1 / kK y)..(max (1 / kK y) (1000 / 150000)), |HW.phi w| :=
    intervalIntegral.integral_nonneg (le_max_left _ _) (fun w _ => abs_nonneg _)
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  unfold OC.gT
  rw [hl1]
  positivity

/-- `IntBndI` weakens as `B` grows. -/
theorem intBndI_mono (f : ℝ → ℝ) (q B B' : ℝ) (h : IntBndI f q B) (hB : B ≤ B') :
    IntBndI f q B' :=
  ⟨h.1.trans hB, fun hf => (h.2 hf).trans hB⟩

/-- **The constant of a `w`-free piece majorant is `≥ 0`.** -/
theorem cexp_nonneg (Rb Lam Sb Lb Yb X Z : ℝ) (hRb : 0 ≤ Rb) (hLam : 0 ≤ Lam) (hSb : 0 ≤ Sb)
    (hLb : 0 ≤ Lb) (hYb : 0 ≤ Yb) (hX : 0 ≤ X) (hZ : 0 ≤ Z) :
    0 ≤ 0.70711 * ((Rb * Lam + 0.5) * Sb + 2.5) * X + Lb * Z + 3.2 * Yb := by
  have := mul_nonneg hRb hLam
  positivity

end Principia.Common.TernaryGoldbach.MC
