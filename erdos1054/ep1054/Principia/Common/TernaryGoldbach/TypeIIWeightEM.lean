/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIICortoLargeC

set_option autoImplicit false

/-!
# `M2L.WeightEM` PROVED — the odd-`s` weight of `g₂(m)` in `eq:grotto`

`M2L.WeightEM` asks, for `m ≥ 1` and `S ≥ 10m`,
`|wt(m, S) − (1/4)log(1 + 1/m)| ≤ (5m² + 2m + 1)/S²`, where
`wt(m, S) = ∑_{s ≤ S odd} (1/s)·|{u ∈ [1/2, 1] : ⌊uS/s⌋ = m}|` (`eq:etex`, odd version;
Helfgott prints the error with the factor `c_{2,0} = 1/3`, only the factor `1` is used). Proved
here from the definitions with error factor `13/12·(2m² + 2m + 1)/(5m² + 2m + 1) ≤ 0.68`:

```
 int_ind     ∫_{1/2}^{1} 𝟙[⌊uS/s⌋ = m] du = ρ(βs) − ρ(αs),  ρ = clamp to [1/2, 1],
             α = m/S, β = (m+1)/S
 rho_id      (ρ(γt) − 1/2)/t = γ(w_{1/2γ}(t) − w_{1/γ}(t)),  w_b(t) = max(0, 1 − b/t)
 tel_w       ∑_{k<K} w_b(2k+1) = W_b(2K)/2 + ∑ E_b(2k+1)      (W_b' = w_b, midpoint errors E_b)
 atanh_bd    2/x ≤ log((x+1)/(x−1)) ≤ 2/x + 2/(3x(x² − 1))   (Mathlib's artanh series)
 blk         −1/(4b) ≤ ∑_{k<K} E_b(2k+1) ≤ 5/(12b)   for b ≥ 5/2  (one kink interval, the
             rest telescoped against 1/(y(y+1)))
 main_W      the four W_b(2K) combine to exactly (1/4)log(1 + 1/m)
 weightEM    M2L.WeightEM                                                         PROVED
 cortoLarge_of_yutto : M2H.CortoLarge from YuttoMid2C, YuttoBig2C + the two cited runs
```

No computation is cited and none stands in for a proof step.
-/

namespace Principia.Common.TernaryGoldbach.M2W

open MeasureTheory Set

/-! ## (1) The artanh series -/

/-- **`2/x ≤ log((x+1)/(x−1)) ≤ 2/x + 2/(3x(x² − 1))`** for `x > 1`. -/
theorem atanh_bd (x : ℝ) (hx : 1 < x) :
    2 / x ≤ Real.log ((x + 1) / (x - 1)) ∧
      Real.log ((x + 1) / (x - 1)) ≤ 2 / x + 2 / (3 * x * (x ^ 2 - 1)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : x - 1 ≠ 0 := by linarith
  have h := Real.hasSum_log_one_add_inv (a := (x - 1) / 2) (by linarith)
  have e1 : 1 + ((x - 1) / 2)⁻¹ = (x + 1) / (x - 1) := by
    field_simp
    ring
  have e2 : 2 * ((x - 1) / 2) + 1 = x := by ring
  rw [e1, e2] at h
  have hq0 : 0 ≤ 1 / x := by positivity
  have hq1 : 1 / x < 1 := by rw [div_lt_one hx0]; exact hx
  have hf0 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / x) ^ (2 * 0 + 1) = 2 / x := by
    norm_num
    ring
  constructor
  · have := le_hasSum h 0 (fun j _ => by positivity)
    rw [hf0] at this
    exact this
  · have h1 := (hasSum_nat_add_iff' 1).mpr h
    have hr0 : 0 ≤ (1 / x) ^ 2 := by positivity
    have hr1 : (1 / x) ^ 2 < 1 := pow_lt_one₀ hq0 hq1 two_ne_zero
    have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 / 3 * (1 / x) ^ 3)
    have hle := hasSum_le (fun n => ?_) h1 hg
    · rw [Finset.sum_range_one, hf0] at hle
      have e3 : 2 / 3 * (1 / x) ^ 3 * (1 - (1 / x) ^ 2)⁻¹ = 2 / (3 * x * (x ^ 2 - 1)) := by
        have : x ^ 2 - 1 ≠ 0 := by nlinarith
        field_simp
      linarith
    · have hp : (1 / x) ^ (2 * (n + 1) + 1) = (1 / x) ^ 3 * ((1 / x) ^ 2) ^ n := by
        rw [← pow_mul, ← pow_add]
        ring_nf
      have hd : 1 / (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
        apply one_div_le_one_div_of_le (by norm_num)
        push_cast
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hpow : 0 ≤ (1 / x) ^ 3 * ((1 / x) ^ 2) ^ n := by positivity
      rw [hp]
      nlinarith

/-! ## (2) The block function `w_b`, its primitive `W_b`, midpoint errors `E_b` -/

/-- `w_b(t) = max(0, 1 − b/t)`. -/
noncomputable def w (b t : ℝ) : ℝ := max 0 (1 - b / t)

/-- `W_b(t) = ∫_0^t w_b`: `0` for `t ≤ b`, else `t − b − b log(t/b)`. -/
noncomputable def W (b t : ℝ) : ℝ := if t ≤ b then 0 else t - b - b * Real.log (t / b)

/-- The midpoint error `E_b(c) = w_b(c) − (W_b(c+1) − W_b(c−1))/2`. -/
noncomputable def E (b c : ℝ) : ℝ := w b c - (W b (c + 1) - W b (c - 1)) / 2

/-- `T(y) = 1/(y(y+1))`. -/
noncomputable def T (y : ℝ) : ℝ := 1 / (y * (y + 1))

/-- `G_b(k) = T(max(2k, b))`, the telescoping majorant. -/
noncomputable def G (b : ℝ) (k : ℕ) : ℝ := T (max (2 * (k : ℝ)) b)

theorem W_of_le (b t : ℝ) (h : t ≤ b) : W b t = 0 := by
  unfold W
  rw [if_pos h]

theorem W_of_ge (b t : ℝ) (hb : 0 < b) (h : b ≤ t) : W b t = t - b - b * Real.log (t / b) := by
  unfold W
  split_ifs with h'
  · have : t = b := le_antisymm h' h
    rw [this, div_self hb.ne', Real.log_one]
    ring
  · rfl

theorem T_anti (y z : ℝ) (hy : 0 < y) (hyz : y ≤ z) : T z ≤ T y := by
  unfold T
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem T_nonneg (y : ℝ) (hy : 0 < y) : 0 ≤ T y := by
  unfold T
  positivity

/-- **`W_b(t)` between `e²/(t+b) − e³/(6t(t+b))` and `e²/(t+b)`**, `e = t − b > 0`. -/
theorem Wbd (b t : ℝ) (hb : 0 < b) (ht : b < t) :
    (t - b) ^ 2 / (t + b) - (t - b) ^ 3 / (6 * t * (t + b)) ≤ W b t ∧
      W b t ≤ (t - b) ^ 2 / (t + b) := by
  rw [W_of_ge b t hb ht.le]
  have he : 0 < t - b := by linarith
  have ht0 : 0 < t := by linarith
  set x := (t + b) / (t - b) with hxdef
  have hx : 1 < x := by
    rw [hxdef, lt_div_iff₀ he]
    linarith
  obtain ⟨hlo, hhi⟩ := atanh_bd x hx
  have hb' := hb.ne'
  have he' := he.ne'
  have ht' := ht0.ne'
  have hx1 : x - 1 = 2 * b / (t - b) := by
    rw [hxdef]
    field_simp
    ring
  have hx2 : x + 1 = 2 * t / (t - b) := by
    rw [hxdef]
    field_simp
    ring
  have ex : (x + 1) / (x - 1) = t / b := by
    rw [hx1, hx2, div_div_div_cancel_right₀ he']
    rw [mul_div_mul_left _ _ (two_ne_zero)]
  rw [ex] at hlo hhi
  have e1 : b * (2 / x) = 2 * b * (t - b) / (t + b) := by
    rw [hxdef]
    field_simp
  have e2 : b * (2 / (3 * x * (x ^ 2 - 1))) = (t - b) ^ 3 / (6 * t * (t + b)) := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, hx1, hx2, hxdef]
    have hp : t + b ≠ 0 := by linarith
    field_simp
    ring
  have e3 : t - b - 2 * b * (t - b) / (t + b) = (t - b) ^ 2 / (t + b) := by
    field_simp
    ring
  have l1 := mul_le_mul_of_nonneg_left hlo hb.le
  have l2 := mul_le_mul_of_nonneg_left hhi hb.le
  rw [mul_add, e1, e2] at l2
  rw [e1] at l1
  constructor <;> linarith

/-! ## (3) One midpoint error at a time -/

/-- `c + 1 ≤ b`: no mass yet. -/
theorem E_A (b : ℝ) (k : ℕ) (hk : 2 * (k : ℝ) + 2 ≤ b) :
    E b (2 * k + 1) = 0 := by
  unfold E w
  have hc : (0 : ℝ) < 2 * k + 1 := by positivity
  have h1 : 1 - b / (2 * (k : ℝ) + 1) ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hc]
    linarith
  rw [max_eq_left h1, W_of_le b _ (by linarith), W_of_le b _ (by linarith)]
  ring

/-- `b ≤ c − 1`: the smooth part, `0 ≤ E ≤ b/(3c(c² − 1))`. -/
theorem E_B (b : ℝ) (hb : 0 < b) (k : ℕ) (hk : b ≤ 2 * (k : ℝ)) :
    0 ≤ E b (2 * k + 1) ∧ E b (2 * k + 1) ≤ b / 6 * (G b k - G b (k + 1)) := by
  have hk1 : (1 : ℝ) ≤ k := by
    have : (0 : ℝ) < 2 * k := by linarith
    have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
    exact_mod_cast hk0
  set c := 2 * (k : ℝ) + 1 with hcdef
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hEc : E b c = b / 2 * Real.log ((c + 1) / (c - 1)) - b / c := by
    unfold E w
    have hbc : b < c := by rw [hcdef]; linarith
    have h1 : 0 ≤ 1 - b / c := by
      rw [sub_nonneg, div_le_one (by linarith)]
      exact hbc.le
    rw [max_eq_right h1, W_of_ge b _ hb (by linarith), W_of_ge b _ hb (by rw [hcdef]; linarith)]
    have hl : Real.log ((c + 1) / (c - 1)) = Real.log ((c + 1) / b) - Real.log ((c - 1) / b) := by
      rw [← Real.log_div (by positivity) (by
        have : 0 < c - 1 := by linarith
        positivity)]
      congr 1
      field_simp
    rw [hl]
    ring
  obtain ⟨hlo, hhi⟩ := atanh_bd c hc1
  have hG : G b k - G b (k + 1) = T (c - 1) - T (c + 1) := by
    unfold G
    rw [max_eq_left hk, max_eq_left (by push_cast; linarith)]
    congr 2 <;> [rw [hcdef]; (rw [hcdef]; push_cast)] <;> ring
  rw [hG, hEc]
  constructor
  · have := mul_le_mul_of_nonneg_left hlo (show 0 ≤ b / 2 by positivity)
    have e : b / 2 * (2 / c) = b / c := by field_simp
    linarith
  · have h2 := mul_le_mul_of_nonneg_left hhi (show 0 ≤ b / 2 by positivity)
    have hc0 : 0 < c - 1 := by linarith
    have hcc : c ^ 2 - 1 ≠ 0 := by nlinarith
    have hcc' : c - 1 ≠ 0 := by linarith
    have hcc'' : c + 1 ≠ 0 := by linarith
    have hc0' : c ≠ 0 := by linarith
    have e : b / 2 * (2 / c + 2 / (3 * c * (c ^ 2 - 1))) =
        b / c + b / (3 * ((c - 1) * c * (c + 1))) := by
      field_simp
      ring
    have hT : 2 / ((c - 1) * c * (c + 1)) ≤ T (c - 1) - T (c + 1) := by
      unfold T
      have e2 : c - 1 + 1 = c := by ring
      rw [e2]
      have hle : 1 / ((c + 1) * (c + 1 + 1)) ≤ 1 / (c * (c + 1)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have e3 : 1 / ((c - 1) * c) - 1 / (c * (c + 1)) = 2 / ((c - 1) * c * (c + 1)) := by
        field_simp
        ring
      linarith
    have h3 : b / (3 * ((c - 1) * c * (c + 1))) ≤ b / 6 * (T (c - 1) - T (c + 1)) := by
      have := mul_le_mul_of_nonneg_left hT (show 0 ≤ b / 6 by positivity)
      have e4 : b / 6 * (2 / ((c - 1) * c * (c + 1))) = b / (3 * ((c - 1) * c * (c + 1))) := by
        field_simp
        ring
      linarith
    linarith

/-- The kink inequality, `c > b`: `δ/(b+δ) − (1+δ)²/(2(2b+1+δ)) ≥ −1/(4b)`. -/
theorem kink_lo (b d : ℝ) (hb : 5 / 2 ≤ b) (hd0 : 0 < d) (hd1 : d < 1) :
    -(1 / (4 * b)) ≤ d / (b + d) - (1 + d) ^ 2 / (2 * (2 * b + 1 + d)) := by
  have hb0 : 0 < b := by linarith
  have key : d / (b + d) - (1 + d) ^ 2 / (2 * (2 * b + 1 + d)) + 1 / (4 * b) =
      (2 * b ^ 2 * d * (2 - d) + b * d * (5 - 2 * d ^ 2) + b + d + d ^ 2) /
        (4 * b * (b + d) * (2 * b + 1 + d)) := by
    field_simp
    ring
  have hP : 0 ≤ (2 * b ^ 2 * d * (2 - d) + b * d * (5 - 2 * d ^ 2) + b + d + d ^ 2) /
      (4 * b * (b + d) * (2 * b + 1 + d)) := by
    apply div_nonneg _ (by positivity)
    have h1 : 0 ≤ 2 * b ^ 2 * d * (2 - d) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ b * d * (5 - 2 * d ^ 2) := mul_nonneg (by positivity) (by nlinarith)
    positivity
  linarith

/-- The kink inequality, `c > b`, upper side (main part): `≤ 1/(20b)`. -/
theorem kink_hi (b d : ℝ) (hb : 5 / 2 ≤ b) (hd0 : 0 < d) (hd1 : d < 1) :
    d / (b + d) - (1 + d) ^ 2 / (2 * (2 * b + 1 + d)) ≤ 1 / (20 * b) := by
  have hb0 : 0 < b := by linarith
  have key : 1 / (20 * b) - (d / (b + d) - (1 + d) ^ 2 / (2 * (2 * b + 1 + d))) =
      (2 * (b + d) * (2 * b + 1 + d) + 20 * b ^ 2 * (1 - d) ^ 2 -
        20 * b * (d * (1 - d ^ 2))) / (40 * b * (b + d) * (2 * b + 1 + d)) := by
    field_simp
    ring
  have hc : d * (1 - d ^ 2) ≤ 2 / 5 := by
    nlinarith [mul_nonneg (sq_nonneg (d - 0.58)) (show (0 : ℝ) ≤ d + 1.16 by linarith)]
  have hQ : 0 ≤ (2 * (b + d) * (2 * b + 1 + d) + 20 * b ^ 2 * (1 - d) ^ 2 -
      20 * b * (d * (1 - d ^ 2))) / (40 * b * (b + d) * (2 * b + 1 + d)) := by
    apply div_nonneg _ (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 20 * b by positivity)
    have h2 : 0 ≤ 20 * b ^ 2 * (1 - d) ^ 2 := by positivity
    nlinarith
  linarith

/-- `c − 1 < b < c + 1`: the one kink interval, `−1/(4b) ≤ E ≤ 1/(4b)`. -/
theorem E_C (b : ℝ) (hb : 5 / 2 ≤ b) (k : ℕ) (hk1 : 2 * (k : ℝ) < b) (hk2 : b < 2 * k + 2) :
    -(1 / (4 * b)) ≤ E b (2 * k + 1) ∧ E b (2 * k + 1) ≤ 1 / (4 * b) := by
  have hb0 : 0 < b := by linarith
  set c := 2 * (k : ℝ) + 1 with hcdef
  set t := c + 1 with htdef
  have ht : b < t := by rw [htdef, hcdef]; linarith
  have htb : t ≤ b + 2 := by rw [htdef, hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have ht2 : 2 ≤ t := by
    rw [htdef, hcdef]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hEc : E b c = w b c - W b t / 2 := by
    unfold E
    rw [W_of_le b (c - 1) (by rw [hcdef]; linarith)]
    ring
  obtain ⟨hWlo, hWhi⟩ := Wbd b t hb0 ht
  rw [hEc]
  have hp : 0 < t + b := by linarith
  rcases le_or_gt c b with hcb | hcb
  · have hw : w b c = 0 := by
      unfold w
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hc0]
      linarith
    rw [hw]
    have he1 : t - b ≤ 1 := by rw [htdef]; linarith
    have he0 : 0 < t - b := by linarith
    constructor
    · have h1 : (t - b) ^ 2 / (t + b) ≤ 1 / (2 * b) := by
        rw [div_le_div_iff₀ hp (by positivity)]
        have hsq : (t - b) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ 2 * b by positivity)]
      have e : 1 / (2 * b) / 2 = 1 / (4 * b) := by field_simp; ring
      linarith
    · have h1 : (t - b) ^ 3 / (6 * t * (t + b)) ≤ (t - b) ^ 2 / (t + b) := by
        rw [div_le_div_iff₀ (by positivity) hp]
        have := pow_pos he0 2
        nlinarith [mul_pos (pow_pos he0 2) hp]
      have : 0 ≤ 1 / (4 * b) := by positivity
      linarith
  · set d := c - b with hddef
    have hd0 : 0 < d := by rw [hddef]; linarith
    have hd1 : d < 1 := by rw [hddef, hcdef]; linarith
    have hw : w b c = d / (b + d) := by
      unfold w
      have hbd : b + d = c := by rw [hddef]; ring
      rw [hbd, max_eq_right]
      · rw [hddef]
        field_simp
      · rw [sub_nonneg, div_le_one hc0]
        exact hcb.le
    have hte : t - b = 1 + d := by rw [htdef, hddef]; ring
    have htb' : t + b = 2 * b + 1 + d := by rw [htdef, hddef]; ring
    rw [hw]
    rw [hte, htb'] at hWlo hWhi
    have hA : (1 + d) ^ 2 / (2 * (2 * b + 1 + d)) = (1 + d) ^ 2 / (2 * b + 1 + d) / 2 := by
      rw [div_div, mul_comm]
    constructor
    · have := kink_lo b d hb hd0 hd1
      linarith
    · have h1 := kink_hi b d hb hd0 hd1
      have h2 : (1 + d) ^ 3 / (6 * t * (2 * b + 1 + d)) ≤ 4 / (15 * b) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : t * (2 * b + 1 + d) ≥ b * (2 * b) := by nlinarith
        nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + d)
          (show 1 + d ≤ 2 by linarith) 3]
      have e1 : 1 / (20 * b) + 4 / (15 * b) / 2 ≤ 1 / (4 * b) := by
        rw [div_div, div_add_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

/-- **Per-`k` bound**: `−[k = ⌊b/2⌋]/(4b) ≤ E_b(2k+1)` and
`E_b(2k+1) ≤ (b/6)(G_b(k) − G_b(k+1)) + [k = ⌊b/2⌋]/(4b)`. -/
theorem E_k (b : ℝ) (hb : 5 / 2 ≤ b) (k : ℕ) :
    -(if k = ⌊b / 2⌋₊ then 1 / (4 * b) else 0) ≤ E b (2 * k + 1) ∧
      E b (2 * k + 1) ≤ b / 6 * (G b k - G b (k + 1)) +
        (if k = ⌊b / 2⌋₊ then 1 / (4 * b) else 0) := by
  have hb0 : 0 < b := by linarith
  have hite : 0 ≤ (if k = ⌊b / 2⌋₊ then 1 / (4 * b) else 0) := by
    split_ifs <;> positivity
  have hGmono : 0 ≤ G b k - G b (k + 1) := by
    unfold G
    have h1 : 0 < max (2 * (k : ℝ)) b := lt_of_lt_of_le hb0 (le_max_right _ _)
    have := T_anti _ _ h1 (max_le_max
      (show 2 * (k : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) by push_cast; linarith) le_rfl)
    linarith
  have hG0 : 0 ≤ b / 6 * (G b k - G b (k + 1)) := mul_nonneg (by positivity) hGmono
  rcases le_or_gt (2 * (k : ℝ) + 2) b with hA | hA
  · rw [E_A b k hA]
    constructor <;> linarith
  rcases le_or_gt b (2 * (k : ℝ)) with hB | hB
  · obtain ⟨h1, h2⟩ := E_B b hb0 k hB
    constructor <;> linarith
  · have hfl : k = ⌊b / 2⌋₊ := by
      symm
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> linarith
    rw [if_pos hfl]
    obtain ⟨h1, h2⟩ := E_C b hb k hB hA
    constructor <;> linarith

/-- **The block bound**: `−1/(4b) ≤ ∑_{k<K} E_b(2k+1) ≤ 1/(6b) + 1/(4b)` for `b ≥ 5/2`. -/
theorem blk (b : ℝ) (hb : 5 / 2 ≤ b) (K : ℕ) :
    -(1 / (4 * b)) ≤ ∑ k ∈ Finset.range K, E b (2 * k + 1) ∧
      ∑ k ∈ Finset.range K, E b (2 * k + 1) ≤ 1 / (6 * b) + 1 / (4 * b) := by
  have hb0 : 0 < b := by linarith
  have hsite : ∑ k ∈ Finset.range K, (if k = ⌊b / 2⌋₊ then 1 / (4 * b) else 0) ≤
      1 / (4 * b) := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hsite0 : 0 ≤ ∑ k ∈ Finset.range K, (if k = ⌊b / 2⌋₊ then 1 / (4 * b) else 0) :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  constructor
  · have h := Finset.sum_le_sum fun k (_ : k ∈ Finset.range K) => (E_k b hb k).1
    rw [Finset.sum_neg_distrib] at h
    linarith
  · have h := Finset.sum_le_sum fun k (_ : k ∈ Finset.range K) => (E_k b hb k).2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub'] at h
    have hG0 : G b 0 = T b := by
      unfold G
      rw [max_eq_right (by push_cast; linarith)]
    have hGK : 0 ≤ G b K := T_nonneg _ (lt_of_lt_of_le hb0 (le_max_right _ _))
    have hTb : b / 6 * T b ≤ 1 / (6 * b) := by
      unfold T
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : b / 6 * (G b 0 - G b K) ≤ b / 6 * T b := by
      rw [hG0]
      have := mul_nonneg (show 0 ≤ b / 6 by positivity) hGK
      nlinarith
    linarith

/-! ## (4) Telescoping and the main term -/

/-- **`∑_{k<K} w_b(2k+1) = W_b(2K)/2 + ∑_{k<K} E_b(2k+1)`**. -/
theorem tel_w (b : ℝ) (hb : 0 ≤ b) (K : ℕ) :
    ∑ k ∈ Finset.range K, w b (2 * k + 1) =
      W b (2 * K) / 2 + ∑ k ∈ Finset.range K, E b (2 * k + 1) := by
  have h : ∀ k : ℕ, w b (2 * k + 1) =
      E b (2 * k + 1) + (W b (2 * ((k + 1 : ℕ) : ℝ)) - W b (2 * (k : ℝ))) / 2 := by
    intro k
    unfold E
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_range_sub (fun k : ℕ => W b (2 * (k : ℝ)))]
  simp only [Nat.cast_zero, mul_zero]
  rw [W_of_le b 0 hb]
  ring

/-- `γ(W_{1/2γ}(M) − W_{1/γ}(M)) = (1 − log 2 + log(γM))/2` for `M ≥ 1/γ`. -/
theorem gW (γ M : ℝ) (hγ : 0 < γ) (hM : 1 / γ ≤ M) :
    γ * (W (1 / (2 * γ)) M - W (1 / γ) M) = (1 - Real.log 2 + Real.log (γ * M)) / 2 := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  rw [W_of_ge _ _ (by positivity) (le_trans (by
      rw [div_le_div_iff₀ (by positivity) hγ]
      linarith) hM), W_of_ge _ _ (by positivity) hM]
  have e1 : M / (1 / (2 * γ)) = 2 * (γ * M) := by field_simp
  have e2 : M / (1 / γ) = γ * M := by field_simp
  rw [e1, e2, Real.log_mul (by norm_num) (by positivity)]
  field_simp
  ring

/-- **The main term**: the four `W_b(M)` combine to `(1/4)log(1 + 1/m)`. -/
theorem main_W (m : ℕ) (hm : 1 ≤ m) (S M : ℝ) (hS : 0 < S) (hM : S / m ≤ M) :
    ((m : ℝ) + 1) / S * (W (1 / (2 * (((m : ℝ) + 1) / S))) M - W (1 / (((m : ℝ) + 1) / S)) M) / 2 -
      (m : ℝ) / S * (W (1 / (2 * ((m : ℝ) / S))) M - W (1 / ((m : ℝ) / S)) M) / 2 =
        Real.log (1 + 1 / (m : ℝ)) / 4 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < ((m : ℝ) + 1) / S := by positivity
  have ha : 0 < (m : ℝ) / S := by positivity
  have hMa : 1 / ((m : ℝ) / S) ≤ M := by rw [one_div_div]; exact hM
  have hMb : 1 / (((m : ℝ) + 1) / S) ≤ M := by
    rw [one_div_div]
    refine le_trans ?_ hM
    rw [div_le_div_iff₀ (by positivity) hm0]
    nlinarith
  rw [gW _ M hb hMb, gW _ M ha hMa]
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  rw [Real.log_mul hb.ne' hM0.ne', Real.log_mul ha.ne' hM0.ne',
    Real.log_div (by positivity) hS.ne', Real.log_div hm0.ne' hS.ne']
  have e : (1 : ℝ) + 1 / m = ((m : ℝ) + 1) / m := by field_simp
  rw [e, Real.log_div (by positivity) hm0.ne']
  ring

/-! ## (5) The weight as a sum -/

/-- `ρ(y) = min(1, max(1/2, y))`. -/
noncomputable def rho (y : ℝ) : ℝ := min 1 (max (1 / 2) y)

theorem meas_ge (p : ℝ) : Measurable fun u : ℝ => if p ≤ u then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

theorem ii_ge (p a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => if p ≤ u then (1 : ℝ) else 0) volume a b :=
  M2H.ii_of_bdd _ (meas_ge p) 1 a b hab fun u _ => by split_ifs <;> norm_num

/-- `∫_{1/2}^{1} 𝟙[p ≤ u] du = 1 − ρ(p)`. -/
theorem int_ge (p : ℝ) : ∫ u in (1 / 2 : ℝ)..1, (if p ≤ u then (1 : ℝ) else 0) = 1 - rho p := by
  have hq1 : 1 / 2 ≤ rho p := le_min (by norm_num) (le_max_left _ _)
  have hq2 : rho p ≤ 1 := min_le_left _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := rho p)
    (ii_ge p _ _ hq1) (ii_ge p _ _ hq2)]
  have h0 : ∫ u in (1 / 2 : ℝ)..rho p, (if p ≤ u then (1 : ℝ) else 0) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hq1 (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      have h1 := hu.2
      unfold rho at h1
      rw [lt_min_iff, lt_max_iff] at h1
      have : ¬ p ≤ u := by
        rcases h1.2 with h | h
        · linarith [hu.1]
        · linarith
      simp only [this, if_false]
  have h1 : ∫ u in rho p..1, (if p ≤ u then (1 : ℝ) else 0) = 1 - rho p := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hq2 (g := fun _ => (1 : ℝ))]
    · simp
    · intro u hu
      have h1 := hu.1
      unfold rho at h1
      rw [min_lt_iff, max_lt_iff] at h1
      have : p ≤ u := by
        rcases h1 with h | h
        · linarith [hu.2]
        · exact h.2.le
      simp only [this, if_true]
  rw [h0, h1, zero_add]

theorem ind_eq (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 0 < S) (s : ℕ) (hs : 1 ≤ s) (u : ℝ) :
    M2L.ind m S s u = (if (m : ℝ) * s / S ≤ u then 1 else 0) -
      (if ((m : ℝ) + 1) * s / S ≤ u then 1 else 0) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  unfold M2L.ind
  by_cases h1 : (m : ℝ) * s / S ≤ u
  · have hx : (m : ℝ) ≤ u * S / s := by
      rw [le_div_iff₀ hs0]
      rw [div_le_iff₀ hS] at h1
      linarith
    by_cases h2 : ((m : ℝ) + 1) * s / S ≤ u
    · have hx2 : (m : ℝ) + 1 ≤ u * S / s := by
        rw [le_div_iff₀ hs0]
        rw [div_le_iff₀ hS] at h2
        linarith
      have hf : ⌊u * S / s⌋₊ ≠ m := by
        intro h
        have := Nat.le_floor (show (((m + 1 : ℕ) : ℝ)) ≤ u * S / s by push_cast; exact hx2)
        omega
      rw [if_neg hf, if_pos h1, if_pos h2]
      ring
    · have hx2 : u * S / s < (m : ℝ) + 1 := by
        rw [div_lt_iff₀ hs0]
        rw [not_le, lt_div_iff₀ hS] at h2
        linarith
      rw [if_pos (M2H.floor_eq m _ hx hx2), if_pos h1, if_neg h2]
      ring
  · have hx : u * S / s < m := by
      rw [div_lt_iff₀ hs0]
      rw [not_le, lt_div_iff₀ hS] at h1
      linarith
    have hf : ⌊u * S / s⌋₊ ≠ m := by
      intro h
      have := (Nat.floor_lt' (by omega : m ≠ 0)).mpr hx
      omega
    have h2 : ¬ ((m : ℝ) + 1) * s / S ≤ u := by
      intro h2
      apply h1
      refine le_trans ?_ h2
      rw [div_le_div_iff_of_pos_right hS]
      nlinarith
    rw [if_neg hf, if_neg h1, if_neg h2]
    ring

/-- **`∫_{1/2}^{1} 𝟙[⌊uS/s⌋ = m] du = ρ(βs) − ρ(αs)`**. -/
theorem int_ind (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 0 < S) (s : ℕ) (hs : 1 ≤ s) :
    ∫ u in (1 / 2 : ℝ)..1, M2L.ind m S s u =
      rho (((m : ℝ) + 1) / S * s) - rho ((m : ℝ) / S * s) := by
  rw [intervalIntegral.integral_congr fun u _ => ind_eq m hm S hS s hs u,
    intervalIntegral.integral_sub (ii_ge _ _ _ (by norm_num)) (ii_ge _ _ _ (by norm_num)),
    int_ge, int_ge]
  have e1 : (m : ℝ) * s / S = (m : ℝ) / S * s := by ring
  have e2 : ((m : ℝ) + 1) * s / S = ((m : ℝ) + 1) / S * s := by ring
  rw [e1, e2]
  ring

/-- **`(ρ(γt) − 1/2)/t = γ(w_{1/2γ}(t) − w_{1/γ}(t))`**. -/
theorem rho_id (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) :
    1 / t * (rho (γ * t) - 1 / 2) = γ * (w (1 / (2 * γ)) t - w (1 / γ) t) := by
  have hy : 0 < γ * t := by positivity
  have e1 : 1 / (2 * γ) / t = 1 / (2 * (γ * t)) := by field_simp
  have e2 : 1 / γ / t = 1 / (γ * t) := by field_simp
  unfold w rho
  rw [e1, e2]
  rcases le_or_gt (γ * t) (1 / 2) with h1 | h1
  · rw [max_eq_left h1, min_eq_right (by norm_num)]
    have a1 : 1 - 1 / (2 * (γ * t)) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ (by positivity)]
      linarith
    have a2 : 1 - 1 / (γ * t) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hy]
      linarith
    rw [max_eq_left a1, max_eq_left a2]
    ring
  rcases le_or_gt (γ * t) 1 with h2 | h2
  · rw [max_eq_right h1.le, min_eq_right h2]
    have a1 : 0 ≤ 1 - 1 / (2 * (γ * t)) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      linarith
    have a2 : 1 - 1 / (γ * t) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hy]
      linarith
    rw [max_eq_right a1, max_eq_left a2]
    field_simp
    ring
  · rw [max_eq_right h1.le, min_eq_left h2.le]
    have a1 : 0 ≤ 1 - 1 / (2 * (γ * t)) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      linarith
    have a2 : 0 ≤ 1 - 1 / (γ * t) := by
      rw [sub_nonneg, div_le_one hy]
      linarith
    rw [max_eq_right a1, max_eq_right a2]
    field_simp
    ring

/-- A sum over odd `s ≤ N` of a function vanishing on odd `s > N` is the sum over the first `K`
odd numbers, `N ≤ 2K`. -/
theorem sum_odd_eq (N K : ℕ) (hK : N ≤ 2 * K) (f : ℕ → ℝ)
    (hz : ∀ k : ℕ, N < 2 * k + 1 → f (2 * k + 1) = 0) :
    ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s 2), f s =
      ∑ k ∈ Finset.range K, f (2 * k + 1) := by
  rw [← Finset.sum_image (s := Finset.range K) (g := fun k => 2 * k + 1) (f := f)
    (fun a _ b _ h => by simp only at h; omega)]
  refine Finset.sum_subset (fun s hs => ?_) (fun s hs hns => ?_)
  · rw [Finset.mem_filter, Finset.mem_Icc] at hs
    have hnd : ¬ 2 ∣ s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hs.2.symm
    rw [Finset.mem_image]
    exact ⟨s / 2, Finset.mem_range.mpr (by omega), by omega⟩
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
    apply hz
    by_contra h
    apply hns
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, Nat.Coprime.symm ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)

/-! ## (6) `M2L.WeightEM` -/

/-- The weight as a sum of the four blocks over the first `⌊S⌋` odd numbers. -/
theorem wt_sum (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 10 * (m : ℝ) ≤ S) (α β : ℝ)
    (hα : α = (m : ℝ) / S) (hβ : β = ((m : ℝ) + 1) / S) :
    M2L.wt m S = ∑ k ∈ Finset.range ⌊S⌋₊,
      (β * (w (1 / (2 * β)) (2 * k + 1) - w (1 / β) (2 * k + 1)) -
        α * (w (1 / (2 * α)) (2 * k + 1) - w (1 / α) (2 * k + 1))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hS0 : 0 < S := by linarith
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  unfold M2L.wt
  have hterm : ∀ s : ℕ, 1 ≤ s → 1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, M2L.ind m S s u =
      β * (w (1 / (2 * β)) s - w (1 / β) s) - α * (w (1 / (2 * α)) s - w (1 / α) s) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    rw [int_ind m hm S hS0 s hs, ← hα, ← hβ, ← rho_id β s hβ0 hs0, ← rho_id α s hα0 hs0]
    ring
  rw [Finset.sum_congr rfl fun s hs => hterm s
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1]
  rw [sum_odd_eq ⌊S⌋₊ ⌊S⌋₊ (by omega)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  · intro k hk
    have hsS : S < ((2 * k + 1 : ℕ) : ℝ) := by
      have h2 : ((⌊S⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hk
      have h3 := Nat.lt_floor_add_one S
      push_cast at h2 ⊢
      linarith
    have hs0 : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hr1 : 1 ≤ α * ((2 * k + 1 : ℕ) : ℝ) := by
      rw [hα, div_mul_eq_mul_div, le_div_iff₀ hS0]
      nlinarith
    have hr2 : 1 ≤ β * ((2 * k + 1 : ℕ) : ℝ) := by
      rw [hβ, div_mul_eq_mul_div, le_div_iff₀ hS0]
      nlinarith
    rw [← rho_id β _ hβ0 hs0, ← rho_id α _ hα0 hs0]
    unfold rho
    rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_left hr1,
      min_eq_left hr2]
    ring

/-- **The weight = main term + the four midpoint-error sums**, exactly. -/
theorem wt_split (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 10 * (m : ℝ) ≤ S) (α β : ℝ)
    (hα : α = (m : ℝ) / S) (hβ : β = ((m : ℝ) + 1) / S) :
    M2L.wt m S = Real.log (1 + 1 / (m : ℝ)) / 4 +
      (β * (∑ k ∈ Finset.range ⌊S⌋₊, E (1 / (2 * β)) (2 * k + 1) -
          ∑ k ∈ Finset.range ⌊S⌋₊, E (1 / β) (2 * k + 1)) -
        α * (∑ k ∈ Finset.range ⌊S⌋₊, E (1 / (2 * α)) (2 * k + 1) -
          ∑ k ∈ Finset.range ⌊S⌋₊, E (1 / α) (2 * k + 1))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hS0 : 0 < S := by linarith
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hM : S / m ≤ 2 * (⌊S⌋₊ : ℝ) := by
    have h1 : S / m ≤ S := div_le_self hS0.le hm1
    have h2 := Nat.lt_floor_add_one S
    linarith
  have hmain := main_W m hm S (2 * (⌊S⌋₊ : ℝ)) hS0 hM
  rw [← hα, ← hβ] at hmain
  rw [wt_sum m hm S hS α β hα hβ, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    tel_w (1 / (2 * β)) (by positivity) ⌊S⌋₊, tel_w (1 / β) (by positivity) ⌊S⌋₊,
    tel_w (1 / (2 * α)) (by positivity) ⌊S⌋₊, tel_w (1 / α) (by positivity) ⌊S⌋₊]
  linear_combination hmain

/-- **`M2L.WeightEM` PROVED**: `|wt(m, S) − (1/4)log(1 + 1/m)| ≤ (5m² + 2m + 1)/S²` for `m ≥ 1`,
`S ≥ 10m` (in fact `≤ (13/12)(2m² + 2m + 1)/S²`). -/
theorem weightEM : M2L.WeightEM := by
  intro m hm S hS
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hS0 : 0 < S := by linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (m : ℝ) / S := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ((m : ℝ) + 1) / S := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  rw [wt_split m hm S hS α β hα hβ, add_sub_cancel_left]
  have hb1 : 5 / 2 ≤ 1 / (2 * β) := by
    rw [hβ, le_div_iff₀ (by positivity)]
    rw [show 5 / 2 * (2 * (((m : ℝ) + 1) / S)) = 5 * ((m : ℝ) + 1) / S by ring,
      div_le_iff₀ hS0]
    nlinarith
  have hαβ : α ≤ β := by
    rw [hα, hβ]
    exact div_le_div_of_nonneg_right (by linarith) hS0.le
  have hb2 : 5 / 2 ≤ 1 / β := by
    have : 1 / (2 * β) ≤ 1 / β := one_div_le_one_div_of_le hβ0 (by linarith)
    linarith
  have hb3 : 5 / 2 ≤ 1 / (2 * α) := by
    have : 1 / (2 * β) ≤ 1 / (2 * α) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hb4 : 5 / 2 ≤ 1 / α := by
    have : 1 / (2 * α) ≤ 1 / α := one_div_le_one_div_of_le hα0 (by linarith)
    linarith
  obtain ⟨d1l, d1u⟩ := blk _ hb1 ⌊S⌋₊
  obtain ⟨d2l, d2u⟩ := blk _ hb2 ⌊S⌋₊
  obtain ⟨d3l, d3u⟩ := blk _ hb3 ⌊S⌋₊
  obtain ⟨d4l, d4u⟩ := blk _ hb4 ⌊S⌋₊
  generalize ∑ k ∈ Finset.range ⌊S⌋₊, E (1 / (2 * β)) (2 * k + 1) = D1 at d1l d1u ⊢
  generalize ∑ k ∈ Finset.range ⌊S⌋₊, E (1 / β) (2 * k + 1) = D2 at d2l d2u ⊢
  generalize ∑ k ∈ Finset.range ⌊S⌋₊, E (1 / (2 * α)) (2 * k + 1) = D3 at d3l d3u ⊢
  generalize ∑ k ∈ Finset.range ⌊S⌋₊, E (1 / α) (2 * k + 1) = D4 at d4l d4u ⊢
  have q1 : 1 / (4 * (1 / (2 * β))) = β / 2 := by field_simp; ring
  have q2 : 1 / (6 * (1 / (2 * β))) + 1 / (4 * (1 / (2 * β))) = 5 * β / 6 := by
    field_simp
    ring
  have q3 : 1 / (4 * (1 / β)) = β / 4 := by field_simp
  have q4 : 1 / (6 * (1 / β)) + 1 / (4 * (1 / β)) = 5 * β / 12 := by field_simp; ring
  have q5 : 1 / (4 * (1 / (2 * α))) = α / 2 := by field_simp; ring
  have q6 : 1 / (6 * (1 / (2 * α))) + 1 / (4 * (1 / (2 * α))) = 5 * α / 6 := by
    field_simp
    ring
  have q7 : 1 / (4 * (1 / α)) = α / 4 := by field_simp
  have q8 : 1 / (6 * (1 / α)) + 1 / (4 * (1 / α)) = 5 * α / 12 := by field_simp; ring
  rw [q1] at d1l
  rw [q2] at d1u
  rw [q3] at d2l
  rw [q4] at d2u
  rw [q5] at d3l
  rw [q6] at d3u
  rw [q7] at d4l
  rw [q8] at d4u
  have pβu : β * (D1 - D2) ≤ 13 / 12 * (β * β) := by
    have := mul_le_mul_of_nonneg_left (show D1 - D2 ≤ 13 / 12 * β by linarith) hβ0.le
    linarith
  have pβl : -(11 / 12 * (β * β)) ≤ β * (D1 - D2) := by
    have := mul_le_mul_of_nonneg_left (show -(11 / 12 * β) ≤ D1 - D2 by linarith) hβ0.le
    linarith
  have pαu : α * (D3 - D4) ≤ 13 / 12 * (α * α) := by
    have := mul_le_mul_of_nonneg_left (show D3 - D4 ≤ 13 / 12 * α by linarith) hα0.le
    linarith
  have pαl : -(11 / 12 * (α * α)) ≤ α * (D3 - D4) := by
    have := mul_le_mul_of_nonneg_left (show -(11 / 12 * α) ≤ D3 - D4 by linarith) hα0.le
    linarith
  have hsq : β * β + α * α = (2 * (m : ℝ) ^ 2 + 2 * m + 1) / S ^ 2 := by
    rw [hα, hβ]
    field_simp
    ring
  have hfin : 13 / 12 * ((2 * (m : ℝ) ^ 2 + 2 * m + 1) / S ^ 2) ≤
      (5 * (m : ℝ) ^ 2 + 2 * m + 1) / S ^ 2 := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hsq2 : α * α ≤ β * β := mul_self_le_mul_self hα0.le hαβ
  rw [abs_le]
  constructor <;> linarith

/-! ## (7) `M2H.CortoLarge` down to the two corrected `lem:yutto` links -/

/-- **`M2H.CortoLarge` from the corrected `lem:yutto` links and the two cited runs**:
`M2LC.cortoLarge_of_linksC` with `M2L.WeightEM` := `weightEM`. -/
theorem cortoLarge_of_yutto (ym : M2LC.YuttoMid2C) (yb : M2LC.YuttoBig2C)
    (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited) : M2H.CortoLarge :=
  M2LC.cortoLarge_of_linksC ym yb weightEM ys c0

end Principia.Common.TernaryGoldbach.M2W
